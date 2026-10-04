//! Lowering: the checked program to LatticeFoundry IR.
//!
//! Every local gets a stack slot (`alloca`) in the entry block; LF's mem2reg
//! promotes them to SSA values at `-O1` and above. Every operation reaching
//! this pass has been proven safe by the checker, so proven arithmetic carries
//! `nsw`/`nuw` flags and nothing here emits a run-time check.
//!
//! A view (a `str` or a slice) is two IR values, its pointer and its length:
//! it's passed as two parameters and stored in two slots. String literals
//! become read-only data symbols ([`Lowered::strings`]) that the object
//! writer emits, and so do array constants ([`Lowered::tables`]): a use of
//! one is a pointer to its data, read in place like an array in memory.
//!
//! Arrays and structs live in memory. Such an expression lowers to a
//! pointer to its storage ([`Val::Mem`]): a local's slot, an element or a
//! field of another value, or a temporary slot that a literal is written
//! into. Copying one copies its scalars, field by field and element by
//! element (in a loop for longer arrays). Slots and temporaries are
//! `alloca`s, which LF gives static frame slots. A struct's IR type is an LF
//! struct of its fields in declaration order, so its layout is LF's: each
//! field at the next offset aligned for it, the size rounded up to the
//! largest alignment.
//!
//! Enums and optionals (an optional `?T` is an enum with the variants `none`
//! and `some(value: T)`) live in memory too. Their IR type is an LF struct
//! of the tag and a payload area: `{ tag, [K x iA] }`, where `A` is the
//! largest alignment of the variants' payloads (each payload is an LF struct
//! of its fields) and `K` words of `A` bytes hold the largest one. A variant
//! without payload stores only the tag, and an enum where no variant has a
//! payload is just `{ tag }`. The tag is the enum's tag type (`u8` unless a
//! C-style enum declares another), holding the variant's position, or its
//! declared value in a C-style enum. A payload field is reached by viewing
//! the payload area's address as the variant's payload struct, so every
//! field is at an offset aligned for it. Code that depends on the variant
//! (`match`, copies, `==`, `??`) tests the tag and branches; only the active
//! variant's payload is ever read.
//!
//! Calls pass a value in memory as a pointer to it. A default parameter is
//! read-only for the duration of the call (docs/memory.md), and nothing can
//! change the argument while the callee runs, so the pointer is to the
//! caller's own value, not to a copy. An `inout` or `set` parameter is the
//! caller's place itself: a value in memory is passed the same way, and a
//! scalar as the address of the caller's variable, field or element, which
//! the callee loads and stores through (its slot is that address). An
//! `inout` slice is passed like any slice: the callee writes its elements
//! through its pointer. A `sink` parameter in memory is copied into the
//! callee's own storage on entry, since the callee may change it. A method
//! is an ordinary function with its receiver as the first parameter, named
//! `<package path>.<Type>.<name>`.
//!
//! A function returning a value in memory takes a pointer to the caller's
//! storage for the result as its first IR parameter and returns nothing. The caller passes fresh storage: a new local's slot
//! for `let x = f()`, otherwise a temporary that's then copied, so the
//! callee never writes to something it can also read through a parameter.
//!
//! A function that throws returns a result `throws(E) -> T`, which is an
//! enum `{ ok(T), err(E) }` in memory, written through the result pointer
//! like any value in memory. `return v` writes `ok(v)`; `throw e` writes
//! `err(e)`. A caller's `try`, `catch` or `match` calls into a temporary
//! (or a hidden local) and tests its tag. There is no unwinding: an error
//! is a return value.
//!
//! `defer` bodies are emitted at each exit of their block, in reverse
//! order: at its end, and at every `return`, `throw`, failing `try`,
//! `break` and `continue` that leaves it. `errdefer` bodies only at the
//! exits that leave the function with an error.

use std::rc::Rc;

use latticefoundry::Module;
use latticefoundry::ir::builder::FunctionBuilder;
use latticefoundry::ir::{
    BinOp as IrOp, BlockId, CastOp, Const, Flags, FuncAttrs, FuncId as IrFunc, Global, GlobalId,
    IntPred, Linkage, TypeId, ValueId, Visibility,
};
use latticefoundry::support::StrInterner;

use crate::mono;
use crate::sema::{
    CmpOp, Convention, Func, Handler, Local, Mode, Program, TBinOp, TExpr, TExprKind, TStmt, TUnOp,
};
use crate::types::{IntTy, Ty};

/// The IR layout of an enum or an optional (see the module docs).
struct SumIr {
    /// `{ tag, [K x iA] }`, or `{ tag }` without payloads.
    ty: TypeId,
    tag: IntTy,
    /// Each variant's payload struct, if it has a payload.
    payloads: Vec<Option<TypeId>>,
    /// Each variant's tag value.
    values: Vec<i128>,
}

/// The name of the entry wrapper, for a program whose `main` is also called
/// from Lode code (see [`lower`]).
pub const ENTRY_WRAPPER: &str = "main";

/// The result of lowering.
#[derive(Debug)]
pub struct Lowered {
    pub module: Module,
    pub syms: StrInterner,
    /// The symbol of the entry function LatticeFoundry's linker calls from
    /// `_start`, if the program has a `main`. Its `i64` return value is the
    /// process exit status.
    pub entry: Option<String>,
    /// Read-only data the object must define: `(symbol, bytes)` for each
    /// string literal.
    pub strings: Vec<(String, Vec<u8>)>,
    /// Read-only data the object must define for each array constant:
    /// `(symbol, bytes, alignment)`.
    pub tables: Vec<(String, Vec<u8>, u64)>,
    /// The program's warnings ([`Program::warnings`]).
    pub warnings: Vec<crate::diag::Diagnostic>,
}

/// IR types for every Lode type, interned up front (the function builder
/// borrows the module, so types can't be interned while building).
#[derive(Clone, Copy)]
struct Types {
    void: TypeId,
    bool: TypeId,
    ptr: TypeId,
    i8: TypeId,
    i16: TypeId,
    i32: TypeId,
    i64: TypeId,
}

impl Types {
    /// The IR type of a single-valued Lode type.
    fn of(&self, ty: Ty) -> TypeId {
        match ty {
            Ty::Unit => self.void,
            Ty::Bool => self.bool,
            Ty::Int(t) => self.int(t),
            Ty::Ptr(_) => self.ptr,
            Ty::Str | Ty::Slice(_) => unreachable!("a view is two values"),
            Ty::Array(_) | Ty::Struct(_) | Ty::Enum(_) | Ty::Optional(_) | Ty::Result(_) => {
                unreachable!("{ty} lives in memory")
            }
            Ty::Param(_) => unreachable!("instances have concrete types"),
        }
    }

    /// The IR values a Lode value is made of, as parameter types.
    fn parts(&self, ty: Ty) -> Vec<TypeId> {
        match ty {
            Ty::Unit => Vec::new(),
            Ty::Str | Ty::Slice(_) => vec![self.ptr, self.i64],
            _ if ty.in_memory() => vec![self.ptr],
            _ => vec![self.of(ty)],
        }
    }

    /// A function's IR parameter and return types. A result in memory is
    /// written through a pointer passed first (see the module docs).
    fn signature(&self, f: &Func) -> (Vec<TypeId>, TypeId) {
        let mut params = Vec::new();
        let result = f.result_ty();
        let ret = if result.in_memory() || result.is_view() {
            params.push(self.ptr);
            self.void
        } else {
            self.of(result)
        };
        params.extend(
            f.params
                .iter()
                .flat_map(|&p| self.param_parts(&f.locals[p])),
        );
        (params, ret)
    }

    /// The IR parameters of a parameter: its value's parts, or the address
    /// of the caller's place for a scalar passed `inout` or `set`.
    fn param_parts(&self, local: &Local) -> Vec<TypeId> {
        if local.by_ref() && !local.ty.in_memory() && !local.ty.is_view() {
            return vec![self.ptr];
        }
        self.parts(local.ty)
    }

    fn int(&self, t: IntTy) -> TypeId {
        match t.bits {
            8 => self.i8,
            16 => self.i16,
            32 => self.i32,
            _ => self.i64,
        }
    }
}

/// A lowered value.
#[derive(Clone, Copy, Debug)]
enum Val {
    Unit,
    One(ValueId),
    /// A view (`str` or slice): pointer and length.
    View(ValueId, ValueId),
    /// An array, a struct, an enum or an optional: a pointer to its storage.
    Mem(ValueId),
}

impl Val {
    fn one(self) -> ValueId {
        match self {
            Val::One(v) => v,
            other => unreachable!("expected a single value, found {other:?}"),
        }
    }

    fn parts(self) -> Vec<ValueId> {
        match self {
            Val::Unit => Vec::new(),
            Val::One(v) => vec![v],
            Val::View(p, n) => vec![p, n],
            Val::Mem(p) => vec![p],
        }
    }
}

/// Where a local lives: one stack slot per IR value.
#[derive(Clone, Copy, Debug)]
enum Slot {
    One {
        slot: ValueId,
        ty: TypeId,
        align: u32,
    },
    View {
        ptr: ValueId,
        len: ValueId,
    },
    /// An array's or a struct's storage.
    Mem(ValueId),
}

/// Lower a checked program to an IR module named `name`.
///
/// Only the code the program reaches is lowered: the functions `main` calls,
/// directly or not, and the string literals they use. A program without a
/// `main` (a library) is lowered whole, so `--emit=ir` shows all of it.
///
/// `main` itself is the entry function: it keeps its symbol (`main.main`)
/// and returns its exit status as an `i64`, extended from its integer type,
/// or `0` for a `main` that returns nothing. When Lode code also calls
/// `main`, it is lowered as an ordinary function and an entry wrapper named
/// [`ENTRY_WRAPPER`] calls it.
///
/// Every function but the entry has internal linkage: nothing outside the
/// program calls it, so the backend may drop it once it's inlined.
pub fn lower(program: &Program, name: &str) -> Lowered {
    let mut syms = StrInterner::new();
    let mut module = Module::new(name.to_owned());
    let t = {
        let types = module.types_mut();
        Types {
            void: types.void(),
            bool: types.bool(),
            ptr: types.ptr(),
            i8: types.int(8),
            i16: types.int(16),
            i32: types.int(32),
            i64: types.int(64),
        }
    };
    let reach = mono::instantiate(program);
    // `main` is the entry itself unless Lode code calls it.
    let direct_entry = reach.main.filter(|_| !reach.root_called);

    let mut strings = Vec::new();
    let mut string_globals = Vec::new();
    for (i, bytes) in program.strings.iter().enumerate() {
        let symbol = format!("lode.str.{i}");
        let ty = module.types_mut().array(t.i8, bytes.len().max(1) as u64);
        // The bytes themselves are emitted into the object by the caller; the
        // IR global only needs to exist so code can take its address.
        let init = module.intern_const(Const::Poison(ty));
        string_globals.push(module.add_global(Global {
            name: syms.intern(&symbol),
            ty,
            init: Some(init),
        }));
        if reach.strings[i] {
            strings.push((symbol, bytes.clone()));
        }
    }

    // Array constants are read-only data too, laid out like the IR type of
    // the array (each scalar at its type's size, row after row).
    let mut tables = Vec::new();
    let mut table_globals = Vec::new();
    for (i, table) in program.tables.iter().enumerate() {
        let symbol = format!("lode.table.{i}");
        let ty = ir_array(module.types_mut(), t, table.ty);
        let layout = module.types().layout(ty);
        let init = module.intern_const(Const::Poison(ty));
        table_globals.push(module.add_global(Global {
            name: syms.intern(&symbol),
            ty,
            init: Some(init),
        }));
        if reach.tables[i] {
            let leaf = crate::sema::table_leaf(table.ty).expect("an array of scalars");
            let size = module.types().layout(t.of(leaf)).size as usize;
            let mut bytes = Vec::with_capacity(layout.size as usize);
            for &v in &table.values {
                bytes.extend_from_slice(&v.to_le_bytes()[..size]);
            }
            debug_assert_eq!(bytes.len() as u64, layout.size);
            tables.push((symbol, bytes, layout.align));
        }
    }

    let internal = FuncAttrs::new(Linkage::Internal, Visibility::Default);
    let ids: Vec<Option<IrFunc>> = reach
        .funcs
        .iter()
        .enumerate()
        .map(|(i, f)| {
            let (params, ret) = t.signature(f);
            let is_entry = direct_entry == Some(i);
            let ret = if is_entry { t.i64 } else { ret };
            let sig = module.types_mut().func(params, ret, false);
            let id = module.declare_function(syms.intern(&f.symbol), sig);
            if !is_entry {
                module.set_func_attrs(id, internal.clone());
            }
            Some(id)
        })
        .collect();

    for (i, f) in reach.funcs.iter().enumerate() {
        let Some(id) = ids[i] else { continue };
        let b = module.build(id);
        FnLower {
            b,
            t,
            ids: &ids,
            strings: &string_globals,
            string_lens: &program.strings,
            tables: &table_globals,
            slots: Vec::new(),
            loops: Vec::new(),
            defers: Vec::new(),
            terminated: false,
            exit_status: (direct_entry == Some(i)).then_some(f.ret),
            result: None,
            result_ty: f.result_ty(),
            throws: f.throws.is_some(),
        }
        .function(f);
    }

    let entry = match (reach.main, direct_entry) {
        (Some(main), None) => {
            let sig = module.types_mut().func(Vec::new(), t.i64, false);
            let entry = module.declare_function(syms.intern(ENTRY_WRAPPER), sig);
            let ret = reach.funcs[main].ret;
            let mut b = module.build(entry);
            b.create_entry_block();
            let callee = b.func_ref(ids[main].expect("main is reached"));
            let result = b.call(callee, &[], t.of(ret));
            let status = exit_status(&mut b, t, ret, result);
            b.ret(Some(status));
            Some(ENTRY_WRAPPER.to_owned())
        }
        (Some(main), Some(_)) => Some(reach.funcs[main].symbol.clone()),
        (None, _) => None,
    };

    Lowered {
        module,
        syms,
        entry,
        strings,
        tables,
        warnings: program.warnings.clone(),
    }
}

/// The IR type of an array of scalars (or of arrays of them), built at
/// module level, before any function.
fn ir_array(types: &mut latticefoundry::ir::TypeContext, t: Types, ty: Ty) -> TypeId {
    match ty.as_array() {
        Some((elem, n)) => {
            let elem = ir_array(types, t, elem);
            types.array(elem, n)
        }
        None => t.of(ty),
    }
}

/// `main`'s result `v`, of type `ret`, as the `i64` exit status the entry
/// returns: an integer extended by its signedness, or `0` for `()`.
fn exit_status(b: &mut FunctionBuilder<'_>, t: Types, ret: Ty, v: Option<ValueId>) -> ValueId {
    match (ret, v) {
        (Ty::Int(it), Some(v)) if it.bits < 64 => {
            let op = if it.signed {
                CastOp::SExt
            } else {
                CastOp::ZExt
            };
            b.cast(op, v, t.i64)
        }
        (Ty::Int(_), Some(v)) => v,
        _ => b.const_i64(t.i64, 0),
    }
}

struct FnLower<'a> {
    b: FunctionBuilder<'a>,
    t: Types,
    /// The IR function of each reached function.
    ids: &'a [Option<IrFunc>],
    strings: &'a [GlobalId],
    string_lens: &'a [Vec<u8>],
    /// The global of each array constant.
    tables: &'a [GlobalId],
    slots: Vec<Slot>,
    /// `(continue target, break target, defer scopes outside it)` of each
    /// enclosing loop.
    loops: Vec<(BlockId, BlockId, usize)>,
    /// For each statement list being lowered, innermost last: the `defer`
    /// bodies registered so far, with whether each is an `errdefer`.
    defers: Vec<Vec<(Rc<[TStmt]>, bool)>>,
    /// Whether the current block already has its terminator.
    terminated: bool,
    /// For the entry function, `main`'s return type: its returns become
    /// `i64` exit statuses.
    exit_status: Option<Ty>,
    /// Where to write the result, for a function returning a value in memory.
    result: Option<ValueId>,
    /// What the function returns: its return type, or its result type if
    /// it throws.
    result_ty: Ty,
    /// Whether the function throws (and returns a result).
    throws: bool,
}

/// The most scalar copies an array copy or fill is unrolled into; longer
/// arrays are copied in a loop.
const UNROLL_LIMIT: u64 = 16;

/// The number of scalars in a value of type `ty`.
fn scalars(ty: Ty) -> u64 {
    if let Some((elem, n)) = ty.as_array() {
        return n.saturating_mul(scalars(elem));
    }
    if let Some(def) = ty.sum() {
        // The tag and the largest payload.
        let payload = def.variants.iter().map(|v| {
            v.fields
                .iter()
                .fold(0, |n: u64, f| n.saturating_add(scalars(f.ty)))
        });
        return payload.max().unwrap_or(0).saturating_add(1);
    }
    match ty.as_struct() {
        Some(def) => def
            .fields
            .iter()
            .fold(0, |n, f| n.saturating_add(scalars(f.ty))),
        None => 1,
    }
}

fn align_of(ty: Ty) -> u32 {
    match ty {
        Ty::Int(t) => t.bits / 8,
        Ty::Ptr(_) => 8,
        _ => 1,
    }
}

/// `v` (known to be in range for `t`) as the `i64` bit pattern of a `t`-wide
/// constant, sign-extended from the type's width.
fn const_bits(v: i128, t: IntTy) -> i64 {
    let shift = 64 - t.bits;
    ((v as i64) << shift) >> shift
}

impl FnLower<'_> {
    fn function(mut self, f: &Func) {
        let entry = self.b.create_entry_block();
        // The IR parameters: the result's storage first, if it's in memory,
        // then each parameter's parts.
        let mut next = 0;
        if self.result_ty.in_memory() || self.result_ty.is_view() {
            self.result = Some(self.b.param(entry, 0));
            next = 1;
        }
        let mut params: Vec<Option<Val>> = vec![None; f.locals.len()];
        for &p in &f.params {
            let ty = f.locals[p].ty;
            let mut part = || {
                next += 1;
                self.b.param(entry, next - 1)
            };
            params[p] = Some(match ty {
                Ty::Str | Ty::Slice(_) => {
                    let ptr = part();
                    Val::View(ptr, part())
                }
                _ if ty.in_memory() => Val::Mem(part()),
                _ => Val::One(part()),
            });
        }
        for (local, param) in f.locals.iter().zip(&params) {
            match *param {
                // A parameter in memory is the caller's value, read (or for
                // `inout` and `set`, written) in place. A `sink` one is the
                // callee's own copy.
                Some(Val::Mem(p)) if local.convention != Some(Convention::Sink) => {
                    self.slots.push(Slot::Mem(p));
                    continue;
                }
                // A scalar passed `inout` or `set`: the caller's place.
                Some(Val::One(p)) if local.by_ref() => {
                    let ty = self.t.of(local.ty);
                    self.slots.push(Slot::One {
                        slot: p,
                        ty,
                        align: align_of(local.ty),
                    });
                    continue;
                }
                _ => {}
            }
            let slot = match local.ty {
                Ty::Str | Ty::Slice(_) => Slot::View {
                    ptr: self.b.alloca(self.t.ptr),
                    len: self.b.alloca(self.t.i64),
                },
                ty if ty.in_memory() => {
                    let ir_ty = self.ir_ty(ty);
                    Slot::Mem(self.b.alloca(ir_ty))
                }
                ty => {
                    let ir_ty = self.t.of(ty);
                    Slot::One {
                        slot: self.b.alloca(ir_ty),
                        ty: ir_ty,
                        align: align_of(ty),
                    }
                }
            };
            self.slots.push(slot);
        }
        for (local, param) in params.into_iter().enumerate() {
            let info = &f.locals[local];
            match (param, self.slots[local]) {
                (Some(Val::Mem(src)), Slot::Mem(dst)) if dst != src => self.copy(dst, src, info.ty),
                (Some(Val::Mem(_)), _) | (None, _) => {}
                (Some(Val::One(_)), _) if info.by_ref() => {}
                (Some(val), _) => self.store(local, val),
            }
        }
        self.stmts(&f.body);
        if !self.terminated {
            if f.ret == Ty::Unit {
                self.return_value(None);
            } else {
                // The checker proved every path returns, so this block is dead.
                self.b.unreachable();
            }
        }
    }

    /// Return `v`; the entry returns it as an exit status.
    fn ret(&mut self, v: Option<ValueId>) {
        let v = match self.exit_status {
            Some(ty) => Some(exit_status(&mut self.b, self.t, ty, v)),
            None => v,
        };
        self.b.ret(v);
    }

    fn store(&mut self, local: usize, val: Val) {
        match (self.slots[local], val) {
            (Slot::One { slot, ty, align }, Val::One(v)) => self.b.store(ty, slot, v, align),
            (Slot::View { ptr, len }, Val::View(p, n)) => {
                self.b.store(self.t.ptr, ptr, p, 8);
                self.b.store(self.t.i64, len, n, 8);
            }
            (slot, val) => unreachable!("storing {val:?} into {slot:?}"),
        }
    }

    fn load(&mut self, local: usize) -> Val {
        match self.slots[local] {
            Slot::One { slot, ty, align } => Val::One(self.b.load(ty, slot, align)),
            Slot::View { ptr, len } => {
                let p = self.b.load(self.t.ptr, ptr, 8);
                let n = self.b.load(self.t.i64, len, 8);
                Val::View(p, n)
            }
            Slot::Mem(ptr) => Val::Mem(ptr),
        }
    }

    fn start_block(&mut self, block: BlockId) {
        self.b.switch_to(block);
        self.terminated = false;
    }

    /// A statement list, which is a scope for `defer`.
    fn stmts(&mut self, stmts: &[TStmt]) {
        self.defers.push(Vec::new());
        for s in stmts {
            if self.terminated {
                // Code after a `return`/`break`: give it a fresh (unreachable) block.
                let dead = self.b.create_block(&[]);
                self.start_block(dead);
            }
            self.stmt(s);
        }
        if !self.terminated {
            self.run_defers(self.defers.len() - 1, false);
        }
        self.defers.pop();
    }

    /// Emit the `defer` bodies of the scopes from `outer` in, innermost
    /// first and each scope's last first, for leaving them; with `error`,
    /// the `errdefer` bodies too.
    fn run_defers(&mut self, outer: usize, error: bool) {
        for scope in (outer..self.defers.len()).rev() {
            let bodies = self.defers[scope].clone();
            for (body, on_error) in bodies.iter().rev() {
                if *on_error && !error {
                    continue;
                }
                // The body can't leave its own statements, so the defers
                // registered while lowering it are its own.
                let depth = self.defers.len();
                self.stmts(body);
                debug_assert_eq!(depth, self.defers.len());
            }
        }
    }

    /// `return value`: write it (as `ok(value)` in a function that throws),
    /// run every `defer`, and return.
    fn return_value(&mut self, value: Option<&TExpr>) {
        let v = if self.throws {
            let dst = self.result.expect("a result in memory");
            if let Some(e) = value {
                let d = self.payload_at(dst, self.result_ty, 0, 0);
                self.fill_or_write(d, e);
            }
            self.store_tag(dst, self.result_ty, 0);
            None
        } else {
            match (value, self.result) {
                (Some(e), Some(dst)) if e.ty.is_view() => {
                    let v = self.expr(e);
                    self.write_view(dst, v);
                    None
                }
                (Some(e), Some(dst)) => {
                    self.fill(dst, e);
                    None
                }
                (Some(e), None) => Some(self.expr(e).one()),
                (None, _) => None,
            }
        };
        self.run_defers(0, false);
        self.ret(v);
        self.terminated = true;
    }

    /// Leave the function with an error: `write` stores it in the payload
    /// of `err` at the given address, then every `defer` and `errdefer`
    /// runs.
    fn fail(&mut self, write: impl FnOnce(&mut Self, ValueId)) {
        let dst = self.result.expect("a result in memory");
        let d = self.payload_at(dst, self.result_ty, 1, 0);
        write(self, d);
        self.store_tag(dst, self.result_ty, 1);
        self.run_defers(0, true);
        self.ret(None);
        self.terminated = true;
    }

    /// `throw e`.
    fn throw(&mut self, e: &TExpr) {
        self.fail(|this, d| this.fill(d, e));
    }

    /// Call `call`, a call to a function that throws, into a temporary, and
    /// branch on its result: to the returned block for `ok`, to `err_bb`
    /// for `err`. Returns the temporary and the `ok` block.
    fn call_result(&mut self, call: &TExpr, err_bb: BlockId) -> (ValueId, BlockId) {
        let ir_ty = self.ir_ty(call.ty);
        let tmp = self.b.alloca(ir_ty);
        self.fill(tmp, call);
        let tag = self.load_tag(tmp, call.ty);
        let ok_bb = self.b.create_block(&[]);
        self.branch_on_tag(tag, call.ty, &[(vec![0], ok_bb), (vec![1], err_bb)]);
        (tmp, ok_bb)
    }

    /// The value of `ok` in the result of type `ty` at `base`, or `Unit`.
    fn ok_value(&mut self, base: ValueId, ty: Ty) -> Val {
        let (value, _) = ty.as_result().expect("a result");
        if value == Ty::Unit {
            return Val::Unit;
        }
        let addr = self.payload_at(base, ty, 0, 0);
        self.read(addr, value)
    }

    /// `try call`.
    fn try_call(&mut self, call: &TExpr) -> Val {
        let (_, err) = call.ty.as_result().expect("a result");
        let err_bb = self.b.create_block(&[]);
        let (tmp, ok_bb) = self.call_result(call, err_bb);
        self.start_block(err_bb);
        let src = self.payload_at(tmp, call.ty, 1, 0);
        self.fail(|this, d| this.copy(d, src, err));
        self.start_block(ok_bb);
        self.ok_value(tmp, call.ty)
    }

    /// `call catch ...`, of type `ty`.
    fn catch(&mut self, call: &TExpr, binding: Option<usize>, handler: &Handler, ty: Ty) -> Val {
        let (_, err) = call.ty.as_result().expect("a result");
        // Where the value goes: a temporary in memory, or the join
        // block's parameter.
        let scalar = ty != Ty::Unit && !ty.in_memory();
        let out = if ty.in_memory() {
            let ir_ty = self.ir_ty(ty);
            Some(self.b.alloca(ir_ty))
        } else {
            None
        };
        let err_bb = self.b.create_block(&[]);
        let (tmp, ok_bb) = self.call_result(call, err_bb);
        let join = if scalar {
            let ir_ty = self.t.of(ty);
            self.b.create_block(&[ir_ty])
        } else {
            self.b.create_block(&[])
        };
        let arrive = |this: &mut Self, v: Val| {
            match (out, v) {
                (Some(dst), Val::Mem(src)) => this.copy(dst, src, ty),
                (None, Val::One(v)) => {
                    this.b.br(join, &[v]);
                    return;
                }
                _ => {}
            }
            this.b.br(join, &[]);
        };

        self.start_block(ok_bb);
        let v = self.ok_value(tmp, call.ty);
        arrive(self, v);

        self.start_block(err_bb);
        if let Some(local) = binding {
            let Slot::Mem(dst) = self.slots[local] else {
                unreachable!("an error is an enum, in memory")
            };
            let src = self.payload_at(tmp, call.ty, 1, 0);
            self.copy(dst, src, err);
        }
        match handler {
            Handler::Value(v) => match out {
                Some(dst) => {
                    self.fill(dst, v);
                    self.b.br(join, &[]);
                }
                None => {
                    let v = self.expr(v);
                    arrive(self, v);
                }
            },
            Handler::Block(body) => {
                self.stmts(body);
                // Only a `catch` whose value isn't used ends its block.
                if !self.terminated {
                    if scalar {
                        let ir_ty = self.t.of(ty);
                        let unused = self.b.poison(ir_ty);
                        self.b.br(join, &[unused]);
                    } else {
                        self.b.br(join, &[]);
                    }
                }
            }
        }
        self.start_block(join);
        match out {
            Some(dst) => Val::Mem(dst),
            None if scalar => Val::One(self.b.param(join, 0)),
            None => Val::Unit,
        }
    }

    fn stmt(&mut self, s: &TStmt) {
        match s {
            TStmt::Init(local, e) => match self.slots[*local] {
                // A new local can't appear in its own initializer, so a
                // literal is written straight into its storage.
                Slot::Mem(dst) => self.fill(dst, e),
                _ => {
                    let v = self.expr(e);
                    self.store(*local, v);
                }
            },
            TStmt::Assign(local, e) => match self.slots[*local] {
                Slot::Mem(dst) => self.assign_into(dst, e),
                _ => {
                    let v = self.expr(e);
                    self.store(*local, v);
                }
            },
            TStmt::Store(place, e) => {
                let dst = self.address(place);
                self.assign_into(dst, e);
            }
            TStmt::Expr(e) => {
                self.expr(e);
            }
            TStmt::Return(value) => self.return_value(value.as_ref()),
            TStmt::Throw(e) => self.throw(e),
            TStmt::Defer { body, on_error } => {
                let scope = self.defers.last_mut().expect("in a statement list");
                scope.push((Rc::from(body.clone()), *on_error));
            }
            TStmt::If(cond, then, otherwise) => {
                let c = self.expr(cond).one();
                let then_bb = self.b.create_block(&[]);
                let else_bb = self.b.create_block(&[]);
                let join = self.b.create_block(&[]);
                self.b.cond_br(c, then_bb, &[], else_bb, &[]);
                for (bb, body) in [(then_bb, then), (else_bb, otherwise)] {
                    self.start_block(bb);
                    self.stmts(body);
                    if !self.terminated {
                        self.b.br(join, &[]);
                    }
                }
                self.start_block(join);
            }
            TStmt::While(cond, body) => {
                let header = self.b.create_block(&[]);
                let body_bb = self.b.create_block(&[]);
                let exit = self.b.create_block(&[]);
                self.b.br(header, &[]);
                self.start_block(header);
                let c = self.expr(cond).one();
                self.b.cond_br(c, body_bb, &[], exit, &[]);
                self.loop_body(body_bb, header, exit, body);
                self.start_block(exit);
            }
            TStmt::Loop(body) => {
                let body_bb = self.b.create_block(&[]);
                let exit = self.b.create_block(&[]);
                self.b.br(body_bb, &[]);
                self.loop_body(body_bb, body_bb, exit, body);
                self.start_block(exit);
            }
            TStmt::For {
                var,
                start,
                end,
                body,
            } => {
                let it = start.ty.as_int().expect("integer range");
                let first = self.expr(start).one();
                let end = self.expr(end).one();
                self.store(*var, Val::One(first));
                let header = self.b.create_block(&[]);
                let body_bb = self.b.create_block(&[]);
                let latch = self.b.create_block(&[]);
                let exit = self.b.create_block(&[]);
                self.b.br(header, &[]);
                self.start_block(header);
                let i = self.load(*var).one();
                let pred = if it.signed {
                    IntPred::Slt
                } else {
                    IntPred::Ult
                };
                let more = self.b.icmp(pred, i, end);
                self.b.cond_br(more, body_bb, &[], exit, &[]);
                self.loop_body(body_bb, latch, exit, body);
                // The counter is below `end`, so adding one can't overflow.
                self.start_block(latch);
                let i = self.load(*var).one();
                let one = self.b.const_i64(self.t.int(it), 1);
                let flags = if it.signed {
                    Flags::nsw()
                } else {
                    Flags::nuw()
                };
                let next = self.b.add(i, one, flags);
                self.store(*var, Val::One(next));
                self.b.br(header, &[]);
                self.start_block(exit);
            }
            TStmt::Break | TStmt::Continue => {
                let (cont, brk, outer) = *self.loops.last().expect("checked: inside a loop");
                let target = if matches!(s, TStmt::Break) { brk } else { cont };
                self.run_defers(outer, false);
                self.b.br(target, &[]);
                self.terminated = true;
            }
            TStmt::Block(body) => self.stmts(body),
            TStmt::Match { value, arms } => {
                let base = self.place(value);
                let tag = self.load_tag(base, value.ty);
                let blocks: Vec<BlockId> = arms.iter().map(|_| self.b.create_block(&[])).collect();
                let join = self.b.create_block(&[]);
                let targets: Vec<(Vec<u32>, BlockId)> = arms
                    .iter()
                    .zip(&blocks)
                    .map(|(a, &bb)| (a.variants.clone(), bb))
                    .collect();
                self.branch_on_tag(tag, value.ty, &targets);
                for (arm, bb) in arms.iter().zip(blocks) {
                    self.start_block(bb);
                    self.stmts(&arm.body);
                    if !self.terminated {
                        self.b.br(join, &[]);
                    }
                }
                self.start_block(join);
            }
        }
    }

    fn loop_body(&mut self, body_bb: BlockId, cont: BlockId, exit: BlockId, body: &[TStmt]) {
        self.start_block(body_bb);
        self.loops.push((cont, exit, self.defers.len()));
        self.stmts(body);
        self.loops.pop();
        if !self.terminated {
            self.b.br(cont, &[]);
        }
    }

    /// An integer or pointer operand as the 64-bit value a syscall register holds.
    fn syscall_operand(&mut self, e: &TExpr) -> ValueId {
        let v = self.expr(e).one();
        match e.ty {
            Ty::Int(it) if it.bits < 64 => {
                let op = if it.signed {
                    CastOp::SExt
                } else {
                    CastOp::ZExt
                };
                self.b.cast(op, v, self.t.i64)
            }
            _ => v,
        }
    }

    fn expr(&mut self, e: &TExpr) -> Val {
        let v = match &e.kind {
            TExprKind::Int(v) => {
                let it = e.ty.as_int().expect("integer literal");
                let ty = self.t.int(it);
                self.b.const_i64(ty, const_bits(*v, it))
            }
            TExprKind::Bool(v) => self.b.const_bool(*v),
            TExprKind::Str(id) => {
                let p = self.b.global_ref(self.strings[*id]);
                let n = self
                    .b
                    .const_i64(self.t.i64, self.string_lens[*id].len() as i64);
                return Val::View(p, n);
            }
            // An array constant is read in place, like any array in memory;
            // nothing writes to it.
            TExprKind::Table(id) => return Val::Mem(self.b.global_ref(self.tables[*id])),
            TExprKind::Local(local) => return self.load(*local),
            // A returned view is written to a pointer and length in memory.
            TExprKind::Call(f, args) if e.ty.is_view() => {
                let ty = self.view_ir();
                let tmp = self.b.alloca(ty);
                self.call(*f, args, e.ty, Some(tmp));
                let p = self.b.struct_field(tmp, ty, 0);
                let n = self.b.struct_field(tmp, ty, 1);
                let p = self.b.load(self.t.ptr, p, 8);
                let n = self.b.load(self.t.i64, n, 8);
                return Val::View(p, n);
            }
            TExprKind::Call(..) if e.ty.in_memory() => {
                let ir_ty = self.ir_ty(e.ty);
                let tmp = self.b.alloca(ir_ty);
                self.fill(tmp, e);
                return Val::Mem(tmp);
            }
            TExprKind::Call(f, args) => return self.call(*f, args, e.ty, None),
            TExprKind::GenericCall(..) => unreachable!("instances call instances"),
            TExprKind::Syscall(args) => {
                let ops: Vec<ValueId> = args.iter().map(|a| self.syscall_operand(a)).collect();
                self.b.syscall(ops[0], &ops[1..])
            }
            TExprKind::ViewLen(s) => match self.expr(s) {
                Val::View(_, n) => n,
                other => unreachable!("`len` of {other:?}"),
            },
            // The same pointer and length.
            TExprKind::Bytes(s) => return self.expr(s),
            TExprKind::StrPtr(s) => match self.expr(s) {
                Val::View(p, _) => p,
                other => unreachable!("`ptr` of {other:?}"),
            },
            TExprKind::ArrayLen(a) => {
                self.expr(a);
                let (_, n) = a.ty.as_array().expect("an array");
                self.b.const_i64(self.t.i64, n as i64)
            }
            TExprKind::ArrayLit(_)
            | TExprKind::ArrayRepeat(..)
            | TExprKind::StructLit(_)
            | TExprKind::Variant(..)
            | TExprKind::EnumFrom(_)
            | TExprKind::Compare(..) => {
                let ir_ty = self.ir_ty(e.ty);
                let tmp = self.b.alloca(ir_ty);
                self.fill(tmp, e);
                return Val::Mem(tmp);
            }
            TExprKind::Index(..) | TExprKind::Field(..) | TExprKind::Payload(..) => {
                let addr = self.address(e);
                return self.read(addr, e.ty);
            }
            TExprKind::Coalesce(opt, default) => return self.coalesce(opt, default, e.ty),
            // The address of the place: as for any value in memory, of a
            // scalar's storage, or a view of an array.
            TExprKind::Ref(place) => {
                if place.ty.in_memory() || place.ty.is_view() {
                    return self.expr(place);
                }
                match place.kind {
                    TExprKind::Local(l) => match self.slots[l] {
                        Slot::One { slot, .. } => slot,
                        other => unreachable!("a scalar in {other:?}"),
                    },
                    _ => self.address(place),
                }
            }
            TExprKind::Try(call) => return self.try_call(call),
            TExprKind::Catch {
                call,
                binding,
                handler,
            } => return self.catch(call, *binding, handler, e.ty),
            // Only the default of `??`: it leaves, and the code after it,
            // which uses its value, is unreachable.
            TExprKind::Throw(value) => {
                self.throw(value);
                let dead = self.b.create_block(&[]);
                self.start_block(dead);
                if e.ty.in_memory() {
                    let ir_ty = self.ir_ty(e.ty);
                    return Val::Mem(self.b.alloca(ir_ty));
                }
                let ir_ty = self.t.of(e.ty);
                self.b.poison(ir_ty)
            }
            TExprKind::EnumValue(inner) => {
                let base = self.place(inner);
                self.load_tag(base, inner.ty)
            }
            // A view of part of the base's storage: proven in bounds, so
            // no check.
            TExprKind::Slice(base, start, end) => {
                let Val::View(p, n) = self.expr(base) else {
                    unreachable!("slicing a {}", base.ty)
                };
                let start = start.as_deref().map(|s| self.offset(s));
                let end = match end.as_deref() {
                    Some(e) => self.offset(e),
                    None => n,
                };
                let Some(start) = start else {
                    return Val::View(p, end);
                };
                let elem = e.ty.as_slice().expect("a slice");
                let elem = self.ir_ty(elem);
                let p = self.b.array_elem(p, elem, start);
                let n = self.b.sub(end, start, Flags::nuw());
                return Val::View(p, n);
            }
            TExprKind::ToSlice(a) => {
                let p = self.place(a);
                let (_, n) = a.ty.as_array().expect("an array");
                let n = self.b.const_i64(self.t.i64, n as i64);
                return Val::View(p, n);
            }
            TExprKind::PtrAdd(p, n) => {
                let base = self.expr(p).one();
                let count = self.expr(n).one();
                let Ty::Ptr(elem) = p.ty else {
                    unreachable!("pointer arithmetic on {}", p.ty)
                };
                let size = i64::from(elem.bits / 8);
                let offset = if size == 1 {
                    count
                } else {
                    let s = self.b.const_i64(self.t.i64, size);
                    self.b.mul(count, s, Flags::NONE)
                };
                self.b.ptr_add(base, offset, false)
            }
            TExprKind::Unary(op, operand) => {
                let ty = self.t.of(e.ty);
                let v = self.expr(operand).one();
                match op {
                    TUnOp::Neg => {
                        let zero = self.b.const_i64(ty, 0);
                        self.b.sub(zero, v, Flags::nsw())
                    }
                    TUnOp::Not => {
                        let one = self.b.const_bool(true);
                        self.b.bin(IrOp::Xor, v, one, Flags::NONE)
                    }
                    TUnOp::BitNot => {
                        let ones = self.b.const_i64(ty, -1);
                        self.b.bin(IrOp::Xor, v, ones, Flags::NONE)
                    }
                }
            }
            TExprKind::Binary(TBinOp::Cmp(op @ (CmpOp::Eq | CmpOp::Ne)), lhs, rhs)
                if lhs.ty.in_memory() =>
            {
                let l = self.place(lhs);
                let r = self.place(rhs);
                let eq = self.equal(l, r, lhs.ty);
                if *op == CmpOp::Eq {
                    eq
                } else {
                    let one = self.b.const_bool(true);
                    self.b.bin(IrOp::Xor, eq, one, Flags::NONE)
                }
            }
            TExprKind::Binary(op, lhs, rhs) => {
                let l = self.expr(lhs).one();
                let r = self.expr(rhs).one();
                self.binary(*op, lhs.ty, e.ty, l, r, rhs.ty)
            }
            TExprKind::And(lhs, rhs) | TExprKind::Or(lhs, rhs) => {
                let is_and = matches!(e.kind, TExprKind::And(..));
                let l = self.expr(lhs).one();
                let rhs_bb = self.b.create_block(&[]);
                let merge = self.b.create_block(&[self.t.bool]);
                let short = self.b.const_bool(!is_and);
                if is_and {
                    self.b.cond_br(l, rhs_bb, &[], merge, &[short]);
                } else {
                    self.b.cond_br(l, merge, &[short], rhs_bb, &[]);
                }
                self.start_block(rhs_bb);
                let r = self.expr(rhs).one();
                self.b.br(merge, &[r]);
                self.start_block(merge);
                self.b.param(merge, 0)
            }
            TExprKind::Convert(inner) => {
                let v = self.expr(inner).one();
                let from = inner.ty.as_int().expect("integer conversion");
                let to = e.ty.as_int().expect("integer conversion");
                self.resize(v, from, to)
            }
        };
        Val::One(v)
    }

    /// A call. A result in memory is written to `dst`, which must be fresh
    /// storage (see the module docs).
    fn call(&mut self, f: usize, args: &[TExpr], ret: Ty, dst: Option<ValueId>) -> Val {
        let mut values: Vec<ValueId> = dst.into_iter().collect();
        for a in args {
            let v = self.expr(a).parts();
            values.extend(v);
        }
        let callee = self.b.func_ref(self.ids[f].expect("a reached function"));
        let ret_ty = if dst.is_some() {
            self.t.void
        } else {
            self.t.of(ret)
        };
        match (self.b.call(callee, &values, ret_ty), dst) {
            (_, Some(p)) => Val::Mem(p),
            (Some(v), None) => Val::One(v),
            (None, None) => Val::Unit,
        }
    }

    /// The IR type of a view in memory, for a function returning one: its
    /// pointer, then its length.
    fn view_ir(&mut self) -> TypeId {
        let (ptr, len) = (self.t.ptr, self.t.i64);
        self.b.types_mut().struct_(vec![ptr, len])
    }

    /// Store the view `v` (a returned `str`) at `dst`.
    fn write_view(&mut self, dst: ValueId, v: Val) {
        let Val::View(p, n) = v else {
            unreachable!("a view, found {v:?}")
        };
        let ty = self.view_ir();
        let pa = self.b.struct_field(dst, ty, 0);
        let na = self.b.struct_field(dst, ty, 1);
        self.b.store(self.t.ptr, pa, p, 8);
        self.b.store(self.t.i64, na, n, 8);
    }

    /// The IR type of a value stored in memory: a scalar, or an array or a
    /// struct of them.
    fn ir_ty(&mut self, ty: Ty) -> TypeId {
        if let Some((elem, n)) = ty.as_array() {
            let elem = self.ir_ty(elem);
            return self.b.types_mut().array(elem, n);
        }
        if ty.sum().is_some() {
            return self.sum_ir(ty).ty;
        }
        match ty.as_struct() {
            Some(def) => {
                let fields = def.fields.iter().map(|f| self.ir_ty(f.ty)).collect();
                self.b.types_mut().struct_(fields)
            }
            None => self.t.of(ty),
        }
    }

    /// The IR layout of an enum or an optional (see the module docs).
    fn sum_ir(&mut self, ty: Ty) -> SumIr {
        let def = ty.sum().expect("an enum or an optional");
        let tag = self.t.int(def.tag);
        let payloads: Vec<Option<TypeId>> = def
            .variants
            .iter()
            .map(|v| {
                if v.fields.is_empty() {
                    return None;
                }
                let fields = v.fields.iter().map(|f| self.ir_ty(f.ty)).collect();
                Some(self.b.types_mut().struct_(fields))
            })
            .collect();
        let (mut size, mut align) = (0, 1);
        for &p in payloads.iter().flatten() {
            let layout = self.b.types().layout(p);
            size = size.max(layout.size);
            align = align.max(layout.align);
        }
        let ir = if size == 0 {
            self.b.types_mut().struct_(vec![tag])
        } else {
            let word = self.b.types_mut().int(align as u32 * 8);
            let area = self.b.types_mut().array(word, size.div_ceil(align));
            self.b.types_mut().struct_(vec![tag, area])
        };
        SumIr {
            ty: ir,
            tag: def.tag,
            payloads,
            values: def.variants.iter().map(|v| v.value).collect(),
        }
    }

    /// The tag of the enum or optional of type `ty` at `base`.
    fn load_tag(&mut self, base: ValueId, ty: Ty) -> ValueId {
        let sum = self.sum_ir(ty);
        let addr = self.b.struct_field(base, sum.ty, 0);
        let tag = self.t.int(sum.tag);
        self.b.load(tag, addr, align_of(Ty::Int(sum.tag)))
    }

    /// Make the enum or optional of type `ty` at `base` variant `variant`
    /// (its payload is written separately).
    fn store_tag(&mut self, base: ValueId, ty: Ty, variant: u32) {
        let sum = self.sum_ir(ty);
        let addr = self.b.struct_field(base, sum.ty, 0);
        let tag = self.t.int(sum.tag);
        let v = self
            .b
            .const_i64(tag, const_bits(sum.values[variant as usize], sum.tag));
        self.b.store(tag, addr, v, align_of(Ty::Int(sum.tag)));
    }

    /// The address of payload field `field` of variant `variant` of the enum
    /// or optional of type `ty` at `base`.
    fn payload_at(&mut self, base: ValueId, ty: Ty, variant: u32, field: u32) -> ValueId {
        let sum = self.sum_ir(ty);
        let area = self.b.struct_field(base, sum.ty, 1);
        let payload = sum.payloads[variant as usize].expect("a variant with a payload");
        self.b.struct_field(area, payload, field)
    }

    /// Branch on `tag`, the tag of a value of the enum or optional type
    /// `ty`: to `targets[k].1` when it's one of the variants in
    /// `targets[k].0`. Every variant is in exactly one target, so the last
    /// target (with variants) is taken without a test. The current block is
    /// left terminated.
    fn branch_on_tag(&mut self, tag: ValueId, ty: Ty, targets: &[(Vec<u32>, BlockId)]) {
        let sum = self.sum_ir(ty);
        let tag_ty = self.t.int(sum.tag);
        let live: Vec<&(Vec<u32>, BlockId)> =
            targets.iter().filter(|(v, _)| !v.is_empty()).collect();
        for (i, (variants, bb)) in live.iter().enumerate() {
            if i + 1 == live.len() {
                self.b.br(*bb, &[]);
                break;
            }
            let mut cond = None;
            for &v in variants {
                let value = self
                    .b
                    .const_i64(tag_ty, const_bits(sum.values[v as usize], sum.tag));
                let is = self.b.icmp(IntPred::Eq, tag, value);
                cond = Some(match cond {
                    None => is,
                    Some(c) => self.b.bin(IrOp::Or, c, is, Flags::NONE),
                });
            }
            let next = self.b.create_block(&[]);
            self.b
                .cond_br(cond.expect("a variant"), *bb, &[], next, &[]);
            self.start_block(next);
        }
        self.terminated = true;
    }

    /// For each variant of the enum or optional of type `ty` that has a
    /// payload, a block, run `body` in it with the variant, and go on after
    /// all of them. `tag` is the value's tag.
    fn each_payload(&mut self, tag: ValueId, ty: Ty, mut body: impl FnMut(&mut Self, u32)) {
        let def = ty.sum().expect("an enum or an optional");
        let with: Vec<u32> = (0..def.variants.len() as u32)
            .filter(|&v| !def.variants[v as usize].fields.is_empty())
            .collect();
        if with.is_empty() {
            return;
        }
        let without: Vec<u32> = (0..def.variants.len() as u32)
            .filter(|v| !with.contains(v))
            .collect();
        let join = self.b.create_block(&[]);
        let mut targets: Vec<(Vec<u32>, BlockId)> = with
            .iter()
            .map(|&v| (vec![v], self.b.create_block(&[])))
            .collect();
        let blocks: Vec<(u32, BlockId)> = targets.iter().map(|(v, bb)| (v[0], *bb)).collect();
        targets.push((without, join));
        self.branch_on_tag(tag, ty, &targets);
        for (v, bb) in blocks {
            self.start_block(bb);
            body(self, v);
            self.b.br(join, &[]);
        }
        self.start_block(join);
    }

    /// `opt ?? default`, of type `ty`.
    fn coalesce(&mut self, opt: &TExpr, default: &TExpr, ty: Ty) -> Val {
        let base = self.place(opt);
        let tag = self.load_tag(base, opt.ty);
        let some_bb = self.b.create_block(&[]);
        let none_bb = self.b.create_block(&[]);
        let targets = [(vec![1], some_bb), (vec![0], none_bb)];
        if ty.in_memory() {
            let ir_ty = self.ir_ty(ty);
            let tmp = self.b.alloca(ir_ty);
            let join = self.b.create_block(&[]);
            self.branch_on_tag(tag, opt.ty, &targets);
            self.start_block(some_bb);
            let src = self.payload_at(base, opt.ty, 1, 0);
            self.copy(tmp, src, ty);
            self.b.br(join, &[]);
            self.start_block(none_bb);
            self.fill(tmp, default);
            self.b.br(join, &[]);
            self.start_block(join);
            return Val::Mem(tmp);
        }
        let join = self.b.create_block(&[self.t.of(ty)]);
        self.branch_on_tag(tag, opt.ty, &targets);
        self.start_block(some_bb);
        let src = self.payload_at(base, opt.ty, 1, 0);
        let v = self.read(src, ty).one();
        self.b.br(join, &[v]);
        self.start_block(none_bb);
        let d = self.expr(default).one();
        self.b.br(join, &[d]);
        self.start_block(join);
        Val::One(self.b.param(join, 0))
    }

    /// Write `E(x)` (a `?E` for the C-style enum `E`) to `dst`: the variant
    /// whose value is `x`, or `none`.
    fn enum_from(&mut self, dst: ValueId, opt: Ty, x: &TExpr) {
        let enum_ty = opt.as_optional().expect("an optional");
        let def = enum_ty.as_enum().expect("an enum");
        let it = x.ty.as_int().expect("an integer");
        let v = self.expr(x).one();
        let join = self.b.create_block(&[]);
        for (k, variant) in def.variants.iter().enumerate() {
            if !it.range().contains(variant.value) {
                continue;
            }
            let value = self
                .b
                .const_i64(self.t.int(it), const_bits(variant.value, it));
            let is = self.b.icmp(IntPred::Eq, v, value);
            let found = self.b.create_block(&[]);
            let next = self.b.create_block(&[]);
            self.b.cond_br(is, found, &[], next, &[]);
            self.start_block(found);
            self.store_tag(dst, opt, 1);
            let inner = self.payload_at(dst, opt, 1, 0);
            self.store_tag(inner, enum_ty, k as u32);
            self.b.br(join, &[]);
            self.start_block(next);
        }
        self.store_tag(dst, opt, 0);
        self.b.br(join, &[]);
        self.start_block(join);
    }

    /// Write `a.cmp(b)` (an `Ordering`, a C-style enum whose tag is its
    /// value: -1, 0 or 1) to `dst`: `(a > b) - (a < b)`.
    fn compare(&mut self, dst: ValueId, ordering: Ty, a: &TExpr, b: &TExpr) {
        let l = self.expr(a).one();
        let r = self.expr(b).one();
        let lt = self.binary(TBinOp::Cmp(CmpOp::Lt), a.ty, Ty::Bool, l, r, b.ty);
        let gt = self.binary(TBinOp::Cmp(CmpOp::Gt), a.ty, Ty::Bool, l, r, b.ty);
        let sum = self.sum_ir(ordering);
        let tag = self.t.int(sum.tag);
        let lt = self.b.cast(CastOp::ZExt, lt, tag);
        let gt = self.b.cast(CastOp::ZExt, gt, tag);
        let v = self.b.sub(gt, lt, Flags::NONE);
        let addr = self.b.struct_field(dst, sum.ty, 0);
        self.b.store(tag, addr, v, align_of(Ty::Int(sum.tag)));
    }

    /// The storage of an expression whose value lives in memory.
    fn place(&mut self, e: &TExpr) -> ValueId {
        match self.expr(e) {
            Val::Mem(p) => p,
            other => unreachable!("{} lowered to {other:?}", e.ty),
        }
    }

    /// The address of field `i` of the struct of type `ty` at `base`.
    fn field_at(&mut self, base: ValueId, ty: Ty, i: u32) -> ValueId {
        let ir_ty = self.ir_ty(ty);
        self.b.struct_field(base, ir_ty, i)
    }

    /// The address of the element or field an [`TExprKind::Index`] or a
    /// [`TExprKind::Field`] names.
    fn address(&mut self, e: &TExpr) -> ValueId {
        if let TExprKind::Field(base, i) = &e.kind {
            let p = self.place(base);
            return self.field_at(p, base.ty, *i);
        }
        if let TExprKind::Payload(base, v, k) = &e.kind {
            let p = self.place(base);
            return self.payload_at(p, base.ty, *v, *k);
        }
        let TExprKind::Index(base, index) = &e.kind else {
            unreachable!("not an element or a field: {e:?}")
        };
        let base = match self.expr(base) {
            Val::Mem(p) | Val::View(p, _) => p,
            other => unreachable!("indexing {other:?}"),
        };
        let i = self.offset(index);
        let elem = self.ir_ty(e.ty);
        self.b.array_elem(base, elem, i)
    }

    /// An index or a slice bound, as an `i64`. It's proven non-negative, so
    /// zero-extension is exact.
    fn offset(&mut self, index: &TExpr) -> ValueId {
        let i = self.expr(index).one();
        let from = IntTy {
            signed: false,
            ..index.ty.as_int().expect("integer index")
        };
        self.resize(i, from, IntTy::new(false, 64))
    }

    /// The value of type `ty` stored at `addr`.
    fn read(&mut self, addr: ValueId, ty: Ty) -> Val {
        if ty.in_memory() {
            return Val::Mem(addr);
        }
        let ir_ty = self.t.of(ty);
        Val::One(self.b.load(ir_ty, addr, align_of(ty)))
    }

    /// Store `val`, of type `ty`, at `addr`.
    fn write(&mut self, addr: ValueId, val: Val, ty: Ty) {
        match val {
            Val::Mem(src) => self.copy(addr, src, ty),
            Val::One(v) => {
                let ir_ty = self.t.of(ty);
                self.b.store(ir_ty, addr, v, align_of(ty));
            }
            other => unreachable!("storing {other:?} in memory"),
        }
    }

    /// The address of element `k` of the array of `elem` at `base`.
    fn elem_at(&mut self, base: ValueId, elem: Ty, k: ValueId) -> ValueId {
        let ir_ty = self.ir_ty(elem);
        self.b.array_elem(base, ir_ty, k)
    }

    /// Run `body` for each `k` in `0..n` (an `i64`): unrolled when the array
    /// is small, otherwise in a loop.
    fn each_elem(&mut self, n: u64, elem: Ty, mut body: impl FnMut(&mut Self, ValueId)) {
        if n.saturating_mul(scalars(elem)) <= UNROLL_LIMIT {
            for k in 0..n {
                let k = self.b.const_i64(self.t.i64, k as i64);
                body(self, k);
            }
            return;
        }
        let header = self.b.create_block(&[self.t.i64]);
        let body_bb = self.b.create_block(&[]);
        let exit = self.b.create_block(&[]);
        let zero = self.b.const_i64(self.t.i64, 0);
        self.b.br(header, &[zero]);
        self.start_block(header);
        let k = self.b.param(header, 0);
        let end = self.b.const_i64(self.t.i64, n as i64);
        let more = self.b.icmp(IntPred::Ult, k, end);
        self.b.cond_br(more, body_bb, &[], exit, &[]);
        self.start_block(body_bb);
        body(self, k);
        let one = self.b.const_i64(self.t.i64, 1);
        let next = self.b.add(k, one, Flags::nuw());
        self.b.br(header, &[next]);
        self.start_block(exit);
    }

    /// Copy the array or struct of type `ty` at `src` to `dst`, element by
    /// element and field by field. The two are the same value or don't
    /// overlap.
    fn copy(&mut self, dst: ValueId, src: ValueId, ty: Ty) {
        if let Some((elem, n)) = ty.as_array() {
            self.each_elem(n, elem, |this, k| {
                let s = this.elem_at(src, elem, k);
                let d = this.elem_at(dst, elem, k);
                let v = this.read(s, elem);
                this.write(d, v, elem);
            });
            return;
        }
        if let Some(def) = ty.sum() {
            // The tag, then the active variant's payload fields.
            let sum = self.sum_ir(ty);
            let tag_ty = self.t.int(sum.tag);
            let align = align_of(Ty::Int(sum.tag));
            let s = self.b.struct_field(src, sum.ty, 0);
            let d = self.b.struct_field(dst, sum.ty, 0);
            let tag = self.b.load(tag_ty, s, align);
            self.b.store(tag_ty, d, tag, align);
            self.each_payload(tag, ty, |this, v| {
                for (k, f) in def.variants[v as usize].fields.iter().enumerate() {
                    let s = this.payload_at(src, ty, v, k as u32);
                    let d = this.payload_at(dst, ty, v, k as u32);
                    let val = this.read(s, f.ty);
                    this.write(d, val, f.ty);
                }
            });
            return;
        }
        let def = ty.as_struct().expect("copying an array or a struct");
        for (i, f) in def.fields.iter().enumerate() {
            let s = self.field_at(src, ty, i as u32);
            let d = self.field_at(dst, ty, i as u32);
            let v = self.read(s, f.ty);
            self.write(d, v, f.ty);
        }
    }

    /// Whether the arrays or structs of type `ty` at `a` and `b` are equal:
    /// every scalar in one equals the one at the same place in the other.
    fn equal(&mut self, a: ValueId, b: ValueId, ty: Ty) -> ValueId {
        // The result so far, in a slot (promoted to a register from `-O1`),
        // so long arrays can be compared in a loop.
        let acc = self.b.alloca(self.t.bool);
        let yes = self.b.const_bool(true);
        self.b.store(self.t.bool, acc, yes, 1);
        self.equal_into(acc, a, b, ty);
        self.b.load(self.t.bool, acc, 1)
    }

    fn equal_into(&mut self, acc: ValueId, a: ValueId, b: ValueId, ty: Ty) {
        if let Some((elem, n)) = ty.as_array() {
            self.each_elem(n, elem, |this, k| {
                let x = this.elem_at(a, elem, k);
                let y = this.elem_at(b, elem, k);
                this.equal_into(acc, x, y, elem);
            });
        } else if let Some(def) = ty.as_struct() {
            for (i, f) in def.fields.iter().enumerate() {
                let x = self.field_at(a, ty, i as u32);
                let y = self.field_at(b, ty, i as u32);
                self.equal_into(acc, x, y, f.ty);
            }
        } else if let Some(def) = ty.sum() {
            // The same variant, and then the same payload.
            let ta = self.load_tag(a, ty);
            let tb = self.load_tag(b, ty);
            let same = self.b.icmp(IntPred::Eq, ta, tb);
            let so_far = self.b.load(self.t.bool, acc, 1);
            let both = self.b.bin(IrOp::And, so_far, same, Flags::NONE);
            self.b.store(self.t.bool, acc, both, 1);
            if def.variants.iter().all(|v| v.fields.is_empty()) {
                return;
            }
            let payloads = self.b.create_block(&[]);
            let done = self.b.create_block(&[]);
            self.b.cond_br(same, payloads, &[], done, &[]);
            self.start_block(payloads);
            self.each_payload(ta, ty, |this, v| {
                for (k, f) in def.variants[v as usize].fields.iter().enumerate() {
                    let x = this.payload_at(a, ty, v, k as u32);
                    let y = this.payload_at(b, ty, v, k as u32);
                    this.equal_into(acc, x, y, f.ty);
                }
            });
            self.b.br(done, &[]);
            self.start_block(done);
        } else {
            let ir_ty = self.t.of(ty);
            let x = self.b.load(ir_ty, a, align_of(ty));
            let y = self.b.load(ir_ty, b, align_of(ty));
            let same = self.b.icmp(IntPred::Eq, x, y);
            let so_far = self.b.load(self.t.bool, acc, 1);
            let both = self.b.bin(IrOp::And, so_far, same, Flags::NONE);
            self.b.store(self.t.bool, acc, both, 1);
        }
    }

    /// Write the value `e`, of an array or struct type, into the (fresh)
    /// storage at `dst`. A literal is written element by element or field by
    /// field, and a call writes its result there directly.
    fn fill(&mut self, dst: ValueId, e: &TExpr) {
        match &e.kind {
            TExprKind::ArrayLit(elems) => {
                let (elem, _) = e.ty.as_array().expect("an array");
                for (k, el) in elems.iter().enumerate() {
                    let k = self.b.const_i64(self.t.i64, k as i64);
                    let d = self.elem_at(dst, elem, k);
                    self.fill_or_write(d, el);
                }
            }
            TExprKind::StructLit(fields) => {
                for (i, value) in fields {
                    let d = self.field_at(dst, e.ty, *i);
                    self.fill_or_write(d, value);
                }
            }
            TExprKind::Call(f, args) => {
                self.call(*f, args, e.ty, Some(dst));
            }
            TExprKind::Variant(v, values) => {
                self.store_tag(dst, e.ty, *v);
                for (k, value) in values.iter().enumerate() {
                    let d = self.payload_at(dst, e.ty, *v, k as u32);
                    self.fill_or_write(d, value);
                }
            }
            TExprKind::EnumFrom(x) => self.enum_from(dst, e.ty, x),
            TExprKind::Compare(a, b) => self.compare(dst, e.ty, a, b),
            TExprKind::ArrayRepeat(value, n) => {
                let (elem, _) = e.ty.as_array().expect("an array");
                let v = self.expr(value);
                self.each_elem(*n, elem, |this, k| {
                    let d = this.elem_at(dst, elem, k);
                    this.write(d, v, elem);
                });
            }
            _ => {
                let src = self.place(e);
                self.copy(dst, src, e.ty);
            }
        }
    }

    /// Write `e` into the fresh storage at `dst`, whatever its type.
    fn fill_or_write(&mut self, dst: ValueId, e: &TExpr) {
        if e.ty.in_memory() {
            self.fill(dst, e);
        } else {
            let v = self.expr(e);
            self.write(dst, v, e.ty);
        }
    }

    /// `dst = e`, for an existing value at `dst` of `e`'s type. A literal
    /// may read `dst` (`a = [a[1], a[0]]`), and a call may read it through
    /// a parameter, so they're built in a temporary first.
    fn assign_into(&mut self, dst: ValueId, e: &TExpr) {
        if !e.ty.in_memory() {
            let v = self.expr(e);
            self.write(dst, v, e.ty);
            return;
        }
        let src = self.place(e);
        self.copy(dst, src, e.ty);
    }

    /// Change an integer's width: sign- or zero-extend by the source's
    /// signedness, or truncate. Same-width values are unchanged (IR integers
    /// carry no signedness).
    fn resize(&mut self, v: ValueId, from: IntTy, to: IntTy) -> ValueId {
        let target = self.t.int(to);
        if to.bits > from.bits {
            let op = if from.signed {
                CastOp::SExt
            } else {
                CastOp::ZExt
            };
            self.b.cast(op, v, target)
        } else if to.bits < from.bits {
            self.b.cast(CastOp::Trunc, v, target)
        } else {
            v
        }
    }

    fn binary(
        &mut self,
        op: TBinOp,
        operand: Ty,
        result: Ty,
        l: ValueId,
        r: ValueId,
        rhs_ty: Ty,
    ) -> ValueId {
        let signed = operand.as_int().is_some_and(|t| t.signed);
        let proven = if signed { Flags::nsw() } else { Flags::nuw() };
        let ty = self.t.of(result);
        match op {
            TBinOp::Add(Mode::Proven) => self.b.add(l, r, proven),
            TBinOp::Sub(Mode::Proven) => self.b.sub(l, r, proven),
            TBinOp::Mul(Mode::Proven) => self.b.mul(l, r, proven),
            TBinOp::Add(Mode::Wrap) => self.b.add(l, r, Flags::NONE),
            TBinOp::Sub(Mode::Wrap) => self.b.sub(l, r, Flags::NONE),
            TBinOp::Mul(Mode::Wrap) => self.b.mul(l, r, Flags::NONE),
            TBinOp::Add(Mode::Saturate) | TBinOp::Sub(Mode::Saturate) => {
                let it = operand.as_int().expect("integer operands");
                self.saturating(matches!(op, TBinOp::Add(_)), it, ty, l, r)
            }
            TBinOp::Mul(Mode::Saturate) => {
                let it = operand.as_int().expect("integer operands");
                self.saturating_mul(it, ty, l, r)
            }
            TBinOp::Div => self.b.bin(
                if signed { IrOp::SDiv } else { IrOp::UDiv },
                l,
                r,
                Flags::NONE,
            ),
            TBinOp::Rem => self.b.bin(
                if signed { IrOp::SRem } else { IrOp::URem },
                l,
                r,
                Flags::NONE,
            ),
            TBinOp::BitAnd => self.b.bin(IrOp::And, l, r, Flags::NONE),
            TBinOp::BitOr => self.b.bin(IrOp::Or, l, r, Flags::NONE),
            TBinOp::BitXor => self.b.bin(IrOp::Xor, l, r, Flags::NONE),
            TBinOp::Shl | TBinOp::ShlWrap | TBinOp::Shr => {
                let it = operand.as_int().expect("integer operands");
                let amount_ty = rhs_ty.as_int().expect("integer shift amount");
                let mut amount = self.resize(r, amount_ty, it);
                if op == TBinOp::ShlWrap {
                    let mask = self.b.const_i64(ty, i64::from(it.bits) - 1);
                    amount = self.b.bin(IrOp::And, amount, mask, Flags::NONE);
                }
                let ir_op = match op {
                    TBinOp::Shr if signed => IrOp::AShr,
                    TBinOp::Shr => IrOp::LShr,
                    _ => IrOp::Shl,
                };
                self.b.bin(ir_op, l, amount, Flags::NONE)
            }
            // `false < true`, as unsigned integers.
            TBinOp::Cmp(c) if operand == Ty::Bool && !matches!(c, CmpOp::Eq | CmpOp::Ne) => {
                let l = self.b.cast(CastOp::ZExt, l, self.t.i8);
                let r = self.b.cast(CastOp::ZExt, r, self.t.i8);
                let i8_ty = Ty::Int(IntTy::new(false, 8));
                self.binary(op, i8_ty, result, l, r, rhs_ty)
            }
            TBinOp::Cmp(c) => {
                let pred = match (c, signed) {
                    (CmpOp::Eq, _) => IntPred::Eq,
                    (CmpOp::Ne, _) => IntPred::Ne,
                    (CmpOp::Lt, true) => IntPred::Slt,
                    (CmpOp::Lt, false) => IntPred::Ult,
                    (CmpOp::Le, true) => IntPred::Sle,
                    (CmpOp::Le, false) => IntPred::Ule,
                    (CmpOp::Gt, true) => IntPred::Sgt,
                    (CmpOp::Gt, false) => IntPred::Ugt,
                    (CmpOp::Ge, true) => IntPred::Sge,
                    (CmpOp::Ge, false) => IntPred::Uge,
                };
                self.b.icmp(pred, l, r)
            }
        }
    }

    /// Saturating `l * r`. Up to 32 bits, the product is exact in 64 bits:
    /// clamp it there. For 64 bits, the wrapped product `p` overflowed iff
    /// `l != 0` and `p / l != r` (an exact product divides back; a wrapped
    /// one differs from it by a multiple of 2^64, more than `|l|`), except
    /// for `l == -1`, which overflows only with `r == MIN` and can't be the
    /// divisor (`MIN / -1` traps). The divisor is 1 in those cases.
    fn saturating_mul(&mut self, it: IntTy, ty: TypeId, l: ValueId, r: ValueId) -> ValueId {
        if it.bits <= 32 {
            let wide = IntTy {
                signed: it.signed,
                bits: 64,
                size: false,
            };
            let wide_ty = self.t.int(wide);
            let (lw, rw) = (self.resize(l, it, wide), self.resize(r, it, wide));
            let product = self.b.mul(lw, rw, Flags::NONE);
            let (gt, lt) = if it.signed {
                (IntPred::Sgt, IntPred::Slt)
            } else {
                (IntPred::Ugt, IntPred::Ult)
            };
            // The bounds as 64-bit constants (both fit in an `i64`).
            let max = self.b.const_i64(wide_ty, it.max() as i64);
            let min = self.b.const_i64(wide_ty, it.min() as i64);
            let above = self.b.icmp(gt, product, max);
            let clamped = self.b.select(above, max, product);
            let below = self.b.icmp(lt, clamped, min);
            let clamped = self.b.select(below, min, clamped);
            return self.resize(clamped, wide, it);
        }
        let wrapped = self.b.mul(l, r, Flags::NONE);
        let zero = self.b.const_i64(ty, 0);
        let one = self.b.const_i64(ty, 1);
        let l_zero = self.b.icmp(IntPred::Eq, l, zero);
        if !it.signed {
            let divisor = self.b.select(l_zero, one, l);
            let back = self.b.bin(IrOp::UDiv, wrapped, divisor, Flags::NONE);
            let differs = self.b.icmp(IntPred::Ne, back, r);
            let f = self.b.const_bool(false);
            let overflow = self.b.select(l_zero, f, differs);
            let max = self.b.const_i64(ty, -1);
            return self.b.select(overflow, max, wrapped);
        }
        let minus_one = self.b.const_i64(ty, -1);
        let min = self.b.const_i64(ty, const_bits(it.min(), it));
        let max = self.b.const_i64(ty, const_bits(it.max(), it));
        let l_minus_one = self.b.icmp(IntPred::Eq, l, minus_one);
        let unsafe_divisor = self.b.bin(IrOp::Or, l_zero, l_minus_one, Flags::NONE);
        let divisor = self.b.select(unsafe_divisor, one, l);
        let back = self.b.bin(IrOp::SDiv, wrapped, divisor, Flags::NONE);
        let differs = self.b.icmp(IntPred::Ne, back, r);
        let r_min = self.b.icmp(IntPred::Eq, r, min);
        let f = self.b.const_bool(false);
        let overflow = self.b.select(l_zero, f, differs);
        let overflow = self.b.select(l_minus_one, r_min, overflow);
        // On overflow, neither operand is 0: the true product is negative
        // (past MIN) iff exactly one of them is.
        let signs = self.b.bin(IrOp::Xor, l, r, Flags::NONE);
        let negative = self.b.icmp(IntPred::Slt, signs, zero);
        let bound = self.b.select(negative, min, max);
        self.b.select(overflow, bound, wrapped)
    }

    /// Saturating `l + r` or `l - r`: compute the wrapped result, detect
    /// overflow from the operand and result signs, and select the bound.
    fn saturating(&mut self, add: bool, it: IntTy, ty: TypeId, l: ValueId, r: ValueId) -> ValueId {
        let wrapped = if add {
            self.b.add(l, r, Flags::NONE)
        } else {
            self.b.sub(l, r, Flags::NONE)
        };
        if !it.signed {
            // Unsigned: an addition overflowed if the result is below an
            // operand; a subtraction if the subtrahend was larger.
            let (overflow, bound) = if add {
                (
                    self.b.icmp(IntPred::Ult, wrapped, l),
                    self.b.const_i64(ty, -1),
                )
            } else {
                (self.b.icmp(IntPred::Ult, l, r), self.b.const_i64(ty, 0))
            };
            return self.b.select(overflow, bound, wrapped);
        }
        // Signed: overflow iff the result's sign differs from what the operands
        // allow: add: (l ^ s) & (r ^ s) < 0; sub: (l ^ r) & (l ^ s) < 0.
        let ls = self.b.bin(IrOp::Xor, l, wrapped, Flags::NONE);
        let other = if add {
            self.b.bin(IrOp::Xor, r, wrapped, Flags::NONE)
        } else {
            self.b.bin(IrOp::Xor, l, r, Flags::NONE)
        };
        let both = self.b.bin(IrOp::And, ls, other, Flags::NONE);
        let zero = self.b.const_i64(ty, 0);
        let overflow = self.b.icmp(IntPred::Slt, both, zero);
        // On overflow the true result is past MIN if l is negative, else past MAX.
        let l_negative = self.b.icmp(IntPred::Slt, l, zero);
        let min = self.b.const_i64(ty, const_bits(it.min(), it));
        let max = self.b.const_i64(ty, const_bits(it.max(), it));
        let bound = self.b.select(l_negative, min, max);
        self.b.select(overflow, bound, wrapped)
    }
}
