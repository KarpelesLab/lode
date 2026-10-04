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
//! writer emits.
//!
//! Arrays live in memory. An array-typed expression lowers to a pointer to
//! its storage ([`Val::Mem`]): a local's slot, an element of another array,
//! or a temporary slot that a literal is written into. Copying an array
//! copies its elements, one by one or in a loop for longer arrays. Array
//! slots and temporaries are `alloca`s, which LF gives static frame slots.

use latticefoundry::Module;
use latticefoundry::ir::builder::FunctionBuilder;
use latticefoundry::ir::{
    BinOp as IrOp, BlockId, CastOp, Const, Flags, FuncAttrs, FuncId as IrFunc, Global, GlobalId,
    IntPred, Linkage, TypeId, ValueId, Visibility,
};
use latticefoundry::support::StrInterner;

use crate::reach::Reach;
use crate::sema::{CmpOp, Func, Mode, Program, TBinOp, TExpr, TExprKind, TStmt, TUnOp};
use crate::types::{IntTy, Ty};

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
            Ty::Array(_) => unreachable!("an array lives in memory"),
        }
    }

    /// The IR values a Lode value is made of, as parameter types.
    fn parts(&self, ty: Ty) -> Vec<TypeId> {
        match ty {
            Ty::Unit => Vec::new(),
            Ty::Str | Ty::Slice(_) => vec![self.ptr, self.i64],
            _ => vec![self.of(ty)],
        }
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
    /// An array: a pointer to its storage.
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
            Val::Mem(_) => unreachable!("arrays aren't passed by value"),
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
    /// An array's storage.
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
    let reach = match program.main {
        Some(main) => Reach::from(program, main),
        None => Reach::all(program),
    };
    // `main` is the entry itself unless Lode code calls it.
    let direct_entry = program.main.filter(|_| !reach.root_called);

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

    let internal = FuncAttrs::new(Linkage::Internal, Visibility::Default);
    let ids: Vec<Option<IrFunc>> = program
        .funcs
        .iter()
        .enumerate()
        .map(|(i, f)| {
            if !reach.reached[i] {
                return None;
            }
            let params = f
                .params
                .iter()
                .flat_map(|&p| t.parts(f.locals[p].ty))
                .collect();
            let is_entry = direct_entry == Some(i);
            let ret = if is_entry { t.i64 } else { t.of(f.ret) };
            let sig = module.types_mut().func(params, ret, false);
            let id = module.declare_function(syms.intern(&f.symbol), sig);
            if !is_entry {
                module.set_func_attrs(id, internal.clone());
            }
            Some(id)
        })
        .collect();

    for (i, f) in program.funcs.iter().enumerate() {
        let Some(id) = ids[i] else { continue };
        let b = module.build(id);
        FnLower {
            b,
            t,
            ids: &ids,
            strings: &string_globals,
            string_lens: &program.strings,
            slots: Vec::new(),
            loops: Vec::new(),
            terminated: false,
            exit_status: (direct_entry == Some(i)).then_some(f.ret),
        }
        .function(f);
    }

    let entry = match (program.main, direct_entry) {
        (Some(main), None) => {
            let sig = module.types_mut().func(Vec::new(), t.i64, false);
            let entry = module.declare_function(syms.intern(ENTRY_WRAPPER), sig);
            let ret = program.funcs[main].ret;
            let mut b = module.build(entry);
            b.create_entry_block();
            let callee = b.func_ref(ids[main].expect("main is reached"));
            let result = b.call(callee, &[], t.of(ret));
            let status = exit_status(&mut b, t, ret, result);
            b.ret(Some(status));
            Some(ENTRY_WRAPPER.to_owned())
        }
        (Some(main), Some(_)) => Some(program.funcs[main].symbol.clone()),
        (None, _) => None,
    };

    Lowered {
        module,
        syms,
        entry,
        strings,
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
    slots: Vec<Slot>,
    /// `(continue target, break target)` of each enclosing loop.
    loops: Vec<(BlockId, BlockId)>,
    /// Whether the current block already has its terminator.
    terminated: bool,
    /// For the entry function, `main`'s return type: its returns become
    /// `i64` exit statuses.
    exit_status: Option<Ty>,
}

/// The most scalar copies an array copy or fill is unrolled into; longer
/// arrays are copied in a loop.
const UNROLL_LIMIT: u64 = 16;

/// The number of scalars in a value of type `ty`.
fn scalars(ty: Ty) -> u64 {
    match ty.as_array() {
        Some((elem, n)) => n.saturating_mul(scalars(elem)),
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
        for local in &f.locals {
            let slot = match local.ty {
                Ty::Str | Ty::Slice(_) => Slot::View {
                    ptr: self.b.alloca(self.t.ptr),
                    len: self.b.alloca(self.t.i64),
                },
                ty @ Ty::Array(_) => {
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
        let mut next = 0;
        for &p in &f.params {
            let val = match f.locals[p].ty {
                Ty::Str | Ty::Slice(_) => {
                    let v = Val::View(self.b.param(entry, next), self.b.param(entry, next + 1));
                    next += 2;
                    v
                }
                _ => {
                    next += 1;
                    Val::One(self.b.param(entry, next - 1))
                }
            };
            self.store(p, val);
        }
        self.stmts(&f.body);
        if !self.terminated {
            if f.ret == Ty::Unit {
                self.ret(None);
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

    fn stmts(&mut self, stmts: &[TStmt]) {
        for s in stmts {
            if self.terminated {
                // Code after a `return`/`break`: give it a fresh (unreachable) block.
                let dead = self.b.create_block(&[]);
                self.start_block(dead);
            }
            self.stmt(s);
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
            TStmt::Return(value) => {
                let v = value.as_ref().map(|e| self.expr(e).one());
                self.ret(v);
                self.terminated = true;
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
                let (cont, brk) = *self.loops.last().expect("checked: inside a loop");
                let target = if matches!(s, TStmt::Break) { brk } else { cont };
                self.b.br(target, &[]);
                self.terminated = true;
            }
            TStmt::Block(body) => self.stmts(body),
        }
    }

    fn loop_body(&mut self, body_bb: BlockId, cont: BlockId, exit: BlockId, body: &[TStmt]) {
        self.start_block(body_bb);
        self.loops.push((cont, exit));
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
            TExprKind::Local(local) => return self.load(*local),
            TExprKind::Call(f, args) => {
                let args: Vec<ValueId> = args.iter().flat_map(|a| self.expr(a).parts()).collect();
                let callee = self.b.func_ref(self.ids[*f].expect("a reached function"));
                let ret_ty = self.t.of(e.ty);
                return match self.b.call(callee, &args, ret_ty) {
                    Some(v) => Val::One(v),
                    None => Val::Unit,
                };
            }
            TExprKind::Syscall(args) => {
                let ops: Vec<ValueId> = args.iter().map(|a| self.syscall_operand(a)).collect();
                self.b.syscall(ops[0], &ops[1..])
            }
            TExprKind::ViewLen(s) => match self.expr(s) {
                Val::View(_, n) => n,
                other => unreachable!("`len` of {other:?}"),
            },
            TExprKind::StrPtr(s) => match self.expr(s) {
                Val::View(p, _) => p,
                other => unreachable!("`ptr` of {other:?}"),
            },
            TExprKind::ArrayLen(a) => {
                self.expr(a);
                let (_, n) = a.ty.as_array().expect("an array");
                self.b.const_i64(self.t.i64, n as i64)
            }
            TExprKind::ArrayLit(_) | TExprKind::ArrayRepeat(..) => {
                let ir_ty = self.ir_ty(e.ty);
                let tmp = self.b.alloca(ir_ty);
                self.fill(tmp, e);
                return Val::Mem(tmp);
            }
            TExprKind::Index(..) => {
                let addr = self.address(e);
                return self.read(addr, e.ty);
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

    /// The IR type of a value stored in memory: a scalar, or an array of them.
    fn ir_ty(&mut self, ty: Ty) -> TypeId {
        match ty.as_array() {
            Some((elem, n)) => {
                let elem = self.ir_ty(elem);
                self.b.types_mut().array(elem, n)
            }
            None => self.t.of(ty),
        }
    }

    /// The storage of an array-typed expression.
    fn place(&mut self, e: &TExpr) -> ValueId {
        match self.expr(e) {
            Val::Mem(p) => p,
            other => unreachable!("an array lowered to {other:?}"),
        }
    }

    /// The address of the element an [`TExprKind::Index`] names.
    fn address(&mut self, e: &TExpr) -> ValueId {
        let TExprKind::Index(base, index) = &e.kind else {
            unreachable!("not an element: {e:?}")
        };
        let base = match self.expr(base) {
            Val::Mem(p) | Val::View(p, _) => p,
            other => unreachable!("indexing {other:?}"),
        };
        let i = self.expr(index).one();
        // The index is proven non-negative, so zero-extension is exact.
        let from = IntTy {
            signed: false,
            ..index.ty.as_int().expect("integer index")
        };
        let i = self.resize(i, from, IntTy::new(false, 64));
        let elem = self.ir_ty(e.ty);
        self.b.array_elem(base, elem, i)
    }

    /// The value of type `ty` stored at `addr`.
    fn read(&mut self, addr: ValueId, ty: Ty) -> Val {
        if ty.as_array().is_some() {
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

    /// Copy the array of type `ty` at `src` to `dst`, element by element.
    /// The two are the same array or don't overlap.
    fn copy(&mut self, dst: ValueId, src: ValueId, ty: Ty) {
        let (elem, n) = ty.as_array().expect("copying an array");
        self.each_elem(n, elem, |this, k| {
            let s = this.elem_at(src, elem, k);
            let d = this.elem_at(dst, elem, k);
            let v = this.read(s, elem);
            this.write(d, v, elem);
        });
    }

    /// Write the array value `e` into the (fresh) storage at `dst`. A literal
    /// is written element by element.
    fn fill(&mut self, dst: ValueId, e: &TExpr) {
        let (elem, _) = e.ty.as_array().expect("filling an array");
        match &e.kind {
            TExprKind::ArrayLit(elems) => {
                for (k, el) in elems.iter().enumerate() {
                    let k = self.b.const_i64(self.t.i64, k as i64);
                    let d = self.elem_at(dst, elem, k);
                    if el.ty.as_array().is_some() {
                        self.fill(d, el);
                    } else {
                        let v = self.expr(el);
                        self.write(d, v, elem);
                    }
                }
            }
            TExprKind::ArrayRepeat(value, n) => {
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

    /// `dst = e`, for an existing value at `dst` of `e`'s type. A literal
    /// may read `dst` (`a = [a[1], a[0]]`), so it's built in a temporary
    /// first.
    fn assign_into(&mut self, dst: ValueId, e: &TExpr) {
        if e.ty.as_array().is_none() {
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
            TBinOp::Mul(Mode::Saturate) => unreachable!("rejected by the checker"),
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
