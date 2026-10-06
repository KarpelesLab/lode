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
//! storage for the result as its first IR parameter and returns nothing.
//! The caller passes fresh storage: a new local's slot for `let x = f()`,
//! otherwise a temporary that's then copied, so the callee never writes to
//! something it can also read through a parameter.
//!
//! A function that throws returns a result `throws(E) -> T`, which is an
//! enum `{ ok(T), err(E) }` with a `u8` tag, `ok` 0 and `err` 1. `return v`
//! makes `ok(v)`; `throw e` makes `err(e)`. There is no unwinding: an error
//! is a return value.
//!
//! Small results are returned in a register instead, packed in an `i64`.
//! The packed form of a value is defined for these types only:
//! - `()`: 0 bits. `bool`: 1 bit. An integer: its width, its bits as they
//!   are (a signed one isn't sign-extended).
//! - An enum, an optional or a result: its tag in the low bits (the width
//!   of its tag type, a `u8` unless a C-style enum declares another, as
//!   the bits of the tag value), then the active variant's payload fields
//!   in declaration order, each in its packed form, from the lowest bits
//!   up. It has a packed form when every payload field of every variant
//!   has one, and the tag plus the largest payload is at most 64 bits.
//!   Bits above the active variant's fields are 0.
//!
//! Arrays, structs, views and pointers have no packed form. A function
//! whose result (its return type, or its result type if it throws) is an
//! enum, an optional or a result with a packed form returns it as an
//! `i64` and takes no result pointer. So `throws(E) -> ()`, `-> u8`,
//! `-> u32`, `-> bool` and `-> ?u16` are packed when `E` is an enum whose
//! payloads fit, as is a C-style enum, `?u8` or `?u32`; `throws(E) ->
//! u64`, `-> usize` and `?usize` are not (72 bits), nor is any result with
//! a struct inside. Values in packed form are never passed: the caller
//! tests and takes apart the `i64` itself for `try`, `catch`, `??` and
//! `==`, and unpacks it into memory where a value in memory is needed.
//!
//! A local of such a type is kept in packed form, in an `i64` slot that
//! mem2reg promotes, when it's only matched, compared and assigned
//! ([`packed_locals`]). That covers the hidden local a `match`, an `if
//! let` or a `let ... else` on a call stores its value in. The packed form
//! of a value is unique, so `==` compares two packed values as integers.
//!
//! A struct local is split into one slot per scalar field (recursively
//! through nested structs), each promoted by mem2reg on its own, when it's
//! only used field by field ([`split_locals`] has the exact rule): `p.x`
//! reads a slot, `p.x = v` writes one, `let p = e` and `p = e` write them
//! all (from a literal field by field, or from a value in memory scalar by
//! scalar), `==` compares them pairwise, and a copy into memory (`return
//! p`, a field of a literal) stores each one. A local passed to a call,
//! read whole any other way, or whose address is taken (`&p`) stays in
//! memory: copying it into a temporary for such a use costs more than the
//! split saves. `&p.x` of a scalar field is that field's slot.
//!
//! A local that a loop body declares, and that nothing outside the body
//! names, is dead at the end of each iteration: poison is stored in its
//! slots there ([`iteration_locals`]), so mem2reg doesn't carry its value
//! around the loop.
//!
//! `defer` bodies are emitted at each exit of their block, in reverse
//! order: at its end, and at every `return`, `throw`, failing `try`,
//! `break` and `continue` that leaves it. `errdefer` bodies only at the
//! exits that leave the function with an error.
//!
//! Destruction (docs/allocation.md, When destruction runs) goes with them:
//! a `TStmt::Drop` registers its local where a `defer` would be, and each
//! exit destroys it, by a call of the function [`crate::mono`] gives its
//! type (its `deinit`, or one that destroys its parts) with the local's
//! address. A local the checker gave a drop flag ([`Local::drop_flag`])
//! has a `bool` slot saying whether it holds a value: a move clears it, an
//! assignment sets it, and destruction tests it. mem2reg promotes it, and
//! the optimizer folds it where the paths are known. An assignment to a
//! place that holds a value destroys the old value after the new one is
//! computed. A local whose type needs destruction is always in memory
//! (never split or packed), since destruction takes its address.
//!
//! While an array, a struct, a variant or a call's arguments are built,
//! the parts already built that need destruction are registered too, until
//! the value is complete: a `try` (or another early exit) in a later part
//! destroys them, so a value built into an aggregate that never completes
//! is destroyed once (docs/allocation.md, M8b in the compiler).
//!
//! A `static` is a global in `.bss` (or `.data`, when its value isn't all
//! zeros), which the object defines ([`Lowered::data`]).
//!
//! The allocator context (docs/allocation.md, Lowering the context): when
//! the program has allocator types besides the root's
//! ([`Instances::dynamic_alloc`]), a function that `uses alloc` takes one
//! more parameter, last: the address of the handle in context (an
//! `alloc.Handle`: its allocator's number and address). `main` makes the
//! root's, and `with alloc = h` passes `h`'s. Otherwise there's no such
//! parameter, and `alloc.Handle` has no fields: it's zero-sized, in boxes
//! too.

use std::collections::HashMap;
use std::rc::Rc;

use latticefoundry::Module;
use latticefoundry::ir::builder::FunctionBuilder;
use latticefoundry::ir::{
    BinOp as IrOp, BlockId, CastOp, Const, Flags, FuncAttrs, FuncId as IrFunc, Global, GlobalId,
    IntPred, Linkage, TypeContext, TypeId, ValueId, Visibility,
};
use latticefoundry::support::StrInterner;

use crate::mono::{self, Instances};
use crate::sema::{
    CmpOp, Convention, Func, Handler, Intrinsic, Local, LocalId, Mode, Program, TBinOp, TExpr,
    TExprKind, TStmt, TUnOp,
};
use crate::source::{FileId, SourceMap};
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

/// What leaving a statement list runs, registered as it's lowered.
#[derive(Clone)]
enum Defer {
    /// A `defer` body, whether it's an `errdefer`, and how many handles
    /// were in context where it was written (its calls use the
    /// innermost of those, wherever it runs).
    Body(Rc<[TStmt]>, bool, usize),
    /// The destruction of a local that owns its value (`TStmt::Drop`).
    Drop(LocalId),
    /// The destruction of a part of an aggregate being built, at this
    /// address, of this type, until the aggregate is complete.
    Place(ValueId, Ty),
}

/// The width of a result's tag (a `u8`), below its payload in the packed
/// form.
const RESULT_TAG_BITS: u32 = 8;

/// The width of an optional's tag (a `u8`).
const OPTIONAL_TAG_BITS: u32 = 8;

/// A result a call returned.
#[derive(Clone, Copy)]
enum Outcome {
    /// In memory, at this address.
    Mem(ValueId),
    /// Packed in an `i64`.
    Packed(ValueId),
}

/// The error a function leaves with.
#[derive(Clone, Copy)]
enum Failure<'e> {
    /// `throw e`.
    Expr(&'e TExpr),
    /// A `try` passing on an error in memory, at this address.
    Mem(ValueId),
    /// A `try` passing on a packed result (of the same error type) whose
    /// variant is `err`.
    Packed(ValueId),
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
    /// The functions defined, and whether each is internal (only called
    /// from the module: optimization may leave it unreferenced).
    pub funcs: Vec<(IrFunc, bool)>,
    /// With debug information ([`lower_debug`]), the source line of each
    /// IR line number: line `n` is `(file, line)` at index `n - 1`. IR
    /// line numbers stand for a file and a line, as LatticeFoundry's
    /// debug information only has one source file. Empty otherwise.
    pub lines: Vec<(FileId, u32)>,
    /// The writable data the object must define for each `static` the
    /// program uses: `(symbol, bytes, alignment)`, in `.bss` when the
    /// bytes are all zeros.
    pub data: Vec<(String, Vec<u8>, u64)>,
}

/// The IR line numbers given so far, for debug information (see
/// [`Lowered::lines`]).
#[derive(Default)]
struct Lines {
    ids: HashMap<(FileId, u32), u32>,
    table: Vec<(FileId, u32)>,
}

impl Lines {
    /// The IR line number of `line` (1-based) of `file`.
    fn id(&mut self, file: FileId, line: u32) -> u32 {
        *self.ids.entry((file, line)).or_insert_with(|| {
            self.table.push((file, line));
            self.table.len() as u32
        })
    }
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
            // A `never` function returns nothing: its calls are followed by
            // `unreachable`.
            Ty::Unit | Ty::Never => self.void,
            Ty::Bool => self.bool,
            Ty::Int(t) => self.int(t),
            Ty::Ptr(_) => self.ptr,
            Ty::Str | Ty::Slice(_) => unreachable!("a view is two values"),
            Ty::Array(_) | Ty::Struct(_) | Ty::Enum(_) | Ty::Optional(_) | Ty::Result(_) => {
                unreachable!("{ty} lives in memory")
            }
            Ty::Param(_) | Ty::Value(_) => unreachable!("instances have concrete types"),
        }
    }

    /// The IR values a Lode value is made of, as parameter types.
    fn parts(&self, ty: Ty) -> Vec<TypeId> {
        match ty {
            Ty::Unit | Ty::Never => Vec::new(),
            Ty::Str | Ty::Slice(_) => vec![self.ptr, self.i64],
            _ if ty.in_memory() => vec![self.ptr],
            _ => vec![self.of(ty)],
        }
    }

    /// A function's IR parameter and return types. A result in memory is
    /// written through a pointer passed first (see the module docs); with
    /// `ctx`, the address of the handle in context comes last.
    fn signature(&self, f: &Func, ctx: bool) -> (Vec<TypeId>, TypeId) {
        let mut params = Vec::new();
        let result = f.result_ty();
        let ret = if returns_packed(result) {
            self.i64
        } else if result.in_memory() || result.is_view() {
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
        if ctx {
            params.push(self.ptr);
        }
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
    /// An `i64` slot holding a value in packed form (see
    /// [`packed_locals`]), of this type.
    Packed(ValueId, Ty),
    /// A struct split into one slot per scalar ([`split_locals`]): the
    /// index of its slots in [`FnLower::splits`].
    Split(usize),
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
    lower_with(program, name, None)
}

/// [`lower`], with source lines for debug information: each instruction
/// gets the IR line number ([`Lowered::lines`]) of the statement it's
/// from, and each function the one of its declaration.
pub fn lower_debug(program: &Program, name: &str, files: &SourceMap) -> Lowered {
    lower_with(program, name, Some(files))
}

fn lower_with(program: &Program, name: &str, files: Option<&SourceMap>) -> Lowered {
    let mut lines = Lines::default();
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
    let dynamic = reach.dynamic_alloc();
    // With only the root allocator, a handle holds nothing.
    if let Some(info) = program.alloc
        && !dynamic
    {
        info.handle.set_fields(Vec::new());
    }

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

    // The `static`s used: globals the object defines, with their initial
    // values' bytes.
    let mut data = Vec::new();
    let mut static_globals = Vec::new();
    for (i, st) in program.statics.iter().enumerate() {
        if !reach.statics[i] {
            static_globals.push(None);
            continue;
        }
        let ty = ir_type(module.types_mut(), t, st.ty);
        let layout = module.types().layout(ty);
        let mut bytes = vec![0u8; layout.size as usize];
        static_bytes(module.types_mut(), t, &st.init, &mut bytes, 0);
        let init = module.intern_const(Const::Poison(ty));
        static_globals.push(Some(module.add_global(Global {
            name: syms.intern(&st.symbol),
            ty,
            init: Some(init),
        })));
        data.push((st.symbol.clone(), bytes, layout.align));
    }
    let root_static = program
        .alloc
        .filter(|_| !reach.allocators.is_empty())
        .and_then(|info| static_globals[info.root]);
    // With only the root allocator, a call through a handle is a call of
    // the root's method, directly: the dispatch functions aren't made.
    let redirect: HashMap<usize, usize> = if dynamic {
        HashMap::new()
    } else {
        reach
            .dispatch
            .iter()
            .copied()
            .filter(|&(d, root)| reach.funcs[d].result_ty() == reach.funcs[root].result_ty())
            .collect()
    };

    let internal = FuncAttrs::new(Linkage::Internal, Visibility::Default);
    let ids: Vec<Option<IrFunc>> = reach
        .funcs
        .iter()
        .enumerate()
        .map(|(i, f)| {
            if redirect.contains_key(&i) {
                return None;
            }
            let is_entry = direct_entry == Some(i);
            let (params, ret) = t.signature(f, dynamic && f.uses_alloc && !is_entry);
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
            reach: &reach,
            locals: &f.locals,
            flags: Vec::new(),
            ids: &ids,
            strings: &string_globals,
            string_lens: &program.strings,
            tables: &table_globals,
            statics: &static_globals,
            root_static,
            redirect: &redirect,
            handle: program.alloc.map(|a| a.handle),
            ctx: Vec::new(),
            dynamic,
            slots: Vec::new(),
            splits: Vec::new(),
            addrs: HashMap::new(),
            loops: Vec::new(),
            names: Vec::new(),
            defers: Vec::new(),
            terminated: false,
            exit_status: (direct_entry == Some(i)).then_some(f.ret),
            result: None,
            result_ty: f.result_ty(),
            packed: returns_packed(f.result_ty()),
            throws: f.throws.is_some(),
            files,
            lines: &mut lines,
            line: 0,
        }
        .function(f);
    }

    let mut funcs: Vec<(IrFunc, bool)> = ids
        .iter()
        .enumerate()
        .filter_map(|(i, id)| id.map(|id| (id, direct_entry != Some(i))))
        .collect();
    let entry = match (reach.main, direct_entry) {
        (Some(main), None) => {
            let sig = module.types_mut().func(Vec::new(), t.i64, false);
            let entry = module.declare_function(syms.intern(ENTRY_WRAPPER), sig);
            funcs.push((entry, false));
            let ret = reach.funcs[main].ret;
            let mut b = module.build(entry);
            if let Some(files) = files {
                let span = reach.funcs[main].span;
                let (line, _) = files.get(span.file).line_col(span.start);
                let id = lines.id(span.file, line);
                b.set_decl_line(id);
                b.set_line(id);
            }
            b.create_entry_block();
            let callee = b.func_ref(ids[main].expect("main is reached"));
            // `main` that `uses alloc` gets the root allocator.
            let mut args = Vec::new();
            if dynamic && reach.funcs[main].uses_alloc {
                let handle = program.alloc.expect("a program that allocates").handle;
                let ty = ir_type(b.types_mut(), t, handle);
                let h = b.alloca(ty);
                let root = b.global_ref(root_static.expect("the root allocator is used"));
                write_root_handle(&mut b, t, ty, h, root);
                args.push(h);
            }
            let result = b.call(callee, &args, t.of(ret));
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
        funcs,
        lines: lines.table,
        data,
    }
}

/// Write the root allocator's handle at `h` (of the IR type `ty`): number
/// 0, and the address of the root, `root`.
fn write_root_handle(b: &mut FunctionBuilder<'_>, t: Types, ty: TypeId, h: ValueId, root: ValueId) {
    let zero = b.const_i64(t.i64, 0);
    b.store(t.i64, h, zero, 8);
    let addr = b.cast(CastOp::PtrToInt, root, t.i64);
    let (offset, _) = b.types().field_offset(ty, 1);
    let off = b.const_i64(t.i64, offset as i64);
    let at = b.ptr_add(h, off, true);
    b.store(t.i64, at, addr, 8);
}

/// The IR type of a value of type `ty` stored in memory: a scalar, or an
/// array, a struct, an enum or an optional of them (see the module docs).
fn ir_type(types: &mut TypeContext, t: Types, ty: Ty) -> TypeId {
    if let Some((elem, n)) = ty.as_known_array() {
        let elem = ir_type(types, t, elem);
        return types.array(elem, n);
    }
    if ty.sum().is_some() {
        return sum_layout(types, t, ty).ty;
    }
    match ty.as_struct() {
        Some(def) => {
            let fields = def.fields.iter().map(|f| ir_type(types, t, f.ty)).collect();
            types.struct_(fields)
        }
        None => t.of(ty),
    }
}

/// The IR layout of an enum, an optional or a result (see the module
/// docs).
fn sum_layout(types: &mut TypeContext, t: Types, ty: Ty) -> SumIr {
    let def = ty.sum().expect("an enum or an optional");
    let tag = t.int(def.tag);
    let payloads: Vec<Option<TypeId>> = def
        .variants
        .iter()
        .map(|v| {
            if v.fields.is_empty() {
                return None;
            }
            let fields = v.fields.iter().map(|f| ir_type(types, t, f.ty)).collect();
            Some(types.struct_(fields))
        })
        .collect();
    let (mut size, mut align) = (0, 1);
    for &p in payloads.iter().flatten() {
        let layout = types.layout(p);
        size = size.max(layout.size);
        align = align.max(layout.align);
    }
    let ir = if size == 0 {
        types.struct_(vec![tag])
    } else {
        let word = types.int(align as u32 * 8);
        let area = types.array(word, size.div_ceil(align));
        types.struct_(vec![tag, area])
    };
    SumIr {
        ty: ir,
        tag: def.tag,
        payloads,
        values: def.variants.iter().map(|v| v.value).collect(),
    }
}

/// Write the bytes of the literal `e` (a `static`'s value: integers,
/// `bool`s, and arrays, structs and variants of them) at `at` in `out`,
/// laid out as its IR type.
fn static_bytes(types: &mut TypeContext, t: Types, e: &TExpr, out: &mut [u8], at: u64) {
    let mut put = |v: i128, size: u64| {
        let bytes = v.to_le_bytes();
        out[at as usize..(at + size) as usize].copy_from_slice(&bytes[..size as usize]);
    };
    match &e.kind {
        TExprKind::Int(v) => {
            let size = types.layout(t.of(e.ty)).size;
            put(*v, size);
        }
        TExprKind::Bool(b) => put(i128::from(*b), 1),
        TExprKind::ArrayLit(items) => {
            let (elem, _) = e.ty.as_known_array().expect("an array");
            let ir = ir_type(types, t, elem);
            let stride = types.stride(ir);
            for (k, item) in items.iter().enumerate() {
                static_bytes(types, t, item, out, at + stride * k as u64);
            }
        }
        TExprKind::ArrayRepeat(item) => {
            let (elem, n) = e.ty.as_known_array().expect("an array");
            let ir = ir_type(types, t, elem);
            let stride = types.stride(ir);
            for k in 0..n {
                static_bytes(types, t, item, out, at + stride * k);
            }
        }
        TExprKind::StructLit(fields) => {
            let ir = ir_type(types, t, e.ty);
            for (i, v) in fields {
                let (offset, _) = types.field_offset(ir, *i);
                static_bytes(types, t, v, out, at + offset);
            }
        }
        TExprKind::Variant(k, values) => {
            let sum = sum_layout(types, t, e.ty);
            let tag_size = types.layout(t.int(sum.tag)).size;
            let tag = const_bits(sum.values[*k as usize], sum.tag);
            put(i128::from(tag), tag_size);
            if let Some(payload) = sum.payloads[*k as usize] {
                let (area, _) = types.field_offset(sum.ty, 1);
                for (j, v) in values.iter().enumerate() {
                    let (offset, _) = types.field_offset(payload, j as u32);
                    static_bytes(types, t, v, out, at + area + offset);
                }
            }
        }
        other => unreachable!("a static's value is a literal, found {other:?}"),
    }
}

/// Whether evaluating `e` may leave the statement it's in before it's
/// done: a `try`, a `throw` (after `??`), or the block of a `catch`.
fn may_leave(e: &TExpr) -> bool {
    match &e.kind {
        TExprKind::Try(_) | TExprKind::Throw(_) => true,
        TExprKind::Catch {
            handler: Handler::Block(body),
            ..
        } if !body.is_empty() => true,
        _ => crate::sema::subexprs(e).into_iter().any(may_leave),
    }
}

/// For each of `parts`, whether a part after it may leave early (see
/// [`may_leave`]).
fn later_leaves<'e>(parts: impl DoubleEndedIterator<Item = &'e TExpr>) -> Vec<bool> {
    let mut out: Vec<bool> = Vec::new();
    let mut any = false;
    for p in parts.rev() {
        out.push(any);
        any |= may_leave(p);
    }
    out.reverse();
    out
}

/// The IR type of an array of scalars (or of arrays of them), built at
/// module level, before any function.
fn ir_array(types: &mut latticefoundry::ir::TypeContext, t: Types, ty: Ty) -> TypeId {
    match ty.as_known_array() {
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
    /// The program's instances: their parameters' conventions, and the
    /// destruction of each type.
    reach: &'a Instances,
    /// The function's locals.
    locals: &'a [Local],
    /// The drop flag of each local that has one (see the module docs).
    flags: Vec<Option<ValueId>>,
    /// The IR function of each reached function.
    ids: &'a [Option<IrFunc>],
    strings: &'a [GlobalId],
    string_lens: &'a [Vec<u8>],
    /// The global of each array constant.
    tables: &'a [GlobalId],
    /// The global of each `static` the program uses.
    statics: &'a [Option<GlobalId>],
    /// The root allocator's global, if the program allocates.
    root_static: Option<GlobalId>,
    /// The dispatch functions called as the root allocator's method they
    /// call, with the root as `self` (with no other allocator type).
    redirect: &'a HashMap<usize, usize>,
    /// `alloc.Handle`, if the program imports `std/alloc`.
    handle: Option<Ty>,
    /// The addresses of the handles in context, innermost last (with a
    /// dynamic allocator context).
    ctx: Vec<ValueId>,
    /// Whether the allocator context is passed at run time
    /// ([`Instances::dynamic_alloc`]).
    dynamic: bool,
    slots: Vec<Slot>,
    /// The slots of each split local ([`Slot::Split`]): one per scalar,
    /// in the order of [`leaf_tys`], with its type.
    splits: Vec<Vec<(ValueId, Ty)>>,
    /// The addresses [`byte_offset`](Self::byte_offset) made, by block,
    /// base and offset.
    addrs: HashMap<(BlockId, ValueId, u64), ValueId>,
    /// `(continue target, break target, defer scopes outside it, locals
    /// dead at the end of an iteration)` of each enclosing loop.
    loops: Vec<(BlockId, BlockId, usize, Rc<[LocalId]>)>,
    /// How many times each local is named in the function (see
    /// [`iteration_locals`]).
    names: Vec<u32>,
    /// For each statement list being lowered, innermost last: the `defer`
    /// bodies and the destructions registered so far.
    defers: Vec<Vec<Defer>>,
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
    /// Whether the function returns its result packed in an `i64`
    /// ([`returns_packed`]).
    packed: bool,
    /// Whether the function throws (and returns a result).
    throws: bool,
    /// The sources, when building with debug information.
    files: Option<&'a SourceMap>,
    /// The IR line numbers of the program.
    lines: &'a mut Lines,
    /// The IR line number of the instructions made now (0: none).
    line: u32,
}

/// The most scalar copies an array copy or fill is unrolled into; longer
/// arrays are copied in a loop.
const UNROLL_LIMIT: u64 = 16;

/// The number of scalars in a value of type `ty`.
fn scalars(ty: Ty) -> u64 {
    if let Some((elem, n)) = ty.as_known_array() {
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

/// The width in bits of the packed form of a value of type `ty` (see the
/// module docs), if it has one: `()` is 0 bits, `bool` 1, an integer its
/// width, and an enum, optional or result its tag's width plus its largest
/// payload, if every payload field has a packed form and the total is at
/// most 64 bits.
fn packed_bits(ty: Ty) -> Option<u32> {
    match ty {
        Ty::Unit => Some(0),
        Ty::Bool => Some(1),
        Ty::Int(t) => Some(t.bits),
        _ => {
            let def = ty.sum()?;
            let mut largest = 0;
            for v in &def.variants {
                let mut n = 0;
                for f in &v.fields {
                    n += packed_bits(f.ty)?;
                }
                largest = largest.max(n);
            }
            let bits = def.tag.bits + largest;
            (bits <= 64).then_some(bits)
        }
    }
}

/// Whether a function whose result has type `ty` returns it packed in an
/// `i64` instead of writing it through a result pointer: an enum, an
/// optional or a result with a packed form.
fn returns_packed(ty: Ty) -> bool {
    ty.sum().is_some() && packed_bits(ty).is_some()
}

/// Which locals of `f` are kept in packed form, in an `i64` slot that LF's
/// mem2reg promotes to a register: those of a type a function would return
/// packed ([`returns_packed`]), not parameters, that are only initialized,
/// assigned, bound by `catch`, compared with `==` or `!=`, and read through
/// their tag or payload (by `match`, `if let`, `let ... else`, `??` or a
/// payload field). That's the hidden local a `match` on a call's result is
/// stored in. A local used in any other way (passed to a function, copied
/// whole, written through a field) stays in memory.
fn packed_locals(f: &Func) -> Vec<bool> {
    let mut packed: Vec<bool> = f
        .locals
        .iter()
        .map(|l| l.convention.is_none() && returns_packed(l.ty) && !l.ty.needs_destroy())
        .collect();
    for &p in &f.params {
        packed[p] = false;
    }
    uses_in_stmts(&f.body, &mut packed);
    packed
}

/// Clear `packed` for the locals `stmts` use other than as
/// [`packed_locals`] allows.
fn uses_in_stmts(stmts: &[TStmt], packed: &mut [bool]) {
    for s in stmts {
        match s {
            TStmt::Init(_, e) | TStmt::Assign(_, e) | TStmt::Expr(e) | TStmt::Throw(e) => {
                uses_in_expr(e, packed)
            }
            TStmt::Store(place, e) => {
                uses_in_place(place, packed);
                uses_in_expr(e, packed);
            }
            TStmt::Return(e) => {
                if let Some(e) = e {
                    uses_in_expr(e, packed);
                }
            }
            TStmt::If(c, then, otherwise) => {
                uses_in_expr(c, packed);
                uses_in_stmts(then, packed);
                uses_in_stmts(otherwise, packed);
            }
            TStmt::While(c, body) => {
                uses_in_expr(c, packed);
                uses_in_stmts(body, packed);
            }
            TStmt::For {
                start, end, body, ..
            } => {
                uses_in_expr(start, packed);
                uses_in_expr(end, packed);
                uses_in_stmts(body, packed);
            }
            TStmt::Loop(body) | TStmt::Block(body) | TStmt::Defer { body, .. } => {
                uses_in_stmts(body, packed)
            }
            TStmt::With(local, body) => {
                packed[*local] = false;
                uses_in_stmts(body, packed);
            }
            TStmt::Drop { local, .. } => packed[*local] = false,
            TStmt::Destroy(place) => uses_in_place(place, packed),
            TStmt::Match { value, arms } => {
                if !matches!(value.kind, TExprKind::Local(_)) {
                    uses_in_expr(value, packed);
                }
                for arm in arms {
                    uses_in_stmts(&arm.body, packed);
                }
            }
            TStmt::Break | TStmt::Continue | TStmt::Loc(_) => {}
        }
    }
}

/// [`uses_in_stmts`] for an expression whose value is read.
fn uses_in_expr(e: &TExpr, packed: &mut [bool]) {
    match &e.kind {
        TExprKind::Local(l) => packed[*l] = false,
        TExprKind::Payload(inner, ..) | TExprKind::EnumValue(inner)
            if matches!(inner.kind, TExprKind::Local(_)) => {}
        TExprKind::Coalesce(inner, default) if matches!(inner.kind, TExprKind::Local(_)) => {
            uses_in_expr(default, packed)
        }
        // Compared whole: read, unpacked into a temporary if the other side
        // isn't packed.
        TExprKind::Binary(TBinOp::Cmp(CmpOp::Eq | CmpOp::Ne), l, r) if l.ty.in_memory() => {
            for side in [l, r] {
                if !matches!(side.kind, TExprKind::Local(_)) {
                    uses_in_expr(side, packed);
                }
            }
        }
        TExprKind::Ref(place) => uses_in_place(place, packed),
        TExprKind::Catch { call, handler, .. } => {
            uses_in_expr(call, packed);
            match handler {
                Handler::Value(v) => uses_in_expr(v, packed),
                Handler::Block(body) => uses_in_stmts(body, packed),
            }
        }
        _ => {
            for sub in crate::sema::subexprs(e) {
                uses_in_expr(sub, packed);
            }
        }
    }
}

/// [`uses_in_stmts`] for a place that's written or whose address is
/// taken: the local it's part of stays in memory.
fn uses_in_place(place: &TExpr, packed: &mut [bool]) {
    match &place.kind {
        TExprKind::Local(l) => packed[*l] = false,
        TExprKind::Field(base, _) | TExprKind::Payload(base, ..) => uses_in_place(base, packed),
        TExprKind::Index(base, index) => {
            uses_in_place(base, packed);
            uses_in_expr(index, packed);
        }
        _ => uses_in_expr(place, packed),
    }
}

/// Which locals of `f` the body may change in place: assigned whole, or a
/// part of them assigned or passed with `&` (or as an `inout self`).
fn written_locals(f: &Func) -> Vec<bool> {
    fn root(mut e: &TExpr) -> Option<LocalId> {
        loop {
            match &e.kind {
                TExprKind::Local(l) => return Some(*l),
                TExprKind::Field(base, _)
                | TExprKind::Index(base, _)
                | TExprKind::Payload(base, ..)
                | TExprKind::Slice(base, ..)
                | TExprKind::ToSlice(base)
                | TExprKind::Deref(base) => e = base,
                _ => return None,
            }
        }
    }
    fn in_expr(e: &TExpr, out: &mut [bool]) {
        if let TExprKind::Ref(place) = &e.kind
            && let Some(l) = root(place)
        {
            out[l] = true;
        }
        if let TExprKind::Catch {
            handler: Handler::Block(body),
            ..
        } = &e.kind
        {
            in_stmts(body, out);
        }
        for sub in crate::sema::subexprs(e) {
            in_expr(sub, out);
        }
    }
    fn in_stmts(stmts: &[TStmt], out: &mut [bool]) {
        for s in stmts {
            match s {
                TStmt::Assign(l, _) => out[*l] = true,
                TStmt::Store(place, _) => {
                    if let Some(l) = root(place) {
                        out[l] = true;
                    }
                }
                _ => {}
            }
            for e in crate::sema::stmt_exprs(s) {
                in_expr(e, out);
            }
            match s {
                TStmt::If(_, then, otherwise) => {
                    in_stmts(then, out);
                    in_stmts(otherwise, out);
                }
                TStmt::While(_, body)
                | TStmt::For { body, .. }
                | TStmt::Loop(body)
                | TStmt::Block(body)
                | TStmt::With(_, body)
                | TStmt::Defer { body, .. } => in_stmts(body, out),
                TStmt::Match { arms, .. } => {
                    for arm in arms {
                        in_stmts(&arm.body, out);
                    }
                }
                _ => {}
            }
        }
    }
    let mut out = vec![false; f.locals.len()];
    in_stmts(&f.body, &mut out);
    out
}

/// The most scalars a split local has ([`split_locals`]).
const SPLIT_LIMIT: usize = 16;

/// The scalars a value of type `ty` is split into, in order: a `bool`, an
/// integer or a pointer is itself, `()` is none, and a struct is its
/// fields' scalars in declaration order. `None` for any other type, or a
/// struct with an array, an enum, an optional, a result or a view in it.
fn leaf_tys(ty: Ty) -> Option<Vec<Ty>> {
    fn add(ty: Ty, out: &mut Vec<Ty>) -> bool {
        match ty {
            Ty::Bool | Ty::Int(_) | Ty::Ptr(_) => {
                out.push(ty);
                true
            }
            Ty::Unit => true,
            _ => match ty.as_struct() {
                Some(def) => def.fields.iter().all(|f| add(f.ty, out)),
                None => false,
            },
        }
    }
    let mut out = Vec::new();
    add(ty, &mut out).then_some(out)
}

/// The number of scalars of a type [`leaf_tys`] splits.
fn leaf_count(ty: Ty) -> usize {
    leaf_tys(ty).expect("a type that splits").len()
}

/// The local `e` is, or is a field of through field accesses only (`p`,
/// `p.min.x`).
fn field_root(e: &TExpr) -> Option<LocalId> {
    match &e.kind {
        TExprKind::Local(l) => Some(*l),
        TExprKind::Field(base, _) => field_root(base),
        _ => None,
    }
}

/// Which locals of `f` are split into one slot per scalar ([`leaf_tys`]),
/// each of which LF's mem2reg promotes to a register: the locals of a
/// struct type with at most [`SPLIT_LIMIT`] scalars, all of them `bool`s,
/// integers, pointers or structs of them, that aren't parameters and are
/// only used field by field:
/// - `p.x`, `p.min.x`: reads the slot of a scalar field;
/// - `p.x = v`, `p.min = q`, `p.x += 1`: writes the slots of a field;
/// - `let p = e`, `var p = e`, `p = e`: writes every slot, from a struct
///   literal (field by field), another split local, or any other value
///   in memory (a call's result, an element, a field of a parameter),
///   read scalar by scalar;
/// - `p == q`, `p != q`: compares scalar by scalar;
/// - `p` or `p.min` copied into memory, scalar by scalar: `return p`,
///   `throw p`, `q = p` for a `q` in memory, `ps[i] = p`, a field of a
///   struct literal, an element of an array literal or a payload of a
///   variant that's stored or compared;
/// - `&p.x` of a scalar field (an `inout` or `set` argument): the address
///   of that field's own slot, which then stays in memory alone.
///
/// Any other use keeps the local in memory: `p` or `p.min` as a call
/// argument (it's passed by address) or read whole anywhere else, `&p`
/// or `&p.min`, and a `catch` binding. Copying the struct into a
/// temporary for such a use costs more code than its slots save (measured
/// on tests/programs: about 1 KB more over all programs).
fn split_locals(f: &Func) -> Vec<bool> {
    let mut memory = vec![false; f.locals.len()];
    for &p in &f.params {
        memory[p] = true;
    }
    split_in_stmts(&f.body, &mut memory);
    f.locals
        .iter()
        .enumerate()
        .map(|(l, local)| {
            !memory[l]
                && local.convention.is_none()
                && local.ty.as_struct().is_some()
                && !local.ty.needs_destroy()
                && leaf_tys(local.ty).is_some_and(|t| t.len() <= SPLIT_LIMIT)
        })
        .collect()
}

/// Set `memory` for the locals `stmts` use other than as [`split_locals`]
/// allows.
fn split_in_stmts(stmts: &[TStmt], memory: &mut [bool]) {
    for s in stmts {
        match s {
            TStmt::Init(_, e) | TStmt::Assign(_, e) | TStmt::Throw(e) | TStmt::Return(Some(e)) => {
                split_copied(e, memory)
            }
            TStmt::Store(place, e) => {
                if field_root(place).is_none() {
                    split_place(place, memory);
                }
                split_copied(e, memory);
            }
            TStmt::Return(None) | TStmt::Break | TStmt::Continue | TStmt::Loc(_) => {}
            TStmt::Expr(e) => split_in_expr(e, memory),
            TStmt::If(c, then, otherwise) => {
                split_in_expr(c, memory);
                split_in_stmts(then, memory);
                split_in_stmts(otherwise, memory);
            }
            TStmt::While(c, body) => {
                split_in_expr(c, memory);
                split_in_stmts(body, memory);
            }
            TStmt::For {
                start, end, body, ..
            } => {
                split_in_expr(start, memory);
                split_in_expr(end, memory);
                split_in_stmts(body, memory);
            }
            TStmt::Loop(body) | TStmt::Block(body) | TStmt::Defer { body, .. } => {
                split_in_stmts(body, memory)
            }
            // The handle in context is passed by address.
            TStmt::With(local, body) => {
                memory[*local] = true;
                split_in_stmts(body, memory);
            }
            TStmt::Drop { local, .. } => memory[*local] = true,
            TStmt::Destroy(place) => split_place(place, memory),
            TStmt::Match { value, arms } => {
                split_in_expr(value, memory);
                for arm in arms {
                    split_in_stmts(&arm.body, memory);
                }
            }
        }
    }
}

/// [`split_in_stmts`] for a value that's copied scalar by scalar: into a
/// local or into memory, or compared by `==`.
fn split_copied(e: &TExpr, memory: &mut [bool]) {
    match &e.kind {
        _ if field_root(e).is_some() => {}
        TExprKind::StructLit(fields) => {
            for (_, v) in fields {
                split_copied(v, memory);
            }
        }
        TExprKind::ArrayLit(items) | TExprKind::Variant(_, items) => {
            for v in items {
                split_copied(v, memory);
            }
        }
        _ => split_in_expr(e, memory),
    }
}

/// [`split_in_stmts`] for an expression whose value is read.
fn split_in_expr(e: &TExpr, memory: &mut [bool]) {
    match &e.kind {
        // Read whole.
        TExprKind::Local(l) => memory[*l] = true,
        TExprKind::Field(..) if field_root(e).is_some() => {
            if e.ty.in_memory() {
                memory[field_root(e).expect("a field of a local")] = true;
            }
        }
        TExprKind::Binary(TBinOp::Cmp(CmpOp::Eq | CmpOp::Ne), l, r) if l.ty.in_memory() => {
            split_copied(l, memory);
            split_copied(r, memory);
        }
        TExprKind::Ref(place) => match field_root(place) {
            Some(_) if !place.ty.in_memory() => {}
            _ => split_place(place, memory),
        },
        TExprKind::Catch {
            call,
            binding,
            handler,
        } => {
            if let Some(b) = binding {
                memory[*b] = true;
            }
            split_in_expr(call, memory);
            match handler {
                Handler::Value(v) => split_in_expr(v, memory),
                Handler::Block(body) => split_in_stmts(body, memory),
            }
        }
        _ => {
            for sub in crate::sema::subexprs(e) {
                split_in_expr(sub, memory);
            }
        }
    }
}

/// [`split_in_stmts`] for a place that's written other than through its
/// fields, or whose address is taken: the local it's part of stays in
/// memory.
fn split_place(place: &TExpr, memory: &mut [bool]) {
    match &place.kind {
        TExprKind::Local(l) => memory[*l] = true,
        TExprKind::Field(base, _) | TExprKind::Payload(base, ..) | TExprKind::ToSlice(base) => {
            split_place(base, memory)
        }
        TExprKind::Index(base, index) => {
            split_place(base, memory);
            split_in_expr(index, memory);
        }
        TExprKind::Slice(base, start, end) => {
            split_place(base, memory);
            for b in [start, end].into_iter().flatten() {
                split_in_expr(b, memory);
            }
        }
        _ => split_in_expr(place, memory),
    }
}

/// The locals a loop body `body` doesn't carry from one iteration to the
/// next: those it declares (with `let`, `var` or `for`), named nowhere
/// else in the function (`names` counts every name in it). The checker
/// proves a local is assigned before it's read, so each iteration writes
/// such a local before reading it: its value at the end of an iteration
/// is dead. Lowering stores poison in their slots there (at the end of
/// the body and at `continue`), so LF's mem2reg doesn't make them live
/// around the loop: it doesn't prune dead block parameters, and each one
/// costs a register or a stack slot for the whole loop.
fn iteration_locals(body: &[TStmt], names: &[u32]) -> Vec<LocalId> {
    let mut here = vec![0; names.len()];
    let mut declared = Vec::new();
    count_names(body, &mut here, &mut declared);
    declared.retain(|&l| here[l] == names[l]);
    declared.sort_unstable();
    declared.dedup();
    declared
}

/// Count each name of a local in `stmts` (its declaration, assignments
/// and reads) in `names`, and add the locals they declare to `declared`.
fn count_names(stmts: &[TStmt], names: &mut [u32], declared: &mut Vec<LocalId>) {
    for s in stmts {
        match s {
            TStmt::Init(l, _) | TStmt::For { var: l, .. } => {
                names[*l] += 1;
                declared.push(*l);
            }
            TStmt::Assign(l, _) | TStmt::With(l, _) => names[*l] += 1,
            _ => {}
        }
        for e in crate::sema::stmt_exprs(s) {
            count_names_in(e, names, declared);
        }
        match s {
            TStmt::If(_, then, otherwise) => {
                count_names(then, names, declared);
                count_names(otherwise, names, declared);
            }
            TStmt::While(_, body)
            | TStmt::For { body, .. }
            | TStmt::Loop(body)
            | TStmt::Block(body)
            | TStmt::With(_, body)
            | TStmt::Defer { body, .. } => count_names(body, names, declared),
            TStmt::Match { arms, .. } => {
                for arm in arms {
                    count_names(&arm.body, names, declared);
                }
            }
            _ => {}
        }
    }
}

/// [`count_names`] in an expression.
fn count_names_in(e: &TExpr, names: &mut [u32], declared: &mut Vec<LocalId>) {
    match &e.kind {
        TExprKind::Local(l) => names[*l] += 1,
        TExprKind::Catch {
            binding, handler, ..
        } => {
            if let Some(b) = binding {
                names[*b] += 1;
            }
            if let Handler::Block(body) = handler {
                count_names(body, names, declared);
            }
        }
        _ => {}
    }
    for sub in crate::sema::subexprs(e) {
        count_names_in(sub, names, declared);
    }
}

/// Where payload field `field` of variant `variant` starts in the packed
/// form of a value of type `ty`: after the tag and the fields before it.
fn payload_shift(ty: Ty, variant: u32, field: u32) -> u32 {
    let def = ty.sum().expect("an enum, an optional or a result");
    let before = &def.variants[variant as usize].fields[..field as usize];
    def.tag.bits
        + before
            .iter()
            .map(|f| packed_bits(f.ty).expect("a packed payload"))
            .sum::<u32>()
}

/// The low `bits` bits of `v`.
fn mask(v: u64, bits: u32) -> u64 {
    if bits >= 64 { v } else { v & ((1 << bits) - 1) }
}

/// `v` (known to be in range for `t`) as the `i64` bit pattern of a `t`-wide
/// constant, sign-extended from the type's width.
fn const_bits(v: i128, t: IntTy) -> i64 {
    let shift = 64 - t.bits;
    ((v as i64) << shift) >> shift
}

impl FnLower<'_> {
    fn function(mut self, f: &Func) {
        self.at(f.span.start, f.span.file);
        if self.line != 0 {
            self.b.set_decl_line(self.line);
        }
        let entry = self.b.create_entry_block();
        // The IR parameters: the result's storage first, if it's in memory,
        // then each parameter's parts.
        let mut next = 0;
        if !self.packed && (self.result_ty.in_memory() || self.result_ty.is_view()) {
            self.result = Some(self.b.param(entry, 0));
            next = 1;
        }
        // The handle in context: a parameter, last, or for the entry, the
        // root allocator's.
        if self.dynamic && f.uses_alloc {
            let ctx = if self.exit_status.is_some() {
                self.root_handle()
            } else {
                let parts: usize = f
                    .params
                    .iter()
                    .map(|&p| self.t.param_parts(&f.locals[p]).len())
                    .sum();
                self.b.param(entry, next + parts as u32)
            };
            self.ctx.push(ctx);
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
        let packed = packed_locals(f);
        let split = split_locals(f);
        let written = written_locals(f);
        self.names = vec![0; f.locals.len()];
        count_names(&f.body, &mut self.names, &mut Vec::new());
        for (local, param) in f.locals.iter().zip(&params) {
            match *param {
                // A parameter in memory is the caller's value, read (or for
                // `inout` and `set`, written) in place. A `sink` one is the
                // callee's own copy, unless the callee never changes it: the
                // caller's value is moved in, or can't change during the
                // call (exclusivity), so it's read in place too.
                Some(Val::Mem(p))
                    if local.convention != Some(Convention::Sink) || !written[self.slots.len()] =>
                {
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
                ty if packed[self.slots.len()] => Slot::Packed(self.b.alloca(self.t.i64), ty),
                ty if split[self.slots.len()] => {
                    let leaves = leaf_tys(ty)
                        .expect("a type that splits")
                        .into_iter()
                        .map(|t| (self.b.alloca(self.t.of(t)), t))
                        .collect();
                    self.splits.push(leaves);
                    Slot::Split(self.splits.len() - 1)
                }
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
        // Drop flags, in the entry block. A `set` parameter starts
        // unassigned; every other local's is set where it's declared.
        for (l, local) in f.locals.iter().enumerate() {
            let flag = (local.drop_flag && local.ty.needs_destroy()).then(|| {
                let slot = self.b.alloca(self.t.bool);
                if local.convention == Some(Convention::Set) {
                    let no = self.b.const_bool(false);
                    self.b.store(self.t.bool, slot, no, 1);
                }
                slot
            });
            debug_assert_eq!(self.flags.len(), l);
            self.flags.push(flag);
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
            // At the closing brace.
            self.at(f.span.end.saturating_sub(1), f.span.file);
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
            Slot::Split(_) => unreachable!("a split local read whole"),
            // Only when it's read whole, which `packed_locals` rules out:
            // unpacked into a temporary.
            Slot::Packed(slot, ty) => {
                let p = self.b.load(self.t.i64, slot, 8);
                let ir_ty = self.ir_ty(ty);
                let tmp = self.b.alloca(ir_ty);
                self.unpack(tmp, ty, p, 0);
                Val::Mem(tmp)
            }
        }
    }

    /// Give the instructions made from now on the line of `offset` in
    /// `file`, when building with debug information.
    fn at(&mut self, offset: u32, file: FileId) {
        if let Some(files) = self.files {
            let (line, _) = files.get(file).line_col(offset);
            let id = self.lines.id(file, line);
            self.set_line(id);
        }
    }

    /// Give the instructions made from now on the IR line number `line`.
    fn set_line(&mut self, line: u32) {
        if line != 0 {
            self.line = line;
            self.b.set_line(line);
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
            if let TStmt::Loc(span) = s {
                self.at(span.start, span.file);
                continue;
            }
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

    /// Mark the values of `locals` dead: store poison in their slots, so a
    /// loop doesn't carry them to its next iteration (see
    /// [`iteration_locals`]).
    fn kill(&mut self, locals: &[LocalId]) {
        for &l in locals {
            self.kill_one(l);
        }
    }

    fn kill_one(&mut self, local: usize) {
        let slots: Vec<(ValueId, TypeId, u32)> = match self.slots[local] {
            Slot::One { slot, ty, align } => vec![(slot, ty, align)],
            Slot::Packed(slot, _) => vec![(slot, self.t.i64, 8)],
            Slot::View { ptr, len } => vec![(ptr, self.t.ptr, 8), (len, self.t.i64, 8)],
            Slot::Split(k) => self.splits[k]
                .iter()
                .map(|&(slot, t)| (slot, self.t.of(t), align_of(t)))
                .collect(),
            Slot::Mem(_) => Vec::new(),
        };
        for (slot, ty, align) in slots {
            let p = self.b.poison(ty);
            self.b.store(ty, slot, p, align);
        }
    }

    /// Emit the `defer` bodies of the scopes from `outer` in, innermost
    /// first and each scope's last first, for leaving them; with `error`,
    /// the `errdefer` bodies too.
    fn run_defers(&mut self, outer: usize, error: bool) {
        for scope in (outer..self.defers.len()).rev() {
            let entries = self.defers[scope].clone();
            for entry in entries.iter().rev() {
                match entry {
                    Defer::Body(_, true, _) if !error => {}
                    Defer::Body(body, _, ctx) => {
                        // The body can't leave its own statements, so the
                        // defers registered while lowering it are its own.
                        // It runs in the context it was written in, outside
                        // the `with` blocks an exit leaves.
                        let depth = self.defers.len();
                        let inner = self.ctx.split_off((*ctx).min(self.ctx.len()));
                        self.stmts(body);
                        self.ctx.extend(inner);
                        debug_assert_eq!(depth, self.defers.len());
                    }
                    Defer::Drop(local) => self.destroy_local(*local, false),
                    Defer::Place(addr, ty) => self.destroy(*addr, *ty),
                }
            }
        }
    }

    /// `mem.swap(&a, &b)`: exchange the values of the places `a` and `b`
    /// (`&` arguments), which don't overlap.
    fn swap(&mut self, a: &TExpr, b: &TExpr) {
        let (TExprKind::Ref(pa), TExprKind::Ref(pb)) = (&a.kind, &b.kind) else {
            unreachable!("`swap` takes two places")
        };
        let ty = pa.ty;
        if ty.in_memory() {
            let x = self.place(pa);
            let y = self.place(pb);
            let ir_ty = self.ir_ty(ty);
            let tmp = self.b.alloca(ir_ty);
            self.copy(tmp, x, ty);
            self.copy(x, y, ty);
            self.copy(y, tmp, ty);
            return;
        }
        // A scalar's place is its address.
        let x = self.expr(a).one();
        let y = self.expr(b).one();
        let ir_ty = self.t.of(ty);
        let vx = self.b.load(ir_ty, x, align_of(ty));
        let vy = self.b.load(ir_ty, y, align_of(ty));
        self.b.store(ir_ty, x, vy, align_of(ty));
        self.b.store(ir_ty, y, vx, align_of(ty));
    }

    /// A new handle of the root allocator (number 0, at `alloc.ROOT`), in
    /// a temporary.
    fn root_handle(&mut self) -> ValueId {
        let handle = self.handle.expect("a program that allocates");
        let ty = self.ir_ty(handle);
        let h = self.b.alloca(ty);
        let root = self
            .b
            .global_ref(self.root_static.expect("the root allocator is used"));
        write_root_handle(&mut self.b, self.t, ty, h, root);
        h
    }

    /// Set the drop flag of `local`, if it has one, to `value`.
    fn set_flag(&mut self, local: LocalId, value: bool) {
        if let Some(flag) = self.flags[local] {
            let v = self.b.const_bool(value);
            self.b.store(self.t.bool, flag, v, 1);
        }
    }

    /// Destroy the value of `local` (if it holds one, when it has a drop
    /// flag); with `clear`, it's unassigned after.
    fn destroy_local(&mut self, local: LocalId, clear: bool) {
        let ty = self.locals[local].ty;
        let Slot::Mem(addr) = self.slots[local] else {
            unreachable!("a local that needs destruction is in memory")
        };
        let Some(flag) = self.flags[local] else {
            self.destroy(addr, ty);
            return;
        };
        let held = self.b.load(self.t.bool, flag, 1);
        let yes = self.b.create_block(&[]);
        let done = self.b.create_block(&[]);
        self.b.cond_br(held, yes, &[], done, &[]);
        self.start_block(yes);
        self.destroy(addr, ty);
        if clear {
            self.set_flag(local, false);
        }
        self.b.br(done, &[]);
        self.start_block(done);
    }

    /// Destroy the value of type `ty` at `addr`: call its type's
    /// destruction.
    fn destroy(&mut self, addr: ValueId, ty: Ty) {
        let f = self.reach.destroy[&ty];
        let callee = self.b.func_ref(self.ids[f].expect("a reached function"));
        self.b.call(callee, &[addr], self.t.void);
    }

    /// `return value`: write it (as `ok(value)` in a function that throws),
    /// or pack it, run every `defer`, and return.
    fn return_value(&mut self, value: Option<&TExpr>) {
        // A value that needs destruction and may leave while it's built
        // is built aside first: the exit it may take writes the result's
        // storage, and destroys the parts built so far.
        if let Some(e) = value
            && !self.packed
            && e.ty.needs_destroy()
            && matches!(
                e.kind,
                TExprKind::StructLit(_) | TExprKind::ArrayLit(_) | TExprKind::Variant(..)
            )
            && may_leave(e)
        {
            let ir_ty = self.ir_ty(e.ty);
            let tmp = self.b.alloca(ir_ty);
            self.fill(tmp, e);
            let dst = self.result.expect("a result in memory");
            let dst = if self.throws {
                self.payload_at(dst, self.result_ty, 0, 0)
            } else {
                dst
            };
            self.copy(dst, tmp, e.ty);
            if self.throws {
                let base = self.result.expect("a result in memory");
                self.store_tag(base, self.result_ty, 0);
            }
            self.run_defers(0, false);
            self.ret(None);
            self.terminated = true;
            return;
        }
        let v = if self.packed {
            Some(if self.throws {
                let bits = value.map(|e| self.pack(e));
                self.pack_variant(self.result_ty, 0, bits)
            } else {
                self.pack(value.expect("a value to return"))
            })
        } else if self.throws {
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

    /// Leave the function with the error `err`, then run every `defer` and
    /// `errdefer`.
    fn fail(&mut self, err: Failure<'_>) {
        let (_, err_ty) = self.result_ty.as_result().expect("a result");
        let v = if self.packed {
            let bits = match err {
                Failure::Expr(e) => self.pack(e),
                Failure::Mem(src) => self.pack_mem(src, err_ty),
                // Every result has a `u8` tag with `err` as 1, so a packed
                // `err` of the same error type is this function's result
                // as it is.
                Failure::Packed(p) => p,
            };
            Some(match err {
                Failure::Packed(_) => bits,
                _ => self.pack_variant(self.result_ty, 1, Some(bits)),
            })
        } else {
            let dst = self.result.expect("a result in memory");
            let d = self.payload_at(dst, self.result_ty, 1, 0);
            match err {
                Failure::Expr(e) => self.fill(d, e),
                Failure::Mem(src) => self.copy(d, src, err_ty),
                Failure::Packed(p) => self.unpack(d, err_ty, p, RESULT_TAG_BITS),
            }
            self.store_tag(dst, self.result_ty, 1);
            None
        };
        self.run_defers(0, true);
        self.ret(v);
        self.terminated = true;
    }

    /// `throw e`.
    fn throw(&mut self, e: &TExpr) {
        self.fail(Failure::Expr(e));
    }

    /// Call `call`, a call to a function that throws, and branch on its
    /// result: to the returned block for `ok`, to `err_bb` for `err`.
    /// Returns the result, packed or in a temporary, and the `ok` block.
    fn call_result(&mut self, call: &TExpr, err_bb: BlockId) -> (Outcome, BlockId) {
        let ok_bb = self.b.create_block(&[]);
        let targets = [(vec![0], ok_bb), (vec![1], err_bb)];
        if returns_packed(call.ty) {
            let p = self.pack(call);
            let tag = self.unpack_scalar(p, 0, Ty::Int(IntTy::new(false, 8)));
            self.branch_on_tag(tag, call.ty, &targets);
            return (Outcome::Packed(p), ok_bb);
        }
        let ir_ty = self.ir_ty(call.ty);
        let tmp = self.b.alloca(ir_ty);
        self.fill(tmp, call);
        let tag = self.load_tag(tmp, call.ty);
        self.branch_on_tag(tag, call.ty, &targets);
        (Outcome::Mem(tmp), ok_bb)
    }

    /// The value of `ok` in the result `result` of type `ty`, or `Unit`.
    fn ok_value(&mut self, result: Outcome, ty: Ty) -> Val {
        let (value, _) = ty.as_result().expect("a result");
        if value == Ty::Unit {
            return Val::Unit;
        }
        match result {
            Outcome::Mem(base) => {
                let addr = self.payload_at(base, ty, 0, 0);
                self.read(addr, value)
            }
            Outcome::Packed(p) if value.in_memory() => {
                let ir_ty = self.ir_ty(value);
                let tmp = self.b.alloca(ir_ty);
                self.unpack(tmp, value, p, RESULT_TAG_BITS);
                Val::Mem(tmp)
            }
            Outcome::Packed(p) => Val::One(self.unpack_scalar(p, RESULT_TAG_BITS, value)),
        }
    }

    /// `try call`.
    fn try_call(&mut self, call: &TExpr) -> Val {
        let err_bb = self.b.create_block(&[]);
        let (result, ok_bb) = self.call_result(call, err_bb);
        self.start_block(err_bb);
        let failure = match result {
            Outcome::Mem(tmp) => Failure::Mem(self.payload_at(tmp, call.ty, 1, 0)),
            Outcome::Packed(p) => Failure::Packed(p),
        };
        self.fail(failure);
        self.start_block(ok_bb);
        self.ok_value(result, call.ty)
    }

    /// `call catch ...`, of type `ty`.
    fn catch(&mut self, call: &TExpr, binding: Option<usize>, handler: &Handler, ty: Ty) -> Val {
        let (_, err) = call.ty.as_result().expect("a result");
        // `f() catch _ {}` ignores the result: no branch on it (two
        // branches to the same place that the backend doesn't merge yet,
        // after each argument of `io.print`).
        if binding.is_none()
            && ty == Ty::Unit
            && matches!(handler, Handler::Block(b) if b.is_empty())
        {
            if returns_packed(call.ty) {
                self.pack(call);
            } else {
                let ir_ty = self.ir_ty(call.ty);
                let tmp = self.b.alloca(ir_ty);
                self.fill(tmp, call);
            }
            return Val::Unit;
        }
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
        let (result, ok_bb) = self.call_result(call, err_bb);
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
        let v = self.ok_value(result, call.ty);
        arrive(self, v);

        self.start_block(err_bb);
        if let Some(local) = binding {
            match (self.slots[local], result) {
                (Slot::Mem(dst), Outcome::Mem(tmp)) => {
                    let src = self.payload_at(tmp, call.ty, 1, 0);
                    self.copy(dst, src, err);
                }
                (Slot::Mem(dst), Outcome::Packed(p)) => self.unpack(dst, err, p, RESULT_TAG_BITS),
                (Slot::Packed(slot, _), Outcome::Mem(tmp)) => {
                    let src = self.payload_at(tmp, call.ty, 1, 0);
                    let p = self.pack_mem(src, err);
                    self.b.store(self.t.i64, slot, p, 8);
                }
                (Slot::Packed(slot, _), Outcome::Packed(p)) => {
                    let amount = self.b.const_i64(self.t.i64, i64::from(RESULT_TAG_BITS));
                    let e = self.b.bin(IrOp::LShr, p, amount, Flags::NONE);
                    self.b.store(self.t.i64, slot, e, 8);
                }
                (slot, _) => unreachable!("an error in {slot:?}"),
            }
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
                Slot::Split(k) => {
                    let vals = self.leaf_values(e);
                    self.store_leaves(k, 0, &vals);
                }
                Slot::Packed(slot, _) => {
                    let p = self.pack(e);
                    self.b.store(self.t.i64, slot, p, 8);
                }
                _ => {
                    let v = self.expr(e);
                    self.store(*local, v);
                }
            },
            TStmt::Assign(local, e) if self.locals[*local].ty.needs_destroy() => {
                let Slot::Mem(dst) = self.slots[*local] else {
                    unreachable!("a local that needs destruction is in memory")
                };
                // The new value first, then the old one is destroyed.
                let src = self.place(e);
                self.destroy_local(*local, false);
                self.copy(dst, src, e.ty);
                self.set_flag(*local, true);
            }
            TStmt::Assign(local, e) => match self.slots[*local] {
                Slot::Mem(dst) => self.assign_into(dst, e),
                Slot::Split(k) => {
                    let vals = self.leaf_values(e);
                    self.store_leaves(k, 0, &vals);
                }
                Slot::Packed(slot, _) => {
                    let p = self.pack(e);
                    self.b.store(self.t.i64, slot, p, 8);
                }
                _ => {
                    let v = self.expr(e);
                    self.store(*local, v);
                }
            },
            TStmt::Store(place, e) if place.ty.needs_destroy() => {
                let dst = self.address(place);
                let src = self.place(e);
                self.destroy(dst, place.ty);
                self.copy(dst, src, e.ty);
            }
            TStmt::Store(place, e) => {
                if let Some((k, start)) = self.split_path(place) {
                    let vals = self.leaf_values(e);
                    self.store_leaves(k, start, &vals);
                    return;
                }
                let dst = self.address(place);
                self.assign_into(dst, e);
            }
            TStmt::Expr(e) => {
                self.expr(e);
            }
            TStmt::Return(value) => self.return_value(value.as_ref()),
            TStmt::Throw(e) => self.throw(e),
            TStmt::Defer { body, on_error } => {
                let ctx = self.ctx.len();
                let scope = self.defers.last_mut().expect("in a statement list");
                scope.push(Defer::Body(Rc::from(body.clone()), *on_error, ctx));
            }
            TStmt::Drop { local, init } => {
                self.set_flag(*local, *init);
                let scope = self.defers.last_mut().expect("in a statement list");
                scope.push(Defer::Drop(*local));
            }
            TStmt::Destroy(place) => match place.kind {
                TExprKind::Local(l) => self.destroy_local(l, true),
                _ => {
                    let addr = self.place(place);
                    self.destroy(addr, place.ty);
                }
            },
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
                let line = self.line;
                self.loop_body(body_bb, latch, exit, body);
                // The counter is below `end`, so adding one can't overflow.
                self.start_block(latch);
                self.set_line(line);
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
                let (cont, brk, outer, kills) =
                    self.loops.last().cloned().expect("checked: inside a loop");
                let target = if matches!(s, TStmt::Break) { brk } else { cont };
                self.run_defers(outer, false);
                if matches!(s, TStmt::Continue) {
                    self.kill(&kills);
                }
                self.b.br(target, &[]);
                self.terminated = true;
            }
            TStmt::Block(body) => self.stmts(body),
            // The block's calls get `local`'s handle as the context.
            TStmt::With(local, body) => {
                if self.dynamic {
                    let Slot::Mem(addr) = self.slots[*local] else {
                        unreachable!("a handle in context is in memory")
                    };
                    self.ctx.push(addr);
                    self.stmts(body);
                    self.ctx.pop();
                } else {
                    self.stmts(body);
                }
            }
            // Handled by `stmts`.
            TStmt::Loc(_) => {}
            TStmt::Match { value, arms } => {
                let tag = self.tag_of(value);
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
        let kills: Rc<[LocalId]> = iteration_locals(body, &self.names).into();
        self.loops
            .push((cont, exit, self.defers.len(), kills.clone()));
        self.stmts(body);
        self.loops.pop();
        if !self.terminated {
            self.kill(&kills);
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
            TExprKind::Move(inner, local) => {
                let v = self.expr(inner);
                self.set_flag(*local, false);
                return v;
            }
            TExprKind::Intrinsic(Intrinsic::Swap, args) => {
                self.swap(&args[0], &args[1]);
                return Val::Unit;
            }
            TExprKind::Intrinsic(Intrinsic::Take, _) => {
                let ir_ty = self.ir_ty(e.ty);
                let tmp = self.b.alloca(ir_ty);
                self.fill(tmp, e);
                return Val::Mem(tmp);
            }
            // The value is moved in, and nothing destroys it.
            TExprKind::Intrinsic(Intrinsic::Forget, args) => {
                self.expr(&args[0]);
                return Val::Unit;
            }
            TExprKind::Clone(_) => unreachable!("instances clone by copies and calls"),
            TExprKind::NeedsDeinit(_) => unreachable!("instances know their types"),
            TExprKind::Static(k) => {
                let g = self.statics[*k].expect("a static the program uses");
                let addr = self.b.global_ref(g);
                return self.read(addr, e.ty);
            }
            TExprKind::Deref(p) => {
                let addr = self.expr(p).one();
                return self.read(addr, e.ty);
            }
            TExprKind::Layout(ty, align) => {
                let ir_ty = self.ir_ty(*ty);
                let layout = self.b.types().layout(ir_ty);
                let v = if *align { layout.align } else { layout.size };
                self.b.const_i64(self.t.i64, v as i64)
            }
            TExprKind::Intrinsic(Intrinsic::PtrRead, args) => {
                let addr = self.expr(&args[0]).one();
                if e.ty.in_memory() {
                    let ir_ty = self.ir_ty(e.ty);
                    let tmp = self.b.alloca(ir_ty);
                    self.copy(tmp, addr, e.ty);
                    return Val::Mem(tmp);
                }
                return self.read(addr, e.ty);
            }
            TExprKind::Intrinsic(Intrinsic::PtrWrite, args) => {
                let addr = self.expr(&args[0]).one();
                self.fill_or_write(addr, &args[1]);
                return Val::Unit;
            }
            TExprKind::Intrinsic(Intrinsic::PtrDestroy, args) => {
                let addr = self.expr(&args[0]).one();
                let to = args[0].ty.as_ptr().expect("a pointer");
                if to.needs_destroy() {
                    self.destroy(addr, to);
                }
                return Val::Unit;
            }
            TExprKind::Intrinsic(Intrinsic::PtrCast, args) => return self.expr(&args[0]),
            TExprKind::Intrinsic(Intrinsic::PtrAddr, args) => {
                let p = self.expr(&args[0]).one();
                self.b.cast(CastOp::PtrToInt, p, self.t.i64)
            }
            TExprKind::Intrinsic(Intrinsic::FromAddr, args) => {
                let a = self.expr(&args[0]).one();
                self.b.cast(CastOp::IntToPtr, a, self.t.ptr)
            }
            // The handle in context, read in place.
            TExprKind::Intrinsic(Intrinsic::AllocCurrent, _) => {
                if self.dynamic {
                    return Val::Mem(*self.ctx.last().expect("a function that `uses alloc`"));
                }
                let ir_ty = self.ir_ty(e.ty);
                return Val::Mem(self.b.alloca(ir_ty));
            }
            TExprKind::Intrinsic(Intrinsic::AllocRoot, _) => {
                if self.dynamic {
                    return Val::Mem(self.root_handle());
                }
                let ir_ty = self.ir_ty(e.ty);
                return Val::Mem(self.b.alloca(ir_ty));
            }
            // A handle of the allocator `a`: its type's number and its
            // address.
            TExprKind::Intrinsic(Intrinsic::AllocHandle, args) => {
                let a = &args[0];
                if !self.dynamic {
                    // A handle of the root itself, which holds nothing.
                    self.expr(a);
                    let ir_ty = self.ir_ty(e.ty);
                    return Val::Mem(self.b.alloca(ir_ty));
                }
                let addr = match self.expr(a) {
                    Val::Mem(p) => p,
                    Val::One(v) => {
                        let ir_ty = self.t.of(a.ty);
                        let tmp = self.b.alloca(ir_ty);
                        self.b.store(ir_ty, tmp, v, align_of(a.ty));
                        tmp
                    }
                    other => unreachable!("an allocator is a value, found {other:?}"),
                };
                let number = self
                    .reach
                    .allocators
                    .iter()
                    .position(|&t| t == a.ty)
                    .expect("an allocator type of the program");
                let ir_ty = self.ir_ty(e.ty);
                let h = self.b.alloca(ir_ty);
                let n = self.b.const_i64(self.t.i64, number as i64);
                self.b.store(self.t.i64, h, n, 8);
                let addr = self.b.cast(CastOp::PtrToInt, addr, self.t.i64);
                let at = self.field_at(h, e.ty, 1);
                self.b.store(self.t.i64, at, addr, 8);
                return Val::Mem(h);
            }
            TExprKind::Intrinsic(
                Intrinsic::HandleAlloc | Intrinsic::HandleResize | Intrinsic::HandleFree,
                _,
            ) => unreachable!("instances call the allocators"),
            // Kept in its hidden local, whose value from an earlier time
            // round a loop is destroyed first.
            TExprKind::Temp(local, inner) => {
                let Slot::Mem(dst) = self.slots[*local] else {
                    unreachable!("a temporary that needs destruction is in memory")
                };
                self.destroy_local(*local, false);
                self.fill(dst, inner);
                self.set_flag(*local, true);
                return Val::Mem(dst);
            }
            // A returned view is written to a pointer and length in memory.
            TExprKind::Call(f, args) if e.ty.is_view() => {
                let ty = self.view_ir();
                let tmp = self.b.alloca(ty);
                self.call(*f, args, e.ty, Some(tmp));
                let p = self.struct_field(tmp, ty, 0);
                let n = self.struct_field(tmp, ty, 1);
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
                let (_, n) = a.ty.as_known_array().expect("an array");
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
            TExprKind::Payload(base, v, k) if self.packed_slot(base).is_some() => {
                let p = self.packed_local(base).expect("a packed local");
                return self.packed_field(p, base.ty, *v, *k);
            }
            TExprKind::Field(..) if self.split_path(e).is_some() => {
                // A scalar field: `split_locals` keeps a local whose struct
                // fields are read whole in memory.
                let (k, start) = self.split_path(e).expect("a split local");
                return match self.load_leaves(k, start, e.ty)[..] {
                    [] => Val::Unit,
                    [v] => Val::One(v),
                    _ => unreachable!("a struct field of a split local read whole"),
                };
            }
            TExprKind::Index(..) | TExprKind::Field(..) | TExprKind::Payload(..) => {
                let addr = self.address(e);
                return self.read(addr, e.ty);
            }
            TExprKind::Coalesce(opt, default) => return self.coalesce(opt, default, e.ty),
            // The address of the place: as for any value in memory, of a
            // scalar's storage, or a view of an array.
            TExprKind::Ref(place) => {
                // A scalar field of a split local: its own slot.
                if let Some((k, start)) = self.split_path(place) {
                    debug_assert!(!place.ty.in_memory(), "a split local's address");
                    return Val::One(self.splits[k][start].0);
                }
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
                return self.no_value(e.ty);
            }
            // The call ends in `unreachable`, in a block of its own.
            TExprKind::Never(call) => {
                self.expr(call);
                return self.no_value(e.ty);
            }
            TExprKind::Unproven(..) | TExprKind::Refined(..) | TExprKind::CompileError { .. } => {
                unreachable!("only in code run at compile time")
            }
            TExprKind::EnumValue(inner) => self.tag_of(inner),
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
                let p = self.array_elem(p, elem, start);
                let n = self.b.sub(end, start, Flags::nuw());
                return Val::View(p, n);
            }
            TExprKind::ToSlice(a) => {
                let p = self.place(a);
                let (_, n) = a.ty.as_known_array().expect("an array");
                let n = self.b.const_i64(self.t.i64, n as i64);
                return Val::View(p, n);
            }
            TExprKind::PtrAdd(p, n) => {
                let base = self.expr(p).one();
                let count = self.expr(n).one();
                let elem = p.ty.as_ptr().expect("pointer arithmetic on a pointer");
                let elem = self.ir_ty(elem);
                let size = self.b.types().stride(elem) as i64;
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
                // A split local is compared scalar by scalar, without going
                // through memory.
                let split = self.split_path(lhs).is_some() || self.split_path(rhs).is_some();
                // The packed form of a value is unique (the bits above the
                // active variant's fields are 0), so two values are equal
                // when their packed forms are.
                let eq = if split {
                    let l = self.leaf_values(lhs);
                    let r = self.leaf_values(rhs);
                    self.leaves_equal(&l, &r)
                } else if returns_packed(lhs.ty)
                    && self.packs_cheaply(lhs)
                    && self.packs_cheaply(rhs)
                {
                    let l = self.pack(lhs);
                    let r = self.pack(rhs);
                    self.b.icmp(IntPred::Eq, l, r)
                } else {
                    let l = self.place(lhs);
                    let r = self.place(rhs);
                    self.equal(l, r, lhs.ty)
                };
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

    /// A placeholder value of type `ty`, in a block no path reaches (after
    /// a `throw` or a call to a `never` function).
    fn no_value(&mut self, ty: Ty) -> Val {
        match ty {
            Ty::Unit | Ty::Never => Val::Unit,
            Ty::Str | Ty::Slice(_) => {
                let p = self.b.poison(self.t.ptr);
                Val::View(p, self.b.poison(self.t.i64))
            }
            _ if ty.in_memory() => {
                let ir_ty = self.ir_ty(ty);
                Val::Mem(self.b.alloca(ir_ty))
            }
            _ => {
                let ir_ty = self.t.of(ty);
                Val::One(self.b.poison(ir_ty))
            }
        }
    }

    /// A call. A result in memory is written to `dst`, which must be fresh
    /// storage (see the module docs). A call to a `never` function is
    /// followed by `unreachable`, and what comes after it goes in a new
    /// block that no path reaches.
    ///
    /// A packed result is unpacked into `dst` if there is one, otherwise
    /// it's the call's value.
    fn call(&mut self, f: usize, args: &[TExpr], ret: Ty, dst: Option<ValueId>) -> Val {
        let packed = returns_packed(ret);
        let mut values: Vec<ValueId> = dst.filter(|_| !packed).into_iter().collect();
        // A call through a handle, with no allocator but the root: the
        // root's method, on `alloc.ROOT` (the handle holds nothing).
        let root = self.redirect.get(&f).copied();
        let f = root.unwrap_or(f);
        // An argument moved in (`sink`) belongs to the call: until it's
        // made, an argument after it that leaves early destroys it.
        let later = later_leaves(args.iter());
        let callee_fn = &self.reach.funcs[f];
        let owned: Vec<bool> = callee_fn
            .params
            .iter()
            .map(|&p| callee_fn.locals[p].convention == Some(Convention::Sink))
            .collect();
        let pending = self.defers.last().map_or(0, Vec::len);
        for (k, a) in args.iter().enumerate() {
            let v = self.expr(a);
            if root.is_some() && k == 0 {
                let g = self.root_static.expect("the root allocator is used");
                values.push(self.b.global_ref(g));
                continue;
            }
            if let Val::Mem(addr) = v
                && later[k]
                && owned.get(k).copied().unwrap_or(false)
                && a.ty.needs_destroy()
                && let Some(scope) = self.defers.last_mut()
            {
                scope.push(Defer::Place(addr, a.ty));
            }
            values.extend(v.parts());
        }
        if let Some(scope) = self.defers.last_mut() {
            scope.truncate(pending);
        }
        // The handle in context, for a function that `uses alloc`.
        if self.dynamic && self.reach.funcs[f].uses_alloc {
            values.push(*self.ctx.last().expect("a caller that `uses alloc`"));
        }
        let callee = self.b.func_ref(self.ids[f].expect("a reached function"));
        let ret_ty = if packed {
            self.t.i64
        } else if dst.is_some() {
            self.t.void
        } else {
            self.t.of(ret)
        };
        let result = self.b.call(callee, &values, ret_ty);
        self.set_args_assigned(f, args, ret, result, dst);
        if ret == Ty::Never {
            self.b.unreachable();
            let dead = self.b.create_block(&[]);
            self.start_block(dead);
        }
        if let (true, Some(p), Some(d)) = (packed, result, dst) {
            self.unpack(d, ret, p, 0);
        }
        match (result, dst) {
            (_, Some(p)) => Val::Mem(p),
            (Some(v), None) => Val::One(v),
            (None, None) => Val::Unit,
        }
    }

    /// After a call of `f`, of result type `ret` (packed in `result`, or in
    /// memory at `dst`): the locals with drop flags passed to its `set`
    /// parameters hold a value, if the call succeeded.
    fn set_args_assigned(
        &mut self,
        f: usize,
        args: &[TExpr],
        ret: Ty,
        result: Option<ValueId>,
        dst: Option<ValueId>,
    ) {
        let callee = &self.reach.funcs[f];
        for (&p, a) in callee.params.iter().zip(args) {
            if callee.locals[p].convention != Some(Convention::Set) {
                continue;
            }
            let TExprKind::Ref(place) = &a.kind else {
                continue;
            };
            let TExprKind::Local(l) = place.kind else {
                continue;
            };
            let Some(flag) = self.flags[l] else {
                continue;
            };
            let ok = if ret.as_result().is_none() {
                self.b.const_bool(true)
            } else {
                // `ok` is variant 0, in the low bits.
                let tag = match (result, dst) {
                    (Some(p), _) if returns_packed(ret) => {
                        self.unpack_scalar(p, 0, Ty::Int(IntTy::new(false, 8)))
                    }
                    (_, Some(d)) => self.load_tag(d, ret),
                    _ => unreachable!("a result packed or in memory"),
                };
                let zero = self.b.const_i64(self.t.i8, 0);
                self.b.icmp(IntPred::Eq, tag, zero)
            };
            self.b.store(self.t.bool, flag, ok, 1);
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
        let pa = self.struct_field(dst, ty, 0);
        let na = self.struct_field(dst, ty, 1);
        self.b.store(self.t.ptr, pa, p, 8);
        self.b.store(self.t.i64, na, n, 8);
    }

    /// The IR type of a value stored in memory: a scalar, or an array or a
    /// struct of them.
    fn ir_ty(&mut self, ty: Ty) -> TypeId {
        ir_type(self.b.types_mut(), self.t, ty)
    }

    /// The IR layout of an enum or an optional (see the module docs).
    fn sum_ir(&mut self, ty: Ty) -> SumIr {
        sum_layout(self.b.types_mut(), self.t, ty)
    }

    /// The tag of the enum or optional of type `ty` at `base`.
    fn load_tag(&mut self, base: ValueId, ty: Ty) -> ValueId {
        let sum = self.sum_ir(ty);
        let addr = self.struct_field(base, sum.ty, 0);
        let tag = self.t.int(sum.tag);
        self.b.load(tag, addr, align_of(Ty::Int(sum.tag)))
    }

    /// Make the enum or optional of type `ty` at `base` variant `variant`
    /// (its payload is written separately).
    fn store_tag(&mut self, base: ValueId, ty: Ty, variant: u32) {
        let sum = self.sum_ir(ty);
        let addr = self.struct_field(base, sum.ty, 0);
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
        let area = self.struct_field(base, sum.ty, 1);
        let payload = sum.payloads[variant as usize].expect("a variant with a payload");
        self.struct_field(area, payload, field)
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
        if returns_packed(opt.ty)
            && (matches!(opt.kind, TExprKind::Call(..)) || self.packed_slot(opt).is_some())
        {
            return self.coalesce_packed(opt, default, ty);
        }
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

    /// `call ?? default`, of type `ty`, for a call returning its optional
    /// packed: the value is taken from the packed form, not from memory.
    fn coalesce_packed(&mut self, call: &TExpr, default: &TExpr, ty: Ty) -> Val {
        let p = self.pack(call);
        let tag = self.unpack_scalar(p, 0, Ty::Int(IntTy::new(false, 8)));
        let some_bb = self.b.create_block(&[]);
        let none_bb = self.b.create_block(&[]);
        let targets = [(vec![1], some_bb), (vec![0], none_bb)];
        if ty.in_memory() {
            let ir_ty = self.ir_ty(ty);
            let tmp = self.b.alloca(ir_ty);
            let join = self.b.create_block(&[]);
            self.branch_on_tag(tag, call.ty, &targets);
            self.start_block(some_bb);
            self.unpack(tmp, ty, p, OPTIONAL_TAG_BITS);
            self.b.br(join, &[]);
            self.start_block(none_bb);
            self.fill(tmp, default);
            self.b.br(join, &[]);
            self.start_block(join);
            return Val::Mem(tmp);
        }
        let join = self.b.create_block(&[self.t.of(ty)]);
        self.branch_on_tag(tag, call.ty, &targets);
        self.start_block(some_bb);
        let v = self.unpack_scalar(p, OPTIONAL_TAG_BITS, ty);
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
        let addr = self.struct_field(dst, sum.ty, 0);
        self.b.store(tag, addr, v, align_of(Ty::Int(sum.tag)));
    }

    /// The packed form of `e`, whose type has one (see the module docs), as
    /// an `i64`. A call that returns it packed, and a variant, are packed
    /// without going through memory.
    fn pack(&mut self, e: &TExpr) -> ValueId {
        if let Some(p) = self.packed_local(e) {
            return p;
        }
        match &e.kind {
            TExprKind::Call(f, args) if returns_packed(e.ty) => {
                self.call(*f, args, e.ty, None).one()
            }
            // A payload field of a packed local: its bits, without those
            // of the fields above it.
            TExprKind::Payload(base, v, k) if self.packed_slot(base).is_some() => {
                let p = self.packed_local(base).expect("a packed local");
                let shift = payload_shift(base.ty, *v, *k);
                let bits = packed_bits(e.ty).expect("a packed payload");
                let mut v = p;
                if shift > 0 {
                    let amount = self.b.const_i64(self.t.i64, i64::from(shift));
                    v = self.b.bin(IrOp::LShr, v, amount, Flags::NONE);
                }
                if shift + bits < 64 {
                    let m = self.b.const_i64(self.t.i64, mask(u64::MAX, bits) as i64);
                    v = self.b.bin(IrOp::And, v, m, Flags::NONE);
                }
                v
            }
            TExprKind::Variant(v, values) => {
                let def = e.ty.sum().expect("an enum or an optional");
                let fields = &def.variants[*v as usize].fields;
                let mut bits = None;
                let mut shift = 0;
                for (value, f) in values.iter().zip(fields) {
                    let v = self.pack(value);
                    let acc = match bits {
                        Some(acc) => acc,
                        None => self.b.const_i64(self.t.i64, 0),
                    };
                    bits = Some(self.or_shifted(acc, v, shift));
                    shift += packed_bits(f.ty).expect("a packed payload");
                }
                self.pack_variant(e.ty, *v, bits)
            }
            _ if e.ty == Ty::Unit => {
                self.expr(e);
                self.b.const_i64(self.t.i64, 0)
            }
            _ if !e.ty.in_memory() => {
                let v = self.expr(e).one();
                self.widen(v, e.ty)
            }
            _ => {
                let addr = self.place(e);
                self.pack_mem(addr, e.ty)
            }
        }
    }

    /// Whether [`pack`](Self::pack) gets the packed form of `e` without
    /// reading it from memory: a call returning it packed, a local kept
    /// packed, or a variant whose payload packs cheaply too.
    fn packs_cheaply(&self, e: &TExpr) -> bool {
        match &e.kind {
            TExprKind::Call(..) => returns_packed(e.ty),
            TExprKind::Local(_) => self.packed_slot(e).is_some(),
            TExprKind::Variant(_, values) => values
                .iter()
                .all(|v| !v.ty.in_memory() || self.packs_cheaply(v)),
            _ => false,
        }
    }

    /// The `i64` slot of `e`, if it's a local kept in packed form.
    fn packed_slot(&self, e: &TExpr) -> Option<ValueId> {
        match e.kind {
            TExprKind::Local(l) => match self.slots[l] {
                Slot::Packed(slot, _) => Some(slot),
                _ => None,
            },
            _ => None,
        }
    }

    /// The value of `e`, if it's a local kept in packed form.
    fn packed_local(&mut self, e: &TExpr) -> Option<ValueId> {
        let slot = self.packed_slot(e)?;
        Some(self.b.load(self.t.i64, slot, 8))
    }

    /// The tag of `e`, an enum, an optional or a result.
    fn tag_of(&mut self, e: &TExpr) -> ValueId {
        match self.packed_local(e) {
            Some(p) => {
                let def = e.ty.sum().expect("an enum, an optional or a result");
                self.unpack_scalar(p, 0, Ty::Int(def.tag))
            }
            None => {
                let base = self.place(e);
                self.load_tag(base, e.ty)
            }
        }
    }

    /// Payload field `field` of variant `variant` of the value of type
    /// `ty` whose packed form is `p`.
    fn packed_field(&mut self, p: ValueId, ty: Ty, variant: u32, field: u32) -> Val {
        let def = ty.sum().expect("an enum, an optional or a result");
        let shift = payload_shift(ty, variant, field);
        let fty = def.variants[variant as usize].fields[field as usize].ty;
        if fty == Ty::Unit {
            return Val::Unit;
        }
        if fty.in_memory() {
            let ir_ty = self.ir_ty(fty);
            let tmp = self.b.alloca(ir_ty);
            self.unpack(tmp, fty, p, shift);
            return Val::Mem(tmp);
        }
        Val::One(self.unpack_scalar(p, shift, fty))
    }

    /// The packed form of variant `variant` of the enum, optional or
    /// result `ty`, with the packed form of its payload `payload` (none
    /// for a variant without one).
    fn pack_variant(&mut self, ty: Ty, variant: u32, payload: Option<ValueId>) -> ValueId {
        let def = ty.sum().expect("an enum, an optional or a result");
        let value = const_bits(def.variants[variant as usize].value, def.tag);
        let tag = self
            .b
            .const_i64(self.t.i64, mask(value as u64, def.tag.bits) as i64);
        match payload {
            Some(p) => self.or_shifted(tag, p, def.tag.bits),
            None => tag,
        }
    }

    /// The packed form of the value of type `ty` at `addr`. Only the active
    /// variant's payload is used: the others are read but not selected.
    fn pack_mem(&mut self, addr: ValueId, ty: Ty) -> ValueId {
        if ty == Ty::Unit {
            return self.b.const_i64(self.t.i64, 0);
        }
        if !ty.in_memory() {
            let ir_ty = self.t.of(ty);
            let v = self.b.load(ir_ty, addr, align_of(ty));
            return self.widen(v, ty);
        }
        let def = ty.sum().expect("an enum, an optional or a result");
        let tag_ty = Ty::Int(def.tag);
        let tag = self.load_tag(addr, ty);
        let mut payload = None;
        for (v, variant) in def.variants.iter().enumerate() {
            if variant.fields.is_empty() {
                continue;
            }
            let mut bits = self.b.const_i64(self.t.i64, 0);
            let mut shift = 0;
            for (k, f) in variant.fields.iter().enumerate() {
                let at = self.payload_at(addr, ty, v as u32, k as u32);
                let field = self.pack_mem(at, f.ty);
                bits = self.or_shifted(bits, field, shift);
                shift += packed_bits(f.ty).expect("a packed payload");
            }
            let value = self
                .b
                .const_i64(self.t.int(def.tag), const_bits(variant.value, def.tag));
            let is = self.b.icmp(IntPred::Eq, tag, value);
            let other = match payload {
                Some(p) => p,
                None => self.b.const_i64(self.t.i64, 0),
            };
            payload = Some(self.b.select(is, bits, other));
        }
        let tag = self.widen(tag, tag_ty);
        match payload {
            Some(p) => self.or_shifted(tag, p, def.tag.bits),
            None => tag,
        }
    }

    /// Store the value of type `ty` whose packed form is in the bits of
    /// `p` from `shift` up at `addr`. The payload of the active variant is
    /// written; when only one variant has a payload, it's written whatever
    /// the variant.
    fn unpack(&mut self, addr: ValueId, ty: Ty, p: ValueId, shift: u32) {
        if ty == Ty::Unit {
            return;
        }
        if !ty.in_memory() {
            let v = self.unpack_scalar(p, shift, ty);
            let ir_ty = self.t.of(ty);
            self.b.store(ir_ty, addr, v, align_of(ty));
            return;
        }
        let def = ty.sum().expect("an enum, an optional or a result");
        let tag_ty = Ty::Int(def.tag);
        let tag = self.unpack_scalar(p, shift, tag_ty);
        let sum = self.sum_ir(ty);
        let tag_addr = self.struct_field(addr, sum.ty, 0);
        self.b
            .store(self.t.int(def.tag), tag_addr, tag, align_of(tag_ty));
        let payload_at = shift + def.tag.bits;
        let write = |this: &mut Self, v: u32| {
            let mut at = payload_at;
            for (k, f) in def.variants[v as usize].fields.iter().enumerate() {
                let field = this.payload_at(addr, ty, v, k as u32);
                this.unpack(field, f.ty, p, at);
                at += packed_bits(f.ty).expect("a packed payload");
            }
        };
        let with: Vec<u32> = (0..def.variants.len() as u32)
            .filter(|&v| !def.variants[v as usize].fields.is_empty())
            .collect();
        if let [only] = with[..] {
            write(self, only);
        } else {
            self.each_payload(tag, ty, write);
        }
    }

    /// The scalar of type `ty` whose packed form is in the bits of `p`
    /// from `shift` up.
    fn unpack_scalar(&mut self, p: ValueId, shift: u32, ty: Ty) -> ValueId {
        let v = if shift == 0 {
            p
        } else {
            let amount = self.b.const_i64(self.t.i64, i64::from(shift));
            self.b.bin(IrOp::LShr, p, amount, Flags::NONE)
        };
        match ty {
            Ty::Int(t) if t.bits == 64 => v,
            _ => {
                let ir_ty = self.t.of(ty);
                self.b.cast(CastOp::Trunc, v, ir_ty)
            }
        }
    }

    /// The scalar `v` of type `ty` (a `bool` or an integer) zero-extended
    /// to an `i64`.
    fn widen(&mut self, v: ValueId, ty: Ty) -> ValueId {
        match ty {
            Ty::Int(t) if t.bits == 64 => v,
            _ => self.b.cast(CastOp::ZExt, v, self.t.i64),
        }
    }

    /// `acc | v << shift`, folded when both are constants or `v` is 0.
    fn or_shifted(&mut self, acc: ValueId, v: ValueId, shift: u32) -> ValueId {
        let (a, x) = (self.const_u64(acc), self.const_u64(v));
        if x == Some(0) {
            return acc;
        }
        if let (Some(a), Some(x)) = (a, x) {
            return self.b.const_i64(self.t.i64, (a | x << shift) as i64);
        }
        let shifted = if shift == 0 {
            v
        } else {
            let amount = self.b.const_i64(self.t.i64, i64::from(shift));
            self.b.bin(IrOp::Shl, v, amount, Flags::NONE)
        };
        if a == Some(0) {
            return shifted;
        }
        self.b.bin(IrOp::Or, acc, shifted, Flags::NONE)
    }

    /// The storage of an expression whose value lives in memory.
    fn place(&mut self, e: &TExpr) -> ValueId {
        match self.expr(e) {
            Val::Mem(p) => p,
            other => unreachable!("{} lowered to {other:?}", e.ty),
        }
    }

    /// `base` moved by the constant `bytes`: `base` itself for 0, so a
    /// field, payload or element at offset 0 costs no instruction (LF
    /// counts each one against its inlining threshold).
    ///
    /// The same address computed again in the same block is the earlier
    /// `ptr_add` (LF's optimizer treats `ptr_add` as opaque, so it doesn't
    /// merge them).
    fn byte_offset(&mut self, base: ValueId, bytes: u64) -> ValueId {
        if bytes == 0 {
            return base;
        }
        let block = self.b.current_block().expect("in a block");
        if let Some(&addr) = self.addrs.get(&(block, base, bytes)) {
            return addr;
        }
        let off = self.b.const_i64(self.t.i64, bytes as i64);
        let addr = self.b.ptr_add(base, off, true);
        self.addrs.insert((block, base, bytes), addr);
        addr
    }

    /// The address of field `i` of the IR struct `ty` at `base`.
    fn struct_field(&mut self, base: ValueId, ty: TypeId, i: u32) -> ValueId {
        let (offset, _) = self.b.types().field_offset(ty, i);
        self.byte_offset(base, offset)
    }

    /// The address of element `index` (an `i64`) of an array of the IR type
    /// `elem` at `base`. A constant index is a constant offset, and an
    /// element of one byte needs no multiplication.
    fn array_elem(&mut self, base: ValueId, elem: TypeId, index: ValueId) -> ValueId {
        let stride = self.b.types().stride(elem);
        if let Some(k) = self.const_u64(index) {
            return self.byte_offset(base, k.wrapping_mul(stride));
        }
        let offset = if stride == 1 {
            index
        } else {
            let s = self.b.const_i64(self.t.i64, stride as i64);
            self.b.mul(index, s, Flags::NONE)
        };
        self.b.ptr_add(base, offset, true)
    }

    /// The value of `v` if it's an integer constant that fits in a `u64`.
    fn const_u64(&self, v: ValueId) -> Option<u64> {
        let c = self.b.const_of(v)?;
        match self.b.consts().get(c) {
            Const::Int { value, .. } => value.to_u64(),
            _ => None,
        }
    }

    /// The address of field `i` of the struct of type `ty` at `base`.
    fn field_at(&mut self, base: ValueId, ty: Ty, i: u32) -> ValueId {
        let ir_ty = self.ir_ty(ty);
        self.struct_field(base, ir_ty, i)
    }

    /// The split local and the index of its first scalar, if `e` is a
    /// split local or a field of one ([`split_locals`]). Its scalars are
    /// the next [`leaf_count`]`(e.ty)` ones.
    fn split_path(&self, e: &TExpr) -> Option<(usize, usize)> {
        match &e.kind {
            TExprKind::Local(l) => match self.slots[*l] {
                Slot::Split(k) => Some((k, 0)),
                _ => None,
            },
            TExprKind::Field(base, i) => {
                let (k, start) = self.split_path(base)?;
                let def = base.ty.as_struct().expect("a struct");
                let before: usize = def.fields[..*i as usize]
                    .iter()
                    .map(|f| leaf_count(f.ty))
                    .sum();
                Some((k, start + before))
            }
            _ => None,
        }
    }

    /// The scalars of split local `k` from `start` on that make up a value
    /// of type `ty`.
    fn load_leaves(&mut self, k: usize, start: usize, ty: Ty) -> Vec<ValueId> {
        (start..start + leaf_count(ty))
            .map(|j| {
                let (slot, t) = self.splits[k][j];
                let ir_ty = self.t.of(t);
                self.b.load(ir_ty, slot, align_of(t))
            })
            .collect()
    }

    /// Store `vals` in the slots of split local `k` from `start` on.
    fn store_leaves(&mut self, k: usize, start: usize, vals: &[ValueId]) {
        for (j, &v) in vals.iter().enumerate() {
            let (slot, t) = self.splits[k][start + j];
            let ir_ty = self.t.of(t);
            self.b.store(ir_ty, slot, v, align_of(t));
        }
    }

    /// The scalars of `e`, of a type [`leaf_tys`] splits, in its order. A
    /// struct literal is evaluated field by field (in source order), a
    /// split local is read from its slots, and any other value from
    /// memory. Every scalar is read before any is stored, so `p = Point{x:
    /// p.y, y: p.x}` is fine.
    fn leaf_values(&mut self, e: &TExpr) -> Vec<ValueId> {
        if let Some((k, start)) = self.split_path(e) {
            return self.load_leaves(k, start, e.ty);
        }
        match &e.kind {
            TExprKind::StructLit(fields) => {
                let def = e.ty.as_struct().expect("a struct");
                let mut each = vec![Vec::new(); def.fields.len()];
                for (i, value) in fields {
                    each[*i as usize] = self.leaf_values(value);
                }
                each.concat()
            }
            _ if e.ty == Ty::Unit => {
                self.expr(e);
                Vec::new()
            }
            _ if !e.ty.in_memory() => vec![self.expr(e).one()],
            _ => {
                let addr = self.place(e);
                let mut vals = Vec::new();
                self.read_leaves(addr, e.ty, &mut vals);
                vals
            }
        }
    }

    /// Append the scalars of the value of type `ty` at `addr` to `out`.
    fn read_leaves(&mut self, addr: ValueId, ty: Ty, out: &mut Vec<ValueId>) {
        match ty.as_struct() {
            Some(def) => {
                for (i, f) in def.fields.iter().enumerate() {
                    let at = self.field_at(addr, ty, i as u32);
                    self.read_leaves(at, f.ty, out);
                }
            }
            None if ty == Ty::Unit => {}
            None => out.push(self.read(addr, ty).one()),
        }
    }

    /// Store the scalars `vals` of a value of type `ty` at `addr`.
    fn write_leaves(&mut self, addr: ValueId, ty: Ty, vals: &mut impl Iterator<Item = ValueId>) {
        match ty.as_struct() {
            Some(def) => {
                for (i, f) in def.fields.iter().enumerate() {
                    let at = self.field_at(addr, ty, i as u32);
                    self.write_leaves(at, f.ty, vals);
                }
            }
            None if ty == Ty::Unit => {}
            None => {
                let v = vals.next().expect("a scalar for each");
                self.write(addr, Val::One(v), ty);
            }
        }
    }

    /// Copy `e`, a split local or a field of one, to `dst`.
    fn write_split(&mut self, dst: ValueId, e: &TExpr) {
        let vals = self.leaf_values(e);
        self.write_leaves(dst, e.ty, &mut vals.into_iter());
    }

    /// Whether every scalar in `a` equals the one at the same place in `b`.
    fn leaves_equal(&mut self, a: &[ValueId], b: &[ValueId]) -> ValueId {
        let mut eq = None;
        for (&x, &y) in a.iter().zip(b) {
            let same = self.b.icmp(IntPred::Eq, x, y);
            eq = Some(match eq {
                Some(acc) => self.b.bin(IrOp::And, acc, same, Flags::NONE),
                None => same,
            });
        }
        eq.unwrap_or_else(|| self.b.const_bool(true))
    }

    /// The address of the element or field an [`TExprKind::Index`] or a
    /// [`TExprKind::Field`] names.
    fn address(&mut self, e: &TExpr) -> ValueId {
        match &e.kind {
            TExprKind::Static(k) => {
                let g = self.statics[*k].expect("a static the program uses");
                return self.b.global_ref(g);
            }
            TExprKind::Deref(p) => return self.expr(p).one(),
            _ => {}
        }
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
        self.array_elem(base, elem, i)
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
        self.array_elem(base, ir_ty, k)
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
        if let Some((elem, n)) = ty.as_known_array() {
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
            let s = self.struct_field(src, sum.ty, 0);
            let d = self.struct_field(dst, sum.ty, 0);
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
        if let Some((elem, n)) = ty.as_known_array() {
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
                let (elem, _) = e.ty.as_known_array().expect("an array");
                let later = later_leaves(elems.iter());
                let pending = self.defers.last().map_or(0, Vec::len);
                for (k, el) in elems.iter().enumerate() {
                    let at = self.b.const_i64(self.t.i64, k as i64);
                    let d = self.elem_at(dst, elem, at);
                    self.fill_or_write(d, el);
                    self.built(d, el, later[k]);
                }
                self.complete(pending);
            }
            TExprKind::StructLit(fields) => {
                let later = later_leaves(fields.iter().map(|(_, v)| v));
                let pending = self.defers.last().map_or(0, Vec::len);
                for (k, (i, value)) in fields.iter().enumerate() {
                    let d = self.field_at(dst, e.ty, *i);
                    self.fill_or_write(d, value);
                    self.built(d, value, later[k]);
                }
                self.complete(pending);
            }
            TExprKind::Call(f, args) => {
                self.call(*f, args, e.ty, Some(dst));
            }
            TExprKind::Variant(v, values) => {
                self.store_tag(dst, e.ty, *v);
                let later = later_leaves(values.iter());
                let pending = self.defers.last().map_or(0, Vec::len);
                for (k, value) in values.iter().enumerate() {
                    let d = self.payload_at(dst, e.ty, *v, k as u32);
                    self.fill_or_write(d, value);
                    self.built(d, value, later[k]);
                }
                self.complete(pending);
            }
            TExprKind::Intrinsic(Intrinsic::PtrRead, args) => {
                let src = self.expr(&args[0]).one();
                self.copy(dst, src, e.ty);
            }
            TExprKind::EnumFrom(x) => self.enum_from(dst, e.ty, x),
            TExprKind::Compare(a, b) => self.compare(dst, e.ty, a, b),
            // The optional is copied, and `none` written in its place.
            TExprKind::Intrinsic(Intrinsic::Take, args) => {
                let TExprKind::Ref(place) = &args[0].kind else {
                    unreachable!("`take` takes a place")
                };
                let src = self.place(place);
                self.copy(dst, src, e.ty);
                self.store_tag(src, e.ty, 0);
            }
            TExprKind::ArrayRepeat(value) => {
                let (elem, n) = e.ty.as_known_array().expect("an array");
                let v = self.expr(value);
                self.each_elem(n, elem, |this, k| {
                    let d = this.elem_at(dst, elem, k);
                    this.write(d, v, elem);
                });
            }
            _ if self.split_path(e).is_some() => self.write_split(dst, e),
            _ => {
                let src = self.place(e);
                self.copy(dst, src, e.ty);
            }
        }
    }

    /// A part `e` of an aggregate was built at `addr`: when a later part
    /// may leave early (`later`) and `e` needs destruction, it's destroyed
    /// at such an exit, until the aggregate is complete.
    fn built(&mut self, addr: ValueId, e: &TExpr, later: bool) {
        if later
            && e.ty.needs_destroy()
            && let Some(scope) = self.defers.last_mut()
        {
            scope.push(Defer::Place(addr, e.ty));
        }
    }

    /// An aggregate is complete: its parts, registered since `pending`
    /// (the length of the innermost scope's list then), are its own.
    fn complete(&mut self, pending: usize) {
        if let Some(scope) = self.defers.last_mut() {
            scope.truncate(pending);
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
        if self.split_path(e).is_some() {
            self.write_split(dst, e);
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
