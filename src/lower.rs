//! Lowering: the checked program to LatticeFoundry IR.
//!
//! Every local gets a stack slot (`alloca`) in the entry block; LF's mem2reg
//! promotes them to SSA values at `-O1` and above. Every operation reaching
//! this pass has been proven safe by the checker, so proven arithmetic carries
//! `nsw`/`nuw` flags and nothing here emits a run-time check.
//!
//! A `str` is two IR values, its pointer and its length: it's passed as two
//! parameters and stored in two slots. String literals become read-only data
//! symbols ([`Lowered::strings`]) that the object writer emits.

use latticefoundry::Module;
use latticefoundry::ir::builder::FunctionBuilder;
use latticefoundry::ir::{
    BinOp as IrOp, BlockId, CastOp, Const, Flags, FuncId as IrFunc, Global, GlobalId, IntPred,
    TypeId, ValueId,
};
use latticefoundry::support::StrInterner;

use crate::sema::{CmpOp, Func, Mode, Program, TBinOp, TExpr, TExprKind, TStmt, TUnOp};
use crate::types::{IntTy, Ty};

/// The entry symbol LatticeFoundry's linker calls from `_start`; its return
/// value becomes the process exit status.
pub const ENTRY_SYMBOL: &str = "main";

/// The result of lowering.
#[derive(Debug)]
pub struct Lowered {
    pub module: Module,
    pub syms: StrInterner,
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
            Ty::Str => unreachable!("a str is two values"),
        }
    }

    /// The IR values a Lode value is made of, as parameter types.
    fn parts(&self, ty: Ty) -> Vec<TypeId> {
        match ty {
            Ty::Unit => Vec::new(),
            Ty::Str => vec![self.ptr, self.i64],
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
    /// A `str`: pointer and length.
    Str(ValueId, ValueId),
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
            Val::Str(p, n) => vec![p, n],
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
    Str {
        ptr: ValueId,
        len: ValueId,
    },
}

/// Lower a checked program to an IR module named `name`. If the program has a
/// `main`, an entry function named [`ENTRY_SYMBOL`] is added that calls it and
/// returns its exit status as an `i64`.
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
        strings.push((symbol, bytes.clone()));
    }

    let ids: Vec<IrFunc> = program
        .funcs
        .iter()
        .map(|f| {
            let params = f
                .params
                .iter()
                .flat_map(|&p| t.parts(f.locals[p].ty))
                .collect();
            let sig = module.types_mut().func(params, t.of(f.ret), false);
            module.declare_function(syms.intern(&f.symbol), sig)
        })
        .collect();

    for (f, &id) in program.funcs.iter().zip(&ids) {
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
        }
        .function(f);
    }

    if let Some(main) = program.main {
        let sig = module.types_mut().func(Vec::new(), t.i64, false);
        let entry = module.declare_function(syms.intern(ENTRY_SYMBOL), sig);
        let ret = program.funcs[main].ret;
        let mut b = module.build(entry);
        b.create_entry_block();
        let callee = b.func_ref(ids[main]);
        let result = b.call(callee, &[], t.of(ret));
        let status = match (ret, result) {
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
        };
        b.ret(Some(status));
    }

    Lowered {
        module,
        syms,
        strings,
    }
}

struct FnLower<'a> {
    b: FunctionBuilder<'a>,
    t: Types,
    ids: &'a [IrFunc],
    strings: &'a [GlobalId],
    string_lens: &'a [Vec<u8>],
    slots: Vec<Slot>,
    /// `(continue target, break target)` of each enclosing loop.
    loops: Vec<(BlockId, BlockId)>,
    /// Whether the current block already has its terminator.
    terminated: bool,
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
                Ty::Str => Slot::Str {
                    ptr: self.b.alloca(self.t.ptr),
                    len: self.b.alloca(self.t.i64),
                },
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
                Ty::Str => {
                    let v = Val::Str(self.b.param(entry, next), self.b.param(entry, next + 1));
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
                self.b.ret(None);
            } else {
                // The checker proved every path returns, so this block is dead.
                self.b.unreachable();
            }
        }
    }

    fn store(&mut self, local: usize, val: Val) {
        match (self.slots[local], val) {
            (Slot::One { slot, ty, align }, Val::One(v)) => self.b.store(ty, slot, v, align),
            (Slot::Str { ptr, len }, Val::Str(p, n)) => {
                self.b.store(self.t.ptr, ptr, p, 8);
                self.b.store(self.t.i64, len, n, 8);
            }
            (slot, val) => unreachable!("storing {val:?} into {slot:?}"),
        }
    }

    fn load(&mut self, local: usize) -> Val {
        match self.slots[local] {
            Slot::One { slot, ty, align } => Val::One(self.b.load(ty, slot, align)),
            Slot::Str { ptr, len } => {
                let p = self.b.load(self.t.ptr, ptr, 8);
                let n = self.b.load(self.t.i64, len, 8);
                Val::Str(p, n)
            }
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
            TStmt::Init(local, e) | TStmt::Assign(local, e) => {
                let v = self.expr(e);
                self.store(*local, v);
            }
            TStmt::Expr(e) => {
                self.expr(e);
            }
            TStmt::Return(value) => {
                let v = value.as_ref().map(|e| self.expr(e).one());
                self.b.ret(v);
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
                return Val::Str(p, n);
            }
            TExprKind::Local(local) => return self.load(*local),
            TExprKind::Call(f, args) => {
                let args: Vec<ValueId> = args.iter().flat_map(|a| self.expr(a).parts()).collect();
                let callee = self.b.func_ref(self.ids[*f]);
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
            TExprKind::StrLen(s) => match self.expr(s) {
                Val::Str(_, n) => n,
                other => unreachable!("`len` of {other:?}"),
            },
            TExprKind::StrPtr(s) => match self.expr(s) {
                Val::Str(p, _) => p,
                other => unreachable!("`ptr` of {other:?}"),
            },
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
