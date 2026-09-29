//! Lowering: the checked program to LatticeFoundry IR.
//!
//! Every local gets a stack slot (`alloca`) in the entry block; LF's mem2reg
//! promotes them to SSA values at `-O1` and above. Every operation reaching
//! this pass has been proven safe by the checker, so proven arithmetic carries
//! `nsw`/`nuw` flags and nothing here emits a run-time check.

use latticefoundry::Module;
use latticefoundry::ir::builder::FunctionBuilder;
use latticefoundry::ir::{
    BinOp as IrOp, BlockId, CastOp, Flags, FuncId as IrFunc, IntPred, TypeId, ValueId,
};
use latticefoundry::support::StrInterner;

use crate::sema::{CmpOp, Func, Mode, Program, TBinOp, TExpr, TExprKind, TStmt, TUnOp};
use crate::types::{IntTy, Ty};

/// The entry symbol LatticeFoundry's linker calls from `_start`; its return
/// value becomes the process exit status.
pub const ENTRY_SYMBOL: &str = "main";

/// IR types for every Lode type, interned up front (the function builder
/// borrows the module, so types can't be interned while building).
#[derive(Clone, Copy)]
struct Types {
    void: TypeId,
    bool: TypeId,
    i8: TypeId,
    i16: TypeId,
    i32: TypeId,
    i64: TypeId,
}

impl Types {
    fn of(&self, ty: Ty) -> TypeId {
        match ty {
            Ty::Unit => self.void,
            Ty::Bool => self.bool,
            Ty::Int(t) => self.int(t),
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

/// Lower a checked program to an IR module. If the program has a `main`, an
/// entry function named [`ENTRY_SYMBOL`] is added that calls it and returns
/// its exit status as an `i64`.
pub fn lower(program: &Program) -> (Module, StrInterner) {
    let mut syms = StrInterner::new();
    let mut module = Module::new(program.package.clone());
    let t = {
        let types = module.types_mut();
        Types {
            void: types.void(),
            bool: types.bool(),
            i8: types.int(8),
            i16: types.int(16),
            i32: types.int(32),
            i64: types.int(64),
        }
    };

    let ids: Vec<IrFunc> = program
        .funcs
        .iter()
        .map(|f| {
            let params = f.params.iter().map(|&p| t.of(f.locals[p].ty)).collect();
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

    (module, syms)
}

struct FnLower<'a> {
    b: FunctionBuilder<'a>,
    t: Types,
    ids: &'a [IrFunc],
    /// The stack slot of each local.
    slots: Vec<(ValueId, TypeId, u32)>,
    /// `(continue target, break target)` of each enclosing loop.
    loops: Vec<(BlockId, BlockId)>,
    /// Whether the current block already has its terminator.
    terminated: bool,
}

fn align_of(ty: Ty) -> u32 {
    match ty {
        Ty::Int(t) => t.bits / 8,
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
            let ty = self.t.of(local.ty);
            let slot = self.b.alloca(ty);
            self.slots.push((slot, ty, align_of(local.ty)));
        }
        for (i, &p) in f.params.iter().enumerate() {
            let v = self.b.param(entry, i as u32);
            let (slot, ty, align) = self.slots[p];
            self.b.store(ty, slot, v, align);
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
                let (slot, ty, align) = self.slots[*local];
                self.b.store(ty, slot, v, align);
            }
            TStmt::Expr(e) => {
                self.expr_opt(e);
            }
            TStmt::Return(value) => {
                let v = value.as_ref().map(|e| self.expr(e));
                self.b.ret(v);
                self.terminated = true;
            }
            TStmt::If(cond, then, otherwise) => {
                let c = self.expr(cond);
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
                let c = self.expr(cond);
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

    fn expr(&mut self, e: &TExpr) -> ValueId {
        self.expr_opt(e).expect("expression has a value")
    }

    /// Lower an expression; `None` for a call to a function returning `()`.
    fn expr_opt(&mut self, e: &TExpr) -> Option<ValueId> {
        let ty = self.t.of(e.ty);
        Some(match &e.kind {
            TExprKind::Int(v) => {
                let it = e.ty.as_int().expect("integer literal");
                self.b.const_i64(ty, const_bits(*v, it))
            }
            TExprKind::Bool(v) => self.b.const_bool(*v),
            TExprKind::Local(local) => {
                let (slot, slot_ty, align) = self.slots[*local];
                self.b.load(slot_ty, slot, align)
            }
            TExprKind::Call(f, args) => {
                let args: Vec<ValueId> = args.iter().map(|a| self.expr(a)).collect();
                let callee = self.b.func_ref(self.ids[*f]);
                return self.b.call(callee, &args, ty);
            }
            TExprKind::Unary(op, operand) => {
                let v = self.expr(operand);
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
                let operand_ty = lhs.ty;
                let l = self.expr(lhs);
                let r = self.expr(rhs);
                self.binary(*op, operand_ty, ty, l, r, rhs.ty)
            }
            TExprKind::And(lhs, rhs) | TExprKind::Or(lhs, rhs) => {
                let is_and = matches!(e.kind, TExprKind::And(..));
                let l = self.expr(lhs);
                let rhs_bb = self.b.create_block(&[]);
                let merge = self.b.create_block(&[self.t.bool]);
                let short = self.b.const_bool(!is_and);
                if is_and {
                    self.b.cond_br(l, rhs_bb, &[], merge, &[short]);
                } else {
                    self.b.cond_br(l, merge, &[short], rhs_bb, &[]);
                }
                self.start_block(rhs_bb);
                let r = self.expr(rhs);
                self.b.br(merge, &[r]);
                self.start_block(merge);
                self.b.param(merge, 0)
            }
            TExprKind::Convert(inner) => {
                let v = self.expr(inner);
                let from = inner.ty.as_int().expect("integer conversion");
                let to = e.ty.as_int().expect("integer conversion");
                self.resize(v, from, to)
            }
        })
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
        ty: TypeId,
        l: ValueId,
        r: ValueId,
        rhs_ty: Ty,
    ) -> ValueId {
        let signed = operand.as_int().is_some_and(|t| t.signed);
        let proven = if signed { Flags::nsw() } else { Flags::nuw() };
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
