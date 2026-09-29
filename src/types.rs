//! Lode types and integer value ranges.

use std::fmt;

/// A fixed-width integer type. `size` marks `usize`/`isize`, which are distinct
/// types from the same-width `u64`/`i64` even though they share a layout.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct IntTy {
    pub signed: bool,
    pub bits: u32,
    pub size: bool,
}

impl IntTy {
    pub const fn new(signed: bool, bits: u32) -> IntTy {
        IntTy {
            signed,
            bits,
            size: false,
        }
    }

    pub fn min(self) -> i128 {
        if self.signed {
            -(1i128 << (self.bits - 1))
        } else {
            0
        }
    }

    pub fn max(self) -> i128 {
        if self.signed {
            (1i128 << (self.bits - 1)) - 1
        } else {
            (1i128 << self.bits) - 1
        }
    }

    /// Every value of the type.
    pub fn range(self) -> Range {
        Range {
            lo: self.min(),
            hi: self.max(),
        }
    }
}

impl fmt::Display for IntTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sign = if self.signed { 'i' } else { 'u' };
        if self.size {
            write!(f, "{sign}size")
        } else {
            write!(f, "{sign}{}", self.bits)
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    Int(IntTy),
    Bool,
    Unit,
    /// A UTF-8 string view: a pointer and a length in bytes. The standard
    /// library's `Str[E]` will replace it once there are generics
    /// (docs/strings.md); `str` stays the name for `Str[utf8]`.
    Str,
    /// A raw pointer `*T` to an integer type. Only usable in `unsafe` code.
    Ptr(IntTy),
}

impl Ty {
    pub fn as_int(self) -> Option<IntTy> {
        match self {
            Ty::Int(t) => Some(t),
            _ => None,
        }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Int(t) => t.fmt(f),
            Ty::Bool => f.write_str("bool"),
            Ty::Unit => f.write_str("()"),
            Ty::Str => f.write_str("str"),
            Ty::Ptr(t) => write!(f, "*{t}"),
        }
    }
}

/// The result of looking up a primitive type name.
#[derive(Debug)]
pub enum Primitive {
    Ty(Ty),
    /// A known type name the compiler can't handle yet.
    Unsupported,
}

/// Look up a primitive type by name. `ptr_bits` is the target's address width,
/// which gives `usize` and `isize` their size.
pub fn primitive(name: &str, ptr_bits: u32) -> Option<Primitive> {
    let int = |signed, bits| Some(Primitive::Ty(Ty::Int(IntTy::new(signed, bits))));
    match name {
        "i8" => int(true, 8),
        "i16" => int(true, 16),
        "i32" => int(true, 32),
        "i64" => int(true, 64),
        "u8" => int(false, 8),
        "u16" => int(false, 16),
        "u32" => int(false, 32),
        "u64" => int(false, 64),
        "isize" => Some(Primitive::Ty(Ty::Int(IntTy {
            signed: true,
            bits: ptr_bits,
            size: true,
        }))),
        "usize" => Some(Primitive::Ty(Ty::Int(IntTy {
            signed: false,
            bits: ptr_bits,
            size: true,
        }))),
        "bool" => Some(Primitive::Ty(Ty::Bool)),
        "str" => Some(Primitive::Ty(Ty::Str)),
        "i128" | "u128" | "f16" | "f32" | "f64" | "string" | "never" => {
            Some(Primitive::Unsupported)
        }
        _ => None,
    }
}

/// An inclusive range of integer values that an expression is known to lie in.
/// This is the fact language of the proof-obligation checker (docs/safety.md):
/// an operation is accepted when the ranges of its operands prove it safe.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Range {
    pub lo: i128,
    pub hi: i128,
}

impl Range {
    pub fn exact(v: i128) -> Range {
        Range { lo: v, hi: v }
    }

    /// The range of `a op b` for a monotone-per-corner operation, or `None` if
    /// a corner overflows `i128` (which means it certainly overflows any
    /// supported type).
    fn corners(a: Range, b: Range, op: fn(i128, i128) -> Option<i128>) -> Option<Range> {
        let vals = [
            op(a.lo, b.lo)?,
            op(a.lo, b.hi)?,
            op(a.hi, b.lo)?,
            op(a.hi, b.hi)?,
        ];
        Some(Range {
            lo: *vals.iter().min()?,
            hi: *vals.iter().max()?,
        })
    }

    pub fn checked_add(self, o: Range) -> Option<Range> {
        Some(Range {
            lo: self.lo.checked_add(o.lo)?,
            hi: self.hi.checked_add(o.hi)?,
        })
    }

    pub fn checked_sub(self, o: Range) -> Option<Range> {
        Some(Range {
            lo: self.lo.checked_sub(o.hi)?,
            hi: self.hi.checked_sub(o.lo)?,
        })
    }

    pub fn checked_mul(self, o: Range) -> Option<Range> {
        Range::corners(self, o, i128::checked_mul)
    }

    /// The values in both ranges, or `None` if there are none.
    pub fn intersect(self, o: Range) -> Option<Range> {
        let r = Range {
            lo: self.lo.max(o.lo),
            hi: self.hi.min(o.hi),
        };
        (r.lo <= r.hi).then_some(r)
    }

    /// The smallest range containing both.
    pub fn hull(self, o: Range) -> Range {
        Range {
            lo: self.lo.min(o.lo),
            hi: self.hi.max(o.hi),
        }
    }

    pub fn contains(self, v: i128) -> bool {
        self.lo <= v && v <= self.hi
    }

    /// Whether every value of `self` is also in `outer`.
    pub fn within(self, outer: Range) -> bool {
        outer.lo <= self.lo && self.hi <= outer.hi
    }
}

impl fmt::Display for Range {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.lo == self.hi {
            write!(f, "{}", self.lo)
        } else {
            write!(f, "{}..={}", self.lo, self.hi)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn int_ranges() {
        assert_eq!(IntTy::new(false, 8).range(), Range { lo: 0, hi: 255 });
        assert_eq!(IntTy::new(true, 64).min(), i64::MIN as i128);
        assert_eq!(IntTy::new(false, 64).max(), u64::MAX as i128);
    }

    #[test]
    fn range_arithmetic() {
        let a = Range { lo: 0, hi: 10 };
        let b = Range { lo: -2, hi: 3 };
        assert_eq!(a.checked_add(b), Some(Range { lo: -2, hi: 13 }));
        assert_eq!(a.checked_sub(b), Some(Range { lo: -3, hi: 12 }));
        assert_eq!(a.checked_mul(b), Some(Range { lo: -20, hi: 30 }));
        let big = IntTy::new(false, 64).range();
        assert!(big.checked_mul(big).is_none());
    }
}
