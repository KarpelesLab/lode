//! Lode types and integer value ranges.

use std::collections::HashMap;
use std::fmt;
use std::sync::{Arc, Mutex, OnceLock};

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
    /// A fixed-size array `[N]T`: a [`Compound::Array`] in the interner.
    Array(CompoundId),
    /// A slice `[]T`, a read-only view like `str`: a [`Compound::Slice`] in
    /// the interner.
    Slice(CompoundId),
    /// A struct: a [`Compound::Struct`] in the interner. Structs are nominal,
    /// so each declaration is a type of its own.
    Struct(CompoundId),
    /// An enum (a sum type): a [`Compound::Enum`] in the interner. Nominal,
    /// like structs.
    Enum(CompoundId),
    /// An optional `?T`: a [`Compound::Optional`] in the interner. It works
    /// like an enum with two variants, `none` and `some(value: T)`.
    Optional(CompoundId),
}

impl Ty {
    pub fn as_int(self) -> Option<IntTy> {
        match self {
            Ty::Int(t) => Some(t),
            _ => None,
        }
    }

    /// The array type `[len]elem`.
    pub fn array(elem: Ty, len: u64) -> Ty {
        Ty::Array(intern(Compound::Array { elem, len }))
    }

    /// The slice type `[]elem`.
    pub fn slice(elem: Ty) -> Ty {
        Ty::Slice(intern(Compound::Slice { elem }))
    }

    /// The element type and length of an array type.
    pub fn as_array(self) -> Option<(Ty, u64)> {
        match self {
            Ty::Array(id) => match compound(id) {
                Compound::Array { elem, len } => Some((elem, len)),
                _ => unreachable!("an array id names another type"),
            },
            _ => None,
        }
    }

    /// The element type of a slice type.
    pub fn as_slice(self) -> Option<Ty> {
        match self {
            Ty::Slice(id) => match compound(id) {
                Compound::Slice { elem } => Some(elem),
                _ => unreachable!("a slice id names another type"),
            },
            _ => None,
        }
    }

    /// The element type of an array or slice.
    pub fn elem(self) -> Option<Ty> {
        self.as_array().map(|(elem, _)| elem).or(self.as_slice())
    }

    /// Whether values of this type are views, a pointer and a length (`str`
    /// and slices).
    pub fn is_view(self) -> bool {
        matches!(self, Ty::Str | Ty::Slice(_))
    }

    /// The optional type `?inner`.
    pub fn optional(inner: Ty) -> Ty {
        Ty::Optional(intern(Compound::Optional { inner }))
    }

    /// The type an optional `?T` holds, `T`.
    pub fn as_optional(self) -> Option<Ty> {
        match self {
            Ty::Optional(id) => match compound(id) {
                Compound::Optional { inner } => Some(inner),
                _ => unreachable!("an optional id names another type"),
            },
            _ => None,
        }
    }

    /// Whether values of this type live in memory, as places (arrays,
    /// structs, enums and optionals), rather than in registers.
    pub fn in_memory(self) -> bool {
        matches!(
            self,
            Ty::Array(_) | Ty::Struct(_) | Ty::Enum(_) | Ty::Optional(_)
        )
    }

    /// The declaration of an enum type (not an optional: see [`Ty::sum`]).
    pub fn as_enum(self) -> Option<Arc<EnumDef>> {
        match self {
            Ty::Enum(id) => match compound(id) {
                Compound::Enum { def } => Some(enum_def(def)),
                _ => unreachable!("an enum id names another type"),
            },
            _ => None,
        }
    }

    /// The variants of an enum or an optional, which share their layout and
    /// their operations. An optional `?T` is `none` (tag 0) or
    /// `some(value: T)` (tag 1).
    pub fn sum(self) -> Option<Arc<EnumDef>> {
        if let Some(def) = self.as_enum() {
            return Some(def);
        }
        let inner = self.as_optional()?;
        Some(Arc::new(EnumDef {
            name: self.to_string(),
            pkg: usize::MAX,
            is_pub: true,
            tag: IntTy::new(false, 8),
            explicit: false,
            variants: vec![
                Variant {
                    name: "none".to_owned(),
                    fields: Vec::new(),
                    value: 0,
                },
                Variant {
                    name: "some".to_owned(),
                    fields: vec![Field {
                        name: "value".to_owned(),
                        ty: inner,
                    }],
                    value: 1,
                },
            ],
        }))
    }

    /// Declare a new enum type named `name` (as shown in messages), from
    /// package `pkg`. Its variants are set once they're resolved, with
    /// [`Ty::set_variants`].
    pub fn new_enum(name: String, pkg: usize, is_pub: bool) -> Ty {
        let mut tables = interner().lock().unwrap_or_else(|e| e.into_inner());
        let def = u32::try_from(tables.enums.len()).expect("too many enums");
        tables.enums.push(Arc::new(EnumDef {
            name,
            pkg,
            is_pub,
            tag: IntTy::new(false, 8),
            explicit: false,
            variants: Vec::new(),
        }));
        drop(tables);
        Ty::Enum(intern(Compound::Enum { def }))
    }

    /// Set the tag type and variants of an enum type declared with
    /// [`Ty::new_enum`]. `explicit` marks an enum whose variants have
    /// declared integer values (`enum Color: u8 { red = 1 ... }`).
    pub fn set_variants(self, tag: IntTy, explicit: bool, variants: Vec<Variant>) {
        let Ty::Enum(id) = self else {
            unreachable!("not an enum: {self}")
        };
        let Compound::Enum { def } = compound(id) else {
            unreachable!("an enum id names another type")
        };
        let mut tables = interner().lock().unwrap_or_else(|e| e.into_inner());
        let entry = &mut tables.enums[def as usize];
        *entry = Arc::new(EnumDef {
            tag,
            explicit,
            variants,
            ..EnumDef::clone(entry)
        });
    }

    /// The declaration of a struct type.
    pub fn as_struct(self) -> Option<Arc<StructDef>> {
        match self {
            Ty::Struct(id) => match compound(id) {
                Compound::Struct { def } => Some(struct_def(def)),
                _ => unreachable!("a struct id names another type"),
            },
            _ => None,
        }
    }

    /// Declare a new struct type named `name` (as shown in messages), from
    /// package `pkg`. Its fields are set once they're resolved, with
    /// [`Ty::set_fields`].
    pub fn new_struct(name: String, pkg: usize, is_pub: bool) -> Ty {
        let mut tables = interner().lock().unwrap_or_else(|e| e.into_inner());
        let def = u32::try_from(tables.structs.len()).expect("too many structs");
        tables.structs.push(Arc::new(StructDef {
            name,
            pkg,
            is_pub,
            fields: Vec::new(),
        }));
        drop(tables);
        Ty::Struct(intern(Compound::Struct { def }))
    }

    /// Set the fields of a struct type declared with [`Ty::new_struct`].
    pub fn set_fields(self, fields: Vec<Field>) {
        let Ty::Struct(id) = self else {
            unreachable!("not a struct: {self}")
        };
        let Compound::Struct { def } = compound(id) else {
            unreachable!("a struct id names another type")
        };
        let mut tables = interner().lock().unwrap_or_else(|e| e.into_inner());
        let entry = &mut tables.structs[def as usize];
        *entry = Arc::new(StructDef {
            fields,
            ..StructDef::clone(entry)
        });
    }
}

/// A struct declaration: its name, where it's declared and its fields, in
/// declaration order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructDef {
    /// The name shown in messages: `Point`, or `os.Stat` for a struct of an
    /// imported package.
    pub name: String,
    /// The index of the declaring package (in the checker's package list).
    pub pkg: usize,
    pub is_pub: bool,
    pub fields: Vec<Field>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Field {
    pub name: String,
    pub ty: Ty,
}

impl StructDef {
    /// The index and type of the field called `name`.
    pub fn field(&self, name: &str) -> Option<(usize, Ty)> {
        self.fields
            .iter()
            .position(|f| f.name == name)
            .map(|i| (i, self.fields[i].ty))
    }
}

/// An enum declaration (or the variants of an optional, see [`Ty::sum`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnumDef {
    /// The name shown in messages, like [`StructDef::name`].
    pub name: String,
    /// The index of the declaring package (`usize::MAX` for an optional).
    pub pkg: usize,
    pub is_pub: bool,
    /// The type of the tag that tells the variants apart in memory.
    pub tag: IntTy,
    /// Whether the variants have declared integer values (a C-style enum).
    pub explicit: bool,
    pub variants: Vec<Variant>,
}

/// One variant of an enum: its name, its payload fields (none for a
/// variant without payload) and its tag value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Variant {
    pub name: String,
    pub fields: Vec<Field>,
    /// The tag value: the declared value of a C-style enum's variant, or
    /// else the variant's position.
    pub value: i128,
}

impl EnumDef {
    /// The index and declaration of the variant called `name`.
    pub fn variant(&self, name: &str) -> Option<(usize, &Variant)> {
        self.variants
            .iter()
            .enumerate()
            .find(|(_, v)| v.name == name)
    }
}

/// The index of a compound type in the global type interner.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CompoundId(u32);

/// A type made of other types. Compound types are interned (hash-consed) so
/// that [`Ty`] stays small and `Copy`: equal compound types always get the
/// same [`CompoundId`], so comparing ids compares the types.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Compound {
    Array {
        elem: Ty,
        len: u64,
    },
    Slice {
        elem: Ty,
    },
    /// A struct, by the index of its declaration: two declarations are two
    /// types, even with the same fields.
    Struct {
        def: u32,
    },
    /// An enum, by the index of its declaration.
    Enum {
        def: u32,
    },
    /// `?inner`.
    Optional {
        inner: Ty,
    },
}

/// The interner's tables. Entries are only ever appended, so an id stays
/// valid for the life of the process.
#[derive(Default)]
struct Interner {
    entries: Vec<Compound>,
    ids: HashMap<Compound, CompoundId>,
    structs: Vec<Arc<StructDef>>,
    enums: Vec<Arc<EnumDef>>,
}

fn interner() -> &'static Mutex<Interner> {
    static INTERNER: OnceLock<Mutex<Interner>> = OnceLock::new();
    INTERNER.get_or_init(Mutex::default)
}

/// The id of a compound type, adding it to the interner if it's new.
pub fn intern(c: Compound) -> CompoundId {
    let mut tables = interner().lock().unwrap_or_else(|e| e.into_inner());
    if let Some(&id) = tables.ids.get(&c) {
        return id;
    }
    let id = CompoundId(u32::try_from(tables.entries.len()).expect("too many types"));
    tables.entries.push(c);
    tables.ids.insert(c, id);
    id
}

/// The compound type an id stands for.
pub fn compound(id: CompoundId) -> Compound {
    let tables = interner().lock().unwrap_or_else(|e| e.into_inner());
    tables.entries[id.0 as usize]
}

fn struct_def(def: u32) -> Arc<StructDef> {
    let tables = interner().lock().unwrap_or_else(|e| e.into_inner());
    Arc::clone(&tables.structs[def as usize])
}

fn enum_def(def: u32) -> Arc<EnumDef> {
    let tables = interner().lock().unwrap_or_else(|e| e.into_inner());
    Arc::clone(&tables.enums[def as usize])
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Int(t) => t.fmt(f),
            Ty::Bool => f.write_str("bool"),
            Ty::Unit => f.write_str("()"),
            Ty::Str => f.write_str("str"),
            Ty::Ptr(t) => write!(f, "*{t}"),
            Ty::Array(id) | Ty::Slice(id) | Ty::Struct(id) | Ty::Enum(id) | Ty::Optional(id) => {
                match compound(*id) {
                    Compound::Array { elem, len } => write!(f, "[{len}]{elem}"),
                    Compound::Slice { elem } => write!(f, "[]{elem}"),
                    Compound::Struct { def } => f.write_str(&struct_def(def).name),
                    Compound::Enum { def } => f.write_str(&enum_def(def).name),
                    Compound::Optional { inner } => write!(f, "?{inner}"),
                }
            }
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

    #[test]
    fn interned_types_are_shared_and_display() {
        let u8_ = Ty::Int(IntTy::new(false, 8));
        let a = Ty::array(u8_, 4);
        assert_eq!(a, Ty::array(u8_, 4));
        assert_ne!(a, Ty::array(u8_, 5));
        assert_ne!(Ty::slice(u8_), Ty::slice(Ty::Bool));
        let nested = Ty::array(a, 3);
        assert_eq!(nested.as_array(), Some((a, 3)));
        assert_eq!(nested.to_string(), "[3][4]u8");
        assert_eq!(Ty::slice(a).to_string(), "[][4]u8");
        assert_eq!(Ty::slice(a).as_slice(), Some(a));
        assert_eq!(Ty::slice(a).elem(), Some(a));
        assert!(Ty::slice(u8_).is_view() && Ty::Str.is_view() && !a.is_view());
        let id = intern(Compound::Slice { elem: u8_ });
        assert_eq!(Ty::Slice(id), Ty::slice(u8_));
        assert_eq!(compound(id), Compound::Slice { elem: u8_ });
    }

    #[test]
    fn structs_are_nominal() {
        let u8_ = Ty::Int(IntTy::new(false, 8));
        let a = Ty::new_struct("P".into(), 0, false);
        let b = Ty::new_struct("P".into(), 1, true);
        let fields = vec![Field {
            name: "x".into(),
            ty: u8_,
        }];
        a.set_fields(fields.clone());
        b.set_fields(fields);
        assert_ne!(a, b);
        assert_eq!(a.to_string(), "P");
        let def = b.as_struct().expect("a struct");
        assert!(def.is_pub && def.pkg == 1);
        assert_eq!(def.field("x"), Some((0, u8_)));
        assert!(a.in_memory() && !a.is_view() && Ty::array(a, 2).in_memory());
    }

    #[test]
    fn enums_and_optionals() {
        let u8_ = Ty::Int(IntTy::new(false, 8));
        let e = Ty::new_enum("E".into(), 0, true);
        e.set_variants(
            IntTy::new(false, 8),
            false,
            vec![
                Variant {
                    name: "a".into(),
                    fields: Vec::new(),
                    value: 0,
                },
                Variant {
                    name: "b".into(),
                    fields: vec![Field {
                        name: "x".into(),
                        ty: u8_,
                    }],
                    value: 1,
                },
            ],
        );
        assert_eq!(e.to_string(), "E");
        let def = e.sum().expect("an enum");
        assert_eq!(def.variant("b").map(|(i, _)| i), Some(1));
        let o = Ty::optional(e);
        assert_eq!(o, Ty::optional(e));
        assert_eq!(o.to_string(), "?E");
        assert_eq!(o.as_optional(), Some(e));
        let sum = o.sum().expect("an optional");
        assert_eq!(sum.variants[1].fields[0].ty, e);
        assert!(e.in_memory() && o.in_memory() && o.as_enum().is_none());
    }
}
