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
    /// The return type of a function that never returns (docs/types.md):
    /// every path in it ends the process or loops forever. A call to one
    /// has no value; where a value is expected, it stands for any type.
    Never,
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
    /// The result of calling a function that throws, `throws(E) -> T`: a
    /// [`Compound::Result`] in the interner. It works like an enum with two
    /// variants, `ok(value: T)` (`ok` when `T` is `()`) and `err(error: E)`.
    /// Only the checker's hidden locals and temporaries hold one: the
    /// program handles a call's result right away (`try`, `catch`, `match`).
    Result(CompoundId),
    /// A generic parameter (`T` in `fn max[T: Ordered]`, `N` in
    /// `struct StackBuf[N: usize]`), with its bounds or its integer type: a
    /// [`ParamDef`] in the interner. Only the checker sees it;
    /// instantiation replaces a type parameter with a concrete type, and a
    /// value parameter with a [`Ty::Value`]. A value parameter is never
    /// the type of a value: it's the length of an array (`[N]u8`) or a
    /// generic argument (`StackBuf[N]`).
    Param(ParamId),
    /// An integer known when compiling, as a generic argument for a value
    /// parameter (`64` in `StackBuf[64]`) or an array's length: a
    /// [`Compound::Value`] in the interner. Never the type of a value.
    Value(CompoundId),
}

/// The length of an array type: a number, or a value parameter (`[N]u8`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Len {
    Known(u64),
    /// A value parameter ([`Ty::Param`]) of type `usize`.
    Param(Ty),
}

impl Len {
    /// The length, if it's a number.
    pub fn known(self) -> Option<u64> {
        match self {
            Len::Known(n) => Some(n),
            Len::Param(_) => None,
        }
    }
}

impl fmt::Display for Len {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Len::Known(n) => write!(f, "{n}"),
            Len::Param(p) => p.fmt(f),
        }
    }
}

impl Ty {
    pub fn as_int(self) -> Option<IntTy> {
        match self {
            Ty::Int(t) => Some(t),
            _ => None,
        }
    }

    /// The declaration of a type parameter.
    pub fn as_param(self) -> Option<Arc<ParamDef>> {
        match self {
            Ty::Param(id) => Some(param_def(id)),
            _ => None,
        }
    }

    /// Declare a new type parameter named `name` with `bounds` (already
    /// closed under supertraits, see [`Bounds::new`]). `ptr_bits` is the
    /// target's address width: it sizes `usize` and `isize`, which a
    /// numeric bound admits.
    pub fn new_param(name: String, bounds: Bounds, ptr_bits: u32) -> Ty {
        let admitted: Vec<IntTy> = int_types(ptr_bits)
            .into_iter()
            .filter(|t| bounds.admits_int(*t))
            .collect();
        let numeric = bounds.has(Trait::Integer) && !admitted.is_empty();
        let values = numeric.then(|| {
            admitted
                .iter()
                .map(|t| t.range())
                .reduce(Range::hull)
                .expect("admitted types")
        });
        let fits = numeric.then(|| {
            admitted
                .iter()
                .map(|t| t.range())
                .reduce(|a, b| a.intersect(b).expect("every integer type holds 0"))
                .expect("admitted types")
        });
        let signed_min = admitted.iter().filter(|t| t.signed).map(|t| t.min()).max();
        Ty::push_param(ParamDef {
            name,
            bounds,
            values,
            fits,
            signed_min,
            value: None,
        })
    }

    /// Declare a new value parameter named `name`, an integer of type `ty`
    /// known when compiling (`N` in `[N: usize]`).
    pub fn new_value_param(name: String, ty: IntTy) -> Ty {
        Ty::push_param(ParamDef {
            name,
            bounds: Bounds::default(),
            values: None,
            fits: None,
            signed_min: None,
            value: Some(ty),
        })
    }

    fn push_param(def: ParamDef) -> Ty {
        let mut tables = interner().lock().unwrap_or_else(|e| e.into_inner());
        let id = ParamId(u32::try_from(tables.params.len()).expect("too many type parameters"));
        tables.params.push(Arc::new(def));
        Ty::Param(id)
    }

    /// The integer type of a value parameter (`None` for a type parameter
    /// or any other type).
    pub fn value_param(self) -> Option<IntTy> {
        self.as_param().and_then(|d| d.value)
    }

    /// The generic argument `v`, for a value parameter.
    pub fn value(v: i128) -> Ty {
        Ty::Value(intern(Compound::Value { value: v }))
    }

    /// The number a [`Ty::Value`] stands for.
    pub fn as_value(self) -> Option<i128> {
        match self {
            Ty::Value(id) => match compound(id) {
                Compound::Value { value } => Some(value),
                _ => unreachable!("a value id names another type"),
            },
            _ => None,
        }
    }

    /// The built-in enum `Ordering`, what `a.cmp(b)` returns:
    /// `less = -1`, `equal = 0`, `greater = 1` (an `i8` C-style enum).
    pub fn ordering() -> Ty {
        static ORDERING: OnceLock<Ty> = OnceLock::new();
        *ORDERING.get_or_init(|| {
            let ty = Ty::new_enum("Ordering".to_owned(), usize::MAX, true, Vec::new());
            let variant = |name: &str, value| Variant {
                name: name.to_owned(),
                fields: Vec::new(),
                value,
            };
            ty.set_variants(
                IntTy::new(true, 8),
                true,
                vec![
                    variant("less", -1),
                    variant("equal", 0),
                    variant("greater", 1),
                ],
            );
            ty
        })
    }

    /// Whether a value of this type can be copied implicitly (the built-in
    /// trait `Copy`). Every type the compiler has is plain data, so every
    /// type is, except a type parameter without the bound `Copy` and the
    /// arrays, optionals, results, structs and enums that hold one. A view
    /// is `Copy`: copying it doesn't copy what it views.
    pub fn is_copy(self) -> bool {
        match self {
            Ty::Param(_) => {
                let def = self.as_param().expect("a parameter");
                def.value.is_some() || def.bounds.has(Trait::Copy)
            }
            Ty::Array(_) => self.as_array().expect("an array").0.is_copy(),
            Ty::Optional(_) => self.as_optional().expect("an optional").is_copy(),
            Ty::Result(_) => {
                let (ok, err) = self.as_result().expect("a result");
                ok.is_copy() && err.is_copy()
            }
            Ty::Struct(_) | Ty::Enum(_) => self.members().iter().all(|t| t.is_copy()),
            _ => true,
        }
    }

    /// The types a struct holds (its fields) or an enum (every payload
    /// field), as instantiated.
    pub fn members(self) -> Vec<Ty> {
        if let Some(def) = self.as_struct() {
            return def.fields.iter().map(|f| f.ty).collect();
        }
        match self.as_enum() {
            Some(def) => def
                .variants
                .iter()
                .flat_map(|v| v.fields.iter().map(|f| f.ty))
                .collect(),
            None => Vec::new(),
        }
    }

    /// Whether this type implements the built-in trait `t`
    /// (docs/generics.md, Built-in traits).
    pub fn satisfies(self, t: Trait) -> bool {
        if let Some(def) = self.as_param() {
            return def.bounds.has(t);
        }
        match t {
            Trait::Copy => self.is_copy(),
            Trait::Eq => match self {
                Ty::Int(_) | Ty::Bool | Ty::Ptr(_) => true,
                Ty::Array(_) => self.as_array().expect("an array").0.satisfies(t),
                Ty::Optional(_) => self.as_optional().expect("an optional").satisfies(t),
                Ty::Struct(_) | Ty::Enum(_) => self.members().iter().all(|m| m.satisfies(t)),
                _ => false,
            },
            Trait::Ordered => matches!(self, Ty::Int(_) | Ty::Bool),
            Trait::Integer => matches!(self, Ty::Int(_)),
            Trait::Unsigned => matches!(self, Ty::Int(it) if !it.signed),
            Trait::Signed => matches!(self, Ty::Int(it) if it.signed),
        }
    }

    /// The type parameters this type mentions, added to `out` (once each).
    pub fn params(self, out: &mut Vec<Ty>) {
        match self {
            Ty::Param(_) => {
                if !out.contains(&self) {
                    out.push(self);
                }
            }
            Ty::Array(_) => {
                let (elem, len) = self.as_array().expect("an array");
                elem.params(out);
                if let Len::Param(p) = len {
                    p.params(out);
                }
            }
            Ty::Slice(_) => self.as_slice().expect("a slice").params(out),
            Ty::Optional(_) => self.as_optional().expect("an optional").params(out),
            Ty::Result(_) => {
                let (ok, err) = self.as_result().expect("a result");
                ok.params(out);
                err.params(out);
            }
            Ty::Struct(_) | Ty::Enum(_) => {
                for a in self.type_args().iter() {
                    a.params(out);
                }
            }
            _ => {}
        }
    }

    /// Whether this type mentions a type parameter.
    pub fn is_generic(self) -> bool {
        let mut found = Vec::new();
        self.params(&mut found);
        !found.is_empty()
    }

    /// This type with each type parameter `p` replaced by `with(p)` (or
    /// kept, where it gives `None`).
    pub fn subst(self, with: &impl Fn(Ty) -> Option<Ty>) -> Ty {
        match self {
            Ty::Param(_) => with(self).unwrap_or(self),
            Ty::Array(_) => {
                let (elem, len) = self.as_array().expect("an array");
                let len = match len {
                    Len::Known(_) => len,
                    Len::Param(p) => match p.subst(with) {
                        v @ Ty::Value(_) => Len::Known(
                            u64::try_from(v.as_value().expect("a value"))
                                .expect("a length is a valid `usize`"),
                        ),
                        q => Len::Param(q),
                    },
                };
                Ty::array_of(elem.subst(with), len)
            }
            Ty::Slice(_) => Ty::slice(self.as_slice().expect("a slice").subst(with)),
            Ty::Optional(_) => Ty::optional(self.as_optional().expect("an optional").subst(with)),
            Ty::Result(_) => {
                let (ok, err) = self.as_result().expect("a result");
                Ty::result(ok.subst(with), err.subst(with))
            }
            Ty::Struct(_) | Ty::Enum(_) => {
                let args = self.type_args();
                if args.is_empty() {
                    return self;
                }
                let args: Vec<Ty> = args.iter().map(|a| a.subst(with)).collect();
                self.instantiate(&args)
            }
            _ => self,
        }
    }

    /// The array type `[len]elem`.
    pub fn array(elem: Ty, len: u64) -> Ty {
        Ty::array_of(elem, Len::Known(len))
    }

    /// The array type `[len]elem`, of a length that may be a value
    /// parameter.
    pub fn array_of(elem: Ty, len: Len) -> Ty {
        let len = match len {
            Len::Known(n) => Ty::value(i128::from(n)),
            Len::Param(p) => p,
        };
        Ty::Array(intern(Compound::Array { elem, len }))
    }

    /// The slice type `[]elem`.
    pub fn slice(elem: Ty) -> Ty {
        Ty::Slice(intern(Compound::Slice { elem }))
    }

    /// The element type and length of an array type.
    pub fn as_array(self) -> Option<(Ty, Len)> {
        match self {
            Ty::Array(id) => match compound(id) {
                Compound::Array { elem, len } => Some((
                    elem,
                    match len.as_value() {
                        Some(n) => Len::Known(n as u64),
                        None => Len::Param(len),
                    },
                )),
                _ => unreachable!("an array id names another type"),
            },
            _ => None,
        }
    }

    /// The element type and length of an array type of a known length
    /// (every array, once instantiated).
    pub fn as_known_array(self) -> Option<(Ty, u64)> {
        let (elem, len) = self.as_array()?;
        Some((
            elem,
            len.known().expect("an instance's array has a known length"),
        ))
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

    /// The result type `throws(err) -> ok`.
    pub fn result(ok: Ty, err: Ty) -> Ty {
        Ty::Result(intern(Compound::Result { ok, err }))
    }

    /// The value and error types of a result type.
    pub fn as_result(self) -> Option<(Ty, Ty)> {
        match self {
            Ty::Result(id) => match compound(id) {
                Compound::Result { ok, err } => Some((ok, err)),
                _ => unreachable!("a result id names another type"),
            },
            _ => None,
        }
    }

    /// Whether values of this type live in memory, as places (arrays,
    /// structs, enums, optionals and results), rather than in registers.
    pub fn in_memory(self) -> bool {
        matches!(
            self,
            Ty::Array(_) | Ty::Struct(_) | Ty::Enum(_) | Ty::Optional(_) | Ty::Result(_)
        )
    }

    /// The declaration of an enum type (not an optional: see [`Ty::sum`]).
    /// For an instance of a generic enum, its payload fields have the
    /// instance's types (`Either[u8, bool]`'s `left` holds a `u8`).
    pub fn as_enum(self) -> Option<Arc<EnumDef>> {
        let Ty::Enum(id) = self else {
            return None;
        };
        let Compound::Enum { def, args } = compound(id) else {
            unreachable!("an enum id names another type")
        };
        if args == ArgsId::EMPTY {
            return Some(enum_def(def));
        }
        if let Some(found) = cached(id) {
            let Def::Enum(d) = found else {
                unreachable!("an enum's cache entry")
            };
            return Some(d);
        }
        let decl = enum_def(def);
        let args = arg_list(args);
        let map = |p: Ty| decl.params.iter().position(|&q| q == p).map(|k| args[k]);
        let variants = decl
            .variants
            .iter()
            .map(|v| Variant {
                fields: subst_fields(&v.fields, &map),
                ..v.clone()
            })
            .collect();
        let out = Arc::new(EnumDef {
            variants,
            args: args.to_vec(),
            ..EnumDef::clone(&decl)
        });
        cache(id, Def::Enum(Arc::clone(&out)));
        Some(out)
    }

    /// The type arguments of an instance of a generic struct or enum
    /// (`[u8, bool]` for `Pair[u8, bool]`); empty for any other type.
    pub fn type_args(self) -> Arc<[Ty]> {
        match self {
            Ty::Struct(id) | Ty::Enum(id) => match compound(id) {
                Compound::Struct { args, .. } | Compound::Enum { args, .. } => arg_list(args),
                _ => unreachable!("a struct or enum id names another type"),
            },
            _ => Arc::from(Vec::new()),
        }
    }

    /// The parameters a generic struct or enum declares (`[A, B]` for
    /// `struct Pair[A, B]`); empty for any other type.
    pub fn decl_params(self) -> Vec<Ty> {
        match self {
            Ty::Struct(id) => match compound(id) {
                Compound::Struct { def, .. } => struct_def(def).params.clone(),
                _ => unreachable!("a struct id names another type"),
            },
            Ty::Enum(id) => match compound(id) {
                Compound::Enum { def, .. } => enum_def(def).params.clone(),
                _ => unreachable!("an enum id names another type"),
            },
            _ => Vec::new(),
        }
    }

    /// The same struct or enum declaration with the type arguments `args`
    /// (as many as it declares parameters).
    pub fn instantiate(self, args: &[Ty]) -> Ty {
        let list = intern_args(args);
        match self {
            Ty::Struct(id) => match compound(id) {
                Compound::Struct { def, .. } => {
                    Ty::Struct(intern(Compound::Struct { def, args: list }))
                }
                _ => unreachable!("a struct id names another type"),
            },
            Ty::Enum(id) => match compound(id) {
                Compound::Enum { def, .. } => Ty::Enum(intern(Compound::Enum { def, args: list })),
                _ => unreachable!("an enum id names another type"),
            },
            _ => unreachable!("only a struct or an enum is instantiated: {self}"),
        }
    }

    /// A generic struct or enum as declared, with its own parameters as
    /// arguments (`Pair[A, B]`); any other type itself. Methods are found
    /// through it.
    pub fn decl(self) -> Ty {
        let params = self.decl_params();
        if params.is_empty() {
            return self;
        }
        self.instantiate(&params)
    }

    /// Whether this is a generic struct or enum as declared (see
    /// [`Ty::decl`]): a name written without its type arguments.
    pub fn is_decl_form(self) -> bool {
        let params = self.decl_params();
        !params.is_empty() && *self.type_args() == *params
    }

    /// Whether two types are instances of the same struct or enum
    /// declaration.
    pub fn same_decl(self, other: Ty) -> bool {
        match (self, other) {
            (Ty::Struct(a), Ty::Struct(b)) | (Ty::Enum(a), Ty::Enum(b)) => {
                match (compound(a), compound(b)) {
                    (Compound::Struct { def: x, .. }, Compound::Struct { def: y, .. })
                    | (Compound::Enum { def: x, .. }, Compound::Enum { def: y, .. }) => x == y,
                    _ => false,
                }
            }
            _ => false,
        }
    }

    /// The variants of an enum, an optional or a result, which share their
    /// layout and their operations. An optional `?T` is `none` (tag 0) or
    /// `some(value: T)` (tag 1). A result is `ok(value: T)` (tag 0; `ok`
    /// without payload when `T` is `()`) or `err(error: E)` (tag 1).
    pub fn sum(self) -> Option<Arc<EnumDef>> {
        if let Some(def) = self.as_enum() {
            return Some(def);
        }
        if let Some((ok, err)) = self.as_result() {
            let field = |name: &str, ty| Field {
                name: name.to_owned(),
                ty,
            };
            let ok_fields = if ok == Ty::Unit {
                Vec::new()
            } else {
                vec![field("value", ok)]
            };
            return Some(Arc::new(EnumDef {
                name: self.to_string(),
                pkg: usize::MAX,
                is_pub: true,
                params: Vec::new(),
                args: Vec::new(),
                tag: IntTy::new(false, 8),
                explicit: false,
                variants: vec![
                    Variant {
                        name: "ok".to_owned(),
                        fields: ok_fields,
                        value: 0,
                    },
                    Variant {
                        name: "err".to_owned(),
                        fields: vec![field("error", err)],
                        value: 1,
                    },
                ],
            }));
        }
        let inner = self.as_optional()?;
        Some(Arc::new(EnumDef {
            name: self.to_string(),
            pkg: usize::MAX,
            is_pub: true,
            params: Vec::new(),
            args: Vec::new(),
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
    /// package `pkg`, with the generic parameters `params` (none for an
    /// enum that isn't generic). Its variants are set once they're
    /// resolved, with [`Ty::set_variants`]. For a generic enum, the type
    /// returned is its declared form ([`Ty::decl`]).
    pub fn new_enum(name: String, pkg: usize, is_pub: bool, params: Vec<Ty>) -> Ty {
        let mut tables = interner().lock().unwrap_or_else(|e| e.into_inner());
        let def = u32::try_from(tables.enums.len()).expect("too many enums");
        tables.enums.push(Arc::new(EnumDef {
            name,
            pkg,
            is_pub,
            args: params.clone(),
            params: params.clone(),
            tag: IntTy::new(false, 8),
            explicit: false,
            variants: Vec::new(),
        }));
        drop(tables);
        let args = intern_args(&params);
        Ty::Enum(intern(Compound::Enum { def, args }))
    }

    /// Set the tag type and variants of an enum type declared with
    /// [`Ty::new_enum`] (or of its declared form). `explicit` marks an enum
    /// whose variants have declared integer values (`enum Color: u8 { red
    /// = 1 ... }`).
    pub fn set_variants(self, tag: IntTy, explicit: bool, variants: Vec<Variant>) {
        let Ty::Enum(id) = self else {
            unreachable!("not an enum: {self}")
        };
        let Compound::Enum { def, .. } = compound(id) else {
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
        tables.instances.clear();
    }

    /// The declaration of a struct type. For an instance of a generic
    /// struct, its fields have the instance's types (`Pair[u8, bool]`'s
    /// `first` is a `u8`).
    pub fn as_struct(self) -> Option<Arc<StructDef>> {
        let Ty::Struct(id) = self else {
            return None;
        };
        let Compound::Struct { def, args } = compound(id) else {
            unreachable!("a struct id names another type")
        };
        if args == ArgsId::EMPTY {
            return Some(struct_def(def));
        }
        if let Some(found) = cached(id) {
            let Def::Struct(d) = found else {
                unreachable!("a struct's cache entry")
            };
            return Some(d);
        }
        let decl = struct_def(def);
        let args = arg_list(args);
        let map = |p: Ty| decl.params.iter().position(|&q| q == p).map(|k| args[k]);
        let out = Arc::new(StructDef {
            fields: subst_fields(&decl.fields, &map),
            args: args.to_vec(),
            ..StructDef::clone(&decl)
        });
        cache(id, Def::Struct(Arc::clone(&out)));
        Some(out)
    }

    /// Declare a new struct type named `name` (as shown in messages), from
    /// package `pkg`, with the generic parameters `params`. Its fields are
    /// set once they're resolved, with [`Ty::set_fields`]. For a generic
    /// struct, the type returned is its declared form ([`Ty::decl`]).
    pub fn new_struct(name: String, pkg: usize, is_pub: bool, params: Vec<Ty>) -> Ty {
        let mut tables = interner().lock().unwrap_or_else(|e| e.into_inner());
        let def = u32::try_from(tables.structs.len()).expect("too many structs");
        tables.structs.push(Arc::new(StructDef {
            name,
            pkg,
            is_pub,
            args: params.clone(),
            params: params.clone(),
            fields: Vec::new(),
        }));
        drop(tables);
        let args = intern_args(&params);
        Ty::Struct(intern(Compound::Struct { def, args }))
    }

    /// Set the fields of a struct type declared with [`Ty::new_struct`] (or
    /// of its declared form).
    pub fn set_fields(self, fields: Vec<Field>) {
        let Ty::Struct(id) = self else {
            unreachable!("not a struct: {self}")
        };
        let Compound::Struct { def, .. } = compound(id) else {
            unreachable!("a struct id names another type")
        };
        let mut tables = interner().lock().unwrap_or_else(|e| e.into_inner());
        let entry = &mut tables.structs[def as usize];
        *entry = Arc::new(StructDef {
            fields,
            ..StructDef::clone(entry)
        });
        tables.instances.clear();
    }
}

/// Fields with each parameter `p` replaced by `with(p)`.
fn subst_fields(fields: &[Field], with: &impl Fn(Ty) -> Option<Ty>) -> Vec<Field> {
    fields
        .iter()
        .map(|f| Field {
            name: f.name.clone(),
            ty: f.ty.subst(with),
        })
        .collect()
}

/// A struct declaration: its name, where it's declared and its fields, in
/// declaration order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructDef {
    /// The name shown in messages: `Point`, or `os.Stat` for a struct of an
    /// imported package. A generic struct's arguments aren't in it.
    pub name: String,
    /// The index of the declaring package (in the checker's package list).
    pub pkg: usize,
    pub is_pub: bool,
    /// The generic parameters it declares (empty if it isn't generic).
    pub params: Vec<Ty>,
    /// The type arguments of this instance (its own `params` for the
    /// declared form; empty if it isn't generic).
    pub args: Vec<Ty>,
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
    /// The generic parameters it declares, as for [`StructDef::params`].
    pub params: Vec<Ty>,
    /// The type arguments of this instance, as for [`StructDef::args`].
    pub args: Vec<Ty>,
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

/// A built-in trait (docs/generics.md, Built-in traits). User traits come
/// with M7c; until then, these are the only bounds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Trait {
    /// `==` and `!=`.
    Eq,
    /// A total order: `a.cmp(b)`, `a.lt(b)` and the like.
    Ordered,
    /// Values are copied implicitly.
    Copy,
    /// The integer types, with their operators. Sealed.
    Integer,
    /// The unsigned integer types. Sealed.
    Unsigned,
    /// The signed integer types. Sealed.
    Signed,
}

impl Trait {
    pub const ALL: [Trait; 6] = [
        Trait::Eq,
        Trait::Ordered,
        Trait::Copy,
        Trait::Integer,
        Trait::Unsigned,
        Trait::Signed,
    ];

    pub fn name(self) -> &'static str {
        match self {
            Trait::Eq => "Eq",
            Trait::Ordered => "Ordered",
            Trait::Copy => "Copy",
            Trait::Integer => "Integer",
            Trait::Unsigned => "Unsigned",
            Trait::Signed => "Signed",
        }
    }

    pub fn from_name(name: &str) -> Option<Trait> {
        Trait::ALL.into_iter().find(|t| t.name() == name)
    }

    fn bit(self) -> u8 {
        1 << (self as u8)
    }

    /// The trait and its supertraits: `Ordered: Eq`, `Integer: Ordered +
    /// Copy`, `Unsigned: Integer`, `Signed: Integer`.
    fn closure(self) -> u8 {
        let integer =
            Trait::Integer.bit() | Trait::Ordered.bit() | Trait::Eq.bit() | Trait::Copy.bit();
        match self {
            Trait::Eq | Trait::Copy => self.bit(),
            Trait::Ordered => self.bit() | Trait::Eq.bit(),
            Trait::Integer => integer,
            Trait::Unsigned | Trait::Signed => self.bit() | integer,
        }
    }
}

impl fmt::Display for Trait {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// The bounds of a type parameter: a set of built-in traits, closed under
/// supertraits (`T: Integer` is also `Ordered`, `Eq` and `Copy`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Bounds(u8);

impl Bounds {
    /// The traits, with their supertraits.
    pub fn new(traits: &[Trait]) -> Bounds {
        Bounds(traits.iter().fold(0, |acc, t| acc | t.closure()))
    }

    pub fn has(self, t: Trait) -> bool {
        self.0 & t.bit() != 0
    }

    /// Whether the integer type `t` satisfies these bounds (an integer
    /// type satisfies every bound but the other sign).
    fn admits_int(self, t: IntTy) -> bool {
        !(self.has(Trait::Unsigned) && t.signed || self.has(Trait::Signed) && !t.signed)
    }

    /// The most precise numeric bound: `Unsigned`, `Signed` or `Integer`.
    pub fn numeric(self) -> Option<Trait> {
        [Trait::Unsigned, Trait::Signed, Trait::Integer]
            .into_iter()
            .find(|&t| self.has(t))
    }
}

/// The integer types of a target whose address width is `ptr_bits`.
pub fn int_types(ptr_bits: u32) -> Vec<IntTy> {
    let mut out = Vec::new();
    for signed in [false, true] {
        for bits in [8, 16, 32, 64] {
            out.push(IntTy::new(signed, bits));
        }
        out.push(IntTy {
            signed,
            bits: ptr_bits,
            size: true,
        });
    }
    out
}

/// A type parameter's declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParamDef {
    /// Its name, as written: `T`.
    pub name: String,
    pub bounds: Bounds,
    /// With a numeric bound: every value of every type the bound admits,
    /// the hull of their ranges (for `Integer`, the smallest `i64` to the
    /// largest `u64`). A value of the parameter's type lies in it.
    pub values: Option<Range>,
    /// With a numeric bound: the values every type the bound admits holds,
    /// the intersection of their ranges (`0..=127` for `Integer`). A value
    /// in it fits in the parameter's type, whatever the type is.
    pub fits: Option<Range>,
    /// The largest of the smallest values of the signed types the bound
    /// admits (-128 for `i8`), if it admits any: a value above it is no
    /// signed type's smallest.
    pub signed_min: Option<i128>,
    /// For a value parameter (`N: usize`), its integer type; `None` for a
    /// type parameter.
    pub value: Option<IntTy>,
}

/// The index of a type parameter in the global type interner.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ParamId(u32);

/// The index of a compound type in the global type interner.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CompoundId(u32);

/// A type made of other types. Compound types are interned (hash-consed) so
/// that [`Ty`] stays small and `Copy`: equal compound types always get the
/// same [`CompoundId`], so comparing ids compares the types.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Compound {
    /// `[len]elem`: `len` is a [`Ty::Value`], or a value parameter.
    Array {
        elem: Ty,
        len: Ty,
    },
    Slice {
        elem: Ty,
    },
    /// A struct, by the index of its declaration and its type arguments:
    /// two declarations are two types, even with the same fields, and so
    /// are two instances of a generic struct with different arguments.
    Struct {
        def: u32,
        args: ArgsId,
    },
    /// An enum, by the index of its declaration and its type arguments.
    Enum {
        def: u32,
        args: ArgsId,
    },
    /// An integer generic argument, for a value parameter.
    Value {
        value: i128,
    },
    /// `?inner`.
    Optional {
        inner: Ty,
    },
    /// `throws(err) -> ok`.
    Result {
        ok: Ty,
        err: Ty,
    },
}

/// A list of type arguments in the interner.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ArgsId(u32);

impl ArgsId {
    /// No arguments: a struct or an enum that isn't generic.
    const EMPTY: ArgsId = ArgsId(0);
}

/// An instantiated declaration, cached by [`Ty::as_struct`] and
/// [`Ty::as_enum`].
#[derive(Clone)]
enum Def {
    Struct(Arc<StructDef>),
    Enum(Arc<EnumDef>),
}

/// The interner's tables. Entries are only ever appended, so an id stays
/// valid for the life of the process.
struct Interner {
    entries: Vec<Compound>,
    ids: HashMap<Compound, CompoundId>,
    structs: Vec<Arc<StructDef>>,
    enums: Vec<Arc<EnumDef>>,
    params: Vec<Arc<ParamDef>>,
    /// The lists of type arguments, `ArgsId::EMPTY` first.
    arg_lists: Vec<Arc<[Ty]>>,
    arg_ids: HashMap<Arc<[Ty]>, ArgsId>,
    /// The declarations of the instances of generic types, with their
    /// fields' types substituted; cleared when a declaration changes.
    instances: HashMap<CompoundId, Def>,
}

impl Default for Interner {
    fn default() -> Interner {
        let empty: Arc<[Ty]> = Arc::from(Vec::new());
        Interner {
            entries: Vec::new(),
            ids: HashMap::new(),
            structs: Vec::new(),
            enums: Vec::new(),
            params: Vec::new(),
            arg_ids: HashMap::from([(Arc::clone(&empty), ArgsId::EMPTY)]),
            arg_lists: vec![empty],
            instances: HashMap::new(),
        }
    }
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

/// The id of a list of type arguments, adding it if it's new.
fn intern_args(args: &[Ty]) -> ArgsId {
    let mut tables = interner().lock().unwrap_or_else(|e| e.into_inner());
    if let Some(&id) = tables.arg_ids.get(args) {
        return id;
    }
    let id = ArgsId(u32::try_from(tables.arg_lists.len()).expect("too many types"));
    let list: Arc<[Ty]> = Arc::from(args);
    tables.arg_lists.push(Arc::clone(&list));
    tables.arg_ids.insert(list, id);
    id
}

fn arg_list(id: ArgsId) -> Arc<[Ty]> {
    let tables = interner().lock().unwrap_or_else(|e| e.into_inner());
    Arc::clone(&tables.arg_lists[id.0 as usize])
}

fn cached(id: CompoundId) -> Option<Def> {
    let tables = interner().lock().unwrap_or_else(|e| e.into_inner());
    tables.instances.get(&id).cloned()
}

fn cache(id: CompoundId, def: Def) {
    let mut tables = interner().lock().unwrap_or_else(|e| e.into_inner());
    tables.instances.insert(id, def);
}

fn struct_def(def: u32) -> Arc<StructDef> {
    let tables = interner().lock().unwrap_or_else(|e| e.into_inner());
    Arc::clone(&tables.structs[def as usize])
}

fn param_def(id: ParamId) -> Arc<ParamDef> {
    let tables = interner().lock().unwrap_or_else(|e| e.into_inner());
    Arc::clone(&tables.params[id.0 as usize])
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
            Ty::Never => f.write_str("never"),
            Ty::Str => f.write_str("str"),
            Ty::Ptr(t) => write!(f, "*{t}"),
            Ty::Param(id) => f.write_str(&param_def(*id).name),
            Ty::Array(id)
            | Ty::Slice(id)
            | Ty::Struct(id)
            | Ty::Enum(id)
            | Ty::Optional(id)
            | Ty::Result(id)
            | Ty::Value(id) => match compound(*id) {
                Compound::Array { elem, len } => write!(f, "[{len}]{elem}"),
                Compound::Slice { elem } => write!(f, "[]{elem}"),
                Compound::Struct { def, args } => {
                    f.write_str(&struct_def(def).name)?;
                    write_args(f, &arg_list(args))
                }
                Compound::Enum { def, args } => {
                    f.write_str(&enum_def(def).name)?;
                    write_args(f, &arg_list(args))
                }
                Compound::Optional { inner } => write!(f, "?{inner}"),
                Compound::Result { ok: Ty::Unit, err } => write!(f, "throws({err})"),
                Compound::Result { ok, err } => write!(f, "throws({err}) -> {ok}"),
                Compound::Value { value } => write!(f, "{value}"),
            },
        }
    }
}

/// `[a, b]` after a generic type's name (nothing if there are no
/// arguments).
fn write_args(f: &mut fmt::Formatter<'_>, args: &[Ty]) -> fmt::Result {
    if args.is_empty() {
        return Ok(());
    }
    f.write_str("[")?;
    for (k, a) in args.iter().enumerate() {
        if k > 0 {
            f.write_str(", ")?;
        }
        write!(f, "{a}")?;
    }
    f.write_str("]")
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
        assert_eq!(nested.as_array(), Some((a, Len::Known(3))));
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
        let a = Ty::new_struct("P".into(), 0, false, Vec::new());
        let b = Ty::new_struct("P".into(), 1, true, Vec::new());
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
    fn type_parameters() {
        let u8_ = Ty::Int(IntTy::new(false, 8));
        let range = |lo: i128, hi: i128| Some(Range { lo, hi });

        let t = Ty::new_param("T".into(), Bounds::new(&[Trait::Integer]), 64);
        let def = t.as_param().expect("a parameter");
        assert_eq!(
            def.values,
            range(i128::from(i64::MIN), i128::from(u64::MAX))
        );
        assert_eq!(def.fits, range(0, 127));
        assert_eq!(def.signed_min, Some(-128));
        for tr in [Trait::Eq, Trait::Ordered, Trait::Copy, Trait::Integer] {
            assert!(t.satisfies(tr), "{tr}");
        }
        assert!(!t.satisfies(Trait::Unsigned) && t.to_string() == "T");

        let u = Ty::new_param("U".into(), Bounds::new(&[Trait::Unsigned]), 64);
        let def = u.as_param().expect("a parameter");
        assert_eq!(def.values, range(0, i128::from(u64::MAX)));
        assert_eq!((def.fits, def.signed_min), (range(0, 255), None));
        let s = Ty::new_param("S".into(), Bounds::new(&[Trait::Signed]), 64);
        assert_eq!(s.as_param().expect("a parameter").fits, range(-128, 127));

        // Without `Copy`, a parameter isn't copied, nor what holds it; a
        // view of it is.
        let o = Ty::new_param("O".into(), Bounds::new(&[Trait::Ordered]), 64);
        assert!(o.as_param().expect("a parameter").values.is_none());
        assert!(!o.is_copy() && !Ty::optional(o).is_copy() && Ty::slice(o).is_copy());
        assert!(o.satisfies(Trait::Eq) && !o.satisfies(Trait::Copy));

        let mut found = Vec::new();
        Ty::array(Ty::optional(o), 2).params(&mut found);
        assert_eq!(found, [o]);
        let with = |p: Ty| (p == o).then_some(u8_);
        assert_eq!(
            Ty::array(Ty::optional(o), 2).subst(&with),
            Ty::array(Ty::optional(u8_), 2)
        );
        assert!(!Ty::array(u8_, 2).is_generic() && Ty::slice(o).is_generic());

        // The concrete types' built-in traits.
        assert!(Ty::Bool.satisfies(Trait::Ordered) && !Ty::Bool.satisfies(Trait::Integer));
        assert!(Ty::Int(IntTy::new(true, 8)).satisfies(Trait::Signed));
        assert!(!Ty::Str.satisfies(Trait::Eq) && Ty::array(u8_, 3).satisfies(Trait::Eq));

        let ordering = Ty::ordering();
        assert_eq!(
            (ordering, ordering.to_string()),
            (Ty::ordering(), "Ordering".into())
        );
        let values: Vec<i128> = ordering
            .as_enum()
            .expect("an enum")
            .variants
            .iter()
            .map(|v| v.value)
            .collect();
        assert_eq!(values, [-1, 0, 1]);
    }

    #[test]
    fn enums_and_optionals() {
        let u8_ = Ty::Int(IntTy::new(false, 8));
        let e = Ty::new_enum("E".into(), 0, true, Vec::new());
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
