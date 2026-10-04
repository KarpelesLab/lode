//! Build targets, and `target`, the compile-time value that describes the
//! one a program is checked for (docs/comptime.md, Conditional compilation).
//!
//! The compiler knows a small set of targets. Each can be checked
//! (`lode check --targets=...`), since checking needs only the target's
//! properties; only those LatticeFoundry can link for in Lode today can be
//! built ([`Target::can_build`]).

use std::sync::OnceLock;

use crate::types::{Field, IntTy, Ty, Variant};

/// The operating systems a target can have, in the order of the variants of
/// the built-in enum `target.Os`.
pub const OS_NAMES: &[&str] = &["linux", "none"];

/// The processor architectures, in the order of `target.Arch`'s variants.
pub const ARCH_NAMES: &[&str] = &["x86_64", "aarch64", "wasm32", "arm", "avr"];

/// The byte orders, in the order of `target.Endian`'s variants.
pub const ENDIAN_NAMES: &[&str] = &["little", "big"];

/// A target the compiler knows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Target {
    /// The name used on the command line: `x86_64-linux`.
    pub name: &'static str,
    /// The index of its operating system in [`OS_NAMES`].
    pub os: u32,
    /// The index of its architecture in [`ARCH_NAMES`].
    pub arch: u32,
    /// The width of an address, and of `usize` and `isize`.
    pub pointer_bits: u32,
    /// The index of its byte order in [`ENDIAN_NAMES`].
    pub endian: u32,
    /// Whether `lode build` can make executables for it.
    pub can_build: bool,
}

/// Every target the compiler knows, the default first.
pub const TARGETS: &[Target] = &[
    Target {
        name: "x86_64-linux",
        os: 0,
        arch: 0,
        pointer_bits: 64,
        endian: 0,
        can_build: true,
    },
    Target {
        name: "aarch64-linux",
        os: 0,
        arch: 1,
        pointer_bits: 64,
        endian: 0,
        can_build: false,
    },
    Target {
        name: "wasm32",
        os: 1,
        arch: 2,
        pointer_bits: 32,
        endian: 0,
        can_build: false,
    },
    Target {
        name: "thumbv7m",
        os: 1,
        arch: 3,
        pointer_bits: 32,
        endian: 0,
        can_build: false,
    },
    Target {
        name: "avr",
        os: 1,
        arch: 4,
        pointer_bits: 16,
        endian: 0,
        can_build: false,
    },
];

impl Target {
    /// The target `lode` builds for by default: x86-64 Linux.
    pub fn host() -> &'static Target {
        &TARGETS[0]
    }

    /// The target called `name`.
    pub fn by_name(name: &str) -> Option<&'static Target> {
        TARGETS.iter().find(|t| t.name == name)
    }

    /// The fields of the `target` value, in the order of `target.Target`'s
    /// fields: each an enum variant index or an integer.
    pub fn field_values(&self) -> [i128; 4] {
        [
            i128::from(self.os),
            i128::from(self.arch),
            i128::from(self.pointer_bits),
            i128::from(self.endian),
        ]
    }
}

/// The built-in types of `target`'s value.
#[derive(Clone, Copy, Debug)]
pub struct TargetTypes {
    /// `target.Target`, a struct of `os`, `arch`, `pointer_bits` and
    /// `endian`.
    pub target: Ty,
    pub os: Ty,
    pub arch: Ty,
    pub endian: Ty,
}

/// The field names of `target.Target`, in order.
pub const FIELD_NAMES: &[&str] = &["os", "arch", "pointer_bits", "endian"];

/// The types of `target`, made once.
pub fn types() -> TargetTypes {
    static TYPES: OnceLock<TargetTypes> = OnceLock::new();
    *TYPES.get_or_init(|| {
        let make_enum = |name: &str, names: &[&str]| {
            let ty = Ty::new_enum(format!("target.{name}"), usize::MAX, true, Vec::new());
            let variants = names
                .iter()
                .enumerate()
                .map(|(k, n)| Variant {
                    name: (*n).to_owned(),
                    fields: Vec::new(),
                    value: k as i128,
                })
                .collect();
            ty.set_variants(IntTy::new(false, 8), false, variants);
            ty
        };
        let os = make_enum("Os", OS_NAMES);
        let arch = make_enum("Arch", ARCH_NAMES);
        let endian = make_enum("Endian", ENDIAN_NAMES);
        let target = Ty::new_struct("target.Target".to_owned(), usize::MAX, true, Vec::new());
        let field = |name: &str, ty| Field {
            name: name.to_owned(),
            ty,
        };
        target.set_fields(vec![
            field(FIELD_NAMES[0], os),
            field(FIELD_NAMES[1], arch),
            field(FIELD_NAMES[2], Ty::Int(IntTy::new(false, 32))),
            field(FIELD_NAMES[3], endian),
        ]);
        TargetTypes {
            target,
            os,
            arch,
            endian,
        }
    })
}

/// The comma-separated names of every target, for messages.
pub fn names() -> String {
    TARGETS
        .iter()
        .map(|t| t.name)
        .collect::<Vec<_>>()
        .join(", ")
}
