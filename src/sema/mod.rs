//! Semantic checking: names, types, `unsafe`, and proof obligations.
//!
//! The checker walks every package, resolves names across packages, checks
//! types, and discharges the proof obligations of docs/safety.md using the
//! flow-sensitive facts in [`facts`]. Its output is the typed tree in [`tree`].

mod expr;
pub mod facts;
pub mod tree;

use std::collections::{HashMap, HashSet};

use crate::ast::{self, Convention, ExprKind, Stmt, TypeExpr};
use crate::diag::Diagnostic;
use crate::load::Package;
use crate::source::{FileId, Span};
use crate::types::{Field, IntTy, Primitive, Range, Ty, Variant, primitive};

use facts::{Env, Linear, Term};
pub use tree::*;

/// Check every loaded package (dependencies first, the root package last).
/// `ptr_bits` is the target's address width.
pub fn check(packages: &[Package], ptr_bits: u32) -> (Program, Vec<Diagnostic>) {
    let mut ck = Checker {
        diags: Vec::new(),
        pkgs: Vec::new(),
        sigs: Vec::new(),
        consts: Vec::new(),
        imports: HashMap::new(),
        strings: Vec::new(),
        string_ids: HashMap::new(),
        ptr_bits,
    };
    ck.collect(packages);

    // Check every constant, used or not, so its errors are reported.
    for id in 0..ck.consts.len() {
        ck.const_value(id);
    }

    let mut funcs = Vec::new();
    for (pkg, package) in packages.iter().enumerate() {
        for file in &package.files {
            for item in &file.items {
                if let ast::Item::Fn(f) = item {
                    let id = funcs.len();
                    funcs.push(ck.function(f, id, pkg, file.id));
                }
            }
        }
    }

    let root = packages.len().saturating_sub(1);
    let main = match ck.pkgs.get(root).and_then(|p| p.items.get("main")) {
        Some(Item::Func(id)) => Some(*id),
        _ => None,
    };
    if let Some(id) = main {
        let sig = &ck.sigs[id];
        let (no_params, ret, span) = (sig.params.is_empty(), sig.ret, sig.span);
        if !no_params {
            ck.error(span, "`main` takes no parameters");
        }
        if !matches!(ret, Ty::Unit | Ty::Int(_)) {
            ck.error(span, "`main` must return nothing or an integer exit status");
        }
    }

    let program = Program {
        funcs,
        strings: ck.strings,
        main,
        warnings: Vec::new(),
    };
    (program, ck.diags)
}

#[derive(Clone, Copy, Debug)]
enum Item {
    Func(FuncId),
    Const(usize),
    /// A struct or an enum type.
    Type(Ty),
}

struct PkgInfo {
    path: String,
    items: HashMap<String, Item>,
}

struct Sig {
    is_pub: bool,
    is_unsafe: bool,
    params: Vec<Ty>,
    ret: Ty,
    /// The function name's span.
    span: Span,
}

/// The value of a checked constant.
#[derive(Clone, Copy, Debug)]
enum ConstVal {
    /// A typed integer constant.
    Typed(Ty, i128),
    /// An untyped integer constant: like a literal, it takes its type from
    /// the context where it's used.
    Untyped(i128),
}

#[derive(Clone, Copy, Debug)]
enum ConstState {
    Unchecked,
    Checking,
    Done(ConstVal),
    Failed,
}

struct ConstInfo<'a> {
    decl: &'a ast::ConstDecl,
    pkg: usize,
    file: FileId,
    state: ConstState,
}

struct Checker<'a> {
    diags: Vec<Diagnostic>,
    pkgs: Vec<PkgInfo>,
    sigs: Vec<Sig>,
    consts: Vec<ConstInfo<'a>>,
    /// For each file: import name to package index.
    imports: HashMap<FileId, HashMap<String, usize>>,
    strings: Vec<Vec<u8>>,
    string_ids: HashMap<Vec<u8>, usize>,
    ptr_bits: u32,
}

/// Per-function (or per-constant) checking state.
struct FnCx {
    pkg: usize,
    file: FileId,
    locals: Vec<Local>,
    scopes: Vec<HashMap<String, LocalId>>,
    ret: Ty,
    loop_depth: u32,
    /// Nesting of `unsafe` blocks; an `unsafe fn` body starts at 1.
    unsafe_depth: u32,
    /// The facts known at the current point.
    env: Env,
}

impl FnCx {
    fn new(pkg: usize, file: FileId, ret: Ty, is_unsafe: bool) -> FnCx {
        FnCx {
            pkg,
            file,
            locals: Vec::new(),
            scopes: vec![HashMap::new()],
            ret,
            loop_depth: 0,
            unsafe_depth: u32::from(is_unsafe),
            env: Env::default(),
        }
    }

    fn lookup(&self, name: &str) -> Option<LocalId> {
        self.scopes.iter().rev().find_map(|s| s.get(name).copied())
    }
}

/// The hidden local holding the sequence of a `for x in xs` loop. Hidden names
/// start with `$`, so they can't clash with (or be used by) the program.
const SEQ: &str = "$seq";

/// The hidden index of a `for x in xs` loop.
const INDEX: &str = "$i";

/// The hidden local holding the value a `match`, an `if let` or a
/// `let ... else` looks into, unless it's already a local.
const MATCHED: &str = "$match";

/// Names assigned anywhere in `stmts` (for forgetting facts at loop heads).
fn assigned_names(stmts: &[Stmt], out: &mut HashSet<String>) {
    for s in stmts {
        match s {
            Stmt::Assign { target, .. } => {
                // `a[i] = v` and `p.x = v` assign (part of) `a` and `p`.
                let root = place_root(target);
                if let ExprKind::Name(n) = &root.kind {
                    out.insert(n.clone());
                }
            }
            Stmt::Let {
                otherwise: Some(b), ..
            } => assigned_names(&b.stmts, out),
            Stmt::Match { arms, .. } => {
                for arm in arms {
                    assigned_names(&arm.body.stmts, out);
                }
            }
            Stmt::If(i) => {
                let mut cur = Some(i);
                while let Some(i) = cur {
                    assigned_names(&i.then.stmts, out);
                    cur = match &i.otherwise {
                        Some(ast::Else::If(next)) => Some(next),
                        Some(ast::Else::Block(b)) => {
                            assigned_names(&b.stmts, out);
                            None
                        }
                        None => None,
                    };
                }
            }
            Stmt::While { body, .. }
            | Stmt::Loop { body, .. }
            | Stmt::For { body, .. }
            | Stmt::Unsafe(body) => {
                assigned_names(&body.stmts, out);
            }
            _ => {}
        }
    }
}

/// The variable a place like `a[i].x` is part of: the expression under its
/// indexes and fields.
fn place_root(mut e: &ast::Expr) -> &ast::Expr {
    while let ExprKind::Index(base, _) | ExprKind::Field(base, _) = &e.kind {
        e = base;
    }
    e
}

/// The struct or enum type a value of type `ty` holds directly (not behind
/// a view): itself if it's a struct or an enum, or the one in its element
/// type or optional's value.
fn held_nominal(ty: Ty) -> Option<Ty> {
    match ty {
        Ty::Struct(_) | Ty::Enum(_) => Some(ty),
        Ty::Array(_) => held_nominal(ty.as_array()?.0),
        Ty::Optional(_) => held_nominal(ty.as_optional()?),
        _ => None,
    }
}

/// The values a struct or an enum holds: a struct's fields, or the payload
/// fields of every variant of an enum, with their names for messages
/// (`Point.x`, `Shape.circle.r`).
fn members(ty: Ty) -> Vec<(String, Ty)> {
    if let Some(def) = ty.as_struct() {
        return def
            .fields
            .iter()
            .map(|f| (format!("{ty}.{}", f.name), f.ty))
            .collect();
    }
    let def = ty.as_enum().expect("a struct or an enum");
    def.variants
        .iter()
        .flat_map(|v| {
            v.fields
                .iter()
                .map(move |f| (format!("{ty}.{}.{}", v.name, f.name), f.ty))
        })
        .collect()
}

/// Make member `k` (numbered as in [`members`]) of a struct or an enum `()`,
/// to break a cycle that was reported.
fn clear_member(ty: Ty, k: usize) {
    if let Some(def) = ty.as_struct() {
        let mut fields = def.fields.clone();
        fields[k].ty = Ty::Unit;
        ty.set_fields(fields);
        return;
    }
    let def = ty.as_enum().expect("a struct or an enum");
    let mut variants = def.variants.clone();
    let mut k = k;
    for v in &mut variants {
        if k < v.fields.len() {
            v.fields[k].ty = Ty::Unit;
            break;
        }
        k -= v.fields.len();
    }
    ty.set_variants(def.tag, def.explicit, variants);
}

/// What a value of type `ty` can be stored in: a struct field, a payload
/// field, an array element or an optional. `Err` says why not: `Some` for a
/// view, which can never be stored, `None` for a type the compiler can't
/// store yet.
fn storable(ty: Ty) -> Result<(), Option<()>> {
    match ty {
        Ty::Int(_) | Ty::Bool | Ty::Array(_) | Ty::Struct(_) | Ty::Enum(_) | Ty::Optional(_) => {
            Ok(())
        }
        Ty::Str | Ty::Slice(_) => Err(Some(())),
        Ty::Ptr(_) | Ty::Unit => Err(None),
    }
}

/// The local a `match` (or an `if let`, or a `let ... else`) looks into:
/// `value` itself if it's a local, or else a hidden local it's stored in
/// first, by a statement added to `before`.
fn matched_local(cx: &mut FnCx, value: expr::Checked, before: &mut Vec<TStmt>) -> TExpr {
    if let TExprKind::Local(_) = value.expr.kind {
        return value.expr;
    }
    let ty = value.ty();
    let id = cx.locals.len();
    cx.locals.push(Local {
        name: MATCHED.to_owned(),
        ty,
        mutable: false,
    });
    cx.scopes
        .last_mut()
        .expect("scope")
        .insert(MATCHED.to_owned(), id);
    cx.env.assign(id, None);
    before.push(TStmt::Init(id, value.expr));
    TExpr {
        kind: TExprKind::Local(id),
        ty,
    }
}

/// Statements, wrapped in a block if there's more than one.
fn one_stmt(mut stmts: Vec<TStmt>) -> TStmt {
    if stmts.len() == 1 {
        stmts.pop().expect("one statement")
    } else {
        TStmt::Block(stmts)
    }
}

/// `matched`'s payload field `field` of variant `variant`.
fn payload(matched: &TExpr, variant: u32, field: u32, ty: Ty) -> TExpr {
    TExpr {
        kind: TExprKind::Payload(Box::new(matched.clone()), variant, field),
        ty,
    }
}

/// Stands in for a condition that failed to check, so the statement around it
/// is kept for control-flow analysis. Only used when the program has errors.
fn placeholder_bool() -> TExpr {
    TExpr {
        kind: TExprKind::Bool(false),
        ty: Ty::Bool,
    }
}

impl<'a> Checker<'a> {
    fn error(&mut self, span: Span, msg: impl Into<String>) {
        self.diags.push(Diagnostic::error(span, msg));
    }

    /// The name shown in messages for a type declared in package `pkg`:
    /// `Point`, or `os.Stat` for a type of an imported package.
    fn shown_name(packages: &[Package], pkg: usize, name: &str) -> String {
        if pkg == packages.len().saturating_sub(1) {
            name.to_owned()
        } else {
            let last = packages[pkg].path.rsplit('/').next().unwrap_or_default();
            format!("{last}.{name}")
        }
    }

    /// Build the package and item tables, every file's imports, and every
    /// function's signature.
    fn collect(&mut self, packages: &'a [Package]) {
        let mut fns = Vec::new();
        let mut structs = Vec::new();
        let mut enums = Vec::new();
        for (pkg, package) in packages.iter().enumerate() {
            self.pkgs.push(PkgInfo {
                path: package.path.clone(),
                items: HashMap::new(),
            });
            for file in &package.files {
                let mut names = HashMap::new();
                for import in &file.imports {
                    let name = import.alias.as_ref().map_or_else(
                        || {
                            import
                                .path
                                .rsplit('/')
                                .next()
                                .unwrap_or_default()
                                .to_owned()
                        },
                        |a| a.name.clone(),
                    );
                    if let Some(target) = packages.iter().position(|p| p.path == import.path) {
                        names.insert(name, target);
                    }
                }
                self.imports.insert(file.id, names);

                for item in &file.items {
                    let (name, entry) = match item {
                        ast::Item::Fn(f) => {
                            fns.push((f, pkg, file.id));
                            (&f.name, Item::Func(fns.len() - 1))
                        }
                        ast::Item::Const(c) => {
                            self.consts.push(ConstInfo {
                                decl: c,
                                pkg,
                                file: file.id,
                                state: ConstState::Unchecked,
                            });
                            (&c.name, Item::Const(self.consts.len() - 1))
                        }
                        ast::Item::Struct(s) => {
                            // Messages name another package's struct the
                            // way code does: `os.Stat`.
                            let shown = Self::shown_name(packages, pkg, &s.name.name);
                            let ty = Ty::new_struct(shown, pkg, s.is_pub);
                            self.check_type_name(&s.name);
                            structs.push((s, pkg, file.id, ty));
                            (&s.name, Item::Type(ty))
                        }
                        ast::Item::Enum(e) => {
                            let shown = Self::shown_name(packages, pkg, &e.name.name);
                            let ty = Ty::new_enum(shown, pkg, e.is_pub);
                            self.check_type_name(&e.name);
                            enums.push((e, pkg, file.id, ty));
                            (&e.name, Item::Type(ty))
                        }
                    };
                    if self.pkgs[pkg].items.contains_key(&name.name) {
                        self.error(
                            name.span,
                            format!("`{}` is defined more than once", name.name),
                        );
                    }
                    self.pkgs[pkg].items.insert(name.name.clone(), entry);
                }
            }
        }
        // Field types and signatures come once every item is known: an array
        // length in a type can name a constant declared further down, and a
        // field's type a struct declared further down.
        for &(s, pkg, file, ty) in &structs {
            let fields = self.struct_fields(s, pkg, file);
            ty.set_fields(fields);
        }
        for &(e, pkg, file, ty) in &enums {
            let (tag, explicit, variants) = self.enum_variants(e, pkg, file);
            ty.set_variants(tag, explicit, variants);
        }
        for &(s, _, _, ty) in &structs {
            self.check_recursion(&s.name, "struct", ty);
        }
        for &(e, _, _, ty) in &enums {
            self.check_recursion(&e.name, "enum", ty);
        }
        for (f, pkg, file) in fns {
            let mut cx = FnCx::new(pkg, file, Ty::Unit, false);
            let sig = self.signature(&mut cx, f);
            self.sigs.push(sig);
        }
    }

    /// The fields of a struct declaration. A field whose type is in error
    /// gets the type `()`, so later checks see no more problems with it.
    fn struct_fields(&mut self, s: &ast::StructDecl, pkg: usize, file: FileId) -> Vec<Field> {
        let mut cx = FnCx::new(pkg, file, Ty::Unit, false);
        let mut fields: Vec<Field> = Vec::new();
        if s.fields.is_empty() {
            self.error(
                s.name.span,
                "structs without fields are not supported by the compiler yet",
            );
        }
        for f in &s.fields {
            if fields.iter().any(|g| g.name == f.name.name) {
                self.error(
                    f.name.span,
                    format!(
                        "`{}` has more than one field `{}`",
                        s.name.name, f.name.name
                    ),
                );
                continue;
            }
            let ty = self.field_type(&mut cx, &f.ty, "struct");
            fields.push(Field {
                name: f.name.name.clone(),
                ty,
            });
        }
        fields
    }

    /// Report a struct or an enum named like a primitive type.
    fn check_type_name(&mut self, name: &ast::Ident) {
        if primitive(&name.name, self.ptr_bits).is_some() {
            self.error(
                name.span,
                format!("`{}` is the name of a built-in type", name.name),
            );
        }
    }

    /// The type of a field of a `what` (a struct or a payload), which must
    /// be one that can be stored. A field whose type is in error gets the
    /// type `()`, so later checks see no more problems with it.
    fn field_type(&mut self, cx: &mut FnCx, t: &TypeExpr, what: &str) -> Ty {
        let Some(ty) = self.resolve_type(cx, t) else {
            return Ty::Unit;
        };
        match storable(ty) {
            Ok(()) => ty,
            Err(Some(())) => {
                let (field, holder) = match what {
                    "struct" => ("a struct field", "structs"),
                    _ => ("a payload field", "enums"),
                };
                self.diags.push(
                    Diagnostic::error(t.span(), format!("{field} can't be a view (`{ty}`)"))
                        .with_help(format!(
                            "views are never stored in {holder}, so they can't outlive what they view (docs/memory.md, Views)"
                        ))
                        .with_help("store the data itself, for example in an array"),
                );
                Ty::Unit
            }
            Err(None) => {
                self.error(
                    t.span(),
                    format!("{what} fields of type `{ty}` are not supported by the compiler yet"),
                );
                Ty::Unit
            }
        }
    }

    /// The tag type, whether the variants have declared values, and the
    /// variants of an enum declaration.
    fn enum_variants(
        &mut self,
        e: &ast::EnumDecl,
        pkg: usize,
        file: FileId,
    ) -> (IntTy, bool, Vec<Variant>) {
        let mut cx = FnCx::new(pkg, file, Ty::Unit, false);
        let enum_name = &e.name.name;
        if e.variants.is_empty() {
            self.error(
                e.name.span,
                "enums without variants are not supported by the compiler yet",
            );
        }
        let explicit = e.tag.is_some();
        let tag = match &e.tag {
            Some(t) => match self.resolve_type(&mut cx, t) {
                Some(Ty::Int(it)) => Some(it),
                Some(other) => {
                    self.error(
                        t.span(),
                        format!("the values of an enum must be integers, not `{other}`"),
                    );
                    None
                }
                None => None,
            },
            None => None,
        };
        let mut variants: Vec<Variant> = Vec::new();
        for v in &e.variants {
            let name = &v.name.name;
            if variants.iter().any(|w| &w.name == name) {
                self.error(
                    v.name.span,
                    format!("`{enum_name}` has more than one variant `{name}`"),
                );
                continue;
            }
            let mut fields: Vec<Field> = Vec::new();
            match &v.fields {
                Some(decls) if decls.is_empty() => self.error(
                    v.name.span,
                    format!("`{name}` has no payload, so it's written without parentheses"),
                ),
                Some(_) if explicit => self.error(
                    v.name.span,
                    format!(
                        "`{name}` can't have a payload: the variants of `{enum_name}` are integer values"
                    ),
                ),
                Some(decls) => {
                    for f in decls {
                        if fields.iter().any(|g| g.name == f.name.name) {
                            self.error(
                                f.name.span,
                                format!(
                                    "`{name}` has more than one field `{}`",
                                    f.name.name
                                ),
                            );
                            continue;
                        }
                        let ty = self.field_type(&mut cx, &f.ty, "payload");
                        fields.push(Field {
                            name: f.name.name.clone(),
                            ty,
                        });
                    }
                }
                None => {}
            }
            let value = match (&v.value, tag) {
                (Some(expr), Some(it)) => self.variant_value(&mut cx, expr, it, &variants),
                (Some(_), None) if explicit => None,
                (Some(expr), None) => {
                    self.diags.push(
                        Diagnostic::error(
                            expr.span,
                            "only the variants of an enum with an integer type have values",
                        )
                        .with_help(format!("declare the type: `enum {enum_name}: u8 {{`")),
                    );
                    None
                }
                (None, _) if explicit => {
                    self.error(
                        v.name.span,
                        format!(
                            "`{name}` needs a value, like every variant of `{enum_name}`: `{name} = 1`"
                        ),
                    );
                    None
                }
                (None, _) => Some(variants.len() as i128),
            };
            variants.push(Variant {
                name: name.clone(),
                fields,
                value: value.unwrap_or(variants.len() as i128),
            });
        }
        let tag = tag.unwrap_or(if variants.len() <= 256 {
            IntTy::new(false, 8)
        } else {
            IntTy::new(false, 16)
        });
        (tag, explicit, variants)
    }

    /// The value of a C-style enum's variant: a constant of the tag type
    /// that no earlier variant has.
    fn variant_value(
        &mut self,
        cx: &mut FnCx,
        e: &ast::Expr,
        tag: IntTy,
        earlier: &[Variant],
    ) -> Option<i128> {
        let c = self.expr(cx, e, Some(Ty::Int(tag)))?;
        let c = self.coerce(c, Ty::Int(tag), e.span)?;
        let v = match c.range {
            Some(r) if r.lo == r.hi => r.lo,
            _ => {
                self.error(
                    e.span,
                    "the value of a variant must be known when compiling",
                );
                return None;
            }
        };
        if let Some(other) = earlier.iter().find(|w| w.value == v) {
            self.error(
                e.span,
                format!("`{}` already has the value {v}", other.name),
            );
            return None;
        }
        Some(v)
    }

    /// Report a struct or an enum (`kind`) that holds a value of its own
    /// type, directly or through other structs, enums, arrays and optionals:
    /// it would be infinitely large. Each cycle is reported once, at the
    /// first of its types, and broken (the member closing it becomes `()`)
    /// so later checks terminate.
    fn check_recursion(&mut self, name: &ast::Ident, kind: &str, ty: Ty) {
        // The members leading from `from` back to `ty`, as (type, member index).
        fn path_back(from: Ty, ty: Ty, seen: &mut Vec<Ty>, path: &mut Vec<(Ty, usize)>) -> bool {
            if seen.contains(&from) {
                return false;
            }
            seen.push(from);
            for (i, (_, mty)) in members(from).into_iter().enumerate() {
                let Some(inner) = held_nominal(mty) else {
                    continue;
                };
                path.push((from, i));
                if inner == ty || path_back(inner, ty, seen, path) {
                    return true;
                }
                path.pop();
            }
            false
        }
        loop {
            let mut path = Vec::new();
            if !path_back(ty, ty, &mut Vec::new(), &mut path) {
                return;
            }
            let through: Vec<String> = path
                .iter()
                .map(|&(t, i)| format!("`{}`", members(t)[i].0))
                .collect();
            let holds = if kind == "struct" {
                "a struct holds its fields by value"
            } else {
                "an enum holds its payload by value"
            };
            self.diags.push(
                Diagnostic::error(
                    name.span,
                    format!("the {kind} `{}` contains itself", name.name),
                )
                .with_help(format!("through {}", through.join(", then ")))
                .with_help(format!("{holds}, so it would be infinitely large")),
            );
            let &(last, i) = path.last().expect("a member");
            clear_member(last, i);
        }
    }

    /// The Lode type a type expression names. `cx` is where it appears: array
    /// lengths are constant expressions evaluated there.
    fn resolve_type(&mut self, cx: &mut FnCx, t: &TypeExpr) -> Option<Ty> {
        match t {
            TypeExpr::Unit(_) => Some(Ty::Unit),
            TypeExpr::Array(len, elem, _) => {
                let elem_ty = self.resolve_type(cx, elem)?;
                let len = self.const_count(cx, len)?;
                self.check_elem(elem_ty, "arrays", elem.span())?;
                Some(Ty::array(elem_ty, len))
            }
            TypeExpr::Slice(elem, _) => {
                let elem_ty = self.resolve_type(cx, elem)?;
                self.check_elem(elem_ty, "slices", elem.span())?;
                Some(Ty::slice(elem_ty))
            }
            TypeExpr::Optional(inner, span) => {
                let ty = self.resolve_type(cx, inner)?;
                match storable(ty) {
                    Ok(()) => Some(Ty::optional(ty)),
                    Err(Some(())) => {
                        self.diags.push(
                            Diagnostic::error(*span, format!("an optional can't hold a view (`{ty}`)"))
                                .with_help("views are never stored, so they can't outlive what they view (docs/memory.md, Views)"),
                        );
                        None
                    }
                    Err(None) => {
                        self.error(
                            *span,
                            format!("optionals of `{ty}` are not supported by the compiler yet"),
                        );
                        None
                    }
                }
            }
            TypeExpr::Ptr(inner, span) => match self.resolve_type(cx, inner)? {
                Ty::Int(it) => Some(Ty::Ptr(it)),
                other => {
                    self.error(
                        *span,
                        format!("pointers to `{other}` are not supported by the compiler yet"),
                    );
                    None
                }
            },
            TypeExpr::Qualified(pkg_name, name) => {
                let Some(pkg) = self
                    .imports
                    .get(&cx.file)
                    .and_then(|m| m.get(&pkg_name.name))
                    .copied()
                else {
                    self.error(
                        pkg_name.span,
                        format!("unknown package `{}`", pkg_name.name),
                    );
                    return None;
                };
                match self.package_item(cx, pkg, &name.name, name.span)? {
                    Item::Type(ty) => Some(ty),
                    _ => {
                        self.error(
                            t.span(),
                            format!("`{}.{}` is not a type", pkg_name.name, name.name),
                        );
                        None
                    }
                }
            }
            TypeExpr::Named(id) => match primitive(&id.name, self.ptr_bits) {
                Some(Primitive::Ty(ty)) => Some(ty),
                Some(Primitive::Unsupported) => {
                    self.error(
                        id.span,
                        format!(
                            "the type `{}` is not supported by the compiler yet",
                            id.name
                        ),
                    );
                    None
                }
                None => match self.pkgs[cx.pkg].items.get(&id.name) {
                    Some(Item::Type(ty)) => Some(*ty),
                    Some(_) => {
                        self.error(id.span, format!("`{}` is not a type", id.name));
                        None
                    }
                    None => {
                        self.error(id.span, format!("unknown type `{}`", id.name));
                        None
                    }
                },
            },
        }
    }

    /// Whether `elem` can be the element type of an array or slice (`what`).
    fn check_elem(&mut self, elem: Ty, what: &str, span: Span) -> Option<()> {
        match elem {
            Ty::Int(_)
            | Ty::Bool
            | Ty::Array(_)
            | Ty::Struct(_)
            | Ty::Enum(_)
            | Ty::Optional(_) => Some(()),
            other => {
                self.error(
                    span,
                    format!("{what} of `{other}` are not supported by the compiler yet"),
                );
                None
            }
        }
    }

    /// The value of a constant count, like an array length: an untyped
    /// integer, or a typed integer constant.
    pub(super) fn const_count(&mut self, cx: &mut FnCx, e: &ast::Expr) -> Option<u64> {
        let v = match self.untyped_int(cx, e) {
            Some(v) => v,
            None => {
                let c = self.expr(cx, e, None)?;
                match (&c.expr.kind, c.ty()) {
                    (TExprKind::Int(v), Ty::Int(_)) => *v,
                    _ => {
                        self.error(e.span, "an array length must be a constant integer");
                        return None;
                    }
                }
            }
        };
        match u64::try_from(v) {
            Ok(n) if n <= i64::MAX as u64 => Some(n),
            _ => {
                self.error(e.span, format!("`{v}` is not a valid array length"));
                None
            }
        }
    }

    fn signature(&mut self, cx: &mut FnCx, f: &ast::FnDecl) -> Sig {
        let mut params = Vec::new();
        for p in &f.params {
            if p.convention != Convention::Let {
                self.error(
                    p.name.span,
                    "`inout`, `sink` and `set` parameters are not supported by the compiler yet",
                );
            }
            let ty = self.resolve_type(cx, &p.ty).unwrap_or(Ty::Unit);
            params.push(ty);
        }
        let ret = match &f.ret {
            Some(t) => match self.resolve_type(cx, t) {
                Some(ty @ (Ty::Str | Ty::Slice(_))) => {
                    let what = match ty {
                        Ty::Str => "a `str`",
                        _ => "a slice",
                    };
                    self.error(
                        t.span(),
                        format!("returning {what} is not supported by the compiler yet"),
                    );
                    // The type is kept, so the body is still checked.
                    ty
                }
                Some(ty) => ty,
                None => Ty::Unit,
            },
            None => Ty::Unit,
        };
        Sig {
            is_pub: f.is_pub,
            is_unsafe: f.is_unsafe,
            params,
            ret,
            span: f.name.span,
        }
    }

    /// Look up `name` in package `pkg` as seen from `cx`'s package, reporting
    /// an error if it doesn't exist or is private.
    fn package_item(&mut self, cx: &FnCx, pkg: usize, name: &str, span: Span) -> Option<Item> {
        let Some(&item) = self.pkgs[pkg].items.get(name) else {
            let path = self.pkgs[pkg].path.clone();
            self.error(span, format!("package `{path}` has no `{name}`"));
            return None;
        };
        let is_pub = match item {
            Item::Func(id) => self.sigs[id].is_pub,
            Item::Const(id) => self.consts[id].decl.is_pub,
            Item::Type(ty) => match ty.as_struct() {
                Some(def) => def.is_pub,
                None => ty.as_enum().expect("a struct or an enum").is_pub,
            },
        };
        if pkg != cx.pkg && !is_pub {
            let path = self.pkgs[pkg].path.clone();
            self.error(span, format!("`{name}` is private to package `{path}`"));
            return None;
        }
        Some(item)
    }

    /// The package an import name refers to in `cx`'s file, unless a local
    /// variable of that name hides it.
    fn imported(&self, cx: &FnCx, name: &str) -> Option<usize> {
        if cx.lookup(name).is_some() {
            return None;
        }
        self.imports
            .get(&cx.file)
            .and_then(|m| m.get(name))
            .copied()
    }

    /// Evaluate a constant (once; later calls return the cached value).
    fn const_value(&mut self, id: usize) -> Option<ConstVal> {
        match self.consts[id].state {
            ConstState::Done(v) => return Some(v),
            ConstState::Failed => return None,
            ConstState::Checking => {
                let decl = self.consts[id].decl;
                self.error(
                    decl.name.span,
                    format!("the value of `{}` depends on itself", decl.name.name),
                );
                self.consts[id].state = ConstState::Failed;
                return None;
            }
            ConstState::Unchecked => {}
        }
        self.consts[id].state = ConstState::Checking;
        let ConstInfo {
            decl, pkg, file, ..
        } = self.consts[id];
        let mut cx = FnCx::new(pkg, file, Ty::Unit, false);
        let value = match &decl.ty {
            None => match self.untyped_int(&mut cx, &decl.value) {
                Some(v) => Some(ConstVal::Untyped(v)),
                None => {
                    self.diags.push(
                        Diagnostic::error(
                            decl.value.span,
                            "an untyped constant must be an integer literal or another untyped constant",
                        )
                        .with_help(format!("give it a type, e.g. `const {}: u32 = ...`", decl.name.name)),
                    );
                    None
                }
            },
            Some(t) => {
                let ty = self.resolve_type(&mut cx, t);
                match ty {
                    Some(ty @ Ty::Int(_)) => self
                        .expr(&mut cx, &decl.value, Some(ty))
                        .and_then(|c| self.coerce(c, ty, decl.value.span))
                        .and_then(|c| match c.range {
                            Some(r) if r.lo == r.hi => Some(ConstVal::Typed(ty, r.lo)),
                            _ => {
                                self.error(
                                    decl.value.span,
                                    "the value of a constant must be known when compiling",
                                );
                                None
                            }
                        }),
                    Some(other) => {
                        self.error(
                            t.span(),
                            format!(
                                "constants of type `{other}` are not supported by the compiler yet"
                            ),
                        );
                        None
                    }
                    None => None,
                }
            }
        };
        self.consts[id].state = value.map_or(ConstState::Failed, ConstState::Done);
        value
    }

    fn function(&mut self, f: &ast::FnDecl, id: FuncId, pkg: usize, file: FileId) -> Func {
        let (ret, is_unsafe) = (self.sigs[id].ret, self.sigs[id].is_unsafe);
        let mut cx = FnCx::new(pkg, file, ret, is_unsafe);
        let mut params = Vec::new();
        let param_tys = self.sigs[id].params.clone();
        for (p, &ty) in f.params.iter().zip(&param_tys) {
            if cx.scopes[0].contains_key(&p.name.name) {
                self.error(
                    p.name.span,
                    format!("parameter `{}` is declared twice", p.name.name),
                );
            }
            params.push(self.declare(&mut cx, &p.name.name, ty, false));
        }
        let body = self.block(&mut cx, &f.body.stmts);
        if ret != Ty::Unit && !terminates(&body) {
            self.error(
                f.name.span,
                format!(
                    "`{}` can reach the end of its body without returning a value",
                    f.name.name
                ),
            );
        }
        Func {
            name: f.name.name.clone(),
            symbol: format!("{}.{}", self.pkgs[pkg].path, f.name.name),
            params,
            ret,
            locals: cx.locals,
            body,
            span: f.span,
        }
    }

    fn declare(&mut self, cx: &mut FnCx, name: &str, ty: Ty, mutable: bool) -> LocalId {
        let id = cx.locals.len();
        cx.locals.push(Local {
            name: name.to_owned(),
            ty,
            mutable,
        });
        cx.scopes
            .last_mut()
            .expect("scope")
            .insert(name.to_owned(), id);
        id
    }

    fn intern_string(&mut self, bytes: &[u8]) -> usize {
        if let Some(&id) = self.string_ids.get(bytes) {
            return id;
        }
        self.strings.push(bytes.to_vec());
        self.string_ids
            .insert(bytes.to_vec(), self.strings.len() - 1);
        self.strings.len() - 1
    }

    // --- statements ---------------------------------------------------------

    fn block(&mut self, cx: &mut FnCx, stmts: &[Stmt]) -> Vec<TStmt> {
        cx.scopes.push(HashMap::new());
        let out = stmts.iter().filter_map(|s| self.stmt(cx, s)).collect();
        cx.scopes.pop();
        out
    }

    /// A local was given a new value: record what's known about it.
    fn record_value(cx: &mut FnCx, local: LocalId, value: &expr::Checked) {
        cx.env.assign(local, value.range);
        if let TExprKind::StructLit(_) = value.expr.kind {
            Self::record_fields(cx, local, &value.expr, 0);
        }
        // a == b + k
        let equal = |a: Term, b: Term, k: i128| {
            [
                facts::Fact::Rel { a, b, c: k },
                facts::Fact::Rel { a: b, b: a, c: -k },
            ]
        };
        if let Some(src) = value.term
            && src.term != Term::Local(local)
        {
            // Another term (a local or a length) plus a constant: related to
            // it, as in `let i = xs.len - 1`.
            cx.env
                .apply(&equal(Term::Local(local), src.term, src.offset));
        }
        if cx.locals[local].ty.is_view() {
            match &value.expr.kind {
                // A copy of another view has its length.
                TExprKind::Local(src) if *src != local => {
                    cx.env.apply(&equal(Term::Len(local), Term::Len(*src), 0));
                    if let Some(r) = cx.env.range(Term::Len(*src)) {
                        cx.env.apply(&[facts::Fact::Narrow {
                            term: Term::Len(local),
                            bound: r,
                            full: r,
                        }]);
                    }
                }
                // A view of a whole array has the array's length.
                TExprKind::ToSlice(array) => {
                    let (_, n) = array.ty.as_array().expect("an array");
                    let n = i128::from(n);
                    cx.env.apply(&[facts::Fact::Narrow {
                        term: Term::Len(local),
                        bound: Range::exact(n),
                        full: Range { lo: n, hi: n },
                    }]);
                }
                _ => {}
            }
        }
    }

    /// A struct local was given the value of a literal: its integer fields
    /// given as constants have known values. `base` numbers the literal's
    /// fields among the local's (see [`Term::Field`]).
    fn record_fields(cx: &mut FnCx, local: LocalId, lit: &TExpr, base: u32) {
        let (TExprKind::StructLit(fields), Some(def)) = (&lit.kind, lit.ty.as_struct()) else {
            return;
        };
        for (i, value) in fields {
            let before: u32 = def.fields[..*i as usize]
                .iter()
                .map(|f| expr::flat_size(f.ty))
                .sum();
            let term = Term::Field(local, base + before);
            match (&value.kind, type_range(value.ty)) {
                (TExprKind::Int(v), Some(full)) => cx.env.apply(&[facts::Fact::Narrow {
                    term,
                    bound: Range::exact(*v),
                    full,
                }]),
                (TExprKind::StructLit(_), _) => {
                    Self::record_fields(cx, local, value, base + before);
                }
                _ => {}
            }
        }
    }

    fn stmt(&mut self, cx: &mut FnCx, stmt: &Stmt) -> Option<TStmt> {
        match stmt {
            Stmt::Let {
                mutable,
                name,
                ty,
                init: Some(init),
                otherwise: Some(otherwise),
                ..
            } => self.let_else(cx, *mutable, name, ty.as_ref(), init, otherwise),
            Stmt::Let {
                mutable,
                name,
                ty,
                init,
                span,
                ..
            } => {
                let annotated = match ty {
                    Some(t) => Some(self.resolve_type(cx, t)?),
                    None => None,
                };
                let Some(init) = init else {
                    let what = if *mutable {
                        "`var` without an initial value is"
                    } else {
                        "`let` needs an initial value; it"
                    };
                    self.error(*span, format!("{what} not supported by the compiler yet"));
                    return None;
                };
                if cx.scopes.last().expect("scope").contains_key(&name.name) {
                    self.error(
                        name.span,
                        format!("`{}` is already declared in this block", name.name),
                    );
                    return None;
                }
                let value = self.expr(cx, init, annotated);
                let value = match (value, annotated) {
                    (Some(v), Some(t)) => self.coerce(v, t, init.span),
                    (v, _) => v,
                };
                let Some(value) = value else {
                    // Keep the name declared so later uses don't report it as unknown.
                    if let Some(t) = annotated {
                        self.declare(cx, &name.name, t, *mutable);
                    }
                    return None;
                };
                if value.ty() == Ty::Unit {
                    self.error(init.span, "this expression has no value to store");
                    return None;
                }
                let local = self.declare(cx, &name.name, value.ty(), *mutable);
                self.check_kept_view(cx, &value, init.span)?;
                Self::record_value(cx, local, &value);
                Some(TStmt::Init(local, value.expr))
            }
            Stmt::Assign {
                target,
                op,
                value,
                span,
            } => {
                if let ExprKind::Index(..) | ExprKind::Field(..) = target.kind {
                    return self.place_assign(cx, target, *op, value, *span);
                }
                let ExprKind::Name(name) = &target.kind else {
                    self.error(
                        target.span,
                        "only variables, their elements and their fields can be assigned to",
                    );
                    return None;
                };
                let Some(local) = cx.lookup(name) else {
                    self.error(target.span, format!("cannot find `{name}` in this scope"));
                    return None;
                };
                if !cx.locals[local].mutable {
                    self.diags.push(
                        Diagnostic::error(
                            target.span,
                            format!("cannot assign to `{name}`, which is immutable"),
                        )
                        .with_help(format!("declare it with `var {name}` to make it mutable")),
                    );
                    return None;
                }
                let ty = cx.locals[local].ty;
                let checked = match op {
                    None => self.expr(cx, value, Some(ty))?,
                    Some(op) => {
                        let combined = ast::Expr {
                            kind: ExprKind::Binary(
                                *op,
                                Box::new(target.clone()),
                                Box::new(value.clone()),
                            ),
                            span: *span,
                        };
                        self.expr(cx, &combined, Some(ty))?
                    }
                };
                let checked = self.coerce(checked, ty, value.span)?;
                self.check_kept_view(cx, &checked, value.span)?;
                Self::record_value(cx, local, &checked);
                Some(TStmt::Assign(local, checked.expr))
            }
            Stmt::Expr(e) => {
                if !matches!(e.kind, ExprKind::Call(..)) {
                    self.error(e.span, "this expression has no effect");
                    return None;
                }
                Some(TStmt::Expr(self.expr(cx, e, None)?.expr))
            }
            // A `return` that fails to check still ends control flow, so it's kept
            // (as a bare `return`) to avoid a cascade of "missing return" errors.
            // Lowering never sees it: the program has errors.
            Stmt::Return { value, span } => Some(TStmt::Return(match (value, cx.ret) {
                (None, Ty::Unit) => None,
                (None, ret) => {
                    self.error(
                        *span,
                        format!("this function must return a value of type `{ret}`"),
                    );
                    None
                }
                (Some(v), Ty::Unit) => {
                    self.error(v.span, "this function doesn't return a value");
                    None
                }
                (Some(v), ret) => self
                    .expr(cx, v, Some(ret))
                    .and_then(|checked| self.coerce(checked, ret, v.span))
                    .map(|c| c.expr),
            })),
            Stmt::If(i) => Some(self.if_stmt(cx, i)),
            Stmt::While { cond, body, .. } => {
                self.forget_assigned(cx, &body.stmts);
                let (cond, facts) = self.condition(cx, cond);
                let entry = cx.env.clone();
                cx.env.apply(&facts.when_true);
                cx.loop_depth += 1;
                let body = self.block(cx, &body.stmts);
                cx.loop_depth -= 1;
                // The loop ends when the condition is false, unless a `break`
                // leaves it earlier.
                cx.env = entry;
                if !breaks(&body) {
                    cx.env.apply(&facts.when_false);
                }
                Some(TStmt::While(cond.unwrap_or_else(placeholder_bool), body))
            }
            Stmt::Loop { body, .. } => {
                self.forget_assigned(cx, &body.stmts);
                let entry = cx.env.clone();
                cx.loop_depth += 1;
                let body = self.block(cx, &body.stmts);
                cx.loop_depth -= 1;
                cx.env = entry;
                Some(TStmt::Loop(body))
            }
            Stmt::For {
                var, iter, body, ..
            } => {
                cx.scopes.push(HashMap::new());
                let out = self.for_stmt(cx, var, iter, body);
                cx.scopes.pop();
                out
            }
            Stmt::Break(span) | Stmt::Continue(span) => {
                if cx.loop_depth == 0 {
                    self.error(
                        *span,
                        "`break` and `continue` can only be used inside a loop",
                    );
                    return None;
                }
                Some(if matches!(stmt, Stmt::Break(_)) {
                    TStmt::Break
                } else {
                    TStmt::Continue
                })
            }
            Stmt::Unsafe(block) => {
                cx.unsafe_depth += 1;
                let body = self.block(cx, &block.stmts);
                cx.unsafe_depth -= 1;
                Some(TStmt::Block(body))
            }
            Stmt::Match { value, arms, span } => {
                cx.scopes.push(HashMap::new());
                let out = self.match_stmt(cx, value, arms, *span);
                cx.scopes.pop();
                out
            }
        }
    }

    /// The facts after statements that branch: `envs` are the facts at the
    /// end of each branch, with whether it always leaves. A branch that
    /// leaves contributes nothing; the others are joined.
    fn join_branches(envs: Vec<(Env, bool)>) -> Env {
        envs.into_iter()
            .filter(|(_, leaves)| !leaves)
            .map(|(env, _)| env)
            .reduce(Env::join)
            .unwrap_or_else(Env::unreachable)
    }

    /// `match value { pattern => body ... }` on an enum or an optional, in
    /// a scope of its own (for the hidden local holding `value`, if any).
    /// Every variant must be matched by exactly one arm.
    fn match_stmt(
        &mut self,
        cx: &mut FnCx,
        value: &ast::Expr,
        arms: &[ast::Arm],
        span: Span,
    ) -> Option<TStmt> {
        let checked = self.expr(cx, value, None)?;
        let ty = checked.ty();
        let Some(def) = ty.sum() else {
            self.error(
                value.span,
                format!("`match` needs an enum or an optional, found `{ty}`"),
            );
            return None;
        };
        let mut before = Vec::new();
        let matched = matched_local(cx, checked, &mut before);
        let entry = cx.env.clone();
        let mut covered = vec![false; def.variants.len()];
        let mut wildcard: Option<Span> = None;
        let mut ok = true;
        let mut envs = Vec::new();
        let mut tarms = Vec::new();
        for arm in arms {
            cx.env = entry.clone();
            if wildcard.is_some() {
                self.diags.push(
                    Diagnostic::error(
                        arm.pattern.span(),
                        "this arm is never used: it comes after `_`",
                    )
                    .with_help("`_` matches every variant not matched before it"),
                );
                ok = false;
            }
            // The variants the arm handles, and its payload bindings.
            let mut variants = Vec::new();
            let mut bindings: Vec<(&ast::Ident, u32, Ty)> = Vec::new();
            match &arm.pattern {
                ast::Pattern::Wildcard(wspan) => {
                    variants = (0..covered.len() as u32)
                        .filter(|&v| !covered[v as usize])
                        .collect();
                    self.lint_wildcard(cx, ty, &def, &variants, *wspan);
                    covered.fill(true);
                    wildcard = wildcard.or(Some(*wspan));
                }
                ast::Pattern::Variant {
                    name,
                    bindings: names,
                    ..
                } => match def.variant(&name.name) {
                    None => {
                        self.error(name.span, format!("`{ty}` has no variant `{}`", name.name));
                        ok = false;
                    }
                    Some((v, variant)) => {
                        if covered[v] && wildcard.is_none() {
                            self.error(
                                name.span,
                                format!("`{}` is already matched by an earlier arm", name.name),
                            );
                            ok = false;
                        }
                        covered[v] = true;
                        variants.push(v as u32);
                        match names {
                            Some(names) if names.len() != variant.fields.len() => {
                                let msg = if variant.fields.is_empty() {
                                    format!(
                                        "`{}` has no payload, so it's matched without parentheses",
                                        name.name
                                    )
                                } else {
                                    format!(
                                        "`{}` has {} payload field(s), but the pattern binds {}",
                                        name.name,
                                        variant.fields.len(),
                                        names.len()
                                    )
                                };
                                self.error(arm.pattern.span(), msg);
                                ok = false;
                            }
                            Some(names) => {
                                for (k, (b, f)) in names.iter().zip(&variant.fields).enumerate() {
                                    if b.name == "_" {
                                        continue;
                                    }
                                    if bindings.iter().any(|(o, ..)| o.name == b.name) {
                                        self.error(
                                            b.span,
                                            format!("`{}` is bound twice in this pattern", b.name),
                                        );
                                        ok = false;
                                        continue;
                                    }
                                    bindings.push((b, k as u32, f.ty));
                                }
                            }
                            None => {}
                        }
                    }
                },
            }
            cx.scopes.push(HashMap::new());
            let mut body = Vec::new();
            if let [v] = variants[..] {
                for (b, k, fty) in bindings {
                    let local = self.declare(cx, &b.name, fty, false);
                    let value = expr::Checked::new(
                        TExprKind::Payload(Box::new(matched.clone()), v, k),
                        fty,
                        None,
                    );
                    Self::record_value(cx, local, &value);
                    body.push(TStmt::Init(local, value.expr));
                }
            }
            body.extend(self.block(cx, &arm.body.stmts));
            cx.scopes.pop();
            envs.push((std::mem::take(&mut cx.env), diverges(&body)));
            tarms.push(TArm { variants, body });
        }
        let missing: Vec<String> = def
            .variants
            .iter()
            .zip(&covered)
            .filter(|&(_, &c)| !c)
            .map(|(v, _)| format!("`{}`", v.name))
            .collect();
        cx.env = Self::join_branches(envs);
        if !missing.is_empty() {
            let s = if missing.len() == 1 { "" } else { "s" };
            self.diags.push(
                Diagnostic::error(
                    span,
                    format!(
                        "this `match` doesn't handle the variant{s} {} of `{ty}`",
                        missing.join(", ")
                    ),
                )
                .with_help("add an arm for each, or `_ => ...` for the rest"),
            );
            ok = false;
        }
        if !ok {
            return None;
        }
        before.push(TStmt::Match {
            value: matched,
            arms: tarms,
        });
        Some(one_stmt(before))
    }

    /// Warn about a `_` arm that hides variants added later (on an enum of
    /// the same package, which can list them all), or that matches nothing.
    fn lint_wildcard(
        &mut self,
        cx: &FnCx,
        ty: Ty,
        def: &crate::types::EnumDef,
        rest: &[u32],
        span: Span,
    ) {
        let names: Vec<String> = rest
            .iter()
            .map(|&v| format!("`{}`", def.variants[v as usize].name))
            .collect();
        if rest.is_empty() {
            // On another package's enum, `_` handles variants it may add.
            if def.pkg == cx.pkg || ty.as_optional().is_some() {
                self.diags.push(Diagnostic::warning(
                    span,
                    format!("this `_` matches nothing: every variant of `{ty}` is matched above"),
                ));
            }
        } else if def.pkg == cx.pkg {
            self.diags.push(
                Diagnostic::warning(
                    span,
                    format!("`_` hides the variants of `{ty}` that are added later"),
                )
                .with_help(format!(
                    "match {} by name, so a new variant must be handled where `{ty}` is matched",
                    names.join(", ")
                )),
            );
        }
    }

    /// `if let name = opt { ... } else { ... }`: a `match` on the optional
    /// `opt`, with `name` bound to its value in the first block.
    fn if_let(&mut self, cx: &mut FnCx, i: &ast::IfStmt, name: &ast::Ident) -> TStmt {
        let checked = self.expr(cx, &i.cond, None);
        let inner = match &checked {
            Some(c) => match c.ty().as_optional() {
                Some(inner) => Some(inner),
                None => {
                    self.diags.push(
                        Diagnostic::error(
                            i.cond.span,
                            format!("`if let` needs an optional, found `{}`", c.ty()),
                        )
                        .with_help("use `match` for an enum"),
                    );
                    None
                }
            },
            None => None,
        };
        let mut before = Vec::new();
        cx.scopes.push(HashMap::new());
        let matched = match (checked, inner) {
            (Some(c), Some(_)) => Some(matched_local(cx, c, &mut before)),
            _ => None,
        };
        let entry = cx.env.clone();

        cx.scopes.push(HashMap::new());
        // The value's type, or `()` if it's in error (only to keep checking).
        let local = self.declare(cx, &name.name, inner.unwrap_or(Ty::Unit), false);
        cx.env.assign(local, None);
        let mut then = Vec::new();
        if let (Some(m), Some(t)) = (&matched, inner) {
            then.push(TStmt::Init(local, payload(m, 1, 0, t)));
        }
        then.extend(self.block(cx, &i.then.stmts));
        cx.scopes.pop();
        let then_env = std::mem::replace(&mut cx.env, entry);

        let otherwise = match &i.otherwise {
            None => Vec::new(),
            Some(ast::Else::Block(b)) => self.block(cx, &b.stmts),
            Some(ast::Else::If(inner)) => vec![self.if_stmt(cx, inner)],
        };
        cx.scopes.pop();
        let else_env = std::mem::take(&mut cx.env);
        cx.env = Self::join_branches(vec![
            (then_env, diverges(&then)),
            (else_env, diverges(&otherwise)),
        ]);
        let Some(matched) = matched else {
            // In error: kept for control-flow analysis only.
            return TStmt::If(placeholder_bool(), then, otherwise);
        };
        before.push(TStmt::Match {
            value: matched,
            arms: vec![
                TArm {
                    variants: vec![1],
                    body: then,
                },
                TArm {
                    variants: vec![0],
                    body: otherwise,
                },
            ],
        });
        one_stmt(before)
    }

    /// `let name = opt else { ... }`: `name` is the value of the optional
    /// `opt`, and the block, which must leave, runs when it's `none`.
    fn let_else(
        &mut self,
        cx: &mut FnCx,
        mutable: bool,
        name: &ast::Ident,
        ty: Option<&TypeExpr>,
        init: &ast::Expr,
        otherwise: &ast::Block,
    ) -> Option<TStmt> {
        let annotated = match ty {
            Some(t) => Some(self.resolve_type(cx, t)?),
            None => None,
        };
        let checked = self.expr(cx, init, annotated.map(Ty::optional))?;
        let Some(inner) = checked.ty().as_optional() else {
            self.diags.push(
                Diagnostic::error(
                    init.span,
                    format!("`let ... else` needs an optional, found `{}`", checked.ty()),
                )
                .with_help("the `else` block runs when the optional is `none`"),
            );
            return None;
        };
        if let Some(t) = annotated
            && t != inner
        {
            self.error(
                init.span,
                format!("expected `?{t}`, found `{}`", checked.ty()),
            );
            return None;
        }
        let mut before = Vec::new();
        let matched = matched_local(cx, checked, &mut before);
        let entry = cx.env.clone();
        let else_body = self.block(cx, &otherwise.stmts);
        cx.env = entry;
        if !diverges(&else_body) {
            self.diags.push(
                Diagnostic::error(
                    otherwise.span,
                    "the `else` block of `let ... else` must leave",
                )
                .with_help("end it with `return`, `break` or `continue`"),
            );
            return None;
        }
        if cx.scopes.last().expect("scope").contains_key(&name.name) {
            self.error(
                name.span,
                format!("`{}` is already declared in this block", name.name),
            );
            return None;
        }
        let local = self.declare(cx, &name.name, inner, mutable);
        let value = expr::Checked::new(
            TExprKind::Payload(Box::new(matched.clone()), 1, 0),
            inner,
            None,
        );
        Self::record_value(cx, local, &value);
        before.push(TStmt::Match {
            value: matched,
            arms: vec![
                TArm {
                    variants: vec![0],
                    body: else_body,
                },
                TArm {
                    variants: vec![1],
                    body: Vec::new(),
                },
            ],
        });
        before.push(TStmt::Init(local, value.expr));
        Some(TStmt::Block(before))
    }

    /// At the head of a loop: forget the facts about every variable the loop
    /// body assigns, since they may change on each iteration.
    fn forget_assigned(&mut self, cx: &mut FnCx, body: &[Stmt]) {
        let mut names = HashSet::new();
        assigned_names(body, &mut names);
        for name in names {
            if let Some(local) = cx.lookup(&name) {
                cx.env.forget(local);
            }
        }
    }

    /// A `for` loop, in a scope of its own (for the loop variable and the
    /// hidden locals of `for x in xs`).
    ///
    /// `for i in a..b` evaluates `a` and `b` once. In the body, `i` is
    /// immutable and `a <= i < b`: its range is `a.lo..=b.hi - 1`, and when
    /// `a` or `b` is a term the body doesn't assign, `i` is related to it.
    ///
    /// `for x in xs` is an index loop over `0..xs.len` with a hidden index
    /// `$i` and `let x = xs[$i]` at the top of the body. `xs` is evaluated
    /// once: unless it's a local the body doesn't assign, it's copied to a
    /// hidden local `$seq` first.
    fn for_stmt(
        &mut self,
        cx: &mut FnCx,
        var: &ast::Ident,
        iter: &ast::ForIter,
        body: &ast::Block,
    ) -> Option<TStmt> {
        let mut assigned = HashSet::new();
        assigned_names(&body.stmts, &mut assigned);
        let usize_ty = self.usize_ty();
        let mut before = Vec::new();
        // The range, and for `for x in xs`, the name of the sequence.
        let (start, end, each) = match iter {
            ast::ForIter::Range(a, b) => {
                // Ranges are mostly for indexing: two untyped bounds are `usize`.
                let untyped =
                    self.untyped_int(cx, a).is_some() && self.untyped_int(cx, b).is_some();
                let (start, end) = self.operands(cx, a, b, untyped.then_some(usize_ty))?;
                if start.ty().as_int().is_none() {
                    self.error(
                        a.span.to(b.span),
                        format!("a range needs integers, found `{}`", start.ty()),
                    );
                    return None;
                }
                (start, end, None)
            }
            ast::ForIter::Each(xs) => {
                let seq = self.expr(cx, xs, None)?;
                let (elem, len) = match (seq.ty().as_array(), seq.ty().as_slice()) {
                    (Some((elem, n)), _) => (elem, Some(n)),
                    (_, Some(elem)) => (elem, None),
                    _ => {
                        self.error(
                            xs.span,
                            format!(
                                "`for` goes over a range `a..b`, an array or a slice; found `{}`",
                                seq.ty()
                            ),
                        );
                        return None;
                    }
                };
                let seq_name = match (&xs.kind, &seq.expr.kind) {
                    (ExprKind::Name(name), TExprKind::Local(_)) if !assigned.contains(name) => {
                        name.clone()
                    }
                    _ => {
                        let hidden = self.declare(cx, SEQ, seq.ty(), false);
                        Self::record_value(cx, hidden, &seq);
                        before.push(TStmt::Init(hidden, seq.expr));
                        SEQ.to_owned()
                    }
                };
                let local = cx.lookup(&seq_name).expect("declared");
                let end = match len {
                    Some(n) => {
                        let n = i128::from(n);
                        expr::Checked::new(TExprKind::Int(n), usize_ty, Some(Range::exact(n)))
                    }
                    None => self.view_len(
                        cx,
                        TExpr {
                            kind: TExprKind::Local(local),
                            ty: cx.locals[local].ty,
                        },
                    ),
                };
                let start = expr::Checked::new(TExprKind::Int(0), usize_ty, Some(Range::exact(0)));
                (start, end, Some((seq_name, elem)))
            }
        };

        self.forget_assigned(cx, &body.stmts);
        let entry = cx.env.clone();

        // What the body knows about the loop variable.
        let ty = start.ty();
        let index = match &each {
            Some(_) => self.declare(cx, INDEX, ty, false),
            None => self.declare(cx, &var.name, ty, false),
        };
        let (lo, hi) = (start.int_range().lo, end.int_range().hi - 1);
        // An empty range: the body never runs, and any range will do.
        cx.env.assign(index, Some(Range { lo, hi: hi.max(lo) }));
        // A bound that's a term the body doesn't assign keeps its value for
        // the whole loop, so the index can be related to it.
        let unassigned = |cx: &FnCx, t: Term| !assigned.contains(&cx.locals[t.local()].name);
        let mut loop_facts = Vec::new();
        if let Some(e) = end.term
            && unassigned(cx, e.term)
        {
            // i < e + k: i - e <= k - 1
            loop_facts.push(facts::Fact::Rel {
                a: Term::Local(index),
                b: e.term,
                c: e.offset - 1,
            });
        }
        if let Some(s) = start.term
            && unassigned(cx, s.term)
        {
            // s + k <= i: s - i <= -k
            loop_facts.push(facts::Fact::Rel {
                a: s.term,
                b: Term::Local(index),
                c: -s.offset,
            });
        }
        cx.env.apply(&loop_facts);

        cx.loop_depth += 1;
        let mut stmts = Vec::new();
        if let Some((seq_name, elem)) = &each {
            // let x = seq[$i]
            let element = ast::Expr {
                kind: ExprKind::Index(
                    Box::new(ast::Expr {
                        kind: ExprKind::Name(seq_name.clone()),
                        span: var.span,
                    }),
                    Box::new(ast::Expr {
                        kind: ExprKind::Name(INDEX.to_owned()),
                        span: var.span,
                    }),
                ),
                span: var.span,
            };
            let value = if end.range == Some(Range::exact(0)) {
                // An empty array: the body never runs, so the element read
                // needs no proof (there's no index that could be proven).
                let seq = cx.lookup(seq_name).expect("declared");
                let index = cx.lookup(INDEX).expect("declared");
                let local = |l: LocalId, ty: Ty| TExpr {
                    kind: TExprKind::Local(l),
                    ty,
                };
                let kind = TExprKind::Index(
                    Box::new(local(seq, cx.locals[seq].ty)),
                    Box::new(local(index, usize_ty)),
                );
                Some(expr::Checked::new(kind, *elem, None))
            } else {
                self.expr(cx, &element, Some(*elem))
            };
            let x = self.declare(cx, &var.name, *elem, false);
            if let Some(value) = value {
                Self::record_value(cx, x, &value);
                stmts.push(TStmt::Init(x, value.expr));
            }
        }
        stmts.extend(self.block(cx, &body.stmts));
        cx.loop_depth -= 1;
        cx.env = entry;

        let for_loop = TStmt::For {
            var: index,
            start: start.expr,
            end: end.expr,
            body: stmts,
        };
        if before.is_empty() {
            Some(for_loop)
        } else {
            before.push(for_loop);
            Some(TStmt::Block(before))
        }
    }

    /// A slice stored in a local must not see its array change: the array
    /// can't be changed while a view of it is in use (docs/memory.md, Views),
    /// and until the compiler checks that, a slice local may only view a
    /// `let` array (or part of one), or part of another view. A slice of a
    /// `var` array or of a temporary can still be passed to a function.
    fn check_kept_view(&mut self, cx: &FnCx, value: &expr::Checked, span: Span) -> Option<()> {
        let TExprKind::ToSlice(array) = &value.expr.kind else {
            return Some(());
        };
        let mut root = &**array;
        while let TExprKind::Index(base, _) | TExprKind::Field(base, _) = &root.kind {
            root = base;
        }
        let diag = match root.kind {
            // Reassigning a `var` view doesn't change what it viewed.
            TExprKind::Local(l) if !cx.locals[l].mutable || cx.locals[l].ty.is_view() => {
                return Some(());
            }
            TExprKind::Local(l) => {
                let name = &cx.locals[l].name;
                Diagnostic::error(
                    span,
                    format!("cannot keep a slice of `{name}`, which is mutable"),
                )
                .with_help(format!(
                    "declare it with `let`, or pass `{name}` straight to the function that takes the slice"
                ))
            }
            _ => Diagnostic::error(span, "cannot keep a slice of a temporary array")
                .with_help("store the array with `let` first"),
        };
        self.diags.push(diag);
        None
    }

    /// `a[i] = v`, `p.x = v`, `a[i].x[j] op= v`: assign to an element or
    /// a field of a `var` array or struct.
    fn place_assign(
        &mut self,
        cx: &mut FnCx,
        target: &ast::Expr,
        op: Option<ast::BinOp>,
        value: &ast::Expr,
        span: Span,
    ) -> Option<TStmt> {
        let root = place_root(target);
        let ExprKind::Name(name) = &root.kind else {
            self.error(
                root.span,
                "only variables, their elements and their fields can be assigned to",
            );
            return None;
        };
        let Some(local) = cx.lookup(name) else {
            self.error(root.span, format!("cannot find `{name}` in this scope"));
            return None;
        };
        let root_ty = cx.locals[local].ty;
        if root_ty.is_view() {
            self.diags.push(
                Diagnostic::error(
                    target.span,
                    format!("cannot assign through `{name}`, which is a `{root_ty}`"),
                )
                .with_help("slices are read-only views for now"),
            );
            return None;
        }
        if root_ty.in_memory() && !cx.locals[local].mutable {
            let part = match target.kind {
                ExprKind::Field(..) => "a field",
                _ => "an element",
            };
            self.diags.push(
                Diagnostic::error(
                    target.span,
                    format!("cannot assign to {part} of `{name}`, which is immutable"),
                )
                .with_help(format!("declare it with `var {name}` to make it mutable")),
            );
            return None;
        }

        // For `op=`, the target is read and then written: an index that
        // isn't a variable or a constant is evaluated once, into a hidden
        // local.
        let mut before = Vec::new();
        let mut target = target.clone();
        if op.is_some() {
            let usize_ty = self.usize_ty();
            let mut place = &mut target;
            loop {
                let (base, index) = match &mut place.kind {
                    ExprKind::Index(base, index) => (base, index),
                    ExprKind::Field(base, _) => {
                        place = base;
                        continue;
                    }
                    _ => break,
                };
                let simple = matches!(index.kind, ExprKind::Name(_))
                    || self.untyped_int(cx, index).is_some();
                if !simple {
                    let checked = self.expr(cx, index, Some(usize_ty))?;
                    let name = format!("$index{}", before.len());
                    let hidden = self.declare(cx, &name, checked.ty(), false);
                    Self::record_value(cx, hidden, &checked);
                    before.push(TStmt::Init(hidden, checked.expr));
                    **index = ast::Expr {
                        kind: ExprKind::Name(name),
                        span: index.span,
                    };
                }
                place = base;
            }
        }

        let place = self.expr(cx, &target, None)?;
        let ty = place.ty();
        let checked = match op {
            None => self.expr(cx, value, Some(ty))?,
            Some(op) => {
                let combined = ast::Expr {
                    kind: ExprKind::Binary(op, Box::new(target), Box::new(value.clone())),
                    span,
                };
                self.expr(cx, &combined, Some(ty))?
            }
        };
        let checked = self.coerce(checked, ty, value.span)?;
        // A field reached through fields only is a term, or a struct of them:
        // forget what was known about them, then learn their new values.
        // Anything under an index is in an array, which has no facts.
        if let Some(Term::Field(l, off)) = expr::place_term(&place.expr) {
            cx.env.forget_fields(l, off..off + expr::flat_size(ty));
            Self::record_fields(cx, l, &checked.expr, off);
        }
        if let Some(Linear { term, offset: 0 }) = place.term {
            if let Some(r) = checked.range {
                cx.env.apply(&[facts::Fact::Narrow {
                    term,
                    bound: r,
                    full: type_range(ty).unwrap_or(r),
                }]);
            }
            if let Some(src) = checked.term
                && src.term != term
            {
                cx.env.apply(&[
                    facts::Fact::Rel {
                        a: term,
                        b: src.term,
                        c: src.offset,
                    },
                    facts::Fact::Rel {
                        a: src.term,
                        b: term,
                        c: -src.offset,
                    },
                ]);
            }
        }
        let store = TStmt::Store(place.expr, checked.expr);
        if before.is_empty() {
            Some(store)
        } else {
            before.push(store);
            Some(TStmt::Block(before))
        }
    }

    fn if_stmt(&mut self, cx: &mut FnCx, i: &ast::IfStmt) -> TStmt {
        if let Some(name) = &i.binding {
            return self.if_let(cx, i, name);
        }
        let (cond, facts) = self.condition(cx, &i.cond);
        let before = cx.env.clone();

        cx.env.apply(&facts.when_true);
        let then = self.block(cx, &i.then.stmts);
        let then_env = std::mem::replace(&mut cx.env, before);

        cx.env.apply(&facts.when_false);
        let otherwise = match &i.otherwise {
            None => Vec::new(),
            Some(ast::Else::Block(b)) => self.block(cx, &b.stmts),
            Some(ast::Else::If(inner)) => vec![self.if_stmt(cx, inner)],
        };
        let else_env = std::mem::take(&mut cx.env);

        // Facts after the `if`: a branch that always leaves the block (with
        // `return`, `break` or `continue`) contributes nothing.
        cx.env = match (diverges(&then), diverges(&otherwise)) {
            (true, false) => else_env,
            (false, true) => then_env,
            (true, true) => Env::unreachable(),
            (false, false) => Env::join(then_env, else_env),
        };
        TStmt::If(cond.unwrap_or_else(placeholder_bool), then, otherwise)
    }

    fn condition(&mut self, cx: &mut FnCx, e: &ast::Expr) -> (Option<TExpr>, facts::CondFacts) {
        match self
            .expr(cx, e, Some(Ty::Bool))
            .and_then(|c| self.coerce(c, Ty::Bool, e.span))
        {
            Some(c) => {
                let facts = c.facts.map(|f| *f).unwrap_or_default();
                (Some(c.expr), facts)
            }
            None => (None, facts::CondFacts::default()),
        }
    }
}

/// The range of values a type's integers can hold (`None` for non-integers).
fn type_range(ty: Ty) -> Option<Range> {
    ty.as_int().map(|t| t.range())
}
