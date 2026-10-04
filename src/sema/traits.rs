//! Traits declared in Lode and their implementations (docs/generics.md,
//! Traits, Implementations, Coherence; M7c).
//!
//! A trait's methods are functions whose first generic parameter is
//! `Self`, a type parameter bounded by the trait: a default method has a
//! body, checked once against the trait; a required one has none. An
//! `impl` registers the trait for a named type ([`crate::types::add_impl`]),
//! and its methods are methods of the type, with the impl's parameters as
//! the type's. A call of a trait's method on a type parameter is a generic
//! call of the trait's function; [`Dispatch::resolve`] points it at the
//! impl's method (or the default) once `Self` is known, in `crate::mono`
//! and in the compile-time evaluator.
//!
//! The built-in `Ordered` can be implemented too (`impl Ordered for
//! Point`): its `cmp` is required, `lt`, `le`, `gt` and `ge` may be given,
//! and otherwise come from `cmp` ([`Dispatch::ordered`]).

use std::collections::HashMap;

use crate::ast::{self, TypeExpr};
use crate::diag::Diagnostic;
use crate::source::{FileId, Span};
use crate::types::{AssocType, ImplDef, IntTy, Primitive, Trait, Ty, primitive};

use super::generic::GenericEdge;
use super::tree::*;
use super::{Checker, FnCx, Item, Sig};

/// A trait declared in Lode, as the checker knows it.
pub(super) struct TraitInfo<'a> {
    pub trait_: Trait,
    pub decl: &'a ast::TraitDecl,
    pub pkg: usize,
    pub file: FileId,
    /// `Self` in its methods: a type parameter bounded by the trait.
    pub self_param: Ty,
    /// Its methods and associated functions, by name, with their function
    /// ids, and whether each has a default body.
    pub methods: Vec<(String, FuncId, bool)>,
}

/// An `impl` block, as the checker knows it.
pub(super) struct ImplInfo<'a> {
    pub decl: &'a ast::ImplDecl,
    pub pkg: usize,
    pub file: FileId,
    /// The trait and `Self`, the type with the impl's parameters as its
    /// arguments; `None` if the header is in error (reported).
    pub head: Option<(Trait, Ty)>,
    /// The impl's generic parameters and the traits each declares.
    pub params: Vec<Ty>,
    pub bounds: Vec<Vec<Trait>>,
    /// Its methods, by name, with their function ids.
    pub methods: Vec<(String, FuncId)>,
}

/// What a function declared in a trait or an `impl` belongs to.
#[derive(Clone, Copy, Debug)]
pub(super) enum Member {
    /// The trait with this index in [`Checker::traits`]; whether the
    /// method has a body.
    Trait(usize, bool),
    /// The `impl` with this index in [`Checker::impls`].
    Impl(usize),
}

/// The methods `Ordered` gives, besides `cmp`: an `impl Ordered` may
/// write them, or they come from `cmp`.
const ORDERED_DEFAULTS: [&str; 4] = ["lt", "le", "gt", "ge"];

/// How a function's signature is written, for messages: `fn area(self) ->
/// u32`.
fn sig_text(name: &str, sig: &Sig, map: &impl Fn(Ty) -> Option<Ty>) -> String {
    let method = name.rsplit('.').next().unwrap_or(name);
    let params: Vec<String> = sig
        .params
        .iter()
        .enumerate()
        .map(|(k, (ty, conv, pname))| {
            let conv = match conv {
                Convention::Let => "",
                Convention::Inout => "inout ",
                Convention::Sink => "sink ",
                Convention::Set => "set ",
            };
            if k == 0 && sig.has_self {
                format!("{conv}self")
            } else {
                format!("{conv}{pname}: {}", ty.subst(map))
            }
        })
        .collect();
    let mut out = format!("fn {method}({})", params.join(", "));
    if let Some(e) = sig.throws {
        out.push_str(&format!(" throws({})", e.subst(map)));
    }
    if sig.ret != Ty::Unit {
        out.push_str(&format!(" -> {}", sig.ret.subst(map)));
    }
    out
}

impl<'a> Checker<'a> {
    /// The trait a bound names: a built-in one, a trait of the package, or
    /// `pkg.Trait` of an imported package (reported if it's none).
    pub(super) fn resolve_bound(
        &mut self,
        pkg: usize,
        file: FileId,
        b: &ast::Bound,
    ) -> Option<Trait> {
        let name = &b.name.name;
        let found = match &b.pkg {
            None => match self.pkgs[pkg].items.get(name) {
                Some(&Item::Trait(t)) => Some(t),
                Some(_) => None,
                None => Trait::from_name(name),
            },
            Some(p) => {
                let Some(&target) = self.imports.get(&file).and_then(|m| m.get(&p.name)) else {
                    self.error(p.span, format!("unknown package `{}`", p.name));
                    return None;
                };
                match self.pkgs[target].items.get(name) {
                    Some(&Item::Trait(t)) => {
                        let info = &self.traits[self.trait_index[&t]];
                        if target != pkg && !info.decl.is_pub {
                            let path = self.pkgs[target].path.clone();
                            self.error(
                                b.span(),
                                format!("`{name}` is private to package `{path}`"),
                            );
                            return None;
                        }
                        Some(t)
                    }
                    Some(_) => None,
                    None => {
                        let path = self.pkgs[target].path.clone();
                        self.error(b.span(), format!("package `{path}` has no `{name}`"));
                        return None;
                    }
                }
            }
        };
        if found.is_none() {
            let text = b.text();
            let msg = match self.pkgs[pkg].items.get(name) {
                Some(_) if b.pkg.is_none() => format!("`{text}` is not a trait"),
                _ if b.pkg.is_some() => format!("`{text}` is not a trait"),
                _ => format!("unknown trait `{text}`"),
            };
            self.diags.push(Diagnostic::error(b.span(), msg).with_help(
                "a bound is a trait: a built-in one (`Eq`, `Ordered`, `Copy`, `Integer`, `Unsigned`, `Signed`) or one declared with `trait`",
            ));
        }
        found
    }

    /// Declare the traits of package `pkg` (their names, so bounds can
    /// name them).
    pub(super) fn declare_trait_names(
        &mut self,
        items: &[&'a ast::Item],
        pkg: usize,
        file: FileId,
        shown: impl Fn(&str) -> String,
    ) {
        for item in items {
            let ast::Item::Trait(t) = item else {
                continue;
            };
            let tr = Trait::declare(shown(&t.name.name), pkg, self.ptr_bits);
            if self.pkgs[pkg].items.contains_key(&t.name.name)
                || primitive(&t.name.name, self.ptr_bits).is_some()
                || Trait::from_name(&t.name.name).is_some()
            {
                self.error(
                    t.name.span,
                    format!("`{}` is defined more than once", t.name.name),
                );
            }
            self.pkgs[pkg]
                .items
                .insert(t.name.name.clone(), Item::Trait(tr));
            self.trait_index.insert(tr, self.traits.len());
            self.traits.push(TraitInfo {
                trait_: tr,
                decl: t,
                pkg,
                file,
                self_param: Ty::Unit,
                methods: Vec::new(),
            });
        }
    }

    /// Resolve every trait's supertraits and associated items, then give
    /// each its `Self`.
    pub(super) fn declare_trait_items(&mut self) {
        for k in 0..self.traits.len() {
            let (decl, pkg, file, tr) = {
                let t = &self.traits[k];
                (t.decl, t.pkg, t.file, t.trait_)
            };
            let mut supers = Vec::new();
            for b in &decl.supers {
                if let Some(s) = self.resolve_bound(pkg, file, b) {
                    if s == tr {
                        self.error(
                            b.span(),
                            format!("`{}` can't be its own supertrait", b.text()),
                        );
                    } else if !supers.contains(&s) {
                        supers.push(s);
                    }
                }
            }
            let mut types = Vec::new();
            let mut consts = Vec::new();
            let mut names: Vec<&str> = Vec::new();
            for item in &decl.items {
                let name = match item {
                    ast::TraitItem::Method { decl, .. } => &decl.name,
                    ast::TraitItem::Type { name, .. } | ast::TraitItem::Const { name, .. } => name,
                };
                if names.contains(&name.name.as_str()) {
                    self.error(
                        name.span,
                        format!("`{}` has more than one `{}`", decl.name.name, name.name),
                    );
                    continue;
                }
                names.push(&name.name);
                match item {
                    ast::TraitItem::Method { .. } => {}
                    ast::TraitItem::Type { name, bounds } => {
                        let bounds = bounds
                            .iter()
                            .filter_map(|b| self.resolve_bound(pkg, file, b))
                            .collect();
                        types.push(AssocType {
                            name: name.name.clone(),
                            bounds,
                        });
                    }
                    ast::TraitItem::Const { name, ty } => {
                        let it = match ty {
                            TypeExpr::Named(id) => match primitive(&id.name, self.ptr_bits) {
                                Some(Primitive::Ty(Ty::Int(it))) => Some(it),
                                _ => None,
                            },
                            _ => None,
                        };
                        match it {
                            Some(it) => consts.push((name.name.clone(), it)),
                            None => self.diags.push(
                                Diagnostic::error(
                                    ty.span(),
                                    "an associated constant is an integer",
                                )
                                .with_help("as in `const MAX_LEN: usize`"),
                            ),
                        }
                    }
                }
            }
            tr.set_def(supers, types, consts);
        }
        // A cycle of supertraits: each trait in it is reported.
        for k in 0..self.traits.len() {
            let tr = self.traits[k].trait_;
            let def = tr.def().expect("a declared trait");
            if def.supers.iter().any(|s| s.with_supers().contains(&tr)) {
                let span = self.traits[k].decl.name.span;
                self.error(
                    span,
                    format!("`{tr}` is its own supertrait, through its supertraits"),
                );
                tr.set_def(Vec::new(), def.types.clone(), def.consts.clone());
            }
        }
        for t in &mut self.traits {
            t.self_param = Ty::new_param(
                "Self".to_owned(),
                crate::types::Bounds::new(&[t.trait_]),
                self.ptr_bits,
            );
        }
    }

    /// The package a trait belongs to for coherence: its declaring package,
    /// or the standard library (`None`) for a built-in one.
    fn trait_pkg(&self, t: Trait) -> Option<usize> {
        t.def().map(|d| d.pkg)
    }

    /// Whether package `pkg` is part of the standard library, which owns
    /// the built-in traits and types.
    fn is_std(&self, pkg: usize) -> bool {
        self.pkgs[pkg].path.starts_with("std/")
    }

    /// Resolve each `impl`'s header (its trait, its type and its
    /// parameters), check coherence, and register it with its associated
    /// types and constants.
    pub(super) fn declare_impls(&mut self) {
        for k in 0..self.impls.len() {
            let (decl, pkg, file) = {
                let i = &self.impls[k];
                (i.decl, i.pkg, i.file)
            };
            let Some(tr) = self.resolve_bound(pkg, file, &decl.trait_) else {
                continue;
            };
            let tspan = decl.trait_.span();
            match tr {
                Trait::Eq => {
                    self.diags.push(
                        Diagnostic::error(tspan, "`Eq` is derived, never implemented")
                            .with_help("a type is `Eq` when its fields are: `==` compares them (docs/generics.md, Operators in generic code)"),
                    );
                    continue;
                }
                Trait::Copy => {
                    self.diags.push(
                        Diagnostic::error(tspan, "`Copy` is automatic, never implemented")
                            .with_help("a type is `Copy` when its fields are"),
                    );
                    continue;
                }
                Trait::Integer | Trait::Unsigned | Trait::Signed => {
                    self.diags.push(
                        Diagnostic::error(tspan, format!("`{tr}` is sealed")).with_help(
                            "only the integer types implement it: its operators are theirs",
                        ),
                    );
                    continue;
                }
                Trait::Ordered | Trait::User(_) => {}
            }
            let Some((ty, params, bounds)) = self.impl_type(decl, pkg, file) else {
                continue;
            };
            // Coherence: in the trait's package or the type's.
            let type_pkg = match ty.as_struct() {
                Some(d) => Some(d.pkg),
                None => ty.as_enum().map(|d| d.pkg),
            };
            let in_trait_pkg = match self.trait_pkg(tr) {
                Some(p) => p == pkg,
                None => self.is_std(pkg),
            };
            let in_type_pkg = match type_pkg {
                Some(p) => p == pkg,
                None => self.is_std(pkg),
            };
            if !in_trait_pkg && !in_type_pkg {
                let whose = |p: Option<usize>| match p {
                    Some(p) => format!("`{}`", self.pkgs[p].path),
                    None => "the standard library".to_owned(),
                };
                let decl_ty = ty.decl();
                let shown_ty = if decl_ty.is_decl_form() {
                    super::expr::nominal_name(decl_ty)
                } else {
                    ty.to_string()
                };
                self.diags.push(
                    Diagnostic::error(
                        decl.span_head(),
                        format!(
                            "`impl {tr} for {shown_ty}` must be in the package of `{tr}` ({}) or of `{shown_ty}` ({})",
                            whose(self.trait_pkg(tr)),
                            whose(type_pkg)
                        ),
                    )
                    .with_help("an implementation lives next to its trait or its type, so there's at most one per trait and type (docs/generics.md, Coherence)"),
                );
                continue;
            }
            let decl_ty = ty.decl();
            let def = ImplDef {
                params: params.clone(),
                types: Vec::new(),
                consts: Vec::new(),
            };
            if !crate::types::add_impl(tr, decl_ty, def) {
                let shown = if decl_ty.is_decl_form() {
                    super::expr::nominal_name(decl_ty)
                } else {
                    ty.to_string()
                };
                self.diags.push(
                    Diagnostic::error(
                        decl.span_head(),
                        format!("`{shown}` already implements `{tr}`"),
                    )
                    .with_help("a trait has at most one implementation per type, generic or not"),
                );
                continue;
            }
            if tr == Trait::Ordered && matches!(ty, Ty::Int(_) | Ty::Bool) {
                // Unreachable: the built-in types implement it already.
                continue;
            }
            self.impls[k].head = Some((tr, ty));
            self.impls[k].params = params;
            self.impls[k].bounds = bounds;
            self.impl_items(k);
        }
    }

    /// The type an `impl` is for, with its parameters: a named type (a
    /// struct, an enum, an integer or `bool`), whose parameters, if it's
    /// generic, are the impl's own, each once and in order (`impl[A: Eq, B]
    /// Shape for Pair[A, B]`), as for a method of a generic type.
    #[allow(clippy::type_complexity)]
    fn impl_type(
        &mut self,
        decl: &ast::ImplDecl,
        pkg: usize,
        file: FileId,
    ) -> Option<(Ty, Vec<Ty>, Vec<Vec<Trait>>)> {
        let mut cx = FnCx::new(pkg, file, Ty::Unit, false);
        // `impl[T] Shape for T`: a blanket impl.
        if let TypeExpr::Named(id) = &decl.ty
            && decl.generics.iter().any(|g| g.name.name == id.name)
        {
            self.diags.push(
                Diagnostic::error(
                    id.span,
                    "an `impl` is for a named type, not for a type parameter",
                )
                .with_help(
                    "blanket implementations are not supported (docs/generics.md, Coherence)",
                ),
            );
            return None;
        }
        let (base, written) = match &decl.ty {
            TypeExpr::Generic(base, args, _) => (&**base, Some(args)),
            t => (t, None),
        };
        let base_ty = match base {
            TypeExpr::Named(_) | TypeExpr::Qualified(..) => {
                self.resolve_type_or_decl(&mut cx, base)?
            }
            t => {
                self.diags.push(
                    Diagnostic::error(t.span(), "an `impl` is for a named type")
                        .with_help("a struct, an enum, an integer type or `bool`"),
                );
                return None;
            }
        };
        if !matches!(base_ty, Ty::Struct(_) | Ty::Enum(_) | Ty::Int(_) | Ty::Bool) {
            self.diags.push(
                Diagnostic::error(
                    decl.ty.span(),
                    format!("an `impl` for `{base_ty}` is not supported by the compiler yet"),
                )
                .with_help("an `impl` is for a struct, an enum, an integer type or `bool`"),
            );
            return None;
        }
        let decl_params = base_ty.decl_params();
        if decl_params.is_empty() {
            if let Some(g) = decl.generics.first() {
                self.diags.push(
                    Diagnostic::error(
                        g.name.span,
                        format!("`{base_ty}` is not generic, so the `impl` has no parameters"),
                    )
                    .with_help(format!("write `impl {} for {base_ty}`", decl.trait_.text())),
                );
                return None;
            }
            if written.is_some() {
                self.error(
                    decl.ty.span(),
                    format!("`{base_ty}` is not generic: it takes no arguments"),
                );
                return None;
            }
            return Some((base_ty, Vec::new(), Vec::new()));
        }
        let name = super::expr::nominal_name(base_ty);
        let names: Vec<String> = decl.generics.iter().map(|g| g.name.name.clone()).collect();
        let args_ok = written.is_some_and(|args| {
            args.len() == names.len()
                && args.iter().zip(&names).all(|(a, n)| match a {
                    ast::TypeArg::Expr(e) => matches!(&e.kind, ast::ExprKind::Name(m) if m == n),
                    ast::TypeArg::Type(TypeExpr::Named(id)) => &id.name == n,
                    _ => false,
                })
        });
        if decl.generics.len() != decl_params.len() || !args_ok {
            let params: Vec<String> = decl_params.iter().map(Ty::to_string).collect();
            self.diags.push(
                Diagnostic::error(
                    decl.ty.span(),
                    format!(
                        "an `impl` for the generic type `{name}` declares a parameter for each of its parameters and names them, in order"
                    ),
                )
                .with_help(format!(
                    "write `impl[{p}] {} for {name}[{p}]`, with bounds on the parameters if needed",
                    decl.trait_.text(),
                    p = params.join(", ")
                )),
            );
            return None;
        }
        let (params, bounds) =
            self.declare_owner_generics(&cx, base_ty, &decl.generics, decl.ty.span())?;
        Some((base_ty.instantiate(&params), params, bounds))
    }

    /// Check and register the associated types and constants of impl `k`.
    fn impl_items(&mut self, k: usize) {
        let (decl, pkg, file) = {
            let i = &self.impls[k];
            (i.decl, i.pkg, i.file)
        };
        let (tr, ty) = self.impls[k].head.expect("a resolved impl");
        let def = tr.def();
        let mut cx = FnCx::new(pkg, file, Ty::Unit, false);
        cx.type_params = self.impls[k].params.clone();
        cx.self_ty = Some(ty);
        let mut types: Vec<(String, Ty)> = Vec::new();
        let mut consts: Vec<(String, i128)> = Vec::new();
        for item in &decl.items {
            match item {
                ast::ImplItem::Method(_) => {}
                ast::ImplItem::Type { name, ty: te } => {
                    let declared = def
                        .as_ref()
                        .is_some_and(|d| d.types.iter().any(|a| a.name == name.name));
                    if !declared {
                        self.error(
                            name.span,
                            format!("`{tr}` has no associated type `{}`", name.name),
                        );
                        continue;
                    }
                    if types.iter().any(|(n, _)| *n == name.name) {
                        self.error(name.span, format!("`{}` is given twice", name.name));
                        continue;
                    }
                    let Some(t) = self.resolve_type(&mut cx, te) else {
                        continue;
                    };
                    if self.check_type_arg(t, te.span()).is_none() {
                        continue;
                    }
                    types.push((name.name.clone(), t));
                }
                ast::ImplItem::Const(c) => {
                    let it = def.as_ref().and_then(|d| {
                        d.consts
                            .iter()
                            .find(|(n, _)| *n == c.name.name)
                            .map(|&(_, it)| it)
                    });
                    let Some(it) = it else {
                        self.error(
                            c.name.span,
                            format!("`{tr}` has no associated constant `{}`", c.name.name),
                        );
                        continue;
                    };
                    if consts.iter().any(|(n, _)| *n == c.name.name) {
                        self.error(c.name.span, format!("`{}` is given twice", c.name.name));
                        continue;
                    }
                    if let Some(v) = self.assoc_const_value(&mut cx, c, it) {
                        consts.push((c.name.name.clone(), v));
                    }
                }
            }
        }
        if let Some(d) = &def {
            let missing: Vec<String> = d
                .types
                .iter()
                .map(|a| a.name.clone())
                .filter(|n| !types.iter().any(|(m, _)| m == n))
                .chain(
                    d.consts
                        .iter()
                        .map(|(n, _)| n.clone())
                        .filter(|n| !consts.iter().any(|(m, _)| m == n)),
                )
                .collect();
            for n in missing {
                self.error(
                    decl.span_head(),
                    format!("the `impl` of `{tr}` for `{ty}` doesn't give `{n}`"),
                );
            }
        }
        crate::types::set_impl_items(tr, ty.decl(), types, consts);
    }

    /// The value of an associated constant in an `impl`, of type `it`:
    /// known when compiling.
    fn assoc_const_value(&mut self, cx: &mut FnCx, c: &ast::ConstDecl, it: IntTy) -> Option<i128> {
        if let Some(t) = &c.ty {
            let ty = self.resolve_type(cx, t)?;
            if ty != Ty::Int(it) {
                self.error(
                    t.span(),
                    format!("`{}` is a `{it}` in the trait, not a `{ty}`", c.name.name),
                );
                return None;
            }
        }
        let v = self.expr(cx, &c.value, Some(Ty::Int(it)))?;
        let v = self.coerce(cx, v, Ty::Int(it), c.value.span)?;
        match (&v.expr.kind, v.range) {
            (TExprKind::Int(_), Some(r)) if r.lo == r.hi => Some(r.lo),
            _ => {
                self.error(
                    c.value.span,
                    "the value of an associated constant must be known when compiling",
                );
                None
            }
        }
    }

    /// The signature of a method declared in trait `k`: its first generic
    /// parameter is the trait's `Self`.
    pub(super) fn trait_method_sig(&mut self, f: &ast::FnDecl, k: usize) -> Sig {
        let (pkg, file, self_param, tr) = {
            let t = &self.traits[k];
            (t.pkg, t.file, t.self_param, t.trait_)
        };
        let mut cx = FnCx::new(pkg, file, Ty::Unit, false);
        cx.self_ty = Some(self_param);
        cx.member = Some((vec![self_param], vec![vec![tr]]));
        let mut sig = self.signature(&mut cx, f, Some(self_param));
        sig.name = format!("{tr}.{}", f.name.name);
        sig.is_pub = self.traits[k].decl.is_pub;
        sig.symbol_name = Some(format!("{}.{}", self.traits[k].decl.name.name, f.name.name));
        sig
    }

    /// The signature of a method declared in impl `k`: a method of the
    /// impl's type, whose parameters are the impl's.
    pub(super) fn impl_method_sig(&mut self, f: &ast::FnDecl, k: usize) -> Sig {
        let (pkg, file) = (self.impls[k].pkg, self.impls[k].file);
        let mut cx = FnCx::new(pkg, file, Ty::Unit, false);
        let Some((tr, ty)) = self.impls[k].head else {
            // The header is in error: the body is still checked, with
            // `self` failed.
            cx.member = Some((Vec::new(), Vec::new()));
            let mut sig = self.signature(&mut cx, f, None);
            sig.is_pub = true;
            return sig;
        };
        cx.self_ty = Some(ty);
        cx.member = Some((self.impls[k].params.clone(), self.impls[k].bounds.clone()));
        let mut sig = self.signature(&mut cx, f, Some(ty));
        let decl = ty.decl();
        let shown = if decl.is_decl_form() {
            super::expr::nominal_name(decl)
        } else {
            ty.to_string()
        };
        let bare = shown.rsplit('.').next().unwrap_or(&shown).to_owned();
        sig.name = format!("{shown}.{}", f.name.name);
        sig.is_pub = tr.def().is_none_or(|_| {
            self.trait_index
                .get(&tr)
                .is_none_or(|&t| self.traits[t].decl.is_pub)
        });
        // Its symbol names the trait, after the method: a type may have a
        // method of its own with the same name.
        let trait_sym = match tr.def() {
            Some(d) => format!(
                "{}.{}",
                self.pkgs[d.pkg].path,
                d.name.rsplit('.').next().unwrap_or(&d.name)
            ),
            None => tr.name(),
        };
        sig.symbol_name = Some(format!("{bare}.{}<{trait_sym}>", f.name.name));
        sig
    }

    /// Compare each impl's methods with its trait's, and make them the
    /// type's: the trait's methods each impl doesn't replace are its
    /// defaults. Also checks the supertraits and the associated types'
    /// bounds.
    pub(super) fn check_impls(&mut self) {
        for k in 0..self.impls.len() {
            let Some((tr, ty)) = self.impls[k].head else {
                continue;
            };
            let decl = self.impls[k].decl;
            let head = decl.span_head();
            // The supertraits, with the impl's bounds.
            let supers: Vec<Trait> = match tr {
                Trait::Ordered => vec![Trait::Eq],
                t => t.def().map(|d| d.supers.clone()).unwrap_or_default(),
            };
            for s in supers {
                if !ty.satisfies(s) {
                    let help = match s {
                        Trait::Eq => format!("`{ty}` is `Eq` when its fields are"),
                        Trait::Copy => format!("`{ty}` is `Copy` when its fields are"),
                        s if !self.impls[k].params.is_empty() => format!(
                            "implement `{s}` for it, or add a bound on the impl's parameters"
                        ),
                        s => format!("add `impl {s} for {ty}`"),
                    };
                    self.diags.push(
                        Diagnostic::error(
                            head,
                            format!("`{tr}` requires `{s}`, which `{ty}` doesn't implement"),
                        )
                        .with_help(help),
                    );
                }
            }
            // The associated types' bounds.
            if let Some(d) = tr.def() {
                for a in &d.types {
                    let t = Ty::project(ty, tr, &a.name);
                    if t == Ty::Unit {
                        continue;
                    }
                    for &b in &a.bounds {
                        if !t.satisfies(b) {
                            self.error(
                                head,
                                format!(
                                    "`{}` is `{t}`, which doesn't implement `{b}`, as `{tr}` requires",
                                    a.name
                                ),
                            );
                        }
                    }
                }
            }
            let methods = self.impls[k].methods.clone();
            match tr {
                Trait::Ordered => self.check_ordered_impl(k, ty, &methods),
                Trait::User(_) => self.check_user_impl(k, tr, ty, &methods),
                _ => unreachable!("only `Ordered` and user traits have impls"),
            }
        }
    }

    /// The methods of an `impl Ordered`: `cmp(self, other: Self) ->
    /// Ordering`, and maybe `lt`, `le`, `gt`, `ge` (`-> bool`).
    fn check_ordered_impl(&mut self, k: usize, ty: Ty, methods: &[(String, FuncId)]) {
        let decl = ty.decl();
        let mut table = HashMap::new();
        for (name, id) in methods {
            let want = if name == "cmp" {
                Ty::ordering()
            } else if ORDERED_DEFAULTS.contains(&name.as_str()) {
                Ty::Bool
            } else {
                let span = self.sigs[*id].span;
                self.diags.push(
                    Diagnostic::error(span, format!("`{name}` is not a method of `Ordered`"))
                        .with_help(
                            "`impl Ordered` has `cmp`, and may have `lt`, `le`, `gt` and `ge`",
                        ),
                );
                continue;
            };
            let sig = &self.sigs[*id];
            let ok = sig.has_self
                && sig.params.len() == 2
                && sig.params[0].1 == Convention::Let
                && sig.params[1].1 == Convention::Let
                && sig.params[1].0 == ty
                && sig.ret == want
                && sig.throws.is_none();
            if !ok {
                let span = sig.span;
                self.diags.push(
                    Diagnostic::error(
                        span,
                        format!("`{ty}.{name}` doesn't match `Ordered.{name}`"),
                    )
                    .with_help(format!(
                        "declare it `fn {name}(self, other: Self) -> {want}`"
                    )),
                );
                continue;
            }
            table.insert(name.clone(), *id);
            self.impl_methods
                .entry((decl, name.clone()))
                .or_default()
                .push((Trait::Ordered, *id));
        }
        if !methods.iter().any(|(n, _)| n == "cmp") {
            let head = self.impls[k].decl.span_head();
            self.diags.push(
                Diagnostic::error(
                    head,
                    format!("the `impl` of `Ordered` for `{ty}` has no `cmp`"),
                )
                .with_help("add `fn cmp(self, other: Self) -> Ordering`"),
            );
        }
        self.dispatch.impls.insert((Trait::Ordered, decl), table);
    }

    /// The methods of an impl of a trait declared in Lode.
    fn check_user_impl(&mut self, k: usize, tr: Trait, ty: Ty, methods: &[(String, FuncId)]) {
        let decl = ty.decl();
        let t = self.trait_index[&tr];
        let self_param = self.traits[t].self_param;
        let trait_methods = self.traits[t].methods.clone();
        let map = |p: Ty| (p == self_param).then_some(ty);
        let mut table = HashMap::new();
        for (name, id) in methods {
            let Some(&(_, tid, _)) = trait_methods.iter().find(|(n, ..)| n == name) else {
                let span = self.sigs[*id].span;
                self.diags.push(
                    Diagnostic::error(span, format!("`{name}` is not a method of `{tr}`"))
                        .with_help(format!(
                            "an `impl` has the trait's methods only; declare other methods as `fn {}.{name}(...)`",
                            super::expr::nominal_name(decl)
                        )),
                );
                continue;
            };
            if let Some(why) = self.sig_mismatch(&self.sigs[tid], &self.sigs[*id], &map) {
                let want = sig_text(&self.sigs[tid].name, &self.sigs[tid], &map);
                let span = self.sigs[*id].span;
                self.diags.push(
                    Diagnostic::error(
                        span,
                        format!(
                            "`{}` doesn't match `{tr}.{name}`: {why}",
                            self.sigs[*id].name
                        ),
                    )
                    .with_help(format!("declare it `{want}`")),
                );
                continue;
            }
            table.insert(name.clone(), *id);
            self.impl_methods
                .entry((decl, name.clone()))
                .or_default()
                .push((tr, *id));
            // For the check that instances end: the trait's function may
            // become this one.
            self.generic_calls.push(GenericEdge {
                caller: tid,
                callee: *id,
                args: self.impls[k].params.clone(),
                span: self.sigs[*id].span,
            });
        }
        let mut missing = Vec::new();
        for (name, tid, default) in &trait_methods {
            if methods.iter().any(|(n, _)| n == name) {
                continue;
            }
            if *default {
                self.impl_methods
                    .entry((decl, name.clone()))
                    .or_default()
                    .push((tr, *tid));
            } else {
                missing.push(sig_text(&self.sigs[*tid].name, &self.sigs[*tid], &map));
            }
        }
        for m in missing {
            let head = self.impls[k].decl.span_head();
            let name = m
                .trim_start_matches("fn ")
                .split('(')
                .next()
                .unwrap_or_default()
                .to_owned();
            self.diags.push(
                Diagnostic::error(
                    head,
                    format!("the `impl` of `{tr}` for `{ty}` is missing `{name}`"),
                )
                .with_help(format!("add `{m}`")),
            );
        }
        self.dispatch.impls.insert((tr, decl), table);
    }

    /// Why the signature `imp` of an impl's method doesn't match `want`,
    /// the trait's (with `Self` replaced by `map`): `None` if it does. The
    /// impl may throw nothing where the trait throws.
    fn sig_mismatch(
        &self,
        want: &Sig,
        imp: &Sig,
        map: &impl Fn(Ty) -> Option<Ty>,
    ) -> Option<String> {
        if want.has_self != imp.has_self {
            return Some(if want.has_self {
                "the trait's has `self`".to_owned()
            } else {
                "the trait's has no `self`".to_owned()
            });
        }
        if want.params.len() != imp.params.len() {
            return Some(format!(
                "it takes {} parameter(s), the trait's {}",
                imp.params.len(),
                want.params.len()
            ));
        }
        for ((wt, wc, wn), (it, ic, _)) in want.params.iter().zip(&imp.params) {
            if wc != ic {
                return Some(format!("`{wn}` is passed differently"));
            }
            let wt = wt.subst(map);
            if wt != *it {
                return Some(format!("`{wn}` is a `{wt}` in the trait, not a `{it}`"));
            }
        }
        let ret = want.ret.subst(map);
        if ret != imp.ret {
            return Some(format!("it returns `{}`, the trait's `{ret}`", imp.ret));
        }
        match (want.throws.map(|e| e.subst(map)), imp.throws) {
            (_, None) => {}
            (Some(a), Some(b)) if a == b => {}
            (Some(a), Some(b)) => return Some(format!("it throws `{b}`, the trait's `{a}`")),
            (None, Some(b)) => {
                return Some(format!("it throws `{b}`, and the trait's doesn't throw"));
            }
        }
        if imp.is_unsafe && !want.is_unsafe {
            return Some("it's `unsafe`, and the trait's isn't".to_owned());
        }
        None
    }

    /// The methods (and associated functions) called `name` that the
    /// traits bounding the type parameter `ty` give, with their traits.
    pub(super) fn param_methods(&self, ty: Ty, name: &str) -> Vec<(Trait, FuncId)> {
        let Some(def) = ty.as_param() else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for t in def.bounds.user() {
            let Some(&k) = self.trait_index.get(&t) else {
                continue;
            };
            for (n, id, _) in &self.traits[k].methods {
                if n == name && !out.iter().any(|&(_, f)| f == *id) {
                    out.push((t, *id));
                }
            }
        }
        out
    }

    /// The trait method `name` of `ty` found through its traits: a type
    /// parameter's bounds, or the impls of a struct, an enum or a
    /// primitive. `Some(None)` if there's none; `None` if several traits
    /// give one (reported at `span`, with the qualified form to use).
    pub(super) fn trait_method(
        &mut self,
        ty: Ty,
        name: &str,
        span: Span,
    ) -> Option<Option<FuncId>> {
        let found: Vec<(Trait, FuncId)> = if ty.as_param().is_some() {
            self.param_methods(ty, name)
        } else {
            self.impl_methods
                .get(&(ty.decl(), name.to_owned()))
                .cloned()
                .unwrap_or_default()
        };
        match found.as_slice() {
            [] => Some(None),
            [(_, id)] => Some(Some(*id)),
            several => {
                let traits: Vec<String> = several.iter().map(|(t, _)| format!("`{t}`")).collect();
                let first = several[0].0;
                self.diags.push(
                    Diagnostic::error(
                        span,
                        format!(
                            "`{name}` of `{ty}` is ambiguous: {} each have one",
                            traits.join(" and ")
                        ),
                    )
                    .with_help(format!(
                        "call it through its trait: `{first}.{name}(x, ...)`"
                    )),
                );
                None
            }
        }
    }

    /// The method `name` of trait `t`, called as `Trait.name(...)`.
    pub(super) fn trait_fn(&self, t: Trait, name: &str) -> Option<FuncId> {
        let k = *self.trait_index.get(&t)?;
        self.traits[k]
            .methods
            .iter()
            .find(|(n, ..)| n == name)
            .map(|&(_, id, _)| id)
    }

    /// Whether `id` is a method declared in a trait (whose first generic
    /// argument is `Self`).
    pub(super) fn is_trait_fn(&self, id: FuncId) -> bool {
        self.dispatch.trait_fns.contains_key(&id)
    }

    /// The trait an expression names, as in `Shape.area(p)` or
    /// `io.Writer.write(&f, s)`: a trait of the package, a public one of an
    /// imported package, or a built-in one.
    pub(super) fn names_trait(&self, cx: &FnCx, e: &ast::Expr) -> Option<Trait> {
        match &e.kind {
            ast::ExprKind::Name(n) if cx.lookup(n).is_none() => {
                match self.pkgs[cx.pkg].items.get(n) {
                    Some(&Item::Trait(t)) => Some(t),
                    Some(_) => None,
                    None => Trait::from_name(n),
                }
            }
            ast::ExprKind::Field(base, member) => match &base.kind {
                ast::ExprKind::Name(p) => {
                    let pkg = self.imported(cx, p)?;
                    match self.pkgs[pkg].items.get(&member.name) {
                        Some(&Item::Trait(t))
                            if pkg == cx.pkg || self.traits[self.trait_index[&t]].decl.is_pub =>
                        {
                            Some(t)
                        }
                        _ => None,
                    }
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// The type `name` names as the base of `name.Item` (an associated type
    /// or constant): `Self`, a type parameter, or a type of the package,
    /// unless an imported package has the name.
    pub(super) fn type_base(&self, cx: &FnCx, name: &str) -> Option<Ty> {
        if cx.lookup(name).is_some() {
            return None;
        }
        if name == super::SELF {
            return cx.self_ty;
        }
        if let Some(p) = Self::type_param(cx, name) {
            return p.value_param().is_none().then_some(p);
        }
        if self.imported(cx, name).is_some() {
            return None;
        }
        match self.pkgs[cx.pkg].items.get(name) {
            Some(&Item::Type(ty)) if !ty.is_decl_form() => Some(ty),
            _ => None,
        }
    }

    /// The associated type or constant `name` of `base` (a type parameter,
    /// `Self`, or a type with impls): the trait declaring it, if exactly
    /// one of `base`'s traits does. `Err(())` if none does or several do
    /// (not reported).
    pub(super) fn assoc_trait(&self, base: Ty, name: &str) -> Result<Trait, Vec<Trait>> {
        let has = |t: Trait| {
            t.def().is_some_and(|d| {
                d.types.iter().any(|a| a.name == name) || d.consts.iter().any(|(n, _)| n == name)
            })
        };
        let found: Vec<Trait> = match base.as_param() {
            Some(def) => def.bounds.user().into_iter().filter(|&t| has(t)).collect(),
            None => self
                .traits
                .iter()
                .map(|t| t.trait_)
                .filter(|&t| has(t) && crate::types::find_impl(t, base).is_some())
                .collect(),
        };
        match found.as_slice() {
            [t] => Ok(*t),
            _ => Err(found),
        }
    }

    /// `base.name` in a type (`E.Rune`, `Self.Rune`, `Utf8.Rune`): the
    /// associated type `name` of `base` (reported if it has none).
    pub(super) fn assoc_type(&mut self, base: Ty, name: &ast::Ident) -> Option<Ty> {
        match self.assoc_trait(base, &name.name) {
            Ok(t)
                if t.def()
                    .is_some_and(|d| d.types.iter().any(|a| a.name == name.name)) =>
            {
                let ty = Ty::project(base, t, &name.name);
                (ty != Ty::Unit).then_some(ty)
            }
            Ok(_) => {
                self.error(
                    name.span,
                    format!("`{base}.{}` is a constant, not a type", name.name),
                );
                None
            }
            Err(found) => {
                self.assoc_error(base, name, &found);
                None
            }
        }
    }

    /// Report `base.name`, which isn't one associated item of `base`.
    pub(super) fn assoc_error(&mut self, base: Ty, name: &ast::Ident, found: &[Trait]) {
        if found.is_empty() {
            let mut d = Diagnostic::error(
                name.span,
                format!(
                    "`{base}` has no associated type or constant `{}`",
                    name.name
                ),
            );
            if base.as_param().is_some() {
                d = d.with_help(format!(
                    "a type parameter has the associated items of its bounds: `[{base}: Trait]`"
                ));
            }
            self.diags.push(d);
        } else {
            let names: Vec<String> = found.iter().map(|t| format!("`{t}`")).collect();
            self.error(
                name.span,
                format!(
                    "`{base}.{}` is ambiguous: {} each declare one",
                    name.name,
                    names.join(" and ")
                ),
            );
        }
    }

    /// `base.name` in an expression or an array length: the associated
    /// constant `name` of `base`, as a type: a value parameter standing for
    /// it, or the value an impl gives it. `None` if `base` has none (not
    /// reported).
    pub(super) fn assoc_const(&self, base: Ty, name: &str) -> Option<(Ty, IntTy)> {
        let t = self.assoc_trait(base, name).ok()?;
        let it = t
            .def()?
            .consts
            .iter()
            .find(|(n, _)| n == name)
            .map(|&(_, it)| it)?;
        let ty = Ty::project(base, t, name);
        (ty != Ty::Unit).then_some((ty, it))
    }

    /// The value parameters standing for the associated constants of the
    /// type parameters `params` (`E.MAX_LEN` for `E: Encoding`): a body
    /// holds each in a local, which an instance assigns first.
    pub(super) fn assoc_value_params(&self, params: &[Ty]) -> Vec<(Ty, IntTy)> {
        let mut out = Vec::new();
        for &p in params {
            let Some(def) = p.as_param() else {
                continue;
            };
            if def.value.is_some() {
                continue;
            }
            for t in def.bounds.user() {
                for (name, it) in t.def().map(|d| d.consts.clone()).unwrap_or_default() {
                    let ty = Ty::project(p, t, &name);
                    if ty != Ty::Unit && !out.iter().any(|&(q, _)| q == ty) {
                        out.push((ty, it));
                    }
                }
            }
        }
        out
    }
}

impl ast::ImplDecl {
    /// Where messages about the whole `impl` point: its header, `impl
    /// Trait for Type`.
    pub fn span_head(&self) -> Span {
        Span {
            end: self.ty.span().end,
            ..self.span
        }
    }
}

impl Dispatch {
    /// The function a call of `f` with the type arguments `types` (all
    /// concrete) runs, and its type arguments: for a method declared in a
    /// trait, the method of `Self`'s impl if it gives one, or else the
    /// trait's default. Any other function is itself.
    pub fn resolve(&self, f: FuncId, types: &[Ty]) -> (FuncId, Vec<Ty>) {
        let Some((t, name)) = self.trait_fns.get(&f) else {
            return (f, types.to_vec());
        };
        let self_ty = types[0];
        match self
            .impls
            .get(&(*t, self_ty.decl()))
            .and_then(|m| m.get(name))
        {
            Some(&g) => (g, self_ty.type_args().to_vec()),
            None => (f, types.to_vec()),
        }
    }

    /// For `a.cmp(b)` or `a.lt(b)` (`method`) on a struct or an enum `ty`
    /// that implements `Ordered`: the impl's method of that name and its
    /// type arguments, and whether it's `cmp` standing in for the method
    /// (the result is then compared with `.equal`).
    pub fn ordered(&self, ty: Ty, method: &str) -> Option<(FuncId, Vec<Ty>, bool)> {
        let table = self.impls.get(&(Trait::Ordered, ty.decl()))?;
        let args = ty.type_args().to_vec();
        if let Some(&f) = table.get(method) {
            return Some((f, args, false));
        }
        table.get("cmp").map(|&f| (f, args, true))
    }

    /// `e`, if it's `a.cmp(b)` or `a.lt(b)` (and the like) of two values of
    /// a struct or an enum `ty` (a concrete type) that implements
    /// `Ordered`, as a call of the impl's method: of `cmp`, compared with
    /// `.less` or `.greater`, where the impl doesn't give the method. The
    /// operands are evaluated once, in order, as before.
    pub fn ordered_expr(&self, e: &TExpr, ty: Ty) -> Option<TExpr> {
        if !matches!(ty, Ty::Struct(_) | Ty::Enum(_)) {
            return None;
        }
        let (method, a, b) = match &e.kind {
            TExprKind::Compare(a, b) => ("cmp", a, b),
            TExprKind::Binary(TBinOp::Cmp(op), a, b) => match op {
                CmpOp::Lt => ("lt", a, b),
                CmpOp::Le => ("le", a, b),
                CmpOp::Gt => ("gt", a, b),
                CmpOp::Ge => ("ge", a, b),
                CmpOp::Eq | CmpOp::Ne => return None,
            },
            _ => return None,
        };
        let (f, args, via_cmp) = self.ordered(ty, method)?;
        let operands = vec![(**a).clone(), (**b).clone()];
        let call = |ret: Ty| TExpr {
            kind: if args.is_empty() {
                TExprKind::Call(f, operands.clone())
            } else {
                TExprKind::GenericCall(f, args.clone(), operands.clone())
            },
            ty: ret,
        };
        if !via_cmp {
            return Some(call(e.ty));
        }
        // `Ordering`'s variants: `less`, `equal`, `greater`.
        let ordering = Ty::ordering();
        let (cmp, k) = match method {
            "lt" => (CmpOp::Eq, 0),
            "le" => (CmpOp::Ne, 2),
            "gt" => (CmpOp::Eq, 2),
            _ => (CmpOp::Ne, 0),
        };
        Some(TExpr {
            kind: TExprKind::Binary(
                TBinOp::Cmp(cmp),
                Box::new(call(ordering)),
                Box::new(TExpr {
                    kind: TExprKind::Variant(k, Vec::new()),
                    ty: ordering,
                }),
            ),
            ty: Ty::Bool,
        })
    }
}
