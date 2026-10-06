//! Instantiation: the concrete functions a program reaches, from `main`.
//!
//! The checker gives one typed body per function; a generic function's body
//! mentions its type parameters ([`Ty::Param`]). This pass walks the call
//! graph from `main` and makes an instance of each function for each set of
//! type arguments it's called with, its types substituted and its calls
//! pointing at instances (docs/generics.md, Dispatch). A function that isn't
//! generic has one instance. Lowering emits the instances, and only the
//! string literals and array constants they use, so code nothing calls
//! costs nothing in the executable. Every function is still checked: an
//! error in code nothing calls fails the build like any other.
//!
//! A call (`TExprKind::Call`, or `TExprKind::GenericCall` with type
//! arguments) is the only way to refer to a function today; a method call
//! is one too, with the receiver as its first argument. The walk goes
//! through every expression, including the places passed with `&`
//! (`TExprKind::Ref`), whose indexes can call functions.
//!
//! An instance's symbol is its function's, followed by its type arguments:
//! `std/math.max[u32]`, `main.first[main.Point]`; for a method of a
//! generic type, the type's arguments follow the type's name:
//! `std/buf.StackBuf[64].push`, `main.Pair[u8, bool].swap`. A value
//! parameter's local is assigned its value at the start of the body. The
//! checker makes sure the instances are finitely many (`sema`'s check of
//! generic recursion).
//!
//! Destruction (docs/allocation.md, Generics): where an instance destroys
//! a value of a type that needs destruction (a `TStmt::Drop` of a local, a
//! `TStmt::Destroy`, an assignment that replaces a value), the destruction
//! of that type is reached too: its `deinit`'s instance, or else a function
//! made here that destroys its parts (`main.Pair[main.Fd, u8].$destroy`):
//! a struct's fields in reverse order, the payload of an enum's variant, an
//! array's elements in order. For a type that needs none (an instance of
//! generic code for plain data), the checker's moves, temporaries and
//! destructions are removed, so the code is the same as without them.

use std::collections::HashMap;

use crate::sema::{
    Convention, Func, FuncId, Handler, Local, Program, TArm, TExpr, TExprKind, TStmt,
    stmt_blocks_mut, stmt_exprs_mut, subexprs_mut,
};
use crate::source::Span;
use crate::types::{IntTy, Ty};

/// The concrete functions of a program, reached from its root.
#[derive(Debug)]
pub struct Instances {
    /// Every instance reached, in the order of their functions in the
    /// program.
    pub funcs: Vec<Func>,
    /// The instance of `main`, if the program has one.
    pub main: Option<FuncId>,
    /// `strings[i]`: whether an instance uses string literal `i`.
    pub strings: Vec<bool>,
    /// `tables[i]`: whether an instance uses array constant `i`.
    pub tables: Vec<bool>,
    /// Whether an instance calls `main` (`main` is recursive).
    pub root_called: bool,
    /// The function that destroys a value of each type that needs
    /// destruction and is destroyed somewhere: its `deinit`'s instance, or
    /// one made here. It takes the value's address.
    pub destroy: HashMap<Ty, FuncId>,
}

/// The instances `main` reaches. A program without `main` (a library:
/// `--emit=ir` shows all of its code) reaches every function that isn't
/// generic, and the instances they call.
pub fn instantiate(program: &Program) -> Instances {
    let mut m = Mono {
        program,
        ids: HashMap::new(),
        work: Vec::new(),
        funcs: Vec::new(),
        strings: vec![false; program.strings.len()],
        tables: vec![false; program.tables.len()],
        root: None,
        root_called: false,
        destroy: HashMap::new(),
        clones: HashMap::new(),
        made: Vec::new(),
        span: program.funcs.first().map(|f| f.span).unwrap_or_default(),
    };
    let main = match program.main {
        Some(main) => {
            let id = m.instance(main, Vec::new());
            m.root = Some(id);
            Some(id)
        }
        None => {
            for (i, f) in program.funcs.iter().enumerate() {
                if f.type_params.is_empty() && !f.template {
                    m.instance(i, Vec::new());
                }
            }
            None
        }
    };
    let mut origin = vec![0; m.funcs.len()];
    while let Some((orig, args, throws, id)) = m.work.pop() {
        let mut f = m.make(orig, &args);
        // A call through a trait whose method throws expects a result: the
        // impl's method that doesn't throw is made to, never throwing.
        if let Some(err) = throws {
            f.throws = Some(err);
            f.symbol.push_str("<throws>");
        }
        origin.resize(m.funcs.len(), 0);
        origin[id] = orig;
        m.funcs[id] = Some(f);
    }
    // The destructions made here come last.
    origin.resize(m.funcs.len(), 0);
    for &id in &m.made {
        origin[id] = program.funcs.len();
    }
    // The instances in the order of their functions in the program (and of
    // their making, for one function's), so the code's layout doesn't
    // depend on the order calls are found in.
    let mut order: Vec<FuncId> = (0..m.funcs.len()).collect();
    order.sort_by_key(|&i| (origin[i], i));
    let mut new_id = vec![0; order.len()];
    for (k, &i) in order.iter().enumerate() {
        new_id[i] = k;
    }
    let mut funcs: Vec<Option<Func>> = m.funcs;
    let mut sorted: Vec<Func> = order
        .iter()
        .map(|&i| funcs[i].take().expect("every instance is made"))
        .collect();
    for f in &mut sorted {
        for s in &mut f.body {
            renumber_stmt(s, &new_id);
        }
    }
    Instances {
        funcs: sorted,
        main: main.map(|id| new_id[id]),
        strings: m.strings,
        tables: m.tables,
        root_called: m.root_called,
        destroy: m
            .destroy
            .into_iter()
            .map(|(ty, id)| (ty, new_id[id]))
            .collect(),
    }
}

/// Point the calls in `s` at the instances' new ids.
fn renumber_stmt(s: &mut TStmt, new_id: &[FuncId]) {
    for e in stmt_exprs_mut(s) {
        renumber_expr(e, new_id);
    }
    for block in stmt_blocks_mut(s) {
        for s in block {
            renumber_stmt(s, new_id);
        }
    }
}

fn renumber_expr(e: &mut TExpr, new_id: &[FuncId]) {
    match &mut e.kind {
        TExprKind::Call(f, _) => *f = new_id[*f],
        TExprKind::Catch {
            handler: Handler::Block(body),
            ..
        } => {
            for s in body {
                renumber_stmt(s, new_id);
            }
        }
        _ => {}
    }
    for sub in subexprs_mut(e) {
        renumber_expr(sub, new_id);
    }
}

struct Mono<'p> {
    program: &'p Program,
    /// The instance of each function and type arguments made so far, and
    /// the error type it throws when it's an impl's method that doesn't
    /// throw, called through a trait's that does.
    ids: HashMap<(FuncId, Vec<Ty>, Option<Ty>), FuncId>,
    /// The instances to make: the function, its type arguments, the error
    /// type it's made to throw, and the instance's id.
    work: Vec<(FuncId, Vec<Ty>, Option<Ty>, FuncId)>,
    funcs: Vec<Option<Func>>,
    strings: Vec<bool>,
    tables: Vec<bool>,
    root: Option<FuncId>,
    root_called: bool,
    /// The destruction of each type, as in [`Instances::destroy`].
    destroy: HashMap<Ty, FuncId>,
    /// The clones made here, by type (see [`Mono::clone_fn`]).
    clones: HashMap<Ty, FuncId>,
    /// The destructions and clones made here (see [`Mono::destroy_fn`]).
    made: Vec<FuncId>,
    /// The span of the function being made, for the destructions it
    /// makes (their debug information).
    span: Span,
}

impl Mono<'_> {
    /// The id of the instance of function `f` with the type arguments
    /// `args` (concrete types), made later if it's new.
    fn instance(&mut self, f: FuncId, args: Vec<Ty>) -> FuncId {
        self.instance_throwing(f, args, None)
    }

    /// [`Mono::instance`], made to throw `throws` if it's given.
    fn instance_throwing(&mut self, f: FuncId, args: Vec<Ty>, throws: Option<Ty>) -> FuncId {
        let key = (f, args, throws);
        if let Some(&id) = self.ids.get(&key) {
            return id;
        }
        let id = self.funcs.len();
        self.funcs.push(None);
        self.ids.insert(key.clone(), id);
        self.work.push((key.0, key.1, key.2, id));
        id
    }

    /// The instance of function `orig` for the type arguments `args`.
    fn make(&mut self, orig: FuncId, args: &[Ty]) -> Func {
        let f = &self.program.funcs[orig];
        debug_assert_eq!(f.type_params.len(), args.len());
        let params = f.type_params.clone();
        let map = |t: Ty| params.iter().position(|&p| p == t).map(|k| args[k]);
        let names = |args: &[Ty]| -> String {
            let names: Vec<String> = args.iter().map(|&a| self.type_symbol(a)).collect();
            names.join(", ")
        };
        // A method of a generic type has the type's arguments after the
        // type's name: `std/buf.StackBuf[64].push`.
        // A method of an `impl` names its trait after the method:
        // `main.Pair[u8].cmp<Ordered>`.
        let (owner, own) = args.split_at(f.owner_params);
        let mut symbol = f.symbol.clone();
        let (base, suffix) = match f.symbol.find('<') {
            Some(k) => f.symbol.split_at(k),
            None => (f.symbol.as_str(), ""),
        };
        if !owner.is_empty()
            && let Some((ty, method)) = base.rsplit_once('.')
        {
            symbol = format!("{ty}[{}].{method}{suffix}", names(owner));
        }
        if !own.is_empty() {
            symbol = format!("{symbol}[{}]", names(own));
        }
        let locals: Vec<Local> = f
            .locals
            .iter()
            .map(|l| Local {
                name: l.name.clone(),
                ty: l.ty.subst(&map),
                mutable: l.mutable,
                convention: l.convention,
                drop_flag: l.drop_flag,
            })
            .collect();
        // Each value parameter's local starts with its value.
        let mut body: Vec<TStmt> = f
            .value_params
            .iter()
            .map(|&(p, local)| {
                let ty = f.locals[local].ty;
                // A value parameter, or an associated constant of a type
                // parameter (`E.MAX_LEN`), which the type argument's impl
                // gives.
                let v = p
                    .subst(&map)
                    .as_value()
                    .expect("a value argument for each value parameter");
                TStmt::Init(
                    local,
                    TExpr {
                        kind: TExprKind::Int(v),
                        ty,
                    },
                )
            })
            .collect();
        body.extend(f.body.iter().cloned());
        self.span = f.span;
        self.block(&mut body, &map, &locals);
        Func {
            name: f.name.clone(),
            symbol,
            type_params: Vec::new(),
            owner_params: 0,
            value_params: Vec::new(),
            params: f.params.clone(),
            ret: f.ret.subst(&map),
            throws: f.throws.map(|t| t.subst(&map)),
            locals,
            body,
            span: f.span,
            template: false,
        }
    }

    /// A statement list: what it destroys of types that need no
    /// destruction is removed, the rest is made concrete.
    fn block(&mut self, stmts: &mut Vec<TStmt>, map: &impl Fn(Ty) -> Option<Ty>, locals: &[Local]) {
        stmts.retain(|s| match s {
            TStmt::Drop { local, .. } => locals[*local].ty.needs_destroy(),
            TStmt::Destroy(place) => place.ty.subst(map).needs_destroy(),
            _ => true,
        });
        for s in stmts {
            self.stmt(s, map, locals);
        }
    }

    fn stmt(&mut self, s: &mut TStmt, map: &impl Fn(Ty) -> Option<Ty>, locals: &[Local]) {
        for e in stmt_exprs_mut(s) {
            self.expr(e, map, locals);
        }
        // What the statement destroys.
        let destroyed = match s {
            TStmt::Drop { local, .. } | TStmt::Assign(local, _) => Some(locals[*local].ty),
            TStmt::Destroy(place) | TStmt::Store(place, _) => Some(place.ty),
            _ => None,
        };
        if let Some(ty) = destroyed
            && ty.needs_destroy()
        {
            self.destroy_fn(ty);
        }
        for block in stmt_blocks_mut(s) {
            self.block(block, map, locals);
        }
    }

    /// The function that destroys a value of type `ty` (concrete, and
    /// needing destruction): its `deinit`'s instance, or one made here
    /// that destroys its parts.
    fn destroy_fn(&mut self, ty: Ty) -> FuncId {
        if let Some(&id) = self.destroy.get(&ty) {
            return id;
        }
        if ty.has_deinit() {
            let f = self.program.deinits[&ty.decl()];
            let id = self.instance(f, ty.type_args().to_vec());
            self.destroy.insert(ty, id);
            return id;
        }
        let id = self.funcs.len();
        self.funcs.push(None);
        self.destroy.insert(ty, id);
        self.made.push(id);
        let mut f = destroy_parts(ty, format!("{}.$destroy", self.type_symbol(ty)), self.span);
        let locals = f.locals.clone();
        self.block(&mut f.body, &|_| None, &locals);
        self.funcs[id] = Some(f);
        id
    }

    /// The function that clones a value of type `ty`, a struct, an enum,
    /// an optional or an array without a `deinit` or an `impl Clone` of its
    /// own, whose parts are `Clone`: made here, it clones each part.
    fn clone_fn(&mut self, ty: Ty) -> FuncId {
        if let Some(&id) = self.clones.get(&ty) {
            return id;
        }
        let id = self.funcs.len();
        self.funcs.push(None);
        self.clones.insert(ty, id);
        self.made.push(id);
        let mut f = clone_parts(ty, format!("{}.$clone", self.type_symbol(ty)), self.span);
        let locals = f.locals.clone();
        self.block(&mut f.body, &|_| None, &locals);
        self.funcs[id] = Some(f);
        id
    }

    fn expr(&mut self, e: &mut TExpr, map: &impl Fn(Ty) -> Option<Ty>, locals: &[Local]) {
        e.ty = e.ty.subst(map);
        // A move or a temporary of a type that needs no destruction is its
        // value.
        while let TExprKind::Move(inner, _) | TExprKind::Temp(_, inner) = &mut e.kind
            && !e.ty.needs_destroy()
        {
            let inner = std::mem::replace(
                &mut **inner,
                TExpr {
                    kind: TExprKind::Bool(false),
                    ty: Ty::Bool,
                },
            );
            *e = inner;
            e.ty = e.ty.subst(map);
        }
        if let TExprKind::Temp(local, _) = e.kind {
            self.destroy_fn(locals[local].ty);
        }
        if let TExprKind::NeedsDeinit(t) = e.kind {
            e.kind = TExprKind::Bool(t.subst(map).needs_destroy());
        }
        // `a.lt(b)` of a type that implements `Ordered` with an `impl`.
        if let TExprKind::Compare(a, _) | TExprKind::Binary(_, a, _) = &e.kind
            && let Some(call) = self.program.dispatch.ordered_expr(e, a.ty.subst(map))
        {
            *e = call;
        }
        match &mut e.kind {
            TExprKind::GenericCall(f, types, args) => {
                let types: Vec<Ty> = types.iter().map(|t| t.subst(map)).collect();
                // A trait's method runs the method of `Self`'s impl.
                let (g, types) = self.program.dispatch.resolve(*f, &types);
                let throws = match (e.ty.as_result(), &self.program.funcs[g].throws) {
                    (Some((_, err)), None) if g != *f => Some(err),
                    _ => None,
                };
                let id = self.instance_throwing(g, types, throws);
                self.root_called |= Some(id) == self.root;
                e.kind = TExprKind::Call(id, std::mem::take(args));
            }
            TExprKind::Call(f, _) => {
                *f = self.instance(*f, Vec::new());
                self.root_called |= Some(*f) == self.root;
            }
            TExprKind::Str(id) => self.strings[*id] = true,
            TExprKind::Table(id) => self.tables[*id] = true,
            TExprKind::Catch {
                handler: Handler::Block(body),
                ..
            } => self.block(body, map, locals),
            _ => {}
        }
        // `x.clone()`: the copy, or a call of the type's `clone`.
        if let TExprKind::Clone(inner) = &mut e.kind {
            let inner = std::mem::replace(
                &mut **inner,
                TExpr {
                    kind: TExprKind::Bool(false),
                    ty: Ty::Bool,
                },
            );
            let ty = e.ty;
            if ty.is_copy() {
                *e = inner;
                self.expr(e, map, locals);
                return;
            }
            let f = match self.program.dispatch.clone_impl(ty) {
                Some(f) => self.instance(f, ty.type_args().to_vec()),
                None => self.clone_fn(ty),
            };
            *e = TExpr {
                kind: TExprKind::Call(f, vec![inner]),
                ty,
            };
        }
        for sub in subexprs_mut(e) {
            self.expr(sub, map, locals);
        }
    }

    /// How a type argument is written in a symbol: as in the source, with
    /// a struct or an enum named by its package's path (`main.Point`,
    /// `std/os.Error`), so two packages' types never share a symbol.
    fn type_symbol(&self, ty: Ty) -> String {
        let declared = |pkg: usize, shown: &str| {
            let bare = shown.rsplit('.').next().unwrap_or(shown);
            match self.program.packages.get(pkg) {
                Some(path) => format!("{path}.{bare}"),
                None => bare.to_owned(),
            }
        };
        let with_args = |name: String, args: &[Ty]| {
            if args.is_empty() {
                return name;
            }
            let args: Vec<String> = args.iter().map(|&a| self.type_symbol(a)).collect();
            format!("{name}[{}]", args.join(", "))
        };
        if let Some(def) = ty.as_struct() {
            return with_args(declared(def.pkg, &def.name), &def.args);
        }
        if let Some(def) = ty.as_enum() {
            return with_args(declared(def.pkg, &def.name), &def.args);
        }
        if let Some((elem, n)) = ty.as_array() {
            return format!("[{n}]{}", self.type_symbol(elem));
        }
        if let Some(inner) = ty.as_optional() {
            return format!("?{}", self.type_symbol(inner));
        }
        ty.to_string()
    }
}

/// A function that destroys the parts of a value of type `ty`, which has
/// no `deinit` (see [`Mono::destroy_fn`]): it takes the value `inout`, and
/// destroys each part that needs destruction.
fn destroy_parts(ty: Ty, symbol: String, span: Span) -> Func {
    let usize_ty = Ty::Int(IntTy {
        signed: false,
        bits: 64,
        size: true,
    });
    let mut locals = vec![Local {
        name: "self".to_owned(),
        ty,
        mutable: true,
        convention: Some(Convention::Inout),
        drop_flag: false,
    }];
    let this = TExpr {
        kind: TExprKind::Local(0),
        ty,
    };
    let destroy = |kind: TExprKind, ty: Ty| TStmt::Destroy(TExpr { kind, ty });
    let body = if let Some((elem, n)) = ty.as_known_array() {
        locals.push(Local {
            name: "$i".to_owned(),
            ty: usize_ty,
            mutable: false,
            convention: None,
            drop_flag: false,
        });
        let int = |v: u64| TExpr {
            kind: TExprKind::Int(i128::from(v)),
            ty: usize_ty,
        };
        let index = TExpr {
            kind: TExprKind::Local(1),
            ty: usize_ty,
        };
        vec![TStmt::For {
            var: 1,
            start: int(0),
            end: int(n),
            body: vec![destroy(
                TExprKind::Index(Box::new(this), Box::new(index)),
                elem,
            )],
        }]
    } else if let Some(def) = ty.as_struct() {
        (0..def.fields.len())
            .rev()
            .filter(|&k| def.fields[k].ty.needs_destroy())
            .map(|k| {
                destroy(
                    TExprKind::Field(Box::new(this.clone()), k as u32),
                    def.fields[k].ty,
                )
            })
            .collect()
    } else {
        let def = ty
            .sum()
            .expect("a struct, an enum, an optional, a result or an array");
        let arms = def
            .variants
            .iter()
            .enumerate()
            .map(|(v, variant)| TArm {
                variants: vec![v as u32],
                body: (0..variant.fields.len())
                    .rev()
                    .filter(|&k| variant.fields[k].ty.needs_destroy())
                    .map(|k| {
                        destroy(
                            TExprKind::Payload(Box::new(this.clone()), v as u32, k as u32),
                            variant.fields[k].ty,
                        )
                    })
                    .collect(),
            })
            .collect();
        vec![TStmt::Match { value: this, arms }]
    };
    Func {
        name: format!("{ty}.$destroy"),
        symbol,
        type_params: Vec::new(),
        owner_params: 0,
        value_params: Vec::new(),
        params: vec![0],
        ret: Ty::Unit,
        throws: None,
        locals,
        body,
        span,
        template: false,
    }
}

/// A function that clones a value of type `ty` part by part (see
/// [`Mono::clone_fn`]): it takes the value read-only, and returns a struct
/// literal, a variant or an array literal of its parts' clones.
fn clone_parts(ty: Ty, symbol: String, span: Span) -> Func {
    let locals = vec![Local {
        name: "self".to_owned(),
        ty,
        mutable: false,
        convention: Some(Convention::Let),
        drop_flag: false,
    }];
    let this = TExpr {
        kind: TExprKind::Local(0),
        ty,
    };
    let clone = |kind: TExprKind, ty: Ty| TExpr {
        kind: TExprKind::Clone(Box::new(TExpr { kind, ty })),
        ty,
    };
    let value = |kind: TExprKind| TStmt::Return(Some(TExpr { kind, ty }));
    let body = if let Some((elem, n)) = ty.as_known_array() {
        let usize_ty = Ty::Int(IntTy {
            signed: false,
            bits: 64,
            size: true,
        });
        let elems = (0..n)
            .map(|k| {
                let index = TExpr {
                    kind: TExprKind::Int(i128::from(k)),
                    ty: usize_ty,
                };
                clone(
                    TExprKind::Index(Box::new(this.clone()), Box::new(index)),
                    elem,
                )
            })
            .collect();
        vec![value(TExprKind::ArrayLit(elems))]
    } else if let Some(def) = ty.as_struct() {
        let fields = def
            .fields
            .iter()
            .enumerate()
            .map(|(k, f)| {
                (
                    k as u32,
                    clone(TExprKind::Field(Box::new(this.clone()), k as u32), f.ty),
                )
            })
            .collect();
        vec![value(TExprKind::StructLit(fields))]
    } else {
        let def = ty
            .sum()
            .expect("a struct, an enum, an optional or an array");
        let arms = def
            .variants
            .iter()
            .enumerate()
            .map(|(v, variant)| {
                let payload = variant
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(k, f)| {
                        clone(
                            TExprKind::Payload(Box::new(this.clone()), v as u32, k as u32),
                            f.ty,
                        )
                    })
                    .collect();
                TArm {
                    variants: vec![v as u32],
                    body: vec![value(TExprKind::Variant(v as u32, payload))],
                }
            })
            .collect();
        vec![TStmt::Match { value: this, arms }]
    };
    Func {
        name: format!("{ty}.$clone"),
        symbol,
        type_params: Vec::new(),
        owner_params: 0,
        value_params: Vec::new(),
        params: vec![0],
        ret: ty,
        throws: None,
        locals,
        body,
        span,
        template: false,
    }
}
