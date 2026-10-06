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
//!
//! The destruction of a chain of boxes, a struct with a field `next:
//! ?Box[Self]` (docs/allocation.md, Destroying recursive structures), is a
//! loop: it takes `next`, takes the node out of its box (freeing the box),
//! destroys the node's other fields, and goes on with the node's `next`.
//! Its stack doesn't grow with the chain.
//!
//! The allocator context (docs/allocation.md, Lowering the context): the
//! program's allocator types are the root's (`alloc.ROOT`'s), first, and
//! each type an `alloc.handle(a)` the program reaches makes a handle of.
//! A call through a handle (`h.alloc(...)`, `h.resize(...)`, `h.free(...)`)
//! is a call of a function made here (`std/alloc.Handle.$alloc`) that
//! calls the method of the handle's allocator type: a test of the handle's
//! number, one direct call per type (closed-world dispatch, no function
//! pointers). With only the root, it calls the root's method, and handles
//! hold nothing; a call through `alloc.root()` calls it directly.

use std::collections::HashMap;

use crate::sema::{
    AllocInfo, CmpOp, Convention, Func, FuncId, Handler, Intrinsic, Local, Program, TArm, TBinOp,
    TExpr, TExprKind, TStmt, stmt_blocks_mut, stmt_exprs_mut, subexprs_mut,
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
    /// `statics[i]`: whether an instance uses `static` `i`.
    pub statics: Vec<bool>,
    /// The program's allocator types, the root's first (empty for a
    /// program that never allocates). A handle's number is the index of
    /// its allocator's type here; with only the root, handles are
    /// zero-sized and `uses alloc` functions take no hidden parameter.
    pub allocators: Vec<Ty>,
}

impl Instances {
    /// Whether the allocator context is passed at run time: the program
    /// has allocator types besides the root's (docs/allocation.md,
    /// Lowering the context).
    pub fn dynamic_alloc(&self) -> bool {
        self.allocators.len() > 1
    }
}

/// The methods of the `Allocator` trait, in the order of a handle's
/// intrinsics (`HandleAlloc`, `HandleResize`, `HandleFree`).
const ALLOC_METHODS: [&str; 3] = ["alloc", "resize", "free"];

/// The allocator context, while instances are made.
struct AllocState {
    info: AllocInfo,
    /// The allocator types reached, the root's first, each with the
    /// instances of the methods the dispatch functions call, once made.
    types: Vec<(Ty, [Option<FuncId>; 3])>,
    /// The dispatch function of each method, once a call needs it.
    dispatch: [Option<FuncId>; 3],
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
        statics: vec![false; program.statics.len()],
        alloc: program.alloc.map(|info| AllocState {
            info,
            types: Vec::new(),
            dispatch: [None; 3],
        }),
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
    loop {
        while let Some((orig, args, throws, id)) = m.work.pop() {
            let mut f = m.make(orig, &args);
            // A call through a trait whose method throws expects a result:
            // the impl's method that doesn't throw is made to, never
            // throwing.
            if let Some(err) = throws {
                f.throws = Some(err);
                f.symbol.push_str("<throws>");
            }
            origin.resize(m.funcs.len(), 0);
            origin[id] = orig;
            m.funcs[id] = Some(f);
        }
        // The allocators' methods, then the dispatch through handles,
        // once every allocator type is known.
        if !m.alloc_step() {
            break;
        }
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
        statics: m.statics,
        allocators: m
            .alloc
            .map(|a| a.types.iter().map(|&(t, _)| t).collect())
            .unwrap_or_default(),
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
    /// The clones made here, by type and whether they throw (see
    /// [`Mono::clone_fn`]).
    clones: HashMap<(Ty, bool), FuncId>,
    /// The destructions and clones made here (see [`Mono::destroy_fn`]).
    made: Vec<FuncId>,
    /// The span of the function being made, for the destructions it
    /// makes (their debug information).
    span: Span,
    /// `statics[i]`: whether an instance uses `static` `i`.
    statics: Vec<bool>,
    /// The allocator context, if the program imports `std/alloc`.
    alloc: Option<AllocState>,
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
            uses_alloc: f.uses_alloc,
        }
    }

    /// The root allocator's type, reached by the program (once anything
    /// allocates, or names an allocator).
    fn root_allocator(&mut self) -> Ty {
        let a = self.alloc.as_mut().expect("`std/alloc` is loaded");
        if a.types.is_empty() {
            a.types.push((a.info.root_ty, [None; 3]));
        }
        self.statics[a.info.root] = true;
        a.info.root_ty
    }

    /// The program-level function of method `m` (in [`ALLOC_METHODS`]) of
    /// the `Allocator` implementation of `ty`.
    fn allocator_method(&self, ty: Ty, m: usize) -> FuncId {
        let info = self.alloc.as_ref().expect("`std/alloc` is loaded").info;
        self.program.dispatch.impls[&(info.allocator, ty.decl())][ALLOC_METHODS[m]]
    }

    /// The next step of the allocator context, once the instances so far
    /// are made: the methods the dispatch functions call, of each
    /// allocator type reached, then the dispatch functions. Only the
    /// methods called are made: a program that never resizes has no
    /// `resize`. Whether it made anything.
    fn alloc_step(&mut self) -> bool {
        let Some(a) = &self.alloc else {
            return false;
        };
        let missing: Vec<(usize, usize, Ty)> = a
            .types
            .iter()
            .enumerate()
            .flat_map(|(k, &(ty, made))| {
                (0..3)
                    .filter(move |&m| a.dispatch[m].is_some() && made[m].is_none())
                    .map(move |m| (k, m, ty))
            })
            .collect();
        if !missing.is_empty() {
            for (k, m, ty) in missing {
                let f = self.allocator_method(ty, m);
                let id = self.instance(f, ty.type_args().to_vec());
                self.alloc.as_mut().expect("checked").types[k].1[m] = Some(id);
            }
            return true;
        }
        let pending: Vec<(usize, FuncId)> = a
            .dispatch
            .iter()
            .enumerate()
            .filter_map(|(m, id)| id.map(|id| (m, id)))
            .filter(|&(_, id)| self.funcs[id].is_none())
            .collect();
        if pending.is_empty() {
            return false;
        }
        for (m, id) in pending {
            let mut f = self.dispatch_parts(m);
            let locals = f.locals.clone();
            self.block(&mut f.body, &|_| None, &locals);
            self.funcs[id] = Some(f);
        }
        true
    }

    /// The function a call through a handle of method `m` calls (made
    /// once every allocator type is known).
    fn dispatch_fn(&mut self, m: usize) -> FuncId {
        self.root_allocator();
        let a = self.alloc.as_mut().expect("`std/alloc` is loaded");
        if let Some(id) = a.dispatch[m] {
            return id;
        }
        let id = self.funcs.len();
        self.funcs.push(None);
        self.made.push(id);
        self.alloc.as_mut().expect("checked").dispatch[m] = Some(id);
        id
    }

    /// The dispatch function of method `m` (see the module docs): it takes
    /// the handle and the method's other parameters, and calls the method
    /// of the allocator type the handle's number names, with the
    /// allocator the handle's address points to (the root's, a `static`,
    /// for number 0).
    fn dispatch_parts(&self, m: usize) -> Func {
        let a = self.alloc.as_ref().expect("`std/alloc` is loaded");
        let info = a.info;
        let usize_ty = Ty::Int(IntTy {
            signed: false,
            bits: 64,
            size: true,
        });
        let bytes = Ty::ptr(Ty::Int(IntTy::new(false, 8)));
        let (names, tys, ret): (&[&str], Vec<Ty>, Ty) = match m {
            0 => (&["size", "align"], vec![usize_ty, usize_ty], bytes),
            1 => (
                &["p", "old", "new", "align"],
                vec![bytes, usize_ty, usize_ty, usize_ty],
                Ty::Bool,
            ),
            _ => (
                &["p", "size", "align"],
                vec![bytes, usize_ty, usize_ty],
                Ty::Unit,
            ),
        };
        let param = |name: &str, ty: Ty| Local {
            name: name.to_owned(),
            ty,
            mutable: false,
            convention: Some(Convention::Let),
            drop_flag: false,
        };
        let mut locals = vec![param("self", info.handle)];
        locals.extend(names.iter().zip(&tys).map(|(n, &t)| param(n, t)));
        let local = |l: usize| TExpr {
            kind: TExprKind::Local(l),
            ty: locals[l].ty,
        };
        let handle_field = |k: u32| TExpr {
            kind: TExprKind::Field(Box::new(local(0)), k),
            ty: usize_ty,
        };
        let throws = (m == 0).then(Ty::alloc_error);
        let call_of = |k: usize, ty: Ty| -> Vec<TStmt> {
            let f = self.allocator_method(ty, m);
            let callee = &self.program.funcs[f];
            let this = if k == 0 {
                TExpr {
                    kind: TExprKind::Static(info.root),
                    ty,
                }
            } else {
                let addr = TExpr {
                    kind: TExprKind::Intrinsic(Intrinsic::FromAddr, vec![handle_field(1)]),
                    ty: Ty::ptr(ty),
                };
                TExpr {
                    kind: TExprKind::Deref(Box::new(addr)),
                    ty,
                }
            };
            let mut args = vec![this];
            args.extend((1..locals.len()).map(local));
            let call = TExpr {
                kind: TExprKind::GenericCall(f, ty.type_args().to_vec(), args),
                ty: match callee.throws {
                    Some(err) => Ty::result(ret, err),
                    None => ret,
                },
            };
            let value = if callee.throws.is_some() {
                TExpr {
                    kind: TExprKind::Try(Box::new(call)),
                    ty: ret,
                }
            } else {
                call
            };
            if ret == Ty::Unit {
                vec![TStmt::Expr(value), TStmt::Return(None)]
            } else {
                vec![TStmt::Return(Some(value))]
            }
        };
        // Number 0 (the root's) last, without a test.
        let mut body = call_of(0, a.types[0].0);
        for (k, &(ty, _)) in a.types.iter().enumerate().skip(1) {
            let is = TExpr {
                kind: TExprKind::Binary(
                    TBinOp::Cmp(CmpOp::Eq),
                    Box::new(handle_field(0)),
                    Box::new(TExpr {
                        kind: TExprKind::Int(k as i128),
                        ty: usize_ty,
                    }),
                ),
                ty: Ty::Bool,
            };
            body = vec![TStmt::If(is, call_of(k, ty), body)];
        }
        Func {
            name: format!("Handle.${}", ALLOC_METHODS[m]),
            symbol: format!("std/alloc.Handle.${}", ALLOC_METHODS[m]),
            type_params: Vec::new(),
            owner_params: 0,
            value_params: Vec::new(),
            params: (0..locals.len()).collect(),
            ret,
            throws,
            locals,
            body,
            span: self.span,
            template: false,
            uses_alloc: false,
        }
    }

    /// Whether cloning a value of the concrete type `ty` allocates, and
    /// whether it throws (as the checker's `clone_effects`).
    fn clone_effects(&self, ty: Ty) -> (bool, bool) {
        if ty.is_copy() {
            return (false, false);
        }
        if let Some(f) = self.program.dispatch.clone_impl(ty) {
            let f = &self.program.funcs[f];
            return (f.uses_alloc, f.throws.is_some());
        }
        let parts = match ty {
            Ty::Array(_) => vec![ty.as_array().expect("an array").0],
            Ty::Optional(_) => vec![ty.as_optional().expect("an optional")],
            _ => ty.members(),
        };
        parts.into_iter().fold((false, false), |(a, t), p| {
            let (pa, pt) = self.clone_effects(p);
            (a || pa, t || pt)
        })
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
        let chain = self.chain_link(ty);
        let mut f = destroy_parts(
            ty,
            format!("{}.$destroy", self.type_symbol(ty)),
            self.span,
            chain,
        );
        let locals = f.locals.clone();
        self.block(&mut f.body, &|_| None, &locals);
        self.funcs[id] = Some(f);
        id
    }

    /// For a struct with one field `?Box[Self]` (a link of a chain), the
    /// field's index, which its destruction loops over (see the module
    /// docs).
    fn chain_link(&self, ty: Ty) -> Option<usize> {
        let info = self.program.alloc?;
        let def = ty.as_struct()?;
        let links: Vec<usize> = (0..def.fields.len())
            .filter(|&k| {
                def.fields[k]
                    .ty
                    .as_optional()
                    .is_some_and(|b| b.same_decl(info.boxed) && b.type_args().first() == Some(&ty))
            })
            .collect();
        match links[..] {
            [k] => Some(k),
            _ => None,
        }
    }

    /// The function that clones a value of type `ty`, a struct, an enum,
    /// an optional or an array without a `deinit` or an `impl Clone` of its
    /// own, whose parts are `Clone`: made here, it clones each part. It
    /// allocates and throws when a part's clone does, and throws when the
    /// call expects a result (`throws`).
    fn clone_fn(&mut self, ty: Ty, throws: bool) -> FuncId {
        if let Some(&id) = self.clones.get(&(ty, throws)) {
            return id;
        }
        let id = self.funcs.len();
        self.funcs.push(None);
        self.clones.insert((ty, throws), id);
        self.made.push(id);
        let (allocates, parts_throw) = self.clone_effects(ty);
        debug_assert!(throws || !parts_throw, "a clone that throws gives a result");
        let mut f = clone_parts(
            ty,
            format!(
                "{}.$clone{}",
                self.type_symbol(ty),
                if throws { "<throws>" } else { "" }
            ),
            self.span,
            &|t| self.clone_effects(t).1,
        );
        f.uses_alloc = allocates;
        f.throws = throws.then(Ty::alloc_error);
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
        if let TExprKind::Layout(t, _) = &mut e.kind {
            *t = t.subst(map);
        }
        if let TExprKind::Static(k) = e.kind {
            self.statics[k] = true;
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
        // `x.clone()`: the copy, or a call of the type's `clone`. Where it
        // may fail, its value is a result: the copy is `ok`, and a clone
        // that doesn't throw is made to.
        if let TExprKind::Clone(inner) = &mut e.kind {
            let inner = std::mem::replace(
                &mut **inner,
                TExpr {
                    kind: TExprKind::Bool(false),
                    ty: Ty::Bool,
                },
            );
            let rty = e.ty;
            let (ty, wants) = match rty.as_result() {
                Some((ok, _)) => (ok, true),
                None => (rty, false),
            };
            if ty.is_copy() {
                *e = if wants {
                    TExpr {
                        kind: TExprKind::Variant(0, vec![inner]),
                        ty: rty,
                    }
                } else {
                    inner
                };
                self.expr(e, map, locals);
                return;
            }
            let f = match self.program.dispatch.clone_impl(ty) {
                Some(f) => {
                    let adapt = wants && self.program.funcs[f].throws.is_none();
                    self.instance_throwing(f, ty.type_args().to_vec(), adapt.then(Ty::alloc_error))
                }
                None => self.clone_fn(ty, wants),
            };
            *e = TExpr {
                kind: TExprKind::Call(f, vec![inner]),
                ty: rty,
            };
        }
        // `p.destroy()` destroys what the pointer points to.
        if let TExprKind::Intrinsic(Intrinsic::PtrDestroy, args) = &e.kind
            && let Some(to) = args[0].ty.subst(map).as_ptr()
            && to.needs_destroy()
        {
            self.destroy_fn(to);
        }
        // The allocator context.
        if let TExprKind::Intrinsic(
            k @ (Intrinsic::AllocCurrent
            | Intrinsic::AllocRoot
            | Intrinsic::AllocHandle
            | Intrinsic::HandleAlloc
            | Intrinsic::HandleResize
            | Intrinsic::HandleFree),
            args,
        ) = &mut e.kind
        {
            let k = *k;
            self.root_allocator();
            let m = match k {
                Intrinsic::HandleAlloc => 0,
                Intrinsic::HandleResize => 1,
                Intrinsic::HandleFree => 2,
                Intrinsic::AllocHandle => {
                    // Another allocator type, for the handles of `a`.
                    let ty = args[0].ty.subst(map);
                    let a = self.alloc.as_mut().expect("checked");
                    if !a.types.iter().any(|&(t, _)| t == ty) {
                        a.types.push((ty, [None; 3]));
                    }
                    3
                }
                _ => 3,
            };
            if m < 3 {
                let mut args = std::mem::take(args);
                let via_root =
                    matches!(args[0].kind, TExprKind::Intrinsic(Intrinsic::AllocRoot, _));
                let f = if via_root {
                    // `alloc.root().free(...)`: the root's method, directly.
                    let a = self.alloc.as_ref().expect("checked");
                    let (root, root_ty) = (a.info.root, a.info.root_ty);
                    let g = self.allocator_method(root_ty, m);
                    let adapt =
                        e.ty.as_result().is_some() && self.program.funcs[g].throws.is_none();
                    args[0] = TExpr {
                        kind: TExprKind::Static(root),
                        ty: root_ty,
                    };
                    self.instance_throwing(
                        g,
                        root_ty.type_args().to_vec(),
                        adapt.then(Ty::alloc_error),
                    )
                } else {
                    self.dispatch_fn(m)
                };
                e.kind = TExprKind::Call(f, args);
            }
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
/// destroys each part that needs destruction. With `chain`, the struct's
/// field of that index is a link `?Box[Self]`, destroyed by a loop (see
/// [`chain_loop`]), not by destroying it.
fn destroy_parts(ty: Ty, symbol: String, span: Span, chain: Option<usize>) -> Func {
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
        // The fields of `of`, last first, but the link of a chain.
        let fields = |of: &TExpr| -> Vec<TStmt> {
            (0..def.fields.len())
                .rev()
                .filter(|&k| def.fields[k].ty.needs_destroy() && Some(k) != chain)
                .map(|k| {
                    destroy(
                        TExprKind::Field(Box::new(of.clone()), k as u32),
                        def.fields[k].ty,
                    )
                })
                .collect()
        };
        let mut body = fields(&this);
        if let Some(k) = chain {
            body.extend(chain_loop(&mut locals, ty, k, &this, &fields));
        }
        body
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
        uses_alloc: false,
    }
}

/// The loop that destroys the chain of boxes from field `k` of `this` (a
/// struct of type `ty`, whose other fields `fields` destroys), with two
/// more locals: the link taken out (`$link`, a `?Box[ty]`) and the node
/// moved out of its box (`$node`). Neither is destroyed as a whole: the
/// node is read from the box's pointer (its first field), the box's memory
/// is freed through its handle (its second field), and the node's fields
/// are destroyed but its link, which goes on to `$link`. No function in
/// it destroys a box of `ty`, so the call graph has no cycle.
fn chain_loop(
    locals: &mut Vec<Local>,
    ty: Ty,
    k: usize,
    this: &TExpr,
    fields: &dyn Fn(&TExpr) -> Vec<TStmt>,
) -> Vec<TStmt> {
    let def = ty.as_struct().expect("a struct");
    let link_ty = def.fields[k].ty;
    let box_ty = link_ty.as_optional().expect("an optional box");
    let hidden = |name: &str, ty: Ty| Local {
        name: name.to_owned(),
        ty,
        mutable: true,
        convention: None,
        drop_flag: false,
    };
    let (link, node) = (locals.len(), locals.len() + 1);
    locals.push(hidden("$link", link_ty));
    locals.push(hidden("$node", ty));
    let local = |l: usize, ty: Ty| TExpr {
        kind: TExprKind::Local(l),
        ty,
    };
    // `$link = take(&of.next)`: written over, never destroyed.
    let take = |of: &TExpr| {
        let place = TExpr {
            kind: TExprKind::Field(Box::new(of.clone()), k as u32),
            ty: link_ty,
        };
        TStmt::Init(
            link,
            TExpr {
                kind: TExprKind::Intrinsic(
                    Intrinsic::Take,
                    vec![TExpr {
                        kind: TExprKind::Ref(Box::new(place)),
                        ty: link_ty,
                    }],
                ),
                ty: link_ty,
            },
        )
    };
    let boxed = TExpr {
        kind: TExprKind::Payload(Box::new(local(link, link_ty)), 1, 0),
        ty: box_ty,
    };
    let box_def = box_ty.as_struct().expect("a box");
    let part = |i: u32| TExpr {
        kind: TExprKind::Field(Box::new(boxed.clone()), i),
        ty: box_def.fields[i as usize].ty,
    };
    let usize_ty = Ty::Int(IntTy {
        signed: false,
        bits: 64,
        size: true,
    });
    let layout = |align: bool| TExpr {
        kind: TExprKind::Layout(ty, align),
        ty: usize_ty,
    };
    let bytes = TExpr {
        kind: TExprKind::Intrinsic(Intrinsic::PtrCast, vec![part(0)]),
        ty: Ty::ptr(Ty::Int(IntTy::new(false, 8))),
    };
    let mut next = vec![
        TStmt::Init(
            node,
            TExpr {
                kind: TExprKind::Intrinsic(Intrinsic::PtrRead, vec![part(0)]),
                ty,
            },
        ),
        TStmt::Expr(TExpr {
            kind: TExprKind::Intrinsic(
                Intrinsic::HandleFree,
                vec![part(1), bytes, layout(false), layout(true)],
            ),
            ty: Ty::Unit,
        }),
    ];
    next.extend(fields(&local(node, ty)));
    next.push(take(&local(node, ty)));
    vec![
        take(this),
        TStmt::Loop(vec![TStmt::Match {
            value: local(link, link_ty),
            arms: vec![
                TArm {
                    variants: vec![0],
                    body: vec![TStmt::Break],
                },
                TArm {
                    variants: vec![1],
                    body: next,
                },
            ],
        }]),
    ]
}

/// A function that clones a value of type `ty` part by part (see
/// [`Mono::clone_fn`]): it takes the value read-only, and returns a struct
/// literal, a variant or an array literal of its parts' clones. A part
/// whose clone throws (`throws` says) is passed on with `try`.
fn clone_parts(ty: Ty, symbol: String, span: Span, throws: &dyn Fn(Ty) -> bool) -> Func {
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
    let clone = |kind: TExprKind, ty: Ty| {
        let part = TExpr { kind, ty };
        if !throws(ty) {
            return TExpr {
                kind: TExprKind::Clone(Box::new(part)),
                ty,
            };
        }
        let result = TExpr {
            kind: TExprKind::Clone(Box::new(part)),
            ty: Ty::result(ty, Ty::alloc_error()),
        };
        TExpr {
            kind: TExprKind::Try(Box::new(result)),
            ty,
        }
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
        uses_alloc: false,
    }
}
