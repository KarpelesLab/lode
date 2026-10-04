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

use std::collections::HashMap;

use crate::sema::{
    Func, FuncId, Handler, Local, Program, TExpr, TExprKind, TStmt, stmt_blocks_mut,
    stmt_exprs_mut, subexprs_mut,
};
use crate::types::Ty;

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
    };
    let main = match program.main {
        Some(main) => {
            let id = m.instance(main, Vec::new());
            m.root = Some(id);
            Some(id)
        }
        None => {
            for (i, f) in program.funcs.iter().enumerate() {
                if f.type_params.is_empty() {
                    m.instance(i, Vec::new());
                }
            }
            None
        }
    };
    let mut origin = vec![0; m.funcs.len()];
    while let Some((orig, args, id)) = m.work.pop() {
        let f = m.make(orig, &args);
        origin.resize(m.funcs.len(), 0);
        origin[id] = orig;
        m.funcs[id] = Some(f);
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
    /// The instance of each function and type arguments made so far.
    ids: HashMap<(FuncId, Vec<Ty>), FuncId>,
    /// The instances to make: the function, its type arguments, and the
    /// instance's id.
    work: Vec<(FuncId, Vec<Ty>, FuncId)>,
    funcs: Vec<Option<Func>>,
    strings: Vec<bool>,
    tables: Vec<bool>,
    root: Option<FuncId>,
    root_called: bool,
}

impl Mono<'_> {
    /// The id of the instance of function `f` with the type arguments
    /// `args` (concrete types), made later if it's new.
    fn instance(&mut self, f: FuncId, args: Vec<Ty>) -> FuncId {
        if let Some(&id) = self.ids.get(&(f, args.clone())) {
            return id;
        }
        let id = self.funcs.len();
        self.funcs.push(None);
        self.ids.insert((f, args.clone()), id);
        self.work.push((f, args, id));
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
        let locals = f
            .locals
            .iter()
            .map(|l| Local {
                name: l.name.clone(),
                ty: l.ty.subst(&map),
                mutable: l.mutable,
                convention: l.convention,
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
        for s in &mut body {
            self.stmt(s, &map);
        }
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
        }
    }

    fn stmt(&mut self, s: &mut TStmt, map: &impl Fn(Ty) -> Option<Ty>) {
        for e in stmt_exprs_mut(s) {
            self.expr(e, map);
        }
        for block in stmt_blocks_mut(s) {
            for s in block {
                self.stmt(s, map);
            }
        }
    }

    fn expr(&mut self, e: &mut TExpr, map: &impl Fn(Ty) -> Option<Ty>) {
        e.ty = e.ty.subst(map);
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
                let (f, types) = self.program.dispatch.resolve(*f, &types);
                let id = self.instance(f, types);
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
            } => {
                for s in body {
                    self.stmt(s, map);
                }
            }
            _ => {}
        }
        for sub in subexprs_mut(e) {
            self.expr(sub, map);
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
