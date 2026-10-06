//! Semantic checking: names, types, `unsafe`, and proof obligations.
//!
//! The checker walks every package, resolves names across packages, checks
//! types, and discharges the proof obligations of docs/safety.md using the
//! flow-sensitive facts in [`facts`]. Its output is the typed tree in [`tree`].

mod comptime;
mod eval;
mod expr;
pub mod facts;
mod generic;
mod refine;
mod traits;
pub mod tree;

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::ast::{self, ExprKind, Stmt, TypeExpr};
use crate::diag::Diagnostic;
use crate::load::Package;
use crate::source::{FileId, Span};
use crate::target::Target;
use crate::types::{Field, IntTy, Len, Primitive, Range, Trait, Ty, Variant, primitive};

use facts::{Env, Linear, Term};
pub use tree::*;

/// Check every loaded package (dependencies first, the root package last)
/// for `target`, which picks the branches of `if comptime` and is the value
/// of `target`.
pub fn check(packages: &[Package], target: &Target) -> (Program, Vec<Diagnostic>) {
    let mut ck = Checker {
        diags: Vec::new(),
        pkgs: Vec::new(),
        sigs: Vec::new(),
        consts: Vec::new(),
        imports: HashMap::new(),
        methods: HashMap::new(),
        strings: Vec::new(),
        tables: Vec::new(),
        string_ids: HashMap::new(),
        generic_calls: Vec::new(),
        declared_bounds: HashMap::new(),
        pending_bounds: None,
        ptr_bits: target.pointer_bits,
        target: *target,
        fn_decls: Vec::new(),
        func_states: Vec::new(),
        checked_order: Vec::new(),
        const_exprs: Vec::new(),
        declaring: true,
        package_error: false,
        traits: Vec::new(),
        trait_index: HashMap::new(),
        impls: Vec::new(),
        impl_methods: HashMap::new(),
        members: HashMap::new(),
        dispatch: Dispatch::default(),
        expansions: HashMap::new(),
        expansion_ids: HashMap::new(),
        expansion_counts: HashMap::new(),
        expanding: 0,
        view_params: HashSet::new(),
        refined_types: Vec::new(),
        field_refines: HashMap::new(),
        deinits: HashSet::new(),
        sources: packages
            .iter()
            .flat_map(|p| &p.files)
            .map(|f| (f.id, f.source.as_str()))
            .collect(),
    };
    ck.collect(packages);
    // Every named refinement, used or not, so its errors are reported.
    for k in 0..ck.refined_types.len() {
        ck.refined_type(k);
    }
    ck.declaring = false;
    if ck.package_error {
        let program = Program {
            funcs: Vec::new(),
            strings: Vec::new(),
            tables: Vec::new(),
            main: None,
            packages: packages.iter().map(|p| p.path.clone()).collect(),
            warnings: Vec::new(),
            dispatch: Dispatch::default(),
            deinits: HashMap::new(),
        };
        return (program, ck.diags);
    }

    // Check every constant, used or not, so its errors are reported. The
    // functions a constant's value calls are checked on the way.
    for id in 0..ck.consts.len() {
        ck.const_value(id);
    }
    // Expansions are added as they're made (and checked then, unless a
    // trial check of a loop's body rolled that back).
    let mut id = 0;
    while id < ck.fn_decls.len() {
        if matches!(ck.func_states[id], FuncState::Unchecked) {
            ck.check_function(id);
        }
        id += 1;
    }
    let funcs: Vec<Func> = std::mem::take(&mut ck.func_states)
        .into_iter()
        .map(|state| match state {
            FuncState::Done(f, _) => Rc::try_unwrap(f).unwrap_or_else(|f| (*f).clone()),
            _ => unreachable!("every function is checked"),
        })
        .collect();

    let root = packages.len().saturating_sub(1);
    let main = match ck.pkgs.get(root).and_then(|p| p.items.get("main")) {
        Some(Item::Func(id)) => Some(*id),
        _ => None,
    };
    if let Some(id) = main {
        let sig = &ck.sigs[id];
        let (no_params, ret, span) = (sig.params.is_empty(), sig.ret, sig.span);
        let throws = sig.throws.is_some();
        if !no_params {
            ck.error(span, "`main` takes no parameters");
        }
        if throws {
            ck.diags.push(
                Diagnostic::error(span, "`main` can't throw").with_help(
                    "handle its errors with `catch` or `match`, and return an exit status",
                ),
            );
        }
        if !matches!(ret, Ty::Unit | Ty::Int(_) | Ty::Never) {
            ck.error(
                span,
                "`main` must return nothing, an integer exit status or `never`",
            );
        }
        if !ck.sigs[id].type_params.is_empty() {
            ck.error(span, "`main` can't be generic");
        }
    }
    ck.check_generic_recursion();
    // An error in a function with `comptime` parameters is found once per
    // expansion: it's reported once.
    let mut seen = HashSet::new();
    ck.diags
        .retain(|d| seen.insert((d.span.file, d.span.start, d.span.end, d.message.clone())));

    let deinits = ck
        .methods
        .iter()
        .filter(|&((_, name), _)| name == DEINIT)
        .map(|(&(ty, _), &id)| (ty, id))
        .collect();
    let program = Program {
        funcs,
        strings: ck.strings,
        tables: ck.tables,
        main,
        packages: packages.iter().map(|p| p.path.clone()).collect(),
        warnings: Vec::new(),
        dispatch: ck.dispatch,
        deinits,
    };
    (program, ck.diags)
}

#[derive(Clone, Copy, Debug)]
enum Item {
    Func(FuncId),
    Const(usize),
    /// A struct or an enum type.
    Type(Ty),
    /// A trait declared in Lode.
    Trait(Trait),
    /// A named refinement (`type Digit = u8 where self <= 9`), by index
    /// into [`Checker::refined_types`].
    Refined(usize),
}

/// A named refinement's declaration, and its type and refinement once
/// resolved.
struct RefinedType<'a> {
    decl: &'a ast::TypeDecl,
    pkg: usize,
    file: FileId,
    state: RefinedState,
}

enum RefinedState {
    Unresolved,
    Resolving,
    Done(Option<(Ty, Rc<refine::Refine>)>),
}

struct PkgInfo {
    path: String,
    items: HashMap<String, Item>,
}

struct Sig {
    is_pub: bool,
    is_unsafe: bool,
    /// The package that declares it.
    pkg: usize,
    /// The name calls are shown with: `f`, or `Point.scale` for a method
    /// or an associated function.
    name: String,
    /// The parameters' types, conventions and names; a method's `self`
    /// first.
    params: Vec<(Ty, Convention, String)>,
    /// Whether the first parameter is `self`.
    has_self: bool,
    ret: Ty,
    /// The error type, for a function that throws.
    throws: Option<Ty>,
    /// The function name's span.
    span: Span,
    /// The generic parameters of a generic function, and the traits each
    /// declares as its bounds (for a method of a generic type, those of
    /// the type's declaration too). A method of a generic type has the
    /// type's parameters first (`owner_params` of them), then its own.
    type_params: Vec<Ty>,
    bounds: Vec<Vec<Trait>>,
    owner_params: usize,
    /// For a method of a trait or an `impl`: what `Self` is in it (the
    /// trait's type parameter, or the impl's type).
    self_ty: Option<Ty>,
    /// The name in its symbol, after the package's path, when it's not
    /// `name`: a method of an `impl` names its trait (`Point.area<main.Shape>`).
    symbol_name: Option<String>,
    /// For a function with `comptime` parameters or a pack: the kind of
    /// each parameter. Its calls are calls of its expansions.
    template: Option<comptime::Template>,
    /// For a function the compiler implements (`@intrinsic`): which.
    intrinsic: Option<Intrinsic>,
    /// The refinement of each parameter (docs/safety.md, Refinements in
    /// types), and of the result.
    refines: Vec<Option<Rc<refine::Refine>>>,
    ret_refine: Option<Rc<refine::Refine>>,
    /// The refinements of its own value parameters (`[N: usize where N >
    /// 0]`), together.
    vparam_refine: Option<Rc<refine::Refine>>,
}

/// The value of a checked constant.
#[derive(Clone, Copy, Debug)]
enum ConstVal {
    /// A typed integer constant.
    Typed(Ty, i128),
    /// An untyped integer constant: like a literal, it takes its type from
    /// the context where it's used.
    Untyped(i128),
    /// An array constant, of its type, by index into [`Checker::tables`].
    Table(Ty, usize),
    /// A constant of another type (`bool`, a struct, an enum, an optional,
    /// an array of them): the expression that builds it, by index into
    /// [`Checker::const_exprs`].
    Expr(usize),
}

/// Where a function is in being checked: in order, or earlier, on demand,
/// when a constant's value calls it.
enum FuncState {
    Unchecked,
    Checking,
    /// Checked, and whether without errors (only then can it run at
    /// compile time).
    Done(Rc<Func>, bool),
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
    /// The methods and associated functions of each struct and enum, by
    /// name.
    methods: HashMap<(Ty, String), FuncId>,
    strings: Vec<Vec<u8>>,
    string_ids: HashMap<Vec<u8>, usize>,
    /// The array constants checked so far.
    tables: Vec<Table>,
    /// The calls from generic functions to generic functions, for
    /// [`Checker::check_generic_recursion`].
    generic_calls: Vec<generic::GenericEdge>,
    /// The traits each type parameter declared as its bounds (closed under
    /// supertraits in its [`crate::types::ParamDef`]).
    declared_bounds: HashMap<Ty, Vec<Trait>>,
    /// While the types' declarations are collected: the instances of
    /// generic types whose bounds are checked once every type is known.
    pending_bounds: Option<Vec<(Ty, Span)>>,
    ptr_bits: u32,
    /// The target checked for.
    target: Target,
    /// Every function's declaration, package and file, by id.
    fn_decls: Vec<(&'a ast::FnDecl, usize, FileId)>,
    /// Every function's checking state, by id.
    func_states: Vec<FuncState>,
    /// The functions checked so far, in order (for [`Checker::rollback`]).
    checked_order: Vec<FuncId>,
    /// The values of the constants of [`ConstVal::Expr`].
    const_exprs: Vec<TExpr>,
    /// Whether types and signatures are being declared: a constant needed
    /// for them can't call functions, which aren't all known yet.
    declaring: bool,
    /// Whether a package-level `compile_error` was reached: the program
    /// isn't checked further.
    package_error: bool,
    /// The traits declared in Lode, and the index of each by trait.
    traits: Vec<traits::TraitInfo<'a>>,
    trait_index: HashMap<Trait, usize>,
    /// The `impl` blocks.
    impls: Vec<traits::ImplInfo<'a>>,
    /// The methods the impls give each named type (in its declared form),
    /// by name, with their traits: an impl's own, or a trait's default.
    impl_methods: HashMap<(Ty, String), Vec<(Trait, FuncId)>>,
    /// The functions declared in traits and impls.
    members: HashMap<FuncId, traits::Member>,
    /// What calls of trait methods run (see [`Dispatch`]).
    dispatch: Dispatch,
    /// The expansions of functions with `comptime` parameters or a pack,
    /// and the expansion of each template for each set of values.
    expansions: HashMap<FuncId, comptime::Expansion>,
    expansion_ids: HashMap<comptime::ExpansionKey, FuncId>,
    /// How many expansions each template has, for their symbols.
    expansion_counts: HashMap<FuncId, usize>,
    /// How deep the expansions being checked nest.
    expanding: usize,
    /// The type parameters of the expansions' packs, which may be views.
    view_params: HashSet<Ty>,
    /// The text of each file, for errors pointing into string literals.
    sources: HashMap<FileId, &'a str>,
    /// The named refinements.
    refined_types: Vec<RefinedType<'a>>,
    /// The refinements of each struct's fields, by declaration, with the
    /// field's index.
    field_refines: HashMap<Ty, Vec<(usize, Rc<refine::Refine>)>>,
    /// The `deinit` methods, which can't be called directly.
    deinits: HashSet<FuncId>,
}

/// Per-function (or per-constant) checking state.
struct FnCx {
    pkg: usize,
    file: FileId,
    locals: Vec<Local>,
    scopes: Vec<HashMap<String, LocalId>>,
    ret: Ty,
    /// The function's error type, if it throws.
    throws: Option<Ty>,
    loop_depth: u32,
    /// Nesting of `defer` blocks, which can't be left with `return`,
    /// `throw` or `try`.
    defer_depth: u32,
    /// In a `defer` block, the first local declared in it: it can't assign
    /// the locals before it, which are declared outside it.
    defer_floor: LocalId,
    /// Nesting of `unsafe` blocks; an `unsafe fn` body starts at 1.
    unsafe_depth: u32,
    /// The facts known at the current point.
    env: Env,
    /// How many of the first locals are the function's parameters.
    params: usize,
    /// Locals whose declaration failed to check, with an error reported:
    /// any use of them fails without another error.
    failed: HashSet<LocalId>,
    /// The function's `set` parameters, which must be assigned when it
    /// returns.
    set_params: Vec<LocalId>,
    /// The locals the last call checked assigns through `set` arguments
    /// that weren't assigned before it: they're assigned only if the call
    /// succeeds.
    call_sets: Vec<LocalId>,
    /// How deep the current expression is in the expression being checked
    /// (0 outside of one): a whole expression is checked for exclusivity
    /// once it's done.
    expr_depth: u32,
    /// For each loop around the current point, innermost last: where its
    /// body has left an iteration so far.
    loops: Vec<LoopEdges>,
    /// Where the `str` locals' values come from, for `-> str`.
    strs: StrOrigins,
    /// The function being checked (`None` for a constant or a declaration).
    func: Option<FuncId>,
    /// The generic parameters of a generic function (or of the struct or
    /// enum whose fields are checked).
    type_params: Vec<Ty>,
    /// The local holding each value parameter, in a function's body.
    value_locals: Vec<(Ty, LocalId)>,
    /// The locals a value was moved out of somewhere (see
    /// [`Checker::consume`]), for the message when one is used unassigned.
    moved: HashSet<LocalId>,
    /// Whether this is code that only runs at compile time (a constant's
    /// value, an `if comptime` condition). Its proof obligations are
    /// discharged by running it (docs/generics.md, Proof obligations in
    /// compile-time code): an operation that isn't proven is wrapped in an
    /// [`TExprKind::Unproven`] instead of being an error.
    comptime: bool,
    /// In a trait or an `impl`: what `Self` names.
    self_ty: Option<Ty>,
    /// While a trait's or an impl's method's signature is resolved: the
    /// generic parameters it gets from the trait (`Self`) or the impl, and
    /// their bounds.
    member: Option<(Vec<Ty>, Vec<Vec<Trait>>)>,
    /// The values of the locals known when compiling: `comptime`
    /// parameters of an expansion, `comptime let` values, the variable of a
    /// `comptime for`, the bindings of a `match comptime`.
    ct_values: HashMap<LocalId, eval::Value>,
    /// In an expansion with a pack: the pack.
    pack: Option<comptime::PackCx>,
    /// In an expansion: where its `compile_error`s are reported.
    report: Option<Span>,
    /// In the body of a `comptime for`: the loop depth outside it, which a
    /// `break` or `continue` can't leave to.
    ct_loop_floor: Option<u32>,
    /// While the signature of an expansion is resolved: how many arguments
    /// its pack has.
    expanding: Option<usize>,
    /// The type parameters a pack declared (one per argument in an
    /// expansion).
    pack_params: Vec<Ty>,
    /// The locals with a refinement every value they're given must meet: a
    /// `var` of a named refinement, and a parameter with a refinement that
    /// the body can assign. With the leaf that's the local itself.
    place_refines: HashMap<LocalId, (Rc<refine::Refine>, refine::Leaf)>,
    /// The refinement of the function's result.
    ret_refine: Option<Rc<refine::Refine>>,
    /// The pattern bindings that read their value in place, whose type
    /// isn't `Copy` (docs/allocation.md, Partial moves and patterns): each
    /// with the place it reads, rooted at a local or at another binding.
    /// Keeping one moves that local.
    projections: HashMap<LocalId, TExpr>,
    /// The temporaries of the statements being checked (see
    /// [`Checker::temp`]), innermost statement's last.
    temps: Vec<LocalId>,
    /// The statements to add after the ones being checked, in their lists:
    /// the `Drop` of a local they declare. Innermost statement's last.
    after: Vec<TStmt>,
    /// The variables `defer` bodies move, which must be assigned at every
    /// exit they run at.
    defer_moves: Vec<DeferMove>,
    /// In a `defer` body: whether it's an `errdefer`, and the depth of the
    /// scope of the block it's in.
    defer_kind: Option<(bool, usize)>,
    /// In a `deinit`: its `self`, which can't be moved.
    deinit_self: Option<LocalId>,
}

/// A variable a `defer` body moves (see [`FnCx::defer_moves`]).
#[derive(Clone, Copy, Debug)]
struct DeferMove {
    local: LocalId,
    /// Whether the `defer` is an `errdefer`, which runs only at the exits
    /// with an error.
    on_error: bool,
    /// The depth of the scope of the block the `defer` is in.
    depth: usize,
    /// Where the body moves it.
    span: Span,
}

/// For a function returning a `str`: which locals hold only strings with
/// static storage (see [`Checker::check_str_returns`]).
#[derive(Clone, Default)]
struct StrOrigins {
    /// For each `str` local (not a parameter) given a value so far: the
    /// locals its values were copied from, or `None` once it held a value
    /// that may not be static.
    deps: HashMap<LocalId, Option<Vec<LocalId>>>,
    /// The locals returned, and where.
    returned: Vec<(LocalId, Span)>,
}

/// The facts where a loop's body leaves an iteration: at each back-edge
/// (a `continue`, or the end of the body) and at each `break`.
#[derive(Default)]
struct LoopEdges {
    next: Vec<Env>,
    exits: Vec<Env>,
    /// The thresholds of the terms compared in the body (see
    /// [`note_thresholds`]).
    thresholds: Vec<(Term, i128)>,
    /// The depth of the scope around the loop: a `break` or `continue`
    /// leaves the deeper ones.
    scope_depth: usize,
}

/// The state a trial check of a loop body rolls back.
struct Mark {
    diags: usize,
    locals: usize,
    consts: Vec<ConstState>,
    strs: StrOrigins,
    moved: HashSet<LocalId>,
    generic_calls: usize,
    checked: usize,
    tables: usize,
    const_exprs: usize,
}

impl FnCx {
    fn new(pkg: usize, file: FileId, ret: Ty, is_unsafe: bool) -> FnCx {
        FnCx {
            pkg,
            file,
            locals: Vec::new(),
            scopes: vec![HashMap::new()],
            ret,
            throws: None,
            loop_depth: 0,
            defer_depth: 0,
            defer_floor: 0,
            unsafe_depth: u32::from(is_unsafe),
            env: Env::default(),
            loops: Vec::new(),
            params: 0,
            failed: HashSet::new(),
            set_params: Vec::new(),
            call_sets: Vec::new(),
            expr_depth: 0,
            strs: StrOrigins::default(),
            func: None,
            type_params: Vec::new(),
            value_locals: Vec::new(),
            moved: HashSet::new(),
            comptime: false,
            self_ty: None,
            member: None,
            ct_values: HashMap::new(),
            pack: None,
            report: None,
            ct_loop_floor: None,
            expanding: None,
            pack_params: Vec::new(),
            place_refines: HashMap::new(),
            ret_refine: None,
            projections: HashMap::new(),
            temps: Vec::new(),
            after: Vec::new(),
            defer_moves: Vec::new(),
            defer_kind: None,
            deinit_self: None,
        }
    }

    /// The local holding the value parameter `p`.
    fn value_local(&self, p: Ty) -> Option<LocalId> {
        self.value_locals
            .iter()
            .find(|&&(q, _)| q == p)
            .map(|&(_, l)| l)
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

/// The return type of a function that doesn't return.
const NEVER: &str = "never";

/// The type implementing the trait, in a trait or an `impl`.
const SELF: &str = "Self";

/// The method that destroys a value: `fn T.deinit(sink self)`
/// (docs/allocation.md, Declaring destruction).
const DEINIT: &str = "deinit";

/// `compile_error("message")`: an error where it's reached.
const COMPILE_ERROR: &str = "compile_error";

/// `compile_error_at(place, "message")`: an error pointing at `place`, a
/// part of a string literal.
const COMPILE_ERROR_AT: &str = "compile_error_at";

/// The compile-time value describing the target.
const TARGET: &str = "target";

/// The names an expression uses (not in the blocks of its `catch`es), with
/// their spans.
fn expr_names<'e>(e: &'e ast::Expr, out: &mut Vec<(&'e str, Span)>) {
    match &e.kind {
        ExprKind::Name(n) => out.push((n, e.span)),
        ExprKind::Int(_)
        | ExprKind::Char(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::None
        | ExprKind::Dot(_) => {}
        ExprKind::Unary(_, a)
        | ExprKind::Field(a, _)
        | ExprKind::TypeArgs(a, _)
        | ExprKind::Paren(a)
        | ExprKind::Try(a)
        | ExprKind::Throw(a)
        | ExprKind::Ref(a)
        | ExprKind::Spread(a) => expr_names(a, out),
        ExprKind::Binary(_, a, b) | ExprKind::ArrayRepeat(a, b) | ExprKind::Index(a, b) => {
            expr_names(a, out);
            expr_names(b, out);
        }
        ExprKind::Slice(base, start, end) => {
            expr_names(base, out);
            start.iter().chain(end).for_each(|a| expr_names(a, out));
        }
        ExprKind::Call(callee, args) => {
            expr_names(callee, out);
            args.iter().for_each(|a| expr_names(a, out));
        }
        ExprKind::ArrayLit(items) => items.iter().for_each(|a| expr_names(a, out)),
        ExprKind::StructLit(_, fields) => fields.iter().for_each(|f| expr_names(&f.value, out)),
        ExprKind::Catch { value, handler, .. } => {
            expr_names(value, out);
            if let ast::CatchHandler::Value(v) = handler {
                expr_names(v, out);
            }
        }
    }
}

/// The blocks of the `catch`es in an expression, at any depth.
fn catch_blocks<'e>(e: &'e ast::Expr, out: &mut Vec<&'e ast::Block>) {
    match &e.kind {
        ExprKind::Int(_)
        | ExprKind::Char(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Name(_)
        | ExprKind::None
        | ExprKind::Dot(_) => {}
        ExprKind::Unary(_, a)
        | ExprKind::Field(a, _)
        | ExprKind::TypeArgs(a, _)
        | ExprKind::Paren(a)
        | ExprKind::Try(a)
        | ExprKind::Throw(a)
        | ExprKind::Ref(a)
        | ExprKind::Spread(a) => catch_blocks(a, out),
        ExprKind::Binary(_, a, b) | ExprKind::ArrayRepeat(a, b) | ExprKind::Index(a, b) => {
            catch_blocks(a, out);
            catch_blocks(b, out);
        }
        ExprKind::Slice(base, start, end) => {
            catch_blocks(base, out);
            start.iter().chain(end).for_each(|a| catch_blocks(a, out));
        }
        ExprKind::Call(callee, args) => {
            catch_blocks(callee, out);
            args.iter().for_each(|a| catch_blocks(a, out));
        }
        ExprKind::ArrayLit(items) => items.iter().for_each(|a| catch_blocks(a, out)),
        ExprKind::StructLit(_, fields) => fields.iter().for_each(|f| catch_blocks(&f.value, out)),
        ExprKind::Catch { value, handler, .. } => {
            catch_blocks(value, out);
            match handler {
                ast::CatchHandler::Block(b) => out.push(b),
                ast::CatchHandler::Value(v) => catch_blocks(v, out),
            }
        }
    }
}

/// The expressions a statement evaluates itself (not those of the
/// statements nested in it).
fn own_exprs(s: &Stmt) -> Vec<&ast::Expr> {
    match s {
        Stmt::Let { init, .. } => init.iter().collect(),
        Stmt::ComptimeLet { init, .. } => vec![init],
        Stmt::Assign { target, value, .. } => vec![target, value],
        Stmt::Expr(e) | Stmt::Throw { value: e, .. } | Stmt::Match { value: e, .. } => vec![e],
        Stmt::Return { value, .. } => value.iter().collect(),
        Stmt::If(i) => vec![&i.cond],
        Stmt::While { cond, .. } => vec![cond],
        Stmt::For { iter, .. } => match iter {
            ast::ForIter::Range(a, b) => vec![a, b],
            ast::ForIter::Each(xs) => vec![xs],
        },
        Stmt::Loop { .. }
        | Stmt::Break(_)
        | Stmt::Continue(_)
        | Stmt::Unsafe(_)
        | Stmt::Defer { .. } => Vec::new(),
    }
}

/// The variables an expression may change: those passed with `&`, and the
/// receivers of method calls (which may take `inout self`; the method isn't
/// known here, so every receiver counts).
fn changed_names(e: &ast::Expr, out: &mut HashSet<String>) {
    let root_name = |place: &ast::Expr, out: &mut HashSet<String>| {
        if let ExprKind::Name(n) = &place_root(place).kind {
            out.insert(n.clone());
        }
    };
    match &e.kind {
        ExprKind::Ref(place) => root_name(place, out),
        ExprKind::Call(callee, _) => {
            if let ExprKind::Field(base, _) = &callee.kind {
                root_name(base, out);
            }
        }
        _ => {}
    }
    match &e.kind {
        ExprKind::Int(_)
        | ExprKind::Char(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Name(_)
        | ExprKind::None
        | ExprKind::Dot(_) => {}
        ExprKind::Unary(_, a)
        | ExprKind::Field(a, _)
        | ExprKind::TypeArgs(a, _)
        | ExprKind::Paren(a)
        | ExprKind::Try(a)
        | ExprKind::Throw(a)
        | ExprKind::Ref(a)
        | ExprKind::Spread(a) => changed_names(a, out),
        ExprKind::Binary(_, a, b) | ExprKind::ArrayRepeat(a, b) | ExprKind::Index(a, b) => {
            changed_names(a, out);
            changed_names(b, out);
        }
        ExprKind::Slice(base, start, end) => {
            changed_names(base, out);
            start.iter().chain(end).for_each(|a| changed_names(a, out));
        }
        ExprKind::Call(callee, args) => {
            changed_names(callee, out);
            args.iter().for_each(|a| changed_names(a, out));
        }
        ExprKind::ArrayLit(items) => items.iter().for_each(|a| changed_names(a, out)),
        ExprKind::StructLit(_, fields) => fields.iter().for_each(|f| changed_names(&f.value, out)),
        ExprKind::Catch { value, handler, .. } => {
            changed_names(value, out);
            if let ast::CatchHandler::Value(v) = handler {
                changed_names(v, out);
            }
        }
    }
}

/// The blocks nested directly in a statement: its branches, arms and
/// bodies, and the blocks of the `catch`es in its own expressions.
fn child_blocks(s: &Stmt) -> Vec<&ast::Block> {
    let mut blocks = Vec::new();
    for e in own_exprs(s) {
        catch_blocks(e, &mut blocks);
    }
    match s {
        Stmt::Let {
            otherwise: Some(b), ..
        } => blocks.push(b),
        Stmt::Match { arms, .. } => blocks.extend(arms.iter().map(|arm| &arm.body)),
        Stmt::If(i) => {
            let mut cur = Some(i);
            while let Some(i) = cur {
                blocks.push(&i.then);
                cur = match &i.otherwise {
                    Some(ast::Else::If(next)) => Some(next),
                    Some(ast::Else::Block(b)) => {
                        blocks.push(b);
                        None
                    }
                    None => None,
                };
            }
        }
        Stmt::While { body, .. }
        | Stmt::Loop { body, .. }
        | Stmt::For { body, .. }
        | Stmt::Unsafe(body)
        | Stmt::Defer { body, .. } => blocks.push(body),
        _ => {}
    }
    blocks
}

/// Names assigned anywhere in `stmts` (for forgetting facts at loop heads),
/// including through `&` and method calls (see [`changed_names`]).
fn assigned_names(stmts: &[Stmt], out: &mut HashSet<String>) {
    for s in stmts {
        for e in own_exprs(s) {
            changed_names(e, out);
        }
        if let Stmt::Assign { target, .. } = s {
            // `a[i] = v` and `p.x = v` assign (part of) `a` and `p`.
            let root = place_root(target);
            if let ExprKind::Name(n) = &root.kind {
                out.insert(n.clone());
            }
        }
        for b in child_blocks(s) {
            assigned_names(&b.stmts, out);
        }
    }
}

/// Names assigned whole anywhere in `stmts`, by `name = v` or `name op= v`
/// (not through a field, an element, `&` or a method call). A view can
/// change only this way: `&` and a method's receiver change elements.
fn whole_assigned_names(stmts: &[Stmt], out: &mut HashSet<String>) {
    for s in stmts {
        if let Stmt::Assign { target, .. } = s
            && let ExprKind::Name(n) = &target.kind
        {
            out.insert(n.clone());
        }
        for b in child_blocks(s) {
            whole_assigned_names(&b.stmts, out);
        }
    }
}

/// The height of the loops in `stmts`: 0 without loops, otherwise one more
/// than the height of the loops in the body of the highest one (loops at
/// any depth in blocks count, as do loops in `catch` blocks).
fn loop_height(stmts: &[Stmt]) -> u32 {
    stmts
        .iter()
        .map(|s| {
            let inner = child_blocks(s)
                .iter()
                .map(|b| loop_height(&b.stmts))
                .max()
                .unwrap_or(0);
            match s {
                Stmt::While { .. }
                | Stmt::Loop { .. }
                | Stmt::For {
                    comptime: false, ..
                } => inner + 1,
                _ => inner,
            }
        })
        .max()
        .unwrap_or(0)
}

/// The highest loop whose head is searched for among the candidates of
/// docs/safety.md ("Facts through loops"). A higher loop (one with more
/// than `SEARCH_HEIGHT - 1` loops nested one in another inside it) takes
/// the simplest head, which forgets every fact about the variables it
/// assigns, and its body is checked once. So no chain of nested loops
/// multiplies the checks by more than the search does for this many
/// loops, whatever the nesting.
const SEARCH_HEIGHT: u32 = 4;

/// The locals assigned anywhere in `body`, as seen from before it (for the
/// facts at a loop's head).
fn assigned_locals(cx: &FnCx, body: &[Stmt]) -> HashSet<LocalId> {
    let mut names = HashSet::new();
    assigned_names(body, &mut names);
    let mut whole = HashSet::new();
    whole_assigned_names(body, &mut whole);
    // An `inout` slice is never assigned itself, only its elements, which
    // have no facts: its length stays. Another view keeps its length unless
    // it's assigned whole.
    names
        .iter()
        .filter_map(|n| cx.lookup(n).map(|l| (n, l)))
        .filter(|&(n, l)| {
            let local = &cx.locals[l];
            !local.mutable_view() && (!local.ty.is_view() || whole.contains(n))
        })
        .map(|(_, l)| l)
        .collect()
}

/// The values `term` can take by its type, for the locals' types `tys`.
fn term_full(tys: &[Ty], term: Term) -> Range {
    term_full_by(|l| tys[l], term)
}

/// [`term_full`], with the locals' types given by `ty_of`.
fn term_full_by(ty_of: impl Fn(LocalId) -> Ty, term: Term) -> Range {
    let any = Range {
        lo: i128::MIN,
        hi: i128::MAX,
    };
    match term {
        Term::Local(l) => type_range(ty_of(l)).unwrap_or(any),
        // No object is bigger than the largest `isize` (as in `view_len`).
        Term::Len(_) => Range {
            lo: 0,
            hi: i128::from(i64::MAX),
        },
        Term::Field(l, k) => flat_field(ty_of(l), k).and_then(type_range).unwrap_or(any),
    }
}

/// The index of a `for` loop, for the facts at the loop's head: its local,
/// and the range and term (if any) of the start it counts from.
struct ForIndex {
    local: LocalId,
    start: Range,
    start_term: Option<Linear>,
}

/// The relations added to the facts before a loop, `E`, so that the loop's
/// head can keep them (docs/safety.md, "Facts through loops"). For each
/// two integer locals `v` and `w` of `assigned`, `v - w <= c` with the
/// tightest `c` that `E` gives (see [`Env::diff`]). For a `for` loop's
/// `index` `i`, which starts at `s`, `v - i <= c` with `c` from `v - s`:
/// the largest `v` minus the smallest `s`, or a relation with `s`.
fn head_relations(
    env: &Env,
    tys: &[Ty],
    assigned: &HashSet<LocalId>,
    index: Option<&ForIndex>,
) -> Vec<facts::Fact> {
    let mut vars: Vec<LocalId> = assigned
        .iter()
        .copied()
        .filter(|&l| index.is_none_or(|ix| ix.local != l))
        .filter(|&l| type_range(tys[l]).is_some())
        .collect();
    vars.sort_unstable();
    let mut out = Vec::new();
    for &v in &vars {
        for &w in &vars {
            if v == w {
                continue;
            }
            if let Some(c) = env.diff(Term::Local(v), Term::Local(w)) {
                out.push(facts::Fact::Rel {
                    a: Term::Local(v),
                    b: Term::Local(w),
                    c,
                });
            }
        }
        if let Some(ix) = index {
            let v_lin = Linear::of(Term::Local(v));
            let by_range = env
                .range(Term::Local(v))
                .and_then(|r| r.hi.checked_sub(ix.start.lo));
            let by_rel = ix.start_term.and_then(|s| env.diff_bound(v_lin, s));
            let c = match (by_range, by_rel) {
                (Some(x), Some(y)) => Some(x.min(y)),
                (x, y) => x.or(y),
            };
            if let Some(c) = c {
                out.push(facts::Fact::Rel {
                    a: Term::Local(v),
                    b: Term::Local(ix.local),
                    c,
                });
            }
        }
    }
    out
}

/// A comparison of `l` and `r` was checked: when one side is a term plus a
/// constant `d` and the other a single value `k`, `k - d` is a threshold
/// of the term for every loop around (docs/safety.md, "Facts through
/// loops").
fn note_thresholds(cx: &mut FnCx, l: facts::Side, r: facts::Side) {
    for (x, k) in [(l, r), (r, l)] {
        if let Some(lin) = x.term
            && k.range.lo == k.range.hi
            && let Some(v) = k.range.lo.checked_sub(lin.offset)
        {
            for edges in &mut cx.loops {
                if !edges.thresholds.contains(&(lin.term, v)) {
                    edges.thresholds.push((lin.term, v));
                }
            }
        }
    }
}

/// The range of `term` where an expression reads it: its known range,
/// narrowed by its relations (see [`Env::range_via`]).
fn read_range(cx: &FnCx, term: Term) -> Option<Range> {
    cx.env
        .range_via(term, |t| term_full_by(|l| cx.locals[l].ty, t))
}

/// The type of field number `k` of a value of type `ty`, numbered as in
/// [`Term::Field`].
fn flat_field(ty: Ty, mut k: u32) -> Option<Ty> {
    let Some(def) = ty.as_struct() else {
        return (k == 0).then_some(ty);
    };
    for f in &def.fields {
        let n = expr::flat_size(f.ty);
        if k < n {
            return flat_field(f.ty, k);
        }
        k -= n;
    }
    None
}

/// The variable a place like `a[i].x` or `a[i..j]` is part of: the
/// expression under its indexes, slices and fields.
fn place_root(mut e: &ast::Expr) -> &ast::Expr {
    while let ExprKind::Index(base, _) | ExprKind::Field(base, _) | ExprKind::Slice(base, ..) =
        &e.kind
    {
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
    // A generic type as declared is shown by its name alone.
    let shown = if ty.is_decl_form() {
        expr::nominal_name(ty)
    } else {
        ty.to_string()
    };
    if let Some(def) = ty.as_struct() {
        return def
            .fields
            .iter()
            .map(|f| (format!("{shown}.{}", f.name), f.ty))
            .collect();
    }
    let def = ty.as_enum().expect("a struct or an enum");
    def.variants
        .iter()
        .flat_map(|v| {
            let shown = &shown;
            v.fields
                .iter()
                .map(move |f| (format!("{shown}.{}.{}", v.name, f.name), f.ty))
        })
        .collect()
}

/// What the structs and enums of a program hold by value: for each
/// declaration (by its declared form, [`Ty::decl`]), the declarations of
/// the structs and enums it holds, and which of its own parameters (by
/// position) it holds, through other types too. A fixed point over the
/// declarations, so it's found even when instances grow without end.
struct HeldBy {
    types: Vec<Ty>,
    decls: HashMap<Ty, HashSet<Ty>>,
    params: HashMap<Ty, HashSet<usize>>,
}

impl HeldBy {
    fn new(types: Vec<Ty>) -> HeldBy {
        let mut h = HeldBy {
            decls: types.iter().map(|&t| (t, HashSet::new())).collect(),
            params: types.iter().map(|&t| (t, HashSet::new())).collect(),
            types,
        };
        h.update();
        h
    }

    /// Recompute the fixed point (after a member was cleared).
    fn update(&mut self) {
        for t in &self.types {
            self.decls.insert(*t, HashSet::new());
            self.params.insert(*t, HashSet::new());
        }
        loop {
            let mut changed = false;
            for &t in &self.types {
                let own = t.decl_params();
                let (mut ds, mut ps) = (HashSet::new(), HashSet::new());
                for (_, m) in members(t) {
                    self.held(m, &own, &mut ds, &mut ps);
                }
                if ds.len() != self.decls[&t].len() || ps.len() != self.params[&t].len() {
                    changed = true;
                }
                self.decls.insert(t, ds);
                self.params.insert(t, ps);
            }
            if !changed {
                return;
            }
        }
    }

    /// Add what a value of type `ty` holds, inside a declaration whose own
    /// parameters are `own`, to `ds` and `ps`.
    fn held(&self, ty: Ty, own: &[Ty], ds: &mut HashSet<Ty>, ps: &mut HashSet<usize>) {
        match ty {
            Ty::Param(_) => ps.extend(own.iter().position(|&p| p == ty)),
            Ty::Array(_) => {
                let (elem, _) = ty.as_array().expect("an array");
                self.held(elem, own, ds, ps);
            }
            Ty::Optional(_) => {
                self.held(ty.as_optional().expect("an optional"), own, ds, ps);
            }
            Ty::Struct(_) | Ty::Enum(_) => {
                let key = ty.decl();
                ds.insert(key);
                if let Some(more) = self.decls.get(&key) {
                    ds.extend(more.iter().copied());
                }
                let args = ty.type_args();
                for &k in self.params.get(&key).into_iter().flatten() {
                    self.held(args[k], own, ds, ps);
                }
            }
            _ => {}
        }
    }

    /// The first member of `ty`'s declaration through which it holds
    /// `target`'s.
    fn leading_member(&self, ty: Ty, target: Ty) -> usize {
        let own = ty.decl_params();
        members(ty)
            .iter()
            .position(|&(_, m)| {
                let (mut ds, mut ps) = (HashSet::new(), HashSet::new());
                self.held(m, &own, &mut ds, &mut ps);
                ds.contains(&target)
            })
            .expect("a member leads back")
    }
}

/// Make member `k` (numbered as in [`members`]) of a struct or an enum `()`,
/// to break a cycle that was reported.
fn clear_member(ty: Ty, k: usize) {
    // In the declaration: an instance's members are its declaration's.
    let ty = ty.decl();
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
        Ty::Int(_)
        | Ty::Bool
        | Ty::Array(_)
        | Ty::Struct(_)
        | Ty::Enum(_)
        | Ty::Optional(_)
        | Ty::Param(_) => Ok(()),
        Ty::Str | Ty::Slice(_) => Err(Some(())),
        Ty::Ptr(_) | Ty::Unit | Ty::Never | Ty::Result(_) | Ty::Value(_) => Err(None),
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
        convention: None,
        drop_flag: false,
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

/// The statements that destroy the parts of the value of `local`, of type
/// `ty` (in a `deinit`, its `self`): a struct's fields in reverse order, or
/// the payload of an enum's variant, those that aren't `Copy`.
fn destroy_fields(local: LocalId, ty: Ty) -> Vec<TStmt> {
    let this = TExpr {
        kind: TExprKind::Local(local),
        ty,
    };
    let destroy = |kind: TExprKind, ty: Ty| TStmt::Destroy(TExpr { kind, ty });
    if let Some(def) = ty.as_struct() {
        return (0..def.fields.len())
            .rev()
            .filter(|&k| !def.fields[k].ty.is_copy())
            .map(|k| {
                destroy(
                    TExprKind::Field(Box::new(this.clone()), k as u32),
                    def.fields[k].ty,
                )
            })
            .collect();
    }
    let Some(def) = ty.as_enum() else {
        return Vec::new();
    };
    if def
        .variants
        .iter()
        .all(|v| v.fields.iter().all(|f| f.ty.is_copy()))
    {
        return Vec::new();
    }
    let arms = def
        .variants
        .iter()
        .enumerate()
        .map(|(v, variant)| TArm {
            variants: vec![v as u32],
            body: (0..variant.fields.len())
                .rev()
                .filter(|&k| !variant.fields[k].ty.is_copy())
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
}

/// Whether a checked expression is the result of a call that throws.
fn ty_is_result(c: &expr::Checked) -> bool {
    c.ty().as_result().is_some()
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
/// The most names [`name_list`] shows.
const LISTED_NAMES: usize = 8;

/// `names` joined with commas for a message, the first [`LISTED_NAMES`] of
/// them if there are more (with how many are left out).
fn name_list(names: &[String]) -> String {
    if names.len() <= LISTED_NAMES {
        return names.join(", ");
    }
    format!(
        "{} and {} more",
        names[..LISTED_NAMES].join(", "),
        names.len() - LISTED_NAMES
    )
}

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
        let mut file_items = Vec::new();
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

                let mut items = Vec::new();
                self.active_items(&file.items, &mut items);
                // Traits first, so every bound can name them.
                self.declare_trait_names(&items, pkg, file.id, |n| {
                    Self::shown_name(packages, pkg, n)
                });
                file_items.push((pkg, file, items));
            }
        }
        if !self.package_error {
            self.declare_trait_items();
        }
        for (pkg, file, items) in file_items {
            {
                for item in items {
                    let (name, entry) = match item {
                        ast::Item::Trait(t) => {
                            let k = self
                                .traits
                                .iter()
                                .position(|i| std::ptr::eq(i.decl, t))
                                .expect("a declared trait");
                            for item in &t.items {
                                if let ast::TraitItem::Method { decl, default } = item {
                                    let id = fns.len();
                                    fns.push((&**decl, pkg, file.id));
                                    self.members.insert(id, traits::Member::Trait(k, *default));
                                    self.traits[k].methods.push((
                                        decl.name.name.clone(),
                                        id,
                                        *default,
                                    ));
                                    self.dispatch.trait_fns.insert(
                                        id,
                                        (self.traits[k].trait_, decl.name.name.clone()),
                                    );
                                }
                            }
                            continue;
                        }
                        ast::Item::Impl(i) => {
                            let k = self.impls.len();
                            let mut methods = Vec::new();
                            for item in &i.items {
                                if let ast::ImplItem::Method(decl) = item {
                                    let id = fns.len();
                                    fns.push((decl, pkg, file.id));
                                    self.members.insert(id, traits::Member::Impl(k));
                                    if methods.iter().any(|(n, _)| *n == decl.name.name) {
                                        self.error(
                                            decl.name.span,
                                            format!(
                                                "`{}` is defined more than once in this `impl`",
                                                decl.name.name
                                            ),
                                        );
                                        continue;
                                    }
                                    methods.push((decl.name.name.clone(), id));
                                }
                            }
                            self.impls.push(traits::ImplInfo {
                                decl: i,
                                pkg,
                                file: file.id,
                                head: None,
                                params: Vec::new(),
                                bounds: Vec::new(),
                                methods,
                            });
                            continue;
                        }
                        // Methods and associated functions are found
                        // through their type, once types are known.
                        ast::Item::Fn(f) if f.owner.is_some() => {
                            fns.push((f, pkg, file.id));
                            continue;
                        }
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
                            let mut gcx = FnCx::new(pkg, file.id, Ty::Unit, false);
                            self.no_pack(&s.generics, "a struct's");
                            self.no_generic_refine(&s.generics);
                            let (params, _) = self.declare_generics(&mut gcx, &s.generics);
                            let ty = Ty::new_struct(shown, pkg, s.is_pub, params);
                            self.check_type_name(&s.name);
                            structs.push((s, pkg, file.id, ty));
                            (&s.name, Item::Type(ty))
                        }
                        ast::Item::Enum(e) => {
                            let shown = Self::shown_name(packages, pkg, &e.name.name);
                            let mut gcx = FnCx::new(pkg, file.id, Ty::Unit, false);
                            self.no_pack(&e.generics, "an enum's");
                            self.no_generic_refine(&e.generics);
                            let (params, _) = self.declare_generics(&mut gcx, &e.generics);
                            let ty = Ty::new_enum(shown, pkg, e.is_pub, params);
                            self.check_type_name(&e.name);
                            enums.push((e, pkg, file.id, ty));
                            (&e.name, Item::Type(ty))
                        }
                        ast::Item::Type(t) => {
                            self.refined_types.push(RefinedType {
                                decl: t,
                                pkg,
                                file: file.id,
                                state: RefinedState::Unresolved,
                            });
                            self.check_type_name(&t.name);
                            (&t.name, Item::Refined(self.refined_types.len() - 1))
                        }
                        ast::Item::If(_) | ast::Item::CompileError(_) => {
                            unreachable!("replaced by `active_items`")
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
        // A package that can't be compiled for the target said so: what uses
        // it would only give errors that follow from that one.
        if self.package_error {
            return;
        }
        // Field types and signatures come once every item is known: an array
        // length in a type can name a constant declared further down, and a
        // field's type a struct declared further down. The bounds of the
        // generic types they name are checked once every field is known.
        // The types that declare a `deinit` aren't `Copy`, which the bounds
        // checked below and every signature depend on.
        for &(f, pkg, _) in &fns {
            if f.name.name == DEINIT
                && let Some(TypeExpr::Named(t)) = &f.owner
                && let Some(Item::Type(ty)) = self.pkgs[pkg].items.get(&t.name)
            {
                ty.set_deinit();
            }
        }
        self.pending_bounds = Some(Vec::new());
        for &(s, pkg, file, ty) in &structs {
            let fields = self.struct_fields(s, pkg, file, ty);
            ty.set_fields(fields);
        }
        for &(e, pkg, file, ty) in &enums {
            let (tag, explicit, variants) = self.enum_variants(e, pkg, file, ty);
            ty.set_variants(tag, explicit, variants);
        }
        let nominal: Vec<(&ast::Ident, &str, Ty)> = structs
            .iter()
            .map(|&(s, _, _, ty)| (&s.name, "struct", ty))
            .chain(enums.iter().map(|&(e, _, _, ty)| (&e.name, "enum", ty)))
            .collect();
        self.check_recursion(&nominal);
        // The impls are registered before the bounds are checked: an impl
        // can make a type satisfy one.
        self.declare_impls();
        for (ty, span) in self.pending_bounds.take().unwrap_or_default() {
            self.check_type_bounds(ty, span);
        }
        let mut owners = Vec::new();
        for (id, &(f, pkg, file)) in fns.iter().enumerate() {
            let owner = f
                .owner
                .as_ref()
                .and_then(|o| self.method_owner(o, &f.name, id, pkg, file));
            owners.push(owner);
        }
        for (id, (&(f, pkg, file), owner)) in fns.iter().zip(owners).enumerate() {
            let sig = match self.members.get(&id) {
                Some(&traits::Member::Trait(k, _)) => self.trait_method_sig(f, k),
                Some(&traits::Member::Impl(k)) => self.impl_method_sig(f, k),
                None => {
                    let mut cx = FnCx::new(pkg, file, Ty::Unit, false);
                    self.signature(&mut cx, f, owner)
                }
            };
            self.sigs.push(sig);
        }
        for (id, &(f, _, _)) in fns.iter().enumerate() {
            if f.name.name == DEINIT && f.owner.is_some() {
                self.check_deinit(id, f);
            }
        }
        self.check_impls();
        self.func_states = fns.iter().map(|_| FuncState::Unchecked).collect();
        self.fn_decls = fns;
    }

    /// The items of a file that are compiled for the target: those outside
    /// any `if comptime`, and those in the branches the target picks. A
    /// `compile_error` among them is reported.
    fn active_items(&mut self, items: &'a [ast::Item], out: &mut Vec<&'a ast::Item>) {
        for item in items {
            match item {
                ast::Item::If(i) => {
                    let mut branch = Some(i);
                    while let Some(i) = branch.take() {
                        match self.item_cond(&i.cond) {
                            Some(true) => self.active_items(&i.then, out),
                            Some(false) => match &i.otherwise {
                                Some(ast::ItemElse::If(inner)) => branch = Some(inner),
                                Some(ast::ItemElse::Items(items)) => self.active_items(items, out),
                                None => {}
                            },
                            None => {}
                        }
                    }
                }
                ast::Item::CompileError(call) => {
                    self.compile_error(call);
                    self.package_error = true;
                }
                _ => out.push(item),
            }
        }
    }

    /// Report `compile_error("message")`, reached in code compiled for the
    /// target.
    fn compile_error(&mut self, call: &ast::Expr) {
        let ExprKind::Call(_, args) = &call.kind else {
            unreachable!("a call of `compile_error`")
        };
        match args.as_slice() {
            [
                ast::Expr {
                    kind: ExprKind::Str(msg),
                    ..
                },
            ] => {
                let msg = String::from_utf8_lossy(msg).into_owned();
                self.diags.push(Diagnostic::error(call.span, msg).with_help(
                    "`compile_error` is an error in the code compiled for the target: outside of `if comptime`, or in a branch the target takes",
                ));
            }
            _ => self.error(call.span, "`compile_error` takes one string literal"),
        }
    }

    /// The value of a package-level `if comptime` condition. It's evaluated
    /// before names are resolved, so it can only use `target`, literals,
    /// comparisons, `&&`, `||` and `!` (docs/generics.md, What M7 needs).
    fn item_cond(&mut self, e: &ast::Expr) -> Option<bool> {
        match self.cond_value(e)? {
            CondVal::Bool(b) => Some(b),
            _ => {
                self.error(e.span, "the condition of `if comptime` must be a `bool`");
                None
            }
        }
    }

    fn cond_value(&mut self, e: &ast::Expr) -> Option<CondVal> {
        use ast::{BinOp, UnOp};
        match &e.kind {
            ExprKind::Bool(b) => Some(CondVal::Bool(*b)),
            ExprKind::Int(v) => match i128::try_from(*v) {
                Ok(v) => Some(CondVal::Int(v)),
                Err(_) => {
                    self.error(e.span, "integer literal is too large");
                    None
                }
            },
            ExprKind::Paren(inner) => self.cond_value(inner),
            ExprKind::Dot(name) => Some(CondVal::Dot(name.clone())),
            ExprKind::Unary(UnOp::Not, inner) => match self.cond_value(inner)? {
                CondVal::Bool(b) => Some(CondVal::Bool(!b)),
                _ => {
                    self.error(inner.span, "`!` needs a `bool`");
                    None
                }
            },
            ExprKind::Field(base, member) if matches!(&base.kind, ExprKind::Name(n) if n == TARGET) =>
            {
                let (ty, v) = self.target_field(member)?;
                Some(match ty {
                    Ty::Int(_) => CondVal::Int(v),
                    _ => CondVal::Enum(ty, v as u32),
                })
            }
            ExprKind::Binary(op @ (BinOp::And | BinOp::Or), l, r) => {
                let (a, b) = (self.cond_value(l), self.cond_value(r));
                match (a?, b?) {
                    (CondVal::Bool(a), CondVal::Bool(b)) => {
                        Some(CondVal::Bool(if *op == BinOp::And {
                            a && b
                        } else {
                            a || b
                        }))
                    }
                    _ => {
                        self.error(e.span, format!("`{}` needs `bool` operands", op.as_str()));
                        None
                    }
                }
            }
            ExprKind::Binary(
                op @ (BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge),
                l,
                r,
            ) => {
                let (a, b) = (self.cond_value(l), self.cond_value(r));
                let (a, b) = (a?, b?);
                let equality = matches!(op, BinOp::Eq | BinOp::Ne);
                let ord = match (&a, &b) {
                    (CondVal::Int(x), CondVal::Int(y)) => x.cmp(y),
                    (CondVal::Bool(x), CondVal::Bool(y)) if equality => x.cmp(y),
                    (CondVal::Enum(t, x), CondVal::Enum(u, y)) if t == u && equality => x.cmp(y),
                    (CondVal::Enum(t, x), CondVal::Dot(name))
                    | (CondVal::Dot(name), CondVal::Enum(t, x))
                        if equality =>
                    {
                        let def = t.as_enum().expect("an enum");
                        let Some((k, _)) = def.variant(&name.name) else {
                            let names: Vec<String> = def
                                .variants
                                .iter()
                                .map(|v| format!("`.{}`", v.name))
                                .collect();
                            self.diags.push(
                                Diagnostic::error(
                                    name.span,
                                    format!("`{t}` has no variant `{}`", name.name),
                                )
                                .with_help(format!("its variants are {}", names.join(", "))),
                            );
                            return None;
                        };
                        x.cmp(&(k as u32))
                    }
                    _ => {
                        self.error(
                            e.span,
                            format!("`{}` can't compare these values", op.as_str()),
                        );
                        return None;
                    }
                };
                let r = match op {
                    BinOp::Eq => ord.is_eq(),
                    BinOp::Ne => ord.is_ne(),
                    BinOp::Lt => ord.is_lt(),
                    BinOp::Le => ord.is_le(),
                    BinOp::Gt => ord.is_gt(),
                    _ => ord.is_ge(),
                };
                Some(CondVal::Bool(r))
            }
            _ => {
                self.diags.push(
                    Diagnostic::error(
                        e.span,
                        "a package-level `if comptime` condition can only use `target`, literals, comparisons, `&&`, `||` and `!`",
                    )
                    .with_help("it's evaluated before the package's names are known"),
                );
                None
            }
        }
    }

    /// The type and value of `target.name`: an enum variant's index, or an
    /// integer.
    fn target_field(&mut self, member: &ast::Ident) -> Option<(Ty, i128)> {
        let types = crate::target::types();
        let def = types.target.as_struct().expect("a struct");
        let Some((k, ty)) = def.field(&member.name) else {
            let fields: Vec<String> = crate::target::FIELD_NAMES
                .iter()
                .map(|n| format!("`{n}`"))
                .collect();
            self.diags.push(
                Diagnostic::error(
                    member.span,
                    format!("`target` has no field `{}`", member.name),
                )
                .with_help(format!("its fields are {}", fields.join(", "))),
            );
            return None;
        };
        Some((ty, self.target.field_values()[k]))
    }

    /// The value of `target`, of the built-in struct `target.Target`.
    fn target_value(&self) -> TExpr {
        let types = crate::target::types();
        let def = types.target.as_struct().expect("a struct");
        let fields = def
            .fields
            .iter()
            .zip(self.target.field_values())
            .enumerate()
            .map(|(k, (f, v))| (k as u32, scalar_expr(f.ty, v)))
            .collect();
        TExpr {
            kind: TExprKind::StructLit(fields),
            ty: types.target,
        }
    }

    /// Whether `e` is a call of `compile_error`, as a statement (unless a
    /// variable or an item of that name hides it).
    fn is_compile_error(&self, cx: &FnCx, e: &ast::Expr) -> bool {
        matches!(&e.kind, ExprKind::Call(callee, _)
            if matches!(&callee.kind, ExprKind::Name(n)
                if (n == COMPILE_ERROR || n == COMPILE_ERROR_AT)
                    && cx.lookup(n).is_none()
                    && !self.pkgs[cx.pkg].items.contains_key(n)))
    }

    /// The type `fn Owner.name` belongs to: a struct or an enum declared in
    /// the same package. Registers the function `id` as its method `name`,
    /// unless that clashes with a field, a variant or another method.
    fn method_owner(
        &mut self,
        owner: &TypeExpr,
        name: &ast::Ident,
        id: FuncId,
        pkg: usize,
        file: FileId,
    ) -> Option<Ty> {
        let ty = match owner {
            TypeExpr::Named(t) => match self.pkgs[pkg].items.get(&t.name) {
                Some(Item::Type(ty)) => *ty,
                _ if primitive(&t.name, self.ptr_bits).is_some() => {
                    self.diags.push(
                        Diagnostic::error(
                            t.span,
                            format!("`{}` is a built-in type: it can't have methods", t.name),
                        )
                        .with_help("methods belong to the structs and enums a package declares"),
                    );
                    return None;
                }
                Some(_) => {
                    self.error(t.span, format!("`{}` is not a type", t.name));
                    return None;
                }
                None => {
                    self.error(t.span, format!("unknown type `{}`", t.name));
                    return None;
                }
            },
            TypeExpr::Qualified(p, t) => {
                let path = self
                    .imports
                    .get(&file)
                    .and_then(|m| m.get(&p.name))
                    .map(|&k| self.pkgs[k].path.clone());
                let whose = match path {
                    Some(path) => format!("package `{path}`"),
                    None => format!("package `{}`", p.name),
                };
                self.diags.push(
                    Diagnostic::error(
                        owner.span(),
                        format!(
                            "the methods of `{}.{}` can only be declared in {whose}, which declares it",
                            p.name, t.name
                        ),
                    )
                    .with_help(
                        "every method of a type is declared next to the type (docs/types.md, Methods)",
                    ),
                );
                return None;
            }
            _ => unreachable!("the parser gives a name or `pkg.Name`"),
        };
        let n = &name.name;
        let clash = if let Some(def) = ty.as_struct() {
            def.field(n).map(|_| "a field")
        } else {
            ty.as_enum()
                .and_then(|def| def.variant(n).map(|_| "a variant"))
        };
        if let Some(what) = clash {
            self.diags.push(
                Diagnostic::error(
                    name.span,
                    format!("`{ty}` has {what} `{n}`, so it can't also have a method `{n}`"),
                )
                .with_help("give the method another name"),
            );
            return Some(ty);
        }
        if self.methods.contains_key(&(ty, n.clone())) {
            self.error(name.span, format!("`{ty}.{n}` is defined more than once"));
            return Some(ty);
        }
        self.methods.insert((ty, n.clone()), id);
        Some(ty)
    }

    /// Which function the compiler implements, for a declaration marked
    /// `@intrinsic`: only in the standard library, by its name.
    fn intrinsic(&mut self, cx: &FnCx, f: &ast::FnDecl) -> Option<Intrinsic> {
        if !f.intrinsic {
            return None;
        }
        if !self.pkgs[cx.pkg].path.starts_with("std/") || f.owner.is_some() {
            self.error(
                f.name.span,
                "`@intrinsic` is only for the functions of the standard library that the compiler implements",
            );
            return None;
        }
        match f.name.name.as_str() {
            "swap" => Some(Intrinsic::Swap),
            "forget" => Some(Intrinsic::Forget),
            "take" => Some(Intrinsic::Take),
            other => {
                self.error(
                    f.name.span,
                    format!("the compiler has no intrinsic `{other}`"),
                );
                None
            }
        }
    }

    /// Check the declaration of `fn T.deinit(sink self)`, function `id`:
    /// `sink self` and nothing else, no result, no error, no parameters or
    /// bounds of its own, not `unsafe` (docs/allocation.md, Declaring
    /// destruction).
    fn check_deinit(&mut self, id: FuncId, f: &ast::FnDecl) {
        self.deinits.insert(id);
        let sig = &self.sigs[id];
        let owner = sig.name.rsplit_once('.').map_or("T", |(t, _)| t).to_owned();
        let shape = sig.has_self
            && sig.params.len() == 1
            && sig.params[0].1 == Convention::Sink
            && sig.ret == Ty::Unit;
        let mut errors = Vec::new();
        if !shape {
            errors.push(
                Diagnostic::error(
                    f.name.span,
                    "`deinit` takes `sink self` and nothing else, and returns nothing",
                )
                .with_help(format!("declare it `fn {owner}.deinit(sink self)`")),
            );
        }
        if sig.throws.is_some() {
            errors.push(
                Diagnostic::error(f.name.span, "`deinit` can't throw")
                    .with_help("destruction runs at the end of scopes, also in functions that don't throw")
                    .with_help("a type whose cleanup can fail offers a method like `close(sink self) throws(E)`, and its `deinit` does the same cleanup and ignores the error"),
            );
        }
        if sig.is_unsafe {
            errors.push(
                Diagnostic::error(
                    f.name.span,
                    "`deinit` can't be `unsafe`: destruction runs in safe code",
                )
                .with_help("use an `unsafe` block in its body"),
            );
        }
        if sig.type_params.len() > sig.owner_params {
            errors.push(Diagnostic::error(
                f.name.span,
                "`deinit` can't have generic parameters of its own",
            ));
        }
        let decl = self
            .methods
            .iter()
            .find(|&(_, &m)| m == id)
            .map(|((t, _), _)| *t);
        if let Some(decl) = decl {
            let added = decl.decl_params().iter().zip(&sig.bounds).any(|(p, b)| {
                b.iter()
                    .any(|t| !self.declared_bounds.get(p).is_some_and(|d| d.contains(t)))
            });
            if added {
                errors.push(
                    Diagnostic::error(
                        f.name.span,
                        "`deinit` can't add bounds to the type's parameters",
                    )
                    .with_help(
                        "every value of every instance is destroyed: declare it for all of them",
                    ),
                );
            }
        }
        self.diags.extend(errors);
    }

    /// The fields of a struct declaration. A field whose type is in error
    /// gets the type `()`, so later checks see no more problems with it.
    fn struct_fields(
        &mut self,
        s: &ast::StructDecl,
        pkg: usize,
        file: FileId,
        ty: Ty,
    ) -> Vec<Field> {
        let mut cx = FnCx::new(pkg, file, Ty::Unit, false);
        cx.type_params = ty.decl_params();
        let mut fields: Vec<Field> = Vec::new();
        // The named refinements of the fields' types, by field.
        let mut named = Vec::new();
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
            let (ty, r) = match self.resolve_refined(&mut cx, &f.ty) {
                Some((ty, r)) => (self.storable_field(ty, &f.ty, "struct"), r),
                None => (Ty::Unit, None),
            };
            named.push((fields.len(), f, r));
            if let Some(at) = f.uninit {
                self.check_uninit_field(f, at, ty);
            }
            fields.push(Field {
                name: f.name.name.clone(),
                ty,
                is_pub: f.is_pub,
                read_only: f.read_only,
                uninit: f.uninit.is_some(),
            });
        }
        // The refinements, which can name any field.
        let mut refines = Vec::new();
        for (j, f, r) in named {
            let written = match &f.refine {
                Some(e) => {
                    let scope = refine::Scope {
                        params: &[],
                        visible: 0,
                        own: None,
                        result: None,
                        fields: Some((&fields, j)),
                        self_ty: None,
                    };
                    let w = self.refinement(&mut cx, e, &scope);
                    if w.is_some() && type_range(fields[j].ty).is_none() {
                        self.error(
                            f.ty.span(),
                            format!("a refined field is an integer, not a `{}`", fields[j].ty),
                        );
                        None
                    } else {
                        w
                    }
                }
                None => None,
            };
            if let Some(r) = refine::Refine::and(r, written) {
                refines.push((j, r));
            }
        }
        if !refines.is_empty() {
            self.field_refines.insert(ty, refines);
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
    /// An `@uninit` field must be private and an array of integers: only
    /// its package's methods can read it, and an integer of it read before
    /// it's written is merely unknown (docs/safety.md, "The trusted
    /// boundary").
    fn check_uninit_field(&mut self, f: &ast::FieldDecl, at: Span, ty: Ty) {
        if f.is_pub {
            self.diags.push(
                Diagnostic::error(at, "an `@uninit` field can't be `pub`").with_help(
                    "only the struct's package may read it, after writing the part it reads",
                ),
            );
        }
        let ints = ty
            .as_array()
            .is_some_and(|(elem, _)| matches!(elem, Ty::Int(_)));
        if ty != Ty::Unit && !ints {
            self.error(
                f.ty.span(),
                format!("an `@uninit` field must be an array of integers, not `{ty}`"),
            );
        }
    }

    fn field_type(&mut self, cx: &mut FnCx, t: &TypeExpr, what: &str) -> Ty {
        let Some(ty) = self.resolve_type(cx, t) else {
            return Ty::Unit;
        };
        self.storable_field(ty, t, what)
    }

    /// `ty`, written `t`, if a field of a `what` can have it; `()` after
    /// an error.
    fn storable_field(&mut self, ty: Ty, t: &TypeExpr, what: &str) -> Ty {
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
        ty: Ty,
    ) -> (IntTy, bool, Vec<Variant>) {
        let mut cx = FnCx::new(pkg, file, Ty::Unit, false);
        cx.type_params = ty.decl_params();
        if e.tag.is_some() && !e.generics.is_empty() {
            self.error(
                e.name.span,
                "a C-style enum (with integer values) can't be generic",
            );
        }
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
                        fields.push(Field::public(f.name.name.clone(), ty));
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
        let c = self.coerce(cx, c, Ty::Int(tag), e.span)?;
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

    /// Report each struct or enum (of `decls`, with its name and its kind)
    /// that holds a value of its own type, directly or through other
    /// structs, enums, arrays and optionals: it would be infinitely large.
    /// For a generic one, any instance of it counts (`struct W[T] { w:
    /// ?W[Pair[T, T]] }`), since every instance holds one in turn. Each
    /// cycle is reported once, at the first of its types, and broken (its
    /// member leading back becomes `()`) so later checks terminate.
    fn check_recursion(&mut self, decls: &[(&ast::Ident, &str, Ty)]) {
        // The members leading from `from` to an instance of `ty`'s
        // declaration, as (type, member index), looking at no more than
        // `budget` types.
        fn path_back(
            from: Ty,
            ty: Ty,
            seen: &mut Vec<Ty>,
            path: &mut Vec<(Ty, usize)>,
            budget: &mut u32,
        ) -> bool {
            if seen.contains(&from) || *budget == 0 {
                return false;
            }
            *budget -= 1;
            seen.push(from);
            for (i, (_, mty)) in members(from).into_iter().enumerate() {
                let Some(inner) = held_nominal(mty) else {
                    continue;
                };
                path.push((from, i));
                if inner.same_decl(ty) || path_back(inner, ty, seen, path, budget) {
                    return true;
                }
                path.pop();
            }
            false
        }
        let mut holds = HeldBy::new(decls.iter().map(|&(_, _, ty)| ty).collect());
        for &(name, kind, ty) in decls {
            while holds.decls[&ty].contains(&ty) {
                let mut path = Vec::new();
                path_back(ty, ty, &mut Vec::new(), &mut path, &mut 1000);
                let holds_by = if kind == "struct" {
                    "a struct holds its fields by value"
                } else {
                    "an enum holds its payload by value"
                };
                let mut d = Diagnostic::error(
                    name.span,
                    format!("the {kind} `{}` contains itself", name.name),
                );
                if !path.is_empty() {
                    let through: Vec<String> = path
                        .iter()
                        .map(|&(t, i)| format!("`{}`", members(t)[i].0))
                        .collect();
                    d = d.with_help(format!("through {}", through.join(", then ")));
                }
                self.diags
                    .push(d.with_help(format!("{holds_by}, so it would be infinitely large")));
                // A member of its own that leads back: a member further
                // on may be another generic type's, which holds a
                // parameter.
                clear_member(ty, holds.leading_member(ty, ty));
                holds.update();
            }
        }
    }

    /// The Lode type a type expression names. `cx` is where it appears: array
    /// lengths are constant expressions evaluated there. A generic struct
    /// or enum needs its arguments (`Pair[u8, bool]`).
    fn resolve_type(&mut self, cx: &mut FnCx, t: &TypeExpr) -> Option<Ty> {
        let ty = self.resolve_type_or_decl(cx, t)?;
        if matches!(t, TypeExpr::Named(_) | TypeExpr::Qualified(..)) && ty.is_decl_form() {
            let params: Vec<String> = ty.decl_params().iter().map(Ty::to_string).collect();
            let name = generic::type_text(t);
            self.diags.push(
                Diagnostic::error(t.span(), format!("`{name}` needs its generic arguments"))
                    .with_help(format!(
                        "it takes {}: `{name}[{}]`",
                        params.len(),
                        params.join(", ")
                    )),
            );
            return None;
        }
        Some(ty)
    }

    /// Like [`Checker::resolve_type`], but a generic struct or enum named
    /// without its arguments (`Pair`) is its declared form, whose
    /// arguments a literal or a call infers.
    fn resolve_type_or_decl(&mut self, cx: &mut FnCx, t: &TypeExpr) -> Option<Ty> {
        match t {
            TypeExpr::Unit(_) => Some(Ty::Unit),
            TypeExpr::Pack(name, span) => {
                self.diags.push(
                    Diagnostic::error(
                        *span,
                        format!(
                            "`..{}` is only the type of a function's pack parameter",
                            name.name
                        ),
                    )
                    .with_help(format!(
                        "as in `fn f[..{0}: Bound](args: ..{0})`",
                        name.name
                    )),
                );
                None
            }
            TypeExpr::Array(len, elem, _) => {
                let elem_ty = self.resolve_type(cx, elem)?;
                let len = self.array_len_arg(cx, len)?;
                self.check_elem(elem_ty, "arrays", elem.span())?;
                Some(Ty::array_of(elem_ty, len))
            }
            TypeExpr::Generic(base, items, span) => {
                let ty = self.resolve_type_or_decl(cx, base)?;
                let params = ty.decl_params();
                let name = generic::type_text(base);
                if params.is_empty() {
                    self.error(
                        *span,
                        format!("`{name}` is not generic: it takes no arguments"),
                    );
                    return None;
                }
                if items.len() != params.len() {
                    self.error(
                        *span,
                        format!(
                            "`{name}` takes {} generic argument(s), but {} were given",
                            params.len(),
                            items.len()
                        ),
                    );
                    return None;
                }
                let mut args = Vec::new();
                for (item, &p) in items.iter().zip(&params) {
                    args.push(self.generic_arg(cx, item, p));
                }
                let args: Vec<Ty> = args.into_iter().collect::<Option<_>>()?;
                let inst = ty.instantiate(&args);
                self.check_type_bounds(inst, *span).then_some(inst)
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
                // `E.Rune`, `Self.Rune`: an associated type.
                if let Some(base) = self.type_base(cx, &pkg_name.name) {
                    return self.assoc_type(base, name);
                }
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
                    Item::Refined(_) => {
                        self.refined_here(t.span(), &format!("{}.{}", pkg_name.name, name.name));
                        None
                    }
                    _ => {
                        self.error(
                            t.span(),
                            format!("`{}.{}` is not a type", pkg_name.name, name.name),
                        );
                        None
                    }
                }
            }
            TypeExpr::Named(id) if id.name == SELF => match cx.self_ty {
                Some(ty) => Some(ty),
                None => {
                    self.diags.push(
                        Diagnostic::error(id.span, "`Self` is only used in a trait or an `impl`")
                            .with_help("there, it's the type implementing the trait"),
                    );
                    None
                }
            },
            TypeExpr::Named(id) if id.name == NEVER => {
                self.diags.push(
                    Diagnostic::error(id.span, "`never` is only a function's return type")
                        .with_help("there are no values of type `never`: a call to a `never` function doesn't return"),
                );
                None
            }
            TypeExpr::Named(id) if Self::type_param(cx, &id.name).is_some() => {
                let p = Self::type_param(cx, &id.name).expect("checked");
                if let Some(it) = p.value_param() {
                    self.diags.push(
                        Diagnostic::error(
                            id.span,
                            format!("`{p}` is a value (a `{it}`), not a type"),
                        )
                        .with_help(format!("it can be an array's length: `[{p}]u8`")),
                    );
                    return None;
                }
                Some(p)
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
                    Some(Item::Refined(_)) => {
                        self.refined_here(id.span, &id.name);
                        None
                    }
                    Some(Item::Trait(_)) => {
                        self.diags.push(
                            Diagnostic::error(
                                id.span,
                                format!("`{}` is a trait, not a type", id.name),
                            )
                            .with_help(format!("use it as a bound: `fn f[T: {}](x: T)`", id.name)),
                        );
                        None
                    }
                    Some(_) => {
                        self.error(id.span, format!("`{}` is not a type", id.name));
                        None
                    }
                    None if id.name == "Ordering" => Some(Ty::ordering()),
                    // In a trait, its associated types: `Rune` is
                    // `Self.Rune`.
                    None if cx.self_ty.is_some_and(|s| {
                        s.as_param().is_some() && self.assoc_trait(s, &id.name).is_ok()
                    }) =>
                    {
                        self.assoc_type(cx.self_ty.expect("checked"), id)
                    }

                    None if Trait::from_name(&id.name).is_some() => {
                        self.diags.push(
                            Diagnostic::error(
                                id.span,
                                format!("`{}` is a trait, not a type", id.name),
                            )
                            .with_help(format!("use it as a bound: `fn f[T: {}](x: T)`", id.name)),
                        );
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

    /// Report a named refinement used inside another type, where it would
    /// lose its refinement.
    fn refined_here(&mut self, span: Span, name: &str) {
        self.diags.push(
            Diagnostic::error(span, format!("`{name}` is a named refinement, which can't be part of another type yet"))
                .with_help("a named refinement is the whole type of a parameter, a result, a struct field or a `let` or `var`"),
        );
    }

    /// Whether `elem` can be the element type of an array or slice (`what`).
    fn check_elem(&mut self, elem: Ty, what: &str, span: Span) -> Option<()> {
        match elem {
            Ty::Int(_)
            | Ty::Bool
            | Ty::Array(_)
            | Ty::Struct(_)
            | Ty::Enum(_)
            | Ty::Optional(_)
            | Ty::Param(_) => Some(()),
            other => {
                self.error(
                    span,
                    format!("{what} of `{other}` are not supported by the compiler yet"),
                );
                None
            }
        }
    }

    /// The length in an array type `[len]T`: a constant count, or a value
    /// parameter of type `usize`.
    fn array_len_arg(&mut self, cx: &mut FnCx, e: &ast::Expr) -> Option<Len> {
        if let ExprKind::Name(n) = &e.kind
            && let Some(p) = Self::type_param(cx, n)
        {
            return match p.value_param() {
                Some(it) if Ty::Int(it) == self.usize_ty() => Some(Len::Param(p)),
                Some(it) => {
                    self.error(
                        e.span,
                        format!("an array's length is a `usize`, but `{p}` is a `{it}`"),
                    );
                    None
                }
                None => {
                    self.error(e.span, format!("`{p}` is a type, not a length"));
                    None
                }
            };
        }
        // `[E.MAX_LEN]u8`, or `[MAX_LEN]u8` in a trait: an associated
        // constant.
        let assoc = match &e.kind {
            ExprKind::Field(base, member) => match &base.kind {
                ExprKind::Name(b) => self.type_base(cx, b).map(|t| (t, member.clone())),
                _ => None,
            },
            ExprKind::Name(n)
                if !self.pkgs[cx.pkg].items.contains_key(n)
                    && cx.self_ty.is_some_and(|s| self.assoc_const(s, n).is_some()) =>
            {
                cx.self_ty.map(|s| {
                    (
                        s,
                        ast::Ident {
                            name: n.clone(),
                            span: e.span,
                        },
                    )
                })
            }
            _ => None,
        };
        if let Some((base, member)) = assoc {
            let Some((ty, it)) = self.assoc_const(base, &member.name) else {
                let found = self
                    .assoc_trait(base, &member.name)
                    .err()
                    .unwrap_or_default();
                self.assoc_error(base, &member, &found);
                return None;
            };
            if Ty::Int(it) != self.usize_ty() {
                self.error(
                    e.span,
                    format!("an array's length is a `usize`, but `{ty}` is a `{it}`"),
                );
                return None;
            }
            return match ty.as_value() {
                Some(v) => Some(Len::Known(v as u64)),
                None => Some(Len::Param(ty)),
            };
        }
        self.const_count(cx, e).map(Len::Known)
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

    /// The signature of `f`, whose owner type is `owner` for a method or an
    /// associated function (`None` if it's in error).
    fn signature(&mut self, cx: &mut FnCx, f: &ast::FnDecl, owner: Option<Ty>) -> Sig {
        // A method of a generic type names the type's parameters first:
        // `self` is the type with them as arguments.
        let mut owner = owner;
        let (mut type_params, mut bounds) = (Vec::new(), Vec::new());
        let member = cx.member.take();
        let is_member = member.is_some();
        if let Some((ps, bs)) = member {
            // A trait's or an impl's method: its parameters are the
            // trait's `Self` or the impl's.
            type_params = ps;
            bounds = bs;
        } else if let Some(o) = owner
            && (!o.decl_params().is_empty() || !f.owner_generics.is_empty())
        {
            let span = f.owner.as_ref().map_or(f.name.span, TypeExpr::span);
            if cx.expanding.is_none() {
                self.no_generic_refine(&f.owner_generics);
            }
            match self.declare_owner_generics(cx, o, &f.owner_generics, span) {
                Some((ps, bs)) => {
                    owner = Some(o.instantiate(&ps));
                    type_params = ps;
                    bounds = bs;
                }
                None => owner = None,
            }
        }
        let owner_params = type_params.len();
        let (own, own_bounds) = self.declare_generics(cx, &f.generics);
        for p in &own {
            if type_params.iter().any(|q| q.to_string() == p.to_string()) {
                self.error(
                    f.name.span,
                    format!("the type parameter `{p}` is declared twice"),
                );
            }
        }
        type_params.extend(own);
        bounds.extend(own_bounds);
        cx.type_params = type_params.clone();
        let vparam_refine = if cx.expanding.is_none() {
            self.vparam_refine(cx, &f.generics)
        } else {
            None
        };
        let mut params = Vec::new();
        // The named refinements of the parameters' types.
        let mut named = Vec::new();
        let has_self = f.params.first().is_some_and(ast::Param::is_self);
        // `comptime` parameters and a pack make a template
        // ([`comptime`]); its expansions have neither.
        let kinds: Vec<comptime::ParamKind> = f
            .params
            .iter()
            .map(|p| match (&p.ty, p.comptime) {
                (_, true) => comptime::ParamKind::Comptime,
                (TypeExpr::Pack(..), _) => comptime::ParamKind::Pack,
                _ => comptime::ParamKind::Runtime,
            })
            .collect();
        let is_template = kinds.iter().any(|&k| k != comptime::ParamKind::Runtime)
            || f.generics.iter().any(|g| g.pack);
        if is_template && cx.expanding.is_none() {
            self.check_template(f, is_member || owner.is_some() || f.owner.is_some(), &kinds);
        }
        for (p, &kind) in f.params.iter().zip(&kinds) {
            if kind == comptime::ParamKind::Pack {
                let TypeExpr::Pack(name, _) = &p.ty else {
                    unreachable!("a pack's type")
                };
                let named = cx
                    .pack_params
                    .first()
                    .is_some_and(|q| q.as_param().is_some_and(|d| d.name == name.name));
                match cx.expanding {
                    // One parameter per argument, of its type parameter.
                    Some(_) if named => {
                        for (i, &ty) in cx.pack_params.iter().enumerate() {
                            params.push((
                                ty,
                                Convention::Let,
                                comptime::pack_local(&p.name.name, i),
                            ));
                        }
                    }
                    Some(_) => {}
                    None => {
                        let ty = cx.pack_params.first().copied().unwrap_or(Ty::Unit);
                        params.push((ty, Convention::Let, p.name.name.clone()));
                    }
                }
                continue;
            }
            if kind == comptime::ParamKind::Comptime {
                let ty = self.resolve_type(cx, &p.ty).unwrap_or(Ty::Unit);
                if cx.expanding.is_none() {
                    if !matches!(ty, Ty::Int(_) | Ty::Bool | Ty::Str | Ty::Unit) {
                        self.diags.push(
                            Diagnostic::error(
                                p.ty.span(),
                                format!("a `comptime` parameter of type `{ty}` is not supported by the compiler yet"),
                            )
                            .with_help("a `comptime` parameter is an integer, a `bool` or a `str`"),
                        );
                    }
                    if p.convention != Convention::Let {
                        self.error(p.name.span, "a `comptime` parameter is read-only");
                    }
                    params.push((ty, Convention::Let, p.name.name.clone()));
                }
                continue;
            }
            let ty = if p.is_self() {
                if p.convention == Convention::Set {
                    self.diags.push(
                        Diagnostic::error(p.name.span, "`self` can't be `set`").with_help(
                            "a method is called on a value that exists; use `inout self` to change it",
                        ),
                    );
                }
                named.push(None);
                owner.unwrap_or(Ty::Unit)
            } else {
                let (ty, r) = self.resolve_refined(cx, &p.ty).unwrap_or((Ty::Unit, None));
                named.push(r);
                ty
            };
            self.check_convention(p, ty);
            // A `set self` is reported, and checked as `self`.
            let convention = match p.convention {
                Convention::Set if p.is_self() => Convention::Let,
                c => c,
            };
            params.push((ty, convention, p.name.name.clone()));
        }
        let mut ret_named = None;
        let ret = match &f.ret {
            // `never` is only a return type (docs/types.md).
            Some(TypeExpr::Named(id)) if id.name == NEVER => {
                if f.throws.is_some() {
                    self.diags.push(
                        Diagnostic::error(id.span, "a `never` function can't throw")
                            .with_help("it never returns, with a value or with an error"),
                    );
                }
                Ty::Never
            }
            Some(t) => match self.resolve_refined(cx, t).map(|(ty, r)| {
                ret_named = r;
                ty
            }) {
                // A `str` with static storage can be returned (see
                // `check_str_returns`).
                Some(Ty::Str) if f.throws.is_some() => {
                    self.error(t.span(), "a function that throws can't return a `str` yet");
                    Ty::Str
                }
                Some(ty @ Ty::Slice(_)) => {
                    self.error(
                        t.span(),
                        "returning a slice is not supported by the compiler yet",
                    );
                    // The type is kept, so the body is still checked.
                    ty
                }
                Some(ty) => ty,
                None => Ty::Unit,
            },
            None => Ty::Unit,
        };
        let throws = f.throws.as_ref().and_then(|t| self.error_type(cx, t));
        let (refines, ret_refine) = if is_template || cx.expanding.is_some() {
            let given = f
                .params
                .iter()
                .find_map(|p| p.refine.as_ref())
                .or(f.ret_refine.as_ref());
            if let (Some(e), None) = (given, cx.expanding) {
                self.error(
                    e.span,
                    "refinements on a function with `comptime` parameters or a pack are not supported by the compiler yet",
                );
            }
            (vec![None; params.len()], None)
        } else {
            self.sig_refines(cx, f, &params, &named, ret, ret_named, is_member)
        };
        let name = match &f.owner {
            Some(TypeExpr::Named(t)) => format!("{}.{}", t.name, f.name.name),
            Some(TypeExpr::Qualified(p, t)) => format!("{}.{}.{}", p.name, t.name, f.name.name),
            _ => f.name.name.clone(),
        };
        Sig {
            is_pub: f.is_pub,
            is_unsafe: f.is_unsafe,
            pkg: cx.pkg,
            template: (is_template && cx.expanding.is_none())
                .then_some(comptime::Template { kinds }),
            intrinsic: self.intrinsic(cx, f),
            name,
            params,
            has_self,
            ret,
            throws,
            span: f.name.span,
            type_params,
            bounds,
            owner_params,
            self_ty: cx.self_ty,
            symbol_name: None,
            refines,
            ret_refine,
            vparam_refine,
        }
    }

    /// Report a convention that a parameter of type `ty` can't have.
    fn check_convention(&mut self, p: &ast::Param, ty: Ty) {
        let why = match (p.convention, ty) {
            (Convention::Inout, Ty::Str) => {
                "a `str` can't be passed `inout`: its bytes are read-only".to_owned()
            }
            (Convention::Set, ty) if ty.is_view() => {
                format!("a `set` parameter can't be a view (`{ty}`)")
            }
            _ => return,
        };
        self.error(p.name.span, why);
    }

    /// The error type of a `throws` clause: an enum.
    fn error_type(&mut self, cx: &mut FnCx, t: &ast::Throws) -> Option<Ty> {
        let Some(te) = &t.ty else {
            self.diags.push(
                Diagnostic::error(
                    t.span,
                    "inferred error sets (`throws` without a type) are not supported by the compiler yet",
                )
                .with_help("name the error type, an enum: `throws(E)`"),
            );
            return None;
        };
        let ty = self.resolve_type(cx, te)?;
        if ty.as_enum().is_none() {
            self.diags.push(
                Diagnostic::error(
                    te.span(),
                    format!("an error type must be an enum, found `{ty}`"),
                )
                .with_help("declare the errors as the variants of an enum: `enum E { ... }`"),
            );
            return None;
        }
        if !ty.is_copy() {
            self.diags.push(
                Diagnostic::error(
                    te.span(),
                    format!("an error type must be `Copy`, and `{ty}` isn't"),
                )
                .with_help("an error is dropped by `catch v` and `catch _`: it can't hold a value that needs destruction"),
            );
            return None;
        }
        Some(ty)
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
            Item::Trait(t) => self.traits[self.trait_index[&t]].decl.is_pub,
            Item::Refined(k) => self.refined_types[k].decl.is_pub,
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
                    Some(ty) if table_leaf(ty).is_some() && table_scalars(ty) > TABLE_MAX => {
                        self.error(
                            t.span(),
                            format!("an array constant has at most {TABLE_MAX} elements"),
                        );
                        None
                    }
                    Some(ty) if !ty.is_copy() => {
                        self.diags.push(
                            Diagnostic::error(
                                t.span(),
                                format!("a constant's type must be `Copy`, and `{ty}` isn't"),
                            )
                            .with_help("a constant is copied where it's used: make the value with a function instead"),
                        );
                        None
                    }
                    Some(ty) if const_type(ty) => self.computed_const(&mut cx, decl, ty),
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

    /// The value of the typed constant `decl`, of type `ty`, computed at
    /// compile time (docs/generics.md, What M7 needs): any expression of
    /// the type, calls of ordinary functions included. Its proof
    /// obligations are discharged by running it.
    fn computed_const(&mut self, cx: &mut FnCx, decl: &ast::ConstDecl, ty: Ty) -> Option<ConstVal> {
        cx.comptime = true;
        let c = self.expr(cx, &decl.value, Some(ty))?;
        let c = self.coerce(cx, c, ty, decl.value.span)?;
        // A value the checker already knows.
        if let (TExprKind::Int(v), Ty::Int(_)) = (&c.expr.kind, ty) {
            return Some(ConstVal::Typed(ty, *v));
        }
        if let TExprKind::Table(id) = c.expr.kind {
            return Some(ConstVal::Table(ty, id));
        }
        let budget = match &decl.budget {
            None => eval::DEFAULT_STEPS,
            Some(b) => match self.untyped_int(cx, b).map(u64::try_from) {
                Some(Ok(n)) if n > 0 => n,
                _ => {
                    self.error(
                        b.span,
                        "the budget must be a positive integer literal or untyped constant",
                    );
                    return None;
                }
            },
        };
        let what = format!("`{}`", decl.name.name);
        let subject = eval::Subject {
            what: &what,
            span: decl.value.span,
            budget_span: decl.budget.as_ref().map(|b| b.span),
        };
        let v = self.evaluate(&c.expr, cx.locals.len(), budget, &subject)?;
        if let Ty::Int(_) = ty {
            let mut out = Vec::new();
            eval::flatten(&v, &mut out);
            return Some(ConstVal::Typed(ty, out[0]));
        }
        if table_leaf(ty).is_some() {
            let mut values = Vec::new();
            eval::flatten(&v, &mut values);
            self.tables.push(Table {
                name: decl.name.name.clone(),
                ty,
                values,
            });
            return Some(ConstVal::Table(ty, self.tables.len() - 1));
        }
        if eval::scalars(&v) > CONST_EXPR_MAX {
            self.diags.push(
                Diagnostic::error(
                    decl.value.span,
                    format!(
                        "a constant of type `{ty}` has at most {CONST_EXPR_MAX} scalars"
                    ),
                )
                .with_help("only arrays of integers and `bool` are kept in read-only data; others are built where they're used"),
            );
            return None;
        }
        self.const_exprs.push(eval::materialize(&v, ty));
        Some(ConstVal::Expr(self.const_exprs.len() - 1))
    }

    /// Check function `id`'s body, now.
    fn check_function(&mut self, id: FuncId) {
        self.func_states[id] = FuncState::Checking;
        let errors = self.diags.iter().filter(|d| d.is_error()).count();
        let (decl, pkg, file) = self.fn_decls[id];
        let func = self.function(decl, id, pkg, file);
        let ok = self.diags.iter().filter(|d| d.is_error()).count() == errors;
        self.func_states[id] = FuncState::Done(Rc::new(func), ok);
        self.checked_order.push(id);
    }

    /// Function `id`'s checked body, for the evaluator, checked now if it
    /// isn't yet (docs/generics.md, The evaluator): `None` if it has errors
    /// (reported), `Some(None)` if it's being checked (its body needs the
    /// value being computed), and an error while types and signatures are
    /// declared.
    fn func_for_eval(&mut self, id: FuncId) -> Result<Option<Rc<Func>>, String> {
        if self.declaring {
            return Err(
                "a constant needed to declare a type or a signature can't call a function"
                    .to_owned(),
            );
        }
        if let FuncState::Unchecked = self.func_states[id] {
            self.check_function(id);
        }
        match &self.func_states[id] {
            FuncState::Done(f, true) => Ok(Some(f.clone())),
            FuncState::Done(_, false) => Ok(None),
            FuncState::Checking => Err(format!(
                "it calls `{}`, whose body needs this value: it depends on itself",
                self.sigs[id].name
            )),
            FuncState::Unchecked => unreachable!("checked above"),
        }
    }

    fn function(&mut self, f: &ast::FnDecl, id: FuncId, pkg: usize, file: FileId) -> Func {
        let (ret, is_unsafe) = (self.sigs[id].ret, self.sigs[id].is_unsafe);
        let throws = self.sigs[id].throws;
        let name = self.sigs[id].name.clone();
        let symbol = format!(
            "{}.{}",
            self.pkgs[pkg].path,
            self.sigs[id].symbol_name.as_ref().unwrap_or(&name)
        );
        let mut cx = FnCx::new(pkg, file, ret, is_unsafe);
        cx.throws = throws;
        cx.func = Some(id);
        cx.type_params = self.sigs[id].type_params.clone();
        cx.self_ty = self.sigs[id].self_ty;
        // A trait's required method has no body: an impl's replaces it in
        // every call. A template isn't checked on its own: its expansions
        // are.
        // An intrinsic's body isn't used: its calls are the compiler's.
        let template = self.sigs[id].template.is_some() || self.sigs[id].intrinsic.is_some();
        if template || matches!(self.members.get(&id), Some(traits::Member::Trait(_, false))) {
            return Func {
                symbol,
                name,
                type_params: cx.type_params.clone(),
                owner_params: self.sigs[id].owner_params,
                value_params: Vec::new(),
                params: Vec::new(),
                ret,
                throws,
                locals: Vec::new(),
                body: Vec::new(),
                span: f.span,
                template,
            };
        }
        let mut params = Vec::new();
        let param_tys = self.sigs[id].params.clone();
        let expansion = self.expansions.contains_key(&id);
        for (k, (ty, convention, pname)) in param_tys.into_iter().enumerate() {
            // An expansion's parameters are the template's runtime ones,
            // then one per pack argument (hidden names).
            let p = if expansion {
                f.params.iter().find(|p| p.name.name == pname)
            } else {
                f.params.get(k)
            };
            let pspan = p.map_or(f.name.span, |p| p.name.span);
            if cx.scopes[0].contains_key(&pname) {
                self.error(pspan, format!("parameter `{pname}` is declared twice"));
            }
            // The callee may change an `inout`, `sink` or `set` parameter;
            // an `inout` slice's elements, not the slice itself.
            let mutable = match convention {
                Convention::Let => false,
                Convention::Inout => !ty.is_view(),
                Convention::Sink | Convention::Set => true,
            };
            let local = Self::declare_local(&mut cx, &pname, ty, mutable, Some(convention));
            // `self` of a type in error: uses of it fail without more errors.
            if p.is_some_and(ast::Param::is_self) && ty == Ty::Unit {
                cx.failed.insert(local);
            }
            if convention == Convention::Set && !ty.is_view() {
                cx.env.declare_uninit(local);
                cx.set_params.push(local);
            }
            params.push(local);
        }
        cx.params = params.len();
        self.declare_expansion(&mut cx, id);
        // A value parameter is an immutable local of its type, a term like
        // any other; an instance assigns it its value first.
        for p in cx.type_params.clone() {
            let Some(it) = p.value_param() else {
                continue;
            };
            let name = p.to_string();
            if cx.scopes[0].contains_key(&name) {
                self.error(
                    f.name.span,
                    format!("`{name}` is both a value parameter and a parameter"),
                );
                continue;
            }
            let local = Self::declare_local(&mut cx, &name, Ty::Int(it), false, None);
            cx.value_locals.push((p, local));
        }
        // So is an associated constant of a type parameter (`E.MAX_LEN`),
        // in a hidden local.
        for (p, it) in self.assoc_value_params(&cx.type_params.clone()) {
            let local = Self::declare_local(&mut cx, &format!("${p}"), Ty::Int(it), false, None);
            cx.value_locals.push((p, local));
        }
        self.assume_vparams(&mut cx, id);
        self.assume_params(&mut cx, id);
        // A `sink` parameter owns its value: it's destroyed when the body
        // ends, unless it's moved on. In a `deinit`, `self` isn't destroyed
        // again (it can't be moved either): its fields are, when the body
        // ends (docs/allocation.md, Declaring destruction).
        let mut prologue = Vec::new();
        for &p in &params {
            let local = &cx.locals[p];
            if local.convention != Some(Convention::Sink) || local.ty.is_copy() {
                continue;
            }
            if self.deinits.contains(&id) && p == 0 {
                cx.deinit_self = Some(p);
                let fields = destroy_fields(p, local.ty);
                if !fields.is_empty() {
                    prologue.push(TStmt::Defer {
                        body: fields,
                        on_error: false,
                    });
                }
                continue;
            }
            prologue.push(TStmt::Drop {
                local: p,
                init: true,
            });
        }
        let mut body = self.block(&mut cx, &f.body.stmts);
        if !prologue.is_empty() {
            prologue.append(&mut body);
            body = prologue;
        }
        self.check_str_returns(&cx);
        // A failed local is only declared after its error was reported.
        debug_assert!(cx.failed.is_empty() || crate::diag::has_errors(&self.diags));
        if ret == Ty::Never && !terminates(&body) {
            self.diags.push(
                Diagnostic::error(
                    f.name.span,
                    format!(
                        "`{}` is declared `-> never`, but can reach the end of its body",
                        f.name.name
                    ),
                )
                .with_help("every path must end in a call to another `never` function (like `os.exit`), or an endless `loop`"),
            );
        } else if ret != Ty::Unit && !terminates(&body) {
            self.error(
                f.name.span,
                format!(
                    "`{}` can reach the end of its body without returning a value",
                    f.name.name
                ),
            );
        } else if !terminates(&body) {
            // At the closing `}`.
            let end = Span {
                start: f.body.span.end.saturating_sub(1),
                ..f.body.span
            };
            self.check_set_params(&cx, end);
        }
        Func {
            symbol,
            name,
            type_params: cx.type_params.clone(),
            owner_params: self.sigs[id].owner_params,
            value_params: cx.value_locals,
            params,
            ret,
            throws,
            locals: cx.locals,
            body,
            span: f.span,
            template: false,
        }
    }

    /// Report an assignment to `name`, which is not a variable: a constant,
    /// or nothing known.
    fn unknown_target(&mut self, cx: &FnCx, name: &str, span: Span) {
        if let Some(Item::Const(_)) = self.pkgs[cx.pkg].items.get(name) {
            self.diags.push(
                Diagnostic::error(
                    span,
                    format!("cannot assign to `{name}`, which is a constant"),
                )
                .with_help(format!("change a copy: `var v = {name}`")),
            );
            return;
        }
        self.error(span, format!("cannot find `{name}` in this scope"));
    }

    /// A function returning a `str` returns only strings with static
    /// storage, which borrow from nothing: string literals, the results of
    /// other functions returning a `str`, and locals that only ever hold
    /// such strings. Until the compiler checks that a returned view borrows
    /// from the parameters (docs/memory.md, Views), that's what keeps a
    /// returned `str` valid. Report each returned local that may hold
    /// another string.
    fn check_str_returns(&mut self, cx: &FnCx) {
        // The locals that may hold a string that isn't static: any that
        // was given one, and any copied from such a local.
        let deps = &cx.strs.deps;
        let mut tainted: HashSet<LocalId> = deps
            .iter()
            .filter(|(_, d)| d.is_none())
            .map(|(&l, _)| l)
            .collect();
        loop {
            let more: Vec<LocalId> = deps
                .iter()
                .filter(|(l, d)| {
                    !tainted.contains(l)
                        && d.as_ref().is_some_and(|d| {
                            d.iter()
                                .any(|s| tainted.contains(s) || !deps.contains_key(s))
                        })
                })
                .map(|(&l, _)| l)
                .collect();
            if more.is_empty() {
                break;
            }
            tainted.extend(more);
        }
        let mut reported = HashSet::new();
        for &(l, span) in &cx.strs.returned {
            if (tainted.contains(&l) || !deps.contains_key(&l)) && reported.insert(span) {
                self.report_str_return(span);
            }
        }
    }

    fn report_str_return(&mut self, span: Span) {
        self.diags.push(
            Diagnostic::error(
                span,
                "a function can only return a `str` that is a string literal (or another function's `str` result)",
            )
            .with_help("a returned `str` can't borrow from the parameters yet (docs/memory.md, Views)"),
        );
    }

    /// The help for assigning to the immutable `local`, named `name`.
    pub(super) fn immutable_help(cx: &FnCx, local: LocalId, name: &str) -> String {
        if cx.value_locals.iter().any(|&(_, l)| l == local) {
            format!("`{name}` is a value parameter: its value is fixed when compiling")
        } else if name == "self" && local == 0 {
            "declare the method with `inout self` to change the value it's called on".to_owned()
        } else if local < cx.params {
            format!(
                "parameters are read-only; declare it `inout {name}` to change the caller's variable, or change a copy: `var m = {name}`"
            )
        } else {
            format!("declare it with `var {name}` to make it mutable")
        }
    }

    /// Report the `set` parameters that may not be assigned when the
    /// function returns at `span`.
    fn check_set_params(&mut self, cx: &FnCx, span: Span) {
        for &p in &cx.set_params {
            if cx.env.is_uninit(p) {
                let name = &cx.locals[p].name;
                self.diags.push(
                    Diagnostic::error(
                        span,
                        format!("`{name}` is a `set` parameter, but it may not be assigned when the function returns here"),
                    )
                    .with_help(format!(
                        "assign `{name}` on every path that returns; a `throw` doesn't need to"
                    )),
                );
            }
        }
    }

    fn declare(&mut self, cx: &mut FnCx, name: &str, ty: Ty, mutable: bool) -> LocalId {
        Self::declare_local(cx, name, ty, mutable, None)
    }

    fn declare_local(
        cx: &mut FnCx,
        name: &str,
        ty: Ty,
        mutable: bool,
        convention: Option<Convention>,
    ) -> LocalId {
        let id = cx.locals.len();
        cx.locals.push(Local {
            name: name.to_owned(),
            ty,
            mutable,
            convention,
            drop_flag: false,
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
        let mut out = Vec::new();
        for (k, s) in stmts.iter().enumerate() {
            let (temps, after) = (cx.temps.len(), cx.after.len());
            let checked = match s {
                Stmt::Defer { body, on_error, .. } => {
                    self.defer(cx, body, *on_error, &stmts[k + 1..])
                }
                _ => self.stmt(cx, s),
            };
            // A `let` or `var` that failed (its error is reported) still
            // declares its name, so later uses don't report it as unknown.
            // Without a known type, it's a failed local: uses of it fail
            // silently.
            if checked.is_none()
                && let Stmt::Let { name, mutable, .. } = s
                && !cx.scopes.last().expect("scope").contains_key(&name.name)
            {
                let local = self.declare(cx, &name.name, Ty::Unit, *mutable);
                cx.failed.insert(local);
            }
            // The statement's temporaries are destroyed when it ends, and
            // what it declares owns its value from there.
            let temps = cx.temps.split_off(temps);
            let after = cx.after.split_off(after);
            let Some(checked) = checked else {
                continue;
            };
            out.extend(
                temps
                    .iter()
                    .map(|&local| TStmt::Drop { local, init: false }),
            );
            out.push(TStmt::Loc(s.span()));
            out.push(checked);
            out.extend(after);
            out.extend(temps.iter().rev().map(|&t| {
                TStmt::Destroy(TExpr {
                    kind: TExprKind::Local(t),
                    ty: cx.locals[t].ty,
                })
            }));
        }
        // The variables the block's `defer` bodies move are moved at its end.
        let depth = cx.scopes.len();
        for l in self.defer_moves_at(cx, depth - 1, false, None) {
            cx.env.declare_uninit(l);
            cx.moved.insert(l);
        }
        cx.defer_moves.retain(|m| m.depth < depth);
        cx.scopes.pop();
        out
    }

    /// The variables the `defer` bodies that an exit runs move: those of
    /// the blocks deeper than `depth` (the scopes the exit leaves), and of
    /// their `errdefer`s too for an exit with an error. Each must be
    /// assigned here, at the exit `at` (`None`: a block's end); after the
    /// exit, it isn't.
    fn defer_moves_at(
        &mut self,
        cx: &FnCx,
        depth: usize,
        error: bool,
        at: Option<Span>,
    ) -> Vec<LocalId> {
        if cx.env.dead {
            return Vec::new();
        }
        let moves: Vec<DeferMove> = cx
            .defer_moves
            .iter()
            .filter(|m| m.depth > depth && (error || !m.on_error))
            .copied()
            .collect();
        let mut out = Vec::new();
        for m in moves {
            if cx.env.is_uninit(m.local) && !out.contains(&m.local) {
                let name = &cx.locals[m.local].name;
                let (what, an) = if m.on_error {
                    ("errdefer", "an")
                } else {
                    ("defer", "a")
                };
                let d = match at {
                    Some(at) => Diagnostic::error(
                        at,
                        format!("`{name}` may be moved already at this exit, where {an} `{what}` that moves it runs"),
                    )
                    .with_note(m.span, format!("the `{what}` moves `{name}` here")),
                    None => Diagnostic::error(
                        m.span,
                        format!("this `{what}` moves `{name}`, which may be moved already at the end of its block"),
                    ),
                };
                self.diags.push(d.with_help(format!(
                    "{an} `{what}` that moves a variable runs only where it's still assigned: don't move `{name}` after it"
                )));
            }
            out.push(m.local);
        }
        out
    }

    /// `defer` or `errdefer` (`on_error`), followed by `rest` in its block.
    /// The body runs when control leaves the block, at a point after the
    /// `defer` statement, so it's checked with the facts known here about
    /// the variables `rest` doesn't assign. It can't assign variables
    /// declared outside it, so running it changes no facts.
    fn defer(
        &mut self,
        cx: &mut FnCx,
        body: &ast::Block,
        on_error: bool,
        rest: &[Stmt],
    ) -> Option<TStmt> {
        if on_error && cx.throws.is_none() {
            self.diags.push(
                Diagnostic::error(
                    body.span,
                    "`errdefer` can only be used in a function that throws",
                )
                .with_help("use `defer` to run it whenever the block is left"),
            );
            return None;
        }
        let mut later = HashSet::new();
        assigned_names(rest, &mut later);
        let saved = cx.env.clone();
        for name in &later {
            if let Some(local) = cx.lookup(name) {
                cx.env.forget(local);
            }
        }
        let loop_depth = std::mem::replace(&mut cx.loop_depth, 0);
        let floor = std::mem::replace(&mut cx.defer_floor, cx.locals.len());
        let kind = cx.defer_kind.replace((on_error, cx.scopes.len()));
        cx.defer_depth += 1;
        let checked = self.block(cx, &body.stmts);
        cx.defer_depth -= 1;
        cx.defer_kind = kind;
        cx.defer_floor = floor;
        cx.loop_depth = loop_depth;
        cx.env = saved;
        Some(TStmt::Defer {
            body: checked,
            on_error,
        })
    }

    /// Report an assignment to `local` (named `name`) in a `defer` block
    /// that declared it outside the block.
    fn check_defer_assign(
        &mut self,
        cx: &FnCx,
        local: LocalId,
        name: &str,
        span: Span,
    ) -> Option<()> {
        if cx.defer_depth == 0 || local >= cx.defer_floor {
            return Some(());
        }
        self.diags.push(
            Diagnostic::error(
                span,
                format!("a `defer` block can't assign `{name}`, which is declared outside it"),
            )
            .with_help("`defer` is for cleanup, like closing what was opened"),
        );
        None
    }

    /// Report a statement (`what`) that would leave a `defer` block.
    pub(super) fn check_not_in_defer(&mut self, cx: &FnCx, span: Span, what: &str) -> Option<()> {
        if cx.defer_depth == 0 {
            return Some(());
        }
        self.diags.push(
            Diagnostic::error(span, format!("{what} can't leave a `defer` block"))
                .with_help("a `defer` block runs while its block is left, and must end normally"),
        );
        None
    }

    /// A local was given a new value: record what's known about it.
    fn record_value(&self, cx: &mut FnCx, local: LocalId, value: &expr::Checked) {
        if cx.locals[local].ty == Ty::Str {
            let origin = str_origin(cx, &value.expr);
            let entry = cx.strs.deps.entry(local).or_insert(Some(Vec::new()));
            match (entry.as_mut(), origin) {
                (Some(deps), Some(more)) => deps.extend(more),
                _ => *entry = None,
            }
        }
        match value.term {
            // `i = i + k`: what was known about `i` shifts by `k`.
            Some(src) if src.term == Term::Local(local) => {
                cx.env.shift(local, value.range, src.offset);
            }
            _ => cx.env.assign(local, value.range),
        }
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
            // it, as in `let i = xs.len - 1`, and has its holes.
            cx.env
                .apply(&equal(Term::Local(local), src.term, src.offset));
            cx.env.copy_holes(src.term, Term::Local(local), src.offset);
        }
        // A form of one other term, as in `let x = 9 - d` or `t = 10 * v`:
        // `x - F <= 0` and `F - x <= 0`, a relation or a sum.
        if value.term.is_none()
            && let Some(f) = value.form
            && f.term_count() == 1
            && f.terms().all(|(t, _)| t.local() != local)
        {
            let x = facts::Form::of(Linear::of(Term::Local(local)));
            let full = term_full_by(|l| cx.locals[l].ty, Term::Local(local));
            for d in [x.minus(f), f.minus(x)].into_iter().flatten() {
                cx.env.apply(&d.le(0, full));
            }
        }
        // At most another term plus a constant, as in `let mid = xs.len / 2`.
        if let Some(up) = value.upper
            && up.term != Term::Local(local)
        {
            cx.env.apply(&[facts::Fact::Rel {
                a: Term::Local(local),
                b: up.term,
                c: up.offset,
            }]);
        }
        // Bounds a call's result refinement gives (`result <= buf.len`).
        if !value.known.is_empty() {
            let known = refine::known_facts(cx, local, &value.known);
            cx.env.apply(&known);
        }
        // A slice `v[i..j]` has the length `j - i`: its range, and how it
        // relates to `j` when that's a term (exactly, when `i` is a
        // constant).
        if let Some(sl) = value.len {
            let len = Term::Len(local);
            let mut known = vec![facts::Fact::Narrow {
                term: len,
                bound: sl.range,
                full: term_full_by(|l| cx.locals[l].ty, len),
            }];
            if let Some(end) = sl.end
                && end.term.local() != local
            {
                // end - start.hi <= len <= end - start.lo
                if let Some(c) = end.offset.checked_sub(sl.start.lo) {
                    known.push(facts::Fact::Rel {
                        a: len,
                        b: end.term,
                        c,
                    });
                }
                if let Some(c) = sl.start.hi.checked_sub(end.offset) {
                    known.push(facts::Fact::Rel {
                        a: end.term,
                        b: len,
                        c,
                    });
                }
            }
            cx.env.apply(&known);
        }
        if cx.locals[local].ty.is_view() {
            // `s.bytes()` views the same bytes as `s`.
            let viewed = match &value.expr.kind {
                TExprKind::Bytes(s) => &s.kind,
                kind => kind,
            };
            match viewed {
                // A string literal has its length.
                TExprKind::Str(id) => {
                    let n = self.strings[*id].len() as i128;
                    cx.env.apply(&[facts::Fact::Narrow {
                        term: Term::Len(local),
                        bound: Range::exact(n),
                        full: Range { lo: n, hi: n },
                    }]);
                }
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
                TExprKind::ToSlice(array) => match array.ty.as_array().expect("an array").1 {
                    Len::Known(n) => {
                        let n = i128::from(n);
                        cx.env.apply(&[facts::Fact::Narrow {
                            term: Term::Len(local),
                            bound: Range::exact(n),
                            full: Range { lo: n, hi: n },
                        }]);
                    }
                    // `[N]T`: the length is the value parameter's local.
                    Len::Param(p) => {
                        if let Some(n) = cx.value_local(p) {
                            cx.env.apply(&equal(Term::Len(local), Term::Local(n), 0));
                        }
                    }
                },
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
                let (annotated, named) = match ty {
                    Some(t) => {
                        let (ty, r) = self.resolve_refined(cx, t)?;
                        (Some(ty), r)
                    }
                    None => (None, None),
                };
                let Some(init) = init else {
                    // `var x: T`: assigned later, before it's read.
                    if !*mutable {
                        self.diags.push(
                            Diagnostic::error(*span, "`let` needs a value")
                                .with_help("declare it with `var` to assign it later"),
                        );
                        return None;
                    }
                    let Some(ty) = annotated else {
                        self.diags.push(
                            Diagnostic::error(*span, "a `var` without a value needs a type")
                                .with_help(format!("e.g. `var {}: u32`", name.name)),
                        );
                        return None;
                    };
                    if cx.scopes.last().expect("scope").contains_key(&name.name) {
                        self.error(
                            name.span,
                            format!("`{}` is already declared in this block", name.name),
                        );
                        return None;
                    }
                    let local = self.declare(cx, &name.name, ty, true);
                    cx.env.declare_uninit(local);
                    if let Some(r) = named {
                        cx.place_refines.insert(local, (r, refine::Leaf::Value));
                    }
                    if ty.is_copy() {
                        return None;
                    }
                    // It owns what it's assigned, from here.
                    cx.locals[local].drop_flag = true;
                    return Some(TStmt::Drop { local, init: false });
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
                    (Some(v), Some(t)) => self.coerce(cx, v, t, init.span),
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
                if value.ty() == Ty::Never {
                    self.diags.push(
                        Diagnostic::error(
                            init.span,
                            "this call never returns, so there's no value to store",
                        )
                        .with_help("call it on its own: the code after it can't be reached"),
                    );
                    return None;
                }
                let value = self.kept(cx, value, init.span)?;
                let local = self.declare(cx, &name.name, value.ty(), *mutable);
                self.check_kept_view(cx, &value, init.span)?;
                if let Some(r) = named {
                    cx.place_refines.insert(local, (r, refine::Leaf::Value));
                    self.check_local_refine(cx, local, &value, init.span);
                }
                self.record_value(cx, local, &value);
                self.assume_local_refine(cx, local);
                if !value.ty().is_copy() {
                    cx.after.push(TStmt::Drop { local, init: true });
                }
                Some(TStmt::Init(local, value.expr))
            }
            Stmt::Assign {
                target,
                op,
                value,
                span,
            } => {
                if let ExprKind::Index(..) | ExprKind::Field(..) = target.kind {
                    let out = self.place_assign(cx, target, *op, value, *span);
                    // An assignment that fails to check still changes the
                    // variable: what was known about it no longer holds (in
                    // a loop, its errors must not come from a head that
                    // only holds because the assignment was skipped).
                    if out.is_none()
                        && let ExprKind::Name(name) = &place_root(target).kind
                        && let Some(local) = cx.lookup(name)
                    {
                        cx.env.forget(local);
                    }
                    return out;
                }
                let ExprKind::Name(name) = &target.kind else {
                    self.error(
                        target.span,
                        "only variables, their elements and their fields can be assigned to",
                    );
                    return None;
                };
                let Some(local) = cx.lookup(name) else {
                    self.unknown_target(cx, name, target.span);
                    return None;
                };
                if cx.failed.contains(&local) {
                    return None;
                }
                if !cx.locals[local].mutable {
                    self.diags.push(
                        Diagnostic::error(
                            target.span,
                            format!("cannot assign to `{name}`, which is immutable"),
                        )
                        .with_help(Self::immutable_help(cx, local, name)),
                    );
                    return None;
                }
                self.check_defer_assign(cx, local, name, target.span)?;
                let ty = cx.locals[local].ty;
                let checked = match op {
                    None => self.expr(cx, value, Some(ty)),
                    Some(op) => {
                        let combined = ast::Expr {
                            kind: ExprKind::Binary(
                                *op,
                                Box::new(target.clone()),
                                Box::new(value.clone()),
                            ),
                            span: *span,
                        };
                        self.expr(cx, &combined, Some(ty))
                    }
                };
                let checked = checked.and_then(|c| self.coerce(cx, c, ty, value.span));
                let checked = checked.and_then(|c| self.kept(cx, c, value.span));
                let Some(checked) = checked else {
                    // As for a place above: the variable is still assigned.
                    cx.env.forget(local);
                    return None;
                };
                if !ty.is_copy() {
                    // The old value is destroyed, if there's one: the drop
                    // flag says, where there may be none.
                    if cx.env.is_uninit(local) {
                        cx.locals[local].drop_flag = true;
                    }
                    Self::invalidate_projections(cx, local);
                }
                self.check_kept_view(cx, &checked, value.span)?;
                self.check_local_refine(cx, local, &checked, value.span);
                self.record_value(cx, local, &checked);
                self.assume_local_refine(cx, local);
                Some(TStmt::Assign(local, checked.expr))
            }
            // Reached in code that's checked: an error. The program isn't
            // compiled, so this stands for code that doesn't go on, which
            // a function returning a value needs after it.
            Stmt::Expr(e) if !cx.comptime && self.is_compile_error(cx, e) => {
                self.compile_error_stmt(cx, e);
                Some(TStmt::Loop(Vec::new()))
            }
            Stmt::ComptimeLet { name, ty, init, .. } => {
                self.comptime_let(cx, name, ty.as_ref(), init);
                None
            }
            Stmt::Expr(e) => match &e.kind {
                // A value that isn't `()` is destroyed right away.
                ExprKind::Call(..) | ExprKind::Try(_) => {
                    let c = self.expr(cx, e, None)?;
                    Some(TStmt::Expr(self.temp(cx, c).expr))
                }
                // The value is dropped, so the block may end normally.
                ExprKind::Catch {
                    value,
                    binding,
                    handler,
                } => {
                    let c = self.whole(cx, e.span, |ck, cx| {
                        ck.catch(cx, value, binding.as_ref(), handler, false, None)
                    })?;
                    // On success, the value would be lost, not destroyed.
                    if !c.ty().is_copy() {
                        self.diags.push(
                            Diagnostic::error(
                                e.span,
                                format!("the value of this call, a `{}`, would be dropped without being destroyed", c.ty()),
                            )
                            .with_help("keep it: `let x = f() catch ...`, with a block that leaves"),
                        );
                        return None;
                    }
                    Some(TStmt::Expr(c.expr))
                }
                _ => {
                    self.error(e.span, "this expression has no effect");
                    None
                }
            },
            // A `return` that fails to check still ends control flow, so it's kept
            // (as a bare `return`) to avoid a cascade of "missing return" errors.
            // Lowering never sees it: the program has errors.
            Stmt::Return { span, .. } if cx.defer_depth > 0 => {
                self.check_not_in_defer(cx, *span, "`return`");
                None
            }
            // Like a `return`, a `throw` that fails to check still ends
            // control flow; lowering never sees it.
            Stmt::Throw { value, span } => Some(match self.throw(cx, value, *span) {
                Some(e) => {
                    self.defer_moves_at(cx, 0, true, Some(*span));
                    TStmt::Throw(e)
                }
                None => TStmt::Return(None),
            }),
            // Only reached for a `defer` outside a block's statements.
            Stmt::Defer { body, on_error, .. } => self.defer(cx, body, *on_error, &[]),
            Stmt::Return { span, .. } if cx.ret == Ty::Never => {
                self.diags.push(
                    Diagnostic::error(*span, "this function is declared `-> never`, so it can't return")
                        .with_help("end it with a call to another `never` function (like `os.exit`), or an endless `loop`"),
                );
                // Kept as a `return`, to avoid a cascade of errors.
                Some(TStmt::Return(None))
            }
            Stmt::Return { value, span } => {
                let value = match (value, cx.ret) {
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
                        .inspect(|checked| self.check_return_refine(cx, checked, v.span))
                        .and_then(|checked| self.coerce(cx, checked, ret, v.span))
                        .and_then(|c| self.kept(cx, c, v.span))
                        .map(|c| c.expr),
                };
                if let (Some(e), Ty::Str) = (&value, cx.ret) {
                    match str_origin(cx, e) {
                        Some(locals) => {
                            let at = *span;
                            cx.strs.returned.extend(locals.into_iter().map(|l| (l, at)));
                        }
                        None => self.report_str_return(*span),
                    }
                }
                self.check_set_params(cx, *span);
                self.defer_moves_at(cx, 0, false, Some(*span));
                Some(TStmt::Return(value))
            }
            Stmt::If(i) => Some(self.if_stmt(cx, i)),
            Stmt::While { cond, body, .. } => {
                let ((cond, facts, body), head, exits) =
                    self.loop_body(cx, &body.stmts, None, |ck, cx| {
                        let (cond, facts) = ck.condition(cx, cond);
                        cx.env.apply(&facts.when_true);
                        let body = ck.block(cx, &body.stmts);
                        let reaches_end = !diverges(&body);
                        ((cond, facts, body), reaches_end)
                    });
                // The loop ends at its head when the condition is false, or
                // at a `break`.
                let mut done = head;
                done.apply(&facts.when_false);
                cx.env = exits.into_iter().fold(done, Env::join);
                Some(TStmt::While(cond.unwrap_or_else(placeholder_bool), body))
            }
            Stmt::Loop { body, .. } => {
                let (body, _, exits) = self.loop_body(cx, &body.stmts, None, |ck, cx| {
                    let body = ck.block(cx, &body.stmts);
                    let reaches_end = !diverges(&body);
                    (body, reaches_end)
                });
                // Only a `break` leaves.
                cx.env = exits.into_iter().fold(Env::unreachable(), Env::join);
                Some(TStmt::Loop(body))
            }
            Stmt::For {
                comptime: true,
                var,
                iter,
                body,
                span,
            } => self.comptime_for(cx, var, iter, body, *span),
            Stmt::For {
                var, iter, body, ..
            } => {
                cx.scopes.push(HashMap::new());
                let out = self.for_stmt(cx, var, iter, body);
                cx.scopes.pop();
                out
            }
            Stmt::Break(span) | Stmt::Continue(span) => {
                if cx.loop_depth == 0 && cx.defer_depth > 0 {
                    self.check_not_in_defer(cx, *span, "`break` or `continue`");
                    return None;
                }
                if cx.ct_loop_floor == Some(cx.loop_depth) {
                    self.diags.push(
                        Diagnostic::error(
                            *span,
                            "`break` and `continue` can't leave a `comptime for`",
                        )
                        .with_help("its body is repeated for each element when compiling: it isn't a loop when the program runs"),
                    );
                    return None;
                }
                if cx.loop_depth == 0 {
                    self.error(
                        *span,
                        "`break` and `continue` can only be used inside a loop",
                    );
                    return None;
                }
                let depth = cx.loops.last().expect("in a loop").scope_depth;
                let mut env = cx.env.clone();
                for l in self.defer_moves_at(cx, depth, false, Some(*span)) {
                    env.declare_uninit(l);
                }
                let edges = cx.loops.last_mut().expect("in a loop");
                Some(if matches!(stmt, Stmt::Break(_)) {
                    edges.exits.push(env);
                    TStmt::Break
                } else {
                    edges.next.push(env);
                    TStmt::Continue
                })
            }
            Stmt::Unsafe(block) => {
                cx.unsafe_depth += 1;
                let body = self.block(cx, &block.stmts);
                cx.unsafe_depth -= 1;
                Some(TStmt::Block(body))
            }
            Stmt::Match {
                comptime: true,
                value,
                arms,
                ..
            } => self.comptime_match(cx, value, arms),
            Stmt::Match {
                value, arms, span, ..
            } => {
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
        // A call that throws gives its result, to match `ok` and `err`.
        let checked = match &value.kind {
            ExprKind::Call(callee, args) => self.whole(cx, value.span, |ck, cx| {
                ck.call(cx, callee, args, value.span, true, None)
            })?,
            _ => self.expr(cx, value, None)?,
        };
        // When a call fails, the variables it was to assign (`set`) aren't.
        let sets = match (&value.kind, ty_is_result(&checked)) {
            (ExprKind::Call(..), true) => std::mem::take(&mut cx.call_sets),
            _ => Vec::new(),
        };
        let ty = checked.ty();
        if ty == Ty::Bool || generic::num(ty).is_some() {
            return self.value_match(cx, checked, arms, span);
        }
        let Some(def) = ty.sum() else {
            self.error(
                value.span,
                format!("`match` needs an enum, an optional, an integer or a `bool`, found `{ty}`"),
            );
            return None;
        };
        let mut before = Vec::new();
        let matched = self.scrutinee(cx, checked, value.span, &mut before)?;
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
            let alternatives = arm.pattern.alternatives();
            for pattern in alternatives {
                match pattern {
                    ast::Pattern::Value(_) | ast::Pattern::Range(..) | ast::Pattern::Or(..) => {
                        self.diags.push(
                            Diagnostic::error(
                                pattern.span(),
                                format!("a pattern of `{ty}` is the name of one of its variants"),
                            )
                            .with_help("write the variant's name alone, as in `circle(c, r) =>`"),
                        );
                        ok = false;
                    }
                    ast::Pattern::Wildcard(wspan) => {
                        let rest: Vec<u32> = (0..covered.len() as u32)
                            .filter(|&v| !covered[v as usize])
                            .collect();
                        self.lint_wildcard(cx, ty, &def, &rest, *wspan);
                        variants.extend(rest);
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
                                Some(_) if alternatives.len() > 1 => {
                                    self.diags.push(
                                    Diagnostic::error(
                                        pattern.span(),
                                        "variants listed with `|` can't bind payload fields",
                                    )
                                    .with_help(format!(
                                        "match `{}` by its name alone, or in an arm of its own",
                                        name.name
                                    )),
                                );
                                    ok = false;
                                }
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
                                    for (k, (b, f)) in names.iter().zip(&variant.fields).enumerate()
                                    {
                                        if b.name == "_" {
                                            continue;
                                        }
                                        if bindings.iter().any(|(o, ..)| o.name == b.name) {
                                            self.error(
                                                b.span,
                                                format!(
                                                    "`{}` is bound twice in this pattern",
                                                    b.name
                                                ),
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
            }
            // The `err` arm of a call's result (variant 1).
            if variants.contains(&1) {
                for &l in &sets {
                    cx.env.declare_uninit(l);
                }
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
                    // A binding reads the payload in place: keeping it
                    // moves the matched value.
                    if !fty.is_copy() {
                        cx.projections.insert(local, value.expr.clone());
                    }
                    self.record_value(cx, local, &value);
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
                        name_list(&missing)
                    ),
                )
                .with_help("add an arm for each, or `_ => ...` for the rest"),
            );
            ok = false;
        }
        if !ok {
            // Like a `return` that fails to check, a `match` whose arms all
            // leave still ends control flow, to avoid a "missing return"
            // error. Lowering never sees it: the program has errors.
            if !tarms.is_empty() && tarms.iter().all(|a| diverges(&a.body)) {
                return Some(TStmt::Return(None));
            }
            return None;
        }
        before.push(TStmt::Match {
            value: matched,
            arms: tarms,
        });
        Some(one_stmt(before))
    }

    /// `match value { ... }` on an integer or a `bool` (`checked`), as a
    /// chain of `if`s on the matched value: an arm runs when the value is
    /// one of its pattern's values and no earlier arm matched it. Patterns
    /// are values known when compiling and ranges of them, `|` lists
    /// several, and `_` matches the rest. Every value must be matched.
    ///
    /// When the value is a term (plus a constant), each arm knows it's
    /// within its pattern's values (from the smallest to the largest), and
    /// that no earlier arm matched: a value or range at an end of what's
    /// left narrows it, a single value inside gives a hole.
    fn value_match(
        &mut self,
        cx: &mut FnCx,
        checked: expr::Checked,
        arms: &[ast::Arm],
        span: Span,
    ) -> Option<TStmt> {
        let ty = checked.ty();
        // The values the matched value can have.
        let all = match ty {
            Ty::Bool => Range { lo: 0, hi: 1 },
            _ => checked.int_range(),
        };
        let term = checked.term;
        let full = type_range(ty).unwrap_or(all);
        let mut before = Vec::new();
        let matched = matched_local(cx, checked, &mut before);
        // The facts when no arm so far matched.
        let mut rest = cx.env.clone();
        let mut covered: Vec<Range> = Vec::new();
        let mut wildcard: Option<Span> = None;
        let mut ok = true;
        let mut envs = Vec::new();
        let mut tarms: Vec<(Option<TExpr>, Vec<TStmt>)> = Vec::new();
        for arm in arms {
            if wildcard.is_some() {
                self.diags.push(
                    Diagnostic::error(
                        arm.pattern.span(),
                        "this arm is never used: it comes after `_`",
                    )
                    .with_help("`_` matches every value not matched before it"),
                );
                ok = false;
            }
            let mut ranges: Vec<Range> = Vec::new();
            let mut wild = None;
            for pattern in arm.pattern.alternatives() {
                if let ast::Pattern::Wildcard(w) = pattern {
                    wild = Some(*w);
                    continue;
                }
                let Some(r) = self.pattern_range(cx, pattern, ty) else {
                    ok = false;
                    continue;
                };
                let earlier: Vec<Range> = covered.iter().chain(&ranges).copied().collect();
                if wildcard.is_none() && uncovered(&earlier, r).is_none() {
                    self.error(
                        pattern.span(),
                        "this pattern is never used: its values are matched before it",
                    );
                    ok = false;
                }
                ranges.push(r);
            }
            if let Some(w) = wild {
                if wildcard.is_none() && uncovered(&covered, all).is_none() {
                    self.diags.push(Diagnostic::warning(
                        w,
                        format!("this `_` matches nothing: every value of `{ty}` is matched above"),
                    ));
                }
                wildcard = wildcard.or(Some(w));
            }
            cx.env = rest.clone();
            if wild.is_none()
                && let (Some(t), Some(first)) = (term, ranges.first())
            {
                // Within the pattern's values.
                let hull = ranges.iter().fold(*first, |h, r| h.hull(*r));
                cx.env.apply(&[facts::Fact::Narrow {
                    term: t.term,
                    bound: Range {
                        lo: hull.lo.saturating_sub(t.offset),
                        hi: hull.hi.saturating_sub(t.offset),
                    },
                    full,
                }]);
            }
            cx.scopes.push(HashMap::new());
            let body = self.block(cx, &arm.body.stmts);
            cx.scopes.pop();
            envs.push((std::mem::take(&mut cx.env), diverges(&body)));
            let cond = match wild {
                Some(_) => None,
                None => Some(value_cond(&matched, &ranges, all)),
            };
            tarms.push((cond, body));
            // What the arms after it know: it didn't match.
            if wild.is_some() {
                rest = Env::unreachable();
            } else if let Some(t) = term {
                for r in &ranges {
                    exclude(&mut rest, t, *r, all, full);
                }
            }
            covered.extend(ranges);
        }
        let exhaustive = wildcard.is_some() || uncovered(&covered, all).is_none();
        if let (false, Some(v)) = (wildcard.is_some(), uncovered(&covered, all)) {
            let msg = match ty {
                Ty::Bool => format!("this `match` doesn't handle `{}`", v == 1),
                _ => format!("this `match` doesn't handle every `{ty}`: {v} isn't matched"),
            };
            self.diags.push(
                Diagnostic::error(span, msg)
                    .with_help("add an arm for the rest, or `_ => ...` for every value left"),
            );
            ok = false;
        }
        cx.env = Self::join_branches(envs);
        if !ok {
            // As for a `match` on an enum: kept to end control flow.
            if !tarms.is_empty() && tarms.iter().all(|(_, b)| diverges(b)) {
                return Some(TStmt::Return(None));
            }
            return None;
        }
        // An `if` per arm; the last one of a `match` that handles every
        // value needs no test.
        let mut chain: Option<Vec<TStmt>> = None;
        for (cond, body) in tarms.into_iter().rev() {
            chain = Some(match (cond, chain) {
                (Some(c), Some(rest)) => vec![TStmt::If(c, body, rest)],
                (Some(c), None) if !exhaustive => vec![TStmt::If(c, body, Vec::new())],
                (_, _) => body,
            });
        }
        before.push(TStmt::Block(chain.unwrap_or_default()));
        Some(one_stmt(before))
    }

    /// The values of a pattern of a `match` on a value of type `ty` (an
    /// integer or `bool`): a value known when compiling, or a range of them.
    fn pattern_range(&mut self, cx: &mut FnCx, pattern: &ast::Pattern, ty: Ty) -> Option<Range> {
        match pattern {
            ast::Pattern::Value(e) => self.pattern_value(cx, e, ty).map(Range::exact),
            // A name alone is a constant.
            ast::Pattern::Variant {
                name,
                bindings: None,
                ..
            } => {
                let e = ast::Expr {
                    kind: ExprKind::Name(name.name.clone()),
                    span: name.span,
                };
                self.pattern_value(cx, &e, ty).map(Range::exact)
            }
            ast::Pattern::Range(..) if ty == Ty::Bool => {
                self.error(
                    pattern.span(),
                    "a `bool` is matched by `true` and `false`, not ranges",
                );
                None
            }
            ast::Pattern::Range(lo, hi, span) => {
                let (lo, hi) = (
                    self.pattern_value(cx, lo, ty),
                    self.pattern_value(cx, hi, ty),
                );
                let (lo, hi) = (lo?, hi?);
                if lo > hi {
                    self.error(
                        *span,
                        format!("this range is empty: {lo} is more than {hi}"),
                    );
                    return None;
                }
                Some(Range { lo, hi })
            }
            _ => {
                self.diags.push(
                    Diagnostic::error(
                        pattern.span(),
                        format!("a pattern of `{ty}` is a value, a range `lo..=hi` or `_`"),
                    )
                    .with_help("variants with payloads are for enums and optionals"),
                );
                None
            }
        }
    }

    /// The value of the pattern `e` against a `ty`: a literal or a constant
    /// (`bool`s as 0 and 1).
    fn pattern_value(&mut self, cx: &mut FnCx, e: &ast::Expr, ty: Ty) -> Option<i128> {
        let c = self.expr(cx, e, Some(ty))?;
        let c = self.coerce(cx, c, ty, e.span)?;
        match (&c.expr.kind, c.range) {
            (TExprKind::Bool(b), _) => Some(i128::from(*b)),
            (_, Some(r)) if r.lo == r.hi && ty != Ty::Bool => Some(r.lo),
            _ => {
                self.error(
                    e.span,
                    "a pattern must be a value known when compiling: a literal or a constant",
                );
                None
            }
        }
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
            if def.pkg == cx.pkg || ty.as_optional().is_some() || ty.as_result().is_some() {
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
                    name_list(&names)
                )),
            );
        }
    }

    /// `if let name = opt { ... } else { ... }`: a `match` on the optional
    /// `opt`, with `name` bound to its value in the first block.
    /// The local a `match` or an `if let` looks into, for the value
    /// `checked` (docs/allocation.md, Partial moves and patterns): the
    /// local itself; for another place of a type that isn't `Copy`, a
    /// hidden local that reads it in place, so its bindings do too; or
    /// else a hidden local the value is stored in, by a statement added to
    /// `before`, which owns it (destroyed when the statement ends).
    fn scrutinee(
        &mut self,
        cx: &mut FnCx,
        checked: expr::Checked,
        span: Span,
        before: &mut Vec<TStmt>,
    ) -> Option<TExpr> {
        if let TExprKind::Local(_) = checked.expr.kind {
            return Some(checked.expr);
        }
        let ty = checked.ty();
        if !ty.is_copy() && generic::place_local(cx, &checked.expr).is_some() {
            let place = checked.expr.clone();
            let matched = matched_local(cx, checked, before);
            if let TExprKind::Local(m) = matched.kind {
                cx.projections.insert(m, place);
            }
            return Some(matched);
        }
        let checked = self.kept(cx, checked, span)?;
        let matched = matched_local(cx, checked, before);
        if let TExprKind::Local(m) = matched.kind
            && !ty.is_copy()
        {
            before.push(TStmt::Drop {
                local: m,
                init: true,
            });
        }
        Some(matched)
    }

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
        // What a refined result says about the value in it.
        let known = checked.as_ref().and_then(|c| c.payload.clone());
        let matched = match (checked, inner) {
            (Some(c), Some(_)) => self.scrutinee(cx, c, i.cond.span, &mut before),
            _ => None,
        };
        let entry = cx.env.clone();

        cx.scopes.push(HashMap::new());
        // The value's type, or `()` if it's in error (only to keep checking).
        let local = self.declare(cx, &name.name, inner.unwrap_or(Ty::Unit), false);
        cx.env.assign(local, known.as_ref().and_then(|k| k.0));
        if let Some(k) = &known {
            let facts = refine::known_facts(cx, local, &k.1);
            cx.env.apply(&facts);
        }
        let mut then = Vec::new();
        if let (Some(m), Some(t)) = (&matched, inner) {
            // The binding reads the value in place, as in a `match`.
            let value = payload(m, 1, 0, t);
            if !t.is_copy() {
                cx.projections.insert(local, value.clone());
            }
            then.push(TStmt::Init(local, value));
        }
        then.extend(self.block(cx, &i.then.stmts));
        cx.scopes.pop();
        let then_env = std::mem::replace(&mut cx.env, entry);

        let otherwise = match &i.otherwise {
            None => Vec::new(),
            Some(ast::Else::Block(b)) => self.block(cx, &b.stmts),
            Some(ast::Else::If(inner)) => {
                vec![TStmt::Loc(inner.span), self.if_stmt(cx, inner)]
            }
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
        let owned = !matches!(checked.expr.kind, TExprKind::Local(_));
        let checked = if owned {
            self.kept(cx, checked, init.span)?
        } else {
            checked
        };
        // What a refined result says about the value in it.
        let known = checked.payload.clone();
        let matched = matched_local(cx, checked, &mut before);
        if let TExprKind::Local(m) = matched.kind
            && owned
            && !matched.ty.is_copy()
        {
            before.push(TStmt::Drop {
                local: m,
                init: true,
            });
        }
        let entry = cx.env.clone();
        let else_body = self.block(cx, &otherwise.stmts);
        cx.env = entry;
        if !diverges(&else_body) {
            self.diags.push(
                Diagnostic::error(
                    otherwise.span,
                    "the `else` block of `let ... else` must leave",
                )
                .with_help(
                    "end it with `return`, `break`, `continue`, or a call to a `never` function like `os.exit`",
                ),
            );
            // Its type is known: later uses are checked against it.
            if !cx.scopes.last().expect("scope").contains_key(&name.name) {
                self.declare(cx, &name.name, inner, mutable);
            }
            return None;
        }
        if cx.scopes.last().expect("scope").contains_key(&name.name) {
            self.error(
                name.span,
                format!("`{}` is already declared in this block", name.name),
            );
            return None;
        }
        let mut value = expr::Checked::new(
            TExprKind::Payload(Box::new(matched.clone()), 1, 0),
            inner,
            None,
        );
        if let Some(k) = known {
            value.range = k.0;
            value.known = k.1;
        }
        let value = self.kept(cx, value, name.span)?;
        let local = self.declare(cx, &name.name, inner, mutable);
        self.record_value(cx, local, &value);
        if !inner.is_copy() {
            cx.after.push(TStmt::Drop { local, init: true });
        }
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

    /// Check a loop's body (with `check`, which also says whether the body
    /// can reach its end), starting from the facts at the loop's head.
    /// Returns what `check` gave, the head facts, and the facts at each
    /// `break`.
    ///
    /// The head facts are the facts before the loop, with those about the
    /// variables the loop assigns kept only as far as every iteration keeps
    /// them. A candidate head holds when each of its facts about those
    /// variables holds again at every back-edge (`continue`, or the end of
    /// the body). The body is checked from each candidate in turn, at most
    /// six times; the first that holds is the head, and only the check from
    /// it counts (the others are rolled back with their errors). From the
    /// facts before the loop, `E` (docs/safety.md, "Facts through loops"):
    ///
    /// 1. `E` itself;
    /// 2. `C`: `E` loosened to cover the back-edges of check 1;
    /// 3. `W`: `C` without the facts that failed at a back-edge of check 2
    ///    (each end of a range on its own). If `W` doesn't hold either, the
    ///    head is `E` with everything about the variables forgotten;
    /// 4. `T`: `N` (below) with range ends moved in to the thresholds of
    ///    check 3, if that changes it;
    /// 5. `N`: `E` loosened to cover the back-edges of check 3. If `N` is
    ///    `W` or doesn't hold, the head is `W`.
    ///
    /// A loop higher than [`SEARCH_HEIGHT`] doesn't search: its head is `E`
    /// with everything about the variables forgotten.
    ///
    /// A variable a value is moved out of in the body (see
    /// [`Checker::consume`]) is unassigned at a back-edge: it's unassigned
    /// at the head too, and the body is checked again from it.
    fn loop_body<T>(
        &mut self,
        cx: &mut FnCx,
        body: &[Stmt],
        index: Option<&ForIndex>,
        mut check: impl FnMut(&mut Self, &mut FnCx) -> (T, bool),
    ) -> (T, Env, Vec<Env>) {
        let mark = self.mark(cx);
        let index_local = index.map(|ix| ix.local);
        let (mut out, mut head, mut edges) = self.loop_search(cx, body, index, &mut check);
        loop {
            let moved: Vec<LocalId> = edges
                .next
                .iter()
                .filter(|e| !e.dead)
                .flat_map(Env::uninit_locals)
                .filter(|&l| l < mark.locals && !head.dead && !head.is_uninit(l))
                .collect();
            if moved.is_empty() {
                return (out, head, edges.exits);
            }
            for &l in &moved {
                head.declare_uninit(l);
            }
            self.rollback(cx, &mark);
            cx.moved.extend(moved);
            (out, edges) = self.loop_pass(cx, head.clone(), index_local, &mut check);
        }
    }

    /// The search for a loop's head (see [`Checker::loop_body`]): what
    /// `check` gave, the head, and where the body left an iteration.
    fn loop_search<T>(
        &mut self,
        cx: &mut FnCx,
        body: &[Stmt],
        index: Option<&ForIndex>,
        check: &mut impl FnMut(&mut Self, &mut FnCx) -> (T, bool),
    ) -> (T, Env, LoopEdges) {
        use facts::Loosen::{Cover, Drop};
        let mut assigned = assigned_locals(cx, body);
        if let Some(ix) = index {
            assigned.insert(ix.local);
        }
        let about = |l: LocalId| assigned.contains(&l);
        let tys: Vec<Ty> = cx.locals.iter().map(|l| l.ty).collect();
        let full = |t: Term| term_full(&tys, t);
        let holds = |head: &Env, edges: &LoopEdges| {
            edges.next.iter().all(|e| head.holds_in(about, full, e))
        };
        let mut entry = cx.env.clone();
        entry.apply(&head_relations(&entry, &tys, &assigned, index));
        let index = index.map(|ix| ix.local);
        let mark = self.mark(cx);
        // The simplest head: everything about the variables forgotten.
        let forget_all = |entry: Env| {
            let mut base = entry;
            for &local in &assigned {
                base.forget(local);
            }
            base
        };
        if 1 + loop_height(body) > SEARCH_HEIGHT {
            let base = forget_all(entry);
            let (out, edges) = self.loop_pass(cx, base.clone(), index, check);
            return (out, base, edges);
        }

        // 1. E
        let (out, edges) = self.loop_pass(cx, entry.clone(), index, check);
        if holds(&entry, &edges) {
            return (out, entry, edges);
        }
        // 2. C
        self.rollback(cx, &mark);
        let c = entry.loosen(about, full, &edges.next, Cover);
        let (out, edges) = self.loop_pass(cx, c.clone(), index, check);
        if holds(&c, &edges) {
            return (out, c, edges);
        }
        // 3. W
        self.rollback(cx, &mark);
        let w = c.loosen(about, full, &edges.next, Drop);
        let (out, edges) = self.loop_pass(cx, w.clone(), index, check);
        if !holds(&w, &edges) {
            self.rollback(cx, &mark);
            let base = forget_all(entry);
            let (out, edges) = self.loop_pass(cx, base.clone(), index, check);
            return (out, base, edges);
        }
        // 4. T, from N
        let n = entry.loosen(about, full, &edges.next, Cover);
        let t = n.to_thresholds(&entry, about, full, &edges.thresholds);
        let mut w_checked = Some((out, edges));
        if !t.same(&n) {
            self.rollback(cx, &mark);
            w_checked = None;
            let (out, edges) = self.loop_pass(cx, t.clone(), index, check);
            if holds(&t, &edges) {
                return (out, t, edges);
            }
        }
        // 5. N
        if !n.same(&w) {
            self.rollback(cx, &mark);
            let (out, edges) = self.loop_pass(cx, n.clone(), index, check);
            if holds(&n, &edges) {
                return (out, n, edges);
            }
            w_checked = None;
        }
        let (out, edges) = match w_checked {
            Some(checked) => checked,
            None => {
                self.rollback(cx, &mark);
                self.loop_pass(cx, w.clone(), index, check)
            }
        };
        (out, w, edges)
    }

    /// Check a loop's body once, from the facts `head`. For a `for` loop,
    /// the back-edges go on to the next index: `index` is advanced by 1.
    fn loop_pass<T>(
        &mut self,
        cx: &mut FnCx,
        head: Env,
        index: Option<LocalId>,
        check: &mut impl FnMut(&mut Self, &mut FnCx) -> (T, bool),
    ) -> (T, LoopEdges) {
        cx.env = head;
        cx.loops.push(LoopEdges {
            scope_depth: cx.scopes.len(),
            ..LoopEdges::default()
        });
        cx.loop_depth += 1;
        let (out, reaches_end) = check(self, cx);
        cx.loop_depth -= 1;
        let mut edges = cx.loops.pop().expect("pushed above");
        if reaches_end {
            edges.next.push(std::mem::take(&mut cx.env));
        }
        if let Some(ix) = index {
            for e in &mut edges.next {
                let next = e.range(Term::Local(ix)).map(|r| Range {
                    lo: r.lo + 1,
                    hi: r.hi + 1,
                });
                e.shift(ix, next, 1);
            }
        }
        (out, edges)
    }

    /// What a trial check of a loop body changes: errors, locals, and
    /// constants evaluated (whose errors are reported once).
    fn mark(&self, cx: &FnCx) -> Mark {
        Mark {
            diags: self.diags.len(),
            locals: cx.locals.len(),
            consts: self.consts.iter().map(|c| c.state).collect(),
            strs: cx.strs.clone(),
            moved: cx.moved.clone(),
            generic_calls: self.generic_calls.len(),
            checked: self.checked_order.len(),
            tables: self.tables.len(),
            const_exprs: self.const_exprs.len(),
        }
    }

    fn rollback(&mut self, cx: &mut FnCx, mark: &Mark) {
        self.diags.truncate(mark.diags);
        cx.locals.truncate(mark.locals);
        cx.failed.retain(|&l| l < mark.locals);
        cx.ct_values.retain(|&l, _| l < mark.locals);
        cx.place_refines.retain(|&l, _| l < mark.locals);
        cx.projections.retain(|&l, _| l < mark.locals);
        cx.temps.retain(|&l| l < mark.locals);
        cx.defer_moves.retain(|m| m.local < mark.locals);
        cx.strs = mark.strs.clone();
        cx.moved = mark.moved.clone();
        self.generic_calls.truncate(mark.generic_calls);
        for (c, &state) in self.consts.iter_mut().zip(&mark.consts) {
            c.state = state;
        }
        // The functions checked on demand since, for constants evaluated
        // since, are checked again when needed, so their errors are
        // reported once.
        for id in self.checked_order.drain(mark.checked..) {
            self.func_states[id] = FuncState::Unchecked;
        }
        self.tables.truncate(mark.tables);
        self.const_exprs.truncate(mark.const_exprs);
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
        let mut whole = HashSet::new();
        whole_assigned_names(&body.stmts, &mut whole);
        let usize_ty = self.usize_ty();
        let mut before = Vec::new();
        // The range, and for `for x in xs`, the name of the sequence.
        let (start, end, each) = match iter {
            ast::ForIter::Range(a, b) => {
                // Ranges are mostly for indexing: two untyped bounds are `usize`.
                let untyped =
                    self.untyped_int(cx, a).is_some() && self.untyped_int(cx, b).is_some();
                let (start, end) = self.operands(cx, a, b, untyped.then_some(usize_ty))?;
                if generic::num(start.ty()).is_none() {
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
                // The sequence the body reads elements of: the local itself,
                // an array constant itself (read in place, with the facts
                // about its elements), or else a hidden copy.
                let (seq_ast, seq_t) = match (&xs.kind, &seq.expr.kind) {
                    (ExprKind::Name(name), TExprKind::Local(_)) if !assigned.contains(name) => {
                        (xs.clone(), seq.expr)
                    }
                    (_, TExprKind::Table(_)) => (xs.clone(), seq.expr),
                    _ => {
                        self.check_looped_slice(cx, &seq.expr, &assigned, xs.span)?;
                        // A sequence that isn't `Copy` moves into it, and is
                        // destroyed after the loop.
                        let seq = self.kept(cx, seq, xs.span)?;
                        let hidden = self.declare(cx, SEQ, seq.ty(), false);
                        self.record_value(cx, hidden, &seq);
                        let ty = seq.ty();
                        before.push(TStmt::Init(hidden, seq.expr));
                        if !ty.is_copy() {
                            before.push(TStmt::Drop {
                                local: hidden,
                                init: true,
                            });
                        }
                        let name = ast::Expr {
                            kind: ExprKind::Name(SEQ.to_owned()),
                            span: xs.span,
                        };
                        let local = TExpr {
                            kind: TExprKind::Local(hidden),
                            ty,
                        };
                        (name, local)
                    }
                };
                let end = match len {
                    Some(Len::Known(n)) => {
                        let n = i128::from(n);
                        expr::Checked::new(TExprKind::Int(n), usize_ty, Some(Range::exact(n)))
                    }
                    Some(Len::Param(p)) => self.param_len(cx, p),
                    None => self.view_len(cx, seq_t.clone()),
                };
                let start = expr::Checked::new(TExprKind::Int(0), usize_ty, Some(Range::exact(0)));
                (start, end, Some((seq_ast, seq_t, elem)))
            }
        };

        // The index is a local of the loop's head too: the head can relate
        // the variables the body assigns to it.
        let ty = start.ty();
        let index = match &each {
            Some(_) => self.declare(cx, INDEX, ty, false),
            None => self.declare(cx, &var.name, ty, false),
        };
        let for_index = ForIndex {
            local: index,
            start: start.int_range(),
            start_term: start.term,
        };
        // A bound that's a term the body doesn't assign keeps its value for
        // the whole loop, so the index can be related to it.
        let unassigned = |cx: &FnCx, t: Term| {
            let local = &cx.locals[t.local()];
            local.mutable_view()
                || !assigned.contains(&local.name)
                || (local.ty.is_view() && !whole.contains(&local.name))
        };
        let (stmts, head, exits) = self.loop_body(cx, &body.stmts, Some(&for_index), |ck, cx| {
            // What the body knows about the loop variable.
            let (lo, hi) = (start.int_range().lo, end.int_range().hi - 1);
            // An empty range: the body never runs, and any range will do.
            let full = type_range(ty).expect("an integer");
            cx.env.apply(&[facts::Fact::Narrow {
                term: Term::Local(index),
                bound: Range { lo, hi: hi.max(lo) },
                full,
            }]);
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

            let mut stmts = Vec::new();
            if let Some((seq_ast, seq_t, elem)) = &each {
                // let x = seq[$i]
                let element = ast::Expr {
                    kind: ExprKind::Index(
                        Box::new(ast::Expr {
                            span: var.span,
                            ..seq_ast.clone()
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
                    let index = cx.lookup(INDEX).expect("declared");
                    let kind = TExprKind::Index(
                        Box::new(seq_t.clone()),
                        Box::new(TExpr {
                            kind: TExprKind::Local(index),
                            ty: usize_ty,
                        }),
                    );
                    Some(expr::Checked::new(kind, *elem, None))
                } else {
                    ck.expr(cx, &element, Some(*elem))
                };
                let x = ck.declare(cx, &var.name, *elem, false);
                match value {
                    Some(value) => {
                        // It reads the element in place: it can't be kept.
                        if !elem.is_copy() {
                            cx.projections.insert(x, value.expr.clone());
                        }
                        ck.record_value(cx, x, &value);
                        stmts.push(TStmt::Init(x, value.expr));
                    }
                    None => {
                        cx.failed.insert(x);
                    }
                }
            }
            stmts.extend(ck.block(cx, &body.stmts));
            let reaches_end = !diverges(&stmts);
            (stmts, reaches_end)
        });
        // The loop ends at its head (the head facts still hold) when the
        // index has reached the end: `end <= i`, and `i <= end` if the start
        // is at most the end. Or it ends at a `break`.
        let mut done = head;
        let (s, e) = (start.int_range(), end.int_range());
        let starts_below = s.hi <= e.lo
            || matches!((start.term, end.term), (Some(a), Some(b)) if done.diff_bound(a, b).is_some_and(|c| c <= 0));
        let full = type_range(ty).expect("an integer");
        let mut exit_facts = vec![facts::Fact::Narrow {
            term: Term::Local(index),
            bound: Range {
                lo: e.lo,
                hi: if starts_below { e.hi } else { s.hi.max(e.hi) },
            },
            full,
        }];
        if let Some(b) = end.term
            && unassigned(cx, b.term)
        {
            // b + k <= i: b - i <= -k
            exit_facts.push(facts::Fact::Rel {
                a: b.term,
                b: Term::Local(index),
                c: -b.offset,
            });
            if starts_below {
                exit_facts.push(facts::Fact::Rel {
                    a: Term::Local(index),
                    b: b.term,
                    c: b.offset,
                });
            }
        }
        done.apply(&exit_facts);
        cx.env = exits.into_iter().fold(done, Env::join);

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

    /// `for x in a[i..j]` views `a` for the whole loop, so the body can't
    /// change the array `a` (whose elements it would then see change). An
    /// `inout` slice is read as the loop goes, as in `for x in xs`.
    fn check_looped_slice(
        &mut self,
        cx: &FnCx,
        seq: &TExpr,
        assigned: &HashSet<String>,
        span: Span,
    ) -> Option<()> {
        let mut root = seq;
        while let TExprKind::Slice(base, ..)
        | TExprKind::ToSlice(base)
        | TExprKind::Index(base, _)
        | TExprKind::Field(base, _) = &root.kind
        {
            root = base;
        }
        if !matches!(seq.kind, TExprKind::Slice(..)) {
            return Some(());
        }
        if let TExprKind::Local(l) = root.kind
            && !cx.locals[l].ty.is_view()
            && assigned.contains(&cx.locals[l].name)
        {
            let name = &cx.locals[l].name;
            self.diags.push(
                Diagnostic::error(
                    span,
                    format!("cannot loop over a slice of `{name}` while the loop changes `{name}`"),
                )
                .with_help("loop over the indexes instead: `for k in i..j`"),
            );
            return None;
        }
        Some(())
    }

    /// A slice stored in a local must not see its array change: the array
    /// can't be changed while a view of it is in use (docs/memory.md, Views),
    /// and until the compiler checks that, a slice local may only view a
    /// `let` array (or part of one), or part of another view. A slice of a
    /// `var` array or of a temporary can still be passed to a function.
    fn check_kept_view(&mut self, cx: &FnCx, value: &expr::Checked, span: Span) -> Option<()> {
        // A slice `v[i..j]` views what `v` views.
        let mut viewed = &value.expr;
        while let TExprKind::Slice(base, ..) = &viewed.kind {
            viewed = base;
        }
        let sliced = !std::ptr::eq(viewed, &value.expr);
        // A copy of an `inout` slice, or a slice of one, would see its
        // elements change.
        if let TExprKind::Local(l) = viewed.kind
            && cx.locals[l].mutable_view()
        {
            let name = &cx.locals[l].name;
            let what = if sliced { "a slice" } else { "a copy" };
            self.diags.push(
                Diagnostic::error(
                    span,
                    format!("cannot keep {what} of `{name}`, an `inout` slice"),
                )
                .with_help(format!(
                    "its elements can change; use `{name}` itself, or pass it to the function that takes the slice"
                )),
            );
            return None;
        }
        let TExprKind::ToSlice(array) = &viewed.kind else {
            return Some(());
        };
        let mut root = &**array;
        while let TExprKind::Index(base, _) | TExprKind::Field(base, _) = &root.kind {
            root = base;
        }
        let diag = match root.kind {
            // An array constant never changes.
            TExprKind::Table(_) => return Some(()),
            // Reassigning a `var` view doesn't change what it viewed.
            TExprKind::Local(l)
                if !cx.locals[l].mutable_view()
                    && (!cx.locals[l].mutable || cx.locals[l].ty.is_view()) =>
            {
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
            self.unknown_target(cx, name, root.span);
            return None;
        };
        if cx.failed.contains(&local) {
            return None;
        }
        self.check_defer_assign(cx, local, name, target.span)?;
        let root_ty = cx.locals[local].ty;
        if root_ty.is_view() && !cx.locals[local].mutable_view() {
            self.diags.push(
                Diagnostic::error(
                    target.span,
                    format!("cannot assign through `{name}`, which is a read-only `{root_ty}`"),
                )
                .with_help(
                    "only the elements of an `inout` slice parameter can be assigned (`inout xs: []u8`)",
                ),
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
                .with_help(Self::immutable_help(cx, local, name)),
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
                    self.record_value(cx, hidden, &checked);
                    before.push(TStmt::Init(hidden, checked.expr));
                    **index = ast::Expr {
                        kind: ExprKind::Name(name),
                        span: index.span,
                    };
                }
                place = base;
            }
        }

        let target_span = target.span;
        let place = self.expr(cx, &target, None)?;
        self.check_read_only(cx, &place.expr, target_span)?;
        if !place.ty().is_copy() {
            Self::invalidate_projections(cx, local);
        }
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
        let checked = self.coerce(cx, checked, ty, value.span)?;
        let checked = self.kept(cx, checked, value.span)?;
        self.check_field_assign(cx, &place.expr, &checked, value.span);
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

    /// `if comptime cond { ... } else ...` in a function: only the branch
    /// `cond` picks is checked (the others only had to parse), and it's a
    /// block of its own. Without a value for `cond`, neither is.
    fn comptime_if(&mut self, cx: &mut FnCx, i: &ast::IfStmt) -> TStmt {
        let stmts = match self.comptime_cond(cx, &i.cond) {
            Some(true) => self.block(cx, &i.then.stmts),
            Some(false) => match &i.otherwise {
                None => Vec::new(),
                Some(ast::Else::Block(b)) => self.block(cx, &b.stmts),
                Some(ast::Else::If(inner)) => {
                    vec![TStmt::Loc(inner.span), self.if_stmt(cx, inner)]
                }
            },
            None => Vec::new(),
        };
        TStmt::Block(stmts)
    }

    /// The value of an `if comptime` condition in a function: an expression
    /// of constants, `target` and calls, evaluated now.
    fn comptime_cond(&mut self, cx: &FnCx, e: &ast::Expr) -> Option<bool> {
        let mut locals = Vec::new();
        expr_names(e, &mut locals);
        // A `comptime let` whose value failed (reported) fails silently.
        if locals
            .iter()
            .any(|(n, _)| cx.lookup(n).is_some_and(|l| cx.failed.contains(&l)))
        {
            return None;
        }
        if let Some((name, span)) = locals.into_iter().find(|(n, _)| {
            cx.lookup(n)
                .is_some_and(|l| !Self::is_comptime_local(cx, l))
        }) {
            self.diags.push(
                Diagnostic::error(
                    span,
                    format!("`{name}` is a variable, so this condition isn't known when compiling"),
                )
                .with_help("an `if comptime` condition uses constants, `target` and calls; use `if` to test a variable"),
            );
            return None;
        }
        let (mut ccx, init) = self.comptime_cx(cx);
        let c = self.expr(&mut ccx, e, Some(Ty::Bool))?;
        let c = self.coerce(&mut ccx, c, Ty::Bool, e.span)?;
        if let TExprKind::Bool(b) = c.expr.kind {
            return Some(b);
        }
        let subject = eval::Subject {
            what: "the condition",
            span: e.span,
            budget_span: None,
        };
        let v = self.evaluate_with(
            &c.expr,
            ccx.locals.len(),
            &init,
            eval::DEFAULT_STEPS,
            &subject,
        )?;
        match v {
            eval::Value::Bool(b) => Some(b),
            other => unreachable!("a `bool` condition gave {other:?}"),
        }
    }

    fn if_stmt(&mut self, cx: &mut FnCx, i: &ast::IfStmt) -> TStmt {
        if i.comptime {
            return self.comptime_if(cx, i);
        }
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
            Some(ast::Else::If(inner)) => {
                vec![TStmt::Loc(inner.span), self.if_stmt(cx, inner)]
            }
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
            .and_then(|c| self.coerce(cx, c, Ty::Bool, e.span))
        {
            Some(c) => {
                let facts = c.facts.map(|f| *f).unwrap_or_default();
                (Some(c.expr), facts)
            }
            None => (None, facts::CondFacts::default()),
        }
    }
}

/// The most scalars a constant that isn't an array of integers or `bool`
/// holds: it's built where it's used, not kept in read-only data.
const CONST_EXPR_MAX: u64 = 256;

/// Whether a constant can have type `ty`: an integer, `bool`, or an array,
/// struct, enum or optional of those (anything stored, but views and
/// pointers).
fn const_type(ty: Ty) -> bool {
    match ty {
        Ty::Int(_) | Ty::Bool => true,
        Ty::Array(_) => const_type(ty.as_array().expect("an array").0),
        Ty::Optional(_) => const_type(ty.as_optional().expect("an optional")),
        Ty::Struct(_) => ty
            .as_struct()
            .expect("a struct")
            .fields
            .iter()
            .all(|f| const_type(f.ty)),
        Ty::Enum(_) => ty
            .as_enum()
            .expect("an enum")
            .variants
            .iter()
            .all(|v| v.fields.iter().all(|f| const_type(f.ty))),
        _ => false,
    }
}

/// A value in a package-level `if comptime` condition.
enum CondVal {
    Bool(bool),
    Int(i128),
    /// A variant of an enum, by index.
    Enum(Ty, u32),
    /// `.name`, a variant of the enum it's compared with.
    Dot(ast::Ident),
}

/// The expression of an integer, or of an enum's variant without payload
/// (by index).
fn scalar_expr(ty: Ty, v: i128) -> TExpr {
    let kind = match ty {
        Ty::Enum(_) => TExprKind::Variant(v as u32, Vec::new()),
        _ => TExprKind::Int(v),
    };
    TExpr { kind, ty }
}

/// The scalar type at the bottom of an array type that can be a constant
/// (`u8` for `[12]u8` and `[2][3]u8`): an integer or `bool`.
pub fn table_leaf(ty: Ty) -> Option<Ty> {
    let (mut elem, _) = ty.as_array()?;
    while let Some((inner, _)) = elem.as_array() {
        elem = inner;
    }
    matches!(elem, Ty::Int(_) | Ty::Bool).then_some(elem)
}

/// Where the `str` value `e` comes from, if its storage is static: the
/// locals it's copied from (whose values must be static too), or `None` if
/// it may borrow from a parameter. A string literal is static, and so is
/// the result of a function returning a `str`, which returns only static
/// strings.
fn str_origin(cx: &FnCx, e: &TExpr) -> Option<Vec<LocalId>> {
    match &e.kind {
        // A call to a `never` function has no value at all.
        TExprKind::Str(_) | TExprKind::Call(..) | TExprKind::Never(_) => Some(Vec::new()),
        TExprKind::Local(l) if *l >= cx.params => Some(vec![*l]),
        TExprKind::Try(call) => str_origin(cx, call),
        TExprKind::Catch { call, handler, .. } => {
            let mut out = str_origin(cx, call)?;
            if let Handler::Value(v) = handler {
                out.extend(str_origin(cx, v)?);
            }
            Some(out)
        }
        _ => None,
    }
}

/// The smallest value of `all` that none of `ranges` holds, if any.
fn uncovered(ranges: &[Range], all: Range) -> Option<i128> {
    let mut sorted = ranges.to_vec();
    sorted.sort_by_key(|r| r.lo);
    let mut next = all.lo;
    for r in sorted {
        if r.lo > next {
            break;
        }
        if r.hi >= next {
            if r.hi >= all.hi {
                return None;
            }
            next = r.hi + 1;
        }
    }
    (next <= all.hi).then_some(next)
}

/// Learn in `env` that the value `t` (a term plus a constant, in `all`, of
/// a type whose range is `full`) isn't in `r`: at an end of what's left,
/// its range narrows; a single value inside it is a hole.
fn exclude(env: &mut Env, t: Linear, r: Range, all: Range, full: Range) {
    let cur = env
        .range(t.term)
        .map(|c| Range {
            lo: c.lo.saturating_add(t.offset),
            hi: c.hi.saturating_add(t.offset),
        })
        .and_then(|c| c.intersect(all))
        .unwrap_or(all);
    let fact = if r.lo <= cur.lo && r.hi >= cur.hi {
        *env = Env::unreachable();
        return;
    } else if r.lo <= cur.lo {
        facts::Fact::Narrow {
            term: t.term,
            bound: Range {
                lo: (r.hi + 1).saturating_sub(t.offset),
                hi: i128::MAX,
            },
            full,
        }
    } else if r.hi >= cur.hi {
        facts::Fact::Narrow {
            term: t.term,
            bound: Range {
                lo: i128::MIN,
                hi: (r.lo - 1).saturating_sub(t.offset),
            },
            full,
        }
    } else if r.lo == r.hi {
        facts::Fact::Hole {
            term: t.term,
            value: r.lo.saturating_sub(t.offset),
        }
    } else {
        return;
    };
    env.apply(&[fact]);
}

/// The condition that `matched` (an integer or `bool` with values in
/// `all`) is in one of `ranges`.
fn value_cond(matched: &TExpr, ranges: &[Range], all: Range) -> TExpr {
    let boolean = |kind: TExprKind| TExpr { kind, ty: Ty::Bool };
    let cmp = |op: CmpOp, v: i128| {
        boolean(TExprKind::Binary(
            TBinOp::Cmp(op),
            Box::new(matched.clone()),
            Box::new(TExpr {
                kind: TExprKind::Int(v),
                ty: matched.ty,
            }),
        ))
    };
    let one = |r: &Range| {
        if matched.ty == Ty::Bool {
            return if r.lo == 1 {
                matched.clone()
            } else {
                boolean(TExprKind::Unary(TUnOp::Not, Box::new(matched.clone())))
            };
        }
        if r.lo == r.hi {
            return cmp(CmpOp::Eq, r.lo);
        }
        match (r.lo > all.lo, r.hi < all.hi) {
            (true, true) => boolean(TExprKind::And(
                Box::new(cmp(CmpOp::Ge, r.lo)),
                Box::new(cmp(CmpOp::Le, r.hi)),
            )),
            (true, false) => cmp(CmpOp::Ge, r.lo),
            (false, true) => cmp(CmpOp::Le, r.hi),
            (false, false) => boolean(TExprKind::Bool(true)),
        }
    };
    let mut conds = ranges.iter().map(one);
    let first = conds
        .next()
        .unwrap_or_else(|| boolean(TExprKind::Bool(false)));
    conds.fold(first, |acc, c| {
        boolean(TExprKind::Or(Box::new(acc), Box::new(c)))
    })
}

/// The most scalars an array constant holds (16 MiB of `u8`).
const TABLE_MAX: u64 = 1 << 24;

/// How many scalars an array of type `ty` holds.
fn table_scalars(ty: Ty) -> u64 {
    match ty.as_known_array() {
        Some((elem, n)) => n.saturating_mul(table_scalars(elem)),
        None => 1,
    }
}

/// The range of values a type's integers can hold (`None` for non-integers).
/// For a type parameter with a numeric bound, the values of every type
/// the bound admits (see [`crate::types::ParamDef::values`]).
fn type_range(ty: Ty) -> Option<Range> {
    match ty {
        Ty::Param(_) => ty.as_param()?.values,
        _ => ty.as_int().map(|t| t.range()),
    }
}
