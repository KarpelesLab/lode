//! Semantic checking: names, types, `unsafe`, and proof obligations.
//!
//! The checker walks every package, resolves names across packages, checks
//! types, and discharges the proof obligations of docs/safety.md using the
//! flow-sensitive facts in [`facts`]. Its output is the typed tree in [`tree`].

mod expr;
pub mod facts;
pub mod tree;

use std::collections::{HashMap, HashSet};

use crate::ast::{self, ExprKind, Stmt, TypeExpr};
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
        methods: HashMap::new(),
        strings: Vec::new(),
        tables: Vec::new(),
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
        if !matches!(ret, Ty::Unit | Ty::Int(_)) {
            ck.error(span, "`main` must return nothing or an integer exit status");
        }
    }

    let program = Program {
        funcs,
        strings: ck.strings,
        tables: ck.tables,
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
    ptr_bits: u32,
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
}

/// The state a trial check of a loop body rolls back.
struct Mark {
    diags: usize,
    locals: usize,
    consts: Vec<ConstState>,
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
        | ExprKind::Paren(a)
        | ExprKind::Try(a)
        | ExprKind::Throw(a)
        | ExprKind::Ref(a) => catch_blocks(a, out),
        ExprKind::Binary(_, a, b) | ExprKind::ArrayRepeat(a, b) | ExprKind::Index(a, b) => {
            catch_blocks(a, out);
            catch_blocks(b, out);
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
        | ExprKind::Paren(a)
        | ExprKind::Try(a)
        | ExprKind::Throw(a)
        | ExprKind::Ref(a) => changed_names(a, out),
        ExprKind::Binary(_, a, b) | ExprKind::ArrayRepeat(a, b) | ExprKind::Index(a, b) => {
            changed_names(a, out);
            changed_names(b, out);
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
                Stmt::While { .. } | Stmt::Loop { .. } | Stmt::For { .. } => inner + 1,
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
    // An `inout` slice is never assigned itself, only its elements, which
    // have no facts: its length stays.
    names
        .iter()
        .filter_map(|n| cx.lookup(n))
        .filter(|&l| !cx.locals[l].mutable_view())
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
        Ty::Ptr(_) | Ty::Unit | Ty::Result(_) => Err(None),
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
        let mut owners = Vec::new();
        for (id, &(f, pkg, file)) in fns.iter().enumerate() {
            let owner = f
                .owner
                .as_ref()
                .and_then(|o| self.method_owner(o, &f.name, id, pkg, file));
            owners.push(owner);
        }
        for ((f, pkg, file), owner) in fns.into_iter().zip(owners) {
            let mut cx = FnCx::new(pkg, file, Ty::Unit, false);
            let sig = self.signature(&mut cx, f, owner);
            self.sigs.push(sig);
        }
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

    /// The signature of `f`, whose owner type is `owner` for a method or an
    /// associated function (`None` if it's in error).
    fn signature(&mut self, cx: &mut FnCx, f: &ast::FnDecl, owner: Option<Ty>) -> Sig {
        let mut params = Vec::new();
        let has_self = f.params.first().is_some_and(ast::Param::is_self);
        for p in &f.params {
            let ty = if p.is_self() {
                if p.convention == Convention::Set {
                    self.diags.push(
                        Diagnostic::error(p.name.span, "`self` can't be `set`").with_help(
                            "a method is called on a value that exists; use `inout self` to change it",
                        ),
                    );
                }
                owner.unwrap_or(Ty::Unit)
            } else {
                self.resolve_type(cx, &p.ty).unwrap_or(Ty::Unit)
            };
            self.check_convention(p, ty);
            // A `set self` is reported, and checked as `self`.
            let convention = match p.convention {
                Convention::Set if p.is_self() => Convention::Let,
                c => c,
            };
            params.push((ty, convention, p.name.name.clone()));
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
        let throws = f.throws.as_ref().and_then(|t| self.error_type(cx, t));
        let name = match &f.owner {
            Some(TypeExpr::Named(t)) => format!("{}.{}", t.name, f.name.name),
            Some(TypeExpr::Qualified(p, t)) => format!("{}.{}.{}", p.name, t.name, f.name.name),
            _ => f.name.name.clone(),
        };
        Sig {
            is_pub: f.is_pub,
            is_unsafe: f.is_unsafe,
            pkg: cx.pkg,
            name,
            params,
            has_self,
            ret,
            throws,
            span: f.name.span,
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
                    Some(ty) if table_leaf(ty).is_some() && table_scalars(ty) > TABLE_MAX => {
                        self.error(
                            t.span(),
                            format!("an array constant has at most {TABLE_MAX} elements"),
                        );
                        None
                    }
                    Some(ty) if table_leaf(ty).is_some() => {
                        let mut values = Vec::new();
                        self.table_values(&mut cx, &decl.value, ty, &mut values)
                            .map(|()| {
                                self.tables.push(Table {
                                    name: decl.name.name.clone(),
                                    ty,
                                    values,
                                });
                                ConstVal::Table(ty, self.tables.len() - 1)
                            })
                    }
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

    /// Append the scalars of `e`, the value of an array constant (or of one
    /// of its elements) of type `ty`, to `out`: from array literals,
    /// `[v; n]`, other array constants, and scalars known when compiling.
    fn table_values(
        &mut self,
        cx: &mut FnCx,
        e: &ast::Expr,
        ty: Ty,
        out: &mut Vec<i128>,
    ) -> Option<()> {
        let Some((elem, n)) = ty.as_array() else {
            let c = self.expr(cx, e, Some(ty))?;
            let c = self.coerce(c, ty, e.span)?;
            let v = match (&c.expr.kind, c.range) {
                (TExprKind::Bool(b), _) => i128::from(*b),
                (_, Some(r)) if r.lo == r.hi && ty.as_int().is_some() => r.lo,
                _ => {
                    self.error(
                        e.span,
                        "the elements of an array constant must be known when compiling",
                    );
                    return None;
                }
            };
            out.push(v);
            return Some(());
        };
        let found = |count: u64| format!("expected `{ty}`, found an array of {count} element(s)");
        match &e.kind {
            ExprKind::Paren(inner) => self.table_values(cx, inner, ty, out),
            ExprKind::ArrayLit(elems) => {
                if elems.len() as u64 != n {
                    self.error(e.span, found(elems.len() as u64));
                    return None;
                }
                let mut ok = true;
                for el in elems {
                    ok &= self.table_values(cx, el, elem, out).is_some();
                }
                ok.then_some(())
            }
            ExprKind::ArrayRepeat(value, count) => {
                let count = self.const_count(cx, count)?;
                if count != n {
                    self.error(e.span, found(count));
                    return None;
                }
                let start = out.len();
                self.table_values(cx, value, elem, out)?;
                let one: Vec<i128> = out[start..].to_vec();
                for _ in 1..n {
                    out.extend_from_slice(&one);
                }
                Some(())
            }
            _ => {
                let c = self.expr(cx, e, Some(ty))?;
                let c = self.coerce(c, ty, e.span)?;
                let TExprKind::Table(id) = c.expr.kind else {
                    self.error(
                        e.span,
                        "the value of an array constant must be an array literal or another array constant",
                    );
                    return None;
                };
                out.extend_from_slice(&self.tables[id].values);
                Some(())
            }
        }
    }

    fn function(&mut self, f: &ast::FnDecl, id: FuncId, pkg: usize, file: FileId) -> Func {
        let (ret, is_unsafe) = (self.sigs[id].ret, self.sigs[id].is_unsafe);
        let throws = self.sigs[id].throws;
        let mut cx = FnCx::new(pkg, file, ret, is_unsafe);
        cx.throws = throws;
        let mut params = Vec::new();
        let param_tys = self.sigs[id].params.clone();
        for (p, (ty, convention, _)) in f.params.iter().zip(param_tys) {
            if cx.scopes[0].contains_key(&p.name.name) {
                self.error(
                    p.name.span,
                    format!("parameter `{}` is declared twice", p.name.name),
                );
            }
            // The callee may change an `inout`, `sink` or `set` parameter;
            // an `inout` slice's elements, not the slice itself.
            let mutable = match convention {
                Convention::Let => false,
                Convention::Inout => !ty.is_view(),
                Convention::Sink | Convention::Set => true,
            };
            let local = Self::declare_local(&mut cx, &p.name.name, ty, mutable, Some(convention));
            // `self` of a type in error: uses of it fail without more errors.
            if p.is_self() && ty == Ty::Unit {
                cx.failed.insert(local);
            }
            if convention == Convention::Set && !ty.is_view() {
                cx.env.declare_uninit(local);
                cx.set_params.push(local);
            }
            params.push(local);
        }
        cx.params = params.len();
        let body = self.block(&mut cx, &f.body.stmts);
        // A failed local is only declared after its error was reported.
        debug_assert!(cx.failed.is_empty() || crate::diag::has_errors(&self.diags));
        if ret != Ty::Unit && !terminates(&body) {
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
        let name = self.sigs[id].name.clone();
        Func {
            symbol: format!("{}.{name}", self.pkgs[pkg].path),
            name,
            params,
            ret,
            throws,
            locals: cx.locals,
            body,
            span: f.span,
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

    /// The help for assigning to the immutable `local`, named `name`.
    pub(super) fn immutable_help(cx: &FnCx, local: LocalId, name: &str) -> String {
        if name == "self" && local == 0 {
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
            out.extend(checked);
        }
        cx.scopes.pop();
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
        cx.defer_depth += 1;
        let checked = self.block(cx, &body.stmts);
        cx.defer_depth -= 1;
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
                self.record_value(cx, local, &value);
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
                let checked = checked.and_then(|c| self.coerce(c, ty, value.span));
                let Some(checked) = checked else {
                    // As for a place above: the variable is still assigned.
                    cx.env.forget(local);
                    return None;
                };
                self.check_kept_view(cx, &checked, value.span)?;
                self.record_value(cx, local, &checked);
                Some(TStmt::Assign(local, checked.expr))
            }
            Stmt::Expr(e) => match &e.kind {
                ExprKind::Call(..) | ExprKind::Try(_) => {
                    Some(TStmt::Expr(self.expr(cx, e, None)?.expr))
                }
                // The value is dropped, so the block may end normally.
                ExprKind::Catch {
                    value,
                    binding,
                    handler,
                } => Some(TStmt::Expr(
                    self.whole(cx, e.span, |ck, cx| {
                        ck.catch(cx, value, binding.as_ref(), handler, false)
                    })?
                    .expr,
                )),
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
                Some(e) => TStmt::Throw(e),
                None => TStmt::Return(None),
            }),
            // Only reached for a `defer` outside a block's statements.
            Stmt::Defer { body, on_error, .. } => self.defer(cx, body, *on_error, &[]),
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
                        .and_then(|checked| self.coerce(checked, ret, v.span))
                        .map(|c| c.expr),
                };
                self.check_set_params(cx, *span);
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
                if cx.loop_depth == 0 {
                    self.error(
                        *span,
                        "`break` and `continue` can only be used inside a loop",
                    );
                    return None;
                }
                let edges = cx.loops.last_mut().expect("in a loop");
                Some(if matches!(stmt, Stmt::Break(_)) {
                    edges.exits.push(cx.env.clone());
                    TStmt::Break
                } else {
                    edges.next.push(cx.env.clone());
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
        // A call that throws gives its result, to match `ok` and `err`.
        let checked = match &value.kind {
            ExprKind::Call(callee, args) => self.whole(cx, value.span, |ck, cx| {
                ck.call(cx, callee, args, value.span, true)
            })?,
            _ => self.expr(cx, value, None)?,
        };
        // When a call fails, the variables it was to assign (`set`) aren't.
        let sets = match (&value.kind, ty_is_result(&checked)) {
            (ExprKind::Call(..), true) => std::mem::take(&mut cx.call_sets),
            _ => Vec::new(),
        };
        let ty = checked.ty();
        if let Ty::Int(_) | Ty::Bool = ty {
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
        let c = self.coerce(c, ty, e.span)?;
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
        let local = self.declare(cx, &name.name, inner, mutable);
        let value = expr::Checked::new(
            TExprKind::Payload(Box::new(matched.clone()), 1, 0),
            inner,
            None,
        );
        self.record_value(cx, local, &value);
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
    fn loop_body<T>(
        &mut self,
        cx: &mut FnCx,
        body: &[Stmt],
        index: Option<&ForIndex>,
        mut check: impl FnMut(&mut Self, &mut FnCx) -> (T, bool),
    ) -> (T, Env, Vec<Env>) {
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
            let (out, edges) = self.loop_pass(cx, base.clone(), index, &mut check);
            return (out, base, edges.exits);
        }

        // 1. E
        let (out, edges) = self.loop_pass(cx, entry.clone(), index, &mut check);
        if holds(&entry, &edges) {
            return (out, entry, edges.exits);
        }
        // 2. C
        self.rollback(cx, &mark);
        let c = entry.loosen(about, full, &edges.next, Cover);
        let (out, edges) = self.loop_pass(cx, c.clone(), index, &mut check);
        if holds(&c, &edges) {
            return (out, c, edges.exits);
        }
        // 3. W
        self.rollback(cx, &mark);
        let w = c.loosen(about, full, &edges.next, Drop);
        let (out, edges) = self.loop_pass(cx, w.clone(), index, &mut check);
        if !holds(&w, &edges) {
            self.rollback(cx, &mark);
            let base = forget_all(entry);
            let (out, edges) = self.loop_pass(cx, base.clone(), index, &mut check);
            return (out, base, edges.exits);
        }
        // 4. T, from N
        let n = entry.loosen(about, full, &edges.next, Cover);
        let t = n.to_thresholds(&entry, about, full, &edges.thresholds);
        let mut w_checked = Some((out, edges));
        if !t.same(&n) {
            self.rollback(cx, &mark);
            w_checked = None;
            let (out, edges) = self.loop_pass(cx, t.clone(), index, &mut check);
            if holds(&t, &edges) {
                return (out, t, edges.exits);
            }
        }
        // 5. N
        if !n.same(&w) {
            self.rollback(cx, &mark);
            let (out, edges) = self.loop_pass(cx, n.clone(), index, &mut check);
            if holds(&n, &edges) {
                return (out, n, edges.exits);
            }
            w_checked = None;
        }
        let (out, edges) = match w_checked {
            Some(checked) => checked,
            None => {
                self.rollback(cx, &mark);
                self.loop_pass(cx, w.clone(), index, &mut check)
            }
        };
        (out, w, edges.exits)
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
        cx.loops.push(LoopEdges::default());
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
        }
    }

    fn rollback(&mut self, cx: &mut FnCx, mark: &Mark) {
        self.diags.truncate(mark.diags);
        cx.locals.truncate(mark.locals);
        cx.failed.retain(|&l| l < mark.locals);
        for (c, &state) in self.consts.iter_mut().zip(&mark.consts) {
            c.state = state;
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
                // The sequence the body reads elements of: the local itself,
                // an array constant itself (read in place, with the facts
                // about its elements), or else a hidden copy.
                let (seq_ast, seq_t) = match (&xs.kind, &seq.expr.kind) {
                    (ExprKind::Name(name), TExprKind::Local(_)) if !assigned.contains(name) => {
                        (xs.clone(), seq.expr)
                    }
                    (_, TExprKind::Table(_)) => (xs.clone(), seq.expr),
                    _ => {
                        let hidden = self.declare(cx, SEQ, seq.ty(), false);
                        self.record_value(cx, hidden, &seq);
                        let ty = seq.ty();
                        before.push(TStmt::Init(hidden, seq.expr));
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
                    Some(n) => {
                        let n = i128::from(n);
                        expr::Checked::new(TExprKind::Int(n), usize_ty, Some(Range::exact(n)))
                    }
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
            local.mutable_view() || !assigned.contains(&local.name)
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
                if let Some(value) = value {
                    ck.record_value(cx, x, &value);
                    stmts.push(TStmt::Init(x, value.expr));
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

    /// A slice stored in a local must not see its array change: the array
    /// can't be changed while a view of it is in use (docs/memory.md, Views),
    /// and until the compiler checks that, a slice local may only view a
    /// `let` array (or part of one), or part of another view. A slice of a
    /// `var` array or of a temporary can still be passed to a function.
    fn check_kept_view(&mut self, cx: &FnCx, value: &expr::Checked, span: Span) -> Option<()> {
        // A copy of an `inout` slice would see its elements change.
        if let TExprKind::Local(l) = value.expr.kind
            && cx.locals[l].mutable_view()
        {
            let name = &cx.locals[l].name;
            self.diags.push(
                Diagnostic::error(
                    span,
                    format!("cannot keep a copy of `{name}`, an `inout` slice"),
                )
                .with_help(format!(
                    "its elements can change; use `{name}` itself, or pass it to the function that takes the slice"
                )),
            );
            return None;
        }
        let TExprKind::ToSlice(array) = &value.expr.kind else {
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

/// The scalar type at the bottom of an array type that can be a constant
/// (`u8` for `[12]u8` and `[2][3]u8`): an integer or `bool`.
pub fn table_leaf(ty: Ty) -> Option<Ty> {
    let (mut elem, _) = ty.as_array()?;
    while let Some((inner, _)) = elem.as_array() {
        elem = inner;
    }
    matches!(elem, Ty::Int(_) | Ty::Bool).then_some(elem)
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
    match ty.as_array() {
        Some((elem, n)) => n.saturating_mul(table_scalars(elem)),
        None => 1,
    }
}

/// The range of values a type's integers can hold (`None` for non-integers).
fn type_range(ty: Ty) -> Option<Range> {
    ty.as_int().map(|t| t.range())
}
