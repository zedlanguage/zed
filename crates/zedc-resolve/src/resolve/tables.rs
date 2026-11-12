//! The binders of a unit and their uses (`Tables`), which the checker and elaboration share,
//! and the dependency order of its statements.

use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

use imbl::Vector;

use crate::resolve::{Ref, Resolution};
use zedc_base::rejection::Row;
use zedc_syntax::ast::{
    Expr, ExprKind, Function, Note, Param, Stmt, StmtKind, StrPart, Target, Type,
};
use zedc_syntax::lex::Span;

use super::pick::{Call, Pick, picks};
use super::topo::{topo_around_cycles, topo_joined};

/// The binders of a unit, shared by the checker and elaboration.
pub struct Tables<'a> {
    /// The unit's resolution, which the tables index.
    pub res: &'a Resolution,
    /// Each binder's index, by its span and name.
    pub ids: HashMap<(Span, &'a str), usize>,
    /// Each function binder's declaration.
    pub funcs: HashMap<usize, &'a Function>,
    /// The uses of the unit's binders, grouped by the list of binders each may name (one
    /// binder, or the arrows of an overload set), each use once, in the order of the text: `U`
    /// uses of a set of `K` arrows are `U + K` entries, not `U·K`.
    uses: Vec<Uses>,
    /// The groups of `uses` naming each binder.
    groups_of: Vec<Vec<usize>>,
    /// Every written type of the unit, each once, in the order of the text: a parameter's, a
    /// lambda parameter's, an output port's and an `is` test's. The checker checks their
    /// bounds.
    pub written: Vec<&'a Type>,
    /// The unit's text, when it is known, which a message quotes: the line a fix rewrites
    /// (DESIGN.md sec:diagnostics).
    pub text: Option<&'a str>,
    /// The binders of each name, in the order of the binders.
    by_name: HashMap<&'a str, Vec<usize>>,
    /// What each call of an overload set waits on, by the use of the set ([`super::pick`]). A
    /// use of a set that is not here, the set passed as a value, waits on every overload.
    picks: HashMap<Span, Pick>,
}

/// The uses of one list of binders.
struct Uses {
    binders: Vector<usize>,
    at: Vec<Span>,
}

/// A list of binders as a key: hashed by its first binder and length, compared by sharing
/// first and by content only when not shared. Each use of an overload set shares the set's
/// list (`Ref::Bound`), so finding a use's group costs `O(1)`.
// Complexity tradeoff (COMPLEXITY.md F49, F16): the naive tables record each use once per
// binder it may name, and each statement using an overload set waits on every overload,
// O(U·K) entries and edges for U uses of K overloads (7.3 s at U = K = 8,000). Grouping the
// uses by their shared list makes U + K entries and edges. The key hashes the first binder
// and the length only, O(1) per use; two different lists that agree on both collide and
// are compared by content, O(K) per such comparison, which only lists not shared reach.
struct ListKey<'a>(&'a Vector<usize>);

impl Hash for ListKey<'_> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        (self.0.front(), self.0.len()).hash(h)
    }
}

impl PartialEq for ListKey<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.0.ptr_eq(other.0) || self.0 == other.0
    }
}

impl Eq for ListKey<'_> {}

/// A part of the unit still to visit while [`Tables`] collects the declarations and written
/// types.
enum Collect<'a> {
    Stmt(&'a Stmt),
    Expr(&'a Expr),
    Type(&'a Type),
}

/// Puts each parameter's written type and default on `todo`, in the order of the text.
fn collect_params<'a>(params: &'a [Param], todo: &mut Vec<Collect<'a>>) {
    for p in params {
        todo.extend(p.ty.as_ref().map(Collect::Type));
        todo.extend(p.default.as_ref().map(Collect::Expr));
    }
}

/// Puts the parts `e` holds on `todo`, in the order of the text.
fn collect_expr<'a>(e: &'a Expr, todo: &mut Vec<Collect<'a>>) {
    let expr = |e: &'a Expr| Collect::Expr(e);
    match &e.kind {
        ExprKind::Block(stmts) => todo.extend(stmts.iter().map(Collect::Stmt)),
        ExprKind::Str(parts) => todo.extend(parts.iter().filter_map(|p| match p {
            StrPart::Hole(h) => Some(expr(h)),
            _ => None,
        })),
        ExprKind::Unary(_, a) | ExprKind::Member { of: a, .. } => todo.push(expr(a)),
        ExprKind::Is { of, ty, .. } => todo.extend([expr(of), Collect::Type(ty)]),
        ExprKind::Binary(_, a, b)
        | ExprKind::Index(a, b)
        | ExprKind::Else {
            of: a, default: b, ..
        } => todo.extend([expr(a), expr(b)]),
        ExprKind::Call {
            callee,
            positional,
            named,
            ..
        } => {
            todo.push(expr(callee));
            todo.extend(positional.iter().map(expr));
            todo.extend(named.iter().map(|(_, a)| expr(a)));
        }
        ExprKind::Tuple(items) => todo.extend(items.iter().map(expr)),
        ExprKind::Lambda { params, body } => {
            collect_params(params, todo);
            todo.push(expr(body));
        }
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => todo.extend([expr(cond), expr(then), expr(otherwise)]),
        _ => {}
    }
}

impl<'a> Tables<'a> {
    /// The tables of the unit `unit`, whose resolution is `res`.
    pub fn new(unit: &'a [Stmt], res: &'a Resolution) -> Self {
        Tables::with_text(unit, res, None)
    }

    /// [`Tables::new`], with the unit's text when it is known, which a message quotes.
    pub fn with_text(unit: &'a [Stmt], res: &'a Resolution, text: Option<&'a str>) -> Self {
        let ids = res
            .binders
            .iter()
            .enumerate()
            .map(|(i, b)| ((b.span, b.name.as_str()), i))
            .collect();
        let mut by_name: HashMap<&str, Vec<usize>> = HashMap::new();
        for (i, b) in res.binders.iter().enumerate() {
            by_name.entry(b.name.as_str()).or_default().push(i);
        }
        let mut uses: Vec<Uses> = Vec::new();
        let mut groups_of = vec![Vec::new(); res.binders.len()];
        let mut group: HashMap<ListKey, usize> = HashMap::new();
        for (u, r) in &res.uses {
            let Ref::Bound(ids) = r else { continue };
            let g = *group.entry(ListKey(ids)).or_insert_with(|| {
                for &b in ids {
                    groups_of[b].push(uses.len());
                }
                uses.push(Uses {
                    binders: ids.clone(),
                    at: Vec::new(),
                });
                uses.len() - 1
            });
            uses[g].at.push(*u);
        }
        let mut t = Tables {
            res,
            ids,
            funcs: HashMap::new(),
            uses,
            groups_of,
            written: Vec::new(),
            text,
            by_name,
            picks: HashMap::new(),
        };
        let (calls, param_ty) = t.collect_functions(unit);
        t.picks = picks(&calls, res, &t.funcs, &param_ty);
        t
    }

    /// Records every function declaration and written type of `stmts` and of the blocks
    /// inside them. The walk keeps the parts still to visit on a heap stack, so a deeply nested
    /// expression does not grow the thread's stack. Each part's children go on the stack in
    /// reverse, so the parts are met in the order of the text, the order of `written`.
    /// Returns the calls of overload sets and the written type of each parameter, by the
    /// parameter's text, which [`picks`] reads.
    #[allow(clippy::type_complexity)]
    fn collect_functions(&mut self, stmts: &'a [Stmt]) -> (Vec<Call<'a>>, HashMap<Span, &'a Type>) {
        let mut calls: Vec<Call<'a>> = Vec::new();
        let mut called: HashSet<Span> = HashSet::new();
        let mut param_ty: HashMap<Span, &'a Type> = HashMap::new();
        let mut params = |ps: &'a [Param]| {
            for p in ps {
                if let Some(t) = &p.ty {
                    param_ty.insert(p.span, t);
                }
            }
        };
        let res = self.res;
        let set = |at: Span| matches!(res.uses.get(&at), Some(Ref::Bound(ids)) if ids.len() > 1);
        let mut todo: Vec<Collect<'a>> = stmts.iter().rev().map(Collect::Stmt).collect();
        while let Some(c) = todo.pop() {
            let at = todo.len();
            match c {
                Collect::Type(t) => self.written.push(t),
                Collect::Stmt(s) => {
                    if let StmtKind::Function(f) = &s.kind {
                        params(&f.params);
                    }
                    self.collect_stmt(s, &mut todo)
                }
                Collect::Expr(e) => {
                    match &e.kind {
                        // `f(args)` and `x.f(args)`, the uniform call `f(x, args)`. A curried
                        // call `f(a, ...)` is a function value, which waits on every overload.
                        ExprKind::Call {
                            callee,
                            positional,
                            named,
                            curry: false,
                        } if set(callee.span) => {
                            let receiver = match &callee.kind {
                                ExprKind::Member { of, .. } => Some(&**of),
                                _ => None,
                            };
                            called.insert(callee.span);
                            calls.push(Call {
                                use_at: callee.span,
                                receiver,
                                positional,
                                named,
                            });
                        }
                        // `x.f` without parentheses, the call `f(x)`; the callee of a call is
                        // met after the call.
                        ExprKind::Member { of, .. } if set(e.span) && !called.contains(&e.span) => {
                            calls.push(Call {
                                use_at: e.span,
                                receiver: Some(of),
                                positional: &[],
                                named: &[],
                            })
                        }
                        ExprKind::Lambda { params: ps, .. } => params(ps),
                        _ => {}
                    }
                    collect_expr(e, &mut todo)
                }
            }
            todo[at..].reverse();
        }
        (calls, param_ty)
    }

    /// Records the function declaration `s` if it is one and puts the parts it holds on
    /// `todo`, in the order of the text.
    fn collect_stmt(&mut self, s: &'a Stmt, todo: &mut Vec<Collect<'a>>) {
        match &s.kind {
            StmtKind::Function(f) => {
                if let Some(&id) = self.ids.get(&(s.span, f.name.as_str())) {
                    self.funcs.insert(id, f);
                }
                collect_params(&f.params, todo);
                todo.extend(
                    f.ports()
                        .into_iter()
                        .flatten()
                        .map(|p| Collect::Type(&p.ty)),
                );
                todo.push(Collect::Expr(&f.body));
                for (a, b) in &f.tests {
                    todo.extend([Collect::Expr(a), Collect::Expr(b)]);
                }
            }
            StmtKind::Bind { value, .. } | StmtKind::Push { value, .. } => {
                todo.push(Collect::Expr(value))
            }
            StmtKind::Return(es) => todo.extend(es.iter().map(Collect::Expr)),
            StmtKind::Struct(_)
            | StmtKind::Type(_)
            | StmtKind::Method(_)
            | StmtKind::Import(_)
            | StmtKind::Local(_)
            | StmtKind::Annotated { .. }
            | StmtKind::Mutable(_)
            | StmtKind::IndexedDef(_)
            | StmtKind::Initial(_)
            | StmtKind::While(_)
            | StmtKind::Until(_)
            | StmtKind::Expr(_)
            | StmtKind::UnitAnnot(_) => {}
        }
    }

    /// The index of the binder named `name` declared at `span`.
    pub fn id(&self, span: Span, name: &str) -> usize {
        self.ids[&(span, name)]
    }

    /// The binders used in `span`, outside the spans in `skip`.
    pub fn uses_in(&self, span: Span, skip: &[Span]) -> Vec<usize> {
        let from = Span {
            start: span.start,
            end: 0,
        };
        let to = Span {
            start: span.end,
            end: 0,
        };
        self.res
            .uses
            .range(from..to)
            .filter(|(u, _)| u.end <= span.end)
            .filter(|(u, _)| !skip.iter().any(|s| s.start <= u.start && u.end <= s.end))
            .filter_map(|(_, r)| match r {
                Ref::Bound(ids) => Some(ids),
                Ref::Prelude(_) | Ref::Unit { .. } => None,
            })
            .flatten()
            .copied()
            .collect()
    }

    fn binders_of(&self, s: &'a Stmt) -> Vec<usize> {
        match &s.kind {
            StmtKind::Bind { targets, .. } => targets
                .iter()
                .filter_map(|t| match t {
                    Target::Name(n, _) => Some(self.id(s.span, n)),
                    Target::Wild => None,
                })
                .collect(),
            StmtKind::Function(f) => vec![self.id(s.span, &f.name)],
            StmtKind::Push { .. } | StmtKind::Return(_) | StmtKind::UnitAnnot(_) => Vec::new(),
            StmtKind::Struct(_)
            | StmtKind::Type(_)
            | StmtKind::Method(_)
            | StmtKind::Import(_)
            | StmtKind::Local(_)
            | StmtKind::Annotated { .. } => {
                unreachable!("resolve rejects the forms of layer L2")
            }
            StmtKind::Mutable(_)
            | StmtKind::IndexedDef(_)
            | StmtKind::Initial(_)
            | StmtKind::While(_)
            | StmtKind::Until(_)
            | StmtKind::Expr(_) => unreachable!("resolve rejects the forms of layer L6"),
        }
    }

    /// The order the statements of one scope are bound in, each after those it uses, a
    /// function's `test` tables aside; else the statements of each cycle. Each use of a
    /// binder of the scope is placed in its statement by a binary search, so the order
    /// reads the uses of the scope's own binders only, not those of the scopes inside it.
    /// A call of an overload set waits on the one overload its arguments select, or on none
    /// when type checking must choose ([`super::pick`]); any other use of a set waits on one
    /// join node, which waits on the set's statements, so `U` uses of `K` overloads make
    /// `U + K` dependencies, not `U·K`.
    // Complexity tradeoff (COMPLEXITY.md F7, F49): the naive order collects each scope's
    // uses with `uses_in`, which reads the uses of every scope nested inside, O(uses · depth)
    // over a nest; here a scope reads only the groups of its own binders and places each use
    // in its statement by binary search, O(uses log n) in all, with a hash map from binder
    // to statement per scope.
    pub fn order(&self, items: &[&'a Stmt]) -> Result<Vec<usize>, Vec<Vec<usize>>> {
        topo_joined(&self.deps(items), items.len())
    }

    /// The order of [`Tables::order`] around the cycles: the statements outside a cycle, each
    /// after those outside a cycle it uses, and the statements of each cycle
    /// ([`topo_around_cycles`]). The checker checks every statement that is not in a cycle,
    /// those that use one among them, so that no definition goes unchecked.
    pub fn order_around_cycles(&self, items: &[&'a Stmt]) -> (Vec<usize>, Vec<Vec<usize>>) {
        topo_around_cycles(&self.deps(items), items.len())
    }

    /// The dependency graph of [`Tables::order`]: for each statement, then for each join of
    /// an overload set, the nodes it waits on.
    fn deps(&self, items: &[&'a Stmt]) -> Vec<Vec<usize>> {
        let bound: Vec<(usize, usize)> = (items.iter().enumerate())
            .flat_map(|(i, s)| self.binders_of(s).into_iter().map(move |b| (b, i)))
            .collect();
        let item_of: HashMap<usize, usize> = bound.iter().copied().collect();
        let mut deps: Vec<Vec<usize>> = vec![Vec::new(); items.len()];
        let mut seen: HashSet<usize> = HashSet::new();
        for &(b, _) in &bound {
            for &g in &self.groups_of[b] {
                if !seen.insert(g) {
                    continue;
                }
                let group = &self.uses[g];
                // The join of the set, made at its first use that waits on every overload.
                let mut join: Option<usize> = None;
                for u in &group.at {
                    let k = items.partition_point(|s| s.span.start <= u.start);
                    let Some(user) = k.checked_sub(1) else {
                        continue;
                    };
                    let at = items[user];
                    if u.end > at.span.end || in_tests(at, *u) {
                        continue;
                    }
                    let on = match self.picks.get(u) {
                        Some(Pick::Arm(b)) => match item_of.get(b) {
                            Some(&i) => i,
                            None => continue,
                        },
                        Some(Pick::Undecided) => continue,
                        None => *join.get_or_insert_with(|| {
                            let mut named: Vec<usize> = (group.binders.iter())
                                .filter_map(|b| item_of.get(b).copied())
                                .collect();
                            named.sort_unstable();
                            named.dedup();
                            match named[..] {
                                [one] => one,
                                _ => {
                                    deps.push(named);
                                    deps.len() - 1
                                }
                            }
                        }),
                    };
                    deps[user].push(on);
                }
            }
        }
        for d in &mut deps {
            d.sort_unstable();
            d.dedup();
        }
        deps
    }
}

/// Whether `u` lies in one of the `test` tables of the function `s` declares.
fn in_tests(s: &Stmt, u: Span) -> bool {
    let StmtKind::Function(f) = &s.kind else {
        return false;
    };
    let k = f.tests.partition_point(|(a, _)| a.span.start <= u.start);
    k.checked_sub(1)
        .is_some_and(|k| u.end <= f.tests[k].1.span.end)
}

/// Whether `u` lies in one of the sorted, disjoint spans `spans`.
fn inside(spans: &[Span], u: Span) -> bool {
    let k = spans.partition_point(|s| s.start <= u.start);
    k.checked_sub(1).is_some_and(|k| u.end <= spans[k].end)
}

/// The spans of the value `e` whose uses do not read a value when `e` is computed: each
/// lambda and each function declared in a block, outermost ones only, so the spans are
/// disjoint; sorted.
fn deferred_spans(e: &Expr) -> Vec<Span> {
    let mut out = Vec::new();
    let mut todo = vec![Collect::Expr(e)];
    while let Some(c) = todo.pop() {
        match c {
            Collect::Expr(e) if matches!(e.kind, ExprKind::Lambda { .. }) => out.push(e.span),
            Collect::Expr(e) => collect_expr(e, &mut todo),
            Collect::Stmt(s) => match &s.kind {
                StmtKind::Function(_) => out.push(s.span),
                StmtKind::Bind { value, .. } | StmtKind::Push { value, .. } => {
                    todo.push(Collect::Expr(value))
                }
                StmtKind::Return(es) => todo.extend(es.iter().map(Collect::Expr)),
                _ => {}
            },
            Collect::Type(_) => {}
        }
    }
    out.sort_unstable();
    out
}

/// The rejection of one cycle among the statements of a scope ([`Tables::cycle_reports`]).
#[derive(Debug)]
pub struct CycleReport {
    /// Where it is reported: the statement of the cycle that comes first by name.
    pub span: Span,
    /// The row of the rejection table it is a case of, if any.
    pub row: Option<Row>,
    /// The message.
    pub message: String,
    /// Each use that closes the cycle, in the order of the cycle, then the repairs.
    pub notes: Vec<Note>,
}

/// The uses by one statement of a cycle of one list of binders that names statements of the
/// same cycle.
struct Edge<'n> {
    /// The first of the uses.
    first: Span,
    /// The first of the uses outside the lambdas and the functions of the statement's value,
    /// which reads the value as the statement is computed, if any.
    read: Option<Span>,
    /// The statements of the cycle the list names, as an index into the lists of
    /// [`Tables::cycle_reports`].
    list: usize,
    /// The name it uses.
    name: &'n str,
}

impl<'a> Tables<'a> {
    /// The rejection of each cycle `cycles` among the statements `items` of one scope, as
    /// [`Tables::order`] gives them. A cycle of values each read as the next is computed is
    /// the row "A definition that reads its own value"; any other cycle is a recursion, which
    /// zedc compiles from layer L6 on. The message shows each use that closes the cycle, at
    /// its site, in the order of the cycle, then the repairs (DESIGN.md sec:diagnostics). The
    /// cycle starts at its statement that comes first by name, the declarations of one name in
    /// written order, and each statement's uses are taken in the order of the text, so nothing
    /// depends on where the statements stand in the unit (DESIGN.md L1.29b). The checker and
    /// elaboration both report each cycle, in the same words, so that a unit reports it once.
    // Complexity tradeoff: the naive search names each use of a cycle's statements once per
    // statement its list of binders names, O(U·K) for U uses of a set of K overloads, and
    // finds the order of the cycle by a search from each statement, O(n·(n + e)) for a cycle
    // of n statements and e uses. Here each use is placed in its statement by binary search
    // and kept once per (statement, list), the lists grouped by cycle once per list, O(U log n
    // + K) in all; one search with a visited set over statements and lists, which takes each
    // statement's uses in the order of the text, gives the order, O((n + e) log e).
    pub fn cycle_reports(&self, items: &[&'a Stmt], cycles: &[Vec<usize>]) -> Vec<CycleReport> {
        let mut cycle_of: HashMap<usize, usize> = HashMap::new();
        let mut item_of: HashMap<usize, usize> = HashMap::new();
        let mut member_binders: Vec<usize> = Vec::new();
        for (c, cycle) in cycles.iter().enumerate() {
            for &i in cycle {
                cycle_of.insert(i, c);
                for b in self.binders_of(items[i]) {
                    item_of.insert(b, i);
                    member_binders.push(b);
                }
            }
        }
        let deferred: HashMap<usize, Vec<Span>> = (cycle_of.keys())
            .filter_map(|&i| match &items[i].kind {
                StmtKind::Bind { value, .. } => Some((i, deferred_spans(value))),
                _ => None,
            })
            .collect();
        let mut lists: Vec<Vec<usize>> = Vec::new();
        // The list of each statement that a call picks alone.
        let mut single: HashMap<usize, usize> = HashMap::new();
        let mut edges: HashMap<usize, Vec<Edge>> = HashMap::new();
        let mut seen: HashSet<usize> = HashSet::new();
        for &b in &member_binders {
            for &g in &self.groups_of[b] {
                if !seen.insert(g) {
                    continue;
                }
                let group = &self.uses[g];
                // The statements of each cycle the list names.
                let mut named: HashMap<usize, usize> = HashMap::new();
                for b in &group.binders {
                    let Some(&i) = item_of.get(b) else { continue };
                    let l = *named.entry(cycle_of[&i]).or_insert_with(|| {
                        lists.push(Vec::new());
                        lists.len() - 1
                    });
                    lists[l].push(i);
                }
                for &l in named.values() {
                    lists[l].sort_unstable();
                    lists[l].dedup();
                }
                let name = self.res.binders[group.binders[0]].name.as_str();
                // Each statement's edge for each list, by statement and list.
                let mut edge_at: HashMap<(usize, usize), usize> = HashMap::new();
                for u in &group.at {
                    let k = items.partition_point(|s| s.span.start <= u.start);
                    let Some(user) = k.checked_sub(1) else {
                        continue;
                    };
                    let at = items[user];
                    if u.end > at.span.end || in_tests(at, *u) {
                        continue;
                    }
                    let Some(&c) = cycle_of.get(&user) else {
                        continue;
                    };
                    // The statements the use waits on, as `deps` gives them: the overload a
                    // call picks, none, or every overload.
                    let list = match self.picks.get(u) {
                        Some(Pick::Arm(b)) => match item_of.get(b) {
                            Some(&i) if cycle_of[&i] == c => {
                                *single.entry(i).or_insert_with(|| {
                                    lists.push(vec![i]);
                                    lists.len() - 1
                                })
                            }
                            _ => continue,
                        },
                        Some(Pick::Undecided) => continue,
                        None => match named.get(&c) {
                            Some(&l) => l,
                            None => continue,
                        },
                    };
                    let es = edges.entry(user).or_default();
                    let k = *edge_at.entry((user, list)).or_insert_with(|| {
                        es.push(Edge {
                            first: *u,
                            read: None,
                            list,
                            name,
                        });
                        es.len() - 1
                    });
                    let e = &mut es[k];
                    if e.read.is_none() && !deferred.get(&user).is_some_and(|d| inside(d, *u)) {
                        e.read = Some(*u);
                    }
                }
            }
        }
        (cycles.iter())
            .map(|cycle| self.cycle_report(items, cycle, &mut edges, &lists, &item_of))
            .collect()
    }

    /// The rejection of the cycle `cycle`, whose statements' uses `edges` holds
    /// ([`Tables::cycle_reports`]).
    fn cycle_report(
        &self,
        items: &[&'a Stmt],
        cycle: &[usize],
        edges: &mut HashMap<usize, Vec<Edge>>,
        lists: &[Vec<usize>],
        item_of: &HashMap<usize, usize>,
    ) -> CycleReport {
        let mut own: HashMap<usize, Vec<Edge>> = (cycle.iter())
            .map(|i| (*i, edges.remove(i).unwrap_or_default()))
            .collect();
        let value = cycle.iter().all(|&i| {
            matches!(items[i].kind, StmtKind::Bind { .. })
                && own[&i].iter().all(|e| e.read.is_some())
        });
        let shown = |e: &Edge| {
            if value {
                e.read.unwrap_or(e.first)
            } else {
                e.first
            }
        };
        for es in own.values_mut() {
            es.sort_unstable_by_key(|e| shown(e));
        }
        let start = (cycle.iter())
            .map(|&i| (what(items[i]), i))
            .min()
            .expect("a cycle has a statement")
            .1;
        // The cycle's order: a search from `start` that takes each statement's uses in the
        // order of the text, each statement and each list once.
        let mut order: Vec<usize> = Vec::with_capacity(cycle.len());
        let mut visited: HashSet<usize> = HashSet::new();
        let mut expanded: HashSet<usize> = HashSet::new();
        let mut todo = vec![start];
        while let Some(i) = todo.pop() {
            if !visited.insert(i) {
                continue;
            }
            order.push(i);
            for e in own[&i].iter().rev() {
                if expanded.insert(e.list) {
                    todo.extend(lists[e.list].iter().rev());
                }
            }
        }
        debug_assert_eq!(
            order.len(),
            cycle.len(),
            "a cycle reaches each of its statements"
        );

        let mut notes = Vec::new();
        let mut uses = 0;
        for &i in &order {
            let who = self.shown(items[i]);
            let several = names_bound(items[i]) > 1;
            let verb = match (value, several) {
                (true, false) => "reads",
                (true, true) => "read",
                (false, false) => "uses",
                (false, true) => "use",
            };
            for e in &own[&i] {
                uses += 1;
                let whom = if lists[e.list] == [i] && !several {
                    "itself".to_string()
                } else if let [j] = lists[e.list][..]
                    && let Some(h) = self.header(items[j])
                {
                    h
                } else {
                    format!("`{}`", e.name)
                };
                notes.push(Note {
                    span: shown(e),
                    text: format!("{who} {verb} {whom} here"),
                });
            }
        }
        let first = self.shown(items[start]);
        let several = names_bound(items[start]) > 1;
        let names: Vec<String> = order.iter().map(|&i| self.shown(items[i])).collect();
        let at = items[start].span;
        if value {
            let head = match (&names[..], several) {
                ([_], false) => format!("{first} is defined in terms of its own value"),
                ([_], true) => format!("{first} are defined in terms of their own values"),
                _ => format!(
                    "{} are defined in terms of each other's values",
                    names.join(", ")
                ),
            };
            notes.push(Note {
                span: at,
                text: self.step_repair(items[start], cycle.len() == 1),
            });
            // A value read where another binder of the same name was meant.
            let mut renamed: HashSet<&str> = HashSet::new();
            for &i in &order {
                for b in self.binders_of(items[i]) {
                    let name = self.res.binders[b].name.as_str();
                    if !renamed.insert(name) {
                        continue;
                    }
                    let other = (self.by_name.get(name).into_iter().flatten())
                        .find(|o| !item_of.contains_key(o));
                    if let Some(&o) = other {
                        notes.push(Note {
                            span: self.res.binders[o].span,
                            text: format!(
                                "repair: to read the `{name}` defined here, give the `{name}` \
                                 that reads its own value another name"
                            ),
                        });
                    }
                }
            }
            let each = if several { "each of " } else { "" };
            notes.push(Note {
                span: at,
                text: format!(
                    "repair: to define a recursive function, write {each}{first} as a function \
                     with a parameter. Recursion is part of the Zed language, and this version of \
                     zedc does not compile it yet."
                ),
            });
            CycleReport {
                span: at,
                row: Some(Row::ReadsOwnValue),
                message: format!(
                    "{head}. A value cannot be defined in terms of itself, since no step of the \
                     program makes the earlier value."
                ),
                notes,
            }
        } else {
            let head = match (&names[..], several) {
                ([_], false) => format!("{first} is defined in terms of itself"),
                ([_], true) => format!("{first} are defined in terms of themselves"),
                _ => format!("{} are defined in terms of each other", names.join(", ")),
            };
            let text = if uses == 1 {
                "repair: remove the use shown, which ends the cycle"
            } else if uses == cycle.len() {
                "repair: remove one of the uses shown, which ends the cycle"
            } else {
                "repair: remove uses shown until no definition uses itself, directly or through \
                 the others"
            };
            notes.push(Note {
                span: at,
                text: text.into(),
            });
            CycleReport {
                span: at,
                row: None,
                message: format!(
                    "{head}, which is recursion. Recursion is part of the Zed language, and this \
                     version of zedc does not compile it yet. Write the program without it, with \
                     the forms this zedc compiles."
                ),
                notes,
            }
        }
    }

    /// How a message names the statement `s` of a cycle: [`Tables::header`] for an overload,
    /// else [`what`].
    fn shown(&self, s: &Stmt) -> String {
        self.header(s).unwrap_or_else(|| what(s))
    }

    /// The written head of the function `s` declares, with its parameters and their types, as
    /// `` `f(positional n: int)` ``, when another binder shares its name and the text is known:
    /// the name alone does not tell the overloads of a set apart.
    fn header(&self, s: &Stmt) -> Option<String> {
        let StmtKind::Function(f) = &s.kind else {
            return None;
        };
        let text = self.text?;
        if self
            .by_name
            .get(f.name.as_str())
            .is_none_or(|b| b.len() < 2)
        {
            return None;
        }
        let head = text.get(s.span.start..f.body.span.start)?;
        let head: Vec<&str> = head
            .trim_end()
            .trim_end_matches('=')
            .split_whitespace()
            .collect();
        Some(format!("`{}`", head.join(" ")))
    }

    /// The repair of a value that reads its own value: step it from its earlier value, in a
    /// `loop` or an indexed definition. When `s` alone binds one name and the text is known,
    /// both are written with the statement's own value, `x' = e` and `e` with each read of `x`
    /// made `x[i-1]`; otherwise with the example of DESIGN.md sec:diagnostics and the name.
    fn step_repair(&self, s: &Stmt, alone: bool) -> String {
        let StmtKind::Bind { targets, value } = &s.kind else {
            unreachable!("a value's statement")
        };
        let mut names = targets.iter().filter_map(|t| match t {
            Target::Name(n, _) => Some(n.as_str()),
            Target::Wild => None,
        });
        let x = names.next().expect("a value has a name");
        let own = (self.text)
            .filter(|_| alone && names.next().is_none())
            .map(|text| {
                let b = self.id(s.span, x);
                let mut indexed = String::new();
                let mut from = value.span.start;
                let from_start = Span {
                    start: value.span.start,
                    end: 0,
                };
                for (u, r) in self.res.uses.range(from_start..) {
                    if u.start >= value.span.end {
                        break;
                    }
                    if matches!(r, Ref::Bound(ids) if ids.contains(&b)) {
                        indexed.push_str(&text[from..u.start]);
                        indexed.push_str(&format!("{x}[i-1]"));
                        from = u.end;
                    }
                }
                indexed.push_str(&text[from..value.span.end]);
                (text[value.span.start..value.span.end].to_string(), indexed)
            });
        let (next, indexed) = own.unwrap_or_else(|| (format!("{x} + 1"), format!("{x}[i-1] + 1")));
        format!(
            "repair: to step `{x}` from its earlier value, write a `loop` with a start value, as \
             `loop t {{ while t < 10; initial {x} = 0; {x}' = {next}; }}`, or an indexed \
             definition, as `{x}[i in 0..<10] = {indexed} with {x}[-1] = 0`, with the start value \
             in place of 0 and the number of steps in place of 10. Loops and indexed definitions \
             are part of the Zed language, and this version of zedc does not compile them yet."
        )
    }
}

/// The number of names the statement `s` binds.
fn names_bound(s: &Stmt) -> usize {
    match &s.kind {
        StmtKind::Bind { targets, .. } => targets
            .iter()
            .filter(|t| matches!(t, Target::Name(..)))
            .count(),
        _ => 1,
    }
}

/// How a message names the statement `s` of a cycle: by the names it binds. Only a statement
/// that binds a name is in a cycle, since only such a statement is waited on (`deps`).
fn what(s: &Stmt) -> String {
    match &s.kind {
        StmtKind::Bind { targets, .. } => {
            let names: Vec<String> = targets
                .iter()
                .filter_map(|t| match t {
                    Target::Name(n, _) => Some(format!("`{n}`")),
                    Target::Wild => None,
                })
                .collect();
            names.join(" and ")
        }
        StmtKind::Function(f) => format!("`{}`", f.name),
        StmtKind::Push { .. } | StmtKind::Return(_) => {
            unreachable!("a push or an export binds no name, so it is in no cycle")
        }
        StmtKind::UnitAnnot(_) => unreachable!("a unit item binds no name, so it is in no cycle"),
        StmtKind::Struct(_)
        | StmtKind::Type(_)
        | StmtKind::Method(_)
        | StmtKind::Import(_)
        | StmtKind::Local(_)
        | StmtKind::Annotated { .. } => {
            unreachable!("resolve rejects the forms of layer L2")
        }
        StmtKind::Mutable(_)
        | StmtKind::IndexedDef(_)
        | StmtKind::Initial(_)
        | StmtKind::While(_)
        | StmtKind::Until(_)
        | StmtKind::Expr(_) => unreachable!("resolve rejects the forms of layer L6"),
    }
}
