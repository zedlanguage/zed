//! The binders of a unit and their uses (`Tables`), which the checker and elaboration share,
//! and the dependency order of its statements.

use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

use imbl::Vector;

use crate::resolve::{Ref, Resolution};
use zedc_syntax::ast::{Expr, ExprKind, Function, Param, Stmt, StmtKind, StrPart, Target, Type};
use zedc_syntax::lex::Span;

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
        let ids = res
            .binders
            .iter()
            .enumerate()
            .map(|(i, b)| ((b.span, b.name.as_str()), i))
            .collect();
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
        };
        t.collect_functions(unit);
        t
    }

    /// Records every function declaration and written type of `stmts` and of the blocks
    /// inside them. The walk keeps the parts still to visit on a heap stack, so a deeply nested
    /// expression does not grow the thread's stack. Each part's children go on the stack in
    /// reverse, so the parts are met in the order of the text, the order of `written`.
    fn collect_functions(&mut self, stmts: &'a [Stmt]) {
        let mut todo: Vec<Collect<'a>> = stmts.iter().rev().map(Collect::Stmt).collect();
        while let Some(c) = todo.pop() {
            let at = todo.len();
            match c {
                Collect::Type(t) => self.written.push(t),
                Collect::Stmt(s) => self.collect_stmt(s, &mut todo),
                Collect::Expr(e) => collect_expr(e, &mut todo),
            }
            todo[at..].reverse();
        }
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
                todo.extend(f.ports.iter().flatten().map(|p| Collect::Type(&p.ty)));
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
            | StmtKind::While(_)
            | StmtKind::Until(_)
            | StmtKind::Expr(_) => unreachable!("resolve rejects the forms of layer L6"),
        }
    }

    /// The order the statements of one scope are bound in, each after those it uses, a
    /// function's `test` tables aside; else the statements of each cycle. Each use of a
    /// binder of the scope is placed in its statement by a binary search, so the order
    /// reads the uses of the scope's own binders only, not those of the scopes inside it.
    /// A use of an overload set waits on one join node, which waits on the set's statements,
    /// so `U` uses of `K` overloads make `U + K` dependencies, not `U·K`.
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
                let mut named: Vec<usize> = (group.binders.iter())
                    .filter_map(|b| item_of.get(b).copied())
                    .collect();
                named.sort_unstable();
                named.dedup();
                let on = match named[..] {
                    [one] => one,
                    _ => {
                        deps.push(named);
                        deps.len() - 1
                    }
                };
                for u in &group.at {
                    let k = items.partition_point(|s| s.span.start <= u.start);
                    let Some(user) = k.checked_sub(1) else {
                        continue;
                    };
                    let at = items[user];
                    if u.end > at.span.end || in_tests(at, *u) {
                        continue;
                    }
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

/// The rejection of the cycle `cycle` among the statements `items` of one scope, a recursion,
/// which zedc compiles from layer L6 on: where to report it and the message. The cycle names
/// its statements by name and is reported at the first by name; the declarations of one name
/// keep their written order, so neither depends on where the items stand in the unit (DESIGN.md
/// L1.29b). The checker and elaboration both report it, in the same words, so that a unit
/// reports it once.
pub fn recursion(items: &[&Stmt], cycle: &[usize]) -> (Span, String) {
    let mut named: Vec<(String, usize)> = cycle.iter().map(|&i| (what(items[i]), i)).collect();
    named.sort_unstable();
    let names: Vec<&str> = named.iter().map(|(n, _)| n.as_str()).collect();
    let message = match &names[..] {
        [one] => format!("{one} is defined in terms of itself"),
        _ => format!("{} are defined in terms of each other", names.join(", ")),
    };
    (
        items[named[0].1].span,
        format!(
            "{message}, which is recursion. Recursion is part of the Zed language, and this \
             version of zedc does not compile it yet. Write the computation without a definition \
             that uses itself."
        ),
    )
}

/// How a message names the statement `s`: by the names it binds.
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
        StmtKind::Push { port, .. } => format!("the push to `{port}`"),
        StmtKind::Return(_) => "the export".into(),
        StmtKind::UnitAnnot(a) => format!("the unit item `@{}`", a.name),
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
        | StmtKind::While(_)
        | StmtKind::Until(_)
        | StmtKind::Expr(_) => unreachable!("resolve rejects the forms of layer L6"),
    }
}
