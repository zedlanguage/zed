//! Which functions can block (DESIGN.md sec:ports, "Every port operation says whether it can
//! block"; QUESTIONS A68). An operation on a port that can wait is blocking: a read of standard
//! input (`m.stdin`) or of a file (`files()`), each of which waits for its data, and a push to
//! an output port (`m.stdout`, `m.stderr`), which waits while the reader is not reading. A read
//! of `m.args` or `m.env` takes a short, fixed time and is not. A function can block when its
//! body performs a blocking operation or calls, or names as a value, a function that can, and
//! when it calls a function value whose body the checker cannot see. The fact is computed for
//! every declared function, for an editor to show, with the path of calls that makes a function
//! blocking ([`explain`]).
//!
//! Ports reach other functions as values: `first(m.stdin)` passes standard input to `first`,
//! whose reads of its parameter are reads of the port. Which names may hold a blocking input is
//! found by following each value as a whole: from the input to a name bound to it, to the
//! parameter a call passes it to, and from a function's result to its calls. Passing a port on
//! whole so is not a read: `main` above reads nothing itself, and blocks because it calls
//! `first`, which reads (and because it pushes). A value computed
//! from a port by an operator or a prelude word (`m.stdin[0]`, `count(m.stdin)`) is data read
//! where it is computed, which is that function's blocking read. A lambda's body is part of the
//! function that writes it: a read there is that function's, wherever the lambda is called.

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};

use imbl::Vector;
use zedc_resolve::resolve::tables::{ListKey, Tables};
use zedc_resolve::resolve::{Kind, Ref, Resolution, prelude_layer};
use zedc_syntax::ast::{
    Annot, Expr, ExprKind, Field, Function, IndexKey, Param, RangeEnd, Stmt, StmtKind, StrPart,
    Struct, Target, TypeKind,
};
use zedc_syntax::lex::Span;

/// Why a function can block: the first blocking operation its body performs, in the order of
/// the text, or else the call by which it first reaches one along a shortest path of calls.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Cause {
    /// It reads, at `at`, the name `value`, which holds the input `port` of `main`, `m.stdin`
    /// or `files()`; `value` is `port` itself when the body names the input.
    Reads {
        /// The binder read.
        value: usize,
        /// The input of `main` it holds.
        port: usize,
        /// The use.
        at: Span,
    },
    /// It pushes to the output port `port` of `main` in the push statement `at`.
    Pushes {
        /// The output port's binder.
        port: usize,
        /// The push statement.
        at: Span,
    },
    /// It calls, at `at`, the function value `callee`, whose body the checker cannot see.
    CallsValue {
        /// The call.
        at: Span,
        /// The callee as written.
        callee: Span,
    },
    /// It calls or names, at `at`, the function `callee`, which can block.
    Calls {
        /// The function's binder.
        callee: usize,
        /// The use of its name.
        at: Span,
    },
}

impl Cause {
    /// Where the body performs the operation or makes the call.
    pub fn at(&self) -> Span {
        match self {
            Cause::Reads { at, .. }
            | Cause::Pushes { at, .. }
            | Cause::CallsValue { at, .. }
            | Cause::Calls { at, .. } => *at,
        }
    }
}

/// A step backward over the calls, from a function or an overload set's junction.
enum Up {
    /// The function that names it, and the use.
    Caller(usize, Span),
    /// The junction of an overload set it is an arrow of.
    Set(usize),
}

/// Whether the parameter `p` of `main` is an input whose reads can block: `m.stdin` (`Lines`)
/// and `files()` (`Files`) can; `m.args` (`CommandLine`) and `m.env` (a lookup by name) take a
/// short, fixed time. The one place the inputs are classed: an input `main` gains is classed
/// here.
fn input_blocks(p: &Param) -> bool {
    match p.ty.as_ref().map(|t| &t.kind) {
        Some(TypeKind::Name(n)) => n == "Lines" || n == "Files",
        _ => false,
    }
}

/// An argument's place among a function's parameters: its position among the positional
/// parameters, or its name.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Slot<'a> {
    At(usize),
    Named(&'a str),
}

/// A call of a list of binders, recorded during the walk and joined to the declarations after
/// it, when every declaration is known: the values each argument may be, by its slot.
struct CallFlow<'a> {
    callee: &'a Vector<usize>,
    args: Vec<(Slot<'a>, Vec<usize>)>,
}

/// A part of the unit still to walk, and the function whose body holds it, if one does.
enum Part<'a> {
    Stmt(&'a Stmt),
    Expr(&'a Expr),
}

/// What the walk of a unit records, from which [`facts`] decides.
struct Walk<'t, 'a> {
    t: &'t Tables<'a>,
    /// The flow graph: the nodes each node's value may become. Nodes `0..binders` are the
    /// unit's binders; the others are the results of functions and the junctions below.
    flow: Vec<Vec<usize>>,
    /// The inputs of `main` whose reads block: where the flow starts.
    sources: Vec<usize>,
    /// The parameters of every `main`: ports, whose calls (`m.env("HOME")`) are reads.
    main_params: HashSet<usize>,
    /// The declaration of each function and method, by its binder.
    decls: HashMap<usize, &'a Function>,
    /// The functions, in the order of the text.
    functions: Vec<usize>,
    /// The function holding each use of a name, its text and the binders it names.
    uses: Vec<(usize, Span, &'a Vector<usize>)>,
    /// Each push: the function holding it, the statement and the port.
    pushes: Vec<(usize, Span, usize)>,
    /// Each call through a name that is no declared function: the function holding it, the
    /// call, the callee as written and the binders the name names. Decided after the flow.
    by_name: Vec<(usize, Span, Span, &'a Vector<usize>)>,
    /// Each call through a value the checker cannot see: the function, the call, the callee.
    unseen: Vec<(usize, Span, Span)>,
    /// The bindings whose value is a lambda or a declared function: a call through one calls a
    /// body the checker sees.
    seen_values: HashSet<usize>,
    /// The calls of declared functions, joined to the parameters after the walk.
    calls: Vec<CallFlow<'a>>,
    /// The node of the results of each list of functions a call may call, made once per list.
    results: HashMap<ListKey<'a>, usize>,
    /// The result node of each function.
    result_of: HashMap<usize, usize>,
    /// The uses of names whose value is passed on whole, as an argument of a declared
    /// function, a binding's value or a result: not reads, which the receiver makes.
    passed: HashSet<Span>,
}

/// Each function of the unit whose tables are `t` and whose statements are `unit` that can
/// block, by its binder, with why. A function not here cannot block.
// Complexity tradeoff: the naive method decides each function on its own, following its calls
// and the parameters its port arguments reach, O(F·(V+E)) for F functions over a call graph of
// V functions and E calls (a chain of n calls is O(n²)). This walks the unit once, O(n), builds
// the flow of port values and the call graph, then finds the names that may hold a blocking
// input by one search forward from the inputs, and the blocking functions by one search
// backward over the calls from the functions with a blocking operation of their own: each a
// breadth-first search with a visited set, O(V+E) (the transitive closure of one set, which
// is all the fact needs, not of every pair). The uses of an overload set of K arrows share one
// junction node, as `Tables` groups them (COMPLEXITY.md F49): U uses cost U + K edges, not U·K.
pub fn facts<'a>(t: &Tables<'a>, unit: &'a [Stmt]) -> BTreeMap<usize, Cause> {
    let mut w = Walk {
        t,
        flow: vec![Vec::new(); t.res.binders.len()],
        sources: Vec::new(),
        main_params: HashSet::new(),
        decls: HashMap::new(),
        functions: Vec::new(),
        uses: Vec::new(),
        pushes: Vec::new(),
        by_name: Vec::new(),
        unseen: Vec::new(),
        seen_values: HashSet::new(),
        calls: Vec::new(),
        results: HashMap::new(),
        result_of: HashMap::new(),
        passed: HashSet::new(),
    };
    w.walk(unit);
    w.join_calls();
    let holds = w.holds();
    w.blocking(&holds)
}

impl<'t, 'a> Walk<'t, 'a> {
    /// A new node of the flow graph.
    fn node(&mut self) -> usize {
        self.flow.push(Vec::new());
        self.flow.len() - 1
    }

    /// The result node of the function `f`.
    fn result(&mut self, f: usize) -> usize {
        if let Some(&r) = self.result_of.get(&f) {
            return r;
        }
        let r = self.node();
        self.result_of.insert(f, r);
        r
    }

    /// The binders `ids` of a use, when they are declared functions or methods.
    fn functions_in(&self, r: Option<&'a Ref>) -> Option<&'a Vector<usize>> {
        match r {
            Some(Ref::Bound(ids))
                if matches!(
                    self.t.res.binders[ids[0]].kind,
                    Kind::Function | Kind::Method
                ) =>
            {
                Some(ids)
            }
            Some(Ref::Bound(_) | Ref::Prelude(_) | Ref::Unit { .. }) | None => None,
        }
    }

    /// Walks the statements `unit` with an explicit stack, so a deep tree takes no thread stack.
    fn walk(&mut self, unit: &'a [Stmt]) {
        let mut todo: Vec<(Part<'a>, Option<usize>)> =
            unit.iter().rev().map(|s| (Part::Stmt(s), None)).collect();
        while let Some((part, owner)) = todo.pop() {
            match part {
                Part::Stmt(s) => self.stmt(s, owner, &mut todo),
                Part::Expr(e) => self.expr(e, owner, &mut todo),
            }
        }
    }

    /// The function `f` declared by the statement `s` as `name`: a node of its own, its body
    /// and its parameters' defaults walked as its own. Its test rows are not its body and are
    /// not walked.
    fn function(
        &mut self,
        s: &'a Stmt,
        name: &str,
        f: &'a Function,
        todo: &mut Vec<(Part<'a>, Option<usize>)>,
    ) {
        let Some(&id) = self.t.ids.get(&(s.span, name)) else {
            // Not bound (a primed name, refused by resolution): no fact, its body walked as
            // no function's.
            todo.push((Part::Expr(&f.body), None));
            return;
        };
        self.decls.insert(id, f);
        self.functions.push(id);
        if f.main.is_some() {
            for p in &f.params {
                let Some(&b) = self.t.ids.get(&(p.span, p.name.as_str())) else {
                    continue;
                };
                self.main_params.insert(b);
                if input_blocks(p) {
                    self.sources.push(b);
                }
            }
        }
        let r = self.result(id);
        for v in self.values(&f.body) {
            self.flow[v].push(r);
        }
        todo.push((Part::Expr(&f.body), Some(id)));
        todo.extend(
            (f.params.iter().rev())
                .filter_map(|p| p.default.as_ref())
                .map(|d| (Part::Expr(d), Some(id))),
        );
    }

    fn stmt(
        &mut self,
        s: &'a Stmt,
        owner: Option<usize>,
        todo: &mut Vec<(Part<'a>, Option<usize>)>,
    ) {
        let expr = |e: &'a Expr| (Part::Expr(e), owner);
        match &s.kind {
            StmtKind::Bind { targets, value } => {
                self.bind(s.span, targets, value);
                todo.push(expr(value));
            }
            StmtKind::Initial(i) => {
                todo.push(expr(&i.value));
                todo.extend(keys(&i.keys).map(expr));
            }
            StmtKind::Local(decl) => todo.push((Part::Stmt(decl), owner)),
            StmtKind::Annotated { annots, decl } => {
                todo.push((Part::Stmt(decl), owner));
                todo.extend(annots.iter().flat_map(annot).map(expr));
            }
            StmtKind::IndexedDef(d) => {
                todo.push(expr(&d.value));
                todo.extend(keys(&d.keys).map(expr));
                for b in &d.boundary {
                    todo.push(expr(&b.value));
                    todo.extend(keys(&b.keys).map(expr));
                }
            }
            StmtKind::While(e) | StmtKind::Until(e) | StmtKind::Expr(e) => todo.push(expr(e)),
            StmtKind::Return(es) => todo.extend(es.iter().rev().map(expr)),
            StmtKind::Function(f) => self.function(s, &f.name, f, todo),
            StmtKind::Method(m) => {
                let name = format!("{}.{}", m.receiver, m.function.name);
                self.function(s, &name, &m.function, todo)
            }
            StmtKind::Push { value, .. } => {
                if let (Some(f), Some(Ref::Bound(ids))) = (owner, self.t.res.uses.get(&s.span)) {
                    self.pushes.push((f, s.span, ids[0]));
                }
                todo.push(expr(value));
            }
            StmtKind::Struct(Struct { fields, .. }) => {
                todo.extend(fields.iter().filter_map(|f| match f {
                    Field::Typed { default, .. } => default.as_ref().map(expr),
                    Field::Import { .. } => None,
                }))
            }
            StmtKind::Type(_) | StmtKind::Import(_) => {}
            StmtKind::UnitAnnot(a) => todo.extend(annot(a).map(expr)),
        }
    }

    /// The binding `targets = value` of the statement at `span`: the value flows to each
    /// target, through one junction when there are several, so a tuple of k values bound to k
    /// names makes 2k edges, not k².
    fn bind(&mut self, span: Span, targets: &'a [Target], value: &'a Expr) {
        let ids: Vec<usize> = (targets.iter())
            .filter_map(|t| match t {
                Target::Name(n, _) => self.t.ids.get(&(span, n.as_str())).copied(),
                Target::Wild => None,
            })
            .collect();
        let values = self.values(value);
        let into = match ids.as_slice() {
            [] => return,
            [one] => {
                let named = self.t.res.uses.get(&value.span);
                let seen = matches!(value.kind, ExprKind::Lambda { .. } | ExprKind::Section(_))
                    || (matches!(value.kind, ExprKind::Name(_))
                        && (matches!(named, Some(Ref::Prelude(_)))
                            || self.functions_in(named).is_some()));
                if seen {
                    self.seen_values.insert(*one);
                }
                *one
            }
            many => {
                let j = self.node();
                self.flow[j].extend_from_slice(many);
                j
            }
        };
        for v in values {
            self.flow[v].push(into);
        }
    }

    fn expr(
        &mut self,
        e: &'a Expr,
        owner: Option<usize>,
        todo: &mut Vec<(Part<'a>, Option<usize>)>,
    ) {
        let uses = &self.t.res.uses;
        match &e.kind {
            ExprKind::Block(stmts) => {
                todo.extend(stmts.iter().rev().map(|s| (Part::Stmt(s), owner)));
                return;
            }
            ExprKind::Name(_) | ExprKind::This => {
                if let (Some(f), Some(Ref::Bound(ids))) = (owner, uses.get(&e.span)) {
                    self.uses.push((f, e.span, ids));
                }
            }
            // `x.f` names `f` when `f` is in scope: the call `f(x)`, whose receiver is its first
            // positional argument.
            ExprKind::Member { of, .. } => {
                if let (Some(f), Some(Ref::Bound(ids))) = (owner, uses.get(&e.span)) {
                    self.uses.push((f, e.span, ids));
                }
                if let Some(ids) = self.functions_in(uses.get(&e.span)) {
                    let receiver = self.values(of);
                    self.calls.push(CallFlow {
                        callee: ids,
                        args: vec![(Slot::At(0), receiver)],
                    });
                }
            }
            ExprKind::Call {
                callee,
                positional,
                named,
                ..
            } => self.call(e.span, callee, positional, named, owner),
            ExprKind::Int { .. }
            | ExprKind::Float { .. }
            | ExprKind::Rat(_)
            | ExprKind::Str(_)
            | ExprKind::Bool(_)
            | ExprKind::Atom(_)
            | ExprKind::Unary(..)
            | ExprKind::Binary(..)
            | ExprKind::Index(..)
            | ExprKind::Tuple(_)
            | ExprKind::Lambda { .. }
            | ExprKind::Is { .. }
            | ExprKind::Else { .. }
            | ExprKind::If { .. }
            | ExprKind::Record(_)
            | ExprKind::With { .. }
            | ExprKind::Match { .. }
            | ExprKind::Range(..)
            | ExprKind::In { .. }
            | ExprKind::Reduce { .. }
            | ExprKind::Read { .. }
            | ExprKind::Section(_)
            | ExprKind::Array(_)
            | ExprKind::Set(_)
            | ExprKind::Map(_)
            | ExprKind::For { .. }
            | ExprKind::Loop { .. }
            | ExprKind::Break(_)
            | ExprKind::Spread { .. }
            | ExprKind::SortKey { .. } => {}
        }
        let at = todo.len();
        kids(&e.kind, &mut |k| todo.push((Part::Expr(k), owner)));
        todo[at..].reverse();
    }

    /// The call at `span` of `callee` with the arguments `positional` and `named`, in the
    /// function `owner`: its arguments' flow to the parameters of a declared callee, or the
    /// callee's class when it is a value.
    fn call(
        &mut self,
        span: Span,
        callee: &'a Expr,
        positional: &'a [Expr],
        named: &'a [(String, Expr)],
        owner: Option<usize>,
    ) {
        let uses = &self.t.res.uses;
        let r = uses.get(&callee.span);
        if let Some(ids) = self.functions_in(r) {
            // `x.f(a)` is `f(x, a)`: the receiver is the first positional argument, which the
            // walk of the member records.
            let first = usize::from(matches!(callee.kind, ExprKind::Member { .. }));
            let mut args = Vec::new();
            for (i, a) in positional.iter().enumerate() {
                args.push((Slot::At(first + i), self.values(a)));
            }
            for (n, a) in named {
                args.push((Slot::Named(n.as_str()), self.values(a)));
            }
            self.calls.push(CallFlow { callee: ids, args });
            return;
        }
        let Some(f) = owner else { return };
        let unseen = match (&callee.kind, r) {
            (ExprKind::Lambda { .. } | ExprKind::Section(_), _) => false,
            (_, Some(Ref::Prelude(_))) => false,
            // A definition of another unit: its body is not in this unit, and until step L2.4
            // links units its fact is not known here, so the call counts as blocking.
            (_, Some(Ref::Unit { .. })) => true,
            (_, Some(Ref::Bound(ids))) => {
                self.by_name.push((f, span, callee.span, ids));
                false
            }
            // `x.f(a)` with no `f` in scope: a prelude word, or a field of `x` holding a
            // function, whose body the checker cannot see.
            (ExprKind::Member { name, .. }, None) => prelude_layer(name).is_none(),
            // A name not in scope, which resolution reports.
            (ExprKind::Name(_), None) => false,
            (_, None) => true,
        };
        if unseen {
            self.unseen.push((f, span, callee.span));
        }
    }

    /// The nodes whose value `e` may be as a whole: a name, a branch of an `if`, a `match` or an
    /// `else`, a block's result, a tuple's items, and the results of the functions a call
    /// calls. A value computed from them by an operator or a prelude word is not one.
    fn values(&mut self, e: &'a Expr) -> Vec<usize> {
        let uses = &self.t.res.uses;
        let mut out = Vec::new();
        let mut todo = vec![e];
        while let Some(e) = todo.pop() {
            match &e.kind {
                ExprKind::Name(_) => {
                    if let Some(Ref::Bound(ids)) = uses.get(&e.span)
                        && ids.len() == 1
                    {
                        out.push(ids[0]);
                        self.passed.insert(e.span);
                    }
                }
                ExprKind::If {
                    then, otherwise, ..
                } => todo.extend([&**otherwise, &**then]),
                ExprKind::Else { of, default, .. } => todo.extend([&**default, &**of]),
                ExprKind::Match { arms, .. } => todo.extend(arms.iter().rev().map(|a| &a.body)),
                ExprKind::Tuple(items) => todo.extend(items.iter().rev()),
                ExprKind::Block(stmts) => {
                    for s in stmts.iter().rev() {
                        if let StmtKind::Return(es) = &s.kind {
                            todo.extend(es.iter().rev());
                        }
                    }
                }
                ExprKind::Call { callee, .. } => {
                    if let Some(ids) = self.functions_in(uses.get(&callee.span)) {
                        out.push(self.results_of(ids));
                    }
                }
                // Data computed from its parts, or a value holding no port.
                ExprKind::Int { .. }
                | ExprKind::Float { .. }
                | ExprKind::Rat(_)
                | ExprKind::Str(_)
                | ExprKind::Bool(_)
                | ExprKind::Atom(_)
                | ExprKind::Unary(..)
                | ExprKind::Binary(..)
                | ExprKind::Index(..)
                | ExprKind::Lambda { .. }
                | ExprKind::Is { .. }
                | ExprKind::Member { .. }
                | ExprKind::Record(_)
                | ExprKind::With { .. }
                | ExprKind::This
                | ExprKind::Range(..)
                | ExprKind::In { .. }
                | ExprKind::Reduce { .. }
                | ExprKind::Read { .. }
                | ExprKind::Section(_)
                | ExprKind::Array(_)
                | ExprKind::Set(_)
                | ExprKind::Map(_)
                | ExprKind::For { .. }
                | ExprKind::Loop { .. }
                | ExprKind::Break(_)
                | ExprKind::Spread { .. }
                | ExprKind::SortKey { .. } => {}
            }
        }
        out
    }

    /// The node of the results of the functions `ids`, made once per list: each function's
    /// result flows to it.
    fn results_of(&mut self, ids: &'a Vector<usize>) -> usize {
        if let Some(&n) = self.results.get(&ListKey(ids)) {
            return n;
        }
        let n = self.node();
        for &f in ids {
            let r = self.result(f);
            self.flow[r].push(n);
        }
        self.results.insert(ListKey(ids), n);
        n
    }

    /// Joins each recorded call to the parameters of the functions it may call: each argument
    /// flows to the parameter of its slot in each. The slots of a list of functions are indexed
    /// once per list, O(their parameters), and each argument reaches its slot through one
    /// junction per list and slot, so U calls of K arrows cost U + K edges per slot, not U·K.
    fn join_calls(&mut self) {
        let calls = std::mem::take(&mut self.calls);
        let mut slots: HashMap<ListKey<'a>, HashMap<Slot<'a>, usize>> = HashMap::new();
        for c in calls {
            let index = (slots.entry(ListKey(c.callee))).or_insert_with(|| self.slots(c.callee));
            for (slot, values) in c.args {
                let Some(&j) = index.get(&slot) else { continue };
                for v in values {
                    self.flow[v].push(j);
                }
            }
        }
    }

    /// A junction for each slot of the functions `ids`, which flows to that slot's parameter
    /// in each of them that has it.
    fn slots(&mut self, ids: &'a Vector<usize>) -> HashMap<Slot<'a>, usize> {
        let mut index: HashMap<Slot<'a>, usize> = HashMap::new();
        for &f in ids {
            let Some(decl) = self.decls.get(&f).copied() else {
                continue;
            };
            let mut at = 0;
            for p in &decl.params {
                let slot = match p.positional || p.tuple.is_some() {
                    true => {
                        at += 1;
                        Slot::At(at - 1)
                    }
                    false => Slot::Named(p.name.as_str()),
                };
                let binders: Vec<usize> = match &p.tuple {
                    None => (self.t.ids.get(&(p.span, p.name.as_str())).copied())
                        .into_iter()
                        .collect(),
                    Some(targets) => (targets.iter())
                        .filter_map(|t| match t {
                            Target::Name(n, at) => self.t.ids.get(&(*at, n.as_str())).copied(),
                            Target::Wild => None,
                        })
                        .collect(),
                };
                let j = match index.get(&slot) {
                    Some(&j) => j,
                    None => {
                        let j = self.node();
                        index.insert(slot, j);
                        j
                    }
                };
                self.flow[j].extend(binders);
            }
        }
        index
    }

    /// The input of `main` each node may hold, if any: one breadth-first search forward from
    /// the inputs, each node visited once, O(nodes + edges).
    fn holds(&self) -> Vec<Option<usize>> {
        let mut port = vec![None; self.flow.len()];
        let mut queue = VecDeque::new();
        for &s in &self.sources {
            if port[s].is_none() {
                port[s] = Some(s);
                queue.push_back(s);
            }
        }
        while let Some(n) = queue.pop_front() {
            for &m in &self.flow[n] {
                if port[m].is_none() {
                    port[m] = port[n];
                    queue.push_back(m);
                }
            }
        }
        port
    }

    /// The blocking functions: those with a blocking operation of their own, first in the
    /// order of the text, then those that call one, by one breadth-first search backward over
    /// the calls, each function visited once, so each gets a shortest path of calls.
    fn blocking(self, holds: &[Option<usize>]) -> BTreeMap<usize, Cause> {
        let binders = &self.t.res.binders;
        let mut own: HashMap<usize, Cause> = HashMap::new();
        let mut first = |f: usize, c: Cause| match own.get(&f) {
            Some(old) if old.at().start <= c.at().start => {}
            Some(_) | None => {
                own.insert(f, c);
            }
        };
        // The calls backward, over nodes numbered as binders and, past them, one junction per
        // overload set: each node's callers, and the junctions of the sets it is an arrow of.
        let mut up: HashMap<usize, Vec<Up>> = HashMap::new();
        let mut sets: HashMap<ListKey<'a>, usize> = HashMap::new();
        for &(f, at, ids) in &self.uses {
            if ids.len() == 1
                && !self.passed.contains(&at)
                && let Some(port) = holds[ids[0]]
            {
                first(
                    f,
                    Cause::Reads {
                        value: ids[0],
                        port,
                        at,
                    },
                );
            }
            match binders[ids[0]].kind {
                Kind::Function | Kind::Method if ids.len() == 1 => {
                    up.entry(ids[0]).or_default().push(Up::Caller(f, at));
                }
                Kind::Function | Kind::Method => {
                    let next = binders.len() + sets.len();
                    let s = *sets.entry(ListKey(ids)).or_insert_with(|| {
                        for &g in ids {
                            up.entry(g).or_default().push(Up::Set(next));
                        }
                        next
                    });
                    up.entry(s).or_default().push(Up::Caller(f, at));
                }
                Kind::Binding
                | Kind::Param
                | Kind::Port
                | Kind::Pattern
                | Kind::Struct
                | Kind::Type
                | Kind::TypeParam
                | Kind::Field
                | Kind::Receiver
                | Kind::Unit => {}
            }
        }
        for &(f, at, port) in &self.pushes {
            first(f, Cause::Pushes { port, at });
        }
        for &(f, at, callee) in &self.unseen {
            first(f, Cause::CallsValue { at, callee });
        }
        for &(f, at, callee, ids) in &self.by_name {
            let b = ids[0];
            let unseen = match binders[b].kind {
                Kind::Function
                | Kind::Method
                | Kind::Struct
                | Kind::Type
                | Kind::TypeParam
                | Kind::Field
                | Kind::Port
                | Kind::Unit => false,
                // A parameter of `main` is a port, whose call (`m.env("HOME")`) is a read,
                // decided above; another parameter holds a function value whose body the
                // checker cannot see, as does a binding not bound to a lambda or a function.
                Kind::Param => !self.main_params.contains(&b) && holds[b].is_none(),
                Kind::Binding => !self.seen_values.contains(&b) && holds[b].is_none(),
                Kind::Pattern | Kind::Receiver => true,
            };
            if unseen {
                first(f, Cause::CallsValue { at, callee });
            }
        }
        // The search: `out` is the visited set of the functions and `reached` that of the
        // junctions; each queued node carries the blocking function it was reached from.
        let mut out: BTreeMap<usize, Cause> = BTreeMap::new();
        let mut reached: HashSet<usize> = HashSet::new();
        let mut queue: VecDeque<(usize, usize)> = VecDeque::new();
        for &f in &self.functions {
            if let Some(c) = own.remove(&f) {
                out.insert(f, c);
                queue.push_back((f, f));
            }
        }
        while let Some((n, callee)) = queue.pop_front() {
            for u in up.get(&n).map_or(&[][..], Vec::as_slice) {
                match *u {
                    Up::Caller(f, at) => {
                        if let std::collections::btree_map::Entry::Vacant(e) = out.entry(f) {
                            e.insert(Cause::Calls { callee, at });
                            queue.push_back((f, f));
                        }
                    }
                    Up::Set(s) => {
                        if reached.insert(s) {
                            queue.push_back((s, callee));
                        }
                    }
                }
            }
        }
        out
    }
}

/// The expressions of the keys `keys`.
fn keys(keys: &[IndexKey]) -> impl DoubleEndedIterator<Item = &Expr> {
    keys.iter().map(|k| match k {
        IndexKey::In { set, .. } => set,
        IndexKey::At(e) => e,
    })
}

/// The expressions of the annotation `a`.
fn annot(a: &Annot) -> impl Iterator<Item = &Expr> {
    (a.positional.iter()).chain(a.named.iter().map(|(_, e)| e))
}

/// Gives `push` each expression directly in `kind`, except a block's, whose statements the
/// walk takes.
fn kids<'a>(kind: &'a ExprKind, push: &mut impl FnMut(&'a Expr)) {
    match kind {
        ExprKind::Int { .. }
        | ExprKind::Float { .. }
        | ExprKind::Rat(_)
        | ExprKind::Bool(_)
        | ExprKind::Atom(_)
        | ExprKind::Name(_)
        | ExprKind::This
        | ExprKind::Section(_)
        | ExprKind::Block(_) => {}
        ExprKind::Str(parts) => (parts.iter()).for_each(|p| match p {
            StrPart::Hole(e) => push(e),
            StrPart::Text(_) => {}
        }),
        ExprKind::Unary(_, a)
        | ExprKind::Is { of: a, .. }
        | ExprKind::Member { of: a, .. }
        | ExprKind::Read { of: a, .. }
        | ExprKind::Loop { body: a, .. }
        | ExprKind::Break(a)
        | ExprKind::Spread { of: a, .. } => push(a),
        ExprKind::SortKey { key, .. } => key.as_deref().into_iter().for_each(push),
        ExprKind::Binary(_, a, b)
        | ExprKind::Index(a, b)
        | ExprKind::In { of: a, set: b, .. }
        | ExprKind::Reduce { of: a, op: b }
        | ExprKind::Else {
            of: a, default: b, ..
        } => {
            push(a);
            push(b);
        }
        ExprKind::Call {
            callee,
            positional,
            named,
            ..
        } => {
            push(callee);
            positional.iter().for_each(&mut *push);
            named.iter().for_each(|(_, e)| push(e));
        }
        ExprKind::Tuple(es) | ExprKind::Array(es) | ExprKind::Set(es) => es.iter().for_each(push),
        ExprKind::Map(entries) => entries.iter().for_each(|(k, v)| {
            push(k);
            push(v);
        }),
        ExprKind::Range(from, to) => {
            push(from);
            match to {
                RangeEnd::Below(b) | RangeEnd::Through(b) => push(b),
                RangeEnd::Open => {}
            }
        }
        ExprKind::For {
            source,
            guard,
            body,
            ..
        } => {
            push(source);
            guard.as_deref().into_iter().for_each(&mut *push);
            push(body);
        }
        ExprKind::Lambda { params, body } => {
            params
                .iter()
                .filter_map(|p| p.default.as_ref())
                .for_each(&mut *push);
            push(body);
        }
        ExprKind::Match { of, arms } => {
            push(of);
            for a in arms {
                a.guard.iter().for_each(&mut *push);
                push(&a.body);
            }
        }
        ExprKind::Record(fields) => fields.iter().for_each(|(_, e)| push(e)),
        ExprKind::With { of, updates } => {
            push(of);
            updates.iter().for_each(|u| push(&u.value));
        }
        ExprKind::If {
            cond,
            then,
            otherwise,
        } => {
            push(cond);
            push(then);
            push(otherwise);
        }
    }
}

/// Why the function `f` can block, in the program's words, from the facts `facts` of its unit
/// resolved as `res`, whose text is `text`: the path of calls from `f` to the blocking
/// operation, as an editor shows it; `None` when `f` cannot block.
pub fn explain(
    facts: &BTreeMap<usize, Cause>,
    res: &Resolution,
    text: Option<&str>,
    f: usize,
) -> Option<String> {
    let name = |b: usize| format!("`{}`", res.binders[b].name);
    let mut out = format!("{} can block:", name(f));
    // Each step goes to a function the search marked before the one it leaves, so the path
    // ends; `seen` is its visited set all the same.
    let mut seen: HashSet<usize> = HashSet::new();
    let mut g = f;
    let mut cause = facts.get(&f)?;
    let mut lead = " it";
    loop {
        seen.insert(g);
        match cause {
            Cause::Calls { callee, .. } => {
                out.push_str(&format!("{lead} calls {}", name(*callee)));
                g = *callee;
                cause = facts
                    .get(&g)
                    .expect("a function a blocking call reaches is blocking");
                assert!(!seen.contains(&g), "the path of calls has no cycle");
                lead = ", which";
            }
            Cause::Reads { value, port, .. } if value == port => {
                out.push_str(&format!(
                    "{lead} reads {}, which can wait for its data.",
                    name(*port)
                ));
                return Some(out);
            }
            Cause::Reads { value, port, .. } => {
                out.push_str(&format!(
                    "{lead} reads {}, which holds {}, which can wait for its data.",
                    name(*value),
                    name(*port)
                ));
                return Some(out);
            }
            Cause::Pushes { port, .. } => {
                out.push_str(&format!(
                    "{lead} pushes to {}, which can wait while its reader does not read.",
                    name(*port)
                ));
                return Some(out);
            }
            Cause::CallsValue { callee, .. } => {
                let written = text.map_or("a function value".to_string(), |t| {
                    format!("`{}`", &t[callee.start..callee.end])
                });
                out.push_str(&format!(
                    "{lead} calls {written}, a function value whose body is not known where it \
                     is called, so the call may block."
                ));
                return Some(out);
            }
        }
    }
}
