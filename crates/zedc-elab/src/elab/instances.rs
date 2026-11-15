//! One body of a generic function for each identity its calls decide (REDUCE-generic-identity;
//! DESIGN.md sec:reduction, "Identity as data"). A fold `xs >< max` in `top(positional xs)`
//! called at `int` folds an empty level to `#empty`, and called at `f64` to `-inf`; an empty
//! level holds no entry to tell its carrier at run time, so one body cannot give both. The
//! checker lists each such fold (`Info::split_folds`), the identity each call found for it
//! (`Info::fold_calls`), and the folds each function's calls decide (`Info::split_needs`).
//! Elaboration gives each call of a top-level function that decides them a body made at
//! those identities, `top@N`, one for each distinct list of identities, as sec:units makes
//! one body per instance of a generic. A call inside such a body that the checker did not
//! decide on its own, as `top(ys)` in `g(ys) = top(ys)`, takes the identities of the body it
//! is in, which the outer call decided. A lambda passed to a built-in that calls it only
//! while the call runs ([`IN_PLACE`]: `.map`, `.where`, …) is part of the body around it: the
//! identities that call decided, as for `m.map(r -> top(r))` checked at `f64`, are in force
//! in the lambda, and a fold under it, as in `g(mm) = mm.map(r -> top(r))`, is decided by
//! `g`'s calls (the checker searches the needs nested in `g`'s signature).
//!
//! What stays refused, as "not compiled yet": a fold whose identity no call decides where it
//! is elaborated (a function passed as a value, a nested function or any other lambda, whose
//! bodies take no identity from around them, a default that folds), a read where two
//! identities for one fold are in force (a `.map` at `f64` inside one at `int`, both folding
//! by one `top`), and a call whose decided folds are not all its callee's. Each such
//! fold is recorded where it is met ([`Instancing::undecided`]); the definitions it lands in
//! are refused when the unit reaches them, and a decided call no elaboration took is refused
//! at once ([`Elab::check_instances`]).

use std::collections::hash_map::Entry;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::mem;
use std::sync::Arc;

use zed_kernel::{Shared, Term, Value};
use zedc_base::rejection::not_yet;
use zedc_stage::defs::{Def, Test};
use zedc_stage::stage::free;
use zedc_syntax::ast::{Error, Expr, ExprKind, Note, Stmt, StmtKind};
use zedc_syntax::lex::Span;

use super::state::Elab;

/// The identities of the folds a body is made at, by fold.
pub(super) type Env = HashMap<Span, Option<Value>>;

/// What [`Elab::enter_expr`] changed, for [`Elab::leave_expr`] to put back.
pub(super) enum Saved {
    /// The entries a built-in call put in `env`: each fold with its earlier entry and
    /// provider, or none.
    Pushed(Vec<(Span, Option<Option<Value>>, Option<Span>)>),
    /// The identities and providers in force around a body that takes none from there.
    Cleared(Env, HashMap<Span, Span>),
}

/// The built-in methods that apply a lambda passed to them only while the call runs (DESIGN.md
/// sec:tour_collections, sec:grouping, sec:reduction): a check of such a lambda's folds is a
/// check of the call's needs, made at the call's frame. The lambda itself is not kept in the
/// result; what its body builds that outlives the call, as `r -> (y -> top(y))` builds
/// `y -> top(y)`, is a lambda or a function of its own, whose body takes no identity from here
/// (`clear_env`).
const IN_PLACE: [&str; 8] = [
    "map", "where", "foldl", "foldr", "flatMap", "group", "rekey", "reduce",
];

/// The bodies made and to make, and the folds no call decided where they were met.
pub(super) struct Instancing<'a> {
    /// The identities the body being elaborated is made at; empty for a written body.
    pub(super) env: Env,
    /// Each body made or queued, by the function's binder and the identities of its
    /// `split_needs` in their order: its kernel name.
    made: HashMap<(usize, Vec<Option<Value>>), Arc<str>>,
    /// The bodies to make: binder, kernel name, identities.
    queue: Vec<(usize, Arc<str>, Env)>,
    /// For each fold of `env` that a built-in call put there ([`Elab::enter_expr`]), that
    /// call's span.
    provider: HashMap<Span, Span>,
    /// The entries of [`zedc_check::check::Info::fold_calls`] elaboration took, by call and
    /// fold: at a call of the function whose body runs the fold ([`Elab::fkernel`]), or by
    /// a read of the fold that found the entry its call put in `env`.
    consumed: HashSet<(Span, Span)>,
    /// The bodies of lambdas passed directly to a built-in call that applies them in place,
    /// whose folds take the identities that call decides ([`Elab::enter_expr`]), by span.
    in_place: HashSet<Span>,
    /// The number of bodies being elaborated whose folds take no identity from around them
    /// ([`Elab::enter_expr`]); while it is above zero, no built-in call puts any in `env`.
    opaque: usize,
    /// The folds met with no identity decided, since the last time they were attributed.
    pub(super) undecided: Vec<Span>,
    /// The folds no call decided in each definition, by kernel name.
    undecided_defs: HashMap<Arc<str>, Vec<Span>>,
    /// Each function declared at the unit's top level, by its binder.
    pub(super) fns: HashMap<usize, &'a Stmt>,
    /// The binders by the start of their spans: start, end, binder; made at the first body.
    by_start: Vec<(usize, usize, usize)>,
    /// The number the next fresh kernel name takes, `name@N`: above every number
    /// [`Elab::new`] gives, which is at most the number of binders.
    next: usize,
    /// The bodies made, each with the binder of the function it is a body of.
    pub(super) bodies: Vec<(usize, Def)>,
}

impl Instancing<'_> {
    pub(super) fn new(next: usize) -> Self {
        Instancing {
            env: HashMap::new(),
            made: HashMap::new(),
            queue: Vec::new(),
            provider: HashMap::new(),
            consumed: HashSet::new(),
            in_place: HashSet::new(),
            opaque: 0,
            undecided: Vec::new(),
            undecided_defs: HashMap::new(),
            fns: HashMap::new(),
            by_start: Vec::new(),
            next,
            bodies: Vec::new(),
        }
    }

    /// Records that the definitions `kernels` hold the folds `sites`, which no call decided.
    pub(super) fn attribute<'k>(
        &mut self,
        kernels: impl IntoIterator<Item = &'k Arc<str>>,
        sites: Vec<Span>,
    ) {
        if sites.is_empty() {
            return;
        }
        for k in kernels {
            (self.undecided_defs.entry(k.clone()).or_default()).extend(&sites);
        }
    }
}

/// `t`, a default's term at a call ([`Elab::defaults`]), with each name of `map` renamed: a
/// literal, a marked literal, a parameter's name, or a call of the default's own definition on
/// parameters' names, the shapes `Frame::FnDefault` makes.
fn renamed(t: &Term, map: &HashMap<Arc<str>, Arc<str>>) -> Term {
    let name = |x: &Arc<str>| map.get(x).unwrap_or(x).clone();
    match t {
        Term::Var(x) => Term::Var(name(x)),
        Term::App(f, args) => Term::App(
            f.clone(),
            (args.iter())
                .map(|a| match a {
                    Term::Var(x) => Term::Var(name(x)),
                    a => a.clone(),
                })
                .collect(),
        ),
        t => t.clone(),
    }
}

/// The refusal of the fold at `site`, whose words the checker wrote (`Info::split_folds`).
fn refusal(site: Span, what: &str) -> Error {
    Error {
        menu: String::new(),
        row: None,
        span: site,
        message: not_yet(what),
        notes: vec![Note {
            span: site,
            text: "repair: write the function once for each of these types".to_string(),
        }],
    }
}

impl<'a> Elab<'a> {
    /// The identity of the fold at `site`: the one the checker found, or for a fold whose
    /// calls decide it ([`zedc_check::check::Info::split_folds`]) the one of the body being
    /// made; none where that folds an empty level to `#empty`. A fold no call decided here is
    /// recorded ([`Instancing::undecided`]) and elaborated with none, for a body no call
    /// reaches, or for [`Self::check_instances`] to refuse.
    pub(super) fn fold_identity(&mut self, site: Span) -> Option<Value> {
        if !self.info.split_folds.contains_key(&site) {
            return self.info.reduce.get(&site).cloned();
        }
        self.env_identity(site).flatten()
    }

    /// The identity `env` holds for the fold at `site`, taking the entry of the built-in call
    /// that put it there; none recorded as undecided.
    fn env_identity(&mut self, site: Span) -> Option<Option<Value>> {
        let Some(v) = self.inst.env.get(&site) else {
            self.inst.undecided.push(site);
            return None;
        };
        if let Some(&call) = self.inst.provider.get(&site) {
            self.inst.consumed.insert((call, site));
        }
        Some(v.clone())
    }

    /// Enters the expression `e` where folds the checker decided at calls exist
    /// ([`zedc_check::check::Info::split_folds`]). Returns what it changed, for
    /// [`Self::leave_expr`].
    ///
    /// A call of a built-in of [`IN_PLACE`] puts the identities the checker decided at it
    /// ([`zedc_check::check::Info::fold_calls`]) in `env` for the code within it, as the
    /// lambda of `m.map(r -> top(r))` is checked at the call of `map`; its lambdas take them.
    /// Any other lambda's body, and any function declared in a block, takes none and lets no
    /// built-in put any: the checker checks it where it is called, as `f(m["a"])` for
    /// `f = x -> top(x)`, which is not where it is written. A fold met there with no call of
    /// its function deciding it is refused when the unit reaches it.
    ///
    /// Why a fold's read inside a built-in's lambda takes the identity its check found: the
    /// read's need is met at its own call (whose entry [`Self::fkernel`] takes before `env`),
    /// or passes to the lambda's signature and from there is met at the built-in's call or
    /// passes on outward, through built-in calls only, since every other body cuts `env`
    /// off, to the body being elaborated, whose entries came from its own call. Each of
    /// those calls that met a need on the fold put its one result in `env` around the read,
    /// and a call whose result differs from the entry in force is refused, not put there
    /// (the fold is recorded as undecided), so every entry in force around the read is the one
    /// result, the meeting call's among them.
    // Complexity tradeoff: one hash lookup per expression, and per built-in call O(k) to put
    // and later restore the k identities the checker decided at it, so O(e + Σk) for a body
    // of e expressions; a lambda's body takes the maps out and puts them back whole, O(1).
    // The naive form, a scope chain searched outward at each fold, costs O(depth) per fold.
    pub(super) fn enter_expr(&mut self, e: &Expr) -> Option<Saved> {
        match &e.kind {
            ExprKind::Lambda { .. } if self.inst.in_place.remove(&e.span) => None,
            ExprKind::Lambda { .. } => Some(self.clear_env()),
            ExprKind::Call {
                callee,
                positional,
                named,
                ..
            } if matches!(&callee.kind, ExprKind::Member { name, .. } if IN_PLACE.contains(&&**name)) =>
            {
                let args = positional.iter().chain(named.iter().map(|(_, a)| a));
                for a in args {
                    if matches!(a.kind, ExprKind::Lambda { .. }) {
                        self.inst.in_place.insert(a.span);
                    }
                }
                if self.inst.opaque > 0 {
                    return None;
                }
                let given = self.info.fold_calls.get(&e.span)?;
                let mut saved = Vec::with_capacity(given.len());
                for (s, v) in given {
                    // A different identity in force is refused where the body is reached:
                    // the fold is undecided here. It is recorded in each body, since the
                    // written body of a function, in which nothing is in force, may have
                    // consumed the call's entry already.
                    if self.inst.env.get(s).is_some_and(|old| old != v) {
                        self.inst.undecided.push(*s);
                        continue;
                    }
                    let old = self.inst.env.insert(*s, v.clone());
                    let from = self.inst.provider.insert(*s, e.span);
                    saved.push((*s, old, from));
                }
                Some(Saved::Pushed(saved))
            }
            _ => None,
        }
    }

    /// Empties `env` for a body that takes no identity from around it.
    pub(super) fn clear_env(&mut self) -> Saved {
        self.inst.opaque += 1;
        Saved::Cleared(
            mem::take(&mut self.inst.env),
            mem::take(&mut self.inst.provider),
        )
    }

    /// Puts back what [`Self::enter_expr`] or [`Self::clear_env`] changed.
    pub(super) fn leave_expr(&mut self, saved: Saved) {
        match saved {
            Saved::Pushed(entries) => {
                for (s, old, from) in entries {
                    match old {
                        Some(v) => self.inst.env.insert(s, v),
                        None => self.inst.env.remove(&s),
                    };
                    match from {
                        Some(c) => self.inst.provider.insert(s, c),
                        None => self.inst.provider.remove(&s),
                    };
                }
            }
            Saved::Cleared(env, provider) => {
                self.inst.opaque -= 1;
                self.inst.env = env;
                self.inst.provider = provider;
            }
        }
    }

    /// The term of the declared function `id` called at `at`: its own kernel name, or for a
    /// top-level function whose calls decide folds ([`zedc_check::check::Info::split_needs`])
    /// the body made at the identities the call decides, each the checker's for this call or
    /// else the one the body being made holds. A call where any is decided by neither takes the
    /// written body and records the folds as undecided.
    // Complexity tradeoff: the identities of a call's folds are found by binary search in the
    // checker's sorted list, O(k log k) for a callee of k decided folds, against O(k²) for a
    // search of the list for each fold. A body is made once for each distinct list of
    // identities, found in a hash map, O(k) to hash the list.
    pub(super) fn fref(&mut self, id: usize, at: Span) -> Shared {
        Shared::new(Term::Var(self.fkernel(id, at)))
    }

    /// The kernel name [`Self::fref`] calls.
    pub(super) fn fkernel(&mut self, id: usize, at: Span) -> Arc<str> {
        let info = self.info;
        let Some(sites) = info.split_needs.get(&id) else {
            return self.names[id].clone();
        };
        if !self.inst.fns.contains_key(&id) {
            return self.names[id].clone();
        }
        let given = info.fold_calls.get(&at).map_or(&[][..], Vec::as_slice);
        let mut key = Vec::with_capacity(sites.len());
        let mut open = false;
        for s in sites {
            match given.binary_search_by_key(s, |(x, _)| *x) {
                Ok(i) => {
                    self.inst.consumed.insert((at, *s));
                    key.push(given[i].1.clone());
                }
                Err(_) => match self.env_identity(*s) {
                    Some(v) => key.push(v),
                    None => open = true,
                },
            }
        }
        if open {
            return self.names[id].clone();
        }
        let env: Env = sites.iter().copied().zip(key.iter().cloned()).collect();
        match self.inst.made.entry((id, key)) {
            Entry::Occupied(e) => e.get().clone(),
            Entry::Vacant(e) => {
                let name = &self.t.res.binders[id].name;
                let kernel: Arc<str> = format!("{name}@{}", self.inst.next).into();
                self.inst.next += 1;
                e.insert(kernel.clone());
                self.inst.queue.push((id, kernel.clone(), env));
                kernel
            }
        }
    }

    /// Makes each body [`Self::fref`] queued, and the bodies their calls queue in turn.
    /// Each binder of the function's statement other than the function's own is given a fresh
    /// kernel name while its body is elaborated, as kernel names are unique in the unit (stage
    /// `mix` and a default's `let` rely on it), then given back.
    // Complexity tradeoff: each body costs one elaboration of the function, O(s) for a
    // function of size s, and one search of the binders by start, O(log b); the bodies are
    // as many as the distinct lists of identities the calls decide, at most the calls. The
    // naive form, one copy of the elaborated body with its names renamed by a walk of the
    // term, would cost the same O(s) but must know every form of the kernel that binds a name.
    pub(super) fn make_instances(&mut self) {
        while let Some((id, kernel, env)) = self.inst.queue.pop() {
            let s = self.inst.fns[&id];
            let StmtKind::Function(f) = &s.kind else {
                unreachable!("`fns` holds function declarations")
            };
            if self.inst.by_start.is_empty() {
                let mut by_start: Vec<_> = (self.t.res.binders.iter().enumerate())
                    .map(|(i, b)| (b.span.start, b.span.end, i))
                    .collect();
                by_start.sort_unstable();
                self.inst.by_start = by_start;
            }
            let lo = (self.inst.by_start).partition_point(|&(start, ..)| start < s.span.start);
            let mut map: HashMap<Arc<str>, Arc<str>> = HashMap::new();
            let mut given_back = Vec::new();
            for k in lo..self.inst.by_start.len() {
                let (start, end, b) = self.inst.by_start[k];
                if start >= s.span.end {
                    break;
                }
                if end > s.span.end || b == id {
                    continue;
                }
                let fresh: Arc<str> =
                    format!("{}@{}", self.t.res.binders[b].name, self.inst.next).into();
                self.inst.next += 1;
                let old = mem::replace(&mut self.names[b], fresh.clone());
                map.insert(old.clone(), fresh);
                given_back.push((b, old));
            }
            let defaults: Vec<(usize, Term)> = (0..f.params.len())
                .filter_map(|j| Some((j, self.defaults.get(&(id, j))?.clone())))
                .collect();
            for (j, t) in &defaults {
                self.defaults.insert((id, *j), renamed(t, &map));
            }
            let reads = mem::take(&mut self.reads);
            // The body's identities came from its call, which took them ([`Self::fkernel`]):
            // no built-in call around the body provides them.
            let outer = mem::replace(&mut self.inst.env, env);
            let providers = mem::take(&mut self.inst.provider);
            let opaque = mem::replace(&mut self.inst.opaque, 0);
            let mark = self.inst.undecided.len();
            let body = self.body_term(f);
            let params: Vec<Arc<str>> = (f.params.iter())
                .map(|p| self.names[self.id(p.span, &p.name)].clone())
                .collect();
            let sites = self.inst.undecided.split_off(mark);
            self.inst.attribute([&kernel], sites);
            self.inst.env = outer;
            self.inst.provider = providers;
            self.inst.opaque = opaque;
            self.reads = reads;
            for (j, t) in defaults {
                self.defaults.insert((id, j), t);
            }
            for (b, old) in given_back {
                self.names[b] = old;
            }
            if let Some(body) = body {
                let first_order = self.info.tops.get(&f.name).is_some_and(|t| t.first_order());
                self.inst.bodies.push((
                    id,
                    Def {
                        name: kernel.to_string(),
                        kernel,
                        term: Shared::new(Term::Lam(params, Shared::new(body))),
                        first_order,
                    },
                ));
            }
        }
    }

    /// The refusals of the folds no body could take: each fold of a call the checker decided
    /// that no call's elaboration took ([`Self::fkernel`]), the folds `export` left undecided
    /// in the unit's export, which the unit always runs, and each fold left undecided in a
    /// definition the unit reaches, from every definition other than the written bodies of
    /// functions whose calls decide folds and the bodies made for them, and from every test
    /// row. A written body no call reaches is not run, so its folds need no identity.
    // Complexity tradeoff: one search of the definitions the unit reaches, each met once (a
    // visited set), O(t log t) for terms of size t in all with `stage::free`; it runs only when
    // a fold was left undecided. The naive form, a search from each root, costs O(roots × t).
    pub(super) fn check_instances(&mut self, defs: &[Def], tests: &[Test], export: Vec<Span>) {
        let info = self.info;
        let mut sites: BTreeSet<Span> = export.into_iter().collect();
        for (&call, folds) in &info.fold_calls {
            for &(s, _) in folds {
                if !self.inst.consumed.contains(&(call, s)) {
                    sites.insert(s);
                }
            }
        }
        if !self.inst.undecided_defs.is_empty() {
            let at: HashMap<&str, usize> = (defs.iter().enumerate())
                .map(|(i, d)| (&*d.kernel, i))
                .collect();
            let made: HashSet<&str> = self.inst.made.values().map(|k| &**k).collect();
            let written: HashSet<&str> = (info.split_needs.keys())
                .filter(|id| self.inst.fns.contains_key(id))
                .map(|&id| &*self.names[id])
                .collect();
            let mut seen = vec![false; defs.len()];
            let mut todo: Vec<usize> = Vec::new();
            for (i, d) in defs.iter().enumerate() {
                if !made.contains(&*d.kernel) && !written.contains(&*d.kernel) {
                    seen[i] = true;
                    todo.push(i);
                }
            }
            let mut reach = |names: BTreeSet<Arc<str>>, todo: &mut Vec<usize>| {
                for x in names {
                    if let Some(&i) = at.get(&*x)
                        && !mem::replace(&mut seen[i], true)
                    {
                        todo.push(i);
                    }
                }
            };
            for t in tests {
                reach(free(&t.check), &mut todo);
            }
            while let Some(i) = todo.pop() {
                if let Some(s) = self.inst.undecided_defs.get(&defs[i].kernel) {
                    sites.extend(s);
                }
                reach(free(&defs[i].term), &mut todo);
            }
        }
        for site in sites {
            let what = &info.split_folds[&site];
            self.errors.push(refusal(site, what));
        }
    }
}
