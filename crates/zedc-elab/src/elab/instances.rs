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
//! while the call runs ([`IN_PLACE`](super::identities::IN_PLACE): `.map`, `.where`, …) is part
//! of the body around it: the identities that call decided, as for `m.map(r -> top(r))`
//! checked at `f64`, are in force in the lambda, and a fold under it, as in
//! `g(mm) = mm.map(r -> top(r))`, is decided by `g`'s calls (the checker searches the needs
//! nested in `g`'s signature). A function declared in a block takes a body for each list of
//! identities its calls decide too ([`Local`], REDUCE-generic-identity-rest); its bodies close
//! over the block's names, so they are made and bound in the block when its statements end
//! ([`Elab::place_locals`](super::state::Elab::place_locals)), and its written body is kept
//! only if a term that runs names it. A kept term that names a dropped written body, which a
//! reference [`Instancing::written_named`] missed would give, is refused at compile time
//! ([`Elab::check_dropped`](super::state::Elab::check_dropped),
//! PROOF-block-body-kept-when-named), never left to run with the name unbound.
//!
//! A function used as a value takes bodies the same way (REDUCE-generic-identity-values): a
//! name bound to such a function, `f = top`, stands for it ([`Instancing::alias`]); a lambda
//! bound to a name in a block, `f = x -> top(x)`, is a [`Local`] whose calls decide the folds
//! its written body leaves undecided; a function passed to a call that decides its folds and
//! whose result does not hold it, as `top` in `ap(top, m["a"])` or `x -> top(x)` there, is
//! the body made at that call's identities ([`Instancing::value_at`], `Info::escaping_calls`).
//! Where calls deciding one fold at two identities are both in force at a use, as in
//! `mi.map(q -> m.map(r -> (top(r), top(q))))`, the use takes the identity of the call that
//! checked it (`Info::fold_reads`, `Elab::env_identity`).
//!
//! What stays refused, as not supported by this zedc: a fold whose identity no call decides where
//! it is elaborated (a function the result of a call holds, run later at another identity, as
//! `p[1]` of `p = h3(x -> top(x), m["a"])` for `h3(f, y) = (f(y), f)`, which needs the
//! identity chosen when the program runs: the proof is at `check_instances`, and row
//! REDUCE-identity-closure-bodies holds the change that would compile it; a block's
//! function named as a value other than as an argument of such a call; a default that
//! folds), a use where calls of different identities for one fold are in force and none
//! or several of different identities checked it, and a call whose decided folds are not all
//! its callee's. Each such fold is recorded where it is met ([`Instancing::undecided`]); the
//! definitions it lands in are refused when the unit reaches them, and a decided call no
//! elaboration took is refused at once
//! ([`Elab::check_instances`](super::state::Elab::check_instances)).
//!
//! The work is in three files whose imports form no cycle (step S.1f): this one holds the
//! state, which [`state`](super::state) keeps in the elaborator and which imports nothing of
//! the elaborator; [`identities`](super::identities) the identities in force at each
//! expression and the kernel name of each call, which the walk calls; and
//! [`bodies`](super::bodies) the bodies of top-level functions made after the walk, which
//! call the walk. A block's function's bodies are made while the walk runs, by the walk
//! itself ([`walk`](super::walk): `place_locals`, `instance_body`), since making a body runs
//! the walk and the walk, at a block's end, makes bodies; `bodies` calls `instance_body`
//! there.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use zed_kernel::{Term, Value};
use zedc_stage::defs::Def;
use zedc_syntax::ast::Stmt;
use zedc_syntax::lex::Span;

/// The identities of the folds a body is made at, by fold.
pub(super) type Env = HashMap<Span, Option<Value>>;

/// The bodies made and to make, and the folds no call decided where they were met.
pub(super) struct Instancing<'a> {
    /// The identities the body being elaborated is made at; empty for a written body.
    pub(super) env: Env,
    /// Each body made or queued, by the function's binder and the identities of its
    /// `split_needs` in their order: its kernel name.
    pub(super) made: HashMap<(usize, Vec<Option<Value>>), Arc<str>>,
    /// The bodies to make: binder, kernel name, identities.
    pub(super) queue: Vec<(usize, Arc<str>, Env)>,
    /// The identities the calls around the expression being elaborated put in force for the
    /// code within them ([`Elab::enter_expr`](super::state::Elab::enter_expr)), by fold.
    pub(super) pushed: HashMap<Span, InForce>,
    /// The calls that checked each use of a fold whose calls decide it, by fold and use
    /// ([`zedc_check::check::Info::fold_reads`]), only those whose span holds the use's: no
    /// other call is in force at the use.
    pub(super) checked_by: HashMap<(Span, Span), Vec<Span>>,
    /// Each name bound by `=` to a function whose calls decide folds, or to another such name,
    /// as `f` of `f = top`, by its binder: the function's binder. A call of the name is a call
    /// of the function, and the binding is not made (REDUCE-generic-identity-values).
    pub(super) alias: HashMap<usize, usize>,
    /// Each name of such a function passed directly to a call that decides its folds and lets
    /// no function passed to it run after it returns, by the name's span: the call's span. The
    /// name stands for the body made at that call's identities.
    pub(super) value_at: HashMap<Span, Span>,
    /// Each name of a lambda bound in a block ([`Local`]) that a call calls, by the name's
    /// span: the call's span, whose identities choose the lambda's body.
    pub(super) callee_at: HashMap<Span, Span>,
    /// The entries of [`zedc_check::check::Info::fold_calls`] elaboration took, by call and
    /// fold: at a call of the function whose body runs the fold
    /// ([`Elab::fkernel`](super::state::Elab::fkernel)), or by a read of the fold that found
    /// the entry its call put in `env`.
    pub(super) consumed: HashSet<(Span, Span)>,
    /// The bodies of lambdas passed directly to a built-in call that applies them in place,
    /// whose folds take the identities that call decides
    /// ([`Elab::enter_expr`](super::state::Elab::enter_expr)), by span.
    pub(super) in_place: HashSet<Span>,
    /// The number of bodies being elaborated whose folds take no identity from around them
    /// ([`Elab::enter_expr`](super::state::Elab::enter_expr)); while it is above zero, no
    /// built-in call puts any in `env`.
    pub(super) opaque: usize,
    /// The folds met with no identity decided, since the last time they were attributed.
    pub(super) undecided: Vec<Span>,
    /// The folds no call decided in each definition, by kernel name.
    pub(super) undecided_defs: HashMap<Arc<str>, Vec<Span>>,
    /// Each function declared at the unit's top level, by its binder.
    pub(super) fns: HashMap<usize, &'a Stmt>,
    /// The binders by the start of their spans: start, end, binder; made at the first body.
    pub(super) by_start: Vec<(usize, usize, usize)>,
    /// The number the next fresh kernel name takes, `name@N`: above every number
    /// [`Elab::new`](super::state::Elab::new) gives, which is at most the number of binders.
    pub(super) next: usize,
    /// The bodies made, each with the binder of the function it is a body of.
    pub(super) bodies: Vec<(usize, Def)>,
    /// The functions declared in the blocks being elaborated whose calls decide folds, innermost
    /// last.
    pub(super) locals: Vec<Local<'a>>,
    /// The index in `locals` of each, by its binder.
    pub(super) local_at: HashMap<usize, usize>,
    /// The indices in `locals` whose queue holds a body to make.
    pub(super) pending: Vec<usize>,
    /// The indices in `locals` whose written bodies are being elaborated, innermost last.
    pub(super) writing: Vec<usize>,
    /// The written bodies dropped since no term that runs names them
    /// ([`Elab::place_locals`](super::state::Elab::place_locals)), by kernel name; a kept term
    /// that names one is refused ([`Elab::check_dropped`](super::state::Elab::check_dropped)).
    pub(super) dropped: HashMap<Arc<str>, Dropped<'a>>,
}

/// A function declared in a block whose calls decide the identities of its folds, as
/// `h(positional q) = top(q)` in `{ h(…) = …; (h(mi["a"]), h(m["a"])) }`. Its bodies close over
/// the block's names, so they are made when the block's statements are elaborated and bound
/// in the block after the written body, one for each distinct list of identities its calls in
/// that elaboration of the block decide.
pub(super) struct Local<'a> {
    pub(super) id: usize,
    pub(super) stmt: &'a Stmt,
    /// Each body made or queued, by the identities of its `split_needs` in their order.
    pub(super) made: HashMap<Vec<Option<Value>>, Arc<str>>,
    /// The bodies to make: kernel name, identities.
    pub(super) queue: Vec<(Arc<str>, Env)>,
    /// The bodies made, in the order made.
    pub(super) done: Vec<(Arc<str>, Term)>,
    /// Whether a term that is run if the block is run names the written body: a call no
    /// identity decided, or the function as a value.
    pub(super) used: bool,
    /// The functions declared before this one, in this block or around it, whose written
    /// bodies this one's written body names: run if this one's is.
    pub(super) names: Vec<usize>,
    /// The folds the written body left undecided, refused only if `used`.
    pub(super) written: Vec<Span>,
    /// The entry of `local_at` for the binder before this one.
    pub(super) prev: Option<usize>,
    /// For a lambda bound to a name, as `f = x -> top(x)`: the length of
    /// [`Instancing::undecided`] when its written body started, and once it ends, the folds
    /// that body left undecided, sorted, each once, which its calls decide in place of
    /// [`zedc_check::check::Info::split_needs`], which holds declared functions only. None
    /// for a declared function.
    pub(super) from: usize,
    pub(super) key: Option<Vec<Span>>,
}

#[cfg(test)]
thread_local! {
    /// In this crate's unit tests only: while set, [`Instancing::written_named`] records
    /// nothing, as a reference it missed would, so that
    /// [`Elab::check_dropped`](super::state::Elab::check_dropped) can be run on one.
    pub(super) static MISS_WRITTEN_NAMED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// The calls in force around the expression being elaborated that decide one fold
/// ([`Instancing::pushed`]). Calls are entered and left in nested order.
// Complexity tradeoff: O(1) expected to enter or leave a call and to find the identity of a
// call in force, and each call is taken at most once while in force ([`InForce::take`]), so a
// use costs O(c) for the c calls that checked it, whatever the depth d of the calls in force.
// The naive form, a stack of (call, identity) searched at each use, costs O(d) per use, so
// O(d²) for a nest of d `.map` calls each reading the fold (measured 10.6x at 8n, depth 50 to
// 400, in instructions).
#[derive(Default)]
pub(super) struct InForce {
    /// Each call's identity, by call.
    at: HashMap<Span, Option<Value>>,
    /// The calls not yet taken, by identity, each list in the order entered. Keyed by the
    /// value's hash (`impl Hash for Value`, an assumption documented there): were two equal
    /// identities to hash apart, a call would stay untaken and `check_instances` refuse the
    /// program, not run it at a wrong identity.
    open: HashMap<Option<Value>, Vec<Span>>,
}

impl InForce {
    /// Puts the call `c` in force, at identity `v`.
    pub(super) fn enter(&mut self, c: Span, v: Option<Value>) {
        self.open.entry(v.clone()).or_default().push(c);
        self.at.insert(c, v);
    }

    /// Ends the call `c`, the last entered of those in force. Whether none is left.
    pub(super) fn leave(&mut self, c: Span) -> bool {
        let v = self
            .at
            .remove(&c)
            .expect("a call's entry stays in force until it is left");
        // Calls nest, so `c` is the last of its list if no use took it.
        if let Some(open) = self.open.get_mut(&v)
            && open.last() == Some(&c)
        {
            open.pop();
        }
        self.at.is_empty()
    }

    /// The identity of the call `c`, if it is in force.
    pub(super) fn get(&self, c: &Span) -> Option<&Option<Value>> {
        self.at.get(c)
    }

    /// Takes the calls in force at identity `v` not taken before: each is taken once.
    pub(super) fn take(&mut self, v: &Option<Value>) -> Vec<Span> {
        self.open.get_mut(v).map(std::mem::take).unwrap_or_default()
    }
}

/// The written body of a block's function that no term that runs names, left out of the block:
/// the function's declaration and the folds its written body left undecided.
pub(super) struct Dropped<'a> {
    pub(super) stmt: &'a Stmt,
    pub(super) sites: Vec<Span>,
}

impl<'a> Instancing<'a> {
    pub(super) fn new(next: usize, fold_reads: &HashSet<(Span, Span, Span)>) -> Self {
        // Only the entries whose call holds the read in its text are kept. Proof that no
        // other call is ever in force at the read, so nothing it could decide is lost:
        // `pushed` gains entries only in `Elab::enter_expr` at a call `e`, which also pushes
        // `Frame::Env`, and loses them when that frame runs; `Elab::run` drains its stack
        // with no early exit, failures included, so the frame always runs, after the jobs of
        // `e`'s subexpressions only, whose spans lie in `e`'s. Every walk of other text in
        // between starts with `pushed` empty, case by case: a lambda not run in place
        // (`Elab::clear_env` in `enter_expr`); a block function's declaration (`clear_env`
        // in `Elab::stmt`); a body made at a call, of a function, an alias of one, a function
        // value or a bound lambda (`Elab::instance_body` takes `pushed`). A lambda run in
        // place is an argument of the call around it. With no split fold `enter_expr` never
        // runs, and `pushed` stays empty.
        let mut checked_by: HashMap<(Span, Span), Vec<Span>> = HashMap::new();
        for &(call, site, read) in fold_reads {
            if call.start <= read.start && read.end <= call.end {
                checked_by.entry((site, read)).or_default().push(call);
            }
        }
        Instancing {
            env: HashMap::new(),
            made: HashMap::new(),
            queue: Vec::new(),
            pushed: HashMap::new(),
            checked_by,
            alias: HashMap::new(),
            value_at: HashMap::new(),
            callee_at: HashMap::new(),
            consumed: HashSet::new(),
            in_place: HashSet::new(),
            opaque: 0,
            undecided: Vec::new(),
            undecided_defs: HashMap::new(),
            fns: HashMap::new(),
            by_start: Vec::new(),
            next,
            bodies: Vec::new(),
            locals: Vec::new(),
            local_at: HashMap::new(),
            pending: Vec::new(),
            writing: Vec::new(),
            dropped: HashMap::new(),
        }
    }

    /// Starts the written body of the function `id` declared in a block by `stmt`, whose
    /// calls decide folds, or of the lambda `stmt` binds to `id`.
    pub(super) fn declare_local(&mut self, id: usize, stmt: &'a Stmt) {
        let from = self.undecided.len();
        let i = self.locals.len();
        let prev = self.local_at.insert(id, i);
        self.writing.push(i);
        self.locals.push(Local {
            id,
            stmt,
            made: HashMap::new(),
            queue: Vec::new(),
            done: Vec::new(),
            used: false,
            names: Vec::new(),
            written: Vec::new(),
            prev,
            from,
            key: None,
        });
    }

    /// Ends the written body of the lambda `stmt` binds, if it is a block's [`Local`] being
    /// written. Its calls decide the folds it left undecided, which are refused only if the
    /// written body is named; with none left undecided it is no [`Local`], and the binding
    /// stays as written.
    pub(super) fn end_bound(&mut self, stmt: &Stmt) {
        let Some(&i) = self.writing.last() else {
            return;
        };
        if !std::ptr::eq(self.locals[i].stmt, stmt) {
            return;
        }
        self.writing.pop();
        let mut sites = self.undecided.split_off(self.locals[i].from);
        zed_collections::sorted::sort_dedup(&mut sites);
        if sites.is_empty() {
            // The block's own functions declared inside the lambda were placed when their
            // blocks ended, so it is the last.
            assert_eq!(
                i + 1,
                self.locals.len(),
                "a lambda's body ends after its blocks"
            );
            let l = self.locals.pop().expect("the lambda's entry");
            match l.prev {
                Some(p) => self.local_at.insert(l.id, p),
                None => self.local_at.remove(&l.id),
            };
            // The written bodies it names are named where it is written.
            for j in l.names {
                let id = self.locals[j].id;
                self.written_named(id);
            }
            return;
        }
        self.locals[i].key = Some(sites.clone());
        self.locals[i].written = sites;
    }

    /// Ends the written body of the block's function `id`, if its body is the one being
    /// elaborated, keeping the folds it left undecided (`sites`) until the block ends; else
    /// gives `sites` back.
    pub(super) fn end_written(&mut self, id: usize, sites: Vec<Span>) -> Option<Vec<Span>> {
        match self.writing.last() {
            Some(&i) if self.locals[i].id == id => {
                self.writing.pop();
                self.locals[i].written = sites;
                None
            }
            _ => Some(sites),
        }
    }

    /// Records that the term being elaborated names the written body of the block's function
    /// `id`, if it is one. Within its own written body that is recursion, which runs nothing
    /// new; within the written body of a function declared after it, that function names it,
    /// and runs it if it is run; anywhere else, within a function declared inside its own
    /// body among them, it is run if the block is.
    pub(super) fn written_named(&mut self, id: usize) {
        #[cfg(test)]
        if MISS_WRITTEN_NAMED.get() {
            return;
        }
        let Some(&i) = self.local_at.get(&id) else {
            return;
        };
        match self.writing.last() {
            Some(&j) if j == i => {}
            Some(&j) if j > i => self.locals[j].names.push(i),
            _ => self.locals[i].used = true,
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
