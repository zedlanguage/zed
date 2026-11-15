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
//! What stays refused, as "not compiled yet": a fold whose identity no call decides where it
//! is elaborated (a function passed as a value, a block's function named as a value at two
//! identities, a lambda other than one a built-in runs in place, whose bodies take no
//! identity from around them, a default that folds), a read where two
//! identities for one fold are in force (a `.map` at `f64` inside one at `int`, both folding
//! by one `top`), and a call whose decided folds are not all its callee's. Each such
//! fold is recorded where it is met ([`Instancing::undecided`]); the definitions it lands in
//! are refused when the unit reaches them, and a decided call no elaboration took is refused
//! at once ([`Elab::check_instances`](super::state::Elab::check_instances)).
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
    /// For each fold of `env` that a built-in call put there
    /// ([`Elab::enter_expr`](super::state::Elab::enter_expr)), that call's span.
    pub(super) provider: HashMap<Span, Span>,
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
}

#[cfg(test)]
thread_local! {
    /// In this crate's unit tests only: while set, [`Instancing::written_named`] records
    /// nothing, as a reference it missed would, so that
    /// [`Elab::check_dropped`](super::state::Elab::check_dropped) can be run on one.
    pub(super) static MISS_WRITTEN_NAMED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// The written body of a block's function that no term that runs names, left out of the block:
/// the function's declaration and the folds its written body left undecided.
pub(super) struct Dropped<'a> {
    pub(super) stmt: &'a Stmt,
    pub(super) sites: Vec<Span>,
}

impl<'a> Instancing<'a> {
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
            locals: Vec::new(),
            local_at: HashMap::new(),
            pending: Vec::new(),
            writing: Vec::new(),
            dropped: HashMap::new(),
        }
    }

    /// Starts the written body of the function `id` declared in a block by `stmt`, whose
    /// calls decide folds.
    pub(super) fn declare_local(&mut self, id: usize, stmt: &'a Stmt) {
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
        });
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
