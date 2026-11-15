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
//! nested in `g`'s signature).
//!
//! What stays refused, as "not compiled yet": a fold whose identity no call decides where it
//! is elaborated (a function passed as a value, a nested function or any other lambda, whose
//! bodies take no identity from around them, a default that folds), a read where two
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
//! [`bodies`](super::bodies) the bodies made after the walk, which call the walk.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use zed_kernel::Value;
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
