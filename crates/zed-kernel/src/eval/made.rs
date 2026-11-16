//! The value a run gives when it may be a function or hold one ([`super::Evaluator::run_made`]): a
//! back end that runs one node of a program in the kernel takes back a family of functions a
//! `map` made, a `where` kept or a remap moved, as the kernel holds it (rows
//! FAIL-native-fam-result-holds-function and FAIL-machine-held-family; DESIGN.md step L1.17:
//! only a use that needs data, such as showing or `==`, is an error).
//!
//! A run's value lives in the run's machine, its closures pointing into the term run and into
//! environments the run made. [`Made`] is the same value apart from them: a list of nodes,
//! each part before what holds it, a value held twice being one node. A closure is its lambda,
//! the body shared with the term run, with the value of each name of its environment the body
//! may read, so the back end builds the closure's term again from the terms of those values.
//!
//! This file holds the value apart and what it is made of; the walk that takes a value of the
//! run apart, `Machine::made`, is in eval.rs beside the machine whose values it reads, so that
//! this file imports nothing from eval.rs and the two make no import cycle (step S.1f, row
//! S1F-kernel-eval-made-cycle).

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::term::walk::{Binds, Kid, kids};
use crate::term::{Prim, Shared, Term};
use crate::value::{Fields, HeldFamily, Value};

/// A value a run gives, functions and all: its nodes, each part before the value that holds
/// it, the value itself last. A value held at two places is one node, named by both.
#[derive(Clone, Debug)]
pub struct Made {
    /// The nodes, the value's own last.
    pub nodes: Vec<MadeNode>,
}

/// One node of a [`Made`].
#[derive(Clone, Debug)]
pub enum MadeNode {
    /// Data.
    Data(Value),
    /// A primitive used as a function.
    Prim(Prim),
    /// An input port read by lookup, by its name.
    Source(Arc<str>),
    /// A closure.
    Fun(MadeFun),
    /// A tuple, an atom or a family with a part that is no data, and the nodes of its parts in
    /// the order of the kernel's `Held`'s parts.
    Held(MadeShape, Vec<usize>),
}

/// A closure the kernel made: `params -> body`, where each name of `caps` that the body reads
/// is the value of its node.
#[derive(Clone, Debug)]
pub struct MadeFun {
    /// The lambda's parameters.
    pub params: Vec<Arc<str>>,
    /// The lambda's body, shared with the term the kernel ran.
    pub body: Shared,
    /// Each name of the closure's environment the body may read, in name order, and its node.
    pub caps: Vec<(Arc<str>, usize)>,
}

/// The closed term of a closure the kernel made, given its parameters, its body, the names of
/// its captures and the term of each capture in the order of `names`:
/// `params -> ((names…) -> body)(caps…)`. The captures are bound inside the lambda, so the
/// term gives its closure in one step, as a lambda does, and a closure that captures another
/// twice is not built twice; a call binds the captures, as a call of a closure the back end
/// made binds its own, O(captures). They are bound by one application, not a `let` each, so
/// no capture's term is read under another capture's name: a back end names the values it
/// binds outside a term (`\0cell k`), and a name of this closure's environment may be one of
/// those from an earlier run, standing for another value.
pub fn fun_term(params: &[Arc<str>], body: &Shared, names: &[Arc<str>], caps: Vec<Term>) -> Term {
    if caps.is_empty() {
        return Term::Lam(params.to_vec(), body.clone());
    }
    let inner = Term::Lam(names.to_vec(), body.clone());
    let body = Term::App(Shared::new(inner), caps);
    Term::Lam(params.to_vec(), Shared::new(body))
}

/// What a [`MadeNode::Held`] is.
#[derive(Clone, Debug)]
pub enum MadeShape {
    /// A tuple.
    Tuple,
    /// An atom: its name and its field names, sorted as [`Value::atom_named`] sorts them,
    /// empty for a payload by position.
    Atom(Arc<str>, Fields),
    /// A family whose entries at [`HeldFamily`]'s parts are the parts.
    Family(HeldFamily),
}

/// The names a lambda body reads, each once, sorted: R(body), every free name of the body and
/// perhaps more. The body's region (its parts outside its lambdas) is read once with a scope,
/// the count of each name the binders around the part in hand bind ([`kids`] gives each
/// binder's names, as the evaluator binds them). A part held in a node the region reaches once
/// is read under its one parent's scope; a node reached twice or more is read once, apart,
/// under no scope. A variable is kept unless its name is in scope, and a lambda `ps -> b`
/// adds R(b) less `ps` and less the names in scope at the lambda.
///
/// R holds every free name: a free occurrence of `x` is a path from the body to it on which
/// nothing binds `x`. The scope a part is read under holds only binders on the chain of
/// once-reached nodes above it, and every path to the part runs through that chain, so a name
/// in that scope is bound on every path; by induction on the nesting of lambdas, the same
/// holds of R(b). On a region with no shared node R is exact; at a node reached twice the
/// names the binders above it bind are kept, though bound, as the evaluator then binds a
/// name to a value that exists. R(body) is kept on the body ([`Shared::reads_memo`]), found
/// once for the life of the term, so each lambda body is read once whatever the number of
/// runs and closures made of it. R is a function of the body alone, so the memo is right
/// under whatever binds around the lambda, and the order the memos are found in does not
/// change them. Tests: `binder_tests` checks R against a walk of the tree per binder form, on
/// random terms, and at a node shared under every pair of binders (row
/// TEST-reads-binder-forms).
// Complexity tradeoff: the exact free names of each shared node, kept per node, cost O(n²) on a
// chain of n `let`s whose last body reads them all, and taking them along each path instead
// crosses a shared graph exponentially often. The former set was every variable of the body:
// it kept every name a `let`, a pattern or a `fam` binds inside the body, so a closure of a
// function whose body binds n names (`x * i` is elaborated to a `let` of `x`) looked up n
// names each time it was made, Θ(n²) for n test rows that each make it
// (FAIL-elab-rows-reaching-ratio); and its nested lambdas' bodies were walked again for each
// enclosing body and on each run, Θ(n²) per run for n nested lambdas
// (FAIL-map-nest-bench-ratio-again). Used: per lambda body, one pass counting the references
// to each shared node of the region and one pass reading it with the scope, O(its distinct
// parts + the names its binders bind), and per nested lambda O(r log p) for r names and p
// parameters from its memo; in all O(Σ over lambda bodies of (region + Σ r log p)), where a
// region shared by k lambda bodies is read k times. Tradeoff: a name bound above a node
// reached twice is kept (exact by the common part of the parents' scopes would need a meet of
// scopes per shared node), and the memo costs a cell on each shared node.
pub(super) fn reads(body: &Shared) -> Arc<[Arc<str>]> {
    if let Some(r) = body.reads_memo().get() {
        return r.clone();
    }
    // A lambda body to enter, or one whose nested lambdas' sets are all found, with the names
    // of its region and its nested lambdas. Terms are acyclic (a `Shared` is immutable once
    // built), so a body's `Exit` comes after every nested body entered from it has its memo.
    enum Job<'a> {
        Enter(&'a Shared),
        Exit(&'a Shared, Region<'a>),
    }
    let mut entered: HashSet<u64> = HashSet::new();
    let mut jobs = vec![Job::Enter(body)];
    while let Some(job) = jobs.pop() {
        match job {
            Job::Enter(b) => {
                if b.reads_memo().get().is_some() || !entered.insert(b.id()) {
                    continue;
                }
                let r = region(b);
                let lams = r.lams.clone();
                jobs.push(Job::Exit(b, r));
                jobs.extend(lams.into_iter().map(Job::Enter));
            }
            Job::Exit(b, r) => {
                let mut names: Vec<_> = scoped_names(b, &r.refs).into_iter().collect();
                names.sort();
                // Another thread may have set it first: R is a function of the term, so the
                // two sets are equal.
                let _ = b.reads_memo().set(names.into());
            }
        }
    }
    body.reads_memo()
        .get()
        .expect("the body's own `Exit` sets it")
        .clone()
}

/// A lambda body's region, its parts outside its lambdas: the number of references the region
/// makes to each node it reaches, and the bodies of its lambdas.
struct Region<'a> {
    refs: HashMap<u64, u32>,
    lams: Vec<&'a Shared>,
}

/// The region of `body` ([`Region`]), each node read once. [`kids`] lists every part, a
/// lattice `fix`'s join included (row CLOSURE-captures-read-only: a name only it reads was
/// missed).
fn region(body: &Shared) -> Region<'_> {
    let mut refs: HashMap<u64, u32> = HashMap::new();
    let mut lams = Vec::new();
    let mut stack: Vec<&Term> = vec![body];
    while let Some(t) = stack.pop() {
        if let Term::Lam(_, b) = t {
            lams.push(b);
            continue;
        }
        kids(t, |k, _| match k {
            Kid::Inline(u) => stack.push(u),
            Kid::Shared(s) => {
                let n = refs.entry(s.id()).or_insert(0);
                *n += 1;
                if *n == 1 {
                    stack.push(s);
                }
            }
        });
    }
    Region { refs, lams }
}

/// R(body) as [`reads`] defines it, given the references `refs` of its region and the sets of
/// its lambdas' bodies, each read from its memo.
fn scoped_names<'a>(body: &'a Shared, refs: &HashMap<u64, u32>) -> HashSet<Arc<str>> {
    // A part to read, or the names a binder binds over the part read between the two.
    enum Step<'a> {
        Read(&'a Term),
        Bind(Binds<'a>),
        Unbind(Binds<'a>),
    }
    let mut names: HashSet<Arc<str>> = HashSet::new();
    let mut scope: HashMap<&'a str, u32> = HashMap::new();
    // The nodes reached twice or more, each read once under no scope.
    let mut apart: Vec<&'a Term> = vec![body];
    let mut queued: HashSet<u64> = HashSet::new();
    let mut steps: Vec<Step<'a>> = Vec::new();
    let mut ps: Vec<&'a Arc<str>> = Vec::new();
    while let Some(root) = apart.pop() {
        debug_assert!(scope.is_empty(), "each binder is undone after its part");
        steps.push(Step::Read(root));
        while let Some(step) = steps.pop() {
            match step {
                Step::Bind(b) => b.each(|x| *scope.entry(&**x).or_insert(0) += 1),
                Step::Unbind(b) => b.each(|x| {
                    let n = scope.get_mut(&**x).expect("bound before");
                    *n -= 1;
                    if *n == 0 {
                        scope.remove(&**x);
                    }
                }),
                Step::Read(Term::Var(x)) => {
                    if !scope.contains_key(&**x) {
                        names.insert(x.clone());
                    }
                }
                Step::Read(Term::Lam(xs, l)) => {
                    let inner = l.reads_memo().get().expect("a nested body is found first");
                    ps.clear();
                    ps.extend(xs.iter());
                    ps.sort();
                    names.extend(
                        (inner.iter())
                            .filter(|y| !scope.contains_key(&***y) && ps.binary_search(y).is_err())
                            .cloned(),
                    );
                }
                Step::Read(t) => kids(t, |k, b| {
                    let u = match k {
                        Kid::Inline(u) => u,
                        Kid::Shared(s) if refs[&s.id()] == 1 => &**s,
                        Kid::Shared(s) => {
                            if queued.insert(s.id()) {
                                apart.push(s);
                            }
                            return;
                        }
                    };
                    // Popped in reverse: the names are bound, the part read, then unbound.
                    steps.push(Step::Unbind(b));
                    steps.push(Step::Read(u));
                    steps.push(Step::Bind(b));
                }),
            }
        }
    }
    names
}
