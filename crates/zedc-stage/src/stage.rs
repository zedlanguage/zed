//! Staging (DESIGN.md sec:staging, step L1.28): which terms the build evaluates, and when
//! the build specializes a function on the values of a parameter.
//!
//! A term is a build-stage term when every name it reads is a build-stage definition or a
//! prelude word and it reads no port; a port input and a function parameter are run-stage.
//! `mix` evaluates the demanded build-stage terms to literals and leaves the rest to run.
//! A term is demanded when the residual program or a test reads it, so a definition nothing
//! reads is never evaluated. A demanded build-stage term is evaluated only when its form
//! shows that it ends ([`ends`], docs/thresholds.md, replacement 6), with no fuel; otherwise,
//! or when its evaluation fails, it is left to run whole, where a failure is reported in the
//! ordinary way.
//!
//! The Trick: `split` specializes a function on a run-stage parameter only when the
//! parameter's domain is finite, `int[0..=256]` but not `int`, and only on the values of the
//! domain that the program's static calls pass it (docs/thresholds.md, replacement 7): at
//! most one per call site, so the code grows at most linearly in the program. Each value gets
//! a copy of the body mixed with the parameter known, and the general body stays as the last
//! arm.

use std::borrow::Cow;
use std::cell::OnceCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use zed_kernel::digest::DigestMap;
use zed_kernel::text;
use zed_kernel::types::{Type, defs as printed};
use zed_kernel::{
    Evaluator, Global, Globals, KernelError, Lookup, Pattern, Shared, Term, Value, World,
};

use crate::defs::{Def, Unit};
use zedc_base::interp;

/// When a term is evaluated.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Stage {
    /// By the build.
    Build,
    /// By the run.
    Run,
}

/// What `mix` did.
#[derive(Clone, Default, PartialEq, Debug)]
pub struct Report {
    /// The definitions the build evaluated, by source name.
    pub built: Vec<String>,
    /// The definitions nothing demanded, which the build did not evaluate.
    pub unread: Vec<String>,
    /// The build-stage terms left to run, each with why: a part held in a node and reached
    /// under the same bindings of its names from many places is listed once. Each entry holds
    /// the term, its parts still shared, not its text. `print::pretty_in` writes it for a user,
    /// each shared part once, in O(n log n) for n distinct parts; `Display` and `Debug` are for
    /// debugging and label a shared part that reads a name bound in two places (`#1=`).
    pub left: Vec<(Shared, String)>,
    /// The definitions, by kernel name, that the roots reach as written only through an arm of
    /// an `if` the build does not take: one whose condition the build evaluated to the other
    /// arm's `bool`, or to an atom, which takes neither arm. A definition the build evaluates,
    /// or one whose run a cut read keeps (`keep_cut_reads`), is reached.
    pub untaken: BTreeSet<Arc<str>>,
}

/// The names `t` reads and does not bind. The term is read as the graph of its distinct parts:
/// a part held in one [`Shared`] node reached from two places is read once (`Frees`), and
/// the parts still to read wait on a heap stack, so a deep term does not grow the thread's
/// stack.
// Complexity tradeoff: naive version, every term read through `Frees`, whose maps, sets and
// memo of shared nodes are made and dropped for each call, about 13,000 instructions for a
// test such as `n > 3` (COMPLEXITY.md row PA-bind-cost). Used: a term built of names,
// literals, primitives and `if`s alone, which binds no name, is read into the set at once,
// each shared node once (a set of the node ids met), O(s log s) for `s` distinct parts; any
// other term goes through `Frees`, after the parts read before its first other form, at
// most O(s log s) more. Test:
// `l01_39_reduced_product::deep_let::the_arms_of_a_deep_block_scale`.
pub fn free(t: &Term) -> BTreeSet<Arc<str>> {
    if let Some(names) = free_of_primitives(t) {
        return names;
    }
    let mut f = Frees::default();
    let s = f.summary(Part::inline(t));
    f.names_in(s.free).into_iter().cloned().collect()
}

/// The names `t` reads, when it is built of names, literals, primitives and `if`s alone: then
/// it binds no name, so each name it holds is free, and a node shared by two of its parts
/// reads the same names from each, so it is read once. `None` when it holds any other form.
fn free_of_primitives(t: &Term) -> Option<BTreeSet<Arc<str>>> {
    let mut out = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut todo = vec![t];
    while let Some(t) = todo.pop() {
        match t {
            Term::Var(x) => {
                out.insert(x.clone());
            }
            Term::Lit(_) | Term::PrimFn(_) | Term::Read(_) => {}
            Term::Prim(_, args) => todo.extend(args),
            Term::If(c, a, b) => todo.extend(
                [c, a, b]
                    .into_iter()
                    .filter(|s| seen.insert(s.id()))
                    .map(|s| &**s),
            ),
            _ => return None,
        }
    }
    Some(out)
}

impl Unit {
    /// `body` under the definitions it reaches, each a let, in the unit's order. For many
    /// terms of one unit, make its [`Cones`] once.
    pub fn close(&self, body: Term) -> Term {
        Cones::new(self).close(body)
    }

    /// The definition of source name `name`, closed over the others.
    pub fn get(&self, name: &str) -> Option<Term> {
        let d = self.defs.iter().find(|d| d.name == name)?;
        Some(self.close(Term::Var(d.kernel.clone())))
    }
}

/// The definitions each term of a unit reaches, from an index of the unit made once: each
/// kernel name's definition, and the definitions each definition reads, found when first
/// needed. A term's cone then costs the definitions in it, not a pass over the unit, and
/// closing a term over its cone shares each definition's term rather than copying it.
// Complexity tradeoff (COMPLEXITY.md F9, F41): the naive form closes each test row over the
// whole unit (`Unit::close` per row), O(rows × unit), and copies each definition's term into
// the row's lets and prints it into the row's key, O(rows × reached size). The index here is
// built once, O(definitions); each definition's reads are found once, when first asked, and
// its key number once; a row's cone is a worklist over the definitions it reaches, with a
// visited set, and its lets share the definitions' terms (`Def.term` is an `Arc`). Memory:
// one entry per definition for the map, its reads and its number, kept while the index lives.
pub struct Cones<'u> {
    unit: &'u Unit,
    by_kernel: HashMap<&'u str, usize>,
    /// The positions of the definitions each definition reads.
    reads: Vec<OnceCell<Vec<usize>>>,
    /// The number a query database gave each definition's text, for a query key.
    numbers: Vec<OnceCell<u64>>,
    /// The stamp of that database.
    db: OnceCell<u64>,
}

impl<'u> Cones<'u> {
    /// The index of `unit`.
    pub fn new(unit: &'u Unit) -> Self {
        Cones {
            unit,
            by_kernel: unit
                .defs
                .iter()
                .enumerate()
                .map(|(i, d)| (&*d.kernel, i))
                .collect(),
            reads: unit.defs.iter().map(|_| OnceCell::new()).collect(),
            numbers: unit.defs.iter().map(|_| OnceCell::new()).collect(),
            db: OnceCell::new(),
        }
    }

    /// The positions of the definitions of the names `t` reads.
    fn positions(&self, t: &Term) -> impl Iterator<Item = usize> {
        free(t)
            .into_iter()
            .filter_map(|x| self.by_kernel.get(&*x).copied())
    }

    /// The positions of the definitions the definition at position `i` reads, found when
    /// first asked.
    pub fn reads(&self, i: usize) -> &[usize] {
        self.reads[i].get_or_init(|| self.positions(&self.unit.defs[i].term).collect())
    }

    /// The definitions `roots` read, and those they read in turn: their positions in the
    /// unit, in its order.
    pub fn reach(&self, roots: &[&Term]) -> Vec<usize> {
        let mut seen = BTreeSet::new();
        let mut todo: Vec<usize> = roots.iter().flat_map(|t| self.positions(t)).collect();
        while let Some(i) = todo.pop() {
            if seen.insert(i) {
                todo.extend(self.reads(i));
            }
        }
        seen.into_iter().collect()
    }

    /// The definitions `roots` reach, in the unit's order.
    pub fn defs(&self, roots: &[&Term]) -> impl Iterator<Item = &'u Def> + use<'u> {
        let unit = self.unit;
        self.reach(roots).into_iter().map(move |i| &unit.defs[i])
    }

    /// The number of the definition at position `i` in the query database of stamp `db`:
    /// what `number` gives its text, its kernel name and its term as `Debug` prints them,
    /// asked once. The numbers are those of one database, so a [`Cones`] is read with one.
    pub fn number(&self, i: usize, db: u64, number: impl FnOnce(&str) -> u64) -> u64 {
        let first = *self.db.get_or_init(|| db);
        assert_eq!(
            first, db,
            "the definitions of a unit are numbered by the one query database that met them"
        );
        *self.numbers[i].get_or_init(|| {
            let d = &self.unit.defs[i];
            number(&format!("{}={:?}", d.kernel, d.term))
        })
    }

    /// `body` under the definitions it reaches, each a let, in the unit's order: each after
    /// those it uses, as in the unit. Each let shares its definition's term.
    pub fn close(&self, body: Term) -> Term {
        self.close_with(body, None)
    }

    /// `body` closed as [`Cones::close`] closes it, with the definition at position `i` bound
    /// to `term` when `swap` is `Some((i, term))` (step L25.8, a mutant). `term` must read
    /// the names the definition reads, as a mutant's term does, so the cone is the same.
    pub fn close_with(&self, body: Term, swap: Option<(usize, &Shared)>) -> Term {
        let reach = self.reach(&[&body]);
        reach.into_iter().rev().fold(body, |body, i| {
            let d = &self.unit.defs[i];
            let term = match swap {
                Some((j, term)) if j == i => term.clone(),
                _ => d.term.clone(),
            };
            Term::Let(d.kernel.clone(), term, Shared::new(body))
        })
    }
}

/// The names `p` binds, left to right, borrowed from it.
fn pattern_names(p: &Pattern) -> Vec<&Arc<str>> {
    let mut out = Vec::new();
    let mut todo = vec![p];
    while let Some(p) = todo.pop() {
        match p {
            Pattern::Bind(x) => out.push(x),
            Pattern::Atom(_, ps) | Pattern::Tuple(ps) => todo.extend(ps.iter().rev()),
            Pattern::Fields(_, fs) => todo.extend(fs.iter().rev().map(|(_, p)| p)),
            _ => {}
        }
    }
    out
}

/// Whether `t` is shown to end by its form (docs/thresholds.md, replacement 6): it has no
/// `fix` or `gen`, and every function it calls, or hands to a family operation, is a
/// primitive, a lambda whose body ends, or a name a `let` binds to one. A `let` binds a name
/// only in its body, so such calls nest no deeper than the term; a call through a parameter
/// or a pattern variable, as in `w(w)`, is not shown to end. Free names are prelude words,
/// which are primitives.
///
/// The term is read as the graph of its distinct parts: a part shared by two places (one
/// [`Shared`] node reached twice, known by its id) is read once, so the time is near the
/// number of distinct parts, not the size of the term unshared (COMPLEXITY.md row ENDS; read
/// as a tree, a chain of k `if`s whose two arms hold one shared part cost O(2^k); the reads
/// kept by id cost one entry per distinct part). Each part is read once whatever
/// names are bound around it: what it needs of them is the set of names it calls that must
/// each be free or bound by `let` to a function that ends (`Needs`), and the binder of a
/// name reads that set. A part shared under two bindings of a name it calls so gives each
/// place its own answer.
// Complexity tradeoff: a term that ends but whose form does not show it (recursion, `fix`,
// `gen`, a call through a parameter) is treated as possibly not ending: the build stage
// leaves it to run time ("its form does not show that it ends"), and enumeration and `@exact`
// skip it. Why: whether a term ends is undecidable, and running it under a step count would
// switch behavior at a size. Trigger: any of those forms in the term or in a function it
// calls. Tests:
// `l01_28_staging::mix::a_term_whose_form_does_not_show_it_ends_is_left_to_run`,
// `l01_28_staging::mix::a_term_whose_form_shows_it_ends_is_built_with_no_fuel`.
// COMPLEXITY.md row C20 (docs/thresholds.md replacement 6). A complete solution cannot
// exist; a stronger sound one would add a termination proof by decreasing measures
// (size-change termination, PSPACE-complete in the call graph).
pub fn ends(t: &Term) -> bool {
    Reader::default().read(Part::inline(t)).is_some()
}

/// What a part of a term needs of the names bound around it to end: `None` when no binding
/// makes it end, otherwise the set of names it calls that must each be free (a prelude word) or
/// bound by `let` to a function that ends. A name bound by a lambda, a pattern or a family is
/// not known to be such a function, so a binder of a name in the set gives `None`.
type Needs = Option<Set>;

/// A name's number among the names of one term.
type Name = u32;

/// The reading of one term by [`ends`]: each distinct part numbered once, in an order that puts
/// a part after its own parts, with what it needs.
#[derive(Default)]
struct Reader {
    /// What each part needs, by its number.
    needs: Vec<Needs>,
    /// The number of each part held in a [`Shared`] node, by the node's id
    /// ([`Shared::id`]: copies of a node share it and no other node has it, the way
    /// [`zed_kernel::Items`] and [`zed_kernel::Family`] are known by theirs). A part shared by
    /// two places is one node reached twice, so it is read once. A part held inline (an
    /// argument, a match arm, the root) has one place, inside the one part that holds it, and
    /// is read once with that part. What a part needs depends on the part alone, so a reader
    /// kept across readings ([`Mixer::reader`]) reads each node once over all of them: an id is
    /// drawn once and never given to another node, and a node changed in place takes a new one
    /// ([`Shared::make_mut`]), so an id it holds names the same part even after the node is
    /// freed.
    ///
    /// The numbers are given in the order the parts are read, which depends only on the term's
    /// structure and sharing: never on the ids' values, which follow the order the nodes were
    /// built in, nor on addresses (tests
    /// `l01_28_staging::ends::three_allocation_orders_read_alike` and
    /// `l01_28_staging::ids::two_build_orders_read_and_stage_alike`).
    ///
    /// A node's id is the only key that sees sharing without an address: occurrence ids from
    /// one walk, as `zir::lower::Places` gives, cannot tell a part shared by both arms of `k`
    /// nested `if`s from its unshared copy, which has `2^k` places, and on that copy every
    /// place must be read, since a `fix` at any one of them changes the answer. Measured
    /// (negative controls, a reader keyed by occurrence ids): ADDR-stage, 1.0, 6.8, 23.7, 63.6,
    /// 256 and 1235 ms at k = 10 to 20; TERM-id, see COMPLEXITY.md row K44.
    ids: DigestMap<u64, usize>,
    /// For the test hook [`reading`] only: the numbers of the parts each part reads, by its
    /// number, in the order [`each_part`] gives them.
    reads: Option<Vec<Vec<usize>>>,
    /// The number of each name, in the order read: keyed by the program's names, so it keeps
    /// the seeded hasher ([`DigestMap`]).
    names: HashMap<Arc<str>, Name>,
    /// Each name, by its number.
    named: Vec<Arc<str>>,
    sets: Sets,
}

/// A part of a term to be read: the term, and the [`Shared`] node that holds it,
/// when one does.
#[derive(Clone, Copy)]
struct Part<'t> {
    term: &'t Term,
    node: Option<&'t Shared>,
}

impl<'t> Part<'t> {
    /// The part held in the node `s`.
    fn held(s: &'t Shared) -> Self {
        Part {
            term: s,
            node: Some(s),
        }
    }

    /// The part `t`, held inline by the one part that holds it.
    fn inline(t: &'t Term) -> Self {
        Part {
            term: t,
            node: None,
        }
    }
}

/// Test hook: the reading of `t` by [`ends`], each part in the order of its number, with its
/// answer (`None`, it never ends, or the number of the set of names it needs) and the numbers
/// of the parts it reads, in the order `each_part` gives them.
pub fn reading(t: &Term) -> Vec<(Option<u32>, Vec<usize>)> {
    let mut r = Reader {
        reads: Some(Vec::new()),
        ..Reader::default()
    };
    r.read(Part::inline(t));
    let reads = r.reads.unwrap_or_default();
    r.needs.into_iter().zip(reads).collect()
}

impl Reader {
    /// What `root` needs. The parts are read with an explicit stack, each after its own parts,
    /// and each part held in a node only the first time the node is reached.
    fn read(&mut self, root: Part<'_>) -> Needs {
        // A part to read, with `None`; or a part whose `k` parts are on their way, with `k`.
        let mut todo = vec![(root, None)];
        // The numbers of the parts read and not yet taken by the part that reads them: a
        // part's own parts end up on top, in the reverse of the order they were put on `todo`.
        let mut done: Vec<usize> = Vec::new();
        let mut parts = Vec::new();
        let mut got = Vec::new();
        while let Some((p, count)) = todo.pop() {
            let Some(k) = count else {
                if let Some(&i) = p.node.and_then(|s| self.ids.get(&s.id())) {
                    done.push(i);
                    continue;
                }
                each_part(p.term, &mut parts);
                todo.push((p, Some(parts.len())));
                todo.extend(parts.drain(..).map(|q| (q, None)));
                continue;
            };
            let from = done.len() - k;
            got.clear();
            got.extend(done[from..].iter().rev().map(|&i| self.needs[i]));
            let needs = self.needs_of(p.term, &got);
            let n = self.needs.len();
            self.needs.push(needs);
            if let Some(s) = p.node {
                self.ids.insert(s.id(), n);
            }
            if let Some(reads) = &mut self.reads {
                reads.push(done[from..].iter().rev().copied().collect());
            }
            done.truncate(from);
            done.push(n);
        }
        let root = done.pop().expect("the root, read");
        self.needs[root]
    }

    fn name(&mut self, x: &Arc<str>) -> Name {
        if let Some(&n) = self.names.get(x) {
            return n;
        }
        let n = self.names.len() as Name;
        self.names.insert(x.clone(), n);
        self.named.push(x.clone());
        n
    }

    /// The names in the set `s`.
    fn names_in(&self, s: Set) -> impl Iterator<Item = &Arc<str>> {
        let members = self.sets.members(s).into_iter();
        members.map(|x| &self.named[x as usize])
    }

    /// The names the lambda `k`, called, calls by name, when its form shows that a call ends
    /// once each of them ends; `None` when no binding of them makes it end.
    ///
    /// Invariant (item STAGE-stub-called): the answer is `None` when the body of `k` calls a
    /// name bound inside `k` (a parameter, a pattern variable or a family's key), calls
    /// anything but a primitive, a lambda or a name (the result of a call, an `if`), or holds a
    /// `fix` or a `gen`. [`Mixer::shown`] sets `call_ends` and [`Mixer::stub`] gives a stub from
    /// this answer alone, so a function with a stub calls only prelude words, lambdas and
    /// functions with stubs, and never a function handed to it ([`Port::function`]): this is
    /// why each run of [`fill`] ends. A stub of `w = (f) -> f(f)` would make `w(w)` ask its own
    /// port at its own token without end. Tests that fail when this reading admits such a
    /// function:
    /// `l01_28_staging::cone::calls_at_float_zeros_and_at_functions_give_what_they_give_as_written`
    /// (through the parameter of `apply`, from seed 2),
    /// `l01_28_staging::cone::calls_through_a_parameter_a_pattern_a_result_or_a_key_are_left_to_run`
    /// (each of the four ways), and
    /// `l01_28_staging::mix::a_term_whose_form_does_not_show_it_ends_is_left_to_run` (the build
    /// of `w(w)` no longer ends).
    fn called(&mut self, k: &Shared) -> Option<Vec<Arc<str>>> {
        let needs = self.read(Part::held(k))?;
        Some(self.names_in(needs).cloned().collect())
    }

    /// What a term needs whose parts need `a` and `b`: both.
    fn and(&mut self, a: Needs, b: Needs) -> Needs {
        Some(self.sets.union(a?, b?))
    }

    /// What `t` needs, given what its parts need, in the order [`each_part`] gives them.
    fn needs_of(&mut self, t: &Term, parts: &[Needs]) -> Needs {
        let mut parts = parts.iter().copied();
        let mut part = move || parts.next().expect("each part `each_part` gives, read");
        match t {
            Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => Some(EMPTY),
            Term::Fix { .. } | Term::Gen { .. } => None,
            Term::Lam(ps, _) => {
                let body = part();
                self.under(ps, body)
            }
            Term::App(f, args) => {
                let mut out = self.callee(f, &mut part);
                for _ in args {
                    out = self.and(out, part());
                }
                out
            }
            Term::Prim(_, args) => {
                let mut out = Some(EMPTY);
                for _ in args {
                    out = self.and(out, part());
                }
                out
            }
            Term::Let(x, e, _) => {
                let (bound, mut body) = (part(), part());
                // A lambda bound and never called need not end; any other binding is evaluated.
                let evaluated = match &**e {
                    Term::Lam(..) => Some(EMPTY),
                    _ => bound,
                };
                let x = self.name(x);
                if let Some(rest) = body.and_then(|b| self.sets.remove(b, x)) {
                    let callee = self.callee(e, &mut || bound);
                    body = self.and(Some(rest), callee);
                }
                self.and(body, evaluated)
            }
            Term::If(..) => {
                let (c, a, b) = (part(), part(), part());
                let ca = self.and(c, a);
                self.and(ca, b)
            }
            Term::Match(_, arms) => {
                let mut out = part();
                for (p, _) in arms {
                    let arm = self.under(&binds(p), part());
                    out = self.and(out, arm);
                }
                out
            }
            Term::Fam { var, .. } => {
                let (domain, body) = (part(), part());
                let body = self.under(std::slice::from_ref(var), body);
                self.and(domain, body)
            }
            Term::Reindex { kf, vf, .. } => {
                let family = part();
                let (k, v) = (self.callee(kf, &mut part), self.callee(vf, &mut part));
                let kv = self.and(k, v);
                self.and(family, kv)
            }
            Term::Discard { sel, .. } => {
                let family = part();
                let sel = self.callee(sel, &mut part);
                self.and(family, sel)
            }
            Term::Fold { op, identity, .. } => {
                let family = part();
                let op = self.callee(op, &mut part);
                let out = self.and(family, op);
                match identity {
                    Some(_) => {
                        let identity = part();
                        self.and(out, identity)
                    }
                    None => out,
                }
            }
            Term::Push(..) => part(),
        }
    }

    /// What `f`, in the position of a function called, needs to be one that ends: a primitive
    /// ends, a lambda when its body does (`lambda` gives what the lambda, a part read, needs),
    /// a name when it is free or bound to one that ends.
    fn callee(&mut self, f: &Term, lambda: &mut impl FnMut() -> Needs) -> Needs {
        match f {
            Term::PrimFn(_) => Some(EMPTY),
            Term::Lam(..) => lambda(),
            Term::Var(x) => {
                let x = self.name(x);
                Some(self.sets.one(x))
            }
            _ => None,
        }
    }

    /// What a body that needs `body` needs with `names` bound around it to values not known to
    /// be functions that end.
    fn under(&mut self, names: &[Arc<str>], body: Needs) -> Needs {
        let body = body?;
        for x in names {
            let x = self.name(x);
            if self.sets.remove(body, x).is_some() {
                return None;
            }
        }
        Some(body)
    }
}

/// A set of names, by its number in [`Sets`].
type Set = u32;

/// The set of no names.
const EMPTY: Set = 0;

/// A node of a set of names as a big-endian Patricia trie (Okasaki and Gill, "Fast Mergeable
/// Integer Maps", 1998).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum SetNode {
    Empty,
    One(Name),
    /// The names whose bits above `bit` are those of `prefix`: those with `bit` clear in
    /// `zero`, the others in `one`, neither empty.
    Split {
        prefix: Name,
        bit: Name,
        zero: Set,
        one: Set,
    },
}

/// The sets of names of one reading, each node made once and each union of two nodes computed
/// once. A Patricia trie is fixed by its names, so two equal sets have one number and a union
/// stops where its two sets share a node; a set that adds one name to another differs from it
/// only along the path to that name, so a union of two sets each one name larger than a pair
/// joined before reads only those paths, at most 32 nodes deep. The sets of the arms of an `if`
/// that each add a name to what a shared part needs, and two chains of calls joined at every
/// level, are so joined in time near the length of a path, not the size of the sets
/// (COMPLEXITY.md row ENDS).
// Complexity tradeoff: the time of a union is bounded by the number of pairs of nodes it reads
// that no earlier union read, not by the sizes of its sets, and no bound in the size of the
// term is proved for that number: a term whose parts need many sets that share few nodes
// pairwise could make it near the product of their sizes. Why: the sets are the answer the
// reading of each part must carry so that it is read once, and hash-consed tries with a memo
// of the pairs joined make the common case, sets that mostly agree, cost a path. Trigger: many
// distinct parts calling many distinct names whose sets are joined in ways unlike those of a
// program's nesting. Tests: the four scaling tests in `l01_28_staging::ends`, each at k and 8k,
// one of which fails at 60 s with the memo of pairs removed. COMPLEXITY.md row ENDS. A complete
// solution would bound the pairs read, for instance by reading each binder only against the
// one name it binds (a membership query per binder on a persistent structure built once per
// part), which needs the parts' sets never to be materialized.
struct Sets {
    nodes: Vec<SetNode>,
    /// The number of names in each set.
    sizes: Vec<u32>,
    made: DigestMap<SetNode, Set>,
    /// The union of each pair of sets joined, the smaller number first.
    unions: DigestMap<(Set, Set), Set>,
}

impl Default for Sets {
    fn default() -> Self {
        Sets {
            nodes: vec![SetNode::Empty],
            sizes: vec![0],
            made: DigestMap::from_iter([(SetNode::Empty, EMPTY)]),
            unions: DigestMap::default(),
        }
    }
}

/// The bits of `x` above `bit`.
fn above(x: Name, bit: Name) -> Name {
    x & !(bit | (bit - 1))
}

impl Sets {
    fn make(&mut self, n: SetNode) -> Set {
        let Sets {
            nodes, sizes, made, ..
        } = self;
        *made.entry(n).or_insert_with(|| {
            sizes.push(match n {
                SetNode::Empty => 0,
                SetNode::One(_) => 1,
                SetNode::Split { zero, one, .. } => sizes[zero as usize] + sizes[one as usize],
            });
            nodes.push(n);
            (nodes.len() - 1) as Set
        })
    }

    fn size(&self, s: Set) -> u32 {
        self.sizes[s as usize]
    }

    /// Whether `x` is in `s`, read along the one path to it.
    fn contains(&self, mut s: Set, x: Name) -> bool {
        loop {
            match self.nodes[s as usize] {
                SetNode::Empty => return false,
                SetNode::One(y) => return x == y,
                SetNode::Split {
                    prefix,
                    bit,
                    zero,
                    one,
                } => {
                    if above(x, bit) != prefix {
                        return false;
                    }
                    s = if x & bit == 0 { zero } else { one };
                }
            }
        }
    }

    /// The names of `s`, in increasing order.
    fn members(&self, s: Set) -> Vec<Name> {
        let mut out = Vec::new();
        let mut todo = vec![s];
        while let Some(s) = todo.pop() {
            match self.nodes[s as usize] {
                SetNode::Empty => {}
                SetNode::One(x) => out.push(x),
                SetNode::Split { zero, one, .. } => todo.extend([one, zero]),
            }
        }
        out
    }

    fn one(&mut self, x: Name) -> Set {
        self.make(SetNode::One(x))
    }

    fn split(&mut self, prefix: Name, bit: Name, zero: Set, one: Set) -> Set {
        match (zero, one) {
            (EMPTY, s) | (s, EMPTY) => s,
            _ => self.make(SetNode::Split {
                prefix,
                bit,
                zero,
                one,
            }),
        }
    }

    /// The union of the nonempty sets `s` and `t`, whose names start with `p` and `q`, which
    /// differ above both sets' split bits.
    fn join(&mut self, p: Name, s: Set, q: Name, t: Set) -> Set {
        let bit = 1 << (Name::BITS - 1 - (p ^ q).leading_zeros());
        match p & bit {
            0 => self.split(above(p, bit), bit, s, t),
            _ => self.split(above(p, bit), bit, t, s),
        }
    }

    fn insert(&mut self, s: Set, x: Name) -> Set {
        match self.nodes[s as usize] {
            SetNode::Empty => self.one(x),
            SetNode::One(y) if y == x => s,
            SetNode::One(y) => {
                let o = self.one(x);
                self.join(x, o, y, s)
            }
            SetNode::Split {
                prefix,
                bit,
                zero,
                one,
            } => {
                if above(x, bit) != prefix {
                    let o = self.one(x);
                    self.join(x, o, prefix, s)
                } else if x & bit == 0 {
                    let zero = self.insert(zero, x);
                    self.split(prefix, bit, zero, one)
                } else {
                    let one = self.insert(one, x);
                    self.split(prefix, bit, zero, one)
                }
            }
        }
    }

    /// `s` without `x`, or `None` when `x` is not in `s`.
    fn remove(&mut self, s: Set, x: Name) -> Option<Set> {
        match self.nodes[s as usize] {
            SetNode::Empty => None,
            SetNode::One(y) => (y == x).then_some(EMPTY),
            SetNode::Split {
                prefix,
                bit,
                zero,
                one,
            } => {
                if above(x, bit) != prefix {
                    None
                } else if x & bit == 0 {
                    let zero = self.remove(zero, x)?;
                    Some(self.split(prefix, bit, zero, one))
                } else {
                    let one = self.remove(one, x)?;
                    Some(self.split(prefix, bit, zero, one))
                }
            }
        }
    }

    /// The union of `s` and `t`. A part the two share is not read: the recursion goes no
    /// deeper than the bits of a name.
    fn union(&mut self, s: Set, t: Set) -> Set {
        if s == t || t == EMPTY {
            return s;
        }
        if s == EMPTY {
            return t;
        }
        let pair = (s.min(t), s.max(t));
        if let Some(&u) = self.unions.get(&pair) {
            return u;
        }
        let u = self.union_new(s, t);
        self.unions.insert(pair, u);
        u
    }

    /// The union of the distinct nonempty sets `s` and `t`, not joined before.
    fn union_new(&mut self, s: Set, t: Set) -> Set {
        let split = |n: SetNode| match n {
            SetNode::Split {
                prefix,
                bit,
                zero,
                one,
            } => (prefix, bit, zero, one),
            SetNode::Empty | SetNode::One(_) => unreachable!("a node of two names or more"),
        };
        match (self.nodes[s as usize], self.nodes[t as usize]) {
            (SetNode::One(x), _) => self.insert(t, x),
            (_, SetNode::One(x)) => self.insert(s, x),
            (ns, nt) => {
                let (p, m, s0, s1) = split(ns);
                let (q, n, t0, t1) = split(nt);
                if m == n && p == q {
                    let zero = self.union(s0, t0);
                    let one = self.union(s1, t1);
                    self.split(p, m, zero, one)
                } else if m > n && above(q, m) == p {
                    if q & m == 0 {
                        let zero = self.union(s0, t);
                        self.split(p, m, zero, s1)
                    } else {
                        let one = self.union(s1, t);
                        self.split(p, m, s0, one)
                    }
                } else if n > m && above(p, n) == q {
                    if p & n == 0 {
                        let zero = self.union(s, t0);
                        self.split(q, n, zero, t1)
                    } else {
                        let one = self.union(s, t1);
                        self.split(q, n, t0, one)
                    }
                } else {
                    self.join(p, s, q, t)
                }
            }
        }
    }
}

/// Puts on `todo`, to be read, the parts of `t` that [`Reader::needs_of`] reads: every subterm,
/// except those of `fix` and `gen`, and a function called or handed to a family operation only
/// when it is a lambda.
fn each_part<'t>(t: &'t Term, todo: &mut Vec<Part<'t>>) {
    let lam = |g: &'t Shared| matches!(**g, Term::Lam(..)).then(|| Part::held(g));
    match t {
        Term::Lit(_)
        | Term::Var(_)
        | Term::PrimFn(_)
        | Term::Read(_)
        | Term::Fix { .. }
        | Term::Gen { .. } => {}
        Term::Lam(_, b) | Term::Push(_, b) => todo.push(Part::held(b)),
        Term::App(g, args) => todo.extend(lam(g).into_iter().chain(args.iter().map(Part::inline))),
        Term::Prim(_, args) => todo.extend(args.iter().map(Part::inline)),
        Term::Let(_, e, b) => todo.extend([e, b].map(Part::held)),
        Term::If(c, a, b) => todo.extend([c, a, b].map(Part::held)),
        Term::Match(s, arms) => todo.extend(
            std::iter::once(Part::held(s)).chain(arms.iter().map(|(_, a)| Part::inline(a))),
        ),
        Term::Fam { domain, body, .. } => todo.extend([domain, body].map(Part::held)),
        Term::Reindex { family, kf, vf, .. } => todo.extend(
            [Some(Part::held(family)), lam(kf), lam(vf)]
                .into_iter()
                .flatten(),
        ),
        Term::Discard { family, sel } => {
            todo.extend([Some(Part::held(family)), lam(sel)].into_iter().flatten())
        }
        Term::Fold {
            family,
            op,
            identity,
            ..
        } => todo.extend(
            [
                Some(Part::held(family)),
                lam(op),
                identity.as_ref().map(Part::held),
            ]
            .into_iter()
            .flatten(),
        ),
    }
}

/// The names `p` binds.
fn binds(p: &Pattern) -> Vec<Arc<str>> {
    pattern_names(p).into_iter().cloned().collect()
}

/// What a part of a term reads: the names it reads and does not bind, and whether it reads
/// or writes a port outside the join of a lattice recursion (a port the join reads is not an
/// effect of the recursion).
#[derive(Clone, Copy, Default, PartialEq, Eq)]
struct Summary {
    free: Set,
    effects: bool,
}

/// The summaries of the parts of terms, each part held in a [`Shared`] node read once, known
/// by the node's id as in [`Reader::ids`]: a part shared by two places is one node reached
/// twice. The names a part reads are a set of [`Sets`], so a union stops where its two sets
/// share a node.
// Complexity tradeoff (COMPLEXITY.md F4, F13, F83): the naive mix computes `free` and `effects`
// afresh at every node, with the bound names in a `Vec`, O(k³) for a chain of k local
// definitions (O(t · depth) for `free` alone), and reading the term as a tree costs O(2^d)
// when each of d levels shares one part between two places (F83). Here each part held in a
// node is summarized once, by the node's id (O(P log P) for P distinct parts), and the names
// are sets of [`Sets`], so a mix costs the distinct parts plus the unions [`Sets`] bounds. Memory: one summary per node read and the tries of
// the sets until the next `mix_top` clears them.
#[derive(Default)]
struct Frees {
    names: HashMap<Arc<str>, Name>,
    /// Each name, by its number.
    list: Vec<Arc<str>>,
    sets: Sets,
    /// The summary of each part held in a node, by the node's id.
    of: HashMap<u64, Summary>,
    /// The names of each set that are not prelude words.
    nonwords: HashMap<Set, Set>,
}

impl Frees {
    fn name(&mut self, x: &Arc<str>) -> Name {
        if let Some(&n) = self.names.get(x) {
            return n;
        }
        let n = self.list.len() as Name;
        self.names.insert(x.clone(), n);
        self.list.push(x.clone());
        n
    }

    /// The names of `s`.
    fn names_in(&self, s: Set) -> Vec<&Arc<str>> {
        let members = self.sets.members(s).into_iter();
        members.map(|x| &self.list[x as usize]).collect()
    }

    /// What `root` reads. The parts are read with an explicit stack, each after its own parts,
    /// and each part held in a node only the first time the node is reached: a node reached
    /// again while its own parts are being read would be a part of itself.
    fn summary(&mut self, root: Part<'_>) -> Summary {
        // A part to read, with `None`; or a part whose `k` parts are on their way, with `k`.
        let mut todo = vec![(root, None)];
        // The summaries read and not yet taken by the part that reads them: a part's own parts
        // end up on top, in the reverse of the order they were put on `todo`.
        let mut done: Vec<Summary> = Vec::new();
        let mut parts = Vec::new();
        while let Some((p, count)) = todo.pop() {
            let Some(k) = count else {
                if let Some(&s) = p.node.and_then(|s| self.of.get(&s.id())) {
                    done.push(s);
                    continue;
                }
                let subs = subs(p.term);
                todo.push((p, Some(subs.len())));
                todo.extend(subs.into_iter().map(|(q, ..)| (q, None)));
                continue;
            };
            let from = done.len() - k;
            parts.clear();
            parts.extend(done[from..].iter().rev().copied());
            done.truncate(from);
            let s = self.combine(p.term, &parts);
            if let Some(n) = p.node {
                self.of.insert(n.id(), s);
            }
            done.push(s);
        }
        done.pop().expect("the root, read")
    }

    /// What `t` reads, given what its parts read, in the order [`subs`] gives them.
    fn combine(&mut self, t: &Term, parts: &[Summary]) -> Summary {
        let mut out = match t {
            Term::Var(x) => Summary {
                free: {
                    let x = self.name(x);
                    self.sets.one(x)
                },
                effects: false,
            },
            Term::Read(_) | Term::Push(..) => Summary {
                free: EMPTY,
                effects: true,
            },
            _ => Summary::default(),
        };
        for ((_, names, join), p) in subs(t).iter().zip(parts) {
            let mut free = p.free;
            for x in names.iter() {
                let x = self.name(x);
                free = self.sets.remove(free, x).unwrap_or(free);
            }
            out.free = self.sets.union(out.free, free);
            out.effects |= p.effects && !join;
        }
        out
    }

    /// The names of `s` that are not prelude words. Each node of a set is read once over the
    /// life of the summaries.
    fn nonwords(&mut self, s: Set) -> Set {
        if let Some(&n) = self.nonwords.get(&s) {
            return n;
        }
        let n = match self.sets.nodes[s as usize] {
            SetNode::Empty => EMPTY,
            SetNode::One(x) if interp::word(&self.list[x as usize]) => EMPTY,
            SetNode::One(_) => s,
            SetNode::Split {
                prefix,
                bit,
                zero,
                one,
            } => {
                let (zero, one) = (self.nonwords(zero), self.nonwords(one));
                self.sets.split(prefix, bit, zero, one)
            }
        };
        self.nonwords.insert(s, n);
        n
    }
}

/// The parts of `t`, in the order `mix` meets them, each with the names it is under, borrowed
/// from the term where it holds them as a list, and whether it is the join of a lattice
/// recursion.
fn subs(t: &Term) -> Vec<(Part<'_>, Names<'_>, bool)> {
    fn held(s: &Shared) -> (Part<'_>, Names<'_>, bool) {
        (Part::held(s), Cow::Borrowed(&[][..]), false)
    }
    fn inline(t: &Term) -> (Part<'_>, Names<'_>, bool) {
        (Part::inline(t), Cow::Borrowed(&[][..]), false)
    }
    let one = std::slice::from_ref;
    match t {
        Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => Vec::new(),
        Term::Lam(ps, b) => vec![(Part::held(b), Cow::Borrowed(&ps[..]), false)],
        Term::App(g, args) => std::iter::once(held(g))
            .chain(args.iter().map(inline))
            .collect(),
        Term::Prim(_, args) => args.iter().map(inline).collect(),
        Term::Let(x, e, b) => vec![held(e), (Part::held(b), Cow::Borrowed(one(x)), false)],
        Term::If(c, a, b) => vec![held(c), held(a), held(b)],
        Term::Match(s, arms) => std::iter::once(held(s))
            .chain(
                arms.iter()
                    .map(|(p, a)| (Part::inline(a), Cow::Owned(binds(p)), false)),
            )
            .collect(),
        Term::Fam { domain, var, body } => vec![
            held(domain),
            (Part::held(body), Cow::Borrowed(one(var)), false),
        ],
        Term::Reindex { family, kf, vf, .. } => vec![held(family), held(kf), held(vf)],
        Term::Discard { family, sel } => vec![held(family), held(sel)],
        Term::Fold {
            family,
            op,
            identity,
            ..
        } => [family, op].into_iter().chain(identity).map(held).collect(),
        Term::Fix {
            init,
            step,
            this,
            key,
            kind,
            ..
        } => {
            let names: Names<'_> = Cow::Owned(vec![this.clone(), key.clone()]);
            let mut out = vec![held(init), (Part::held(step), names.clone(), false)];
            if let zed_kernel::FixKind::Lattice { join } = kind {
                out.push((Part::held(join), names, true));
            }
            out
        }
        Term::Gen {
            init, step, guard, ..
        } => vec![held(init), held(step), held(guard)],
        Term::Push(_, v) => vec![held(v)],
    }
}

/// A map of names to bindings, by its number in [`Maps`].
type Map = u32;

/// The map of no names.
const NO_MAP: Map = 0;

/// A binding of a name in scope, by its number: [`UNKNOWN`] for every binding not known at
/// build, else the number [`Mixer::number`] gives to what the binding is.
type Binding = u32;

/// The number of every binding not known at build (a let bound to a run-stage term, a
/// parameter). Mixing cannot tell two such bindings of a name apart: the name is left as it
/// is under either, and nothing evaluates it. So they share one number, and a part reached
/// under two of them is mixed once.
const UNKNOWN: Binding = 0;

/// A node of a map of names to bindings as a big-endian Patricia trie, as [`SetNode`].
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum MapNode {
    Empty,
    One(Name, Binding),
    Split {
        prefix: Name,
        bit: Name,
        zero: Map,
        one: Map,
    },
}

/// The maps of names to bindings of one mixer, each node made once. The scope's map of each
/// name in scope to its innermost binding is one map, changed along one path when a name is
/// pushed; the bindings of the names a part reads are that map restricted to the part's set
/// of names, and two places under the same bindings of those names have one map, so the map's
/// number is a key of what the part mixes to.
// Complexity tradeoff: the time of a restriction is bounded by the number of pairs of a map
// and a set it reads that no earlier restriction read, not by the sizes of the map and the
// set, and no bound in the size of the term is proved for that number, as for a union of
// [`Sets`]: parts that read many sets sharing few nodes, under scopes that differ in many
// places, could make it near the product of their sizes. Why: the restricted map is the key
// that lets a part shared by two places under the same bindings be mixed once, and a
// hash-consed restriction with a memo of the pairs read makes the common case, a scope one
// name larger than one seen and a set much like one seen, cost a path. Trigger: many distinct
// parts reading many distinct names under scopes unlike those of a program's nesting. Tests:
// `l01_28_staging::dag::mixing_nested_ifs_whose_arms_are_one_part_scales`,
// `l01_28_staging::dag::mixing_nested_lets_of_a_parameter_over_one_body_scales` and
// `l01_28_staging::scaling::mixing_a_chain_of_local_definitions_scales`, each at n and 8n.
// COMPLEXITY.md row F83. A complete solution would bound the pairs read, for instance
// by keying a part by the innermost binding among the names it reads, found by a query on a
// structure over the scope's positions that needs no set materialized.
struct Maps {
    nodes: Vec<MapNode>,
    sizes: Vec<u32>,
    made: HashMap<MapNode, Map>,
    /// The restriction of each map to each set read, by the pair.
    restricted: HashMap<(Map, Set), Map>,
    /// Whether every binding of each map is build-stage.
    known: HashMap<Map, bool>,
}

impl Default for Maps {
    fn default() -> Self {
        Maps {
            nodes: vec![MapNode::Empty],
            sizes: vec![0],
            made: HashMap::from([(MapNode::Empty, NO_MAP)]),
            restricted: HashMap::new(),
            known: HashMap::new(),
        }
    }
}

impl Maps {
    fn make(&mut self, n: MapNode) -> Map {
        let Maps {
            nodes, sizes, made, ..
        } = self;
        *made.entry(n).or_insert_with(|| {
            sizes.push(match n {
                MapNode::Empty => 0,
                MapNode::One(..) => 1,
                MapNode::Split { zero, one, .. } => sizes[zero as usize] + sizes[one as usize],
            });
            nodes.push(n);
            (nodes.len() - 1) as Map
        })
    }

    fn size(&self, m: Map) -> u32 {
        self.sizes[m as usize]
    }

    fn split(&mut self, prefix: Name, bit: Name, zero: Map, one: Map) -> Map {
        match (zero, one) {
            (NO_MAP, m) | (m, NO_MAP) => m,
            _ => self.make(MapNode::Split {
                prefix,
                bit,
                zero,
                one,
            }),
        }
    }

    /// The union of the nonempty maps `m` and `n`, whose names start with `p` and `q`, which
    /// differ above both maps' split bits.
    fn join(&mut self, p: Name, m: Map, q: Name, n: Map) -> Map {
        let bit = 1 << (Name::BITS - 1 - (p ^ q).leading_zeros());
        match p & bit {
            0 => self.split(above(p, bit), bit, m, n),
            _ => self.split(above(p, bit), bit, n, m),
        }
    }

    /// `m` with `x` mapped to `b`, in place of any binding it had.
    fn insert(&mut self, m: Map, x: Name, b: Binding) -> Map {
        match self.nodes[m as usize] {
            MapNode::Empty => self.make(MapNode::One(x, b)),
            MapNode::One(y, _) if y == x => self.make(MapNode::One(x, b)),
            MapNode::One(y, _) => {
                let o = self.make(MapNode::One(x, b));
                self.join(x, o, y, m)
            }
            MapNode::Split {
                prefix,
                bit,
                zero,
                one,
            } => {
                if above(x, bit) != prefix {
                    let o = self.make(MapNode::One(x, b));
                    self.join(x, o, prefix, m)
                } else if x & bit == 0 {
                    let zero = self.insert(zero, x, b);
                    self.split(prefix, bit, zero, one)
                } else {
                    let one = self.insert(one, x, b);
                    self.split(prefix, bit, zero, one)
                }
            }
        }
    }

    /// The binding `m` maps `x` to, read along the one path to it.
    fn get(&self, mut m: Map, x: Name) -> Option<Binding> {
        loop {
            match self.nodes[m as usize] {
                MapNode::Empty => return None,
                MapNode::One(y, b) => return (y == x).then_some(b),
                MapNode::Split {
                    prefix,
                    bit,
                    zero,
                    one,
                } => {
                    if above(x, bit) != prefix {
                        return None;
                    }
                    m = if x & bit == 0 { zero } else { one };
                }
            }
        }
    }

    /// `m` restricted to the names of `s`. A pair read before is not read again, and the
    /// recursion goes no deeper than the bits of a name in each trie.
    fn restrict(&mut self, sets: &Sets, m: Map, s: Set) -> Map {
        if m == NO_MAP || s == EMPTY {
            return NO_MAP;
        }
        if let Some(&r) = self.restricted.get(&(m, s)) {
            return r;
        }
        let r = match (self.nodes[m as usize], sets.nodes[s as usize]) {
            (MapNode::One(x, _), _) => match sets.contains(s, x) {
                true => m,
                false => NO_MAP,
            },
            (_, SetNode::One(x)) => match self.get(m, x) {
                Some(b) => self.make(MapNode::One(x, b)),
                None => NO_MAP,
            },
            (
                MapNode::Split {
                    prefix: p,
                    bit: mb,
                    zero: m0,
                    one: m1,
                },
                SetNode::Split {
                    prefix: q,
                    bit: n,
                    zero: s0,
                    one: s1,
                },
            ) => {
                if mb == n && p == q {
                    let zero = self.restrict(sets, m0, s0);
                    let one = self.restrict(sets, m1, s1);
                    self.split(p, mb, zero, one)
                } else if mb > n && above(q, mb) == p {
                    self.restrict(sets, if q & mb == 0 { m0 } else { m1 }, s)
                } else if n > mb && above(p, n) == q {
                    self.restrict(sets, m, if p & n == 0 { s0 } else { s1 })
                } else {
                    NO_MAP
                }
            }
            (MapNode::Empty, _) | (_, SetNode::Empty) => unreachable!("empty, answered above"),
        };
        self.restricted.insert((m, s), r);
        r
    }

    /// Whether every binding of `m` is build-stage: each node is read once.
    fn all_known(&mut self, m: Map) -> bool {
        if let Some(&k) = self.known.get(&m) {
            return k;
        }
        let k = match self.nodes[m as usize] {
            MapNode::Empty => true,
            MapNode::One(_, b) => b != UNKNOWN,
            MapNode::Split { zero, one, .. } => self.all_known(zero) && self.all_known(one),
        };
        self.known.insert(m, k);
        k
    }
}

/// The stage of each definition of `unit`, by source name, in order: the stage [`mix`] binds
/// it with, that of its mixed term, under the definitions before it, each bound mixed.
pub fn color(unit: &Unit) -> Vec<(String, Stage)> {
    let mut m = Mixer::default();
    unit.defs
        .iter()
        .map(|d| (d.name.clone(), m.bind_mixed(d).1))
        .collect()
}

/// `unit` with its demanded build-stage terms evaluated, keeping the definitions `roots`
/// and the tests read. The result has no warnings: they are the elaborator's, and
/// `zedc::run::Program::stage` shares the program's placed warnings instead.
pub fn mix(unit: &Unit, roots: &[&str]) -> (Unit, Report) {
    let (out, m) = mix_keeping(unit, roots);
    (out, m.report)
}

/// The mixer of a unit after [`mix`] with every definition a root: it mixes a changed term of
/// one of the unit's definitions under the others (step L25.8, a mutant).
pub struct Remix {
    m: Mixer,
}

impl Remix {
    /// `unit` with its build-stage terms evaluated, every definition kept, and the mixer.
    pub fn new(unit: &Unit) -> (Unit, Remix) {
        let roots: Vec<&str> = unit.defs.iter().map(|d| d.name.as_str()).collect();
        let (out, mut m) = mix_keeping(unit, &roots);
        m.report = Report::default();
        (out, Remix { m })
    }

    /// `t`, a changed term of a definition of the unit, mixed as [`mix`] mixes that
    /// definition: under the definitions of the unit, which names unique in the unit keep
    /// apart from those `t` does not read, each read of a definition the mix cut kept as [`mix`]
    /// keeps it. It costs the mixing of `t` alone and two reads of its free names.
    pub fn mix(&mut self, t: &Term) -> Term {
        let out = Shared::new(inline(self.m.mix_top(Part::inline(t))));
        self.m.report = Report::default();
        let now = free(&out);
        let cut: Vec<Arc<str>> = (free(t).into_iter())
            .filter(|x| !now.contains(x) && self.m.runs.contains(x))
            .collect();
        match cut.is_empty() {
            true => Shared::unwrap_or_clone(out),
            false => Shared::unwrap_or_clone(with_reads(&out, &cut)),
        }
    }
}

fn mix_keeping(unit: &Unit, roots: &[&str]) -> (Unit, Mixer) {
    // Complexity tradeoff (COMPLEXITY.md F25): a search of the list of roots for each
    // definition costs O(definitions × roots); the roots in a hash set cost O(1) per
    // definition and O(roots) memory.
    let roots: HashSet<&str> = roots.iter().copied().collect();
    let mut demanded: BTreeSet<Arc<str>> = unit
        .defs
        .iter()
        .filter(|d| roots.contains(&d.name.as_str()))
        .map(|d| d.kernel.clone())
        .collect();
    for t in unit.tests.iter() {
        for term in std::iter::once(&t.check).chain(&t.args).chain([&t.want]) {
            demanded.extend(free(term));
        }
    }
    // The names each demanded definition reads as written, kept for `keep_cut_reads`.
    let mut read: HashMap<&str, BTreeSet<Arc<str>>> = HashMap::new();
    for d in unit.defs.iter().rev() {
        if demanded.contains(&d.kernel) {
            let names = free(&d.term);
            demanded.extend(names.iter().cloned());
            read.insert(&d.kernel, names);
        }
    }
    let mut m = Mixer::default();
    // What each definition mixed reads in the parts the build takes, by kernel name.
    let mut taken: HashMap<&str, Vec<Arc<str>>> = HashMap::new();
    let mut out = Unit {
        defs: Vec::new(),
        tests: unit.tests.clone(),
        warnings: Vec::new(),
        int_params: Default::default(),
        limits: unit.limits,
    };
    for d in &unit.defs {
        if !demanded.contains(&d.kernel) {
            m.report.unread.push(d.name.clone());
            continue;
        }
        let (term, _) = m.bind_mixed(d);
        let names = m.frees.names_in(m.taken).into_iter().cloned().collect();
        taken.insert(&d.kernel, names);
        if matches!(*term, Term::Lit(_)) && term != d.term {
            m.report.built.push(d.name.clone());
        }
        out.defs.push(Def {
            name: d.name.clone(),
            kernel: d.kernel.clone(),
            term,
            first_order: d.first_order,
        });
    }
    m.runs = keep_cut_reads(&mut out.defs, &read, &mut taken);
    let roots: Vec<&str> = (unit.defs.iter())
        .filter(|d| roots.contains(&d.name.as_str()))
        .map(|d| &*d.kernel)
        .collect();
    let reached = reach(&roots, &taken);
    m.report.untaken = (reach(&roots, &read).into_iter())
        .filter(|x| !reached.contains(x))
        .map(Arc::from)
        .collect();
    (out, m)
}

/// The definitions `roots` reach, by kernel name, where `edges` gives the names each
/// definition reads; a name `edges` does not hold is no definition. Each definition is
/// visited once: O(D + E) hash operations for the D definitions reached and their E names.
fn reach<'a, C>(roots: &[&'a str], edges: &'a HashMap<&str, C>) -> HashSet<&'a str>
where
    &'a C: IntoIterator<Item = &'a Arc<str>>,
{
    let mut seen: HashSet<&str> = roots.iter().copied().collect();
    let mut todo: Vec<&str> = roots.to_vec();
    while let Some(d) = todo.pop() {
        for x in edges.get(d).into_iter().flatten() {
            if edges.contains_key(&**x) && seen.insert(x) {
                todo.push(x);
            }
        }
    }
    seen
}

/// The binder of a read [`keep_cut_reads`] adds: `$0`, a binder the compiler made, which the
/// elaborator never makes (its first is `$1`) and nothing reads.
const CUT_READ: &str = "$0";

/// `defs`, the mixed definitions of a unit in its order, each still reading every definition
/// it read as written whose run can stop or not end; gives the kernel names of those that run,
/// and adds each cut read it keeps to the names the definition reads in `taken`.
///
/// A run evaluates the definitions a term reaches, each a let around it, call by value (DESIGN
/// step M0.9), so a definition `main` names only in a branch is evaluated, and when it stops
/// the run stops (DESIGN step L1.28: "a binding named only in a branch cut later is still
/// evaluated", "the run reports the stop in the ordinary way"). Mixing replaces an `if` whose
/// condition is a literal by its arm and a build-stage definition by its value, so the mixed
/// term may no longer name a definition the term as written named. Such a cut name is kept
/// by a let of `$0` to it, around the term or, for a lambda, around its body, when the cut
/// definition runs: its mixed term is not a literal, lambda, primitive or name, or it reads,
/// mixed or as written, a definition that runs. Then a term's mixed cone holds every
/// definition that runs in its cone as written, by induction in the unit's order, and a
/// definition that does not run has no effect when evaluated, so it needs no read.
// Complexity tradeoff: the naive form compares, for each root, its cone as written with its
// mixed cone, O(roots × definitions) (every definition is a root in `Remix::new`). Used: each
// definition's names as written (read once by `mix_keeping`) against its mixed names, one
// `free` of its mixed term, O(s log s) for `s` distinct parts, and one hash lookup per name
// for whether it runs, so O(N log N) over the unit, N its size. What it gives up: a read is
// kept for a cut definition that runs but whose run ends with no effect (one left to run
// because its form does not show that it ends); the run then evaluates it, as the program
// as written does. `Remix::mix` keeps the cut reads of one term at the cost of two `free`s of
// it, O(s log s) for its s distinct parts. Test:
// `l01_28_staging::arms::cut_reads_are_kept_in_time_that_scales`.
fn keep_cut_reads(
    defs: &mut [Def],
    read: &HashMap<&str, BTreeSet<Arc<str>>>,
    taken: &mut HashMap<&str, Vec<Arc<str>>>,
) -> HashSet<Arc<str>> {
    let mut runs: HashSet<Arc<str>> = HashSet::new();
    for d in defs.iter_mut() {
        let now = free(&d.term);
        let was = &read[&*d.kernel];
        let cut: Vec<Arc<str>> = (was.iter())
            .filter(|x| !now.contains(*x) && runs.contains(*x))
            .cloned()
            .collect();
        let value = matches!(
            *d.term,
            Term::Lit(_) | Term::Lam(..) | Term::PrimFn(_) | Term::Var(_)
        );
        if !value || now.iter().chain(was).any(|x| runs.contains(x)) {
            runs.insert(d.kernel.clone());
        }
        if !cut.is_empty() {
            d.term = with_reads(&d.term, &cut);
            // The run evaluates a cut definition kept so: the build takes it.
            if let Some(names) = taken.get_mut(&*d.kernel) {
                names.extend(cut);
            }
        }
    }
    runs
}

/// `t` with a let of [`CUT_READ`] to each of `names` around it, or around its body when it is
/// a lambda none of whose parameters is one of `names`, so that a function stays a function.
fn with_reads(t: &Shared, names: &[Arc<str>]) -> Shared {
    let wrap = |body: Shared| {
        names.iter().rev().fold(body, |body, x| {
            Shared::new(Term::Let(
                CUT_READ.into(),
                Shared::new(Term::Var(x.clone())),
                body,
            ))
        })
    };
    match &**t {
        Term::Lam(ps, body) if !ps.iter().any(|p| names.contains(p)) => {
            Shared::new(Term::Lam(ps.clone(), wrap(body.clone())))
        }
        _ => wrap(t.clone()),
    }
}

/// The domain of a parameter.
#[derive(Clone, Debug)]
pub enum Domain {
    /// The values of a type.
    Type(Type),
    /// The integers between two bounds, either of which may be absent.
    Ints(Option<i64>, Option<i64>),
}

/// What the Trick decides for a parameter.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Choice {
    /// Specialize on each of these values.
    Split(Vec<Value>),
    /// Do not specialize, for this reason.
    Keep(String),
}

/// The Trick: split on the members of `d` among `passed` only when `d` is finite. A type is
/// finite here when it is known finite ([`Type::finite`]).
pub fn trick(d: &Domain, passed: &BTreeSet<Value>) -> Choice {
    let within: Vec<Value> = match d {
        Domain::Type(t) => {
            if !t.finite() {
                // A part written more than once is declared after the sentence, as in a
                // checker's message, unless a message around this one lays it out.
                let local = printed::local();
                let mut why = format!("the domain `{}` is not known to be finite", t.surface());
                if local.is_some() {
                    printed::finish(&mut why);
                }
                return Choice::Keep(why);
            }
            passed.iter().filter(|v| t.contains(v)).cloned().collect()
        }
        Domain::Ints(Some(lo), Some(hi)) => passed
            .iter()
            .filter(|v| matches!(v, Value::Int(i) if lo <= i && i <= hi))
            .cloned()
            .collect(),
        Domain::Ints(..) => {
            return Choice::Keep("an unbounded integer domain is infinite".into());
        }
    };
    if within.is_empty() {
        return Choice::Keep("no static call passes a value of the domain".into());
    }
    Choice::Split(within)
}

/// The values the static calls of `name` in `unit` pass its parameter `param`: each call by
/// its kernel name, in a definition once mixed, whose argument there is a literal, and each
/// case of a test of `name` whose argument there is a literal.
pub fn passed(unit: &Unit, name: &str, param: usize) -> BTreeSet<Value> {
    Specializer::new(unit).passed(name, param)
}

/// The function `name` of `unit` split on its parameter `param` over the values of `d` its
/// static calls pass ([`passed`]), each arm its body mixed with the parameter known, and the
/// general body last; or why the Trick keeps it.
pub fn split(unit: &Unit, name: &str, param: usize, d: &Domain) -> Result<(Term, Report), String> {
    Specializer::new(unit).split(name, param, d)
}

/// What the Trick reads of a unit, gathered once for any number of splits: the literal
/// arguments of the unit's calls once mixed, those of its tests' cases, and a mixer with
/// every definition bound mixed, as [`mix`] binds it. Splitting `k` functions then costs one mix of the
/// unit and `k` mixes of their bodies, where each split mixed the whole unit again.
// Complexity tradeoff (COMPLEXITY.md F42): the naive split mixes the whole unit to find the
// calls and binds every definition again for each function split, O(splits × unit) (72.3
// times the work for 8 times the functions). The specializer mixes and binds once,
// O(unit), and each split then costs the mixes of one body, once per value and once for the
// general arm. Memory: the mixer's scope and the gathered arguments live as long as the
// specializer; a split must leave the scope as it found it.
pub struct Specializer<'u> {
    unit: &'u Unit,
    /// The position of the first definition of each source name.
    by_name: HashMap<&'u str, usize>,
    /// The literal arguments of the calls of each kernel name, by parameter.
    calls: HashMap<(Arc<str>, usize), BTreeSet<Value>>,
    /// The literal arguments of the tests' cases of each source name, by parameter.
    cases: HashMap<(&'u str, usize), BTreeSet<Value>>,
    mixer: Mixer,
}

impl<'u> Specializer<'u> {
    /// What the Trick reads of `unit`.
    pub fn new(unit: &'u Unit) -> Self {
        let mut by_name = HashMap::new();
        for (i, d) in unit.defs.iter().enumerate() {
            by_name.entry(d.name.as_str()).or_insert(i);
        }
        let roots: Vec<&str> = unit.defs.iter().map(|d| d.name.as_str()).collect();
        // The mixer binds each definition mixed, as `mix` binds it, so the splits see what the
        // build sees: a build-stage binding is a literal, lambda, primitive or name, and a
        // definition whose mix fails is left to run.
        let (mixed, mut mixer) = mix_keeping(unit, &roots);
        mixer.report = Report::default();
        let mut calls: HashMap<(Arc<str>, usize), BTreeSet<Value>> = HashMap::new();
        // Each part held in a node is read once, however many places reach it.
        let mut seen = HashSet::new();
        let mut todo: Vec<Part<'_>> = mixed.defs.iter().map(|d| Part::held(&d.term)).collect();
        while let Some(p) = todo.pop() {
            if let Some(s) = p.node
                && !seen.insert(s.id())
            {
                continue;
            }
            if let Term::App(g, args) = p.term
                && let Term::Var(f) = &**g
            {
                for (i, x) in args.iter().enumerate() {
                    if let Term::Lit(v) = x {
                        calls.entry((f.clone(), i)).or_default().insert(v.clone());
                    }
                }
            }
            // The join of a lattice recursion is not read, as before.
            let subs = subs(p.term).into_iter();
            todo.extend(subs.filter(|(_, _, join)| !join).map(|(q, ..)| q));
        }
        let mut cases: HashMap<(&'u str, usize), BTreeSet<Value>> = HashMap::new();
        for t in unit.tests.iter() {
            // A clause's values give `main` its inputs, not an argument of a parameter.
            let written = &t.args[..t.args.len() - t.ports.len()];
            for (i, x) in written.iter().enumerate() {
                if let Term::Lit(v) = x {
                    let key = (t.function.as_str(), i);
                    cases.entry(key).or_default().insert(v.clone());
                }
            }
        }
        Specializer {
            unit,
            by_name,
            calls,
            cases,
            mixer,
        }
    }

    /// The values the static calls of `name` pass its parameter `param` ([`passed`]).
    pub fn passed(&self, name: &str, param: usize) -> BTreeSet<Value> {
        let Some(&at) = self.by_name.get(name) else {
            return BTreeSet::new();
        };
        let kernel = self.unit.defs[at].kernel.clone();
        let calls = self.calls.get(&(kernel, param)).into_iter().flatten();
        let cases = self.cases.get(&(name, param)).into_iter().flatten();
        calls.chain(cases).cloned().collect()
    }

    /// The function `name` split on its parameter `param` ([`split`]). Every definition is
    /// bound in the mixer, where the body of `name` was mixed under those before it alone;
    /// the body reads only those, since each definition comes after those it uses and no two
    /// share a kernel name.
    pub fn split(
        &mut self,
        name: &str,
        param: usize,
        d: &Domain,
    ) -> Result<(Term, Report), String> {
        let at = *self
            .by_name
            .get(name)
            .ok_or_else(|| format!("no definition `{name}`"))?;
        let Term::Lam(ps, body) = &*self.unit.defs[at].term else {
            return Err(format!("`{name}` is not a function"));
        };
        let p = ps
            .get(param)
            .ok_or_else(|| format!("`{name}` has no parameter {param}"))?
            .clone();
        let values = match trick(d, &self.passed(name, param)) {
            Choice::Split(vs) => vs,
            Choice::Keep(why) => return Err(why),
        };
        let m = &mut self.mixer;
        let n = m.scope.len();
        m.unknown(ps);
        let mut arms = Vec::new();
        for v in values {
            m.bind(p.clone(), Stage::Build, &Shared::new(Term::Lit(v.clone())));
            arms.push((Pattern::Lit(v), inline(m.mix_top(Part::held(body)))));
            m.scope.pop();
        }
        arms.push((Pattern::Wild, inline(m.mix_top(Part::held(body)))));
        m.scope.truncate(n);
        let lam = Term::Lam(
            ps.clone(),
            Shared::new(Term::Match(Shared::new(Term::Var(p)), arms)),
        );
        Ok((lam, std::mem::take(&mut m.report)))
    }
}

/// A name in scope: its term when it is build-stage, else nothing, the names that term reads,
/// and the maps of the scope's bindings and entries before it was pushed.
struct Entry {
    name: Arc<str>,
    known: Option<Shared>,
    reads: Set,
    prev: Map,
    prev_stamps: Map,
    /// The number of parameters of the function the term is, when it is a lambda or a name of
    /// one; such an entry is a function.
    arity: Option<usize>,
    /// The number of what the binding is exactly: a literal by its value, any other term by
    /// its id and the exact numbers of the bindings it reads ([`Mixer::number`]).
    fine: Binding,
    /// Whether a call of the binding is shown to end by its form, as [`ends`] reads a call,
    /// and, for a function, whether it has a stub.
    ends: bool,
    /// Whether a call of the binding is shown to end by its form, exactly as [`ends`] reads a
    /// call of the name in the term closed under the bindings it needs ([`Mixer::closed`]): a
    /// primitive, a name free or bound to such a binding, or a lambda each name of
    /// [`Reader::called`] is.
    call_ends: bool,
    /// Whether the binding and each binding it reads, closed the same way, are shown to end
    /// by their form where they are bound, as [`ends`] reads their `let`s: each of them that
    /// is no lambda is shown to end once the names it calls do, and each of those names is
    /// free or bound to a binding whose calls end.
    cone_ends: bool,
    /// The port that answers calls of the function, when it is one whose calls end.
    stub: Option<Arc<Stub>>,
    /// The binding's position in [`Scope::globals`], when it and each binding it needs are
    /// literals, lambdas, primitives or names.
    global: Option<usize>,
}

/// The names in scope, innermost last, with the positions of each name's entries, so a name
/// is looked up in `O(log n)` rather than by a scan of the scope, and the map of each name in
/// scope to its innermost binding (`top`, in [`Maps`]) and to the stamp of its innermost entry
/// (`stamps`): the number of entries pushed before it over the whole run (`pushed`), which
/// only grows and so is never reused after a pop, so two places where a map restricted to
/// some names is one map bind each of those names to one entry.
// Complexity tradeoff (COMPLEXITY.md F4): the naive scope is a list searched from the
// innermost entry, O(n) per lookup and O(n · depth) over a nest of lets; `by_name` finds a
// name's entries in O(log n), at the cost of one map entry per name in scope and a pop that
// removes each name's position as its entry leaves.
#[derive(Default)]
struct Scope {
    entries: Vec<Entry>,
    by_name: BTreeMap<Arc<str>, Vec<usize>>,
    top: Map,
    /// The build-stage entries with a position here ([`Entry::global`]), which a run as
    /// written is under ([`Mixer::run_under`]).
    globals: Globals,
    stamps: Map,
    pushed: Binding,
}

impl Scope {
    fn push(&mut self, e: Entry) {
        self.by_name
            .entry(e.name.clone())
            .or_default()
            .push(self.entries.len());
        self.entries.push(e);
    }

    fn len(&self) -> usize {
        self.entries.len()
    }

    fn pop(&mut self) {
        let e = self.entries.pop().expect("a name in scope");
        let at = self.by_name.get_mut(&e.name).expect("pushed with it");
        at.pop();
        if at.is_empty() {
            self.by_name.remove(&e.name);
        }
        if e.global.is_some() {
            self.globals.pop();
        }
        self.top = e.prev;
        self.stamps = e.prev_stamps;
    }

    /// What each of `names`, read at position `at`, refers to among the globals: the
    /// innermost build-stage entry below `at` of that name, else the prelude word. `None` when
    /// such an entry has no position among the globals. A name that is neither is left out, so
    /// a run reads it as unbound, as it would under the `let`s of [`Mixer::closed`].
    fn reads<'n>(
        &self,
        names: impl IntoIterator<Item = &'n Arc<str>>,
        at: usize,
    ) -> Option<Vec<(Arc<str>, Global)>> {
        let mut out = Vec::new();
        for y in names {
            let g = match self.known_below(y, at) {
                Some(j) => Global::At(self.entries[j].global?),
                None => match interp::prim(y) {
                    Some(p) => Global::Prim(p),
                    None => continue,
                },
            };
            out.push((y.clone(), g));
        }
        Some(out)
    }

    fn truncate(&mut self, n: usize) {
        while self.len() > n {
            self.pop();
        }
    }

    /// The innermost binding of `x`: `None` for a name the scope does not bind.
    fn lookup(&self, x: &str) -> Option<&Option<Shared>> {
        let i = *self.by_name.get(x)?.last()?;
        Some(&self.entries[i].known)
    }

    /// The innermost build-stage entry of `x` below position `below`.
    fn known_below(&self, x: &str, below: usize) -> Option<usize> {
        let at = self.by_name.get(x)?;
        let n = at.partition_point(|&i| i < below);
        at[..n]
            .iter()
            .rev()
            .copied()
            .find(|&i| self.entries[i].known.is_some())
    }
}

/// The names a subterm is under.
type Names<'t> = Cow<'t, [Arc<str>]>;

/// Where a part to mix is: held in a node, or held inline at a position of [`Mixer::arena`].
#[derive(Clone, Copy)]
enum Site<'t> {
    Held(&'t Shared),
    Inline(&'t Term, usize),
}

/// A part mixed, held in a node when it can be shared, with what it reads.
struct Out {
    term: Mixed,
    sum: Summary,
}

enum Mixed {
    Held(Shared),
    Inline(Term),
}

impl Out {
    fn term(&self) -> &Term {
        match &self.term {
            Mixed::Held(s) => s,
            Mixed::Inline(t) => t,
        }
    }
}

/// `o` as a term held inline: moved out of its node when nothing else holds it, else that
/// node's term copied one level deep (its own parts stay shared).
fn inline(o: Out) -> Term {
    match o.term {
        Mixed::Held(s) => Shared::unwrap_or_clone(s),
        Mixed::Inline(t) => t,
    }
}

/// Why a build-stage term is left to run when its form does not show that it ends.
const FORM: &str = "its form does not show that it ends";

/// The value of the closed term `t` under the prelude, its calls of the functions of `stubs`
/// answered by their ports for the run `calls`.
fn run_with(t: Term, stubs: &[Arc<Stub>], calls: &Arc<Run>) -> Result<Value, KernelError> {
    let ports: Arc<BTreeMap<Arc<str>, Arc<Stub>>> =
        Arc::new(stubs.iter().map(|s| (s.port.clone(), s.clone())).collect());
    let world = stubs.iter().fold(World::new(), |w, s| {
        let port = Port {
            stub: s.clone(),
            run: calls.clone(),
            ports: ports.clone(),
        };
        w.source(&s.port, Arc::new(port))
    });
    Evaluator::new(world).run(&interp::prelude(t))
}

/// A run's value, or its failure with the error the run as written stops with when that is
/// known.
type Said = Result<Value, Option<String>>;

/// The error the run `calls` with stubs, which stopped with `e`, stops with as written, when
/// that is known. A run with stubs takes the steps of the run as written but at the calls of
/// stubbed functions, and a stub's call that gives a value gives the value the call as written
/// gives, so the two runs differ only where a stub's call fails. A stub's call fails where the
/// call as written fails, and its error is then the as-written error kept in the stub's table
/// ([`Run::failed`]); or where the stub itself fails: at a call inside a pure region, an
/// argument holding a function no stub stands for, one a key cannot tell apart or an answer
/// that cannot be compared, which the call as written may not meet, and then the error is not
/// known. A run whose result is a function fails where the call as written gives that
/// function, so that error is not known either. Any other error is met outside the stubs'
/// bodies, where the two runs agree. An error the evaluator gives for want of memory is treated
/// as not known, since the run as written holds other values than the run with stubs.
fn error_as_written(e: KernelError, calls: &Run) -> Option<String> {
    match e {
        KernelError::Port(..) => calls.failed.lock().expect("one thread").take(),
        KernelError::Type(m)
            if m.ends_with("applied to a function")
                || m.ends_with("used inside a pure region")
                || m == "the program's result is a function" =>
        {
            None
        }
        KernelError::UnknownPort(_)
        | KernelError::OutOfFuel
        | KernelError::NumberTooLarge { .. }
        | KernelError::TextTooLarge { .. } => None,
        e => Some(e.to_string()),
    }
}

/// Whether the value `v` is compared in time near the memory it holds: each leaf is a boolean,
/// a number or a string, in tuples and keypaths. Floats compare by their bits, so `-0.0` and
/// `0.0` are told apart. A string is compared by its canonical name ([`Key`]), which a join of
/// any length gets in time near its nodes, not its bytes, so how a call stages does not switch
/// at a length or at a join (QUESTIONS A7). A family's or an atom's parts are not walked.
// Complexity tradeoff: a walk of every path reads a tuple holding itself doubled k times
// 2^k times. Used: a set of the ids of the shared tuples met (`Value::shared_parts`), so each
// is read once, O(s) for `s` distinct parts. Test
// `l01_28_staging::dag::calls_at_a_doubled_tuple_stage_alike`.
fn compared(v: &Value) -> bool {
    let mut met = HashSet::new();
    let mut todo = vec![v];
    while let Some(v) = todo.pop() {
        match v {
            Value::Bool(_)
            | Value::Int(_)
            | Value::Big(_)
            | Value::Rat(_)
            | Value::Float(_)
            | Value::Float32(_)
            | Value::Str(_) => {}
            Value::Tuple(items) | Value::Path(items) => {
                if v.shared_parts().is_none_or(|(id, _)| met.insert(id)) {
                    todo.extend(items.iter());
                }
            }
            Value::Atom(_) | Value::Family(_) => return false,
        }
    }
    true
}

/// A value as a key of the stage's maps: the value, and its canonical form, by which keys are
/// equal and ordered. The canonical form names each string by its bytes ([`text::Names`]) and
/// each tuple or keypath by its kind and the forms of its parts ([`Namer`]), so two keys are
/// equal exactly when their values are. The order is that of names, not of bytes, and no
/// result reads it: each map is only looked up, and the run log is read in the order of the
/// run (item STAGE-joined-eq-build).
// Complexity tradeoff: a key holding a string compared by its bytes reads every byte at each
// comparison, and a join doubled k times is 2^k bytes in O(k) nodes, so staging gave up
// keying calls at joins (item STAGE-joined-eq). Here a key's strings are named once, when the
// key is made, in O(n log N) dictionary steps for n nodes not named before and N bytes
// ([`text::Names`]); each tuple is named by the forms of its parts in O(p log T) for p parts
// and T tuples named, a shared tuple once by its id; and a comparison reads no byte and no
// part. Tradeoff: each
// node and tuple named is kept, with its summary, while the mix lives. Nothing is refused.
// Tests `l01_28_staging::dag::calls_at_joins_of_100_and_200_bytes_stage_alike`,
// `l01_28_staging::dag::a_call_at_a_long_join_is_mixed_once` and
// `l01_28_staging::dag::calls_at_a_doubled_tuple_stage_alike`; COMPLEXITY.md row
// STAGE-joined-eq-build.
#[derive(Clone, Debug)]
struct Key {
    canon: Canon,
    value: Value,
}

/// A value's canonical form.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Canon {
    /// A number, boolean, atom or family, compared as before.
    Other(Value),
    Str(text::Name),
    /// A tuple or keypath, by its number in [`Namer::seqs`].
    Seq(u64),
}

/// The names of the strings and the numbers of the tuples and keypaths of the keys of one mix.
#[derive(Debug, Default)]
struct Namer {
    text: text::Names,
    /// The number of each tuple (`false`) or keypath (`true`), by the forms of its parts.
    seqs: BTreeMap<(bool, Vec<Canon>), u64>,
    /// The number of each shared tuple met, by its id ([`Value::shared_parts`]). A sequence is
    /// never changed in place and its id is never drawn again, so an id names one sequence.
    seen: HashMap<u64, u64>,
}

impl Namer {
    /// The canonical form of `v`, read on the heap, so a tuple of any depth is read, and each
    /// shared tuple once.
    fn canon(&mut self, v: &Value) -> Canon {
        // The tuples and keypaths being read: each, its parts not yet read, and the forms of
        // those read.
        let mut open: Vec<(&Value, std::slice::Iter<'_, Value>, Vec<Canon>)> = Vec::new();
        let mut next = Some(v);
        loop {
            let c = match next {
                Some(v) => match self.known(v) {
                    Some(c) => c,
                    None => {
                        let (Value::Tuple(items) | Value::Path(items)) = v else {
                            unreachable!("only a sequence is not known at once")
                        };
                        let mut rest = items.as_slice().iter();
                        next = rest.next();
                        open.push((v, rest, Vec::with_capacity(items.len())));
                        continue;
                    }
                },
                None => {
                    let (v, _, parts) = open.pop().expect("a sequence being read");
                    let fresh = self.seqs.len() as u64;
                    let n = *self
                        .seqs
                        .entry((matches!(v, Value::Path(_)), parts))
                        .or_insert(fresh);
                    if let Some((id, _)) = v.shared_parts() {
                        self.seen.insert(id, n);
                    }
                    Canon::Seq(n)
                }
            };
            let Some((_, rest, parts)) = open.last_mut() else {
                return c;
            };
            parts.push(c);
            next = rest.next();
        }
    }

    /// The form of `v` when it is known without reading parts: none for a tuple or keypath
    /// not met before.
    fn known(&mut self, v: &Value) -> Option<Canon> {
        Some(match v {
            Value::Str(s) => Canon::Str(self.text.name(s)),
            Value::Tuple(_) | Value::Path(_) => {
                let (id, _) = v.shared_parts()?;
                Canon::Seq(*self.seen.get(&id)?)
            }
            Value::Bool(_)
            | Value::Int(_)
            | Value::Big(_)
            | Value::Rat(_)
            | Value::Float(_)
            | Value::Float32(_)
            | Value::Atom(_)
            | Value::Family(_) => Canon::Other(v.clone()),
        })
    }
}

impl Key {
    /// `v` as a key, named in `namer`.
    fn new(namer: &Mutex<Namer>, v: &Value) -> Key {
        Key {
            canon: namer.lock().expect("one thread").canon(v),
            value: v.clone(),
        }
    }
}

impl PartialEq for Key {
    fn eq(&self, other: &Key) -> bool {
        self.canon == other.canon
    }
}

impl Eq for Key {}

impl PartialOrd for Key {
    fn partial_cmp(&self, other: &Key) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Key {
    fn cmp(&self, other: &Key) -> std::cmp::Ordering {
        self.canon.cmp(&other.canon)
    }
}

/// A function bound outside a part being mixed, as a part calls it: a lambda that reads its
/// arguments from a port, and the answers given so far, so each call at an argument is run
/// once.
#[derive(Debug)]
struct Stub {
    /// The port the lambda calls. As the name of an atom it is also the token that stands for
    /// the function in a key of another stub's table ([`Port::function`]); a written atom's
    /// name does not start with `#`.
    port: Arc<str>,
    /// `(#0, .., #n) -> port(#0, .., #n)`.
    lam: Shared,
    /// The function's name and term.
    name: Arc<str>,
    known: Shared,
    /// The bindings the term reads, in order, each function among them bound to its stub.
    lets: Vec<(Arc<str>, Shared)>,
    /// The stubs of the functions among them.
    reads: Vec<Arc<Stub>>,
    /// The answer at each argument tuple asked so far.
    table: Mutex<BTreeMap<Key, Said>>,
    /// The names of the strings and tuples of keys ([`Namer`]), shared by every stub and the
    /// mixer of one mix.
    names: Arc<Mutex<Namer>>,
}

impl Stub {
    /// The call of the function at the arguments `key`, under the bindings it reads; each
    /// argument that is the token of a stub of `with` is that stub's lambda, bound to the
    /// token's name.
    fn term_at(&self, key: &Key, with: &[Arc<Stub>]) -> Term {
        let Value::Tuple(args) = &key.value else {
            unreachable!("a stub is asked with the tuple of its arguments")
        };
        let arg = |v: &Value| match token(v) {
            Some(port) => Term::Var(port.clone()),
            None => Term::Lit(v.clone()),
        };
        let f = Shared::new(Term::Var(self.name.clone()));
        let call = Term::App(f, args.iter().map(arg).collect());
        let call = with.iter().fold(call, |body, s| {
            Term::Let(s.port.clone(), s.lam.clone(), Shared::new(body))
        });
        let call = Term::Let(self.name.clone(), self.known.clone(), Shared::new(call));
        self.lets.iter().rev().fold(call, |body, (x, e)| {
            Term::Let(x.clone(), e.clone(), Shared::new(body))
        })
    }

    fn answer(&self, key: &Key) -> Option<Said> {
        self.table.lock().expect("one thread").get(key).cloned()
    }
}

/// Puts in `stub`'s table its answer at `key`, and before it each answer that answer needs.
/// Each run calls the functions it reads through stubs that do not answer a key not yet in
/// their tables; such a run stops, the missing answer is found first, and the run starts
/// again, so the runs do not nest. `with` are the stubs whose tokens `key` holds.
fn fill(stub: &Arc<Stub>, key: &Key, with: Vec<Arc<Stub>>) {
    let mut todo = vec![(stub.clone(), key.clone(), with)];
    while let Some((s, k, with)) = todo.last().cloned() {
        if s.answer(&k).is_some() {
            todo.pop();
            continue;
        }
        let calls = Arc::new(Run {
            stop: true,
            ..Run::default()
        });
        let reads: Vec<Arc<Stub>> = s.reads.iter().chain(&with).cloned().collect();
        let out = run_with(s.term_at(&k, &with), &reads, &calls);
        match calls.need.lock().expect("one thread").take() {
            Some(need) => todo.push(need),
            None => {
                let said = out.map_err(|e| error_as_written(e, &calls));
                s.table.lock().expect("one thread").insert(k, said);
                todo.pop();
            }
        }
    }
}

/// An answer a run needed: the stub, the key it was asked at, and the stubs whose tokens the
/// key holds ([`Port::with`]).
type Need = (Arc<Stub>, Key, Vec<Arc<Stub>>);

/// One run with stubs: the first answer it needed that no table held, with the stubs whose
/// tokens its key holds, when it stops at such an answer (`stop`), and otherwise each call it
/// made, with its arguments and answer, and whether it made a call at an argument holding a
/// function (`function`), which is not logged: a part's memo asks again only calls at data.
#[derive(Debug, Default)]
struct Run {
    need: Mutex<Option<Need>>,
    log: Mutex<Vec<(Probe, Answer)>>,
    function: AtomicBool,
    stop: bool,
    /// The error as written of the failing call a stub answered, when it is known. A port's
    /// error ends the run, so the run ended at that call.
    failed: Mutex<Option<String>>,
}

/// The port of a stub in one run.
#[derive(Debug)]
struct Port {
    stub: Arc<Stub>,
    run: Arc<Run>,
    /// The stubs of the run, by port.
    ports: Arc<BTreeMap<Arc<str>, Arc<Stub>>>,
}

/// The port named by `v` when it is a stub's token: an atom whose name, the port's, starts
/// with `#`, which no written atom's does.
fn token(v: &Value) -> Option<&Arc<str>> {
    match v {
        Value::Atom(a) if a.name.starts_with('#') => Some(&a.name),
        _ => None,
    }
}

impl Port {
    /// The stubs of the run whose tokens are arguments in `key`, or `None` when an argument
    /// is neither such a token nor compared ([`compared`]).
    fn with(&self, key: &Value) -> Option<Vec<Arc<Stub>>> {
        let Value::Tuple(args) = key else {
            unreachable!("a stub is called with the tuple of its arguments")
        };
        let mut with = Vec::new();
        for a in args.iter() {
            match token(a) {
                Some(port) => with.push(self.ports.get(port)?.clone()),
                None if compared(a) => {}
                None => return None,
            }
        }
        Some(with)
    }
}

impl Lookup for Port {
    fn refuses(&self, key: &Value) -> Option<String> {
        let plain = self.with(key).is_some();
        (!plain).then(|| "an argument a key cannot tell apart".into())
    }

    fn calls(&self) -> bool {
        true
    }

    /// The stub's table, keyed by [`Key`], keeps each answer: a key holding a long join is
    /// compared there by its name, where the world's map would compare it byte by byte.
    fn keeps_answers(&self) -> bool {
        true
    }

    /// The token of the stub whose lambda has the body `body`: `port(#0, .., #n)`. A lambda
    /// written in place and a primitive have none, and a call at one stops the run.
    ///
    /// Invariant (item STAGE-stub-called): a stub is given only to a function that calls
    /// nothing through a parameter ([`Reader::called`]), so the run of a stub's answer at a
    /// key holding a token never calls the function the token stands for: it binds the token
    /// to that stub's lambda only to pass it on or give it back as written, and the run calls
    /// only functions whose calls end. If a function that calls through a parameter had a
    /// stub, an answer at its own token, as in `w(w)` with `w = (f) -> f(f)`, would ask itself
    /// again and [`fill`] would not end.
    fn function(&self, body: &Term) -> Option<Value> {
        let Term::App(f, _) = body else {
            return None;
        };
        let Term::Read(port) = &**f else {
            return None;
        };
        self.ports.contains_key(port).then(|| Value::atom(port))
    }

    fn get(&self, value: &Value) -> Result<Value, String> {
        let with = self.with(value).expect("a key the port takes");
        let key = Key::new(&self.stub.names, value);
        let answer = match self.stub.answer(&key) {
            Some(a) => a,
            None if self.run.stop => {
                let need = (self.stub.clone(), key.clone(), with);
                *self.run.need.lock().expect("one thread") = Some(need);
                return Err("an answer not yet known".into());
            }
            None => {
                fill(&self.stub, &key, with.clone());
                self.stub.answer(&key).expect("filled")
            }
        };
        // An answer that cannot be compared is not recorded, and the run fails.
        if answer.as_ref().is_ok_and(|v| !compared(v)) {
            return Err("an answer that cannot be compared".into());
        }
        if !self.run.stop && !with.is_empty() {
            self.run.function.store(true, Ordering::Relaxed);
        } else if !self.run.stop {
            let log = (
                Probe::Call(self.stub.name.clone(), key),
                Answer::Gives(
                    answer
                        .as_ref()
                        .ok()
                        .map(|v| Key::new(&self.stub.names, v).canon),
                ),
            );
            self.run.log.lock().expect("one thread").push(log);
        }
        answer.map_err(|why| {
            *self.run.failed.lock().expect("one thread") = why;
            "the call fails".into()
        })
    }
}

/// A question a part being mixed asked of the scope outside it: what a function gives at a
/// tuple of arguments, or what a binding is, exactly.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Probe {
    Call(Arc<str>, Key),
    Same(Arc<str>),
}

impl Probe {
    /// The name the question is asked of.
    fn name(&self) -> &Arc<str> {
        match self {
            Probe::Call(x, _) | Probe::Same(x) => x,
        }
    }
}

/// The answer to a [`Probe`]: the canonical form of the call's value ([`Key`]), `None` when it
/// fails; or the binding's exact number.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Answer {
    Gives(Option<Canon>),
    Is(Binding),
}

/// What a part asked: a question and its answer, or all that a part held in it asked, as
/// the leaf of that part's tree, which keeps it ([`Leaf::asked`]). A part held in nested
/// parts is so asked once, and each part around it holds one item for it, not a copy of its
/// questions.
#[derive(Clone)]
enum Item {
    One(Probe, Answer),
    Part(usize),
}

/// A node of the tree of the questions a part asked ([`Mixer::memo`]): the part mixed; a
/// question with the node each answer leads to; or a part held in it, by the root of its
/// tree, with the node each leaf of that tree leads to.
enum Node {
    Leaf(Box<Leaf>),
    Ask(Probe, BTreeMap<Answer, usize>),
    Part(usize, BTreeMap<usize, usize>),
}

/// What a part mixed to, and what it asked to mix to that.
struct Leaf {
    out: Shared,
    sum: Summary,
    /// The root of the part's tree.
    root: usize,
    asked: Vec<Item>,
    /// The names `asked` asks of, through the parts it holds too.
    names: Set,
    /// Whether the leaf is reached from `root` by the answers to `asked`
    /// ([`Mixer::remember`]).
    kept: bool,
}

/// What a part held in a node being mixed has asked, in order, of the entries of the scope
/// below `base`, where the part was entered, when the scope's map of names to entries was
/// `stamps`.
struct Watch {
    base: usize,
    stamps: Map,
    seen: BTreeSet<Probe>,
    /// The leaves of the parts held in it whose questions it took as a whole.
    parts: BTreeSet<usize>,
    said: Vec<Item>,
    names: Set,
}

impl Watch {
    fn new(base: usize, stamps: Map) -> Watch {
        Watch {
            base,
            stamps,
            seen: BTreeSet::new(),
            parts: BTreeSet::new(),
            said: Vec::new(),
            names: EMPTY,
        }
    }
}

#[derive(Default)]
struct Mixer {
    scope: Scope,
    report: Report,
    frees: Frees,
    maps: Maps,
    /// The last number given to a build-stage binding ([`Mixer::number`]).
    given: Binding,
    /// The number of each build-stage binding to a literal, by its value.
    literals: BTreeMap<Key, Binding>,
    /// The names of the strings and tuples of keys ([`Key`]), shared with each stub.
    names: Arc<Mutex<Namer>>,
    /// The exact number of each other build-stage binding, by the id of its term and the exact
    /// numbers of the bindings that term reads where it is bound, in the order of their names.
    fines: HashMap<(u64, Vec<Binding>), Binding>,
    /// The number of the functions of one kind: lambda or a name of one, the number of
    /// parameters, and whether their calls are shown to end.
    kinds: HashMap<(bool, usize, bool), Binding>,
    /// The names each lambda, called, calls ([`Reader::called`]), by the lambda's id.
    calls: HashMap<u64, Option<Vec<Arc<str>>>>,
    /// What each part read for [`Mixer::shows_end`] and [`Mixer::number`] needs, kept across
    /// evaluations and calls of [`Mixer::mix_top`], so that each node is read once in the mix.
    reader: Reader,
    /// The ports given to stubs so far.
    ports: u64,
    /// What each part held in a node in the term `mix_top` is mixing became, by the node's id
    /// and the map of the names it reads to their bindings ([`Maps::restrict`]): the root of a
    /// tree in [`Mixer::trie`] that asks what the part asked of the functions it reads
    /// ([`Probe`]) and the parts it holds ([`Item`]), each answer leading to the next question
    /// or to the mixed part. What a
    /// part mixes to depends on nothing else, so a part shared by two places under the same
    /// bindings of its names, or under functions that answer it alike, is mixed once and the
    /// places share the result.
    memo: HashMap<(u64, Map), usize>,
    trie: Vec<Node>,
    /// The names each tree asks of on all its paths, by its root.
    asks: HashMap<usize, Set>,
    /// The leaf each tree's walk reached ([`Mixer::recall`]), by its root and the scope's map
    /// of names to entries restricted to the names the tree asks of: under one such map each
    /// question gets the answer it got, since what a name answers depends only on its entry.
    recalled: HashMap<(usize, Map), usize>,
    /// What each part held in a node now being mixed has asked, innermost last.
    watch: Vec<Watch>,
    /// What each part held inline in a node being mixed reads, and how many positions its
    /// inline parts take, in preorder ([`Mixer::cluster`]).
    arena: Vec<(Summary, usize)>,
    /// The definitions of the unit whose run can stop or not end, by kernel name, as
    /// [`keep_cut_reads`] found them, so that [`Remix::mix`] keeps a cut read as `mix` does.
    runs: HashSet<Arc<str>>,
    /// The names the term [`Mixer::mix_top`] is mixing reads in the parts the build takes:
    /// each part the mix keeps as written or evaluates adds what it reads, and the arms of an
    /// `if` the build does not take add nothing.
    taken: Set,
}

impl Mixer {
    fn push(&mut self, name: Arc<str>, known: Option<Shared>) {
        let reads = known
            .as_ref()
            .map_or(EMPTY, |k| self.frees.summary(Part::held(k)).free);
        let x = self.frees.name(&name);
        let prev = self.scope.top;
        let prev_stamps = self.scope.stamps;
        let mut e = Entry {
            name,
            known: None,
            reads,
            prev,
            prev_stamps,
            arity: None,
            fine: UNKNOWN,
            ends: false,
            call_ends: false,
            cone_ends: false,
            stub: None,
            global: None,
        };
        let b = match &known {
            Some(k) => self.number(&mut e, k),
            None => UNKNOWN,
        };
        if let Some(k) = &known {
            let at = self.scope.len();
            let reads = self.scope.reads(self.frees.names_in(e.reads), at);
            e.global = reads.and_then(|r| self.scope.globals.push(k.clone(), r));
        }
        e.known = known;
        self.scope.top = self.maps.insert(prev, x, b);
        self.scope.stamps = self.maps.insert(prev_stamps, x, self.scope.pushed);
        self.scope.pushed += 1;
        self.scope.push(e);
    }

    /// The number of the entry `e`, bound to the build-stage term `k` and pushed next, and
    /// what else `e` holds of `k`. The number says what mixing can tell apart of the binding,
    /// not when it was pushed. A literal is numbered by its value when the value is compared
    /// in time linear in its memory ([`compared`]), else as any other term. A function, a
    /// lambda or a name of one, is numbered by its kind alone (lambda or name, the number of
    /// parameters, whether its calls end): a part that calls it is keyed by what it asked of it
    /// as well ([`Probe`]), so a part reached under two functions that answer it alike is
    /// mixed once.
    /// Any other term is numbered by `e.fine`, its id and the exact numbers of the bindings it
    /// reads, which are the bindings [`Mixer::eval`] closes it under. Two bindings with one
    /// number, or two functions with one number that answer alike, evaluate alike, so a part
    /// reached under either mixes to one term and is mixed once.
    fn number(&mut self, e: &mut Entry, k: &Shared) -> Binding {
        let at = self.scope.len();
        self.shown(e, k, at);
        let below = |x: &Arc<str>| self.scope.known_below(x, at);
        let reads: Vec<Option<usize>> = self
            .frees
            .names_in(e.reads)
            .into_iter()
            .map(below)
            .collect();
        let at_entry = |j: usize| &self.scope.entries[j];
        e.arity = match &**k {
            Term::Lam(ps, _) => Some(ps.len()),
            Term::Var(y) => below(y).and_then(|j| at_entry(j).arity),
            _ => None,
        };
        e.ends = match &**k {
            Term::PrimFn(_) => true,
            Term::Var(y) => below(y).is_none_or(|j| at_entry(j).ends),
            _ => false,
        };
        if let Term::Lit(v) = &**k
            && compared(v)
        {
            let next = self.given + 1;
            let b = *self
                .literals
                .entry(Key::new(&self.names, v))
                .or_insert(next);
            self.given = self.given.max(b);
            e.fine = b;
            return b;
        }
        let fines = reads
            .iter()
            .map(|j| j.map_or(UNKNOWN, |j| at_entry(j).fine))
            .collect();
        let next = self.given + 1;
        e.fine = *self.fines.entry((k.id(), fines)).or_insert(next);
        self.given = self.given.max(e.fine);
        let Some(arity) = e.arity else {
            return e.fine;
        };
        e.stub = self.stub(e, k, at);
        e.ends = e.stub.is_some();
        let lam = matches!(**k, Term::Lam(..));
        let next = self.given + 1;
        let b = *self.kinds.entry((lam, arity, e.ends)).or_insert(next);
        self.given = self.given.max(b);
        b
    }

    /// Sets `e.call_ends` and `e.cone_ends` for the entry `e`, bound to the build-stage term
    /// `k` and pushed next at position `at`, from the entries below it, so that
    /// [`Mixer::shows_end`] answers what [`ends`] answers of a term closed under the bindings
    /// it needs without building that term.
    fn shown(&mut self, e: &mut Entry, k: &Shared, at: usize) {
        let scope = &self.scope;
        let call_ends = |y: &Arc<str>| {
            let j = scope.known_below(y, at);
            j.is_none_or(|j| scope.entries[j].call_ends)
        };
        e.call_ends = match &**k {
            Term::PrimFn(_) => true,
            Term::Var(y) => call_ends(y),
            Term::Lam(..) => {
                let reader = &mut self.reader;
                let called = self.calls.entry(k.id());
                let called = called.or_insert_with(|| reader.called(k));
                called.as_ref().is_some_and(|c| c.iter().all(call_ends))
            }
            _ => false,
        };
        // A lambda bound and never called need not end; any other binding is evaluated.
        let evaluated = match &**k {
            Term::Lam(..) => true,
            _ => {
                let needs = self.reader.read(Part::held(k));
                needs.is_some_and(|s| self.reader.names_in(s).all(call_ends))
            }
        };
        e.cone_ends = evaluated
            && self.frees.names_in(e.reads).into_iter().all(|y| {
                let j = scope.known_below(y, at);
                j.is_none_or(|j| scope.entries[j].cone_ends)
            });
    }

    /// The stub of the function `e`, bound to `k` at position `at`: `None` unless a call of
    /// it is shown to end, with each function it reads by that function's own stub and each
    /// other binding as it is.
    fn stub(&mut self, e: &Entry, k: &Shared, at: usize) -> Option<Arc<Stub>> {
        let called = match &**k {
            Term::Var(y) => Some(vec![y.clone()]),
            _ => {
                let reader = &mut self.reader;
                let called = self.calls.entry(k.id());
                called.or_insert_with(|| reader.called(k)).clone()
            }
        }?;
        let entries = &self.scope.entries;
        let callee_ends = |y: &Arc<str>| {
            self.scope
                .known_below(y, at)
                .is_none_or(|j| entries[j].ends)
        };
        if !called.iter().all(callee_ends) {
            return None;
        }
        let mut todo: BTreeSet<usize> = self
            .frees
            .names_in(e.reads)
            .into_iter()
            .filter_map(|y| self.scope.known_below(y, at))
            .collect();
        let (mut lets, mut reads) = (Vec::new(), Vec::new());
        while let Some(j) = todo.pop_last() {
            let f = &entries[j];
            let known = f.known.as_ref().expect("a build-stage entry");
            if f.arity.is_some() {
                let s = f.stub.clone()?;
                lets.push((f.name.clone(), s.lam.clone()));
                reads.push(s);
                continue;
            }
            // A binding of another form is evaluated where it is bound, so only these, whose
            // evaluation ends, are kept.
            if !matches!(**known, Term::Lit(_) | Term::PrimFn(_) | Term::Var(_)) {
                return None;
            }
            todo.extend(
                self.frees
                    .names_in(f.reads)
                    .into_iter()
                    .filter_map(|y| self.scope.known_below(y, j)),
            );
            lets.push((f.name.clone(), known.clone()));
        }
        lets.reverse();
        self.ports += 1;
        let port: Arc<str> = format!("#stub{}", self.ports).into();
        let arity = e.arity.expect("a function");
        let params: Vec<Arc<str>> = (0..arity).map(|i| format!("#{i}").into()).collect();
        let args = params.iter().cloned().map(Term::Var).collect();
        let call = Term::App(Shared::new(Term::Read(port.clone())), args);
        Some(Arc::new(Stub {
            port,
            lam: Shared::new(Term::Lam(params, Shared::new(call))),
            name: e.name.clone(),
            known: k.clone(),
            lets,
            reads,
            table: Mutex::default(),
            names: self.names.clone(),
        }))
    }

    fn bind(&mut self, name: Arc<str>, stage: Stage, t: &Shared) {
        let known = (stage == Stage::Build).then(|| t.clone());
        self.push(name, known);
    }

    /// Binds the definition `d` to its term mixed under the scope, by the stage of the mixed
    /// term ([`Mixer::known`]), and gives that term and stage.
    fn bind_mixed(&mut self, d: &Def) -> (Shared, Stage) {
        let mixed = self.mix_top(Part::held(&d.term));
        let term = self.hold(mixed);
        let stage = self.known(&term);
        self.bind(d.kernel.clone(), stage, &term);
        (term, stage)
    }

    /// The stage a name bound to the mixed term `t` has: build when `t` is a literal or a
    /// build-stage function, run when it is left to run, so that nothing evaluates it again.
    fn known(&mut self, t: &Shared) -> Stage {
        match **t {
            Term::Lit(_) => Stage::Build,
            Term::Lam(..) | Term::PrimFn(_) | Term::Var(_) => self.stage(t),
            _ => Stage::Run,
        }
    }

    fn unknown(&mut self, names: &[Arc<str>]) {
        for x in names {
            self.push(x.clone(), None);
        }
    }

    fn lookup(&self, x: &str) -> Option<&Option<Shared>> {
        self.scope.lookup(x)
    }

    fn stage(&mut self, t: &Shared) -> Stage {
        let sum = self.frees.summary(Part::held(t));
        let names = self
            .maps
            .restrict(&self.frees.sets, self.scope.top, sum.free);
        if self.build(sum, names) {
            Stage::Build
        } else {
            Stage::Run
        }
    }

    /// Whether a part that reads `sum` is build-stage, where `names` maps the names it reads
    /// that are in scope to their bindings: it reads no port, each of those bindings is
    /// build-stage, and each name it reads that the scope does not bind is a prelude word.
    fn build(&mut self, sum: Summary, names: Map) -> bool {
        if sum.effects || !self.maps.all_known(names) {
            return false;
        }
        let words = self.frees.nonwords(sum.free);
        let bound = self.maps.restrict(&self.frees.sets, self.scope.top, words);
        self.maps.size(bound) == self.frees.sets.size(words)
    }

    /// The entries the build-stage term `t`, which reads `free`, needs, in position order: the
    /// innermost build-stage entry of each name it reads, and of each name those read, below
    /// them. With `base`, each function below `base` that `t` or an entry from `base` up
    /// reads is not followed but given apart, second, to be called through its stub; the
    /// rest are bindings below `base` that such a function reads by no other path.
    fn needs(&self, free: Set, base: Option<usize>) -> (Vec<usize>, Vec<usize>) {
        let top = self.scope.len();
        let names = |s: Set| self.frees.names_in(s);
        // Each entry needed, with whether `t` or an entry from `base` up reads it.
        let mut todo: BTreeMap<usize, bool> = names(free)
            .into_iter()
            .filter_map(|x| self.scope.known_below(x, top))
            .map(|i| (i, true))
            .collect();
        let (mut lets, mut stubs) = (Vec::new(), Vec::new());
        while let Some((i, first)) = todo.pop_last() {
            let e = &self.scope.entries[i];
            let above = base.is_none_or(|b| i >= b);
            if !above && first && e.arity.is_some() {
                stubs.push(i);
                continue;
            }
            for y in names(e.reads) {
                if let Some(j) = self.scope.known_below(y, i) {
                    *todo.entry(j).or_insert(false) |= above;
                }
            }
            lets.push(i);
        }
        lets.reverse();
        stubs.reverse();
        (lets, stubs)
    }

    /// `t` under the `let`s of the entries at the positions `at`, in order, each function in
    /// `stubs` bound to its stub.
    fn closed(&self, t: &Term, at: &[usize], stubs: &[usize]) -> Term {
        let mut all: Vec<(usize, bool)> = at.iter().map(|&i| (i, false)).collect();
        all.extend(stubs.iter().map(|&i| (i, true)));
        all.sort_unstable();
        all.into_iter().rev().fold(t.clone(), |body, (i, stub)| {
            let e = &self.scope.entries[i];
            let bound = match stub {
                true => e.stub.as_ref().expect("a stub").lam.clone(),
                false => e.known.clone().expect("a build-stage entry"),
            };
            Term::Let(e.name.clone(), bound, Shared::new(body))
        })
    }

    /// The value of the build-stage term `t`, which reads `free`, under the bindings it
    /// needs ([`Mixer::needs`]). While a part held in a node is mixed, each function bound
    /// outside the part that `t` reads is called through its stub, and each call at data, its
    /// arguments and its answer, is recorded as what the part asked ([`Probe::Call`]); when
    /// one of those has no stub, a call's argument holds a function, or the run with stubs
    /// fails, the part is recorded as depending on what each of them is ([`Probe::Same`]), and
    /// `t` gives the error as written the failed run kept ([`error_as_written`]) or, where that
    /// is not known, is evaluated as written.
    // Complexity tradeoff: what is given up is sharing, not exactness. A part that calls a
    // function bound outside it is keyed by what it asked of the function only when the
    // function's calls are shown to end (each function it calls through a name has a stub,
    // and the other bindings it reads are literals, primitives or names), when the calls are
    // made outside a family operation or a `fix` (a pure region, which reads no port), and
    // when each run succeeds with arguments that hold no family and no atom ([`compared`]) and
    // with answers of those kinds (a string of any length, a join or not, is keyed by its name,
    // item STAGE-joined-eq-build); otherwise the
    // part is keyed by what the function is, its term and the bindings it reads, and is mixed
    // once under each such function, as before. A float is keyed by its bits, so `-0.0` and
    // `0.0` are two answers, and an argument that is a function bound to a stub by that stub's
    // token (item STAGE-stub-fast): such a call is answered from the table, and the part
    // is keyed by what each function is, since the memo asks again only calls at data. What
    // is still run as written, in time linear in what the run reaches ([`Mixer::run_under`]):
    // a call inside a pure region, a call whose answer cannot be compared (a family, an atom,
    // or a function), a call at such an argument or at a function no stub stands for
    // (a lambda written in place, a primitive), and a call of a function with no stub. A call
    // whose answer is not yet known runs the function's term with its own reads called
    // through their stubs; a run that meets an answer not yet known stops, that answer is
    // found first, and the run starts again, so a function whose term asks m new answers runs
    // m + 1 times. Why: whether two functions compute the same values is undecidable in
    // general, so a part is keyed by the answers it took, which mixing can compare; a pure
    // region reads no port, and a family's entries are keys; a string is compared by its name
    // ([`Key`]), not its bytes, which for a join may be exponential in its nodes, so how a
    // call stages never switches at a length or at a join (QUESTIONS A7). The
    // runs start again rather than nest, so the thread's stack does not grow with the depth of
    // the functions.
    // Trigger: a part shared below `let`s of functions that differ on each path and are
    // called inside a family operation, through a parameter, or with such an argument; for
    // the restart, a function that calls many earlier functions at many new arguments in one
    // run. On the family of the scaling test below (d nested `if c`s whose arms are
    // `let f = (y) -> f(y) + 1` and `+ 2` over one body, `f(1)` at the bottom) the mixed term
    // has (3d^2 + 17d - 6)/2 nodes, a quadratic the output itself needs: `c` is run-stage,
    // so every path stays; the `if` at depth k (k = 0 to d - 1) is reached under k + 1
    // functions `y + s`, s = k to 2k the sum of the steps above it, and the leftmost literal
    // below it is 1 + s + d - k, so its k + 1 mixed forms differ as terms and no sharing can
    // merge them: the output holds exactly the sum of k + 1 over k, d(d + 1)/2 distinct `if`s
    // (counted by structure at d = 1 to 32), and the node count is 3 times that plus 7d - 3, so
    // it is within a constant factor of what the output needs. Tests:
    // `l01_28_staging::dag::mixing_lets_of_composed_functions_over_one_body_gives_what_the_tree_gives`,
    // `l01_28_staging::dag::mixing_lets_of_composed_functions_over_one_body_scales` (at d and
    // 8d; deferred to plan row STAGE-scaling-10_5 in
    // wt/scratch/deferred-tests/STAGE-scaling-10_5.rs),
    // `l01_28_staging::dag::a_call_at_minus_zero_is_answered_apart_from_zero`,
    // `l01_28_staging::differential::a_part_calling_a_function_at_a_float_zero_gives_each_functions_value`
    // (one part under two functions, keyed by what each gives at `0.0`),
    // `l01_28_staging::cone::calls_at_minus_zero_of_a_long_chain_are_answered_in_linear_time`,
    // `l01_28_staging::cone::calls_passing_functions_of_a_long_chain_are_answered_in_linear_time`
    // (each at n and 8n), `l01_28_staging::dag::calls_at_joins_of_100_and_200_bytes_stage_alike`,
    // `l01_28_staging::cone::calls_at_float_zeros_and_at_functions_give_what_they_give_as_written`
    // and `l01_28_staging::mix::an_evaluation_error_is_left_to_run`. COMPLEXITY.md row F83. A
    // complete solution would read a part's calls inside a pure region through a pure lookup,
    // and key a call at an argument holding a family by a hash-consed form of it.
    // Naive version: a part keyed by what each function is, mixed once per distinct
    // function it reads, O(part × functions) (inferred); used: keyed by the answers taken, mixed
    // once per distinct answers, a function asking m new answers run m + 1 times.
    fn eval(&mut self, t: &Term, free: Set) -> Result<Value, String> {
        let base = self.watch.last().map(|w| w.base);
        let (lets, stubs) = self.needs(free, base);
        if stubs.is_empty() {
            if !self.shows_end(t, free) {
                return Err(FORM.into());
            }
            return run_with(self.closed(t, &lets, &[]), &[], &Arc::default())
                .map_err(|e| e.to_string());
        }
        let entries = &self.scope.entries;
        if stubs.iter().any(|&i| entries[i].stub.is_none()) {
            return self.as_written(t, free, &stubs);
        }
        if !self.shows_end(t, free) {
            return Err(FORM.into());
        }
        let closed = self.closed(t, &lets, &stubs);
        let entries = &self.scope.entries;
        let ports: Vec<Arc<Stub>> = stubs
            .iter()
            .map(|&i| entries[i].stub.clone().expect("a stub"))
            .collect();
        let calls = Arc::new(Run::default());
        let out = run_with(closed, &ports, &calls);
        let log = std::mem::take(&mut *calls.log.lock().expect("one thread"));
        for (p, a) in log {
            self.record(p, a);
        }
        // A call at a function's token is keyed by what each function is, as written.
        if calls.function.load(Ordering::Relaxed) {
            self.same(&stubs);
        }
        match out.map_err(|e| error_as_written(e, &calls)) {
            Ok(v) => Ok(v),
            // The error as written depends on what each function is, as when it is run.
            Err(Some(why)) => {
                self.same(&stubs);
                Err(why)
            }
            Err(None) => self.as_written(t, free, &stubs),
        }
    }

    /// Records that the part being mixed depends on what each function at `stubs` is.
    fn same(&mut self, stubs: &[usize]) {
        for &i in stubs {
            let e = &self.scope.entries[i];
            let (x, fine) = (e.name.clone(), e.fine);
            self.record(Probe::Same(x), Answer::Is(fine));
        }
    }

    /// The value of `t`, which reads `free`, with every binding it needs as written, recorded as
    /// depending on what each function at `stubs` is. A run with stubs that fails where the
    /// error as written is known ([`error_as_written`]) does not come here.
    fn as_written(&mut self, t: &Term, free: Set, stubs: &[usize]) -> Result<Value, String> {
        self.same(stubs);
        if !self.shows_end(t, free) {
            return Err(FORM.into());
        }
        self.run_under(t, free)
    }

    /// The value of the build-stage term `t`, which reads `free`, run as written under the
    /// globals of the scope ([`Evaluator::run_under`]). Each build-stage binding has a position
    /// among them ([`Entry::global`]): every definition and `let` is bound mixed, so a
    /// build-stage binding is a literal, lambda, primitive or name ([`Mixer::known`]), and each
    /// name it reads is such a binding or a prelude word. It gives what the run of `t` closed under the
    /// bindings it needs ([`Mixer::closed`]) gives, since that run's `let`s bind literals,
    /// lambdas, primitives and names alone, each of which gives its value in one step and
    /// cannot fail; and in time linear in `t` and the bindings the run reaches, since a
    /// binding's value is made when the run first reads it.
    fn run_under(&self, t: &Term, free: Set) -> Result<Value, String> {
        let top = self.scope.len();
        let reads = self.scope.reads(self.frees.names_in(free), top);
        let reads =
            reads.expect("each build-stage binding is a literal, lambda, primitive or name");
        let mut ev = Evaluator::new(World::new());
        let out = ev.run_under(t, &self.scope.globals, &reads);
        out.map_err(|e| e.to_string())
    }

    /// Whether [`ends`] would show that the build-stage term `t`, which reads `free`, ends
    /// when closed under the bindings it needs ([`Mixer::needs`]), with or without stubs,
    /// read from what `t` needs and what each entry holds ([`Mixer::shown`]) in time linear in
    /// what `t` reads, not in the bindings it needs. The `let` of each binding the closed
    /// term holds asks that the binding's own evaluation end and that a call of its name end
    /// when the name is called, which are `cone_ends` and `call_ends`. With stubs, a function
    /// bound below the base is replaced by its stub, which ends; it is there only when every
    /// such function has a stub, and a function with a stub has both flags set (its calls
    /// end by `Mixer::stub`, and each binding it reads is a function with a stub or a
    /// literal, primitive or name, each of which ends), so both readings agree.
    fn shows_end(&mut self, t: &Term, free: Set) -> bool {
        let top = self.scope.len();
        let Some(needs) = self.reader.read(Part::inline(t)) else {
            return false;
        };
        let scope = &self.scope;
        let entry = |y: &Arc<str>| scope.known_below(y, top).map(|j| &scope.entries[j]);
        self.reader
            .names_in(needs)
            .all(|y| entry(y).is_none_or(|e| e.call_ends))
            && self
                .frees
                .names_in(free)
                .into_iter()
                .all(|y| entry(y).is_none_or(|e| e.cone_ends))
    }

    /// Records that the part being mixed asked `p` and was told `a`, once.
    fn record(&mut self, p: Probe, a: Answer) {
        let Some(w) = self.watch.last_mut() else {
            return;
        };
        if !w.seen.insert(p.clone()) {
            return;
        }
        let x = self.frees.name(p.name());
        let x = self.frees.sets.one(x);
        w.names = self.frees.sets.union(w.names, x);
        w.said.push(Item::One(p, a));
    }

    /// Records that the part being mixed asked all that the part whose tree ends at `leaf`
    /// asked, once.
    fn record_part(&mut self, leaf: usize) {
        let Some(w) = self.watch.last_mut() else {
            return;
        };
        if !w.parts.insert(leaf) {
            return;
        }
        let Node::Leaf(l) = &self.trie[leaf] else {
            unreachable!("a leaf")
        };
        w.names = self.frees.sets.union(w.names, l.names);
        w.said.push(Item::Part(leaf));
    }

    /// Whether each name of `names` is bound to the entry it was bound to where the part
    /// being mixed was entered, so a question asked of it here, below the part's base, gets
    /// the answer it gets there and asks nothing more.
    fn outside(&mut self, names: Set) -> bool {
        let Some(w) = self.watch.last() else {
            return false;
        };
        let sets = &self.frees.sets;
        let there = self.maps.restrict(sets, w.stamps, names);
        there == self.maps.restrict(sets, self.scope.stamps, names)
    }

    /// Records that the part being mixed asked what the part held in it whose tree ends at
    /// `leaf` asked, here, where that part is mixed or recalled: the leaf itself when each
    /// name it asks of is bound as where the part being mixed was entered, and otherwise each
    /// of its items so, asking again here the questions of names bound in between, which
    /// asks what their bindings ask of the scope outside ([`Mixer::ask`]).
    fn take(&mut self, leaf: usize) {
        if self.watch.is_empty() {
            return;
        }
        let mut todo = vec![Item::Part(leaf)];
        // The leaves whose items were taken one by one: each once, as the parts share them.
        let mut opened = HashSet::new();
        while let Some(item) = todo.pop() {
            match item {
                Item::One(p, a) => {
                    let x = self.frees.name(p.name());
                    let w = self.watch.last().expect("not empty");
                    match self.maps.get(w.stamps, x) == self.maps.get(self.scope.stamps, x) {
                        true => self.record(p, a),
                        false => {
                            self.ask(&p);
                        }
                    }
                }
                Item::Part(at) => {
                    let Node::Leaf(l) = &self.trie[at] else {
                        unreachable!("a leaf")
                    };
                    let (kept, names) = (l.kept, l.names);
                    if kept && self.outside(names) {
                        self.record_part(at);
                    } else if opened.insert(at) {
                        let Node::Leaf(l) = &self.trie[at] else {
                            unreachable!("a leaf")
                        };
                        todo.extend(l.asked.iter().rev().cloned());
                    }
                }
            }
        }
    }

    /// The answer to `p` here, recorded nowhere.
    fn answer(&mut self, p: &Probe) -> Answer {
        let Some(w) = self.watch.last() else {
            return self.ask(p);
        };
        let w = Watch::new(w.base, w.stamps);
        self.watch.push(w);
        let a = self.ask(p);
        self.watch.pop();
        a
    }

    /// The answer to `p` here, recorded as asked by the part being mixed.
    fn ask(&mut self, p: &Probe) -> Answer {
        match p {
            Probe::Call(x, k) => {
                let Value::Tuple(args) = &k.value else {
                    unreachable!("a call is asked with the tuple of its arguments")
                };
                let f = Shared::new(Term::Var(x.clone()));
                let call = Term::App(f, args.iter().cloned().map(Term::Lit).collect());
                let x = self.frees.name(x);
                let free = self.frees.sets.one(x);
                let v = self.eval(&call, free).ok();
                Answer::Gives(v.map(|v| Key::new(&self.names, &v).canon))
            }
            Probe::Same(x) => {
                let top = self.scope.len();
                let Some(i) = self.scope.known_below(x, top) else {
                    return Answer::Is(UNKNOWN);
                };
                // The functions bound outside the part being mixed that what `x` is reads.
                if let Some(base) = self.watch.last().map(|w| w.base) {
                    let mut todo = BTreeSet::from([i]);
                    while let Some(j) = todo.pop_last() {
                        let e = &self.scope.entries[j];
                        if j < base {
                            let (y, fine) = (e.name.clone(), e.fine);
                            self.record(Probe::Same(y), Answer::Is(fine));
                            continue;
                        }
                        let reads = self.frees.names_in(e.reads);
                        todo.extend(
                            reads
                                .into_iter()
                                .filter_map(|y| self.scope.known_below(y, j)),
                        );
                    }
                }
                Answer::Is(self.scope.entries[i].fine)
            }
        }
    }

    /// The leaf the tree of questions of a part, at `root`, leads to here, when the part was
    /// mixed before under functions that answer each question as they answer here. Records
    /// nothing; the caller takes what the leaf asked ([`Mixer::take`]). A node of a part held
    /// in it recalls that part's tree, on an explicit stack, and each tree's walk is kept by
    /// the entries of the names it asks of ([`Mixer::recalled`]), so a part held in many
    /// nested parts is walked once under one scope, not once per part around it.
    fn recall(&mut self, root: usize) -> Option<usize> {
        // Each tree being walked: its root, the key its walk is kept by, and the node reached.
        let mut walks: Vec<(usize, Map, usize)> = Vec::new();
        // The leaf the tree last walked reached, for the node of the tree that asked for it.
        let mut reached = None;
        let start = |m: &mut Mixer, root: usize, walks: &mut Vec<(usize, Map, usize)>| {
            let names = m.asks.get(&root).copied().unwrap_or(EMPTY);
            let key = m.maps.restrict(&m.frees.sets, m.scope.stamps, names);
            match m.recalled.get(&(root, key)) {
                Some(&leaf) => Some(leaf),
                None => {
                    walks.push((root, key, root));
                    None
                }
            }
        };
        if let Some(leaf) = start(self, root, &mut walks) {
            return Some(leaf);
        }
        while let Some(&(root, key, at)) = walks.last() {
            let next = match (&self.trie[at], reached.take()) {
                (Node::Part(_, next), Some(leaf)) => *next.get(&leaf)?,
                (Node::Leaf(_), _) => {
                    self.recalled.insert((root, key), at);
                    walks.pop();
                    reached = Some(at);
                    continue;
                }
                (Node::Ask(p, _), _) => {
                    let p = p.clone();
                    let a = self.answer(&p);
                    let Node::Ask(_, next) = &self.trie[at] else {
                        unreachable!("asked above")
                    };
                    *next.get(&a)?
                }
                (Node::Part(part, _), None) => {
                    let part = *part;
                    reached = start(self, part, &mut walks);
                    continue;
                }
            };
            walks.last_mut().expect("walking").2 = next;
        }
        reached
    }

    /// Remembers that the part held in the node with id `id`, under `names`, mixed to `out`
    /// after it asked what `w` holds, and gives the leaf that keeps it.
    fn remember(&mut self, key: (u64, Map), w: Watch, out: Shared, sum: Summary) -> usize {
        let leaf = self.trie.len();
        self.trie.push(Node::Leaf(Box::new(Leaf {
            out,
            sum,
            root: leaf,
            asked: Vec::new(),
            names: w.names,
            kept: false,
        })));
        let root_of = |trie: &[Node], at: usize| match &trie[at] {
            Node::Leaf(l) => l.root,
            _ => unreachable!("a leaf"),
        };
        let chain = |trie: &mut Vec<Node>, from: &[Item]| {
            from.iter().rev().fold(leaf, |next, item| {
                let node = match item {
                    Item::One(p, a) => Node::Ask(p.clone(), BTreeMap::from([(a.clone(), next)])),
                    Item::Part(at) => Node::Part(root_of(trie, *at), BTreeMap::from([(*at, next)])),
                };
                trie.push(node);
                trie.len() - 1
            })
        };
        let (root, kept) = match self.memo.get(&key) {
            None => {
                let root = chain(&mut self.trie, &w.said);
                self.memo.insert(key, root);
                (root, true)
            }
            Some(&root) => {
                let mut at = root;
                let mut kept = false;
                for (i, item) in w.said.iter().enumerate() {
                    let branch = match (&self.trie[at], item) {
                        (Node::Ask(q, next), Item::One(p, a)) if q == p => {
                            next.get(a).copied().ok_or(())
                        }
                        (Node::Part(r, next), Item::Part(l)) if *r == root_of(&self.trie, *l) => {
                            next.get(l).copied().ok_or(())
                        }
                        _ => break,
                    };
                    match branch {
                        Ok(n) => at = n,
                        Err(()) => {
                            let rest = chain(&mut self.trie, &w.said[i + 1..]);
                            match (&mut self.trie[at], item) {
                                (Node::Ask(_, next), Item::One(_, a)) => {
                                    next.insert(a.clone(), rest)
                                }
                                (Node::Part(_, next), Item::Part(l)) => next.insert(*l, rest),
                                _ => unreachable!("matched above"),
                            };
                            kept = true;
                            break;
                        }
                    }
                }
                (root, kept)
            }
        };
        if kept {
            let names = self.asks.get(&root).copied().unwrap_or(EMPTY);
            let names = self.frees.sets.union(names, w.names);
            self.asks.insert(root, names);
        }
        let Node::Leaf(l) = &mut self.trie[leaf] else {
            unreachable!("pushed above")
        };
        (l.root, l.asked, l.kept) = (root, w.said, kept);
        leaf
    }

    /// `o` held in a node, its summary recorded under the node's id.
    fn hold(&mut self, o: Out) -> Shared {
        match o.term {
            Mixed::Held(s) => s,
            Mixed::Inline(t) => {
                let s = Shared::new(t);
                self.frees.of.insert(s.id(), o.sum);
                s
            }
        }
    }

    /// Adds `free`, what a part the build takes reads, to [`Mixer::taken`]. A union stops where
    /// the two sets share a node ([`Sets::union`]), so a part adding one name reads one path.
    fn read_taken(&mut self, free: Set) {
        self.taken = self.frees.sets.union(self.taken, free);
    }

    /// What the build-stage term `t`, which the build has evaluated, reads on the arms its run
    /// takes: what [`Frees::summary`] gives, except that an `if` outside every binder of `t`
    /// whose condition the build evaluates to a `bool` reads its condition and that one arm.
    /// Under a binder an arm may read the bound name, which the scope cannot tell from an
    /// outer name of the same spelling, so both arms are read there; a condition the build
    /// cannot evaluate reads both arms too. Each part held in a node is walked once.
    // Complexity tradeoff (COMPLEXITY.md TEST-staged): reading `t`'s summary costs one lookup but
    // counts the arm the run leaves as taken; this walk costs O(parts outside binders) plus one
    // evaluation of each condition on the path the run takes, which the run itself evaluates
    // too, so at most twice the run's work on those conditions.
    fn taken_reads(&mut self, t: &Term) -> Set {
        let (mut out, mut seen, mut todo) = (EMPTY, HashSet::new(), vec![t]);
        while let Some(t) = todo.pop() {
            if let Term::If(c, x, y) = t {
                let sum = self.frees.summary(Part::held(c));
                let names = (self.maps).restrict(&self.frees.sets, self.scope.top, sum.free);
                let arm = match self.build(sum, names).then(|| self.eval(c, sum.free)) {
                    Some(Ok(Value::Bool(true))) => Some(x),
                    Some(Ok(Value::Bool(false))) => Some(y),
                    _ => None,
                };
                if let Some(arm) = arm {
                    out = self.frees.sets.union(out, sum.free);
                    if seen.insert(arm.id()) {
                        todo.push(arm);
                    }
                    continue;
                }
            }
            if let Term::Var(x) = t {
                let x = self.frees.name(x);
                let one = self.frees.sets.one(x);
                out = self.frees.sets.union(out, one);
            }
            for (p, names, _) in subs(t) {
                if names.is_empty() {
                    if p.node.is_none_or(|n| seen.insert(n.id())) {
                        todo.push(p.term);
                    }
                    continue;
                }
                let mut free = self.frees.summary(p).free;
                for x in names.iter() {
                    let x = self.frees.name(x);
                    free = self.frees.sets.remove(free, x).unwrap_or(free);
                }
                out = self.frees.sets.union(out, free);
            }
        }
        out
    }

    /// `t` with its build-stage subterms evaluated.
    fn mix_top(&mut self, t: Part<'_>) -> Out {
        self.memo.clear();
        self.trie.clear();
        self.asks.clear();
        self.recalled.clear();
        self.watch.clear();
        self.arena.clear();
        self.frees.of.clear();
        self.taken = EMPTY;
        let site = match t.node {
            Some(s) => Site::Held(s),
            None => {
                // A root held inline has a base too, as one held in a node has when it is
                // entered, so that each evaluation in it calls the functions bound outside it
                // through their stubs rather than closing over all the bindings they need. No
                // part is stored under what the root asked.
                let w = Watch::new(self.scope.len(), self.scope.stamps);
                self.watch.push(w);
                Site::Inline(t.term, self.cluster(t.term))
            }
        };
        self.mix(site)
    }

    /// Puts on the arena, in preorder from the returned position, what the part `t` and each
    /// part held inline in it reads, with how many positions each one's inline parts take.
    /// The parts held in nodes below are read by [`Frees::summary`], once each.
    fn cluster(&mut self, t: &Term) -> usize {
        let base = self.arena.len();
        let mut terms = Vec::new();
        let mut todo = vec![t];
        while let Some(u) = todo.pop() {
            terms.push(u);
            let parts = subs(u);
            todo.extend(
                parts
                    .iter()
                    .rev()
                    .filter_map(|(p, ..)| p.node.is_none().then_some(p.term)),
            );
        }
        self.arena
            .extend(terms.iter().map(|_| (Summary::default(), 1)));
        let mut sums = Vec::new();
        for (i, u) in terms.iter().enumerate().rev() {
            let at = base + i;
            let mut next = at + 1;
            sums.clear();
            for (p, ..) in subs(u) {
                match p.node {
                    Some(s) => sums.push(self.frees.summary(Part::held(s))),
                    None => {
                        let (sum, size) = self.arena[next];
                        sums.push(sum);
                        next += size;
                    }
                }
            }
            let sum = self.frees.combine(u, &sums);
            self.arena[at] = (sum, next - at);
        }
        base
    }

    /// The parts of `t`, whose inline parts are on the arena from `at`, as sites.
    fn sites<'t>(&self, t: &'t Term, at: usize) -> Vec<(Site<'t>, Names<'t>)> {
        let mut next = at + 1;
        subs(t)
            .into_iter()
            .map(|(p, names, _)| {
                let site = match p.node {
                    Some(s) => Site::Held(s),
                    None => {
                        let site = Site::Inline(p.term, next);
                        next += self.arena[next].1;
                        site
                    }
                };
                (site, names)
            })
            .collect()
    }

    /// The part at `site` with its build-stage subterms evaluated. The parts still to mix and
    /// the terms to build from them wait on heap stacks, so a deep term does not grow the
    /// thread's stack; the walk meets the parts in the order of the recursion it replaces, so
    /// the scope and the report change in the same order. A part held in a node is mixed once
    /// under each map of the names it reads to their bindings, and every place that reaches
    /// it again under that map shares the result, so the parts mixed, and the mixed term's
    /// distinct parts, are not more than the term's distinct parts times the maps each is
    /// reached under (COMPLEXITY.md row F83).
    // Complexity tradeoff (COMPLEXITY.md row F83): the naive mix reads the term as a tree, so
    // a part shared by two places is mixed once per path, O(2^d) for d levels that each share
    // one part. Used: a memo by (node id, map of the names the part reads), O(Q log Q) for Q
    // such pairs, and heap stacks in place of recursion. Tradeoffs: the memo holds one mixed
    // part per pair until the mix ends; a part reached under many maps is mixed once per map.
    fn mix(&mut self, site: Site<'_>) -> Out {
        let mut todo = vec![Mix::Part(site)];
        let mut done: Vec<Out> = Vec::new();
        while let Some(job) = todo.pop() {
            match job {
                Mix::Part(s) => self.enter(s, &mut todo, &mut done),
                Mix::Under(names, s) => {
                    let n = self.scope.len();
                    self.unknown(&names);
                    todo.extend([Mix::Truncate(n), Mix::Part(s)]);
                }
                Mix::Truncate(n) => self.scope.truncate(n),
                Mix::Let(t, body) => {
                    let Term::Let(x, ..) = t else {
                        unreachable!("only a `let` binds its name")
                    };
                    let e = done.pop().expect("the bound term");
                    let e = self.hold(e);
                    let stage = self.known(&e);
                    self.bind(x.clone(), stage, &e);
                    todo.extend([Mix::LetBody(t, e), Mix::Part(body)]);
                }
                Mix::LetBody(t, e) => {
                    let Term::Let(x, ..) = t else {
                        unreachable!("only a `let` binds its name")
                    };
                    let body = done.pop().expect("the body");
                    self.scope.pop();
                    let x = self.frees.name(x);
                    let read = self.frees.sets.contains(body.sum.free, x);
                    done.push(if matches!(*e, Term::Lit(_)) && !read {
                        body
                    } else {
                        let sum = self.frees.summary(Part::held(&e));
                        let e = Out {
                            term: Mixed::Held(e),
                            sum,
                        };
                        self.build_from(t, vec![e, body])
                    });
                }
                Mix::If(t, x, y) => {
                    let c = done.pop().expect("the condition");
                    match c.term() {
                        Term::Lit(Value::Bool(true)) => todo.push(Mix::Part(x)),
                        Term::Lit(Value::Bool(false)) => todo.push(Mix::Part(y)),
                        Term::Lit(Value::Atom(_)) => done.push(c),
                        _ => todo.extend([Mix::IfBranches(t, c), Mix::Part(y), Mix::Part(x)]),
                    }
                }
                Mix::IfBranches(t, c) => {
                    let y = done.pop().expect("the second branch");
                    let x = done.pop().expect("the first branch");
                    let built = self.build_from(t, vec![c, x, y]);
                    done.push(built);
                }
                Mix::Build(t, k) => {
                    let parts = done.split_off(done.len() - k);
                    let built = self.build_from(t, parts);
                    done.push(built);
                }
                Mix::Store(id, names) => {
                    let out = done.pop().expect("the part mixed");
                    let sum = out.sum;
                    let s = self.hold(out);
                    let w = self.watch.pop().expect("pushed on entering the part");
                    let leaf = self.remember((id, names), w, s.clone(), sum);
                    // What the part asked of the scope outside it, the part that holds it
                    // asked too, of the scope outside that one.
                    self.take(leaf);
                    done.push(Out {
                        term: Mixed::Held(s),
                        sum,
                    });
                }
            }
        }
        done.pop().expect("the mixed term")
    }

    /// Mixes the part at `site`: puts it on `done` when it is a leaf, is evaluated here or
    /// was mixed before under the same bindings of its names, and otherwise puts on `todo` the
    /// steps that mix its parts and build it from them.
    fn enter<'t>(&mut self, site: Site<'t>, todo: &mut Vec<Mix<'t>>, done: &mut Vec<Out>) {
        let (t, held, sum, at) = match site {
            Site::Held(s) => (&**s, Some(s), self.frees.summary(Part::held(s)), None),
            Site::Inline(t, at) => (t, None, self.arena[at].0, Some(at)),
        };
        let as_written = || Out {
            term: match held {
                Some(s) => Mixed::Held(s.clone()),
                None => Mixed::Inline(t.clone()),
            },
            sum,
        };
        let function = |t: &Term| matches!(t, Term::Lam(..) | Term::PrimFn(_));
        let value = match t {
            Term::Lit(_) | Term::PrimFn(_) | Term::Lam(..) => false,
            Term::Var(x) => matches!(self.lookup(x), Some(Some(e)) if !function(e)),
            _ => true,
        };
        // A name kept here is bound to no literal (one bound to a literal is a value, computed
        // below), so it does not keep a definition `Let` would drop.
        // A port read is never build-stage.
        let leaf = matches!(t, Term::Lit(_) | Term::Var(_) | Term::PrimFn(_));
        if (!value && leaf) || matches!(t, Term::Read(_)) {
            self.read_taken(sum.free);
            done.push(as_written());
            return;
        }
        let names = self
            .maps
            .restrict(&self.frees.sets, self.scope.top, sum.free);
        if let Some(s) = held {
            let root = self.memo.get(&(s.id(), names)).copied();
            if let Some(leaf) = root.and_then(|at| self.recall(at)) {
                self.take(leaf);
                let Node::Leaf(l) = &self.trie[leaf] else {
                    unreachable!("a leaf")
                };
                done.push(Out {
                    term: Mixed::Held(l.out.clone()),
                    sum: l.sum,
                });
                return;
            }
            let w = Watch::new(self.scope.len(), self.scope.stamps);
            self.watch.push(w);
            todo.push(Mix::Store(s.id(), names));
        }
        if value && self.build(sum, names) {
            done.push(match self.eval(t, sum.free) {
                Ok(v) => {
                    let read = self.taken_reads(t);
                    self.read_taken(read);
                    Out {
                        term: Mixed::Inline(Term::Lit(v)),
                        sum: Summary::default(),
                    }
                }
                Err(why) => {
                    self.read_taken(sum.free);
                    // The term itself, not its text: printing a term with shared parts within
                    // O(n log n) is the ledger item STAGE-print.
                    let left = match held {
                        Some(s) => s.clone(),
                        None => Shared::new(t.clone()),
                    };
                    self.report.left.push((left, why));
                    as_written()
                }
            });
            return;
        }
        let at = match at {
            Some(at) => at,
            None => self.cluster(t),
        };
        let mut parts = self.sites(t, at);
        match t {
            // A recursion's binders are left as written; recursion arrives at L6.
            Term::Var(_) | Term::Fix { .. } => {
                self.read_taken(sum.free);
                done.push(as_written());
            }
            Term::Lam(..) | Term::Fam { .. } | Term::Match(..) => {
                todo.push(Mix::Build(t, parts.len()));
                todo.extend(
                    parts
                        .into_iter()
                        .rev()
                        .map(|(s, names)| match names.is_empty() {
                            true => Mix::Part(s),
                            false => Mix::Under(names, s),
                        }),
                );
            }
            Term::Let(x, e, b) => {
                let (body, _) = parts.pop().expect("the body");
                let bound = self.frees.summary(Part::held(e));
                let names = self
                    .maps
                    .restrict(&self.frees.sets, self.scope.top, bound.free);
                let name = self.frees.name(x);
                let read = self.frees.summary(Part::held(b)).free;
                let read = self.frees.sets.contains(read, name);
                if self.build(bound, names) && !read {
                    // Not an arm the build leaves out: the bound term is read as taken.
                    self.read_taken(bound.free);
                    self.report
                        .unread
                        .push(crate::defs::written_name(x).to_string());
                    todo.push(Mix::Part(body));
                } else {
                    let (e, _) = parts.pop().expect("the bound term");
                    todo.extend([Mix::Let(t, body), Mix::Part(e)]);
                }
            }
            Term::If(..) => {
                let [(c, _), (x, _), (y, _)] = <[_; 3]>::try_from(parts).ok().expect("three parts");
                todo.extend([Mix::If(t, x, y), Mix::Part(c)]);
            }
            _ => {
                todo.push(Mix::Build(t, parts.len()));
                todo.extend(parts.into_iter().rev().map(|(s, _)| Mix::Part(s)));
            }
        }
    }

    /// The term of the form of `t` whose parts are `parts`, mixed, in the order [`subs`]
    /// gives them.
    fn build_from(&mut self, t: &Term, parts: Vec<Out>) -> Out {
        let sums: Vec<Summary> = parts.iter().map(|o| o.sum).collect();
        let mut parts = parts.into_iter();
        let mut next = || parts.next().expect("each part, mixed");
        let built = match t {
            Term::Lam(ps, _) => Term::Lam(ps.clone(), self.hold(next())),
            Term::App(_, args) => {
                let g = self.hold(next());
                Term::App(g, args.iter().map(|_| inline(next())).collect())
            }
            Term::Prim(p, args) => Term::Prim(*p, args.iter().map(|_| inline(next())).collect()),
            Term::Let(x, ..) => {
                let e = self.hold(next());
                Term::Let(x.clone(), e, self.hold(next()))
            }
            Term::If(..) => {
                let c = self.hold(next());
                let x = self.hold(next());
                Term::If(c, x, self.hold(next()))
            }
            Term::Match(_, arms) => {
                let s = self.hold(next());
                Term::Match(
                    s,
                    arms.iter()
                        .map(|(p, _)| (p.clone(), inline(next())))
                        .collect(),
                )
            }
            Term::Fam { var, .. } => {
                let domain = self.hold(next());
                Term::Fam {
                    domain,
                    var: var.clone(),
                    body: self.hold(next()),
                }
            }
            Term::Reindex { witness, .. } => {
                let family = self.hold(next());
                let kf = self.hold(next());
                Term::Reindex {
                    family,
                    kf,
                    vf: self.hold(next()),
                    witness: witness.clone(),
                }
            }
            Term::Discard { .. } => {
                let family = self.hold(next());
                Term::Discard {
                    family,
                    sel: self.hold(next()),
                }
            }
            Term::Fold {
                identity,
                depth,
                ev,
                ..
            } => {
                let family = self.hold(next());
                let op = self.hold(next());
                Term::Fold {
                    family,
                    op,
                    identity: identity.as_ref().map(|_| self.hold(next())),
                    depth: *depth,
                    ev: ev.clone(),
                }
            }
            Term::Gen { pos, .. } => {
                let init = self.hold(next());
                let step = self.hold(next());
                Term::Gen {
                    init,
                    step,
                    guard: self.hold(next()),
                    pos: *pos,
                }
            }
            Term::Push(port, _) => Term::Push(port.clone(), self.hold(next())),
            Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) | Term::Fix { .. } => {
                unreachable!("leaves and recursions are kept as written")
            }
        };
        zed_kernel::sites::inherit(t, &built);
        let sum = self.frees.combine(&built, &sums);
        Out {
            term: Mixed::Inline(built),
            sum,
        }
    }
}

/// A step of [`Mixer::mix`], on its heap stack.
enum Mix<'t> {
    /// Mix the part at the site.
    Part(Site<'t>),
    /// Mix the part at the site with `names` bound to values not known at build.
    Under(Names<'t>, Site<'t>),
    /// Unbind all but the first `n` names in scope.
    Truncate(usize),
    /// The bound term of the `let` `t`, mixed, is on the results: bind its name and mix the
    /// body, at the site.
    Let(&'t Term, Site<'t>),
    /// The body of the `let` `t`, binding the name to the mixed term, is on the results:
    /// unbind the name and build the `let`, or drop it when nothing reads it.
    LetBody(&'t Term, Shared),
    /// The condition of the `if` `t`, mixed, is on the results: mix the branch it chooses, or
    /// both, at the sites.
    If(&'t Term, Site<'t>, Site<'t>),
    /// Both branches of the `if` `t` with the condition, mixed, are on the results: build it.
    IfBranches(&'t Term, Out),
    /// The `k` parts of `t`, mixed, are on the results: build it.
    Build(&'t Term, usize),
    /// The part held in the node with this id, mixed under this map of the names it reads to
    /// their bindings, is on the results: hold it in a node and remember it.
    Store(u64, Map),
}
