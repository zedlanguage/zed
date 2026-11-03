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
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Pattern, Term, Value, World};

use crate::elab::{Def, Unit};
use crate::interp;

/// When a term is evaluated.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Stage {
    /// By the build.
    Build,
    /// By the run.
    Run,
}

/// What `mix` did.
#[derive(Clone, Default, PartialEq, Eq, Debug)]
pub struct Report {
    /// The definitions the build evaluated, by source name.
    pub built: Vec<String>,
    /// The definitions nothing demanded, which the build did not evaluate.
    pub unread: Vec<String>,
    /// The build-stage terms left to run, each printed with why.
    pub left: Vec<(String, String)>,
}

/// The names `t` reads and does not bind.
pub fn free(t: &Term) -> BTreeSet<Arc<str>> {
    let mut out = BTreeSet::new();
    free_in(t, &mut BTreeMap::new(), &mut out);
    out
}

/// The names bound around a subterm, each with how many binders bind it.
type Bound = BTreeMap<Arc<str>, usize>;

fn free_in(t: &Term, bound: &mut Bound, out: &mut BTreeSet<Arc<str>>) {
    let mut under = |names: &[Arc<str>], t: &Term, bound: &mut Bound| {
        for x in names {
            *bound.entry(x.clone()).or_default() += 1;
        }
        free_in(t, bound, out);
        for x in names {
            match bound.get_mut(x) {
                Some(1) => {
                    bound.remove(x);
                }
                Some(k) => *k -= 1,
                None => unreachable!("bound above"),
            }
        }
    };
    match t {
        Term::Lit(_) | Term::PrimFn(_) | Term::Read(_) => {}
        Term::Var(x) => {
            if !bound.contains_key(x) {
                out.insert(x.clone());
            }
        }
        Term::Lam(ps, b) => under(ps, b, bound),
        Term::Let(x, e, b) => {
            under(&[], e, bound);
            under(std::slice::from_ref(x), b, bound);
        }
        Term::Match(s, arms) => {
            under(&[], s, bound);
            for (p, a) in arms {
                under(&binds(p), a, bound);
            }
        }
        Term::Fam { domain, var, body } => {
            under(&[], domain, bound);
            under(std::slice::from_ref(var), body, bound);
        }
        Term::Fix {
            init,
            step,
            this,
            key,
            kind,
            ..
        } => {
            under(&[], init, bound);
            let names = [this.clone(), key.clone()];
            under(&names, step, bound);
            if let zed_kernel::FixKind::Lattice { join } = kind {
                under(&names, join, bound);
            }
        }
        _ => {
            for c in children(t) {
                under(&[], c, bound);
            }
        }
    }
}

/// The subterms of a term that binds nothing.
fn children(t: &Term) -> Vec<&Term> {
    match t {
        Term::App(f, args) => std::iter::once(&**f).chain(args).collect(),
        Term::Prim(_, args) => args.iter().collect(),
        Term::If(c, a, b) => vec![c, a, b],
        Term::Reindex { family, kf, vf, .. } => vec![family, kf, vf],
        Term::Discard { family, sel } => vec![family, sel],
        Term::Fold {
            family,
            op,
            identity,
            ..
        } => [family, op]
            .into_iter()
            .chain(identity)
            .map(|t| &**t)
            .collect(),
        Term::Gen {
            init, step, guard, ..
        } => vec![init, step, guard],
        Term::Push(_, t) => vec![t],
        _ => Vec::new(),
    }
}

/// Whether `t` is shown to end by its form (docs/thresholds.md, replacement 6): it has no
/// `fix` or `gen`, and every function it calls, or hands to a family operation, is a
/// primitive, a lambda whose body ends, or a name a `let` binds to one. A `let` binds a name
/// only in its body, so such calls nest no deeper than the term; a call through a parameter
/// or a pattern variable, as in `w(w)`, is not shown to end. Free names are prelude words,
/// which are primitives.
///
/// The term is read as the graph of its distinct parts: a part shared by two places (one
/// `Arc` reached twice) is read once, so the time is near the number of distinct parts, not
/// the size of the term unshared (COMPLEXITY.md row ENDS). Each part is read once whatever
/// names are bound around it: what it needs of them is the set of names it calls that must
/// each be free or bound by `let` to a function that ends ([`Needs`]), and the binder of a
/// name reads that set. A part shared under two bindings of a name it calls so gives each
/// place its own answer.
///
/// Complexity tradeoff: a term that ends but whose form does not show it (recursion, `fix`,
/// `gen`, a call through a parameter) is treated as possibly not ending: the build stage
/// leaves it to run time ("its form does not show that it ends"), and enumeration and `@exact`
/// skip it. Why: whether a term ends is undecidable, and running it under a step count would
/// switch behavior at a size. Trigger: any of those forms in the term or in a function it
/// calls. Tests:
/// `l01_28_staging::mix::a_term_whose_form_does_not_show_it_ends_is_left_to_run`,
/// `l01_28_staging::mix::a_term_whose_form_shows_it_ends_is_built_with_no_fuel`.
/// COMPLEXITY.md row C20 (docs/thresholds.md replacement 6). A complete solution cannot
/// exist; a stronger sound one would add a termination proof by decreasing measures
/// (size-change termination, PSPACE-complete in the call graph).
pub fn ends(t: &Term) -> bool {
    Reader::default().read(t).is_some()
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
    /// The number of each part read. A part is found by its address while the term is held
    /// borrowed, so no address outlives the reading and none is reused within it; results are
    /// kept by number.
    ids: HashMap<*const Term, usize>,
    names: HashMap<Arc<str>, Name>,
    sets: Sets,
}

impl Reader {
    /// What `root` needs. The parts are read with an explicit stack, each after its own parts.
    fn read(&mut self, root: &Term) -> Needs {
        let mut todo = vec![(root, false)];
        while let Some((t, parts_read)) = todo.pop() {
            if self.ids.contains_key(&(t as *const Term)) {
                continue;
            }
            if parts_read {
                let needs = self.needs_of(t);
                self.ids.insert(t, self.needs.len());
                self.needs.push(needs);
            } else {
                todo.push((t, true));
                each_part(t, &mut todo);
            }
        }
        self.got(root)
    }

    /// What the part `t`, already read, needs.
    fn got(&self, t: &Term) -> Needs {
        self.needs[self.ids[&(t as *const Term)]]
    }

    fn name(&mut self, x: &Arc<str>) -> Name {
        if let Some(&n) = self.names.get(x) {
            return n;
        }
        let n = self.names.len() as Name;
        self.names.insert(x.clone(), n);
        n
    }

    /// What a term needs whose parts need `a` and `b`: both.
    fn and(&mut self, a: Needs, b: Needs) -> Needs {
        Some(self.sets.union(a?, b?))
    }

    /// What `t` needs, its parts read.
    fn needs_of(&mut self, t: &Term) -> Needs {
        match t {
            Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => Some(EMPTY),
            Term::Fix { .. } | Term::Gen { .. } => None,
            Term::Lam(ps, b) => self.under(ps, b),
            Term::App(f, args) => {
                let mut out = self.callee(f);
                for a in args {
                    out = self.and(out, self.got(a));
                }
                out
            }
            Term::Prim(_, args) => {
                let mut out = Some(EMPTY);
                for a in args {
                    out = self.and(out, self.got(a));
                }
                out
            }
            Term::Let(x, e, b) => {
                // A lambda bound and never called need not end; any other binding is evaluated.
                let evaluated = match &**e {
                    Term::Lam(..) => Some(EMPTY),
                    _ => self.got(e),
                };
                let x = self.name(x);
                let mut body = self.got(b);
                if let Some(rest) = body.and_then(|b| self.sets.remove(b, x)) {
                    let callee = self.callee(e);
                    body = self.and(Some(rest), callee);
                }
                self.and(body, evaluated)
            }
            Term::If(c, a, b) => {
                let ca = self.and(self.got(c), self.got(a));
                self.and(ca, self.got(b))
            }
            Term::Match(s, arms) => {
                let mut out = self.got(s);
                for (p, a) in arms {
                    let arm = self.under(&binds(p), a);
                    out = self.and(out, arm);
                }
                out
            }
            Term::Fam { domain, var, body } => {
                let body = self.under(std::slice::from_ref(var), body);
                self.and(self.got(domain), body)
            }
            Term::Reindex { family, kf, vf, .. } => {
                let (k, v) = (self.callee(kf), self.callee(vf));
                let kv = self.and(k, v);
                self.and(self.got(family), kv)
            }
            Term::Discard { family, sel } => {
                let sel = self.callee(sel);
                self.and(self.got(family), sel)
            }
            Term::Fold {
                family,
                op,
                identity,
                ..
            } => {
                let op = self.callee(op);
                let out = self.and(self.got(family), op);
                match identity {
                    Some(i) => self.and(out, self.got(i)),
                    None => out,
                }
            }
            Term::Push(_, t) => self.got(t),
        }
    }

    /// What `f`, in the position of a function called, needs to be one that ends: a primitive
    /// ends, a lambda when its body does, a name when it is free or bound to one that ends.
    fn callee(&mut self, f: &Term) -> Needs {
        match f {
            Term::PrimFn(_) => Some(EMPTY),
            Term::Lam(..) => self.got(f),
            Term::Var(x) => {
                let x = self.name(x);
                Some(self.sets.one(x))
            }
            _ => None,
        }
    }

    /// What `body`, read, needs with `names` bound around it to values not known to be
    /// functions that end.
    fn under(&mut self, names: &[Arc<str>], body: &Term) -> Needs {
        let body = self.got(body)?;
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
///
/// Complexity tradeoff: the time of a union is bounded by the number of pairs of nodes it reads
/// that no earlier union read, not by the sizes of its sets, and no bound in the size of the
/// term is proved for that number: a term whose parts need many sets that share few nodes
/// pairwise could make it near the product of their sizes. Why: the sets are the answer the
/// reading of each part must carry so that it is read once, and hash-consed tries with a memo
/// of the pairs joined make the common case, sets that mostly agree, cost a path. Trigger: many
/// distinct parts calling many distinct names whose sets are joined in ways unlike those of a
/// program's nesting. Tests: the four scaling tests in `l01_28_staging::ends`, each at k and 8k,
/// one of which fails at 60 s with the memo of pairs removed. COMPLEXITY.md row ENDS. A complete
/// solution would bound the pairs read, for instance by reading each binder only against the
/// one name it binds (a membership query per binder on a persistent structure built once per
/// part), which needs the parts' sets never to be materialized.
struct Sets {
    nodes: Vec<SetNode>,
    made: HashMap<SetNode, Set>,
    /// The union of each pair of sets joined, the smaller number first.
    unions: HashMap<(Set, Set), Set>,
}

impl Default for Sets {
    fn default() -> Self {
        Sets {
            nodes: vec![SetNode::Empty],
            made: HashMap::from([(SetNode::Empty, EMPTY)]),
            unions: HashMap::new(),
        }
    }
}

/// The bits of `x` above `bit`.
fn above(x: Name, bit: Name) -> Name {
    x & !(bit | (bit - 1))
}

impl Sets {
    fn make(&mut self, n: SetNode) -> Set {
        let Sets { nodes, made, .. } = self;
        *made.entry(n).or_insert_with(|| {
            nodes.push(n);
            (nodes.len() - 1) as Set
        })
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
fn each_part<'t>(t: &'t Term, todo: &mut Vec<(&'t Term, bool)>) {
    let mut part = |p: &'t Term| todo.push((p, false));
    let lam = |g: &'t Term| matches!(g, Term::Lam(..)).then_some(g);
    match t {
        Term::Lit(_)
        | Term::Var(_)
        | Term::PrimFn(_)
        | Term::Read(_)
        | Term::Fix { .. }
        | Term::Gen { .. } => {}
        Term::Lam(_, b) | Term::Push(_, b) => part(b),
        Term::App(g, args) => lam(g).into_iter().chain(args).for_each(part),
        Term::Prim(_, args) => args.iter().for_each(part),
        Term::Let(_, e, b) => [e, b].into_iter().for_each(|p| part(p)),
        Term::If(c, a, b) => [c, a, b].into_iter().for_each(|p| part(p)),
        Term::Match(s, arms) => std::iter::once(&**s)
            .chain(arms.iter().map(|(_, a)| a))
            .for_each(part),
        Term::Fam { domain, body, .. } => [domain, body].into_iter().for_each(|p| part(p)),
        Term::Reindex { family, kf, vf, .. } => std::iter::once(&**family)
            .chain(lam(kf))
            .chain(lam(vf))
            .for_each(part),
        Term::Discard { family, sel } => std::iter::once(&**family).chain(lam(sel)).for_each(part),
        Term::Fold {
            family,
            op,
            identity,
            ..
        } => std::iter::once(&**family)
            .chain(lam(op))
            .chain(identity.as_deref())
            .for_each(part),
    }
}

/// The names `p` binds.
fn binds(p: &Pattern) -> Vec<Arc<str>> {
    match p {
        Pattern::Bind(x) => vec![x.clone()],
        Pattern::Atom(_, ps) | Pattern::Tuple(ps) => ps.iter().flat_map(binds).collect(),
        Pattern::Fields(_, fs) => fs.iter().flat_map(|(_, p)| binds(p)).collect(),
        _ => Vec::new(),
    }
}

/// Whether `t` reads or writes a port.
fn effects(t: &Term) -> bool {
    match t {
        Term::Read(_) | Term::Push(..) => true,
        Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) => false,
        Term::Lam(_, b) => effects(b),
        Term::Let(_, e, b) => effects(e) || effects(b),
        Term::Match(s, arms) => effects(s) || arms.iter().any(|(_, a)| effects(a)),
        Term::Fam { domain, body, .. } => effects(domain) || effects(body),
        Term::Fix { init, step, .. } => effects(init) || effects(step),
        _ => children(t).into_iter().any(effects),
    }
}

/// The stage of each definition of `unit`, by source name, in order.
pub fn color(unit: &Unit) -> Vec<(String, Stage)> {
    let mut m = Mixer::default();
    unit.defs
        .iter()
        .map(|d| {
            let stage = m.stage(&d.term);
            m.bind(d.kernel.clone(), stage, &d.term);
            (d.name.clone(), stage)
        })
        .collect()
}

/// `unit` with its demanded build-stage terms evaluated, keeping the definitions `roots`
/// and the tests read.
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
    /// apart from those `t` does not read. It costs the mixing of `t` alone.
    pub fn mix(&mut self, t: &Term) -> Term {
        let out = self.m.mix_top(t);
        self.m.report = Report::default();
        out
    }
}

fn mix_keeping(unit: &Unit, roots: &[&str]) -> (Unit, Mixer) {
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
    for d in unit.defs.iter().rev() {
        if demanded.contains(&d.kernel) {
            demanded.extend(free(&d.term));
        }
    }
    let mut m = Mixer::default();
    let mut out = Unit {
        defs: Vec::new(),
        tests: unit.tests.clone(),
    };
    for d in &unit.defs {
        if !demanded.contains(&d.kernel) {
            m.report.unread.push(d.name.clone());
            continue;
        }
        let term = Arc::new(m.mix_top(&d.term));
        if matches!(*term, Term::Lit(_)) && term != d.term {
            m.report.built.push(d.name.clone());
        }
        let stage = m.known(&term);
        m.bind(d.kernel.clone(), stage, &term);
        out.defs.push(Def {
            name: d.name.clone(),
            kernel: d.kernel.clone(),
            term,
            first_order: d.first_order,
        });
    }
    (out, m)
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
                return Choice::Keep(format!("the domain `{t}` is not known to be finite"));
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
/// every definition bound by its stage. Splitting `k` functions then costs one mix of the
/// unit and `k` mixes of their bodies, where each split mixed the whole unit again.
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
        let (mixed, _) = mix(unit, &roots);
        let mut calls: HashMap<(Arc<str>, usize), BTreeSet<Value>> = HashMap::new();
        let mut todo: Vec<&Term> = mixed.defs.iter().map(|d| &*d.term).collect();
        while let Some(t) = todo.pop() {
            if let Term::App(g, args) = t
                && let Term::Var(f) = &**g
            {
                for (i, x) in args.iter().enumerate() {
                    if let Term::Lit(v) = x {
                        calls.entry((f.clone(), i)).or_default().insert(v.clone());
                    }
                }
            }
            match t {
                Term::Lam(_, b) => todo.push(b),
                Term::Let(_, e, b) => todo.extend([&**e, &**b]),
                Term::Match(e, arms) => {
                    todo.push(e);
                    todo.extend(arms.iter().map(|(_, a)| a));
                }
                Term::Fam { domain, body, .. } => todo.extend([&**domain, &**body]),
                Term::Fix { init, step, .. } => todo.extend([&**init, &**step]),
                _ => todo.extend(children(t)),
            }
        }
        let mut cases: HashMap<(&'u str, usize), BTreeSet<Value>> = HashMap::new();
        for t in unit.tests.iter() {
            for (i, x) in t.args.iter().enumerate() {
                if let Term::Lit(v) = x {
                    let key = (t.function.as_str(), i);
                    cases.entry(key).or_default().insert(v.clone());
                }
            }
        }
        let mut mixer = Mixer::default();
        for d in &unit.defs {
            let stage = mixer.stage(&d.term);
            mixer.bind(d.kernel.clone(), stage, &d.term);
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
            m.bind(p.clone(), Stage::Build, &Arc::new(Term::Lit(v.clone())));
            arms.push((Pattern::Lit(v), m.mix_top(body)));
            m.scope.pop();
        }
        arms.push((Pattern::Wild, m.mix_top(body)));
        m.scope.truncate(n);
        let lam = Term::Lam(
            ps.clone(),
            Arc::new(Term::Match(Arc::new(Term::Var(p)), arms)),
        );
        Ok((lam, std::mem::take(&mut m.report)))
    }
}

/// A name in scope: its term when it is build-stage, else nothing, and the names that term
/// reads.
struct Entry {
    name: Arc<str>,
    known: Option<Arc<Term>>,
    reads: BTreeSet<Arc<str>>,
}

/// The names in scope, innermost last, with the positions of each name's entries, so a name
/// is looked up in `O(log n)` rather than by a scan of the scope.
#[derive(Default)]
struct Scope {
    entries: Vec<Entry>,
    by_name: BTreeMap<Arc<str>, Vec<usize>>,
}

impl Scope {
    fn push(&mut self, name: Arc<str>, known: Option<Arc<Term>>) {
        let reads = known.as_deref().map(free).unwrap_or_default();
        self.by_name
            .entry(name.clone())
            .or_default()
            .push(self.entries.len());
        self.entries.push(Entry { name, known, reads });
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
    }

    fn truncate(&mut self, n: usize) {
        while self.len() > n {
            self.pop();
        }
    }

    /// The innermost binding of `x`: `None` for a name the scope does not bind.
    fn lookup(&self, x: &str) -> Option<&Option<Arc<Term>>> {
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

/// The least of the values of a range of positions, with one value changed at a time, in
/// `O(log n)` each.
struct Mins {
    n: usize,
    tree: Vec<i64>,
}

impl Mins {
    fn new(values: Vec<i64>) -> Self {
        let n = values.len();
        let mut tree = vec![i64::MAX; n];
        tree.extend(values);
        for i in (1..n).rev() {
            tree[i] = tree[2 * i].min(tree[2 * i + 1]);
        }
        Mins { n, tree }
    }

    fn set(&mut self, i: usize, v: i64) {
        let mut i = i + self.n;
        self.tree[i] = v;
        while i > 1 {
            i /= 2;
            self.tree[i] = self.tree[2 * i].min(self.tree[2 * i + 1]);
        }
    }

    /// The least value of the positions `l..r`.
    fn min(&self, l: usize, r: usize) -> i64 {
        let (mut l, mut r, mut m) = (l + self.n, r + self.n, i64::MAX);
        while l < r {
            if l % 2 == 1 {
                m = m.min(self.tree[l]);
                l += 1;
            }
            if r % 2 == 1 {
                r -= 1;
                m = m.min(self.tree[r]);
            }
            l /= 2;
            r /= 2;
        }
        m
    }
}

/// A value of `Mins`: a name read that cannot be known at build, or a port read.
const RUN: i64 = -1;

/// The names a subterm is under.
type Names<'t> = Cow<'t, [Arc<str>]>;

/// The subterms of a term, in the order `mix` meets them, each with the names it is under,
/// borrowed from the term where it holds them as a list. The join of a lattice recursion is
/// marked, since a port it reads is not an effect of the recursion (`effects`).
fn kids(t: &Term) -> Vec<(&Term, Names<'_>, bool)> {
    let none = || Cow::Borrowed(&[][..]);
    match t {
        Term::Lam(ps, b) => vec![(b, Cow::Borrowed(&ps[..]), false)],
        Term::Let(x, e, b) => vec![
            (e, none(), false),
            (b, Cow::Borrowed(std::slice::from_ref(x)), false),
        ],
        Term::Match(s, arms) => std::iter::once((&**s, none(), false))
            .chain(arms.iter().map(|(p, a)| (a, Cow::Owned(binds(p)), false)))
            .collect(),
        Term::Fam { domain, var, body } => vec![
            (domain, none(), false),
            (body, Cow::Borrowed(std::slice::from_ref(var)), false),
        ],
        Term::Fix {
            init,
            step,
            this,
            key,
            kind,
            ..
        } => {
            let names: Names<'_> = Cow::Owned(vec![this.clone(), key.clone()]);
            let mut out = vec![(&**init, none(), false), (&**step, names.clone(), false)];
            if let zed_kernel::FixKind::Lattice { join } = kind {
                out.push((join, names, true));
            }
            out
        }
        _ => children(t)
            .into_iter()
            .map(|c| (c, none(), false))
            .collect(),
    }
}

/// The term `mix` is mixing, by preorder position: a subterm is build-stage when no name it
/// reads, bound outside it, is unknown at build and it reads no port. Each position holds
/// the position of the binder of the unknown name read there, or `RUN`, so a subterm at
/// `p..p + size` is build-stage exactly when the least value there is at least `p`: its own
/// binders are at `p` or after. Deciding the stage of a subterm is then one query, where
/// reading its free names cost `O(size)` at each of the nodes `mix` enters.
#[derive(Default)]
struct Index {
    size: Vec<usize>,
    /// For a name read, the position of the binder inside the term that binds it.
    binder: Vec<Option<usize>>,
    /// The positions reading each binder's names.
    reads: BTreeMap<usize, Vec<usize>>,
    /// How many names of each binder the mixed term still reads.
    kept: BTreeMap<usize, usize>,
    mins: Option<Mins>,
}

impl Index {
    fn new(t: &Term, scope: &Scope) -> Self {
        let mut ix = Index::default();
        let mut values = Vec::new();
        ix.walk(t, scope, &mut BTreeMap::new(), false, &mut values);
        ix.mins = Some(Mins::new(values));
        ix
    }

    fn walk(
        &mut self,
        t: &Term,
        scope: &Scope,
        bound: &mut BTreeMap<Arc<str>, Vec<usize>>,
        join: bool,
        values: &mut Vec<i64>,
    ) {
        let at = self.size.len();
        self.size.push(0);
        self.binder.push(None);
        values.push(i64::MAX);
        match t {
            Term::Var(x) => match bound.get(x).and_then(|b| b.last()) {
                Some(&b) => {
                    self.binder[at] = Some(b);
                    self.reads.entry(b).or_default().push(at);
                    values[at] = b as i64;
                }
                None => {
                    let known = match scope.lookup(x) {
                        Some(t) => t.is_some(),
                        None => interp::word(x),
                    };
                    if !known {
                        values[at] = RUN;
                    }
                }
            },
            Term::Read(_) | Term::Push(..) if !join => values[at] = RUN,
            _ => {}
        }
        for (c, names, in_join) in kids(t) {
            for x in names.iter() {
                bound.entry(x.clone()).or_default().push(at);
            }
            self.walk(c, scope, bound, join || in_join, values);
            for x in names.iter() {
                let b = bound.get_mut(x).expect("pushed above");
                b.pop();
                if b.is_empty() {
                    bound.remove(x);
                }
            }
        }
        self.size[at] = self.size.len() - at;
    }

    fn build(&self, at: usize) -> bool {
        let mins = self.mins.as_ref().expect("made with the index");
        mins.min(at, at + self.size[at]) >= at as i64
    }

    /// The positions of the subterms of the term at `at`, of which there are `n`.
    fn kids(&self, at: usize, n: usize) -> Vec<usize> {
        let mut p = at + 1;
        (0..n)
            .map(|_| {
                let k = p;
                p += self.size[k];
                k
            })
            .collect()
    }

    /// The binder at `at` is known at build: the names it binds no longer make a term
    /// run-stage.
    fn known(&mut self, at: usize) {
        let mins = self.mins.as_mut().expect("made with the index");
        for &p in self.reads.get(&at).into_iter().flatten() {
            mins.set(p, i64::MAX);
        }
    }

    /// The subterm at `at` is kept as written: the names it reads are read by the mixed term.
    fn keep(&mut self, at: usize) {
        for p in at..at + self.size[at] {
            if let Some(b) = self.binder[p] {
                *self.kept.entry(b).or_default() += 1;
            }
        }
    }
}

#[derive(Default)]
struct Mixer {
    scope: Scope,
    report: Report,
    index: Index,
}

impl Mixer {
    fn bind(&mut self, name: Arc<str>, stage: Stage, t: &Arc<Term>) {
        let known = (stage == Stage::Build).then(|| t.clone());
        self.scope.push(name, known);
    }

    /// The stage a name bound to the mixed term `t` has: build when `t` is a literal or a
    /// build-stage function, run when it is left to run, so that nothing evaluates it again.
    fn known(&self, t: &Term) -> Stage {
        match t {
            Term::Lit(_) => Stage::Build,
            Term::Lam(..) | Term::PrimFn(_) | Term::Var(_) => self.stage(t),
            _ => Stage::Run,
        }
    }

    fn unknown(&mut self, names: &[Arc<str>]) {
        for x in names {
            self.scope.push(x.clone(), None);
        }
    }

    fn lookup(&self, x: &str) -> Option<&Option<Arc<Term>>> {
        self.scope.lookup(x)
    }

    fn stage(&self, t: &Term) -> Stage {
        let known = free(t).iter().all(|x| match self.lookup(x) {
            Some(t) => t.is_some(),
            None => interp::word(x),
        });
        if known && !effects(t) {
            Stage::Build
        } else {
            Stage::Run
        }
    }

    /// The value of the build-stage term `t`, under the bindings it needs: the innermost
    /// build-stage entry of each name it reads, and of each name those read, below them.
    fn eval(&self, t: &Term) -> Result<Value, String> {
        let top = self.scope.len();
        let mut todo: BTreeSet<usize> = free(t)
            .iter()
            .filter_map(|x| self.scope.known_below(x, top))
            .collect();
        let mut lets = Vec::new();
        while let Some(i) = todo.pop_last() {
            let e = &self.scope.entries[i];
            todo.extend(e.reads.iter().filter_map(|x| self.scope.known_below(x, i)));
            let known = e.known.clone().expect("a build-stage entry");
            lets.push((e.name.clone(), known));
        }
        let closed = lets
            .into_iter()
            .fold(t.clone(), |body, (x, e)| Term::Let(x, e, Arc::new(body)));
        if !ends(&closed) {
            return Err("its form does not show that it ends".into());
        }
        Evaluator::new(World::new())
            .run(&interp::prelude(closed))
            .map_err(|e| e.to_string())
    }

    /// `t` with its build-stage subterms evaluated.
    fn mix_top(&mut self, t: &Term) -> Term {
        self.index = Index::new(t, &self.scope);
        self.mix(t, 0)
    }

    /// The subterm `t` at position `at` of the term `mix_top` is mixing, with its
    /// build-stage subterms evaluated.
    fn mix(&mut self, t: &Term, at: usize) -> Term {
        let function = |t: &Term| matches!(t, Term::Lam(..) | Term::PrimFn(_));
        let value = match t {
            Term::Lit(_) | Term::PrimFn(_) | Term::Lam(..) => false,
            Term::Var(x) => matches!(self.lookup(x), Some(Some(e)) if !function(e)),
            _ => true,
        };
        if value && self.index.build(at) {
            return match self.eval(t) {
                Ok(v) => Term::Lit(v),
                Err(why) => {
                    self.report.left.push((t.to_string(), why));
                    self.index.keep(at);
                    t.clone()
                }
            };
        }
        let k = self.index.kids(at, kids(t).len());
        let under = |m: &mut Mixer, names: &[Arc<str>], t: &Term, at: usize| {
            let n = m.scope.len();
            m.unknown(names);
            let out = m.mix(t, at);
            m.scope.truncate(n);
            out
        };
        let a = |t: Term| Arc::new(t);
        match t {
            // A name kept here is bound to no literal (one bound to a literal was computed
            // above), so it does not keep a definition `Let` would drop.
            Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => t.clone(),
            Term::Lam(ps, b) => Term::Lam(ps.clone(), a(under(self, ps, b, k[0]))),
            Term::Let(x, e, b) => {
                if self.index.build(k[0]) && !self.index.reads.contains_key(&at) {
                    self.report.unread.push(x.to_string());
                    return self.mix(b, k[1]);
                }
                let e = a(self.mix(e, k[0]));
                let stage = self.known(&e);
                self.bind(x.clone(), stage, &e);
                if stage == Stage::Build {
                    self.index.known(at);
                }
                let body = self.mix(b, k[1]);
                self.scope.pop();
                if matches!(*e, Term::Lit(_)) && !self.index.kept.contains_key(&at) {
                    return body;
                }
                Term::Let(x.clone(), e, a(body))
            }
            Term::If(c, x, y) => match self.mix(c, k[0]) {
                Term::Lit(Value::Bool(true)) => self.mix(x, k[1]),
                Term::Lit(Value::Bool(false)) => self.mix(y, k[2]),
                atom @ Term::Lit(Value::Atom(_)) => atom,
                c => Term::If(a(c), a(self.mix(x, k[1])), a(self.mix(y, k[2]))),
            },
            Term::App(f, args) => Term::App(
                a(self.mix(f, k[0])),
                args.iter()
                    .zip(&k[1..])
                    .map(|(x, &p)| self.mix(x, p))
                    .collect(),
            ),
            Term::Prim(p, args) => Term::Prim(
                *p,
                args.iter().zip(&k).map(|(x, &p)| self.mix(x, p)).collect(),
            ),
            Term::Match(s, arms) => Term::Match(
                a(self.mix(s, k[0])),
                arms.iter()
                    .zip(&k[1..])
                    .map(|((p, x), &at)| (p.clone(), under(self, &binds(p), x, at)))
                    .collect(),
            ),
            Term::Fam { domain, var, body } => Term::Fam {
                domain: a(self.mix(domain, k[0])),
                var: var.clone(),
                body: a(under(self, std::slice::from_ref(var), body, k[1])),
            },
            Term::Reindex {
                family,
                kf,
                vf,
                witness,
            } => Term::Reindex {
                family: a(self.mix(family, k[0])),
                kf: a(self.mix(kf, k[1])),
                vf: a(self.mix(vf, k[2])),
                witness: witness.clone(),
            },
            Term::Discard { family, sel } => Term::Discard {
                family: a(self.mix(family, k[0])),
                sel: a(self.mix(sel, k[1])),
            },
            Term::Fold {
                family,
                op,
                identity,
                depth,
                ev,
            } => Term::Fold {
                family: a(self.mix(family, k[0])),
                op: a(self.mix(op, k[1])),
                identity: identity.as_ref().map(|i| a(self.mix(i, k[2]))),
                depth: *depth,
                ev: ev.clone(),
            },
            Term::Gen {
                init,
                step,
                guard,
                pos,
            } => Term::Gen {
                init: a(self.mix(init, k[0])),
                step: a(self.mix(step, k[1])),
                guard: a(self.mix(guard, k[2])),
                pos: *pos,
            },
            // A recursion's binders are left as written; recursion arrives at L6.
            Term::Fix { .. } => {
                self.index.keep(at);
                t.clone()
            }
            Term::Push(port, x) => Term::Push(port.clone(), a(self.mix(x, k[0]))),
        }
    }
}
