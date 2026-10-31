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

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Pattern, Term, Value, World};

use crate::elab::Unit;
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
/// which are primitives. Each subterm is read once.
pub fn ends(t: &Term) -> bool {
    ends_in(t, &mut Vec::new())
}

/// [`ends`] under `scope`: each name bound around `t`, innermost last, with whether it is
/// bound to a function that ends.
fn ends_in(t: &Term, scope: &mut Vec<(Arc<str>, bool)>) -> bool {
    match t {
        Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => true,
        Term::Fix { .. } | Term::Gen { .. } => false,
        Term::Lam(ps, b) => under(scope, ps, |scope| ends_in(b, scope)),
        Term::App(f, args) => callable(f, scope) && args.iter().all(|a| ends_in(a, scope)),
        Term::Let(x, e, b) => {
            // A lambda bound and never called need not end; any other binding is evaluated.
            let c = match &**e {
                Term::Lam(..) => ends_in(e, scope),
                _ if ends_in(e, scope) => callable(e, scope),
                _ => return false,
            };
            scope.push((x.clone(), c));
            let out = ends_in(b, scope);
            scope.pop();
            out
        }
        Term::Match(s, arms) => {
            ends_in(s, scope)
                && arms
                    .iter()
                    .all(|(p, a)| under(scope, &binds(p), |scope| ends_in(a, scope)))
        }
        Term::Fam { domain, var, body } => {
            ends_in(domain, scope)
                && under(scope, std::slice::from_ref(var), |scope| {
                    ends_in(body, scope)
                })
        }
        Term::Reindex { family, kf, vf, .. } => {
            ends_in(family, scope) && callable(kf, scope) && callable(vf, scope)
        }
        Term::Discard { family, sel } => ends_in(family, scope) && callable(sel, scope),
        Term::Fold {
            family,
            op,
            identity,
            ..
        } => {
            ends_in(family, scope)
                && callable(op, scope)
                && identity.iter().all(|i| ends_in(i, scope))
        }
        _ => children(t).into_iter().all(|c| ends_in(c, scope)),
    }
}

/// Whether `f`, in the position of a function called, is one that ends: a primitive, a
/// lambda whose body ends, or a name bound to one; a free name is a prelude word.
fn callable(f: &Term, scope: &mut Vec<(Arc<str>, bool)>) -> bool {
    match f {
        Term::PrimFn(_) => true,
        Term::Lam(..) => ends_in(f, scope),
        Term::Var(x) => scope
            .iter()
            .rev()
            .find(|(n, _)| n == x)
            .is_none_or(|(_, c)| *c),
        _ => false,
    }
}

/// `f` with `names` bound around it to values not known to be functions that end.
fn under<T>(
    scope: &mut Vec<(Arc<str>, bool)>,
    names: &[Arc<str>],
    f: impl FnOnce(&mut Vec<(Arc<str>, bool)>) -> T,
) -> T {
    let n = scope.len();
    scope.extend(names.iter().map(|x| (x.clone(), false)));
    let out = f(scope);
    scope.truncate(n);
    out
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
    let mut demanded: BTreeSet<Arc<str>> = unit
        .defs
        .iter()
        .filter(|d| roots.contains(&d.name.as_str()))
        .map(|d| d.kernel.clone())
        .collect();
    for t in &unit.tests {
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
        let term = m.mix_top(&d.term);
        if matches!(term, Term::Lit(_)) && term != d.term {
            m.report.built.push(d.name.clone());
        }
        let stage = m.known(&term);
        m.bind(d.kernel.clone(), stage, &term);
        out.defs.push(crate::elab::Def { term, ..d.clone() });
    }
    (out, m.report)
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
/// finite here when it lists its values no longer than it is written ([`Type::listed`]).
pub fn trick(d: &Domain, passed: &BTreeSet<Value>) -> Choice {
    let within: Vec<Value> = match d {
        Domain::Type(t) => {
            if t.listed().is_none() {
                return Choice::Keep(format!("the domain `{t}` is not a finite list"));
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
    let mut out = BTreeSet::new();
    let Some(f) = unit.defs.iter().find(|d| d.name == name) else {
        return out;
    };
    let roots: Vec<&str> = unit.defs.iter().map(|d| d.name.as_str()).collect();
    let (mixed, _) = mix(unit, &roots);
    for d in &mixed.defs {
        calls(&d.term, &f.kernel, param, &mut out);
    }
    for t in unit.tests.iter().filter(|t| t.function == name) {
        if let Some(Term::Lit(v)) = t.args.get(param) {
            out.insert(v.clone());
        }
    }
    out
}

/// Adds to `out` the literal argument `param` of each call of `f` in `t`.
fn calls(t: &Term, f: &Arc<str>, param: usize, out: &mut BTreeSet<Value>) {
    if let Term::App(g, args) = t
        && matches!(&**g, Term::Var(n) if n == f)
        && let Some(Term::Lit(v)) = args.get(param)
    {
        out.insert(v.clone());
    }
    match t {
        Term::Lam(_, b) => calls(b, f, param, out),
        Term::Let(_, e, b) => {
            calls(e, f, param, out);
            calls(b, f, param, out);
        }
        Term::Match(e, arms) => {
            calls(e, f, param, out);
            for (_, a) in arms {
                calls(a, f, param, out);
            }
        }
        Term::Fam { domain, body, .. } => {
            calls(domain, f, param, out);
            calls(body, f, param, out);
        }
        Term::Fix { init, step, .. } => {
            calls(init, f, param, out);
            calls(step, f, param, out);
        }
        _ => {
            for c in children(t) {
                calls(c, f, param, out);
            }
        }
    }
}

/// The function `name` of `unit` split on its parameter `param` over the values of `d` its
/// static calls pass ([`passed`]), each arm its body mixed with the parameter known, and the
/// general body last; or why the Trick keeps it.
pub fn split(unit: &Unit, name: &str, param: usize, d: &Domain) -> Result<(Term, Report), String> {
    let at = unit
        .defs
        .iter()
        .position(|d| d.name == name)
        .ok_or_else(|| format!("no definition `{name}`"))?;
    let Term::Lam(ps, body) = &unit.defs[at].term else {
        return Err(format!("`{name}` is not a function"));
    };
    let p = ps
        .get(param)
        .ok_or_else(|| format!("`{name}` has no parameter {param}"))?
        .clone();
    let values = match trick(d, &passed(unit, name, param)) {
        Choice::Split(vs) => vs,
        Choice::Keep(why) => return Err(why),
    };
    let mut m = Mixer::default();
    for d in &unit.defs[..at] {
        let stage = m.stage(&d.term);
        m.bind(d.kernel.clone(), stage, &d.term);
    }
    let n = m.scope.len();
    for q in ps {
        m.bind(q.clone(), Stage::Run, &Term::Var(q.clone()));
    }
    let mut arms = Vec::new();
    for v in values {
        m.bind(p.clone(), Stage::Build, &Term::Lit(v.clone()));
        arms.push((Pattern::Lit(v), m.mix_top(body)));
        m.scope.pop();
    }
    arms.push((Pattern::Wild, m.mix_top(body)));
    m.scope.truncate(n);
    let lam = Term::Lam(
        ps.clone(),
        Arc::new(Term::Match(Arc::new(Term::Var(p)), arms)),
    );
    Ok((lam, m.report))
}

/// A name in scope: its term when it is build-stage, else nothing, and the names that term
/// reads.
struct Entry {
    name: Arc<str>,
    known: Option<Term>,
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
    fn push(&mut self, name: Arc<str>, known: Option<Term>) {
        let reads = known.as_ref().map(free).unwrap_or_default();
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
    fn lookup(&self, x: &str) -> Option<&Option<Term>> {
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

/// The subterms of a term, in the order `mix` meets them, each with the names it is under.
/// The join of a lattice recursion is marked, since a port it reads is not an effect of the
/// recursion (`effects`).
fn kids(t: &Term) -> Vec<(&Term, Vec<Arc<str>>, bool)> {
    match t {
        Term::Lam(ps, b) => vec![(b, ps.clone(), false)],
        Term::Let(x, e, b) => vec![(e, vec![], false), (b, vec![x.clone()], false)],
        Term::Match(s, arms) => std::iter::once((&**s, vec![], false))
            .chain(arms.iter().map(|(p, a)| (a, binds(p), false)))
            .collect(),
        Term::Fam { domain, var, body } => {
            vec![(domain, vec![], false), (body, vec![var.clone()], false)]
        }
        Term::Fix {
            init,
            step,
            this,
            key,
            kind,
            ..
        } => {
            let names = vec![this.clone(), key.clone()];
            let mut out = vec![(&**init, vec![], false), (&**step, names.clone(), false)];
            if let zed_kernel::FixKind::Lattice { join } = kind {
                out.push((join, names, true));
            }
            out
        }
        _ => children(t)
            .into_iter()
            .map(|c| (c, vec![], false))
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
            for x in &names {
                bound.entry(x.clone()).or_default().push(at);
            }
            self.walk(c, scope, bound, join || in_join, values);
            for x in &names {
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
    fn bind(&mut self, name: Arc<str>, stage: Stage, t: &Term) {
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

    fn lookup(&self, x: &str) -> Option<&Option<Term>> {
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
        let closed = lets.into_iter().fold(t.clone(), |body, (x, e)| {
            Term::Let(x, Arc::new(e), Arc::new(body))
        });
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
                let e = self.mix(e, k[0]);
                let stage = self.known(&e);
                self.bind(x.clone(), stage, &e);
                if stage == Stage::Build {
                    self.index.known(at);
                }
                let body = self.mix(b, k[1]);
                self.scope.pop();
                if matches!(e, Term::Lit(_)) && !self.index.kept.contains_key(&at) {
                    return body;
                }
                Term::Let(x.clone(), a(e), a(body))
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
