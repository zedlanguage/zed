//! The reduced product against the interpreter on random bodies of one shape:
//!
//! ```text
//! z = <integer term over x, y>;
//! if <test over x, y> { if <test over x, y> { 1 } else { 2 } } else { if z > c { 3 } else { 4 } }
//! ```
//!
//! At every point of a window, the interpreter gives the value of `z` and the outcome of each
//! test, so the arms the point reaches; each such arm's scope must hold `x`, `y` and `z` at
//! the point, and so no point reaches an arm found unreachable.
//!
//! The same check runs on chains of one to three random bindings or calls, each link reading
//! and really using the one before it, with tests of the chain's end that narrow `x` and `y`
//! through every link ([`chain`]).

use std::collections::BTreeMap;
use std::sync::Arc;
use zed_kernel::Shared;

use zed_kernel::{Evaluator, Prim, Term, Value, World};
use zed_tests::instances::Rng;
use zedc::store::product::Arm;

use super::ints;
use zed_tests::step_helpers::l01_38_presburger::{bool_term, int_term};

/// The window of `x` and `y`.
const LO: i64 = -6;
const HI: i64 = 6;

/// One body of the shape.
#[derive(Clone, Debug)]
struct Shape {
    pub z: Term,
    pub outer: Term,
    pub inner: Term,
    pub c: i64,
}

fn var(n: &str) -> Term {
    Term::Var(n.into())
}

fn lit(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

fn if_(c: Term, a: Term, b: Term) -> Term {
    Term::If(Shared::new(c), Shared::new(a), Shared::new(b))
}

impl Shape {
    fn random(rng: &mut Rng) -> Shape {
        Shape {
            z: int_term(rng, 2),
            outer: bool_term(rng, 2),
            inner: bool_term(rng, 2),
            c: rng.int(-6, 6),
        }
    }

    fn last(&self) -> Term {
        Term::Prim(Prim::Gt, vec![var("z"), lit(self.c)])
    }

    fn body(&self) -> Term {
        Term::Let(
            "z".into(),
            Shared::new(self.z.clone()),
            Shared::new(if_(
                self.outer.clone(),
                if_(self.inner.clone(), lit(1), lit(2)),
                if_(self.last(), lit(3), lit(4)),
            )),
        )
    }

    /// The six arms of the body's own tests, in the walk's order: those of `z`'s term come
    /// first.
    fn arms(&self) -> Vec<Arm> {
        let all = zedc::store::product::arms(&self.body(), &ints(&["x".into(), "y".into()]));
        all[all.len() - 6..].to_vec()
    }
}

/// The value of `t` at the state `env`.
fn at(t: &Term, env: &BTreeMap<Arc<str>, Value>) -> Option<Value> {
    let t = env.iter().fold(t.clone(), |b, (n, v)| {
        Term::Let(n.clone(), Shared::new(Term::Lit(v.clone())), Shared::new(b))
    });
    Evaluator::new(World::new()).run(&t).ok()
}

/// Checks `arms` against the interpreter over the window: the number of (point, arm) pairs
/// checked, or the first point that reaches an arm whose scope does not hold it.
fn check(s: &Shape, arms: &[Arm]) -> Result<usize, String> {
    assert_eq!(arms.len(), 6);
    check_on(s, arms)
}

fn check_on(s: &Shape, arms: &[Arm]) -> Result<usize, String> {
    let at = |t: &Term, env: &BTreeMap<Arc<str>, Value>| at(t, env);
    let mut checked = 0;
    for x in LO..=HI {
        for y in LO..=HI {
            let mut env: BTreeMap<Arc<str>, Value> =
                [("x".into(), Value::Int(x)), ("y".into(), Value::Int(y))].into();
            let Some(z) = at(&s.z, &env) else { continue };
            let Some(Value::Bool(o)) = at(&s.outer, &env) else {
                continue;
            };
            let reached = if o {
                match at(&s.inner, &env) {
                    Some(Value::Bool(true)) => [0, 1],
                    Some(Value::Bool(false)) => [0, 2],
                    _ => continue,
                }
            } else {
                env.insert("z".into(), z.clone());
                match at(&s.last(), &env) {
                    Some(Value::Bool(true)) => [3, 4],
                    Some(Value::Bool(false)) => [3, 5],
                    _ => continue,
                }
            };
            env.insert("z".into(), z);
            for i in reached {
                checked += 1;
                if !arms[i].scope.contains(&env) {
                    return Err(format!(
                        "the point {env:?} reaches arm {i} (test {}, outcome {}), whose scope \
                         does not hold it:\n{}",
                        arms[i].guard, arms[i].outcome, arms[i].scope
                    ));
                }
            }
        }
    }
    Ok(checked)
}

#[test]
fn every_value_that_reaches_an_arm_is_in_its_scope() {
    let mut rng = Rng::new(0x1_39);
    let (mut checked, mut unreachable, mut narrowed) = (0, 0, 0);
    for _ in 0..300 {
        let s = Shape::random(&mut rng);
        let arms = s.arms();
        checked += check(&s, &arms).unwrap_or_else(|e| panic!("{s:?}: {e}"));
        unreachable += arms.iter().filter(|a| !a.reachable()).count();
        narrowed += arms
            .iter()
            .filter(|a| {
                a.reachable()
                    && a.scope.get("x").ints().bounds().is_some_and(|(lo, hi)| {
                        *lo != zedc::store::interval::End::NegInf
                            || *hi != zedc::store::interval::End::PosInf
                    })
            })
            .count();
    }
    // The check ran, found arms unreachable, and found arms the tests narrowed.
    assert!(checked > 20_000, "{checked} checks");
    assert!(unreachable > 40, "{unreachable} unreachable arms");
    assert!(narrowed > 100, "{narrowed} narrowed arms");
}

/// The same shape with `z`'s term as a function `h` of `x` and `y` that the last test calls,
/// and that function:
///
/// ```text
/// h = (x, y) -> <integer term over x, y>;
/// if <test> { if <test> { 1 } else { 2 } } else { if h(x, y) > c { 3 } else { 4 } }
/// ```
fn helper_body(s: &Shape) -> (Term, Term, Term) {
    let h = Term::Lam(vec!["x".into(), "y".into()], Shared::new(s.z.clone()));
    let last = Term::Prim(
        Prim::Gt,
        vec![
            Term::App(Shared::new(var("h")), vec![var("x"), var("y")]),
            lit(s.c),
        ],
    );
    let body = if_(
        s.outer.clone(),
        if_(s.inner.clone(), lit(1), lit(2)),
        if_(last.clone(), lit(3), lit(4)),
    );
    let body = Term::Let("h".into(), Shared::new(h.clone()), Shared::new(body));
    (body, last, h)
}

/// The path condition of each of the six arms, in the walk's order.
fn paths(s: &Shape, last: &Term) -> Vec<Term> {
    let not = |t: &Term| Term::Prim(Prim::Not, vec![t.clone()]);
    let and = |a: Term, b: Term| Term::Prim(Prim::And, vec![a, b]);
    vec![
        s.outer.clone(),
        and(s.outer.clone(), s.inner.clone()),
        and(s.outer.clone(), not(&s.inner)),
        not(&s.outer),
        and(not(&s.outer), last.clone()),
        and(not(&s.outer), not(last)),
    ]
}

/// The atomic tests a scope is narrowed by when `t` gives `outcome`, each with the outcome it
/// must give, as `Scope::assume` takes them apart; `false` when `t` is a disjunction of cases,
/// whose scope is the join of theirs.
fn forced(t: &Term, outcome: bool, out: &mut Vec<(Term, bool)>) -> bool {
    match t {
        Term::Prim(Prim::Not, a) => forced(&a[0], !outcome, out),
        Term::Prim(p @ (Prim::And | Prim::Or), a) if (*p == Prim::And) == outcome => {
            forced(&a[0], outcome, out) && forced(&a[1], outcome, out)
        }
        Term::Prim(Prim::And | Prim::Or, _) | Term::If(..) => false,
        _ => {
            out.push((t.clone(), outcome));
            true
        }
    }
}

/// For each arm with its path condition, closed under the body's binding `name = value`:
/// wherever the path's preimage is exact and the scope is exact, the preimage is empty
/// exactly when the arm is unreachable. The scope is exact when the path is a conjunction of
/// atomic tests and each has an exact preimage on its own: each is then a box, and the scope
/// meets their boxes. A test that reads a value bound by `let` is read through that name's
/// product, not its term, so it is not exact; a test that calls a function is read through
/// the call. The number of arms compared, or the first that disagrees.
fn agree(arms: &[Arm], paths: &[Term], name: &str, value: &Term) -> Result<usize, String> {
    use zedc::store::interval::IntervalSet;
    use zedc::store::preimage::{Demand, preimage};
    let doms = [
        ("x".into(), IntervalSet::top()),
        ("y".into(), IntervalSet::top()),
    ]
    .into();
    let closed = |t: &Term| {
        Term::Let(
            name.into(),
            Shared::new(value.clone()),
            Shared::new(t.clone()),
        )
    };
    let exact = |t: &Term, o: bool| preimage(&closed(t), &doms, &Demand::Bool(o)).exact;
    let function = matches!(value, Term::Lam(..));
    let mut compared = 0;
    for (a, p) in arms.iter().zip(paths) {
        let mut atoms = Vec::new();
        let scope_exact = forced(p, true, &mut atoms)
            && atoms
                .iter()
                .all(|(t, o)| (function || !zedc::stage::free(t).contains(name)) && exact(t, *o));
        let pre = preimage(&closed(p), &doms, &Demand::Bool(true));
        if !scope_exact || !pre.exact {
            continue;
        }
        compared += 1;
        let empty = pre.domains.values().any(IntervalSet::is_empty);
        if empty == a.reachable() {
            return Err(format!(
                "path {p}: the exact preimage is {}, but the arm's scope is\n{}",
                if empty { "empty" } else { "not empty" },
                a.scope
            ));
        }
    }
    Ok(compared)
}

#[test]
fn the_closed_path_condition_and_the_scope_agree_on_emptiness() {
    let mut rng = Rng::new(0x1_39_33);
    let (mut compared, mut through) = (0, 0);
    for _ in 0..300 {
        let s = Shape::random(&mut rng);
        compared += agree(&s.arms(), &paths(&s, &s.last()), "z", &s.z)
            .unwrap_or_else(|e| panic!("{s:?}: {e}"));
        let (body, last, h) = helper_body(&s);
        let arms = zedc::store::product::arms(&body, &ints(&["x".into(), "y".into()]));
        compared +=
            agree(&arms, &paths(&s, &last), "h", &h).unwrap_or_else(|e| panic!("{s:?}: {e}"));
        through += usize::from(arms[3].reachable() && !arms[4].reachable());
    }
    // The comparison ran, and some arms are unreachable only through what `h` returns.
    assert!(compared > 500, "{compared} arms compared");
    assert!(through > 10, "{through} arms unreachable through `h`");
}

/// `if y >= abs(-3 * y) { if y == (x - x) mod -3 { 1 } else { 2 } } else { 3 }`: the outer test
/// leaves `y` the one value 0, and `(x - x) mod -3` is 0, so the arm `2` is unreachable. The
/// inner test is read with `y` as a name of the interval `[0..=0]`; with 0 put in its place,
/// the preimage reads `x` only through `x - x`, which intervals do not cancel, and keeps the
/// arm (found by the cross-check above).
#[test]
fn a_name_of_one_integer_value_is_read_through_its_interval() {
    let (x, y) = (var("x"), var("y"));
    let outer = Term::Prim(
        Prim::Ge,
        vec![
            y.clone(),
            Term::Prim(
                Prim::Abs,
                vec![Term::Prim(Prim::Mul, vec![lit(-3), y.clone()])],
            ),
        ],
    );
    let zero = Term::Prim(
        Prim::Mod,
        vec![Term::Prim(Prim::Sub, vec![x.clone(), x]), lit(-3)],
    );
    let inner = Term::Prim(Prim::Eq, vec![y, zero]);
    let body = if_(outer, if_(inner, lit(1), lit(2)), lit(3));
    let a = zedc::store::product::arms(&body, &ints(&["x".into(), "y".into()]));
    assert_eq!(a.len(), 4);
    assert_eq!(a[0].scope.get("y").ints().to_string(), "[0..=0]");
    assert!(a[1].reachable() && !a[2].reachable(), "{:#?}", a);
}

/// The bindings in force at a point of a run, outermost first: an input or a bound value as
/// its literal, a bound function as its term.
type Env = Vec<(Arc<str>, Term)>;

/// Whether arm `i` holds the inputs of a run, by the domains the fix prints.
type Holds<'a> = dyn Fn(usize, &BTreeMap<Arc<str>, Value>) -> bool + 'a;

/// The value of `t` with the bindings `env`; `None` when the run fails.
fn value_in(t: &Term, env: &Env) -> Option<Value> {
    let t = env.iter().rev().fold(t.clone(), |b, (n, v)| {
        Term::Let(n.clone(), Shared::new(v.clone()), Shared::new(b))
    });
    Evaluator::new(World::new()).run(&t).ok()
}

/// Whether `t` holds an `if` the walk enters.
fn has_arms(t: &Term) -> bool {
    match t {
        Term::If(..) => true,
        Term::Let(_, e, b) => has_arms(e) || has_arms(b),
        Term::Prim(_, args) => args.iter().any(has_arms),
        Term::App(f, args) => has_arms(f) || args.iter().any(has_arms),
        _ => false,
    }
}

/// A run of a body at one point, matched against the arms `product::arms` found for it: the
/// trace numbers the arms as the walk does (an `if` gives its true arm, the arms of its first
/// branch, its false arm, the arms of its second branch; a `let` the arms of its value, then of
/// its body; the walk enters no test), and each arm the run reaches must hold the run's values
/// there. An arm found unreachable holds no value, so no run may reach it.
struct Trace<'a> {
    arms: &'a [Arm],
    /// Whether the arm with this index holds the values; `Scope::contains` but for the
    /// negative control.
    holds: &'a Holds<'a>,
    next: usize,
    /// The (arm, values) pairs checked.
    checked: usize,
    /// Per arm and integer name, the least and greatest value of a run that reached it.
    seen: BTreeMap<(usize, Arc<str>), (i64, i64)>,
}

impl Trace<'_> {
    /// Walks `t`; `live` when the run at `env` reaches `t`.
    fn walk(&mut self, t: &Term, env: &mut Env, live: bool) -> Result<(), String> {
        match t {
            Term::Let(x, e, b) => {
                self.walk(e, env, live)?;
                let (v, live) = match &**e {
                    Term::Lam(..) => ((**e).clone(), live),
                    _ => match live.then(|| value_in(e, env)).flatten() {
                        Some(v) => (Term::Lit(v), true),
                        None => ((**e).clone(), false),
                    },
                };
                env.push((x.clone(), v));
                let r = self.walk(b, env, live);
                env.pop();
                r
            }
            Term::If(c, a, b) => {
                let o = match live.then(|| value_in(c, env)).flatten() {
                    Some(Value::Bool(o)) => Some(o),
                    _ => None,
                };
                for (outcome, branch) in [(true, a), (false, b)] {
                    let i = self.next;
                    self.next += 1;
                    let here = o == Some(outcome);
                    if here {
                        self.reach(i, env)?;
                    }
                    self.walk(branch, env, here)?;
                }
                Ok(())
            }
            Term::Prim(_, args) => self.args(args.iter(), env, live),
            Term::App(f, args) => self.args(std::iter::once(&**f).chain(args), env, live),
            _ => Ok(()),
        }
    }

    /// Walks the arguments `args`, evaluated in order: one that fails ends the run.
    fn args<'t>(
        &mut self,
        args: impl Iterator<Item = &'t Term> + Clone,
        env: &mut Env,
        mut live: bool,
    ) -> Result<(), String> {
        let mut rest = args.clone();
        for a in args {
            rest.next();
            self.walk(a, env, live)?;
            if live && rest.clone().any(has_arms) {
                live = value_in(a, env).is_some();
            }
        }
        Ok(())
    }

    fn reach(&mut self, i: usize, env: &Env) -> Result<(), String> {
        let values: BTreeMap<Arc<str>, Value> = env
            .iter()
            .filter_map(|(n, t)| match t {
                Term::Lit(v) => Some((n.clone(), v.clone())),
                _ => None,
            })
            .collect();
        self.checked += 1;
        if !(self.holds)(i, &values) {
            let a = &self.arms[i];
            return Err(format!(
                "the run at {values:?} reaches arm {i} (test {}, outcome {}), whose scope does \
                 not hold it:\n{}",
                a.guard, a.outcome, a.scope
            ));
        }
        for (n, v) in &values {
            if let Value::Int(v) = v {
                let e = self.seen.entry((i, n.clone())).or_insert((*v, *v));
                *e = (e.0.min(*v), e.1.max(*v));
            }
        }
        Ok(())
    }
}

/// The values each input takes in the check: `-12..=12`, and each finite end of the input's
/// integer pieces in any arm with its two neighbors, so that a domain narrowed past the window
/// is tested at its ends.
fn grid(inputs: &[Arc<str>], arms: &[Arm]) -> Vec<Vec<i64>> {
    inputs
        .iter()
        .map(|n| {
            let mut vs: Vec<i64> = (-12..=12).collect();
            for a in arms.iter().filter(|a| a.reachable()) {
                for (lo, hi) in a.scope.get(n).ints().pieces() {
                    for e in [lo, hi].into_iter().filter_map(|e| e.to_i64()) {
                        vs.extend([e.saturating_sub(1), e, e.saturating_add(1)]);
                    }
                }
            }
            vs.sort_unstable();
            vs.dedup();
            vs
        })
        .collect()
}

/// Runs `body` at every point of the grid of `inputs` against `arms`, with `holds` as the arm's
/// test of the values: the trace, or the first run that reaches an arm not holding it.
fn trace<'a>(
    body: &Term,
    inputs: &[Arc<str>],
    arms: &'a [Arm],
    holds: &'a Holds<'a>,
) -> Result<Trace<'a>, String> {
    let mut t = Trace {
        arms,
        holds,
        next: 0,
        checked: 0,
        seen: BTreeMap::new(),
    };
    let grid = grid(inputs, arms);
    let mut at = vec![0; inputs.len()];
    'points: loop {
        let mut env: Env = inputs
            .iter()
            .zip(&at)
            .zip(&grid)
            .map(|((n, &k), vs)| (n.clone(), lit(vs[k])))
            .collect();
        t.next = 0;
        t.walk(body, &mut env, true)?;
        assert_eq!(
            t.next,
            arms.len(),
            "the trace numbers the arms as the walk does"
        );
        for (k, vs) in at.iter_mut().zip(&grid) {
            *k += 1;
            if *k < vs.len() {
                continue 'points;
            }
            *k = 0;
        }
        return Ok(t);
    }
}

/// The three bodies of one random draw: the shape itself, the shape with `z`'s term as a
/// function `h`, and two bindings, the second over the first and an input:
/// `z = <integer term>; u = z + y; if u >= c { 1 } else { 2 }`.
fn bodies(rng: &mut Rng) -> [Term; 3] {
    let s = Shape::random(rng);
    let w = int_term(rng, 2);
    let c = rng.int(-6, 6);
    let u = Term::Let(
        "u".into(),
        Shared::new(Term::Prim(Prim::Add, vec![var("z"), var("y")])),
        Shared::new(if_(
            Term::Prim(Prim::Ge, vec![var("u"), lit(c)]),
            lit(1),
            lit(2),
        )),
    );
    [
        s.body(),
        helper_body(&s).0,
        Term::Let("z".into(), Shared::new(w), Shared::new(u)),
    ]
}

/// Every run of every random body, at every point of its grid, reaches only arms whose scope
/// holds the run's values there, and no arm found unreachable; checked for every arm of the
/// body, those in `z`'s term too. Item PA-walk-multi narrows inputs through bindings over
/// several of them, which this tests at the narrowed ends. Each of the three seeds is its own
/// test, 900 bodies each, so that each runs in a process of its own (TEST-split-slow: the three
/// together took 43 to 58 s alone at load 18 to 40). Each seed makes over a million checks
/// (1,025,066 to 1,028,509), as the three together had to.
fn every_run_of_random_bodies_reaches_only_arms_that_hold_it(seed: u64) {
    let xy: Vec<Arc<str>> = vec!["x".into(), "y".into()];
    let (mut checked, mut bodies_run) = (0, 0);
    let mut rng = Rng::new(seed);
    for _ in 0..300 {
        for body in bodies(&mut rng) {
            let arms = zedc::store::product::arms(&body, &ints(&xy));
            let holds = |i: usize, v: &BTreeMap<Arc<str>, Value>| arms[i].scope.contains(v);
            let t = trace(&body, &xy, &arms, &holds).unwrap_or_else(|e| panic!("{body}: {e}"));
            checked += t.checked;
            bodies_run += 1;
        }
    }
    assert_eq!(bodies_run, 900);
    assert!(checked > 1_000_000, "{checked} checks");
}

#[test]
fn every_run_of_a_random_body_reaches_only_arms_that_hold_it_seed_1() {
    every_run_of_random_bodies_reaches_only_arms_that_hold_it(0x1_39);
}

#[test]
fn every_run_of_a_random_body_reaches_only_arms_that_hold_it_seed_2() {
    every_run_of_random_bodies_reaches_only_arms_that_hold_it(0x1_39_33);
}

#[test]
fn every_run_of_a_random_body_reaches_only_arms_that_hold_it_seed_3() {
    every_run_of_random_bodies_reaches_only_arms_that_hold_it(7);
}

/// The check above fails on a scope one value too narrow: at each arm a run reached, an input
/// whose least or greatest reached value is a finite end of its domain, with that one value
/// taken out of the domain, makes the check report a run outside the arm's scope.
#[test]
fn the_check_finds_a_domain_one_value_too_narrow() {
    let xy: Vec<Arc<str>> = vec!["x".into(), "y".into()];
    let mut rng = Rng::new(0x1_39);
    let (mut ends, mut found) = (0, 0);
    for _ in 0..40 {
        for body in bodies(&mut rng) {
            let arms = zedc::store::product::arms(&body, &ints(&xy));
            let holds = |i: usize, v: &BTreeMap<Arc<str>, Value>| arms[i].scope.contains(v);
            let seen = trace(&body, &xy, &arms, &holds)
                .unwrap_or_else(|e| panic!("{body}: {e}"))
                .seen;
            for ((i, n), (least, most)) in seen {
                let p = arms[i].scope.get(&n);
                let Some((lo, hi)) = p.ints().bounds().map(|(l, h)| (l.to_i64(), h.to_i64()))
                else {
                    continue;
                };
                for end in [least, most] {
                    if lo != Some(end) && hi != Some(end) {
                        continue;
                    }
                    ends += 1;
                    let narrower = |j: usize, v: &BTreeMap<Arc<str>, Value>| {
                        holds(j, v) && !(j == i && v.get(&n) == Some(&Value::Int(end)))
                    };
                    found += usize::from(trace(&body, &xy, &arms, &narrower).is_err());
                }
            }
        }
    }
    assert!(ends > 50, "{ends} reached ends");
    assert_eq!(found, ends, "every end taken out is found");
}

/// `t`, a term of [`int_term`] or [`bool_term`], with each `x` in it replaced by `by`.
fn with_x(t: &Term, by: &Term) -> Term {
    match t {
        Term::Var(n) if &**n == "x" => by.clone(),
        Term::Prim(p, args) => Term::Prim(*p, args.iter().map(|a| with_x(a, by)).collect()),
        Term::If(c, a, b) => if_(with_x(c, by), with_x(a, by), with_x(b, by)),
        _ => t.clone(),
    }
}

/// A chain of `depth` random links, each reading the link before it (the first reads `x`) and
/// `y`, and the tests at its end. With `calls` unset the links are bindings, with it set
/// functions, each calling the one before it:
///
/// ```text
/// z1 = T1(x, y); z2 = T2(z1, y); ...; zd = Td(z(d-1), y);
/// h1 = (x, y) -> T1(x, y); h2 = (x, y) -> T2(h1(x, y), y); ...;
/// if B1(x, y) { if B2(e, y) { 1 } else { 2 } } else { if e > c { 3 } else { 4 } }
/// ```
///
/// with `e` the last link, `zd` or `hd(x, y)`, and `T` and `B` random terms over `x` and `y`.
/// A test of `e` narrows `x` and `y` through every link. Each `T` really uses the link before
/// it: over the window, at some `y`, it changes with that link, so `e` changes with `x` through
/// all `depth` links; [`links_that_depend`] checks the finished body for it.
fn chain(rng: &mut Rng, depth: usize, calls: bool) -> Term {
    let name = |k: usize| -> Arc<str> { format!("{}{k}", if calls { 'h' } else { 'z' }).into() };
    let link = |k: usize| {
        if calls {
            Term::App(Shared::new(var(&name(k))), vec![var("x"), var("y")])
        } else {
            var(&name(k))
        }
    };
    // The outcomes of the link before at each point of the window; `x` before the first.
    let mut before: Vec<Option<i64>> = window().map(|(x, _)| Some(x)).collect();
    let values: Vec<Term> = (1..=depth)
        .map(|k| {
            // A term over `x` and `y`, drawn again until, with the link before in `x`, it
            // changes with that link at some `y` of the window: `0 * x` or `x - x` mention `x`
            // and do not use it.
            let (t, outcomes) = loop {
                let t = int_term(rng, 2);
                let outcomes: Vec<Option<i64>> = window()
                    .zip(&before)
                    .map(|((_, y), b)| {
                        let env = vec![("x".into(), lit((*b)?)), ("y".into(), lit(y))];
                        int_of(value_in(&t, &env))
                    })
                    .collect();
                if varies(window().map(|(_, y)| y).zip(outcomes.iter().copied())) {
                    break (t, outcomes);
                }
            };
            before = outcomes;
            let t = if k == 1 { t } else { with_x(&t, &link(k - 1)) };
            if calls {
                Term::Lam(vec!["x".into(), "y".into()], Shared::new(t))
            } else {
                t
            }
        })
        .collect();
    let (outer, inner, c) = (bool_term(rng, 2), bool_term(rng, 2), rng.int(-6, 6));
    let end = link(depth);
    let mut body = if_(
        outer,
        if_(with_x(&inner, &end), lit(1), lit(2)),
        if_(Term::Prim(Prim::Gt, vec![end, lit(c)]), lit(3), lit(4)),
    );
    for (k, v) in values.into_iter().enumerate().rev() {
        body = Term::Let(name(k + 1), Shared::new(v), Shared::new(body));
    }
    assert_eq!(
        links_that_depend(&body),
        depth,
        "a chain drawn as {depth} links deep is not:\n{body}"
    );
    body
}

/// The points of the window, `x` outer, `y` inner.
fn window() -> impl Iterator<Item = (i64, i64)> {
    (LO..=HI).flat_map(|x| (LO..=HI).map(move |y| (x, y)))
}

/// `v` as an integer; `None` for a run that failed or gave another value.
fn int_of(v: Option<Value>) -> Option<i64> {
    match v {
        Some(Value::Int(n)) => Some(n),
        _ => None,
    }
}

/// Whether a link changes with the one before it over the window: at some `y`, two points
/// give the link two outcomes. `runs` gives, at each point, `y` and the link's outcome.
fn varies(runs: impl IntoIterator<Item = (i64, Option<i64>)>) -> bool {
    let mut first: BTreeMap<i64, Option<i64>> = BTreeMap::new();
    runs.into_iter()
        .any(|(y, v)| *first.entry(y).or_insert(v) != v)
}

/// The number of links of `body`, a [`chain`], that really depend on the one before them (the
/// first on `x`), found by running the body's own bindings over the window. A link counts when
/// at some `y` it takes two outcomes; each link must also be a function of the one before it
/// and `y` (two points that agree on them agree on the link), so that outcomes changing with
/// `x` change through the link before. A link that does not depend on the one before cuts the
/// chain there: no later link changes with `x`, so none after it counts.
fn links_that_depend(body: &Term) -> usize {
    let mut links: Env = Vec::new();
    let mut t = body;
    while let Term::Let(n, v, b) = t {
        links.push((n.clone(), (**v).clone()));
        t = b;
    }
    let mut before: Vec<Option<i64>> = window().map(|(x, _)| Some(x)).collect();
    let mut deep = 0;
    for k in 0..links.len() {
        let (name, value) = &links[k];
        let read = match value {
            Term::Lam(..) => Term::App(Shared::new(var(name)), vec![var("x"), var("y")]),
            _ => var(name),
        };
        let outcomes: Vec<Option<i64>> = window()
            .map(|(x, y)| {
                let mut env: Env = vec![("x".into(), lit(x)), ("y".into(), lit(y))];
                env.extend(links[..=k].iter().cloned());
                int_of(value_in(&read, &env))
            })
            .collect();
        let mut by: BTreeMap<(i64, Option<i64>), Option<i64>> = BTreeMap::new();
        for (((_, y), b), o) in window().zip(&before).zip(&outcomes) {
            assert_eq!(
                *by.entry((y, *b)).or_insert(*o),
                *o,
                "link {name} of the chain reads more than the link before it and y:\n{body}"
            );
        }
        deep += usize::from(varies(
            window().map(|(_, y)| y).zip(outcomes.iter().copied()),
        ));
        before = outcomes;
    }
    deep
}

/// Counts of one run of [`chains_reach_only_arms_that_hold_them`].
#[derive(Debug, Default)]
struct ChainCounts {
    /// (arm, run) pairs checked.
    checked: usize,
    /// Arms of `e > c` found unreachable inside a reachable `else` of `B1`: no value of the
    /// chain there is above `c`, or none is at most `c`.
    cut: usize,
    /// Arms of `e > c`, reachable, where `x` or `y` is narrower than in the `else` of `B1`
    /// around them: the test of the chain's end narrowed an input through every link.
    narrowed: usize,
}

/// Every run of each of the random chains `traced` among the first `draws` of `depth` links
/// (bindings, or functions when `calls` is set), drawn from `seed`, at every point of its grid,
/// reaches only arms whose scope holds the run's values there, and no arm found unreachable.
/// With `counted` set, the arms of `e > c` cut and narrowed are counted over all `draws` chains,
/// which needs their arms and not their runs. A failure names the seed, the draw, the body and
/// the command that runs the test again; the draws are fixed by the seed, so a rerun repeats it.
fn chains_reach_only_arms_that_hold_them(
    test: &str,
    seed: u64,
    (depth, calls): (usize, bool),
    draws: usize,
    traced: std::ops::Range<usize>,
    counted: bool,
) -> ChainCounts {
    let xy: Vec<Arc<str>> = vec!["x".into(), "y".into()];
    let mut rng = Rng::new(seed);
    let mut n = ChainCounts::default();
    for draw in 0..draws {
        let body = chain(&mut rng, depth, calls);
        if !counted && !traced.contains(&draw) {
            continue;
        }
        let arms = zedc::store::product::arms(&body, &ints(&xy));
        if traced.contains(&draw) {
            let holds = |i: usize, v: &BTreeMap<Arc<str>, Value>| arms[i].scope.contains(v);
            let t = trace(&body, &xy, &arms, &holds).unwrap_or_else(|e| {
                panic!(
                    "seed {seed:#x}, draw {draw} of {draws}, a chain of {} of depth {depth}:\n{body}\n{e}\n\
                     To run this test again, from the root of the checkout:\n  \
                     tools/run_tests.sh --no-doc --only 'l01_39_reduced_product::random::{test}$'",
                    if calls { "calls" } else { "bindings" }
                )
            });
            n.checked += t.checked;
        }
        if !counted {
            continue;
        }
        // The arms of the tests at the chain's end, in the walk's order: `B1`, `B2` inside it,
        // the `else` of `B1`, then `e > c` inside that.
        let end = &arms[arms.len() - 6..];
        if end[3].reachable() {
            for a in &end[4..] {
                if !a.reachable() {
                    n.cut += 1;
                } else if ["x", "y"]
                    .iter()
                    .any(|v| a.scope.get(v).ints() != end[3].scope.get(v).ints())
                {
                    n.narrowed += 1;
                }
            }
        }
    }
    n
}

/// [`chains_reach_only_arms_that_hold_them`] on one half of the chains of a depth and form,
/// `part` 1 or 2, with checks that it ran: over 1,000 (arm, run) pairs a traced chain, and, in
/// part 1, over all the chains, some arms of `e > c` cut (over 100) and some narrowed through
/// the chain (over 150). A depth draws the same terms for bindings and for calls, from one seed.
///
/// Every link really uses the one before ([`chain`]), and a test of a bound name narrows the
/// inputs only through a summary of its value, which `abs`, `div`, `mod`, a `min` or `max` of two
/// terms and a value over both inputs do not have, where a call is read through its term: over
/// the same 600 chains, bindings cut 85 to 110 arms and narrow 86 to 379, calls cut 113 to 151
/// and narrow 463 to 691. Bindings are drawn 1,200 times, calls 600, so that both pass the same
/// counts (bindings over 1,200 chains: cut 164 to 214, narrowed 159 to 734). The two halves of
/// the traced chains are two pieces, 377,634 to 1,125,863 checks and 10 to 35 s each at load
/// 34 with the twelve running together (item TESTS-walk-chains-strict-depth; item
/// TESTS-l01_39-walk-chains made these tests, from chains of item PA-walk-multi).
fn chains_of(test: &str, depth: usize, calls: bool, part: usize) {
    let draws = if calls { 600 } else { 1200 };
    let half = draws / 2;
    let traced = if part == 1 { 0..half } else { half..draws };
    let seed = 0x1_39_c0 + depth as u64;
    let n =
        chains_reach_only_arms_that_hold_them(test, seed, (depth, calls), draws, traced, part == 1);
    assert!(n.checked > 1_000 * half, "{n:?}");
    if part == 1 {
        assert!(n.cut > 100, "{n:?}");
        assert!(n.narrowed > 150, "{n:?}");
    }
}

#[test]
fn every_run_of_a_chain_of_one_binding_reaches_only_arms_that_hold_it_part_1() {
    chains_of(
        "every_run_of_a_chain_of_one_binding_reaches_only_arms_that_hold_it_part_1",
        1,
        false,
        1,
    );
}

#[test]
fn every_run_of_a_chain_of_one_binding_reaches_only_arms_that_hold_it_part_2() {
    chains_of(
        "every_run_of_a_chain_of_one_binding_reaches_only_arms_that_hold_it_part_2",
        1,
        false,
        2,
    );
}

#[test]
fn every_run_of_a_chain_of_two_bindings_reaches_only_arms_that_hold_it_part_1() {
    chains_of(
        "every_run_of_a_chain_of_two_bindings_reaches_only_arms_that_hold_it_part_1",
        2,
        false,
        1,
    );
}

#[test]
fn every_run_of_a_chain_of_two_bindings_reaches_only_arms_that_hold_it_part_2() {
    chains_of(
        "every_run_of_a_chain_of_two_bindings_reaches_only_arms_that_hold_it_part_2",
        2,
        false,
        2,
    );
}

#[test]
fn every_run_of_a_chain_of_three_bindings_reaches_only_arms_that_hold_it_part_1() {
    chains_of(
        "every_run_of_a_chain_of_three_bindings_reaches_only_arms_that_hold_it_part_1",
        3,
        false,
        1,
    );
}

#[test]
fn every_run_of_a_chain_of_three_bindings_reaches_only_arms_that_hold_it_part_2() {
    chains_of(
        "every_run_of_a_chain_of_three_bindings_reaches_only_arms_that_hold_it_part_2",
        3,
        false,
        2,
    );
}

#[test]
fn every_run_of_a_chain_of_one_call_reaches_only_arms_that_hold_it_part_1() {
    chains_of(
        "every_run_of_a_chain_of_one_call_reaches_only_arms_that_hold_it_part_1",
        1,
        true,
        1,
    );
}

#[test]
fn every_run_of_a_chain_of_one_call_reaches_only_arms_that_hold_it_part_2() {
    chains_of(
        "every_run_of_a_chain_of_one_call_reaches_only_arms_that_hold_it_part_2",
        1,
        true,
        2,
    );
}

#[test]
fn every_run_of_a_chain_of_two_calls_reaches_only_arms_that_hold_it_part_1() {
    chains_of(
        "every_run_of_a_chain_of_two_calls_reaches_only_arms_that_hold_it_part_1",
        2,
        true,
        1,
    );
}

#[test]
fn every_run_of_a_chain_of_two_calls_reaches_only_arms_that_hold_it_part_2() {
    chains_of(
        "every_run_of_a_chain_of_two_calls_reaches_only_arms_that_hold_it_part_2",
        2,
        true,
        2,
    );
}

#[test]
fn every_run_of_a_chain_of_three_calls_reaches_only_arms_that_hold_it_part_1() {
    chains_of(
        "every_run_of_a_chain_of_three_calls_reaches_only_arms_that_hold_it_part_1",
        3,
        true,
        1,
    );
}

#[test]
fn every_run_of_a_chain_of_three_calls_reaches_only_arms_that_hold_it_part_2() {
    chains_of(
        "every_run_of_a_chain_of_three_calls_reaches_only_arms_that_hold_it_part_2",
        3,
        true,
        2,
    );
}
