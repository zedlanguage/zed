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

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::{Evaluator, Prim, Term, Value, World, on_stack};
use zed_tests::instances::Rng;
use zedc::store::product::Arm;

use super::ints;
use crate::l01_38_presburger::random::{bool_term, int_term};

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
    Term::If(Arc::new(c), Arc::new(a), Arc::new(b))
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
            Arc::new(self.z.clone()),
            Arc::new(if_(
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
        Term::Let(n.clone(), Arc::new(Term::Lit(v.clone())), Arc::new(b))
    });
    Evaluator::new(World::new()).run(&t).ok()
}

/// Checks `arms` against the interpreter over the window: the number of (point, arm) pairs
/// checked, or the first point that reaches an arm whose scope does not hold it.
fn check(s: &Shape, arms: &[Arm]) -> Result<usize, String> {
    assert_eq!(arms.len(), 6);
    on_stack(|| check_on(s, arms))
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
                        lo != zedc::store::interval::End::NegInf
                            || hi != zedc::store::interval::End::PosInf
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
    let h = Term::Lam(vec!["x".into(), "y".into()], Arc::new(s.z.clone()));
    let last = Term::Prim(
        Prim::Gt,
        vec![
            Term::App(Arc::new(var("h")), vec![var("x"), var("y")]),
            lit(s.c),
        ],
    );
    let body = if_(
        s.outer.clone(),
        if_(s.inner.clone(), lit(1), lit(2)),
        if_(last.clone(), lit(3), lit(4)),
    );
    let body = Term::Let("h".into(), Arc::new(h.clone()), Arc::new(body));
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
    let closed = |t: &Term| Term::Let(name.into(), Arc::new(value.clone()), Arc::new(t.clone()));
    let exact =
        |t: &Term, o: bool| on_stack(|| preimage(&closed(t), &doms, &Demand::Bool(o))).exact;
    let function = matches!(value, Term::Lam(..));
    let mut compared = 0;
    for (a, p) in arms.iter().zip(paths) {
        let mut atoms = Vec::new();
        let scope_exact = forced(p, true, &mut atoms)
            && atoms
                .iter()
                .all(|(t, o)| (function || !zedc::stage::free(t).contains(name)) && exact(t, *o));
        let pre = on_stack(|| preimage(&closed(p), &doms, &Demand::Bool(true)));
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
