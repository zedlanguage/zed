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

use zed_kernel::{Evaluator, Prim, Stack, Term, Value, World, on_stack};
use zed_tests::instances::Rng;
use zedc::store::product::Arm;

use super::ints;
use crate::l01_38_presburger::random::{bool_term, int_term};

/// The window of `x` and `y`.
pub(super) const LO: i64 = -6;
pub(super) const HI: i64 = 6;

/// One body of the shape.
#[derive(Clone, Debug)]
pub(super) struct Shape {
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
    pub(super) fn random(rng: &mut Rng) -> Shape {
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

    pub(super) fn body(&self) -> Term {
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
    pub(super) fn arms(&self) -> Vec<Arm> {
        let all = zedc::store::product::arms(&self.body(), &ints(&["x".into(), "y".into()]));
        all[all.len() - 6..].to_vec()
    }
}

/// The value of `t` at the state `env`.
fn at(stack: &Stack, t: &Term, env: &BTreeMap<Arc<str>, Value>) -> Option<Value> {
    let t = env.iter().fold(t.clone(), |b, (n, v)| {
        Term::Let(n.clone(), Arc::new(Term::Lit(v.clone())), Arc::new(b))
    });
    Evaluator::new(World::new()).run_on(stack, &t).ok()
}

/// Checks `arms` against the interpreter over the window: the number of (point, arm) pairs
/// checked, or the first point that reaches an arm whose scope does not hold it.
pub(super) fn check(s: &Shape, arms: &[Arm]) -> Result<usize, String> {
    assert_eq!(arms.len(), 6);
    on_stack(|stack| check_on(stack, s, arms))
}

fn check_on(stack: &Stack, s: &Shape, arms: &[Arm]) -> Result<usize, String> {
    let at = |t: &Term, env: &BTreeMap<Arc<str>, Value>| at(stack, t, env);
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
