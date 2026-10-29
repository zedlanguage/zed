//! Checking an equation of kernel terms on finite models: run both sides on each instance and
//! compare what they compute (step M0.10).

use std::fmt::Debug;

use zed_kernel::{KernelError, Term, Value, eval};

/// What a closed term computes: a value, or the error that stopped it.
pub type Outcome = Result<Value, KernelError>;

/// Whether two outcomes agree: equal values, compared as the law catalog compares them
/// (bitwise on floats after NaN canonicalization), or errors of one kind. Errors are compared
/// by kind because a law whose two sides are both rejected, such as a reindex that collides
/// on either side (law 5), may report the collision at different keypaths.
pub fn agree(a: &Outcome, b: &Outcome) -> bool {
    match (a, b) {
        (Ok(x), Ok(y)) => x == y,
        (Err(x), Err(y)) => std::mem::discriminant(x) == std::mem::discriminant(y),
        _ => false,
    }
}

/// Checks that the two terms `sides` builds agree on every instance, and returns how many
/// instances were run. Panics at the first disagreement, naming the instance and both
/// outcomes.
pub fn holds<I: Debug>(
    instances: impl IntoIterator<Item = I>,
    sides: impl Fn(&I) -> (Term, Term),
) -> usize {
    let mut n = 0;
    for inst in instances {
        let (lhs, rhs) = sides(&inst);
        let (a, b) = (eval(&lhs), eval(&rhs));
        assert!(
            agree(&a, &b),
            "the law fails on {inst:?}:\n  left  {a:?}\n  right {b:?}"
        );
        n += 1;
    }
    n
}

/// Returns the first instance on which the two terms disagree, with both outcomes. Panics
/// when they agree on every instance, since the counterexample was expected.
pub fn refuted<I: Debug>(
    instances: impl IntoIterator<Item = I>,
    sides: impl Fn(&I) -> (Term, Term),
) -> (I, Outcome, Outcome) {
    for inst in instances {
        let (lhs, rhs) = sides(&inst);
        let (a, b) = (eval(&lhs), eval(&rhs));
        if !agree(&a, &b) {
            return (inst, a, b);
        }
    }
    panic!("no instance refutes the equation")
}

/// Checks a property that is not an equation of two terms on every instance, and returns how
/// many were run. `prop` returns why an instance fails.
pub fn property<I: Debug>(
    instances: impl IntoIterator<Item = I>,
    prop: impl Fn(&I) -> Result<(), String>,
) -> usize {
    let mut n = 0;
    for inst in instances {
        if let Err(why) = prop(&inst) {
            panic!("the property fails on {inst:?}: {why}");
        }
        n += 1;
    }
    n
}

/// Returns the first instance on which `prop` fails, with the reason. Panics when it holds on
/// every instance.
pub fn property_refuted<I: Debug>(
    instances: impl IntoIterator<Item = I>,
    prop: impl Fn(&I) -> Result<(), String>,
) -> (I, String) {
    for inst in instances {
        if let Err(why) = prop(&inst) {
            return (inst, why);
        }
    }
    panic!("no instance refutes the property")
}

#[cfg(test)]
mod tests {
    use super::*;
    use zed_kernel::Prim;
    use zed_kernel::term::build::{lit, prim};

    #[test]
    fn agreement_is_bitwise_on_floats_and_by_kind_on_errors() {
        assert!(agree(&Ok(Value::Int(1)), &Ok(Value::Int(1))));
        assert!(!agree(&Ok(Value::float(0.0)), &Ok(Value::float(-0.0))));
        assert!(agree(
            &Ok(Value::float(f64::NAN)),
            &Ok(Value::float(-f64::NAN))
        ));
        let c = |k: i64| KernelError::Collision {
            keypath: vec![Value::Int(k)],
        };
        assert!(agree(&Err(c(1)), &Err(c(2))));
        assert!(!agree(&Err(c(1)), &Err(KernelError::Overflow)));
        assert!(!agree(&Err(c(1)), &Ok(Value::Int(1))));
    }

    #[test]
    fn holds_counts_and_refuted_finds_the_counterexample() {
        // `x * 2 == x + x` holds; `x * x == x + x` fails first at -8.
        let xs = || -8..=8i64;
        let double = |x: &i64| {
            (
                prim(Prim::Mul, vec![lit(*x), lit(2)]),
                prim(Prim::Add, vec![lit(*x), lit(*x)]),
            )
        };
        assert_eq!(holds(xs(), double), 17);
        let square = |x: &i64| {
            (
                prim(Prim::Mul, vec![lit(*x), lit(*x)]),
                prim(Prim::Add, vec![lit(*x), lit(*x)]),
            )
        };
        let (x, a, b) = refuted(xs(), square);
        assert_eq!((x, a, b), (-8, Ok(Value::Int(64)), Ok(Value::Int(-16))));
    }

    #[test]
    #[should_panic(expected = "the law fails on 3")]
    fn holds_names_the_failing_instance() {
        holds([1i64, 2, 3], |x| {
            (lit(*x), lit(if *x == 3 { 0 } else { *x }))
        });
    }

    #[test]
    #[should_panic(expected = "no instance refutes")]
    fn refuted_insists_on_a_counterexample() {
        let _ = refuted([1i64, 2], |x| (lit(*x), lit(*x)));
    }

    #[test]
    fn properties() {
        assert_eq!(property(0..5, |_| Ok(())), 5);
        let (i, why) =
            property_refuted(0..5, |i| if *i == 3 { Err("three".into()) } else { Ok(()) });
        assert_eq!((i, why.as_str()), (3, "three"));
    }
}
