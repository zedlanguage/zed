//! The Omega test at the rule of low complexity (DESIGN.md Part G). An inexact elimination
//! has two shadows that both recurse, so the order and the checks before them decide whether
//! the work doubles with each variable: the dark shadow is solved first, since a point of it
//! settles the problem, and an empty problem is first tried by the real shadows alone. Each
//! family below doubles without one of the two: `chain(v, 3)` without the order, `rising`
//! without the real shadows (it passes the step budget at 15 variables).

use std::sync::Arc;
use std::time::{Duration, Instant};

use zed_tests::scaling;
use zedc::store::presburger::{Atom, Con, Formula, Lin, satisfiable};

fn x(i: usize) -> Lin {
    Lin::atom(Atom::Sym(Arc::from(format!("x{i}"))))
}

/// `3·x[i+1] >= 2·x[i] + 1` and `2·x[i] + k >= 3·x[i+1]` for `i < v`: no elimination is
/// exact, the chain has a point when `k >= 1`, and none when `k == 0`.
fn chain(v: usize, k: i128) -> Formula {
    let mut cons = Vec::new();
    for i in 0..v {
        let a = x(i).times(2).unwrap();
        let b = x(i + 1).times(3).unwrap();
        cons.push(Formula::Con(
            Con::ge(&b, &a.plus(&Lin::constant(1)).unwrap()).unwrap(),
        ));
        cons.push(Formula::Con(
            Con::ge(&a.plus(&Lin::constant(k)).unwrap(), &b).unwrap(),
        ));
    }
    Formula::and(cons)
}

/// `3·x[i] + 1 <= 2·x[i+1] <= 3·x[i] + 5` for `i < v`, `x[0] >= 0` and `x[v] <= 0`: empty,
/// since each `x[i+1]` is above `x[i]`, but no single step shows it.
fn rising(v: usize) -> Formula {
    let zero = Lin::constant(0);
    let mut cons = vec![
        Formula::Con(Con::ge(&x(0), &zero).unwrap()),
        Formula::Con(Con::ge(&zero, &x(v)).unwrap()),
    ];
    for i in 0..v {
        let a = x(i).times(3).unwrap();
        let b = x(i + 1).times(2).unwrap();
        cons.push(Formula::Con(
            Con::ge(&b, &a.plus(&Lin::constant(1)).unwrap()).unwrap(),
        ));
        cons.push(Formula::Con(
            Con::ge(&a.plus(&Lin::constant(5)).unwrap(), &b).unwrap(),
        ));
    }
    Formula::and(cons)
}

#[test]
fn chains_of_inexact_eliminations_are_answered() {
    for v in 1..=15 {
        let m = satisfiable(&chain(v, 3)).expect("within the budget");
        let m = m.unwrap_or_else(|| panic!("the chain of {v} has a point"));
        assert!(chain(v, 3).holds(&m).unwrap(), "{m:?}");
        assert_eq!(
            satisfiable(&chain(v, 0)),
            Ok(None),
            "the chain of {v} is empty"
        );
        assert_eq!(
            satisfiable(&rising(v)),
            Ok(None),
            "the rising chain of {v} is empty"
        );
    }
}

/// A family of problems by their number of variables.
type Family = fn(usize) -> Formula;

/// The fastest of five runs of `f`.
fn fastest(f: impl Fn()) -> Duration {
    f();
    (0..5)
        .map(|_| {
            let t = Instant::now();
            f();
            t.elapsed()
        })
        .min()
        .expect("five runs")
}

#[test]
fn a_chain_of_inexact_eliminations_does_not_double() {
    // The variables are bounded by the budget of 16, so the n-against-8n test of
    // `zed_tests::scaling` does not apply; a chain of 15 against one of 7 tells doubling (256
    // times as long) from the polynomial cost of the eliminations (about 10 times).
    let cases: [(&str, Family); 3] = [
        ("the chain with a point", |v| chain(v, 3)),
        ("the empty chain", |v| chain(v, 0)),
        ("the rising chain", rising),
    ];
    for (what, f) in cases {
        let small = fastest(|| drop(satisfiable(&f(7))));
        let large = fastest(|| drop(satisfiable(&f(15))));
        let ratio = large.as_secs_f64() / small.as_secs_f64();
        assert!(
            ratio <= scaling::RATIO,
            "{what}: 7 variables take {small:?} and 15 take {large:?}, {ratio:.1} times as \
             long; doubling with each variable would be 256 times"
        );
    }
}
