use zed_tests::scaling;

use super::super::divisors::{chained_rat_tests, chained_tests};
use super::super::sig;

#[test]
fn chained_tests_and_divisions_check_in_linear_time() {
    // Each division reads the integers of its divisor in the scope of its arm once
    // (`Ck::ints_here`), only where the divisor's type holds a zero (COMPLEXITY.md row
    // NARROW-ne-divisor).
    assert_eq!(sig(&chained_tests(3), "f"), "(x: int, d: int) -> int");
    let built = scaling::inputs(1000, |m| {
        let stmts = zed_tests::deep::statements(&chained_tests(m));
        let res = zedc::resolve::resolve(&stmts).unwrap();
        (stmts, res)
    });
    scaling::check(
        "n chained tests each with a division in its arm",
        1000,
        |m| {
            let (stmts, res) = &built[&m];
            let info = zedc::check::walk::check(stmts, res);
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}

#[test]
fn chained_rat_tests_and_divisions_check_in_linear_time() {
    // Each division by a `rat` whose type holds `0r` reads the divisor's product in the scope
    // of its arm once (`Ck::may_be_here`), and each test against a `rat` literal reads the
    // literal's sign once (`Scope::atom_names`) (COMPLEXITY.md row NARROW-ne-rat-divisor).
    assert_eq!(sig(&chained_rat_tests(3), "f"), "(x: rat, r: rat) -> rat");
    let built = scaling::inputs(800, |m| {
        let stmts = zed_tests::deep::statements(&chained_rat_tests(m));
        let res = zedc::resolve::resolve(&stmts).unwrap();
        (stmts, res)
    });
    scaling::check(
        "n chained tests each with a division by a rat in its arm",
        800,
        |m| {
            let (stmts, res) = &built[&m];
            let info = zedc::check::walk::check(stmts, res);
            assert!(info.errors.is_empty(), "{:?}", info.errors);
        },
    );
}
