//! Benchmarks of `let_terms`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// A test of a link of a chain of bindings with no summary reads only the links whose
/// integers it changes, each once: in [`nested_halvings`] each test changes one link in each
/// arm, so a chain of n links each read by k tests makes 2 n k term reads and costs O(n k).
#[test]
fn reading_chains_of_terms_scales() {
    let (a, _) = term_reads(&nested_halvings(3, 2));
    // `z1 <= 1000` gives `x <= 2001`; the tests of `z2` and `z3` leave `z1` and `z2` as they were.
    assert_eq!(ints_of(&a, "(z1 <= 1000)", true, "x"), "[..=2001]");
    assert_eq!(ints_of(&a, "(z2 <= 1000)", true, "z1"), "[..=1000]");
    assert_eq!(ints_of(&a, "(z3 <= 1000)", true, "z3"), "[..=1000]");
    assert!(!arm(&a, "(z3 <= 1001)", false).reachable());
    for n in [3, 32, 256] {
        assert_eq!(
            term_reads(&nested_halvings(n, 2)).1,
            4 * n as u64,
            "{n} links"
        );
    }
    let chains = scaling::inputs(32, |n| nested_halvings(n, 2));
    let x = ints(&["x".into()]);
    scaling::check_order(
        "a chain of n bindings `zj = z(j-1) div 2`, each read by 2 nested tests",
        32,
        1,
        |n| {
            zedc::store::product::arms(&chains[&n], &x);
        },
    );
}

/// A test that narrows every link of a chain reads every link once in each arm. In the `else`
/// chain of [`else_halvings`] at k = 2, the scope of the tests of `zj` holds `z(j+1) <= 0`, so
/// `zj <= 1` and each link below and `x` the range that gives; `zj > 0` splits `zj` into `1`
/// and `..=0`, which changes `zj`, `z(j-1)`, …, `z1` and `x` in each arm, `j` term reads an
/// arm, and `zj > 1` changes nothing. So the reads number `2 (1 + … + n) = n (n + 1)`, and
/// the arms differ from the scopes they are tested in by `Θ(n²)` names in all: the output is
/// quadratic, and the work, of order `n²`, is checked at that order. A test that reads each
/// link through its term only when it changes cannot do better, since the narrowed range of
/// each link is in the output.
#[test]
fn a_test_that_narrows_every_link_reads_every_link_once() {
    let (a, _) = term_reads(&else_halvings(3, 2));
    assert_eq!(ints_of(&a, "(z3 > 0)", true, "x"), "[8..]");
    assert_eq!(ints_of(&a, "(z2 > 0)", true, "z1"), "[2..=3]");
    assert_eq!(ints_of(&a, "(z2 > 0)", false, "x"), "[..=3]");
    assert_eq!(ints_of(&a, "(z1 > 1)", false, "x"), "[..=1]");
    for n in [3, 8, 32, 64] {
        let n64 = n as u64;
        assert_eq!(
            term_reads(&else_halvings(n, 2)).1,
            n64 * (n64 + 1),
            "{n} links"
        );
    }
    let chains = scaling::inputs(16, |n| else_halvings(n, 2));
    let x = ints(&["x".into()]);
    scaling::check_order(
        "a chain of n bindings `zj = z(j-1) div 2` under an `else` chain of 2 tests each",
        16,
        2,
        |n| {
            zedc::store::product::arms(&chains[&n], &x);
        },
    );
}
