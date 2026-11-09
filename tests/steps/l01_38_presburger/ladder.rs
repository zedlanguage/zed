//! Rung 2 of the discharge ladder at its boundaries with the rungs around it (LADDER-study;
//! the study is docs/studies/ladder.md; DESIGN.md sec:verification, "The discharge ladder").
//! Each test is one class of corner case: an obligation rung 2 only just proves, one it only
//! just leaves open, one it must refute, one where a wrong "proved" or a wrong refutation would
//! be unsound, and the determinism cases. Rung 2 is called directly on an obligation: the
//! premise and the goal are the bodies of `ok`, translated in one call.
//!
//! "Proved" is `Proved(#domain)` and ends rungs 1 to 7; "refuted" ends the ladder; "not
//! proved" and "refused" leave the obligation to the next rung (sec:verification, rung 2: "the
//! store's lattices and Presburger layer settle the residual where their polynomial
//! procedures reach it"; sec:domains: a refused question "is reported as not proved").

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::Value;
use zed_tests::scaling;
use zed_tests::step_helpers::l01_25_preimage_catalog::int_ok;
use zedc::store::preimage::relations;
use zedc::store::presburger::{
    self, Atom, Con, Entailment, Factor, Formula, Lin, Relation, entails,
};

use super::entailment::rung2;
use super::{at, holds, point, window};

/// The kind of a verdict, which must not depend on the order or names of what was written.
fn kind(e: &Entailment) -> &'static str {
    match e {
        Entailment::Proved(_) => "proved",
        Entailment::Refuted(_) => "refuted",
        Entailment::NotProved(_) => "not proved",
        Entailment::Refused(_) => "refused",
    }
}

fn assert_proved(premise: &str, goal: &str) {
    let e = rung2(premise, goal);
    assert!(
        matches!(e, Entailment::Proved(_)),
        "{premise} to {goal}: {e}"
    );
}

/// The witness of a refutation, checked against the interpreter: the premise holds there and
/// the goal does not give `true`.
fn refuted_at(premise: &str, goal: &str) -> Vec<i64> {
    let e = rung2(premise, goal);
    let Entailment::Refuted(m) = &e else {
        panic!("{premise} to {goal}: {e}")
    };
    let (ps, p) = function(premise);
    let (_, g) = function(goal);
    let w = point(m, &ps);
    assert!(holds(&p, &ps, &w) && !holds(&g, &ps, &w), "{goal} at {w:?}");
    w
}

/// Whether the goal holds at every point of the window `[-4..=4]` where the premise does, so
/// that a test can tell a true fact rung 2 leaves open from a false one.
fn true_on_window(premise: &str, goal: &str) -> bool {
    let (ps, p) = function(premise);
    let (_, g) = function(goal);
    window(ps.len(), -4, 4)
        .iter()
        .all(|w| !holds(&p, &ps, w) || holds(&g, &ps, w))
}

/// The parameters and body of `ok` in `src`, each of its parameters written without a type
/// declared `int` ([`int_ok`]): rung 2 reads integers, and a bare literal no longer makes a
/// parameter `int` (L1.26a).
fn function(src: &str) -> (Vec<Arc<str>>, zed_kernel::Term) {
    zed_tests::step_helpers::l01_25_preimage_catalog::function(&int_ok(src))
}

const TRUE: &str = "ok(x: int, y: int) = true;";

#[test]
fn products_of_two_symbols_are_settled_in_the_polynomial_normal_form() {
    // "Each side of a comparison is first put in a sparse polynomial normal form over ℤ, of
    // any degree: products of sums are expanded ... and like monomials are merged."
    for goal in [
        "ok(x, y) = x * y == y * x;",
        "ok(x, y) = (x + y) * (x - y) == x * x - y * y;",
        "ok(x, y) = x + (y + x) == (x + x) + y;",
        "ok(x, y) = (x + 1) * (x + 1) == x * x + 2 * x + 1;",
        "ok(x, y) = x * 0 == 0;",
    ] {
        assert_proved(TRUE, goal);
    }
}

#[test]
fn a_square_is_bounded_only_from_a_premise_on_its_factor() {
    // "for each product of two symbols the residual mentions, the premises on its factors are
    // multiplied in pairs once": with no premise on `a` nothing is multiplied, and the true
    // `a * a >= 0` is left open, never refuted, since its countermodel gives the atom `a * a`
    // a value no square has. With a premise it is proved, the premise squared.
    let goal = "ok(a) = a * a >= 0;";
    let e = rung2("ok(a) = true;", goal);
    assert!(matches!(e, Entailment::NotProved(_)), "{e}");
    assert!(true_on_window("ok(a) = true;", goal));
    assert_proved("ok(a) = a >= 0;", goal);
    // From `-a - 1 >= 0` squared, `a * a >= -2 * a - 1 >= 1`.
    assert_proved("ok(a) = a <= -1;", "ok(a) = a * a >= 1;");
    // One less in the premise and the bound is lost: `a = 0` gives `0 >= 1` false.
    let w = refuted_at("ok(a) = a <= 0;", "ok(a) = a * a >= 1;");
    assert_eq!(w, [0]);
    // Both rung 1 and rung 2 settle `k * k <= 2 * k` over `k: 0 | 1 | 2`: rung 2 from the
    // product of `k >= 0` and `2 - k >= 0`. The ladder's order gives it `CheckedExhaustive`
    // at rung 1, never `Proved(#domain)` (the two grades are incomparable; the ladder is
    // "spec-fixed, so the grade an obligation reaches is a function of the source").
    assert_proved("ok(k) = 0 <= k && k <= 2;", "ok(k) = k * k <= 2 * k;");
}

#[test]
fn a_false_product_fact_is_never_proved_and_a_refutation_is_only_a_real_one() {
    // `y >= 0 && w <= 0` gives `y * w <= 0`, not `>= 0`; `y <= z` gives `x * y <= x * z`
    // only where `x >= 0`. Both are false. Rung 2 finds a point that gives the product atom a
    // value no product has, so it does not refute either; rung 6 or rung 7 must ("A
    // refutation is a real refutation and comes with a trace").
    for (premise, goal) in [
        ("ok(y, w) = y >= 0 && w <= 0;", "ok(y, w) = y * w >= 0;"),
        (
            "ok(x: int, y: int, z: int) = y <= z;",
            "ok(x, y, z) = x * y <= x * z;",
        ),
    ] {
        assert!(!true_on_window(premise, goal), "{goal} is false");
        match rung2(premise, goal) {
            Entailment::NotProved(_) => {}
            Entailment::Refuted(_) => {
                refuted_at(premise, goal);
            }
            e => panic!("{goal}: {e}"),
        }
    }
    assert_proved("ok(y, w) = y >= 0 && w <= 0;", "ok(y, w) = y * w <= 0;");
}

#[test]
fn a_true_residue_fact_is_not_refuted_before_the_falling_factorial_test() {
    // "So `(x * (x + 1)) mod 2 == 0` is `Proved` with no facet on `x` ... and with
    // `x mod 2 == 1`, `(x * x) mod 8 == 1` is `Proved`." Until step MOD-residue the two are
    // left open; a refutation would end the ladder on a true fact.
    for (premise, goal) in [
        ("ok(x) = true;", "ok(x) = (x * (x + 1)) mod 2 == 0;"),
        ("ok(x) = x mod 2 == 1;", "ok(x) = (x * x) mod 8 == 1;"),
    ] {
        assert!(true_on_window(premise, goal), "{goal}");
        let e = rung2(premise, goal);
        assert!(!matches!(e, Entailment::Refuted(_)), "{goal}: {e}");
    }
}

#[test]
fn false_linear_and_min_max_facts_are_refuted_with_a_witness_the_interpreter_confirms() {
    // `(x in 0..<n).implies(x + 1 <= n)` is proved; the next index is refuted.
    assert_proved("ok(x, n) = 0 <= x && x < n;", "ok(x, n) = x + 1 <= n;");
    assert_eq!(
        refuted_at("ok(x, n) = 0 <= x && x < n;", "ok(x, n) = x + 2 <= n;"),
        [0, 1]
    );
    refuted_at(TRUE, "ok(x, y) = (2 * x) mod 2 == 2;");
    refuted_at(
        "ok(a: int, b: int, c: int) = a <= c;",
        "ok(a, b, c) = max(a, b) <= c;",
    );
    assert_proved(
        "ok(a: int, b: int, c: int) = a <= c && b <= c;",
        "ok(a, b, c) = max(a, b) <= c;",
    );
}

const CLAMP: &str = "clamp(positional v, positional l, positional h) = if v < l { l } else if v > h { h } else { v };\n";

#[test]
fn clamp_is_in_range_exactly_when_lo_is_at_most_hi() {
    // "`clamp(x, lo, hi) in lo..=hi` is exact `min`/`max` transfer": it holds from
    // `lo <= hi`, and without that premise it is false (`lo = 1, hi = 0`), which DESIGN's
    // example leaves out (docs/studies/ladder.md, defect D5). `clamp` as DESIGN writes it
    // (sec:grammar), an `if` chain, and as `max` of `min`.
    let chain = format!("{CLAMP}ok(x, lo, hi) = lo <= clamp(x, lo, hi) && clamp(x, lo, hi) <= hi;");
    let minmax = "ok(x, lo, hi) = lo <= max(lo, min(x, hi)) && max(lo, min(x, hi)) <= hi;";
    for range in [chain.as_str(), minmax] {
        assert_proved("ok(x: int, lo: int, hi: int) = lo <= hi;", range);
        assert!(!true_on_window(
            "ok(x: int, lo: int, hi: int) = true;",
            range
        ));
    }
    // Without the premise, both are refuted at a point with `lo > hi`. The `if` chain, three
    // nested disjunctions, was refused until S22-shapes-linear, and the obligation went on to
    // rung 5, whose split on `v < l` gives halves rung 2 refutes; now the search for a
    // countermodel answers with the first point its probe finds where the rest of its search
    // refuses (`presburger::found`).
    for range in [minmax, chain.as_str()] {
        let w = refuted_at("ok(x: int, lo: int, hi: int) = true;", range);
        assert!(w[1] > w[2], "{w:?}");
    }
}

#[test]
fn a_helper_without_recursion_is_unfolded_at_each_call() {
    // "A call, reached by name or through a function value, is unfolded: its callee's body
    // with the arguments bound gives its value." The helper's binder is named apart from
    // `ok`'s, so elaboration does not rename `x`. Its parameter is declared `int`: written
    // without a type, `u + 1` would be generic (L1.26a), and rung 2 reads integers.
    let g = "g(positional u: int) = u + 1;\n";
    assert_proved("ok(x) = true;", &format!("{g}ok(x) = g(x) > x;"));
    assert_proved("ok(x) = true;", &format!("{g}ok(x) = g(g(x)) == x + 2;"));
    let w = refuted_at("ok(x) = true;", &format!("{g}ok(x) = g(g(x)) == x + 1;"));
    assert_eq!(w.len(), 1);
}

#[test]
fn contradictory_premises_close_a_part() {
    // Rung 5: "A half whose premises rung 2 shows inconsistent is excluded with every path in
    // it". A residue premise no remainder meets is inconsistent, so any goal follows.
    assert_proved("ok(x) = x mod 2 == 3;", "ok(x) = false;");
    assert_proved("ok(a) = a > 0 && a <= 0;", "ok(a) = a == 7;");
}

#[test]
fn a_refutation_at_a_zero_divisor_is_a_point_where_the_operation_fails() {
    // "at `n == 0`, where the operation fails, they are left free ... from `n >= 0` neither
    // is." Rung 2 refutes `x mod n < n` with the witness `n = 0`, where the goal is no
    // boolean: `x mod 0` gives the atom `#divByZero`. DESIGN does not say whether such a point is a refutation
    // (docs/studies/ladder.md, defect D4); this test fixes what rung 2 does today.
    let (premise, goal) = ("ok(x, n) = n == 0;", "ok(x, n) = x mod n < 1;");
    let e = rung2(premise, goal);
    let Entailment::Refuted(m) = &e else {
        panic!("{e}")
    };
    let (ps, g) = function(goal);
    let w = point(m, &ps);
    assert_eq!(w[1], 0);
    let v = at(&g, &ps, &w);
    assert!(
        matches!(v, Some(Value::Atom(_))),
        "the goal fails at {w:?}: {v:?}"
    );
    // The contrast: a guard that excludes the zero divisor removes the failing point, and the
    // goal is proved. A residual that drops a `mod` by a divisor that may be zero, as
    // `(x mod n) * 0 == 0`, is `false` at `n = 0`, so it is proved only where a premise
    // excludes the zero (RUNG2-definedness, docs/studies/ladder.md defect D9; the tests
    // below).
    assert_proved(
        "ok(x, n) = true;",
        "ok(x, n) = if n != 0 { x mod n < n || x mod n < 0 - n } else { true };",
    );
    assert_proved("ok(x, n) = n >= 1;", "ok(x, n) = (x mod n) * 0 == 0;");
}

/// Rung 2's verdict on `premise` to `goal`, checked against the interpreter: a proved goal
/// gives `true` at every point of the window where the premise does, and a refutation's
/// witness is a point where the premise gives `true` and the goal does not.
fn checked(premise: &str, goal: &str) -> Entailment {
    let e = rung2(premise, goal);
    match &e {
        Entailment::Proved(_) => assert!(true_on_window(premise, goal), "{premise} to {goal}"),
        Entailment::Refuted(_) => _ = refuted_at(premise, goal),
        _ => {}
    }
    e
}

#[test]
fn a_residual_that_drops_a_failing_operation_is_not_proved() {
    // RUNG2-definedness (D9, U1): the `mod` is gone from the linear term, but at `n = 0` it
    // gives `#divByZero`, which `* 0` passes on, and `#divByZero == 0` is `false`.
    for goal in [
        "ok(x, n) = (x mod n) * 0 == 0;",
        "ok(x, n) = x mod n - x mod n == 0;",
    ] {
        for premise in ["ok(x, n) = true;", "ok(x, n) = n >= 0;"] {
            let e = checked(premise, goal);
            assert!(
                !matches!(e, Entailment::Proved(_)),
                "{premise} to {goal}: {e}"
            );
        }
    }
}

#[test]
fn a_point_where_an_operation_fails_is_a_witness_only_where_the_interpreter_agrees() {
    // RUNG2-definedness (D9, U2 and U3): at `n = 0` the premise `n >= 0 && x mod n == 0` is
    // `false` (`#divByZero == 0`), so `n = 0` is no witness against `n >= 1`; and
    // `x mod n == (x + 1) mod n` is `true` there, both sides `#divByZero` (DESIGN.md M0.9
    // (a): `==` compares atoms).
    for (p, g) in [
        ("ok(x, n) = n >= 0 && x mod n == 0;", "ok(x, n) = n >= 1;"),
        ("ok(x, n) = n == 0;", "ok(x, n) = x mod n == (x + 1) mod n;"),
    ] {
        if let Entailment::Refuted(_) = rung2(p, g) {
            refuted_at(p, g);
        }
        // Both hold: the first since the premise fails at `n = 0`, the second since both
        // sides fail alike.
        assert!(true_on_window(p, g), "{p} to {g}");
        assert_proved(p, g);
    }
}

#[test]
fn each_partial_operation_and_each_place_it_fails_in_agrees_with_the_interpreter() {
    // Only `div` and `mod` by a term fail at a point of the linear-relation domain; each place
    // a failure can reach the test is checked: an operand of an operation, a `!`, the first
    // and the second operand of `||` and `&&`, an `if`'s guard and arm, `==` and `!=` of two
    // operands that may fail, and an argument of a call. Each verdict is checked against the
    // interpreter, and the kind is fixed.
    let not_proved = [
        // `div` as `mod`: `#divByZero * 0` is no integer.
        ("ok(x, n) = true;", "ok(x, n) = (x div n) * 0 == 0;"),
        // Under `!`: `!(#divByZero < 0)` is the atom.
        ("ok(x, n) = true;", "ok(x, n) = !(x mod n < 0);"),
        // The failing operand first: `#divByZero >= 0 || ...` is the atom; `||` short-circuits
        // only on `true`.
        ("ok(x, n) = true;", "ok(x, n) = x mod n >= 0 || n == 0;"),
        // An `if` on a failing guard is the atom.
        (
            "ok(x, n) = true;",
            "ok(x, n) = if x mod n >= 0 { true } else { true };",
        ),
        // A failing arm the guard takes, in an integer `if`.
        (
            "ok(x, n) = true;",
            "ok(x, n) = (if x > 0 { x mod n } else { 0 }) * 0 == 0;",
        ),
        // `==` of two tests one of which fails.
        ("ok(x, n) = true;", "ok(x, n) = (x mod n < 0) == false;"),
    ];
    for (p, g) in not_proved {
        let e = checked(p, g);
        assert!(!matches!(e, Entailment::Proved(_)), "{p} to {g}: {e}");
        assert!(!true_on_window(p, g), "{p} to {g}");
    }
    let proved = [
        ("ok(x, n) = n != 0;", "ok(x, n) = (x div n) * 0 == 0;"),
        // The guard first: `n == 0 || ...` is `true` before the `mod` is read.
        ("ok(x, n) = true;", "ok(x, n) = n == 0 || x mod n >= 0;"),
        (
            "ok(x, n) = true;",
            "ok(x, n) = n != 0 && x mod n >= 0 || n == 0;",
        ),
        // The arm the guard takes never fails.
        (
            "ok(x, n) = x <= 0;",
            "ok(x, n) = (if x > 0 { x mod n } else { 0 }) * 0 == 0;",
        ),
        // Two failures compare equal, and differ from every integer and boolean.
        (
            "ok(x, n) = true;",
            "ok(x, n) = (x mod n < 0) == (x mod n < 0);",
        ),
        ("ok(x, n) = n == 0;", "ok(x, n) = x mod n != 0;"),
        ("ok(x, n) = n == 0;", "ok(x, n) = x div n != x;"),
    ];
    for (p, g) in proved {
        let e = checked(p, g);
        assert!(matches!(e, Entailment::Proved(_)), "{p} to {g}: {e}");
    }
}

#[test]
fn a_call_with_an_argument_that_may_fail_is_read_at_its_place() {
    // `f((x mod n) * 0)` and `f(0)` pass arguments with the same linear term, `0`, but at
    // `n = 0` the first is `#divByZero`, so `f` gives `false` there and `true` for `0`. A call
    // shared by the arguments' terms would prove the goal; the call is shared only with calls
    // whose arguments have the same terms and the same conditions
    // ([`Walk::shared_call_key`] in preimage.rs). Written without a type, `a == 0` follows
    // the carrier of `a` (L1.26a), the comparison of an atom with `0` is `false`, and rung 2
    // refutes both goals at `n = 0`, a point the interpreter confirms ([`checked`]).
    let f = "f(positional a) = a == 0;\n";
    for goal in [
        format!("{f}ok(x, n) = f((x mod n) * 0) == f(0);"),
        format!("{f}ok(x, n) = f(x mod n);"),
    ] {
        let e = checked("ok(x, n) = true;", &goal);
        assert!(matches!(e, Entailment::Refuted(_)), "{goal}: {e}");
    }
    // With `a` declared `int`, an argument that fails bubbles out of the call, which rung 2
    // does not yet translate where the argument holds a quotient or remainder by a term, with
    // or without the condition, so it takes nothing here.
    let f = "f(positional a: int) = a == 0;\n";
    for goal in [
        format!("{f}ok(x, n) = f((x mod n) * 0) == f(0);"),
        format!("{f}ok(x, n) = f(x mod n);"),
    ] {
        let (ps, p) = function("ok(x, n) = true;");
        let (_, g) = function(&goal);
        assert!(relations(&[&p, &g], &ps, true).is_none(), "{goal}");
    }
    // A call binds an atom as a value: a parameter that is not read does not fail, and a call
    // with an argument that may fail is read at its place, beside one that is shared.
    let g = "g(positional a, positional b) = b;\n";
    for goal in [
        format!("{g}ok(x, n) = g(x mod n, x) == x;"),
        format!("{g}ok(x, n) = g(x mod n, x) == g(0, x);"),
    ] {
        assert!(true_on_window("ok(x, n) = true;", &goal), "{goal}");
        let e = checked("ok(x, n) = true;", &goal);
        assert!(matches!(e, Entailment::Proved(_)), "{goal}: {e}");
    }
    // A function whose body fails where its argument is 0, called with one.
    let h = "h(positional a, positional m) = a mod m;\n";
    let goal = format!("{h}ok(x, n) = h(x, n) * 0 == 0;");
    assert!(!matches!(
        checked("ok(x, n) = true;", &goal),
        Entailment::Proved(_)
    ));
    assert_proved("ok(x, n) = n <= -1;", &goal);
}

/// The premise `n >= 1` and the goal `(x mod (n + 0)) * 0 + ... == 0` over `k` divisors,
/// translated.
fn divisors(k: usize) -> (Relation, Relation) {
    let head = "ok(x, n)";
    let goal: Vec<String> = (0..k).map(|i| format!("(x mod (n + {i})) * 0")).collect();
    let (ps, p) = function(&format!("{head} = n >= 1;"));
    let (_, g) = function(&format!("{head} = {} == 0;", goal.join(" + ")));
    let mut rs = relations(&[&p, &g], &ps, true).expect("in the domain");
    let g = rs.pop().expect("two relations");
    (rs.pop().expect("two relations"), g)
}

/// The premise `true` and the goal `(n + 0 == 0 || x mod (n + 0) >= 0) && ...` over `k`
/// divisors, each guarded by its own test, translated.
fn guarded_divisors(k: usize) -> (Relation, Relation) {
    let head = "ok(x, n)";
    let goal: Vec<String> = (0..k)
        .map(|i| format!("(n + {i} == 0 || x mod (n + {i}) >= 0)"))
        .collect();
    let (ps, p) = function(&format!("{head} = true;"));
    let (_, g) = function(&format!("{head} = {};", goal.join(" && ")));
    let mut rs = relations(&[&p, &g], &ps, true).expect("in the domain");
    let g = rs.pop().expect("two relations");
    (rs.pop().expect("two relations"), g)
}

#[test]
fn the_condition_that_no_operation_fails_scales() {
    // One condition `n + i != 0` for each of k divisors, each made once, and k divisors each
    // shown not 0 by the guard of its `||`, so that no condition is left; the translation is
    // timed at k and 8k. The entailment is checked at k here and timed in
    // `a_chain_of_guarded_remainders_scales` and `a_chain_of_remainders_by_terms_scales`.
    // COMPLEXITY.md rows RUNG2-definedness, PRES-mod-conjuncts and PRES-guarded-chain.
    let n = 16;
    for (p, g) in [divisors(n), guarded_divisors(n)] {
        let e = entails(&p, &g);
        assert!(matches!(e, Entailment::Proved(_)), "{e}");
    }
    let measure = move || {
        scaling::check_order("the definedness of k remainders by terms", n, 1, |k| {
            divisors(k);
        });
        scaling::check_order("the definedness of k guarded remainders", n, 1, |k| {
            guarded_divisors(k);
        });
    };
    let thread = std::thread::Builder::new().stack_size(8 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

#[test]
fn a_chain_of_guarded_remainders_scales() {
    // PRES-guarded-chain: the goal `(n + 0 == 0 || x mod (n + 0) >= 0) && ...` over k
    // divisors under the premise `true`. Its negation is a disjunction of k disjuncts
    // `n + i != 0 && x mod (n + i) < 0`, each refuted only through the cases of its own
    // remainder's definition, and each was refuted by a settling of the whole formula: 1.14G
    // instructions at k = 16 and 148.6G at k = 128, 130 times (measured 2026-11-08). Now each is
    // refuted by a settling of its own definition alone (`refuted_by_links` in `probe`). The
    // entailment is timed at k and 8k. COMPLEXITY.md row PRES-guarded-chain.
    let n = 16;
    let (p, g) = guarded_divisors(n);
    assert_eq!(kind(&entails(&p, &g)), "proved");
    let measure = move || {
        let inputs = scaling::inputs(n, guarded_divisors);
        scaling::check_order("a chain of guarded remainders", n, 1, |k| {
            let (p, g) = &inputs[&k];
            assert_eq!(kind(&entails(p, g)), "proved");
        });
    };
    let thread = std::thread::Builder::new().stack_size(8 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

/// The premise `premise` and the goal `x mod (n + 0) >= 0 && ...` over `k` divisors, a chain
/// of `&&` written from the left, translated.
fn remainder_chain(premise: &str, k: usize) -> (Relation, Relation) {
    let head = "ok(x, n)";
    let goal: Vec<String> = (0..k).map(|i| format!("x mod (n + {i}) >= 0")).collect();
    let (ps, p) = function(&format!("{head} = {premise};"));
    let (_, g) = function(&format!("{head} = {};", goal.join(" && ")));
    let mut rs = relations(&[&p, &g], &ps, true).expect("in the domain");
    let g = rs.pop().expect("two relations");
    (rs.pop().expect("two relations"), g)
}

#[test]
fn a_chain_of_remainders_by_terms_scales() {
    // PRES-mod-conjuncts: a `&&` of k conjuncts written from the left, each reading a
    // remainder by a term of its own. Read as nested `if`s, its condition held the negation of
    // each prefix, Θ(k²) constraints, and each remainder's definition was repaired by reading
    // all k definitions that share `n` and `x`: from k = 16 to 128, 28 times the work under
    // the premise `true` and 22 times the work under `n >= 1` after the first fix alone
    // (measured 2026-11-08; 2.04G instructions at k = 16 before either). The entailment is
    // timed at k and 8k. Under `n >= 1` it is proved; under `true` it is refuted at a
    // divisor 0. COMPLEXITY.md row PRES-mod-conjuncts.
    let n = 16;
    let cases = [
        ("proved", "a chain of remainders by terms", "n >= 1"),
        ("refuted", "a chain of remainders that may fail", "true"),
    ];
    for (verdict, _, premise) in cases {
        let (p, g) = remainder_chain(premise, n);
        assert_eq!(kind(&entails(&p, &g)), verdict, "{premise}");
    }
    let measure = move || {
        for (verdict, what, premise) in cases {
            let inputs = scaling::inputs(n, |k| remainder_chain(premise, k));
            scaling::check_order(what, n, 1, |k| {
                let (p, g) = &inputs[&k];
                assert_eq!(kind(&entails(p, g)), verdict);
            });
        }
        let inputs = scaling::inputs(n, divisors);
        scaling::check_order("a sum of remainders by terms", n, 1, |k| {
            let (p, g) = &inputs[&k];
            assert_eq!(kind(&entails(p, g)), "proved");
        });
    };
    let thread = std::thread::Builder::new().stack_size(8 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

#[test]
fn conditionals_are_refused_raw_and_proved_once_joined() {
    // Rung 5: "Rung 2 is first asked about a part with each conditional's value the join of
    // its arms in the store's lattices, each arm with its condition as a premise, so
    // `(if a > 0 { 1 } else { 0 }) + (if b > 0 { 1 } else { 0 }) <= 2` is proved with no
    // split." Asked raw, rung 2 refuses: `a` and `b` are interchangeable, which the
    // Presburger layer refuses (sec:domains). Joined, each value in `0..=1`, it is proved.
    let raw = "ok(a, b) = (if a > 0 { 1 } else { 0 }) + (if b > 0 { 1 } else { 0 }) <= 2;";
    let e = rung2("ok(a, b) = true;", raw);
    assert!(matches!(e, Entailment::Refused(_)), "{e}");
    assert_proved(
        "ok(p, q) = 0 <= p && p <= 1 && 0 <= q && q <= 1;",
        "ok(p, q) = p + q <= 2;",
    );
}

#[test]
fn the_halves_of_the_triangle_inequality_are_refused_for_their_symmetry() {
    // Rung 5: the triangle inequality "splits once, on `a + b >= 0`, ... and both halves close
    // at rung 2 from the joins of the left side". Each half, the joins of `|a|` and `|b|`
    // written as `p` and `q`, is symmetric under swapping `a` with `b` and `p` with `q`, and
    // the Presburger layer refuses it ("When two atoms share a color the formula is not
    // searched"). The two sentences of DESIGN disagree (docs/studies/ladder.md, defect D3);
    // this test fixes what rung 2 does today.
    let abs = "ok(a, b, p, q) = p >= a && p >= -a && q >= b && q >= -b";
    for (cond, goal) in [
        ("a + b >= 0", "ok(a, b, p, q) = p + q >= a + b;"),
        ("a + b <= -1", "ok(a, b, p, q) = p + q >= -a - b;"),
    ] {
        let e = rung2(&format!("{abs} && {cond};"), goal);
        assert!(matches!(e, Entailment::Refused(_)), "{cond}: {e}");
    }
    // Asymmetric, the same half is proved.
    assert_proved(
        &format!("{abs} && a + b >= 0 && a >= 3;"),
        "ok(a, b, p, q) = p + q >= a + b;",
    );
}

#[test]
fn outside_the_fragment_rung_2_takes_nothing() {
    // A `bool` binder is rung 1's (its domain is listed), and a monomial of three symbols is
    // "an atom for which no premises are multiplied", outside the fragment written flat.
    for goal in [
        "ok(a: bool, b: bool) = (a && b) == (b && a);",
        "ok(x, y, z) = x * y * z >= 0;",
    ] {
        let (ps, g) = function(goal);
        assert!(relations(&[&g], &ps, true).is_none(), "{goal}");
    }
}

#[test]
fn the_verdict_does_not_depend_on_order_or_names() {
    // "the grade an obligation reaches is a function of the source and its pins, the same in
    // every compiler": reordering the premise's or the goal's conjuncts, renaming binders, and
    // translating the goal before the premise give the same verdict, for each kind.
    let cases = [
        (
            ["ok(x, n) = 0 <= x && x < n;", "ok(x, n) = x < n && 0 <= x;"],
            [
                "ok(x, n) = x + 1 <= n && 0 <= x;",
                "ok(x, n) = 0 <= x && x + 1 <= n;",
            ],
            "proved",
        ),
        (
            ["ok(x, n) = 0 <= x && x < n;", "ok(x, n) = x < n && 0 <= x;"],
            ["ok(x, n) = x + 2 <= n;", "ok(x, n) = n >= x + 2;"],
            "refuted",
        ),
        (
            ["ok(x, n) = true;", "ok(x, n) = true;"],
            ["ok(x, n) = x * x >= 0;", "ok(x, n) = 0 <= x * x;"],
            "not proved",
        ),
        (
            ["ok(x, n) = true;", "ok(x, n) = true;"],
            [
                "ok(x, n) = (if x > 0 { 1 } else { 0 }) + (if n > 0 { 1 } else { 0 }) <= 2;",
                "ok(x, n) = (if n > 0 { 1 } else { 0 }) + (if x > 0 { 1 } else { 0 }) <= 2;",
            ],
            "refused",
        ),
    ];
    let renamed = |s: &str| {
        s.replace("ok(x, n)", "ok(u, m)")
            .replace('x', "u")
            .replace('n', "m")
    };
    for (premises, goals, want) in cases {
        for p in premises {
            for g in goals {
                assert_eq!(kind(&rung2(p, g)), want, "{p} to {g}");
                let (p2, g2) = (renamed(p), renamed(g));
                assert_eq!(kind(&rung2(&p2, &g2)), want, "{p2} to {g2}");
                let (ps, pt) = function(p);
                let (_, gt) = function(g);
                let rs = relations(&[&gt, &pt], &ps, true).expect("in the domain");
                assert_eq!(
                    kind(&entails(&rs[1], &rs[0])),
                    want,
                    "goal first: {p} to {g}"
                );
            }
        }
    }
}

/// The premise `x{i} >= i && y{i} >= 2 * i + 1` for each `i < k` and the goal
/// `x0 * y0 + ... >= 0`, translated: `k` products of two symbols, each factor bounded below by
/// its own constant, so no two names are interchangeable.
fn product_sum(k: usize) -> (Relation, Relation) {
    let names: Vec<String> = (0..k).map(|i| format!("x{i}, y{i}")).collect();
    let head = format!("ok({})", names.join(", "));
    let premise: Vec<String> = (0..k)
        .map(|i| format!("x{i} >= {i} && y{i} >= {}", 2 * i + 1))
        .collect();
    let goal: Vec<String> = (0..k).map(|i| format!("x{i} * y{i}")).collect();
    let (ps, p) = function(&format!("{head} = {};", premise.join(" && ")));
    let (_, g) = function(&format!("{head} = {} >= 0;", goal.join(" + ")));
    let mut rs = relations(&[&p, &g], &ps, true).expect("in the domain");
    let g = rs.pop().expect("two relations");
    (rs.pop().expect("two relations"), g)
}

#[test]
fn products_of_premises_in_pairs_scale() {
    // The pairs are taken per product, each from the premises on its two factors; with one
    // lower bound on each factor that is one pair per product.
    let n = 16;
    let built: BTreeMap<usize, (Relation, Relation)> = [n, n * scaling::FACTOR]
        .into_iter()
        .map(|k| (k, product_sum(k)))
        .collect();
    let measure = move || {
        scaling::check("a sum of products of bounded factors entailed", n, |k| {
            let (p, g) = &built[&k];
            let e = entails(p, g);
            assert!(matches!(e, Entailment::Proved(_)), "{k}: {e}");
        });
    };
    let thread = std::thread::Builder::new().stack_size(8 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

/// The chain `z0 >= 0 && z1 >= z0 + 1 && ... && z{k-1} >= z{k-2} + 1 && z{k-1} <= 2 * k`, the
/// links `x{i} >= z{i} && y{i} >= z{i}`, and the goal `x0 * y0 + ... >= 0`, translated: `k`
/// products whose factors one chain of premises connects, so that every factor lies in one part
/// of the premise rows, and each is bounded below by its own constant `i`, which only the chain
/// gives.
fn product_chain(k: usize) -> (Relation, Relation) {
    product_chain_with(k, &[])
}

/// [`product_chain`] with the rows `extra` added to the premise.
fn product_chain_with(k: usize, extra: &[String]) -> (Relation, Relation) {
    let (premise, goal) = product_chain_source(k, extra);
    let (ps, p) = function(&premise);
    let (_, g) = function(&goal);
    let mut rs = relations(&[&p, &g], &ps, true).expect("in the domain");
    let g = rs.pop().expect("two relations");
    (rs.pop().expect("two relations"), g)
}

/// The premise and the goal of [`product_chain_with`], as written.
fn product_chain_source(k: usize, extra: &[String]) -> (String, String) {
    let names: Vec<String> = (0..k).map(|i| format!("x{i}, y{i}, z{i}")).collect();
    let head = format!("ok({})", names.join(", "));
    let mut premise = vec!["z0 >= 0".to_string()];
    premise.extend((1..k).map(|i| format!("z{i} >= z{} + 1", i - 1)));
    premise.push(format!("z{} <= {}", k - 1, 2 * k));
    premise.extend((0..k).map(|i| format!("x{i} >= z{i} && y{i} >= z{i}")));
    premise.extend(extra.iter().cloned());
    let goal: Vec<String> = (0..k).map(|i| format!("x{i} * y{i}")).collect();
    (
        format!("{head} = {};", premise.join(" && ")),
        format!("{head} = {} >= 0;", goal.join(" + ")),
    )
}

#[test]
fn products_whose_factors_one_chain_connects_scale() {
    // Every factor lies in one part, the chain; its atoms are bounded in one pass over the
    // part, not each by its own questions over the whole part (C2-chain): no side of a hull is
    // asked of the solver.
    let n = 16;
    let built = scaling::inputs(n, product_chain);
    let measure = move || {
        scaling::check("a sum of products along one chain entailed", n, |k| {
            let (p, g) = &built[&k];
            presburger::hull_sides_asked();
            let e = entails(p, g);
            assert!(matches!(e, Entailment::Proved(_)), "{k}: {e}");
            assert_eq!(presburger::hull_sides_asked(), 0, "{k}");
        });
    };
    scaling::on_a_thread(8 << 20, measure);
}

#[test]
fn products_along_a_chain_with_a_general_row_scale() {
    // The chain of `product_chain` and one row of three atoms, which is not a difference
    // constraint (C2-chain-general); no side of a hull is asked of the solver.
    let n = 16;
    let built = scaling::inputs(n, |k| {
        product_chain_with(k, &["z0 + z1 + x0 >= 0".to_string()])
    });
    let measure = move || {
        scaling::check(
            "a sum of products along a chain with a general row",
            n,
            |k| {
                let (p, g) = &built[&k];
                presburger::hull_sides_asked();
                let e = entails(p, g);
                assert!(matches!(e, Entailment::Proved(_)), "{k}: {e}");
                assert_eq!(presburger::hull_sides_asked(), 0, "{k}");
            },
        );
    };
    scaling::on_a_thread(8 << 20, measure);
}

#[test]
fn products_along_a_chain_with_a_general_row_on_each_link_scale() {
    // The chain of `product_chain` with one general row on each link, a coefficient 2 and
    // three atoms: k general rows in the one part (C2-chain-general).
    let n = 16;
    let built = scaling::inputs(n, |k| {
        let extra: Vec<String> = (0..k).map(|i| format!("2 * x{i} + y{i} >= z{i}")).collect();
        product_chain_with(k, &extra)
    });
    let measure = move || {
        scaling::check(
            "a sum of products along a chain with k general rows",
            n,
            |k| {
                let (p, g) = &built[&k];
                let e = entails(p, g);
                assert!(matches!(e, Entailment::Proved(_)), "{k}: {e}");
            },
        );
    };
    scaling::on_a_thread(8 << 20, measure);
}

#[test]
fn products_along_a_chain_with_a_disjunction_on_each_link_scale() {
    // The chain of `product_chain` with `abs(x{i} - y{i}) <= z{i} + 1` on each link: the
    // definition of each `abs` is a disjunction over the link's atoms, so k disjunctions lie
    // in the one part (C2-chain-general).
    let n = 16;
    let built = scaling::inputs(n, |k| {
        let extra: Vec<String> = (0..k)
            .map(|i| format!("abs(x{i} - y{i}) <= z{i} + 1"))
            .collect();
        product_chain_with(k, &extra)
    });
    let measure = move || {
        scaling::check(
            "a sum of products along a chain with k disjunctions",
            n,
            |k| {
                let (p, g) = &built[&k];
                let e = entails(p, g);
                assert!(matches!(e, Entailment::Proved(_)), "{k}: {e}");
            },
        );
    };
    scaling::on_a_thread(8 << 20, measure);
}

#[test]
fn a_general_row_bounds_a_factor_from_the_bounds_of_its_other_atoms() {
    // `b >= 7` follows from `a + b >= 10` and `a <= 3` alone; `2 * a == b + 4` with `b >= 0`
    // gives `a >= 2`, the equality read in both directions and the bound rounded up; and a
    // bound on one atom with a coefficient, `3 * c >= 7`, gives `c >= 3`.
    assert_proved(
        "ok(a, b, c) = a + b >= 10 && a <= 3 && c >= 0;",
        "ok(a, b, c) = b * c >= 7 * c;",
    );
    assert_proved(
        "ok(a, b, c) = 2 * a == b + 4 && b >= 0 && c >= 0;",
        "ok(a, b, c) = a * c >= 2 * c;",
    );
    assert_proved(
        "ok(a, c) = 3 * c >= 7 && a >= 0;",
        "ok(a, c) = a * c >= 3 * a;",
    );
    // The bound found through a general row reaches the rest of the part through its
    // difference rows: `d >= b + 1` gives `d >= 8`.
    assert_proved(
        "ok(a, b, c, d) = a + b >= 10 && a <= 3 && d >= b + 1 && c >= 0;",
        "ok(a, b, c, d) = d * c >= 8 * c;",
    );
    // A disjunction among the definitions bounds a side of an atom that each disjunct with a
    // point bounds, at the widest, and the bound reaches the rest of the part. `abs(a)` is `a`
    // where `a >= 0` and `-a` where `a < 0`: with no bound on `a` each disjunct gives
    // `abs(a) >= 0`, so `d >= 0`; and with `a >= b`, `b >= 5` the second has no point and the
    // first gives `abs(a) >= 5`, so `d >= 5`. The literal in `d <= 1000` makes `d` an `int`.
    assert_proved(
        "ok(a, c, d) = abs(a) <= d && d <= 1000 && c >= 0;",
        "ok(a, c, d) = d * c >= 0;",
    );
    assert_proved(
        "ok(a, b, c, d) = b >= 5 && a >= b && abs(a) <= d && d <= 1000 && c >= 0;",
        "ok(a, b, c, d) = d * c >= 5 * c;",
    );
    // An atom that no difference row names keeps the bounds found for it: `a >= -1000` from
    // the second disjunct's `a + abs(a) == 0` and `abs(a) <= 1000`, where the point of the
    // part the shortest paths start from gives `a` no value.
    assert_proved(
        "ok(a, c, d) = abs(a) <= d && d <= 1000 && c >= 0;",
        "ok(a, c, d) = a * c >= -1000 * c;",
    );
    // One bound more than the rows give is not proved: `b >= 8` fails at `a = 3, b = 7`.
    let e = rung2(
        "ok(a, b, c) = a + b >= 10 && a <= 3 && c >= 0;",
        "ok(a, b, c) = b * c >= 8 * c;",
    );
    assert!(!matches!(e, Entailment::Proved(_)), "{e}");
}

#[test]
fn a_bound_through_a_general_row_and_difference_rows_is_found() {
    // `v >= w1`, `v >= w2` and `w1 + w2 >= 10` give `2 * v >= 10`, so `v >= 5`: the general
    // row with each atom replaced by its bound through the difference rows to the factor `v`
    // (C2-chain-general, `eliminate` in `part_bounds`), with no question to the solver. With
    // `w1 + w2 >= 9` the bound rounds up to the same `v >= 5`, since `2 * v >= 9` on integers;
    // with `w1 + w2 >= 8` the goal fails at `v = w1 = w2 = 4, c = 1`, and is not proved.
    let at_ten = (
        "ok(v, w1, w2, c) = v >= w1 && v >= w2 && w1 + w2 >= 10 && c >= 0;",
        "ok(v, w1, w2, c) = v * c >= 5 * c;",
    );
    let at_nine = (
        "ok(v, w1, w2, c) = v >= w1 && v >= w2 && w1 + w2 >= 9 && c >= 0;",
        "ok(v, w1, w2, c) = v * c >= 5 * c;",
    );
    // A disjunction written among the premises joins the part of its atoms, and gives the
    // side that each disjunct bounds, at the widest: `a >= 5`.
    let joined = (
        "ok(a, c) = (a >= 5 || a >= 7) && c >= 0;",
        "ok(a, c) = a * c >= 5 * c;",
    );
    for (premise, goal) in [at_ten, at_nine, joined] {
        presburger::hull_sides_asked();
        assert_proved(premise, goal);
        assert_eq!(presburger::hull_sides_asked(), 0, "{premise} to {goal}");
    }
    let (premise, goal) = (
        "ok(v, w1, w2, c) = v >= w1 && v >= w2 && w1 + w2 >= 8 && c >= 0;",
        "ok(v, w1, w2, c) = v * c >= 5 * c;",
    );
    let e = rung2(premise, goal);
    assert!(
        !matches!(e, Entailment::Proved(_)),
        "{premise} to {goal}: {e}"
    );
    assert!(!true_on_window(premise, goal));
}

#[test]
fn a_bound_that_needs_two_general_rows_is_found_by_the_solver() {
    // `b + c <= 3` and `c >= 0` give `b <= 3`, and only then does `a + b >= 10` give `a >= 7`.
    // Where `b` and `c` are not factors they are eliminated first (`shadow` in `part_bounds`),
    // which leaves `a >= 7` as a bound, with no question to the solver.
    presburger::hull_sides_asked();
    assert_proved(
        "ok(a, b, c, d) = a + b >= 10 && b + c <= 3 && c >= 0 && d >= 0;",
        "ok(a, b, c, d) = a * d >= 7 * d;",
    );
    assert_eq!(presburger::hull_sides_asked(), 0);
    // Where `b` and `c` are factors too (of `b * c` in the premise) they are kept, and the
    // bound `b <= 3` found from `b + 2 * c <= 3` is passed on to `a + b >= 10` (`propagate`
    // in `part_bounds`), again with no question. With `b + c >= -100` as well, `b <= 3` and
    // `c >= 0` each wait on the other through the two rows; each is let go with the bound it
    // has, `c >= 0` from `c >= 0`, which gives `b <= 3` and then `a >= 7`.
    for premise in [
        "ok(a, b, c, d) = a + b >= 10 && b + 2 * c <= 3 && c >= 0 && d >= 0 && b * c >= -1000;",
        "ok(a, b, c, d) = a + b >= 10 && b + 2 * c <= 3 && c >= 0 && d >= 0 && b * c >= -1000 \
         && b + c >= -100;",
    ] {
        presburger::hull_sides_asked();
        assert_proved(premise, "ok(a, b, c, d) = a * d >= 7 * d;");
        assert_eq!(presburger::hull_sides_asked(), 0, "{premise}");
    }
    // Complexity tradeoff of `part_bounds` (C2-chain-general): `e` is eliminated, which leaves
    // `a + b >= 10` and `a - 2 * b >= 1`, and `b` is kept, being in a disjunction. `a >= 7`
    // needs both rows at once (twice the first and the second give `3 * a >= 21`), so no one
    // row bounds `a` from the bounds of the others, the goal is not proved from the bounds
    // found, and the sides not known to be hulls are asked of the solver (`products`, first
    // over each factor's cluster), which finds `a >= 7`. With `a * d >= 8 * d` the goal fails at
    // `a = e = 7, b = 3, d = 1`, and is not proved.
    let premise = "ok(a, b, d, e) = a >= e && e + b >= 10 && e - 2 * b >= 1 && (b >= 0 || b <= -5) && d >= 0;";
    presburger::hull_sides_asked();
    assert_proved(premise, "ok(a, b, d, e) = a * d >= 7 * d;");
    assert!(presburger::hull_sides_asked() > 0);
    let goal = "ok(a, b, d, e) = a * d >= 8 * d;";
    let e = rung2(premise, goal);
    assert!(
        !matches!(e, Entailment::Proved(_)),
        "{premise} to {goal}: {e}"
    );
}

#[test]
fn a_chain_bounds_each_factor_by_the_whole_chain() {
    // `x0 * x2 >= 3` needs `x2 >= 3`, which no row on `x2` states: it follows from the chain
    // `x0 >= 1`, `x1 >= x0 + 1`, `x2 >= x1 + 1`, through `(x0 - 1) * (x2 - 3) >= 0`. With
    // `x2 >= 1` in place of the last link it fails at `x0 = x2 = 1`.
    assert_proved(
        "ok(x0, x1, x2) = x0 >= 1 && x1 >= x0 + 1 && x2 >= x1 + 1;",
        "ok(x0, x1, x2) = x0 * x2 >= 3;",
    );
    let e = rung2(
        "ok(x0, x1, x2) = x0 >= 1 && x1 >= x0 + 1 && x2 >= 1;",
        "ok(x0, x1, x2) = x0 * x2 >= 3;",
    );
    assert!(!matches!(e, Entailment::Proved(_)), "{e}");
}

/// The parameters of `ok` in `src`, as written.
fn parameters(src: &str) -> Vec<String> {
    let start = src.find("ok(").expect("a definition `ok`") + 3;
    let end = start + src[start..].find(')').expect("a closed parameter list");
    src[start..end]
        .split(',')
        .map(|p| p.split(':').next().unwrap_or(p).trim().to_string())
        .filter(|p| !p.is_empty())
        .collect()
}

/// `src` with each word (a run of letters, digits and `_`) that `to` names replaced by its
/// image.
fn renamed(src: &str, to: &BTreeMap<String, String>) -> String {
    let mut out = String::with_capacity(src.len());
    let mut word = String::new();
    let flush = |word: &mut String, out: &mut String| {
        out.push_str(to.get(word.as_str()).unwrap_or(word));
        word.clear();
    };
    for c in src.chars() {
        if c.is_ascii_alphanumeric() || c == '_' {
            word.push(c);
        } else {
            flush(&mut word, &mut out);
            out.push(c);
        }
    }
    flush(&mut word, &mut out);
    out
}

/// A verdict written over the names `back` gives each symbol, so that two verdicts compare
/// up to a renaming: its kind, and for a proof each top-level conjunct of its certificate
/// (whose products of premises in pairs carry the bounds found for each factor), sorted, and
/// for a refutation the witness. A point where the linear reading fails is any such point, and
/// a refusal names the variables it could not tell apart, so neither is compared.
fn up_to_names(e: &Entailment, back: &BTreeMap<Arc<str>, Arc<str>>) -> String {
    let sym = |s: &Arc<str>| back.get(s).cloned().unwrap_or_else(|| s.clone());
    let factor = |f: &Factor| match f {
        Factor::Sym(s) => Factor::Sym(sym(s)),
        Factor::Aux(n) => Factor::Aux(*n),
    };
    let atom = |a: &Atom| match a {
        Atom::Sym(s) => Atom::Sym(sym(s)),
        Atom::Product(x, y) => Atom::product_of(factor(x), factor(y)),
        Atom::Aux(n) => Atom::Aux(*n),
    };
    let con = |c: &Con| {
        Formula::Con(Con {
            lin: Lin {
                terms: c
                    .lin
                    .terms
                    .iter()
                    .map(|(a, k)| (atom(a), k.clone()))
                    .collect(),
                constant: c.lin.constant.clone(),
            },
            rel: c.rel,
        })
    };
    fn conjuncts(f: &Formula, out: &mut Vec<String>) {
        match f {
            Formula::And(gs) => gs.iter().for_each(|g| conjuncts(g, out)),
            _ => out.push(f.to_string()),
        }
    }
    match e {
        Entailment::Proved(ps) => {
            let mut shown = Vec::new();
            for p in ps {
                conjuncts(&p.map_cons(&con), &mut shown);
            }
            shown.sort();
            format!("proved from {}", shown.join(" && "))
        }
        Entailment::Refuted(m) => {
            let w: BTreeMap<Atom, _> = m.iter().map(|(a, v)| (atom(a), v.clone())).collect();
            format!("refuted at {w:?}")
        }
        Entailment::NotProved(_) => "not proved".to_string(),
        Entailment::Refused(_) => "refused".to_string(),
    }
}

/// Each obligation that `part_bounds` reads through its shortest paths, which the tests above
/// name, at three links where a family has `k`.
fn path_search_cases() -> Vec<(String, String)> {
    let pair = |p: &str, g: &str| (p.to_string(), g.to_string());
    let links: [fn(usize) -> String; 4] = [
        |i| format!("b{i} + 2 * c{i} <= 3 && c{i} >= z{i}"),
        |i| format!("b{i} + 2 * c{i} <= 3 && c{i} >= z{i} && b{i} * c{i} >= -1000000"),
        |i| {
            format!(
                "b{i} + 2 * c{i} <= 3 && c{i} >= z{i} && b{i} * c{i} >= -1000000 \
                 && b{i} + c{i} >= z{i} - 100"
            )
        },
        |i| format!("x{i} - b{i} - c{i} >= 4 && c{i} >= 0 && b{i} * c{i} >= -1000000"),
    ];
    let k = 3;
    let mut cases = vec![
        product_chain_source(k, &[]),
        product_chain_source(k, &["z0 + z1 + x0 >= 0".to_string()]),
        product_chain_source(
            k,
            &(0..k)
                .map(|i| format!("2 * x{i} + y{i} >= z{i}"))
                .collect::<Vec<_>>(),
        ),
        product_chain_source(
            k,
            &(0..k)
                .map(|i| format!("abs(x{i} - y{i}) <= z{i} + 1"))
                .collect::<Vec<_>>(),
        ),
    ];
    cases.extend(links.iter().map(|&l| open_side_chain_source(k, l)));
    cases.extend([
        pair(
            "ok(a, b, c) = a + b >= 10 && a <= 3 && c >= 0;",
            "ok(a, b, c) = b * c >= 7 * c;",
        ),
        pair(
            "ok(a, b, c) = 2 * a == b + 4 && b >= 0 && c >= 0;",
            "ok(a, b, c) = a * c >= 2 * c;",
        ),
        pair(
            "ok(a, b, c, d) = a + b >= 10 && a <= 3 && d >= b + 1 && c >= 0;",
            "ok(a, b, c, d) = d * c >= 8 * c;",
        ),
        pair(
            "ok(a, c, d) = abs(a) <= d && d <= 1000 && c >= 0;",
            "ok(a, c, d) = d * c >= 0;",
        ),
        pair(
            "ok(a, b, c, d) = b >= 5 && a >= b && abs(a) <= d && d <= 1000 && c >= 0;",
            "ok(a, b, c, d) = d * c >= 5 * c;",
        ),
        pair(
            "ok(a, c, d) = abs(a) <= d && d <= 1000 && c >= 0;",
            "ok(a, c, d) = a * c >= -1000 * c;",
        ),
        pair(
            "ok(v, w1, w2, c) = v >= w1 && v >= w2 && w1 + w2 >= 10 && c >= 0;",
            "ok(v, w1, w2, c) = v * c >= 5 * c;",
        ),
        pair(
            "ok(v, w1, w2, c) = v >= w1 && v >= w2 && w1 + w2 >= 8 && c >= 0;",
            "ok(v, w1, w2, c) = v * c >= 5 * c;",
        ),
        pair(
            "ok(a, c) = (a >= 5 || a >= 7) && c >= 0;",
            "ok(a, c) = a * c >= 5 * c;",
        ),
        pair(
            "ok(a, b, c, d) = a + b >= 10 && b + 2 * c <= 3 && c >= 0 && d >= 0 \
             && b * c >= -1000;",
            "ok(a, b, c, d) = a * d >= 7 * d;",
        ),
        pair(
            "ok(a, b, d, e) = a >= e && e + b >= 10 && e - 2 * b >= 1 \
             && (b >= 0 || b <= -5) && d >= 0;",
            "ok(a, b, d, e) = a * d >= 7 * d;",
        ),
        pair(
            "ok(x0, x1, x2) = x0 >= 1 && x1 >= x0 + 1 && x2 >= x1 + 1;",
            "ok(x0, x1, x2) = x0 * x2 >= 3;",
        ),
    ]);
    cases
}

/// Obligations whose general row `w1 + w2 >= 10` reaches the two factors `u` and `v` through
/// difference rows (`w1 <= u`, `w2 <= u`, `w1 <= v`, `w2 <= v - 1`) at one slack where the
/// point meets them all the paths tie; they give the two different bounds `u >= 5` and
/// `v >= 6`. In the last two, `w1` and `w2` are in a disjunction, so they are kept and the
/// general row is read through the paths (`eliminate` in `part_bounds`); in the first two
/// they are eliminated first. Each goal needs one of the bounds, and the certificate shows
/// both, so a bound that went with the name of a factor would show in it.
const TIED: [(&str, &str); 4] = [
    (
        "ok(u, v, w1, w2, c) = u >= w1 && u >= w2 && v >= w1 && v >= w2 + 1 && w1 + w2 >= 10 \
         && v >= 0 && c >= 0;",
        "ok(u, v, w1, w2, c) = u * c >= 5 * c && v * c >= 0;",
    ),
    (
        "ok(u, v, w1, w2, c) = u >= w1 && u >= w2 && v >= w1 && v >= w2 + 1 && w1 + w2 >= 10 \
         && u >= 0 && c >= 0;",
        "ok(u, v, w1, w2, c) = v * c >= 6 * c && u * c >= 0;",
    ),
    (
        "ok(u, v, w1, w2, c) = u >= w1 && u >= w2 && v >= w1 && v >= w2 + 1 && w1 + w2 >= 10 \
         && v >= 0 && c >= 0 && (w1 >= -1000 || w2 <= -2000);",
        "ok(u, v, w1, w2, c) = u * c >= 5 * c && v * c >= 0;",
    ),
    (
        "ok(u, v, w1, w2, c) = u >= w1 && u >= w2 && v >= w1 && v >= w2 + 1 && w1 + w2 >= 10 \
         && u >= 0 && c >= 0 && (w1 >= -1000 || w2 <= -2000);",
        "ok(u, v, w1, w2, c) = v * c >= 6 * c && u * c >= 0;",
    ),
];

#[test]
fn the_bounds_found_do_not_depend_on_names() {
    // "the checker never lets a name change an answer": each obligation above whose bounds
    // `part_bounds` reads through shortest paths, renamed so that the order of its names is
    // reversed, and again so that it is rotated, gives the same verdict and, for a proof, the
    // same certificate up to the renaming, so the same bounds on each factor
    // (C2-chain-general). In the tied cases ([`TIED`]) the paths to `u` and `v` tie, and
    // choosing the factor that is first by name gave `u >= 5` alone as written and both bounds
    // with the names reversed; a node with two nearest factors now goes with neither, and the
    // sides left open are asked of the solver, which gives both under every naming.
    let tied = TIED.iter().map(|(p, g)| (p.to_string(), g.to_string()));
    let mut differ = Vec::new();
    for (premise, goal) in path_search_cases().into_iter().chain(tied) {
        let mut names = parameters(&premise);
        names.sort();
        let n = names.len();
        let first = up_to_names(&rung2(&premise, &goal), &BTreeMap::new());
        if TIED.iter().any(|(p, _)| *p == premise) {
            for bound in ["5 * c <= c * u", "6 * c <= c * v"] {
                assert!(first.contains(bound), "{premise}: {first}");
            }
        }
        let places: [fn(usize, usize) -> usize; 2] =
            [|r, n| n - 1 - r, |r, n| (r + n.div_ceil(2)) % n];
        for place in places {
            let to: BTreeMap<String, String> = (names.iter().enumerate())
                .map(|(r, a)| (a.clone(), format!("v{:03}", place(r, n))))
                .collect();
            let back: BTreeMap<Arc<str>, Arc<str>> = (to.iter())
                .map(|(a, b)| (Arc::from(b.as_str()), Arc::from(a.as_str())))
                .collect();
            let (p2, g2) = (renamed(&premise, &to), renamed(&goal, &to));
            let second = up_to_names(&rung2(&p2, &g2), &back);
            if second != first {
                differ.push(format!(
                    "{premise} to {goal}:\n  as written: {first}\n  as {p2}: {second}"
                ));
            }
        }
    }
    assert!(differ.is_empty(), "{}", differ.join("\n"));
}

/// `g{k}`, which calls `g{k-1}` twice, each time with the argument `b mod (b + 1)`, which fails
/// at `b = -1`, and so on down to `g0(a, b) = b >= 0`; and `ok(x, n) = g{k}(x, n)`. Not `f`,
/// since `f64` names a type.
fn nested_double_calls(k: usize) -> String {
    let mut src = String::from("g0(positional a, positional b) = b >= 0;\n");
    for i in 1..=k {
        let j = i - 1;
        src.push_str(&format!(
            "g{i}(positional a, positional b) = g{j}(b mod (b + 1), b) && g{j}(b mod (b + 1), b);\n"
        ));
    }
    src.push_str(&format!("ok(x, n) = g{k}(x, n);"));
    src
}

/// `t(a, b) = a mod (a mod (... (a mod b)))`, k remainders deep, whose condition holds k
/// divisors. Its parameters are not named as `ok`'s, which elaboration would rename.
fn deep_divisor(k: usize) -> String {
    let mut t = String::from("b");
    for _ in 0..k {
        t = format!("a mod ({t})");
    }
    format!("t(positional a, positional b) = {t};\n")
}

/// Over [`deep_divisor`]'s `t` of k divisors, k remainders by `t(x, n) + j` summed, each
/// operand's condition the k divisors and its own, met one by one.
fn met_divisors(k: usize) -> String {
    let sum: Vec<String> = (0..k).map(|j| format!("y mod (t(x, n) + {j})")).collect();
    format!("{}ok(x, y, n) = {} >= 0;", deep_divisor(k), sum.join(" + "))
}

/// Over [`deep_divisor`]'s `t` of k divisors, k `if`s whose arm reads the divisors its guard
/// reads.
fn guarded_arms(k: usize) -> String {
    let arms: Vec<String> = (0..k)
        .map(|j| format!("(if x mod t(x, n) >= {j} {{ y mod t(x, n) >= 0 }} else {{ true }})"))
        .collect();
    format!("{}ok(x, y, n) = {};", deep_divisor(k), arms.join(" && "))
}

/// The relation of `ok` in `src`.
fn ok_relation(src: &str) -> Relation {
    let (ps, g) = function(src);
    let mut rs = relations(&[&g], &ps, true).expect("in the domain");
    rs.pop().expect("one relation")
}

#[test]
fn calls_whose_arguments_may_fail_alike_share_one_translation() {
    // The two calls of `g{k-1}` in `g{k}` pass arguments made apart but alike, with the same
    // terms and the same conditions, so they share one translation ([`Walk::shared_call_key`]
    // in preimage.rs). The argument `b mod (b + 1)` fails at `b = -1`, but no callee reads
    // it, so `ok` is `n >= 0`.
    for k in [1, 2, 3] {
        let goal = nested_double_calls(k);
        assert!(true_on_window("ok(x, n) = n >= 0;", &goal), "{k}");
        assert!(!true_on_window("ok(x, n) = n >= -1;", &goal), "{k}");
        assert_proved("ok(x, n) = n >= 0;", &goal);
        let e = checked("ok(x, n) = n >= -1;", &goal);
        assert!(!matches!(e, Entailment::Proved(_)), "{k}: {e}");
    }
}

#[test]
fn the_conditions_of_shared_divisors_scale() {
    // k remainders whose divisors each read the k divisors of `t`, met one by one, and k
    // `if`s whose arm reads its guard's divisors: each meet and each test of the arm's
    // divisors against the guard's is a union of the sets of divisors, which share their
    // parts ([`Sets::union`] in divisors.rs), where a copy of the sets made each O(k), O(k²)
    // in all (28.0 times the bytes at 8k for the remainders, k = 128, measured 2026-11-08;
    // 10.2 now). And k functions each calling the one before twice with an argument that may
    // fail, translated once each, where reading each such call at its place read 2^k calls
    // (0.48 s at k = 12, 34 s at k = 18, measured 2026-11-08).
    let k = 128;
    // Each fails where `n = 0`; a verdict is checked against the interpreter (`checked`).
    for src in [met_divisors(2), guarded_arms(2)] {
        assert!(!true_on_window("ok(x, y, n) = true;", &src), "{src}");
        let e = checked("ok(x, y, n) = true;", &src);
        assert!(!matches!(e, Entailment::Proved(_)), "{src}: {e}");
    }
    let measure = move || {
        scaling::check_order("k remainders by terms over k shared divisors", k, 1, |k| {
            ok_relation(&met_divisors(k));
        });
        scaling::check_order("k guards over k shared divisors", k, 1, |k| {
            ok_relation(&guarded_arms(k));
        });
        scaling::check_order(
            "k nested pairs of calls with arguments that may fail",
            k,
            1,
            |k| {
                ok_relation(&nested_double_calls(k));
            },
        );
    };
    let thread = std::thread::Builder::new().stack_size(8 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

/// A sum of products `x{i} * y{i}` over a chain `z0 <= z1 <= ...` of `k` links, where each
/// link has `x{i} >= z{i}`, `y{i} >= z{i}`, `x{i} + b{i} >= 10` and the rows `link(i)`, which
/// bound `x{i}` below by 7 or more; the goal is that the sum is at least `Σ 7 * y{i}`.
fn open_side_chain(k: usize, link: fn(usize) -> String) -> (Relation, Relation) {
    let (premise, goal) = open_side_chain_source(k, link);
    let (ps, p) = function(&premise);
    let (_, g) = function(&goal);
    let mut rs = relations(&[&p, &g], &ps, true).expect("in the domain");
    let g = rs.pop().expect("two relations");
    (rs.pop().expect("two relations"), g)
}

/// The premise and the goal of [`open_side_chain`], as written.
fn open_side_chain_source(k: usize, link: fn(usize) -> String) -> (String, String) {
    let names: Vec<String> = (0..k)
        .map(|i| format!("x{i}, y{i}, z{i}, b{i}, c{i}"))
        .collect();
    let head = format!("ok({})", names.join(", "));
    let mut premise = vec!["z0 >= 0".to_string()];
    premise.extend((1..k).map(|i| format!("z{i} >= z{} + 1", i - 1)));
    premise.push(format!("z{} <= {}", k - 1, 2 * k));
    premise.extend((0..k).map(|i| {
        format!(
            "x{i} >= z{i} && y{i} >= z{i} && x{i} + b{i} >= 10 && {}",
            link(i)
        )
    }));
    let left: Vec<String> = (0..k).map(|i| format!("x{i} * y{i}")).collect();
    let right: Vec<String> = (0..k).map(|i| format!("7 * y{i}")).collect();
    (
        format!("{head} = {};", premise.join(" && ")),
        format!("{head} = {} >= {};", left.join(" + "), right.join(" + ")),
    )
}

/// The scaling test of [`open_side_chain`] with `link`: each goal is proved, and with
/// `no_side`, no side of a hull is asked of the solver.
fn open_side_chain_scales(what: &'static str, link: fn(usize) -> String, no_side: bool) {
    let n = 16;
    let built = scaling::inputs(n, |k| open_side_chain(k, link));
    let measure = move || {
        scaling::check(what, n, |k| {
            let (p, g) = &built[&k];
            presburger::hull_sides_asked();
            let e = entails(p, g);
            let asked = presburger::hull_sides_asked();
            assert!(matches!(e, Entailment::Proved(_)), "{k}: {e}");
            assert!(!no_side || asked == 0, "{k}: {asked} sides asked");
        });
    };
    scaling::on_a_thread(8 << 20, measure);
}

#[test]
fn products_whose_factor_bounds_pass_through_two_general_rows_scale() {
    // The bound `x{i} >= 7 + 2 * i` needs `x{i} + b{i} >= 10` and `b{i} + 2 * c{i} <= 3` at
    // once; `b{i}` and `c{i}` are not factors, so they are eliminated before the factors are
    // bounded (`shadow` in `part_bounds`), and no side of a hull is asked of the solver
    // (C2-chain-general).
    open_side_chain_scales(
        "a sum of products whose factor bounds pass through two general rows",
        |i| format!("b{i} + 2 * c{i} <= 3 && c{i} >= z{i}"),
        true,
    );
}

#[test]
fn products_whose_factor_bounds_pass_from_row_to_row_scale() {
    // As above, but `b{i}` and `c{i}` are factors (of `b{i} * c{i}`) and are kept: the bound
    // `b{i} <= 3 - 2 * i` from `b{i} + 2 * c{i} <= 3` is passed on to `x{i} + b{i} >= 10`
    // (`propagate` in `part_bounds`), and no side is asked (C2-chain-general).
    open_side_chain_scales(
        "a sum of products whose factor bounds pass from row to row",
        |i| format!("b{i} + 2 * c{i} <= 3 && c{i} >= z{i} && b{i} * c{i} >= -1000000"),
        true,
    );
}

#[test]
fn products_whose_factor_bounds_wait_on_each_other_scale() {
    // As above, with `b{i} + c{i} >= z{i} - 100`, so that the upper side of `b{i}` and the
    // lower side of `c{i}` each wait on the other through the rows; each is let go with the
    // bound it has (`propagate`), and no side is asked (C2-chain-general).
    open_side_chain_scales(
        "a sum of products whose factor bounds wait on each other",
        |i| {
            format!(
                "b{i} + 2 * c{i} <= 3 && c{i} >= z{i} && b{i} * c{i} >= -1000000 \
                 && b{i} + c{i} >= z{i} - 100"
            )
        },
        true,
    );
}

#[test]
fn products_whose_factors_keep_open_sides_scale() {
    // Complexity tradeoff of `products` (C2-chain-general): `x{i} >= 7` needs
    // `x{i} + b{i} >= 10`, `x{i} - b{i} - c{i} >= 4` and `c{i} >= 0` at once, with `b{i}` and
    // `c{i}` kept (they are factors of `b{i} * c{i}`), so no row bounds `x{i}` from the bounds
    // of the others and the goal is not proved from the bounds found. Each open side of a
    // factor is then asked of the solver over the rows of that factor's link alone (its
    // cluster, `clusters` in `part_bounds`), not over the whole chain, so the work stays
    // linear in the number of links.
    open_side_chain_scales(
        "a sum of products whose factors keep open sides",
        |i| format!("x{i} - b{i} - c{i} >= 4 && c{i} >= 0 && b{i} * c{i} >= -1000000"),
        false,
    );
}
