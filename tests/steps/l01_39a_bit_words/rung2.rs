//! Rung 2 on `bitAnd(a, b)` (plan row RUNG2-bit; DESIGN.md sec:verification, rung 2): an
//! auxiliary variable `x` bounded by one disjunct for each pair of signs of `a` and `b`, each
//! integer read as an infinite two's-complement word, so that every row holds at every sign,
//! not only at the `int[0..]` operands L1.39a admits: `0 <= x` where `a` or `b` is
//! nonnegative, `x <= a` where `a` is nonnegative or both are negative, and `x <= b` likewise.
//! The definition bounds `x` and does not fix it, so a point the solver finds is a
//! countermodel only where it still is with `x` set to `a & b`.

use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zed_tests::step_helpers::l01_25_preimage_catalog::function;
use zedc::store::int::Int;
use zedc::store::preimage::relations;
use zedc::store::presburger::{Atom, Entailment, Model, entails};

/// What rung 2 concludes from the body of `ok` in `premise` to the body of `ok` in `goal`,
/// over the same parameters, each read as an integer input. The two are translated in one
/// call, so that their auxiliary variables are numbered apart.
fn rung2(premise: &str, goal: &str) -> Entailment {
    let (ps, p) = function(premise);
    let (_, g) = function(goal);
    let rs = relations(&[&p, &g], &ps, true).expect("in the domain");
    entails(&rs[0], &rs[1])
}

/// The values of the parameters of `src` in the model `m`, each absent one zero.
fn point(src: &str, m: &Model) -> Vec<i64> {
    let (ps, _) = function(src);
    (ps.iter())
        .map(|n| {
            let v = m.get(&Atom::Sym(n.clone())).map_or(Some(0), Int::to_i128);
            v.and_then(|v| i64::try_from(v).ok())
                .expect("a model value within i64")
        })
        .collect()
}

/// The point of the countermodel `e` over the parameters of `src`.
fn countermodel(e: &Entailment, src: &str) -> Vec<i64> {
    match e {
        Entailment::Refuted(m) => point(src, m),
        e => panic!("not refuted: {e}"),
    }
}

#[test]
fn the_bounds_hold_at_x_equal_to_a_and_b_at_every_sign() {
    // Every pair of operands in -40..=40, each sign and zero, with the and of Rust's `i64`,
    // which reads a negative integer as two's complement as L1.39d does.
    let src = "ok(a, b, v) = bitAnd(a, b) == v;";
    let (ps, t) = function(src);
    let r = &relations(&[&t], &ps, true).expect("in the domain")[0];
    assert_eq!(r.bit_ands.len(), 1, "{r}");
    let x = Atom::Aux(r.bit_ands[0].0);
    for a in -40i64..=40 {
        for b in -40i64..=40 {
            let mut at: Model = (ps.iter().zip([a, b, a & b]))
                .map(|(n, v)| (Atom::Sym(n.clone()), Int::from(v)))
                .collect();
            at.insert(x.clone(), Int::from(a & b));
            assert!(r.defined().holds(&at), "bitAnd({a}, {b}) = {}: {r}", a & b);
            assert!(r.body.holds(&at), "bitAnd({a}, {b}) = {}: {r}", a & b);
        }
    }
}

#[test]
fn a_bit_and_of_nonnegative_operands_is_at_most_each() {
    let premise = "ok(i, n) = i >= 0 && n >= 0;";
    for goal in [
        "ok(i, n) = bitAnd(i, n) <= n;",
        "ok(i, n) = bitAnd(i, n) <= i;",
        "ok(i, n) = 0 <= bitAnd(i, n);",
        "ok(i, n) = 0 <= bitAnd(i, n) && bitAnd(i, n) <= n && bitAnd(i, n) <= i;",
    ] {
        let e = rung2(premise, goal);
        assert!(matches!(e, Entailment::Proved(_)), "{goal}: {e}");
    }
}

#[test]
fn a_bit_and_is_not_proved_below_an_operand() {
    // The negative control of an unsound relation: `bitAnd(n, n) = n`, so `bitAnd(i, n) < n`
    // fails at `i = n`, and at any `i` with every bit of `n` set. A countermodel the answer
    // gives is checked with the true and.
    let premise = "ok(i, n) = n >= 1;";
    let e = rung2(premise, "ok(i, n) = bitAnd(i, n) < n;");
    match &e {
        Entailment::Refuted(_) => {
            let [i, n] = countermodel(&e, premise)[..] else {
                panic!("two parameters")
            };
            assert!(n >= 1 && (i & n) >= n, "i = {i}, n = {n}");
        }
        Entailment::NotProved(_) => {}
        e => panic!("{e}"),
    }
    // Nor from nonnegative operands both.
    let e = rung2(
        "ok(i, n) = i >= 0 && n >= 1;",
        "ok(i, n) = bitAnd(i, n) < n;",
    );
    assert!(!matches!(e, Entailment::Proved(_)), "{e}");
}

#[test]
fn a_point_with_the_variable_not_the_and_is_no_countermodel() {
    // At `a = b = 3` the and is 3, but its bounds leave it anywhere in `0..=3`: the solver may
    // give it 0, and that point is no countermodel. Before the variable was set to the and,
    // it was reported as one.
    for goal in [
        "ok(a, b) = bitAnd(a, b) == 3;",
        "ok(a, b) = bitAnd(a, b) >= 3;",
        "ok(a, b) = bitAnd(a, b) == a;",
    ] {
        let e = rung2("ok(a, b) = a == 3 && b == 3;", goal);
        assert!(!matches!(e, Entailment::Refuted(_)), "{goal}: {e}");
    }
}

#[test]
fn a_goal_the_and_breaks_is_refuted_at_its_operands() {
    // `bitAnd(3, 5)` is 1.
    let premise = "ok(a, b) = a == 3 && b == 5;";
    for goal in [
        "ok(a, b) = bitAnd(a, b) == 3;",
        "ok(a, b) = bitAnd(a, b) == 0;",
        "ok(a, b) = bitAnd(a, b) != 1;",
    ] {
        let e = rung2(premise, goal);
        assert_eq!(countermodel(&e, premise), [3, 5], "{goal}");
    }
    let e = rung2(premise, "ok(a, b) = bitAnd(a, b) == 1;");
    assert!(!matches!(e, Entailment::Refuted(_)), "{e}");
}

#[test]
fn each_row_holds_only_at_its_signs() {
    // Both negative: the and is negative, at most each operand (`-4 & -3 = -4`).
    let e = rung2(
        "ok(a, b) = a <= -1 && b <= -1;",
        "ok(a, b) = bitAnd(a, b) <= -1 && bitAnd(a, b) <= a && bitAnd(a, b) <= b;",
    );
    assert!(matches!(e, Entailment::Proved(_)), "{e}");
    // One negative: the and is nonnegative and at most the nonnegative operand.
    let premise = "ok(a, b) = a <= -1 && b >= 0;";
    let e = rung2(
        premise,
        "ok(a, b) = 0 <= bitAnd(a, b) && bitAnd(a, b) <= b;",
    );
    assert!(matches!(e, Entailment::Proved(_)), "{e}");
    // ... and not at most the negative one: `bitAnd(-1, 5)` is 5.
    let e = rung2(premise, "ok(a, b) = bitAnd(a, b) <= a;");
    if let Entailment::Refuted(_) = e {
        let [a, b] = countermodel(&e, premise)[..] else {
            panic!("two parameters")
        };
        assert!(a <= -1 && b >= 0 && (a & b) > a, "a = {a}, b = {b}");
    } else {
        assert!(matches!(e, Entailment::NotProved(_)), "{e}");
    }
    // With no sign known, no bound is proved.
    for goal in [
        "ok(a, b) = 0 <= bitAnd(a, b);",
        "ok(a, b) = bitAnd(a, b) <= a;",
        "ok(a, b) = bitAnd(a, b) <= b;",
    ] {
        let e = rung2("ok(a, b) = true;", goal);
        assert!(!matches!(e, Entailment::Proved(_)), "{goal}: {e}");
    }
}

#[test]
fn an_and_of_terms_and_a_nested_and_are_bounded() {
    // Operands that are terms, and an and of an and: `bitAnd(bitAnd(i, j), n) <= n` and
    // `<= i`.
    let premise = "ok(i, j, n) = i >= 0 && j >= 0 && n >= 0;";
    for goal in [
        "ok(i, j, n) = bitAnd(bitAnd(i, j), n) <= n && bitAnd(bitAnd(i, j), n) <= i;",
        // Terms as operands, written under a test that shows the checker they are in
        // `int[0..]` (L1.39a): a mask `n - 1` keeps the and below `n`.
        "ok(i: int, j: int, n: int) = if i >= 0 && n >= 1 { bitAnd(i + 1, n - 1) <= i + 1 } else { true };",
        "ok(i: int, j: int, n: int) = if i >= 0 && n >= 1 { bitAnd(i, n - 1) < n } else { true };",
    ] {
        let e = rung2(premise, goal);
        assert!(matches!(e, Entailment::Proved(_)), "{goal}: {e}");
    }
    // The inner and set to its value moves the outer one's operand: at `i = 6, j = 3,
    // n = 7` the inner and is 2 and the outer 2, so `!= 2` is refuted there.
    let premise = "ok(i, j, n) = i == 6 && j == 3 && n == 7;";
    let e = rung2(premise, "ok(i, j, n) = bitAnd(bitAnd(i, j), n) != 2;");
    assert_eq!(countermodel(&e, premise), [6, 3, 7]);
}

#[test]
fn a_program_with_a_bit_and_in_a_test_is_checked_and_runs() {
    // Through `zedc run`: the checker's linear questions on `ok` now read `bitAnd`, and
    // deciding them rejects nothing (front.rs, `linear_questions`).
    let src = "ok(i, n) = bitAnd(i, n) <= n && bitAnd(i, n) != 2;\n\
               main(m: MainArgs) {\n  \
               a = int(m.stdin[0] else \"0\") else 0;\n  \
               held = if a >= 0 { ok(i: a, n: 6) } else { false };\n  \
               r = if held { \"in\" } else { \"out\" };\n  m.stdout <- \"${r}\";\n}\n";
    for (input, out) in [("5\n", "in\n"), ("3\n", "out\n"), ("-3\n", "out\n")] {
        let o = zed_tests::step_helpers::l01_19_whole_file_ports::run("bits", src, input, &[]);
        assert_eq!(
            (o.status, o.stdout.as_str(), o.stderr.as_str()),
            (0, out, ""),
            "{input}"
        );
    }
}

/// `bitAnd(x{i}, x{i+1}) <= x{i+1}` for `i < k`, joined by `&&`, over `k + 1` inputs.
pub(super) fn chain(k: usize) -> Term {
    let var = |i: usize| Term::Var(format!("x{i}").into());
    let prim = |p: Prim, args: Vec<Term>| Term::Prim(p, args);
    (0..k)
        .map(|i| {
            let and = prim(Prim::BitAnd, vec![var(i), var(i + 1)]);
            prim(Prim::Le, vec![and, var(i + 1)])
        })
        .reduce(|a, b| prim(Prim::And, vec![a, b]))
        .expect("one link or more")
}

/// `x{i} >= 0` for `i <= k`, joined by `&&`.
pub(super) fn signs(k: usize) -> Term {
    let var = |i: usize| Term::Var(format!("x{i}").into());
    let prim = |p: Prim, args: Vec<Term>| Term::Prim(p, args);
    (0..=k)
        .map(|i| prim(Prim::Ge, vec![var(i), Term::Lit(Value::Int(0))]))
        .reduce(|a, b| prim(Prim::And, vec![a, b]))
        .expect("one sign or more")
}

#[test]
fn a_short_chain_of_bit_ands_is_proved() {
    // The small instance of `bench::rung2`: one bit and a link, each translated once.
    for k in 1..=3 {
        let names: Vec<Arc<str>> = (0..=k).map(|i| Arc::from(format!("x{i}"))).collect();
        let (p, g) = (signs(k), chain(k));
        let rs = relations(&[&p, &g], &names, true).expect("in the domain");
        assert_eq!(rs[1].bit_ands.len(), k);
        let e = entails(&rs[0], &rs[1]);
        assert!(matches!(e, Entailment::Proved(_)), "k = {k}: {e}");
    }
}
