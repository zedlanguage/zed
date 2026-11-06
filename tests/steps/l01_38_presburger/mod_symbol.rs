//! Rung 2 on `x div n` and `x mod n` for a divisor `n` that is a symbol (RUNG2-mod-symbol;
//! DESIGN.md sec:domains, "Backward transfer, and `@ensure`", and sec:verification, rung 2):
//! the quotient `q` and remainder `r` are auxiliary variables with `x == n * q + r` and
//! `0 <= r <= |n| - 1`, `n * q` a product atom, one disjunct for each sign of `n` and none
//! for `n == 0`, where the operation fails. The index `i mod len` of a ring buffer is in
//! bounds when a premise gives `len >= 1`, and not from `len >= 0`.

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zed_tests::scaling;
use zedc::store::int::Int;
use zedc::store::preimage::relations;
use zedc::store::presburger::{Atom, Con, Entailment, Formula, Lin, Model, satisfiable};

use super::entailment::rung2;
use super::{holds, point, window};
use zed_tests::step_helpers::l01_25_preimage_catalog::function;

/// The countermodel of `e`, checked against the interpreter: the premise holds there and the
/// goal does not give `true`.
fn countermodel(e: &Entailment, premise: &str, goal: &str) -> Vec<i64> {
    let Entailment::Refuted(m) = e else {
        panic!("{premise} to {goal}: {e}")
    };
    let (ps, p) = function(premise);
    let (_, g) = function(goal);
    let at = point(m, &ps);
    assert!(holds(&p, &ps, &at) && !holds(&g, &ps, &at), "{at:?}");
    at
}

const POSITIVE: &str = "ok(x, n) = n >= 1;";
const IN_RANGE: &str = "ok(x, n) = 0 <= x mod n && x mod n < n;";
const SPLIT: &str = "ok(x, n) = x div n * n + x mod n == x;";

#[test]
fn a_remainder_by_a_positive_symbol_is_in_range() {
    let e = rung2(POSITIVE, IN_RANGE);
    assert!(matches!(e, Entailment::Proved(_)), "{e}");
}

#[test]
fn quotient_times_divisor_plus_remainder_is_the_dividend() {
    let e = rung2(POSITIVE, SPLIT);
    assert!(matches!(e, Entailment::Proved(_)), "{e}");
}

#[test]
fn from_a_divisor_that_may_be_zero_neither_is_proved() {
    // At `n = 0` both goals fail: `x mod 0` is no number. The relation leaves the quotient
    // and remainder free there, so neither is proved; where the point rung 2 finds gives the
    // product atom `n * q0` a value that is no product, it is not a countermodel, and the
    // answer is "not proved" (sec:verification, rung 2).
    let premise = "ok(x, n) = n >= 0;";
    for goal in [IN_RANGE, SPLIT] {
        match rung2(premise, goal) {
            e @ Entailment::Refuted(_) => assert_eq!(countermodel(&e, premise, goal)[1], 0),
            Entailment::NotProved(_) => {}
            e => panic!("{goal}: {e}"),
        }
    }
}

#[test]
fn a_remainder_by_a_negative_symbol_is_below_its_magnitude() {
    // Euclidean: `-7 mod -3` is 2, so `0 <= r <= -n - 1`.
    let e = rung2(
        "ok(x, n) = n <= -1;",
        "ok(x, n) = 0 <= x mod n && x mod n < -n && x div n * n + x mod n == x;",
    );
    assert!(matches!(e, Entailment::Proved(_)), "{e}");
    // A nonzero divisor of either sign bounds the remainder by its magnitude, not by itself.
    let premise = "ok(x, n) = n != 0;";
    let e = rung2(premise, "ok(x, n) = 0 <= x mod n && x mod n <= abs(n) - 1;");
    assert!(matches!(e, Entailment::Proved(_)), "{e}");
    let goal = "ok(x, n) = x mod n < n;";
    let at = countermodel(&rung2(premise, goal), premise, goal);
    assert!(at[1] < 0, "{at:?}");
}

#[test]
fn a_ring_buffer_index_is_in_bounds() {
    // `buf[(head + k) mod len]` over a buffer of `len >= 1` slots, the divisor a sum.
    let e = rung2(
        "ok(head, k, len) = len >= 1 && 0 <= head && 0 <= k;",
        "ok(head, k, len) = 0 <= (head + k) mod len && (head + k) mod len <= len - 1;",
    );
    assert!(matches!(e, Entailment::Proved(_)), "{e}");
    // A tile of width `w`: column and row of a flat index `i` put it back together.
    let e = rung2(
        "ok(i, w) = w >= 1 && i >= 0;",
        "ok(i, w) = (i div w) * w + i mod w == i && i mod w < w;",
    );
    assert!(matches!(e, Entailment::Proved(_)), "{e}");
    // Into a buffer of `len + 1` slots, the divisor a linear term with a constant.
    let e = rung2(
        "ok(i, len) = len >= 0;",
        "ok(i, len) = i mod (len + 1) <= len;",
    );
    assert!(matches!(e, Entailment::Proved(_)), "{e}");
}

#[test]
fn a_constant_divisor_is_translated_as_before() {
    // The definition of a constant divisor has no disjunction.
    let (ps, t) = function("ok(x) = x mod 3 == 1;");
    let r = &relations(&[&t], &ps, true).expect("in the domain")[0];
    assert_eq!(r.to_string(), "q1 == 1 where q0 = x div 3, q1 = x mod 3");
    let def = r.defined().to_string();
    assert!(!def.contains("||"), "{def}");
    // A divisor `0` is outside the domain, as before.
    let (ps, t) = function("ok(x) = x mod 0 == 1;");
    assert!(relations(&[&t], &ps, true).is_none());
}

#[test]
fn a_symbolic_divisor_is_read_by_rung_2_alone() {
    // The preimage's linear stage, which has no product atoms, keeps a symbolic divisor
    // outside the domain.
    let (ps, t) = function("ok(x, n) = x mod n == 1;");
    assert!(relations(&[&t], &ps, false).is_none());
    let r = &relations(&[&t], &ps, true).expect("in the domain")[0];
    assert_eq!(r.to_string(), "q1 == 1 where q0 = x div n, q1 = x mod n");
}

/// At each point of the window where the divisor is nonzero, the definitions hold at the
/// interpreter's quotient and remainder (auxiliary variables 0 and 1, their product atoms read
/// as products), and the body holds there exactly where the interpreter gives `true`; at each
/// point where it is zero, where the interpreter fails, the relation holds for some quotient
/// and remainder. `pair` gives the dividend and divisor at a point.
fn agrees(src: &str, pair: impl Fn(&[i64]) -> (i64, i64)) {
    let (ps, t) = function(src);
    let r = &relations(&[&t], &ps, true).expect("in the domain")[0];
    for p in window(ps.len(), -6, 6) {
        let (a, d) = pair(&p);
        let mut at: Model = (ps.iter().zip(&p))
            .map(|(n, v)| (Atom::Sym(n.clone()), Int::from(*v)))
            .collect();
        if d == 0 {
            let fixed = at.iter().map(|(x, v)| {
                Formula::Con(Con::eq(&Lin::atom(x.clone()), &Lin::constant(v.clone())))
            });
            let f = Formula::and(
                [r.defined(), r.body.clone()]
                    .into_iter()
                    .chain(fixed)
                    .collect(),
            );
            let sat = satisfiable(&f).unwrap_or_else(|e| panic!("{src} at {p:?}: refused: {e}"));
            assert!(sat.is_some(), "{src} at {p:?}: {r}");
            continue;
        }
        at.insert(Atom::Aux(0), Int::from(a.div_euclid(d)));
        at.insert(Atom::Aux(1), Int::from(a.rem_euclid(d)));
        assert!(r.defined().holds(&at), "{src} at {p:?}: {r}");
        assert_eq!(r.body.holds(&at), holds(&t, &ps, &p), "{src} at {p:?}: {r}");
    }
}

#[test]
fn the_translation_agrees_with_the_interpreter() {
    let xn = |p: &[i64]| (p[0], p[1]);
    agrees("ok(x, n, v) = x mod n == v;", xn);
    agrees("ok(x, n, v) = x div n == v;", xn);
    agrees(
        "ok(x, n, v) = x div n * n + x mod n == x && x mod n != v;",
        xn,
    );
    agrees("ok(x, n, v) = (x + v) mod (n - v) < 2;", |p| {
        (p[0] + p[2], p[1] - p[2])
    });
}

/// `x div (n + i) * (n + i) + x mod (n + i) == x` for `i < k`, joined by `&&`: `2k`
/// auxiliary variables, `x div (n + i)` and `x mod (n + i)` sharing a pair, and `k` product atoms `n * q`.
fn splits(k: usize) -> Term {
    let var = |s: &str| Term::Var(s.into());
    let prim = |p: Prim, args: Vec<Term>| Term::Prim(p, args);
    (0..k)
        .map(|i| {
            let i = i64::try_from(i).expect("a small count");
            let d = prim(Prim::Add, vec![var("n"), Term::Lit(Value::Int(i))]);
            let q = prim(Prim::IntDiv, vec![var("x"), d.clone()]);
            let r = prim(Prim::Mod, vec![var("x"), d.clone()]);
            let back = prim(Prim::Add, vec![prim(Prim::Mul, vec![q, d]), r]);
            prim(Prim::Eq, vec![back, var("x")])
        })
        .reduce(|a, b| prim(Prim::And, vec![a, b]))
        .expect("one split or more")
}

#[test]
fn translating_symbolic_divisors_scales() {
    let n = 256;
    let built: BTreeMap<usize, Term> = [n, n * scaling::FACTOR]
        .into_iter()
        .map(|k| (k, splits(k)))
        .collect();
    let inputs: [Arc<str>; 2] = ["x".into(), "n".into()];
    let measure = move || {
        scaling::check("splits by symbolic divisors translated", n, |k| {
            let rs = relations(&[&built[&k]], &inputs, true).expect("in the domain");
            assert_eq!(rs[0].defs.len(), 2 * k);
        });
    };
    let thread = std::thread::Builder::new().stack_size(8 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

#[test]
fn a_program_with_a_remainder_by_a_symbol_is_checked_and_runs() {
    // Through `zedc run`: the checker's linear questions on `ok` now read `i mod len`, and
    // deciding them rejects nothing (front.rs, `linear_questions`).
    let src = "ok(i, len) = len >= 1 && 0 <= i mod len && i mod len < len;\n\
               main(stdin: Lines) -> (stdout: Lines) {\n  \
               a = int(stdin[1] else \"0\") else 0;\n  \
               held = ok(i: a, len: a - 2) else false;\n  \
               r = if held { \"in\" } else { \"out\" };\n  stdout <- \"${r}\";\n}\n";
    for (input, out) in [("7\n", "in\n"), ("-3\n", "out\n")] {
        let o = zed_tests::step_helpers::l01_19_whole_file_ports::run("ring", src, input, &[]);
        assert_eq!(
            (o.status, o.stdout.as_str(), o.stderr.as_str()),
            (0, out, ""),
            "{input}"
        );
    }
}

#[test]
fn remainders_by_two_distinct_divisors_are_not_confused() {
    // `x mod n` and `x mod m` are distinct auxiliary variables: at `x = 5, n = 2, m = 3` the
    // first is 1 and the second 2.
    let e = rung2(
        "ok(x, n, m) = n >= 2 && m >= 2 && x mod n == 1;",
        "ok(x, n, m) = x mod m <= 1;",
    );
    assert!(!matches!(e, Entailment::Proved(_)), "{e}");
    // With a constant divisor on one side.
    let e = rung2(
        "ok(x, n) = n >= 2 && x mod 2 == 1;",
        "ok(x, n) = x mod n <= 1;",
    );
    assert!(!matches!(e, Entailment::Proved(_)), "{e}");
}

#[test]
#[should_panic(expected = "numbered apart")]
fn relations_translated_in_two_calls_are_refused_by_entails() {
    // Two calls of `relations` both number their auxiliary variables from 0, so `x mod 2` of
    // the premise and `x mod 4` of the goal would be one variable and `x mod 4 <= 1` would
    // follow from `x mod 2 == 1`. `entails` stops on such a pair rather than answer.
    let (ps, p) = function("ok(x) = x mod 2 == 1;");
    let (_, g) = function("ok(x) = x mod 4 <= 1;");
    let p = relations(&[&p], &ps, true).expect("in the domain");
    let g = relations(&[&g], &ps, true).expect("in the domain");
    let _ = zedc::store::presburger::entails(&p[0], &g[0]);
}
