//! `Scope` on disjunctions of difference tests (S4, META4 results 2 and 3), against answers
//! worked out by hand or by enumeration. Each family runs as one conjunction, one test at a
//! time in the order written, and one test at a time in the reverse order; the answer must be
//! the same in all three.
//!
//! Where class K3 (META4 result 3) refuses a system, the answer the tests accept is a refusal
//! (a warning on the scope) that keeps every value of the exact answer; where it accepts, the
//! answer is the exact one with no warning.

use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zed_tests::scaling;
use zedc::store::cell::Premises;
use zedc::store::product::Scope;

use crate::ints;
use crate::nests::{and, boxed, diff_ge, int, names, or, prim, var};

/// How the relation's tests reach the scope.
#[derive(Clone, Copy, Debug)]
enum How {
    AtOnce,
    Forward,
    Backward,
}

const HOWS: [How; 3] = [How::AtOnce, How::Forward, How::Backward];

/// A scope and the tests of a relation, assumed after it.
struct Sys {
    start: Scope,
    rel: Vec<Term>,
}

impl Sys {
    /// The scope of `ns`, each in `lo..=hi`, then `extra` (if any).
    fn new(ns: &[String], lo: i64, hi: i64, extra: Vec<Term>, rel: Vec<Term>) -> Sys {
        let refs: Vec<&str> = ns.iter().map(String::as_str).collect();
        let start = within(&refs, lo, hi).into_iter().chain(extra).reduce(and);
        let s = ints(&names(&refs));
        let start = match start {
            Some(t) => s.assume(&t, true, &Premises::new()),
            None => s,
        };
        Sys { start, rel }
    }

    fn narrowed(&self, how: How) -> Scope {
        let p = Premises::new();
        match how {
            How::AtOnce => match self.rel.iter().cloned().reduce(and) {
                Some(all) => self.start.assume(&all, true, &p),
                None => self.start.clone(),
            },
            How::Forward => self
                .rel
                .iter()
                .fold(self.start.clone(), |s, t| s.assume(t, true, &p)),
            How::Backward => self
                .rel
                .iter()
                .rev()
                .fold(self.start.clone(), |s, t| s.assume(t, true, &p)),
        }
    }
}

/// `lo <= n <= hi` for each of `ns`.
fn within(ns: &[&str], lo: i64, hi: i64) -> Vec<Term> {
    ns.iter()
        .flat_map(|n| {
            [
                prim(Prim::Ge, var(n), int(lo)),
                prim(Prim::Le, var(n), int(hi)),
            ]
        })
        .collect()
}

/// The values of `n` in `s`, within `lo..=hi`.
fn kept(s: &Scope, n: &str, lo: i64, hi: i64) -> Vec<i64> {
    let p = s.get(n);
    (lo..=hi).filter(|v| p.contains(&Value::Int(*v))).collect()
}

/// Asserts that `sys` keeps exactly `want` of each `(name, lo, hi, want)` with no warning, in
/// each of [`HOWS`].
fn exact(what: &str, sys: &Sys, want: &[(&str, i64, i64, Vec<i64>)]) {
    for how in HOWS {
        let s = sys.narrowed(how);
        for (n, lo, hi, w) in want {
            assert_eq!(&kept(&s, n, *lo, *hi), w, "{what}, {how:?}: {n} in {s}");
        }
        assert!(
            s.warnings().is_empty(),
            "{what}, {how:?}: {:?}",
            s.warnings()
        );
    }
}

/// What a system gives: the exact answer with no warning, or a refusal that keeps every value
/// of the exact answer.
#[derive(Debug, PartialEq)]
enum Answer {
    Exact,
    Refused,
}

/// The answer of `s`, after asserting it is one of the two [`Answer`]s.
fn answer(what: &str, s: &Scope, want: &[(&str, i64, i64, Vec<i64>)]) -> Answer {
    if s.warnings().is_empty() {
        for (n, lo, hi, w) in want {
            assert_eq!(&kept(s, n, *lo, *hi), w, "{what}: {n} in {s}");
        }
        Answer::Exact
    } else {
        for (n, lo, hi, w) in want {
            let k = kept(s, n, *lo, *hi);
            assert!(
                w.iter().all(|v| k.contains(v)),
                "{what}: refused but unsound, {n} in {s}"
            );
        }
        Answer::Refused
    }
}

/// Asserts that every run of `runs` gives the same [`Answer`].
fn same_answer(what: &str, runs: Vec<(String, Scope)>, want: &[(&str, i64, i64, Vec<i64>)]) {
    let answers: Vec<(String, Answer)> = runs
        .into_iter()
        .map(|(how, s)| {
            let a = answer(&format!("{what}, {how}"), &s, want);
            (how, a)
        })
        .collect();
    for (how, a) in &answers {
        assert_eq!(a, &answers[0].1, "{what}: {how} against {}", answers[0].0);
    }
}

/// `0..=m`.
fn upto(m: i64) -> Vec<i64> {
    (0..=m).collect()
}

/// The orchestrator's round-3 meta-review (`xst_verify.rs`, `fan_in`): `y` is fed by `k`
/// chains of difference tests, chain `c` of length `c` from a head `h{c}_0 <= 100 - 5c`, then
/// `x <= y`, all names in `0..=100`. With `or`, also `z - x >= 0 || z <= 5`. No cycle: the
/// exact answer is `x` in `0..=100 - 5k`.
fn fan_in(k: usize, with_or: bool) -> Sys {
    let mut all: Vec<String> = vec!["x".into(), "y".into(), "z".into()];
    let mut heads = Vec::new();
    let mut rel = Vec::new();
    for c in 1..=k {
        let head = format!("h{c}_0");
        heads.push(prim(Prim::Le, var(&head), int(100 - 5 * c as i64)));
        let mut prev = head.clone();
        all.push(head);
        for d in 1..c {
            let n = format!("h{c}_{d}");
            rel.push(diff_ge(&prev, &n, 0));
            all.push(n.clone());
            prev = n;
        }
        rel.push(diff_ge(&prev, "y", 0));
    }
    rel.push(diff_ge("y", "x", 0));
    if with_or {
        rel.push(or(diff_ge("z", "x", 0), prim(Prim::Le, var("z"), int(5))));
    }
    Sys::new(&all, 0, 100, heads, rel)
}

#[test]
fn fan_in_chains_give_the_exact_bound() {
    for k in [1usize, 2, 3, 4, 6, 8] {
        for with_or in [false, true] {
            exact(
                &format!("fan_in k = {k}, or = {with_or}"),
                &fan_in(k, with_or),
                &[("x", 0, 100, upto(100 - 5 * k as i64))],
            );
        }
    }
}

/// `fan_in_or` (variant 2 of `xst_verify.rs`): every link `a >= b` is written as
/// `a - b >= 0 || b <= 2`, and each chain of length `c` has `c` links, the last to `y`.
/// Exact: `x` in `0..=100 - 5k`.
fn fan_in_or(k: usize) -> Sys {
    let link = |a: &str, b: &str| or(diff_ge(a, b, 0), prim(Prim::Le, var(b), int(2)));
    let mut all: Vec<String> = vec!["x".into(), "y".into()];
    let mut heads = Vec::new();
    let mut rel = Vec::new();
    for c in 1..=k {
        let head = format!("h{c}_0");
        heads.push(prim(Prim::Le, var(&head), int(100 - 5 * c as i64)));
        let mut prev = head.clone();
        all.push(head);
        for d in 1..=c {
            let n = if d == c {
                "y".to_string()
            } else {
                format!("h{c}_{d}")
            };
            rel.push(link(&prev, &n));
            if d != c {
                all.push(n.clone());
            }
            prev = n;
        }
    }
    rel.push(link("y", "x"));
    Sys::new(&all, 0, 100, heads, rel)
}

#[test]
fn fan_in_chains_of_disjunctions_give_the_exact_bound() {
    for k in [1usize, 2, 3, 4, 6, 8, 12] {
        exact(
            &format!("fan_in_or k = {k}"),
            &fan_in_or(k),
            &[("x", 0, 100, upto(100 - 5 * k as i64))],
        );
    }
}

/// `diamond` of `xst_verify.rs`: one biconnected block of chains `c = 1..=k` from root `r` to
/// `y`, chain `c` of length `c`, its first link `r - a >= 5c || a <= 2`, the rest
/// `a - b >= 0 || b <= 2`, then `y - x >= 0 || x <= 2`. Bounds flow from `r` to `x` only.
/// Exact: `x` in `0..=100 - 5k`. `prefix` renames the chain names, which changes their order.
fn diamond(k: usize, prefix: &str) -> Sys {
    let lk = |a: &str, b: &str, off: i64| or(diff_ge(a, b, off), prim(Prim::Le, var(b), int(2)));
    let mut all: Vec<String> = vec!["r".into(), "x".into(), "y".into()];
    let mut rel = Vec::new();
    for c in 1..=k {
        let mut prev = "r".to_string();
        for d in 1..=c {
            let n = if d == c {
                "y".to_string()
            } else {
                format!("{prefix}{c}_{d}")
            };
            rel.push(lk(&prev, &n, if d == 1 { 5 * c as i64 } else { 0 }));
            if d != c {
                all.push(n.clone());
            }
            prev = n;
        }
    }
    rel.push(lk("y", "x", 0));
    Sys::new(&all, 0, 100, vec![], rel)
}

#[test]
fn a_diamond_of_disjunctions_gives_the_exact_bound() {
    for prefix in ["a", "z"] {
        for k in [1usize, 2, 3, 4, 6, 8] {
            exact(
                &format!("diamond prefix {prefix}, k = {k}"),
                &diamond(k, prefix),
                &[("x", 0, 100, upto(100 - 5 * k as i64))],
            );
        }
    }
}

/// `diamond_rev` of `xst_verify.rs`: `diamond` with names that sort the parts sink first
/// (`x` is `a0`, `y` is `a1`, the root `z`, chain names `b{c}_{20-d}`), plus
/// `z - a0 >= 0 || a0 <= 2`. Exact: `a0` in `0..=100 - 5k`. At `k` from 5 to 8 this refutes
/// a move limit as a refusal rule (META3, G8); Gemini's round-4 test asserts the bound with no
/// warning at `k = 8`.
fn diamond_rev(k: usize) -> Sys {
    let lk = |a: &str, b: &str, off: i64| or(diff_ge(a, b, off), prim(Prim::Le, var(b), int(2)));
    let mut all: Vec<String> = vec!["z".into(), "a0".into(), "a1".into()];
    let mut rel = Vec::new();
    for c in 1..=k {
        let mut prev = "z".to_string();
        for d in 1..=c {
            let n = if d == c {
                "a1".to_string()
            } else {
                format!("b{c:02}_{:02}", 20 - d)
            };
            rel.push(lk(&prev, &n, if d == 1 { 5 * c as i64 } else { 0 }));
            if d != c {
                all.push(n.clone());
            }
            prev = n;
        }
    }
    rel.push(lk("a1", "a0", 0));
    rel.push(lk("z", "a0", 0));
    Sys::new(&all, 0, 100, vec![], rel)
}

#[test]
fn a_diamond_with_its_parts_sorted_sink_first_gives_the_exact_bound() {
    for k in [1usize, 2, 3, 4, 5, 6, 8] {
        exact(
            &format!("diamond_rev k = {k}"),
            &diamond_rev(k),
            &[("a0", 0, 100, upto(100 - 5 * k as i64))],
        );
    }
}

/// Gemini round 4 (`nests.rs`): `x - y >= 1 || x >= 0` and `y - x >= 1 || y >= 0` with `x`, `y`
/// in `-10..=10`. If `x < 0`, the first gives `y < x`, and then the second needs `y >= 0`, which
/// fails: the exact answer is `x`, `y` in `0..=10`. The greatest fixpoint reaches it only by
/// narrowing the two parts in turn once for each value, so class K3 refuses it.
#[test]
fn a_cycle_of_two_disjunctions_is_exact_or_refused_in_every_order() {
    let p = Premises::new();
    let s = boxed(&["x", "y"], 10);
    let c1 = or(diff_ge("x", "y", 1), prim(Prim::Ge, var("x"), int(0)));
    let c2 = or(diff_ge("y", "x", 1), prim(Prim::Ge, var("y"), int(0)));
    let want = [("x", -10, 10, upto(10)), ("y", -10, 10, upto(10))];
    same_answer(
        "ping-pong",
        vec![
            (
                "one conjunction".into(),
                s.assume(&and(c1.clone(), c2.clone()), true, &p),
            ),
            (
                "c1 then c2".into(),
                s.assume(&c1, true, &p).assume(&c2, true, &p),
            ),
            (
                "c2 then c1".into(),
                s.assume(&c2, true, &p).assume(&c1, true, &p),
            ),
        ],
        &want,
    );
}

/// Every point of the box `lo..=hi` of each name that meets `ok`, projected on each name.
fn enumerate(lo: &[i64], hi: &[i64], ok: impl Fn(&[i64]) -> bool) -> Vec<Vec<i64>> {
    let n = lo.len();
    let mut out = vec![std::collections::BTreeSet::new(); n];
    let mut x = lo.to_vec();
    loop {
        if ok(&x) {
            for (o, v) in out.iter_mut().zip(&x) {
                o.insert(*v);
            }
        }
        let mut i = 0;
        while i < n && x[i] == hi[i] {
            x[i] = lo[i];
            i += 1;
        }
        if i == n {
            break;
        }
        x[i] += 1;
    }
    out.into_iter().map(|s| s.into_iter().collect()).collect()
}

/// Runs the base and the two parts of a class K counterexample in both part orders, one at a
/// time and as one conjunction, and asserts the same [`Answer`] in each.
fn both_part_orders(
    what: &str,
    ns: &[&str],
    lo: &[i64],
    hi: &[i64],
    [base, a, b]: [Term; 3],
    want: Vec<Vec<i64>>,
) {
    let p = Premises::new();
    let bx = ns
        .iter()
        .zip(lo.iter().zip(hi))
        .map(|(n, (l, h))| {
            and(
                prim(Prim::Ge, var(n), int(*l)),
                prim(Prim::Le, var(n), int(*h)),
            )
        })
        .reduce(and)
        .expect("one name");
    let s = ints(&names(ns)).assume(&and(bx, base), true, &p);
    let want: Vec<(&str, i64, i64, Vec<i64>)> = ns
        .iter()
        .zip(lo.iter().zip(hi))
        .zip(want)
        .map(|((n, (l, h)), w)| (*n, *l, *h, w))
        .collect();
    same_answer(
        what,
        vec![
            (
                "A then B".into(),
                s.assume(&a, true, &p).assume(&b, true, &p),
            ),
            (
                "B then A".into(),
                s.assume(&b, true, &p).assume(&a, true, &p),
            ),
            (
                "A and B".into(),
                s.assume(&and(a.clone(), b.clone()), true, &p),
            ),
            ("B and A".into(), s.assume(&and(b, a), true, &p)),
        ],
        &want,
    );
}

/// Codex round 4 (`k-order.rs`): class K is not independent of the order of the parts. Names
/// `x0..x4` in `[0, 10]`, `[0, 10]`, `[5, 5]`, `[0, 5]`, `[0, 5]`; base `x1 - x0 <= -1`;
/// parts `A = x0 - x1 <= 0 || x0 - x2 <= 0` and `B = x1 - x3 <= 0 || x1 - x4 <= 0`. Class K's
/// evaluator refuses with `A` first and gives boxes with `B` first; K3 refuses in both orders.
/// By enumeration, `x0` is in `1..=5` and `x1` in `0..=4`.
#[test]
fn codex_class_k_counterexample_gives_one_answer_in_both_part_orders() {
    let ns = ["x0", "x1", "x2", "x3", "x4"];
    let (lo, hi) = ([0, 0, 5, 0, 0], [10, 10, 5, 5, 5]);
    let le0 = |a: &str, b: &str| prim(Prim::Le, prim(Prim::Sub, var(a), var(b)), int(0));
    let want = enumerate(&lo, &hi, |x| {
        x[1] - x[0] <= -1 && (x[0] <= x[1] || x[0] <= x[2]) && (x[1] <= x[3] || x[1] <= x[4])
    });
    assert_eq!(want[0], (1..=5).collect::<Vec<_>>(), "Codex's enumeration");
    assert_eq!(want[1], (0..=4).collect::<Vec<_>>(), "Codex's enumeration");
    both_part_orders(
        "Codex's K counterexample",
        &ns,
        &lo,
        &hi,
        [
            prim(Prim::Le, prim(Prim::Sub, var("x1"), var("x0")), int(-1)),
            or(le0("x0", "x1"), le0("x0", "x2")),
            or(le0("x1", "x3"), le0("x1", "x4")),
        ],
        want,
    );
}

/// Gemini round 4: `z = 0`, `x`, `y` in `0..=10`, base `x - y <= 0`, parts
/// `A = y - x <= -1 || y <= 5` and `B = y - z <= 5 || y - z <= 4`. Class K's evaluator refuses
/// with `A` first and gives boxes with `B` first (the orchestrator's gord.rs); K3 refuses both.
/// Exact: `x`, `y` in `0..=5`.
#[test]
fn gemini_class_k_counterexample_gives_one_answer_in_both_part_orders() {
    let ns = ["x", "y", "z"];
    let (lo, hi) = ([0, 0, 0], [10, 10, 0]);
    let want = enumerate(&lo, &hi, |v| {
        v[0] - v[1] <= 0
            && (v[1] - v[0] <= -1 || v[1] <= 5)
            && (v[1] - v[2] <= 5 || v[1] - v[2] <= 4)
    });
    assert_eq!(want, [upto(5), upto(5), vec![0]], "the enumeration");
    let dle = |a: &str, b: &str, c: i64| prim(Prim::Le, prim(Prim::Sub, var(a), var(b)), int(c));
    both_part_orders(
        "Gemini's K counterexample",
        &ns,
        &lo,
        &hi,
        [
            dle("x", "y", 0),
            or(dle("y", "x", -1), prim(Prim::Le, var("y"), int(5))),
            or(dle("y", "z", 5), dle("y", "z", 4)),
        ],
        want,
    );
}

/// Codex round 4 (`engine-boundary.rs`): `x`, `y` in `0..=1`, `x + y <= s`, `x + y >= s`,
/// `x - y <= 0`, `x - y >= 0`. At `s = 1` no point meets them (Claude's model engine kept a
/// box); at `s = 0` the one point is `(0, 0)`.
#[test]
fn an_equality_on_a_sum_and_on_a_difference_meet_exactly() {
    let sum = || prim(Prim::Add, var("x"), var("y"));
    let dif = || prim(Prim::Sub, var("x"), var("y"));
    for s in [0, 1] {
        let rel = vec![
            prim(Prim::Le, sum(), int(s)),
            prim(Prim::Ge, sum(), int(s)),
            prim(Prim::Le, dif(), int(0)),
            prim(Prim::Ge, dif(), int(0)),
        ];
        let sys = Sys::new(&["x".into(), "y".into()], 0, 1, vec![], rel);
        for how in HOWS {
            let got = sys.narrowed(how);
            if s == 1 {
                assert!(got.bottom, "s = 1, {how:?}: {got}");
            } else {
                assert!(!got.bottom, "s = 0, {how:?}");
                assert_eq!(kept(&got, "x", 0, 1), [0], "{how:?}: {got}");
                assert_eq!(kept(&got, "y", 0, 1), [0], "{how:?}: {got}");
            }
        }
    }
}

/// Codex round 4 (`R4_REGRESSIONS.patch`, `cycle_edge_control`): `x >= y >= z`, `z <= 10`
/// leaves `x` unbounded above; with `z >= x` the three are equal and `x <= 10`.
#[test]
fn a_closing_edge_bounds_a_path() {
    let p = Premises::new();
    let init = ints(&names(&["x", "y", "z"]));
    let path = and(diff_ge("x", "y", 0), diff_ge("y", "z", 0));
    let bound = prim(Prim::Le, var("z"), int(10));
    let open = init
        .clone()
        .assume(&and(path.clone(), bound.clone()), true, &p);
    let closed = init.assume(&and(and(path, diff_ge("z", "x", 0)), bound), true, &p);
    assert!(open.get("x").contains(&Value::Int(11)), "{open}");
    assert!(!closed.get("x").contains(&Value::Int(11)), "{closed}");
    assert!(closed.get("x").contains(&Value::Int(10)), "{closed}");
}

/// Codex round 4 (`cyclic_base_measure`): the cycle `x_i >= x_{(i+1) mod n}` with `x0 <= 10`
/// holds the `n` names equal, so each is at most 10 and may be 10. As one conjunction, at
/// `n = 16` and `8n`, in near linear time (Codex measured 8.31 times for 8 times).
fn cyclic_base(n: usize) -> (Vec<Arc<str>>, Term) {
    let ls: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let refs: Vec<&str> = ls.iter().map(String::as_str).collect();
    let all = (0..n)
        .map(|i| diff_ge(&ls[i], &ls[(i + 1) % n], 0))
        .chain(std::iter::once(prim(Prim::Le, var("x0"), int(10))))
        .reduce(and)
        .expect("one test");
    (names(&refs), all)
}

#[test]
fn a_cycle_of_differences_with_one_bound_is_exact_in_near_linear_time() {
    let p = Premises::new();
    for n in [16, 128] {
        let (ns, all) = cyclic_base(n);
        let s = ints(&ns).assume(&all, true, &p);
        for x in &ns {
            assert!(s.get(x).contains(&Value::Int(10)), "n = {n}: {x}");
            assert!(!s.get(x).contains(&Value::Int(11)), "n = {n}: {x}");
        }
    }
    let inputs = scaling::inputs(16, cyclic_base);
    scaling::check_order(
        "a cyclic base of n differences, one conjunction",
        16,
        1,
        |m| {
            let (ns, all) = &inputs[&m];
            drop(ints(ns).assume(all, true, &Premises::new()));
        },
    );
}

/// Claude round 4 (`probe_r4.rs`, B(S)): the chain `x_{i+1} - x_i >= 1` over `n` names in
/// `0..=4n`, closed by `x0 - x_{n-1} >= c` when `c` is given. With `c = 1 - n` the cycle has
/// weight 0, each name is `x0 + i`, and `x_i` is in `i..=3n + 1 + i`; the open chain has the
/// same projection; with `c = 2 - n` the cycle is positive and the scope is empty. Each bound
/// moves on each test, so main's base closure is quadratic one test at a time (META4 O5).
fn chain(n: usize, close: Option<i64>) -> Sys {
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let mut rel: Vec<Term> = (0..n - 1).map(|i| diff_ge(&xs[i + 1], &xs[i], 1)).collect();
    if let Some(c) = close {
        rel.push(diff_ge("x0", &xs[n - 1], c));
    }
    Sys::new(&xs, 0, 4 * n as i64, vec![], rel)
}

/// Asserts the answers of [`chain`] closed by `close` in each of [`HOWS`] at 8 and 64 names,
/// then near linear time in each: in the reverse order the closing test comes first and each
/// link then moves the ends of a closed path (ST-walk-orders: on main 36 to 61 at 8n).
fn chain_answers(what: &str, close: impl Fn(usize) -> Option<i64> + Sync, empty: bool) {
    for n in [8, 64] {
        let sys = chain(n, close(n));
        for how in HOWS {
            let s = sys.narrowed(how);
            assert_eq!(s.bottom, empty, "{what}, n = {n}, {how:?}: {s}");
            if !empty {
                for i in 0..n {
                    let hi = 4 * n as i64;
                    let want: Vec<i64> = (i as i64..=3 * n as i64 + 1 + i as i64).collect();
                    assert_eq!(
                        kept(&s, &format!("x{i}"), 0, hi),
                        want,
                        "{what}, n = {n}, {how:?}: x{i}"
                    );
                }
            }
        }
    }
    for how in HOWS {
        let inputs = scaling::inputs(8, |n| chain(n, close(n)));
        scaling::check_order(&format!("{what}, {how:?}, n names"), 8, 1, |m| {
            drop(inputs[&m].narrowed(how));
        });
    }
}

#[test]
fn a_cycle_of_weight_zero_fixes_each_name_in_near_linear_time() {
    chain_answers("cycle of weight 0", |n| Some(1 - n as i64), false);
}

#[test]
fn a_cycle_of_weight_one_is_empty_in_near_linear_time() {
    chain_answers("cycle of weight 1", |n| Some(2 - n as i64), true);
}

/// CONTROL of the two above (Claude's open chain): no closing test.
#[test]
fn an_open_chain_narrows_in_near_linear_time() {
    chain_answers("open chain", |_| None, false);
}

/// Claude round 3 (`probe_r3.rs`, walk): `v_i` in `0..=3`, `w` in `0..=1`,
/// `v_i + w <= 0 || v_{i+1} - w >= 1` for `i < n - 1`, and `v0 - w >= 1`. The last test makes
/// `v0 >= 1`, so `v0 + w <= 0` fails and `v1 >= 1`, and so on down the walk: exact `v_i` in
/// `1..=3`, `w` in `0..=1`. Without the last test (the CONTROL) nothing narrows.
fn walk(n: usize, start: bool) -> Sys {
    let vs: Vec<String> = (0..n).map(|i| format!("v{i}")).collect();
    let mut rel: Vec<Term> = (0..n - 1)
        .map(|i| {
            or(
                prim(Prim::Le, prim(Prim::Add, var(&vs[i]), var("w")), int(0)),
                diff_ge(&vs[i + 1], "w", 1),
            )
        })
        .collect();
    if start {
        rel.push(diff_ge("v0", "w", 1));
    }
    let mut all = vs;
    all.push("w".into());
    Sys::new(&all, 0, 3, vec![prim(Prim::Le, var("w"), int(1))], rel)
}

/// Asserts `want` of each name at sizes `n` and `8n`, then near linear time one test at a
/// time.
fn family(
    what: &str,
    n: usize,
    make: impl Fn(usize) -> Sys + Sync,
    want: impl Fn(usize) -> Vec<(String, i64, i64, Vec<i64>)>,
) {
    for m in [n, 8 * n] {
        let sys = make(m);
        let w = want(m);
        let w: Vec<(&str, i64, i64, Vec<i64>)> = w
            .iter()
            .map(|(a, l, h, v)| (a.as_str(), *l, *h, v.clone()))
            .collect();
        same_answer(
            &format!("{what}, n = {m}"),
            HOWS.iter()
                .map(|h| (format!("{h:?}"), sys.narrowed(*h)))
                .collect(),
            &w,
        );
    }
    let inputs = scaling::inputs(n, make);
    scaling::check_order(&format!("{what}, one at a time"), n, 1, |m| {
        drop(inputs[&m].narrowed(How::Forward));
    });
}

/// A walk whose start forces each `v` to at least `1 + w` and whose end asks `v5 + w <= 0`
/// leaves no point. Its block is solved as a whole (`threshold::solve` answers that it is
/// empty), which empties only the block's first name; the scope must then keep no value of any
/// name, `u` too, which no test names, and must stay empty under a later test. With the step
/// that turns an empty name into an empty scope (`Scope::reduce_with`) removed, this test fails
/// on `u`.
#[test]
fn a_walk_that_leaves_no_point_empties_every_name() {
    let mut sys = walk(6, true);
    sys.rel
        .push(prim(Prim::Le, prim(Prim::Add, var("v5"), var("w")), int(0)));
    let mut all: Vec<String> = (0..6).map(|i| format!("v{i}")).collect();
    all.extend(["w".into(), "u".into()]);
    let sys = Sys::new(&all, 0, 3, vec![prim(Prim::Le, var("w"), int(1))], sys.rel);
    let later = prim(Prim::Ge, var("u"), int(2));
    for how in HOWS {
        let s = sys.narrowed(how);
        for s in [&s, &s.assume(&later, true, &Premises::new())] {
            assert!(s.bottom, "{how:?}: {s}");
            for n in &all {
                assert_eq!(kept(s, n, 0, 3), Vec::<i64>::new(), "{how:?}: {n} in {s}");
            }
        }
    }
}

#[test]
fn a_walk_of_disjunctions_narrows_in_near_linear_time() {
    family(
        "walk",
        5,
        |n| walk(n, true),
        |n| {
            let mut w: Vec<_> = (0..n)
                .map(|i| (format!("v{i}"), 0, 3, vec![1, 2, 3]))
                .collect();
            w.push(("w".into(), 0, 1, vec![0, 1]));
            w
        },
    );
}

#[test]
fn control_a_walk_without_its_start_narrows_nothing_in_near_linear_time() {
    family(
        "walk without its start",
        5,
        |n| walk(n, false),
        |n| {
            let mut w: Vec<_> = (0..n).map(|i| (format!("v{i}"), 0, 3, upto(3))).collect();
            w.push(("w".into(), 0, 1, upto(1)));
            w
        },
    );
}

/// The walk, and the walk without its start, given as one conjunction and in the reverse
/// order: near linear time in both, as [`family`] checks in the forward order, where it also
/// checks the answers in each order (ST-walk-orders: on main 44 to 85 at 8n at once, each row
/// joined against all the rows before it, and 43 to 81 in reverse). The walk is measured from
/// 40 rows, where a meet of a threshold row that changed nothing but copied its product made a
/// kept block compare every product so copied since (`Scope::meet_own`): 11.0 in reverse.
#[test]
fn a_walk_narrows_in_near_linear_time_at_once_and_in_reverse() {
    for (what, n, start) in [("walk", 40, true), ("walk without its start", 10, false)] {
        let inputs = scaling::inputs(n, |m| walk(m, start));
        for how in [How::AtOnce, How::Backward] {
            scaling::check_order(&format!("{what}, {how:?}, n rows"), n, 1, |m| {
                drop(inputs[&m].narrowed(how));
            });
        }
    }
}

/// Claude round 3 (`probe_r3.rs`, C26 and base churn): unbounded `a`, `x`, `y`,
/// `a >= x + y`, then `x + y >= j || x - y >= j` for `j < k`; with `churn`, also
/// `x + y >= j || x - y >= 2k + j` and `x - y >= j`. Each name stays unbounded both ways.
fn c26(k: usize, churn: bool) -> Sys {
    let sum = || prim(Prim::Add, var("x"), var("y"));
    let dif = || prim(Prim::Sub, var("x"), var("y"));
    let mut rel = vec![prim(Prim::Ge, var("a"), sum())];
    for j in 0..k as i64 {
        rel.push(or(
            prim(Prim::Ge, sum(), int(j)),
            prim(Prim::Ge, dif(), int(j)),
        ));
        if churn {
            rel.push(or(
                prim(Prim::Ge, sum(), int(j)),
                prim(Prim::Ge, dif(), int(2 * k as i64 + j)),
            ));
            rel.push(prim(Prim::Ge, dif(), int(j)));
        }
    }
    let start = ints(&names(&["a", "x", "y"]));
    Sys { start, rel }
}

/// Far values each name must keep: every name of C26 and base churn is unbounded.
fn far(ns: &[&str]) -> Vec<(String, i64, i64, Vec<i64>)> {
    ns.iter()
        .map(|n| {
            (
                n.to_string(),
                -1_000_000,
                1_000_000,
                vec![-1_000_000, 1_000_000],
            )
        })
        .collect()
}

/// Asserts that `sys` keeps the far values of [`far`] in each of [`HOWS`], then near linear
/// time.
fn unbounded_family(what: &str, n: usize, make: impl Fn(usize) -> Sys + Sync) {
    for m in [n, 8 * n] {
        let sys = make(m);
        for how in HOWS {
            let s = sys.narrowed(how);
            for (x, _, _, vs) in far(&["a", "x", "y"]) {
                for v in vs {
                    assert!(
                        s.get(&x).contains(&Value::Int(v)),
                        "{what}, n = {m}, {how:?}: {x} {s}"
                    );
                }
            }
        }
    }
    let inputs = scaling::inputs(n, make);
    scaling::check_order(&format!("{what}, one at a time"), n, 1, |m| {
        drop(inputs[&m].narrowed(How::Forward));
    });
}

#[test]
fn c26_narrows_in_near_linear_time() {
    unbounded_family("C26", 16, |k| c26(k, false));
}

#[test]
fn base_churn_narrows_in_near_linear_time() {
    unbounded_family("base churn", 4, |k| c26(k, true));
}

/// Claude round 3 (`probe_r3.rs`, shifted ping-pong): `x`, `y`, `z` in `-1..=r`,
/// `x - y >= 0 || y <= 0`, `x - z >= 0 || z <= 0`, `y - x >= 1 || z - x >= 1`. If `y > x`
/// the first gives `y <= 0`, so `x <= -1`; likewise for `z`: exact `x = -1`, `y`, `z` in
/// `{-1, 0}`. Class K3 refuses it (a cycle of parts).
fn ping_pong_shifted(r: usize) -> Sys {
    let le0 = |v: &str| prim(Prim::Le, var(v), int(0));
    let rel = vec![
        or(diff_ge("x", "y", 0), le0("y")),
        or(diff_ge("x", "z", 0), le0("z")),
        or(diff_ge("y", "x", 1), diff_ge("z", "x", 1)),
    ];
    Sys::new(
        &["x".into(), "y".into(), "z".into()],
        -1,
        r as i64,
        vec![],
        rel,
    )
}

#[test]
fn shifted_ping_pong_is_exact_or_refused_in_near_linear_time() {
    family("shifted ping-pong", 16, ping_pong_shifted, |r| {
        let r = r as i64;
        vec![
            ("x".into(), -1, r, vec![-1]),
            ("y".into(), -1, r, vec![-1, 0]),
            ("z".into(), -1, r, vec![-1, 0]),
        ]
    });
}

/// Claude round 3 (`probe_r3.rs`, chain raise): `x0 >= 0`, `x_{i+1} >= x_i`, `y_j` in `0..=1`,
/// and `x0 >= j + 1 || y_j <= -1` for `j < k`. The second case never holds, so `x0 >= k` and
/// every `x_i` is in `k..`: exact, each `x_i` keeps `k` and not `k - 1`.
fn chain_raise(k: usize) -> Sys {
    let xs: Vec<String> = (0..k).map(|i| format!("x{i}")).collect();
    let ys: Vec<String> = (0..k).map(|j| format!("y{j}")).collect();
    let mut rel: Vec<Term> = (0..k - 1).map(|i| diff_ge(&xs[i + 1], &xs[i], 0)).collect();
    rel.extend((0..k).map(|j| {
        or(
            prim(Prim::Ge, var("x0"), int(j as i64 + 1)),
            prim(Prim::Le, var(&ys[j]), int(-1)),
        )
    }));
    let all: Vec<&str> = xs.iter().chain(&ys).map(String::as_str).collect();
    let start = within(&ys.iter().map(String::as_str).collect::<Vec<_>>(), 0, 1)
        .into_iter()
        .chain([prim(Prim::Ge, var("x0"), int(0))])
        .reduce(and)
        .expect("one test");
    let start = ints(&names(&all)).assume(&start, true, &Premises::new());
    Sys { start, rel }
}

#[test]
fn a_chain_raise_narrows_in_near_linear_time() {
    family("chain raise", 16, chain_raise, |k| {
        let k = k as i64;
        let mut w: Vec<_> = (0..k)
            .map(|i| (format!("x{i}"), k - 1, k + 1, vec![k, k + 1]))
            .collect();
        w.extend((0..k).map(|j| (format!("y{j}"), 0, 1, upto(1))));
        w
    });
}

/// The chain raise given as one conjunction: near linear time, as in the forward order
/// (ST-walk-orders: on main 16 to 37 at 8n, each `x0 >= j + 1` raising every `x_i` in turn).
#[test]
fn a_chain_raise_given_at_once_narrows_in_near_linear_time() {
    let inputs = scaling::inputs(16, chain_raise);
    scaling::check_order("chain raise, AtOnce, k tests", 16, 1, |m| {
        drop(inputs[&m].narrowed(How::AtOnce));
    });
}

/// The B4 test of `nests.rs`, flipped to its exact answer (Gemini rounds 3 and 4, META3 and
/// META4): `x - y >= 5 || y - x >= 5`, then `-2 <= x - y <= 2`, `x`, `y` in `-20..=20`, leave no
/// value, in either order.
#[test]
fn a_band_after_a_disjunction_is_empty() {
    let p = Premises::new();
    let s = boxed(&["x", "y"], 20);
    let d = or(diff_ge("x", "y", 5), diff_ge("y", "x", 5));
    let band = and(diff_ge("x", "y", -2), diff_ge("y", "x", -2));
    let late = s.assume(&d, true, &p).assume(&band, true, &p);
    assert!(late.bottom, "{late}");
    assert!(s.assume(&band, true, &p).assume(&d, true, &p).bottom);
}

/// The tests of the B4 limits of `lazy.rs` and `l01_39a_bit_words/narrowing.rs`, flipped to
/// their exact answers (Gemini, META3 and META4): `used`, `free` in `-20..=20`,
/// `used + free >= 1 || used - free >= 30`, a test on `cap` (a star `cap >= used + free - 3`,
/// or `cap >= 0`), then `used >= free`. If `used - free >= 30` then `used >= 10`; else
/// `used + free >= 1` with `used >= free` gives `2 used >= 1`: exact `used` in `1..=20`, in an
/// eager and a lazy scope, with the test on `cap` before or after the disjunction.
#[test]
fn a_test_between_two_names_after_a_disjunction_on_both_is_exact() {
    let p = Premises::new();
    let all = names(&["used", "free", "cap"]);
    let sum = || prim(Prim::Add, var("used"), var("free"));
    let bounds = within(&["used", "free"], -20, 20)
        .into_iter()
        .reduce(and)
        .expect("two names");
    let start = ints(&all).assume(&bounds, true, &p);
    let room = or(prim(Prim::Ge, sum(), int(1)), diff_ge("used", "free", 30));
    let used: Arc<str> = Arc::from("used");
    for cap in [
        prim(Prim::Ge, var("cap"), prim(Prim::Sub, sum(), int(3))),
        prim(Prim::Ge, var("cap"), int(0)),
    ] {
        for (first, second) in [(&cap, &room), (&room, &cap)] {
            for lazy in [false, true] {
                let s = if lazy {
                    start.clone().lazy()
                } else {
                    start.clone()
                };
                let s = s.assume(first, true, &p).assume(second, true, &p).assume(
                    &diff_ge("used", "free", 0),
                    true,
                    &p,
                );
                let got: Vec<i64> = (-20..=20)
                    .filter(|v| s.settled(&used).contains(&Value::Int(*v)))
                    .collect();
                assert_eq!(
                    got,
                    (1..=20).collect::<Vec<i64>>(),
                    "{first:?} then {second:?}, lazy {lazy}: {s}"
                );
            }
        }
    }
}

/// A cycle of weight 0 makes `x_i = x0 + i` (ST-walk-orders): a bound on `x0` (the head of
/// the chain) or on `x_{n-1}` (its tail) afterward reaches every name, through the closing
/// test as well as through the chain, in every order.
#[test]
fn a_bound_on_an_end_of_a_closed_cycle_reaches_every_name() {
    let n = 8;
    let last = format!("x{}", n - 1);
    for how in HOWS {
        let s = chain(n, Some(1 - n as i64)).narrowed(how);
        let p = Premises::new();
        let head = s.assume(&prim(Prim::Le, var("x0"), int(5)), true, &p);
        let tail = s.assume(&prim(Prim::Ge, var(&last), int(30)), true, &p);
        for i in 0..n {
            let x = format!("x{i}");
            let want: Vec<i64> = (i as i64..=5 + i as i64).collect();
            assert_eq!(kept(&head, &x, 0, 32), want, "{how:?}, x0 <= 5: {x}");
            let want: Vec<i64> = (30 - (n - 1 - i) as i64..=3 * n as i64 + 1 + i as i64).collect();
            assert_eq!(kept(&tail, &x, 0, 32), want, "{how:?}, {last} >= 30: {x}");
        }
    }
}

/// Every family above in every order with `path_check` on: each test the paths take, a side of
/// one conjunction among them (`Scope::narrow_linear`), and each row `extend_threshold`
/// certifies is run again by the solver, and the scopes agree (ST-walk-orders). Given as one
/// conjunction, a family whose sides the paths take is compared at least once.
#[test]
fn every_order_of_the_families_on_paths_matches_the_solver() {
    use zedc::store::product::path_check;
    let fams: Vec<(&str, Sys, bool)> = vec![
        ("cycle of weight 0", chain(8, Some(-7)), true),
        ("cycle of weight 1", chain(8, Some(-6)), false),
        ("open chain", chain(8, None), true),
        ("walk", walk(6, true), true),
        ("walk without its start", walk(6, false), true),
        ("chain raise", chain_raise(6), true),
        ("churn", c26(3, true), false),
    ];
    for (what, sys, on_paths) in &fams {
        for how in HOWS {
            path_check::start();
            drop(sys.narrowed(how));
            let (compared, differences) = path_check::stop();
            assert!(
                differences.is_empty(),
                "{what}, {how:?}: the scopes on paths differ from the solver's:\n{}",
                differences.join("\n")
            );
            if matches!(how, How::AtOnce) && *on_paths {
                assert!(compared > 0, "{what}, {how:?}: nothing compared");
            }
        }
    }
}
