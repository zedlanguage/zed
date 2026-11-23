//! Tests of [`solve`] (PRES-one-variable-scaled-and-nested-residues): the row's scaled example,
//! a random family of scaled remainders against enumeration, [`affine_preimage`] against
//! enumeration, and the shapes that are still declined, among them the row's nested example
//! (row PRES-nested-quotient-residues).

use super::*;
use crate::scaling;
use crate::seed::Rng;
mod bench;

fn sym(s: &str) -> Lin {
    Lin::atom(Atom::Sym(s.into()))
}

fn x() -> Lin {
    sym("x")
}

/// One division as the checker writes it: `a * t + k == m * q + r` with `0 <= r <= m - 1`,
/// where `t` is `x` (`t == 0`) or the quotient of division `t - 1`. With `fixed`, the
/// remainder is that constant and the row is `a * t + k - fixed == m * q`, as the checker
/// writes it once step 1 has fixed the remainder.
#[derive(Clone, Debug)]
struct Div {
    t: usize,
    a: i64,
    k: i64,
    m: i64,
    fixed: Option<i64>,
}

/// The quotient and the remainder of division `i`, as `Aux` atoms, as the checker writes them
/// (zedc-preimage `Normal::parts`: the remainder `Aux(n)` has its quotient at `Aux(n - 1)`).
fn q_atom(i: usize) -> Atom {
    Atom::Aux(2 * i as u32)
}

fn r_atom(i: usize) -> Atom {
    Atom::Aux(2 * i as u32 + 1)
}

fn q(i: usize) -> Lin {
    Lin::atom(q_atom(i))
}

fn r(i: usize) -> Lin {
    Lin::atom(r_atom(i))
}

fn term(t: usize) -> Lin {
    if t == 0 { x() } else { q(t - 1) }
}

/// The rows of `divs`, then `lits`, then `extra`, as one conjunction.
fn formula(divs: &[Div], lits: Formula, extra: Vec<Formula>) -> Formula {
    let mut parts = Vec::new();
    for (i, d) in divs.iter().enumerate() {
        let left = term(d.t).times(d.a).plus(&Lin::constant(d.k));
        match d.fixed {
            None => {
                parts.push(Formula::Con(Con::eq(&left, &q(i).times(d.m).plus(&r(i)))));
                parts.push(Formula::Con(Con::ge(&r(i), &Lin::constant(0))));
                parts.push(Formula::Con(Con::ge(&Lin::constant(d.m - 1), &r(i))));
            }
            Some(c) => parts.push(Formula::Con(Con::eq(
                &left.plus(&Lin::constant(-c)),
                &q(i).times(d.m),
            ))),
        }
    }
    parts.push(lits);
    parts.extend(extra);
    Formula::and(parts)
}

/// The point of `divs` at `x = v`, each quotient and remainder the floor division defines; `None`
/// when a fixed remainder is not the remainder there.
fn point(divs: &[Div], v: i64) -> Option<Model> {
    let mut model = Model::new();
    model.insert(Atom::Sym("x".into()), Int::from(v));
    let mut qs: Vec<i64> = Vec::new();
    for (i, d) in divs.iter().enumerate() {
        let t = if d.t == 0 { v } else { qs[d.t - 1] };
        let e = d.a * t + d.k;
        let (fl, rem) = (e.div_euclid(d.m), e.rem_euclid(d.m));
        match d.fixed {
            None => {
                model.insert(r_atom(i), Int::from(rem));
            }
            Some(c) if c != rem => return None,
            Some(_) => {}
        }
        model.insert(q_atom(i), Int::from(fl));
        qs.push(fl);
    }
    Some(model)
}

/// Whether `f`, over the rows `divs`, has a point with `x` in `xs`.
fn has_point(f: &Formula, divs: &[Div], xs: impl Iterator<Item = i64>) -> bool {
    xs.into_iter()
        .any(|v| point(divs, v).is_some_and(|m| f.holds(&m)))
}

/// Checks `f` against `want`: [`decide`](crate::presburger::decide), the checker's entry, must
/// give `want`, and so must [`sweep::solve_modular_scaled_or_swept`] (the chain the checker
/// asks: [`solve_modular_or_scaled`], then the period sweep) with and without a model when it
/// answers; a model must be a point of `f`. Returns whether the chain answered. It may decline
/// a formula whose remainders, once rewritten, are of `x` alone:
/// [`solve_modular_whole`] declines some of those, written so from the start, before and after
/// this row (seed 7293238915329919861 case 40, `x mod 2`, `x mod 4` and `x mod 9` under a
/// negation), and the general path decides them.
fn check(f: &Formula, want: bool, what: &str) -> bool {
    assert_eq!(
        crate::presburger::decide(f),
        Ok(want),
        "{what}: decide\n{f}"
    );
    match sweep::solve_modular_scaled_or_swept(f, true) {
        Some(Some(m)) => assert!(want && f.holds(&m), "{what}: point {m:?} of\n{f}"),
        Some(None) => assert!(!want, "{what}: no point found, but one exists, in\n{f}"),
        None => return false,
    }
    assert_eq!(
        sweep::solve_modular_scaled_or_swept(f, false).map(|m| m.is_some()),
        Some(want),
        "{what} without a model\n{f}"
    );
    true
}

/// [`check`], and the chain it asks must answer.
fn check_answered(f: &Formula, want: bool, what: &str) {
    assert!(check(f, want, what), "{what}: declined\n{f}");
}

/// The rows of the scaled example: `(3 * x - 4) mod 30`, `(5 * x + 5) mod 8`,
/// `(7 * x + 4) mod 10`, `(x - 3) mod 2`, `(5 * x) mod 6`, `(7 * x) mod 12`.
fn scaled_example() -> (Vec<Div>, Formula) {
    let d = |a, k, m| Div {
        t: 0,
        a,
        k,
        m,
        fixed: None,
    };
    let divs = vec![
        d(3, -4, 30),
        d(5, 5, 8),
        d(7, 4, 10),
        d(1, -3, 2),
        d(5, 0, 6),
        d(7, 0, 12),
    ];
    let lits = example_literals(&[0, 1, 2, 3, 4, 5]);
    (divs, lits)
}

/// `r_a <= 9 && r_b <= 7 && r_c <= 5 && r_d == 1 && !(r_e == 1) && !(r_f == 11)`, the literals
/// of both examples.
fn example_literals(at: &[usize; 6]) -> Formula {
    let le = |i: usize, c: i64| Formula::Con(Con::ge(&Lin::constant(c), &r(i)));
    let is = |i: usize, c: i64| Formula::Con(Con::eq(&r(i), &Lin::constant(c)));
    Formula::and(vec![
        le(at[0], 9),
        le(at[1], 7),
        le(at[2], 5),
        is(at[3], 1),
        Formula::negate(is(at[4], 1)),
        Formula::negate(is(at[5], 11)),
    ])
}

/// The rows of the nested example: `x div 3` (row 0), `(x div 3) mod 10` (row 1),
/// `(x - 4) mod 30`, `(x + 5) mod 8`, `(x - 3) mod 2`, `x mod 6`, `x div 7` (row 6) and
/// `(x div 7) mod 12` (row 7).
fn nested_example() -> (Vec<Div>, Formula) {
    let d = |t, k, m| Div {
        t,
        a: 1,
        k,
        m,
        fixed: None,
    };
    let divs = vec![
        d(0, 0, 3),
        d(1, 0, 10),
        d(0, -4, 30),
        d(0, 5, 8),
        d(0, -3, 2),
        d(0, 0, 6),
        d(0, 0, 7),
        d(7, 0, 12),
    ];
    // `(x div 3) mod 10 <= 5`, then the literals of the scaled example on rows 2 to 5 and 7.
    let lits = Formula::and(vec![
        Formula::Con(Con::ge(&Lin::constant(5), &r(1))),
        example_literals(&[2, 3, 3, 4, 5, 7]),
    ]);
    (divs, lits)
}

#[test]
fn the_rows_scaled_example_is_decided() {
    // It was declined, and refused by the general path with the shadows reason. It holds
    // exactly at x = 4 mod 10.
    let fix = |v: i64| vec![Formula::Con(Con::eq(&x(), &Lin::constant(v)))];
    let (divs, lits) = scaled_example();
    let ins = [4, 14, -6, 64, 124];
    check_answered(&formula(&divs, lits.clone(), vec![]), true, "scaled");
    for v in [4, 5, 14, -6, 64, 124] {
        let f = formula(&divs, lits.clone(), fix(v));
        let want = has_point(&f, &divs, [v].into_iter());
        assert_eq!(want, ins.contains(&v), "scaled at {v}: the enumeration");
        check_answered(&f, want, &format!("scaled at {v}"));
    }
}

/// Up to three divisions of `x`, with coefficients that may be negative, larger than the
/// modulus, or share a factor with it.
fn random_divs(rng: &mut Rng) -> Vec<Div> {
    let n = 1 + rng.below(3);
    let mut divs = Vec::new();
    for _ in 0..n {
        let t = 0;
        let a = if rng.below(3) == 0 {
            rng.pick(&[1, -1])
        } else {
            let a = rng.int(2, 14);
            if rng.coin() { a } else { -a }
        };
        let m = rng.int(2, 9);
        let k = rng.int(-12, 12);
        let fixed = (rng.below(6) == 0).then(|| rng.int(0, m - 1));
        divs.push(Div { t, a, k, m, fixed });
    }
    divs
}

/// A random Boolean combination of one-term literals on the remainders of `divs` and on `x`.
fn random_literals(rng: &mut Rng, divs: &[Div], depth: u32) -> Formula {
    let free: Vec<usize> = (0..divs.len())
        .filter(|&i| divs[i].fixed.is_none())
        .collect();
    if depth == 0 || rng.below(3) == 0 {
        if free.is_empty() || rng.below(6) == 0 {
            let c = Lin::constant(rng.int(-20, 20));
            return Formula::Con(if rng.coin() {
                Con::ge(&x(), &c)
            } else {
                Con::ge(&c, &x())
            });
        }
        let i = rng.pick(&free);
        let c = Lin::constant(rng.int(-1, divs[i].m));
        return Formula::Con(match rng.below(3) {
            0 => Con::ge(&r(i), &c),
            1 => Con::ge(&c, &r(i)),
            _ => Con::eq(&r(i), &c),
        });
    }
    let kids = (0..2 + rng.below(2))
        .map(|_| random_literals(rng, divs, depth - 1))
        .collect();
    match rng.below(3) {
        0 => Formula::and(kids),
        1 => Formula::or(kids),
        _ => Formula::negate(Formula::and(kids)),
    }
}

#[test]
fn scaled_remainders_match_enumeration() {
    // Every remainder is periodic in `x` with a period dividing the product `P` of the moduli
    // (at `x + P` each row's dividend moves by a multiple of its modulus), and each literal on
    // `x` has a constant in
    // [-20, 20], so it has one truth value on all of `x < -20` and one on all of `x > 20`. A
    // point at `x < -20 - P` thus has one at `x + j P` in `[-20 - P, -21]` for some `j`, and
    // likewise above, so `[-20 - P, 20 + P]` holds a point exactly when the line does; an outer
    // bound on `x` is read on its own window.
    let (mut rng, seed) = Rng::fresh("scaled_remainders_match_enumeration");
    crate::presburger::CHECK_LOSSLESS.with(|c| c.set(true));
    let mut answered = [0usize; 2];
    let mut by_solve = [0usize; 2];
    for case in 0..400 {
        let divs = random_divs(&mut rng);
        let lits = random_literals(&mut rng, &divs, 2);
        let period: i64 = divs.iter().map(|d| d.m).product();
        let (extra, xs): (Vec<Formula>, Vec<i64>) = if rng.coin() {
            (vec![], (-20 - period..=20 + period).collect())
        } else {
            let lo = rng.int(-30, 30);
            let hi = lo + rng.int(0, 40);
            (
                vec![
                    Formula::Con(Con::ge(&x(), &Lin::constant(lo))),
                    Formula::Con(Con::ge(&Lin::constant(hi), &x())),
                ],
                (lo..=hi).collect(),
            )
        };
        let f = formula(&divs, lits, extra);
        let want = has_point(&f, &divs, xs.into_iter());
        let by_module = check(&f, want, &format!("seed {seed} case {case} {divs:?}"));
        answered[usize::from(want)] += 1;
        by_solve[usize::from(want)] += usize::from(by_module);
    }
    // Both answers are met, so neither side is checked vacuously, and this module answers most
    // cases itself (388 to 396 of 400 over nine seeds when written), so a module that declined
    // everything would not pass on `decide` alone.
    assert!(answered[0] > 40 && answered[1] > 40, "{answered:?}");
    assert!(
        by_solve[0] > 40 && by_solve[1] > 40 && by_solve[0] + by_solve[1] > 300,
        "{by_solve:?}"
    );
}

/// Case 272 of [`scaled_remainders_match_enumeration`] at seed 9563318029921447897
/// (FAIL-presburger-fresh-seed-refusals): `(x + 5) mod 8`, `(-14 x - 2) mod 8` and
/// `(11 x + 3) mod 5`, with no bound on `x`.
fn seed_9563318029921447897_case_272() -> (Vec<Div>, Formula) {
    let one = |a, k, m| Div {
        t: 0,
        a,
        k,
        m,
        fixed: None,
    };
    let divs = vec![one(1, 5, 8), one(-14, -2, 8), one(11, 3, 5)];
    let c = Lin::constant;
    let lits = Formula::negate(Formula::and(vec![
        Formula::Con(Con::ge(&r(2), &c(2))),
        Formula::or(vec![
            Formula::Con(Con::eq(&r(2), &c(1))),
            Formula::Con(Con::ge(&r(2), &c(1))),
            Formula::Con(Con::ge(&r(0), &c(4))),
        ]),
        Formula::negate(Formula::and(vec![
            Formula::Con(Con::ge(&x(), &c(11))),
            Formula::Con(Con::ge(&c(4), &r(0))),
        ])),
    ]));
    let f = formula(&divs, lits, vec![]);
    (divs, f)
}

#[test]
fn seed_9563318029921447897_case_272_is_decided() {
    // Refused (Shadows) before the lossless stage of `Omega::run`: of the band
    // `31 <= 56 x3 + 7 x4 + 4 x6 <= 34`, the dark shadow of x3 was taken where eliminating x6
    // loses nothing (4 * 3 >= (4 - 1) * (4 - 1)).
    let (divs, f) = seed_9563318029921447897_case_272();
    let period: i64 = divs.iter().map(|d| d.m).product();
    assert!(has_point(&f, &divs, -20 - period..=20 + period), "{f}");
    // The period sweep (`sweep.rs`) decides `f` itself; `y >= 0` on a symbol of no row keeps it
    // out, so `f` still reaches the Omega test and its lossless stage.
    let f = Formula::and(vec![f, Formula::Con(Con::ge(&sym("y"), &Lin::constant(0)))]);
    assert_eq!(sweep::solve(&f, false), None);
    crate::presburger::CHECK_LOSSLESS.with(|c| c.set(true));
    crate::presburger::LOSSLESS_STEPS.with(|c| c.set(0));
    check(&f, true, "seed 9563318029921447897 case 272");
    let steps = crate::presburger::LOSSLESS_STEPS.with(|c| c.get());
    assert!(steps > 0, "the lossless stage was not taken");
}

#[test]
fn an_affine_preimage_matches_enumeration() {
    // Every `a` in [-20, 20], `k` in [-9, 9] and `m` in [1, 24], with a random set of residues:
    // the residues `t mod n` [`affine_preimage`] gives are those at which `(a t + k) mod m` lies
    // in the set. Both ways of writing an interval (points, windows) and both sides (the set,
    // its complement) are met.
    let (mut rng, seed) = Rng::fresh("an_affine_preimage_matches_enumeration");
    for m in 1..=24i64 {
        for a in -20..=20i64 {
            for k in -9..=9i64 {
                let mut v = Vec::new();
                for _ in 0..1 + rng.below(3) {
                    let l = rng.int(0, m - 1);
                    v.push((Int::from(l), Int::from(rng.int(l, m - 1))));
                }
                let v = res_normalize(v, &Int::from(m));
                let inside = |w: i64| {
                    v.iter()
                        .any(|(l, h)| *l <= Int::from(w) && Int::from(w) <= *h)
                };
                let (n, t) = affine_preimage(&Int::from(a), &Int::from(k), &Int::from(m), &v)
                    .expect("small sets are written");
                let g = if a == 0 { m } else { num_gcd(a, m) };
                assert_eq!(n, Int::from(m / g), "seed {seed}: n of {a} t + {k} mod {m}");
                let nn = m / g;
                for s in 0..nn {
                    let got = t
                        .iter()
                        .any(|(l, h)| *l <= Int::from(s) && Int::from(s) <= *h);
                    let want = inside((a * s + k).rem_euclid(m));
                    assert_eq!(
                        got, want,
                        "seed {seed}: t = {s}, {a} t + {k} mod {m} in {v:?}"
                    );
                }
            }
        }
    }
}

fn num_gcd(a: i64, b: i64) -> i64 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

#[test]
fn reflected_residues_match_enumeration() {
    for n in 1..=12i64 {
        let nn = Int::from(n);
        for l in 0..n {
            for h in l..n {
                let s = vec![(Int::from(l), Int::from(h))];
                let t = reflect_residues(&s, &nn);
                for v in 0..n {
                    let got = t
                        .iter()
                        .any(|(a, b)| *a <= Int::from(v) && Int::from(v) <= *b);
                    let want = (l..=h).contains(&(n - v).rem_euclid(n));
                    assert_eq!(got, want, "n {n}, [{l}, {h}], {v}");
                }
            }
        }
    }
}

#[test]
fn a_scaled_remainder_outside_its_values_has_no_point() {
    // Negative controls: `(3 x) mod 6` is 0 or 3, so `== 1` has no point; `(4 x + 2) mod 8` is
    // 2 or 6, so `<= 1 || == 4` has none. Each was declined before.
    let one = |a, k, m| Div {
        t: 0,
        a,
        k,
        m,
        fixed: None,
    };
    let is = |i: usize, c: i64| Formula::Con(Con::eq(&r(i), &Lin::constant(c)));
    let le = |i: usize, c: i64| Formula::Con(Con::ge(&Lin::constant(c), &r(i)));
    let cases = [
        (vec![one(3, 0, 6)], is(0, 1)),
        (vec![one(4, 2, 8)], Formula::or(vec![le(0, 1), is(0, 4)])),
    ];
    for (i, (divs, lits)) in cases.into_iter().enumerate() {
        let f = formula(&divs, lits, vec![]);
        let period: i64 = divs.iter().map(|d| d.m).product();
        assert!(
            !has_point(&f, &divs, 0..period),
            "case {i}: the enumeration"
        );
        check_answered(&f, false, &format!("case {i}"));
    }
}

#[test]
fn other_shapes_are_still_declined() {
    // Negative controls of the shape: a second variable in a remainder, a quotient read by a
    // bound, and a remainder of a sum of two quotients (a row of four atoms). Each needs more
    // than residues of one variable, and `solve` leaves it to the general path.
    let ge = |a: &Lin, c: i64| Formula::Con(Con::ge(a, &Lin::constant(c)));
    let row = |left: Lin, m: i64, i: usize| {
        vec![
            Formula::Con(Con::eq(&left, &q(i).times(m).plus(&r(i)))),
            ge(&r(i), 0),
            Formula::Con(Con::ge(&Lin::constant(m - 1), &r(i))),
        ]
    };
    let two_vars = Formula::and(
        [
            row(x().times(3).plus(&sym("y")), 30, 0),
            vec![Formula::Con(Con::ge(&Lin::constant(9), &r(0)))],
        ]
        .concat(),
    );
    let quotient_bound = Formula::and(
        [
            row(x().times(3), 30, 0),
            vec![
                ge(&q(0), 5),
                Formula::Con(Con::ge(&Lin::constant(9), &r(0))),
            ],
        ]
        .concat(),
    );
    // A sum whose remainder's bound reaches the modulus is not a remainder ([`read_sum`]).
    let sum_bound_too_high = Formula::and(
        [
            row(x(), 3, 0),
            row(x(), 5, 1),
            vec![
                Formula::Con(Con::eq(&q(0).plus(&q(1)), &q(2).times(7).plus(&r(2)))),
                ge(&r(2), 0),
                Formula::Con(Con::ge(&Lin::constant(7), &r(2))),
            ],
        ]
        .concat(),
    );
    // A sum whose quotient another constraint reads.
    let sum_quotient_read = Formula::and(
        [
            row(x(), 3, 0),
            row(x(), 5, 1),
            row(q(0).plus(&q(1)), 7, 2),
            vec![Formula::Con(Con::ge(&q(2).plus(&x()), &Lin::constant(4)))],
        ]
        .concat(),
    );
    // A quotient read by a bound was declined here until FAIL-omega-pairs-4972743790605253739;
    // the period sweep (`sweep.rs`) now decides it: `3 x div 30 >= 5` with `3 x mod 30 <= 9`
    // holds at `x = 50`.
    check_answered(&quotient_bound, true, "a quotient read by a bound");
    for (what, f) in [
        ("two variables", two_vars),
        (
            "a sum whose remainder may reach the modulus",
            sum_bound_too_high,
        ),
        ("a sum whose quotient is read", sum_quotient_read),
    ] {
        assert!(solve(&f, true).is_none(), "{what}: answered\n{f}");
    }
}

/// The example of row PRES-one-variable-sum-of-quotients, `(x div 3 + x div 5) mod 7 <= 2`, with
/// the checker's `(x - 4) mod 30 <= 9` and `x mod 6 != 1` (the program of
/// tests/steps/l01_38_presburger/checker.rs), and the same with `== 6` added, decided against
/// enumeration over one period (`3 * 5 * 7 * 30 * 6` covers every row's period).
#[test]
fn the_rows_sum_example_is_decided() {
    let ge = |a: &Lin, c: i64| Formula::Con(Con::ge(a, &Lin::constant(c)));
    let le = |a: &Lin, c: i64| Formula::Con(Con::ge(&Lin::constant(c), a));
    let row = |left: Lin, m: i64, i: usize| {
        vec![
            Formula::Con(Con::eq(&left, &q(i).times(m).plus(&r(i)))),
            ge(&r(i), 0),
            le(&r(i), m - 1),
        ]
    };
    let rows = [
        row(x(), 3, 0),
        row(x(), 5, 1),
        row(q(0).plus(&q(1)), 7, 2),
        row(x().plus(&Lin::constant(-4)), 30, 3),
        row(x(), 6, 4),
    ]
    .concat();
    let lits = vec![
        le(&r(2), 2),
        le(&r(3), 9),
        Formula::or(vec![le(&r(4), 0), ge(&r(4), 2)]),
    ];
    let value = |v: i64, eq6: bool| {
        let s = v.div_euclid(3) + v.div_euclid(5);
        s.rem_euclid(7) <= 2
            && (v - 4).rem_euclid(30) <= 9
            && v.rem_euclid(6) != 1
            && (!eq6 || s.rem_euclid(7) == 6)
    };
    for eq6 in [false, true] {
        let mut parts = [rows.clone(), lits.clone()].concat();
        if eq6 {
            parts.push(Formula::Con(Con::eq(&r(2), &Lin::constant(6))));
        }
        let f = Formula::and(parts);
        let want = (0..3 * 5 * 7 * 30 * 6).any(|v| value(v, eq6));
        check_answered(&f, want, &format!("the row's example, == 6: {eq6}"));
    }
}

/// A sum `sum c_j p_j + k == m qs + rs` (or `== m qs` with no remainder) over parts of the
/// divisions: part `0` is `x`, part `2 i + 1` the quotient and `2 i + 2` the remainder of
/// division `i`. Its quotient and remainder are `Aux` atoms past every division's.
#[derive(Clone, Debug)]
struct Sum {
    parts: Vec<(usize, i64)>,
    k: i64,
    m: i64,
    rem: bool,
}

fn part(p: usize) -> Lin {
    match p {
        0 => x(),
        p if p % 2 == 1 => q(p / 2),
        p => r(p / 2 - 1),
    }
}

/// Up to two sums over two or three distinct parts of `divs` each (remainders only of
/// divisions whose remainder is not fixed), as constraints, with their atoms numbered from
/// division `divs.len()` on.
fn random_sums(rng: &mut Rng, divs: &[Div]) -> Vec<Sum> {
    let mut avail: Vec<usize> = vec![0];
    for (i, d) in divs.iter().enumerate() {
        avail.push(2 * i + 1);
        if d.fixed.is_none() {
            avail.push(2 * i + 2);
        }
    }
    (0..1 + rng.below(2))
        .map(|_| {
            let rem = avail.len() < 3 || rng.below(4) != 0;
            // Three parts with no remainder, so the equation has four terms and is no row.
            let want = if rem { 2 + rng.below(2) } else { 3 };
            let mut parts: Vec<(usize, i64)> = Vec::new();
            while parts.len() < (want as usize).min(avail.len()) {
                let p = rng.pick(&avail);
                if parts.iter().all(|(o, _)| *o != p) {
                    let c = rng.int(1, 4);
                    parts.push((p, if rng.coin() { c } else { -c }));
                }
            }
            Sum {
                parts,
                k: rng.int(-6, 6),
                m: rng.int(2, 6),
                rem,
            }
        })
        .collect()
}

fn sum_formulas(divs: &[Div], sums: &[Sum]) -> Vec<Formula> {
    let mut out = Vec::new();
    for (j, s) in sums.iter().enumerate() {
        let i = divs.len() + j;
        let mut left = Lin::constant(s.k);
        for (p, c) in &s.parts {
            left = left.plus(&part(*p).times(*c));
        }
        if s.rem {
            out.push(Formula::Con(Con::eq(&left, &q(i).times(s.m).plus(&r(i)))));
            out.push(Formula::Con(Con::ge(&r(i), &Lin::constant(0))));
            out.push(Formula::Con(Con::ge(&Lin::constant(s.m - 1), &r(i))));
        } else {
            out.push(Formula::Con(Con::eq(&left, &q(i).times(s.m))));
        }
    }
    out
}

/// [`point`], with each sum's quotient and remainder; `None` when a sum with no remainder is
/// not divisible.
fn point_sums(divs: &[Div], sums: &[Sum], v: i64) -> Option<Model> {
    let mut model = point(divs, v)?;
    for (j, s) in sums.iter().enumerate() {
        let i = divs.len() + j;
        let mut e = s.k;
        for (p, c) in &s.parts {
            let at = match *p {
                0 => v,
                p if p % 2 == 1 => model[&q_atom(p / 2)].to_i128().expect("small") as i64,
                p => model[&r_atom(p / 2 - 1)].to_i128().expect("small") as i64,
            };
            e += c * at;
        }
        let (fl, rem) = (e.div_euclid(s.m), e.rem_euclid(s.m));
        if s.rem {
            model.insert(r_atom(i), Int::from(rem));
        } else if rem != 0 {
            return None;
        }
        model.insert(q_atom(i), Int::from(fl));
    }
    Some(model)
}

/// A random Boolean combination of one-term literals on the sums' remainders.
fn random_sum_literals(rng: &mut Rng, divs: &[Div], sums: &[Sum], depth: u32) -> Formula {
    let free: Vec<usize> = (0..sums.len()).filter(|&j| sums[j].rem).collect();
    if free.is_empty() {
        return Formula::top();
    }
    if depth == 0 || rng.below(3) == 0 {
        let j = rng.pick(&free);
        let i = divs.len() + j;
        // In `0..m`, so a top-level literal leaves the remainder's bounds a nonempty part of
        // `[0, m - 1]`, which [`read_sum`] needs.
        let c = Lin::constant(rng.int(0, sums[j].m - 1));
        return Formula::Con(match rng.below(3) {
            0 => Con::ge(&r(i), &c),
            1 => Con::ge(&c, &r(i)),
            _ => Con::eq(&r(i), &c),
        });
    }
    let kids = (0..2 + rng.below(2))
        .map(|_| random_sum_literals(rng, divs, sums, depth - 1))
        .collect();
    match rng.below(3) {
        0 => Formula::and(kids),
        1 => Formula::or(kids),
        _ => Formula::negate(Formula::and(kids)),
    }
}

/// Seed 3730609663341733710 case 223 of [`sums_of_quotients_match_enumeration`] (row
/// PRES-sum-of-quotients-period-product, part 2): the remainder of `(-5 x - 5) mod 5` is fixed
/// at 0, so the row is written `5 x + 5 q4 == -5`, and divided by its gcd it is `x + q4 == -1`,
/// a row of modulus 1. `solve` declined the formula, since `q4` was no row's quotient, and
/// `decide` refused it with `Shadows`; it has a point (`x = -3`: `q1 = 1`, `q3 = 2`, the sum
/// `x + 3 q6 + q7 == 3 q1 + q3 - 4` gives `q7 = 1`).
#[test]
fn seed_3730609663341733710_case_223_is_decided() {
    let aux = |i: u32| Lin::atom(Atom::Aux(i));
    let c = Lin::constant;
    let eq = |a: Lin, b: Lin| Formula::Con(Con::eq(&a, &b));
    let ge = |a: Lin, b: Lin| Formula::Con(Con::ge(&a, &b));
    let q7 = || aux(7);
    let f = Formula::and(vec![
        eq(x().times(2).plus(&aux(0).times(3)).plus(&aux(1)), c(-5)),
        ge(aux(1), c(0)),
        ge(c(2), aux(1)),
        eq(x().plus(&aux(2).times(4)).plus(&aux(3)), c(-9)),
        ge(aux(3), c(0)),
        ge(c(3), aux(3)),
        eq(x().times(5).plus(&aux(4).times(5)), c(-5)),
        Formula::negate(Formula::and(vec![ge(aux(3), c(3)), ge(c(4), aux(3))])),
        Formula::negate(Formula::and(vec![
            ge(c(0), q7()),
            eq(q7(), c(0)),
            Formula::or(vec![ge(c(2), q7()), eq(q7(), c(1)), ge(c(2), q7())]),
        ])),
        eq(
            x().plus(&aux(6).times(3)).plus(&q7()),
            aux(1).times(3).plus(&aux(3)).plus(&c(-4)),
        ),
        ge(q7(), c(0)),
        ge(c(2), q7()),
    ]);
    check_answered(&f, true, "seed 3730609663341733710 case 223");
}

/// Seed 12744803785466090665 case 189 of [`sums_of_quotients_match_enumeration`] (row
/// PRES-sum-of-quotients-shadows-random; found by b22-checkrest2 on main 090973b27). The
/// general path asks again with its atoms renamed to `Sym`s, where `4 y + r == 5 x + 11`
/// (`r` in `[0, 3]`) reads with either end as the quotient; `orient` took `y` as the variable,
/// the other row became a chain on `x`, `solve` declined, and `decide` refused with `Shadows`.
/// The module may still decline the formula as first written, as [`check`] allows; `decide`
/// answers.
#[test]
fn seed_12744803785466090665_case_189_is_decided() {
    let aux = |i: u32| Lin::atom(Atom::Aux(i));
    let c = Lin::constant;
    let eq = |a: Lin, b: Lin| Formula::Con(Con::eq(&a, &b));
    let ge = |a: Lin, b: Lin| Formula::Con(Con::ge(&a, &b));
    let f = Formula::and(vec![
        eq(x().times(4), aux(0).times(3).plus(&aux(1)).plus(&c(4))),
        ge(aux(1), c(0)),
        ge(c(2), aux(1)),
        eq(x().times(5), aux(2).times(4).plus(&aux(3)).plus(&c(-11))),
        ge(aux(3), c(0)),
        ge(c(3), aux(3)),
        Formula::or(vec![
            Formula::negate(Formula::and(vec![eq(aux(7), c(0)), ge(c(1), aux(5))])),
            Formula::and(vec![eq(aux(5), c(1)), ge(aux(7), c(2))]),
        ]),
        eq(
            aux(0),
            aux(3)
                .times(3)
                .plus(&aux(4).times(3))
                .plus(&aux(5))
                .plus(&c(-5)),
        ),
        ge(aux(5), c(0)),
        ge(c(2), aux(5)),
        eq(
            x().times(3)
                .plus(&aux(0))
                .plus(&aux(6).times(4))
                .plus(&aux(7)),
            aux(2).times(3).plus(&c(4)),
        ),
        ge(aux(7), c(0)),
        ge(c(3), aux(7)),
    ]);
    check(&f, true, "seed 12744803785466090665 case 189");
}

/// Seed 3700079103403926633 case 92 of [`sums_of_quotients_match_enumeration`] (row
/// PRES-sum-of-quotients-shadows-random): the sum `3 q0 + 3 q4 == 3 q2 + 3 q3 - 6`, whose
/// remainder is always zero, is `q0 + q4 - q2 - q3 == -2` divided by its gcd, a sum of
/// modulus one. `read_sum` asked for a modulus of at least 2, so `q4` was no sum's quotient,
/// `solve` declined, and `decide` refused with `Shadows`.
#[test]
fn seed_3700079103403926633_case_92_is_decided() {
    let aux = |i: u32| Lin::atom(Atom::Aux(i));
    let c = Lin::constant;
    let eq = |a: Lin, b: Lin| Formula::Con(Con::eq(&a, &b));
    let ge = |a: Lin, b: Lin| Formula::Con(Con::ge(&a, &b));
    let f = Formula::and(vec![
        eq(x().times(2).plus(&aux(0).times(5)).plus(&aux(1)), c(-5)),
        ge(aux(1), c(0)),
        ge(c(4), aux(1)),
        eq(x().times(10), aux(2).times(3).plus(&aux(3)).plus(&c(-10))),
        ge(aux(3), c(0)),
        ge(c(2), aux(3)),
        Formula::or(vec![eq(aux(1), c(3)), eq(aux(3), c(2))]),
        ge(c(1), aux(7)),
        eq(
            aux(0).times(3).plus(&aux(4).times(3)),
            aux(2).times(3).plus(&aux(3).times(3)).plus(&c(-6)),
        ),
        eq(
            x().plus(&aux(3).times(2))
                .plus(&aux(6).times(4))
                .plus(&aux(7)),
            aux(1).plus(&c(-2)),
        ),
        ge(aux(7), c(0)),
        ge(x(), c(-10)),
        ge(c(-6), x()),
    ]);
    check_answered(&f, true, "seed 3700079103403926633 case 92");
}

#[test]
fn sums_of_quotients_match_enumeration() {
    // As in `scaled_remainders_match_enumeration`: every remainder and every sum's remainder is
    // periodic in `x` with a period dividing the product `P` of all the moduli (a sum's period
    // `m L` divides it, [`sum_residues`]), so `[-20 - P, 20 + P]` holds a point exactly when
    // the line does.
    let (mut rng, seed) = Rng::fresh("sums_of_quotients_match_enumeration");
    crate::presburger::CHECK_LOSSLESS.with(|c| c.set(true));
    let mut answered = [0usize; 2];
    let mut by_solve = [0usize; 2];
    for case in 0..300 {
        let divs: Vec<Div> = random_divs(&mut rng)
            .into_iter()
            .map(|d| Div {
                m: 2 + d.m % 4,
                fixed: d.fixed.map(|c| c % (2 + d.m % 4)),
                ..d
            })
            .collect();
        let sums = random_sums(&mut rng, &divs);
        let lits = Formula::and(vec![
            random_literals(&mut rng, &divs, 1),
            random_sum_literals(&mut rng, &divs, &sums, 2),
        ]);
        let period: i64 = divs
            .iter()
            .map(|d| d.m)
            .chain(sums.iter().map(|s| s.m))
            .product();
        let (extra, xs): (Vec<Formula>, Vec<i64>) = if rng.coin() {
            (vec![], (-20 - period..=20 + period).collect())
        } else {
            let lo = rng.int(-30, 30);
            let hi = lo + rng.int(0, 40);
            (
                vec![
                    Formula::Con(Con::ge(&x(), &Lin::constant(lo))),
                    Formula::Con(Con::ge(&Lin::constant(hi), &x())),
                ],
                (lo..=hi).collect(),
            )
        };
        let f = formula(&divs, lits, [sum_formulas(&divs, &sums), extra].concat());
        let want = xs
            .into_iter()
            .any(|v| point_sums(&divs, &sums, v).is_some_and(|m| f.holds(&m)));
        let by_module = check(
            &f,
            want,
            &format!("seed {seed} case {case} {divs:?} {sums:?}"),
        );
        answered[usize::from(want)] += 1;
        by_solve[usize::from(want)] += usize::from(by_module);
    }
    // `solve` answers 293 to 300 of 300 over eleven seeds when written (the rest
    // `solve_modular_whole` declines, as in `check`, and `decide` answers them), so a module
    // that declined the sums would fail here and on `decide`.
    assert!(
        answered[0] > 40 && answered[1] > 40 && by_solve[0] + by_solve[1] > 270,
        "seed {seed}: answers {answered:?}, by solve {by_solve:?}"
    );
}

#[test]
fn a_remainder_of_a_quotient_is_still_declined() {
    // A row on the quotient of another row is declined (see the tradeoff at [`solve`]; row
    // PRES-nested-quotient-residues), so these stay as on main before this row: the row's
    // nested example is refused, and a chain of quotients by 3 with a literal on each level,
    // and `((2 x) div 3) mod 4 == 1` with `x mod 3 == 0` (no point: there `2 x div 3 = 2 (x / 3)`
    // is even), are declined here; the general path refuses them or gives the enumerated answer.
    let (divs, lits) = nested_example();
    let f = formula(&divs, lits, vec![]);
    assert!(solve(&f, true).is_none(), "nested example: answered\n{f}");
    assert!(
        crate::presburger::decide(&f).is_err(),
        "nested example: not refused\n{f}"
    );
    let one = |t, a, m| Div {
        t,
        a,
        k: 0,
        m,
        fixed: None,
    };
    let is = |i: usize, c: i64| Formula::Con(Con::eq(&r(i), &Lin::constant(c)));
    let even = vec![one(0, 2, 3), one(1, 1, 4), one(0, 1, 3)];
    let mut cases = vec![(
        "an even quotient".to_string(),
        even.clone(),
        formula(
            &even,
            Formula::and(vec![is(1, 1), is(0, 0), is(2, 0)]),
            vec![],
        ),
    )];
    // Depth 1 is one row on `x`, not a chain.
    for depth in 2..=6 {
        let (divs, f) = chain_of_quotients(depth);
        cases.push((format!("depth {depth}"), divs, f));
    }
    for (what, divs, f) in cases {
        assert!(solve(&f, true).is_none(), "{what}: answered\n{f}");
        let period: i64 = divs.iter().map(|d| d.m).product();
        let want = has_point(&f, &divs, 0..period);
        let got = crate::presburger::decide(&f);
        assert!(
            got.is_err() || got == Ok(want),
            "{what}: {got:?}, want {want}\n{f}"
        );
    }
}

/// The small instances of the benchmark in `bench.rs`, against enumeration.
#[test]
fn the_benchmark_inputs_have_their_answers_at_small_sizes() {
    for m in [7, 30, 101] {
        let (divs, f) = bench_modulus(m);
        let want = has_point(&f, &divs, 0..m);
        check_answered(&f, want, &format!("modulus {m}"));
    }
    for m in [7, 30, 101] {
        let (divs, f) = bench_sum(m);
        let want = (0..15 * m).any(|v| {
            let s = v.div_euclid(3) + v.div_euclid(5);
            point(&divs, v).is_some_and(|mut p| {
                for (i, k) in [(2, 0), (3, 1)] {
                    p.insert(q_atom(i), Int::from((s + k).div_euclid(m)));
                    p.insert(r_atom(i), Int::from((s + k).rem_euclid(m)));
                }
                f.holds(&p)
            })
        });
        assert!(!want, "sum modulus {m}: a point");
        check_answered(&f, want, &format!("sum modulus {m}"));
    }
    for n in [1, 3] {
        assert_eq!(
            sweep::solve(&bench_runs(n), true),
            Some(None),
            "runs at {n}"
        );
    }
}

/// `(x div 3 + x div 5) mod m == 0` and `(x div 3 + x div 5 + 1) mod m == 0`, two sums with no
/// common point (for `m >= 2`): no point stops the search early, and each sum's literal gives
/// residues of `x` modulo its period `15 m` ([`sum_residues`]), so the work is at least linear
/// in `m`. The second sum's quotient and remainder are those of division 3.
fn bench_sum(m: i64) -> (Vec<Div>, Formula) {
    let divs: Vec<Div> = [3, 5]
        .into_iter()
        .map(|d| Div {
            t: 0,
            a: 1,
            k: 0,
            m: d,
            fixed: None,
        })
        .collect();
    let mut sums = Vec::new();
    for (i, k) in [(2, 0), (3, 1)] {
        sums.push(Formula::Con(Con::eq(
            &q(0).plus(&q(1)).plus(&Lin::constant(k)),
            &q(i).times(m).plus(&r(i)),
        )));
        sums.push(Formula::Con(Con::ge(&r(i), &Lin::constant(0))));
        sums.push(Formula::Con(Con::ge(&Lin::constant(m - 1), &r(i))));
    }
    let lits = Formula::or(vec![
        Formula::negate(Formula::Con(Con::eq(&r(2), &Lin::constant(0)))),
        Formula::Con(Con::eq(&r(3), &Lin::constant(0))),
    ]);
    let lits = Formula::and(vec![lits, Formula::Con(Con::eq(&r(2), &Lin::constant(0)))]);
    (divs.clone(), formula(&divs, lits, sums))
}

/// `(a x + 3) mod m` with `a` the nearest integer to `m / 3` coprime to `m`, in the lower half
/// `[0, m / 2]` and not `1`: each literal pulls back to about `m / 3` runs of residues of `x`
/// on both sides, the most the windows allow, so this is the costly case of a modulus `m`.
fn bench_modulus(m: i64) -> (Vec<Div>, Formula) {
    let a = (m / 3..).find(|a| num_gcd(*a, m) == 1).expect("a coprime");
    let divs = vec![Div {
        t: 0,
        a,
        k: 3,
        m,
        fixed: None,
    }];
    let lits = Formula::and(vec![
        Formula::Con(Con::ge(&Lin::constant(m / 2), &r(0))),
        Formula::negate(Formula::Con(Con::eq(&r(0), &Lin::constant(1)))),
    ]);
    (divs.clone(), formula(&divs, lits, vec![]))
}

/// `x div 3`, its quotient by 3, and so on, `depth` times, with the literal
/// `(x div 3^i) mod 3 == i mod 3` on the remainder of each level, as the checker writes nested
/// quotients: one point modulo `3^depth`.
fn chain_of_quotients(depth: usize) -> (Vec<Div>, Formula) {
    let mut divs = Vec::new();
    let mut lits = Vec::new();
    for i in 0..depth {
        divs.push(Div {
            t: if i == 0 { 0 } else { i },
            a: 1,
            k: 0,
            m: 3,
            fixed: None,
        });
        lits.push(Formula::Con(Con::eq(&r(i), &Lin::constant((i % 3) as i64))));
    }
    let f = formula(&divs, Formula::and(lits), vec![]);
    (divs, f)
}

/// Runs `body` with [`sumset`] taken whatever the costs, and returns how many formulas it was
/// selected for ([`sumset::SELECTED`]) and how many it answered ([`sumset::ANSWERED`]).
fn with_sumset_always(body: impl FnOnce()) -> (usize, usize) {
    let counts = || {
        (
            sumset::SELECTED.with(std::cell::Cell::get),
            sumset::ANSWERED.with(std::cell::Cell::get),
        )
    };
    sumset::ALWAYS.with(|a| a.set(true));
    let before = counts();
    body();
    sumset::ALWAYS.with(|a| a.set(false));
    let after = counts();
    (after.0 - before.0, after.1 - before.1)
}

/// Rows over pairwise coprime moduli (two rows may share one, a block of two rows), sums of
/// their parts modulo powers of 2, top-level literals on the rows' remainders and any Boolean
/// combination of literals on the sums' remainders: the shape [`sumset`] decides, here taken
/// on every formula (`with_sumset_always`), against enumeration over one period of `x` (the
/// sums' lcm `M` times the rows' moduli: every remainder of a row and of a sum has a period
/// dividing it, the latter by [`sum_residues`]'s proof).
#[test]
fn sumset_decisions_match_enumeration() {
    let (mut rng, seed) = Rng::fresh("sumset_decisions_match_enumeration");
    crate::presburger::CHECK_LOSSLESS.with(|c| c.set(true));
    let mut answered = [0usize; 2];
    let mut taken = 0;
    for case in 0..300 {
        let mut moduli: Vec<i64> = vec![3, 5, 7, 11];
        rng.shuffle(&mut moduli);
        let mut divs: Vec<Div> = Vec::new();
        for &m in &moduli[..1 + rng.below(3)] {
            for _ in 0..1 + usize::from(rng.below(4) == 0) {
                let a = rng.int(1, 2 * m);
                let a = if rng.coin() { a } else { -a };
                let fixed = (rng.below(5) == 0).then(|| rng.int(0, m - 1));
                divs.push(Div {
                    t: 0,
                    a,
                    k: rng.int(-12, 12),
                    m,
                    fixed,
                });
            }
        }
        let sums: Vec<Sum> = random_sums(&mut rng, &divs)
            .into_iter()
            .map(|s| Sum {
                m: rng.pick(&[2, 4, 8]),
                ..s
            })
            .collect();
        // Literals on the rows' remainders at the top level only, as the path needs.
        let mut lits = vec![random_sum_literals(&mut rng, &divs, &sums, 2)];
        for (i, d) in divs.iter().enumerate() {
            if d.fixed.is_none() && rng.coin() {
                let c = Lin::constant(rng.int(0, d.m - 1));
                lits.push(Formula::Con(if rng.coin() {
                    Con::ge(&r(i), &c)
                } else {
                    Con::ge(&c, &r(i))
                }));
            }
        }
        let f = formula(&divs, Formula::and(lits), sum_formulas(&divs, &sums));
        let period: i64 = 8 * divs.iter().map(|d| d.m).product::<i64>();
        let want = (0..period).any(|v| point_sums(&divs, &sums, v).is_some_and(|m| f.holds(&m)));
        let what = format!("seed {seed} case {case} {divs:?} {sums:?}");
        // `solve` itself, then the entries above it ([`check`]).
        let (_, n) = with_sumset_always(|| {
            for want_model in [true, false] {
                if let Some(got) = solve(&f, want_model) {
                    assert_eq!(got.is_some(), want, "{what}: solve\n{f}");
                    if let Some(m) = got.filter(|_| want_model) {
                        assert!(f.holds(&m), "{what}: point {m:?} of\n{f}");
                    }
                }
            }
            check(&f, want, &what);
        });
        taken += usize::from(n > 0);
        answered[usize::from(want)] += 1;
    }
    // The path declines only where `solve` declines before it (a reading `orient` or
    // [`read_sum`] refuses), which these shapes rarely meet.
    assert!(
        answered[0] > 30 && answered[1] > 30 && taken > 250,
        "seed {seed}: answers {answered:?}, taken in {taken} of 300 cases"
    );
}

/// The path's scope: moduli that share a factor, a literal on `x`, and a literal on a row's
/// remainder under a disjunction are left to the other paths, which give the enumerated answer.
#[test]
fn the_sumset_path_takes_the_coprime_sums() {
    let row = |a, m| Div {
        t: 0,
        a,
        k: 0,
        m,
        fixed: None,
    };
    let sum = Sum {
        parts: vec![(1, 1), (3, 1)],
        k: 0,
        m: 2,
        rem: true,
    };
    let even = Formula::Con(Con::eq(&r(2), &Lin::constant(0)));
    let cases: Vec<(&str, Vec<Div>, Formula, bool)> = vec![
        ("coprime", vec![row(1, 3), row(1, 5)], even.clone(), true),
        (
            "a sum modulus shares 3",
            vec![row(1, 3), row(1, 5)],
            even.clone(),
            false,
        ),
        (
            "rows share 3",
            vec![row(1, 3), row(1, 9)],
            even.clone(),
            false,
        ),
        (
            "a literal on x",
            vec![row(1, 3), row(1, 5)],
            Formula::and(vec![
                even.clone(),
                Formula::Con(Con::ge(&x(), &Lin::constant(4))),
            ]),
            false,
        ),
        (
            "a nested row literal",
            vec![row(1, 3), row(1, 5)],
            Formula::or(vec![
                even.clone(),
                Formula::Con(Con::eq(&r(0), &Lin::constant(1))),
            ]),
            false,
        ),
    ];
    for (what, divs, lits, takes) in cases {
        let sums = vec![Sum {
            m: if what == "a sum modulus shares 3" {
                6
            } else {
                2
            },
            ..sum.clone()
        }];
        let f = formula(&divs, lits, sum_formulas(&divs, &sums));
        let period: i64 = 6 * divs.iter().map(|d| d.m).product::<i64>();
        let want = (0..period).any(|v| point_sums(&divs, &sums, v).is_some_and(|m| f.holds(&m)));
        let mut got = None;
        let (taken, _) = with_sumset_always(|| got = solve(&f, false).map(|m| m.is_some()));
        assert_eq!(taken > 0, takes, "{what}: taken {taken}\n{f}");
        assert!(
            got.is_none_or(|g| g == want),
            "{what}: {got:?}, want {want}\n{f}"
        );
        if takes {
            assert_eq!(got, Some(want), "{what}\n{f}");
        }
        let got = crate::presburger::decide(&f);
        assert!(
            got.is_err() || got == Ok(want),
            "{what}: {got:?}, want {want}\n{f}"
        );
    }
}

/// A sum whose remainder is a product atom `P = a * b` (META1 A1 of XR-presburger4, Codex's
/// example): `q_0 + q_1 == 2 q_2 + P` with `P == 1` has a point (`x = 3`, `a = b = 1`), but the
/// tuples of [`sumset`] give `P` a value only as an atom, and [`Formula::holds`] reads a product
/// through its factors, absent here, so it read `P` as 0 at every tuple and answered "no point".
/// The path must leave the formula to the others, and [`solve`] and
/// [`decide`](crate::presburger::decide) must find the point.
#[test]
fn sumset_leaves_a_product_remainder_to_the_fallback() {
    use crate::presburger::formula::Factor;

    let divs = [3, 5].map(|m| Div {
        t: 0,
        a: 1,
        k: 0,
        m,
        fixed: None,
    });
    let product = Lin::atom(Atom::Product(
        Factor::Sym("a".into()),
        Factor::Sym("b".into()),
    ));
    let f = formula(
        &divs,
        Formula::Con(Con::eq(&product, &Lin::constant(1))),
        vec![Formula::Con(Con::eq(
            &q(0).plus(&q(1)),
            &q(2).times(2).plus(&product),
        ))],
    );
    let mut witness = point(&divs, 3).expect("both divisions have a point");
    witness.insert(Atom::Sym("a".into()), Int::ONE);
    witness.insert(Atom::Sym("b".into()), Int::ONE);
    witness.insert(q_atom(2), Int::ZERO);
    assert!(f.holds(&witness));

    let (taken, _) = with_sumset_always(|| {
        for want_model in [false, true] {
            assert!(!matches!(solve(&f, want_model), Some(None)), "{f}");
        }
        assert!(
            !matches!(crate::presburger::decide(&f), Ok(false)),
            "decide\n{f}"
        );
    });
    assert_eq!(taken, 0, "{f}");
    assert!(
        !matches!(crate::presburger::decide(&f), Ok(false)),
        "decide\n{f}"
    );
}

/// The rows `x == p_i q_i + r_i` for the first `k` odd primes and one more row
/// `2 x == 3 q + r` (a block of two rows of modulus 3), and `j` sums `E + c`, `c` in `0..j`,
/// each modulo 2, `E` the sum of all the quotients, with the literals `(E + c) mod 2 == c mod 2`,
/// the last one flipped without `point`. The sums' tuples number `S = 2^j`, but only the two
/// tuples of `E mod 2` are reached (META1 A3 of XR-presburger4, Codex's 20 rows and 40 sums).
fn bench_many_sums(k: usize, j: usize, point: bool) -> (Vec<Div>, Vec<Sum>, Formula) {
    let mut divs: Vec<Div> = zed_numtheory::first_primes(k + 1)
        .into_iter()
        .skip(1)
        .map(|p| Div {
            t: 0,
            a: 1,
            k: 0,
            m: p as i64,
            fixed: None,
        })
        .collect();
    divs.push(Div {
        t: 0,
        a: 2,
        k: 0,
        m: 3,
        fixed: None,
    });
    let sums: Vec<Sum> = (0..j as i64)
        .map(|c| Sum {
            parts: (0..divs.len()).map(|i| (2 * i + 1, 1)).collect(),
            k: c,
            m: 2,
            rem: true,
        })
        .collect();
    let lits = (0..j)
        .map(|c| {
            let want = (c % 2) as i64;
            let want = if c + 1 == j && !point { 1 - want } else { want };
            Formula::Con(Con::eq(&r(divs.len() + c), &Lin::constant(want)))
        })
        .collect();
    let f = formula(&divs, Formula::and(lits), sum_formulas(&divs, &sums));
    (divs, sums, f)
}

/// META1 A3 of XR-presburger4: 20 rows and 40 sums modulo 2 have `2^40` tuples of the sums'
/// remainders, two of them reached. The path held a table of all `2^40` (16 TiB of slots), which
/// the allocator refused, and the formula went unanswered; it must hold only the tuples
/// reached ([`sumset::MOST_HELD`]) and answer, with the costs choosing the path as they do.
#[test]
fn sumset_holds_only_the_tuples_reached() {
    for point in [false, true] {
        let (_, _, f) = bench_many_sums(20, 40, point);
        sumset::MOST_HELD.with(|h| h.set(0));
        let before = sumset::ANSWERED.with(std::cell::Cell::get);
        for want_model in [false, true] {
            match solve_modular_or_scaled(&f, want_model) {
                Some(Some(m)) => assert!(point && (!want_model || f.holds(&m)), "{f}"),
                Some(None) => assert!(!point, "point {point}: no point found\n{f}"),
                None => panic!("point {point}: declined\n{f}"),
            }
        }
        assert_eq!(
            sumset::ANSWERED.with(std::cell::Cell::get) - before,
            2,
            "point {point}"
        );
        let most = sumset::MOST_HELD.with(std::cell::Cell::get);
        assert!(most <= 2, "point {point}: {most} tuples held at once");
    }
    // Small sizes against enumeration: `x` over one period, the sums' lcm 2 times the rows'.
    for (k, j) in [(2, 2), (2, 5), (3, 3)] {
        for point in [false, true] {
            let (divs, sums, f) = bench_many_sums(k, j, point);
            let period: i64 = 2 * divs.iter().map(|d| d.m).product::<i64>();
            let want =
                (0..period).any(|v| point_sums(&divs, &sums, v).is_some_and(|m| f.holds(&m)));
            assert_eq!(want, point, "k = {k}, j = {j}");
            check(&f, want, &format!("k = {k}, j = {j}, point {point}"));
        }
    }
}

/// The shapes [`sumset`] must also decide (META1 B6 of XR-presburger4), against enumeration and
/// taken on every formula in its scope: sum moduli that are not powers of 2 and need not divide
/// each other (2, 3, 4, 5, 9), sums with no remainder, several literals on one row's remainder,
/// a row whose `x` coefficient is a multiple of its modulus (`m / g = 1`, one remainder at
/// every `x`), and literals that leave a row no remainder (an empty block, whose `R + W_b` is
/// empty at once).
#[test]
fn sumset_shapes_match_enumeration() {
    let (mut rng, seed) = Rng::fresh("sumset_shapes_match_enumeration");
    crate::presburger::CHECK_LOSSLESS.with(|c| c.set(true));
    let mut answered = [0usize; 2];
    let (mut taken, mut empty_blocks, mut no_rem, mut whole) = (0, 0, 0, 0);
    for case in 0..200 {
        let mut moduli: Vec<i64> = vec![7, 11, 13];
        rng.shuffle(&mut moduli);
        let mut divs: Vec<Div> = Vec::new();
        for &m in &moduli[..1 + rng.below(2)] {
            for _ in 0..1 + usize::from(rng.below(4) == 0) {
                let a = if rng.below(6) == 0 {
                    m * rng.int(1, 2)
                } else {
                    rng.int(1, 2 * m)
                };
                divs.push(Div {
                    t: 0,
                    a: if rng.coin() { a } else { -a },
                    k: rng.int(-12, 12),
                    m,
                    fixed: None,
                });
            }
        }
        let sums: Vec<Sum> = random_sums(&mut rng, &divs)
            .into_iter()
            .map(|s| Sum {
                m: rng.pick(&[2, 3, 4, 5, 9]),
                ..s
            })
            .collect();
        let mut lits = vec![random_sum_literals(&mut rng, &divs, &sums, 2)];
        let mut empty = false;
        for (i, d) in divs.iter_mut().enumerate() {
            if rng.below(8) == 0 {
                // No remainder for the row's block: with `x`'s coefficient a multiple of `m` the
                // row has the one remainder `k mod m` at every `x`, and the literal leaves it
                // out. (Contradictory bounds on `r` never reach [`sumset`]: [`read_shape`] reads
                // no row whose remainder bounds are empty.) `random_sums` does not read `a`.
                d.a = d.m * if rng.coin() { 1 } else { -1 };
                let v = d.k.rem_euclid(d.m);
                lits.push(Formula::Con(if v > 0 {
                    Con::ge(&Lin::constant(v - 1), &r(i))
                } else {
                    Con::ge(&r(i), &Lin::constant(1))
                }));
                empty = true;
                continue;
            }
            for _ in 0..rng.below(3) {
                let c = Lin::constant(rng.int(0, d.m - 1));
                lits.push(Formula::Con(if rng.coin() {
                    Con::ge(&r(i), &c)
                } else {
                    Con::ge(&c, &r(i))
                }));
            }
        }
        let f = formula(&divs, Formula::and(lits), sum_formulas(&divs, &sums));
        let lcm = sums.iter().fold(1, |l, s| l / num_gcd(l, s.m) * s.m);
        let period: i64 = lcm * divs.iter().map(|d| d.m).product::<i64>();
        let want = (0..period).any(|v| point_sums(&divs, &sums, v).is_some_and(|m| f.holds(&m)));
        let what = format!("seed {seed} case {case} {divs:?} {sums:?}");
        let (_, n) = with_sumset_always(|| {
            for want_model in [true, false] {
                if let Some(got) = solve(&f, want_model) {
                    assert_eq!(got.is_some(), want, "{what}: solve\n{f}");
                    if let Some(m) = got.filter(|_| want_model) {
                        assert!(f.holds(&m), "{what}: point {m:?} of\n{f}");
                    }
                }
            }
            check(&f, want, &what);
        });
        if n > 0 {
            taken += 1;
            empty_blocks += usize::from(empty);
            no_rem += usize::from(sums.iter().any(|s| !s.rem));
            whole += usize::from(divs.iter().any(|d| d.a % d.m == 0));
        }
        answered[usize::from(want)] += 1;
    }
    assert!(
        answered[0] > 20
            && answered[1] > 20
            && taken > 120
            && empty_blocks > 5
            && no_rem > 5
            && whole > 5,
        "seed {seed}: answers {answered:?}, taken {taken}, empty blocks {empty_blocks}, \
         sums with no remainder {no_rem}, m / g = 1 {whole}"
    );
}

/// The rows `x == p_i q_i + r_i` for the first `k` odd primes, and the sums
/// `E = sum_i q_i` and `E + 1`, each modulo 2, with `E mod 2 == 0` and, with `point`,
/// `(E + 1) mod 2 == 1`, else `== 0`. Without `point` there is no point, so every reachable
/// tuple is visited. The residues of `x` that [`sum_residues`] writes number `2 prod_i p_i`,
/// exponential in `k`; [`sumset`] keeps 4 tuples, so its work is linear in `k`. From `k = 2`:
/// at `k = 1` each sum, `q_0 == 2 q + r`, reads as a row on the quotient of another row, a
/// chain, which [`solve`] declines before either path.
fn bench_coprime_sums(k: usize, point: bool) -> (Vec<Div>, Vec<Sum>, Formula) {
    let divs: Vec<Div> = zed_numtheory::first_primes(k + 1)
        .into_iter()
        .skip(1)
        .map(|p| Div {
            t: 0,
            a: 1,
            k: 0,
            m: p as i64,
            fixed: None,
        })
        .collect();
    let sums: Vec<Sum> = [0, 1]
        .into_iter()
        .map(|c| Sum {
            parts: (0..k).map(|i| (2 * i + 1, 1)).collect(),
            k: c,
            m: 2,
            rem: true,
        })
        .collect();
    let lits = Formula::and(vec![
        Formula::Con(Con::eq(&r(k), &Lin::constant(0))),
        Formula::Con(Con::eq(&r(k + 1), &Lin::constant(i64::from(point)))),
    ]);
    let f = formula(&divs, lits, sum_formulas(&divs, &sums));
    (divs, sums, f)
}

/// The small instances of `bench::sums_over_many_coprime_moduli_scale`, against enumeration,
/// with the costs choosing the path as they do in the benchmark.
#[test]
fn the_coprime_sums_benchmark_has_its_answers_at_small_sizes() {
    for k in 2..=5 {
        for point in [false, true] {
            let (divs, sums, f) = bench_coprime_sums(k, point);
            let period: i64 = 2 * divs.iter().map(|d| d.m).product::<i64>();
            let want =
                (0..period).any(|v| point_sums(&divs, &sums, v).is_some_and(|m| f.holds(&m)));
            assert_eq!(want, point, "k = {k}");
            check_answered(&f, want, &format!("k = {k}, point {point}"));
        }
    }
}

/// The rows of FAIL-omega-pairs-4972743790605253739: `x - s == m q + r` for `(m, s)` in
/// `(5, 0), (4, 2), (5, 5), (4, 7)`.
fn four_pairs() -> Vec<Div> {
    [(5, 0), (4, 2), (5, 5), (4, 7)]
        .into_iter()
        .map(|(m, s)| Div {
            t: 0,
            a: 1,
            k: -s,
            m,
            fixed: None,
        })
        .collect()
}

#[test]
fn four_pairs_with_a_sum_of_their_quotients_are_decided() {
    // `r3 + q2 + r1 + q0 >= 9`: the quotients grow with `x`, so a large `x` is a point, and the
    // general path refused it (`Growth`) before the sweep.
    let divs = four_pairs();
    let sum = r(3).plus(&q(2)).plus(&r(1)).plus(&q(0));
    let f = formula(
        &divs,
        Formula::Con(Con::ge(&sum, &Lin::constant(9))),
        vec![],
    );
    check_answered(&f, true, "the four pairs");
    // With `x <= 12`, `q0 <= 2` and `q2 <= 1`; `r1 = (x - 2) mod 4` and `r3 = (x - 7) mod 4`
    // differ by 1 modulo 4, so they are never both 3 and their sum is at most 5: the sum is at
    // most 8 (enumerated below as well).
    let bounded = formula(
        &divs,
        Formula::Con(Con::ge(&sum, &Lin::constant(9))),
        vec![Formula::Con(Con::ge(&Lin::constant(12), &x()))],
    );
    let want = has_point(&bounded, &divs, -200..=12);
    assert!(!want, "the bounded rows have a point");
    check_answered(&bounded, false, "the four pairs with x <= 12");
    // Unbounded and empty: `(x + 4) div 4 - x div 4` is 1 at every `x`.
    let same = vec![
        Div {
            t: 0,
            a: 1,
            k: 0,
            m: 4,
            fixed: None,
        },
        Div {
            t: 0,
            a: 1,
            k: 4,
            m: 4,
            fixed: None,
        },
    ];
    let apart = formula(
        &same,
        Formula::Con(Con::ge(&q(1), &q(0).plus(&Lin::constant(2)))),
        vec![],
    );
    check_answered(&apart, false, "two quotients one apart");
}

/// `x = p q_i + r_i` for each `p` of `primes`, as rows.
fn prime_rows(primes: &[i64]) -> Vec<Div> {
    primes
        .iter()
        .map(|&m| Div {
            t: 0,
            a: 1,
            k: 0,
            m,
            fixed: None,
        })
        .collect()
}

/// The rows of 101, 103 and 107 with `q0 + q1 + q2 == c` and `extra`.
fn sum_past_the_old_bound(c: i64, extra: Vec<Formula>) -> (Vec<Div>, Formula) {
    let divs = prime_rows(&[101, 103, 107]);
    let sum = q(0).plus(&q(1)).plus(&q(2));
    let mut lits = vec![Formula::Con(Con::eq(&sum, &Lin::constant(c)))];
    lits.extend(extra);
    let f = formula(&divs, Formula::and(lits), vec![]);
    (divs, f)
}

/// [`sum_past_the_old_bound`] at `c = 30,000` with `n` constraints `i r0 >= i` for `i` in
/// `1..=n` (each `r0 >= 1`, written apart so that each is its own part) and `not (r0 >= 1)`: no
/// point. The period of the rows is 1,113,121, past what the residue sweep runs; the runs
/// (Lemma E of `sweep.rs`) are the window of the sum and 101 points on each side of it, the same
/// at every `n`, each folding the formula's `n + 13` or so parts. The benchmark
/// `bench::the_runs_scale_in_the_constraints`.
fn bench_runs(n: usize) -> Formula {
    let ge_one = |i: i64| Formula::Con(Con::ge(&r(0).times(i), &Lin::constant(i)));
    let mut extra: Vec<Formula> = (1..=n as i64).map(ge_one).collect();
    extra.push(Formula::negate(ge_one(1)));
    sum_past_the_old_bound(30_000, extra).1
}

/// PRES-period-sweep-no-budget: the moduli 101, 103 and 107 have the period
/// `L = 1,113,121`, so the residue sweep (`sweep.rs`, Lemma C) counts `L` times the constraints,
/// past `PERIOD_SWEEP_SWITCHOVER`, and declined; the sum of quotients reads the moduli only
/// through `x`'s size, so the runs (Lemma E) test one window near `x = 1,024,000` (the sum grows
/// by about `x / 34.3`) and, with `r0 != 5`, the 101 points on each side. Every `x` off the
/// window has a sum other than `c`, so enumerating `[1,000,000, 1,050,000]` decides each case.
#[test]
fn a_sum_of_quotients_past_the_old_bound_is_decided() {
    let not_five = || Formula::negate(Formula::Con(Con::eq(&r(0), &Lin::constant(5))));
    for (c, extra) in [
        (30_000, vec![]),
        (30_001, vec![not_five()]),
        // `r0 == 5` with the sum fixed, under a disjunction so that it is not read as a bound
        // of the row; `x <= -5` gives the sum no value `c` there.
        (
            30_000,
            vec![Formula::or(vec![
                Formula::Con(Con::eq(&r(0), &Lin::constant(5))),
                Formula::Con(Con::ge(&Lin::constant(-5), &x())),
            ])],
        ),
    ] {
        let (divs, f) = sum_past_the_old_bound(c, extra);
        assert_eq!(
            sweep::solve_by(
                &f,
                false,
                sweep::Method::Residues,
                sweep::PERIOD_SWEEP_SWITCHOVER
            ),
            None,
            "the residue sweep is past the switchover\n{f}"
        );
        let want = has_point(&f, &divs, 1_000_000..=1_050_000);
        match sweep::solve(&f, true) {
            Some(Some(m)) => assert!(want && f.holds(&m), "point {m:?} of\n{f}"),
            Some(None) => assert!(!want, "no point found, but one exists, in\n{f}"),
            None => panic!("declined\n{f}"),
        }
        assert_eq!(sweep::solve(&f, false).map(|m| m.is_some()), Some(want));
    }
}

/// The two exact methods of `sweep.rs`, the residue sweep (Lemma C) and the runs (Lemma E),
/// give the same answer on random formulas of [`random_part_literals`] over up to four rows
/// with moduli up to 30, where both answer; each model is a point. Catches a window or a
/// period `L_P` too narrow (the runs miss a point the sweep finds) and a wrong value at a
/// point; cannot catch an error both methods share (`point_at`, the shape), which
/// `quotients_beside_the_variable_match_enumeration` checks against enumeration.
#[test]
fn the_runs_agree_with_the_residue_sweep() {
    let (mut rng, seed) = Rng::fresh("the_runs_agree_with_the_residue_sweep");
    let mut both = [0usize; 2];
    for case in 0..1500 {
        let mut divs = random_divs(&mut rng);
        while case % 3 == 0 && divs.len() < 4 {
            divs.extend(random_divs(&mut rng));
        }
        divs.truncate(4);
        for d in &mut divs {
            if rng.coin() {
                d.m = rng.int(10, 30);
                d.fixed = d.fixed.map(|c| c % d.m);
            }
        }
        let lits = random_part_literals(&mut rng, &divs, 3);
        let f = formula(&divs, lits, vec![]);
        // 400,000 units, the bound this test ran under before PRES-period-sweep-no-budget, so
        // each method answers about as often as it did.
        let runs = sweep::solve_by(&f, true, sweep::Method::Runs, 400_000);
        let swept = sweep::solve_by(&f, true, sweep::Method::Residues, 400_000);
        for m in [&runs, &swept].into_iter().flatten().flatten() {
            assert!(
                f.holds(m),
                "seed {seed} case {case}: not a point {m:?}\n{f}"
            );
        }
        if let (Some(a), Some(b)) = (&runs, &swept) {
            assert_eq!(a.is_some(), b.is_some(), "seed {seed} case {case}\n{f}");
            both[usize::from(a.is_some())] += 1;
        }
    }
    eprintln!("seed {seed}: both methods answered {both:?} (empty, with a point)");
    assert!(both[0] > 50 && both[1] > 50, "{both:?}");
}

/// A random Boolean combination of constraints on sums of `x` and the quotients and
/// remainders of `divs`, with coefficients in `[-3, 3]`.
fn random_part_literals(rng: &mut Rng, divs: &[Div], depth: u32) -> Formula {
    if depth == 0 || rng.below(3) == 0 {
        let mut parts: Vec<Lin> = vec![x()];
        for (i, d) in divs.iter().enumerate() {
            parts.push(q(i));
            if d.fixed.is_none() {
                parts.push(r(i));
            }
        }
        let mut sum = Lin::constant(0);
        for _ in 0..1 + rng.below(3) {
            let p = rng.pick(&parts);
            sum = sum.plus(&p.times(rng.int(-3, 3)));
        }
        let c = Lin::constant(rng.int(-20, 20));
        return Formula::Con(if rng.below(5) == 0 {
            Con::eq(&sum, &c)
        } else {
            Con::ge(&sum, &c)
        });
    }
    let kids = (0..2 + rng.below(2))
        .map(|_| random_part_literals(rng, divs, depth - 1))
        .collect();
    match rng.below(3) {
        0 => Formula::and(kids),
        1 => Formula::or(kids),
        _ => Formula::negate(Formula::and(kids)),
    }
}

/// Random formulas of [`random_part_literals`] with `x` unbounded, on up to four rows: where the
/// module and [`decide`](crate::presburger::decide) both answer, they agree (enumeration cannot
/// check an unbounded `x`). The counts are printed: on seed 16937151135935670534 at 2cf833851,
/// `decide` refused 7 of 3000 and the module declined 2394 before the period sweep (`sweep.rs`),
/// and 0 and 100 with it.
#[test]
fn unbounded_quotient_formulas_agree_with_decide() {
    let (mut rng, seed) = Rng::fresh("unbounded_quotient_formulas_agree_with_decide");
    let mut refused = 0;
    let mut declined = 0;
    let n = 3000;
    for case in 0..n {
        let mut divs = random_divs(&mut rng);
        while case % 2 == 0 && divs.len() < 4 {
            divs.extend(random_divs(&mut rng));
        }
        divs.truncate(4);
        let lits = random_part_literals(&mut rng, &divs, 3);
        let f = formula(&divs, lits, vec![]);
        let by_module = sweep::solve_modular_scaled_or_swept(&f, true);
        if let Some(Some(model)) = &by_module {
            assert!(f.holds(model), "seed {seed} case {case}: not a point\n{f}");
        }
        let by_decide = crate::presburger::decide(&f);
        declined += usize::from(by_module.is_none());
        refused += usize::from(by_decide.is_err());
        if let (Some(m), Ok(want)) = (by_module, by_decide) {
            assert_eq!(m.is_some(), want, "seed {seed} case {case}\n{f}");
        }
    }
    eprintln!("seed {seed}: decide refused {refused}, the module declined {declined}, of {n}");
}

#[test]
fn quotients_beside_the_variable_match_enumeration() {
    // `x` is bounded to a window, so enumerating the window decides each formula.
    let (mut rng, seed) = Rng::fresh("quotients_beside_the_variable_match_enumeration");
    crate::presburger::CHECK_LOSSLESS.with(|c| c.set(true));
    let mut answered = [0usize; 2];
    let mut by_solve = [0usize; 2];
    for case in 0..300 {
        let divs = random_divs(&mut rng);
        let lits = random_part_literals(&mut rng, &divs, 2);
        let lo = rng.int(-60, 60);
        let hi = lo + rng.int(0, 80);
        let extra = vec![
            Formula::Con(Con::ge(&x(), &Lin::constant(lo))),
            Formula::Con(Con::ge(&Lin::constant(hi), &x())),
        ];
        let f = formula(&divs, lits, extra);
        let want = has_point(&f, &divs, lo..=hi);
        let by_module = check(&f, want, &format!("seed {seed} case {case} {divs:?}"));
        answered[usize::from(want)] += 1;
        by_solve[usize::from(want)] += usize::from(by_module);
    }
    // Both answers are met, and the module answers each side often, so neither is checked
    // vacuously and a module that declined everything would not pass on `decide` alone.
    assert!(answered[0] > 30 && answered[1] > 30, "{answered:?}");
    assert!(by_solve[0] > 30 && by_solve[1] > 30, "{by_solve:?}");
}

/// A random formula of [`random_part_literals`] over one to four rows, each modulus with even
/// odds a prime from 11 to 113, and with even odds a sum of the quotients equal to or at least
/// 1,000 to 1,000,000: the formulas of the measurement of `sweep::PERIOD_SWEEP_SWITCHOVER`,
/// whose periods and windows put the period sweep's count of units from a few hundred to past
/// 10^7.
fn prime_part_formula(rng: &mut Rng) -> Formula {
    let primes = [
        11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101,
        103, 107, 109, 113,
    ];
    let k = 1 + rng.below(4);
    let mut divs = random_divs(rng);
    while divs.len() < k {
        divs.extend(random_divs(rng));
    }
    divs.truncate(k);
    for d in &mut divs {
        if rng.coin() {
            d.m = rng.pick(&primes);
            d.fixed = d.fixed.map(|c| c % d.m);
        }
    }
    let mut extra = Vec::new();
    if rng.coin() {
        let mut sum = Lin::constant(0);
        for i in 0..divs.len() {
            sum = sum.plus(&q(i).times(rng.int(1, 3)));
        }
        let c = Lin::constant(rng.int(1_000, 1_000_000));
        extra.push(Formula::Con(if rng.coin() {
            Con::eq(&sum, &c)
        } else {
            Con::ge(&sum, &c)
        }));
    }
    let lits = random_part_literals(rng, &divs, 3);
    formula(&divs, lits, extra)
}

/// PRES-period-sweep-no-budget: a formula past `PERIOD_SWEEP_SWITCHOVER` that the general path
/// refuses is answered by the sweep after the refusal (`presburger::swept_after_refusal`), by
/// [`decide`](crate::presburger::decide) and by `satisfiable`, with the sweep's answer. Formulas
/// of [`prime_part_formula`] that the sweep declines at its switchover and `decide` refuses with
/// the sweep after a refusal switched off (`presburger::NO_SWEEP_AFTER_REFUSAL`): about one in
/// 15 of those with 32,768 to 500,000 units in the measurement (red at b22-presburger8 with only
/// that sweep left out). The sweep is bounded here by 500,000 units, so the test stays short;
/// `decide`'s own bound is `PERIOD_SWEEP_AFTER_REFUSAL_UNITS`.
#[test]
fn a_formula_the_general_path_refuses_is_swept_past_the_switchover() {
    let (mut rng, seed) =
        Rng::fresh("a_formula_the_general_path_refuses_is_swept_past_the_switchover");
    let mut found = 0;
    let mut tried = 0;
    while found < 3 && tried < 400 {
        let f = prime_part_formula(&mut rng);
        if solve_modular_or_scaled(&f, false).is_some() || sweep::solve(&f, false).is_some() {
            continue;
        }
        tried += 1;
        let refused = {
            let _off = crate::presburger::SetFor::new(&crate::presburger::NO_SWEEP_AFTER_REFUSAL);
            crate::presburger::decide(&f).is_err()
        };
        if !refused {
            continue;
        }
        let Some(want) = sweep::solve_by(&f, false, sweep::Method::Cheaper, 500_000) else {
            continue;
        };
        found += 1;
        let want = want.is_some();
        match crate::presburger::decide(&f) {
            Ok(b) => assert_eq!(b, want, "seed {seed}\n{f}"),
            Err(e) => panic!("seed {seed}: refused ({e:?}), the sweep gives {want}\n{f}"),
        }
        match crate::presburger::satisfiable(&f) {
            Ok(Some(m)) => assert!(want && f.holds(&m), "seed {seed}: point {m:?} of\n{f}"),
            Ok(None) => assert!(
                !want,
                "seed {seed}: no point found, the sweep finds one\n{f}"
            ),
            Err(e) => panic!("seed {seed}: refused ({e:?}), the sweep gives {want}\n{f}"),
        }
    }
    eprintln!("seed {seed}: {found} refused formulas swept, of {tried} past the switchover");
    assert!(found > 0, "seed {seed}: no formula refused of {tried}");
}

/// PRES-period-sweep-no-budget: no formula that 60267344b answered by its sweep (the residue
/// sweep, first, up to 400,000 units) is refused now, though the sweep now runs first only up to
/// `PERIOD_SWEEP_SWITCHOVER`: [`decide`](crate::presburger::decide) and `satisfiable` answer
/// each such formula of [`prime_part_formula`] past the switchover, with the residue sweep's
/// answer. Formulas 60267344b sent to the general path are sent there now too. Catches a sweep
/// after a refusal that is missing or bounded below 400,000 units.
#[test]
fn what_the_old_switchover_swept_is_answered() {
    let (mut rng, seed) = Rng::fresh("what_the_old_switchover_swept_is_answered");
    let mut checked = 0;
    let mut tried = 0;
    while checked < 30 && tried < 3000 {
        tried += 1;
        let f = prime_part_formula(&mut rng);
        if solve_modular_or_scaled(&f, false).is_some() || sweep::solve(&f, false).is_some() {
            continue;
        }
        let Some(want) = sweep::solve_by(&f, false, sweep::Method::Residues, 400_000) else {
            continue;
        };
        checked += 1;
        let want = want.is_some();
        match crate::presburger::decide(&f) {
            Ok(b) => assert_eq!(b, want, "seed {seed}\n{f}"),
            Err(e) => panic!("seed {seed}: refused ({e:?}), the old sweep gives {want}\n{f}"),
        }
        match crate::presburger::satisfiable(&f) {
            Ok(Some(m)) => assert!(want && f.holds(&m), "seed {seed}: point {m:?} of\n{f}"),
            Ok(None) => assert!(
                !want,
                "seed {seed}: no point found, the old sweep finds one\n{f}"
            ),
            Err(e) => panic!("seed {seed}: refused ({e:?}), the old sweep gives {want}\n{f}"),
        }
    }
    eprintln!("seed {seed}: {checked} formulas the old switchover swept, of {tried}");
    assert!(checked >= 10, "seed {seed}: {checked} of {tried}");
}
