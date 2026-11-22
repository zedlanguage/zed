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
/// give `want`, and so must [`solve_modular_or_scaled`] with and without a model when it
/// answers; a model must be a point of `f`. Returns whether [`solve_modular_or_scaled`]
/// answered. It may decline a formula whose remainders, once rewritten, are of `x` alone:
/// [`solve_modular_whole`] declines some of those, written so from the start, before and after
/// this row (seed 7293238915329919861 case 40, `x mod 2`, `x mod 4` and `x mod 9` under a
/// negation), and the general path decides them.
fn check(f: &Formula, want: bool, what: &str) -> bool {
    assert_eq!(
        crate::presburger::decide(f),
        Ok(want),
        "{what}: decide\n{f}"
    );
    match solve_modular_or_scaled(f, true) {
        Some(Some(m)) => assert!(want && f.holds(&m), "{what}: point {m:?} of\n{f}"),
        Some(None) => assert!(!want, "{what}: no point found, but one exists, in\n{f}"),
        None => return false,
    }
    assert_eq!(
        solve_modular_or_scaled(f, false).map(|m| m.is_some()),
        Some(want),
        "{what} without a model\n{f}"
    );
    true
}

/// [`check`], and [`solve_modular_or_scaled`] must answer.
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
    for (what, f) in [
        ("two variables", two_vars),
        ("a quotient read by a bound", quotient_bound),
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
            // A multiple of the modulus (`(-5 x - 5) mod 5`) normalizes to `x + q == -1`, no
            // row, so `solve` declines and the general path refuses the sum over it (seed
            // 3730609663341733710 case 223, `Shadows`); row PRES-sum-of-quotients-period-product
            // records it.
            .filter(|d| d.a % d.m != 0)
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
