//! The checks of the study of exact integer sets, round 1 (plan rows SETS-study and
//! XSETS-unified-tests; docs/studies/exact-sets.md), ported from the node scripts of its
//! meta-review, /home/luke/Work/wt/xsets: `alg.js` (STUDY1's rules), `meta1/claims.js` (the
//! reviewers' claims), `meta1/algebra.js` (results J and K of META1.md section 6) and
//! `meta1/study2_examples.js` (STUDY2 section 3). Each test checks a claim on its range and
//! holds a negative control, a wrong variant of the claim that the same check must reject, so
//! that the check is known to be able to fail. Where zed-impl has the routine the claim is
//! about, the test checks that routine too: the affine preimage of check 10 against
//! `Int::solve_linear_congruence`.
//!
//! The random checks draw a new seed each run ([`Rng::fresh`], printed; `ZED_TEST_SEED`
//! repeats it), with as many cases as the scripts ran: each case is a few hundred operations
//! on small integers, so every test runs in well under a second.
//!
//! Not ported: the reviewers' Python scripts, which the meta-review did not run either (its
//! section 1: their claims are re-checked in node where they matter, and those checks are
//! here), and its re-runs of the reviewers' Rust prototypes, which live outside zed-impl.

use std::collections::BTreeSet;
use zed_tests::seed::Rng;
use zedc_int::int::Int;

fn gcd(a: i64, b: i64) -> i64 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// `n!`.
fn fact(k: i64) -> i64 {
    (1..=k).product()
}

/// `x^2 mod m` for each `x` in `0..m` as a set.
fn squares_mod(m: i64) -> BTreeSet<i64> {
    (0..m).map(|x| x * x % m).collect()
}

// ---- meta1/claims.js ----

/// claims.js check 1: the Stockmeyer and Meyer predicate for `(x1 | !x2 | x3) & (!x1 | x2 |
/// !x3)`, `z mod 2 <= 1 && z mod 3 <= 1 && z mod 5 <= 1` with the residues `excl` mod 30 left
/// out, agrees with the formula at every `z` below 30.
fn sm_agrees(excl: &[i64]) -> bool {
    let cnf: [[i64; 3]; 2] = [[1, -2, 3], [-1, 2, -3]];
    let p = |z: i64| z % 2 <= 1 && z % 3 <= 1 && z % 5 <= 1 && excl.iter().all(|e| z % 30 != *e);
    (0..30).all(|z| {
        if z % 3 > 1 || z % 5 > 1 {
            return !p(z);
        }
        let a = [0, z % 2, z % 3, z % 5];
        let sat = cnf.iter().all(|c| {
            c.iter().any(|&l| {
                if l > 0 {
                    a[l as usize] == 1
                } else {
                    a[(-l) as usize] == 0
                }
            })
        });
        sat == p(z)
    })
}

#[test]
fn the_stockmeyer_meyer_residues_encode_two_clauses() {
    assert!(sm_agrees(&[10, 21]));
    // Controls: a wrong code for the first clause, and the second clause dropped.
    assert!(!sm_agrees(&[11, 21]));
    assert!(!sm_agrees(&[10]));
}

/// The least `x >= 0` with `x == rs[i] (mod ms[i])` for each `i`, the moduli coprime.
fn crt(rs: &[i64], ms: &[i64]) -> i64 {
    let (mut x, mut m) = (0i64, 1i64);
    for (r, mi) in rs.iter().zip(ms) {
        while x.rem_euclid(*mi) != *r {
            x += m;
        }
        m *= mi;
    }
    x
}

/// claims.js check 1b: a random 3-CNF formula on `n <= 5` variables, variable `i` read as `z
/// mod p_i` for the first `n` primes, each clause excluding one residue modulo the product of
/// its three primes; at every `z` whose residues are 0 or 1 (an assignment), the encoding
/// accepts `z` exactly when the assignment satisfies the formula. With `flip`, the first
/// clause's residue is that of the flipped polarity (the control).
fn sm_general(rng: &mut Rng, trials: usize, flip: bool) -> bool {
    const PR: [i64; 5] = [2, 3, 5, 7, 11];
    for _ in 0..trials {
        let n = rng.int(3, 5) as usize;
        let m = rng.int(1, 8) as usize;
        let cnf: Vec<Vec<i64>> = (0..m)
            .map(|_| {
                let mut vs: Vec<i64> = (0..n as i64).collect();
                for i in 0..3 {
                    let j = i + rng.below(n - i);
                    vs.swap(i, j);
                }
                vs[..3]
                    .iter()
                    .map(|v| if rng.coin() { v + 1 } else { -(v + 1) })
                    .collect()
            })
            .collect();
        let prime = |l: i64| PR[(l.unsigned_abs() - 1) as usize];
        let ex: Vec<(i64, i64)> = cnf
            .iter()
            .enumerate()
            .map(|(i, c)| {
                let ms: Vec<i64> = c.iter().map(|&l| prime(l)).collect();
                let rs: Vec<i64> = c
                    .iter()
                    .map(|&l| if (l > 0) != (flip && i == 0) { 0 } else { 1 })
                    .collect();
                (crt(&rs, &ms), ms.iter().product())
            })
            .collect();
        let l: i64 = PR[..n].iter().product();
        for z in 0..l {
            if !PR[..n].iter().all(|p| z % p <= 1) {
                continue;
            }
            let sat = cnf
                .iter()
                .all(|c| c.iter().any(|&l| z % prime(l) == i64::from(l > 0)));
            if sat != ex.iter().all(|(r, m)| z % m != *r) {
                return false;
            }
        }
    }
    true
}

#[test]
fn the_stockmeyer_meyer_encoding_of_random_3_cnf_agrees_at_every_assignment() {
    let (mut rng, _) = Rng::fresh("exact sets: Stockmeyer-Meyer encoding of random 3-CNF");
    assert!(sm_general(&mut rng, 400, false));
    // Control: the first clause excluded with flipped polarity. Compared at every assignment,
    // not by satisfiability, which a dropped clause almost never changes (META1 section 1).
    assert!(!sm_general(&mut rng, 400, true));
}

fn pairwise_coprime(k: i64, f: impl Fn(i64, i64) -> i64) -> bool {
    (1..=k).all(|i| (i + 1..=k).all(|j| gcd(f(i, k), f(j, k)) == 1))
}

/// claims.js check 2, Codex: the moduli `m_i = 1 + i k!` for `i` in `1..=k` are pairwise
/// coprime (a common prime divides `j - i`, hence `k!`, against `m_i == 1 (mod k!)`).
#[test]
fn moduli_one_plus_i_times_k_factorial_are_pairwise_coprime() {
    assert!((2..=9).all(|k| pairwise_coprime(k, |i, k| 1 + i * fact(k))));
    // Control: `1 + i k` in place of `k!`.
    assert!(!(2..=9).all(|k| pairwise_coprime(k, |i, k| 1 + i * k)));
}

/// claims.js check 3: `f(x, a, b)` lies in `[c_lo..<b]` for every `x` in `[0..=g]` exactly
/// when `x^2 - a` has no root mod `b` there.
fn contain_reduction(f: impl Fn(i64, i64, i64) -> i64, c_lo: i64) -> bool {
    for b in 2..=40 {
        for a in 0..b {
            for g in [0i64, 3, 7, 20, 60] {
                let root = (0..=g).any(|x| (x * x - a).rem_euclid(b) == 0);
                let contained = (0..=g).all(|x| (c_lo..b).contains(&f(x, a, b)));
                if contained == root {
                    return false;
                }
            }
        }
    }
    true
}

#[test]
fn containment_in_one_to_b_reduces_from_a_quadratic_root() {
    // Codex: `(x^2 - a) mod b` in `[1..<b]`; control `[0..<b]`.
    assert!(contain_reduction(|x, a, b| (x * x - a).rem_euclid(b), 1));
    assert!(!contain_reduction(|x, a, b| (x * x - a).rem_euclid(b), 0));
    // Claude: `(x^2 + (b - a)) mod b` in `[1..<b]`; control `x^2 + a`.
    assert!(contain_reduction(
        |x, a, b| (x * x + (b - a)).rem_euclid(b),
        1
    ));
    assert!(!contain_reduction(|x, a, b| (x * x + a).rem_euclid(b), 1));
}

/// claims.js check 4: `x * x mod 4 == x mod 2` on `[0..=255]`; control mod 8.
#[test]
fn a_square_mod_4_is_the_number_mod_2() {
    let holds = |m: i64| (0..256).all(|x| x * x % m == x % 2);
    assert!(holds(4));
    assert!(!holds(8));
}

/// claims.js check 5 and study2 R6: on `[0..=18]`, `x * x mod 10 == 9` exactly at
/// `{3, 7, 13, 17}`; control `== 4`.
#[test]
fn the_ranged_arm_is_3_7_13_17() {
    let arm = |m: i64, t: i64| -> Vec<i64> { (0..19).filter(|x| x * x % m == t).collect() };
    assert_eq!(arm(10, 9), [3, 7, 13, 17]);
    assert_ne!(arm(10, 4), [3, 7, 13, 17]);
}

/// claims.js check 6, Gemini: the image of `x^2 mod 2^k` is `{0}` and, for each `v` with
/// `2v < k`, the class `4^v mod 2^min(k, 2v + extra)`, `extra` = 3.
fn two_adic_formula(k: u32, extra: u32) -> BTreeSet<i64> {
    let m = 1i64 << k;
    let mut s = BTreeSet::from([0]);
    let mut v = 0;
    while 2 * v < k {
        let q = 1i64 << k.min(2 * v + extra);
        let mut y = (1i64 << (2 * v)) % q;
        while y < m {
            s.insert(y);
            y += q;
        }
        v += 1;
    }
    s
}

#[test]
fn the_image_of_a_square_mod_a_power_of_two_is_gemini_s_formula() {
    assert!((1..=16).all(|k| squares_mod(1 << k) == two_adic_formula(k, 3)));
    // Control: `2v + 2` in place of `2v + 3`.
    assert!(!(1..=16).all(|k| squares_mod(1 << k) == two_adic_formula(k, 2)));
}

/// Whether the classes `(m, r)` cover every integer: every `x` below the moduli's lcm, 12
/// for the systems here, lies in one.
fn covers(sys: &[(i64, i64)]) -> bool {
    (0..12).all(|x| sys.iter().any(|(m, r)| x % m == *r))
}

/// claims.js check 7: Erdős's covering system `(2, 0), (3, 0), (4, 1), (6, 5), (12, 7)`.
#[test]
fn erdos_s_system_covers_the_integers() {
    let erdos = [(2, 0), (3, 0), (4, 1), (6, 5), (12, 7)];
    assert!(covers(&erdos));
    assert!(!covers(&erdos[..4]));
}

/// The longest progression inside the complement of `0 mod p` in `[0..<p^2)`.
fn longest_progression(p: i64) -> i64 {
    let (n, inside) = (p * p, |x: i64| x % p != 0);
    let mut best = 0;
    for s in (0..n).filter(|s| inside(*s)) {
        for d in 1..n {
            let len = (0..)
                .map(|i| s + i * d)
                .take_while(|x| *x < n && inside(*x))
                .count();
            best = best.max(len as i64);
        }
    }
    best
}

/// claims.js check 8, Codex: the longest progression inside the complement of `0 mod p` in
/// `[0..<p^2)` has exactly `p` terms, so the complement needs at least `p - 1` progressions.
#[test]
fn the_complement_of_a_class_holds_no_progression_longer_than_p() {
    let lens: Vec<i64> = [3, 5, 7, 11].map(longest_progression).to_vec();
    assert_eq!(lens, [3, 5, 7, 11]);
    // Control: the claim "at most p - 1".
    assert!(!lens.iter().zip([3, 5, 7, 11]).all(|(l, p)| *l < p));
}

fn roots_of_one(m: i64) -> usize {
    (0..m).filter(|x| x * x % m == 1 % m).count()
}

/// claims.js check 9, Codex: `x^2 == 1` has `2^t` roots modulo a product of `t` distinct odd
/// primes; control: with the prime 2 among them.
#[test]
fn one_has_two_to_the_t_square_roots_mod_t_odd_primes() {
    let odd = [3i64, 5, 7, 11, 13];
    assert!((1..=4).all(|t| roots_of_one(odd[..t].iter().product()) == 1 << t));
    assert!(!(1..=4).all(|t| roots_of_one(2 * odd[..t - 1].iter().product::<i64>()) == 1 << t));
}

/// `x` in `0..m` with `a x + b == r (mod m)`.
fn affine_brute(a: i64, b: i64, r: i64, m: i64) -> Vec<i64> {
    (0..m).filter(|x| (a * x + b).rem_euclid(m) == r).collect()
}

/// The class `(r', m / g)`, `g = gcd(a, m)`, of the solutions of `a x + b == r (mod m)`, or
/// none; with `bug`, the division by `g` of `r - b` forgotten (the control).
fn affine_rule(a: i64, b: i64, r: i64, m: i64, bug: bool) -> Option<(i64, i64)> {
    let (g, c) = (gcd(a, m), (r - b).rem_euclid(m));
    if c % g != 0 {
        return None;
    }
    let m2 = m / g;
    let inv = (0..m2).find(|i| ((a / g).rem_euclid(m2) * i) % m2 == 1 % m2)?;
    let c = if bug { c } else { c / g };
    Some(((c * inv).rem_euclid(m2), m2))
}

fn members(class: Option<(i64, i64)>, m: i64) -> Vec<i64> {
    class.map_or(vec![], |(r, q)| (0..m).filter(|x| x % q == r).collect())
}

/// claims.js check 10, Codex: the affine preimage `{x : a x + b == r (mod m)}` is empty or one
/// class mod `m / gcd(a, m)`; and zed-impl's `Int::solve_linear_congruence`, which solves
/// `a t == r - b (mod m)`, gives that class.
#[test]
fn an_affine_preimage_is_one_class_by_the_gcd() {
    let (mut rng, seed) = Rng::fresh("exact sets: affine preimages by the gcd");
    let mut control_caught = false;
    for _ in 0..20000 {
        let m = rng.int(1, 60);
        let (a, b, r) = (rng.int(-60, 60), rng.int(-60, 60), rng.int(0, m - 1));
        let brute = affine_brute(a, b, r, m);
        assert_eq!(
            members(affine_rule(a, b, r, m, false), m),
            brute,
            "seed {seed}"
        );
        control_caught |= members(affine_rule(a, b, r, m, true), m) != brute;
        let solved = Int::from(a).solve_linear_congruence(&Int::from(r - b), &Int::from(m));
        let small = |x: Int| x.to_string().parse::<i64>().expect("below m");
        let class = solved.map(|(t, p)| (small(t), small(p)));
        assert_eq!(
            members(class, m),
            brute,
            "seed {seed}: {a} x + {b} == {r} mod {m}"
        );
    }
    assert!(
        control_caught,
        "seed {seed}: the rule without the division by g was not caught"
    );
}

/// The states of the least automaton that reads a number's bits from the top and accepts the
/// multiples of `m`, by partition refinement of the residues mod `m`.
fn min_dfa(m: usize) -> usize {
    let mut cls: Vec<usize> = (0..m).map(|r| usize::from(r == 0)).collect();
    loop {
        let sig: Vec<(usize, usize, usize)> = (0..m)
            .map(|r| (cls[r], cls[2 * r % m], cls[(2 * r + 1) % m]))
            .collect();
        let mut ids = std::collections::BTreeMap::new();
        let next: Vec<usize> = sig
            .iter()
            .map(|s| {
                let n = ids.len();
                *ids.entry(*s).or_insert(n)
            })
            .collect();
        let count = |v: &[usize]| v.iter().collect::<BTreeSet<_>>().len();
        if count(&next) == count(&cls) {
            return count(&next);
        }
        cls = next;
    }
}

/// claims.js check 11, Codex: the multiples of an odd `m`, read from the top bit, need `m`
/// states; control: even `m` (a power of two `2^k` needs `k + 1`).
#[test]
fn the_multiples_of_an_odd_m_need_m_states() {
    assert!((1..=63).step_by(2).all(|m| min_dfa(m) == m));
    assert!(![4, 8, 12, 16].iter().all(|m| min_dfa(*m) == *m));
}

/// claims.js check 12 and study2 R5, Claude: `x^2` mod an odd prime `p` takes `(p + 1) / 2`
/// values; control `(p - 1) / 2`.
#[test]
fn a_square_mod_an_odd_prime_takes_half_the_values_and_one() {
    let ps = [3i64, 5, 7, 11, 13, 17, 19, 23, 97];
    assert!(
        ps.iter()
            .all(|p| squares_mod(*p).len() as i64 == (p + 1) / 2)
    );
    assert!(
        !ps.iter()
            .all(|p| squares_mod(*p).len() as i64 == (p - 1) / 2)
    );
}

// ---- alg.js (STUDY1) ----

/// alg.js rule 1: the image under `mod m` of the progression `{lo + i k : 0 <= i < n}` is the
/// class `lo mod g` in `[0, m)` (`g = gcd(k, m)`) when `n >= m / g`; for `k = 1` and `n < m`
/// it is `[l..=h]` if `l <= h`, else `[0..=h]` and `[l..<m]`, with `l = lo mod m`,
/// `h = (lo + n - 1) mod m`. `None` for a partial progression of stride above 1. With `wrong`,
/// the full image one step early (the control).
fn image_rule(lo: i64, k: i64, n: i64, m: i64, wrong: bool) -> Option<BTreeSet<i64>> {
    let g = gcd(k, m);
    let full = if wrong { n >= m / g - 1 } else { n >= m / g };
    if full {
        return Some((lo.rem_euclid(g)..m).step_by(g as usize).collect());
    }
    if k != 1 {
        return None;
    }
    let (l, h) = (lo.rem_euclid(m), (lo + n - 1).rem_euclid(m));
    Some(if l <= h {
        (l..=h).collect()
    } else {
        (0..=h).chain(l..m).collect()
    })
}

#[test]
fn the_image_of_a_progression_mod_m_is_a_class_or_an_arc() {
    let (mut rng, seed) = Rng::fresh("exact sets: images of progressions mod m");
    let mut control_caught = false;
    for _ in 0..20000 {
        let (m, k, n, lo) = (
            rng.int(1, 30),
            rng.int(1, 12),
            rng.int(1, 70),
            rng.int(-100, 99),
        );
        let brute: BTreeSet<i64> = (0..n).map(|i| (lo + i * k).rem_euclid(m)).collect();
        if let Some(r) = image_rule(lo, k, n, m, false) {
            assert_eq!(r, brute, "seed {seed}: {lo} + i {k}, {n} terms, mod {m}");
        }
        control_caught |= image_rule(lo, k, n, m, true).is_some_and(|r| r != brute);
    }
    assert!(
        control_caught,
        "seed {seed}: the full image one step early was not caught"
    );
}

/// alg.js rule 2, the author's example: the image of `[0..<n]` under `mod m` is
/// `[0..<min(n, m)]` for `n >= 1`; control `max`.
#[test]
fn the_image_of_zero_to_n_mod_m_is_zero_to_the_least_of_n_and_m() {
    let image = |n: i64, m: i64| (0..n).map(|x| x % m).collect::<BTreeSet<_>>();
    let all = |f: fn(i64, i64) -> i64| {
        (1..60).all(|n| (1..40).all(|m| image(n, m) == (0..f(n, m)).collect::<BTreeSet<_>>()))
    };
    assert!(all(i64::min));
    assert!(!all(i64::max));
}

/// `cs` (highest degree first) at `x`, by Horner's rule.
fn eval_poly(cs: &[i64], x: i64) -> i64 {
    cs.iter().fold(0, |acc, c| acc * x + c)
}

/// `Δ^j p(0)` for `j` in `0..=deg`: the coefficients of `p` in the binomial basis `C(x, j)`.
fn binomial_coeffs(p: impl Fn(i64) -> i64, deg: usize) -> Vec<i64> {
    let mut v: Vec<i64> = (0..=deg as i64).map(p).collect();
    let mut c = vec![];
    for _ in 0..=deg {
        c.push(v[0]);
        v = v.windows(2).map(|w| w[1] - w[0]).collect();
    }
    c
}

/// The power-basis coefficients of `p(x + d) - p(x)`, by the binomial theorem (the control's
/// wrong test of rule 3).
fn power_coeffs_of_shift_diff(cs: &[i64], d: i64) -> Vec<i64> {
    let deg = cs.len() - 1;
    let mut out = vec![0; deg + 1];
    let choose = |n: usize, k: usize| (0..k).fold(1i64, |r, i| r * (n - i) as i64 / (i + 1) as i64);
    for (i, c) in cs.iter().enumerate() {
        let n = deg - i;
        for (k, o) in out.iter_mut().enumerate().take(n) {
            *o += c * choose(n, k) * d.pow((n - k) as u32);
        }
    }
    out
}

/// alg.js rule 3: the period of `p mod m` is the least `d` dividing `m` with every binomial
/// coefficient of `p(x + d) - p(x)` divisible by `m`.
fn period_rule(cs: &[i64], m: i64, wrong: bool) -> i64 {
    let deg = cs.len() - 1;
    for d in (1..=m).filter(|d| m % d == 0) {
        let bc = if wrong {
            power_coeffs_of_shift_diff(cs, d)
        } else {
            binomial_coeffs(|x| eval_poly(cs, x + d) - eval_poly(cs, x), deg)
        };
        if bc.iter().all(|c| c.rem_euclid(m) == 0) {
            return d;
        }
    }
    m
}

fn period_brute(cs: &[i64], m: i64) -> i64 {
    (1..=m)
        .find(|d| (0..2 * m).all(|x| (eval_poly(cs, x + d) - eval_poly(cs, x)).rem_euclid(m) == 0))
        .expect("p(x + m) == p(x) mod m")
}

#[test]
fn the_period_of_a_polynomial_mod_m_is_read_from_its_binomial_basis() {
    let (mut rng, seed) = Rng::fresh("exact sets: periods of polynomials mod m");
    let mut cases: Vec<(Vec<i64>, i64)> = vec![
        (vec![1, 0, -1, 0], 6),
        (vec![1, 0, -1, 0], 3),
        (vec![1, 0, 0, -1, 0], 30),
    ];
    for _ in 0..4000 {
        let deg = rng.int(1, 4);
        let m = rng.pick(&[6, 12, 24, 30, 60]) * rng.int(1, 2);
        cases.push(((0..=deg).map(|_| rng.int(-10, 10)).collect(), m));
    }
    let mut control_caught = false;
    for (cs, m) in &cases {
        let brute = period_brute(cs, *m);
        assert_eq!(
            period_rule(cs, *m, false),
            brute,
            "seed {seed}: {cs:?} mod {m}"
        );
        control_caught |= period_rule(cs, *m, true) != brute;
    }
    assert!(
        control_caught,
        "seed {seed}: the power-basis test was not caught"
    );
}

/// alg.js rule 4: a polynomial of degree `d` whose leading coefficient is not 0 mod a prime
/// `p` takes at least `ceil(p / d)` values mod `p` (each value has at most `d` roots); the
/// control's bound, one more, fails somewhere.
#[test]
fn a_polynomial_of_degree_d_mod_p_takes_at_least_p_over_d_values() {
    let (mut rng, seed) = Rng::fresh("exact sets: images of polynomials mod a prime");
    let primes = [2i64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];
    let mut control_caught = false;
    for _ in 0..4000 {
        let (p, deg) = (rng.pick(&primes), rng.int(1, 4));
        let cs: Vec<i64> = (0..=deg).map(|_| rng.int(-20, 20)).collect();
        if cs[0].rem_euclid(p) == 0 {
            continue;
        }
        let image: BTreeSet<i64> = (0..p).map(|x| eval_poly(&cs, x).rem_euclid(p)).collect();
        let bound = (p as u64).div_ceil(deg as u64) as i64;
        assert!(image.len() as i64 >= bound, "seed {seed}: {cs:?} mod {p}");
        control_caught |= (image.len() as i64) < bound + 1;
    }
    assert!(
        control_caught,
        "seed {seed}: the bound plus one was not caught"
    );
}

/// alg.js's examples: the classes of `x * x mod 10 == 9` by the CRT, `x == 1 (mod 2)` and `x
/// in {2, 3} (mod 5)`, are `{3, 7}`; and `x * x mod 4` has period 2 by rule 3, with image `{0,
/// 1}`, inside `[0..=1]`.
#[test]
fn the_q11_examples_by_the_rules() {
    let roots = |m: i64| {
        (0..m)
            .filter(|r| (r * r - 9).rem_euclid(m) == 0)
            .collect::<Vec<_>>()
    };
    let (r2, r5) = (roots(2), roots(5));
    assert_eq!((r2.clone(), r5.clone()), (vec![1], vec![2, 3]));
    let classes: BTreeSet<i64> = (0..10)
        .filter(|r| r2.contains(&(r % 2)) && r5.contains(&(r % 5)))
        .collect();
    assert_eq!(classes, BTreeSet::from([3, 7]));
    let d = period_rule(&[1, 0, 0], 4, false);
    assert_eq!(d, 2);
    let image: BTreeSet<i64> = (0..d).map(|r| r * r % 4).collect();
    assert_eq!(image, BTreeSet::from([0, 1]));
}

// ---- meta1/algebra.js ----

/// `Σ ⌊(a i + b) / m⌋` for `i` below `n` (the AtCoder Library's form, `n >= 0`, `m >= 1`, `a,
/// b >= 0`), and the number of rounds of its loop, each one Euclid step on `(a, m)`.
fn floor_sum(n: &Int, m: &Int, a: &Int, b: &Int) -> (Int, usize) {
    let two = Int::from(2);
    let (mut n, mut m, mut a, mut b) = (n.clone(), m.clone(), a.clone(), b.clone());
    let (mut ans, mut steps) = (Int::ZERO, 0);
    loop {
        steps += 1;
        if a >= m {
            let pairs = (&n * &(&n - &Int::ONE)).div_floor(&two);
            ans = &ans + &(&pairs * &a.div_floor(&m));
            a = a.mod_floor(&m);
        }
        if b >= m {
            ans = &ans + &(&n * &b.div_floor(&m));
            b = b.mod_floor(&m);
        }
        let y_max = &(&a * &n) + &b;
        if y_max < m {
            return (ans, steps);
        }
        (n, b) = (y_max.div_floor(&m), y_max.mod_floor(&m));
        (m, a) = (a, m);
    }
}

/// `#{t < n : (a t + b) mod m >= c}`, `0 <= c <= m`, by the identity `⌊(v + m - c) / m⌋ -
/// ⌊v / m⌋ = [v mod m >= c]`; with `bug`, the cut one too high (the control). Also the rounds.
fn at_least(n: &Int, a: &Int, b: &Int, m: &Int, c: &Int, bug: bool) -> (Int, usize) {
    let shift = &(&(b + m) - c) + &Int::from(i64::from(bug));
    let (hi, s1) = floor_sum(n, m, a, &shift);
    let (lo, s2) = floor_sum(n, m, a, b);
    (&hi - &lo, s1 + s2)
}

/// `#{t < n : l <= (a t + b) mod m <= r}`, and the rounds of the four floor sums.
fn hits(n: &Int, a: &Int, b: &Int, m: &Int, (l, r): (&Int, &Int), bug: bool) -> (Int, usize) {
    let (x, s1) = at_least(n, a, b, m, l, bug);
    let (y, s2) = at_least(n, a, b, m, &(r + &Int::ONE), false);
    (&x - &y, s1 + s2)
}

/// algebra.js result J: the hits of a partial progression `(a t + b) mod m`, `t < n`, in an
/// interval `[l..=r]`, by floor sums, against counting them; control: the lower cut off by one.
#[test]
fn the_hits_of_a_progression_in_an_interval_are_a_difference_of_floor_sums() {
    let (mut rng, seed) = Rng::fresh("exact sets: hits of a progression by floor sums");
    let mut control_caught = false;
    for _ in 0..30000 {
        let m = rng.int(1, 200);
        let (a, b, n) = (rng.int(0, m - 1), rng.int(0, m - 1), rng.int(0, 3 * m));
        let l = rng.int(0, m - 1);
        let r = rng.int(l, m - 1);
        let brute = (0..n)
            .filter(|i| (l..=r).contains(&((a * i + b) % m)))
            .count();
        let ints = [n, a, b, m, l, r].map(Int::from);
        let [n_, a_, b_, m_, l_, r_] = &ints;
        let got = |bug| hits(n_, a_, b_, m_, (l_, r_), bug).0;
        assert_eq!(
            got(false),
            Int::from(brute),
            "seed {seed}: ({a} t + {b}) mod {m}, t < {n}, in [{l}, {r}]"
        );
        control_caught |= got(true) != Int::from(brute);
    }
    assert!(
        control_caught,
        "seed {seed}: the lower cut off by one was not caught"
    );
}

/// algebra.js result J's cost: the rounds of the floor sums are Euclid steps on `(a, m)`, at
/// most `log_φ m + 2` each (Lamé), so counting the hits of `(a t + 1) mod 10^d`, `t <
/// 10^d / 3`, in a window takes `O(d)` rounds: the four floor sums at most `4 (4.79 d + 2)`
/// (log_φ 10 = 4.785). The script printed the counts at d = 10 to 320; this holds them to the
/// bound. A count linear in `m`, such as subtracting `m` once a round, fails it at the first
/// `d`.
#[test]
fn the_hits_of_a_progression_take_rounds_linear_in_the_digits_of_m() {
    let (mut rng, _) = Rng::fresh("exact sets: rounds of floor sums at large m");
    let ten = Int::from(10);
    for d in [10usize, 20, 40, 80, 160, 320] {
        let m = (0..d).fold(Int::ONE, |p, _| &p * &ten);
        let a = (0..d).fold(Int::ZERO, |a, _| &(&a * &ten) + &Int::from(rng.int(0, 9)));
        // Odd, as the script's `a | 1`.
        let a = if a.mod_floor(&Int::from(2)).is_zero() {
            &a + &Int::ONE
        } else {
            a
        };
        let a = a.mod_floor(&m);
        let half = m.div_floor(&Int::from(2));
        let window = (&half, &(&half + &ten));
        let (count, rounds) = hits(
            &m.div_floor(&Int::from(3)),
            &a,
            &Int::ONE,
            &m,
            window,
            false,
        );
        assert!(count >= Int::ZERO);
        let bound = 4 * (479 * d / 100 + 3);
        assert!(rounds <= bound, "d = {d}: {rounds} rounds, bound {bound}");
    }
}

/// The exponent of `p` in `n`.
fn valuation(mut n: i64, p: i64) -> u32 {
    let mut e = 0;
    while n % p == 0 {
        n /= p;
        e += 1;
    }
    e
}

/// Whether the balls `(r, e)` (the class `r mod p^e`) cover every `x == prefix (mod p^d)`:
/// the walk of the `p`-adic trie along the balls. With `bug`, a region no ball reaches counts
/// as covered (the control).
fn tree_covers(balls: &[(i64, u32)], p: i64, prefix: i64, d: u32, bug: bool) -> bool {
    if balls
        .iter()
        .any(|(r, e)| *e <= d && r % p.pow(*e) == prefix % p.pow(*e))
    {
        return true;
    }
    let below: Vec<(i64, u32)> = balls
        .iter()
        .filter(|(r, e)| *e > d && r % p.pow(d) == prefix)
        .copied()
        .collect();
    if below.is_empty() {
        return bug;
    }
    (0..p).all(|c| tree_covers(&below, p, prefix + c * p.pow(d), d + 1, bug))
}

/// algebra.js result K: whether the congruences `(m, r)`, each `m = 2^a 3^b`, cover the
/// integers, by the CRT split `Z/2^A 3^B = Z/2^A × Z/3^B`: walk the 2-adic trie along the
/// balls, and where no deeper 2-ball splits, test whether the 3-balls active there cover by the
/// same walk in base 3: O(k^2 A B) nodes for k congruences, polynomial in the written size.
fn covers_2_3(sys: &[(i64, i64)], bug: bool) -> bool {
    let cong: Vec<(u32, u32, i64, i64)> = sys
        .iter()
        .map(|&(m, r)| {
            let (a, b) = (valuation(m, 2), valuation(m, 3));
            (a, b, r % (1 << a), r % 3i64.pow(b))
        })
        .collect();
    fn walk(cong: &[(u32, u32, i64, i64)], prefix: i64, d: u32, bug: bool) -> bool {
        let active: Vec<(i64, u32)> = cong
            .iter()
            .filter(|(a, _, r2, _)| *a <= d && *r2 == prefix % (1 << a))
            .map(|(_, b, _, r3)| (*r3, *b))
            .collect();
        if !cong
            .iter()
            .any(|(a, _, r2, _)| *a > d && r2 % (1 << d) == prefix)
        {
            return tree_covers(&active, 3, 0, 0, bug);
        }
        walk(cong, prefix, d + 1, bug) && walk(cong, prefix + (1 << d), d + 1, bug)
    }
    walk(&cong, 0, 0, bug)
}

#[test]
fn covering_by_congruences_of_moduli_2_to_the_a_3_to_the_b_is_decided_by_two_tries() {
    let (mut rng, seed) = Rng::fresh("exact sets: covering by 3-smooth moduli");
    let mut control_caught = false;
    for _ in 0..20000 {
        let k = rng.int(1, 8);
        let sys: Vec<(i64, i64)> = (0..k)
            .map(|_| {
                let m = (1 << rng.int(0, 4)) * 3i64.pow(rng.int(0, 2) as u32);
                (m, rng.int(0, m - 1))
            })
            .collect();
        let lcm = sys.iter().fold(1, |l, (m, _)| l / gcd(l, *m) * m);
        let brute = (0..lcm).all(|x| sys.iter().any(|(m, r)| x % m == *r));
        assert_eq!(covers_2_3(&sys, false), brute, "seed {seed}: {sys:?}");
        control_caught |= covers_2_3(&sys, true) != brute;
    }
    assert!(
        control_caught,
        "seed {seed}: an unreached region counted as covered was not caught"
    );
    // Erdős's system has the 3-smooth moduli 2, 3, 4, 6, 12.
    let erdos = [(2, 0), (3, 0), (4, 1), (6, 5), (12, 7)];
    assert!(covers_2_3(&erdos, false));
    assert!(!covers_2_3(&erdos[..4], false));
}

// ---- meta1/study2_examples.js ----

fn image(lo: i64, hi: i64, f: impl Fn(i64) -> i64, keep: impl Fn(i64) -> bool) -> BTreeSet<i64> {
    (lo..=hi).filter(|x| keep(*x)).map(f).collect()
}

/// STUDY2 section 3's worked examples by brute force, each against the wrong answer it must
/// reject.
#[test]
fn the_worked_examples_of_study2() {
    let check = |name: &str, actual: BTreeSet<i64>, claimed: &[i64], wrong: &[i64]| {
        let (claimed, wrong): (BTreeSet<i64>, BTreeSet<i64>) = (
            claimed.iter().copied().collect(),
            wrong.iter().copied().collect(),
        );
        assert_eq!(actual, claimed, "{name}");
        assert_ne!(actual, wrong, "{name}: control");
    };
    let range = |a: i64, b: i64| (a..=b).collect::<Vec<_>>();
    let all = |_: i64| true;
    let r1 = [range(0, 3), range(7, 9)].concat();
    check(
        "R1 [7..13] mod 10",
        image(7, 13, |x| x % 10, all),
        &r1[..],
        &[range(0, 3), range(7, 10)].concat()[..],
    );
    check(
        "R2 {0, 4, 8} mod 6",
        image(0, 2, |i| 4 * i % 6, all),
        &[0, 2, 4],
        &[0, 4],
    );
    check(
        "R4 x * x mod 4 on [0..=255]",
        image(0, 255, |x| x * x % 4, all),
        &[0, 1],
        &[0, 1, 2],
    );
    check(
        "R5 squares mod 11 count 6",
        BTreeSet::from([squares_mod(11).len() as i64]),
        &[6],
        &[5],
    );
    let nine = |x: i64| x * x % 10 == 9;
    check(
        "R6 x * x mod 10 == 9 classes mod 10",
        image(0, 9, |x| x, nine),
        &[3, 7],
        &[3],
    );
    check(
        "ranged arm on [0..=18]",
        image(0, 18, |x| x, nine),
        &[3, 7, 13, 17],
        &[3, 7, 13],
    );
    // τ: the primes q of m at which x^2 == 1 has more than one root mod q.
    let tau = |m: i64| {
        [2i64, 3, 5, 7]
            .iter()
            .filter(|q| m % *q == 0 && (0..**q).filter(|x| x * x % *q == 1 % *q).count() > 1)
            .count() as i64
    };
    check(
        "R10 tau(mod 105, == 1) = 3",
        BTreeSet::from([tau(105)]),
        &[3],
        &[2],
    );
    let more_than_one = i64::from((0..5).filter(|x| x * x % 5 == 4).count() > 1);
    check(
        "R10 tau(mod 10, == 9) = 1",
        BTreeSet::from([more_than_one]),
        &[1],
        &[0],
    );
    let window = |t: i64| (500..=510).contains(&((7 * t + 1) % 1000));
    check(
        "R9 one hit, t = 72",
        image(0, 99, |t| t, window),
        &[72],
        &[],
    );
    let r8 = [range(0, 4), range(6, 100)].concat();
    check(
        "R8 x mod 101 != 5",
        image(0, 100, |x| x, |x| x != 5),
        &r8[..],
        &range(0, 100)[..],
    );
}
