//! Study Q1-LOCAL, phase 1 (docs/plan_dag.md, row Q1-LOCAL): how the solver does today on
//! systems with four live variables or more. Two kinds of test.
//!
//! The census decides random systems over four variables in [-4, 4] and checks each answer
//! against every point of the box; each refusal is classed by whether the system has an integer
//! point, and if not, whether it has a rational one (`stages::rationally_empty`). The systems
//! are those of `oracle::small_coefficients_over_four_variables_match_enumeration` (seed
//! 0x38_0a) and the fresh-seed family of cross-review XR3 (`wt/xt4/verify-r3/probes/
//! verify_r3.rs`, seeds 0x5eed_0001 to 0x5eed_0005, 2,000 systems each, its xorshift
//! generator). Phase 1 measured the counts on 2026-11-07 at 8874023a; phase 2 (pivots chosen by
//! the rows a pivot leaves, eliminations that write no more terms than they remove, and rows of
//! two terms implied by another within the bounds dropped) decides more, and the counts below
//! are those of phase 2, on 2026-11-08. The oracle family went from 274 true, 5 false and 121
//! refused to 281, 7 and 112.
//!
//! The growth tables time `decide` on families of systems at n, 2n, 4n and 8n, each built
//! before it is timed, and print the instructions with the ratio to n; each test then checks the
//! answer at every size and the ratio from n to 8n against the harness's limit
//! (`scaling::check`). A family whose 8n run is above that limit today fails, and a row of
//! docs/plan_dag.md owns its fix (Q1-LOCAL-method for those refused with `Growth`).

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_tests::instances::Rng;
use zed_tests::scaling::{self, Meter};
use zedc::store::presburger::{Atom, Con, Formula, Lin, Refusal, decide, satisfiable};

use super::stages::{Row, rationally_empty};

/// The formula of the rows `Σ c·x[i] + k >= 0`, with `x[i]` named `{prefix}{i}`.
fn system(rows: &[Row], prefix: &str) -> Formula {
    Formula::and(
        rows.iter()
            .map(|(t, k)| {
                let lin = t.iter().fold(Lin::constant(*k), |l, (i, c)| {
                    l.plus(&Lin::atom(Atom::Sym(Arc::from(format!("{prefix}{i}")))).times(*c))
                });
                Formula::Con(Con::ge(&lin, &Lin::constant(0)))
            })
            .collect(),
    )
}

/// The rows `x[i] + half >= 0` and `half - x[i] >= 0` for `i < n`.
fn boxed(rows: &mut Vec<Row>, n: usize, half: i64) {
    for i in 0..n {
        rows.push((vec![(i, 1)], half));
        rows.push((vec![(i, -1)], half));
    }
}

/// Whether some point of `[-half, half]^n` holds every row.
fn has_point(rows: &[Row], n: usize, half: i64) -> bool {
    let mut p = vec![-half; n];
    loop {
        if rows
            .iter()
            .all(|(t, k)| t.iter().map(|(i, c)| c * p[*i]).sum::<i64>() + k >= 0)
        {
            return true;
        }
        let mut i = 0;
        loop {
            if i == n {
                return false;
            }
            if p[i] < half {
                p[i] += 1;
                break;
            }
            p[i] = -half;
            i += 1;
        }
    }
}

/// The fewest rows of `rows` that have no rational point together: the size of the least
/// support of a Farkas certificate. Every subset of each size is tried, in increasing size.
fn least_empty_support(rows: &[Row], n: usize) -> usize {
    let m = rows.len();
    for size in 1..=m {
        let mut pick: Vec<usize> = (0..size).collect();
        loop {
            let sub: Vec<Row> = pick.iter().map(|&i| rows[i].clone()).collect();
            if rationally_empty(&sub, n) {
                return size;
            }
            // The next subset of `size` in lexicographic order.
            let Some(i) = (0..size).rev().find(|&i| pick[i] < m - size + i) else {
                break;
            };
            pick[i] += 1;
            for j in i + 1..size {
                pick[j] = pick[j - 1] + 1;
            }
        }
    }
    unreachable!("the rows have no rational point")
}

/// The xorshift generator of cross-review XR3's probes (`verify_r3.rs:196`).
struct XorShift(u64);

impl XorShift {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn int(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next() % ((hi - lo + 1) as u64)) as i64
    }
}

/// One system of the fresh-seed family: 2 to 5 rows over four variables, coefficients in
/// [-7, 7], constants in [-20, 20], drawn as `verify_r3.rs` draws them, then the box [-4, 4].
fn fresh(rng: &mut XorShift) -> Vec<Row> {
    let m = 2 + rng.int(0, 3) as usize;
    let mut rows: Vec<Row> = (0..m)
        .map(|_| {
            let t = (0..4).map(|j| (j, rng.int(-7, 7))).collect();
            (t, rng.int(-20, 20))
        })
        .collect();
    boxed(&mut rows, 4, 4);
    rows
}

/// One system of the oracle's family (seed 0x38_0a): 2 to 5 rows over four variables,
/// coefficients in [-7, 7], constants in [-20, 20], then the box [-4, 4].
fn oracle(rng: &mut Rng) -> Vec<Row> {
    let m = 2 + rng.below(4);
    let mut rows: Vec<Row> = (0..m)
        .map(|_| {
            let t = (0..4).map(|j| (j, rng.int(-7, 7))).collect();
            (t, rng.int(-20, 20))
        })
        .collect();
    boxed(&mut rows, 4, 4);
    rows
}

/// What the census found: by the solver's answer, the system's truth.
#[derive(Default, Debug, PartialEq, Eq)]
struct Census {
    /// Decided with a point; decided empty.
    sat: usize,
    unsat: usize,
    /// Refused, by cause and by what the system is: an integer point; a rational point and no
    /// integer one; no rational point.
    refused: BTreeMap<(String, &'static str), usize>,
    /// For the refused systems with no rational point, the least support of a certificate, by
    /// size.
    support: BTreeMap<usize, usize>,
}

/// The cause of a refusal, without the rows a tie names.
fn cause(r: &Refusal) -> String {
    match r {
        Refusal::Growth => "Growth",
        Refusal::Shadows => "Shadows",
        Refusal::Disjuncts => "Disjuncts",
        Refusal::Tie(_) => "Tie",
        Refusal::Unordered(_) => "Unordered",
    }
    .to_string()
}

/// Decides each system, checks every answer against the box's points, and classes each
/// refusal. A model must hold, and `decide` must agree with `satisfiable`.
fn census(systems: impl Iterator<Item = Vec<Row>>) -> Census {
    let mut c = Census::default();
    for rows in systems {
        let f = system(&rows, "v");
        let truth = has_point(&rows, 4, 4);
        let got = satisfiable(&f);
        assert_eq!(
            decide(&f),
            got.as_ref().map(Option::is_some).map_err(Refusal::clone),
            "{f}"
        );
        match &got {
            Ok(Some(m)) => {
                assert!(truth && f.holds(m), "{f}: {m:?}");
                c.sat += 1;
            }
            Ok(None) => {
                assert!(!truth, "{f}: no point found in a system with one");
                c.unsat += 1;
            }
            Err(r) => {
                let what = if truth {
                    "integer point"
                } else if rationally_empty(&rows, 4) {
                    *c.support.entry(least_empty_support(&rows, 4)).or_insert(0) += 1;
                    "no rational point"
                } else {
                    "rational point only"
                };
                *c.refused.entry((cause(r), what)).or_insert(0) += 1;
            }
        }
    }
    c
}

/// The refusals of a census: the cause, the truth of the system, and the count.
type Refused = Vec<(String, &'static str, usize)>;

/// The counts of a census, written for the assertions below.
fn counts(c: &Census) -> (usize, usize, Refused, Vec<(usize, usize)>) {
    (
        c.sat,
        c.unsat,
        c.refused
            .iter()
            .map(|((r, w), n)| (r.clone(), *w, *n))
            .collect(),
        c.support.iter().map(|(s, n)| (*s, *n)).collect(),
    )
}

/// Refusals all for `Growth`: with an integer point, with no rational point, with a rational
/// point and no integer one.
fn g(point: usize, no_rational: usize, rational: usize) -> Refused {
    vec![
        ("Growth".to_string(), "integer point", point),
        ("Growth".to_string(), "no rational point", no_rational),
        ("Growth".to_string(), "rational point only", rational),
    ]
}

/// The checks the census rests on, each shown able to fail: the enumeration finds a point and
/// misses one, and the rational test tells an empty pair of rows from one with a point.
#[test]
fn the_census_checks_can_fail() {
    let one: Vec<Row> = vec![(vec![(0, 2), (1, -2)], -1), (vec![(0, -2), (1, 2)], 1)];
    // `2·x0 - 2·x1 == 1`: a rational point, no integer one.
    assert!(!has_point(&one, 2, 4));
    assert!(!rationally_empty(&one, 2));
    let two: Vec<Row> = vec![(vec![(0, 1), (1, -1)], 0), (vec![(0, -1), (1, 1)], 0)];
    assert!(has_point(&two, 2, 4));
    let empty: Vec<Row> = vec![(vec![(0, 1)], -1), (vec![(0, -1)], 0)];
    assert!(rationally_empty(&empty, 1));
    assert_eq!(least_empty_support(&empty, 1), 2);
    let mut three = empty.clone();
    three.insert(1, (vec![(1, 1)], 0));
    assert_eq!(least_empty_support(&three, 2), 2);
}

#[test]
fn the_census_of_the_oracle_family() {
    let mut rng = Rng::new(0x38_0a);
    let c = census((0..400).map(|_| oracle(&mut rng)));
    println!("Q1-LOCAL census, oracle seed 0x38_0a, 400 systems: {c:?}");
    assert_eq!(
        counts(&c),
        (281, 7, g(91, 14, 7), vec![(4, 2), (5, 12)]),
        "{c:?}"
    );
}

/// The census of the 2,000 systems of one fresh seed.
fn fresh_census(seed: u64) -> Census {
    let mut rng = XorShift(seed);
    let c = census((0..2000).map(|_| fresh(&mut rng)));
    println!("Q1-LOCAL census, fresh seed {seed:#x}, 2,000 systems: {c:?}");
    c
}

#[test]
fn the_census_of_fresh_seed_1() {
    let c = fresh_census(0x5eed_0001);
    assert_eq!(
        counts(&c),
        (1365, 52, g(432, 121, 30), vec![(3, 1), (4, 16), (5, 104)]),
        "{c:?}"
    );
}

#[test]
fn the_census_of_fresh_seed_2() {
    let c = fresh_census(0x5eed_0002);
    assert_eq!(
        counts(&c),
        (1376, 55, g(438, 116, 15), vec![(3, 1), (4, 16), (5, 99)]),
        "{c:?}"
    );
}

#[test]
fn the_census_of_fresh_seed_3() {
    let c = fresh_census(0x5eed_0003);
    assert_eq!(
        counts(&c),
        (1353, 77, g(397, 152, 21), vec![(3, 2), (4, 29), (5, 121)]),
        "{c:?}"
    );
}

#[test]
fn the_census_of_fresh_seed_4() {
    let c = fresh_census(0x5eed_0004);
    assert_eq!(
        counts(&c),
        (1378, 60, g(416, 125, 21), vec![(3, 1), (4, 17), (5, 107)]),
        "{c:?}"
    );
}

#[test]
fn the_census_of_fresh_seed_5() {
    let c = fresh_census(0x5eed_0005);
    assert_eq!(
        counts(&c),
        (1358, 77, g(412, 133, 20), vec![(3, 2), (4, 12), (5, 119)]),
        "{c:?}"
    );
}

// ---------------------------------------------------------------------------------------------
// Growth.

/// The instructions `decide` takes on `f`, the least of two runs, each on a thread of its own so
/// that no memo of a thread carries over, and its answer.
fn work(f: &Formula) -> (u64, Result<bool, Refusal>) {
    let one = || {
        scaling::on_a_thread(1 << 28, || {
            let mut meter = Meter::new();
            let mut answer = None;
            let w = meter.work(|| answer = Some(decide(f)));
            (w.units, answer.expect("decided"))
        })
    };
    let (a, answer) = one();
    let (b, again) = one();
    assert_eq!(answer, again, "{f}");
    (a.min(b), answer)
}

/// The answer, short.
fn short(a: &Result<bool, Refusal>) -> String {
    match a {
        Ok(true) => "point".to_string(),
        Ok(false) => "empty".to_string(),
        Err(r) => cause(r),
    }
}

/// Prints the instructions of `decide` on `make(m)` for m = n, 2n, 4n, 8n, with their ratio to n
/// and the ratio n log n gives, and returns the answers and the ratio at 8n.
fn table(
    what: &str,
    n: usize,
    make: impl Fn(usize) -> Vec<Row>,
) -> (Vec<Result<bool, Refusal>>, f64) {
    let sizes = [n, 2 * n, 4 * n, 8 * n];
    let systems: Vec<(usize, usize, Formula)> = sizes
        .iter()
        .map(|&m| {
            let rows = make(m);
            let terms = rows.iter().map(|(t, _)| t.len()).sum();
            (rows.len(), terms, system(&rows, "x"))
        })
        .collect();
    let mut answers = Vec::new();
    let mut first = 0;
    let mut ratio = 0.0;
    for (&m, (rows, terms, f)) in sizes.iter().zip(&systems) {
        let (units, answer) = work(f);
        if m == n {
            first = units;
        }
        ratio = units as f64 / first as f64;
        let nlogn = (m as f64 * (m as f64).log2()) / (n as f64 * (n as f64).log2());
        println!(
            "Q1-LOCAL growth | {what} | n={m} | rows={rows} | terms={terms} | {} | {units} | {ratio:.2}x | n log n {nlogn:.2}x | load {}",
            short(&answer),
            std::fs::read_to_string("/proc/loadavg")
                .map(|l| l.split(' ').next().unwrap_or("").to_string())
                .unwrap_or_default()
        );
        answers.push(answer);
    }
    (answers, ratio)
}

/// [`table`], then the answers checked against `answer` at every size and the work from n to
/// 8n against the harness's limit.
fn grows(what: &str, n: usize, answer: Result<bool, Refusal>, make: impl Fn(usize) -> Vec<Row>) {
    let (answers, _) = table(what, n, &make);
    for a in &answers {
        assert_eq!(a, &answer, "{what}");
    }
    let (small, large) = (
        system(&make(n), "x"),
        system(&make(scaling::FACTOR * n), "x"),
    );
    scaling::check(what, n, |m| {
        let _ = std::hint::black_box(decide(if m == n { &small } else { &large }));
    });
}

/// A row over `vars` with coefficients drawn from `coefs`, holding at `p` with a slack in
/// `0..=slack`.
fn planted(rng: &mut Rng, p: &[i64], vars: &[usize], coefs: &[i64], slack: i64) -> Row {
    let t: Vec<(usize, i64)> = vars.iter().map(|&v| (v, rng.pick(coefs))).collect();
    let at: i64 = t.iter().map(|(v, c)| c * p[*v]).sum();
    (t, rng.int(0, slack) - at)
}

/// A point in `[-half + 1, half - 1]^n`, away from the origin.
fn point(rng: &mut Rng, n: usize, half: i64) -> Vec<i64> {
    (0..n).map(|_| rng.int(-half + 1, half - 1)).collect()
}

const SMALL: [i64; 6] = [-3, -2, -1, 1, 2, 3];

/// Sums of four neighbors held in a range, as a schedule's sliding windows are: for `i < n`,
/// `lo[i] <= x[i] + x[i+1] + x[i+2] + x[i+3] <= hi[i]`, each `x` in [0, 9], the range drawn
/// around a hidden point.
fn windows(n: usize) -> (Vec<Row>, Vec<i64>) {
    let mut rng = Rng::new(0x51_0d);
    let v = n + 3;
    let p: Vec<i64> = (0..v).map(|_| rng.int(0, 9)).collect();
    let mut r = Vec::new();
    for i in 0..n {
        let t: Vec<(usize, i64)> = (i..i + 4).map(|j| (j, 1)).collect();
        let s: i64 = (i..i + 4).map(|j| p[j]).sum();
        let neg: Vec<(usize, i64)> = t.iter().map(|(j, c)| (*j, -c)).collect();
        r.push((t, rng.int(0, 2) - s));
        r.push((neg, s + rng.int(0, 2)));
    }
    for i in 0..v {
        r.push((vec![(i, 1)], 0));
        r.push((vec![(i, -1)], 9));
    }
    (r, p)
}

/// [`windows`] with weights: `Σ w[j]·x[i+j]` for the weights `[2, 3, 1, 4]` (a weighted
/// moving sum), range around a hidden point.
fn weighted_windows(n: usize) -> (Vec<Row>, Vec<i64>) {
    let mut rng = Rng::new(0x51_0e);
    let v = n + 3;
    let w = [2, 3, 1, 4];
    let p: Vec<i64> = (0..v).map(|_| rng.int(0, 9)).collect();
    let mut r = Vec::new();
    for i in 0..n {
        let t: Vec<(usize, i64)> = (0..4).map(|j| (i + j, w[j])).collect();
        let s: i64 = (0..4).map(|j| w[j] * p[i + j]).sum();
        let neg: Vec<(usize, i64)> = t.iter().map(|(j, c)| (*j, -c)).collect();
        r.push((t, rng.int(0, 3) - s));
        r.push((neg, s + rng.int(0, 3)));
    }
    for i in 0..v {
        r.push((vec![(i, 1)], 0));
        r.push((vec![(i, -1)], 9));
    }
    (r, p)
}

/// Offsets of `n` pieces laid end to end: `o[0] == 0`, `o[i+1] == o[i] + l[i]`, `1 <= l[i] <=
/// 8`, and `o[n] <= 4n`: variables `o[i]` at `i` and `l[i]` at `n + 1 + i`.
fn offsets(n: usize) -> Vec<Row> {
    let o = |i: usize| i;
    let l = |i: usize| n + 1 + i;
    let mut r: Vec<Row> = vec![(vec![(o(0), 1)], 0), (vec![(o(0), -1)], 0)];
    for i in 0..n {
        let t = vec![(o(i + 1), 1), (o(i), -1), (l(i), -1)];
        let neg = t.iter().map(|(j, c)| (*j, -c)).collect();
        r.push((t, 0));
        r.push((neg, 0));
        r.push((vec![(l(i), 1)], -1));
        r.push((vec![(l(i), -1)], 8));
    }
    r.push((vec![(o(n), -1)], 4 * n as i64));
    r
}

/// A convex sequence: `x[i] - 2·x[i+1] + x[i+2] >= 0` for `i + 2 < n`, each `x` in [0, 4n],
/// with `x[0] >= 2n`, `x[n-1] >= 2n` and the middle at most `n / 4`: a valley.
fn convex(n: usize) -> Vec<Row> {
    let top = 4 * n as i64;
    let mut r = Vec::new();
    for i in 0..n - 2 {
        r.push((vec![(i, 1), (i + 1, -2), (i + 2, 1)], 0));
    }
    for i in 0..n {
        r.push((vec![(i, 1)], 0));
        r.push((vec![(i, -1)], top));
    }
    r.push((vec![(0, 1)], -2 * n as i64));
    r.push((vec![(n - 1, 1)], -2 * n as i64));
    r.push((vec![(n / 2, -1)], n as i64 / 4));
    r
}

/// Sums of the four cells of each 2 by 2 square of a `v` by `v` grid held in a range around a
/// hidden point, each cell in [0, 9]: `v·v` variables, `2 (v - 1)^2` rows of four terms.
fn grid_squares(v: usize) -> (Vec<Row>, Vec<i64>) {
    let mut rng = Rng::new(0x51_0f);
    let p: Vec<i64> = (0..v * v).map(|_| rng.int(0, 9)).collect();
    let mut r = Vec::new();
    for i in 0..v - 1 {
        for j in 0..v - 1 {
            let cells = [
                i * v + j,
                i * v + j + 1,
                (i + 1) * v + j,
                (i + 1) * v + j + 1,
            ];
            let s: i64 = cells.iter().map(|&c| p[c]).sum();
            r.push((cells.iter().map(|&c| (c, 1)).collect(), rng.int(0, 2) - s));
            r.push((cells.iter().map(|&c| (c, -1)).collect(), s + rng.int(0, 2)));
        }
    }
    for i in 0..v * v {
        r.push((vec![(i, 1)], 0));
        r.push((vec![(i, -1)], 9));
    }
    (r, p)
}

/// The side of the grid of [`grid_squares`] whose cells are about `n` (n = 144 gives 12; 2n,
/// 4n and 8n give 17, 24 and 34, within 1% of 2, 4 and 8 times the cells).
fn side(n: usize) -> usize {
    (n as f64).sqrt().round() as usize
}

/// A band: row `i` over `x[i..i+4]` with coefficients in ±1..3, holding at a hidden point with
/// slack 0 to 2, each `x` in [-10, 10]: `n` rows over `n + 3` variables.
fn band(n: usize) -> (Vec<Row>, Vec<i64>) {
    let mut rng = Rng::new(0x51_10);
    let v = n + 3;
    let p = point(&mut rng, v, 10);
    let mut r: Vec<Row> = (0..n)
        .map(|i| planted(&mut rng, &p, &[i, i + 1, i + 2, i + 3], &SMALL, 2))
        .collect();
    boxed(&mut r, v, 10);
    (r, p)
}

/// Sparse random rows: `2n` rows over `n` variables, each over 3 or 4 distinct variables drawn
/// at random, coefficients in ±1..3, holding at a hidden point with slack 0 to 2, each `x` in
/// [-10, 10].
fn sparse_random(n: usize) -> (Vec<Row>, Vec<i64>) {
    let mut rng = Rng::new(0x51_11);
    let p = point(&mut rng, n, 10);
    let mut r = Vec::new();
    for _ in 0..2 * n {
        let k = 3 + rng.below(2);
        let mut vars: Vec<usize> = Vec::new();
        while vars.len() < k {
            let v = rng.below(n);
            if !vars.contains(&v) {
                vars.push(v);
            }
        }
        vars.sort_unstable();
        r.push(planted(&mut rng, &p, &vars, &SMALL, 2));
    }
    boxed(&mut r, n, 10);
    (r, p)
}

/// Blocks of five variables, block `b` over `x[4b..4b+5]`, so that each block shares its last
/// variable with the next block's first: six rows per block, each over three to five of the
/// block's variables, coefficients in ±1..3, holding at a hidden point with slack 0 to 2, each
/// `x` in [-10, 10].
fn chained_blocks(n: usize) -> (Vec<Row>, Vec<i64>) {
    let mut rng = Rng::new(0x51_12);
    let v = 4 * n + 1;
    let p = point(&mut rng, v, 10);
    let mut r = Vec::new();
    for b in 0..n {
        for _ in 0..6 {
            let k = 3 + rng.below(3);
            let mut vars: Vec<usize> = Vec::new();
            while vars.len() < k {
                let x = 4 * b + rng.below(5);
                if !vars.contains(&x) {
                    vars.push(x);
                }
            }
            vars.sort_unstable();
            r.push(planted(&mut rng, &p, &vars, &SMALL, 2));
        }
    }
    boxed(&mut r, v, 10);
    (r, p)
}

/// Blocks of five variables joined as a tree: block `b > 0` has four variables of its own and
/// one of its parent `(b - 1) / 2`, as a record's fields share a name with the record that holds
/// it; six rows per block as in [`chained_blocks`].
fn tree_blocks(n: usize) -> (Vec<Row>, Vec<i64>) {
    let mut rng = Rng::new(0x51_13);
    let v = 4 * n + 1;
    let p = point(&mut rng, v, 10);
    let mut r = Vec::new();
    for b in 0..n {
        // The block's own variables, then the one it shares.
        let mut block: Vec<usize> = (0..4).map(|j| 1 + 4 * b + j).collect();
        block.push(if b == 0 { 0 } else { 1 + 4 * ((b - 1) / 2) });
        for _ in 0..6 {
            let k = 3 + rng.below(3);
            let mut vars: Vec<usize> = Vec::new();
            while vars.len() < k {
                let x = block[rng.below(5)];
                if !vars.contains(&x) {
                    vars.push(x);
                }
            }
            vars.sort_unstable();
            r.push(planted(&mut rng, &p, &vars, &SMALL, 2));
        }
    }
    boxed(&mut r, v, 10);
    (r, p)
}

/// [`chained_blocks`] with a row joining its two ends, `x[0] + x[4n] >= 21`, which no point of
/// the box [-10, 10] holds: empty, and the box's bounds alone show it.
fn chained_blocks_empty(n: usize) -> Vec<Row> {
    let mut r = chained_blocks(n).0;
    r.push((vec![(0, 1), (4 * n, 1)], -21));
    r
}

// Every family below with a point but `Err(Growth)` as its answer is refused today at every
// size: its active test pins that answer and checks the time to the refusal, and an ignored test
// asks for the right answer (`the_families_with_a_point_have_it` shows the point). Ratios from n
// to 8n measured on 2026-11-07 at 8874023a, load about 20, are in each comment.
//
// Each refusal comes from the stage that refuses once every elimination left adds terms
// (`Refusal::Growth`), not from the splinters. An experiment on 2026-11-08 (not kept) took,
// at that point, the variable of least fill on the primal graph of the rows, by its exact
// shadow where a side is unit and by its dark shadow with splinters otherwise. The largest
// bag (a variable and its neighbors) of the min-fill and min-degree orders, at n to 8n:
// 4 for weighted windows and the band, 5 for blocks chained or as a tree, from 19 to 55 for
// grid squares (it grows with the side) and from 36 to 295 for sparse random rows (it grows
// with n). The band was then decided at every size, rows of 4 terms at most, about 13 times
// the instructions from 64 to 512 without the choice's own cost. Weighted windows (at 64, 128
// and 512, not at 256) and both kinds of blocks were refused with `Refusal::Shadows`: a
// splinter of a splinter, which the solver then never searched (a fixed depth of one, since
// OMEGA-splinter-cap a splinter is split again while its dark eliminations leave fewer live
// variables than the one it came from). Grid squares
// from n = 36 and sparse random rows from n = 16 ran past 60 s (sparse random at n = 8 went
// from 32 rows to 3,755 in four eliminations), and stay refused by their form.

#[test]
fn growth_of_the_hub_family() {
    // 9.39x. The hub variable joins the blocks; the first block of four is refused.
    grows(
        "the hub family",
        64,
        Err(Refusal::Growth),
        super::scaling::blocks_with_a_hub,
    );
}

#[test]
fn sliding_windows_of_four_are_decided() {
    // 9.3x the instructions and 8.4x the bytes from 64 to 512 (load 8 to 12, 2026-11-08). Refused
    // with Growth at every size until the exact eliminations were also taken by the terms they
    // write (`System::shrink`): `Sides::fill` counted each opposite pair of windows as growing.
    grows("sliding windows of four", 64, Ok(true), |n| windows(n).0);
}

#[test]
fn growth_of_weighted_sliding_windows() {
    // 9.25x to the refusal.
    grows("weighted sliding windows", 64, Err(Refusal::Growth), |n| {
        weighted_windows(n).0
    });
}

#[test]
fn weighted_sliding_windows_are_decided() {
    grows("weighted sliding windows", 64, Ok(true), |n| {
        weighted_windows(n).0
    });
}

#[test]
fn growth_of_offsets_laid_end_to_end() {
    // 9.3x the instructions and 8.0x the bytes from 256 to 2048, 2.09x, 2.15x and 2.08x per
    // doubling (load 14, 2026-11-08); from 64 to 512, 9.3x and 8.0x. Before, `Omega::flush`
    // resolved every definition of the chain in full (1, 2, ..., n terms) and
    // `System::refresh` read the sum of the n lengths once for each of them, both O(n^2):
    // 16.8x and 16.2x from 64 to 512 (2.37x, 2.53x, 2.81x per doubling), and 34.2x and 30.4x
    // from 256 to 2048 (2.88x, 3.28x, 3.63x), which fails here; so the sizes start at 256.
    // Before that, 23.4x and 32.4x from 64 to 512 until the pivot of an equality was taken
    // among the variables no other equality holds (`pivots`): the chain
    // `o[i+1] == o[i] + l[i]` wrote rows of 3 to n + 1 terms.
    grows("offsets laid end to end", 256, Ok(true), offsets);
}

#[test]
fn growth_of_a_convex_valley() {
    // 9.4x the instructions and 8.1x the bytes from 64 to 512 (load 27, 2026-11-08). Without
    // `System::dominated`, once the stage of `System::shrink` was added, 38.1x the bytes: each
    // step carried one more row `k·x - (k - 1)·y >= -N` implied by the next.
    grows("a convex valley", 64, Ok(true), convex);
}

#[test]
fn growth_of_sums_over_grid_squares() {
    // 10.25x to the refusal.
    grows("sums over grid squares", 144, Err(Refusal::Growth), |n| {
        grid_squares(side(n)).0
    });
}

#[test]
fn sums_over_grid_squares_are_decided() {
    grows("sums over grid squares", 144, Ok(true), |n| {
        grid_squares(side(n)).0
    });
}

#[test]
fn growth_of_a_band_of_four() {
    // 10.03x to the refusal.
    grows("a band of four", 64, Err(Refusal::Growth), |n| band(n).0);
}

#[test]
fn a_band_of_four_is_decided() {
    grows("a band of four", 64, Ok(true), |n| band(n).0);
}

#[test]
fn growth_of_sparse_random_rows() {
    // 9.46x to the refusal.
    grows("sparse random rows", 64, Err(Refusal::Growth), |n| {
        sparse_random(n).0
    });
}

#[test]
fn sparse_random_rows_are_decided() {
    grows("sparse random rows", 64, Ok(true), |n| sparse_random(n).0);
}

#[test]
fn growth_of_chained_blocks_of_five() {
    // 9.40x to the refusal.
    grows("chained blocks of five", 32, Err(Refusal::Growth), |n| {
        chained_blocks(n).0
    });
}

#[test]
fn chained_blocks_of_five_are_decided() {
    grows("chained blocks of five", 32, Ok(true), |n| {
        chained_blocks(n).0
    });
}

#[test]
fn growth_of_a_tree_of_blocks_of_five() {
    // 9.29x to the refusal.
    grows("a tree of blocks of five", 32, Err(Refusal::Growth), |n| {
        tree_blocks(n).0
    });
}

#[test]
fn a_tree_of_blocks_of_five_is_decided() {
    grows("a tree of blocks of five", 32, Ok(true), |n| {
        tree_blocks(n).0
    });
}

#[test]
fn growth_of_chained_blocks_with_a_far_contradiction() {
    // 9.42x.
    grows(
        "chained blocks, far contradiction",
        32,
        Ok(false),
        chained_blocks_empty,
    );
}
fn holds_at(rows: &[Row], p: &[i64]) -> bool {
    rows.iter()
        .all(|(t, k)| t.iter().map(|(i, c)| c * p[*i]).sum::<i64>() + k >= 0)
}

/// The answers the growth tests expect for the families with a point are right: each family's
/// hidden point holds its rows at n and 8n. Offsets get `l[i] = 1`, and the valley
/// `x[i] = 2·|2i - (n - 1)| + 2`. Negative control: the same point with its first coordinate
/// moved past the box holds no family.
#[test]
fn the_families_with_a_point_have_it() {
    let offsets_at =
        |n: usize| -> Vec<i64> { (0..=n).map(|i| i as i64).chain((0..n).map(|_| 1)).collect() };
    let valley_at = |n: usize| -> Vec<i64> {
        (0..n)
            .map(|i| 2 * (2 * i as i64 - (n as i64 - 1)).abs() + 2)
            .collect()
    };
    type Make<'a> = Box<dyn Fn(usize) -> (Vec<Row>, Vec<i64>) + 'a>;
    let families: Vec<(&str, usize, Make)> = vec![
        ("windows", 64, Box::new(windows)),
        ("weighted windows", 64, Box::new(weighted_windows)),
        ("offsets", 64, Box::new(|n| (offsets(n), offsets_at(n)))),
        ("convex", 64, Box::new(|n| (convex(n), valley_at(n)))),
        ("grid squares", 144, Box::new(|n| grid_squares(side(n)))),
        ("band", 64, Box::new(band)),
        ("sparse random", 64, Box::new(sparse_random)),
        ("chained blocks", 32, Box::new(chained_blocks)),
        ("tree blocks", 32, Box::new(tree_blocks)),
    ];
    for (what, n, make) in &families {
        for m in [*n, scaling::FACTOR * n] {
            let (rows, mut p) = make(m);
            assert!(holds_at(&rows, &p), "{what} at {m}");
            p[0] = 1_000_000;
            assert!(!holds_at(&rows, &p), "{what} at {m}: the control holds");
        }
    }
    // The empty family: the hidden point of its blocks fails only the joining row.
    let (blocks, p) = chained_blocks(32);
    let rows = chained_blocks_empty(32);
    assert!(holds_at(&blocks, &p) && !holds_at(&rows, &p));
}

// Order.

/// `rows` in an order drawn from `seed`, and with the variables renamed by a permutation drawn
/// from it: `x[i]` becomes `x[p[i]]`. Both by Fisher-Yates.
fn shuffled(rows: &[Row], seed: u64) -> Vec<Row> {
    let mut rng = Rng::new(seed);
    let n = rows
        .iter()
        .flat_map(|(t, _)| t.iter().map(|(i, _)| i + 1))
        .max()
        .unwrap_or(0);
    let mut p: Vec<usize> = (0..n).collect();
    for i in (1..n).rev() {
        p.swap(i, rng.below(i + 1));
    }
    let mut out: Vec<Row> = rows
        .iter()
        .map(|(t, k)| (t.iter().map(|(i, c)| (p[*i], *c)).collect(), *k))
        .collect();
    for i in (1..out.len()).rev() {
        out.swap(i, rng.below(i + 1));
    }
    out
}

/// The answers on `rows` taken incrementally, on one thread: each prefix of eight chunks of the
/// rows decided in turn, then the whole written as the conjunction of those chunks, each kept as
/// a conjunction of its own ([`Formula::and_keeping`]). Returns the prefixes' answers and the
/// whole's.
fn incrementally(rows: &[Row]) -> (Vec<Result<bool, Refusal>>, Result<bool, Refusal>) {
    let size = rows.len().div_ceil(8).max(1);
    let chunks: Vec<Formula> = rows.chunks(size).map(|c| system(c, "x")).collect();
    scaling::on_a_thread(1 << 28, || {
        let prefixes = (1..chunks.len())
            .map(|k| decide(&Formula::and_keeping(chunks[..k].to_vec(), |_| true)))
            .collect();
        (prefixes, decide(&Formula::and_keeping(chunks, |_| true)))
    })
}

/// The answer on `rows` is the same, true, false or a refusal with the same cause, as written
/// and in five orders with the variables renamed ([`shuffled`]), each decided at once on a
/// thread of its own and incrementally ([`incrementally`]); and no prefix is empty where the
/// whole has a point. A refusal is compared by its cause, as a [`Refusal::Tie`] names the
/// variables. Returns the answer, short ([`short`]).
///
/// `decide` sorts the constraints by their terms before `solve` sees them, so an order of the
/// rows alone never reaches the solver; the names of the variables do, and `solve` puts the
/// rows in the order of `canonical` instead (its doc). Negative controls (2026-11-08): with
/// `solve` taking the rows in the order it is given them and `System::add` leaving in place
/// the held rows a new row implies, so that the rows kept depend on the order, every answer
/// stayed the same; with `solve` refusing when the first row it is given has an odd constant,
/// the oracle's family failed at its first renaming at once and fresh seed 1 incrementally.
fn order_free(what: &str, rows: &[Row]) -> String {
    let once = |rows: &[Row]| {
        let f = system(rows, "x");
        short(&scaling::on_a_thread(1 << 28, || decide(&f)))
    };
    let answer = once(rows);
    for seed in [None, Some(1), Some(2), Some(3), Some(4), Some(5)] {
        let rows = seed.map_or_else(|| rows.to_vec(), |s| shuffled(rows, 0x0d_e7 + s));
        assert_eq!(once(&rows), answer, "{what}, order {seed:?}, at once");
        let (prefixes, whole) = incrementally(&rows);
        assert_eq!(
            short(&whole),
            answer,
            "{what}, order {seed:?}, incrementally"
        );
        if answer == "point" {
            assert!(
                !prefixes.contains(&Ok(false)),
                "{what}, order {seed:?}: a prefix is empty and the whole has a point"
            );
        }
    }
    answer
}

#[test]
fn the_answer_of_each_family_is_free_of_the_order_of_its_rows() {
    let families: Vec<(&str, Vec<Row>, &str)> = vec![
        ("windows", windows(64).0, "point"),
        ("weighted windows", weighted_windows(64).0, "Growth"),
        ("offsets", offsets(64), "point"),
        ("convex", convex(64), "point"),
        ("band", band(64).0, "Growth"),
        ("sparse random", sparse_random(64).0, "Growth"),
        ("chained blocks", chained_blocks(32).0, "Growth"),
        ("tree blocks", tree_blocks(32).0, "Growth"),
        (
            "chained blocks, far contradiction",
            chained_blocks_empty(32),
            "empty",
        ),
        (
            "the hub family",
            super::scaling::blocks_with_a_hub(64),
            "Growth",
        ),
    ];
    for (what, rows, expected) in families {
        assert_eq!(order_free(what, &rows), expected, "{what}");
    }
}

#[test]
fn the_answer_over_grid_squares_is_free_of_the_order_of_its_rows() {
    let rows = grid_squares(side(144)).0;
    assert_eq!(order_free("grid squares", &rows), "Growth");
}

#[test]
fn the_answers_of_the_oracle_family_are_free_of_the_order_of_their_rows() {
    let mut rng = Rng::new(0x38_0a);
    let answers: Vec<_> = (0..400)
        .map(|_| order_free("oracle", &oracle(&mut rng)))
        .collect();
    // The census's counts: the orders change no answer.
    let decided = |b: &str| answers.iter().filter(|a| *a == b).count();
    assert_eq!((decided("point"), decided("empty")), (281, 7));
}

#[test]
fn the_answers_of_fresh_seed_1_are_free_of_the_order_of_their_rows() {
    let mut rng = XorShift(0x5eed_0001);
    for _ in 0..2000 {
        let _ = order_free("fresh seed 1", &fresh(&mut rng));
    }
}
