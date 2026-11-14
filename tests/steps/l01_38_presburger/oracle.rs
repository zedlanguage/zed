//! The Omega test against enumeration: random conjunctions over a few variables within a box,
//! each answered by trying every point of the box. Every answer the solver gives must be the
//! enumeration's, every model must hold, and deciding without a model must agree with
//! finding one. Three families reach the three exact paths: rows of small coefficients over
//! four variables (eliminations, dark shadows and splinters), rows `±x ± y + k >= 0` over five
//! (the parity test), and rows of large coefficients over two (the count under the
//! envelopes).

use std::sync::Arc;

use zed_tests::instances::Rng;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Refusal, decide, satisfiable};

/// A row `Σ c·x + k >= 0` over the variables by place.
pub(super) struct Row {
    c: Vec<i64>,
    k: i64,
}

fn name(i: usize) -> Atom {
    Atom::Sym(Arc::from(format!("v{i}")))
}

fn formula(rows: &[Row], n: usize, half: i64) -> Formula {
    let mut fs: Vec<Formula> = rows
        .iter()
        .map(|r| {
            let lin =
                r.c.iter()
                    .enumerate()
                    .fold(Lin::constant(r.k), |l, (i, c)| {
                        l.plus(&Lin::atom(name(i)).times(*c))
                    });
            Formula::Con(Con::ge(&lin, &Lin::constant(0)))
        })
        .collect();
    for i in 0..n {
        let x = Lin::atom(name(i));
        fs.push(Formula::Con(Con::ge(&x, &Lin::constant(-half))));
        fs.push(Formula::Con(Con::ge(&Lin::constant(half), &x)));
    }
    Formula::and(fs)
}

/// Whether some point of the box `[-half, half]^n` meets every row.
fn enumerate(rows: &[Row], n: usize, half: i64) -> bool {
    let mut p = vec![-half; n];
    loop {
        if rows
            .iter()
            .all(|r| r.c.iter().zip(&p).map(|(c, v)| c * v).sum::<i64>() + r.k >= 0)
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

/// What the solver answered over a family.
#[derive(Default, Debug)]
pub(super) struct Tally {
    pub(super) sat: usize,
    pub(super) unsat: usize,
    pub(super) growth: usize,
    pub(super) shadows: usize,
    pub(super) tie: usize,
}

/// Checks `count` random systems from `make` at `seed` against enumeration.
pub(super) fn run(
    seed: u64,
    count: usize,
    n: usize,
    half: i64,
    make: impl Fn(&mut Rng) -> Vec<Row>,
) -> Tally {
    run_on(&mut Rng::new(seed), count, n, half, make)
}

/// [`run`] on `count` systems drawn with a new seed each run (author P169).
fn run_fresh(
    what: &str,
    count: usize,
    n: usize,
    half: i64,
    make: impl Fn(&mut Rng) -> Vec<Row>,
) -> Tally {
    let (mut rng, _) = Rng::fresh(what);
    run_on(&mut rng, count, n, half, make)
}

/// Checks `count` random systems from `make`, drawn from `rng`, against enumeration.
fn run_on(
    rng: &mut Rng,
    count: usize,
    n: usize,
    half: i64,
    make: impl Fn(&mut Rng) -> Vec<Row>,
) -> Tally {
    let mut t = Tally::default();
    for _ in 0..count {
        let rows = make(rng);
        let f = formula(&rows, n, half);
        let truth = enumerate(&rows, n, half);
        let got = satisfiable(&f);
        match &got {
            Ok(Some(m)) => {
                assert!(truth, "a model of a system with no point: {f}");
                assert!(f.holds(m), "the model {m:?} fails {f}");
                t.sat += 1;
            }
            Ok(None) => {
                assert!(!truth, "no point found in a system with one: {f}");
                t.unsat += 1;
            }
            Err(Refusal::Growth) => t.growth += 1,
            Err(Refusal::Shadows) => t.shadows += 1,
            Err(Refusal::Tie(_)) => t.tie += 1,
            Err(Refusal::Disjuncts) => panic!("a conjunction refused for its disjunctions: {f}"),
            Err(Refusal::Unordered(_)) => panic!("a conjunction refused for its disjunctions: {f}"),
        }
        assert_eq!(
            decide(&f),
            got.as_ref().map(Option::is_some).map_err(Refusal::clone),
            "{f}"
        );
    }
    t
}

fn small(rng: &mut Rng, n: usize, rows: usize, c: i64, k: i64) -> Vec<Row> {
    (0..rows)
        .map(|_| Row {
            c: (0..n).map(|_| rng.int(-c, c)).collect(),
            k: rng.int(-k, k),
        })
        .collect()
}

#[test]
fn small_coefficients_over_four_variables_match_enumeration() {
    let t = run(0x38_0a, 400, 4, 4, |rng| {
        let rows = 2 + rng.below(4);
        small(rng, 4, rows, 7, 20)
    });
    // Both answers occur, so neither check passes by never being asked; the refusals are
    // counted, not required to be absent, and each is a cause of its own. Option A (STATUS.md,
    // L1.38): the counts are those measured with design R, which has no linear program, and
    // the five points of its box stage (XT3). Before R more than 10 of these systems were
    // shown empty; now 3 are, and the empty systems the program decided are refused with
    // Growth. With only the point nearest zero the counts were (213, 3, 184); the four other
    // points decide 42 more with a point, more than the 229 the linear program found: (255, 3,
    // 142). The `hull3` stage (XT3 B4), which decided three live variables with a unit side
    // exactly, decided 6 more with a point (`live3` decides them since that stage was removed,
    // HULL3-subsumed). Of the 136 systems then refused, 18 have no rational
    // point (cross-review XR3, Q1); the row test of the box stage (Q1-ROWBOX), two rows
    // bounding one variable by rationals that cross, shows 1 of them empty. `live3`, which
    // decides every part left with three variables, decides 13 more with a point and shows one
    // more empty: (274, 5, 121). Exact eliminations counted by the rows they write
    // (`System::shrink`, Q1-LOCAL) decide 7 more with a point and show 2 more empty: (281, 7,
    // 112). The counts measure how much is decided, not correctness, which `run` checks on
    // every system against enumeration.
    assert_eq!(
        (t.sat, t.unsat, t.growth, t.shadows),
        (281, 7, 112, 0),
        "{t:?}"
    );
}

#[test]
fn unit_rows_over_five_variables_match_enumeration() {
    let t = run(0x38_0b, 400, 5, 3, |rng| {
        let rows = 3 + rng.below(6);
        (0..rows)
            .map(|_| {
                let mut c = vec![0; 5];
                let i = rng.below(5);
                c[i] = rng.pick(&[-1, 1]);
                let j = rng.below(5);
                if j != i {
                    c[j] = rng.pick(&[-1, 1]);
                }
                Row {
                    c,
                    k: rng.int(-4, 4),
                }
            })
            .collect()
    });
    assert!(t.sat > 40 && t.unsat > 40, "{t:?}");
    // The parity test decides every such system.
    assert_eq!((t.growth, t.shadows, t.tie), (0, 0, 0), "{t:?}");
}

#[test]
fn large_coefficients_over_two_variables_match_enumeration() {
    let t = run(0x38_0c, 400, 2, 40, |rng| {
        let rows = 2 + rng.below(4);
        small(rng, 2, rows, 60, 400)
    });
    assert!(t.sat > 40 && t.unsat > 40, "{t:?}");
    // Two variables are always decided.
    assert_eq!((t.growth, t.shadows, t.tie), (0, 0, 0), "{t:?}");
}

#[test]
fn rows_over_three_variables_with_a_unit_side_match_enumeration() {
    // 4 to 12 rows over three variables, the last with coefficient ±1 in every row: once no
    // elimination keeps the rows from growing, `live3` decides the three variables exactly, so
    // none is refused. (Until HULL3-subsumed the `hull3` stage projected that variable out
    // first, XT3 B4.)
    let t = run(0x38_0d, 400, 3, 6, |rng| {
        let rows = 4 + rng.below(9);
        (0..rows)
            .map(|_| Row {
                c: vec![rng.int(-7, 7), rng.int(-7, 7), rng.pick(&[-1, 1])],
                k: rng.int(-20, 20),
            })
            .collect()
    });
    assert!(t.sat > 40 && t.unsat > 40, "{t:?}");
    assert_eq!((t.growth, t.shadows, t.tie), (0, 0, 0), "{t:?}");
}

/// 2 to 6 rows of three terms with coefficients up to 5 over `n` variables, half of them met
/// only at a corner of the box `[-half, half]^n`.
pub(super) fn corner_rows(rng: &mut Rng, n: usize, half: i64) -> Vec<Row> {
    let rows = 2 + rng.below(5);
    (0..rows)
        .map(|_| {
            let mut c = vec![0; n];
            let mut placed = 0;
            while placed < 3 {
                let i = rng.below(n);
                if c[i] == 0 {
                    c[i] = rng.int(1, 5) * rng.pick(&[-1, 1]);
                    placed += 1;
                }
            }
            let top: i64 = c.iter().map(|c| c.abs() * half).sum();
            let k = if rng.below(2) == 0 {
                -top
            } else {
                rng.int(-12, 8)
            };
            Row { c, k }
        })
        .collect()
}

#[test]
fn rows_of_three_terms_tight_at_a_corner_match_enumeration() {
    // Most eliminations of these rows are inexact or add terms, so the box of the bounds and
    // its five points decide, with `live3` once three variables are left, and a bound one too
    // tight or a point not checked against every row gives a wrong answer here. 600 systems
    // of a new seed each run; `run` fails at the first wrong answer. The 12,000 systems of
    // seed 0x383b and the counts measured on them are in `bench::oracle` (7.2 s at load 25).
    // About 22% of the systems hold somewhere and 0.2% are refused (2634, 9342 and 24 of the
    // 12,000), so both answers occur here at any seed.
    //
    // A `Shadows` refusal is allowed, and is rare. It is the cause DESIGN.md sec:diagnostics
    // names: a point that could lie only in a splinter that would have to be split again with
    // as many live variables left (step OMEGA-splinter-cap, COMPLEXITY.md S18). Here the dark
    // elimination at four live variables has bound coefficients of 2 to 5, each splinter adds
    // the gap variable and keeps four live variables, and its own dark shadow is empty. Pugh's
    // enumeration of the gap by value would answer it, but at a cost linear in the coefficient
    // values, which the "Limits" paragraph of DESIGN.md excludes (polynomial in rows, not in
    // bit length); enumerating only small gaps would be a size threshold. Measured over 2,500
    // fresh seeds (1,500,000 systems): 10 `Shadows` refusals, never two at one seed, 2 of the
    // 10 systems with a point (`the_refused_corner_systems_are_refused_for_a_splinter`).
    // At that rate three in one run of 600 has odds near 1 in 10^8, so more than two means
    // the refusal has spread past this cause.
    let t = run_fresh("rows of three terms tight at a corner", 600, 4, 3, |rng| {
        corner_rows(rng, 4, 3)
    });
    assert!(t.sat >= 60 && t.unsat >= 300 && t.shadows <= 2, "{t:?}");
}

/// 2 to 5 rows `c·(p·a + q·b) + k >= 0` over `a = x0 + 2·x1` and `b = 2·x2 - 3·x3`, with `c` 1
/// or 2, and `|a|, |b| <= 4` as rows on them: the columns of `x0`, `x1` and of `x2`, `x3` are
/// proportional, the second pair with a negative ratio, and no variable has a bound of its
/// own. The rows as `(c·p, c·q, k)` over `a` and `b`, and the formula with the bound rows.
fn aggregate_rows(rng: &mut Rng) -> (Vec<(i64, i64, i64)>, Formula) {
    let c = 1 + rng.below(2) as i64;
    let mut ab = Vec::new();
    for _ in 0..2 + rng.below(4) {
        ab.push((rng.int(-7, 7), rng.int(-7, 7), rng.int(-12, 12)));
    }
    let lin = |p: i64, q: i64, k: i64| {
        [(0, p), (1, 2 * p), (2, 2 * q), (3, -3 * q)]
            .iter()
            .fold(Lin::constant(k), |l, (i, m)| {
                l.plus(&Lin::atom(name(*i)).times(c * m))
            })
    };
    let mut fs: Vec<Formula> = ab
        .iter()
        .map(|&(p, q, k)| Formula::Con(Con::ge(&lin(p, q, k), &Lin::constant(0))))
        .collect();
    for s in [1, -1] {
        fs.push(Formula::Con(Con::ge(&lin(s, 0, 4 * c), &Lin::constant(0))));
        fs.push(Formula::Con(Con::ge(&lin(0, s, 4 * c), &Lin::constant(0))));
    }
    let ab = ab.into_iter().map(|(p, q, k)| (c * p, c * q, k)).collect();
    (ab, Formula::and(fs))
}

#[test]
fn proportional_columns_match_enumeration_of_their_aggregates() {
    // Each value of `a` and of `b` is taken by some integer point, so the rows have one exactly
    // when some `(a, b)` in [-4, 4]^2 meets every row. Merging the proportional columns leaves
    // two variables, which are always decided: none is refused.
    let mut rng = Rng::new(0x38_3c);
    let mut t = Tally::default();
    for _ in 0..1000 {
        let (ab, f) = aggregate_rows(&mut rng);
        let truth =
            (-4..=4).any(|a| (-4..=4).any(|b| ab.iter().all(|(p, q, k)| p * a + q * b + k >= 0)));
        match satisfiable(&f) {
            Ok(Some(m)) => {
                assert!(truth, "a model of a system with no point: {f}");
                assert!(f.holds(&m), "the model {m:?} fails {f}");
                t.sat += 1;
            }
            Ok(None) => {
                assert!(!truth, "no point found in a system with one: {f}");
                t.unsat += 1;
            }
            Err(r) => panic!("refused with {r:?}: {f}"),
        }
        assert_eq!(decide(&f), Ok(truth), "{f}");
    }
    assert!(t.sat > 100 && t.unsat > 100, "{t:?}");
    eprintln!("aggregates: {t:?}");
}

#[test]
fn answers_do_not_depend_on_names_or_order() {
    // Each system of the four-variable family, its first row an equality in one system of
    // three, its variables renamed by a random permutation to names that sort in another order
    // and its rows shuffled, gets the same answer: the same refusal, or a model exactly when
    // the original has one.
    let mut rng = Rng::new(0x38_0e);
    let (n, half) = (4, 4);
    let mut refused = 0;
    for _ in 0..400 {
        let count = 2 + rng.below(4);
        let rows = small(&mut rng, n, count, 7, 20);
        let eq = rng.below(3) == 0;
        let mut perm: Vec<usize> = (0..n).collect();
        for i in (1..n).rev() {
            perm.swap(i, rng.below(i + 1));
        }
        let mut order: Vec<usize> = (0..rows.len()).collect();
        for i in (1..order.len()).rev() {
            order.swap(i, rng.below(i + 1));
        }
        let system = |name: &dyn Fn(usize) -> Atom, order: &[usize], down: bool| {
            let mut fs: Vec<Formula> = order
                .iter()
                .map(|&r| {
                    let lin = rows[r]
                        .c
                        .iter()
                        .enumerate()
                        .fold(Lin::constant(rows[r].k), |l, (i, c)| {
                            l.plus(&Lin::atom(name(i)).times(*c))
                        });
                    let zero = Lin::constant(0);
                    Formula::Con(if eq && r == 0 {
                        Con::eq(&lin, &zero)
                    } else {
                        Con::ge(&lin, &zero)
                    })
                })
                .collect();
            let vars: Vec<usize> = if down {
                (0..n).rev().collect()
            } else {
                (0..n).collect()
            };
            for i in vars {
                let x = Lin::atom(name(i));
                fs.push(Formula::Con(Con::ge(&x, &Lin::constant(-half))));
                fs.push(Formula::Con(Con::ge(&Lin::constant(half), &x)));
            }
            Formula::and(fs)
        };
        let named = |i: usize| Atom::Sym(Arc::from(format!("x{i}")));
        let f = system(&named, &(0..rows.len()).collect::<Vec<_>>(), false);
        let renamed = |i: usize| Atom::Sym(Arc::from(format!("z{}", n - perm[i])));
        let g = system(&renamed, &order, true);
        let (a, b) = (decide(&f), decide(&g));
        // A tie names its variables, which the renaming changes: two ties are the same answer
        // when they name as many variables and rows.
        let same = match (&a, &b) {
            (Err(Refusal::Tie(s)), Err(Refusal::Tie(t))) => {
                (s.vars.len(), s.rows.len()) == (t.vars.len(), t.rows.len())
            }
            _ => a == b,
        };
        assert!(same, "{f}\nrenamed and reordered: {g}\n{a:?}\n{b:?}");
        refused += usize::from(a.is_err());
    }
    // The refusals are among the answers compared: 73 until Q1-LOCAL, whose exact eliminations
    // counted by the rows they write (`System::shrink`) decide 9 more.
    assert_eq!(refused, 64);
}

#[test]
fn a_model_past_the_box_needs_no_box() {
    // Unbounded systems have no enumeration; their models are checked.
    let mut rng = Rng::new(0x38_0d);
    for _ in 0..200 {
        let rows = small(&mut rng, 3, 3, 9, 30);
        let fs: Vec<Formula> = rows
            .iter()
            .map(|r| {
                let lin =
                    r.c.iter()
                        .enumerate()
                        .fold(Lin::constant(r.k), |l, (i, c)| {
                            l.plus(&Lin::atom(name(i)).times(*c))
                        });
                Formula::Con(Con::ge(&lin, &Lin::constant(0)))
            })
            .collect();
        let f = Formula::and(fs);
        if let Ok(Some(m)) = satisfiable(&f) {
            assert!(f.holds(&m), "{m:?} fails {f}");
        }
    }
}

/// The rows, each `Σ c·x + k >= 0`, and the bounds `-half <= x <= half` of each variable after
/// them, as one formula taken in `order`, with variable `i` named `names[i]`.
fn named(rows: &[Row], half: i64, names: &[Arc<str>], order: &[usize]) -> Formula {
    let x = |i: usize| Lin::atom(Atom::Sym(names[i].clone()));
    let fs = order
        .iter()
        .map(|&r| {
            let con = match r.checked_sub(rows.len()) {
                None => {
                    let lin = rows[r]
                        .c
                        .iter()
                        .enumerate()
                        .fold(Lin::constant(rows[r].k), |l, (i, c)| {
                            l.plus(&x(i).times(*c))
                        });
                    Con::ge(&lin, &Lin::constant(0))
                }
                Some(b) if b % 2 == 0 => Con::ge(&x(b / 2), &Lin::constant(-half)),
                Some(b) => Con::ge(&Lin::constant(half), &x(b / 2)),
            };
            Formula::Con(con)
        })
        .collect();
    Formula::and(fs)
}

/// Calls `visit` with every permutation of `0..n`, by Heap's algorithm, and returns how many
/// there were.
fn each_permutation(n: usize, mut visit: impl FnMut(&[usize])) -> usize {
    let mut perm: Vec<usize> = (0..n).collect();
    visit(&perm);
    let mut count = 1;
    let mut c = vec![0; n];
    let mut i = 1;
    while i < n {
        if c[i] < i {
            perm.swap(if i % 2 == 0 { 0 } else { c[i] }, i);
            visit(&perm);
            count += 1;
            c[i] += 1;
            i = 1;
        } else {
            c[i] = 0;
            i += 1;
        }
    }
    count
}

/// Decides `count` systems from `make`, drawn from `rng`, over `n` variables in the box
/// `[-half, half]^n`; when `compare`, decides each again under every naming of its variables:
/// `n` random names given to the variables in each of the `n!` orders, so that the names sort
/// in every order, with the rows and bounds shuffled anew each time; when `n! < 4` the orders
/// are run again, so each system is shuffled at least four times. Fails at the first answer
/// that changes. Returns the refusals, which are among the answers compared. Without
/// `compare` the names and orders are drawn all the same, so that a seed gives the same
/// systems either way.
fn reorderings(
    rng: &mut Rng,
    count: usize,
    n: usize,
    half: i64,
    compare: bool,
    make: impl Fn(&mut Rng) -> Vec<Row>,
) -> usize {
    let plain: Vec<Arc<str>> = (0..n).map(|i| Arc::from(format!("v{i}"))).collect();
    let mut refused = 0;
    for _ in 0..count {
        let rows = make(rng);
        let all = rows.len() + 2 * n;
        let f = named(&rows, half, &plain, &(0..all).collect::<Vec<_>>());
        let a = decide(&f);
        refused += usize::from(a.is_err());
        let mut drawn: Vec<Arc<str>> = Vec::new();
        while drawn.len() < n {
            let prefix = rng.pick(&["q", "b", "zz", "a", "m"]);
            let s: Arc<str> = Arc::from(format!("{prefix}{}", rng.below(1000)));
            if !drawn.contains(&s) {
                drawn.push(s);
            }
        }
        // At least four row orders per system: the namings run again until four have run.
        let all_namings = (1..=n).product::<usize>();
        for _ in 0..4usize.div_ceil(all_namings) {
            let namings = each_permutation(n, |perm| {
                let mut order: Vec<usize> = (0..all).collect();
                for i in (1..all).rev() {
                    order.swap(i, rng.below(i + 1));
                }
                if compare {
                    let names: Vec<Arc<str>> = perm.iter().map(|&p| drawn[p].clone()).collect();
                    let g = named(&rows, half, &names, &order);
                    assert_eq!(a, decide(&g), "{f}\nrenamed and reordered: {g}");
                }
            });
            assert_eq!(namings, all_namings);
        }
    }
    refused
}

/// [`reorderings`] of `count` systems drawn with a new seed each run (author P169: random
/// tests run few cases, with a new seed each run).
fn fresh_reorderings(
    what: &str,
    count: usize,
    n: usize,
    half: i64,
    make: impl Fn(&mut Rng) -> Vec<Row>,
) -> usize {
    let (mut rng, _) = Rng::fresh(what);
    reorderings(&mut rng, count, n, half, true, make)
}

/// The refusals among the first `count` systems of [`reorderings`] at `seed`, each decided
/// once.
pub(super) fn refusals_at(
    seed: u64,
    count: usize,
    n: usize,
    half: i64,
    make: impl Fn(&mut Rng) -> Vec<Row>,
) -> usize {
    reorderings(&mut Rng::new(seed), count, n, half, false, make)
}

// 198,000 renamed and reordered systems ran in all at fixed seeds, 46 s: 72,000 and 96,000 in
// the two four-variable families, 18,000 over three variables and 12,000 over two (each of the
// two namings twice). Now each test draws a few systems with a new seed each run, and the
// refusals among the systems at the old seeds, each decided once, are counted apart. The
// four-variable families check that the five points of the box stage, which are computed on
// the rows left after the eliminations, give no answer that depends on the names (XT3 report,
// part E).

pub(super) fn small_coefficients(rng: &mut Rng) -> Vec<Row> {
    let rows = 2 + rng.below(4);
    small(rng, 4, rows, 7, 20)
}

#[test]
fn small_coefficients_answer_the_same_under_any_names_and_order() {
    fresh_reorderings("small coefficients", 60, 4, 4, small_coefficients);
}

#[test]
fn small_coefficients_over_four_variables_are_refused_81_times_in_300() {
    // The first 300 systems of the 3000 in `bench::oracle` (839 refused there).
    assert_eq!(refusals_at(0x38_40, 300, 4, 4, small_coefficients), 81);
}

#[test]
fn rows_of_three_terms_answer_the_same_under_any_names_and_order() {
    fresh_reorderings("rows of three terms", 60, 4, 3, |rng| {
        corner_rows(rng, 4, 3)
    });
}

#[test]
fn rows_of_three_terms_over_four_variables_are_refused_3_times_in_1000() {
    // The first 1000 systems of the 4000 in `bench::oracle` (13 refused there, with the history
    // of that count).
    assert_eq!(
        refusals_at(0x38_41, 1000, 4, 3, |rng| corner_rows(rng, 4, 3)),
        3
    );
}

pub(super) fn three_variables(rng: &mut Rng) -> Vec<Row> {
    let rows = 2 + rng.below(4);
    small(rng, 3, rows, 9, 30)
}

#[test]
fn rows_over_three_variables_answer_the_same_under_any_names_and_order() {
    // The first 300 systems of the fixed seed here; all 3000 are in `bench::oracle`.
    assert_eq!(
        fresh_reorderings("rows over three variables", 200, 3, 3, three_variables),
        0
    );
    assert_eq!(refusals_at(0x38_42, 300, 3, 3, three_variables), 0);
}

pub(super) fn large_coefficients(rng: &mut Rng) -> Vec<Row> {
    let rows = 2 + rng.below(4);
    small(rng, 2, rows, 60, 400)
}

#[test]
fn large_coefficients_answer_the_same_under_any_names_and_order() {
    // The first 300 systems of the fixed seed here; all 3000 are in `bench::oracle`.
    assert_eq!(
        fresh_reorderings("large coefficients", 300, 2, 40, large_coefficients),
        0
    );
    assert_eq!(refusals_at(0x38_43, 300, 2, 40, large_coefficients), 0);
}

/// Sixteen rows `a·v - 1 >= 0` over eight variables, each with two coefficients 6 and one -5:
/// they hold at `v = (1, ..., 1)`, where each is 6, and every elimination adds terms.
const REGULAR: [[i64; 8]; 16] = [
    [0, 6, 0, 0, 0, 0, 6, -5],
    [0, 0, 0, 0, -5, 6, 0, 6],
    [-5, 0, 0, 6, 6, 0, 0, 0],
    [6, -5, 6, 0, 0, 0, 0, 0],
    [0, 6, 0, 0, 0, -5, 6, 0],
    [0, 0, 0, -5, 0, 6, 0, 6],
    [0, 0, -5, 6, 6, 0, 0, 0],
    [6, 0, 6, 0, 0, 0, -5, 0],
    [6, 0, 0, 6, 0, 0, -5, 0],
    [0, 0, 6, 0, 6, -5, 0, 0],
    [-5, 6, 0, 0, 0, 0, 0, 6],
    [0, 0, -5, 6, 0, 0, 6, 0],
    [0, 0, 0, 0, 6, 6, 0, -5],
    [6, 6, 0, -5, 0, 0, 0, 0],
    [0, 0, 6, 0, -5, 0, 6, 0],
    [0, -5, 0, 0, 0, 6, 0, 6],
];

fn regular() -> Vec<Row> {
    REGULAR
        .iter()
        .map(|c| Row {
            c: c.to_vec(),
            k: -1,
        })
        .collect()
}

#[test]
fn a_regular_system_is_decided_under_every_naming() {
    // 400 of the 8! namings of the variables, drawn with a new seed each run (author P169;
    // all 40,320 took 13 s), in the box [-1, 1]^8. Before design R the answer changed with the
    // names (cross-review xt, round 2); with only the point nearest zero every naming was
    // refused with Growth. The upper corner of the box, (1, ..., 1), holds every row, and every
    // naming finds it.
    let rows = regular();
    let all: Vec<usize> = (0..rows.len() + 16).collect();
    let (mut rng, seed) = Rng::fresh("namings of the regular system");
    for _ in 0..400 {
        let mut perm: Vec<usize> = (0..8).collect();
        for i in (1..8).rev() {
            perm.swap(i, rng.below(i + 1));
        }
        let names: Vec<Arc<str>> = perm.iter().map(|p| Arc::from(format!("v{p}"))).collect();
        let f = named(&rows, 1, &names, &all);
        assert_eq!(decide(&f), Ok(true), "seed {seed}: {f}");
    }
}

/// The points of the box `[-1, 1]^8` that meet every row.
fn points_of_the_unit_box(rows: &[Row]) -> Vec<Vec<i64>> {
    (0..3i64.pow(8))
        .map(|code| (0..8).map(|i| code / 3i64.pow(i) % 3 - 1).collect())
        .filter(|p: &Vec<i64>| {
            rows.iter()
                .all(|r| r.c.iter().zip(p).map(|(c, v)| c * v).sum::<i64>() + r.k >= 0)
        })
        .collect()
}

#[test]
fn a_system_whose_only_point_is_the_upper_corner_has_that_point() {
    // In the box [-1, 1]^8 the regular rows hold at 38 points, each in {0, 1}^8. The rows
    // `v[i] + v[i + 1] - v[i + 2] >= 1` around the cycle of 8 leave only (1, ..., 1): a 0 at
    // `v[j]` needs `v[j + 1] = 0` by row `j - 1`, and then `v[j + 2] = -1` by row `j`. No one
    // row moves a bound of the box, so the box stage sees all of [-1, 1]^8; the point nearest
    // zero and the lower corner miss, the midpoints are the point nearest zero, and the upper
    // corner is the one point of the five that holds.
    let mut rows = regular();
    let points = points_of_the_unit_box(&rows);
    assert_eq!(points.len(), 38);
    assert!(points.iter().flatten().all(|v| *v >= 0));
    rows.extend((0..8).map(|i| {
        let mut c = vec![0; 8];
        c[i] = 1;
        c[(i + 1) % 8] = 1;
        c[(i + 2) % 8] = -1;
        Row { c, k: -1 }
    }));
    assert_eq!(points_of_the_unit_box(&rows), [vec![1; 8]]);
    let f = formula(&rows, 8, 1);
    let m = satisfiable(&f).expect("answered").expect("a point");
    assert!(f.holds(&m), "{m:?} fails {f}");
}

/// Seed 12228408859946558652 of FAIL-tight-corner-shadows-seed: system 233 is refused with
/// `Shadows`, the refusal DESIGN.md allows (the comment in
/// `rows_of_three_terms_tight_at_a_corner_match_enumeration` says why), and every other
/// system is answered as enumeration answers it.
#[test]
fn rows_of_three_terms_tight_at_a_corner_of_seed_12228408859946558652_match_enumeration() {
    let t = run(12228408859946558652, 600, 4, 3, |rng| {
        corner_rows(rng, 4, 3)
    });
    assert_eq!(
        (t.sat, t.unsat, t.growth, t.shadows, t.tie),
        (122, 477, 0, 1, 0),
        "{t:?}"
    );
}

/// Systems of rows tight at a corner that `decide` and `satisfiable` refuse with `Shadows`, the
/// cause DESIGN.md sec:diagnostics names: the dark elimination at four live variables splinters,
/// each splinter keeps four live variables, and its own dark shadow is empty. The first three
/// are the refused systems of the seeds of FAIL-tight-corner-shadows-seed (12228408859946558652
/// system 233, 15956874539988706693 system 30, 9658193861429432057 system 155); the next two
/// are those of seeds 1178677564335123856 (system 25) and 16004174331354764304 (system 222),
/// which have points; the last two are the first and third made smaller, a row or a coefficient
/// at a time, while the refusal stayed. The refusal can stand where there is a point.
#[test]
fn the_refused_corner_systems_are_refused_for_a_splinter() {
    type Case = (i64, &'static [([i64; 4], i64)], bool);
    let cases: [Case; 7] = [
        (
            3,
            &[
                ([-2, 3, 0, -3], -7),
                ([2, 0, 3, 3], 7),
                ([3, -3, -4, 0], -10),
            ],
            false,
        ),
        (
            3,
            &[
                ([-5, 0, -3, 3], -4),
                ([-4, -4, 0, 5], 2),
                ([-3, 0, 5, 4], 6),
                ([4, 5, 0, -3], -11),
            ],
            false,
        ),
        (
            3,
            &[
                ([-3, 0, -5, -3], -11),
                ([0, 3, 4, 5], 3),
                ([5, -5, 0, 3], -12),
            ],
            false,
        ),
        (
            3,
            &[
                ([0, 2, 5, -3], -6),
                ([5, 2, 0, 3], 3),
                ([-5, -4, -2, 0], -6),
            ],
            true,
        ),
        (
            3,
            &[
                ([0, 5, -5, 2], -7),
                ([5, -3, 0, 5], -9),
                ([-5, 1, 0, 1], -4),
                ([0, 4, 3, -3], 4),
            ],
            true,
        ),
        (
            3,
            &[
                ([-2, 3, 0, -2], -6),
                ([1, 0, 3, 3], 3),
                ([3, -3, -4, 0], -1),
            ],
            false,
        ),
        (
            1,
            &[([-2, 0, -2, -3], 0), ([0, 3, 3, 2], 0), ([4, -3, 0, 2], -1)],
            true,
        ),
    ];
    for (half, rows, point) in cases {
        let rows: Vec<Row> = rows
            .iter()
            .map(|(c, k)| Row {
                c: c.to_vec(),
                k: *k,
            })
            .collect();
        let f = formula(&rows, 4, half);
        assert_eq!(enumerate(&rows, 4, half), point, "{f}: enumeration");
        assert_eq!(decide(&f), Err(Refusal::Shadows), "{f}: decide");
        assert_eq!(satisfiable(&f), Err(Refusal::Shadows), "{f}: satisfiable");
    }
}
