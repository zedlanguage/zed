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
struct Row {
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
struct Tally {
    sat: usize,
    unsat: usize,
    growth: usize,
    shadows: usize,
}

/// Checks `count` random systems from `make` against enumeration.
fn run(seed: u64, count: usize, n: usize, half: i64, make: impl Fn(&mut Rng) -> Vec<Row>) -> Tally {
    let mut rng = Rng::new(seed);
    let mut t = Tally::default();
    for _ in 0..count {
        let rows = make(&mut rng);
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
            Err(Refusal::Disjuncts) => panic!("a conjunction refused for its disjunctions: {f}"),
        }
        assert_eq!(
            decide(&f),
            got.as_ref().map(Option::is_some).map_err(|r| *r),
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
    // L1.38): the counts are those measured with design R, which has no linear program. Before
    // it more than 10 of these systems were shown empty; now 3 are, and the systems the
    // program decided are refused with Growth. The counts measure how much is decided, not
    // correctness, which `run` checks on every system against enumeration.
    assert_eq!(
        (t.sat, t.unsat, t.growth, t.shadows),
        (213, 3, 184, 0),
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
    assert_eq!((t.growth, t.shadows), (0, 0), "{t:?}");
}

#[test]
fn large_coefficients_over_two_variables_match_enumeration() {
    let t = run(0x38_0c, 400, 2, 40, |rng| {
        let rows = 2 + rng.below(4);
        small(rng, 2, rows, 60, 400)
    });
    assert!(t.sat > 40 && t.unsat > 40, "{t:?}");
    // Two variables are always decided.
    assert_eq!((t.growth, t.shadows), (0, 0), "{t:?}");
}

/// 2 to 6 rows of three terms with coefficients up to 5 over `n` variables, half of them met
/// only at a corner of the box `[-half, half]^n`.
fn corner_rows(rng: &mut Rng, n: usize, half: i64) -> Vec<Row> {
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
    // No elimination of these rows is exact, so the box of the bounds and the point nearest
    // zero in it decide, and a bound one too tight or a point not checked against every row
    // gives a wrong answer here. 12,000 systems; `run` fails at the first wrong answer.
    let t = run(0x38_3b, 12_000, 4, 3, |rng| corner_rows(rng, 4, 3));
    // The counts measured with design R. Without the box test 5,074 are refused (control run
    // once, STATUS.md, L1.38); the box shows most of the empty ones empty.
    assert_eq!(
        (t.sat, t.unsat, t.growth, t.shadows),
        (2550, 9282, 168, 0),
        "{t:?}"
    );
    eprintln!("three terms: {t:?}");
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
        assert_eq!(a, b, "{f}\nrenamed and reordered: {g}");
        refused += usize::from(a.is_err());
    }
    // The refusals are among the answers compared.
    assert!(refused > 10, "{refused}");
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

/// Decides 3000 systems from `make` over `n` variables in the box `[-half, half]^n`, then each
/// again 4 times with its variables renamed at random to names that sort in another order and
/// its rows and bounds shuffled, and fails at the first answer that changes. The refusals, which
/// are among the answers compared.
fn reorderings(seed: u64, n: usize, half: i64, make: impl Fn(&mut Rng) -> Vec<Row>) -> usize {
    let mut rng = Rng::new(seed);
    let plain: Vec<Arc<str>> = (0..n).map(|i| Arc::from(format!("v{i}"))).collect();
    let mut refused = 0;
    for _ in 0..3000 {
        let rows = make(&mut rng);
        let all = rows.len() + 2 * n;
        let f = named(&rows, half, &plain, &(0..all).collect::<Vec<_>>());
        let a = decide(&f);
        refused += usize::from(a.is_err());
        for _ in 0..4 {
            let mut names: Vec<Arc<str>> = Vec::new();
            while names.len() < n {
                let prefix = rng.pick(&["q", "b", "zz", "a", "m"]);
                let s: Arc<str> = Arc::from(format!("{prefix}{}", rng.below(1000)));
                if !names.contains(&s) {
                    names.push(s);
                }
            }
            let mut order: Vec<usize> = (0..all).collect();
            for i in (1..all).rev() {
                order.swap(i, rng.below(i + 1));
            }
            let g = named(&rows, half, &names, &order);
            assert_eq!(a, decide(&g), "{f}\nrenamed and reordered: {g}");
        }
    }
    refused
}

// 48,000 renamed and reordered systems in all, 12,000 of each family.

#[test]
fn small_coefficients_answer_the_same_under_any_names_and_order() {
    let refused = reorderings(0x38_40, 4, 4, |rng| {
        let rows = 2 + rng.below(4);
        small(rng, 4, rows, 7, 20)
    });
    assert!(refused > 100, "{refused}");
}

#[test]
fn rows_of_three_terms_answer_the_same_under_any_names_and_order() {
    let refused = reorderings(0x38_41, 4, 3, |rng| corner_rows(rng, 4, 3));
    assert!(refused > 20, "{refused}");
}

#[test]
fn rows_over_three_variables_answer_the_same_under_any_names_and_order() {
    let refused = reorderings(0x38_42, 3, 3, |rng| {
        let rows = 2 + rng.below(4);
        small(rng, 3, rows, 9, 30)
    });
    eprintln!("three variables: {refused} refused");
}

#[test]
fn large_coefficients_answer_the_same_under_any_names_and_order() {
    let refused = reorderings(0x38_43, 2, 40, |rng| {
        let rows = 2 + rng.below(4);
        small(rng, 2, rows, 60, 400)
    });
    assert_eq!(refused, 0);
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

#[test]
fn a_regular_system_answers_the_same_under_every_naming() {
    // All 8! namings of the variables, in the box [-1, 1]^8, by Heap's algorithm. Before
    // design R the answer changed with the names (cross-review xt, round 2); now every naming
    // is refused with Growth, though the rows hold at (1, ..., 1).
    let rows: Vec<Row> = REGULAR
        .iter()
        .map(|c| Row {
            c: c.to_vec(),
            k: -1,
        })
        .collect();
    let all: Vec<usize> = (0..rows.len() + 16).collect();
    let mut perm: Vec<usize> = (0..8).collect();
    let answer = |perm: &[usize]| {
        let names: Vec<Arc<str>> = perm.iter().map(|p| Arc::from(format!("v{p}"))).collect();
        let f = named(&rows, 1, &names, &all);
        assert_eq!(decide(&f), Err(Refusal::Growth), "{f}");
    };
    answer(&perm);
    let mut count = 1;
    let mut c = [0usize; 8];
    let mut i = 1;
    while i < 8 {
        if c[i] < i {
            perm.swap(if i % 2 == 0 { 0 } else { c[i] }, i);
            answer(&perm);
            count += 1;
            c[i] += 1;
            i = 1;
        } else {
            c[i] = 0;
            i += 1;
        }
    }
    assert_eq!(count, 40_320);
}
