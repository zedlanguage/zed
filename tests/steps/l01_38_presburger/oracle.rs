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
    // counted, not required to be absent, and each is a cause of its own.
    assert!(t.sat > 40 && t.unsat > 10, "{t:?}");
    eprintln!("four variables: {t:?}");
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
