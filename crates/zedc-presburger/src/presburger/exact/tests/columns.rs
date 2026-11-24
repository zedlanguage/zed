//! XR-cover-hybrid round 3 tests (Opus seat, P328): column classes in `exact_each`
//! (`by_columns`) and the shared written text of `deep::show` and `written_names`. In a file
//! of their own so that tests appended to `tests.rs` do not conflict with them.

use super::*;
use crate::seed::Rng;

/// The names `z0` to `z{k-1}`.
fn zs(k: usize) -> Vec<String> {
    (0..k).map(|i| format!("z{i}")).collect()
}

/// The shape of the formulas of `families::bench::wide` (the probe of round 3 printed them):
/// `S >= -1000 && (z0 <= -1 || S >= 1)` for S the sum of z0 to z{k-1}, and where `bounded`
/// also `y == S` and `0 <= S <= 10`. z1 to z{k-1} have one column; z0 and y each have their own.
fn wide_sum(k: usize, bounded: bool) -> Formula {
    let names = zs(k);
    let sum: Vec<(&str, i64)> = names.iter().map(|n| (n.as_str(), 1)).collect();
    let mut all = vec![
        ge(&sum, 1000),
        Formula::or(vec![ge(&[("z0", -1)], -1), ge(&sum, -1)]),
    ];
    if bounded {
        let mut with_y = sum.clone();
        with_y.push(("y", -1));
        all.push(eq(&with_y, 0));
        all.push(ge(&sum, 0));
        let neg: Vec<(&str, i64)> = names.iter().map(|n| (n.as_str(), -1)).collect();
        all.push(ge(&neg, 10));
    }
    Formula::and(all)
}

/// `f` and, for each atom named, the always-true `n >= 0 || n <= -1`: the same set of points,
/// with every atom named given a column of its own, so no two atoms named share a column.
fn columns_broken(f: Formula, names: &[String]) -> Formula {
    let mut all = vec![f];
    for n in names {
        all.push(Formula::or(vec![
            ge(&[(n.as_str(), 1)], 0),
            ge(&[(n.as_str(), -1)], -1),
        ]));
    }
    Formula::and(all)
}

fn asked(names: &[String]) -> Vec<Atom> {
    names.iter().map(|n| a(n)).collect()
}

/// The answers where atoms share a column are those of the same formula with every column
/// apart, and are the exact projections: every integer for each z, and 0 to 10 for y where S
/// is bounded. Holds before and after T2 (both answers come from the covers there); after T2
/// the first answer comes from `by_columns`, so this compares the two paths.
#[test]
fn a_sum_row_answers_as_with_its_columns_apart() {
    for k in [2, 3, 5, 9] {
        for bounded in [false, true] {
            let mut names = zs(k);
            if bounded {
                names.push("y".into());
            }
            let f = wide_sum(k, bounded);
            let syms = asked(&names);
            let got = project_each_exact(&f, &syms).unwrap();
            let apart = project_each_exact(&columns_broken(f, &names), &syms).unwrap();
            assert_eq!(got, apart, "k {k}, bounded {bounded}");
            for (n, r) in names.iter().zip(&got.0) {
                let want = if n == "y" {
                    IntervalSet::of(0, 10)
                } else {
                    IntervalSet::top()
                };
                assert_eq!(r.as_ref().unwrap(), &want, "{n}, k {k}, bounded {bounded}");
            }
            assert!(got.1.is_empty(), "{:?}", got.1);
        }
    }
}

/// A class with no point: `(S >= 1 && S <= 0) || (S >= 3 && S <= 2)` over z0 to z3 in one
/// column. Every member is empty. Note (measured with a mutation, REPORT.md): this answer comes
/// from the solver's empty set, which `exact_each` returns before `by_columns` runs, so it does
/// not exercise `by_columns`' empty branch; that branch runs only where the solver's set is
/// nonempty and f has no point, and no test here reaches it.
#[test]
fn a_class_with_no_point_answers_empty() {
    let names = zs(4);
    let sum: Vec<(&str, i64)> = names.iter().map(|n| (n.as_str(), 1)).collect();
    let neg: Vec<(&str, i64)> = names.iter().map(|n| (n.as_str(), -1)).collect();
    let f = Formula::or(vec![
        Formula::and(vec![ge(&sum, -1), ge(&neg, 0)]),
        Formula::and(vec![ge(&sum, -3), ge(&neg, 2)]),
    ]);
    let got = project_each_exact(&f, &asked(&names)).unwrap();
    for r in &got.0 {
        assert_eq!(r.as_ref().unwrap(), &IntervalSet::empty());
    }
}

/// Random formulas over x and y, boxed to -B..=B, and the sum `c * (u + v)` of two unboxed
/// atoms u and v that only ever appear together with one coefficient c per row: u and v are a
/// class. The answers for x, y, u and v are those of the formula with the columns apart, and
/// x's and y's are those found by trying every point of the formula with u + v replaced by one
/// atom z (the rows `-B <= u + v <= B` make z's box -B..=B exact), u's and v's every integer
/// where that formula has a point and none where it has none. Caught the mutation that answers a
/// member with m's own set (REPORT.md).
#[test]
fn random_classes_answer_as_with_their_columns_apart() {
    let (mut rng, _) = Rng::fresh("random_classes_answer_as_with_their_columns_apart");
    let names: Vec<String> = ["x", "y", "u", "v"].iter().map(|s| s.to_string()).collect();
    for _ in 0..300 {
        let leaf = |rng: &mut Rng| {
            let c = rng.int(-2, 2);
            let terms = [
                ("x", rng.int(-3, 3)),
                ("y", rng.int(-3, 3)),
                ("u", c),
                ("v", c),
            ];
            let k = rng.int(-6, 6);
            if rng.below(4) == 0 {
                eq(&terms, k)
            } else {
                ge(&terms, k)
            }
        };
        let mut arms = Vec::new();
        for _ in 0..rng.int(1, 3) {
            let rows: Vec<Formula> = (0..rng.int(1, 3)).map(|_| leaf(&mut rng)).collect();
            arms.push(if rng.below(3) == 0 {
                Formula::Not(Shared::new(Formula::and(rows)))
            } else {
                Formula::and(rows)
            });
        }
        let sum_box = Formula::and(vec![
            ge(&[("u", 1), ("v", 1)], B),
            ge(&[("u", -1), ("v", -1)], B),
        ]);
        let f = Formula::and(vec![
            member(&a("x"), &IntervalSet::of(-B, B)),
            member(&a("y"), &IntervalSet::of(-B, B)),
            sum_box,
            Formula::or(arms),
        ]);
        let syms = asked(&names);
        let got = project_each_exact(&f, &syms).unwrap();
        let apart = project_each_exact(&columns_broken(f.clone(), &names), &syms).unwrap();
        assert_eq!(got, apart, "{f}");
        // The oracle for x and y: u + v is any value s in -B..=B, so `f` with u + v as z.
        let z = f.map_cons(&|c| {
            let mut c = c.clone();
            if let Some(k) = c.lin.terms.remove(&a("u")) {
                c.lin.terms.remove(&a("v"));
                c.lin.terms.insert(a("z"), k);
            }
            Formula::Con(c)
        });
        for (i, n) in ["x", "y"].iter().enumerate() {
            if let Ok(set) = &got.0[i] {
                assert_eq!(set, &brute(&z, n), "{n} of {f}");
            }
        }
        let some = !brute(&z, "x").is_empty();
        for i in [2, 3] {
            if let Ok(set) = &got.0[i] {
                let want = if some {
                    IntervalSet::top()
                } else {
                    IntervalSet::empty()
                };
                assert_eq!(set, &want, "{} of {f}", names[i]);
            }
        }
    }
}

/// The exact work of one call over the sum row of `wide` grows at most near-linearly in its
/// width: under 8 times from k = 32 to k = 128 (4 times the width). Before T2 each of the k
/// symbols read the k-term row, 14.1 times (949,300 to 13,356,200, measured); after it, the
/// rows have one term per class, 1.0 times (15,000 to 14,900, measured).
#[test]
fn the_work_of_a_sum_row_is_near_linear_in_its_width() {
    let work = |k: usize| {
        let mut names = zs(k);
        names.push("y".into());
        EXACT_WORK.set(0);
        let got = project_each_exact(&wide_sum(k, true), &asked(&names)).unwrap();
        assert!(got.0.iter().all(|r| r.is_ok()), "k {k}: {:?}", got.0);
        EXACT_WORK.replace(0)
    };
    let (small, large) = (work(32), work(128));
    assert!(large < 8 * small, "{small} at 32, {large} at 128");
}

/// A random constraint over a few names, some of them prefixes of others (`a`, `a1`, `a@2`),
/// a product and an auxiliary atom among them.
fn named_con(rng: &mut Rng) -> Formula {
    const SYMS: [&str; 6] = ["a", "a1", "a@2", "b_c", "q", "q1"];
    let mut terms: std::collections::BTreeMap<Atom, Int> = std::collections::BTreeMap::new();
    for _ in 0..rng.int(0, 3) {
        let atom = match rng.below(8) {
            0 => Atom::product(&SYMS[rng.below(6)].into(), &SYMS[rng.below(6)].into()),
            1 => Atom::Aux(rng.below(3) as u32),
            _ => a(SYMS[rng.below(6)]),
        };
        let sign = if rng.below(2) == 0 { 1 } else { -1 };
        terms.insert(atom, Int::from(sign * rng.int(1, 3)));
    }
    let l = Lin {
        terms,
        constant: Int::from(rng.int(-5, 5)),
    };
    Formula::Con(if rng.below(3) == 0 {
        Con::eq(&l, &Lin::constant(0))
    } else {
        Con::ge(&l, &Lin::constant(0))
    })
}

/// A random DAG: a pool of nodes, each new one a `Not`, `And` or `Or` (empty ones included) of
/// nodes already in the pool, so later nodes share earlier ones. Built with `Shared::new`
/// directly, not `Formula::and`, so that no simplification hides the sharing.
fn shared_dag(rng: &mut Rng, nodes: usize) -> Formula {
    let mut pool: Vec<Formula> = (0..4).map(|_| named_con(rng)).collect();
    for _ in 0..nodes {
        let pick = |rng: &mut Rng, pool: &Vec<Formula>| pool[rng.below(pool.len())].clone();
        let g = match rng.below(5) {
            0 => Formula::Not(Shared::new(pick(rng, &pool))),
            k => {
                let n = rng.below(4);
                let kids: Vec<Formula> = (0..n).map(|_| pick(rng, &pool)).collect();
                if k % 2 == 0 {
                    Formula::And(Shared::new(kids))
                } else {
                    Formula::Or(Shared::new(kids))
                }
            }
        };
        pool.push(g);
        if rng.below(3) == 0 {
            pool.push(named_con(rng));
        }
    }
    pool.pop().unwrap()
}

/// `f` with every compound node made anew: the same tree, no part held twice.
fn unshared(f: &Formula) -> Formula {
    match f {
        Formula::Con(c) => Formula::Con(c.clone()),
        Formula::Not(h) => Formula::Not(Shared::new(unshared(h))),
        Formula::And(gs) => Formula::And(Shared::new(gs.iter().map(unshared).collect())),
        Formula::Or(gs) => Formula::Or(Shared::new(gs.iter().map(unshared).collect())),
        // A call node is a leaf: it holds no part.
        Formula::Holes(_) => f.clone(),
    }
}

fn first_name(s: &str) -> &str {
    s.split('@').next().unwrap()
}

/// The text of a DAG, written with a part's text copied where it is held again, is the text of
/// the same tree with no part shared, in `Display`, `Debug` and `written` under two namings.
/// Passes before T3 too (both texts written in full there); after T3 it compares the copied
/// text with the text written in full.
#[test]
fn a_shared_part_is_written_as_if_written_again() {
    let (mut rng, _) = Rng::fresh("a_shared_part_is_written_as_if_written_again");
    for _ in 0..400 {
        let nodes = 1 + rng.below(12);
        let f = shared_dag(&mut rng, nodes);
        let g = unshared(&f);
        assert_eq!(f.to_string(), g.to_string());
        assert_eq!(format!("{f:?}"), format!("{g:?}"));
        assert_eq!(f.written(first_name), g.written(first_name));
        assert_eq!(f.written(|s| s), g.written(|s| s));
    }
}

/// The names `written_names` finds are those `names_in` finds in the text of `written`, under
/// two namings, products and auxiliary atoms (`q0`) included. New with T3: `written_names` is
/// not in the tree before it.
#[test]
fn the_names_of_the_constraints_are_the_names_of_the_text() {
    let (mut rng, _) = Rng::fresh("the_names_of_the_constraints_are_the_names_of_the_text");
    for _ in 0..400 {
        let nodes = rng.below(13);
        let f = shared_dag(&mut rng, nodes);
        for name in [first_name as fn(&str) -> &str, |s| s] {
            let text = f.written(name);
            let want: HashSet<String> = (crate::presburger::names_in(&text).into_iter())
                .map(String::from)
                .collect();
            assert_eq!(f.written_names(name), want, "{text}");
        }
    }
}

/// A part held twice at each of 64 levels, `x_i >= 0 && (p || !p)` for the part p below: the
/// tree written out has about 2^64 constraints, the DAG 64. `written_names` reads the 64. Before
/// T3 the only route to the names was `names_in` of the text, which cannot be written.
#[test]
fn a_part_held_twice_at_each_of_64_levels_names_its_atoms() {
    let mut p = Formula::Con(Con::ge(&lin(&[("x0", 1)], 0), &Lin::constant(0)));
    for i in 1..64 {
        let c = Formula::Con(Con::ge(
            &lin(&[(format!("x{i}").as_str(), 1)], 0),
            &Lin::constant(0),
        ));
        let or = Formula::Or(Shared::new(vec![p.clone(), Formula::Not(Shared::new(p))]));
        p = Formula::And(Shared::new(vec![c, or]));
    }
    let want: HashSet<String> = (0..64).map(|i| format!("x{i}")).collect();
    let t = std::time::Instant::now();
    assert_eq!(p.written_names(|s| s), want);
    assert!(t.elapsed().as_secs() < 5, "{:?}", t.elapsed());
}

/// The formula `random_classes_answer_as_with_their_columns_apart` printed at
/// ZED_TEST_SEED=16869946785917123429. Its second arm holds `-3 >= 0`, false, so the first arm
/// holds, and its `x + y <= -1` with `y >= -4` gives `x <= 3`; x = -4 has the point y = -4,
/// u + v = -4 (check: -16 <= -9, -8 <= -12 + 4, -8 <= -1). So x's set is -4..=3.
fn seed_16869946785917123429(second: Formula) -> Formula {
    let first = Formula::and(vec![
        ge(&[("x", 2), ("y", -2), ("u", -2), ("v", -2)], -1),
        ge(&[("x", 2), ("y", 2), ("u", -2), ("v", -2)], 4),
        ge(&[("x", -1), ("y", -1)], -1),
    ]);
    Formula::and(vec![
        member(&a("x"), &IntervalSet::of(-4, 4)),
        member(&a("y"), &IntervalSet::of(-4, 4)),
        ge(&[("u", 1), ("v", 1)], 4),
        ge(&[("u", -1), ("v", -1)], 4),
        Formula::or(vec![first, second]),
    ])
}

#[test]
fn seed_16869946785917123429_projects_x_to_its_points() {
    let false_arm = |b: Formula| Formula::and(vec![b, ge(&[], -3)]);
    // The seed's formula, two variants whose false arm reads another atom, and the least
    // formula found with the same fault: `x + y <= -1 || (w >= 0 && -3 >= 0)`, whose arm
    // `w >= 0 && -3 >= 0` went to `star` as one block and was read as having points, so
    // `read_once` gave the disjunction an arm with a point that does not read x, and x every
    // value of its box. Each was -4..=4 before the fix in `star`, with `direct` on or off for
    // some of them; the solver alone (`project_each_solver`) gave -4..=3 for each.
    let cases = [
        seed_16869946785917123429(false_arm(ge(&[("u", 1), ("v", 1)], 3))),
        seed_16869946785917123429(false_arm(ge(&[("y", 1)], 3))),
        seed_16869946785917123429(false_arm(ge(&[("u", 1)], 3))),
        Formula::and(vec![
            member(&a("x"), &IntervalSet::of(-4, 4)),
            member(&a("y"), &IntervalSet::of(-4, 4)),
            Formula::or(vec![
                ge(&[("x", -1), ("y", -1)], -1),
                false_arm(ge(&[("w", 1)], 0)),
            ]),
        ]),
    ];
    for f in cases {
        let on = project_each_exact(&f, &[a("x")]).map(|p| p.0);
        DIRECT_OFF.set(true);
        let off = project_each_exact(&f, &[a("x")]).map(|p| p.0);
        DIRECT_OFF.set(false);
        let want = Ok(vec![Ok(IntervalSet::of(-4, 3))]);
        assert_eq!(on, want, "x of {f}, `direct` on");
        assert_eq!(off, want, "x of {f}, `direct` off");
    }
}
