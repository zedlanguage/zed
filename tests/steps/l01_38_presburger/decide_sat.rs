//! `decide` and `satisfiable` answer the same formulas (I18). `decide` asks `has_point`, which
//! probed with the search stopped at its first point, and that probe skipped the removals and
//! the batched searches that `found`'s probe makes first: on twelve formulas of the shared-sum
//! shape below `satisfiable` returned a point and `decide` refused with `Disjuncts`. Each entry
//! now tries the other's probe when its own refuses. The formulas are those of seed 777 of the
//! random shared-sum generator: 3 to 7 atoms, each `y == a` or `y == b` (now and then an
//! interval `[b, c]`), one row that sums them, sometimes a second.

use std::sync::Arc;

use zedc::store::presburger::{Atom, Con, Formula, Lin, Shared, decide, satisfiable};

use super::repair::answers;

struct Rng(u64);

impl Rng {
    fn next(&mut self, n: u64) -> i64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((self.0 >> 33) % n) as i64
    }
}

fn lin(t: &[(&str, i64)], k: i64) -> Lin {
    t.iter().fold(Lin::constant(k), |l, (a, c)| {
        l.plus(&Lin::atom(Atom::Sym(Arc::from(*a))).times(*c))
    })
}

fn eq(t: &[(&str, i64)], k: i64) -> Formula {
    Formula::Con(Con::eq(&lin(t, k), &Lin::constant(0)))
}

fn ge(t: &[(&str, i64)], k: i64) -> Formula {
    Formula::Con(Con::ge(&lin(t, k), &Lin::constant(0)))
}

/// The formulas of cases `0..n` of the generator, with whether each has a point by brute force.
fn formulas(n: u64) -> Vec<(Formula, bool)> {
    let mut rng = Rng(777);
    let mut out = Vec::new();
    for _ in 0..n {
        let k = 3 + rng.next(5) as usize;
        let names: Vec<String> = (0..k).map(|i| format!("y{i}")).collect();
        let mut fs = Vec::new();
        let mut doms: Vec<Vec<i64>> = Vec::new();
        for nm in &names {
            let a = if rng.next(3) == 0 { rng.next(6) } else { 0 };
            let b = a + 1 + rng.next(30);
            let mut dom = vec![a];
            let second = if rng.next(6) == 0 {
                let c = b + rng.next(3);
                dom.extend(b..=c);
                Formula::and(vec![ge(&[(nm, 1)], -b), ge(&[(nm, -1)], c)])
            } else {
                dom.push(b);
                eq(&[(nm, 1)], -b)
            };
            fs.push(Formula::or(vec![eq(&[(nm, 1)], -a), second]));
            doms.push(dom);
        }
        let mut rows: Vec<(Vec<i64>, i64, bool)> = Vec::new();
        let nrows = 1 + (rng.next(4) == 0) as u64;
        for r in 0..nrows {
            let cs: Vec<i64> = (0..k)
                .map(|_| [1, 1, 1, 1, 1, -1, 2][rng.next(7) as usize])
                .collect();
            let is_eq = r == 0 || rng.next(2) == 0;
            let t = if rng.next(2) == 0 {
                (0..k)
                    .map(|i| cs[i] * doms[i][rng.next(doms[i].len() as u64) as usize])
                    .sum()
            } else {
                let hi: i64 = (0..k)
                    .map(|i| cs[i].abs() * doms[i][doms[i].len() - 1])
                    .sum();
                rng.next(hi.max(1) as u64 + 1)
            };
            let terms: Vec<(&str, i64)> = names
                .iter()
                .zip(&cs)
                .map(|(n, c)| (n.as_str(), *c))
                .collect();
            fs.push(if is_eq {
                eq(&terms, -t)
            } else {
                ge(&terms, -t)
            });
            rows.push((cs, t, is_eq));
        }
        // Every point of the domains, in the order of an odometer.
        let mut idx = vec![0usize; k];
        let mut truth = false;
        'outer: loop {
            let pt: Vec<i64> = (0..k).map(|i| doms[i][idx[i]]).collect();
            truth |= rows.iter().all(|(cs, t, e)| {
                let s: i64 = cs.iter().zip(&pt).map(|(c, x)| c * x).sum();
                if *e { s == *t } else { s >= *t }
            });
            for i in 0..k {
                idx[i] += 1;
                if idx[i] < doms[i].len() {
                    continue 'outer;
                }
                idx[i] = 0;
            }
            break;
        }
        out.push((Formula::and(fs), truth));
    }
    out
}

/// The twelve cases where `decide` refused and `satisfiable` returned a point: both now answer,
/// with the brute-force answer, and the point meets the formula.
#[test]
fn decide_answers_where_satisfiable_answers() {
    let fs = formulas(2474);
    for case in [
        78, 91, 399, 590, 646, 918, 1093, 1312, 1711, 1911, 2156, 2473,
    ] {
        let (f, truth) = &fs[case];
        answers(f, *truth);
    }
}

/// Case 43 of seed 8087861239740142386 of `l01_39_reduced_product::pendants`'s rewritten parts
/// (FAIL-pendants-rewrite-growth-seed), with its boxes as rows: `decide` found no point, but
/// `satisfiable` refused by growth on the part as written and found none once the equation
/// `2 * a + b + 2 * c + z0 == 3` was written as two rows. `satisfiable` now removes the
/// disjuncts the bounds show have no point first, as `decide` does, and gives no point on both.
#[test]
fn an_equation_written_as_one_row_or_two_is_decided_by_both() {
    let ne = Formula::Not(Shared::new(Formula::Con(Con::eq(
        &lin(&[("a", 2), ("c", 1), ("b", -1), ("z2", -1)], -1),
        &Lin::constant(0),
    ))));
    let rows = |equation: Vec<Formula>| {
        let mut fs = vec![
            ge(&[("b", 1)], 7),
            ge(&[("b", -1)], -3),
            ge(&[("c", -1)], 5),
            ge(&[("z0", -1)], -7),
            ge(&[("z2", 1)], -2),
            ge(&[("z2", -1)], 17),
            ge(&[("a", 1), ("b", 2), ("c", 2)], -5),
            ge(&[("b", 1), ("c", 1), ("z2", 1)], 9),
            ne.clone(),
        ];
        fs.extend(equation);
        fs.extend([
            ge(&[("a", 1), ("b", 1), ("z2", -1)], 1),
            ge(&[("b", 2), ("c", -1)], 12),
            ge(&[("z0", 1), ("z2", -1)], 4),
            ge(&[("a", 1), ("c", 1), ("b", -1), ("z2", -1)], -6),
        ]);
        Formula::and(fs)
    };
    let sum = [("a", 2), ("b", 1), ("c", 2), ("z0", 1)];
    let one = rows(vec![eq(&sum, -3)]);
    let neg: Vec<(&str, i64)> = sum.iter().map(|&(a, c)| (a, -c)).collect();
    let two = rows(vec![ge(&sum, -3), ge(&neg, 3)]);
    for f in [&one, &two] {
        assert_eq!(decide(f), Ok(false), "{f}");
        assert_eq!(satisfiable(f).map(|m| m.is_some()), Ok(false), "{f}");
    }
}
