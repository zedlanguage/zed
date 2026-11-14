//! Choice sums that reach the point search over rows whose names are not bounded
//! (`slack::sweep_row_unbounded` and its arms of `slack::fill_row_model`), and the greedy search
//! over such rows (`try_pick_disjoint_wide`), checked against enumeration of every subset.
//!
//! Each formula is `y_i == 0 || y_i == w_i` for each `i` with the row `Σ y_i == t`, and in most
//! cases a second such row over other names `z_j` with its own weights. The rows the
//! disjunctions imply (`0 <= y_i <= w_i`) are asked first; the search over unbounded rows runs
//! only where that ask is refused and the formula is asked again without them, or on the old
//! path that a refused question is asked again on, and with the method of PRES-overlap-fast
//! (module `row_sums`) off, since with it on the rows are answered before the solver. The
//! weights and targets are ones a random search found to reach those searches: the first row
//! hard enough that the ask with the implied rows is refused, the second easy enough that the
//! search without them finds its point. With `row_sums` off the solver may refuse, and its
//! projection may be wider than the exact one (COMPLEXITY.md PRES-exp-families, A87): a point
//! it gives must hold, an answer it gives must be the enumerated one, and its projection must
//! hold every enumerated value. With it on, every answer must be exact.

use std::collections::BTreeSet;
use std::sync::Arc;

use zedc::store::interval::IntervalSet;
use zedc::store::presburger::{
    Atom, Con, Formula, Lin, ROW_SUMS_OFF, decide, project_each, satisfiable,
};

fn name(n: &str, i: usize) -> Atom {
    Atom::Sym(Arc::from(format!("{n}{i}").as_str()))
}

fn is(a: Atom, v: i64) -> Formula {
    Formula::Con(Con::eq(&Lin::atom(a), &Lin::constant(i128::from(v))))
}

/// One row over the names `n0, n1, ...`: `n_i == 0 || n_i == w_i` (the `w_i` arm first where
/// `high_first[i]`) and `Σ n_i == t`.
fn row(n: &str, w: &[i64], high_first: &[bool], t: i64) -> Vec<Formula> {
    let mut fs: Vec<Formula> = w
        .iter()
        .zip(high_first)
        .enumerate()
        .map(|(i, (&wi, &hf))| {
            let (lo, hi) = (is(name(n, i), 0), is(name(n, i), wi));
            Formula::or(if hf { vec![hi, lo] } else { vec![lo, hi] })
        })
        .collect();
    let sum = (0..w.len()).fold(Lin::constant(0), |s, i| s.plus(&Lin::atom(name(n, i))));
    fs.push(Formula::Con(Con::eq(&sum, &Lin::constant(i128::from(t)))));
    fs
}

/// The sums of the subsets of `w`, each with whether it can take `w_0`.
fn sums(w: &[i64]) -> Vec<(i64, bool)> {
    (0u32..1 << w.len())
        .map(|s| {
            let sum = (0..w.len()).filter(|i| s >> i & 1 == 1).map(|i| w[i]).sum();
            (sum, s & 1 == 1)
        })
        .collect()
}

/// The values of `y0` over the points of the rows, by enumeration: the values of `y0` over the
/// subsets of `w` summing to `t`, or none where the second row has no subset summing to `t2`.
fn y0_values(w: &[i64], t: i64, second: Option<(&[i64], i64)>) -> IntervalSet {
    if second.is_some_and(|(w2, t2)| !sums(w2).iter().any(|&(s, _)| s == t2)) {
        return IntervalSet::empty();
    }
    sums(w)
        .into_iter()
        .filter(|&(s, _)| s == t)
        .map(|(_, takes)| if takes { w[0] } else { 0 })
        .collect::<BTreeSet<i64>>()
        .into_iter()
        .fold(IntervalSet::empty(), |acc, v| {
            acc.join(&IntervalSet::single(v))
        })
}

/// A first row and, where `second` is given, a second row `(weights, arm order, target)`.
struct Family<'a> {
    w: &'a [i64],
    high_first: &'a [bool],
    second: Option<(&'a [i64], &'a [bool], i64)>,
}

/// Checks every entry point on the family at each target `t` of `ts` and at each `t + 1`, with
/// `row_sums` on and off, and returns the wrong answers.
fn wrong_answers(fam: &Family, ts: &[i64]) -> Vec<String> {
    let mut wrong = Vec::new();
    for t in ts.iter().flat_map(|&t| [t, t + 1]) {
        let mut fs = row("y", fam.w, fam.high_first, t);
        if let Some((w2, hf2, t2)) = fam.second {
            fs.extend(row("z", w2, hf2, t2));
        }
        let f = Formula::and(fs);
        let want = y0_values(fam.w, t, fam.second.map(|(w2, _, t2)| (w2, t2)));
        for alone in [false, true] {
            ROW_SUMS_OFF.with(|o| o.set(alone));
            let d = decide(&f);
            let s = satisfiable(&f);
            let p = project_each(&f, &[name("y", 0)]);
            ROW_SUMS_OFF.with(|o| o.set(false));
            let tag = format!("w {:?}, t {t}, alone {alone}", fam.w);
            match d {
                Ok(b) if b == want.is_empty() => wrong.push(format!("{tag}: decide {b}")),
                Err(e) if !alone => wrong.push(format!("{tag}: decide refused {e:?}")),
                _ => {}
            }
            match s {
                Ok(Some(m)) if !f.holds(&m) => wrong.push(format!("{tag}: the point fails")),
                Ok(Some(_)) if want.is_empty() => wrong.push(format!("{tag}: a point of none")),
                Ok(None) if !want.is_empty() => wrong.push(format!("{tag}: no point")),
                Err(e) if !alone => wrong.push(format!("{tag}: satisfiable refused {e:?}")),
                _ => {}
            }
            match p.map(|(p, _)| p[0].clone()) {
                Ok(Ok(got)) if got != want && (!alone || !want.is_subset(&got)) => {
                    wrong.push(format!("{tag}: projection {got:?}, want {want:?}"));
                }
                Ok(Err(e)) | Err(e) if !alone => {
                    wrong.push(format!("{tag}: projection refused {e:?}"));
                }
                _ => {}
            }
        }
    }
    wrong
}

fn assert_right(fam: &Family, ts: &[i64]) {
    let wrong = wrong_answers(fam, ts);
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// Two rows; the second, `z0 + z2 == 52` over the weights 27, 13, 25, 22.
#[test]
fn second_row_of_four() {
    assert_right(
        &Family {
            w: &[72, 77, 40, 25, 78, 63, 13, 59],
            high_first: &[false, true, true, false, false, true, true, true],
            second: Some((&[27, 13, 25, 22], &[false, false, true, true], 52)),
        },
        &[143],
    );
}

/// Two rows; the second, `z0 + z2 == 38` over the weights 10, 23, 28, 14.
#[test]
fn second_row_of_four_wide_first() {
    assert_right(
        &Family {
            w: &[15, 72, 35, 97, 1, 50, 98, 95, 80, 32],
            high_first: &[
                true, true, true, true, true, false, false, true, true, false,
            ],
            second: Some((&[10, 23, 28, 14], &[true, false, true, false], 38)),
        },
        &[139],
    );
}

/// Two rows; the second, `z0 + z2 == 7` over the weights 3, 7, 4, 9, where `z1 == 7` alone
/// also holds.
#[test]
fn second_row_with_two_points() {
    assert_right(
        &Family {
            w: &[9, 38, 85, 31, 92, 91, 28, 37],
            high_first: &[true, false, true, true, false, true, true, false],
            second: Some((&[3, 7, 4, 9], &[false, true, true, false], 7)),
        },
        &[74, 144],
    );
}

/// Two rows; the second, `z0 + z2 == 42` over the weights 20, 16, 22, 17.
#[test]
fn second_row_projected() {
    assert_right(
        &Family {
            w: &[100, 5, 20, 31, 34, 100, 67, 15, 18, 50],
            high_first: &[
                true, false, true, true, false, true, true, true, true, false,
            ],
            second: Some((&[20, 16, 22, 17], &[true, false, true, false], 42)),
        },
        &[146],
    );
}

/// One row with two equal weights, which the projection of `y0` reaches with a part of the
/// row fixed.
#[test]
fn one_row_with_equal_weights_projected() {
    assert_right(
        &Family {
            w: &[83, 12, 83, 69, 53, 42, 76, 66, 54, 5],
            high_first: &[
                false, false, false, true, false, false, false, true, true, true,
            ],
            second: None,
        },
        &[108, 122],
    );
}
