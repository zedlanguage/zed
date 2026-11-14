//! Small choice sums that reach the point search of the slack index (`find_probe_points`,
//! `slack::sweep_row`, `slack::fill_row_model`, `find_tied_point`, `settle_tied`, and the
//! repair of a wide point), checked against enumeration of every subset.
//!
//! Each formula is `y_i == 0 || y_i == w_i` for each `i` and `Σ y_i == t`, for every subset
//! sum `t` of `w` and every `t + 1` (no point in most cases), the arms in either order, and with
//! the method of PRES-overlap-fast (module `row_sums`) on and off. With it on every entry
//! point answers exactly. With it off the solver alone may refuse (`Disjuncts`, or a tie of
//! names), and its projection may be wider than the exact one (COMPLEXITY.md
//! PRES-exp-families, A87): a point it gives must hold, an answer it gives must be the
//! enumerated one, and its projection must hold every enumerated value.

use std::collections::BTreeSet;
use std::sync::Arc;

use zedc::store::interval::IntervalSet;
use zedc::store::presburger::{
    Atom, Con, Formula, Lin, ROW_SUMS_OFF, decide, project_each, satisfiable,
};

fn y(i: usize) -> Atom {
    Atom::Sym(Arc::from(format!("y{i}").as_str()))
}

fn is(a: Atom, v: i64) -> Formula {
    Formula::Con(Con::eq(&Lin::atom(a), &Lin::constant(i128::from(v))))
}

/// How the sum row is written, and what stands beside it. Each shape has the points of
/// `Plain` on the `y_i` (and `y0` projects the same), so one enumeration checks them all.
#[derive(Clone, Copy, Debug)]
enum Shape {
    /// `Σ y_i == t`.
    Plain,
    /// `-Σ y_i == -t`: the row with a negative first coefficient.
    Negated,
    /// `Σ y_i == t` and `3 <= z <= 7`, `z` in no row.
    FreeAtom,
    /// `Σ y_i == t` and `0 <= y_i <= w_i` for each `i`: every name of the row bounded.
    Bounded,
    /// `Σ y_i + c == t + 4` and `c == 4`: a fixed name inside the row.
    FixedInRow,
}

fn con(c: Con) -> Formula {
    Formula::Con(c)
}

fn k(v: i64) -> Lin {
    Lin::constant(i128::from(v))
}

/// `y_i == 0 || y_i == w_i` for each `i` (the `w_i` arm first where `high_first`) and the sum
/// row `Σ y_i == t` written as `shape` says.
fn choice(w: &[i64], t: i64, high_first: bool, shape: Shape) -> Formula {
    let mut fs: Vec<Formula> = w
        .iter()
        .enumerate()
        .map(|(i, &wi)| {
            let (lo, hi) = (is(y(i), 0), is(y(i), wi));
            Formula::or(if high_first {
                vec![hi, lo]
            } else {
                vec![lo, hi]
            })
        })
        .collect();
    let sum = (0..w.len()).fold(k(0), |s, i| s.plus(&Lin::atom(y(i))));
    let c = Lin::atom(Atom::Sym(Arc::from("c")));
    let z = Lin::atom(Atom::Sym(Arc::from("z")));
    match shape {
        Shape::Plain => fs.push(con(Con::eq(&sum, &k(t)))),
        Shape::Negated => fs.push(con(Con::eq(&sum.times(-1), &k(-t)))),
        Shape::FreeAtom => fs.extend([
            con(Con::eq(&sum, &k(t))),
            con(Con::ge(&z, &k(3))),
            con(Con::ge(&k(7), &z)),
        ]),
        Shape::Bounded => {
            fs.push(con(Con::eq(&sum, &k(t))));
            for (i, &wi) in w.iter().enumerate() {
                fs.push(con(Con::ge(&Lin::atom(y(i)), &k(0))));
                fs.push(con(Con::ge(&k(wi), &Lin::atom(y(i)))));
            }
        }
        Shape::FixedInRow => fs.extend([
            con(Con::eq(&sum.plus(&c), &k(t + 4))),
            con(Con::eq(&c, &k(4))),
        ]),
    }
    Formula::and(fs)
}

/// The sum of the subset `s` (bit `i` set takes `w_i`).
fn subset_sum(w: &[i64], s: u32) -> i64 {
    (0..w.len()).filter(|i| s >> i & 1 == 1).map(|i| w[i]).sum()
}

/// The values of `y0` over the subsets of `w` summing to `t`, by enumeration.
fn y0_values(w: &[i64], t: i64) -> IntervalSet {
    (0u32..1 << w.len())
        .filter(|&s| subset_sum(w, s) == t)
        .map(|s| if s & 1 == 1 { w[0] } else { 0 })
        .collect::<BTreeSet<i64>>()
        .into_iter()
        .fold(IntervalSet::empty(), |acc, v| {
            acc.join(&IntervalSet::single(v))
        })
}

/// Checks every entry point on `choice(w, t, .., shape)` for each subset sum `t` and each
/// `t + 1`, and returns the wrong answers.
fn wrong_answers(w: &[i64], orders: &[bool], shape: Shape) -> Vec<String> {
    let mut wrong = Vec::new();
    let targets: BTreeSet<i64> = (0u32..1 << w.len())
        .flat_map(|s| [subset_sum(w, s), subset_sum(w, s) + 1])
        .collect();
    for t in targets {
        let want = y0_values(w, t);
        for &high_first in orders {
            let f = choice(w, t, high_first, shape);
            for alone in [false, true] {
                ROW_SUMS_OFF.with(|o| o.set(alone));
                let d = decide(&f);
                let s = satisfiable(&f);
                let p = project_each(&f, &[y(0)]);
                ROW_SUMS_OFF.with(|o| o.set(false));
                let tag = format!(
                    "{shape:?}, w {w:?}, t {t}, high arm first {high_first}, alone {alone}"
                );
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
    }
    wrong
}

fn assert_right(ws: &[Vec<i64>], orders: &[bool]) {
    assert_shape_right(ws, orders, Shape::Plain);
}

fn assert_shape_right(ws: &[Vec<i64>], orders: &[bool], shape: Shape) {
    let wrong: Vec<String> = ws
        .iter()
        .flat_map(|w| wrong_answers(w, orders, shape))
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// The weights the shapes below are tried on: equal, two classes, distinct.
fn shape_weights() -> [Vec<i64>; 3] {
    [vec![5, 5, 5, 5], vec![3, 3, 5, 5], vec![3, 5, 9, 17]]
}

/// The sum row written with a negative first coefficient.
#[test]
fn negated_row() {
    assert_shape_right(&shape_weights(), &[false, true], Shape::Negated);
}

/// A bounded name in no row beside the choices.
#[test]
fn free_atom_beside() {
    assert_shape_right(&shape_weights(), &[false, true], Shape::FreeAtom);
}

/// Every choice name bounded to `0..=w_i` as well.
#[test]
fn bounded_names() {
    assert_shape_right(&shape_weights(), &[false, true], Shape::Bounded);
}

/// A fixed name inside the sum row.
#[test]
fn fixed_name_in_row() {
    assert_shape_right(&shape_weights(), &[false, true], Shape::FixedInRow);
}

/// Equal weights tie every name: `settle_tied` and `find_tied_point`.
#[test]
fn equal_weights() {
    assert_right(
        &[
            vec![5, 5],
            vec![5, 5, 5],
            vec![5, 5, 5, 5],
            vec![5, 5, 5, 5, 5],
        ],
        &[false, true],
    );
}

/// Two classes of equal weights, a tie of names inside each.
#[test]
fn two_classes_of_weights() {
    assert_right(
        &[vec![3, 3, 5, 5], vec![2, 2, 2, 7], vec![4, 4, 4, 9, 9]],
        &[false, true],
    );
}

/// Distinct weights: `sweep_row` and `fill_row_model` over one row of distinct colors.
#[test]
fn distinct_weights() {
    assert_right(
        &[
            vec![3, 5, 9],
            vec![1000, 1037, 1148, 1333],
            vec![2, 3, 7, 13, 19],
        ],
        &[false, true],
    );
}

/// The weights of the benchmarks (`1000 + 37 i² mod 991`) at k = 5, where the solver alone
/// starts to refuse, the zero arm first.
#[test]
fn benchmark_weights_zero_arm_first() {
    assert_right(&[vec![1000, 1037, 1148, 1333, 1592]], &[false]);
}

/// As `benchmark_weights_zero_arm_first`, the weight arm first.
#[test]
fn benchmark_weights_weight_arm_first() {
    assert_right(&[vec![1000, 1037, 1148, 1333, 1592]], &[true]);
}
