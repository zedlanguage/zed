//! `decide` on a conjunction of rows of at most two terms with coefficients 1 or -1 (COMPLEXITY.md
//! S44, DECIDE-front-cost). Such rows are decided by `utvpi::integer_empty` alone, without the
//! front end every other formula takes (the normal form, the canonical order, the linked rows),
//! which cost 3 to 5 times the search on them and grew with the number of variables. The answers
//! are those of the whole path (`satisfiable`) and of enumeration, and the cost stays within a
//! constant of the search's at every size.

use std::sync::Arc;

use zed_tests::instances::Rng;
use zed_tests::scaling::Meter;
use zed_tests::step_helpers::l01_38_presburger::small_cost::least;
use zedc::store::int::Int;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Model, decide, satisfiable};
use zedc::store::utvpi::integer_empty;

use super::scaling::utvpi_rows;

/// The variables of the small formulas: three symbols and an auxiliary variable, which the
/// rows treat alike.
fn var(i: usize) -> Atom {
    if i == 3 {
        Atom::Aux(0)
    } else {
        Atom::Sym(Arc::from(format!("x{i}")))
    }
}

/// `Σ c·v[i] + k >= 0`, or `== 0` when `eq`.
fn row(t: &[(usize, i64)], k: i64, eq: bool) -> Formula {
    let l = t.iter().fold(Lin::constant(k), |l, (i, c)| {
        l.plus(&Lin::atom(var(*i)).times(*c))
    });
    let zero = Lin::constant(0);
    Formula::Con(if eq {
        Con::eq(&l, &zero)
    } else {
        Con::ge(&l, &zero)
    })
}

/// Whether `f` holds at some point with every variable of [`var`] in `-3..=3`.
fn holds_in_box(f: &Formula) -> bool {
    (0..7i64.pow(4)).any(|code| {
        let m: Model = (0..4)
            .map(|i| (var(i), Int::from(code / 7i64.pow(i as u32) % 7 - 3)))
            .collect();
        f.holds(&m)
    })
}

/// 200 conjunctions of [`unit_rows_agree`] of a new seed each run. Both answers occur at every
/// seed tried, but no count of them is reached at every seed, so none is asserted;
/// [`unit_rows_built_with_and_without_a_point_agree`] asserts each answer. The 600 of seed 0x544
/// (1.1 s at load 25) are in `bench::front_cost`.
#[test]
fn unit_rows_are_decided_as_enumeration_and_the_whole_path_decide_them() {
    let (mut rng, _) = Rng::fresh("front_cost unit rows");
    unit_rows_agree(&mut rng, 200);
}

/// `decide` answers `f` as enumeration over the box `[-3, 3]^4` does and as `satisfiable` does,
/// and the point `satisfiable` gives holds; whether `f` has a point.
fn unit_rows_answer(f: &Formula) -> bool {
    let point = holds_in_box(f);
    assert_eq!(decide(f), Ok(point), "{f}");
    let found = satisfiable(f).expect("answered");
    assert_eq!(found.is_some(), point, "{f}");
    if let Some(m) = &found {
        assert!(f.holds(m), "{m:?} fails {f}");
    }
    point
}

/// Two conjunctions of the shape [`unit_rows_agree`] draws, the box rows and one row of two
/// unit terms each: `x0 - x1 - 4 >= 0` holds at `x0 = 3, x1 = -1`; `x0 + x1 - 4 == 0` holds at
/// `(2, 2)` beside `x0 - x1 - 1 == 0`, which asks for `2 x0 == 5`, so together they have no
/// integer point.
#[test]
fn unit_rows_built_with_and_without_a_point_agree() {
    let boxed = |mut rows: Vec<Formula>| {
        rows.extend((0..4).flat_map(|i| [row(&[(i, 1)], 3, false), row(&[(i, -1)], 3, false)]));
        Formula::and(rows)
    };
    assert!(unit_rows_answer(&boxed(vec![row(
        &[(0, 1), (1, -1)],
        -4,
        false
    )])));
    assert!(!unit_rows_answer(&boxed(vec![
        row(&[(0, 1), (1, 1)], -4, true),
        row(&[(0, 1), (1, -1)], -1, true),
    ])));
}

/// `count` random conjunctions of one to six rows of one or two unit terms, inequalities and
/// equalities, some of no term, with every variable bounded to `-3..=3` by rows of one term:
/// `decide` answers as enumeration over the box does and as `satisfiable`, which takes the
/// whole path, does, and the point `satisfiable` gives holds. The counts with and without a
/// point.
pub(super) fn unit_rows_agree(rng: &mut Rng, count: usize) -> (usize, usize) {
    let (mut with, mut without) = (0, 0);
    for _ in 0..count {
        let mut rows: Vec<Formula> = (0..4)
            .flat_map(|i| [row(&[(i, 1)], 3, false), row(&[(i, -1)], 3, false)])
            .collect();
        for _ in 0..1 + rng.below(6) {
            let a = rng.below(4);
            let b = (a + 1 + rng.below(3)) % 4;
            let terms: Vec<(usize, i64)> = match rng.below(8) {
                0 => Vec::new(),
                1 | 2 => vec![(a, rng.pick(&[-1, 1]))],
                _ => vec![(a, rng.pick(&[-1, 1])), (b, rng.pick(&[-1, 1]))],
            };
            rows.push(row(&terms, rng.int(-4, 4), rng.below(3) == 0));
        }
        let f = Formula::and(rows);
        if unit_rows_answer(&f) {
            with += 1;
        } else {
            without += 1;
        }
    }
    (with, without)
}

/// Rows a checker meets, with the answer of each: a bound of no variable, an equality that ties
/// two variables, the parity of `x + y == 1` with `x == y`, a product, which is not a variable of
/// these rows and goes the whole path, and a coefficient of 2, which does too.
#[test]
fn unit_rows_at_their_corners_are_decided() {
    let product = Lin::atom(Atom::product(&Arc::from("x0"), &Arc::from("x1")));
    let cases: [(&str, Vec<Formula>, bool); 8] = [
        ("-1 >= 0", vec![row(&[], -1, false)], false),
        ("0 == 0", vec![row(&[], 0, true)], true),
        ("2 == 0", vec![row(&[], 2, true)], false),
        (
            "x0 - x1 == 1 && x1 - x0 == 1",
            vec![
                row(&[(0, 1), (1, -1)], -1, true),
                row(&[(1, 1), (0, -1)], -1, true),
            ],
            false,
        ),
        (
            "x0 + x1 == 1 && x0 == x1: no integer point, the rational 1/2",
            vec![
                row(&[(0, 1), (1, 1)], -1, true),
                row(&[(0, 1), (1, -1)], 0, true),
            ],
            false,
        ),
        (
            "x0 + x1 == 2 && x0 == x1",
            vec![
                row(&[(0, 1), (1, 1)], -2, true),
                row(&[(0, 1), (1, -1)], 0, true),
            ],
            true,
        ),
        (
            "x0 * x1 - x2 >= 0 && x2 >= 5",
            vec![
                Formula::Con(Con::ge(
                    &product.minus(&Lin::atom(var(2))),
                    &Lin::constant(0),
                )),
                row(&[(2, 1)], -5, false),
            ],
            true,
        ),
        ("2 * x0 == 1", vec![row(&[(0, 2)], -1, true)], false),
    ];
    for (what, rows, point) in cases {
        let f = Formula::and(rows);
        assert_eq!(decide(&f), Ok(point), "{what}");
        let found = satisfiable(&f).expect("answered");
        assert_eq!(found.is_some(), point, "{what}");
    }
}

/// The instructions `decide` and `integer_empty` take on the family `utvpi(n)`, each the least
/// of [`Meter::least`]'s runs, after checking that both find a point.
pub(super) fn costs(meter: &mut Meter, n: usize) -> (u64, u64) {
    let (f, rows) = utvpi_rows(n);
    let terms: Vec<(&[(usize, Int)], &Int)> = rows.iter().map(|(t, k)| (&t[..], k)).collect();
    assert_eq!(decide(&f), Ok(true));
    assert!(!integer_empty(n, &terms));
    let d = least(meter, &|| drop(std::hint::black_box(decide(&f))));
    let u = least(meter, &|| {
        std::hint::black_box(integer_empty(n, &terms));
    });
    (d, u)
}

/// The checks [`costs`] makes besides the ratio of the benchmark, at small sizes: `decide` and
/// `integer_empty` both find the point of `utvpi(n)`.
#[test]
fn decide_and_the_search_both_find_the_point_of_unit_rows_at_small_sizes() {
    let mut meter = Meter::new();
    for n in [2, 8, 32] {
        costs(&mut meter, n);
    }
}
