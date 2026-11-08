//! The point of rows `±x ± y + k >= 0` and `±x + k >= 0` (UTVPI-model): `utvpi::integer_point`
//! rounds the rational point a potential of the constraint graph gives, settling the halves by
//! 2-SAT over the tight edges, and `satisfiable` takes that point once every row left has that
//! form, where it used to eliminate every variable with fill allowed (COMPLEXITY.md S38).

use std::sync::Arc;

use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::int::Int;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Model, decide, satisfiable};
use zedc::store::utvpi::{Search, integer_empty, integer_point_by};

use super::scaling::x;

/// A row `Σ c·x[i] + k >= 0` with its terms ordered by variable.
type Row = (Vec<(usize, Int)>, Int);

fn row(t: &[(usize, i64)], k: i64) -> Row {
    let mut t: Vec<(usize, Int)> = t.iter().map(|&(i, c)| (i, Int::from(c))).collect();
    t.sort_by_key(|t| t.0);
    (t, Int::from(k))
}

const SEARCHES: [Search; 4] = [
    Search::First,
    Search::GoldbergRadzik,
    Search::BfDijkstra,
    Search::Duong,
];

/// Whether `p` meets every row.
fn meets(rows: &[Row], p: &[Int]) -> bool {
    rows.iter().all(|(t, k)| {
        let sum = t.iter().fold(k.clone(), |s, (i, c)| &s + &(c * &p[*i]));
        !sum.is_negative()
    })
}

/// The point each search gives, checked against every row, and whether there is one; every
/// search must agree with the others and with `integer_empty`.
fn point(n: usize, rows: &[Row]) -> Option<Vec<Int>> {
    let terms: Vec<(&[(usize, Int)], &Int)> = rows.iter().map(|(t, k)| (&t[..], k)).collect();
    let empty = integer_empty(n, &terms);
    let mut first = None;
    for search in SEARCHES {
        let found = integer_point_by(n, &terms, search);
        assert_eq!(found.is_none(), empty, "{search:?} on {rows:?}");
        if let Some(p) = &found {
            assert_eq!(p.len(), n, "{search:?} on {rows:?}");
            assert!(meets(rows, p), "{search:?} gives {p:?} on {rows:?}");
        }
        first = first.or(found);
    }
    first
}

/// The rows as a formula over `x0, x1, …`.
fn formula(rows: &[Row]) -> Formula {
    Formula::and(
        rows.iter()
            .map(|(t, k)| {
                let k = i64::try_from(k.to_i128().expect("small")).expect("small");
                let l = t.iter().fold(Lin::constant(k), |l, (i, c)| {
                    let c = i64::try_from(c.to_i128().expect("unit")).expect("unit");
                    l.plus(&x(*i).times(c))
                });
                Formula::Con(Con::ge(&l, &Lin::constant(0)))
            })
            .collect(),
    )
}

/// Whether some point of `[-half, half]^n` meets every row.
fn enumerated(rows: &[Row], n: usize, half: i64) -> bool {
    let mut p = vec![Int::from(-half); n];
    loop {
        if meets(rows, &p) {
            return true;
        }
        let mut i = 0;
        loop {
            if i == n {
                return false;
            }
            if p[i] < Int::from(half) {
                p[i] = &p[i] + &Int::ONE;
                break;
            }
            p[i] = Int::from(-half);
            i += 1;
        }
    }
}

#[test]
fn a_parity_conflict_has_no_point() {
    // `x0 == x1` and `x0 + x1 == 1`: the rational point (1/2, 1/2), no integer point.
    let odd = [
        row(&[(0, 1), (1, -1)], 0),
        row(&[(0, -1), (1, 1)], 0),
        row(&[(0, -1), (1, -1)], 1),
        row(&[(0, 1), (1, 1)], -1),
    ];
    assert_eq!(point(2, &odd), None);
    assert_eq!(satisfiable(&formula(&odd)), Ok(None));
    // Without `x0 + x1 >= 1`, the halves are rounded down together: `x0 = x1 <= 0`.
    let p = point(2, &odd[..3]).expect("a point");
    assert_eq!(p[0], p[1]);
    // The parity conflict hidden in a cycle of three: `x0 == x1 == x2`, `x0 + x2 == 1`.
    let cycle = [
        row(&[(0, 1), (1, -1)], 0),
        row(&[(1, 1), (2, -1)], 0),
        row(&[(2, 1), (0, -1)], 0),
        row(&[(0, -1), (2, -1)], 1),
        row(&[(0, 1), (2, 1)], -1),
    ];
    assert_eq!(point(3, &cycle), None);
    // An even sum has a point: `x0 + x2 == 2` gives `x0 = x1 = x2 = 1`.
    let even = [
        row(&[(0, 1), (1, -1)], 0),
        row(&[(1, 1), (2, -1)], 0),
        row(&[(2, 1), (0, -1)], 0),
        row(&[(0, -1), (2, -1)], 2),
        row(&[(0, 1), (2, 1)], -2),
    ];
    let one = Int::ONE;
    assert_eq!(point(3, &even), Some(vec![one.clone(), one.clone(), one]));
}

#[test]
fn one_variable_has_its_bounds() {
    // `3 <= x0 <= 3`; `x0 >= 4` and `x0 <= 3`; no row at all.
    assert_eq!(
        point(1, &[row(&[(0, 1)], -3), row(&[(0, -1)], 3)]),
        Some(vec![Int::from(3)])
    );
    assert_eq!(point(1, &[row(&[(0, 1)], -4), row(&[(0, -1)], 3)]), None);
    assert_eq!(point(1, &[]), Some(vec![Int::ZERO]));
    // A variable in no row is 0.
    assert_eq!(
        point(3, &[row(&[(0, 1), (2, 1)], -7)]).map(|p| p[1].clone()),
        Some(Int::ZERO)
    );
}

#[test]
fn random_unit_rows_agree_with_enumeration() {
    // Rows over up to four variables, each held in `[-4, 4]` by rows of one term, so that a
    // point exists exactly when one lies in that box.
    let mut rng = Rng::new(0x07_7f1);
    let (mut with, mut without) = (0, 0);
    for _ in 0..600 {
        let n = 1 + rng.below(4);
        let mut rows: Vec<Row> = (0..n)
            .flat_map(|i| [row(&[(i, 1)], 4), row(&[(i, -1)], 4)])
            .collect();
        for _ in 0..1 + rng.below(3 * n) {
            let a = rng.below(n);
            let ca = if rng.below(2) == 0 { 1 } else { -1 };
            let k = rng.int(-3, 3);
            let b = rng.below(n);
            if b == a {
                rows.push(row(&[(a, ca)], k));
            } else {
                let cb = if rng.below(2) == 0 { 1 } else { -1 };
                rows.push(row(&[(a, ca), (b, cb)], k));
            }
        }
        let expected = enumerated(&rows, n, 4);
        assert_eq!(point(n, &rows).is_some(), expected, "{rows:?}");
        let f = formula(&rows);
        let found = satisfiable(&f).expect("answered");
        assert_eq!(found.is_some(), expected, "{f}");
        if let Some(m) = found {
            assert!(f.holds(&m), "{m:?} fails {f}");
        }
        if expected {
            with += 1;
        } else {
            without += 1;
        }
    }
    // Both answers are well represented.
    assert!(
        with > 100 && without > 100,
        "{with} with a point, {without} without"
    );
}

/// `x[a] - x[b]` within `[lo, hi]`.
fn between(a: usize, b: usize, lo: i64, hi: i64) -> Formula {
    let d = x(a).plus(&x(b).times(-1));
    Formula::and(vec![
        Formula::Con(Con::ge(&d, &Lin::constant(lo))),
        Formula::Con(Con::ge(&Lin::constant(hi), &d)),
    ])
}

/// The value of `x[i]` in a model, zero when absent.
fn value(m: &Model, i: usize) -> i128 {
    m.get(&Atom::Sym(Arc::from(format!("x{i}"))))
        .map_or(Some(0), Int::to_i128)
        .expect("a small value")
}

#[test]
fn a_disjunction_of_unit_rows_is_decided_and_placed() {
    // A path of five differences `x[i+1] - x[i]`, each in `[1, 2]` or in `[-9, -8]` from the
    // step `from` on, and in `[1, 2]` before it: with `m` of them in the second, their sum
    // `x5 - x0` lies in `[5 - 10m, 10 - 10m]`, so in `[5, 10]`, `[-5, 0]`, `[-15, -10]`, … and
    // never in `[1, 4]`.
    let path = |from: usize, lo: i64, hi: i64| {
        let mut parts: Vec<Formula> = (0..5)
            .map(|i| {
                let up = between(i + 1, i, 1, 2);
                if i < from {
                    up
                } else {
                    Formula::or(vec![up, between(i + 1, i, -9, -8)])
                }
            })
            .collect();
        parts.push(between(5, 0, lo, hi));
        Formula::and(parts)
    };
    // Five disjunctions, `x5 == x0`: `decide` finds four steps up and one down.
    let f = path(0, 0, 0);
    assert_eq!(decide(&f), Ok(true), "{f}");
    // `x5 - x0` in `[1, 4]`: no choice of arms reaches it.
    let gap = path(0, 1, 4);
    assert_eq!(decide(&gap), Ok(false), "{gap}");
    // `satisfiable` searches as `decide` does: for each disjunction it takes the first arm that
    // meets what it has taken and the rows the disjunctions imply (each step in `[-9, 2]`), and
    // never undoes one. Without those rows it took two steps down, which the three steps left
    // cannot balance, and was refused (`Refusal::Disjuncts`); with them a second step down leaves
    // the rest a sum of at least 16 from three steps of at most 2, so it is not taken.
    let m = satisfiable(&f).expect("answered").expect("a point");
    assert!(f.holds(&m), "{m:?} fails {f}");
    assert_eq!(value(&m, 5), value(&m, 0));
    let down = (0..5).filter(|&i| value(&m, i + 1) < value(&m, i)).count();
    assert_eq!(down, 1, "{m:?}");
    assert_eq!(satisfiable(&gap), Ok(None), "{gap}");
    // With one disjunction, the last step, its first arm misses and the second gives the point,
    // placed from the potential.
    let one = path(4, 0, 0);
    assert_eq!(decide(&one), Ok(true), "{one}");
    let m = satisfiable(&one).expect("answered").expect("a point");
    assert!(one.holds(&m), "{m:?} fails {one}");
    assert_eq!(value(&m, 5), value(&m, 0));
    assert_eq!(value(&m, 5) - value(&m, 4), -8);
}

/// A path of `n` steps `x[i+1] - x[i]`, each in `[1, 2]` or in `[-9, -8]`, with `x[n] == x[0]`:
/// a point takes between `n/10` and `n/5` steps down.
fn round_trip(n: usize) -> Formula {
    let mut parts: Vec<Formula> = (0..n)
        .map(|i| Formula::or(vec![between(i + 1, i, 1, 2), between(i + 1, i, -9, -8)]))
        .collect();
    parts.push(between(n, 0, 0, 0));
    Formula::and(parts)
}

/// The steps down of a point of [`round_trip`], checked to be one.
fn steps_down(n: usize, f: &Formula) -> usize {
    let m = satisfiable(f).expect("answered").expect("a point");
    assert!(f.holds(&m), "{m:?} fails a round trip of {n}");
    (0..n).filter(|&i| value(&m, i + 1) < value(&m, i)).count()
}

#[test]
fn satisfiable_agrees_with_decide_on_disjunctions_of_unit_rows() {
    // Up to five variables, each in `[-3, 3]`, three to eight disjunctions of two or three arms,
    // each arm one or two unit rows: whenever `decide` answers, `satisfiable` gives the same
    // answer, and the point it gives meets the formula; both agree with enumeration. Before
    // `satisfiable` asked the rows the disjunctions imply, as `decide` does, it was refused on
    // some of these where `decide` answered.
    let mut rng = Rng::new(0x9e_ed1);
    let (mut with, mut without) = (0, 0);
    for _ in 0..400 {
        let n = 2 + rng.below(4);
        let mut rows: Vec<Row> = (0..n)
            .flat_map(|i| [row(&[(i, 1)], 3), row(&[(i, -1)], 3)])
            .collect();
        let unit = |rng: &mut Rng| {
            let a = rng.below(n);
            let b = (a + 1 + rng.below(n - 1)) % n;
            let s = |rng: &mut Rng| if rng.below(2) == 0 { 1 } else { -1 };
            let (ca, cb) = (s(rng), s(rng));
            row(&[(a, ca), (b, cb)], rng.int(-4, 1))
        };
        for _ in 0..rng.below(n) {
            rows.push(unit(&mut rng));
        }
        let mut parts = vec![formula(&rows)];
        let mut ors: Vec<Vec<Vec<Row>>> = Vec::new();
        for _ in 0..3 + rng.below(6) {
            let arms: Vec<Vec<Row>> = (0..2 + rng.below(2))
                .map(|_| (0..1 + rng.below(2)).map(|_| unit(&mut rng)).collect())
                .collect();
            parts.push(Formula::or(arms.iter().map(|a| formula(a)).collect()));
            ors.push(arms);
        }
        let f = Formula::and(parts);
        // Whether some point of the box meets the rows and one arm of each disjunction.
        let expected = {
            let mut p = vec![Int::from(-3); n];
            'points: loop {
                if meets(&rows, &p) && ors.iter().all(|arms| arms.iter().any(|a| meets(a, &p))) {
                    break true;
                }
                for v in &mut p {
                    if *v < Int::from(3) {
                        *v = &*v + &Int::ONE;
                        continue 'points;
                    }
                    *v = Int::from(-3);
                }
                break false;
            }
        };
        let Ok(decided) = decide(&f) else {
            continue;
        };
        assert_eq!(decided, expected, "{f}");
        let found = satisfiable(&f).unwrap_or_else(|e| panic!("{e:?} where decide answers {f}"));
        assert_eq!(found.is_some(), decided, "{f}");
        if let Some(m) = found {
            assert!(f.holds(&m), "{m:?} fails {f}");
            with += 1;
        } else {
            without += 1;
        }
    }
    assert!(
        with > 100 && without > 100,
        "{with} with a point, {without} without"
    );
}

#[test]
fn a_round_trip_of_steps_up_or_down_is_placed() {
    // Every length from 1 to 40: a point exactly when some `m` steps down balance `n - m` up,
    // `8m <= 2(n - m)` and `9m >= n - m`, so from 5 on, and at 1 to 4 none.
    for n in 1..=40 {
        let f = round_trip(n);
        let any = (0..=n).any(|m| 10 * m >= n && 5 * m <= n);
        assert_eq!(decide(&f), Ok(any), "a round trip of {n}");
        if any {
            let down = steps_down(n, &f);
            assert!(10 * down >= n && 5 * down <= n, "{down} of {n} down");
        } else {
            assert_eq!(satisfiable(&f), Ok(None), "a round trip of {n}");
        }
    }
}

/// The point of a round trip of 64 and of 512 steps, each up or down, built first.
#[test]
fn the_point_of_a_round_trip_scales() {
    let (small, large) = (round_trip(64), round_trip(scaling::FACTOR * 64));
    steps_down(64, &small);
    steps_down(scaling::FACTOR * 64, &large);
    scaling::check("the point of a round trip of steps up or down", 64, |m| {
        drop(satisfiable(if m == 64 { &small } else { &large }));
    });
}
