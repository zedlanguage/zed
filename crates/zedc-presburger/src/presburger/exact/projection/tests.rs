use super::*;

fn sym(n: &str) -> Atom {
    Atom::Sym(n.into())
}
fn row(t: &[(&str, i64)], c: i64, rel: Rel) -> Con {
    Con {
        lin: Lin {
            terms: t.iter().map(|(n, k)| (sym(n), Int::from(*k))).collect(),
            constant: Int::from(c),
        },
        rel,
    }
}
fn work() -> Work {
    Work {
        used: 0,
        limit: 10_000_000,
        solver: super::super::super::SOLVER,
    }
}
/// The values of `s` in `lo..=hi` at some point of `rows` with every other atom in
/// `-r..=r`, by enumeration.
fn brute(rows: &[Con], s: &str, lo: i64, hi: i64, r: i64) -> Vec<i64> {
    let mut atoms: BTreeSet<Atom> = BTreeSet::new();
    for k in rows {
        atoms.extend(k.lin.terms.keys().cloned());
    }
    atoms.remove(&sym(s));
    let atoms: Vec<Atom> = atoms.into_iter().collect();
    let mut out = Vec::new();
    for v in lo..=hi {
        let mut idx = vec![-r; atoms.len()];
        loop {
            let mut m = Model::new();
            m.insert(sym(s), Int::from(v));
            for (a, x) in atoms.iter().zip(&idx) {
                m.insert(a.clone(), Int::from(*x));
            }
            if rows.iter().all(|k| holds_at(k, &value(&k.lin, &m))) {
                out.push(v);
                break;
            }
            let mut i = 0;
            while i < idx.len() && idx[i] == r {
                idx[i] = -r;
                i += 1;
            }
            if i == idx.len() {
                break;
            }
            idx[i] += 1;
        }
    }
    out
}
fn values(set: &IntervalSet, lo: i64, hi: i64) -> Vec<i64> {
    (lo..=hi).filter(|v| set.contains(*v)).collect()
}

#[test]
fn the_pendants_ray_is_one_projection() {
    // `w == 2a - b`, `a <= -14`, `1 <= b <= 8`: every `w <= -29`.
    let rows = vec![
        row(&[("w", 1), ("a", -2), ("b", 1)], 0, Rel::Eq),
        row(&[("a", -1)], -14, Rel::Ge),
        row(&[("b", 1)], -1, Rel::Ge),
        row(&[("b", -1)], 8, Rel::Ge),
    ];
    let mut w = work();
    let (got, tails) = ranges(
        &pugh(&rows, &sym("w"), &IntervalSet::top(), &mut w).unwrap(),
        &mut w,
    )
    .unwrap();
    assert_eq!(got, IntervalSet::range(End::NegInf, End::from(-29i64)));
    assert!(tails.is_empty());
}

#[test]
fn a_ray_with_holes_is_a_tail_and_a_filled_one_is_not() {
    // `w == 2a`, `a <= 0`: the even values up to 0, holes without end.
    let rows = vec![
        row(&[("w", 1), ("a", -2)], 0, Rel::Eq),
        row(&[("a", -1)], 0, Rel::Ge),
    ];
    let mut w = work();
    let parts = pugh(&rows, &sym("w"), &IntervalSet::top(), &mut w).unwrap();
    let (got, tails) = ranges(&parts, &mut w).unwrap();
    assert!(got.is_empty());
    assert_eq!(tails.len(), 1);
    assert_eq!(
        (tails[0].step.clone(), tails[0].have.clone()),
        (Int::from(2), vec![true, false])
    );
    // With `w == 2a + b`, `0 <= b <= 1` the holes fill.
    let rows = vec![
        row(&[("w", 1), ("a", -2), ("b", -1)], 0, Rel::Eq),
        row(&[("a", -1)], 0, Rel::Ge),
        row(&[("b", 1)], 0, Rel::Ge),
        row(&[("b", -1)], 1, Rel::Ge),
    ];
    let parts = pugh(&rows, &sym("w"), &IntervalSet::top(), &mut w).unwrap();
    assert_eq!(
        ranges(&parts, &mut w).unwrap().0,
        IntervalSet::range(End::NegInf, End::from(1i64))
    );
}

#[test]
fn the_omega_nightmare_has_no_point() {
    // Pugh 1992: 27 <= 11x + 13y <= 45, -10 <= 7x - 9y <= 4 has no integer point.
    let rows = vec![
        row(&[("x", 11), ("y", 13)], -27, Rel::Ge),
        row(&[("x", -11), ("y", -13)], 45, Rel::Ge),
        row(&[("x", 7), ("y", -9)], 10, Rel::Ge),
        row(&[("x", -7), ("y", 9)], 4, Rel::Ge),
    ];
    let mut w = work();
    let got = ranges(
        &pugh(&rows, &sym("x"), &IntervalSet::top(), &mut w).unwrap(),
        &mut w,
    )
    .unwrap()
    .0;
    assert!(got.is_empty(), "{got:?}");
}

#[test]
fn small_systems_project_to_their_enumerated_values() {
    // A fixed family of small systems with strides and non-unit bounds, each checked
    // against enumeration over a box larger than every point's coordinates.
    let mut rng = crate::seed::Rng::new(0x2545_f491_4f6c_dd1d);
    let mut next = |n: i64| rng.int(-n, n);
    for case in 0..300 {
        let names = ["s", "x", "y"];
        let mut rows = Vec::new();
        // Box every atom to keep enumeration exact.
        for n in names {
            rows.push(row(&[(n, 1)], 6, Rel::Ge));
            rows.push(row(&[(n, -1)], 6, Rel::Ge));
        }
        for _ in 0..(1 + case % 3) {
            let t: Vec<(&str, i64)> = names
                .iter()
                .map(|n| (*n, next(4)))
                .filter(|(_, k)| *k != 0)
                .collect();
            if t.is_empty() {
                continue;
            }
            let rel = if next(2) == 0 { Rel::Eq } else { Rel::Ge };
            rows.push(row(&t, next(6), rel));
        }
        let mut w = work();
        let got = ranges(
            &pugh(&rows, &sym("s"), &IntervalSet::top(), &mut w).unwrap(),
            &mut w,
        )
        .unwrap()
        .0;
        assert_eq!(
            values(&got, -6, 6),
            brute(&rows, "s", -6, 6, 6),
            "case {case}: {rows:?}"
        );
        assert!(
            values(&got, -100, -7).is_empty() && values(&got, 7, 100).is_empty(),
            "case {case}"
        );
        // With a goal, the answer may stop once the goal is held: it still holds only values
        // of the projection, and every value of the projection in the goal.
        let (a, b) = (next(6), next(6));
        let goal = IntervalSet::range(End::from(a.min(b)), End::from(a.max(b)));
        let part = ranges(&pugh(&rows, &sym("s"), &goal, &mut w).unwrap(), &mut w)
            .unwrap()
            .0;
        assert!(part.is_subset(&got), "case {case}: {part:?} beyond {got:?}");
        assert!(
            got.meet(&goal).is_subset(&part),
            "case {case}: {part:?} misses some of {got:?} in {goal:?}"
        );
    }
}

/// A goal held early stops the projection: the repaired unit's rows (`w == 0` put in) onto
/// `x` make 1,562 parts with every splinter, and far fewer once `[4, 7]` and `[9, +inf)`, the
/// goal of its first cell, are held (`exact::tests::every_name_of_the_repaired_unit_has_its_exact_answer`).
/// The rows `Σ c[j]·x[start + j] + k >= 0` of the first 8 windows of the window system of
/// `l01_38_presburger::exp_families` (width 3, 2 rows a window, n = 12, seed 1096302828291),
/// the smallest prefix of its windows whose projection onto `x0` builds a shadow past the limit
/// (FAIL-window-seed-13014466797380974686).
const WINDOWS: [(usize, [i64; 3], i64); 16] = [
    (0, [7, -10, -10], -2),
    (0, [-7, -6, 11], -3),
    (1, [-4, 6, -11], -5),
    (1, [-7, 1, 6], 0),
    (2, [-7, -2, 11], -5),
    (2, [-6, -3, -9], -6),
    (3, [-10, -11, -11], 1),
    (3, [-10, -11, -3], 1),
    (4, [-10, 4, -1], -5),
    (4, [-10, 7, -11], -1),
    (5, [5, -10, 7], -2),
    (5, [11, 5, -3], -5),
    (6, [1, 7, -1], -2),
    (6, [-8, 1, 5], -6),
    (7, [9, 6, 7], 2),
    (7, [3, 1, -11], 6),
];

/// The rows of the first `w` windows of [`WINDOWS`], with each of `x0 .. x(w+1)` in `-12..=12`.
fn window_rows(w: usize) -> Vec<Con> {
    let mut rows = Vec::new();
    for i in 0..w + 2 {
        let x = format!("x{i}");
        rows.push(row(&[(&x, 1)], 12, Rel::Ge));
        rows.push(row(&[(&x, -1)], 12, Rel::Ge));
    }
    for (start, c, k) in WINDOWS.iter().filter(|r| r.0 < w) {
        let names: Vec<String> = (0..3).map(|j| format!("x{}", start + j)).collect();
        let t: Vec<(&str, i64)> = (0..3).map(|j| (names[j].as_str(), c[j])).collect();
        rows.push(row(&t, *k, Rel::Ge));
    }
    rows
}

/// The values of `x0` at the points of [`window_rows`]`(w)`, by a dynamic program from the last
/// window back over the pairs `(x[i], x[i+1])`: O(w · 25^3).
fn window_x0(w: usize) -> Vec<i64> {
    let vals: Vec<i64> = (-12..=12).collect();
    let at = |v: i64| (v + 12) as usize;
    let mut kept = vec![[true; 25]; 25];
    for i in (0..w).rev() {
        let mine: Vec<_> = WINDOWS.iter().filter(|r| r.0 == i).collect();
        let mut before = vec![[false; 25]; 25];
        for &a in &vals {
            for &b in &vals {
                before[at(a)][at(b)] = vals.iter().any(|&c| {
                    kept[at(b)][at(c)]
                        && (mine.iter()).all(|(_, k, d)| k[0] * a + k[1] * b + k[2] * c + d >= 0)
                });
            }
        }
        kept = before;
    }
    (vals.iter().copied())
        .filter(|&a| kept[at(a)].iter().any(|&k| k))
        .collect()
}

fn limited() -> Work {
    Work {
        used: 0,
        limit: super::super::EXACT_LIMIT,
        solver: super::super::super::SOLVER,
    }
}

/// The 8 windows of [`WINDOWS`] onto `x0`: one shadow of 591,501 rows (each lower bound of
/// an atom paired with each upper bound). Before, it was built whole and only then read, so the
/// call charged 119,398,000 units, 38.5 times [`EXACT_LIMIT`] (2026-11-19), and at
/// all 10 windows its shadow of 3,212,640 rows took about 8 s against the 250 ms the limit
/// stands for. Now each row is charged as it is made, and the call is refused within one row
/// of the limit: a row reads at most the 10 atoms, so it is charged at most 11 · SOLVER_UNIT.
/// Control: [`the_window_projection_one_window_shorter_is_exact_within_the_limit`].
#[test]
fn a_shadow_past_the_limit_is_refused_while_it_is_made() {
    let mut w = limited();
    let goal = IntervalSet::range(End::from(-12i64), End::from(12i64));
    let got = pugh(&window_rows(8), &sym("x0"), &goal, &mut w);
    assert!(matches!(got, Err(Refusal::Questions)), "{got:?}");
    let row_most = 11 * super::super::SOLVER_UNIT;
    assert!(
        w.used <= w.limit + row_most,
        "{} units past the limit {}",
        w.used - w.limit,
        w.limit
    );
}

/// The control of [`a_shadow_past_the_limit_is_refused_while_it_is_made`]: the first 7
/// windows project onto `x0` within the limit (325,032 units, 2026-11-19), to the values the
/// dynamic program gives, so the refusal there comes from the size of its shadow.
#[test]
fn the_window_projection_one_window_shorter_is_exact_within_the_limit() {
    let mut w = limited();
    let goal = IntervalSet::range(End::from(-12i64), End::from(12i64));
    let parts = pugh(&window_rows(7), &sym("x0"), &goal, &mut w).expect("answered");
    let (set, tails) = ranges(&parts, &mut w).expect("answered");
    assert!(tails.is_empty());
    assert!(w.used <= w.limit, "{} of {}", w.used, w.limit);
    let expected = window_x0(7);
    assert!(!expected.is_empty());
    assert_eq!(values(&set, -12, 12), expected);
}

#[test]
fn a_held_goal_stops_the_splinters() {
    let rows = vec![
        row(&[("x", 4), ("y", -10), ("z", -12)], 11, Rel::Ge),
        row(&[("x", 10), ("y", -10), ("z", -11)], -28, Rel::Ge),
        row(&[("x", 4), ("y", -1), ("z", 12)], -28, Rel::Ge),
        row(&[("x", -5), ("y", 12), ("z", -1)], 31, Rel::Ge),
    ];
    let mut w = work();
    let whole = pugh(&rows, &sym("x"), &IntervalSet::top(), &mut w).unwrap();
    let goal = IntervalSet::from_pieces(vec![
        (End::from(4i64), End::from(7i64)),
        (End::from(9i64), End::PosInf),
    ]);
    let mut v = work();
    let part = pugh(&rows, &sym("x"), &goal, &mut v).unwrap();
    assert!(
        part.len() * 10 < whole.len(),
        "{} of {}",
        part.len(),
        whole.len()
    );
    assert!(v.used * 10 < w.used, "{} of {}", v.used, w.used);
    let expected = IntervalSet::range(End::from(4i64), End::PosInf);
    assert_eq!(ranges(&whole, &mut w).unwrap().0, expected);
    let got = ranges(&part, &mut v).unwrap().0;
    assert!(goal.is_subset(&got) && got.is_subset(&expected), "{got:?}");
}
