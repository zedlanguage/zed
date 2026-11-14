//! Many disjunctions over one linked group of rows (plan items DISJ-diff-fast and
//! DISJ-incremental): each disjunct is tested against the base projected onto the atoms of
//! the disjuncts near it, so `n` disjunctions cost about `n log n`, not `n` solves of the
//! whole group.

use zed_tests::scaling;
use zedc::store::presburger::{self, Atom, Con, Formula, Lin, decide, project_each};

fn x(i: usize) -> Lin {
    Lin::atom(Atom::Sym(format!("x{i:05}").into()))
}

fn y(i: usize) -> Lin {
    Lin::atom(Atom::Sym(format!("y{i:05}").into()))
}

fn ge(l: Lin) -> Formula {
    Formula::Con(Con::ge(&l, &Lin::constant(0)))
}

fn eq(l: Lin) -> Formula {
    Formula::Con(Con::eq(&l, &Lin::constant(0)))
}

/// `x[i + 1] - x[i]`.
fn step(i: usize) -> Lin {
    x(i + 1).minus(&x(i))
}

/// Which disjunct holds at the point the solver finds for the base.
#[derive(Clone, Copy, PartialEq)]
pub enum Holds {
    First,
    None,
}

/// A chain of difference rows `x[i + 1] - x[i] >= 1` over `n` stages, `0 <= x[0]` and
/// `x[n - 1] <= 4n`, with a disjunction at every fourth stage: `x[i + 1] - x[i] <= 1 ||
/// x[i + 1] - x[i] >= 3` (the first holds at the least point), or `x[i + 1] - x[i] == 2 ||
/// x[i + 1] - x[i] == 3` (neither does).
pub fn difference_chain(n: usize, holds: Holds) -> Formula {
    let mut fs = vec![ge(x(0)), ge(Lin::constant(4 * n as i128).minus(&x(n - 1)))];
    fs.extend((0..n - 1).map(|i| ge(step(i).minus(&Lin::constant(1)))));
    for i in (0..n - 1).step_by(4) {
        let s = step(i);
        fs.push(Formula::or(match holds {
            Holds::First => vec![
                ge(Lin::constant(1).minus(&s)),
                ge(s.minus(&Lin::constant(3))),
            ],
            Holds::None => vec![
                eq(s.minus(&Lin::constant(2))),
                eq(s.minus(&Lin::constant(3))),
            ],
        }));
    }
    Formula::and(fs)
}

/// The rows of three atoms `x[i + 1] - x[i] - y[i] >= 0` with `1 <= y[i] <= 2`, over `n`
/// stages, `0 <= x[0]` and `x[n - 1] <= 8n`, with a disjunction at every fourth stage on
/// `x[i + 1] - x[i] + y[i]`: `<= 2 || >= 5` (the first holds at the least point), or `== 4 ||
/// == 5` (neither does).
pub fn general_chain(n: usize, holds: Holds) -> Formula {
    let mut fs = general_rows(n);
    for i in (0..n - 1).step_by(4) {
        let s = step(i).plus(&y(i));
        fs.push(Formula::or(match holds {
            Holds::First => vec![
                ge(Lin::constant(2).minus(&s)),
                ge(s.minus(&Lin::constant(5))),
            ],
            Holds::None => vec![
                eq(s.minus(&Lin::constant(4))),
                eq(s.minus(&Lin::constant(5))),
            ],
        }));
    }
    Formula::and(fs)
}

/// The rows of [`general_chain`] without its disjunctions: `x[i + 1] - x[i] - y[i] >= 0` with
/// `1 <= y[i] <= 2` over `n` stages, `0 <= x[0]` and `x[n - 1] <= 8n`.
fn general_rows(n: usize) -> Vec<Formula> {
    let mut fs = vec![ge(x(0)), ge(Lin::constant(8 * n as i128).minus(&x(n - 1)))];
    for i in 0..n - 1 {
        fs.push(ge(step(i).minus(&y(i))));
        fs.push(ge(y(i).minus(&Lin::constant(1))));
        fs.push(ge(Lin::constant(2).minus(&y(i))));
    }
    fs
}

/// The symbol asked for: the middle of the chain.
pub(super) fn middle(n: usize) -> [Atom; 1] {
    [Atom::Sym(format!("x{:05}", n / 2).into())]
}

/// Projects the middle of the chain `fam(m, holds)` at each size `m` of a scaling check.
pub(super) fn projects(what: &str, n: usize, fam: fn(usize, Holds) -> Formula, holds: Holds) {
    let inputs = scaling::inputs(n, |m| fam(m, holds));
    scaling::check_order(what, n, 1, |m| {
        let r = project_each(&inputs[&m], &middle(m)).expect("a projection");
        assert!(r.0[0].as_ref().is_ok_and(|s| !s.is_empty()));
    });
}

/// Decides the chain `fam(m, Holds::None)` at each size `m` of a scaling check.
pub(super) fn decides(what: &str, n: usize, fam: fn(usize, Holds) -> Formula) {
    let inputs = scaling::inputs(n, |m| fam(m, Holds::None));
    scaling::check_order(what, n, 1, |m| {
        assert_eq!(decide(&inputs[&m]), Ok(true));
    });
}

/// The exact hull of the middle of the difference chain, found by the rows its disjunctions imply
/// where the projection before them stopped wider (`[36, 221]`).
#[test]
fn the_middle_of_a_chain_whose_disjuncts_do_not_hold_has_its_exact_hull() {
    let n = 64;
    let r = project_each(&difference_chain(n, Holds::None), &middle(n)).expect("a projection");
    let s = r.0[0].clone().expect("a hull");
    // Every step at least 1, and at least 2 at the 8 stages of disjunctions before the
    // middle; the 31 steps after it, 8 of them at disjunctions, end at most at `4n`.
    let (lo, hi) = (32 + 8, 4 * 64 - (31 + 8));
    assert!(s.contains(lo) && !s.contains(lo - 1), "{s:?}");
    assert!(s.contains(hi) && !s.contains(hi + 1), "{s:?}");
}

/// The exact hull of the middle of the chain of three-atom rows (plan item
/// DISJ-three-atom-empty), where the projection before it stopped wider (`[36, 477]`).
#[test]
fn the_middle_of_a_chain_of_three_atom_rows_whose_disjuncts_do_not_hold_has_its_exact_hull() {
    let n = 64;
    let r = project_each(&general_chain(n, Holds::None), &middle(n)).expect("a projection");
    let s = r.0[0].clone().expect("a hull");
    // Every step at least 1, and at least 2 at the 8 stages of disjunctions before the
    // middle (`y <= 2` with `s >= 4`); the 31 steps after it, 8 of them at disjunctions, end
    // at most at `8n`.
    let (lo, hi) = (32 + 8, 8 * 64 - (31 + 8));
    assert!(s.contains(lo) && !s.contains(lo - 1), "{s:?}");
    assert!(s.contains(hi) && !s.contains(hi + 1), "{s:?}");
}

/// The hull of the middle of a chain of three-atom rows with no disjunction (plan item
/// THREE-atom-exponent) is found without asking the solver for a side of a hull: each `y[i]`,
/// bounded below by its own row only, is set to its least value 1, which leaves difference
/// rows, whose hulls are shortest paths. Before, each side was a search of O(log n) questions
/// about the whole chain, 77% of the work of projecting [`general_chain`] at 2048 stages.
#[test]
fn the_middle_of_a_chain_of_three_atom_rows_is_found_without_asking_for_a_side() {
    for n in [8, 64, 512] {
        let f = Formula::and(general_rows(n));
        presburger::hull_sides_asked();
        let r = project_each(&f, &middle(n)).expect("a projection");
        assert_eq!(presburger::hull_sides_asked(), 0, "{n} stages");
        let s = r.0[0].clone().expect("a hull");
        // Every step at least 1: the middle lies in [n / 2, 8n - (n - 1 - n / 2)].
        let (lo, hi) = ((n / 2) as i64, (8 * n - (n - 1 - n / 2)) as i64);
        assert!(s.contains(lo) && !s.contains(lo - 1), "{s:?}");
        assert!(s.contains(hi) && !s.contains(hi + 1), "{s:?}");
    }
}

/// A chain of three-atom rows of `n` stages as [`general_chain`] with `x[n - 1] <= end`, and
/// at every `every`-th stage `x[i + 1] - x[i] + y[i]` in `sums` and, unless `steps` is empty,
/// `x[i + 1] - x[i]` in `steps`. Each equation `l == v` of a disjunction is written `l - v ==
/// 0`, or `v - l == 0` when `negated`.
fn small_chain(
    n: usize,
    every: usize,
    end: i128,
    sums: &[i128],
    steps: &[i128],
    negated: bool,
) -> Formula {
    let mut fs = vec![ge(x(0)), ge(Lin::constant(end).minus(&x(n - 1)))];
    for i in 0..n - 1 {
        fs.push(ge(step(i).minus(&y(i))));
        fs.push(ge(y(i).minus(&Lin::constant(1))));
        fs.push(ge(Lin::constant(2).minus(&y(i))));
    }
    let any_of = |l: &Lin, vs: &[i128]| {
        Formula::or(
            vs.iter()
                .map(|v| match negated {
                    false => eq(l.minus(&Lin::constant(*v))),
                    true => eq(Lin::constant(*v).minus(l)),
                })
                .collect(),
        )
    };
    for i in (0..n - 1).step_by(every) {
        fs.push(any_of(&step(i).plus(&y(i)), sums));
        if !steps.is_empty() {
            fs.push(any_of(&step(i), steps));
        }
    }
    Formula::and(fs)
}

/// A chain of three-atom rows of `n` stages (plan item DISJ-dpll) as [`small_chain`] with
/// `x[n - 1] <= 8n` and, at every fourth stage, two disjunctions that together leave one step
/// where the rows each implies allow more: `x[i + 1] - x[i]` in {3, 7} and `x[i + 1] - x[i] +
/// y[i]` in {6, 9}, with `1 <= y[i] <= 2`, force the step 7 (and `y[i] == 2`), where the
/// implied rows allow 4. How it is written must not change any answer or the cost.
fn joint_chain(n: usize, written: Written) -> Formula {
    let end = 8 * n as i128;
    match written {
        Written::AsIs => small_chain(n, 4, end, &[6, 9], &[3, 7], false),
        Written::Negated => small_chain(n, 4, end, &[6, 9], &[3, 7], true),
        Written::Reversed => {
            let f = small_chain(n, 4, end, &[9, 6], &[7, 3], false);
            let Formula::And(fs) = &f else {
                panic!("a conjunction");
            };
            Formula::and(fs.iter().rev().cloned().collect())
        }
    }
}

/// How [`joint_chain`] is written: as is, with each disjunction's values and all the parts in
/// the reverse order, or with each equation of a disjunction negated (`v - l == 0`), which
/// orders each disjunction's disjuncts the other way (item PROJECT-each-canon).
#[derive(Clone, Copy, Debug)]
pub(super) enum Written {
    AsIs,
    Reversed,
    Negated,
}

/// The exact hull of the middle of [`joint_chain`]: every step at least 1, and 7 at the 8
/// stages of disjunctions before the middle; the 31 steps after it, 8 of them at
/// disjunctions, end at most at `8n`.
const JOINT_MIDDLE_64: (i64, i64) = (32 + 6 * 8, 8 * 64 - (31 + 6 * 8));

pub(super) fn joint_chain_scales(written: Written) {
    let inputs = scaling::inputs(128, |m| joint_chain(m, written));
    scaling::check_order(
        &format!(
            "a chain whose disjunctions jointly leave one step, written {written:?}, projected"
        ),
        128,
        1,
        |m| {
            let r = project_each(&inputs[&m], &middle(m)).expect("a projection");
            assert!(r.0[0].as_ref().is_ok_and(|s| !s.is_empty()));
        },
    );
}

#[test]
fn the_middle_of_a_chain_whose_disjunctions_jointly_leave_one_step_has_its_exact_hull() {
    let n = 64;
    for written in [Written::AsIs, Written::Reversed, Written::Negated] {
        let r = project_each(&joint_chain(n, written), &middle(n)).expect("a projection");
        let s = r.0[0].clone().expect("a hull");
        let (lo, hi) = JOINT_MIDDLE_64;
        assert!(s.contains(lo) && !s.contains(lo - 1), "{written:?}: {s:?}");
        assert!(s.contains(hi) && !s.contains(hi + 1), "{written:?}: {s:?}");
        assert!(r.1.is_empty(), "{written:?}: {:?}", r.1);
    }
}

/// The least and greatest value of each `x[i]` over the points of `f`, a chain of `n` stages
/// ending at most at `end`, by trying every `x[0]` and every step and `y[i]` the rows of a
/// stage allow (`x` rising by at least `y[i]`, up to `end`), each point read on `f` itself.
fn brute_hulls(f: &Formula, n: usize, end: i128) -> Option<Vec<(i128, i128)>> {
    fn walk(
        f: &Formula,
        n: usize,
        end: i128,
        at: &mut Vec<(i128, i128)>,
        hulls: &mut Option<Vec<(i128, i128)>>,
    ) {
        let i = at.len() - 1;
        if i == n - 1 {
            let mut m = zedc::store::presburger::Model::new();
            for (k, (xv, yv)) in at.iter().enumerate() {
                m.insert(Atom::Sym(format!("x{k:05}").into()), (*xv).into());
                if k < n - 1 {
                    m.insert(Atom::Sym(format!("y{k:05}").into()), (*yv).into());
                }
            }
            if f.holds(&m) {
                let h = hulls.get_or_insert_with(|| at.iter().map(|p| (p.0, p.0)).collect());
                for (h, p) in h.iter_mut().zip(at.iter()) {
                    *h = (h.0.min(p.0), h.1.max(p.0));
                }
            }
            return;
        }
        let xi = at[i].0;
        for yv in 1..=2 {
            at[i].1 = yv;
            for next in xi + yv..=end {
                at.push((next, 0));
                walk(f, n, end, at, hulls);
                at.pop();
            }
        }
    }
    let mut hulls = None;
    for x0 in 0..=end {
        walk(f, n, end, &mut vec![(x0, 0)], &mut hulls);
    }
    hulls
}

/// A case of [`small_chain`]: its stages, its stride of disjunctions, its end, sums and steps.
type Small<'a> = (usize, usize, i128, &'a [i128], &'a [i128]);

/// The hull of each `x[i]` that [`project_each`] gives, against the points counted one by
/// one: disjunctions with no disjunct holding at the base's point, with a value missing from
/// the hull of their form (`4` or `6`), two on one stage that leave one step only (`3` or `7`
/// with sums `6` or `9`, so 7: the rows each implies allow 4), and none at all.
#[test]
fn hulls_of_small_chains_of_three_atom_rows_are_those_of_their_points() {
    let cases: [Small; 8] = [
        (6, 2, 14, &[4, 5], &[]),
        (6, 2, 14, &[4, 6], &[]),
        (7, 3, 16, &[4, 5], &[]),
        (5, 2, 18, &[6, 9], &[3, 7]),
        (5, 2, 17, &[6, 9], &[3, 7]),
        (5, 2, 5, &[4, 5], &[]),
        // [`joint_chain`]'s stride, with room past its one least point, and at that point
        // with each disjunction's values in the reverse order.
        (6, 4, 20, &[6, 9], &[3, 7]),
        (6, 4, 17, &[9, 6], &[7, 3]),
    ];
    for (n, every, end, sums, steps) in cases {
        let f = small_chain(n, every, end, sums, steps, false);
        let syms: Vec<Atom> = (0..n)
            .map(|i| Atom::Sym(format!("x{i:05}").into()))
            .collect();
        let got = project_each(&f, &syms).expect("a projection");
        let want = brute_hulls(&f, n, end);
        let case = format!("n {n}, every {every}, end {end}, sums {sums:?}, steps {steps:?}");
        for (i, r) in got.0.iter().enumerate() {
            let s = r.as_ref().expect("a hull");
            match &want {
                None => assert!(s.is_empty(), "{case}: x{i} {s:?}, no point"),
                Some(h) => {
                    let (lo, hi) = (h[i].0 as i64, h[i].1 as i64);
                    assert!(
                        s.contains(lo)
                            && !s.contains(lo - 1)
                            && s.contains(hi)
                            && !s.contains(hi + 1),
                        "{case}: x{i} {s:?}, points from {lo} to {hi}"
                    );
                }
            }
        }
    }
}

/// A chain of `n` stages (plan item DISJ-dpll) where each disjunction is shown empty only
/// once the one before it is gone: `x[0] == 0`, `x[i + 1] - x[i]` in {0, 10} and `x[i + 1]`
/// in {0, 15}. Step 10 leaves `x[1]` at 10, so `x[1]` is 0 and the step 0, and so on to the
/// end: every `x[i]` is 0. `flipped` lists the parts in the reverse order, so that the
/// removals run against the order of the disjunctions.
pub(super) fn cascade(n: usize, flipped: bool) -> Formula {
    let any_of = |l: &Lin, vs: &[i128]| {
        Formula::or(vs.iter().map(|v| eq(l.minus(&Lin::constant(*v)))).collect())
    };
    let mut fs = vec![eq(x(0))];
    for i in 0..n - 1 {
        fs.push(any_of(&step(i), &[0, 10]));
        fs.push(any_of(&x(i + 1), &[0, 15]));
    }
    if flipped {
        fs.reverse();
    }
    Formula::and(fs)
}

/// An atom by name.
fn named(n: &str) -> Lin {
    Lin::atom(Atom::Sym(n.into()))
}

/// `l` is one of `vs`, as a disjunction of equations.
fn one_of(l: &Lin, vs: &[i128]) -> Formula {
    Formula::or(vs.iter().map(|v| eq(l.minus(&Lin::constant(*v)))).collect())
}

/// The hull of `z` over `f`, with `lo` and `hi` its ends (`None`: unbounded), and no part
/// left out.
fn assert_hull(f: &Formula, lo: Option<i64>, hi: Option<i64>) {
    let r = project_each(f, &[Atom::Sym("z".into())]).expect("a projection");
    let s = r.0[0].clone().expect("a hull");
    let probe = 1_000_000;
    match lo {
        Some(lo) => assert!(s.contains(lo) && !s.contains(lo - 1), "{f}: {s:?}"),
        None => assert!(s.contains(-probe), "{f}: {s:?}"),
    }
    match hi {
        Some(hi) => assert!(s.contains(hi) && !s.contains(hi + 1), "{f}: {s:?}"),
        None => assert!(s.contains(probe), "{f}: {s:?}"),
    }
    assert!(r.1.is_empty(), "{f}: {:?}", r.1);
}

/// `b + c >= z` with `b` in {0, 2} and `c` in {0, 3}: each disjunction alone leaves `z`
/// unbounded above (the other's atom is free), and the rows the two imply, `0 <= b <= 2` and
/// `0 <= c <= 3`, give `z <= 5`, reached at `b = 2`, `c = 3` (item PRES-pendants-wider: seed 17
/// case 121 of `l01_39_reduced_product::pendants`, `z0` unbounded below where it is `-21`).
#[test]
fn an_unbounded_end_that_the_rows_the_disjunctions_imply_bound_is_read() {
    let f = Formula::and(vec![
        ge(named("b").plus(&named("c")).minus(&named("z"))),
        one_of(&named("b"), &[0, 2]),
        one_of(&named("c"), &[0, 3]),
    ]);
    assert_hull(&f, None, Some(5));
}

/// `z <= 5` with `x >= 1 || z <= 0` and `x <= 0 || z <= 0`: `z >= 1` leaves `x >= 1` and
/// `x <= 0` together, so `z <= 0`, reached at `x = 0`, `z = 0`. No row the disjunctions imply
/// bounds `z` above but `z <= 5`, so only a question of the whole formula past the end does (item
/// PRES-pendants-wider: `z1 <= 6` of seed 11 case 226 of `l01_39_reduced_product::pendants`,
/// left at `[-3, inf]` before).
#[test]
fn a_finite_end_whose_other_is_infinite_is_tightened_by_cases() {
    let (x, z) = (named("x"), named("z"));
    let f = Formula::and(vec![
        ge(Lin::constant(5).minus(&z)),
        Formula::or(vec![ge(x.minus(&Lin::constant(1))), ge(z.times(-1))]),
        Formula::or(vec![ge(x.times(-1)), ge(z.times(-1))]),
    ]);
    assert_hull(&f, None, Some(0));
    // The same with the end below: `z >= -5`, `x >= 1 || z >= 0`, `x <= 0 || z >= 0`.
    let g = Formula::and(vec![
        ge(z.plus(&Lin::constant(5))),
        Formula::or(vec![ge(x.minus(&Lin::constant(1))), ge(z.clone())]),
        Formula::or(vec![ge(x.times(-1)), ge(z.clone())]),
    ]);
    assert_hull(&g, Some(0), None);
}

/// `z <= 0 || a >= 5` with `z <= 0 || a <= 3`: `z <= 0` by cases, and no row bounds `z` at
/// either end; the disjunct `z <= 0` gives 0 as a candidate end, and one question, the formula
/// with `z >= 1`, shows no point lies past it (item PRES-pendants-wider: `z1 <= 6` of seed 11
/// case 226 of `l01_39_reduced_product::pendants`, left at `[-3, inf]` before).
#[test]
fn an_end_only_case_reasoning_bounds_is_read_from_a_disjunct() {
    let (a, z) = (named("a"), named("z"));
    let f = Formula::and(vec![
        Formula::or(vec![ge(z.times(-1)), ge(a.minus(&Lin::constant(5)))]),
        Formula::or(vec![ge(z.times(-1)), ge(Lin::constant(3).minus(&a))]),
    ]);
    assert_hull(&f, None, Some(0));
}

/// `z <= x + y` with `x <= 0` and `y <= 0` each by cases (`x <= 0 || p >= 1` with
/// `x <= 0 || p <= 0`, the same for `y` with `q`): `z <= 0`, but no disjunct bounds `z` alone
/// (`x <= 0` leaves `y` free), so no candidate end is found and the hull stays open, sound and
/// wider than the exact `z <= 0` (the tradeoff of [`project_each`] at `tighten`, item
/// PRES-pendants-wider).
#[test]
fn an_end_that_cases_bound_at_a_value_no_disjunct_gives_is_left_open() {
    let (x, y, z, p, q) = (named("x"), named("y"), named("z"), named("p"), named("q"));
    let mut fs = vec![ge(x.plus(&y).minus(&z))];
    for (v, w) in [(&x, &p), (&y, &q)] {
        fs.push(Formula::or(vec![
            ge(v.times(-1)),
            ge(w.minus(&Lin::constant(1))),
        ]));
        fs.push(Formula::or(vec![ge(v.times(-1)), ge(w.times(-1))]));
    }
    assert_hull(&Formula::and(fs), None, None);
}

/// A chain of `n` stages `y[i + 1] >= y[i] - 1` with `y[0] == 0`, and at the middle stage
/// `m`, `x >= 1 || y[m] >= 0` and `x <= 0 || y[m] >= 0`: by cases `y[m] >= 0`, where the rows
/// allow `-m`; no row bounds it above (item PRES-pendants-wider). Cases at every stage
/// (`x[i] >= 1 || y[i + 1] >= y[i]` and `x[i] <= 0 || y[i + 1] >= y[i]`) give the same bound
/// by cases, but the search through the disjunctions ([`pick`]) refuses its questions, so
/// that hull stays sound and wider (the tradeoff of plan item DISJ-dpll).
pub(super) fn case_chain(n: usize) -> Formula {
    let m = n / 2;
    let mut fs = vec![eq(y(0))];
    for i in 0..n - 1 {
        fs.push(ge(y(i + 1).minus(&y(i)).plus(&Lin::constant(1))));
    }
    let x = named("x");
    fs.push(Formula::or(vec![ge(x.minus(&Lin::constant(1))), ge(y(m))]));
    fs.push(Formula::or(vec![ge(x.times(-1)), ge(y(m))]));
    Formula::and(fs)
}

/// `z <= 5` with `x >= 1 || z <= 0`, `x <= 0 || z <= 0` and the same two with `w`: `x` and
/// `w` are told apart by no structure, so the formula is asked of [`decide`], which gives no
/// point, and the search for the upper end steps down from 5 by 1, 2, 4 to a value with no
/// proof that no point lies above it, then bisects (item PRES-pendants-wider; left at 5
/// before).
#[test]
fn a_finite_end_is_tightened_where_the_solver_gives_no_point() {
    let (x, w, z) = (named("x"), named("w"), named("z"));
    let mut fs = vec![ge(Lin::constant(5).minus(&z))];
    for v in [&x, &w] {
        fs.push(Formula::or(vec![
            ge(v.minus(&Lin::constant(1))),
            ge(z.times(-1)),
        ]));
        fs.push(Formula::or(vec![ge(v.times(-1)), ge(z.times(-1))]));
    }
    assert_hull(&Formula::and(fs), None, Some(0));
}

/// `y == a || y == b`, or `y == a || b <= y <= c` with `c` given.
fn two_values(y: &Lin, a: i128, b: i128, c: Option<i128>) -> Formula {
    let second = match c {
        None => eq(y.minus(&Lin::constant(b))),
        Some(c) => Formula::and(vec![
            ge(y.minus(&Lin::constant(b))),
            ge(Lin::constant(c).minus(y)),
        ]),
    };
    Formula::or(vec![eq(y.minus(&Lin::constant(a))), second])
}

/// Each `y[i]` takes one of two values (or a value and a short range), with one row
/// `Σ c[i] y[i] == t`; the projections of every `y[i]`, asked at once.
fn projected_two_values(
    doms: &[(i128, i128, Option<i128>)],
    cs: &[i128],
    t: i128,
) -> Vec<Option<(i64, i64)>> {
    let ys: Vec<Lin> = (0..doms.len()).map(|i| named(&format!("y{i}"))).collect();
    let mut fs: Vec<Formula> = ys
        .iter()
        .zip(doms)
        .map(|(y, &(a, b, c))| two_values(y, a, b, c))
        .collect();
    let row = ys
        .iter()
        .zip(cs)
        .fold(Lin::constant(-t), |s, (y, c)| s.plus(&y.times(*c)));
    fs.push(eq(row));
    let atoms: Vec<Atom> = (0..doms.len())
        .map(|i| Atom::Sym(format!("y{i}").into()))
        .collect();
    let (each, _) = project_each(&Formula::and(fs), &atoms).expect("a projection");
    each.into_iter()
        .map(|s| {
            let s = s.expect("a hull");
            assert!(!s.contains(-1_000) && !s.contains(1_000), "{s:?}");
            let vs: Vec<i64> = (-100..=100).filter(|v| s.contains(*v)).collect();
            vs.first().map(|l| (*l, vs[vs.len() - 1]))
        })
        .collect()
}

/// Random case 1063 of the harness: the one point is `(3, 0, 0, 29, 17, 16)`. The solver alone
/// refuses the question `y4 <= 16` after the removals by bounds, so its hull of `y4` is
/// `16..=17`, which holds the point's 17, as on main before PRES-disj-cost-xr. Item I21 asked
/// the refused question again without the removals, which made the hull exact, at 1.77 times
/// main's instructions on `overlap_rows` projected at k = 16; it was removed
/// (PRES-disj-regressions, comment at `ask` in `project_parts`). The other hulls are exact.
/// With the method of PRES-overlap-fast (module `row_sums`), which answers first here, every
/// hull is exact.
#[test]
fn a_hull_question_refused_after_the_removals_by_bounds_keeps_its_point() {
    let doms = [
        (3, 12, None),
        (0, 17, None),
        (0, 22, None),
        (0, 29, None),
        (0, 16, Some(18)),
        (0, 16, None),
    ];
    let cs = [-1, -1, 1, 2, 1, 1];
    let want = [3, 0, 0, 29, 17, 16].map(|v| Some((v, v)));
    assert_eq!(projected_two_values(&doms, &cs, 88), want);
    presburger::ROW_SUMS_OFF.with(|o| o.set(true));
    let alone = projected_two_values(&doms, &cs, 88);
    presburger::ROW_SUMS_OFF.with(|o| o.set(false));
    let mut want = want;
    want[4] = Some((16, 17));
    assert_eq!(alone, want);
}

/// Random case 98 of the harness has no point, by parity of the row with the box. For
/// `y3`, `y3 <= 29` and `y3 >= 30` are each shown to have no point while `y3 <= 30` is
/// refused, so the hull of `y3` is empty, and so is every other hull (item I21).
#[test]
fn a_hull_whose_two_sides_are_shown_empty_is_empty() {
    let doms = [
        (3, 29, None),
        (0, 30, None),
        (0, 16, None),
        (0, 30, None),
        (0, 10, None),
        (0, 29, None),
        (0, 8, Some(9)),
    ];
    let got = projected_two_values(&doms, &[1, 1, 1, 1, 1, 1, 2], 119);
    assert_eq!(got, vec![None; 7]);
}

/// Rows of sums over atoms each confined to a finite union of ranges (PRES-overlap-fast,
/// QUESTIONS A87): the module `row_sums` joins one table of sums per group of atoms that appear
/// in the same rows, in alternation with the solver.
pub(super) mod row_sums {
    use std::collections::BTreeSet;
    use std::sync::Arc;

    use zed_tests::scaling::Meter;
    use zedc::store::presburger::{Atom, Con, Formula, Lin, ROW_SUMS_OFF, decide, project_each};

    use super::super::repair::answers;

    pub(crate) fn v(i: usize) -> Atom {
        Atom::Sym(Arc::from(format!("y{i}")))
    }

    /// The row `Σ cs[i]·y_i - t`, `== 0` or `>= 0`.
    fn row(cs: &[i64], t: i64, eq: bool) -> Formula {
        let lin = (cs.iter().enumerate())
            .filter(|(_, c)| **c != 0)
            .fold(Lin::constant(-i128::from(t)), |l, (i, c)| {
                l.plus(&Lin::atom(v(i)).times(i128::from(*c)))
            });
        let zero = Lin::constant(0);
        Formula::Con(if eq {
            Con::eq(&lin, &zero)
        } else {
            Con::ge(&lin, &zero)
        })
    }

    /// `y_i` in one of `ranges`, each `(l, h)` written `y_i == l` when `l == h`.
    fn one_of(i: usize, ranges: &[(i64, i64)]) -> Formula {
        let y = Lin::atom(v(i));
        let bound = |l: &Lin| Formula::Con(Con::ge(l, &Lin::constant(0)));
        Formula::or(
            (ranges.iter())
                .map(|&(l, h)| {
                    if l == h {
                        Formula::Con(Con::eq(&y, &Lin::constant(i128::from(l))))
                    } else {
                        Formula::and(vec![
                            bound(&y.minus(&Lin::constant(i128::from(l)))),
                            bound(&Lin::constant(i128::from(h)).minus(&y)),
                        ])
                    }
                })
                .collect(),
        )
    }

    /// Atoms with their ranges, and rows `(coefficients, target, equation)`.
    pub(crate) struct Case {
        pub(crate) ranges: Vec<Vec<(i64, i64)>>,
        pub(crate) rows: Vec<(Vec<i64>, i64, bool)>,
    }

    impl Case {
        pub(crate) fn formula(&self) -> Formula {
            let mut fs: Vec<Formula> = (self.ranges.iter().enumerate())
                .map(|(i, r)| one_of(i, r))
                .collect();
            fs.extend(self.rows.iter().map(|(cs, t, e)| row(cs, *t, *e)));
            Formula::and(fs)
        }

        /// Each atom's set of values over the points, by trying every point.
        fn brute(&self) -> Vec<BTreeSet<i64>> {
            let doms: Vec<Vec<i64>> = (self.ranges.iter())
                .map(|r| r.iter().flat_map(|&(l, h)| l..=h).collect())
                .collect();
            let mut sets = vec![BTreeSet::new(); doms.len()];
            if doms.iter().any(Vec::is_empty) {
                return sets;
            }
            let mut idx = vec![0usize; doms.len()];
            'next: loop {
                let pt: Vec<i64> = (0..doms.len()).map(|i| doms[i][idx[i]]).collect();
                let meets = self.rows.iter().all(|(cs, t, e)| {
                    let s: i64 = cs.iter().zip(&pt).map(|(c, x)| c * x).sum();
                    if *e { s == *t } else { s >= *t }
                });
                if meets {
                    for (s, x) in sets.iter_mut().zip(&pt) {
                        s.insert(*x);
                    }
                }
                for i in 0..doms.len() {
                    idx[i] += 1;
                    if idx[i] < doms[i].len() {
                        continue 'next;
                    }
                    idx[i] = 0;
                }
                return sets;
            }
        }

        /// `decide`, `satisfiable` and each atom's projection are the exact answers.
        fn is_answered_exactly(&self) {
            let (f, sets) = (self.formula(), self.brute());
            answers(&f, !sets[0].is_empty());
            let atoms: Vec<Atom> = (0..sets.len()).map(v).collect();
            let (each, _) = project_each(&f, &atoms).expect("a projection");
            for (i, (got, want)) in each.iter().zip(&sets).enumerate() {
                let got = got.as_ref().expect("an answer");
                let lo = want.first().copied().unwrap_or(0) - 50;
                let hi = want.last().copied().unwrap_or(0) + 50;
                let seen: BTreeSet<i64> = (lo..=hi).filter(|x| got.contains(*x)).collect();
                assert_eq!(&seen, want, "y{i} of {f}");
                assert!(
                    !got.contains(-1_000_000) && !got.contains(1_000_000),
                    "y{i}: {got:?}"
                );
            }
        }
    }

    fn weights(k: usize) -> Vec<i64> {
        (0..k).map(|i| 1000 + 37 * (i * i) as i64 % 991).collect()
    }

    /// Each atom `y_i` in `{0, w_i}`.
    fn two_values(w: &[i64]) -> Vec<Vec<(i64, i64)>> {
        w.iter().map(|&wi| vec![(0, 0), (wi, wi)]).collect()
    }

    /// The coefficients 1 on `y_lo .. y_(hi-1)` of k atoms.
    fn ones(k: usize, lo: usize, hi: usize) -> Vec<i64> {
        (0..k).map(|i| i64::from(lo <= i && i < hi)).collect()
    }

    /// The sum of the even-numbered weights of `y_lo .. y_(hi-1)`.
    fn even(w: &[i64], lo: usize, hi: usize) -> i64 {
        (lo..hi).filter(|i| i % 2 == 0).map(|i| w[i]).sum()
    }

    /// `y_0 + .. + y_(a-1) == t1` and `y_b + .. + y_(k-1) == t2`, a = 2k/3, b = k/3: two sums
    /// that share the atoms `y_b .. y_(a-1)` (the family of QUESTIONS A87).
    pub(crate) fn overlap_rows(k: usize) -> Case {
        let w = weights(k);
        let (a, b) = (2 * k / 3, k / 3);
        Case {
            ranges: two_values(&w),
            rows: vec![
                (ones(k, 0, a), even(&w, 0, a), true),
                (ones(k, b, k), even(&w, b, k), true),
            ],
        }
    }

    /// `overlap_rows` with the second sum's coefficients 1 and 2 in turn: the shared atoms'
    /// two coefficients are not proportional, so the sums over them take two numbers each.
    pub(crate) fn coefficients_one_and_two(k: usize) -> Case {
        coefficients(k, |i| 1 + (i % 2) as i64)
    }

    /// `overlap_rows` with the second sum's coefficient of `y_i` `c(i)`, its constant the sum
    /// at the point where the even-numbered atoms take their weights.
    fn coefficients(k: usize, c: impl Fn(usize) -> i64) -> Case {
        let mut case = overlap_rows(k);
        let w = weights(k);
        let row = &mut case.rows[1];
        row.0 = (0..k).map(|i| if i >= k / 3 { c(i) } else { 0 }).collect();
        row.1 = (k / 3..k).filter(|i| i % 2 == 0).map(|i| c(i) * w[i]).sum();
        case
    }

    /// m rows, row i over `y_(3i) .. y_(3i+5)`, each sharing three atoms with the next.
    pub(crate) fn chain(m: usize) -> Case {
        let k = 3 * m + 3;
        let w = weights(k);
        let rows = (0..m).map(|i| (ones(k, 3 * i, 3 * i + 6), even(&w, 3 * i, 3 * i + 6), true));
        Case {
            ranges: two_values(&w),
            rows: rows.collect(),
        }
    }

    /// The parity example of A87: `a1 + a2 + c + d == 4` and `b1 + b2 + c + d == 3`, the `a`s
    /// and `b`s in {0, 2}, `c` and `d` in {0, 1}. Each value of c and d is possible in each
    /// sum alone; together the sums need `c + d` even and odd.
    #[test]
    fn two_sums_whose_shared_atoms_meet_neither_parity_have_no_point() {
        let (two, one) = (vec![(0, 0), (2, 2)], vec![(0, 1)]);
        let case = Case {
            ranges: vec![two.clone(), two.clone(), two.clone(), two, one.clone(), one],
            rows: vec![
                (vec![1, 1, 0, 0, 1, 1], 4, true),
                (vec![0, 0, 1, 1, 1, 1], 3, true),
            ],
        };
        case.is_answered_exactly();
        for (i, r) in case.rows.iter().enumerate() {
            let alone = Case {
                ranges: case.ranges.clone(),
                rows: vec![r.clone()],
            };
            let sets = alone.brute();
            assert_eq!((sets[4].len(), sets[5].len()), (2, 2), "row {i} alone");
        }
    }

    /// Two equations that share a group: the closing one is met by a lookup (the key join).
    #[test]
    fn two_overlapping_sums_are_answered_exactly() {
        overlap_rows(9).is_answered_exactly();
        overlap_rows(12).is_answered_exactly();
        let mut none = overlap_rows(9);
        none.rows[1].1 += 1;
        none.is_answered_exactly();
    }

    /// Two overlapping sums whose shared atoms have coefficients 1 and 2 in turn in one and 1 in
    /// the other: exact at k = 12 and 16 (the solver alone gives `y0` both 0 and 1000 at k = 16,
    /// where only 1000 is in a point); also with the ratios the other way round, a ratio of -1,
    /// three ratios, and no point. The work at k = 64 and 512 is checked in
    /// `two_overlapping_sums_with_coefficients_one_and_two_of_64_and_512_atoms_scale`.
    #[test]
    fn two_overlapping_sums_with_coefficients_one_and_two_are_answered_exactly() {
        coefficients_one_and_two(12).is_answered_exactly();
        coefficients_one_and_two(16).is_answered_exactly();
        // The two ratios the other way round, a ratio of -1, three ratios, and no point.
        coefficients(12, |i| 2 - (i % 2) as i64).is_answered_exactly();
        coefficients(12, |i| if i % 2 == 0 { 1 } else { -1 }).is_answered_exactly();
        coefficients(12, |i| 1 + (i % 3) as i64).is_answered_exactly();
        let mut none = coefficients_one_and_two(12);
        none.rows[1].1 += 1;
        none.is_answered_exactly();
    }

    /// An inequality that closes beside an equation, checked on each pair of a key's bucket;
    /// and one that closes alone.
    #[test]
    fn an_inequality_sharing_atoms_with_an_equation_is_answered_exactly() {
        let w = weights(8);
        for t2 in [0, even(&w, 3, 8), even(&w, 3, 8) + 1, 7000] {
            Case {
                ranges: two_values(&w),
                rows: vec![
                    (ones(8, 0, 5), even(&w, 0, 5), true),
                    (ones(8, 3, 8), t2, false),
                ],
            }
            .is_answered_exactly();
        }
        Case {
            ranges: two_values(&w),
            rows: vec![(ones(8, 0, 5), 3000, false), (ones(8, 3, 8), 4000, false)],
        }
        .is_answered_exactly();
    }

    /// A row over one group alone, with coefficients -1 and 2, ranges of several values, and an
    /// atom in no row, which takes each of its values.
    #[test]
    fn a_row_of_one_group_with_ranges_and_a_free_atom_is_answered_exactly() {
        Case {
            ranges: vec![
                vec![(0, 0), (3, 5)],
                vec![(1, 2), (7, 7)],
                vec![(0, 0), (4, 6)],
                vec![(3, 3), (7, 9)],
            ],
            rows: vec![(vec![2, -1, 1, 0], 8, true)],
        }
        .is_answered_exactly();
        Case {
            ranges: vec![
                vec![(0, 0), (3, 5)],
                vec![(1, 2), (7, 7)],
                vec![(0, 0), (4, 6)],
                vec![(3, 3)],
            ],
            rows: vec![(vec![2, -1, 1, 0], 100, true)],
        }
        .is_answered_exactly();
    }

    /// An atom whose bound leaves none of its values: no point.
    #[test]
    fn an_atom_with_no_value_leaves_no_point() {
        let f = Formula::and(vec![
            one_of(0, &[(0, 0), (2, 2)]),
            row(&[1], 5, false),
            one_of(1, &[(0, 0), (2, 2)]),
            row(&[1, 1], 2, true),
        ]);
        answers(&f, false);
        let (each, _) = project_each(&f, &[v(0), v(1)]).expect("a projection");
        assert!(
            each.iter().all(|s| s.as_ref().is_ok_and(|s| s.is_empty())),
            "{each:?}"
        );
    }

    /// The 3,000 shared-sum formulas of seed 777 (`decide_sat.rs`): every answer is right, and
    /// no answer is coarser than the solver's alone; the first 100 are compared with it.
    #[test]
    fn random_shared_sums_are_answered_and_never_coarser_than_the_solver_alone() {
        let cases = random_cases(3000);
        let (mut exact, mut finer) = (0, 0);
        for (c, (case, sets)) in cases.iter().enumerate() {
            let f = case.formula();
            let atoms: Vec<Atom> = (0..sets.len()).map(v).collect();
            let ask = || (decide(&f), project_each(&f, &atoms).map(|e| e.0));
            let (d, p) = ask();
            if let Ok(d) = d {
                assert_eq!(d, !sets[0].is_empty(), "case {c}: {f}");
            }
            let p = p.expect("a projection");
            let mut all_exact = true;
            for (i, s) in p.iter().enumerate() {
                let Ok(s) = s else {
                    all_exact = false;
                    continue;
                };
                let got: Vec<i64> = (-200..=200).filter(|x| s.contains(*x)).collect();
                assert!(
                    sets[i].iter().all(|x| got.contains(x)),
                    "case {c}: y{i} lost a value"
                );
                all_exact &= got.len() == sets[i].len() && !s.contains(1000) && !s.contains(-1000);
            }
            exact += usize::from(all_exact);
            if c < 100 {
                ROW_SUMS_OFF.with(|o| o.set(true));
                let (d_old, p_old) = ask();
                ROW_SUMS_OFF.with(|o| o.set(false));
                assert!(d_old.is_err() || d.is_ok(), "case {c}: decide coarser");
                let p_old = p_old.expect("a projection");
                for (i, (new, old)) in p.iter().zip(&p_old).enumerate() {
                    match (new, old) {
                        (Ok(new), Ok(old)) => {
                            let n: Vec<i64> = (-200..=200).filter(|x| new.contains(*x)).collect();
                            let o: Vec<i64> = (-200..=200).filter(|x| old.contains(*x)).collect();
                            assert!(n.iter().all(|x| o.contains(x)), "case {c}: y{i} coarser");
                            finer += usize::from(n.len() < o.len());
                        }
                        (Err(_), Ok(_)) => panic!("case {c}: y{i} refused"),
                        _ => {}
                    }
                }
            }
        }
        eprintln!(
            "random shared sums: {exact} of 3000 exact; {finer} projections finer than the \
             solver's in the first 100"
        );
        assert_eq!(exact, 3000);
    }

    /// Cases `0..n` of the seed-777 generator of `decide_sat.rs`, with each atom's values over
    /// the points.
    fn random_cases(n: u64) -> Vec<(Case, Vec<BTreeSet<i64>>)> {
        struct Rng(u64);
        impl Rng {
            fn next(&mut self, n: u64) -> i64 {
                self.0 =
                    (self.0.wrapping_mul(6364136223846793005)).wrapping_add(1442695040888963407);
                ((self.0 >> 33) % n) as i64
            }
        }
        let mut rng = Rng(777);
        let mut out = Vec::new();
        for _ in 0..n {
            let k = 3 + rng.next(5) as usize;
            let mut ranges = Vec::new();
            let mut doms: Vec<Vec<i64>> = Vec::new();
            for _ in 0..k {
                let a = if rng.next(3) == 0 { rng.next(6) } else { 0 };
                let b = a + 1 + rng.next(30);
                let c = if rng.next(6) == 0 { b + rng.next(3) } else { b };
                ranges.push(vec![(a, a), (b, c)]);
                doms.push(std::iter::once(a).chain(b..=c).collect());
            }
            let mut rows = Vec::new();
            for r in 0..1 + u64::from(rng.next(4) == 0) {
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
                rows.push((cs, t, is_eq));
            }
            let case = Case { ranges, rows };
            let sets = case.brute();
            out.push((case, sets));
        }
        out
    }

    pub(crate) fn work(f: impl FnOnce()) -> u64 {
        Meter::new().work(f).units
    }

    /// One sum over k atoms in `{0, w_i}` whose target, the least unreachable sum from half
    /// the total up, no subset meets.
    pub(crate) fn unreachable(k: usize) -> Case {
        let w = weights(k);
        let mut sums = vec![false; w.iter().sum::<i64>() as usize + 1];
        sums[0] = true;
        for &x in &w {
            for s in (x as usize..sums.len()).rev() {
                sums[s] |= sums[s - x as usize];
            }
        }
        let t = (sums.len() / 2..sums.len())
            .find(|&s| !sums[s])
            .expect("a gap") as i64;
        Case {
            ranges: two_values(&w),
            rows: vec![(vec![1; k], t, true)],
        }
    }

    /// The work of `ask` on `f` with the method and with the solver alone, and the two answers.
    pub(crate) fn both_and_alone<T>(
        f: &Formula,
        ask: impl Fn(&Formula) -> T,
    ) -> ((u64, T), (u64, T)) {
        let mut answer = None;
        let both = work(|| answer = Some(ask(f)));
        let with = answer.take().expect("an answer");
        ROW_SUMS_OFF.with(|o| o.set(true));
        let alone = work(|| answer = Some(ask(f)));
        ROW_SUMS_OFF.with(|o| o.set(false));
        ((both, with), (alone, answer.expect("an answer")))
    }
}
