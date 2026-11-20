//! Many disjunctions over one linked group of rows (plan items DISJ-diff-fast and
//! DISJ-incremental): each disjunct is tested against the base projected onto the atoms of
//! the disjuncts near it, so `n` disjunctions cost about `n log n`, not `n` solves of the
//! whole group.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_38_presburger::{project_alone, solver_alone};
use zedc::store::interval::{End, IntervalSet, Num};
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
        assert_middle_projected(&inputs[&m], m);
    });
}

/// Decides the chain `fam(m, Holds::None)` at each size `m` of a scaling check.
pub(super) fn decides(what: &str, n: usize, fam: fn(usize, Holds) -> Formula) {
    let inputs = scaling::inputs(n, |m| fam(m, Holds::None));
    scaling::check_order(what, n, 1, |m| {
        assert_eq!(decide(&inputs[&m]), Ok(true));
    });
}

/// The check of the benchmarks that project the middle of a chain of `m` stages: a hull that is
/// not empty. These benchmarks measure the solver's search through the disjunctions, so they
/// ask the solver alone ([`solver_alone`]); the exact cover's cost is measured by
/// `bench/exact_cover.rs`, and its answers on these chains by
/// [`the_chains_of_the_benchmarks_are_answered_at_small_sizes`].
pub(super) fn assert_middle_projected(f: &Formula, m: usize) {
    let r = solver_alone(|| project_each(f, &middle(m))).expect("a projection");
    assert!(r.0[0].as_ref().is_ok_and(|s| !s.is_empty()), "{r:?}");
}

/// The check of the benchmark of [`cascade`] of `m` stages: the hull of the middle holds 0 and
/// neither -1 nor 1. The solver alone, as in [`assert_middle_projected`].
pub(super) fn assert_cascade_middle(f: &Formula, m: usize) {
    let r = solver_alone(|| project_each(f, &middle(m))).expect("a projection");
    let s = r.0[0].clone().expect("a hull");
    assert!(s.contains(0) && !s.contains(-1) && !s.contains(1), "{s:?}");
}

/// The check of the benchmark of [`case_chain`] of `m` stages: the hull of `y[m / 2]` holds 0
/// and 1,000,000, not -1. The solver alone, as in [`assert_middle_projected`].
pub(super) fn assert_case_chain_middle(f: &Formula, m: usize) {
    let mid = m / 2;
    let r = solver_alone(|| project_each(f, &[Atom::Sym(format!("y{mid:05}").into())]))
        .expect("a projection");
    let s = r.0[0].clone().expect("a hull");
    assert!(
        s.contains(0) && !s.contains(-1) && s.contains(1_000_000),
        "{s:?}"
    );
}

/// The checks of the benchmarks of `bench/disj_groups.rs` at small sizes, but those of
/// [`row_sums`], which has its own; and the exact cover's answer on each chain, the solver's
/// or refused for its work limit ([`project_alone`]).
#[test]
fn the_chains_of_the_benchmarks_are_answered_at_small_sizes() {
    for m in [2, 3, 8, 24] {
        let mut fs = Vec::new();
        for fam in [difference_chain, general_chain] {
            assert_eq!(decide(&fam(m, Holds::None)), Ok(true), "{m}");
            assert_middle_projected(&fam(m, Holds::None), m);
            fs.push(fam(m, Holds::None));
        }
        assert_middle_projected(&difference_chain(m, Holds::First), m);
        fs.push(difference_chain(m, Holds::First));
        for written in [Written::AsIs, Written::Negated] {
            assert_middle_projected(&joint_chain(m, written), m);
            fs.push(joint_chain(m, written));
        }
        for flipped in [false, true] {
            assert_cascade_middle(&cascade(m, flipped), m);
            fs.push(cascade(m, flipped));
        }
        for f in &fs {
            project_alone(f, &middle(m));
        }
        assert_case_chain_middle(&case_chain(m), m);
    }
}

/// The exact hull of the middle of the difference chain, found by the rows its disjunctions imply
/// where the projection before them stopped wider (`[36, 221]`).
#[test]
fn the_middle_of_a_chain_whose_disjuncts_do_not_hold_has_its_exact_hull() {
    let n = 64;
    let r = project_alone(&difference_chain(n, Holds::None), &middle(n));
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
    let r = project_alone(&general_chain(n, Holds::None), &middle(n));
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
        let r = solver_alone(|| project_each(&f, &middle(n))).expect("a projection");
        assert_eq!(presburger::hull_sides_asked(), 0, "{n} stages");
        // At 512 stages the cover passes its work limit (236M units, 7.1 s, when unlimited).
        project_alone(&f, &middle(n));
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

pub(super) fn joint_chain_scales(written: Written, n: usize) {
    let inputs = scaling::inputs(n, |m| joint_chain(m, written));
    scaling::check_order(
        &format!(
            "a chain whose disjunctions jointly leave one step, written {written:?}, projected"
        ),
        n,
        1,
        |m| {
            assert_middle_projected(&inputs[&m], m);
        },
    );
}

#[test]
fn the_middle_of_a_chain_whose_disjunctions_jointly_leave_one_step_has_its_exact_hull() {
    let n = 64;
    for written in [Written::AsIs, Written::Reversed, Written::Negated] {
        let r = project_alone(&joint_chain(n, written), &middle(n));
        let s = r.0[0].clone().expect("a hull");
        let (lo, hi) = JOINT_MIDDLE_64;
        assert!(s.contains(lo) && !s.contains(lo - 1), "{written:?}: {s:?}");
        assert!(s.contains(hi) && !s.contains(hi + 1), "{written:?}: {s:?}");
        assert!(r.1.is_empty(), "{written:?}: {:?}", r.1);
    }
}

/// The least and greatest value of each `x[i]` over the points of `f` = [`small_chain`] of
/// `case` (not negated), by trying every `x[0]` and every step and `y[i]` the rows of a stage
/// allow (`x` rising by at least `y[i]`, up to `end`), each point read on `f` itself. A branch
/// is cut where a disjunction of the stage it has just fixed has no disjunct holding (sum
/// `step + y[i]` not among `sums`, or step not among `steps`): every point under it breaks a
/// conjunct of `f`. A cut this test got wrong could only lose points the projection keeps,
/// which the comparison reports. One model is kept and each atom's value set as the walk
/// reaches it, so a point costs one reading of `f`. Without the cut and with a model built
/// per point, the 8 cases of the test cost 7.9 s (2026-11-14, load 21).
fn brute_hulls(f: &Formula, case: Small) -> Option<Vec<(i128, i128)>> {
    struct Walk<'a> {
        f: &'a Formula,
        case: Small<'a>,
        xs: Vec<Atom>,
        ys: Vec<Atom>,
        model: zedc::store::presburger::Model,
        at: Vec<i128>,
        hulls: Option<Vec<(i128, i128)>>,
    }
    impl Walk<'_> {
        fn visit(&mut self, value: i128) {
            let (n, every, end, sums, steps) = self.case;
            let i = self.at.len();
            self.at.push(value);
            self.model.insert(self.xs[i].clone(), value.into());
            if i == n - 1 {
                if self.f.holds(&self.model) {
                    let at = &self.at;
                    let h = self
                        .hulls
                        .get_or_insert_with(|| at.iter().map(|&p| (p, p)).collect());
                    for (h, &p) in h.iter_mut().zip(at) {
                        *h = (h.0.min(p), h.1.max(p));
                    }
                }
            } else {
                for yv in 1..=2 {
                    self.model.insert(self.ys[i].clone(), yv.into());
                    for next in value + yv..=end {
                        let step = next - value;
                        let holds = !i.is_multiple_of(every)
                            || (sums.contains(&(step + yv))
                                && (steps.is_empty() || steps.contains(&step)));
                        if holds {
                            self.visit(next);
                        }
                    }
                }
            }
            self.at.pop();
        }
    }
    let n = case.0;
    let mut walk = Walk {
        f,
        case,
        xs: (0..n)
            .map(|k| Atom::Sym(format!("x{k:05}").into()))
            .collect(),
        ys: (0..n - 1)
            .map(|k| Atom::Sym(format!("y{k:05}").into()))
            .collect(),
        model: zedc::store::presburger::Model::new(),
        at: Vec::new(),
        hulls: None,
    };
    for x0 in 0..=case.2 {
        walk.visit(x0);
    }
    walk.hulls
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
        let want = brute_hulls(&f, (n, every, end, sums, steps));
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

/// `z + 2w >= 1 || z + 3y >= 3` with `w <= 1` and `y` in {-1, 2}: at `y = -1` the least `z`
/// is -1 (`w = 1`), at `y = 2` it is -3 (`z + 6 >= 3`), so `z >= -3`. The second disjunct,
/// projected with the base alone, has `y` free and leaves `z` unbounded below; the bound needs
/// `y <= 2`, a row the disjunction on `y` implies. With `-1 <= y <= 2` written as two rows, a
/// wider set, `z >= -3` was found, and with the hole `z` was left unbounded: a narrower input
/// gave a wider output (row PRES-monotone-rules; audit seed 51 step 8 of
/// `l01_39_scope_relations::families`, `x` unbounded below in the narrow run).
#[test]
fn a_bound_through_a_set_with_a_hole_is_projected_as_through_its_hull() {
    let (w, y, z) = (named("w"), named("y"), named("z"));
    let disj = Formula::or(vec![
        ge(z.plus(&w.times(2)).minus(&Lin::constant(1))),
        ge(z.plus(&y.times(3)).minus(&Lin::constant(3))),
    ]);
    let w_le_1 = ge(Lin::constant(1).minus(&w));
    let hole = Formula::and(vec![one_of(&y, &[-1, 2]), w_le_1.clone(), disj.clone()]);
    assert_hull(&hole, Some(-3), None);
    let hull = Formula::and(vec![
        ge(y.plus(&Lin::constant(1))),
        ge(Lin::constant(2).minus(&y)),
        w_le_1,
        disj,
    ]);
    assert_hull(&hull, Some(-3), None);
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
/// (`x <= 0` leaves `y` free), so the solver finds no candidate end and its hull stays open,
/// sound and wider than the exact `z <= 0` (the tradeoff of [`project_each`] at `tighten`, item
/// PRES-pendants-wider). The exact cover (PRES-pugh-work-budget) gives `z <= 0`: every `z <= 0`
/// has the point `x = y = 0`.
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
    let f = Formula::and(fs);
    solver_alone(|| assert_hull(&f, None, None));
    assert_hull(&f, None, Some(0));
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
/// hull is exact. Since FAIL-product-refused-box-renamed, which signs each equation by the
/// structure of the formula and asks a third writing, with each equation's sign the other
/// way, where the first two refuse, the solver alone also gives the exact hull `17..=17`.
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
    use std::cell::Cell;
    use std::collections::BTreeSet;
    use std::sync::Arc;

    use zed_tests::scaling::Meter;
    use zed_tests::step_helpers::l01_38_presburger::solver_alone;
    use zedc::store::presburger::{
        Atom, Con, Formula, JOIN_LIMIT_SET, JOINED, Lin, ROW_SUMS_JOIN, ROW_SUMS_OFF, Refusal,
        decide, project_each, satisfiable,
    };

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
        pub(crate) fn brute(&self) -> Vec<BTreeSet<i64>> {
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
        overlap_rows_by(&weights(k))
    }

    /// [`overlap_rows`] over the weights `w`, one atom each.
    pub(crate) fn overlap_rows_by(w: &[i64]) -> Case {
        let k = w.len();
        let (a, b) = (2 * k / 3, k / 3);
        Case {
            ranges: two_values(w),
            rows: vec![
                (ones(k, 0, a), even(w, 0, a), true),
                (ones(k, b, k), even(w, b, k), true),
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

    /// Two overlapping sums projected by the solver alone (ROW_SUMS_OFF): each atom's hull
    /// search runs over a set of two points, `{0, w_i}`, and asks no question inside the gap
    /// between them (PRES-solver-projection-uncounted); the answers are the exact sets. The
    /// time at k = 16 is in `bench::disj_groups::overlap_rows_by_the_solver_alone`.
    #[test]
    fn two_overlapping_sums_by_the_solver_alone_are_answered_exactly() {
        ROW_SUMS_OFF.with(|o| o.set(true));
        overlap_rows(6).is_answered_exactly();
        overlap_rows(8).is_answered_exactly();
        ROW_SUMS_OFF.with(|o| o.set(false));
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

    /// 300 shared-sum formulas of a new seed each run, the first 30 compared with the solver
    /// alone; the 3,000 of seed 777 are many cases, so they run in `bench::disj_groups`
    /// (author P178).
    #[test]
    fn random_shared_sums_are_answered_and_never_coarser_than_the_solver_alone() {
        let (_, seed) = zed_tests::instances::Rng::fresh("row_sums: random shared sums");
        shared_sums_are_answered(seed, 300, 30);
    }

    /// The cases of seed 10247473762259090707, where the solver alone refused a projection.
    #[test]
    fn shared_sums_of_seed_10247473762259090707_are_answered_and_never_coarser() {
        shared_sums_are_answered(10247473762259090707, 300, 30);
    }

    /// Cases `0..count` of the generator of `decide_sat.rs` at `seed` (777 there): every answer
    /// is right and exact, and no answer is coarser than the solver's alone, with which the
    /// first `compared` are compared.
    pub(crate) fn shared_sums_are_answered(seed: u64, count: usize, compared: usize) {
        let cases = random_cases(seed, count);
        let (mut exact, mut finer, mut alone_refused) = (0, 0, 0);
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
            if c < compared {
                ROW_SUMS_OFF.with(|o| o.set(true));
                let (d_old, p_old) = ask();
                ROW_SUMS_OFF.with(|o| o.set(false));
                assert!(d_old.is_err() || d.is_ok(), "case {c}: decide coarser");
                // The solver alone may refuse the projection as a whole, as it may refuse
                // `decide` or one atom: where two atoms that share a row are told apart by
                // nothing but their names it refuses with `Tie` rather than choose one (author
                // ruling XR3, fix B). Seed 10247473762259090707 meets one: `-y0 + y1 + y4 - y2 +
                // 2 * y3 == 42` and `y0 - y1 - y4 + y2 + 2 * y3 == 42` swap into each other
                // with y0 and y1, y2 and y4. The method's answer, exact as checked above, is
                // then finer than none, and there is nothing to compare.
                let Ok(p_old) = p_old else {
                    alone_refused += 1;
                    continue;
                };
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
            "random shared sums: {exact} of {count} exact; {finer} projections finer than the \
             solver's in the first {compared}, where the solver alone refused \
             {alone_refused} projections"
        );
        assert_eq!(exact, count, "seed {seed}");
    }

    /// Cases `0..n` of the generator of `decide_sat.rs` at `seed`, with each atom's values over
    /// the points.
    fn random_cases(seed: u64, n: usize) -> Vec<(Case, Vec<BTreeSet<i64>>)> {
        struct Rng(u64);
        impl Rng {
            fn next(&mut self, n: u64) -> i64 {
                self.0 =
                    (self.0.wrapping_mul(6364136223846793005)).wrapping_add(1442695040888963407);
                ((self.0 >> 33) % n) as i64
            }
        }
        let mut rng = Rng(seed);
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

    /// The check of the benchmarks that project sums: each of `syms` has a hull that is not
    /// empty.
    pub(crate) fn assert_every_hull_non_empty(f: &Formula, syms: &[Atom]) {
        let p = project_each(f, syms).expect("a projection");
        assert!(
            p.0.iter().all(|s| s.as_ref().is_ok_and(|s| !s.is_empty())),
            "{p:?}"
        );
    }

    /// The first, middle and last of `k` atoms.
    pub(crate) fn ends_and_middle(k: usize) -> [Atom; 3] {
        [v(0), v(k / 2), v(k - 1)]
    }

    /// The answer of `decide`, `None` when refused.
    pub(crate) fn decided(f: &Formula) -> Option<bool> {
        decide(f).ok()
    }

    /// Whether the projection of `y0` is empty, `None` when it alone is refused.
    pub(crate) fn projected(f: &Formula) -> Result<Option<bool>, Refusal> {
        project_each(f, &[v(0)]).map(|e| e.0[0].as_ref().map(|s| s.is_empty()).ok())
    }

    /// The race's cases where the solver answers and where the method does not: a sum of 8
    /// atoms, each in 0..=1e5 or 2e5..=3e5, at most 200,003; and the same with ranges of 1e9.
    pub(crate) fn solver_cases() -> [(&'static str, Formula); 2] {
        [
            (
                "the solver first",
                Case {
                    ranges: vec![vec![(0, 100_000), (200_000, 300_000)]; 8],
                    rows: vec![(vec![1; 8], 200_003, true)],
                }
                .formula(),
            ),
            (
                "a bound past u64",
                Case {
                    ranges: vec![vec![(0, 1_000_000_000), (2_000_000_000, 3_000_000_000)]; 8],
                    rows: vec![(vec![1; 8], 1_000_000_007, true)],
                }
                .formula(),
            ),
        ]
    }

    /// The units the join spends on `ask` with no limit, which it must answer within, and
    /// its answer.
    fn units_of<T>(ask: impl Fn() -> T) -> (u64, T) {
        ROW_SUMS_JOIN.with(|o| o.set(true));
        let answer = ask();
        ROW_SUMS_JOIN.with(|o| o.set(false));
        let (units, answered) = JOINED.with(Cell::get).expect("a plan");
        assert!(answered);
        (units, answer)
    }

    /// `ask` with the join's limit set to `limit`, and whether the join answered.
    fn at_limit<T>(limit: u64, ask: impl Fn() -> T) -> (T, bool) {
        JOIN_LIMIT_SET.with(|l| l.set(Some(limit)));
        let answer = ask();
        JOIN_LIMIT_SET.with(|l| l.set(None));
        (answer, JOINED.with(Cell::get).expect("a plan").1)
    }

    /// Whether the solver answered, below the limit, `decide` and `satisfiable`.
    type SolverAnswered = (bool, bool);

    /// `f` asked on both sides of the switch (`row_sums::JOIN_LIMIT`, PRES-switchover-not-race):
    /// with the limit at the units the join takes, the join answers, as it does with no
    /// limit; one unit below, it stops, `decide` and `satisfiable` give the solver's answer,
    /// equal to the join's wherever the solver does not refuse (a model holding `f`), and
    /// `project_each` gives the solver's answer made exact by the cover, the join's sets
    /// (PRES-project-exact-solver); with the cover off ([`solver_alone`]) it refuses with
    /// `Refusal::Work`, since the solver's projection alone is coarser.
    fn both_sides_of_the_limit(name: &str, f: &Formula, atoms: &[Atom]) -> SolverAnswered {
        let (u, d) = units_of(|| decide(f));
        assert_eq!(
            at_limit(u, || decide(f)),
            (d.clone(), true),
            "{name}: decide at {u}"
        );
        let (below, joined) = at_limit(u - 1, || decide(f));
        assert!(!joined, "{name}: decide below {u}");
        if below.is_ok() {
            assert_eq!(below, d, "{name}: decide below {u}");
        }
        let (u, p) = units_of(|| satisfiable(f));
        let p = p.expect("the join answers");
        assert!(p.as_ref().is_none_or(|m| f.holds(m)), "{name}");
        assert_eq!(
            at_limit(u, || satisfiable(f)),
            (Ok(p.clone()), true),
            "{name}: point at {u}"
        );
        let (point_below, joined) = at_limit(u - 1, || satisfiable(f));
        assert!(!joined, "{name}: point below {u}");
        if let Ok(m) = &point_below {
            assert_eq!(m.is_some(), p.is_some(), "{name}: point below {u}");
            assert!(m.as_ref().is_none_or(|m| f.holds(m)), "{name}");
        }
        let ask = || project_each(f, atoms).map(|e| e.0);
        let (u, each) = units_of(ask);
        assert!(each.is_ok(), "{name}");
        // With no control set, a formula over two atoms besides defined ones is projected by
        // polygons (`row_sums::plane`) and not by the join: the sets are the join's.
        assert_eq!(ask(), each, "{name}: project by default");
        assert_eq!(
            at_limit(u, ask),
            (each.clone(), true),
            "{name}: project at {u}"
        );
        // Below the limit the cover answers each symbol with the join's set, or refuses it:
        // past its own work limit (`Refusal::Questions`, A99's 250 ms) or where the solver
        // refuses the formula (`Refusal::Disjuncts`, as `decide` above may); never with
        // another set. The solver's projection the cover starts from is counted against the
        // same limit there, and refuses the whole call with `Refusal::Questions` past it
        // (PRES-solver-projection-uncounted: uncounted, `overlap_rows(16)` took over 60 s).
        let (by_cover, joined) = at_limit(u - 1, ask);
        assert!(!joined, "{name}: project below {u}");
        let want = each.clone().expect(name);
        match by_cover {
            Err(r) => assert_eq!(r, Refusal::Questions, "{name}: project below {u}"),
            Ok(by_cover) => {
                assert_eq!(by_cover.len(), want.len(), "{name}");
                for (got, want) in by_cover.iter().zip(&want) {
                    assert!(
                        got == want || got.is_err(),
                        "{name}: project below {u}, by the cover: {got:?}, the join's {want:?}"
                    );
                }
                eprintln!(
                    "{name}: project below {u}: {} of {} symbols answered",
                    by_cover.iter().filter(|s| s.is_ok()).count(),
                    by_cover.len()
                );
            }
        }
        // With the cover off the solver reads `f` as written, not `cover_input`'s writing, so
        // its rows reach the join in another order and its units are its own: under the names
        // `project_each` gives by structure, `overlap_rows(16)` takes 1,501 units with the cover
        // and 1,454 without, and answered at 1,500 (PRES-project-each-naming).
        let (u, _) = solver_alone(|| units_of(ask));
        assert_eq!(
            solver_alone(|| at_limit(u - 1, ask)),
            (Err(Refusal::Work), false),
            "{name}: project below {u}, with the cover off"
        );
        (below.is_ok(), point_below.is_ok())
    }

    /// The families of the benchmarks at small sizes and an unreachable sum, on both sides of
    /// the switch.
    #[test]
    fn each_family_is_answered_alike_on_both_sides_of_the_join_limit() {
        let cases = [
            ("overlap_rows k=16", overlap_rows(16), 16),
            ("coefficients 1, 2 k=12", coefficients_one_and_two(12), 12),
            ("chain m=4", chain(4), 15),
            ("unreachable k=10", unreachable(10), 10),
        ];
        let mut answered = Vec::new();
        for (name, case, k) in cases {
            let atoms: Vec<Atom> = (0..k).map(v).collect();
            let t = std::time::Instant::now();
            answered.push(both_sides_of_the_limit(name, &case.formula(), &atoms));
            eprintln!("{name}: both sides in {:?}", t.elapsed());
        }
        // The solver refuses the unreachable sum (`Disjuncts`), so below the limit the answer
        // is a refusal: the switch to the solver is taken, and the join is the side that
        // answers.
        assert_eq!(answered[3], (false, false));
    }

    /// 200 formulas of the generator of `decide_sat.rs` at a fresh seed, through
    /// [`random_cases_alike_on_both_sides`]. Most have a plan, but no count of them is reached
    /// at every seed, so none is asserted here; the 20 cases of seed 777 below have an exact
    /// count, and the built families of
    /// `each_family_is_answered_alike_on_both_sides_of_the_join_limit` each have a plan.
    #[test]
    fn random_shared_sums_are_answered_alike_on_both_sides_of_the_join_limit() {
        let (_, seed) = zed_tests::instances::Rng::fresh("row_sums: both sides of the limit");
        random_cases_alike_on_both_sides(seed, 200);
    }

    /// The first 20 cases of seed 777 of the generator of `decide_sat.rs`, through
    /// [`random_cases_alike_on_both_sides`]: the count with a plan is exact, so a plan lost
    /// shows here at every run.
    #[test]
    fn the_first_20_shared_sums_of_seed_777_are_answered_alike_on_both_sides_of_the_join_limit() {
        assert_eq!(random_cases_alike_on_both_sides(777, 20), 17);
    }

    /// Cases `0..n` of the generator of `decide_sat.rs` at `seed`, each that the join plans
    /// checked on both sides of the switch, with the projection at the limit checked against
    /// brute force; prints how often the solver answered below the limit. The count with a plan.
    fn random_cases_alike_on_both_sides(seed: u64, n: usize) -> usize {
        let (mut decided, mut pointed, mut count) = (0, 0, 0);
        for (c, (case, sets)) in random_cases(seed, n).into_iter().enumerate() {
            let f = case.formula();
            let atoms: Vec<Atom> = (0..sets.len()).map(v).collect();
            if !has_plan(&f) {
                continue;
            }
            count += 1;
            let (d, p) = both_sides_of_the_limit(&format!("seed {seed} case {c}: {f}"), &f, &atoms);
            decided += usize::from(d);
            pointed += usize::from(p);
            case.is_answered_exactly();
        }
        eprintln!(
            "both sides of the limit, seed {seed}: {count} of {n} with a plan; below the limit \
             the solver decided {decided} and found a point or none for {pointed}"
        );
        count
    }

    /// Whether the join plans `f`: a formula of the class, not settled by its bounds alone,
    /// whose keys stay below 2^62.
    fn has_plan(f: &Formula) -> bool {
        JOINED.with(|j| j.set(None));
        ROW_SUMS_JOIN.with(|o| o.set(true));
        let _ = decide(f);
        ROW_SUMS_JOIN.with(|o| o.set(false));
        JOINED.with(Cell::get).is_some()
    }

    /// The checks of the benchmarks of sums in `bench/disj_groups.rs` at small sizes, but their
    /// ratios of work: each family decided true and its hulls not empty, an unreachable sum
    /// answered by the method and refused by the solver alone, and the solver's cases answered
    /// alike both ways.
    #[test]
    fn the_sums_of_the_benchmarks_are_answered_at_small_sizes() {
        for k in [9, 12, 16] {
            for f in [
                overlap_rows(k).formula(),
                coefficients_one_and_two(k).formula(),
            ] {
                assert_eq!(decide(&f), Ok(true), "{k}");
                assert_every_hull_non_empty(&f, &ends_and_middle(k));
            }
        }
        for m in [1, 2, 8] {
            let f = chain(m).formula();
            assert_eq!(decide(&f), Ok(true), "{m}");
            assert_every_hull_non_empty(&f, &[v(3 * m / 2)]);
        }
        let (_, with) = both_and_alone(&unreachable(4).formula(), decided).0;
        assert_eq!(with, Some(false));
        for k in [10, 16] {
            let ((_, with), (_, without)) = both_and_alone(&unreachable(k).formula(), decided);
            assert_eq!((with, without), (Some(false), None), "{k}");
        }
        for (what, f) in solver_cases() {
            let ((_, with), (_, without)) = both_and_alone(&f, projected);
            assert_eq!(with, without, "{what}");
        }
    }

    /// The classes answered exactly where the join does not (`row_sums::classes`,
    /// PRES-overlap-sums-exact-subclasses): forced atoms, scaled atoms, and the join once more
    /// on the rows they reduce. Each answer is checked against every point; each class has a
    /// case it must not take.
    pub(crate) mod classes {
        use std::collections::BTreeSet;

        use zedc::store::interval::{End, Num};
        use zedc::store::presburger::{
            Atom, Con, Formula, JOIN_LIMIT_SET, Lin, REDUCED, Reduced, ReducedBy, project_each,
        };

        use super::v;

        /// Atoms with their values (each a list of ranges) and rows `(coefficients, target,
        /// equation)`, in `i128`, so that values past `2^62` can be written.
        pub(crate) struct Big {
            pub(crate) ranges: Vec<Vec<(i128, i128)>>,
            pub(crate) rows: Vec<(Vec<i128>, i128, bool)>,
        }

        impl Big {
            pub(crate) fn formula(&self) -> Formula {
                let mut fs = Vec::new();
                for (i, ranges) in self.ranges.iter().enumerate() {
                    let y = Lin::atom(v(i));
                    let ge = |l: Lin| Formula::Con(Con::ge(&l, &Lin::constant(0)));
                    fs.push(Formula::or(
                        (ranges.iter())
                            .map(|&(l, h)| {
                                if l == h {
                                    Formula::Con(Con::eq(&y, &Lin::constant(l)))
                                } else {
                                    Formula::and(vec![
                                        ge(y.minus(&Lin::constant(l))),
                                        ge(Lin::constant(h).minus(&y)),
                                    ])
                                }
                            })
                            .collect(),
                    ));
                }
                for (cs, t, eq) in &self.rows {
                    let lin = (cs.iter().enumerate())
                        .filter(|(_, c)| **c != 0)
                        .fold(Lin::constant(-t), |l, (i, c)| {
                            l.plus(&Lin::atom(v(i)).times(*c))
                        });
                    let zero = Lin::constant(0);
                    fs.push(Formula::Con(if *eq {
                        Con::eq(&lin, &zero)
                    } else {
                        Con::ge(&lin, &zero)
                    }));
                }
                Formula::and(fs)
            }

            /// Each atom's values over the points, by trying every point.
            pub(crate) fn brute(&self) -> Vec<BTreeSet<i128>> {
                let doms: Vec<Vec<i128>> = (self.ranges.iter())
                    .map(|r| r.iter().flat_map(|&(l, h)| l..=h).collect())
                    .collect();
                let mut sets = vec![BTreeSet::new(); doms.len()];
                let mut idx = vec![0usize; doms.len()];
                'next: loop {
                    let pt: Vec<i128> = (0..doms.len()).map(|i| doms[i][idx[i]]).collect();
                    let meets = self.rows.iter().all(|(cs, t, e)| {
                        let s: i128 = cs.iter().zip(&pt).map(|(c, x)| c * x).sum();
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

            /// Each atom's projection, with the join's limit at `limit` (`None`, the default),
            /// and the reductions that answered it; each set answered is checked against
            /// `want`, the values over the points, on the values of the atom's ranges (an
            /// answer holds no value outside them, the join's sets being subsets of the
            /// ranges and the solver's exact). The count of atoms answered.
            pub(crate) fn projected(
                &self,
                limit: Option<u64>,
                want: &[BTreeSet<i128>],
            ) -> (usize, Option<Reduced>) {
                let f = self.formula();
                let atoms: Vec<Atom> = (0..self.ranges.len()).map(v).collect();
                REDUCED.with(|r| r.set(None));
                JOIN_LIMIT_SET.with(|l| l.set(limit));
                let got = project_each(&f, &atoms);
                JOIN_LIMIT_SET.with(|l| l.set(None));
                let reduced = REDUCED.with(|r| r.take());
                let each = match got {
                    Ok((each, _)) => each,
                    Err(r) => {
                        assert!(reduced.is_none(), "{f}: refused {r:?} after {reduced:?}");
                        return (0, reduced);
                    }
                };
                let mut answered = 0;
                for (i, (s, want)) in each.iter().zip(want).enumerate() {
                    let Ok(s) = s else {
                        assert!(reduced.is_none(), "y{i} of {f}: refused after {reduced:?}");
                        continue;
                    };
                    answered += 1;
                    let seen: BTreeSet<i128> = (self.ranges[i].iter())
                        .flat_map(|&(l, h)| l..=h)
                        .filter(|&x| s.contains_end(&end(x)))
                        .collect();
                    assert_eq!(&seen, want, "y{i} of {f}, {reduced:?}: {s:?}");
                    let (lo, hi) = (
                        self.ranges[i][0].0,
                        self.ranges[i].last().expect("a range").1,
                    );
                    assert!(
                        !s.contains_end(&end(lo - 1)) && !s.contains_end(&end(hi + 1)),
                        "y{i} of {f}: {s:?}"
                    );
                }
                (answered, reduced)
            }
        }

        fn end(x: i128) -> End {
            End::Fin(Num::from(x))
        }

        /// k atoms each in `0..=m` or `2m..=3m`, with coefficients the powers of `10m`, summing
        /// to `t`: each coefficient is greater than the width of the terms below it, so the
        /// row is superincreasing and solved from its heaviest term down (the `sparse` family
        /// of the switchover benchmark, whose join stops at its limit from k = 3, m = 300).
        pub(crate) fn sparse(k: usize, m: i128, t: i128) -> Big {
            let g = 10 * m;
            Big {
                ranges: vec![vec![(0, m), (2 * m, 3 * m)]; k],
                rows: vec![((0..k).map(|i| g.pow(i as u32)).collect(), t, true)],
            }
        }

        /// The limit no join meets: every join stops at its first step.
        const STOPPED: Option<u64> = Some(0);

        /// The sparse family past the join's limit, at targets met by one point, by none
        /// (a value in the gap between an atom's ranges), and by none past the greatest sum:
        /// each answered exactly by forced atoms alone.
        #[test]
        fn sparse_sums_past_the_limit_are_answered_by_forced_atoms() {
            for (k, m) in [(2usize, 4i128), (3, 3), (4, 2)] {
                let g = 10 * m;
                for t in [3 + g * m, 3 + g * (m + 1), m + 1 + g * m] {
                    let case = sparse(k, m, t);
                    let want = case.brute();
                    let (answered, reduced) = case.projected(STOPPED, &want);
                    assert_eq!(answered, k, "k = {k}, m = {m}, t = {t}");
                    let by = reduced.expect("answered by the classes").by;
                    let none = want[0].is_empty();
                    assert_eq!(
                        by,
                        if none {
                            ReducedBy::NoPoint
                        } else {
                            ReducedBy::Forced
                        },
                        "k = {k}, m = {m}, t = {t}"
                    );
                }
            }
        }

        /// The negative control of forcing: in `y0 + 4·y1 == 4`, `y0` in `0..=4` and `y1` in
        /// `0..=2`, the coefficient of `y1` equals the width of `y0`'s term, so neither is
        /// forced (the points are (4, 0) and (0, 1)); no class answers, and the projection is
        /// the solver's with the cover, or refused.
        #[test]
        fn a_coefficient_equal_to_the_width_below_it_forces_nothing() {
            let case = Big {
                ranges: vec![vec![(0, 4)], vec![(0, 2)]],
                rows: vec![(vec![1, 4], 4, true)],
            };
            let want = case.brute();
            assert_eq!(want[1], BTreeSet::from([0, 1]));
            let (_, reduced) = case.projected(STOPPED, &want);
            assert_eq!(reduced, None);
        }

        /// `overlap_rows(k)` with every value times `step`: at `10^15` and k >= 9, a row's sums
        /// span more than `2^62`, so the join has no plan (at k = 6 they do not, and it plans); each atom is scaled by its one value besides 0, each row is divided by
        /// `10^15`, and the join answers the rows of `overlap_rows(k)`.
        pub(crate) fn overlap_scaled(k: usize, step: i128) -> Big {
            overlap_scaled_by(&super::overlap_rows(k), step)
        }

        /// [`overlap_scaled`] of the case `case` in place of `overlap_rows(k)`.
        pub(crate) fn overlap_scaled_by(case: &super::Case, step: i128) -> Big {
            Big {
                ranges: (case.ranges.iter())
                    .map(|r| {
                        (r.iter())
                            .map(|&(l, h)| (i128::from(l) * step, i128::from(h) * step))
                            .collect()
                    })
                    .collect(),
                rows: (case.rows.iter())
                    .map(|(cs, t, e)| {
                        (
                            cs.iter().map(|&c| i128::from(c)).collect(),
                            i128::from(*t) * step,
                            *e,
                        )
                    })
                    .collect(),
            }
        }

        const STEP: i128 = 1_000_000_000_000_000;

        /// The scaled family with no plan, answered exactly; and its negative control, the same
        /// with the value of `y_(k/3)`, an atom of both rows, 1 more, so the gcd of each row's
        /// coefficients is 1 and the keys still pass `2^62`: no class answers. The control had
        /// the 1 on `y_(k-1)`, which only the second row reads: the first row kept its factor
        /// `10^15`, and dividing it out shrank its keys, so whether the join then had a plan
        /// depended on the order of the rows. At k = 9 it had none under the written names and
        /// one under the names `project_each` gives by structure (PRES-project-each-naming),
        /// where the classes answered all 9 atoms exactly (`Joined(202)`, each set the one over
        /// the points); with the 1 on `y_0` it was the other way round. With the 1 on an atom
        /// of both rows, neither naming answers (2026-11-20, k = 9 and 12).
        #[test]
        fn sums_of_values_with_a_common_factor_past_2_62_are_answered_by_scaling() {
            for k in [9, 12, 15] {
                let case = overlap_scaled(k, STEP);
                let want = case.brute();
                let (answered, reduced) = case.projected(None, &want);
                let reduced = reduced.expect("answered by the classes");
                assert_eq!(answered, k, "k = {k}");
                assert_eq!(reduced.scaled, k, "k = {k}");
                assert!(matches!(reduced.by, ReducedBy::Joined(_)), "k = {k}");
            }
            // The control goes to the solver, whose work on these values grows quickly with k
            // (2026-11-19: 0.1 s at k = 9; 22 s for k = 9, 12 and 15 together; 2026-11-20, the 1
            // on `y_(k/3)`: 0.2 s at k = 9), so it is asked at k = 9 alone.
            let k = 9;
            let mut control = overlap_scaled(k, STEP);
            control.ranges[k / 3][1].0 += 1;
            control.ranges[k / 3][1].1 += 1;
            let want = control.brute();
            let t = std::time::Instant::now();
            let (answered, reduced) = control.projected(None, &want);
            eprintln!(
                "control, k = {k}: {answered} of {k} answered by the solver in {:?}",
                t.elapsed()
            );
            assert_eq!(reduced, None, "control, k = {k}");
        }

        /// Four atoms in `{1, 3, 7, 11}`, summing to 15, with `y0 >= y1`: every value is odd, so
        /// no point, shown by the gcd of the scaled row (each `y = 1 + 2·z`, so the row is
        /// `2·(z0 + z1 + z2 + z3) == 11`) not dividing its constant. (One equation alone is
        /// settled before the join by its residue, `row_domains`, hence the second row.) Its
        /// control, the sum 16, has points, answered past the limit by the solver with the
        /// cover and not by the classes, since the scaled rows' join stops at the same limit.
        #[test]
        fn an_odd_sum_of_four_odd_values_past_the_limit_has_no_point_by_the_gcd() {
            let ranges = vec![vec![(1, 1), (3, 3), (7, 7), (11, 11)]; 4];
            let odd = Big {
                ranges: ranges.clone(),
                rows: vec![(vec![1, 1, 1, 1], 15, true), (vec![1, -1, 0, 0], 0, false)],
            };
            let want = odd.brute();
            assert!(want.iter().all(BTreeSet::is_empty));
            let (answered, reduced) = odd.projected(STOPPED, &want);
            assert_eq!(answered, 4);
            assert_eq!(reduced.map(|r| r.by), Some(ReducedBy::NoPoint));
            let even = Big {
                ranges,
                rows: vec![(vec![1, 1, 1, 1], 16, true), (vec![1, -1, 0, 0], 0, false)],
            };
            let want = even.brute();
            assert!(!want[0].is_empty());
            let (_, reduced) = even.projected(STOPPED, &want);
            assert_eq!(reduced, None);
        }

        /// Random rows with the shapes the classes take (coefficients growing by a random
        /// factor, values of a common step) and shapes they do not, past the join's limit and
        /// with no limit: every answer is the set over the points. The count of formulas the
        /// classes answered.
        pub(crate) fn random_agree(seed: u64, n: usize) -> usize {
            let mut rng = zed_tests::instances::Rng::new(seed);
            let mut by_classes = 0;
            for c in 0..n {
                let k = 2 + rng.below(3);
                let step = [1, 1, 2, 3][rng.below(4)] as i128;
                let mut ranges = Vec::new();
                for _ in 0..k {
                    let l = rng.int(-2, 2) as i128;
                    let mut r: Vec<(i128, i128)> = vec![(l * step, l * step)];
                    let mut at = l;
                    for _ in 0..1 + rng.below(3) {
                        at += 1 + rng.below(3) as i128;
                        let wide = if step == 1 { rng.below(3) as i128 } else { 0 };
                        r.push((at * step, (at + wide) * step));
                        at += wide;
                    }
                    ranges.push(r);
                }
                let mut rows = Vec::new();
                for r in 0..1 + rng.below(2) {
                    let mut c = 1i128;
                    let cs: Vec<i128> = (0..k)
                        .map(|_| {
                            let x = c * [1, -1][rng.below(2)];
                            c *= 1 + rng.below(30) as i128;
                            x
                        })
                        .collect();
                    let t = (0..k)
                        .map(|i| {
                            let r = &ranges[i][rng.below(ranges[i].len())];
                            cs[i] * r.0
                        })
                        .sum::<i128>()
                        + rng.int(-1, 1) as i128;
                    rows.push((cs, t, r == 0 || rng.below(2) == 0));
                }
                let case = Big { ranges, rows };
                let want = case.brute();
                let (_, reduced) = case.projected(STOPPED, &want);
                by_classes += usize::from(reduced.is_some());
                let (answered, _) = case.projected(None, &want);
                assert_eq!(answered, k, "seed {seed} case {c}: {}", case.formula());
            }
            by_classes
        }

        /// 300 random formulas of a fresh seed through [`random_agree`].
        #[test]
        fn random_rows_past_the_limit_are_answered_exactly_or_refused() {
            let (_, seed) = zed_tests::instances::Rng::fresh("row_sums::classes");
            let count = random_agree(seed, 300);
            eprintln!("row_sums::classes, seed {seed}: {count} of 300 answered by the classes");
        }

        /// 300 random formulas of seed 777: the count the classes answer is exact, so a class
        /// lost shows at every run.
        #[test]
        fn the_300_random_rows_of_seed_777_past_the_limit_are_answered_exactly() {
            let count = random_agree(777, 300);
            eprintln!("row_sums::classes, seed 777: {count} of 300 answered by the classes");
            assert_eq!(count, 181);
        }
    }
}

/// The two rows over `x` and `y` of the questions [`two_wide_atoms`] asks, `a·x + b·y + k >= 0`:
/// the two kinds the `chain` family of l01_39 asks, `y - x - j >= 0` and `x + c·y - 1 >= 0`.
pub const TWO_WIDE_ROWS: [(i128, i128, i128); 2] = [(-1, 1, 2), (1, 7, -1)];

/// The question `Scope::project_by_pendants` asks for each test of the `chain` family of
/// l01_39 `families` (FAIL-scope-chain-scales-bytes): `-m <= x <= m`, `y` in `[-m, -m/8]` or
/// `[m/8, m]`, `a·x + b·y + k >= 0`, and `w == x + y` with `-2m <= w <= 2m`, projected onto
/// `w`, `x` and `y`. The atoms `x` and `y` share both rows with coefficients not proportional,
/// so the join of row sums keys their group by two digits and builds a table of every pair:
/// work of order m^2 for one question, where the solver's bounds do not grow with m.
pub fn two_wide_atoms(m: i128, (a, b, k): (i128, i128, i128)) -> (Formula, Vec<Atom>) {
    let (w, x, y) = (named("w"), named("x"), named("y"));
    let c = Lin::constant;
    let fin = |v: i128| End::Fin(Num::from(v));
    let ys = IntervalSet::from_pieces(vec![(fin(-m), fin(-m / 8)), (fin(m / 8), fin(m))]);
    let f = Formula::and(vec![
        ge(x.plus(&c(m))),
        ge(c(m).minus(&x)),
        presburger::member(&Atom::Sym("y".into()), &ys),
        ge(x.times(a).plus(&y.times(b)).plus(&c(k))),
        eq(w.minus(&x).minus(&y)),
        ge(w.plus(&c(2 * m))),
        ge(c(2 * m).minus(&w)),
    ]);
    let names = ["w", "x", "y"].map(|n| Atom::Sym(n.into())).to_vec();
    (f, names)
}

/// The values of `w`, `x` and `y` over the points of [`two_wide_atoms`], by trying every pair.
fn two_wide_atoms_by_points(m: i128, (a, b, k): (i128, i128, i128)) -> [Vec<i128>; 3] {
    let mut each: [std::collections::BTreeSet<i128>; 3] = Default::default();
    for x in -m..=m {
        for y in (-m..=-m / 8).chain(m / 8..=m) {
            if a * x + b * y + k >= 0 {
                for (s, v) in each.iter_mut().zip([x + y, x, y]) {
                    s.insert(v);
                }
            }
        }
    }
    each.map(|s| s.into_iter().collect())
}

/// [`two_wide_atoms`] at small sizes: each projection holds exactly the values of the points.
#[test]
fn two_wide_atoms_are_projected_exactly_at_small_sizes() {
    for row in TWO_WIDE_ROWS {
        for m in [8, 16, 40, 200] {
            let (f, names) = two_wide_atoms(m, row);
            let (each, skipped) = project_each(&f, &names).expect("a projection");
            assert!(skipped.is_empty(), "m = {m}: {skipped:?}");
            let points = two_wide_atoms_by_points(m, row);
            for ((name, got), want) in names.iter().zip(each).zip(points) {
                let got = got.expect("a set");
                let lo = want[0] - 2;
                let hi = want[want.len() - 1] + 2;
                for v in lo..=hi {
                    assert_eq!(
                        got.contains(v as i64),
                        want.binary_search(&v).is_ok(),
                        "{row:?}, m = {m}, {name:?} at {v}: {got:?}"
                    );
                }
            }
        }
    }
}
