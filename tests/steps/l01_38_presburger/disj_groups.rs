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
fn middle(n: usize) -> [Atom; 1] {
    [Atom::Sym(format!("x{:05}", n / 2).into())]
}

/// Projects the middle of the chain `fam(m, holds)` at each size `m` of a scaling check.
fn projects(what: &str, n: usize, fam: fn(usize, Holds) -> Formula, holds: Holds) {
    let inputs = scaling::inputs(n, |m| fam(m, holds));
    scaling::check_order(what, n, 1, |m| {
        let r = project_each(&inputs[&m], &middle(m)).expect("a projection");
        assert!(r.0[0].as_ref().is_ok_and(|s| !s.is_empty()));
    });
}

/// Decides the chain `fam(m, Holds::None)` at each size `m` of a scaling check.
fn decides(what: &str, n: usize, fam: fn(usize, Holds) -> Formula) {
    let inputs = scaling::inputs(n, |m| fam(m, Holds::None));
    scaling::check_order(what, n, 1, |m| {
        assert_eq!(decide(&inputs[&m]), Ok(true));
    });
}

#[test]
fn the_middle_of_a_difference_chain_whose_disjuncts_hold_is_projected_in_n_log_n() {
    projects(
        "a difference chain projected, a disjunct holding",
        64,
        difference_chain,
        Holds::First,
    );
}

#[test]
fn a_difference_chain_whose_disjuncts_do_not_hold_is_decided_in_n_log_n() {
    decides(
        "a difference chain decided, no disjunct holding",
        64,
        difference_chain,
    );
}

#[test]
fn the_middle_of_a_difference_chain_whose_disjuncts_do_not_hold_is_projected_in_n_log_n() {
    projects(
        "a difference chain projected, no disjunct holding",
        64,
        difference_chain,
        Holds::None,
    );
}

/// At 256 stages, not fewer: the limit for work of order n log n is 12.1 times from 256 to
/// 2048, and work of order n^1.2 gives 8^1.2 = 12.13 times there, but at 32 stages the limit is
/// 14.1 and n log n itself gives 12.8 times, so n^1.2 passed unseen (plan item
/// THREE-atom-exponent; COMPLEXITY.md row THREE-atom-exponent).
#[test]
fn the_middle_of_a_chain_of_three_atom_rows_whose_disjuncts_hold_is_projected_in_n_log_n() {
    projects(
        "a chain of three-atom rows projected, a disjunct holding",
        256,
        general_chain,
        Holds::First,
    );
}

/// At 512 stages, where the limit, 11.7 times, is below the 12.13 times of work of order n^1.2;
/// at 64 it was 13.2 (plan item THREE-atom-exponent).
#[test]
fn a_chain_of_three_atom_rows_whose_disjuncts_do_not_hold_is_decided_in_n_log_n() {
    decides(
        "a chain of three-atom rows decided, no disjunct holding",
        512,
        general_chain,
    );
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

/// At 256 stages, for the reason given at the test of the chain whose disjuncts hold.
#[test]
fn the_middle_of_a_chain_of_three_atom_rows_whose_disjuncts_do_not_hold_is_projected_in_n_log_n() {
    projects(
        "a chain of three-atom rows projected, no disjunct holding",
        256,
        general_chain,
        Holds::None,
    );
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
enum Written {
    AsIs,
    Reversed,
    Negated,
}

/// The exact hull of the middle of [`joint_chain`]: every step at least 1, and 7 at the 8
/// stages of disjunctions before the middle; the 31 steps after it, 8 of them at
/// disjunctions, end at most at `8n`.
const JOINT_MIDDLE_64: (i64, i64) = (32 + 6 * 8, 8 * 64 - (31 + 6 * 8));

#[test]
fn the_middle_of_a_chain_whose_disjunctions_jointly_leave_one_step_is_projected_in_n_log_n() {
    joint_chain_scales(Written::AsIs);
}

/// [`joint_chain`] with its equations negated: before item PROJECT-each-canon the greedy
/// search took `x[i + 1] - x[i] == 3` first, failed, and a question per disjunct followed,
/// 122 times the bytes at 8n.
#[test]
fn the_middle_of_a_chain_whose_negated_disjunctions_jointly_leave_one_step_is_projected_in_n_log_n()
{
    joint_chain_scales(Written::Negated);
}

fn joint_chain_scales(written: Written) {
    let inputs = scaling::inputs(16, |m| joint_chain(m, written));
    scaling::check_order(
        &format!(
            "a chain whose disjunctions jointly leave one step, written {written:?}, projected"
        ),
        16,
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
fn cascade(n: usize, flipped: bool) -> Formula {
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

#[test]
fn the_middle_of_a_chain_of_removals_each_needing_the_one_before_is_projected_in_n_log_n() {
    for flipped in [false, true] {
        let inputs = scaling::inputs(16, |m| cascade(m, flipped));
        scaling::check_order(
            &format!("a chain of removals each needing the one before, flipped {flipped}"),
            16,
            1,
            |m| {
                let r = project_each(&inputs[&m], &middle(m)).expect("a projection");
                let s = r.0[0].clone().expect("a hull");
                assert!(s.contains(0) && !s.contains(-1) && !s.contains(1), "{s:?}");
            },
        );
    }
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

/// A chain of `n` stages `y[i + 1] <= y[i] + x[i]` with `x[i]` in {0, 2} and `y[0] == 0`:
/// `y[i]` is at most `2i` and unbounded below, a bound only the rows the disjunctions imply
/// give (item PRES-pendants-wider).
fn sum_chain(n: usize) -> Formula {
    let mut fs = vec![eq(y(0))];
    for i in 0..n - 1 {
        fs.push(ge(y(i).plus(&x(i)).minus(&y(i + 1))));
        fs.push(one_of(&x(i), &[0, 2]));
    }
    Formula::and(fs)
}

#[test]
fn the_middle_of_a_chain_bounded_by_the_rows_its_disjunctions_imply_is_projected_in_n_log_n() {
    let inputs = scaling::inputs(16, sum_chain);
    scaling::check(
        "a chain bounded by the rows its disjunctions imply",
        16,
        |m| {
            let mid = m / 2;
            let r = project_each(&inputs[&m], &[Atom::Sym(format!("y{mid:05}").into())])
                .expect("a projection");
            let s = r.0[0].clone().expect("a hull");
            let top = 2 * mid as i64;
            assert!(
                s.contains(top) && !s.contains(top + 1) && s.contains(-1_000_000),
                "{s:?}"
            );
        },
    );
}

/// A chain of `n` stages `y[i + 1] >= y[i] - 1` with `y[0] == 0`, and at the middle stage
/// `m`, `x >= 1 || y[m] >= 0` and `x <= 0 || y[m] >= 0`: by cases `y[m] >= 0`, where the rows
/// allow `-m`; no row bounds it above (item PRES-pendants-wider). Cases at every stage
/// (`x[i] >= 1 || y[i + 1] >= y[i]` and `x[i] <= 0 || y[i + 1] >= y[i]`) give the same bound
/// by cases, but the search through the disjunctions ([`pick`]) refuses its questions, so
/// that hull stays sound and wider (the tradeoff of plan item DISJ-dpll).
fn case_chain(n: usize) -> Formula {
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

#[test]
fn the_middle_of_a_chain_whose_lower_end_only_cases_give_is_projected_in_n_log_n() {
    let inputs = scaling::inputs(16, case_chain);
    scaling::check("a chain whose lower end only cases give", 16, |m| {
        let mid = m / 2;
        let r = project_each(&inputs[&m], &[Atom::Sym(format!("y{mid:05}").into())])
            .expect("a projection");
        let s = r.0[0].clone().expect("a hull");
        assert!(
            s.contains(0) && !s.contains(-1) && s.contains(1_000_000),
            "{s:?}"
        );
    });
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

/// Random case 1063 of the harness: the one point is `(3, 0, 0, 29, 17, 16)`. The question
/// `y4 <= 16` is refused after the removals by bounds, so the hull of `y4` is `16..=17`,
/// which holds the point's 17, as on main before PRES-disj-cost-xr. Item I21 asked the
/// refused question again without the removals, which made the hull exact, at 1.77 times
/// main's instructions on `overlap_rows` projected at k = 16; it was removed
/// (PRES-disj-regressions, comment at `ask` in `project_parts`). The other hulls are exact.
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
    let got = projected_two_values(&doms, &[-1, -1, 1, 2, 1, 1], 88);
    let mut want = [3, 0, 0, 29, 17, 16].map(|v| Some((v, v)));
    want[4] = Some((16, 17));
    assert_eq!(got, want);
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
