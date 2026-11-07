//! Many disjunctions over one linked group of rows (plan items DISJ-diff-fast and
//! DISJ-incremental): each disjunct is tested against the base projected onto the atoms of
//! the disjuncts near it, so `n` disjunctions cost about `n log n`, not `n` solves of the
//! whole group.

use zed_tests::scaling;
use zedc::store::presburger::{Atom, Con, Formula, Lin, decide, project_each};

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
    let mut fs = vec![ge(x(0)), ge(Lin::constant(8 * n as i128).minus(&x(n - 1)))];
    for i in 0..n - 1 {
        fs.push(ge(step(i).minus(&y(i))));
        fs.push(ge(y(i).minus(&Lin::constant(1))));
        fs.push(ge(Lin::constant(2).minus(&y(i))));
    }
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

#[test]
fn the_middle_of_a_chain_of_three_atom_rows_whose_disjuncts_hold_is_projected_in_n_log_n() {
    projects(
        "a chain of three-atom rows projected, a disjunct holding",
        32,
        general_chain,
        Holds::First,
    );
}

#[test]
fn a_chain_of_three_atom_rows_whose_disjuncts_do_not_hold_is_decided_in_n_log_n() {
    decides(
        "a chain of three-atom rows decided, no disjunct holding",
        64,
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

#[test]
fn the_middle_of_a_chain_of_three_atom_rows_whose_disjuncts_do_not_hold_is_projected_in_n_log_n() {
    projects(
        "a chain of three-atom rows projected, no disjunct holding",
        32,
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

/// A chain of three-atom rows of `n` stages as [`general_chain`] with `x[n - 1] <= end`, and
/// at every `every`-th stage `x[i + 1] - x[i] + y[i]` in `sums` and, unless `steps` is empty,
/// `x[i + 1] - x[i]` in `steps`.
fn small_chain(n: usize, every: usize, end: i128, sums: &[i128], steps: &[i128]) -> Formula {
    let mut fs = vec![ge(x(0)), ge(Lin::constant(end).minus(&x(n - 1)))];
    for i in 0..n - 1 {
        fs.push(ge(step(i).minus(&y(i))));
        fs.push(ge(y(i).minus(&Lin::constant(1))));
        fs.push(ge(Lin::constant(2).minus(&y(i))));
    }
    let any_of = |l: &Lin, vs: &[i128]| {
        Formula::or(vs.iter().map(|v| eq(l.minus(&Lin::constant(*v)))).collect())
    };
    for i in (0..n - 1).step_by(every) {
        fs.push(any_of(&step(i).plus(&y(i)), sums));
        if !steps.is_empty() {
            fs.push(any_of(&step(i), steps));
        }
    }
    Formula::and(fs)
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
    let cases: [Small; 6] = [
        (6, 2, 14, &[4, 5], &[]),
        (6, 2, 14, &[4, 6], &[]),
        (7, 3, 16, &[4, 5], &[]),
        (5, 2, 18, &[6, 9], &[3, 7]),
        (5, 2, 17, &[6, 9], &[3, 7]),
        (5, 2, 5, &[4, 5], &[]),
    ];
    for (n, every, end, sums, steps) in cases {
        let f = small_chain(n, every, end, sums, steps);
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
