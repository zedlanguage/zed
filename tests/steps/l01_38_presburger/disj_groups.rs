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
