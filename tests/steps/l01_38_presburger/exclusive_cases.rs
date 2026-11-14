//! A disjunction of cases that exclude each other, as a `match` on an opcode gives:
//!
//! ```text
//! match op {
//!     0 => z = x + 2 w,
//!     1 => z = x + 2 w + 1,
//!     ...
//!     m - 1 => z = x + 2 w + m - 1,
//! }
//! ```
//!
//! with `w` in 0..5 but not 2 (a second disjunction, `w <= 1 || w >= 3`). Each case is
//! `op == k && z == x + 2 w + k`; no two hold at one point. Asked for `z`, the search for points
//! once forced the cases a round each, `m` searches of the whole formula, since one case's
//! bounds on `op` exclude every other's (item PROJECT-canon-rounds). The first search now
//! settles the cases left waiting by moving `op` and `z`, which only their disjunction reads.
//! In the chained forms `x` is one stage of a chain `x[i + 1] >= x[i] + 1` of `m` stages: the
//! middle one for every case, or stage `k` for case `k`, so that each case reads its own part
//! of the chain.

use zed_tests::scaling;
use zedc::store::interval::IntervalSet;
use zedc::store::presburger::{Atom, Con, Formula, Lin, project_each};

fn a(n: &str) -> Lin {
    Lin::atom(Atom::Sym(n.into()))
}

fn x(i: usize) -> Lin {
    Lin::atom(Atom::Sym(format!("x{i:05}").into()))
}

fn ge(l: Lin) -> Formula {
    Formula::Con(Con::ge(&l, &Lin::constant(0)))
}

fn eq(l: Lin) -> Formula {
    Formula::Con(Con::eq(&l, &Lin::constant(0)))
}

/// `0 <= w <= 5`, `w <= 1 || w >= 3`.
fn w_not_two() -> Vec<Formula> {
    vec![
        ge(a("w")),
        ge(Lin::constant(5).minus(&a("w"))),
        Formula::or(vec![
            ge(Lin::constant(1).minus(&a("w"))),
            ge(a("w").minus(&Lin::constant(3))),
        ]),
    ]
}

/// The `m` cases `op == k && z == x + 2 w + k`, with `x` the atom `x_of(k)`.
fn match_on_op(m: usize, x_of: impl Fn(usize) -> Lin) -> Formula {
    Formula::or(
        (0..m)
            .map(|k| {
                let k_ = Lin::constant(k as i128);
                Formula::and(vec![
                    eq(a("op").minus(&k_)),
                    eq(a("z")
                        .minus(&x_of(k))
                        .minus(&a("w"))
                        .minus(&a("w"))
                        .minus(&k_)),
                ])
            })
            .collect(),
    )
}

/// The `match` with `0 <= x <= 100`; `z` is in `[0, 109 + m]`.
pub(super) fn cases(m: usize) -> Formula {
    let mut fs = vec![ge(a("x")), ge(Lin::constant(100).minus(&a("x")))];
    fs.extend(w_not_two());
    fs.push(match_on_op(m, |_| a("x")));
    Formula::and(fs)
}

/// The `match` over a chain of `m` stages, `0 <= x[0]`, `x[i + 1] >= x[i] + 1`,
/// `x[m - 1] <= 4m`, so that `x[i]` is in `[i, 3m + 1 + i]`; case `k` reads stage `at(k, m)`.
fn chained(m: usize, at: fn(usize, usize) -> usize) -> Formula {
    let mut fs = vec![ge(x(0)), ge(Lin::constant(4 * m as i128).minus(&x(m - 1)))];
    fs.extend((0..m - 1).map(|i| ge(x(i + 1).minus(&x(i)).minus(&Lin::constant(1)))));
    fs.extend(w_not_two());
    fs.push(match_on_op(m, |k| x(at(k, m))));
    Formula::and(fs)
}

/// Every case reads the middle stage `h = m / 2`: `z` is in `[h, 4m + h + 10]`.
pub(super) fn middle(m: usize) -> Formula {
    chained(m, |_, m| m / 2)
}

/// Case `k` reads stage `k`: `z` is in `[0, 5m + 9]`.
pub(super) fn own_stage(m: usize) -> Formula {
    chained(m, |k, _| k)
}

fn z_of(f: &Formula) -> IntervalSet {
    let r = project_each(f, &[Atom::Sym("z".into())]).expect("a projection");
    r.0[0].clone().expect("a projection of z")
}

#[test]
fn every_case_of_the_match_is_projected_exactly() {
    for m in [1, 2, 3, 16, 40] {
        let h = (m / 2) as i64;
        let m_ = m as i64;
        assert_eq!(
            z_of(&cases(m)),
            IntervalSet::of(0, 109 + m_),
            "cases, m = {m}"
        );
        assert_eq!(
            z_of(&middle(m)),
            IntervalSet::of(h, 4 * m_ + h + 10),
            "middle stage, m = {m}"
        );
        assert_eq!(
            z_of(&own_stage(m)),
            IntervalSet::of(0, 5 * m_ + 9),
            "own stage, m = {m}"
        );
    }
}

/// Projects `z` of `fam(m)` at each size `m` of a scaling check, with its answer checked.
pub(super) fn projects(what: &str, fam: fn(usize) -> Formula, want: fn(usize) -> IntervalSet) {
    let inputs = scaling::inputs(32, fam);
    scaling::check_order(what, 32, 1, |m| {
        assert_eq!(z_of(&inputs[&m]), want(m), "{what}, m = {m}");
    });
}
