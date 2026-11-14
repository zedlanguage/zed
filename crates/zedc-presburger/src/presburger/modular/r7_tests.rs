//! Round-7 tests of the one-variable modular solver (PERF-negated-chain-xr).

use super::*;
use crate::scaling;
mod bench;

/// `x mod 3 == 2`, `0 <= x <= 10000`, and `n` atoms fixed one after another: `a_n == 1` and
/// `2 a_i == 2 a_(i+1)`, the rows written so that each pass of the constant propagation of
/// step 1 can fix only one more atom.
fn fixed_chain(n: usize) -> Formula {
    let atoms: Vec<_> = (0..=n)
        .map(|i| Atom::Sym(format!("f{i:06}").into()))
        .collect();
    let mut parts = Vec::new();
    for pair in atoms.windows(2) {
        parts.push(Formula::Con(Con::eq(
            &Lin::atom(pair[0].clone()).times(2),
            &Lin::atom(pair[1].clone()).times(2),
        )));
    }
    parts.push(Formula::Con(Con::eq(
        &Lin::atom(atoms[n].clone()),
        &Lin::constant(1),
    )));
    let x = Lin::atom(Atom::Sym("x".into()));
    let q = Lin::atom(Atom::Aux(0));
    let r = Lin::atom(Atom::Aux(1));
    parts.extend([
        Formula::Con(Con::eq(&x, &q.times(3).plus(&r))),
        Formula::Con(Con::ge(&r, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(2), &r)),
        Formula::Con(Con::eq(&r, &Lin::constant(2))),
        Formula::Con(Con::ge(&x, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(10000), &x)),
    ]);
    Formula::And(crate::presburger::Shared::new(parts))
}

/// `(x mod 6) mod 2 == 1 && 0 <= x <= 20`: `x = 6 q + r`, `r = 2 p + s`, the rows of the two
/// divisions in the order given by `inner_first`, and in the coordinates of `names`.
fn nested_remainder(inner_first: bool, names: [&str; 5]) -> Formula {
    let [x, q, r, p, s] = names.map(|n| Lin::atom(Atom::Sym(n.into())));
    let outer = vec![
        Formula::Con(Con::eq(&x, &q.times(6).plus(&r))),
        Formula::Con(Con::ge(&r, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(5), &r)),
    ];
    let inner = vec![
        Formula::Con(Con::eq(&r, &p.times(2).plus(&s))),
        Formula::Con(Con::ge(&s, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(1), &s)),
    ];
    let (a, b) = if inner_first {
        (inner, outer)
    } else {
        (outer, inner)
    };
    let mut parts = a;
    parts.extend(b);
    parts.extend([
        Formula::Con(Con::eq(&s, &Lin::constant(1))),
        Formula::Con(Con::ge(&x, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(20), &x)),
    ]);
    Formula::and(parts)
}

#[test]
fn nested_remainder_answers_do_not_depend_on_row_order() {
    // R7-CLAUDE-2: step 3 kept the first row that defines a remainder and skipped a later row
    // whose `x_root` an earlier row had defined. Each writing has the point x = 1.
    let mut got = Vec::new();
    for names in [
        ["x", "q", "r", "p", "s"],
        ["x", "a", "b", "c", "d"],
        ["z", "y", "w", "v", "u"],
    ] {
        for inner_first in [false, true] {
            let f = nested_remainder(inner_first, names);
            let answer = solve_modular(&f, true).map(|m| m.map(|m| f.holds(&m)));
            got.push((names[0], inner_first, answer));
        }
    }
    println!("NESTED {got:?}");
    assert!(got.iter().all(|g| g.2 == got[0].2), "{got:?}");
}

/// The small instances of the benchmark in `bench.rs`: each chain of fixed atoms has a point.
#[test]
fn the_benchmark_inputs_have_their_answers_at_small_sizes() {
    for n in 1..=8 {
        assert!(
            matches!(solve_modular(&fixed_chain(n), false), Some(Some(_))),
            "{n}"
        );
    }
}
