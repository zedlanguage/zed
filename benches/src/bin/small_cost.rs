//! Hand-run benchmark of PRES-small-cost and PRES-small-front, moved out of
//! `tests/steps/l01_38_presburger/small_cost.rs`, where it was built only under a cfg switch:
//! prints the least instructions of five calls of `satisfiable` and `decide` on small formulas,
//! on chains of `max` definitions of growing length, and on ladders of bounds, and asserts
//! nothing. The tests of that file check the order of the same costs. `small_cost` takes no
//! arguments.

use zed_tests::scaling::Meter;
use zed_tests::step_helpers::l01_38_presburger::small_cost::*;
use zedc::store::presburger::{Formula, decide, satisfiable};

fn main() {
    let mut meter = Meter::new();
    let one = Formula::and(vec![
        max_def(&sym("x"), 1, &sym("x"), &q(0)),
        eq(&sym("x"), &k(6)),
        eq(&sym("y"), &k(4)),
    ]);
    let three = Formula::and(vec![
        eq(&q(0), &k(1)),
        eq(&sym("x"), &k(6)),
        eq(&sym("y"), &k(4)),
    ]);
    for (what, f) in [("one disjunction", &one), ("three equations", &three)] {
        let s = least(&mut meter, &|| drop(std::hint::black_box(satisfiable(f))));
        let d = least(&mut meter, &|| drop(std::hint::black_box(decide(f))));
        eprintln!("{what}: satisfiable {s}, decide {d}  {f}");
    }
    for inputs in [Inputs::Fixed, Inputs::Bounded, Inputs::Ranged] {
        for n in [1, 2, 4, 7, 8, 16, 32, 64, 512] {
            let f = defs(n, inputs);
            let s = least(&mut meter, &|| drop(std::hint::black_box(satisfiable(&f))));
            let d = least(&mut meter, &|| drop(std::hint::black_box(decide(&f))));
            eprintln!(
                "{inputs:?} n {n}: satisfiable {s} ({}/def), decide {d}; {:?}",
                s / u64::from(n),
                satisfiable(&f).map(|m| m.map(|m| m.len()))
            );
        }
    }
    for n in [64, 512] {
        let f = ladder(n);
        let s = least(&mut meter, &|| drop(std::hint::black_box(satisfiable(&f))));
        let d = least(&mut meter, &|| drop(std::hint::black_box(decide(&f))));
        eprintln!(
            "ladder n {n}: satisfiable {s} ({}/rung), decide {d}",
            s / u64::from(n)
        );
    }
}
