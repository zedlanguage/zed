//! The benchmarks of `extend.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::extend::*;
use zedc::store::presburger::extend::Extending;
use zedc::store::presburger::{Formula, Lin};

#[test]
fn a_chain_of_extensions_is_decided_in_time_of_its_links() {
    // f{i} = f{i-1} && x + i * y <= 1000 i, over x >= y + 1: the conjunction of f{n} holds n
    // constraints, and deciding each f{i} whole costs O(n²) in all; each is decided from the
    // one it extends.
    let chain = |n: usize| {
        let mut f = Formula::and(vec![
            ge(sym("x"), sym("y").plus(&Lin::constant(1))),
            ge(sym("y"), Lin::constant(0)),
        ]);
        let mut out = Vec::with_capacity(n);
        for i in 1..=n as i64 {
            f = extend(&f, vec![sum(i, 1000 * i)]);
            out.push(f.clone());
        }
        out
    };
    let chains = zed_tests::scaling::inputs(2500, chain);
    for f in chains[&2500].iter().step_by(37) {
        assert_eq!(Extending::new().answers(f), decided(f), "{f}");
    }
    zed_tests::scaling::check("the answers of a chain of extensions", 2500, |n| {
        let mut e = Extending::new();
        for f in &chains[&n] {
            let a = e.answers(f);
            assert_eq!((a.holds, a.fails), (Ok(true), Ok(true)));
        }
    });
}

#[test]
fn bindings_put_in_place_scale() {
    // The substitution reads each top-level constraint once and resolves each atom through a
    // union of classes with its path compressed: time of the formula times a logarithm.
    use zedc::store::presburger::extend::with_bindings_in_place;
    let chains = zed_tests::scaling::inputs(9500, |n| bound_chain(n, 0));
    zed_tests::scaling::check("the bindings of a chain put in place", 9500, |n| {
        assert!(with_bindings_in_place(&chains[&n]).is_some());
    });
}
