//! Terms nested 20,000 deep lowered, raised and checked on a thread of the default 2 MiB stack
//! (author P178: an unusual size is a benchmark): the lowering, the walk that finds a lambda
//! body's uses and the raise each keep their work on the heap (step T2-mid). A plain recursion
//! takes at least 112 bytes a level (measured at opt-level 2), so 20,000 levels, 2.2 MB, would
//! overflow that stack. The same inputs at small sizes are checked in `scaling.rs`.

use zed_kernel::{Evaluator, Term, World};
use zed_tests::deep::on_small_stack;
use zedc::zir::lower::{lower, raise};

use crate::scaling::{lets_of_lambdas, nest, push_under_ifs};

#[test]
fn a_term_nested_20000_deep_is_lowered_and_raised_on_a_2_mib_stack() {
    on_small_stack(|| {
        let t = nest(20_000);
        let back = raise(&lower(&t).unwrap()).unwrap();
        let run = |t: &Term| Evaluator::new(World::new()).run(t).unwrap();
        assert_eq!(run(&back), run(&t));
    });
}

#[test]
fn lambdas_nested_20000_deep_are_lowered_on_a_2_mib_stack() {
    on_small_stack(|| {
        let t = lets_of_lambdas(20_000);
        let back = raise(&lower(&t).unwrap()).unwrap();
        let run = |t: &Term| Evaluator::new(World::new()).run(t).unwrap();
        assert_eq!(run(&back), run(&t));
    });
}

#[test]
fn a_port_used_20000_regions_deep_is_lowered_and_checked_on_a_2_mib_stack() {
    on_small_stack(|| {
        let g = lower(&push_under_ifs(20_000)).unwrap();
        zedc::zir::validate::validate(&g).unwrap();
    });
}
