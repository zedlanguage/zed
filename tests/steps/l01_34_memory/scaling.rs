//! The memory planner and the machine keep their work on the heap (step T2-mid): regions nest,
//! values nest and closures capture closures as deep as the program, on a thread of the
//! default 2 MiB stack.
//!
//! The plan numbers its regions and links each to the region holding it, so a region is found
//! from its parent's in O(1) and a path is printed for a message only: planning and running a
//! nest `d` deep are of order d (T14-paths; COMPLEXITY.md F62 and Z4). Each depth here is the
//! smallest round depth about 20% past the one at which the recursive planner and machine before
//! T2-mid (578fbe70e) overflowed a 2 MiB stack in the dev profile, measured 2026-11-14: a nest of
//! ifs, a push under ifs and a closure chain at 1,046 (1,031 ran), a value at 11,875 (11,750
//! ran). Their benchmarks, in `bench.rs`, check the order of the work.

use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::value::Value;
use zed_kernel::{Evaluator, Prim, Term, World};
use zed_tests::deep::on_small_stack;
use zedc::zir::lower::lower;
use zedc::zir::memory;

use zed_tests::step_helpers::l01_33_lowering::{nest, push_under_ifs};

/// `t` lowered, planned with fusion and run by the machine, on a 2 MiB stack: the value it
/// gives.
fn planned_and_run(t: &Term) -> Value {
    let g = lower(t).unwrap();
    on_small_stack(|| {
        let p = memory::plan(&g, true);
        memory::run(&g, &p, &mut Evaluator::new(World::new()))
            .unwrap()
            .0
    })
}

#[test]
fn a_nest_of_ifs_1250_deep_is_planned_and_run_on_a_2_mib_stack() {
    let t = nest(1_250);
    let want = Evaluator::new(World::new()).run(&t).unwrap();
    assert_eq!(planned_and_run(&t), want);
}

#[test]
fn a_push_1250_regions_deep_is_planned_and_run_on_a_2_mib_stack() {
    let g = lower(&push_under_ifs(1_250)).unwrap();
    on_small_stack(|| {
        let p = memory::plan(&g, true);
        let mut ev = Evaluator::new(World::new().output("stdout"));
        memory::run(&g, &p, &mut ev).unwrap();
        assert_eq!(ev.world.log("stdout").len(), 1);
    });
}

/// `((…((), 1)…), 1)`, `d` deep.
fn deep_tuple(d: usize) -> Value {
    (0..d).fold(Value::tuple(Vec::new()), |v, _| {
        Value::tuple(vec![v, Value::from(1i64)])
    })
}

/// Part 0 of a constant tuple, a value `d` deep: the machine allocates a cell for each of its
/// parts, a constant having none, and frees them all when the result is dropped.
pub(super) fn wrap_deep(d: usize) -> Term {
    let t = Value::tuple(vec![deep_tuple(d), Value::from(1i64)]);
    prim(Prim::TupleGet, vec![lit(t), lit(0i64)])
}

#[test]
fn a_value_14000_deep_is_allocated_and_freed_on_a_2_mib_stack() {
    let t = wrap_deep(14_000);
    let g = lower(&t).unwrap();
    let s = on_small_stack(|| {
        let p = memory::plan(&g, true);
        memory::run(&g, &p, &mut Evaluator::new(World::new()))
            .unwrap()
            .1
    });
    assert_eq!((s.allocations, s.frees), (14_000, 14_000), "{s:?}");
}

/// `c0 = (x) -> x; c1 = (x) -> c0(x); …; c{d}(7)`: each closure captures the one before, so
/// the call runs `d` regions deep and the last closure holds a chain `d` deep.
pub(super) fn closure_chain(d: usize) -> Term {
    let call = app(var(&format!("c{d}")), vec![lit(7i64)]);
    (0..=d).rev().fold(call, |body, i| {
        let f = if i == 0 {
            lam(&["x"], var("x"))
        } else {
            lam(&["x"], app(var(&format!("c{}", i - 1)), vec![var("x")]))
        };
        let_(&format!("c{i}"), f, body)
    })
}

#[test]
fn closures_capturing_closures_1250_deep_are_called_and_dropped_on_a_2_mib_stack() {
    let g = lower(&closure_chain(1_250)).unwrap();
    let v = on_small_stack(|| {
        let p = memory::plan(&g, true);
        memory::run(&g, &p, &mut Evaluator::new(World::new()))
            .unwrap()
            .0
    });
    assert_eq!(v, Value::from(7i64));
}
