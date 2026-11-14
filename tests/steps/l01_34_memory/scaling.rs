//! The memory planner and the machine keep their work on the heap (step T2-mid): regions nest,
//! values nest and closures capture closures as deep as the program.
//!
//! The plan numbers its regions and links each to the region holding it, so a region is found
//! from its parent's in O(1) and a path is printed for a message only: planning and running a
//! nest `d` deep are of order d (T14-paths; COMPLEXITY.md F62 and Z4). The tests here run each
//! shape at depths 0 to 6 on the test's own stack. The same shapes at depths about 20% past the
//! ones at which the recursive planner and machine before T2-mid (578fbe70e) overflowed a 2 MiB
//! stack, and the order of the work, are benchmarks, in `bench.rs` (author P178: a test that
//! needs an unusual size is a benchmark).

use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::value::Value;
use zed_kernel::{Evaluator, Prim, Term, World};
use zedc::zir::lower::lower;
use zedc::zir::memory::{self, Stats};

use zed_tests::step_helpers::l01_33_lowering::{nest, push_under_ifs};

/// The depths of the tests here: the empty shape, one level, and a few levels more.
const DEPTHS: std::ops::RangeInclusive<usize> = 0..=6;

/// `t` lowered, planned with fusion and run by the machine: the value it gives and its counts.
fn planned_and_run(t: &Term) -> (Value, Stats) {
    let g = lower(t).unwrap();
    let p = memory::plan(&g, true);
    memory::run(&g, &p, &mut Evaluator::new(World::new())).unwrap()
}

/// `t` lowered, planned with fusion and run with a `stdout` port: the lines it pushed.
fn pushed_lines(t: &Term) -> usize {
    let g = lower(t).unwrap();
    let p = memory::plan(&g, true);
    let mut ev = Evaluator::new(World::new().output("stdout"));
    memory::run(&g, &p, &mut ev).unwrap();
    ev.world.log("stdout").len()
}

#[test]
fn a_nest_of_ifs_is_planned_and_run_to_the_kernels_value() {
    for d in DEPTHS {
        let t = nest(d);
        let want = Evaluator::new(World::new()).run(&t).unwrap();
        assert_eq!(planned_and_run(&t).0, want, "depth {d}");
    }
}

#[test]
fn a_push_under_nested_ifs_is_planned_and_run_once() {
    for d in DEPTHS {
        assert_eq!(pushed_lines(&push_under_ifs(d)), 1, "depth {d}");
    }
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
fn a_nested_value_is_allocated_and_freed_a_cell_a_level() {
    for d in DEPTHS {
        let (v, s) = planned_and_run(&wrap_deep(d));
        assert_eq!(v, deep_tuple(d), "depth {d}");
        let n = d as u64;
        assert_eq!((s.allocations, s.frees), (n, n), "depth {d}: {s:?}");
    }
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
fn closures_capturing_closures_are_called_and_dropped() {
    for d in DEPTHS {
        let (v, s) = planned_and_run(&closure_chain(d));
        assert_eq!(v, Value::from(7i64), "depth {d}");
        assert_eq!(s.allocations, s.frees, "depth {d}: {s:?}");
    }
}
