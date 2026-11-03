//! The memory planner and the machine keep their work on the heap (step T2-mid): regions nest,
//! values nest and closures capture closures as deep as the program, on a thread of the
//! default 2 MiB stack.
//!
//! The plan names each region by its path from the root, so a nest `d` deep holds paths of
//! O(d²) bytes in all, and planning and running it are of order d² (COMPLEXITY.md F62; the
//! keys are T12-Z4's to change). The nests here are 8,000 deep, four times the depth at
//! which the recursive planner and machine overflowed a 2 MiB stack, and not 100,000.

use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::value::Value;
use zed_kernel::{Evaluator, Prim, Term, World};
use zed_tests::deep::on_small_stack;
use zed_tests::scaling::check_order;
use zedc::zir::lower::lower;
use zedc::zir::memory;

use crate::l01_33_lowering::scaling::{nest, push_under_ifs};

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
fn a_nest_of_ifs_8000_deep_is_planned_and_run_on_a_2_mib_stack() {
    let t = nest(8_000);
    let want = Evaluator::new(World::new()).run(&t).unwrap();
    assert_eq!(planned_and_run(&t), want);
}

#[test]
fn a_push_8000_regions_deep_is_planned_and_run_on_a_2_mib_stack() {
    let g = lower(&push_under_ifs(8_000)).unwrap();
    on_small_stack(|| {
        let p = memory::plan(&g, true);
        let mut ev = Evaluator::new(World::new().output("stdout"));
        memory::run(&g, &p, &mut ev).unwrap();
        assert_eq!(ev.world.log("stdout").len(), 1);
    });
}

#[test]
fn planning_and_running_a_deep_nest_is_of_order_its_paths() {
    on_small_stack(|| {
        let (small, large) = (lower(&nest(500)).unwrap(), lower(&nest(4_000)).unwrap());
        let pick = |d: usize| if d == 500 { &small } else { &large };
        check_order("planning nested `if`s, paths O(d) long", 500, 2, |d| {
            memory::plan(pick(d), true);
        });
        let (ps, pl) = (memory::plan(&small, true), memory::plan(&large, true));
        check_order("running nested `if`s, paths O(d) long", 500, 2, |d| {
            let (g, p) = if d == 500 {
                (&small, &ps)
            } else {
                (&large, &pl)
            };
            memory::run(g, p, &mut Evaluator::new(World::new())).unwrap();
        });
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
fn wrap_deep(d: usize) -> Term {
    let t = Value::tuple(vec![deep_tuple(d), Value::from(1i64)]);
    prim(Prim::TupleGet, vec![lit(t), lit(0i64)])
}

#[test]
fn a_value_100000_deep_is_allocated_and_freed_on_a_2_mib_stack() {
    let t = wrap_deep(100_000);
    let g = lower(&t).unwrap();
    let s = on_small_stack(|| {
        let p = memory::plan(&g, true);
        memory::run(&g, &p, &mut Evaluator::new(World::new()))
            .unwrap()
            .1
    });
    assert_eq!((s.allocations, s.frees), (100_000, 100_000), "{s:?}");
}

/// `c0 = (x) -> x; c1 = (x) -> c0(x); …; c{d}(7)`: each closure captures the one before, so
/// the call runs `d` regions deep and the last closure holds a chain `d` deep.
fn closure_chain(d: usize) -> Term {
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
fn closures_capturing_closures_100000_deep_are_called_and_dropped_on_a_2_mib_stack() {
    let g = lower(&closure_chain(100_000)).unwrap();
    let v = on_small_stack(|| {
        let p = memory::plan(&g, true);
        memory::run(&g, &p, &mut Evaluator::new(World::new()))
            .unwrap()
            .0
    });
    assert_eq!(v, Value::from(7i64));
}

#[test]
fn deep_values_and_closure_chains_are_linear_in_their_depth() {
    on_small_stack(|| {
        let (small, large) = (
            lower(&wrap_deep(5_000)).unwrap(),
            lower(&wrap_deep(40_000)).unwrap(),
        );
        let (ps, pl) = (memory::plan(&small, true), memory::plan(&large, true));
        check_order("allocating and freeing a value n deep", 5_000, 1, |d| {
            let (g, p) = if d == 5_000 {
                (&small, &ps)
            } else {
                (&large, &pl)
            };
            memory::run(g, p, &mut Evaluator::new(World::new())).unwrap();
        });
        let small = lower(&closure_chain(5_000)).unwrap();
        let large = lower(&closure_chain(40_000)).unwrap();
        let pick = |d: usize| if d == 5_000 { &small } else { &large };
        check_order("planning a closure chain n deep", 5_000, 1, |d| {
            memory::plan(pick(d), true);
        });
        let (ps, pl) = (memory::plan(&small, true), memory::plan(&large, true));
        check_order(
            "calling and dropping a closure chain n deep",
            5_000,
            1,
            |d| {
                let (g, p) = if d == 5_000 {
                    (&small, &ps)
                } else {
                    (&large, &pl)
                };
                memory::run(g, p, &mut Evaluator::new(World::new())).unwrap();
            },
        );
    });
}
