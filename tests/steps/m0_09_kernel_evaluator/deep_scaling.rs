//! The time of operations on deep values against the depth (the rule of low complexity,
//! DESIGN.md Part G), on an 8 MiB stack. See deep_values.rs for why this is a program of its own.

use zed_kernel::{Family, Value};
use zed_tests::deep::*;
use zed_tests::scaling;

/// The depth of the scaling tests. Below it the time per level rises with depth as the values
/// outgrow the caches: equality took 76 ns a level at 20,000, 435 at 160,000 and 403 at
/// 1,280,000, so a smaller size measures the caches and not the walk.
const SCALING_DEPTH: usize = 160_000;

/// Times `op` on two values holding every shape, built before any is timed, so that a shape
/// walked in more than linear time shows however few of the levels it is.
fn timed(what: &str, op: impl Fn(&Value, &Value) + Sync) {
    let n = SCALING_DEPTH;
    let build = |d| {
        (
            nested(in_each_in_turn, d, Value::Int(1)),
            nested(in_each_in_turn, d, Value::Int(2)),
        )
    };
    let (small, large) = (build(n), build(8 * n));
    scaling::check(what, n, |d| {
        let (a, b) = if d == n { &small } else { &large };
        op(a, b);
    });
}

#[test]
fn equality_scales_with_depth() {
    on_main_sized_stack(|| timed("equality, by depth", |a, b| assert!(a != b)));
}

#[test]
fn order_scales_with_depth() {
    on_main_sized_stack(|| timed("order, by depth", |a, b| assert!(a < b)));
}

#[test]
fn surface_equality_scales_with_depth() {
    on_main_sized_stack(|| {
        timed("surface equality, by depth", |a, b| {
            assert!(!a.surface_eq(b));
        });
    });
}

#[test]
fn a_copy_and_its_end_scale_with_depth() {
    on_main_sized_stack(|| timed("copy and free, by depth", |a, _| drop(a.clone())));
}

#[test]
fn printing_scales_with_depth() {
    on_main_sized_stack(|| timed("printing, by depth", |a, _| drop(a.to_string())));
}

#[test]
fn debug_printing_scales_with_depth() {
    on_main_sized_stack(|| {
        timed("debug printing, by depth", |a, _| drop(format!("{a:?}")));
    });
}

#[test]
fn the_key_scales_with_depth() {
    on_main_sized_stack(|| timed("the key, by depth", |a, _| drop(a.key())));
}

#[test]
fn membership_scales_with_length() {
    on_main_sized_stack(|| {
        let list = list_type();
        let n = SCALING_DEPTH;
        let build = |d| nested(in_atom, d, Value::atom("nil"));
        let (small, large) = (build(n), build(8 * n));
        scaling::check("membership in a recursive type, by length", n, |d| {
            assert!(list.contains(if d == n { &small } else { &large }));
        });
    });
}

#[test]
fn keypaths_scale_with_length() {
    on_main_sized_stack(|| {
        let n = 20_000;
        let path = |d: usize, last: i64| {
            let mut path = vec![Value::Int(0); d];
            path.push(Value::Int(last));
            Family::from_leaves([(path, Value::Int(1))]).unwrap()
        };
        let build = |d| (path(d, 1), path(d, 2));
        let (small, large) = (build(n), build(8 * n));
        scaling::check("a union of long keypaths, by length", n, |d| {
            let (a, b) = if d == n { &small } else { &large };
            assert_eq!(a.union(b).unwrap().leaves().len(), 2);
        });
    });
}
