//! Benchmarks of `xst::s4`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

#[test]
fn a_cycle_of_differences_with_one_bound_is_exact_in_near_linear_time() {
    let p = Premises::new();
    for n in [16, 128] {
        let (ns, all) = cyclic_base(n);
        let s = ints(&ns).assume(&all, true, &p);
        for x in &ns {
            assert!(s.get(x).contains(&Value::Int(10)), "n = {n}: {x}");
            assert!(!s.get(x).contains(&Value::Int(11)), "n = {n}: {x}");
        }
    }
    let inputs = scaling::inputs(16, cyclic_base);
    scaling::check_order(
        "a cyclic base of n differences, one conjunction",
        16,
        1,
        |m| {
            let (ns, all) = &inputs[&m];
            drop(ints(ns).assume(all, true, &Premises::new()));
        },
    );
}

#[test]
fn a_cycle_of_weight_zero_fixes_each_name_in_near_linear_time() {
    chain_answers("cycle of weight 0", |n| Some(1 - n as i64), false);
}

#[test]
fn a_cycle_of_weight_one_is_empty_in_near_linear_time() {
    chain_answers("cycle of weight 1", |n| Some(2 - n as i64), true);
}

/// CONTROL of the two above (Claude's open chain): no closing test.
#[test]
fn an_open_chain_narrows_in_near_linear_time() {
    chain_answers("open chain", |_| None, false);
}

#[test]
fn a_walk_of_disjunctions_narrows_in_near_linear_time() {
    family(
        "walk",
        5,
        |n| walk(n, true),
        |n| {
            let mut w: Vec<_> = (0..n)
                .map(|i| (format!("v{i}"), 0, 3, vec![1, 2, 3]))
                .collect();
            w.push(("w".into(), 0, 1, vec![0, 1]));
            w
        },
    );
}

/// The walk without its start, of `n` rows: `walk(n + 1, false)`, since without its start a
/// walk of `m` names has `m - 1` rows, and sizes 5 and 40 of `walk(n, false)` were 4 and 39
/// rows, 9.75 times apart where the check reads 8 (ST-walk-orders-nine).
#[test]
fn control_a_walk_without_its_start_narrows_nothing_in_near_linear_time() {
    family(
        "walk without its start",
        5,
        |n| walk(n + 1, false),
        |n| {
            let mut w: Vec<_> = (0..=n).map(|i| (format!("v{i}"), 0, 3, upto(3))).collect();
            w.push(("w".into(), 0, 1, upto(1)));
            w
        },
    );
}

/// The walk, and the walk without its start, given as one conjunction and in the reverse
/// order: near linear time in both, as [`family`] checks in the forward order, where it also
/// checks the answers in each order (ST-walk-orders: on main 44 to 85 at 8n at once, each row
/// joined against all the rows before it, and 43 to 81 in reverse). The walk is measured from
/// 40 rows, where a meet of a threshold row that changed nothing but copied its product made a
/// kept block compare every product so copied since (`Scope::meet_own`): 11.0 in reverse.
/// Each is of `n` rows: the walk without its start has one name more than its rows.
#[test]
fn a_walk_narrows_in_near_linear_time_at_once_and_in_reverse() {
    for (what, n, start) in [("walk", 40, true), ("walk without its start", 10, false)] {
        let inputs = scaling::inputs(n, |m| walk(m + usize::from(!start), start));
        for how in [How::AtOnce, How::Backward] {
            scaling::check_order(&format!("{what}, {how:?}, n rows"), n, 1, |m| {
                drop(inputs[&m].narrowed(how));
            });
        }
    }
}

#[test]
fn c26_narrows_in_near_linear_time() {
    unbounded_family("C26", 16, |k| c26(k, false));
}

#[test]
fn base_churn_narrows_in_near_linear_time() {
    unbounded_family("base churn", 4, |k| c26(k, true));
}

#[test]
fn shifted_ping_pong_is_exact_or_refused_in_near_linear_time() {
    family("shifted ping-pong", 16, ping_pong_shifted, |r| {
        let r = r as i64;
        vec![
            ("x".into(), -1, r, vec![-1]),
            ("y".into(), -1, r, vec![-1, 0]),
            ("z".into(), -1, r, vec![-1, 0]),
        ]
    });
}

#[test]
fn a_chain_raise_narrows_in_near_linear_time() {
    family("chain raise", 16, chain_raise, |k| {
        let k = k as i64;
        let mut w: Vec<_> = (0..k)
            .map(|i| (format!("x{i}"), k - 1, k + 1, vec![k, k + 1]))
            .collect();
        w.extend((0..k).map(|j| (format!("y{j}"), 0, 1, upto(1))));
        w
    });
}

/// The chain raise given as one conjunction: near linear time, as in the forward order
/// (ST-walk-orders: on main 16 to 37 at 8n, each `x0 >= j + 1` raising every `x_i` in turn).
#[test]
fn a_chain_raise_given_at_once_narrows_in_near_linear_time() {
    let inputs = scaling::inputs(16, chain_raise);
    scaling::check_order("chain raise, AtOnce, k tests", 16, 1, |m| {
        drop(inputs[&m].narrowed(How::AtOnce));
    });
}

/// The chain raise in the reverse order: near linear time, as in the other two orders
/// (ST-walk-orders-left: on main 10.4 to 11.0 at 8n, since a case `y_j <= -1` emptied `x0`
/// by its interval alone, `x0 < j + 1` where `x0 >= k`, which was found only after every
/// block naming `x0` was projected, O(k) blocks at each of k tests).
#[test]
fn a_chain_raise_in_reverse_narrows_in_near_linear_time() {
    let inputs = scaling::inputs(32, chain_raise);
    scaling::check_order("chain raise, Backward, k tests", 32, 1, |m| {
        drop(inputs[&m].narrowed(How::Backward));
    });
}

/// C26 given as one conjunction: near linear time, as one at a time (on main 10.0 at 8n at
/// n = 32). The answers in this order are checked by [`unbounded_family`].
#[test]
fn c26_given_at_once_narrows_in_near_linear_time() {
    let inputs = scaling::inputs(32, |k| c26(k, false));
    scaling::check_order("C26, AtOnce, k tests", 32, 1, |m| {
        drop(inputs[&m].narrowed(How::AtOnce));
    });
}

/// Base churn given as one conjunction: near linear time, as one at a time. Before
/// PERF-l139-family 11.1 at 8n by bytes at n = 16 and 10.7 at n = 32: the conjunction the
/// paths do not take is narrowed as one node, whose cases project blocks of a few rows each,
/// a linear number of them, but the hull of each asked O(log k) questions for a side inside a
/// row of two atoms (`x - y >= 2k + j`) at distance about k from the point (`hull_side`).
/// Since PERF-l139-family each side is asked first at the real bound of its rows (`real_end`),
/// one question a side: 8.1 at 8n. The answers in this order are checked by
/// [`unbounded_family`].
#[test]
fn churn_given_at_once_narrows_in_near_linear_time() {
    let inputs = scaling::inputs(16, |k| c26(k, true));
    scaling::check_order("base churn, AtOnce, k tests", 16, 1, |m| {
        drop(inputs[&m].narrowed(How::AtOnce));
    });
}

/// [`class_cases`] in the reverse order, the class last, which narrows again by each of the
/// `k` kept tests once: near linear time, and every `y_i` in `-20..=-5`.
#[test]
fn split_class_last_scales() {
    let low: Vec<i64> = (-20..=-5).collect();
    let s = class_cases(5).narrowed(How::Backward);
    for i in 0..5 {
        assert_eq!(kept(&s, &format!("y{i}"), -21, 21), low, "y{i}: {s}");
    }
    let inputs = scaling::inputs(16, class_cases);
    scaling::check_order("class cases, Backward, k tests", 16, 1, |m| {
        drop(inputs[&m].narrowed(How::Backward));
    });
}

/// [`class_cases_moved`] one at a time: near linear time.
#[test]
fn split_moved_often_scales() {
    let inputs = scaling::inputs(16, class_cases_moved);
    scaling::check_order("class cases moved, Forward, k tests", 16, 1, |m| {
        drop(inputs[&m].narrowed(How::Forward));
    });
}

/// [`holes_cut_one_at_a_time`] in the forward order: each cut looks only at the spans inside
/// the run of non-members it lengthens, so near linear time, though every case's span starts
/// at the member each cut takes.
#[test]
fn holes_cut_one_at_a_time_scale() {
    let s = holes_cut_one_at_a_time(5).narrowed(How::Forward);
    let even: Vec<i64> = (-30i64..=30).filter(|v| v.rem_euclid(2) == 0).collect();
    for i in 0..5 {
        assert_eq!(kept(&s, &format!("x{i}"), -31, 31), even, "x{i}: {s}");
    }
    let inputs = scaling::inputs(16, holes_cut_one_at_a_time);
    scaling::check_order("holes cut one at a time, Forward, k tests", 16, 1, |m| {
        drop(inputs[&m].narrowed(How::Forward));
    });
}

/// [`points_written_after`] backward, the second case `x_i % 2 == 0`: each constraint looks
/// only at the tests that fix its name `x_i`, not the `k` that fix `y`, so near linear time;
/// each `x_i` ends even.
#[test]
fn points_written_after_scale() {
    let s = points_written_after(5, even).narrowed(How::Backward);
    let even_values: Vec<i64> = (-20i64..=20).filter(|v| v.rem_euclid(2) == 0).collect();
    for i in 0..5 {
        assert_eq!(
            kept(&s, &format!("x{i}"), -21, 21),
            even_values,
            "x{i}: {s}"
        );
    }
    let inputs = scaling::inputs(16, |k| points_written_after(k, even));
    scaling::check_order("points written after, Backward, k tests", 16, 1, |m| {
        drop(inputs[&m].narrowed(How::Backward));
    });
}

/// [`relation_points_written_after`] backward: each test is kept with the points of its
/// cases, and each constraint rereads only the tests that fix its own `x_i`, so near linear
/// time in the number of tests. The answers are checked at a small size in
/// `points_of_relations_written_after_are_dropped`. Sized at 64 tests: at load 24 to 31 the
/// one run at 64 takes 0.16 s and at 512 1.6 s, the whole check (warm-up, first and least
/// runs of each size) 4.7 s; at 128 the check took 15 s and at 256 it passed the 20 s limit.
#[test]
fn points_of_relations_written_after_scale() {
    let inputs = scaling::inputs(64, relation_points_written_after);
    scaling::check_order(
        "points of relations written after, Backward, k tests",
        64,
        1,
        |m| {
            drop(inputs[&m].narrowed(How::Backward));
        },
    );
}

/// [`linear_moved`] narrows in near-linear time.
#[test]
fn linear_moved_often_scales() {
    let inputs = scaling::inputs(16, linear_moved);
    scaling::check_order("linear cases moved, Forward, k tests", 16, 1, |m| {
        drop(inputs[&m].narrowed(How::Forward));
    });
}
