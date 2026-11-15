//! Benchmarks of step L3.2 (plan row MAP-run), run apart from the correctness tests
//! (`tools/run_tests.sh --bench`): `map`, `><`, ranges, a float `><` and `.foldl` over n
//! entries and over 8n. Their small instances are the cases of `runs`.
//!
//! The kernel runs time the terms zedc elaborates `xs.map(f)` and `xs >< (+)` to, built before
//! the runs; the whole-path run times `zedc run` of a program whose display holds the entries,
//! so it measures the parse, the check, the elaboration and the run together.

use std::collections::HashMap;

use zed_kernel::term::build::{lam, let_, lit, var};
use zed_kernel::{Family, Prim, Term, Value, eval};
use zed_tests::kernel::*;
use zed_tests::scaling::{self, FACTOR, Meter, hold_linear};

use super::program;
use zed_tests::step_helpers::l01_36a_executables::interpreter;

/// Entries of a kernel run.
const N_KERNEL: usize = 20_000;
/// Entries of the display of a whole-path run.
const N_PROGRAM: usize = 1_000;

/// `{0 -> 0, …, n-1 -> n-1}`.
fn entries(n: usize) -> Term {
    lit(Value::Family(Family::of((0..n as i64).map(|k| (k, k)))))
}

/// The term `xs.map(x -> x + 1)` elaborates to: a family over the keys of `xs` whose entry
/// at `k` is `f` applied to `xs[k]` (zedc-elab, `map_term`).
fn map_term(n: usize) -> Term {
    let f = lam(&["x"], add(var("x"), lit(1)));
    let body = Term::Fam {
        domain: rc(var("xs")),
        var: "k".into(),
        body: rc(Term::App(rc(var("f")), vec![get(var("xs"), var("k"))])),
    };
    let_("xs", entries(n), let_("f", f, body))
}

/// The term `xs >< (+)` elaborates to over int entries, with the identity 0.
fn sum_term(n: usize) -> Term {
    Term::Fold {
        family: rc(entries(n)),
        op: rc(Term::PrimFn(Prim::Add)),
        identity: Some(rc(lit(0))),
        depth: 1,
        ev: Default::default(),
    }
}

/// Holds the instructions of `run` at n and 8n, the least of three runs each, under
/// [`scaling::PREFERRED`] times: `map` and `><` are linear, and a count linear in n stays
/// near 8.
fn under_nine(what: &str, n: usize, run: impl Fn(usize)) {
    let mut meter = Meter::new();
    let mut least = |k: usize| (0..3).map(|_| meter.work(|| run(k)).units).min().unwrap();
    let (small, large) = (least(n), least(FACTOR * n));
    hold_linear(what, meter.unit(), small, large);
}

#[test]
fn map_runs_in_linear_time() {
    let terms = scaling::inputs(N_KERNEL, map_term);
    let run = |k: usize| {
        let v = eval(&terms[&k]).unwrap();
        assert!(matches!(v, Value::Family(f) if f.len() == k));
    };
    scaling::check(
        "the kernel run of `xs.map(x -> x + 1)` over n entries",
        N_KERNEL,
        run,
    );
    under_nine(
        "the kernel run of `xs.map(x -> x + 1)`, instructions",
        N_KERNEL,
        run,
    );
}

#[test]
fn a_sum_runs_in_linear_time() {
    let terms = scaling::inputs(N_KERNEL, sum_term);
    let run = |k: usize| {
        let want = (k as i64) * (k as i64 - 1) / 2;
        assert_eq!(eval(&terms[&k]).unwrap(), Value::Int(want));
    };
    scaling::check(
        "the kernel run of `xs >< (+)` over n entries",
        N_KERNEL,
        run,
    );
    under_nine("the kernel run of `xs >< (+)`, instructions", N_KERNEL, run);
}

#[test]
fn map_then_sum_of_a_display_runs_in_linear_time() {
    let srcs: HashMap<usize, _> = scaling::inputs(N_PROGRAM, |k| {
        let xs = (0..k).map(|x| x.to_string()).collect::<Vec<_>>().join(", ");
        program(
            &format!("whole_{k}"),
            &format!("${{[{xs}].map(x -> x + 1) >< (+)}}"),
        )
    });
    let run = |k: usize| {
        let ran = interpreter(&srcs[&k], &[], &[]);
        assert_eq!(ran.stderr, "");
        assert_eq!(ran.stdout, format!("{}\n", (k * (k + 1)) / 2));
    };
    scaling::check(
        "`zedc run` of `[…].map(x -> x + 1) >< (+)` over n entries",
        N_PROGRAM,
        run,
    );
}

/// The term `0 ..< n` elaborates to (zedc-elab, `Frame::Range`).
fn range_term(n: usize) -> Term {
    Term::Prim(Prim::Range, vec![lit(0), lit(n as i64)])
}

#[test]
fn a_range_runs_in_linear_time() {
    // Plan row MAP-run-rest. Complexity tradeoff: the range is built as a family of n entries,
    // O(n) time and space; a lazy range would read in O(1) and hold O(1), and is what the
    // kernel's `Fam` over an interval would give, but no consumer here reads a range without
    // visiting its entries, so the entries are made at once.
    let terms = scaling::inputs(N_KERNEL, range_term);
    let run = |k: usize| {
        let v = eval(&terms[&k]).unwrap();
        assert!(matches!(v, Value::Family(f) if f.len() == k));
    };
    scaling::check("the kernel run of `0 ..< n`", N_KERNEL, run);
    under_nine("the kernel run of `0 ..< n`, instructions", N_KERNEL, run);
}

/// The term `xs >< (+)` elaborates to over n float entries `0.5, 1.5, …`, which is never
/// empty here, so it takes no identity.
fn float_sum_term(n: usize) -> Term {
    let xs = (0..n as i64).map(|k| (Value::Int(k), Value::float(k as f64 + 0.5)));
    Term::Fold {
        family: rc(lit(Value::Family(Family::of(xs)))),
        op: rc(Term::PrimFn(Prim::Add)),
        identity: None,
        depth: 1,
        ev: Default::default(),
    }
}

#[test]
fn a_float_sum_on_the_canonical_tree_runs_in_linear_time() {
    let terms = scaling::inputs(N_KERNEL, float_sum_term);
    let run = |k: usize| {
        // Every partial sum is a multiple of 0.5 below 2^53, so each grouping gives k^2 / 2.
        let want = (k * k) as f64 / 2.0;
        assert_eq!(eval(&terms[&k]).unwrap(), Value::float(want));
    };
    scaling::check(
        "the kernel run of `xs >< (+)` over n float entries",
        N_KERNEL,
        run,
    );
    under_nine(
        "the kernel run of `xs >< (+)` over floats, instructions",
        N_KERNEL,
        run,
    );
}

#[test]
fn a_foldl_of_a_display_runs_in_linear_time() {
    let srcs: HashMap<usize, _> = scaling::inputs(N_PROGRAM, |k| {
        let xs = (0..k).map(|x| x.to_string()).collect::<Vec<_>>().join(", ");
        program(
            &format!("foldl_{k}"),
            &format!("${{[{xs}].foldl(0, (a, x) -> a + x)}}"),
        )
    });
    let run = |k: usize| {
        let ran = interpreter(&srcs[&k], &[], &[]);
        assert_eq!(ran.stderr, "");
        assert_eq!(ran.stdout, format!("{}\n", (k * (k.max(1) - 1)) / 2));
    };
    scaling::check(
        "`zedc run` of `[…].foldl(0, (a, x) -> a + x)` over n entries",
        N_PROGRAM,
        run,
    );
}

#[test]
fn a_sum_over_a_range_runs_in_linear_time() {
    let srcs: HashMap<usize, _> = scaling::inputs(N_KERNEL, |k| {
        program(
            &format!("range_sum_{k}"),
            &format!("${{(0 ..< {k}) >< (+)}}"),
        )
    });
    let run = |k: usize| {
        let ran = interpreter(&srcs[&k], &[], &[]);
        assert_eq!(ran.stderr, "");
        assert_eq!(ran.stdout, format!("{}\n", (k * (k - 1)) / 2));
    };
    scaling::check("`zedc run` of `(0 ..< n) >< (+)`", N_KERNEL, run);
}
