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
use zed_tests::step_helpers::l01_36a_executables::{built, dir, executable, interpreter};

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
    // Counted here and held by `hold_linear`, not by a check: beside other tests on a machine with
    // no counter of instructions the test runs again alone, in a new process
    // (BENCH-self-counted-meters-processor-time).
    if scaling::ran_alone_in_a_new_process(&meter) {
        return;
    }
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

/// `r = 0 ..< n` read without a walk: the tuple of `r[n - 1]`, `n / 2 in r`, `r.count`, the
/// last entry of `r` and the entry after the one at `n / 2`.
fn range_reads_term(n: usize) -> Term {
    let n = n as i64;
    let half = Term::Prim(Prim::Tuple, vec![lit(n / 2), lit(n / 2)]);
    let reads = Term::Prim(
        Prim::Tuple,
        vec![
            get(var("r"), lit(n - 1)),
            Term::Prim(Prim::Has, vec![lit(n / 2), var("r")]),
            count(var("r")),
            Term::Prim(Prim::LastEntry, vec![var("r")]),
            Term::Prim(Prim::EntryAfter, vec![var("r"), half]),
        ],
    );
    let_("r", range_term(n as usize), reads)
}

#[test]
fn a_range_is_made_and_read_in_constant_time() {
    // Plan row RANGE-lazy. Complexity tradeoff: the range was built as a family of n entries,
    // O(n) time and memory for any read (the method until RANGE-lazy); it is kept as its two
    // ends, so making it and each read here cost O(1), and the entry after a key O(log n) by
    // a search over the ends with no entry built. The walk is the other side, below.
    let terms = scaling::inputs(N_KERNEL, range_reads_term);
    let run = |k: usize| {
        let (n, half) = (k as i64, k as i64 / 2);
        let pair = |x: i64| Value::tuple(vec![Value::Int(x), Value::Int(x)]);
        let want = Value::tuple(vec![
            Value::Int(n - 1),
            Value::Bool(true),
            Value::Int(n),
            pair(n - 1),
            pair(half + 1),
        ]);
        assert_eq!(eval(&terms[&k]).unwrap(), want);
    };
    scaling::check_order("the kernel run of reads of `0 ..< n`", N_KERNEL, 0, run);
}

/// `2^63 + d`, an integer past `i64`.
fn past_i64(d: usize) -> Value {
    Value::int(num_bigint::BigInt::from(i64::MAX) + 1 + d)
}

/// `r = 2^63 - 2 ..< 2^63 + n`, which crosses the 64-bit edge, read without a walk: the tuple
/// of `r[2^63 + n - 1]`, `2^63 + n / 2 in r`, `r.count`, the first and last entry of `r` and
/// the entries before and after the one at `2^63 + n / 2`.
fn wide_reads_term(n: usize) -> Term {
    let lo = lit(Value::int(num_bigint::BigInt::from(i64::MAX) - 1));
    let range = Term::Prim(Prim::Range, vec![lo, lit(past_i64(n))]);
    let half = || {
        Term::Prim(
            Prim::Tuple,
            vec![lit(past_i64(n / 2)), lit(past_i64(n / 2))],
        )
    };
    let reads = Term::Prim(
        Prim::Tuple,
        vec![
            get(var("r"), lit(past_i64(n - 1))),
            Term::Prim(Prim::Has, vec![lit(past_i64(n / 2)), var("r")]),
            count(var("r")),
            Term::Prim(Prim::FirstEntry, vec![var("r")]),
            Term::Prim(Prim::LastEntry, vec![var("r")]),
            Term::Prim(Prim::EntryBefore, vec![var("r"), half()]),
            Term::Prim(Prim::EntryAfter, vec![var("r"), half()]),
        ],
    );
    let_("r", range, reads)
}

#[test]
fn a_wide_range_is_made_and_read_in_constant_time() {
    // Plan row RANGE-lazy-wide. Complexity tradeoff: a range with an end past `i64` was built
    // as a family of its n entries, n big-integer additions and O(n) memory for any read (the
    // method until RANGE-lazy-wide); it is kept as its two ends, so making it and each read
    // here cost O(digits), the same at n and 8n.
    let terms = scaling::inputs(N_KERNEL, wide_reads_term);
    let run = |k: usize| {
        let pair = |x: Value| Value::tuple(vec![x.clone(), x]);
        let low = Value::Int(i64::MAX - 1);
        let want = Value::tuple(vec![
            past_i64(k - 1),
            Value::Bool(true),
            Value::Int(k as i64 + 2),
            pair(low),
            pair(past_i64(k - 1)),
            pair(past_i64(k / 2 - 1)),
            pair(past_i64(k / 2 + 1)),
        ]);
        assert_eq!(eval(&terms[&k]).unwrap(), want);
    };
    scaling::check_order(
        "the kernel run of reads of `2^63 - 2 ..< 2^63 + n`",
        N_KERNEL,
        0,
        run,
    );
}

/// `(0 ..< n) < (1 ..< n)`, `min` and `max` of the two, and `min` and `max` of `0 ..< n` and
/// `0 ..< n + 1`, which differ at their last ends.
fn ranges_ordered_term(n: usize) -> Term {
    let r = |a: i64, b: i64| Term::Prim(Prim::Range, vec![lit(a), lit(b)]);
    let n = n as i64;
    let both = |p: Prim, x: Term, y: Term| Term::Prim(p, vec![x, y]);
    Term::Prim(
        Prim::Tuple,
        vec![
            both(Prim::Lt, r(0, n), r(1, n)),
            both(Prim::Min, r(1, n), r(0, n)),
            both(Prim::Max, r(0, n), r(1, n)),
            both(Prim::Min, r(0, n + 1), r(0, n)),
            both(Prim::Max, r(0, n), r(0, n + 1)),
        ],
    )
}

#[test]
fn two_ranges_are_ordered_from_their_ends_in_constant_time() {
    // Plan row RANGE-lazy-wide. Complexity tradeoff: two ranges of other ends were ordered by
    // the walk over both maps, which built each, O(n) (the method until RANGE-lazy-wide); the
    // ends decide the order, so it is read from them, O(1), and no entry is built.
    let terms = scaling::inputs(N_KERNEL, ranges_ordered_term);
    let run = |k: usize| {
        let r = |a: i64, b: i64| Value::Family(Family::range(a, b - 1));
        let n = k as i64;
        let want = Value::tuple(vec![
            Value::Bool(true),
            r(0, n),
            r(1, n),
            r(0, n),
            r(0, n + 1),
        ]);
        let got = eval(&terms[&k]).unwrap();
        assert_eq!(got, want);
        let Value::Tuple(parts) = &got else {
            panic!("a tuple")
        };
        // The results are the ranges themselves, kept as their ends.
        let spans = parts[1..].iter().map(|v| match v {
            Value::Family(f) => f.span(),
            _ => None,
        });
        assert!(spans.into_iter().all(|s| s.is_some()));
    };
    scaling::check_order(
        "the kernel run of `<`, `min` and `max` of two ranges of n entries",
        N_KERNEL,
        0,
        run,
    );
}

/// `(2^63 ..< 2^63 + n) >< (+)` in the kernel: the walk builds the wide range's entries.
fn wide_sum_term(n: usize) -> Term {
    let range = Term::Prim(Prim::Range, vec![lit(past_i64(0)), lit(past_i64(n))]);
    fold(range, Term::PrimFn(Prim::Add), Some(lit(0)))
}

#[test]
fn a_walk_over_a_wide_range_runs_in_linear_time() {
    // Plan row RANGE-lazy-wide, the other side of the switchover (A96): the first walk builds
    // the wide range's n entries once, O(n) big-integer additions, as the eager range did, and
    // adds them, O(n).
    let terms = scaling::inputs(N_KERNEL, wide_sum_term);
    let run = |k: usize| {
        let n = num_bigint::BigInt::from(k);
        let base = num_bigint::BigInt::from(i64::MAX) + 1;
        let want = &base * &n + &n * (&n - 1) / 2;
        assert_eq!(eval(&terms[&k]).unwrap(), Value::int(want));
    };
    scaling::check(
        "the kernel run of `(2^63 ..< 2^63 + n) >< (+)`",
        N_KERNEL,
        run,
    );
    under_nine(
        "the kernel run of `(2^63 ..< 2^63 + n) >< (+)`, instructions",
        N_KERNEL,
        run,
    );
}

/// `r = 0 ..` read at `n`: the tuple of `r[n]`, `n in r` and `r.first` (zedc-elab,
/// `Frame::RangeFrom`).
fn open_reads_term(n: usize) -> Term {
    let n = n as i64;
    let reads = Term::Prim(
        Prim::Tuple,
        vec![
            Term::Prim(Prim::At, vec![var("r"), lit(n)]),
            Term::Prim(Prim::Has, vec![lit(n), var("r")]),
            Term::Prim(Prim::First, vec![var("r")]),
        ],
    );
    let_("r", Term::Prim(Prim::RangeFrom, vec![lit(0)]), reads)
}

#[test]
fn a_range_with_no_upper_end_is_read_in_constant_time() {
    // Plan row RANGE-open. Complexity tradeoff: a read of `0 ..` at `n` built by the integers
    // up to `n` would cost O(n) time and memory; `rangeFrom(0)` is kept as its low end, so the
    // range and each read cost O(1) at any key (a key past 64 bits, O(digits), in `runs`).
    let terms = scaling::inputs(N_KERNEL, open_reads_term);
    let run = |k: usize| {
        let n = k as i64;
        let want = Value::tuple(vec![Value::Int(n), Value::Bool(true), Value::Int(0)]);
        assert_eq!(eval(&terms[&k]).unwrap(), want);
    };
    scaling::check_order("the kernel run of reads of `0 ..` at n", N_KERNEL, 0, run);
}

#[test]
fn a_program_reading_a_range_with_no_upper_end_runs_in_constant_time() {
    // Plan row RANGE-open: the whole path, parse to output, of reads of `0 ..` at n; the key's
    // text grows by one digit from n to 8n.
    let srcs: HashMap<usize, _> = scaling::inputs(N_KERNEL, |k| {
        program(
            &format!("open_reads_{k}"),
            &format!(
                "${{[(0 ..)[{k}] else #outOfBounds -> -1, {k} in 0 .., (0 ..).first else #none -> -1]}}"
            ),
        )
    });
    let run = |k: usize| {
        let ran = interpreter(&srcs[&k], &[], &[]);
        assert_eq!(ran.stderr, "");
        assert_eq!(ran.stdout, format!("{{0 -> {k}, 1 -> true, 2 -> 0}}\n"));
    };
    scaling::check_order("`zedc run` of reads of `0 ..` at n", N_KERNEL, 0, run);
}

#[test]
fn a_walk_over_a_range_with_no_upper_end_runs_in_n_log_n_time() {
    // Plan row RANGE-open-walk: `zedc run` and the executable of a stream over `0 ..` whose
    // deciding entry is the n-th, n read at run time so that nothing folds at compile time.
    // Complexity tradeoff: the naive form builds each link's family over the whole range,
    // which never ends; the walk asks n entries, each through both links on a one-entry
    // family, O(1), and a step of the `gen` over its n frames, O(log n), so O(n log n), and
    // reads nothing past the deciding entry.
    let d = dir("l03_02_map_run/open_walk");
    let src = d.join("open_walk.zed");
    let body = "${[(0 ..).map(x -> x * 2).where(x -> x >= n).first else #none -> -1, \
                (0 ..).any(x -> x == n), (0 ..).find(x -> x >= n) else #none -> -1]}";
    let text = format!(
        "main(m: MainArgs) {{\n    n = int(m.stdin[0]) else #invalid -> 0 else #ioError -> 0 else #outOfBounds -> 0;\n    m.stdout <- \"{body}\";\n}}\n"
    );
    std::fs::write(&src, text).unwrap();
    let exe = d.join("open_walk");
    built(&src, &exe);
    let want = |k: usize| format!("{{0 -> {}, 1 -> true, 2 -> {k}}}\n", 2 * k.div_ceil(2));
    let run = |k: usize| {
        let ran = interpreter(&src, &[], format!("{k}\n").as_bytes());
        assert_eq!((ran.stderr.as_str(), ran.stdout), ("", want(k)));
    };
    // Both run at the whole-path size: at the kernel size, 20,000 and 160,000, the
    // executable alone took 36 s (measured 2026-11-16, load 147).
    scaling::check(
        "`zedc run` of walks over `0 ..` to the n-th entry",
        N_PROGRAM,
        run,
    );
    let run = |k: usize| {
        let ran = executable(&exe, &[], format!("{k}\n").as_bytes());
        assert_eq!((ran.stderr.as_str(), ran.stdout), ("", want(k)));
    };
    scaling::check(
        "an executable of walks over `0 ..` to the n-th entry",
        N_PROGRAM,
        run,
    );
}

/// `(0 ..< n) >< (+)` in the kernel: the walk builds the range's entries.
fn range_sum_term(n: usize) -> Term {
    fold(range_term(n), Term::PrimFn(Prim::Add), Some(lit(0)))
}

#[test]
fn a_walk_over_a_range_runs_in_linear_time() {
    // Plan row RANGE-lazy, the other side of the switchover (A96): the first walk builds the
    // range's n entries once, O(n), as the eager range did, and adds them, O(n).
    let terms = scaling::inputs(N_KERNEL, range_sum_term);
    let run = |k: usize| {
        let want = (k as i64) * (k as i64 - 1) / 2;
        assert_eq!(eval(&terms[&k]).unwrap(), Value::Int(want));
    };
    scaling::check("the kernel run of `(0 ..< n) >< (+)`", N_KERNEL, run);
    under_nine(
        "the kernel run of `(0 ..< n) >< (+)`, instructions",
        N_KERNEL,
        run,
    );
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

/// The terms of `xs.map(x -> (y -> y + x)).map(f -> f(1)) >< (+)` over `xs = {0 -> 0, …}`:
/// the first `map` makes a held family of n functions ([`zed_kernel::HeldFamily`], row
/// FAIL-family-function-entry), the second reads each entry and applies it. The sum is
/// n + n (n - 1) / 2.
fn function_entries_term(n: usize) -> Term {
    let make = Term::Fam {
        domain: rc(var("xs")),
        var: "k".into(),
        body: rc(lam(&["y"], add(var("y"), get(var("xs"), var("k"))))),
    };
    let apply = Term::Fam {
        domain: rc(var("g")),
        var: "k".into(),
        body: rc(Term::App(rc(get(var("g"), var("k"))), vec![lit(1)])),
    };
    let sum = Term::Fold {
        family: rc(apply),
        op: rc(Term::PrimFn(Prim::Add)),
        identity: Some(rc(lit(0))),
        depth: 1,
        ev: Default::default(),
    };
    let_("xs", entries(n), let_("g", make, sum))
}

#[test]
fn a_family_of_functions_is_made_read_and_applied_in_linear_time() {
    let terms = scaling::inputs(N_KERNEL, function_entries_term);
    let run = |k: usize| {
        let want = k as i64 + (k as i64) * (k as i64 - 1) / 2;
        assert_eq!(eval(&terms[&k]).unwrap(), Value::Int(want));
    };
    scaling::check(
        "the kernel run of a family of n functions made by `map`, read and applied",
        N_KERNEL,
        run,
    );
    under_nine(
        "the kernel run of a family of n functions, instructions",
        N_KERNEL,
        run,
    );
}

/// `zedc run` of a program and the executable `zedc build` makes of it, whose display holds
/// n functions `(y -> y + i)`, each read and applied to 1 by `map`: n + n (n - 1) / 2. The
/// executable reads the held family on the native path (zed-native `hooks.rs`,
/// `family_at`), and runs the `map` in the kernel on a term that makes the family once
/// (`Lets::held`; before, once per entry: 0.25 s at 500 entries, 14 s at 4000).
#[test]
fn a_display_of_functions_read_and_applied_runs_in_linear_time() {
    let n = N_PROGRAM / 2;
    let srcs: HashMap<usize, _> = scaling::inputs(n, |k| {
        let fs: Vec<String> = (0..k).map(|i| format!("{i} -> (y -> y + {i})")).collect();
        let d = dir(&format!("l03_02_map_run/function_display_{k}"));
        let src = d.join("f.zed");
        let text = format!(
            "main(m: MainArgs) {{\n    b = {{ {} }};\n    r = b.map(f -> f(1)) >< (+);\n    \
             m.stdout <- \"${{r}}\";\n}}\n",
            fs.join(", ")
        );
        std::fs::write(&src, text).unwrap();
        let exe = d.join("f");
        built(&src, &exe);
        (src, exe)
    });
    let want = |k: usize| format!("{}\n", k + k * (k - 1) / 2);
    let run = |k: usize| {
        let ran = interpreter(&srcs[&k].0, &[], &[]);
        assert_eq!((ran.stderr.as_str(), ran.stdout), ("", want(k)));
    };
    scaling::check(
        "`zedc run` of a display of n functions, each read and applied",
        n,
        run,
    );
    let run = |k: usize| {
        let ran = executable(&srcs[&k].1, &[], &[]);
        assert_eq!((ran.stderr.as_str(), ran.stdout), ("", want(k)));
    };
    scaling::check(
        "an executable over a display of n functions, each read and applied",
        n,
        run,
    );
}

/// `zedc run` and the executable of a program whose display `b` of n functions `(y -> y + i)`
/// goes through `op`, which keeps each, then has each function read and applied to 1 by
/// `map`: n + n (n - 1) / 2 (row FAIL-held-family-operators: the kernel keeps a held family
/// through `where` and a remap; the executable runs each in the kernel on a term that makes
/// the family once, `Lets::held`). Small instances: `functions::entries_that_are_functions_
/// are_read_and_applied`.
fn through_display_of_functions(name: &str, op: &str) {
    let n = N_PROGRAM / 2;
    let srcs: HashMap<usize, _> = scaling::inputs(n, |k| {
        let fs: Vec<String> = (0..k).map(|i| format!("{i} -> (y -> y + {i})")).collect();
        let d = dir(&format!("l03_02_map_run/function_{name}_{k}"));
        let src = d.join("f.zed");
        let text = format!(
            "main(m: MainArgs) {{\n    b = {{ {} }};\n    c = {op};\n    r = c.map(f -> f(1)) \
             >< (+);\n    m.stdout <- \"${{r}}\";\n}}\n",
            fs.join(", ")
        );
        std::fs::write(&src, text).unwrap();
        let exe = d.join("f");
        built(&src, &exe);
        (src, exe)
    });
    let want = |k: usize| format!("{}\n", k + k * (k - 1) / 2);
    let run = |k: usize| {
        let ran = interpreter(&srcs[&k].0, &[], &[]);
        assert_eq!((ran.stderr.as_str(), ran.stdout), ("", want(k)));
    };
    scaling::check(
        &format!("`zedc run` of a display of n functions through {name}"),
        n,
        run,
    );
    let run = |k: usize| {
        let ran = executable(&srcs[&k].1, &[], &[]);
        assert_eq!((ran.stderr.as_str(), ran.stdout), ("", want(k)));
    };
    scaling::check(
        &format!("an executable over a display of n functions through {name}"),
        n,
        run,
    );
}

/// Parts of the tuple of [`a_tuple_accumulator_settling_in_three_rounds_checks_in_linear_time`].
const N_SWAP: usize = 64;

/// `zedc run` of `[1, 2, 3].foldl((1.5, 0, ..., 0), (a, x) -> (a[1], a[0], a[2], ...))` with
/// n parts (row FAIL-fold-rotating-tuple-rounds): the checker's fold takes 3 rounds at every
/// width, each one application of the function to an accumulator of at most two rows of n
/// parts, and the run 3 steps of n parts. Measured before it was written (load 38 to 59):
/// 14, 20, 37 and 79 ms at n = 32, 64, 128 and 256. A rotation of n parts takes n + 1
/// rounds, so its check is Θ(n²) at best by this method (row PERF-fold-projection-fast-path,
/// COMPLEXITY.md); its small instances are
/// `folds::a_rotated_tuple_accumulator_settles_and_runs_at_any_width`.
#[test]
fn a_tuple_accumulator_settling_in_three_rounds_checks_in_linear_time() {
    let srcs: HashMap<usize, _> = scaling::inputs(N_SWAP, |k| {
        let start: Vec<&str> = (0..k).map(|i| if i == 0 { "1.5" } else { "0" }).collect();
        let parts: Vec<String> = (0..k)
            .map(|i| format!("a[{}]", if i < 2 { 1 - i } else { i }))
            .collect();
        program(
            &format!("swap_{k}"),
            &format!(
                "${{[1, 2, 3].foldl(({}), (a, x) -> ({}))}}",
                start.join(", "),
                parts.join(", ")
            ),
        )
    });
    // Three swaps of the first two parts leave the 1.5 at index 1.
    let want = |k: usize| {
        let parts: Vec<&str> = (0..k).map(|i| if i == 1 { "1.5" } else { "0" }).collect();
        format!("({})\n", parts.join(", "))
    };
    let run = |k: usize| {
        let ran = interpreter(&srcs[&k], &[], &[]);
        assert_eq!((ran.stderr.as_str(), ran.stdout), ("", want(k)));
    };
    scaling::check(
        "`zedc run` of a fold that swaps two parts of a tuple of n parts",
        N_SWAP,
        run,
    );
}

/// `zedc run` of `[1, 2, 3].foldl((1.5, 0, ..., 0), (a, x) -> (a[1], ..., a[n - 1], a[0]))`
/// with n parts (row PERF-fold-projection-fast-path): the rounds took n + 1 applications of
/// the function, Θ(n²); `fold_projections` reads the rotation's one cycle and the checker
/// applies the function twice, so the check is linear in n. The run takes 3 steps of n parts.
/// Its small instances are `folds::a_rotated_tuple_accumulator_settles_and_runs_at_any_width`.
#[test]
fn a_rotated_tuple_accumulator_checks_in_linear_time() {
    let srcs: HashMap<usize, _> = scaling::inputs(N_SWAP, |k| {
        let start: Vec<&str> = (0..k).map(|i| if i == 0 { "1.5" } else { "0" }).collect();
        let parts: Vec<String> = (0..k).map(|i| format!("a[{}]", (i + 1) % k)).collect();
        program(
            &format!("rotate_{k}"),
            &format!(
                "${{[1, 2, 3].foldl(({}), (a, x) -> ({}))}}",
                start.join(", "),
                parts.join(", ")
            ),
        )
    });
    // Three left rotations move the 1.5 from index 0 to index -3 mod k.
    let want = |k: usize| {
        let at = (3 * (k - 1)) % k;
        let parts: Vec<&str> = (0..k).map(|i| if i == at { "1.5" } else { "0" }).collect();
        format!("({})\n", parts.join(", "))
    };
    let run = |k: usize| {
        let ran = interpreter(&srcs[&k], &[], &[]);
        assert_eq!((ran.stderr.as_str(), ran.stdout), ("", want(k)));
    };
    scaling::check(
        "`zedc run` of a fold that rotates a tuple of n parts",
        N_SWAP,
        run,
    );
}

/// `where(f -> f(0) >= 0)`, which calls each function.
#[test]
fn where_over_a_display_of_functions_runs_in_linear_time() {
    through_display_of_functions("where", "b.where(f -> f(0) >= 0)");
}

/// `as (k -> v) into (k -> v)`.
#[test]
fn a_remap_of_a_display_of_functions_runs_in_linear_time() {
    through_display_of_functions("remap", "b as (k -> v) into (k -> v)");
}
