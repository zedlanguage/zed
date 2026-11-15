//! Benchmarks of step L8.2 (plan row REMAP-run), run apart from the correctness tests
//! (`tools/run_tests.sh --bench`), each at n and 8n: the whole path (parse, check,
//! elaboration and the reference evaluator's run) of `group`, `flatMap`, a transpose, a truncation and
//! folds over n entries, and the checker's collision rule on a pattern of n levels, with
//! literal keys and with an affine tuple key. Their small instances are the cases of `rules`.

use zed_tests::scaling;
use zed_tests::step_helpers::l01_16_elaboration::{elab, value};

/// Entries of a whole-path run.
const N_ENTRIES: usize = 2_000;
/// Levels of a checked pattern.
const N_LEVELS: usize = 100;

/// `[0, 1, …, n-1]`.
fn list(n: usize) -> String {
    let xs = (0..n).map(|x| x.to_string()).collect::<Vec<_>>();
    format!("[{}]", xs.join(", "))
}

/// n entries in rows of 10, `[[0, …, 9], [10, …, 19], …]`.
fn rows(n: usize) -> String {
    let rs = (0..n / 10)
        .map(|r| {
            let xs = (0..10)
                .map(|j| (r * 10 + j).to_string())
                .collect::<Vec<_>>();
            format!("[{}]", xs.join(", "))
        })
        .collect::<Vec<_>>();
    format!("[{}]", rs.join(", "))
}

#[test]
fn group_then_folds_run_in_linear_time() {
    let srcs = scaling::inputs(N_ENTRIES, |n| {
        format!(
            "xs = {};\ng = xs.group(v -> v mod 7);\n\
             t = g as (c -> i -> v) into (c >< (+) -> i >< (+) -> v);\n",
            list(n)
        )
    });
    let run = |n: usize| {
        assert_eq!(value(&srcs[&n], "t"), (n * (n - 1) / 2).to_string());
    };
    scaling::check(
        "`xs.group(v -> v mod 7)` over n entries, then both levels folded, whole path",
        N_ENTRIES,
        run,
    );
}

#[test]
fn flat_map_then_folds_run_in_linear_time() {
    let srcs = scaling::inputs(N_ENTRIES, |n| {
        format!(
            "xs = {};\nf = xs.flatMap(v -> [v, 1]);\n\
             t = f as (i -> j -> v) into (i >< (+) -> j >< (+) -> v);\n",
            list(n)
        )
    });
    let run = |n: usize| {
        assert_eq!(value(&srcs[&n], "t"), (n * (n - 1) / 2 + n).to_string());
    };
    scaling::check(
        "`xs.flatMap(v -> [v, 1])` over n entries, then both levels folded, whole path",
        N_ENTRIES,
        run,
    );
}

#[test]
fn a_transpose_and_a_truncation_run_in_linear_time() {
    let srcs = scaling::inputs(N_ENTRIES, |n| {
        format!(
            "m = {};\nx = m as (i -> j -> v) into (j -> i -> v);\n\
             t = x as (j -> i -> v) into (j >< (+) -> i >< (+) -> v);\n\
             s = m as (i -> j -> v) into (j -> i -> _);\n",
            rows(n)
        )
    });
    let run = |n: usize| {
        assert_eq!(value(&srcs[&n], "t"), (n * (n - 1) / 2).to_string());
        assert!(value(&srcs[&n], "s").starts_with("{0 -> {0, 1, 2"));
    };
    scaling::check(
        "a transpose of n entries in rows of 10, its folds and a truncation, whole path",
        N_ENTRIES,
        run,
    );
}

/// A display nested `n` levels deep, `{0 -> {0 -> … {0 -> 1} … }}`, and the binders
/// `k0 -> … -> k(n-1) -> v`.
fn deep(n: usize) -> (String, String) {
    let display = format!("{}1{}", "{0 -> ".repeat(n), "}".repeat(n));
    let binders = (0..n)
        .map(|i| format!("k{i}"))
        .collect::<Vec<_>>()
        .join(" -> ");
    (display, format!("{binders} -> v"))
}

#[test]
fn the_collision_rule_on_n_literal_levels_takes_linear_time() {
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let (display, binders) = deep(n);
        let rev = (0..n)
            .rev()
            .map(|i| format!("k{i}"))
            .collect::<Vec<_>>()
            .join(" -> ");
        format!("m = {display};\nx = m as ({binders}) into ({rev} -> v);\n")
    });
    let run = |n: usize| assert!(elab(&srcs[&n]).is_ok(), "{}", &srcs[&n]);
    scaling::check(
        "the check of a remap reversing n levels, keys written as binders",
        N_LEVELS,
        run,
    );
}

#[test]
fn the_collision_rule_on_an_affine_key_of_n_components() {
    // The tuple `(k0 + k1, k1 + k2, …, k(n-1))`: triangular, so of full column rank, read by
    // the catalog's affine entry.
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let (display, binders) = deep(n);
        let comps = (0..n)
            .map(|i| match i + 1 < n {
                true => format!("k{i} + k{}", i + 1),
                false => format!("k{i}"),
            })
            .collect::<Vec<_>>()
            .join(", ");
        format!("m = {display};\nx = m as ({binders}) into (({comps}) -> v);\n")
    });
    let run = |n: usize| assert!(elab(&srcs[&n]).is_ok(), "{}", &srcs[&n]);
    scaling::check(
        "the check of a remap to an affine tuple key of n components over n levels",
        N_LEVELS,
        run,
    );
}

#[test]
fn a_remap_and_a_group_of_a_map_lambdas_parameter_run_in_linear_time() {
    // Each row of `m` is the lambda's parameter `g`: the remap and the group are checked once,
    // at the type of the rows, and run once per row.
    let srcs = scaling::inputs(N_ENTRIES, |n| {
        format!(
            "m = {};\nx = m.map(g -> g as (k -> v) into (k + 1 -> v));\n\
             t = x as (i -> j -> v) into (i >< (+) -> j >< (+) -> v);\n\
             y = m.map(g -> g.group(v -> v mod 7));\n\
             u = y as (i -> c -> j -> v) into (i >< (+) -> c >< (+) -> j >< (+) -> v);\n",
            rows(n)
        )
    });
    let run = |n: usize| {
        let sum = (n * (n - 1) / 2).to_string();
        assert_eq!(value(&srcs[&n], "t"), sum);
        assert_eq!(value(&srcs[&n], "u"), sum);
    };
    scaling::check(
        "a remap and a group of a `map` lambda's parameter over n entries in rows of 10, \
         whole path",
        N_ENTRIES,
        run,
    );
}

#[test]
fn n_calls_of_a_generic_remap_are_checked_in_linear_time() {
    // Each call passes a family of another key type, so the remap is checked once per call.
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let calls = (0..n)
            .map(|i| format!("x{i} = f(g: {{ {i} -> 1 }});\n"))
            .collect::<String>();
        format!("f(g) = g as (k -> v) into (k + 1 -> v);\n{calls}")
    });
    let run = |n: usize| {
        let u = elab(&srcs[&n]).unwrap_or_else(|e| panic!("{e:?}"));
        assert!(u.get(&format!("x{}", n - 1)).is_some());
    };
    scaling::check(
        "n calls of a generic function that remaps its parameter",
        N_LEVELS,
        run,
    );
}

#[test]
fn a_remap_of_a_map_lambdas_parameter_below_a_known_level_runs_in_linear_time() {
    // `r` is a class below the key level of `{ 0 -> r }`: the remap is checked once, when the
    // rows' type flows into `r`, and runs once per row.
    let srcs = scaling::inputs(N_ENTRIES, |n| {
        format!(
            "m = {};\nx = m.map(r -> ({{ 0 -> r }}) as (a -> k -> v) into (k -> a -> v));\n\
             t = x as (i -> k -> a -> v) into (i >< (+) -> k >< (+) -> a >< (+) -> v);\n",
            rows(n)
        )
    });
    let run = |n: usize| {
        assert_eq!(value(&srcs[&n], "t"), (n * (n - 1) / 2).to_string());
    };
    scaling::check(
        "a remap of `{ 0 -> r }`, `r` a `map` lambda's parameter, over n entries in rows of \
         10, whole path",
        N_ENTRIES,
        run,
    );
}

#[test]
fn n_calls_of_a_generic_remap_below_a_known_level_are_checked_in_linear_time() {
    // Each call passes a family of another key type, so the remap is checked once per call.
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let calls = (0..n)
            .map(|i| format!("x{i} = f(g: {{ {i} -> 1 }});\n"))
            .collect::<String>();
        format!("f(g) = ({{ 0 -> g }}) as (a -> k -> v) into (k -> a -> v);\n{calls}")
    });
    let run = |n: usize| {
        let u = elab(&srcs[&n]).unwrap_or_else(|e| panic!("{e:?}"));
        assert!(u.get(&format!("x{}", n - 1)).is_some());
    };
    scaling::check(
        "n calls of a generic function that remaps `{ 0 -> g }`, `g` its parameter",
        N_LEVELS,
        run,
    );
}
