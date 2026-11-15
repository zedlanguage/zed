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

#[test]
fn a_generic_sum_of_a_map_lambdas_parameter_runs_in_linear_time() {
    // `.sum` on the type parameter of `s` is decided at its one call, on the rows of `m`, and
    // runs once per row (row FAIL-generic-sum-method).
    let srcs = scaling::inputs(N_ENTRIES, |n| {
        format!(
            "s(positional xs) = xs.sum;\nm = {};\nx = m.map(r -> s(r));\nt = x >< (+);\n",
            rows(n)
        )
    });
    let run = |n: usize| {
        assert_eq!(value(&srcs[&n], "t"), (n * (n - 1) / 2).to_string());
    };
    scaling::check(
        "a generic `.sum` of each row of n entries in rows of 10, whole path",
        N_ENTRIES,
        run,
    );
}

#[test]
fn n_calls_of_a_generic_sum_on_families_and_tuples_are_checked_in_linear_time() {
    // Each call passes a family of another key type or a tuple, so `.sum` is decided once per
    // call (row FAIL-generic-sum-method).
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let calls = (0..n)
            .map(|i| match i % 2 {
                0 => format!("x{i} = s({{ {i} -> 1 }});\n"),
                _ => format!("x{i} = s(({i}, 1));\n"),
            })
            .collect::<String>();
        format!("s(positional xs) = xs.sum;\n{calls}")
    });
    let run = |n: usize| {
        let u = elab(&srcs[&n]).unwrap_or_else(|e| panic!("{e:?}"));
        assert!(u.get(&format!("x{}", n - 1)).is_some());
    };
    scaling::check(
        "n calls of a generic function that sums its parameter, a family or a tuple",
        N_LEVELS,
        run,
    );
}

#[test]
fn n_calls_of_a_generic_sum_written_as_a_call_on_a_union_are_checked_in_linear_time() {
    // `sum(x)` with `x` a parameter beside a tuple: each call is summed region by region, the
    // family by the fold and the tuple by adding (row FAIL-sum-word-family).
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let calls = (0..n)
            .map(|i| match i % 2 {
                0 => format!("x{i} = s({{ {i} -> 1 }}, true);\n"),
                _ => format!("x{i} = s(({i}, 1), false);\n"),
            })
            .collect::<String>();
        format!("s(positional xs, positional b) = sum(if b {{ xs }} else {{ (1, 2) }});\n{calls}")
    });
    let run = |n: usize| {
        let u = elab(&srcs[&n]).unwrap_or_else(|e| panic!("{e:?}"));
        assert!(u.get(&format!("x{}", n - 1)).is_some());
    };
    scaling::check(
        "n calls of a generic function whose `sum(x)` takes a parameter beside a tuple",
        N_LEVELS,
        run,
    );
}

#[test]
fn n_calls_of_a_generic_sum_beside_an_empty_family_run_in_linear_time() {
    // `[]` beside the parameter is summed with what each call passes: a tuple, where it folds
    // to `#empty`, an `int` family (`0`) or an `f64` family (`-0.0`), so the fold has three
    // bodies and each call takes one (row FAIL-sum-empty-family-beside-parameter).
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let calls = (0..n)
            .map(|i| match i % 3 {
                0 => format!("x{i} = s(({i}, 1), false);\n"),
                1 => format!("x{i} = s([{i}, 1], false);\n"),
                _ => format!("x{i} = s([{i}.5], false);\n"),
            })
            .collect::<String>();
        let last = format!("t = (x0, x1, x2, x{});\n", n - 1);
        format!(
            "s(positional xs, positional b) = (if b {{ xs }} else {{ [] }}).sum;\n{calls}{last}"
        )
    });
    let run = |n: usize| {
        let want = match (n - 1) % 3 {
            0 => "#empty",
            1 => "0",
            _ => "-0.0",
        };
        assert_eq!(value(&srcs[&n], "t"), format!("(#empty, 0, -0.0, {want})"));
    };
    scaling::check(
        "n calls of a generic `.sum` of a parameter beside `[]`, at a tuple, `int` and `f64`, \
         whole path",
        N_LEVELS,
        run,
    );
}

/// The leaves `leaves` joined by a balanced tree of `if`s, the k-th `if` met on the way down
/// testing its own parameter `ck`: every leaf is reachable, and the tree is about log n deep.
fn if_tree(leaves: &[String], next: &mut usize) -> String {
    match leaves {
        [one] => one.clone(),
        _ => {
            let k = *next;
            *next += 1;
            let (l, r) = leaves.split_at(leaves.len() / 2);
            let (l, r) = (if_tree(l, next), if_tree(r, next));
            format!("if c{k} {{ {l} }} else {{ {r} }}")
        }
    }
}

/// A generic function `s` of n family parameters `x0` … and n conditions `c0` … whose body is
/// `x0`, …, `x(n-1)` and `[1, 2]` joined by [`if_tree`] and then `tail`, and the call that
/// passes `[i, 1]` as `xi` and `false` as each condition, which takes the last leaf, `[1, 2]`.
fn joined_parameters(n: usize, tail: &str) -> String {
    let mut leaves = (0..n).map(|i| format!("x{i}")).collect::<Vec<_>>();
    leaves.push("[1, 2]".to_string());
    let recv = if_tree(&leaves, &mut 0);
    let params = (0..n)
        .map(|i| format!("positional x{i}, positional c{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let args = (0..n)
        .map(|i| format!("[{i}, 1], false"))
        .collect::<Vec<_>>()
        .join(", ");
    format!("s({params}) = ({recv}){tail};\nt = s({args});\n")
}

#[test]
fn a_fold_of_n_joined_parameters_is_checked_in_linear_time() {
    // The receiver of `.sum` and of `>< (+)` is n type parameters joined with a family, and
    // each parameter takes one need, met at the one call with n families (row
    // TEST-generic-sum-branches). The `if`s form a balanced tree, each with its own condition:
    // under one shared condition every inner `then` branch is known not to run and is
    // dropped, and a chain of n `if`s over n parameters is checked in quadratic time before
    // any fold (row FAIL-if-chain-params-quadratic).
    let srcs = scaling::inputs(N_LEVELS, |n| {
        (
            joined_parameters(n, ".sum"),
            joined_parameters(n, " >< (+)"),
        )
    });
    let run = |n: usize| {
        assert_eq!(value(&srcs[&n].0, "t"), "3");
        assert_eq!(value(&srcs[&n].1, "t"), "3");
    };
    scaling::check(
        "a `.sum` and a `><` of n type parameters joined with a family, one call each",
        N_LEVELS,
        run,
    );
}

#[test]
fn a_chain_of_n_ifs_over_n_parameters_is_checked_in_n_log_n_time() {
    // The body is `if b0 { x0 } else { if b1 { x1 } else { … [1, 2] } }`, n deep, each `if`
    // with its own condition and type parameter, and no fold (row
    // FAIL-if-chain-params-quadratic: 30.1 times from n = 100 to 800 before the fix).
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let params = (0..n)
            .map(|i| format!("positional x{i}, positional b{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let recv = (0..n).fold("[1, 2]".to_string(), |acc, i| {
            format!("if b{i} {{ x{i} }} else {{ {acc} }}")
        });
        let args = (0..n)
            .map(|i| format!("[{i}, 1], false"))
            .collect::<Vec<_>>()
            .join(", ");
        format!("s({params}) = ({recv});\nt = s({args});\n")
    });
    let run = |n: usize| {
        assert_eq!(value(&srcs[&n], "t"), "{0 -> 1, 1 -> 2}");
    };
    scaling::check(
        "a chain of n `if`s over n type parameters, one call",
        N_LEVELS,
        run,
    );
}

/// `mi` and `m`: one family of an empty `int` level and one entry, and its `f64` twin.
const EMPTY_LEVELS: &str = "mi = { \"a\" -> [1], \"b\" -> [5] }.map(r -> r.where(v -> v > 3));\n\
                            m = { \"a\" -> [1.0], \"b\" -> [5.0] }.map(r -> r.where(v -> v > 3.0));\n";

#[test]
fn n_calls_of_a_generic_fold_at_two_carriers_run_in_linear_time() {
    // The calls alternate `int` and `f64`, so `top` has two bodies, one per identity, and each
    // call takes one of them (row REDUCE-generic-identity).
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let calls = (0..n)
            .map(|i| match i % 2 {
                0 => format!("x{i} = mi.map(r -> top(r));\n"),
                _ => format!("x{i} = m.map(r -> top(r));\n"),
            })
            .collect::<String>();
        format!("top(positional xs) = xs >< max;\n{EMPTY_LEVELS}{calls}")
    });
    let run = |n: usize| {
        let last = value(&srcs[&n], &format!("x{}", n - 1));
        assert_eq!(last, "{\"a\" -> -inf, \"b\" -> 5.0}");
    };
    scaling::check(
        "n `.map` calls of a generic `max` fold, alternately at `int` and `f64`, whole path",
        N_LEVELS,
        run,
    );
}

#[test]
fn a_chain_of_n_generic_functions_over_a_map_of_a_fold_runs_in_linear_time() {
    // The fold's need waits in `g0`'s `.map` lambda, and each `g{i}` passes it on, so the
    // checker searches each signature's needs, nested ones too, and each function has two
    // bodies, at `int` and at `f64` (row REDUCE-generic-identity).
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let chain = (1..n)
            .map(|i| format!("g{i}(positional mm) = g{}(mm);\n", i - 1))
            .collect::<String>();
        format!(
            "top(positional xs) = xs >< max;\n{EMPTY_LEVELS}\
             g0(positional mm) = mm.map(r -> top(r));\n{chain}a = (g{0}(mi), g{0}(m));\n",
            n - 1
        )
    });
    let run = |n: usize| {
        assert_eq!(
            value(&srcs[&n], "a"),
            "({\"a\" -> #empty, \"b\" -> 5}, {\"a\" -> -inf, \"b\" -> 5.0})"
        );
    };
    scaling::check(
        "a chain of n generic functions, the first mapping a `max` fold, called at `int` and \
         `f64`, whole path",
        N_LEVELS,
        run,
    );
}

#[test]
fn a_chain_of_n_functions_declared_in_a_block_over_a_fold_runs_in_linear_time() {
    // Each `h{i}` calls the one before it, so each has two bodies, at `int` and at `f64`,
    // made and bound in the block when it ends (row REDUCE-generic-identity-rest).
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let chain = (1..n)
            .map(|i| format!("h{i}(positional q) = h{}(q);\n", i - 1))
            .collect::<String>();
        format!(
            "top(positional xs) = xs >< max;\n{EMPTY_LEVELS}\
             a = {{\nh0(positional q) = top(q);\n{chain}(h{0}(mi[\"a\"]), h{0}(m[\"a\"])) }};\n",
            n - 1
        )
    });
    let run = |n: usize| {
        assert_eq!(value(&srcs[&n], "a"), "(#empty, -inf)");
    };
    scaling::check(
        "a chain of n functions declared in one block, the first a `max` fold, called at `int` \
         and `f64`, whole path",
        N_LEVELS,
        run,
    );
}
