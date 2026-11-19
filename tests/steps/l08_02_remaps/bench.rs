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

/// `if c0 { v0 } else if c1 { v1 } … else { last }`, the `n` arms `arm(i) = (ci, vi)`: an
/// `else if` chain of `n` links (row BENCH-if-chain-other-paths).
fn else_if_chain(n: usize, arm: impl Fn(usize) -> (String, String), last: &str) -> String {
    let links = (0..n)
        .map(|i| {
            let (c, v) = arm(i);
            format!("if {c} {{ {v} }} else ")
        })
        .collect::<String>();
    format!("{links}{{ {last} }}")
}

/// Checks that `src(n)`, a program whose `t` is `want(n)`, is checked and run in O(n log n)
/// at n and 8n `else if` links.
fn chain_scales(what: &str, src: impl Fn(usize) -> String, want: impl Fn(usize) -> String) {
    let srcs = scaling::inputs(N_LEVELS, |n| (src(n), want(n)));
    scaling::check(what, N_LEVELS, |n: usize| {
        let (src, want) = &srcs[&n];
        assert_eq!(&value(src, "t"), want);
    });
}

#[test]
fn an_else_if_chain_of_n_less_than_tests_on_one_integer_is_checked_in_n_log_n_time() {
    // Each `else` narrows `x` to `x >= i + 1`; the call takes the last arm but one.
    chain_scales(
        "an `else if` chain of n tests `x < i` on one `int` parameter, one call",
        |n| {
            let body = else_if_chain(n, |i| (format!("x < {}", i + 1), i.to_string()), "-1");
            format!("f(positional x: int) = {body};\nt = f({});\n", n - 1)
        },
        |n| (n - 1).to_string(),
    );
}

#[test]
fn an_else_if_chain_of_n_equality_tests_on_one_integer_is_checked_in_n_log_n_time() {
    // Each `else` puts one more hole in `x`, `x != i`, so the `else` at depth k holds k holes.
    chain_scales(
        "an `else if` chain of n tests `x == i` on one `int` parameter, one call",
        |n| {
            let body = else_if_chain(n, |i| (format!("x == {i}"), i.to_string()), "-1");
            format!("f(positional x: int) = {body};\nt = f({});\n", n - 1)
        },
        |n| (n - 1).to_string(),
    );
}

#[test]
fn an_else_if_chain_of_n_tests_on_n_integers_is_checked_in_n_log_n_time() {
    // Each link tests its own parameter, `xi > 0`; only the last is 1.
    chain_scales(
        "an `else if` chain of n tests `xi > 0`, one per `int` parameter, one call",
        |n| {
            let params = (0..n)
                .map(|i| format!("positional x{i}: int"))
                .collect::<Vec<_>>()
                .join(", ");
            let body = else_if_chain(n, |i| (format!("x{i} > 0"), i.to_string()), "-1");
            let args = (0..n)
                .map(|i| if i + 1 == n { "1" } else { "0" })
                .collect::<Vec<_>>()
                .join(", ");
            format!("g({params}) = {body};\nt = g({args});\n")
        },
        |n| (n - 1).to_string(),
    );
}

#[test]
fn an_else_if_chain_of_n_tests_on_the_atoms_of_a_union_is_checked_in_n_log_n_time() {
    // `v` is one of n + 1 atoms; each link takes one away, so the `else` at depth k is a union
    // of n + 1 - k atoms.
    chain_scales(
        "an `else if` chain of n tests `v is #ai` on a union of n + 1 atoms, one call",
        |n| {
            let union = (0..=n)
                .map(|i| format!("#a{i}"))
                .collect::<Vec<_>>()
                .join(" | ");
            let body = else_if_chain(n, |i| (format!("v is #a{i}"), i.to_string()), "-1");
            format!("h(positional v: {union}) = {body};\nt = h(#a{});\n", n - 1)
        },
        |n| (n - 1).to_string(),
    );
}

#[test]
fn an_else_if_chain_of_n_tests_with_a_fold_inside_is_checked_in_n_log_n_time() {
    // Each condition folds the list parameter, `xs >< (+) < i + 1`.
    chain_scales(
        "an `else if` chain of n tests `xs >< (+) < i` on one list parameter, one call",
        |n| {
            let body = else_if_chain(
                n,
                |i| (format!("xs >< (+) < {}", i + 1), i.to_string()),
                "-1",
            );
            format!("k(positional xs) = {body};\nt = k([{}, 0]);\n", n - 1)
        },
        |n| (n - 1).to_string(),
    );
}

#[test]
fn an_else_if_chain_returning_n_different_types_is_checked_in_n_log_n_time() {
    // The arm at link i returns the atom `#ri`, so the chain's type is a union of n + 1 atoms,
    // and the `else` type at depth k is a union of n + 1 - k of them. Each `if` asks whether
    // one arm's type is a subtype of the other's; that difference complemented every atom
    // the result so far lists, Θ(n²) in all, 25.2 times the instructions at 100 and 800
    // links, until `Atoms::minus` (COMPLEXITY.md K119).
    chain_scales(
        "an `else if` chain of n links each returning its own atom, one call",
        |n| {
            let body = else_if_chain(n, |i| (format!("c == {i}"), format!("#r{i}")), "#none");
            format!("r(positional c: int) = {body};\nt = r({});\n", n - 1)
        },
        |n| format!("#r{}", n - 1),
    );
}

/// `mi` and `m`: one family of an empty `int` level and one entry, and its `f64` twin.
const EMPTY_LEVELS: &str = "mi = { \"a\" -> [1], \"b\" -> [5] }.map(r -> r.where(v -> v > 3));\n\
                            m = { \"a\" -> [1.0], \"b\" -> [5.0] }.map(r -> r.where(v -> v > 3.0));\n";

#[test]
fn n_functions_calls_return_run_in_linear_time() {
    // Each `p{i}` is a call that runs the lambda it is passed and returns it; `d{i}` runs the
    // returned lambda at the same carrier, compiled, and `r{i}` at the other one, refused
    // (row REDUCE-identity-escaping-values).
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let uses = (0..n)
            .map(|i| {
                format!("p{i} = h3(x -> top(x), m[\"a\"]);\nd{i} = (p{i}[0], p{i}[1](m[\"b\"]));\n")
            })
            .collect::<String>();
        format!(
            "top(positional xs) = xs >< max;\n{EMPTY_LEVELS}\
             h3(positional f, positional y) = (f(y), f);\n{uses}"
        )
    });
    let run = |n: usize| assert_eq!(value(&srcs[&n], &format!("d{}", n - 1)), "(-inf, 5.0)");
    scaling::check(
        "n calls returning the lambda they run, each run again at the same carrier, whole path",
        N_LEVELS,
        run,
    );
    let refused = scaling::inputs(N_LEVELS, |n| {
        let uses = (0..n)
            .map(|i| format!("p{i} = h3(x -> x >< max, m[\"a\"]);\nr{i} = p{i}[1](mi[\"a\"]);\n"))
            .collect::<String>();
        format!("{EMPTY_LEVELS}h3(positional f, positional y) = (f(y), f);\n{uses}")
    });
    let run = |n: usize| {
        let errs = elab(&refused[&n]).expect_err("each fold runs at two carriers");
        assert_eq!(errs.len(), n, "{errs:?}");
    };
    scaling::check(
        "n calls returning the lambda they run, each run again at another carrier, refused",
        N_LEVELS,
        run,
    );
}

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

/// The one-level words on a generic function's parameter, each a need met at each call
/// (plan row FP-ops-generic-receivers).
const WORDS: &str = "w(positional xs) = (xs.count, xs.first, xs.last, xs.any(x -> x > 1), \
                     xs.all(x -> x > 0), xs.find(x -> x > 1), xs.scan(max).last, \
                     xs.chunkBy(x -> x).count);\n";

#[test]
fn n_calls_of_a_generic_function_of_the_one_level_words_run_in_linear_time() {
    // The calls alternate a list of `int` and a keyed display of `f64`, so each word's need is
    // checked on another family type at each call (plan row FP-ops-generic-receivers).
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let calls = (0..n)
            .map(|i| match i % 2 {
                0 => format!("x{i} = w([{i}, 2]);\n"),
                _ => format!("x{i} = w({{\"a\" -> {i}.5, \"b\" -> 0.5}});\n"),
            })
            .collect::<String>();
        format!("{WORDS}{calls}")
    });
    let run = |n: usize| {
        let i = n - 1;
        assert_eq!(
            value(&srcs[&n], &format!("x{i}")),
            format!("(2, {i}.5, 0.5, true, true, \"a\", {i}.5, 2)")
        );
    };
    scaling::check(
        "n calls of a generic function of `count`, `first`, `last`, `any`, `all`, `find`, \
         `scan` and `chunkBy`, alternately on a list and a keyed display, whole path",
        N_LEVELS,
        run,
    );
}

#[test]
fn a_chain_of_n_generic_functions_passing_on_the_one_level_words_runs_in_linear_time() {
    // `w`'s needs wait on `g0`'s parameter, and each `g{i}` passes them on, so they are
    // checked once at each of the two calls at the chain's top (plan row
    // FP-ops-generic-receivers).
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let chain = (1..n)
            .map(|i| format!("g{i}(positional mm) = g{}(mm);\n", i - 1))
            .collect::<String>();
        format!(
            "{WORDS}g0(positional mm) = w(mm);\n{chain}a = (g{0}([3, 2]), g{0}({{\"a\" -> 1.5}}));\n",
            n - 1
        )
    });
    let run = |n: usize| {
        assert_eq!(
            value(&srcs[&n], "a"),
            "((2, 3, 2, true, true, 0, 3, 2), (1, 1.5, 1.5, true, true, \"a\", 1.5, 1))"
        );
    };
    scaling::check(
        "a chain of n generic functions passing a list and a keyed display to one of the \
         one-level words, whole path",
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

#[test]
fn n_blocks_that_each_drop_a_written_body_run_in_linear_time() {
    // Each `a{i}` declares `h` and calls it at `int` and `f64` by name only, so each of the n
    // written bodies is dropped, and the search for a kept term naming one
    // (`Elab::check_dropped`, row PROOF-block-body-kept-when-named) reads every definition.
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let blocks = (0..n)
            .map(|i| {
                format!("a{i} = {{ h(positional q) = top(q); (h(mi[\"a\"]), h(m[\"a\"])) }};\n")
            })
            .collect::<String>();
        format!("top(positional xs) = xs >< max;\n{EMPTY_LEVELS}{blocks}")
    });
    let run = |n: usize| {
        assert_eq!(value(&srcs[&n], &format!("a{}", n - 1)), "(#empty, -inf)");
    };
    scaling::check(
        "n blocks, each declaring a `max` fold's function called at `int` and `f64` by name, \
         whole path",
        N_LEVELS,
        run,
    );
}

#[test]
fn n_function_values_called_at_two_carriers_run_in_linear_time() {
    // Each `t{i}` is an alias of `top`, called at `int` and `f64`, and each `e{i}` passes `top`
    // to `ap`, so each call through a value runs the body made at its own identity (row
    // REDUCE-generic-identity-values, form 1).
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let uses = (0..n)
            .map(|i| {
                format!(
                    "t{i} = top;\nd{i} = (t{i}(mi[\"a\"]), t{i}(m[\"a\"]));\n\
                     e{i} = (ap(top, mi[\"a\"]), ap(top, m[\"a\"]));\n"
                )
            })
            .collect::<String>();
        format!(
            "top(positional xs) = xs >< max;\n{EMPTY_LEVELS}\
             ap(positional f, positional x) = f(x);\n{uses}"
        )
    });
    let run = |n: usize| {
        let src = &srcs[&n];
        assert_eq!(value(src, &format!("d{}", n - 1)), "(#empty, -inf)");
        assert_eq!(value(src, &format!("e{}", n - 1)), "(#empty, -inf)");
    };
    scaling::check(
        "n aliases of a generic `max` fold and n passings of it to a function, each called at \
         `int` and `f64`, whole path",
        N_LEVELS,
        run,
    );
}

#[test]
fn n_folds_read_under_two_identities_run_in_linear_time() {
    // Each `x{i}` reads `top(q)` of the outer `.map`'s `int` row inside the inner `.map` at
    // `f64`, so one read is in force under both identities (row
    // REDUCE-generic-identity-values, form 2), and the repeated `top(q)` is one need of one
    // class (`Ck::same_use`).
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let uses = (0..n)
            .map(|i| format!("x{i} = mi.map(q -> (top(q), m.map(r -> (top(r), top(q)))));\n"))
            .collect::<String>();
        format!("top(positional xs) = xs >< max;\n{EMPTY_LEVELS}{uses}")
    });
    let run = |n: usize| {
        assert_eq!(
            value(&srcs[&n], &format!("x{}", n - 1)),
            "{\"a\" -> (#empty, {\"a\" -> (-inf, #empty), \"b\" -> (5.0, #empty)}), \
             \"b\" -> (5, {\"a\" -> (-inf, 5), \"b\" -> (5.0, 5)})}"
        );
    };
    scaling::check(
        "n `.map` calls at `int`, each reading a `max` fold of its row inside a `.map` at \
         `f64`, whole path",
        N_LEVELS,
        run,
    );
}

/// Levels of a nest of `.map` calls: at 50 and 400 a search of the calls in force at each
/// read measured 10.6x, against 8.7x at 25 and 200.
const N_NEST: usize = 50;

#[test]
fn a_nest_of_n_maps_each_reading_a_fold_runs_in_linear_time() {
    // `.map` calls nested n deep, alternately over a one-entry `int` and `f64` family, each
    // lambda reading `top` of its own row and of the row of the `.map` around it: at depth i,
    // i calls that decide `top`'s fold are in force (`Instancing::pushed`), and each read takes
    // the identity of the one that checked it (row REDUCE-generic-identity-values, form 2).
    let srcs = scaling::inputs(N_NEST, |n| {
        let mut body = String::from("0");
        for i in (0..n).rev() {
            let (fam, outer) = match (i % 2, i) {
                (0, 0) => ("ni", "0".to_string()),
                (0, _) => ("ni", format!("top(q{})", i - 1)),
                (_, _) => ("nf", format!("top(q{})", i - 1)),
            };
            body = format!("{fam}.map(q{i} -> (top(q{i}), {outer}, {body}))");
        }
        format!(
            "top(positional xs) = xs >< max;\n\
             ni = {{ \"a\" -> [5] }}.map(r -> r.where(v -> v > 3));\n\
             nf = {{ \"a\" -> [1.0] }}.map(r -> r.where(v -> v > 3.0));\n\
             x = {body};\n"
        )
    });
    let run = |n: usize| {
        let x = value(&srcs[&n], "x");
        // Level 0 reads `int`'s 5 and gives `0` for the row around; each odd level reads
        // `f64`'s `-inf` of its row and 5 of the `int` row around, each even one the reverse.
        assert!(x.starts_with("{\"a\" -> (5, 0, "), "{x}");
        assert_eq!(x.matches("(-inf, 5, ").count(), n / 2, "{x}");
        assert_eq!(x.matches("(5, -inf, ").count(), (n - 1) / 2, "{x}");
    };
    scaling::check(
        "`.map` calls nested n deep over one-entry `int` and `f64` families, each reading a \
         `max` fold of its row and of the row around, whole path",
        N_NEST,
        run,
    );
}

#[test]
fn n_generic_functions_with_a_fold_in_a_tuple_member_run_in_linear_time() {
    // Each `g{i}` returns a tuple whose second member is a `.map` of a fold at `f64` while its
    // first is a fold at the call's carrier, so `split_needs` searches the tuple's members
    // (row REDUCE-generic-identity-values, form 3).
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let uses = (0..n)
            .map(|i| {
                format!(
                    "g{i}(positional ys) = (top(ys), m.map(r -> top(r)));\n\
                     x{i} = g{i}(mi[\"a\"]);\n"
                )
            })
            .collect::<String>();
        format!("top(positional xs) = xs >< max;\n{EMPTY_LEVELS}{uses}")
    });
    let run = |n: usize| {
        assert_eq!(
            value(&srcs[&n], &format!("x{}", n - 1)),
            "(#empty, {\"a\" -> -inf, \"b\" -> 5.0})"
        );
    };
    scaling::check(
        "n generic functions, each returning a `max` fold and a `.map` of one in a tuple, \
         called at `int`, whole path",
        N_LEVELS,
        run,
    );
}

#[test]
fn n_partial_map_parameters_with_a_ranged_key_passed_on_take_linear_time() {
    // `pass0` remaps its `m: int[0..<n] ->? int` by `k mod n`, which the modulo witness accepts
    // from the range; `pass1` … `pass{n-1}` each pass their own `m` on, and one call passes a family
    // of n keys (row RANGE-keys): n containments of a written range in another and one check of
    // n listed keys, and the run of the remap over n entries.
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let mut src = format!(
            "pass0(positional m: int[0..<{n}] ->? int) = m as (k -> v) into (k mod {n} -> v);\n"
        );
        for i in 1..n {
            src += &format!(
                "pass{i}(positional m: int[0..<{n}] ->? int) = pass{}(m);\n",
                i - 1
            );
        }
        // Each value differs from its key, or the display would print as a set.
        let entries = (0..n)
            .map(|k| format!("{k} -> {}", k + 1))
            .collect::<Vec<_>>();
        src += &format!("x = pass{}({{ {} }});\n", n - 1, entries.join(", "));
        src
    });
    let run = |n: usize| {
        let x = value(&srcs[&n], "x");
        assert!(x.starts_with("{0 -> 1, 1 -> 2, "), "{x}");
        assert!(x.ends_with(&format!("{} -> {n}}}", n - 1)), "{x}");
    };
    scaling::check(
        "n functions passing on a partial map whose key has a range, the first remapping it \
         by `k mod n`, called once with n keys, whole path",
        N_LEVELS,
        run,
    );
}

#[test]
fn n_lambdas_that_call_a_parameter_in_a_returned_tuple_run_in_linear_time() {
    // Each of `h`'s n lambdas calls `f`, so the call `h(x -> x + 1)` defers n needs and joins
    // each to its lambda (`hold` in crates/zedc-check/src/check/mod.rs; row
    // FAIL-tuple-lambda-calls-param). Small instances:
    // `empty::a_tuple_holding_a_lambda_that_calls_a_parameter_runs`.
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let lambdas = (0..n)
            .map(|i| format!("z -> f(z) + {i}"))
            .collect::<Vec<_>>();
        format!(
            "h(positional f) = ({});\na = {{ p = h(x -> x + 1); p[{}](1) }};\n",
            lambdas.join(", "),
            n - 1
        )
    });
    let run = |n: usize| assert_eq!(value(&srcs[&n], "a"), (n + 1).to_string());
    scaling::check(
        "n lambdas that call a parameter, returned in one tuple and one of them run, whole path",
        N_LEVELS,
        run,
    );
}

#[test]
fn a_lambda_that_calls_a_parameter_n_tuples_deep_runs_in_linear_time() {
    // The call walks the n rows above the lambda once to defer its need and once to join it
    // (`Ty::each_held_fn`, `Ty::with_held_fns`).
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let deep = (0..n).fold("z -> f(z)".to_string(), |t, _| format!("(0, {t})"));
        let path = "[1]".repeat(n);
        format!("h(positional f) = {deep};\na = {{ p = h(x -> x + 1); p{path}(2) }};\n")
    });
    let run = |n: usize| assert_eq!(value(&srcs[&n], "a"), "3");
    scaling::check(
        "a lambda that calls a parameter, n tuples deep in the result, run, whole path",
        N_LEVELS,
        run,
    );
}

#[test]
fn n_lambdas_that_call_a_parameter_in_a_returned_family_run_in_linear_time() {
    // The family's n entries each hold a lambda that calls `f`; the call enters the family
    // once (`Ty::each_held_fn`, `Ty::with_held_fns`) and joins each need to its lambda (row
    // FAIL-family-lambda-calls-param). Small instances:
    // `empty::a_family_holding_a_lambda_that_calls_a_parameter_runs`.
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let entries = (0..n)
            .map(|i| format!("\"k{i}\" -> (z -> f(z) + {i})"))
            .collect::<Vec<_>>();
        format!(
            "h(positional f) = {{{}}};\na = {{ p = h(x -> x + 1); p[\"k{}\"](1) }};\n",
            entries.join(", "),
            n - 1
        )
    });
    let run = |n: usize| assert_eq!(value(&srcs[&n], "a"), (n + 1).to_string());
    scaling::check(
        "n lambdas that call a parameter, returned in one family and one of them run, whole path",
        N_LEVELS,
        run,
    );
}

/// Row FAIL-map-generic-parameter-function: `group` by a parameter with no written type, over
/// n entries: one need "`f` takes the entries" on `f`'s class, met once at the call, and the
/// kernel's reindex over the n entries. Small instances:
/// `empty::the_words_that_take_a_function_take_a_function_parameter`.
#[test]
fn group_by_a_function_parameter_runs_in_linear_time() {
    let srcs = scaling::inputs(N_ENTRIES, |n| {
        format!(
            "g(positional f) = {}.group(f);\na = g(v -> v mod 7).count;\n",
            list(n)
        )
    });
    let run = |n: usize| assert_eq!(value(&srcs[&n], "a"), "7");
    scaling::check(
        "group of n entries by a function parameter, whole path",
        N_ENTRIES,
        run,
    );
}

/// Row FAIL-fold-unknown-fn-known-family: `foldl` over a list of n entries by a parameter with
/// no written type: one need NeedKind::Fold on `f`'s class, met once at the call, where the
/// accumulator is found and the kernel folds the n entries. Small instances:
/// `empty::a_fold_over_a_known_family_by_a_function_parameter_runs`.
#[test]
fn fold_of_a_known_family_by_a_function_parameter_runs_in_linear_time() {
    let srcs = scaling::inputs(N_ENTRIES, |n| {
        format!(
            "h(positional f) = {}.foldl(0, f);\na = h((a, x) -> a + x);\n",
            list(n)
        )
    });
    let run = |n: usize| assert_eq!(value(&srcs[&n], "a"), (n * (n - 1) / 2).to_string());
    scaling::check(
        "foldl of n entries by a function parameter, whole path",
        N_ENTRIES,
        run,
    );
}

/// Row FAIL-map-lambda-calls-param-entry: `map` of a parameter `m` holding n entries by a
/// lambda that calls a parameter `f`: the need "the entries of `m`", recorded before the
/// lambda, is met once at the call, and so is the call of `f` on them; the kernel maps the n
/// entries. Small instances: `empty::map_of_a_parameter_by_a_lambda_calling_a_parameter_runs`.
#[test]
fn map_of_a_parameter_by_a_lambda_calling_a_parameter_runs_in_linear_time() {
    let srcs = scaling::inputs(N_ENTRIES, |n| {
        format!(
            "h(positional f, positional m) = m.map(x -> f(x));\na = h(x -> x + 1, {}).sum;\n",
            list(n)
        )
    });
    let run = |n: usize| assert_eq!(value(&srcs[&n], "a"), (n * (n + 1) / 2).to_string());
    scaling::check(
        "map of n entries of a parameter by a lambda calling a parameter, whole path",
        N_ENTRIES,
        run,
    );
}

/// Row FAIL-group-key-function: n families nested, each keyed by a call of the parameter `f`:
/// the call meets each key's data need once, no longer deferred as a lambda's parameter.
/// Small instances: `empty::a_key_made_by_a_function_is_data_at_each_call`.
#[test]
fn n_families_keyed_by_calls_of_a_parameter_check_in_linear_time() {
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let deep = (0..n).fold("0".to_string(), |t, i| format!("{{f({i}) -> {t}}}"));
        let path: String = (0..n).rev().map(|i| format!("[{}]", i + 1)).collect();
        format!("h(positional f) = {deep};\na = h(x -> x + 1){path};\n")
    });
    let run = |n: usize| assert_eq!(value(&srcs[&n], "a"), "0");
    scaling::check(
        "n families nested, keyed by calls of a parameter, whole path",
        N_LEVELS,
        run,
    );
}

#[test]
fn a_lambda_that_calls_a_parameter_n_families_deep_runs_in_linear_time() {
    // The call enters each of the n families above the lambda once, and each of the n
    // lookups, a call of a family with no needs, walks none of them (`apply_one` in
    // crates/zedc-check/src/check/walk.rs; walking at each lookup gave 14.55 at 8n).
    let srcs = scaling::inputs(N_LEVELS, |n| {
        let deep = (0..n).fold("(z -> f(z))".to_string(), |t, _| {
            format!("{{\"k\" -> {t}}}")
        });
        let path = "[\"k\"]".repeat(n);
        format!("h(positional f) = {deep};\na = {{ p = h(x -> x + 1); p{path}(2) }};\n")
    });
    let run = |n: usize| assert_eq!(value(&srcs[&n], "a"), "3");
    scaling::check(
        "a lambda that calls a parameter, n families deep in the result, run, whole path",
        N_LEVELS,
        run,
    );
}

#[test]
fn n_maps_by_a_parameter_chained_check_in_linear_time() {
    // Plan row FAIL-map-chain-needs-quadratic: link h{i} calls h{i-1} and maps its result by
    // the parameter `f`, so the needs of a link's signature grow with its depth.
    for lambda in [false, true] {
        let by = if lambda { "x -> f(x)" } else { "f" };
        let srcs = scaling::inputs(N_LEVELS, |n| {
            let mut src = format!("h0(positional f, positional m) = m.map({by});\n");
            for i in 1..n {
                src.push_str(&format!(
                    "h{i}(positional f, positional m) = h{}(f, m).map({by});\n",
                    i - 1
                ));
            }
            src.push_str(&format!(
                "a = h{}(x -> x + 1, {{\"k\" -> 0}})[\"k\"];\n",
                n - 1
            ));
            src
        });
        let run = |n: usize| assert_eq!(value(&srcs[&n], "a"), n.to_string());
        scaling::check(
            &format!("n functions chained, each mapping by `{by}`, whole path"),
            N_LEVELS,
            run,
        );
    }
}

#[test]
fn n_calls_mapping_by_one_parameter_check_in_linear_time() {
    // Landing review of FAIL-map-chain-needs-quadratic (LAND-map-chain-neon, Sol's L1 finding):
    // n calls `h0(f, m_i)` in one body, each kept as a forward that watches the one operand `f`.
    // Each admission scanned `f`'s watchers for `#19`, each need scanned them for `f1`, and each
    // forward kept or forced removed itself from the list: O(n^2) in all, check-stage work 17
    // times as large at 8n for n = 1000 before the per-root counts and key index.
    let n_calls = 1000;
    let srcs = scaling::inputs(n_calls, |n| {
        let mut src = String::from("h0(positional f, positional m) = m.map(f);\n");
        let params: Vec<String> = (1..=n).map(|i| format!("positional m{i}")).collect();
        src.push_str(&format!(
            "outer(positional f, {}) = {{\n",
            params.join(", ")
        ));
        for i in 1..=n {
            src.push_str(&format!("  _ = h0(f, m{i});\n"));
        }
        src.push_str("  f\n};\n");
        let args: Vec<&str> = (1..=n).map(|_| "{\"k\" -> 0}").collect();
        src.push_str(&format!("a = outer(x -> x + 1, {})(1);\n", args.join(", ")));
        src
    });
    let run = |n: usize| assert_eq!(value(&srcs[&n], "a"), "2");
    scaling::check(
        "n calls mapping by one parameter `f`, whole path",
        n_calls,
        run,
    );
}
