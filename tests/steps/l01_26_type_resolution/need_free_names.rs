//! A need recorded in a generic function that reads a name besides the value it is on, met at
//! a call with an argument of the wrong type: one program per need kind, in the shape of the
//! remap bug FAIL-remap-need-free-names-unbound (b22-checkwalk12), where the key expression of
//! a remap read a parameter that was unbound when the need was met and stopped zedc with "a bug
//! in zedc". b22-checkwalk12 claimed, by reading, that no other need kind re-reads a stored
//! expression; these programs check it by running (b22-checkwalk13, 2026-11-24, row
//! NEED-kinds-probe). Each wrong call is refused with the checker's own words and none stops
//! zedc; each right call runs and prints its value. The right calls of the folds whose lambda
//! passes the entry to a function parameter are refused (`f` met at `_`), a false refusal, not
//! a crash: row FAIL-fold-lambda-calls-param-entry, test source in
//! /home/luke/Work/wt/failing-tests/. The same refusal of `any` was fixed by
//! FAIL-any-lambda-calls-param (b22-scale1, 2026-11-26), so its right call runs here.

use zed_tests::step_helpers::l01_36a_executables::{Ran, dir, interpreter};

/// Runs `{def}` with `main` printing `{call}`, through `zedc run`.
fn run(name: &str, def: &str, call: &str) -> Ran {
    let d = dir(&format!("l01_26/need_free_names/{name}"));
    let src = d.join(format!("{name}.zed"));
    std::fs::write(
        &src,
        format!("{def}\nmain(m: MainArgs) {{\n  c = {call};\n  m.stdout <- \"${{c}}\";\n}}\n"),
    )
    .unwrap();
    interpreter(&src, &[], &[])
}

/// The program is refused by the checker, with `needle` in its message, and does not stop zedc.
fn refused(name: &str, def: &str, call: &str, needle: &str) {
    let ran = run(name, def, call);
    let err = &ran.stderr;
    assert!(!err.contains("bug in zedc"), "{name}: {err}");
    assert_eq!(ran.status, 1, "{name}: {err}");
    assert!(ran.stdout.is_empty(), "{name}");
    assert!(err.contains(needle), "{name}: wanted {needle:?} in {err}");
}

/// The program runs and prints `out`.
fn runs(name: &str, def: &str, call: &str, out: &str) {
    let ran = run(name, def, call);
    assert_eq!(ran.status, 0, "{name}: {}", ran.stderr);
    assert_eq!(ran.stdout, format!("{out}\n"), "{name}");
}

#[test]
fn a_group_need_reading_another_parameter_is_met_at_each_call() {
    let f = "g(positional m, positional f) = m.group(x -> f(x));";
    refused(
        "group_f_bad",
        f,
        "g([\"a\", \"b\"], w -> w + 1)",
        "`f` does not take (\"a\" | \"b\")",
    );
    runs(
        "group_f_good",
        f,
        "g([1, 2, 3], w -> w mod 2)",
        "{0 -> {1 -> 2}, 1 -> {0 -> 1, 2 -> 3}}",
    );
    let y = "g(positional m, positional y) = m.group(x -> x mod y);";
    refused(
        "group_y_bad",
        y,
        "g([\"a\"], 1)",
        "`g` gives each entry of its argument to a function that requires a value of int, and an \
         entry here is \"a\"",
    );
    runs(
        "group_y_good",
        y,
        "g([1, 2, 3], 2)",
        "{0 -> {1 -> 2}, 1 -> {0 -> 1, 2 -> 3}}",
    );
}

#[test]
fn a_level_need_reading_another_parameter_is_met_at_each_call() {
    let y = "g(positional m, positional y) = m.any(x -> x > y);";
    // The call is refused, which is what this test is for. The headline names `g`'s arguments,
    // not the comparison `x > y` that fails; plan row
    // MSG-level-need-at-call-names-the-comparison makes it name the comparison.
    refused(
        "any_y_bad",
        y,
        "g([\"a\"], 1)",
        "`g` does not take (0 -> \"a\", 1)",
    );
    runs("any_y_good", y, "g([1, 5], 2)", "true");
    // Since FAIL-any-lambda-calls-param the lambda is checked with the entries bound, so the
    // right call runs.
    let f = "g(positional m, positional f) = m.any(x -> f(x));";
    refused(
        "any_f_bad",
        f,
        "g([\"a\"], w -> w + 1 > 2)",
        "`f` does not take",
    );
    runs("any_f_good", f, "g([1, 5], w -> w > 2)", "true");
    let c = "g(positional m, positional f) = m.where(x -> f(x)).count;";
    refused(
        "count_bad",
        c,
        "g([\"a\"], w -> w > 2)",
        "`f` does not take (\"a\")",
    );
    runs("count_good", c, "g([1, 5], w -> w > 2)", "1");
}

#[test]
fn a_strings_need_reading_another_parameter_is_met_at_each_call() {
    let f = "p(positional s, positional f) = s.split(f(1));";
    refused(
        "split_f_bad",
        f,
        "p(\"a,b\", x -> x + 1)",
        "`split` reads strings, and this value is int",
    );
    runs(
        "split_f_good",
        f,
        "p(\"a,b\", x -> \",\")",
        "{0 -> \"a\", 1 -> \"b\"}",
    );
    let y = "p(positional m, positional y) = m.map(t -> t.split(y));";
    refused(
        "split_y_bad",
        y,
        "p([\"a,b\"], 1)",
        "`split` reads strings, and this value, passed as `y`, is 1",
    );
    runs(
        "split_y_good",
        y,
        "p([\"a,b\"], \",\")",
        "{0 -> {0 -> \"a\", 1 -> \"b\"}}",
    );
}

#[test]
fn a_fold_need_reading_another_parameter_is_met_at_each_call() {
    // The wrong calls of a fold whose lambda calls `f` on the entry are refused, though with
    // `(_)` in place of `("a")`, and its right calls are refused too (row
    // FAIL-fold-lambda-calls-param-entry): neither stops zedc.
    let l = "g(positional m, positional f) = m.foldl(0, (a, x) -> a + f(x));";
    refused(
        "foldl_f_bad",
        l,
        "g([\"a\"], w -> w + 1)",
        "`f` does not take",
    );
    let r = "g(positional m, positional f) = m.foldr((x, a) -> a + f(x), 0);";
    refused(
        "foldr_f_bad",
        r,
        "g([\"a\"], w -> w + 1)",
        "`f` does not take",
    );
    let y = "g(positional m, positional y) = m.foldl(0, (a, x) -> a + x + y);";
    refused(
        "foldl_y_bad",
        y,
        "g([1], \"s\")",
        "`g` does not take (0 -> 1, \"s\")",
    );
    runs("foldl_y_good", y, "g([1, 2], 10)", "23");
    let by = "g(positional f) = [1, 2].foldl(0, f);";
    runs("foldl_by_good", by, "g((a, x) -> a + x + 1)", "5");
    refused(
        "foldl_by_bad",
        "g(positional f) = [\"a\"].foldl(0, f);",
        "g((a, x) -> a + x + 1)",
        "the function given to `foldl` does not take (int, \"a\")",
    );
    // Negative controls: the fold on a parameter with no other name, and on a known family.
    runs(
        "foldl_plain",
        "g(positional m) = m.foldl(0, (a, x) -> a + x);",
        "g([1, 2])",
        "3",
    );
    runs(
        "foldl_known_m",
        "g(positional f) = [1, 2].foldl(0, (a, x) -> a + f(x));",
        "g(w -> w + 1)",
        "5",
    );
}

#[test]
fn a_sum_need_reading_another_parameter_is_met_at_each_call() {
    // `.reduce` and `><` take `max`, `min` or an operator section in this zedc, none of which
    // reads a name; `.sum` of a `map` is the reduction that does.
    let s = "g(positional m, positional f) = m.map(x -> f(x)).sum;";
    refused(
        "sum_map_bad",
        s,
        "g([\"a\"], w -> w + 1)",
        "`f` does not take (\"a\")",
    );
    runs("sum_map_good", s, "g([1, 2], w -> w + 1)", "5");
}

#[test]
fn a_map_need_reading_another_parameter_is_met_at_each_call() {
    let f = "g(positional m, positional f) = m.map(x -> f(x));";
    refused(
        "map_f_bad",
        f,
        "g([\"a\"], w -> w + 1)",
        "`f` does not take (\"a\")",
    );
    runs("map_f_good", f, "g([1, 2], w -> w + 1)", "{0 -> 2, 1 -> 3}");
    let y = "g(positional m, positional y) = m.map(x -> x + y);";
    refused(
        "map_y_bad",
        y,
        "g([\"a\"], 1)",
        "`g` does not take (0 -> \"a\", 1)",
    );
    refused(
        "map_pass_bad",
        "g(positional m, positional f) = m.map(x -> f(x));\nh(positional m, positional f) = g(m, f);",
        "h([\"a\"], w -> w + 1)",
        "`f` does not take (\"a\")",
    );
    refused(
        "map_nested_bad",
        "g(positional m, positional f) = [1].map(i -> m.map(x -> f(x)));",
        "g([\"a\"], w -> w + 1)",
        "`f` does not take (\"a\")",
    );
    let w = "g(positional m, positional f) = m.where(x -> f(x));";
    refused(
        "where_f_bad",
        w,
        "g([\"a\"], w -> w + 1 > 2)",
        "`f` does not take (\"a\")",
    );
    runs("where_f_good", w, "g([1, 5], w -> w > 2)", "{1 -> 5}");
    refused(
        "flatmap_f_bad",
        "g(positional m, positional f) = m.flatMap(x -> [f(x)]);",
        "g([\"a\"], w -> w + 1)",
        "`f` does not take (\"a\")",
    );
}

#[test]
fn a_concat_need_reading_another_parameter_is_met_at_each_call() {
    let f = "cc(positional a, positional f) = a ++ f(a);";
    refused(
        "concat_f_bad",
        f,
        "cc(\"ab\", x -> [1])",
        "which is not String",
    );
    runs("concat_f_good", f, "cc(\"ab\", x -> \"c\")", "abc");
    let y = "cc(positional a, positional y) = a.map(x -> x ++ y);";
    refused(
        "concat_y_bad",
        y,
        "cc([\"ab\"], [1])",
        "`cc` does not take (0 -> \"ab\", 0 -> 1)",
    );
    runs("concat_y_good", y, "cc([\"ab\"], \"c\")", "{0 -> \"abc\"}");
}

#[test]
fn a_zip_need_reading_another_parameter_is_met_at_each_call() {
    let f = "z(positional a, positional f) = a.zip(f(a));";
    refused(
        "zip_f_bad",
        f,
        "z([1], x -> 5)",
        "`zip` reads the entries of a family, and this value is 5",
    );
    runs("zip_f_good", f, "z([1], x -> [2])", "{0 -> (1, 2)}");
    let y = "z(positional a, positional y) = a.map(x -> x.zip(y));";
    refused(
        "zip_y_bad",
        y,
        "z([[1]], 5)",
        "`zip` reads the entries of a family, and this value is 5",
    );
    runs("zip_y_good", y, "z([[1]], [2])", "{0 -> {0 -> (1, 2)}}");
}

#[test]
fn a_power_or_domain_need_reading_another_parameter_is_met_at_each_call() {
    let f = "p(positional x, positional f) = 2 ^ f(x);";
    refused(
        "pow_f_bad",
        f,
        "p(1, x -> -1)",
        "Int power with an exponent that may be negative",
    );
    runs("pow_f_good", f, "p(1, x -> 3)", "8");
    let y = "p(positional m, positional y) = m.map(x -> x ^ y);";
    refused("pow_y_bad", y, "p([2], -1)", "`p` takes `y` in int[0..]");
    runs("pow_y_good", y, "p([2], 3)", "{0 -> 8}");
    refused(
        "pow_lam_bad",
        "p(positional m, positional f) = m.map(x -> 2 ^ f(x));",
        "p([2], x -> -1)",
        "Int power with an exponent that may be negative",
    );
}
