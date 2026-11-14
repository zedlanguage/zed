//! The static type of a call of a function whose parameter's type is a bounded variable holds
//! every value the call gives (item LIT-generic-parts-type). A bounded variable, as `T` in
//! `(x: T, p: _) -> T for T in int | f64 | rat`, stands for one carrier of its bound: a call
//! "checks that its arguments' carriers are one carrier in the bound" (DESIGN.md step L1.26),
//! and the body's operators make new values of that carrier. So `f(x, p) = x + p[0]` called as
//! `f(x: 1r, p: (2r, 1))` is `rat`, which holds its value `3r`; it was `1r | 2r`, the literals
//! the call passed, which does not.

use zed_tests::step_helpers::l01_16_elaboration::{elab, with_prelude};
use zed_tests::step_helpers::l01_26_type_resolution::info;

/// The static type of `name` in `src`, its value, and whether the type holds the value; and
/// the checker's errors, which must be none.
fn typed_value(src: &str, name: &str) -> (String, String, bool) {
    let (i, _) = info(src);
    let errors: Vec<&str> = i.errors.iter().map(|e| e.message.as_str()).collect();
    assert!(errors.is_empty(), "{src}\nerrors: {errors:?}");
    let ty = i
        .tops
        .get(name)
        .unwrap_or_else(|| panic!("{src}\nno type for `{name}`"));
    let unit = elab(src).unwrap_or_else(|e| panic!("{src}\n{e:?}"));
    let term = unit
        .get(name)
        .unwrap_or_else(|| panic!("{src}\nno `{name}`"));
    let v = zed_kernel::eval(&with_prelude(term)).unwrap_or_else(|e| panic!("{src}\n{e:?}"));
    let kernel = ty
        .kernel()
        .unwrap_or_else(|| panic!("{src}\n`{ty}` has no kernel type"));
    (ty.to_string(), v.to_string(), kernel.contains(&v))
}

/// Each program's `y` has the static type and the value written beside it, and the type
/// holds the value. The first line of each is the case of the item; the old types, before the
/// fix, are in the comments.
#[test]
fn a_call_through_a_bounded_variable_has_the_carrier_and_not_the_arguments_values() {
    let cases = [
        // was `1r | 2r`
        (
            "f(x, p) = x + p[0];\ny = f(x: 1r, p: (2r, 1));\n",
            "rat",
            "3r",
        ),
        // was `1r` (and rejected on main before LIT-tuple-rest)
        (
            "f(x, p) = x + p[0];\ny = f(x: 1r, p: (2, 1));\n",
            "rat",
            "3r",
        ),
        // was `1r | 2r`
        (
            "f(x, p) = x + p[0];\ny = f(x: 1r, p: (2r, 1r));\n",
            "rat",
            "3r",
        ),
        // was `1r | 2r`
        (
            "f(x, p) = x - p[0];\ny = f(x: 1r, p: (2r, 1));\n",
            "rat",
            "-1r",
        ),
        // was `2r | 3r`
        (
            "f(x, p) = x * p[0];\ny = f(x: 3r, p: (2r, 1));\n",
            "rat",
            "6r",
        ),
        // was `1r | 2r | 4r`
        (
            "f(x, p) = x + p[0] + p[2];\ny = f(x: 1r, p: (2r, 1, 4r));\n",
            "rat",
            "7r",
        ),
        // was `1r | 2r`
        (
            "f(x, p) = x + p[0][1];\ny = f(x: 1r, p: ((1, 2r), 1));\n",
            "rat",
            "3r",
        ),
        // was `1r | 2r`
        (
            "g(x, p) = x + p[0];\nf(x, p) = g(x: x, p: p);\ny = f(x: 1r, p: (2r, 1));\n",
            "rat",
            "3r",
        ),
        // was `1r | 2r`
        (
            "f(x, p) = x + p[0];\nq = (2r, 1);\ny = f(x: 1r, p: q);\n",
            "rat",
            "3r",
        ),
        // was `(1r | 2r, 1)`
        (
            "f(x, p) = (x + p[0], p[1]);\ny = f(x: 1r, p: (2r, 1));\n",
            "(rat, 1)",
            "(3r, 1)",
        ),
        // was `1r`
        ("inc(x) = x + 1;\ny = inc(x: 1r);\n", "rat", "2r"),
        // was `2`
        ("inc(x) = x + 1;\na = 2;\ny = inc(x: a);\n", "int", "3"),
        // was `1r`
        ("dbl(x) = x + x;\ny = dbl(x: 1r);\n", "rat", "2r"),
        // was `1r`
        ("neg(x) = -x;\ny = neg(x: 1r);\n", "rat", "-1r"),
        // these held before and hold now
        ("f(x, p) = x + p[0];\ny = f(x: 1, p: (2, 1));\n", "int", "3"),
        (
            "f(x, p) = x + p[0];\ny = f(x: 1.0f64, p: (2.0f64, 1));\n",
            "f64",
            "3.0",
        ),
        ("f(x, y) = x + y;\ny = f(x: 1r, y: 2r);\n", "rat", "3r"),
        ("y = 1r + 2r;\n", "rat", "3r"),
    ];
    for (src, ty, value) in cases {
        let (t, v, holds) = typed_value(src, "y");
        assert_eq!((t.as_str(), v.as_str()), (ty, value), "{src}");
        assert!(holds, "{src}\n`{t}` does not hold {v}");
    }
}

/// The static type of each generated call holds the value the evaluator gives: 432 programs,
/// every combination of a carrier (`int`, `rat` by the `r` suffix, `f64` by its suffix), an
/// operator (`+`, `-`, `*`), where the part stands (the first or second component of a pair,
/// the last of a 3-tuple, inside a nested tuple, or both components), whether the part carries the suffix or is a bare
/// literal that takes `x`'s carrier (the same `2` for `int`, which has no suffix), and how the
/// call is made (directly, through a second function, with the tuple bound to a name, or with
/// `x` bound to a name, whose type is then its value, `w = 3`). A bare literal in a tuple bound
/// to a name is read as `int` (DESIGN.md step L1.26a: "bound to a name alone"), so
/// `q = (2, 1); y = f(x: 3r, p: q)` is rejected, and the test says so.
#[test]
fn the_static_type_of_each_generated_call_holds_its_value() {
    let carriers = [("", "", ""), ("r", "2r", "2"), ("f64", "2.5f64", "2.5")];
    let ops = ["+", "-", "*"];
    // The index read in the body, and the tuple the call passes, with `{}` for the part.
    let shapes = [
        ("p[0]", "({}, 1)"),
        ("p[1]", "(1, {})"),
        ("p[2]", "(\"s\", 1, {})"),
        ("p[0][1]", "((1, {}), 1)"),
        ("p[1][0][0]", "(1, (({},), 2))"),
        ("p[0] + p[1]", "({}, {})"),
    ];
    let (mut checked, mut rejected) = (0, 0);
    let mut wrong = Vec::new();
    for (suffix, forced_part, bare_part) in carriers {
        let x = match suffix {
            "" => "3".to_string(),
            "f64" => "3.5f64".to_string(),
            s => format!("3{s}"),
        };
        for op in ops {
            for (read, tuple) in shapes {
                for forced in [true, false] {
                    let part = match (suffix, forced) {
                        ("", _) => "2",
                        (_, true) => forced_part,
                        (_, false) => bare_part,
                    };
                    let p = tuple.replace("{}", part);
                    let body = format!("x {op} {read}");
                    let direct = format!("f(x, p) = {body};\ny = f(x: {x}, p: {p});\n");
                    let chained = format!(
                        "g(x, p) = {body};\nf(x, p) = g(x: x, p: p) {op} x;\ny = f(x: {x}, p: {p});\n"
                    );
                    let named = format!("f(x, p) = {body};\nq = {p};\ny = f(x: {x}, p: q);\n");
                    let named_x = format!("f(x, p) = {body};\nw = {x};\ny = f(x: w, p: {p});\n");
                    for (call, int_parts) in [
                        (direct, false),
                        (chained, false),
                        (named, true),
                        (named_x, false),
                    ] {
                        checked += 1;
                        if int_parts && !forced && !suffix.is_empty() {
                            let (i, _) = info(&call);
                            assert!(!i.errors.is_empty(), "{call}\naccepted");
                            rejected += 1;
                            continue;
                        }
                        let (t, v, holds) = typed_value(&call, "y");
                        if !holds {
                            wrong.push(format!("{call}  type {t}, value {v}"));
                        }
                    }
                }
            }
        }
    }
    assert_eq!((checked, rejected), (432, 36));
    assert!(
        wrong.is_empty(),
        "{} of {checked}:\n{}",
        wrong.len(),
        wrong.join("\n")
    );
}

/// A function that reads `n` parts of its tuple parameter, called with a tuple of `n` distinct
/// `r` literals: the binding of its bounded variable has `n + 1` pieces, each widened to `rat`
/// once (COMPLEXITY.md F170).
pub(super) fn parts(n: usize) -> String {
    let reads: Vec<String> = (0..n).map(|i| format!("p[{i}]")).collect();
    let tuple: Vec<String> = (0..n).map(|i| format!("{}r", i + 2)).collect();
    format!(
        "f(x, p) = x + {};\ny = f(x: 1r, p: ({}));\n",
        reads.join(" + "),
        tuple.join(", ")
    )
}

/// `n` calls of one function, each with its own `r` literals (COMPLEXITY.md F170).
pub(super) fn calls(n: usize) -> String {
    let ys: Vec<String> = (0..n)
        .map(|i| format!("y{i} = f(x: {}r, p: ({}r, 1));\n", i + 1, i + 2))
        .collect();
    format!("f(x, p) = x + p[0];\n{}", ys.concat())
}


#[test]
fn a_call_that_reads_many_parts_widens_each_to_rat() {
    // A small instance of the benchmark
    // `bench::parts_type::a_call_that_reads_many_parts_checks_in_linear_time`.
    assert_eq!(
        typed_value(&parts(3), "y"),
        ("rat".into(), "10r".into(), true)
    );
}

#[test]
fn many_calls_through_a_bounded_variable_each_take_rat() {
    // A small instance of the benchmark
    // `bench::parts_type::many_calls_through_a_bounded_variable_check_in_linear_time`.
    assert_eq!(
        typed_value(&calls(3), "y2"),
        ("rat".into(), "7r".into(), true)
    );
}
