//! An `if` of literals is a union of literal values, each fixed where the result is used as
//! the literal would be alone; an operation on integer literals alone keeps its value in an
//! `if`; and a negated `rat` literal is a literal (DESIGN.md step L1.26a). Item
//! LIT-branch-carrier, from the findings of TESTS-L1.26-refined-divisor.

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{sig, type_errors};

use super::tuple_rest::{fixes_check, unfixed};

const H: &str = "h(positional z: f64) = z;\n";

#[test]
fn literal_branches_take_f64_at_a_parameter_of_type_f64() {
    // DESIGN.md step L1.26a: "where both branches are literals each keeps its own value and
    // is fixed where the result is used", and step L1.26: "A literal at a declared type takes
    // the one numeric carrier of the type it can take". `h(2)` is accepted, so `h(if c { 2 }
    // else { 1 })` is too, each branch read at `f64`.
    let src = format!(
        "{H}f(positional c: bool) = h(if c {{ 2 }} else {{ 1 }});\n\
         a = f(true);\nb = f(false);\nc = h(if true {{ 2 }} else {{ 1 }});\n"
    );
    assert_eq!(type_errors(&src), Vec::<String>::new());
    assert_eq!(sig(&src, "f"), "bool -> f64");
    assert_eq!(value(&src, "a"), "2.0");
    assert_eq!(value(&src, "b"), "1.0");
    assert_eq!(value(&src, "c"), "2.0");
}

#[test]
fn nested_literal_branches_each_take_f64() {
    // Each branch of a nest of `if`s, a decimal and a negated literal among them.
    let src = format!(
        "{H}f(positional a: bool, positional b: bool) = \
         h(if a {{ 1 }} else if b {{ 2.5 }} else {{ -3 }});\n\
         x = f(true, false);\ny = f(false, true);\nz = f(false, false);\n"
    );
    assert_eq!(type_errors(&src), Vec::<String>::new());
    assert_eq!(sig(&src, "f"), "(bool, bool) -> f64");
    assert_eq!(value(&src, "x"), "1.0");
    assert_eq!(value(&src, "y"), "2.5");
    assert_eq!(value(&src, "z"), "-3.0");
}

#[test]
fn a_decimal_branch_is_still_rejected_at_int() {
    // Negative control: each branch is fixed as it would be alone, so a decimal branch at an
    // `int` parameter is rejected as `h(1.5)` is, at the decimal, and the integer branch is
    // not.
    let src = "h(positional z: int) = z;\nf(positional c: bool) = h(if c { 2 } else { 1.5 });\n";
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("A decimal literal is never an `int`: the literal `1.5`")
            && errors[0].ends_with("[1.5]"),
        "{errors:?}"
    );
}

#[test]
fn literal_branches_take_the_carrier_of_the_dividend() {
    // The finding of TESTS-L1.26-refined-divisor: `x / (if c { 2 } else { -3 })` with `x`
    // a `rat` or an `f64`. Each branch takes the carrier of `x`, as `x / 2` does, and the
    // divisor `2 | -3` holds no zero, so the `rat` division adds no `#divByZero` (L1.26: "A
    // division, `div` or `mod` whose divisor's type holds no zero adds no `#divByZero`").
    for (x, arg, sig_, v) in [
        ("rat", "1r", "(bool, x: rat) -> rat", "-1r/3r"),
        ("f64", "1.5f64", "(bool, x: f64) -> f64", "-0.5"),
    ] {
        let src = format!(
            "f(positional c: bool, x: {x}) = x / (if c {{ 2 }} else {{ -3 }});\n\
             a = f(false, x: {arg});\n"
        );
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{x}");
        assert_eq!(sig(&src, "f"), sig_);
        assert_eq!(value(&src, "a"), v);
    }
}

#[test]
fn a_zero_branch_keeps_div_by_zero() {
    // Negative control: a divisor `2 | 0` holds zero, so the `rat` division keeps
    // `#divByZero`.
    let src = "f(positional c: bool, x: rat) = x / (if c { 2 } else { 0 });\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(sig(src, "f"), "(bool, x: rat) -> rat | #divByZero");
}

#[test]
fn literal_branches_join_the_class_of_a_generic_operand() {
    // DESIGN.md step L1.26a: a literal "joins the class of a parameter of the function" it
    // meets, and takes its carrier by a `match` at run time; so does each branch.
    let src = "f(positional c: bool, x) = x + (if c { 2 } else { 3 });\n\
               a = f(true, x: 0.5f64);\nb = f(false, x: 1);\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(
        sig(src, "f"),
        "(bool, x: T) -> T for T in int | f32 | f64 | rat"
    );
    assert_eq!(value(src, "a"), "2.5");
    assert_eq!(value(src, "b"), "4");
}

#[test]
fn literal_branches_with_nothing_to_fix_them_stay_int() {
    // Negative control: where no other operand gives a carrier, integer branches are `int`,
    // as an integer literal that nothing fixes is.
    let src = "f(positional c: bool) = (if c { 2 } else { 3 }) + 1;\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(sig(src, "f"), "bool -> int");
}

#[test]
fn an_operation_on_literals_keeps_its_value_beside_a_carrier() {
    // DESIGN.md step L1.26a, beside "with `x: f64`, `if c { x } else { 1 }` is `1 | f64`":
    // "an operation on literals alone keeps its value in an `if`". At run time the operation
    // is the `int` 2, as the literal `1` is the `int` 1 in `1 | f64`.
    let src = "g(positional c: bool, x: f64) = if c { 1 + 1 } else { x };\n\
               a = g(true, x: 0.5f64);\nb = g(false, x: 0.5f64);\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(sig(src, "g"), "(bool, x: f64) -> 2 | f64");
    assert_eq!(value(src, "a"), "2");
    assert_eq!(value(src, "b"), "0.5");
}

#[test]
fn an_operation_on_literals_in_an_if_has_its_value_at_run_time() {
    // Each result is compared where it is used, which fixes the `1.5`. Bound alone, `b =
    // g(false)` settles the `1.5` as it would be alone, at `f64` (DESIGN.md L1.26a, "`y = g(c)`
    // [...] settles each as it would be alone, the `1` at `int` and the `2.5` at `f64`").
    let src = "g(positional c: bool) = if c { 1 + 1 } else { 1.5 };\n\
               a = g(true) == 2;\nb = g(false) == 1.5f64;\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(value(src, "a"), "true");
    assert_eq!(value(src, "b"), "true");
    let alone =
        "g(positional c: bool) = if c { 1 + 1 } else { 1.5 };\na = g(true);\nb = g(false);\n";
    assert_eq!(type_errors(alone), Vec::<String>::new());
    assert_eq!(value(alone, "a"), "2");
    assert_eq!(value(alone, "b"), "1.5");
}

#[test]
fn a_division_of_literals_in_an_if_is_not_kept_as_its_value() {
    // Negative control: DESIGN.md step L1.26a, "one that meets no carrier is typed `int`,
    // rejected under `/`, not as its value". `1 / 2` beside `1.5` is not `0.5`: where both
    // branches are literals "each keeps its own value and is fixed where the result is used",
    // so the decimal gives the `/` no carrier, and the `/`, not kept as its value, is rejected.
    // This zedc rejects it beside an integer literal.
    let src = "g(positional c: bool) = if c { 1 / 2 } else { 2 };\n";
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("Nothing gives the literal `1` a carrier"),
        "{errors:?}"
    );
    // Beside a decimal too: the decimal takes `f64` as it would alone, which gives the `/` no
    // carrier (row LIT-branch-division-beside-decimal; zedc took `f64` for the `/` from the
    // other branch, and `g(true)` was `0.5`).
    division_rejected_at_its_one(
        "g(positional c: bool) = if c { 1 / 2 } else { 1.5 };",
        "a = g(true);\nb = g(false);\n",
    );
}

/// `def`, which holds the `/` of integer literals `1 / 2` once, followed by `uses`, is
/// rejected at the `1` alone, with the fixes `1r / 2` and `1.0f64 / 2`, each of which checks.
fn division_rejected_at_its_one(def: &str, uses: &str) {
    let src = format!("{def}\n{uses}");
    let [rat, f64] = ["1r / 2", "1.0f64 / 2"].map(|f| def.replacen("1 / 2", f, 1));
    assert_eq!(type_errors(&src), [unfixed("1", &rat, &f64)], "{src}");
    fixes_check(&src, def, [&rat, &f64]);
}

#[test]
fn a_division_beside_a_decimal_is_rejected_in_every_form() {
    // DESIGN.md step L1.26a: where both branches are literals "each keeps its own value", and
    // an operation on literals alone is a literal; a `/` of integer literals "that meets no
    // carrier is typed `int`, rejected under `/`". A decimal or an operation with a decimal in
    // the other branch is no carrier of the `/`, wherever the `if` stands, and neither is a
    // use that gives no carrier: a generic parameter, `min` beside an integer literal, a cast
    // to `String`, a string hole, a failure fallback. Row LIT-branch-division-beside-decimal:
    // zedc accepted each, the `/` at `f64`.
    let cases = [
        (
            "g(positional c: bool) = if c { 1.5 } else { 1 / 2 };",
            "a = g(true);\nb = g(false);\n",
        ),
        (
            "g(positional c: bool) = if c { 1 / 2 } else { 0.5 * 2 };",
            "a = g(true);\n",
        ),
        (
            "g(positional c: bool) = if c { 1 / 2 + 1 } else { 1.5 };",
            "a = g(true);\n",
        ),
        (
            "g(positional c: bool) = { y = if c { 1 / 2 } else { 1.5 }; y };",
            "a = g(true);\n",
        ),
        (
            "g(positional c: bool) = h(if c { 1 / 2 } else { 1.5 });",
            "h(positional z) = z;\na = g(true);\n",
        ),
        (
            "g(positional c: bool) = min(if c { 1 / 2 } else { 1.5 }, 2);",
            "y = g(true);\n",
        ),
        (
            "g(positional c: bool) = String(if c { 1 / 2 } else { 1.5 });",
            "y = g(true);\n",
        ),
        // DESIGN.md does not say whether `== 0.5` gives the `/` the `f64` the `0.5` takes where
        // nothing fixes it; zedc accepts `g() = 1 / 2 == 0.5` as `true`, in a body and at the
        // top level, but rejects this. Row LIT-division-meets-default-decimal.
        (
            "g(positional c: bool) = (if c { 1 / 2 } else { 1.5 }) == 0.5;",
            "y = g(true);\n",
        ),
        (
            "g(positional c: bool) = \"${if c { 1 / 2 } else { 1.5 }}\";",
            "y = g(true);\n",
        ),
        (
            "g(positional c: bool) = if c { 1 / 2 } else { 1.5 };",
            "y = g(true);\n",
        ),
    ];
    for (def, uses) in cases {
        division_rejected_at_its_one(def, uses);
    }
}

#[test]
fn a_division_beside_a_decimal_takes_the_carrier_the_if_meets() {
    // Negative control: where the `if` meets a carrier, each branch takes it (DESIGN.md step
    // L1.26a, "fixed where the result is used"), the `/` among them.
    let cases = [
        (
            "g(positional c: bool, positional x: f64) = x * (if c { 1 / 2 } else { 1.5 });\n\
             a = g(true, 2.0f64);\nb = g(false, 2.0f64);\n",
            ["1.0", "3.0"],
        ),
        (
            "g(positional c: bool, positional x: rat) = x * (if c { 1 / 2 } else { 1.5 });\n\
             a = g(true, 2r);\nb = g(false, 2r);\n",
            ["1r", "3r"],
        ),
        (
            "h(positional z: f64) = z;\n\
             g(positional c: bool) = h(if c { 1 / 2 } else { 1.5 });\na = g(true);\nb = g(false);\n",
            ["0.5", "1.5"],
        ),
    ];
    for (src, [a, b]) in cases {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
        assert_eq!(value(src, "a"), a, "{src}");
        assert_eq!(value(src, "b"), b, "{src}");
    }
}

#[test]
fn an_integer_literal_beside_an_operation_with_a_decimal_is_read_at_f64() {
    // DESIGN.md step L1.26a: where both branches are literals "each keeps its own value", and
    // step L1.26b: "an operation on literals alone with a decimal among its operands" takes
    // `f64`. So `0.5 * 2` is the `f64` `1.0` and the integer literal beside it stays an `int`,
    // `1` and `6`, in a body as at the top level. This zedc reads the integer literal at
    // `f64` too, `1.0` and `6.0`, in a body, since the branches share one class, which takes
    // one carrier, and at the top level where the decimal branch comes first; row
    // LIT-branch-int-beside-decimal-op. The verdicts this zedc gives
    // are pinned here, so the fix changes them.
    let src = "g(positional c: bool) = if c { 0.5 * 2 } else { 1 };\na = g(true);\nb = g(false);\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(value(src, "a"), "1.0");
    assert_eq!(value(src, "b"), "1.0", "DESIGN.md: 1");
    let src =
        "g(positional c: bool) = if c { 2 * 3 } else { 0.5 * 2 };\na = g(true);\nb = g(false);\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(value(src, "a"), "6.0", "DESIGN.md: 6");
    assert_eq!(value(src, "b"), "1.0");
    let src = "c = 1 < 2;\ny = if c { 0.5 * 2 } else { 1 };\nz = if c { 1 } else { 0.5 * 2 };\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(value(src, "y"), "1.0");
    // At the top level the order of the branches decides it: `z` is `1`, as DESIGN.md says.
    assert_eq!(value(src, "z"), "1");
}

#[test]
fn an_operation_beside_an_integer_literal_takes_the_carrier_of_its_use() {
    // Negative control for the value kept: beside an integer literal the operation and the
    // literal share one class, which takes the carrier of the parameter the `if` meets.
    let src =
        format!("{H}f(positional c: bool) = h(if c {{ 1 + 1 }} else {{ 1 }});\na = f(true);\n");
    assert_eq!(type_errors(&src), Vec::<String>::new());
    assert_eq!(sig(&src, "f"), "bool -> f64");
    assert_eq!(value(&src, "a"), "2.0");
}

#[test]
fn a_negated_rat_literal_is_a_literal() {
    // DESIGN.md step L1.26a: "An operation on literals alone, as `2 + 1` or `-1`, is a
    // literal too"; `-3r` is the value -3 at `rat`, as `3r` is 3.
    assert_eq!(sig("f() = -3r;\n", "f"), "() -> -3r");
    assert_eq!(value("y = -3r;\n", "y"), "-3r");
}

#[test]
fn a_negated_rat_divisor_adds_no_div_by_zero() {
    // The finding of TESTS-L1.26-refined-divisor: `x / -3r` kept `#divByZero`, since `-3r`
    // was typed `rat`.
    let src = "f(positional x: rat) = x / -3r;\na = f(1r);\n";
    assert_eq!(type_errors(src), Vec::<String>::new());
    assert_eq!(sig(src, "f"), "rat -> rat");
    assert_eq!(value(src, "a"), "-1r/3r");
}

#[test]
fn a_negated_zero_rat_divisor_keeps_div_by_zero() {
    // Negative control: `-0r` is 0, so the division always fails.
    let src = "f(positional x: rat) = x / -0r;\n";
    assert_eq!(sig(src, "f"), "rat -> rat | #divByZero");
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("`/` here always fails with `#divByZero`"),
        "{errors:?}"
    );
}

/// A call of a parameter of type `f64` on a nest of `n` `if`s, each branch its own integer
/// literal: a union of `n + 1` literal values, each fixed at `f64`.
pub(super) fn nest(n: usize) -> String {
    let mut body = String::new();
    for i in 0..n {
        body += &format!("if c == {i} {{ {i} }} else ");
    }
    body += &format!("{{ {n} }}");
    format!("{H}f(positional c: int) = h({body});\n")
}

#[test]
fn an_if_of_many_literal_branches_takes_f64_at_a_parameter() {
    // A small instance of the benchmark `bench::lit_branches::scaling`.
    assert_eq!(type_errors(&nest(3)), Vec::<String>::new());
    assert_eq!(sig(&nest(3), "f"), "int -> f64");
}

/// The definition of `g`, a sum of `n` `if`s, each `if c { 1 / 2 } else { 1.5 }`, times the
/// parameter `x` where `x` is `Some` of its type: the classes of the `if`s join one class.
pub(super) fn summed_ifs(n: usize, x: Option<&str>) -> String {
    let (param, times) = x.map_or((String::new(), ""), |t| {
        (format!(", positional x: {t}"), "x * ")
    });
    let terms = vec![format!("{times}(if c {{ 1 / 2 }} else {{ 1.5 }})"); n];
    format!("g(positional c: bool{param}) = {};", terms.join(" + "))
}

/// The definition of `g`, one `if` whose first branch is a sum of `n` divisions `1 / 2`.
pub(super) fn wide_branch(n: usize) -> String {
    let sum = vec!["1 / 2"; n].join(" + ");
    format!("g(positional c: bool) = if c {{ {sum} }} else {{ 1.5 }};")
}

#[test]
fn many_divisions_beside_decimals_are_rejected_once() {
    // Small instances of the benchmarks of `bench::lit_branches`: the branches rejected alone
    // are rejected at the first `1` once; in one branch, a fix of that literal checks, since
    // it gives the branch's class its carrier; at `x: f64` each `if` takes it, with no error.
    // In a sum of `if`s the `rat` fix is not offered, since it does not check:
    // `(if c { 1r / 2 } else { 1.5 })` is `rat | f64` (DESIGN.md step L1.26a, "where one branch
    // is a literal and the other has a carrier, the literal branch is fixed as it would be
    // alone"), which `+` does not take beside the next `if`; the `f64` fix checks (row
    // MSG-branch-sum-fix-unchecked).
    let def = summed_ifs(3, None);
    let src = format!("{def}\ny = g(true);\n");
    let [rat, f64] = ["1r / 2", "1.0f64 / 2"].map(|f| def.replacen("1 / 2", f, 1));
    let w = f64.len() + 4;
    let only_f64 = format!(
        "Nothing gives the literal `1` a carrier. Try `{}` instead.\n  fixes, each checked \
         here:\n    {f64:w$}the literal is then the f64 1.0 [1]",
        f64.trim_end_matches(';')
    );
    assert_eq!(type_errors(&src), [only_f64]);
    assert_eq!(type_errors(&src.replace(&def, &rat)).len(), 2);
    assert_eq!(type_errors(&src.replace(&def, &f64)), Vec::<String>::new());
    division_rejected_at_its_one(&wide_branch(3), "y = g(true);\n");
    let src = format!("{}\ny = g(true, 2.0f64);\n", summed_ifs(3, Some("f64")));
    assert_eq!(type_errors(&src), Vec::<String>::new());
    assert_eq!(value(&src, "y"), "3.0");
}

#[test]
fn each_fix_offered_for_a_sum_of_ifs_checks() {
    // DESIGN.md step L1.26b: "each fix its message offers is applied in turn, and the file then
    // checks" (row MSG-branch-sum-fix-unchecked).
    let src = "g(positional c: bool) = (if c { 1 / 2 } else { 1.5 }) + (if c { 1 / 2 } else { 1.5 });\ny = g(true);\n";
    let errors = type_errors(src);
    assert_eq!(errors.len(), 1, "{errors:?}");
    let fixes: Vec<&str> = errors[0]
        .lines()
        .skip_while(|l| !l.contains("fixes, each checked here"))
        .skip(1)
        .map(|l| l.trim().split("    ").next().unwrap_or(""))
        .collect();
    assert!(!fixes.is_empty(), "{}", errors[0]);
    for fix in fixes {
        let fixed = src.replacen(src.lines().next().unwrap(), fix, 1);
        assert_eq!(type_errors(&fixed), Vec::<String>::new(), "{fixed}");
    }
}
