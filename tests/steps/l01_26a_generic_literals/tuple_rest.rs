//! A literal that nothing gives a carrier is rejected where its carrier matters, in the places
//! item LIT-tuple-rest adds to those of item MSG-literal-tuple: a tuple passed to `min` or
//! `max`, the payload of an atom in a call's argument, a part of a tuple display that reaches a
//! variable the display's other parts fix nothing for, the branches of an `if`, the value of a
//! block, the body of a called function, an indexed tuple display, and a string hole that holds
//! any of these. Since the author decision of 2026-11-12 a decimal that nothing fixes takes
//! `f64` (DESIGN.md step L1.26b), in all these places, so the rejection these tests reach is
//! that of a `/` of integer literals alone, which has no carrier at `int`; each test also
//! checks that the decimal written there is accepted, at `f64`. A literal that a carrier
//! reaches stays accepted: `x: 1r` gives the `2` of `p: (2, 1)` its carrier in
//! `f(x, p) = x + p[0]`. A called function's result settles each literal as it would be alone
//! (DESIGN.md L1.26a: "`y = g(c)` reads the `1` at `int` and the `2.5` at `f64`").

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{Resolved, sig, type_errors};

/// The rejection of the integer literal `lit` that nothing gives a carrier, the dividend of a
/// `/` of integer literals, whose fixes write it as a `rat`, the line `rat`, and as an `f64`,
/// the line `f64`, each naming the value the literal then is.
pub(super) fn unfixed(lit: &str, rat: &str, f64: &str) -> String {
    let w = f64.len().max(rat.len()) + 4;
    format!(
        "Nothing gives the literal `{lit}` a carrier. Try `{}` instead.\n  fixes, each checked \
         here:\n    {rat:w$}the literal is then exactly {lit}, a rat\n    {f64:w$}the literal \
         is then the f64 {lit}.0 [{lit}]",
        rat.trim_end_matches(';')
    )
}

/// `src`, which defines `g(positional c: bool) = if c { 1 } else { 5 / 2 };` and calls it, is
/// rejected at the `5`. DESIGN.md step L1.26a settles each branch of an `if` of literals as it
/// would be alone ("where both branches are literals each keeps its own value"), so the `5 / 2`
/// is rejected at its `5`, with the fixes `5r / 2` and `5.0f64 / 2`, as at the top level, and
/// each fix checks. Row LIT-branch-division-names-wrong-literal: zedc rejected the `1` of the
/// other branch, with the fixes `1r` and `1.0f64`, each rejected in turn at the `5`.
pub(super) fn branch_division_names_the_one(src: &str) {
    let g = "g(positional c: bool) = if c { 1 } else { 5 / 2 };";
    let named = [
        "g(positional c: bool) = if c { 1 } else { 5r / 2 };",
        "g(positional c: bool) = if c { 1 } else { 5.0f64 / 2 };",
    ];
    assert_eq!(
        type_errors(src),
        [unfixed("5", named[0], named[1])],
        "{src}"
    );
    fixes_check(src, g, named);
}

/// The fixes of the `/` of integer literals `1 / 2` first written in `line`: `1r / 2` and
/// `1.0f64 / 2`.
fn half_fixes(line: &str) -> [String; 2] {
    ["1r / 2", "1.0f64 / 2"].map(|f| line.replacen("1 / 2", f, 1))
}

/// Each fix of the one rejection of `src`, the line `old` rewritten, gives a program with no
/// error: `src` with its line `old` replaced by the fix.
pub(super) fn fixes_check(src: &str, old: &str, fixes: [&str; 2]) {
    for fix in fixes {
        let fixed = src.replace(old, fix);
        assert_ne!(fixed, src, "{old:?} is not a line of {src:?}");
        assert_eq!(type_errors(&fixed), Vec::<String>::new(), "{fixed}");
    }
}

/// `src`, whose one rejected line is `old`, holding `1 / 2`, is rejected at the `1` with the
/// fixes `1r / 2` and `1.0f64 / 2`, and each fix checks.
fn half_rejected(src: &str, old: &str) {
    let [rat, f64] = half_fixes(old);
    assert_eq!(type_errors(src), [unfixed("1", &rat, &f64)], "{src}");
    fixes_check(src, old, [&rat, &f64]);
}

#[test]
fn a_division_in_a_tuple_passed_to_min_or_max_is_rejected() {
    // As `min(1 / 2, 1)` is: the other tuple's `1` gives the `1 / 2` no carrier.
    for old in [
        "x = min((1 / 2, 1), (1, 2));",
        "x = max((1, 2), (1 / 2, 1));",
    ] {
        half_rejected(&format!("{old}\n"), old);
    }
    assert_eq!(
        value("x = min((1.0f64 / 2, 1), (1, 2));\n", "x"),
        "(0.5, 1)"
    );
    // The `1` compared with `1r / 2` takes its carrier; the `2` meets only `1` and stays `int`.
    assert_eq!(value("x = max((1, 2), (1r / 2, 1));\n", "x"), "(1r, 2)");
    // A decimal there takes `f64`.
    assert_eq!(value("x = min((0.5, 1), (1, 2));\n", "x"), "(0.5, 1)");
    assert_eq!(value("x = max((1, 2), (0.5, 1));\n", "x"), "(1.0, 2)");
}

#[test]
fn a_division_in_a_payload_of_an_argument_is_rejected() {
    let old = "y = id(x: #bad(1 / 2));";
    half_rejected(&format!("id(x) = x;\n{old}\n"), old);
    assert_eq!(
        value("id(x) = x;\ny = id(x: #bad(1r / 2));\n", "y"),
        "#bad(1r/2r)"
    );
    assert_eq!(
        value("id(x) = x;\ny = id(x: #bad(0.5));\n", "y"),
        "#bad(0.5)"
    );
}

#[test]
fn the_parts_of_a_tuple_that_reach_one_variable_fix_nothing_for_each_other() {
    // The display reaches `x` whole, and its components are apart: the `0.5f64` gives the
    // `1 / 2` no carrier.
    let old = "y = id(x: (0.5f64, 1 / 2));";
    let src = format!("id(x) = x;\n{old}\n");
    half_rejected(&src, old);
    assert_eq!(rejected_at(&src), [src.rfind("1 / 2)").unwrap()]);
    assert_eq!(
        value("id(x) = x;\ny = id(x: (0.5f64, 1r / 2));\n", "y"),
        "(0.5, 1r/2r)"
    );
    // A decimal beside it takes `f64` of its own.
    assert_eq!(
        value("id(x) = x;\ny = id(x: (0.5f64, 0.5));\n", "y"),
        "(0.5, 0.5)"
    );
}

/// The byte offset of each rejection of `src`.
fn rejected_at(src: &str) -> Vec<usize> {
    let r = Resolved::new(src);
    r.check().errors.iter().map(|e| e.span.start).collect()
}

#[test]
fn an_argument_of_a_carrier_fixes_the_literals_of_a_tuple_part() {
    // `x: 1r` reaches `p[0]` through `+`: the `2`, and a decimal there, are `rat`s.
    let f = "f(x, p) = x + p[0];\n";
    for (call, v) in [
        ("y = f(x: 1r, p: (2, 1));", "3r"),
        ("y = f(x: 1r, p: (0.5, 1));", "3r/2r"),
        ("y = f(x: 1.0f64, p: (2, 1));", "3.0"),
    ] {
        let src = format!("{f}{call}\n");
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{call}");
        assert_eq!(value(&src, "y"), v, "{call}");
    }
}

#[test]
fn a_division_bound_to_several_names_through_a_call_or_an_if_is_rejected() {
    let old = "a, b = id(x: (1 / 2, 1));";
    half_rejected(&format!("id(x) = x;\n{old}\n"), old);
    let old = "a, b = if c { (1 / 2, 1) } else { (1, 2) };";
    half_rejected(&format!("c = true;\n{old}\n"), old);
    // A decimal there takes `f64`.
    let src = "id(x) = x;\na, b = id(x: (0.5, 1));\n";
    assert_eq!(
        (value(src, "a"), value(src, "b")),
        ("0.5".into(), "1".into())
    );
    let src = "c = true;\na, b = if c { (0.5, 1) } else { (1, 2) };\n";
    assert_eq!(value(src, "a"), "0.5");
}

#[test]
fn a_division_a_branch_or_a_block_ends_in_is_rejected() {
    let cases = [
        "y = if c { 1 / 2 } else { 1 };",
        "y = if c { (1 / 2, 1) } else { (1, 1) };",
        "y = if c { #bad(1 / 2) } else { 1 };",
        "y = (if c { 1 / 2 } else { 1 }, 2);",
        "y = { q = 1; (q, 1 / 2) };",
        // A component that the index does not select is rejected all the same: nothing
        // gives it a carrier, wherever it stands.
        "y = (1 / 2, 1)[1];",
    ];
    for old in cases {
        half_rejected(&format!("c = true;\n{old}\n"), old);
        // The same place with a decimal takes `f64`.
        let src = format!("c = true;\n{}\n", old.replacen("1 / 2", "0.5", 1));
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
    }
    assert_eq!(
        value("c = true;\ny = if c { 1r / 2 } else { 1 };\n", "y"),
        "1r/2r"
    );
    assert_eq!(
        value("c = true;\ny = if c { 0.5 } else { 1 };\n", "y"),
        "0.5"
    );
    assert_eq!(
        value("c = true;\ny = { q = 1; (q, 0.5) };\n", "y"),
        "(1, 0.5)"
    );
}

#[test]
fn a_division_a_string_hole_ends_in_is_rejected() {
    for old in [
        "y = \"a${(1 / 2, 1)[0]}\";",
        "y = \"${if c { 1 / 2 } else { 1 }}\";",
    ] {
        half_rejected(&format!("c = true;\n{old}\n"), old);
    }
    assert_eq!(
        value("c = true;\ny = \"a${(1r / 2, 1)[0]}\";\n", "y"),
        "\"a1r/2r\""
    );
    assert_eq!(
        value("c = true;\ny = \"a${(0.5, 1)[0]}\";\n", "y"),
        "\"a0.5\""
    );
}

#[test]
fn a_division_a_called_function_returns_is_rejected() {
    // A body that is the division, one that returns it in a tuple, one that calls a function
    // that returns it, and bodies that return it in a payload, which nothing fixes, as at
    // `y = #bad(1 / 2)`: the rejection is at the body's line, whose fixes rewrite it.
    for (defs, call) in [
        ("f() = 1 / 2;\n", "y = f();"),
        ("f(x: int) = (x, 1 / 2);\n", "y = f(x: 1);"),
        ("f() = 1 / 2;\ng() = f();\n", "y = g();"),
        ("f() = #bad(1 / 2);\n", "y = f();"),
        ("f() = (1, #bad(1 / 2));\n", "y = f();"),
        (
            "f(positional c: bool) = if c { #bad(1 / 2) } else { #ok };\n",
            "y = f(true);",
        ),
        (
            "f(x) = if x > 0 { #bad(x) } else { #bad(1 / 2) };\n",
            "y = f(x: 1.0f64);",
        ),
    ] {
        let src = format!("{defs}{call}\n");
        half_rejected(&src, defs.lines().next().unwrap());
        // The same body with a decimal returns an `f64`.
        let src = src.replacen("1 / 2", "0.5", 1);
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
    }
    assert_eq!(value("f() = 1r / 2;\ny = f();\n", "y"), "1r/2r");
    assert_eq!(value("f() = #bad(1r / 2);\ny = f();\n", "y"), "#bad(1r/2r)");
    assert_eq!(value("f() = 0.5;\ny = f();\n", "y"), "0.5");
    assert_eq!(value("f() = #bad(0.5);\ny = f();\n", "y"), "#bad(0.5)");
}

#[test]
fn a_binding_of_a_call_settles_each_literal_of_its_result_as_alone() {
    // Item LIT-unfixed-decimal-binding, the program of its note: `y = g(true)` with `g` of type
    // `(bool) -> 1 | 2.5`. DESIGN.md L1.26a: "`y = g(c)` reads the `1` at `int` and the `2.5`
    // at `f64`, as each would be read alone where nothing fixes it". The argument's value does
    // not matter to the type: the type of `g(true)` is the type of `g`'s result.
    let g = "g(positional c: bool) = if c { 1 } else { 2.5 };";
    assert_eq!(sig(&format!("{g}\n"), "g"), "bool -> 1 | 2.5");
    for (defs, call, v) in [
        ("c = true;\n", "y = g(c);", "1"),
        ("", "y = g(true);", "1"),
        ("", "y = g(false);", "2.5"),
        // Through nested calls.
        ("k(positional c: bool) = g(c);\n", "y = k(true);", "1"),
        (
            "k(positional c: bool) = g(c);\nm(positional c: bool) = k(c);\n",
            "y = m(false);",
            "2.5",
        ),
    ] {
        let src = format!("{g}\n{defs}{call}\n");
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
        assert_eq!(value(&src, "y"), v, "{src}");
    }
    // The suffixes give these values: the `1` meets no carrier and is the `int` 1, and the
    // decimal is the carrier its suffix names.
    let rat = "g(positional c: bool) = if c { 1 } else { 2.5r };";
    assert_eq!(value(&format!("{rat}\ny = g(false);\n"), "y"), "5r/2r");
    // A carrier at the use fixes both values: an `f64` parameter reads the `1` as 1.0. (A
    // declared binding, `y: f64 = g(true);`, is the other fix DESIGN names; this zedc does not
    // compile a declared binding yet.)
    let fixed = format!("{g}\nh(positional z: f64) = z;\na = h(g(true));\nb = h(g(false));\n");
    assert_eq!(type_errors(&fixed), Vec::<String>::new());
    assert_eq!(value(&fixed, "a"), "1.0");
    assert_eq!(value(&fixed, "b"), "2.5");
}

#[test]
fn a_division_in_a_branch_of_a_called_function_is_rejected_at_its_own_literal() {
    // `y = g(c)` settles each branch as it would be alone (DESIGN.md L1.26a): the `1` at
    // `int`, and the `5 / 2` is rejected, as `y = 5 / 2` is; its fixes rewrite the `5`. The
    // top level does so: `y = if c { 1 } else { 5 / 2 }` is rejected at the `5`, and so is
    // each call (`branch_division_names_the_one`; row LIT-branch-division-names-wrong-literal).
    let g = "g(positional c: bool) = if c { 1 } else { 5 / 2 };";
    let (rat, f64) = (
        "g(positional c: bool) = if c { 1 } else { 5r / 2 };",
        "g(positional c: bool) = if c { 1 } else { 5.0f64 / 2 };",
    );
    let old = "y = if c { 1 } else { 5 / 2 };";
    let src = format!("c = true;\n{old}\n");
    assert_eq!(
        type_errors(&src),
        [unfixed(
            "5",
            "y = if c { 1 } else { 5r / 2 };",
            "y = if c { 1 } else { 5.0f64 / 2 };"
        )]
    );
    assert_eq!(value(&format!("{rat}\ny = g(false);\n"), "y"), "5r/2r");
    assert_eq!(value(&format!("{f64}\ny = g(false);\n"), "y"), "2.5");
    for (defs, call) in [
        ("c = true;\n", "y = g(c);"),
        ("", "y = g(true);"),
        ("k(positional c: bool) = g(c);\n", "y = k(true);"),
        (
            "k(positional c: bool) = g(c);\nm(positional c: bool) = k(c);\n",
            "y = m(false);",
        ),
    ] {
        let src = format!("{g}\n{defs}{call}\n");
        branch_division_names_the_one(&src);
    }
}

#[test]
fn a_decimal_a_call_gives_a_carrier_stays_accepted() {
    // The literal has a suffix; it joins the class of the parameter, which the argument
    // fixes; and it joins the class beside an atom the other branch may give.
    let cases = [
        ("f() = 0.5f64;\ny = f();\n", "0.5"),
        ("f() = #bad(0.5f64);\ny = f();\n", "#bad(0.5)"),
        ("f(x) = #bad(x);\ny = f(x: 1.0f64);\n", "#bad(1.0)"),
        (
            "g(x) = if x > 0 { x } else { 0.5 };\ny = g(x: 1.0f64);\n",
            "1.0",
        ),
        (
            "g(x) = if x > 0 { x } else { 0.5 };\ny = g(x: -1r);\n",
            "1r/2r",
        ),
        (
            "f(positional x) = if x > 0 { 1 / x } else { -1.5 };\ny = f(2r);\n",
            "1r/2r",
        ),
    ];
    for (src, v) in cases {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
        assert_eq!(value(src, "y"), v, "{src}");
    }
}

#[test]
fn a_literal_branch_joins_a_class_beside_atoms() {
    // DESIGN.md L1.26a: a literal joins the class of a parameter "as a branch of an `if` whose
    // other branch is of a class"; the other branch may also give `#divByZero`.
    assert_eq!(
        sig("f(positional x) = if x > 0 { 1 / x } else { -1.5 };\n", "f"),
        "T -> T | #divByZero for T in f32 | f64 | rat"
    );
    assert_eq!(
        sig(
            "f(positional x) = if x > 0 { x / x } else { 1 + 1 };\n",
            "f"
        ),
        "T -> T | #divByZero for T in f32 | f64 | rat"
    );
}

/// TESTS-branch-kept-op-beside-atoms: `Ck::branches` keeps the value of an operation on
/// integer literals alone (`1 + 1`, a kept operation) only where the other branch is of no
/// class; where the other branch is a class beside atoms (`x / x`, `T | #divByZero`), the
/// operation joins the class as a literal does. The case above has the operation in the
/// `else`; these are its siblings: the operation in the `then`, the values at calls that fix
/// the class, and the same operation beside a branch of atoms alone, which is of no class and
/// so keeps the operation's value.
#[test]
fn a_kept_operation_beside_a_class_with_atoms_joins_the_class_in_either_branch() {
    let swapped = "f(positional x) = if x > 0 { 1 + 1 } else { x / x };\n";
    assert_eq!(
        sig(swapped, "f"),
        "T -> T | #divByZero for T in f32 | f64 | rat"
    );
    let cases = [
        (format!("{swapped}y = f(-1.0f64);\n"), "1.0"),
        (format!("{swapped}y = f(2.0f64);\n"), "2.0"),
        (format!("{swapped}y = f(-2r);\n"), "1r"),
        (
            "f(positional x) = if x > 0 { x / x } else { 1 + 1 };\ny = f(-1r);\n".to_string(),
            "2r",
        ),
        (
            "f(positional x) = if x > 0 { x / x } else { 1 + 1 };\ny = f(3.0f32);\n".to_string(),
            "1.0f32",
        ),
    ];
    for (src, v) in &cases {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
        assert_eq!(value(src, "y"), *v, "{src}");
    }
    // Beside atoms alone the other branch is of no class: the operation keeps its value.
    assert_eq!(
        sig(
            "f(positional c: bool) = if c { 1 + 1 } else { #bad };\n",
            "f"
        ),
        "bool -> 2 | #bad"
    );
}

#[test]
fn the_divisions_in_two_branched_parts_of_a_value_are_each_rejected() {
    // Each `if` is its own place, so each division is one rejection at its own literal. (A
    // plain tuple of divisions is one message: `tuples::the_divisions_of_a_tuple_are_rejected_
    // in_one_message`.)
    let old = "y = (if c { 1 / 2 } else { 1 }, if c { 1 / 4 } else { 2 });";
    let src = format!("c = true;\n{old}\n");
    assert_eq!(
        type_errors(&src),
        [
            unfixed(
                "1",
                "y = (if c { 1r / 2 } else { 1 }, if c { 1 / 4 } else { 2 });",
                "y = (if c { 1.0f64 / 2 } else { 1 }, if c { 1 / 4 } else { 2 });"
            ),
            unfixed(
                "1",
                "y = (if c { 1 / 2 } else { 1 }, if c { 1r / 4 } else { 2 });",
                "y = (if c { 1 / 2 } else { 1 }, if c { 1.0f64 / 4 } else { 2 });"
            ),
        ]
    );
    // With both fixed, and with decimals there, the value is accepted.
    for fixed in [
        "y = (if c { 1r / 2 } else { 1 }, if c { 1r / 4 } else { 2 });",
        "y = (if c { 0.5 } else { 1 }, if c { 0.25 } else { 2 });",
    ] {
        let src = format!("c = true;\n{fixed}\n");
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{fixed}");
    }
}

/// `y = (0 / 2, 1 / 2, …);`, `n` divisions of integer literals on one line.
pub(super) fn divisions(n: usize) -> String {
    let parts: Vec<String> = (0..n).map(|i| format!("{i} / 2")).collect();
    format!("y = ({});\n", parts.join(", "))
}

/// The diagnostics `zedc` prints for `src`, which it rejects.
pub(super) fn printed(src: &str) -> String {
    zedc::run::load(src.as_bytes()).err().expect("rejected")
}

/// A chain of `n` functions, each returning a call of the one before, the first returning
/// `body`, and `n` bindings, each a call of the last.
pub(super) fn chain(n: usize, body: &str) -> String {
    let mut src = format!("c0() = {body};\n");
    for k in 1..=n {
        src += &format!("c{k}() = c{}();\n", k - 1);
    }
    for i in 0..n {
        src += &format!("y{i} = c{n}();\n");
    }
    src
}

#[test]
fn many_divisions_on_one_line_print_the_line_once_in_one_message() {
    // A small instance of the benchmark
    // `bench::tuple_rest::many_divisions_on_one_line_print_the_line_once`.
    let src = divisions(5);
    assert_eq!(
        printed(&src).matches(&src[..20]).count(),
        1,
        "the line is printed once"
    );
    assert_eq!(type_errors(&src).len(), 1);
}

#[test]
fn calls_of_a_chain_that_returns_a_division_are_one_error() {
    // A small instance of the benchmark
    // `bench::tuple_rest::many_calls_of_a_long_chain_check_in_linear_time`.
    let errors = type_errors(&chain(2, "1 / 2"));
    assert_eq!(errors.len(), 1, "{errors:?}");
    // With a decimal the chain returns an `f64`.
    assert_eq!(value(&chain(2, "0.5"), "y1"), "0.5");
}

#[test]
fn a_declared_parameter_or_an_f64_operand_fixes_the_literals_of_a_value() {
    // Plan row LIT-op-top: `id(1 / 2)` with `id(x: f64)` at the top level was rejected as a
    // decimal nothing fixes; the parameter fixes the `/` at `f64`, as a written type does.
    let id = "id(positional x: f64) = x;\n";
    assert_eq!(value(&format!("{id}y = id(1 / 2);\n"), "y"), "0.5");
    assert_eq!(value(&format!("{id}y = id(1 - 3 * 2);\n"), "y"), "-5.0");
    // Plan row LIT-result-at-operator: the `f64` operand of `*` settles the literal results of
    // `g`; `*` was refused with "* does not take (1, 1.0f64)". (A declared binding,
    // `z: f64 = g(true)`, is row LIT-decl-binding, pending step L10.)
    let g = "g(positional c: bool) = if c { 1 } else { 2.5 };\n";
    assert_eq!(value(&format!("{g}z = g(true) * 1.0f64;\n"), "z"), "1.0");
    assert_eq!(value(&format!("{g}z = 1.0f64 * g(false);\n"), "z"), "2.5");
}

#[test]
fn a_hole_of_literal_branches_reads_alike_in_a_function_and_outside_one() {
    // Plan row LIT-hole-in-function: the hole was accepted in a function and rejected outside
    // one. A decimal that nothing fixes takes `f64` (DESIGN.md step L1.26b, author 2026-11-12),
    // so it is accepted in both, with the same text.
    let hole = "\"${if x > 0.0f64 { 0.5 } else { 1 }}\"";
    let f = format!("f(positional x: f64) = {hole};\ns = f(1.0f64);\n");
    let top = format!("x = 1.0f64;\ns = {hole};\n");
    assert_eq!(value(&f, "s"), value(&top, "s"));
    assert_eq!(value(&top, "s"), "\"0.5\"");
}
