//! Where a loose atom stops (DESIGN.md sec:failure, *Where a loose atom stops*, and rule 6 of
//! sec:type_resolution; zed ATOM-BUBBLE-STUDY.md): an atom a function or lambda body makes, and
//! that no argument of a call gives, passes out of the body to the function's result, so the
//! call gives it; and the miss atom of a read through a parameter with no written type is the
//! one the bound argument's type gives (`#outOfBounds` for `m.args`, a `CommandLine`), not one
//! fixed when the body is checked (CHK-index-else-bubble).
//!
//! Each program runs with no arguments. Each accepted program has a negative control: the same
//! program without the `else`, rejected at the `m.stdout <-` write, naming `#outOfBounds`.

use super::type_errors;
use zed_tests::step_helpers::l01_19a_command_line::run;

/// `src` is accepted, and run with no arguments it prints `want`.
fn prints(name: &str, src: &str, want: &str) {
    assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
    let out = run(name, src, &["--"]);
    assert_eq!(out.status, 0, "{src}\n{}", out.stderr);
    assert_eq!(out.stdout, want, "{src}");
}

/// `src` is rejected once, at the write `m.stdout <- value`, whose value may be `#outOfBounds`.
fn rejected_at_write(src: &str, value: &str) {
    rejected_at_write_as(src, value, value);
}

/// [`rejected_at_write`], where the repair writes `value` as `operand` before its `else`: the
/// repair puts a value in parentheses unless it is made only of letters, digits and `_.:[]()`
/// (zedc-check's `else_operand`), needed or not.
fn rejected_at_write_as(src: &str, value: &str, operand: &str) {
    rejected_at_write_of(src, value, operand, "String");
}

/// [`rejected_at_write_as`], where the value is `ty | #outOfBounds`.
fn rejected_at_write_of(src: &str, value: &str, operand: &str, ty: &str) {
    let expected = format!(
        "A `Lines` port takes a `String` or a family of strings: \
         `m.stdout <- {value} : {ty} | #outOfBounds`. \
         Try `m.stdout <- {operand} else \"\";` instead. [{value}]"
    );
    assert_eq!(type_errors(src), [expected], "{src}");
}

/// `main` binding `a` to `call else #outOfBounds -> "none"` and writing it; without the `else`
/// when `handled` is false.
fn main_writing(call: &str, handled: bool) -> String {
    let tail = if handled {
        " else #outOfBounds -> \"none\""
    } else {
        ""
    };
    format!("main(m: MainArgs) {{\n  a = {call}{tail};\n  m.stdout <- a;\n}}\n")
}

/// Each form of a body that makes `#outOfBounds` from a read of `m.args` through a parameter
/// with no written type, and the call that gives it (study appendix: q/call_body, q/return,
/// q/lambda, q/call_body_two, q/a10_trim, q/a10_g, r/arg_inner, r/typed_param).
const FORMS: &[(&str, &str, &str)] = &[
    (
        "bubble_call_body",
        "h(args) = args[0] ++ \"!\";\n",
        "h(args: m.args)",
    ),
    (
        "bubble_return",
        "h(args) { y = args[0]; return y ++ \"!\"; }\n",
        "h(args: m.args)",
    ),
    (
        "bubble_two_levels",
        "h(args) = args[0] ++ \"!\";\ng(args) = h(args: args) ++ \"?\";\n",
        "g(args: m.args)",
    ),
    (
        "bubble_trim",
        "r(args, k) = trim(args[k]);\n",
        "r(args: m.args, k: 0)",
    ),
    (
        "bubble_applied",
        "r(g, args, k) = g(args[k]);\n",
        "r(g: (p) -> p ++ \"!\", args: m.args, k: 0)",
    ),
    (
        "bubble_applied_typed",
        "r(g, args, k) = g(args[k]);\n",
        "r(g: (p: String) -> p ++ \"!\", args: m.args, k: 0)",
    ),
    (
        "bubble_inner",
        "h(p) = p[0] ++ \"!\";\n",
        "h(p: (m.args[0], 1))",
    ),
    (
        "bubble_typed",
        "h(args: [String]) = args[0] ++ \"!\";\n",
        "h(args: m.args)",
    ),
];

#[test]
fn an_atom_a_body_makes_joins_the_result_of_the_call() {
    for (name, helper, call) in FORMS {
        prints(
            name,
            &format!("{helper}{}", main_writing(call, true)),
            "none\n",
        );
    }
}

#[test]
fn without_the_else_each_form_is_rejected_at_the_write() {
    for (_, helper, call) in FORMS {
        rejected_at_write(&format!("{helper}{}", main_writing(call, false)), "a");
    }
}

#[test]
fn an_atom_a_lambda_body_makes_joins_the_result_of_its_application() {
    let src = |tail: &str| {
        format!(
            "main(m: MainArgs) {{\n  g = (args) -> args[0] ++ \"!\";\n  \
             a = g(m.args){tail};\n  m.stdout <- a;\n}}\n"
        )
    };
    prints(
        "bubble_lambda",
        &src(" else #outOfBounds -> \"none\""),
        "none\n",
    );
    rejected_at_write(&src(""), "a");
}

/// The A10 program (QUESTIONS.md A10): `r` reads the file the `k`th argument names.
fn a10(handled: bool) -> String {
    let oob = if handled {
        "(r(fs: fs, args: args, k: K) else #outOfBounds -> \"no argument\")"
    } else {
        "r(fs: fs, args: args, k: K)"
    };
    let one = |k: &str| {
        format!(
            "({} else #notFound -> \"missing\") else #ioError -> \"unreadable\"",
            oob.replace('K', k)
        )
    };
    format!(
        "r(fs, args, k) = fs[args[k]];\nmain(m: MainArgs) {{\n  fs = main::files;\n  \
         args = m.args;\n  a = {};\n  b = {};\n  m.stdout <- \"${{a}}|${{b}}\";\n}}\n",
        one("0"),
        one("1")
    )
}

#[test]
fn the_a10_program_prints_no_argument_twice() {
    prints("bubble_a10", &a10(true), "no argument|no argument\n");
}

#[test]
fn the_a10_program_without_its_out_of_bounds_else_is_rejected_at_the_write() {
    rejected_at_write_as(&a10(false), "\"${a}|${b}\"", "(\"${a}|${b}\")");
}

#[test]
fn the_miss_atom_of_a_read_through_a_parameter_is_the_bound_arguments() {
    // `args[0]` with `args` bound to a `CommandLine` misses with `#outOfBounds`, so the `else`
    // handles every atom the read gives (r/need_oob).
    prints(
        "bubble_need_oob",
        "h(args) = args[0] else #outOfBounds -> \"x\";\n\
         main(m: MainArgs) {\n  m.stdout <- h(args: m.args);\n}\n",
        "x\n",
    );
    // `else #notFound` handles an atom this read never gives, so its `#outOfBounds` reaches the
    // write (r/need_nf, the negative control).
    rejected_at_write_as(
        "h(args) = args[0] else #notFound -> \"x\";\n\
         main(m: MainArgs) {\n  m.stdout <- h(args: m.args);\n}\n",
        "h(args: m.args)",
        "(h(args: m.args))",
    );
}

#[test]
fn an_unhandled_atom_of_a_call_is_rejected_at_the_write() {
    // q/call_body_unhandled: the call is accepted, and the atom reaches the port.
    rejected_at_write(
        &format!(
            "h(args) = args[0] ++ \"!\";\n{}",
            main_writing("h(args: m.args)", false)
        ),
        "a",
    );
}

/// The forms zedc already handled before CHK-index-else-bubble (study appendix), each with
/// what it prints with no arguments.
const HANDLED: &[(&str, &str, &str)] = &[
    (
        "bubble_op",
        "main(m: MainArgs) {\n  a = (m.args[0] ++ \"!\") else #outOfBounds -> \"none\";\n  \
         m.stdout <- a;\n}\n",
        "none\n",
    ),
    (
        "bubble_call_arg",
        "h(s) = s ++ \"!\";\nmain(m: MainArgs) {\n  \
         a = h(s: m.args[0]) else #outOfBounds -> \"none\";\n  m.stdout <- a;\n}\n",
        "none\n",
    ),
    (
        "bubble_default_param",
        "h(s = \"q\", t) = s ++ t;\nmain(m: MainArgs) {\n  \
         a = h(t: m.args[0]) else #outOfBounds -> \"none\";\n  m.stdout <- a;\n}\n",
        "none\n",
    ),
    (
        "bubble_arg_pass",
        "h(s) = s ++ \"!\";\nmain(m: MainArgs) {\n  a = h(s: m.args[0]);\n  \
         m.stdout <- a else #outOfBounds -> \"none\";\n}\n",
        "none\n",
    ),
    (
        "bubble_callee",
        "up(s) = s ++ \"!\";\ndn(s) = s ++ \"?\";\nmain(m: MainArgs) {\n  fs = [up, dn];\n  \
         a = (fs[int(m.args[0]) else #invalid -> 0])(s: \"x\") else #outOfBounds -> \"none\";\n  \
         m.stdout <- a;\n}\n",
        "none\n",
    ),
    (
        "bubble_index_key",
        "main(m: MainArgs) {\n  t = [\"a\", \"b\"];\n  \
         a = t[int(m.args[0])] else #outOfBounds -> \"none\";\n  m.stdout <- a;\n}\n",
        "none\n",
    ),
    (
        "bubble_member",
        "main(m: MainArgs) {\n  a = m.args[0].trim() else #outOfBounds -> \"none\";\n  \
         m.stdout <- a;\n}\n",
        "none\n",
    ),
    (
        "bubble_safe",
        "main(m: MainArgs) {\n  a = m.args[0]?.trim() else #outOfBounds -> \"none\";\n  \
         m.stdout <- a;\n}\n",
        "none\n",
    ),
    (
        "bubble_interp",
        "main(m: MainArgs) {\n  a = \"v${m.args[0]}\" else #outOfBounds -> \"none\";\n  \
         m.stdout <- a;\n}\n",
        "none\n",
    ),
    (
        "bubble_if_arm",
        "main(m: MainArgs) {\n  \
         a = (if m.args == m.args { m.args[0] } else { \"x\" }) else #outOfBounds -> \"none\";\n  \
         m.stdout <- a;\n}\n",
        "none\n",
    ),
    (
        "bubble_if_cond",
        "main(m: MainArgs) {\n  \
         a = (if m.args[0] < \"a\" { \"A\" } else { \"B\" }) else #outOfBounds -> \"none\";\n  \
         m.stdout <- a;\n}\n",
        "none\n",
    ),
    (
        "bubble_block",
        "main(m: MainArgs) {\n  \
         a = { y = m.args[0]; y ++ \"!\" } else #outOfBounds -> \"none\";\n  m.stdout <- a;\n}\n",
        "none\n",
    ),
    (
        "bubble_binding",
        "main(m: MainArgs) {\n  y = m.args[0];\n  z = y ++ \"!\";\n  \
         m.stdout <- z else #outOfBounds -> \"none\";\n}\n",
        "none\n",
    ),
    (
        "bubble_else_default",
        "main(m: MainArgs) {\n  a = m.args[0] else m.args[1];\n  \
         m.stdout <- a else #outOfBounds -> \"none\";\n}\n",
        "none\n",
    ),
    (
        "bubble_in",
        "main(m: MainArgs) {\n  a = (m.args[0] in [\"a\", \"b\"]) else #outOfBounds -> false;\n  \
         m.stdout <- \"${a}\";\n}\n",
        "false\n",
    ),
    (
        "bubble_capture",
        "main(m: MainArgs) {\n  g = (k) -> m.args[k] ++ \"!\";\n  \
         a = g(0) else #outOfBounds -> \"none\";\n  m.stdout <- a;\n}\n",
        "none\n",
    ),
    (
        "bubble_power",
        "main(m: MainArgs) {\n  a = (int(m.args[0]) ^ 2) else #outOfBounds -> 0;\n  \
         m.stdout <- \"${a else #invalid -> 1}\";\n}\n",
        "0\n",
    ),
    // `==` and `is` hold no atom: the test is false, or the atom is tested.
    (
        "bubble_eq",
        "main(m: MainArgs) {\n  a = m.args[0] == \"a\";\n  m.stdout <- \"${a}\";\n}\n",
        "false\n",
    ),
    (
        "bubble_if_eq",
        "main(m: MainArgs) {\n  \
         a = (if m.args[0] == \"a\" { \"A\" } else { \"B\" }) else #outOfBounds -> \"none\";\n  \
         m.stdout <- a;\n}\n",
        "B\n",
    ),
    (
        "bubble_is",
        "main(m: MainArgs) {\n  y = m.args[0];\n  \
         a = if y is #outOfBounds { \"none\" } else { y ++ \"!\" };\n  m.stdout <- a;\n}\n",
        "none\n",
    ),
    // A display holds the atom as data; the read of the element gives it again.
    (
        "bubble_tuple",
        "main(m: MainArgs) {\n  t = (m.args[0], \"b\");\n  \
         a = t[0] else #outOfBounds -> \"none\";\n  m.stdout <- a;\n}\n",
        "none\n",
    ),
    (
        "bubble_array",
        "main(m: MainArgs) {\n  ys = [m.args[0], \"b\"];\n  \
         a = ys[0] else #outOfBounds -> \"none\";\n  m.stdout <- a;\n}\n",
        "none\n",
    ),
    (
        "bubble_map",
        "main(m: MainArgs) {\n  ys = [0, 1].map((i) -> m.args[i]);\n  \
         a = ys[0] else #outOfBounds -> \"none\";\n  m.stdout <- a;\n}\n",
        "none\n",
    ),
    (
        "bubble_unread",
        "main(m: MainArgs) {\n  y = m.args[0];\n  m.stdout <- \"done\";\n}\n",
        "done\n",
    ),
];

#[test]
fn the_forms_that_pass_an_atom_on_or_hold_it_as_data() {
    for (name, src, want) in HANDLED {
        prints(name, src, want);
    }
}

#[test]
fn a_port_write_an_interpolation_and_an_operator_reject_an_unhandled_atom() {
    for (src, value) in [
        (
            "main(m: MainArgs) {\n  m.stdout <- m.args[0];\n}\n",
            "m.args[0]",
        ),
        (
            "main(m: MainArgs) {\n  y = m.args[0];\n  z = y ++ \"!\";\n  m.stdout <- z;\n}\n",
            "z",
        ),
        (
            "main(m: MainArgs) {\n  t = (m.args[0], \"b\");\n  a = t[0];\n  m.stdout <- a;\n}\n",
            "a",
        ),
    ] {
        rejected_at_write(src, value);
    }
}

#[test]
fn a_statement_and_an_underscore_stop_an_atom() {
    // An expression statement and `_` are boundaries: the atom is rejected there, not passed on.
    let errors = type_errors("main(m: MainArgs) {\n  _ = m.args[0];\n  m.stdout <- \"done\";\n}\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with(
            "`_` drops a loose failure this value may be, #outOfBounds: `_` drops only a failure"
        ),
        "{errors:?}"
    );
    let errors = type_errors("main(m: MainArgs) {\n  m.args[0];\n  m.stdout <- \"done\";\n}\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("Statement has no effect: `m.args[0]`"),
        "{errors:?}"
    );
}

/// Bodies that handle the atom a read through `args` makes, each with what it prints with no
/// arguments, and the same body with a handler of an atom the read never gives, or none
/// (study probes p3): the atom reaches the call, which `main` writes unhandled, as a value of
/// the last field's type or `#outOfBounds`.
const HANDLED_IN_BODY: &[(&str, &str, &str, &str, &str)] = &[
    (
        "bubble_body_else",
        "h(args) = (args[0] ++ \"!\") else #outOfBounds -> \"x\";\n",
        "h(args) = (args[0] ++ \"!\") else #notFound -> \"x\";\n",
        "x\n",
        "String",
    ),
    (
        "bubble_body_plain_else",
        "h(args) = (args[0] ++ \"!\") else \"x\";\n",
        "h(args) = args[0] ++ \"!\";\n",
        "x\n",
        "String",
    ),
    (
        "bubble_body_is",
        "h(args) { y = args[0]; return if y is #outOfBounds { \"none\" } else { y ++ \"!\" }; }\n",
        "h(args) { y = args[0]; return if y is #ioError { \"none\" } else { y ++ \"!\" }; }\n",
        "none\n",
        "String",
    ),
    // `==` tests the atom, and `<` passes it on, as at the top level.
    (
        "bubble_body_eq",
        "h(args) = if args[0] ++ \"!\" == \"a!\" { \"A\" } else { \"B\" };\n",
        "h(args) = if args[0] ++ \"!\" < \"a!\" { \"A\" } else { \"B\" };\n",
        "B\n",
        "\"A\" | \"B\"",
    ),
];

#[test]
fn an_atom_a_body_handles_does_not_reach_the_call() {
    let main = "main(m: MainArgs) {\n  m.stdout <- h(args: m.args);\n}\n";
    for (name, handled, unhandled, want, ty) in HANDLED_IN_BODY {
        prints(name, &format!("{handled}{main}"), want);
        rejected_at_write_of(
            &format!("{unhandled}{main}"),
            "h(args: m.args)",
            "(h(args: m.args))",
            ty,
        );
    }
}

#[test]
fn an_atom_a_body_handles_does_not_reach_a_call_two_levels_out() {
    let src = |handler: &str| {
        format!(
            "h(args) = (args[0] ++ \"!\") else {handler} -> \"x\";\n\
             g(args) = h(args: args) ++ \"?\";\n\
             main(m: MainArgs) {{\n  m.stdout <- g(args: m.args);\n}}\n"
        )
    };
    prints("bubble_body_else_two", &src("#outOfBounds"), "x?\n");
    rejected_at_write_as(&src("#notFound"), "g(args: m.args)", "(g(args: m.args))");
}

#[test]
fn an_atom_one_reader_handles_and_another_passes_on_reaches_the_call() {
    // `b`'s `==` handles the atom of its read; `a`'s `++` passes its own on to the result.
    let src = |tail: &str| {
        format!(
            "h(args) {{ a = args[0] ++ \"!\"; b = (args[0] ++ \"?\") == \"x?\"; return a; }}\n\
             main(m: MainArgs) {{\n  m.stdout <- h(args: m.args){tail};\n}}\n"
        )
    };
    prints(
        "bubble_two_uses",
        &src(" else #outOfBounds -> \"none\""),
        "none\n",
    );
    rejected_at_write_as(&src(""), "h(args: m.args)", "(h(args: m.args))");
}

#[test]
fn an_atom_a_body_drops_with_an_underscore_is_still_rejected() {
    // `_` drops no loose failure (DESIGN.md sec:failure): the atom stops there, and the call
    // keeps its rejection.
    let errors = type_errors(
        "h(args) { _ = args[0] ++ \"!\"; return \"y\"; }\n\
         main(m: MainArgs) {\n  m.stdout <- h(args: m.args);\n}\n",
    );
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("`h` gives String | #outOfBounds here, which is not String"),
        "{errors:?}"
    );
}

/// `n` helpers whose body makes `#outOfBounds`, and `main` handling it at each call (the
/// benchmark `bench::bubble::many_calls_giving_a_body_s_atom_scale`).
pub(super) fn helpers_giving_their_atom(n: usize) -> String {
    let mut src: String = (0..n)
        .map(|i| format!("h{i}(args) = args[0] ++ \"{i}\";\n"))
        .collect();
    src.push_str("main(m: MainArgs) {\n");
    for i in 0..n {
        src.push_str(&format!(
            "  a{i} = h{i}(args: m.args) else #outOfBounds -> \"none\";\n"
        ));
    }
    src.push_str("  m.stdout <- a0;\n}\n");
    src
}

/// `n` helpers, each passing on the atom of the one before it, and `main` handling it at the
/// last (the benchmark `bench::bubble::a_chain_of_calls_passing_a_body_s_atom_on_scale`).
pub(super) fn chain_of_helpers(n: usize) -> String {
    let mut src = String::from("h0(args) = args[0] ++ \"!\";\n");
    for i in 1..n {
        src.push_str(&format!("h{i}(args) = h{}(args: args) ++ \"!\";\n", i - 1));
    }
    src.push_str(&format!(
        "main(m: MainArgs) {{\n  m.stdout <- h{}(args: m.args) else #outOfBounds -> \"none\";\n}}\n",
        n - 1
    ));
    src
}

/// One helper whose body passes its read's atom through `n` bindings to its result, and
/// `main` handling it (the benchmark `bench::bubble::a_body_of_many_bindings_scale`).
pub(super) fn body_of_bindings(n: usize) -> String {
    let mut src = String::from("h(args) {\n  y0 = args[0];\n");
    for i in 1..n {
        src.push_str(&format!("  y{i} = y{} ++ \"!\";\n", i - 1));
    }
    src.push_str(&format!(
        "  return y{};\n}}\nmain(m: MainArgs) {{\n  m.stdout <- h(args: m.args) else #outOfBounds -> \"none\";\n}}\n",
        n - 1
    ));
    src
}

#[test]
fn small_instances_of_the_bubble_benchmarks_are_accepted() {
    for src in [
        helpers_giving_their_atom(3),
        chain_of_helpers(3),
        body_of_bindings(3),
    ] {
        assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
    }
    prints("bubble_chain", &chain_of_helpers(3), "none\n");
    prints("bubble_bindings", &body_of_bindings(3), "none\n");
}
