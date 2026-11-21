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
    // `_` drops no loose failure (DESIGN.md sec:failure, crossing (7)): the atom stops there,
    // and is rejected there, naming the call that makes it, with the repair as code; the
    // call's value, `"y"`, holds no atom, so the write is not rejected (MSG-atom-stop-in-body).
    let src = |stmt: &str| {
        format!(
            "h(args) {{ {stmt} return \"y\"; }}\n\
             main(m: MainArgs) {{\n  m.stdout <- h(args: m.args);\n}}\n"
        )
    };
    assert_eq!(
        type_errors(&src("_ = args[0] ++ \"!\";")),
        [
            "`_` drops a loose failure: `args[0]` may be #outOfBounds when `h` is called as \
          `h(args: m.args)`. Try `_ = args[0] ++ \"!\" else #ok;` instead. \
          [_ = args[0] ++ \"!\";]"
        ],
    );
    // The repair the message gives is accepted, and runs.
    prints(
        "bubble_underscore_repaired",
        &src("_ = args[0] ++ \"!\" else #ok;"),
        "y\n",
    );
}

#[test]
fn an_atom_a_body_drops_in_a_statement_is_rejected_at_the_statement() {
    // An expression statement drops its value (crossing (7)); a call there that writes to
    // `out` is legal, so the body alone, with no type on `args`, is accepted, and the atom
    // the call makes is rejected at the statement.
    let src = |stmt: &str| {
        format!(
            "say(s: String, out: Lines) {{ out <- s; }}\n\
             h(args, out: Lines) {{ {stmt} }}\n\
             main(m: MainArgs) {{\n  h(args: m.args, out: m.stdout);\n}}\n"
        )
    };
    assert_eq!(
        type_errors(&src("say(s: args[0], out: out);")),
        [
            "A statement drops a loose failure: `args[0]` may be #outOfBounds when `h` is called \
          as `h(args: m.args, out: m.stdout)`. Try `_ = say(s: args[0], out: out) else #ok;` \
          instead. [say(s: args[0], out: out);]"
        ],
    );
    // The headline's repair is accepted and, with no arguments, skips the call; handling
    // the read itself keeps the call.
    prints(
        "bubble_statement_dropped",
        &src("_ = say(s: args[0], out: out) else #ok;"),
        "",
    );
    prints(
        "bubble_statement_repaired",
        &src("say(s: args[0] else \"none\", out: out);"),
        "none\n",
    );
}

#[test]
fn an_atom_a_default_under_a_written_type_takes_is_rejected_at_the_default() {
    // A default is a value of its parameter's written type (crossing (5)): the atom a read
    // through an undeclared parameter makes there, once the call binds it, is a type error
    // at the default, whose repairs are an `else` or the wider type.
    let src = |param: &str| {
        format!(
            "h(positional xs, {param}) = s ++ \"!\";\n\
             main(m: MainArgs) {{\n  m.stdout <- h(m.args);\n}}\n"
        )
    };
    // The default's own type is `String` whatever `xs` holds, so `h` alone is accepted; a
    // default of `xs[0]` alone has no type until a call, and `h`'s own check refuses it
    // (the message of row MSG-default-unknown-type).
    assert_eq!(
        type_errors(&src("s: String = \"<\" ++ xs[0]")),
        [
            "The default of `s` is not `String`: `\"<\" ++ xs[0]` may be #outOfBounds when `h` \
          is called as `h(m.args)`. Try `s: String | #outOfBounds = \"<\" ++ xs[0]` instead. \
          [s: String = \"<\" ++ xs[0]]"
        ],
    );
    prints(
        "bubble_default_repaired",
        &src("s: String = \"<\" ++ xs[0] else \"none\""),
        "none!\n",
    );
}

#[test]
fn an_atom_a_body_writes_to_a_port_is_rejected_at_the_write() {
    // A port write takes no loose failure (crossing (8)): the body alone, with no type on
    // `args`, is accepted, and the atom the call makes is rejected at the write in the body.
    let src = |stmt: &str| {
        format!(
            "h(args, out: Lines) {{ {stmt} }}\n\
             main(m: MainArgs) {{\n  h(args: m.args, out: m.stdout);\n}}\n"
        )
    };
    // Pushed as it is, the value's type at the call is `String | #outOfBounds`, which the
    // push's own check refuses (row PORT-untyped-arg); before, nothing refused it and the
    // run pushed #outOfBounds and exited 1.
    assert_eq!(
        type_errors(&src("out <- args[0];")),
        [
            "A `Lines` port takes a `String` or a family of strings: `out <- args[0] : String | \
          #outOfBounds`. Try `out <- args[0] else \"\";` instead. [args[0]]"
        ],
    );
    // Through an operation, the atom is one the call makes in the body (`gives_made`), and
    // the write is where it stops.
    assert_eq!(
        type_errors(&src("out <- args[0] ++ \"!\";")),
        [
            "A port write does not take a loose failure: `args[0]` may be #outOfBounds when `h` \
          is called as `h(args: m.args, out: m.stdout)`, and `out <- args[0] ++ \"!\"` writes \
          it. [out <- args[0] ++ \"!\";]"
        ],
    );
    prints(
        "bubble_write_repaired",
        &src("out <- args[0] else \"none\";"),
        "none\n",
    );
}

#[test]
fn a_body_s_push_of_an_untyped_parameter_is_checked_at_each_call() {
    // A `Lines` port takes text or a family of strings. The push in `h` has no type to check
    // where it is written, so each call checks what it passes (row PORT-untyped-arg): `5` is
    // rejected at the push, a string and a family of strings are accepted and printed.
    let src = |arg: &str| {
        format!(
            "h(x, out: Lines) {{ out <- x; }}\n\
             main(m: MainArgs) {{\n  h(x: {arg}, out: m.stdout);\n}}\n"
        )
    };
    assert_eq!(
        type_errors(&src("5")),
        [
            "A `Lines` port takes a `String` or a family of strings: `out <- x : 5`. Try \
          `out <- \"${x}\";` instead. [x]"
        ],
    );
    // The row's own example: a positional parameter, given `3`.
    assert_eq!(
        type_errors(
            "say(positional s, out: Lines) { out <- s; }\n\
             main(m: MainArgs) {\n  say(3, out: m.stdout);\n}\n"
        ),
        [
            "A `Lines` port takes a `String` or a family of strings: `out <- s : 3`. Try \
          `out <- \"${s}\";` instead. [s]"
        ],
    );
    prints("bubble_push_string", &src("\"a\""), "a\n");
    prints("bubble_push_family", &src("[\"a\", \"b\"]"), "a\nb\n");
}

#[test]
fn a_pushed_family_whose_entry_is_an_untyped_parameter_is_checked_at_each_call() {
    // `[x]` is a family whose entry is the class of `x`: the push waits for it as for `x`
    // pushed alone, and each call checks the family with the entry it passes, the rest kept
    // (row PORT-untyped-arg-gaps).
    let src = |arg: &str| {
        format!(
            "h(x, out: Lines) {{ out <- [x]; }}\n\
             main(m: MainArgs) {{\n  h(x: {arg}, out: m.stdout);\n}}\n"
        )
    };
    assert_eq!(
        type_errors(&src("5")),
        ["A `Lines` port takes a `String` or a family of strings: `out <- [x] : 0 -> 5`. [[x]]"],
    );
    prints("bubble_push_entry_string", &src("\"a\""), "a\n");
}

#[test]
fn a_pushed_family_is_checked_at_every_depth_of_nesting() {
    // A `Lines` port writes a family one line per entry at any depth of nesting (DESIGN.md
    // sec:ports), so each entry at each depth must be a string or a family (row
    // PROOF-push-vars-other-var, `push_entries` in zedc-check). Before, only the first level
    // was read: a function in a family was taken, and the run stopped with zedc's message for
    // a bug of its own ("expected data, found a function"); `[[x]]` was not checked at the
    // call.
    let f = "f(positional x: int) = x + 1;\n";
    let push = |value: &str| format!("{f}main(m: MainArgs) {{\n  m.stdout <- {value};\n}}\n");
    for (value, ty) in [
        ("[f]", "0 -> int -> int"),
        ("[[f]]", "0 -> 0 -> int -> int"),
        ("{\"k\" -> f}", "\"k\" -> int -> int"),
    ] {
        assert_eq!(
            type_errors(&push(value)),
            [format!(
                "A `Lines` port takes a `String` or a family of strings: \
                 `m.stdout <- {value} : {ty}`. [{value}]"
            )],
            "{value}"
        );
    }
    prints(
        "bubble_push_nested",
        &push("[[\"a\"], [\"b\", \"c\"]]"),
        "a\nb\nc\n",
    );
    // An untyped parameter two levels down waits for its class as one level down does.
    let src = |arg: &str| {
        format!(
            "h(x, out: Lines) {{ out <- [[x]]; }}\n\
             main(m: MainArgs) {{\n  h(x: {arg}, out: m.stdout);\n}}\n"
        )
    };
    assert_eq!(
        type_errors(&src("5")),
        [
            "A `Lines` port takes a `String` or a family of strings: `out <- [[x]] : 0 -> 0 -> \
          5`. [[[x]]]"
        ],
    );
    prints("bubble_push_nested_entry_string", &src("\"a\""), "a\n");
}

#[test]
fn a_push_that_waits_on_a_class_typed_at_the_end_waits_on_the_rest() {
    // The push waits on the first class of its value, `x`'s. At the end of `h`, `x.upper`
    // has made `x` a `String`, so the push is checked then with `x` a `String`, and waits
    // again on `y`, by then a type variable of `h`: each call checks what it passes for `y`
    // (row PORT-untyped-arg-gaps, case (a) at `Ck::push_vars`). Before, such a `y` was read
    // as no value, and `h(x: "a", y: 5, out: m.stdout)` failed only at run time.
    let src = |y: &str| {
        format!(
            "h(x, y, out: Lines) {{ out <- [x, y, x.upper]; }}\n\
             main(m: MainArgs) {{\n  h(x: \"a\", y: {y}, out: m.stdout);\n}}\n"
        )
    };
    assert_eq!(
        type_errors(&src("5")),
        [
            "A `Lines` port takes a `String` or a family of strings: `out <- [x, y, x.upper] : \
          (0 | 1 | 2) -> 5 | String`. [[x, y, x.upper]]"
        ],
    );
    prints("bubble_push_waits_on_rest", &src("\"b\""), "a\nb\nA\n");
}

#[test]
fn a_push_whose_known_part_cannot_be_text_is_refused_where_it_is_written() {
    // The value of the push is `x` or `5`: whatever `x` becomes, `5` is pushed when `c` is
    // false, so the push is refused in `h` and not left to each call, nor to the run time
    // (row PORT-untyped-arg-gaps). The call passes a number for `x`, which the `if` joins
    // with `5`: a string there is refused at the call as well. The control: with `"z"` in
    // place of `5`, each call checks what it passes for `x`.
    let src = |e: &str, x: &str| {
        format!(
            "h(x, c, out: Lines) {{ out <- if c {{ x }} else {{ {e} }}; }}\n\
             main(m: MainArgs) {{\n  h(x: {x}, c: false, out: m.stdout);\n}}\n"
        )
    };
    assert_eq!(
        type_errors(&src("5", "1")),
        [
            "A `Lines` port takes a `String` or a family of strings: `out <- if c { x } else \
          { 5 } : int | f32 | f64 | rat`. Try `out <- \"${if c { x } else { 5 }}\";` instead. \
          [if c { x } else { 5 }]"
        ],
    );
    assert_eq!(
        type_errors(&src("\"z\"", "5")),
        [
            "A `Lines` port takes a `String` or a family of strings: `out <- if c { x } else \
          { \"z\" } : 5 | \"z\"`. Try `out <- \"${if c { x } else { \"z\" }}\";` instead. \
          [if c { x } else { \"z\" }]"
        ],
    );
    prints("bubble_push_known_part", &src("\"z\"", "\"a\""), "z\n");
}

#[test]
fn a_body_s_else_whose_atom_pattern_has_parts_passes_the_atom_on() {
    // `#outOfBounds()` takes only the atom whose payload is the empty tuple; the miss atom of
    // `args[0]` has none, so it is not handled there and passes on to the call (row
    // CHK-fate-unwalked-forms), which gives `String | #outOfBounds` to the write. A pattern
    // keeps in the type each payload it can fail to match (step L1.27). The control: the bare
    // `#outOfBounds` handles it. The other forms of the row, `#outOfBounds(..)`, a binding
    // `#outOfBounds(i)` and a name `e`, are refused by the parser or by resolution and never
    // reach the checker.
    let src = |pat: &str| {
        format!(
            "h(args) = args[0] else {pat} -> \"none\";\n\
             main(m: MainArgs) {{\n  m.stdout <- h(args: m.args);\n}}\n"
        )
    };
    rejected_at_write_as(
        &src("#outOfBounds()"),
        "h(args: m.args)",
        "(h(args: m.args))",
    );
    prints("bubble_else_bare_pattern", &src("#outOfBounds"), "none\n");
}

#[test]
fn an_atom_a_body_holds_in_a_display_reaches_the_caller_as_data() {
    // A display holds the atom as data (crossing (2)): the call's type is a display of
    // `String | #outOfBounds`, so the caller's `else` takes it, and without that `else` the
    // caller's write is where it stops.
    let src = |e: &str, tail: &str| {
        format!(
            "h(args) = {e};\n\
             main(m: MainArgs) {{\n  m.stdout <- h(args: m.args)[0]{tail};\n}}\n"
        )
    };
    prints(
        "bubble_display_data",
        &src("[args[0]]", " else \"none\""),
        "none\n",
    );
    rejected_at_write_of(
        &src("[args[0]]", ""),
        "h(args: m.args)[0]",
        "(h(args: m.args)[0])",
        "String",
    );
    prints(
        "bubble_display_repaired",
        &src("[args[0] else \"none\"]", " else \"none\""),
        "none\n",
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

/// `n` helpers, each pushing its untyped parameter to a port, and `main` calling each with a
/// string (the benchmark `bench::bubble::many_pushes_of_untyped_parameters_scale`).
pub(super) fn helpers_pushing_their_parameter(n: usize) -> String {
    let mut src: String = (0..n)
        .map(|i| format!("p{i}(x, out: Lines) {{ out <- x; }}\n"))
        .collect();
    src.push_str("main(m: MainArgs) {\n");
    for i in 0..n {
        src.push_str(&format!("  p{i}(x: \"{i}\", out: m.stdout);\n"));
    }
    src.push_str("}\n");
    src
}

/// One helper pushing each of its `n` untyped parameters to a port, called once (the
/// benchmark `bench::bubble::a_body_pushing_many_untyped_parameters_scales`).
pub(super) fn body_pushing_parameters(n: usize) -> String {
    let params: String = (0..n).map(|i| format!("x{i}, ")).collect();
    let pushes: String = (0..n).map(|i| format!("  out <- x{i};\n")).collect();
    let args: String = (0..n).map(|i| format!("x{i}: \"{i}\", ")).collect();
    format!(
        "p({params}out: Lines) {{\n{pushes}}}\n\
         main(m: MainArgs) {{\n  p({args}out: m.stdout);\n}}\n"
    )
}

/// One helper pushing a family of its `n` untyped parameters and `x0.upper`, called once: the
/// push waits on `x0`'s class, which the body's end makes a `String`, then on the classes left,
/// each a type variable of the helper (row PORT-untyped-arg-gaps; the benchmark
/// `bench::bubble::a_body_pushing_a_family_of_many_untyped_parameters_scales`).
pub(super) fn body_pushing_a_family(n: usize) -> String {
    let params: String = (0..n).map(|i| format!("x{i}, ")).collect();
    let entries: String = (0..n).map(|i| format!("x{i}, ")).collect();
    let args: String = (0..n).map(|i| format!("x{i}: \"{i}\", ")).collect();
    format!(
        "p({params}out: Lines) {{\n  out <- [{entries}x0.upper];\n}}\n\
         main(m: MainArgs) {{\n  p({args}out: m.stdout);\n}}\n"
    )
}

/// One helper pushing a family nested `n` deep around its untyped parameter, each level
/// holding the one below twice (`a{i} = [a{i-1}, a{i-1}]`), called once: the push waits on
/// `x`'s class through every level (`push_entries` in zedc-check, row
/// PROOF-push-vars-other-var; the benchmark
/// `bench::bubble::a_push_of_a_family_nested_n_deep_scales`).
pub(super) fn body_pushing_a_nested_family(n: usize) -> String {
    let levels: String = (1..n)
        .map(|i| format!("  a{i} = [a{}, a{}];\n", i - 1, i - 1))
        .collect();
    format!(
        "h(x, out: Lines) {{\n  a0 = [x];\n{levels}  out <- a{};\n}}\n\
         main(m: MainArgs) {{\n  h(x: \"a\", out: m.stdout);\n}}\n",
        n - 1
    )
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

#[test]
fn a_push_in_an_inner_function_of_a_class_around_and_its_own_parameter_is_checked() {
    // The push in `g` holds `x`, a class of `h`, and `y`, `g`'s own parameter, which is named
    // when `g` ends. Each call is checked with what it passes for both: `y` at the call of
    // `g`, `x` at the call of `h` (row PROOF-push-vars-other-route, the need way at
    // `Ck::push_vars` in zedc-check). A number for either is refused; strings are taken.
    let src = |y: &str, x: &str| {
        format!(
            "h(x, out: Lines) {{ g(positional y, o: Lines) {{ o <- [x, y]; }} g({y}, o: out); }}\n\
             main(m: MainArgs) {{ h(x: {x}, out: m.stdout); }}\n"
        )
    };
    assert_eq!(
        type_errors(&src("5", "\"a\"")),
        [
            "A `Lines` port takes a `String` or a family of strings: `o <- [x, y] : (0 | 1) -> \
          int | \"a\"`. [[x, y]]"
        ],
    );
    assert_eq!(
        type_errors(&src("\"b\"", "5")),
        [
            "A `Lines` port takes a `String` or a family of strings: `o <- [x, y] : (0 | 1) -> 5 \
          | String`. [[x, y]]"
        ],
    );
    prints(
        "bubble_push_inner_function",
        &src("\"b\"", "\"a\""),
        "a\nb\n",
    );
}

/// `h` holding an inner `g` whose push holds `x`, `h`'s parameter, and `y`, `g`'s own, with
/// `rest` the statement after `g`, called with `x` given `x`.
fn inner_push(rest: &str, x: &str) -> String {
    format!(
        "h(x, out: Lines) {{ g(positional y, o: Lines) {{ o <- [x, y]; }} {rest} }}\n\
         main(m: MainArgs) {{ h(x: {x}, out: m.stdout); }}\n"
    )
}

/// `h` holding `n` inner functions, none called, each pushing `x`, `h`'s parameter, beside its
/// own `y`, called once: `h`'s signature holds `n` push needs, each with a variable no call
/// binds (the benchmark `bench::bubble::many_uncalled_inner_pushes_scale`).
pub(super) fn body_of_uncalled_inner_pushes(n: usize) -> String {
    let inner: String = (0..n)
        .map(|i| format!("  g{i}(positional y, o: Lines) {{ o <- [x, y]; }}\n"))
        .collect();
    format!(
        "h(x, out: Lines) {{\n{inner}  out <- x.upper;\n}}\n\
         main(m: MainArgs) {{ h(x: \"a\", out: m.stdout); }}\n"
    )
}

/// `h` holding one inner function, not called, pushing `x` and a family of its own `n`
/// parameters, called once: one push need with `n` variables no call binds (the benchmark
/// `bench::bubble::an_uncalled_inner_push_of_many_parameters_scales`).
pub(super) fn uncalled_inner_push_of_parameters(n: usize) -> String {
    let params: String = (0..n).map(|i| format!("positional y{i}, ")).collect();
    let entries: String = (0..n).map(|i| format!(", y{i}")).collect();
    format!(
        "h(x, out: Lines) {{\n  g({params}o: Lines) {{ o <- [x{entries}]; }}\n  out <- x.upper;\n}}\n\
         main(m: MainArgs) {{ h(x: \"a\", out: m.stdout); }}\n"
    )
}

/// `h` of `n` parameters, each pushed where a test against its own type variable `Ti`,
/// written nowhere else, holds (the benchmark
/// `bench::bubble::pushes_narrowed_by_tests_against_type_variables_scale`).
pub(super) fn pushes_narrowed_by_type_variables(n: usize) -> String {
    let params: String = (0..n).map(|i| format!("x{i}, ")).collect();
    let tests: String = (0..n)
        .map(|i| format!("  if x{i} is T{i} {{ out <- x{i}; }};\n"))
        .collect();
    format!("h({params}out: Lines) {{\n{tests}}}\n")
}

/// `text`'s errors from elaboration, which checks it first; none if it elaborates.
fn elab_errors(text: &str) -> Vec<String> {
    zed_tests::step_helpers::l01_16_elaboration::elab(text)
        .err()
        .unwrap_or_default()
}

/// Row PROOF-push-vars-other-route: a test `x is T` against a type variable reads `T` as a
/// class of the function, as a parameter's written `T` is (DESIGN sec:type_resolution, rule
/// 4: a name of the form `[A-Z][0-9]*` is a type variable), so a push of the narrowed `x`
/// waits on it as on any open class. Before, a `T` written nowhere else stayed a variable of
/// no class, and the push was refused a second time as "a push of a value whose type the
/// checker cannot follow here", beside the refusal of the test itself, which named `T` "the
/// type of a port". A run-time test against a type variable is refused by elaboration, as
/// one this version does not build; a test against a type that is not a variable is taken.
///
/// In a lambda, `T` is the lambda's own variable, and only its result holds it (`f` gives
/// `"b" | T`); no argument of `f(x)` binds it, so the call gives the unknown `_` for it, and
/// the push of a value holding `_` is refused, as a value not known to be text (row
/// CHECK-dynamic-push-unchecked). This is the one program known to reach that refusal.
#[test]
fn a_push_narrowed_by_a_test_against_a_type_variable_waits_on_it() {
    let call = "main(m: MainArgs) { h(x: \"a\", out: m.stdout); }\n";
    let variable = "a test against a type variable `T` is part of the Zed language but is not \
                    supported by this version of zedc. Write the program without it. [T]";
    let list = "a test against a list type `[T]` is part of the Zed language but is not \
                supported by this version of zedc. Write the program without it. [[T]]";
    let unknown = "a push of a value whose type the checker cannot follow here is part of the \
                   Zed language but is not supported by this version of zedc. Write the \
                   program without it. [f(x)]";
    for (body, checked, want) in [
        ("if x is T { out <- x; };", vec![], vec![variable]),
        (
            "out <- if x is T { x } else { \"b\" };",
            vec![],
            vec![variable],
        ),
        ("if x is [T] { out <- x; };", vec![], vec![list]),
        (
            "f = (positional v) -> if v is T { v } else { \"b\" }; out <- f(x);",
            vec![unknown],
            vec![variable, unknown],
        ),
    ] {
        let text = format!("h(x, out: Lines) {{ {body} }}\n{call}");
        assert_eq!(type_errors(&text), checked, "{text}");
        assert_eq!(elab_errors(&text), want, "{text}");
    }
    let bound = "h(positional y: T, x, out: Lines) { if x is T { out <- x; }; }\n\
                 main(m: MainArgs) { h(\"c\", x: \"a\", out: m.stdout); }\n";
    assert_eq!(type_errors(bound), Vec::<String>::new());
    assert_eq!(elab_errors(bound), vec![variable]);
    // Controls: a test against a type that is no variable is taken; a push whose rest fails
    // whatever `x` is is refused at once.
    let string = format!("h(x, out: Lines) {{ if x is String {{ out <- x; }}; }}\n{call}");
    assert_eq!(elab_errors(&string), Vec::<String>::new());
    prints("narrowed_by_string", &string, "a\n");
    let rest = format!("h(x, out: Lines) {{ if x is T {{ out <- [x, 5]; }}; }}\n{call}");
    assert_eq!(
        type_errors(&rest),
        vec![
            "A `Lines` port takes a `String` or a family of strings: \
             `out <- [x, 5] : (0 | 1) -> 5 | T`. [[x, 5]]"
        ]
    );
}

#[test]
fn an_uncalled_inner_function_s_push_does_not_refuse_the_call_around() {
    // No call reaches `g`, so nothing gives `y` a value: the push of `[x, y]` holds `x`'s
    // values alone, as its own check read `y` when it was written, and `h(x: "a", …)` is taken
    // (row CHECK-uncalled-inner-push-refused, `Ck::unreached_in_pushes` in zedc-check). Before,
    // each call of `h` read `y` as `_`, every value, and was refused: "`h`, which needs this of
    // its argument, does not take every value, and this value is `_`".
    prints(
        "bubble_push_uncalled_inner",
        &inner_push("out <- x.upper;", "\"a\""),
        "A\n",
    );
    // The controls: a call of `g` gives `y` its value, which is checked.
    assert_eq!(
        type_errors(&inner_push("g(5, o: out);", "\"a\"")),
        [
            "A `Lines` port takes a `String` or a family of strings: `o <- [x, y] : (0 | 1) -> \
          int | \"a\"`. [[x, y]]"
        ],
    );
    prints(
        "bubble_push_called_inner",
        &inner_push("g(\"b\", o: out);", "\"a\""),
        "a\nb\n",
    );
}

#[test]
fn an_uncalled_inner_lambda_s_push_does_not_refuse_the_call_around() {
    // The lambda twin of the test above: `f` is never applied, so `y` holds no value.
    let src = "h(x, out: Lines) { f = (positional y) -> { out <- [x, y]; 0 }; out <- x.upper; }\n\
               main(m: MainArgs) { h(x: \"a\", out: m.stdout); }\n";
    prints("bubble_push_uncalled_lambda", src, "A\n");
}

#[test]
fn an_uncalled_inner_push_still_checks_the_outer_value() {
    // The checker checks the body of an inner function whether or not it is called, so the
    // push still constrains `x`, a parameter of `h`: a number for `x` is refused at the push,
    // with `y`, which holds no value, adding nothing to the type of `[x, y]`.
    assert_eq!(
        type_errors(&inner_push("out <- \"z\";", "5")),
        [
            "A `Lines` port takes a `String` or a family of strings: `o <- [x, y] : (0 | 1) -> \
          5`. [[x, y]]"
        ],
    );
    prints(
        "bubble_push_uncalled_inner_outer",
        &inner_push("out <- \"z\";", "\"a\""),
        "z\n",
    );
}
