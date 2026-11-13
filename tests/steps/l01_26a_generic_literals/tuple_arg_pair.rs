//! A literal component of a tuple argument outside every function stands for a value its
//! carriers hold, and a use in the body that requires a closed type restricts its carriers
//! to that type's, as a parameter of that type does (DESIGN.md L1.26a). A call requires a
//! function, which no carrier holds: `h(positional p) = p[1](p[0]); r = h((1, 2))` is
//! rejected as `(1, "s")` is (item SOUND-call-pair); it was accepted, and the run stopped on
//! "a value of type `int` is not a function". A body that returns a component beside a
//! literal, or adds `1r` to it, restricts it to `int` or `rat`, so `h((1, 2))` checks as
//! `h(1)` of the same body does (item CHK-replay-pair); it was rejected with "`h` gives 1
//! here, which is not int".

use zed_tests::scaling;
use zed_tests::step_helpers::l01_19_whole_file_ports::run;
use zed_tests::step_helpers::l01_26_type_resolution::{info, type_errors};

/// `def` and `r = call;` with a `main` that prints `r`.
fn program(def: &str, call: &str) -> String {
    format!("{def}\nr = {call};\nmain(m: MainArgs) {{ m.stdout <- \"${{r}}\"; }}\n")
}

/// What `zedc run` prints of `program(def, call)`, in test directory `name`: its standard
/// output when it runs, else its standard error with the program's path removed.
fn outcome(name: &str, def: &str, call: &str) -> String {
    let o = run(name, &program(def, call), "", &[]);
    match o.status {
        0 => {
            assert_eq!(o.stderr, "", "{def} {call}");
            o.stdout
        }
        _ => {
            assert_eq!(o.stdout, "", "{def} {call}");
            let (_, rest) = (o.stderr.split_once("prog.zed:"))
                .unwrap_or_else(|| panic!("{def} {call}: no placed message in {}", o.stderr));
            rest.to_string()
        }
    }
}

/// The rejection of a call of a component that is not a function, for the value `shown`
/// written as `arg` at `h(positional p) = p[1](p[0])`.
fn not_a_function(shown: &str, arg: &str) -> String {
    let marks = "^".repeat(arg.len() + 3);
    format!(
        "2:5: `p[1]` is {shown}, not a function: this call applies `p[1]` to arguments, and a value \
         of type {shown} cannot be applied.\n\
         \x20 [1] 1:19: `h` needs this of its argument here\n\
         \x20     1 | h(positional p) = p[1](p[0]);\n\
         \x20       | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [2]\n\
         \x20       |                   ^^^^^^^^^^ [1]\n\
         \x20 [2] 1:1: `h` is declared here with no type written for `p` or its result; the \
         type the checker found for `h` is `(_) -> _`\n\
         \x20 [3] 2:5: repair: call a function here, or write `p[1]` without the parentheses of the call \
         if its value is meant\n\
         \x20     2 | r = h({arg});\n\
         \x20       |     {marks}\n"
    )
}

const CALL: &str = "h(positional p) = p[1](p[0]);";

/// The call of a literal component is rejected with the message of a call of a string
/// component; a component of a nested tuple and one of another carrier alike.
#[test]
fn a_call_of_a_literal_component_is_rejected_as_one_of_a_string() {
    let name = "l01_26a_tuple_arg_pair_call";
    assert_eq!(
        outcome(name, CALL, "h((1, \"s\"))"),
        not_a_function("\"s\"", "(1, \"s\")")
    );
    assert_eq!(
        outcome(name, CALL, "h((1, 2))"),
        not_a_function("2", "(1, 2)")
    );
    assert_eq!(
        outcome(name, CALL, "h(((1, 3), 2))"),
        not_a_function("2", "((1, 3), 2)")
    );
    let errors = type_errors("h(positional p) = p[0](1);\nr = h((2.5f64, 1));\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("`p[0]` is 2.5f64, not a function"),
        "{errors:?}"
    );
    // A literal component that `+` asks for a carrier is not called either.
    let errors = type_errors("g(positional x) = (x + 1)(2);\nr = g(1);\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("`(x + 1)` is int | f32 | f64 | rat, not a function"),
        "{errors:?}"
    );
}

/// A callee that is not a name is named in a call's messages by its own code, as written,
/// with the parentheses around it and the spaces inside it (item MSG-callee-code); it was
/// named "`the function called here`", in code quotes as if it were code. A callee written
/// over two lines cannot stand in a headline and is named by those words, not in quotes.
#[test]
fn a_callee_that_is_not_a_name_is_named_by_its_code() {
    let name = "l01_26a_tuple_arg_pair_callee";
    for (def, call, code) in [
        (
            "h(positional fs, positional i) = fs[i + 1](2);",
            "h((1, \"s\"), 0)",
            "`fs[i + 1]`",
        ),
        (
            "h(positional c, positional p) = (if c { p[0] } else { p[1] })(2);",
            "h(false, (1, \"s\"))",
            "`(if c { p[0] } else { p[1] })`",
        ),
        (
            "h(positional p) = ( p[1] )(p[0]);",
            "h((1, \"s\"))",
            "`( p[1] )`",
        ),
        (
            "h(positional p) = (\n  p[1])(p[0]);",
            "h((1, \"s\"))",
            "the function called here",
        ),
    ] {
        let got = outcome(name, def, call);
        let at = 2 + def.matches('\n').count();
        let head = format!(
            "{at}:5: {code} is \"s\", not a function: this call applies {code} to arguments, and \
             a value of type \"s\" cannot be applied.\n"
        );
        assert!(got.starts_with(&head), "{def} {call}\n{got}");
        let repair = format!(
            "repair: call a function here, or write {code} without the parentheses of the call \
             if its value is meant\n"
        );
        assert!(got.contains(&repair), "{def} {call}\n{got}");
    }
    // A call of a call: the callee is `scale(2)`.
    assert_eq!(
        outcome(
            name,
            "scale(positional k: int) = (x: int) -> k * x;",
            "scale(2)(\"a\")"
        ),
        "2:5: `scale(2)` does not take (\"a\"): no arrow of `scale(2)` takes these types.\n\
         \x20 [1] 2:14: this expression is \"a\"\n\
         \x20     2 | r = scale(2)(\"a\");\n\
         \x20       |     ^^^^^^^^^^^^^ [2]\n\
         \x20       |              ^^^ [1]\n\
         \x20 [2] 2:5: `scale(2)` takes (int) -> int\n"
    );
    // Arguments that do not fit the parameters of a function a component holds.
    let got = outcome(
        name,
        "h(positional p) = p[1](p[0], q: 3);",
        "h((1, (x) -> x))",
    );
    assert!(
        got.contains(
            "`p[1]` here is a function of type `(T) -> T`, and the arguments of this call do \
             not fit its parameters: this argument is passed by the name `q`, and `p[1]` has no \
             parameter of that name"
        ),
        "{got}"
    );
}

/// A function is called beside the tuple, and the body's parameter that may hold one is
/// called: both run. A tuple cannot hold the function, which is data's rule.
#[test]
fn a_call_of_a_function_beside_the_literals_runs() {
    let name = "l01_26a_tuple_arg_pair_fn";
    assert_eq!(
        outcome(
            name,
            "h(positional f, positional p) = f(p[0]);",
            "h(x -> x + 1, (1, 2))"
        ),
        "2\n"
    );
    assert_eq!(
        outcome(name, "h(positional f) = f(1);", "h(x -> x * 3)"),
        "3\n"
    );
    let errors = type_errors(&format!("{CALL}\nr = h((1, x -> x + 1));\n"));
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("a tuple takes data, and this value may hold a function"),
        "{errors:?}"
    );
}

const PICK: &str = "h(positional p) = if p[0] < 5 { p[0] } else { 0 };";
const ADD_R: &str = "h(positional p) = p[0] + 1r;";

/// The type of `r` in `def` and `r = call;`, which must check.
fn type_of_r(def: &str, call: &str) -> String {
    let src = format!("{def}\nr = {call};\n");
    let (i, _) = info(&src);
    let errors: Vec<&str> = i.errors.iter().map(|e| e.message.as_str()).collect();
    assert!(errors.is_empty(), "{src}\nerrors: {errors:?}");
    i.tops.get("r").expect("a type for `r`").to_string()
}

/// A literal component returned beside a literal, or added to `1r`, has the type and value
/// of the literal passed alone, where it was rejected.
#[test]
fn a_component_returned_beside_a_carrier_checks_as_the_literal_alone() {
    let name = "l01_26a_tuple_arg_pair_replay";
    for (def, pair, alone, ty, out) in [
        (PICK, "h((1, 2))", "h(1)", "int", "1\n"),
        (PICK, "h((7, 2))", "h(7)", "int", "0\n"),
        (ADD_R, "h((1, 2))", "h(1)", "rat", "2r\n"),
        (
            "h(positional p) = if p[0] < 5 { p[0] } else { 0r };",
            "h((7, 2))",
            "h(7)",
            "0r | int",
            "0r\n",
        ),
    ] {
        // The same body on a parameter that is the component itself.
        let one = def.replace("p[0]", "p");
        assert_eq!(outcome(name, def, pair), out, "{def} {pair}");
        assert_eq!(outcome(name, &one, alone), out, "{one} {alone}");
        assert_eq!(type_of_r(def, pair), ty, "{def} {pair}");
        assert_eq!(type_of_r(&one, alone), ty, "{one} {alone}");
    }
    // A component from a parameter: the call is inside a function.
    assert_eq!(
        outcome(
            name,
            &format!("{ADD_R}\ng(positional x) = h((x, 2));"),
            "g(3r)"
        ),
        "4r\n"
    );
}

/// A first component that is not a literal without a suffix keeps its type, and is rejected
/// where it is not the type the use requires.
#[test]
fn a_first_component_of_another_type_is_rejected() {
    let name = "l01_26a_tuple_arg_pair_other";
    assert_eq!(
        outcome(name, ADD_R, "h((1.0f64, 2))"),
        "2:5: `h` gives 1.0f64 here, which is not rat: the use requires a value of rat.\n\
         \x20 [1] 1:19: `h` needs this of its argument here\n\
         \x20     1 | h(positional p) = p[0] + 1r;\n\
         \x20       | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [2]\n\
         \x20       |                   ^^^^ [1]\n\
         \x20 [2] 1:1: `h` is declared here with no type written for `p` or its result; the \
         type the checker found for `h` is `(_) -> rat`\n\
         \x20 [3] 2:5: repair: change the argument, so that `h` gives a value of rat here\n\
         \x20     2 | r = h((1.0f64, 2));\n\
         \x20       |     ^^^^^^^^^^^^^^\n"
    );
    for (def, call, head) in [
        (
            PICK,
            "h((\"a\", 2))",
            "2:5: `h` gives \"a\" here, which is not int",
        ),
        (
            ADD_R,
            "h((true, 2))",
            "2:5: `h` gives true here, which is not rat",
        ),
    ] {
        let got = outcome(name, def, call);
        assert!(got.starts_with(head), "{def} {call}\n{got}");
        assert_eq!(got.matches("prog.zed:").count(), 0, "one message: {got}");
    }
}

/// A decimal literal component takes the carrier its use in the body requires, and has the
/// type and value of the literal passed alone (item LIT-tuple-decimal-body); it was rejected
/// with "Nothing gives the literal `1.5` a carrier". Two components added together, a component
/// of a nested tuple, and one that meets a `rat` component take it too.
#[test]
fn a_decimal_component_takes_the_carrier_its_use_requires() {
    let name = "l01_26a_tuple_arg_pair_decimal";
    for (def, pair, alone, ty, out) in [
        (ADD_R, "h((1.5, 2))", "h(1.5)", "rat", "5r/2r\n"),
        (ADD_R, "h((-1.5, 2))", "h(-1.5)", "rat", "-1r/2r\n"),
        (
            "h(positional p) = p[0] + 1.0f64;",
            "h((0.1, 2))",
            "h(0.1)",
            "f64",
            "1.1\n",
        ),
    ] {
        let one = def.replace("p[0]", "p");
        assert_eq!(outcome(name, def, pair), out, "{def} {pair}");
        assert_eq!(outcome(name, &one, alone), out, "{one} {alone}");
        assert_eq!(type_of_r(def, pair), ty, "{def} {pair}");
        assert_eq!(type_of_r(&one, alone), ty, "{one} {alone}");
    }
    for (def, call, out) in [
        (
            "h(positional p) = p[0] + p[1] + 1r;",
            "h((1.5, 0.25))",
            "11r/4r\n",
        ),
        (
            "h(positional p) = p[0][1] + 1r;",
            "h(((1, 2.5), 2))",
            "7r/2r\n",
        ),
        ("h(positional p) = p[0] * p[1];", "h((1.5, 2r))", "3r\n"),
    ] {
        assert_eq!(outcome(name, def, call), out, "{def} {call}");
    }
}

/// A decimal component at a use that asks for `f32` takes `f32`, and one at a use that leaves
/// it the float formats alone takes `f64` (author decision, 2026-11-12), as the literal passed
/// alone does (row FLOAT-f32).
#[test]
fn a_decimal_component_takes_f32_or_the_float_formats_f64() {
    let name = "l01_26a_tuple_arg_pair_decimal_f32";
    for (def, pair, alone, ty, out) in [
        (
            "h(positional p) = p[0] + 1.0f32;",
            "h((1.5, 2))",
            "h(1.5)",
            "f32",
            "2.5\n",
        ),
        (
            "h(positional p) = p[0] ^ 2.0;",
            "h((1.5, 2))",
            "h(1.5)",
            "f64",
            "2.25\n",
        ),
    ] {
        let one = def.replace("p[0]", "p");
        assert_eq!(outcome(name, def, pair), out, "{def} {pair}");
        assert_eq!(outcome(name, &one, alone), out, "{one} {alone}");
        assert_eq!(type_of_r(def, pair), ty, "{def} {pair}");
        assert_eq!(type_of_r(&one, alone), ty, "{one} {alone}");
    }
}

/// A decimal component that no use gives one carrier is rejected as before: one the body does
/// not read, one beside a component a use does fix, which alone is rejected, and one that `*`
/// with a literal leaves `f64` or `rat`. One at an `int` use is rejected for that use.
#[test]
fn a_decimal_component_no_use_fixes_is_rejected() {
    let name = "l01_26a_tuple_arg_pair_decimal_rejected";
    assert_eq!(
        outcome(name, "h(positional p) = p[0];", "h((1.5, 2))"),
        "2:8: Nothing gives the literal `1.5` a carrier. Try `r = h((1.5f64, 2))` instead.\n\
         \x20 [1] 2:8: this expression is 1.5\n\
         \x20     2 | r = h((1.5, 2));\n\
         \x20       |        ^^^\n\
         \x20 [2] 1:1: `h` is declared here with no type written for `p` or its result; the \
         type the checker found for `h` is `(_) -> _`\n\
         \x20     1 | h(positional p) = p[0];\n\
         \x20       | ^^^^^^^^^^^^^^^^^^^^^^^\n\
         \x20 fixes, each checked here:\n\
         \x20   r = h((1.5f64, 2));    the literal is then the f64 1.5\n\
         \x20   r = h((1.5r, 2));      the literal is then exactly 1.5, a rat\n"
    );
    assert_eq!(
        outcome(name, ADD_R, "h((1.5, 2.5))"),
        "2:13: Nothing gives the literal `2.5` a carrier. Try `r = h((1.5, 2.5f64))` instead.\n\
         \x20 [1] 2:13: this expression is 2.5\n\
         \x20     2 | r = h((1.5, 2.5));\n\
         \x20       |             ^^^\n\
         \x20 [2] 1:1: `h` is declared here with no type written for `p` or its result; the \
         type the checker found for `h` is `(_) -> rat`\n\
         \x20     1 | h(positional p) = p[0] + 1r;\n\
         \x20       | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n\
         \x20 fixes, each checked here:\n\
         \x20   r = h((1.5, 2.5f64));    the literal is then the f64 2.5\n\
         \x20   r = h((1.5, 2.5r));      the literal is then exactly 2.5, a rat\n"
    );
    for (def, call, head) in [
        (
            "h(positional p) = p[1] + 1r;",
            "h((1.5, 2))",
            "2:8: Nothing gives the literal `1.5` a carrier.",
        ),
        (
            "h(positional p) = p[0] * 2;",
            "h((1.5, 2))",
            "2:8: Nothing gives the literal `1.5` a carrier.",
        ),
        (
            PICK,
            "h((1.5, 2))",
            "2:5: `h` gives 1.5 here, which is not int: the use requires a value of int.",
        ),
    ] {
        let got = outcome(name, def, call);
        assert!(got.starts_with(head), "{def} {call}\n{got}");
    }
}

/// `n` decimal components and a call with `n` decimal literals: a tuple of the components each
/// added to `1r`, or the sum of all of them and `1r`. Each literal keeps a class of its own in
/// both, and the sum reads all of them in one expression.
fn decimals(n: usize, together: bool) -> String {
    let reads: Vec<String> = (0..n).map(|i| format!("p[{i}]")).collect();
    let body = match together {
        true => format!("{} + 1r", reads.join(" + ")),
        false => format!(
            "({})",
            reads
                .iter()
                .map(|r| format!("{r} + 1r"))
                .collect::<Vec<_>>()
                .join(", ")
        ),
    };
    let args: Vec<String> = (0..n).map(|i| format!("{}.5", i % 9)).collect();
    format!("h(positional p) = {body};\nr = h(({}));\n", args.join(", "))
}

#[test]
fn many_decimal_components_check_in_linear_time() {
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            for together in [false, true] {
                assert_eq!(type_errors(&decimals(3, together)), Vec::<String>::new());
                let n = 100;
                let srcs = [
                    decimals(n, together),
                    decimals(scaling::FACTOR * n, together),
                ];
                let what = match together {
                    false => "checking a call of n decimal components, each added to 1r",
                    true => "checking a call of n decimal components summed",
                };
                scaling::check(what, n, |m| {
                    assert_eq!(
                        type_errors(&srcs[usize::from(m != n)]),
                        Vec::<String>::new()
                    );
                });
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

/// `n` components, each returned beside a literal, and a call with `n` integer literals: the
/// replay restricts each component's class once.
fn picks(n: usize) -> String {
    let body: Vec<String> = (0..n)
        .map(|i| format!("if p[{i}] < 5 {{ p[{i}] }} else {{ 0 }}"))
        .collect();
    let args: Vec<String> = (0..n).map(|i| (i % 9).to_string()).collect();
    format!(
        "h(positional p) = ({});\nr = h(({}));\n",
        body.join(", "),
        args.join(", ")
    )
}

/// `n` functions, each passing its parameter's first component to the next beside `1r`, and a
/// call of the first with a pair of literals: the replay runs through `n` nested calls.
fn chain(n: usize) -> String {
    let mut src = String::from("h0(positional p) = p[0] + 1r;\n");
    for i in 1..n {
        src.push_str(&format!(
            "h{i}(positional p) = h{}((p[0], 2)) + 1r;\n",
            i - 1
        ));
    }
    src.push_str(&format!("r = h{}((1, 2));\n", n - 1));
    src
}

#[test]
fn many_components_and_nested_calls_check_in_linear_time() {
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            assert_eq!(type_errors(&picks(3)), Vec::<String>::new());
            assert_eq!(type_errors(&chain(3)), Vec::<String>::new());
            let n = 100;
            let srcs = [picks(n), picks(scaling::FACTOR * n)];
            scaling::check("checking a call of n literal components", n, |m| {
                assert_eq!(
                    type_errors(&srcs[usize::from(m != n)]),
                    Vec::<String>::new()
                );
            });
            let n = 40;
            let srcs = [chain(n), chain(scaling::FACTOR * n)];
            scaling::check("checking n nested calls of a pair of literals", n, |m| {
                assert_eq!(
                    type_errors(&srcs[usize::from(m != n)]),
                    Vec::<String>::new()
                );
            });
        })
        .unwrap()
        .join()
        .unwrap();
}
