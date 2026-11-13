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
        "2:5: `the function called here` is {shown}, not a function: this call applies `the \
         function called here` to arguments, and a value of type {shown} cannot be applied.\n\
         \x20 [1] 1:19: `h` needs this of its argument here\n\
         \x20     1 | h(positional p) = p[1](p[0]);\n\
         \x20       | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [2]\n\
         \x20       |                   ^^^^^^^^^^ [1]\n\
         \x20 [2] 1:1: `h` is declared here with no type written for `p` or its result; the \
         type the checker found for `h` is `(_) -> _`\n\
         \x20 [3] 2:5: repair: call a function here, or write `the function called here` \
         without the parentheses if its value is meant\n\
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
        errors[0].starts_with("`the function called here` is 2.5f64, not a function"),
        "{errors:?}"
    );
    // A literal component that `+` asks for a carrier is not called either.
    let errors = type_errors("g(positional x) = (x + 1)(2);\nr = g(1);\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].starts_with("`the function called here` is int | f64 | rat, not a function"),
        "{errors:?}"
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
