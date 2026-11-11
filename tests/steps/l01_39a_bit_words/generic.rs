//! A bit word or `^` on a value of a type-variable type (CHK-need-bound): the use records a
//! need of the function on the parameter that gives the value, its ints in the word's domain,
//! `int[0..]` or, for an operand read as `width` digits under a width of an int type,
//! `int[0..<2 ^ w]` for the smallest width `w`. Each call checks it with the caller's ints,
//! from the interval of the argument's expression and the listed ints of its type, and a
//! caller that passes on a parameter of no declared type takes the need on. A rejection shows
//! the argument's derivation and each call that passed the value on, down to the use.
//!
//! The kernel raises `KernelError::Type` at these places, and a generic use of each is
//! rejected before the program runs (`each_kernel_type_error_has_a_rejected_generic_use`):
//! - `^` on ints with a negative exponent (zed-kernel eval.rs `prim_data`);
//! - a bit word's operand below 0, above `2 ^ width`, a funnel shift's `k` not below
//!   `width`, and a `byteSwap` width not a multiple of 8 (bits.rs `outside`, `not_bytes`);
//! - `f64Bits` of a value that is not an f64, and a bit word of one that is not an int
//!   (bits.rs `word`);
//! - a cast of a value of no number or text kind (words.rs `type_err`);
//! - an operator or word on operands of kinds it does not take, `sum` of a tuple that is not
//!   all numbers among them (eval.rs `prim_data`);
//! - `if` on a value that is not a bool, a call of a value that is not a function, and a
//!   component of a value that is not a tuple (eval.rs `type_err`).
//!
//! The last, a program's result that is a function (eval.rs `run`), is no use of a value:
//! `main` writes data to its ports.

use zed_kernel::{Evaluator, Prim, Term, Value, World};
use zed_tests::step_helpers::l01_19_whole_file_ports::run;

use super::{accepted, rejected};

/// A program that writes the text `expr` after the definitions `defs`.
fn printing(defs: &str, expr: &str) -> String {
    format!("{defs}\nmain(m: MainArgs) {{\n  m.stdout <- {expr};\n}}\n")
}

/// What the program `src` prints, run in the test directory `name`.
fn prints(name: &str, src: &str) -> String {
    let o = run(name, src, "", &[]);
    assert_eq!(o.status, 0, "{src}\n{}", o.stderr);
    o.stdout.trim_end().to_string()
}

/// Each word with the parameter `n` as one operand, the domain `n` takes, an argument in it
/// and the value the word gives on it.
const WORDS: [(&str, &str, &str, &str); 15] = [
    ("2^n", "int[0..]", "3", "8"),
    ("bitAnd(n, 6)", "int[0..]", "3", "2"),
    ("bitAnd(6, n)", "int[0..]", "3", "2"),
    ("bitOr(n, 1)", "int[0..]", "2", "3"),
    ("bitXor(n, 1)", "int[0..]", "3", "2"),
    ("shl(1, n)", "int[0..]", "3", "8"),
    ("shr(16, n)", "int[0..]", "3", "2"),
    ("popCount(n)", "int[0..]", "7", "3"),
    ("bitNot(n, width: 8)", "int[0..<2^8]", "200", "55"),
    ("leadingZeros(n, width: 8)", "int[0..<2^8]", "1", "7"),
    ("trailingZeros(n, width: 8)", "int[0..<2^8]", "8", "3"),
    ("rotl(n, 1, width: 8)", "int[0..<2^8]", "129", "3"),
    ("rotr(n, 1, width: 8)", "int[0..<2^8]", "3", "129"),
    ("rotl(1, n, width: 8)", "int[0..]", "3", "8"),
    ("rotr(5, n, width: 8)", "int[0..]", "1", "130"),
];

#[test]
fn a_negative_argument_is_rejected_at_the_call_for_each_word() {
    for (body, domain, _, _) in WORDS {
        let src = format!("f(positional n) = {body};\nx = f(-1);\n");
        let out = rejected(&src);
        assert!(
            out.starts_with(&format!(
                "2:5: `f` takes `n` in {domain}, and this `n` is -1"
            )),
            "{body}: {out}"
        );
        assert!(out.contains("`n` is this argument, -1"), "{body}: {out}");
        assert!(out.contains(" here\n"), "the use is shown: {body}: {out}");
        assert!(
            out.contains("1:19"),
            "the note is at the use: {body}: {out}"
        );
    }
}

#[test]
fn an_argument_in_the_domain_is_accepted_and_runs_for_each_word() {
    for (body, _, arg, want) in WORDS {
        let src = printing(
            &format!("f(positional n) = {body};"),
            &format!("String(f({arg}))"),
        );
        assert_eq!(prints("generic_words", &src), want, "{body}");
    }
}

#[test]
fn a_wrapper_passes_the_need_on_and_the_message_shows_each_call() {
    for (body, domain, arg, want) in WORDS {
        let defs = format!("f(positional n) = {body};\nw(positional k) = f(k);\n");
        let out = rejected(&format!("{defs}x = w(-1);\n"));
        assert!(
            out.starts_with(&format!(
                "3:5: `w` takes `k` in {domain}, and this `k` is -1"
            )),
            "{body}: {out}"
        );
        assert!(
            out.contains("`k` is passed on as `n` of `f` here"),
            "{body}: {out}"
        );
        let src = printing(&defs, &format!("String(w({arg}))"));
        assert_eq!(prints("generic_wrapper", &src), want, "{body}");
    }
}

#[test]
fn a_chain_of_wrappers_names_every_call_in_order() {
    let out = rejected(
        "f(positional n) = 2^n;\ng(positional m) = f(m);\nh(positional k) { j = k; return g(j); }\nx = h(-3);\n",
    );
    assert!(
        out.starts_with("4:5: `h` takes `k` in int[0..], and this `k` is -3"),
        "{out}"
    );
    let first = out.find("`j` is passed on as `m` of `g` here").expect(&out);
    let second = out.find("`m` is passed on as `n` of `f` here").expect(&out);
    let last = (out.find("`^` on an int takes an exponent in int[0..] here")).expect(&out);
    assert!(first < second && second < last, "{out}");
}

#[test]
fn f_of_3_gives_8_and_f_of_2_point_0_gives_4_point_0() {
    // The bare base `2` takes the carrier of `n` (L1.26a): an int at `f(3)`, an f64 at
    // `f(2.0)`.
    let defs = "f(positional n) = 2^n;";
    let src = printing(defs, "String(f(3)) ++ \" \" ++ String(f(2.0))");
    assert_eq!(prints("generic_pow", &src), "8 4.0");
    let out = rejected(&format!("{defs}\nx = f(true);\n"));
    assert!(out.contains("`f` does not take (true)"), "{out}");
}

#[test]
fn an_unknown_int_is_rejected_and_the_kernel_would_stop_on_it() {
    let src = "f(positional n) = 2^n;\nmain(m: MainArgs) {\n  m.stdout <- String(f(int(m.stdin[1]) else 0));\n}\n";
    let out = rejected(src);
    assert!(
        out.starts_with("3:22: `f` takes `n` in int[0..], and this `n` is int"),
        "{out}"
    );
    assert!(!out.contains("type error"), "{out}");
    // The negative control: the term `2 ^ -1`, which the checker no longer lets through, stops
    // the kernel at run time, the error the need now reports at the call.
    let t = Term::Prim(
        Prim::Pow,
        vec![Term::Lit(Value::Int(2)), Term::Lit(Value::Int(-1))],
    );
    let stop = Evaluator::new(World::new())
        .run(&t)
        .unwrap_err()
        .to_string();
    assert_eq!(
        stop,
        zed_kernel::KernelError::Type("`^` applied to `int`, `int`".into()).to_string()
    );
}

#[test]
fn an_argument_of_a_declared_int_type_is_rejected() {
    let out = rejected("h(positional x) = popCount(x);\nf(positional n: int) = h(n);\n");
    assert!(
        out.starts_with("2:24: `h` takes `x` in int[0..], and this `x` is int"),
        "{out}"
    );
    // A range type, `n: int[0..]`, is a form of L10; at L1 a test shows the range.
    assert!(accepted(
        "h(positional x) = popCount(x);\nf(positional n: int) = if n >= 0 { h(n) } else { 0 };\n"
    ));
}

#[test]
fn an_expression_of_a_parameter_is_checked_at_the_wrapper() {
    let out = rejected("f(positional x) = popCount(x);\ng(positional y) = f(y + 1);\n");
    assert!(
        out.starts_with("2:21: `f` takes `x` in int[0..], and this value may be int"),
        "{out}"
    );
    let out = rejected("f(positional x) = popCount(x);\nx = f(5 - 7);\n");
    assert!(
        out.starts_with("2:5: `f` takes `x` in int[0..], and this `x` is -2"),
        "{out}"
    );
}

#[test]
fn a_guarded_use_gives_0_directly_and_through_a_helper() {
    // `n` is declared `int`: a test narrows only a name whose values are all ints, and with
    // `n` undeclared the bare `0` leaves it `int | f64 | rat` (follow-up GUARD-follow).
    let defs =
        "e(positional n: int) = if n >= 0 { popCount(n) } else { 0 };\ng(positional m) = e(m);";
    let src = printing(defs, "String(e(-1)) ++ \" \" ++ String(g(-1))");
    assert_eq!(prints("generic_guard", &src), "0 0");
    let src = format!(
        "{defs}\nmain(m: MainArgs) {{\n  m.stdout <- String(g(int(m.stdin[1]) else 0));\n}}\n"
    );
    assert!(accepted(&src));
}

#[test]
fn a_lambda_and_a_curried_call_take_the_need() {
    let out = rejected("pc = x -> popCount(x);\ny = pc(-1);\n");
    assert!(
        out.starts_with("2:5: `pc` takes `x` in int[0..], and this `x` is -1"),
        "{out}"
    );
    assert_eq!(
        prints(
            "generic_lambda",
            &printing("pc = x -> popCount(x);", "String(pc(3))")
        ),
        "2"
    );
    let defs = "p(b, e) = b^e;\nq = p(b: 2, ...);";
    let out = rejected(&format!("{defs}\ny = q(e: -1);\n"));
    assert!(
        out.starts_with("3:5: `q` takes `e` in int[0..], and this `e` is -1"),
        "{out}"
    );
    assert_eq!(
        prints("generic_curry", &printing(defs, "String(q(e: 3))")),
        "8"
    );
}

#[test]
fn the_smallest_width_decides() {
    let defs =
        "g(positional x) = bitNot(x, width: 16);\nf(positional x) = g(x) + bitNot(x, width: 8);\n";
    let out = rejected(&format!("{defs}y = f(300);\n"));
    assert!(
        out.starts_with("3:5: `f` takes `x` in int[0..<2^8], and this `x` is 300"),
        "{out}"
    );
    assert!(accepted(&format!("{defs}y = f(255);\n")));
    let out = rejected("f(positional x) = bitNot(x, width: 4);\ny = f(16);\n");
    assert!(
        out.contains("`f` takes `x` in int[0..<2^4], and this `x` is 16"),
        "{out}"
    );
}

#[test]
fn a_relation_between_two_operands_of_type_variables_is_rejected_at_the_use() {
    for (body, msg) in [
        (
            "f(positional x, positional w) = rotl(x, 1, width: w);",
            "`rotl` checks `x` against `width`",
        ),
        (
            "f(positional w) = bitNot(3, width: w);",
            "`bitNot` checks its operands against `width`",
        ),
        (
            "f(positional k) = funnelShl(1, 2, k, width: 8);",
            "`funnelShl` checks `k` against `width`",
        ),
        (
            "f(positional w) = byteSwap(1, width: w);",
            "`byteSwap` checks its operands against `width`",
        ),
    ] {
        let out = rejected(&format!("{body}\n"));
        assert!(out.contains(msg), "{body}: {out}");
        assert!(out.contains("declare the type of"), "{body}: {out}");
    }
}

#[test]
fn each_kernel_type_error_has_a_rejected_generic_use() {
    for (defs, call, msg) in [
        // A domain: `^`'s exponent, an operand, `2 ^ width`; funnel `k` and `byteSwap`'s
        // width are in a_relation_between_two_operands_of_type_variables_is_rejected_at_the_use.
        (
            "f(positional n) = 2^n;",
            "f(-1)",
            "`f` takes `n` in int[0..]",
        ),
        (
            "f(positional n) = shl(1, n);",
            "f(-1)",
            "`f` takes `n` in int[0..]",
        ),
        (
            "f(positional n) = bitNot(n, width: 8);",
            "f(256)",
            "in int[0..<2^8]",
        ),
        (
            "f(positional h) = funnelShl(h, 1, 3, width: 8);",
            "f(300)",
            "in int[0..<2^8]",
        ),
        (
            "f(positional x) = pdep(x, 5);",
            "f(-1)",
            "`f` takes `x` in int[0..]",
        ),
        (
            "f(positional m) = pext(7, m);",
            "f(-1)",
            "`f` takes `m` in int[0..]",
        ),
        // A kind: `f64Bits`, a bit word, a cast, operators and words, `sum`, `if`, a call,
        // a component.
        // `f64Bits(x)` makes `x` an f64, so a bare `3` is one; an int value is not.
        (
            "f(positional x) = f64Bits(x);\ni = 3 + 4;",
            "f(i)",
            "`f` does not take (int)",
        ),
        (
            "f(positional x) = popCount(x);",
            "f(2.0)",
            "is a decimal, and `int` is expected here",
        ),
        (
            "f(positional x) = int(x);",
            "f(true)",
            "`f` does not take (true)",
        ),
        (
            "f(positional x) = f64(x);",
            "f(true)",
            "`f` does not take (true)",
        ),
        (
            "f(positional x, positional y) = x + y;\ni = 3 + 4;",
            "f(i, 2.0f64)",
            "`f` does not take",
        ),
        (
            "f(positional x, positional y) = x < y;",
            "f(1, \"a\")",
            "`f` does not take",
        ),
        (
            "f(positional x, positional y) = x ++ y;",
            "f(1, 2)",
            "`f` does not take",
        ),
        ("f(positional x) = -x;", "f(\"a\")", "`f` does not take"),
        (
            "f(positional x, positional y) = min(x, y);",
            "f((1, \"a\"), (\"b\", 2))",
            "`f` does not take",
        ),
        (
            "f(positional x) = sum(x);",
            "f((\"a\", \"b\"))",
            "`sum` does not take (\"a\", \"b\")",
        ),
        (
            "f(positional x) = sum(x);\ng(positional y) = f(y);",
            "g((\"a\", \"b\"))",
            "`sum` does not take",
        ),
        (
            "f(positional c) = if c { 1 } else { 2 };",
            "f(3)",
            "`f` does not take (3)",
        ),
        (
            "f(positional g) = g(1);",
            "f(3)",
            "`g` is 3, not a function",
        ),
        (
            "f(positional t) = t[0];",
            "f(3)",
            "`[0]` takes a tuple, not 3",
        ),
    ] {
        let out = rejected(&format!("{defs}\nx = {call};\n"));
        assert!(out.contains(msg), "{defs} {call}: {out}");
    }
}

#[test]
fn a_generic_sum_of_numbers_runs() {
    let defs = "f(positional x) = sum(x);\ng(positional y) = f(y);";
    let src = printing(
        defs,
        "String(f((1, 2, 3))) ++ \" \" ++ String(g((1.5f64, 2.0f64)))",
    );
    assert_eq!(prints("generic_sum", &src), "6 3.5");
}

/// The unit `text` lexed, parsed and resolved, for a test that times the check alone.
fn resolved(text: &str) -> (Vec<zedc::ast::Stmt>, zedc::resolve::Resolution) {
    use zedc::parse::{TOP, parse};
    let tokens = zedc::lex::lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    let stmts = zedc::ast::unit(text, &tokens, &tree).unwrap();
    let res = zedc::resolve::resolve(&stmts).unwrap_or_else(|e| panic!("{e:?}"));
    (stmts, res)
}

/// Checks `make(n)` at `n` and `8n` with `check_order`, each input resolved before timing.
fn check_scales(what: &str, n: usize, make: impl Fn(usize) -> String) {
    let inputs = zed_tests::scaling::inputs(n, |m| resolved(&make(m)));
    zed_tests::scaling::check_order(what, n, 1, |m| {
        let (stmts, res) = &inputs[&m];
        let info = zedc::check::walk::check(stmts, res);
        assert!(info.errors.is_empty(), "{what}: {:?}", info.errors);
    });
}

/// A function whose parameter takes three needs, from `^`, `popCount` and `bitNot`.
const USES: &str = "f(positional n) = 2^n + popCount(n) + bitNot(n, width: 8);\n";

#[test]
fn call_sites_scale_linearly() {
    check_scales("calls of a function with needs", 400, |n| {
        let calls: String = (0..n)
            .map(|i| format!("x{i} = f({});\n", i % 200))
            .collect();
        format!("{USES}w(positional k) = f(k);\n{calls}")
    });
}

#[test]
fn a_chain_of_wrappers_scales_linearly() {
    check_scales("a chain of wrappers passing a need on", 200, |n| {
        let chain: String = (1..=n)
            .map(|i| format!("w{i}(positional k) = w{}(k);\n", i - 1))
            .collect();
        format!("{USES}w0(positional k) = f(k);\n{chain}x = w{n}(7);\n")
    });
}
