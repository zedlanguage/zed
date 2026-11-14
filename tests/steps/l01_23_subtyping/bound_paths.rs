//! The bound check of a morphism type `L .. U -> V` (its guarantee `L` within its permission
//! `U`) runs once for every written type, wherever it is written: a parameter, a lambda
//! parameter, a default, a test or an `is`. Loading a program, checking it alone and checking
//! it in a batch give the same message.

use zed_kernel::types::Refusal;
use zedc::ast::unit;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};
use zedc::resolve::resolve;

/// The start of the message for a morphism type whose guarantee is outside its permission.
const BOUND: &str = "in a function type `L .. U -> V`, every function the guarantee `L`, left of \
                     `..`, describes must also be allowed by the permission `U`, right of `..`, ";
/// The repairs that message ends with.
const REPAIR: &str = ". To repair it, narrow the type left of `..`, or widen the type right of it.";
const BAD: &str = "in a function type `L .. U -> V`, every function the guarantee `L`, left of \
                   `..`, describes must also be allowed by the permission `U`, right of `..`, \
                   and in this one the guarantee allows functions the permission does not. To \
                   repair it, narrow the type left of `..`, or widen the type right of it.";

/// The diagnostics of `src` through `zedc::run::load`, one per message: its first line, with
/// the indented lines after it, as the reason a refused check gives.
fn through_load(src: &str) -> Vec<String> {
    let e = match zedc::run::load(src.as_bytes()) {
        Ok(_) => panic!("accepted:\n{src}"),
        Err(e) => e,
    };
    let mut out: Vec<String> = Vec::new();
    for line in e.lines() {
        match out.last_mut() {
            Some(m) if line.starts_with("  ") => {
                m.push('\n');
                m.push_str(line);
            }
            _ => out.push(line.to_string()),
        }
    }
    out
}

/// The type errors of `src` through `zedc::check::walk::check`, as `line:col: message`.
fn through_check(src: &str) -> Vec<String> {
    let tokens = lex_fence(src).unwrap();
    let tree = parse(src, &tokens, "Unit", TOP).unwrap();
    let stmts = unit(src, &tokens, &tree).unwrap();
    let res = resolve(&stmts).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    let info = zedc::check::walk::check(&stmts, &res);
    info.errors
        .iter()
        .map(|e| {
            let before = &src[..e.span.start];
            let line = before.matches('\n').count() + 1;
            let col = before.len() - before.rfind('\n').map_or(0, |i| i + 1) + 1;
            format!("{line}:{col}: {}", e.message)
        })
        .collect()
}

/// `src` is rejected with exactly `want` through load, through check, and in a batch: alone
/// on a fresh thread, after another program and after itself.
fn rejected_everywhere(src: &str, want: &[String]) {
    assert_eq!(through_load(src), want, "load: {src}");
    // The checker alone gives the bound errors; elaboration may add its own.
    let bound: Vec<String> = want.iter().filter(|w| w.contains(BOUND)).cloned().collect();
    assert_eq!(through_check(src), bound, "check: {src}");
    let s = src.to_string();
    let alone = std::thread::spawn(move || through_load(&s)).join().unwrap();
    assert_eq!(alone, want, "alone: {src}");
    assert!(zedc::run::load(b"f(x: #a .. #a | #b -> int) = 0;\nmain() = 0;\n").is_ok());
    assert_eq!(through_load(src), want, "after another: {src}");
    assert_eq!(through_load(src), want, "again: {src}");
}

#[test]
fn a_parameter_whose_morphism_bound_fails_is_rejected_on_every_path() {
    rejected_everywhere(
        "f(x: #a .. #b -> int) = 0;\nmain() = 0;\n",
        &[format!("1:6: {BAD}")],
    );
    // Nested in a union and a tuple, and as a lambda parameter, a default and an `is`.
    rejected_everywhere(
        "f(x: (int, (#a | #b) .. #a -> int) | int) = 0;\nmain() = 0;\n",
        &[format!("1:12: {BAD}")],
    );
    rejected_everywhere(
        "main() = { g = (y: #a .. #b -> int) -> 0; 0 };\n",
        &[format!("1:20: {BAD}")],
    );
    rejected_everywhere(
        "f(x: int) = x is (#a .. #b -> int);\nmain() = 0;\n",
        &[
            "1:18: `is` tests a value against a type when the program runs, and a function value does not show its type then. Test against a type that is not a function type, or remove the `is`.".to_string(),
            format!("1:18: {BAD}"),
        ],
    );
}

#[test]
fn a_parameter_whose_morphism_bound_holds_is_taken() {
    for src in [
        "f(x: #a .. #a | #b -> int) = 0;\nmain() = 0;\n",
        "f(x: (int, #a .. #a -> int)) = 0;\nmain() = 0;\n",
    ] {
        assert!(zedc::run::load(src.as_bytes()).is_ok(), "{src}");
        assert_eq!(through_check(src), Vec::<String>::new(), "{src}");
    }
}

#[test]
fn a_parameter_whose_morphism_bound_check_was_refused_says_why() {
    let src = "f(x: (int -> #a | #b) .. ((int -> #a) | (int -> #b)) -> int) = 0;\nmain() = 0;\n";
    rejected_everywhere(
        src,
        &[format!(
            "1:6: {BOUND}and the checker could not decide whether this one's guarantee is within \
             its permission, so it is not proved wrong{REPAIR}\n  because {}",
            Refusal::MorphismSplit.message()
        )],
    );
}

/// An old output port's type is a written type too, and the form is refused before its bound
/// is read: on `main`, whose result is an `int`, and on another function, where a port in the
/// result is a later form.
#[test]
fn an_old_output_port_is_refused_before_its_bound_is_read() {
    assert_eq!(
        through_load("main() -> (out: #a .. #b -> int) {\n  out <- \"x\";\n}\n"),
        [[
            "1:11: Result of `main` that is not an `int`: `(out: #a .. #b -> int)`. Try `int` \
             instead.",
            "  [1] 1:11: `main` gives an `int`, the program's exit status, 0 for success; a body \
             that exports nothing gives 0, so the result may be left out",
            "      1 | main() -> (out: #a .. #b -> int) {",
            "        |           ^^^^^^^^^^^^^^^^^^^^^^",
            "  [2] 1:11: the program writes lines with a push to `m.stdout`, as \
             `m.stdout <- lines;`, with `main(m: MainArgs)`"
        ]
        .join("\n")]
    );
    assert_eq!(
        through_load("f() -> (out: #a .. #b -> int) { 0 }\nmain() = 0;\n"),
        [zed_tests::not_yet(
            "1:5: the declared result type `-> (out: #a .. #b -> int)`"
        )]
    );
}

mod bench;
