//! A test on what a use of an undeclared parameter gives narrows it at each call (rule 3):
//! `args[k] else ""` in the body of `r(fs, args, k)` holds no `#notFound` where a call binds
//! `args` to a `CommandLine`, so `fs` is never given one. Before, the `else` kept the whole
//! type variable of `args[k]`, the call bound it to `String | #notFound`, and the program was
//! rejected with "this function, which `r` applies, does not take #notFound" (repair
//! CHK-index-else, found writing the L1.36a test programs).

use zed_tests::scaling;

use super::{Resolved, type_errors};
use zed_tests::step_helpers::l01_19a_command_line::{dir, run};

/// `main` reading the files its first two arguments name through `r`, `missing` for a file
/// that is not there.
const MAIN: &str = "main(m: MainArgs) {\n  fs = main::files;\n  \
    a = (r(fs: fs, args: m.args, k: 0) else #notFound -> \"missing\") else #ioError -> \"unreadable\";\n  \
    b = (r(fs: fs, args: m.args, k: 1) else #notFound -> \"missing\") else #ioError -> \"unreadable\";\n  \
    m.stdout <- \"${a}|${b}\";\n}\n";

/// Runs `r`, defined as `helper`, with `main` on the arguments `present.txt absent.txt` of a
/// test directory of its own, and gives standard output.
fn read_two(name: &str, helper: &str) -> String {
    let src = format!("{helper}\n{MAIN}");
    assert_eq!(type_errors(&src), Vec::<String>::new(), "{src}");
    let d = dir(name);
    std::fs::write(d.join("present.txt"), "hello").unwrap();
    let (present, absent) = (d.join("present.txt"), d.join("absent.txt"));
    let words = ["--", present.to_str().unwrap(), absent.to_str().unwrap()];
    let out = run(name, &src, &words);
    assert_eq!(out.status, 0, "{}", out.stderr);
    out.stdout
}

#[test]
fn a_helper_reading_the_file_an_argument_names_or_the_empty_path() {
    // The repair's repro: every read had to be written out by hand.
    let helper = "r(fs, args, k) = fs[args[k] else \"\"];";
    assert_eq!(read_two("given_else", helper), "hello|missing\n");
}

#[test]
fn the_argument_named_first_is_the_same() {
    let helper = "r(fs, args, k) { p = args[k] else \"\"; return fs[p]; }";
    assert_eq!(read_two("given_named", helper), "hello|missing\n");
}

#[test]
fn an_else_on_the_one_atom_narrows_as_well() {
    let helper = "r(fs, args, k) = fs[args[k] else #notFound -> \"\"];";
    assert_eq!(read_two("given_atom", helper), "hello|missing\n");
}

#[test]
fn an_is_test_narrows_its_other_branch() {
    let helper =
        "r(fs, args, k) { p = args[k]; return if p is #notFound { #notFound } else { fs[p] }; }";
    assert_eq!(read_two("given_is", helper), "hello|missing\n");
}

#[test]
fn a_function_value_applied_to_the_narrowed_value_takes_no_atom() {
    let src = format!(
        "r(g, args, k) = g(args[k] else \"\");\n{}",
        MAIN.replace("fs: fs", "g: (p) -> fs[p]")
    );
    assert_eq!(type_errors(&src), Vec::<String>::new());
}

#[test]
fn a_test_that_leaves_the_atom_is_still_rejected() {
    // `else #ioError -> ""` and `is #ioError` handle an atom `args[k]` never gives, so its
    // `#notFound` still reaches `fs`, which does not take it.
    let expected = "this function, which `r` applies, does not take #notFound, and no argument \
                    of this call gives it. [r(fs: fs, args: m.args, k: 0)]";
    for helper in [
        "r(fs, args, k) = fs[args[k] else #ioError -> \"\"];",
        "r(fs, args, k) { p = args[k]; return if p is #ioError { \"\" } else { fs[p] }; }",
    ] {
        let errors = type_errors(&format!("{helper}\n{MAIN}"));
        assert_eq!(
            errors.first().map(String::as_str),
            Some(expected),
            "{helper}"
        );
    }
}

/// `n` helpers, each reading the file an argument names or the empty path, and `main` calling
/// each once.
fn helpers(n: usize) -> String {
    let mut src: String = (0..n)
        .map(|i| format!("r{i}(fs, args, k) = fs[args[k] else \"\"];\n"))
        .collect();
    src.push_str("main(m: MainArgs) {\nfs = main::files;\n");
    for i in 0..n {
        src.push_str(&format!(
            "  a{i} = (r{i}(fs: fs, args: m.args, k: {}) else #notFound -> \"m\") \
             else #ioError -> \"u\";\n",
            i
        ));
    }
    src.push_str("  m.stdout <- \"${a0}\";\n}\n");
    src
}

#[test]
fn many_helpers_narrowing_what_a_use_gives_scale() {
    let n = 200;
    let units: Vec<(usize, Resolved)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, Resolved::new(&helpers(m))))
        .collect();
    scaling::check("n helpers narrowing what a use gives", n, |m| {
        let (_, r) = units.iter().find(|(k, _)| *k == m).unwrap();
        let info = r.check();
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    });
}

#[test]
fn a_key_handled_beside_the_read_is_followed_too() {
    // The key `k` of `args[k]` passes its atoms to the read (rule 6), so `d = k else 0`
    // handles them for `k` as well. Before, the key was not followed, and the call was
    // rejected: "`r` applies, does not take #_" (CLASS-atoms-index-key).
    let helper = "r(fs, args, k) { d = k else 0; return fs[args[k] else \"\"]; }";
    assert_eq!(read_two("given_key", helper), "hello|missing\n");
}

#[test]
fn an_else_on_a_parameter_of_any_value_leaves_no_atom_at_a_call() {
    // `r else d` on a parameter of any value leaves a value of its own, which a call gives as
    // the argument without its loose atoms (DESIGN.md sec:failure: "loose atoms ... are
    // stripped"). Before, it kept the parameter's type variable whole, so `g(args[0])` was
    // `0 | String | #notFound` and a `Lines` port rejected it (CHECK-else-notfound, QUESTIONS.md
    // A11's side observation).
    for (src, want) in [
        (
            "g(positional r) = r else 0;\n\
             main(m: MainArgs) { m.stdout <- \"${g(m.args[0])}\"; }\n",
            "0\n",
        ),
        (
            "g(positional r) = r else \"zero\";\n\
             main(m: MainArgs) { m.stdout <- g(m.args[0]) ++ \"a\"; }\n",
            "zeroa\n",
        ),
        (
            "g(positional r) { d = r else 0; return r; }\n\
             main(m: MainArgs) { m.stdout <- g(\"abc\"); }\n",
            "abc\n",
        ),
    ] {
        assert_eq!(type_errors(src), Vec::<String>::new(), "{src}");
        let out = run("given_else_any", src, &["--"]);
        assert_eq!(out.status, 0, "{}", out.stderr);
        assert_eq!(out.stdout, want, "{src}");
    }
}

#[test]
fn a_value_left_by_a_test_used_against_the_tested_value_is_rejected_at_the_test() {
    // `trim(r)` makes `r` a `String`, which holds no atom, so `r else 0` is `r` itself and
    // `d + 1` cannot take it; the error is at the `else`.
    let src = "g(positional r) { d = r else 0; e = d + 1; return trim(r); }\n";
    assert_eq!(
        type_errors(src),
        [
            "the value this test leaves is used as int, and the value it tests as String: the test \
          narrows the value it tests, so both uses are of one value, and no value is both. [r else 0]"
        ]
    );
}
