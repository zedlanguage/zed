//! Step L1.29c: the four rows of DESIGN.md sec:diagnostics for an argument beyond the
//! parameters, an argument named for no parameter, a parameter given two values, and a value
//! before the dot for a function with no parameters, each with its menu in the program's own
//! text. A call through a value is offered no edit of a declaration; the moved parenthesis
//! `f(g(x), y)` is offered only where both calls then check; the parameter nearest in
//! spelling is offered only among those the call gives no value.

use super::rejected;
use zed_tests::step_helpers::l01_26_type_resolution::info;
use zed_tests::step_helpers::l01_29_diagnostics::{accepted_with_main, with_main};

/// `limit`, which takes three arguments by position.
const LIMIT: &str = "limit(positional v: int, positional lo: int, positional hi: int) = v;\n";

/// `greet`, with a positional parameter and a named one with a default.
const GREET: &str = "greet(positional name: String, punct: String = \"!\") = name ++ punct;\n";

/// `g` of one argument and `f` of two, whose second parameter is `second`.
fn moved(second: &str) -> String {
    format!(
        "g(positional a: int) = a;\nf(positional a: int, positional b: {second}) = a;\ny = 2;\nx = f(g(1, y));\n"
    )
}

/// The rendered diagnostics of `src` with a `main` added.
fn out(src: &str) -> String {
    rejected(&with_main(src))
}

/// Each program the checker's "repair: write `t`" notes give for `src`, `t` written in place
/// of the note's span, with the note.
fn written(src: &str) -> Vec<(String, String)> {
    let src = with_main(src);
    let (i, _) = info(&src);
    let mut fixed = Vec::new();
    for e in &i.errors {
        for note in &e.notes {
            let Some(t) = note.text.strip_prefix("repair: write `") else {
                continue;
            };
            let (t, _) = t.split_once('`').expect("a rewrite in backquotes");
            let s = note.span;
            let p = format!("{}{t}{}", &src[..s.start], &src[s.end..]);
            fixed.push((p, note.text.to_string()));
        }
    }
    fixed
}

#[test]
fn an_argument_beyond_the_parameters_names_the_count_and_offers_its_removal() {
    let o = out(&format!("{LIMIT}x = limit(5, 0, 10, 2);\n"));
    assert!(o.contains("`limit` takes 3 arguments by position"), "{o}");
    assert!(o.contains("repair: remove this argument"), "{o}");
    assert!(
        o.contains("repair: add a parameter for it to the declaration of `limit`"),
        "{o}"
    );
    // The removal checks.
    assert!(accepted_with_main(&format!(
        "{LIMIT}x = limit(5, 0, 10);\n"
    )));
}

#[test]
fn an_argument_of_an_inner_call_is_offered_the_moved_parenthesis() {
    let src = moved("int");
    let o = out(&src);
    assert!(o.contains("repair: write `f(g(1), y)`"), "{o}");
    // Offered after the removal and before the edit of the declaration.
    let at = |s: &str| o.find(s).unwrap_or_else(|| panic!("{s} in {o}"));
    assert!(
        at("repair: remove this argument") < at("repair: write `f(g(1), y)`"),
        "{o}"
    );
    assert!(
        at("repair: write `f(g(1), y)`") < at("declaration of `g`"),
        "{o}"
    );
    // The error is reported once, at `y`, the argument beyond `g`'s parameter.
    assert_eq!(o.matches("one more than `g` takes").count(), 1, "{o}");
}

#[test]
fn the_moved_parenthesis_is_not_offered_where_the_moved_argument_does_not_fit() {
    let o = out(&moved("String"));
    assert!(o.contains("one more than `g` takes"), "{o}");
    assert!(!o.contains("f(g(1), y)"), "{o}");
}

#[test]
fn the_moved_parenthesis_after_no_argument_writes_an_empty_call() {
    let src = "g() = 1;\nf(positional a: int, positional b: int) = a + b;\nx = f(g(2));\n";
    let o = out(src);
    assert!(o.contains("repair: write `f(g(), 2)`"), "{o}");
}

#[test]
fn a_name_for_no_parameter_is_offered_the_nearest_parameter() {
    let o = out(&format!("{GREET}x = greet(\"Al\", puntc: \"?\");\n"));
    assert!(o.contains("repair: write `punct: \"?\"`"), "{o}");
    assert!(
        o.contains("repair: add a parameter `puntc` to the declaration of `greet`"),
        "{o}"
    );
}

#[test]
fn the_nearest_parameter_is_not_offered_when_the_call_gives_it_a_value() {
    let o = out(&format!(
        "{GREET}x = greet(\"Al\", punct: \"!\", puntc: \"?\");\n"
    ));
    assert!(!o.contains("repair: write `punct:"), "{o}");
    assert!(o.contains("repair: remove this argument"), "{o}");
}

#[test]
fn a_parameter_given_two_values_offers_the_removal_of_either() {
    // A call that names one parameter twice is refused by the parser, so the receiver is the
    // second value a program can give a parameter; the parameter is not positional, as a
    // positional one passed by name is refused first, for that.
    let o = out("hello(name: String) = name;\nx = \"Al\".hello(name: \"Bo\");\n");
    assert!(
        o.contains("repair: remove this second value for `name`"),
        "{o}"
    );
    assert!(
        o.contains("repair: remove the first value for `name` and keep this one"),
        "{o}"
    );
}

#[test]
fn a_value_before_the_dot_for_no_parameters_offers_the_bare_call() {
    let o = out("seed() = 42;\nx = 3.seed;\n");
    assert!(o.contains("repair: call it as `seed()`"), "{o}");
    assert!(
        o.contains("repair: add a first parameter to the declaration of `seed`"),
        "{o}"
    );
}

#[test]
fn a_call_through_a_value_is_offered_no_edit_of_a_declaration() {
    let o = out("h = (a) -> a;\nx = h(1, 2);\n");
    assert!(o.contains("repair: remove this argument"), "{o}");
    assert!(!o.contains("declaration"), "{o}");
}

#[test]
fn a_call_of_no_parameters_given_two_arguments_reports_the_first() {
    let o = out("z() = 1;\nx = z(1, 2);\n");
    assert!(o.contains("`z` takes no arguments."), "{o}");
    assert_eq!(o.matches("one more than `z` takes").count(), 1, "{o}");
}

#[test]
fn an_extra_argument_and_a_name_for_no_parameter_are_both_reported() {
    let o = out("p(positional a: int) = a;\nx = p(1, 2, b: 3);\n");
    assert!(o.contains("one more than `p` takes"), "{o}");
    assert!(o.contains("`p` has no parameter of that name"), "{o}");
}

/// Every "repair: write" these rows offer gives a program that checks.
#[test]
fn each_offered_rewrite_checks() {
    let srcs = [
        moved("int"),
        format!("{GREET}x = greet(\"Al\", puntc: \"?\");\n"),
        "g() = 1;\nf(positional a: int, positional b: int) = a + b;\nx = f(g(2));\n".into(),
    ];
    for src in srcs {
        let fixed = written(&src);
        assert!(!fixed.is_empty(), "no rewrite offered for\n{src}");
        for (p, note) in fixed {
            assert!(
                zedc::run::load(p.as_bytes()).is_ok(),
                "{note} gives a program that does not check:\n{p}"
            );
        }
    }
}

/// The programs above, each checked alone on a thread of its own and all of them one after
/// another on one thread, give the same diagnostics.
#[test]
fn batch_and_single_file_output_agree() {
    let srcs: Vec<String> = [
        format!("{LIMIT}x = limit(5, 0, 10, 2);\n"),
        moved("int"),
        moved("String"),
        format!("{GREET}x = greet(\"Al\", puntc: \"?\");\n"),
        format!("{GREET}x = greet(\"Al\", punct: \"!\", puntc: \"?\");\n"),
        "p(positional a: int) = a;\nx = p(1, 2, b: 3);\n".into(),
    ]
    .iter()
    .map(|s| with_main(s))
    .collect();
    let alone: Vec<String> = (srcs.iter().cloned())
        .map(|s| std::thread::spawn(move || rejected(&s)).join().unwrap())
        .collect();
    let batch: Vec<String> = srcs.iter().map(|s| rejected(s)).collect();
    assert_eq!(alone, batch);
}

/// `n` calls, each with an argument beyond the parameters of an inner call and a name near
/// a parameter, for the scaling test (`bench::argument_rows`).
pub(super) fn calls(n: usize) -> String {
    let mut src = String::from(GREET);
    src += "g(positional a: int) = a;\nf(positional a: int, positional b: int) = a;\n";
    for i in 0..n {
        src +=
            &format!("y{i} = {i};\nx{i} = f(g(1, y{i}));\nw{i} = greet(\"Al\", puntc: \"?\");\n");
    }
    with_main(&src)
}

/// Each of the `n` calls of [`calls`] is offered both repairs.
pub(super) fn calls_offered(src: &str, n: usize) {
    let o = rejected(src);
    assert_eq!(o.matches("repair: write `punct: \"?\"`").count(), n, "{o}");
    for i in [0, n / 2, n - 1] {
        assert!(
            o.contains(&format!("repair: write `f(g(1), y{i})`")),
            "{i}: {o}"
        );
    }
}

#[test]
fn many_calls_are_each_offered_their_repairs() {
    for n in [1, 3, 8] {
        calls_offered(&calls(n), n);
    }
}
