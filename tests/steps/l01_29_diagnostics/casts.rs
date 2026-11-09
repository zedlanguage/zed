//! Two numeric values with no common carrier (DESIGN.md sec:diagnostics; item CAST-menu): Zed
//! converts no value implicitly, so `r + x` with `r: rat` and `x: f64` is rejected. The
//! rejection shows both operands with their carriers and where each carrier comes from, and
//! its menu is the casts the checker accepts, written at the operand: `f64(r)`, `rat(x)`.

use zed_tests::scaling::{self, Meter, on_a_thread};

use super::{rejected, steps};
use zedc::ast::Stmt;
use zedc::rejection::Row;
use zedc::resolve::Resolution;
use zedc::run::load;

/// The program `src` with the one occurrence of `from` replaced by `to`.
fn edited(src: &str, from: &str, to: &str) -> String {
    assert_eq!(src.matches(from).count(), 1, "{from}");
    src.replace(from, to)
}

/// Asserts that `src` checks.
fn checks(src: &str) {
    load(src.as_bytes()).unwrap_or_else(|e| panic!("{src}\n{e}"));
}

/// The menu entry offering the cast `cast`.
fn offered(cast: &str) -> String {
    format!("repair: write `{cast}`; the checker accepts that")
}

/// `body` as the one function of a program.
fn program(body: &str) -> String {
    format!("{body}\nmain(stdin: Lines) -> (stdout: Lines) {{\n  stdout <- \"a\";\n}}\n")
}

#[test]
fn a_rat_and_an_f64_are_shown_with_their_carriers_and_the_casts_between_them() {
    let src = program("total(r: rat, x: f64) = r + x;");
    let out = rejected(&src);
    assert_eq!(
        out.lines().next(),
        Some(
            "1:25: `+` does not take (rat, f64): these are the types of its arguments here, and `+` has no arrow that takes them all"
        ),
        "{out}"
    );
    let s = steps(&out);
    for step in [
        "`r` is rat here",
        "`r` is declared `rat`",
        "`x` is f64 here",
        "`x` is declared `f64`",
        "`+` takes (f64, f64) -> f64",
        "`+` takes (rat, rat) -> rat",
    ] {
        assert!(s.contains(&step), "{step}\n{out}");
    }
    let menu: Vec<&str> = s
        .iter()
        .copied()
        .filter(|t| t.starts_with("repair:"))
        .collect();
    assert_eq!(menu, [offered("f64(r)"), offered("rat(x)")], "{out}");
    checks(&edited(&src, "r + x", "f64(r) + x"));
    checks(&edited(&src, "r + x", "r + rat(x)"));
}

#[test]
fn an_int_and_an_f64_offer_f64_of_the_int() {
    let src = program("scaled(n: int, x: f64) = n * x;");
    let out = rejected(&src);
    assert!(
        out.starts_with("1:26: `*` does not take (int, f64): these are the types of its arguments here, and `*` has no arrow that takes them all"),
        "{out}"
    );
    assert!(out.contains(&offered("f64(n)")), "{out}");
    checks(&edited(&src, "n * x", "f64(n) * x"));
    // The other way is a cast too: `int(x)` is `int | #inexact | #invalid`, and `*` passes
    // those atoms on.
    assert!(out.contains(&offered("int(x)")), "{out}");
    checks(&edited(&src, "n * x", "n * int(x)"));
}

#[test]
fn a_comparison_offers_the_same_casts() {
    let src = program("late(r: rat, x: f64) = r < x;");
    let out = rejected(&src);
    for (to, cast) in [("f64(r) < x", "f64(r)"), ("r < rat(x)", "rat(x)")] {
        assert!(out.contains(&offered(cast)), "{cast}\n{out}");
        checks(&edited(&src, "r < x", to));
    }
}

#[test]
fn parameters_without_declared_types_are_shown_with_the_uses_that_gave_their_carriers() {
    let src = program("mix(positional a, positional b) = (a * 1r, b * 2.5f64, a + b);");
    let out = rejected(&src);
    assert!(
        out.starts_with("1:56: `+` does not take (rat, f64): these are the types of its arguments here, and `+` has no arrow that takes them all"),
        "{out}"
    );
    let s = steps(&out);
    for step in [
        "`a` has no declared type; its uses give it rat",
        "`b` has no declared type; its uses give it f64",
        "the literal 2.5f64 takes f64",
    ] {
        assert!(s.contains(&step), "{step}\n{out}");
    }
    assert!(out.contains(&offered("f64(a)")), "{out}");
    assert!(out.contains(&offered("rat(b)")), "{out}");
    checks(&edited(&src, "a + b", "f64(a) + b"));
    checks(&edited(&src, "a + b", "a + rat(b)"));
}

#[test]
fn values_joined_by_an_earlier_use_offer_the_cast_of_the_joined_one() {
    // `a + b` gives `a` and `b` one carrier, `a * 1r` makes it rat, and `b * 2.5f64` meets f64.
    let src = program("join(positional a, positional b) = (a + b, a * 1r, b * 2.5f64);");
    let out = rejected(&src);
    let s = steps(&out);
    assert!(s.contains(&"`+` gives these values one carrier"), "{out}");
    assert!(out.contains(&offered("f64(b)")), "{out}");
    checks(&edited(&src, "b * 2.5f64", "f64(b) * 2.5f64"));
}

#[test]
fn an_operand_that_is_not_a_name_is_shown_with_the_cast_around_it() {
    let src = program("area(r: rat, x: f64) = r * r + x;");
    let out = rejected(&src);
    assert!(
        out.contains("repair: wrap this in `f64(…)`; the checker accepts that"),
        "{out}"
    );
    checks(&edited(&src, "r * r + x", "f64(r * r) + x"));
}

#[test]
fn a_value_with_no_numeric_cast_is_offered_none() {
    // `bool` has no cast to a number, and a number none to `bool`: the menu offers no cast
    // that does not exist. Types a program declares are built from step L2.5; this one
    // stands for them, since the casts tried are the prelude's (`int`, `rat`, `f64`, `String`).
    let src = program("bump(b: bool, x: f64) = b + x;");
    let out = rejected(&src);
    assert!(
        out.starts_with("1:25: `+` does not take (bool, f64): these are the types of its arguments here, and `+` has no arrow that takes them all"),
        "{out}"
    );
    assert!(!out.contains("repair:"), "{out}");
}

/// `n` functions, each adding a `rat` and an `f64`.
fn mixed(n: usize) -> String {
    (0..n)
        .map(|i| format!("sum{i}(r: rat, x: f64) = r + x;\n"))
        .collect()
}

/// `n` functions, each with three rejections of the row: a call of `max`, a `rat` literal
/// beside an `f64`, and an `f64` literal compared with an `int`.
fn called(n: usize) -> String {
    (0..n)
        .map(|i| format!("call{i}(r: rat, x: f64, n: int) = (max(r, x), x * 1r, n == 1.0);\n"))
        .collect()
}

#[test]
fn the_cast_menus_of_many_rejections_scale() {
    // Each rejection tries four casts at each of its two operands: a constant per rejection.
    scaling::check("the cast menus of n rejected sums", 300, |n| {
        let out = rejected(&mixed(n));
        assert_eq!(out.matches(&offered("f64(r)")).count(), n);
        assert_eq!(out.matches(&offered("rat(x)")).count(), n);
    });
}

/// A program of one function giving a tuple of `m` integers and `r` functions each adding a
/// `rat` and an `f64`, parsed and resolved, so that only its check is measured.
fn padded(m: usize, r: usize) -> (Vec<Stmt>, Resolution) {
    padded_with(m, &mixed(r))
}

/// A program of one function giving a tuple of `m` integers and the functions `rest`, parsed
/// and resolved.
fn padded_with(m: usize, rest: &str) -> (Vec<Stmt>, Resolution) {
    let mut text = String::from("big() = (0");
    text.push_str(&", 1".repeat(m));
    text.push_str(");\n");
    text.push_str(rest);
    let tokens = zedc::lex::lex_fence(&text).expect("the program lexes");
    let tree = zedc::parse::parse(&text, &tokens, "Unit", zedc::parse::TOP).expect("it parses");
    let stmts = zedc::ast::unit(&text, &tokens, &tree).expect("it is a unit");
    let res = zedc::resolve::resolve(&stmts).expect("it resolves");
    (stmts, res)
}

#[test]
fn a_cast_menu_costs_the_same_in_a_larger_program() {
    // The test above holds the work of n rejections to n, but not the cost of one rejection
    // to a constant: the checker spends about 33,000 instructions on each expression and a
    // scan of its record of expressions about 16 per entry, so a menu that scanned the whole
    // record once per offered cast, O(n) per rejection and O(n²) in all, did 8.8 times the
    // work at 1,000 and 8,000 rejections and passed it. Here the work of the rejections
    // alone, the check of the program with them less the check without, is held to the
    // limit of work of order n^0 as the program around them grows from m to 8m expressions.
    // That scan did 4.1 times the work at m = 60,000 against 480,000; this code 1.00 times.
    // The difference of two counts needs the count of instructions; a meter of processor time
    // does not repeat closely enough. With malloc's cache per thread, one check at 8m now and
    // then took 0.26 billion instructions more in malloc, from what earlier threads left in
    // its arena, and the difference came out 1.38 to 1.44 times (4 of 18 runs of this step on
    // 2026-11-09). `tools/run_tests.sh` turns that cache off: the difference then repeats to
    // within 0.04% when the checks run alone, and beside this step's other tests, which
    // allocate at the same time, it was 0.97 to 1.02 times in 30 runs.
    const R: usize = 100;
    let meter = &mut Meter::new();
    let mut rejections = |m: usize| {
        let mut work = |r: usize| {
            let (stmts, res) = padded(m, r);
            let mut errors = 0;
            let units = meter
                .work(|| {
                    errors = on_a_thread(256 << 20, || zedc::check::walk::check(&stmts, &res))
                        .errors
                        .iter()
                        .filter(|e| e.notes.iter().any(|n| n.text.starts_with("repair:")))
                        .count();
                })
                .units;
            assert_eq!(errors, r, "rejections with a menu among {r}");
            units
        };
        let without = work(0);
        work(R)
            .checked_sub(without)
            .expect("the rejections add work")
    };
    let m = 60_000;
    let limit = scaling::limit(m, scaling::FACTOR * m, 0);
    let (small, large) = (rejections(m), rejections(scaling::FACTOR * m));
    let ratio = large as f64 / small as f64;
    assert!(
        ratio <= limit,
        "{R} rejections beside {m} and {} expressions: {small} and {large} {}, {ratio:.2} \
         times the work; for work of order n^0 the rule of low complexity allows at most \
         {limit:.2} times (DESIGN.md Part G)",
        scaling::FACTOR * m,
        meter.unit(),
    );
}

/// The errors of checking `text`, parsed and resolved.
fn errors(text: &str) -> Vec<zedc::ast::Error> {
    let tokens = zedc::lex::lex_fence(text).expect("the program lexes");
    let tree = zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP).expect("it parses");
    let stmts = zedc::ast::unit(text, &tokens, &tree).expect("it is a unit");
    let res = zedc::resolve::resolve(&stmts).expect("it resolves");
    zedc::check::walk::check(&stmts, &res).errors
}

/// The rows of the errors of checking `text`.
fn rows(text: &str) -> Vec<Option<Row>> {
    errors(text).into_iter().map(|e| e.row).collect()
}

/// The menu of the one rejection of `src`: its entries after `repair: `.
fn menu(src: &str) -> Vec<String> {
    let out = rejected(src);
    steps(&out)
        .iter()
        .filter_map(|t| t.strip_prefix("repair: "))
        .map(str::to_string)
        .collect()
}

/// The menu entry offering the cast or literal `cast`, after `repair: `.
fn entry(cast: &str) -> String {
    format!("write `{cast}`; the checker accepts that")
}

#[test]
fn a_plain_literal_beside_a_value_of_another_carrier_is_a_case_of_the_row() {
    // README.md's `bad = q + 1.5;` with `q` an `int`: a decimal literal is never an `int`, so
    // the literal is refused in the row of a literal at a carrier it cannot take, with the
    // operation rewritten in its message and each cast of the operand that checks in its menu.
    let src = program("half(q: int) = q + 1.5;");
    assert_eq!(rows(&src), [Some(Row::LiteralCarrier)]);
    let out = rejected(&src);
    assert!(
        out.starts_with(
            "1:20: the literal `1.5` is a decimal, and `+` expects `int`, the carrier of `q`; a \
             decimal literal is never an `int`; write `f64(q) + 1.5`"
        ),
        "{out}"
    );
    assert!(steps(&out).contains(&"`q` is declared `int`"), "{out}");
    assert_eq!(menu(&src), [entry("rat(q)"), entry("f64(q)")]);
    checks(&edited(&src, "q + 1.5", "f64(q) + 1.5"));
    checks(&edited(&src, "q + 1.5", "rat(q) + 1.5"));
    // Beside a `rat` a bare decimal takes `rat`; one with the suffix `f64` is a case of the
    // row.
    checks(&program("half(r: rat) = r * 1.5;"));
    let src = program("half(r: rat) = r * 1.5f64;");
    assert_eq!(rows(&src), [Some(Row::LiteralCarrier)]);
    assert_eq!(menu(&src), [entry("f64(r)")]);
}

#[test]
fn a_literal_an_operator_takes_at_another_carrier_is_not_a_case_of_the_row() {
    // `"a" ++ 1` refuses the literal too, but `++` takes no number at all: no carrier is
    // missing, and the error keeps no row of the two numeric values.
    let src = program("tag(s: String) = s ++ 1;");
    assert!(!rows(&src).contains(&Some(Row::NoCommonCarrier)), "{src}");
}

#[test]
fn a_call_of_max_offers_the_casts_of_its_arguments() {
    let src = program("top(r: rat, x: f64) = max(r, x);");
    let out = rejected(&src);
    assert!(
        out.starts_with("1:23: `max` does not take (rat, f64): these are the types of its arguments here, and `max` has no arrow that takes them all"),
        "{out}"
    );
    assert_eq!(rows(&src), [Some(Row::NoCommonCarrier)]);
    assert_eq!(menu(&src), [entry("f64(r)"), entry("rat(x)")]);
    checks(&edited(&src, "max(r, x)", "max(f64(r), x)"));
    checks(&edited(&src, "max(r, x)", "max(r, rat(x))"));
    let src = program("low(n: int, x: f64) = min(n, x);");
    assert!(menu(&src).contains(&entry("f64(n)")), "{src}");
    checks(&edited(&src, "min(n, x)", "min(f64(n), x)"));
}

#[test]
fn a_rat_literal_is_offered_its_literal_forms_not_a_cast() {
    let src = program("scaled(b: f64) = b * 1r;");
    assert_eq!(rows(&src), [Some(Row::NoCommonCarrier)]);
    assert_eq!(menu(&src), [entry("rat(b)"), entry("1.0")]);
    checks(&edited(&src, "b * 1r", "b * 1.0"));
    checks(&edited(&src, "b * 1r", "rat(b) * 1r"));
    // A negative literal keeps its sign, and an integral one beside an `int` drops the point.
    let src = program("scaled(n: int) = n * -3r;");
    assert_eq!(menu(&src), [entry("rat(n)"), entry("-3")]);
    checks(&edited(&src, "n * -3r", "n * -3"));
    let src = program("scaled(b: f64) = b * 0.5r;");
    assert_eq!(menu(&src), [entry("rat(b)"), entry("0.5")]);
    checks(&edited(&src, "b * 0.5r", "b * 0.5"));
}

#[test]
fn a_rat_literal_that_no_f64_holds_exactly_is_offered_no_literal() {
    // 0.1 has no exact `f64`; writing `0.1` would change the number, so only the cast of the
    // other operand is offered.
    let src = program("scaled(b: f64) = b * 0.1r;");
    assert_eq!(menu(&src), [entry("rat(b)")]);
}

#[test]
fn a_comparison_with_a_literal_of_another_carrier_offers_the_cast_of_the_value() {
    let src = program("one(n: int) = n == 1.0;");
    assert_eq!(rows(&src), [Some(Row::LiteralCarrier)]);
    let out = rejected(&src);
    let s = steps(&out);
    assert!(s.contains(&"`n` is declared `int`"), "{out}");
    assert_eq!(menu(&src), [entry("rat(n)"), entry("f64(n)")]);
    checks(&edited(&src, "n == 1.0", "f64(n) == 1.0"));
    checks(&edited(&src, "n == 1.0", "rat(n) == 1.0"));
    checks(&edited(&src, "n == 1.0", "n == 1"));
    // Beside a `rat` a bare decimal takes `rat`; one with the suffix `f64` is refused.
    checks(&program("one(r: rat) = r == 1.0;"));
    let src = program("one(r: rat) = r == 1.0f64;");
    assert_eq!(menu(&src), [entry("f64(r)")]);
    checks(&edited(&src, "r == 1.0f64", "f64(r) == 1.0f64"));
}

#[test]
fn two_literals_of_different_carriers_compared_show_both() {
    // Each literal has a suffix, so neither takes the other's carrier.
    let src = program("same() = 1r == 1.0f64;");
    assert_eq!(rows(&src), [Some(Row::LiteralCarrier)]);
    let out = rejected(&src);
    let s = steps(&out);
    // A `rat` literal is shown as the expression it is.
    assert!(s.contains(&"this expression is 1r"), "{out}");
    assert!(s.contains(&"this literal, 1.0f64, is 1.0"), "{out}");
    // A bare `1` takes the carrier of a decimal with a suffix.
    checks(&program("same() = 1 == 1.0f64;"));
}

#[test]
fn the_menus_of_calls_literals_and_comparisons_scale() {
    // Each rejection tries a constant number of casts and literal forms.
    scaling::check(
        "the menus of 3n rejected calls, literals and comparisons",
        200,
        |n| {
            let out = rejected(&called(n));
            assert_eq!(out.matches(&offered("f64(r)")).count(), n);
            assert_eq!(out.matches(&offered("1.0")).count(), n);
            assert_eq!(out.matches(&offered("f64(n)")).count(), n);
        },
    );
}

#[test]
fn the_menus_of_calls_literals_and_comparisons_cost_the_same_in_a_larger_program() {
    // As `a_cast_menu_costs_the_same_in_a_larger_program`, for the menus of a call of `max`, a
    // `rat` literal and a comparison with a literal: the work of R functions of three
    // rejections each, held to order n^0 as the program around them grows from m to 8m.
    const R: usize = 100;
    let meter = &mut Meter::new();
    let mut rejections = |m: usize| {
        let mut work = |r: usize| {
            let (stmts, res) = padded_with(m, &called(r));
            let mut errors = 0;
            let units = meter
                .work(|| {
                    errors = on_a_thread(256 << 20, || zedc::check::walk::check(&stmts, &res))
                        .errors
                        .iter()
                        .filter(|e| e.notes.iter().any(|n| n.text.starts_with("repair:")))
                        .count();
                })
                .units;
            assert_eq!(errors, 3 * r, "rejections with a menu among {r} functions");
            units
        };
        let without = work(0);
        work(R)
            .checked_sub(without)
            .expect("the rejections add work")
    };
    let m = 60_000;
    let limit = scaling::limit(m, scaling::FACTOR * m, 0);
    let (small, large) = (rejections(m), rejections(scaling::FACTOR * m));
    let ratio = large as f64 / small as f64;
    assert!(
        ratio <= limit,
        "{R} functions beside {m} and {} expressions: {small} and {large} {}, {ratio:.2} \
         times the work; for work of order n^0 the rule of low complexity allows at most \
         {limit:.2} times (DESIGN.md Part G)",
        scaling::FACTOR * m,
        meter.unit(),
    );
}
