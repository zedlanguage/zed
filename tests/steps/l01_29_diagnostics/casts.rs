//! Two numeric values with no common carrier (DESIGN.md sec:diagnostics; item CAST-menu): Zed
//! converts no value implicitly, so `r + x` with `r: rat` and `x: f64` is rejected. The
//! rejection shows both operands with their carriers and where each carrier comes from, and
//! its menu is the widening casts the checker accepts, written at the operand: `rat(n)` beside
//! a `rat` with `n: int`. A cast that narrows is never offered (DESIGN.md sec:diagnostics), so
//! `r + x` has none: `f64(r)` is inexact and `rat(x)` is `#invalid` at NaN and the infinities.

use zed_tests::scaling::{self, Meter, on_a_thread};
use zed_tests::step_helpers::l01_19a_command_line::run;

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
    format!("{body}\nmain(m: MainArgs) {{\n  m.stdout <- \"a\";\n}}\n")
}

#[test]
fn a_rat_and_an_f64_are_shown_with_their_carriers_and_offered_no_cast() {
    let src = program("total(r: rat, x: f64) = r + x;");
    let out = rejected(&src);
    assert_eq!(
        out.lines().next(),
        Some("1:25: `+` does not take (rat, f64): no arrow of `+` takes these types."),
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
    // Each cast checks, but each narrows, so neither is offered.
    assert!(!out.contains("repair:"), "{out}");
    checks(&edited(&src, "r + x", "f64(r) + x"));
    checks(&edited(&src, "r + x", "r + rat(x)"));
}

#[test]
fn an_unbounded_int_and_an_f64_offer_no_cast() {
    let src = program("scaled(n: int, x: f64) = n * x;");
    let out = rejected(&src);
    assert!(
        out.starts_with("1:26: `*` does not take (int, f64): no arrow of `*` takes these types"),
        "{out}"
    );
    // `f64(n)` is inexact above 2^53 and `int(x)` narrows: neither is offered.
    assert!(!out.contains("repair:"), "{out}");
    // An `int` beside a `rat` is offered `rat(n)`, which holds each int exactly.
    let src = program("scaled(n: int, r: rat) = n * r;");
    let out = rejected(&src);
    assert!(out.contains(&offered("rat(n)")), "{out}");
    assert!(!out.contains(&offered("int(r)")), "{out}");
    checks(&edited(&src, "n * r", "rat(n) * r"));
}

#[test]
fn a_comparison_offers_the_same_casts() {
    // The comparison is rewritten whole, in the headline and as the repair.
    let src = program("late(n: int, r: rat) = n < r;");
    let out = rejected(&src);
    assert!(
        out.starts_with(
            "1:24: Cannot compare unequal types: `n : int < r : rat`. Try `rat(n) < r` instead.\n"
        ),
        "{out}"
    );
    assert!(steps(&out).contains(&"repair: `rat(n) < r`"), "{out}");
    assert!(!out.contains("int(r)"), "{out}");
    checks(&edited(&src, "n < r", "rat(n) < r"));
    // Each cast narrows, so the headline offers none, and the one repair says a type has to
    // change, as for two components of tuples.
    let out = rejected(&program("late(r: rat, x: f64) = r < x;"));
    assert!(
        out.starts_with("1:24: Cannot compare unequal types: `r : rat < x : f64`.\n"),
        "{out}"
    );
    assert_eq!(
        menu(&program("late(r: rat, x: f64) = r < x;")),
        ["change the type of `r` or `x` so that the two compare"]
    );
}

#[test]
fn an_int_compared_with_an_f64_is_offered_the_widening_cast_where_it_is_exact() {
    // The author's example (DESIGN.md sec:facets, comparisons across units): an int whose
    // values the checker proves lie within ±2^53, here by the test around the comparison, is
    // offered `f64(tempC)`, which holds each of them exactly.
    let src = program(
        "warm(tempC: int, tempK: f64) = \
         if tempC >= -273 && tempC <= 1000 { tempC < tempK } else { false };",
    );
    let out = rejected(&src);
    assert!(
        out.starts_with(
            "1:68: Cannot compare unequal types: `tempC : int < tempK : f64`. \
             Try `f64(tempC) < tempK` instead.\n"
        ),
        "{out}"
    );
    checks(&edited(&src, "{ tempC < tempK }", "{ f64(tempC) < tempK }"));
    // The example as DESIGN writes it, `int[-273..=1000]`, waits for refinements; the step
    // that compiles them changes this pin to the headline above with that type.
    let out = rejected(&program(
        "warm(tempC: int[-273..=1000], tempK: f64) = tempC < tempK;",
    ));
    assert_eq!(
        out.lines().next(),
        Some(concat!(
            "1:16: ",
            zed_tests::not_yet!("the refinement `[-273..=1000]`")
        )),
        "{out}"
    );
    // An unbounded `int` is offered no cast: `f64(n)` carries `#inexact` above 2^53.
    let src = program("warm(tempC: int, tempK: f64) = tempC < tempK;");
    let out = rejected(&src);
    assert!(
        out.starts_with("1:32: Cannot compare unequal types: `tempC : int < tempK : f64`.\n"),
        "{out}"
    );
    assert!(!out.contains("f64(tempC)"), "{out}");
}

#[test]
fn parameters_without_declared_types_are_shown_with_the_uses_that_gave_their_carriers() {
    let src = program("mix(positional a, positional b) = (a * 1r, b * 2.5f64, a + b);");
    let out = rejected(&src);
    assert!(
        out.starts_with("1:56: `+` does not take (rat, f64): no arrow of `+` takes these types."),
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
    // A `rat` and an `f64`: no cast is offered.
    assert!(!out.contains("repair:"), "{out}");
}

#[test]
fn values_joined_by_an_earlier_use_offer_the_cast_of_the_joined_one() {
    // `a + b` gives `a` and `b` one carrier, `a + n` makes it int, and `b * 2.5r` meets rat,
    // which holds each int exactly.
    let src = program("join(positional a, positional b, n: int) = (a + b, a + n, b * 2.5r);");
    let out = rejected(&src);
    let s = steps(&out);
    assert!(s.contains(&"`+` gives these values one carrier"), "{out}");
    assert!(out.contains(&offered("rat(b)")), "{out}");
    checks(&edited(&src, "b * 2.5r", "rat(b) * 2.5r"));
}

#[test]
fn an_operand_that_is_not_a_name_is_shown_with_the_cast_around_it() {
    let src = program("area(n: int, r: rat) = n * n + r;");
    let out = rejected(&src);
    assert!(
        out.contains("repair: wrap this in `rat(…)`; the checker accepts that"),
        "{out}"
    );
    checks(&edited(&src, "n * n + r", "rat(n * n) + r"));
}

#[test]
fn a_value_with_no_numeric_cast_is_offered_none() {
    // `bool` has no cast to a number, and a number none to `bool`: the menu offers no cast
    // that does not exist. Types a program declares are built from step L2.5; this one
    // stands for them, since the casts tried are the prelude's (`int`, `rat`, `f64`, `String`).
    let src = program("bump(b: bool, x: f64) = b + x;");
    let out = rejected(&src);
    assert!(
        out.starts_with("1:25: `+` does not take (bool, f64): no arrow of `+` takes these types"),
        "{out}"
    );
    assert!(!out.contains("repair:"), "{out}");
}

/// `n` functions, each adding an `int` and a `rat`.
fn mixed(n: usize) -> String {
    (0..n)
        .map(|i| format!("sum{i}(n: int, r: rat) = n + r;\n"))
        .collect()
}

/// `n` functions, each with three rejections of the row: a call of `max`, a `rat` literal
/// beside an `f64`, and a decimal literal compared with an `int`.
fn called(n: usize) -> String {
    (0..n)
        .map(|i| format!("call{i}(r: rat, x: f64, n: int) = (max(n, r), x * 1r, n == 1.0);\n"))
        .collect()
}

#[test]
fn the_cast_menus_of_many_rejections_scale() {
    // Each rejection tries four casts at each of its two operands: a constant per rejection.
    scaling::check("the cast menus of n rejected sums", 300, |n| {
        let out = rejected(&mixed(n));
        assert_eq!(out.matches(&offered("rat(n)")).count(), n);
    });
}

/// A program of one function giving a tuple of `m` integers and `r` functions each adding an
/// `int` and a `rat`, parsed and resolved, so that only its check is measured.
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
    // allocate at the same time, it was 0.97 to 1.02 times in 30 runs. At m = 60,000 this test
    // took 36 s alone at load 46, so m is now 30,000: a scan of that record once per offered
    // repair still did 1.88 times the work there, against a limit of 1.32 (TESTS-l01_29-split).
    const R: usize = 100;
    let meter = &mut Meter::new();
    let unit = meter.unit();
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
    let m = 30_000;
    scaling::hold(
        &format!(
            "{R} rejections beside {m} and {} expressions",
            scaling::FACTOR * m
        ),
        unit,
        rejections(m),
        rejections(scaling::FACTOR * m),
        0,
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

/// The lines of the fixes of the one rejection of `src`, each without what it then holds.
fn fixed(src: &str) -> Vec<String> {
    let out = rejected(src);
    let Some((_, rest)) = out.split_once("\n  fixes, each checked here:\n") else {
        return Vec::new();
    };
    (rest.lines())
        .take_while(|l| l.starts_with("    "))
        .map(|l| {
            l.trim_start()
                .split_once("  ")
                .map_or(l.trim(), |(line, _)| line)
                .to_string()
        })
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
    // The menu stands after the steps (DESIGN.md sec:diagnostics).
    let (head, fixes) = (out.split_once("\n  fixes, each checked here:\n"))
        .unwrap_or_else(|| panic!("no menu: {out}"));
    assert!(
        head.starts_with(
            "1:20: A decimal literal is never an `int`: `q : int + 1.5`. Try \
             `half(q: int) = rat(q) + 1.5` instead.\n  [1] "
        ),
        "{out}"
    );
    // `f64(q)` is not offered: `q: int` is unbounded, and `f64` is exact only up to 2^53, so
    // that cast can lose information (DESIGN.md sec:diagnostics, "A repair never narrows a
    // type").
    assert_eq!(
        fixes,
        "    half(q: int) = rat(q) + 1.5;    q is cast to rat, and `+` takes two rat"
    );
    assert!(!fixes.contains("\n  ["), "a step after the menu: {out}");
    assert!(steps(&out).contains(&"`q` is declared `int`"), "{out}");
    assert_eq!(menu(&src), [entry("rat(q)")]);
    checks(&edited(&src, "q + 1.5", "rat(q) + 1.5"));
    // Beside a `rat` a bare decimal takes `rat`; one with the suffix `f64` is a case of the
    // row.
    checks(&program("half(r: rat) = r * 1.5;"));
    // `f64(r)` is inexact, so no cast is offered.
    let src = program("half(r: rat) = r * 1.5f64;");
    assert_eq!(rows(&src), [Some(Row::LiteralCarrier)]);
    assert!(menu(&src).is_empty());
}

#[test]
fn a_literal_an_operator_takes_at_another_carrier_is_not_a_case_of_the_row() {
    // `"a" ++ 1` refuses the literal too, but `++` takes no number at all: no carrier is
    // missing, and the error keeps no row of the two numeric values.
    let src = program("tag(s: String) = s ++ 1;");
    assert!(!rows(&src).contains(&Some(Row::NoCommonCarrier)), "{src}");
}

#[test]
fn a_call_of_max_offers_the_widening_casts_of_its_arguments() {
    let src = program("top(r: rat, x: f64) = max(r, x);");
    let out = rejected(&src);
    assert!(
        out.starts_with(
            "1:23: `max` does not take (rat, f64): no arrow of `max` takes these types"
        ),
        "{out}"
    );
    assert_eq!(rows(&src), [Some(Row::NoCommonCarrier)]);
    assert!(menu(&src).is_empty(), "{out}");
    let src = program("low(n: int, r: rat) = min(n, r);");
    assert_eq!(menu(&src), [entry("rat(n)")]);
    checks(&edited(&src, "min(n, r)", "min(rat(n), r)"));
}

#[test]
fn a_rat_literal_is_offered_its_literal_forms_not_a_cast() {
    let src = program("scaled(b: f64) = b * 1r;");
    assert_eq!(rows(&src), [Some(Row::NoCommonCarrier)]);
    let out = rejected(&src);
    assert!(
        out.starts_with(
            "1:22: The suffix makes the literal `1r` a `rat`, never `f64`. Try \
             `scaled(b: f64) = b * 1.0` instead.\n"
        ),
        "{out}"
    );
    // `rat(b)` is `#invalid` at NaN and the infinities, so it is not offered.
    assert_eq!(fixed(&src), ["scaled(b: f64) = b * 1.0;"]);
    assert!(menu(&src).is_empty());
    checks(&edited(&src, "b * 1r", "b * 1.0"));
    // A negative literal keeps its sign, and an integral one beside an `int` drops the point.
    // The literal's own form comes first, as the headline names the literal; the cast is a
    // step as well.
    let src = program("scaled(n: int) = n * -3r;");
    assert_eq!(
        fixed(&src),
        ["scaled(n: int) = n * -3;", "scaled(n: int) = rat(n) * -3r;"]
    );
    assert_eq!(menu(&src), [entry("rat(n)")]);
    checks(&edited(&src, "n * -3r", "n * -3"));
    let src = program("scaled(b: f64) = b * 0.5r;");
    assert_eq!(fixed(&src), ["scaled(b: f64) = b * 0.5;"]);
    checks(&edited(&src, "b * 0.5r", "b * 0.5"));
}

#[test]
fn a_rat_literal_that_no_f64_holds_exactly_is_offered_no_literal() {
    // 0.1 has no exact `f64`; writing `0.1` would change the number, and `rat(b)` narrows, so
    // nothing is offered.
    let src = program("scaled(b: f64) = b * 0.1r;");
    assert!(menu(&src).is_empty());
    assert!(fixed(&src).is_empty());
}

#[test]
fn a_comparison_with_a_literal_of_another_carrier_offers_the_cast_of_the_value() {
    let src = program("one(n: int) = n == 1.0;");
    assert_eq!(rows(&src), [Some(Row::LiteralCarrier)]);
    let out = rejected(&src);
    let s = steps(&out);
    assert!(s.contains(&"`n` is declared `int`"), "{out}");
    assert_eq!(menu(&src), [entry("rat(n)")]);
    checks(&edited(&src, "n == 1.0", "rat(n) == 1.0"));
    checks(&edited(&src, "n == 1.0", "n == 1"));
    // Beside a `rat` a bare decimal takes `rat`; one with the suffix `f64` is refused.
    checks(&program("one(r: rat) = r == 1.0;"));
    // `f64(r)` is inexact, so no cast is offered.
    let src = program("one(r: rat) = r == 1.0f64;");
    assert!(menu(&src).is_empty());
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
            assert_eq!(out.matches(&offered("rat(n)")).count(), 2 * n);
            assert_eq!(out.matches("the literal is then the f64 1.0").count(), n);
        },
    );
}

#[test]
fn the_menus_of_calls_literals_and_comparisons_cost_the_same_in_a_larger_program() {
    // As `a_cast_menu_costs_the_same_in_a_larger_program`, for the menus of a call of `max`, a
    // `rat` literal and a comparison with a literal: the work of R functions of three
    // rejections each, held to order n^0 as the program around them grows from m to 8m. The
    // same scan per offered repair did 1.91 times the work at m = 30,000.
    const R: usize = 100;
    let meter = &mut Meter::new();
    let unit = meter.unit();
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
    let m = 30_000;
    scaling::hold(
        &format!(
            "{R} functions beside {m} and {} expressions",
            scaling::FACTOR * m
        ),
        unit,
        rejections(m),
        rejections(scaling::FACTOR * m),
        0,
    );
}

/// Row MSG-cast-repair-parens: a cast written around an operand in parentheses takes their
/// place, `String(2 + 13) < "a"` for `(2 + 13) < "a"`, as the program would be written; it
/// printed `String((2 + 13)) < "a"`. Each case is the operand as written, and the cast the
/// headline, the fix and the program rewritten with it write.
const IN_PARENTHESES: [(&str, &str); 6] = [
    ("(2 + 13)", "String(2 + 13)"),
    ("((2 + 13))", "String(2 + 13)"),
    ("( (2 + 13) )", "String(2 + 13)"),
    ("(b)", "String(b)"),
    // A cast of an operand without parentheses around the whole of it is written as before.
    ("b", "String(b)"),
    ("(b + 1) * (b - 1)", "String((b + 1) * (b - 1))"),
];

#[test]
fn a_cast_takes_the_place_of_the_parentheses_around_its_operand() {
    // The row's program.
    let out = rejected("f() { c = (2 + 13) < \"a\"; return c; }\n");
    assert_eq!(
        out.lines().next(),
        Some(
            "1:11: `<` does not take (int | f32 | f64 | rat, \"a\"): no arrow of `<` takes \
             these types. Try `String(2 + 13) < \"a\"` instead."
        ),
        "{out}"
    );
    for (operand, cast) in IN_PARENTHESES {
        let src = program(&format!(
            "f() {{ b = 2 + 13; c = {operand} < \"a\"; return c; }}"
        ));
        let out = rejected(&src);
        let headline = out.lines().next().expect("a headline");
        let at = format!(
            "1:{}: `<` does not take (",
            src.find("c = ").expect("it") + 5
        );
        assert!(headline.starts_with(&at), "{out}");
        let try_ = format!(" Try `{cast} < \"a\"` instead.");
        assert!(headline.ends_with(&try_), "{out}");
        let line = format!("f() {{ b = 2 + 13; c = {cast} < \"a\"; return c; }}");
        checks(&program(&line));
    }
}

#[test]
fn a_numeric_cast_takes_the_place_of_the_parentheses_around_its_operand() {
    // The cast of an operation's operand, of a name beside a decimal literal, and of a name
    // compared with a literal of another carrier, which other parts of the checker offer.
    for (src, from, to) in [
        (
            "area(n: int, r: rat) = (n * n) + r;",
            "(n * n)",
            "rat(n * n)",
        ),
        ("area(n: int, r: rat) = n * n + r;", "n * n", "rat(n * n)"),
        (
            "area(n: int, r: rat) = (n) * (n) + r;",
            "(n) * (n)",
            "rat((n) * (n))",
        ),
        ("one(n: int) = (n) == 1.0;", "(n)", "rat(n)"),
        ("one(n: int) = ((n)) == 1.0;", "((n))", "rat(n)"),
        ("half(q: int) = (q) + 1.5;", "(q)", "rat(q)"),
        ("half(q: int) = 1.5 * ((q));", "((q))", "rat(q)"),
    ] {
        let src = program(src);
        let out = rejected(&src);
        let line = edited(&src, from, to);
        let line = line.lines().next().expect("the function");
        // An operation's repair ends the headline; a comparison's fix is a line of the menu.
        let try_ = format!("Try `{to} ");
        let in_headline = out.lines().next().is_some_and(|h| h.contains(&try_));
        assert!(
            in_headline || fixed(&src).iter().any(|l| l == line),
            "{line}\n{out}"
        );
        checks(&edited(&src, from, to));
    }
}

/// `f` comparing `2 + 13` in `d` pairs of parentheses with a string.
fn nested(d: usize) -> String {
    format!(
        "f() {{ c = {}2 + 13{} < \"a\"; return c; }}\n",
        "(".repeat(d),
        ")".repeat(d)
    )
}

#[test]
fn a_cast_in_place_of_many_parentheses_scales() {
    // The parentheses are matched in one pass over the operand's tokens: O(d) for `d` pairs.
    let programs = scaling::inputs(777, nested);
    scaling::check(
        "the cast repair of an operand in n pairs of parentheses",
        777,
        |d| {
            let out = on_a_thread(256 << 20, || rejected(&programs[&d]));
            assert!(
                out.contains("Try `String(2 + 13) < \"a\"` instead."),
                "{out}"
            );
        },
    );
}

/// `f`, of one parameter `x: t`, called with the literal `lit`.
fn call_with(t: &str, lit: &str) -> String {
    format!(
        "f(x: {t}) = x;\nmain(m: MainArgs) {{\n  y = f(x: {lit});\n  m.stdout <- \"${{y}}\";\n}}\n"
    )
}

#[test]
fn a_literal_with_a_suffix_is_named_by_the_carrier_its_suffix_names() {
    // The headline names the literal's own carrier, `f32`, not the one expected: it said
    // "makes the literal `1.0f32` an `f64`, never `f64`" (MSG-never-f64-wording). The same
    // literal without its suffix is exactly the f64 1.0, so it is offered (DESIGN.md
    // sec:diagnostics, row "Two numeric values with no common carrier").
    let src = call_with("f64", "1.0f32");
    let out = rejected(&src);
    assert!(
        out.starts_with(
            "3:12: The suffix makes the literal `1.0f32` an `f32`, never `f64`. Try \
             `y = f(x: 1.0)` instead.\n"
        ),
        "{out}"
    );
    assert!(out.contains("the literal is then the f64 1.0"), "{out}");
    assert_eq!(fixed(&src), ["y = f(x: 1.0);"]);
    checks(&edited(&src, "1.0f32", "1.0"));
    // `1.0` for `1.0f64` beside an `f32`, as the row's own example has it; the value is
    // written as an `f32` is printed.
    let src = call_with("f32", "0.5f64");
    let out = rejected(&src);
    assert!(
        out.starts_with("3:12: The suffix makes the literal `0.5f64` an `f64`, never `f32`."),
        "{out}"
    );
    assert!(out.contains("the literal is then the f32 0.5"), "{out}");
    assert_eq!(fixed(&src), ["y = f(x: 0.5);"]);
    checks(&edited(&src, "0.5f64", "0.5"));
    // A negative literal keeps its sign.
    let src = call_with("f64", "-1.5f32");
    assert!(
        rejected(&src).starts_with(
            "3:12: The suffix makes the literal `-1.5f32` an `f32`, never `f64`. Try \
             `y = f(x: -1.5)` instead.\n"
        ),
        "{}",
        rejected(&src)
    );
    assert!(rejected(&src).contains("the literal is then the f64 -1.5"));
}

#[test]
fn a_literal_with_a_suffix_that_no_value_of_the_carrier_equals_is_offered_nothing() {
    // `0.1` has no exact `f64`, and `0.1f32` is another number again, so writing `0.1` would
    // change the number: nothing is offered, as for `0.1r` beside an `f64`.
    let src = call_with("f64", "0.1f32");
    let out = rejected(&src);
    assert_eq!(
        out.lines().next(),
        Some("3:12: The suffix makes the literal `0.1f32` an `f32`, never `f64`."),
        "{out}"
    );
    assert!(fixed(&src).is_empty(), "{out}");
    // 2^24 + 1 is an `f64` but no `f32`.
    let src = call_with("f32", "16777217.0f64");
    let out = rejected(&src);
    assert_eq!(
        out.lines().next(),
        Some("3:12: The suffix makes the literal `16777217.0f64` an `f64`, never `f32`."),
        "{out}"
    );
    assert!(fixed(&src).is_empty(), "{out}");
    // 2^24 is both.
    assert_eq!(
        fixed(&call_with("f32", "16777216.0f64")),
        ["y = f(x: 16777216.0);"]
    );
    // A decimal is never an `int`, whatever its value (the row's `2.0f64` beside an `int`).
    let src = call_with("int", "2.0f32");
    let out = rejected(&src);
    assert_eq!(
        out.lines().next(),
        Some("3:12: The suffix makes the literal `2.0f32` an `f32`, never `int`."),
        "{out}"
    );
    assert!(fixed(&src).is_empty(), "{out}");
}

#[test]
fn an_f32_literal_beside_a_rat_is_offered_its_rat_forms() {
    let src = call_with("rat", "0.5f32");
    assert!(
        rejected(&src).starts_with(
            "3:12: The suffix makes the literal `0.5f32` an `f32`, never `rat`. Try \
             `y = f(x: 0.5)` instead.\n"
        ),
        "{}",
        rejected(&src)
    );
    assert_eq!(fixed(&src), ["y = f(x: 0.5);", "y = f(x: 0.5r);"]);
    // Beside `f64 | rat` the bare literal would take neither alone, so only `0.25r` checks.
    let src = call_with("f64 | rat", "0.25f32");
    assert!(
        rejected(&src).starts_with(
            "3:12: The suffix makes the literal `0.25f32` an `f32`, never `f64 | rat`."
        ),
        "{}",
        rejected(&src)
    );
    assert_eq!(fixed(&src), ["y = f(x: 0.25r);"]);
}

#[test]
fn a_literal_with_a_suffix_compared_with_a_value_of_another_format_names_its_own() {
    let src = program("same(x: f32) = x == 2.0f64;");
    let out = rejected(&src);
    assert!(
        out.starts_with(
            "1:21: The suffix makes the literal `2.0f64` an `f64`, never `f32`. Try \
             `same(x: f32) = x == 2.0` instead.\n"
        ),
        "{out}"
    );
    assert_eq!(
        fixed(&src),
        [
            "same(x: f32) = x == 2.0;",
            "same(x: f32) = f64(x) == 2.0f64;"
        ]
    );
    checks(&edited(&src, "x == 2.0f64", "x == 2.0"));
}

/// The literal `0.5000…0` with `n` zeros and the suffix `suffix`, and the literal
/// `0.1000…01` with `n` zeros, each passed to a parameter of the other format.
fn long_suffixed_literals(n: usize) -> String {
    let zeros = "0".repeat(n);
    format!(
        "f(x: f32) = x;\ng(x: f64) = x;\nmain(m: MainArgs) {{\n  y = f(x: 0.5{zeros}f64);\n  \
         z = g(x: 0.1{zeros}1f32);\n  m.stdout <- \"${{y}}${{z}}\";\n}}\n"
    )
}

#[test]
fn the_message_of_a_long_literal_with_a_suffix_scales() {
    // Each literal is read once at `rat` and cast to the format expected, which decides
    // whether its form without a suffix is offered: O(n log^2 n) in its digits (COMPLEXITY.md
    // K41).
    let srcs = scaling::inputs(1000, long_suffixed_literals);
    scaling::check(
        "the messages of two literals of n digits with a suffix",
        1000,
        |n| {
            let out = rejected(&srcs[&n]);
            assert_eq!(out.matches("an `f64`, never `f32`").count(), 1, "{out}");
            assert_eq!(out.matches("an `f32`, never `f64`").count(), 1, "{out}");
            assert_eq!(out.matches("the literal is then the f32 0.5").count(), 1);
        },
    );
}

/// Row REPAIR-literal-string-order: an ordering of a number with a text no number cast reads
/// offers the number as text, a literal as a string literal, `"2" < "a"`, and anything else
/// cast, `String(2 + 13) < "a"`; it offered the operation's cast and nothing for the literal.
/// Each case is the comparison as written and its repair, in both orders of the operands, at
/// each ordering, with the number grouped and not.
const ORDERED_AS_TEXT: [(&str, &str); 12] = [
    ("2 < \"a\"", "\"2\" < \"a\""),
    ("\"a\" < 2", "\"a\" < \"2\""),
    ("(2) <= \"a\"", "\"2\" <= \"a\""),
    ("\"a\" > ((2))", "\"a\" > \"2\""),
    ("-2 >= \"x8\"", "\"-2\" >= \"x8\""),
    ("\"a\" >= (-2)", "\"a\" >= \"-2\""),
    ("2.5 < \"a\"", "\"2.5\" < \"a\""),
    ("\"a\" > 2.5", "\"a\" > \"2.5\""),
    ("(2 + 13) < \"a\"", "String(2 + 13) < \"a\""),
    ("\"a\" < (2 + 13)", "\"a\" < String(2 + 13)"),
    ("2 + 13 <= \"a\"", "String(2 + 13) <= \"a\""),
    ("\"a\" >= 2 + 13", "\"a\" >= String(2 + 13)"),
];

#[test]
fn a_literal_ordered_with_a_text_is_offered_as_text_where_an_operation_is_cast() {
    for (compare, repair) in ORDERED_AS_TEXT {
        let src = program(&format!("f() {{ c = {compare}; return c; }}"));
        let out = rejected(&src);
        let headline = out.lines().next().expect("a headline");
        assert!(
            headline.ends_with(&format!(" Try `{repair}` instead.")),
            "{compare}\n{out}"
        );
        checks(&program(&format!("f() {{ c = {repair}; return c; }}")));
    }
}

/// Orderings of a number with a text a number cast reads, in both orders of the operands,
/// with the number a literal and an operation, grouped and not: none is offered as text
/// (row REPAIR-string-compare-offer), and each is offered the text's number, `8`, alone.
const ORDERED_WITH_A_NUMBER_TEXT: [&str; 8] = [
    "2 < \"8\"",
    "\"8\" < 2",
    "(2) <= \"8\"",
    "\"8\" >= (2)",
    "(2 + 13) > \"8\"",
    "\"8\" > (2 + 13)",
    "2 + 13 < \"8\"",
    "\"8\" <= 2 + 13",
];

#[test]
fn a_literal_ordered_with_a_text_written_as_a_number_is_offered_no_text() {
    for compare in ORDERED_WITH_A_NUMBER_TEXT {
        let src = program(&format!("f() {{ c = {compare}; return c; }}"));
        let out = rejected(&src);
        assert!(!out.contains("String("), "{compare}\n{out}");
        assert!(!out.contains("write `\"2\"`"), "{compare}\n{out}");
        let offers = menu(&src);
        assert_eq!(offers.first(), Some(&entry("8")), "{compare}\n{out}");
        assert!(offers.iter().all(|o| !o.contains('"')), "{compare}\n{out}");
    }
}

#[test]
fn a_literal_compared_by_equality_with_a_text_is_offered_as_text_in_both_orders() {
    // `==` and `!=` write the literal as text beside any text, a number's or not: equality of
    // two texts does not depend on their order, and `"8" == 2` always gives `false` as written.
    for (compare, repair) in [
        ("\"8\" == 2", "\"8\" == \"2\""),
        ("2 == \"8\"", "\"2\" == \"8\""),
        ("\"a\" != 2", "\"a\" != \"2\""),
    ] {
        let src = program(&format!("f() {{ c = {compare}; return c; }}"));
        let line = format!("f() {{ c = {repair}; return c; }}");
        assert!(fixed(&src).contains(&line), "{compare}\n{}", rejected(&src));
        checks(&program(&line));
    }
}

/// Row REPAIR-literal-text-spelling: a number literal written as text is the text `String`
/// gives for it at its own carrier, `int` for an integer literal and `f64` for a decimal one,
/// not its spelling, which `"8" == "0x08"` shows: false, where `"8" == String(0x08)` is true.
/// Each case is the literal as the program spells it and that text, as `zedc run` prints
/// `String` of it (`String(2.50f64)` for a decimal, which nothing else gives a carrier).
const SPELLED_AS_TEXT: [(&str, &str); 15] = [
    ("0x08", "\"8\""),
    ("0b101", "\"5\""),
    ("0o17", "\"15\""),
    ("1_000", "\"1000\""),
    ("-1_000", "\"-1000\""),
    ("007", "\"7\""),
    ("0_0", "\"0\""),
    ("-0", "\"0\""),
    ("-0x0", "\"0\""),
    ("2.50", "\"2.5\""),
    ("0.10", "\"0.1\""),
    ("1_000.5", "\"1000.5\""),
    ("1e3", "\"1000.0\""),
    ("1e22", "\"1.0e22\""),
    ("-0.0", "\"-0.0\""),
];

#[test]
fn each_text_of_a_literal_is_the_text_string_gives_at_run_time() {
    // A decimal is given `f64` by its suffix, the carrier it has where nothing fixes one.
    let shown: Vec<String> = SPELLED_AS_TEXT
        .iter()
        .map(|(lit, _)| {
            let decimal = !lit.contains('x') && (lit.contains('.') || lit.contains('e'));
            let suffix = if decimal { "f64" } else { "" };
            format!("${{String({lit}{suffix})}}")
        })
        .collect();
    let src = format!(
        "main(m: MainArgs) {{\n  m.stdout <- \"{}\\n\";\n}}\n",
        shown.join(" ")
    );
    let out = run("literal_texts", &src, &[]);
    assert_eq!((out.status, out.stderr.as_str()), (0, ""), "{src}");
    let texts: Vec<String> = SPELLED_AS_TEXT
        .iter()
        .map(|(_, t)| t.trim_matches('"').to_string())
        .collect();
    assert_eq!(out.stdout.trim_end(), texts.join(" "), "{src}");
}

#[test]
fn a_literal_compared_by_equality_with_a_text_is_offered_the_text_string_gives() {
    for (lit, text) in SPELLED_AS_TEXT {
        let src = program(&format!("f() {{ c = \"x8\" == {lit}; return c; }}"));
        let line = format!("f() {{ c = \"x8\" == {text}; return c; }}");
        assert_eq!(fixed(&src), [line.as_str()], "{lit}\n{}", rejected(&src));
        checks(&program(&line));
    }
}

#[test]
fn a_literal_ordered_with_a_text_is_offered_the_text_string_gives() {
    for (lit, text) in SPELLED_AS_TEXT {
        let src = program(&format!("f() {{ c = {lit} < \"x8\"; return c; }}"));
        let out = rejected(&src);
        let headline = out.lines().next().expect("a headline");
        assert!(
            headline.ends_with(&format!(" Try `{text} < \"x8\"` instead.")),
            "{lit}\n{out}"
        );
        assert!(out.contains(&entry(text)), "{lit}\n{out}");
        checks(&program(&format!(
            "f() {{ c = {text} < \"x8\"; return c; }}"
        )));
    }
}

#[test]
fn a_literal_in_another_base_compared_with_its_text_is_offered_the_equal_text() {
    // The case the row names: `"8" == 0x08` is offered `"8" == "8"`, which is true, as
    // `"8" == String(0x08)` is; and a literal compared with a component of a tuple whose
    // component there is a `String` is written the same way.
    let src = program("f() { c = \"8\" == 0x08; return c; }");
    let line = "f() { c = \"8\" == \"8\"; return c; }";
    assert_eq!(fixed(&src), [line], "{}", rejected(&src));
    checks(&program(line));
    let src = program("f(p: (String, int)) = p == (0x0A, 2);");
    let line = "f(p: (String, int)) = p == (\"10\", 2);";
    assert_eq!(fixed(&src), [line], "{}", rejected(&src));
    checks(&program(line));
}

#[test]
fn a_text_ordered_with_a_literal_of_its_value_is_offered_the_number_the_text_reads() {
    // Row REPAIR-text-cast-spelling. `"8" < 0x08` orders a text with a number; the repair
    // writes the number the text reads in place of the text, in decimal, as the text writes
    // it: `8 < 0x08`, not `0x08 < 0x08`, the other operand's spelling of the same value. Each
    // case is the text, the literal beside it, and the number written for the text; both
    // orders of the operands are tried.
    for (text, lit, number) in [
        ("8", "0x08", "8"),
        ("5", "0b101", "5"),
        ("15", "0o17", "15"),
        ("1000", "1_000", "1000"),
        ("1000", "0x3_E8", "1000"),
        ("-8", "-0x08", "-8"),
        ("0", "0x0", "0"),
        // `rat` comes before `f64` in the menu, so the first repair is the `rat` literal.
        ("0.5", "5e-1", "0.5r"),
    ] {
        for (expr, want) in [
            (format!("\"{text}\" < {lit}"), format!("{number} < {lit}")),
            (format!("{lit} >= \"{text}\""), format!("{lit} >= {number}")),
        ] {
            let out = rejected(&program(&format!("f() {{ c = {expr}; return c; }}")));
            let headline = out.lines().next().expect("a headline");
            assert!(
                headline.ends_with(&format!(" Try `{want}` instead.")),
                "{expr}\n{out}"
            );
            assert!(out.contains(&entry(number)), "{expr}\n{out}");
            assert!(!out.contains(&entry(lit)), "{expr}\n{out}");
            checks(&program(&format!("f() {{ c = {want}; return c; }}")));
        }
    }
}

#[test]
fn a_literal_of_many_digits_ordered_with_a_text_is_offered_as_text_and_scales() {
    // The literal is written as text, O(d) for d digits, and the ordering checked once with it.
    let srcs = scaling::inputs(4000, |d| {
        program(&format!(
            "f() {{ c = \"a\" < {}; return c; }}",
            "7".repeat(d)
        ))
    });
    scaling::check(
        "the text repair of a literal of d digits ordered with a text",
        4000,
        |d| {
            let out = rejected(&srcs[&d]);
            let want = format!("Try `\"a\" < \"{}\"` instead.", "7".repeat(d));
            assert!(out.contains(&want), "{out}");
        },
    );
}
