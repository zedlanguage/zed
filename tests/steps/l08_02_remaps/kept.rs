//! Which written bodies of a block's functions are kept (row PROOF-block-body-kept-when-named).
//! A function declared in a block whose calls run a fold at two types takes a body made at
//! the identities of each call (sec:reduction, "Identity as data"); its written body is kept
//! only if a term that runs names it, and else dropped (`Elab::place_locals`). Each way
//! DESIGN.md lets a program refer to a function is written here once:
//!
//! - those that name the written body, which is then kept and its fold, which no call
//!   decides, refused: a value bound to a name, an alias of that name, an argument, a tuple's
//!   member, an `if`'s branch, a map's or array's entry, a block's result, a lambda that
//!   captures it, a function whose body is it, a function whose body names it and that is
//!   itself named, a parameter's default, a port push in `main`, and a value never used;
//! - those that run a body made at each call's identity and leave the written body
//!   dropped, which give their values: a call, UFCS, indexing, a call of the name in
//!   parentheses, currying with `...`, a bracket section, `~f~` infix, a default that calls
//!   it, a lambda a built-in runs in place, a call from a generic function's block;
//! - those refused before the written body could be dropped: `::source`, `><` by a
//!   function, a law, a test table in a block, a string or `==` of a function.
//!
//! A dropped written body that a kept term names is refused by `Elab::check_dropped`, whose
//! words, "used as a value", none of these programs gets: a reference `written_named`
//! missed fails the first group's tests. zedc-elab's unit tests run the check with the
//! references switched off.

use crate::source::{all_errors, does_not_parse, prints, rejected};
use zed_tests::step_helpers::l01_16_elaboration::elab;

/// `top`, a fold by `max` whose identity its calls decide.
const TOP: &str = "top(positional xs) = xs >< max;\n";
/// `m["a"]` an empty `f64` level, `m["b"]` holds 5.0.
const F: &str = "m = { \"a\" -> [1.0], \"b\" -> [5.0] }.map(r -> r.where(v -> v > 3.0));\n";
/// `mi["a"]` an empty `int` level, `mi["b"]` holds 5.
const I: &str = "mi = { \"a\" -> [1], \"b\" -> [5] }.map(r -> r.where(v -> v > 3));\n";
/// A function a block declares, called at `int` and `f64` in each test.
const H: &str = "h(positional q) = top(q);";

fn at(body: &str) -> String {
    format!("{TOP}{F}{I}{body}")
}

/// `body` is refused at the fold of `top` that the written body of `h` runs at no decided
/// identity: the written body is kept. Not by `check_dropped`, which would mean it was dropped.
fn written_body_kept(body: &str) {
    let src = at(body);
    rejected(
        &src,
        &[
            "a fold `><` that the calls of one function run on entries of type",
            "`#empty` at `int`",
            "`-inf` at `f64`",
            "does not compile it yet",
        ],
    );
    let es = all_errors(&src).join("\n");
    assert!(!es.contains("used as a value"), "{src}\n{es}");
}

#[test]
fn a_block_function_named_as_a_value_keeps_its_written_body() {
    for body in [
        // Bound to a name, and that name's alias.
        format!("a = {{ {H} p = h; (h(mi[\"a\"]), p(m[\"a\"])) }};\n"),
        format!("a = {{ {H} p = h; q = p; (h(mi[\"a\"]), q(m[\"a\"])) }};\n"),
        // Bound to a name never used: the term is kept all the same.
        format!("a = {{ {H} p = h; (h(mi[\"a\"]), h(m[\"a\"])) }};\n"),
        // Passed as an argument.
        format!(
            "ap(positional f, positional x) = f(x);\n\
             a = {{ {H} (h(mi[\"a\"]), ap(h, m[\"a\"])) }};\n"
        ),
        // A tuple's member, an `if`'s branches, a map's and an array's entry.
        format!("a = {{ {H} (h(mi[\"a\"]), (h, 1)[0](m[\"a\"])) }};\n"),
        format!("a = {{ {H} p = if true {{ h }} else {{ h }}; (h(mi[\"a\"]), p(m[\"a\"])) }};\n"),
        format!("a = {{ {H} p = {{ \"f\" -> h }}; (h(mi[\"a\"]), h(m[\"a\"]), p) }};\n"),
        format!("a = {{ {H} p = [h][0]; (h(mi[\"a\"]), h(m[\"a\"]), p) }};\n"),
        // A block's result, and a value an inner block names.
        format!("a = {{ {H} x = (h(mi[\"a\"]), h(m[\"a\"])); h }};\nb = a(m[\"a\"]);\n"),
        format!("a = {{ {H} x = {{ p = h; p(m[\"a\"]) }}; (h(mi[\"a\"]), x) }};\n"),
        // Captured by a lambda, called at one type and at two; returned by one.
        format!("a = {{ {H} p = x -> h(x); (h(mi[\"a\"]), p(m[\"a\"])) }};\n"),
        format!("a = {{ {H} p = x -> h(x); (p(mi[\"a\"]), p(m[\"a\"])) }};\n"),
        format!("a = {{ {H} p = () -> h; (h(mi[\"a\"]), p()(m[\"a\"])) }};\n"),
        // The body of a function declared after it, and named in one's body: run if that one
        // is, whether called by name or itself named as a value.
        format!("a = {{ {H} k() = h; (h(mi[\"a\"]), k()(m[\"a\"])) }};\n"),
        format!(
            "a = {{ {H} k(positional z) = {{ p = h; p(z) }}; (h(mi[\"a\"]), k(m[\"a\"])) }};\n"
        ),
        format!(
            "a = {{ {H} k(positional z) = {{ p = h; (p(z), h(mi[\"a\"])) }}; \
             (k(m[\"a\"]), k(mi[\"b\"])) }};\n"
        ),
        format!("a = {{ {H} k(positional z) = h(z); p = k; (h(mi[\"a\"]), h(m[\"a\"]), p) }};\n"),
        format!("a = {{ {H} k(positional z) = h(z); p = k; (h(mi[\"a\"]), h(m[\"a\"])) }};\n"),
        // A parameter's default.
        format!(
            "a = {{ {H} k(positional z, f = h) = (z, f); (h(mi[\"a\"]), h(m[\"a\"]), k(1)) }};\n"
        ),
        // In a generic function's block and in a lambda a built-in runs in place.
        format!(
            "g(positional ys) = {{ {H} p = h; (h(ys), p(m[\"a\"])) }};\n\
             a = (g(mi[\"a\"]), g(m[\"a\"]));\n"
        ),
        format!("a = mi.map(r -> {{ {H} p = h; (h(r), p(m[\"a\"])) }});\n"),
        // Pushed to a port in `main`.
        format!(
            "main(io: MainArgs) {{ {H} p = h; \
             io.stdout <- (String(h(mi[\"a\"])) ++ String(p(m[\"a\"]))) else \"\"; }}\n\
             a = 1;\n"
        ),
    ] {
        written_body_kept(&body);
    }
}

#[test]
fn a_block_function_called_in_each_form_runs_the_body_of_each_call() {
    // UFCS, indexing and a call of the name in parentheses are calls.
    for call in ["m[\"a\"].h", "h[m[\"a\"]]", "(h)(m[\"a\"])"] {
        prints(
            &at(&format!("a = {{ {H} (h(mi[\"a\"]), {call}) }};\n")),
            "a",
            "(#empty, -inf)",
        );
    }
    let g = "g(positional z, w = 0) = (top(z), w);";
    let g2 = "g2(positional z, positional w) = (top(z), w);";
    // Currying with `...` and a bracket section fix the argument, whose type decides the
    // identity; `~g2~` infix is the call `g2(m["a"], 2)`.
    prints(
        &at(&format!(
            "a = {{ {g} p = g(m[\"a\"], ...); (g(mi[\"a\"]), p()) }};\n"
        )),
        "a",
        "((#empty, 0), (-inf, 0))",
    );
    prints(
        &at(&format!(
            "a = {{ {g2} p = g2[m[\"a\"]]; (g2(mi[\"a\"], 1), p(2)) }};\n"
        )),
        "a",
        "((#empty, 1), (-inf, 2))",
    );
    prints(
        &at(&format!(
            "a = {{ {g2} (g2(mi[\"a\"], 1), m[\"a\"] ~g2~ 2) }};\n"
        )),
        "a",
        "((#empty, 1), (-inf, 2))",
    );
    // A default that calls `h`, taken and overridden.
    let k = "k(positional z, y = h(m[\"b\"])) = (z, y);";
    prints(
        &at(&format!("a = {{ {H} {k} (h(mi[\"a\"]), k(1)) }};\n")),
        "a",
        "(#empty, (1, 5.0))",
    );
    prints(
        &at(&format!(
            "a = {{ {H} {k} (h(mi[\"a\"]), k(1, y: 2.0)) }};\n"
        )),
        "a",
        "(#empty, (1, 2.0))",
    );
    // A lambda `.map` runs in place, and a generic function's block.
    prints(
        &at(&format!(
            "a = {{ {H} (h(m[\"a\"]), mi.map(r -> h(r))) }};\n"
        )),
        "a",
        "(-inf, {\"a\" -> #empty, \"b\" -> 5})",
    );
    prints(
        &at(&format!(
            "g(positional ys) = {{ {H} (h(ys), h(m[\"a\"])) }};\n\
             a = (g(mi[\"a\"]), g(m[\"a\"]));\n"
        )),
        "a",
        "((#empty, -inf), (-inf, -inf))",
    );
    // Called by name in `main`, whose port push runs it.
    let src = at(&format!(
        "main(io: MainArgs) {{ {H} \
         io.stdout <- (String(h(mi[\"a\"])) ++ String(h(m[\"a\"]))) else \"\"; }}\n\
         a = 1;\n"
    ));
    assert!(elab(&src).is_ok(), "{src}: {:?}", all_errors(&src));
}

#[test]
fn a_block_function_named_in_a_form_refused_before_elaboration_drops_nothing() {
    // `::source` and `><` by a function are refused by name resolution, a law in a block when
    // the block is read, a test table in a block does not parse, and a string of a function and
    // `==` of two are refused by the checker: no written body is dropped while named.
    let mut wrong = String::new();
    for (body, why) in [
        (
            format!("a = {{ {H} s = h::source; (h(mi[\"a\"]), h(m[\"a\"])) }};\n"),
            "a metadata read `::` is part of the Zed language",
        ),
        (
            format!("a = {{ {H} (h(mi[\"a\"]), h(m[\"a\"]), mi[\"b\"] >< h) }};\n"),
            "a fold `><` by a function other than `max`, `min` or an operator section",
        ),
        (
            format!("a = {{ {H} s = \"${{h}}\"; (h(mi[\"a\"]), h(m[\"a\"])) }};\n"),
            "interpolation takes data, and this value may hold a function",
        ),
        (
            format!("a = {{ {H} s = h == h; (h(mi[\"a\"]), h(m[\"a\"])) }};\n"),
            "`==` takes data, and this value may hold a function",
        ),
    ] {
        let src = at(&body);
        let es = all_errors(&src).join("\n");
        if !es.contains(why) || es.contains("used as a value") {
            wrong.push_str(&format!("{body}want {why:?}, got:\n{es}\n\n"));
        }
    }
    assert!(wrong.is_empty(), "{wrong}");
    let src = at(&format!(
        "a = {{ {H} law l(x) = h(x) == h(x); (h(mi[\"a\"]), h(m[\"a\"])) }};\n"
    ));
    let tokens = zedc::lex::lex_fence(&src).unwrap();
    let tree = zedc::parse::parse(&src, &tokens, "Unit", zedc::parse::TOP).unwrap();
    let e = zedc::ast::unit(&src, &tokens, &tree).expect_err(&src);
    assert!(
        e.message
            .starts_with("the law `law l(x) = h(x) == h(x);` is part of the Zed language"),
        "{}",
        e.message
    );
    does_not_parse(&at(&format!(
        "a = {{ {H} test h {{ mi[\"a\"] -> #empty; }} (h(mi[\"a\"]), h(m[\"a\"])) }};\n"
    )));
}
