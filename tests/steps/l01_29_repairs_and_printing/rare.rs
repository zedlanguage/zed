//! Messages no other test produced (test audit 2026-11-08, row 10; item
//! TESTS-messages-never-produced): for each, the shortest program that produces it, with the
//! whole message pinned.

use super::rejected;

#[test]
fn a_default_of_no_type_yet_is_said_to_have_none() {
    // Plan row MSG-default-unknown-type: `g`, a parameter of no written type, has no type yet
    // where `k`'s default reads it. The headline said "the default of `h` is _", and a repair
    // offered `h: _`; `_` reads as the type of every value. The headline now says the default
    // has no type yet, as the note on `g` does, and offers no type to widen `h` by.
    let program = |ret: &str| {
        format!(
            "f(positional g) {{\n  k(h: (int) -> int = g) = h(2);\n  return {ret};\n}}\n\
             main(m: MainArgs) {{\n  m.stdout <- \"${{f(x -> x + 1)}}\";\n}}\n"
        )
    };
    for ret in ["k()", "0"] {
        assert_eq!(
            shown(&program(ret)),
            r#"2:23: the default of `h` has no type yet here, and a default is a value of its parameter's type, int -> int.
  [1] 2:23: `g` has no type yet here
      2 |   k(h: (int) -> int = g) = h(2);
        |                       ^
  [2] 1:3: `g` has no declared type; its uses give it no type yet
      1 | f(positional g) {
        |   ^^^^^^^^^^^^
  [3] 2:23: repair: write a default of type int -> int"#
        );
    }
    // A default whose type is known is shown by it, as before.
    let known = shown(
        "k(h: (int) -> int = g) = h(2);\ng(positional x) = \"s\";\n\
         main(m: MainArgs) {\n  m.stdout <- \"${k()}\";\n}\n",
    );
    assert!(
        known.starts_with("1:21: `g` is `_ -> \"s\"`, not `int -> int`"),
        "{known}"
    );
}

/// MSG-list-value-printed-by-arrows: a list value whose keys the type knows, as `[1, 2]` and
/// `[x.trim]`, is printed by its arrow, `(0 | 1) -> 1 | 2` and `0 -> String`, and not as
/// `[1 | 2]` or `[String]`. DESIGN.md sec:diagnostics asks a printed type to be exact and to
/// parse back; `[V]` is `int ->? V` over the ranks `0 ..< n` with `n` not known
/// (sec:type_language), a larger type than the value's, so it would say `size` is refused a type it takes at other
/// lengths. `Sig::list` (zedc-types) holds only where the length is not known, and there `[V]`
/// is printed (the third program, `xs: [int]`). The shape form `[V; n]` (sec:type_language,
/// step L14.1) is not yet read, so it cannot be printed; plan row MSG-list-value-printed-shape.
#[test]
fn a_list_value_of_known_keys_is_printed_by_its_arrow() {
    let size = "size(ps: [String]) = ps.count;\n";
    let known = shown(&format!(
        "{size}main(m: MainArgs) {{\n  m.stdout <- \"${{size(ps: [1, 2])}}\";\n}}\n"
    ));
    assert!(
        known.starts_with(
            "3:18: `size` does not take ((0 | 1) -> 1 | 2): no arrow of `size` takes these types.\n  [1] 3:27: this expression is (0 | 1) -> 1 | 2\n"
        ),
        "{known}"
    );
    assert!(
        known.contains("`size` takes (ps: [String]) -> int"),
        "{known}"
    );
    let lambda =
        shown("main(m: MainArgs) {\n  m.stdout <- \"${[1, 2].flatMap(x -> [x.trim])}\";\n}\n");
    assert!(
        lambda.starts_with(
            "2:18: the function given to `flatMap` does not take (1 | 2): no arrow of the function given to `flatMap` takes these types.\n  [1] 2:18: the function given to `flatMap` takes String -> 0 -> String\n"
        ),
        "{lambda}"
    );
    let unknown = shown(&format!(
        "{size}f(xs: [int]) = size(ps: xs);\nmain(m: MainArgs) {{\n  m.stdout <- \"${{f(xs: [1])}}\";\n}}\n"
    ));
    assert!(
        unknown.starts_with(
            "2:16: `size` does not take ([int]): no arrow of `size` takes these types.\n  [1] 2:25: `xs` is [int] here\n"
        ),
        "{unknown}"
    );
}

/// The rejection of `src`, without the line end after its last line.
fn shown(src: &str) -> String {
    rejected(src).trim_end().to_string()
}

#[test]
fn a_default_whose_type_its_uses_exclude_is_rejected() {
    // A parameter with no declared type takes the type its uses give it; its default must be
    // of that type.
    assert_eq!(
        shown("f(positional y = (y + 1, 2)) = y;\n"),
        r#"1:18: the default of `y` is (_, 2), not int | f32 | f64 | rat: a default is a value of its parameter's type.
  [1] 1:18: this expression gives (_, 2)
      1 | f(positional y = (y + 1, 2)) = y;
        |   ^^^^^^^^^^^^^^^^^^^^^^^^^ [4]
        |                   ^ [3]  ^ [6]
        |                   ^^^^^ [2]
        |                       ^ [5, 7]
        |                  ^--------^ [1, 8, 9]
  [2] 1:19: this `+` gives int | f32 | f64 | rat
  [3] 1:19: `y` is int | f32 | f64 | rat here
  [4] 1:3: `y` has no declared type; its uses give it int | f32 | f64 | rat
  [5] 1:23: this literal, 1, is 1
  [6] 1:26: this literal, 2, is 2
  [7] 1:23: the literal 1 takes int | f32 | f64 | rat
  [8] 1:18: repair: write a default of type int | f32 | f64 | rat
  [9] 1:18: repair: declare `y` with a type that holds (_, 2) as well, as `y: int | f32 | f64 | rat | (_, 2)`"#
    );
}

#[test]
fn a_default_the_checker_cannot_place_in_a_range_is_rejected_at_the_call() {
    assert_eq!(
        shown("f(positional a, positional b = a) = bitAnd(b, 1);\nmain = f(1);\n"),
        r#"2:8: `f` takes `b` in int[0..]: `f(1)` leaves out `b`.
  [1] 1:37: `bitAnd` takes `a` in int[0..] here
      1 | f(positional a, positional b = a) = bitAnd(b, 1);
        | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [3]
        |                                     ^^^^^^^^^^^^ [1]
  [2] 2:8: `b` takes its default, which the checker cannot show lies in int[0..]
      2 | main = f(1);
        |        ^^^^
  [3] 1:1: `f` is declared here with no type written for `a`, `b` or its result; the type the checker found for `f` is `(int, int) -> int`
  [4] 2:8: repair: pass `b` in this call, with a value in int[0..]
  [5] 2:8: repair: give `b` a default in int[0..]"#
    );
}

#[test]
fn an_argument_forwarded_to_a_function_parameter_is_checked_against_its_range() {
    // The repair names the argument `-1` of the call at 3:8, not `a`, which belongs to `h`
    // (MSG-forwarded-repair); step [1] shows where `-1` is passed.
    assert_eq!(
        shown(
            "ap(positional g, positional v) = g(v);\nh(positional a) = bitAnd(a, 1);\n\
             main = ap(h, -1);\n"
        ),
        r#"3:8: `g` takes `a` in int[0..]: `ap(h, -1 : int)`.
  [1] 3:14: `-1` reaches `g` as `a`
      3 | main = ap(h, -1);
        |        ^^^^^^^^^ [3, 6]
        |              ^^ [1]
  [2] 2:19: `bitAnd` takes `a` in int[0..] here
      2 | h(positional a) = bitAnd(a, 1);
        |                   ^^^^^^^^^^^^
  [3] 3:8: a value outside int[0..] would reach a use that does not take it
  [4] 1:34: `ap` needs this of its argument here
      1 | ap(positional g, positional v) = g(v);
        | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [5]
        |                                  ^^^^ [4]
  [5] 1:1: `ap` is declared here with no type written for `g`, `v` or its result; the type the checker found for `ap` is `(_, _) -> _`
  [6] 3:8: repair: pass a value in int[0..] where this call passes `-1`"#
    );
}

#[test]
fn sum_of_a_value_that_is_not_a_tuple_is_rejected() {
    assert_eq!(
        shown("x = sum(3);\n"),
        r#"1:5: `sum` does not take (3): it adds only numbers.
  [1] 1:5: repair: pass a tuple whose components are all numbers, as `sum((1, 2, 3))`
      1 | x = sum(3);
        |     ^^^^^^"#
    );
}

#[test]
fn a_component_of_a_destructured_tuple_is_named_with_its_place() {
    // Before, step [2] read "`a` is component 0 of this, 1", which did not say what "this"
    // is or which of the two is the type.
    // No repair is offered: `int(b)` always fails, at `#invalid`, so `c = a + int(b)` is
    // rejected.
    assert_eq!(
        shown("p = (1, \"x\");\na, b = p;\nc = a + b;\n"),
        r#"3:5: `+` does not take (1, "x"): no arrow of `+` takes these types.
  [1]  3:5: `a` is 1 here
       3 | c = a + b;
         |     ^ [1]
         |     ^^^^^ [10, 11, 12, 13]
         |         ^ [8]
  [2]  2:8: `a` is 1, component 0 of this tuple
       2 | a, b = p;
         |        ^
  [3]  2:8: `p` is (1, "x") here
  [4]  1:5: `p` is defined as this expression, (1, "x")
       1 | p = (1, "x");
         |     ^^^^^^^^ [4, 5]
         |      ^ [6]
         |         ^^^ [7]
  [5]  1:5: this expression gives (1, "x")
  [6]  1:6: this literal, 1, is 1
  [7]  1:9: this expression is "x"
  [8]  3:9: `b` is "x" here
  [9]  2:8: `b` is "x", component 1 of this tuple
  [10] 3:5: `+` takes (int, int) -> int
  [11] 3:5: `+` takes (f64, f64) -> f64
  [12] 3:5: `+` takes (rat, rat) -> rat
  [13] 3:5: `+` takes (f32, f32) -> f32"#
    );
}

#[test]
fn a_parameter_typed_by_its_default_says_so() {
    // Before, step [2] read "`n` is String, the carrier of its default".
    assert_eq!(
        shown("f(positional n = \"a\") = n + 1;\n"),
        r#"1:25: `+` does not take (String, 1): no arrow of `+` takes these types.
  [1] 1:25: `n` is String here
      1 | f(positional n = "a") = n + 1;
        |   ^^^^^^^^^^^^^^^^^^ [2]    ^ [3]
        |                         ^ [1]
        |                         ^^^^^ [4, 5, 6, 7]
  [2] 1:3: `n` is String, the type of its default
  [3] 1:29: this literal, 1, is 1
  [4] 1:25: `+` takes (int, int) -> int
  [5] 1:25: `+` takes (f64, f64) -> f64
  [6] 1:25: `+` takes (rat, rat) -> rat
  [7] 1:25: `+` takes (f32, f32) -> f32"#
    );
}

/// `f` calls `g` and adds 1, so `g` gives a number; `k` takes `h` with the default `g`, which
/// makes `h` and `g` one value (DESIGN L1.29, item MSG-flow-origin).
const FLOW: &str = "f(positional g) {\n  a = g(1) + 1;\n  k(positional h = g) = h(2);\n  \
                    b = k(x -> \"s\");\n  return a;\n}\n";

/// A `main` that calls `f`, so that a program built on [`FLOW`] runs.
const MAIN: &str = "main(m: MainArgs) { m.stdout <- \"${f(x -> x + 1)}\"; }\n";

/// The message for [`FLOW`], after its first `file:` or none.
const FLOW_SHOWN: &str = r#"2:7: `g(1)` gives "s" on the value `x -> "s"`, but other uses need int | f32 | f64 | rat.
  [1] 2:7: this call of `g` gives int | f32 | f64 | rat
      2 |   a = g(1) + 1;
        |       ^^^^ [1, 3, 7, 8]
        |         ^ [2]
  [2] 2:9: this literal, 1, is 1
  [3] 2:7: this use needs it here
  [4] 4:9: `x -> "s"` comes from here and reaches `g(1)`
      4 |   b = k(x -> "s");
        |         ^^^^^^^^
  [5] 3:20: the default `h = g` gives `h` the type of `g`
      3 |   k(positional h = g) = h(2);
        |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^ [6]
        |                    ^ [5]
  [6] 3:3: `k` is declared here with no type written for `h` or its result; the type the checker found for `k` is `_ -> _`
  [7] 2:7: repair: write `h` with no default, as `k(positional h) = h(2);`, and pass `g` as `h` in each call that leaves `h` out
  [8] 2:7: repair: declare the types of the values this use reads, so that it is checked where it is written"#;

#[test]
fn a_value_that_flows_into_a_class_another_use_fixed_shows_its_origin() {
    // The rejection is right: a default is checked at its parameter's type, so `h = g` makes
    // `h` and `g` one value, and `k`, declared in `f`, reads `g` as it is; `x -> "s"` passed
    // as `h` is passed as `g` (DESIGN L1.29, MSG-flow-origin). Before, the message named
    // neither the lambda at 4:9 nor the default at 3:20, and its headline read "this use gives
    // "s", not int | f32 | f64 | rat: its result flows into a value that other uses have
    // already made int | f32 | f64 | rat".
    assert_eq!(shown(FLOW), FLOW_SHOWN);
}

#[test]
fn zedc_run_prints_the_origin_of_a_value_that_flows_into_a_class() {
    let file = super::refused_warning::unit("flow_origin", "flow.zed", FLOW);
    let (status, err) = super::refused_warning::run(&file, &[]);
    assert_eq!(status, 1);
    assert_eq!(err.trim_end(), format!("{file}:{FLOW_SHOWN}"));
}

#[test]
fn the_repairs_of_a_value_that_flows_through_a_default_are_accepted() {
    // The repair at [7] above, as written: `k` with no default; the call passes "s" to `h` alone.
    let repaired = FLOW.replace("h = g", "h");
    if let Err(e) = zedc::run::load(format!("{repaired}{MAIN}").as_bytes()) {
        panic!("{repaired}\n{e}");
    }
    // Passing `g` where the default was read, and the lambda in another call: each is its own
    // argument, and neither reaches `g`.
    let passed = FLOW
        .replace("h = g", "h")
        .replace("b = k(x -> \"s\");", "b = k(g);\n  c = k(x -> \"s\");");
    if let Err(e) = zedc::run::load(format!("{passed}{MAIN}").as_bytes()) {
        panic!("{passed}\n{e}");
    }
}

#[test]
fn a_chain_of_defaults_is_shown_link_by_link() {
    // The repair names `h1`, the parameter whose default reads `g`: `h2` and `h3` are `k`'s
    // own and are no value a caller passes.
    let src = FLOW.replace(
        "k(positional h = g) = h(2);\n  b = k(x -> \"s\");",
        "k(h1 = g, h2 = h1, h3 = h2) = h3(2);\n  b = k(h3: x -> \"s\");",
    );
    assert_eq!(
        shown(&src),
        r#"2:7: `g(1)` gives "s" on the value `x -> "s"`, but other uses need int | f32 | f64 | rat.
  [1]  2:7: this call of `g` gives int | f32 | f64 | rat
       2 |   a = g(1) + 1;
         |       ^^^^ [1, 3, 9, 10]
         |         ^ [2]
  [2]  2:9: this literal, 1, is 1
  [3]  2:7: this use needs it here
  [4]  4:13: `x -> "s"` comes from here and reaches `g(1)`
       4 |   b = k(h3: x -> "s");
         |             ^^^^^^^^
  [5]  3:27: the default `h3 = h2` gives `h3` the type of `h2`
       3 |   k(h1 = g, h2 = h1, h3 = h2) = h3(2);
         |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [8]
         |          ^ [7]   ^^ [6]   ^^ [5]
  [6]  3:18: the default `h2 = h1` gives `h2` the type of `h1`
  [7]  3:10: the default `h1 = g` gives `h1` the type of `g`
  [8]  3:3: `k` is declared here with no type written for `h1`, `h2`, `h3` or its result; the type the checker found for `k` is `(h1: _, h2: _, h3: _) -> _`
  [9]  2:7: repair: write `h1` with no default, as `k(h1, h2 = h1, h3 = h2) = h3(2);`, and pass `g` as `h1` in each call that leaves `h1` out
  [10] 2:7: repair: declare the types of the values this use reads, so that it is checked where it is written"#
    );
    let repaired = src.replace("h1 = g", "h1").replace("k(h3:", "k(h1: g, h3:");
    if let Err(e) = zedc::run::load(format!("{repaired}{MAIN}").as_bytes()) {
        panic!("{repaired}\n{e}");
    }
}

#[test]
fn a_value_with_one_origin_names_no_default() {
    // Two calls of `k`: `x -> 1` makes `h`, and so `g`, give int; then `x -> "s"` is rejected
    // twice. At `g(1)` the value reaches `g` through the default; at `h(2)` it reaches `h`
    // directly, as an argument, so the derivation names only where it comes from. The first
    // error gives the type found for `k`, and the second points to it
    // (MSG-call-signature-per-message).
    let src = FLOW.replace("b = k(x -> \"s\");", "b = k(x -> 1);\n  c = k(x -> \"s\");");
    let out = shown(&src);
    let second = out
        .find("\n3:25: ")
        .map(|i| &out[i + 1..])
        .unwrap_or_else(|| panic!("{out}"));
    assert_eq!(
        second,
        r#"3:25: `h(2)` gives "s" on the value `x -> "s"`, but other uses need int.
  [1] 3:25 to 3:28: this call of `h` gives int
      line 3 is shown above
  [2] 3:27 to 3:27: this literal, 2, is 2
  [3] 3:25 to 3:28: this use needs it here
  [4] 5:9 to 5:16: `x -> "s"` comes from here and reaches `h(2)`
      line 5 is shown above
  [5] 3:3 to 3:29: `k` is declared here; the error above gives the type the checker found for `k`
  [6] 3:25 to 3:28: repair: declare the types of the values this use reads, so that it is checked where it is written"#
    );
    assert!(
        out.starts_with(
            "2:7: `g(1)` gives \"s\" on the value `x -> \"s\"`, but other uses need int.\n"
        ),
        "{out}"
    );
    assert!(
        out.contains("[5] 3:20: the default `h = g` gives `h` the type of `g`\n"),
        "{out}"
    );
}

#[test]
fn a_value_no_use_has_typed_is_said_to_have_no_type_yet() {
    // A parameter of no written type that its uses leave every value, as `x` pushed alone, has
    // no type yet: its notes say so and do not print `_`, which would read as the type of every
    // value (row MSG-untyped-note-placeholder). Its name, its origin, a call of it and another
    // expression of that type each have one such note.
    assert_eq!(
        shown(
            "h(x, out: Lines) { out <- x; }\n\
             g(y, out: Lines) { h(x: y, out: out); }\n\
             main(m: MainArgs) {\n  g(y: 5, out: m.stdout);\n}\n"
        ),
        r#"1:27: A `Lines` port takes a `String` or a family of strings: `out <- x : 5`. Try `out <- "${x}";` instead.
  [1] 1:27: `x` has no type yet here
      1 | h(x, out: Lines) { out <- x; }
        |   ^ [2]                   ^ [1, 3, 4, 5, 7]
  [2] 1:3: `x` has no declared type; its uses give it no type yet
  [3] 1:27: the port `out` writes each value pushed to it as one line of text
  [4] 1:27: `g` needs this of its argument here
  [5] 1:27: `h` needs this of its argument here
  [6] 2:1: `g` is declared here with no type written for `y` or its result; the type the checker found for `g` is `(y: _, out: Lines) -> ()`
      2 | g(y, out: Lines) { h(x: y, out: out); }
        | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  [7] 1:27: repair: write the value into a string, as `out <- "${x}";`"#
    );
    let call = shown(
        "h(f, out: Lines) { out <- f(1); }\n\
         main(m: MainArgs) {\n  h(f: (k) -> k, out: m.stdout);\n}\n",
    );
    assert!(
        call.contains("\n  [1] 1:27: this call of `f` has no type yet\n"),
        "{call}"
    );
    let other = shown(
        "h(x, c, out: Lines) { out <- if c { x } else { \"z\" }; }\n\
         main(m: MainArgs) {\n  h(x: 5, c: false, out: m.stdout);\n}\n",
    );
    for note in [
        "\n  [1]  1:30: this `if` has no type yet\n",
        "\n  [4]  1:35: this block has no type yet\n",
        "\n  [5]  1:37: `x` has no type yet here\n",
        "\n  [6]  1:3: `x` has no declared type; its uses give it no type yet\n",
    ] {
        assert!(other.contains(note), "{other}");
    }
    for old in [" is _ here", "give it _\n", " gives _\n"] {
        assert!(
            !other.contains(old) && !call.contains(old),
            "{other}\n{call}"
        );
    }
}
