//! What an `else` or a failed test leaves of a value of an unbounded type variable prints with
//! the variable of that value and the type former that removes the rest (DESIGN.md
//! sec:diagnostics, "Types in a message": "What an `else` or a failed test leaves of a value
//! prints with the variable of that value and the type former that removes the rest:
//! `(T \ #outOfBounds) | 0` for the result of `g(r) = r else #outOfBounds -> 0`, and `T \ int`
//! for what `if r is int` leaves of `r` in its `else` arm"; and sec:type_language: "The type
//! of an `else` is a difference and a union ... `e else #a -> d` has the type `(t \ #a) | u`").
//! Before (found by a helper of else1 rewriting `handled.rs`, plan row ELSE-explicit-atoms,
//! fixed by else1x1), the printer joined the leftover to the variable and wrote `(r: T) -> 0 |
//! T`, a type that also holds `#outOfBounds`. The typing kept the difference all along: the
//! tests at the end show a call removes the named atom and only it.
//!
//! An `else #a ->` takes `#a` with any payload or none (sec:type_resolution: "`p else #a -> d`
//! adds `#a` with any payload"), and the type `#a` is the bare atom alone (L1.40d: "`#a` and
//! `#a()` are different types"), so what is removed prints `#a | #a(..)`, as the parameter
//! that takes it does in `handled.rs`. The spec's examples write `T \ #outOfBounds`, which
//! read back holds `#outOfBounds(..)`; the rule of the same sentence ("holds exactly the
//! values the result can hold, and reads back as the same type") is what these tests hold.

use super::{sig, type_errors};
use zedc::check::read::parse_type;

/// What a message says of the type found for `g(positional r) = r else #outOfBounds -> 0`.
const G_FOUND: &str = "`g` is `T -> (T \\ (#outOfBounds | #outOfBounds(..))) | 0`, not";

/// The report of loading `src`, which the checker rejects.
fn report(src: &str) -> String {
    match zedc::run::load(src.as_bytes()) {
        Ok(_) => panic!("accepted:\n{src}"),
        Err(e) => e.to_string(),
    }
}

#[test]
fn an_else_on_a_named_parameter_prints_the_difference() {
    // The spec's own example, with a named parameter, which prints its name.
    assert_eq!(
        sig("g(r) = r else #outOfBounds -> 0;\n", "g"),
        "(r: T) -> (T \\ (#outOfBounds | #outOfBounds(..))) | 0"
    );
}

#[test]
fn an_else_on_a_positional_parameter_prints_the_difference() {
    // DESIGN.md:1200 writes `g(positional r) = r else #outOfBounds -> 0` with the type
    // `(r: T) -> (T \ #outOfBounds) | 0`; a positional parameter prints without its name, as
    // `(bool, T, U) -> T | U` does for `pick` in `signatures.rs` and as "a function of one
    // positional parameter prints as `int -> bool`" (sec:diagnostics), so the type is written
    // `T -> …`.
    assert_eq!(
        sig("g(positional r) = r else #outOfBounds -> 0;\n", "g"),
        "T -> (T \\ (#outOfBounds | #outOfBounds(..))) | 0"
    );
}

#[test]
fn a_chain_of_elses_prints_one_difference_of_the_atoms_in_order() {
    // `(r else #a -> 0) else #b -> 1` leaves `(T \ #a) \ #b`, which is `T \ (#a | #b)`; the
    // atoms are a union, which prints in its fixed order, so the two orders of the chain print
    // alike ("equal types print alike whatever order the program wrote them in"), and the
    // union is parenthesized as the right operand of `\`, a `TypeNot`.
    for src in [
        "g(r) = (r else #a -> 0) else #b -> 1;\n",
        "g(r) = (r else #b -> 0) else #a -> 1;\n",
    ] {
        assert_eq!(
            sig(src, "g"),
            "(r: T) -> (T \\ (#a | #a(..) | #b | #b(..))) | 0 | 1",
            "{src}"
        );
    }
}

#[test]
fn the_difference_beside_its_own_variable_is_the_variable() {
    // `T | (T \ #a)` holds exactly the values of `T`, so the union prints `T`.
    assert_eq!(
        sig("g(r, c: bool) = if c { r } else { r else #a -> 0 };\n", "g"),
        "(r: T, c: bool) -> 0 | T"
    );
}

#[test]
fn two_leftovers_of_one_variable_in_a_union_print_what_both_remove() {
    // `(T \ #a) | (T \ #b)` is `T \ (#a & #b)`, `T`, as no value is both atoms; and `(T \ #a) |
    // (T \ (#a | #b))` is `T \ #a`.
    assert_eq!(
        sig(
            "g(r, c: bool) = if c { r else #a -> 0 } else { r else #b -> 1 };\n",
            "g"
        ),
        "(r: T, c: bool) -> 0 | 1 | T"
    );
    assert_eq!(
        sig(
            "g(r, c: bool) = if c { r else #a -> 0 } else { (r else #a -> 0) else #b -> 1 };\n",
            "g"
        ),
        "(r: T, c: bool) -> (T \\ (#a | #a(..))) | 0 | 1"
    );
}

#[test]
fn each_variable_prints_its_own_difference() {
    assert_eq!(
        sig("g(r, s) = (r else #a -> 0, s else #b -> 1, r, s);\n", "g"),
        "(r: T, s: U) -> ((T \\ (#a | #a(..))) | 0, (U \\ (#b | #b(..))) | 1, T, U)"
    );
    assert_eq!(
        sig("g(r) = (r else #a -> 0, r else #b -> 1);\n", "g"),
        "(r: T) -> ((T \\ (#a | #a(..))) | 0, (T \\ (#b | #b(..))) | 1)"
    );
}

#[test]
fn a_pattern_with_an_empty_payload_removes_that_atom_alone() {
    // `x else #a() -> 2` strips `#a()` alone (DESIGN.md step L1.40d), and `#a` and `#a()` are
    // different types, so the difference is `T \ #a()`, not `T \ #a(..)`.
    assert_eq!(
        sig("g(r) = r else #a() -> 0;\n", "g"),
        "(r: T) -> (T \\ #a()) | 0"
    );
}

#[test]
fn a_difference_in_a_function_result_prints_there() {
    assert_eq!(
        sig("g(r) = { k = r else #a -> 0; (y: int) -> k };\n", "g"),
        "(r: T) -> int -> (T \\ (#a | #a(..))) | 0"
    );
}

#[test]
fn a_difference_is_parenthesized_only_where_the_grammar_needs_it() {
    // A tuple component is a whole `Type`, where a `TypeDiff` stands bare (sec:grammar
    // `TupleType`, `Type`); a member of a union is a `TypeAnd`, where it needs the pair.
    assert_eq!(
        sig("g(r) = (r else #a -> 0, r);\n", "g"),
        "(r: T) -> ((T \\ (#a | #a(..))) | 0, T)"
    );
    assert_eq!(
        sig("k(r) = if r is int { (0, 0) } else { (r, r) };\n", "k"),
        "(r: T) -> (0, 0) | (T \\ int, T \\ int)"
    );
}

#[test]
fn what_a_failed_is_test_leaves_prints_the_difference() {
    // The spec's second example: what `if r is int` leaves of `r` in its `else` arm is `T \
    // int`, here a component of a tuple.
    assert_eq!(
        sig("k(r) = if r is int { (0, 0) } else { (r, 0) };\n", "k"),
        "(r: T) -> (0, 0) | (T \\ int, 0)"
    );
}

#[test]
fn each_printed_difference_reads_back_as_the_same_type() {
    // "reads back as the same type" (sec:diagnostics): the reader makes `T \ s` the leftover
    // the checker makes, a variable of its own with the need of a failed `is s` (`Denote::left_of`
    // in zedc-check), which prints as the same text. Before, it read `T`, and printed `0 | T`.
    for src in [
        "g(r) = r else #outOfBounds -> 0;\n",
        "g(positional r) = r else #outOfBounds -> 0;\n",
        "g(r) = (r else #a -> 0) else #b -> 1;\n",
        "g(r) = r else #a() -> 0;\n",
        "g(r) = (r else #a -> 0, r);\n",
        "g(r, s) = (r else #a -> 0, s else #b -> 1, r, s);\n",
        "g(r) = { k = r else #a -> 0; (y: int) -> k };\n",
        "g(r) = if r is int { (0, 0) } else { (r, r) };\n",
    ] {
        let printed = sig(src, "g");
        assert!(printed.contains(" \\ "), "{src}: {printed}");
        let t = parse_type(&printed).unwrap_or_else(|e| panic!("{printed}: {e}"));
        assert_eq!(t.fns.len(), 1, "{printed}");
        assert_eq!(t.fns[0].to_string(), printed, "{src}");
    }
}

#[test]
fn a_message_writes_the_difference_in_the_type_found_for_the_function() {
    // The step on `g` writes the type found for it, which before dropped the difference:
    // `` `g` is `T -> 0 | T` ``.
    let src = "g(positional r) = r else #outOfBounds -> 0;\n\
               apply(f: (String | #outOfBounds) -> String) = 0;\n\
               main(m: MainArgs) { y = apply(f: g); }\n";
    let out = report(src);
    assert!(out.contains(G_FOUND), "{src}\n{out}");
}

#[test]
fn a_call_removes_the_named_atom_and_keeps_the_others() {
    // The typing is not what the printer lost: at a call with `String | #outOfBounds` the
    // result is `0 | String` (DESIGN.md:1200: "its result at a call with `Utf8String |
    // #outOfBounds` is `0 | Utf8String`"; the checker prints `Utf8String` as `String`).
    let out = report(
        "g(positional r) = r else #outOfBounds -> 0;\n\
         main(m: MainArgs) { y = g(m.args[0]) + true; }\n",
    );
    assert!(out.contains("this call of `g` gives 0 | String\n"), "{out}");
    // Another atom is kept: only the named one is removed.
    let out = report(
        "g(positional r) = r else #a -> 0;\n\
         k(positional b: bool) = if b { \"s\" } else if len(\"x\") > 5 { #a } else { #b };\n\
         main(m: MainArgs) { y = g(k(true)) + true; }\n",
    );
    assert!(
        out.contains("this call of `g` gives 0 | \"s\" | #b\n"),
        "{out}"
    );
}

#[test]
fn a_written_function_type_takes_the_function_exactly_where_the_difference_says() {
    // DESIGN.md:1203: "A written `g : (r: T) -> T | 0` is accepted as a wider result; `g : (r:
    // T) -> T` is rejected". zedc refuses a written result type and a literal type in a written
    // type in this layer, so the test passes `g` where a function type is written, at the
    // instance `T = String | #outOfBounds`, with `int` for the literal `0`: `(r: T) -> T` is
    // `(String | #outOfBounds) -> String | #outOfBounds` there, and refuses `g`, whose `0` it
    // does not hold; `(r: T) -> T | 0` is `… -> String | #outOfBounds | int` and takes it. Had
    // the typing lost the difference, `(String | #outOfBounds) -> String | int` would refuse
    // `g`; and `#other`, which `g` does not name, stays in its result.
    let call = |f: &str| {
        format!(
            "g(positional r) = r else #outOfBounds -> 0;\n\
             apply(f: {f}) = 0;\n\
             main(m: MainArgs) {{ y = apply(f: g); }}\n"
        )
    };
    let refused = |f: &str| {
        let errors = type_errors(&call(f));
        assert_eq!(errors.len(), 1, "{f}: {errors:?}");
        assert!(errors[0].contains(G_FOUND), "{f}: {errors:?}");
    };
    let taken = |f: &str| assert_eq!(type_errors(&call(f)), Vec::<String>::new(), "{f}");
    refused("(String | #outOfBounds) -> String | #outOfBounds");
    taken("(String | #outOfBounds) -> String | #outOfBounds | int");
    taken("(String | #outOfBounds) -> String | int");
    refused("(String | #outOfBounds | #other) -> String | int");
    taken("(String | #outOfBounds | #other) -> String | #other | int");
}
