//! Loose atoms, the failure channel: `else` defaults them, the pattern form handles the one it
//! names, and they flow through the operators unchanged.

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{sig, type_errors};

/// A lookup's result: a value, a missing row, or a stored NULL.
const LOOKUP: &str = "positional x: int | #notFound | #none";

#[test]
fn else_defaults_every_loose_atom() {
    let t = format!("f({LOOKUP}) = x else 0;\n");
    assert_eq!(sig(&t, "f"), "(int | #none | #notFound) -> int");
    let run = format!("{t}a = f(#none);\nb = f(#notFound);\nc = f(4);\n");
    assert_eq!(value(&run, "a"), "0");
    assert_eq!(value(&run, "b"), "0");
    assert_eq!(value(&run, "c"), "4");
}

#[test]
fn the_pattern_form_handles_the_atom_it_names_and_keeps_the_rest() {
    let t = format!("f({LOOKUP}) = x else #notFound -> -1;\n");
    assert_eq!(sig(&t, "f"), "(int | #none | #notFound) -> int | #none");
    let run = format!("{t}a = f(#none);\nb = f(#notFound);\nc = f(4);\n");
    assert_eq!(value(&run, "a"), "#none");
    assert_eq!(value(&run, "b"), "-1");
    assert_eq!(value(&run, "c"), "4");
    // Two patterns in turn handle both, and the result is the plain number.
    let both = format!("f({LOOKUP}) = (x else #notFound -> -1) else #none -> 0;\n");
    assert_eq!(sig(&both, "f"), "(int | #none | #notFound) -> int");
    // A pattern naming an atom the value cannot hold handles nothing.
    let other = format!("f({LOOKUP}) = x else #empty -> 0;\n");
    assert_eq!(
        sig(&other, "f"),
        "type T1 = int | #none | #notFound;\n(T1) -> T1"
    );
}

/// A value that may be the number 3, the atom `#e` with the payload `code: 1`, or `#e` with
/// no payload.
const PICK: &str = "pick(positional c: bool, positional d: bool) = \
                    if c { #e(code: 1) } else { if d { #e } else { 3 } };\n";

#[test]
fn a_pattern_with_a_payload_keeps_the_atom_in_the_type() {
    // DESIGN.md step L1.27: "The pattern form `e else #a -> d` removes `#a` from the type when
    // the pattern has no payload; a pattern with a payload keeps the atom in the type, since
    // other payloads may remain."
    assert_eq!(sig(PICK, "pick"), "(bool, bool) -> 3 | #e | #e(code: 1)");
    let with = format!(
        "{PICK}f(positional c: bool, positional d: bool) = pick(c, d) else #e(code:) -> 0;\n"
    );
    assert_eq!(sig(&with, "f"), "(bool, bool) -> 0 | 3 | #e | #e(code: 1)");
    let without =
        format!("{PICK}f(positional c: bool, positional d: bool) = pick(c, d) else #e -> 0;\n");
    assert_eq!(sig(&without, "f"), "(bool, bool) -> 0 | 3");
    // The payload pattern takes `#e(code: 1)` and passes the bare `#e` on, which is the
    // payload that remains.
    let run = format!("{with}a = f(true, false);\nb = f(false, true);\nc = f(false, false);\n");
    assert_eq!(value(&run, "a"), "0");
    assert_eq!(value(&run, "b"), "#e");
    assert_eq!(value(&run, "c"), "3");
    let run = format!("{without}b = f(false, true);\n");
    assert_eq!(value(&run, "b"), "0");
}

#[test]
fn a_payload_pattern_that_binds_its_field_keeps_the_atom_for_underscore() {
    // `code` is bound from the payload; `#e` stays in the type even where the one payload the
    // value can hold is handled, so `_` still sees a loose failure and rejects it.
    let one = "pick(positional c: bool) = if c { #e(code: 1) } else { 3 };\n";
    let bound = format!("{one}f(positional c: bool) = pick(c) else #e(code:) -> code;\n");
    assert_eq!(sig(&bound, "f"), "(bool) -> 1 | 3 | #e(code: 1)");
    assert_eq!(value(&format!("{bound}y = f(true);\n"), "y"), "1");
    assert_eq!(
        type_errors(&format!(
            "{one}f(positional c: bool) = {{ _ = pick(c) else #e(code:) -> code; 1 }};\n"
        )),
        [
            "`_` drops a loose failure this value may be, #e(code: 1): `_` drops only a failure \
             the program names, as the default of an `else` names it, and this one would be \
             dropped with nothing in the text saying so [_ = pick(c) else #e(code:) -> code;]"
        ]
    );
    assert_eq!(
        type_errors(&format!(
            "{one}f(positional c: bool) = {{ _ = pick(c) else #e -> 0; 1 }};\n"
        )),
        Vec::<String>::new()
    );
}

#[test]
#[ignore = "open: an atom type with a payload in a parameter type, `#e(int)`, is refused by \
            zedc at L1"]
fn a_declared_payload_pattern_keeps_the_atom_in_the_type() {
    // The program of the test audit of 2026-11-08, with a declared parameter. The printed
    // types are read from the printer's form for an inferred payload, `#e(code: 1)`.
    let t = "positional x: int | #e(code: int)";
    assert_eq!(
        sig(&format!("f({t}) = x else #e(code:) -> 0;\n"), "f"),
        "(int | #e(code: int)) -> int | #e(code: int)"
    );
    assert_eq!(
        sig(&format!("f({t}) = x else #e -> 0;\n"), "f"),
        "(int | #e(code: int)) -> int"
    );
}

#[test]
fn the_three_absences_stay_three_facts() {
    // Through an operator each absence flows unchanged, and two at once merge into `#errs`.
    assert_eq!(
        sig(
            "f(positional x: int | #notFound, positional y: int | #none) = x + y;\n",
            "f"
        ),
        "type T1 = #none | #notFound;\n(int | #notFound, int | #none) -> int | #errs(T1 ->? T1) | #none | #notFound"
    );
    let run = "f(positional x: int | #notFound, positional y: int | #none) = x + y;\n\
               a = f(#notFound, 1);\nb = f(1, #none);\nc = f(#notFound, #none);\n";
    assert_eq!(value(run, "a"), "#notFound");
    assert_eq!(value(run, "b"), "#none");
    assert_eq!(value(run, "c"), "#errs({#none, #notFound})");
}

#[test]
fn a_loose_atom_flows_through_safe_navigation() {
    let t = "f(positional x: int | #notFound) = x?.abs;\n";
    assert_eq!(sig(t, "f"), "type T1 = int | #notFound;\n(T1) -> T1");
    assert!(type_errors(t).is_empty());
    let run = format!("{t}a = f(#notFound);\nb = f(-3);\n");
    assert_eq!(value(&run, "a"), "#notFound");
    assert_eq!(value(&run, "b"), "3");
}

#[test]
fn a_loose_atom_passes_through_a_declared_function_whose_type_omits_it() {
    // Rule 6: the atom selects no arrow of `g` and is the call's value; `g`'s body never sees it.
    let t = "g(positional n: int) = n + 1;\n\
             f(positional x: int | #notFound) = g(x);\n";
    assert!(type_errors(t).is_empty());
    assert_eq!(sig(t, "f"), "type T1 = int | #notFound;\n(T1) -> T1");
    let run = format!("{t}a = f(#notFound);\nb = f(2);\n");
    assert_eq!(value(&run, "a"), "#notFound");
    assert_eq!(value(&run, "b"), "3");
}

#[test]
fn a_loose_atom_passes_through_a_generic_function_bounded_to_carriers() {
    // Rule 6 at an inferred parameter: `add` is `(T, T) -> T for T in int | f64 | rat`, a
    // bound that holds no atom, so `#nf` selects no arrow and is the call's value.
    let t = "add(positional a, positional b) = a + b;\n\
             h(positional y: int | #nf) = add(y, 1);\n";
    assert!(type_errors(t).is_empty());
    assert_eq!(sig(t, "h"), "type T1 = int | #nf;\n(T1) -> T1");
    let run = format!("{t}a = h(#nf);\nb = h(2);\n");
    assert_eq!(value(&run, "a"), "#nf");
    assert_eq!(value(&run, "b"), "3");
}

#[test]
fn a_call_takes_the_arrow_of_a_generic_function_that_takes_its_atoms() {
    // `r` handles the atoms of `x` and lets them reach its result, so it has two arrows; the
    // first, whose `T` is bounded to carriers, takes no atom, and a call passing `#nf` takes
    // the second.
    let t = "r(positional x, positional d) = if (x else d) == d { d } else { x + d };\n\
             h(positional y: int | #nf) = r(y, 1);\n";
    assert!(type_errors(t).is_empty());
    assert_eq!(
        sig(t, "r"),
        "((T, T) -> T) & ((T | #_, T) -> T | #_) for T in int | f64 | rat"
    );
    assert_eq!(sig(t, "h"), "(int | #nf) -> int | #_");
    let run = format!("{t}a = h(#nf);\nb = h(2);\n");
    assert_eq!(value(&run, "a"), "1");
    assert_eq!(value(&run, "b"), "3");
}

#[test]
fn a_loose_atom_enters_a_parameter_whose_bound_may_take_other_values() {
    // `k`'s parameter may take other values, so its type `_` holds every atom (DESIGN.md
    // L1.26) and `#nf` is not passed by: it enters `k`, whose need `size(a)` refuses it.
    let t = "size(positional v: int | (int, int)) = 1;\n\
             k(positional a) = (size(a), a);\n";
    let bad = format!("{t}h(positional y: int | #nf) = k(y);\n");
    assert_eq!(
        type_errors(&bad),
        [
            "`k` does not take (int | #nf): no arrow of `k` takes these types [k(y)]",
            "`size` does not take #nf, which is not int | (int, int): `size` takes only values of int | (int, int) [k(y)]"
        ]
    );
    let ok = format!("{t}h(positional y: int) = k(y);\nb = h(2);\n");
    assert!(type_errors(&ok).is_empty());
    assert_eq!(value(&ok, "b"), "(1, 2)");
}

#[test]
fn a_loose_atom_enters_the_first_arrow_at_a_parameter_that_may_take_other_values() {
    // `x`'s atoms reach the result, so `r` has two arrows; `v` may take other values, so in
    // both arrows its type holds every atom and `#nf` enters it, where `size` refuses it. The
    // first arrow takes the call, as its other parameter takes the plain `1`. `v`'s variable
    // stands in both arrows, so it prints by name, `T` (DESIGN sec:diagnostics, UNDERSCORE-print).
    let t = "size(positional v: int | (int, int)) = 1;\n\
             r(positional x, positional v) = if (x else 0) == 0 { size(v) } else { x + size(v) };\n";
    assert_eq!(
        sig(t, "r"),
        "type T1 = int | #_;\n((int, T) -> int) & ((T1, T) -> T1)"
    );
    let bad = format!("{t}h(positional y: int | #nf) = r(1, y);\n");
    assert_eq!(
        type_errors(&bad),
        [
            "`r` does not take (1, int | #nf): no arrow of `r` takes these types\n  T1 stands for a part written more than once:\n    type T1 = int | #_; [r(1, y)]",
            "`size` does not take #nf, which is not int | (int, int): `size` takes only values of int | (int, int)\n  T1 stands for a part written more than once:\n    type T1 = int | #_; [r(1, y)]"
        ]
    );
    let ok = format!("{t}h(positional y: int | #nf) = r(y, 2);\na = h(#nf);\nb = h(2);\n");
    assert!(type_errors(&ok).is_empty());
    assert_eq!(value(&ok, "a"), "1");
    assert_eq!(value(&ok, "b"), "3");
}

/// Item PRINT-fmt-audit: the repair that tests the value with `is` writes the parameter's type
/// as `is` reads it, a function type in parentheses. Before, it was
/// `if v is (int) -> int { … }`, which reads as `(v is (int)) -> int`.
#[test]
fn the_is_repair_writes_a_function_type_in_parentheses() {
    let t = "ap(positional g: (int) -> int) = g(1);\n";
    let bad = format!("{t}k(positional a) = (ap(a), a);\nh(positional y: int | #nf) = k(y);\n");
    let out = match zedc::run::load(bad.as_bytes()) {
        Ok(_) => panic!("accepted:\n{bad}"),
        Err(e) => e,
    };
    assert!(
        out.contains(
            "repair: test the value with `is` first, as `if v is ((int) -> int) { … }`, or \
             handle the values that are not (int) -> int with `else` or `match`"
        ),
        "{out}"
    );
    assert!(
        out.contains("repair: pass `ap` a value of (int) -> int"),
        "{out}"
    );
    // The repair, applied, is accepted, and the type it names reads back as written.
    let ok = format!(
        "{t}k(positional a) = if a is ((int) -> int) {{ ap(a) }} else {{ 0 }};\n\
         h(positional y: int | #nf) = k(y);\n"
    );
    assert!(type_errors(&ok).is_empty(), "{:?}", type_errors(&ok));
    let back = zedc::check::read::parse_type("(int) -> int").unwrap();
    assert_eq!(back.to_string(), "(int) -> int");
}

/// Item REPAIR-is-shared-type: the `is` repair on a type with a part written twice. Before, the
/// repair wrote the definition inside the code, `if v is type T1 = int | #x; (T1, T1) { … }`,
/// which no parser reads. Now the message writes the definition once, on a line of its own,
/// and the repair says to write it at the top level; its name is no name of the program.
/// Applied, the repaired program parses and resolves, and the declaration is the one thing
/// this zedc does not compile yet (DESIGN.md step L2.1); the same test with the part written
/// out is accepted.
#[test]
fn the_is_repair_on_a_shared_part_declares_it_at_the_top_level() {
    let t = "ap(positional g: (int | #x, int | #x)) = 0;\n";
    let call = "h(positional y: int | #nf) = k(y);\n";
    let bad = format!("{t}k(positional a) = (ap(a), a);\n{call}");
    let out = match zedc::run::load(bad.as_bytes()) {
        Ok(_) => panic!("accepted:\n{bad}"),
        Err(e) => e,
    };
    assert!(
        out.contains(
            "`ap` does not take #nf, which is not (T1, T1): `ap` takes only values of (T1, T1)\n  \
             T1 stands for a part written more than once:\n    type T1 = int | #x;\n"
        ),
        "{out}"
    );
    assert!(
        out.contains(
            "repair: test the value with `is` first, as `if v is (T1, T1) { … }`, with the \
             declaration above written first at the top level of the file, before the function, \
             or handle the values that are not (T1, T1) with `else` or `match`"
        ),
        "{out}"
    );
    assert!(
        out.contains("repair: pass `ap` a value of (T1, T1)\n"),
        "{out}"
    );
    assert!(!out.contains("type T1 = int | #x; "), "{out}");
    // The repair applied: it parses and resolves, and only the declaration is refused.
    let fixed = format!(
        "type T1 = int | #x;\n{t}k(positional a) = if a is (T1, T1) {{ ap(a) }} else {{ 0 }};\n\
         {call}"
    );
    let refused = match zedc::run::load(fixed.as_bytes()) {
        Ok(_) => panic!("type declarations compile now: check the repair in full:\n{fixed}"),
        Err(e) => e,
    };
    assert_eq!(refused.lines().count(), 1, "{refused}");
    assert!(
        refused.contains("1:1: a type declaration is part of the Zed language"),
        "{refused}"
    );
    let inline = format!(
        "{t}k(positional a) = if a is (int | #x, int | #x) {{ ap(a) }} else {{ 0 }};\n{call}"
    );
    assert!(
        type_errors(&inline).is_empty(),
        "{:?}",
        type_errors(&inline)
    );
    // A program that names something `T1` gets the next free name.
    let taken = format!("T1(positional q) = q;\n{bad}");
    let out = match zedc::run::load(taken.as_bytes()) {
        Ok(_) => panic!("accepted:\n{taken}"),
        Err(e) => e,
    };
    assert!(out.contains("as `if v is (T2, T2) { … }`"), "{out}");
    assert!(out.contains("\n    type T2 = int | #x;\n"), "{out}");
}
