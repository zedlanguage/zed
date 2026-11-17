//! Row "Or-pattern alternatives bind different names" (DESIGN.md sec:diagnostics, step L2.7b,
//! *Names*): every alternative of an or-pattern binds the same names. Where they differ, the
//! error names each name with the alternatives that bind it, or those that do not when they are
//! fewer, and gives two repairs: the arm written out once for each alternative, where the rest
//! of the arm reads no name an alternative leaves unbound, and, where each alternative binds one
//! name and the rest of the arm reads none but the first's, the first's name in each.

use zedc::ast::Error;
use zedc::rejection::Row;

use super::resolution_errors;

/// The one error of row "Or-pattern alternatives bind different names" that `src` gives.
#[track_caller]
fn differ(src: &str) -> Error {
    let errors = resolution_errors(src);
    let mut hits = errors
        .into_iter()
        .filter(|e| e.row == Some(Row::OrPatternNamesDiffer));
    let e = hits
        .next()
        .unwrap_or_else(|| panic!("no names-differ error for {src}"));
    assert!(hits.next().is_none(), "two names-differ errors for {src}");
    e
}

/// The repairs of `e`, without their `repair: ` prefix.
fn repairs(e: &Error) -> Vec<&str> {
    e.notes
        .iter()
        .filter_map(|n| n.text.strip_prefix("repair: "))
        .collect()
}

const OUT: &str = "write the arm out once for each alternative: ";
const SAME: &str = "bind the same name in each alternative: ";

#[test]
fn the_row_in_design_gives_its_message_and_both_repairs() {
    let src = "f(r) = match r { (#ok(x) | #err(y)) -> 0, _ -> 1 };\n";
    let e = differ(src);
    assert_eq!(&src[e.span.start..e.span.end], "(#ok(x) | #err(y))");
    assert!(
        e.message.starts_with(
            "the alternatives of this or-pattern bind different names: `x` is bound only in the \
             first alternative and `y` only in the second"
        ),
        "{}",
        e.message
    );
    assert_eq!(
        repairs(&e),
        [
            format!("{OUT}`#ok(x) -> 0, #err(y) -> 0`"),
            format!("{SAME}`(#ok(x) | #err(x)) -> 0`"),
        ]
    );
}

#[test]
fn a_name_most_alternatives_bind_is_given_with_those_that_do_not() {
    let src = "f(r) = match r { (#a(x, y) | #b(x) | #c(y)) -> 0, _ -> 1 };\n";
    let e = differ(src);
    assert!(
        e.message.starts_with(
            "the alternatives of this or-pattern bind different names: `x` is bound in every \
             alternative but the third and `y` in every alternative but the second"
        ),
        "{}",
        e.message
    );
    // The first alternative binds two names, so no one name serves in each.
    assert_eq!(
        repairs(&e),
        [format!("{OUT}`#a(x, y) -> 0, #b(x) -> 0, #c(y) -> 0`")]
    );
}

#[test]
fn an_or_pattern_as_a_payload_is_written_out_in_the_atoms_parentheses() {
    let e = differ("f(r) = match r { #p(#ok(x) | #err(y)) -> 0, _ -> 1 };\n");
    assert_eq!(
        repairs(&e),
        [
            format!("{OUT}`#p(#ok(x)) -> 0, #p(#err(y)) -> 0`"),
            format!("{SAME}`#p(#ok(x) | #err(x)) -> 0`"),
        ]
    );
}

/// A repair is left out where the arm it writes would read a name its pattern does not bind.
#[test]
fn a_repair_that_would_read_an_unbound_name_is_left_out() {
    // The body reads `x`: the second arm written out would not bind it; `x` in each serves.
    let e = differ("f(r) = match r { (#ok(x) | #err(y)) -> x, _ -> 1 };\n");
    assert_eq!(repairs(&e), [format!("{SAME}`(#ok(x) | #err(x)) -> x`")]);
    // The guard reads `x` too.
    let e = differ("f(r) = match r { (#ok(x) | #err(y)) where x > 0 -> 1, _ -> 1 };\n");
    assert_eq!(
        repairs(&e),
        [format!("{SAME}`(#ok(x) | #err(x)) where x > 0 -> 1`")]
    );
    // The body reads `y`, which renaming would leave unbound, and which the first arm written
    // out would not bind: no repair is offered, only the message.
    let e = differ("f(r) = match r { (#ok(x) | #err(y)) -> y + 1, _ -> 1 };\n");
    assert_eq!(repairs(&e), Vec::<&str>::new());
}

#[test]
fn alternatives_binding_the_same_names_are_not_refused() {
    for src in [
        "f(r) = match r { (#ok(x) | #err(x)) -> x, _ -> 1 };\n",
        "f(r) = match r { (#a | #b | #c) -> 0, _ -> 1 };\n",
        "f(r) = match r { ((x, _) | (_, x)) -> x };\n",
        "f(r) = match r { ((n is int) | (n is f64)) -> n, _ -> 0 };\n",
        "f(r) = r else #p(#ok(x) | #err(x)) -> x;\n",
    ] {
        let errors = resolution_errors(src);
        assert!(
            !errors
                .iter()
                .any(|e| e.row == Some(Row::OrPatternNamesDiffer)),
            "{src}: {errors:?}"
        );
    }
}

#[test]
fn a_nested_or_pattern_is_refused_at_the_group_whose_alternatives_differ() {
    let src = "f(r) = match r { ((#a(x) | #b(x)) | #c(y)) -> 0, _ -> 1 };\n";
    let e = differ(src);
    assert_eq!(&src[e.span.start..e.span.end], "((#a(x) | #b(x)) | #c(y))");
    let src = "f(r) = match r { ((#a(x) | #b(y)) | #c) -> 0, _ -> 1 };\n";
    let errors: Vec<Error> = resolution_errors(src)
        .into_iter()
        .filter(|e| e.row == Some(Row::OrPatternNamesDiffer))
        .collect();
    let spans: Vec<&str> = errors
        .iter()
        .map(|e| &src[e.span.start..e.span.end])
        .collect();
    assert!(spans.contains(&"(#a(x) | #b(y))"), "{spans:?}");
}

/// In an `else` tail, the or-pattern stands as a payload; the tail is a form of a later step,
/// so the error comes with that one, and no repair rewrites the tail. The or-pattern shares the
/// atom's parentheses, and its span holds them.
#[test]
fn an_else_payload_whose_alternatives_differ_is_refused() {
    let src = "f(r) = r else #p(#ok(x) | #err(y)) -> 0;\n";
    let e = differ(src);
    assert_eq!(&src[e.span.start..e.span.end], "(#ok(x) | #err(y))");
    assert_eq!(repairs(&e), Vec::<&str>::new());
}
