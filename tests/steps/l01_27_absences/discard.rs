//! `_` drops no loose failure the text does not name (DESIGN.md sec:tour_methods, the
//! rejection row "Statement that writes nothing, or drops a declared result"). `_ = e;` binds
//! a value only when its type has no loose atom other than the default an `else` in `e`
//! writes; a family's atoms are data, and `_` drops them freely. The rejection names each
//! dropped atom, where it enters the value, the derivation, and the repairs.

use std::collections::BTreeSet;

use zed_kernel::types::Type as KType;
use zedc::check::ty::{Carrier, Ty};
use zedc::lex::Span;
use zedc::rejection::Row;

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{info, type_errors};

/// A lookup that misses: a number, or the loose failure `#notFound`.
const LOOKUP: &str = "lookup(positional k: int) = if k > 0 { k } else { #notFound };\n";

/// A parameter typed as a stored row: a number, a missing row, or a stored NULL.
const ROW: &str = "positional x: int | #notFound | #none";

/// The text at `s` of `text`.
fn at(text: &str, s: Span) -> &str {
    &text[s.start..s.end]
}

/// The one error of `text`, a case of the row "Statement that writes nothing, or drops a
/// declared result": its message, its span's text, and each note as `text [span]`.
fn the_error(text: &str) -> (String, String, Vec<String>) {
    let (info, _) = info(text);
    assert_eq!(info.errors.len(), 1, "{text}: {:?}", info.errors);
    let e = &info.errors[0];
    assert_eq!(e.row, Some(Row::WritesNothing), "{text}: {e:?}");
    let notes = e
        .notes
        .iter()
        .map(|n| format!("{} [{}]", n.text, at(text, n.span)))
        .collect();
    (e.message.clone(), at(text, e.span).to_string(), notes)
}

#[test]
fn a_dropped_lookup_miss_is_rejected_with_its_derivation_and_repairs() {
    let t = format!("{LOOKUP}_ = lookup(3);\n");
    let (message, span, notes) = the_error(&t);
    assert_eq!(
        message,
        "`_` drops a loose failure this value may be, #notFound: `_` drops only a failure the program names, as the default of an `else` names it, and this one would be dropped with nothing in the text saying so"
    );
    assert_eq!(span, "_ = lookup(3);");
    assert_eq!(
        notes,
        [
            "the loose failure #notFound enters here [lookup(3)]",
            "this call of `lookup` gives int | #notFound [lookup(3)]",
            "`lookup` is declared here, `(int) -> int | #notFound` \
             [lookup(positional k: int) = if k > 0 { k } else { #notFound };]",
            "repair: write a default for the value, as `_ = … else #ok;`, so the text names what \
             it drops [_ = lookup(3);]",
            "repair: handle each failure with a `match` on the value [_ = lookup(3);]",
            "repair: bind the value to a name, and use the name [_ = lookup(3);]",
        ]
    );
}

#[test]
fn an_else_default_names_what_is_dropped() {
    // A number default replaces the failure; an atom default is the failure the text names.
    for bound in ["_ = lookup(3) else 0;", "_ = lookup(3) else #ok;"] {
        let t = format!("{LOOKUP}{bound}\n");
        assert!(type_errors(&t).is_empty(), "{t}: {:?}", type_errors(&t));
    }
    // The repair the menu offers is accepted, and the program still runs.
    let t = format!("{LOOKUP}_ = lookup(-1) else #ok;\nr = lookup(-1) else #ok;\n");
    assert!(type_errors(&t).is_empty());
    assert_eq!(value(&t, "r"), "#ok");
    // An atom default with a payload names its atom too.
    let t = format!("{LOOKUP}_ = lookup(3) else #ok(1);\n");
    assert!(type_errors(&t).is_empty(), "{:?}", type_errors(&t));
}

#[test]
fn an_else_default_inside_an_if_branch_or_a_block_names_what_is_dropped() {
    // Each branch writes `#ok` as its default, and the `if` passes its branches through
    // unchanged, so the text names every failure the value may be.
    let t = format!(
        "{LOOKUP}f(positional c: int) = {{\n  _ = if c > 0 {{ lookup(1) else #ok }} else {{ lookup(2) else #ok }};\n  0\n}};\n"
    );
    assert!(type_errors(&t).is_empty(), "{t}: {:?}", type_errors(&t));
    // A block's export passes its value through unchanged too.
    let t = format!("{LOOKUP}_ = {{\n  y = 1;\n  lookup(y) else #ok\n}};\n");
    assert!(type_errors(&t).is_empty(), "{t}: {:?}", type_errors(&t));
    // A default in one branch only: the other branch's `#notFound` is still dropped.
    let t = format!(
        "{LOOKUP}f(positional c: int) = {{\n  _ = if c > 0 {{ lookup(1) else #ok }} else {{ lookup(2) }};\n  0\n}};\n"
    );
    let (message, _, notes) = the_error(&t);
    assert_eq!(
        message,
        "`_` drops a loose failure this value may be, #notFound: `_` drops only a failure the program names, as the default of an `else` names it, and this one would be dropped with nothing in the text saying so"
    );
    assert_eq!(
        notes[0],
        "the loose failure #notFound enters here [lookup(2)]"
    );
}

#[test]
fn the_pattern_form_drops_only_the_atom_it_handles() {
    // `else #notFound -> 0` handles the missing row; the stored NULL would still be dropped.
    let t = format!("f({ROW}) = {{\n  _ = x else #notFound -> 0;\n  0\n}};\n");
    let (message, span, notes) = the_error(&t);
    assert_eq!(
        message,
        "`_` drops a loose failure this value may be, #none: `_` drops only a failure the program names, as the default of an `else` names it, and this one would be dropped with nothing in the text saying so"
    );
    assert_eq!(span, "_ = x else #notFound -> 0;");
    // `#none` enters at the parameter, and is not blamed on the default.
    assert_eq!(
        notes[0],
        format!("the loose failure #none enters here [{ROW}]")
    );
    // Handling both in turn leaves nothing dropped.
    let both = format!("f({ROW}) = {{\n  _ = (x else #notFound -> 0) else #none -> 1;\n  0\n}};\n");
    assert!(type_errors(&both).is_empty(), "{:?}", type_errors(&both));
    // A default naming one atom, written after a pattern that handles the other.
    let named =
        format!("f({ROW}) = {{\n  _ = (x else #notFound -> 0) else #none -> #ok;\n  0\n}};\n");
    assert!(type_errors(&named).is_empty(), "{:?}", type_errors(&named));
}

#[test]
fn every_dropped_atom_is_named_with_where_it_enters() {
    // Two failures from two operands: both are named, each where it enters.
    let t = format!(
        "{LOOKUP}f({ROW}) = {{\n  a = lookup(x else 1);\n  b = a + 1;\n  _ = b;\n  0\n}};\n"
    );
    let (message, span, notes) = the_error(&t);
    assert_eq!(
        message,
        "`_` drops a loose failure this value may be, #notFound: `_` drops only a failure the program names, as the default of an `else` names it, and this one would be dropped with nothing in the text saying so"
    );
    assert_eq!(span, "_ = b;");
    // Followed through `b` and `a` to the call that gives it.
    assert_eq!(
        notes[0],
        "the loose failure #notFound enters here [lookup(x else 1)]"
    );
    let t = format!("f({ROW}) = {{\n  _ = x;\n  0\n}};\n");
    let (message, _, notes) = the_error(&t);
    assert_eq!(
        message,
        "`_` drops a loose failure this value may be, #none | #notFound: `_` drops only a failure the program names, as the default of an `else` names it, and this one would be dropped with nothing in the text saying so"
    );
    assert_eq!(
        notes[0],
        format!("the loose failure #none | #notFound enters here [{ROW}]")
    );
    // From two operands of one `+`: each enters at its own operand.
    let t = "f(positional x: int | #a, positional y: int | #b) = {\n  _ = x + y;\n  0\n};\n";
    let (message, _, notes) = the_error(t);
    assert_eq!(
        message,
        "`_` drops a loose failure this value may be, type T1 = #a | #b; T1 | #errs(T1 ->? T1): `_` drops only a failure the program names, as the default of an `else` names it, and this one would be dropped with nothing in the text saying so"
    );
    assert!(notes.contains(&"the loose failure #a enters here [positional x: int | #a]".into()));
    assert!(notes.contains(&"the loose failure #b enters here [positional y: int | #b]".into()));
    assert!(
        notes.contains(
            &"the loose failure type T1 = #a | #b; #errs(T1 ->? T1) enters here [x + y]".into()
        ),
        "{notes:?}"
    );
}

#[test]
fn a_family_atom_is_data_and_dropped_freely() {
    // `type Opt = int | #none` names a family; a `type` declaration arrives at step L2.1, so
    // the rule is read from the type it gives, as `families.rs` does.
    let none = Ty::set(KType::atom("none"));
    let opt = Ty::carrier(Carrier::Int).union(&none).named();
    assert!(opt.dropped(&KType::empty()).is_empty());
    // A loose failure beside the family is still dropped, and only it.
    let read = opt.union(&Ty::set(KType::atom("ioError")));
    assert_eq!(read.dropped(&KType::empty()), KType::atom("ioError"));
    // The same atoms written inline are loose.
    assert_eq!(opt.written().dropped(&KType::empty()), KType::atom("none"));
    // An `else` default names what it writes.
    assert!(opt.written().dropped(&KType::atom("none")).is_empty());
}

#[test]
fn a_discarded_component_is_checked_alone() {
    let pair = "pair(positional k: int) = (lookup(k), k);\n";
    // Component 0 may be the failure, and `_` drops it.
    let t = format!("{LOOKUP}{pair}_, x = pair(1);\n");
    let (message, span, notes) = the_error(&t);
    assert_eq!(
        message,
        "`_` drops a loose failure component 0 of this value may be, #notFound: `_` drops only a failure the program names, as the default of an `else` names it, and this one would be dropped with nothing in the text saying so"
    );
    assert_eq!(span, "_, x = pair(1);");
    assert_eq!(
        notes[0],
        "the loose failure #notFound enters here [pair(1)]"
    );
    // Component 1 is a number, and `_` drops it freely.
    let t = format!("{LOOKUP}{pair}x, _ = pair(1);\n");
    assert!(type_errors(&t).is_empty(), "{:?}", type_errors(&t));
    // Written as a tuple, the component's own `else` names its default.
    let t = format!("{LOOKUP}_, x = (lookup(1) else #ok, 2);\n");
    assert!(type_errors(&t).is_empty(), "{:?}", type_errors(&t));
    let t = format!("{LOOKUP}_, x = (lookup(1), 2);\n");
    let (_, _, notes) = the_error(&t);
    assert_eq!(
        notes[0],
        "the loose failure #notFound enters here [lookup(1)]"
    );
}

#[test]
fn a_failure_of_the_whole_tuple_reaches_each_named_component() {
    // The failure is the whole value's, not a component's: `x` receives it, so nothing is
    // dropped; with every target `_`, it is dropped.
    let maybe = "maybe(positional k: int) = if k > 0 { (k, k) } else { #notFound };\n";
    let t = format!("{maybe}_, x = maybe(1);\n");
    assert!(type_errors(&t).is_empty(), "{:?}", type_errors(&t));
    assert_eq!(
        value(&format!("{maybe}_, x = maybe(-1);\n"), "x"),
        "#notFound"
    );
    let t = format!("{maybe}_, _ = maybe(1);\n");
    let (message, span, _) = the_error(&t);
    assert_eq!(
        message,
        "`_` drops a loose failure this value may be, #notFound: `_` drops only a failure the program names, as the default of an `else` names it, and this one would be dropped with nothing in the text saying so"
    );
    assert_eq!(span, "_, _ = maybe(1);");
}

#[test]
fn a_parenthesized_target_list_is_not_a_binding_at_layer_l1() {
    // `(_, x) = f();` destructures in a parameter list only (`TupleParam`, layer L2); as a
    // binding the grammar has `_, x = f();`, which the test above checks.
    let text = "(_, x) = (1, 2);\n";
    let tokens = zedc::lex::lex_fence(text).unwrap();
    assert!(zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP).is_err());
}

#[test]
fn a_match_arm_is_a_pattern_not_a_dropped_binding() {
    // DESIGN.md's table of `_`: in patterns it matches anything, in binding targets it
    // discards. This zedc does not compile `match` yet, and its arm `_ ->` is refused only as
    // that.
    let text = "f(positional x: int | #notFound) = match x { #notFound -> 0, _ -> 1 };\n";
    let tokens = zedc::lex::lex_fence(text).unwrap();
    let tree = zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP).unwrap();
    let stmts = zedc::ast::unit(text, &tokens, &tree).unwrap();
    let err = zedc::resolve::resolve(&stmts).unwrap_err();
    let shown = format!("{err:?}");
    assert!(zed_tests::is_not_yet(&shown), "{shown}");
    assert!(!shown.contains("drops"), "{shown}");
}

#[test]
fn checking_units_together_and_alone_agree() {
    let units = [
        format!("{LOOKUP}_ = lookup(3);\n"),
        format!("g({ROW}) = {{\n  _ = x else #notFound -> 0;\n  0\n}};\n"),
        "h(positional y: int | #e) = {\n  _ = y else 0;\n  _, z = (y, 1);\n  z\n};\n".into(),
        "maybe(positional k: int) = if k > 0 { (k, k) } else { #notFound };\n_, _ = maybe(1);\n"
            .into(),
    ];
    let errors = |text: &str| -> BTreeSet<(String, String)> {
        info(text)
            .0
            .errors
            .iter()
            .map(|e| (e.message.clone(), at(text, e.span).to_string()))
            .collect()
    };
    let alone: BTreeSet<_> = units.iter().flat_map(|u| errors(u)).collect();
    let together = errors(&units.concat());
    assert_eq!(alone.len(), 4, "{alone:?}");
    assert_eq!(together, alone);
    // In the reverse order too: the result does not depend on which unit comes first.
    let reversed: String = units.iter().rev().map(String::as_str).collect();
    assert_eq!(errors(&reversed), alone);
}
