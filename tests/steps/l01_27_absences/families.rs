//! The atoms of a named family, `type Color = #red | #green | #blue`, are data. The marking is
//! the type's: `Ty::named` gives it, as a `type` declaration will (step L2.1), and these tests
//! read the rules from the type representation and the operator rule directly.

use zed_kernel::types::Type as KType;
use zedc::ast::BinaryOp;
use zedc::check::Operator;
use zedc::check::ty::{Carrier, Ty};
use zedc::check::walk::{check_given, operator};

/// `#a | #b | …`.
fn atoms(names: &[&str]) -> Ty {
    names
        .iter()
        .fold(Ty::empty(), |t, n| t.union(&Ty::set(KType::atom(n))))
}

/// `Color`, the named family `#red | #green | #blue`.
fn color() -> Ty {
    atoms(&["red", "green", "blue"]).named()
}

/// `Color | #ioError`: a family and a loose failure.
fn read_color() -> Ty {
    color().union(&atoms(&["ioError"]))
}

#[test]
fn else_keeps_the_family_and_strips_the_loose_atom() {
    let t = read_color();
    assert_eq!(t.loose(), KType::atom("ioError"));
    assert_eq!(t.without_loose(), color());
    // Without the name, every atom is loose and `else` strips them all.
    assert!(read_color().written().without_loose().is_empty());
}

#[test]
fn the_pattern_form_strips_a_family_member() {
    let t = read_color().diff(&atoms(&["red"]));
    assert_eq!(t.to_string(), "#blue | #green | #ioError");
    // What is left of the family is still the family's.
    assert_eq!(t.without_loose().to_string(), "#blue | #green");
}

#[test]
fn a_join_keeps_an_atom_protected_when_either_side_protects_it() {
    let loose_red = atoms(&["red"]);
    for joined in [color().union(&loose_red), loose_red.union(&color())] {
        assert_eq!(joined.loose(), KType::empty());
        assert_eq!(joined.without_loose(), color());
    }
}

#[test]
fn a_written_type_makes_the_atoms_loose() {
    let t = color().union(&Ty::carrier(Carrier::Int)).written();
    assert_eq!(t.loose(), color().atoms());
    assert_eq!(t.without_loose(), Ty::carrier(Carrier::Int));
}

#[test]
fn narrowing_keeps_the_marking() {
    let t = read_color().union(&Ty::carrier(Carrier::Int));
    let red = t.meet(&atoms(&["red", "ioError"]));
    assert_eq!(red.loose(), KType::atom("ioError"));
    assert_eq!(red.without_loose().to_string(), "#red");
    let not_int = t.diff(&Ty::carrier(Carrier::Int));
    assert_eq!(not_int.without_loose(), color());
}

#[test]
fn a_family_atom_that_selects_no_arrow_is_an_error() {
    let int = Ty::carrier(Carrier::Int);
    let (_, errors) = operator(Operator::Binary(BinaryOp::Add), &[int.clone(), color()]);
    assert_eq!(
        errors,
        [
            "`+` does not take (int, #blue | #green | #red): these are the types of its arguments here, and `+` has no arrow that takes them all"
        ]
    );
    // Loose, the same atoms flow through.
    let (out, errors) = operator(
        Operator::Binary(BinaryOp::Add),
        &[int.clone(), color().written()],
    );
    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(out.to_string(), "#blue | #green | #red");
    // The loose failure beside a family still flows; the family is still rejected.
    let (out, errors) = operator(
        Operator::Binary(BinaryOp::Add),
        &[int.clone(), int.union(&read_color())],
    );
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(out.atoms().contains(&zed_kernel::Value::atom("ioError")));
}

/// `text`, checked with the name its first statement binds given the type `v` (as a `type`
/// declaration will give it one, step L2.5): each error, its message and then its notes and
/// menu, one line each.
fn errors_given(text: &str, v: &Ty) -> Vec<String> {
    let tokens = zedc::lex::lex_fence(text).unwrap();
    let tree = zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP).unwrap();
    let stmts = zedc::ast::unit(text, &tokens, &tree).unwrap();
    let res = zedc::resolve::resolve(&stmts).unwrap();
    (check_given(&stmts, &res, text, v.clone())
        .errors
        .into_iter())
    .map(|e| {
        let notes = e.notes.iter().map(|n| format!("\n{}", n.text));
        format!("{}{}{}", e.message, notes.collect::<String>(), e.menu)
    })
    .collect()
}

/// A program that reads `v`, of the type `v` given, in the condition of `if`, where neither an
/// atom of a family nor any other atom has a case.
const IF: &str = "v = 0;\ny = if v { 1 } else { 2 };\n";

/// The code of the repair `which` (0 for the `else` chain, 1 for the `match`) in `error`, with
/// each `d` given as `true`, which the condition of `if` takes.
fn repair(error: &str, which: usize) -> String {
    let line = (error.lines())
        .filter(|l| l.starts_with("repair: "))
        .nth(which)
        .expect("the repair");
    let code = line.split_once(" as `").expect("the repair's code").1;
    let code = code
        .split_once('`')
        .expect("the end of the repair's code")
        .0;
    code.replace(" -> d", " -> true")
}

/// `IF` with `v` replaced by the repair's code.
fn repaired(error: &str, which: usize) -> String {
    IF.replace("if v ", &format!("if {} ", repair(error, which)))
}

/// `text` parses as a unit: how the `match` repair is checked, since `match` is parsed from
/// step L2.2 but checked only in layer L2, after this step.
fn parses(text: &str) -> bool {
    let tokens = zedc::lex::lex_fence(text).unwrap();
    zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP).is_ok()
}

#[test]
fn a_family_of_one_atom_has_a_repair_for_that_atom() {
    let v = atoms(&["off"]).union(&Ty::carrier(Carrier::Bool)).named();
    let errors = errors_given(IF, &v);
    assert_eq!(
        errors,
        [
            "the condition of `if` does not take #off, which the value here may be: an atom of a \
          named family is data like any other value, not a failure that passes through the \
          condition of `if` untouched, and the condition of `if` has no case for it\n\
          `v` is bool | #off here\n\
          `v` is bound here\n\
          repair: replace `#off` by a value the condition of `if` takes before the value gets \
          here, as `(v else #off -> d)`, where `v` is the value and `d` the value to use \
          instead\n\
          repair: test the value with `match`, with an arm for the atom and one for the rest, \
          as `match v { #off -> d, rest -> rest }`, where `v` is the value and `d` the value to \
          use in place of the atom"
        ]
    );
    let fixed = repaired(&errors[0], 0);
    assert_eq!(
        fixed,
        "v = 0;\ny = if (v else #off -> true) { 1 } else { 2 };\n"
    );
    assert_eq!(errors_given(&fixed, &v), Vec::<String>::new());
    assert!(parses(&repaired(&errors[0], 1)));
}

#[test]
fn a_value_of_two_atoms_and_nothing_else_has_no_arm_for_the_rest() {
    let v = atoms(&["on", "off"]).named();
    let errors = errors_given(IF, &v);
    assert_eq!(
        errors,
        [
            "the condition of `if` does not take #off | #on, which the value here may be: an atom \
          of a named family is data like any other value, not a failure that passes through the \
          condition of `if` untouched, and the condition of `if` has no case for it\n\
          `v` is #off | #on here\n\
          `v` is bound here\n\
          repair: replace each of `#off` and `#on` by a value the condition of `if` takes \
          before the value gets here, as `(v else #off -> d else #on -> d)`, where `v` is the \
          value and each `d` the value to use in place of the atom before it\n\
          repair: test the value with `match`, with one arm for each atom, as \
          `match v { #off -> d, #on -> d }`, where `v` is the value and each `d` the value to \
          use in place of the atom of its arm"
        ]
    );
    let fixed = repaired(&errors[0], 0);
    assert_eq!(
        fixed,
        "v = 0;\ny = if (v else #off -> true else #on -> true) { 1 } else { 2 };\n"
    );
    assert_eq!(errors_given(&fixed, &v), Vec::<String>::new());
    // Handling one of the two atoms is not enough: the other still reaches `if`.
    let half = IF.replace("if v ", "if (v else #off -> true) ");
    let left = errors_given(&half, &v);
    assert_eq!(left.len(), 1, "{left:?}");
    assert!(
        left[0].starts_with("the condition of `if` does not take #on, "),
        "{}",
        left[0]
    );
    assert!(parses(&repaired(&errors[0], 1)));
}

#[test]
fn a_family_of_many_atoms_beside_a_loose_failure_has_a_pattern_for_each() {
    let days = ["mon", "tue", "wed", "thu", "fri", "sat", "sun"];
    let v = (atoms(&days).union(&Ty::carrier(Carrier::Bool)).named()).union(&atoms(&["ioError"]));
    let errors = errors_given(IF, &v);
    assert_eq!(
        errors,
        [
            "the condition of `if` does not take #fri | #mon | #sat | #sun | #thu | #tue | #wed, \
          which the value here may be: an atom of a named family is data like any other value, \
          not a failure that passes through the condition of `if` untouched, and the condition \
          of `if` has no case for it\n\
          `v` is bool | #fri | #ioError | #mon | #sat | #sun | #thu | #tue | #wed here\n\
          `v` is bound here\n\
          repair: replace each of `#fri`, `#mon`, `#sat`, `#sun`, `#thu`, `#tue` and `#wed` by \
          a value the condition of `if` takes before the value gets here, as `(v else #fri -> d \
          else #mon -> d else #sat -> d else #sun -> d else #thu -> d else #tue -> d else #wed \
          -> d)`, where `v` is the value and each `d` the value to use in place of the atom \
          before it\n\
          repair: test the value with `match`, with one arm for each atom and one for the rest, \
          as `match v { #fri -> d, #mon -> d, #sat -> d, #sun -> d, #thu -> d, #tue -> d, \
          #wed -> d, rest -> rest }`, where `v` is the value and each `d` the value to use in \
          place of the atom of its arm"
        ]
    );
    // The loose `#ioError` passes through `if` as before; only the family needed handling.
    let fixed = repaired(&errors[0], 0);
    assert_eq!(errors_given(&fixed, &v), Vec::<String>::new());
    assert!(parses(&repaired(&errors[0], 1)));
}

#[test]
fn the_repair_for_an_atom_with_a_payload_is_the_bare_pattern() {
    let circle = Ty::set(KType::atom_with("circle", &KType::top()));
    let v = circle.union(&Ty::carrier(Carrier::Bool)).named();
    let errors = errors_given(IF, &v);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        repair(&errors[0], 0),
        "(v else #circle -> true)",
        "{}",
        errors[0]
    );
    assert_eq!(
        errors_given(&repaired(&errors[0], 0), &v),
        Vec::<String>::new()
    );
    // A pattern with a payload keeps the atom in the type (step L1.27), so it would not do.
    let with_payload = IF.replace("if v ", "if (v else #circle(r:) -> true) ");
    let left = errors_given(&with_payload, &v);
    assert_eq!(left.len(), 1, "{left:?}");
    assert!(
        left[0].starts_with("the condition of `if` does not take #circle(..), "),
        "{}",
        left[0]
    );
}
