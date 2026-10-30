//! The atoms of a named family, `type Color = #red | #green | #blue`, are data. The marking is
//! the type's: `Ty::named` gives it, as a `type` declaration will (step L2.1), and these tests
//! read the rules from the type representation and the operator rule directly.

use zed_kernel::types::Type as KType;
use zedc::check::operator;
use zedc::check::ty::{Carrier, Ty};

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
    let (_, errors) = operator("+", &[int.clone(), color()]);
    assert_eq!(errors, ["`+` does not take (int, #blue | #green | #red)"]);
    // Loose, the same atoms flow through.
    let (out, errors) = operator("+", &[int.clone(), color().written()]);
    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(out.to_string(), "#blue | #green | #red");
    // The loose failure beside a family still flows; the family is still rejected.
    let (out, errors) = operator("+", &[int.clone(), int.union(&read_color())]);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(out.atoms().contains(&zed_kernel::Value::atom("ioError")));
}
