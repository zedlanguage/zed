//! Row FAIL-default-literal-sum-carrier: a default made of integer literals joined by an
//! operator takes the carrier of its parameter's declared type, as a lone literal does
//! (DESIGN.md L1.26a: an integer literal "is that integer in whichever numeric carrier its use
//! needs", and the use is the parameter). `g(x: int = 1 + 2)` was refused as "the default of
//! `x` is int | f32 | f64 | rat, not int", with a repair that named `int` twice.

use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{Resolved, type_errors};

#[test]
fn a_default_of_joined_integer_literals_takes_its_parameters_carrier() {
    for (text, want) in [
        ("g(x: int = 1 + 2) = x;\nr = g();\n", "3"),
        ("g(x: int[0..=3] = 1 + 2) = x;\nr = g();\n", "3"),
        ("g(x: f64 = 1 + 2) = x;\nr = g();\n", "3.0"),
        ("g(x: rat = 1 + 2) = x;\nr = g();\n", "3r"),
        ("g(x: int = 2 * 3 - 1) = x;\nr = g();\n", "5"),
        ("g(x: f64 = -(1 + 2)) = x;\nr = g();\n", "-3.0"),
    ] {
        assert_eq!(type_errors(text), Vec::<String>::new(), "{text}");
        assert_eq!(value(text, "r"), want, "{text}");
    }
    // A `/` whose value is no int stays refused at `int`, and is a `rat` at `rat`.
    let errors = type_errors("g(x: int = 1 / 2) = x;\nr = g();\n");
    assert!(!errors.is_empty(), "{errors:#?}");
    let text = "g(x: rat = 1 / 2) = x;\nr = g();\n";
    assert_eq!(type_errors(text), Vec::<String>::new(), "{text}");
    assert_eq!(value(text, "r"), "1r/2r", "{text}");
    // Out of range it is refused for the range alone.
    let errors = type_errors("g(x: int[0..=3] = 2 + 2) = x;\nmain = g();\n");
    assert_eq!(errors.len(), 1, "{errors:#?}");
    assert!(errors[0].contains("`g()` leaves out `x`"), "{errors:#?}");
}

#[test]
fn a_default_of_another_type_names_each_member_once_in_its_repair() {
    // A default of a type the parameter does not hold is still refused, and the repair's
    // union names each member once.
    for text in [
        "g(x: int = 1.5f64 + 1) = x;\nr = g();\n",
        "g(y: bool, x: int = if y { 1 } else { 1.5f64 }) = x;\nr = g(y: true);\n",
        "g(y: bool, x: int = if y { 1 + 2 } else { 1.5f64 }) = x;\nr = g(y: true);\n",
        // The default's type holds `int` itself, which the repair's union names once.
        "g(y: bool, z: int, x: int = if y { z } else { 1.5f64 }) = x;\nr = g(y: true, z: 1);\n",
    ] {
        let errors = Resolved::new(text).check().errors;
        assert_eq!(errors.len(), 1, "{text}\n{errors:#?}");
        let e = &errors[0];
        assert!(
            e.message.contains("the default of `x` is"),
            "{text}\n{e:#?}"
        );
        // The headline, the menu and each note.
        let texts = [e.message.as_str(), e.menu.as_str()]
            .into_iter()
            .chain(e.notes.iter().map(|n| n.text.as_str()));
        let unions: Vec<&str> = texts
            .flat_map(|t| t.split("as `x: ").skip(1))
            .map(|r| r.split_once('`').unwrap_or_else(|| panic!("{e:#?}")).0)
            .collect();
        assert!(!unions.is_empty(), "{text}\n{e:#?}");
        for union in unions {
            let members: Vec<&str> = union.split(" | ").collect();
            let mut once = members.clone();
            zed_collections::sorted::sort_dedup(&mut once);
            assert_eq!(once.len(), members.len(), "{text}\n{e:#?}");
        }
    }
}
