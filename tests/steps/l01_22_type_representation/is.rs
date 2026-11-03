//! `e is T` elaborates to a match whose first arm is the type and whose second is `_`, and
//! `is not` swaps the answers; a type naming a port, or bounding functions, is rejected.

use crate::l01_16_elaboration::elab;

fn term(text: &str, name: &str) -> String {
    let u = elab(text).unwrap_or_else(|e| panic!("{text}: {e:?}"));
    u.get(name).unwrap().to_string()
}

#[test]
fn is_is_a_match_on_the_type() {
    let t = term("f(x) = x is int | (int, String);", "f");
    assert!(
        t.contains("(is (| int (tuple int String))) -> true, _ -> false"),
        "{t}"
    );
    let t = term("f(x) = x is not #none;", "f");
    assert!(t.contains("(is #none) -> false, _ -> true"), "{t}");
}

#[test]
fn function_types_are_curried_one_level_per_parameter() {
    // Only a test that cannot run shows the type, so the shape is read from the kernel:
    // `(a: int, b: int) -> int` is `int -> int -> int`.
    use zed_kernel::types::Type;
    let curried = Type::exact(Type::int(), Type::exact(Type::int(), Type::int()));
    assert_eq!(curried.to_string(), "(-> int (-> int int))");
    let errs = elab("f(x) = x is ((a: int, b: int) -> int);").unwrap_err();
    assert_eq!(
        errs,
        [
            "`is` cannot test a value against a function type at run time [((a: int, b: int) -> int)]"
        ]
    );
}

#[test]
fn port_types_and_function_bounds_are_rejected() {
    assert_eq!(
        elab("f(x) = x is Lines;").unwrap_err(),
        ["`Lines` is the type of a port, and no value has it [Lines]"]
    );
    assert_eq!(
        elab("f(x) = x is (int, String ->? int);").unwrap_err(),
        ["`is` cannot test a value against a function type at run time [(int, String ->? int)]"]
    );
}

#[test]
fn a_one_tuple_and_a_morphism_type_with_two_bounds_elaborate() {
    let t = term("f(x) = x is (int,);", "f");
    assert!(t.contains("(is (tuple int)) -> true"), "{t}");
    // The guarantee lies within the permission: a morphism type, which `is` cannot test.
    assert_eq!(
        elab("f(x) = x is (#a .. #a | #b -> int);").unwrap_err(),
        ["`is` cannot test a value against a function type at run time [(#a .. #a | #b -> int)]"]
    );
    // A guarantee outside its permission promises keys the type forbids. The `is` is still an
    // error of its own.
    assert_eq!(
        elab("f(x) = x is (#a | #c .. #a | #b -> int);").unwrap_err(),
        [
            "`is` cannot test a value against a function type at run time [(#a | #c .. #a | #b -> int)]",
            "the guarantee (left of `..`) of this morphism type is not within its permission (right of `..`) [(#a | #c .. #a | #b -> int)]"
        ]
    );
}
