//! The binders of L2's declarations: struct names and fields, type names and parameters,
//! methods and their receiver `this`, and the names `match` arms and patterns bind.

use super::{alone, describe, errors};

#[test]
fn a_struct_name_is_a_type_and_its_fields_are_binders_no_scope_holds() {
    let text = "struct Point { x: f64, y: f64 }\nnorm(p: Point) = p.x;\nx = 1.0;\n";
    let r = alone(text);
    assert_eq!(
        describe(text, &r, "Point", 1),
        ["struct struct Point { x: f64, y: f64 }"]
    );
    let fields: Vec<&str> = r
        .res
        .fields
        .values()
        .next()
        .unwrap()
        .clone()
        .map(|i| r.res.binders[i].name.as_str())
        .collect();
    assert_eq!(fields, ["x", "y"]);
    // A field is not in scope: the top-level `x` is no rebinding of it.
    assert_eq!(errors(text), Vec::<String>::new());
}

#[test]
fn a_field_named_twice_is_rejected_when_the_struct_is_read() {
    let text = "struct Point { x: f64, x: f64 }\n";
    let tokens = zedc::lex::lex(text).unwrap();
    let tree = zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP).unwrap();
    let e = zedc::ast::unit(text, &tokens, &tree).unwrap_err();
    assert_eq!(e.to_string(), "the field `x` is declared twice");
}

#[test]
fn a_type_parameter_is_in_scope_in_its_declaration_only() {
    let text = "type Pair(T) = (T, T);\nfirst(p: Pair(int)) = p;\nbad(x: T) = x;\n";
    let r = alone(text);
    // A binder's text is what binds it: here the declaration.
    assert_eq!(
        describe(text, &r, "T", 1),
        ["typeparam type Pair(T) = (T, T);"]
    );
    assert_eq!(
        describe(text, &r, "Pair", 1),
        ["type type Pair(T) = (T, T);"]
    );
    assert_eq!(errors(text), ["the type `T` is not defined [T]"]);
}

#[test]
fn a_method_binds_its_receiver_this_in_its_body() {
    let text = "struct Circle { r: f64 }\nCircle.area() = 3.14159 * this.r * this.r;\n";
    let r = alone(text);
    assert_eq!(
        describe(text, &r, "this", 0),
        ["receiver Circle.area() = 3.14159 * this.r * this.r;"]
    );
    assert_eq!(
        describe(text, &r, "Circle", 1),
        ["struct struct Circle { r: f64 }"]
    );
    assert_eq!(errors(text), Vec::<String>::new());
}

#[test]
fn a_method_of_a_type_no_declaration_names_is_rejected() {
    assert_eq!(
        errors("Square.area() = this.side * this.side;\n"),
        ["the type `Square` is not defined [Square.area() = this.side * this.side;]"]
    );
}

#[test]
fn a_match_arm_binds_its_names_in_its_guard_and_value_only() {
    let text = "classify(r) = match r {\n  #ok(v: n) where n > 0 -> n,\n  #ok(v: n) -> 0 - n,\n  \
                #err(e:) -> e\n};\nleak = n;\n";
    let r = alone(text);
    assert_eq!(describe(text, &r, "n", 1), ["pattern n"]);
    assert_eq!(describe(text, &r, "n", 2), ["pattern n"]);
    assert_eq!(describe(text, &r, "e", 1), ["pattern #err(e:)"]);
    assert_eq!(errors(text), ["`n` is not defined [n]"]);
    assert_eq!(r.res.patterns.len(), 3);
}

#[test]
fn a_name_pattern_that_names_a_type_is_a_type_test() {
    let text = "struct Point { x: f64 }\nisPoint(v) = match v { Point -> true, other -> other };\n";
    let r = alone(text);
    assert_eq!(
        describe(text, &r, "Point", 1),
        ["struct struct Point { x: f64 }"]
    );
    assert_eq!(describe(text, &r, "other", 1), ["pattern other"]);
}
