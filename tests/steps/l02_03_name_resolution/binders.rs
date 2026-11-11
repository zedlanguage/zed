//! The binders of L2's declarations: struct names and fields, type names and parameters,
//! methods and their receiver `this`, and the names `match` arms and patterns bind.

use super::{STR_TYPES_PENDING, alone, describe, errors};

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
    assert_eq!(
        e.to_string(),
        "the field `x` is declared twice, and each field is declared once. Remove one of the two."
    );
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
    assert_eq!(
        errors(text),
        [
            "the type `T` is not defined: no type in scope has this name, and the prelude has none. Correct the name if it is misspelled, or write a type of the prelude, such as `int` or `String`. [T]"
        ]
    );
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
        [
            "the type `Square` is not defined: no type in scope has this name, and the prelude has none. Correct the name if it is misspelled, or write a type of the prelude, such as `int` or `String`. [Square.area() = this.side * this.side;]"
        ]
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
    assert_eq!(
        errors(text),
        [
            "`n` is not defined: no definition, parameter or binding in scope has this name, and the prelude has none. Define `n`, or correct the name if it is misspelled. [n]"
        ]
    );
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

/// The corpus's UTF-8 decoder writes each decoded code point with `scalar` (step L1.39c) in a
/// `match` arm, which resolution now walks: every name in it resolves, to the arm's binder or
/// to the prelude.
#[test]
fn the_utf8_corpus_program_resolves_the_code_points_its_match_arms_write() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../zed/corpus/08-utf8-percent.zed"
    );
    let text = std::fs::read_to_string(path).unwrap();
    let r = alone(&text);
    // The decoder's state holds a `Utf8String`, pending STR-types (see `STR_TYPES_PENDING`).
    let errors = errors(&text);
    assert!(
        errors.len() == 1 && errors[0].starts_with(STR_TYPES_PENDING),
        "{errors:?}"
    );
    assert_eq!(describe(&text, &r, "scalar", 0), ["prelude scalar"]);
    assert_eq!(describe(&text, &r, "b", 2), ["pattern #byte(b:)"]);
    assert_eq!(describe(&text, &r, "scalar", 1), ["prelude scalar"]);
}

/// A tuple-destructuring parameter binds its names in the lambda's body, as a `match` arm's
/// pattern binds its own, though both are elaborated from step L2.4: a name in the body that
/// nothing binds is not defined. The corpus's maximum prefix sum folds with such a lambda.
#[test]
fn a_tuple_destructuring_parameter_binds_its_names_in_the_body() {
    let text = "f = ((s, b), x) -> (s + x, max(b, s + x), total);\nleak = s;\n";
    let r = alone(text);
    assert_eq!(describe(text, &r, "s", 1), ["param s"]);
    assert_eq!(describe(text, &r, "b", 1), ["param b"]);
    assert_eq!(describe(text, &r, "x", 1), ["param x"]);
    assert_eq!(describe(text, &r, "max", 0), ["prelude max"]);
    assert_eq!(
        errors(text),
        [
            "`total` is not defined: no definition, parameter or binding in scope has this name, and the prelude has none. Define `total`, or correct the name if it is misspelled. [total]",
            "`s` is not defined: no definition, parameter or binding in scope has this name, and the prelude has none. Define `s`, or correct the name if it is misspelled. [s]"
        ]
    );
    assert_eq!(
        errors("f = ((a, a)) -> a;\n"),
        [
            "`a` is already bound in this scope, and a scope binds each name once [a]; the first binding of `a` [a]; repair: give \
             this binding a new name [a]; repair: move this binding into a nested block, where \
             it shadows the first [a]"
        ]
    );
    let text =
        std::fs::read_to_string(zed_tests::oracle::corpus_dir().join("05-max-prefix-sum.zed"))
            .unwrap();
    let r = alone(&text);
    // Occurrence 0 is in the header comment and 2 inside `><`, which step L3.2 compiles.
    assert_eq!(describe(&text, &r, "max", 3), ["prelude max"]);
    assert_eq!(errors(&text), Vec::<String>::new());
}
