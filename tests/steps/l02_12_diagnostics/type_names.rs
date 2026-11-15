//! Plan row TYPEVAR-names (QUESTIONS Q23, author 2026-11-15): a type variable is exactly a name
//! of the form `[A-Z][0-9]*` (`T`, `X`, `T1`), decided when the tree is analyzed, not by the
//! lexer (DESIGN.md sec:type_language, rule 4). Any other capitalized name in a type that names
//! no type is a misspelling, rejected with the nearest type name as its menu, and never read
//! as a type variable; a name of the form declared as anything but a type variable is
//! rejected; a type variable written once in a signature and nowhere in the body is rejected
//! (DESIGN.md sec:diagnostics, the rows from "Type variable" on; L2.12's tests).

use crate::rejected;

/// Whether the program `src` loads with no error.
fn accepted(src: &str) {
    if let Err(e) = zedc::run::load(src.as_bytes()) {
        panic!("rejected:\n{src}\n{e}");
    }
}

/// Asserts that the rejection of `src` holds each of `parts`.
fn rejects(src: &str, parts: &[&str]) -> String {
    let out = rejected(src);
    for p in parts {
        assert!(
            out.contains(p),
            "{p:?} missing from the rejection of\n{src}\n{out}"
        );
    }
    out
}

#[test]
fn a_misspelled_type_gets_the_nearest_type_and_is_no_type_variable() {
    let out = rejects(
        "struct Config { a: int }\nf(c: Confg) = 0;\nmain() = 0;\n",
        &["2:6: The type `Confg` is not defined.", "repair: `Config`"],
    );
    assert!(!out.contains("type variable"), "{out}");
}

#[test]
fn a_type_variable_written_once_is_rejected_with_the_parameter_untyped() {
    rejects(
        "f(c: T) = 0;\nmain() = 0;\n",
        &[
            "1:6: The type variable `T` is written once in this signature and nowhere in its body.",
            "repair: `c`",
        ],
    );
}

#[test]
fn a_parameter_with_a_default_keeps_it_in_the_repair() {
    rejects(
        "f(c: T = 3) = 0;\nmain() = 0;\n",
        &["The type variable `T` is written once", "repair: `c = …`"],
    );
}

#[test]
fn a_type_variable_written_once_inside_a_type_gets_no_menu() {
    let out = rejects(
        "f(c: (T) -> int) = 0;\nmain() = 0;\n",
        &[
            "The type variable `T` is written once",
            "`_` in place of `T` is part of the Zed language",
        ],
    );
    assert!(!out.contains("repair:"), "{out}");
}

#[test]
fn a_type_variable_written_twice_is_accepted() {
    accepted("pair(x: T, y: T) = (x, y);\nmain() = 0;\n");
    accepted("pair(x: T, y: T) = x;\nmain() = pair(x: 1, y: 2);\n");
    accepted("f(x: (T) -> T) = 0;\nmain() = 0;\n");
}

#[test]
fn a_type_variable_the_body_reads_is_accepted() {
    // The checker reads a free `T` as `_` (row FAIL-typevar-free-in-checker), so `main` does
    // not use the result here.
    accepted("f(x: T) = { g = (y: T) -> y; g(x) };\nmain() = 0;\n");
}

#[test]
fn a_value_named_like_a_type_variable_is_rejected_with_the_lowercase_name() {
    rejects(
        "R = 1;\nmain() = 0;\n",
        &[
            "1:1: The binding target `R` has the form of a type variable.",
            "repair: `r = 1;`",
        ],
    );
    rejects(
        "R' = 2;\nmain() = 0;\n",
        &[
            "1:1: The binding target `R'` has the form of a type variable.",
            "repair: `r' = 2;`",
        ],
    );
    rejects(
        "f(T1: int) = 0;\nmain() = 0;\n",
        &[
            "1:3: The parameter `T1` has the form of a type variable.",
            "repair: `t1: int`",
        ],
    );
}

#[test]
fn a_function_named_like_a_type_variable_is_rejected() {
    rejects(
        "F(x: int) = x;\nmain() = 0;\n",
        &[
            "The function `F` has the form of a type variable.",
            "repair: `f(x: int) = x;`",
        ],
    );
}

#[test]
fn the_lowercase_name_in_use_is_not_offered() {
    let out = rejects(
        "r = 0;\nR = 1;\nmain() = 0;\n",
        &[
            "2:1: The binding target `R` has the form of a type variable.",
            "repair: rename the binding target; `r` already names something in scope",
        ],
    );
    assert!(!out.contains("repair: `r = 1;`"), "{out}");
}

#[test]
fn a_struct_named_like_a_type_variable_is_rejected_and_its_name_stays_a_variable() {
    let out = rejects(
        "struct T2 { a: int }\ng(x: T2, y: T2) = x;\nmain() = 0;\n",
        &[
            "1:1: The struct `T2` has the form of a type variable.",
            "repair: give the struct a longer name",
        ],
    );
    // `T2` in `g` is a type variable, written twice, not a use of the struct.
    assert!(!out.contains("2:"), "{out}");
}

#[test]
fn names_near_the_form_are_types_or_misspellings() {
    // `Tx` and `AB` are not of the form: they name no type, so each is unknown, and no type
    // name is one slip from either, so neither gets a menu.
    for n in ["Tx", "AB"] {
        let out = rejects(
            &format!("f(c: {n}) = 0;\nmain() = 0;\n"),
            &[&format!("The type `{n}` is not defined.")],
        );
        assert!(!out.contains("repair:"), "{out}");
    }
    // `T01` is of the form: a capital letter followed only by digits.
    accepted("pair(x: T01, y: T01) = x;\nmain() = 0;\n");
}

#[test]
fn a_struct_field_names_no_type_variable_and_is_not_named_like_one() {
    rejects(
        "struct Box { a: T }\nmain() = 0;\n",
        &[
            "1:17: The type variable `T` stands in a field of a struct that declares no type parameter `T`.",
        ],
    );
    rejects(
        "struct Box { A: int }\nmain() = 0;\n",
        &[
            "1:14: The field `A` has the form of a type variable.",
            "repair: `a: int`",
        ],
    );
}

#[test]
fn a_misspelling_written_many_times_is_reported_at_each() {
    let out = rejected("f(a: Confg, b: Confg) = 0;\nmain() = 0;\n");
    assert_eq!(
        out.matches("The type `Confg` is not defined.").count(),
        2,
        "{out}"
    );
}

/// DESIGN.md step L1.29e's examples, at type names: each kind of slip offers `Config`.
#[test]
fn each_kind_of_slip_offers_the_type() {
    for n in ["Confg", "Configg", "Cinfig", "Cofnig"] {
        rejects(
            &format!("struct Config {{ a: int }}\nf(c: {n}) = 0;\nmain() = 0;\n"),
            &[
                &format!("The type `{n}` is not defined."),
                "repair: `Config`",
            ],
        );
    }
}

#[test]
fn a_name_equal_once_case_and_underscores_are_folded_is_near() {
    rejects(
        "struct MyConfig { a: int }\nf(c: My_config) = 0;\nmain() = 0;\n",
        &["The type `My_config` is not defined.", "repair: `MyConfig`"],
    );
}

#[test]
fn of_two_near_types_the_first_in_name_order_is_offered() {
    let out = rejects(
        "struct Cat { a: int }\nstruct Bat { a: int }\nf(c: Hat) = 0;\nmain() = 0;\n",
        &["The type `Hat` is not defined.", "repair: `Bat`"],
    );
    assert!(!out.contains("repair: `Cat`"), "{out}");
}

#[test]
fn a_type_two_slips_away_is_not_offered() {
    let out = rejects(
        "struct Config { a: int }\nf(c: Cnfgi) = 0;\nmain() = 0;\n",
        &["The type `Cnfgi` is not defined."],
    );
    assert!(!out.contains("repair:"), "{out}");
}
