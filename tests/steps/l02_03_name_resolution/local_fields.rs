//! A struct's `local` field (DESIGN.md sec:units, author A80 answer B): `struct Money { local
//! cents: int[0..] }` exports `Money` and keeps the name `cents` to the unit `money`. Inside it
//! the field is an ordinary field; outside it a construction or a pattern that names the field
//! is rejected, naming the field, the struct and the unit. The read `total.cents` and a
//! structural match need the value's type, so plan row LOCAL-fields-typed rejects them.

use super::{errors, mistakes, package};

/// The unit `money`: one local field and one exported field, built and read inside the unit.
const MONEY: &str = "struct Money { local cents: int[0..], n: int }\n\
                     dollars(positional d: int[0..]) = Money(cents: d * 100, n: 0);\n\
                     amount(positional m: Money) = match m { Money(cents: c, n:) -> c + n };\n";

#[test]
fn a_local_field_is_an_ordinary_field_inside_its_unit() {
    let p = package(&[
        ("money.zed", MONEY),
        ("main.zed", "import money.{dollars};\ntotal = dollars(3);\n"),
    ]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    let money = p.unit("money").unwrap().resolved.as_ref().unwrap();
    assert_eq!(money.res.exports.local_fields("Money"), ["cents"]);
    assert_eq!(
        money.res.exports.local_fields("dollars"),
        Vec::<&str>::new()
    );
}

#[test]
fn a_construction_outside_the_unit_that_names_a_local_field_is_rejected() {
    let p = package(&[
        ("money.zed", MONEY),
        (
            "main.zed",
            "import money.{Money};\nbad = Money(cents: 5, n: 1);\nfine = Money(n: 1);\n",
        ),
    ]);
    assert_eq!(
        mistakes(&p),
        [
            "main.zed:2:7: Invalid construction `Money(cents: 5, n: 1)`: the field `cents` of \
             `Money` is declared `local` in the unit `money`, so no other unit names it.\n  \
             [1] 1:1: the import of the unit `money`\n      \
             1 | import money.{Money};\n        \
             | ^^^^^^^^^^^^^^^^^^^^^\n  \
             [2] 2:7: repair: make the `Money` by a call of a function of the unit `money`, or \
             declare `cents` without `local` there\n      \
             2 | bad = Money(cents: 5, n: 1);\n        \
             |       ^^^^^^^^^^^^^^^^^^^^^"
        ]
    );
}

#[test]
fn a_qualified_construction_outside_the_unit_is_rejected_too() {
    let p = package(&[
        ("money.zed", MONEY),
        (
            "main.zed",
            "import money;\nbad = money.Money(cents: 5, n: 1);\n",
        ),
    ]);
    let m = mistakes(&p);
    assert_eq!(m.len(), 1, "{m:?}");
    assert!(
        m[0].starts_with(
            "main.zed:2:7: Invalid construction `money.Money(cents: 5, n: 1)`: the field `cents` \
             of `Money` is declared `local` in the unit `money`, so no other unit names it."
        ),
        "{m:?}"
    );
}

#[test]
fn a_pattern_outside_the_unit_that_binds_a_local_field_is_rejected() {
    let p = package(&[
        ("money.zed", MONEY),
        (
            "main.zed",
            "import money.{Money};\n\
             f(m: Money) = match m { Money(cents:) -> cents };\n\
             g(m: Money) = match m { Money(n:) -> n };\n",
        ),
    ]);
    let m = mistakes(&p);
    assert_eq!(m.len(), 1, "{m:?}");
    assert!(
        m[0].starts_with(
            "main.zed:2:25: Invalid pattern `Money(cents:)`: the field `cents` of `Money` is \
             declared `local` in the unit `money`, so no other unit names it."
        ),
        "{m:?}"
    );
}

#[test]
fn a_struct_of_the_importer_with_the_same_name_is_its_own() {
    let p = package(&[
        ("money.zed", MONEY),
        (
            "main.zed",
            "import money.{dollars};\nstruct Money { cents: int }\nmine = Money(cents: 5);\n",
        ),
    ]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
}

#[test]
fn a_local_field_changes_the_exports_an_importer_reads() {
    let exports = |text: &str| {
        let p = package(&[("money.zed", text), ("main.zed", "import money.{Money};\n")]);
        let r = p.unit("money").unwrap().resolved.as_ref().unwrap();
        r.res.exports.bytes()
    };
    assert_ne!(
        exports("struct Money { local cents: int }\n"),
        exports("struct Money { cents: int }\n")
    );
}

#[test]
fn a_local_field_of_a_struct_in_a_block_is_rejected() {
    assert_eq!(
        errors("f(x) = {\n  struct Pair { local a: int }\n  x\n};\n"),
        [
            "`local` keeps a field from other units, and a struct declared in a block is seen \
             by no other unit already, so `local` marks a field only of a struct at a unit's \
             top level. Remove the `local`. [local a: int]"
        ]
    );
}

#[test]
fn a_local_field_prints_as_written() {
    let text = "struct Money { local cents: int[0..], n: int = 0 }\n";
    let tokens = zedc::lex::lex(text).unwrap();
    let tree = zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP).unwrap();
    let stmts = zedc::ast::unit(text, &tokens, &tree).unwrap();
    assert_eq!(zedc::format::format(text, &tokens, &stmts), text);
}
