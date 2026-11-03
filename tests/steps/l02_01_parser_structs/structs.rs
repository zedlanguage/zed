//! `struct` declarations: typed fields, defaults, and `import` fields that copy another
//! struct's fields in.

use super::check;

#[test]
fn a_struct_lists_its_typed_fields() {
    check(&[
        (
            "struct Point { x: f64, y: f64 }",
            "(struct Point (x: f64) (y: f64))",
        ),
        (
            "struct Reading { t: int, sensor: String, v: int, }",
            "(struct Reading (t: int) (sensor: String) (v: int))",
        ),
        ("struct Unit {}", "(struct Unit)"),
    ]);
}

#[test]
fn a_field_may_have_a_default() {
    check(&[(
        "struct Config { port: int = 8080, host: String = \"localhost\", verbose: bool }",
        "(struct Config (port: int = 8080) (host: String = (str \"localhost\")) (verbose: bool))",
    )]);
}

#[test]
fn an_import_field_names_a_struct_by_its_path() {
    check(&[(
        "struct Point3 { import Point, import geo.Datum, z: f64 = 0.0 }",
        "(struct Point3 (import Point) (import geo.Datum) (z: f64 = 0.0))",
    )]);
}

#[test]
fn a_field_type_is_any_type_of_layer_2() {
    check(&[(
        "struct Node { label: String, kids: Tree(int), pos: { x: f64, y: f64 }, \
         next: #end | #more(at: int) }",
        "(struct Node (label: String) (kids: (Tree int)) (pos: (record (x: f64) (y: f64))) \
         (next: (| #end (#more (at: int)))))",
    )]);
}

#[test]
fn a_field_declared_twice_is_an_error() {
    check(&[
        (
            "struct Point { x: f64, y: f64, x: int }",
            "error: the field `x` is declared twice; the first field `x` at byte 15",
        ),
        (
            "struct P { import geo.Datum, import geo.Datum }",
            "error: the import `geo.Datum` is written twice; the first import `geo.Datum` at byte 18",
        ),
    ]);
}

#[test]
fn a_grammar_struct_is_of_a_later_layer() {
    check(&[(
        "struct KeyVal grammar { key: JsonStr \":\" value: Json }",
        "error: this form (Struct) is built from layer L20",
    )]);
}
