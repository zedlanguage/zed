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
    check(&[(
        "struct Point { x: f64, y: f64, x: int }",
        "error: the field `x` is declared twice, and each field is declared once. Remove one of \
         the two.; the first field `x` at byte 15",
    )]);
}

/// A path imported twice brings in the same fields twice, and a field brought in twice with
/// equal forms is one field, at its first place (DESIGN.md sec:introspection). Spaces around
/// the `.` of a path do not change it, so every spelling of one path is kept once, at the
/// first import's place.
#[test]
fn a_path_imported_twice_is_kept_once_however_it_is_spaced() {
    check(&[
        (
            "struct P { import geo.Datum, import geo.Datum }",
            "(struct P (import geo.Datum))",
        ),
        (
            "struct P { import a.B, z: f64, import a .B, }",
            "(struct P (import a.B) (z: f64))",
        ),
        (
            "struct P { import a.B, z: f64, import a. B, }",
            "(struct P (import a.B) (z: f64))",
        ),
        (
            "struct P { import a.B, z: f64, import a . B, }",
            "(struct P (import a.B) (z: f64))",
        ),
        (
            "struct Q { w: int, import geo .Datum, z: f64, import geo.Datum, import geo . Datum }",
            "(struct Q (w: int) (import geo.Datum) (z: f64))",
        ),
        (
            "struct P { import a.B, import a.C }",
            "(struct P (import a.B) (import a.C))",
        ),
        (
            "struct P { import a.B, import a .C, import a . b.B }",
            "(struct P (import a.B) (import a.C) (import a.b.B))",
        ),
    ]);
}

#[test]
fn a_grammar_struct_is_of_a_later_layer() {
    check(&[(
        "struct KeyVal grammar { key: JsonStr \":\" value: Json }",
        concat!(
            "error: ",
            zed_tests::not_yet!(
                "the struct declaration `struct KeyVal grammar { key: JsonStr \":\" value: Json }`"
            )
        ),
    )]);
}

#[test]
fn a_struct_law_member_is_of_a_later_layer() {
    // With no parameters the member has two children, with parameters three; neither may be
    // read as a field with a default (step L12.0 builds law members).
    check(&[
        (
            "struct Span { lo: int, hi: int, law ordered() = lo <= hi }",
            concat!(
                "error: ",
                zed_tests::not_yet!("the struct law member `law ordered() = lo <= hi`")
            ),
        ),
        (
            "struct Span { lo: int, hi: int, law within(k: int) = hi - lo <= k }",
            concat!(
                "error: ",
                zed_tests::not_yet!("the struct law member `law within(k: int) = hi - lo <= k`")
            ),
        ),
    ]);
}
