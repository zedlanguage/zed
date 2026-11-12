//! The three forms of import, the qualifier as a name, ambiguity, and overloads across units.

use std::path::Path;

use super::{mistakes, package, use_of};

const SHAPES: &str = "\
area(r: f64) = 3.14159 * r * r;
perimeter(r: f64) = 2.0 * 3.14159 * r;
unitRadius = 1.0;
";

#[test]
fn a_selective_import_brings_in_the_names_it_lists() {
    let p = package(&[
        ("geometry/shapes.zed", SHAPES),
        (
            "main.zed",
            "import geometry.shapes.{area, unitRadius};\nbig = area(unitRadius * 10.0);\n",
        ),
    ]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    assert_eq!(
        use_of(&p, "main", "area", 1),
        ["function import geometry.shapes.{area, unitRadius}; from geometry.shapes"]
    );
    assert_eq!(
        use_of(&p, "main", "unitRadius", 1),
        ["binding import geometry.shapes.{area, unitRadius}; from geometry.shapes"]
    );
}

#[test]
fn a_name_the_unit_does_not_define_is_rejected_at_the_import() {
    let p = package(&[
        ("geometry/shapes.zed", SHAPES),
        (
            "main.zed",
            "import geometry.shapes.{area, volume};\nv = volume(2.0);\n",
        ),
    ]);
    assert_eq!(
        mistakes(&p),
        [
            "main.zed:1:1: the unit `geometry.shapes` defines no `volume`.\n  \
          [1] 1:1: the import of the unit `geometry.shapes`\n      \
          1 | import geometry.shapes.{area, volume};\n        \
          | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^"
        ]
    );
}

#[test]
fn a_qualified_import_names_the_unit_by_its_last_name_and_an_alias_by_its_own() {
    let p = package(&[
        ("geometry/shapes.zed", SHAPES),
        (
            "main.zed",
            "import geometry.shapes;\nimport geometry.shapes as g;\n\
             a = shapes.area(2.0);\nb = g.perimeter(2.0);\n",
        ),
    ]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    assert_eq!(
        use_of(&p, "main", "shapes", 2),
        ["unit import geometry.shapes; for geometry.shapes"]
    );
    assert_eq!(
        use_of(&p, "main", "shapes.area", 0),
        ["geometry.shapes.area"]
    );
    assert_eq!(
        use_of(&p, "main", "g.perimeter", 0),
        ["geometry.shapes.perimeter"]
    );
}

#[test]
fn a_qualified_member_the_unit_does_not_define_is_rejected() {
    let p = package(&[
        ("geometry/shapes.zed", SHAPES),
        (
            "main.zed",
            "import geometry.shapes;\nv = shapes.volume(2.0);\n",
        ),
    ]);
    let m = mistakes(&p);
    assert_eq!(m.len(), 1, "{m:?}");
    assert!(
        m[0].starts_with("main.zed:2:5: the unit `geometry.shapes` defines no `volume`"),
        "{m:?}"
    );
}

#[test]
fn a_qualifier_is_a_name_that_a_parameter_shadows() {
    // `shapes` here is the parameter, a record with a field `area`, never the unit.
    let p = package(&[
        ("geometry/shapes.zed", SHAPES),
        (
            "main.zed",
            "import geometry.shapes;\nfirstArea(shapes) = shapes.area;\n",
        ),
    ]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    assert_eq!(use_of(&p, "main", "shapes", 2), ["param shapes"]);
}

#[test]
fn a_qualifier_is_no_value() {
    let p = package(&[
        ("geometry/shapes.zed", SHAPES),
        ("main.zed", "import geometry.shapes;\nall = shapes;\n"),
    ]);
    assert_eq!(
        mistakes(&p),
        [
            "main.zed:2:7: `shapes` names the unit `geometry.shapes`, which is no value; a \
          definition of the unit is written `shapes.f`."
        ]
    );
}

#[test]
fn a_name_two_units_bring_in_is_ambiguous_where_it_is_used() {
    let p = package(&[
        ("metric.zed", "scale = 1000.0;\n"),
        ("imperial.zed", "scale = 1760.0;\n"),
        (
            "main.zed",
            "import metric.{scale};\nimport imperial.{scale};\nfar = 3.0 * scale;\n",
        ),
    ]);
    assert_eq!(
        mistakes(&p),
        [
            "main.zed:3:13: `scale` is ambiguous between two imports. Try `metric.scale` after \
          `import metric;` instead.\n  \
          [1] 1:1: this import brings `scale` in from the unit `metric`\n      \
          1 | import metric.{scale};\n        \
          | ^^^^^^^^^^^^^^^^^^^^^^\n  \
          [2] 2:1: this import brings `scale` in from the unit `imperial`\n      \
          2 | import imperial.{scale};\n        \
          | ^^^^^^^^^^^^^^^^^^^^^^^^"
        ]
    );
}

#[test]
fn an_unused_ambiguous_name_is_no_error_and_a_top_level_definition_shadows_it() {
    let p = package(&[
        ("metric.zed", "scale = 1000.0;\n"),
        ("imperial.zed", "scale = 1760.0;\n"),
        (
            "main.zed",
            "import metric.{scale};\nimport imperial.{scale};\nscale = 1.0;\nnear = scale;\n",
        ),
    ]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    assert_eq!(use_of(&p, "main", "scale", 3), ["binding scale = 1.0;"]);
}

#[test]
fn functions_of_one_name_from_two_units_and_the_unit_are_one_overload_set() {
    let p = package(&[
        ("circles.zed", "area(r: f64) = 3.14159 * r * r;\n"),
        ("squares.zed", "area(s: int) = s * s;\n"),
        (
            "main.zed",
            "import circles.{area};\nimport squares.{area};\n\
             area(label: String) = 0;\ntotal = area(2);\n",
        ),
    ]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    assert_eq!(
        use_of(&p, "main", "area", 3),
        [
            "function area(label: String) = 0;",
            "function import circles.{area}; from circles",
            "function import squares.{area}; from squares",
        ]
    );
}

#[test]
fn one_unit_imported_twice_brings_in_one_binder_without_ambiguity() {
    let p = package(&[
        ("geometry/shapes.zed", SHAPES),
        (
            "main.zed",
            "import geometry.shapes.{unitRadius};\nimport geometry.shapes.{unitRadius};\n\
             r = unitRadius;\n",
        ),
    ]);
    // Bringing the name in twice in one scope is a rebinding, not an ambiguity.
    let m = mistakes(&p);
    assert!(m.iter().all(|m| !m.contains("ambiguous")), "{m:?}");
}

#[test]
fn an_import_in_a_block_is_seen_in_that_block_only() {
    let p = package(&[
        ("geometry/shapes.zed", SHAPES),
        (
            "main.zed",
            "ring(r) = {\n  import geometry.shapes.{area};\n  area(r) - area(r / 2.0)\n};\n\
             disk(r) = area(r);\n",
        ),
    ]);
    assert_eq!(mistakes(&p), ["main.zed:5:11: `area` is not defined."]);
    assert_eq!(
        use_of(&p, "main", "area", 1),
        ["function import geometry.shapes.{area}; from geometry.shapes"]
    );
}

#[test]
fn a_block_import_shadows_the_top_level() {
    let p = package(&[
        ("geometry/shapes.zed", SHAPES),
        (
            "main.zed",
            "unitRadius = 2.0;\n\
             f(x) = {\n  import geometry.shapes.{unitRadius};\n  x * unitRadius\n};\n",
        ),
    ]);
    assert_eq!(mistakes(&p), Vec::<String>::new());
    assert_eq!(
        use_of(&p, "main", "unitRadius", 2),
        ["binding import geometry.shapes.{unitRadius}; from geometry.shapes"]
    );
}

#[test]
fn a_binding_after_a_block_import_of_its_name_is_a_rebinding() {
    let p = package(&[
        ("geometry/shapes.zed", SHAPES),
        (
            "main.zed",
            "f(x) = {\n  import geometry.shapes.{unitRadius};\n  unitRadius = 2.0;\n  x * unitRadius\n};\n",
        ),
    ]);
    assert_eq!(
        mistakes(&p),
        [
            "main.zed:3:3: `unitRadius` is already bound in this scope by an import.\n  \
             [1] 2:3: the import that brings `unitRadius` into this scope\n      \
             2 |   import geometry.shapes.{unitRadius};\n        \
             |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n  \
             [2] 3:3: repair: give this binding a new name\n      \
             3 |   unitRadius = 2.0;\n        \
             |   ^^^^^^^^^^^^^^^^^\n  \
             [3] 3:3: repair: move this binding into a nested block, where it shadows the first"
        ]
    );
}

#[test]
fn an_import_after_a_block_binding_of_its_name_is_a_rebinding() {
    let p = package(&[
        ("geometry/shapes.zed", SHAPES),
        (
            "main.zed",
            "f(x) = {\n  unitRadius = 2.0;\n  import geometry.shapes.{unitRadius};\n  x * unitRadius\n};\n",
        ),
    ]);
    assert_eq!(
        mistakes(&p),
        [
            "main.zed:3:3: `unitRadius` is already bound in this scope.\n  \
             [1] 2:3: the binding of `unitRadius` the import would hide\n      \
             2 |   unitRadius = 2.0;\n        \
             |   ^^^^^^^^^^^^^^^^^\n  \
             [2] 2:3: repair: give this binding a new name"
        ]
    );
}

#[test]
fn a_type_of_another_unit_is_not_yet_linked() {
    let p = package(&[
        ("geometry/shapes.zed", "struct Point { x: f64 }\n"),
        (
            "main.zed",
            "import geometry.shapes;\nf(positional p: shapes.Point) = p;\n",
        ),
    ]);
    // Without the filter `mistakes` applies, which drops the forms a later step links.
    assert_eq!(
        p.report(Path::new("")),
        [
            "geometry/shapes.zed:1:1: a struct declaration is part of the Zed language, and this \
             version of zedc does not compile it yet. Write the program without it, with the \
             forms this zedc compiles.",
            "main.zed:1:1: an import is part of the Zed language, and this version of zedc does \
             not yet tie a name an import brings in to the other unit's definition. Write the \
             definitions this file uses in it, and remove the import.",
            "main.zed:2:17: `shapes.Point`, a type of another unit, is used here, and this \
             version of zedc does not yet link a use to a definition in another unit. Write the \
             definition in this file instead, and use it from there."
        ]
    );
}
