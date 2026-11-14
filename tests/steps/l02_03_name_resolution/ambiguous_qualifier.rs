//! The repairs of an ambiguous qualifier or alias (row FAIL-ambiguous-qualifier-repair, found by
//! TEST-complete-names). DESIGN.md sec:units, "Ambiguity is rejected, not ranked": uses of a
//! name two imports bring in are an error "with both origins named and the repairs
//! enumerated"; and "A qualifier is itself a name — `import geometry.shapes;` introduces
//! `shapes` (and `as g` introduces `g`) into the importing scope as a unit name, subject to
//! this same order". So two imports whose qualifiers (or aliases) are one name make a use of it
//! ambiguous, and the repair renames one of them with the aliased form
//! `import geometry.shapes as g;`. The repair of a name a selective import brings in, reading
//! it through its unit's qualifier, would here name a member the unit does not define
//! (`shapes.shapes` after `import a.shapes;`), which zedc offered before.

use std::path::Path;

use super::{mistakes, package};

/// The units every case imports from: two of one last name, `shapes`, and one other.
const UNITS: [(&str, &str); 4] = [
    ("a/shapes.zed", "o = 1;\n"),
    ("b/shapes.zed", "o = 1;\n"),
    ("b/forms.zed", "o = 1;\n"),
    ("c.zed", "shapes = 2;\n"),
];

/// The headline of each problem of the package of `UNITS` and the unit `main`.
fn headlines(main: &str) -> Vec<String> {
    let mut fs = UNITS.to_vec();
    fs.push(("main.zed", main));
    mistakes(&package(&fs))
        .iter()
        .map(|m| m.lines().next().unwrap_or_default().to_string())
        .collect()
}

#[test]
fn an_ambiguous_qualifier_is_offered_an_alias_not_a_member() {
    let units = [
        ("a/shapes.zed", "o = 1;\n"),
        ("b/shapes.zed", "o = 1;\n"),
        ("b/forms.zed", "o = 1;\n"),
    ];
    let mut wrong = Vec::new();
    for (main, member) in [
        // A qualifier at a type, at a value, and an alias.
        (
            "import a.shapes;\nimport b.shapes;\nf(positional p: shapes.T) = p;\n",
            "`shapes.shapes`",
        ),
        (
            "import a.shapes;\nimport b.shapes;\ny = shapes.o;\n",
            "`shapes.shapes`",
        ),
        (
            "import a.shapes as s;\nimport b.forms as s;\ny = s.o;\n",
            "`shapes.s`",
        ),
    ] {
        let mut fs = units.to_vec();
        fs.push(("main.zed", main));
        let report = package(&fs).report(Path::new(""));
        let Some(ambiguous) = report.iter().find(|m| m.contains("is ambiguous")) else {
            wrong.push(format!("{main}: no ambiguity reported in {report:?}"));
            continue;
        };
        if ambiguous.contains(member) || !ambiguous.contains(" as ") {
            wrong.push(format!("{main}:\n{ambiguous}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n\n"));
}

#[test]
fn two_qualifiers_of_one_last_name_are_each_offered_their_whole_path() {
    let want = "main.zed:3:5: `shapes` is ambiguous between two imports. Try `import a.shapes \
                as a_shapes;` or `import b.shapes as b_shapes;` instead.";
    assert_eq!(
        headlines("import a.shapes;\nimport b.shapes;\ny = shapes.o;\n"),
        [want]
    );
    // At a type, the same repairs.
    assert_eq!(
        headlines("import a.shapes;\nimport b.shapes;\nf(positional p: shapes.T) = p;\n"),
        [
            "main.zed:3:17: `shapes` is ambiguous between two imports. Try `import a.shapes as \
          a_shapes;` or `import b.shapes as b_shapes;` instead."
        ]
    );
}

#[test]
fn two_aliases_are_each_offered_the_last_name_of_their_unit() {
    assert_eq!(
        headlines("import a.shapes as s;\nimport b.forms as s;\ny = s.o;\n"),
        [
            "main.zed:3:5: `s` is ambiguous between two imports. Try `import a.shapes as \
          shapes;` or `import b.forms as forms;` instead."
        ]
    );
}

#[test]
fn a_new_name_the_program_uses_is_passed_over() {
    // `a_shapes` is taken by a definition, so the first import is offered `a_shapes2`.
    assert_eq!(
        headlines("import a.shapes;\nimport b.shapes;\na_shapes = 3;\ny = shapes.o;\n"),
        [
            "main.zed:4:5: `shapes` is ambiguous between two imports. Try `import a.shapes as \
          a_shapes2;` or `import b.shapes as b_shapes;` instead."
        ]
    );
    // The last name `forms` is taken by an import, so its whole path is offered.
    assert_eq!(
        headlines("import a.shapes as s;\nimport b.forms as s;\nimport b.forms;\ny = s.o;\n"),
        [
            "main.zed:4:5: `s` is ambiguous between two imports. Try `import a.shapes as \
          shapes;` or `import b.forms as b_forms;` instead."
        ]
    );
}

#[test]
fn a_qualifier_and_a_selective_import_each_get_their_own_repair() {
    assert_eq!(
        headlines("import a.shapes;\nimport c.{shapes};\ny = shapes;\n"),
        [
            "main.zed:3:5: `shapes` is ambiguous between two imports. Try `import a.shapes as \
          a_shapes;` or `c.shapes` after `import c;` instead."
        ]
    );
}

#[test]
fn following_a_repair_resolves_the_program() {
    for main in [
        "import a.shapes as a_shapes;\nimport b.shapes;\ny = shapes.o;\n",
        "import a.shapes;\nimport b.shapes as b_shapes;\ny = shapes.o;\n",
        "import a.shapes;\nimport b.forms as forms;\ny = forms.o;\n",
        "import a.shapes as shapes;\nimport b.forms as s;\ny = s.o;\n",
    ] {
        assert_eq!(headlines(main), Vec::<String>::new(), "{main}");
    }
}
