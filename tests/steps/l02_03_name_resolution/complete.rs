//! The cases COMPLETENESS.md lists that the other files of this group leave out: a unit whose
//! text does not lex, imported or named as the prelude; each file of a package the system will
//! not give zedc; and the manifest that does not lex or parse, or binds more than one name.

use zedc::query::Db;
use zedc::unit::{Dir, load, manifest};

use super::source::package_dir;
use super::{mistakes, package};

/// How zedc says a string ends at the end of its line.
const OPEN_STRING: &str = "this `\"` string reaches the end of its line without its closing \
    `\"`, and a `\"` string ends on its line. Close it on this line, or write a string over \
    several lines as `\"\"\"`.";

#[test]
fn a_unit_that_does_not_lex_reports_its_own_error_and_its_importer_none() {
    let p = package(&[
        ("broken.zed", "x = \"abc\n"),
        ("main.zed", "import broken.{x};\ny = x;\n"),
    ]);
    assert_eq!(mistakes(&p), [format!("broken.zed:1:5: {OPEN_STRING}")]);
}

#[test]
fn a_prelude_unit_that_does_not_lex_reports_its_own_error_only() {
    let p = package(&[
        ("zed.manifest", "prelude = \"pre\";\n"),
        ("pre.zed", "x = \"abc\n"),
        ("main.zed", "y = 1;\n"),
    ]);
    assert_eq!(mistakes(&p), [format!("pre.zed:1:5: {OPEN_STRING}")]);
}

#[test]
fn a_file_the_system_will_not_give_is_reported_with_the_repair_wherever_it_is_read() {
    // A directory where a file is looked for: reading it fails, as a file without read
    // permission does, with no line and column.
    let cannot = |file: &str| {
        format!(
            "{file}: zedc could not read this file: Is a directory. Check the path and that you \
             may read the file."
        )
    };
    let main: &[(&str, &[u8])] = &[("main.zed", b"y = 1;\n")];
    for (name, files, expected) in [
        (
            "import",
            vec![
                ("pricing.zed/x", &b"x"[..]),
                ("main.zed", b"import pricing.{net};\ny = net;\n"),
            ],
            vec![format!(
                "main.zed:1:1: the unit `pricing` cannot be imported: {}",
                cannot("pricing.zed")
            )],
        ),
        (
            "root",
            vec![("main.zed/x", &b"x"[..])],
            vec![cannot("main.zed")],
        ),
        (
            "manifest",
            [&[("zed.manifest/x", &b"x"[..])][..], main].concat(),
            vec![cannot("zed.manifest")],
        ),
        (
            "pins",
            [&[("zed.pins/x", &b"x"[..])][..], main].concat(),
            vec![cannot("zed.pins")],
        ),
        (
            "prelude",
            [
                &[
                    ("zed.manifest", &b"prelude = \"pre\";\n"[..]),
                    ("pre.zed/x", b"x"),
                ][..],
                main,
            ]
            .concat(),
            vec![format!(
                "zed.manifest:1:11: the prelude unit `pre` is missing: {}",
                cannot("pre.zed")
            )],
        ),
    ] {
        let d = package_dir(&format!("complete_unreadable_{name}"), &files);
        let p = load(&mut Db::new(), &Dir(d), &["main"]);
        assert_eq!(mistakes(&p), expected, "{name}");
    }
}

#[test]
fn a_manifest_that_does_not_lex_or_parse_or_binds_two_names_is_refused() {
    for (text, expected) in [
        (
            "prelude = \"std",
            "this string is not closed before the end of the file. Write the closing `\"` \
             where its text ends. [\"std]",
        ),
        ("prelude = ;\n", "Syntax error at `;`. [;]"),
        ("prelude = \"a\", \"b\";\n", "Syntax error at `,`. [,]"),
        (
            "a, b = \"x\";\n",
            "a manifest entry binds one name to a string literal, as \
             `prelude = \"std.prelude\";` [a, b = \"x\";]",
        ),
        (
            "x.y = \"z\";\n",
            "a manifest holds only bindings of string literals, as \
             `prelude = \"std.prelude\";` [x.y = \"z\";]",
        ),
    ] {
        let refused: Vec<String> = manifest(text)
            .unwrap_err()
            .iter()
            .map(|e| format!("{} [{}]", e.message, &text[e.span.start..e.span.end]))
            .collect();
        assert_eq!(refused, [expected], "{text}");
    }
    // The package stops at a refused manifest, as at one that cannot be read.
    let p = package(&[("zed.manifest", "prelude = ;\n"), ("main.zed", "y = 1;\n")]);
    let m = mistakes(&p);
    assert_eq!(m.len(), 1, "{m:?}");
    assert_eq!(
        m[0].lines().next(),
        Some("zed.manifest:1:11: Syntax error at `;`.")
    );
}

/// The first line of each problem of the package `fs`, but for the forms of later steps.
fn heads(fs: &[(&str, &str)]) -> Vec<String> {
    mistakes(&package(fs))
        .iter()
        .map(|m| m.lines().next().unwrap().to_string())
        .collect()
}

#[test]
fn a_qualified_type_names_a_type_of_an_imported_unit_or_is_refused() {
    // DESIGN.md sec:units: "Qualified names skip to the named unit", and a qualifier is a name
    // an import binds. A member of the unit that is no type, a member it lacks, a dotted head
    // that is no qualifier and a type of two qualifiers are each refused at the type.
    let shapes = ("shapes.zed", "origin = 1;\n");
    let cases: [(&[(&str, &str)], &str); 6] = [
        (
            &[
                shapes,
                (
                    "main.zed",
                    "import shapes;\nf(positional p: shapes.origin) = p;\n",
                ),
            ],
            "main.zed:2:17: `shapes.origin` stands where a type is written, and the unit \
             `shapes` declares `origin` as the binding target, which is no type.",
        ),
        (
            &[
                shapes,
                (
                    "main.zed",
                    "import shapes;\nf(positional p: shapes.Point) = p;\n",
                ),
            ],
            "main.zed:2:17: the unit `shapes` defines no `Point`.",
        ),
        (
            &[("main.zed", "f(positional p: a.b.Point) = p;\n")],
            "main.zed:1:17: the type `a.b.Point` has more than one qualifier; a qualified type \
             is a qualifier and a type, as `shapes.Point` after `import geometry.shapes;`.",
        ),
        (
            &[("main.zed", "a = 1;\nf(positional p: a.Point) = p;\n")],
            "main.zed:2:17: `a` in the type `a.Point` names the binding target `a`, not a unit \
             imported as `import a.a;`.",
        ),
        (
            &[("main.zed", "f(positional p: a.Point) = p;\n")],
            "main.zed:1:17: `a` in the type `a.Point` names no unit: no import in scope binds \
             the qualifier `a`.",
        ),
        (
            &[("main.zed", "n = 1;\nf(positional p: n) = p;\n")],
            "main.zed:2:17: `n` stands where a type is written, and names the binding target \
             `n`, which is no type.",
        ),
    ];
    for (fs, expected) in cases {
        assert_eq!(heads(fs), [expected], "{fs:?}");
    }
}

#[test]
fn a_prelude_unit_name_that_is_no_type_or_is_broken_at_a_type() {
    let manifest = ("zed.manifest", "prelude = \"pre\";\n");
    assert_eq!(
        heads(&[
            manifest,
            ("pre.zed", "origin = 1;\n"),
            ("main.zed", "f(positional p: origin) = p;\n"),
        ]),
        [
            "main.zed:1:17: `origin` stands where a type is written, and the prelude unit `pre` \
          declares `origin` as the binding target, which is no type."
        ]
    );
    // A use of the name a broken declaration of the prelude unit binds is not checked, at a
    // type or a value (step L1.29d); a name it does not bind still is.
    assert_eq!(
        heads(&[
            manifest,
            ("pre.zed", "origin = ;\n"),
            (
                "main.zed",
                "f(positional p: origin) = p;\ny = origin;\ng(positional p: Point) = p;\n"
            ),
        ]),
        [
            "main.zed:3:17: The type `Point` is not defined.",
            "pre.zed:1:10: Syntax error at `;`.",
        ]
    );
}
