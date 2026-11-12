//! The manifest: its one entry `prelude`, the prelude unit every other unit sees, and what the
//! manifest may not hold.

use super::{mistakes, package, use_of};
use zedc::unit::{Manifest, manifest};

/// The manifest's errors, as `message [text]`.
fn refused(text: &str) -> Vec<String> {
    manifest(text)
        .unwrap_err()
        .iter()
        .map(|e| {
            let mut out = format!("{} [{}]", e.message, &text[e.span.start..e.span.end]);
            for n in &e.notes {
                out += &format!("; {} [{}]", n.text, &text[n.span.start..n.span.end]);
            }
            out
        })
        .collect()
}

#[test]
fn a_manifest_names_the_prelude_unit_or_nothing() {
    let m = manifest("prelude = \"std.prelude\";\n").unwrap();
    assert_eq!(m.prelude.map(|p| p.0), Some("std.prelude".to_string()));
    assert_eq!(manifest("// no prelude\n").unwrap(), Manifest::default());
}

#[test]
fn a_manifest_holds_only_its_entries_each_once_bound_to_a_plain_string() {
    assert_eq!(
        refused("prelude = \"std.prelude\";\nprelude = \"std.base\";\n"),
        [
            "the manifest binds `prelude` twice, and a manifest binds each name once. Remove one of the two. [prelude]; `prelude` is first bound here [prelude]"
        ]
    );
    assert_eq!(
        refused("version = \"1.0\";\n"),
        [
            "the manifest has no entry `version`: its one entry is `prelude`, the path of the \
          package's prelude unit [version]"
        ]
    );
    assert_eq!(
        refused("prelude = 3;\n"),
        [
            "the manifest entry `prelude` is bound to a string literal with no hole, as \
          `prelude = \"std.prelude\";` [3]"
        ]
    );
    assert_eq!(
        refused("base = \"std\";\nprelude = \"${base}.prelude\";\n"),
        [
            "the manifest has no entry `base`: its one entry is `prelude`, the path of the \
             package's prelude unit [base]",
            "the manifest entry `prelude` is bound to a string literal with no hole, as \
             `prelude = \"std.prelude\";` [\"${base}.prelude\"]",
        ]
    );
    assert_eq!(
        refused("prelude = \"std/prelude\";\n"),
        [
            "the prelude `std/prelude` is not a unit path: `std/prelude` is not a name \
          [\"std/prelude\"]"
        ]
    );
    assert_eq!(
        refused("f(x) = x;\n"),
        [
            "a manifest holds only bindings of string literals, as `prelude = \"std.prelude\";` \
          [f(x) = x;]"
        ]
    );
}

#[test]
fn every_unit_but_the_prelude_and_what_it_reaches_sees_the_prelude_unit() {
    let p = package(&[
        ("zed.manifest", "prelude = \"std.prelude\";\n"),
        (
            "std/prelude.zed",
            "import std.math.{square};\ndouble(x) = x + x;\n",
        ),
        (
            "std/math.zed",
            "square(x) = x * x;\nhalf(x) = double(x) / 4;\n",
        ),
        ("main.zed", "four = double(2);\n"),
    ]);
    // `main` sees the prelude's `double`; `std.math`, which the prelude reaches, does not.
    assert_eq!(use_of(&p, "main", "double", 0), ["std.prelude.double"]);
    assert_eq!(
        mistakes(&p),
        ["std/math.zed:2:11: `double` is not defined."]
    );
}

#[test]
fn a_prelude_unit_with_no_file_is_reported_at_the_manifest() {
    let p = package(&[
        ("zed.manifest", "prelude = \"std.prelude\";\n"),
        ("main.zed", "four = 2 + 2;\n"),
    ]);
    assert_eq!(
        mistakes(&p),
        [
            "zed.manifest:1:11: the prelude unit `std.prelude` is missing: there is no file \
          `std/prelude.zed` under the root."
        ]
    );
}

#[test]
fn a_manifest_that_is_refused_stops_the_package() {
    let p = package(&[("zed.manifest", "prelude = 1;\n"), ("main.zed", "x = y;\n")]);
    assert_eq!(
        mistakes(&p),
        [
            "zed.manifest:1:11: the manifest entry `prelude` is bound to a string literal with no \
          hole, as `prelude = \"std.prelude\";`."
        ]
    );
    assert!(p.units.is_empty());
}

#[test]
fn a_prelude_unit_name_that_is_no_type_stands_where_a_type_is_written() {
    let p = package(&[
        ("zed.manifest", "prelude = \"std.prelude\";\n"),
        ("std/prelude.zed", "scale = 1.0;\n"),
        ("main.zed", "f(positional a: scale) = a;\n"),
    ]);
    // Before: "the type `scale` is not defined: no type in scope has this name, and the
    // prelude has none", though the prelude unit declares it.
    assert_eq!(
        mistakes(&p),
        [
            "main.zed:1:17: `scale` stands where a type is written, and the prelude unit \
             `std.prelude` declares `scale` as the binding target, which is no type."
        ]
    );
}
