//! `import`: a unit path, imported whole, under another name or name by name, and pinned to a
//! content address with a trailing `@hash("…")` of 64 lowercase hexadecimal digits.

use super::check;

/// A content address, 64 lowercase hexadecimal digits.
const H: &str = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

#[test]
fn the_three_forms_of_import() {
    check(&[
        ("import geometry.shapes;", "(import geometry.shapes)"),
        (
            "import geometry.shapes as gs;",
            "(import geometry.shapes as gs)",
        ),
        (
            "import geometry.shapes.{Circle, area,};",
            "(import geometry.shapes (Circle area))",
        ),
        ("import io;\nmain() = 0;", "(import io)\n(def main () = 0)"),
    ]);
}

#[test]
fn a_pin_follows_the_path() {
    let text = |form: &str| format!("import geometry.shapes{form} @hash(\"{H}\");");
    let want = |form: &str| format!("(import geometry.shapes{form} @hash({H}))");
    let cases = [
        (text(""), want("")),
        (text(" as gs"), want(" as gs")),
        (text(".{Circle}"), want(" (Circle)")),
        (format!("import geometry.shapes @hash(\"{H}\",);"), want("")),
    ];
    let cases: Vec<(&str, &str)> = cases
        .iter()
        .map(|(t, w)| (t.as_str(), w.as_str()))
        .collect();
    check(&cases);
}

#[test]
fn a_malformed_pin_is_refused_with_its_fault() {
    let upper = H.to_uppercase();
    let cases = [
        (
            format!("import a.b @hash(\"{upper}\");"),
            "error: a hash is written in lowercase hexadecimal digits, and 'A' is not one",
        ),
        (
            format!("import a.b @hash(\"{}\");", &H[..63]),
            "error: a hash has 64 hexadecimal digits, and this one has 63",
        ),
        (
            format!("import a.b @hash(\"{H}0\");"),
            "error: a hash has 64 hexadecimal digits, and this one has 65",
        ),
        (
            "import a.b @hash(\"\");".into(),
            "error: a hash has 64 hexadecimal digits, and this one has 0",
        ),
        (
            "import a.b @hash(\"0123456789abcdefg\");".into(),
            "error: a hash is written in lowercase hexadecimal digits, and 'g' is not one",
        ),
        (
            format!("import a.b @pin(\"{H}\");"),
            "error: an import is pinned with `@hash`, not `@pin`",
        ),
        (
            "import a.b @hash(\"${h}\");".into(),
            "error: the hash of a pin is written out; it has no `${…}` hole",
        ),
    ];
    let cases: Vec<(&str, &str)> = cases.iter().map(|(t, w)| (t.as_str(), *w)).collect();
    check(&cases);
}

#[test]
fn malformed_imports() {
    check(&[
        ("import;", "syntax"),
        ("import a.b", "syntax"),
        ("import a.{};", "syntax"),
        ("import a as;", "syntax"),
        ("import a.{b} as c;", "syntax"),
        ("import a @hash;", "syntax"),
        ("import a @hash(h);", "syntax"),
        ("import a @hash(\"x\", \"y\");", "syntax"),
        (
            "import a.b.{c, c};",
            "error: the name `c` is imported twice, and each name is imported once. Remove one of \
             the two.; the first name `c` at byte 12",
        ),
    ]);
}
