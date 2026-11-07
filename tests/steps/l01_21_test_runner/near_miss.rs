//! The near-miss listing (DESIGN.md step L1.29): each row of the rejection table the
//! implementation raises has one program one edit from an accepted one, listed with the place
//! its diagnostic reports and the first entry of its menu. The listing fails for a row the
//! implementation raises that it does not list, and for a listed program whose diagnostic
//! differs from it.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use zedc::query::Db;
use zedc::rejection::Row;

/// A label printer, a stamp that hands a weight to a handler, a fee, and a lookup that misses.
const LABEL: &str = "label(positional name: String, city: String, postcode: String = \"\") = \
                     name ++ \", \" ++ city ++ \" \" ++ postcode;\n";
const STAMP: &str =
    "stamp(positional weight: int, handler: (grams: int) -> String) = handler(grams: weight);\n";
const FEE: &str = "fee(positional base: int, rate: int) = base * rate;\n";
const LOOKUP: &str = "lookup(positional k: int) = if k > 0 { k } else { #notFound };\n";

/// A near miss: its row, the text before the rest, the accepted line, the rejected line (one
/// edit from it), the place of the row's diagnostic, and the first entry of its menu, after
/// `repair: `. `None` is a row whose menu has not landed: the listing fails once it has one.
type NearMiss = (
    Row,
    &'static str,
    &'static str,
    &'static str,
    &'static str,
    Option<&'static str>,
);

const NEAR_MISSES: &[NearMiss] = &[
    (
        Row::Rebinding,
        "f(x) {\n  y = x + 1;\n",
        "  z = y * 2;\n  z\n}\n",
        "  y = y * 2;\n  y\n}\n",
        "3:3",
        Some("give this binding a new name"),
    ),
    (
        Row::BinderNamingType,
        "",
        "f(positional n) = 1;\n",
        "f(positional int) = 1;\n",
        "1:14",
        Some("rename the binder; where a cast was meant, write the type application `int(…)`"),
    ),
    (
        Row::PrefixMinus,
        "",
        "y = (-1).abs;\n",
        "y = -1.abs;\n",
        "1:5",
        Some("`(-1).abs`, the chain started at `-1`, which is 1"),
    ),
    (
        Row::DisplayInBody,
        LOOKUP,
        "t = lookup(3) else { (0, 1) };\n",
        "t = lookup(3) else { 0, 1 };\n",
        "2:20",
        Some("`({ 0, 1 })`, the set display in parentheses"),
    ),
    (
        Row::NoArrowAtCarrier,
        "",
        "s(positional n: int) = \"#\" ++ String(n);\n",
        "s(positional n: int) = \"#\" ++ n;\n",
        "1:24",
        Some("write `String(n)`; the checker accepts that"),
    ),
    (
        Row::NoCommonCarrier,
        "",
        "total(r: rat, x: f64) = f64(r) + x;\n",
        "total(r: rat, x: f64) = r + x;\n",
        "1:25",
        Some("write `f64(r)`; the checker accepts that"),
    ),
    (
        Row::NamedBeforePositional,
        FEE,
        "f = fee(5, rate: 3);\n",
        "f = fee(rate: 3, 5);\n",
        "2:18",
        Some("pass this argument before `rate`, the positional arguments first"),
    ),
    (
        Row::PositionalAfterNamed,
        "",
        "surcharge(positional base: int, rate: int) = base * rate;\n",
        "surcharge(rate: int, positional base: int) = base * rate;\n",
        "1:22",
        Some("declare `base` before `rate`, the positional parameters first"),
    ),
    (
        Row::WrongForm,
        LABEL,
        "b = label(\"Ada\", city: \"Leeds\");\n",
        "b = label(name: \"Ada\", city: \"Leeds\");\n",
        "2:17",
        Some("pass `name` by position"),
    ),
    (
        Row::ParameterKinds,
        STAMP,
        "d = stamp(120, handler: grams -> \"x\");\n",
        "d = stamp(120, handler: g -> \"x\");\n",
        "2:25",
        Some("rename `g` to `grams`"),
    ),
    (
        Row::MissingArgument,
        LABEL,
        "a = label(\"Ada\", city: \"Leeds\");\n",
        "a = label(\"Ada\");\n",
        "2:5",
        Some("supply `city`"),
    ),
    (
        Row::NothingLeftOut,
        LABEL,
        "c = label(\"Ada\", city: \"Leeds\", postcode: \"LS1\");\n",
        "c = label(\"Ada\", city: \"Leeds\", postcode: \"LS1\", ...);\n",
        "2:5",
        Some("remove the `...`"),
    ),
    (
        Row::WritesNothing,
        LOOKUP,
        "_ = lookup(3) else #ok;\n",
        "_ = lookup(3);\n",
        "2:1",
        Some(
            "write a default for the value, as `_ = … else #ok;`, so the text names what it \
             drops",
        ),
    ),
    // Its menu is plan item MENU-linear's (`NON_LINEAR_MENU` in crates/zedc/src/front.rs).
    (
        Row::NonLinearQuestion,
        "",
        "ok(x, y, z, w) = 9 * x - 4 * y - 8 * w - 3 >= 0 && 5 * x + 11 * y + 9 * w - 9 >= 0 && \
         -7 * x - 12 * y - 2 * z + 8 * w - 1 >= 0 && -9 * x + 8 * y + 7 * z >= 0;\n",
        "ok(x, y, z, w) = 9 * x - 4 * y - 8 * w - 3 >= 0 && 5 * x + 11 * y + 9 * w - 9 >= 0 && \
         -7 * x - 12 * y - 2 * z + 8 * w - 1 >= 0 && -9 * x + 8 * y + 7 * z >= 0 && \
         -10 * x + 4 * y - 6 * z - 4 * w + 22 >= 0;\n",
        "1:1",
        Some(
            "state an equality on one of the names, as `x == 4 && …`, so the solver removes \
             that name from the question",
        ),
    ),
];

/// The `.rs` files under `dir`, in no order.
fn sources(dir: &Path, out: &mut Vec<PathBuf>) {
    for e in std::fs::read_dir(dir).expect("a source directory") {
        let path = e.expect("an entry").path();
        if path.is_dir() {
            sources(&path, out);
        } else if path.extension().is_some_and(|x| x == "rs") {
            out.push(path);
        }
    }
}

/// The rows the implementation raises: those whose variant the compiler's source names, the
/// table's own file aside.
fn raised() -> BTreeSet<Row> {
    let src = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../crates/zedc/src");
    let mut files = Vec::new();
    sources(&src, &mut files);
    let names: Vec<(String, Row)> = Row::ALL.iter().map(|&r| (format!("{r:?}"), r)).collect();
    let mut out = BTreeSet::new();
    for f in files.iter().filter(|f| !f.ends_with("rejection.rs")) {
        let text = std::fs::read_to_string(f).expect("a readable source");
        for (at, _) in text.match_indices("Row::") {
            let rest = &text[at + "Row::".len()..];
            let end = rest
                .find(|c: char| !c.is_ascii_alphanumeric())
                .unwrap_or(rest.len());
            if let Some((_, r)) = names.iter().find(|(n, _)| *n == rest[..end]) {
                out.insert(*r);
            }
        }
    }
    out
}

#[test]
fn each_row_the_implementation_raises_has_a_near_miss() {
    let listed: BTreeSet<Row> = NEAR_MISSES.iter().map(|m| m.0).collect();
    assert_eq!(listed.len(), NEAR_MISSES.len(), "a row is listed twice");
    let raised = raised();
    let missing: Vec<&str> = raised.difference(&listed).map(|r| r.name()).collect();
    let stale: Vec<&str> = listed.difference(&raised).map(|r| r.name()).collect();
    assert!(missing.is_empty(), "raised, with no near miss: {missing:?}");
    assert!(stale.is_empty(), "listed, and raised nowhere: {stale:?}");
}

#[test]
fn each_near_miss_gives_its_row_place_and_first_repair() {
    let mut failed = Vec::new();
    for &(row, head, accepted, rejected, at, first) in NEAR_MISSES {
        let good = format!("{head}{accepted}");
        if let Err(ds) = &*Db::new().front(&good) {
            failed.push(format!(
                "{}: the accepted program is rejected: {ds:?}",
                row.name()
            ));
        }
        let text = format!("{head}{rejected}");
        let front = Db::new().front(&text);
        let Err(ds) = &*front else {
            failed.push(format!("{}: the near miss is accepted", row.name()));
            continue;
        };
        let Some(d) = ds.iter().find(|d| d.row == Some(row)) else {
            failed.push(format!("{}: no diagnostic in the row: {ds:?}", row.name()));
            continue;
        };
        let place = format!("{}:{}", d.line, d.col);
        let repair = d.steps.iter().find_map(|s| s.text.strip_prefix("repair: "));
        if place != at || repair != first {
            failed.push(format!(
                "{}: at {place}, first repair {repair:?}; listed at {at}, {first:?}",
                row.name()
            ));
        }
    }
    assert!(failed.is_empty(), "{failed:#?}");
}
