//! The edges of the messages for a `with` clause, a `mutable` declaration and a word after
//! `with` (DESIGN.md sec:generations, sec:diagnostics): the key of an item given on an indexed
//! definition, one below the low edge of its domain, worked out for each form of the low edge;
//! an item of another indexed variable kept as written; a name given twice in one clause in a
//! loop written once; a sentinel value already given by an `initial` statement written after an
//! annotation with arguments, or with a key; and a `mutable` declaration whose repair would not
//! parse, or that is no declaration of its own statement.

use super::initial::{notes, refusal};
use zedc::rejection::Row;

/// The repair notes of the refusal of `src` in `row`.
#[track_caller]
fn repairs(src: &str, row: Row) -> Vec<String> {
    let e = refusal(src);
    assert_eq!(e.row, Some(row), "{src}: {e:?}");
    notes(src, &e)
        .into_iter()
        .filter(|n| n.starts_with("repair: "))
        .collect()
}

/// The entry below the domain `lo..<hi` has the key `lo - 1`: a literal is worked out, negated
/// or not, and any other low edge is written `lo - 1`, in parentheses when it is more than one
/// token.
#[test]
fn the_key_below_the_domain_follows_the_low_edge() {
    for (lo, key) in [
        ("0", "-1"),
        ("3", "2"),
        ("-3", "-4"),
        ("1_000", "999"),
        ("n", "n - 1"),
        ("n + 1", "(n + 1) - 1"),
    ] {
        let src = format!("d[i in {lo}..<9] = d[i - 1] + 1 with d = 0;\n");
        let r = repairs(&src, Row::BareBoundary);
        let want = format!("d[i in {lo}..<9] = d[i - 1] + 1 with d[{key}] = 0;");
        assert!(
            r.len() == 1 && r[0].starts_with(&format!("repair: `{want}`")),
            "{src}: {r:?}"
        );
    }
    // `..=` and an open range have the same low edge.
    for range in ["2..=9", "2.."] {
        let src = format!("d[i in {range}] = d[i - 1] + 1 with d = 0;\n");
        let r = repairs(&src, Row::BareBoundary);
        assert!(
            r.len() == 1 && r[0].contains("with d[1] = 0;`"),
            "{src}: {r:?}"
        );
    }
}

/// A domain with no low edge, as `i in s`, has no entry below it: the item is not given a key
/// the program does not state, so no repair is offered that names one.
#[test]
fn a_domain_with_no_low_edge_gives_no_key() {
    let src = "d[i in s] = d[i - 1] + 1 with d = 0;\n";
    let e = refusal(src);
    assert_eq!(e.row, Some(Row::BareBoundary), "{e:?}");
    let all = notes(src, &e);
    assert!(
        all.iter()
            .all(|n| !n.starts_with("repair: ") || n.contains("d[…]")),
        "{all:?}"
    );
}

/// On an indexed definition, an item of another variable with its key is kept as written beside
/// the repaired one.
#[test]
fn a_keyed_item_of_another_variable_is_kept() {
    let src = "d[i in 0..<5] = d[i - 1] + e[i] with d = 0, e[-1] = 1;\n";
    let r = repairs(src, Row::BareBoundary);
    assert!(
        r.len() == 1
            && r[0].starts_with(
                "repair: `d[i in 0..<5] = d[i - 1] + e[i] with d[-1] = 0, e[-1] = 1;`"
            ),
        "{r:?}"
    );
}

/// In a loop, a name given twice in one clause is written as one `initial` statement.
#[test]
fn a_name_given_twice_in_a_loop_is_written_once() {
    let src = "r = loop t {\n  while t < 3;\n  x' = x + 1 with x = 0, x = 1;\n};\n";
    let r = repairs(src, Row::BareBoundary);
    assert!(
        r.len() == 1
            && r[0].starts_with("repair: `initial x = 0; x' = x + 1;`")
            && !r[0].contains("initial x = 1"),
        "{r:?}"
    );
}

/// An `initial` statement that already gives the sentinel value is found after annotations,
/// one with arguments among them, and in its keyed form `initial x[-1] = e;`; the item is then
/// only deleted.
#[test]
fn an_initial_statement_after_annotations_or_with_a_key_is_found() {
    for site in [
        "@a @b(1, (2)) initial x = 0;",
        "initial x[-1] = 0;",
        "@a initial x[-1] = 0;",
    ] {
        let src = format!(
            "r = loop t {{\n  while t < 3;\n  {site}\n  p <- t with x = 0;\n  x' = x + 1;\n}};\n"
        );
        let r = repairs(&src, Row::BareBoundary);
        assert_eq!(
            r,
            ["repair: `p <- t;`, the `with` clause deleted [x = 0]"],
            "{src}"
        );
    }
    // `initial x[-2] = 0;` gives another entry, so the item is written as a statement.
    let src = "r = loop t {\n  while t < 3;\n  initial x[-2] = 0;\n  p <- t with x = 0;\n  x' = x + 1;\n};\n";
    let r = repairs(src, Row::BareBoundary);
    assert!(
        r.len() == 1 && r[0].starts_with("repair: `initial x = 0; p <- t;`"),
        "{r:?}"
    );
}

/// `local mutable x = e;` outside a loop is the plain binding `local x = e;`.
#[test]
fn a_local_mutable_outside_a_loop_keeps_local() {
    let src = "f(n) = {\n  local mutable x = n;\n  x\n};\n";
    let e = refusal(src);
    assert_eq!(e.row, Some(Row::MutableDeclaration), "{e:?}");
    assert_eq!(
        e.message,
        "Zed has no `mutable`: `local mutable x = n;`. Try `local x = n;` instead."
    );
}

/// A `mutable` declaration whose repair would not parse either is named, with no repair.
#[test]
fn a_mutable_declaration_whose_repair_does_not_parse_is_named_alone() {
    let src = "mutable x = ;\n";
    let e = refusal(src);
    assert_eq!(e.row, Some(Row::MutableDeclaration), "{e:?}");
    assert_eq!(e.message, "Zed has no `mutable`: `mutable x = ;`.");
    assert!(
        notes(src, &e).iter().all(|n| !n.starts_with("repair: ")),
        "{e:?}"
    );
}

/// `mutable` followed by a name that does not start its statement, or a statement with no `;`,
/// is no `mutable` declaration: the parser's own message stands.
#[test]
fn mutable_inside_a_statement_is_not_a_declaration() {
    for src in ["y = mutable x = 1;\n", "mutable x = 1"] {
        let e = refusal(src);
        assert_ne!(e.row, Some(Row::MutableDeclaration), "{src}: {e:?}");
    }
}
