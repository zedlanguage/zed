//! The loader in the query database: each unit's resolution is keyed by its text and the
//! exports of the units it imports, so an edit inside a unit that keeps its names resolves none
//! of its importers again, and an edit that changes them resolves each importer once.

use super::files;
use zedc::query::{Db, Query};
use zedc::unit::load;

const MAIN: &str = "import pricing.{net};\nimport shipping.{fee};\ntotal = net(10.0) + fee;\n";

#[test]
fn an_edit_that_keeps_a_units_exports_resolves_no_importer_again() {
    let mut db = Db::new();
    let first = [
        ("main.zed", MAIN),
        ("pricing.zed", "net(gross: f64) = gross / 1.2;\n"),
        ("shipping.zed", "fee = 4.5;\n"),
    ];
    load(&mut db, &files(&first), &["main"]);
    assert_eq!(db.computed(Query::Resolve), 3);
    // The body of `net` changes and a comment moves every position; the names stay.
    let body = [
        ("main.zed", MAIN),
        (
            "pricing.zed",
            "// net of VAT\nnet(gross: f64) = gross / 1.25;\n",
        ),
        ("shipping.zed", "fee = 4.5;\n"),
    ];
    let p = load(&mut db, &files(&body), &["main"]);
    assert_eq!(
        db.computed(Query::Resolve),
        4,
        "only `pricing` is resolved again"
    );
    assert_eq!(db.computed(Query::Parse), 4);
    assert!(p.unit("main").unwrap().resolved.is_some());
    // A new name changes the exports, so `main` is resolved again; `shipping` is not.
    let names = [
        ("main.zed", MAIN),
        (
            "pricing.zed",
            "// net of VAT\nnet(gross: f64) = gross / 1.25;\nvat = 0.25;\n",
        ),
        ("shipping.zed", "fee = 4.5;\n"),
    ];
    load(&mut db, &files(&names), &["main"]);
    assert_eq!(db.computed(Query::Resolve), 6);
}

#[test]
fn a_unit_read_again_unchanged_is_neither_parsed_nor_resolved_again() {
    let mut db = Db::new();
    let fs = files(&[
        ("main.zed", MAIN),
        ("pricing.zed", "net(g) = g;\n"),
        ("shipping.zed", "fee = 1;\n"),
    ]);
    load(&mut db, &fs, &["main"]);
    load(&mut db, &fs, &["main"]);
    assert_eq!(db.computed(Query::Parse), 3);
    assert_eq!(db.computed(Query::Resolve), 3);
}
