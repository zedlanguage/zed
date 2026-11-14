//! The completeness pass over the queries (row TEST-complete-diagnostics): the cases
//! COMPLETENESS.md lists that the other files leave out. Expected results are from DESIGN.md,
//! step L1.30: a query's result is kept under a key made of everything it reads, so asking
//! again with the same inputs computes nothing, and any change of an input computes again.

use std::cell::Cell;

use zedc::build::Build;
use zedc::query::{Db, Query, key};
use zedc::resolve::Exports;

use super::{PRICING, checks};

const GOOD: &str = "double(positional n: int) = n * 2;\n";
const BAD: &str = "double(positional n: int) = n * \"2\";\n";

/// A build of a package that declares the option `fast`, turned on or not.
fn with_fast(on: bool) -> Build {
    let target = Build::default().target().to_string();
    let on: &[&str] = if on { &["fast"] } else { &[] };
    Build::new(&target, &["fast".to_string()], on).unwrap()
}

#[test]
fn a_key_keeps_the_name_apart_from_the_parts() {
    assert_ne!(key("ab", &[]), key("a", &[b"b"]));
    assert_ne!(key("row", &[]), key("row", &[b""]));
    assert_eq!(key("row", &[]), key("row", &[]));
    assert_eq!(key("", &[]), key("", &[]));
    assert_ne!(key("", &[]), key("", &[b""]));
    // Bytes that are not text are kept as they are.
    assert_ne!(key("row", &[&[0xff, 0]]), key("row", &[&[0xff]]));
}

#[test]
fn a_new_database_has_computed_nothing() {
    let db = Db::new();
    for q in [
        Query::Front,
        Query::Row,
        Query::Wave,
        Query::Parse,
        Query::Resolve,
        Query::Address,
        Query::Check,
    ] {
        assert_eq!(db.computed(q), 0, "{q:?}");
    }
}

#[test]
fn a_row_is_computed_once_per_key_and_a_failure_is_kept_too() {
    let mut db = Db::new();
    let runs = Cell::new(0);
    let fail = || {
        runs.set(runs.get() + 1);
        Err("the result is 3".to_string())
    };
    let k = key("row", &[b"f"]);
    assert_eq!(
        db.row(Query::Row, k.clone(), fail),
        Err("the result is 3".into())
    );
    assert_eq!(
        db.row(Query::Row, k.clone(), fail),
        Err("the result is 3".into())
    );
    assert_eq!(runs.get(), 1);
    assert_eq!(db.computed(Query::Row), 1);
    // Another key computes.
    assert_eq!(db.row(Query::Row, key("row", &[b"g"]), || Ok(())), Ok(()));
    assert_eq!(db.computed(Query::Row), 2);
}

#[test]
fn a_function_row_and_a_wave_row_under_one_key_are_kept_apart() {
    let mut db = Db::new();
    let k = key("row", &[b"same"]);
    assert_eq!(db.row(Query::Row, k.clone(), || Ok(())), Ok(()));
    assert_eq!(
        db.row(Query::Wave, k.clone(), || Err("wave".into())),
        Err("wave".into())
    );
    assert_eq!(db.computed(Query::Row), 1);
    assert_eq!(db.computed(Query::Wave), 1);
    assert_eq!(db.row(Query::Row, k, || Err("again".into())), Ok(()));
}

#[test]
fn the_front_end_is_kept_by_text() {
    let mut db = Db::new();
    let a = db.front(GOOD);
    let b = db.front(GOOD);
    assert!(std::sync::Arc::ptr_eq(&a, &b));
    assert!(a.is_ok());
    assert_eq!(db.computed(Query::Front), 1);
    // One byte more is another text.
    db.front(&format!("{GOOD}\n"));
    assert_eq!(db.computed(Query::Front), 2);
    // A text the front end rejects is kept as well.
    assert!(db.front(BAD).is_err());
    assert!(db.front(BAD).is_err());
    assert_eq!(db.computed(Query::Front), 3);
}

#[test]
fn another_build_computes_the_front_end_again_and_keeps_the_first() {
    let mut db = Db::for_build(with_fast(false));
    assert_eq!(db.build(), &with_fast(false));
    db.front(GOOD);
    db.set_build(&with_fast(true));
    db.front(GOOD);
    assert_eq!(db.computed(Query::Front), 2);
    // Back to the first build: its result is still kept.
    db.set_build(&with_fast(false));
    db.front(GOOD);
    assert_eq!(db.computed(Query::Front), 2);
    // Setting the build it already has changes nothing.
    db.set_build(&with_fast(false));
    db.front(GOOD);
    assert_eq!(db.computed(Query::Front), 2);
}

#[test]
fn a_check_is_kept_by_text_and_build() {
    let mut db = Db::new();
    assert!(db.check(GOOD).is_empty());
    assert!(!db.check(BAD).is_empty());
    assert!(!db.check(BAD).is_empty());
    assert!(db.check(GOOD).is_empty());
    assert_eq!(db.computed(Query::Check), 2);
    db.set_build(&with_fast(true));
    db.check(GOOD);
    assert_eq!(db.computed(Query::Check), 3);
}

#[test]
fn a_parse_is_kept_by_text_alone() {
    let mut db = Db::new();
    assert!(db.parse(GOOD).is_ok());
    db.set_build(&with_fast(true));
    assert!(db.parse(GOOD).is_ok());
    assert_eq!(db.computed(Query::Parse), 1);
    db.parse(BAD);
    assert_eq!(db.computed(Query::Parse), 2);
}

#[test]
fn a_resolution_is_computed_once_per_key() {
    let mut db = Db::new();
    let runs = Cell::new(0);
    let compute = || {
        runs.set(runs.get() + 1);
        zedc::resolve::Resolved {
            res: zedc::resolve::resolve(&[]).unwrap(),
            errors: Vec::new(),
            later: Vec::new(),
        }
    };
    let k = key("resolve", &[b"u"]);
    let a = db.resolve(k.clone(), compute);
    let b = db.resolve(k, compute);
    assert!(std::sync::Arc::ptr_eq(&a, &b));
    assert_eq!(runs.get(), 1);
    db.resolve(key("resolve", &[b"v"]), compute);
    assert_eq!(runs.get(), 2);
    assert_eq!(db.computed(Query::Resolve), 2);
}

#[test]
fn an_address_is_kept_and_the_options_of_a_build_leave_it() {
    let mut db = Db::for_build(with_fast(false));
    let e = Exports::default();
    let a = db.address(GOOD, &e);
    assert!(a.is_some());
    let fronts = db.computed(Query::Front);
    // The option on: the unit is pinned with every option off, so nothing is computed.
    db.set_build(&with_fast(true));
    let b = db.address(GOOD, &e);
    assert!(std::sync::Arc::ptr_eq(&a, &b));
    assert_eq!(db.computed(Query::Address), 1);
    assert_eq!(db.computed(Query::Front), fronts);
    // A unit that does not compile alone has none.
    assert!(db.address(BAD, &e).is_none());
    assert_eq!(db.computed(Query::Address), 2);
    // Another target is another key.
    db.set_build(&Build::default().for_target("aarch64-linux"));
    db.address(GOOD, &e);
    assert_eq!(db.computed(Query::Address), 3);
}

#[test]
fn equal_exports_share_a_number_and_unequal_ones_do_not() {
    let mut db = Db::new();
    let empty = Exports::default();
    let mut broken = Exports::default();
    broken.set_broken(["f".to_string()]);
    let a = db.exports_number(&empty);
    let b = db.exports_number(&broken);
    assert_ne!(a, b);
    assert_eq!(db.exports_number(&Exports::default()), a);
    assert_eq!(db.exports_number(&broken.clone()), b);
}

#[test]
fn a_copy_keeps_what_was_computed_and_goes_on_apart() {
    let mut db = Db::new();
    let first = checks(&mut db, PRICING);
    let mut copy = db.clone();
    assert_eq!(checks(&mut copy, PRICING), first);
    assert_eq!(copy.computed(Query::Row), db.computed(Query::Row));
    assert_eq!(copy.computed(Query::Front), 1);
    // An edit on the copy computes on the copy only.
    let edited = PRICING.replace("cents * 8 div 100", "cents * 9 div 100");
    checks(&mut copy, &edited);
    assert!(copy.computed(Query::Row) > db.computed(Query::Row));
    assert_eq!(db.computed(Query::Front), 1);
    // And the original still answers as before, computing nothing.
    assert_eq!(checks(&mut db, PRICING), first);
    assert_eq!(db.computed(Query::Front), 1);
}

#[test]
fn two_databases_give_one_answer() {
    let mut a = Db::new();
    let mut b = Db::new();
    // The second database meets other texts first, so it numbers them otherwise.
    checks(&mut b, GOOD);
    assert_eq!(checks(&mut a, PRICING), checks(&mut b, PRICING));
}

#[test]
fn a_unit_with_no_table_computes_no_row() {
    let mut db = Db::new();
    assert!(checks(&mut db, GOOD).is_empty());
    assert_eq!(db.computed(Query::Row), 0);
    assert_eq!(db.computed(Query::Wave), 0);
}

#[test]
fn an_edit_back_reuses_the_first_results() {
    let mut db = Db::new();
    checks(&mut db, PRICING);
    let edited = PRICING.replace("cents * 8 div 100", "cents * 10 div 100");
    checks(&mut db, &edited);
    let rows = db.computed(Query::Row);
    let fronts = db.computed(Query::Front);
    checks(&mut db, PRICING);
    assert_eq!(db.computed(Query::Row), rows);
    assert_eq!(db.computed(Query::Front), fronts);
}
