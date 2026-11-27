//! What each query records it read, and the reverse map.

use zedc::query::{Db, Query, Read};
use zedc::testing::test_in;
use zedc::unit::load;

use super::{chain, files, names, read_count, records, reverse_entries};

/// `g` calls `f`; `h` calls nothing. Each has a table of one row.
const CALLS: &str = "\
f(positional x: int) = x + 1
test { 1 -> 2 }

g(positional x: int) = f(x) * 2
test { 1 -> 4 }

h(positional x: int) = x - 1
test { 1 -> 0 }
";

/// The names each row of `db` read, a list per row, in increasing order.
fn rows(db: &Db) -> Vec<Vec<String>> {
    let mut out: Vec<Vec<String>> = (db.records())
        .filter(|(q, _, _)| *q == Query::Row)
        .map(|(_, _, reads)| names(reads))
        .collect();
    out.sort();
    out
}

#[test]
fn a_row_records_the_definitions_it_reaches_and_each_has_its_readers() {
    let mut db = Db::new();
    test_in(&mut db, CALLS);
    assert_eq!(rows(&db), [vec!["f"], vec!["f", "g"], vec!["h"]]);
    let f = (db.records())
        .flat_map(|(_, _, reads)| reads)
        .find(|r| matches!(r, Read::Definition(_, name) if &**name == "f"))
        .expect("a row read `f`")
        .clone();
    let mut readers: Vec<Vec<String>> = (db.readers(&f))
        .map(|(q, k)| {
            assert_eq!(q, Query::Row);
            names(db.reads(q, k).expect("a reader has a record"))
        })
        .collect();
    readers.sort();
    assert_eq!(readers, [vec!["f"], vec!["f", "g"]]);
}

#[test]
fn a_comment_changes_no_record() {
    let mut db = Db::new();
    test_in(&mut db, CALLS);
    let before = records(&db);
    test_in(&mut db, &format!("// three functions\n{CALLS}"));
    assert_eq!(records(&db), before);
}

#[test]
fn two_runs_from_scratch_record_the_same() {
    let run = || {
        let mut db = Db::new();
        test_in(&mut db, CALLS);
        test_in(&mut db, &chain(20));
        records(&db)
    };
    let first = run();
    assert!(!first.is_empty());
    assert_eq!(first, run());
}

#[test]
fn a_chain_records_one_read_per_definition_and_one_reverse_entry_per_read() {
    let n = 50;
    let mut db = Db::new();
    test_in(&mut db, &chain(n));
    let want: Vec<String> = (0..n).map(|i| format!("d{i}")).collect();
    let mut want = want;
    want.sort();
    assert_eq!(rows(&db), [want]);
    assert_eq!(read_count(&db), n);
    assert_eq!(reverse_entries(&db), n);
}

#[test]
fn a_resolution_records_the_resolution_of_each_unit_it_imports() {
    let fs = files(&[
        ("main.zed", "import pricing.{net};\ntotal = net(100.0);\n"),
        ("pricing.zed", "net(gross: f64) = gross / 1.2;\n"),
    ]);
    let mut db = Db::new();
    load(&mut db, &fs, &["main"]);
    let resolves: Vec<Vec<Read>> = (db.records())
        .filter(|(q, _, _)| *q == Query::Resolve)
        .map(|(_, _, reads)| reads.to_vec())
        .collect();
    assert_eq!(resolves.len(), 1, "only `main` imports: {resolves:?}");
    let [Read::Query(Query::Resolve, k)] = &resolves[0][..] else {
        panic!("`main` read one resolution: {:?}", resolves[0]);
    };
    let pricing = b"net(gross: f64) = gross / 1.2;";
    assert!(k.0.windows(pricing.len()).any(|w| w == pricing));
    let readers: Vec<Query> = db.readers(&resolves[0][0]).map(|(q, _)| q).collect();
    assert_eq!(readers, [Query::Resolve]);
}

#[test]
fn an_address_records_the_front_end_it_read() {
    let unit = "v0(x: f64) = x * 0.0 + 1.0;\n";
    let fs = files(&[
        ("u0.zed", unit),
        ("main.zed", "import u0;\nmain(m: MainArgs) {}\n"),
    ]);
    let pinned = load(&mut Db::new(), &fs, &["main"]).pinned("main").unwrap();
    let fs = files(&[("u0.zed", unit), ("main.zed", &pinned)]);
    let mut db = Db::new();
    load(&mut db, &fs, &["main"]);
    let addresses: Vec<Vec<Read>> = (db.records())
        .filter(|(q, _, _)| *q == Query::Address)
        .map(|(_, _, reads)| reads.to_vec())
        .collect();
    assert_eq!(addresses.len(), 1, "`u0` is addressed: {addresses:?}");
    let [Read::Query(Query::Front, k)] = &addresses[0][..] else {
        panic!("an address reads the front end: {:?}", addresses[0]);
    };
    assert!(k.0.windows(unit.len()).any(|w| w == unit.as_bytes()));
}
