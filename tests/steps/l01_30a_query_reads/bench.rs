//! Recording what a row reads is linear in its reads: a tree of n definitions whose root has a
//! table records n reads and n reverse entries (`reads.rs` checks the counts at a small size).

use std::sync::Arc;

use zed_tests::scaling::{check, inputs};
use zedc::query::{Db, Query, Read, key};
use zedc::testing::test_in;

use crate::{read_count, reverse_entries, tree};

#[test]
fn recording_the_reads_of_a_tree_of_calls_scales() {
    let texts = inputs(1_000, tree);
    check(
        "checking a tree of n definitions and recording its reads",
        1_000,
        |n| {
            let mut db = Db::new();
            test_in(&mut db, &texts[&n]);
            assert_eq!(read_count(&db), n);
        },
    );
}

#[test]
fn trees_of_ten_to_the_third_to_the_fifth_record_one_reverse_entry_per_read() {
    // Through the front end and the tables at 10^3 and 10^4. At 10^5 the row's reads are given
    // to the database as a tree's would be, by number and name, and recorded the same way: the
    // front end's own cost at that size is the business of its benchmarks, not of this one.
    for n in [1_000, 10_000] {
        let mut db = Db::new();
        test_in(&mut db, &tree(n));
        assert_eq!(read_count(&db), n);
        assert_eq!(reverse_entries(&db), n);
    }
    let n = 100_000;
    let reads: Vec<Read> = (0..n as u64)
        .map(|i| Read::Definition(i, Arc::from(format!("d{i}"))))
        .collect();
    let mut db = Db::new();
    let got = db.row(Query::Row, key("row", &[b"tree"]), reads, || Ok(()));
    assert_eq!(got, Ok(()));
    assert_eq!(read_count(&db), n);
    assert_eq!(reverse_entries(&db), n);
}
