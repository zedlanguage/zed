//! Recording what a row reads is linear in its reads: a chain of n definitions whose last has a
//! table records n reads and n reverse entries (`reads.rs` checks the counts at a small size).

use std::sync::Arc;

use zed_tests::scaling::{check, inputs};
use zedc::query::{Db, Query, Read, key};
use zedc::testing::test_in;

use crate::{chain, read_count, reverse_entries};

#[test]
fn recording_the_reads_of_a_chain_scales() {
    let texts = inputs(1_000, chain);
    check(
        "checking a chain of n definitions and recording its reads",
        1_000,
        |n| {
            let mut db = Db::new();
            test_in(&mut db, &texts[&n]);
            assert_eq!(read_count(&db), n);
        },
    );
}

#[test]
fn chains_of_ten_to_the_third_to_the_fifth_record_one_reverse_entry_per_read() {
    // Through the front end and the tables at 10^3 and 10^4; at 10^5 the evaluation of the
    // chain's row would nest 10^5 calls, so the row's reads are given to the database as a
    // chain's would be, by number and name, and recorded the same way.
    for n in [1_000, 10_000] {
        let mut db = Db::new();
        test_in(&mut db, &chain(n));
        assert_eq!(read_count(&db), n);
        assert_eq!(reverse_entries(&db), n);
    }
    let n = 100_000;
    let reads: Vec<Read> = (0..n as u64)
        .map(|i| Read::Definition(i, Arc::from(format!("d{i}"))))
        .collect();
    let mut db = Db::new();
    let got = db.row(Query::Row, key("row", &[b"chain"]), reads, || Ok(()));
    assert_eq!(got, Ok(()));
    assert_eq!(read_count(&db), n);
    assert_eq!(reverse_entries(&db), n);
}
