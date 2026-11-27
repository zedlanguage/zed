//! Step L1.30a: each query records the keys of the queries and definitions it read, and the
//! database keeps the reverse map from each key to the queries that read it (DESIGN.md
//! sec:incremental, "The compiler's own stages are derived the same way", item 3). No result
//! changes; the records are read by these tests until step L7.13 propagates along them.

mod bench;
mod reads;

use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

use zedc::query::{Db, Key, Query, Read};
use zedc::unit::Memory;

/// Every record of `db`: each query computed that read something, its key, and what it read.
pub(crate) fn records(db: &Db) -> BTreeSet<(Query, Key, Vec<Read>)> {
    db.records()
        .map(|(q, k, reads)| (q, k.clone(), reads.to_vec()))
        .collect()
}

/// The written names of the definitions among `reads`, in increasing order.
pub(crate) fn names(reads: &[Read]) -> Vec<String> {
    let mut out: Vec<String> = (reads.iter())
        .filter_map(|r| match r {
            Read::Definition(_, name) => Some(name.to_string()),
            Read::Query(..) => None,
        })
        .collect();
    out.sort();
    out
}

/// The number of entries of the reverse map of `db`, counted from the reads of its records: the
/// readers of each distinct read.
pub(crate) fn reverse_entries(db: &Db) -> usize {
    let distinct: BTreeSet<&Read> = db.records().flat_map(|(_, _, reads)| reads).collect();
    distinct.into_iter().map(|r| db.readers(r).count()).sum()
}

/// The number of reads of the records of `db`.
pub(crate) fn read_count(db: &Db) -> usize {
    db.records().map(|(_, _, reads)| reads.len()).sum()
}

/// `n` functions `d0`, …, `d{n-1}` that call each other as a binary tree, `d{i}` calling
/// `d{2i+1}` and `d{2i+2}` where they exist, and `d0`, written last, with a table: its row
/// reads every one of them. A tree, not a chain, so the row's evaluation nests about `log2 n`
/// calls and not `n`, which at `n` = 10^4 would need more than a test thread's 2 MiB stack.
pub(crate) fn tree(n: usize) -> String {
    let mut out = String::new();
    for i in (0..n).rev() {
        let (a, b) = (2 * i + 1, 2 * i + 2);
        let body = match (a < n, b < n) {
            (true, true) => format!("d{a}(x) + d{b}(x)"),
            (true, false) => format!("d{a}(x) + 1"),
            _ => "x + 1".to_string(),
        };
        out.push_str(&format!("d{i}(positional x: int) = {body}\n"));
    }
    out.push_str(&format!("test {{ 0 -> {} }}\n", tree_value(n, 0)));
    out
}

/// `d{i}(0)` in [`tree`]`(n)`.
fn tree_value(n: usize, i: usize) -> usize {
    let (a, b) = (2 * i + 1, 2 * i + 2);
    match (a < n, b < n) {
        (true, true) => tree_value(n, a) + tree_value(n, b),
        (true, false) => tree_value(n, a) + 1,
        _ => 1,
    }
}

/// The files `files`, each a name under the root and its text.
pub(crate) fn files(files: &[(&str, &str)]) -> Memory {
    Memory(
        files
            .iter()
            .map(|&(name, text)| (name.to_string(), Arc::from(text)))
            .collect::<HashMap<_, _>>(),
    )
}
