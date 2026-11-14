//! Reading the names of a graph in binary is linear in their bytes: the benchmark of
//! `names.rs`, whose test reads back a graph of a few names.

use zed_tests::scaling::check_order;
use zedc::zir::binary;

use crate::names::names;

#[test]
fn reading_names_in_binary_is_linear_in_their_bytes() {
    let (n, large) = (40_000, 320_000);
    let (small_bytes, large_bytes) = (
        binary::encode(&names(n)).expect("memory for the bytes"),
        binary::encode(&names(large)).expect("memory for the bytes"),
    );
    check_order("reading the names of a graph in binary", n, 1, |k| {
        binary::decode(if k == n { &small_bytes } else { &large_bytes }).unwrap();
    });
}
