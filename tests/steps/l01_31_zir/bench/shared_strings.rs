//! A string held in shared nodes costs its distinct nodes, not its bytes, to write in binary,
//! read back, hash and compare (BUILD-doubling-60s): the benchmark of `binary_forms.rs`, whose
//! test writes a string doubled 62 times, and of the kernel's text tests, which hash and
//! compare such strings at small sizes.

use std::cmp::Ordering;
use std::collections::HashMap;

use zed_kernel::text::Text;
use zed_kernel::value::Value;
use zed_tests::scaling::{check_order, inputs};
use zedc::zir::{Src, binary};

use crate::binary_forms::holding;

/// `n` distinct blocks of 200 bytes, two of which never share a block, joined, and the result
/// doubled 40 times: about `2^48 n` bytes in O(n) nodes.
fn shared(n: usize) -> Text {
    let mut t = Text::from("");
    for i in 0..n {
        t = Text::join(&t, &Text::from(format!("{i:0>200}"))).unwrap();
    }
    (0..40).fold(t, |t, _| Text::join(&t, &t).expect("under 2^64 bytes"))
}

#[test]
fn a_shared_string_costs_its_nodes() {
    let n = 1_000;
    let texts = inputs(n, shared);
    check_order("writing a shared string in binary", n, 1, |k| {
        binary::encode(&holding(texts[&k].clone())).expect("memory for the bytes");
    });
    let data: HashMap<usize, Vec<u8>> = texts
        .iter()
        .map(|(&k, t)| (k, binary::encode(&holding(t.clone())).unwrap()))
        .collect();
    check_order("reading a shared string in binary", n, 1, |k| {
        let g = binary::decode(&data[&k]).unwrap();
        assert!(matches!(&g.results[0], Src::Const(Value::Str(_))));
    });
    check_order("hashing a shared string", n, 1, |k| {
        std::hint::black_box(texts[&k].poly_hash());
    });
    // The same string with a last byte more: the compare skips the shared nodes and reads
    // the last block.
    let longer: HashMap<usize, Text> = texts
        .iter()
        .map(|(&k, t)| (k, Text::join(t, &Text::from("c")).unwrap()))
        .collect();
    check_order("comparing two shared strings", n, 1, |k| {
        assert_eq!(texts[&k].cmp(&longer[&k]), Ordering::Less);
    });
}
