//! The kernel address of a string costs the rules of its canonical parse, not its bytes
//! (CANON-term-string-nodes): the benchmarks of `string_nodes.rs`, whose tests serialize a
//! string of 2^30 bytes in 30 nodes and strings of one text in several trees.

use zed_kernel::term::build::lit;
use zed_kernel::text::Text;
use zed_kernel::value::Value;
use zed_tests::scaling::{check_order, inputs};
use zed_tests::seed::Xorshift64;
use zedc::canon::{self, Def};

fn holding(t: Text) -> Def {
    Def {
        name: "s".into(),
        domain: None,
        facets: vec![],
        body: lit(Value::Str(t)),
    }
}

/// `n` distinct blocks of 200 bytes joined, and the result doubled 40 times: about `2^48 n`
/// bytes in O(n) nodes, as `l01_31_zir::bench::shared_strings` builds it.
fn shared(n: usize) -> Text {
    let mut t = Text::from("");
    for i in 0..n {
        t = Text::join(&t, &Text::from(format!("{i:0>200}"))).unwrap();
    }
    (0..40).fold(t, |t, _| Text::join(&t, &t).expect("under 2^64 bytes"))
}

#[test]
fn a_shared_string_is_addressed_by_its_distinct_content() {
    let n = 200;
    let defs = inputs(n, |k| holding(shared(k)));
    let none = |_: &str| None;
    check_order("the kernel address of a shared string", n, 1, |k| {
        canon::address(&defs[&k], &none).expect("memory for the bytes");
    });
}

#[test]
fn a_flat_string_is_addressed_in_time_linear_in_its_bytes() {
    // One block of n bytes with no repeats longer than a few bytes: the parse makes about n/3
    // rules (348,644 for 1 MiB), each hashed and written once. The count of rules depends on
    // the bytes drawn, so the stream of the generator the limit was measured on is kept.
    let n = 1 << 15;
    let bytes = |k: usize| -> String {
        let mut x = Xorshift64::new(0x9e37_79b9_7f4a_7c15);
        (0..k)
            .map(|_| char::from(b'a' + x.below(26) as u8))
            .collect()
    };
    let defs = inputs(n, |k| holding(Text::from(bytes(k))));
    let none = |_: &str| None;
    check_order("the kernel address of a flat string", n, 1, |k| {
        canon::address(&defs[&k], &none).expect("memory for the bytes");
    });
}
