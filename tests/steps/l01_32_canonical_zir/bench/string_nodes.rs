//! The kernel address of a string costs its bytes (author answer A106, 2026-11-20): hashing a
//! string of L bytes is O(L) whatever the tree holding it, and a concatenation of strings of n
//! and m bytes is O(n + m) (proof at `Out::string`, crates/zedc-zir/src/canon/serial.rs). The
//! benchmarks of `string_nodes.rs`, whose tests check the bytes written at small sizes.

use zed_kernel::term::build::lit;
use zed_kernel::text::Text;
use zed_kernel::value::Value;
use zed_tests::scaling::{check, check_order, compare_costs, inputs};
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

/// `k` random lowercase letters, from a fixed stream.
fn letters(k: usize) -> String {
    let mut x = Xorshift64::new(0x9e37_79b9_7f4a_7c15);
    (0..k)
        .map(|_| char::from(b'a' + x.below(26) as u8))
        .collect()
}

#[test]
fn a_flat_string_is_addressed_in_time_linear_in_its_bytes() {
    let n = 1 << 17;
    let defs = inputs(n, |k| holding(Text::from(letters(k))));
    let none = |_: &str| None;
    check_order("the kernel address of a flat string", n, 1, |k| {
        canon::address(&defs[&k], &none).expect("memory for the bytes");
    });
}

/// A string of `k` bytes in each of five trees: pieces of 16 bytes joined from the left, from
/// the right and as a balanced tree; `"ab"` doubled; and the concatenation of a flat string of
/// k/2 bytes with a doubled one of k/2.
fn shapes(k: usize) -> [Text; 5] {
    let pieces: Vec<Text> = letters(k)
        .as_bytes()
        .chunks(16)
        .map(|c| Text::from(std::str::from_utf8(c).unwrap()))
        .collect();
    let join = |a: &Text, b: &Text| Text::join(a, b).expect("under 2^63 bytes");
    let left = pieces.iter().fold(Text::from(""), |t, p| join(&t, p));
    let right = pieces.iter().rev().fold(Text::from(""), |t, p| join(p, &t));
    fn balanced(ts: &[Text]) -> Text {
        match ts {
            [] => Text::from(""),
            [t] => t.clone(),
            _ => Text::join(
                &balanced(&ts[..ts.len() / 2]),
                &balanced(&ts[ts.len() / 2..]),
            )
            .expect("under 2^63 bytes"),
        }
    }
    let doubled = |len: usize| {
        let mut t = Text::from("ab");
        while t.len() < len {
            t = join(&t, &t);
        }
        t
    };
    let concat = join(&Text::from(letters(k / 2)), &doubled(k / 2));
    let all = [left, right, balanced(&pieces), doubled(k), concat];
    assert!(all.iter().all(|t| t.len() == k), "k a power of two");
    all
}

#[test]
fn a_string_of_any_tree_is_addressed_in_time_linear_in_its_bytes() {
    // k a power of two, so the doubled strings have k and k/2 bytes.
    let n = 1 << 17;
    let defs = inputs(n, |k| shapes(k).map(holding));
    let none = |_: &str| None;
    for (i, what) in [
        "the kernel address of a string joined from the left",
        "the kernel address of a string joined from the right",
        "the kernel address of a string joined as a balanced tree",
        "the kernel address of a doubled string",
        "the kernel address of a flat string concatenated with a doubled one",
    ]
    .into_iter()
    .enumerate()
    {
        check_order(what, n, 1, |k| {
            canon::address(&defs[&k][i], &none).expect("memory for the bytes");
        });
    }
}

/// Row PERF-canon-flat-strings (2026-11-15): when a string was written as the rules of its
/// canonical parse, a flat literal of 1 MiB cost 3,591 M instructions against 2.6 M to hash
/// its bytes. Written as its bytes, it costs a few copies and hashes of them.
#[test]
fn a_flat_literal_is_addressed_in_a_few_hashes_of_its_bytes() {
    let s = letters(1 << 20);
    let def = holding(Text::from(s.clone()));
    let none = |_: &str| None;
    compare_costs(
        "copying and hashing 1 MiB of bytes, then addressing a definition holding them as a string",
        "row PERF-canon-flat-strings: a flat literal costs at most 50 copies and hashes of its bytes",
        50.0,
        || {
            let copy = s.as_bytes().to_vec();
            std::hint::black_box(blake3::hash(&copy));
        },
        || {
            canon::address(&def, &none).expect("memory for the bytes");
        },
    );
}

/// Row PROOF-address-reads-literals-only: a program of n lines doubling `"ab"` with `++` is
/// addressed in time linear in its text, though the string it builds when run has 2^(n+1)
/// bytes; its small instance is `a_program_holding_a_doubled_string_is_addressed_by_its_text`.
#[test]
fn a_doubling_program_is_addressed_in_time_linear_in_its_text() {
    let n = 200;
    // Both programs are loaded before the runs are measured; the address is taken from the
    // ports and the term, as `Program::address` does, since that caches it after one run.
    let programs = inputs(n, |k| {
        zedc::run::load(super::super::string_nodes::doubling(k).as_bytes()).unwrap()
    });
    check(
        "the content address of a program doubling a string n times",
        n,
        |k| {
            let p = &programs[&k];
            std::hint::black_box(p.ports().address(p.term()).unwrap());
        },
    );
}
