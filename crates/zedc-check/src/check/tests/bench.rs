//! The tests of `check::tests` at unusual sizes (author P178), run by `tools/run_tests.sh
//! --bench` and left out of its default run (TEST-bench-move-crates). The correctness test that
//! keeps what this checks at small sizes is
//! `one_shape_per_length_joins_each_length_once_through_shared_parts`.

use super::*;

/// The type of `min` of two tuples nested 20,000 deep, one with an `int` at the bottom and
/// one with an `f64`, is joined at every level on the 8 MiB stack of a main thread: one
/// shape per level, `int | f64` at the bottom. Joined by recursion, once per level, it
/// overflowed that stack.
#[test]
fn one_shape_per_length_joins_a_tuple_nested_deep_on_a_main_sized_stack() {
    const DEPTH: usize = 20_000;
    let (int, f64) = (Ty::carrier(Carrier::Int), Ty::carrier(Carrier::F64));
    let both = nested(int.clone(), DEPTH).union(&nested(f64.clone(), DEPTH));
    assert_eq!(both.tuples.len(), 2);
    let want = digest(&nested(int.union(&f64), DEPTH));
    let joined = crate::scaling::on_a_stack(8 << 20, || {
        let joined = one_shape_per_length(&both);
        (joined.tuples.len(), digest(&joined))
    });
    assert_eq!(joined, (1, want));
}

/// Plan row PERF-value-key-sites-bench: n integer literals, each written in decimal and then in
/// hex, half of them 64-bit and half past 64 bits, recorded by [`Ck::spells`] and each printed
/// again by [`Ck::spelling`]. `spelled` takes n keys and `mixed` n, each found by one hash, O(1)
/// expected compares and a tree of two spans: O(n) in all, as long as the hash tells the values
/// apart. The text, the values and their spans are built before timing; a run makes the checker
/// (O(1)), records the 2n literals and reads n spellings. The correctness test that keeps this
/// at small sizes is `equal_literal_values_are_one_key_of_the_spellings`.
#[test]
fn the_spellings_of_literals_written_two_ways_scale() {
    use num_bigint::BigInt;
    let res = zedc_resolve::resolve::resolve(&[]).expect("the empty unit resolves");
    let inputs = crate::scaling::inputs(20_000, |n| {
        let mut text = String::new();
        let mut written = Vec::with_capacity(2 * n);
        for k in 0..n as u64 {
            let x = match k % 2 {
                0 => BigInt::from(k),
                _ => (BigInt::from(u64::MAX) << 8) + k,
            };
            for s in [x.to_string(), format!("0x{}", x.to_str_radix(16))] {
                let start = text.len();
                text.push_str(&s);
                let end = text.len();
                text.push(' ');
                written.push((Value::int(x.clone()), Span { start, end }));
            }
        }
        (text, written)
    });
    crate::scaling::check_order(
        "the spellings of n integer literals written in decimal and in hex",
        20_000,
        1,
        |n| {
            let (text, written) = &inputs[&n];
            let mut t = Tables::new(&[], &res);
            t.text = Some(text);
            let mut ck = checker(&t);
            for (v, span) in written {
                ck.spells(v, *span);
            }
            assert_eq!((ck.spelled.len(), ck.mixed.len()), (n, n));
            for (v, span) in written.iter().step_by(2) {
                let want = &text[span.start..span.end];
                assert_eq!(ck.spelling(v).text.as_deref(), Some(want));
            }
        },
    );
}
