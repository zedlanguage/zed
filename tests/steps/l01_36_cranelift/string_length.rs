//! A string's length past the address range (COMPLEXITY.md R5): a string doubled `k` times,
//! `s = s ++ s`, shares its halves, so it takes `k` nodes whatever its length, and its length
//! in bytes is `2^k` times the first. Up to `2^63` bytes the length is kept exactly and `len`
//! reads it without writing the text out, past `i64::MAX` as a big integer; at `2^64` bytes it
//! is not representable, and `++` refuses with its own error, natively and in the kernel.

use zed_kernel::term::build::{let_, lit, prim, var};
use zed_kernel::{Prim, Term, Value};

use super::{kernel, native};

/// `s0 = block; s1 = s0 ++ s0; …; len(sk)`: a block doubled `k` times, as a test fixture
/// filling a buffer by doubling a block does.
fn doubled(block: &str, k: u32) -> Term {
    let mut body = prim(Prim::Len, vec![var(&format!("s{k}"))]);
    for i in (1..=k).rev() {
        let before = var(&format!("s{}", i - 1));
        body = let_(
            &format!("s{i}"),
            prim(Prim::Concat, vec![before.clone(), before]),
            body,
        );
    }
    let_("s0", lit(block), body)
}

/// `len` of `block` doubled `k` times, natively and in the kernel, and the native run's
/// kernel calls.
fn len_both(block: &str, k: u32) -> (Value, Value, u64) {
    let t = doubled(block, k);
    let o = native(&t).unwrap();
    (o.value, kernel(&t).unwrap(), o.kernel_calls)
}

/// The refusal of `++` when the two halves are `2^63` bytes each.
const TOO_LONG: &str = "String too long: `++` would join strings of 8.0 EiB and 8.0 EiB, 16 EiB in \
                        all; a string holds at most 2^64 - 1 bytes. Keep the parts apart, as a \
                        list of strings written out one at a time, or join fewer of them";

#[test]
fn a_string_doubled_to_2_62_bytes_has_its_length_natively() {
    let (n, k, calls) = len_both("a", 62);
    assert_eq!(n, Value::Int(1 << 62));
    assert_eq!(k, n);
    assert_eq!(calls, 0, "len reads the kept count natively");
}

#[test]
fn a_string_doubled_to_2_63_bytes_has_a_big_length() {
    // 2^63 characters is one past `i64::MAX`, so `len` is a big integer, made by the kernel.
    let (n, k, calls) = len_both("a", 63);
    assert!(matches!(n, Value::Big(_)), "{n:?}");
    assert_eq!(n.to_string(), "9223372036854775808");
    assert_eq!(k, n);
    assert_eq!(calls, 1, "the one kernel call is the big len");
    // `ä` is two bytes: 2^63 bytes are 2^62 characters, which an `i64` holds.
    assert_eq!(
        len_both("ä", 62),
        (Value::Int(1 << 62), Value::Int(1 << 62), 0)
    );
}

#[test]
fn a_string_doubled_to_2_64_bytes_is_refused_natively_and_in_the_kernel() {
    for (block, k) in [("a", 64), ("ä", 63)] {
        let t = doubled(block, k);
        assert_eq!(kernel(&t).unwrap_err(), TOO_LONG, "{block} {k}");
        assert_eq!(native(&t).err().unwrap(), TOO_LONG, "{block} {k}");
    }
}

#[test]
fn the_empty_string_doubled_64_times_is_empty() {
    assert_eq!(len_both("", 64), (Value::Int(0), Value::Int(0), 0));
}

#[test]
fn a_string_joined_with_itself_reads_twice() {
    // "tōkyō" is 5 characters in 7 bytes.
    let t = let_(
        "s",
        lit("tōkyō"),
        let_(
            "ss",
            prim(Prim::Concat, vec![var("s"), var("s")]),
            prim(
                Prim::Tuple,
                vec![var("ss"), prim(Prim::Len, vec![var("ss")])],
            ),
        ),
    );
    let want = Value::tuple(vec![Value::str("tōkyōtōkyō"), Value::Int(10)]);
    assert_eq!(native(&t).unwrap().value, want);
    assert_eq!(kernel(&t).unwrap(), want);
}
