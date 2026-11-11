//! A program that multiplies two integers read from its command line, built into an
//! executable, prints the interpreter's line and the exact product at the edges of the machine
//! word: "semantic `int` widens its domain instead of overflowing" (DESIGN.md sec:failure,
//! item 1), so `MIN * -1` is `2^63`, one past the word, and `MAX * MAX` is `2^126 - 2^64 + 1`,
//! the operands known only when the program runs.

use std::ffi::OsString;

use num_bigint::BigInt;

use super::{built, dir, executable, interpreter};

const MUL: &str = "\
main(m: MainArgs) {
  x = int(m.args[1] else \"\") else 0;
  y = int(m.args[2] else \"\") else 0;
  m.stdout <- \"${x * y}\";
}
";

const MIN: i128 = i64::MIN as i128;
const MAX: i128 = i64::MAX as i128;

#[test]
fn products_at_the_word_edges_are_exact_in_the_executable() {
    let d = dir("mul_edges");
    let src = d.join("mul.zed");
    std::fs::write(&src, MUL).unwrap();
    let exe = d.join("mul");
    built(&src, &exe);
    let mut n = 0;
    // The products the test audit named and those at the square root of the bound and at
    // `2^32 * 2^31`, each with every neighbor of each operand; a neighbor one past the word
    // the program reads as an unbounded integer.
    for (a, b) in [
        (MIN, -1),
        (-1, MIN),
        (MIN, MIN),
        (MAX, MAX),
        (MIN, 2),
        (3_037_000_499, 3_037_000_499),
        (-3_037_000_499, 3_037_000_500),
        (-(1 << 32), 1 << 31),
        (1 << 32, 1 << 31),
    ] {
        for i in -1..=1 {
            for j in -1..=1 {
                let (x, y) = (a + i, b + j);
                let words: Vec<OsString> =
                    vec!["--".into(), x.to_string().into(), y.to_string().into()];
                let native = executable(&exe, &words, b"");
                assert_eq!(native, interpreter(&src, &words, b""), "{x} * {y}");
                let want = format!("{}\n", BigInt::from(x) * BigInt::from(y));
                assert_eq!((native.status, native.stdout), (0, want), "{x} * {y}");
                n += 1;
            }
        }
    }
    assert_eq!(n, 81);
}
