//! The interpreter and native code agree on every word: each term is run by the kernel and by
//! the code Cranelift generates, and the values are compared. `codePoint` of a string of one
//! scalar runs in the runtime without a kernel call; the other words run in the kernel.

use zed_kernel::Term;
use zed_kernel::term::build::{let_, lit, prim, var};
use zed_kernel::{Prim, Value};

use super::{BOUNDARIES, from_one, from_zero};
use crate::l01_36_cranelift::{kernel, native};

fn agree(t: &Term) -> Value {
    let k = kernel(t).unwrap_or_else(|e| panic!("{t}: {e}"));
    let n = native(t).unwrap_or_else(|e| panic!("{t}: {e}"));
    assert_eq!(n.value, k, "{t}");
    k
}

fn one(p: Prim, v: impl Into<Value>) -> Term {
    prim(p, vec![lit(v)])
}

#[test]
fn code_point_agrees_and_needs_no_kernel_call_for_one_scalar() {
    for s in ["a", "é", "€", "😀", "\u{10FFFF}"] {
        let t = one(Prim::CodePoint, s);
        let v = agree(&t);
        assert_eq!(
            v,
            Value::Int(i64::from(u32::from(s.chars().next().unwrap())))
        );
        assert_eq!(native(&t).unwrap().kernel_calls, 0, "{s}");
    }
    for s in ["", "ab", "é😀"] {
        assert_eq!(
            agree(&one(Prim::CodePoint, s)),
            Value::atom("notScalar"),
            "{s}"
        );
    }
    // A join of two scalars is not one scalar; a join with the empty string is its other part.
    let joined = prim(Prim::Concat, vec![lit("a"), lit("b")]);
    assert_eq!(
        agree(&prim(Prim::CodePoint, vec![joined])),
        Value::atom("notScalar")
    );
    let empty_join = prim(Prim::Concat, vec![lit(""), lit("é")]);
    assert_eq!(
        agree(&prim(Prim::CodePoint, vec![empty_join])),
        Value::Int(233)
    );
}

#[test]
fn scalar_agrees_at_every_boundary_and_outside() {
    for c in BOUNDARIES {
        agree(&one(Prim::Scalar, i64::from(c)));
    }
    for n in [-1, 0xD800, 0xDFFF, 0x110000, i64::MAX] {
        assert_eq!(
            agree(&one(Prim::Scalar, n)),
            Value::atom("notScalar"),
            "{n}"
        );
    }
}

#[test]
fn utf8_and_from_utf8_agree() {
    for s in [
        "",
        "a",
        "aé€😀",
        "\u{7F}\u{80}\u{7FF}\u{800}\u{FFFF}\u{10000}",
    ] {
        agree(&one(Prim::Utf8, s));
        let round = prim(Prim::FromUtf8, vec![one(Prim::Utf8, s)]);
        assert_eq!(agree(&round), Value::str(s), "{s}");
    }
    for b in [
        from_zero(&[192, 128]),
        from_one(&[0xED, 0xA0, 0x80]),
        from_one(&[0xE2, 0x82]),
        from_one(&[0x80]),
        from_one(&[256]),
        from_one(&[104, 105]),
    ] {
        agree(&one(Prim::FromUtf8, b));
    }
}

#[test]
fn a_string_read_twice_agrees() {
    // `s` is used by `codePoint` and by `utf8`, so the runtime borrows it for the first.
    let t = let_(
        "s",
        prim(Prim::Concat, vec![lit(""), lit("λ")]),
        prim(
            Prim::Tuple,
            vec![
                prim(Prim::CodePoint, vec![var("s")]),
                prim(Prim::FromUtf8, vec![prim(Prim::Utf8, vec![var("s")])]),
                var("s"),
            ],
        ),
    );
    assert_eq!(agree(&t).to_string(), "(955, \"λ\", \"λ\")");
}
