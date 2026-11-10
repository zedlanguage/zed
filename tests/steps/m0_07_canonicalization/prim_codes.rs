//! The canonical serialization writes a primitive by its fixed number, [`Prim::code`], so that
//! renaming a variant or adding one cannot change any address (repair PRIM-hidden-names). The
//! numbers are written out here: a change to any of them fails this test, and a change to the
//! numbers needs a new canonicalization VERSION and new pinned addresses.

use zed_kernel::Prim;
use zedc::zir::text::PRIMS;

const CODES: [(Prim, u64); 63] = [
    (Prim::Add, 0),
    (Prim::Sub, 1),
    (Prim::Mul, 2),
    (Prim::Div, 3),
    (Prim::IntDiv, 4),
    (Prim::Mod, 5),
    (Prim::Neg, 6),
    (Prim::Eq, 7),
    (Prim::Ne, 8),
    (Prim::Lt, 9),
    (Prim::Le, 10),
    (Prim::Gt, 11),
    (Prim::Ge, 12),
    (Prim::And, 13),
    (Prim::Or, 14),
    (Prim::Not, 15),
    (Prim::Min, 16),
    (Prim::Max, 17),
    (Prim::Get, 18),
    (Prim::Count, 19),
    (Prim::Union, 20),
    (Prim::Path, 21),
    (Prim::PathKey, 22),
    (Prim::PathLen, 23),
    (Prim::Tuple, 24),
    (Prim::TupleGet, 25),
    (Prim::Concat, 26),
    (Prim::Pow, 27),
    (Prim::Atom, 28),
    (Prim::Show, 29),
    (Prim::CastInt, 30),
    (Prim::CastRat, 31),
    (Prim::CastF64, 32),
    (Prim::Abs, 33),
    (Prim::Len, 34),
    (Prim::Lower, 35),
    (Prim::Upper, 36),
    (Prim::Trim, 37),
    (Prim::Sum, 38),
    (Prim::BitAnd, 39),
    (Prim::BitOr, 40),
    (Prim::BitXor, 41),
    (Prim::BitNot, 42),
    (Prim::Shl, 43),
    (Prim::Shr, 44),
    (Prim::PopCount, 45),
    (Prim::LeadingZeros, 46),
    (Prim::TrailingZeros, 47),
    (Prim::Rotl, 48),
    (Prim::Rotr, 49),
    (Prim::F64Bits, 50),
    (Prim::CodePoint, 51),
    (Prim::Scalar, 52),
    (Prim::Utf8, 53),
    (Prim::FromUtf8, 54),
    (Prim::MulHi, 55),
    (Prim::BitReverse, 56),
    (Prim::ByteSwap, 57),
    (Prim::Pdep, 58),
    (Prim::Pext, 59),
    (Prim::FunnelShl, 60),
    (Prim::FunnelShr, 61),
    (Prim::At, 62),
];

#[test]
fn each_primitive_keeps_its_number() {
    for (p, n) in CODES {
        assert_eq!(p.code(), n, "{p:?}");
    }
}

/// Every primitive is in the table once, and no two share a number. The ZIR text form lists
/// every primitive, so the table covering it covers them all.
#[test]
fn the_numbers_cover_every_primitive_once() {
    assert_eq!(CODES.len(), PRIMS.len());
    let mut numbers: Vec<u64> = PRIMS.iter().map(|p| p.code()).collect();
    numbers.sort_unstable();
    numbers.dedup();
    assert_eq!(numbers.len(), PRIMS.len());
    for p in PRIMS {
        assert!(
            CODES.iter().any(|(q, _)| *q == p),
            "{p:?} is not in the table"
        );
    }
}

/// Two terms that differ only in their primitive have different addresses.
#[test]
fn the_number_reaches_the_address() {
    use zed_kernel::term::build::{lit, prim};
    let a = super::def("x", prim(Prim::Add, vec![lit(1), lit(2)]));
    let b = super::def("x", prim(Prim::Sub, vec![lit(1), lit(2)]));
    assert_ne!(super::addr(&a), super::addr(&b));
}
