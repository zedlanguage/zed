//! The cases COMPLETENESS.md lists that the other files of this group leave out: each
//! primitive written in a term at its arity, a term with every variant compared and copied
//! when built apart, a part changed in place, and a pattern's `Debug` alone.

use zed_kernel::term::build::{prim, var};
use zed_kernel::term::{Pattern, Prim};
use zed_kernel::types::Type;
use zed_kernel::{Shared, Term, Value};
use zedc::zir::text::PRIMS;

use super::deep::every_variant;

/// Each primitive applied to `a`, `b`, ... at its arity (two for one of any arity), as the
/// printer writes it: an operator between its operands in parentheses, `-` and `!` before
/// one, an entry or component as an index, an atom with no literal name as `#_(..)`, and
/// every other primitive as its prelude word called.
const WRITTEN: [(Prim, &str); 66] = [
    (Prim::Add, "(a + b)"),
    (Prim::Sub, "(a - b)"),
    (Prim::Mul, "(a * b)"),
    (Prim::Div, "(a / b)"),
    (Prim::IntDiv, "(a div b)"),
    (Prim::Mod, "(a mod b)"),
    (Prim::Neg, "-a"),
    (Prim::Eq, "(a == b)"),
    (Prim::Ne, "(a != b)"),
    (Prim::Lt, "(a < b)"),
    (Prim::Le, "(a <= b)"),
    (Prim::Gt, "(a > b)"),
    (Prim::Ge, "(a >= b)"),
    (Prim::And, "(a && b)"),
    (Prim::Or, "(a || b)"),
    (Prim::Not, "!a"),
    (Prim::Min, "min(a, b)"),
    (Prim::Max, "max(a, b)"),
    (Prim::Get, "a[b]"),
    (Prim::Count, "count(a)"),
    (Prim::Union, "union(a, b)"),
    (Prim::Path, "path(a, b)"),
    (Prim::PathKey, "pathKey(a, b)"),
    (Prim::PathLen, "pathLen(a)"),
    (Prim::Tuple, "(a, b)"),
    (Prim::TupleGet, "a[b]"),
    (Prim::Concat, "(a ++ b)"),
    (Prim::Pow, "(a^b)"),
    (Prim::Atom, "#_()"),
    (Prim::Show, "String(a)"),
    (Prim::CastInt, "int(a)"),
    (Prim::CastRat, "rat(a)"),
    (Prim::CastF64, "f64(a)"),
    (Prim::Abs, "abs(a)"),
    (Prim::Len, "len(a)"),
    (Prim::Lower, "lower(a)"),
    (Prim::Upper, "upper(a)"),
    (Prim::Trim, "trim(a)"),
    (Prim::Sum, "sum(a)"),
    (Prim::BitAnd, "bitAnd(a, b)"),
    (Prim::BitOr, "bitOr(a, b)"),
    (Prim::BitXor, "bitXor(a, b)"),
    (Prim::BitNot, "bitNot(a, b)"),
    (Prim::Shl, "shl(a, b)"),
    (Prim::Shr, "shr(a, b)"),
    (Prim::PopCount, "popCount(a)"),
    (Prim::LeadingZeros, "leadingZeros(a, b)"),
    (Prim::TrailingZeros, "trailingZeros(a, b)"),
    (Prim::Rotl, "rotl(a, b, c)"),
    (Prim::Rotr, "rotr(a, b, c)"),
    (Prim::F64Bits, "f64Bits(a)"),
    (Prim::CodePoint, "codePoint(a)"),
    (Prim::Scalar, "scalar(a)"),
    (Prim::Utf8, "utf8(a)"),
    (Prim::FromUtf8, "fromUtf8(a)"),
    (Prim::MulHi, "mulHi(a, b, c)"),
    (Prim::BitReverse, "bitReverse(a, b)"),
    (Prim::ByteSwap, "byteSwap(a, b)"),
    (Prim::Pdep, "pdep(a, b)"),
    (Prim::Pext, "pext(a, b)"),
    (Prim::FunnelShl, "funnelShl(a, b, c, d)"),
    (Prim::FunnelShr, "funnelShr(a, b, c, d)"),
    (Prim::At, "a[b]"),
    (Prim::CastF32, "f32(a)"),
    (Prim::Sqrt, "sqrt(a)"),
    (Prim::Fma, "fma(a, b, c)"),
];

#[test]
fn each_primitive_is_written_at_its_arity() {
    // `PRIMS` lists every primitive, so a new one fails here until it has a row.
    assert_eq!(PRIMS.len(), WRITTEN.len());
    for (p, (q, text)) in PRIMS.into_iter().zip(WRITTEN) {
        assert_eq!(p, q, "WRITTEN in the order of PRIMS");
        let n = p.arity().unwrap_or(2);
        let args = ["a", "b", "c", "d"][..n].iter().map(|x| var(x)).collect();
        assert_eq!(prim(p, args).to_string(), text, "{p:?}");
    }
}

#[test]
fn a_term_of_every_variant_built_twice_is_equal_to_itself_and_its_copy() {
    // Built apart, the two share no subterm, so `==` walks every variant and pattern.
    let (a, b) = (every_variant(), every_variant());
    assert!(a == b);
    let copy = a.clone();
    assert!(copy == b);
    assert_eq!(format!("{copy:?}"), format!("{b:?}"));
}

#[test]
fn each_variant_differs_from_every_other_and_from_itself_changed() {
    let all = every_variant();
    let Term::Prim(_, parts) = &all else {
        unreachable!("every_variant is a tuple of its parts")
    };
    for (i, a) in parts.iter().enumerate() {
        for (j, b) in parts.iter().enumerate() {
            assert_eq!(a == b, i == j, "part {i} against part {j}");
        }
    }
    let sh = Shared::new;
    let pairs = [
        (Term::PrimFn(Prim::Add), Term::PrimFn(Prim::Sub)),
        (
            Term::Push("out".into(), sh(var("v"))),
            Term::Push("err".into(), sh(var("v"))),
        ),
        (
            Term::Push("out".into(), sh(var("v"))),
            Term::Push("out".into(), sh(var("w"))),
        ),
        (
            Term::Let("x".into(), sh(var("a")), sh(var("x"))),
            Term::Let("y".into(), sh(var("a")), sh(var("x"))),
        ),
        (
            Term::Let("x".into(), sh(var("a")), sh(var("x"))),
            Term::Let("x".into(), sh(var("a")), sh(var("a"))),
        ),
        (
            Term::Fam {
                domain: sh(var("D")),
                var: "i".into(),
                body: sh(var("i")),
            },
            Term::Fam {
                domain: sh(var("D")),
                var: "j".into(),
                body: sh(var("i")),
            },
        ),
    ];
    for (a, b) in pairs {
        assert!(a != b, "{a} against {b}");
    }
}

#[test]
fn patterns_differ_by_each_of_their_parts() {
    let arm = |p: Pattern| Term::Match(Shared::new(var("v")), vec![(p, var("r"))]);
    let fields =
        |name: &str, field: &str, p: Pattern| Pattern::Fields(name.into(), vec![(field.into(), p)]);
    let pairs = [
        (Pattern::Lit(Value::Int(3)), Pattern::Lit(Value::Int(4))),
        (
            fields("node", "next", Pattern::AnyAtom),
            fields("leaf", "next", Pattern::AnyAtom),
        ),
        (
            fields("node", "next", Pattern::AnyAtom),
            fields("node", "prev", Pattern::AnyAtom),
        ),
        (
            fields("node", "next", Pattern::AnyAtom),
            fields("node", "next", Pattern::Wild),
        ),
        (Pattern::Is(Type::int()), Pattern::Wild),
    ];
    for (p, q) in pairs {
        assert!(p != q, "{p} against {q}");
        assert!(
            arm(p.clone()) != arm(q.clone()),
            "{p} against {q} in an arm"
        );
        assert!(arm(p.clone()) == arm(p.clone()), "{p} against itself");
    }
}

#[test]
fn a_pattern_alone_debugs_as_derived() {
    let p = Pattern::Fields(
        "node".into(),
        vec![("next".into(), Pattern::Lit(Value::Int(3)))],
    );
    assert_eq!(
        format!("{p:?}"),
        "Fields(\"node\", [(\"next\", Lit(Int(3)))])"
    );
}

#[test]
fn a_part_changed_in_place_takes_a_new_id_and_a_shared_one_is_copied_first() {
    let mut alone: Shared = var("x").into();
    let id = alone.id();
    *Shared::make_mut(&mut alone) = var("y");
    assert_ne!(alone.id(), id);
    assert_eq!(alone.to_string(), "y");

    let mut held = Shared::new(var("x"));
    let other = held.clone();
    *Shared::make_mut(&mut held) = var("y");
    assert_ne!(held.id(), other.id());
    assert_eq!(
        (held.to_string(), other.to_string()),
        ("y".into(), "x".into())
    );
    assert_eq!(Shared::strong_count(&other), 1);
}
