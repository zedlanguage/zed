//! Sets kept as ranges met with one class (row DOMAINS-classed-sets): a preimage whose set is
//! every `m`-th integer of some ranges keeps it exact as a class, with no value listed, and
//! prints it as the refinement type the program itself writes (DESIGN "Types in a message").

use super::s22::{int, prim, var};
use super::{pre, shown};
use zed_kernel::{Prim, Term};
use zedc::lex::lex;
use zedc::parse::{TOP, parse};
use zedc::store::classed::Classed;
use zedc::store::interval::{End, IntervalSet};
use zedc::store::lattice::Congruence;
use zedc::store::preimage::{Demand, Domains, preimage};

/// Whether `text` parses as a type, at the top ring, with the grammar of `zed/grammar`.
fn parses_as_type(text: &str) -> Result<(), String> {
    let tokens = lex(text).map_err(|e| format!("{text}: {e}"))?;
    parse(text, &tokens, "Type", TOP)
        .map(|_| ())
        .map_err(|e| format!("{text}: {e}"))
}

/// The printed form of a classed set: the ranges as a type, then `where x mod m == r`, in the
/// `FieldType` parentheses with the bound name `x` where the set stands alone, and as a
/// binding's type with no parentheses where it has a name. Every text parses as a `Type` with
/// the grammar unchanged. A set with every integer as its class prints its ranges alone, and a
/// set of points with a common gap prints as its class, the same text as the class made by
/// hand: two equal sets print the same; and where its members print no longer, as they do.
#[test]
fn a_classed_set_prints_as_a_refinement_that_parses() {
    let class = |m: i64, r: i64| Congruence::new(m, r);
    let one = Classed::new(IntervalSet::of(0, 1000), class(10, 3));
    assert_eq!(one.type_text(None), "(x: int[3..=993] where x mod 10 == 3)");
    assert_eq!(one.type_text(Some("i")), "int[3..=993] where i mod 10 == 3");
    let two_ranges =
        IntervalSet::from_pieces(vec![(End::of(0), End::of(9)), (End::of(20), End::of(31))]);
    let two = Classed::new(two_ranges, class(2, 0));
    assert_eq!(
        two.type_text(None),
        "(x: int[0..=8, 20..=30] where x mod 2 == 0)"
    );
    let points = IntervalSet::from_pieces(
        [3, 13, 23, 33, 43]
            .map(|v| (End::of(v), End::of(v)))
            .to_vec(),
    );
    let listed = Classed::plain(points);
    assert_eq!(listed, Classed::new(IntervalSet::of(3, 43), class(10, 3)));
    assert_eq!(
        listed.type_text(None),
        "(x: int[3..=43] where x mod 10 == 3)"
    );
    // Where the members print no longer than the class, they print: 1 and 4 are the class
    // `1 mod 3` within `[1, 4]`, 29 characters as a class and 17 listed, as `{3, 13, 23}`,
    // 31 against 28; the members of a set with a class of no two members one modulus apart
    // always print shorter, as `{3, 7, 13, 17}`.
    let short = |vs: &[i64]| {
        Classed::plain(IntervalSet::from_pieces(
            vs.iter().map(|&v| (End::of(v), End::of(v))).collect(),
        ))
    };
    assert_eq!(short(&[1, 4]).class, class(3, 1));
    assert_eq!(short(&[1, 4]).type_text(None), "int[1..=1, 4..=4]");
    assert_eq!(short(&[1, 4]).to_string(), "[1..=1, 4..=4]");
    assert_eq!(
        short(&[3, 13, 23]).type_text(Some("i")),
        "int[3..=3, 13..=13, 23..=23]"
    );
    assert_eq!(
        short(&[3, 7, 13, 17]).type_text(None),
        "int[3..=3, 7..=7, 13..=13, 17..=17]"
    );
    let plain = Classed::plain(IntervalSet::of(0, 9));
    assert_eq!(plain.type_text(None), "int[0..=9]");
    for text in [
        one.type_text(None),
        two.type_text(None),
        listed.type_text(None),
        plain.type_text(None),
        format!("{} | int[40..=50]", one.type_text(None)),
        one.type_text(Some("i")),
    ] {
        parses_as_type(&text).unwrap_or_else(|e| panic!("does not parse: {e}"));
    }
}

/// `i mod m == r`, the term asked `true`.
pub(crate) fn remainder_is(m: i64, r: i64) -> Term {
    prim(Prim::Eq, prim(Prim::Mod, var("i"), int(m)), int(r))
}

/// The domains `i` in `[0, n]`.
pub(crate) fn i_upto(n: i64) -> Domains {
    [("i".into(), IntervalSet::of(0, n))].into_iter().collect()
}

/// The preimage of `i mod m == r` over `[0, n]`, checked to be the class exactly with no value
/// listed: its count of values grows with `n`, its ranges do not.
pub(crate) fn check_class_unlisted(n: i64, m: i64, r: i64) {
    let p = preimage(&remainder_is(m, r), &i_upto(n), &Demand::Bool(true));
    assert!(p.exact, "{p:?}");
    let i = &p.domains["i"];
    let top = n - (n - r).rem_euclid(m);
    assert_eq!(
        *i,
        Classed::new(IntervalSet::of(r, top), Congruence::new(m, r))
    );
    assert_eq!(i.ranges.len(), 1, "{i:?}");
    assert_eq!(i.count(), ((top - r) / m + 1) as u64);
}

/// The l01_25 entry `i mod 10 == 3` over `[0, 10^9]`, which listed 10^8 values: now one class,
/// exact, printed as the binding of `i`.
#[test]
fn a_remainder_over_many_periods_is_one_class_exact() {
    check_class_unlisted(1_000_000_000, 10, 3);
    check_class_unlisted(40, 10, 3);
    check_class_unlisted(1000, 7, 0);
    let p = pre(
        "ok(i) = i mod 10 == 3;\n",
        &[("i", Some(0), Some(1_000_000_000))],
        &Demand::Bool(true),
    );
    assert_eq!(
        shown(&p),
        "i: int[3..=999999993] where i mod 10 == 3; exact"
    );
}
