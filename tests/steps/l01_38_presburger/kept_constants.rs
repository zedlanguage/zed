//! Questions that hold a constant too wide to build (row PRES-kept-constants): the constant is a
//! symbol of its own, and a question is decided at its exact value, kept, never built
//! (`presburger::decide_at`): by the exact projection of the formula onto the symbol, ranges met
//! with one congruence class, against which the kept value is compared by its order and its
//! residue.

use num_bigint::BigUint;
use zed_kernel::num::Rat;
use zedc::store::interval::Num;
use zedc::store::presburger::exact::EXACT_LIMIT_SET;
use zedc::store::presburger::{Atom, Con, Formula, KeptSum, Lin, Shared, decide_at};

fn sym(n: &str) -> Lin {
    Lin::atom(Atom::Sym(n.into()))
}

fn ge(l: Lin, c: i64) -> Formula {
    Formula::Con(Con::ge(&l, &Lin::constant(c)))
}

fn le(l: Lin, c: i64) -> Formula {
    ge(l.times(-1), -c)
}

fn eq(l: Lin, c: i64) -> Formula {
    Formula::Con(Con::eq(&l, &Lin::constant(c)))
}

fn and(fs: Vec<Formula>) -> Formula {
    Formula::And(Shared::new(fs))
}

/// The symbol a kept constant is read as, `#k0`, the first of its scope.
pub(crate) fn k() -> Atom {
    Atom::Sym("#k0".into())
}

/// `3^e`, kept as a power: `Rat::pow` keeps a power of a prime by its exponent, and
/// `Num::from` keeps any value past `i128` as such a product (zedc-int `Num::power`), so
/// nothing as wide as the value is built.
pub(crate) fn three_to(e: &BigUint) -> Num {
    Num::from(
        &Rat::int(3.into())
            .pow(e)
            .expect("a power of a prime is kept"),
    )
}

/// `3^(2^40)`, about 1.7·10^12 bits written out.
fn wide() -> Num {
    three_to(&(BigUint::from(1u32) << 40u32))
}

/// `0 <= x <= 2^40 - 1 && 3 * x == #k0 + 1`. No point at `#k0 = 3^(2^40)`, since
/// `3 * x <= 3 * 2^40 - 3`; a point at `#k0 = 2^40 + 1`, `x = (2^40 + 2) / 3`.
pub(crate) fn first() -> Formula {
    let k = Lin::atom(k());
    and(vec![
        ge(sym("x"), 0),
        le(sym("x"), (1 << 40) - 1),
        eq(sym("x").times(3).plus(&k.times(-1)), 1),
    ])
}

/// `x == #k0 && x == 2 * t`: `#k0` even. No point at `3^(2^40)`, which is odd; one at `4`.
pub(crate) fn second() -> Formula {
    let k = Lin::atom(k());
    and(vec![
        eq(sym("x").plus(&k.times(-1)), 0),
        eq(sym("x").plus(&sym("t").times(-2)), 0),
    ])
}

/// The two counterexamples of `decide_at`'s note to reading a kept constant by its order
/// alone: each has no point at `3^(2^40)`. Negative control: each has one at a small value
/// that stands, as `3^(2^40)` does, above every other constant of its formula, so an answer
/// that reads the constant only by that order answers both alike, and is wrong at one of them.
/// The second, whose projection is the even integers, unbounded, is answered by the residue of
/// the value modulo 2 in the projection's periodic tail (row CLASSED-periodic-tail); before
/// that row it was refused for `Refusal::Repeats` at both values, its ranges wider than exact.
#[test]
fn a_kept_constant_is_decided_at_its_value_not_by_its_order() {
    let v = wide();
    assert!(v > Num::from(i128::MAX), "3^(2^40) is past i128");
    assert_eq!(
        decide_at(&first(), &k(), &v),
        Ok(false),
        "3 * x == 3^(2^40) + 1"
    );
    assert_eq!(
        decide_at(&second(), &k(), &v),
        Ok(false),
        "3^(2^40) is odd, so not even"
    );
    let control = Num::from((1i64 << 40) + 1);
    assert_eq!(decide_at(&first(), &k(), &control), Ok(true), "at 2^40 + 1");
    assert_eq!(decide_at(&second(), &k(), &Num::from(4)), Ok(true), "at 4");
}

/// Kept values that are members of an unbounded range, and not of a bounded one, and of a
/// class over unbounded values by their residue (`3^(2^40)` is `0 mod 9` and `1 mod 2`), read
/// in the projection's periodic tail (row CLASSED-periodic-tail; refused for
/// `Refusal::Repeats` before it).
#[test]
fn a_kept_constant_is_a_member_by_its_residue_and_its_range() {
    let v = wide();
    let kl = || Lin::atom(k());
    let nine = eq(kl().plus(&sym("t").times(-9)), 0);
    let nine_plus_one = eq(kl().plus(&sym("t").times(-9)), 1);
    let odd = eq(kl().plus(&sym("t").times(-2)), 1);
    let above = and(vec![ge(sym("x"), 0), ge(kl().plus(&sym("x").times(-1)), 0)]);
    let below = and(vec![
        ge(sym("x"), 0),
        le(sym("x"), 1 << 62),
        le(kl().plus(&sym("x").times(-1)), 0),
    ]);
    let cases = [
        (nine, Ok(true), "#k0 == 9 * t"),
        (nine_plus_one, Ok(false), "#k0 == 9 * t + 1"),
        (odd, Ok(true), "#k0 == 2 * t + 1"),
        (above, Ok(true), "#k0 >= x >= 0"),
        (below, Ok(false), "#k0 <= x <= 2^62"),
    ];
    for (f, want, what) in cases {
        assert_eq!(decide_at(&f, &k(), &v), want, "{what}: {f}");
    }
}

/// Two kept constants held in one combination are one symbol at one kept value
/// (`KeptSum`): `0 <= x <= 2^63 - 1 && x + 3^(2^40) - 2^(2^41) >= 1` has no point, since
/// `2^(2^41) = 4^(2^40)` exceeds `3^(2^40)` by far more than `x` adds, and its negation has
/// one. Negative control: the rewritten formula has a point at the value 1 of the symbol,
/// so the answer comes from the kept value. Two constants in two combinations,
/// `x <= 3^(2^40) && y <= 2^(2^41)`, are not one symbol.
#[test]
fn two_kept_constants_in_one_combination_are_one_symbol() {
    let two = Num::from(
        &Rat::int(2.into())
            .pow(&(BigUint::from(1u32) << 41u32))
            .expect("a power of a prime is kept"),
    );
    let (k0, k1) = (Atom::Sym("#k0".into()), Atom::Sym("#k1".into()));
    let kept = [(k0.clone(), wide()), (k1.clone(), two)];
    let term = (sym("x").plus(&Lin::atom(k0.clone()))).minus(&Lin::atom(k1.clone()));
    let f = and(vec![ge(sym("x"), 0), le(sym("x"), i64::MAX), ge(term, 1)]);
    let sum = KeptSum::of(&f, &kept).expect("one combination");
    assert!(sum.value < Num::ZERO, "3^(2^40) - 2^(2^41) is negative");
    let g = sum.rewrite(&f);
    assert_eq!(decide_at(&g, &sum.sym, &sum.value), Ok(false), "{g}");
    let negated = sum.rewrite(&Formula::negate(f.clone()));
    assert_eq!(
        decide_at(&negated, &sum.sym, &sum.value),
        Ok(true),
        "{negated}"
    );
    assert_eq!(decide_at(&g, &sum.sym, &Num::ONE), Ok(true), "control: {g}");
    let apart = and(vec![
        le(sym("x").minus(&Lin::atom(k0)), 0),
        le(sym("y").minus(&Lin::atom(k1)), 0),
    ]);
    assert!(KeptSum::of(&apart, &kept).is_none(), "two combinations");
}

/// A projection the cover refuses, here at a work limit of 0 units, refuses the question:
/// `decide_at` answers only from an exact set.
#[test]
fn a_kept_constant_whose_projection_is_refused_is_refused() {
    let kl = || Lin::atom(k());
    let f = and(vec![
        ge(sym("x"), 0),
        le(sym("x"), 100),
        Formula::Or(Shared::new(vec![
            eq(sym("x").times(3).plus(&kl().times(-1)), 0),
            eq(sym("x").times(5).plus(&kl().times(-1)), 1),
        ])),
        Formula::Or(Shared::new(vec![ge(sym("x"), 7), le(sym("x"), 3)])),
    ]);
    EXACT_LIMIT_SET.with(|l| l.set(Some(0)));
    let got = decide_at(&f, &k(), &wide());
    EXACT_LIMIT_SET.with(|l| l.set(None));
    assert!(got.is_err(), "answered past the limit: {got:?}");
    assert_eq!(
        decide_at(&f, &k(), &wide()),
        Ok(false),
        "at the usual limit"
    );
}
