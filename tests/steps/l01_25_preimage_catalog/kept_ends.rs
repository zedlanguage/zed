//! Preimages whose bounds are powers and roots far past i64: the bounds stay in kept forms, so
//! the preimage takes no time to write out their digits.

use super::pre;
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::preimage::Demand;

fn timed<R>(what: &str, f: impl FnOnce() -> R) -> R {
    let start = std::time::Instant::now();
    let r = f();
    let took = start.elapsed();
    assert!(
        took < std::time::Duration::from_secs(1),
        "{what} took {took:?}"
    );
    r
}

#[test]
fn a_sum_with_a_large_power_has_its_preimage_without_the_digits() {
    // Every x in 2..=3 meets `x ** 10^8 + 1 >= 50`, and so does every x in it for `x ** 10^8`.
    for src in [
        "ok(x) = x ** 100000000 + 1 >= 50;\n",
        "ok(x) = x ** 100000000 >= 50;\n",
        "ok(x) = 3 * x ** 100000000 - 1 >= 50;\n",
    ] {
        let p = timed(src, || {
            pre(src, &[("x", Some(2), Some(3))], &Demand::Bool(true))
        });
        assert_eq!(p.domains["x"], IntervalSet::of(2, 3), "{src}");
    }
}

#[test]
fn a_power_under_a_large_power_has_a_root_bound() {
    // `x ** 3 <= 2 ** 10^8` holds for x up to the floor of the cube root of 2^(10^8), an
    // irrational root of about 3.3 * 10^7 bits; `x ** 4 <= 2 ** 10^8` up to 2^(2.5 * 10^7).
    let k = 100_000_000;
    let two = Num::from(2).pow(k);
    for (src, r) in [
        ("ok(x) = x ** 3 <= 2 ** 100000000;\n", 3),
        ("ok(x) = x ** 4 <= 2 ** 100000000;\n", 4),
    ] {
        let p = timed(src, || pre(src, &[("x", None, None)], &Demand::Bool(true)));
        let root = two.floor_root(r);
        let x = &p.domains["x"];
        let (lo, hi) = x.bounds().expect("a range");
        assert_eq!(*hi, End::Fin(root.clone()), "{src}");
        if r % 2 == 0 {
            assert_eq!(*lo, End::Fin(-&root), "{src}");
        } else {
            assert_eq!(*lo, End::NegInf, "{src}");
        }
        assert_eq!(x.pieces().len(), 1, "{src}");
    }
}

/// `if i >= c { i } else { i + 100 }` with an end of the domain or of the demand past `i64`,
/// where the piecewise-affine summary gives up and each arm is read by the catalog; the same
/// chain on a domain unbounded on both sides, whose infinities must not be read as the ends of
/// `i64`; and the chain inside `i64`, where the summary reads it. Every answer is exact.
#[test]
fn an_if_chain_over_ends_past_i64_is_read_arm_by_arm() {
    use num_bigint::BigInt;
    use std::sync::Arc;
    use zed_kernel::{Prim, Term, Value};
    use zedc::store::preimage::{Domains, preimage};
    let big = |k: i64| &Num::from(BigInt::from(1) << 70u32) + &Num::from(k);
    let lit = |n: &Num| Term::Lit(Value::from(n));
    let chain_by = |c: &Num, by: i64| {
        let i = Term::Var("i".into());
        let guard = Term::Prim(Prim::Ge, vec![i.clone(), lit(c)]);
        let other = Term::Prim(Prim::Add, vec![i.clone(), Term::Lit(Value::Int(by))]);
        Term::If(Arc::new(guard), Arc::new(i), Arc::new(other))
    };
    let chain = |c: &Num| chain_by(c, 100);
    let on =
        |lo: End, hi: End| -> Domains { [(Arc::from("i"), IntervalSet::range(lo, hi))].into() };
    let fin = |n: Num| End::Fin(n);
    let cases = [
        // The domain's ends past `i64`: only the else arm reaches the demand.
        (
            chain(&big(5)),
            on(fin(big(0)), fin(big(10))),
            IntervalSet::range(fin(big(100)), fin(big(105))),
            IntervalSet::range(fin(big(0)), fin(big(4))),
        ),
        // The demand's end past `i64` on a domain unbounded above: the then arm from `2^70` up.
        (
            chain(&Num::from(5)),
            on(End::of(0), End::PosInf),
            IntervalSet::range(fin(big(0)), End::PosInf),
            IntervalSet::range(fin(big(0)), End::PosInf),
        ),
        // A demand at the end of `i64` on a domain unbounded above.
        (
            chain(&Num::from(5)),
            on(End::of(0), End::PosInf),
            IntervalSet::range(End::of(i64::MAX - 1), End::of(i64::MAX)),
            IntervalSet::of(i64::MAX - 1, i64::MAX),
        ),
        // A domain unbounded on both sides, which the summary reads with the ends of `i64`
        // standing for the infinities: the else arm `i - 100` runs down to minus infinity.
        (
            chain_by(&Num::from(5), -100),
            on(End::NegInf, End::PosInf),
            IntervalSet::range(End::NegInf, End::of(-1000)),
            IntervalSet::range(End::NegInf, End::of(-900)),
        ),
        // The same domain with a demand inside `i64` that both arms reach.
        (
            chain_by(&Num::from(5), -100),
            on(End::NegInf, End::PosInf),
            IntervalSet::of(-200, 50),
            IntervalSet::of(-100, 50),
        ),
        // A demand unbounded above on the same domain: the then arm runs up to infinity.
        (
            chain(&Num::from(5)),
            on(End::NegInf, End::PosInf),
            IntervalSet::range(End::of(100), End::PosInf),
            IntervalSet::of(0, 4).join(&IntervalSet::range(End::of(100), End::PosInf)),
        ),
        // A demand near the top of `i64` on the same domain: the then arm only.
        (
            chain(&Num::from(5)),
            on(End::NegInf, End::PosInf),
            IntervalSet::of(i64::MAX - 50, i64::MAX - 10),
            IntervalSet::of(i64::MAX - 50, i64::MAX - 10),
        ),
        // Inside `i64`, read by the summary.
        (
            chain(&Num::from(5)),
            on(End::of(0), End::of(10)),
            IntervalSet::of(100, 105),
            IntervalSet::of(0, 4),
        ),
    ];
    for (t, ds, z, want) in cases {
        let p = preimage(&t, &ds, &Demand::Ints(z.clone()));
        assert_eq!(p.domains["i"], want, "{t} in {z}");
        assert!(p.exact, "{t} in {z}");
    }
}
