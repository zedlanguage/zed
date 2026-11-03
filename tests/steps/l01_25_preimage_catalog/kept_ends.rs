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
