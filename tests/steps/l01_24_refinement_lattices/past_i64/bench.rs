//! The benchmarks of `past_i64.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `past_i64.rs`.

use super::*;

#[test]
fn classes_affine_bounds_and_powers_past_i64_scale_linearly() {
    let step = two_big(64);
    // The normal form of n offsets past `i64` (one gcd per point).
    scaling::check("the least class of n points past i64", 2000, |count| {
        let ints = IntervalSet::from_pieces(
            (0..count as i128)
                .map(|k| {
                    let p = &n(MAX) + &(&step * &n(k * k + k));
                    (End::Fin(p.clone()), End::Fin(p))
                })
                .collect(),
        );
        let d = Domain {
            ints,
            class: Congruence::top(),
            finite: FiniteSet::Top,
        };
        assert_ne!(d.normal().class, Congruence::top());
    });
    // A chain of n meets of classes modulo `2^64 · 3` that agree.
    let m = &step * &n(3);
    scaling::check("n meets of classes past i64", 2000, |count| {
        let mut c = Congruence::top();
        for k in 0..count as i128 {
            c = c.meet(&class(&m, &(&n(MAX) + &(&m * &n(k)))));
        }
        assert_eq!(c, class(&m, &n(MAX)));
    });
    // An affine bound over n symbols scaled by `-2^127`.
    scaling::check("an affine bound of n terms times -2^127", 2000, |count| {
        let mut a = Affine::constant(1);
        a.terms = (0..count)
            .map(|i| (Sym(format!("s{i}")), n(i as i128 + 1)))
            .collect::<BTreeMap<_, _>>();
        assert_eq!(a.times(n(i128::MIN)).terms.len(), count);
    });
    // `x ^ (2^32 + 1)` over n pieces, and the reduction of n pieces onto a class past `i64`.
    scaling::check("x^(2^32 + 1) over n pieces", 400, |count| {
        let x = IntervalSet::from_pieces(
            (0..count as i64)
                .map(|i| (End::of(10 * i + 2), End::of(10 * i + 5)))
                .collect(),
        );
        assert_eq!(forward(&pow((1i128 << 32) + 1), &x, &x).len(), count);
    });
    scaling::check(
        "n pieces moved onto a class modulo 2^64 · 3",
        2000,
        |count| {
            let x = IntervalSet::from_pieces(
                (0..count as i128)
                    .map(|i| {
                        let lo = &n(MAX) + &(&m * &n(2 * i));
                        (End::Fin(lo.clone()), End::Fin(&lo + &m))
                    })
                    .collect(),
            );
            let (x2, _) = reduce_congruence(&x, &class(&m, &Num::ONE));
            assert_eq!(x2.len(), count);
        },
    );
}
