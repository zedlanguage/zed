//! The benchmarks of `past_i64.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `past_i64.rs`.

use super::*;

// The five checks below were one test, `classes_affine_bounds_and_powers_past_i64_scale_linearly`,
// at n = 2000 (400 for the power); each is now a test of its own (TEST-bench-move-l0123,
// author P169).

/// The modulus `2^64 · 3` of the classes past `i64`.
fn modulus() -> Num {
    &two_big(64) * &n(3)
}

/// The normal form of n offsets past `i64` (one gcd per point).
/// TEST-bench-move-l0123, author P169: n was 2000, now 200_000; 1x 0.40 s at load 53.
#[test]
fn the_least_class_of_points_past_i64_scales_linearly() {
    let step = two_big(64);
    scaling::check("the least class of n points past i64", 200_000, |count| {
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
}

/// A chain of n meets of classes modulo `2^64 · 3` that agree.
/// TEST-bench-move-l0123, author P169: n was 2000, now 400_000; 1x 0.81 s at load 32.
#[test]
fn meets_of_classes_past_i64_scale_linearly() {
    let m = modulus();
    scaling::check("n meets of classes past i64", 400_000, |count| {
        let mut c = Congruence::top();
        for k in 0..count as i128 {
            c = c.meet(&class(&m, &(&n(MAX) + &(&m * &n(k)))));
        }
        assert_eq!(c, class(&m, &n(MAX)));
    });
}

/// An affine bound over n symbols scaled by `-2^127`.
/// TEST-bench-move-l0123, author P169: n was 2000, now 750_000; 1x 0.50 s at load 32.
#[test]
fn an_affine_bound_times_minus_2_to_the_127_scales_linearly() {
    scaling::check(
        "an affine bound of n terms times -2^127",
        750_000,
        |count| {
            let mut a = Affine::constant(1);
            a.terms = (0..count)
                .map(|i| (Sym(format!("s{i}")), n(i as i128 + 1)))
                .collect::<BTreeMap<_, _>>();
            assert_eq!(a.times(n(i128::MIN)).terms.len(), count);
        },
    );
}

/// `x ^ (2^32 + 1)` over n pieces.
/// TEST-bench-move-l0123, author P169: n was 400, now 6000; 1x 0.96 s at load 37.
#[test]
fn a_power_past_2_to_the_32_over_n_pieces_scales_linearly() {
    scaling::check("x^(2^32 + 1) over n pieces", 6000, |count| {
        let x = IntervalSet::from_pieces(
            (0..count as i64)
                .map(|i| (End::of(10 * i + 2), End::of(10 * i + 5)))
                .collect(),
        );
        assert_eq!(forward(&pow((1i128 << 32) + 1), &x, &x).len(), count);
    });
}

/// The reduction of n pieces onto a class past `i64`.
/// TEST-bench-move-l0123, author P169: n was 2000, now 180_000; 1x 0.65 s at load 38.
#[test]
fn pieces_moved_onto_a_class_past_i64_scale_linearly() {
    let m = modulus();
    scaling::check(
        "n pieces moved onto a class modulo 2^64 · 3",
        180_000,
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
