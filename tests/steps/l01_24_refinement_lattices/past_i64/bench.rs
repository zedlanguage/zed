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
/// FAIL-lazy-join-random-seed (Colab v5e2, zed_icount): 1490.3M instructions at n = 200,000,
/// was 1751.9M (-14.9%): the gcd of the differences in two machine words (zedc-lattice `Gcd`),
/// where it was a `BigInt` subtraction and gcd a point.
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

/// `x ^ e - y ^ e` for `x` and `y` in `2..=3` and `e = 2^n`, whose ends `2^e - 3^e` and
/// `3^e - 2^e` are kept sums of two terms, and `3^e - 3^(e - 1)`, a sum of two powers of one
/// integer, placed in sign; the size is the bits of `e`. Before PERF-num-kept-multi-term-precision
/// each such sum was placed against `i128` by approximations at 64, 128, ... bits, and the
/// approximation of `3 ^ e` keeps a lower end above 0 only once its bits pass those of `e`, so
/// the cost was about `n` products of `n`-bit numbers a round: 37.3 times the instructions at
/// n = 256. Now n = 16384; 1x 0.20 s at load 23, ratio 7.9.
#[test]
fn differences_of_powers_by_an_exponent_of_n_bits_scale_with_its_bits() {
    scaling::check(
        "differences of powers by an exponent of n bits",
        16384,
        |bits| {
            let e = two_big(bits as u32);
            let x = IntervalSet::of(2, 3);
            let image = forward(&pow(e.clone()), &x, &x);
            let d = forward(&Op::Sub, &image, &image);
            let (low, high) = (Num::pow2(&e), Num::from(3).pow_by(&e).unwrap());
            let gap = &high - &low;
            assert!(gap.signum() > 0);
            assert_eq!(d, IntervalSet::range(End::Fin(-&gap), End::Fin(gap)));
            let below = Num::from(3).pow_by(&(&e - &Num::ONE)).unwrap();
            let twice = &high - &below;
            assert!(twice.signum() > 0);
            assert!((&twice - &(&below * &n(2))).is_zero());
        },
    );
}

/// The reduction of n pieces onto a class past `i64`.
/// TEST-bench-move-l0123, author P169: n was 2000, now 180_000; 1x 0.65 s at load 38.
/// FAIL-lazy-join-random-seed (Colab v5e2, zed_icount): 2733.0M instructions at n = 180,000,
/// was 2620.4M (+4.3%, ratio 8.000 both). Each piece keeps one point, 2m apart, and the class
/// is now their least one, `first mod 2m`, where the code before kept `1 mod m`
/// (`classes_affine_bounds_and_powers_past_i64_on_several_pieces` asserts it and fails on
/// that code). The cost is one gcd a point, of the differences in two machine words
/// (zedc-lattice `Gcd`): about 690 instructions a point; with the differences as `BigInt`s it
/// was 16.7%.
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
