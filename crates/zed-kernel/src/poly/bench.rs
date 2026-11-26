//! The benchmarks of the merges of `poly` (DRY-sorted-intervals-2026-11-26, group 1): the
//! product of two sparse keys and the sum of two polynomials, each one merge of two sorted
//! lists, now `zed_collections::sorted::merge_with`. Each is run 64 times on one pair of `n`
//! items each, half of them shared, so that the merge and not the setup is counted.
//! Correctness: `tests` of `poly` and `zed_collections::sorted`'s
//! `merge_with_meet_with_and_merge_iter_match_a_map`.

use super::*;

/// The indices below `3n / 2` whose remainder by 3 is not `skip`, `n` of them for `n` a multiple
/// of 2: two such lists of different `skip` share half their items.
fn indices(n: usize, skip: usize) -> Vec<u32> {
    (0..3 * n / 2)
        .filter(|i| i % 3 != skip)
        .map(|i| i as u32)
        .collect()
}

#[test]
fn a_product_of_sparse_keys_scales_with_their_names() {
    let inputs = crate::scaling::inputs(4096, |n| {
        let key = |skip| Sparse(indices(n, skip).into_iter().map(|v| (v, 2)).collect());
        (key(0), key(1))
    });
    crate::scaling::check_order(
        "a product of two sparse keys of n names, 64 times",
        4096,
        1,
        |n| {
            let (a, b) = &inputs[&n];
            for _ in 0..64 {
                let p = std::hint::black_box(a).times(std::hint::black_box(b));
                assert_eq!(p.0.len(), a.0.len() + b.0.len() - n / 2);
            }
        },
    );
}

#[test]
fn a_sum_of_polynomials_scales_with_their_terms() {
    let inputs = crate::scaling::inputs(4096, |n| {
        let poly = |skip, c: i64| Poly {
            den: BigInt::one(),
            terms: (indices(n, skip).into_iter())
                .map(|v| (Sparse(Box::new([(v, 1)])), BigInt::from(c)))
                .collect::<Vec<(Sparse, BigInt)>>(),
        };
        // Every coefficient is 3, so the shared terms cancel in the difference.
        (poly(0, 3), poly(1, 3))
    });
    crate::scaling::check_order(
        "a difference of two polynomials of n terms, 64 times",
        4096,
        1,
        |n| {
            let (a, b) = &inputs[&n];
            let mut budget = Budget::new(f64::INFINITY);
            for _ in 0..64 {
                let s = std::hint::black_box(a).add(std::hint::black_box(b), true, &mut budget);
                assert_eq!(
                    s.expect("no budget").terms.len(),
                    a.terms.len() + b.terms.len() - n
                );
            }
        },
    );
}
