//! The benchmarks of `ladder.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::ladder::*;
use std::collections::BTreeMap;
use zed_tests::scaling;
use zedc::store::presburger::{self, Entailment, Relation, entails};

#[test]
fn the_condition_that_no_operation_fails_scales() {
    // One condition `n + i != 0` for each of k divisors, each made once, and k divisors each
    // shown not 0 by the guard of its `||`, so that no condition is left; the translation is
    // timed at k and 8k. The entailment is checked at k here and timed in
    // `a_chain_of_guarded_remainders_scales` and `a_chain_of_remainders_by_terms_scales`.
    // COMPLEXITY.md rows RUNG2-definedness, PRES-mod-conjuncts and PRES-guarded-chain.
    let n = 256;
    for (p, g) in [divisors(n), guarded_divisors(n)] {
        let e = entails(&p, &g);
        assert!(matches!(e, Entailment::Proved(_)), "{e}");
    }
    let measure = move || {
        scaling::check_order("the definedness of k remainders by terms", n, 1, |k| {
            divisors(k);
        });
        scaling::check_order("the definedness of k guarded remainders", n, 1, |k| {
            guarded_divisors(k);
        });
    };
    let thread = std::thread::Builder::new().stack_size(8 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

#[test]
fn a_chain_of_guarded_remainders_scales() {
    // PRES-guarded-chain: the goal `(n + 0 == 0 || x mod (n + 0) >= 0) && ...` over k
    // divisors under the premise `true`. Its negation is a disjunction of k disjuncts
    // `n + i != 0 && x mod (n + i) < 0`, each refuted only through the cases of its own
    // remainder's definition, and each was refuted by a settling of the whole formula: 1.14G
    // instructions at k = 16 and 148.6G at k = 128, 130 times (measured 2026-11-08). Now each is
    // refuted by a settling of its own definition alone (`refuted_by_links` in `probe`). The
    // entailment is timed at k and 8k. COMPLEXITY.md row PRES-guarded-chain.
    let n = 250;
    let (p, g) = guarded_divisors(n);
    assert_eq!(kind(&entails(&p, &g)), "proved");
    let measure = move || {
        let inputs = scaling::inputs(n, guarded_divisors);
        scaling::check_order("a chain of guarded remainders", n, 1, |k| {
            let (p, g) = &inputs[&k];
            assert_eq!(kind(&entails(p, g)), "proved");
        });
    };
    let thread = std::thread::Builder::new().stack_size(8 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

#[test]
fn a_chain_of_remainders_by_terms_scales() {
    // PRES-mod-conjuncts: a `&&` of k conjuncts written from the left, each reading a
    // remainder by a term of its own. Read as nested `if`s, its condition held the negation of
    // each prefix, Θ(k²) constraints, and each remainder's definition was repaired by reading
    // all k definitions that share `n` and `x`: from k = 16 to 128, 28 times the work under
    // the premise `true` and 22 times the work under `n >= 1` after the first fix alone
    // (measured 2026-11-08; 2.04G instructions at k = 16 before either). The entailment is
    // timed at k and 8k. Under `n >= 1` it is proved; under `true` it is refuted at a
    // divisor 0. COMPLEXITY.md row PRES-mod-conjuncts.
    let n = 62;
    let cases = [
        ("proved", "a chain of remainders by terms", "n >= 1"),
        ("refuted", "a chain of remainders that may fail", "true"),
    ];
    for (verdict, _, premise) in cases {
        let (p, g) = remainder_chain(premise, n);
        assert_eq!(kind(&entails(&p, &g)), verdict, "{premise}");
    }
    let measure = move || {
        for (verdict, what, premise) in cases {
            let inputs = scaling::inputs(n, |k| remainder_chain(premise, k));
            scaling::check_order(what, n, 1, |k| {
                let (p, g) = &inputs[&k];
                assert_eq!(kind(&entails(p, g)), verdict);
            });
        }
        let inputs = scaling::inputs(n, divisors);
        scaling::check_order("a sum of remainders by terms", n, 1, |k| {
            let (p, g) = &inputs[&k];
            assert_eq!(kind(&entails(p, g)), "proved");
        });
    };
    let thread = std::thread::Builder::new().stack_size(8 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

#[test]
fn products_of_premises_in_pairs_scale() {
    // The pairs are taken per product, each from the premises on its two factors; with one
    // lower bound on each factor that is one pair per product.
    let n = 1000;
    let built: BTreeMap<usize, (Relation, Relation)> = [n, n * scaling::FACTOR]
        .into_iter()
        .map(|k| (k, product_sum(k)))
        .collect();
    let measure = move || {
        scaling::check("a sum of products of bounded factors entailed", n, |k| {
            let (p, g) = &built[&k];
            let e = entails(p, g);
            assert!(matches!(e, Entailment::Proved(_)), "{k}: {e}");
        });
    };
    let thread = std::thread::Builder::new().stack_size(8 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

#[test]
fn products_along_a_chain_with_a_disjunction_on_each_link_scale() {
    // The chain of `product_chain` (deferred, see [`product_chain_with`]) with
    // `abs(x{i} - y{i}) <= z{i} + 1` on each link: the definition of each `abs` is a disjunction
    // over the link's atoms, so k disjunctions lie in the one part (C2-chain-general).
    let n = 16;
    let built = scaling::inputs(n, |k| {
        let extra: Vec<String> = (0..k)
            .map(|i| format!("abs(x{i} - y{i}) <= z{i} + 1"))
            .collect();
        product_chain_with(k, &extra)
    });
    let measure = move || {
        scaling::check(
            "a sum of products along a chain with k disjunctions",
            n,
            |k| {
                let (p, g) = &built[&k];
                let e = entails(p, g);
                assert!(matches!(e, Entailment::Proved(_)), "{k}: {e}");
            },
        );
    };
    scaling::on_a_thread(8 << 20, measure);
}

#[test]
fn the_conditions_of_shared_divisors_scale() {
    // k remainders whose divisors each read the k divisors of `t`, met one by one, and k
    // `if`s whose arm reads its guard's divisors: each meet and each test of the arm's
    // divisors against the guard's is a union of the sets of divisors, which share their
    // parts ([`Sets::union`] in divisors.rs), where a copy of the sets made each O(k), O(k²)
    // in all (28.0 times the bytes at 8k for the remainders, k = 128, measured 2026-11-08;
    // 10.2 now). And k functions each calling the one before twice with an argument that may
    // fail, translated once each, where reading each such call at its place read 2^k calls
    // (0.48 s at k = 12, 34 s at k = 18, measured 2026-11-08).
    let k = 200;
    // Each fails where `n = 0`; a verdict is checked against the interpreter (`checked`).
    for src in [met_divisors(2), guarded_arms(2)] {
        assert!(!true_on_window("ok(x, y, n) = true;", &src), "{src}");
        let e = checked("ok(x, y, n) = true;", &src);
        assert!(!matches!(e, Entailment::Proved(_)), "{src}: {e}");
    }
    let measure = move || {
        scaling::check_order("k remainders by terms over k shared divisors", k, 1, |k| {
            ok_relation(&met_divisors(k));
        });
        scaling::check_order("k guards over k shared divisors", k, 1, |k| {
            ok_relation(&guarded_arms(k));
        });
        scaling::check_order(
            "k nested pairs of calls with arguments that may fail",
            k,
            1,
            |k| {
                ok_relation(&nested_double_calls(k));
            },
        );
    };
    let thread = std::thread::Builder::new().stack_size(8 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}

#[test]
fn products_whose_factor_bounds_pass_from_row_to_row_scale() {
    // As above, but `b{i}` and `c{i}` are factors (of `b{i} * c{i}`) and are kept: the bound
    // `b{i} <= 3 - 2 * i` from `b{i} + 2 * c{i} <= 3` is passed on to `x{i} + b{i} >= 10`
    // (`propagate` in `part_bounds`), and no side is asked (C2-chain-general).
    open_side_chain_scales(
        "a sum of products whose factor bounds pass from row to row",
        160,
        |i| format!("b{i} + 2 * c{i} <= 3 && c{i} >= z{i} && b{i} * c{i} >= -1000000"),
        true,
    );
}

#[test]
fn products_whose_factor_bounds_wait_on_each_other_scale() {
    // As above, with `b{i} + c{i} >= z{i} - 100`, so that the upper side of `b{i}` and the
    // lower side of `c{i}` each wait on the other through the rows; each is let go with the
    // bound it has (`propagate`), and no side is asked (C2-chain-general).
    open_side_chain_scales(
        "a sum of products whose factor bounds wait on each other",
        160,
        |i| {
            format!(
                "b{i} + 2 * c{i} <= 3 && c{i} >= z{i} && b{i} * c{i} >= -1000000 \
                 && b{i} + c{i} >= z{i} - 100"
            )
        },
        true,
    );
}

#[test]
fn products_whose_factors_keep_open_sides_scale() {
    // Complexity tradeoff of `products` (C2-chain-general): `x{i} >= 7` needs
    // `x{i} + b{i} >= 10`, `x{i} - b{i} - c{i} >= 4` and `c{i} >= 0` at once, with `b{i}` and
    // `c{i}` kept (they are factors of `b{i} * c{i}`), so no row bounds `x{i}` from the bounds
    // of the others and the goal is not proved from the bounds found. Each open side of a
    // factor is then asked of the solver over the rows of that factor's link alone (its
    // cluster, `clusters` in `part_bounds`), not over the whole chain, so the work stays
    // linear in the number of links.
    open_side_chain_scales(
        "a sum of products whose factors keep open sides",
        16,
        |i| format!("x{i} - b{i} - c{i} >= 4 && c{i} >= 0 && b{i} * c{i} >= -1000000"),
        false,
    );
}

#[test]
fn products_whose_factors_one_sum_on_the_factors_joins_scale() {
    // As `products_whose_factors_one_sum_joins_scale`, with the sum on the factors `b{i}`
    // themselves (C2-pairs-long-row).
    let n = 8;
    let built = scaling::inputs(n, one_sum_on_factors);
    let measure = move || {
        scaling::check(
            "a sum of products whose factors one sum on the factors joins",
            n,
            |k| {
                let (p, g) = &built[&k];
                let e = entails(p, g);
                assert!(matches!(e, Entailment::Proved(_)), "{k}: {e}");
            },
        );
    };
    scaling::on_a_thread(8 << 20, measure);
}

#[test]
fn products_whose_premise_holds_k_atoms_in_no_product_scale() {
    // The sum on `x` holds k atoms that no product holds and that no other row holds, so its
    // product with each row `y - w{j}` alone holds `z{i} * w{j}` and is left out; the k
    // products of the sum cost Θ(k²) terms (C2-pairs-long-row, C2-pairs-exact).
    let n = 8;
    let built = scaling::inputs(n, one_sum_of_atoms_in_no_product);
    let measure = move || {
        scaling::check(
            "a premise of atoms in no product beside many rows on the other factor",
            n,
            |k| {
                let (p, g) = &built[&k];
                let e = entails(p, g);
                assert!(matches!(e, Entailment::Proved(_)), "{k}: {e}");
            },
        );
    };
    scaling::on_a_thread(8 << 20, measure);
}

#[test]
fn products_whose_factors_one_sum_joins_scale() {
    // One cluster holds all k links, so a solver search over the cluster for each open side
    // cost O(sides × cluster): 41 times the instructions at 8n with the sum on `b{i}` itself
    // (C2-local-tier). Through the cluster's block-cut tree each link is its own block, and the
    // sides are found in one pass over the blocks. The sum is on atoms tied to `b{i}`, not on
    // `b{i}`: a sum on the factors themselves is
    // `products_whose_factors_one_sum_on_the_factors_joins_scale` (C2-pairs-long-row).
    let n = 8;
    let built = scaling::inputs(n, one_sum_joins);
    let measure = move || {
        scaling::check("a sum of products whose factors one sum joins", n, |k| {
            let (p, g) = &built[&k];
            presburger::hull_sides_asked();
            let e = entails(p, g);
            let asked = presburger::hull_sides_asked();
            assert!(matches!(e, Entailment::Proved(_)), "{k}: {e}");
            assert!(
                asked > 0,
                "{k}: no side asked, so the cluster was not searched"
            );
        });
    };
    scaling::on_a_thread(8 << 20, measure);
}
