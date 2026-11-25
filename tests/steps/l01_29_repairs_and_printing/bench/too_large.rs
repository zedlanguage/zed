//! Chains and lists of builds past the address space, at `n` and `8n` (`too_large.rs`). Each
//! input is built before the timing.

use zed_tests::scaling;

use crate::too_large::{
    bounded_sums, built, chain, coprime_fourth_powers, even_chain, exponent, kept_sums, powers,
    product_chain, rat_product_chain, rejected_times,
};

/// Checks that rejecting `make(n)`, with `per * n` rejections, scales as a pass of order n.
fn rejecting(what: &str, n: usize, per: usize, make: fn(usize) -> String) {
    let srcs = scaling::inputs(n, make);
    scaling::check(what, n, |k| rejected_times(&srcs[&k], per * k));
}

#[test]
fn rejecting_many_powers_scales() {
    // Each power is kept, O(1) words, and its sum with 1 refused before it allocates.
    rejecting(
        "n sums of a power past the address space, each rejected",
        200,
        1,
        powers,
    );
}

#[test]
fn reading_a_chain_of_names_and_divisions_scales() {
    // Each name is read once, however many powers read it: the chain of `n` names costs `n`
    // divisions of 103-bit numbers and `n` rejections, each of a sum with a power.
    rejecting(
        "a chain of n names and divisions, a sum with a power of each rejected",
        200,
        1,
        chain,
    );
}

#[test]
fn bounding_a_chain_of_products_scales() {
    // Each name is read once, however many products read through it: the chain of `n` names
    // costs O(n) kernel products of kept powers, each O(1) words, and `n` rejections, each at
    // the sum with 1 of its line.
    rejecting(
        "a chain of n names and products, a sum with a product of each rejected",
        200,
        1,
        product_chain,
    );
}

#[test]
fn bounding_a_chain_of_rat_products_scales() {
    // Plan row CONST-too-large-products-unproved, cases (a) and (c): each name keeps `b` and
    // `c` as atoms, so each `*` adds exponents of O(1) words, not a product of the whole
    // chain's: O(n) in all, and `2n` rejections, each of a sum with 1.
    rejecting(
        "a chain of n rat names, a sum with a product and with a power of each rejected",
        200,
        2,
        rat_product_chain,
    );
}

#[test]
fn judging_many_sums_beside_a_bounded_int_scales() {
    // Plan row CONST-build-typed-operands: one bound per sum, O(primes kept), and one read of
    // `k` under each arm's test: O(n) in all, and `n` rejections.
    rejecting(
        "n kept powers and n sums with an int bounded away from 0, each sum rejected",
        800,
        1,
        bounded_sums,
    );
}

#[test]
fn judging_many_builds_scales() {
    // One kernel step per sum, refused before it allocates: O(1) words each, O(n) in all.
    rejecting(
        "n kept powers and n sums past the address space, each sum rejected",
        800,
        1,
        kept_sums,
    );
}

/// `main` writing `b ^ (2 ^ n)`, past the address space, whose exponent has `n + 1` bits.
fn power_of_huge_exponent(b: u32, n: usize) -> String {
    format!("main(m: MainArgs) {{\n    m.stdout <- String({b} ^ (2 ^ {n}));\n}}\n")
}

#[test]
fn folding_a_power_of_a_huge_exponent_scales() {
    // Item PERF-fold-power-of-huge-exponent: the checker approximates `2 ^ (2 ^ n)` by squaring
    // once per bit of the exponent (`Approx::pow` in zedc-int), O(n) products of 64-bit ends,
    // and finds the shift once at the end in O(n); carried through every squaring, the shift
    // of about n bits made it O(n^2), and `2 ^ (2^(2^20))` took 11 s in a dev build. `3 ^ (2 ^
    // n)` is placed past `i128` by the least size of its core (`Num::kept`), where the loop of
    // approximations doubled its precision until it neared n bits, O(n M(n)) a round. Each
    // input reads and writes `2 ^ n` once, O(n).
    for b in [2, 3] {
        let srcs = scaling::inputs(N_EXPONENT_BITS, |n| power_of_huge_exponent(b, n));
        scaling::check(
            &format!("{b} ^ (2 ^ n), rejected past the address space"),
            N_EXPONENT_BITS,
            |k| rejected_times(&srcs[&k], 1),
        );
    }
}

/// The bits of the exponent at the smaller size, the item's `2 ^ (2^(2^20))`. At 8n the fold of
/// `2 ^ (2^23)` stays within the checker's bound on a fold's memory (`FOLD_ASK_BITS` in
/// zedc-check); at `2^24` that fold is unknown and a later stage refuses the program instead.
const N_EXPONENT_BITS: usize = 1 << 20;

/// Plan row CONST-too-large-coprime-base: `n` names from `y0 = rat(r0) ^ e` ([`exponent`]),
/// each the one before times or divided by `rat(r_i)`, for `r_i` of [`coprime_fourth_powers`],
/// and `y * y + 1` for the last name `y`, past the address space.
fn coprime_chain(n: usize, fixed: bool) -> String {
    let r = coprime_fourth_powers(n);
    let body: String = (1..n)
        .map(|i| {
            let op = if i % 2 == 0 { "*" } else { "/" };
            format!("    y{i} = y{} {op} rat({});\n", i - 1, r[i])
        })
        .collect();
    format!(
        "main(m: MainArgs) {{\n{}    y0 = rat({}) ^ e;\n{body}    \
         m.stdout <- String(y{} * y{} + 1 > 0);\n}}\n",
        exponent(fixed),
        r[0],
        n - 1,
        n - 1
    )
}

/// The chains of roots of the two benches below with the exponent fixed: since KEPT-power-form
/// `rat(r0) ^ (2^60)` is kept, so every name is a fixed value and the sum of the last square is
/// rejected, once. With the exponent the input picks, the program compiles: the sum is left to
/// the run, as `2^(2^70) + n` is.
#[test]
fn a_fixed_chain_of_roots_is_rejected_at_its_last_sum() {
    // `reused_chain` needs two links for its last `y`.
    for n in [2, 5] {
        rejected_times(&coprime_chain(n, true), 1);
        rejected_times(&reused_chain(n, true), 1);
        for src in [coprime_chain(n, false), reused_chain(n, false)] {
            assert_eq!(built(&src), None, "{src}");
        }
    }
}

#[test]
fn bounding_a_chain_of_products_with_several_roots_scales() {
    // The roots path (`Ck::least_built`): no name is fixed, as the exponent is the input's, so
    // each `*` and `/` by a coprime `r_i` unions the roots of the two operands, O(1) a link. With
    // the exponent fixed every name is a fixed kernel value, and folding the chain exactly
    // holds `i` words at link `i`, O(n^2) in the memo (`Ck::fixed_value`, "as the run's would";
    // plan row FOLD-growing-chains); that program is tested at small sizes above.
    let srcs = scaling::inputs(N_ROOTS, |n| coprime_chain(n, false));
    scaling::check(
        "a chain of n products and quotients by coprime numbers, the square of the last left to \
         the run",
        N_ROOTS,
        |k| assert_eq!(built(&srcs[&k]), None),
    );
}

#[test]
fn bounding_a_chain_of_products_whose_roots_all_share_a_prime_scales() {
    // Plan row CONST-coprime-base-shared-primes: the `n / 2` even numerator roots all share 2,
    // so the batch gcd leaves them all to the coprime base by halves (zed-kernel's
    // `num::coprime::coprime_base`, since DRY-coprime-bases-one), a polylogarithmic factor over
    // M(N), where factor refinement split each against every element before it, O(n^2) gcds.
    // Timed with the exponent the input picks, as the two benches above.
    let srcs = scaling::inputs(N_ROOTS, |n| even_chain(n, false));
    scaling::check(
        "a chain of n products by even numbers and quotients by odd ones, the square of the \
         last left to the run",
        N_ROOTS,
        |k| assert_eq!(built(&srcs[&k]), None),
    );
}

/// The first `n` primes.
fn primes(n: usize) -> Vec<u128> {
    zed_numtheory::first_primes(n)
        .into_iter()
        .map(u128::from)
        .collect()
}

/// `x` of `k = isqrt(n)` primes and `k` sets `u_i` and `k` sets `v_j` of `k` primes each, all
/// distinct, and a check of `x` against each union of a `u_i` and a `v_j`: `n` checks.
fn pool(n: usize) -> zedc::check::Pool {
    let k = n.isqrt().max(1);
    let ps = primes(k * (1 + 2 * k));
    let mut sets = ps.chunks(k).map(<[u128]>::to_vec);
    let x = sets.next().expect("k primes for x");
    let us = sets.by_ref().take(k).collect();
    zedc::check::Pool::new(x, us, sets.collect())
}

#[test]
fn settling_checks_of_one_set_against_unions_from_one_pool_scales() {
    // Plan row CONST-coprime-check-many-sets, past the walk and the base: `n` checks of `x`
    // against a union of `u_i` and `v_j`, each of `k = isqrt(n)` roots. The first check
    // through each `u_i` and `v_j` keeps its answer against `x`, and only `x`, the `u_i` and
    // the `v_j` are built (`coprime::Sets`): O(n log n) in all, where a lookup per root at
    // each check, or each union built, is O(n^1.5).
    let pools = scaling::inputs(N_SETTLE, pool);
    scaling::check(
        "settling checks of one set of isqrt(n) roots against each union of two sets from one \
         pool",
        N_SETTLE,
        |k| assert!(pools[&k].settle().iter().all(|h| *h)),
    );
}

/// The checks settled past the walk: 67 ms at n and 0.94 s at 8n, at load 56.
const N_SETTLE: usize = 20_000;

/// The size of the chains of roots, at about 1 s a run.
const N_ROOTS: usize = 2000;

/// Plan row CONST-too-large-coprime-base: `x` of `n` roots, a chain `z_i = z_{i-1} / rat(r_i)`
/// of fixed values, `y_i = x * z_i` at each link, and the last `y * y + 1`, past the address
/// space.
fn reused_chain(n: usize, fixed: bool) -> String {
    let r = coprime_fourth_powers(2 * n);
    let mut s = format!(
        "main(m: MainArgs) {{\n{}    x0 = rat({}) ^ e;\n    z0 = rat(1) / rat({});\n",
        exponent(fixed),
        r[0],
        r[n]
    );
    for (i, ri) in r.iter().enumerate().take(n).skip(1) {
        s += &format!("    x{i} = x{} * rat({ri});\n", i - 1);
    }
    for i in 1..n {
        s += &format!(
            "    z{i} = z{} / rat({});\n    y{i} = x{} * z{i};\n",
            i - 1,
            r[n + i],
            n - 1
        );
    }
    s + &format!(
        "    m.stdout <- String(y{} * y{} + 1 > 0);\n}}\n",
        n - 1,
        n - 1
    )
}

#[test]
fn bounding_products_of_one_value_and_each_link_of_a_chain_scales() {
    // The roots path, as above: `x` is not fixed, so each `y_i = x * z_i` unions the roots of
    // `x` with those of the fixed `z_i`. With the exponent fixed each `y_i` is one exact kernel
    // product, a gcd of the `n` words of `x` against the `i` of `z_i`, superquadratic in all
    // (plan row FOLD-growing-chains); that program is tested at small sizes above.
    let srcs = scaling::inputs(N_ROOTS / 2, |n| reused_chain(n, false));
    scaling::check(
        "products of one value of n roots and each link of a chain of n fixed quotients, the \
         square of the last left to the run",
        N_ROOTS / 2,
        |k| assert_eq!(built(&srcs[&k]), None),
    );
}
