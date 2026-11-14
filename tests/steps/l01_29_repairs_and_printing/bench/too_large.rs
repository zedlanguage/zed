//! Chains and lists of builds past the address space, at `n` and `8n` (`too_large.rs`). Each
//! input is built before the timing.

use zed_tests::scaling;

use crate::too_large::{
    chain, coprime_fourth_powers, even_chain, kept_sums, powers, product_chain, rat_product_chain,
    rejected_times,
};

/// Checks that rejecting `make(n)`, with `per * n` rejections, scales as a pass of order n.
fn rejecting(what: &str, n: usize, per: usize, make: fn(usize) -> String) {
    let srcs = scaling::inputs(n, make);
    scaling::check(what, n, |k| rejected_times(&srcs[&k], per * k));
}

#[test]
fn rejecting_many_powers_scales() {
    // The bound is O(1) words per power: one division and one comparison.
    rejecting(
        "n powers past the address space, each rejected",
        200,
        1,
        powers,
    );
}

#[test]
fn reading_a_chain_of_names_and_divisions_scales() {
    // Each name is read once, however many powers read it: the chain of `n` names costs `n`
    // divisions of 103-bit numbers and `n` rejections.
    rejecting(
        "a chain of n names and divisions, a power of each rejected",
        200,
        1,
        chain,
    );
}

#[test]
fn bounding_a_chain_of_products_scales() {
    // Each name is read once, however many products read through it: the chain of `n` names
    // costs O(n) reads of bit lengths and `n` rejections, each at the third `*` of its line.
    rejecting(
        "a chain of n names and products, a product of each rejected",
        200,
        1,
        product_chain,
    );
}

#[test]
fn bounding_a_chain_of_rat_products_scales() {
    // Plan row CONST-too-large-products-unproved, cases (a) and (c): each name keeps `b` as
    // the root of its numerator and `c` as that of its denominator, so each `*` costs at most
    // six gcds of 65-bit numbers, not a gcd of the whole chain's product: O(n) in all, and
    // `2n` rejections.
    rejecting(
        "a chain of n rat names, a product and a power of each rejected",
        200,
        2,
        rat_product_chain,
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

/// Plan row CONST-too-large-coprime-base: `n` names from `y0 = rat(r0) ^ (2^60)`, each the one
/// before times or divided by `rat(r_i)`, for `r_i` of [`coprime_fourth_powers`], and `y * y`
/// for the last name `y`, past the address space.
fn coprime_chain(n: usize) -> String {
    let r = coprime_fourth_powers(n);
    let body: String = (1..n)
        .map(|i| {
            let op = if i % 2 == 0 { "*" } else { "/" };
            format!("    y{i} = y{} {op} rat({});\n", i - 1, r[i])
        })
        .collect();
    format!(
        "main(m: MainArgs) {{\n    y0 = rat({}) ^ (2^60);\n{body}    \
         m.stdout <- String(y{} * y{}) else \"\";\n}}\n",
        r[0],
        n - 1,
        n - 1
    )
}

#[test]
fn bounding_a_chain_of_products_with_several_roots_scales() {
    // Each `*` and `/` joins the roots in O(1) and leaves its check between a set and a root
    // to the end of the walk; the coprime base of the `n` roots costs O(M(N) log n) for `N`
    // bits in all, and the checks a lookup per root of the smaller side: one rejection.
    let srcs = scaling::inputs(N_ROOTS, coprime_chain);
    scaling::check(
        "a chain of n products and quotients by coprime numbers, the square of the last rejected",
        N_ROOTS,
        |k| rejected_times(&srcs[&k], 1),
    );
}

#[test]
fn bounding_a_chain_of_products_whose_roots_all_share_a_prime_scales() {
    // Plan row CONST-coprime-base-shared-primes: the `n / 2` even numerator roots all share 2,
    // so the batch gcd leaves them all to the coprime base by halves (`coprime::coprime_base`),
    // O(M(N) log^3 N), where factor refinement split each against every element before it,
    // O(n^2) gcds.
    let srcs = scaling::inputs(N_ROOTS, |n| even_chain(n, false));
    scaling::check(
        "a chain of n products by even numbers and quotients by odd ones, the square of the \
         last rejected",
        N_ROOTS,
        |k| rejected_times(&srcs[&k], 1),
    );
}

/// The first `n` primes, by a sieve that doubles its range until it holds them.
fn primes(n: usize) -> Vec<u128> {
    let mut top = 64;
    loop {
        let mut composite = vec![false; top];
        let mut out = Vec::with_capacity(n);
        for p in 2..top {
            if composite[p] {
                continue;
            }
            out.push(p as u128);
            if out.len() == n {
                return out;
            }
            for m in (p * p..top).step_by(p) {
                composite[m] = true;
            }
        }
        top *= 2;
    }
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
/// of fixed values, `y_i = x * z_i` at each link, and the last `y * y`, past the address
/// space. Each `y_i` checks the `n` roots of `x` against the `i` of `z_i`'s denominator.
fn reused_chain(n: usize) -> String {
    let r = coprime_fourth_powers(2 * n);
    let mut s = format!(
        "main(m: MainArgs) {{\n    x0 = rat({}) ^ (2^60);\n    z0 = rat(1) / rat({});\n",
        r[0], r[n]
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
        "    m.stdout <- String(y{} * y{}) else \"\";\n}}\n",
        n - 1,
        n - 1
    )
}

#[test]
fn bounding_products_of_one_value_and_each_link_of_a_chain_scales() {
    // Each `z_i` is fixed, and its roots are the literals it is made of, not its own
    // denominator of `i` words (`Ck::fixed_roots`), so the base holds `2n` roots of O(1) words;
    // the check of `x` against `z_i` reuses that against `z_{i-1}` and looks up one root
    // (`coprime::Roots::settle`): O(log n) a link, where the lookups alone cost `i`. Before
    // both, 941 times the work at 8n for n = 25.
    let srcs = scaling::inputs(N_ROOTS / 2, reused_chain);
    scaling::check(
        "products of one value of n roots and each link of a chain of n fixed quotients, the \
         square of the last rejected",
        N_ROOTS / 2,
        |k| rejected_times(&srcs[&k], 1),
    );
}
