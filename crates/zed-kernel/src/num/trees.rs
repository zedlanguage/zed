//! Product, scaled remainder, and cofactor trees over `BigUint`, the one copy for zedc-int
//! (`remainders`, under `Int::is_perfect_power`), zedc-check `check/coprime.rs` (`base_of` and its
//! remainders) and zedc-presburger `presburger/modular.rs` (the batch "shares a factor" test, the
//! CRT tree and `batch_remainders`), DRY-number-theory-wide item 2.
//!
//! The product tree of leaves `m_0 .. m_{k-1}` multiplies them in pairs, then those in pairs,
//! up to one product `P`; a level of odd length carries its last node up unchanged, so node
//! `j` of a level is the product of nodes `2 j` and `2 j + 1` of the level below, or equal to
//! node `2 j` when there is no `2 j + 1`.
//!
//! **Remainders ([`remainders`]).** Computed by D. J. Bernstein's scaled remainder tree,
//! "Scaled remainder trees", draft 2004-08-20, <https://cr.yp.to/arith/scaledmod-20040820.pdf>
//! (checked 2026-11-20 against the extracted text of the author's PDF, Theorems 2.1 and 2.2,
//! pp. 4-5; no DOI). After one root reduction `u = x mod P` and one root scaling `S_root ≈ u / P`
//! to `f_root` bits, each node `v = a * b` (`a, b >= 2`) at level `i` of an `l`-level tree holds
//! `S_v in [0, 2^f)` within `(l + i) / (4 l v)` of `(u / v) mod 1` modulo `Z` (`2^f >= 8 l v`).
//! Stepping to children `a` and `b` multiplies `S_v` by `b` and `a` modulo `2^f` (Theorem 2.1) or
//! modulo `2^f - 1` by cyclic NTT with `S_v`'s spectrum shared across both children (Theorem 2.2),
//! rounds to `e` bits (`2^e >= 8 l a`, `e <= f`), and reduces modulo `2^e`. At each leaf `m >= 2`
//! (`i = l`), the distance is `< 2l / (4 l m) = 1 / (2 m)`, so `round(m S_leaf / 2^e)` (wrapping
//! `m` to `0`) recovers `u mod m = x mod m` exactly. Every division inside the tree is replaced by
//! a multiplication (or cyclic NTT of half the linear width). Tests:
//! `the_remainders_agree_with_one_division_a_leaf` and
//! `the_scaled_remainders_and_cofactors_agree_past_ntt_width`.
//!
//! **Cofactors ([`cofactors_mod_leaves`]).** Computes `(P / m_j) mod m_j` for all leaves `m_j` by
//! the identity of P. Bürgisser, M. Clausen, and M. A. Shokrollahi, *Algebraic Complexity Theory*,
//! Springer, 1997, doi:10.1007/978-3-662-03338-8, pp. 77-78, as stated in D. J. Bernstein, "Fast
//! multiplication and its applications", in *Algorithmic Number Theory*, MSRI Publications 44,
//! Cambridge University Press, 2008, pp. 325-384,
//! <https://cr.yp.to/lineartime/multapps-20080515.pdf> (checked 2026-11-20 against Bernstein's
//! PDF, §23.7, p. 372, and Crossref for BCS 1997):
//! let `S = sum_{i=0}^{k-1} (P / m_i)`, built bottom-up by [`linear_combination_up`] with weight 1
//! at each leaf. For any fixed `j` and every `i != j`, `m_j` divides `P / m_i` (no coprimality
//! needed, even when leaves are equal or share factors), so `S == P / m_j (mod m_j)`. One scaled
//! remainder tree [`remainders`]`(&S, leaves, levels)` then gives `(P / m_j) mod m_j` for every
//! leaf while keeping every intermediate integer at width `bits(v)` rather than
//! `bits(v^2) = 2 bits(v)`.
//! Tests: `the_cofactors_agree_with_division` and
//! `the_scaled_remainders_and_cofactors_agree_past_ntt_width`.
//!
//! Complexity tradeoff: a level of the tree holds at most `B + k` bits for `k` leaves of `B`
//! bits in all, so the products, [`linear_combination_up`], and the scaled remainder tree each
//! cost O(M(B)) a level and O(M(B) log k) in all (plus O(M(X + B)) for the root reduction of `x`
//! of `X` bits), against O(k M(X)) for one division a leaf and against the previous `P mod v^2`
//! descent whose doubled widths `2 bits(v)` kept Burnikel-Ziegler divisions in the `w^1.52` regime.

use std::borrow::{Borrow, Cow};

use num_bigint::BigUint;
use num_traits::{One, Zero};

use super::{fast, mul_uint, rem_uint};

/// The levels of the product tree of `leaves` above the leaves themselves: the products of
/// pairs of leaves first, then of pairs of those, up to the one product of all, a node with no
/// partner carried up as it is. Empty for no leaf or one leaf. A leaf 0 makes its ancestors
/// 0, which [`remainders`] and [`cofactors_mod_leaves`] do not accept.
pub fn product_tree<L: Borrow<BigUint>>(leaves: &[L]) -> Vec<Vec<BigUint>> {
    let _hold = fast::hold_roots();
    let mut levels: Vec<Vec<BigUint>> = Vec::new();
    if leaves.len() > 1 {
        let first = (leaves.chunks(2))
            .map(|c| pair(c[0].borrow(), c.get(1).map(Borrow::borrow)))
            .collect();
        levels.push(first);
    }
    while let Some(top) = levels.last().filter(|l| l.len() > 1) {
        let up = top.chunks(2).map(|c| pair(&c[0], c.get(1))).collect();
        levels.push(up);
    }
    levels
}

/// `a * b`, or `a` where `b` is missing (a node carried up).
fn pair(a: &BigUint, b: Option<&BigUint>) -> BigUint {
    match b {
        Some(b) => mul_uint(a, b),
        None => a.clone(),
    }
}

/// The product of all `leaves`, given `levels`, their [`product_tree`]: its root, or the one
/// leaf; 1 for no leaf.
pub fn tree_product<'a, L: Borrow<BigUint>>(
    leaves: &'a [L],
    levels: &'a [Vec<BigUint>],
) -> Cow<'a, BigUint> {
    match (levels.last(), leaves.first()) {
        (Some(top), _) => Cow::Borrowed(&top[0]),
        (None, Some(leaf)) => Cow::Borrowed(leaf.borrow()),
        (None, None) => Cow::Owned(BigUint::from(1u32)),
    }
}

/// `sum_i vals[i] * (P / leaves[i])`, built bottom-up along `levels`, the [`product_tree`] of
/// `leaves`: at each internal node `v = p0 * p1`, `v_out = v0 * p1 + v1 * p0` (via
/// `fast::mul_add_pair`); an odd node carried up keeps its value. Returns `0` for no leaf.
pub fn linear_combination_up<L: Borrow<BigUint>>(
    vals: Vec<BigUint>,
    leaves: &[L],
    levels: &[Vec<BigUint>],
) -> BigUint {
    debug_assert_eq!(vals.len(), leaves.len());
    if vals.is_empty() {
        return BigUint::zero();
    }
    if vals.len() == 1 {
        return vals.into_iter().next().expect("checked len == 1");
    }
    let _hold = fast::hold_roots();
    // Level 0 uses borrowed `leaves` directly; higher levels use `levels[..levels.len() - 1]`.
    let mut cur: Vec<BigUint> = (vals.chunks(2).zip(leaves.chunks(2)))
        .map(|(v, p)| match (v, p) {
            ([v0, v1], [p0, p1]) => fast::mul_add_pair(v0, p1.borrow(), v1, p0.borrow()),
            _ => v[0].clone(),
        })
        .collect();
    for prods in &levels[..levels.len().saturating_sub(1)] {
        cur = (cur.chunks(2).zip(prods.chunks(2)))
            .map(|(v, p)| match (v, p) {
                ([v0, v1], [p0, p1]) => fast::mul_add_pair(v0, p1, v1, p0),
                _ => v[0].clone(),
            })
            .collect();
    }
    cur.into_iter().next().expect("nonempty tree has one root")
}

/// `x mod m` for each leaf `m` of `leaves`, every leaf above 0, by Bernstein's scaled remainder
/// tree (2004, Theorems 2.1 and 2.2) down `levels`, their [`product_tree`].
pub fn remainders<L: Borrow<BigUint>>(
    x: &BigUint,
    leaves: &[L],
    levels: &[Vec<BigUint>],
) -> Vec<BigUint> {
    if leaves.is_empty() {
        return Vec::new();
    }
    let p = tree_product(leaves, levels);
    // `rem_uint` panics with "a division by zero" if `p == 0` (any leaf is 0).
    let top = rem_uint(x, &p);
    if leaves.len() == 1 {
        return vec![top];
    }
    if top.is_zero() || p.is_one() {
        return vec![BigUint::zero(); leaves.len()];
    }
    // Two exact methods, switched at their measured crossover. The scaled tree works at every
    // node's full width `bits(v) + guard` whatever the width of `top`; the exact descent
    // `x mod v = (x mod u) mod v` costs a comparison at each node wider than its parent's
    // remainder and a division whose quotient has the width of the difference below it. With
    // `top` short the scaled tree is far the dearer: moduli 2, 4, .., 2^k with `x < 2^(k + 1)`
    // (`pncx_power_propagation_scale`, k about 12,649) are O(M(k) k) by the descent and
    // O(M(k^2) log k) by the scaled tree, which did not finish in 60 s. Measured by
    // `the_remainders_crossover_axis` (2026-11-21, load 70, instructions, `w` the width of `top`
    // as a fraction of `bits(P)`): 1024 odd word leaves, descent against scaled tree, 22.6 M
    // against 24.0 M at 3/4 and 26.1 M against 24.0 M at 7/8; 32 odd leaves of 64 words, 53.7 M
    // against 53.6 M at 3/4 and 61.6 M against 53.7 M at 7/8; on 2, 4, .., 2^200 the descent is
    // the cheaper at every width (1.7 M against 7.2 M at 1/1). So the scaled tree from 7/8 on.
    // The cofactors' `S mod P` (`cofactors_mod_leaves`) is about the width of `P` and takes it.
    // Those runs are zed-kernel's own tests, built with the test constants (`MUL_LEAF` 48, no
    // Toom-3). Measured again 2026-11-21 (load 31) the same, and in zedc-presburger, where
    // zed-kernel has its real constants (load 10 to 22, the scaled side with its switch to the
    // descent at `SCALED_TO_EXACT_WORDS`): 1024 odd word leaves, descent against scaled, 12.9 M
    // against 19.3 M at 7/8 and 14.0 M against 18.9 M at 1/1; 32 leaves of 64 words 31.8 M
    // against 37.4 M at 7/8 and 35.2 M against 33.5 M at 1/1; 32 leaves of 512 words 733 M
    // against 529 M at 7/8 and 573 M against 526 M already at 1/2; 2, .., 2^200 the descent the
    // cheaper below 1/1, a tie at 1/1; the CRT cofactor sum over 2,048 odd primes (`x` at
    // 1/1) 8.13 M against 7.60 M. So with the real constants no switch by the width of `x`
    // alone is right for all of these: it depends on the widths of the nodes as well, and
    // 7/8 stays until a switch from both methods' costs node by node is measured
    // (PERF-remainders-switch-by-cost).
    // Tests: `the_remainders_of_a_short_x_take_the_exact_descent`, and the axis above.
    if 8 * top.bits() < 7 * p.bits() {
        return descend(top, leaves, levels);
    }
    scaled_descend(&top, &p, leaves, levels)
}

/// The width in words at or below which [`scaled_descend`] leaves the scaled tree for the exact
/// descent: at the first level (from the root down) whose nodes are all at most this wide, each
/// node's scaled value becomes its exact remainder and [`descend_from`] finishes below it.
/// Measured by `presburger::modular::r4_tests::bench::the_scaled_to_exact_switch_axis`
/// (zedc-presburger, so that zed-kernel is built with its own multiplication constants rather
/// than the test build's `MUL_LEAF` 48; 2026-11-21, load 15 to 19, instructions, `x` about the
/// width of `P`), widths 0 (scaled tree alone) to all (descent alone): the CRT cofactor sum over
/// the first 2,048 / 16,384 / 131,072 odd primes 9.27 M / 147.3 M / 2,375 M scaled alone, 7.60 M
/// / 131.2 M / 2,267 M at 128 words, 8.13 M / 190.4 M / 4,707 M by the descent alone; 4,096 word
/// leaves 117.8 M, 100.9 M, 168.0 M; 512 leaves of 8 words 94.9 M, 92.3 M, 161.6 M; 256 leaves
/// of 64 words 417.2 M, 416.3 M, 1,037.9 M; 32 leaves of 512 words 473.7 M at every width up to
/// 512 (no level that narrow above them), 941.6 M by the descent; 2, 4, .., 2^200 1.59 M,
/// 1.69 M, 2.13 M (the one family where 128 is not the best, 16 words gave 1.51 M). 64 words
/// was within 3% of 128 on every family and lost on seven of nine; 256 and above cost more on
/// every family with nodes that narrow.
const SCALED_TO_EXACT_WORDS: u64 = 128;

/// `top mod m` for each leaf `m` by the scaled remainder tree (module comment) down to nodes of
/// [`SCALED_TO_EXACT_WORDS`] words, then the exact descent, for at least two leaves, `p` their
/// product above 1 and `top` in `(0, p)`.
fn scaled_descend<L: Borrow<BigUint>>(
    top: &BigUint,
    p: &BigUint,
    leaves: &[L],
    levels: &[Vec<BigUint>],
) -> Vec<BigUint> {
    scaled_descend_switch(top, p, leaves, levels, SCALED_TO_EXACT_WORDS)
}

/// `scaled_descend` with its switch to the exact descent at levels whose nodes are all at most
/// `switch_words` words (0: the scaled tree to the leaves), public for the benchmark of both
/// sides of `SCALED_TO_EXACT_WORDS` in a crate that builds zed-kernel with its own constants.
#[doc(hidden)]
pub fn scaled_descend_switch<L: Borrow<BigUint>>(
    top: &BigUint,
    p: &BigUint,
    leaves: &[L],
    levels: &[Vec<BigUint>],
    switch_words: u64,
) -> Vec<BigUint> {
    let _hold = fast::hold_roots();
    // Number of levels counting root as 1 and leaves as `l = levels.len() + 1`.
    // Guard bits `g` satisfy `2^g >= 8 * l`, so for every node `v >= 2`,
    // `2^(bits(v) + g) > v * 2^g >= 8 * l * v`, fulfilling Theorems 2.1 and 2.2.
    let l = (levels.len() + 1) as u64;
    let guard = (8 * l).next_power_of_two().trailing_zeros() as u64;
    debug_assert!(1u64 << guard >= 8 * l);

    // Helper: child slice at level index `child_lvl` (`0` = leaves, `d + 1` = `levels[d]`).
    let child_len = |child_lvl: usize| -> usize {
        if child_lvl == 0 {
            leaves.len()
        } else {
            levels[child_lvl - 1].len()
        }
    };
    let child_node = |child_lvl: usize, idx: usize| -> &BigUint {
        if child_lvl == 0 {
            leaves[idx].borrow()
        } else {
            &levels[child_lvl - 1][idx]
        }
    };

    // Determine the root's precision (no cap from above).
    let root_lvl = levels.len();
    let root_child_lvl = root_lvl - 1;
    let root_prec = |cap: u64| -> (u64, bool) {
        if child_len(root_child_lvl) >= 2 {
            let a = child_node(root_child_lvl, 0);
            let b = child_node(root_child_lvl, 1);
            if a.bits() >= 2 && b.bits() >= 2 {
                return fast::scaled_node_precision(p, a, b, guard, cap);
            }
        }
        (p.bits() + guard, false)
    };
    let (f_root, root_ntt) = root_prec(u64::MAX);
    // `scaled_root` promises `|S_root / 2^f_root - top / p| < 1.5 / 2^f_root <= 1.5 / (8 l p)
    // < (l + 1) / (4 l p)` since `l >= 2` implies `l + 1 >= 3 > 0.75`.
    let s_root = fast::scaled_root(top, p, f_root);
    let mut vals: Vec<(BigUint, u64, bool)> = vec![(s_root, f_root, root_ntt)];

    // Descend from level `levels.len() - 1` (children of root) down to level `0` (leaves).
    for child_lvl in (0..levels.len()).rev() {
        // The switch to the exact descent. `vals` holds the nodes of `levels[child_lvl]`, at
        // level `i <= l - 1` of the tree, each `S_v` (precision `f`) within `(l + i) / (4 l v)
        // <= (2 l - 1) / (4 l v) < 1 / (2 v)` of `(u / v) mod 1` modulo `Z`, carried nodes
        // included (a carried node keeps its parent's `S` and `f`, and its parent is the same
        // integer at a level nearer the root, so the smaller `i` bound holds). So `v S_v / 2^f`
        // is within `1 / 2` of `u mod v` modulo `v`, and `round(v S_v / 2^f)`, `v` wrapped to
        // 0, is `u mod v` exactly: the leaf recovery's argument at an inner node (`v = 1`
        // nodes hold `(0, 0)` and give 0). Below, each node's remainder is its parent's
        // remainder mod the node, which is `u mod v` since `v` divides its parent. A level is
        // taken whole, so every node of the level must be narrow (one wide node keeps the
        // scaled tree for the level). Measurements: [`SCALED_TO_EXACT_WORDS`]. Tests:
        // `the_scaled_tree_switches_to_the_descent_at_any_level`.
        // Complexity tradeoff: the levels below the switch cost what the exact descent costs on
        // nodes of at most `SCALED_TO_EXACT_WORDS` words, num-bigint's divisions, cheaper there
        // than the scaled steps' products with their guard bits; the order O(M(B) log k) is
        // unchanged, as the descent on nodes of bounded width costs O(B) a level.
        if levels[child_lvl]
            .iter()
            .all(|v| v.bits() <= 64 * switch_words)
        {
            let rems = (vals.into_iter().zip(&levels[child_lvl]))
                .map(|((s, e, _), v)| fast::scaled_leaf_rem(v, &s, e))
                .collect();
            return descend_from(rems, child_lvl, leaves, levels);
        }
        let clen = child_len(child_lvl);
        let mut next: Vec<(BigUint, u64, bool)> = Vec::with_capacity(clen);
        let prec_for = |idx: usize, cap: u64| -> (u64, bool) {
            let v = child_node(child_lvl, idx);
            if v.bits() < 2 {
                return (0, false);
            }
            if child_lvl == 0 {
                // Leaf: no further children, so tight precision `bits(v) + guard` suffices.
                return (v.bits() + guard, false);
            }
            let gc_lvl = child_lvl - 1;
            let gc_len = child_len(gc_lvl);
            if 2 * idx + 1 < gc_len {
                let ga = child_node(gc_lvl, 2 * idx);
                let gb = child_node(gc_lvl, 2 * idx + 1);
                if ga.bits() >= 2 && gb.bits() >= 2 {
                    return fast::scaled_node_precision(v, ga, gb, guard, cap);
                }
            }
            (v.bits() + guard, false)
        };
        for (parent_idx, (sv, f, use_ntt)) in vals.into_iter().enumerate() {
            let i0 = 2 * parent_idx;
            let i1 = i0 + 1;
            if i1 >= clen {
                // Carried odd node: `a = parent`, so `(u / a) mod 1` is identical; keep `(sv, f)`.
                // Re-evaluate `use_ntt` for the carried node's children using its existing `f`
                // (it can use NTT only if `f` is already a power-of-two multiple of 64).
                let v = child_node(child_lvl, i0);
                if v.bits() < 2 {
                    next.push((BigUint::zero(), 0, false));
                } else {
                    let keep_ntt = use_ntt && child_lvl > 0 && {
                        let gc_lvl = child_lvl - 1;
                        2 * i0 + 1 < child_len(gc_lvl)
                            && child_node(gc_lvl, 2 * i0).bits() >= 2
                            && child_node(gc_lvl, 2 * i0 + 1).bits() >= 2
                    };
                    next.push((sv, f, keep_ntt));
                }
                continue;
            }
            let a = child_node(child_lvl, i0);
            let b = child_node(child_lvl, i1);
            if a.bits() < 2 {
                // `a == 1`: left remainder is 0; right child `b == parent`, so carry `sv`.
                next.push((BigUint::zero(), 0, false));
                if b.bits() < 2 {
                    next.push((BigUint::zero(), 0, false));
                } else {
                    let keep_ntt = use_ntt && child_lvl > 0 && {
                        let gc_lvl = child_lvl - 1;
                        2 * i1 + 1 < child_len(gc_lvl)
                            && child_node(gc_lvl, 2 * i1).bits() >= 2
                            && child_node(gc_lvl, 2 * i1 + 1).bits() >= 2
                    };
                    next.push((sv, f, keep_ntt));
                }
                continue;
            }
            if b.bits() < 2 {
                // `b == 1`: left child `a == parent`, so carry `sv`; right remainder is 0.
                let keep_ntt = use_ntt && child_lvl > 0 && {
                    let gc_lvl = child_lvl - 1;
                    2 * i0 + 1 < child_len(gc_lvl)
                        && child_node(gc_lvl, 2 * i0).bits() >= 2
                        && child_node(gc_lvl, 2 * i0 + 1).bits() >= 2
                };
                next.push((sv, f, keep_ntt));
                next.push((BigUint::zero(), 0, false));
                continue;
            }
            let (ea, ntt_a) = prec_for(i0, f);
            let (eb, ntt_b) = prec_for(i1, f);
            let (sa, sb) = fast::scaled_children(&sv, f, use_ntt, a, ea, b, eb);
            next.push((sa, ea, ntt_a));
            next.push((sb, eb, ntt_b));
        }
        vals = next;
    }

    // Leaf recovery: `|S_j / 2^e - u / m_j| < 2 l / (4 l m_j) = 1 / (2 m_j)` modulo `Z`,
    // so `round(m_j * S_j / 2^e)` is the unique integer in `[0, m_j]` congruent to `u mod m_j`,
    // wrapping `m_j` to `0`.
    (vals.into_iter().zip(leaves))
        .map(|((s, e, _), leaf)| fast::scaled_leaf_rem(leaf.borrow(), &s, e))
        .collect()
}

/// `(P / m) mod m` for each leaf `m` of `leaves`, every leaf above 0, with `P` their product,
/// by computing `S = sum_i (P / m_i)` up `levels` ([`linear_combination_up`], Bürgisser, Clausen,
/// and Shokrollahi 1997, pp. 77-78; Bernstein 2008, §23.7) and reducing `S` down `levels` by
/// [`remainders`]. For one leaf `P / m` is 1, so the answer is `1 mod m`.
pub fn cofactors_mod_leaves<L: Borrow<BigUint>>(
    leaves: &[L],
    levels: &[Vec<BigUint>],
) -> Vec<BigUint> {
    if leaves.is_empty() {
        return Vec::new();
    }
    if leaves.len() == 1 {
        return vec![rem_uint(&BigUint::one(), leaves[0].borrow())];
    }
    let _hold = fast::hold_roots();
    // Level 0 of `S = sum_i (P / m_i)` with all weights 1 is simply `m0 + m1` for each pair
    // (no multiplications needed at level 0), then `linear_combination_up` from level 1 up.
    let mut cur: Vec<BigUint> = (leaves.chunks(2))
        .map(|c| match c {
            [a, b] => a.borrow() + b.borrow(),
            [a] => {
                let _ = a;
                BigUint::one()
            }
            _ => unreachable!("chunks(2) yields 1 or 2 items"),
        })
        .collect();
    for prods in &levels[..levels.len().saturating_sub(1)] {
        cur = (cur.chunks(2).zip(prods.chunks(2)))
            .map(|(v, p)| match (v, p) {
                ([v0, v1], [p0, p1]) => fast::mul_add_pair(v0, p1, v1, p0),
                _ => v[0].clone(),
            })
            .collect();
    }
    let s = cur.into_iter().next().expect("nonempty tree has one root");
    remainders(&s, leaves, levels)
}

/// `top mod m` for each leaf `m`, `leaves` holding at least two, when `top` is below their
/// product: each node's value is its parent's value `mod` the node.
fn descend<L: Borrow<BigUint>>(
    top: BigUint,
    leaves: &[L],
    levels: &[Vec<BigUint>],
) -> Vec<BigUint> {
    descend_from(vec![top], levels.len() - 1, leaves, levels)
}

/// The exact descent from `vals`, the remainders at the nodes of `levels[child_lvl]` (each below
/// its node), to the leaves: each node's remainder is its parent's remainder `mod` the node.
fn descend_from<L: Borrow<BigUint>>(
    mut vals: Vec<BigUint>,
    child_lvl: usize,
    leaves: &[L],
    levels: &[Vec<BigUint>],
) -> Vec<BigUint> {
    for level in levels[..child_lvl].iter().rev() {
        vals = (level.iter().enumerate())
            .map(|(j, v)| rem_uint(&vals[j / 2], v))
            .collect();
    }
    (leaves.iter().enumerate())
        .map(|(j, m)| rem_uint(&vals[j / 2], m.borrow()))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn big(v: u64) -> BigUint {
        BigUint::from(v)
    }

    /// The leaf sets: none, one, ones, equal, every count from 2 to 17 (a carried node at some
    /// level for each count that is not a power of 2), and leaves past 512 words.
    fn leaf_sets() -> Vec<Vec<BigUint>> {
        let mut sets = vec![
            vec![],
            vec![big(1)],
            vec![big(7)],
            vec![big(1), big(1), big(1)],
            vec![big(12), big(12), big(12)],
            vec![big(1), big(5), big(1), big(5), big(9)],
            vec![big(u64::MAX); 6],
        ];
        for k in 2..=17u64 {
            sets.push((0..k).map(|i| big(3 * i * i + 2 * i + 1)).collect());
        }
        let wide = |e: u32, c: u64| big(18446744073709551557).pow(e) * c + 1u32;
        sets.push(vec![
            wide(600, 1),
            wide(700, 3),
            wide(10, 5),
            wide(1200, 7),
            big(2),
        ]);
        sets
    }

    #[test]
    fn the_product_tree_multiplies_and_carries() {
        for leaves in leaf_sets() {
            let levels = product_tree(&leaves);
            let want: BigUint = leaves.iter().product();
            assert_eq!(*tree_product(&leaves, &levels), want, "{leaves:?}");
            assert_eq!(levels.is_empty(), leaves.len() <= 1);
            let mut below: Vec<BigUint> = leaves.clone();
            for level in &levels {
                assert_eq!(level.len(), below.len().div_ceil(2));
                for (j, v) in level.iter().enumerate() {
                    let want: BigUint = below[2 * j..(2 * j + 2).min(below.len())].iter().product();
                    assert_eq!(*v, want);
                }
                below = level.clone();
            }
        }
    }

    #[test]
    fn the_remainders_agree_with_one_division_a_leaf() {
        let xs = [
            big(0),
            big(1),
            big(11),
            big(3).pow(5000) + 17u32,
            big(18446744073709551557).pow(3000),
        ];
        for leaves in leaf_sets() {
            let levels = product_tree(&leaves);
            for x in &xs {
                let want: Vec<BigUint> = leaves.iter().map(|m| x % m).collect();
                assert_eq!(
                    remainders(x, &leaves, &levels),
                    want,
                    "x {} {leaves:?}",
                    x.bits()
                );
            }
        }
    }

    #[test]
    fn the_cofactors_agree_with_division() {
        for leaves in leaf_sets() {
            let levels = product_tree(&leaves);
            let p: BigUint = leaves.iter().product();
            let want: Vec<BigUint> = leaves.iter().map(|m| (&p / m) % m).collect();
            assert_eq!(cofactors_mod_leaves(&leaves, &levels), want, "{leaves:?}");
        }
        // Borrowed leaves give the same as owned ones.
        let owned = [big(6), big(10), big(15), big(7)];
        let refs: Vec<&BigUint> = owned.iter().collect();
        let levels = product_tree(&refs);
        assert_eq!(
            cofactors_mod_leaves(&refs, &levels),
            cofactors_mod_leaves(&owned, &levels)
        );
    }

    #[test]
    fn the_linear_combination_up_agrees_with_sum_of_cofactors() {
        for leaves in leaf_sets() {
            let levels = product_tree(&leaves);
            let p = tree_product(&leaves, &levels);
            let vals: Vec<BigUint> = leaves
                .iter()
                .enumerate()
                .map(|(i, m)| big(i as u64 + 1) % m)
                .collect();
            let want: BigUint = leaves
                .iter()
                .zip(&vals)
                .map(|(m, v)| v * (p.as_ref() / m))
                .sum();
            assert_eq!(
                linear_combination_up(vals, &leaves, &levels),
                want,
                "k={}",
                leaves.len()
            );
        }
    }

    /// Exercises both Theorem 2.1 (`mul`) and Theorem 2.2 (cyclic NTT with shared parent
    /// spectrum) paths of [`remainders`] and [`cofactors_mod_leaves`] on wide trees past the
    /// test NTT width (`MUL_LEAF = 48` words), including 512 odd primes and wide skewed leaves.
    #[test]
    fn the_scaled_remainders_and_cofactors_agree_past_ntt_width() {
        // First 512 odd primes: 10 tree levels, crossing the test NTT width at upper levels.
        let mut primes: Vec<BigUint> = Vec::with_capacity(512);
        let mut cand = 3u64;
        while primes.len() < 512 {
            if zed_numtheory::is_prime(cand) {
                primes.push(big(cand));
            }
            cand += 2;
        }
        let levels = product_tree(&primes);
        let p = tree_product(&primes, &levels);
        let x = (&*p * 7u32 + 123456789u64) ^ (BigUint::one() << 2000u32);
        let got_rem = remainders(&x, &primes, &levels);
        let want_rem: Vec<BigUint> = primes.iter().map(|m| &x % m).collect();
        assert_eq!(got_rem, want_rem, "512 primes remainders");
        let got_cof = cofactors_mod_leaves(&primes, &levels);
        let want_cof: Vec<BigUint> = primes.iter().map(|m| (p.as_ref() / m) % m).collect();
        assert_eq!(got_cof, want_cof, "512 primes cofactors");

        // Wide multi-word leaves (100+ words each) that force Theorem 2.2 cyclic NTT at every
        // internal level, with an odd leaf count (9) so a carried node appears at multiple levels.
        let mut rng = crate::seed::Rng::new(crate::seed::seed("scaled_wide_leaves"));
        let wide_leaves: Vec<BigUint> = (0..9)
            .map(|i| {
                let words = 90 + (i % 3) * 40;
                let digits: Vec<u32> = (0..2 * words).map(|_| rng.next_u64() as u32).collect();
                BigUint::new(digits) | BigUint::one()
            })
            .collect();
        let wlevels = product_tree(&wide_leaves);
        let wp = tree_product(&wide_leaves, &wlevels);
        let wx = (&*wp >> 1u32) + big(987654321);
        let wgot = remainders(&wx, &wide_leaves, &wlevels);
        let wwant: Vec<BigUint> = wide_leaves.iter().map(|m| &wx % m).collect();
        assert_eq!(wgot, wwant, "wide leaves remainders");
        let wcof = cofactors_mod_leaves(&wide_leaves, &wlevels);
        let wcof_want: Vec<BigUint> = wide_leaves.iter().map(|m| (wp.as_ref() / m) % m).collect();
        assert_eq!(wcof, wcof_want, "wide leaves cofactors");
    }

    /// Moduli 2, 4, .., 2^k (the shape of `pncx_power_propagation_scale`) and odd moduli, with
    /// `x mod P` just under, at and just over 7/8 of the width of `P` (the switch), so both the
    /// exact descent and the scaled tree run; each against one division a leaf. The cost of the
    /// short case is measured by that bench (it times out without the exact descent).
    #[test]
    fn the_remainders_of_a_short_x_take_the_exact_descent() {
        let powers: Vec<BigUint> = (1..=60u32).map(|i| BigUint::one() << i).collect();
        let odd: Vec<BigUint> = (0..40u64).map(|i| big(1_000_003 + 2 * i)).collect();
        for leaves in [powers, odd] {
            let levels = product_tree(&leaves);
            let cut = (7 * tree_product(&leaves, &levels).bits()).div_ceil(8);
            for w in [1, 61, cut - 1, cut, cut + 1] {
                let x = (BigUint::one() << w) - big(1);
                let got = remainders(&x, &leaves, &levels);
                let want: Vec<BigUint> = leaves.iter().map(|m| &x % m).collect();
                assert_eq!(got, want, "width {w}");
            }
        }
    }

    /// [`scaled_descend_switch`] at every switch width, from 0 (the scaled tree to the leaves)
    /// to past every node (the descent from the root), against one division a leaf: odd counts
    /// (carried nodes at several levels), leaves 1 (nodes `v = 1`), one wide leaf among narrow
    /// ones (a level with one wide node keeps the scaled tree), word leaves and wide leaves.
    #[test]
    fn the_scaled_tree_switches_to_the_descent_at_any_level() {
        let mut rng = crate::seed::Rng::new(crate::seed::seed("scaled_to_exact"));
        let mut odd = |words: usize| -> BigUint {
            let digits: Vec<u32> = (0..2 * words).map(|_| rng.next_u64() as u32).collect();
            BigUint::new(digits) | BigUint::one() | (BigUint::one() << (64 * words - 1))
        };
        let mut one_wide: Vec<BigUint> = (0..37).map(|_| odd(1)).collect();
        one_wide[20] = odd(300);
        let families: Vec<Vec<BigUint>> = vec![
            (0..301).map(|_| odd(1)).collect(),
            (0..13).map(|i| odd(1 + 30 * (i % 4))).collect(),
            one_wide,
            (0..41u64)
                .map(|i| big(if i % 5 == 0 { 1 } else { 1_000_003 + 2 * i }))
                .collect(),
            (1..=70u32).map(|i| BigUint::one() << i).collect(),
        ];
        for leaves in families {
            let levels = product_tree(&leaves);
            let p = tree_product(&leaves, &levels).into_owned();
            let x = &p - big(1) - (&p >> 5u32);
            let want: Vec<BigUint> = leaves.iter().map(|m| &x % m).collect();
            for w in [0, 1, 2, 4, 16, 64, 128, 512, 1 << 40] {
                let got = scaled_descend_switch(&x, &p, &leaves, &levels, w);
                assert_eq!(got, want, "{} leaves, switch at {w} words", leaves.len());
            }
        }
    }

    /// The switch in [`remainders`] between the exact descent and the scaled tree, on both
    /// sides: for `x` of `w` bits under `P` (the top `w` bits of `P`), `w` from `1/64` of
    /// `bits(P)` to all of it, on three families of leaves (1024 odd words; 2, 4, .., 2^200;
    /// 32 odd leaves of 64 words, past the transform width at the top levels). Prints the
    /// instructions and bytes of each method and holds their answers equal. The measurements
    /// and the switch they give are in the comment at the switch in [`remainders`].
    #[test]
    fn the_remainders_crossover_axis() {
        let mut meter = crate::scaling::Meter::new();
        let mut rng = crate::seed::Rng::new(crate::seed::seed("remainders_crossover"));
        let mut odd = |words: usize| -> BigUint {
            let digits: Vec<u32> = (0..2 * words).map(|_| rng.next_u64() as u32).collect();
            BigUint::new(digits) | BigUint::one() | (BigUint::one() << (64 * words - 1))
        };
        let families: Vec<(&str, Vec<BigUint>)> = vec![
            ("words", (0..1024).map(|_| odd(1)).collect()),
            (
                "powers",
                (1..=200u32).map(|i| BigUint::one() << i).collect(),
            ),
            ("wide", (0..32).map(|_| odd(64)).collect()),
        ];
        for (name, leaves) in families {
            let levels = product_tree(&leaves);
            let p = tree_product(&leaves, &levels).into_owned();
            let n = p.bits();
            for (num, den) in [
                (1, 64),
                (1, 16),
                (1, 8),
                (1, 4),
                (3, 8),
                (1, 2),
                (5, 8),
                (3, 4),
                (7, 8),
                (1, 1),
            ] {
                let w = (n * num / den).max(1);
                let x = &p >> (n - w);
                let x = if x == p { &x - big(1) } else { x };
                let (mut exact, mut scaled) = (Vec::new(), Vec::new());
                let e = meter.work(|| exact = descend(x.clone(), &leaves, &levels));
                let s = meter.work(|| scaled = scaled_descend(&x, &p, &leaves, &levels));
                assert_eq!(exact, scaled, "{name} w {w}");
                eprintln!(
                    "remainders crossover {name} bits(P) {n} w {num}/{den}: exact {} instr {} bytes; scaled {} instr {} bytes",
                    e.units, e.bytes, s.units, s.bytes
                );
            }
        }
    }
}
