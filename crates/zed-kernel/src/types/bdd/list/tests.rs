//! The digests and the depth of the treaps of cells of lists (PERF-set-digest-shape-free,
//! COMPLEXITY.md K123). A cell's priority is drawn once per run ([`priority`]), so its shape
//! follows the draw, and its digests must not: they are folds of the blocks in order
//! ([`folded`]). The kernel's unit tests take the fixed draw of seed 0 when `ZED_TREAP_SEED` is
//! unset, so the height test checks one draw; the bound it checks is the one of `set/tests.rs`.

use super::*;
use crate::types::Row;
use crate::value::Value;

/// The block of the one literal of `i`, taken.
fn block(i: u64) -> Arc<Set<Row>> {
    let row = Row::new(vec![
        crate::types::Type::lit(&Value::Int(i as i64)).expect("a literal"),
    ]);
    set::single((row, true))
}

/// One sequence of three blocks built by hand with each block at the root: the digests are the
/// same for the three shapes (a fold of the blocks in order), and the lengths too.
#[test]
fn every_shape_of_a_sequence_has_its_digests() {
    let [a, b, c] = [0, 1, 2].map(block);
    let one = |x: &Arc<Set<Row>>| Some(cell(None, x.clone(), None));
    let shapes = [
        cell(None, a.clone(), Some(cell(None, b.clone(), one(&c)))),
        cell(one(&a), b.clone(), one(&c)),
        cell(Some(cell(None, a.clone(), one(&b))), c.clone(), None),
    ];
    let digests = shapes.each_ref().map(|s| (s.digest, s.name_digest, s.len));
    assert!(digests.iter().all(|&d| d == digests[0]), "{digests:?}");
    // Two orders of the same blocks are two sequences.
    let other = cell(one(&b), a.clone(), one(&c));
    assert_ne!(other.digest, digests[0].0);
}

/// Blocks laid out so that the fixed hash that was the priority before the draw
/// (`mix(mix(19, digest), taken)` of the block's root literal, which a program can compute)
/// rises with the position: under that hash the sequence was a path of `n` cells. Under the
/// run's draw its height is checked against Seidel and Aragon's Lemma 4.8 at probability `1/n`,
/// as in `set/tests.rs`: with `c = (h - T - 1) / (2 ln n)`, `T` the cells in classes of equal
/// priority, the test fails when `c > e` and `ln 2 + ln n - c ln(c/e)(ln n - 1) < -ln n`.
#[test]
fn blocks_chosen_against_a_fixed_hash_give_a_logarithmic_height() {
    let n = 1 << 14;
    let mut blocks: Vec<Arc<Set<Row>>> = (0..n as u64).map(block).collect();
    let fixed = |b: &Arc<Set<Row>>| mix(mix(19, b.key.0.digest()), u64::from(b.key.1));
    blocks.sort_by_key(fixed);
    // Each block is merged at the end, so the sequence is built in `O(n log n)` expected.
    let seq = (blocks.into_iter()).fold(None, |s, b| merge(s, Some(cell(None, b, None))));
    assert_eq!(len(&seq), n);
    let mut height = 0;
    let mut by_prio: crate::digest::DigestMap<u64, usize> = Default::default();
    let mut stack: Vec<(&Arc<Cell<Row>>, usize)> = seq.iter().map(|c| (c, 1)).collect();
    while let Some((c, d)) = stack.pop() {
        height = height.max(d);
        *by_prio.entry(c.prio).or_default() += 1;
        stack.extend(
            [&c.left, &c.right]
                .into_iter()
                .flatten()
                .map(|k| (k, d + 1)),
        );
    }
    let tied: usize = by_prio.values().filter(|&&k| k > 1).sum();
    let ln_n = (n as f64).ln();
    let c = (height.saturating_sub(tied) as f64 - 1.0) / (2.0 * ln_n);
    let ln_bound = 2f64.ln() + ln_n - c * (c / std::f64::consts::E).ln() * (ln_n - 1.0);
    assert!(
        c <= std::f64::consts::E || ln_bound >= -ln_n,
        "{n} blocks, height {height} cells, {tied} in classes of equal priority: c = {c:.2}, \
         and the model gives this height a probability below e^{ln_bound:.1}, under 1/n"
    );
}
