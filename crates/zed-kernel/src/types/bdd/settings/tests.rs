//! Tests of the treaps of settings. They are a file of their own, as `bdd/tests.rs` is for
//! `bdd.rs`: they name `types::Row` and `bdd::tests::atom`, and `settings.rs` naming them would
//! put it in an import cycle with `types.rs` and `bdd.rs` (`s_01f_import_graph`).

use super::*;
use crate::types::Row;
use crate::types::bdd::tests::atom;
use crate::types::hash::mix;
use std::collections::BTreeSet;

/// Every node above its children and its settings in order, and its length right.
fn well_formed(t: &Tree<Row>) {
    let mut stack: Vec<&Node<Row>> = t.as_deref().into_iter().collect();
    while let Some(n) = stack.pop() {
        assert_eq!(n.len, 1 + len(&n.left) + len(&n.right));
        for c in [n.left.as_deref(), n.right.as_deref()]
            .into_iter()
            .flatten()
        {
            assert!(above(n, c));
            stack.push(c);
        }
    }
    let k = keys(t);
    assert!(k.windows(2).all(|w| w[0] < w[1]));
}

/// Settings drawn from a fixed rule over `0..span`, so the sets overlap in part.
fn sample(seed: u64, count: u64, span: u64) -> Vec<Key<Row>> {
    (0..count)
        .map(|i| {
            let h = mix(seed, i) % (2 * span);
            (atom(h / 2), h % 2 == 1)
        })
        .collect()
}

#[test]
fn union_and_meet_agree_with_ordered_sets() {
    for (seed, (a, b, span)) in [(0, 0, 4), (1, 5, 4), (7, 7, 10), (40, 3, 30), (64, 64, 50)]
        .into_iter()
        .enumerate()
    {
        let (xs, ys) = (
            sample(2 * seed as u64, a, span),
            sample(2 * seed as u64 + 1, b, span),
        );
        let (x, y) = (from_keys(xs.clone()), from_keys(ys.clone()));
        let (bx, by): (BTreeSet<_>, BTreeSet<_>) =
            (xs.into_iter().collect(), ys.into_iter().collect());
        let u = union(&x, &y);
        let m = meet(&x, &y);
        for t in [&x, &y, &u, &m] {
            well_formed(t);
        }
        assert_eq!(
            keys(&u),
            bx.union(&by).cloned().collect::<Vec<_>>(),
            "{seed}"
        );
        assert_eq!(
            keys(&m),
            bx.intersection(&by).cloned().collect::<Vec<_>>(),
            "{seed}"
        );
        for k in bx.union(&by) {
            assert!(contains(&u, k));
            assert_eq!(contains(&m, k), bx.contains(k) && by.contains(k));
        }
        // One set has one shape: the union built from the settings at once is the same tree.
        let whole = from_keys(keys(&u));
        assert_eq!(shape(&whole), shape(&u), "{seed}");
        assert!(same(&union(&x, &x), &x) && same(&meet(&x, &x), &x));
        // Three or more at once agree with the two at a time, whatever the largest.
        let z = from_keys(sample(100 + seed as u64, 2 * a + 1, span));
        let bz: BTreeSet<_> = keys(&z).into_iter().collect();
        let all = union_all(&[&x, &y, &z]);
        well_formed(&all);
        let want: BTreeSet<_> = bx.union(&by).cloned().collect();
        assert_eq!(
            keys(&all),
            want.union(&bz).cloned().collect::<Vec<_>>(),
            "{seed}"
        );
        assert_eq!(shape(&all), shape(&union(&u, &z)), "{seed}");
        let both = meet_all(&[&z, &x, &y]);
        well_formed(&both);
        let want: BTreeSet<_> = bx.intersection(&by).cloned().collect();
        assert_eq!(
            keys(&both),
            want.intersection(&bz).cloned().collect::<Vec<_>>()
        );
        assert!(same(&union_all(&[&x]), &x) && same(&meet_all(&[&x]), &x));
    }
}

fn shape(t: &Tree<Row>) -> String {
    let mut out = String::new();
    let mut stack = vec![t.as_deref()];
    while let Some(n) = stack.pop() {
        match n {
            None => out.push('.'),
            Some(n) => {
                out += &format!("({:?},{})", n.key.0, n.key.1);
                stack.push(n.right.as_deref());
                stack.push(n.left.as_deref());
            }
        }
    }
    out
}

/// The number of nodes on the longest path from the root, walked from a stack.
fn height(t: &Tree<Row>) -> usize {
    let mut most = 0;
    let mut stack: Vec<(&Node<Row>, usize)> = t.as_deref().map(|n| (n, 1)).into_iter().collect();
    while let Some((n, d)) = stack.pop() {
        most = most.max(d);
        for c in [n.left.as_deref(), n.right.as_deref()]
            .into_iter()
            .flatten()
        {
            stack.push((c, d + 1));
        }
    }
    most
}

/// The settings whose priorities rose with their order under the fixed hash that the drawn
/// priorities replace (PERF-treap-seeded-priorities, COMPLEXITY.md K123), `mix(mix(17, d), v)`
/// of the atom's digest `d`: the longest rising run among the settings of `0` to `2^16 - 1`, by
/// patience sorting, has 506 settings (Erdős and Szekeres give about `2 sqrt(n)`), and under
/// that hash their set was a path of 506 nodes. Under the drawn priorities it is a treap of
/// independent priorities, and its height is checked against Seidel and Aragon's Lemma 4.8 at
/// probability `1/n`, as `set/tests.rs` does. The unit tests of this crate fix the draw
/// (`priority::fixed_seed`), so the height checked is that of one draw, the same on every run.
#[test]
fn settings_chosen_against_a_fixed_hash_give_a_logarithmic_height() {
    let mut all: Vec<Key<Row>> = (0..1 << 16).map(|i| (atom(i), true)).collect();
    all.sort();
    let old: Vec<u64> = all
        .iter()
        .map(|k| mix(mix(17, k.0.digest()), u64::from(k.1)))
        .collect();
    let mut tails: Vec<usize> = Vec::new();
    let mut prev = vec![usize::MAX; old.len()];
    for i in 0..old.len() {
        let j = tails.partition_point(|&t| old[t] < old[i]);
        if j > 0 {
            prev[i] = tails[j - 1];
        }
        if j == tails.len() {
            tails.push(i)
        } else {
            tails[j] = i
        }
    }
    let mut pick = vec![*tails.last().expect("settings")];
    while prev[*pick.last().expect("a pick")] != usize::MAX {
        pick.push(prev[*pick.last().expect("a pick")]);
    }
    let n = pick.len();
    let t = from_keys(pick.iter().map(|&i| all[i].clone()).collect());
    assert_eq!(len(&t), n);
    let h = height(&t);
    let ln_n = (n as f64).ln();
    let c = (h as f64 - 1.0) / (2.0 * ln_n);
    let ln_bound = 2f64.ln() + ln_n - c * (c / std::f64::consts::E).ln() * (ln_n - 1.0);
    assert!(
        c <= std::f64::consts::E || ln_bound >= -ln_n,
        "{n} settings chosen against the fixed hash: height {h} nodes, c = {c:.2}, a \
         probability below e^{ln_bound:.1} for independent priorities, under 1/n"
    );
}
