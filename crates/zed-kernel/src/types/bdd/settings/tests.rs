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
