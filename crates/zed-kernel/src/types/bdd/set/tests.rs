//! The depth of the sets' treaps on structured keys (PROOF-treap-digest-priorities, COMPLEXITY.md
//! K123). A node's priority is a fixed hash of its literal's digest, so no bound on the depth
//! holds for every input (K123 gives a family that makes a path); the bounds of the treaps hold
//! under the model that the priorities of distinct literals are independent and uniform. These
//! tests check that keys built the way programs build them (consecutive numbers, names, rows that
//! share a prefix or a suffix, digests that are consecutive numbers) give depths that model would
//! give: each fails when Seidel and Aragon's bound puts the probability of the measured height,
//! under the model, below `1/n`.
//!
//! The bound. Seidel and Aragon ("Randomized search trees", Algorithmica 16, 1996, Lemma 4.8): for
//! independent identically distributed priorities in a treap of `n > 1` nodes, every node `x`,
//! and every `c > 1`, `Pr[D(x) >= 1 + 2c ln n] < 2 (n/e)^(-c ln(c/e))`, where `D(x)` counts the
//! nodes from `x` to the root, `x` included. A union bound over the `n` nodes gives
//! `Pr[height >= 1 + 2c ln n] < 2n (n/e)^(-c ln(c/e))`. The tests take `1/n` for the probability
//! ("with high probability"), so a height `h` fails when `c = (h - 1) / (2 ln n)` has
//! `c > e` and `ln 2 + ln n - c ln(c/e) (ln n - 1) < -ln n`. At `n = 65,536` the largest height
//! that passes has `c = 4.50`, 100 nodes, or `6.25 log2 n`; Devroye's limit for the height of
//! such a tree is `4.311 ln n = 2.99 log2 n` (quoted by Seidel and Aragon), 48 nodes.
//!
//! Equal priorities. Literals whose priorities are equal (atoms whose digests collide) are ordered
//! by their literals ([`above`]), so they are not independent. Let the classes be the groups of
//! two or more nodes of one priority, and `T` their total size. A node `y` outside every class is
//! an ancestor of `x` exactly when its priority is above every other priority of the keys from
//! `x` to `y` (Seidel and Aragon, Lemma 4.3, which needs only that `y`'s priority equals no other
//! there); then it is also above every priority of those keys outside the classes, so `y` is an
//! ancestor of `x` in the treap of `x` and the keys outside the classes, whose priorities are
//! distinct. So `D(x)` is at most `x`'s depth in that treap of at most `n` nodes, plus `T`: the
//! tests measure `T` and apply the bound to the height less `T`.

use super::*;
use crate::types::{Row, Shared, Type};
use crate::value::Value;

/// The number of nodes on the longest path from the root, and the total size of the classes of
/// nodes that share a priority, walked from a stack.
fn shape(t: &Tree<Row>) -> (usize, usize) {
    let mut height = 0;
    let mut by_prio: crate::digest::DigestMap<u64, usize> = Default::default();
    let mut stack: Vec<(&Arc<Set<Row>>, usize)> = t.iter().map(|r| (r, 1)).collect();
    while let Some((n, d)) = stack.pop() {
        height = height.max(d);
        *by_prio.entry(n.prio).or_default() += 1;
        for c in [&n.left, &n.right].into_iter().flatten() {
            stack.push((c, d + 1));
        }
    }
    let tied = by_prio.values().filter(|&&k| k > 1).sum();
    (height, tied)
}

/// The set of `atoms`, each taken as `taken(i)` says, checked against the bound in the module
/// comment. Returns the height and the size of the classes of equal priorities.
fn check(family: &str, atoms: Vec<Row>, taken: impl Fn(usize) -> bool) -> (usize, usize) {
    let mut keys: Vec<Key<Row>> = atoms
        .into_iter()
        .enumerate()
        .map(|(i, a)| (a, taken(i)))
        .collect();
    keys.sort();
    keys.dedup_by(|a, b| a.0 == b.0);
    let n = keys.len();
    let t = from_sorted(keys);
    assert_eq!(len(t.as_ref()), n);
    let (height, tied) = shape(&t);
    let ln_n = (n as f64).ln();
    let c = (height.saturating_sub(tied) as f64 - 1.0) / (2.0 * ln_n);
    let ln_bound = 2f64.ln() + ln_n - c * (c / std::f64::consts::E).ln() * (ln_n - 1.0);
    assert!(
        c <= std::f64::consts::E || ln_bound >= -ln_n,
        "{family}: {n} literals, height {height} nodes, {tied} in classes of equal priority: \
         c = {c:.2}, and the model gives this height a probability below e^{ln_bound:.1}, \
         under 1/n"
    );
    (height, tied)
}

const N: usize = 1 << 16;

fn int(i: usize) -> Type {
    Type::lit(&Value::Int(i as i64)).expect("a literal")
}

/// A row whose digest and names-aware digest are `d`, over `items`.
fn forced(d: u64, items: Vec<Type>) -> Row {
    Row(Shared::new(d, d, items))
}

#[test]
fn consecutive_numbers_give_a_logarithmic_height() {
    check(
        "numbers",
        (0..N).map(|i| Row::new(vec![int(i)])).collect(),
        |_| true,
    );
    check(
        "numbers, refused",
        (0..N).map(|i| Row::new(vec![int(i)])).collect(),
        |_| false,
    );
    check(
        "numbers, alternating",
        (0..N).map(|i| Row::new(vec![int(i)])).collect(),
        |i| i % 2 == 0,
    );
}

#[test]
fn consecutive_names_give_a_logarithmic_height() {
    let names = |f: fn(&str) -> Type| (0..N).map(move |i| Row::new(vec![f(&format!("a{i}"))]));
    check(
        "strings",
        names(|s| Type::lit(&Value::from(s)).expect("a literal")).collect(),
        |_| true,
    );
    check("atoms", names(Type::atom).collect(), |_| true);
}

#[test]
fn rows_sharing_a_prefix_or_a_suffix_give_a_logarithmic_height() {
    let common = || std::iter::repeat_n(int(0), 8);
    let prefix = (0..N).map(|i| Row::new(common().chain([int(i)]).collect()));
    check("shared prefix", prefix.collect(), |_| true);
    let suffix = (0..N).map(|i| Row::new(std::iter::once(int(i)).chain(common()).collect()));
    check("shared suffix", suffix.collect(), |_| true);
}

/// Digests that are themselves structured, as the hash takes them: consecutive numbers, numbers
/// in the high half of the word, and multiples of the constant the hash's step adds.
#[test]
fn structured_digests_give_a_logarithmic_height() {
    let rows = |d: fn(u64) -> u64| {
        (0..N as u64)
            .map(move |i| forced(d(i), vec![int(i as usize), Type::atom("structured")]))
            .collect()
    };
    check("digests 0 to n - 1", rows(|i| i), |_| true);
    check("digests i * 2^32", rows(|i| i << 32), |_| true);
    check(
        "digests i * the step's constant",
        rows(|i| i.wrapping_mul(0x9e37_79b9_7f4a_7c15)),
        |_| true,
    );
}

/// `m` distinct atoms of one digest among `N` others share one priority, and they are next to
/// each other in the order, so they make a path of `m` nodes: the height is at least `m`, and at
/// most the bound for the other atoms plus `m`.
#[test]
fn colliding_digests_add_at_most_their_number_to_the_height() {
    let m = 256;
    let shared = Row::new(vec![int(0)]).digest();
    let atoms = (0..N)
        .map(|i| Row::new(vec![int(i)]))
        .chain((0..m).map(|j| forced(shared, vec![int(j), Type::atom("collides")])))
        .collect();
    let (height, tied) = check("colliding digests", atoms, |_| true);
    assert!(
        height >= m && tied > m,
        "height {height}, {tied} in classes of equal priority"
    );
}
