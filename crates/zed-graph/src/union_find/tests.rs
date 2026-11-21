use super::{Compression, Diff, Keep, Linking, Offset, Parity, Signed, UnionFind};
use crate::seed::Rng;

const COMPRESSIONS: [Compression; 3] = [Compression::None, Compression::Halving, Compression::Full];
const LINKINGS: [Linking; 2] = [Linking::Rank, Linking::Size];
const KEEPS: [Keep; 4] = [Keep::Rule, Keep::First, Keep::Second, Keep::Least];

/// The number of edges from `x` to its root.
fn depth<V, O: Offset>(uf: &UnionFind<V, O>, mut x: usize) -> usize {
    let mut d = 0;
    while uf.parent(x) != x {
        x = uf.parent(x);
        d += 1;
    }
    d
}

/// Runs random unions under `compression` and `linking` on `UnionFind` and on a plain labeling
/// (each element's class label, relabeled in full on each union), checking the classes, each
/// [`Keep`]'s root and, under [`Linking::Size`], each class's size; returns the unions that
/// joined two classes and those that found one.
fn agree(rng: &mut Rng, compression: Compression, linking: Linking) -> (usize, usize) {
    let n = 1 + rng.below(24);
    let mut uf = UnionFind::<(), ()>::new(n, compression, linking);
    let mut label: Vec<usize> = (0..n).collect();
    let (mut joined, mut same) = (0, 0);
    for _ in 0..rng.below(2 * n + 1) {
        let (a, b) = (rng.below(n), rng.below(n));
        let keep = rng.pick(&KEEPS);
        let was = label[a] == label[b];
        let (ra, rb) = (uf.find(a), uf.find(b));
        let sizes = (linking == Linking::Size).then(|| (uf.size(ra), uf.size(rb)));
        let did = uf.join(a, b, &(), keep, |_, _, _| {});
        assert_eq!(did.is_ok(), !was, "{keep:?} {a} {b}");
        if was {
            same += 1;
            continue;
        }
        joined += 1;
        let root = uf.find(a);
        assert_eq!(did, Ok(root));
        match keep {
            Keep::Rule => match sizes {
                Some((sa, sb)) => assert_eq!(root, if sa >= sb { ra } else { rb }),
                None => assert!(root == ra || root == rb),
            },
            Keep::First => assert_eq!(root, ra),
            Keep::Second => assert_eq!(root, rb),
            Keep::Least => assert_eq!(root, ra.min(rb)),
        }
        let (from, to) = (label[b], label[a]);
        for l in &mut label {
            if *l == from {
                *l = to;
            }
        }
    }
    for a in 0..n {
        assert_eq!(uf.find_shared(a), uf.find(a));
        if linking == Linking::Size {
            let count = label.iter().filter(|&&l| l == label[a]).count();
            let r = uf.find(a);
            assert_eq!(uf.size(r), count, "the size of {a}'s class");
        }
        for b in 0..n {
            assert_eq!(uf.same(a, b), label[a] == label[b], "{a} {b}");
        }
    }
    (joined, same)
}

#[test]
fn union_find_classes_match_a_plain_labeling() {
    // Built: both outcomes of a union, so the check can fail either way on every run.
    let mut uf = UnionFind::<(), ()>::new(3, Compression::Halving, Linking::Rank);
    assert!(uf.union(0, 1));
    assert!(!uf.union(1, 0));
    assert!(uf.union_least(2, 1));
    assert_eq!(uf.find(2), 0);
    assert_eq!(uf.push(), 3);
    assert!(uf.union_into(3, 0));
    assert_eq!(uf.find(1), 3);
    let (mut rng, _) = Rng::fresh("union_find_classes_match_a_plain_labeling");
    for compression in COMPRESSIONS {
        for linking in LINKINGS {
            let (mut joined, mut same) = (0, 0);
            for _ in 0..1000 {
                let (j, s) = agree(&mut rng, compression, linking);
                joined += j;
                same += s;
            }
            assert!(
                joined > 0 && same > 0,
                "{compression:?} {linking:?}: {joined} {same}"
            );
        }
    }
}

/// An offset applied to a value: what the tests compare each found offset with.
trait Apply: Offset {
    type X: Clone + PartialEq + std::fmt::Debug;
    /// The value of the element from its base's.
    fn apply(&self, x: &Self::X) -> Self::X;
    /// A value drawn at random.
    fn draw(rng: &mut Rng) -> Self::X;
    /// An offset drawn at random that gives `to` from `from`.
    fn between(rng: &mut Rng, to: &Self::X, from: &Self::X) -> Self;
}

impl Apply for Diff<i64> {
    type X = i64;
    fn apply(&self, x: &i64) -> i64 {
        x + self.0
    }
    fn draw(rng: &mut Rng) -> i64 {
        rng.int(-20, 20)
    }
    fn between(_: &mut Rng, to: &i64, from: &i64) -> Self {
        Diff(to - from)
    }
}

impl Apply for Signed<i64> {
    type X = i64;
    fn apply(&self, x: &i64) -> i64 {
        if self.neg { self.d - x } else { self.d + x }
    }
    fn draw(rng: &mut Rng) -> i64 {
        rng.int(-20, 20)
    }
    fn between(rng: &mut Rng, to: &i64, from: &i64) -> Self {
        let neg = rng.below(2) == 1;
        let d = if neg { to + from } else { to - from };
        Signed { neg, d }
    }
}

impl Apply for Parity {
    type X = bool;
    fn apply(&self, x: &bool) -> bool {
        *x != self.0
    }
    fn draw(rng: &mut Rng) -> bool {
        rng.below(2) == 1
    }
    fn between(_: &mut Rng, to: &bool, from: &bool) -> Self {
        Parity(to != from)
    }
}

/// Values drawn first, each record true of them, so every find must give a function that
/// takes the root's value to the element's, and each record inside a class the function the
/// class holds, which takes `b`'s value to `a`'s. Returns the records inside a class that
/// disagreed with it (drawn at random, a record agrees only by chance) and those that agreed,
/// or the first wrong find.
fn offsets_agree<O: Apply>(
    rng: &mut Rng,
    compression: Compression,
    linking: Linking,
) -> Result<(usize, usize), String> {
    let n = 1 + rng.below(24);
    let x: Vec<O::X> = (0..n).map(|_| O::draw(rng)).collect();
    let mut uf = UnionFind::<(), O>::new(n, compression, linking);
    let mut label: Vec<usize> = (0..n).collect();
    let (mut joined, mut held) = (0, 0);
    for _ in 0..rng.below(2 * n + 1) {
        let (a, b) = (rng.below(n), rng.below(n));
        let keep = rng.pick(&KEEPS);
        let r = O::between(rng, &x[a], &x[b]);
        match uf.join(a, b, &r, keep, |_, _, _| {}) {
            Ok(_) => {
                assert_ne!(label[a], label[b]);
                joined += 1;
                let (from, to) = (label[b], label[a]);
                for l in &mut label {
                    if *l == from {
                        *l = to;
                    }
                }
            }
            Err(c) => {
                assert_eq!(label[a], label[b]);
                held += 1;
                if c.apply(&x[b]) != x[a] {
                    return Err(format!("the relation of {a} and {b}"));
                }
            }
        }
        for v in 0..n {
            let (root, f) = uf.find_offset(v);
            let (shared_root, g) = uf.find_offset_shared(v);
            assert_eq!(root, shared_root);
            if f.apply(&x[root]) != x[v] || g.apply(&x[root]) != x[v] {
                return Err(format!("element {v} from its root {root}"));
            }
        }
    }
    Ok((joined, held))
}

/// Runs [`offsets_agree`] under every compression and linking.
fn every_offset_agrees<O: Apply>(name: &str) {
    let (mut rng, _) = Rng::fresh(name);
    for compression in COMPRESSIONS {
        for linking in LINKINGS {
            let (mut joined, mut held) = (0, 0);
            for _ in 0..1000 {
                let (j, h) = offsets_agree::<O>(&mut rng, compression, linking)
                    .unwrap_or_else(|e| panic!("{compression:?} {linking:?}: {e}"));
                joined += j;
                held += h;
            }
            assert!(
                joined > 0 && held > 0,
                "{compression:?} {linking:?}: {joined} {held}"
            );
        }
    }
}

#[test]
fn offset_union_find_matches_plain_values() {
    // Built: a chain 0 <- 1 <- 2 with offsets 5 and -2 (x_1 = x_0 + 5, x_2 = x_1 - 2), the
    // root of `b` staying as the old `OffsetUnionFind::union_into` kept it, then a cycle that
    // agrees and one that does not.
    let mut uf = UnionFind::<(), Diff<i64>>::new(4, Compression::Halving, Linking::Rank);
    let into = |uf: &mut UnionFind<(), Diff<i64>>, b: usize, a: usize, d: i64| {
        uf.join(a, b, &Diff(d), Keep::Second, |_, _, _| {})
            .map(|_| ())
            .map_err(|c| c.0)
    };
    assert_eq!(into(&mut uf, 0, 1, 5), Ok(()));
    assert_eq!(into(&mut uf, 1, 2, -2), Ok(()));
    assert_eq!(uf.find_offset(2), (0, Diff(3)));
    assert_eq!(into(&mut uf, 0, 2, 3), Err(3));
    assert_eq!(into(&mut uf, 0, 2, 4), Err(3));
    assert_eq!(uf.find_offset(3), (3, Diff(0)));
    every_offset_agrees::<Diff<i64>>("offset_union_find_matches_plain_values/diff");
    every_offset_agrees::<Signed<i64>>("offset_union_find_matches_plain_values/signed");
    every_offset_agrees::<Parity>("offset_union_find_matches_plain_values/parity");
}

/// `Signed` with its composition reversed (`inner ∘ self`), which is wrong since two signed
/// offsets do not commute: `(-1, 1) ∘ (1, 1)` gives `-x`, `(1, 1) ∘ (-1, 1)` gives `2 - x`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Reversed(Signed<i64>);

impl Offset for Reversed {
    fn identity() -> Self {
        Reversed(Signed::identity())
    }
    fn compose(&self, inner: &Self) -> Self {
        Reversed(inner.0.compose(&self.0))
    }
    fn inverse(&self) -> Self {
        Reversed(self.0.inverse())
    }
}

impl Apply for Reversed {
    type X = i64;
    fn apply(&self, x: &i64) -> i64 {
        self.0.apply(x)
    }
    fn draw(rng: &mut Rng) -> i64 {
        Signed::<i64>::draw(rng)
    }
    fn between(rng: &mut Rng, to: &i64, from: &i64) -> Self {
        Reversed(Signed::between(rng, to, from))
    }
}

/// Negative control for `offset_union_find_matches_plain_values`: an offset whose composition
/// is in the wrong order is caught by the same check, under every compression (a path of two
/// edges is composed by every find, compressing or not).
#[test]
fn an_offset_composed_in_the_wrong_order_is_caught() {
    let (mut rng, _) = Rng::fresh("an_offset_composed_in_the_wrong_order_is_caught");
    for compression in COMPRESSIONS {
        let caught = (0..1000)
            .any(|_| offsets_agree::<Reversed>(&mut rng, compression, Linking::Rank).is_err());
        assert!(caught, "{compression:?}");
    }
}

#[test]
fn values_merge_by_the_callers_function() {
    // Each class's value is the sorted list of its elements, each with its value less the
    // root's (`x_v - x_root`), merged by the caller: the other class's entries are stated in
    // terms of its root, so the merge adds the edge (`x_other_root - x_kept_root`) to each. A
    // union inside one class must not call the merge.
    let (mut rng, _) = Rng::fresh("values_merge_by_the_callers_function");
    for compression in COMPRESSIONS {
        for linking in LINKINGS {
            for _ in 0..500 {
                let n = 1 + rng.below(24);
                let x: Vec<i64> = (0..n).map(|_| rng.int(-20, 20)).collect();
                let mut uf =
                    UnionFind::<Vec<(usize, i64)>, Diff<i64>>::new(0, compression, linking);
                for v in 0..n {
                    assert_eq!(uf.push_value(vec![(v, 0)]), v);
                }
                let mut label: Vec<usize> = (0..n).collect();
                for _ in 0..rng.below(2 * n + 1) {
                    let (a, b) = (rng.below(n), rng.below(n));
                    let keep = rng.pick(&KEEPS);
                    let mut called = false;
                    let did = uf.join(a, b, &Diff(x[a] - x[b]), keep, |kept, other, edge| {
                        called = true;
                        kept.extend(other.into_iter().map(|(v, o)| (v, o + edge.0)));
                        kept.sort_unstable();
                    });
                    assert_eq!(called, did.is_ok());
                    if did.is_ok() {
                        let (from, to) = (label[b], label[a]);
                        for l in &mut label {
                            if *l == from {
                                *l = to;
                            }
                        }
                    }
                }
                for v in 0..n {
                    let root = uf.find(v);
                    let members: Vec<(usize, i64)> = (0..n)
                        .filter(|&u| label[u] == label[v])
                        .map(|u| (u, x[u] - x[root]))
                        .collect();
                    assert_eq!(*uf.value(root), members, "{compression:?} {linking:?} {v}");
                }
            }
        }
    }
}

#[test]
fn rank_and_size_bound_the_height_without_compression() {
    // Corollary 2 and Lemma 2 of Tarjan and van Leeuwen 1984: linked by rank or size, with no
    // compression, no path is longer than log2 n. Random unions and the worst order for a
    // rule-less link (a chain joined at its newest element) both stay within it.
    let n = 1 << 12;
    let (mut rng, _) = Rng::fresh("rank_and_size_bound_the_height_without_compression");
    for linking in LINKINGS {
        let mut random = UnionFind::<(), ()>::new(n, Compression::None, linking);
        for _ in 0..2 * n {
            random.union(rng.below(n), rng.below(n));
        }
        let mut chain = UnionFind::<(), ()>::new(n, Compression::None, linking);
        for v in 1..n {
            chain.union(v, v - 1);
        }
        for uf in [&random, &chain] {
            let height = (0..n).map(|v| depth(uf, v)).max().unwrap_or(0);
            assert!(height <= 12, "{linking:?}: height {height}");
        }
    }
}

/// Negative control for `rank_and_size_bound_the_height_without_compression`: roots chosen by
/// the caller, with no compression, build a chain of height n - 1, which the same bound
/// refuses.
#[test]
fn a_chosen_root_without_compression_makes_a_chain() {
    let n = 1 << 12;
    let mut uf = UnionFind::<(), ()>::new(n, Compression::None, Linking::Rank);
    for v in 1..n {
        uf.union_into(v, v - 1);
    }
    assert_eq!(depth(&uf, 0), n - 1);
    assert!(depth(&uf, 0) > 12);
}

#[test]
fn each_compression_does_what_it_says_to_the_path() {
    // A chain 0 -> 1 -> … -> 8 (8 the root) and a find of 0: no compression leaves it; halving
    // points 0, 2, 4, 6 at their grandparents; full compression points every element at 8.
    let chain = |compression| {
        let mut uf = UnionFind::<(), Diff<i64>>::new(9, compression, Linking::Rank);
        for v in 1..9 {
            assert!(
                uf.join(v, v - 1, &Diff(1), Keep::First, |_, _, _| {})
                    .is_ok()
            );
        }
        uf
    };
    for compression in COMPRESSIONS {
        let mut uf = chain(compression);
        assert_eq!(uf.find_offset(0), (8, Diff(-8)), "{compression:?}");
        let parents: Vec<usize> = (0..9).map(|v| uf.parent(v)).collect();
        let expected = match compression {
            Compression::None => vec![1, 2, 3, 4, 5, 6, 7, 8, 8],
            Compression::Halving => vec![2, 2, 4, 4, 6, 6, 8, 8, 8],
            Compression::Full => vec![8; 9],
        };
        assert_eq!(parents, expected, "{compression:?}");
        for v in 0..9 {
            assert_eq!(
                uf.find_offset_shared(v),
                (8, Diff(v as i64 - 8)),
                "{compression:?}"
            );
        }
    }
}

#[test]
fn union_roots_keeps_the_named_root_and_passes_the_edge() {
    // Classes {0, 1} (root 0) and {2}, values x = [3, 7, -4], joined at their roots given
    // x_0 = x_2 + 7. Each keep leaves the root it names (the rule: the larger class, 0), each
    // find states x_v - x_root, and the merge is handed x_child - x_root.
    let x = [3i64, 7, -4];
    for linking in LINKINGS {
        for keep in KEEPS {
            let mut uf = UnionFind::<Vec<usize>, Diff<i64>>::new(0, Compression::None, linking);
            for v in 0..3 {
                uf.push_value(vec![v]);
            }
            let first = uf.join(0, 1, &Diff(x[0] - x[1]), Keep::First, |k, o, _| k.extend(o));
            assert!(first.is_ok());
            let mut seen = None;
            let root = uf.union_roots(0, 2, Diff(x[0] - x[2]), keep, |k, o, e| {
                seen = Some(e.0);
                k.extend(o);
                k.sort_unstable();
            });
            let want = match keep {
                Keep::Second => 2,
                _ => 0,
            };
            assert_eq!(root, want, "{linking:?} {keep:?}");
            assert_eq!(seen, Some(x[2 - root] - x[root]), "{linking:?} {keep:?}");
            assert_eq!(*uf.value(root), vec![0, 1, 2], "{linking:?} {keep:?}");
            for v in 0..3 {
                assert_eq!(
                    uf.find_offset(v),
                    (root, Diff(x[v] - x[root])),
                    "{keep:?} {v}"
                );
            }
        }
    }
}

#[test]
fn truncate_drops_elements_opened_as_a_stack() {
    // Elements opened as a stack and joined by `Keep::Least`, as zedc-types `Scope` does:
    // after dropping 3..6 the kept classes are as before the opens, and the next element
    // pushed is 3, in a class of its own.
    for compression in COMPRESSIONS {
        let mut uf = UnionFind::<(), ()>::new(3, compression, Linking::Rank);
        uf.union_least(1, 2);
        for _ in 3..6 {
            uf.push();
        }
        uf.union_least(4, 0);
        uf.union_least(5, 2);
        uf.union_least(3, 5);
        assert!(uf.same(3, 1) && uf.same(4, 0));
        uf.truncate(3);
        assert_eq!(uf.len(), 3);
        let roots: Vec<usize> = (0..3).map(|v| uf.find(v)).collect();
        assert_eq!(roots, vec![0, 1, 1], "{compression:?}");
        assert_eq!(uf.push(), 3);
        assert_eq!(uf.find(3), 3);
        assert!(!uf.same(3, 0) && !uf.same(3, 1), "{compression:?}");
    }
}

#[test]
fn then_is_compose_with_the_zero_shortcut() {
    // `Diff` and `Signed` skip the add in `then` when the inner constant is 0; the result must
    // still be `self ∘ inner`, the sign included.
    for d1 in -2i64..=2 {
        for d2 in -2i64..=2 {
            let mut a = Diff(d1);
            a.then(&Diff(d2));
            assert_eq!(a, Diff(d1).compose(&Diff(d2)), "{d1} {d2}");
            for (n1, n2) in [(false, false), (false, true), (true, false), (true, true)] {
                let (s1, s2) = (Signed { neg: n1, d: d1 }, Signed { neg: n2, d: d2 });
                let mut a = s1.clone();
                a.then(&s2);
                assert_eq!(a, s1.compose(&s2), "{s1:?} {s2:?}");
            }
        }
    }
}

#[test]
fn rank_bounds_the_height_of_a_root() {
    // Two pairs joined, then the pairs: the root's rank is 2, the tree's height 2.
    let mut uf = UnionFind::<(), ()>::new(4, Compression::None, Linking::Rank);
    assert!((0..4).all(|v| uf.rank(v) == 0));
    uf.union(0, 1);
    uf.union(2, 3);
    let r = uf.find(0);
    assert_eq!(uf.rank(r), 1);
    uf.union(0, 2);
    let r = uf.find(0);
    assert_eq!(uf.rank(r), 2);
    assert_eq!((0..4).map(|v| depth(&uf, v)).max(), Some(2));
}

/// The benchmarks of the union-find, run by `tools/run_tests.sh --bench`.
mod bench {
    use std::collections::BTreeMap;

    use super::{Compression, Linking, Rng, UnionFind};
    use crate::scaling;

    /// `n` elements and `n` unions of random pairs, then a find of each: O(n α(n)), Theorem 3
    /// of Tarjan and van Leeuwen 1984 (JACM 31(2), doi:10.1145/62.2160; the full comment is
    /// at the head of `union_find.rs`).
    fn churn(n: usize, pairs: &[(usize, usize)]) -> usize {
        let mut uf = UnionFind::<(), ()>::new(n, Compression::Halving, Linking::Rank);
        for &(a, b) in pairs {
            uf.union(a, b);
        }
        (0..n).filter(|&v| uf.find(v) == v).count()
    }

    /// Small instances: `union_find_classes_match_a_plain_labeling`.
    #[test]
    fn union_find_takes_near_linear_time() {
        // 200,000 elements and 8 times as many: large enough that a run takes milliseconds
        // and timing noise is small, small enough that the larger run stays well under a
        // second.
        let n = 200_000;
        // A fixed seed (any serves), so the pairs are the same on every run and the two sizes
        // compare like with like.
        let mut rng = Rng::new(0);
        let built: BTreeMap<usize, Vec<(usize, usize)>> = [n, scaling::FACTOR * n]
            .into_iter()
            .map(|m| {
                let pairs = (0..m).map(|_| (rng.below(m), rng.below(m))).collect();
                (m, pairs)
            })
            .collect();
        scaling::check("n unions and n finds on n elements", n, |m| {
            assert!(churn(m, &built[&m]) >= 1);
        });
    }

    /// A chain of `n` elements joined with the root chosen as the newest (the worst order for a
    /// rule-less link), then a find of each: path halving keeps it O(n log n) (Theorem 6 of
    /// Tarjan and van Leeuwen 1984).
    #[test]
    fn union_into_a_chain_takes_n_log_n_time() {
        // As in `union_find_takes_near_linear_time`.
        let n = 200_000;
        scaling::check("n chained union_into then n finds", n, |m| {
            let mut uf = UnionFind::<(), ()>::new(m, Compression::Halving, Linking::Rank);
            for v in 1..m {
                uf.union_into(v, v - 1);
            }
            assert_eq!((0..m).filter(|&v| uf.find(v) == v).count(), 1);
        });
    }
}
