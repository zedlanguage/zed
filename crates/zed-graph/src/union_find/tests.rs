use super::{OffsetUnionFind, UnionFind};
use crate::seed::Rng;

/// How each union of the random tests links.
#[derive(Clone, Copy, Debug)]
enum Rule {
    Rank,
    Into,
    Least,
}

/// Runs random unions on `UnionFind` and on a plain labeling (each element's class label,
/// relabeled in full on each union), checking classes and each rule's root; returns
/// the unions that joined two classes and those that found one.
fn agree(rng: &mut Rng) -> (usize, usize) {
    let n = 1 + rng.below(24);
    let mut uf = UnionFind::new(n);
    let mut label: Vec<usize> = (0..n).collect();
    let (mut joined, mut same) = (0, 0);
    for _ in 0..rng.below(2 * n + 1) {
        let (a, b) = (rng.below(n), rng.below(n));
        let rule = rng.pick(&[Rule::Rank, Rule::Into, Rule::Least]);
        let was = label[a] == label[b];
        let (ra, rb) = (uf.find(a), uf.find(b));
        let did = match rule {
            Rule::Rank => uf.union(a, b),
            Rule::Into => uf.union_into(a, b),
            Rule::Least => uf.union_least(a, b),
        };
        assert_eq!(did, !was, "{rule:?} {a} {b}");
        if was {
            same += 1;
            continue;
        }
        joined += 1;
        let root = uf.find(a);
        match rule {
            Rule::Rank => assert!(root == ra || root == rb),
            Rule::Into => assert_eq!(root, ra, "union_into keeps the root of `keep`"),
            Rule::Least => assert_eq!(root, ra.min(rb)),
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
        for b in 0..n {
            assert_eq!(uf.same(a, b), label[a] == label[b], "{a} {b}");
        }
    }
    (joined, same)
}

#[test]
fn union_find_classes_match_a_plain_labeling() {
    // Built: both outcomes of a union, so the check can fail either way on every run.
    let mut uf = UnionFind::new(3);
    assert!(uf.union(0, 1));
    assert!(!uf.union(1, 0));
    assert!(uf.union_least(2, 1));
    assert_eq!(uf.find(2), 0);
    assert_eq!(uf.push(), 3);
    assert!(uf.union_into(3, 0));
    assert_eq!(uf.find(1), 3);
    let (mut rng, _) = Rng::fresh("union_find_classes_match_a_plain_labeling");
    let (mut joined, mut same) = (0, 0);
    for _ in 0..5000 {
        let (j, s) = agree(&mut rng);
        joined += j;
        same += s;
    }
    assert!(joined > 0 && same > 0, "{joined} {same}");
}

#[test]
fn offset_union_find_matches_plain_values() {
    // Built: a chain 0 <- 1 <- 2 with offsets 5 and -2, then a cycle that agrees and one that
    // does not.
    let mut uf: OffsetUnionFind<i64> = OffsetUnionFind::new(4);
    assert_eq!(uf.union_into(0, 1, &5), Ok(()));
    assert_eq!(uf.union_into(1, 2, &-2), Ok(()));
    assert_eq!(uf.find(2), (0, 3));
    assert_eq!(uf.union_into(0, 2, &3), Err(3));
    assert_eq!(uf.union_into(0, 2, &4), Err(3));
    assert_eq!(uf.find(3), (3, 0));
    // Random: values drawn first, each record true of them, so every find must give
    // `x_v - x_root` of the drawn values, and each record inside a class the true difference.
    let (mut rng, _) = Rng::fresh("offset_union_find_matches_plain_values");
    for _ in 0..5000 {
        let n = 1 + rng.below(24);
        let x: Vec<i64> = (0..n).map(|_| rng.int(-20, 20)).collect();
        let mut uf: OffsetUnionFind<i64> = OffsetUnionFind::new(n);
        let mut label: Vec<usize> = (0..n).collect();
        for _ in 0..rng.below(2 * n + 1) {
            let (a, b) = (rng.below(n), rng.below(n));
            let rb = uf.find(b).0;
            match uf.union_into(b, a, &(x[a] - x[b])) {
                Ok(()) => {
                    assert_ne!(label[a], label[b]);
                    assert_eq!(uf.find(a).0, rb, "the root of `b` stays");
                    let (from, to) = (label[a], label[b]);
                    for l in &mut label {
                        if *l == from {
                            *l = to;
                        }
                    }
                }
                Err(d) => {
                    assert_eq!(label[a], label[b]);
                    assert_eq!(d, x[a] - x[b]);
                }
            }
            for v in 0..n {
                let (r, o) = uf.find(v);
                assert_eq!(o, x[v] - x[r], "element {v}");
            }
        }
    }
}

/// The benchmarks of the union-find, run by `tools/run_tests.sh --bench`.
mod bench {
    use std::collections::BTreeMap;

    use super::{Rng, UnionFind};
    use crate::scaling;

    /// `n` elements and `n` unions of random pairs, then a find of each: O(n α(n)), the bound
    /// of Tarjan and van Leeuwen 1984 (JACM 31(2), doi:10.1145/62.2160); the full comment is
    /// at the head of `union_find.rs`.
    fn churn(n: usize, pairs: &[(usize, usize)]) -> usize {
        let mut uf = UnionFind::new(n);
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
    /// rule-less link), then a find of each: path halving keeps it O(n log n).
    #[test]
    fn union_into_a_chain_takes_n_log_n_time() {
        // As in `union_find_takes_near_linear_time`.
        let n = 200_000;
        scaling::check("n chained union_into then n finds", n, |m| {
            let mut uf = UnionFind::new(m);
            for v in 1..m {
                uf.union_into(v, v - 1);
            }
            assert_eq!((0..m).filter(|&v| uf.find(v) == v).count(), 1);
        });
    }
}
