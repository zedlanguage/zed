use super::*;
use crate::seed::Rng;
use std::collections::BTreeMap;

impl Hole for u64 {
    fn hole() -> Self {
        0
    }
}

pub(super) type M = Map<u64, u64>;

/// Checks the shape of `node`, `root` when it is the root, and appends its entries to `out`.
/// Returns its height.
fn shape(node: &Node<u64, u64>, root: bool, out: &mut Vec<(u64, u64)>) -> usize {
    let n = node.len();
    assert!(n <= MAX, "a node of {n} entries");
    assert!(
        if root { n >= 1 } else { n >= MIN },
        "a {} node of {n} entries",
        if root { "root" } else { "non-root" }
    );
    match node {
        Node::Leaf(s) => {
            out.extend(s.iter().copied());
            0
        }
        Node::Inner(bs) => {
            let mut height = None;
            for (j, b) in bs.iter().enumerate() {
                let h = shape(&b.child, false, out);
                assert_eq!(*height.get_or_insert(h), h, "leaves at different depths");
                assert_eq!(
                    b.next.is_some(),
                    j + 1 < bs.len(),
                    "an entry after branch {j}"
                );
                out.extend(b.next);
            }
            height.expect("an inner node has children") + 1
        }
    }
}

/// Checks the shape of `m` and that it holds exactly the entries of `model`, by every reader.
fn agrees(m: &M, model: &BTreeMap<u64, u64>) {
    let mut all = Vec::new();
    if let Some(root) = &m.root {
        shape(root, true, &mut all);
    }
    let want: Vec<(u64, u64)> = model.iter().map(|(&k, &v)| (k, v)).collect();
    assert_eq!(all, want, "the entries in node order");
    assert_eq!(m.len(), model.len());
    assert_eq!(m.is_empty(), model.is_empty());
    let it = m.iter();
    assert_eq!(it.len(), model.len());
    assert_eq!(it.map(|(&k, &v)| (k, v)).collect::<Vec<_>>(), want);
    let mut back: Vec<(u64, u64)> = m.iter().rev().map(|(&k, &v)| (k, v)).collect();
    back.reverse();
    assert_eq!(back, want, "the entries read backward");
    // Both ends at once, meeting in the middle.
    let mut it = m.iter();
    let (mut front, mut rear) = (Vec::new(), Vec::new());
    while let Some((&k, &v)) = it.next() {
        front.push((k, v));
        match it.next_back() {
            Some((&k, &v)) => rear.push((k, v)),
            None => break,
        }
    }
    assert!(it.next().is_none() && it.next_back().is_none());
    front.extend(rear.into_iter().rev());
    assert_eq!(front, want, "the entries read from both ends");
    assert_eq!(
        m.keys().copied().collect::<Vec<_>>(),
        model.keys().copied().collect::<Vec<_>>()
    );
    assert_eq!(
        m.values().copied().collect::<Vec<_>>(),
        model.values().copied().collect::<Vec<_>>()
    );
    assert_eq!(
        m.get_min().copied(),
        model.first_key_value().map(|(&k, &v)| (k, v))
    );
    assert_eq!(
        m.get_max().copied(),
        model.last_key_value().map(|(&k, &v)| (k, v))
    );
    beside_agrees(m, model, model.keys().copied());
    for (&k, &v) in model {
        assert_eq!(m.get(&k), Some(&v));
    }
}

/// `beside` at each key of `at`, held or not, agrees with the model's range search.
fn beside_agrees(m: &M, model: &BTreeMap<u64, u64>, at: impl Iterator<Item = u64>) {
    for k in at {
        let after = model.range(k + 1..).next().map(|(&k, &v)| (k, v));
        let before = model.range(..k).next_back().map(|(&k, &v)| (k, v));
        assert_eq!(m.beside(&k, true).copied(), after, "the entry after {k}");
        assert_eq!(m.beside(&k, false).copied(), before, "the entry before {k}");
    }
}

/// A change as the key, the old value and the new value.
type Change = (u64, Option<u64>, Option<u64>);

/// The change `d` stands for, checking that an update keeps its key.
fn change(d: DiffItem<'_, '_, u64, u64>) -> Change {
    match d {
        DiffItem::Add(&k, &w) => (k, None, Some(w)),
        DiffItem::Remove(&k, &v) => (k, Some(v), None),
        DiffItem::Update {
            old: (&k, &v),
            new: (&l, &w),
        } => {
            assert_eq!(k, l, "an update is of one key");
            (k, Some(v), Some(w))
        }
    }
}

/// The changes from `a` to `b` as the model gives them.
fn model_diff(a: &BTreeMap<u64, u64>, b: &BTreeMap<u64, u64>) -> Vec<Change> {
    let keys: std::collections::BTreeSet<u64> = a.keys().chain(b.keys()).copied().collect();
    keys.into_iter()
        .map(|k| (k, a.get(&k).copied(), b.get(&k).copied()))
        .filter(|(_, v, w)| v != w)
        .collect()
}

/// Checks `a.diff(b)` against the model, and that `zip` with and without passing over shared
/// subtrees gives the pairs a positional walk gives, less only pairs of one entry with itself.
fn compare(a: &M, b: &M, ma: &BTreeMap<u64, u64>, mb: &BTreeMap<u64, u64>) {
    let got: Vec<Change> = a.diff(b).map(change).collect();
    assert_eq!(
        got,
        model_diff(ma, mb),
        "the changes from one map to the other"
    );
    let pairs = |skip: bool| {
        let mut z = a.zip(b);
        let mut out = Vec::new();
        loop {
            match z.next(skip) {
                (None, None) => return out,
                (x, y) => out.push((x.copied(), y.copied())),
            }
        }
    };
    let positional: Vec<_> = {
        let (mut x, mut y) = (ma.iter(), mb.iter());
        let mut out = Vec::new();
        loop {
            match (x.next(), y.next()) {
                (None, None) => break out,
                (p, q) => out.push((p.map(|(&k, &v)| (k, v)), q.map(|(&k, &v)| (k, v)))),
            }
        }
    };
    assert_eq!(
        pairs(false),
        positional,
        "the pairs of a walk that reads every entry"
    );
    let mut rest = positional.iter();
    for p in pairs(true) {
        assert!(
            rest.by_ref().any(|q| *q == p),
            "a walk passing over shared subtrees gives the pairs in order"
        );
    }
}

#[test]
fn an_empty_map() {
    let mut m = M::default();
    agrees(&m, &BTreeMap::new());
    assert!(m.get(&3).is_none());
    assert!(!m.remove(&3));
    assert!(m.ptr_eq(&M::default()));
    assert_eq!(m.diff(&M::default()).count(), 0);
    assert_eq!(m.zip(&M::default()).next(false), (None, None));
    let one: M = [(1, 2)].into_iter().collect();
    compare(&m, &one, &BTreeMap::new(), &BTreeMap::from([(1, 2)]));
    compare(&one, &m, &BTreeMap::from([(1, 2)]), &BTreeMap::new());
    let built: M = Vec::new().into_iter().collect();
    assert!(built.root.is_none());
}

#[test]
fn one_entry_and_removal_down_to_empty() {
    let mut m = M::default();
    assert!(m.insert(5, 50));
    assert!(!m.insert(5, 51), "the key is not new");
    agrees(&m, &BTreeMap::from([(5, 51)]));
    let Some(Node::Leaf(s)) = &m.root else {
        panic!("one entry is one leaf");
    };
    assert_eq!(s.len(), 1, "a node of one entry is allocated at one");
    assert!(!m.remove(&4));
    assert!(m.remove(&5));
    assert!(m.root.is_none(), "an emptied map holds no node");
    agrees(&m, &BTreeMap::new());
}

#[test]
fn every_size_across_the_split_boundaries() {
    // Insertion in increasing, decreasing and mixed order up to three levels, removal of all of
    // them in each order, with a copy kept at every size to show it unchanged.
    let n = (MAX + 1) * (MAX + 1) + 2 * MAX;
    let orders: [Vec<u64>; 3] = [
        (0..n as u64).collect(),
        (0..n as u64).rev().collect(),
        (0..n as u64).map(|i| (i * 7919) % n as u64).collect(),
    ];
    for order in &orders {
        let mut m = M::default();
        let mut model = BTreeMap::new();
        let mut kept = Vec::new();
        for &k in order {
            kept.push((m.clone(), model.clone()));
            assert!(m.insert(k, k * 10));
            model.insert(k, k * 10);
            agrees(&m, &model);
        }
        for removal in &orders {
            let mut r = m.clone();
            let mut rm = model.clone();
            for &k in removal {
                assert!(r.remove(&k));
                rm.remove(&k);
                agrees(&r, &rm);
            }
            assert!(r.root.is_none());
        }
        for (m, model) in &kept {
            agrees(m, model);
        }
        agrees(&m, &model);
    }
}

#[test]
fn a_built_map_has_every_node_in_bounds() {
    // Every size up to past two levels, and the sizes around the next.
    let edge = (MAX + 1) * (MAX + 1);
    let sizes =
        (0..edge + 40).chain([edge * (MAX + 1) - 1, edge * (MAX + 1), edge * (MAX + 1) + 1]);
    for n in sizes {
        let model: BTreeMap<u64, u64> = (0..n as u64).map(|k| (k, k + 1)).collect();
        let m: M = (0..n as u64).map(|k| (k, k + 1)).collect();
        agrees(&m, &model);
    }
}

#[test]
fn a_build_keeps_the_last_of_equal_keys() {
    let m: M = [(3, 1), (1, 1), (3, 2), (2, 9), (3, 3), (1, 4)]
        .into_iter()
        .collect();
    agrees(&m, &BTreeMap::from([(1, 4), (2, 9), (3, 3)]));
}

#[test]
fn random_changes_agree_with_the_model_and_keep_old_versions() {
    let base = crate::seed::seed("random_changes_agree_with_the_model_and_keep_old_versions");
    for i in 0..6u64 {
        let mut d = Rng::new(base.wrapping_add(i));
        // Small domains make removals and replacements common, large ones deep trees.
        let domain = [20, 300, 3000][i as usize % 3];
        let mut versions: Vec<(M, BTreeMap<u64, u64>)> = vec![(M::default(), BTreeMap::new())];
        for step in 0..800 {
            let from = d.below(versions.len());
            let (mut m, mut model) = versions[from].clone();
            for _ in 0..1 + d.below(8) {
                let k = d.below_u64(domain);
                if d.below(3) == 0 {
                    assert_eq!(m.remove(&k), model.remove(&k).is_some());
                } else {
                    let v = d.next_u64();
                    assert_eq!(m.insert(k, v), model.insert(k, v).is_none());
                }
            }
            agrees(&m, &model);
            let (base, base_model) = &versions[from];
            compare(base, &m, base_model, &model);
            compare(&m, base, &model, base_model);
            if versions.len() < 12 {
                versions.push((m, model));
            } else {
                versions[step % 12] = (m, model);
            }
            if step % 100 == 0 {
                for (m, model) in &versions {
                    agrees(m, model);
                }
            }
        }
        for (m, model) in &versions {
            agrees(m, model);
        }
    }
}

#[test]
fn shared_subtrees_are_passed_over() {
    let n = 10_000u64;
    let a: M = (0..n).map(|k| (k, k)).collect();
    let mut b = a.clone();
    assert!(a.ptr_eq(&b));
    assert_eq!(a.zip(&b).next(true), (None, None), "one tree is not walked");
    // Without passing over, one tree is read in full, since a comparison such as the surface
    // equality of floats need not hold an entry equal to itself.
    for m in [&a, &(0..5).map(|k| (k, k)).collect::<M>()] {
        let mut z = m.zip(m);
        let mut all = Vec::new();
        loop {
            match z.next(false) {
                (None, None) => break,
                (x, y) => all.push((x.copied(), y.copied())),
            }
        }
        let every: Vec<_> = m
            .iter()
            .map(|(&k, &v)| (Some((k, v)), Some((k, v))))
            .collect();
        assert_eq!(all, every, "the pairs of one tree with itself");
    }
    assert_eq!(a.diff(&b).count(), 0);
    b.insert(n / 2, 0);
    assert!(!a.ptr_eq(&b));
    let changes: Vec<_> = a.diff(&b).collect();
    assert_eq!(
        changes,
        [DiffItem::Update {
            old: (&(n / 2), &(n / 2)),
            new: (&(n / 2), &0)
        }]
    );
    // Only the nodes on the changed path differ: at most MAX + 1 branches each of MAX entries
    // per level are read, against n.
    let mut z = a.zip(&b);
    let mut read = 0;
    while z.next(true) != (None, None) {
        read += 1;
    }
    let height = a.root.as_ref().map_or(0, Node::height) as u64;
    assert!(
        read <= (height + 1) * (MAX as u64 + 1),
        "{read} pairs read for one change"
    );
    // Without passing over, every pair is read.
    let mut z = a.zip(&b);
    let mut all = 0;
    while z.next(false) != (None, None) {
        all += 1;
    }
    assert_eq!(all, n);
    // A key added in the middle shifts the positions: the zip of positions shares nothing past
    // it, but the difference still reads only the changed path.
    let mut c = a.clone();
    c.insert(n + 1, 1);
    c.remove(&3);
    let mc: BTreeMap<u64, u64> = c.iter().map(|(&k, &v)| (k, v)).collect();
    let ma: BTreeMap<u64, u64> = a.iter().map(|(&k, &v)| (k, v)).collect();
    compare(&a, &c, &ma, &mc);
}

#[test]
fn the_entries_beside_a_key_held_or_not() {
    // Even keys only, so every odd key falls between two entries, at every size up to past
    // two levels; keys below the least and above the greatest have no entry on that side.
    let edge = (MAX + 1) * (MAX + 1);
    for n in (0..edge + 40).chain([edge * (MAX + 1) - 1, edge * (MAX + 1)]) {
        let model: BTreeMap<u64, u64> = (1..=n as u64).map(|k| (2 * k, k)).collect();
        let m: M = model.iter().map(|(&k, &v)| (k, v)).collect();
        beside_agrees(&m, &model, 0..2 * n as u64 + 3);
    }
}

/// The term of an entry for the sums of these tests, below the modulus.
fn term(k: &u64, v: &u64) -> u64 {
    (k.wrapping_mul(0x9e37_79b9) ^ v.wrapping_mul(0x85eb_ca6b)) % SUM_MODULUS
}

/// The sum read again from every entry, keeping nothing.
fn fresh_sum(m: &M) -> u64 {
    m.iter().fold(0, |acc, (k, v)| add(acc, term(k, v)))
}

/// The sum of `m` and the number of entries it read.
fn counted_sum(m: &M) -> (u64, usize) {
    let mut reads = 0;
    let s = m.sum(&mut |k, v| {
        reads += 1;
        term(k, v)
    });
    (s, reads)
}

/// Random inserts and removals on a map whose sums were all filled before each change, in
/// place (`shared` false) or on a copy that another holder keeps (`shared` true): after each
/// change the kept sums give the sum of the entries, and so does the copy kept from before.
/// Returns how often each arm of the changes ran (`Arm`).
fn changes_after_sums(seed: u64, shared: bool) -> [u32; 10] {
    ARMS.with(|a| a.set([0; 10]));
    let mut draw = Rng::new(seed);
    let mut m = M::default();
    // Grow, then shrink, so nodes merge and borrow; then remove every key left, so the root
    // collapses through each height.
    let mut changes: Vec<(bool, u64)> = (0..6000_u64)
        .map(|step| {
            (
                draw.below(5) < if step < 3000 { 4 } else { 1 },
                draw.below_u64(1500),
            )
        })
        .collect();
    for (step, &(insert, k)) in changes.iter().enumerate() {
        change_once(&mut m, shared, insert, k, step as u64, seed);
    }
    changes = m.keys().map(|&k| (false, k)).collect();
    for (step, &(insert, k)) in changes.iter().enumerate() {
        change_once(&mut m, shared, insert, k, step as u64, seed);
    }
    ARMS.with(|a| a.get())
}

/// The one key test of these tests' calls of [`Map::all_keys`]: the key is not 700. Keys are
/// drawn below 1500, so the answer turns as 700 goes in and out of the map.
fn plain(k: &u64) -> bool {
    *k != 700
}

/// [`Map::all_keys`] of `m` by [`plain`] and the number of keys it tested.
fn counted_all_keys(m: &M) -> (bool, usize) {
    let tested = std::cell::Cell::new(0);
    let all = m.all_keys(&|k| {
        tested.set(tested.get() + 1);
        plain(k)
    });
    (all, tested.get())
}

/// One change to `m`, with its sums and key answers filled before and checked after, on the map
/// and on the copy kept from before when `shared`.
fn change_once(m: &mut M, shared: bool, insert: bool, k: u64, step: u64, seed: u64) {
    assert_eq!(m.sum(&mut term), fresh_sum(m), "seed {seed} step {step}");
    assert_eq!(
        m.all_keys(&plain),
        m.keys().all(plain),
        "seed {seed} step {step}"
    );
    let kept = shared.then(|| m.clone());
    match insert {
        true => m.insert(k, step),
        false => m.remove(&k),
    };
    // The entries `for_each_unsummed` lists are those the sum reads, and after it none.
    let mut listed = 0;
    m.for_each_unsummed(&mut |_, _| listed += 1);
    assert_eq!(
        counted_sum(m),
        (fresh_sum(m), listed),
        "seed {seed} step {step}"
    );
    assert_eq!(counted_sum(m), (fresh_sum(m), 0), "seed {seed} step {step}");
    // The key answer after the change is a fresh scan's; a second call at an inner root tests
    // no key, as a kept answer stops it either at its end or at the branch that failed.
    let fresh = m.keys().all(plain);
    assert_eq!(counted_all_keys(m).0, fresh, "seed {seed} step {step}");
    let inner = matches!(m.root, Some(Node::Inner(_)));
    let again = counted_all_keys(m);
    assert_eq!(
        (again.0, again.1 == 0 || !inner),
        (fresh, true),
        "seed {seed} step {step}"
    );
    if let Some(kept) = kept {
        assert_eq!(
            kept.sum(&mut term),
            fresh_sum(&kept),
            "seed {seed} step {step}"
        );
        assert_eq!(
            kept.all_keys(&plain),
            kept.keys().all(plain),
            "seed {seed} step {step}"
        );
    }
}

/// An inner root's kept key answers: the first call tests every key, a second none, whether all
/// pass or one fails; a change tests only the keys on its path again, and a copy kept from
/// before the change keeps its own answer.
#[test]
fn an_unchanged_inner_root_tests_no_key() {
    // Every key but 700, which `plain` refuses.
    let n = 5000_u64;
    let mut m: M = (0..n).filter(|&k| k != 700).map(|k| (k, k)).collect();
    assert_eq!(counted_all_keys(&m), (true, n as usize - 1));
    assert_eq!(counted_all_keys(&m), (true, 0));
    let copy = m.clone();
    // A change, here a value replaced and then a key taken out, clears the answers on its path
    // only: the next call tests at most the keys of the nodes there and of the siblings a mend
    // rebuilt, 2 (MAX + 1) a level.
    let height = m.root.as_ref().map_or(0, Node::height);
    for change in [true, false] {
        match change {
            true => m.insert(1234, 1),
            false => m.remove(&1234),
        };
        let (all, tested) = counted_all_keys(&m);
        let bound = 2 * (MAX + 1) * (height + 1);
        assert!(all && tested > 0 && tested <= bound, "{tested} keys tested");
    }
    m.insert(700, 1);
    let (all, tested) = counted_all_keys(&m);
    assert!(!all && tested > 0 && tested <= n as usize);
    assert_eq!(
        counted_all_keys(&m),
        (false, 0),
        "the failed branch's answer is kept"
    );
    assert_eq!(
        counted_all_keys(&copy),
        (true, 0),
        "the copy keeps its answer"
    );
    assert!(M::default().all_keys(&plain));
}

/// A branch of families' entries is 152 bytes: 144 before it kept its key answer
/// (`Branch::keys`), the cost `Map::all_keys` states.
#[test]
fn a_branch_of_values_is_152_bytes() {
    use crate::value::Value;
    assert_eq!(size_of::<Branch<Value, Value>>(), 152);
}

/// A map held in one leaf keeps its sum: a second sum, and a copy's, read no entry, and no entry
/// is left unsummed; a change clears it, and the next sum is right. Before the leaf root kept
/// its sum each sum read every entry again, which made building nested families quadratic
/// (`Map::word`, FAIL-bench-main-f215d9c90).
#[test]
fn a_leaf_root_keeps_its_sum() {
    let mut m: M = (0..MAX as u64).map(|k| (k, k + 1)).collect();
    let mut reads = 0;
    let mut counted = |k: &u64, v: &u64| {
        reads += 1;
        term(k, v)
    };
    assert_eq!(m.sum(&mut counted), fresh_sum(&m));
    assert_eq!(reads, MAX);
    let copy = m.clone();
    for map in [&m, &copy] {
        reads = 0;
        let mut counted = |k: &u64, v: &u64| {
            reads += 1;
            term(k, v)
        };
        assert_eq!(map.sum(&mut counted), fresh_sum(&m));
        assert_eq!(reads, 0, "a kept sum reads no entry");
        let mut unsummed = 0;
        map.for_each_unsummed(&mut |_, _| unsummed += 1);
        assert_eq!(unsummed, 0);
    }
    // A value replaced, an entry added, one taken out: each clears the kept sum.
    m.insert(3, 100);
    assert_eq!(m.sum(&mut term), fresh_sum(&m));
    m.insert(MAX as u64, 7);
    assert_eq!(m.sum(&mut term), fresh_sum(&m));
    m.remove(&0);
    assert_eq!(m.sum(&mut term), fresh_sum(&m));
    // The copy kept from before the changes keeps its own sum.
    assert_eq!(copy.sum(&mut term), fresh_sum(&copy));
}

/// A map of MAX + 1 entries built at once has an inner root of two leaves of MIN, with the
/// ninth entry between them: the shape `value::tests::nested_record` and the bench
/// `hashing_records_nested_at_an_inner_roots_separator_scales` rely on.
#[test]
fn seventeen_entries_split_at_the_ninth() {
    let m: M = (0..=MAX as u64).map(|k| (k, k)).collect();
    let Some(Node::Inner(bs)) = &m.root else {
        panic!("17 entries need an inner root");
    };
    assert_eq!(bs.len(), 2);
    assert_eq!(bs[0].next, Some((MIN as u64, MIN as u64)));
    assert!(bs.iter().all(|b| b.child.len() == MIN));
}

/// A map whose root is an inner node keeps the sum of its separators too: after a sum, a second
/// sum and a copy's read no entry, and no entry is left unsummed, at heights 1 and 2. Then each
/// way a separator changes, its value replaced, or taken out so that a mend moves an entry up,
/// clears what covered it, and the next sum is right and reads only the changed paths. Before
/// (BTREE-inner-root-sum) each sum read the root's separators again.
#[test]
fn an_inner_root_keeps_its_sum() {
    for len in [MAX as u64 + 1, 40, 2000] {
        let mut m: M = (0..len).map(|k| (k, k + 1)).collect();
        assert!(matches!(m.root, Some(Node::Inner(_))), "{len}");
        assert_eq!(counted_sum(&m), (fresh_sum(&m), len as usize), "{len}");
        let copy = m.clone();
        for map in [&m, &copy] {
            assert_eq!(
                counted_sum(map),
                (fresh_sum(&m), 0),
                "{len}: a kept sum reads none"
            );
            let mut unsummed = 0;
            map.for_each_unsummed(&mut |_, _| unsummed += 1);
            assert_eq!(unsummed, 0, "{len}");
        }
        let separators: Vec<u64> = match &m.root {
            Some(Node::Inner(bs)) => bs.iter().filter_map(|b| b.next.map(|(k, _)| k)).collect(),
            _ => unreachable!("checked above"),
        };
        for &k in &separators {
            // A separator's value replaced in place (`insert_in`, `Ok(i)` of an inner node).
            m.insert(k, 7 * k);
            let (s, reads) = counted_sum(&m);
            assert_eq!(s, fresh_sum(&m), "{len}: {k} replaced");
            assert!(reads <= MAX + 1, "{len}: {k} replaced read {reads}");
            assert_eq!(counted_sum(&m), (s, 0), "{len}");
            // The separator taken out: the entry before it moves up from a leaf.
            m.remove(&k);
            assert_eq!(counted_sum(&m).0, fresh_sum(&m), "{len}: {k} removed");
            assert_eq!(counted_sum(&m), (fresh_sum(&m), 0), "{len}");
        }
        // The copy kept from before the changes keeps its own sum.
        assert_eq!(counted_sum(&copy), (fresh_sum(&copy), 0), "{len}");
    }
}

/// Every arm that moves entries or subtrees between nodes runs with the sums filled, in place
/// and on a copy, and the kept sums stay right through each (plan row
/// PERF-family-hash-count-only). Controls (not committed), each failing this test and
/// `value::tests::kept_sums_follow_changes`: `mend` without `r.child_mut()`, so a sibling that
/// gains or loses a subtree keeps its old sum; and `Branch::with_next` keeping the sum it
/// carries, so a subtree moved with a new entry after it arrives with a sum of the old one.
/// Each change also checks that the sum reads the entries `for_each_unsummed` lists, and that
/// a second sum reads none (`change_once`, BTREE-inner-root-sum).
#[test]
fn kept_sums_survive_every_arm_of_a_change() {
    let names = [
        "leaf from right",
        "leaf from left",
        "leaf merge",
        "inner from right",
        "inner from left",
        "inner merge",
        "root collapse",
        "root split",
        "mend in place",
        "mend on a copy",
    ];
    let mut total = [0_u32; 10];
    for (seed, shared) in [(1, false), (2, true), (3, false), (4, true)] {
        let arms = changes_after_sums(seed, shared);
        for (t, a) in total.iter_mut().zip(arms) {
            *t += a;
        }
    }
    for (name, count) in names.iter().zip(total) {
        eprintln!("{name}: {count}");
        assert!(count > 0, "the arm {name} was never reached");
    }
}
