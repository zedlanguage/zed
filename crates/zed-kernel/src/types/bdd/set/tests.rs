//! The depth of the sets' treaps on structured keys (PROOF-treap-digest-priorities,
//! PERF-xor-shape-free, COMPLEXITY.md K123). A node's priority is the run's random polynomial at
//! its literal's digest ([`priority`]), so the bound holds for every input whose literals are
//! distinct points, and literals at one point add their number (module [`crate::priority`];
//! a program can write many, PERF-set-tied-digest-depth); the unit tests run one fixed draw (seed 0 unless `ZED_TREAP_SEED` is
//! set). These tests check keys built the way programs build them (consecutive numbers, names,
//! rows that share a prefix or a suffix, digests that are consecutive numbers) and keys chosen
//! against the fixed hash the priority was before: each fails when Seidel and Aragon's bound puts
//! the probability of the measured height, for independent uniform priorities, below `1/n`.
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
//! distinct. So `D(x)` is at most `x`'s depth in that treap of at most `n` nodes, plus `T`. The
//! tests apply the bound to the height less the part of `T` the keys force: the literals whose
//! point (their `taken` and their digest modulo `2^64 - 59`) another literal shares, which tie
//! under every draw. Distinct points tie with probability `1/p` a pair; such ties are not taken
//! off, so a priority that ties distinct points (a constant, say) fails the tests.

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
    let sum = |d: fn(&Row) -> u64| (keys.iter()).fold(0, |s, k| summed(d(&k.0), k.1, s, 0));
    let sums = (sum(Atom::digest), sum(Atom::name_digest));
    // The literals that share their point with another: they tie under every draw.
    let mut points: crate::digest::DigestMap<(bool, u64), usize> = Default::default();
    for k in &keys {
        *points
            .entry((k.1, k.0.digest() % crate::priority::P))
            .or_default() += 1;
    }
    let forced: usize = points.values().filter(|&&k| k > 1).sum();
    let t = from_sorted(keys);
    assert_eq!(len(t.as_ref()), n);
    assert_eq!(
        (digest(t.as_ref()), name_digest(t.as_ref())),
        sums,
        "{family}"
    );
    let (height, tied) = shape(&t);
    assert!(
        tied >= forced,
        "{family}: {tied} tied, {forced} at shared points"
    );
    let ln_n = (n as f64).ln();
    let c = (height.saturating_sub(forced) as f64 - 1.0) / (2.0 * ln_n);
    let ln_bound = 2f64.ln() + ln_n - c * (c / std::f64::consts::E).ln() * (ln_n - 1.0);
    assert!(
        c <= std::f64::consts::E || ln_bound >= -ln_n,
        "{family}: {n} literals, height {height} nodes, {tied} in classes of equal priority, \
         {forced} at shared points: c = {c:.2}, and the model gives this height a probability \
         below e^{ln_bound:.1}, under 1/n"
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

/// A set's digests are sums over its literals, so two shapes of one set have one digest: built by
/// hand with each of three literals at the root.
#[test]
fn every_shape_of_a_set_has_its_digests() {
    let [a, b, c] = [0, 1, 2].map(|i| (Row::new(vec![int(i)]), i != 1));
    let one = |k: &Key<Row>| Some(make(k.clone(), None, None));
    let shapes = [
        make(a.clone(), None, Some(make(b.clone(), None, one(&c)))),
        make(b.clone(), one(&a), one(&c)),
        make(c.clone(), Some(make(a.clone(), None, one(&b))), None),
    ];
    let digests = shapes.each_ref().map(|s| (s.digest, s.name_digest));
    assert!(digests.iter().all(|&d| d == digests[0]), "{digests:?}");
    let sum = [&a, &b, &c]
        .iter()
        .fold(0, |s, k| summed(Atom::digest(&k.0), k.1, s, 0));
    assert_eq!(digests[0].0, sum);
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

/// [`symmetric`] gives the set, and on one thread the node, that adding or removing the smaller
/// set's literals one at a time gives: sets of 0 to 300 literals over atoms that overlap by a
/// part that goes from none to all, in both orders of the arguments.
#[test]
fn the_symmetric_difference_is_the_one_made_a_literal_at_a_time() {
    let set = |r: std::ops::Range<usize>| -> Tree<Row> {
        r.map(|i| (Row::new(vec![int(i)]), true))
            .fold(None, |t, k| Some(insert(t.as_ref(), k)))
    };
    let naive = |x: &Tree<Row>, y: &Tree<Row>| {
        let (big, small) = if len(x.as_ref()) >= len(y.as_ref()) {
            (x, y)
        } else {
            (y, x)
        };
        let mut out = big.clone();
        for k in iter(small.as_ref()) {
            out = match &out {
                Some(o) if get(Some(o), &k.0).is_some() => remove(o, k),
                _ => Some(insert(out.as_ref(), k.clone())),
            };
        }
        out
    };
    let mut cases = 0;
    for n in [0, 1, 2, 7, 64, 300] {
        for (a, b) in [(0, 0), (0, n), (n / 3, n), (n, 2 * n), (n / 2, n / 2 + 1)] {
            let (x, y) = (set(0..n), set(a..b));
            let want = naive(&x, &y);
            let expected: Vec<usize> = (0..n.min(a))
                .chain(n.max(a).min(b)..b)
                .chain(b.min(n).max(a)..n)
                .collect();
            for got in [symmetric(&x, &y), symmetric(&y, &x)] {
                assert_eq!(id(got.as_ref()), id(want.as_ref()), "{n}: {a}..{b}");
                let atoms: Vec<Row> = iter(got.as_ref()).map(|k| k.0.clone()).collect();
                let mut keys: Vec<Row> = expected.iter().map(|&i| Row::new(vec![int(i)])).collect();
                keys.sort();
                assert_eq!(atoms, keys, "{n}: {a}..{b}");
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 60);
}

/// Two distinct sets whose digests tie and whose shapes differ are ordered by their literals in
/// order (`Walk::SetRest`), as the sequences compare, whatever the draw. An atom of digest `e`
/// taken and one of digest `e ^ 1` not taken add the same hash to a sum ([`summed`]), so
/// `{p, q}` and `{p, q'}` tie; their priorities are the draw's, so `e` is searched for where the
/// two roots' left sides differ in size.
#[test]
fn sets_whose_digests_tie_and_shapes_differ_are_ordered_by_their_literals() {
    use super::super::{Literal, Walk};
    let p: Key<Row> = (forced(1 << 40, vec![int(0)]), true);
    let in_order = |t: &Tree<Row>| iter(t.as_ref()).cloned().collect::<Vec<_>>();
    let mut found = 0;
    for e in (2u64 << 40..).step_by(2).take(64) {
        let q = (forced(e, vec![int(1)]), true);
        let q2 = (forced(e ^ 1, vec![int(2)]), false);
        let s = from_sorted(vec![p.clone(), q]);
        let t = from_sorted(vec![p.clone(), q2]);
        let (x, y) = (s.as_ref().expect("two"), t.as_ref().expect("two"));
        assert_eq!((x.digest, x.name_digest), (y.digest, y.name_digest), "{e}");
        if len(x.left.as_ref()) == len(y.left.as_ref()) {
            continue;
        }
        found += 1;
        let expected = (in_order(&s).iter().map(|k| (k.1, &k.0)))
            .cmp(in_order(&t).iter().map(|k| (k.1, &k.0)));
        assert_ne!(expected, std::cmp::Ordering::Equal);
        assert_eq!(Row::order(Walk::Sets(Some(x), Some(y))), expected, "{e}");
        assert_eq!(
            Row::order(Walk::Sets(Some(y), Some(x))),
            expected.reverse(),
            "{e}"
        );
        assert_eq!(
            Row::order(Walk::Sets(Some(x), Some(x))),
            std::cmp::Ordering::Equal
        );
    }
    assert!(found > 0, "no digest of 64 gave two shapes");
}

/// Literals chosen by the fixed hash of a literal's digest that was the priority before the draw
/// (`mix(mix(13, digest), taken)`, which a program can compute): of the first 2^20 numbers,
/// those whose hashes rise in the order of the literals, by patience sorting in `O(N log N)`,
/// about `2 sqrt(N)` of them (Erdős and Szekeres; 2,030 here). Under that hash their set was a
/// path of 2,030 nodes; under the draw ([`priority`]) its height is logarithmic
/// (PERF-xor-shape-free).
/// `step(h, x)` of [`crate::digest::step`] solved for `x`: the finalizer's three xor-shifts and
/// two odd multiplications undone (each multiplication by its inverse modulo 2^64).
fn step_x(h: u64, out: u64) -> u64 {
    let inv = |m: u64| {
        (0..6).fold(m, |y, _| {
            y.wrapping_mul(2u64.wrapping_sub(m.wrapping_mul(y)))
        })
    };
    let unshift = |z: u64, s: u32| (1..=64 / s).fold(z, |y, k| y ^ (z >> (s * k)));
    let mut z = unshift(out, 31).wrapping_mul(inv(0x94d0_49bb_1331_11eb));
    z = unshift(z, 27).wrapping_mul(inv(0xbf58_476d_1ce4_e5b9));
    z = unshift(z, 30).wrapping_sub(0x9e37_79b9_7f4a_7c15);
    z ^ h.rotate_left(29)
}

/// `step(h, x)` solved for `h`.
fn step_h(x: u64, out: u64) -> u64 {
    (step_x(0, out) ^ x).rotate_right(29)
}

/// [`mix`] solved for its first or its second argument: `step` with this thread's salt.
fn mix_inv(a: Option<u64>, b: Option<u64>, out: u64) -> u64 {
    let out = out ^ crate::types::hash::SALT.with(std::cell::Cell::get);
    match (a, b) {
        (Some(a), None) => step_x(a, out),
        (None, Some(b)) => step_h(b, out),
        _ => unreachable!("one argument is given"),
    }
}

/// The integer whose literal type has digest `d`: [`Parts::hashes`] of `Type::empty()` with
/// one integer, and `scalar`, undone a step at a time.
fn int_of_digest(d: u64) -> i64 {
    let e = Type::empty();
    let p = e.p();
    assert!(p.tuples.lens.is_empty() && !p.f32s.cofinite && p.f32s.values.is_empty());
    let mut h = mix_inv(None, Some(p.morphisms.digest()), d);
    for b in [u64::from(p.structs), u64::from(p.tuples.rest), p.atoms.sum] {
        h = mix_inv(None, Some(b), h);
    }
    h = mix_inv(None, Some(u64::from(p.atoms.cofinite)), h);
    for l in [&p.strings, &p.floats, &p.rats] {
        h = mix_inv(None, Some(l.sum), h);
        h = mix_inv(None, Some(u64::from(l.cofinite)), h);
    }
    let before = mix(mix(0, u64::from(p.bools)), u64::from(p.ints.cofinite));
    mix_inv(Some(1), None, mix_inv(Some(before), None, h)) as i64
}

/// Distinct rows that a program can write, of one digest, so of one priority whatever the draw
/// (PERF-set-tied-digest-depth): rows `(a, b)` of two integers, `b` solved from `a` through the
/// steps of the hash, each of which is a bijection in either argument. Under short addresses a
/// digest has 8 bits, and the rows `(i)` that share the first one's digest are taken instead.
fn rows_of_one_digest(n: usize) -> Vec<Row> {
    if crate::address::SHORT {
        let target = Row::new(vec![int(0)]).digest();
        let rows = (0..).map(|i| Row::new(vec![int(i)]));
        return rows.filter(|r| r.digest() == target).take(n).collect();
    }
    let target = Row::new(vec![int(0), int(0)]).digest();
    (0..n)
        .map(|a| {
            let first = mix(5, int(a).digest());
            let b = int_of_digest(mix_inv(Some(first), None, target));
            Row::new(vec![int(a), Type::lit(&Value::Int(b)).expect("a literal")])
        })
        .collect()
}

/// A program can write `n` distinct rows of one digest, which tie whatever the draw: the bound of
/// the module comment of `set.rs` holds only with its term `T0` for them, here `n`, and the set is
/// a path. A bound free of the digests is PERF-set-tied-digest-depth.
#[test]
fn a_program_can_write_many_rows_of_one_digest() {
    let n = 4096;
    let rows = rows_of_one_digest(n);
    let distinct: std::collections::BTreeSet<&Row> = rows.iter().collect();
    assert_eq!(distinct.len(), n, "distinct rows");
    assert!(
        rows.iter().all(|r| r.digest() == rows[0].digest()),
        "one digest"
    );
    let (height, tied) = check("rows of one digest", rows, |_| true);
    assert_eq!((height, tied), (n, n));
}

/// Literals chosen against the fixed hash the priority was before, `mix(mix(13, digest),
/// taken)`: among the numbers below `2^16`, the longest run, in key order, whose old priorities
/// rise (about `2 sqrt(2^16)`, 512), which that hash made a path of over 400 nodes, far past
/// the bound (`c` above 30). The same choice among `2^20` numbers (about 2,000 literals)
/// is `bench::chosen_literals_among_a_million_numbers` (FAIL-unit-pieces-time: 6 s alone).
#[test]
fn chosen_literals_give_a_logarithmic_height() {
    chosen_literals(1 << 16, 400);
}

mod bench {
    /// [`super::chosen_literals_give_a_logarithmic_height`] among `2^20` numbers.
    #[test]
    fn chosen_literals_among_a_million_numbers() {
        super::chosen_literals(1 << 20, 1000);
    }
}

/// The literals among the numbers below `n` chosen against the old fixed hash (the longest
/// run whose old priorities rise, found by patience sorting in O(n log n)), at least `least` of
/// them, checked against the bound.
fn chosen_literals(n: usize, least: usize) {
    let mut keys: Vec<Key<Row>> = (0..n).map(|i| (Row::new(vec![int(i)]), true)).collect();
    keys.sort();
    let fixed = |k: &Key<Row>| mix(mix(13, Atom::digest(&k.0)), u64::from(k.1));
    let p: Vec<u64> = keys.iter().map(fixed).collect();
    let mut tails: Vec<usize> = Vec::new();
    let mut prev = vec![usize::MAX; p.len()];
    for i in 0..p.len() {
        let j = tails.partition_point(|&t| p[t] < p[i]);
        if j > 0 {
            prev[i] = tails[j - 1];
        }
        match j == tails.len() {
            true => tails.push(i),
            false => tails[j] = i,
        }
    }
    let mut pick = vec![*tails.last().expect("a number")];
    while let Some(&i) = pick.last()
        && prev[i] != usize::MAX
    {
        pick.push(prev[i]);
    }
    assert!(pick.len() > least, "{} literals chosen", pick.len());
    let atoms = pick.iter().map(|&i| keys[i].0.clone()).collect();
    check("chosen literals", atoms, |_| true);
}

/// `distinct_atoms` files the atoms it meets by digest and compares an atom only with those of
/// its digest, so on atoms that all share one digest its chains carry the whole answer. It must
/// keep every distinct atom once, in the order first met, as a sorted set of the atoms does; a
/// filing by digest alone (the control) keeps one. From cross-review XR-xor-shape-rounds-4-6,
/// round 4 (Codex).
#[test]
fn distinct_atoms_keeps_every_atom_of_one_digest() {
    use crate::types::bdd::{Op, Part};
    let n = 512;
    let rows = rows_of_one_digest(n);
    let parts: Vec<Part<Row>> = rows.iter().cloned().map(Part::literal).collect();
    let union = parts[1..]
        .iter()
        .fold(parts[0].clone(), |u, p| u.zip(p, Op::Or));
    let (mut seen, mut expected) = (std::collections::BTreeSet::new(), Vec::new());
    union.atoms(&mut |a| {
        if seen.insert(a.clone()) {
            expected.push(a.clone());
        }
        true
    });
    assert_eq!(expected.len(), n, "distinct rows met");
    assert_eq!(union.distinct_atoms(), expected);
    let mut digests = std::collections::BTreeSet::new();
    let mut by_digest = 0;
    union.atoms(&mut |a| {
        by_digest += usize::from(digests.insert(a.digest()));
        true
    });
    assert_eq!(
        by_digest, 1,
        "control: filed by digest alone, one row is kept"
    );
}

/// Rows compare by their digests first, so rows of one digest form one interval of the order
/// among rows of other digests: a treap's tied class is a contiguous range of its keys.
/// Morphisms compare by their guarantees first, so two morphisms of one digest can have one of
/// another digest between them: a remedy for tied priorities (PERF-set-tied-digest-depth) that
/// needs tied keys to be contiguous does not hold for every kind of atom. From cross-review
/// XR-xor-shape-rounds-4-6, round 4 (Gemini).
#[test]
fn rows_of_one_digest_are_contiguous_and_morphisms_need_not_be() {
    use crate::types::Morphism;
    let tied = rows_of_one_digest(32);
    let target = tied[0].digest();
    let apart = (1..=64).map(|a| Row::new(vec![int(a), int(a)]));
    let mut mixed: Vec<Row> = tied.iter().cloned().chain(apart).collect();
    mixed.sort();
    mixed.dedup();
    let at: Vec<usize> = (0..mixed.len())
        .filter(|&i| mixed[i].digest() == target)
        .collect();
    assert!(at.len() >= 32, "{} rows of the digest", at.len());
    assert_eq!(
        at[at.len() - 1] - at[0] + 1,
        at.len(),
        "rows of one digest are contiguous"
    );
    if crate::address::SHORT {
        return;
    }
    let mut gs = [int(10), int(20), int(30)];
    gs.sort();
    let m0 = Morphism::new(gs[0].clone(), int(0), int(0));
    let first = mix(mix(6, gs[2].digest()), int(0).digest());
    let v = int_of_digest(mix_inv(Some(first), None, m0.digest()));
    let m2 = Morphism::new(
        gs[2].clone(),
        int(0),
        Type::lit(&Value::Int(v)).expect("a literal"),
    );
    assert_eq!(m0.digest(), m2.digest(), "two morphisms of one digest");
    let m1 = Morphism::new(gs[1].clone(), int(0), int(0));
    assert_ne!(m1.digest(), m0.digest());
    assert!(
        m0 < m1 && m1 < m2,
        "a morphism of another digest lies between them"
    );
}
