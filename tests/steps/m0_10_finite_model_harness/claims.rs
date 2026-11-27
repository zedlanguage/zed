//! Plan row CLAIM-design-checks: the counted checks DESIGN.md states as done at design time,
//! run again. Each test recomputes the rule and its definition by enumeration, asserts the
//! counts the text gives, and prints them.
//!
//! - sec:type_language, "One rule for every join": the bounds `(L', U')` of a join from the region
//!   triple, against the tightest pair over every pair of domains within the operand bounds,
//!   for all 27 triples and all 729 pairs of operand bounds on a three-key universe.
//! - sec:property_tracking, Derived: the map rules over every map between sets of one to three
//!   elements, 3,222 instances.
//! - sec:property_tracking, "Changing a carrier": every binary table on one or two elements and
//!   every injective `encode` into one to four elements, 1,002 instances.
//! - sec:domains, "Interval transfer through reductions": the `+`-fold bound and the
//!   `min`/`max`-fold bound at literal ends, which the text said were "validated on randomized
//!   models" with no count; this test is the check it now cites.
//!
//! The text's "400,000 random expression trees" for the strict-tonicity rules was a run at
//! design time that no test repeats at that size; the text now cites the run that is in the
//! tests, `l01_25_preimage_catalog::strict::random_terms_against_running_them`.
//!
//! Each check is a few thousand instances on sets of at most four elements, well under a
//! millisecond each, so none has a benchmark: there is no size to scale.

/// A region of the triple: kept, dropped, or asserted empty (`#assertEmpty`).
#[derive(Clone, Copy, PartialEq, Debug)]
enum Region {
    Keep,
    Discard,
    Assert,
}
use Region::{Assert, Discard, Keep};

const KEYS: u32 = 3;
const ALL: u8 = (1 << KEYS) - 1;

/// The 27 bounds `(L, U)` with `L ⊆ U ⊆ {0, 1, 2}`: each key out, permitted, or guaranteed.
fn bounds() -> Vec<(u8, u8)> {
    let mut out = Vec::new();
    for code in 0..27u32 {
        let (mut l, mut u, mut c) = (0u8, 0u8, code);
        for k in 0..KEYS {
            match c % 3 {
                0 => {}
                1 => u |= 1 << k,
                _ => {
                    u |= 1 << k;
                    l |= 1 << k;
                }
            }
            c /= 3;
        }
        out.push((l, u));
    }
    out
}

/// Every domain `D` with `L ⊆ D ⊆ U`.
fn domains((l, u): (u8, u8)) -> impl Iterator<Item = u8> {
    (0..=ALL).filter(move |d| d & l == l && d & !u == 0)
}

/// The bounds by the rule of sec:grouping: `P_left = U_a \ L_b`, `P_both = U_a ∩ U_b`,
/// `P_right = U_b \ L_a`; `U'` the union of the kept `P_r`, `L'` is `L_a ∪ L_b` less every
/// dropped `P_r`.
fn by_rule(t: [Region; 3], (la, ua): (u8, u8), (lb, ub): (u8, u8)) -> (u8, u8) {
    let p = [ua & !lb, ua & ub, ub & !la];
    let mut u = 0;
    let mut l = la | lb;
    for (r, pr) in t.iter().zip(p) {
        match r {
            Keep => u |= pr,
            Discard => l &= !pr,
            Assert => {}
        }
    }
    (l & ALL, u & ALL)
}

/// The bounds by definition: over every pair of domains within the operand bounds that leaves
/// each asserted region empty, `U'` the union and `L'` the intersection of the joined domains;
/// `None` when no pair satisfies the assertions.
fn by_definition(t: [Region; 3], a: (u8, u8), b: (u8, u8)) -> Option<(u8, u8)> {
    let mut seen = None;
    for da in domains(a) {
        for db in domains(b) {
            let regions = [da & !db, da & db, db & !da];
            if t.iter().zip(regions).any(|(r, s)| *r == Assert && s != 0) {
                continue;
            }
            let joined = t
                .iter()
                .zip(regions)
                .filter(|(r, _)| **r == Keep)
                .fold(0, |acc, (_, s)| acc | s);
            seen = Some(match seen {
                None => (joined, joined),
                Some((l, u)) => (l & joined, u | joined),
            });
        }
    }
    seen
}

#[test]
fn the_join_rule_is_exact_on_every_triple_and_pair_of_bounds() {
    let regions = [Keep, Discard, Assert];
    let bounds = bounds();
    let (mut cases, mut unsatisfiable, mut agree) = (0, 0, 0);
    for &left in &regions {
        for &both in &regions {
            for &right in &regions {
                let t = [left, both, right];
                for &a in &bounds {
                    for &b in &bounds {
                        cases += 1;
                        let (l, u) = by_rule(t, a, b);
                        match by_definition(t, a, b) {
                            None => {
                                unsatisfiable += 1;
                                assert!(l & !u != 0, "{t:?} {a:?} {b:?}: L' ⊆ U' with no domains");
                            }
                            Some(want) => {
                                assert!(l & !u == 0, "{t:?} {a:?} {b:?}: L' ⊄ U'");
                                assert_eq!((l, u), want, "{t:?} {a:?} {b:?}");
                                agree += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    println!(
        "join rule: {cases} cases, {unsatisfiable} with no pair of domains, {agree} equal to the tightest bounds"
    );
    assert_eq!((cases, unsatisfiable, agree), (19_683, 6_093, 13_590));
}

/// Every map from `0..a` to `0..b`, as its table.
fn maps(a: usize, b: usize) -> Vec<Vec<usize>> {
    let mut out = vec![vec![]];
    for _ in 0..a {
        out = out
            .into_iter()
            .flat_map(|m| {
                (0..b).map(move |v| {
                    let mut m = m.clone();
                    m.push(v);
                    m
                })
            })
            .collect();
    }
    out
}

fn injective(f: &[usize]) -> bool {
    (0..f.len()).all(|i| (0..i).all(|j| f[i] != f[j]))
}

fn surjective(f: &[usize], b: usize) -> bool {
    (0..b).all(|v| f.contains(&v))
}

fn compose(g: &[usize], f: &[usize]) -> Vec<usize> {
    f.iter().map(|&x| g[x]).collect()
}

#[test]
fn the_map_rules_hold_on_every_map_between_sets_of_one_to_three_elements() {
    let sizes = 1..=3usize;
    let (mut composed, mut tupled, mut inverses, mut widened) = (0, 0, 0, 0);
    for a in sizes.clone() {
        for b in sizes.clone() {
            for f in maps(a, b) {
                // A two-sided inverse witnesses bijectivity, and only a bijection has one.
                inverses += 1;
                let has_inverse = maps(b, a).iter().any(|g| {
                    compose(g, &f) == (0..a).collect::<Vec<_>>()
                        && compose(&f, g) == (0..b).collect::<Vec<_>>()
                });
                assert_eq!(has_inverse, injective(&f) && surjective(&f, b), "{f:?}");
                // Widening the codomain to `0..w` preserves injectivity.
                for w in b + 1..=3 {
                    widened += 1;
                    let inclusion: Vec<usize> = (0..b).collect();
                    let wide = compose(&inclusion, &f);
                    assert!(wide.iter().all(|&v| v < w), "{f:?} into 0..{w}");
                    if injective(&f) {
                        assert!(injective(&wide), "{f:?} into 0..{w}");
                    }
                }
                for c in sizes.clone() {
                    // Composition and the two cancellation rules, `g ∘ f` for `g: b -> c`.
                    for g in maps(b, c) {
                        composed += 1;
                        let gf = compose(&g, &f);
                        if injective(&f) && injective(&g) {
                            assert!(injective(&gf), "{g:?} ∘ {f:?}");
                        }
                        if surjective(&f, b) && surjective(&g, c) {
                            assert!(surjective(&gf, c), "{g:?} ∘ {f:?}");
                        }
                        if injective(&gf) {
                            assert!(injective(&f), "{g:?} ∘ {f:?}");
                        }
                        if surjective(&gf, c) {
                            assert!(surjective(&g, c), "{g:?} ∘ {f:?}");
                        }
                    }
                    // The tuple `k ↦ (f(k), g(k))` for `g: a -> c`.
                    for g in maps(a, c) {
                        tupled += 1;
                        let pair: Vec<usize> = (0..a).map(|k| f[k] * c + g[k]).collect();
                        if injective(&f) || injective(&g) {
                            assert!(injective(&pair), "({f:?}, {g:?})");
                        }
                    }
                }
            }
        }
    }
    let all = composed + tupled + inverses + widened;
    println!(
        "map rules: {all} instances ({composed} composable pairs, {tupled} tuples, {inverses} maps for the inverse rule, {widened} widenings), no violation"
    );
    assert_eq!(
        (composed, tupled, inverses, widened, all),
        (1_618, 1_528, 56, 20, 3_222)
    );
}

/// A binary operation on `0..n` as its table, `t[x * n + y]`.
struct Op<'t> {
    n: usize,
    t: &'t [usize],
}

impl Op<'_> {
    fn at(&self, x: usize, y: usize) -> usize {
        self.t[x * self.n + y]
    }
    fn associative(&self) -> bool {
        let n = self.n;
        (0..n).all(|x| {
            (0..n).all(|y| (0..n).all(|z| self.at(self.at(x, y), z) == self.at(x, self.at(y, z))))
        })
    }
    fn commutative(&self) -> bool {
        (0..self.n).all(|x| (0..self.n).all(|y| self.at(x, y) == self.at(y, x)))
    }
    fn idempotent(&self) -> bool {
        (0..self.n).all(|x| self.at(x, x) == x)
    }
    fn zero(&self, z: usize) -> bool {
        (0..self.n).all(|y| self.at(z, y) == z && self.at(y, z) == z)
    }
    fn identity(&self, e: usize) -> bool {
        (0..self.n).all(|y| self.at(e, y) == y && self.at(y, e) == y)
    }
}

#[test]
fn changing_a_carrier_keeps_each_property_with_the_equations_it_needs() {
    let (mut instances, mut idempotence_fails, mut identity_fails, mut either_fails) =
        (0, 0, 0, 0);
    for n in 1..=2usize {
        for t in maps(n * n, n) {
            let op = Op { n, t: &t };
            for m in 1..=4usize {
                for encode in maps(n, m).into_iter().filter(|e| injective(e)) {
                    // `decode` is defined on the whole carrier, with `decode(encode(a)) == a`.
                    for decode in maps(m, n) {
                        if (0..n).any(|a| decode[encode[a]] != a) {
                            continue;
                        }
                        instances += 1;
                        let both = (0..m).all(|b| encode[decode[b]] == b);
                        let lifted: Vec<usize> = (0..m * m)
                            .map(|i| encode[op.at(decode[i / m], decode[i % m])])
                            .collect();
                        let new = Op { n: m, t: &lifted };
                        // From the first equation alone.
                        assert!(!op.associative() || new.associative(), "{t:?} {encode:?}");
                        assert!(!op.commutative() || new.commutative(), "{t:?} {encode:?}");
                        for z in (0..n).filter(|&z| op.zero(z)) {
                            assert!(new.zero(encode[z]), "{t:?} {encode:?} {decode:?}");
                        }
                        // These need the second as well.
                        let idem = !op.idempotent() || new.idempotent();
                        let iden = (0..n)
                            .filter(|&e| op.identity(e))
                            .all(|e| new.identity(encode[e]));
                        if both {
                            assert!(idem && iden, "{t:?} {encode:?} {decode:?}");
                        }
                        idempotence_fails += usize::from(!idem);
                        identity_fails += usize::from(!iden);
                        either_fails += usize::from(!idem || !iden);
                    }
                }
            }
        }
    }
    println!(
        "carrier change: {instances} instances; with only the first equation idempotence fails in {idempotence_fails}, identity in {identity_fails}, one or both in {either_fails}; none with both"
    );
    assert_eq!(
        (instances, idempotence_fails, identity_fails, either_fails),
        (1_002, 249, 249, 369)
    );
}

/// Every sequence of length `c` over `lo..=hi`.
fn sequences(c: usize, lo: i64, hi: i64) -> Vec<Vec<i64>> {
    let width = (hi - lo + 1) as usize;
    maps(c, width)
        .into_iter()
        .map(|s| s.into_iter().map(|v| lo + v as i64).collect())
        .collect()
}

#[test]
fn the_fold_bounds_hold_and_are_reached_at_literal_ends() {
    let mut bounds = 0;
    for lo in -3..=3i64 {
        for hi in lo..=3 {
            for c1 in 0..=3usize {
                for c2 in c1..=3 {
                    bounds += 1;
                    let (k1, k2) = (c1 as i64, c2 as i64);
                    let sum_lo = (k1 * lo).min(k2 * lo);
                    let sum_hi = (k1 * hi).max(k2 * hi);
                    let (mut least, mut most) = (i64::MAX, i64::MIN);
                    for c in c1..=c2 {
                        for s in sequences(c, lo, hi) {
                            let sum: i64 = s.iter().sum();
                            assert!((sum_lo..=sum_hi).contains(&sum), "{s:?}");
                            least = least.min(sum);
                            most = most.max(sum);
                            if let (Some(a), Some(b)) = (s.iter().min(), s.iter().max()) {
                                assert!(lo <= *a && *b <= hi, "{s:?}");
                            }
                        }
                    }
                    // The bound is the tightest: both ends are sums of some level.
                    assert_eq!((least, most), (sum_lo, sum_hi), "{lo} {hi} {c1} {c2}");
                }
            }
        }
    }
    println!("fold bounds: {bounds} bounds, every sum inside and both ends reached");
    assert_eq!(bounds, 280);
}
