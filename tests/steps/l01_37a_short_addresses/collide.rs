//! Forced collisions: with `short-addresses`, many of a few hundred distinct values share an
//! address, and each place that meets two of them still tells them apart by their contents.
//! A map that trusts the address alone, planted here, merges them, so it differs between the
//! two builds where the compiler does not.

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

use zed_kernel::address::SHORT;
use zed_kernel::types::Type;
use zed_kernel::{Prim, Term, Value};
use zedc::zir::canon;
use zedc::zir::lower::lower;

use zed_tests::instances::Rng;
use zed_tests::step_helpers::l01_33_lowering::{count, eval, round_trip};

/// `x + 1` for each `x` in `0..n`: `n` distinct prim nodes.
fn sums(n: i64) -> Vec<Term> {
    (0..n)
        .map(|i| {
            Term::Prim(
                Prim::Add,
                vec![Term::Lit(Value::Int(i)), Term::Lit(Value::Int(1))],
            )
        })
        .collect()
}

#[test]
fn colliding_nodes_stay_distinct_in_the_lowering() {
    let t = Term::Prim(Prim::Tuple, sums(600));
    let g = lower(&t).expect("a tuple of sums lowers");
    // Every sum is its own node, in both builds: the lowering confirms each key it finds by
    // the node's contents (`canon::Shape`).
    assert_eq!(count(&g, "prim"), 601);
    assert_eq!(round_trip(&t), eval(&t));
    // The planted site: one node per key, the key trusted alone.
    let keys: HashSet<_> = g
        .nodes
        .iter()
        .map(|n| canon::node_key(n, &[]).expect("memory for the key"))
        .collect();
    if SHORT {
        assert!(keys.len() <= 256, "{} keys of 8 bits", keys.len());
    } else {
        assert_eq!(keys.len(), g.nodes.len());
    }
}

#[test]
fn equal_sums_are_still_one_node() {
    // Collisions do not stop sharing: each sum built twice apart is one node.
    let t = Term::Prim(
        Prim::Tuple,
        sums(300).into_iter().chain(sums(300)).collect(),
    );
    let g = lower(&t).expect("a tuple of sums lowers");
    assert_eq!(count(&g, "prim"), 301);
    assert_eq!(round_trip(&t), eval(&t));
}

/// A hasher that keeps the last word written: a type writes its digest alone.
#[derive(Default)]
struct Last(u64);

impl Hasher for Last {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        unreachable!("a type's hash writes its digest as one word")
    }
    fn write_u64(&mut self, w: u64) {
        self.0 = w;
    }
}

pub(super) fn digest(t: &Type) -> u64 {
    let mut h = Last::default();
    t.hash(&mut h);
    h.finish()
}

#[test]
fn colliding_types_are_distinct_and_ordered_by_contents() {
    let atoms: Vec<Type> = (0..600).map(|i| Type::atom(&format!("a{i}"))).collect();
    let mut by_digest: HashMap<u64, Vec<&Type>> = HashMap::new();
    for t in &atoms {
        by_digest.entry(digest(t)).or_default().push(t);
    }
    let pairs: Vec<&Vec<&Type>> = by_digest.values().filter(|v| v.len() > 1).collect();
    assert_eq!(!pairs.is_empty(), SHORT, "{} digests shared", pairs.len());
    for v in pairs {
        let (a, b) = (v[0], v[1]);
        assert_ne!(a, b);
        assert_ne!(a.cmp(b), std::cmp::Ordering::Equal);
        assert_eq!(a.cmp(b), b.cmp(a).reverse());
        // A union does not depend on the order its parts are given in.
        let ab = Type::union_all([a.clone(), b.clone()]);
        let ba = Type::union_all([b.clone(), a.clone()]);
        assert_eq!(ab, ba);
        assert_eq!(ab.to_string(), ba.to_string());
    }
    // The union of all, given in either order, is one type, and holds each atom.
    let all = Type::union_all(atoms.iter().cloned());
    let back = Type::union_all(atoms.iter().rev().cloned());
    assert_eq!(all, back);
    assert_eq!(all.to_string(), back.to_string());
    for t in &atoms {
        assert_eq!(&all | t, all);
    }
}

#[test]
fn digests_spread_over_all_their_values() {
    // A digest is mixed from its parts' digests in a chain of steps. With 8-bit digests a step
    // that maps the 256 values of one part to fewer would shrink the chain's values at each
    // step: the names a0 to a99999 reached 73 of 256 atom digests and the one-item tuple types
    // over them 31, so ties were far more common than 8 bits make them. In the full build the
    // low 8 bits of the digests are checked.
    let atoms: Vec<Type> = (0..4000).map(|i| Type::atom(&format!("a{i}"))).collect();
    let values = |ts: &mut dyn Iterator<Item = Type>| -> usize {
        ts.map(|t| digest(&t) & 0xff)
            .collect::<HashSet<u64>>()
            .len()
    };
    let tuples = &mut atoms.iter().map(|a| Type::tuple(vec![a.clone()]));
    let morphisms = &mut atoms
        .windows(3)
        .map(|w| Type::morphism(w[0].clone(), w[1].clone(), w[2].clone()));
    let unions = &mut atoms
        .windows(2)
        .map(|w| Type::union_all([w[0].clone(), w[1].clone()]));
    assert_eq!(values(&mut atoms.iter().cloned()), 256, "atoms");
    assert_eq!(values(tuples), 256, "tuples");
    assert_eq!(values(morphisms), 256, "morphism types");
    assert_eq!(values(unions), 256, "unions");
}

/// `depth` levels of a pair of the level below, over `base`.
fn chain(base: Type, depth: usize) -> Type {
    (0..depth).fold(base, |t, _| Type::tuple(vec![t.clone(), t]))
}

#[test]
fn types_that_tie_in_digest_level_after_level_are_ordered_on_a_small_stack() {
    // With 8-bit digests the levels of a chain tie in digest at every depth, so building one
    // orders each new level against older ones level after level down, as ordering two chains
    // over different bases does where their digests tie. That order was a recursion, which
    // overflowed a 256 KiB stack 500 levels down, and a 2 MiB stack about 3,000 levels down
    // (SHORT-stack-l01_22); it is a loop with a stack of its own. Each comparison still reads
    // the levels on which the digests tie, so building the chain is quadratic in this build.
    const DEPTH: usize = 1000;
    const STACK: usize = 256 << 10;
    std::thread::scope(|scope| {
        let thread = std::thread::Builder::new().stack_size(STACK);
        let run = thread.spawn_scoped(scope, || {
            let a = chain(Type::atom("z"), DEPTH);
            let b = chain(Type::atom("z"), DEPTH);
            assert_eq!(a, b);
            let c = chain(Type::atom("y"), DEPTH);
            assert_ne!(a, c);
            assert_ne!(a.cmp(&c), std::cmp::Ordering::Equal);
            assert_eq!(a.cmp(&c), c.cmp(&a).reverse());
        });
        run.unwrap().join().unwrap();
    });
}

/// A random type over a few atoms, integers and tuple, union, meet, difference and morphism
/// types, `depth` levels deep: in the short build most digests of such types tie.
fn random_type(rng: &mut Rng, depth: usize) -> Type {
    if depth == 0 {
        return match rng.below(4) {
            0 => Type::atom(&format!("a{}", rng.below(6))),
            1 => Type::lit(&Value::Int(rng.int(0, 3))).expect("an integer is a literal type"),
            2 => Type::int(),
            _ => Type::top(),
        };
    }
    let kind = rng.below(7);
    let mut part = || {
        let d = rng.below(depth);
        random_type(rng, d)
    };
    match kind {
        0 => Type::tuple(vec![part()]),
        1 => Type::tuple(vec![part(), part()]),
        2 => &part() | &part(),
        3 => &part() & &part(),
        4 => &part() - &part(),
        5 => Type::morphism(part(), part(), part()),
        _ => !&part(),
    }
}

#[test]
fn the_order_of_types_is_total_on_every_pair_of_900() {
    // 900 random types, 810,000 ordered pairs, the size of the probe of SHORT-stack-l01_22. The
    // order is antisymmetric on every pair; two types are equal in it exactly when their texts
    // are; and the types sorted are in order on every pair, so the order is transitive. Sorting
    // the types given in reverse gives the same sequence.
    const TYPES: usize = 900;
    let mut rng = Rng::new(0x37a);
    let types: Vec<Type> = (0..TYPES).map(|_| random_type(&mut rng, 4)).collect();
    let texts: Vec<String> = types.iter().map(|t| t.to_string()).collect();
    let mut tied = 0;
    for (a, ta) in types.iter().zip(&texts) {
        for (b, tb) in types.iter().zip(&texts) {
            let ab = a.cmp(b);
            assert_eq!(ab, b.cmp(a).reverse(), "{ta} against {tb}");
            assert_eq!(ab == Ordering::Equal, ta == tb, "{ta} against {tb}");
            tied += usize::from(ab != Ordering::Equal && digest(a) == digest(b));
        }
    }
    // The short build orders many pairs by contents, as the full build almost never does.
    assert_eq!(tied > TYPES, SHORT, "{tied} distinct pairs tie in digest");
    let mut sorted = types.clone();
    sorted.sort();
    for (i, a) in sorted.iter().enumerate() {
        for b in &sorted[i + 1..] {
            assert_ne!(a.cmp(b), Ordering::Greater, "{a} after {b}");
        }
    }
    let mut back: Vec<Type> = types.iter().rev().cloned().collect();
    back.sort();
    let text = |ts: &[Type]| ts.iter().map(|t| t.to_string()).collect::<Vec<_>>();
    assert_eq!(text(&sorted), text(&back));
}

#[test]
fn rows_dropped_on_another_thread_leave_entries_that_lookups_pass_over() {
    // Rows and morphism types made here and dropped on another thread leave entries in this
    // thread's tables that no longer upgrade. With 8-bit digests they share buckets with live
    // nodes; a lookup cannot compare them, so it takes them out on the way and starts again
    // (step TABLE-short-scan), and the nodes found are those still alive.
    let atoms: Vec<Type> = (0..3000).map(|i| Type::atom(&format!("d{i}"))).collect();
    let make = |a: &Type| {
        [
            Type::tuple(vec![a.clone()]),
            Type::morphism(a.clone(), a.clone(), a.clone()),
        ]
    };
    let (kept, gone): (Vec<_>, Vec<_>) = atoms.iter().enumerate().partition(|(i, _)| i % 2 == 0);
    let kept: Vec<[Type; 2]> = kept.into_iter().map(|(_, a)| make(a)).collect();
    let gone: Vec<[Type; 2]> = gone.into_iter().map(|(_, a)| make(a)).collect();
    std::thread::spawn(move || drop(gone)).join().unwrap();
    for _ in 0..2 {
        for (i, a) in atoms.iter().enumerate() {
            let again = make(a);
            if i % 2 == 0 {
                assert_eq!(again, kept[i / 2]);
            }
            assert_eq!(again[0], Type::tuple(vec![a.clone()]));
            assert_ne!(
                again[0],
                Type::tuple(vec![atoms[(i + 1) % atoms.len()].clone()])
            );
        }
    }
}
