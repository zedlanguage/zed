//! Forced collisions: with `short-addresses`, many of a few hundred distinct values share an
//! address, and each place that meets two of them still tells them apart by their contents.
//! A map that trusts the address alone, planted here, merges them, so it differs between the
//! two builds where the compiler does not.

use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

use zed_kernel::address::SHORT;
use zed_kernel::types::Type;
use zed_kernel::{Prim, Term, Value};
use zedc::zir::canon;
use zedc::zir::lower::lower;

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

fn digest(t: &Type) -> u64 {
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
