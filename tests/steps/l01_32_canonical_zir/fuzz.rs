//! Termination on random graphs: every step lowers the ranks lexicographically, the normal
//! form has no written binder, hint, out-of-order facet or unnormalized domain, and shuffling
//! facets or renaming binders leaves the address alone.

use super::graph;
use zedc::zir::canon::{address, ranks, step};
use zedc::zir::{Edge, Op};

/// A linear congruential generator, so that every run sees the same graphs.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self, n: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((self.0 >> 33) % n as u64) as usize
    }
}

const FACETS: [&str; 6] = [
    "facet units \"m\"",
    "facet units \"s\"",
    "facet locale \"en\"",
    "hint name \"total\"",
    "hint name \"n\"",
    "facet units \"m\"",
];

const NAMES: [&str; 5] = ["a", "b", "count", "x1", "rest"];

/// A random edge, with its facets in the order `order` gives.
fn edge(rng: &mut Lcg) -> String {
    let mut e = String::from("int");
    match rng.next(4) {
        0 => {}
        1 => {
            let lo = rng.next(20) as i64 - 10;
            e += &format!(" in [{lo}..={}]", lo + rng.next(30) as i64);
        }
        2 => e += &format!(" class {} mod {}", rng.next(3), 3 + rng.next(3)),
        _ => {
            let n = 1 + rng.next(4);
            let mut xs: Vec<i64> = (0..n).map(|_| rng.next(25) as i64 - 5).collect();
            xs.sort();
            xs.dedup();
            let xs: Vec<String> = xs.iter().map(i64::to_string).collect();
            e += &format!(" in [-5..=40] set {{{}}}", xs.join(", "));
        }
    }
    for _ in 0..rng.next(4) {
        e += " ";
        e += FACETS[rng.next(FACETS.len())];
    }
    e
}

/// A random graph: a function region whose nodes negate an argument, match a pair, or define a
/// function whose body matches one, binding names the rename function picks.
fn random(rng: &mut Lcg, name: &dyn Fn(usize) -> String) -> String {
    let args = 1 + rng.next(3);
    let arg: Vec<String> = (0..args).map(|_| edge(rng)).collect();
    let mut src = format!("zir 1\nr region function ({})\n", arg.join("; "));
    let mut binder = 0;
    let nodes = rng.next(5);
    for k in 0..nodes {
        let kind = rng.next(3);
        if kind == 0 {
            src += &format!("r.{k} prim neg (r^0) -> ({})\n", edge(rng));
        } else if kind == 1 {
            // A match inside a function's body, one region down.
            let (a, b) = (name(binder), name(binder + 1));
            binder += 2;
            let (ea, eb) = (edge(rng), edge(rng));
            src += &format!(
                "r.{k} lambda () -> ((-> tuple int))\nr.{k}/0 region function (tuple)\nr.{k}/0.0 match [({a}, {b})] (r.{k}/0^0) -> ({})\nr.{k}/0.0/0 region match ({ea}; {eb})\nr.{k}/0.0/0 results (r.{k}/0.0/0^0)\nr.{k}/0 results (r.{k}/0.0^0)\n",
                edge(rng)
            );
        } else {
            let (a, b) = (name(binder), name(binder + 1));
            binder += 2;
            let (ea, eb) = (edge(rng), edge(rng));
            src += &format!(
                "r.{k} match [(#p({a}), {b})] (r^0) -> ({})\nr.{k}/0 region match ({ea}; {eb})\nr.{k}/0 results (r.{k}/0^1)\n",
                edge(rng)
            );
        }
    }
    src + "r results (r^0)\n"
}

#[test]
fn every_step_lowers_the_ranks() {
    let mut rng = Lcg(7);
    let mut steps = 0;
    for _ in 0..300 {
        let mut g = graph(&random(&mut rng, &|i| {
            NAMES[i % NAMES.len()].to_string() + &i.to_string()
        }));
        let mut before = ranks(&g);
        while let Some(rule) = step(&mut g) {
            let after = ranks(&g);
            assert!(after < before, "{rule}: {before:?} -> {after:?}");
            before = after;
            steps += 1;
        }
        assert_eq!(before[..2], [0, 0]);
        assert_eq!(before[3], 0);
        assert_normal(&g);
    }
    // The graphs gave every rule work to do.
    assert!(steps > 1000, "{steps} steps");
}

/// No hint and no out-of-order or repeated facet on any edge.
fn assert_normal(g: &zedc::zir::Region) {
    let mut edges: Vec<&Edge> = g.args.iter().collect();
    for n in &g.nodes {
        edges.extend(&n.outputs);
        for r in &n.regions {
            assert_normal(r);
        }
        if let Op::Match(ps) = &n.op {
            for p in ps {
                assert!(
                    !zedc::zir::text::pattern(p)
                        .contains(|c: char| c.is_ascii_alphabetic() && c != 'p')
                );
            }
        }
    }
    for e in edges {
        if let Edge::Value(v) = e {
            assert!(v.facets.iter().all(|f| !f.hint));
            assert!(v.facets.windows(2).all(|w| w[0] < w[1]));
            assert_eq!(v.domain.rank(), 0);
        }
    }
}

#[test]
fn shuffles_and_renamings_keep_the_address() {
    for seed in 0..200 {
        // The same draws give the same graph; only the names differ.
        let a = graph(&random(&mut Lcg(seed), &|i| format!("v{i}")));
        let b = graph(&random(&mut Lcg(seed), &|i| format!("w{}", 100 - i)));
        assert_eq!(address(&a), address(&b), "seed {seed}");
        // Reversing every edge's facets leaves the address alone.
        let mut c = a.clone();
        reverse_facets(&mut c);
        assert_eq!(address(&c), address(&a), "seed {seed}");
    }
}

fn reverse_facets(g: &mut zedc::zir::Region) {
    for e in g.args.iter_mut() {
        if let Edge::Value(v) = e {
            v.facets.reverse();
        }
    }
    for n in &mut g.nodes {
        for e in n.outputs.iter_mut() {
            if let Edge::Value(v) = e {
                v.facets.reverse();
            }
        }
        n.regions.iter_mut().for_each(reverse_facets);
    }
}
