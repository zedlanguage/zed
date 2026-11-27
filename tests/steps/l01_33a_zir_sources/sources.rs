//! The sources of each node and the nodes of each source (DESIGN.md step L1.33a): a node CSE
//! shares has the source of every copy, in source order; a source node is named by its
//! declaration and its path, so text above the declaration changes no entry; the run-time
//! sites table is what it was.

use std::collections::HashSet;

use zed_kernel::sites::{Recorder, Sites, Span, mark};
use zed_kernel::term::build::{lit, prim};
use zed_kernel::{Family, Prim, Term, Value};
use zed_tests::kernel::fam;
use zedc::source_map::{Declaration, SourceMap, SourceNode};
use zedc::zir::lower::{lower_debug, lower_sited};
use zedc::zir::text::print;
use zedc::zir::{Op, Region};

use super::{mapped, shared_chain};

/// The program of the step's test: `f`'s two sums are equal, so they are one node.
const F: &str = "f(positional x: rat) = (x + 1r) * (x + 1r);\nmain(m: MainArgs) {\n    n = \
                 int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 1;\n    m.stdout <- \
                 String(f(rat(n)));\n}\n";

/// The source node at `path` in the first declaration named `name`.
fn at(name: &str, path: &[u32]) -> SourceNode {
    SourceNode {
        declaration: Declaration {
            name: Some(name.into()),
            nth: 0,
        },
        path: path.to_vec(),
    }
}

/// The text of `s` in `text`, which `map` was built from.
fn text<'a>(map: &SourceMap, text: &'a str, s: &SourceNode) -> &'a str {
    let span = map.span(s).unwrap_or_else(|| panic!("no node {s:?}"));
    &text[span.start..span.end]
}

/// The text without the parentheses around it, if the parser keeps them in its span.
fn bare(t: &str) -> &str {
    t.strip_prefix('(')
        .and_then(|t| t.strip_suffix(')'))
        .unwrap_or(t)
}

/// Whether each node of `g` is a read of a port, by node number in preorder, as the sites are
/// numbered.
fn reads(g: &Region) -> Vec<bool> {
    let mut out = Vec::new();
    let mut todo = vec![g.nodes.iter()];
    while let Some(top) = todo.last_mut() {
        let Some(n) = top.next() else {
            todo.pop();
            continue;
        };
        out.push(matches!(n.op, Op::Read(_)));
        todo.extend(n.regions.iter().rev().map(|r| r.nodes.iter()));
    }
    out
}

#[test]
fn the_addition_of_two_equal_sums_has_both_sums() {
    let (p, g, sited, map) = mapped(F);
    let (product, left, right) = (at("f", &[0]), at("f", &[0, 0]), at("f", &[0, 1]));
    assert_eq!(text(&map, p.text(), &product), "(x + 1r) * (x + 1r)");
    for s in [&left, &right] {
        assert_eq!(bare(text(&map, p.text(), s)), "x + 1r");
    }
    assert_ne!(map.span(&left), map.span(&right));
    let both = [left.clone(), right.clone()];
    let shared: Vec<usize> = (0..sited.sources.len())
        .filter(|&x| map.sources(x) == both)
        .collect();
    let [x] = shared[..] else {
        panic!("{shared:?} have both sums: {}", print(&g));
    };
    // The reverse map of each sum gives that node, and only it.
    assert_eq!(map.zir_of(&left), [x]);
    assert_eq!(map.zir_of(&right), [x]);
    // Its site, by which a run-time error is placed, is one of the two, the first lowered.
    let site = sited.sites[x].expect("the addition has a site");
    assert!([map.span(&left), map.span(&right)].contains(&Some(site)));
    // The constant `1r` of each sum is an operand of the addition (`prim + (…, 1r)`), not a
    // node, so no node has it; the product has one source.
    let ones = [at("f", &[0, 0, 1]), at("f", &[0, 1, 1])];
    for o in &ones {
        assert_eq!(text(&map, p.text(), o), "1r");
        assert_eq!(map.zir_of(o), [] as [usize; 0], "{}", print(&g));
    }
    let products = map.zir_of(&product);
    assert_eq!(products.len(), 1, "{}", print(&g));
    assert_eq!(map.sources(products[0]), [product]);
    assert_eq!(map.missed(), 0);
}

#[test]
fn text_above_a_declaration_changes_no_entry() {
    // A blank line above `f`, and a declaration `main` does not reach: the graph is the
    // same, the byte offsets of every source move, and no entry changes.
    let (_, g, a, m) = mapped(F);
    for above in ["\n", "g(positional y: int) = y + 1;\n\n"] {
        let (_, h, b, n) = mapped(&format!("{above}{F}"));
        assert_eq!(print(&h), print(&g));
        assert_eq!(b.sources.len(), a.sources.len());
        let moved = above.len();
        for (x, (s, t)) in a.sources.iter().zip(&b.sources).enumerate() {
            let shifted: Vec<Span> = (s.iter())
                .map(|s| Span {
                    start: s.start + moved,
                    end: s.end + moved,
                })
                .collect();
            assert_eq!(*t, shifted, "node {x}");
            assert_eq!(n.sources(x), m.sources(x), "node {x}");
            for source in m.sources(x) {
                assert_eq!(n.zir_of(&source), m.zir_of(&source), "{source:?}");
            }
        }
        assert_eq!(n.len(), m.len());
    }
    assert!(m.len() > 0);
}

#[test]
fn the_sites_table_gives_each_node_the_site_it_gave_before() {
    // The table of `lower_sited`, which the executable's run-time errors are placed by, is the
    // site of the first node lowered, as before step L1.33a; it is among the node's sources,
    // which are in source order and each once.
    for src in [F.to_string(), shared_chain(3)] {
        let (p, g, sited, map) = mapped(&src);
        let (h, sites) = lower_sited(&p.term(), Some(p.sites())).unwrap();
        assert_eq!(print(&h), print(&g));
        assert_eq!(sites, sited.sites);
        assert_eq!(sited.sources.len(), sites.len());
        for (x, (site, sources)) in sites.iter().zip(&sited.sources).enumerate() {
            match site {
                Some(s) => {
                    assert!(sources.contains(s), "node {x}: {s:?} in {sources:?}");
                    assert!(!map.sources(x).is_empty(), "node {x}");
                }
                None => assert_eq!(sources, &[], "node {x}"),
            }
            assert!(
                sources
                    .windows(2)
                    .all(|w| (w[0].start, w[0].end) < (w[1].start, w[1].end)),
                "node {x}: {sources:?}"
            );
        }
        // One entry for each pair of node and source.
        let pairs: usize = (0..sites.len()).map(|x| map.sources(x).len()).sum();
        assert_eq!(map.len(), pairs);
        assert_eq!(map.missed(), 0);
    }
}

#[test]
fn each_line_of_a_chain_has_one_sum_with_both_copies() {
    // The small instance of `bench::building_the_map_scales`: line k's sums are at the paths
    // `[0, k, 0, 0, 0]` and `[0, k, 0, 1, 0]` of `main` (its body, the statement, the value,
    // each remainder, its sum), one node with both.
    let m = 3;
    let (p, _, sited, map) = mapped(&shared_chain(m));
    for k in 1..=m as u32 {
        let sums = [at("main", &[0, k, 0, 0, 0]), at("main", &[0, k, 0, 1, 0])];
        for s in &sums {
            assert_eq!(bare(text(&map, p.text(), s)), format!("s{} + 1", k - 1));
        }
        let [x] = map.zir_of(&sums[0])[..] else {
            panic!("line {k}: {:?}", map.zir_of(&sums[0]));
        };
        assert_eq!(map.zir_of(&sums[1]), [x]);
        assert_eq!(map.sources(x), sums);
    }
    assert!(map.len() >= 5 * m, "{}", map.len());
    assert!(map.len() <= sited.sources.iter().map(Vec::len).sum());
}

#[test]
fn a_read_placed_outside_a_family_has_the_source_of_each_read() {
    // `[for i in {1, 2}: show(stdin) ++ show(stdin)]`, the two `show`s at sites of their own:
    // both reads of `stdin` are placed outside the family body as one node, the second taking
    // the first one's value (`Lower::read_frame`), so that node has both sites, as the two
    // `show`s, merged by CSE, have.
    let (one, two) = (Span { start: 0, end: 4 }, Span { start: 8, end: 12 });
    let recorder = Recorder::start(&Sites::default());
    let mut seen = HashSet::new();
    let show = |span: Span, seen: &mut HashSet<u64>| {
        let t = prim(Prim::Show, vec![Term::Read("stdin".into())]);
        mark(&t, span, seen);
        t
    };
    let (a, b) = (show(one, &mut seen), show(two, &mut seen));
    let t = fam(
        lit(Family::set([1, 2].map(Value::Int))),
        "i",
        prim(Prim::Concat, vec![a, b]),
    );
    let sites = recorder.freeze([&t]);
    let (g, sited) = lower_debug(&t, Some(&sites)).unwrap();
    let is_read = reads(&g);
    assert_eq!(is_read.len(), sited.sources.len());
    let reads: Vec<usize> = (0..is_read.len()).filter(|&x| is_read[x]).collect();
    let [r] = reads[..] else {
        panic!("{reads:?}: {}", print(&g));
    };
    assert_eq!(sited.sources[r], [one, two], "{}", print(&g));
    assert_eq!(sited.sites[r], Some(one));
}
