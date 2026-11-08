//! The order the traversal visits the cells in (DESIGN.md step M0.5): by name, then by the
//! content address of the static node, then by that node's canonical form, never by where an
//! equation is written. Moving an equation changes no head and no cell; renaming one may
//! change the head, and does so the same way wherever the equations are written.

use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zed_tests::scaling;
use zedc::address::ContentAddress;
use zedc::ast::unit;
use zedc::check::walk::check;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};
use zedc::resolve::resolve;
use zedc::store::interval::IntervalSet;
use zedc::store::iterate::{Equations, order, phase1, solve};
use zedc::store::landmarks::Landmarks;
use zedc::store::wto::{Element, SameKey, VertexKey};

use super::iteration::three_cell_loop;
use super::{System, iv};

/// The six orders the three equations of a loop can be written in: `ix[k]` is the place of
/// the `k`-th equation.
const SIX: [[usize; 3]; 6] = [
    [0, 1, 2],
    [0, 2, 1],
    [1, 0, 2],
    [1, 2, 0],
    [2, 0, 1],
    [2, 1, 0],
];

/// The order in Bourdoncle's notation, each cell printed by its name.
fn by_name(eq: &System, order: &[Element]) -> String {
    fn put(eq: &System, e: &Element, out: &mut Vec<String>) {
        match e {
            Element::Vertex(v) => out.push(eq.names[*v].clone()),
            Element::Component { head, body } => {
                let mut inner = vec![eq.names[*head].clone()];
                for b in body {
                    put(eq, b, &mut inner);
                }
                out.push(format!("({})", inner.join(" ")));
            }
        }
    }
    let mut out = Vec::new();
    for e in order {
        put(eq, e, &mut out);
    }
    out.join(" ")
}

/// The cells of `eq` by name: phase 1's, then both phases'.
fn cells_by_name(eq: &System) -> Vec<(String, String, String)> {
    let order = order(eq).unwrap();
    let first = phase1(eq, &order);
    let both = solve(eq).unwrap();
    let mut out: Vec<_> = (0..eq.names.len())
        .map(|v| {
            (
                eq.names[v].clone(),
                first[v].to_string(),
                both[v].to_string(),
            )
        })
        .collect();
    out.sort();
    out
}

#[test]
fn the_loop_gives_c_at_1_to_4_in_each_order_of_its_equations() {
    // `a = 0 ⊔ c; b = a + 1; c = b ⊓ int[..=4]`, with no landmarks, in each of the six orders
    // of its equations: the traversal starts at `a`, the least name, so the loop is cut at `a`
    // and the bound on `c` survives the widening at `a`.
    for ix in SIX {
        let eq = three_cell_loop(["a", "b", "c"], ix).bare();
        let order = order(&eq).unwrap();
        assert_eq!(by_name(&eq, &order), "(a b c)", "equations at {ix:?}");
        let [a, b, c] = ix;
        let first = phase1(&eq, &order);
        assert_eq!(first[c], iv(Some(1), Some(4)), "equations at {ix:?}");
        assert_eq!(
            [&first[a], &first[b]],
            [&iv(Some(0), None), &iv(Some(1), None)]
        );
        let both = solve(&eq).unwrap();
        assert_eq!(
            [&both[a], &both[b], &both[c]],
            [
                &iv(Some(0), Some(4)),
                &iv(Some(1), Some(5)),
                &iv(Some(1), Some(4))
            ],
            "equations at {ix:?}"
        );
        // With the program's literals as landmarks, the same.
        let marked = three_cell_loop(["a", "b", "c"], ix);
        assert_eq!(
            cells_by_name(&marked),
            cells_by_name(&three_cell_loop(["a", "b", "c"], SIX[0]))
        );
        assert_eq!(solve(&marked).unwrap()[c], iv(Some(1), Some(4)));
    }
}

#[test]
fn reversed_and_rotated_units_give_the_same_cells() {
    // Each random system, with its equations reversed and rotated by each position, gives the
    // same order and the same cells by name, in phase 1 and after both phases.
    let mut rng = Rng::new(0x05b7);
    let mut cut = 0;
    for _ in 0..RANDOM_INSTANCES {
        let eq = System::random(&mut rng);
        let eq = if rng.below(2) == 0 { eq } else { eq.bare() };
        let n = eq.names.len();
        let want_order = by_name(&eq, &order(&eq).unwrap());
        let want = cells_by_name(&eq);
        if want_order.contains('(') {
            cut += 1;
        }
        let reversed: Vec<usize> = (0..n).rev().collect();
        let mut moves = vec![reversed];
        moves.extend((1..n).map(|r| (0..n).map(|v| (v + r) % n).collect()));
        for old in moves {
            let m = eq.renumbered(&old);
            assert_eq!(
                by_name(&m, &order(&m).unwrap()),
                want_order,
                "{old:?}: {eq:?}"
            );
            assert_eq!(cells_by_name(&m), want, "{old:?}: {eq:?}");
        }
    }
    // The sample has loops, where the head decides the cells.
    assert!(cut > RANDOM_INSTANCES / 4, "{cut} systems with a loop");
}

#[test]
fn a_rename_that_changes_the_head_does_so_in_every_order() {
    // Renaming `c` to `_c`, which sorts before `a`, makes `c` the head: in phase 1 the bound
    // on `c` is then widened away, in all six orders alike. Renaming `a` to `z` makes `b` the
    // least name, and `b` heads the loop in all six orders. Phase 2 recovers `c`'s bound.
    for (names, want_order, want_c) in [
        (["a", "b", "_c"], "(_c a b)", iv(Some(1), None)),
        (["z", "b", "c"], "(b c z)", iv(Some(1), Some(4))),
    ] {
        let first = three_cell_loop(names, SIX[0]).bare();
        let want = cells_by_name(&first);
        for ix in SIX {
            let eq = three_cell_loop(names, ix).bare();
            assert_eq!(
                by_name(&eq, &order(&eq).unwrap()),
                want_order,
                "{names:?} at {ix:?}"
            );
            assert_eq!(
                phase1(&eq, &order(&eq).unwrap())[ix[2]],
                want_c,
                "{names:?} at {ix:?}"
            );
            assert_eq!(cells_by_name(&eq), want, "{names:?} at {ix:?}");
            assert_eq!(solve(&eq).unwrap()[ix[2]], iv(Some(1), Some(4)));
        }
    }
}

#[test]
fn nodes_of_one_binding_are_ordered_by_address_and_then_by_form() {
    // The three cells are nodes inside one binding's expression, so they share its name, and
    // the traversal orders them by the content addresses of their nodes.
    for ix in SIX {
        let eq = three_cell_loop(["x", "x", "x"], ix).bare();
        let first = (0..3).min_by_key(|&v| eq.addresses[v]).unwrap();
        let order = order(&eq).unwrap();
        assert!(
            matches!(&order[..], [Element::Component { head, .. }] if *head == first),
            "equations at {ix:?}: {order:?}"
        );
    }
    // Two different nodes with one address, as a collision of the hash would give: their
    // canonical forms, compared as structures, decide. The address is not trusted as identity.
    let mut heads = Vec::new();
    for ix in SIX {
        let mut eq = three_cell_loop(["x", "x", "x"], ix).bare();
        eq.addresses = vec![ContentAddress([7; 32]); 3];
        let first = (0..3).min_by_key(|&v| &eq.forms[v]).unwrap();
        let order = order(&eq).unwrap();
        let [Element::Component { head, .. }] = &order[..] else {
            panic!("one loop: {order:?}");
        };
        assert_eq!(*head, first, "equations at {ix:?}");
        heads.push(ix.iter().position(|&k| k == *head).unwrap());
    }
    // It is the same equation in every order.
    assert!(heads.iter().all(|&h| h == heads[0]), "{heads:?}");
}

#[test]
fn two_cells_with_one_key_are_refused_wherever_they_are_written() {
    // Two cells with the same name, address and form: no order of the traversal tells them
    // apart, so the only order left is the written one, and the order is refused instead.
    let eq = System::named(
        vec!["x".into(), "x".into(), "y".into()],
        vec![
            IntervalSet::single(1),
            IntervalSet::single(1),
            IntervalSet::single(2),
        ],
        vec![vec![], vec![], vec![]],
    );
    for old in [[0, 1, 2], [2, 1, 0], [1, 2, 0], [2, 0, 1]] {
        let m = eq.renumbered(&old);
        let err = order(&m).unwrap_err();
        let SameKey(u, w) = err;
        assert!(u < w && m.names[u] == "x" && m.names[w] == "x", "{err}");
        assert_eq!(solve(&m).unwrap_err(), err);
        assert!(
            err.to_string()
                .contains("same name, content address and canonical form")
        );
    }
}

/// Cells with given reads and keys, whose equations give nothing: the cost of the order alone.
struct Keyed {
    reads: Vec<Vec<usize>>,
    names: Vec<String>,
    address: ContentAddress,
    forms: Vec<Vec<u32>>,
}

impl Equations<IntervalSet> for Keyed {
    type Form = Vec<u32>;
    fn reads(&self) -> &[Vec<usize>] {
        &self.reads
    }
    fn key(&self, v: usize) -> VertexKey<'_, Vec<u32>> {
        VertexKey {
            name: &self.names[v],
            address: self.address,
            form: &self.forms[v],
        }
    }
    fn eval(&self, _: usize, _: &[IntervalSet]) -> IntervalSet {
        IntervalSet::empty()
    }
    fn landmarks(&self, _: usize) -> Landmarks {
        Landmarks::none()
    }
}

/// `n` cells, cell `v` reading `read(v)`, named by `name(v)`, each form 8 numbers that differ
/// only in the last.
fn keyed(n: usize, read: impl Fn(usize) -> Vec<usize>, name: impl Fn(usize) -> String) -> Keyed {
    Keyed {
        reads: (0..n).map(read).collect(),
        names: (0..n).map(name).collect(),
        address: ContentAddress([1; 32]),
        forms: (0..n)
            .map(|v| [vec![5; 7], vec![v as u32]].concat())
            .collect(),
    }
}

/// Runs the order at `n` and `8n` on the systems `build` makes, built before the timing.
fn order_scales(what: &str, n: usize, build: impl Fn(usize) -> Keyed) {
    let (small, large) = (build(n), build(scaling::FACTOR * n));
    scaling::check_order(what, n, 1, |m| {
        let eq = if m == n { &small } else { &large };
        order(eq).unwrap();
    });
}

/// Names whose order is not the order of the numbers: written in one order, read in another.
fn scrambled(v: usize) -> String {
    format!(
        "x{:08}",
        (v as u64).wrapping_mul(2_654_435_761) % 100_000_007
    )
}

#[test]
fn the_order_of_a_long_chain_scales() {
    order_scales("the keyed order of a chain", 20_000, |n| {
        keyed(n, |v| if v == 0 { vec![] } else { vec![v - 1] }, scrambled)
    });
}

#[test]
fn the_order_of_many_small_loops_scales() {
    // Loops of three cells, each reading the one before it in the loop.
    order_scales("the keyed order of loops of three", 21_000, |n| {
        keyed(n, |v| vec![v - v % 3 + (v + 2) % 3], scrambled)
    });
}

#[test]
fn the_order_of_one_bindings_nodes_scales() {
    // Every cell has one name and one address, so every comparison reaches the canonical
    // forms: n log n comparisons of forms of a fixed length.
    order_scales(
        "the keyed order of nodes with one name and address",
        21_000,
        |n| keyed(n, |v| vec![v - v % 3 + (v + 2) % 3], |_| "x".to_string()),
    );
}

/// What the checker finds in `text`: each declared function's signature and each top-level
/// name's type by name, and the type errors with the text they point at, each sorted.
fn findings(text: &str) -> (Vec<String>, Vec<String>) {
    let tokens = lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    let stmts = unit(text, &tokens, &tree).unwrap();
    let res = resolve(&stmts).unwrap_or_else(|e| panic!("{text}: {e:?}"));
    let info = check(&stmts, &res);
    let mut types: Vec<String> = info
        .sigs
        .iter()
        .map(|(b, s)| format!("{}: {s}", res.binders[*b].name))
        .chain(info.tops.iter().map(|(n, t)| format!("{n} = {t}")))
        .collect();
    types.sort();
    let mut errors: Vec<String> = info
        .errors
        .iter()
        .map(|e| format!("{} [{}]", e.message, &text[e.span.start..e.span.end]))
        .collect();
    errors.sort();
    (types, errors)
}

#[test]
fn a_unit_reversed_and_rotated_gives_the_same_types_and_diagnostics() {
    // A unit whose declarations use one another in both directions, with one type error.
    // The calls pass each parameter by name, as its declaration says (sec:values_morphisms).
    let decls = [
        "area(w, h) = w * h;",
        "total = area(w: 3, h: 4) + bump(x: 2);",
        "bump(x) = x + 1;",
        "bad(x) = x + \"a\" * 2;",
        "shout(s) = upper(s) ++ \"!\";",
        "loud = shout(s: \"hi\") ++ \"?\";",
        "half(x) = x / 2n;",
    ];
    let text = |order: &[usize]| {
        order
            .iter()
            .map(|&k| format!("{}\n", decls[k]))
            .collect::<String>()
    };
    let n = decls.len();
    let want = findings(&text(&(0..n).collect::<Vec<_>>()));
    assert_eq!(want.1, ["`*` does not take (\"a\", 2) [\"a\" * 2]"]);
    assert!(want.0.contains(&"bump: (x: int) -> int".to_string()));
    assert!(want.0.contains(&"shout: (s: String) -> String".to_string()));
    assert!(want.0.contains(&"total = int".to_string()), "{:?}", want.0);
    assert!(
        want.0.contains(&"loud = String".to_string()),
        "{:?}",
        want.0
    );
    let mut moves: Vec<Vec<usize>> = vec![(0..n).rev().collect()];
    moves.extend((1..n).map(|r| (0..n).map(|v| (v + r) % n).collect()));
    for old in moves {
        assert_eq!(
            findings(&text(&old)),
            want,
            "declarations in the order {old:?}"
        );
    }
}
