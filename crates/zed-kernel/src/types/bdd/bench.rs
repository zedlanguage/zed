//! The benchmarks of the parts of types, run by `tools/run_tests.sh --bench` and left out of
//! its default run (TEST-bench-move-crates). Each check they make besides the ratio has a small
//! instance among the correctness tests in `tests.rs`, named at each benchmark.

use super::tests::*;
use super::*;
use crate::types::{Row, Type};

use crate::scaling;

#[test]
fn forced_atoms_of_a_long_chain_scale() {
    // `w ∧ ((x_1 ∧ … ∧ x_m) ∨ z)`: `true` is reached past `z` from every `x_k`. Finding the
    // branches that dominate `true` took the nearest common dominator of `m` branches at
    // growing depths, walking up one step at a time: `O(m²)`. Small instances:
    // `the_one_atom_a_chain_forces_is_its_first`.
    std::thread::Builder::new()
        .spawn(|| {
            let n = 1 << 12;
            let built = scaling::inputs(n, forced_chain);
            scaling::check("the forced atoms of a chain, by its length", n, |m| {
                let (p, w) = &built[&m];
                assert_eq!(p.forced(), (vec![w.clone()], Vec::new()));
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn forced_atoms_of_a_long_conjunction_scale() {
    // `x_0 ∧ x_1 ∧ … ∧ x_{m-1}`, every third literal refused, kept as expressions: built one
    // literal at a time, and as a balanced tree, whose meets join two large sets. A pass that
    // copied the settings found so far at each conjunction took 12.5 ms at 512 literals and
    // 760 ms at 4096 (cross-review XR3, R3_CODEX.md Q7). Small instances:
    // `a_conjunction_forces_each_of_its_literals`.
    let n = 1 << 13;
    let built: BTreeMap<usize, (Part<Row>, Part<Row>)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, (conjunction(m, false), conjunction(m, true))))
        .collect();
    for (&m, (deep, balanced)) in &built {
        let expected = conjunction_forced(m);
        assert_eq!(sorted_forced(deep.forced()), expected, "{m}, one at a time");
        assert_eq!(sorted_forced(balanced.forced()), expected, "{m}, balanced");
    }
    scaling::check(
        "the forced atoms of a conjunction, by its literals",
        n,
        |m| {
            let (deep, balanced) = &built[&m];
            std::hint::black_box((deep.forced(), balanced.forced()));
        },
    );
}

#[test]
fn comparing_equal_expressions_built_apart_scales() {
    // `x_{k+1} = x_k & !x_k`, built twice: both operands of each level lead to the level
    // below, so comparing operand by operand met the bottom `2^depth` times. Small
    // instances: `equal_expressions_built_apart_compare_equal`.
    std::thread::Builder::new()
        .spawn(|| {
            let n = 1 << 17;
            let built: BTreeMap<usize, (Part<Row>, Part<Row>)> = [n, scaling::FACTOR * n]
                .into_iter()
                .map(|m| (m, (self_meets(m), self_meets(m))))
                .collect();
            scaling::check(
                "comparing equal expressions built apart, by depth",
                n,
                |m| {
                    let (a, b) = &built[&m];
                    assert_eq!(a.cmp(b), Ordering::Equal);
                },
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn comparing_equal_lists_built_on_two_threads_scales() {
    // A list of `m` literals in blocks of two of alternating values. Each thread has its
    // own tables of cells and sets, so the two lists share no node, and comparing them
    // reads each pair of cells and of set nodes once. (The parity of `m` atoms, a diagram
    // the lists no longer build, met its last atom `2^m` times when compared `hi` then
    // `lo`.) Small instances: `equal_lists_built_on_two_threads_compare_equal`.
    let n = 1 << 15;
    let on_a_thread = |m: usize| {
        std::thread::spawn(move || paired_literals(m))
            .join()
            .unwrap()
    };
    let built: BTreeMap<usize, (Part<Row>, Part<Row>)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, (on_a_thread(m), on_a_thread(m))))
        .collect();
    scaling::check(
        "comparing equal lists built on two threads, by literals",
        n,
        |m| {
            let (a, b) = &built[&m];
            assert_eq!(a.cmp(b), Ordering::Equal);
        },
    );
}

#[test]
fn list_of_alternating_literals_scales() {
    // `((x0 | x1) & !x2 | x3) & !x4 …`, each new literal first in the order, so every
    // literal is a block of its own: finding the blocks one by one took a pass over the
    // diagram's nodes per block. Small instances:
    // `a_list_of_alternating_literals_has_a_block_per_literal`.
    let n = 1 << 15;
    let built: BTreeMap<usize, Bdd<Row>> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, alternating_literals(m)))
        .collect();
    scaling::check(
        "the decision list of alternating literals, by atoms",
        n,
        |m| {
            let l = built[&m].list();
            assert_eq!(l.blocks.len(), m - 1);
            assert!(!l.tail);
        },
    );
}

#[test]
fn joining_chains_to_lists_scales() {
    // `((x_0 | x_1) & !x_2 | x_3) & !x_4 …` built a literal at a time, each new literal last
    // in the order of the atoms: the diagram the chain rule built had up to `k` nodes on
    // the `k`-th atom, `O(m²)` in all, and built them all again at each literal (the
    // negative control in STATUS.md, CHAIN-zip-size). A list takes each literal into its
    // first block, or a block of its own, in `O(log m)`. Two chains with half their atoms
    // in common are joined a literal of the shorter at a time. Small instances:
    // `chains_built_a_literal_at_a_time_stay_lists`.
    let n = 1 << 11;
    let lits = scaling::inputs(n, |m| {
        let mut xs: Vec<Row> = (0..m as u64).map(atom).collect();
        xs.sort();
        let lits: Vec<(Part<Row>, Part<Row>)> = xs
            .into_iter()
            .map(|x| (Part::literal(x.clone()), Part::literal(x).not()))
            .collect();
        lits
    });
    let chains = scaling::inputs(n, |m| {
        let chain = |from: u64| {
            (from..from + m as u64).fold(Part::leaf(false), |f, k| {
                f.zip(&Part::literal(atom(k)), Op::Or)
            })
        };
        (chain(0), chain(m as u64 / 2))
    });
    scaling::check("a list built a literal at a time, by literals", n, |m| {
        let xs = &lits[&m];
        let f =
            (xs[1..].iter().enumerate()).fold(xs[0].0.clone(), |f, (i, (x, not_x))| match i % 2 {
                0 => f.zip(x, Op::Or),
                _ => f.zip(not_x, Op::And),
            });
        assert!(matches!(f, Part::Bdd(_)), "{f:?}");
    });
    // A chain grown a literal at a time stays a chain, so both operands of each step are
    // chains; listing the long one too at each step took `O(m²)` (59 s for the forced atoms
    // of a chain of 32768 literals).
    // Each literal goes into the chain's one block, so the work follows the right spine of
    // the block's treap; it is summed over `SHAPES` offsets of the atoms.
    let shapes = scaling::inputs(n, |m| {
        (0..SHAPES)
            .map(|j| {
                let mut xs: Vec<Row> = (0..m as u64).map(|i| atom(j * SHAPE_STRIDE + i)).collect();
                xs.sort();
                xs.into_iter().map(Part::literal).collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    });
    for op in [Op::Or, Op::And] {
        scaling::check("a chain built a literal at a time, by literals", n, |m| {
            for xs in &shapes[&m] {
                let f = (xs[1..].iter()).fold(xs[0].clone(), |f, x| f.zip(x, op));
                assert!(
                    matches!(&f, Part::Bdd(b) if b.chain_len(op) == Some(m)),
                    "{f:?}"
                );
            }
        });
    }
    scaling::check(
        "the union of two chains with half their atoms in common, by literals",
        n,
        |m| {
            let (a, b) = &chains[&m];
            assert!(a.zip(b, Op::Or) != *a);
        },
    );
}

#[test]
fn parity_built_a_literal_at_a_time_scales() {
    // Small instances: `exclusive_ors_built_in_any_order_are_one_node`.
    // Parity built a literal at a time, as the type operations build it: each step takes a
    // literal into the set of the one form in `O(log n)`, and makes the expressions of the
    // `O(log n)` new tree nodes. Each size has atoms of its own. Each literal rebuilds the
    // nodes on its path in the set's treap, so the work follows that path; parity is built
    // over `SHAPES` offsets of the atoms.
    //
    // Measured (16 offsets, 2026-11-09): the tree nodes built per literal at 128 to 8,192
    // literals are 6.30, 7.99, 9.25, 10.48, 11.98, 13.18, 14.84, that is `2 H_n - 4.45`
    // within 0.15, the depth of a treap built by random insertion. So the work is `n log n`
    // with a negative constant term, and its ratio at `n` and `8n` approaches the limit's
    // `ln(8n)/ln(n) × 1.1` from above as `n` falls; at 2,048 and 16,384 the limit is 11.20.
    // With the atoms in sorted order the nodes per literal are `H_n - 1.5`.
    //
    // Each node cost about 147,000 instructions while `xor::half` met its operands by `zip`,
    // whose search for a simpler form (`choice_of`, `same_as_not`, `choice`, `negate`) never
    // finds one for the halves of an exclusive or (see `xor::meet`). With `xor::meet` a node
    // costs about 34,000: 6.51G and 66.12G instructions at 2,048 and 16,384 (10.2 times),
    // 696M and 6.96G bytes (10.0 times), 25 s at load 6 (SCALE-log-offset). Releasing a
    // shared handle in place, one table probe per freed node, the inner nodes' exclusive ors
    // kept in a table, two literals met at once and the exclusive or tested before `zip`'s
    // frames bring it to 4.99G and 50.09G (10.0 times), 489M and 4.97G bytes (10.2 times),
    // 28 s at load 31 where the code before took 54 s at load 30, and 51 s inside a run of
    // 508 tests (KERNEL-parity-cost). So the sizes are now 1,024 and 8,192 literals, where the
    // limit is 11.44: 2.26G and 23.36G instructions (10.3 times), 221M and 2.31G bytes (10.4
    // times), 11 s at load 30. Rebuilding every tree node on each literal fails the check at
    // 128 and 1,024 literals, by 58.6 times the bytes. Making each exclusive or's two meets
    // only when its form is read (KERNEL-parity-lazy-halves) takes 1.96G and 20.45G
    // instructions to 1.48G and 15.31G (10.3 times), 221M and 2.31G bytes to 138M and 1.39G
    // (10.1 times), and 10.4 s to 7.0 s at load 11 to 22.
    let n = 1 << 10;
    let lits = scaling::inputs(n, |m| {
        (0..SHAPES)
            .map(|j| {
                (0..m as u64)
                    .map(|i| Part::literal(atom(j * SHAPE_STRIDE + 16 * m as u64 + i)))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    });
    scaling::check("parity built a literal at a time, by literals", n, |m| {
        for ls in &lits[&m] {
            let x = ls.iter().fold(Part::leaf(false), |f, l| xor_by_or(&f, l));
            assert!(x.xor_tag().is_some());
        }
    });
}

#[test]
fn exclusive_ors_scale() {
    // The exclusive ors of the first half and of the last three quarters of `n` atoms, which
    // share a quarter, are joined in `O(n log n)`. Each size has atoms of its own. Small
    // instances: `exclusive_ors_with_atoms_in_common_join_in_an_exclusive_or`.
    let n = 1 << 13;
    let halves = scaling::inputs(n, overlapping_xors);
    scaling::check(
        "two exclusive ors with half their atoms in common joined, by literals",
        n,
        |m| {
            let (a, b) = &halves[&m];
            assert!(xor_by_and(a, b).xor_tag().is_some());
        },
    );
}

#[test]
fn ordering_types_whose_digests_tie_at_every_depth_scales() {
    // Small instances: `types_whose_digests_tie_at_every_depth_are_ordered`.
    // One step per level: the two chains are equal, so every level is read.
    let n = 100_000;
    let built: BTreeMap<usize, (Type, Type)> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| (m, (tied("z", m), tied("z", m))))
        .collect();
    scaling::check(
        "ordering two equal chains of tied digests, by depth",
        n,
        |m| {
            let (a, b) = &built[&m];
            assert_eq!(a.cmp(b), Ordering::Equal);
        },
    );
}

#[test]
fn the_walks_over_parts_scale() {
    // Small instances: `the_walks_over_parts_hold_at_small_depths`.
    let n = 1 << 14;
    let sizes = [n, scaling::FACTOR * n];
    let ors: BTreeMap<usize, Part<Row>> = sizes
        .map(|m| (m, ors(10 * m as u64, m, Part::literal)))
        .into();
    let pins: BTreeMap<usize, Part<Row>> = sizes
        .map(|m| (m, settled_by_one_pin(20 * m as u64, m)))
        .into();
    let meets: BTreeMap<usize, Part<Row>> =
        sizes.map(|m| (m, Part::Bdd(meet(30 * m as u64, m)))).into();
    let ladders: BTreeMap<usize, Part<Row>> = sizes.map(|m| (m, ladder(40 * m as u64, m))).into();
    scaling::check("eval of an expression, by depth", n, |m| {
        assert!(!ors[&m].eval(&|_| false));
    });
    // Every expression but the top one is read twice, the second time from the memo.
    scaling::check(
        "eval of an expression whose operands are shared, by depth",
        n,
        |m| {
            assert!(!ladders[&m].eval(&|_| false));
        },
    );
    scaling::check("eval3 of an expression and a diagram, by depth", n, |m| {
        assert_eq!(ors[&m].eval3(&|_| None), None);
        assert_eq!(meets[&m].eval3(&|_| None), None);
    });
    scaling::check(
        "the atoms of an expression and a diagram, by depth",
        n,
        |m| {
            assert_eq!(ors[&m].distinct_atoms().len(), m);
            assert_eq!(meets[&m].distinct_atoms().len(), m);
        },
    );
    scaling::check("the union's rows, by depth", n, |m| {
        assert_eq!(ors[&m].union_rows().map(|r| r.len()), Some(m));
    });
    scaling::check("the forced atoms of an expression, by depth", n, |m| {
        assert_eq!(ors[&m].forced(), (Vec::new(), Vec::new()));
    });
    scaling::check(
        "restricting an expression and a diagram, by depth",
        n,
        |m| {
            assert_eq!(ors[&m].restrict(&|_| Some(false)), Part::leaf(false));
            assert_eq!(meets[&m].restrict(&|_| None), meets[&m]);
        },
    );
    scaling::check("settling on one pin, by depth", n, |m| {
        assert_eq!(pins[&m].settle().distinct_atoms().len(), 2 * (m - 1));
    });
}

#[test]
fn the_connectives_on_parts_scale_by_depth() {
    // Small instances: `the_connectives_on_parts_hold_at_small_depths`.
    // Inputs Θ(m) deep, built before any run is timed; each connective meets each node or
    // expression a constant number of times.
    let n = 1 << 13;
    let meets = scaling::inputs(n, |m| {
        let base = 100 * m as u64;
        (meet(base, m), meet_but_last(base, m))
    });
    // A union keeps the complements it makes with the expressions, so each run of it takes
    // chains of its own, on atoms of their own.
    let (small, large) = scaling::Meter::new().runs();
    type Pairs = std::sync::Mutex<Vec<(Part<Row>, Part<Row>)>>;
    let chains: BTreeMap<usize, Pairs> = [(n, small), (scaling::FACTOR * n, large)]
        .map(|(m, runs)| {
            let pairs = (0..runs as u64)
                .map(|i| {
                    let base = (1000 + 10 * i) * m as u64;
                    (
                        choices(base, base + 2 * m as u64, m),
                        choices(base, base + 4 * m as u64, m),
                    )
                })
                .collect();
            (m, std::sync::Mutex::new(pairs))
        })
        .into();
    scaling::check("the meet of two lists, by depth", n, |m| {
        let (a, b) = &meets[&m];
        assert_eq!(a.zip_chain(b, Op::And), Some(Bdd::Leaf(false)));
    });
    // The complement flips the value of the first block and allocates nothing.
    scaling::check_instructions_only("the complement of a list, by depth", n, 1, |m| {
        assert!(meets[&m].0.not() != meets[&m].0);
    });
    scaling::check("the union of two chains of choices, by depth", n, |m| {
        let (p, q) = chains[&m]
            .lock()
            .expect("the chains of a size")
            .pop()
            .expect("a pair of chains per run");
        assert!(p.zip(&q, Op::Or) != p);
    });
}

#[test]
fn restricting_lists_that_share_a_tail_scales() {
    // Small instances: `restricting_with_a_shared_memo_gives_the_lists_restricted_alone`.
    // Item CHAIN-restrict-memo: `m` lists, each a block of its own before one tail of `m`
    // blocks, restricted on an atom of the tail's last block with one memo. Memoized by
    // list, each walked and rebuilt the whole tail again, `O(m²)` in all; memoized by cell,
    // the cells of the tail are restricted once.
    let n = 1 << 11;
    // Each list rebuilds the tail's right spine where its last block shrinks, so the work
    // follows that spine; it is summed over the tails of `SHAPES` offsets of the atoms.
    let lists = scaling::inputs(n, |m| {
        (0..SHAPES)
            .map(|j| {
                let o = j * SHAPE_STRIDE;
                let tail = blocks(o + 8000, m);
                let Bdd::List(_, v) = &tail else {
                    unreachable!("a list of blocks has a cell")
                };
                let heads: Vec<Bdd<Row>> = (0..m as u64)
                    .map(|i| {
                        let head = (!*v, Some(pair_block(o + 30000 + 2 * i)));
                        Bdd::assemble(vec![head], &tail)
                    })
                    .collect();
                (atom(o + 8000 + 2 * (m as u64 - 1)), heads)
            })
            .collect::<Vec<_>>()
    });
    scaling::check("lists sharing a tail of m blocks, restricted", n, |m| {
        for (last, heads) in &lists[&m] {
            let fix = |a: &Row| (a == last).then_some(false);
            let mut memo = list::Memo::default();
            for l in heads {
                assert_ne!(l.restrict(&fix, &mut memo).id(), l.id());
            }
        }
    });
}

#[test]
fn a_long_meet_joined_to_short_meets_scales() {
    // Small instances: `a_long_meet_joined_to_short_meets_is_kept_as_an_expression`.
    // Item CHOICE-both-chains: a meet of `m` literals joined under `|` to `m` meets of two,
    // half of them with the complement of one of its literals, each a choice then. Listing
    // both chains at each join took `O(m)` a join; the longer is now only looked up.
    let n = 1 << 14;
    let parts = scaling::inputs(n, |m| {
        let long = Part::Bdd(meet(40000, m));
        let short: Vec<Part<Row>> = (0..m as u64)
            .map(|i| match i % 2 {
                0 => Part::Bdd(meet(50000 + 2 * i, 2)),
                _ => Part::Bdd(meet(50000 + 2 * i, 1).and_literal((atom(40000 + i), false))),
            })
            .collect();
        (long, short)
    });
    scaling::check("a meet of m literals joined to m meets of two", n, |m| {
        let (long, short) = &parts[&m];
        for s in short {
            assert!(matches!(long.zip(s, Op::Or), Part::Expr(_)));
        }
    });
}

/// How deep the chains of tied digests go: the order reads them that many levels down. It was
/// a recursion, which overflowed a 2 MiB stack at 5,761 levels in a debug build (measured on
/// e3795900d, before SHORT-stack-l01_22); it is a loop with a stack of its own, here half as
/// deep again.
const TIED_DEPTH: usize = 9_000;

#[test]
fn types_whose_digests_tie_at_every_depth_are_ordered_on_a_small_stack() {
    // Small instances: `types_whose_digests_tie_at_every_depth_are_ordered`. A depth that
    // overflowed a small stack (author P178).
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(|| tied_chains_are_ordered(TIED_DEPTH))
        .unwrap()
        .join()
        .unwrap();
}

/// The walks on expressions and diagrams nested this deep, on a 2 MiB stack. Of the walks the
/// test runs, the recursive ones before T2-types-rest part 3 overflowed that stack at 13,085 to
/// 32,812 levels in a debug build (measured on 8e4fdf932); half as deep again as the deepest.
const DEEP: usize = 50_000;

#[test]
fn the_walks_over_parts_nested_deep_run_on_a_small_stack() {
    // Small instances: `the_walks_over_parts_hold_at_small_depths`. Each walk was a recursion,
    // which overflowed this stack (see the negative control in STATUS.md, T2-types-rest part
    // 3); each is now a loop with a stack of its own.
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(|| the_walks_over_parts_hold(DEEP))
        .unwrap()
        .join()
        .unwrap();
}

/// How deep the lists of the depth test go: the diagrams' `apply` and `flip`, as
/// recursions, overflowed a 2 MiB stack at 13,085 and 14,647 levels in a debug build
/// (measured on faf792d10, before T2-types-rest-4), and the 8 MiB stack of a main thread at
/// 60,000. Half as deep again, so that the old code overflows here with room to spare.
const DIAGRAM_DEPTH: usize = 22_000;

/// How deep the choices of the depth test go: `Part::not` and `Part::zip`, as a mutual
/// recursion through `choice`, `choice_of`, `same_as_not` and `choose`, overflowed a 2 MiB
/// stack at 1,684 levels (measured as above), and the 8 MiB stack at 10,000; half as deep again.
const CHOICE_DEPTH: usize = 2_600;

#[test]
fn the_connectives_on_parts_nested_deep_run_on_the_default_stack() {
    // Small instances: `the_connectives_on_parts_hold_at_small_depths`. On the test thread's
    // own stack (2 MiB unless RUST_MIN_STACK says otherwise), which the depths above
    // overflowed in the old recursions.
    the_connectives_on_parts_hold(DIAGRAM_DEPTH, CHOICE_DEPTH);
}
