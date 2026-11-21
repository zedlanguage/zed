//! The benchmarks of [`Text`], run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-move-crates). Each check they make besides the ratio has a small instance
//! among the correctness tests in `text.rs`: the lengths and contents read
//! (`a_join_reads_as_its_parts_in_order`, `a_chain_of_joins_allocates_a_constant_per_join`,
//! `try_flat_reads_every_shape_of_a_text_whole`) and every compare of blocks and trees
//! (`texts_compare_as_their_strs_whatever_their_blocks`).

use super::tests::{
    PIECE, assert_balanced, bytes, chain, chain_text, depth_bound, join, leaves, long, pieces,
};
use super::*;

#[test]
fn reading_every_prefix_costs_the_text_read() {
    // A log printed in full after every line: line `i` reads `i` lines, so `n` lines
    // read `n²/2` lines in all, and each read must cost in proportion to its length
    // (COMPLEXITY.md C29). The work is of order `n²`, so 8n may do 24 × 8 times that of n.
    // Each block's bytes are counted by a loop over the block, which the compiler can do
    // many bytes at a time; counted through one iterator over the bytes of every block, the
    // run at 8000 lines took 9.8 to 13.3 s of the test's 10.1 to 13.6 s at load 21 to 27
    // (BENCH-l0139-follow-over-cap). Either reads every byte once.
    let line = long('l');
    crate::scaling::check_order("a log of n lines printed after every line", 1000, 2, |n| {
        let mut log = Text::from("");
        for i in 1..=n {
            log = join(&log, &line);
            let printed: usize = log
                .chunks()
                .map(|c| c.bytes().filter(|&b| b == b'l').count())
                .sum();
            assert_eq!(printed, PIECE * i);
        }
    });
}

#[test]
fn every_prefix_held_and_compared_costs_order_n_log_n() {
    // A log of n lines whose every prefix is kept, each compared, by `<` and by `==`, with
    // a log of the same length that differs in its first byte: each comparison stops
    // there after setting up a walk of `O(log n)`, and each prefix shares all but `O(1)`
    // nodes, amortized, with the one before (COMPLEXITY.md C29). Order `n log n`, so 8n
    // may do 24 times the work of n.
    let line = long('l');
    let first = join(&Text::from("m"), &Text::from("l".repeat(PIECE - 1)));
    crate::scaling::check("n prefixes of a log held and compared", 352_000, |n| {
        let mut held = Vec::with_capacity(n);
        let (mut log, mut differs): (Text, Text) = (Text::from(""), Text::from(""));
        for _ in 0..n {
            log = join(&log, &line);
            differs = if differs.is_empty() {
                first.clone()
            } else {
                join(&differs, &line)
            };
            assert!(log < differs && log != differs);
            held.push(log.clone());
        }
        assert_eq!(held.len(), n);
    });
}

#[test]
fn a_chain_either_way_is_built_in_order_n() {
    // The `foldl` of `++` of plan row TEXT-append-O1: order `n`, so 8n may do 24 times the
    // work of n.
    let piece = long('p');
    for left in [true, false] {
        crate::scaling::check("a chain of n joins", 640_000, |n| {
            let mut t = Text::from("");
            for _ in 0..n {
                t = if left {
                    join(&t, &piece)
                } else {
                    join(&piece, &t)
                };
            }
            assert_eq!(t.len(), PIECE * n);
        });
    }
}

#[test]
fn try_flat_of_a_join_costs_its_length() {
    // One walk over the blocks into memory asked for once: order `n` in the blocks, so 8n
    // may do 24 times the work of n. The texts are built before the runs are timed, without
    // the string `chain` writes beside them, 1.3 GB at 8n that no run reads.
    let texts = crate::scaling::inputs(256_000, |n| chain_text(n, true));
    crate::scaling::check("try_flat of a join of n blocks", 256_000, |n| {
        let flat = texts[&n].try_flat().unwrap();
        assert_eq!(flat.chars().count(), PIECE * n);
    });
}

#[test]
fn a_compare_of_two_blocks_costs_their_length() {
    // A compare of two equal blocks of n bytes reads both once: order `n`, so 8n may do 24
    // times the work of n. It allocates nothing (`a_compare_of_two_blocks_allocates_nothing`),
    // so only the work is measured.
    let texts = crate::scaling::inputs(1 << 24, |n| {
        (Text::from("q".repeat(n)), Text::from("q".repeat(n)))
    });
    crate::scaling::check_instructions_only(
        "a compare of two blocks of n bytes",
        1 << 24,
        1,
        |n| {
            let (a, b) = &texts[&n];
            for _ in 0..300 {
                assert_eq!(std::hint::black_box(a).cmp(b), Ordering::Equal);
            }
        },
    );
}

/// Two equal texts of n blocks, one a tree joined from the left and one from the right: the
/// compare reads every block once, order `n`, and allocates one stack of `O(log n)` per tree,
/// so 8n may do 24 times the work and the bytes of n.
///
/// This and [`a_compare_of_a_block_and_a_tree_costs_its_length`] were the two checks of one
/// test, which built both trees and the block in each of its three processes (the run at 8n
/// of a check is in a new process that builds the inputs again, `scaling::compare_by`): 16.1 s
/// at load 27, where the runs took 0.2 s (BENCH-l0139-follow-over-cap). Each builds what its
/// check reads.
#[test]
fn a_compare_against_a_tree_costs_its_length() {
    let texts = crate::scaling::inputs(96_000, |n| {
        let (left, s) = chain(n, true);
        (left, pieces(&s, PIECE, false))
    });
    crate::scaling::check("a compare of two trees of n blocks", 96_000, |n| {
        let (left, right) = &texts[&n];
        assert_eq!(left.cmp(right), Ordering::Equal);
    });
}

/// The same text as one block against a tree of n blocks joined from the left: the compare
/// reads every block once, order `n`, as [`a_compare_against_a_tree_costs_its_length`] says.
#[test]
fn a_compare_of_a_block_and_a_tree_costs_its_length() {
    let texts = crate::scaling::inputs(96_000, |n| {
        let (left, s) = chain(n, true);
        (left, Text::from(s))
    });
    crate::scaling::check("a compare of a block and a tree of n blocks", 96_000, |n| {
        let (left, block) = &texts[&n];
        assert_eq!(block.cmp(left), Ordering::Equal);
    });
}

/// A chain of a million blocks joined at either end stays balanced, reads whole and drops
/// without a deep recursion (COMPLEXITY.md K16, C29). Small instance:
/// `a_long_chain_either_way_is_balanced_read_and_dropped` (4096 blocks).
#[test]
fn a_chain_a_million_long_either_way_is_balanced_read_and_dropped() {
    let piece = long('z');
    let n = 1_000_000;
    // `n` blocks: at most `log2(n/2 + 1)` levels, 18.
    for left in [true, false] {
        let mut t = Text::from("");
        for _ in 0..n {
            t = if left {
                join(&t, &piece)
            } else {
                join(&piece, &t)
            };
        }
        assert_eq!((t.len(), t.char_count()), (PIECE * n, PIECE * n));
        assert!(t.depth() <= depth_bound(n), "depth {}", t.depth());
        assert_balanced(&t);
        assert_eq!(leaves(&t), n);
        assert_eq!(t.flat().len(), PIECE * n, "every piece is read");
        assert!(bytes(&t).all(|b| b == b'z'));
        drop(t);
    }
}

/// TEST-dry-shared-units: [`ident::names`] of a text of n names and numbers, one pass over its
/// bytes, O(n), and [`prose::and_list`] of n items, O(the length of the result).
#[test]
fn the_names_of_a_text_and_a_list_of_n_items_scale() {
    let texts = crate::scaling::inputs(1 << 16, |n| {
        let items: Vec<String> = (0..n).map(|i| format!("x_{i}'")).collect();
        let text: String = (0..n).map(|i| format!("f(x{i}') + 12ab - _ * ")).collect();
        (items, text)
    });
    crate::scaling::check(
        "the names of a text of n terms and a list of n items",
        1 << 16,
        |n| {
            let (items, text) = &texts[&n];
            assert_eq!(ident::names(text).count(), 2 * n);
            assert!(prose::and_list(items).len() > n);
        },
    );
}

/// TEST-dry-shared-units: n names of one base from [`ident::numbered`], each from the suffix
/// after the last, with the n odd suffixes below 2n taken: O(n) lookups, where trying from 1
/// each time would be O(n²) (its documented tradeoff).
#[test]
fn numbered_names_scale() {
    let taken = crate::scaling::inputs(1 << 14, |n| {
        (0..n)
            .map(|k| format!("t{}", 2 * k + 1))
            .collect::<std::collections::HashSet<_>>()
    });
    crate::scaling::check("n numbered names beside n taken", 1 << 14, |n| {
        let taken = &taken[&n];
        let mut from = 1;
        for _ in 0..n {
            let (k, name) = ident::numbered("t", from, |s| !taken.contains(s));
            assert!(k % 2 == 0 && name.len() > 1);
            from = k + 1;
        }
    });
}
