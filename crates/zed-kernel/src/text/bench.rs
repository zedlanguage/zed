//! The benchmarks of [`Text`], run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-move-crates). Each check they make besides the ratio has a small instance
//! among the correctness tests in `text.rs`: the lengths and contents read
//! (`a_join_reads_as_its_parts_in_order`, `a_chain_of_joins_allocates_a_constant_per_join`,
//! `try_flat_reads_every_shape_of_a_text_whole`) and every compare of blocks and trees
//! (`texts_compare_as_their_strs_whatever_their_blocks`).

use super::tests::{PIECE, assert_balanced, bytes, chain, depth_bound, join, leaves, long, pieces};
use super::*;

#[test]
fn reading_every_prefix_costs_the_text_read() {
    // A log printed in full after every line: line `i` reads `i` lines, so `n` lines
    // read `n²/2` lines in all, and each read must cost in proportion to its length
    // (COMPLEXITY.md C29). The work is of order `n²`, so 8n may do 24 × 8 times that of n.
    let line = long('l');
    crate::scaling::check_order("a log of n lines printed after every line", 1000, 2, |n| {
        let mut log = Text::from("");
        for i in 1..=n {
            log = join(&log, &line);
            let printed = bytes(&log).filter(|&b| b == b'l').count();
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

/// A text of `n` pieces, each a different character, joined one at a time at the end

#[test]
fn try_flat_of_a_join_costs_its_length() {
    // One walk over the blocks into memory asked for once: order `n` in the blocks, so 8n
    // may do 24 times the work of n. The texts are built before the runs are timed.
    let texts = crate::scaling::inputs(256_000, |n| chain(n, true).0);
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

#[test]
fn a_compare_against_a_tree_costs_its_length() {
    // Two equal texts of n blocks, one a tree joined from the left and one from the right,
    // and the same text as one block against the tree: each compare reads every block
    // once, order `n`, and allocates one stack of `O(log n)` per tree, so 8n may do 24
    // times the work and the bytes of n.
    let texts = crate::scaling::inputs(96_000, |n| {
        let (left, s) = chain(n, true);
        (left, pieces(&s, PIECE, false), Text::from(s))
    });
    crate::scaling::check("a compare of two trees of n blocks", 96_000, |n| {
        let (left, right, _) = &texts[&n];
        assert_eq!(left.cmp(right), Ordering::Equal);
    });
    crate::scaling::check("a compare of a block and a tree of n blocks", 96_000, |n| {
        let (left, _, block) = &texts[&n];
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
