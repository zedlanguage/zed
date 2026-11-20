//! The benchmarks of [`Text::split_chars`] and [`Text::slice_chars`], run by
//! `tools/run_tests.sh --bench`. Their small instances are the correctness tests of
//! `text::split` (`every_piece_of_a_chain_reads_as_the_str_piece` and
//! `a_piece_shares_the_blocks_inside_it`).

use super::super::tests::{PIECE, chain};
use super::*;

#[test]
fn a_piece_of_a_text_of_n_blocks_costs_log_n() {
    // 2,000 pieces, each across three blocks, of a chain of n blocks of 256 code points of one
    // to four bytes: each piece builds O(log n) nodes on a chain (the module comment), O(log² n)
    // at worst, and scans and copies the two blocks its cuts fall in, a constant. Work of order
    // `log n` per piece at a fixed count of pieces, so power 0: 8n may do 1.3125 times the work
    // of n. The texts are built before the runs are timed.
    let texts = crate::scaling::inputs(4096, |n| chain(n, true).0);
    crate::scaling::check_order("2,000 pieces of a text of n blocks", 4096, 0, |n| {
        let t = &texts[&n];
        let chars = t.char_count();
        for q in 0..2000 {
            let a = q * 7919 % (chars - 3 * PIECE);
            let piece = t.slice_chars(a + 5, a + 3 * PIECE - 5);
            assert_eq!(piece.char_count(), 3 * PIECE - 10);
        }
    });
}

#[test]
fn a_piece_of_one_block_of_n_bytes_costs_n() {
    // A literal is one block whatever its length, so a piece of it scans the block to the cut
    // and copies the two pieces: order n, so 8n may do 10.5 times the work of n.
    let texts = crate::scaling::inputs(1 << 20, |n| Text::from("é".repeat(n / 2)));
    crate::scaling::check("a piece of one block of n bytes", 1 << 20, |n| {
        let t = &texts[&n];
        let (l, r) = t.split_chars(n / 4);
        assert_eq!((l.len(), r.len()), (n / 2, n / 2));
    });
}
