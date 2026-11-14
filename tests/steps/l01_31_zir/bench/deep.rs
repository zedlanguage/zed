//! Graphs, values, patterns and types nested far deeper than a plain recursion fits on a thread
//! of the default 2 MiB stack (author P178: an unusual size is a benchmark). Each pass over a
//! graph keeps its own stack on the heap; a plain recursion takes at least 112 bytes a level
//! (measured at opt-level 2), so 20,000 levels, 2.2 MB, would overflow that stack. The same
//! forms are checked at small depths in `scaling.rs`.

use zed_tests::deep::on_small_stack;
use zedc::zir::validate::validate;
use zedc::zir::{Op, Src, binary, text};

use super::super::scaling::{deep_type_text, holding, nested_ifs};

#[test]
fn a_graph_nested_20000_deep_is_checked_compared_and_freed_on_a_2_mib_stack() {
    on_small_stack(|| {
        let g = nested_ifs(20_000);
        validate(&g).unwrap();
        assert_eq!(g, nested_ifs(20_000));
        assert_ne!(g, nested_ifs(99_999));
    });
}

#[test]
fn a_graph_nested_20000_deep_is_written_and_read_in_binary_on_a_2_mib_stack() {
    on_small_stack(|| {
        let g = nested_ifs(20_000);
        assert_eq!(
            binary::decode(&binary::encode(&g).expect("memory for the bytes")),
            Ok(g)
        );
    });
}

// Each line of the text form names its node or region by its whole path, so the text of a
// graph `d` deep holds O(d^2) bytes, 80 MB at depth 4,000. So this test runs on a 64 KiB stack,
// which a recursion of at least 112 bytes a level overflows at 585 levels, 1,000 deep: 5 MB of
// text.

#[test]
fn a_graph_nested_1000_deep_is_written_and_read_as_text_on_a_64_kib_stack() {
    std::thread::scope(|scope| {
        let thread = std::thread::Builder::new().stack_size(1 << 16);
        let run = || {
            let g = nested_ifs(1_000);
            assert_eq!(text::parse(&text::print(&g)), Ok(g));
        };
        thread.spawn_scoped(scope, run).unwrap().join().unwrap();
    });
}

// The values, patterns and types inside a graph nest as deep as the program, so the text and
// binary forms write and read them from stacks of their own (step T2-mid).

#[test]
fn a_value_20000_deep_is_written_and_read_in_binary_and_as_text_on_a_2_mib_stack() {
    on_small_stack(|| {
        let g = holding(20_000, 1);
        assert_eq!(
            binary::decode(&binary::encode(&g).expect("memory for the bytes")).as_ref(),
            Ok(&g)
        );
        let Src::Const(v) = &g.nodes[0].inputs[0] else {
            unreachable!("a constant")
        };
        assert_eq!(text::parse_value(&v.to_string()).as_ref(), Ok(v));
    });
}

// The kernel's `Pattern` drops, clones and compares by recursion, so a pattern 100,000 deep
// overflows a 2 MiB stack whatever reads it (ZED_PORT_GAPS.md); these patterns are 10,000
// deep, five times the depth at which the recursive writers and readers overflowed.

#[test]
fn a_pattern_10000_deep_is_written_and_read_in_binary_and_as_text_on_a_2_mib_stack() {
    on_small_stack(|| {
        let g = holding(1, 10_000);
        let bytes = binary::encode(&g).expect("memory for the bytes");
        assert_eq!(
            binary::encode(&binary::decode(&bytes).unwrap()).expect("memory for the bytes"),
            bytes
        );
        let Op::Match(ps) = &g.nodes[0].op else {
            unreachable!("a match")
        };
        let s = text::pattern(&ps[0]);
        assert_eq!(text::pattern(&text::parse_pattern(&s).unwrap()), s);
    });
}

#[test]
fn a_type_20000_deep_is_read_as_text_on_a_2_mib_stack() {
    // The kernel's `Type` drops its parts by recursion (ZED_PORT_GAPS.md), so a type this deep
    // overflows when dropped, whatever the parser does; the test keeps it.
    on_small_stack(|| {
        std::mem::forget(text::parse_type(&deep_type_text(20_000)).unwrap());
    });
}

// `Debug` writes a region from a stack of its own too, so an assertion that fails on a deep graph
// can print it (step T2-mid).

#[test]
fn a_graph_nested_20000_deep_is_printed_for_debugging_on_a_2_mib_stack() {
    on_small_stack(|| {
        let text = format!("{:?}", nested_ifs(20_000));
        assert_eq!(text.matches("Node { op: If").count(), 20_000);
    });
}
