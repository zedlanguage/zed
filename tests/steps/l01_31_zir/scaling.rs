//! Graphs nested 100,000 deep: an `if` whose `then` region holds the next `if`, as a chain of
//! `else if` branches lowers. Each pass over the graph keeps its own stack on the heap, so such
//! a graph is checked, compared, written and read back on a thread of the default 2 MiB stack,
//! in time linear in its depth, as the benchmarks in `bench/scaling.rs` hold. Here each form
//! is also written and read back at small sizes.

use std::sync::Arc;

use zed_kernel::Value;
use zed_kernel::term::Pattern;
use zed_kernel::types::Type;
use zed_tests::deep::on_small_stack;
use zedc::zir::validate::validate;
use zedc::zir::{Edge, Node, Op, Region, RegionKind, Src, binary, text};

pub(crate) use zed_tests::step_helpers::l01_31_zir::nested_ifs;

#[test]
fn a_graph_nested_100000_deep_is_checked_compared_and_freed_on_a_2_mib_stack() {
    on_small_stack(|| {
        let g = nested_ifs(100_000);
        validate(&g).unwrap();
        assert_eq!(g, nested_ifs(100_000));
        assert_ne!(g, nested_ifs(99_999));
    });
}

#[test]
fn an_error_deep_in_a_graph_is_named_by_its_path() {
    on_small_stack(|| {
        let mut g = nested_ifs(3);
        let then = Arc::get_mut(&mut g.nodes[0].regions[0]).expect("the graph is not shared");
        let inner = Arc::get_mut(&mut then.nodes[0].regions[0]).expect("not shared");
        inner.results = vec![Src::Arg(0)];
        assert_eq!(
            validate(&g).unwrap_err(),
            "r.0/0.0/0: result 0: r.0/0.0/0^0: the region has 0 arguments, numbered from 0"
        );
    });
}

#[test]
fn a_graph_nested_100000_deep_is_written_and_read_in_binary_on_a_2_mib_stack() {
    on_small_stack(|| {
        let g = nested_ifs(100_000);
        assert_eq!(
            binary::decode(&binary::encode(&g).expect("memory for the bytes")),
            Ok(g)
        );
    });
}

// Each line of the text form names its node or region by its whole path, so the text of a
// graph `d` deep holds O(d^2) bytes, 80 MB at depth 4,000; these tests go as deep as that.

#[test]
fn a_graph_nested_4000_deep_is_written_and_read_as_text_on_a_2_mib_stack() {
    on_small_stack(|| {
        let g = nested_ifs(4_000);
        assert_eq!(text::parse(&text::print(&g)), Ok(g));
    });
}

// The values, patterns and types inside a graph nest as deep as the program, so the text and
// binary forms write and read them from stacks of their own (step T2-mid).

/// A value `d` deep whose levels take turns being a pair, a named atom, a positional atom and
/// a path.
pub(super) fn deep_value(d: usize) -> Value {
    (0..d).fold(Value::Int(0), |v, i| match i % 4 {
        0 => Value::tuple(vec![v, Value::Int(1)]),
        1 => Value::atom_named("n", vec![("a".into(), Value::Int(2)), ("b".into(), v)]).unwrap(),
        2 => Value::atom_with("p", vec![v]),
        _ => Value::path(vec![Value::Int(3), v]),
    })
}

/// A pattern `d` deep whose levels take turns being a pair, an atom and a fields pattern.
pub(super) fn deep_pattern(d: usize) -> Pattern {
    (0..d).fold(Pattern::Bind("x".into()), |p, i| match i % 3 {
        0 => Pattern::Tuple(vec![p, Pattern::Wild]),
        1 => Pattern::Atom("a".into(), vec![p]),
        _ => Pattern::Fields("f".into(), vec![("k".into(), p)]),
    })
}

/// A graph of one node, a `match` on a constant: the value `value` deep and the pattern
/// `pattern` deep.
pub(super) fn holding(value: usize, pattern: usize) -> Region {
    Region {
        kind: RegionKind::Function,
        args: Vec::new(),
        nodes: vec![Node {
            op: Op::Match(vec![deep_pattern(pattern)]),
            inputs: vec![Src::Const(deep_value(value))],
            outputs: vec![Edge::value(Type::int())],
            regions: Vec::new(),
        }],
        results: vec![Src::Out(0, 0)],
    }
}

#[test]
fn a_value_100000_deep_is_written_and_read_in_binary_and_as_text_on_a_2_mib_stack() {
    on_small_stack(|| {
        let g = holding(100_000, 1);
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

/// `(tuple (tuple … int …) int)`, `d` deep.
pub(super) fn deep_type_text(d: usize) -> String {
    let mut s = "(tuple ".repeat(d);
    s.push_str("int");
    s.push_str(&" int)".repeat(d));
    s
}

#[test]
fn a_type_100000_deep_is_read_as_text_on_a_2_mib_stack() {
    // The kernel's `Type` drops its parts by recursion (ZED_PORT_GAPS.md), so a type this deep
    // overflows when dropped, whatever the parser does; the test keeps it.
    on_small_stack(|| {
        std::mem::forget(text::parse_type(&deep_type_text(100_000)).unwrap());
    });
}

/// A tuple of `n` generated binders, the elaborator's `$k` and the canonical level `k` in turn,
/// as a wave of `n` values and its canonical form bind them.
pub(super) fn generated_binders(n: usize) -> Pattern {
    let bind = |k: usize| match k % 2 {
        0 => Pattern::Bind(format!("${k}").into()),
        _ => Pattern::Bind(zedc::canon::binders::level_name(k)),
    };
    Pattern::Tuple((0..n).map(bind).collect())
}

// `Debug` writes a region from a stack of its own too, so an assertion that fails on a deep graph
// can print it (step T2-mid).

#[test]
fn a_graph_prints_for_debugging_as_a_derived_debug_would() {
    let edge = format!("{:?}", Edge::value(Type::int()));
    let zero = "Region { kind: Match, args: [], nodes: [], results: [Const(Int(0))] }";
    let branch = |then: &str| {
        format!(
            "Node {{ op: If, inputs: [Const(Bool(true))], outputs: [{edge}], \
             regions: [{then}, {zero}] }}"
        )
    };
    let arm = format!(
        "Region {{ kind: Match, args: [], nodes: [{}], results: [Out(0, 0)] }}",
        branch(zero)
    );
    let expected = format!(
        "Region {{ kind: Function, args: [], nodes: [{}], results: [Out(0, 0)] }}",
        branch(&arm)
    );
    assert_eq!(format!("{:?}", nested_ifs(2)), expected);
    assert_eq!(format!("{:#?}", nested_ifs(2)), expected);
}

#[test]
fn a_graph_nested_100000_deep_is_printed_for_debugging_on_a_2_mib_stack() {
    on_small_stack(|| {
        let text = format!("{:?}", nested_ifs(100_000));
        assert_eq!(text.matches("Node { op: If").count(), 100_000);
    });
}

/// A family literal of `n` entries `{k -> k, ...}`, its keys written from the largest down, and
/// with the key 0 written a second time when `repeat` is set.
pub(super) fn wide_family(n: usize, repeat: bool) -> String {
    let mut entries: Vec<String> = (0..n).rev().map(|k| format!("{k} -> {k}")).collect();
    if repeat {
        entries.push("0 -> 1".into());
    }
    format!("{{{}}}", entries.join(", "))
}

/// The bytes of a graph whose one result is `family`.
pub(super) fn family_graph(family: &str) -> Vec<u8> {
    let src = format!("zir 1\nr region function ()\nr results ({family})\n");
    binary::encode(&text::parse(&src).expect("a graph")).expect("memory for the bytes")
}

/// A few nested `if`s are checked, compared, written and read back in binary and as text, and
/// printed for debugging; the time of each is held linear in its depth in `bench/scaling.rs`.
#[test]
fn a_few_nested_ifs_are_checked_compared_written_read_and_printed() {
    for d in [1, 2, 9] {
        let g = nested_ifs(d);
        validate(&g).unwrap();
        assert!(g == nested_ifs(d));
        let bytes = binary::encode(&g).expect("memory for the bytes");
        assert_eq!(binary::decode(&bytes).as_ref(), Ok(&g));
        assert_eq!(text::parse(&text::print(&g)).as_ref(), Ok(&g));
        assert_eq!(format!("{g:?}").matches("Node { op: If").count(), d);
    }
}

/// Shallow values, patterns and types are written and read back in binary and as text.
#[test]
fn shallow_values_patterns_and_types_are_written_and_read_back() {
    for (value, pattern) in [(1, 1), (2, 3), (9, 9)] {
        let g = holding(value, pattern);
        let bytes = binary::encode(&g).expect("memory for the bytes");
        assert_eq!(binary::decode(&bytes).as_ref(), Ok(&g));
        let Src::Const(v) = &g.nodes[0].inputs[0] else {
            unreachable!("a constant")
        };
        assert_eq!(text::parse_value(&v.to_string()).as_ref(), Ok(v));
        let Op::Match(ps) = &g.nodes[0].op else {
            unreachable!("a match")
        };
        let s = text::pattern(&ps[0]);
        assert_eq!(text::pattern(&text::parse_pattern(&s).unwrap()), s);
    }
    for d in [0, 1, 9] {
        text::parse_type(&deep_type_text(d)).unwrap();
    }
}

#[test]
fn generated_binders_are_written_and_read_back_as_text() {
    for n in [0, 1, 2, 9] {
        let p = generated_binders(n);
        assert_eq!(text::parse_pattern(&text::pattern(&p)).as_ref(), Ok(&p));
    }
}

/// A family is read as text and in binary, and one that repeats a key is refused, at its column.
#[test]
fn a_small_family_is_read_and_a_repeated_key_refused() {
    for n in [1, 2, 9] {
        text::parse_value(&wide_family(n, false)).unwrap();
        let bad = wide_family(n, true);
        assert_eq!(
            text::parse_value(&bad),
            Err(format!(
                "column {}: the family writes the key 0 twice",
                bad.len() + 1
            ))
        );
        binary::decode(&family_graph(&wide_family(n, false))).unwrap();
    }
}
