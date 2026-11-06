//! Graphs nested 100,000 deep: an `if` whose `then` region holds the next `if`, as a chain of
//! `else if` branches lowers. Each pass over the graph keeps its own stack on the heap, so such
//! a graph is checked, compared, written and read back on a thread of the default 2 MiB stack,
//! in time linear in its depth.

use std::sync::Arc;

use zed_kernel::Value;
use zed_kernel::term::Pattern;
use zed_kernel::types::Type;
use zed_tests::deep::on_small_stack;
use zed_tests::scaling::check_order;
use zedc::zir::{Edge, Node, Op, Region, RegionKind, Src, binary, text, validate};

/// `if true then (if true then ... 0 else 0) else 0`, `depth` branches deep, built from the
/// bottom up.
pub(crate) fn nested_ifs(depth: usize) -> Region {
    let region = |kind, nodes, results| Region {
        kind,
        args: Vec::new(),
        nodes,
        results,
    };
    let zero = || {
        region(
            RegionKind::Match,
            Vec::new(),
            vec![Src::Const(Value::Int(0))],
        )
    };
    let branch = |then: Region| Node {
        op: Op::If,
        inputs: vec![Src::Const(Value::Bool(true))],
        outputs: vec![Edge::value(Type::int())],
        regions: vec![Arc::new(then), Arc::new(zero())],
    };
    let mut arm = zero();
    for _ in 1..depth {
        arm = region(RegionKind::Match, vec![branch(arm)], vec![Src::Out(0, 0)]);
    }
    region(
        RegionKind::Function,
        vec![branch(arm)],
        vec![Src::Out(0, 0)],
    )
}

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
fn checking_a_deep_graph_is_linear_in_its_depth() {
    on_small_stack(|| {
        let (small, large) = (nested_ifs(12_500), nested_ifs(100_000));
        let twins = (nested_ifs(12_500), nested_ifs(100_000));
        check_order("checking nested `if` regions", 12_500, 1, |k| {
            validate(if k == 12_500 { &small } else { &large }).unwrap();
        });
        check_order("comparing nested `if` regions", 12_500, 1, |k| {
            let (g, h) = if k == 12_500 {
                (&small, &twins.0)
            } else {
                (&large, &twins.1)
            };
            assert!(g == h);
        });
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

#[test]
fn writing_and_reading_a_deep_graph_in_binary_is_linear_in_its_depth() {
    on_small_stack(|| {
        let (small, large) = (nested_ifs(12_500), nested_ifs(100_000));
        check_order("writing nested `if` regions in binary", 12_500, 1, |k| {
            binary::encode(if k == 12_500 { &small } else { &large })
                .expect("memory for the bytes");
        });
        let (small, large) = (
            binary::encode(&small).expect("memory for the bytes"),
            binary::encode(&large).expect("memory for the bytes"),
        );
        check_order("reading nested `if` regions in binary", 12_500, 1, |k| {
            binary::decode(if k == 12_500 { &small } else { &large }).unwrap();
        });
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

#[test]
fn writing_and_reading_a_deep_graph_as_text_is_linear_in_the_text() {
    on_small_stack(|| {
        let (small, large) = (nested_ifs(250), nested_ifs(2_000));
        // Power 2: the text grows as the square of the depth.
        check_order("writing nested `if` regions as text", 250, 2, |k| {
            text::print(if k == 250 { &small } else { &large });
        });
        let (small, large) = (text::print(&small), text::print(&large));
        check_order("reading nested `if` regions as text", 250, 2, |k| {
            text::parse(if k == 250 { &small } else { &large }).unwrap();
        });
    });
}

// The values, patterns and types inside a graph nest as deep as the program, so the text and
// binary forms write and read them from stacks of their own (step T2-mid).

/// A value `d` deep whose levels take turns being a pair, a named atom, a positional atom and
/// a path.
fn deep_value(d: usize) -> Value {
    (0..d).fold(Value::Int(0), |v, i| match i % 4 {
        0 => Value::tuple(vec![v, Value::Int(1)]),
        1 => Value::atom_named("n", vec![("a".into(), Value::Int(2)), ("b".into(), v)]).unwrap(),
        2 => Value::atom_with("p", vec![v]),
        _ => Value::path(vec![Value::Int(3), v]),
    })
}

/// A pattern `d` deep whose levels take turns being a pair, an atom and a fields pattern.
fn deep_pattern(d: usize) -> Pattern {
    (0..d).fold(Pattern::Bind("x".into()), |p, i| match i % 3 {
        0 => Pattern::Tuple(vec![p, Pattern::Wild]),
        1 => Pattern::Atom("a".into(), vec![p]),
        _ => Pattern::Fields("f".into(), vec![("k".into(), p)]),
    })
}

/// A graph of one node, a `match` on a constant: the value `value` deep and the pattern
/// `pattern` deep.
fn holding(value: usize, pattern: usize) -> Region {
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
fn deep_type_text(d: usize) -> String {
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

#[test]
fn writing_and_reading_deep_values_patterns_and_types_is_linear_in_their_depth() {
    on_small_stack(|| {
        let (small, large) = (holding(12_500, 1_000), holding(100_000, 8_000));
        let pick = |k: usize| if k == 12_500 { &small } else { &large };
        check_order(
            "writing deep values and patterns in binary",
            12_500,
            1,
            |k| {
                binary::encode(pick(k)).expect("memory for the bytes");
            },
        );
        let (bs, bl) = (
            binary::encode(&small).expect("memory for the bytes"),
            binary::encode(&large).expect("memory for the bytes"),
        );
        check_order(
            "reading deep values and patterns in binary",
            12_500,
            1,
            |k| {
                binary::decode(if k == 12_500 { &bs } else { &bl }).unwrap();
            },
        );
        let text_of = |g: &Region| {
            let Src::Const(v) = &g.nodes[0].inputs[0] else {
                unreachable!("a constant")
            };
            v.to_string()
        };
        let (vs, vl) = (text_of(&small), text_of(&large));
        check_order("reading a deep value as text", 12_500, 1, |k| {
            text::parse_value(if k == 12_500 { &vs } else { &vl }).unwrap();
        });
        let pattern_of = |g: &Region| {
            let Op::Match(ps) = &g.nodes[0].op else {
                unreachable!("a match")
            };
            text::pattern(&ps[0])
        };
        check_order("writing a deep pattern as text", 1_000, 1, |k| {
            pattern_of(if k == 1_000 { &small } else { &large });
        });
        let (ps, pl) = (pattern_of(&small), pattern_of(&large));
        check_order("reading a deep pattern as text", 1_000, 1, |k| {
            text::parse_pattern(if k == 1_000 { &ps } else { &pl }).unwrap();
        });
        let (ts, tl) = (deep_type_text(250), deep_type_text(2_000));
        check_order("reading a deep type as text", 250, 1, |k| {
            text::parse_type(if k == 250 { &ts } else { &tl }).unwrap();
        });
    });
}

/// A tuple of `n` generated binders, the elaborator's `$k` and the canonical level `k` in turn,
/// as a wave of `n` values and its canonical form bind them.
fn generated_binders(n: usize) -> Pattern {
    let bind = |k: usize| match k % 2 {
        0 => Pattern::Bind(format!("${k}").into()),
        _ => Pattern::Bind(zedc::canon::binders::level_name(k)),
    };
    Pattern::Tuple((0..n).map(bind).collect())
}

#[test]
fn writing_and_reading_generated_binders_is_linear_in_their_number() {
    let (small, large) = (generated_binders(12_500), generated_binders(100_000));
    let pick = |k: usize| if k == 12_500 { &small } else { &large };
    check_order("writing generated binders as text", 12_500, 1, |k| {
        text::pattern(pick(k));
    });
    let (ts, tl) = (text::pattern(&small), text::pattern(&large));
    assert_eq!(text::parse_pattern(&ts).as_ref(), Ok(&small));
    check_order("reading generated binders as text", 12_500, 1, |k| {
        text::parse_pattern(if k == 12_500 { &ts } else { &tl }).unwrap();
    });
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

#[test]
fn printing_a_deep_graph_for_debugging_is_linear_in_its_depth() {
    on_small_stack(|| {
        let (small, large) = (nested_ifs(12_500), nested_ifs(100_000));
        check_order(
            "printing nested `if` regions for debugging",
            12_500,
            1,
            |k| {
                let _ = format!("{:?}", if k == 12_500 { &small } else { &large });
            },
        );
    });
}

/// A family literal of `n` entries `{k -> k, ...}`, its keys written from the largest down, and
/// with the key 0 written a second time when `repeat` is set.
fn wide_family(n: usize, repeat: bool) -> String {
    let mut entries: Vec<String> = (0..n).rev().map(|k| format!("{k} -> {k}")).collect();
    if repeat {
        entries.push("0 -> 1".into());
    }
    format!("{{{}}}", entries.join(", "))
}

#[test]
fn reading_a_wide_family_and_refusing_a_repeated_key_is_n_log_n_in_its_entries() {
    let (n, large) = (2_000, 16_000);
    let pick = |k: usize, a, b| if k == n { a } else { b };
    let (ok_small, ok_large) = (wide_family(n, false), wide_family(large, false));
    let (bad_small, bad_large) = (wide_family(n, true), wide_family(large, true));
    assert_eq!(
        text::parse_value(&bad_small),
        Err(format!(
            "column {}: the family writes the key 0 twice",
            bad_small.len() + 1
        ))
    );
    check_order("reading a family of n entries as text", n, 1, |k| {
        text::parse_value(pick(k, &ok_small, &ok_large)).unwrap();
    });
    check_order(
        "refusing a family of n entries that repeats a key",
        n,
        1,
        |k| {
            text::parse_value(pick(k, &bad_small, &bad_large)).unwrap_err();
        },
    );
    let graph = |family: &str| {
        let src = format!("zir 1\nr region function ()\nr results ({family})\n");
        binary::encode(&text::parse(&src).expect("a graph")).expect("memory for the bytes")
    };
    let (bin_small, bin_large) = (graph(&ok_small), graph(&ok_large));
    check_order("reading a family of n entries in binary", n, 1, |k| {
        binary::decode(if k == n { &bin_small } else { &bin_large }).unwrap();
    });
}
