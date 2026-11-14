//! Nested `if`s (an `if` whose `then` region holds the next `if`, as a chain of `else if`
//! branches lowers), and values, patterns and types inside a graph, checked, compared, written
//! and read back at small depths. The same forms far deeper than a plain recursion fits on a
//! 2 MiB stack are in `bench/deep.rs`, and their times in `bench/scaling.rs`.

use std::sync::Arc;

use zed_kernel::Value;
use zed_kernel::term::Pattern;
use zed_kernel::types::Type;
use zedc::zir::validate::validate;
use zedc::zir::{Edge, Node, Op, Region, RegionKind, Src, binary, text};

pub(crate) use zed_tests::step_helpers::l01_31_zir::nested_ifs;

#[test]
fn an_error_deep_in_a_graph_is_named_by_its_path() {
    let mut g = nested_ifs(3);
    let then = Arc::get_mut(&mut g.nodes[0].regions[0]).expect("the graph is not shared");
    let inner = Arc::get_mut(&mut then.nodes[0].regions[0]).expect("not shared");
    inner.results = vec![Src::Arg(0)];
    assert_eq!(
        validate(&g).unwrap_err(),
        "r.0/0.0/0: result 0: r.0/0.0/0^0: the region has 0 arguments, numbered from 0"
    );
}

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

/// `(tuple (tuple … int …) int)`, `d` deep.
pub(super) fn deep_type_text(d: usize) -> String {
    let mut s = "(tuple ".repeat(d);
    s.push_str("int");
    s.push_str(&" int)".repeat(d));
    s
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
