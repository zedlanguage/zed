//! The names in the binary form (of atoms, fields, ports, evidence keys and pattern binders)
//! are read by the rule the text form reads them by, the lexer's: data that holds a string
//! that is not a name where a name belongs is refused at that string's count. The binders the
//! compiler makes, the elaborator's `$1` and the canonical `\0` and a level, read back.

use std::sync::Arc;

use zed_kernel::Value;
use zed_kernel::term::{Grade, Pattern};
use zed_kernel::types::Type;
use zed_tests::scaling::check_order;
use zedc::zir::{Edge, Node, Op, Region, RegionKind, Src, binary};

/// A function of one node, `op` on the constant `input`.
fn one_node(op: Op, input: Value) -> Region {
    Region {
        kind: RegionKind::Function,
        args: Vec::new(),
        nodes: vec![Node {
            op,
            inputs: vec![Src::Const(input)],
            outputs: vec![Edge::value(Type::int())],
            regions: Vec::new(),
        }],
        results: vec![Src::Out(0, 0)],
    }
}

/// A `match` of `0` on the one pattern `p`.
fn matching(p: Pattern) -> Region {
    one_node(Op::Match(vec![p]), Value::Int(0))
}

/// A graph whose result is the constant `v`.
fn constant(v: Value) -> Region {
    Region {
        kind: RegionKind::Function,
        args: Vec::new(),
        nodes: Vec::new(),
        results: vec![Src::Const(v)],
    }
}

/// The byte at which `bytes` first writes the string `s` after the magic and the version: its
/// count. The reader refuses the first string that is not a name, and each case holds one.
fn at(bytes: &[u8], s: &str) -> usize {
    let want = [&(s.len() as u64).to_le_bytes()[..], s.as_bytes()].concat();
    8 + bytes[8..]
        .windows(want.len())
        .position(|w| w == want)
        .expect("the string is written")
}

const STARTS: &str = ": a name starts with a letter or `_`";
const UNDERSCORE: &str = ": a name that starts with `_` has a letter, a digit or `_` next";

#[test]
fn a_string_that_is_not_a_name_is_refused_where_a_name_belongs() {
    let bind = |x: &str| matching(Pattern::Bind(x.into()));
    let fold = |k: &str| Op::Fold {
        depth: 0,
        identity: false,
        ev: [(Arc::from(k), Grade::Proved)].into_iter().collect(),
    };
    // Each case: what is wrong, the graph, the string that is not a name, and why not.
    let cases: Vec<(&str, Region, &str, &str)> = vec![
        (
            "an atom's name",
            constant(Value::atom("1st")),
            "1st",
            STARTS,
        ),
        (
            "an atom's field",
            constant(Value::atom_named("e", vec![("a b".into(), Value::Int(1))]).unwrap()),
            "a b",
            "",
        ),
        (
            "a port read",
            one_node(Op::Read("std-in".into()), Value::Int(0)),
            "std-in",
            "",
        ),
        (
            "a port pushed",
            one_node(Op::Push("-out".into()), Value::Int(0)),
            "-out",
            STARTS,
        ),
        (
            "an evidence key",
            one_node(fold("x.y"), Value::Int(0)),
            "x.y",
            "",
        ),
        ("a binder", bind("9lives"), "9lives", STARTS),
        ("the wildcard as a binder", bind("_"), "_", UNDERSCORE),
        ("a binder `$` with no number", bind("$"), "$", STARTS),
        (
            "a made binder with a name after `$`",
            bind("$x"),
            "$x",
            STARTS,
        ),
        (
            "a made binder with a leading zero",
            bind("$01"),
            "$01",
            STARTS,
        ),
        ("a canonical binder with no level", bind("\0"), "\0", STARTS),
        (
            "a canonical binder's level signed",
            bind("\0+1"),
            "\0+1",
            STARTS,
        ),
        (
            "an atom pattern's name",
            matching(Pattern::Atom("#".into(), Vec::new())),
            "#",
            STARTS,
        ),
        (
            "a fields pattern's name",
            matching(Pattern::Fields("-".into(), Vec::new())),
            "-",
            STARTS,
        ),
        (
            "a fields pattern's field",
            matching(Pattern::Fields(
                "p".into(),
                vec![("x:".into(), Pattern::Wild)],
            )),
            "x:",
            "",
        ),
    ];
    for (what, g, name, why) in cases {
        let bytes = binary::encode(&g).expect("memory for the bytes");
        let want = format!("byte {}: `{name}` is not a name{why}", at(&bytes, name));
        assert_eq!(binary::decode(&bytes), Err(want), "{what}");
    }
}

#[test]
fn names_by_the_lexers_rule_and_the_binders_the_compiler_makes_read_back() {
    let fold = Op::Fold {
        depth: 0,
        identity: false,
        ev: [(Arc::from("assoc"), Grade::Proved)].into_iter().collect(),
    };
    let fields = Value::atom_named("größe", vec![("_a".into(), Value::Int(1))]).unwrap();
    let pattern = Pattern::Tuple(vec![
        Pattern::Bind("x'".into()),
        Pattern::Bind("$1".into()),
        Pattern::Bind("$10".into()),
        Pattern::Bind("\x000".into()),
        Pattern::Bind("\x0012".into()),
        Pattern::Fields("面積".into(), vec![("x_1".into(), Pattern::Wild)]),
    ]);
    let graphs = [
        constant(fields),
        one_node(Op::Read("stdin".into()), Value::Int(0)),
        one_node(Op::Push("out".into()), Value::Int(0)),
        one_node(fold, Value::Int(0)),
        matching(pattern),
        // A string value, a catalog entry and the digits of a number are not names.
        constant(Value::str("1 not a name")),
        one_node(
            Op::Reindex(zed_kernel::term::Witness::Catalog("cat-1".into())),
            Value::Int(0),
        ),
    ];
    for g in graphs {
        assert_eq!(
            binary::decode(&binary::encode(&g).expect("memory for the bytes")).as_ref(),
            Ok(&g)
        );
    }
}

/// A graph of one `match` on a tuple of `n / 8` atoms, each with a name and a field of 8
/// bytes, and whose pattern binds one name `n` bytes long, so that the names hold about 3n
/// bytes.
fn names(n: usize) -> Region {
    let atoms = (0..n / 8)
        .map(|i| {
            Value::atom_named(
                format!("a{i:07}"),
                vec![(format!("f{i:07}").into(), Value::Int(0))],
            )
            .unwrap()
        })
        .collect();
    one_node(
        Op::Match(vec![Pattern::Bind("x".repeat(n).into())]),
        Value::tuple(atoms),
    )
}

#[test]
fn reading_names_in_binary_is_linear_in_their_bytes() {
    let (n, large) = (40_000, 320_000);
    let (small_bytes, large_bytes) = (
        binary::encode(&names(n)).expect("memory for the bytes"),
        binary::encode(&names(large)).expect("memory for the bytes"),
    );
    check_order("reading the names of a graph in binary", n, 1, |k| {
        binary::decode(if k == n { &small_bytes } else { &large_bytes }).unwrap();
    });
}
