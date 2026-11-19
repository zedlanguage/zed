//! The facts a module carries, and its stripped form (DESIGN.md sec:kernel, "Facts carried,
//! and the stripped form", author decision P202; plan row STUDY-zir-facts-carried): every fact
//! kind ZIR holds survives the text and binary forms, a reader that drops one is caught, the
//! stripped form keeps none of them and runs to the same values as the full form, and the
//! re-check refuses a stripped module.

use std::sync::Arc;

use zed_kernel::term::build::{lit, prim};
use zed_kernel::term::{Grade, Prim, Shared, Term};
use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Value, World};
use zed_tests::step_helpers::l01_33_lowering::nest;
use zedc::zir::lower::{lower, raise};
use zedc::zir::strip::{STRIPPED_REFUSED, encode_stripped, print_stripped, recheck, strip};
use zedc::zir::validate::validate;
use zedc::zir::{Edge, Form, Op, Region, RegionKind, Src, binary, memory, text};

use super::round;
use super::scaling::nested_ifs;

/// A program that runs with no ports and holds every kind of fact ZIR stores: on value edges an
/// interval, a congruence, a finite set, a facet and a hint, besides the type; the evidence of
/// a `fold` and of a `fix`; and the witness of a `reindex`. The `fix` captures the set constant
/// `{1, 2}`, whose region argument has the constant's type, `_` for a set (a constant of a
/// scalar type keeps it: [`a_shared_region_is_stripped_once_for_each_set_of_constants_its_users_capture`]). Its value is `(60, {1, 2})`: the family
/// `{1 -> 5, 2 -> 10, 3 -> 15}` reindexed to the same keys with its values doubled sums to 60,
/// and the ascent from `{}` by union with `{1, 2}` settles at `{1, 2}`.
fn facts_program() -> String {
    let five = "int in [0..=10] class 1 mod 4 set {5} hint name \"five\" facet units \"cents\"";
    let pair = text::edge(&constant(&pair_value()));
    format!(
        "\
zir 1
r region function ()
r.0 prim + (2, 3) -> ({five})
r.1 lambda () -> ((-> (tuple int int) int))
r.1/0 region function (int; int)
r.1/0.0 prim + (r.1/0^0, r.1/0^1) -> (int)
r.1/0 results (r.1/0.0^0)
r.2 fam ({{1, 2, 3}}, r.0^0) -> (struct)
r.2/0 region function (int; {five})
r.2/0.0 prim * (r.2/0^0, r.2/0^1) -> (int in [5..=15] class 0 mod 5)
r.2/0 results (r.2/0.0^0)
r.3 lambda () -> (_)
r.3/0 region function (_; int)
r.3/0 results (r.3/0^0)
r.4 lambda () -> (_)
r.4/0 region function (_; int)
r.4/0.0 prim * (r.4/0^1, 2) -> (int class 0 mod 2)
r.4/0 results (r.4/0.0^0)
r.5 reindex catalog double (r.2^0, r.3^0, r.4^0) -> (struct)
r.6 fold 1 identity {{associative: axiom, commutative: proved}} (r.5^0, r.1^0, 0) -> (int in [0..] facet units \"cents\")
r.7 lambda () -> ((-> (tuple struct struct) struct))
r.7/0 region function (struct; struct)
r.7/0.0 prim union (r.7/0^0, r.7/0^1) -> (struct)
r.7/0 results (r.7/0.0^0)
r.8 fix lattice {{finiteHeight: bounded, monotone: proved}} ({{}}, r.7^0, {{1, 2}}) -> (struct)
r.8/0 region loop (struct; {pair})
r.8/0.0 prim union (r.8/0^0, r.8/0^1) -> (struct)
r.8/0 results (r.8/0.0^0)
r.9 prim tuple (r.6^0, r.8^0) -> (_)
r results (r.9^0)
"
    )
}

/// The set `{1, 2}` the `fix` of [`facts_program`] captures.
fn pair_value() -> Value {
    text::parse_value("{1, 2}").expect("a set")
}

/// The edge of the constant `v`, which a region argument it is captured into has.
fn constant(v: &Value) -> Edge {
    Edge::value(Type::lit(v).unwrap_or_else(Type::top))
}

/// Lists, in `out`, the edge `e` at `at` when it is a value edge that is not `_`.
fn edge(at: String, e: &Edge, out: &mut Vec<String>) {
    if let Edge::Value(_) = e
        && text::edge(e) != "_"
    {
        out.push(format!("{at}: {}", text::edge(e)));
    }
}

/// Every fact the graph rooted at `g` stores, each as a line naming where it is: a value edge
/// that is not `_`, written as the text form writes it, an evidence record and a witness. A
/// region shared by several nodes is listed at each.
fn facts(g: &Region) -> Vec<String> {
    let mut out = Vec::new();
    let mut todo = vec![("r".to_string(), g)];
    while let Some((path, r)) = todo.pop() {
        for (i, a) in r.args.iter().enumerate() {
            edge(format!("{path}^{i}"), a, &mut out);
        }
        for (k, n) in r.nodes.iter().enumerate() {
            let at = format!("{path}.{k}");
            for (p, o) in n.outputs.iter().enumerate() {
                edge(format!("{at}^{p}"), o, &mut out);
            }
            match &n.op {
                Op::Fold { ev, .. } | Op::Fix { ev, .. } => {
                    out.extend(ev.iter().map(|(key, g)| format!("{at}: {key} {g:?}")));
                }
                Op::Reindex(w) => out.push(format!("{at}: witness {w:?}")),
                _ => {}
            }
            for (j, sub) in n.regions.iter().enumerate() {
                todo.push((format!("{at}/{j}"), &**sub));
            }
        }
    }
    out.sort();
    out
}

/// Each fact the graph holds, as its text writes it, with the text it is written in when it is
/// gone: the negative controls of [`every_fact_survives_the_text_and_binary_forms`].
const DROPPED: [(&str, &str); 9] = [
    (" in [0..=10]", ""),
    (" class 1 mod 4", ""),
    (" set {5}", ""),
    (" hint name \"five\"", ""),
    (" in [0..] facet units \"cents\")", " in [0..])"),
    ("associative: axiom, ", ""),
    ("finiteHeight: bounded, ", ""),
    ("catalog double", "residue"),
    (" -> (int class 0 mod 2)", " -> (int)"),
];

#[test]
fn every_fact_survives_the_text_and_binary_forms() {
    let src = facts_program();
    // `round` asserts the text prints back as written, reads back in any line order, and
    // decodes from its binary form to the same graph, facts included.
    let g = round(&src);
    let all = facts(&g);
    let text_back = text::parse(&text::print(&g)).expect("a graph");
    let bytes = binary::encode(&g).expect("memory for the bytes");
    let binary_back = binary::decode(&bytes).expect("a graph");
    assert_eq!(facts(&text_back), all);
    assert_eq!(facts(&binary_back), all);
    let joined = all.join("\n");
    for kind in [
        " in [",
        " class ",
        " set {",
        " facet units",
        " hint name",
        "associative Axiom",
        "commutative Proved",
        "finiteHeight Bounded",
        "monotone Proved",
        "witness Catalog(\"double\")",
    ] {
        assert!(joined.contains(kind), "no fact `{kind}` in\n{joined}");
    }
    // Negative controls: a module with one fact stripped from its text still reads and
    // validates, and the comparison above tells it from the module with the fact, so a writer or
    // reader that lost that fact would fail this test.
    for (fact, without) in DROPPED {
        assert!(src.contains(fact), "`{fact}` is in the program");
        let lost = src.replace(fact, without);
        let h = text::parse(&lost).unwrap_or_else(|e| panic!("{e}\n{lost}"));
        validate(&h).unwrap_or_else(|e| panic!("{e}\n{lost}"));
        assert_ne!(facts(&h), all, "dropping `{fact}` is seen");
        assert!(facts(&h).len() <= all.len());
    }
}

/// The program's value as the kernel, the reference evaluator of the graph and the native back
/// end give it, each with no ports, and the native heap's counts.
fn outputs(g: &Region) -> (String, String, String) {
    let kernel = raise(g)
        .and_then(|t| {
            Evaluator::new(World::new())
                .run(&t)
                .map_err(|e| e.to_string())
        })
        .map(|v| v.to_string());
    let p = memory::plan(g, true);
    let machine =
        memory::run(g, &p, &mut Evaluator::new(World::new())).map(|(v, s)| format!("{v} {s:?}"));
    let l = zed_native::legalize(g.clone());
    let p = memory::plan(l.graph(), true);
    let native = zed_native::run(&l, &p, &mut Evaluator::new(World::new()))
        .map(|o| format!("{} {:?} {} {}", o.value, o.stats, o.table, o.cells));
    let show = |r: Result<String, String>| r.unwrap_or_else(|e| format!("error: {e}"));
    (show(kernel), show(machine), show(native))
}

/// Programs to strip: [`facts_program`], whose facts were written by hand, and kernel terms
/// lowered as the compiler lowers them, whose edges carry hints only.
fn programs() -> Vec<Region> {
    let family = text::parse_value("{1 -> 4, 2 -> 5, 3 -> 6}").expect("a family");
    let sum = Term::Fold {
        family: Shared::new(lit(family)),
        op: Shared::new(Term::PrimFn(Prim::Add)),
        identity: Some(Shared::new(lit(Value::Int(0)))),
        depth: 1,
        ev: [("associative".into(), Grade::Axiom)].into(),
    };
    let compare = prim(Prim::Gt, vec![lit("a"), lit("b")]);
    let mut out = vec![text::parse(&facts_program()).expect("a graph")];
    for t in [sum, compare, nest(6)] {
        out.push(lower(&t).unwrap_or_else(|e| panic!("{e}")));
    }
    out
}

#[test]
fn the_stripped_form_keeps_no_fact_and_runs_as_the_full_form() {
    for g in programs() {
        validate(&g).expect("a valid graph");
        let s = strip(&g);
        // The stripped form keeps a reindex's witness, which has no unknown form, and no other
        // fact.
        let witnesses: Vec<String> = facts(&g)
            .into_iter()
            .filter(|f| f.contains(": witness "))
            .collect();
        assert_eq!(facts(&s), witnesses, "{}", text::print(&s));
        validate(&s).unwrap_or_else(|e| panic!("{e}\n{}", text::print(&s)));
        // Stripping keeps every node, so the sites of an executable keep their numbers.
        assert_eq!(
            text::print(&s).lines().count(),
            text::print(&g).lines().count()
        );
        assert_eq!(strip(&s), s, "stripping twice is stripping once");
        let full = outputs(&g);
        assert!(!full.0.starts_with("error"), "{full:?}");
        assert_eq!(outputs(&s), full, "{}", text::print(&g));
        // Both serializations write the stripped form and read it back as stripped.
        let written = print_stripped(&g);
        assert!(written.starts_with("zir 1 stripped\n"), "{written}");
        assert_eq!(text::parse_form(&written), Ok((s.clone(), Form::Stripped)));
        let bytes = encode_stripped(&g).expect("memory for the bytes");
        assert_eq!(&bytes[..4], b"ZIRs");
        assert_eq!(binary::decode_form(&bytes), Ok((s.clone(), Form::Stripped)));
        let full_bytes = binary::encode(&g).expect("memory for the bytes");
        assert!(bytes.len() <= full_bytes.len());
        assert_eq!(
            binary::decode_form(&full_bytes),
            Ok((g.clone(), Form::Full))
        );
        assert_eq!(
            text::parse_form(&text::print(&g)),
            Ok((g.clone(), Form::Full))
        );
    }
    // The program of facts computes what its documentation says.
    assert_eq!(
        outputs(&programs()[0]).0,
        Value::tuple(vec![Value::Int(60), pair_value()]).to_string()
    );
}

#[test]
fn the_recheck_refuses_a_stripped_module() {
    let g = text::parse(&facts_program()).expect("a graph");
    assert_eq!(recheck(&g, Form::Full), Ok(()));
    let (s, form) = text::parse_form(&print_stripped(&g)).expect("a graph");
    assert_eq!(form, Form::Stripped);
    assert_eq!(recheck(&s, form), Err(STRIPPED_REFUSED.to_string()));
    let (s, form) =
        binary::decode_form(&encode_stripped(&g).expect("memory for the bytes")).expect("a graph");
    assert_eq!(recheck(&s, form), Err(STRIPPED_REFUSED.to_string()));
    // The readers of a full module refuse a stripped one, so none takes it for one whose facts
    // it may check.
    assert_eq!(
        text::parse(&print_stripped(&g)),
        Err(
            "the first line is `zir 1 stripped`, so the module is stripped of its facts, and \
             this reader reads a full module, whose first line is `zir 1`"
                .to_string()
        )
    );
    assert_eq!(
        binary::decode(&encode_stripped(&g).expect("memory for the bytes")),
        Err(
            "byte 0: the data starts `ZIRs`, so the module is stripped of its facts, and this \
             reader reads a full module, which starts `ZIR\\0`"
                .to_string()
        )
    );
    // A full module that fails its structure fails the re-check.
    let mut bad = g.clone();
    bad.results = vec![Src::Arg(0)];
    assert!(recheck(&bad, Form::Full).is_err());
}

/// `fam` nodes, one per input of `inputs`, each capturing it into one region they share, whose
/// argument has the type of the constant 1: a capture of the constant itself, or of `r.0`, a
/// value whose edge is written with that type too.
fn sharing(inputs: &[Src]) -> Region {
    let one = text::edge(&constant(&Value::Int(1)));
    let mut src = format!("zir 1\nr region function ()\nr.0 prim + (0, 1) -> ({one})\n");
    for k in 1..=inputs.len() {
        src.push_str(&format!(
            "r.{k} fam ({{1}}, 1) -> (struct)\nr.{k}/0 region function (int; {one})\nr.{k}/0 results (r.{k}/0^1)\n"
        ));
    }
    src.push_str("r results (r.1^0)\n");
    let mut g = text::parse(&src).unwrap_or_else(|e| panic!("{e}\n{src}"));
    let shared = g.nodes[1].regions[0].clone();
    for (n, i) in g.nodes[1..].iter_mut().zip(inputs) {
        n.inputs[1] = i.clone();
        n.regions[0] = shared.clone();
    }
    validate(&g).unwrap_or_else(|e| panic!("{e}\n{src}"));
    g
}

#[test]
fn a_shared_region_is_stripped_once_for_each_set_of_constants_its_users_capture() {
    // Both users capture the constant: the region keeps the constant's type and stays shared.
    let one = Src::Const(Value::Int(1));
    let s = strip(&sharing(&[one.clone(), one.clone()]));
    validate(&s).unwrap_or_else(|e| panic!("{e}\n{}", text::print(&s)));
    assert!(Arc::ptr_eq(&s.nodes[1].regions[0], &s.nodes[2].regions[0]));
    assert_ne!(text::edge(&s.nodes[1].regions[0].args[1]), "_");
    // One captures the constant and one the node: their edges differ once stripped, so each
    // gets its own copy, and both validate.
    let s = strip(&sharing(&[one, Src::Out(0, 0)]));
    validate(&s).unwrap_or_else(|e| panic!("{e}\n{}", text::print(&s)));
    assert!(!Arc::ptr_eq(&s.nodes[1].regions[0], &s.nodes[2].regions[0]));
    assert_eq!(text::edge(&s.nodes[2].regions[0].args[1]), "_");
}

/// `d` levels of `if`, each of whose arms is the one region of the level below, shared: its
/// tree has 2^d leaves and its graph d regions.
pub(crate) fn doubly_shared(d: usize) -> Region {
    let mut g = nested_ifs(1);
    for _ in 1..d {
        let mut arm = std::mem::replace(&mut g, nested_ifs(1));
        arm.kind = RegionKind::Match;
        let arm = Arc::new(arm);
        g.nodes[0].regions = vec![arm.clone(), arm];
    }
    g
}

#[test]
fn stripping_keeps_sharing_so_a_graph_strips_in_the_time_of_its_size() {
    // 2^64 leaves in the tree, 64 regions in the graph: only stripping each shared region once
    // ends.
    let g = doubly_shared(64);
    let s = strip(&g);
    assert!(Arc::ptr_eq(&s.nodes[0].regions[0], &s.nodes[0].regions[1]));
    // A deep graph strips on the heap, not the stack.
    let deep = nested_ifs(20_000);
    let s = zed_tests::deep::on_small_stack(|| strip(&deep));
    assert_eq!(s.nodes.len(), 1);
    zed_tests::deep::on_small_stack(|| validate(&s)).expect("a valid graph");
}
