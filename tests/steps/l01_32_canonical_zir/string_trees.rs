//! ZIR-string-tree-address: two graphs equal but for the tree that holds one string constant.
//! Folding `++` of constants joins texts ([`Text::join`]), which shares both parts, so
//! `("a" * 300 ++ "b" * 300) ++ "c" * 300` and `"a" * 300 ++ ("b" * 300 ++ "c" * 300)` give
//! one string held in two trees (pieces longer than `zed_kernel::text::LEAF`, 256 bytes, so no
//! join copies them into one block), and a literal of the same 900 bytes holds it in a third,
//! one block. L1.32 gives a graph's address over the binary form of its normal form, and the
//! binary form (L1.31) writes a value by its structure: a string's structure is its text, not
//! the tree it is held in, so the three must share the ZIR address, as they share the kernel
//! address that import pins and the program's address hash (CANON-term-string-nodes).

use zed_kernel::Term;
use zed_kernel::term::build::{lam, lit, prim, var};
use zed_kernel::term::{Pattern, Prim};
use zed_kernel::text::Text;
use zed_kernel::value::{Family, Value};
use zedc::address::ContentAddress;
use zedc::canon::Def;

/// `c` repeated 300 times.
fn run(c: char) -> Text {
    Text::from(c.to_string().repeat(300))
}

fn join(a: &Text, b: &Text) -> Text {
    Text::join(a, b).expect("short")
}

/// The one text of 900 bytes in three trees: joined from the left, from the right, and read
/// whole as one block.
fn three_trees() -> [Text; 3] {
    let (a, b, c) = (run('a'), run('b'), run('c'));
    let flat = Text::from(format!(
        "{}{}{}",
        "a".repeat(300),
        "b".repeat(300),
        "c".repeat(300)
    ));
    [join(&join(&a, &b), &c), join(&a, &join(&b, &c)), flat]
}

fn zir(t: &Term) -> ContentAddress {
    let g = zedc::zir::lower::lower(t).expect("lowered");
    zedc::zir::canon::address(&g).expect("memory for the address")
}

fn kernel(t: &Term) -> ContentAddress {
    let d = Def {
        name: "s".into(),
        domain: None,
        facets: vec![],
        body: t.clone(),
    };
    zedc::canon::address(&d, &|_| None).expect("memory for the address")
}

/// The trees differ, the texts are equal, and so are the ZIR address and the kernel address
/// of a graph holding each, alone or beside another string.
#[test]
fn equal_strings_in_different_trees_share_the_zir_address() {
    let trees = three_trees();
    for t in &trees[1..] {
        assert_eq!(t, &trees[0], "the texts are equal");
        assert_ne!(t.node_id(), trees[0].node_id(), "held in different trees");
    }
    let other = Value::str("other");
    let terms = |t: &Text| {
        [
            lit(Value::Str(t.clone())),
            prim(
                Prim::Tuple,
                vec![lit(other.clone()), lit(Value::Str(t.clone()))],
            ),
        ]
    };
    let want = terms(&trees[0]);
    for (k, t) in trees.iter().enumerate().skip(1) {
        for (have, want) in terms(t).iter().zip(&want) {
            assert_eq!(kernel(have), kernel(want), "kernel address, tree {k}");
            assert_eq!(zir(have), zir(want), "ZIR address, tree {k}: {have}");
        }
    }
}

/// The string inside a tuple, a keypath, an atom's payload, a family's key and value, and a
/// match arm's literal: each graph's ZIR address is the same for the three trees.
#[test]
fn a_string_nested_in_a_value_or_a_pattern_shares_the_zir_address() {
    let trees = three_trees();
    let holders = |t: &Text| {
        let s = Value::Str(t.clone());
        [
            lit(Value::tuple(vec![Value::Int(1), s.clone()])),
            lit(Value::path(vec![s.clone()])),
            lit(Value::atom_with(
                "tagged",
                vec![Value::tuple(vec![s.clone()])],
            )),
            lit(Family::of([(s.clone(), Value::Int(1))])),
            lit(Family::of([(Value::Int(1), s.clone())])),
            lam(
                &["x"],
                Term::Match(
                    var("x").into(),
                    vec![(Pattern::Lit(s.clone()), lit(1)), (Pattern::Wild, lit(0))],
                ),
            ),
        ]
    };
    let want: Vec<_> = holders(&trees[0]).iter().map(zir).collect();
    for (k, t) in trees.iter().enumerate().skip(1) {
        for (i, (have, want)) in holders(t).iter().zip(&want).enumerate() {
            assert_eq!(&zir(have), want, "holder {i}, tree {k}: {have}");
        }
    }
}

/// Different strings, of one length and one tree shape, still get different ZIR addresses.
#[test]
fn different_strings_get_different_zir_addresses() {
    let (a, b, c) = (run('a'), run('b'), run('c'));
    let texts = [
        join(&join(&a, &b), &c),
        join(&join(&a, &c), &b),
        join(&join(&a, &b), &run('d')),
        join(&a, &b),
    ];
    let addresses: Vec<_> = texts
        .iter()
        .map(|t| zir(&lit(Value::Str(t.clone()))))
        .collect();
    for i in 0..addresses.len() {
        for j in 0..i {
            assert_ne!(addresses[i], addresses[j], "{i} and {j}");
        }
    }
}
