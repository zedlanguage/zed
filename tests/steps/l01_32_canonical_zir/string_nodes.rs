//! A string is serialized as its length and then its bytes (author answer A106, 2026-11-20),
//! whatever tree holds it, so equal strings serialize the same and different strings
//! differently. An address reads only the literals of a program's term
//! (row PROOF-address-reads-literals-only, proof in crates/zedc-zir/src/canon/serial.rs), so a
//! program that builds a string of 2^30 bytes with `++` is addressed by its text, not by the
//! string it builds.

use zed_kernel::term::build::lit;
use zed_kernel::text::Text;
use zed_kernel::value::Value;
use zedc::canon::Def;

fn self_joined(base: &str, k: u32) -> Text {
    (0..k).fold(Text::from(base), |t, _| {
        Text::join(&t, &t).expect("under 2^63 bytes")
    })
}

/// A definition `big` whose body is a string of 2^20 bytes held in 19 joins serializes as `big`
/// holding the empty string does, but for the literal: tag 3, the length as a 64-bit
/// little-endian word, then the bytes.
#[test]
fn a_doubled_string_constant_serializes_to_its_bytes() {
    // 2^20 bytes held in 19 nodes and one block.
    let t = self_joined("ab", 19);
    let bytes = serialized(&Def {
        name: "big".into(),
        domain: None,
        facets: vec![],
        body: lit(Value::Str(t)),
    });
    let mut want = vec![3];
    want.extend_from_slice(&(1u64 << 20).to_le_bytes());
    want.extend_from_slice("ab".repeat(1 << 19).as_bytes());
    assert!(bytes.ends_with(&want), "{} bytes", bytes.len());
    assert_eq!(bytes.len() - want.len(), serialized_empty().len() - 9);
}

/// The serialization of `big` holding the empty string.
fn serialized_empty() -> Vec<u8> {
    serialized(&Def {
        name: "big".into(),
        domain: None,
        facets: vec![],
        body: lit(Value::Str(Text::from(""))),
    })
}

fn holding(name: &str, strings: Vec<Text>) -> Def {
    Def {
        name: name.into(),
        domain: None,
        facets: vec![],
        body: lit(Value::Tuple(strings.into_iter().map(Value::Str).collect())),
    }
}

fn serialized(d: &Def) -> Vec<u8> {
    let none = |_: &str| None;
    zedc::canon::serialize(&zedc::canon::canonicalize(d), &none).expect("memory for the bytes")
}

/// `pieces` joined from the left, from the right, and as a balanced tree.
fn three_trees(pieces: &[&str]) -> [Text; 3] {
    let texts: Vec<Text> = pieces.iter().map(|&p| Text::from(p)).collect();
    let join = |a: &Text, b: &Text| Text::join(a, b).expect("short");
    let left = texts.iter().fold(Text::from(""), |t, p| join(&t, p));
    let right = texts.iter().rev().fold(Text::from(""), |t, p| join(p, &t));
    fn balanced(ts: &[Text]) -> Text {
        match ts {
            [] => Text::from(""),
            [t] => t.clone(),
            _ => Text::join(
                &balanced(&ts[..ts.len() / 2]),
                &balanced(&ts[ts.len() / 2..]),
            )
            .expect("short"),
        }
    }
    [left, right, balanced(&texts)]
}

#[test]
fn equal_strings_serialize_the_same_whatever_their_trees() {
    // One string read whole, joined three ways, and doubled from a shorter base; alone and
    // after another string, which is then written first in each.
    let base = "abcab";
    let flat = Text::from(base.repeat(64));
    let doubled = (0..6).fold(Text::from(base), |t, _| Text::join(&t, &t).unwrap());
    let pieces: Vec<String> = (0..64).map(|_| base.to_string()).collect();
    let pieces: Vec<&str> = pieces.iter().map(String::as_str).collect();
    let mut all = vec![flat.clone(), doubled];
    all.extend(three_trees(&pieces));
    // Pieces cut across the period, so no leaf starts where a copy of the base does.
    all.extend(three_trees(&["ab", &"cabab".repeat(63), "cab"]));
    let want_alone = serialized(&holding("s", vec![flat.clone()]));
    let other = Text::from(base.repeat(9));
    let want_after = serialized(&holding("s", vec![other.clone(), flat]));
    for t in all {
        assert_eq!(t.len(), 320);
        assert_eq!(serialized(&holding("s", vec![t.clone()])), want_alone);
        assert_eq!(
            serialized(&holding("s", vec![other.clone(), t])),
            want_after
        );
    }
}

#[test]
fn different_strings_serialize_differently() {
    // A string of 2^16 · 5 bytes and the same with one byte changed in each copy, or one byte
    // more; the empty string and two one-byte strings.
    let texts = [
        self_joined("abcab", 16),
        self_joined("abcac", 16),
        Text::join(&self_joined("abcab", 16), &Text::from("a")).unwrap(),
        Text::from(""),
        Text::from("a"),
        Text::from("b"),
    ];
    let forms: Vec<Vec<u8>> = texts
        .iter()
        .map(|t| serialized(&holding("s", vec![t.clone()])))
        .collect();
    for i in 0..forms.len() {
        for j in 0..i {
            assert_ne!(forms[i], forms[j], "{i} and {j}");
        }
    }
}

/// `main` doubling `"ab"` `k` times, `s1 = s0 ++ s0` to `s<k>`, then writing the length of the
/// last: the string it builds when run is 2^(k+1) bytes, and the term holds `"ab"` once.
pub(crate) fn doubling(k: usize) -> String {
    let mut src = String::from("main(m: MainArgs) {\n    s0 = \"ab\";\n");
    for i in 1..=k {
        src.push_str(&format!("    s{i} = s{} ++ s{};\n", i - 1, i - 1));
    }
    src.push_str(&format!("    m.stdout <- String(len(s{k}));\n}}\n"));
    src
}

/// A program that builds a string of 2^30 bytes with `++` is addressed without building it:
/// its address is taken from the term, which holds `"ab"` once, is the same each time, and
/// differs from the address of the program that doubles once more. The scaling over the
/// number of lines is
/// `bench::string_nodes::a_doubling_program_is_addressed_in_time_linear_in_its_text`.
#[test]
fn a_program_holding_a_doubled_string_is_addressed_by_its_text() {
    let p = zedc::run::load(doubling(29).as_bytes()).unwrap();
    let address = p.ports().address(p.term()).unwrap();
    assert_eq!(address, p.address().unwrap());
    let once_more = zedc::run::load(doubling(30).as_bytes()).unwrap();
    assert_ne!(address, once_more.address().unwrap());
}
