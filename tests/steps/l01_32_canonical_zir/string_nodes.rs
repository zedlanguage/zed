//! CANON-term-string-nodes: the kernel term serializer writes a string as a canonical tree of
//! its parse, so a string of 2^k bytes held in k nodes serializes by its nodes, and equal
//! strings serialize the same whatever their trees.

use zed_kernel::term::build::lit;
use zed_kernel::text::Text;
use zed_kernel::value::Value;
use zedc::canon::Def;

fn self_joined(k: u32) -> Text {
    let mut t = Text::from("ab");
    for _ in 0..k {
        t = Text::join(&t, &t).expect("2^31 bytes fit");
    }
    t
}

#[test]
fn a_doubled_string_constant_serializes_by_its_nodes() {
    // 2^30 bytes held in 30 nodes and one block.
    let d = Def {
        name: "big".into(),
        domain: None,
        facets: vec![],
        body: lit(Value::Str(self_joined(29))),
    };
    let none = |_: &str| None;
    let bytes = zedc::canon::serialize(&zedc::canon::canonicalize(&d), &none)
        .expect("memory for the bytes");
    assert!(
        bytes.len() < 1 << 20,
        "a string of 2^30 bytes in 30 nodes serialized to {} bytes",
        bytes.len()
    );
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
    // after another string that shares rules with it, which is then written first in each.
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
    // A string of 2^40 · 5 bytes and the same with one byte changed in each copy, or one byte
    // more; the empty string and a one-byte string.
    let doubled = |b: &str| (0..40).fold(Text::from(b), |t, _| Text::join(&t, &t).unwrap());
    let texts = [
        doubled("abcab"),
        doubled("abcac"),
        Text::join(&doubled("abcab"), &Text::from("a")).unwrap(),
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
    // A string of 5 · 2^40 bytes is written in a few hundred bytes.
    assert!(forms[0].len() < 4096, "{} bytes", forms[0].len());
}
