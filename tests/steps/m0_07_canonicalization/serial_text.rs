//! Row SPEC-m07-string-serial: the address step M0.7's text defines, computed here by a
//! serializer of its own that follows the paragraph word for word, against the
//! implementation's address.
//!
//! M0.7: "The serialization gives every node a tag byte and its fields in order, lengths and
//! integers as 64-bit little-endian words and strings as their length then UTF-8, [...] any
//! other free variable by its name. A kernel term's address is BLAKE3-256 over `zed-canon` and
//! a NUL byte, the 32-bit little-endian rule-set version, then the serialization."
//!
//! DESIGN does not say which tag byte each node gets, nor the order of a definition's own
//! fields (its name, domain and facets); [`m07`] takes both from the implementation
//! (crates/zedc-zir/src/canon/serial.rs) and says so at each place. Everything else it writes
//! as the paragraph says.
//!
//! The terms here hold no nonempty string, so the two must agree. Terms holding nonempty
//! strings (short, long, repeated, all distinct, joined) are compared in the parked test
//! /home/luke/Work/wt/failing-tests/SPEC-m07-string-serial.rs: since canonicalization
//! VERSION 11 (CANON-term-string-nodes) the implementation writes a nonempty string as the
//! rules of its canonical parse, not as its UTF-8, and the two differ (QUESTIONS A106).

use zed_kernel::term::Prim;
use zed_kernel::value::Value;
use zedc::address::ContentAddress;

use super::{def, none};

/// Step M0.7's serialization and address, for definitions with no domain and no facets whose
/// bodies are literals, free variables, applications and primitives over booleans, integers,
/// strings and tuples.
pub(super) mod m07 {
    use zed_kernel::term::Term;
    use zed_kernel::value::Value;
    use zedc::address::ContentAddress;
    use zedc::canon::Def;

    /// The address of `d`, already in normal form, under rule-set version `version`:
    /// BLAKE3-256 over `zed-canon`, a NUL byte, the version as a 32-bit little-endian word,
    /// then the serialization.
    pub fn address(version: u32, d: &Def) -> ContentAddress {
        let mut h = blake3::Hasher::new();
        h.update(b"zed-canon\0");
        h.update(&version.to_le_bytes());
        h.update(&serialize(d));
        // `hashed` changes nothing outside the `short-addresses` test build, which keeps one
        // byte of every address.
        ContentAddress::hashed(&h)
    }

    /// The serialization of `d`.
    pub fn serialize(d: &Def) -> Vec<u8> {
        assert!(
            d.domain.is_none() && d.facets.is_empty(),
            "outside the subset"
        );
        let mut out = Vec::new();
        // The definition's fields, in the implementation's order: its name, a tag 0 for no
        // domain, the count of its facets.
        string(&mut out, d.name.as_bytes());
        out.push(0);
        word(&mut out, 0);
        term(&mut out, &d.body);
        out
    }

    /// A length or an integer: a 64-bit little-endian word.
    fn word(out: &mut Vec<u8>, n: u64) {
        out.extend_from_slice(&n.to_le_bytes());
    }

    /// A string: its length, then its UTF-8.
    fn string(out: &mut Vec<u8>, utf8: &[u8]) {
        word(out, utf8.len() as u64);
        out.extend_from_slice(utf8);
    }

    // The tag bytes below are the implementation's (serial.rs `term_head`, `value_head`).
    fn term(out: &mut Vec<u8>, t: &Term) {
        match t {
            Term::Lit(v) => {
                out.push(1);
                value(out, v);
            }
            // A free variable no definition resolves, written by its name; a name with a
            // leading NUL would be a bound variable, which no term here holds.
            Term::Var(x) => {
                assert!(!x.starts_with('\0'), "outside the subset");
                out.push(4);
                string(out, x.as_bytes());
            }
            Term::App(f, args) => {
                out.push(6);
                term(out, f);
                word(out, args.len() as u64);
                args.iter().for_each(|a| term(out, a));
            }
            Term::Prim(p, args) => {
                out.push(7);
                word(out, p.code());
                word(out, args.len() as u64);
                args.iter().for_each(|a| term(out, a));
            }
            _ => panic!("outside the subset"),
        }
    }

    fn value(out: &mut Vec<u8>, v: &Value) {
        match v {
            Value::Bool(b) => {
                out.push(0);
                out.push(u8::from(*b));
            }
            Value::Int(n) => {
                out.push(1);
                word(out, *n as u64);
            }
            Value::Str(s) => {
                out.push(3);
                word(out, s.len() as u64);
                s.chunks().for_each(|c| out.extend_from_slice(c.as_bytes()));
            }
            Value::Tuple(vs) => {
                out.push(5);
                word(out, vs.len() as u64);
                vs.iter().for_each(|v| value(out, v));
            }
            _ => panic!("outside the subset"),
        }
    }
}

fn implementation(d: &zedc::canon::Def) -> ContentAddress {
    zedc::canon::address(d, &none).expect("memory for the address")
}

/// Definitions from a shipping-cost table with no nonempty string: integers, booleans, a
/// tuple, a free variable (the prelude's `max`), primitives, and the empty string.
fn without_text() -> Vec<zedc::canon::Def> {
    use zed_kernel::term::build::{app, lit, prim, var};
    vec![
        def("free_over", lit(Value::Int(5000))),
        def("negative", lit(Value::Int(-17))),
        def("express", lit(Value::Bool(true))),
        def(
            "rates",
            lit(Value::tuple(vec![
                Value::Int(499),
                Value::Int(899),
                Value::tuple(vec![Value::Bool(false), Value::Int(0)]),
            ])),
        ),
        def(
            "cost",
            app(
                var("max"),
                vec![
                    prim(Prim::Add, vec![lit(Value::Int(499)), lit(Value::Int(150))]),
                    lit(Value::Int(0)),
                ],
            ),
        ),
        def("no_note", lit(Value::str(""))),
        def(
            "notes",
            lit(Value::tuple(vec![Value::str(""), Value::Int(3)])),
        ),
    ]
}

/// Where M0.7 states the serialization, the implementation's address is M0.7's: the header,
/// the rule-set version, words, names and the empty string.
#[test]
fn a_definition_without_text_has_the_address_m07_states() {
    for d in without_text() {
        assert_eq!(
            implementation(&d),
            m07::address(zedc::canon::VERSION, &d),
            "{}",
            d.name
        );
    }
}

/// The comparison can fail: the address under another rule-set version, or with one byte of
/// the serialization changed, is not the implementation's.
#[test]
fn another_version_or_byte_gives_another_address() {
    for d in without_text() {
        let ours = implementation(&d);
        assert_ne!(
            ours,
            m07::address(zedc::canon::VERSION - 1, &d),
            "{}",
            d.name
        );
        let mut bytes = m07::serialize(&d);
        let last = bytes.len() - 1;
        bytes[last] ^= 1;
        let mut h = blake3::Hasher::new();
        h.update(b"zed-canon\0");
        h.update(&zedc::canon::VERSION.to_le_bytes());
        h.update(&bytes);
        if !zed_kernel::address::SHORT {
            assert_ne!(ours, ContentAddress::hashed(&h), "{}", d.name);
        }
    }
}

/// [`m07::serialize`] is the implementation's serialization, byte for byte, on these
/// definitions.
#[test]
fn the_serialization_is_m07s_byte_for_byte() {
    for d in without_text() {
        let normal = zedc::canon::canonicalize(&d);
        assert_eq!(
            zedc::canon::serialize(&normal, &none).expect("memory"),
            m07::serialize(&normal),
            "{}",
            d.name
        );
    }
}
