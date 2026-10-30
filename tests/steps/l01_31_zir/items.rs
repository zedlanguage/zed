//! Types, values, patterns and edges, each read back from the text the kernel prints.

use zed_kernel::Value;
use zed_kernel::term::Pattern;
use zedc::zir::text::{edge, parse_edge, parse_pattern, parse_type, parse_value, pattern};

#[test]
fn types_read_back() {
    for t in [
        "_",
        "(|)",
        "bool",
        "true",
        "int",
        "rat",
        "f64",
        "String",
        "#_",
        "tuple",
        "struct",
        "morphism",
        "3",
        "\"GET\"",
        "#none",
        "(#some (tuple int))",
        "(#some _)",
        "(| #none (#some (tuple int)))",
        "(| int String)",
        "(\\ int 0)",
        "(tuple int String)",
        "(-> int bool)",
        "(->? String int)",
        "(| (-> String String) (-> int int))",
    ] {
        let ty = parse_type(t).unwrap_or_else(|e| panic!("{t}: {e}"));
        assert_eq!(ty.to_string(), t);
    }
}

#[test]
fn values_read_back() {
    for v in [
        "true",
        "-42",
        "123456789012345678901234567890",
        "3r",
        "-3r/4r",
        "1.5",
        "-0.0",
        "inf",
        "-inf",
        "nan",
        "1.5e30",
        "\"tab\\there \\\"quoted\\\" 😀\"",
        "#empty",
        "#pair(1, \"b\")",
        "#err(code: 3, why: \"x\")",
        "()",
        "(1)",
        "(1, (2, 3))",
        "[\"eu\" -> 2024 -> 3]",
        "{}",
        "{1 -> \"a\", 2 -> \"b\"}",
        "{\"x\", \"y\"}",
        "{1 -> {2 -> 3}}",
    ] {
        let val = parse_value(v).unwrap_or_else(|e| panic!("{v}: {e}"));
        assert_eq!(val.to_string(), v);
    }
}

#[test]
fn string_escapes() {
    // The kernel prints a printable character as itself; the reader takes Rust's escapes too.
    assert_eq!(
        parse_value("\"\\u{1f600}\\n\\0\""),
        Ok(Value::str("😀\n\0"))
    );
    assert_eq!(
        parse_value("\"a\\qb\""),
        Err("column 2: `\\q` is not an escape".into())
    );
}

#[test]
fn named_payload_fields_sort() {
    // A struct payload's fields are sorted, whatever order the text gives them in.
    assert_eq!(
        parse_value("#err(why: \"x\", code: 3)"),
        parse_value("#err(code: 3, why: \"x\")")
    );
    assert_eq!(
        parse_value("#err(code: 3, code: 4)"),
        Err("column 23: atom `#err` names a field twice".into())
    );
}

#[test]
fn floats_keep_their_bits() {
    let v = parse_value("-0.0").expect("a float");
    assert_eq!(v, Value::float(-0.0));
    assert_ne!(v, Value::float(0.0));
}

#[test]
fn patterns_read_back() {
    for p in [
        "_",
        "n",
        "#_",
        "#none",
        "#some(n)",
        "#err(code: c, why: _)",
        "(a, b)",
        "(a,)",
        "()",
        "=3",
        "=\"GET\"",
        "=#none",
        "=(1, 2)",
        "(is (| int String))",
        "#some((a, #pair(=1, b)))",
    ] {
        let pat = parse_pattern(p).unwrap_or_else(|e| panic!("{p}: {e}"));
        assert_eq!(pattern(&pat), p);
    }
    // A literal atom is not an atom pattern: `=#none` matches the value, `#none` the shape.
    assert_ne!(parse_pattern("=#none"), parse_pattern("#none"));
    assert!(matches!(parse_pattern("#none"), Ok(Pattern::Atom(..))));
}

#[test]
fn edges_read_back() {
    for e in [
        "state out",
        "int",
        "int in [0..=9]",
        "int in [..=-1, 1..]",
        "int class 1 mod 3",
        "int class 5",
        "int set {1, 5, 9}",
        "int in [0..] class 0 mod 2 set {0, 2}",
        "rat facet units \"m/s\"",
        "String hint name \"title\" facet locale \"en\"",
    ] {
        let ed = parse_edge(e).unwrap_or_else(|err| panic!("{e}: {err}"));
        assert_eq!(edge(&ed), e);
    }
}
