//! An integer range that is exactly the range of a fixed-width alias prints as that alias, and
//! the alias reads back as that range (DESIGN.md sec:diagnostics, "Types in a message"; step
//! L1.12; QUESTIONS A72; plan row PRINT-int-carrier-names): `int[-2^63..<2^63]` prints `i64`,
//! `int[0..<2^8]` prints `u8`, and a range one off at either end prints as a range.

use super::{rejected, steps};
use zed_tests::step_helpers::l01_19_whole_file_ports::run;

/// Each alias with its range as DESIGN.md sec:domains writes it, `int[0 ..= 2^k - 1]` and
/// `int[-2^(k - 1) ..= 2^(k - 1) - 1]`, in the half-open spelling.
const ALIASES: [(&str, &str); 10] = [
    ("i8", "int[-2^7..<2^7]"),
    ("i16", "int[-2^15..<2^15]"),
    ("i32", "int[-2^31..<2^31]"),
    ("i64", "int[-2^63..<2^63]"),
    ("i128", "int[-2^127..<2^127]"),
    ("u8", "int[0..<2^8]"),
    ("u16", "int[0..<2^16]"),
    ("u32", "int[0..<2^32]"),
    ("u64", "int[0..<2^64]"),
    ("u128", "int[0..<2^128]"),
];

/// A program whose call of `f`, declared with the parameter type `ty`, passes a string, so that
/// the rejection prints `f`'s type.
fn called_with_a_string(ty: &str) -> String {
    format!("f(positional x: {ty}) = x;\nmain() = f(\"a\");\n")
}

/// The rejection of [`called_with_a_string`] of `ty`, without its source lines.
fn types_printed(ty: &str) -> Vec<String> {
    let out = rejected(&called_with_a_string(ty));
    steps(&out).into_iter().map(str::to_string).collect()
}

#[test]
fn each_alias_range_prints_as_the_alias() {
    let mut wrong = Vec::new();
    for (name, range) in ALIASES {
        let out = rejected(&called_with_a_string(range));
        let want = format!("`f` takes {name} -> {name}");
        if !out.contains(&want) {
            wrong.push(format!("{range}: want {want}\n{out}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn a_range_one_off_at_either_end_prints_as_a_range() {
    for (range, text) in [
        ("int[0..=256]", "int[0..=256]"),
        ("int[1..=255]", "int[1..=255]"),
        ("int[-1..=255]", "int[-1..=255]"),
        ("int[0..=254]", "int[0..=254]"),
        ("int[-129..=127]", "int[-129..=127]"),
        ("int[-127..=127]", "int[-127..=127]"),
        ("int[-128..=126]", "int[-128..=126]"),
        ("int[-128..=128]", "int[-128..=128]"),
        (
            "int[-2^63..=2^63]",
            "int[-9223372036854775808..=9223372036854775808]",
        ),
        ("int[1..<2^64]", "int[1..=18446744073709551615]"),
        // A power of two that is no width.
        ("int[0..<2^4]", "int[0..=15]"),
        (
            "int[0..<2^256]",
            "int[0..=115792089237316195423570985008687907853269984665640564039457584007913129639935]",
        ),
    ] {
        let out = rejected(&called_with_a_string(range));
        let want = format!("`f` takes {text} -> {text}");
        assert!(out.contains(&want), "{range}: want {want}\n{out}");
    }
}

/// The printed type re-parses to the same type: `f` declared with the alias prints exactly what
/// it prints declared with the range, in every step of the rejection.
#[test]
fn an_alias_reads_back_as_its_range() {
    let mut wrong = Vec::new();
    for (name, range) in ALIASES {
        let (by_name, by_range) = (types_printed(name), types_printed(range));
        if by_name != by_range {
            wrong.push(format!("{name}:\n{by_name:#?}\n{range}:\n{by_range:#?}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// A call of `f(x: u8)` outside the range is rejected naming `u8`, and one inside runs: `main`
/// returns `f(x: 200)`, so the status is 200.
#[test]
fn an_alias_checks_a_call_as_its_range_does() {
    let src =
        "f(x: u8) = x;\na = f(x: 256);\nmain(m: MainArgs) -> int { m.stdout <- \"\"; return 0; }\n";
    let out = rejected(src);
    let first = out.lines().next().unwrap_or("");
    assert!(
        first.ends_with("2:5: `f` takes `x` in u8: `f(x: 256 : int)`."),
        "{out}"
    );
    let src = "f(x: i64) = x;\na = f(x: -2^63 - 1);\nmain(m: MainArgs) -> int { m.stdout <- \"\"; return 0; }\n";
    let out = rejected(src);
    assert!(out.contains("`f` takes `x` in i64"), "{out}");
    let src = "f(x: u8) = x;\nmain(m: MainArgs) -> int { m.stdout <- \"a\"; return f(x: 200); }\n";
    let o = run("u8_status", src, "", &[]);
    assert_eq!((o.status, o.stdout.as_str()), (200, "a\n"), "{}", o.stderr);
    let src = "f(positional x: i128) = x;\nmain(m: MainArgs) -> int { m.stdout <- \"a\"; return if f(-2^127) < 0 { 7 } else { 0 }; }\n";
    let o = run("i128_status", src, "", &[]);
    assert_eq!((o.status, o.stdout.as_str()), (7, "a\n"), "{}", o.stderr);
}

/// An alias is a range, so it stands where a range does, the whole type of a parameter or the
/// key of a parameter's partial map, and elsewhere waits for a later step, as a range does.
#[test]
fn an_alias_stands_where_a_range_does() {
    let main = "main(m: MainArgs) -> int { m.stdout <- \"\"; return 0; }\n";
    for src in [
        "f(m: u8 ->? int) = 0;\n",
        "f(m: ((u8, int)) ->? int) = 0;\n",
    ] {
        assert!(
            zedc::run::load(format!("{src}{main}").as_bytes()).is_ok(),
            "{src}"
        );
    }
    for (src, at) in [
        ("f(x: (i64, int)) = 0;\n", "1:7: "),
        ("f(x: u8 | #none) = 0;\n", "1:6: "),
        ("f(g: (positional x: u8) -> int) = 0;\n", "1:21: "),
    ] {
        let out = rejected(&format!("{src}{main}"));
        let first = out.lines().next().unwrap_or("");
        let first = first.split_once(".zed:").map_or(first, |(_, r)| r);
        let want = format!(
            "{at}{}",
            zed_tests::not_yet!(
                "a range type in any place but the whole type of a parameter or the key of a \
                 parameter's partial map `K ->? V`"
            )
        );
        assert!(
            first.starts_with(&want),
            "{src}\n  got  {first}\n  want {want}"
        );
    }
}

/// The repair of a range that holds no int writes the alias where the widened range is one.
#[test]
fn the_repair_of_an_empty_range_writes_the_alias() {
    let out = rejected("f(x: int[255..=0]) = x;\n");
    assert!(
        out.contains("repair: write `x: u8`, the range from the lesser bound"),
        "{out}"
    );
    let out = rejected("f(x: int[256..=0]) = x;\n");
    assert!(out.contains("repair: write `x: int[0..=256]`"), "{out}");
}

/// The domain of a bit word's operand at a width that is an alias's prints as the alias:
/// `bitNot` at width 8 takes `x` in `u8`.
#[test]
fn a_bit_word_domain_at_a_carrier_width_prints_as_the_alias() {
    let out = rejected("f(positional n: int) = bitNot(n, width: 8);\n");
    assert!(out.contains("`bitNot` takes `x` in u8"), "{out}");
    let out = rejected("f(positional n: int) = bitNot(n, width: 7);\n");
    assert!(out.contains("`bitNot` takes `x` in int[0..<2^7]"), "{out}");
}
