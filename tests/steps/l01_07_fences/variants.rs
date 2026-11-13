//! Item SPEC-no-verbatim: the variants are built from the spec's fences by a table that names
//! each fence by key and each changed line by a short piece of it, so the repository keeps no
//! copy of a fence.

use zed_tests::fences::{DocFence, Variant, build};

fn fence(key: &str, text: &str) -> DocFence {
    DocFence {
        key: key.into(),
        at: "DESIGN.md:10".into(),
        layer: 1,
        ring: 1,
        notation: false,
        text: text.into(),
    }
}

const KEY: &str = "DESIGN.md [sec:grammar] 1";
const FENCE: &str = "a = 1;\n  // b = a + x;   // ✗ no x\nc = 2;\n// d = y;   // ✗ no y";

fn one(table: &str) -> Result<Variant, Vec<String>> {
    build(table, &[fence(KEY, FENCE)]).map(|mut v| {
        assert_eq!(v.len(), 1);
        v.remove(0)
    })
}

fn err(table: &str) -> String {
    one(table).expect_err("an error").join("\n")
}

#[test]
fn the_live_line_is_made_live_in_place() {
    let v = one(&format!("variant: v\nfence: {KEY}\nlive: a + x")).unwrap();
    assert_eq!(v.name, "v");
    assert_eq!(v.of, "// b = a + x;   // ✗ no x");
    // The first line names the variant, so each line stands one below its fence line; the
    // live line keeps its indentation, and the other commented ✗ line stays commented.
    assert_eq!(
        v.text,
        "// variant: // b = a + x;   // ✗ no x\na = 1;\n  b = a + x;   // ✗ no x\nc = 2;\n\
         // d = y;   // ✗ no y\n"
    );
}

#[test]
fn omit_keep_and_edit_change_the_lines_they_name() {
    let omit = one(&format!(
        "variant: v\nfence: {KEY}\nlive: d = y\nomit: a = 1\nedit: c = 2 => c = 3"
    ))
    .unwrap();
    assert_eq!(
        omit.text,
        "// variant: // d = y;   // ✗ no y\n  // b = a + x;   // ✗ no x\nc = 3;\nd = y;   // ✗ no y\n"
    );
    let keep = one(&format!(
        "variant: v\nfence: {KEY}\nlive: d = y\nkeep: c = 2"
    ))
    .unwrap();
    assert_eq!(
        keep.text,
        "// variant: // d = y;   // ✗ no y\nc = 2;\nd = y;   // ✗ no y\n"
    );
}

#[test]
fn a_line_that_stands_for_an_edit_makes_the_edit_and_stays() {
    let text = "s = { n: int | #none };\n// n: int   // ✗ #none is missing\nt = 1;";
    let v = build(
        "variant: v\nfence: K\nlive: n: int\nstands: int | #none => int",
        &[fence("K", text)],
    )
    .unwrap();
    assert_eq!(
        v[0].text,
        "// variant: // n: int   // ✗ #none is missing\ns = { n: int };   // ✗ #none is missing\n\
         // n: int   // ✗ #none is missing\nt = 1;\n"
    );
}

#[test]
fn a_fence_that_is_gone_is_named_by_its_key() {
    assert_eq!(
        err("variant: v\nfence: DESIGN.md [sec:grammar] 2\nlive: a + x"),
        "variants.txt:1: the variant `v` is built from the fence `DESIGN.md [sec:grammar] 2`, and the \
         spec has no fence with that key; find the fence that now holds its ✗ line and write \
         that fence's key"
    );
}

#[test]
fn each_text_names_one_line() {
    let at = format!("variants.txt:1: the variant `v`, of the fence `{KEY}` at DESIGN.md:10");
    assert_eq!(
        err(&format!("variant: v\nfence: {KEY}\nlive: a = 1")),
        format!("{at}: no commented ✗ line of the fence holds `a = 1`")
    );
    assert_eq!(
        err(&format!("variant: v\nfence: {KEY}\nlive: ✗ no")),
        format!(
            "{at}: 2 commented ✗ lines of the fence hold `✗ no`, its lines 2, 4; write a \
             longer piece of one"
        )
    );
    assert_eq!(
        err(&format!("variant: v\nfence: {KEY}\nlive: a + x\nomit: zz")),
        format!("{at}: no line of the fence holds `zz`")
    );
    assert_eq!(
        err(&format!(
            "variant: v\nfence: {KEY}\nlive: a + x\nomit: a + x"
        )),
        format!("{at}: its line 2 is both left out and changed")
    );
    assert_eq!(
        err(&format!(
            "variant: v\nfence: {KEY}\nlive: a + x\nkeep: c = 2\nedit: a = 1 => a = 0"
        )),
        format!("{at}: its line 1 is both left out and changed")
    );
    assert_eq!(
        err(&format!("variant: v\nfence: {KEY}\nomit: c = 2")),
        format!("{at}: it has no `live:` line")
    );
}

#[test]
fn a_table_that_is_not_one_is_named_line_by_line() {
    assert_eq!(
        err("# a comment\nlive: x\nvariant: v\nlive: a + x\nfrom: y\nedit: a\nomit:\n"),
        [
            "variants.txt:2: `live:` comes before any `variant:` line",
            "variants.txt:5: `from:` is not a word of the table; the words are variant, fence, \
             live, omit, keep, edit and stands",
            "variants.txt:6: `edit:` needs `OLD => NEW`",
            "variants.txt:7: `omit:` names no text",
            "variants.txt:3: the variant `v` has no `fence:` line",
        ]
        .join("\n")
    );
    let twice =
        format!("variant: v\nfence: {KEY}\nlive: a + x\nvariant: v\nfence: {KEY}\nlive: d = y");
    assert_eq!(
        err(&twice),
        "variants.txt:4: the variant `v` is named twice"
    );
}
