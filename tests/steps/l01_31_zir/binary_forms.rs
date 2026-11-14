//! Damaged binary data at each choice and count the decoder reads, each refused with the byte
//! offset where it was found (DESIGN L1.31: the binary form gives back the same graph, and a
//! decoding error names the byte offset).

use zedc::zir::{binary, text};

/// The binary form of the graph `src`.
fn bytes(src: &str) -> Vec<u8> {
    binary::encode(&text::parse(src).unwrap_or_else(|e| panic!("{e}\n{src}")))
        .expect("memory for the bytes")
}

/// The binary form of a graph whose one result is the constant written `value`.
fn constant(value: &str) -> Vec<u8> {
    bytes(&format!(
        "zir 1\nr region function ()\nr results ({value})\n"
    ))
}

/// The offset of the one place `part` occurs in `data`.
fn at(data: &[u8], part: &[u8]) -> usize {
    let mut hits = data
        .windows(part.len())
        .enumerate()
        .filter(|(_, w)| w == &part);
    let (i, _) = hits.next().expect("the part occurs");
    assert!(hits.next().is_none(), "the part occurs once");
    i
}

/// A word as the binary form writes it.
fn word(n: u64) -> [u8; 8] {
    n.to_le_bytes()
}

/// The first offset where `a` and `b` differ: the tag that tells two graphs apart which
/// differ in one choice.
fn first_difference(a: &[u8], b: &[u8]) -> usize {
    a.iter()
        .zip(b)
        .position(|(x, y)| x != y)
        .expect("the two differ")
}

/// `data` with byte `i` set to `t`.
fn with_byte(mut data: Vec<u8>, i: usize, t: u8) -> Vec<u8> {
    data[i] = t;
    data
}

#[test]
fn each_choice_with_a_tag_past_its_last_case_is_refused() {
    let graph = |op: &str| {
        format!(
            "zir 1\nr region function (int; struct; (-> (tuple int int) int))\nr.0 {op} -> (int)\nr results (r.0^0)\n"
        )
    };
    let fold = |ev: &str, id: &str| {
        graph(&format!(
            "fold 1{id} {{associative: {ev}}} (r^1, r^2{})",
            if id.is_empty() { "" } else { ", 0" }
        ))
    };
    let pairs = [
        ("an operation", graph("prim neg (r^0)"), graph("apply (r^2, r^0)"), 17),
        ("a primitive", graph("prim neg (r^0)"), graph("prim abs (r^0)"), text::PRIMS.len() as u8),
        ("a grade", fold("axiom", ""), fold("assumed", ""), 6),
        ("a boolean", fold("axiom", ""), fold("axiom", " identity"), 2),
        (
            "a guard position",
            "zir 1\nr region function (int)\nr.0 gen before (r^0) -> (struct)\nr.0/0 region loop (int)\nr.0/0 results (r.0/0^0)\nr.0/1 region loop (int)\nr.0/1 results (true)\nr results (r.0^0)\n".to_string(),
            "zir 1\nr region function (int)\nr.0 gen after (r^0) -> (struct)\nr.0/0 region loop (int)\nr.0/0 results (r.0/0^0)\nr.0/1 region loop (int)\nr.0/1 results (true)\nr results (r.0^0)\n".to_string(),
            2,
        ),
        (
            "a derived node",
            "zir 1\nr region function (struct)\nr.0 group (r^0) -> (struct)\nr.0/0 region function (struct)\nr.0/0 results (r.0/0^0)\nr results (r.0^0)\n".to_string(),
            "zir 1\nr region function (struct)\nr.0 join (r^0) -> (struct)\nr.0/0 region function (struct)\nr.0/0 results (r.0/0^0)\nr results (r.0^0)\n".to_string(),
            4,
        ),
        (
            "a pattern",
            "zir 1\nr region function (int)\nr.0 match [_] (r^0) -> (int)\nr.0/0 region match ()\nr.0/0 results (1)\nr results (r.0^0)\n".to_string(),
            "zir 1\nr region function (int)\nr.0 match [#_] (r^0) -> (int)\nr.0/0 region match ()\nr.0/0 results (1)\nr results (r.0^0)\n".to_string(),
            8,
        ),
        (
            "a value",
            "zir 1\nr region function ()\nr results (true)\n".to_string(),
            "zir 1\nr region function ()\nr results (1)\n".to_string(),
            14,
        ),
    ];
    for (what, a, b, bad) in pairs {
        let (a, b) = (bytes(&a), bytes(&b));
        let i = first_difference(&a, &b);
        assert_eq!(
            binary::decode(&with_byte(a, i, bad)),
            Err(format!("byte {i}: {bad} is not a tag of {what}")),
            "{what}"
        );
    }
}

#[test]
fn each_tag_at_its_last_case_reads() {
    // The last case of each choice: `wave`, the last primitive, `assumed`, `true`, `after`,
    // `join`, and the last pattern and value tags, written by the graphs below.
    let last_prim = text::PRIMS[text::PRIMS.len() - 1];
    assert!(
        text::parse(&format!(
            "zir 1\nr region function ()\nr.0 prim {} () -> (_)\nr results (r.0^0)\n",
            last_prim.printed()
        ))
        .is_ok()
    );
    for src in [
        "zir 1\nr region port (state out)\nr.0 wave (r^0) -> (state out)\nr.0/0 region port (state out)\nr.0/0 results (r.0/0^0)\nr results (r.0^0)\n",
        "zir 1\nr region function (struct; (-> (tuple int int) int))\nr.0 fold 1 identity {associative: assumed} (r^0, r^1, 0) -> (int)\nr results (r.0^0)\n",
        "zir 1\nr region function ()\nr results (1.0f32, {1 -> 2}, #a(x: 1), #b, (1, 2), [1 -> 2], 3r/4r, 1267650600228229401496703205376, -1267650600228229401496703205376)\n",
    ] {
        let g = text::parse(src).unwrap_or_else(|e| panic!("{e}\n{src}"));
        let b = binary::encode(&g).expect("memory for the bytes");
        assert_eq!(binary::decode(&b).as_ref(), Ok(&g), "{src}");
    }
}

#[test]
fn a_rational_with_denominator_0_is_refused() {
    let good = constant("3r/4r");
    assert!(binary::decode(&good).is_ok());
    // Tag 3, the sign, the numerator's one limb 3, the denominator's one limb 4.
    let tag = at(
        &good,
        &[&[3u8, 0][..], &word(1), &word(3), &word(1), &word(4)].concat(),
    );
    let bad = [&good[..tag + 26], &word(0), &good[tag + 34..]].concat();
    assert_eq!(
        binary::decode(&bad),
        Err(format!("byte {tag}: a rational with denominator 0"))
    );
}

#[test]
fn an_f32_word_wider_than_32_bits_is_refused() {
    let good = constant("0.5f32");
    let tag = at(&good, &[&[11u8][..], &word(0x3f00_0000)].concat());
    let bad = [&good[..tag + 1], &word(0x1_3f00_0000), &good[tag + 9..]].concat();
    assert_eq!(
        binary::decode(&bad),
        Err(format!("byte {tag}: an f32 word wider than 32 bits"))
    );
}

#[test]
fn an_atom_with_fewer_values_than_fields_is_refused() {
    let good = constant("#e(a: 1, b: 2, c: 3)");
    let fields = [
        &word(3)[..],
        &word(1),
        b"a",
        &word(1),
        b"b",
        &word(1),
        b"c",
        &word(3),
    ]
    .concat();
    let count = at(&good, &fields) + fields.len() - 8;
    let bad = [&good[..count], &word(2), &good[count + 8..]].concat();
    // The atom's tag 6 comes before its name `e`, written as its length and its one byte.
    let tag = count - 3 * 9 - 8 - 9 - 1;
    assert_eq!(bad[tag], 6);
    assert_eq!(
        binary::decode(&bad),
        Err(format!("byte {tag}: atom `#e` has 3 fields and 2 values"))
    );
}

#[test]
fn a_count_past_the_end_of_the_data_is_refused() {
    let good = constant("(1, 2)");
    // Tag 7, a tuple, then its count of parts.
    let count = at(&good, &[&[7u8][..], &word(2)].concat()) + 1;
    let bad = [&good[..count], &word(1 << 40), &good[count + 8..]].concat();
    assert_eq!(
        binary::decode(&bad),
        Err(format!(
            "byte {count}: the count {} is more than the bytes left",
            1u64 << 40
        ))
    );
}

#[test]
fn a_port_named_main_and_a_field_is_refused() {
    let good = bytes(
        "zir 1\nr region port (state main::abc)\nr.0 port push main::abc (r^0, 1) -> (_; state main::abc)\nr results (r.0^1)\n",
    );
    assert!(binary::decode(&good).is_ok());
    // The operation's port is the one string `main::abc` alone; the edges write `state main::abc`.
    let name = at(&good, &[&word(9)[..], b"main::abc"].concat());
    let bad = [&good[..name + 8], b"main::a.c", &good[name + 17..]].concat();
    assert_eq!(
        binary::decode(&bad),
        Err(format!(
            "byte {name}: `main::a.c` is not a port's name: `main::` takes one name"
        ))
    );
}
