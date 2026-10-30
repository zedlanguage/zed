//! Graphs the reader or the validator rejects, each with its message, and damaged binary data.

use super::rejected;
use zedc::zir::binary;

/// Each case: what is wrong, the text, and the message.
const CASES: &[(&str, &str, &str)] = &[
    (
        "a node reads its own output",
        "zir 1\nr region function (int)\nr.0 prim neg (r.0^0) -> (int)\nr results (r.0^0)\n",
        "r.0: input 0: r.0: a node reads only nodes before it, and this is node 0",
    ),
    (
        "an arm reads the other arm's argument",
        "zir 1\nr region function (bool; int)\nr.0 if (r^0, r^1) -> (int)\nr.0/0 region match (int)\nr.0/0 results (r.0/0^0)\nr.0/1 region match (int)\nr.0/1 results (r.0/0^0)\nr results (r.0^0)\n",
        "line 7: column 16: r.0/0^0 is not an edge of region r.0/1, and a region reads only its own edges",
    ),
    (
        "forward reference",
        "zir 1\nr region function (int)\nr.0 prim + (r.1^0, 1) -> (int)\nr.1 prim + (r^0, 1) -> (int)\nr results (r.1^0)\n",
        "r.0: input 0: r.1: a node reads only nodes before it, and this is node 0",
    ),
    (
        "output out of range",
        "zir 1\nr region function (int)\nr.0 prim neg (r^0) -> (int)\nr results (r.0^1)\n",
        "r: result 0: r.0^1: node r.0 (`prim neg`) has 1 output, numbered from 0",
    ),
    (
        "argument out of range",
        "zir 1\nr region function (int)\nr results (r^1)\n",
        "r: result 0: r^1: the region has 1 argument, numbered from 0",
    ),
    (
        "state used twice",
        "zir 1\nr region port (state out)\nr.0 port push out (r^0, 1) -> (_; state out)\nr.1 port push out (r^0, 2) -> (_; state out)\nr results (r.0^1, r.1^1)\n",
        "r^0: a state edge is used 2 times, and each is used exactly once",
    ),
    (
        "state never used",
        "zir 1\nr region port (state out)\nr.0 port push out (r^0, 1) -> (_; state out)\nr results ()\n",
        "r.0^1: a state edge is never used, and each is used exactly once",
    ),
    (
        "state into function region",
        "zir 1\nr region function (state out)\nr results (r^0)\n",
        "r^0: a state edge cannot enter a function region",
    ),
    (
        "wrong port",
        "zir 1\nr region port (state in)\nr.0 port push out (r^0, 1) -> (_; state out)\nr results (r.0^1)\n",
        "r.0: input 0 of `port push out` is state in, and must be `state out`",
    ),
    (
        "state into prim",
        "zir 1\nr region port (state out)\nr.0 prim neg (r^0) -> (int)\nr results (r^0)\n",
        "r.0: input 0 of `prim neg` is a state edge",
    ),
    (
        "arity",
        "zir 1\nr region function (int)\nr.0 prim + (r^0) -> (int)\nr results (r.0^0)\n",
        "r.0: `prim +` takes 2 inputs, and has 1",
    ),
    (
        "fold depth 0",
        "zir 1\nr region function (struct; _)\nr.0 fold 0 {} (r^0, r^1) -> (int)\nr results (r.0^0)\n",
        "r.0: `fold` has depth 0, and a family has at least 1 level",
    ),
    (
        "region kind",
        "zir 1\nr region function (struct; int)\nr.0 fam (r^0, r^1) -> (struct)\nr.0/0 region loop (String; int)\nr.0/0 results (r.0/0^1)\nr results (r.0^0)\n",
        "r.0/0: region 0 of `fam` must be a function region, and is written `loop`",
    ),
    (
        "capture type mismatch",
        "zir 1\nr region function (struct; int)\nr.0 fam (r^0, r^1) -> (struct)\nr.0/0 region function (String; String)\nr.0/0 results (r.0/0^1)\nr results (r.0^0)\n",
        "r.0/0^1: capture 0 is int, and the argument is String",
    ),
    (
        "missing region",
        "zir 1\nr region function (struct)\nr.0 fam (r^0) -> (struct)\nr results (r.0^0)\n",
        "r.0: `fam` has 1 region, and 0 are written",
    ),
    (
        "derived in certificate",
        "zir 1\nr region function (struct)\nr.0 group (r^0) -> (struct)\nr.0/0 region function (struct)\nr.0/0.0 rank (r.0/0^0) -> (struct)\nr.0/0.0/0 region function (struct)\nr.0/0.0/0 results (r.0/0.0/0^0)\nr.0/0 results (r.0/0.0^0)\nr results (r.0^0)\n",
        "r.0/0.0: `rank` in a certificate, which holds only kernel nodes",
    ),
    (
        "result count of if",
        "zir 1\nr region function (bool)\nr.0 if (r^0) -> (int)\nr.0/0 region match ()\nr.0/0 results (1, 2)\nr.0/1 region match ()\nr.0/1 results (3)\nr results (r.0^0)\n",
        "r.0/0: the region must have 1 result, and 2 are written",
    ),
    (
        "match arm binds",
        "zir 1\nr region function (_)\nr.0 match [#some(n), #none] (r^0) -> (int)\nr.0/0 region match ()\nr.0/0 results (1)\nr.0/1 region match ()\nr.0/1 results (0)\nr results (r.0^0)\n",
        "r.0/0: the region takes 1 argument from the node (the pattern `#some(n)` binds 1 name) and 0 captures, 1 in all, and has 0",
    ),
    (
        "parse: first line",
        "zed 1\nr region function ()\nr results ()\n",
        "line 1: the first line is `zir 1`",
    ),
    (
        "parse: unknown op",
        "zir 1\nr region function ()\nr.0 frobnicate () -> (int)\nr results (r.0^0)\n",
        "line 3: column 15: `frobnicate` is not a ZIR operation",
    ),
    (
        "parse: cross-region source",
        "zir 1\nr region function (int)\nr.0 lambda () -> ((-> int int))\nr.0/0 region function (int)\nr.0/0 results (r^0)\nr results (r.0^0)\n",
        "line 5: column 16: r^0 is not an edge of region r.0/0, and a region reads only its own edges",
    ),
    (
        "parse: duplicate line",
        "zir 1\nr region function ()\nr results ()\nr results ()\n",
        "lines 3 and 4: two lines for the results of r",
    ),
    (
        "parse: missing results",
        "zir 1\nr region function ()\n",
        "region r has no results line",
    ),
    (
        "parse: orphan line",
        "zir 1\nr region function ()\nr results ()\nr.3 prim neg (1) -> (int)\n",
        "line 4: node r.3 is not in the graph: region r has 0 nodes before it, numbered from 0",
    ),
    (
        "parse: recursive type",
        "zir 1\nr region function (List)\nr results (r^0)\n",
        "line 2: column 20: `List` is not a type of the text form; a recursive type has none until step L2 declares types",
    ),
    (
        "parse: node path as region",
        "zir 1\nr.0 region function ()\nr results ()\n",
        "line 2: column 11: r.0 is a node's path, not a region's",
    ),
    (
        "parse: bad prim",
        "zir 1\nr region function ()\nr.0 prim ** (2, 3) -> (int)\nr.1 prim sqrt (2) -> (f64)\nr results (r.0^0)\n",
        "line 4: column 14: `sqrt` is not a primitive",
    ),
    (
        "parse: bad grade",
        "zir 1\nr region function (struct; _)\nr.0 fold 1 {associative: likely} (r^0, r^1) -> (int)\nr results (r.0^0)\n",
        "line 3: column 32: `likely` is not a grade",
    ),
    (
        "parse: trailing junk",
        "zir 1\nr region function () extra\nr results ()\n",
        "line 2: column 22: unexpected `extra` after the line",
    ),
];

#[test]
fn each_rejection_names_its_cause() {
    for (what, src, want) in CASES {
        assert_eq!(rejected(src), *want, "{what}");
    }
}

/// The binary form of the greeting graph.
fn greeting() -> Vec<u8> {
    let g = zedc::zir::text::parse(
        "zir 1\nr region port (state out)\nr.0 port push out (r^0, \"hi\") -> (_; state out)\nr results (r.0^1)\n",
    )
    .expect("a graph");
    binary::encode(&g)
}

#[test]
fn damaged_binary_data() {
    let good = greeting();
    assert!(binary::decode(&good).is_ok());
    let mut magic = good.clone();
    magic[0] = b'X';
    let mut version = good.clone();
    version[4] = 9;
    let mut tag = good.clone();
    tag[8] = 7;
    let mut trailing = good.clone();
    trailing.push(0);
    let cases: [(&str, &[u8], &str); 6] = [
        (
            "empty",
            &[],
            "byte 0: the data ends, and 4 more bytes were expected",
        ),
        ("magic", &magic, "byte 0: the data does not start `ZIR\\0`"),
        (
            "version",
            &version,
            "byte 4: version 9, and this compiler reads version 1",
        ),
        ("tag", &tag, "byte 8: 7 is not a tag of a region kind"),
        (
            "truncated",
            &good[..good.len() - 3],
            "byte 142: the data ends, and 8 more bytes were expected",
        ),
        (
            "trailing",
            &trailing,
            "byte 150: 1 byte follows the graph, which ends here",
        ),
    ];
    for (what, bytes, want) in cases {
        assert_eq!(binary::decode(bytes), Err(want.to_string()), "{what}");
    }
}

#[test]
fn binary_atom_fields_in_order() {
    let g = zedc::zir::text::parse("zir 1\nr region function ()\nr results (#e(a: 1, b: 2))\n")
        .expect("a graph");
    let mut bytes = binary::encode(&g);
    // Swap the one-byte field names `a` and `b`, each written after its length 1.
    let len1 = 1u64.to_le_bytes();
    let at = |name: u8| {
        let want = [&len1[..], &[name]].concat();
        bytes
            .windows(9)
            .position(|w| w == want)
            .expect("the field name")
    };
    let (a, b) = (at(b'a') + 8, at(b'b') + 8);
    bytes.swap(a, b);
    assert_eq!(
        binary::decode(&bytes),
        Err("byte 34: atom `#e` has its fields out of order or repeated".to_string())
    );
}
