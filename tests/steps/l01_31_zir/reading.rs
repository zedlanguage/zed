//! The text reader on every form it reads and every way a line can be wrong that the other
//! files do not reach: whole graphs, types, values, patterns and edges (DESIGN L1.31).

use super::round;
use zedc::zir::text::{parse, parse_edge, parse_pattern, parse_type, parse_value, pattern, print};

/// Lists every case whose result differs from the one wanted, so one run shows them all.
fn check<T>(
    cases: &[(&str, &str, &str)],
    read: impl Fn(&str) -> Result<T, String>,
    show: impl Fn(&T) -> String,
) {
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|(what, src, want)| {
            let got = match read(src) {
                Ok(x) => show(&x),
                Err(e) => format!("error: {e}"),
            };
            (got != *want).then(|| format!("{what}:\n  got  {got}\n  want {want}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// Graphs the reader refuses, each with its message.
const GRAPHS: &[(&str, &str, &str)] = &[
    (
        "a graph with no line for its root region's header",
        "zir 1\nr results ()\n",
        "error: region r has no header line",
    ),
    (
        "empty text",
        "",
        "error: the text is empty, and starts `zir 1`",
    ),
    (
        "blank lines only",
        "\n  \n\t\n",
        "error: the text is empty, and starts `zir 1`",
    ),
    (
        "a region's lines with no line for its node",
        "zir 1\nr region function ()\nr.0/0 region function ()\nr.0/0 results ()\nr results ()\n",
        "error: line 3: region r.0/0 is not in the graph: region r has 0 nodes before it, numbered from 0",
    ),
    (
        "an operation on a region's path",
        "zir 1\nr region function ()\nr.0/0 prim neg (1) -> (int)\nr results ()\n",
        "error: line 3: column 7: r.0/0 is a region's path, and its lines are `region` and `results`",
    ),
    (
        "a line that starts with no path",
        "zir 1\nr region function ()\nx.0 prim neg (1) -> (int)\nr results ()\n",
        "error: line 3: column 1: expected a path such as `r.0`, found `x.0`",
    ),
    (
        "a node line with no `->`",
        "zir 1\nr region function ()\nr.0 prim neg (1) (int)\nr results (r.0^0)\n",
        "error: line 3: column 18: expected `->`, found `(int)`",
    ),
    (
        "an unknown region kind",
        "zir 1\nr region blob ()\nr results ()\n",
        "error: line 2: column 14: `blob` is not a region kind",
    ),
    (
        "a reindex that is neither residue nor catalog",
        "zir 1\nr region function ()\nr.0 reindex rows (1, 2, 3) -> (struct)\nr results (r.0^0)\n",
        "error: line 3: column 17: `reindex` takes `residue` or `catalog`, not `rows`",
    ),
    (
        "a fix that is neither lattice nor definedness",
        "zir 1\nr region function ()\nr.0 fix least {} (1) -> (struct)\nr results (r.0^0)\n",
        "error: line 3: column 14: `fix` is `lattice` or `definedness`, not `least`",
    ),
    (
        "a gen that is neither before nor after",
        "zir 1\nr region function ()\nr.0 gen during (1) -> (struct)\nr results (r.0^0)\n",
        "error: line 3: column 15: `gen` tests its guard `before` or `after`, not `during`",
    ),
    (
        "a port op that is neither read nor push",
        "zir 1\nr region port (state out)\nr.0 port peek out (r^0) -> (_; state out)\nr results (r.0^1)\n",
        "error: line 3: column 14: `port` is `read` or `push`, not `peek`",
    ),
    (
        "`main::` with a field after it",
        "zir 1\nr region port (state out)\nr.0 port push main::a.b (r^0, 1) -> (_; state main::a.b)\nr results (r.0^1)\n",
        "error: line 3: column 22: expected `(`, found `.b`",
    ),
    (
        "a port path with a part that is no name",
        "zir 1\nr region port (state out)\nr.0 port push m.9 (r^0, 1) -> (_; state m.9)\nr results (r.0^1)\n",
        "error: line 3: column 17: `9` is not a name: a name starts with an ASCII letter or `_`",
    ),
    (
        "an output list with no `)`",
        "zir 1\nr region function ()\nr.0 prim neg (1) -> (int\nr results (r.0^0)\n",
        "error: line 3: column 25: expected `;`, found the end of the line",
    ),
    (
        "a type form with no `)`",
        "zir 1\nr region function ((tuple int\nr results ()\n",
        "error: line 2: column 30: expected `)`, found the end of the line",
    ),
];

#[test]
fn each_graph_the_reader_refuses_names_the_line_and_column() {
    check(GRAPHS, parse, print);
}

#[test]
fn blank_lines_and_line_order_do_not_change_the_graph() {
    let plain = "zir 1\nr region function (int)\nr.0 prim neg (r^0) -> (int)\nr results (r.0^0)\n";
    let g = round(plain);
    let spaced = "\n\nzir 1\n\nr results (r.0^0)\n   \nr.0 prim neg (r^0) -> (int)\nr region function (int)\n\n";
    assert_eq!(parse(spaced), Ok(g));
}

#[test]
fn ports_named_by_main_and_by_a_field_read_back() {
    round(
        "zir 1\nr region port (state main::files; state m.out)\nr.0 port read main::files (r^0) -> (_; state main::files)\nr.1 port push m.out (r^1, r.0^0) -> (_; state m.out)\nr results (r.0^1, r.1^1)\n",
    );
}

/// Types: each form, read and printed back, or its message.
const TYPES: &[(&str, &str, &str)] = &[
    (
        "a ternary morphism",
        "(-> int String bool)",
        "(-> int String bool)",
    ),
    ("a binary morphism", "(-> int bool)", "(-> int bool)"),
    ("a partial morphism", "(->? int bool)", "(->? int bool)"),
    ("a meet", "(& int (\\ int 0))", "(\\ int 0)"),
    ("an empty meet", "(&)", "_"),
    ("an empty union", "(|)", "(|)"),
    (
        "a complement",
        "(! int)",
        "(| bool rat f32 f64 String #_ tuple struct morphism)",
    ),
    ("a difference of one", "(\\ int)", "int"),
    ("an empty tuple", "(tuple)", "(tuple)"),
    (
        "an atom type form",
        "(#ok (tuple int))",
        "(#ok (tuple int))",
    ),
    (
        "an unknown form",
        "(list int)",
        "error: column 11: `(list …)` is not a type form",
    ),
    (
        "a morphism with one type",
        "(-> int)",
        "error: column 9: `(-> …)` takes 3 types, and has 1",
    ),
    (
        "a partial morphism with three",
        "(->? int int int)",
        "error: column 18: `(->? …)` takes 2 types, and has 3",
    ),
    ("an integer kept as powers", "2^100", "2^100"),
    (
        "a negative integer kept as powers",
        "-5*3^20",
        "-17433922005",
    ),
    (
        "a power that is not a number",
        "2^x",
        "error: column 4: expected a value, found `2^x`",
    ),
    ("a rational type literal", "3r/4r", "75e-2r"),
    ("a float type literal", "1.5", "1.5"),
    ("a string type literal", "\"GET\"", "\"GET\""),
    (
        "an unknown word",
        "widget",
        "error: column 1: `widget` is not a type of the text form; a recursive type has none until step L2 declares types",
    ),
    (
        "a form with no `)`",
        "(tuple int",
        "error: column 11: expected `)`, found the end of the line",
    ),
];

#[test]
fn each_type_form_reads_back_or_is_refused() {
    check(TYPES, parse_type, |t| t.to_string());
}

/// Edges: each fact, read and printed back, or its message.
const EDGES: &[(&str, &str, &str)] = &[
    ("an empty class", "int class {}", "int class {}"),
    ("the class of every integer", "int class any", "int"),
    (
        "an interval from minus infinity",
        "int in [..=5]",
        "int in [..=5]",
    ),
    (
        "an interval with no `..`",
        "int in [3]",
        "error: column 10: expected `..`, found `]`",
    ),
    (
        "a class with no number",
        "int class mod 3",
        "error: column 11: expected a number, found `mod`",
    ),
];

#[test]
fn each_edge_fact_reads_back_or_is_refused() {
    check(EDGES, parse_edge, zedc::zir::text::edge);
}

/// Values: each form, read and printed back, or its message.
const VALUES: &[(&str, &str, &str)] = &[
    ("the empty path", "[]", "[]"),
    (
        "a string with no closing quote",
        "\"abc",
        "error: column 2: the string has no closing `\"`",
    ),
    (
        "a string ending in an escape",
        "\"abc\\",
        "error: column 2: an unfinished escape",
    ),
    (
        "`\\u` without `{`",
        "\"\\u41\"",
        "error: column 2: `\\u` is followed by `{`",
    ),
    (
        "`\\u` of no character",
        "\"\\u{d800}\"",
        "error: column 2: `\\u{d800}` is not a character",
    ),
    (
        "`\\u` of no hex",
        "\"\\u{zz}\"",
        "error: column 2: `\\u{zz}` is not a character",
    ),
    (
        "each one-letter escape",
        "\"\\n\\r\\t\\0\\\\\\\"\\'\\$\"",
        "\"\\n\\r\\t\\0\\\\\\\"'$\"",
    ),
    (
        "an atom with named and positional parts",
        "#e(a: 1, 2)",
        "error: column 12: atom `#e` mixes named and positional payload",
    ),
    (
        "a word that is no number",
        "12ab",
        "error: column 5: expected a value, found `12ab`",
    ),
    (
        "an f32 suffix on an integer",
        "3f32",
        "error: column 5: expected a value, found `3f32`",
    ),
    (
        "an f32 suffix on a bad float",
        "1.2.3f32",
        "error: column 9: expected a value, found `1.2.3f32`",
    ),
    ("an f32 infinity", "inff32", "inff32"),
    (
        "a rational with a decimal point",
        "1.5r",
        "error: column 5: expected a value, found `1.5r`",
    ),
    (
        "a rational over zero",
        "1r/0r",
        "error: column 6: expected a value, found `1r/0r`",
    ),
    ("a rational with an exponent", "1e3r", "1000r"),
    ("a rational that is an integer", "6r/3r", "2r"),
    (
        "a float with two points",
        "1.2.3",
        "error: column 6: expected a value, found `1.2.3`",
    ),
    (
        "a lone minus",
        "-",
        "error: column 2: expected a value, found `-`",
    ),
    ("false", "false", "false"),
    (
        "a large negative integer",
        "-123456789012345678901234567890",
        "-123456789012345678901234567890",
    ),
];

#[test]
fn each_value_form_reads_back_or_is_refused() {
    check(VALUES, parse_value, |v| v.to_string());
}

/// Patterns: each form, read and printed back, or its message.
const PATTERNS: &[(&str, &str, &str)] = &[
    ("an atom pattern with empty parentheses", "#a()", "#a()"),
    ("a fields pattern of one field", "#a(x: n)", "#a(x: n)"),
    (
        "nested fields patterns",
        "#a(x: #b(y: _), z: =1)",
        "#a(x: #b(y: _), z: =1)",
    ),
    (
        "a fields pattern inside a tuple",
        "(#a(x: n), m)",
        "(#a(x: n), m)",
    ),
    (
        "a type test of a union",
        "(is (| int #none))",
        "(is (| int #none))",
    ),
    (
        "a type test with no `)`",
        "(is int",
        "error: column 8: expected `)`, found the end of the line",
    ),
    ("a canonical binder", "$$0", "$$0"),
];

#[test]
fn each_pattern_form_reads_back_or_is_refused() {
    check(PATTERNS, parse_pattern, pattern);
}
