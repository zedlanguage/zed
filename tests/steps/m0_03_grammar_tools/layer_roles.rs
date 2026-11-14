//! The `layer` tool's table of defined words and the positions where a word counts (its module
//! comment): an annotation anywhere, a facet word only in `with name(…)`, a `::x` entry only as
//! a `::` read, a target value only inside `target(…)` or `@require`'s `target:`, any other
//! atom only where it is read (a pattern or a type), the `log` port, words inside string holes,
//! the units of a program directory, and each way the table or a program can fail to read.

use super::{Dir, grammar, tool};
use zed_tools::layer::{self, WordTable};

/// A table with one word of each kind, each at its own layer.
const TABLE: &str = "| Layer | Annotations | Facet words | Words |\n|---|---|---|---|\n\
    | L1 | — | — | `len` |\n\
    | L2 | `@hash` | — | `.fold`, `abs`, `with x`, `zedc build --total`, `nodes:`, `target(…)` |\n\
    | L3 | — | — | `sorted` |\n\
    | L4 | — | `bits` | — |\n\
    | L5 | — | — | `width` |\n\
    | L6 | — | — | `::bytes` |\n\
    | L7 | — | — | `log` |\n\
    | L8 | — | — | `#lost` |\n\
    | L9 | — | — | `#cpu` |\n\
    | L13 | — | — | — |\n\
    | L20 | — | — | — |\n";

/// A spec whose DESIGN.md holds `table` and the real grammars.
fn spec_with(name: &str, table: &str) -> Dir {
    let design = format!(
        "# Test spec\n\n{table}\n```peg\n{}```\n\n```peg\n{}```\n\n```peg\n{}```\n\n\
         ```desugar\n{}```\n",
        grammar("lexical.peg"),
        grammar("syntax.peg"),
        grammar("notation.peg"),
        grammar("desugar.txt"),
    );
    let dir = Dir::new(name);
    dir.write("DESIGN.md", &design);
    dir.write("EXAMPLES.md", "");
    dir
}

/// The hits `layer -v` lists for `program`, as `L<k> <word> <how>` with the padding removed.
fn hits(dir: &Dir, file: &str, program: &str) -> Vec<String> {
    let path = dir.write(file, program);
    let (outcome, out) = tool(layer::run, &[&dir.root(), "-v", &path]);
    assert!(outcome.is_ok(), "{program}\n{outcome:?}\n{out}");
    assert!(!out.contains("PARSE FAIL"), "{program}\n{out}");
    out.lines()
        .filter(|l| l.starts_with("      L"))
        .map(|l| l.split_whitespace().collect::<Vec<_>>().join(" "))
        .collect()
}

#[test]
fn the_table_reads_each_kind_of_word_and_skips_what_is_no_word_of_source() {
    let dir = spec_with("table_kinds", TABLE);
    let t = WordTable::read(&dir.at("DESIGN.md")).expect("the table reads");
    for (w, k) in [
        ("len", Some(1)),
        ("@hash", Some(2)),
        ("sorted", Some(3)),
        ("bits", Some(4)),
        ("width", Some(5)),
        ("bytes", Some(6)),
        ("#lost", Some(8)),
        ("#cpu", Some(9)),
        // Words the table names in prose.
        ("sanitize", Some(13)),
        ("serialize", Some(20)),
        ("Json", Some(20)),
        ("Csv", Some(20)),
        // Spans that need types, compiler modes, `with` facets, arguments and calls.
        (".fold", None),
        ("abs", None),
        ("with x", None),
        ("x", None),
        ("zedc build --total", None),
        ("nodes", None),
        ("nodes:", None),
        ("target", None),
        // The log port is counted as a port, not as a form.
        ("log", None),
        ("missing", None),
    ] {
        assert_eq!(t.layer_of(w), k, "{w}");
    }
}

#[test]
fn a_table_that_does_not_read_is_refused_with_the_reason() {
    let cases = [
        ("# Test spec\n\nno table\n", "no table of defined words"),
        (
            "| Layer | Annotations | Facet words | Words |\n|---|---|---|---|\n| L1 | — |\n",
            "a table row with too few columns",
        ),
        (
            "| Layer | Annotations | Facet words | Words |\n|---|---|---|---|\n| x | — | — | — |\n",
            "a table row with no layer",
        ),
        (
            "| Layer | Annotations | Facet words | Words |\n|---|---|---|---|\n| L1 | — | — | `a b` |\n",
            "unparsed table span",
        ),
    ];
    for (i, (text, want)) in cases.into_iter().enumerate() {
        let dir = Dir::new(&format!("table_bad_{i}"));
        let path = dir.write("DESIGN.md", text);
        let got = WordTable::read(&path);
        assert!(
            got.as_ref().is_err_and(|e| e.contains(want)),
            "{text}\n{got:?}"
        );
    }
}

#[test]
fn each_word_counts_only_in_its_own_position() {
    let dir = spec_with("roles", TABLE);
    let cases: &[(&str, &[&str])] = &[
        // An annotation counts wherever it appears.
        ("@hash\nf(x: int) -> int = x;\n", &["L2 @hash annotation"]),
        // A facet word in `with name(…)`, a form used as a facet, and a facet the table lacks.
        ("f(x: int) -> int = x with bits(8);\n", &["L4 bits facet"]),
        (
            "f(x: int) -> int = x with width(8);\n",
            &["L5 width facet word"],
        ),
        (
            "f(x: int) -> int = x with mine(8);\n",
            &["L12 mine user facet"],
        ),
        ("f(x: int with bits(8)) -> int = x;\n", &["L4 bits facet"]),
        // A facet word outside `with` is not a facet.
        ("f(bits: int) -> int = bits;\n", &[]),
        // A `::` read, and the same word as a name.
        ("f(x: [int]) -> int = x::bytes;\n", &["L6 ::bytes read"]),
        ("f(bytes: int) -> int = bytes;\n", &[]),
        ("f(x: [int]) -> int = x::other;\n", &[]),
        // An atom read in a type or a pattern counts; one the program builds does not.
        ("f(x: #lost | int) -> int = 1;\n", &["L8 #lost atom read"]),
        (
            "f(x: #lost | int) -> int = match x { #lost -> 0, _ -> 1 };\n",
            &["L8 #lost atom read"],
        ),
        ("f() -> #lost = #lost;\n", &["L8 #lost atom read"]),
        ("f() -> int = #lost else 1;\n", &[]),
        // A target value counts inside `target(…)` and `@require`'s `target:` only.
        (
            "@require(target: #cpu)\nf() -> int = 1;\n",
            &["L9 #cpu target value"],
        ),
        (
            "f(x: int) -> int = x with target(#cpu);\n",
            &["L9 #cpu target value", "L12 target user facet"],
        ),
        ("f(x: #cpu | int) -> int = 1;\n", &[]),
        // The log port, as a push target and as a name; a parameter named log shadows it.
        (
            "main(m: MainArgs) { m.log <- [\"a\"]; }\n",
            &["L7 log the log port"],
        ),
        ("f() -> int = log;\n", &["L7 log the log port"]),
        ("f(log: int) -> int = log;\n", &[]),
        // A word the table names in prose.
        ("f(x: int) -> int = sanitize(x);\n", &["L13 sanitize form"]),
        // A word inside a string hole, and inside a hole of a string in a hole.
        (
            "f(x: [int]) -> string = \"${sorted(x)}\";\n",
            &["L3 sorted form"],
        ),
        (
            "f(x: [int]) -> string = \"a${\"b${sorted(x)}\"}\";\n",
            &["L3 sorted form"],
        ),
    ];
    let mut wrong = Vec::new();
    for (i, (program, want)) in cases.iter().enumerate() {
        let got = hits(
            &dir,
            &format!("p{i}.zed"),
            &format!("// layer L1\n{program}"),
        );
        let want: Vec<String> = want.iter().map(|s| s.to_string()).collect();
        let (mut g, mut w) = (got.clone(), want.clone());
        g.sort();
        w.sort();
        if g != w {
            wrong.push(format!("{program}  got  {got:?}\n  want {want:?}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn a_program_is_its_main_file_and_every_zed_file_under_its_directory() {
    let dir = spec_with("units", TABLE);
    let main = dir.write("p.zed", "// layer L3\nf(x: [int]) -> int = g(x);\n");
    std::fs::create_dir_all(dir.at("p/sub")).unwrap();
    dir.write("p/b.zed", "g(x: [int]) -> int = h(sorted(x));\n");
    dir.write("p/notes.txt", "sorted(\n");
    dir.write("p/sub/a.zed", "h(x: [int]) -> int = 1;\n");
    // A link to a directory is skipped, so the unit it holds is not read.
    let other = Dir::new("units_linked");
    other.write("bad.zed", "h(");
    std::os::unix::fs::symlink(other.root(), dir.at("p/linked")).unwrap();
    assert_eq!(
        layer::program_units(&main),
        Ok(vec![main.clone(), dir.at("p/b.zed"), dir.at("p/sub/a.zed")])
    );
    let (outcome, out) = tool(layer::run, &[&dir.root(), &main]);
    assert_eq!(outcome, Ok(true), "{out}");
    let row = out.lines().nth(1).expect("a row");
    let cols: Vec<&str> = row.split_whitespace().collect();
    assert_eq!(cols[1], "3", "{out}");
    assert!(row.contains("L3 (sorted)"), "{out}");

    // A file with no directory is one unit.
    let lone = dir.write("q.zed", "f(x: int) -> int = x;\n");
    assert_eq!(layer::program_units(&lone), Ok(vec![lone.clone()]));
}

#[test]
fn a_unit_that_does_not_parse_fails_its_program_and_names_the_unit() {
    let dir = spec_with("unit_fails", TABLE);
    let main = dir.write("p.zed", "// layer L1\nf(x: int) -> int = x;\n");
    std::fs::create_dir_all(dir.at("p")).unwrap();
    dir.write("p/a.zed", "g(\n");
    dir.write("p/b.zed", "h() -> string = \"${+}\";\n");
    let good = dir.write("q.zed", "// layer L1\nf(x: int) -> int = x;\n");
    let (outcome, out) = tool(layer::run, &[&dir.root(), &main, &good]);
    assert_eq!(outcome, Ok(false), "{out}");
    let fail = out
        .lines()
        .find(|l| l.contains("PARSE FAIL"))
        .unwrap_or_else(|| panic!("{out}"));
    assert!(fail.starts_with("p.zed "), "{out}");
    assert!(
        fail.contains("a.zed: ") && fail.contains("; b.zed: "),
        "{out}"
    );
    assert!(
        out.lines()
            .any(|l| l.starts_with("q.zed ") && l.ends_with(" yes")),
        "{out}"
    );
}

#[test]
fn a_label_is_a_layer_comment_that_ends_its_word() {
    for (text, want) in [
        ("// layer L3\n", Some(3)),
        ("// layer L12 rest\n", Some(12)),
        ("// layer L3", Some(3)),
        ("// layer L3,", Some(3)),
        ("// layer L3x\n", None),
        ("// layer L3_\n", None),
        ("// layer L\n", None),
        ("// layer 3\n", None),
        ("  // layer L3\n", None),
        ("f() = 1;\n", None),
    ] {
        assert_eq!(layer::label_at(text), want, "{text:?}");
    }
}

#[test]
fn a_label_above_both_mechanical_layers_is_marked_and_no_label_is_none() {
    let dir = spec_with("labels", TABLE);
    let above = dir.write("above.zed", "// layer L9\nf(x: int) -> int = x;\n");
    let none = dir.write("none.zed", "f(x: int) -> int = x;\n");
    let zero = dir.write("zero.zed", "// layer L0\nf(x: int) -> int = x;\n");
    let (outcome, out) = tool(layer::run, &[&dir.root(), &above, &none, &zero]);
    assert_eq!(outcome, Ok(false), "{out}");
    let row = |name: &str| {
        out.lines()
            .find(|l| l.starts_with(name))
            .unwrap_or_else(|| panic!("{out}"))
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert!(
        row("above.zed").ends_with("L9 L9 yes (label above ring and table)"),
        "{out}"
    );
    assert!(
        row("none.zed").contains(" none ") && row("none.zed").ends_with(" NO"),
        "{out}"
    );
    assert!(
        row("zero.zed").contains(" none ") && row("zero.zed").ends_with(" NO"),
        "{out}"
    );
}
