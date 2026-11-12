//! Step M0.3: the grammar tools and the hand-run commands of `zed-tools`.
//!
//! CI does not read the spec repository, so each test builds a small spec of its own: the
//! grammars `sync` copied into `zed/grammar`, a table of defined words, and the fences the test
//! needs. A spec author runs these tools on the real spec; the tests here run the same `run`
//! functions the commands call.

mod cite;
mod conflicts;
mod llp;
mod plan;
mod scaling;
mod split;

use std::fs;

use zed_tools::spec::Spec;
use zed_tools::{audit, cases, check, fences, fuzz, layer, progress, ring, sync};

pub(crate) use zed_tests::step_helpers::m0_03_grammar_tools::{
    Dir, design, design_of, fence, grammar, spec_dir, tool,
};

/// A function that doubles a number, which parses at a low ring.
const DOUBLE: &str = "double(x: int) -> int = x * 2;";

#[test]
fn check_accepts_a_spec_whose_fences_all_parse() {
    let dir = spec_dir("check_ok", &design(&fence(DOUBLE)), &fence(DOUBLE));
    let (outcome, out) = tool(check::run, &[&dir.root()]);
    assert_eq!(outcome, Ok(true), "{out}");
    assert!(out.contains("desugar rules"), "{out}");
}

#[test]
fn check_rejects_a_fence_that_does_not_parse_and_names_its_line() {
    let body = format!("{}\n{}", fence(DOUBLE), fence("double(x: int -> int"));
    let dir = spec_dir("check_bad", &design(&body), "");
    let (outcome, out) = tool(check::run, &[&dir.root()]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(
        out.contains("DESIGN.md:") && out.contains(" FAIL "),
        "{out}"
    );
}

#[test]
fn check_of_a_fence_that_is_not_there_says_so() {
    let dir = spec_dir("check_missing", &design(""), "");
    let (outcome, out) = tool(check::run, &[&dir.root(), "DESIGN.md:1"]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(out.contains("NO FENCE AT DESIGN.md:1"), "{out}");
}

#[test]
fn check_rejects_a_rule_with_no_definition() {
    let syn = format!(
        "{}\nStray         = NoSuchRule     L1\n",
        grammar("syntax.peg")
    );
    let text = design_of(
        &grammar("lexical.peg"),
        &syn,
        &grammar("notation.peg"),
        &grammar("desugar.txt"),
        "",
    );
    let dir = spec_dir("check_undefined", &text, "");
    let (outcome, out) = tool(check::run, &[&dir.root()]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(out.contains("NoSuchRule"), "{out}");
}

#[test]
fn check_rejects_a_production_with_no_desugaring_rule() {
    let desugar: String = grammar("desugar.txt")
        .lines()
        .filter(|l| !l.starts_with("Name "))
        .map(|l| format!("{l}\n"))
        .collect();
    let text = design_of(
        &grammar("lexical.peg"),
        &grammar("syntax.peg"),
        &grammar("notation.peg"),
        &desugar,
        "",
    );
    let dir = spec_dir("check_desugar", &text, "");
    let (outcome, out) = tool(check::run, &[&dir.root()]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(out.contains("Name"), "{out}");
}

#[test]
fn a_fence_left_open_stops_the_tool_with_its_line() {
    let dir = spec_dir("open_fence", &design("```zed\nx = 1\n"), "");
    let (outcome, _) = tool(check::run, &[&dir.root()]);
    let why = outcome.expect_err("an open fence stops the tool");
    assert!(why.contains("the fence is not closed"), "{why}");
}

#[test]
fn a_spec_with_too_few_grammars_is_refused() {
    let dir = spec_dir("few_pegs", "```peg\nA = 'a' L1\n```\n", "");
    let why = Spec::open(&dir.root()).expect_err("two grammars are missing");
    assert!(why.contains("fewer than three peg fences"), "{why}");
}

#[test]
fn a_rule_defined_in_both_grammars_is_refused() {
    let doc = format!(
        "{}\nUnit          = Name           L1\n",
        grammar("notation.peg")
    );
    let text = design_of(
        &grammar("lexical.peg"),
        &grammar("syntax.peg"),
        &doc,
        &grammar("desugar.txt"),
        "",
    );
    let dir = spec_dir("twice", &text, "");
    let why = Spec::open(&dir.root()).expect_err("a duplicate rule");
    assert!(why.contains("Unit"), "{why}");
}

#[test]
fn a_missing_spec_is_reported_with_its_path() {
    let (outcome, _) = tool(check::run, &["/no/such/spec"]);
    assert!(
        outcome
            .expect_err("no spec")
            .contains("/no/such/spec/DESIGN.md")
    );
}

#[test]
fn fences_counts_the_fences_and_lines_of_both_documents() {
    let dir = spec_dir(
        "fences",
        &fence("a\nb"),
        &format!("{}{}", fence("c"), fence("d")),
    );
    let (outcome, out) = tool(fences::run, &[&dir.root()]);
    assert_eq!(outcome, Ok(true));
    assert_eq!(out, "3 4 lines\n");
}

#[test]
fn cases_passes_on_the_real_cases_and_fails_on_a_wrong_bracketing() {
    let dir = spec_dir("cases", &design(""), "");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let cases_dir = Dir::new("cases_files");
    cases_dir.write("cases.txt", "Expr ::: a + b * c ::: (a + (b * c))\n");
    cases_dir.write("leftrec.txt", "");
    let run = |dir: String| {
        let mut out = String::new();
        (cases::run_files(&spec, &dir, &mut out), out)
    };
    let (outcome, out) = run(cases_dir.root());
    assert_eq!(outcome, Ok(true), "{out}");

    cases_dir.write("cases.txt", "Expr ::: a + b * c ::: ((a + b) * c)\n");
    let (outcome, out) = run(cases_dir.root());
    assert_eq!(outcome, Ok(false), "{out}");
}

#[test]
fn ring_gives_the_lowest_ring_of_each_file_and_fails_on_one_that_does_not_parse() {
    let dir = spec_dir("ring", &design(""), "");
    let good = dir.write("good.zed", DOUBLE);
    let high = dir.write("high.zed", "main(m: MainArgs) { m.stdout <- [\"a\"]; }\n");
    let (outcome, out) = tool(ring::run, &[&dir.root(), &good, &high]);
    assert_eq!(outcome, Ok(true), "{out}");
    assert!(out.starts_with(&format!("{good} L")), "{out}");

    let bad = dir.write("bad.zed", "double(");
    let (outcome, out) = tool(ring::run, &[&dir.root(), &good, &bad]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(out.contains(&format!("{bad} FAIL")), "{out}");
}

#[test]
fn layer_agrees_with_a_right_label_and_rejects_a_label_below_a_word_of_the_program() {
    let dir = spec_dir("layer", &design(""), "");
    let (_, rung) = tool(ring::run, &[&dir.root(), &dir.write("r.zed", DOUBLE)]);
    let k = rung.split_whitespace().last().expect("a ring");
    let right = dir.write("right.zed", &format!("// layer {k}\n{DOUBLE}\n"));
    let (outcome, out) = tool(layer::run, &[&dir.root(), &right]);
    assert_eq!(outcome, Ok(true), "{out}");

    let uses = "// layer L1\nnames(x: [int]) -> [int] = sorted(x);\n";
    let wrong = dir.write("wrong.zed", uses);
    let (outcome, out) = tool(layer::run, &[&dir.root(), "-v", &wrong]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(out.contains("L3 (sorted)") && out.contains(" NO"), "{out}");
}

#[test]
fn layer_does_not_count_a_word_the_program_binds_itself() {
    let dir = spec_dir("shadow", &design(""), "");
    let text = "// layer L2\nsorted(x: int) -> int = x;\nf(y: int) -> int = sorted(y);\n";
    let program = dir.write("shadow.zed", text);
    let (_, out) = tool(layer::run, &[&dir.root(), &program]);
    assert!(!out.contains("(sorted)"), "{out}");
}

#[test]
fn layer_reads_the_field_names_of_a_type_as_names_the_program_binds() {
    // `sorted` is an L3 word of the table. Named in a type, as the field of an atom, a record
    // or a one-field type, as a named parameter of a function type, or as a type variable of a
    // `for` bound, and named as the acknowledgment of a push, it is the program's own name, as
    // a struct field is, so none of these programs uses the word.
    let dir = spec_dir("type_fields", &design(""), "");
    let programs = [
        "type T = #a(sorted: int);\nf(x: T) -> T = x;\n",
        "f(x: {sorted: int, b: int}) -> int = x.b;\n",
        "f(x: (sorted: int)) -> int = 1;\n",
        "f(g: (sorted: int) -> int) -> int = g(1);\n",
        "f(g: (sorted: int, b: int) -> int) -> int = g(1, 2);\n",
        "f(x: sorted) -> sorted for sorted in int | bool = x;\n",
        "main(m: MainArgs) { sorted = m.stdout <- [\"a\"]; }\n",
    ];
    for (i, text) in programs.iter().enumerate() {
        let program = dir.write(&format!("p{i}.zed"), &format!("// layer L1\n{text}"));
        let (outcome, out) = tool(layer::run, &[&dir.root(), "-v", &program]);
        assert!(
            outcome.is_ok() && !out.contains("PARSE FAIL"),
            "{text}\n{out}"
        );
        assert!(!out.contains("sorted"), "{text}\n{out}");
    }
    // A use of the word in an expression still counts.
    let uses = "// layer L2\ntype T = #a(n: int);\nf(x: [int]) -> [int] = sorted(x);\n";
    let program = dir.write("uses.zed", uses);
    let (outcome, out) = tool(layer::run, &[&dir.root(), &program]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(out.contains("L3 (sorted)"), "{out}");
}

#[test]
fn audit_names_what_a_program_needs_and_fails_when_the_checklist_lacks_it() {
    let dir = spec_dir("audit", &design(""), "");
    let program = dir.write("p.zed", &format!("// layer L3\n{DOUBLE}\n"));
    let (outcome, out) = tool(audit::run, &[&dir.root(), &program]);
    assert_eq!(outcome, Ok(true), "{out}");
    assert!(
        out.lines().any(|l| l.starts_with('L') && l.contains('#')),
        "{out}"
    );

    let list = dir.write("ZED0.md", "Nothing here.\n");
    let (outcome, out) = tool(audit::run, &[&dir.root(), &program, "--checklist", &list]);
    assert_eq!(outcome, Ok(false), "{out}");

    let (outcome, _) = tool(audit::run, &[&dir.root()]);
    assert!(outcome.expect_err("no program").contains("usage"));
}

/// A program of two functions that needs the word `len` of the test spec's table.
const LENGTHS: &str =
    "// layer L3\ndouble(x: int) -> int = x * 2;\nsize(x: [int]) -> int = len(x);\n";

/// Checklist entries, each with the layer of its row.
type Entries = Vec<(u32, String)>;

/// The audit's report on `program`, with no checklist: each needed alternative as
/// (layer, `Rule#i`) and each needed word as (layer, word).
fn audit_needs(spec: &str, program: &str) -> (Entries, Entries) {
    let (outcome, out) = tool(audit::run, &[spec, program]);
    assert_eq!(outcome, Ok(true), "{out}");
    let layer = |s: &str| s.strip_prefix('L')?.parse::<u32>().ok();
    let (mut alts, mut words) = (Vec::new(), Vec::new());
    for l in out.lines() {
        let mut parts = l.split_whitespace();
        let (Some(k), Some(entry)) = (parts.next().and_then(layer), parts.next()) else {
            continue;
        };
        if l.starts_with("      L") {
            words.push((k, entry.to_string()));
        } else if l.starts_with('L') && entry.contains('#') {
            alts.push((k, entry.to_string()));
        }
    }
    (alts, words)
}

/// A checklist whose Part A lists `alts` and `words`, each in the row of its layer.
fn checklist(alts: &[(u32, String)], words: &[(u32, String)]) -> String {
    let mut rows: std::collections::BTreeMap<u32, (String, String)> = Default::default();
    for (k, a) in alts {
        rows.entry(*k).or_default().0 += &format!(" `{a}`");
    }
    for (k, w) in words {
        rows.entry(*k).or_default().1 += &format!(" `{w}`");
    }
    let mut text = "# Checklist\n\n## Part A: what the program needs\n\n\
                    | Layer | Grammar alternatives | Defined words |\n|---|---|---|\n"
        .to_string();
    for (k, (a, w)) in rows {
        let cell = |s: String| if s.is_empty() { " —".into() } else { s };
        text += &format!("| L{k} |{} |{} |\n", cell(a), cell(w));
    }
    text + "\n## Part B: more\n\n`Port#0` and `String` here are prose, not entries.\n"
}

#[test]
fn audit_accepts_a_checklist_that_lists_exactly_what_the_program_needs() {
    let dir = spec_dir("audit_exact", &design(""), "");
    let program = dir.write("p.zed", LENGTHS);
    let (alts, words) = audit_needs(&dir.root(), &program);
    assert!(
        !alts.is_empty() && words == [(1, "len".to_string())],
        "{words:?}"
    );
    let list = dir.write("ZED0.md", &checklist(&alts, &words));
    let (outcome, out) = tool(audit::run, &[&dir.root(), &program, "--checklist", &list]);
    assert_eq!(outcome, Ok(true), "{out}");
    let n = alts.len() + words.len();
    assert!(
        out.contains(&format!("checklist: {n} needed, 0 missing\n")),
        "{out}"
    );
    assert!(
        out.contains(&format!("checklist: {n} listed, 0 not needed\n")),
        "{out}"
    );
}

#[test]
fn audit_fails_on_a_listed_entry_the_grammar_or_the_table_no_longer_has() {
    let dir = spec_dir("audit_stale", &design(""), "");
    let program = dir.write("p.zed", LENGTHS);
    let (mut alts, mut words) = audit_needs(&dir.root(), &program);
    // A rule that was removed, alternatives past the end of a rule of one alternative and of a
    // rule of many, a word the table of defined words does not list, and a word it lists that
    // the program does not use.
    alts.push((1, "Port#0".into()));
    alts.push((1, "Unit#1".into()));
    alts.push((2, "Primary#400".into()));
    words.push((1, "String".into()));
    words.push((3, "sorted".into()));
    let list = dir.write("ZED0.md", &checklist(&alts, &words));
    let (outcome, out) = tool(audit::run, &[&dir.root(), &program, "--checklist", &list]);
    assert_eq!(outcome, Ok(false), "{out}");
    let g = Spec::open(&dir.root()).expect("the spec reads").syntactic;
    assert_eq!(g.rules[g.rule("Unit").expect("a rule Unit")].alts.len(), 1);
    let primary = g.rules[g.rule("Primary").expect("a rule Primary")]
        .alts
        .len();
    for line in [
        " 5 not needed `Port#0` `Primary#400` `Unit#1` `String` `sorted`\n".to_string(),
        "  `Port#0`, in the row L1 of Part A of ZED0.md, is not needed: the grammar has no rule \
         Port."
            .to_string(),
        "  `Unit#1`, in the row L1 of Part A of ZED0.md, is not needed: rule Unit has one \
         alternative, numbered 0."
            .to_string(),
        format!(
            "  `Primary#400`, in the row L2 of Part A of ZED0.md, is not needed: rule Primary has \
             {primary} alternatives, numbered 0 to {}.",
            primary - 1
        ),
        "  `String`, in the row L1 of Part A of ZED0.md, is not needed: the table of defined \
         words in DESIGN.md does not list it."
            .to_string(),
        "  `sorted`, in the row L3 of Part A of ZED0.md, is not needed: the table of defined words \
         lists it at L3, but p.zed does not use it."
            .to_string(),
    ] {
        assert!(out.contains(&line), "no line {line:?} in\n{out}");
    }
    assert!(out.contains(", 0 missing\n"), "{out}");
    assert!(out.contains("To repair ZED0.md"), "{out}");
}

#[test]
fn audit_fails_on_an_alternative_listed_under_its_old_index_and_names_both() {
    let dir = spec_dir("audit_renumbered", &design(""), "");
    let program = dir.write("p.zed", LENGTHS);
    let (mut alts, words) = audit_needs(&dir.root(), &program);
    // A needed alternative listed under the index of another alternative of its rule, one the
    // program does not need, as when an alternative was inserted above it.
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let g = &spec.syntactic;
    let listed: std::collections::HashSet<String> = alts.iter().map(|a| a.1.clone()).collect();
    let (at, old, new) = alts
        .iter()
        .enumerate()
        .find_map(|(at, (_, entry))| {
            let (rule, _) = entry.split_once('#')?;
            let n = g.rules[g.rule(rule)?].alts.len();
            let other = (0..n)
                .map(|j| format!("{rule}#{j}"))
                .find(|e| !listed.contains(e))?;
            Some((at, other, entry.clone()))
        })
        .expect("a needed alternative whose rule has one the program does not need");
    alts[at].1 = old.clone();
    let list = dir.write("ZED0.md", &checklist(&alts, &words));
    let (outcome, out) = tool(audit::run, &[&dir.root(), &program, "--checklist", &list]);
    assert_eq!(outcome, Ok(false), "{out}");
    let (rule, i) = new.split_once('#').unwrap();
    let (_, j) = old.split_once('#').unwrap();
    for line in [
        format!(", 1 missing `{new}`\n"),
        format!(
            "  `{new}` is missing from Part A of ZED0.md: p.zed needs alternative {i} of rule \
             {rule}, `"
        ),
        format!(", 1 not needed `{old}`\n"),
        format!(
            "  `{old}`, in the row L{} of Part A of ZED0.md, is not needed: alternative {j} of \
             rule {rule}, `",
            alts[at].0
        ),
        "still parses to the same trees.".to_string(),
    ] {
        assert!(out.contains(&line), "no text {line:?} in\n{out}");
    }
}

#[test]
fn audit_fails_on_a_checklist_with_no_part_a() {
    let dir = spec_dir("audit_no_part_a", &design(""), "");
    let program = dir.write("p.zed", LENGTHS);
    let list = dir.write(
        "ZED0.md",
        "Nothing here, and `Unit#0` outside any Part A.\n",
    );
    let (outcome, out) = tool(audit::run, &[&dir.root(), &program, "--checklist", &list]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(out.contains("ZED0.md has no section `## Part A`"), "{out}");
}

#[test]
fn audit_fails_on_a_row_of_part_a_it_cannot_read_and_names_its_line() {
    let dir = spec_dir("audit_bad_rows", &design(""), "");
    let program = dir.write("p.zed", LENGTHS);
    let (alts, words) = audit_needs(&dir.root(), &program);
    let good = checklist(&alts, &words);
    let (head, tail) = good.split_once("\n## Part B").expect("a Part B");
    let first = head.lines().count() + 1;
    let bad = [
        "| L1–L6 | `Unit#0` | — |",
        "| L2 | Unit#0 | — |",
        "| L3 | `Unit#0` |",
        "| L4 | — | `len |",
        "L5 | `Unit#0` | — |",
    ];
    let text = format!("{head}{}\n\n## Part B{tail}", bad.join("\n"));
    let list = dir.write("ZED0.md", &text);
    let (outcome, out) = tool(audit::run, &[&dir.root(), &program, "--checklist", &list]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(
        out.contains("checklist: 5 lines of Part A of ZED0.md cannot be read"),
        "{out}"
    );
    let expect = [
        "its first cell is `L1–L6`, but a row starts with one layer, written L and a number, such as L3",
        "its column of grammar alternatives has `Unit#0` outside backticks",
        "it has 2 cells, but a row of Part A has 3",
        "its column of defined words has a backtick with no closing backtick",
        "it does not start with a bar `|`",
    ];
    for (k, (row, what)) in bad.iter().zip(expect).enumerate() {
        let line = format!("  line {} of ZED0.md cannot be read: {what}", first + k);
        assert!(out.contains(&line), "{line}\n---\n{out}");
        assert!(out.contains(&format!("\n    {row}\n")), "{row}\n---\n{out}");
    }
    assert!(!out.contains("missing"), "{out}");

    // A table with no header row: its first row would be taken as the header.
    let list = dir.write("NOHEAD.md", "## Part A\n\n| L1 | `Unit#0` | — |\n");
    let (outcome, out) = tool(audit::run, &[&dir.root(), &program, "--checklist", &list]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(
        out.contains("checklist: 1 line of Part A of NOHEAD.md cannot be read")
            && out.contains("  line 3 of NOHEAD.md cannot be read: it is the first row of the table, which is the header"),
        "{out}"
    );
}

#[test]
fn audit_names_every_reason_a_line_of_part_a_cannot_be_read() {
    let dir = spec_dir("audit_bad_reasons", &design(""), "");
    let program = dir.write("p.zed", LENGTHS);
    let (alts, words) = audit_needs(&dir.root(), &program);
    let good = checklist(&alts, &words);
    let (head, tail) = good.split_once("\n## Part B").expect("a Part B");
    let first = head.lines().count() + 1;
    let bad = [
        // A layer that is a range, an entry outside backticks and a backtick left open.
        "| L1–L6 | Unit#0 | `len |",
        // No bar at either end, an entry with a space in it, and text outside backticks.
        "L7 | `Unit #0` x `Unit#0` | —",
    ];
    let text = format!("{head}{}\n\n## Part B{tail}", bad.join("\n"));
    let list = dir.write("ZED0.md", &text);
    let (outcome, out) = tool(audit::run, &[&dir.root(), &program, "--checklist", &list]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(
        out.contains("checklist: 2 lines of Part A of ZED0.md cannot be read"),
        "{out}"
    );
    let expect = [
        format!(
            "  line {first} of ZED0.md cannot be read, for 3 reasons: its first cell is `L1–L6`, \
             but a row starts with one layer, written L and a number, such as L3; its column of \
             grammar alternatives has `Unit#0` outside backticks; and its column of defined \
             words has a backtick with no closing backtick. The line is:\n    {}\n",
            bad[0]
        ),
        format!(
            "  line {} of ZED0.md cannot be read, for 4 reasons: it does not start with a bar \
             `|`, as a row of a table does; it does not end with a bar `|`, as a row of a table \
             does; its column of grammar alternatives has `Unit #0` in backticks, but an entry in \
             backticks is one name with no spaces; and its column of grammar alternatives has \
             `x` outside backticks. The line is:\n    {}\n",
            first + 1,
            bad[1]
        ),
    ];
    for line in expect {
        assert!(out.contains(&line), "{line}\n---\n{out}");
    }
}

#[test]
fn audit_fails_on_an_entry_in_the_row_of_another_layer_and_names_its_line() {
    let dir = spec_dir("audit_wrong_row", &design(""), "");
    let program = dir.write("p.zed", LENGTHS);
    let (mut alts, mut words) = audit_needs(&dir.root(), &program);
    assert!(
        alts.len() >= 2 && words == [(1, "len".to_string())],
        "{alts:?}"
    );
    let list = dir.write("ZED0.md", &checklist(&alts, &words));
    let (outcome, out) = tool(audit::run, &[&dir.root(), &program, "--checklist", &list]);
    assert_eq!(outcome, Ok(true), "{out}");
    let n = alts.len() + words.len();
    assert!(
        out.contains(&format!(
            "checklist: {n} needed entries listed, 0 in the row of another layer\n"
        )),
        "{out}"
    );

    // An alternative moved to a row of its own, the word moved to the row of a higher layer,
    // and an alternative listed a second time, in the row of another layer.
    let (moved, twice) = (alts[0].clone(), alts[1].clone());
    alts[0].0 = moved.0 + 7;
    words[0].0 = 2;
    alts.push((twice.0 + 8, twice.1.clone()));
    let text = checklist(&alts, &words);
    let line_of = |k: u32| {
        1 + text
            .lines()
            .position(|l| l.starts_with(&format!("| L{k} |")))
            .expect("a row of the layer")
    };
    let list = dir.write("ZED0.md", &text);
    let (outcome, out) = tool(audit::run, &[&dir.root(), &program, "--checklist", &list]);
    assert_eq!(outcome, Ok(false), "{out}");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let g = &spec.syntactic;
    let (rule, i) = moved.1.split_once('#').unwrap();
    assert_eq!(
        g.rules[g.rule(rule).unwrap()].alts[i.parse::<usize>().unwrap()].layer,
        moved.0
    );
    let (rule2, i2) = twice.1.split_once('#').unwrap();
    for line in [
        ", 0 missing\n".to_string(),
        ", 0 not needed\n".to_string(),
        format!("checklist: {n} needed entries listed, 3 in the row of another layer `"),
        format!(
            "  `{}`, on line {} of ZED0.md, is in the row L{} of Part A, but p.zed needs \
             alternative {i} of rule {rule}, `",
            moved.1,
            line_of(moved.0 + 7),
            moved.0 + 7
        ),
        format!("`, which is at L{}.\n", moved.0),
        format!(
            "  `len`, on line {} of ZED0.md, is in the row L2 of Part A, but p.zed uses the word \
             `len`, which is at L1.\n",
            line_of(2)
        ),
        format!(
            "  `{}`, on line {} of ZED0.md, is in the row L{} of Part A, but p.zed needs \
             alternative {i2} of rule {rule2}, `",
            twice.1,
            line_of(twice.0 + 8),
            twice.0 + 8
        ),
        format!(
            "`, which is at L{0}, and line {1} lists it in the row L{0} already.\n",
            twice.0,
            line_of(twice.0)
        ),
        "Move each entry that is in the row of another layer to the row of its own layer"
            .to_string(),
    ] {
        assert!(out.contains(&line), "no text {line:?} in\n{out}");
    }
}

#[test]
fn fuzz_gives_the_same_report_for_the_same_seed() {
    let dir = spec_dir("fuzz", &design(""), "");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let run = |n, seed| {
        let mut out = String::new();
        (fuzz::run_on(&spec, n, seed, &mut out), out)
    };
    let (outcome, first) = run(5, 7);
    assert_eq!(outcome, Ok(true), "{first}");
    assert_eq!(run(5, 7).1, first);
    assert_ne!(run(5, 8).1, first);
}

/// The fuzz of `spec` with `n` sentences per ring at `seed`: its outcome and what it printed.
fn fuzz_of(spec: &Spec, n: usize, seed: i64) -> (zed_tools::Outcome, String) {
    let mut out = String::new();
    (fuzz::run_on(spec, n, seed, &mut out), out)
}

/// The real syntactic grammar with the `break` of before review round 2 put back in `Primary`:
/// an optional operand, so in `if c || break { 1 } else { 2 }` the operand takes the body.
fn syntax_with_old_break() -> String {
    let syn = grammar("syntax.peg");
    let loop_line = syn
        .lines()
        .find(|l| l.trim_start().starts_with("| ~Loop "))
        .expect("Primary has a Loop line");
    let old = format!(
        "{loop_line}\n              | 'break' Expr12?                                                    L6"
    );
    syn.replacen(loop_line, &old, 1)
}

/// The fuzz finds a sentence the old `break` derives with every lookahead satisfied but the
/// parser rejects. Seed 122 at five sentences per ring was found by running seeds 1 to 500 (the
/// first of them that finds it at this size; 149 and 329 do too) after `with carryForward`
/// joined the grammar (MUTABLE-to-initial-facet); if a grammar change moves it, run the seeds
/// again. The same seed on the real grammar finds nothing, so the failure comes from the change.
#[test]
fn fuzz_reports_a_sentence_the_old_break_derives_but_the_parser_rejects() {
    const N: usize = 5;
    const SEED: i64 = 122;
    let real = spec_dir("fuzz_real", &design(""), "");
    let real = Spec::open(&real.root()).expect("the spec reads");
    let (outcome, out) = fuzz_of(&real, N, SEED);
    assert_eq!(outcome, Ok(true), "{out}");

    let text = design_of(
        &grammar("lexical.peg"),
        &syntax_with_old_break(),
        &grammar("notation.peg"),
        &grammar("desugar.txt"),
        "",
    );
    let old = spec_dir("fuzz_old_break", &text, "");
    let old = Spec::open(&old.root()).expect("the spec reads");
    let (outcome, out) = fuzz_of(&old, N, SEED);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(
        out.lines()
            .any(|l| l.starts_with("L6 derived but rejected: ") && l.contains("break")),
        "{out}"
    );
    assert!(!out.contains("derived but rejected 0"), "{out}");
    assert!(out.ends_with("RESULT: FAIL\n"), "{out}");
}

/// Many sentences on the real grammar: every one generated at a ring parses at it with the same
/// tree at every ring above, and none whose derivation passed its lookaheads is rejected. Five
/// hundred per ring take about 5 s.
#[test]
fn fuzz_of_the_real_grammar_at_500_per_ring_finds_no_failure() {
    let dir = spec_dir("fuzz_500", &design(""), "");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let (outcome, out) = fuzz_of(&spec, 500, 1);
    assert_eq!(outcome, Ok(true), "{out}");
    assert!(
        out.contains(" containment failures 0 derived but rejected 0\n"),
        "{out}"
    );
}

#[test]
fn sync_writes_the_copies_and_check_finds_a_stale_one() {
    let dir = spec_dir("sync", &design(&fence(DOUBLE)), &fence(DOUBLE));
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let zed = Dir::new("sync_zed");
    for sub in ["fences", "grammar"] {
        fs::create_dir(zed.at(sub)).expect("a copy directory");
    }
    let run = |check| {
        let mut out = String::new();
        (sync::sync_into(&spec, &zed.root(), check, &mut out), out)
    };
    let (outcome, _) = run(true);
    assert_eq!(outcome, Ok(false), "nothing is written yet");
    let (outcome, out) = run(false);
    assert_eq!(outcome, Ok(true), "{out}");
    assert_eq!(
        fs::read_to_string(zed.at("grammar/syntax.peg")).unwrap(),
        grammar("syntax.peg")
    );
    assert_eq!(
        fs::read_to_string(zed.at("grammar/lexical.peg")).unwrap(),
        grammar("lexical.peg")
    );
    assert_eq!(
        fs::read_to_string(zed.at("grammar/desugar.txt")).unwrap(),
        grammar("desugar.txt")
    );
    let copied = fs::read_to_string(zed.at("fences/design.md")).unwrap();
    assert!(
        copied.contains("DESIGN.md:") && copied.contains(DOUBLE),
        "{copied}"
    );
    assert_eq!(run(true).0, Ok(true));

    zed.write("fences/design.md", "edited by hand\n");
    assert_eq!(run(true).0, Ok(false));
}

/// The rows `sync` copies from the rejection table: each row's name ends at its first
/// parenthesis outside a code span, so a gloss `(sec:memory)` is dropped and a call in code,
/// `` `@stack(bytes: b)` ``, is kept whole; a cell's `\|` is the `|` a reader sees.
#[test]
fn sync_names_each_rejection_row_up_to_a_parenthesis_outside_code() {
    let table = "| Rejection | Required witnesses | Menu |\n|---|---|---|\n\
                 | Collision (two keys meet) | a | b |\n\
                 | Stack depth over `@stack(bytes: b)` (sec:memory) | a | b |\n\
                 | Call `f(x)` and `g(y)` in a row (sec:units; `h(z)`) | a | b |\n\
                 | Pipe `a \\| b` written | a | b |\n\
                 | Missing argument | a | b |\n";
    let dir = spec_dir("sync_rows", &design(table), "");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let zed = Dir::new("sync_rows_zed");
    for sub in ["fences", "grammar"] {
        fs::create_dir(zed.at(sub)).expect("a copy directory");
    }
    let mut out = String::new();
    assert_eq!(
        sync::sync_into(&spec, &zed.root(), false, &mut out),
        Ok(true),
        "{out}"
    );
    assert_eq!(
        fs::read_to_string(zed.at("fences/rejections.txt")).unwrap(),
        "Collision\nStack depth over `@stack(bytes: b)`\nCall `f(x)` and `g(y)` in a row\n\
         Pipe `a | b` written\nMissing argument\n"
    );
}

/// A plan of three steps, one with a title of its own sentence.
const PLAN: &str = "# Part\n\n## (sec:steps) The steps, layer by layer\n\n### M0: scaffolding\n\n\
                    **M0.1.** The repository. More text.\n**M0.2.** Desugaring — test: it reads.\n\n\
                    ### L1: the kernel\n\nL1.1. A lexer.\n\n# Next part\n\nL1.2. Not a step.\n";

#[test]
fn progress_marks_the_steps_the_status_table_marks_done() {
    let status = "| M0.1 | done | x |\n| L1.1 | open | y |\n";
    let (text, done, total) = progress::render(PLAN, status, Some("L1.1")).expect("a plan");
    assert_eq!((done, total), (2, 3));
    assert!(text.contains("## M0: scaffolding (2/2)"), "{text}");
    assert!(text.contains("- [x] **M0.1** The repository."), "{text}");
    assert!(text.contains("- [x] **M0.2** Desugaring"), "{text}");
    assert!(
        text.contains("- [ ] **L1.1** A lexer.  ← in progress"),
        "{text}"
    );
    assert!(!text.contains("L1.2"), "{text}");
}

#[test]
fn progress_refuses_a_design_with_no_plan() {
    let why = progress::render("# Nothing\n", "", None).expect_err("no plan");
    assert_eq!(why, "DESIGN.md has no section sec:steps");
}

/// A nest of `depth` parentheses in a function body.
fn nested_body(depth: usize) -> String {
    format!(
        "double(x: int) -> int = {}x{};",
        "(".repeat(depth),
        ")".repeat(depth)
    )
}

/// The tools parse on the machine's heap stack, so a nest runs on a test thread's 2 MiB stack.
#[test]
fn the_tools_take_a_deep_program_on_a_small_stack() {
    let text = nested_body(4000);
    let dir = spec_dir("deep_tools", &design(&fence(&text)), "");
    let file = dir.write("01-deep.zed", &format!("// layer L1\n{text}\n"));
    let (outcome, out) = tool(ring::run, &[&dir.root(), &file]);
    assert_eq!(outcome, Ok(true), "{out}");
    let (outcome, out) = tool(layer::run, &[&dir.root(), &file]);
    assert!(outcome.is_ok() && out.contains("01-deep"), "{out}");
    let (outcome, out) = tool(check::run, &[&dir.root()]);
    assert_eq!(outcome, Ok(true), "{out}");
}

/// The lexical grammar goes through the same machine one character at a time.
#[test]
fn the_tools_lex_a_long_program_on_a_small_stack() {
    let text = format!(
        "double(x: int) -> int = {};",
        vec!["x"; 200_000].join(" + ")
    );
    let dir = spec_dir("long_lex", &design(""), "");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    assert!(zed_tools::syntax::lex(&spec.lexical, &text).is_ok());
}
