//! Step M0.3: the grammar tools and the hand-run commands of `zed-tools`.
//!
//! CI does not read the spec repository, so each test builds a small spec of its own: the
//! grammars `sync` copied into `zed/grammar`, a table of defined words, and the fences the test
//! needs. A spec author runs these tools on the real spec; the tests here run the same `run`
//! functions the commands call.

mod scaling;

use std::fs;
use std::path::PathBuf;

use zed_tools::spec::Spec;
use zed_tools::{Outcome, audit, cases, check, fences, fuzz, layer, progress, ring, sync};

/// A directory under `build/` that is removed at the end of the test.
pub struct Dir(pub PathBuf);

impl Dir {
    /// A new empty directory named `name`.
    pub fn new(name: &str) -> Dir {
        let path = PathBuf::from(format!(
            "{}/build/tool_tests/{name}",
            zed_tools::impl_root()
        ));
        if path.exists() {
            fs::remove_dir_all(&path).expect("removing an earlier run's directory");
        }
        fs::create_dir_all(&path).expect("creating a test directory");
        Dir(path)
    }

    /// The path of `name` in this directory.
    pub fn at(&self, name: &str) -> String {
        self.0.join(name).to_str().expect("UTF-8 path").into()
    }

    /// Writes `text` to `name` in this directory and gives its path.
    pub fn write(&self, name: &str, text: &str) -> String {
        let path = self.at(name);
        fs::write(&path, text).expect("writing a test file");
        path
    }

    /// This directory's path.
    pub fn root(&self) -> String {
        self.0.to_str().expect("UTF-8 path").into()
    }
}

impl Drop for Dir {
    fn drop(&mut self) {
        // A test that has failed still removes its directory, so this cannot be allowed to panic.
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// The copy of a grammar file in `zed/grammar`.
pub fn grammar(name: &str) -> String {
    fs::read_to_string(format!("{}/zed/grammar/{name}", zed_tools::impl_root()))
        .expect("a file of zed/grammar")
}

/// A table with `sorted` at L3 and the `log` port at L7.
const WORDS: &str = "| Layer | Annotations | Facet words | Words |\n|---|---|---|---|\n\
                     | L1 | | | `len` |\n| L3 | | | `sorted` |\n| L7 | | | `log` |\n";

/// The text of a `DESIGN.md` with the given grammars, then `body`.
pub fn design_of(lex: &str, syn: &str, doc: &str, desugar: &str, body: &str) -> String {
    format!(
        "# Test spec\n\n{WORDS}\n```peg\n{lex}```\n\n```peg\n{syn}```\n\n```peg\n{doc}```\n\n\
         ```desugar\n{desugar}```\n\n{body}\n"
    )
}

/// A `DESIGN.md` with the real grammars, then `body`.
pub fn design(body: &str) -> String {
    design_of(
        &grammar("lexical.peg"),
        &grammar("syntax.peg"),
        &grammar("notation.peg"),
        &grammar("desugar.txt"),
        body,
    )
}

/// A ```` ```zed ```` fence.
pub fn fence(text: &str) -> String {
    format!("```zed\n{text}\n```\n")
}

/// A spec whose `DESIGN.md` is `design` and whose `EXAMPLES.md` is `examples`.
pub fn spec_dir(name: &str, design: &str, examples: &str) -> Dir {
    let dir = Dir::new(name);
    dir.write("DESIGN.md", design);
    dir.write("EXAMPLES.md", examples);
    dir
}

/// Runs a tool and gives what it printed.
pub fn tool(run: fn(&[String], &mut String) -> Outcome, args: &[&str]) -> (Outcome, String) {
    let args: Vec<String> = args.iter().map(|a| a.to_string()).collect();
    let mut out = String::new();
    let outcome = run(&args, &mut out);
    (outcome, out)
}

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
    let high = dir.write(
        "high.zed",
        "main() -> (stdout: Lines) { stdout <- [\"a\"]; }\n",
    );
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
