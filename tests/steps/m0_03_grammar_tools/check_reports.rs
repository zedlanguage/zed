//! Each report of the `check` and `ring` tools, on a small spec whose grammars are the real ones
//! with one change: an alternative that needs a rule empty at its layer (LAYER), a `~` mark
//! above its rule's lowest layer (MARK), a desugaring rule for no production or two for one
//! (DESUGAR), a fence whose tree changes between rings (TREE CHANGES), a fence that does not
//! lex (LEX), a fence that is documentation notation (DOC), and a hole of a string that does not
//! parse. The lexer's token kinds, and the way a report writes a token (Python's `repr`).

use super::{DOUBLE, design, design_of, fence, grammar, spec_dir, tool};
use zed_tools::spec::Spec;
use zed_tools::text::repr;
use zed_tools::{check, ring};

/// The real grammars, with the rule line of the syntactic grammar that starts with `rule` and
/// its alternatives replaced by `with`, `extra` added to the syntactic grammar, and `desugar`
/// added to the desugaring rules; then `body`.
fn changed(rule: &str, with: &str, extra: &str, desugar: &str, body: &str) -> String {
    let mut syn = String::new();
    let mut skipping = false;
    for line in grammar("syntax.peg").lines() {
        if !rule.is_empty() && line.starts_with(&format!("{rule} ")) {
            syn.push_str(with);
            skipping = true;
            continue;
        }
        if skipping && line.trim_start().starts_with('|') {
            continue;
        }
        skipping = false;
        syn.push_str(line);
        syn.push('\n');
    }
    syn.push_str(extra);
    design_of(
        &grammar("lexical.peg"),
        &syn,
        &grammar("notation.peg"),
        &format!("{}{desugar}", grammar("desugar.txt")),
        body,
    )
}

/// `Unit` at L1 is `Item* END`, as in the real grammar, but from L5 on an earlier alternative
/// parses the same text through a rule of its own, so every unit's tree changes at L5.
const SPLIT_UNIT: &str = "Unit          = Later END    L5\n              | Item* END    L1\n";
const LATER: &str = "Later         = Item*        L5\n";

#[test]
fn an_alternative_that_needs_a_rule_empty_at_its_layer_is_reported() {
    let extra = "Lint          = 'lint' High    L1\nHigh          = Name    L5\n";
    let text = changed("", "", extra, "Lint : x\nHigh : x\n", &fence(DOUBLE));
    let dir = spec_dir("check_layer", &text, "");
    let (outcome, out) = tool(check::run, &[&dir.root()]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(
        out.contains("LAYER Lint alternative 1 (L1) requires High, empty below L5\n"),
        "{out}"
    );
    assert!(!out.contains("DESUGAR"), "{out}");
}

#[test]
fn a_mark_above_its_rules_lowest_layer_is_reported() {
    let extra = "Wrap          = ~Name    L3\n";
    let text = changed("", "", extra, "Wrap : x\n", &fence(DOUBLE));
    let dir = spec_dir("check_mark", &text, "");
    let (outcome, out) = tool(check::run, &[&dir.root()]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(
        out.contains("MARK Wrap alternative 1 (L3) marks Name, whose lowest layer is L1\n"),
        "{out}"
    );
}

#[test]
fn a_desugaring_rule_for_no_production_and_a_second_rule_are_reported() {
    let text = changed("", "", "", "Nowhere : x\nName : again\n", &fence(DOUBLE));
    let dir = spec_dir("check_desugar_extra", &text, "");
    let (outcome, out) = tool(check::run, &[&dir.root()]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(
        out.contains("DESUGAR rule for no production: Nowhere\n"),
        "{out}"
    );
    assert!(out.contains("DESUGAR two rules for Name\n"), "{out}");
    assert!(!out.contains("DESUGAR missing"), "{out}");
}

#[test]
fn a_fence_whose_tree_changes_between_rings_is_reported() {
    let text = changed("Unit", SPLIT_UNIT, LATER, "Later : x\n", &fence(DOUBLE));
    let dir = spec_dir("check_tree", &text, "");
    let (outcome, out) = tool(check::run, &[&dir.root()]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(out.contains(" TREE CHANGES between L1 and L5\n"), "{out}");

    // The ring tool reports the same change, against the full ring.
    let file = dir.write("double.zed", DOUBLE);
    let (outcome, out) = tool(ring::run, &[&dir.root(), &file]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(
        out.contains(" FAIL TREE CHANGES between L1 and L29\n"),
        "{out}"
    );
}

/// A fence at a ring above 1, one that does not lex, a string hole that does not lex, does not
/// parse or does not end at the hole's end, each named at its fence.
#[test]
fn each_way_a_fence_fails_is_named_and_a_high_fence_gets_its_ring() {
    let fences = [
        "@a x = 1;",
        "x = 1 ` 2;",
        "s = \"${`}\";",
        "s = \"${a +}\";",
        "s = \"${a b}\";",
    ];
    let body: String = fences.iter().map(|f| fence(f) + "\n").collect();
    let dir = spec_dir("check_fails", &design(&body), "");
    let (outcome, out) = tool(check::run, &[&dir.root(), "", "any"]);
    assert_eq!(outcome, Ok(false), "{out}");
    let reports: Vec<&str> = out.lines().filter(|l| l.starts_with("DESIGN.md")).collect();
    assert_eq!(reports.len(), 5, "{out}");
    assert!(reports[0].contains(" LEX lex error at line 1: '`"), "{out}");
    assert!(
        reports[1].contains(" FAIL lex error at line 1: '`'"),
        "{out}"
    );
    assert!(
        reports[2].contains(" FAIL line 1 near ''; expected "),
        "{out}"
    );
    assert!(
        reports[3].contains(" FAIL line 1 near 'b'; expected ") && reports[3].contains("END"),
        "{out}"
    );
    // Every fence that parses is listed last with its ring, as asked by the third argument.
    assert!(
        reports[4].starts_with("DESIGN.md ") && reports[4].ends_with(" L2"),
        "{out}"
    );
    assert!(
        out.contains("parsed 1 failed 4 ring histogram {2: 1}\n"),
        "{out}"
    );
}

/// FILE:LINE checks only the fence at that line.
#[test]
fn check_of_one_fence_skips_the_others() {
    let body = format!("{}\n{}", fence(DOUBLE), fence("double(x: int -> int"));
    let text = design(&body);
    // A fence is named at the line of its opening ```.
    let line = text.lines().position(|l| l == DOUBLE).expect("the fence");
    let dir = spec_dir("check_one", &text, "");
    let (outcome, out) = tool(check::run, &[&dir.root(), &format!("DESIGN.md:{line}")]);
    assert_eq!(outcome, Ok(true), "{out}");
    assert!(
        out.contains("parsed 1 failed 0 ring histogram {1: 1}\n"),
        "{out}"
    );
}

/// A fence that is not a program but parses as documentation notation is listed as such; one
/// that uses no notation of its own is reported, which only a grammar whose `Unit` refuses a
/// program `DocFence` accepts can show.
#[test]
fn a_documentation_fence_is_listed_and_one_using_no_notation_is_reported() {
    let dir = spec_dir("check_doc", &design(&fence("double: int -> int")), "");
    let (outcome, out) = tool(check::run, &[&dir.root()]);
    assert_eq!(outcome, Ok(true), "{out}");
    let line = out
        .lines()
        .find(|l| l.starts_with("documentation-notation fences: DESIGN.md:"))
        .unwrap_or_else(|| panic!("{out}"));
    assert_eq!(line.split(' ').count(), 3, "{out}");

    let unit = "Unit          = 'program' Item* END    L1\n";
    let text = changed("Unit", unit, "", "", &fence(DOUBLE));
    let dir = spec_dir("check_doc_plain", &text, "");
    let (outcome, out) = tool(check::run, &[&dir.root()]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(
        out.contains(" DOC uses no signature, remap form or trailing expression\n"),
        "{out}"
    );
}

/// A lexical grammar whose `Token` or `Number` has a rule that is no token kind stops the lexer.
#[test]
fn a_token_rule_with_no_kind_stops_the_lexer() {
    let syn = grammar("syntax.peg");
    let (doc, desugar) = (grammar("notation.peg"), grammar("desugar.txt"));
    let lexical = grammar("lexical.peg");
    let cases = [
        ("| Operator ", "| Operator | Odd ", "Token"),
        (
            "(Rational | Float | Integer)",
            "(Rational | Float | Integer | Odd)",
            "Number",
        ),
    ];
    for (from, to, name) in cases {
        assert!(lexical.contains(from), "{from}");
        let lex = format!(
            "{}Odd           = '`'    L1\n",
            lexical.replacen(from, to, 1)
        );
        let dir = spec_dir(
            &format!("lex_kind_{name}"),
            &design_of(&lex, &syn, &doc, &desugar, ""),
            "",
        );
        let spec = Spec::open(&dir.root()).expect("the spec reads");
        let got = ring::ring_of(&spec, "x = `;").map(|r| r.ring);
        let want = if name == "Token" { "Odd" } else { "Number" };
        assert_eq!(got, Err(format!("LEX no token kind for {want}")), "{name}");
    }
}

/// Python's `repr`: each escape, the quote it picks, and what it writes as itself.
#[test]
fn a_token_is_written_as_python_writes_a_string() {
    let cases = [
        ("a\tb\rc\nd\\", r"'a\tb\rc\nd\\'"),
        ("it's", "\"it's\""),
        ("'\"", r#"'\'"'"#),
        ("\u{1}\u{85}", r"'\x01\x85'"),
        ("\u{378}", r"'\u0378'"),
        ("\u{e0001}", r"'\U000e0001'"),
        ("é ∀", "'é ∀'"),
    ];
    for (s, want) in cases {
        assert_eq!(repr(s), want, "{s:?}");
    }
}
