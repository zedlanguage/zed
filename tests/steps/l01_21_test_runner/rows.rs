//! A `// ✗` comment that names a row of the rejection table (DESIGN.md sec:diagnostics) is
//! checked against the row of the diagnostic on its line; one that names no row fails.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use zed_tests::scaling;
use zedc::query::Db;
use zedc::rejection::Row;

use super::checks;

const ROWS: &str = include_str!("../../../zed/fences/rejections.txt");

#[test]
fn the_rows_are_those_of_the_spec_table() {
    let names: Vec<&str> = Row::ALL.iter().map(|r| r.name()).collect();
    let spec: Vec<&str> = ROWS.lines().collect();
    assert_eq!(names, spec);
}

#[test]
fn a_comment_names_a_row_by_its_name_and_a_colon() {
    let cases = [
        (
            " Missing argument: name has no default",
            Some(Row::MissingArgument),
        ),
        (
            " Unreachable `match` arm: every Temp already matched",
            Some(Row::UnreachableArm),
        ),
        (" Missing argument has no colon", None),
        (" compile error: unit mismatch", None),
        (" Missing arguments: a plural is another name", None),
        (" missing argument: the case differs", None),
    ];
    for (comment, want) in cases {
        assert_eq!(Row::named_by(comment), want, "{comment}");
    }
}

/// A label printer whose calls break each argument rule L1 checks: each mark names its row.
const LABELS: &str = include_str!("zed/labels.zed");

#[test]
fn each_argument_rule_names_its_row() {
    assert_eq!(
        checks(LABELS),
        ["5:5: ok", "6:17: ok", "7:5: ok", "8:25: ok"]
    );
}

#[test]
fn a_linear_question_outside_the_fragment_names_its_row() {
    // Four variables: a splinter over three is now decided (LIVE3).
    let unit = "ok(x, y, z, w) = 9 * x - 4 * y - 8 * w - 3 >= 0 && 5 * x + 11 * y + 9 * w - 9 >= \
                0 && -7 * x - 12 * y - 2 * z + 8 * w - 1 >= 0 && -9 * x + 8 * y + 7 * z >= 0 && \
                -10 * x + 4 * y - 6 * z - 4 * w + 22 >= 0;  // ✗ Linear question outside the \
                polynomial fragment of the linear-relation domain: a splinter\n";
    assert_eq!(checks(unit), ["1:1: ok"]);
}

#[test]
fn a_mark_naming_another_row_fails_with_both_rows() {
    let unit = "\
label(positional name: String, city: String) = name ++ \", \" ++ city;
a = label(city: \"Leeds\");    // ✗ Argument in the wrong form: but the name is left out
";
    assert_eq!(
        checks(unit),
        [
            "2:5: the mark names the row \"Argument in the wrong form\", and the diagnostic is \
             in the row \"Missing argument\": this call of `label` gives no value to its parameter `name`, and `name` has no default, so the call cannot be made"
        ]
    );
}

#[test]
fn a_mark_naming_a_row_fails_on_a_diagnostic_in_no_row() {
    let unit = "total = pounds;    // ✗ Missing argument: not this one\n";
    let got = checks(unit);
    assert_eq!(got.len(), 1, "{got:?}");
    assert!(
        got[0].starts_with(
            "1:9: the mark names the row \"Missing argument\", and the diagnostic is in no row \
             of the rejection table: "
        ),
        "{got:?}"
    );
}

#[test]
fn a_mark_naming_no_row_fails() {
    let unit = "\
label(positional name: String, city: String) = name ++ \", \" ++ city;
a = label(city: \"Leeds\");    // ✗ the name is left out
";
    assert_eq!(
        checks(unit),
        [
            "2:5: the line is marked ✗ and its comment names no row of the rejection table: write \
             `// ✗ <row>: …` with the row's name"
        ]
    );
}

/// Every live ✗ mark of the spec's fences, at any layer, names its row; the whole-line `//`
/// variants are checked by their own fixtures.
#[test]
fn every_live_mark_of_the_spec_names_a_row() {
    let mut unnamed = Vec::new();
    let mut named = 0;
    for f in zed_tests::fences::all() {
        let lines: Vec<&str> = f.text.split('\n').collect();
        for k in zedc::fence::marks(&f.text).lines {
            let comment = lines[k - 1].split_once('✗').map(|(_, c)| c);
            match comment.and_then(Row::named_by) {
                Some(_) => named += 1,
                None => unnamed.push(format!("{} line {k}: {}", f.at, lines[k - 1].trim())),
            }
        }
    }
    assert!(unnamed.is_empty(), "{unnamed:#?}");
    assert!(named >= 9, "{named} named marks");
}

/// `n` names each bound twice, the second binding marked with its row.
fn rebound(n: usize) -> String {
    (0..n)
        .map(|i| format!("a{i} = {i};\na{i} = 1;  // ✗ Rebinding in the same scope: a{i}\n"))
        .collect()
}

#[test]
fn checking_n_marks_scales() {
    let n = 200;
    scaling::check_order("checking n marked lines against their rows", n, 1, |m| {
        let got = checks(&rebound(m));
        assert_eq!(got.len(), m);
        assert!(got.iter().all(|c| c.ends_with(": ok")), "{got:?}");
    });
}
/// A fee calculator called with its rate named before its positional base: the grammar takes
/// either order, and the check names the row, the argument, the first named one and the call.
#[test]
fn a_positional_argument_after_a_named_one_names_its_row() {
    let decl = "fee(positional base: int, rate: int) = base * rate;\n";
    let unit = format!(
        "{decl}f = fee(rate: 3, 5);    // ✗ Named argument before a positional one: 5 goes first\n"
    );
    assert_eq!(checks(&unit), ["2:18: ok"]);
    let Err(why) = zedc::run::load(format!("{decl}f = fee(rate: 3, 5);\n").as_bytes()) else {
        panic!("the call is accepted")
    };
    assert_eq!(
        why,
        "\
2:18: this positional argument comes after the named argument `rate`, and a call passes its \
positional arguments first, then its named ones.
  [1] 2:9: the first named argument, `rate`
      2 | f = fee(rate: 3, 5);
        |     ^^^^^^^^^^^^^^^ [2]
        |         ^^^^ [1] ^ [3]
  [2] 2:5: the call
  [3] 2:18: repair: pass this argument before `rate`, the positional arguments first"
    );
}

/// The same rule for an annotation's arguments, and for a call that begins with positional
/// arguments, then names one and passes another by position.
#[test]
fn an_annotation_argument_after_a_named_one_names_its_row() {
    let unit = "@doc(lang: \"en\", \"a fee\")    // ✗ Named argument before a positional one: \
                the text goes first\n\
                fee(positional base: int) = base;\n";
    assert_eq!(checks(unit), ["1:18: ok"]);
    let decl = "fee(positional base: int, positional cap: int, rate: int) = base * rate;\n";
    let unit = format!(
        "{decl}f = fee(7, rate: 3, 5);    // ✗ Named argument before a positional one: 5 too\n"
    );
    assert_eq!(checks(&unit), ["2:21: ok"]);
}

/// A surcharge declared with its positional base after its named rate, and a lambda whose
/// tuple parameter, positional without the keyword, follows a named one.
#[test]
fn a_positional_parameter_after_a_named_one_names_its_row() {
    let unit = "surcharge(rate: int, positional base: int) = base * rate;    // ✗ `positional` \
                parameter after a named one: base goes first\n";
    assert_eq!(checks(unit), ["1:22: ok"]);
    let lambda = "h = (rate, (a, b)) -> a * rate;    // ✗ `positional` parameter after a named \
                  one: the tuple goes first\n";
    assert_eq!(checks(lambda), ["1:12: ok"]);
    let Err(why) = zedc::run::load(b"surcharge(rate: int, positional base: int) = base * rate;\n")
    else {
        panic!("the declaration is accepted")
    };
    assert_eq!(
        why,
        "\
1:22: the positional parameter `base` comes after the named parameter `rate`, and a \
declaration lists its positional parameters first.
  [1] 1:11: the first named parameter, `rate`
      1 | surcharge(rate: int, positional base: int) = base * rate;
        | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [2]
        |           ^^^^^^^^^ [1]
        |                      ^^^^^^^^^^^^^^^^^^^^ [3]
  [2] 1:1: the declaration
  [3] 1:22: repair: declare `base` before `rate`, the positional parameters first"
    );
}

/// Positional items first, then named ones (named in any order), are accepted and run.
#[test]
fn positional_items_before_named_ones_are_accepted() {
    let unit = "\
fee(positional base: int, positional lo: int, rate: int, cap: int = 9) = base * rate + lo + cap;
f(x) = fee(x, 1, rate: 3) + fee(x, 1, cap: 4, rate: 3) test { 2 -> 27 }
";
    assert_eq!(checks(unit), ["2:63: ok"]);
}

/// The words no message prints (DESIGN.md sec:diagnostics): the name of each typing rule of the
/// kernel calculus, `T-` and the generator for each generator of sec:kernel's grammar `F ::= …`
/// (`fam` gives `T-Fam`), with every other `T-` rule the spec names; and `Boom`, since a menu
/// says a reduction owes its operator's laws, not its Boom obligations (item MSG-words).
fn unsaid_words(design: &str) -> HashSet<String> {
    let kernel = design
        .split_once("\n# (sec:kernel)")
        .expect("DESIGN.md has the section sec:kernel")
        .1;
    let kernel = kernel.split_once("\n# (").map_or(kernel, |(k, _)| k);
    let mut words = HashSet::from(["Boom".to_string()]);
    let mut generators = 0;
    for line in kernel.lines() {
        let Some(rest) = line
            .strip_prefix("F ::= ")
            .or_else(|| line.trim_start().strip_prefix("| "))
        else {
            continue;
        };
        let Some((name, _)) = rest.split_once('(') else {
            continue;
        };
        let mut chars = name.chars();
        let Some(first) = chars.next().filter(|c| c.is_ascii_lowercase()) else {
            continue;
        };
        let rest = chars.as_str();
        if rest.chars().all(|c| c.is_ascii_alphanumeric()) {
            words.insert(format!("T-{}{rest}", first.to_ascii_uppercase()));
            generators += 1;
        }
    }
    // The grammar names seven generators; a parse that found none would ban nothing.
    assert!(generators >= 7, "{generators} kernel generators found");
    for (at, _) in design.match_indices("T-") {
        let before = design[..at].chars().next_back();
        let rule: String = design[at + 2..]
            .chars()
            .take_while(|c| c.is_alphanumeric())
            .collect();
        if !before.is_some_and(is_word_char) && rule.starts_with(|c: char| c.is_uppercase()) {
            words.insert(format!("T-{rule}"));
        }
    }
    words
}

/// Whether `c` is part of a word: a letter, a digit or `_`.
fn is_word_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// Each of `words` in `text`, in order of place, matched whole: a word is a run of letters,
/// digits and `_`, and a rule such as `T-Fold` is two words joined by one `-`, so `T-Folder`
/// and `Boomerang` match nothing. O(length of `text`): one pass, a hash lookup per word.
fn said<'w>(text: &str, words: &'w HashSet<String>) -> Vec<&'w str> {
    let mut out = Vec::new();
    let (mut start, mut last) = (None, None);
    let ends = text
        .char_indices()
        .chain(std::iter::once((text.len(), ' ')));
    for (i, c) in ends {
        match (start, is_word_char(c)) {
            (None, true) => start = Some(i),
            (Some(s), false) => {
                out.extend(words.get(&text[s..i]).map(String::as_str));
                if let Some((ls, le)) = last
                    && le + 1 == s
                    && text.as_bytes()[le] == b'-'
                {
                    out.extend(words.get(&text[ls..i]).map(String::as_str));
                }
                (start, last) = (None, Some((s, i)));
            }
            _ => {}
        }
    }
    out
}

/// The lines of `text` that hold expected output: all but a comment line, which is one whose
/// text starts with `//` and holds no ✗ mark (a comment of a test, or of a Zed fence).
fn expected_lines(text: &str) -> impl Iterator<Item = (usize, &str)> {
    text.lines()
        .enumerate()
        .filter(|(_, l)| !l.trim_start().starts_with("//") || l.contains('✗'))
        .map(|(k, l)| (k + 1, l))
}

/// Every file under `dir`, at any depth, sorted.
fn files_under(dir: &Path) -> Vec<PathBuf> {
    let (mut out, mut todo) = (Vec::new(), vec![dir.to_path_buf()]);
    while let Some(d) = todo.pop() {
        for e in std::fs::read_dir(&d).expect("a readable directory") {
            let p = e.expect("an entry").path();
            if p.is_dir() {
                todo.push(p);
            } else {
                out.push(p);
            }
        }
    }
    out.sort();
    out
}

/// No message names a kernel rule (DESIGN.md sec:diagnostics). Checked on what the front end
/// prints for every fence of the spec, every ✗ variant and every unit of a step's `zed/` folder,
/// derivations and warnings included, and on every expected output the step tests and the
/// fence copies hold: each line of their files but a comment line.
#[test]
fn no_message_names_a_kernel_rule() {
    let Some(spec) = zed_tests::spec::dir("the words of messages") else {
        return;
    };
    let design = std::fs::read_to_string(spec.join("DESIGN.md")).expect("a readable DESIGN.md");
    let words = unsaid_words(&design);
    let mut found = Vec::new();
    let mut runs: Vec<(String, String)> = zed_tests::fences::all()
        .into_iter()
        .map(|f| (f.at, f.text))
        .collect();
    runs.extend(
        zed_tests::fences::variants()
            .into_iter()
            .map(|v| (v.name, v.text)),
    );
    for p in zed_tests::oracle::step_units() {
        let text = std::fs::read_to_string(&p).expect("a readable step unit");
        runs.push((p.display().to_string(), text));
    }
    let mut messages = 0;
    for (at, text) in &runs {
        let front = Db::new().front(text);
        let ds = match &*front {
            Ok((_, _, warnings)) => warnings,
            Err(ds) => ds,
        };
        for d in ds {
            let m = d.to_string();
            messages += 1;
            let w = said(&m, &words);
            if !w.is_empty() {
                found.push(format!("{at}: the message names {w:?}: {m}"));
            }
        }
    }
    // A message the spec prints in a ```text fence, as the collision of sec:remap_law.
    let mut lines = 0;
    for doc in ["DESIGN.md", "EXAMPLES.md"] {
        let text = std::fs::read_to_string(spec.join(doc)).expect("a readable spec document");
        let mut inside = false;
        for (k, line) in text.lines().enumerate() {
            if line.starts_with("```") {
                inside = line == "```text";
            } else if inside {
                lines += 1;
                let w = said(line, &words);
                if !w.is_empty() {
                    found.push(format!("{doc}:{}: names {w:?}: {line}", k + 1));
                }
            }
        }
    }
    let fences = zed_tests::fences::dir();
    // This file names the words to test the search for them.
    let this = zed_tests::steps_dir().join("l01_21_test_runner/rows.rs");
    for p in files_under(&zed_tests::steps_dir())
        .into_iter()
        .chain(files_under(&fences))
        .filter(|p| *p != this)
    {
        let text = std::fs::read_to_string(&p).expect("a readable test file");
        for (k, line) in expected_lines(&text) {
            lines += 1;
            let w = said(line, &words);
            if !w.is_empty() {
                found.push(format!("{}:{k}: names {w:?}: {line}", p.display()));
            }
        }
    }
    assert!(found.is_empty(), "{found:#?}");
    // A run that read nothing would pass the loops above.
    assert!(
        messages >= 100 && lines >= 10_000,
        "{messages} messages, {lines} lines"
    );
}

#[test]
fn a_word_is_matched_whole() {
    let words: HashSet<String> = ["T-Fold", "T-Fix", "Boom"]
        .into_iter()
        .map(String::from)
        .collect();
    let cases: [(&str, &[&str]); 7] = [
        ("explicit reduction; owes op's laws", &[]),
        ("the fold (T-Fold) needs evidence", &["T-Fold"]),
        (
            "T-Fix: no bottom, and the Boom obligations",
            &["T-Fix", "Boom"],
        ),
        ("`AT-Folder` and `Boomerang` are a user's names", &[]),
        ("`T - Fold` is a subtraction", &[]),
        ("T-Fixed, T_Fix, xT-Fix", &[]),
        ("ends with T-Fold", &["T-Fold"]),
    ];
    for (text, want) in cases {
        assert_eq!(said(text, &words), want, "{text}");
    }
}

#[test]
fn the_unsaid_words_come_from_the_kernel_grammar() {
    let design = "\
# (sec:syntax_tour) An earlier section
    | skip(x)
# (sec:kernel) Appendix
```
F ::= fam(D, i -> e)   -- introduce
    | reindex(F, kf, vf)
    | discard(F, sel)
    | fold(F, op, ev)
    | fix(F0, step, ev)
    | gen(init, step, guard)
    | port(decl)
```
*T-Fam*: and a rule T-Ext named only in prose; GT-Not is no rule.
# (sec:categories) Appendix
    | other(x)
";
    let mut got: Vec<String> = unsaid_words(design).into_iter().collect();
    got.sort();
    assert_eq!(
        got,
        [
            "Boom",
            "T-Discard",
            "T-Ext",
            "T-Fam",
            "T-Fix",
            "T-Fold",
            "T-Gen",
            "T-Port",
            "T-Reindex"
        ]
    );
}

/// `n` lines of a collision message, each naming one rule, as a message must not.
fn messages(n: usize) -> String {
    (0..n)
        .map(|i| format!("{i}:5: two keypaths land on `k{i}` (T-Reindex); owes op's laws\n"))
        .collect()
}

#[test]
fn finding_the_unsaid_words_scales() {
    let words: HashSet<String> = ["T-Reindex", "T-Fold", "Boom"]
        .into_iter()
        .map(String::from)
        .collect();
    let texts = scaling::inputs(2000, messages);
    scaling::check("finding kernel rule names in n message lines", 2000, |m| {
        assert_eq!(said(&texts[&m], &words).len(), m);
    });
}
