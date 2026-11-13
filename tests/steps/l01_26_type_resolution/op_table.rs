//! Item TYPE-op-table: the table of type inference. Each file of `tests/fixtures/type_table`
//! lists cases of one operator or construct, one per line, each with the type its operands give
//! by the rules of DESIGN.md, written down from the rules and not from zedc's output, and the
//! rule it follows. The test builds one unit of functions from a file, one function per case,
//! checks it once, and compares each function's result type, or the rejection at its line, with
//! the line. Every line that disagrees is reported, all at once.
//!
//! A file is read as follows:
//!
//! - `# …` is a comment, and a blank line is skipped.
//! - `template: e` gives the expression of the cases after it, up to the next `template:`,
//!   `$0`, `$1`, … standing for the operands. The test prints the number of cases of each.
//! - `top: s` adds the statement `s` at the top of every unit the file builds, as `k = 2;`.
//! - A case is `operands => expected -- rule`. The operands are separated by commas outside
//!   brackets. An operand written `=e` is the expression `e` put in place of its `$i`; any other
//!   operand is a type, the parameter `positional ai: T` of the case's function, whose name `ai`
//!   takes the place of `$i`. A function whose template or operands use the name `c` also takes
//!   `positional c: bool` first.
//! - `expected` is the result type as zedc prints it (user-writable syntax), `error R` for a
//!   rejection at the case's line by the diagnostics row named `R`, or `error *` where the spec
//!   names no row. Either may end in ` warn`, a warning at the line. `notyet` is what a case
//!   gives when zedc rejects a form it does not compile yet; it is never expected.
//! - A known failure ends the expected part with ` !! MARK: actual`, `MARK` naming the row of
//!   docs/plan_dag.md that owns the difference (the test checks the row is there), and `actual`
//!   what zedc gives today, `notyet` for a form of a later step. The test fails when the case gives
//!   anything else, the expected included, so a fix shows as a mark to remove.
//!
//! A unit that does not get past the syntax tree or name resolution (a form zedc does not compile
//! yet) is checked again one case per unit. A sample of the cases of every file, one in
//! `SAMPLE`, is also checked one case per unit, and must give what the whole unit gives, as batch
//! and single-file checking agree (sec:type_resolution).
//!
//! Cost: one check per file and one per sampled case, each over a unit linear in its cases; the
//! comparison is one pass over the lines, O(n) in the cases.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use zedc::check::walk::check_text;

/// One case in `SAMPLE` is also checked alone.
const SAMPLE: usize = 7;

/// One line of a fixture.
struct Case {
    /// The line number in the file, from 1.
    line: usize,
    /// The line as written.
    text: String,
    /// The template in force at the line.
    template: String,
    operands: Vec<String>,
    expected: String,
    /// The mark and the actual result of a known failure.
    known: Option<(String, String)>,
}

/// A fixture file read.
struct Table {
    tops: Vec<String>,
    cases: Vec<Case>,
}

fn table_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/type_table")
}

/// The items of `s` separated by commas outside brackets.
fn split_operands(s: &str) -> Vec<String> {
    let mut items = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ',' if depth == 0 => {
                items.push(s[start..i].trim().to_string());
                start = i + 1;
            }
            _ => {}
        }
    }
    items.push(s[start..].trim().to_string());
    items
}

fn read_table(name: &str) -> Table {
    let path = table_dir().join(name);
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path:?}: {e}"));
    let mut template = None;
    let mut tops = Vec::new();
    let mut cases = Vec::new();
    for (i, raw) in text.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some(t) = line.strip_prefix("template:") {
            template = Some(t.trim().to_string());
            continue;
        }
        if let Some(t) = line.strip_prefix("top:") {
            tops.push(t.trim().to_string());
            continue;
        }
        let at = |what: &str| format!("{name}:{}: {what}: {line}", i + 1);
        let (body, rule) = line
            .split_once(" -- ")
            .unwrap_or_else(|| panic!("{}", at("no rule")));
        assert!(!rule.trim().is_empty(), "{}", at("empty rule"));
        let (body, known) = match body.split_once(" !! ") {
            Some((b, k)) => {
                let (mark, actual) = k
                    .split_once(": ")
                    .unwrap_or_else(|| panic!("{}", at("mark")));
                (
                    b,
                    Some((mark.trim().to_string(), actual.trim().to_string())),
                )
            }
            None => (body, None),
        };
        let (operands, expected) = body
            .split_once(" => ")
            .unwrap_or_else(|| panic!("{}", at("=>")));
        let template = template
            .clone()
            .unwrap_or_else(|| panic!("{}", at("no template")));
        cases.push(Case {
            line: i + 1,
            template,
            text: line.to_string(),
            operands: split_operands(operands),
            expected: expected.trim().to_string(),
            known,
        });
    }
    Table { tops, cases }
}

/// Whether `s` holds the name `c` as a word.
fn names_c(s: &str) -> bool {
    s.split(|ch: char| !(ch.is_alphanumeric() || ch == '_' || ch == '\''))
        .any(|w| w == "c")
}

/// The function of case `n`, on one line.
fn function(case: &Case, n: usize) -> String {
    let mut expr = case.template.clone();
    let mut params = Vec::new();
    // Replace the highest index first, so `$1` is not read inside `$10`.
    for (i, op) in case.operands.iter().enumerate().rev() {
        let with = match op.strip_prefix('=') {
            Some(e) => e.to_string(),
            None => {
                params.push((i, format!("positional a{i}: {op}")));
                format!("a{i}")
            }
        };
        expr = expr.replace(&format!("${i}"), &with);
    }
    params.sort();
    let mut list: Vec<String> = params.into_iter().map(|(_, p)| p).collect();
    if names_c(&expr) {
        list.insert(0, "positional c: bool".to_string());
    }
    format!("t{n}({}) = {expr};", list.join(", "))
}

/// The unit of the cases `ns` of `table`, and the line of each case in it.
fn unit(table: &Table, ns: &[usize]) -> (String, HashMap<usize, usize>) {
    let mut text = String::new();
    for t in &table.tops {
        text.push_str(t);
        text.push('\n');
    }
    let mut lines = HashMap::new();
    for &n in ns {
        lines.insert(text.lines().count() + 1, n);
        text.push_str(&function(&table.cases[n], n));
        text.push('\n');
    }
    (text, lines)
}

/// The result of each case of `ns`, checked in one unit, or `None` when the unit does not get
/// past the syntax tree or resolution.
fn check(table: &Table, ns: &[usize]) -> Option<HashMap<usize, String>> {
    let (text, lines) = unit(table, ns);
    let tokens = zedc::lex::lex_fence(&text).ok()?;
    let tree = zedc::parse::parse(&text, &tokens, "Unit", zedc::parse::TOP).ok()?;
    let stmts = zedc::ast::unit(&text, &tokens, &tree).ok()?;
    let res = zedc::resolve::resolve(&stmts).ok()?;
    let info = check_text(&stmts, &res, Some(&text));
    let line_of = |start: usize| text[..start].matches('\n').count() + 1;
    let mut errors: HashMap<usize, String> = HashMap::new();
    for e in &info.errors {
        if let Some(&n) = lines.get(&line_of(e.span.start)) {
            let row = e.row.map_or("-", |r| r.name());
            errors.entry(n).or_insert_with(|| format!("error {row}"));
        }
    }
    let mut warned = std::collections::HashSet::new();
    for w in &info.warnings {
        if let Some(&n) = lines.get(&line_of(w.span.start)) {
            warned.insert(n);
        }
    }
    let mut results = HashMap::new();
    for &n in ns {
        let name = format!("t{n}");
        let got = match errors.remove(&n) {
            Some(e) => e,
            None => {
                let binder = res.binders.iter().position(|b| b.name == name);
                match binder.and_then(|b| info.sigs.get(&b)) {
                    Some(sig) => match sig.arrows.as_slice() {
                        // A type with an alias prints its `type` declarations on lines before it; one line
                        // per case, so the lines are joined by spaces.
                        [arrow] => arrow.result.to_string().replace('\n', " "),
                        _ => format!("arrows {sig}"),
                    },
                    None => "no signature".to_string(),
                }
            }
        };
        let got = if warned.contains(&n) {
            format!("{got} warn")
        } else {
            got
        };
        results.insert(n, got);
    }
    Some(results)
}

/// The result of case `n` checked alone; `notyet` for a form zedc does not compile yet.
fn check_alone(table: &Table, n: usize) -> String {
    if let Some(mut r) = check(table, &[n]) {
        return r.remove(&n).expect("checked");
    }
    let (text, _) = unit(table, &[n]);
    let tokens = match zedc::lex::lex_fence(&text) {
        Ok(t) => t,
        Err(_) => return "error lex".to_string(),
    };
    let tree = match zedc::parse::parse(&text, &tokens, "Unit", zedc::parse::TOP) {
        Ok(t) => t,
        Err(_) => return "error parse".to_string(),
    };
    // A form the grammar has and the checker does not compile yet, or a type the spec defines
    // and resolution does not know yet. Any other name not defined is a rejection: `bool(x)` is
    // no cast (sec:diagnostics), and resolution rejects it as a name.
    const LATER_TYPES: [&str; 6] = ["f16", "bf16", "Utf8String", "char32", "i32", "u8"];
    let not_yet = |m: &str| {
        m.contains("not compile")
            || LATER_TYPES
                .iter()
                .any(|t| m.ends_with(&format!("`{t}` is not defined.")))
    };
    match zedc::ast::unit(&text, &tokens, &tree) {
        Err(e) if not_yet(&e.message) => "notyet".to_string(),
        Err(e) => format!("error {}", e.row.map_or("-", |r| r.name())),
        Ok(stmts) => match zedc::resolve::resolve(&stmts) {
            Err(es) if es.iter().any(|e| not_yet(&e.message)) => "notyet".to_string(),
            Err(es) => format!("error {}", es[0].row.map_or("-", |r| r.name())),
            Ok(_) => unreachable!("checked above"),
        },
    }
}

/// Whether `got` is what `expected` asks for.
fn agrees(expected: &str, got: &str) -> bool {
    let (exp, exp_warn) = match expected.strip_suffix(" warn") {
        Some(e) => (e, true),
        None => (expected, false),
    };
    let (g, got_warn) = match got.strip_suffix(" warn") {
        Some(g) => (g, true),
        None => (got, false),
    };
    exp_warn == got_warn && (exp == g || (exp == "error *" && g.starts_with("error ")))
}

/// Checks every case of the fixture `name` and panics with every line that disagrees.
fn run(name: &str) {
    let table = read_table(name);
    let all: Vec<usize> = (0..table.cases.len()).collect();
    // A unit that does not get past resolution (a form not compiled yet in some case) is checked
    // one case at a time, and the cases that compile alone are checked again as one unit: n small
    // checks and one of size n, linear in the cases.
    let mut results: HashMap<usize, String> = HashMap::new();
    let mut batched = all.clone();
    let mut batch = check(&table, &all);
    if batch.is_none() {
        for &n in &all {
            results.insert(n, check_alone(&table, n));
        }
        batched = all
            .iter()
            .copied()
            .filter(|n| results[n] != "notyet")
            .collect();
        batch = check(&table, &batched);
    }
    if let Some(r) = &batch {
        results.extend(r.iter().map(|(&n, g)| (n, g.clone())));
    }
    let mut report = String::new();
    // Batch and single-file checking agree on a sample.
    if batch.is_some() {
        for n in batched.iter().copied().step_by(SAMPLE) {
            let alone = check_alone(&table, n);
            if alone != results[&n] {
                let c = &table.cases[n];
                let _ = writeln!(
                    report,
                    "{name}:{}: alone `{alone}`, in the unit `{}`: {}",
                    c.line, results[&n], c.text
                );
            }
        }
    }
    // Every mark names a row of the plan: `| MARK |` in docs/plan_dag.md. One read of the plan
    // and one substring search per distinct mark.
    let plan =
        std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("../docs/plan_dag.md"))
            .expect("docs/plan_dag.md");
    let marks: std::collections::BTreeSet<&str> = table
        .cases
        .iter()
        .filter_map(|c| c.known.as_ref().map(|(m, _)| m.as_str()))
        .collect();
    for m in marks {
        if !plan.contains(&format!("| {m} |")) {
            let _ = writeln!(
                report,
                "{name}: the mark {m} names no row of docs/plan_dag.md"
            );
        }
    }
    let (mut agree, mut known) = (0, 0);
    let mut per: std::collections::BTreeMap<&str, usize> = std::collections::BTreeMap::new();
    for (n, c) in table.cases.iter().enumerate() {
        let got = &results[&n];
        *per.entry(c.template.as_str()).or_default() += 1;
        match &c.known {
            None if agrees(&c.expected, got) => agree += 1,
            None => {
                let _ = writeln!(report, "{name}:{}: got `{got}`: {}", c.line, c.text);
            }
            Some((mark, _)) if agrees(&c.expected, got) => {
                let _ = writeln!(
                    report,
                    "{name}:{}: now agrees, remove the mark {mark}: {}",
                    c.line, c.text
                );
            }
            Some((_, actual)) if actual == got => known += 1,
            Some((mark, actual)) => {
                let _ = writeln!(
                    report,
                    "{name}:{}: known failure {mark} recorded `{actual}`, got `{got}`: {}",
                    c.line, c.text
                );
            }
        }
    }
    println!(
        "{name}: {} cases, {agree} agree, {known} known failures",
        table.cases.len()
    );
    for (t, k) in &per {
        println!("  {k:5} cases of `{t}`");
    }
    assert!(report.is_empty(), "{name}:\n{report}");
}

/// Every fixture file has its test below.
#[test]
fn every_fixture_has_a_test() {
    let tested = [
        "arith.txt",
        "divide.txt",
        "power.txt",
        "div_mod.txt",
        "compare.txt",
        "logic.txt",
        "concat.txt",
        "unary.txt",
        "if_else.txt",
        "else.txt",
        "is.txt",
        "match.txt",
        "casts.txt",
        "intervals.txt",
        "second_level.txt",
        "units.txt",
        "folds_joins.txt",
        "family.txt",
    ];
    let mut files: Vec<String> = std::fs::read_dir(table_dir())
        .expect("fixtures")
        .map(|e| e.expect("entry").file_name().to_string_lossy().into_owned())
        .collect();
    files.sort();
    let mut want: Vec<String> = tested.iter().map(|s| s.to_string()).collect();
    want.sort();
    assert_eq!(files, want);
}

#[test]
fn arith() {
    run("arith.txt");
}

#[test]
fn divide() {
    run("divide.txt");
}

#[test]
fn power() {
    run("power.txt");
}

#[test]
fn div_mod() {
    run("div_mod.txt");
}

#[test]
fn compare() {
    run("compare.txt");
}

#[test]
fn logic() {
    run("logic.txt");
}

#[test]
fn concat() {
    run("concat.txt");
}

#[test]
fn unary() {
    run("unary.txt");
}

#[test]
fn if_else() {
    run("if_else.txt");
}

#[test]
fn else_() {
    run("else.txt");
}

#[test]
fn is() {
    run("is.txt");
}

#[test]
fn match_() {
    run("match.txt");
}

#[test]
fn casts() {
    run("casts.txt");
}

#[test]
fn intervals() {
    run("intervals.txt");
}

#[test]
fn second_level() {
    run("second_level.txt");
}

#[test]
fn units() {
    run("units.txt");
}

#[test]
fn folds_joins() {
    run("folds_joins.txt");
}

#[test]
fn family() {
    run("family.txt");
}
