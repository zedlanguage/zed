//! `cite SPEC_DIR` checks the citations of the spec: every section label written `sec:` and a
//! name, and every plan step id (`M0.n`, `Lk.n` or `S.n`, then an optional lower-case letter),
//! named in `SPEC_DIR/DESIGN.md` or in a file git tracks in this repository, must be defined in
//! DESIGN.md. A label is defined by a heading that begins with it in parentheses; a step, by a
//! line of the plan (sec:steps). A step id is also accepted where a row of `docs/plan_dag.md`
//! names it after "DESIGN step", since that plan item adds the step to DESIGN.md. Each
//! citation of neither kind is reported with its file and line. CI does not run it, since CI
//! never reads the spec.

use std::collections::HashSet;
use std::process::Command;

use crate::progress::{plan, step_name};
use crate::{Outcome, arg, impl_root, say};

/// Files whose citations are test data, not citations of the spec: the tests of the fence keys
/// and of this tool write labels and steps that no DESIGN.md defines.
pub const FIXTURES: &[&str] = &[
    "tests/steps/l01_07_fences/keys.rs",
    "tests/steps/m0_03_grammar_tools/cite.rs",
];

/// The plan DAG. Its rows and notes name steps that the plan items will add or that reviews
/// proposed, so only its labels are checked.
pub const PLAN: &str = "docs/plan_dag.md";

/// Checks the citations of `SPEC_DIR/DESIGN.md` and of the files git tracks here.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    let spec = arg(args, 0, "cite SPEC_DIR")?;
    let design = crate::text::read_text(&format!("{spec}/DESIGN.md"))?;
    let root = impl_root();
    let listed = Command::new("git")
        .args(["-C", &root, "ls-files", "-z"])
        .output()
        .map_err(|e| format!("git ls-files: {e}"))?;
    if !listed.status.success() {
        return Err(format!(
            "git ls-files: {}",
            String::from_utf8_lossy(&listed.stderr)
        ));
    }
    let paths = String::from_utf8(listed.stdout).map_err(|e| format!("git ls-files: {e}"))?;
    let mut files = vec![("DESIGN.md".to_string(), design.clone())];
    for path in paths.split('\0').filter(|p| !p.is_empty()) {
        // A file deleted in the working tree and not yet committed has nothing to cite, and a
        // file that is not UTF-8 is not text.
        match std::fs::read(format!("{root}/{path}")) {
            Ok(bytes) => {
                if let Ok(text) = String::from_utf8(bytes) {
                    files.push((path.to_string(), text));
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Err(e) => return Err(format!("{path}: {e}")),
        }
    }
    check_citations(&design, &files, out)
}

/// Checks the citations of each `(path, text)` of `files` against `design`, the text of
/// DESIGN.md, and reports each undefined one in `out`. The file at [`PLAN`], when among
/// `files`, also gives the steps that plan items will add. Every exempt path of [`FIXTURES`]
/// must be among `files`, so that the list cannot outlive the files it names.
pub fn check_citations(design: &str, files: &[(String, String)], out: &mut String) -> Outcome {
    // The labels and steps go into hash sets, so each citation costs one lookup and the check
    // is linear in the length of the files (COMPLEXITY F92).
    let labels: HashSet<&str> = design.lines().filter_map(label_of_heading).collect();
    let mut steps: HashSet<&str> = plan(design)?
        .into_iter()
        .flat_map(|(_, steps)| steps.into_iter().map(|(step, _)| step))
        .collect();
    for (path, text) in files {
        if path == PLAN {
            steps.extend(
                text.lines()
                    .filter(|l| l.starts_with('|'))
                    .flat_map(planned),
            );
        }
    }
    let mut ok = true;
    for exempt in FIXTURES {
        if !files.iter().any(|(path, _)| path == exempt) {
            say!(out, "{exempt}: listed as exempt, but not a tracked file");
            ok = false;
        }
    }
    for (path, text) in files {
        if FIXTURES.contains(&path.as_str()) {
            continue;
        }
        for (n, line) in text.lines().enumerate() {
            for label in cited_labels(line) {
                if !labels.contains(label) {
                    say!(
                        out,
                        "{path}:{}: sec:{label} is no label of DESIGN.md",
                        n + 1
                    );
                    ok = false;
                }
            }
            if path == PLAN {
                continue;
            }
            for step in cited_steps(line) {
                if !steps.contains(step) {
                    say!(out, "{path}:{}: {step} is no step of DESIGN.md", n + 1);
                    ok = false;
                }
            }
        }
    }
    Ok(ok)
}

/// Whether `c` may be part of a label.
fn label_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// The label a heading line defines: `## (sec:order) Order: ...` defines `order`.
fn label_of_heading(line: &str) -> Option<&str> {
    let rest = line.trim_start_matches('#');
    if rest.len() == line.len() {
        return None;
    }
    let rest = rest.strip_prefix(" (sec:")?;
    let end = rest.find(|c: char| !label_char(c))?;
    (end > 0 && rest[end..].starts_with(')')).then_some(&rest[..end])
}

/// The labels `line` cites: each `sec:` not inside a longer word, with the name after it.
fn cited_labels(line: &str) -> impl Iterator<Item = &str> {
    line.match_indices("sec:").filter_map(move |(at, _)| {
        if line[..at].ends_with(label_char) {
            return None;
        }
        let rest = &line[at + 4..];
        let end = rest.find(|c: char| !label_char(c)).unwrap_or(rest.len());
        (end > 0).then_some(&rest[..end])
    })
}

/// The step ids `line` cites: each step name that is not part of a longer word, number or
/// dotted name, so `xL1.2`, `1.L1.2`, `L1.2b3` and `L1.20xy` cite none.
fn cited_steps(line: &str) -> impl Iterator<Item = &str> {
    line.char_indices().filter_map(move |(at, c)| {
        if !matches!(c, 'M' | 'L' | 'S') {
            return None;
        }
        let before = line[..at].chars().next_back();
        if before.is_some_and(|b| b.is_ascii_alphanumeric() || matches!(b, '_' | '.' | '-')) {
            return None;
        }
        step_at(&line[at..])
    })
}

/// The step id at the start of `s`, unless a letter or digit follows it.
fn step_at(s: &str) -> Option<&str> {
    let end = step_name(s)?;
    let after = s[end..].chars().next();
    (!after.is_some_and(|a| a.is_ascii_alphanumeric())).then_some(&s[..end])
}

/// The steps a row of the plan DAG says it adds to DESIGN.md: each step id written right after
/// "DESIGN step ".
fn planned(row: &str) -> impl Iterator<Item = &str> {
    row.match_indices("DESIGN step ")
        .filter_map(move |(at, phrase)| step_at(&row[at + phrase.len()..]))
}
