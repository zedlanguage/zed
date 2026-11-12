//! Item README-fences: the fences of README.md, copied into `zed/fences/readme.md` by the `sync`
//! tool, are lexed and parsed, and from its own layer on each is checked and run, its ✗ lines
//! and commented ✗ variants compared with the diagnostics, and the results the page states
//! compared with the run by the checks of the table of expected results, `expected.txt` (the
//! forms are in `zed_tests::readme`). Every fence has an entry in the table, and every entry
//! lists exactly the results the page states.

mod scaling;

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::sync::Arc;

use zed_kernel::{Evaluator, Term, World};
use zed_tests::fences::{self, DocFence};
use zed_tests::oracle::ENABLED;
use zed_tests::readme::{self, Entry};
use zedc::elab::Cones;
use zedc::fence;
use zedc::interp;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};
use zedc::query::Db;
use zedc::run;
use zedc::testing::test_in;

/// The text of this repository's README.md.
fn page() -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../README.md");
    std::fs::read_to_string(path).expect("README.md is readable")
}

/// The table of expected results.
fn table() -> Vec<Entry> {
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("steps/l01_07_fences/readme/expected.txt");
    let text = std::fs::read_to_string(path).expect("expected.txt is readable");
    readme::entries(&text).unwrap_or_else(|e| panic!("expected.txt: {e}"))
}

/// What is wrong with `table` as the table of expected results of the fences `fences` of the
/// page `page`: an entry missing, repeated, naming no fence or out of the page's order, or an
/// entry whose results are not those the page states. A fence whose entry is missing or wrong
/// is followed by the entry the page gives it, with no checks.
pub(super) fn problems(page: &str, fences: &[DocFence], table: &[Entry]) -> Vec<String> {
    let stated = readme::stated(page);
    assert_eq!(
        stated.len(),
        fences.len(),
        "the copy has every fence of the page"
    );
    let mut out = Vec::new();
    let mut by_key: HashMap<&str, &Entry> = HashMap::with_capacity(table.len());
    for e in table {
        if by_key.insert(&e.key, e).is_some() {
            out.push(format!("the entry {} appears twice", e.key));
        }
    }
    for (f, results) in fences.iter().zip(&stated) {
        let shown = || readme::render(std::slice::from_ref(&f.key), std::slice::from_ref(results));
        let Some(entry) = by_key.get(f.key.as_str()) else {
            out.push(format!(
                "{} ({}) has no entry in the table of expected results; the page gives it:\n{}",
                f.key,
                f.at,
                shown()
            ));
            continue;
        };
        if !entry.results.iter().map(|r| &r.lines).eq(results) {
            out.push(format!(
                "{} ({}): the entry's results are not those the page states, which are:\n{}",
                f.key,
                f.at,
                shown()
            ));
        }
    }
    let keys: HashSet<&str> = fences.iter().map(|f| f.key.as_str()).collect();
    for e in table.iter().filter(|e| !keys.contains(e.key.as_str())) {
        out.push(format!("the entry {} names no fence of README.md", e.key));
    }
    let order = table.iter().map(|e| e.key.as_str());
    if out.is_empty() && !order.eq(fences.iter().map(|f| f.key.as_str())) {
        out.push("the entries are not in the order of the page's fences".into());
    }
    out
}

#[test]
fn the_copy_matches_the_readme() {
    let page = page();
    let want: Vec<(String, String)> = fence::extract(&page)
        .into_iter()
        .map(|f| (format!("README.md:{}", f.line), f.text))
        .collect();
    let got: Vec<(String, String)> = fences::readme()
        .into_iter()
        .map(|f| (f.at, f.text))
        .collect();
    assert!(
        want == got,
        "zed/fences/readme.md is out of date: run the sync tool"
    );
}

#[test]
fn every_readme_fence_lexes_and_parses_first_at_its_recorded_ring() {
    let all = fences::readme();
    assert_eq!(all.len(), 60);
    let mut wrong = Vec::new();
    for f in &all {
        let tokens = lex_fence(&f.text)
            .unwrap_or_else(|e| panic!("{} ({}) does not lex: {e} at {:?}", f.at, f.key, e.span));
        let start = if f.notation { "DocFence" } else { "Unit" };
        let lowest = (1..=TOP).find(|&k| parse(&f.text, &tokens, start, k).is_ok());
        if lowest != Some(f.ring) {
            wrong.push(format!("{}: ring {lowest:?}, recorded {}", f.at, f.ring));
        }
        assert!(
            f.layer >= fence::label(&f.text).unwrap_or(1),
            "{} is below its label",
            f.at
        );
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn every_readme_fence_has_its_entry_listing_the_results_the_page_states() {
    let problems = problems(&page(), &fences::readme(), &table());
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// The unit a fence runs as: its text, with an elision `…` read as the name `elided` as the spec
/// tools read it, then the entry's inputs, then, with `checks`, one binding per check of the entry,
/// named `readmeCheck1`, `readmeCheck2` and so on, and their number. The lines of the fence keep their numbers, so its
/// ✗ marks are where they were.
fn unit(text: &str, entry: &Entry, checks: bool) -> (String, usize) {
    let mut out = text.replace('…', "elided");
    for i in &entry.inputs {
        out.push('\n');
        out.push_str(i);
    }
    let mut k = 0;
    for c in entry
        .results
        .iter()
        .flat_map(|r| &r.checks)
        .filter(|_| checks)
    {
        k += 1;
        out.push_str(&format!("\nreadmeCheck{k} = ({c});"));
    }
    (out, k)
}

/// What is wrong with the run of `text`: a check of the table that fails, a mark with no
/// diagnostic, a diagnostic on no mark, a check that does not hold.
fn run_problems(at: &str, text: &str, checks: usize) -> Vec<String> {
    let mut db = Db::new();
    let mut out: Vec<String> = test_in(&mut db, text)
        .into_iter()
        .filter_map(|o| Some(format!("{at}, line {}: {}", o.line, o.failure?)))
        .collect();
    let front = db.front(text);
    let Ok((_, u, _)) = &*front else {
        return out;
    };
    // One index of the unit for all its checks, where `Unit::get` makes one for each.
    let cones = Cones::new(u);
    let kernels: HashMap<&str, &Arc<str>> = u
        .defs
        .iter()
        .map(|d| (d.name.as_str(), &d.kernel))
        .collect();
    for k in 1..=checks {
        let name = format!("readmeCheck{k}");
        let Some(&kernel) = kernels.get(name.as_str()) else {
            out.push(format!("{at}: `{name}` is not a binding of the unit"));
            continue;
        };
        let term = cones.close(Term::Var(kernel.clone()));
        let got = run::direct(&interp::prelude(term), &mut Evaluator::new(World::new()));
        match got {
            Ok(v) if v.to_string() == "true" => {}
            Ok(v) => out.push(format!("{at}: check {k} gives {v}, not true")),
            Err(e) => out.push(format!("{at}: check {k} stops: {e}")),
        }
    }
    out
}

/// The variants of the fence `text`: each line that is wholly a comment with a ✗, made live by
/// removing its leading `//`, so that the ✗ comment after it marks the line the checker must
/// reject, with its line in the fence.
fn variants(text: &str) -> Vec<(usize, String)> {
    let lines: Vec<&str> = text.split('\n').collect();
    fence::marks(text)
        .variants
        .into_iter()
        .map(|n| {
            let mut v = lines.clone();
            let live = v[n - 1]
                .trim_start()
                .strip_prefix("//")
                .expect("a variant line is a comment");
            v[n - 1] = live;
            (n, v.join("\n"))
        })
        .collect()
}

#[test]
fn the_enabled_readme_fences_run_with_their_stated_results() {
    let all = fences::readme();
    let table = table();
    let by_key: HashMap<&str, &Entry> = table.iter().map(|e| (e.key.as_str(), e)).collect();
    let mut ran = Vec::new();
    let mut wrong = Vec::new();
    for f in &all {
        // A fence with no entry fails the test of the table.
        let Some(&entry) = by_key.get(f.key.as_str()) else {
            continue;
        };
        if let Some(k) = entry.runs_from {
            assert!(
                k > f.layer,
                "{}: `runs from L{k}` is not above its layer",
                f.key
            );
        }
        if entry.runs_from.unwrap_or(f.layer) > ENABLED || f.notation {
            continue;
        }
        for r in &entry.results {
            if r.checks.is_empty() && r.no_check.is_none() {
                wrong.push(format!("{}: `{}` has no check", f.key, r.lines[0]));
            }
        }
        let (text, checks) = unit(&f.text, entry, true);
        let problems = run_problems(&f.at, &text, checks);
        if let Some(&(_, word, item)) = WORD_LATER.iter().find(|&&(key, _, _)| key == f.key) {
            let quoted = format!("`{word}`");
            if !problems.iter().any(|p| p.contains(&quoted)) {
                wrong.push(format!(
                    "{}: no longer stops on {quoted}; {item} has added it, so remove the fence from WORD_LATER",
                    f.key
                ));
            }
            continue;
        }
        wrong.extend(problems);
        for (n, v) in variants(&f.text) {
            if RAISED_LATER
                .iter()
                .any(|&(at, line, _)| (at, line) == (f.at.as_str(), n))
            {
                continue;
            }
            let (text, _) = unit(&v, entry, false);
            wrong.extend(run_problems(&format!("{} variant", f.at), &text, 0));
        }
        ran.push(f.key.as_str());
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    assert_eq!(
        ran,
        [
            "README.md [Numbers] 1",
            "README.md [Tests next to the code] 1"
        ]
    );
}

/// The ✗ variants of enabled fences whose row the checker does not raise yet, by the fence's
/// place and the variant's line in it, with the item that will raise it: the test of the
/// enabled fences leaves them out, and `each_readme_variant_gives_its_pinned_outcome_at_l1`
/// holds what each gives now.
const RAISED_LATER: &[(&str, usize, &str)] = &[];

/// Enabled fences that use a word this zedc does not compile yet, by the fence's key, with the
/// word and the item that adds it: the test of the enabled fences checks that each still stops
/// on its word, and fails once the word compiles, so the item that adds it removes the line and
/// the fence runs with its checks.
const WORD_LATER: &[(&str, &str, &str)] = &[("README.md [Functions] 1", "Utf8String", "STR-types")];

/// What each ✗ variant of README.md gives at L1, by the fence's place and the variant's line
/// in it: `pass`, or its first problem. Most need forms of later layers; the step that
/// enables one changes its pin.
const VARIANT_PINS: &[(&str, usize, &str)] = &[
    (
        "README.md:202",
        1,
        concat!(
            "line 1: the mark names the row \"Collision\", and the diagnostic is in no row of the rejection table: ",
            zed_tests::not_yet!("the reduction `as (region -> day -> sku -> r)`")
        ),
    ),
    (
        "README.md:559",
        4,
        concat!(
            "line 1: ",
            zed_tests::not_yet!("the reduction `with units(\"g\")`")
        ),
    ),
    ("README.md:786", 7, "pass"),
    (
        "README.md:1074",
        7,
        concat!("line 1: ", zed_tests::not_yet!("an array display")),
    ),
    (
        "README.md:1139",
        3,
        "line 2: `users` is not defined: no definition, parameter or binding in scope has this \
         name, and the prelude has none. Define `users`, or correct the name if it is misspelled.",
    ),
    (
        "README.md:1175",
        4,
        concat!(
            "line 1: ",
            zed_tests::not_yet!("the reduction `as (r -> c -> v)`")
        ),
    ),
    (
        "README.md:1270",
        6,
        concat!(
            "line 2: ",
            zed_tests::not_yet!("the reduction `as (region -> year -> sku -> amount)`")
        ),
    ),
    (
        "README.md:1705",
        6,
        concat!("line 1: ", zed_tests::not_yet!("the array type `[T; n]`")),
    ),
    (
        "README.md:2131",
        4,
        concat!("line 1: ", zed_tests::not_yet!("the refinement `[lo..]`")),
    ),
    (
        "README.md:2131",
        9,
        concat!("line 1: ", zed_tests::not_yet!("the refinement `[lo..]`")),
    ),
    (
        "README.md:2161",
        4,
        concat!(
            "line 1: ",
            zed_tests::not_yet!("the reduction `with units(\"m/s\")`")
        ),
    ),
    (
        "README.md:2161",
        9,
        concat!(
            "line 1: ",
            zed_tests::not_yet!("the reduction `with units(\"m/s\")`")
        ),
    ),
];

#[test]
fn each_readme_variant_gives_its_pinned_outcome_at_l1() {
    let table = table();
    let by_key: HashMap<&str, &Entry> = table.iter().map(|e| (e.key.as_str(), e)).collect();
    let mut got = Vec::new();
    for f in fences::readme().iter().filter(|f| !f.notation) {
        let entry = by_key[f.key.as_str()];
        for (n, v) in variants(&f.text) {
            let (text, _) = unit(&v, entry, false);
            let first = run_problems("", &text, 0).into_iter().next();
            let outcome = first.map_or("pass".to_string(), |p| {
                p.trim_start_matches(", ").to_string()
            });
            got.push((f.at.clone(), n, outcome));
        }
    }
    let want: Vec<(String, usize, String)> = VARIANT_PINS
        .iter()
        .map(|&(at, n, o)| (at.to_string(), n, o.to_string()))
        .collect();
    assert!(
        got == want,
        "{}",
        got.iter()
            .map(|(at, n, o)| format!("(\"{at}\", {n}, {o:?}),"))
            .collect::<Vec<_>>()
            .join("\n")
    );
    for &(at, n, _) in RAISED_LATER {
        assert!(
            want.iter()
                .any(|(a, m, o)| (a.as_str(), *m) == (at, n) && o != "pass"),
            "{at} line {n} is left out of the enabled fences, and its pin is not a failure"
        );
    }
}
