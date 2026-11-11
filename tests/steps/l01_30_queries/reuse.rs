//! What an edit recomputes, and that the answers stay those of a fresh database.
//!
//! An edit script is a test of the second kind at any length (step INCR-script): a list of
//! steps, each a list of edits to a set of files, run with one database kept across the steps.
//! After each step every check equals a fresh database's: each unit's verdicts and diagnostics
//! ([`checks`]), and the package the units make, its report and each unit's resolution. The
//! script is text, so a later engine (step L7.6) can run the same scripts. Its lines that start
//! with `%% ` are directives, and the lines after a directive up to the next are its text:
//!
//! - `%% step <name>` starts a step; its edits follow.
//! - `%% write <file>` sets the file's whole text to the lines that follow, each ended by a
//!   newline.
//! - `%% replace <file>`, its lines, `%% with`, and their lines: the one place in the file
//!   holding the first lines, joined by newlines, gets the second, so one line can be part of a
//!   line. A text that is not in the file, or is in it twice, stops the script.
//! - `%% delete <file>` removes the file.
//!
//! Every file whose name ends in `.zed` is a unit and a root of the package. Only checking is
//! compared so far: what the front end, the tables and the loader answer, not a built program.

use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;

use zed_tests::scaling;
use zedc::ast::Error;
use zedc::query::{Db, Query};
use zedc::resolve::Resolution;
use zedc::unit::{Loaded, Memory, Package, load};

use super::{PRICING, checks};

/// The counts of the three queries computed so far.
fn counts(db: &Db) -> [usize; 3] {
    [Query::Front, Query::Row, Query::Wave].map(|q| db.computed(q))
}

#[test]
fn asking_again_recomputes_nothing() {
    let mut db = Db::new();
    let first = checks(&mut db, PRICING);
    assert_eq!(
        first,
        ["2:8: ok", "2:19: ok", "5:8: ok", "5:22: ok", "8:8: ok"]
    );
    assert_eq!(counts(&db), [1, 5, 0]);
    assert_eq!(checks(&mut db, PRICING), first);
    assert_eq!(counts(&db), [1, 5, 0]);
}

#[test]
fn a_comment_reruns_the_front_end_and_no_row() {
    let mut db = Db::new();
    checks(&mut db, PRICING);
    let edited = format!("// prices in cents\n{PRICING}");
    let got = checks(&mut db, &edited);
    // The rows' places move with the text; their results are reused.
    assert_eq!(
        got,
        ["3:8: ok", "3:19: ok", "6:8: ok", "6:22: ok", "9:8: ok"]
    );
    assert_eq!(counts(&db), [2, 5, 0]);
}

#[test]
fn an_edit_reruns_the_rows_that_reach_the_changed_definition() {
    let mut db = Db::new();
    checks(&mut db, PRICING);
    // The tax rate goes to 10%: `tax`'s two rows and `total`'s row read `tax`; `discount`'s
    // two rows do not.
    let edited = PRICING.replace("cents * 8 div 100", "cents * 10 div 100");
    let got = checks(&mut db, &edited);
    assert_eq!(
        got,
        [
            "2:8: ok",
            "2:19: ok",
            "5:8: `10000 -> 800` of `tax`: the result is 1000",
            "5:22: `2500 -> 200` of `tax`: the result is 250",
            "8:8: `20000 -> 19440` of `total`: the result is 19800",
        ]
    );
    assert_eq!(counts(&db), [2, 8, 0]);
}

#[test]
fn a_new_row_is_the_only_row_computed() {
    let mut db = Db::new();
    checks(&mut db, PRICING);
    let edited = PRICING.replace("20000 -> 2000 }", "20000 -> 2000, 10000 -> 1000 }");
    let got = checks(&mut db, &edited);
    assert_eq!(got[2], "2:34: ok");
    assert_eq!(counts(&db), [2, 6, 0]);
}

#[test]
fn a_rejected_unit_is_kept_with_its_diagnostics() {
    let mut db = Db::new();
    let bad = "tax(positional cents: int) = cents * \"8\";\n";
    let first = checks(&mut db, bad);
    assert_eq!(first.len(), 1);
    // The outcome carries the diagnostic's derivation, as `zedc test` prints it.
    assert!(
        first[0]
            .starts_with("1:30: `*` does not take (int, \"8\"): these are the types of its arguments here, and `*` has no arrow that takes them all\n  [1] 1:30: `cents` is int here\n"),
        "{first:?}"
    );
    assert_eq!(checks(&mut db, bad), first);
    assert_eq!(counts(&db), [1, 0, 0]);
}

#[test]
fn a_wave_row_is_reused_until_main_or_what_it_reads_changes() {
    let src = "shout(positional s: String) = upper(s) ++ \"!\";\n\
               whisper(positional s: String) = lower(s);\n\
               main(m: MainArgs) {\n  m.stdout <- shout(m.stdin[1] else \"\");\n}\n\
               test { \"hi\" -> \"HI!\\n\" }\n";
    let mut db = Db::new();
    assert_eq!(checks(&mut db, src), ["6:8: ok"]);
    // `whisper` is not read by `main`: the wave is reused.
    let other = src.replace("lower(s)", "lower(s) ++ \"...\"");
    assert_eq!(checks(&mut db, &other), ["6:8: ok"]);
    assert_eq!(counts(&db), [2, 0, 1]);
    // `shout` is: the wave runs again.
    let read = src.replace("\"!\"", "\"!!\"");
    assert_eq!(
        checks(&mut db, &read),
        ["6:8: `\"hi\" -> \"HI!\\n\"` of `main`: `m.stdout` writes \"HI!!\\n\""]
    );
    assert_eq!(counts(&db), [3, 0, 2]);
}

/// One edit of a script; its texts are slices of the script.
enum Edit<'a> {
    /// The file gets the whole text.
    Write { file: &'a str, text: &'a str },
    /// The one place in the file holding `old` gets `new`.
    Replace {
        file: &'a str,
        old: &'a str,
        new: &'a str,
    },
    /// The file is removed.
    Delete { file: &'a str },
}

/// A step of a script: its name and its edits, in order.
struct Step<'a> {
    name: &'a str,
    edits: Vec<Edit<'a>>,
}

/// The steps of `script`, in order. A malformed script stops the test with the line at fault.
fn parse<'a>(script: &'a str) -> Vec<Step<'a>> {
    // Each directive, with its line number and the text from the line after it to the next
    // directive; the text before the first directive must be empty.
    let mut directives: Vec<(usize, &str, &str)> = Vec::new();
    let mut body_start = 0;
    let mut at = 0;
    for (i, line) in script.split_inclusive('\n').enumerate() {
        if let Some(d) = line.strip_prefix("%% ") {
            let body = &script[body_start..at];
            match directives.last_mut() {
                Some(last) => last.2 = body,
                None => assert!(
                    body.is_empty(),
                    "line 1: a script starts with a directive, not with text"
                ),
            }
            directives.push((i + 1, d.trim_end_matches('\n'), ""));
            body_start = at + line.len();
        }
        at += line.len();
    }
    match directives.last_mut() {
        Some(last) => last.2 = &script[body_start..],
        None => panic!("the script has no directive"),
    }
    // A replace's text is its lines joined by newlines, without the last line's newline.
    let joined = |body: &'a str| body.strip_suffix('\n').unwrap_or(body);
    let mut steps: Vec<Step<'a>> = Vec::new();
    let mut it = directives.into_iter();
    while let Some((line, d, body)) = it.next() {
        let (word, arg) = d.split_once(' ').unwrap_or((d, ""));
        if word == "step" {
            assert!(
                body.is_empty(),
                "line {line}: text after `%% step` and before its first edit"
            );
            steps.push(Step {
                name: arg,
                edits: Vec::new(),
            });
            continue;
        }
        let step = steps
            .last_mut()
            .unwrap_or_else(|| panic!("line {line}: an edit before the first `%% step`"));
        assert!(
            word == "with" || !arg.is_empty(),
            "line {line}: `%% {word}` names no file"
        );
        let edit = match word {
            "write" => Edit::Write {
                file: arg,
                text: body,
            },
            "replace" => {
                let old = joined(body);
                assert!(!old.is_empty(), "line {line}: an empty text to replace");
                let Some((_, "with", new)) = it.next() else {
                    panic!("line {line}: `%% replace` with no `%% with` after its text");
                };
                Edit::Replace {
                    file: arg,
                    old,
                    new: joined(new),
                }
            }
            "delete" => {
                assert!(body.is_empty(), "line {line}: text after `%% delete`");
                Edit::Delete { file: arg }
            }
            "with" => panic!("line {line}: `%% with` with no `%% replace` before it"),
            _ => panic!("line {line}: `%% {word}` is no directive"),
        };
        step.edits.push(edit);
    }
    steps
}

/// The files after `edit`, made in the step `step`.
fn apply(files: &mut HashMap<String, Arc<str>>, edit: &Edit<'_>, step: &str) {
    match *edit {
        Edit::Write { file, text } => {
            files.insert(file.to_string(), Arc::from(text));
        }
        Edit::Replace { file, old, new } => {
            let text = files
                .get_mut(file)
                .unwrap_or_else(|| panic!("step `{step}`: no file `{file}` to edit"));
            let mut places = text.match_indices(old).map(|(i, _)| i);
            let Some(i) = places.next() else {
                panic!("step `{step}`: `{file}` does not hold {old:?}");
            };
            assert!(
                places.next().is_none(),
                "step `{step}`: `{file}` holds {old:?} more than once"
            );
            *text = Arc::from([&text[..i], new, &text[i + old.len()..]].concat());
        }
        Edit::Delete { file } => {
            assert!(
                files.remove(file).is_some(),
                "step `{step}`: no file `{file}` to delete"
            );
        }
    }
}

/// The queries, in the order [`computed`] counts them.
const QUERIES: [Query; 5] = [
    Query::Front,
    Query::Row,
    Query::Wave,
    Query::Parse,
    Query::Resolve,
];

/// How many times each of [`QUERIES`] has been computed in `db`.
fn computed(db: &Db) -> [usize; 5] {
    QUERIES.map(|q| db.computed(q))
}

/// The resolution of the unit `u`: its names, errors and forms of later steps.
fn resolution(u: &Loaded) -> Option<(&Resolution, &[Error], &[Error])> {
    u.resolved
        .as_deref()
        .map(|r| (&r.res, r.errors.as_slice(), r.later.as_slice()))
}

/// The paths of the units of `p` in its dependency order.
fn order(p: &Package) -> Vec<&str> {
    p.order.iter().map(|&i| &*p.units[i].path).collect()
}

/// What a step of a script gave.
struct Ran {
    /// How many times each of [`QUERIES`] had been computed in the kept database.
    computed: [usize; 5],
    /// The package's report, then each unit's checks as `file line:col: ok` or
    /// `file line:col: why`, the units in order of their files.
    seen: Vec<String>,
}

/// Checks the files `files` with `db` and with a fresh database, and that the two agree after
/// the step `step`: each unit's checks, and the package's report, order and resolutions. Returns
/// the report and the checks, as [`Ran::seen`] holds them.
fn same_as_fresh(db: &mut Db, files: &Memory, step: &str) -> Vec<String> {
    let mut names: Vec<&str> = files.0.keys().map(String::as_str).collect();
    names.sort_unstable();
    let roots: Vec<&str> = names
        .iter()
        .filter_map(|f| f.strip_suffix(".zed"))
        .collect();
    let warm = load(db, files, &roots);
    let cold = load(&mut Db::new(), files, &roots);
    let mut seen = warm.report(Path::new(""));
    assert_eq!(
        seen,
        cold.report(Path::new("")),
        "step `{step}`: the package's report"
    );
    assert_eq!(
        order(&warm),
        order(&cold),
        "step `{step}`: the units' order"
    );
    assert_eq!(
        warm.units.len(),
        cold.units.len(),
        "step `{step}`: the units"
    );
    for u in &cold.units {
        let w = warm
            .unit(&u.path)
            .unwrap_or_else(|| panic!("step `{step}`: the kept database misses unit `{}`", u.path));
        assert!(
            resolution(w) == resolution(u),
            "step `{step}`: the resolution of `{}`",
            u.path
        );
    }
    for name in names.iter().filter(|f| f.ends_with(".zed")) {
        let text = &files.0[*name];
        let got = checks(db, text);
        assert_eq!(
            got,
            checks(&mut Db::new(), text),
            "step `{step}`: the checks of `{name}`"
        );
        seen.extend(got.into_iter().map(|c| format!("{name} {c}")));
    }
    seen
}

/// Runs `script` with one database kept across its steps and checks that after each step every
/// answer equals a fresh database's. Returns what each step gave.
fn run(script: &str) -> Vec<Ran> {
    let mut db = Db::new();
    let mut files = Memory(HashMap::new());
    parse(script)
        .iter()
        .map(|step| {
            for edit in &step.edits {
                apply(&mut files.0, edit, step.name);
            }
            let seen = same_as_fresh(&mut db, &files, step.name);
            Ran {
                computed: computed(&db),
                seen,
            }
        })
        .collect()
}

#[test]
fn every_answer_equals_a_fresh_databases() {
    let script = format!(
        "%% step the pricing unit
%% write pricing.zed
{PRICING}%% step a bigger discount
%% replace pricing.zed
cents div 10
%% with
cents div 5
%% step the total's row follows
%% replace pricing.zed
19440
%% with
17280
%% step back, with a comment on top
%% replace pricing.zed
cents div 5
%% with
cents div 10
%% replace pricing.zed
17280
%% with
19440
%% replace pricing.zed
discount(positional
%% with
// v2
discount(positional
%% step tax on the full price
%% replace pricing.zed
// v2
discount(positional
%% with
discount(positional
%% replace pricing.zed
tax(cents - discount(cents))
%% with
tax(cents)
%% step the first text again
%% replace pricing.zed
tax(cents)
%% with
tax(cents - discount(cents))
"
    );
    let ran = run(&script);
    // The last text is the first again: nothing is computed for it, and it checks as it did.
    assert_eq!(ran[5].computed, ran[4].computed);
    assert_eq!(ran[5].seen, ran[0].seen);
}

/// Whether a line of `seen` holds `part`.
fn says(seen: &[String], part: &str) -> bool {
    seen.iter().any(|s| s.contains(part))
}

#[test]
fn a_type_error_added_then_removed() {
    let script = format!(
        "%% step the pricing unit
%% write pricing.zed
{PRICING}%% step the tax rate written as a string
%% replace pricing.zed
cents * 8 div 100
%% with
cents * \"8\" div 100
%% step the rate is a number again
%% replace pricing.zed
cents * \"8\" div 100
%% with
cents * 8 div 100
"
    );
    let ran = run(&script);
    // The rejected unit's front end is computed and no row runs; the fixed unit is the first
    // text, so nothing is computed for it.
    assert!(says(
        &ran[1].seen,
        "pricing.zed 4:30: `*` does not take (int, \"8\"): these are the types of its arguments here, and `*` has no arrow that takes them all"
    ));
    assert!(says(
        &ran[1].seen,
        "`10000 -> 800` of `tax`: not run, since the unit is rejected"
    ));
    assert_eq!(ran[1].computed, [2, 5, 0, 2, 2]);
    assert_eq!(ran[2].computed, ran[1].computed);
    assert_eq!(ran[2].seen, ran[0].seen);
}

/// A package of three units: `main` imports `net` from `pricing`.
const PACKAGE: &str = "\
%% step a package of three units
%% write main.zed
import pricing.{net};
total = net(100.0);
%% write pricing.zed
net(gross: f64) = gross / 1.2;
%% write shipping.zed
fee = 4.5;
";

#[test]
fn a_renamed_definition() {
    let script = format!(
        "{PACKAGE}%% step `net` is renamed `net_of_vat` in its own unit only
%% replace pricing.zed
net(gross
%% with
net_of_vat(gross
%% step `main` follows the rename
%% replace main.zed
import pricing.{{net}};
total = net(100.0);
%% with
import pricing.{{net_of_vat}};
total = net_of_vat(100.0);
"
    );
    let ran = run(&script);
    // The rename changes `pricing`'s exports, so `main` is resolved again and finds no `net`;
    // once `main` follows, only `main` is resolved again.
    let missing = "main.zed:1:1: the unit `pricing` defines no `net`";
    assert!(!says(&ran[0].seen, missing));
    assert!(says(&ran[1].seen, missing));
    assert!(!says(&ran[2].seen, missing));
    assert_eq!(ran[1].computed[4] - ran[0].computed[4], 2);
    assert_eq!(ran[2].computed[4] - ran[1].computed[4], 1);
}

#[test]
fn a_changed_import_edge() {
    let script = format!(
        "{PACKAGE}%% step `main` adds the fee from `shipping`
%% replace main.zed
import pricing.{{net}};
total = net(100.0);
%% with
import pricing.{{net}};
import shipping.{{fee}};
total = net(100.0) + fee;
%% step the fee moves to `pricing`
%% write pricing.zed
net(gross: f64) = gross / 1.2;
fee = 5.0;
%% replace main.zed
import pricing.{{net}};
import shipping.{{fee}};
%% with
import pricing.{{net, fee}};
%% delete shipping.zed
%% step `pricing` imports `main`, a cycle
%% replace pricing.zed
fee = 5.0;
%% with
import main.{{total}};
fee = 5.0;
%% step the cycle is removed
%% replace pricing.zed
import main.{{total}};
%% with
%% step `main` imports a unit that does not exist
%% replace main.zed
import pricing.{{net, fee}};
%% with
import pricing.{{net, fee}};
import duty.{{rate}};
"
    );
    let ran = run(&script);
    let cycle = "the imports form a cycle";
    let absent = "main.zed:2:1: the unit `duty` cannot be imported: there is no file `duty.zed`";
    let said: Vec<[bool; 2]> = ran
        .iter()
        .map(|r| [says(&r.seen, cycle), says(&r.seen, absent)])
        .collect();
    assert_eq!(
        said,
        [
            [false, false],
            [false, false],
            [false, false],
            [true, false],
            [false, false],
            [false, true]
        ]
    );
}

#[test]
#[should_panic(expected = "step `missing`: `pricing.zed` does not hold \"cents div 7\"")]
fn a_replace_of_text_the_file_lacks_stops_the_script() {
    run(&format!(
        "%% step start\n%% write pricing.zed\n{PRICING}%% step missing\n\
         %% replace pricing.zed\ncents div 7\n%% with\ncents div 5\n"
    ));
}

#[test]
#[should_panic(expected = "line 3: `%% replace` with no `%% with` after its text")]
fn a_replace_without_its_with_stops_the_script() {
    parse("%% step start\n%% write a.zed\n%% replace a.zed\nx\n");
}

/// A script of `k` steps after the first, each changing the tax rate of the pricing unit that a
/// second unit imports from.
fn rates(k: usize) -> String {
    let mut s = format!(
        "%% step start\n%% write main.zed\nimport pricing.{{tax}};\nlevy = tax(100);\n\
         %% write pricing.zed\n{PRICING}"
    );
    for i in 0..k {
        // Rates 8, 9, 10, ...: each step's text is new to the kept database.
        s.push_str(&format!(
            "%% step rate {to}\n%% replace pricing.zed\ncents * {from} div 100\n%% with\n\
             cents * {to} div 100\n",
            from = i + 8,
            to = i + 9
        ));
    }
    s
}

#[test]
fn a_script_runs_in_time_linear_in_its_steps() {
    let n = 8;
    let scripts: HashMap<usize, String> = [n, 8 * n].into_iter().map(|k| (k, rates(k))).collect();
    scaling::check("an edit script of n steps", n, |k| {
        std::hint::black_box(run(&scripts[&k]));
    });
}
