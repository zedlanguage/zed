//! Item REFUSAL-census-now: the refusals of the checker on today's corpus, counted. Each
//! program of the corpus is loaded through [`zedc::run::load`], and each of its diagnostics
//! that is a refusal (module `kinds`) is listed with the program, the site, the kind and the
//! reason. The lists are snapshots, so a refusal that appears or disappears fails its test.
//!
//! The corpus: every enabled fence of the spec, the examples and the README; every step unit,
//! `tests/steps/**/*.zed`; and the units the step tests compiled on the day of the census that
//! had a refusal (`programs.txt`, in pieces each under 60 s).
//!
//! The census of 2026-11-12 read all 59,664 distinct units the step tests compiled: each parsed
//! unit was written out by a hook in `ast::unit_all_errors` while the step tests ran, and each
//! was censused as here. The 120 with a refusal are `programs.txt`; the other units hold none, so
//! a refusal that appears in a program a step test writes in its own code, and not in a `.zed`
//! file, shows here only when the census is run again that way (item REFUSAL-census).

mod bench;
mod kinds;
mod programs;

use std::fmt::Write;
use std::path::Path;

use zed_tests::oracle::ENABLED;
use zedc::front::Diagnostic;
use zedc::query::Db;
use zedc::run;

/// The refusals of the unit `text`, named `origin`: one line for each diagnostic that is a
/// refusal, `origin`, then `line:col`, whether it rejects the unit or warns, its kinds and its
/// reason, separated by tabs. The reason is the message and, when the phrase of a kind lies in
/// a step or the menu, that step or the menu, every line break written `/`. A refusal that
/// only [`run::load`] reports, after the front accepted the unit, is listed at site `load`.
fn refusals(origin: &str, text: &str, out: &mut String) {
    let loaded = run::load(text.as_bytes());
    let front = Db::new().front(text);
    let (diagnostics, severity): (&[Diagnostic], &str) = match &*front {
        Ok((_, _, warnings)) => (warnings, "warning"),
        Err(ds) => (ds, "rejected"),
    };
    for d in diagnostics {
        let mut all = d.message.clone();
        for s in &d.steps {
            all.push('\n');
            all.push_str(&s.text);
        }
        all.push_str(&d.menu);
        let found = kinds::of(&all);
        if found.is_empty() {
            continue;
        }
        let mut reason = d.message.clone();
        if kinds::of(&d.message).is_empty() {
            let parts = d
                .steps
                .iter()
                .map(|s| s.text.as_str())
                .chain([d.menu.as_str()]);
            for part in parts.filter(|p| !kinds::of(p).is_empty()) {
                reason.push_str(" | ");
                reason.push_str(part);
            }
        }
        line(
            out,
            origin,
            &format!("{}:{}", d.line, d.col),
            severity,
            &found,
            &reason,
        );
    }
    match (&*front, &loaded) {
        (Err(ds), Err(why)) => {
            for d in ds {
                assert!(
                    why.contains(&d.message),
                    "{origin}: run::load does not report the rejection `{}`",
                    d.message
                );
            }
        }
        (Err(_), Ok(_)) => panic!("{origin}: run::load loads a unit the front rejects"),
        (Ok(_), Err(why)) => {
            let found = kinds::of(why);
            if !found.is_empty() {
                line(out, origin, "load", "rejected", &found, why);
            }
        }
        (Ok(_), Ok(_)) => {}
    }
}

/// Writes one line of the census to `out`.
fn line(out: &mut String, origin: &str, site: &str, severity: &str, kinds: &[&str], why: &str) {
    let why = why.trim().replace('\n', " / ");
    writeln!(
        out,
        "{origin}\t{site}\t{severity}\t{}\t{why}",
        kinds.join(",")
    )
    .expect("a String takes any write");
}

/// The totals of the census `out` by kind, one `kind: count` line each, in the order of
/// [`kinds::KINDS`] then `Other`, with the kinds that have none left out.
fn totals(out: &str) -> String {
    let mut text = String::new();
    let names = kinds::KINDS.iter().map(|k| k.name).chain(["Other"]);
    for name in names {
        let n = out
            .lines()
            .filter(|l| {
                l.split('\t')
                    .nth(3)
                    .is_some_and(|k| k.split(',').any(|k| k == name))
            })
            .count();
        if n > 0 {
            writeln!(text, "{name}: {n}").expect("a String takes any write");
        }
    }
    text
}

/// The census and its totals, as one snapshot text.
fn report(out: &str) -> String {
    format!("{}\n{out}", totals(out))
}

#[test]
fn enabled_fences() {
    let mut out = String::new();
    let fences = zed_tests::fences::all()
        .into_iter()
        .chain(zed_tests::fences::readme());
    let mut n = 0;
    for f in fences.filter(|f| f.layer <= ENABLED && !f.notation) {
        refusals(&f.key, &f.text, &mut out);
        n += 1;
    }
    assert!(n > 0, "the spec and the README have enabled fences");
    insta::assert_snapshot!(report(&out));
}

/// Every `.zed` file under `dir`, in path order.
fn units(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(dir)
        .expect("a directory of the steps")
        .map(|e| e.expect("an entry").path())
        .collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            units(&p, out);
        } else if p.extension().is_some_and(|e| e == "zed") {
            out.push(p);
        }
    }
}

#[test]
fn step_units() {
    let root = zed_tests::steps_dir();
    let mut paths = Vec::new();
    units(&root, &mut paths);
    assert!(!paths.is_empty(), "the steps hold `.zed` units");
    let mut out = String::new();
    for p in paths {
        let text = std::fs::read_to_string(&p).expect("a step unit");
        let name = p
            .strip_prefix(&root)
            .expect("under the steps")
            .display()
            .to_string();
        refusals(&name, &text, &mut out);
    }
    insta::assert_snapshot!(report(&out));
}

#[test]
fn kinds_are_found_by_their_phrases() {
    for k in kinds::KINDS {
        assert_eq!(
            kinds::of(&format!("a reason: {}; more", k.phrase)),
            vec![k.name]
        );
    }
    assert_eq!(
        kinds::of("zedc could not decide whether x holds"),
        vec!["Other"]
    );
    assert!(kinds::of("`x` is not defined").is_empty());
}

/// The census of piece `k` of the [`PIECES`] pieces of `programs.txt`.
fn programs_piece(k: usize) -> String {
    census(programs::piece(k, PIECES))
}

/// The census of `units`.
fn census(units: &[(String, String)]) -> String {
    assert!(!units.is_empty(), "the piece of the programs holds units");
    let mut out = String::new();
    for (origin, text) in units {
        refusals(origin, text, &mut out);
    }
    report(&out)
}

/// The number of pieces of `programs.txt`. Its 120 units took 45 s one after another at load
/// 41, 18 s of it one unit of 165 KB (`l01_26_type_resolution::scaling`, ArrowMeet), and the
/// pieces of 20 units it was split into first took up to 30 s each, run together at load 33.
/// Pieces of 10 units put the large units of `l01_26` and `l01_29` in different pieces.
/// Piece 4 is split once more: its units 47, 48 and 49, from `l01_29_diagnostics` (15, 42 and
/// 78 KB), took 8.4, 3.8 and 8.9 s at load 55, so each is a piece of its own.
const PIECES: usize = 12;

/// The units at `units` among the 10 of piece 4.
fn piece_4(units: std::ops::Range<usize>) -> &'static [(String, String)] {
    let piece = programs::piece(4, PIECES);
    assert_eq!(piece.len(), 10, "piece 4 of the programs holds 10 units");
    &piece[units]
}

#[test]
fn programs_0() {
    insta::assert_snapshot!(programs_piece(0));
}

#[test]
fn programs_1() {
    insta::assert_snapshot!(programs_piece(1));
}

#[test]
fn programs_2() {
    insta::assert_snapshot!(programs_piece(2));
}

#[test]
fn programs_3() {
    insta::assert_snapshot!(programs_piece(3));
}

#[test]
fn programs_4() {
    insta::assert_snapshot!(census(piece_4(0..7)));
}

#[test]
fn programs_4_unit_7() {
    insta::assert_snapshot!(census(piece_4(7..8)));
}

#[test]
fn programs_4_unit_8() {
    insta::assert_snapshot!(census(piece_4(8..9)));
}

#[test]
fn programs_4_unit_9() {
    insta::assert_snapshot!(census(piece_4(9..10)));
}

#[test]
fn programs_5() {
    insta::assert_snapshot!(programs_piece(5));
}

#[test]
fn programs_6() {
    insta::assert_snapshot!(programs_piece(6));
}

#[test]
fn programs_7() {
    insta::assert_snapshot!(programs_piece(7));
}

#[test]
fn programs_8() {
    insta::assert_snapshot!(programs_piece(8));
}

#[test]
fn programs_9() {
    insta::assert_snapshot!(programs_piece(9));
}

#[test]
fn programs_10() {
    insta::assert_snapshot!(programs_piece(10));
}

#[test]
fn programs_11() {
    insta::assert_snapshot!(programs_piece(11));
}
