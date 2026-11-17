//! The `sync` command: the copies of the spec it writes, `--check`, and the checks of the
//! spec's prose it runs. This file spells the kernel rule names to test the list of them, so
//! l01_21's `no_message_names_a_kernel_rule` leaves it out, as it leaves out its own file.

use std::fs;

use zed_tools::spec::Spec;
use zed_tools::{fence_layers, spec_checks, sync};

use super::{DOUBLE, design, fence, grammar, spec_dir};
use zed_tests::step_helpers::m0_03_grammar_tools::{KERNEL, zed_dir};

/// Two tables of step M0.7's serialization, the first ended by a paragraph, the second by a
/// blank line, and between them a table whose header does not end as theirs do.
const SERIAL: &str = "| Grade | Tag | Fields in order |\n|---|---|---|\n| Axiom | 0 | — |\n\
                      | Proved | 2 | — |\nA note.\n\n| Kind | Code | Fields in order |\n|---|---|---|\n\
                      | Other | 9 | — |\n\n| Value | Tag | Fields in order |\n|---|---|---|\n\
                      | Boolean | 0 | `value: byte` |\n\n| Primitive | Code |\n|---|---|\n\
                      | `a + b` | 0 |\n\n| Primitive | Code | Note |\n|---|---|---|\n\
                      | `a - b` | 1 | — |\n";

/// `sync` writes every copy, `--check` then passes, and a copy edited by hand is out of date.
/// A ```` ```text ```` fence inside a list item is copied with its indentation taken off.
#[test]
fn sync_writes_the_copies_and_check_finds_a_stale_one() {
    let body = format!(
        "{}\n- A report:\n\n  ```text\n  trivial models of T\n    one line\n  ```\n\n{SERIAL}\n{KERNEL}",
        fence(DOUBLE)
    );
    let dir = spec_dir("sync", &design(&body), &fence(DOUBLE));
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let zed = zed_dir("sync_zed");
    let run = |check| {
        let mut out = String::new();
        (sync::sync_into(&spec, &zed.root(), check, &mut out), out)
    };
    let (outcome, _) = run(true);
    assert_eq!(outcome, Ok(false), "nothing is written yet");
    let (outcome, out) = run(false);
    assert_eq!(outcome, Ok(true), "{out}");
    for name in ["syntax.peg", "lexical.peg", "notation.peg", "desugar.txt"] {
        assert_eq!(
            fs::read_to_string(zed.at(&format!("grammar/{name}"))).unwrap(),
            grammar(name),
            "{name}"
        );
    }
    let copied = fs::read_to_string(zed.at("fences/design.md")).unwrap();
    assert!(
        copied.contains("DESIGN.md:") && copied.contains(DOUBLE),
        "{copied}"
    );
    let messages = fs::read_to_string(zed.at("fences/messages.md")).unwrap();
    assert!(
        messages.contains("\n```text\ntrivial models of T\n  one line\n```\n"),
        "{messages}"
    );
    assert_eq!(
        fs::read_to_string(zed.at("fences/kernel-rules.txt")).unwrap(),
        "Boom\nT-Discard\nT-Fam\nT-Fix\nT-Fold\nT-Gen\nT-Port\nT-Reindex\n"
    );
    assert_eq!(
        fs::read_to_string(zed.at("fences/canon-serial.md")).unwrap(),
        "| Grade | Tag | Fields in order |\n| Axiom | 0 | — |\n\
         | Proved | 2 | — |\n| Value | Tag | Fields in order |\n| Boolean | 0 | `value: byte` |\n\
         | Primitive | Code |\n| `a + b` | 0 |\n",
        "the tables of M0.7's serialization and its codes of primitives, without the line \
         under each header, the table of the same shape whose header names no tag, or a table \
         whose header only starts as the codes' does"
    );
    let words = fs::read_to_string(zed.at("grammar/words.md")).unwrap();
    assert!(
        words.ends_with(
            "| L1 | — | — | `len` |\n| L3 | — | — | `sorted` |\n| L7 | — | — | `log` |\n"
        ),
        "{words}"
    );
    assert_eq!(run(true).0, Ok(true));

    zed.write("fences/design.md", "edited by hand\n");
    let (outcome, out) = run(true);
    assert_eq!(outcome, Ok(false));
    assert_eq!(out, "design.md is out of date\n");
}

/// A spec with no kernel grammar stops `sync` before it writes anything: with no words to ban,
/// the test that no message names a kernel rule would pass on any message.
#[test]
fn sync_refuses_a_spec_with_no_kernel_grammar() {
    let dir = spec_dir("sync_no_kernel", &design(&fence(DOUBLE)), "");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let zed = zed_dir("sync_no_kernel_zed");
    let mut out = String::new();
    let why = sync::sync_into(&spec, &zed.root(), false, &mut out).expect_err("no sec:kernel");
    assert!(why.contains("sec:kernel"), "{why}");
    assert!(fs::read_dir(zed.at("fences")).unwrap().next().is_none());
}

/// The copy of the table of words gives each fence the layer DESIGN.md's table gives it, though
/// it keeps only each cell's backquoted words.
#[test]
fn the_copied_table_of_words_lays_out_the_fences_as_the_spec_does() {
    let table = "| Layer | Annotations | Facet words | Words |\n|---|---|---|---|\n\
                 | L1 | — | — | `len`, and prose |\n\
                 | L3 | `@pure` (see below) | `::size` here | `sorted`, `#notFound` and `max` |\n\
                 | L7 | | | the port `log` |\n";
    let body = format!(
        "{}\n{}\n{}\n{KERNEL}",
        fence(DOUBLE),
        fence("y = sorted(x);"),
        fence("z = max(x, y);")
    );
    let text = design(&body).replacen(
        "| Layer | Annotations | Facet words | Words |\n|---|---|---|---|\n\
         | L1 | | | `len` |\n| L3 | | | `sorted` |\n| L7 | | | `log` |\n",
        table,
        1,
    );
    assert!(text.contains("and prose"), "the table is replaced");
    let dir = spec_dir("sync_words", &text, "");
    fs::create_dir_all(format!("{}/zed/fences", dir.root())).unwrap();
    fs::create_dir_all(format!("{}/zed/grammar", dir.root())).unwrap();
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let mut out = String::new();
    let zed = format!("{}/zed", dir.root());
    assert_eq!(
        sync::sync_into(&spec, &zed, false, &mut out),
        Ok(true),
        "{out}"
    );
    let copy = Spec::of_impl(&dir.root()).expect("the copied grammars read");
    let layers = |spec: &Spec| -> Vec<u32> {
        fence_layers::of_document(&dir.at("DESIGN.md"), spec)
            .expect("the fences lay out")
            .iter()
            .map(|f| f.layer)
            .collect()
    };
    assert_eq!(layers(&spec), [1, 3, 3]);
    assert_eq!(layers(&copy), layers(&spec));
}

/// A word a cell names again, as DESIGN.md's L3 row names `split` and `concat` again in the note
/// that explains them, is listed once, where it first appears; a word only the note names, as
/// L15's tactics are, is kept.
#[test]
fn a_word_named_again_in_a_note_is_listed_once() {
    let table = "| Layer | Annotations | Facet words | Words |\n|---|---|---|---|\n\
                 | L1 | | | `len` |\n\
                 | L3 | | | `sorted`, `split`, `concat` (`split` keeps every piece; `concat` \
                 takes strings, `max` too) |\n\
                 | L7 | | | `log` |\n";
    let text = design(&format!("{}\n{KERNEL}", fence(DOUBLE))).replacen(
        "| Layer | Annotations | Facet words | Words |\n|---|---|---|---|\n\
         | L1 | | | `len` |\n| L3 | | | `sorted` |\n| L7 | | | `log` |\n",
        table,
        1,
    );
    assert!(text.contains("takes strings"), "the table is replaced");
    let dir = spec_dir("sync_words_once", &text, "");
    fs::create_dir_all(format!("{}/zed/fences", dir.root())).unwrap();
    fs::create_dir_all(format!("{}/zed/grammar", dir.root())).unwrap();
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let mut out = String::new();
    let zed = format!("{}/zed", dir.root());
    assert_eq!(
        sync::sync_into(&spec, &zed, false, &mut out),
        Ok(true),
        "{out}"
    );
    let words = fs::read_to_string(format!("{zed}/grammar/words.md")).unwrap();
    assert!(
        words.contains("\n| L3 | — | — | `sorted`, `split`, `concat`, `max` |\n"),
        "{words}"
    );
}

/// `sync` writes the spec commit the copies come from to `zed/synced-from`
/// (MERGE-spec-lag-by-pin): `unknown` for a spec directory that is not the top of a git checkout
/// (this one lies under build/, inside zed-impl's own checkout, whose commit is not the spec's),
/// the HEAD commit for a clean checkout, and that commit marked when DESIGN.md has uncommitted
/// changes. `--check` neither writes nor compares the stamp.
#[test]
fn sync_writes_the_spec_commit_it_copied_from() {
    let body = format!("{}\n{KERNEL}", fence(DOUBLE));
    let dir = spec_dir("sync_stamp", &design(&body), &fence(DOUBLE));
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let zed = zed_dir("sync_stamp_zed");
    let stamp = || fs::read_to_string(zed.at(sync::STAMP)).unwrap();
    let run = |check| {
        let mut out = String::new();
        (sync::sync_into(&spec, &zed.root(), check, &mut out), out)
    };
    let (outcome, out) = run(true);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(!out.contains("synced-from"), "{out}");
    assert!(
        !std::path::Path::new(&zed.at(sync::STAMP)).exists(),
        "--check writes no stamp"
    );
    let (outcome, out) = run(false);
    assert_eq!(outcome, Ok(true), "{out}");
    assert_eq!(stamp(), "unknown\n");
    let git = |args: &[&str]| {
        let out = std::process::Command::new("git")
            .args(["-C", &dir.root(), "-c", "user.name=test"])
            .args([
                "-c",
                "user.email=test@example.invalid",
                "-c",
                "commit.gpgsign=false",
            ])
            .args(args)
            .output()
            .expect("git runs");
        assert!(out.status.success(), "git {args:?}: {out:?}");
        String::from_utf8(out.stdout).unwrap().trim().to_string()
    };
    git(&["init", "-q"]);
    git(&["add", "DESIGN.md", "EXAMPLES.md"]);
    git(&["commit", "-q", "-m", "spec"]);
    let head = git(&["rev-parse", "HEAD"]);
    let (outcome, out) = run(false);
    assert_eq!(outcome, Ok(true), "{out}");
    assert!(out.contains("synced-from is written"), "{out}");
    assert_eq!(stamp(), format!("{head}\n"));
    let (outcome, out) = run(true);
    assert_eq!(
        outcome,
        Ok(true),
        "the stamp is not a copy --check compares: {out}"
    );
    fs::write(
        dir.at("DESIGN.md"),
        design(&format!("{body}\nA new line.\n")),
    )
    .unwrap();
    assert_eq!(
        sync::spec_commit(&dir.root()),
        format!("{head} with uncommitted changes")
    );
}

/// A copy held back with `--hold` keeps, in `zed/synced-from`, the commit it was written from
/// while the first line moves on (SYNC-held-files-stamp): the stamp named only the last sync's
/// commit, so merge-push counted a held copy's lag from there and missed the commits before it.
/// `--check` names a held copy's own commit; the line goes once the copy is written, and a
/// held copy that is current needs none.
#[test]
fn a_held_copy_keeps_its_own_commit_in_the_stamp() {
    let body = format!("{}\n{KERNEL}", fence(DOUBLE));
    let dir = spec_dir("sync_held", &design(&body), &fence(DOUBLE));
    let zed = zed_dir("sync_held_zed");
    let stamp = || fs::read_to_string(zed.at(sync::STAMP)).unwrap();
    let run = |check, hold: &[&str]| {
        let spec = Spec::open(&dir.root()).expect("the spec reads");
        let hold: Vec<String> = hold.iter().map(|h| h.to_string()).collect();
        let mut out = String::new();
        (
            sync::sync_holding(&spec, &zed.root(), check, &hold, &mut out),
            out,
        )
    };
    let git = |args: &[&str]| {
        let out = std::process::Command::new("git")
            .args(["-C", &dir.root(), "-c", "user.name=test"])
            .args([
                "-c",
                "user.email=test@example.invalid",
                "-c",
                "commit.gpgsign=false",
            ])
            .args(args)
            .output()
            .expect("git runs");
        assert!(out.status.success(), "git {args:?}: {out:?}");
        String::from_utf8(out.stdout).unwrap().trim().to_string()
    };
    let commit = |text: &str| {
        fs::write(dir.at("DESIGN.md"), design(text)).unwrap();
        git(&["add", "DESIGN.md", "EXAMPLES.md"]);
        git(&["commit", "-q", "-m", "spec"]);
        git(&["rev-parse", "HEAD"])
    };
    git(&["init", "-q"]);
    let first = commit(&body);
    assert_eq!(run(false, &[]).0, Ok(true));
    assert_eq!(run(false, &["design.md"]).0, Ok(true));
    assert_eq!(
        stamp(),
        format!("{first}\n"),
        "a current held copy needs no line"
    );

    let body = format!("{}\n{body}", fence("triple(x: int) -> int = x * 3;"));
    let second = commit(&body);
    let (outcome, out) = run(false, &["design.md"]);
    assert_eq!(outcome, Ok(true), "{out}");
    assert!(
        out.contains(&format!("design.md is held, copied from zed {first}")),
        "{out}"
    );
    assert_eq!(stamp(), format!("{second}\ndesign.md {first}\n"));
    let (outcome, out) = run(true, &[]);
    assert_eq!(outcome, Ok(false));
    assert_eq!(
        out,
        format!("design.md is out of date, copied from zed {first}\n")
    );

    let body = format!("{}\n{body}", fence("half(x: int) -> int = x / 2;"));
    let third = commit(&body);
    assert_eq!(run(false, &["design.md"]).0, Ok(true));
    assert_eq!(
        stamp(),
        format!("{third}\ndesign.md {first}\n"),
        "a later sync that still holds the copy keeps its commit"
    );

    let (outcome, out) = run(false, &[]);
    assert_eq!(outcome, Ok(true), "{out}");
    assert!(out.contains("design.md is written"), "{out}");
    assert_eq!(stamp(), format!("{third}\n"));
    assert_eq!(run(true, &[]).0, Ok(true));

    let (outcome, _) = run(false, &["design.txt"]);
    assert!(
        outcome
            .as_ref()
            .is_err_and(|e| e.contains("--hold design.txt")),
        "{outcome:?}"
    );
}

/// The spec checkout `sync` reads: the one directory it is given, else `ZED_SPEC_DIR`; `--check`
/// and `--hold COPY` are no directory, and two directories or none, or `--hold` with no copy, is
/// a usage error.
#[test]
fn sync_reads_the_directory_it_is_given_or_else_the_variable() {
    let args = |a: &[&str]| -> Vec<String> { a.iter().map(|s| s.to_string()).collect() };
    let var = || Some("/from/var".to_string());
    assert_eq!(sync::spec_dir(&args(&["/a"]), var()), Ok("/a".into()));
    assert_eq!(
        sync::spec_dir(&args(&["--check", "/a"]), None),
        Ok("/a".into())
    );
    assert_eq!(
        sync::spec_dir(&args(&["--check"]), var()),
        Ok("/from/var".into())
    );
    assert!(sync::spec_dir(&args(&[]), None).is_err());
    assert!(sync::spec_dir(&args(&[]), Some(String::new())).is_err());
    assert!(sync::spec_dir(&args(&["/a", "/b"]), var()).is_err());
    assert_eq!(
        sync::spec_dir(&args(&["--hold", "syntax.peg", "/a", "--hold", "x"]), None),
        Ok("/a".into()),
        "a held copy's name is no directory"
    );
    assert!(sync::spec_dir(&args(&["/a", "--hold"]), None).is_err());
}

/// The prelude laws `sync` checks DESIGN.md for: named where step L15.7 builds them and where its
/// test brings them to proof grade, and stated in sec:verification, `allIntro` as the mathlib
/// study writes it. A law missing from any of the three is named.
#[test]
fn sync_checks_the_prelude_laws_design_states() {
    let laws = "`anyIntro`, `anyElim`, `allElim` and `allIntro`";
    let design = format!(
        "L15.7. Build the prelude laws {laws}; test: {laws} reach proof grade.\n\
         The prelude also states `anyIntro`, `anyElim`, `allElim` and \
         `law allIntro(p: P) -> Q`. More.\n"
    );
    let page = "law allIntro(p: P) -> Q proof { done }\n";
    assert_eq!(spec_checks::prelude_laws(&design, page), Ok(()));
    let short = design.replacen(" and `allIntro`;", ";", 1);
    assert!(spec_checks::prelude_laws(&short, page).is_err());
    let other = "law allIntro(p: P) -> R proof { done }\n";
    let why = spec_checks::prelude_laws(&design, other).expect_err("stated otherwise");
    assert!(why.contains("allIntro(p: P) -> R"), "{why}");
}

/// The build modes `sync` checks DESIGN.md for: a bullet whose table lacks a row is named.
#[test]
fn sync_checks_the_build_modes_table() {
    let design = "Intro.\n- **Build modes.** A *debug build*.\n\n| | Debug build | Optimized build |\n\
                  |---|---|---|\n| Values | the definitional interpreter | the same |\n\n\
                  - **Next.** Text.\n";
    let why = spec_checks::build_modes(design).expect_err("no row Log mode");
    assert!(why.contains("Log mode"), "{why}");
    assert!(spec_checks::build_modes("No bullet.\n").is_err());
}
