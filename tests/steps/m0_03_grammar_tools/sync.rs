//! The `sync` command: the copies of the spec it writes, `--check`, and the checks of the
//! spec's prose it runs. This file spells the kernel rule names to test the list of them, so
//! l01_21's `no_message_names_a_kernel_rule` leaves it out, as it leaves out its own file.

use std::fs;

use zed_tools::spec::Spec;
use zed_tools::{fence_layers, spec_checks, sync};

use super::{DOUBLE, design, fence, grammar, spec_dir};
use zed_tests::step_helpers::m0_03_grammar_tools::{KERNEL, zed_dir};

/// `sync` writes every copy, `--check` then passes, and a copy edited by hand is out of date.
/// A ```` ```text ```` fence inside a list item is copied with its indentation taken off.
#[test]
fn sync_writes_the_copies_and_check_finds_a_stale_one() {
    let body = format!(
        "{}\n- A report:\n\n  ```text\n  trivial models of T\n    one line\n  ```\n\n{KERNEL}",
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

/// The spec checkout `sync` reads: the one directory it is given, else `ZED_SPEC_DIR`; `--check`
/// is no directory, and two directories or none is a usage error.
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
