//! The `sync` command, which runs the checks of the spec's prose and writes nothing (author P371,
//! P375: this repository holds no copy of the spec); and the readers the tests use on DESIGN.md
//! in place. This file spells the kernel rule names to test the list of them, so l01_21's
//! `no_message_names_a_kernel_rule` leaves it out, as it leaves out its own file.

use std::fs;

use zed_tools::spec::Spec;
use zed_tools::{fence_layers, spec_checks, sync};

use super::{DOUBLE, design, fence, spec_dir, tool};
use zed_tests::step_helpers::m0_03_grammar_tools::KERNEL;

/// Two tables of step M0.7's serialization, the first ended by a paragraph, the second by a
/// blank line, and between them a table whose header does not end as theirs do.
const SERIAL: &str = "| Grade | Tag | Fields in order |\n|---|---|---|\n| Axiom | 0 | — |\n\
                      | Proved | 2 | — |\nA note.\n\n| Kind | Code | Fields in order |\n|---|---|---|\n\
                      | Other | 9 | — |\n\n| Value | Tag | Fields in order |\n|---|---|---|\n\
                      | Boolean | 0 | `value: byte` |\n\n| Primitive | Code |\n|---|---|\n\
                      | `a + b` | 0 |\n\n| Primitive | Code | Note |\n|---|---|---|\n\
                      | `a - b` | 1 | — |\n";

/// The prelude laws as a spec states them, and the study page that states `allIntro` the same.
const LAWS: &str = "L15.7. Build the prelude laws `anyIntro`, `anyElim`, `allElim` and `allIntro`; \
                    test: `anyIntro`, `anyElim`, `allElim` and `allIntro` reach proof grade.\n\
                    The prelude also states `anyIntro`, `anyElim`, `allElim` and \
                    `law allIntro(p: P) -> Q`. More.\n";
const PAGE: &str = "law allIntro(p: P) -> Q proof { done }\n";

/// `sync` on a spec runs each check of its prose and writes nothing; each check that fails is
/// named with its failure, and the command fails. (The build-modes check passes only on a
/// whole bullet; `the_prose_checks_pass_on_the_spec` runs all three on the spec.)
#[test]
fn sync_runs_each_prose_check_and_names_the_one_that_fails() {
    let with =
        |body: &str| sync::prose_checks(&design(&format!("{}\n{body}", fence(DOUBLE))), PAGE);
    let checks = with(&format!("{KERNEL}\n{LAWS}"));
    assert_eq!(
        checks.iter().map(|c| c.0).collect::<Vec<_>>(),
        ["the kernel grammar", "the prelude laws", "the build modes"]
    );
    assert_eq!(checks[0].1, Ok(()), "{checks:?}");
    assert_eq!(checks[1].1, Ok(()), "{checks:?}");
    assert!(checks[2].1.is_err(), "{checks:?}");

    let no_kernel = format!("{}\n{LAWS}", fence(DOUBLE));
    let checks = with(LAWS);
    assert!(
        checks[0]
            .1
            .as_ref()
            .is_err_and(|e| e.contains("sec:kernel")),
        "{checks:?}"
    );
    assert_eq!(checks[1].1, Ok(()), "{checks:?}");

    // The command reads DESIGN.md from the directory, and writes nothing into it.
    let dir = spec_dir("sync_no_kernel", &design(&no_kernel), "");
    let (outcome, out) = tool(sync::run, &[&dir.root(), "--check"]);
    assert_eq!(outcome, Ok(false), "{out}");
    assert!(out.contains("the kernel grammar: "), "{out}");
    assert!(
        out.contains("the citations: DESIGN.md has no section sec:steps"),
        "{out}"
    );
    let mut files: Vec<String> = fs::read_dir(dir.root())
        .unwrap()
        .map(|e| e.unwrap().file_name().into_string().unwrap())
        .collect();
    files.sort();
    assert_eq!(files, ["DESIGN.md", "EXAMPLES.md"]);
}

/// The checks of the spec's prose pass on the spec's own DESIGN.md, read in place, with this
/// repository's study page: `sync` runs them only by hand, so a spec edit that breaks one is
/// caught here (DESIGN.md's "which builds the string" was once read as naming a build).
#[cfg(feature = "spec")]
#[test]
fn the_prose_checks_pass_on_the_spec() {
    let page = zed_tests::spec::read(&format!("{}/docs/mathlib-study.md", zed_tools::impl_root()));
    for (what, result) in sync::prose_checks(zed_tests::spec::design(), &page) {
        assert_eq!(result, Ok(()), "{what}");
    }
}

/// Every label and step this repository cites is defined in the spec, as `sync` checks it
/// (a comment of l07_03 that cited a section label DESIGN.md does not define passed every test
/// and was named only by merge-push's step 0).
#[cfg(feature = "spec")]
#[test]
fn the_citations_of_this_repository_pass_on_the_spec() {
    let dir = zed_tests::spec::dir().to_string_lossy().into_owned();
    let mut out = String::new();
    assert_eq!(zed_tools::cite::run(&[dir], &mut out), Ok(true), "{out}");
}

/// The readers the tests use on DESIGN.md in place: a ```` ```text ```` fence inside a list
/// item is given with its indentation taken off, the kernel grammar's rule names are listed,
/// and the tables of M0.7's serialization are kept apart from tables of other shapes.
#[test]
fn the_in_place_readers_give_the_messages_rules_and_tables() {
    let body = format!(
        "{}\n- A report:\n\n  ```text\n  trivial models of T\n    one line\n  ```\n\n{SERIAL}\n{KERNEL}",
        fence(DOUBLE)
    );
    let text = design(&body);
    let dir = spec_dir("in_place", &text, "");
    let messages = zed_tools::spec::text_fences(&[dir.at("DESIGN.md")]).expect("the fences read");
    assert!(
        messages.contains("\n```text\ntrivial models of T\n  one line\n```"),
        "{messages}"
    );
    assert_eq!(
        spec_checks::kernel_rules(&text).unwrap(),
        [
            "Boom",
            "T-Discard",
            "T-Fam",
            "T-Fix",
            "T-Fold",
            "T-Gen",
            "T-Port",
            "T-Reindex"
        ]
    );
    assert_eq!(
        spec_checks::serial_tables(&text),
        "| Grade | Tag | Fields in order |\n| Axiom | 0 | — |\n\
         | Proved | 2 | — |\n| Value | Tag | Fields in order |\n| Boolean | 0 | `value: byte` |\n\
         | Primitive | Code |\n| `a + b` | 0 |\n",
        "the tables of M0.7's serialization and its codes of primitives, without the line \
         under each header, the table of the same shape whose header names no tag, or a table \
         whose header only starts as the codes' does"
    );
}

/// DESIGN.md's table of words, read in place, gives each fence its layer from a cell's
/// backquoted words only: prose, a gloss in parentheses and a word in another column are
/// passed over, a word a cell names again in its note (as DESIGN.md's L3 row names `split` and
/// `concat` again) counts once, and a word only the note names (as L15's tactics are) counts.
#[test]
fn the_table_of_words_lays_out_the_fences_from_its_backquoted_words() {
    let table = "| Layer | Annotations | Facet words | Words |\n|---|---|---|---|\n\
                 | L1 | — | — | `len`, and prose |\n\
                 | L3 | `@pure` (see below) | `::size` here | `sorted`, `split`, `concat` (`split` \
                 keeps every piece; `concat` takes strings, `max` too) |\n\
                 | L7 | | | the port `log` |\n";
    let body = format!(
        "{}\n{}\n{}\n{}\n{KERNEL}",
        fence(DOUBLE),
        fence("y = sorted(x);"),
        fence("z = max(x, y);"),
        fence("w = split(x);")
    );
    let text = design(&body).replacen(
        "| Layer | Annotations | Facet words | Words |\n|---|---|---|---|\n\
         | L1 | | | `len` |\n| L3 | | | `sorted` |\n| L7 | | | `log` |\n",
        table,
        1,
    );
    assert!(text.contains("takes strings"), "the table is replaced");
    let dir = spec_dir("table_words", &text, "");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let layers: Vec<u32> = fence_layers::of_document(&dir.at("DESIGN.md"), &spec)
        .expect("the fences lay out")
        .iter()
        .map(|f| f.layer)
        .collect();
    assert_eq!(layers, [1, 3, 3, 3]);
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
    assert_eq!(spec_checks::prelude_laws(LAWS, PAGE), Ok(()));
    let short = LAWS.replacen(" and `allIntro`;", ";", 1);
    assert!(spec_checks::prelude_laws(&short, PAGE).is_err());
    let other = "law allIntro(p: P) -> R proof { done }\n";
    let why = spec_checks::prelude_laws(LAWS, other).expect_err("stated otherwise");
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
