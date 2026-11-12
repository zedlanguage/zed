//! The build modes (DESIGN.md Part F, "Build modes"; plan row BUILD-modes): the table names
//! the debug build and the optimized build, each preserving the program's values, and every
//! "X build" of DESIGN.md that names a kind of build is a name the bullet defines. A program
//! gives the same expected outputs in each way this implementation builds it, with and without
//! the unit item `@log(#off);`.
//!
//! The implementation does not yet have the two modes (the log modes come with step L7.3, and
//! what a debug build optimizes is author question A25), so the run test covers the two
//! builds it has: the interpreter, `zedc run`, and the native executable, `zedc build`. There
//! is no log port before step L7.3, so the program writes no log line with or without the
//! item: the test compares the two builds against fixed outputs, and shows that both accept
//! the item and that it changes no output; it cannot yet show that logging off drops a line.

use std::path::Path;

use zed_tests::scaling;

use zed_tests::step_helpers::l01_36a_executables::{Ran, built, dir, executable, interpreter};

/// The words that come before "build" or "builds" in DESIGN.md and name no kind of build: a
/// determiner, a verb or adverb with "build" as a verb, a thing that builds something, a build
/// of one program or command, or a layer that builds something. A new kind of build is either
/// defined in the "Build modes" bullet or, if it is no kind of build, added here.
const NOT_MODES: &[&str] = &[
    // Determiners, numbers and pronouns: "the build", "each build", "the program's build".
    "a",
    "the",
    "each",
    "every",
    "any",
    "per",
    "no",
    "one",
    "two",
    "three",
    "other",
    "first",
    "next",
    "its",
    "whose",
    "that",
    "them",
    "it",
    "you",
    "s",
    "t",
    "5", //
    // "build" as a verb: "to build", "can build", "also build", "does not build".
    "to",
    "can",
    "will",
    "also",
    "never",
    "not",
    "then",
    "and",
    "are",
    "at",
    "yields",
    "above",
    "across",
    "between", //
    // Subjects of the verb "builds": "the step builds", "the stage builds".
    "step",
    "stage",
    "row",
    "library",
    "program",
    "plan",
    "pattern",
    "tier",
    "body",
    "design",
    "elaboration",
    "equality",
    "integers",
    "primes",
    "runtime",
    "source",
    "compiler",
    "checker",
    "itself",
    "number",
    "doubling",
    "sqlite",
    "arduino",
    "access",
    "alternative",
    "2-forms",
    "zed",
    "search", //
    // A build of a program, a command or a toolchain, and not a kind of build: a corpus
    // program's build, the native engine's beside the interpreter, the class of the test builds
    // the bullet lists, a pinned toolchain's, builds that are reproducible, the CLI command.
    "corpus",
    "native",
    "test",
    "toolchain",
    "reproducible",
    "cross",
    "total",
    "zedc", //
    // The executable's "GNU build ID" (step L1.36b), an ELF note, not a kind of build.
    "gnu",
];

/// Whether `word` names a layer of the plan, as in "L4 builds groups".
fn is_layer(word: &str) -> bool {
    word.strip_prefix(['l', 'm'])
        .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
}

/// The "Build modes" bullet of `design`, from its first line to the next bullet.
fn bullet(design: &str) -> &str {
    const HEAD: &str = "\n- **Build modes.**";
    let start = design
        .find(HEAD)
        .expect("DESIGN.md has the bullet \"Build modes\"")
        + 1;
    let end = design[start + HEAD.len()..]
        .find("\n- **")
        .map_or(design.len(), |i| start + HEAD.len() + i);
    &design[start..end]
}

/// Each place in `text` where a word stands before "build" or "builds": its 1-based line and
/// the word, lowercased. One pass over the text.
fn before_build(text: &str) -> Vec<(usize, String)> {
    let bytes = text.as_bytes();
    let word_byte = |b: u8| b.is_ascii_alphanumeric() || b == b'-';
    let mut out = Vec::new();
    let (mut line, mut counted) = (1, 0);
    for (at, _) in text.match_indices("build") {
        let mut after = at + "build".len();
        if bytes.get(after) == Some(&b's') {
            after += 1;
        }
        if bytes.get(after).is_some_and(|&b| word_byte(b)) || at == 0 || bytes[at - 1] != b' ' {
            continue;
        }
        let end = at - 1;
        let start = bytes[..end]
            .iter()
            .rposition(|&b| !word_byte(b))
            .map_or(0, |i| i + 1);
        if start == end {
            continue;
        }
        line += bytes[counted..at].iter().filter(|&&b| b == b'\n').count();
        counted = at;
        out.push((line, text[start..end].to_ascii_lowercase()));
    }
    out
}

/// The kinds of build the bullet defines: the words before each italic "… build*".
fn defined(bullet: &str) -> Vec<String> {
    let mut names: Vec<String> = bullet
        .match_indices(" build*")
        .filter_map(|(at, _)| {
            let start = bullet[..at].rfind(['*', ' '])? + 1;
            Some(bullet[start..at].to_ascii_lowercase())
        })
        .collect();
    names.sort();
    names.dedup();
    names
}

/// The cells of the table row of `bullet` whose first cell is `first`.
fn row<'a>(bullet: &'a str, first: &str) -> Vec<&'a str> {
    let line = bullet
        .lines()
        .find(|l| l.starts_with('|') && l[1..].trim_start().starts_with(first))
        .unwrap_or_else(|| panic!("the table has a row \"{first}\""));
    line.trim_matches('|').split('|').map(str::trim).collect()
}

/// The places in `design` outside the bullet where a word names a kind of build that the
/// bullet does not define, each as `line: "word build"`.
fn undefined(design: &str) -> Vec<String> {
    let b = bullet(design);
    let names = defined(b);
    let start = b.as_ptr() as usize - design.as_ptr() as usize;
    let (first, last) = (
        design[..start].matches('\n').count() + 1,
        design[..start + b.len()].matches('\n').count() + 1,
    );
    before_build(design)
        .into_iter()
        .filter(|(line, word)| {
            !(first..=last).contains(line)
                && !names.contains(word)
                && !NOT_MODES.contains(&word.as_str())
                && !is_layer(word)
        })
        .map(|(line, word)| format!("{line}: \"{word} build\""))
        .collect()
}

#[test]
fn the_table_has_the_two_modes_and_each_keeps_the_values() {
    let Some(spec) = zed_tests::spec::dir("the build modes table") else {
        return;
    };
    let design = std::fs::read_to_string(spec.join("DESIGN.md")).unwrap();
    let b = bullet(&design);
    assert_eq!(row(b, "|"), ["", "Debug build", "Optimized build"]);
    let values = row(b, "Values");
    assert_eq!(values.len(), 3, "{values:?}");
    assert!(values[1].contains("definitional interpreter"), "{values:?}");
    assert_eq!(values[2], "the same");
    for first in ["Log mode", "Log units", "Checks", "Optimization"] {
        assert_eq!(row(b, first).len(), 3, "row {first}");
    }
    assert_eq!(
        defined(b),
        [
            "as-observed",
            "checked",
            "counting",
            "debug",
            "default",
            "full",
            "guard-page",
            "optimized",
            "precise",
            "strict"
        ]
    );
}

#[test]
fn every_kind_of_build_design_names_is_in_the_bullet() {
    let Some(spec) = zed_tests::spec::dir("the kinds of build DESIGN names") else {
        return;
    };
    let design = std::fs::read_to_string(spec.join("DESIGN.md")).unwrap();
    assert_eq!(undefined(&design), Vec::<String>::new());
}

/// A small DESIGN.md: the bullet, then `rest`.
fn fixture(rest: &str) -> String {
    "# Zed\n\n- **Build modes.** A *debug build* or an *optimized build*.\n\n\
     | | Debug build | Optimized build |\n|---|---|---|\n| Values | x | the same |\n\n\
     A *counting build* counts.\n\n- **Next.** Text.\n"
        .to_string()
        + rest
}

#[test]
fn a_kind_of_build_the_bullet_does_not_define_is_named_with_its_line() {
    let ok = fixture("A debug build, the build, the step builds it, a counting build.\n");
    assert_eq!(undefined(&ok), Vec::<String>::new());
    let bad = fixture("Line.\nIn a release build and in fast builds, rebuild.\n");
    assert_eq!(
        undefined(&bad),
        ["13: \"release build\"", "13: \"fast build\""]
    );
}

#[test]
fn build_stage_and_build_dependent_are_not_kinds_of_build() {
    let text = fixture("A demanded build-stage term, a build-dependent string.\n");
    assert_eq!(undefined(&text), Vec::<String>::new());
}

/// The temperature conversion of step L1.21's programs; `@log(#off);` before it when `off`.
fn program(off: bool) -> String {
    let src = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("steps/l01_21_test_runner/zed/fahrenheit.zed"),
    )
    .unwrap();
    if off {
        format!("@log(#off);\n\n{src}")
    } else {
        src
    }
}

#[test]
fn a_run_gives_the_same_outputs_in_each_build_with_and_without_the_log_off_item() {
    let d = dir("build_modes");
    let cases: [(&[u8], &str); 4] = [
        (b"21\n", "69F\n"),
        (b" -40 \n", "-40F\n"),
        (b"twenty\n", "not a whole number: twenty\n"),
        (b"", "not a whole number: \n"),
    ];
    for off in [false, true] {
        let name = if off { "off" } else { "on" };
        let src = d.join(format!("{name}.zed"));
        std::fs::write(&src, program(off)).unwrap();
        let exe = d.join(name);
        built(&src, &exe);
        for (input, expected) in cases {
            let want = Ran {
                status: 0,
                stdout: expected.into(),
                stderr: String::new(),
            };
            assert_eq!(interpreter(&src, &[], input), want, "zedc run, {name}");
            assert_eq!(executable(&exe, &[], input), want, "zedc build, {name}");
        }
    }
}

#[test]
fn finding_the_kinds_of_build_is_linear() {
    let texts: Vec<(usize, String)> = [3000, 24000]
        .into_iter()
        .map(|n| {
            let rest: String = (0..n)
                .map(|i| format!("Line {i}: a debug build, the build, a counting build.\n"))
                .collect();
            (n, fixture(&rest))
        })
        .collect();
    scaling::check_order("finding the kinds of build in n lines", 3000, 1, |n| {
        let (_, text) = texts.iter().find(|(m, _)| *m == n).unwrap();
        assert!(undefined(text).is_empty());
        assert_eq!(before_build(text).len(), 3 * n + 5);
    });
}
