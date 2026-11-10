//! The parts of a message with a menu of fixes stand in DESIGN.md's order (sec:diagnostics,
//! sec:domains): the first sentence, the definitions of the names a type is written with
//! ("T1 stands for ..."), the numbered steps of the derivation, then the menu. Each example in
//! DESIGN.md with a menu is compiled where zedc can produce it, and its message is compared
//! with DESIGN's: the first sentence word for word, and the order of the parts.
//!
//! No example is compared whole yet. Every one differs from DESIGN in the form of its steps:
//! DESIGN writes `1. the literal (1:21)` with the source line under each step, and zedc writes
//! `[1] 1:21: ...` with each source line shown once for all the steps on it. The menus differ
//! too, in the ways recorded under LIT-menu-match-design: zedc offers no fix that declares a
//! type (`q: f64 = ...`, `y: rat = ...`), and for `q = (1 + 2) / (3 + 4)` it gives a suffix
//! to both sides of the `/` where DESIGN gives it to the first literal alone. The fixes of
//! `twice` also differ in their wording and in which are offered (DESIGN offers
//! `twice(x: f64)`, `twice(x: rat)` and `twice(x)`). The example at a declared type,
//! `x: f64 = 9007199254740993;`, is not compared at all: zedc does not compile a top-level
//! binding with a declared type yet.

use super::rejected;

/// A part of a message.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Part {
    /// The first sentence, on the first line.
    First,
    /// The definitions of the names a printed type is written with: `  T1 stands for ...`.
    Definitions,
    /// A numbered step of the derivation: `  1. ...` in DESIGN.md, `  [1] ...` in zedc.
    Step,
    /// The menu of fixes: `  fixes, each checked here:` and the fixes under it.
    Menu,
}

/// The parts of the message `text` in the order they stand, each once where its lines follow
/// one another. A line that starts none of them belongs to the part above it.
fn parts(text: &str) -> Vec<Part> {
    let mut out = vec![Part::First];
    for line in text.lines().skip(1) {
        let part = if line.starts_with("  fixes, each checked here:") {
            Part::Menu
        } else if line.starts_with("  T") && line.contains(" stand") && line.ends_with(':') {
            Part::Definitions
        } else if is_step(line) {
            Part::Step
        } else {
            continue;
        };
        if out.last() != Some(&part) {
            out.push(part);
        }
    }
    out
}

/// Whether `line` starts a step: two spaces, then `[n] ` (zedc) or `n. ` (DESIGN.md).
fn is_step(line: &str) -> bool {
    let Some(rest) = line.strip_prefix("  ") else {
        return false;
    };
    let rest = rest.strip_prefix('[').unwrap_or(rest);
    let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
    digits > 0 && (rest[digits..].starts_with("] ") || rest[digits..].starts_with(". "))
}

/// The first sentence of the message `text`, without DESIGN's `error: ` or zedc's `line:col: `.
fn first(text: &str) -> &str {
    let line = text.lines().next().unwrap_or("");
    if let Some(rest) = line.strip_prefix("error: ") {
        return rest;
    }
    let mut it = line.splitn(3, ':');
    match (it.next(), it.next(), it.next()) {
        (Some(l), Some(c), Some(rest))
            if l.bytes().all(|b| b.is_ascii_digit()) && c.bytes().all(|b| b.is_ascii_digit()) =>
        {
            rest.strip_prefix(' ').unwrap_or(rest)
        }
        _ => line,
    }
}

/// The messages DESIGN.md writes with a menu of fixes: each `text` fence holding the menu's
/// heading.
fn design_examples(design: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut fence: Option<String> = None;
    for line in design.lines() {
        match fence.as_mut() {
            None if line == "```text" => fence = Some(String::new()),
            None => {}
            Some(f) if line == "```" => {
                if f.contains("\n  fixes, each checked here:") {
                    out.push(std::mem::take(f));
                }
                fence = None;
            }
            Some(f) => {
                f.push_str(line);
                f.push('\n');
            }
        }
    }
    out
}

/// The program of each DESIGN.md example with a menu, found by the source line its steps
/// show, and whether zedc compiles it yet.
const PROGRAMS: [(&str, &str, bool); 4] = [
    (
        "twice(x: int) = x * 2.0;",
        "twice(x: int) = x * 2.0;\n",
        true,
    ),
    (
        "y = inc(x: 2.5);",
        "inc(x) = x + 1;\ny = inc(x: 2.5);\n",
        true,
    ),
    ("q = (1 + 2) / (3 + 4);", "q = (1 + 2) / (3 + 4);\n", true),
    (
        "x: f64 = 9007199254740993;",
        "x: f64 = 9007199254740993;\n",
        false,
    ),
];

#[test]
fn each_design_example_with_a_menu_stands_in_designs_order_and_zedc_writes_it_so() {
    let Some(spec) = zed_tests::spec::dir("the order of the parts of DESIGN.md's menus") else {
        return;
    };
    let design = std::fs::read_to_string(spec.join("DESIGN.md")).expect("DESIGN.md");
    let examples = design_examples(&design);
    assert_eq!(examples.len(), PROGRAMS.len(), "{examples:#?}");
    for example in &examples {
        // DESIGN's own order, the same in every example: the definitions, where there are
        // any, before the steps, and the menu last.
        let order = parts(example);
        assert!(
            order == [Part::First, Part::Step, Part::Menu]
                || order == [Part::First, Part::Definitions, Part::Step, Part::Menu],
            "{order:?}\n{example}"
        );
        let found: Vec<_> = PROGRAMS
            .iter()
            .filter(|(line, _, _)| example.contains(&format!("\n       {line}\n")))
            .collect();
        assert_eq!(found.len(), 1, "the program of\n{example}");
        let (_, src, compiled) = found[0];
        let out = rejected(&program(src));
        if !compiled {
            // Held back: zedc does not compile the example yet. Once it does, this fails, and
            // the example is to be compared like the others.
            assert!(out.contains("does not compile it yet"), "{out}");
            continue;
        }
        assert_eq!(
            out.lines()
                .filter(|l| l.starts_with("  fixes, each checked here:"))
                .count(),
            1,
            "{out}"
        );
        assert_eq!(first(&out), first(example), "{out}\n\n{example}");
        assert_eq!(parts(&out), order, "{out}\n\n{example}");
    }
}

#[test]
fn a_message_with_definitions_steps_and_a_menu_writes_them_in_that_order() {
    // The definitions of `T1` come before the steps, and the menu after them.
    let out = rejected(&program("f(positional x: f64 | rat) = x;\ny = f(1);"));
    assert_eq!(
        parts(&out),
        [Part::First, Part::Definitions, Part::Step, Part::Menu],
        "{out}"
    );
}

#[test]
fn the_parts_of_a_message_are_read_as_written() {
    // DESIGN's step form and zedc's, and a message with no menu.
    let design = "error: a\n  T1 stands for b:\n    type T1 = int;\n  1. c (1:1)\n       x\n  \
                  fixes, each checked here:\n    y    z\n";
    assert_eq!(
        parts(design),
        [Part::First, Part::Definitions, Part::Step, Part::Menu]
    );
    let zedc = "1:2: a\n  [1] 1:2: c\n      1 | x\n  [2] 1:3: d\n  fixes, each checked here:\n";
    assert_eq!(parts(zedc), [Part::First, Part::Step, Part::Menu]);
    assert_eq!(
        parts("1:2: a\n  fixes, each checked here:\n  [1] 1:2: c\n"),
        [Part::First, Part::Menu, Part::Step]
    );
    assert_eq!(first(design), "a");
    assert_eq!(first(zedc), "a");
    assert!(!is_step("  12 apples"));
    assert!(is_step("  12. apples"));
}

/// The program `body` with a `main`, so that it loads as a program.
fn program(body: &str) -> String {
    format!("{body}\nmain(stdin: Lines) -> (stdout: Lines) {{\n  stdout <- \"a\";\n}}\n")
}
