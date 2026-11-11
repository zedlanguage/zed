//! The parts of a message with a menu of fixes stand in DESIGN.md's order (sec:diagnostics,
//! sec:domains): the first sentence, the definitions of the names a type is written with
//! ("T1 stands for ..."), the numbered steps of the derivation, then the menu. Each example in
//! DESIGN.md with a menu is compiled where zedc can produce it, and its message is compared
//! with DESIGN's: the first sentence word for word, and the order of the parts.
//!
//! The menus of `q = (1 + 2) / (3 + 4)` and `y = inc(x: 2.5)` are compared too, fix by fix,
//! without DESIGN's fixes that declare a type (`q: f64 = ...`, `y: rat = ...`): a top-level
//! binding with a declared type is layer L10 (TypedBinding), so zedc offers no such fix at
//! layer L1 (LIT-menu-match-design, an open case for QUESTIONS.md).
//!
//! No example is compared whole yet. Every one differs from DESIGN in the form of its steps:
//! DESIGN writes `1. the literal (1:21)` with the source line under each step, and zedc writes
//! `[1] 1:21: ...` with each source line shown once for all the steps on it, as DESIGN's own
//! rule for a source line shared by several steps says; the step texts differ too (DESIGN's
//! "the division", "its left operand"). LIT-menu-match-design left this open for
//! QUESTIONS.md. The fixes of `twice` also differ in their wording and in which are offered
//! (DESIGN offers `twice(x: f64)`, `twice(x: rat)` and `twice(x)`). The example at a declared
//! type, `x: f64 = 9007199254740993;`, is not compared at all: zedc does not compile a
//! top-level binding with a declared type yet.

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

/// The fixes of the menu of the message `text`, each `(line, what it then holds)`, without
/// the fixes that declare the type of a top-level binding (`q: f64 = ...`), which zedc does
/// not offer at layer L1.
fn menu(text: &str) -> Vec<(&str, &str)> {
    let Some((_, rest)) = text.split_once("\n  fixes, each checked here:\n") else {
        return Vec::new();
    };
    rest.lines()
        .take_while(|l| l.starts_with("    ") && !l.starts_with("     "))
        .filter_map(|l| {
            let (line, holds) = l.trim_start().split_once("  ")?;
            let lhs = line.split_once(" = ").map_or("", |(lhs, _)| lhs);
            let declares = lhs.contains(": ") && !lhs.contains('(');
            (!declares).then(|| (line, holds.trim_start()))
        })
        .collect()
}

/// The program of each DESIGN.md example with a menu, found by the source line its steps
/// show, whether zedc compiles it yet, and whether its menu is compared ([`menu`]).
const PROGRAMS: [(&str, &str, bool, bool); 4] = [
    (
        "twice(x: int) = x * 2.0;",
        "twice(x: int) = x * 2.0;\n",
        true,
        false,
    ),
    (
        "y = inc(x: 2.5);",
        "inc(x) = x + 1;\ny = inc(x: 2.5);\n",
        true,
        true,
    ),
    (
        "q = (1 + 2) / (3 + 4);",
        "q = (1 + 2) / (3 + 4);\n",
        true,
        true,
    ),
    (
        "x: f64 = 9007199254740993;",
        "x: f64 = 9007199254740993;\n",
        false,
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
            .filter(|(line, ..)| example.contains(&format!("\n       {line}\n")))
            .collect();
        assert_eq!(found.len(), 1, "the program of\n{example}");
        let (_, src, compiled, compare_menu) = found[0];
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
        if *compare_menu {
            assert!(!menu(example).is_empty(), "{example}");
            assert_eq!(menu(&out), menu(example), "{out}\n\n{example}");
        }
    }
}

#[test]
#[ignore = "open: DESIGN's step form (`1. the division (1:13)` with the source line under each \
            step) against its rule that a source line shared by steps is shown once, and the \
            fixes that declare a type (layer L10); LIT-menu-match-design, QUESTIONS.md"]
fn the_message_of_a_division_of_integer_literals_is_designs_whole() {
    // DESIGN.md sec:diagnostics, "A `/` of integer literals": the message, word for word, with
    // zedc's `line:col: ` in place of `error: `.
    let Some(spec) = zed_tests::spec::dir("DESIGN.md's message for q") else {
        return;
    };
    let design = std::fs::read_to_string(spec.join("DESIGN.md")).expect("DESIGN.md");
    let example = (design_examples(&design).into_iter())
        .find(|e| e.contains("\n       q = (1 + 2) / (3 + 4);\n"))
        .expect("the example");
    let out = rejected(&program("q = (1 + 2) / (3 + 4);"));
    let out = format!(
        "error: {}",
        out.split_once(": ").map_or("", |(_, rest)| rest)
    );
    assert_eq!(out, example);
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
    format!("{body}\nmain(m: MainArgs) {{\n  m.stdout <- \"a\";\n}}\n")
}
