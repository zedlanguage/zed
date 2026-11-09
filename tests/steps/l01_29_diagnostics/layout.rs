//! How a diagnostic is laid out: the message, then each step numbered and padded to one
//! width, its source line with a gutter of one width and the covered text underlined. Each
//! source line is shown once, at its first step; when several spans are on it, each underline
//! is followed by the numbers of its steps.

use zedc::front::{Diagnostic, Step};

fn step(line: usize, col: usize, text: &str, source: &str, width: usize) -> Step {
    Step {
        line,
        col,
        text: text.into(),
        source: source.into(),
        width,
    }
}

#[test]
fn steps_are_numbered_to_one_width_and_places_shown_once_when_repeated() {
    let src9 = "  x = a + b;";
    let src12 = "  y = x ++ \"!\";";
    let mut steps = vec![step(12, 7, "`x` is int here", src12, 1)];
    for i in 0..9 {
        steps.push(step(9, 7, &format!("fact {i}"), src9, 5));
    }
    let d = Diagnostic {
        row: None,
        address: zedc::address::ContentAddress([0; 32]),
        line: 12,
        col: 7,
        message: "`++` does not take (int, \"!\")".into(),
        steps,
    };
    let want = "12:7: `++` does not take (int, \"!\")
  [1]  12:7: `x` is int here
       12 |   y = x ++ \"!\";
          |       ^
  [2]  9:7: fact 0
        9 |   x = a + b;
          |       ^^^^^
  [3]  9:7: fact 1
  [4]  9:7: fact 2
  [5]  9:7: fact 3
  [6]  9:7: fact 4
  [7]  9:7: fact 5
  [8]  9:7: fact 6
  [9]  9:7: fact 7
  [10] 9:7: fact 8";
    assert_eq!(d.to_string(), want);
}

#[test]
fn a_diagnostic_without_steps_is_one_line() {
    let d = Diagnostic {
        row: None,
        address: zedc::address::ContentAddress([0; 32]),
        line: 3,
        col: 1,
        message: "`Point` is not defined".into(),
        steps: Vec::new(),
    };
    assert_eq!(d.to_string(), "3:1: `Point` is not defined");
}

#[test]
fn the_underline_covers_a_multibyte_span_by_characters() {
    let out = super::rejected(
        "main(stdin: Lines) -> (stdout: Lines) {
  größe = 3;
  größe = 4;
  stdout <- \"x\";
}
",
    );
    assert_eq!(
        out,
        "3:3: `größe` is already bound in this scope, and a scope binds each name once
  [1] 2:3: the first binding of `größe`
      2 |   größe = 3;
        |   ^^^^^^^^^^
  [2] 3:3: repair: give this binding a new name
      3 |   größe = 4;
        |   ^^^^^^^^^^
  [3] 3:3: repair: move this binding into a nested block, where it shadows the first"
    );
}

/// A diagnostic of the steps `steps`, at the place of the first.
fn diagnostic(steps: Vec<Step>) -> Diagnostic {
    Diagnostic {
        row: None,
        address: zedc::address::ContentAddress([0; 32]),
        line: steps[0].line,
        col: steps[0].col,
        message: "the message".into(),
        steps,
    }
}

/// The source line `  total = a0 + a1 + … ;` of `n` terms, and a step on each term, then one
/// on the whole sum.
fn terms(n: usize) -> Vec<Step> {
    let names: Vec<String> = (0..n).map(|i| format!("a{i}")).collect();
    let source = format!("  total = {};", names.join(" + "));
    let mut col = 11;
    let mut steps = Vec::new();
    for name in &names {
        let text = format!("`{name}` is int here");
        steps.push(step(1, col, &text, &source, name.len()));
        col += name.len() + 3;
    }
    let sum = source.len() - 11;
    steps.push(step(1, 11, "this `+` gives int", &source, sum));
    steps
}

#[test]
fn a_long_line_is_shown_once_with_each_underline_numbered() {
    let out = diagnostic(terms(8)).to_string();
    assert_eq!(
        out,
        "1:11: the message
  [1] 1:11: `a0` is int here
      1 |   total = a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7;
        |           ^^ [1]    ^^ [3]    ^^ [5]    ^^ [7]
        |           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [9]
        |                ^^ [2]    ^^ [4]    ^^ [6]    ^^ [8]
  [2] 1:16: `a1` is int here
  [3] 1:21: `a2` is int here
  [4] 1:26: `a3` is int here
  [5] 1:31: `a4` is int here
  [6] 1:36: `a5` is int here
  [7] 1:41: `a6` is int here
  [8] 1:46: `a7` is int here
  [9] 1:11: this `+` gives int"
    );
}

#[test]
fn a_short_line_with_one_step_is_shown_as_before() {
    let d = diagnostic(vec![step(2, 5, "`x` is int here", "  y = x;", 1)]);
    assert_eq!(
        d.to_string(),
        "2:5: the message
  [1] 2:5: `x` is int here
      2 |   y = x;
        |     ^"
    );
}

#[test]
fn wide_characters_tabs_and_combining_marks_are_underlined_under_their_columns() {
    // A tab, a name with a combining acute accent (two characters, one column), and a string of
    // two wide characters (two columns each).
    let source = "\tname = \"日本\" ++ ne\u{301}e;";
    let d = diagnostic(vec![
        step(1, 2, "`name` is defined here", source, 4),
        step(1, 9, "this expression is \"日本\"", source, 4),
        step(1, 17, "`née` is int here", source, 4),
        step(1, 19, "the accent", source, 1),
    ]);
    // The tab is shown as four spaces, so that the columns under it are known.
    assert_eq!(
        d.to_string(),
        "1:2: the message
  [1] 1:2: `name` is defined here
      1 |     name = \"日本\" ++ ne\u{301}e;
        |     ^^^^ [1]         ^^^ [3]
        |            ^^^^^^ [2] ^ [4]
  [2] 1:9: this expression is \"日本\"
  [3] 1:17: `née` is int here
  [4] 1:19: the accent"
    );
}

/// Each line is shown once, and a row of underlines is at most as long as the line and its
/// numbers, so `n` steps on one line print O(n) bytes, not a copy of the line for each step.
#[test]
fn rendering_many_steps_on_one_line_scales() {
    use zed_tests::scaling;
    let n = 1000;
    let large = scaling::FACTOR * n;
    let made = scaling::inputs(n, |k| diagnostic(terms(k)));
    let bytes = |k: usize| made[&k].to_string().len();
    let (ratio, limit) = (
        bytes(large) as f64 / bytes(n) as f64,
        scaling::limit(n, large, 1),
    );
    assert!(ratio <= limit, "{ratio} times the bytes, more than {limit}");
    scaling::check("rendering n steps on one line", n, |k| {
        std::hint::black_box(made[&k].to_string());
    });
}

/// A program whose rejection has a step on each of `n` literals of one line.
fn literals(n: usize) -> String {
    let xs: Vec<String> = (0..n).map(|i| i.to_string()).collect();
    format!("x = \"all: \" ++ ({});\n", xs.join(", "))
}

#[test]
fn rejecting_a_line_of_many_literals_scales() {
    use zed_tests::scaling;
    let out = super::rejected(&literals(3));
    assert!(out.contains("  [4] 1:20: this literal, 1, is 1\n"), "{out}");
    assert_eq!(out.matches(" | x = ").count(), 1, "{out}");
    let n = 300;
    let bytes = |k: usize| super::rejected(&literals(k)).len();
    let large = scaling::FACTOR * n;
    let (ratio, limit) = (
        bytes(large) as f64 / bytes(n) as f64,
        scaling::limit(n, large, 1),
    );
    assert!(ratio <= limit, "{ratio} times the bytes, more than {limit}");
    scaling::check("rejecting a line of n literals", n, |k| {
        std::hint::black_box(super::rejected(&literals(k)));
    });
}
