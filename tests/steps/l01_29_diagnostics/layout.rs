//! How a diagnostic is laid out: the message, then each step numbered and padded to one
//! width, its source line with a gutter of one width and the covered text underlined. Each
//! source line is shown once, at its first step; when several spans are on it, each underline
//! is followed by the numbers of its steps. Texts nested in a chain are drawn by their ends on
//! one rule, and a text that cannot be drawn clearly is given by its range in its step.

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
        menu: String::new(),
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
        menu: String::new(),
    };
    assert_eq!(d.to_string(), "3:1: `Point` is not defined");
}

#[test]
fn the_underline_covers_a_multibyte_span_by_characters() {
    // A name is ASCII (NAME-ascii-only), so the characters beyond ASCII are in a string.
    let out = super::rejected(
        "main(m: MainArgs) {
  x = \"größe\";
  x = \"Maß\";
  m.stdout <- \"x\";
}
",
    );
    assert_eq!(
        out,
        "3:3: `x` is already bound in this scope.
  [1] 2:3: the first binding of `x`
      2 |   x = \"größe\";
        |   ^^^^^^^^^^^^
  [2] 3:3: repair: give this binding a new name
      3 |   x = \"Maß\";
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
        menu: String::new(),
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
    scaling::hold(
        "rendering n steps on one line",
        "bytes",
        bytes(n) as u64,
        bytes(large) as u64,
        1,
    );
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
    scaling::hold(
        "rejecting a line of n literals",
        "bytes",
        bytes(n) as u64,
        bytes(large) as u64,
        1,
    );
    scaling::check("rejecting a line of n literals", n, |k| {
        std::hint::black_box(super::rejected(&literals(k)));
    });
}

/// The source line `  total = a0 + a1 + … ;` of `n` terms, a step on each term, then one on
/// each sum `a0 + … + ai` from i = 1, so that the sums nest n - 1 deep.
fn sums(n: usize) -> Vec<Step> {
    let mut steps = terms(n);
    steps.pop();
    let source = steps[0].source.clone();
    let mut width = 2;
    for i in 1..n {
        width += 3 + format!("a{i}").len();
        let text = format!("this `+` gives int, the sum to a{i}");
        steps.push(step(1, 11, &text, &source, width));
    }
    steps
}

/// The source line `  y = f(f(…f(x)…));` of `n` calls, a step on each call from the outermost,
/// then one on `x`.
fn calls(n: usize) -> Vec<Step> {
    let source = format!("  y = {}x{};", "f(".repeat(n), ")".repeat(n));
    let mut steps: Vec<Step> = (0..n)
        .map(|i| {
            let text = format!("this call of `f`, {} deep, gives int", i + 1);
            step(1, 7 + 2 * i, &text, &source, 3 * (n - i) + 1)
        })
        .collect();
    steps.push(step(1, 7 + 2 * n, "`x` is int here", &source, 1));
    steps
}

#[test]
fn sums_nested_on_one_line_are_drawn_by_their_ends_on_one_rule() {
    // The example in DESIGN sec:diagnostics.
    let five = diagnostic(sums(5)).to_string();
    assert!(
        five.contains(
            "\n        |           ^----------^----^ [8]\n        |                      [7]\n"
        ),
        "{five}"
    );
    // Every sum starts at `a0`, so the rule's first caret has no number, and each sum's number
    // stands under the caret where it ends; the outermost and the innermost are underlined.
    assert_eq!(
        diagnostic(sums(8)).to_string(),
        "1:11: the message
  [1]  1:11: `a0` is int here
       1 |   total = a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7;
         |           ^^ [1]    ^^ [3]         ^^ [6]
         |           ^^^^^^^ [9]    ^^ [4]         ^^ [7]
         |           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ [15]
         |                ^^ [2]         ^^ [5]         ^^ [8]
         |           ^----------^----^----^----^----^ [14]
         |                      [10] [11] [12] [13]
  [2]  1:16: `a1` is int here
  [3]  1:21: `a2` is int here
  [4]  1:26: `a3` is int here
  [5]  1:31: `a4` is int here
  [6]  1:36: `a5` is int here
  [7]  1:41: `a6` is int here
  [8]  1:46: `a7` is int here
  [9]  1:11: this `+` gives int, the sum to a1
  [10] 1:11: this `+` gives int, the sum to a2
  [11] 1:11: this `+` gives int, the sum to a3
  [12] 1:11: this `+` gives int, the sum to a4
  [13] 1:11: this `+` gives int, the sum to a5
  [14] 1:11: this `+` gives int, the sum to a6
  [15] 1:11: this `+` gives int, the sum to a7"
    );
}

/// The calls share neither their first nor their last column, so a rule would leave the reader
/// to pair each first caret with its last; the calls between the outermost and the innermost
/// are given by their ranges instead.
#[test]
fn calls_nested_on_one_line_between_the_outermost_and_innermost_are_given_by_their_ranges() {
    assert_eq!(
        diagnostic(calls(5)).to_string(),
        "1:7: the message
  [1] 1:7: this call of `f`, 1 deep, gives int
      1 |   y = f(f(f(f(f(x)))));
        |       ^^^^^^^^^^^^^^^^ [1]
        |               ^^^^ [5]
        |                 ^ [6]
  [2] 1:9 to 1:21: this call of `f`, 2 deep, gives int
  [3] 1:11 to 1:20: this call of `f`, 3 deep, gives int
  [4] 1:13 to 1:19: this call of `f`, 4 deep, gives int
  [5] 1:15: this call of `f`, 5 deep, gives int
  [6] 1:17: `x` is int here"
    );
}

#[test]
fn a_step_whose_text_overlaps_another_without_nesting_is_given_by_its_range() {
    let source = "  y = a + b + c;";
    let d = diagnostic(vec![
        step(1, 7, "`a + b` is int", source, 5),
        step(1, 11, "`b + c` is int", source, 5),
        step(1, 11, "`b` is int here", source, 1),
    ]);
    assert_eq!(
        d.to_string(),
        "1:7: the message
  [1] 1:7: `a + b` is int
      1 |   y = a + b + c;
        |       ^^^^^ [1]
        |           ^ [3]
  [2] 1:11 to 1:15: `b + c` is int
  [3] 1:11: `b` is int here"
    );
}

#[test]
fn a_balanced_nesting_is_underlined_in_full() {
    let source = "  y = (a + b) * (c + d);";
    let d = diagnostic(vec![
        step(1, 7, "this `*` gives int", source, 17),
        step(1, 7, "this `+` gives int", source, 7),
        step(1, 8, "`a` is int here", source, 1),
        step(1, 12, "`b` is int here", source, 1),
        step(1, 17, "this `+` gives int", source, 7),
        step(1, 18, "`c` is int here", source, 1),
        step(1, 22, "`d` is int here", source, 1),
    ]);
    // Neither half holds more than half of the stretches, so nothing is drawn by its ends.
    assert_eq!(
        d.to_string(),
        "1:7: the message
  [1] 1:7: this `*` gives int
      1 |   y = (a + b) * (c + d);
        |       ^^^^^^^ [2]    ^ [7]
        |       ^^^^^^^^^^^^^^^^^ [1]
        |        ^ [3]    ^^^^^^^ [5]
        |            ^ [4] ^ [6]
  [2] 1:7: this `+` gives int
  [3] 1:8: `a` is int here
  [4] 1:12: `b` is int here
  [5] 1:17: this `+` gives int
  [6] 1:18: `c` is int here
  [7] 1:22: `d` is int here"
    );
}

/// A sum `a0 + … + an` whose every partial sum is a step nests n deep on one line; drawn by
/// their ends, the sums take a few rows, not n, so the line's quote costs O(n) bytes, not
/// O(n²).
#[test]
fn rendering_a_line_of_nested_sums_scales() {
    use zed_tests::scaling;
    let n = 1000;
    let large = scaling::FACTOR * n;
    let made = scaling::inputs(n, |k| diagnostic(sums(k)));
    let bytes = |k: usize| made[&k].to_string().len();
    scaling::hold(
        "rendering n nested sums on one line",
        "bytes",
        bytes(n) as u64,
        bytes(large) as u64,
        1,
    );
    scaling::check("rendering n nested sums on one line", n, |k| {
        std::hint::black_box(made[&k].to_string());
    });
}

/// The source line `  y = a0^a1^…;` of `n` terms, a step on each power `ai^…` from the
/// outermost, then one on each term: `^` groups from the right, so the powers share their end.
fn powers(n: usize) -> Vec<Step> {
    let names: Vec<String> = (0..n).map(|i| format!("a{i}")).collect();
    let source = format!("  y = {};", names.join("^"));
    let mut starts = Vec::new();
    let mut col = 7;
    for name in &names {
        starts.push(col);
        col += name.len() + 1;
    }
    let end = col - 1;
    let mut steps: Vec<Step> = (0..n - 1)
        .map(|i| {
            let text = format!("this `^` gives int, from a{i}");
            step(1, starts[i], &text, &source, end - starts[i])
        })
        .collect();
    for (name, &col) in names.iter().zip(&starts) {
        steps.push(step(
            1,
            col,
            &format!("`{name}` is int here"),
            &source,
            name.len(),
        ));
    }
    steps
}

#[test]
fn powers_nested_on_one_line_are_drawn_by_their_ends_on_one_rule() {
    // Every power ends at `a5`, so the rule's last caret has no number, and each power's number
    // stands under the caret where it starts.
    assert_eq!(
        diagnostic(powers(6)).to_string(),
        "1:7: the message
  [1]  1:7: this `^` gives int, from a0
       1 |   y = a0^a1^a2^a3^a4^a5;
         |       ^^ [6]   ^^ [9]
         |       ^^^^^^^^^^^^^^^^^ [1]
         |          ^^ [7]   ^^ [10]
         |             ^^ [8]   ^^ [11]
         |                   ^^^^^ [5]
         |          ^--^--^------^
         |          [2]   [4]
         |             [3]
  [2]  1:10: this `^` gives int, from a1
  [3]  1:13: this `^` gives int, from a2
  [4]  1:16: this `^` gives int, from a3
  [5]  1:19: this `^` gives int, from a4
  [6]  1:7: `a0` is int here
  [7]  1:10: `a1` is int here
  [8]  1:13: `a2` is int here
  [9]  1:16: `a3` is int here
  [10] 1:19: `a4` is int here
  [11] 1:22: `a5` is int here"
    );
}

/// A program whose rejection quotes the line `  total = n + n + … ;` of `n` terms, each of
/// whose partial sums is a step.
fn summed(n: usize) -> String {
    format!(
        "main(m: MainArgs) {{\n  n = int(m.stdin[0]) else 0;\n  total = {};\n  \
         m.stdout <- \"total: \" ++ total;\n}}\n",
        vec!["n"; n].join(" + ")
    )
}

#[test]
fn rejecting_a_line_of_nested_sums_scales() {
    use zed_tests::scaling;
    let out = super::rejected(&summed(4));
    assert!(out.contains("|           ^-------^ [5]\n"), "{out}");
    let n = 200;
    let bytes = |k: usize| super::rejected(&summed(k)).len();
    let large = scaling::FACTOR * n;
    scaling::hold(
        "rejecting a line of n nested sums",
        "bytes",
        bytes(n) as u64,
        bytes(large) as u64,
        1,
    );
    scaling::check("rejecting a line of n nested sums", n, |k| {
        std::hint::black_box(super::rejected(&summed(k)));
    });
}
