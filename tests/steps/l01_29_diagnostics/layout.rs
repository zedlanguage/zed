//! How a diagnostic is laid out: the message, then each step numbered and padded to one
//! width, its source line with a gutter of one width and the covered text underlined, the
//! source shown once for consecutive steps on one place.

use zedc::run::{Diagnostic, Step};

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
        "3:3: `größe` is already bound in this scope
  [1] 2:3: the first binding of `größe`
      2 |   größe = 3;
        |   ^^^^^^^^^^"
    );
}
