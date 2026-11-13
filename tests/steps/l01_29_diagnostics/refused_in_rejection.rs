//! A rejection whose value a question the checker refused may have widened names that question
//! in its derivation, as the question's warning does in a unit the checker accepts (DESIGN.md
//! L1.39; WARN-refused-in-rejection): the steps of the question's derivation, at the place the
//! program asks it, after the tests that decide the value and before the value's own steps.
//! A refused question on other names, and a rejection with no refused question in its scope,
//! add no step.

use super::refused_warning::{GROWTH, LAST, run, unit};
use zed_tests::scaling;

/// The conditions [`GROWTH`] as the checker prints them.
const CONDITIONS: &str = "12 * w + 10 * y + 12 * z <= 4 * x + 11 && \
                          8 * w + 5 * x + z <= 12 * y + 31 && \
                          4 * w + 10 * x >= 10 * y + 11 * z + 28 && \
                          11 * w + 4 * x + 12 * z >= y + 28";

/// The three steps of the derivation of the refused question [`GROWTH`] asks, each at `at`, a
/// line and column, numbered from `first`, for a unit whose source line `line` (its number
/// `number`) holds the conditions: the first step shows that line, with the marks `marks`
/// under it.
fn growth_steps(at: &str, first: usize, number: usize, line: &str, marks: &[String]) -> String {
    let marks: String = marks.iter().map(|m| format!("        | {m}\n")).collect();
    format!(
        "  [{}] {at}: here the conditions `{CONDITIONS}` hold
      {number} | {line}
{marks}  [{}] {at}: the checker could not work out which values each of their variables can take: \
to find whole numbers that meet these conditions, the checker removes one variable at a time, \
putting in place of the conditions on it conditions on the variables left. Here four variables \
or more are left, and removing any one of them would leave more conditions than there are now, \
so the work could grow without end. The checker stopped there, and the bounds that each \
condition gives each variable from the bounds of the others rule out no value: `w`, `x`, `y` \
and `z` may still be any whole number
  [{}] {at}: so here each of their variables keeps only those bounds, which may be wider than \
the conditions allow; so the checker may reject or warn about code here that is correct, and it \
does not accept code that is wrong
",
        first,
        first + 1,
        first + 2
    )
}

/// One line of marks under a source line: each mark `(column, width, label)` is `width` carets
/// from `column` (counted from 1), followed by a space and its label, the marks in order of
/// column.
fn marks(each: &[(usize, usize, &str)]) -> String {
    let mut out = String::new();
    for &(col, width, label) in each {
        out.push_str(&" ".repeat(col - 1 - out.chars().count()));
        out.push_str(&"^".repeat(width));
        out.push(' ');
        out.push_str(label);
    }
    out
}

/// The column, counted from 1, of the first `piece` in `line`.
fn col(line: &str, piece: &str) -> usize {
    line.find(piece).unwrap() + 1
}

#[test]
fn a_rejection_behind_a_refused_test_names_the_question_in_its_derivation() {
    // The refused question leaves `x` any whole number, so `2 ^ x` is rejected; the rejection
    // names the question at the condition that asks it, before the steps of `x`.
    let line = format!("f(x: int, y: int, z: int, w: int) = if {GROWTH} {{ 2 ^ x }} else {{ 0 }};");
    let src = format!("{line}\nmain() {{\n}}\n");
    let file = unit("rejection", "power.zed", &src);
    let (asked, power) = (col(&line, LAST), col(&line, "2 ^ x"));
    let x = power + 4;
    let steps = growth_steps(
        &format!("1:{asked}"),
        1,
        1,
        &line,
        &[
            marks(&[(3, 6, "[5]"), (asked, LAST.len(), "[1, 2, 3]")]),
            marks(&[(power, 5, "[6, 7]")]),
            marks(&[(x, 1, "[4]")]),
        ],
    );
    let expected = format!(
        "\
{file}:1:{power}: Int power with an exponent that may be negative: `2 : int ^ x : int`. Try \
`if x >= 0 {{ 2 ^ x }} else {{ … }}` instead.
{steps}  [4] 1:{x}: `x` is int here
  [5] 1:3: `x` is declared `int`
  [6] 1:{power}: repair: `if x >= 0 {{ 2 ^ x }} else {{ … }}`
  [7] 1:{power}: repair: `2r ^ x`
"
    );
    assert_eq!(run(&file, &[]), (1, expected));
}

#[test]
fn a_rejection_with_no_refused_question_behind_it_has_no_such_step() {
    // The same rejection with no test around it: no refused question, no extra step.
    let line = "f(x: int) = 2 ^ x;";
    let file = unit(
        "rejection",
        "plain.zed",
        &format!("{line}\nmain() {{\n}}\n"),
    );
    let expected = format!(
        "\
{file}:1:13: Int power with an exponent that may be negative: `2 : int ^ x : int`. Try \
`if x >= 0 {{ 2 ^ x }} else {{ … }}` instead.
  [1] 1:17: `x` is int here
      1 | {line}
        |   ^^^^^^ [2]    ^ [1]
        |             ^^^^^ [3, 4]
  [2] 1:3: `x` is declared `int`
  [3] 1:13: repair: `if x >= 0 {{ 2 ^ x }} else {{ … }}`
  [4] 1:13: repair: `2r ^ x`
"
    );
    assert_eq!(run(&file, &[]), (1, expected));
}

#[test]
fn a_refused_question_on_other_names_adds_no_step() {
    // The refused conditions are on `v`, `y`, `z` and `w`; the rejected `2 ^ x` reads only
    // `x`, so the question is not behind it. A fix that named every refused question of the
    // scope would name this one.
    let on_v = GROWTH.replace('x', "v");
    let line =
        format!("f(x: int, v: int, y: int, z: int, w: int) = if {on_v} {{ 2 ^ x }} else {{ 0 }};");
    let file = unit(
        "rejection",
        "other.zed",
        &format!("{line}\nmain() {{\n}}\n"),
    );
    let (status, err) = run(&file, &[]);
    assert_eq!(status, 1, "{err}");
    let power = col(&line, "2 ^ x");
    assert!(
        err.starts_with(&format!(
            "{file}:1:{power}: Int power with an exponent that may be negative"
        )),
        "{err}"
    );
    assert!(!err.contains("here the conditions"), "{err}");
    assert!(!err.contains("could not work out"), "{err}");
}

/// The first step of the refused question's derivation at `at`, as a rejection prints it.
fn names_conditions_at(err: &str, at: &str) -> bool {
    err.contains(&format!("{at}: here the conditions `{CONDITIONS}` hold\n"))
}

#[test]
fn each_rejection_of_a_value_names_the_refused_question_behind_it() {
    // A bit word's operand, an argument passed into a domain, a value bound in the arm, and
    // the result of `main`: each rejection names the refused question once, at its condition.
    let cases = [
        (
            "bit_word",
            format!(
                "g(x: int, y: int, z: int, w: int) = if {GROWTH} {{ popCount(x) }} else {{ 0 }};\n\
                 main() {{\n}}\n"
            ),
            1,
            "`popCount` takes `x` in int[0..]: `popCount(x : int)`",
        ),
        (
            "argument",
            format!(
                "f(positional n) = popCount(n);\n\
                 g(x: int, y: int, z: int, w: int) = if {GROWTH} {{ f(x) }} else {{ 0 }};\n\
                 main() {{\n}}\n"
            ),
            2,
            "`f` takes `n` in int[0..]",
        ),
        (
            "bound",
            format!(
                "g(x: int, y: int, z: int, w: int) = if {GROWTH} {{ {{ b = x - 1; 2 ^ b }} }} \
                 else {{ 0 }};\nmain() {{\n}}\n"
            ),
            1,
            "Int power with an exponent that may be negative",
        ),
        (
            "status",
            format!(
                "main(m: MainArgs) -> int {{\n  \
                 x = int(m.stdin[0] else \"\") else 0;\n  \
                 y = int(m.stdin[1] else \"\") else 0;\n  \
                 z = int(m.stdin[2] else \"\") else 0;\n  \
                 w = int(m.stdin[3] else \"\") else 0;\n  \
                 if x <= 255 && {GROWTH} {{ x }} else {{ 0 }}\n}}\n"
            ),
            6,
            "`main` gives `x`, which is int[..=255]",
        ),
    ];
    for (name, src, number, headline) in cases {
        let file = unit("rejection", &format!("{name}.zed"), &src);
        let (status, err) = run(&file, &[]);
        assert_eq!(status, 1, "{name}: {err}");
        assert!(err.contains(headline), "{name}: {err}");
        let line = src.lines().nth(number - 1).unwrap();
        let at = format!("{number}:{}", col(line, LAST));
        assert!(names_conditions_at(&err, &at), "{name}: {err}");
        assert_eq!(
            err.matches("here the conditions").count(),
            1,
            "{name}: {err}"
        );
    }
}

#[test]
fn an_inner_name_that_shadows_one_under_a_refused_question_does_not_take_its_question() {
    // The refused question is on the parameter `x`. The block's own `x`, from `v` alone, shadows
    // it: its rejection has no question behind it, though the question's text names an `x`. The
    // parameter `x`, rejected after the block, still has the question behind it (WARN-refused-
    // shadowed: the questions were once matched to a value by the name as written).
    let line = format!(
        "f(x: int, y: int, z: int, w: int, v: int) = if {GROWTH} \
         {{ {{ a = {{ x = v - 1; 2 ^ x }}; a + 2 ^ x }} }} else {{ 0 }};"
    );
    let src = format!("{line}\nmain() {{\n}}\n");
    let file = unit("rejection", "shadowed.zed", &src);
    let (asked, declared) = (col(&line, LAST), col(&line, "v: int"));
    let defined = col(&line, "v - 1");
    let one = defined + 4;
    let inner = col(&line, "2 ^ x }");
    let outer = col(&line, "2 ^ x } }");
    let (inner_x, outer_x) = (inner + 4, outer + 4);
    let rows: String = [
        marks(&[
            (declared, 6, "[5]"),
            (defined, 1, "[4]"),
            (inner, 5, "[7, 8]"),
        ]),
        marks(&[(defined, 5, "[2, 3]")]),
        marks(&[(one, 1, "[6]"), (inner_x, 1, "[1]")]),
    ]
    .iter()
    .map(|m| format!("        | {m}\n"))
    .collect();
    let end = asked + LAST.len() - 1;
    let at = format!("1:{asked} to 1:{end}");
    let expected = format!(
        "\
{file}:1:{inner}: Int power with an exponent that may be negative: `2 : int ^ x : int`. Try \
`if x >= 0 {{ 2 ^ x }} else {{ … }}` instead.
  [1] 1:{inner_x}: `x` is int here
      1 | {line}
{rows}  [2] 1:{defined}: `x` is defined as this expression, int
  [3] 1:{defined}: this `-` gives int
  [4] 1:{defined}: `v` is int here
  [5] 1:{declared}: `v` is declared `int`
  [6] 1:{one}: this literal, 1, is 1
  [7] 1:{inner}: repair: `if x >= 0 {{ 2 ^ x }} else {{ … }}`
  [8] 1:{inner}: repair: `2r ^ x`
{file}:1:{outer}: Int power with an exponent that may be negative: `2 : int ^ x : int`. Try \
`if x >= 0 {{ 2 ^ x }} else {{ … }}` instead.
  [1] {at}: here the conditions `{CONDITIONS}` hold
      line 1 is shown above
  [2] {at}: the checker could not work out which values each of their variables can take: to \
find whole numbers that meet these conditions, the checker removes one variable at a time, \
putting in place of the conditions on it conditions on the variables left. Here four variables \
or more are left, and removing any one of them would leave more conditions than there are now, \
so the work could grow without end. The checker stopped there, and the bounds that each \
condition gives each variable from the bounds of the others rule out no value: `w`, `x`, `y` \
and `z` may still be any whole number
  [3] {at}: so here each of their variables keeps only those bounds, which may be wider than \
the conditions allow; so the checker may reject or warn about code here that is correct, and it \
does not accept code that is wrong
  [4] 1:{outer_x} to 1:{outer_x}: `x` is int here
  [5] 1:3 to 1:8: `x` is declared `int`
  [6] 1:{outer} to 1:{outer_end}: repair: `if x >= 0 {{ 2 ^ x }} else {{ … }}`
",
        outer_end = outer + 4,
    );
    assert_eq!(run(&file, &[]), (1, expected));
}

#[test]
fn an_inner_name_read_from_a_name_under_a_refused_question_takes_the_question() {
    // The block's own `x` is computed from `y`, on which the question is asked: the question is
    // behind the inner rejection through `y`, as for any value read from it, and behind the
    // parameter's rejection through the parameter `x`; each names it once.
    let src = format!(
        "f(x: int, y: int, z: int, w: int) = if {GROWTH} \
         {{ {{ a = {{ x = y - 1; 2 ^ x }}; a + 2 ^ x }} }} else {{ 0 }};\nmain() {{\n}}\n"
    );
    let file = unit("rejection", "shadowed_through.zed", &src);
    let (status, err) = run(&file, &[]);
    assert_eq!(status, 1, "{err}");
    assert_eq!(
        err.matches("Int power with an exponent").count(),
        2,
        "{err}"
    );
    assert_eq!(err.matches("here the conditions").count(), 2, "{err}");
}

/// A function of `n` groups of four parameters, each group `xi`, `yi`, `zi`, `wi` under its own
/// copy of [`GROWTH`], all in one test, whose arm adds `2 ^ xi` for each group: `n` refused
/// questions in one scope and `n` rejections, each with one question behind it.
fn many_groups(n: usize) -> String {
    let group = |i: usize| {
        GROWTH
            .replace('x', &format!("x{i}"))
            .replace('y', &format!("y{i}"))
            .replace('z', &format!("z{i}"))
            .replace('w', &format!("w{i}"))
    };
    let params: Vec<String> = (0..n)
        .map(|i| format!("x{i}: int, y{i}: int, z{i}: int, w{i}: int"))
        .collect();
    let tests: Vec<String> = (0..n).map(group).collect();
    let powers: Vec<String> = (0..n).map(|i| format!("2 ^ x{i}")).collect();
    format!(
        "g({}) = if {} {{ {} }} else {{ 0 }};\nmain() {{\n}}\n",
        params.join(", "),
        tests.join(" && "),
        powers.join(" + ")
    )
}

/// `zedc run` on `n` rejections under `n` refused questions in one scope, each rejection
/// naming the one question on its names: finding them is within n log n, where reading every
/// question of the scope for each rejection would be n².
#[test]
fn many_rejections_under_many_refused_tests_scale() {
    let n = 20;
    let files = scaling::inputs(n, |m| {
        unit("rejection", &format!("groups{m}.zed"), &many_groups(m))
    });
    scaling::check(
        "zedc run on n rejections under n refused questions",
        n,
        |m| {
            let (status, err) = run(&files[&m], &[]);
            assert_eq!(status, 1);
            assert_eq!(err.matches("Int power with an exponent").count(), m);
            assert_eq!(err.matches("here the conditions").count(), m);
        },
    );
}
