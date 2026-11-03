//! The solver in the checker, end to end through `zedc run`: a linear question the solver
//! decides rejects nothing, and one it refuses is a rejection with its cause, its span and
//! the constraints.

use crate::l01_19_whole_file_ports::run;

/// A program whose `main` calls `ok`, defined by `def`, at `args`, and prints whether it held.
fn program(def: &str, args: &str) -> String {
    format!(
        "{def}\nmain(stdin: Lines) -> (stdout: Lines) {{\n  a = int(stdin[0] else \"0\") else 0;\n  \
         r = if ok({args}) {{ \"in\" }} else {{ \"out\" }};\n  stdout <- \"${{r}}\";\n}}\n"
    )
}

/// The standard error of a rejected run, with the program's path removed from its first line,
/// and without the source lines the steps underline.
fn rejection(name: &str, src: &str) -> String {
    let o = run(name, src, "3\n", &[]);
    assert_eq!((o.status, o.stdout.as_str()), (1, ""), "{}", o.stderr);
    let (_, rest) = o.stderr.split_once("prog.zed:").expect("a placed message");
    let mut lines = rest.lines();
    let first = lines.next().expect("a message");
    std::iter::once(first)
        .chain(lines.filter(|l| l.trim_start().starts_with('[')))
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn pughs_example_is_decided_and_its_arm_is_unreachable() {
    // 27 <= 11x + 13y <= 45, -10 <= 7x - 9y <= 4 has rational points and no integer point:
    // the test never holds, which is an unreachable arm, not a rejection.
    let src = program(
        "ok(x, y) = 27 <= 11 * x + 13 * y && 11 * x + 13 * y <= 45 && -10 <= 7 * x - 9 * y && \
         7 * x - 9 * y <= 4;",
        "x: a, y: a + 1",
    );
    for input in ["0\n", "1\n", "3\n", "-2\n"] {
        let o = run("pugh", &src, input, &[]);
        assert_eq!(
            (o.status, o.stdout.as_str(), o.stderr.as_str()),
            (0, "out\n", ""),
            "{input}"
        );
    }
}

#[test]
fn a_question_with_no_elimination_that_keeps_the_rows_is_rejected() {
    let src = program(
        "ok(x, y, z, w) = 4 * x - 12 * w - 10 * y - 12 * z + 11 >= 0 && 4 * w + 10 * x - 10 * y \
         - 11 * z - 28 >= 0 && 11 * w + 4 * x - y + 12 * z - 28 >= 0 && -8 * w - 5 * x + 12 * y \
         - z + 31 >= 0;",
        "x: a, y: a, z: a, w: a",
    );
    assert_eq!(
        rejection("growth", &src),
        "1:1: whether `ok` can hold is not decided: the integer constraints have three \
         variables or more, each of whose elimination would enlarge them, so whether they hold \
         at an integer point is not decided\n  \
         [1] 1:18: the constraints: 12 * w + 10 * y + 12 * z <= 4 * x + 11 && 4 * w + 10 * x \
         >= 10 * y + 11 * z + 28 && 11 * w + 4 * x + 12 * z >= y + 28 && 8 * w + 5 * x + z <= \
         12 * y + 31"
    );
}

#[test]
fn a_question_whose_point_lies_past_one_splinter_is_rejected() {
    let src = program(
        "ok(x, y, z) = 4 - 2 * x - 3 * y - 6 * z >= 0 && -4 * x - 6 * z - 22 >= 0 && x - y + 4 \
         * z + 36 >= 0 && 2 * x + 3 * y + 3 * z - 24 >= 0;",
        "x: a, y: a, z: a",
    );
    assert_eq!(
        rejection("shadows", &src),
        "1:1: whether `ok` can hold is not decided: the integer constraints have rational \
         points, and an integer point could lie only in a splinter of a splinter of their \
         projection, so whether one exists is not decided\n  \
         [1] 1:15: the constraints: 2 * x + 3 * y + 6 * z <= 4 && 4 * x + 6 * z <= -22 && x + \
         4 * z >= y - 36 && 2 * x + 3 * y + 3 * z >= 24"
    );
}

#[test]
fn a_decided_question_over_four_names_is_accepted() {
    // Four names with an equality to eliminate and unit bounds: the solver decides it.
    let src = program(
        "ok(x, y, z, w) = 0 <= x && x <= 10 && 0 <= y && y <= x && x + y + z + w == 7;",
        "x: a, y: a, z: 0, w: 7 - 2 * a",
    );
    let o = run("decided", &src, "3\n", &[]);
    assert_eq!(
        (o.status, o.stdout.as_str(), o.stderr.as_str()),
        (0, "in\n", "")
    );
}

#[test]
fn the_linear_questions_of_a_unit_scale() {
    // `n` functions of two linear tests each, every one asked whether it can hold and fail.
    let unit = |n: usize| {
        let mut src: String = (0..n)
            .map(|i| format!("ok{i}(x, y) = 0 <= 3 * x + 5 * y && 2 * x - 7 * y <= {i};\n"))
            .collect();
        src.push_str(&program("", "x: a, y: a").replace("ok(", "ok0("));
        src
    };
    let (small, large) = (unit(64), unit(64 * zed_tests::scaling::FACTOR));
    for src in [&small, &large] {
        assert!(zedc::run::load(src.as_bytes()).is_ok());
    }
    zed_tests::scaling::check("the linear questions of a unit", 64, |m| {
        let src = if m == 64 { &small } else { &large };
        drop(zedc::run::load(src.as_bytes()));
    });
}
