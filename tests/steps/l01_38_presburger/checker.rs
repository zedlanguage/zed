//! The solver in the checker, end to end through `zedc run`: a linear question the solver
//! decides rejects nothing, and one it refuses is a rejection with its cause, its span and
//! the constraints.

use zed_tests::step_helpers::l01_19_whole_file_ports::run;

/// A program whose `main` calls `ok`, defined by `def`, at `args`, and prints whether it held;
/// `a` in `args` is the integer on the first line of the input (lines count from 1), or 0.
fn program(def: &str, args: &str) -> String {
    format!(
        "{def}\nmain(stdin: Lines) -> (stdout: Lines) {{\n  a = int(stdin[1] else \"0\") else 0;\n  \
         r = if ok({args}) {{ \"in\" }} else {{ \"out\" }};\n  stdout <- \"${{r}}\";\n}}\n"
    )
}

/// The standard error of a rejected run, with the program's path removed from its first line,
/// and without the source lines the steps underline. The program is written in test directory
/// `name`, so two tests, which may run at once, give two names.
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

/// The menu a refused question prints at L1, numbered after its one note of constraints, both
/// placed at the body that begins at column 18 of line 1 (that of `ok(x, y, z, w) = `): the
/// repairs an L1 program can follow (DESIGN.md sec:diagnostics, row "Linear question outside the
/// polynomial fragment").
const MENU: &str = "[2] 1:18: repair: state an equality on one of the names, as `x == 4 && …`, \
                    so the solver removes that name from the question\n  \
                    [3] 1:18: repair: split the question into functions of fewer constraints \
                    each, and join their results where they are called; a function whose body \
                    joins them asks the joined question again";

/// A refused `ok` over `x, y, z, w`, and, for each repair of the menu, `ok` repaired by it: an
/// equality joined to the body, and the rows split into `first` and `second` joined at the call.
struct Refused {
    name: &'static str,
    rows: [&'static str; 2],
    equality: &'static str,
}

const REFUSED: [Refused; 3] = [
    // Growth: no elimination keeps the four rows within their count.
    Refused {
        name: "growth",
        rows: [
            "4 * x - 12 * w - 10 * y - 12 * z + 11 >= 0 && 4 * w + 10 * x - 10 * y - 11 * z - 28 \
             >= 0",
            "11 * w + 4 * x - y + 12 * z - 28 >= 0 && -8 * w - 5 * x + 12 * y - z + 31 >= 0",
        ],
        equality: "x == 4",
    },
    // Shadows: a point could lie only in a splinter that would be split again with as many
    // variables left.
    Refused {
        name: "shadows",
        rows: [
            "9 * x - 4 * y - 8 * w - 3 >= 0 && 5 * x + 11 * y + 9 * w - 9 >= 0 && -7 * x - 12 * \
             y - 2 * z + 8 * w - 1 >= 0",
            "-9 * x + 8 * y + 7 * z >= 0 && -10 * x + 4 * y - 6 * z - 4 * w + 22 >= 0",
        ],
        equality: "w == 1",
    },
    // Tie: the cycle `3 * next - this >= 10`, whose four names occur alike and share rows.
    Refused {
        name: "tie",
        rows: [
            "3 * y - x - 10 >= 0 && 3 * z - y - 10 >= 0",
            "3 * w - z - 10 >= 0 && 3 * x - w - 10 >= 0",
        ],
        equality: "x == 5",
    },
];

/// A program like [`program`]'s whose `main` tests `test` in place of a call of `ok`.
fn program_testing(defs: &str, test: &str) -> String {
    format!(
        "{defs}\nmain(stdin: Lines) -> (stdout: Lines) {{\n  a = int(stdin[1] else \"0\") else 0;\n  \
         r = if {test} {{ \"in\" }} else {{ \"out\" }};\n  stdout <- \"${{r}}\";\n}}\n"
    )
}

#[test]
fn following_each_repair_of_the_menu_makes_the_program_check() {
    const ARGS: &str = "x: a, y: a, z: a, w: a";
    for r in &REFUSED {
        let [first, second] = r.rows;
        let refused = program(&format!("ok(x, y, z, w) = {first} && {second};"), ARGS);
        let printed = rejection(r.name, &refused);
        assert!(printed.ends_with(MENU), "{}: {printed}", r.name);
        // The question with a name fixed by an equality is decided; each run prints whether
        // `ok` held at the input, which the equality decides with the rows.
        let equality = program(
            &format!("ok(x, y, z, w) = {} && {first} && {second};", r.equality),
            ARGS,
        );
        let split = program_testing(
            &format!("first(x, y, z, w) = {first};\nsecond(x, y, z, w) = {second};"),
            &format!("first({ARGS}) && second({ARGS})"),
        );
        for (repair, src) in [("equality", &equality), ("split", &split)] {
            for input in ["3\n", "5\n"] {
                let o = run(r.name, src, input, &[]);
                assert_eq!(
                    (o.status, o.stderr.as_str()),
                    (0, ""),
                    "{} {repair} {input}",
                    r.name
                );
                // At x = y = z = w = 5 the cycle holds (3 * 5 - 5 = 10); every other case holds
                // at no point x = y = z = w.
                let held = r.name == "tie" && input == "5\n";
                assert_eq!(
                    o.stdout,
                    if held { "in\n" } else { "out\n" },
                    "{} {repair} {input}",
                    r.name
                );
            }
        }
    }
}

#[test]
fn a_refused_question_over_disjunctions_prints_the_menu_and_an_equality_repairs_it() {
    // (name, parameters, rows, the cause's opening words, the equality, the arguments, and
    // whether `ok` holds at inputs 1 and 3 once repaired).
    let cases = [
        // Four names in 0..=2 that differ pairwise: no point, which the search through the
        // disjunctions of `!=` does not settle.
        (
            "disjuncts",
            "x, y, z, w",
            "0 <= x && x <= 2 && 0 <= y && y <= 2 && 0 <= z && z <= 2 && 0 <= w && w <= 2 && x \
             != y && x != z && y != z && x != w && y != w && z != w",
            "the conditions hold alternatives, where one of several cases is enough (from \
             `||`, from `!=`, which holds when either side is the larger, or from a negated \
             `&&`), and the checker looks for a choice of one case from each alternative that \
             can hold with the rest; no choice it tried has values",
            "x == 0",
            "x: a, y: a, z: a, w: a",
            ["out\n", "out\n"],
        ),
        // Two shifts in 0..=9, each early or late, with a total of at most 10: `x` and `y`
        // occur alike, so the search through the disjunctions would go in an order chosen by
        // name (`l01_38_presburger::names`, the shifts with `x + y <= 10`).
        (
            "unordered",
            "x, y",
            "0 <= x && x <= 9 && 0 <= y && y <= 9 && x + y <= 10 && (x <= 2 || x >= 7) && (y \
             <= 2 || y >= 7)",
            "the conditions hold alternatives, where one of several cases is enough (from \
             `||`, from `!=`, which holds when either side is the larger, or from a negated \
             `&&`), and the checker looks for a choice of one case from each alternative that \
             can hold with the rest. After every case that cannot hold is removed, the \
             alternative",
            "x == 1",
            "x: a, y: a",
            ["in\n", "out\n"],
        ),
    ];
    for (name, params, rows, cause, equality, args, outs) in cases {
        let printed = rejection(name, &program(&format!("ok({params}) = {rows};"), args));
        assert!(
            printed.starts_with(&format!(
                "1:1: whether `ok` can hold is not decided: {cause}"
            )),
            "{printed}"
        );
        // The body begins after `ok(`, the parameters and `) = `.
        let menu = MENU.replace("1:18", &format!("1:{}", params.len() + 8));
        assert!(printed.ends_with(&menu), "{printed}");
        let repaired = program(&format!("ok({params}) = {equality} && {rows};"), args);
        for (input, out) in ["1\n", "3\n"].into_iter().zip(outs) {
            let o = run(name, &repaired, input, &[]);
            assert_eq!(
                (o.status, o.stdout.as_str(), o.stderr.as_str()),
                (0, out, ""),
                "{name} {input}"
            );
        }
    }
}

#[test]
fn a_function_that_joins_the_split_questions_asks_the_joined_question_again() {
    // The second half of the split repair's line: joining `first` and `second` in a function
    // other than `main` inlines both, and the joined question is refused as before.
    let [first, second] = REFUSED[0].rows;
    let src = program(
        &format!(
            "first(x, y, z, w) = {first};\nsecond(x, y, z, w) = {second};\nok(x, y, z, w) = \
             first(x:, y:, z:, w:) && second(x:, y:, z:, w:);"
        ),
        "x: a, y: a, z: a, w: a",
    );
    let o = run("joined", &src, "3\n", &[]);
    assert_eq!(o.status, 1, "{}", o.stderr);
    assert!(
        o.stderr.contains("whether `ok` can hold is not decided"),
        "{}",
        o.stderr
    );
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
fn a_satisfiable_question_with_no_elimination_that_keeps_the_rows_is_refused() {
    // The rows hold at (x, y, z, w) = (4, 0, 1, 0), where they are 15, 1, 0 and 10, so `ok` can
    // hold; the refusal claims only that this is not decided, since every elimination would add
    // terms and the box of the bounds and its five points settle nothing.
    let src = program(
        "ok(x, y, z, w) = 4 * x - 12 * w - 10 * y - 12 * z + 11 >= 0 && 4 * w + 10 * x - 10 * y \
         - 11 * z - 28 >= 0 && 11 * w + 4 * x - y + 12 * z - 28 >= 0 && -8 * w - 5 * x + 12 * y \
         - z + 31 >= 0;",
        "x: a, y: a, z: a, w: a",
    );
    assert_eq!(
        rejection("growth-alone", &src),
        format!(
            "1:1: whether `ok` can hold is not decided: to find whole numbers that meet these \
             conditions, the checker removes one variable at a time, putting in place of the \
             conditions on it conditions on the variables left. Here four variables or more \
             are left, and removing any one of them would leave more conditions than there are \
             now, so the work could grow without end. The checker stopped there, with no \
             values found and none ruled out\n  \
             [1] 1:18: the constraints: 12 * w + 10 * y + 12 * z <= 4 * x + 11 && 4 * w + 10 * \
             x >= 10 * y + 11 * z + 28 && 11 * w + 4 * x + 12 * z >= y + 28 && 8 * w + 5 * x + \
             z <= 12 * y + 31\n  {MENU}"
        )
    );
}

#[test]
fn a_refused_question_names_the_parameters_as_written_when_other_functions_share_them() {
    // `other` and `first` bind `x` and `w` too, so elaboration renames `ok`'s parameters
    // `x@k` and `w@k`; the message names them `x` and `w`, as `ok` wrote them, in the order
    // it prints them with no other function in the unit (item NAME-at-print).
    let [first, second] = REFUSED[2].rows;
    let src = program(
        &format!(
            "ok(x, y, z, w) = {first} && {second};\nother(x) = x > 2;\nfirst(w, x1) = w > x1;"
        ),
        "x: a, y: a, z: a, w: a",
    );
    assert_eq!(
        rejection("tie-alone", &src),
        format!(
            "1:1: whether `ok` can hold is not decided: to find whole numbers that meet these \
             conditions, the checker removes one variable at a time, putting in place of the \
             conditions on it conditions on the variables left. Its next step must choose among \
             the variables `w`, `x`, `z`, `y`, which occur alike in the conditions (with the \
             same coefficients, in conditions that are alike) and share the conditions \
             `-w + 3 * x - 10 >= 0`, `3 * w - z - 10 >= 0`, `-x + 3 * y - 10 >= 0`, \
             `3 * z - y - 10 >= 0`, so only their names could order them, and the checker never \
             lets a name change an answer. The checker stopped there, with no values found and \
             none ruled out\n  \
             [1] 1:18: the constraints: x <= 3 * y - 10 && y <= 3 * z - 10 && 3 * w >= z + 10 \
             && w <= 3 * x - 10\n  {MENU}"
        )
    );
}

#[test]
fn a_question_whose_point_lies_past_one_splinter_is_rejected() {
    let src = program(
        "ok(x, y, z, w) = 9 * x - 4 * y - 8 * w - 3 >= 0 && 5 * x + 11 * y + 9 * w - 9 >= 0 && -7 \
         * x - 12 * y - 2 * z + 8 * w - 1 >= 0 && -9 * x + 8 * y + 7 * z >= 0 && -10 * x + 4 * y \
         - 6 * z - 4 * w + 22 >= 0;",
        "x: a, y: a, z: a, w: a",
    );
    assert_eq!(
        rejection("shadows-alone", &src),
        format!(
            "1:1: whether `ok` can hold is not decided: to find whole numbers that meet these \
             conditions, the checker removes one variable at a time, putting in place of the \
             conditions on it conditions on the variables left. Where the values a variable can \
             take have gaps, it splits the conditions into cases, one for each gap. Here the \
             only values could lie in a case that would have to be split again with as many \
             variables left as before, so the splitting need not end. The checker stopped \
             there, with no values found and none ruled out\n  \
             [1] 1:18: the constraints: 8 * w + 4 * y <= 9 * x - 3 && 9 * w + 5 * x + 11 * y >= \
             9 && 8 * w >= 7 * x + 12 * y + 2 * z + 1 && 9 * x <= 8 * y + 7 * z && 4 * w + 10 * \
             x + 6 * z <= 4 * y + 22\n  {MENU}"
        )
    );
}

#[test]
fn a_question_over_three_names_past_one_splinter_is_decided() {
    // The question this file rejected before LIVE3 (a splinter of a splinter): over three
    // names it is now decided by `live3`, so nothing is rejected, and `ok` holds at
    // (5, 12, -7): 4 - 10 - 36 + 42 = 0, -20 + 42 - 22 = 0, 5 - 12 - 28 + 36 = 1 and
    // 10 + 36 - 21 - 24 = 1. With input 5 the call is at (5, 12, -7); with 0 at (0, 7, -2),
    // where the second row is 12 - 22 = -10.
    let src = program(
        "ok(x, y, z) = 4 - 2 * x - 3 * y - 6 * z >= 0 && -4 * x - 6 * z - 22 >= 0 && x - y + 4 \
         * z + 36 >= 0 && 2 * x + 3 * y + 3 * z - 24 >= 0;",
        "x: a, y: a + 7, z: 0 - a - 2",
    );
    for (input, out) in [("5\n", "in\n"), ("0\n", "out\n")] {
        let o = run("splinter3", &src, input, &[]);
        assert_eq!(
            (o.status, o.stdout.as_str(), o.stderr.as_str()),
            (0, out, ""),
            "{input}"
        );
    }
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
    // The questions are timed alone, on a unit loaded before the timing (COMPLEXITY.md F85).
    let units: std::collections::BTreeMap<usize, _> = [64, 64 * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|m| {
            let src = unit(m);
            let program = zedc::run::load(src.as_bytes()).unwrap();
            (m, (zed_tests::deep::statements(&src), program))
        })
        .collect();
    zed_tests::scaling::check("the linear questions of a unit", 64, |m| {
        let (stmts, program) = &units[&m];
        let refused = zedc::front::linear_questions(stmts, program.unit());
        assert!(refused.is_empty(), "{refused:?}");
    });
}

#[test]
fn a_refused_question_through_a_call_prints_what_the_question_written_out_prints() {
    // `ok` holds `base`'s relation as one shared part (LOAD-chain-share); the refusal, its
    // cause and the constraints it prints are those of `ok` with `base`'s rows written in it.
    // But for the tie: `main` passes `ok` a local, so `ok`'s parameters join no class with
    // `base`'s, and `ok`'s call of `base` binds `base`'s canonical atoms to `ok`'s
    // (LOAD-chain-affine). The question is then over eight variables and four equalities, whose
    // structure tells every variable apart, and the solver decides it (it holds, at 5 for all
    // four) with no choice falling to a name; written over four names alike, the rows tie and
    // are refused. The answer is the same under renamings of the four names, both ways round,
    // checked below; `ok` is false at 3.
    const ARGS: &str = "x: a, y: a, z: a, w: a";
    for r in &REFUSED {
        let [first, second] = r.rows;
        let called = program(
            &format!(
                "base(x, y, z, w) = {first};\nok(x, y, z, w) = base(x: x, y: y, z: z, w: w) && \
                 {second};"
            ),
            ARGS,
        );
        let written = program(&format!("ok(x, y, z, w) = {first} && {second};"), ARGS);
        if r.name == "tie" {
            // `src` with the names x, y, z, w renamed to `to`, where they stand alone.
            let renamed = |src: &str, to: [&str; 4]| {
                let mut out = String::new();
                let cs: Vec<char> = src.chars().collect();
                for (i, &c) in cs.iter().enumerate() {
                    let alone = |j: Option<&char>| !j.is_some_and(|c| c.is_alphanumeric());
                    match "xyzw".find(c) {
                        Some(k)
                            if alone(i.checked_sub(1).map(|j| &cs[j])) && alone(cs.get(i + 1)) =>
                        {
                            out.push_str(to[k])
                        }
                        _ => out.push(c),
                    }
                }
                out
            };
            for (i, to) in [
                ["x", "y", "z", "w"],
                ["w", "z", "y", "x"],
                ["p4", "p3", "p2", "p1"],
                ["p1", "p2", "p3", "p4"],
            ]
            .into_iter()
            .enumerate()
            {
                for input in ["3\n", "5\n"] {
                    let o = run(
                        &format!("tie-called-{i}"),
                        &renamed(&called, to),
                        input,
                        &[],
                    );
                    let want = if input == "3\n" { "out\n" } else { "in\n" };
                    assert_eq!(
                        (o.status, o.stdout.as_str()),
                        (0, want),
                        "{to:?}: {}",
                        o.stderr
                    );
                }
                rejection(&format!("tie-written-{i}"), &renamed(&written, to));
            }
            continue;
        }
        let called = rejection(&format!("{}-called", r.name), &called)
            .replace("2:1: ", "1:1: ")
            .replace("2:18: ", "1:18: ");
        assert_eq!(
            called,
            rejection(&format!("{}-written", r.name), &written),
            "{}",
            r.name
        );
    }
}

#[test]
fn a_question_read_in_its_callees_coordinates_is_answered_and_printed_over_its_own_parameters() {
    // LOAD-chain-args: `ok` passes `tie` its parameters renamed, and moved by constants, so
    // its relation is read over `tie`'s parameters; what the checker prints for `ok` is what it
    // prints when `ok` states the same constraints over its own parameters, with no call.
    let [first, second] = REFUSED[2].rows;
    // `rows` with each of `x`, `y`, `z` and `w` replaced by its argument in `args`.
    let substituted = |rows: &str, args: [&str; 4]| -> String {
        let mut out = String::new();
        let mut prev = ' ';
        for ch in rows.chars() {
            match "xyzw".find(ch).filter(|_| !prev.is_alphanumeric()) {
                Some(i) => out.push_str(&format!("({})", args[i])),
                None => out.push(ch),
            }
            prev = ch;
        }
        out
    };
    // What the checker prints: the messages and their notes, without the source lines.
    let printed = |name: &str, src: &str| -> String {
        let o = run(name, src, "3\n", &[]);
        assert_eq!(o.status, 1, "{}", o.stderr);
        (o.stderr.lines())
            .map(|l| l.split_once("prog.zed:").map_or(l, |(_, rest)| rest))
            .filter(|l| {
                l.starts_with(|c: char| c.is_ascii_digit()) || l.trim_start().starts_with('[')
            })
            .collect::<Vec<_>>()
            .join("\n")
    };
    let tie = format!("tie(x, y, z, w) = {first} && {second};");
    for (i, args) in [["b", "c", "d", "a"], ["b + 1", "c", "d - 2", "a"]]
        .into_iter()
        .enumerate()
    {
        let call = format!(
            "ok(a, b, c, d) = tie(x: {}, y: {}, z: {}, w: {});",
            args[0], args[1], args[2], args[3]
        );
        let alone = format!(
            "ok(a, b, c, d) = {} && {};",
            substituted(first, args),
            substituted(second, args)
        );
        let through = printed(
            &format!("coordinates-call-{i}"),
            &program(&format!("{tie}\n{call}"), "a: a, b: a, c: a, d: a"),
        );
        let expected = printed(
            &format!("coordinates-alone-{i}"),
            &program(&format!("{tie}\n{alone}"), "a: a, b: a, c: a, d: a"),
        );
        assert_eq!(through, expected, "{call}");
        assert!(through.contains("whether `tie` can hold"), "{through}");
    }
}

#[test]
fn a_question_refused_through_a_call_by_a_map_of_its_parameters_names_its_parameters() {
    // LOAD-chain-affine: `ok` passes `base` its `x` doubled or negated, so `base`'s relation
    // is read once, over its own atoms, and the call binds them to `ok`'s terms. The rejection
    // of `ok`'s question, its cause and constraints, are those of `ok` with `base`'s rows
    // written in it at those terms, over `ok`'s own parameters.
    const ARGS: &str = "x: a, y: a, z: a, w: a";
    let mut refused = 0;
    for r in &REFUSED[..2] {
        let [first, second] = r.rows;
        for (i, x) in ["2 * x", "0 - x"].into_iter().enumerate() {
            // `first` with each `x` replaced by `(x)`.
            let mut at = String::new();
            let mut prev = ' ';
            for ch in first.chars() {
                match ch == 'x' && !prev.is_alphanumeric() {
                    true => at.push_str(&format!("({x})")),
                    false => at.push(ch),
                }
                prev = ch;
            }
            let called = program(
                &format!(
                    "base(x, y, z, w) = {first};\nok(x, y, z, w) = base(x: {x}, y: y, z: z, w: w) \
                     && {second};"
                ),
                ARGS,
            );
            let written = program(&format!("ok(x, y, z, w) = {at} && {second};"), ARGS);
            let (o, w) = (
                run(&format!("{}-map-{i}-called", r.name), &called, "3\n", &[]),
                run(&format!("{}-map-{i}-written", r.name), &written, "3\n", &[]),
            );
            assert_eq!(
                (o.status, &o.stdout),
                (w.status, &w.stdout),
                "{x}: {}",
                o.stderr
            );
            if o.status != 1 {
                continue;
            }
            refused += 1;
            let called = rejection(&format!("{}-map-{i}-called", r.name), &called)
                .replace("2:1: ", "1:1: ")
                .replace("2:18: ", "1:18: ");
            assert!(called.contains("whether `ok` can hold"), "{called}");
            assert!(!called.contains(['#', '@']), "{called}");
            assert_eq!(
                called,
                rejection(&format!("{}-map-{i}-written", r.name), &written),
                "{} at {x}",
                r.name
            );
        }
    }
    assert!(refused > 0, "no question refused");
}
