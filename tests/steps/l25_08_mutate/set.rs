//! The mutation set of A103 (MUTATION.md, DESIGN.md L25.8): each heuristic H1 to H12 with
//! every mutant it gives, the two points next to a border that its mutants ask a table for,
//! the literal neighbor left out at an `int` comparison, the operators outside the set, the
//! declared constants left alone, and the A103 example. The list of cases is MUTATION.md
//! section 7.

use super::cases::changes;
use super::report;

/// The mutants of the one-line definition `f(params) = body`, without the table `rows`, as
/// `line:col: \`was\` replaced by \`to\` in \`f\` at path`.
fn of(params: &str, body: &str, rows: &str) -> Vec<String> {
    changes(&format!("f({params}) = {body} test {{ {rows} }}\n"))
}

/// `line` of a mutant of `f` at column `col` of line 1.
fn at(col: usize, was: &str, to: &str, path: &str) -> String {
    format!("1:{col}: `{was}` replaced by `{to}` in `f` at {path}")
}

const INTS: &str = "positional a: int, b: int";
const FLOATS: &str = "positional a: f64, b: f64";
const BOOLS: &str = "positional a: bool, b: bool";

/// H1 and H2: at `int`, with no literal operand, a comparison gives its strictness neighbor,
/// and its right operand moved one the other way, so the two mutants ask for the two points
/// next to the border (MUTATION.md 3.1).
#[test]
fn h1_h2_a_comparison_at_int_gives_its_neighbor_and_the_moved_bound() {
    for (op, to, moved) in [
        ("<", "<=", "a < b - 1"),
        ("<=", "<", "a <= b + 1"),
        (">", ">=", "a > b + 1"),
        (">=", ">", "a >= b - 1"),
    ] {
        let body = format!("a {op} b");
        assert_eq!(
            of(INTS, &body, "(1, 2) -> true"),
            [at(34, op, to, ".0"), at(34, &body, moved, ".0")],
            "{body}"
        );
    }
    for (op, to) in [("==", "!="), ("!=", "==")] {
        assert_eq!(
            of(INTS, &format!("a {op} b"), "(1, 2) -> true"),
            [at(34, op, to, ".0")]
        );
    }
}

/// H1 and H3: not at `int`, a comparison gives its strictness neighbor and is reversed; no
/// bound is moved, since `f64` and `rat` have no next value one away.
#[test]
fn h3_a_comparison_not_at_int_is_reversed() {
    for (op, to, back) in [
        ("<", "<=", ">"),
        ("<=", "<", ">="),
        (">", ">=", "<"),
        (">=", ">", "<="),
    ] {
        assert_eq!(
            of(FLOATS, &format!("a {op} b"), "(1.0, 2.0) -> true"),
            [at(34, op, to, ".0"), at(34, op, back, ".0")],
            "{op}"
        );
    }
}

/// MUTATION.md 3.1, the derivation: each of `<`, `<=`, `>`, `>=` at `int` has its two mutants
/// detected by a table holding the two points next to the border, the tie and the point one
/// off it on the other side, and one of them lives when either point is missing.
#[test]
fn the_two_points_next_to_a_border_detect_h1_and_h2_and_each_is_needed() {
    for (op, tie, off, h1, h2) in [
        ("<", "(5, 5) -> false", "(4, 5) -> true", "<=", "a < b - 1"),
        ("<=", "(5, 5) -> true", "(6, 5) -> false", "<", "a <= b + 1"),
        (">", "(5, 5) -> false", "(6, 5) -> true", ">=", "a > b + 1"),
        (">=", "(5, 5) -> true", "(4, 5) -> false", ">", "a >= b - 1"),
    ] {
        let body = format!("a {op} b");
        let unit = |rows: &str| report(&format!("f({INTS}) = {body} test {{ {rows} }}\n"));
        let lives = |col, was: &str, to: &str| {
            format!(
                "1:{col}: undetected: `{was}` replaced by `{to}` in `f` at .0: every row that \
                 reaches it passes"
            )
        };
        assert_eq!(
            unit(&format!("{tie}, {off}")),
            ["2 mutants: 2 detected, 0 undetected, 0 skipped, 0 not run"],
            "{body}"
        );
        assert_eq!(
            unit(off),
            [
                lives(34, op, h1),
                "2 mutants: 1 detected, 1 undetected, 0 skipped, 0 not run".to_string()
            ],
            "{body}"
        );
        assert_eq!(
            unit(tie),
            [
                lives(34, &body, h2),
                "2 mutants: 1 detected, 1 undetected, 0 skipped, 0 not run".to_string()
            ],
            "{body}"
        );
    }
}

/// H4 and MUTATION.md 3.1: at an `int` comparison with a literal operand, the literal's
/// neighbor that is the strictness neighbor again is left out: `a < 10` gives `9` and not `11`
/// (`a < 11` is `a <= 10`), `a <= 10` gives `11` and not `9`; on the left the other one; under
/// a written `-` the direction reverses.
#[test]
fn h4_the_literal_neighbor_that_is_h1_again_is_left_out() {
    let p = "positional a: int";
    for (body, op, to, col, kept) in [
        ("a < 10", "<", "<=", 28, "9"),
        ("a <= 10", "<=", "<", 29, "11"),
        ("a > 10", ">", ">=", 28, "11"),
        ("a >= 10", ">=", ">", 29, "9"),
    ] {
        assert_eq!(
            of(p, body, "1 -> true"),
            [at(26, op, to, ".0"), at(col, "10", kept, ".0.1")],
            "{body}"
        );
    }
    assert_eq!(
        of(p, "10 < a", "1 -> true"),
        [at(27, "<", "<=", ".0"), at(24, "10", "11", ".0.0")]
    );
    // `a < -10` is `a <= -10` as `a < -9`, the neighbor 9 of the written 10.
    let below = of(p, "a < -10", "1 -> true");
    assert_eq!(below.len(), 2, "{below:?}");
    assert_eq!(below[0], at(26, "<", "<=", ".0"));
    assert!(
        below[1].starts_with("1:29: `10` replaced by `11`"),
        "{below:?}"
    );
    // Not at `int` both neighbors stay: `a < 10.0` and `a < 10.5` differ there.
    assert_eq!(
        of("positional a: f64", "a < 10.5", "1.0 -> true"),
        [
            at(26, "<", "<=", ".0"),
            at(26, "<", ">", ".0"),
            at(28, "10.5", "10.4", ".0.1"),
            at(28, "10.5", "10.6", ".0.1"),
        ]
    );
}

/// H4: an inline decimal literal is changed by one unit of its last written digit, at the
/// carrier it adopted, its exponent, separators and suffix kept.
#[test]
fn h4_a_decimal_literal_moves_by_one_unit_of_its_last_digit() {
    for (carrier, lit, below, above) in [
        ("f64", "2.5", "2.4", "2.6"),
        ("f64", "1.5e-3", "1.4e-3", "1.6e-3"),
        ("f64", "1_000.5", "1000.4", "1000.6"),
        ("f64", "0.0", "-0.1", "0.1"),
        ("f64", "1.9", "1.8", "2.0"),
        ("f64", "10.0", "9.9", "10.1"),
        // A carry out of the first digit, and a borrow down to 0 that is not below zero.
        ("f64", "9.9", "9.8", "10.0"),
        ("f64", "0.1", "0.0", "0.2"),
        ("f32", "2.5", "2.4", "2.6"),
        ("rat", "2.5r", "2.4r", "2.6r"),
    ] {
        let p = format!("positional x: {carrier}");
        assert_eq!(
            of(&p, &format!("x + {lit}"), "1 -> 2"),
            [
                at(26, "+", "-", ".0"),
                at(26, &format!("x + {lit}"), &format!("-(x + {lit})"), ".0"),
                at(28, lit, below, ".0.1"),
                at(28, lit, above, ".0.1"),
            ],
            "{carrier} {lit}"
        );
    }
}

/// H4 and the build-stage skip: a neighbor that rounds to the original at the carrier is the
/// same program, and is skipped.
#[test]
fn h4_a_decimal_neighbor_that_rounds_to_the_original_is_skipped() {
    let unit = "f(positional x: f64) = x + 1.00000000000000001 test { 2.0 -> 3.0 }\n";
    assert_eq!(
        report(unit),
        [
            "1:28: skipped: `1.00000000000000001` replaced by `1.00000000000000000` in `f` at \
             .0.1: the build stage gives the definition the original's term",
            "1:28: skipped: `1.00000000000000001` replaced by `1.00000000000000002` in `f` at \
             .0.1: the build stage gives the definition the original's term",
            "4 mutants: 2 detected, 0 undetected, 2 skipped, 0 not run",
        ]
    );
}

/// H5: a written unary `-` not on a literal is removed; the `+` under it is not the root of
/// its expression, so no `-` is inserted around it (H6).
#[test]
fn h5_a_written_minus_is_removed() {
    let p = "positional a: int";
    assert_eq!(of(p, "-a", "1 -> -1"), [at(24, "-a", "a", ".0")]);
    let p = INTS;
    assert_eq!(
        of(p, "-(a + b)", "(1, 2) -> -3"),
        [
            at(32, "-(a + b)", "(a + b)", ".0"),
            at(36, "+", "-", ".0.0")
        ]
    );
}

/// H6: a `-` is inserted at the root of an arithmetic expression, not at a binary `-`, and
/// not inside the expression.
#[test]
fn h6_a_minus_is_inserted_at_the_root_of_an_arithmetic_expression() {
    assert_eq!(
        of(INTS, "a + b", "(1, 2) -> 3"),
        [at(34, "+", "-", ".0"), at(34, "a + b", "-(a + b)", ".0")]
    );
    assert_eq!(
        of(INTS, "a * b + a", "(1, 2) -> 3"),
        [
            at(38, "+", "-", ".0"),
            at(38, "a * b + a", "-(a * b + a)", ".0")
        ]
    );
    assert_eq!(
        of(INTS, "a - b", "(1, 2) -> -1"),
        [at(34, "-", "+", ".0"), at(34, "a - b", "b - a", ".0")]
    );
}

/// H7: `&&` and `||` swapped, each operand dropped, and `!` inserted before each operand that
/// is not a written `!`.
#[test]
fn h7_and_and_or_are_swapped_dropped_and_negated() {
    let col = |c, was: &str, to: &str| at(c, was, to, ".0");
    assert_eq!(
        of(BOOLS, "a && b", "(true, true) -> true"),
        [
            col(36, "&&", "||"),
            col(36, "a && b", "a"),
            col(36, "a && b", "b"),
            col(36, "a && b", "!a && b"),
            col(36, "a && b", "a && !b"),
        ]
    );
    assert_eq!(
        of(BOOLS, "a || b", "(true, true) -> true"),
        [
            col(36, "||", "&&"),
            col(36, "a || b", "a"),
            col(36, "a || b", "b"),
            col(36, "a || b", "!a || b"),
            col(36, "a || b", "a || !b"),
        ]
    );
    // No `!` before a written `!`: H8 removes it instead.
    assert_eq!(
        of(BOOLS, "!a && b", "(true, true) -> false"),
        [
            col(37, "&&", "||"),
            col(37, "!a && b", "!a"),
            col(37, "!a && b", "b"),
            col(37, "!a && b", "!a && !b"),
            at(34, "!a", "a", ".0.0"),
        ]
    );
    // An operand that is not one name is put in parentheses under the `!`.
    assert_eq!(
        of(INTS, "a == 1 || b == 2", "(1, 2) -> true")[3],
        at(39, "a == 1 || b == 2", "!(a == 1) || b == 2", ".0")
    );
}

/// H8: a written `!` is removed.
#[test]
fn h8_a_written_not_is_removed() {
    assert_eq!(
        of("positional a: bool", "!a", "true -> false"),
        [at(25, "!a", "a", ".0")]
    );
}

/// H9: an `if` replaced by its `then` branch and by its `else` branch, and its condition
/// negated, but not when it is a written `!`.
#[test]
fn h9_an_if_is_replaced_by_each_branch_and_its_condition_negated() {
    let p = "positional c: bool, a: int, b: int";
    let whole = "if c { a } else { b }";
    assert_eq!(
        of(p, whole, "(true, 1, 2) -> 1"),
        [
            at(41, whole, "{ a }", ".0"),
            at(41, whole, "{ b }", ".0"),
            at(41, whole, "if !c { a } else { b }", ".0"),
        ]
    );
    let whole = "if !c { a } else { b }";
    assert_eq!(
        of(p, whole, "(true, 1, 2) -> 2"),
        [
            at(41, whole, "{ a }", ".0"),
            at(41, whole, "{ b }", ".0"),
            at(44, "!c", "c", ".0.0"),
        ]
    );
}

/// H10 and H11: `div` and `mod` each way, `/` by `*`, `*` by `/` where `/` is defined; the
/// operands swapped where the order matters; a `-` at the root (H6). `b` is declared in
/// `int[1..]`, as `mod` takes its modulus (DESIGN.md sec:domains; QUESTIONS A174).
#[test]
fn h10_h11_the_arithmetic_operators_and_their_operand_order() {
    for (op, to) in [("div", "mod"), ("mod", "div")] {
        let body = format!("a {op} b");
        assert_eq!(
            of("positional a: int, b: int[1..]", &body, "(7, 2) -> 1"),
            [
                at(39, op, to, ".0"),
                at(39, &body, &format!("b {op} a"), ".0"),
                at(39, &body, &format!("-({body})"), ".0"),
            ]
        );
    }
    assert_eq!(
        of(FLOATS, "a / b", "(1.0, 2.0) -> 0.5"),
        [
            at(34, "/", "*", ".0"),
            at(34, "a / b", "b / a", ".0"),
            at(34, "a / b", "-(a / b)", ".0"),
        ]
    );
    assert_eq!(
        of(FLOATS, "a * b", "(1.0, 2.0) -> 2.0"),
        [at(34, "*", "/", ".0"), at(34, "a * b", "-(a * b)", ".0")]
    );
    assert_eq!(
        of("positional a: int", "a ^ 3", "2 -> 8"),
        [
            at(26, "a ^ 3", "3 ^ a", ".0"),
            at(26, "a ^ 3", "-(a ^ 3)", ".0"),
            at(28, "3", "2", ".0.1"),
            at(28, "3", "4", ".0.1"),
        ]
    );
    assert_eq!(
        of(
            "positional a: String, b: String",
            "a ++ b",
            "(\"x\", \"y\") -> \"xy\""
        ),
        [at(40, "a ++ b", "b ++ a", ".0")]
    );
    // A swapped operand that is not one name keeps its parentheses, once.
    assert_eq!(
        of(INTS, "(a + 1) - b", "(1, 2) -> 0")[1],
        at(40, "(a + 1) - b", "b - (a + 1)", ".0")
    );
}

/// MUTATION.md 4: the operators outside the set give no mutant of their own: `^` is not
/// replaced and not swapped away from `int`, `*` at `int` has no `/`, `+` and `*` are not
/// swapped, list `++` is not marked.
#[test]
fn the_operators_outside_the_set_give_no_mutant() {
    assert_eq!(
        of(FLOATS, "a ^ b", "(2.0, 3.0) -> 8.0"),
        [at(34, "a ^ b", "-(a ^ b)", ".0")]
    );
    assert_eq!(
        of(INTS, "a * b", "(1, 2) -> 2"),
        [at(34, "a * b", "-(a * b)", ".0")]
    );
    assert_eq!(
        of("positional a: int", "[a] ++ [a]", "1 -> [1, 1]"),
        Vec::<String>::new()
    );
    // A string or boolean literal has no neighbor (MUTATION.md 3.7: `int`, `rat` and float
    // literals only); only the `==` beside it has its mutant.
    assert_eq!(
        of("positional a: bool", "a == true", "true -> true"),
        [at(27, "==", "!=", ".0")]
    );
    assert_eq!(
        of("positional a: String", "a == \"x\"", "\"x\" -> true"),
        [at(29, "==", "!=", ".0")]
    );
}

/// Author, A103: "leave alone constants that are declared, but tweak inline constants". A
/// top-level binding, a local binding and a parameter default that read no name have no
/// mutant, beside an inline literal in the same definition that has its two. A field default
/// waits for structs (plan row L2.4, whose deferred tests hold `a_field_default_has_no_mutant`).
#[test]
fn declared_constants_have_no_mutant() {
    let unit = "limit = 10;\nf(positional a: int) = a * limit + 3 test { 1 -> 13 }\n";
    assert_eq!(
        changes(unit),
        [
            "2:34: `+` replaced by `-` in `f` at .0",
            "2:34: `a * limit + 3` replaced by `-(a * limit + 3)` in `f` at .0",
            "2:36: `3` replaced by `2` in `f` at .0.1",
            "2:36: `3` replaced by `4` in `f` at .0.1",
        ]
    );
    let unit = "rate = 2 * 3;\nf(positional a: int) = a + rate test { 1 -> 7 }\n";
    assert_eq!(
        changes(unit),
        [
            "2:26: `+` replaced by `-` in `f` at .0",
            "2:26: `a + rate` replaced by `-(a + rate)` in `f` at .0",
        ]
    );
    let unit = "f(positional x: f64) {\n  k = 2.5;\n  return x * k + 1.5;\n} test { 1.0 -> 4.0 }\n";
    let found = changes(unit);
    assert!(found.iter().all(|l| !l.contains("`2.5`")), "{found:?}");
    assert!(
        found.iter().any(|l| l.contains("`1.5` replaced by `1.4`")),
        "{found:?}"
    );
    let unit = "f(positional a: int, step = 1) = a + step + 2 test { (1, 1) -> 4 }\ng(positional a: int) = f(a) test { 1 -> 4 }\n";
    let found = changes(unit);
    assert!(
        found.iter().all(|l| !l.contains("`1` replaced")),
        "{found:?}"
    );
    assert!(
        found.iter().any(|l| l.contains("`2` replaced by `1`")),
        "{found:?}"
    );
    // A right side that reads a name is not a constant: its literals are inline.
    let unit = "f(positional a: int) {\n  k = a + 1;\n  return k;\n} test { 1 -> 2 }\n";
    let found = changes(unit);
    assert!(
        found.iter().any(|l| l.contains("`1` replaced by `2`")),
        "{found:?}"
    );
}

/// H12 (MUTATION.md 3.12, section 7 item 9): `k in 0..<10` gives `k in 0..=10` and back, one
/// mutant each, the low end's strictness untouched; at a literal high end the H4 neighbor that
/// is the flip again is left out (`11` at `..<10`, since `0..<11` is `0..=10`; `9` at `..=10`),
/// and the low end keeps both of its neighbors.
#[test]
fn h12_a_range_s_high_end_is_flipped() {
    let p = "positional k: int";
    assert_eq!(
        of(p, "k in 0..<10", "5 -> true"),
        [
            at(30, "..<", "..=", ".0.1"),
            at(29, "0", "-1", ".0.1.0"),
            at(29, "0", "1", ".0.1.0"),
            at(33, "10", "9", ".0.1.1"),
        ]
    );
    assert_eq!(
        of(p, "k in 0..=10", "5 -> true"),
        [
            at(30, "..=", "..<", ".0.1"),
            at(29, "0", "-1", ".0.1.0"),
            at(29, "0", "1", ".0.1.0"),
            at(33, "10", "11", ".0.1.1.0"),
        ]
    );
    // A high end that is not a literal keeps no neighbor to leave out; its own operator's
    // mutants are made as anywhere.
    let found = of("positional k: int, n: int", "k in 0..<n", "(5, 9) -> true");
    assert_eq!(found[0], at(38, "..<", "..=", ".0.1"), "{found:?}");
    assert_eq!(
        found.iter().filter(|l| l.contains("`..")).count(),
        1,
        "{found:?}"
    );
}

/// H12, the derivation of MUTATION.md 3.12: the `isDigitKey` table with no row at the key `10`
/// leaves the flip undetected, and the row `10 -> false` detects it. The flip of a range a fold
/// reads, the domain of a `for` in the kernel's terms, is detected by any row where the entry
/// at the high end is not zero. A range in a type gives no mutant (section 4: a changed type is
/// a program the checker would see again).
#[test]
fn h12_the_row_at_the_high_end_detects_the_flip() {
    let unit = |rows: &str| {
        report(&format!(
            "isDigitKey(positional k: int) = k in 0..<10 test {{ {rows} }}\n"
        ))
    };
    let flip = |l: &&String| l.contains("`..<` replaced by `..=`");
    let without = unit("0 -> true, 5 -> true, 11 -> false");
    assert_eq!(
        without.iter().filter(flip).collect::<Vec<_>>(),
        [
            "1:39: undetected: `..<` replaced by `..=` in `isDigitKey` at .0.1: every row that \
          reaches it passes"
        ],
        "{without:?}"
    );
    // `report` writes only the mutants that live, so each unit is also checked to make the flip.
    let rows = "0 -> true, 5 -> true, 11 -> false, 10 -> false";
    let made = changes(&format!(
        "isDigitKey(positional k: int) = k in 0..<10 test {{ {rows} }}\n"
    ));
    assert_eq!(made.iter().filter(flip).count(), 1, "{made:?}");
    let with = unit(rows);
    assert!(!with.iter().any(|l| flip(&l)), "{with:?}");
    let sum = "f(positional n: int) = (0..<n) >< (+) test { 3 -> 3 }\n";
    assert_eq!(
        changes(sum).iter().filter(flip).count(),
        1,
        "{:?}",
        changes(sum)
    );
    let sum = report(sum);
    assert!(!sum.iter().any(|l| flip(&l)), "{sum:?}");
    let typed = changes("f(positional k: int[0..<10]) = k test { 3 -> 3 }\n");
    assert!(typed.iter().all(|l| !l.contains("`..")), "{typed:?}");
}

/// The A103 example of MUTATION.md section 6 with `&&` (the chain `lo <= x < hi` waits for
/// plan row L22.4): with the rows of A103 the moved bound of `lo <= x` and the drop of
/// `lo <= x` live; the row `(0, 10, -1) -> false` detects both.
#[test]
fn the_a103_example() {
    let text = |extra: &str| {
        format!(
            "inRange(positional lo: int, hi: int, x: int) = lo <= x && x < hi test {{\n  \
             (0, 10, 0) -> true,\n  (0, 10, 9) -> true,\n  (0, 10, 10) -> false,{extra}\n}}\n\
             half(positional n: int) = n div 2 test {{ 7 -> 3 }}\n\
             scale(positional x: f64) = x * 2.5 test {{ 2.0 -> 5.0 }}\n"
        )
    };
    assert_eq!(
        report(&text("")),
        [
            "1:56: undetected: `lo <= x && x < hi` replaced by `x < hi` in `inRange` at .0: \
             every row that reaches it passes",
            "1:51: undetected: `lo <= x` replaced by `lo <= x + 1` in `inRange` at .0.0: every \
             row that reaches it passes",
            "18 mutants: 16 detected, 2 undetected, 0 skipped, 0 not run",
        ]
    );
    assert_eq!(
        report(&text("\n  (0, 10, -1) -> false,")),
        ["18 mutants: 18 detected, 0 undetected, 0 skipped, 0 not run"]
    );
}
