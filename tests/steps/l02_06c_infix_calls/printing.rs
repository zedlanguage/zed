//! The printer writes an infix call back infix (DESIGN.md tier 6), with the parentheses
//! precedence needs and no others (P191): the round trip keeps the syntax tree, and deleting
//! any pair of parentheses from the printed text gives a text that is rejected or that means
//! another tree. A call written out stays written out.

use zed_tests::instances::Rng;
use zed_tests::step_helpers::l01_10_lambdas_types_else_tuples::sx;
use zedc::format::format_source;

/// The expression `e` as the formatter prints it.
fn printed(e: &str) -> String {
    let out = format_source(format!("x = {e};\n").as_bytes()).unwrap();
    out.strip_prefix("x = ")
        .and_then(|s| s.strip_suffix(";\n"))
        .unwrap_or_else(|| panic!("{e} printed as {out}"))
        .to_string()
}

#[test]
fn printed_back_infix() {
    for (written, want) in [
        ("1 ~plus~ 2", "1 ~plus~ 2"),
        ("plus(1, 2)", "plus(1, 2)"),
        ("a ~f~ b ~g~ c", "a ~f~ b ~g~ c"),
        ("(a ~f~ b) ~g~ c", "a ~f~ b ~g~ c"),
        ("a ~f~ (b ~g~ c)", "a ~f~ (b ~g~ c)"),
        ("(p ~scale~ k) * 2", "(p ~scale~ k) * 2"),
        ("(a + b) ~f~ c", "(a + b) ~f~ c"),
        ("-(p ~f~ v)", "-(p ~f~ v)"),
        ("(-p) ~f~ v", "(-p) ~f~ v"),
        ("p ~f~ (-1)", "p ~f~ -1"),
        ("p ~f~ -(-b)", "p ~f~ - -b"),
        ("p ~f~ (-k^2)", "p ~f~ (-k^2)"),
        ("(2^3) ~f~ 1", "(2^3) ~f~ 1"),
        ("2^(3 ~f~ 1)", "2^(3 ~f~ 1)"),
        ("(p.pos) ~f~ (v.dir)", "p.pos ~f~ v.dir"),
        ("(a ~f~ b).len", "(a ~f~ b).len"),
        ("0..<a ~f~ b", "0..<a ~f~ b"),
        ("(a..<b) ~f~ c", "(a..<b) ~f~ c"),
        ("((a ~f~ b)) == q", "a ~f~ b == q"),
        ("(a ~f~ b) >< g", "a ~f~ b >< g"),
        ("a ~f~ (b else c)", "a ~f~ (b else c)"),
        ("a ~f~ (b == c)", "a ~f~ (b == c)"),
        ("(x -> x) ~f~ b", "(x -> x) ~f~ b"),
        ("f(a ~g~ b, c)", "f(a ~g~ b, c)"),
    ] {
        assert_eq!(printed(written), want, "{written}");
    }
}

/// Leaves and operators of the random expressions.
const LEAVES: [&str; 4] = ["a", "b", "c", "1"];
const BINARY: [&str; 7] = ["+", "-", "*", "/", "^", "div", "++"];
const LOOSER: [&str; 5] = ["==", "<", "&&", "else", "..<"];
const INFIX: [&str; 2] = ["~f~", "~g~"];

/// A random expression of depth at most `depth`, with every compound part in parentheses.
fn expr(rng: &mut Rng, depth: usize) -> String {
    if depth == 0 || rng.below(4) == 0 {
        return rng.pick(&LEAVES).to_string();
    }
    let kid = |rng: &mut Rng| expr(rng, depth - 1);
    match rng.below(6) {
        0 => format!("({}{})", rng.pick(&["-", "!"]), kid(rng)),
        1 => format!("({} {} {})", kid(rng), rng.pick(&BINARY), kid(rng)),
        2 => format!("({} {} {})", kid(rng), rng.pick(&LOOSER), kid(rng)),
        3 => format!("({}).len", kid(rng)),
        _ => format!("({} {} {})", kid(rng), rng.pick(&INFIX), kid(rng)),
    }
}

/// The spans of each pair of parentheses in `text` that holds an expression: not those of a
/// call's arguments, `f(...)`.
fn groups(text: &str) -> Vec<(usize, usize)> {
    let (mut open, mut out) = (Vec::new(), Vec::new());
    for (i, c) in text.char_indices() {
        match c {
            '(' => open.push(i),
            ')' => out.push((open.pop().unwrap(), i)),
            _ => {}
        }
    }
    out
}

/// Random expressions printed: the printed text means the same tree, and each pair of
/// parentheses in it is needed. A text the parser or the builder rejects is left out; each
/// case is also covered by a written program in `printed_back_infix`, so no assertion counts the
/// draws kept.
#[test]
fn round_trip_and_minimal_parentheses() {
    let (mut rng, seed) = Rng::fresh("l02_06c round_trip_and_minimal_parentheses");
    for _ in 0..400 {
        let e = expr(&mut rng, 4);
        let tree = sx(&e);
        if !tree.starts_with('(') && !LEAVES.contains(&tree.as_str()) {
            continue;
        }
        let p = printed(&e);
        assert_eq!(sx(&p), tree, "seed {seed}: {e} printed as {p}");
        for (o, c) in groups(&p) {
            // A number before `.` keeps its parentheses, so that `(1).len` does not read as a
            // decimal (format.rs, the operand of a call, index or member).
            if p[o + 1..c].bytes().all(|b| b.is_ascii_digit()) && p[c + 1..].starts_with('.') {
                continue;
            }
            let fewer = format!("{}{}{}", &p[..o], &p[o + 1..c], &p[c + 1..]);
            assert_ne!(
                sx(&fewer),
                tree,
                "seed {seed}: {e} printed as {p}; the parentheses at {o} are not needed"
            );
        }
    }
}
