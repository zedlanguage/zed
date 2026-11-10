//! A name used above its definition (DESIGN.md sec:lexical): each repair the rejection offers,
//! applied as its text says, makes the program check.

use super::{rejected, steps};
use zedc::run::load;

/// The text between the first two backticks of `s` after `from`, and the rest after it.
fn quoted<'a>(s: &'a str, from: &str) -> (&'a str, &'a str) {
    let at = s.find(from).unwrap_or_else(|| panic!("no `{from}` in {s}"));
    let rest = &s[at + from.len()..];
    let open = rest.find('`').unwrap() + 1;
    let close = open + rest[open..].find('`').unwrap();
    (&rest[open..close], &rest[close + 1..])
}

/// The line of `lines` (from 1) whose trimmed text is `text`, which is there once.
fn line_of(lines: &[&str], text: &str) -> usize {
    let found: Vec<usize> = (0..lines.len())
        .filter(|&i| lines[i].trim() == text)
        .collect();
    assert_eq!(found.len(), 1, "`{text}` in {lines:?}");
    found[0] + 1
}

/// The number that follows `word ` in `s`.
fn number_after(s: &str, word: &str) -> usize {
    let at = s.find(word).unwrap_or_else(|| panic!("no `{word}` in {s}")) + word.len();
    s[at..]
        .split(|c: char| !c.is_ascii_digit())
        .find(|t| !t.is_empty())
        .unwrap()
        .parse()
        .unwrap()
}

/// `src` with the repair `repair` applied as its text says.
fn apply(src: &str, repair: &str) -> String {
    let lines: Vec<&str> = src.lines().collect();
    let moved_lines = |first: usize, last: usize, before: usize| {
        // Lines `first..=last` go above line `before`, which is above them.
        assert!(before < first, "{repair}");
        let mut out: Vec<&str> = lines[..before - 1].to_vec();
        out.extend(&lines[first - 1..last]);
        out.extend(&lines[before - 1..first - 1]);
        out.extend(&lines[last..]);
        out.join("\n") + "\n"
    };
    if repair.contains("out of the block to the top level") {
        let (s, rest) = quoted(repair, "move ");
        let (d, _) = quoted(rest, "and ");
        let (ls, ld) = (line_of(&lines, s), line_of(&lines, d));
        let mut out = vec![s, d];
        out.extend(
            lines
                .iter()
                .enumerate()
                .filter(|&(i, _)| i + 1 != ls && i + 1 != ld)
                .map(|(_, l)| *l),
        );
        return out.join("\n") + "\n";
    }
    if repair.contains(" in front of ") {
        let (moved, rest) = quoted(repair, "move ");
        let (user, _) = quoted(rest, "in front of ");
        let without = src.replacen(&format!(", {moved}"), "", 1);
        assert_ne!(without, src, "{repair}");
        return without.replacen(user, &format!("{moved}, {user}"), 1);
    }
    let before = number_after(repair, "above line");
    if repair.starts_with("repair: move lines ") {
        let first = number_after(repair, "move lines");
        let last = number_after(repair, " to");
        moved_lines(first, last, before)
    } else {
        let (moved, _) = quoted(repair, "move ");
        let at = line_of(&lines, moved);
        moved_lines(at, at, before)
    }
}

#[test]
fn each_offered_repair_applied_makes_the_program_check() {
    let main = "main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- String(total(n: 3));\n}\n";
    let cases = [
        // A block binding used on the line above.
        "total(n: int) {\n  a = b + 1;\n  b = n * 2;\n  return a;\n}\n",
        // A use in a statement over two lines.
        "total(n: int) {\n  a = 1 +\n    b;\n  b = n * 2;\n  return a;\n}\n",
        // A definition over two lines.
        "total(n: int) {\n  a = b + 1;\n  b = n *\n    2;\n  return a;\n}\n",
        // A parameter default naming a later parameter.
        "total(n: int, k: int = m, m: int = 2) {\n  return n + k + m;\n}\n",
    ];
    for unit in cases {
        let src = format!("{unit}{main}");
        let out = rejected(&src);
        let repairs: Vec<&str> = steps(&out)
            .into_iter()
            .filter(|s| s.starts_with("repair: "))
            .collect();
        assert_eq!(repairs.len(), 1, "{out}");
        let fixed = apply(&src, repairs[0]);
        load(fixed.as_bytes()).unwrap_or_else(|e| panic!("{fixed}\n{e}"));
    }
}

#[test]
fn functions_that_call_each_other_are_moved_to_the_top_level() {
    // At the top level the two may name each other; the only error left is that this zedc
    // does not compile recursion yet (DESIGN.md L1: recursion is a later form).
    for pair in [
        "  odd = (n) -> if n == 0 { false } else { even(n - 1) };\n  \
         even = (n) -> if n == 0 { true } else { odd(n - 1) };\n",
        "  odd(n) = if n == 0 { false } else { even(n - 1) };\n  \
         even(n) = if n == 0 { true } else { odd(n - 1) };\n",
    ] {
        let src = format!(
            "main(stdin: Lines) -> (stdout: Lines) {{\n{pair}  stdout <- String(even(4));\n}}\n"
        );
        let out = rejected(&src);
        let repairs: Vec<&str> = steps(&out)
            .into_iter()
            .filter(|s| s.starts_with("repair: "))
            .collect();
        assert_eq!(repairs.len(), 1, "{out}");
        assert!(
            repairs[0].starts_with("repair: `odd` and `even` call each other"),
            "{out}"
        );
        let fixed = apply(&src, repairs[0]);
        let after = rejected(&fixed);
        let heads: Vec<&str> = after.lines().filter(|l| !l.starts_with(' ')).collect();
        assert_eq!(heads.len(), 1, "{after}");
        assert!(
            heads[0].contains("defined in terms of each other, which is recursion"),
            "{after}"
        );
    }
}

#[test]
fn a_function_that_reads_a_value_of_the_block_is_not_offered_the_top_level() {
    // `odd` reads `k`, which the block binds, so it cannot leave the block.
    let src = "main(stdin: Lines) -> (stdout: Lines) {\n  k = 0;\n  \
               odd = (n) -> if n == k { false } else { even(n - 1) };\n  \
               even = (n) -> if n == k { true } else { odd(n - 1) };\n  \
               stdout <- String(even(4));\n}\n";
    let out = rejected(src);
    assert!(out.contains("above its definition"), "{out}");
    assert!(!out.contains("repair:"), "{out}");
}
