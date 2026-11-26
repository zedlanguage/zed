//! Words of a message's sentences that every crate writes the same way: a list joined as a
//! sentence lists it, a count with its noun, a number in groups of three digits, and code
//! quoted on one line.

use std::fmt::{self, Display, Write as _};

/// `items` joined as a sentence lists them, with `word` ("and", "or") before the last: `a`,
/// `a and b`, `a, b and c`, and nothing for no items. There is no comma before `word`, as in
/// every message of zedc (the copies this replaced all wrote it so; one doc promised `, and`
/// and its code wrote ` and`). O(the length of the result).
pub fn joined(items: &[impl AsRef<str>], word: &str) -> String {
    let mut out = String::new();
    // Writing to a `String` cannot fail.
    let _ = joined_into(&mut out, items, word, |out, item| {
        out.write_str(item.as_ref())
    });
    out
}

/// [`joined`]'s list written straight to `f`, each item by `item`: for a message written to a
/// `Formatter`, or whose items are not strings yet. The separators are [`joined`]'s.
pub fn joined_into<W: fmt::Write + ?Sized, T>(
    f: &mut W,
    items: impl IntoIterator<Item = T, IntoIter: ExactSizeIterator>,
    word: &str,
    mut item: impl FnMut(&mut W, T) -> fmt::Result,
) -> fmt::Result {
    let items = items.into_iter();
    let n = items.len();
    for (i, x) in items.enumerate() {
        match i {
            0 => {}
            _ if i + 1 == n => write!(f, " {word} ")?,
            _ => f.write_str(", ")?,
        }
        item(f, x)?;
    }
    Ok(())
}

/// `items`, each in backquotes, joined by [`joined`]: `` `a`, `b` and `c` ``.
pub fn code_list<T: Display>(
    items: impl IntoIterator<Item = T, IntoIter: ExactSizeIterator>,
    word: &str,
) -> String {
    let mut out = String::new();
    // Writing to a `String` cannot fail.
    let _ = joined_into(&mut out, items, word, |out, item| write!(out, "`{item}`"));
    out
}

/// `items` joined with "and": `a, b and c` ([`joined`]).
pub fn and_list(items: &[impl AsRef<str>]) -> String {
    joined(items, "and")
}

/// `items` joined with "or": `a, b or c` ([`joined`]).
pub fn or_list(items: &[impl AsRef<str>]) -> String {
    joined(items, "or")
}

/// `n` and `thing`, with an `s` for a count other than one: `1 byte`, `0 bytes`, `2 bytes`.
pub fn counted<N: Display + PartialEq + From<u8>>(n: N, thing: &str) -> String {
    let s = plural(&n);
    format!("{n} {thing}{s}")
}

/// `n` with a comma between each group of three digits: `-1,000`, `999`, `1,000,000`.
/// O(digits).
pub fn grouped(n: i128) -> String {
    let d = n.unsigned_abs().to_string();
    let mut s = String::new();
    for (i, ch) in d.chars().enumerate() {
        if i > 0 && (d.len() - i).is_multiple_of(3) {
            s.push(',');
        }
        s.push(ch);
    }
    if n < 0 { format!("-{s}") } else { s }
}

/// `text` as a message quotes code that may span lines: its first line, trailing spaces cut,
/// and ` …`, when more follows the line; else `text` itself. The line ends where `str::lines`
/// ends it, at `\n` or `\r\n`. O(the first line).
pub fn first_line(text: &str) -> std::borrow::Cow<'_, str> {
    match text.lines().next() {
        Some(first) if first.len() < text.len() => format!("{} …", first.trim_end()).into(),
        _ => text.into(),
    }
}

/// `text` where it is on one line, holding no `\n`, for a message that quotes code inline; else
/// `None`, and the message words it without the code. O(the length of `text`).
pub fn one_line_only(text: &str) -> Option<&str> {
    (!text.contains('\n')).then_some(text)
}

/// The ordinal of the place `i`, counted from 0: `first` to `tenth` in words, then `11th`,
/// `12th`, `21st`, `22nd`, `23rd`, `111th`. The suffix follows the last digit, except for the
/// teens 11, 12 and 13, which take `th` (so `n % 100` is tested beside `n % 10`). O(1) for
/// the word, O(digits) for a number.
pub fn ordinal(i: usize) -> String {
    const WORDS: [&str; 10] = [
        "first", "second", "third", "fourth", "fifth", "sixth", "seventh", "eighth", "ninth",
        "tenth",
    ];
    match WORDS.get(i) {
        Some(w) => (*w).to_string(),
        None => {
            let n = i + 1;
            let suffix = match (n % 10, n % 100) {
                (1, r) if r != 11 => "st",
                (2, r) if r != 12 => "nd",
                (3, r) if r != 13 => "rd",
                _ => "th",
            };
            format!("{n}{suffix}")
        }
    }
}

/// `s` for a count `n` other than one, the ending of a regular plural noun.
pub fn plural<N: PartialEq + From<u8>>(n: &N) -> &'static str {
    if *n == N::from(1) { "" } else { "s" }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_list_has_no_comma_before_its_last_word() {
        let none: [&str; 0] = [];
        assert_eq!(and_list(&none), "");
        assert_eq!(and_list(&["a"]), "a");
        assert_eq!(and_list(&["a", "b"]), "a and b");
        assert_eq!(or_list(&["a", "b", "c"]), "a, b or c");
        assert_eq!(joined(&["a", "b", "c", "d"], "and"), "a, b, c and d");
    }

    #[test]
    fn an_ordinal_is_a_word_to_ten_then_a_number_with_its_suffix() {
        let got: Vec<String> = [0, 1, 2, 9, 10, 11, 12, 20, 21, 22, 110, 111, 112, 120]
            .into_iter()
            .map(ordinal)
            .collect();
        let want = [
            "first", "second", "third", "tenth", "11th", "12th", "13th", "21st", "22nd", "23rd",
            "111th", "112th", "113th", "121st",
        ];
        assert_eq!(got, want);
    }

    #[test]
    fn a_count_other_than_one_takes_an_s() {
        assert_eq!(counted(0u64, "byte"), "0 bytes");
        assert_eq!(counted(1usize, "byte"), "1 byte");
        assert_eq!(counted(2u32, "byte"), "2 bytes");
        assert_eq!(plural(&1usize), "");
        assert_eq!(plural(&0usize), "s");
        assert_eq!(plural(&2u64), "s");
    }

    /// `items` listed by the rule read directly (TEST-dry-shared-units): the items with `", "`
    /// between them, the last separator replaced by `" {word} "`. With `oxford` true the last
    /// separator is `", {word} "`, the negative control's mistake.
    fn naive_joined(items: &[String], word: &str, oxford: bool) -> String {
        match items {
            [] => String::new(),
            [one] => one.clone(),
            [rest @ .., last] => {
                let comma = if oxford && rest.len() > 1 { "," } else { "" };
                format!("{}{comma} {word} {last}", rest.join(", "))
            }
        }
    }

    /// Random lists of up to five items, among them the empty item, an item holding a comma
    /// or the word itself, and one beyond ASCII.
    fn random_lists(name: &str) -> Vec<Vec<String>> {
        let (mut rng, _) = crate::seed::Rng::fresh(name);
        let words = ["a", "", "b c", "x, y", "and", "é"];
        (0..2000)
            .map(|_| {
                let n = rng.below(6);
                (0..n).map(|_| rng.pick(&words).to_string()).collect()
            })
            .collect()
    }

    #[test]
    fn lists_agree_with_the_rule_read_directly() {
        for items in random_lists("lists_agree_with_the_rule_read_directly") {
            for word in ["and", "or", ""] {
                assert_eq!(
                    joined(&items, word),
                    naive_joined(&items, word, false),
                    "{items:?}"
                );
            }
            assert_eq!(and_list(&items), joined(&items, "and"));
            assert_eq!(or_list(&items), joined(&items, "or"));
            let quoted: Vec<String> = items.iter().map(|x| format!("`{x}`")).collect();
            assert_eq!(
                code_list(&items, "or"),
                naive_joined(&quoted, "or", false),
                "{items:?}"
            );
        }
    }

    /// The first line against the copies it replaced (`split_once('\n')`, then the cut first
    /// line and ` …`), on texts with each kind of line end, trailing spaces and none.
    #[test]
    fn a_first_line_is_the_text_up_to_its_first_line_end() {
        let split = |t: &str| match t.split_once('\n') {
            Some((first, _)) => format!("{} …", first.trim_end()),
            None => t.to_string(),
        };
        let (mut rng, _) =
            crate::seed::Rng::fresh("a_first_line_is_the_text_up_to_its_first_line_end");
        let pieces = ["a", " ", "\n", "\r\n", "é", "{ x }", ""];
        for _ in 0..2000 {
            let n = rng.below(6);
            let text: String = (0..n).map(|_| rng.pick(&pieces)).collect();
            assert_eq!(first_line(&text), split(&text), "{text:?}");
        }
        assert_eq!(first_line("if x {\n  y\n}"), "if x { …");
        assert_eq!(first_line("one line "), "one line ");
        assert_eq!(first_line(""), "");
    }

    /// [`grouped`] against the number read back with its commas taken out, and each group
    /// after the first three digits long, on random numbers of every size and at the ends of
    /// `i128`.
    #[test]
    fn a_grouped_number_reads_back_with_groups_of_three() {
        let (mut rng, _) = crate::seed::Rng::fresh("a_grouped_number_reads_back");
        let small = [0, 1, -1, 999, 1000, -1000, 999_999, 1_000_000];
        let ends = small.into_iter().chain([i128::MAX, i128::MIN]);
        // 128 random bits as an `i128`, shifted right by 0 to 127 places with its sign kept:
        // numbers of every length, of both signs.
        let random: Vec<i128> = (0..2000)
            .map(|_| {
                let bits = (u128::from(rng.next_u64()) << 64) | u128::from(rng.next_u64());
                (bits as i128) >> rng.below(128)
            })
            .collect();
        for n in ends.chain(random) {
            let s = grouped(n);
            assert_eq!(s.replace(',', "").parse::<i128>(), Ok(n), "{s}");
            let groups: Vec<&str> = s.trim_start_matches('-').split(',').collect();
            assert!((1..=3).contains(&groups[0].len()), "{s}");
            assert!(groups[1..].iter().all(|g| g.len() == 3), "{s}");
        }
        assert_eq!(grouped(-1000), "-1,000");
        assert_eq!(grouped(1_234_567), "1,234,567");
    }

    #[test]
    fn only_a_text_with_no_newline_is_on_one_line() {
        assert_eq!(one_line_only("f(x)"), Some("f(x)"));
        assert_eq!(one_line_only(""), Some(""));
        assert_eq!(one_line_only("f(\n x)"), None);
        assert_eq!(one_line_only("\n"), None);
    }

    #[test]
    fn a_code_list_puts_each_item_in_backquotes() {
        assert_eq!(code_list([0u8; 0], "and"), "");
        assert_eq!(code_list(["x"], "and"), "`x`");
        assert_eq!(code_list([1, 2, 3], "or"), "`1`, `2` or `3`");
    }

    #[test]
    fn a_list_written_to_a_formatter_is_the_joined_list() {
        let shown = fmt::from_fn(|f| joined_into(f, [1, 2, 3], "and", |f, n| write!(f, "<{n}>")));
        assert_eq!(shown.to_string(), "<1>, <2> and <3>");
    }

    /// Negative control: a list with a comma before its last word differs on some list, so
    /// the property test above can fail.
    #[test]
    fn a_comma_before_the_last_word_is_caught() {
        let lists = random_lists("a_comma_before_the_last_word_is_caught");
        assert!(
            lists
                .iter()
                .any(|l| joined(l, "and") != naive_joined(l, "and", true))
        );
    }

    #[test]
    fn a_count_at_the_ends_of_its_type_takes_an_s() {
        assert_eq!(counted(u64::MAX, "byte"), format!("{} bytes", u64::MAX));
        assert_eq!(counted(-1i64, "step"), "-1 steps");
        assert_eq!(counted(1i16, "step"), "1 step");
        assert_eq!(counted(0u8, "step"), "0 steps");
        assert_eq!(plural(&u128::MAX), "s");
    }
}
