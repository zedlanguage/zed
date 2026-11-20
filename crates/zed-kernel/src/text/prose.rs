//! Words of a message's sentences that every crate writes the same way: a list joined as a
//! sentence lists it, and a count with its noun.

use std::fmt::Display;

/// `items` joined as a sentence lists them, with `word` ("and", "or") before the last: `a`,
/// `a and b`, `a, b and c`, and nothing for no items. There is no comma before `word`, as in
/// every message of zedc (the copies this replaced all wrote it so; one doc promised `, and`
/// and its code wrote ` and`). O(the length of the result).
pub fn joined(items: &[impl AsRef<str>], word: &str) -> String {
    let mut out = String::new();
    for (i, item) in items.iter().enumerate() {
        match i {
            0 => {}
            _ if i + 1 == items.len() => {
                out.push(' ');
                out.push_str(word);
                out.push(' ');
            }
            _ => out.push_str(", "),
        }
        out.push_str(item.as_ref());
    }
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
        }
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
