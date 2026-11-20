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
}
