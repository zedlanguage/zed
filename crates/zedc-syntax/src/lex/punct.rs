//! Keywords, atoms, annotations, and operators (step L1.6): the rules `AtomLit`, `AnnotLit`,
//! `Keyword` and `Operator` of `zed/grammar/lexical.peg`.
//!
//! `where` and `sep` are reserved only by position, so the lexer reads them as names and the
//! parser matches them by their text.

/// The keywords, as the grammar lists them.
pub const KEYWORDS: [&str; 37] = [
    "struct",
    "type",
    "interface",
    "grammar",
    "matching",
    "import",
    "asc",
    "as",
    "into",
    "local",
    "for",
    "initial",
    "in",
    "not",
    "loop",
    "until",
    "while",
    "break",
    "match",
    "if",
    "else",
    "is",
    "positional",
    "without",
    "with",
    "return",
    "test",
    "law",
    "proof",
    "emit",
    "this",
    "desc",
    "div",
    "mod",
    "true",
    "false",
    "unordered",
];

/// The operators, longest first where one is a prefix of another.
pub const OPERATORS: [&str; 42] = [
    "->?", "->", "...", "..<", "..=", "..", "?.", "*.", "^", "++", "<-", "<=", ">=", "><", "==",
    "!=", "&&", "||", "::", "#_", "+", "-", "*", "/", "<", ">", "=", "!", "&", "|", "\\", ":", ",",
    ";", ".", "?", "(", ")", "[", "]", "{", "}",
];

/// For each first byte, a bit for each entry of `words` that starts with it: bit `i` stands for
/// `words[i]`, so the entries are tried in their order. Made at compile time from the list
/// itself, so it cannot fall out of step with it.
const fn by_first_byte<const N: usize>(words: [&str; N]) -> [u64; 256] {
    assert!(N <= 64, "a list of at most 64 words");
    let mut table = [0u64; 256];
    let mut i = 0;
    while i < N {
        table[words[i].as_bytes()[0] as usize] |= 1 << i;
        i += 1;
    }
    table
}

/// The keywords by first byte (`by_first_byte`).
static KEYWORDS_BY_FIRST: [u64; 256] = by_first_byte(KEYWORDS);

/// The operators by first byte (`by_first_byte`).
static OPERATORS_BY_FIRST: [u64; 256] = by_first_byte(OPERATORS);

/// The keyword that is the whole of `word`, a name, if it is one.
///
/// Complexity tradeoff: the naive scan compares `word` with each of the 37 keywords, a length
/// test and a `memcmp` call for each of the same length. Used: the keywords that start with
/// `word`'s first byte, from a table made at compile time, at most seven (`i`), so a name that
/// starts no keyword costs one load. Both are O(|KEYWORDS|) at worst per name; a perfect hash
/// would be O(1) but must be rebuilt by hand with the list. Measured with row
/// FAIL-bench-setup-parse-constant (see `operator`).
pub(super) fn keyword(word: &str) -> Option<&'static str> {
    let mut bits = KEYWORDS_BY_FIRST[usize::from(*word.as_bytes().first()?)];
    while bits != 0 {
        let k = KEYWORDS[bits.trailing_zeros() as usize];
        if k == word {
            return Some(k);
        }
        bits &= bits - 1;
    }
    None
}

/// The operator starting at byte `pos` of `text`, if one starts there.
///
/// Complexity tradeoff: the naive scan calls `starts_with` (a `memcmp` call) on each of the 42
/// operators. Comparing the first byte before the rest left at most five full comparisons per
/// position (those starting with `.`) but still read the first byte of all 42 (row
/// FAIL-bench-bounded-or-free-time: 16% fewer instructions to read the 5.6 MB of printed types
/// of the many-bounded-variables bench). Used now: the operators that start with that byte,
/// from a table made at compile time from `OPERATORS`, tried longest first as the list orders
/// them. O(1) a position for this list. Row FAIL-bench-setup-parse-constant: the keyword and
/// operator scans were 3.9% of the instructions to read those types.
pub(super) fn operator(text: &str, pos: usize) -> Option<&'static str> {
    let rest = &text.as_bytes()[pos..];
    let mut bits = OPERATORS_BY_FIRST[usize::from(*rest.first()?)];
    while bits != 0 {
        let op = OPERATORS[bits.trailing_zeros() as usize];
        if rest.starts_with(op.as_bytes()) {
            return Some(op);
        }
        bits &= bits - 1;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The lookups by first byte give what a scan of the lists in order gives.
    #[test]
    fn the_tables_by_first_byte_agree_with_a_scan_of_the_lists() {
        for k in KEYWORDS {
            assert_eq!(keyword(k), Some(k));
            assert_eq!(keyword(&format!("{k}x")), None);
            assert_eq!(
                keyword(&k[..k.len() - 1]),
                KEYWORDS.iter().copied().find(|&w| w == &k[..k.len() - 1])
            );
        }
        for w in ["", "x", "Type", "types", "where", "sep", "i"] {
            assert_eq!(keyword(w), None);
        }
        for a in 0..=255u8 {
            for b in [
                b"" as &[u8],
                b">",
                b".",
                b"=",
                b"<",
                b"?",
                b"x",
                b"..",
                b"_",
            ] {
                let mut bytes = vec![a];
                bytes.extend_from_slice(b);
                let Ok(text) = std::str::from_utf8(&bytes) else {
                    continue;
                };
                let scan = OPERATORS.iter().copied().find(|op| text.starts_with(op));
                assert_eq!(operator(text, 0), scan, "{text:?}");
            }
        }
    }
}
