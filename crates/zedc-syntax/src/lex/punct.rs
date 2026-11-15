//! Keywords, atoms, annotations, and operators (step L1.6):
//!
//! ```peg
//! AtomLit  = '#' Name
//! AnnotLit = '@' Name
//! Keyword  = KeywordWord !NameChar
//! Operator = '->?' | '->' | '...' | '..<' | '..=' | '..' | … | '#_' | [+\-*/<>=!&|\\:,;.?()\[\]{}]
//! ```
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

/// The keyword that is the whole of `word`, a name, if it is one.
pub(super) fn keyword(word: &str) -> Option<&'static str> {
    KEYWORDS.iter().copied().find(|&k| k == word)
}

/// The operator starting at byte `pos` of `text`, if one starts there.
///
/// Complexity tradeoff: the naive scan calls `starts_with` (a `memcmp` call) on each of the 42
/// operators; comparing the first byte before the rest leaves at most five full comparisons
/// per position (those starting with `.`). Both are O(|OPERATORS|) per position; a 256-entry
/// table would make it O(1) but must be kept in step with `OPERATORS`. Measured on the inputs
/// of the many-bounded-variables bench (row FAIL-bench-bounded-or-free-time), 5.6 MB of printed
/// types: 16% fewer instructions to read them (lexed three times, parsed, resolved).
pub(super) fn operator(text: &str, pos: usize) -> Option<&'static str> {
    let rest = &text.as_bytes()[pos..];
    let first = *rest.first()?;
    OPERATORS
        .iter()
        .copied()
        .find(|op| op.as_bytes()[0] == first && rest.starts_with(op.as_bytes()))
}
