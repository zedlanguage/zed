//! Keywords, atoms, annotations, and operators (step L1.6):
//!
//! ```peg
//! AtomLit  = '#' Name
//! AnnotLit = '@' Name
//! Keyword  = KeywordWord !XID_CONTINUE
//! Operator = '->?' | '->' | '...' | '..<' | '..=' | '..' | … | [+\-*/<>=!&|\\:,;.?()\[\]{}]
//! ```
//!
//! `where` and `sep` are reserved only by position, so the lexer reads them as names and the
//! parser matches them by their text.

/// The keywords, as the grammar lists them.
pub const KEYWORDS: [&str; 36] = [
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
    "mutable",
    "positional",
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
pub const OPERATORS: [&str; 41] = [
    "->?", "->", "...", "..<", "..=", "..", "?.", "*.", "**", "++", "<-", "<=", ">=", "><", "==",
    "!=", "&&", "||", "::", "+", "-", "*", "/", "<", ">", "=", "!", "&", "|", "\\", ":", ",", ";",
    ".", "?", "(", ")", "[", "]", "{", "}",
];

/// The keyword that is the whole of `word`, a name, if it is one.
pub(super) fn keyword(word: &str) -> Option<&'static str> {
    KEYWORDS.iter().copied().find(|&k| k == word)
}

/// The operator starting at byte `pos` of `text`, if one starts there.
pub(super) fn operator(text: &str, pos: usize) -> Option<&'static str> {
    OPERATORS
        .iter()
        .copied()
        .find(|op| text[pos..].starts_with(op))
}
