//! The lexer's output and its errors: tokens, their spans and kinds, the parts of a string
//! literal, and why lexing stopped. The lexer (`super`) and its readers of comments, numbers
//! and strings all make these, so they are kept in a file below all of them.

use std::fmt;
use std::sync::Arc;

use unicode_script::{Script, UnicodeScript};
use unicode_width::UnicodeWidthChar;
use zed_kernel::num::{FloatFormat, TooLarge, bytes_of};
use zedc_base::terminal;

/// A number literal's digits, without `_`: one copy of the source text, made in memory asked
/// for first, and shared by the token and the syntax tree, which never copy it again.
pub type Digits = Arc<String>;

/// A byte range of the loaded text.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    /// The first byte.
    pub start: usize,
    /// One past the last byte.
    pub end: usize,
}

/// A token's kind and the value it carries.
#[derive(Debug, PartialEq, Eq)]
pub enum Tok {
    /// A name, with its trailing `'` when it has one (`x'`).
    Name(String),
    /// The discard wildcard `_`.
    Wildcard,
    /// An integer: its base (2, 8, 10 or 16) and its digits, without `_`.
    Int {
        /// The base.
        radix: u32,
        /// The digits.
        digits: Digits,
    },
    /// A decimal literal (`1.5e-3`, `0.1f64`).
    Float {
        /// Its decimal text, without `_` and the suffix.
        digits: Digits,
        /// The format its suffix names, `f32` or `f64`, which it is forced to; none without.
        forced: Option<FloatFormat>,
    },
    /// An exact rational, as its decimal text without `_` and the `r` (`0.1`).
    Rat(Digits),
    /// A string: its text and its holes, in order, never two text parts in a row.
    Str(Vec<Part>),
    /// An atom `#name`, without the `#`.
    Atom(String),
    /// An annotation `@name`, without the `@`.
    Annot(String),
    /// A keyword.
    Keyword(&'static str),
    /// An operator or punctuation mark.
    Op(&'static str),
}

/// A doc comment: its text after `///` and one space, and its span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Doc {
    /// The text.
    pub text: String,
    /// The span, from the first `/` to the end of the line.
    pub span: Span,
}

/// A part of a string literal.
pub enum Part {
    /// Text, with its escapes decoded and, in a `"""` string, its indentation stripped, shared
    /// with the syntax tree ([`crate::ast::StrPart::Text`]), which copies none of it.
    Text(Arc<String>),
    /// A `${…}` hole: the tokens of its expression, and the span of the whole hole.
    Hole {
        /// The tokens between `${` and `}`.
        tokens: Vec<Token>,
        /// The span from `$` to `}`.
        span: Span,
    },
}

/// A token and its span.
#[derive(Debug, PartialEq, Eq)]
pub struct Token {
    /// The kind.
    pub tok: Tok,
    /// The span.
    pub span: Span,
}

/// Why lexing stopped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    /// A character that starts no token.
    Unexpected(char),
    /// A word that is a name but for a character beyond ASCII (`café`, `#pаypal`): the word as
    /// written, with its `#` or `@` and its `'` if it has them, and the ASCII name offered for
    /// it, written likewise, if there is one ([`super::name::ascii_name`]).
    NonAsciiName {
        /// The word.
        word: String,
        /// The ASCII name offered.
        repair: Option<String>,
    },
    /// A malformed number, and what is wrong with it.
    BadNumber(String),
    /// A malformed string, and what is wrong with it.
    BadString(String),
    /// A block comment that is not closed.
    BadComment(String),
    /// A number literal whose digits the system refused the memory to copy.
    Unread(TooLarge),
}

/// A lexical error and its span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    /// The kind.
    pub kind: ErrorKind,
    /// The span.
    pub span: Span,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            ErrorKind::Unexpected(c) => f.write_str(&unexpected(*c)),
            ErrorKind::BadNumber(why) | ErrorKind::BadString(why) | ErrorKind::BadComment(why) => {
                write!(f, "{why}")
            }
            ErrorKind::Unread(r) => write!(f, "{}", unread_literal(r)),
            ErrorKind::NonAsciiName { word, repair } => f.write_str(&non_ascii(word, repair)),
        }
    }
}

/// The message for `word`, which is a name but for a character beyond ASCII, with the ASCII
/// name `repair` offered for it, if there is one. The first such character is named, by its
/// code point too, since it may look like an ASCII letter (Cyrillic `а`).
fn non_ascii(word: &str, repair: &Option<String>) -> String {
    let c = word
        .chars()
        .find(|c| !c.is_ascii())
        .expect("the word holds a character beyond ASCII");
    let code = c as u32;
    // A combining mark shows on the letter before it in `word`, but not alone.
    let which = if may_not_show(c) {
        format!("the character U+{code:04X}, which may not show on screen,")
    } else {
        format!("`{c}` (U+{code:04X})")
    };
    let what = match word.chars().next() {
        Some('#') => "atom",
        Some('@') => "annotation",
        _ => "name",
    };
    let head = format!("`{word}` is no {what}: {which} is not ASCII.");
    match repair {
        Some(r) => format!("{head} Try `{r}` instead."),
        None => format!("{head} Write the {what} in ASCII letters, digits and `_`."),
    }
}

/// The message for the character `c`, which starts no token where it stands. `#` and `@`
/// start an atom and an annotation only before a name, and `'` ends a name, so each of those
/// has its own text.
fn unexpected(c: char) -> String {
    match c {
        '#' => "`#` starts an atom, and the atom's name must follow it at once, as in `#none`. \
                Write the name right after the `#`, with no space between."
            .into(),
        '@' => "`@` starts an annotation, and the annotation's name must follow it at once, as \
                in `@test`. Write the name right after the `@`, with no space between."
            .into(),
        '\'' => "`'` stands only right after a name, once, as in `x'`, and starts nothing by \
                 itself. Remove this `'`, or write it right after the name it marks."
            .into(),
        _ => {
            let code = c as u32;
            // A character that may not show on screen ([`may_not_show`]) is named by its code
            // point and written in its escape form, never as itself: printed as itself it shows
            // as nothing or as blank space, and a bidirectional control such as U+202E reorders
            // the rest of the reader's terminal line (DESIGN.md sec:lexical, sec:diagnostics).
            if may_not_show(c) {
                return format!(
                    "the character U+{code:04X}, which may not show on screen, starts no name, \
                     number, operator or other part of a Zed program. Remove it, or, if it is \
                     meant as text, write it inside a string, as `\"\\u{{{code:X}}}\"`."
                );
            }
            let quoted = match c {
                '`' => "`` ` ``".to_string(),
                _ => format!("`{c}`"),
            };
            let text = match c {
                '\\' => "`\"\\\\\"`".to_string(),
                '`' => "`` \"`\" ``".to_string(),
                _ => format!("`\"{c}\"`"),
            };
            format!(
                "the character {quoted} (U+{code:04X}) starts no name, number, operator or \
                 other part of a Zed program. Remove it, or, if it is meant as text, write it \
                 inside a string, as {text}."
            )
        }
    }
}

/// The Unicode version of every character table the lexer reads (DESIGN.md step S.1c): the
/// tables below, and those of unicode-script (scripts), unicode-normalization (NFC, NFKD and
/// combining marks), unicode-security (the confusables of UTS #39) and unicode-width. Cargo.lock
/// pins each crate; a crate of another Unicode version does not compile. any_ascii, whose
/// tables are no Unicode data, is pinned by its version alone.
pub const UNICODE_VERSION: (u8, u8, u8) = (18, 0, 0);

const _: () = {
    let v = UNICODE_VERSION;
    let wide = (v.0 as u64, v.1 as u64, v.2 as u64);
    let (s, c, n, w) = (
        unicode_script::UNICODE_VERSION,
        unicode_security::UNICODE_VERSION,
        unicode_normalization::UNICODE_VERSION,
        unicode_width::UNICODE_VERSION,
    );
    assert!(s.0 == wide.0 && s.1 == wide.1 && s.2 == wide.2);
    assert!(c.0 == wide.0 && c.1 == wide.1 && c.2 == wide.2);
    assert!(n.0 == v.0 && n.1 == v.1 && n.2 == v.2);
    assert!(w.0 == v.0 && w.1 == v.1 && w.2 == v.2);
};

/// The characters with the Unicode property Default_Ignorable_Code_Point, as sorted, disjoint,
/// inclusive ranges with a gap between each two: DerivedCoreProperties.txt of Unicode 18.0
/// ([`UNICODE_VERSION`]), with its adjacent ranges joined. The test
/// `the_blank_characters_are_the_default_ignorable_code_points_and_three_more` compares this
/// table with that file for every code point.
const DEFAULT_IGNORABLE: [(char, char); 17] = [
    ('\u{AD}', '\u{AD}'),
    ('\u{34F}', '\u{34F}'),
    ('\u{61C}', '\u{61C}'),
    ('\u{115F}', '\u{1160}'),
    ('\u{17B4}', '\u{17B5}'),
    ('\u{180B}', '\u{180F}'),
    ('\u{200B}', '\u{200F}'),
    ('\u{202A}', '\u{202E}'),
    ('\u{2060}', '\u{206F}'),
    ('\u{3164}', '\u{3164}'),
    ('\u{FE00}', '\u{FE0F}'),
    ('\u{FEFF}', '\u{FEFF}'),
    ('\u{FFA0}', '\u{FFA0}'),
    ('\u{FFF0}', '\u{FFF8}'),
    ('\u{1BCA0}', '\u{1BCA3}'),
    ('\u{1D173}', '\u{1D17A}'),
    ('\u{E0000}', '\u{E0FFF}'),
];

/// The characters that lack the property Default_Ignorable_Code_Point but whose glyph is blank:
/// in Unicode 18.0 these three, by their names and general categories in UnicodeData.txt (two
/// Lo letters and one Mn mark): U+13441 EGYPTIAN HIEROGLYPH FULL BLANK, U+13442 EGYPTIAN
/// HIEROGLYPH HALF BLANK and U+16FE4 KHITAN SMALL SCRIPT FILLER.
const BLANK: [char; 3] = ['\u{13441}', '\u{13442}', '\u{16FE4}'];

/// Whether `c` has the Unicode property Default_Ignorable_Code_Point.
pub fn is_default_ignorable(c: char) -> bool {
    // Complexity tradeoff: the naive form scans the r = 17 ranges, O(r) per character; this is
    // a binary search, O(log r), and a character below U+00AD, which every ASCII character is,
    // is answered by one comparison. Nothing is given up: the answer is exact for every code
    // point, and the table costs 136 bytes.
    c >= '\u{AD}' && in_ranges(&DEFAULT_IGNORABLE, c)
}

/// Whether `c` shows as nothing or as blank space: a Default_Ignorable_Code_Point character
/// (a zero width joiner, a variation selector, a Hangul filler) or one of the three blank
/// characters. A word beyond ASCII never holds one ([`super::name::ascii_name`]), so it keeps
/// the message of a character that may not show.
pub fn is_blank(c: char) -> bool {
    // Complexity tradeoff: the table search of `is_default_ignorable`, O(log r), and three
    // comparisons for the blank characters.
    is_default_ignorable(c) || BLANK.contains(&c)
}

/// Whether `c` lies in one of the sorted, disjoint, inclusive `ranges`: a binary search,
/// O(log r) for r ranges.
fn in_ranges(ranges: &[(char, char)], c: char) -> bool {
    ranges
        .binary_search_by(|&(lo, hi)| {
            if hi < c {
                std::cmp::Ordering::Less
            } else if lo > c {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Equal
            }
        })
        .is_ok()
}

/// The characters of the general category Cf (format): DerivedGeneralCategory.txt of Unicode
/// 18.0 ([`UNICODE_VERSION`]), as sorted, disjoint, inclusive ranges. The test
/// `the_format_table_is_the_general_category_cf` compares it with that file for every code point.
const FORMAT: [(char, char); 21] = [
    ('\u{AD}', '\u{AD}'),
    ('\u{600}', '\u{605}'),
    ('\u{61C}', '\u{61C}'),
    ('\u{6DD}', '\u{6DD}'),
    ('\u{70F}', '\u{70F}'),
    ('\u{890}', '\u{891}'),
    ('\u{8E2}', '\u{8E2}'),
    ('\u{180E}', '\u{180E}'),
    ('\u{200B}', '\u{200F}'),
    ('\u{202A}', '\u{202E}'),
    ('\u{2060}', '\u{2064}'),
    ('\u{2066}', '\u{206F}'),
    ('\u{FEFF}', '\u{FEFF}'),
    ('\u{FFF9}', '\u{FFFB}'),
    ('\u{110BD}', '\u{110BD}'),
    ('\u{110CD}', '\u{110CD}'),
    ('\u{13430}', '\u{1343F}'),
    ('\u{1BCA0}', '\u{1BCA3}'),
    ('\u{1D173}', '\u{1D17A}'),
    ('\u{E0001}', '\u{E0001}'),
    ('\u{E0020}', '\u{E007F}'),
];

/// Whether `c` is of the general category Cf (format).
pub fn is_format(c: char) -> bool {
    // Complexity tradeoff: the naive form scans the r = 21 ranges, O(r); this is a binary
    // search, O(log r), with one comparison for a character below U+00AD.
    c >= '\u{AD}' && in_ranges(&FORMAT, c)
}

/// Whether `c` may not show on screen, so that a message names it by its code point and never
/// prints it: a character a diagnostic prints in its escape form ([`terminal::hidden`]: a
/// control, a space other than U+0020, a format character of no width), a combining mark, which
/// at the start of a token has no letter under it, a character of the general categories Cf,
/// Co, Cs or Cn, or one that shows as blank space ([`is_blank`]), such as a Hangul filler, which
/// shows as blank space one or two columns wide. With U+0020, which `Space` takes
/// before any token, these are the general categories Cc, Cf, Zs, Zl, Zp, Co, Cs and Cn, the
/// White_Space characters and those of no width. Co, Cs and Cn are the characters of the script
/// Unknown (UAX #24; in Unicode 18.0 the two sets are equal), so a character assigned after the
/// version of unicode-script's tables is named by its code point too, which loses nothing.
pub fn may_not_show(c: char) -> bool {
    terminal::hidden(c)
        || c.width() == Some(0)
        || is_format(c)
        || c.script() == Script::Unknown
        || is_blank(c)
}

/// The message for a numeric literal whose digits the system refused the memory to read. It
/// does not quote the literal, which may be millions of digits long.
pub fn unread_literal(r: &TooLarge) -> String {
    format!(
        "this literal has so many digits that the system refused the {} bytes of memory zedc \
         asked for to read it. A literal has no size limit, but this machine cannot hold this \
         one's value. Write it with fewer digits.",
        bytes_of(&r.bits)
    )
}

impl Drop for Part {
    /// Frees nested holes from a stack: each level of a string's holes would be a level of the
    /// thread's stack otherwise.
    fn drop(&mut self) {
        let mut stack = Vec::new();
        take_tokens(self, &mut stack);
        while let Some(tokens) = stack.pop() {
            for token in tokens {
                if let Tok::Str(mut parts) = token.tok {
                    for part in &mut parts {
                        take_tokens(part, &mut stack);
                    }
                }
            }
        }
    }
}

/// Moves the tokens of `part`, a hole, onto `stack`.
fn take_tokens(part: &mut Part, stack: &mut Vec<Vec<Token>>) {
    if let Part::Hole { tokens, .. } = part {
        stack.push(std::mem::take(tokens));
    }
}

impl fmt::Debug for Part {
    /// The output of `#[derive(Debug)]`, from a stack, since holes nest.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Show<'a> {
            Put(&'static str),
            Span(Span),
            Part(&'a Part),
            Tokens(&'a [Token]),
            Parts(&'a [Part]),
        }
        let mut stack = vec![Show::Part(self)];
        while let Some(show) = stack.pop() {
            match show {
                Show::Put(s) => f.write_str(s)?,
                Show::Span(s) => write!(f, "{s:?}")?,
                Show::Part(Part::Text(s)) => write!(f, "Text({s:?})")?,
                Show::Part(Part::Hole { tokens, span }) => {
                    f.write_str("Hole { tokens: [")?;
                    stack.extend([Show::Put(" }"), Show::Span(*span)]);
                    stack.extend([Show::Put("], span: "), Show::Tokens(tokens)]);
                }
                Show::Tokens([]) | Show::Parts([]) => {}
                Show::Tokens([first, rest @ ..]) => {
                    if !rest.is_empty() {
                        stack.extend([Show::Tokens(rest), Show::Put(", ")]);
                    }
                    let Tok::Str(parts) = &first.tok else {
                        write!(f, "{first:?}")?;
                        continue;
                    };
                    f.write_str("Token { tok: Str([")?;
                    stack.extend([Show::Put(" }"), Show::Span(first.span)]);
                    stack.extend([Show::Put("]), span: "), Show::Parts(parts)]);
                }
                Show::Parts([first, rest @ ..]) => {
                    if !rest.is_empty() {
                        stack.extend([Show::Parts(rest), Show::Put(", ")]);
                    }
                    stack.push(Show::Part(first));
                }
            }
        }
        Ok(())
    }
}

impl PartialEq for Part {
    /// Compares nested holes from a stack.
    fn eq(&self, other: &Part) -> bool {
        let mut stack = vec![(self, other)];
        while let Some(pair) = stack.pop() {
            let (a, b, x, y) = match pair {
                (Part::Text(a), Part::Text(b)) if a == b => continue,
                (Part::Hole { tokens: a, span: x }, Part::Hole { tokens: b, span: y }) => {
                    (a, b, x, y)
                }
                (Part::Text(_) | Part::Hole { .. }, Part::Text(_) | Part::Hole { .. }) => {
                    return false;
                }
            };
            if x != y || a.len() != b.len() {
                return false;
            }
            for (a, b) in a.iter().zip(b) {
                if a.span != b.span {
                    return false;
                }
                match (&a.tok, &b.tok) {
                    (Tok::Str(p), Tok::Str(q)) if p.len() == q.len() => {
                        stack.extend(p.iter().zip(q));
                    }
                    // At most one is a string, or their lengths differ: this does not nest.
                    (p, q) => {
                        if p != q {
                            return false;
                        }
                    }
                }
            }
        }
        true
    }
}

impl Eq for Part {}
