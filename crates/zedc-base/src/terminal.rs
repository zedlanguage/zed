//! What a terminal shows of a text zedc prints (DESIGN.md sec:diagnostics, "Characters a
//! terminal does not show"). A character of the program's text that a terminal would not show as
//! itself is printed in its Zed escape form `\u{X}`, so a diagnostic shows every character of the
//! source and none can act on the reader's terminal: an ESC from a string can no longer clear the
//! screen, nor U+202E reverse the rest of the line.

use std::fmt;

use unicode_normalization::char::is_combining_mark;
use unicode_width::UnicodeWidthChar;

/// Whether `c` is printed in its escape form: a control character, a space other than U+0020
/// (U+00A0, U+2028, …), or a character of no display width that is not a combining mark (a
/// format character such as U+200B, U+200D, U+FEFF or the bidirectional controls U+202A to
/// U+202E and U+2066 to U+2069). A combining mark is shown on the character before it, so `née`
/// written with U+0301 keeps its accent. The lexer names the characters it refuses by the same
/// test, and names a combining mark too, since one at the start of a token has no character to
/// stand on (`zedc_syntax::lex`).
pub fn hidden(c: char) -> bool {
    c.is_control()
        || (c.is_whitespace() && c != ' ')
        || (c.width() == Some(0) && !is_combining_mark(c))
}

/// The escape form of `c`: `\u{X}`, `X` its code point in upper-case hex with no leading zeros,
/// as a Zed string writes it.
pub fn escape(c: char, f: &mut impl fmt::Write) -> fmt::Result {
    write!(f, "\\u{{{:X}}}", c as u32)
}

/// The columns [`escape`] writes for `c`: `\u{` and `}` and one hex digit for each four bits up
/// to the highest set.
pub fn escape_width(c: char) -> usize {
    let bits = 32 - (c as u32 | 1).leading_zeros() as usize;
    4 + bits.div_ceil(4)
}

/// `text` as a terminal is to show it: each character [`hidden`] gives in its escape form, but
/// for the line breaks, which lay out a diagnostic, and the tab, which a repair may indent with as
/// the source does. `O(len)`; a text with no such character is
/// written in one call.
pub struct Escaped<'a>(pub &'a str);

impl fmt::Display for Escaped<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut from = 0;
        for (i, c) in self.0.char_indices() {
            if !matches!(c, '\n' | '\t') && hidden(c) {
                f.write_str(&self.0[from..i])?;
                escape(c, f)?;
                from = i + c.len_utf8();
            }
        }
        f.write_str(&self.0[from..])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escape_width_counts_what_escape_writes() {
        for c in [
            '\0', '\u{1}', '\u{F}', '\u{10}', '\u{1B}', '\u{FF}', '\u{100}', '\u{202E}',
        ] {
            let mut s = String::new();
            escape(c, &mut s).unwrap();
            assert_eq!(escape_width(c), s.len(), "{s}");
        }
        let mut s = String::new();
        escape('\u{10FFFF}', &mut s).unwrap();
        assert_eq!(
            (s.as_str(), escape_width('\u{10FFFF}')),
            ("\\u{10FFFF}", 10)
        );
    }

    #[test]
    fn hidden_characters() {
        for c in [
            '\0', '\u{1B}', '\r', '\u{7F}', '\u{9B}', '\u{A0}', '\u{2028}', '\u{200B}',
        ] {
            assert!(hidden(c), "{:X}", c as u32);
        }
        for c in [
            '\u{200D}', '\u{FEFF}', '\u{202E}', '\u{2066}', '\u{2069}', '\u{61C}',
        ] {
            assert!(hidden(c), "{:X}", c as u32);
        }
        // A space, a letter, a wide character, an emoji and a combining mark show as themselves.
        for c in [' ', 'a', 'é', '日', '😀', '\u{301}', '\u{94D}'] {
            assert!(!hidden(c), "{:X}", c as u32);
        }
    }

    #[test]
    fn shown_keeps_line_breaks_and_escapes_the_rest() {
        let s = Escaped("a\u{1B}[2J\nb\u{0}\r\té").to_string();
        assert_eq!(s, "a\\u{1B}[2J\nb\\u{0}\\u{D}\té");
    }
}
