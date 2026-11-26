//! What a terminal shows of a text zedc prints (DESIGN.md sec:diagnostics, "Characters a
//! terminal does not show"). A character of the program's text that a terminal would not show as
//! itself is printed in its Zed escape form `\u{X}`, so a diagnostic shows every character of the
//! source and none can act on the reader's terminal: an ESC from a string can no longer clear the
//! screen, nor U+202E reverse the rest of the line.

use std::fmt;

use unicode_normalization::char::is_combining_mark;
use unicode_width::UnicodeWidthChar;
// The escape form of a character and its columns, which the kernel's string literals write too;
// kept in `zed_kernel::text`, below this crate, so both write one form.
pub use zed_kernel::text::{escape, escape_width};

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

/// The columns `c` takes in a diagnostic: four for a tab, which a quoted line shows as four
/// spaces; the columns of its escape form for another [`hidden`] character; else the columns a
/// terminal gives it, none for a combining mark and two for a wide character. O(1).
pub fn char_width(c: char) -> usize {
    match c {
        '\t' => 4,
        _ if hidden(c) => escape_width(c),
        _ => c.width().unwrap_or(0),
    }
}

/// The columns `text` takes in a diagnostic, the sum of [`char_width`] over its characters:
/// what a column of text written after it must pad to, not its count of characters. O(len).
pub fn width(text: &str) -> usize {
    text.chars().map(char_width).sum()
}

/// Writes `n` copies of `c`: padding or a mark under a quoted line. Not a width in a format
/// string, which takes at most 2^16 - 1, so a mark at a column past that, on a line of 65,536
/// characters or more, is still placed. O(n).
pub fn pad(f: &mut (impl fmt::Write + ?Sized), c: char, n: usize) -> fmt::Result {
    (0..n).try_for_each(|_| f.write_char(c))
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

    /// A narrow, a wide and a combining character, a tab and two hidden characters, each by
    /// the columns a terminal gives it as a diagnostic shows it.
    #[test]
    fn a_width_counts_columns_not_characters() {
        assert_eq!(width(""), 0);
        assert_eq!(width("abc"), 3);
        assert_eq!(width("日本"), 4);
        assert_eq!(width("ne\u{301}e"), 3);
        assert_eq!(width("\tx"), 5);
        assert_eq!(width("a\u{1B}b"), 2 + escape_width('\u{1B}'));
        assert_eq!(char_width('\u{202E}'), "\\u{202E}".len());
        let mut s = String::from(">");
        pad(&mut s, '^', 3).unwrap();
        pad(&mut s, ' ', 0).unwrap();
        assert_eq!(s, ">^^^");
    }

    #[test]
    fn shown_keeps_line_breaks_and_escapes_the_rest() {
        let s = Escaped("a\u{1B}[2J\nb\u{0}\r\té").to_string();
        assert_eq!(s, "a\\u{1B}[2J\nb\\u{0}\\u{D}\té");
    }
}
