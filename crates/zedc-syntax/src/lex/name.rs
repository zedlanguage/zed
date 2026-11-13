//! Names and the wildcard (step L1.2; NAME-ascii-only, 2026-11-12):
//!
//! ```peg
//! NameChar = [A-Za-z0-9_]
//! Wildcard = '_' !NameChar
//! Name     = ([A-Za-z] | '_' &NameChar) NameChar* "'"?
//! ```
//!
//! So `_x`, `x_1` and `__` are names, and a bare `_` is the wildcard. A name is ASCII: a
//! letter, digit or combining mark beyond ASCII where a name would hold it (`café`, `größe`,
//! `δt`, `#pаypal` with a Cyrillic `а`) starts or ends no token. The lexer reads such a run as
//! one word ([`word`]), so that the error shows the whole word, and offers an ASCII name for it
//! when the tables below give one ([`ascii_name`]). Characters that show as nothing or as blank
//! space ([`super::token::is_blank`]) are not read into such a word: they keep the message of a
//! character that may not show.

use std::collections::HashSet;

use any_ascii::{any_ascii, any_ascii_char};
use unicode_normalization::UnicodeNormalization;
use unicode_normalization::char::is_combining_mark;
use unicode_script::{Script, UnicodeScript};
use unicode_security::skeleton;

use super::punct;
use super::token::{Error, ErrorKind, is_blank};

/// Whether `c` may start a name: the grammar's `[A-Za-z]`.
pub fn is_name_start(c: char) -> bool {
    c.is_ascii_alphabetic()
}

/// Whether `c` may continue a name: the grammar's `NameChar`, `[A-Za-z0-9_]`.
pub fn is_name_continue(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// The end of the name starting at byte `pos` of `text`, if one starts there.
pub fn name(text: &str, pos: usize) -> Option<usize> {
    let b = &text.as_bytes()[pos..];
    let first = char::from(*b.first()?);
    let starts = is_name_start(first) || (first == '_' && b.get(1).is_some_and(|&c| continues(c)));
    if !starts {
        return None;
    }
    let run = b.iter().position(|&c| !continues(c)).unwrap_or(b.len());
    Some(pos + run + usize::from(b.get(run) == Some(&b'\'')))
}

/// Whether the byte `c` continues a name. A byte of a character beyond ASCII never does.
fn continues(c: u8) -> bool {
    is_name_continue(char::from(c))
}

/// The end of the wildcard starting at byte `pos` of `text`, if one starts there.
pub(super) fn wildcard(text: &str, pos: usize) -> Option<usize> {
    let b = &text.as_bytes()[pos..];
    (b.first() == Some(&b'_') && !b.get(1).is_some_and(|&c| continues(c))).then_some(pos + 1)
}

/// What [`word`] reads.
pub(super) enum Word {
    /// A name, ending at this byte.
    Name(usize),
    /// A word that is a name but for a character beyond ASCII, ending at this byte.
    Foreign(usize),
}

/// Whether `c` is a character beyond ASCII that a word may start with: a letter or digit of
/// another script, or of Latin beyond ASCII, that shows on screen.
fn starts_foreign(c: char) -> bool {
    !c.is_ascii() && c.is_alphanumeric() && !is_blank(c)
}

/// Whether `c` is a character beyond ASCII that a word may hold: as [`starts_foreign`], or a
/// combining mark, which shows on the letter before it.
fn continues_foreign(c: char) -> bool {
    !c.is_ascii() && (c.is_alphanumeric() || is_combining_mark(c)) && !is_blank(c)
}

/// Whether `c` may stand in a word that is a name or would be one but for characters beyond
/// ASCII: a name character, or a character `continues_foreign` takes. A reader that refuses
/// a name beyond ASCII reads a word this far, so that its error names the whole word.
pub fn is_word_char(c: char) -> bool {
    is_name_continue(c) || continues_foreign(c)
}

/// The name, or the word that would be a name but for characters beyond ASCII, starting at
/// byte `pos` of `text`: a run of name characters and the characters [`continues_foreign`]
/// takes that starts as a name starts or with a letter beyond ASCII, then one `'` at most.
pub(super) fn word(text: &str, pos: usize) -> Option<Word> {
    // Complexity tradeoff: a name of ASCII alone is read by bytes, as `name` reads it, and the
    // character after it is looked at once; only a word that holds a character beyond ASCII is
    // read again by characters. Both are O(length of the word).
    if let Some(end) = name(text, pos) {
        let stop = end - usize::from(text[..end].ends_with('\''));
        if !text[stop..].starts_with(continues_foreign) {
            return Some(Word::Name(end));
        }
    }
    let rest = &text[pos..];
    let mut chars = rest.chars();
    let first = chars.next()?;
    let starts = is_name_start(first)
        || starts_foreign(first)
        || (first == '_'
            && chars
                .next()
                .is_some_and(|c| is_name_continue(c) || starts_foreign(c)));
    if !starts {
        return None;
    }
    let run = rest.find(|c: char| !is_word_char(c)).unwrap_or(rest.len());
    let end = pos + run + usize::from(rest[run..].starts_with('\''));
    Some(if rest[..run].is_ascii() {
        Word::Name(end)
    } else {
        Word::Foreign(end)
    })
}

/// The ASCII name offered for `word`, a word the function `word` reads as foreign, with its `'`
/// if it has one, written in `text`; or none. A name `taken` refuses and a word of ASCII name
/// characters anywhere in `text` are not offered: the least of `_2`, `_3`, ... that makes the
/// name new is added to it.
///
/// A word with no ASCII letter is transliterated as a whole by the any_ascii tables (`число`
/// is `chislo`, `面積` is `MianJi`, `α` is `a`), keeping only the name characters they give.
/// In a word with an ASCII letter, each character beyond ASCII becomes ASCII by the first of
/// these that gives one or more name characters:
/// 1. its compatibility decomposition (NFKD) without combining marks: `é` is `e`, `ﬁ` is `fi`;
/// 2. the ASCII character it is confusable with, by the confusables data of UTS #39 (its
///    skeleton): Cyrillic `а` is `a`, Greek `ο` is `o`, `ℓ` is `l`;
/// 3. its transliteration by the any_ascii tables, for a letter of the Latin script: `ß` is
///    `ss`.
///
/// A combining mark there is dropped, as an accent on the letter before it. A character none of
/// these turns into name characters (a Greek letter in a word with an ASCII letter, as in `ΔT`)
/// leaves the word with no offer, as does a result that is no name (it starts with a digit).
pub fn ascii_name(text: &str, word: &str, taken: &dyn Fn(&str) -> bool) -> Option<String> {
    // Complexity tradeoff: each table lookup is O(log t) or O(1) per character (unicode-security
    // and unicode-normalization search sorted tables; any_ascii indexes blocks), so the offer
    // costs O(w log t) for a word of w characters. The words of `text` are collected once, in
    // O(|text|), and each suffix tried is one hash lookup; at most one more suffix is tried
    // than there are words. The naive form, a scan of `text` per suffix tried, is O(|text|²).
    let body = word.trim_end_matches('\'');
    let prime = &word[body.len()..];
    let out: String = if body.chars().any(|c| c.is_ascii_alphabetic()) {
        let mut out = String::new();
        for c in body.chars().filter(|&c| !is_combining_mark(c)) {
            if c.is_ascii() {
                out.push(c);
                continue;
            }
            let mapped = accents_dropped(c)
                .or_else(|| lookalike(c))
                .or_else(|| (c.script() == Script::Latin).then(|| name_chars(any_ascii_char(c))));
            out.push_str(&mapped.filter(|m| !m.is_empty())?);
        }
        out
    } else {
        name_chars(&any_ascii(body))
    };
    if name(&out, 0) != Some(out.len()) {
        return None;
    }
    let words = words(text);
    let free = |n: &str| !taken(n) && !words.contains(n);
    let mut name = out.clone();
    let mut k = 2;
    while !free(&name) {
        name = format!("{out}_{k}");
        k += 1;
    }
    Some(name + prime)
}

/// The name characters of `s`, in order.
fn name_chars(s: &str) -> String {
    s.chars().filter(|&c| is_name_continue(c)).collect()
}

/// `c` decomposed for compatibility (NFKD) without its combining marks, if that is a non-empty
/// run of name characters.
fn accents_dropped(c: char) -> Option<String> {
    let s: String = std::iter::once(c)
        .nfkd()
        .filter(|&d| !is_combining_mark(d))
        .collect();
    (!s.is_empty() && s.chars().all(is_name_continue)).then_some(s)
}

/// The UTS #39 skeleton of `c`, if that is a non-empty run of name characters: the ASCII
/// characters `c` is confusable with.
fn lookalike(c: char) -> Option<String> {
    let s: String = skeleton(c.encode_utf8(&mut [0; 4])).collect();
    (!s.is_empty() && s.chars().all(is_name_continue)).then_some(s)
}

/// The runs of ASCII name characters in `text`.
fn words(text: &str) -> HashSet<&str> {
    text.split(|c: char| !is_name_continue(c))
        .filter(|w| !w.is_empty())
        .collect()
}

impl Error {
    /// Offers no name `taken` gives (a prelude name, which the lexer does not know) for a word
    /// beyond ASCII lexed from `text`: the offer is made again with those names refused too.
    /// The name offered is no keyword either. An atom or annotation (`#café`, `@tést`) is
    /// offered its ASCII spelling whatever the names and keywords, since `#if` and `@test` are
    /// an atom and an annotation; only another word of `text` is refused, so that the repair
    /// does not turn it into an atom the program already uses.
    pub fn avoid_names(&mut self, text: &str, taken: &dyn Fn(&str) -> bool) {
        if let ErrorKind::NonAsciiName { word, repair } = &mut self.kind {
            let body = word.trim_start_matches(['#', '@']);
            let sign = &word[..word.len() - body.len()];
            let refused = |n: &str| sign.is_empty() && (punct::keyword(n).is_some() || taken(n));
            *repair = ascii_name(text, body, &refused).map(|n| format!("{sign}{n}"));
        }
    }
}
