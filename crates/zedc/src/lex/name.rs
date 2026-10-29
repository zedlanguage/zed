//! Names and the wildcard (step L1.2):
//!
//! ```peg
//! Wildcard = '_' !XID_CONTINUE
//! Name     = (XID_START | '_' &XID_CONTINUE) XID_CONTINUE* "'"?
//! ```
//!
//! `XID_CONTINUE` holds `_`, so `_x`, `x_1` and `__` are names, and a bare `_` is the
//! wildcard. A name must be of one script, as UTS #39 defines it at its "Highly Restrictive"
//! level: one script is shared by every character (a character of the Common or Inherited
//! script, such as a digit or `_`, shares every script), or every character is of one of three
//! writing systems, each of which Latin may join: Han with Hiragana and Katakana (Japanese), Han
//! with Bopomofo (Chinese), Han with Hangul (Korean). So `größe`, `面積`, `ユーザー名`, `user名`
//! are names, and `pаypal` with a Cyrillic `а` is rejected.

use unicode_ident::{is_xid_continue, is_xid_start};
use unicode_script::{Script, ScriptExtension, UnicodeScript};

/// The end of the name starting at byte `pos` of `text`, if one starts there.
pub(super) fn name(text: &str, pos: usize) -> Option<usize> {
    let rest = &text[pos..];
    let mut chars = rest.char_indices().peekable();
    let (_, first) = chars.next()?;
    let starts = is_xid_start(first)
        || (first == '_' && chars.peek().is_some_and(|&(_, c)| is_xid_continue(c)));
    if !starts {
        return None;
    }
    let mut end = rest.len();
    for (i, c) in chars {
        if !is_xid_continue(c) {
            end = i + usize::from(c == '\'');
            break;
        }
    }
    Some(pos + end)
}

/// The end of the wildcard starting at byte `pos` of `text`, if one starts there.
pub(super) fn wildcard(text: &str, pos: usize) -> Option<usize> {
    let mut chars = text[pos..].chars();
    (chars.next() == Some('_') && !chars.next().is_some_and(is_xid_continue)).then_some(pos + 1)
}

/// The writing systems a name may combine with Latin.
const COMBINED: [&[Script]; 3] = [
    &[
        Script::Latin,
        Script::Han,
        Script::Hiragana,
        Script::Katakana,
    ],
    &[Script::Latin, Script::Han, Script::Bopomofo],
    &[Script::Latin, Script::Han, Script::Hangul],
];

/// Whether the characters of `name` are of one script, in the sense of the module comment.
pub fn is_single_script(name: &str) -> bool {
    if !ScriptExtension::for_str(name).is_empty() {
        return true;
    }
    COMBINED.iter().any(|set| {
        let set = set
            .iter()
            .fold(ScriptExtension::from(Script::Unknown), |s, &x| {
                s.union(x.into())
            });
        name.chars()
            .all(|c| !c.script_extension().intersection(set).is_empty())
    })
}

/// The scripts of the characters of `name` other than Common and Inherited, in order of
/// first use, as `Latin, Cyrillic`.
pub(super) fn scripts_of(name: &str) -> String {
    let mut seen: Vec<Script> = Vec::new();
    for c in name.chars() {
        let s = c.script();
        if !matches!(s, Script::Common | Script::Inherited) && !seen.contains(&s) {
            seen.push(s);
        }
    }
    seen.iter()
        .map(|s| s.full_name())
        .collect::<Vec<_>>()
        .join(", ")
}
