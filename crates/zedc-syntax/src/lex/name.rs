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
//!
//! `XID_START` and `XID_CONTINUE` are UAX #31's classes less the characters that show as nothing
//! or as blank space, since a name holding one would look like the name without it and be a
//! different one (QUESTIONS A97, 2026-11-12): every character with the property
//! Default_Ignorable_Code_Point (UAX #31's Default Ignorable Exclusion Profile, section 7.3), and
//! the three characters of those classes whose glyph is blank but which lack the property,
//! U+13441 EGYPTIAN HIEROGLYPH FULL BLANK, U+13442 EGYPTIAN HIEROGLYPH HALF BLANK and U+16FE4
//! KHITAN SMALL SCRIPT FILLER. So a name stops before a zero width joiner, a variation selector
//! or a Hangul filler, which then starts no token and is an error in code; a comment or a string
//! takes it.

use unicode_ident::{is_xid_continue, is_xid_start};
use unicode_script::{Script, ScriptExtension, UnicodeScript};

/// The characters with the Unicode property Default_Ignorable_Code_Point, as sorted, disjoint,
/// inclusive ranges with a gap between each two: DerivedCoreProperties.txt of Unicode 18.0, the
/// version of unicode-ident's tables, with its adjacent ranges joined. The test
/// `the_excluded_characters_are_the_default_ignorable_code_points` compares this table with
/// that file for every code point.
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

/// The characters of XID_Start or XID_Continue that lack the property
/// Default_Ignorable_Code_Point but whose glyph is blank: in Unicode 18.0 these three, by their
/// names and general categories in UnicodeData.txt (two Lo letters and one Mn mark).
const BLANK: [char; 3] = ['\u{13441}', '\u{13442}', '\u{16FE4}'];

/// Whether `c` has the Unicode property Default_Ignorable_Code_Point.
pub fn is_default_ignorable(c: char) -> bool {
    // Complexity tradeoff: the naive form scans the r = 17 ranges, O(r) per character; this is
    // a binary search, O(log r), and a character below U+00AD, which every ASCII character is,
    // is answered by one comparison. Nothing is given up: the answer is exact for every code
    // point, and the table costs 136 bytes.
    c >= '\u{AD}' && in_ranges(&DEFAULT_IGNORABLE, c)
}

/// Whether `c` lies in one of the sorted, disjoint, inclusive `ranges`: a binary search,
/// O(log r) for r ranges.
pub(super) fn in_ranges(ranges: &[(char, char)], c: char) -> bool {
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

/// Whether a name may not hold `c`, which shows as nothing or as blank space: a
/// Default_Ignorable_Code_Point character or one of the three blank characters.
pub fn is_excluded_from_names(c: char) -> bool {
    // Complexity tradeoff: the table search of `is_default_ignorable`, O(log r), and three
    // comparisons for the blank characters.
    is_default_ignorable(c) || BLANK.contains(&c)
}

/// Whether `c` may start a name: the grammar's `XID_START`, UAX #31's XID_Start less the
/// characters [`is_excluded_from_names`] gives.
pub fn is_name_start(c: char) -> bool {
    is_xid_start(c) && !is_excluded_from_names(c)
}

/// Whether `c` may continue a name: the grammar's `XID_CONTINUE`, UAX #31's XID_Continue less
/// the characters [`is_excluded_from_names`] gives.
pub fn is_name_continue(c: char) -> bool {
    is_xid_continue(c) && !is_excluded_from_names(c)
}

/// The end of the name starting at byte `pos` of `text`, if one starts there.
pub fn name(text: &str, pos: usize) -> Option<usize> {
    let rest = &text[pos..];
    let mut chars = rest.char_indices().peekable();
    let (_, first) = chars.next()?;
    let starts = is_name_start(first)
        || (first == '_' && chars.peek().is_some_and(|&(_, c)| is_name_continue(c)));
    if !starts {
        return None;
    }
    let mut end = rest.len();
    for (i, c) in chars {
        if !is_name_continue(c) {
            end = i + usize::from(c == '\'');
            break;
        }
    }
    Some(pos + end)
}

/// The end of the wildcard starting at byte `pos` of `text`, if one starts there.
pub(super) fn wildcard(text: &str, pos: usize) -> Option<usize> {
    let mut chars = text[pos..].chars();
    (chars.next() == Some('_') && !chars.next().is_some_and(is_name_continue)).then_some(pos + 1)
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
/// first use, as `Latin and Cyrillic` or `Latin, Greek and Cyrillic`.
pub(super) fn scripts_of(name: &str) -> String {
    let mut seen: Vec<Script> = Vec::new();
    for c in name.chars() {
        let s = c.script();
        if !matches!(s, Script::Common | Script::Inherited) && !seen.contains(&s) {
            seen.push(s);
        }
    }
    let names: Vec<&str> = seen.iter().map(|s| s.full_name()).collect();
    match names.split_last() {
        Some((last, rest)) if !rest.is_empty() => format!("{} and {last}", rest.join(", ")),
        _ => names.concat(),
    }
}
