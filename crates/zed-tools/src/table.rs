//! The cells of a row of a Markdown table, read the way GitHub renders it (GitHub-flavored
//! Markdown): a row splits at every `|`, one inside backticks too, except a `|` written `\|`,
//! which is part of the cell's text. The one splitter of the tools' table readers (`plan`,
//! `catalog`, `audit`, `layer`, `spec_checks`, DRY-test-helpers); before it, three of them split
//! at every `|`, so a `\|` in a cell made one cell two.

/// `s` split at each `|` that is not written `\|`, each piece trimmed. A row's outer bars are
/// not dropped: `"| a | b |"` gives `["", "a", "b", ""]`. One pass over the bytes: O(length).
pub fn split_cells(s: &str) -> Vec<&str> {
    let mut cells = Vec::new();
    let mut start = 0;
    let mut escaped = false;
    for (at, b) in s.bytes().enumerate() {
        if b == b'|' && !escaped {
            cells.push(s[start..at].trim());
            start = at + 1;
        }
        escaped = b == b'\\';
    }
    cells.push(s[start..].trim());
    cells
}

/// Whether the trimmed row `l` ends with a `|` that splits, not one written `\|`.
pub fn ends_with_bar(l: &str) -> bool {
    let l = l.trim_end();
    l.ends_with('|') && !l[..l.len() - 1].ends_with('\\')
}

/// The cells of the row `l`, trimmed: the text between its splitting bars, its outer bars
/// dropped where it has them. `"| a | b \| c |"` gives `["a", "b \| c"]`.
pub fn cells(l: &str) -> Vec<&str> {
    let l = l.trim();
    // The closing bar first: in `|`, the one bar is both.
    let l = if ends_with_bar(l) {
        &l[..l.len() - 1]
    } else {
        l
    };
    split_cells(l.strip_prefix('|').unwrap_or(l))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A `\|` is text, also inside backticks, and an outer bar is dropped only where it splits.
    #[test]
    fn rows_split_at_unescaped_bars() {
        assert_eq!(split_cells("| a | b |"), ["", "a", "b", ""]);
        assert_eq!(cells("| a | b |"), ["a", "b"]);
        assert_eq!(cells("  | a | `x \\| y` |  "), ["a", "`x \\| y`"]);
        assert_eq!(cells("| a | b \\|"), ["a", "b \\|"]);
        assert_eq!(cells("a | b"), ["a", "b"]);
        assert_eq!(cells("|"), [""]);
        assert_eq!(cells("| |"), [""]);
        assert!(ends_with_bar("| a |  "));
        assert!(!ends_with_bar("| a \\|"));
        assert!(!ends_with_bar("| a"));
    }
}
