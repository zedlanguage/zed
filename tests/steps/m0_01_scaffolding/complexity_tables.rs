//! COMPLEXITY-other-tables-cells: every row of every table in `COMPLEXITY.md` has as many
//! cells as its header. A `|` written inside a cell, in code too, must be escaped as `\|`, or
//! Markdown splits the cell there (COMPLEXITY-table-header-columns found rows of 2 to 7 cells
//! under one header).

use std::fs;

use zed_tests::steps_dir;

/// The cells of a table line: its unescaped `|`, less one. `\|` is no separator. O(length).
fn cells(line: &str) -> usize {
    let mut count: usize = 0;
    let mut escaped = false;
    for c in line.chars() {
        match c {
            '\\' => escaped = !escaped,
            '|' if !escaped => count += 1,
            _ => escaped = false,
        }
    }
    count.saturating_sub(1)
}

/// Each line (1-based number, text, cells, header's cells) of `text` whose table row has a
/// cell count other than its table header's. A table is a run of lines that start with `|`;
/// its first line is the header. One pass over the text.
fn misfits(text: &str) -> Vec<(usize, String, usize, usize)> {
    let mut out = Vec::new();
    let mut header: Option<usize> = None;
    for (i, line) in text.lines().enumerate() {
        if !line.starts_with('|') {
            header = None;
            continue;
        }
        let n = cells(line);
        match header {
            None => header = Some(n),
            Some(h) if n != h => out.push((i + 1, line.to_string(), n, h)),
            Some(_) => {}
        }
    }
    out
}

#[test]
fn cells_counts_unescaped_pipes_only() {
    assert_eq!(cells("| a | b |"), 2);
    assert_eq!(cells(r"| `a \| b` | c |"), 2);
    // `\\` is an escaped backslash, so the `|` after it separates.
    assert_eq!(cells(r"| a \| b |"), 1);
    assert_eq!(cells(r"| a \\| b |"), 2);
    assert_eq!(
        misfits("| h | i |\n|---|---|\n| a | b |\n| `x | y` | c |\n\n| one |\n"),
        [(4, "| `x | y` | c |".to_string(), 3, 2)]
    );
}

#[test]
fn every_complexity_table_row_has_its_header_cell_count() {
    let path = steps_dir().join("../../COMPLEXITY.md");
    let text = fs::read_to_string(&path).expect("COMPLEXITY.md is readable");
    let bad = misfits(&text);
    let shown: Vec<String> = bad
        .iter()
        .map(|(n, line, c, h)| format!("line {n}: {c} cells, header {h}: {line}"))
        .collect();
    assert!(bad.is_empty(), "{} rows:\n{}", bad.len(), shown.join("\n"));
}
