//! 12 balanced brackets. The corpus program fills a CYK table over the bracket grammar; a
//! reference needs only what it prints: whether the line is balanced, and how many of its
//! substrings are. A stack matches each `)` to its `(`, so this reaches the same answer by a
//! different route, in one pass. Characters are code points.

fn balanced(s: &[char]) -> bool {
    let mut d = 0;
    for &c in s {
        d += match c {
            '(' => 1,
            ')' => -1,
            _ => 0,
        };
        if d < 0 || (c != '(' && c != ')') {
            return false;
        }
    }
    d == 0 && !s.is_empty()
}

/// How many non-empty substrings of `s` are balanced. Those ending at a matched `)` are the one
/// that starts at its `(`, and that one after each balanced substring ending just before the `(`.
fn balanced_substrings(s: &[char]) -> usize {
    let mut ending_at = vec![0; s.len()];
    let mut open = Vec::new();
    for (i, &c) in s.iter().enumerate() {
        match c {
            '(' => open.push(i),
            ')' => {
                if let Some(j) = open.pop() {
                    ending_at[i] = 1 + if j > 0 { ending_at[j - 1] } else { 0 };
                }
            }
            _ => open.clear(),
        }
    }
    ending_at.iter().sum()
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    for line in lines {
        let s: Vec<char> = line.chars().collect();
        let verdict = if balanced(&s) {
            "balanced"
        } else {
            "unbalanced"
        };
        say!(out, "{verdict} {} {line}", balanced_substrings(&s));
    }
    Ok(())
}
