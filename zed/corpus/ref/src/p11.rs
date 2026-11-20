//! 11 CSV fields by a three-state quote machine, run serially (the reference for the scan of
//! transition tables). A comma separates when the state before it is not 1 (inside quotes);
//! fields are the text between separators. A line is a `Utf8String`, keyed by code point rank
//! (DESIGN sec:order), so `chars()` walks the program's keys, and the field the program takes as
//! `l.sliceCodePoints(cuts[k] + 1..<cuts[k + 1])` (11-csv-split.zed line 22, the code points of
//! that range made a string again, ranked from 0; DESIGN sec:order, author answer A107) is
//! exactly the code points pushed here between two separators.

const QUOTE_NEXT: [usize; 3] = [1, 2, 1]; // after '"', by state
const OTHER_NEXT: [usize; 3] = [0, 1, 0]; // after any other character

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    for line in lines {
        let mut st = 0;
        let mut fields = vec![String::new()];
        for c in line.chars() {
            if c == ',' && st != 1 {
                fields.push(String::new());
            } else {
                fields.last_mut().expect("never empty").push(c);
            }
            st = if c == '"' { QUOTE_NEXT } else { OTHER_NEXT }[st];
        }
        let shown: Vec<String> = fields.iter().map(|f| format!("[{f}]")).collect();
        say!(out, "{} {}", fields.len(), shown.join(" "));
    }
    Ok(())
}
