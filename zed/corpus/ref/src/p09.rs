//! 09 equality against a canonical form: lower-case, then remove '-' and ' '.

use crate::zedrt::lower;

fn canon(s: &str) -> String {
    lower(s).replace(['-', ' '], "")
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    for line in lines {
        let mut parts = line.split(" | ");
        let a = parts.next().unwrap_or("");
        let b = parts.next().unwrap_or("");
        let verdict = if canon(a) == canon(b) {
            "same: "
        } else {
            "different: "
        };
        say!(out, "{verdict}{a} | {b}");
    }
    Ok(())
}
