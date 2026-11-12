//! `ascii_names PATH ...` checks that every name, atom and annotation in the Zed code of each
//! `.zed` file under each PATH is written in printable ASCII, U+0021 to U+007E (DESIGN.md
//! sec:lexical; plan row NAME-ascii-library): a program's own names may be Unicode, but the
//! keywords and every name the prelude and the standard library (libzed) declare or export are
//! ASCII, so that each can be typed on any keyboard. It prints `FILE:LINE:COLUMN: the name
//! `π`` for each such name, and `FILE FAIL reason` for a file it cannot read or lex, and fails if
//! it prints anything. Comments and the text of strings are not code and may hold any character.
//!
//! Each token is checked, uses as well as declarations: a name a file uses is declared in it,
//! imported from another such file, or a keyword, so checking every token checks every
//! declaration, and a use of a name declared elsewhere is checked where it is declared too.

use std::path::Path;

use zedc::lex::{Part, Tok, Token, lex};

use crate::text::read_text;
use crate::{Outcome, arg, say};

/// Whether `word` is written in printable ASCII only.
pub fn is_printable_ascii(word: &str) -> bool {
    word.chars().all(|c| ('!'..='~').contains(&c))
}

/// Each name, atom and annotation of the Zed code `text` that is not printable ASCII, with its
/// line and column (each from 1, the column in characters), as `#café` or `@ü` for an atom or an
/// annotation; or the lexer's error.
pub fn non_ascii_names(text: &str) -> Result<Vec<(usize, usize, String)>, String> {
    let tokens = lex(text).map_err(|e| e.to_string())?;
    let mut found = Vec::new();
    collect(&tokens, &mut found);
    // Complexity tradeoff: the naive form counts the lines before each of the k words found,
    // O(n) each and O(n k) in all; this finds the start of every line once, O(n), and each
    // word's line by a binary search over them, O(log n), so O(n + k log n).
    let starts: Vec<usize> = std::iter::once(0)
        .chain(text.match_indices('\n').map(|(i, _)| i + 1))
        .collect();
    Ok(found
        .into_iter()
        .map(|(at, word)| {
            let line = starts.partition_point(|&s| s <= at);
            let column = text[starts[line - 1]..at].chars().count() + 1;
            (line, column, word)
        })
        .collect())
}

/// Appends to `found` the start and the written form of each word of `tokens`, and of the holes
/// of their strings, that is not printable ASCII.
fn collect(tokens: &[Token], found: &mut Vec<(usize, String)>) {
    for t in tokens {
        let word = match &t.tok {
            Tok::Name(n) => n.clone(),
            Tok::Atom(a) => format!("#{a}"),
            Tok::Annot(a) => format!("@{a}"),
            Tok::Str(parts) => {
                for p in parts {
                    if let Part::Hole { tokens, .. } = p {
                        collect(tokens, found);
                    }
                }
                continue;
            }
            _ => continue,
        };
        if !is_printable_ascii(&word) {
            found.push((t.span.start, word));
        }
    }
}

/// The `.zed` files under `path`, a file or a directory, in sorted order; a directory whose name
/// starts with `.`, such as `.git`, is skipped.
fn zed_files(path: &Path, files: &mut Vec<String>) -> Result<(), String> {
    let shown = path.display();
    if !path.is_dir() {
        files.push(path.to_str().ok_or(format!("{shown}: not UTF-8"))?.into());
        return Ok(());
    }
    let mut entries: Vec<_> = std::fs::read_dir(path)
        .map_err(|e| format!("{shown}: {e}"))?
        .collect::<Result<_, _>>()
        .map_err(|e| format!("{shown}: {e}"))?;
    entries.sort_by_key(|e| e.file_name());
    for e in entries {
        let p = e.path();
        let hidden = e.file_name().to_str().is_some_and(|n| n.starts_with('.'));
        if p.is_dir() {
            if !hidden {
                zed_files(&p, files)?;
            }
        } else if p.extension().is_some_and(|x| x == "zed") {
            zed_files(&p, files)?;
        }
    }
    Ok(())
}

/// Runs the tool.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    arg(args, 0, "ascii_names PATH ...")?;
    let mut files = Vec::new();
    for a in args {
        zed_files(Path::new(a), &mut files)?;
    }
    let mut bad = 0;
    for f in &files {
        match non_ascii_names(&read_text(f)?) {
            Ok(found) => {
                for (line, column, word) in found {
                    say!(out, "{f}:{line}:{column}: the name `{word}`");
                    bad += 1;
                }
            }
            Err(why) => {
                say!(out, "{f} FAIL {why}");
                bad += 1;
            }
        }
    }
    Ok(bad == 0)
}
