//! The M0.8 audit: which grammar alternatives and which defined words a program needs.
//!
//! An alternative is needed when the program stops parsing, or parses to a different tree, with
//! that alternative removed from the grammar. Every alternative is tried this way, so the list
//! is exact for the parser of DESIGN.md sec:grammar rather than a guess from token shapes. The
//! defined words come from the layer checker (`layer -v`).
//!
//! `audit SPEC_DIR PROGRAM.zed [--checklist ZED0.md]` prints one line per needed alternative,
//! `L<layer> <rule>#<index> <grammar text>`, then the words, then the highest layer met. With
//! `--checklist` it also checks that the checklist names every needed alternative (as `Rule#i`)
//! and every word (in backticks), and fails if not. The audit runs by hand, like the corpus
//! layer check (LEDGER.md), since CI does not read the spec repository.

use std::collections::{BTreeSet, HashMap};

use zedc::parse::{Grammar, TOP, split_line};

use crate::layer::{program_units, report};
use crate::spec::Spec;
use crate::syntax::{Tokens, Tree, lex, parse};
use crate::text::{prefix, read_text, repr, strip};
use crate::{Outcome, arg, say};

/// The grammar text of each alternative of the grammar `text`, by rule and index.
fn bodies(text: &str) -> Result<HashMap<(&str, usize), &str>, String> {
    let mut out = HashMap::new();
    let (mut cur, mut n) = ("", 0);
    for l in text.split('\n').filter(|l| !strip(l).is_empty()) {
        let (rule, body, _) = split_line(l).ok_or_else(|| format!("grammar line: {}", repr(l)))?;
        match rule {
            Some(r) => (cur, n) = (r, 0),
            None => n += 1,
        }
        out.insert((cur, n), body);
    }
    Ok(out)
}

/// Whether some unit stops parsing, or changes its tree, under `g`.
fn changes(g: &Grammar, spec: &Spec, units: &[(Tokens, Tree)]) -> bool {
    units
        .iter()
        .any(|(toks, full)| !parse(g, &spec.lexical, toks, TOP, "Unit").is_ok_and(|t| t.same(full)))
}

/// Runs the tool.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    let usage = "audit SPEC_DIR PROGRAM.zed [--checklist ZED0.md]";
    let spec = Spec::open(arg(args, 0, usage)?)?;
    let program = arg(args, 1, usage)?;
    let main = std::path::absolute(program)
        .map_err(|e| format!("{program}: {e}"))?
        .to_string_lossy()
        .into_owned();
    let checklist = match args.get(2).map(String::as_str) {
        Some("--checklist") => args.get(3),
        Some(_) | None => None,
    };
    let (lexical, syn) = (&spec.lexical, &spec.syntactic);
    let mut units = Vec::new();
    for u in program_units(&main)? {
        let toks = lex(lexical, &read_text(&u)?.replace('…', "elided"))?;
        let full = parse(syn, lexical, &toks, TOP, "Unit")
            .map_err(|_| "the program does not parse".to_string())?;
        units.push((toks, full));
    }

    // Each alternative in turn is put above every ring, so the alternatives keep their indices.
    let mut g = syn.clone();
    let mut needed = BTreeSet::new();
    for r in 0..g.rules.len() {
        for i in 0..g.rules[r].alts.len() {
            let layer = std::mem::replace(&mut g.rules[r].alts[i].layer, u32::MAX);
            if changes(&g, &spec, &units) {
                needed.insert((layer, g.rules[r].name.as_str().to_owned(), i));
            }
            g.rules[r].alts[i].layer = layer;
        }
    }

    let text = bodies(&spec.syn_text)?;
    for (lay, rule, i) in &needed {
        let body = text.get(&(rule.as_str(), *i)).copied().unwrap_or("");
        say!(out, "L{lay} {rule}#{i} {}", prefix(body, 110));
    }
    let mut words = String::new();
    report(&spec, true, &[main.as_str()], &mut words)?;
    say!(out, "{words}");
    let highest = needed
        .iter()
        .map(|n| n.0)
        .max()
        .ok_or("the program needs no alternative of the grammar")?;
    say!(out, "highest grammar layer: L{highest}");

    let Some(checklist) = checklist else {
        return Ok(true);
    };
    let listed = read_text(checklist)?;
    let word_of = |l: &str| {
        let mut parts = strip(l).split(zedc::parse::is_space);
        parts.find(|w| !w.is_empty())?;
        parts.find(|w| !w.is_empty()).map(String::from)
    };
    let found: Vec<String> = needed
        .iter()
        .map(|(_, r, i)| format!("{r}#{i}"))
        .chain(
            words
                .split('\n')
                .filter(|l| l.starts_with("      L"))
                .filter_map(word_of),
        )
        .collect();
    let missing: Vec<&str> = found
        .iter()
        .map(String::as_str)
        .filter(|w| !listed.contains(&format!("`{w}`")))
        .collect();
    say!(
        out,
        "checklist: {} needed, {} missing {}",
        found.len(),
        missing.len(),
        missing.join(" ")
    );
    Ok(missing.is_empty())
}
