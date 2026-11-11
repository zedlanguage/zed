//! The M0.8 audit: which grammar alternatives and which defined words a program needs.
//!
//! An alternative is needed when the program stops parsing, or parses to a different tree, with
//! that alternative removed from the grammar. Every alternative is tried this way, so the list
//! is exact for the parser of DESIGN.md sec:grammar rather than a guess from token shapes. The
//! defined words come from the layer checker (`layer -v`).
//!
//! `audit SPEC_DIR PROGRAM.zed [--checklist ZED0.md]` prints one line per needed alternative,
//! `L<layer> <rule>#<index> <grammar text>`, then the words, then the highest layer met. With
//! `--checklist` it compares the table of the checklist's section `## Part A` with that list:
//! each row is a layer, its second column the needed alternatives (as `Rule#i`, in backticks)
//! and its third the needed words (in backticks). It names every needed entry the table does
//! not list, and every listed entry the program does not need (a rule or alternative the
//! grammar no longer has, a word the table of defined words no longer lists, or one that
//! exists but the program does not use), each list with its count, and fails if either list is
//! not empty. The audit runs by hand, like the corpus layer check (LEDGER.md), since CI does not
//! read the spec repository.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use zedc::parse::{Grammar, TOP, split_line};

use crate::layer::{WordTable, program_units, report};
use crate::spec::Spec;
use crate::syntax::{Tokens, Tree, lex, parse};
use crate::text::{base_name, prefix, read_text, repr, strip};
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
    // A line of the verbose layer report: `      L<layer> <word> <how>`.
    let word_of = |l: &str| {
        let mut parts = strip(l)
            .split(zedc::parse::is_space)
            .filter(|w| !w.is_empty());
        let layer = parts.next()?.strip_prefix('L')?.parse().ok()?;
        Some((parts.next()?.to_string(), layer))
    };
    let needs = Needs {
        program: base_name(&main).to_string(),
        alts: needed,
        words: words
            .split('\n')
            .filter(|l| l.starts_with("      L"))
            .filter_map(word_of)
            .collect(),
    };
    let table = WordTable::read(&spec.design)?;
    compare(
        &spec,
        &table,
        &needs,
        base_name(checklist),
        &read_text(checklist)?,
        out,
    )
}

/// What a program needs, as the audit found it.
#[derive(Clone, Debug, Default)]
pub struct Needs {
    /// The program's file name, as the messages print it.
    pub program: String,
    /// Each needed alternative: its layer, its rule and its index in the rule.
    pub alts: BTreeSet<(u32, String, usize)>,
    /// Each needed word, with its layer.
    pub words: BTreeMap<String, u32>,
}

/// The entries of Part A of a checklist, each with the layer of the row that lists it.
#[derive(Debug, Default)]
struct Listed<'a> {
    alts: BTreeMap<&'a str, u32>,
    words: BTreeMap<&'a str, u32>,
}

/// The table of the section `## Part A` of the checklist `text`, or `None` if it has no such
/// section. A row is a line `| L<k> | <alternatives> | <words> |`; an entry is a span in
/// backticks.
fn part_a(text: &str) -> Option<Listed<'_>> {
    let mut lines = text.split('\n');
    lines.find(|l| l.starts_with("## Part A"))?;
    let mut out = Listed::default();
    for l in lines.take_while(|l| !l.starts_with("## ")) {
        let cells: Vec<&str> = l.split('|').collect();
        let [_, layer, alts, words, ..] = cells[..] else {
            continue;
        };
        let Some(Ok(k)) = strip(layer).strip_prefix('L').map(str::parse::<u32>) else {
            continue;
        };
        for (map, cell) in [(&mut out.alts, alts), (&mut out.words, words)] {
            for entry in cell.split('`').skip(1).step_by(2) {
                map.entry(entry).or_insert(k);
            }
        }
    }
    Some(out)
}

/// Why the alternative entry `entry` of the checklist is not needed by `needs.program`.
fn why_alt_unneeded(
    g: &Grammar,
    text: &HashMap<(&str, usize), &str>,
    needs: &Needs,
    entry: &str,
) -> String {
    let Some((rule, i)) = entry
        .split_once('#')
        .and_then(|(r, i)| Some((r, i.parse::<usize>().ok()?)))
    else {
        return "an entry in the column of grammar alternatives is written `Rule#i`, the name \
                of a rule and the index of one of its alternatives, counted from 0"
            .to_string();
    };
    let Some(r) = g.rule(rule) else {
        return format!("the grammar has no rule {rule}");
    };
    let alts = &g.rules[r].alts;
    match alts.get(i) {
        None if alts.len() == 1 => format!("rule {rule} has one alternative, numbered 0"),
        None => format!(
            "rule {rule} has {} alternatives, numbered 0 to {}",
            alts.len(),
            alts.len() - 1
        ),
        Some(alt) => format!(
            "alternative {i} of rule {rule}, `{}` (L{}), can be taken out of the grammar and {} \
             still parses to the same trees",
            prefix(text.get(&(rule, i)).copied().unwrap_or(""), 110),
            alt.layer,
            needs.program
        ),
    }
}

/// Compares Part A of the checklist `listed` (its file name `name`) with `needs`, writes the
/// needed entries it lacks and the entries it lists that are not needed, and says whether both
/// lists are empty.
///
/// Complexity tradeoff: the earlier form searched the whole checklist text for each needed
/// entry (`listed.contains`), O(e·t) for e entries and a text of t bytes, and did not look for
/// listed entries the program does not need at all; comparing both ways by that search would
/// cost the same again. Here the text is read once into ordered maps, O(t + e log e), and each
/// entry of either side is one tree or hash lookup in the other, O(e log e) in all, with no
/// refused input. The grammar's rules and the table of defined words are hash maps already.
/// Test: `m0_03_grammar_tools::scaling::the_checklist_comparison_scales_with_its_entries`.
pub fn compare(
    spec: &Spec,
    table: &WordTable,
    needs: &Needs,
    name: &str,
    listed: &str,
    out: &mut String,
) -> Outcome {
    let Some(list) = part_a(listed) else {
        say!(
            out,
            "checklist: {name} has no section `## Part A`, so it lists none of the {} entries {} \
             needs",
            needs.alts.len() + needs.words.len(),
            needs.program
        );
        return Ok(false);
    };
    let text = bodies(&spec.syn_text)?;
    let g = &spec.syntactic;

    let mut missing = Vec::new();
    for (layer, rule, i) in &needs.alts {
        let entry = format!("{rule}#{i}");
        if !list.alts.contains_key(entry.as_str()) {
            let body = text.get(&(rule.as_str(), *i)).copied().unwrap_or("");
            let why = format!(
                "{} needs alternative {i} of rule {rule}, `{}`, which is at L{layer}",
                needs.program,
                prefix(body, 110)
            );
            missing.push((entry, why));
        }
    }
    for (word, layer) in &needs.words {
        if !list.words.contains_key(word.as_str()) {
            let why = format!(
                "{} uses the word `{word}`, which is at L{layer}",
                needs.program
            );
            missing.push((word.clone(), why));
        }
    }

    let mut unneeded = Vec::new();
    let needed_alts: BTreeSet<String> = needs
        .alts
        .iter()
        .map(|(_, r, i)| format!("{r}#{i}"))
        .collect();
    for (entry, row) in &list.alts {
        if !needed_alts.contains(*entry) {
            let why = why_alt_unneeded(g, &text, needs, entry);
            unneeded.push((*entry, *row, why));
        }
    }
    for (word, row) in &list.words {
        if !needs.words.contains_key(*word) {
            let why = match table.layer_of(word) {
                None => "the table of defined words in DESIGN.md does not list it".to_string(),
                Some(k) => format!(
                    "the table of defined words lists it at L{k}, but {} does not use it",
                    needs.program
                ),
            };
            unneeded.push((*word, *row, why));
        }
    }

    let names =
        |v: &mut dyn Iterator<Item = &str>| v.map(|e| format!(" `{e}`")).collect::<String>();
    say!(
        out,
        "checklist: {} needed, {} missing{}",
        needs.alts.len() + needs.words.len(),
        missing.len(),
        names(&mut missing.iter().map(|m| m.0.as_str()))
    );
    for (entry, why) in &missing {
        say!(out, "  `{entry}` is missing from Part A of {name}: {why}.");
    }
    say!(
        out,
        "checklist: {} listed, {} not needed{}",
        list.alts.len() + list.words.len(),
        unneeded.len(),
        names(&mut unneeded.iter().map(|u| u.0))
    );
    for (entry, row, why) in &unneeded {
        say!(
            out,
            "  `{entry}`, in the row L{row} of Part A of {name}, is not needed: {why}."
        );
    }
    if missing.is_empty() && unneeded.is_empty() {
        return Ok(true);
    }
    say!(
        out,
        "To repair {name}: make Part A list exactly what {} needs. Add each missing entry to the \
         row of its layer, and take out each entry that is not needed. When a change to the \
         grammar inserted or removed an alternative, the rule's later alternatives move up or \
         down by one: the entry under its old index is then not needed, and the same alternative \
         is missing under its new index.",
        needs.program
    );
    Ok(false)
}
