//! `layer SPEC_DIR steps`: the layer audit of the plan's steps (author P254, row
//! LAYER-steps-check), rerun by the tool instead of by hand. Each code span of each step of
//! DESIGN.md sec:steps, `Lk.n. …` and the paragraphs after it up to the next step or heading,
//! fences left out, is parsed at each ring in eleven readings: as a unit, as a declaration
//! (`span;`), as an expression (`x = span;`), as a type (`f(x: span) = 0;`), as a parameter
//! (`f(span) = 0;`), as a type's suffix (`f(x: int span) = 0;`) and range
//! (`f(x: int[span]) = 0;`), as a pattern (`f(v) = match v { span -> 0 };`), as a function
//! head (`span = 0;`), as an argument (`x = f(span);`) and as an annotation (`span` on
//! `f() = 0;`). A span no
//! reading of which parses at the ring of its step is listed, with the lowest ring above it at
//! which one does, as allowed when the sentence holding it names a later layer or step (`L5`,
//! `step L5.2`), or says the form is refused or is an error there, and as not allowed
//! otherwise: a step that uses a form of a later layer in its own work.
//!
//! What the tool does not see, reported with its counts: spans that parse in no reading
//! (prose in backticks, elided code, grammar rule names), the S and M0 steps (the scaffolding,
//! which has no layer of the language), forms a step names in words with no code span, and
//! the boundaries enforced after parsing (as `main::files` at L1 and every other `::` read at
//! L3, sec:grammar), which the grammar's rings do not express.
//!
//! Cost: each span is lexed once per reading and parsed at most once per ring and reading
//! (twice per reading unless it is listed), with `TOP` rings and eleven readings fixed, so the
//! whole run is O(total length of the spans) besides one pass over DESIGN.md to find them; the
//! parser is a packrat parser, linear in its
//! input (Ford 2002, "Packrat parsing: simple, powerful, lazy, linear time", ICFP,
//! doi:10.1145/581478.581483; the claim that this parser memoizes every rule is from memory of
//! crates/zedc-syntax/src/parse, not checked here). On DESIGN.md of 2026-11-23 (11353 spans)
//! the audit in the optimized test profile took under 11 s on a Colab VM, test start included,
//! with eight readings each parsed at the full ring first; with eleven, it took 25 s that way
//! and 8.2 s with a span stopping at its first reading that parses at its step's ring
//! (b22-small10).

use zedc::parse::TOP;

use crate::spec::Spec;
use crate::syntax::{lex, parse};
use crate::text::read_text;
use crate::{Outcome, say};

/// The non-empty backtick spans of `s`, for this audit and for the table of words (`super`).
pub(crate) fn spans(s: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut rest = s;
    while let Some(a) = rest.find('`') {
        let after = &rest[a + 1..];
        let Some(b) = after.find('`') else { break };
        if b == 0 {
            rest = after;
        } else {
            out.push(&after[..b]);
            rest = &after[b + 1..];
        }
    }
    out
}

/// A span listed: its step, the step's layer, the span, its ring and whether its sentence
/// allows it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Listed {
    /// The step, as `L1.13`.
    pub step: String,
    /// The step's layer.
    pub layer: u32,
    /// The span's text.
    pub span: String,
    /// The lowest ring above the step's layer at which the span parses in some reading.
    pub ring: u32,
    /// Whether its sentence names a later layer or step or a refusal.
    pub allowed: bool,
}

/// The audit of the steps.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Audit {
    /// The spans whose ring is above their step's layer, in the order of DESIGN.md.
    pub listed: Vec<Listed>,
    /// The spans of the steps of a layer.
    pub spans: usize,
    /// Of those, the spans that parse in no reading at any ring.
    pub unread: usize,
    /// The S and M0 steps, which are not read.
    pub other_steps: usize,
}

/// The step id and layer of a line that starts a step, `L12.3a. …` giving `("L12.3a", 12)`;
/// `Some((id, None))` for an S or M0 step; `None` for any other line.
fn step_of(line: &str) -> Option<(&str, Option<u32>)> {
    let (id, rest) = line.split_once(". ")?;
    let (head, num) = id.split_once('.')?;
    let tail_ok = !num.is_empty()
        && num.starts_with(|c: char| c.is_ascii_digit())
        && num.chars().all(|c| c.is_ascii_alphanumeric() || c == '.');
    if !tail_ok || rest.is_empty() {
        return None;
    }
    match head {
        "S" | "M0" => Some((id, None)),
        _ => {
            let k = head.strip_prefix('L')?.parse().ok()?;
            Some((id, Some(k)))
        }
    }
}

/// `None` when `span` parses in none of the eleven readings at the full ring; else `Some(0)`
/// when some reading parses at the ring `layer` of its step, the test of the row; else
/// `Some(r)`, the lowest ring above `layer` at which some reading parses. Most spans stop at
/// the first reading that parses at `layer`, with one more parse of it at the full ring; the
/// rings above `layer` are tried only for a span that fails at `layer`. A grammar of ordered choice need not be monotone in
/// its rings (an alternative a ring adds can take input a later alternative would have read,
/// which `ring::ring_of` reports as a tree that changes), so the span is read at its step's
/// ring itself rather than compared with its lowest ring.
fn ring(spec: &Spec, span: &str, layer: u32) -> Option<u32> {
    let span = span.replace('…', "elided");
    let readings = [
        span.clone(),
        format!("{span};"),
        format!("x = {span};"),
        format!("f(x: int{span}) = 0;"),
        format!("f(x: int[{span}]) = 0;"),
        format!("f(x: {span}) = 0;"),
        format!("f({span}) = 0;"),
        format!("f(v) = match v {{ {span} -> 0 }};"),
        // The three places prose writes a fragment of a declaration or a call (row
        // LAYER-steps-check): a function head, `h(positional z: f64)`, read as the head of a
        // declaration; a named argument, `punct: "?"`, read as the argument of a call; and an
        // annotation written alone, `@invariant`, read on a declaration. Each wraps the span
        // in a context the grammar of the span's own ring has, so a reading parses at a ring
        // only when the span is a form of that ring in that place: a span of a later form
        // still fails every reading at its step's ring, and is listed as before.
        format!("{span} = 0;"),
        format!("x = f({span});"),
        format!("{span}\nf() = 0;"),
    ];
    let (syn, lexical) = (&spec.syntactic, &spec.lexical);
    let at = |t: &_, k| parse(syn, lexical, t, k, "Unit").is_ok();
    let lexed: Vec<_> = readings
        .iter()
        .filter_map(|r| lex(lexical, r).ok())
        .collect();
    // `Some(0)` exactly when some reading parses at the full ring and at the step's ring, as
    // below; tried first, reading by reading, so a span of its step's ring (most spans) stops
    // at the first reading that parses, two parses, instead of parsing every reading at the
    // full ring first (the readings are many, eleven, and most spans read in the first few).
    if lexed.iter().any(|t| at(t, layer.min(TOP)) && at(t, TOP)) {
        return Some(0);
    }
    let toks: Vec<_> = lexed.into_iter().filter(|t| at(t, TOP)).collect();
    if toks.is_empty() {
        return None;
    }
    (layer + 1..=TOP).find(|&k| toks.iter().any(|t| at(t, k)))
}

/// Whether `sentence` names a layer or step above `layer` (`L5`, `L5.2`), or says that what it
/// holds is refused or an error.
fn allows(sentence: &str, layer: u32) -> bool {
    let lower = sentence.to_lowercase();
    if ["refus", "reject", "error", "not supported"]
        .iter()
        .any(|w| lower.contains(w))
    {
        return true;
    }
    let b = sentence.as_bytes();
    (0..b.len()).any(|i| {
        b[i] == b'L'
            && (i == 0 || !b[i - 1].is_ascii_alphanumeric())
            && sentence[i + 1..]
                .split(|c: char| !c.is_ascii_digit())
                .next()
                .and_then(|d| d.parse::<u32>().ok())
                .is_some_and(|k| k > layer)
    })
}

/// The sentences of `para`: split after `. ` outside code spans.
fn sentences(para: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let (mut start, mut code) = (0, false);
    let b = para.as_bytes();
    for i in 0..b.len() {
        match b[i] {
            b'`' => code = !code,
            b'.' if !code && b.get(i + 1) == Some(&b' ') => {
                out.push(&para[start..=i]);
                start = i + 2;
            }
            _ => {}
        }
    }
    if start < para.len() {
        out.push(&para[start..]);
    }
    out
}

/// The audit of the steps in `design`, the text of DESIGN.md, with the grammars of `spec`.
pub fn audit(spec: &Spec, design: &str) -> Audit {
    let mut a = Audit::default();
    let start = design.find("(sec:steps)").unwrap_or(design.len());
    let section = &design[start..];
    let end = ["\n# ", "\n## "]
        .iter()
        .filter_map(|h| section.find(h))
        .min()
        .unwrap_or(section.len());
    // The paragraphs of the section outside fences; a paragraph that starts no step belongs to
    // the step before it, up to the next heading.
    let mut paras = vec![String::new()];
    let mut fenced = false;
    for line in section[..end].lines() {
        if line.trim_start().starts_with("```") {
            fenced = !fenced;
            paras.push(String::new());
        } else if fenced {
            continue;
        } else if line.trim().is_empty() || line.starts_with('#') {
            paras.push(String::new());
            if line.starts_with('#') {
                paras.push("#".into());
            }
        } else {
            let p = paras.last_mut().expect("one paragraph at least");
            p.push_str(line.trim());
            p.push(' ');
        }
    }
    let mut step = None;
    for para in &paras {
        let para = para.trim();
        if para == "#" {
            step = None;
            continue;
        }
        match step_of(para) {
            Some((id, Some(k))) => step = Some((id.to_string(), k)),
            Some((_, None)) => {
                a.other_steps += 1;
                step = None;
            }
            None => {}
        }
        let Some((id, layer)) = &step else {
            continue;
        };
        let (id, layer) = (id.as_str(), *layer);
        for sentence in sentences(para) {
            for span in spans(sentence) {
                a.spans += 1;
                match ring(spec, span, layer) {
                    None => a.unread += 1,
                    Some(r) if r > 0 => a.listed.push(Listed {
                        step: id.to_string(),
                        layer,
                        span: span.to_string(),
                        ring: r,
                        allowed: allows(sentence, layer),
                    }),
                    Some(_) => {}
                }
            }
        }
    }
    a
}

/// Prints the audit of `spec`'s DESIGN.md; fails if a span is listed that its sentence does
/// not allow.
pub fn report(spec: &Spec, out: &mut String) -> Outcome {
    let a = audit(spec, &read_text(&spec.design)?);
    let mut bad = 0;
    for l in &a.listed {
        let how = if l.allowed { "allowed" } else { "NOT ALLOWED" };
        say!(
            out,
            "{} (L{}) `{}` needs L{}: {how}",
            l.step,
            l.layer,
            l.span,
            l.ring
        );
        bad += usize::from(!l.allowed);
    }
    say!(
        out,
        "{} spans in the steps of a layer, {} listed, {} not allowed; not read: {} spans that \
         parse in no reading, {} S and M0 steps, forms named in words, and the boundaries \
         enforced after parsing",
        a.spans,
        a.listed.len(),
        bad,
        a.unread,
        a.other_steps
    );
    Ok(bad == 0)
}
