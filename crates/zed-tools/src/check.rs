//! The grammar checker. `check SPEC_DIR [FILE:LINE [any]]` checks that every reference of the
//! grammars resolves, that no alternative of layer k requires a rule empty at ring k, that a
//! `~` alternative's layer is not above its rule's lowest, and that the `desugar` fence has one
//! rule per production. It then lexes and parses every ```` ```zed ```` fence of `DESIGN.md` and
//! `EXAMPLES.md`, finds each fence's lowest ring, and checks that the parse tree is the same at
//! every higher ring. FILE:LINE checks that fence only; a third argument lists every fence's
//! ring.

use std::collections::{BTreeMap, BTreeSet};

use zedc::parse::{Expr, Grammar, TOP, marked_rule};

use crate::spec::{Spec, fence_texts};
use crate::syntax::{Tokens, Tree, lex, parse};
use crate::text::strip;
use crate::{Outcome, arg, say};

/// Every sub-expression `e` holds that `descend` allows, in order, `e` included: `visit` sees
/// each.
fn each<'g>(e: &'g Expr, descend: fn(&'g Expr) -> Vec<&'g Expr>, mut visit: impl FnMut(&'g Expr)) {
    let mut stack = vec![e];
    while let Some(e) = stack.pop() {
        visit(e);
        stack.extend(descend(e).into_iter().rev());
    }
}

/// The expressions directly inside `e`.
fn inner(e: &Expr) -> Vec<&Expr> {
    match e {
        Expr::Seq(xs) | Expr::Choice(xs) => xs.iter().collect(),
        Expr::Sep(items) => {
            let [sep, x] = &**items;
            vec![x, sep]
        }
        Expr::Star(x)
        | Expr::Plus(x)
        | Expr::Opt(x)
        | Expr::And(x)
        | Expr::Not(x)
        | Expr::SetHead(x)
        | Expr::ClearHead(x) => vec![x],
        Expr::Lit(_)
        | Expr::Rule(_)
        | Expr::Kind(_)
        | Expr::Head
        | Expr::Class(_)
        | Expr::Any
        | Expr::XidStart
        | Expr::XidContinue
        | Expr::Undefined(_) => Vec::new(),
    }
}

/// The expressions directly inside `e` that `e` cannot match without.
fn required(e: &Expr) -> Vec<&Expr> {
    match e {
        Expr::Seq(xs) => xs.iter().collect(),
        Expr::Plus(x) | Expr::SetHead(x) | Expr::ClearHead(x) => vec![x],
        Expr::Sep(items) => vec![&items[1]],
        Expr::Lit(_)
        | Expr::Rule(_)
        | Expr::Kind(_)
        | Expr::Head
        | Expr::Choice(_)
        | Expr::Star(_)
        | Expr::Opt(_)
        | Expr::And(_)
        | Expr::Not(_)
        | Expr::Class(_)
        | Expr::Any
        | Expr::XidStart
        | Expr::XidContinue
        | Expr::Undefined(_) => Vec::new(),
    }
}

/// Reports every undefined name in `g`, and how many there are.
fn undefined(g: &Grammar, out: &mut String) -> usize {
    let mut n = 0;
    for rule in &g.rules {
        for alt in &rule.alts {
            each(&alt.expr, inner, |e| {
                if let Expr::Undefined(name) = e {
                    say!(out, "UNDEFINED {name} in {}", rule.name);
                    n += 1;
                }
            });
        }
    }
    n
}

/// Reports every alternative that requires a rule empty at its layer, and how many there are.
fn containment(g: &Grammar, out: &mut String) -> usize {
    let lowest = g.lowest_layers();
    let mut n = 0;
    for rule in &g.rules {
        for (i, alt) in rule.alts.iter().enumerate() {
            each(&alt.expr, required, |e| {
                if let &Expr::Rule(r) = e
                    && lowest[r] > alt.layer
                {
                    say!(
                        out,
                        "LAYER {} alternative {} (L{}) requires {}, empty below L{}",
                        rule.name,
                        i + 1,
                        alt.layer,
                        g.rules[r].name,
                        lowest[r]
                    );
                    n += 1;
                }
            });
        }
    }
    n
}

/// Reports every `~` alternative above the lowest layer of the rule it marks, and how many
/// there are: such an alternative builds no node, so its layer would be reported by none.
fn marks(g: &Grammar, out: &mut String) -> usize {
    let lowest = g.lowest_layers();
    let mut n = 0;
    for rule in &g.rules {
        for (i, alt) in rule.alts.iter().enumerate() {
            let marked = alt.pass.then(|| marked_rule(&alt.expr)).flatten();
            if let Some(r) = marked
                && lowest[r] < alt.layer
            {
                say!(
                    out,
                    "MARK {} alternative {} (L{}) marks {}, whose lowest layer is L{}",
                    rule.name,
                    i + 1,
                    alt.layer,
                    g.rules[r].name,
                    lowest[r]
                );
                n += 1;
            }
        }
    }
    n
}

/// Checks that the `desugar` fences have one rule per production of `syn` and no other rule,
/// and says how many problems there are.
fn desugar(design: &str, syn: &Grammar, out: &mut String) -> Result<usize, String> {
    let fences = fence_texts(design, "desugar")?;
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    let mut total = 0;
    for f in &fences {
        for l in f.split('\n').filter(|l| !strip(l).is_empty()) {
            let name = strip(l.split(':').next().expect("split yields one item"));
            *counts.entry(name).or_default() += 1;
            total += 1;
        }
    }
    let order: BTreeSet<&str> = syn.rules.iter().map(|r| r.name.as_str()).collect();
    let mut problems = 0;
    for n in order.iter().filter(|n| !counts.contains_key(*n)) {
        say!(out, "DESUGAR missing a rule for {n}");
        problems += 1;
    }
    for n in counts.keys().filter(|n| !order.contains(*n)) {
        say!(out, "DESUGAR rule for no production: {n}");
        problems += 1;
    }
    for (n, _) in counts.iter().filter(|(_, c)| **c > 1) {
        say!(out, "DESUGAR two rules for {n}");
        problems += 1;
    }
    say!(out, "desugar rules {total} productions {}", syn.rules.len());
    Ok(problems)
}

/// What one fence came to.
enum Fenced {
    /// It has a lowest ring.
    Ring(u32),
    /// It failed before it had one.
    Failed,
}

/// The lowest ring at which `toks` parses from `start` in `g`, reporting a tree that changes
/// above it. A fence that parses at no ring below the full one has the full ring.
fn lowest_ring(
    spec: &Spec,
    g: &Grammar,
    toks: &Tokens,
    start: &str,
    site: &str,
    bad: &mut usize,
    out: &mut String,
) -> u32 {
    for k in 1..=TOP {
        let Ok(t) = parse(g, &spec.lexical, toks, k, start) else {
            continue;
        };
        for k2 in k + 1..=TOP {
            let same = parse(g, &spec.lexical, toks, k2, start).is_ok_and(|t2| t2.same(&t));
            if !same {
                say!(out, "{site} TREE CHANGES between L{k} and L{k2}");
                *bad += 1;
                break;
            }
        }
        return k;
    }
    TOP
}

/// Whether the documentation fence with tree `t` uses a signature, a remap form or a trailing
/// expression: a fence that uses only `DocItem`'s first alternative, `Item`, is a program that
/// failed as a `Unit`.
fn doc_uses_notation(spec: &Spec, t: &Tree) -> bool {
    let rule = |c: &usize| spec.all.rules[t.node(*c).rule].name.as_str();
    t.node(t.root)
        .kids
        .iter()
        .any(|c| matches!(rule(c), "Expr" | "DocItem"))
}

/// Checks one fence.
fn fence(
    spec: &Spec,
    site: &str,
    text: &str,
    docs: &mut Vec<String>,
    bad: &mut usize,
    out: &mut String,
) -> Fenced {
    let toks = match lex(&spec.lexical, &text.replace('…', "elided")) {
        Ok(toks) => toks,
        Err(e) => {
            say!(out, "{site} LEX {e}");
            *bad += 1;
            return Fenced::Failed;
        }
    };
    let (g, start) = match parse(&spec.syntactic, &spec.lexical, &toks, TOP, "Unit") {
        Ok(_) => (&spec.syntactic, "Unit"),
        Err(_) => match parse(&spec.all, &spec.lexical, &toks, TOP, "DocFence") {
            Ok(t) => {
                docs.push(site.into());
                if !doc_uses_notation(spec, &t) {
                    say!(
                        out,
                        "{site} DOC uses no signature, remap form or trailing expression"
                    );
                    *bad += 1;
                }
                (&spec.all, "DocFence")
            }
            Err(why) => {
                say!(out, "{site} FAIL {why}");
                *bad += 1;
                return Fenced::Failed;
            }
        },
    };
    Fenced::Ring(lowest_ring(spec, g, &toks, start, site, bad, out))
}

/// Runs the tool.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    let root = arg(args, 0, "check SPEC_DIR [FILE:LINE [any]]")?;
    let spec = Spec::open(root)?;
    let only = args.get(1).map_or("", String::as_str);
    let mut undef = undefined(&spec.lexical, out) + undefined(&spec.all, out);
    let lint = containment(&spec.lexical, out)
        + containment(&spec.all, out)
        + marks(&spec.lexical, out)
        + marks(&spec.all, out);
    undef += desugar(&spec.design, &spec.syntactic, out)?;
    let mut bad = lint + undef;
    let before_fences = bad;
    let mut rings: BTreeMap<(String, usize), u32> = BTreeMap::new();
    let mut docs = Vec::new();
    for f in spec.all_fences()? {
        let site = format!("{}:{}", f.file, f.line);
        if !only.is_empty() && site != only {
            continue;
        }
        match fence(&spec, &site, &f.text, &mut docs, &mut bad, out) {
            Fenced::Ring(k) => {
                rings.insert((f.file, f.line), k);
            }
            Fenced::Failed => {}
        }
    }
    if !only.is_empty() && rings.is_empty() && bad == before_fences {
        say!(out, "NO FENCE AT {only}");
        bad += 1;
    }
    let mut hist: BTreeMap<u32, usize> = BTreeMap::new();
    for &k in rings.values() {
        *hist.entry(k).or_default() += 1;
    }
    let histogram: Vec<String> = hist.iter().map(|(k, n)| format!("{k}: {n}")).collect();
    say!(out, "documentation-notation fences: {}", docs.join(" "));
    say!(
        out,
        "parsed {} failed {bad} ring histogram {{{}}}",
        rings.len(),
        histogram.join(", ")
    );
    if args.len() > 2 {
        for ((file, line), k) in &rings {
            say!(out, "{file} {line} L{k}");
        }
    }
    say!(out, "RESULT: {}", if bad == 0 { "OK" } else { "FAIL" });
    Ok(bad == 0)
}
