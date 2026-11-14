//! Every alternative of every rule of sec:grammar, and every item written in it, is matched by
//! a case: the cases of `grammar_cases.rs`, one or more per alternative, and the bracketing
//! cases of `zed/grammar/cases.txt`. Each case of `grammar_cases.rs` also checks the layer tag of
//! its alternative: the alternative is tried at the ring of its layer and not one ring below.

use std::collections::{BTreeSet, HashSet};
use std::path::Path;

use zed_tests::trees::sx;
use zedc::lex::{Tok, Token, lex};
use zedc::parse::{Expr, Grammar, Kind, TOP, Tree, grammar, literal_matches, marked_rule, parse};

use super::grammar_cases::CASES;

/// The kind the grammar gives the token `t`, as `IDENT`, `INT` and the rest name it.
fn kind(t: &Tok) -> Kind {
    match t {
        Tok::Name(_) => Kind::Ident,
        Tok::Wildcard => Kind::Wild,
        Tok::Int { .. } => Kind::Int,
        Tok::Float { .. } => Kind::Float,
        Tok::Rat(_) => Kind::Rat,
        Tok::Str(_) => Kind::Str,
        Tok::Atom(_) => Kind::Atom,
        Tok::Annot(_) => Kind::Annot,
        Tok::Keyword(_) => Kind::Keyword,
        Tok::Op(_) => Kind::Op,
    }
}

/// The positions the parser reads, as `parse` builds them: each token's kind and text, then
/// one `END` position.
fn positions<'t>(text: &'t str, tokens: &[Token]) -> Vec<(Kind, &'t str)> {
    tokens
        .iter()
        .map(|t| (kind(&t.tok), &text[t.span.start..t.span.end]))
        .chain([(Kind::End, "")])
        .collect()
}

/// The text of the positions `start..end`, joined by one space; `END` has none.
fn span_text(toks: &[(Kind, &str)], start: usize, end: usize) -> String {
    toks[start..end]
        .iter()
        .filter(|(k, _)| *k != Kind::End)
        .map(|(_, t)| *t)
        .collect::<Vec<_>>()
        .join(" ")
}

/// `(rule, alt)` of the label `Rule#k`.
fn label(g: &Grammar, l: &str) -> (usize, usize) {
    let (name, k) = l.split_once('#').expect("a label is `Rule#k`");
    let r = g
        .rule(name)
        .unwrap_or_else(|| panic!("{l}: no rule {name}"));
    let k: usize = k.parse().expect("`k` in `Rule#k` is a number");
    assert!(
        k < g.rules[r].alts.len(),
        "{l}: {name} has no alternative {k}"
    );
    (r, k)
}

/// The rules whose node a match of rule `r` can be: `r` and, through its `~` alternatives, the
/// rules those mark, and so on. A visited set stops at each rule's first visit.
fn reach(g: &Grammar, r: usize) -> HashSet<usize> {
    let mut seen = HashSet::from([r]);
    let mut work = vec![r];
    while let Some(r) = work.pop() {
        for alt in g.rules[r].alts.iter().filter(|a| a.pass) {
            let m = marked_rule(&alt.expr).expect("a `~` alternative marks a rule");
            if seen.insert(m) {
                work.push(m);
            }
        }
    }
    seen
}

/// An item of an alternative that matches input: a literal, a token kind, or a rule.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Item {
    Lit(String),
    Kind(String),
    Rule(usize),
}

/// The items of `e` outside lookaheads, each once.
fn items(e: &Expr, out: &mut BTreeSet<Item>) {
    match e {
        Expr::Lit(s) => {
            out.insert(Item::Lit(s.clone()));
        }
        Expr::Kind(k) => {
            out.insert(Item::Kind(format!("{k:?}")));
        }
        Expr::Rule(r) => {
            out.insert(Item::Rule(*r));
        }
        Expr::Seq(es) | Expr::Choice(es) => es.iter().for_each(|e| items(e, out)),
        Expr::Sep(pair) => pair.iter().for_each(|e| items(e, out)),
        Expr::Star(e) | Expr::Plus(e) | Expr::Opt(e) | Expr::SetHead(e) | Expr::ClearHead(e) => {
            items(e, out)
        }
        Expr::And(_) | Expr::Not(_) | Expr::Head => {}
        Expr::Class(_) | Expr::Any | Expr::Undefined(_) => {
            panic!("the syntactic grammar has no character classes, ANY or undefined names")
        }
    }
}

/// Adds to `seen` each item that a node of `tree` matched, as `(rule, alt, item)`: a position
/// outside every child is a literal or a kind (`END` among them); a child is a rule whose reach
/// holds the child's rule.
fn matched(
    g: &Grammar,
    reaches: &[HashSet<usize>],
    toks: &[(Kind, &str)],
    tree: &Tree,
    seen: &mut HashSet<(usize, usize, Item)>,
) {
    for node in &tree.nodes {
        let mut want = BTreeSet::new();
        items(&g.rules[node.rule].alts[node.alt].expr, &mut want);
        let mut own = vec![true; node.end - node.start];
        for &kid in &node.kids {
            let k = &tree.nodes[kid];
            own[k.start - node.start..k.end - node.start].fill(false);
        }
        let direct = (node.start..node.end)
            .filter(|i| own[i - node.start])
            .map(|i| toks[i]);
        for item in want {
            let hit = match &item {
                Item::Lit(s) => direct.clone().any(|(k, t)| literal_matches(k, t, s)),
                Item::Kind(want) => direct.clone().any(|(k, _)| format!("{k:?}") == *want),
                Item::Rule(r) => node
                    .kids
                    .iter()
                    .any(|&kid| reaches[*r].contains(&tree.nodes[kid].rule)),
            };
            if hit {
                seen.insert((node.rule, node.alt, item));
            }
        }
    }
}

#[test]
fn each_case_builds_its_alternative_at_its_layer_and_not_one_ring_below() {
    let g = grammar();
    let mut wrong = Vec::new();
    for &(l, start, ring, text, want) in CASES {
        let (r, k) = label(g, l);
        let alt = &g.rules[r].alts[k];
        let at = if ring == 0 { alt.layer } else { ring };
        let tokens = lex(text).unwrap_or_else(|e| panic!("{l} | {text}: {e}"));
        let toks = positions(text, &tokens);
        let tree = match parse(text, &tokens, start, at) {
            Ok(t) => t,
            Err(e) => {
                wrong.push(format!(
                    "{l} | {start}@{at} | {text}\n  does not parse: {e}"
                ));
                continue;
            }
        };
        let found = if alt.pass {
            // A `~` alternative builds no node: the parse from the rule itself is the node of
            // a rule the mark reaches, over the whole text, and no node of the rule is over it.
            let m = marked_rule(&alt.expr).expect("a `~` alternative marks a rule");
            let root = &tree.nodes[tree.root];
            start == g.rules[r].name
                && reach(g, m).contains(&root.rule)
                && root.start == 0
                && root.end >= tokens.len()
                && span_text(&toks, 0, toks.len()) == want
        } else {
            tree.nodes
                .iter()
                .any(|n| (n.rule, n.alt) == (r, k) && span_text(&toks, n.start, n.end) == want)
        };
        if !found {
            wrong.push(format!(
                "{l} | {start}@{at} | {text}\n  no node `{want}` of this alternative in {}",
                sx(text, &tokens, &tree)
            ));
            continue;
        }
        // One ring below its layer the alternative is not tried: the parse fails, or holds no
        // node of it (a `~` alternative: gives another tree).
        if alt.layer > 1 && at == alt.layer {
            let below = parse(text, &tokens, start, at - 1);
            let still = match &below {
                Err(_) => false,
                Ok(b) if alt.pass => sx(text, &tokens, b) == sx(text, &tokens, &tree),
                Ok(b) => b.nodes.iter().any(|n| (n.rule, n.alt) == (r, k)),
            };
            if still {
                wrong.push(format!(
                    "{l} | {start}@{} | {text}\n  still parses as this alternative one ring below its layer {}",
                    at - 1,
                    alt.layer
                ));
            }
        }
    }
    assert!(
        wrong.is_empty(),
        "{} of {} wrong:\n{}",
        wrong.len(),
        CASES.len(),
        wrong.join("\n")
    );
}

#[test]
fn every_alternative_of_every_rule_has_a_case() {
    let g = grammar();
    let have: HashSet<(usize, usize)> = CASES.iter().map(|c| label(g, c.0)).collect();
    let missing: Vec<String> = g
        .rules
        .iter()
        .enumerate()
        .flat_map(|(r, rule)| (0..rule.alts.len()).map(move |k| (r, k)))
        .filter(|rk| !have.contains(rk))
        .map(|(r, k)| format!("{}#{k}", g.rules[r].name))
        .collect();
    assert!(missing.is_empty(), "no case for: {}", missing.join(", "));
}

#[test]
fn every_item_of_every_alternative_is_matched_by_some_case() {
    let g = grammar();
    let reaches: Vec<HashSet<usize>> = (0..g.rules.len()).map(|r| reach(g, r)).collect();
    let mut seen = HashSet::new();
    let mut add = |text: &str, start: &str, ring: u32| {
        let tokens = lex(text).unwrap_or_else(|e| panic!("{start} | {text}: {e}"));
        if let Ok(tree) = parse(text, &tokens, start, ring) {
            matched(g, &reaches, &positions(text, &tokens), &tree, &mut seen);
        }
    };
    for &(l, start, ring, text, _) in CASES {
        let (r, k) = label(g, l);
        add(
            text,
            start,
            if ring == 0 {
                g.rules[r].alts[k].layer
            } else {
                ring
            },
        );
    }
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../zed/grammar");
    let cases = std::fs::read_to_string(dir.join("cases.txt")).expect("cases.txt reads");
    for line in cases
        .lines()
        .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
    {
        let [start, text, want] = line.split(" ::: ").map(str::trim).collect::<Vec<_>>()[..] else {
            panic!("a case is `Rule ::: text ::: tree`: {line}");
        };
        if want != "ERROR" {
            let (start, ring) = match start.split_once('@') {
                Some((s, r)) => (s, r.parse().expect("a ring is a number")),
                None => (start, TOP),
            };
            add(&text.replace('⏎', "\n"), start, ring);
        }
    }
    let mut missing = Vec::new();
    for (r, rule) in g.rules.iter().enumerate() {
        for (k, alt) in rule.alts.iter().enumerate().filter(|(_, a)| !a.pass) {
            let mut want = BTreeSet::new();
            items(&alt.expr, &mut want);
            for item in want {
                if !seen.contains(&(r, k, item.clone())) {
                    let shown = match item {
                        Item::Lit(s) => format!("'{s}'"),
                        Item::Kind(k) => k,
                        Item::Rule(x) => g.rules[x].name.clone(),
                    };
                    missing.push(format!("{}#{k}: {shown}", rule.name));
                }
            }
        }
    }
    assert!(
        missing.is_empty(),
        "{} items no case matches:\n{}",
        missing.len(),
        missing.join("\n")
    );
}
