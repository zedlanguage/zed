//! Recovery from syntax errors in a unit (step L1.29d; DESIGN.md sec:tooling, the parser
//! contract, and sec:diagnostics, row "Syntax error").
//!
//! A unit is parsed declaration by declaration, by the rule `Item`, on one table of rule
//! results by position. When a declaration fails, the parse resumes at the next line, past the
//! declaration's first line, that begins at the first column with a token other than a closing
//! bracket, so each top-level declaration reports at most one syntax error, and the
//! declarations that parse are built and checked as usual. A failing declaration begins at the
//! last line at or before its failure that begins at the first column in that way, so the head
//! of `f(x) = { … } test { … }`, which parses before a trailer that does not, is part of it.
//!
//! The error of a failing declaration is found by parsing its tokens alone, up to that line:
//! where that parse stops before the line, it stops where the parse of the unit stopped, since
//! no alternative read past the stopping token; where it reaches the line, the declaration was
//! left open there, and the error is reported at that line. Each failing declaration is read
//! once more this way, and the declarations do not overlap, so the extra work is linear in the
//! unit.

use std::collections::BTreeSet;
use std::ops::Range;

use super::case;
use super::clause::{self, Toks, depth, kind};
use super::engine::{Expected, Node, Parser};
use super::grammar::{Grammar, Kind};
use super::tree::{DOTS, Error, Recovery, Tree, dots_in_list, holes_of, parse_holes, shown};
use crate::lex::{Span, Token};

/// The tree of the unit `tokens`, lexed from `text`, parsed as the rule `unit` (`Item* END`)
/// declaration by declaration with the rule `item`, and the error of each declaration that
/// fails, in the order of the text. A declaration a string hole of which fails is left out
/// with that hole's error. `end` is the span reported for an error at the end of the text.
// Complexity tradeoff: restarting each attempt afresh, with a parser of its own from the
// declaration's first token, re-reads the tokens an earlier attempt read past the line it
// resumes at: O(n²) for n tokens when every declaration leaves a `(` open, since each attempt
// then reads to the end of the unit. Every attempt here reads the one table `p` fills, so a
// rule's result at a position is found once and the parse is linear in the unit, as one with
// no error is, for space linear in the unit (the table the parse of the unit fills anyway).
// Test: `l01_29_diagnostics::syntax_recovery::many_declarations_left_open_parse_in_linear_time`.
pub(super) fn recovering(
    g: &Grammar,
    text: &str,
    tokens: &[Token],
    unit: usize,
    item: usize,
    ring: u32,
    end: Span,
) -> (Tree, Vec<Error>) {
    let toks: Vec<(Kind, &str)> = tokens
        .iter()
        .map(|t| (kind(&t.tok), &text[t.span.start..t.span.end]))
        .chain([(Kind::End, "")])
        .collect();
    let mut p = Parser::new(g, ring, toks.as_slice());
    if let Some((_, root)) = p
        .rule_node(unit, 0, false)
        .filter(|&(e, _)| e + 1 >= toks.len())
        && let Ok(holes) = parse_holes(g, text, holes_of(tokens), ring)
    {
        let tree = Tree {
            nodes: p.nodes,
            root,
            holes,
            skipped: Vec::new(),
        };
        return (tree, Vec::new());
    }
    // Each declaration kept, with the number of holes kept before its own.
    let mut kids: Vec<(usize, usize)> = Vec::new();
    let mut holes = Vec::new();
    let mut skipped: Vec<Range<usize>> = Vec::new();
    let mut errors = Vec::new();
    let mut s = 0;
    while s < tokens.len() {
        if let Some((e, node)) = p.rule_node(item, s, false).filter(|&(e, _)| e > s) {
            match parse_holes(g, text, holes_of(&tokens[s..e]), ring) {
                Ok(h) => {
                    kids.push((node, holes.len()));
                    holes.extend(h);
                }
                Err(mut err) => {
                    err.recovery.defines = defines(&toks[s..e]);
                    errors.push(err);
                    skipped.push(s..e);
                }
            }
            s = e;
            continue;
        }
        // The failing declaration begins at its line: a declaration kept from that line, as
        // the head of `f(x) = { … } test { … }` before a trailer that fails, is part of it.
        let floor = skipped.last().map_or(0, |d| d.end);
        let b = begins_at(text, tokens, s, floor);
        let mut dropped = Vec::new();
        while let Some(&(node, h)) = kids.last()
            && p.nodes[node].start >= b
        {
            kids.pop();
            holes.truncate(h);
            dropped.extend(defines(&toks[p.nodes[node].start..p.nodes[node].end]));
        }
        let r = resumes_at(text, tokens, s);
        let mut err = declaration(g, ring, unit, text, tokens, &toks, b..r, end);
        err.recovery.defines.extend(dropped);
        errors.push(err);
        skipped.push(b..r);
        s = r;
    }
    errors.sort_by_key(|e| e.span);
    let root = p.nodes.len();
    p.nodes.push(Node {
        rule: unit,
        alt: 0,
        start: 0,
        end: toks.len(),
        kids: kids.into_iter().map(|(k, _)| k).collect(),
        branches: Vec::new(),
    });
    let tree = Tree {
        nodes: p.nodes,
        root,
        holes,
        skipped,
    };
    (tree, errors)
}

/// The token the parse resumes at after a declaration that fails from token `s`: the first
/// token after `s` that begins a line at the first column and is no closing bracket, since a
/// `}` at the first column closes the declaration above it; or the end. O(the tokens passed).
fn resumes_at(text: &str, tokens: &[Token], s: usize) -> usize {
    (s + 1..tokens.len())
        .find(|&j| begins_declaration(text, &tokens[j]))
        .unwrap_or(tokens.len())
}

/// The token the declaration that fails at token `s` begins at: the last token from `floor` to
/// `s` that begins a line at the first column and is no closing bracket, or `floor`. The tokens
/// read lie between the end of the last declaration skipped and the next failure, so over the
/// unit each is read at most once.
fn begins_at(text: &str, tokens: &[Token], s: usize, floor: usize) -> usize {
    (floor..=s)
        .rev()
        .find(|&j| begins_declaration(text, &tokens[j]))
        .unwrap_or(floor)
}

/// Whether `t` begins a line at the first column with a token other than a closing bracket.
fn begins_declaration(text: &str, t: &Token) -> bool {
    let starts_line = t.span.start == 0 || text.as_bytes().get(t.span.start - 1) == Some(&b'\n');
    starts_line && depth(&text[t.span.start..t.span.end]) >= 0
}

/// The error of the declaration of tokens `d` of the unit, which fails: its tokens are parsed
/// alone as a unit, and the error is where that parse stops, or at the token after `d` when
/// it reads to the end of them. O(t·m) for a declaration of m tokens and t kinds of token.
#[allow(clippy::too_many_arguments)]
fn declaration(
    g: &Grammar,
    ring: u32,
    unit: usize,
    text: &str,
    tokens: &[Token],
    toks: &[(Kind, &str)],
    d: Range<usize>,
    end: Span,
) -> Error {
    let m = d.len();
    let mut alone: Vec<(Kind, &str)> = Vec::with_capacity(m + 1);
    alone.extend_from_slice(&toks[d.clone()]);
    alone.push((Kind::End, ""));
    // The token after the declaration stands where the parse alone reads its end.
    let after = tokens.get(d.end).map_or(end, |t| t.span);
    let t = Toks {
        g,
        ring,
        start: unit,
        text,
        tokens: &tokens[d.clone()],
        toks: &alone,
        end: after,
    };
    let mut p = Parser::new(g, ring, alone.as_slice());
    let far = match p.rule_node(unit, 0, false) {
        Some((e, _)) if e + 1 >= alone.len() => m,
        Some((e, _)) => {
            p.fail(e, Expected::Name("END"));
            p.far
        }
        None => p.far,
    };
    // The parse alone reads the end of its tokens where the unit has the next line, so `END`
    // is no token the program could write there.
    let ended = far == m;
    // A repair inserts only a token that separates or closes what is written, never one that
    // stands for a value the program did not write.
    let literals: Vec<String> = p
        .expected_in_order()
        .into_iter()
        .filter_map(|e| match e {
            Expected::Lit(s @ (")" | "]" | "}" | ";" | "," | "=")) => Some(s.to_string()),
            _ => None,
        })
        .collect();
    let expected: Vec<String> = p
        .expected_in_order()
        .iter()
        .map(shown)
        .filter(|e| !(ended && e == "END"))
        .collect();
    let defines = defines(&alone[..m]);
    let dots = dots_in_list(&alone, far);
    let found = case::case_item(&t, far).or_else(|| clause::clause(&t, far));
    let mut out = Error {
        span: t.span(dots.unwrap_or(far)),
        expected,
        message: dots.map(|_| DOTS),
        clause: found.map(Box::new),
        recovery: Box::new(Recovery {
            defines,
            ..Recovery::default()
        }),
    };
    if out.clause.is_some() || out.message.is_some() {
        return out;
    }
    // The constructs still open where the parse stopped, outermost first: the declaration,
    // then each bracket not closed before that token.
    let mut open: Vec<usize> = Vec::new();
    for i in 0..far.min(m) {
        match depth(t.t(i)) {
            1 => open.push(i),
            -1 => {
                open.pop();
            }
            _ => {}
        }
    }
    if far > 0 {
        out.recovery.notes.push((
            t.span(0),
            match out.recovery.defines.first() {
                Some(name) => format!("the declaration of `{name}` begins here"),
                None => "the declaration begins here".into(),
            },
        ));
    }
    // The token the parse stopped at, as the program writes it.
    let stop = match &text[after.start..after.end] {
        _ if far < m => format!("at `{}`", t.t(far)),
        "" => "at the end of the text".to_string(),
        s => format!("at `{s}`"),
    };
    let stop = if stop.contains(['\n']) || stop.matches('`').count() > 2 {
        "where the parse stops".to_string()
    } else {
        stop
    };
    for &i in &open {
        let called = i > 0 && alone[i - 1].0 == Kind::Ident && t.t(i) == "(";
        let what = if called {
            format!("{}(", t.t(i - 1))
        } else {
            t.t(i).to_string()
        };
        out.recovery.notes.push((
            t.span(i),
            format!("`{what}` opens here and is still open {stop}"),
        ));
    }
    if far == m && d.end < tokens.len() {
        out.recovery.notes.push((
            after,
            "this line begins at the first column, so it begins the next declaration".into(),
        ));
    }
    out.recovery.repairs = repairs(&t, &alone, far, &open, literals);
    out
}

/// One edit of a failing declaration: before token `at`, delete `delete` tokens and insert
/// `insert`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Edit {
    at: usize,
    delete: usize,
    insert: String,
}

/// The repairs of the declaration `t` (its tokens `alone`, ending in `END`) whose parse alone
/// stops at token `far`, with the brackets `open` not closed there: each as the corrected
/// source line, placed at the edit. In the order of the menu (DESIGN.md sec:diagnostics, row
/// "Syntax error"): each expected token inserted where the parse stopped, the token there
/// deleted, and the closing tokens of the open brackets at the end of the declaration, then
/// those followed by `;`, which a declaration whose body is an expression ends with. Each is
/// offered only when the declaration then parses.
// Complexity tradeoff: the naive menu re-parses the whole unit for each candidate repair,
// O(t·n) for an error in a unit of n tokens with t kinds of token, and O(t·n·e) for e errors.
// Each candidate here re-parses only the failing declaration, O(t·m) for a declaration of m
// tokens, and O(t·n) for the unit, since the declarations do not overlap. The price: a repair
// is judged by the failing declaration alone, never by whether it changes how a later one
// parses. Test:
// `l01_29_diagnostics::syntax_recovery::many_declarations_left_open_parse_in_linear_time`.
fn repairs(
    t: &Toks<'_, '_>,
    alone: &[(Kind, &str)],
    far: usize,
    open: &[usize],
    literals: Vec<String>,
) -> Vec<(Span, String)> {
    let m = alone.len() - 1;
    let closers: String = open
        .iter()
        .rev()
        .map(|&i| match t.t(i) {
            "(" => ')',
            "[" => ']',
            _ => '}',
        })
        .collect();
    let mut edits: Vec<Edit> = Vec::new();
    let mut tried = BTreeSet::new();
    let mut offer = |e: Edit| {
        if tried.insert(e.clone()) {
            edits.push(e);
        }
    };
    for e in literals {
        offer(Edit {
            at: far,
            delete: 0,
            insert: e,
        });
    }
    if far < m {
        offer(Edit {
            at: far,
            delete: 1,
            insert: String::new(),
        });
    }
    if !closers.is_empty() {
        offer(Edit {
            at: m,
            delete: 0,
            insert: closers.clone(),
        });
        offer(Edit {
            at: m,
            delete: 0,
            insert: format!("{closers};"),
        });
    }
    edits
        .into_iter()
        .filter(|e| parses(t, alone, e))
        .map(|e| shown_line(t, &e))
        .collect()
}

/// Whether the declaration `alone` with the edit `e` parses as a unit. O(m) for m tokens.
fn parses(t: &Toks<'_, '_>, alone: &[(Kind, &str)], e: &Edit) -> bool {
    let Ok(new) = crate::lex::lex(&e.insert) else {
        return false;
    };
    let mut fixed: Vec<(Kind, &str)> = Vec::with_capacity(alone.len() + new.len());
    fixed.extend_from_slice(&alone[..e.at]);
    fixed.extend(
        new.iter()
            .map(|n| (kind(&n.tok), &e.insert[n.span.start..n.span.end])),
    );
    fixed.extend_from_slice(&alone[e.at + e.delete..]);
    let mut p = Parser::new(t.g, t.ring, fixed.as_slice());
    matches!(p.rule_node(t.start, 0, false), Some((end, _)) if end + 1 >= fixed.len())
}

/// The source line the edit `e` falls on, from its first token to its last, with the edit
/// made, and the place of the edit. A closing bracket, `,`, `;` or `.`, and any token
/// inserted at the end of the declaration, follows the token before it; any other token
/// goes before the token at the edit, with a space after it. A deleted token takes the
/// spaces after it on its line when spaces or the start of the line come before it, and
/// those before it when it ends its line.
fn shown_line(t: &Toks<'_, '_>, e: &Edit) -> (Span, String) {
    let m = t.tokens.len();
    let word = |c: Option<char>| c.is_some_and(|c| c.is_alphanumeric() || c == '_');
    let attach = e.at == m
        || e.delete == 0
            && e.at > 0
            && matches!(
                e.insert.chars().next(),
                Some(')' | ']' | '}' | ',' | ';' | '.')
            );
    // The bytes replaced, the text put there, and the token whose line is shown.
    let (cut, put, near) = if e.delete > 0 {
        let s = t.span(e.at);
        let same_line = |a: usize, b: usize| !t.text[a..b].contains('\n');
        let next = (e.at + 1 < m).then(|| t.span(e.at + 1).start);
        let next = next.filter(|&n| same_line(s.end, n));
        let prev = (e.at > 0).then(|| t.span(e.at - 1).end);
        let prev = prev.filter(|&p| same_line(p, s.start));
        // Spaces on both sides, or a token first on its line: the spaces after it go too.
        let cut = match (prev, next) {
            (Some(p), Some(n)) if p < s.start => s.start..n,
            (None, Some(n)) => s.start..n,
            (Some(p), None) => p..s.end,
            _ => s.start..s.end,
        };
        (cut, String::new(), e.at)
    } else if attach {
        let at = t.span(e.at - 1).end;
        let space = word(t.text[..at].chars().next_back()) && word(e.insert.chars().next());
        let put = if space {
            format!(" {}", e.insert)
        } else {
            e.insert.clone()
        };
        (at..at, put, e.at - 1)
    } else {
        let at = t.span(e.at).start;
        (at..at, format!("{} ", e.insert), e.at)
    };
    let (a, b) = t.line(near);
    let (from, to) = (t.span(a).start.min(cut.start), t.span(b).end.max(cut.end));
    let line = format!("{}{put}{}", &t.text[from..cut.start], &t.text[cut.end..to]);
    let place = Span {
        start: cut.start,
        end: cut.end.max(cut.start),
    };
    (place, line)
}

/// The names the declaration `d` (its tokens) would define, had it parsed: a function's,
/// an indexed definition's, a binding's targets, a struct's, a type's, an interface's or a
/// law's name, and the names an import brings in, after its annotations and its `local`. A
/// use of one of them gets no row for a name that resolves to nothing (step L1.29d). O(m).
/// Several declarations that fail together, as on one line, are each read: they are split at
/// each `;` outside brackets.
pub(super) fn defines(d: &[(Kind, &str)]) -> Vec<String> {
    let mut out = Vec::new();
    let (mut level, mut from) = (0, 0);
    for (i, &(_, t)) in d.iter().enumerate() {
        level += depth(t);
        if level == 0 && t == ";" {
            out.extend(defines_first(&d[from..i]));
            from = i + 1;
        }
    }
    out.extend(defines_first(&d[from..]));
    out
}

/// The names the first declaration of `d` would define, as [`defines`] reads them.
fn defines_first(d: &[(Kind, &str)]) -> Vec<String> {
    let at = |k: usize| d.get(k).copied().unwrap_or((Kind::End, ""));
    let mut k = 0;
    loop {
        if at(k).0 == Kind::Annot {
            k += 1;
            if at(k).1 == "(" {
                let mut level = 0;
                while at(k).0 != Kind::End {
                    level += depth(at(k).1);
                    k += 1;
                    if level == 0 {
                        break;
                    }
                }
            }
        } else if at(k).1 == "local" {
            k += 1;
        } else {
            break;
        }
    }
    let name = |k: usize| (at(k).0 == Kind::Ident).then(|| vec![at(k).1.to_string()]);
    match at(k) {
        (Kind::Keyword | Kind::Ident, "struct" | "type" | "interface" | "law") => {
            name(k + 1).unwrap_or_default()
        }
        (_, "import") => {
            let mut last = None;
            let mut j = k + 1;
            while at(j).0 == Kind::Ident {
                last = Some(j);
                if at(j + 1).1 != "." {
                    break;
                }
                j += 2;
            }
            match (at(j + 1).1, at(j).1) {
                ("as", _) => name(j + 2).unwrap_or_default(),
                (_, "{") => {
                    let mut out = Vec::new();
                    let mut i = j + 1;
                    while at(i).0 == Kind::Ident {
                        out.push(at(i).1.to_string());
                        if at(i + 1).1 != "," {
                            break;
                        }
                        i += 2;
                    }
                    out
                }
                _ => last.and_then(name).unwrap_or_default(),
            }
        }
        (Kind::Ident, _) => match at(k + 1).1 {
            "(" | "[" => name(k).unwrap_or_default(),
            "," | "=" | ":" => {
                let mut out = Vec::new();
                let mut i = k;
                while matches!(at(i).0, Kind::Ident | Kind::Wild) {
                    if at(i).0 == Kind::Ident {
                        out.push(at(i).1.to_string());
                    }
                    if at(i + 1).1 != "," {
                        break;
                    }
                    i += 2;
                }
                if matches!(at(i + 1).1, "=" | ":") {
                    out
                } else {
                    Vec::new()
                }
            }
            _ => Vec::new(),
        },
        _ => Vec::new(),
    }
}
