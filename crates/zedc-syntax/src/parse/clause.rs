//! The messages for a parse that stops in a `with` clause that gives a sentinel value, and for
//! the reserved word `initial` written as a name (DESIGN.md sec:generations, sec:diagnostics).
//!
//! Since 2026-11-11 the sentinel value of a variable a loop updates is the statement `initial x
//! = e;`, and a `with` clause stands only on an indexed definition, each item with its key,
//! `with d[-1] = e`. So the parse stops at `with initial x = e` (row "A `with initial` item"),
//! at `with x = e` (row "Boundary item with neither `initial` nor an index"), and, on a
//! statement of a loop that is no indexed definition, at `with x[-2] = e` (row "A boundary
//! entry of a loop written without `initial`"). Each is found from the token the parse stopped
//! at, and the clause is rewritten as the rows say: in a loop, each item becomes an `initial`
//! statement written beside the statement; on an indexed definition, an item of its own
//! variable is given its key. Each repair is parsed once more, and offered only when that parse
//! gets past it.

use zedc_base::rejection::Row;

use super::engine::Parser;
use super::grammar::{Grammar, Kind};
use crate::lex::{Span, Tok, Token};

/// A parse error that a row of sec:diagnostics explains: the row, the message, the span the
/// error is reported at, and the notes, each a span with its text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Clause {
    /// The row, where one names the error.
    pub row: Option<Row>,
    /// What the error says.
    pub message: String,
    /// Where it is reported.
    pub span: Span,
    /// The sites the message names, and the repairs, each written `repair: …`.
    pub notes: Vec<(Span, String)>,
}

/// The tokens of a parse, each with its kind and text, ending in `(Kind::End, "")`; and the
/// tokens themselves, with their spans.
pub(super) struct Toks<'a, 't> {
    pub g: &'a Grammar,
    pub ring: u32,
    pub start: usize,
    pub text: &'t str,
    pub tokens: &'t [Token],
    pub toks: &'a [(Kind, &'t str)],
    pub end: Span,
}

/// One item of a `with` clause: its first token (`initial` where it has one), whether it has
/// `initial`, its name, whether it has a key, and the tokens of its value.
struct Item {
    first: usize,
    initial: bool,
    name: usize,
    keyed: bool,
    value: (usize, usize),
}

impl Toks<'_, '_> {
    pub(super) fn span(&self, i: usize) -> Span {
        self.tokens.get(i).map_or(self.end, |t| t.span)
    }

    pub(super) fn t(&self, i: usize) -> &str {
        self.toks.get(i).map_or("", |t| t.1)
    }

    /// The text of tokens `a` through `b`.
    pub(super) fn between(&self, a: usize, b: usize) -> &str {
        &self.text[self.span(a).start..self.span(b).end]
    }

    /// The index after the bracket group that opens at token `i`.
    fn after_group(&self, i: usize) -> usize {
        let mut d = 0;
        let mut j = i;
        while j < self.tokens.len() {
            d += depth(self.t(j));
            j += 1;
            if d == 0 {
                break;
            }
        }
        j
    }

    /// The first token of the statement around token `i`: after the `;` or the unmatched
    /// opening bracket before it.
    fn stmt_first(&self, i: usize) -> usize {
        let mut first = i;
        let mut d = 0;
        while first > 0 {
            let t = self.t(first - 1);
            if d == 0 && t == ";" || d - depth(t) < 0 {
                break;
            }
            d -= depth(t);
            first -= 1;
        }
        first
    }

    /// The token after the statement that starts at `i`: its `;`, the unmatched closing bracket,
    /// or the end.
    fn stmt_stop(&self, i: usize) -> usize {
        let mut stop = i;
        let mut d = 0;
        while stop < self.tokens.len()
            && !(d == 0 && self.t(stop) == ";")
            && d + depth(self.t(stop)) >= 0
        {
            d += depth(self.t(stop));
            stop += 1;
        }
        stop
    }

    /// The first token of the declaration of the statement at `first`, after its annotations
    /// and its `local`.
    fn decl_first(&self, mut k: usize) -> usize {
        while self.toks.get(k).is_some_and(|t| t.0 == Kind::Annot) {
            k += 1;
            if self.t(k) == "(" {
                k = self.after_group(k);
            }
        }
        k + usize::from(self.t(k) == "local")
    }

    /// The `loop` of the block whose statements include the one at `first`: the token after
    /// that block's opening brace, and the `loop` token, when the block is a loop's body.
    fn block_of(&self, first: usize) -> (usize, Option<usize>) {
        let mut o = first;
        let mut d = 0;
        while o > 0 {
            let t = self.t(o - 1);
            if d - depth(t) < 0 {
                break;
            }
            d -= depth(t);
            o -= 1;
        }
        let at_loop = if o >= 2 && self.t(o - 1) == "{" && self.t(o - 2) == "loop" {
            Some(o - 2)
        } else if o >= 3
            && self.t(o - 1) == "{"
            && self.toks[o - 2].0 == Kind::Ident
            && self.t(o - 3) == "loop"
        {
            Some(o - 3)
        } else {
            None
        };
        (o, at_loop)
    }

    /// The statement of the block that starts at token `open`, other than the one at `skip`,
    /// that gives `name` its sentinel value: `initial name = …;`, `initial a, name = …;`,
    /// `initial name: T = …;`, `initial name[-1] = …;` or `mutable name = …;`. One scan of the
    /// block.
    fn site(&self, open: usize, skip: usize, name: &str) -> Option<(usize, usize)> {
        let mut s = open;
        while s < self.tokens.len() && !matches!(self.t(s), "}" | ")" | "]") {
            let e = self.stmt_stop(s);
            let k = self.decl_first(s);
            let gives = match self.t(k) {
                "mutable" => self.t(k + 1) == name && self.t(k + 2) == "=",
                "initial" => {
                    let mut j = k + 1;
                    let mut found = false;
                    while j < e && !matches!(self.t(j), "=" | ":" | "[") {
                        found |= self.t(j) == name;
                        j += 1;
                    }
                    found
                        && match self.t(j) {
                            "[" => {
                                self.t(j + 1) == "-"
                                    && self.t(j + 2) == "1"
                                    && self.t(j + 3) == "]"
                                    && self.t(j + 4) == "="
                            }
                            _ => true,
                        }
                }
                _ => false,
            };
            if s != skip && gives {
                return Some((s, e));
            }
            if e >= self.tokens.len() || self.t(e) != ";" {
                return None;
            }
            s = e + 1;
        }
        None
    }

    /// The items of the `with` clause whose `with` is token `w`, and the token after the
    /// clause; `None` when the clause is not a list of items `[initial] x[k]… = e`.
    fn items(&self, w: usize) -> Option<(Vec<Item>, usize)> {
        let mut items = Vec::new();
        let mut i = w + 1;
        loop {
            let first = i;
            let initial = self.t(i) == "initial";
            i += usize::from(initial);
            if self.toks.get(i)?.0 != Kind::Ident {
                return None;
            }
            let name = i;
            i += 1;
            let keyed = self.t(i) == "[";
            while self.t(i) == "[" {
                i = self.after_group(i);
            }
            if self.t(i) != "=" {
                return None;
            }
            let v = i + 1;
            let mut d = 0;
            while i + 1 < self.tokens.len() {
                let t = self.t(i + 1);
                if d == 0 && matches!(t, "," | ";") || d + depth(t) < 0 {
                    break;
                }
                d += depth(t);
                i += 1;
            }
            if i < v {
                return None;
            }
            items.push(Item {
                first,
                initial,
                name,
                keyed,
                value: (v, i),
            });
            i += 1;
            if self.t(i) != "," {
                return Some((items, i));
            }
            i += 1;
        }
    }

    /// Whether `repair` parses in place of tokens `first` through `close`: the parse gets past
    /// the last of its tokens.
    fn parses(&self, first: usize, close: usize, repair: &str) -> bool {
        let Ok(tokens) = crate::lex::lex(repair) else {
            return false;
        };
        let new: Vec<(Kind, &str)> = tokens
            .iter()
            .map(|t| (kind(&t.tok), &repair[t.span.start..t.span.end]))
            .collect();
        let mut fixed = Vec::with_capacity(self.toks.len() + new.len());
        fixed.extend_from_slice(&self.toks[..first]);
        fixed.extend_from_slice(&new);
        let edit = fixed.len() - 1;
        fixed.extend_from_slice(&self.toks[close + 1..]);
        reaches(self.g, self.ring, self.start, &fixed, edit)
    }
}

/// The [`Clause`] for a parse that stopped at token `far` in a boundary clause written in a test
/// case ([`super::case::case_item`]), in a `with` clause that gives a sentinel value, or at the
/// word `initial` written as a name. The scans run over the statement and its block, and the
/// repair is parsed once: linear in the unit, on the error path only.
pub(super) fn clause(t: &Toks<'_, '_>, far: usize) -> Option<Clause> {
    super::case::case_item(t, far)
        .or_else(|| with_item(t, far))
        .or_else(|| reserved(t, far))
}

fn with_item(t: &Toks<'_, '_>, far: usize) -> Option<Clause> {
    // The first token of the item the parse stopped in.
    let at = match t.t(far) {
        "initial" => far,
        "=" => {
            let mut i = far;
            while i > 0 && t.t(i - 1) == "]" {
                let mut d = 0;
                let mut j = i - 1;
                loop {
                    d += depth(t.t(j));
                    if d == 0 {
                        break;
                    }
                    j = j.checked_sub(1)?;
                }
                i = j;
            }
            let n = i.checked_sub(1)?;
            (t.toks[n].0 == Kind::Ident).then_some(n)?
        }
        // `with x[-2] = 0` on a statement that is no indexed definition: the value before
        // `with` reads `with x` as a facet, which takes `(`.
        "[" if far > 0 && t.toks[far - 1].0 == Kind::Ident => far - 1,
        _ => return None,
    };
    if at == 0 || !matches!(t.t(at - 1), "with" | ",") {
        return None;
    }
    let first = t.stmt_first(at);
    // The clause's `with`: the last at the item's own depth before it.
    let mut w = None;
    let mut d = 0;
    let mut at_depth = 0;
    for i in first..at {
        if t.t(i) == "with" {
            w = Some((i, d));
        }
        d += depth(t.t(i));
        at_depth = d;
    }
    let w = w.filter(|&(_, dw)| dw == at_depth)?.0;
    let (items, cut) = t.items(w)?;
    let bad = items.iter().find(|i| i.first == at)?;
    let close = if t.t(cut) == ";" { cut } else { cut - 1 };
    let semi = t.t(cut) == ";";
    let (open, looped) = t.block_of(first);
    let k = t.decl_first(first);
    let indexed = {
        let mut j = k + 1;
        let keyed = t.toks.get(k).is_some_and(|x| x.0 == Kind::Ident) && t.t(j) == "[";
        while t.t(j) == "[" {
            j = t.after_group(j);
        }
        (keyed && t.t(j) == "=").then(|| t.t(k).to_string())
    };
    let head = t.between(first, w - 1);
    let stmt_text = t.between(first, close);
    let stmt = Span {
        start: t.span(first).start,
        end: t.span(close).end,
    };
    let item_span = |i: &Item| Span {
        start: t.span(i.first).start,
        end: t.span(i.value.1).end,
    };
    // The item without `initial`, `x = 0` or `x[-2] = 0`.
    let plain = |i: &Item| t.between(i.name, i.value.1).to_string();
    let value = |i: &Item| t.between(i.value.0, i.value.1).to_string();

    // The clause rewritten: the items kept in it, the `initial` statements written beside it,
    // and the items dropped since another statement gives their value.
    let mut kept: Vec<String> = Vec::new();
    let mut beside: Vec<String> = Vec::new();
    let mut given: Vec<(String, (usize, usize))> = Vec::new();
    let mut deleted: Vec<String> = Vec::new();
    let mut keyless = false;
    for (n, i) in items.iter().enumerate() {
        let name = t.t(i.name);
        let own = indexed.as_deref() == Some(name);
        if own && !i.keyed {
            match below(&t.toks[k..w], name) {
                Some(key) => kept.push(format!("{name}[{key}] = {}", value(i))),
                None => {
                    keyless = true;
                    kept.push(format!("{name}[…] = {}", value(i)));
                }
            }
        } else if indexed.is_some() && i.keyed || own {
            kept.push(plain(i));
        } else if looped.is_some() {
            let earlier = items[..n]
                .iter()
                .any(|j| t.t(j.name) == name && !j.keyed && !i.keyed);
            match (i.keyed, t.site(open, first, name)) {
                (false, Some(s)) => given.push((name.to_string(), s)),
                _ if earlier => {}
                _ => beside.push(format!("initial {};", plain(i))),
            }
        } else {
            deleted.push(t.between(i.first, i.value.1).to_string());
        }
    }
    let tail = if semi { ";" } else { "" };
    let mut repair = String::new();
    for s in &beside {
        repair.push_str(s);
        repair.push(' ');
    }
    repair.push_str(head);
    if !kept.is_empty() {
        repair.push_str(" with ");
        repair.push_str(&kept.join(", "));
    }
    repair.push_str(tail);

    let name = t.t(bad.name);
    let bad_text = t.between(bad.first, bad.value.1);
    let bad_plain = plain(bad);
    let bad_value = value(bad);
    let own = indexed.as_deref() == Some(name);
    let row = match (bad.initial, bad.keyed) {
        (true, _) => Some(Row::WithInitialItem),
        (false, false) => Some(Row::BareBoundary),
        (false, true) => looped.is_some().then_some(Row::BareLoopEntry),
    };
    let what = if bad.initial {
        "`with initial` is no longer how a sentinel value is given".to_string()
    } else if bad.keyed {
        "a `with` clause stands only on an indexed definition".to_string()
    } else if own {
        format!(
            "it gives no key: it reads as though `{name}` took the value `{bad_value}` at every \
             key"
        )
    } else {
        format!(
            "it gives `{name}` no sentinel value: without `initial` or a key, it reads as though \
             `{name}` took the value `{bad_value}` anew on every step"
        )
    };
    let message = if own {
        let key = below(&t.toks[k..w], name).unwrap_or_else(|| "…".into());
        format!(
            "`with {bad_text}` stands on the definition of `{name}`, whose entries have keys, \
             and {what}. An entry of an indexed definition below its domain is given in the \
             definition's `with` clause with its key, as `with {name}[{key}] = {bad_value}`, the \
             entry one below the low edge of the domain of `{name}`."
        )
    } else if looped.is_some() && bad.keyed {
        format!(
            "`with {bad_text}` stands on `{stmt_text}` in the body of a `loop`, and {what}. An \
             entry of `{name}` below generation 0 is a sentinel value, given once, before the \
             first step, by an `initial` statement among the statements of the loop's body, \
             `initial {bad_plain};`; a `with` item in a loop has no statement it belongs to \
             more than any other."
        )
    } else if looped.is_some() {
        format!(
            "`with {bad_text}` stands on `{stmt_text}` in the body of a `loop`, and {what}. The \
             sentinel value of `{name}`, its value before step 0, is given once, by a statement \
             of its own, `initial {bad_plain};`, which may stand anywhere among the statements \
             of the loop's body."
        )
    } else {
        format!(
            "`with {bad_text}` stands on `{stmt_text}`, which is neither an indexed definition \
             nor a statement of the body of a `loop`, and {what}. A `with` clause stands only on \
             an indexed definition, as `{name}[i in 0..<n] = … with {name}[-1] = 0;`, and a \
             variable a loop updates takes its sentinel value from a statement of the loop's \
             body, `initial {name} = 0;`."
        )
    };
    let mut notes = vec![(
        stmt,
        "the statement the `with` clause stands on".to_string(),
    )];
    if let Some(l) = looped {
        notes.push((t.span(l), "the loop whose body holds the statement".into()));
    }
    for (n, (a, b)) in &given {
        let c = if t.t(*b) == ";" { *b } else { b - 1 };
        notes.push((
            Span {
                start: t.span(*a).start,
                end: t.span(c).end,
            },
            format!(
                "`{}` already gives `{n}` its sentinel value, so the item is deleted, not \
                 written as a statement",
                t.between(*a, c)
            ),
        ));
    }
    if !keyless && t.parses(first, close, &repair) {
        let mut why = Vec::new();
        if !beside.is_empty() {
            why.push(format!(
                "{} written beside the statement, the sentinel value given once, before step 0",
                beside
                    .iter()
                    .map(|s| format!("`{s}`"))
                    .collect::<Vec<_>>()
                    .join(" and ")
            ));
        }
        if own {
            why.push(format!("the entry of `{name}` given with its key"));
        }
        if kept.is_empty() {
            why.push("the `with` clause deleted".to_string());
        } else if !given.is_empty() || !deleted.is_empty() || !beside.is_empty() {
            why.push("the other items deleted from the `with` clause".to_string());
        }
        notes.push((
            item_span(bad),
            format!("repair: `{repair}`, {}", why.join(", and ")),
        ));
    }
    Some(Clause {
        row,
        message,
        span: item_span(bad),
        notes,
    })
}

/// The [`Clause`] for the reserved word `initial` written where a name stands: `initial = 0;`,
/// `initial[0] = 1;`, `initial _ = 0;` or `x = initial;`.
fn reserved(t: &Toks<'_, '_>, far: usize) -> Option<Clause> {
    let at = if t.t(far) == "initial" {
        far
    } else if far > 0 && t.t(far - 1) == "initial" && t.toks[far].0 != Kind::Ident {
        far - 1
    } else {
        return None;
    };
    let span = t.span(at);
    Some(Clause {
        row: None,
        message: "`initial` is a reserved word, so it names no variable: it begins the statement \
                  `initial x = e;`, which gives `x` its value before step 0 of a loop that \
                  updates `x`. Write another name in its place."
            .into(),
        span,
        notes: vec![(
            span,
            "repair: another name in place of `initial`, as `start`".into(),
        )],
    })
}

/// The kind of token the grammar names `tok` by.
pub(super) fn kind(tok: &Tok) -> Kind {
    match tok {
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

/// Whether a parse of `toks` as rule `start` gets past token `edit`: succeeds, or fails only
/// after it.
pub(super) fn reaches(
    g: &Grammar,
    ring: u32,
    start: usize,
    toks: &[(Kind, &str)],
    edit: usize,
) -> bool {
    let mut p = Parser::new(g, ring, toks);
    let reached = match p.rule_node(start, 0, false) {
        Some((e, _)) if e + 1 >= toks.len() => return true,
        Some((e, _)) => e.max(p.far),
        None => p.far,
    };
    reached > edit
}

/// How the bracket depth changes at a token: up at an opening bracket, down at a closing one.
pub(super) fn depth(t: &str) -> i32 {
    match t {
        "(" | "[" | "{" => 1,
        ")" | "]" | "}" => -1,
        _ => 0,
    }
}

/// The key of the entry below the domain of the indexed definition `stmt` of `name`, the
/// tokens before its boundary item, when it has one key `i in lo..<hi`, `lo..=hi` or `lo..`:
/// `lo - 1`, worked out when `lo` is an integer literal, possibly negated.
fn below(stmt: &[(Kind, &str)], name: &str) -> Option<String> {
    let [(_, f), (_, "["), (Kind::Ident, _), (_, "in"), rest @ ..] = stmt else {
        return None;
    };
    if *f != name {
        return None;
    }
    let mut d = 0;
    let mut range = None;
    let mut close = None;
    for (i, &(_, t)) in rest.iter().enumerate() {
        if d == 0 && range.is_none() && matches!(t, ".." | "..<" | "..=") {
            range = Some(i);
        }
        if d + depth(t) < 0 {
            close = Some(i);
            break;
        }
        d += depth(t);
    }
    let (range, close) = (range?, close?);
    if range == 0 || rest.get(close + 1).map(|t| t.1) != Some("=") {
        return None;
    }
    let lo = &rest[..range];
    let int = |t: &str| t.replace('_', "").parse::<i128>().ok();
    let folded = match lo {
        [(Kind::Int, t)] => int(t).and_then(|v| v.checked_sub(1)),
        [(_, "-"), (Kind::Int, t)] => int(t).and_then(|v| (-v).checked_sub(1)),
        _ => None,
    };
    let words: Vec<&str> = lo.iter().map(|t| t.1).collect();
    Some(match (folded, lo.len()) {
        (Some(v), _) => v.to_string(),
        (None, 1) => format!("{} - 1", words[0]),
        (None, _) => format!("({}) - 1", words.join(" ")),
    })
}
