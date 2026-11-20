//! The messages for a parse that stops in a `with` clause that gives a sentinel value, and for
//! a reserved word written where a name stands, for the removed declaration `mutable x = e;`,
//! for a word other than `carryForward` after `with` at the end of an `initial` statement, and for
//! a union, intersection or difference written bare as a key, guarantee or permission, and for
//! `<-` or `=` written in a condition (DESIGN.md sec:generations, sec:lexical, sec:grammar,
//! sec:diagnostics).
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
//!
//! A reserved word written where a name stands, as `without = 3;` or `f(law) = law + 1;`, is
//! found by the parser itself: the parse is run once more with a name in the word's place, and
//! the word is the cause when that parse gets past the token the first one stopped at and past
//! the token after the word (row "Reserved word written where a name stands").
//!
//! In a condition, `if x<-1 {` (an R habit: `<-` is one token, a push) and `if x = 3 {` (a
//! C habit: `=` binds) stop the parse at the `<-` or the `=`, or just after the `<-`. Each is
//! found the same way: the parse is run once more with `< -` or `==` in its place, and the row
//! applies when it gets past where the first stopped (rows "`<-` written where a comparison
//! with a negative operand was meant" and "`=` written in a condition where `==` was
//! meant"). Outside a condition, a statement that stops at its `<-` after a name with fields,
//! views and keys is a push to a target that cannot be pushed to, as `m.stdout::bytes::len <-
//! "a";` (row "Push to a target that cannot be pushed to").

use std::collections::HashSet;

use zedc_base::rejection::Row;

use super::engine::Parser;
use super::grammar::{Grammar, Kind};
use crate::lex::{Span, Tok, Token, ident};
use zed_kernel::text::prose::and_list;

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
    /// `initial name: T = …;` or `initial name[-1] = …;`. One scan of the
    /// block.
    fn site(&self, open: usize, skip: usize, name: &str) -> Option<(usize, usize)> {
        let mut s = open;
        while s < self.tokens.len() && !matches!(self.t(s), "}" | ")" | "]") {
            let e = self.stmt_stop(s);
            let k = self.decl_first(s);
            let gives = match self.t(k) {
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
        self.parses_past(first, close, repair, 0)
    }

    /// Whether `repair` parses in place of tokens `first` through `close` and the parse gets
    /// `more` tokens past the last of its tokens.
    fn parses_past(&self, first: usize, close: usize, repair: &str, more: usize) -> bool {
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
        reaches(self.g, self.ring, self.start, &fixed, edit + more)
    }

    /// Whether the parse, with the name `name` in place of each token of `at`, gets past token
    /// `past`.
    fn renamed(&self, at: &[usize], name: &str, past: usize) -> bool {
        let mut fixed = self.toks.to_vec();
        for &i in at {
            fixed[i] = (Kind::Ident, name);
        }
        reaches(self.g, self.ring, self.start, &fixed, past)
    }

    /// `like`, or `like2`, `like3` and so on, the first that is no name of the text
    /// ([`ident::fresh`]).
    fn unused(&self, like: &str) -> String {
        let words: HashSet<&str> = ident::names(self.text).map(|(_, w)| w).collect();
        ident::fresh(like, |n| !words.contains(n))
    }

    /// The first and last tokens on the source line of token `i`.
    pub(super) fn line(&self, i: usize) -> (usize, usize) {
        let span = self.span(i);
        let (lo, hi) = zedc_base::source::line_bounds(self.text, span.start, span.end);
        let (mut a, mut b) = (i, i);
        while a > 0 && self.span(a - 1).start >= lo {
            a -= 1;
        }
        while b + 1 < self.tokens.len() && self.span(b + 1).end <= hi {
            b += 1;
        }
        (a, b)
    }
}

/// The [`Clause`] for a parse that stopped at token `far` in a `with` clause that gives a
/// sentinel value, at or after a reserved word written where a name stands, at the removed
/// declaration `mutable x = e;`, at a word other than `carryForward` after `with` at the end
/// of an `initial` statement, at a pattern built with an operator written bare, at an or-pattern
/// as an `else` tail's pattern, or at a union, intersection or difference written bare as a key,
/// or at `<-` or `=` in a condition, or after the block of an `if` that gives a value and has
/// no `else`.
/// The scans run over the statement, its block, its line or the type, and each check of a word
/// or a repair is one more parse: linear in the unit, on the error path only.
pub(super) fn clause(t: &Toks<'_, '_>, far: usize) -> Option<Clause> {
    with_item(t, far)
        .or_else(|| direction_word(t, far))
        .or_else(|| reserved(t, far))
        .or_else(|| mutable_decl(t, far))
        .or_else(|| carry_word(t, far))
        // Before `bare_key`, which would read `#a | #b -> 1` in an arm as a bare key.
        .or_else(|| bare_pattern(t, far))
        // Also before `bare_key`, which would read `r else #a | #b -> 0` as a bare key.
        .or_else(|| else_or_pattern(t, far))
        .or_else(|| bare_key(t, far))
        .or_else(|| push_or_less(t, far))
        .or_else(|| push_target(t, far))
        .or_else(|| binding_in_condition(t, far))
        .or_else(|| value_if_without_else(t, far))
}

/// The [`Clause`] for an `if` that gives a value and has no `else` (author, P348): `x = if c {
/// 1 };`. The parse stops just after the `}` of the `if`'s block, since only an `if` statement,
/// the first word of its statement, may leave out its `else`. The `if` is found by matching the
/// brace back and scanning back over its condition to an `if` at the brace's depth; the clause
/// applies when that `if` is not the first word of its statement, and the text with `else { }`
/// written after the brace parses past it. One scan back over the statement and one parse, on
/// the error path only: linear in the unit.
fn value_if_without_else(t: &Toks<'_, '_>, far: usize) -> Option<Clause> {
    let close = far.checked_sub(1)?;
    if t.t(close) != "}" || t.t(far) == "else" {
        return None;
    }
    let mut open = close;
    let mut d = depth(t.t(open));
    while d != 0 {
        open = open.checked_sub(1)?;
        d += depth(t.t(open));
    }
    // Back over the condition, to the `if` at the brace's depth.
    let mut k = open.checked_sub(1)?;
    let mut d = 0;
    loop {
        d += depth(t.t(k));
        if d > 0 || d == 0 && t.t(k) == ";" {
            return None;
        }
        if d == 0 && t.t(k) == "if" {
            break;
        }
        k = k.checked_sub(1)?;
    }
    if t.decl_first(t.stmt_first(k)) == k || !t.parses(close, close, "} else { 0 }") {
        return None;
    }
    let written = t.between(k, close);
    let shown = if quotable(written) {
        written
    } else {
        "if c { … }"
    };
    let span = t.span(far);
    Some(Clause {
        row: None,
        message: format!(
            "Missing `else` in an `if` that gives a value: `{shown}`. An `if` that gives a value \
             has both arms."
        ),
        span,
        notes: vec![(
            t.span(k),
            "an `if` that gives a value has an `else`, as `x = if c { 1 } else { 2 };`; only an \
             `if` statement, which stands alone and ends with `;`, may leave it out, as `if c { \
             break; };`"
                .to_string(),
        )],
    })
}

/// The [`Clause`] for a push statement whose target cannot be pushed to (row "Push to a target
/// that cannot be pushed to", author P302): `m.stdout::bytes::len <- "a";`, where a push target
/// is a name and its fields, then at most one view (`PushTarget` in sec:grammar), then any
/// keys. The parse stops at the `<-`, outside a condition; the
/// row applies when the text before it, from the start of the statement, is a name followed by
/// fields `.f`, views `::v` and keys `[k]`, and the statement parses with one name in its
/// place. No repair: which target was meant is not known. One scan of the statement and one
/// parse more, on the error path only: linear in the unit.
fn push_target(t: &Toks<'_, '_>, far: usize) -> Option<Clause> {
    if t.toks.get(far) != Some(&(Kind::Op, "<-")) || condition(t, far).is_some() {
        return None;
    }
    let first = t.stmt_first(far);
    if first >= far || first > 0 && !matches!(t.t(first - 1), ";" | "{") {
        return None;
    }
    let mut i = first;
    let ident = |i: usize| t.toks.get(i).is_some_and(|x| x.0 == Kind::Ident);
    if !ident(i) {
        return None;
    }
    i += 1;
    while i < far {
        match t.t(i) {
            "." | "::" if ident(i + 1) => i += 2,
            "[" => i = t.after_group(i),
            _ => return None,
        }
    }
    let target = t.between(first, far - 1);
    if i != far || !quotable(target) || !t.parses_past(first, far - 1, &t.unused("p"), 1) {
        return None;
    }
    Some(Clause {
        row: Some(Row::PushTargetNotPushable),
        // The shape only: whether a target of the right shape takes a push is decided when
        // the push is compiled (DESIGN.md sec:ports, "What a push may name").
        message: format!(
            "Invalid push target `{target}`: a target is a name and its fields, then at most one \
             view, then its keys, as `m.stdout::bytes <- b;` or `hist[k] <- 1;`."
        ),
        span: t.span(far),
        notes: Vec::new(),
    })
}

/// The condition around token `at`: its keyword, `if`, `while`, `until` or the word `where`, and the
/// token that ends it, `{`, `;` or `->`, both outside brackets. The keyword is found by going
/// back from `at`, out of any `(` or `[` but never past a `{` or `}`, a `;`, a `,`, an `=` or a
/// `->` outside brackets, which a condition does not hold; None when no keyword comes first.
/// O(c) for a condition of c tokens, and O(s) in the statement around it.
fn condition(t: &Toks<'_, '_>, at: usize) -> Option<(usize, usize)> {
    let mut k = at;
    let mut n = 0;
    loop {
        k = k.checked_sub(1)?;
        let tok = t.t(k);
        if n == 0 {
            if matches!(tok, ";" | "," | "=" | "->" | "{" | "}") {
                return None;
            }
            let kind = t.toks.get(k).map(|x| x.0);
            if matches!(tok, "if" | "while" | "until") && kind == Some(Kind::Keyword) {
                break;
            }
            // `where` is no keyword: the lexer reads it as a name, and the grammar takes it
            // after a pattern or a generator. At the start of a statement it is a name.
            if tok == "where"
                && kind == Some(Kind::Ident)
                && k > 0
                && !matches!(t.t(k - 1), ";" | "{" | "}")
            {
                break;
            }
        }
        // Going back, a closing bracket opens a group, and an opening one closes it, or, at
        // `n == 0`, leads out of the bracket `at` stands in.
        n = (n - depth(tok)).max(0);
    }
    let mut n = 0;
    let end = (k + 1..t.tokens.len()).find(|&i| {
        let tok = t.t(i);
        let ends = n == 0 && matches!(tok, "{" | ";" | "->");
        n += depth(tok);
        ends
    })?;
    (end > at).then_some((k, end))
}

/// The text of tokens `a` through `b` with `with` in place of token `at`.
fn swapped(t: &Toks<'_, '_>, (a, b): (usize, usize), at: usize, with: &str) -> String {
    let (lo, hi) = (t.span(a).start, t.span(b).end);
    let (s, e) = (t.span(at).start, t.span(at).end);
    format!("{}{with}{}", &t.text[lo..s], &t.text[e..hi])
}

/// The token that ends the top-level declaration around token `at`: the first `;` or `}` at
/// or after `at` where every bracket opened since the start of the unit is closed; when there
/// is none, as when a bracket is left open, the end of the unit, so that only a parse of the
/// whole unit gets past it. One scan of the unit, O(n).
///
/// Complexity tradeoff (COMPLEXITY.md, PITFALL-push-vs-less): the naive check that a repair
/// makes the declaration parse would parse the whole unit with it, O(n), and would withhold the
/// repair for an error in a later declaration. Used: the parse need only get past this token,
/// which is also O(n) but stops at the declaration, and judges the repair by its own
/// declaration alone.
fn decl_end(t: &Toks<'_, '_>, at: usize) -> usize {
    let mut d = 0;
    for i in 0..t.tokens.len() {
        d += depth(t.t(i));
        if i >= at && d <= 0 && matches!(t.t(i), ";" | "}") {
            return i;
        }
    }
    t.tokens.len().max(at)
}

/// Whether `s` can be quoted in a headline: one line, and no backtick, which would end the
/// quotation.
fn quotable(s: &str) -> bool {
    !s.contains(['\n', '`'])
}

/// The [`Clause`] for `<-` written where a comparison with a negative operand was meant (row
/// "`<-` written where a comparison with a negative operand was meant"): `if x<-1 { … }`,
/// where `<-` is one token, a push, which only a statement makes. The parse stops at the `<-`
/// or at the token after it; the row applies when that `<-` stands in a condition ([`condition`])
/// and the text with `< -` in its place gets past the token where the parse stopped. Outside a
/// condition, as in a push statement with a malformed target (`m.stdout::bytes::len <- "a";`), a
/// push is allowed and no comparison was meant, so the error stays a syntax error. The repair is
/// the condition with `< -` in place of `<-`, offered when the token after `<-` is not a string
/// or atom literal, which `-` cannot negate, and the declaration then parses: the parse with it
/// gets past the token that ends the declaration ([`decl_end`]). Two parses more and one scan of
/// the unit, on the error path only: linear in the unit.
fn push_or_less(t: &Toks<'_, '_>, far: usize) -> Option<Clause> {
    let push = |i: usize| t.toks.get(i).is_some_and(|x| *x == (Kind::Op, "<-"));
    let at = [Some(far), far.checked_sub(1)]
        .into_iter()
        .flatten()
        .find(|&i| push(i))?;
    if !t.parses_past(at, at, "< -", far - at) {
        return None;
    }
    let (first, end) = condition(t, at)?;
    if end < at {
        return None;
    }
    let written = t.between(first, end);
    let (lo, s, e, hi) = (
        t.span(first).start,
        t.span(at).start,
        t.span(at).end,
        t.span(end).end,
    );
    let repaired = format!(
        "{} < -{}",
        t.text[lo..s].trim_end(),
        t.text[e..hi].trim_start()
    );
    if !quotable(written) {
        return None;
    }
    let span = t.span(at);
    let mut message = format!("Invalid use of the push operator `<-` in a condition: `{written}`.");
    let mut notes = vec![(
        span,
        "`<-` pushes a value into a port, an accumulator or the next generation, and can only be \
         used as a statement; `x < -1`, with a space, compares `x` with a negative number"
            .to_string(),
    )];
    // `-` negates a number, never a string or an atom, so `x < -"a"` is no comparison to offer.
    let negatable = !matches!(t.toks.get(at + 1), Some((Kind::Str | Kind::Atom, _)));
    if negatable && t.parses_past(at, at, "< -", decl_end(t, at) - at) {
        message.push_str(&format!(" Try `{repaired}` instead."));
        notes.push((span, format!("repair: `{repaired}`")));
    }
    Some(Clause {
        row: Some(Row::PushWhereLessMeant),
        message,
        span,
        notes,
    })
}

/// The [`Clause`] for `=` written in a condition where `==` was meant (row "`=` written in a
/// condition where `==` was meant"): `if x = 3 { … }`, where `=` binds a name, which only a
/// statement does. The parse stops at the `=`, in the head of an `if`, the expression of a
/// `while` or an `until`, or a guard after `where` ([`condition`]); the row applies when the
/// text with `==` in its place gets past it. The repair is the condition with `==` in place of
/// `=`, its parentheses kept as written, offered when the declaration then parses, as in
/// [`push_or_less`]. Two parses more and one scan of the unit, on the error path only: linear
/// in the unit.
fn binding_in_condition(t: &Toks<'_, '_>, far: usize) -> Option<Clause> {
    if t.toks.get(far) != Some(&(Kind::Op, "=")) {
        return None;
    }
    let (first, end) = condition(t, far)?;
    let written = t.between(first, end);
    if !quotable(written) || !t.parses(far, far, "==") {
        return None;
    }
    let repaired = swapped(t, (first, end), far, "==");
    let span = t.span(far);
    let mut message = format!("Invalid use of `=` in a condition: `{written}`.");
    let mut notes = vec![(
        span,
        "`=` binds a name and can only be used as a statement; `==` compares two values"
            .to_string(),
    )];
    if t.parses_past(far, far, "==", decl_end(t, far) - far) {
        message.push_str(&format!(" Try `{repaired}` instead."));
        notes.push((span, format!("repair: `{repaired}`")));
    }
    Some(Clause {
        row: Some(Row::BindingInCondition),
        message,
        span,
        notes,
    })
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
                and_list(&beside.iter().map(|s| format!("`{s}`")).collect::<Vec<_>>())
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

/// Each reserved word, in the order of [`crate::lex::KEYWORDS`], with what it begins (the
/// note "`word` is reserved: ...") and a name of like meaning that the repair offers in its
/// place.
pub const RESERVED: [(&str, &str, &str); 37] = [
    (
        "struct",
        "it begins a struct declaration, as `struct Point { x: f64, y: f64 }`",
        "record",
    ),
    (
        "type",
        "it begins a type declaration, as `type Meters = f64;`",
        "kind",
    ),
    (
        "interface",
        "it begins an interface declaration, as `interface Named { name: Utf8String }`",
        "contract",
    ),
    (
        "grammar",
        "it begins the grammar of a string type, as `Utf8String matching grammar { digit digit* }`",
        "syntax",
    ),
    (
        "matching",
        "it gives a string type its grammar, as `Utf8String matching grammar { digit digit* }`",
        "matched",
    ),
    (
        "import",
        "it begins an import, as `import geometry;` or `import geometry as geo;`",
        "imported",
    ),
    (
        "asc",
        "it marks an ascending sort key, as `xs.sort(asc x -> x.name)`",
        "ascending",
    ),
    (
        "as",
        "it renames an import or reshapes a value, as `import geometry as geo;` or \
         `src as (i -> w)`",
        "alias",
    ),
    (
        "into",
        "it regroups a value by its keys, as `sales into (sku -> region -> quantity)`",
        "target",
    ),
    (
        "local",
        "it marks a definition its unit does not export, as `local helper(x) = x + 1;`",
        "inner",
    ),
    (
        "for",
        "it begins a comprehension, as `for x in xs { x * 2 }`",
        "each",
    ),
    (
        "initial",
        "it begins the statement `initial x = e;`, which gives `x` its value before step 0 of a \
         loop that updates `x`",
        "start",
    ),
    (
        "in",
        "it tests membership or names a range, as `k in m::domain`",
        "input",
    ),
    (
        "not",
        "it negates a test, as `x is not int` or `k not in s`",
        "negated",
    ),
    (
        "loop",
        "it begins a loop, as `loop t { while t < n; x' = x + 1; }`",
        "cycle",
    ),
    (
        "until",
        "it begins the statement `until c;`, which ends a loop once `c` holds",
        "limit",
    ),
    (
        "while",
        "it begins the statement `while c;`, which runs a loop as long as `c` holds",
        "during",
    ),
    (
        "break",
        "it begins the statement `break;`, which ends a loop early, as `if c { break; };`",
        "stop",
    ),
    (
        "match",
        "it begins a match, as `match x { 0 -> \"zero\", _ -> \"other\" }`",
        "found",
    ),
    (
        "if",
        "it begins a conditional, as `if x < 0 { -x } else { x }`",
        "cond",
    ),
    (
        "else",
        "it gives the other branch or a fallback value, as `if x < 0 { -x } else { x }` or \
         `xs[0] else 0`",
        "other",
    ),
    (
        "is",
        "it tests a value against a type, as `x is int`",
        "matches",
    ),
    (
        "positional",
        "it marks a parameter given only by position, as `half(positional x: f64) = x / 2;`",
        "ordinal",
    ),
    (
        "without",
        "it removes a facet from a value, as `n without units(\"km\")`",
        "rest",
    ),
    (
        "with",
        "it adds a facet or changes fields of a value, as `5 with units(\"degC\")` or \
         `p with { x = 0.0 }`",
        "extra",
    ),
    (
        "return",
        "it begins the statement `return e;`, which gives a block its value",
        "result",
    ),
    (
        "test",
        "it begins the test table of a definition, as `f(x) = x + 1 test { 1 -> 2 }`",
        "check",
    ),
    (
        "law",
        "it begins a law, as in `struct Span { lo: int, hi: int, law ordered() = lo <= hi }`",
        "rule",
    ),
    (
        "proof",
        "it begins the proof of a law, as `law nonneg(x: int) = x * x >= 0 proof { }`",
        "evidence",
    ),
    (
        "emit",
        "it begins the statement `emit e;`, which gives one more entry of a body",
        "output",
    ),
    (
        "this",
        "it names the value a method is called on, as `int(this)`",
        "current",
    ),
    (
        "desc",
        "it marks a descending sort key, as `xs.sort(desc x -> x.score)`",
        "descending",
    ),
    ("div", "it divides integers, as `a div b`", "quotient"),
    (
        "mod",
        "it gives the remainder of integer division, as `a mod b`",
        "remainder",
    ),
    ("true", "it is a boolean value", "yes"),
    ("false", "it is a boolean value", "no"),
    (
        "unordered",
        "it marks a fold whose order does not matter, as `xs >< (+) unordered`",
        "anyOrder",
    ),
];

/// The [`Clause`] for a direction word, `asc` or `desc`, written where it is no whole sort key,
/// with the headlines of DESIGN.md step L5.1 (sec:order: the word alone stands only as a whole
/// argument, followed by `,` or `)`). The word is the token the parse stopped at or the one
/// before it. In parentheses, `xs.sort((desc))`, the repair drops them; directly in an argument
/// list and followed by more, `xs.sort(desc + 1)`, the repair makes the argument the key
/// `desc x -> x + 1`; each repair is offered when the statement then parses to its end.
/// Elsewhere, `x = desc;`, the word is no value, when a name in its place lets the statement
/// parse to its end and the word is not being defined (the statement's first token, or before
/// its `=` or a `:`), which [`reserved`] explains. One scan of the statement and at most two
/// parses more, on the error path only: linear in the unit.
fn direction_word(t: &Toks<'_, '_>, far: usize) -> Option<Clause> {
    let is_word = |i: usize| {
        t.toks
            .get(i)
            .is_some_and(|k| k.0 == Kind::Keyword && matches!(k.1, "asc" | "desc"))
    };
    let k = [Some(far), far.checked_sub(1)]
        .into_iter()
        .flatten()
        .find(|&i| is_word(i))?;
    let word = t.t(k);
    // The whole statement, out of the parentheses and brackets around the word, as the
    // headline shows it; not out of a block.
    let mut first = t.stmt_first(k);
    while first > 0 && matches!(t.t(first - 1), "(" | "[") {
        first = t.stmt_first(first - 1);
    }
    let mut stop = t.stmt_stop(k);
    while matches!(t.t(stop), ")" | "]") {
        stop = t.stmt_stop(stop + 1);
    }
    let last = stop.checked_sub(1).filter(|&l| l >= first)?;
    let stmt = t.between(first, last);
    // The statement with tokens `a` through `b` replaced by `with`.
    let fixed = |a: usize, b: usize, with: &str| {
        let s = t.span(first).start;
        format!(
            "{}{with}{}",
            &t.text[s..t.span(a).start],
            &t.text[t.span(b).end..t.span(last).end]
        )
    };
    // Whether `with` in place of tokens `a` through `b` lets the statement parse to its end.
    let parses = |a: usize, b: usize, with: &str| t.parses_past(a, b, with, stop - b);
    let note = |r: &str| (t.span(k), format!("repair: `{r}`"));
    // In parentheses: `xs.sort((desc))`.
    if k > 0 && t.t(k - 1) == "(" && t.t(k + 1) == ")" && parses(k - 1, k + 1, word) {
        let r = fixed(k - 1, k + 1, word);
        return Some(Clause {
            row: None,
            message: format!(
                "`{word}` in parentheses is not a sort key: `{stmt}`. Try `{r}` instead."
            ),
            span: t.span(k),
            notes: vec![note(&r)],
        });
    }
    // Directly in an argument list, followed by more of the argument: `xs.sort(desc + 1)`.
    if k > 0 && matches!(t.t(k - 1), "(" | ",") && !matches!(t.t(k + 1), "," | ")") {
        let mut e = k + 1;
        let mut d = 0;
        while e < stop && !(d == 0 && matches!(t.t(e), "," | ")")) && d + depth(t.t(e)) >= 0 {
            d += depth(t.t(e));
            e += 1;
        }
        // At the end of the text or of the statement there is no more of the argument.
        if e <= k + 1 || e > t.tokens.len() {
            return None;
        }
        let x = t.unused("x");
        let key = format!("{word} {x} -> {x} {}", t.between(k + 1, e - 1));
        if parses(k, e - 1, &key) {
            let r = fixed(k, e - 1, &key);
            return Some(Clause {
                row: None,
                message: format!(
                    "`{word}` alone is a whole sort key: `{stmt}`. Try `{r}` instead."
                ),
                span: t.span(k),
                notes: vec![note(&r)],
            });
        }
        return None;
    }
    // Elsewhere: `x = desc;`. A word being defined is left to [`reserved`].
    let mut d = 0;
    let mut eq_after = false;
    for i in first..stop {
        eq_after |= d == 0 && i > k && t.t(i) == "=";
        d += depth(t.t(i));
    }
    let defined = k == first || t.t(k + 1) == ":" || eq_after;
    if defined || !t.renamed(&[k], "x", stop) {
        return None;
    }
    Some(Clause {
        row: None,
        message: format!("`{word}` is not a value: `{stmt}`."),
        span: t.span(k),
        notes: vec![(
            t.span(k),
            format!(
                "`{word}` stands before a sort key, as in `xs.sort({word} x -> x)`, in \
                 `.sort(…)`, `.orderedValues(…)` or an `into` pattern"
            ),
        )],
    })
}

/// The [`Clause`] for a reserved word written where a name stands: `without = 3;`,
/// `f(law) = law + 1;`, `x = s.if;`, `struct S { for: int }`. The word is the token the parse
/// stopped at, or the last or the first reserved word before it in its statement. It is the
/// cause when the parse with a name in its place gets past the token the first parse stopped
/// at and past the token after the word. So `x = a is ;`, where no name in place of `is`
/// helps, and `y = not x;`, where a name in place of `not` stops at `x`, keep the parse's own
/// message.
fn reserved(t: &Toks<'_, '_>, far: usize) -> Option<Clause> {
    // Complexity tradeoff: the naive check tries a name in place of each reserved word of the
    // statement, one parse each: O(k * n) for k words in a unit of n tokens. This tries at
    // most three, the word the parse stopped at and the last and the first before it in the
    // statement: O(n). A reserved word between those two keeps the parse's own message
    // (COMPLEXITY.md, MSG-keyword-as-name).
    let keyword = |i: usize| t.toks.get(i).is_some_and(|k| k.0 == Kind::Keyword);
    let first = t.stmt_first(far);
    let last = (first..far).rev().find(|&i| keyword(i));
    let at = [
        Some(far).filter(|&i| keyword(i)),
        last,
        (first..far).find(|&i| keyword(i)),
    ]
    .into_iter()
    .flatten()
    .find(|&i| t.renamed(&[i], "x", far.max(i + 1)))?;
    let word = t.t(at);
    let (_, what, like) = RESERVED.iter().find(|r| r.0 == word)?;
    let name = t.unused(like);
    let span = t.span(at);
    // The repair: the word's line with the name in place of the word, everywhere on the line
    // the word stands, or else only here; offered when the parse then gets past the line.
    let (a, b) = t.line(at);
    let everywhere: Vec<usize> = (a..=b).filter(|&i| keyword(i) && t.t(i) == word).collect();
    let line = &t.text[t.span(a).start..t.span(b).end];
    let repaired = [everywhere, vec![at]]
        .into_iter()
        .find(|s| t.renamed(s, &name, b))
        .map(|s| {
            let mut out = String::new();
            let mut from = t.span(a).start;
            for i in s {
                out.push_str(&t.text[from..t.span(i).start]);
                out.push_str(&name);
                from = t.span(i).end;
            }
            out.push_str(&t.text[from..t.span(b).end]);
            out
        });
    let (try_, repair) = match &repaired {
        Some(r) => (format!("Try `{r}` instead."), format!("repair: `{r}`")),
        None => (
            format!("Try another name, such as `{name}`."),
            format!("repair: another name, such as `{name}`"),
        ),
    };
    Some(Clause {
        row: Some(Row::ReservedWordAsName),
        message: format!("Reserved word used as a name: `{line}`. {try_}"),
        span,
        notes: vec![
            (span, format!("`{word}` is reserved: {what}")),
            (
                span,
                format!("rename the other uses of `{word}` as a name too"),
            ),
            (span, repair),
        ],
    })
}

/// The [`Clause`] for the removed declaration `mutable x = e;` (row "A `mutable` declaration",
/// DESIGN.md sec:generations): `mutable` is an ordinary name, so the parse stops at the name
/// after it. In the body of a loop the repair is `initial x = e with carryForward;`, `local`
/// moved to the update where one was written; elsewhere it is the plain binding `x = e;`. The
/// repair is parsed once: linear in the statement, on the error path only.
fn mutable_decl(t: &Toks<'_, '_>, far: usize) -> Option<Clause> {
    let k = if t.t(far) == "mutable" {
        far
    } else if far > 0 && t.t(far - 1) == "mutable" {
        far - 1
    } else {
        return None;
    };
    // `mutable` and a name, then what a binding has after its first name: `=`, `:` or `,`.
    if t.toks.get(k)?.0 != Kind::Ident
        || t.toks.get(k + 1)?.0 != Kind::Ident
        || !matches!(t.t(k + 2), "=" | ":" | ",")
    {
        return None;
    }
    let first = t.stmt_first(k);
    if t.decl_first(first) != k {
        return None;
    }
    let close = t.stmt_stop(k);
    if t.t(close) != ";" {
        return None;
    }
    let local = k > first && t.t(k - 1) == "local";
    let name = t.t(k + 1);
    let binding = t.between(k + 1, close - 1);
    let start = if local { k - 1 } else { k };
    let written = t.between(start, close);
    let span = Span {
        start: t.span(start).start,
        end: t.span(close).end,
    };
    let (_, looped) = t.block_of(first);
    let carry = crate::ast::CARRY_FORWARD;
    let (rule, repair, why) = match looped {
        Some(_) => (
            format!(
                "the loop whose body holds the declaration: a variable a loop updates is a \
                 recurrence, defined on every frame, so each step updates it on every path; one \
                 that keeps its value on a step that does not update it is given its value \
                 before step 0 by an `initial` statement with `with {carry}`"
            ),
            format!("initial {binding} with {carry};"),
            if local {
                format!(
                    "its value before step 0, carried forward on a step that does not update \
                     `{name}`, with `local` moved to the update of `{name}`, `local {name}' = …;`"
                )
            } else {
                format!(
                    "its value before step 0, carried forward on a step that does not update \
                     `{name}`"
                )
            },
        ),
        None => (
            format!(
                "outside the body of a loop a name is bound once, with no `mutable`; in a loop, \
                 a variable that keeps its value on a step that does not update it is given its \
                 value before step 0 by an `initial` statement with `with {carry}`"
            ),
            if local {
                format!("local {binding};")
            } else {
                format!("{binding};")
            },
            "a plain binding".to_string(),
        ),
    };
    // The headline shows the declaration and ends with the first repair; the rule is a note.
    let mut notes = vec![(looped.map_or(span, |l| t.span(l)), rule)];
    let message = if t.parses(start, close, &repair) {
        notes.push((span, format!("repair: `{repair}`, {why}")));
        format!("Zed has no `mutable`: `{written}`. Try `{repair}` instead.")
    } else {
        format!("Zed has no `mutable`: `{written}`.")
    };
    Some(Clause {
        row: Some(Row::MutableDeclaration),
        message,
        span,
        notes,
    })
}

/// The [`Clause`] for a word other than `carryForward` after `with` at the end of an `initial`
/// statement, as `initial x = 0 with carry;` (row "A word other than `carryForward` after `with`
/// at the end of an `initial` statement", DESIGN.md sec:generations): the parse reads `with
/// carry` as a facet and stops where its `(` should be. Every word there is offered
/// `carryForward`, not only a word close to it in spelling: the grammar admits exactly one word
/// with no parentheses in that place, so it is the only repair, and a far word such as `keep`
/// or `sticky` means it as surely as `carry` does. The scans run over the statement, and the
/// repair is parsed once: linear in the statement, on the error path only.
fn carry_word(t: &Toks<'_, '_>, far: usize) -> Option<Clause> {
    // The words between `with` and `;`: back from `far` over names to the `with`, then on to the
    // `;`. The parse stops at the `;` after one word, or at the second of several words.
    let mut w = far;
    while w > 0 && t.toks[w - 1].0 == Kind::Ident {
        w -= 1;
    }
    let w = w.checked_sub(1)?;
    let mut close = far;
    while t.toks.get(close)?.0 == Kind::Ident {
        close += 1;
    }
    if t.t(w) != "with" || close == w + 1 || t.t(close) != ";" {
        return None;
    }
    // The `with` ends an `initial` statement, at its own depth.
    let first = t.stmt_first(w);
    let k = t.decl_first(first);
    if t.t(k) != "initial" || (first..w).map(|i| depth(t.t(i))).sum::<i32>() != 0 {
        return None;
    }
    let carry = crate::ast::CARRY_FORWARD;
    let words = t.between(w + 1, close - 1);
    let written = t.between(first, close);
    let repair = format!("{} with {carry};", t.between(first, w - 1));
    let span = Span {
        start: t.span(first).start,
        end: t.span(close).end,
    };
    let at_words = Span {
        start: t.span(w + 1).start,
        end: t.span(close - 1).end,
    };
    // The names the statement gives a value, for the note: `c`, or `a` and `b`.
    let names: Vec<String> = (k + 1..w)
        .take_while(|&i| !matches!(t.t(i), "=" | ":" | "["))
        .filter(|&i| t.toks[i].0 == Kind::Ident)
        .map(|i| format!("`{}`", t.t(i)))
        .collect();
    let (named, them) = match names.len() {
        0 => return None,
        1 => (format!("the value of {}", names[0]), "it"),
        _ => (format!("the values of {}", and_list(&names)), "them"),
    };
    let mut notes = vec![(
        at_words,
        format!(
            "`{carry}` is the one word that stands alone after `with` at the end of an `initial` \
             statement, and keeps {named} on a step that does not update {them}; a facet after \
             `with` takes its arguments in parentheses, as `with {}(…)`",
            t.t(w + 1)
        ),
    )];
    let message = if t.parses(first, close, &repair) {
        notes.push((
            span,
            format!("repair: `{repair}`, `{carry}` in place of `{words}`"),
        ));
        format!("Expected `{carry}` after `with`: `{written}`. Try `{repair}` instead.")
    } else {
        format!("Expected `{carry}` after `with`: `{written}`.")
    };
    Some(Clause {
        row: Some(Row::CarryWord),
        message,
        span,
        notes,
    })
}

/// The [`Clause`] for a union, intersection or difference written bare as the key of `->` or
/// `->?`, or as the guarantee or the permission of `L .. U -> V` (row "Union, intersection or
/// difference written bare as a key, guarantee or permission"; DESIGN.md sec:grammar, author
/// P222): `Arrow` takes a `TypeNot` there, so the parse stops at the connective or at the arrow
/// after it. The type is found from the first arrow at or after the token the parse stopped at,
/// at its bracket depth: back from it to the token before the type (`:`, `=`, `,`, `;`, a
/// keyword or an unmatched opening bracket), and on to the token after it. The first repair
/// parenthesizes each key, guarantee and permission of the type that holds a connective
/// outside brackets, `(int | #a) -> int`; where the type has one arrow, `->` or `->?`, the
/// second makes the last operand of the connective the key, `int | (#a -> int)`. Each repair
/// is offered only when the parse gets past it. The scans run over the type and each repair is
/// one more parse: linear in the unit, on the error path only.
fn bare_key(t: &Toks<'_, '_>, far: usize) -> Option<Clause> {
    let arrow = |i: usize| matches!(t.t(i), "->" | "->?" | "..");
    let keyword = |i: usize| t.toks.get(i).is_some_and(|k| k.0 == Kind::Keyword);
    let n = t.tokens.len();
    // The first arrow at or after `far`, at its depth, before the type ends.
    let (mut a, mut d) = (far, 0);
    while !(d == 0 && arrow(a)) {
        let s = t.t(a);
        if a >= n || d == 0 && matches!(s, "," | ";" | "=") || d + depth(s) < 0 {
            return None;
        }
        d += depth(s);
        a += 1;
    }
    // Back from the arrow to the first token of the type.
    let (mut first, mut d) = (a, 0);
    while first > 0 {
        let p = t.t(first - 1);
        if d == 0 && (matches!(p, ":" | "," | "=" | ";") || keyword(first - 1)) || d - depth(p) < 0
        {
            break;
        }
        d -= depth(p);
        first -= 1;
    }
    // On from the arrow to the token after the type. A type holds the keywords of its facets,
    // its `where` and its bounds, and of `matching` and `positional`.
    let (mut after, mut d) = (a, 0);
    while after < n {
        let x = t.t(after);
        let ends = keyword(after)
            && !matches!(
                x,
                "with" | "where" | "for" | "in" | "matching" | "positional"
            );
        if d == 0 && (matches!(x, "," | ";" | "=") || ends) || d + depth(x) < 0 {
            break;
        }
        d += depth(x);
        after += 1;
    }
    let last = after.checked_sub(1)?;
    // Each key, guarantee and permission that holds a connective outside brackets: its first
    // and last tokens, its first and last connectives, and the arrow after it.
    let mut bare: Vec<(usize, usize, usize, usize, usize)> = Vec::new();
    let (mut from, mut conn, mut arrows, mut d) = (first, None, 0, 0);
    for i in first..after {
        if d == 0 && arrow(i) {
            arrows += 1;
            if let Some((c, l)) = conn {
                bare.push((from, i - 1, c, l, i));
            }
            from = i + 1;
            conn = None;
        } else if d == 0 && matches!(t.t(i), "|" | "&" | "\\") {
            conn = Some(conn.map_or((i, i), |(c, _): (usize, usize)| (c, i)));
        }
        d += depth(t.t(i));
    }
    // The parse stopped at this key, guarantee or permission.
    let &(key_first, key_last, c, l, at) = bare.iter().find(|b| b.4 == a)?;
    // A connective with no operand before or after it, `| #a -> int` or `int | -> int`, is no
    // union: the plain syntax error says what is missing.
    if c == key_first || l == key_last {
        return None;
    }
    let text = |a: usize, b: usize| &t.text[a..b];
    let start = t.span(first).start;
    let end = t.span(last).end;
    let written = text(start, end);
    // Each key, guarantee and permission in parentheses.
    let mut grouped = String::new();
    let mut from = start;
    for &(f, l, ..) in &bare {
        grouped.push_str(text(from, t.span(f).start));
        grouped.push('(');
        grouped.push_str(text(t.span(f).start, t.span(l).end));
        grouped.push(')');
        from = t.span(l).end;
    }
    grouped.push_str(text(from, end));
    let key = text(t.span(key_first).start, t.span(key_last).end);
    let role = role_of(t, key_first, at);
    let mut repairs = Vec::new();
    if t.parses(first, last, &grouped) {
        let what = if bare.len() == 1 {
            format!("with the {role} `{key}`")
        } else {
            "with each key, guarantee and permission in parentheses".to_string()
        };
        repairs.push((grouped, what));
    }
    // The last operand of the connective as the key.
    if arrows == 1 && t.t(at) != ".." {
        let operand = text(t.span(l + 1).start, t.span(key_last).end);
        let other = format!(
            "{}({})",
            text(start, t.span(l + 1).start),
            text(t.span(l + 1).start, end)
        );
        if t.parses(first, last, &other) {
            repairs.push((other, format!("with the key `{operand}`")));
        }
    }
    let (kind, capital) = match t.t(c) {
        "|" => ("union", "Union"),
        "&" => ("intersection", "Intersection"),
        _ => ("difference", "Difference"),
    };
    let mut headline = format!("{capital} written bare as a {role}: `{written}`.");
    if let Some((r, _)) = repairs.first() {
        headline.push_str(&format!(" Try `{r}` instead."));
    }
    let span = t.span(c);
    let mut notes = vec![(
        span,
        format!(
            "a {kind} as a {role} is written in parentheses, which say whether `{}` or `{}` \
             groups first",
            t.t(c),
            t.t(at)
        ),
    )];
    for (r, what) in repairs {
        notes.push((span, format!("repair: `{r}`, {what}")));
    }
    Some(Clause {
        row: Some(Row::BareKey),
        message: headline,
        span,
        notes,
    })
}

/// The [`Clause`] for a pattern built with an operator, an or-pattern `p | q`, a range `a..=b`,
/// `a..<b` or `a..`, or an `is`-pattern `n is T`, written bare in a `match` arm or an `else`
/// tail (row "Pattern built with an operator, written bare"; DESIGN.md step L2.7b): such a
/// pattern stands in parentheses that hold it alone, so the parse stops at its operator, or,
/// where it opens a group, `(#a | #b, x)` or `#p(0..=9, y)`, at the `,` after it. The pattern
/// runs from the `(`, `,` or `:` before its operator to the `,`, `)`, `->` or `where` after it,
/// at its depth; the arm, from the `{`, `,` or `else` before it to the `->` after it at the
/// arm's depth, and on to the `,`, `;` or closing bracket after its value. In an `else` tail
/// whose payload parses as an expression, `r else #ok(v: n is int) -> 0`, the parse stops at
/// the `->` instead, and the operator is where a parse of the payload as a pattern stops. The
/// repair is the arm with the pattern in parentheses, and the clause is given only when the parse
/// gets past it. Each scan runs over the arm, its `match` head and the arms before it, and the
/// repair is one or two more parses: linear in the unit, on the error path only.
fn bare_pattern(t: &Toks<'_, '_>, far: usize) -> Option<Clause> {
    let n = t.tokens.len();
    let op = |i: usize| matches!(t.t(i), "|" | "..=" | "..<" | ".." | "is");
    // The operator: the token the parse stopped at, or, at a `,`, the first operator before it
    // in its group, at its depth.
    let at = if op(far) {
        far
    } else if t.t(far) == "," {
        let (mut i, mut d, mut found) = (far, 0, None);
        while i > 0 {
            let p = t.t(i - 1);
            if d == 0 && matches!(p, "," | ":") || d - depth(p) < 0 {
                break;
            }
            d -= depth(p);
            i -= 1;
            if d == 0 && op(i) {
                found = Some(i);
            }
        }
        found?
    } else if t.t(far) == "->" {
        // `r else #ok(v: n is int) -> 0`: the payload parses as an expression, so the parse
        // stops at the `->` after it. The operator is the first in the payload, which runs
        // back from the `->` to its `else`, at the `->`'s depth.
        let (mut i, mut d) = (far, 0);
        while i > 0 && !(d == 0 && t.t(i - 1) == "else") {
            let p = t.t(i - 1);
            if d == 0 && matches!(p, "," | ";" | "=" | "->") || d - depth(p) < 0 {
                return None;
            }
            d -= depth(p);
            i -= 1;
        }
        if i == 0 {
            return None;
        }
        // The payload's parse as a pattern stops at the operator: one more parse of it.
        let mut p = Parser::new(t.g, t.ring, t.toks);
        p.rule_node(t.g.rule("Pattern")?, i, false);
        if p.far >= far || !op(p.far) {
            return None;
        }
        p.far
    } else {
        return None;
    };
    // The pattern: back from the operator to its first token, on to its last. A range or an
    // `is`-pattern written bare as an alternative, `(#a | n is int)`, stops at the `|` before
    // it, and a range at the `|` after it; an `is`-pattern's type takes the `|` after it.
    let bounds = |at: usize| {
        let bar = t.t(at) != "|";
        let (mut first, mut d) = (at, 0);
        while first > 0 {
            let p = t.t(first - 1);
            if d == 0 && (matches!(p, "," | ":" | "->" | "else") || bar && p == "|")
                || d - depth(p) < 0
            {
                break;
            }
            d -= depth(p);
            first -= 1;
        }
        let range = bar && t.t(at) != "is";
        let (mut after, mut d) = (at, 0);
        while after < n {
            let x = t.t(after);
            if d == 0 && (matches!(x, "," | "->" | "where" | ";") || range && x == "|")
                || d + depth(x) < 0
            {
                break;
            }
            d += depth(x);
            after += 1;
        }
        (first, after)
    };
    let (mut at, (mut first, mut after)) = (at, bounds(at));
    if t.t(at) == "|" {
        // `(0..=9 | #a)`: the parse stops at the `|` after a range it read as one; the range
        // before it, at its depth, is the pattern written bare.
        let mut d = 0;
        if let Some(j) = (first..at).find(|&j| {
            let hit = d == 0 && op(j) && t.t(j) != "|";
            d += depth(t.t(j));
            hit
        }) {
            at = j;
            (first, after) = bounds(j);
        }
    }
    let last = after.checked_sub(1)?;
    if first == at && t.t(at) != "is" || last == at && t.t(at) != ".." {
        // An operator with no operand before or after it is no pattern: the plain syntax error
        // says what is missing. The name before `is` and the bound after `..` may be left out.
        return None;
    }
    // The arm's `->`: the first after the pattern at the lowest depth reached, outside every
    // group the pattern stands in.
    let (mut arrow, mut d, mut low) = (after, 0, 0);
    while arrow < n && !(d == low && t.t(arrow) == "->") {
        let x = t.t(arrow);
        if d == low && matches!(x, ";" | "=") {
            return None;
        }
        d += depth(x);
        low = low.min(d);
        arrow += 1;
    }
    if arrow >= n {
        return None;
    }
    // The arm: back from its `->` to its first token, which follows `{`, `,` or `else`.
    let (mut start, mut d) = (arrow, 0);
    while start > 0 {
        let p = t.t(start - 1);
        if d == 0 && matches!(p, "," | "else" | ";" | "=") || d - depth(p) < 0 {
            break;
        }
        d -= depth(p);
        start -= 1;
    }
    let before = start.checked_sub(1)?;
    if !arm_head(t, before) {
        return None;
    }
    // On from the `->` to the end of the arm's value.
    let (mut end, mut d) = (arrow, 0);
    while end < n {
        let x = t.t(end);
        if d == 0 && matches!(x, "," | ";") || d + depth(x) < 0 {
            break;
        }
        d += depth(x);
        end += 1;
    }
    let end = end.checked_sub(1)?;
    if start > first {
        // The `->` found is not this pattern's arm's: the pattern stands in no arm.
        return None;
    }
    let text = |a: usize, b: usize| &t.text[a..b];
    let (ps, pe) = (t.span(first).start, t.span(last).end);
    let (arm_s, arm_e) = (t.span(start).start, t.span(end).end);
    let pattern = text(ps, pe);
    let repair = format!("{}({pattern}){}", text(arm_s, ps), text(pe, arm_e));
    let what = match t.t(at) {
        "|" => "an or-pattern",
        "is" => "an `is`-pattern",
        _ => "a range pattern",
    };
    // Parentheses are the cure only when the arm then parses: not for `r else n is int -> 0`,
    // whose tail takes an atom pattern alone, nor for `(1..5)`, which is no range pattern. The
    // plain syntax error then says what the parse expected.
    if !t.parses(start, end, &repair) {
        return None;
    }
    let span = Span { start: ps, end: pe };
    Some(Clause {
        row: Some(Row::BareOperatorPattern),
        message: format!("`{pattern}` is {what}; write it in parentheses. Try `{repair}` instead."),
        span,
        notes: vec![(span, format!("repair: `{repair}`"))],
    })
}

/// The [`Clause`] for an or-pattern as the pattern of an `else` tail, bare, `r else #a | #b -> 0`,
/// or in parentheses, `r else (#a | #b) -> 0`: the tail takes one atom pattern (`ElseTail` in
/// DESIGN.md sec:grammar; zed/grammar/cases.txt refuses `x else (#a | #b) -> d`), so the parse
/// stops at the `|`. The repair is the `match` the tail stands for, `e else P -> d` being
/// `match e { P -> d, x -> x }` (the desugaring of `ElseTail`, sec:grammar): exact, where a
/// chain of tails, `r else #a -> 0 else #b -> 0`, would also send a value `#b` of `d` to the
/// second tail. The operand `e` runs back from the `else`, at its depth, over the operators that
/// bind tighter than `else` and over the `else` tails before it, to a `=`, `,`, `;`, `<-`, an
/// unmatched opening bracket, or an arrow that ends no `else` tail's pattern (a lambda's, an
/// arm's); a keyword that begins a form, as `match` or `if`, gives no clause, since the form's
/// extent is not found by this scan. The head is parenthesized only where it does not parse
/// bare. No row: the plain syntax error is made precise, as for the other clauses with none.
/// Each scan runs over the statement, and the repair is one or two more parses: linear in the
/// unit, on the error path only.
fn else_or_pattern(t: &Toks<'_, '_>, far: usize) -> Option<Clause> {
    if t.t(far) != "|" {
        return None;
    }
    let n = t.tokens.len();
    // Back from the `|` to its `else`, through at most the one `(` right after the `else`.
    let (mut i, mut d) = (far, 0);
    loop {
        let p = t.t(i.checked_sub(1)?);
        if p == "else" && d <= 0 {
            break;
        }
        if d == 0 && matches!(p, "," | ";" | "=" | "->") {
            return None;
        }
        d -= depth(p);
        if d < -1 || d == -1 && p != "(" {
            return None;
        }
        i -= 1;
    }
    let e = i - 1;
    let wrapped = d == -1;
    if wrapped && t.t(e + 1) != "(" {
        // `else #p(#a | #b, x) -> 0`: the `(` is a payload's, whose clause is `bare_pattern`'s.
        return None;
    }
    let first = if wrapped { e + 2 } else { e + 1 };
    // On from the `|` to the pattern's last token and the `->` after it.
    let (mut j, mut d) = (far, 0);
    let arrow = loop {
        if j >= n {
            return None;
        }
        let x = t.t(j);
        if wrapped && d == 0 && x == ")" {
            if t.t(j + 1) != "->" {
                return None;
            }
            break j + 1;
        }
        if !wrapped && d == 0 && x == "->" {
            break j;
        }
        if d == 0 && matches!(x, "," | ";" | "=") || d + depth(x) < 0 {
            return None;
        }
        d += depth(x);
        j += 1;
    };
    let last = if wrapped { arrow - 2 } else { arrow - 1 };
    // On from the `->` to the end of the tail's value: a later `else` tail is not part of it.
    let (mut end, mut d) = (arrow + 1, 0);
    while end < n {
        let x = t.t(end);
        if d == 0 && matches!(x, "," | ";" | "else") || d + depth(x) < 0 {
            break;
        }
        d += depth(x);
        end += 1;
    }
    let end = end.checked_sub(1)?;
    if end <= arrow {
        return None;
    }
    // Whether the `->` at `a` ends an `else` tail's atom pattern, `else #c -> ` or
    // `else #p(x) -> `.
    let tail_arrow = |a: usize| {
        let mut k = a;
        if k > 0 && t.t(k - 1) == ")" {
            let mut d = 0;
            loop {
                k -= 1;
                d -= depth(t.t(k));
                if d == 0 || k == 0 {
                    break;
                }
            }
        }
        k >= 2 && t.t(k - 1).starts_with('#') && t.t(k - 2) == "else"
    };
    // The keywords an operand may hold: the operators, the literals and `else`.
    let inner = |w: &str| {
        matches!(
            w,
            "as" | "into"
                | "in"
                | "not"
                | "is"
                | "with"
                | "without"
                | "div"
                | "mod"
                | "true"
                | "false"
                | "this"
                | "else"
        )
    };
    // Back from the `else` to the operand's first token.
    let (mut start, mut d) = (e, 0);
    while start > 0 {
        let p = t.t(start - 1);
        if d == 0 && matches!(p, "=" | "," | ";" | "<-") || d - depth(p) < 0 {
            break;
        }
        if d == 0 && p == "->" && !tail_arrow(start - 1) {
            break;
        }
        if d == 0 && t.toks[start - 1].0 == Kind::Keyword && !inner(p) {
            return None;
        }
        d -= depth(p);
        start -= 1;
    }
    if start == e {
        return None;
    }
    let text = |a: usize, b: usize| &t.text[a..b];
    let operand = text(t.span(start).start, t.span(e - 1).end);
    let (ps, pe) = (t.span(first).start, t.span(last).end);
    let pattern = text(ps, pe);
    let value = text(t.span(arrow + 1).start, t.span(end).end);
    let repair = [
        format!("match {operand} {{ ({pattern}) -> {value}, x -> x }}"),
        format!("match ({operand}) {{ ({pattern}) -> {value}, x -> x }}"),
    ]
    .into_iter()
    .find(|r| t.parses(start, end, r))?;
    let span = Span { start: ps, end: pe };
    Some(Clause {
        row: None,
        message: format!(
            "An `else` tail takes one atom pattern, and `{pattern}` is an or-pattern. Try \
             `{repair}` instead."
        ),
        span,
        notes: vec![(span, format!("repair: `{repair}`"))],
    })
}

/// Whether token `before`, the one before an arm's first token, opens an arm: the `else` of
/// an `else` tail, or the `{` of a `match`, or the `,` after an arm of one, found back over the
/// arms before it, at their depth, to the `{` and the `match` before its value.
fn arm_head(t: &Toks<'_, '_>, before: usize) -> bool {
    let mut i = before;
    match t.t(i) {
        "else" => return true,
        "{" | "," => {}
        _ => return false,
    }
    // Back over the arms before it to the `{`.
    let mut d = 0;
    while t.t(i) != "{" || d != 0 {
        if i == 0 || d == 0 && t.t(i) == ";" {
            return false;
        }
        d -= depth(t.t(i));
        if d < 0 {
            // An unmatched `(` or `[`: no arm.
            return false;
        }
        i -= 1;
    }
    // Back over the value matched to `match`.
    let mut d = 0;
    while i > 0 {
        i -= 1;
        let p = t.t(i);
        if d == 0 && p == "match" {
            return true;
        }
        if d == 0 && matches!(p, ";" | "=" | "{" | ",") || d - depth(p) < 0 {
            return false;
        }
        d -= depth(p);
    }
    false
}

/// What the tokens from `first` up to the arrow `at` are in their type: the guarantee of `..`,
/// the permission between `..` and `->`, or a key.
fn role_of(t: &Toks<'_, '_>, first: usize, at: usize) -> &'static str {
    if t.t(at) == ".." {
        "guarantee"
    } else if first > 0 && t.t(first - 1) == ".." {
        "permission"
    } else {
        "key"
    }
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
        Tok::Infix(_) => Kind::Infix,
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
