//! The messages for a parse that stops in a `with` clause that gives a sentinel value, and for
//! a reserved word written where a name stands (DESIGN.md sec:generations, sec:lexical,
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

use std::collections::HashSet;

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

    /// Whether the parse, with the name `name` in place of each token of `at`, gets past token
    /// `past`.
    fn renamed(&self, at: &[usize], name: &str, past: usize) -> bool {
        let mut fixed = self.toks.to_vec();
        for &i in at {
            fixed[i] = (Kind::Ident, name);
        }
        reaches(self.g, self.ring, self.start, &fixed, past)
    }

    /// `like`, or `like2`, `like3` and so on, the first that is no word of the text.
    fn unused(&self, like: &str) -> String {
        let words: HashSet<&str> = self
            .text
            .split(|c: char| !(c.is_alphanumeric() || c == '_'))
            .collect();
        let mut name = like.to_string();
        let mut n = 1;
        while words.contains(name.as_str()) {
            n += 1;
            name = format!("{like}{n}");
        }
        name
    }

    /// The first and last tokens on the source line of token `i`.
    fn line(&self, i: usize) -> (usize, usize) {
        let span = self.span(i);
        let lo = self.text[..span.start].rfind('\n').map_or(0, |k| k + 1);
        let hi = self.text[span.end..]
            .find('\n')
            .map_or(self.text.len(), |k| span.end + k);
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
/// sentinel value, or at or after a reserved word written where a name stands. The scans run
/// over the statement, its block or its line, and each check of a word or a repair is one more
/// parse: linear in the unit, on the error path only.
pub(super) fn clause(t: &Toks<'_, '_>, far: usize) -> Option<Clause> {
    with_item(t, far).or_else(|| reserved(t, far))
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

/// Each reserved word, in the order of [`crate::lex::KEYWORDS`], with what it begins (the
/// note "`word` is reserved: ...") and a name of like meaning that the repair offers in its
/// place.
pub const RESERVED: [(&str, &str, &str); 38] = [
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
        "it ends a loop early with a value, as `break e`",
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
        "mutable",
        "it marks a binding the program changes, as `mutable total = 0;`",
        "changing",
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
