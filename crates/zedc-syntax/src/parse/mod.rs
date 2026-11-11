//! The parser (step L1.8): tokens become a tree of the rules of DESIGN.md sec:grammar.
//!
//! The parser runs that grammar itself, copied into `zed/grammar/`, as a packrat parser: each
//! rule tries its alternatives in order and memoizes its result at each token. So the
//! precedence ladder is the grammar's, rung for rung, and its trees are the trees
//! the `check` tool of `crates/zed-tools` builds, with this same parser. A parse is at a ring:
//! only the alternatives of that layer and below are tried. Each node records its alternative,
//! so a node of a later layer than the program's is found later, by the elaborator, not here. An alternative marked `~` builds no
//! node, and the rule's match is the node of the marked rule.
//!
//! A literal in the grammar matches a keyword, an operator or a name with its text, so the
//! positional words `where`, `sep` and `initial` are names the grammar matches by their text.
//!
//! A left-recursive rule grows from a failed seed, by the Squirrel parser's algorithm
//! (`squirrel_parser.tex`, fig. Code); a grammar with no left recursion never reaches that code.

pub mod engine;
mod grammar;

use std::fmt;
use std::mem;
use std::sync::OnceLock;

pub use engine::{Expected, Input, Node, Parser, literal_matches};
pub use grammar::{Alt, Expr, Grammar, Kind, Line, Rule, is_space, marked_rule, split_line};

use crate::lex::{Part, Span, Tok, Token};

/// The highest layer, and the ring at which every alternative is tried.
pub const TOP: u32 = 29;

/// The grammar of sec:grammar: its syntactic grammar and its documentation notation.
pub fn grammar() -> &'static Grammar {
    static G: OnceLock<Grammar> = OnceLock::new();
    G.get_or_init(|| {
        Grammar::read(&[
            include_str!("../../../../zed/grammar/syntax.peg"),
            include_str!("../../../../zed/grammar/notation.peg"),
        ])
        .expect("the copied grammar reads")
    })
}

/// A parse tree: its nodes, the root's index, and the trees of the string holes in its tokens.
#[derive(Debug)]
pub struct Tree {
    /// The nodes; a node's children come before it.
    pub nodes: Vec<Node>,
    /// The root.
    pub root: usize,
    /// The tree of each `${…}` hole, in the order of the tokens, each parsed as an `Expr`.
    pub holes: Vec<Tree>,
}

/// Holes nest as deep as the source does: each is moved to a work list before its parent goes.
impl Drop for Tree {
    fn drop(&mut self) {
        let mut stack = mem::take(&mut self.holes);
        while let Some(mut t) = stack.pop() {
            stack.append(&mut t.holes);
        }
    }
}

impl Tree {
    /// The rule name of node `n`.
    pub fn name(&self, n: usize) -> &'static str {
        &grammar().rules[self.nodes[n].rule].name
    }

    /// The layer of the alternative node `n` matched.
    pub fn layer(&self, n: usize) -> u32 {
        let node = &self.nodes[n];
        grammar().rules[node.rule].alts[node.alt].layer
    }
}

/// Why a parse failed: the furthest token any alternative reached, and what it expected there.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    /// The span of that token (empty at the end of the text), or of the `..` that [`DOTS`]
    /// is about.
    pub span: Span,
    /// The literals (quoted) and token kinds expected there, sorted.
    pub expected: Vec<String>,
    /// A message that says more than the expected tokens: [`DOTS`] for a `..` in a list.
    pub message: Option<&'static str>,
    /// The boundary item written with neither `initial` nor an index that the parse stopped
    /// at, as `with x = 0`; the error's span is its `=`.
    pub bare: Option<Box<Bare>>,
    /// The boundary clause written in a test case that the parse stopped at, as
    /// `1 with x = 0 -> 1`; when it is set, `bare` is not.
    pub case: Option<Box<InCase>>,
}

/// A boundary clause written in a test case, as `1 with x = 0 -> 1`. A test case is
/// `Expr12 '->' Expr12` (DESIGN.md sec:grammar), and inside an expression `with` begins only a
/// facet `with f(…)` or an update `with { … }`, so a test case takes no boundary clause.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InCase {
    /// The function or method the test table follows, as `double` or `Counter.tick`, when the
    /// unit parses once the clause is deleted.
    pub function: Option<String>,
    /// The test case, as written.
    pub case: String,
    /// Its span.
    pub case_span: Span,
    /// The span of `test {`, which opens the table.
    pub table: Span,
    /// The clause, from `with` to the end of its last item's value.
    pub clause: String,
    /// Its span.
    pub clause_span: Span,
    /// The code before `with`, as written.
    pub before: String,
    /// The first item up to its `=`: `x =`, `initial x =` or `x[k] =`.
    pub head: String,
    /// The first item's variable.
    pub name: String,
    /// The first item, from its name to the end of its value: `x = 0`.
    pub item: String,
    /// The text of the first item's value.
    pub value: String,
    /// The value of the first item written with neither `initial` nor an index, and its
    /// variable, when the clause holds one.
    pub bare: Option<(String, String)>,
    /// The two sides of the test case without the clause, when the case has its `->`.
    pub sides: Option<(String, String)>,
    /// Whether the clause stands on the left side, so the first item's value ends before the
    /// case's `->`.
    pub left: bool,
    /// The test case with the clause deleted, when that parses.
    pub deleted: Option<String>,
    /// The test case with the clause written as an update of fields, `with { x = 0 }`, when
    /// every item is `x = e`, the code before `with` is not a lone literal, and that parses.
    pub update: Option<String>,
}

impl InCase {
    /// What the error says.
    pub fn message(&self) -> String {
        let InCase {
            function,
            case,
            clause,
            before,
            head,
            name,
            item,
            value,
            ..
        } = self;
        let of = function
            .as_ref()
            .map(|f| format!(" of `{f}`"))
            .unwrap_or_default();
        let mut m = format!(
            "The test case `{case}`{of} holds the boundary clause `{clause}`, and a test case \
             takes no boundary clause."
        );
        if let Some((a, b)) = &self.sides {
            m.push_str(&match function.as_deref() {
                Some("main") => format!(
                    " It states that a wave of `main` reading the ports `{a}` writes the bytes \
                     `{b}`."
                ),
                Some(f) => format!(" It states that `{f}` applied to `{a}` gives `{b}`."),
                None => format!(
                    " It states that the function the table follows, applied to `{a}`, gives \
                     `{b}`."
                ),
            });
        }
        m.push_str(&format!(
            " Each side of a test case is an expression, and in an expression `with` is followed \
             only by a facet, as `{before} with f(…)`, or by an update of fields, as `{before} \
             with {{ {name} = … }}`; here `with` is followed by `{head}`, which begins a boundary \
             item. A boundary clause gives a variable its value below its first step or index, \
             and it follows only the value of a binding, as `{name}' = … with initial {name} = \
             {value};`, or of an indexed definition, as `{name}[i in 0..<n] = … with initial \
             {name} = {value};`."
        ));
        if self.left {
            m.push_str(&format!(
                " The item is read as `{item}`: its value ends before `->`, the arrow of the test \
                 case."
            ));
        }
        if let Some((n, v)) = &self.bare {
            m.push_str(&format!(
                " Written with neither `initial` nor an index, `with {n} = {v}` would be refused \
                 after a binding too: it reads as though `{n}` took the value `{v}` anew on every \
                 step, and the sentinel value is written `with initial {n} = {v}`."
            ));
        }
        m
    }
}

/// A boundary item with neither `initial` nor an index, as `with x = 0` (row "Boundary item
/// with neither `initial` nor an index", DESIGN.md sec:generations).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bare {
    /// The variable.
    pub name: String,
    /// The text of the value, `…` when there is none.
    pub value: String,
    /// The item, from its name to the end of its value.
    pub item: Span,
    /// The statement it stands on, its `;` included where there is one.
    pub stmt: Span,
    /// For an indexed definition of the variable over one key `i in lo..`, the key of the entry
    /// below the domain: `lo - 1`, worked out when `lo` is an integer literal.
    pub below: Option<String>,
    /// When the item follows code that takes no boundary clause (a push, a guard, a `return`, an
    /// expression), that code and the repairs; `None` on a binding or an indexed definition.
    pub misplaced: Option<Misplaced>,
}

/// A boundary item that follows code taking no boundary clause, as `p <- t with x = 0;`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Misplaced {
    /// The code before `with`, as written.
    pub before: String,
    /// Whether that code is a push.
    pub push: bool,
    /// The repairs, each one checked to parse, in the order the menu lists them.
    pub repairs: Vec<Repair>,
}

/// One repair of a [`Misplaced`] item: the text that replaces the code at `span`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Repair {
    /// The code replaced.
    pub span: Span,
    /// The code that replaces it.
    pub text: String,
    /// What the repair does.
    pub fix: Fix,
}

/// What a [`Repair`] does.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fix {
    /// The generation push `x' <- e` written as the binding `x' = e`, which takes the clause.
    Binding,
    /// The item, with `initial`, moved to the first binding of the block that defines the
    /// variable.
    Moved {
        /// The statement the item stood on, without it.
        here: String,
    },
    /// The item deleted.
    Deleted,
}

impl Bare {
    /// What the error says.
    pub fn message(&self) -> String {
        let Bare { name, value, .. } = self;
        let mut m = format!(
            "`with {name} = {value}` gives `{name}` no sentinel value: a boundary item is \
             written `initial {name} = {value}`, which gives the sentinel value, or with an \
             index, as `{name}[k] = {value}`. Without `initial`, `with {name} = {value}` reads \
             as though `{name}` took the value `{value}` anew on every step, while a boundary \
             item gives `{name}` one value, below its first step or index, once."
        );
        if let Some(Misplaced { before, push, .. }) = &self.misplaced {
            let what = if *push { "a push, which" } else { "code that" };
            m.push_str(&format!(
                " The item also follows `{before}`, {what} takes no boundary clause: a boundary \
                 clause follows only the value of a binding, as `{name}' = … with initial \
                 {name} = {value};`, or of an indexed definition, as `{name}[i in 0..<n] = … \
                 with initial {name} = {value};`."
            ));
        }
        m
    }
}

/// The message for a `..` written in a list with other items, as `(int, ..)`, `#a(int, ..)` or
/// `{x: int, ..}`: the kind-wide types hold `..` alone (DESIGN.md sec:type_language).
pub const DOTS: &str = "`..` stands alone between its brackets: `(..)` is every tuple, `{..}` \
                        every struct and `#a(..)` the atom `#a` with any payload, and no list \
                        with other items holds `..`";

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(c) = &self.case {
            return f.write_str(&c.message());
        }
        if let Some(b) = &self.bare {
            return f.write_str(&b.message());
        }
        match self.message {
            Some(m) => f.write_str(m),
            None => write!(f, "expected {}", self.expected.join(" or ")),
        }
    }
}

/// The index of the `..` that a parse failing at token `far` of `toks` stopped at or just
/// after, when it stands in a list with other items: after a `,` (`(int, ..)`), or alone after
/// an opening bracket and followed by more than the closing one (`(.., int)`). No rule takes a
/// `..` after a `,`, or after `(` or `{` but before a token other than the closing bracket.
fn dots_in_list(toks: &[(Kind, &str)], far: usize) -> Option<usize> {
    let text = |i: usize| toks.get(i).map(|t| t.1);
    if text(far) == Some("..") && far > 0 && text(far - 1) == Some(",") {
        return Some(far);
    }
    let d = far.checked_sub(1)?;
    let opened = d > 0 && matches!(text(d - 1), Some("(" | "{"));
    (text(d) == Some("..") && opened).then_some(d)
}

/// Parses `tokens`, lexed from `text`, as the rule `start` at `ring`, to the end of the tokens.
pub fn parse(text: &str, tokens: &[Token], start: &str, ring: u32) -> Result<Tree, Error> {
    let end = Span {
        start: text.len(),
        end: text.len(),
    };
    parse_to(grammar(), text, tokens, start, ring, end)
}

/// Parses as [`parse`] does, by the grammar `g`, which needs a rule `Expr` for a string's holes.
/// [`Tree::name`] and [`Tree::layer`] read [`grammar()`], so they do not apply to this tree; a
/// node's `rule` and `alt` index `g`.
pub fn parse_with(
    g: &Grammar,
    text: &str,
    tokens: &[Token],
    start: &str,
    ring: u32,
) -> Result<Tree, Error> {
    let end = Span {
        start: text.len(),
        end: text.len(),
    };
    parse_to(g, text, tokens, start, ring, end)
}

/// A tree whose holes are being parsed: those left, each with the span of its `}`.
struct Open<'t> {
    tree: Tree,
    holes: std::vec::IntoIter<(&'t [Token], Span)>,
}

/// Parses as `parse` does; `end` is the span reported for an error at the end of `tokens`.
/// Holes nest, so the open trees are on a stack. An error stops the parse at the first failure
/// in the order of the text, each tree before its holes.
fn parse_to(
    g: &Grammar,
    text: &str,
    tokens: &[Token],
    start: &str,
    ring: u32,
    end: Span,
) -> Result<Tree, Error> {
    let start = g.rule(start).unwrap_or_else(|| panic!("no rule {start}"));
    let mut stack = vec![parse_one(g, text, tokens, start, ring, end)?];
    let hole = g.rule("Expr");
    loop {
        let top = stack.last_mut().expect("the outermost tree returns");
        if let Some((tokens, close)) = top.holes.next() {
            let hole = hole.expect("the grammar has a rule `Expr` for a string's holes");
            stack.push(parse_one(g, text, tokens, hole, ring, close)?);
            continue;
        }
        let done = stack.pop().expect("the top was read above").tree;
        match stack.last_mut() {
            Some(parent) => parent.tree.holes.push(done),
            None => return Ok(done),
        }
    }
}

/// Parses `tokens` as rule `start`, its holes left for `parse_to`.
fn parse_one<'t>(
    g: &Grammar,
    text: &str,
    tokens: &'t [Token],
    start: usize,
    ring: u32,
    end: Span,
) -> Result<Open<'t>, Error> {
    let toks: Vec<(Kind, &str)> = tokens
        .iter()
        .map(|t| (kind(&t.tok), &text[t.span.start..t.span.end]))
        .chain([(Kind::End, "")])
        .collect();
    let span = |i: usize| tokens.get(i).map_or(end, |t| t.span);
    let mut p = Parser::new(g, ring, toks.as_slice());
    let matched = match p.rule_node(start, 0, false) {
        Some((e, node)) if e + 1 >= toks.len() => Some(node),
        Some((e, _)) => {
            p.fail(e, Expected::Name("END"));
            None
        }
        None => None,
    };
    let Some(root) = matched else {
        let mut expected: Vec<String> = p.expected().iter().map(shown).collect();
        expected.sort();
        let dots = dots_in_list(&toks, p.far);
        let case = case_item(g, ring, start, &toks, p.far)
            .map(|at| Box::new(in_case(text, tokens, &toks, end, at)));
        let found = case
            .is_none()
            .then(|| bare_item(g, ring, start, &toks, p.far));
        let bare = found.flatten().map(|(n, clause)| {
            let reaches =
                |fixed: &[(Kind, &str)], edit: usize| reaches(g, ring, start, fixed, edit);
            Box::new(bare(
                text,
                tokens,
                &toks,
                n,
                end,
                (!clause).then_some(&reaches),
            ))
        });
        return Err(Error {
            span: case
                .as_ref()
                .map_or_else(|| span(dots.unwrap_or(p.far)), |c| c.clause_span),
            expected,
            message: dots.map(|_| DOTS),
            bare,
            case,
        });
    };
    let mut holes = Vec::new();
    for t in tokens {
        if let Tok::Str(parts) = &t.tok {
            for part in parts {
                if let Part::Hole { tokens, span } = part {
                    let close = Span {
                        start: span.end - 1,
                        end: span.end,
                    };
                    holes.push((tokens.as_slice(), close));
                }
            }
        }
    }
    Ok(Open {
        tree: Tree {
            nodes: p.nodes,
            root,
            holes: Vec::new(),
        },
        holes: holes.into_iter(),
    })
}

fn kind(tok: &Tok) -> Kind {
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

/// How an error names what was expected.
fn shown(e: &Expected<'_>) -> String {
    match e {
        Expected::Lit(s) => format!("'{s}'"),
        Expected::Name(n) => (*n).into(),
        Expected::Class => unreachable!("a grammar over tokens holds no character class"),
    }
}

/// The index of the name of a boundary item written with neither `initial` nor an index, as
/// `with x = 0` or `, x = 0` in a boundary clause, at whose `=` a parse of `toks` as rule
/// `start` failed (token `far`), and whether a boundary clause may stand there: whether the
/// parse gets past that `=` once `initial` is written before the name. After `with`, the
/// shape `with x =` is a boundary item wherever it stands, since no other rule reads a name
/// and `=` after `with` (a facet is `with f(…)`, an update `with { … }`); so `p <- e with x = 0`
/// gives an item that may not stand there. After `,`, only a boundary clause that the parse
/// has entered makes the item one. The second parse runs only when the first has failed, at
/// the cost of one parse.
fn bare_item(
    g: &Grammar,
    ring: u32,
    start: usize,
    toks: &[(Kind, &str)],
    far: usize,
) -> Option<(usize, bool)> {
    let n = far.checked_sub(1).filter(|&n| n > 0)?;
    let shaped = toks.get(far).is_some_and(|t| t.1 == "=")
        && toks[n].0 == Kind::Ident
        && matches!(toks[n - 1].1, "with" | ",");
    if !shaped {
        return None;
    }
    let mut fixed = Vec::with_capacity(toks.len() + 1);
    fixed.extend_from_slice(&toks[..n]);
    fixed.push((Kind::Ident, "initial"));
    fixed.extend_from_slice(&toks[n..]);
    // The `=` is at `far + 1` in `fixed`.
    let clause = reaches(g, ring, start, &fixed, far + 1);
    (clause || toks[n - 1].1 == "with").then_some((n, clause))
}

/// Whether a parse of `toks` as rule `start` gets past token `edit`: succeeds, or fails only
/// after it.
fn reaches(g: &Grammar, ring: u32, start: usize, toks: &[(Kind, &str)], edit: usize) -> bool {
    let mut p = Parser::new(g, ring, toks);
    let reached = match p.rule_node(start, 0, false) {
        Some((e, _)) if e + 1 >= toks.len() => return true,
        Some((e, _)) => e.max(p.far),
        None => p.far,
    };
    reached > edit
}

/// What starts a boundary item.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ItemHead {
    /// `x =`, with neither `initial` nor an index.
    Bare,
    /// `initial x =`.
    Initial,
    /// `x[k] =`, one or more indices.
    Indexed,
}

/// The kind of boundary item that starts at token `i` of `toks`, and the token its value starts
/// at: `initial x =`, `x[k]… =` or `x =`. The scan over the brackets of an index stops at the
/// end of the tokens.
fn item_head(toks: &[(Kind, &str)], i: usize) -> Option<(ItemHead, usize)> {
    let at = |k: usize| toks.get(k).copied().unwrap_or((Kind::End, ""));
    if at(i).0 != Kind::Ident {
        return None;
    }
    match (at(i).1, at(i + 1), at(i + 2)) {
        ("initial", (Kind::Ident, _), (_, "=")) => Some((ItemHead::Initial, i + 3)),
        (_, (_, "="), _) => Some((ItemHead::Bare, i + 2)),
        (_, (_, "["), _) => {
            let mut k = i + 1;
            while at(k).1 == "[" {
                let mut d = 0;
                loop {
                    let t = at(k);
                    if t.0 == Kind::End {
                        return None;
                    }
                    d += depth(t.1);
                    k += 1;
                    if d == 0 {
                        break;
                    }
                }
            }
            (at(k).1 == "=").then_some((ItemHead::Indexed, k + 1))
        }
        _ => None,
    }
}

/// Where [`case_item`] found a boundary clause in a test case, by token index.
struct CaseAt {
    /// The `{` after `test`.
    open: usize,
    /// The case's first token.
    first: usize,
    /// The `with`.
    w: usize,
    /// Each item: its first token, what starts it, and the token its value starts at and the
    /// one after its value.
    items: Vec<(usize, ItemHead, usize, usize)>,
    /// The token after the clause.
    cut: usize,
    /// The `,` or `}` that ends the case.
    stop: usize,
    /// The case's `->`, when the case has one.
    arrow: Option<usize>,
    /// The first token of the code before `with`: the case's first, or the token after `->`.
    before: usize,
    /// The first token of the function or method the table follows, and whether it is a
    /// method, when the unit parses with the clause deleted.
    function: Option<(usize, bool)>,
    /// Whether the unit parses past the case with the clause deleted.
    deleted: bool,
    /// Whether the clause is offered as an update of fields, `with { x = 0 }`.
    update: bool,
}

/// The boundary clause in a test case at whose first item a parse of `toks` as rule `start`
/// failed (token `far`): `with` two tokens before `far`, a boundary item after it, and the `{`
/// of `test {` as the bracket around it. No rule reads a boundary item after an expression, so
/// `with x =`, `with initial x =` and `with x[k] =` each fail one token after the item's first
/// word, where a facet `with f(…)` wants its `(`. Each item's value is matched as an `Expr12`,
/// the rule of a side of a test case (`TestCase = Expr12 '->' Expr12`), so the case's `->`
/// ends it as it ends the left side.
///
/// Cost, on the error path only: a scan back to the table's `{` and forward to the case's end;
/// one packrat parser for the values and the case's left side, linear in what it reads; at
/// most two parses of the unit with the clause rewritten; and one walk down the tree from the
/// root to the case. Linear in the unit.
fn case_item(
    g: &Grammar,
    ring: u32,
    start: usize,
    toks: &[(Kind, &str)],
    far: usize,
) -> Option<CaseAt> {
    // Complexity tradeoff: the naive way reparses each case of the table on its own as a
    // `TestCase` to find the one that fails, O(cases × unit); here the case is cut out by one
    // scan back from `with` and one forward at bracket depth 0, O(unit), and only its values and
    // left side are parsed.
    let w = far.checked_sub(2)?;
    if toks[w] != (Kind::Keyword, "with") {
        return None;
    }
    item_head(toks, w + 1)?;
    // Back to the bracket around the case; the case starts after the nearest `,` at its depth.
    let mut open = w;
    let mut first = None;
    let mut d = 0;
    while open > 0 {
        let t = toks[open - 1].1;
        if d - depth(t) < 0 {
            break;
        }
        if d == 0 && t == "," && first.is_none() {
            first = Some(open);
        }
        d -= depth(t);
        open -= 1;
    }
    if open < 2 || toks[open - 1].1 != "{" || toks[open - 2] != (Kind::Keyword, "test") {
        return None;
    }
    let open = open - 1;
    let first = first.unwrap_or(open + 1);
    let e12 = g.rule("Expr12")?;
    let mut p = Parser::new(g, ring, toks);
    let mut items = Vec::new();
    let mut i = w + 1;
    while let Some((h, v)) = item_head(toks, i) {
        let (e, _) = p.rule_node(e12, v, false)?;
        items.push((i, h, v, e));
        if toks[e].1 != "," {
            break;
        }
        i = e + 1;
    }
    let cut = items.last()?.3;
    // Forward to the `,` or `}` that ends the case.
    let mut stop = cut;
    let mut d = 0;
    while toks[stop].0 != Kind::End
        && !(d == 0 && toks[stop].1 == ",")
        && d + depth(toks[stop].1) >= 0
    {
        d += depth(toks[stop].1);
        stop += 1;
    }
    let (l, _) = p.rule_node(e12, first, false)?;
    let arrow = if l == w {
        (toks[cut].1 == "->").then_some(cut)
    } else {
        (l < w && toks[l].1 == "->").then_some(l)
    };
    let before = arrow.filter(|&a| a < w).map_or(first, |a| a + 1);
    // The clause deleted: the menu's first repair, and the tree the function's name is read
    // from.
    let mut fixed = toks[..w].to_vec();
    fixed.extend_from_slice(&toks[cut..]);
    let mut q = Parser::new(g, ring, fixed.as_slice());
    let (deleted, function) = match q.rule_node(start, 0, false) {
        Some((e, root)) if e + 1 >= fixed.len() => (true, enclosing(&q.nodes, root, w)),
        Some((e, _)) => (e.max(q.far) > w, None),
        None => (q.far > w, None),
    };
    // The clause as an update of fields: only items `x = e`, after code that can be a struct.
    let literal = matches!(
        &toks[before..w],
        [(
            Kind::Int | Kind::Float | Kind::Rat | Kind::Str | Kind::Atom,
            _
        )] | [(_, "-"), (Kind::Int | Kind::Float | Kind::Rat, _)]
            | [(Kind::Keyword, "true" | "false")]
    );
    let update = !literal && items.iter().all(|it| it.1 == ItemHead::Bare) && {
        let mut fixed = toks[..=w].to_vec();
        fixed.push((toks[open].0, "{"));
        fixed.extend_from_slice(&toks[w + 1..cut]);
        fixed.push((toks[open].0, "}"));
        fixed.extend_from_slice(&toks[cut..]);
        reaches(g, ring, start, &fixed, cut + 1)
    };
    Some(CaseAt {
        open,
        first,
        w,
        items,
        cut,
        stop,
        arrow,
        before,
        function,
        deleted,
        update,
    })
}

/// The first token of the innermost `Function` or `Method` node of the tree under `root` whose
/// span holds token `at`, and whether it is a method. One walk from the root down the nodes
/// that hold `at`, each step a scan of one node's kids: linear in the tree.
fn enclosing(nodes: &[Node], root: usize, at: usize) -> Option<(usize, bool)> {
    let g = grammar();
    let mut n = root;
    let mut found = None;
    loop {
        let node = &nodes[n];
        match g.rules[node.rule].name.as_str() {
            "Function" => found = Some((node.start, false)),
            "Method" => found = Some((node.start, true)),
            _ => {}
        }
        let holds = |&&k: &&usize| nodes[k].start <= at && at < nodes[k].end;
        match node.kids.iter().find(holds) {
            Some(&k) => n = k,
            None => return found,
        }
    }
}

/// The [`InCase`] the clause `at` found by [`case_item`] makes, from `text` lexed as `tokens`;
/// `end` is the span of the end of the tokens.
fn in_case(text: &str, tokens: &[Token], toks: &[(Kind, &str)], end: Span, at: CaseAt) -> InCase {
    let span = |i: usize| tokens.get(i).map_or(end, |t| t.span);
    // The text of tokens `a` to `b`, `b` not included; empty when there are none.
    let sl = |a: usize, b: usize| {
        if b > a {
            &text[span(a).start..span(b - 1).end]
        } else {
            ""
        }
    };
    let glue = |a: &str, b: &str| match (a.is_empty(), b.is_empty()) {
        (_, true) => a.to_string(),
        (true, _) => b.to_string(),
        _ => format!("{a} {b}"),
    };
    let CaseAt {
        open,
        first,
        w,
        ref items,
        cut,
        stop,
        arrow,
        before,
        function,
        deleted,
        update,
    } = at;
    let (i0, h0, v0, e0) = items[0];
    let rest = sl(cut, stop);
    let sides = arrow.and_then(|a| {
        let sides = if a == cut {
            (sl(first, w).to_string(), sl(a + 1, stop).to_string())
        } else {
            (sl(first, a).to_string(), glue(sl(a + 1, w), rest))
        };
        (!sides.0.is_empty() && !sides.1.is_empty()).then_some(sides)
    });
    let function = function.map(|(f, method)| match method {
        true => format!("{}.{}", toks[f].1, toks[f + 2].1),
        false => toks[f].1.to_string(),
    });
    InCase {
        function,
        case: sl(first, stop).to_string(),
        case_span: Span {
            start: span(first).start,
            end: span(stop - 1).end,
        },
        table: Span {
            start: span(open - 1).start,
            end: span(open).end,
        },
        clause: sl(w, cut).to_string(),
        clause_span: Span {
            start: span(w).start,
            end: span(cut - 1).end,
        },
        before: sl(before, w).to_string(),
        head: sl(i0, v0).to_string(),
        name: toks[i0 + usize::from(h0 == ItemHead::Initial)]
            .1
            .to_string(),
        item: sl(i0, e0).to_string(),
        value: sl(v0, e0).to_string(),
        bare: items
            .iter()
            .find(|it| it.1 == ItemHead::Bare)
            .map(|&(i, _, v, e)| (toks[i].1.to_string(), sl(v, e).to_string())),
        sides,
        left: arrow == Some(cut),
        deleted: deleted.then(|| glue(sl(first, w), rest)),
        update: update.then(|| {
            glue(
                &format!("{} {{ {} }}", sl(first, w + 1), sl(w + 1, cut)),
                rest,
            )
        }),
    }
}

/// Checks that a rewritten token sequence parses past its last edit, for [`bare`].
type Reaches<'a> = &'a dyn Fn(&[(Kind, &str)], usize) -> bool;

/// How the bracket depth changes at a token: up at an opening bracket, down at a closing one.
fn depth(t: &str) -> i32 {
    match t {
        "(" | "[" | "{" => 1,
        ")" | "]" | "}" => -1,
        _ => 0,
    }
}

/// The [`Bare`] item whose name is token `n` of `toks`, lexed from `text` as `tokens`; `end` is
/// the span of the end of the tokens. The value runs from the `=` to the next `,` or `;` at its
/// own bracket depth; the statement from the token after the `;` or unmatched opening bracket
/// before the item to the `;` after it. Each scan stops at the statement's ends, so the cost is
/// the statement's length. When `misplaced` is given, the item stands where no boundary clause
/// can, and [`misplaced_item`] finds its repairs.
fn bare(
    text: &str,
    tokens: &[Token],
    toks: &[(Kind, &str)],
    n: usize,
    end: Span,
    misplaced: Option<Reaches<'_>>,
) -> Bare {
    let span = |i: usize| tokens.get(i).map_or(end, |t| t.span);
    let mut d = 0;
    let mut last = n + 2;
    while last < tokens.len() {
        let t = toks[last].1;
        if d == 0 && matches!(t, "," | ";") || d + depth(t) < 0 {
            break;
        }
        d += depth(t);
        last += 1;
    }
    let value = if last > n + 2 {
        text[span(n + 2).start..span(last - 1).end].to_string()
    } else {
        "…".to_string()
    };
    let mut stop = last;
    let mut d = 0;
    while stop < tokens.len() && !(d == 0 && toks[stop].1 == ";") && d + depth(toks[stop].1) >= 0 {
        d += depth(toks[stop].1);
        stop += 1;
    }
    let close = if stop < tokens.len() && toks[stop].1 == ";" {
        stop
    } else {
        stop.saturating_sub(1)
    };
    let mut first = n;
    let mut d = 0;
    while first > 0 {
        let t = toks[first - 1].1;
        if d == 0 && t == ";" || d - depth(t) < 0 {
            break;
        }
        d -= depth(t);
        first -= 1;
    }
    let misplaced = misplaced.map(|reaches| {
        let at = Stmt {
            n,
            first,
            close,
            stop,
            last,
        };
        misplaced_item(text, tokens, toks, end, at, &value, reaches)
    });
    Bare {
        name: toks[n].1.to_string(),
        value,
        item: Span {
            start: span(n).start,
            end: span(last.max(n + 3) - 1).end,
        },
        stmt: Span {
            start: span(first).start,
            end: span(close).end,
        },
        below: below(&toks[first..n], toks[n].1),
        misplaced,
    }
}

/// Where [`bare`] found the item: its name (token `n`), its statement's first token, its last
/// (the `;` where there is one), the `;` or unmatched closing bracket that ends it (`stop`),
/// and the token after the item's value (`last`).
struct Stmt {
    n: usize,
    first: usize,
    close: usize,
    stop: usize,
    last: usize,
}

/// The [`Misplaced`] part of the item `at`, with the text `value`. Each repair is the token
/// sequence rewritten and parsed once more, and is offered only when that parse gets past the
/// rewritten statement: so the menu never offers code that does not parse, such as `with
/// initial x = 0` on a push. A repair that gives the variable its sentinel value is offered
/// only when no other statement of the block gives one, since a second would be refused. Three
/// repairs are tried, a constant number of parses, and [`defining`] scans the enclosing block
/// once: linear in the unit, on the error path only.
fn misplaced_item(
    text: &str,
    tokens: &[Token],
    toks: &[(Kind, &str)],
    end: Span,
    at: Stmt,
    value: &str,
    reaches: Reaches<'_>,
) -> Misplaced {
    let span = |i: usize| tokens.get(i).map_or(end, |t| t.span);
    let Stmt {
        n,
        first,
        close,
        stop,
        last,
    } = at;
    let name = toks[n].1;
    let w = n - 1;
    // The clause runs from `with` to the end of the item's value, or of the items after it.
    let cut = if toks.get(last).is_some_and(|t| t.1 == ",") {
        stop
    } else {
        last
    };
    let mut d = 0;
    let mut push = false;
    for t in &toks[first..w] {
        push |= d == 0 && t.1 == "<-";
        d += depth(t.1);
    }
    let head = &text[span(first).start..span(w - 1).end];
    let tail = if cut <= close && close < tokens.len() {
        &text[span(cut).start..span(close).end]
    } else {
        ""
    };
    let here = format!("{head}{tail}");
    let stmt = Span {
        start: span(first).start,
        end: span(close).end,
    };
    let semi = close < tokens.len() && toks[close].1 == ";";
    let mut repairs = Vec::new();
    let (defined, given) = defining(toks, first, stop, name);
    // `x' <- e with x = v;` as the binding `x' = e with initial x = v;`.
    let primed = toks[first].0 == Kind::Ident && toks[first].1.ends_with('\'');
    if semi && primed && !given && toks[first + 1].1 == "<-" {
        let mut fixed = toks.to_vec();
        fixed[first + 1] = toks[n + 1];
        fixed.insert(n, (Kind::Ident, "initial"));
        if reaches(&fixed, close + 1) {
            repairs.push(Repair {
                span: stmt,
                text: format!(
                    "{}={}initial {}",
                    &text[span(first).start..span(first + 1).start],
                    &text[span(first + 1).end..span(n).start],
                    &text[span(n).start..span(close).end],
                ),
                fix: Fix::Binding,
            });
        }
    }
    // The item moved to the first binding of the enclosing block that defines the variable,
    // when it is the only item of its clause: the other items would be lost.
    let alone = cut == last;
    if let Some((s, e)) = defined.filter(|_| alone && !given) {
        let item = [toks[w], (Kind::Ident, "initial")]
            .into_iter()
            .chain(toks[n..last].iter().copied());
        let mut fixed: Vec<(Kind, &str)> = Vec::with_capacity(toks.len() + 1);
        let edit = if e < w {
            fixed.extend_from_slice(&toks[..e]);
            fixed.extend(item);
            fixed.extend_from_slice(&toks[e..w]);
            let edit = fixed.len();
            fixed.extend_from_slice(&toks[cut..]);
            edit
        } else {
            fixed.extend_from_slice(&toks[..w]);
            fixed.extend_from_slice(&toks[cut..e]);
            fixed.extend(item);
            let edit = fixed.len();
            fixed.extend_from_slice(&toks[e..]);
            edit
        };
        if reaches(&fixed, edit) {
            repairs.push(Repair {
                span: Span {
                    start: span(s).start,
                    end: span(e).end,
                },
                text: format!(
                    "{} with initial {name} = {value};",
                    &text[span(s).start..span(e - 1).end]
                ),
                fix: Fix::Moved { here: here.clone() },
            });
        }
    }
    // The item deleted: the repair underlines the clause.
    let mut fixed = toks[..w].to_vec();
    fixed.extend_from_slice(&toks[cut..]);
    if reaches(&fixed, w) {
        repairs.push(Repair {
            span: Span {
                start: span(w).start,
                end: span(cut - 1).end,
            },
            text: here,
            fix: Fix::Deleted,
        });
    }
    Misplaced {
        before: head.to_string(),
        push,
        repairs,
    }
}

/// The first and last tokens (its `;`) of the first statement, other than the one at `first`,
/// in the block around it, that defines `name` as a binding with no `with` clause:
/// `name' = …;` or `mutable name = …;`, either after `local`; and whether a statement of the
/// block other than the one at `first` gives `name` its sentinel value, `with … initial name =`.
/// The block runs from the opening brace before token `first` (or the start of the unit) to the
/// closing one after token `stop`; inside parentheses or brackets there is no such statement.
/// One scan of the block.
fn defining(
    toks: &[(Kind, &str)],
    first: usize,
    stop: usize,
    name: &str,
) -> (Option<(usize, usize)>, bool) {
    let mut open = first;
    let mut d = 0;
    while open > 0 {
        let t = toks[open - 1].1;
        if d - depth(t) < 0 {
            break;
        }
        d -= depth(t);
        open -= 1;
    }
    if open > 0 && toks[open - 1].1 != "{" {
        return (None, false);
    }
    let mut shut = stop;
    let mut d = 0;
    while shut < toks.len() && toks[shut].0 != Kind::End && d + depth(toks[shut].1) >= 0 {
        d += depth(toks[shut].1);
        shut += 1;
    }
    let primed = format!("{name}'");
    let (mut defined, mut given) = (None, false);
    let mut s = open;
    while s < shut {
        let mut e = s;
        let mut d = 0;
        let mut with = false;
        while e < shut && !(d == 0 && toks[e].1 == ";") {
            let t = toks[e].1;
            given |= s != first
                && with
                && d == 0
                && t == "initial"
                && toks.get(e + 1).is_some_and(|u| u.1 == name)
                && toks.get(e + 2).is_some_and(|u| u.1 == "=");
            with |= d == 0 && t == "with";
            d += depth(t);
            e += 1;
        }
        if e == shut {
            break;
        }
        let mut k = s + usize::from(toks[s].1 == "local");
        let mutable = toks[k].1 == "mutable";
        k += usize::from(mutable);
        let target = if mutable { name } else { primed.as_str() };
        let defines =
            k < e && toks[k].0 == Kind::Ident && toks[k].1 == target && toks[k + 1].1 == "=";
        if defined.is_none() && s != first && defines && !with {
            defined = Some((s, e));
        }
        s = e + 1;
    }
    (defined, given)
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
