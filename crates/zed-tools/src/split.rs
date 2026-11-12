//! `split SPEC_DIR [FILE…]` cuts each program into segments of whole items by one scan over its
//! tokens, parses each segment alone, and checks that the items are those of the whole-file
//! parse (plan row ZPARSE-par, `docs/zparse-par-study.md`). With no files named, the programs are
//! the fences of the spec's `DESIGN.md` and `EXAMPLES.md` and every `.zed` file under this
//! repository's `zed/`.
//!
//! The scan keeps a bracket depth. A position between two tokens at depth 0 is a cut when no
//! string of `Item` holds that pair of tokens next to each other at depth 0 ([`Splitter`]). The
//! set of such pairs is computed from the grammar, read as a grammar without order or lookahead:
//! ordered choice is choice, and a lookahead `&e` or `!e` is a branch that reads `e` and ends.
//! That reading only adds strings, so a pair it lacks is in no item, and a cut is always an item
//! boundary of the whole-file parse.
//!
//! A segment is parsed over its own tokens with no `END` after them, so that every test at its
//! end fails. In the whole file every test at a cut fails as well: a test that read the token
//! after the cut would put the pair across the cut into some string of `Item` at depth 0, and an
//! `END` test fails there since the file goes on. So each item's parse reads the same results in
//! both, and the segments give the whole-file items, node for node. When the file has no parse,
//! the failure is merged from the segments up to the first one that fails ([`split_parse`]).

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Write as _;

use zedc::parse::{Expr, Grammar, Kind, Parser, TOP};

use crate::spec::{Spec, zed_fences};
use crate::syntax::lex;
use crate::text::read_text;
use crate::{Outcome, arg, impl_root, say};

/// The number of token kinds, the variants of [`Kind`].
const KINDS: usize = 11;

/// A set of small numbers, as bits.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Bits(Vec<u64>);

impl Bits {
    /// The empty set of numbers below `n`.
    pub(crate) fn new(n: usize) -> Bits {
        Bits(vec![0; n.div_ceil(64)])
    }

    pub(crate) fn insert(&mut self, i: usize) {
        self.0[i / 64] |= 1 << (i % 64);
    }

    pub(crate) fn has(&self, i: usize) -> bool {
        self.0[i / 64] & (1 << (i % 64)) != 0
    }

    /// Adds `other`'s numbers.
    pub(crate) fn union(&mut self, other: &Bits) {
        for (a, b) in self.0.iter_mut().zip(&other.0) {
            *a |= b;
        }
    }

    /// Adds `other`'s numbers, and says whether any was new.
    pub(crate) fn add(&mut self, other: &Bits) -> bool {
        let mut grew = false;
        for (a, b) in self.0.iter_mut().zip(&other.0) {
            grew |= b & !*a != 0;
            *a |= b;
        }
        grew
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.0.iter().enumerate().flat_map(|(w, &bits)| {
            (0..64)
                .filter(move |b| bits & (1 << b) != 0)
                .map(move |b| w * 64 + b)
        })
    }
}

/// What the scan needs to know of an expression, read without order or lookahead.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Sum {
    /// Whether it can match no tokens.
    nullable: bool,
    /// The terminals its first test can read at its start.
    first: Bits,
    /// The terminals it can end with, at depth 0 after them.
    last: Bits,
    /// Whether some match leaves a bracket open: only a lookahead may.
    opens: bool,
    /// Whether some match ends by closing a bracket opened before it: only a lookahead may.
    closes: bool,
}

impl Sum {
    fn empty(n: usize) -> Sum {
        Sum {
            nullable: true,
            first: Bits::new(n),
            last: Bits::new(n),
            opens: false,
            closes: false,
        }
    }

    fn never(n: usize) -> Sum {
        Sum {
            nullable: false,
            ..Sum::empty(n)
        }
    }
}

/// What a walk over an expression records besides its [`Sum`].
struct Out<'a> {
    /// The rule being walked, for messages.
    rule: &'a str,
    /// The pairs at depth 0, by first terminal, when they are collected.
    pairs: Option<&'a mut Vec<Bits>>,
    /// The rules called at depth 0.
    at0: Vec<usize>,
    /// The rules called anywhere.
    all: Vec<usize>,
    /// The constructs the scan cannot read soundly, when they are collected.
    problems: Option<&'a mut BTreeSet<String>>,
}

impl Out<'_> {
    fn problem(&mut self, what: &str) {
        if let Some(p) = self.problems.as_deref_mut() {
            p.insert(format!("rule {}: {what}", self.rule));
        }
    }
}

/// The open and close bracket a literal is, by bracket: 0 `()`, 1 `[]`, 2 `{}`.
fn bracket(text: &str) -> Option<(bool, usize)> {
    match text {
        "(" => Some((true, 0)),
        "[" => Some((true, 1)),
        "{" => Some((true, 2)),
        ")" => Some((false, 0)),
        "]" => Some((false, 1)),
        "}" => Some((false, 2)),
        _ => None,
    }
}

/// The grammar read for the scan: its terminals and the summary of each rule.
struct Reading<'g> {
    g: &'g Grammar,
    /// Each literal's terminal number.
    lits: HashMap<&'g str, usize>,
    /// Each kind's terminal number, if the grammar names it.
    kinds: [Option<usize>; KINDS],
    /// How many terminals there are.
    n: usize,
    /// Each rule's summary.
    rules: Vec<Sum>,
}

impl<'g> Reading<'g> {
    fn new(g: &'g Grammar) -> Reading<'g> {
        let mut r = Reading {
            g,
            lits: HashMap::new(),
            kinds: [None; KINDS],
            n: 0,
            rules: Vec::new(),
        };
        let mut stack: Vec<&Expr> = g
            .rules
            .iter()
            .flat_map(|x| &x.alts)
            .map(|a| &a.expr)
            .collect();
        while let Some(e) = stack.pop() {
            match e {
                Expr::Lit(s) if !r.lits.contains_key(s.as_str()) => {
                    r.lits.insert(s, r.n);
                    r.n += 1;
                }
                Expr::Kind(k) if r.kinds[*k as usize].is_none() => {
                    r.kinds[*k as usize] = Some(r.n);
                    r.n += 1;
                }
                _ => stack.extend(inner(e)),
            }
        }
        r.rules = vec![Sum::never(r.n); g.rules.len()];
        r
    }

    /// The summary of one terminal.
    fn token(&self, t: usize) -> Sum {
        let mut s = Sum::never(self.n);
        s.first.insert(t);
        s.last.insert(t);
        s
    }

    /// `a` then `b`, recording the pairs between them when `at0`.
    fn then(&self, a: Sum, b: &Sum, out: &mut Out, at0: bool) -> Sum {
        if a.closes {
            out.problem("a match goes on after closing a bracket opened before it");
        }
        if at0 && let Some(pairs) = out.pairs.as_deref_mut() {
            for x in a.last.iter() {
                pairs[x].union(&b.first);
            }
        }
        let mut first = a.first;
        if a.nullable {
            first.union(&b.first);
        }
        let mut last = b.last.clone();
        if b.nullable {
            last.union(&a.last);
        }
        Sum {
            nullable: a.nullable && b.nullable,
            first,
            last,
            opens: a.opens || b.opens,
            closes: b.closes,
        }
    }

    /// `s` repeated, at least once unless `star`.
    fn repeat(&self, s: Sum, star: bool, out: &mut Out, at0: bool) -> Sum {
        if s.opens || s.closes {
            out.problem("a repetition leaves a bracket open or closes one opened before it");
        }
        let r = self.then(s.clone(), &s, out, at0);
        Sum {
            nullable: star || s.nullable,
            first: s.first,
            last: s.last,
            opens: r.opens,
            closes: false,
        }
    }

    /// The summary of `e`, recording into `out`; `at0` says whether `e` is at depth 0 in the
    /// rule.
    fn walk(&self, e: &Expr, out: &mut Out, at0: bool) -> Sum {
        let n = self.n;
        match e {
            Expr::Lit(s) => {
                let mut sum = self.token(self.lits[s.as_str()]);
                match bracket(s) {
                    // A bracket alone, outside a sequence that closes it.
                    Some((true, _)) => {
                        sum.last = Bits::new(n);
                        sum.opens = true;
                    }
                    Some((false, _)) => {
                        // A test of a closing bracket at depth 0 never succeeds in a file whose
                        // brackets balance, so it reads no pair.
                        sum = Sum::never(n);
                        sum.closes = true;
                    }
                    None => {}
                }
                sum
            }
            Expr::Kind(k) => self.token(self.kinds[*k as usize].expect("collected")),
            Expr::Rule(r) => {
                out.all.push(*r);
                if at0 {
                    out.at0.push(*r);
                }
                self.rules[*r].clone()
            }
            Expr::Head => Sum::empty(n),
            Expr::Seq(items) => self.seq(items, out, at0),
            Expr::Choice(alts) => self.choice(alts.iter(), out, at0),
            Expr::Star(x) => {
                let s = self.walk(x, out, at0);
                self.repeat(s, true, out, at0)
            }
            Expr::Plus(x) => {
                let s = self.walk(x, out, at0);
                self.repeat(s, false, out, at0)
            }
            Expr::Sep(pair) => {
                let [sep, x] = &**pair;
                let item = self.walk(x, out, at0);
                let sep = self.walk(sep, out, at0);
                let unit = self.then(sep, &item, out, at0);
                let more = self.repeat(unit, true, out, at0);
                self.then(item, &more, out, at0)
            }
            Expr::Opt(x) => {
                let mut s = self.walk(x, out, at0);
                s.nullable = true;
                s
            }
            Expr::And(x) | Expr::Not(x) => {
                // A lookahead reads `x` from here and goes no further: its first tests follow
                // what came before, and nothing follows its end.
                let s = self.walk(x, out, at0);
                Sum {
                    first: s.first,
                    ..Sum::empty(n)
                }
            }
            Expr::SetHead(x) | Expr::ClearHead(x) => self.walk(x, out, at0),
            Expr::Class(_) | Expr::Any | Expr::XidStart | Expr::XidContinue => {
                out.problem("a character class in a grammar over tokens");
                Sum::never(n)
            }
            Expr::Undefined(name) => {
                out.problem(&format!("the undefined name {name}"));
                Sum::never(n)
            }
        }
    }

    /// A sequence: a bracket literal and the literal that closes it in the same sequence are
    /// one group, whose inside is deeper than depth 0.
    fn seq(&self, items: &[Expr], out: &mut Out, at0: bool) -> Sum {
        let mut acc = Sum::empty(self.n);
        let mut open: Vec<usize> = Vec::new();
        for x in items {
            if let Expr::Lit(s) = x
                && let Some((opening, b)) = bracket(s)
            {
                let t = self.lits[s.as_str()];
                if opening {
                    if open.is_empty() {
                        acc = self.then(acc, &self.token(t), out, at0);
                    }
                    open.push(b);
                } else {
                    match open.pop() {
                        Some(o) if o == b => {
                            if open.is_empty() {
                                acc.last = Bits::new(self.n);
                                acc.last.insert(t);
                            }
                        }
                        Some(_) => out.problem(&format!("the bracket {s} closes another kind")),
                        None => {
                            let close = self.walk(x, out, at0);
                            acc = self.then(acc, &close, out, at0);
                        }
                    }
                }
                continue;
            }
            if open.is_empty() {
                let s = self.walk(x, out, at0);
                acc = self.then(acc, &s, out, at0);
            } else {
                let s = self.walk(x, out, false);
                if s.opens || s.closes {
                    out.problem("inside brackets, a match leaves a bracket open or closes one");
                }
            }
        }
        if !open.is_empty() {
            acc.opens = true;
            acc.last = Bits::new(self.n);
        }
        acc
    }

    /// The summary of rule `r` from the current summaries.
    fn rule_sum(&self, r: usize, out: &mut Out) -> Sum {
        self.choice(self.g.rules[r].alts.iter().map(|a| &a.expr), out, true)
    }

    /// A choice among `alts`, read as any of them.
    fn choice<'e>(&self, alts: impl Iterator<Item = &'e Expr>, out: &mut Out, at0: bool) -> Sum {
        let mut sum = Sum::never(self.n);
        for a in alts {
            let s = self.walk(a, out, at0);
            sum.nullable |= s.nullable;
            sum.first.union(&s.first);
            sum.last.union(&s.last);
            sum.opens |= s.opens;
            sum.closes |= s.closes;
        }
        sum
    }
}

/// The operands of `e`.
fn inner(e: &Expr) -> Vec<&Expr> {
    match e {
        Expr::Seq(xs) | Expr::Choice(xs) => xs.iter().collect(),
        Expr::Sep(pair) => pair.iter().collect(),
        Expr::Star(x)
        | Expr::Plus(x)
        | Expr::Opt(x)
        | Expr::And(x)
        | Expr::Not(x)
        | Expr::SetHead(x)
        | Expr::ClearHead(x) => vec![x],
        _ => Vec::new(),
    }
}

/// The scan of one grammar: which pairs of terminals some string of the item rule holds next to
/// each other at depth 0.
pub struct Splitter {
    /// Each literal's terminal number.
    lits: HashMap<String, usize>,
    /// Each kind's terminal number.
    kinds: [Option<usize>; KINDS],
    /// For each terminal, the terminals that follow it at depth 0 in some item.
    follow: Vec<Bits>,
    /// How many terminals there are.
    pub terminals: usize,
    /// How many pairs there are.
    pub pairs: usize,
}

impl Splitter {
    /// The scan for items of rule `item` of `g` at the full ring, which holds every lower ring's
    /// items. The error lists each construct the scan cannot read soundly: brackets that do
    /// not balance in a match of `item`, a repetition of an unbalanced match, a match that goes
    /// on after closing a bracket opened before it, and an item rule that matches no tokens.
    pub fn new(g: &Grammar, item: &str) -> Result<Splitter, String> {
        let item = g
            .rule(item)
            .ok_or_else(|| format!("the grammar has no rule {item}"))?;
        let mut r = Reading::new(g);
        // The least summaries, by a work list: a rule is walked again when a rule it calls
        // changes. Each change adds to a set over the terminals, so each rule changes at most
        // 2T + 3 times for T terminals.
        let mut callers: Vec<Vec<usize>> = vec![Vec::new(); g.rules.len()];
        for (i, rule) in g.rules.iter().enumerate() {
            let mut out = Out {
                rule: &rule.name,
                pairs: None,
                at0: Vec::new(),
                all: Vec::new(),
                problems: None,
            };
            r.rule_sum(i, &mut out);
            for c in out.all {
                callers[c].push(i);
            }
        }
        let mut queued = vec![true; g.rules.len()];
        let mut work: Vec<usize> = (0..g.rules.len()).collect();
        while let Some(i) = work.pop() {
            queued[i] = false;
            let mut out = Out {
                rule: &g.rules[i].name,
                pairs: None,
                at0: Vec::new(),
                all: Vec::new(),
                problems: None,
            };
            let s = r.rule_sum(i, &mut out);
            if s != r.rules[i] {
                r.rules[i] = s;
                for &c in &callers[i] {
                    if !queued[c] {
                        queued[c] = true;
                        work.push(c);
                    }
                }
            }
        }
        // The pairs of the rules called at depth 0 from the item rule, each once; the problems
        // of every rule it calls.
        let mut follow = vec![Bits::new(r.n); r.n];
        let mut problems = BTreeSet::new();
        let mut seen = vec![false; g.rules.len()];
        let mut at0 = vec![false; g.rules.len()];
        seen[item] = true;
        at0[item] = true;
        let mut stack = vec![item];
        while let Some(i) = stack.pop() {
            let mut out = Out {
                rule: &g.rules[i].name,
                pairs: at0[i].then_some(&mut follow),
                at0: Vec::new(),
                all: Vec::new(),
                problems: Some(&mut problems),
            };
            r.rule_sum(i, &mut out);
            let (calls0, calls) = (out.at0, out.all);
            for c in calls0 {
                if !at0[c] {
                    at0[c] = true;
                    // Walked again to collect its pairs, if it was walked without them.
                    seen[c] = true;
                    stack.push(c);
                }
            }
            for c in calls {
                if !seen[c] {
                    seen[c] = true;
                    stack.push(c);
                }
            }
        }
        let s = &r.rules[item];
        if s.opens || s.closes {
            problems.insert(format!(
                "rule {}: some match leaves a bracket open or closes one opened before it",
                g.rules[item].name
            ));
        }
        if s.nullable {
            problems.insert(format!(
                "rule {}: it can match no tokens",
                g.rules[item].name
            ));
        }
        if !problems.is_empty() {
            return Err(problems.into_iter().collect::<Vec<_>>().join("\n"));
        }
        let pairs = follow.iter().map(|f| f.iter().count()).sum();
        Ok(Splitter {
            lits: r.lits.iter().map(|(s, &t)| ((*s).to_string(), t)).collect(),
            kinds: r.kinds,
            follow,
            terminals: r.n,
            pairs,
        })
    }

    /// The terminals a token of kind `k` and text `text` matches: its kind and its text.
    fn terms(&self, k: Kind, text: &str) -> [Option<usize>; 2] {
        let lit = match k {
            Kind::Keyword | Kind::Op | Kind::Ident => self.lits.get(text).copied(),
            _ => None,
        };
        [self.kinds[k as usize], lit]
    }

    /// Whether some item holds a token like `a` then one like `b` at depth 0.
    fn joined(&self, a: [Option<usize>; 2], b: [Option<usize>; 2]) -> bool {
        a.iter()
            .flatten()
            .any(|&x| b.iter().flatten().any(|&y| self.follow[x].has(y)))
    }

    /// The cuts of `toks`, a program's tokens without `END`: the positions where a segment
    /// starts, 0 first. `None` when its brackets do not balance, which no item list does.
    pub fn cuts(&self, toks: &[(Kind, &str)]) -> Option<Vec<usize>> {
        let mut cuts = vec![0];
        let mut depth = 0usize;
        let mut prev: Option<[Option<usize>; 2]> = None;
        for (i, &(k, text)) in toks.iter().enumerate() {
            let here = self.terms(k, text);
            if depth == 0
                && let Some(p) = prev
                && !self.joined(p, here)
            {
                cuts.push(i);
            }
            if k == Kind::Op {
                match bracket(text) {
                    Some((true, _)) => depth += 1,
                    Some((false, _)) => depth = depth.checked_sub(1)?,
                    None => {}
                }
            }
            prev = Some(here);
        }
        (depth == 0).then_some(cuts)
    }
}

/// One node of a parse in preorder: rule, alternative, start, end, number of children, and the
/// branch each inner choice took.
type Shape = (usize, usize, usize, usize, usize, Vec<(u32, u32)>);

/// The result of a parse, comparable between the whole-file and the split parse.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Parsed {
    /// The items, each as its nodes in preorder, positions counted in the whole file.
    Items(Vec<Vec<Shape>>),
    /// No parse: the farthest position a test failed at, and what was expected there.
    Failed(usize, BTreeSet<String>),
}

/// The nodes under `root` of `p`, in preorder, positions moved by `base`.
fn shape<I: zedc::parse::Input + ?Sized>(
    p: &Parser<'_, I>,
    root: usize,
    base: usize,
) -> Vec<Shape> {
    let mut out = Vec::new();
    let mut stack = vec![root];
    while let Some(n) = stack.pop() {
        let node = &p.nodes[n];
        out.push((
            node.rule,
            node.alt,
            node.start + base,
            node.end + base,
            node.kids.len(),
            node.branches.clone(),
        ));
        stack.extend(node.kids.iter().rev());
    }
    out
}

/// What `p` expected at its farthest failure, as text.
fn expected<I: zedc::parse::Input + ?Sized>(p: &Parser<'_, I>) -> BTreeSet<String> {
    p.expected().iter().map(|e| format!("{e:?}")).collect()
}

/// The parse of `toks`, a program's tokens without `END`, as rule `unit` (`Item* END`) of `g`.
pub fn whole_parse(g: &Grammar, unit: &str, toks: &[(Kind, &str)]) -> Result<Parsed, String> {
    let unit = g
        .rule(unit)
        .ok_or_else(|| format!("the grammar has no rule {unit}"))?;
    let mut all = toks.to_vec();
    all.push((Kind::End, ""));
    let mut p = Parser::new(g, TOP, all.as_slice());
    Ok(match p.rule_node(unit, 0, false) {
        Some((end, root)) if end == all.len() => {
            let kids = p.nodes[root].kids.clone();
            Parsed::Items(kids.iter().map(|&k| shape(&p, k, 0)).collect())
        }
        _ => Parsed::Failed(p.far, expected(&p)),
    })
}

/// The parse of `toks` cut at `cuts` (from [`Splitter::cuts`]): each segment alone, as a list
/// of rule `item` of `g` that fills it. On a failure, the farthest failure of the segments up
/// to the first that fails, with the `END` the whole-file parse expects where its item list
/// stops, as the whole-file parse reports it.
pub fn split_parse(
    g: &Grammar,
    item: &str,
    toks: &[(Kind, &str)],
    cuts: &[usize],
) -> Result<Parsed, String> {
    let item = g
        .rule(item)
        .ok_or_else(|| format!("the grammar has no rule {item}"))?;
    let mut items = Vec::new();
    let mut fail = (0, BTreeSet::new());
    let ends = cuts.iter().skip(1).copied().chain([toks.len()]);
    for (s, e) in cuts.iter().copied().zip(ends) {
        let seg = &toks[s..e];
        let mut p = Parser::new(g, TOP, seg);
        let mut pos = 0;
        while pos < seg.len() {
            match p.rule_node(item, pos, false) {
                Some((end, node)) if end > pos => {
                    items.push(shape(&p, node, s));
                    pos = end;
                }
                _ => break,
            }
        }
        note(&mut fail, s + p.far, expected(&p));
        if pos < seg.len() {
            note(
                &mut fail,
                s + pos,
                BTreeSet::from(["Name(\"END\")".to_string()]),
            );
            return Ok(Parsed::Failed(fail.0, fail.1));
        }
    }
    Ok(Parsed::Items(items))
}

/// Adds the failures `what` at `at` to the farthest failures `fail`, as the engine keeps them.
fn note(fail: &mut (usize, BTreeSet<String>), at: usize, what: BTreeSet<String>) {
    if at > fail.0 {
        *fail = (at, BTreeSet::new());
    }
    if at == fail.0 {
        fail.1.extend(what);
    }
}

/// What one program gave.
#[derive(Clone, Debug, Default)]
pub struct Count {
    /// Tokens, without `END`.
    pub tokens: usize,
    /// Items of the whole-file parse; 0 when it failed.
    pub items: usize,
    /// Segments the scan cut it into.
    pub segments: usize,
    /// Whether the whole-file parse succeeded.
    pub parsed: bool,
    /// Whether the brackets balanced, so the scan cut it.
    pub balanced: bool,
    /// Whether the split parse gave what the whole-file parse gave.
    pub same: bool,
    /// Whether every cut is an item boundary of the whole-file parse.
    pub sound: bool,
    /// The item boundaries the scan did not cut, as the pair of token texts around each and the
    /// index of the token after the boundary.
    pub missed: Vec<(String, String, usize)>,
}

/// The text of a token for the miss table: a literal by its text, else its kind.
fn shown(k: Kind, text: &str) -> String {
    match k {
        Kind::Keyword | Kind::Op => text.to_string(),
        _ => k.name().to_string(),
    }
}

/// Compares the split parse of `toks` with its whole-file parse.
pub fn compare(sp: &Splitter, g: &Grammar, toks: &[(Kind, &str)]) -> Result<Count, String> {
    let whole = whole_parse(g, "Unit", toks)?;
    let mut c = Count {
        tokens: toks.len(),
        ..Count::default()
    };
    let cuts = sp.cuts(toks);
    c.balanced = cuts.is_some();
    let cuts = cuts.unwrap_or_else(|| vec![0]);
    c.segments = cuts.len();
    let split = split_parse(g, "Item", toks, &cuts)?;
    c.same = split == whole;
    c.sound = true;
    if let Parsed::Items(items) = &whole {
        c.parsed = true;
        c.items = items.len();
        let starts: BTreeSet<usize> = items.iter().map(|i| i[0].2).collect();
        c.sound = cuts.iter().all(|x| *x == 0 || starts.contains(x));
        let cut: BTreeSet<usize> = cuts.iter().copied().collect();
        for &b in starts.iter().filter(|b| **b > 0 && !cut.contains(b)) {
            let (a, z) = (toks[b - 1], toks[b]);
            c.missed.push((shown(a.0, a.1), shown(z.0, z.1), b));
        }
    }
    Ok(c)
}

/// The `.zed` files under `dir`, sorted.
pub fn zed_files(dir: &str) -> Result<Vec<String>, String> {
    let mut out = Vec::new();
    let mut dirs = vec![dir.to_string()];
    while let Some(d) = dirs.pop() {
        for entry in std::fs::read_dir(&d).map_err(|e| format!("{d}: {e}"))? {
            let path = entry.map_err(|e| format!("{d}: {e}"))?.path();
            let name = path.to_string_lossy().into_owned();
            if path.is_dir() {
                dirs.push(name);
            } else if name.ends_with(".zed") {
                out.push(name);
            }
        }
    }
    out.sort();
    Ok(out)
}

/// Runs the tool.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    let spec = Spec::open(arg(args, 0, "split SPEC_DIR [FILE…]")?)?;
    let sp = Splitter::new(&spec.syntactic, "Item")?;
    say!(
        out,
        "terminals {} pairs at depth 0 in an item {}",
        sp.terminals,
        sp.pairs
    );
    let mut programs: Vec<(String, String)> = Vec::new();
    if args.len() > 1 {
        for f in &args[1..] {
            programs.push((f.clone(), read_text(f)?));
        }
    } else {
        let docs = [spec.design.clone(), format!("{}/EXAMPLES.md", spec.root)];
        for doc in docs {
            for f in zed_fences(&doc)? {
                programs.push((
                    format!("{}:{}", f.file, f.line),
                    f.text.replace('…', "elided"),
                ));
            }
        }
        for f in zed_files(&format!("{}/zed", impl_root()))? {
            let text = read_text(&f)?;
            programs.push((f, text));
        }
    }
    let (mut tokens, mut items, mut cut, mut bounds) = (0, 0, 0, 0);
    let (mut bad, mut failed, mut lexfail, mut unbalanced) = (0, 0, 0, 0);
    let mut missed: BTreeMap<(String, String), (usize, String)> = BTreeMap::new();
    for (site, text) in &programs {
        let toks = match lex(&spec.lexical, text) {
            Ok(t) => t,
            Err(e) => {
                say!(out, "{site} LEX {e}");
                lexfail += 1;
                continue;
            }
        };
        let pairs: Vec<(Kind, &str)> = toks.0[..toks.0.len() - 1]
            .iter()
            .map(|t| (t.kind, t.text.as_str()))
            .collect();
        let c = compare(&sp, &spec.syntactic, &pairs)?;
        if !c.same || !c.sound {
            say!(out, "{site} DIFFERS same {} sound {}", c.same, c.sound);
            bad += 1;
        }
        failed += usize::from(!c.parsed);
        unbalanced += usize::from(!c.balanced);
        if c.parsed {
            tokens += c.tokens;
            items += c.items;
            cut += c.segments - 1;
            bounds += c.items.saturating_sub(1);
        }
        for (a, z, b) in c.missed {
            let near: Vec<&str> = pairs[b.saturating_sub(4)..(b + 4).min(pairs.len())]
                .iter()
                .map(|t| t.1)
                .collect();
            let first = format!("{site}: {}", near.join(" "));
            missed.entry((a, z)).or_insert((0, first)).0 += 1;
        }
    }
    say!(
        out,
        "programs {} lex errors {lexfail} parse errors {failed} unbalanced {unbalanced}",
        programs.len()
    );
    say!(
        out,
        "parsed programs: tokens {tokens} items {items} boundaries cut {cut} of {bounds}"
    );
    let mut rows: Vec<_> = missed.into_iter().collect();
    rows.sort_by(|a, b| b.1.0.cmp(&a.1.0).then(a.0.cmp(&b.0)));
    say!(out, "boundaries not cut, by the tokens around them:");
    for ((a, z), (k, first)) in rows {
        let _ = writeln!(out, "  {k:5}  {a} | {z}   first at {first}");
    }
    say!(out, "RESULT: {}", if bad == 0 { "OK" } else { "FAIL" });
    Ok(bad == 0)
}
