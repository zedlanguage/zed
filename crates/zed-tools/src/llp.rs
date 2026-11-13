//! `llp SPEC_DIR [RULES]` reads the syntactic grammar as a context-free grammar and measures how
//! far it is from LLP(1,1), the class of grammars that a parallel parser in the manner of Pareas
//! parses from a table indexed by two terminals next to each other (plan row ZPARSE-par,
//! `docs/zparse-par-study.md`; the reference is laniusc `bin/parse_gen_tables/llp.rs`). It
//! prints the conflicts with no re-tagging, then after each rule of the file `RULES` (by default
//! [`RULES`]), the rules taken together in order.
//!
//! The PEG is read as a context-free grammar ([`Cfg::of`]):
//! - ordered choice is choice, so a conflict that the order of the alternatives settles shows as
//!   an LL(1) conflict;
//! - `e*`, `e+`, `e % s` and `e?` become right-recursive helper nonterminals;
//! - `head(…)` and `nest(…)` set and clear a flag that `HEAD` tests, so each rule has one copy
//!   for each value of the flag that reaches it (`Rule@head` for the copy with the flag set), and
//!   `HEAD` and `!HEAD` match the empty string or nothing;
//! - every other lookahead `&e` or `!e` has no LLP form: it is read as the empty string, which
//!   adds strings, and listed;
//! - direct left recursion `A = A x | y` becomes `A = y A~`, `A~ = x A~ | ε`; left recursion
//!   through other rules is listed.
//!
//! The pair table is that of Vagner and Melichar, as laniusc's `compute_gamma` gives it, but it
//! is built from items one at a time, not from item sets: each step of the construction reads one
//! item, so the table is the union over the items reached. An item is a core `A = α · β` with the
//! terminal after it, and a stack. From the final item of the start rule, a step goes back over
//! the symbol before the dot:
//! - over a terminal `x`, the stack becomes `[x]`;
//! - into a nonterminal `B`, to the end of each of its productions, keeping the stack;
//! - over `B` when the terminal after starts `B`, the stack becomes `[B]`;
//! - over a nullable `B` when it does not, `B` is pushed on the stack.
//!
//! An item whose dot follows a terminal `x` gives the pair (`x`, the terminal after) and its
//! stack; a pair with two stacks or more is a conflict. The terminal before an item is never read
//! by a step, so items do not carry it. A cycle of steps that keep or push, with a push in it,
//! gives stacks of every length: the grammar is not LLP(1,1) there, and every core the cycle
//! reaches gets the stack "no bound", so the search ends.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use zedc::parse::{Expr, Grammar, Kind};

use crate::spec::Spec;
use crate::split::Bits;
use crate::text::read_text;
use crate::{Outcome, arg, say};

/// The rules of the study, one a line, in two forms:
/// - `NAME: TOKEN in RULE… -> NEW`: `TOKEN`, a literal `'x'` or a kind such as `IDENT`, read
///   directly in one of the `RULE`s (not in the rules they call), is the terminal `NEW`. A lexer
///   pass would give the token that tag from the token before it; the tool checks whether the
///   token before it decides the tag.
/// - `NAME: end of RULE… -> NEW`: a virtual token `NEW` follows each match of the `RULE`s; the
///   rule `head` stands for each `head(…)`, and then the head flag is never set. The depth scan
///   would place the token as it finds a closing bracket.
///
/// These are the two rules that remove conflicts (`docs/zparse-par-study.md`).
pub const RULES: &str = "\
annot-close: end of AnnotExpr -> ANNOT_END
head-close: end of head -> HEAD_END
";

/// A grammar symbol.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Sym {
    /// A terminal, by number.
    T(u32),
    /// A nonterminal, by number.
    N(u32),
}

/// A production.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Prod {
    /// Its nonterminal.
    pub lhs: u32,
    /// What it derives.
    pub rhs: Vec<Sym>,
}

/// A context-free grammar read from a PEG.
#[derive(Clone, Debug, Default)]
pub struct Cfg {
    /// The terminals: a literal as `'x'`, a kind by its name.
    pub terms: Vec<String>,
    /// The nonterminals' names.
    pub nts: Vec<String>,
    /// The PEG rule each nonterminal comes from.
    pub origin: Vec<usize>,
    /// The productions.
    pub prods: Vec<Prod>,
    /// The start nonterminal, `START = END Unit`.
    pub start: u32,
    /// The lookaheads read as the empty string, as `Rule: text`.
    pub dropped: BTreeSet<String>,
}

/// A re-tagging rule: a token re-tagged, or a token put at the end of each match of some rules.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Retag {
    /// Its name.
    pub name: String,
    /// The token it re-tags: `'x'` or a kind; `None` for a new token at the end of each
    /// alternative of its rules, which the depth scan would place as it places a closing bracket.
    pub token: Option<String>,
    /// The PEG rules whose own reads of the token it re-tags, or whose ends it marks (`head` for
    /// each `head(…)`).
    pub rules: Vec<String>,
    /// The new terminal.
    pub to: String,
}

/// The rules written in `text`, one a line; a line that starts with `#` is a comment.
pub fn read_rules(text: &str) -> Result<Vec<Retag>, String> {
    let mut out = Vec::new();
    for (i, raw) in text.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let bad = || {
            format!(
                "rule line {}: want `NAME: TOKEN in RULE… -> NEW` or `NAME: end of RULE… -> NEW`: \
                 {raw}",
                i + 1
            )
        };
        let (name, rest) = line.split_once(':').ok_or_else(bad)?;
        let (lhs, to) = rest.rsplit_once("->").ok_or_else(bad)?;
        let mut words = lhs.split_whitespace();
        let token = match (words.next(), words.next()) {
            (Some("end"), Some("of")) => None,
            (Some(t), Some("in")) => Some(t.to_string()),
            _ => return Err(bad()),
        };
        let rules: Vec<String> = words.map(str::to_string).collect();
        if rules.is_empty() || to.trim().is_empty() || name.trim().is_empty() {
            return Err(bad());
        }
        out.push(Retag {
            name: name.trim().to_string(),
            token,
            rules,
            to: to.trim().to_string(),
        });
    }
    Ok(out)
}

/// The text of `e`, for the list of lookaheads.
fn show(g: &Grammar, e: &Expr) -> String {
    let all = |xs: &[Expr], sep: &str| {
        let parts: Vec<String> = xs.iter().map(|x| show(g, x)).collect();
        format!("({})", parts.join(sep))
    };
    match e {
        Expr::Lit(s) => format!("'{s}'"),
        Expr::Rule(r) => g.rules[*r].name.clone(),
        Expr::Kind(k) => k.name().to_string(),
        Expr::Head => "HEAD".to_string(),
        Expr::Seq(xs) => all(xs, " "),
        Expr::Choice(xs) => all(xs, " | "),
        Expr::Star(x) => format!("{}*", show(g, x)),
        Expr::Plus(x) => format!("{}+", show(g, x)),
        Expr::Opt(x) => format!("{}?", show(g, x)),
        Expr::Sep(pair) => format!("{} % {}", show(g, &pair[1]), show(g, &pair[0])),
        Expr::And(x) => format!("&{}", show(g, x)),
        Expr::Not(x) => format!("!{}", show(g, x)),
        Expr::SetHead(x) => format!("head({})", show(g, x)),
        Expr::ClearHead(x) => format!("nest({})", show(g, x)),
        Expr::Undefined(n) => n.clone(),
        Expr::Class(_) | Expr::Any => "[…]".to_string(),
    }
}

/// The reading of a PEG as a [`Cfg`].
struct Conv<'g> {
    g: &'g Grammar,
    cfg: Cfg,
    terms: HashMap<String, u32>,
    /// Each rule's nonterminal, by the value of the head flag.
    rules: HashMap<(usize, bool), u32>,
    /// Each helper nonterminal, by the address of its expression, used only as its identity,
    /// and the head flag.
    helpers: HashMap<(usize, bool), u32>,
    /// The rule nonterminals whose productions are still to be read.
    work: Vec<(usize, bool, u32)>,
    /// The re-tagging: (PEG rule, token) to the new terminal and the rule's index.
    retag: HashMap<(usize, String), (String, usize)>,
    /// The re-tagging rules that re-tagged some read.
    used: BTreeSet<usize>,
    /// The token placed after each `head(…)`, and its rule's index; with it the head flag is
    /// never set.
    head_end: Option<(u32, usize)>,
}

impl Conv<'_> {
    fn term(&mut self, name: &str) -> u32 {
        if let Some(&t) = self.terms.get(name) {
            return t;
        }
        let t = self.cfg.terms.len() as u32;
        self.cfg.terms.push(name.to_string());
        self.terms.insert(name.to_string(), t);
        t
    }

    /// The terminal of a read of `name` in rule `rule`, after re-tagging.
    fn token(&mut self, rule: usize, name: String) -> Sym {
        let name = match self.retag.get(&(rule, name.clone())) {
            Some((to, i)) => {
                self.used.insert(*i);
                to.clone()
            }
            None => name,
        };
        Sym::T(self.term(&name))
    }

    fn fresh(&mut self, name: String, origin: usize) -> u32 {
        self.cfg.nts.push(name);
        self.cfg.origin.push(origin);
        (self.cfg.nts.len() - 1) as u32
    }

    fn push(&mut self, lhs: u32, rhs: Vec<Sym>) {
        self.cfg.prods.push(Prod { lhs, rhs });
    }

    fn rule(&mut self, r: usize, head: bool) -> u32 {
        if let Some(&n) = self.rules.get(&(r, head)) {
            return n;
        }
        let name = format!(
            "{}{}",
            self.g.rules[r].name,
            if head { "@head" } else { "" }
        );
        let n = self.fresh(name, r);
        self.rules.insert((r, head), n);
        self.work.push((r, head, n));
        n
    }

    /// A new helper nonterminal of rule `rule` for the expression `e`, or the one made before.
    fn helper(&mut self, e: &Expr, head: bool, rule: usize) -> (u32, bool) {
        let key = (e as *const Expr as usize, head);
        if let Some(&n) = self.helpers.get(&key) {
            return (n, false);
        }
        let name = format!("{}.{}", self.g.rules[rule].name, self.cfg.nts.len());
        let n = self.fresh(name, rule);
        self.helpers.insert(key, n);
        (n, true)
    }

    /// The symbols of `e`, read in rule `rule`, or `None` when it matches nothing.
    fn seq(&mut self, e: &Expr, head: bool, rule: usize) -> Result<Option<Vec<Sym>>, String> {
        Ok(Some(match e {
            Expr::Lit(s) => vec![self.token(rule, format!("'{s}'"))],
            Expr::Kind(k) => vec![self.token(rule, k.name().to_string())],
            Expr::Rule(r) => vec![Sym::N(self.rule(*r, head))],
            Expr::Head => return Ok(head.then(Vec::new)),
            Expr::Seq(items) => {
                let mut out = Vec::new();
                for x in items {
                    match self.seq(x, head, rule)? {
                        Some(s) => out.extend(s),
                        None => return Ok(None),
                    }
                }
                out
            }
            Expr::Choice(alts) => {
                let (n, new) = self.helper(e, head, rule);
                if new {
                    for a in alts {
                        if let Some(s) = self.seq(a, head, rule)? {
                            self.push(n, s);
                        }
                    }
                }
                vec![Sym::N(n)]
            }
            Expr::Opt(x) => {
                let (n, new) = self.helper(e, head, rule);
                if new {
                    if let Some(s) = self.seq(x, head, rule)? {
                        self.push(n, s);
                    }
                    self.push(n, Vec::new());
                }
                vec![Sym::N(n)]
            }
            Expr::Star(x) => vec![Sym::N(self.star(e, x, None, head, rule)?)],
            Expr::Plus(x) => {
                let Some(mut s) = self.seq(x, head, rule)? else {
                    return Ok(None);
                };
                s.push(Sym::N(self.star(e, x, None, head, rule)?));
                s
            }
            Expr::Sep(pair) => {
                let [sep, x] = &**pair;
                let Some(mut s) = self.seq(x, head, rule)? else {
                    return Ok(None);
                };
                s.push(Sym::N(self.star(e, x, Some(sep), head, rule)?));
                s
            }
            Expr::And(x) | Expr::Not(x) if matches!(**x, Expr::Head) => {
                let holds = matches!(e, Expr::And(_)) == head;
                return Ok(holds.then(Vec::new));
            }
            Expr::And(_) | Expr::Not(_) => {
                let text = format!("{}: {}", self.g.rules[rule].name, show(self.g, e));
                self.cfg.dropped.insert(text);
                Vec::new()
            }
            Expr::SetHead(x) => match self.head_end {
                None => return self.seq(x, true, rule),
                Some((to, i)) => {
                    let Some(mut s) = self.seq(x, false, rule)? else {
                        return Ok(None);
                    };
                    self.used.insert(i);
                    s.push(Sym::T(to));
                    s
                }
            },
            Expr::ClearHead(x) => return self.seq(x, false, rule),
            Expr::Class(_) | Expr::Any => {
                return Err(format!(
                    "rule {}: a character class in a grammar over tokens",
                    self.g.rules[rule].name
                ));
            }
            Expr::Undefined(name) => {
                return Err(format!(
                    "rule {}: the undefined name {name}",
                    self.g.rules[rule].name
                ));
            }
        }))
    }

    /// The helper `S = sep x S | ε` (or `x S | ε` with no `sep`) of the repetition `e`.
    fn star(
        &mut self,
        e: &Expr,
        x: &Expr,
        sep: Option<&Expr>,
        head: bool,
        rule: usize,
    ) -> Result<u32, String> {
        let (n, new) = self.helper(e, head, rule);
        if !new {
            return Ok(n);
        }
        let mut body = Some(Vec::new());
        for y in sep.into_iter().chain([x]) {
            body = match (body, self.seq(y, head, rule)?) {
                (Some(mut b), Some(s)) => {
                    b.extend(s);
                    Some(b)
                }
                _ => None,
            };
        }
        if let Some(mut b) = body {
            b.push(Sym::N(n));
            self.push(n, b);
        }
        self.push(n, Vec::new());
        Ok(n)
    }
}

impl Cfg {
    /// The grammar `g` read from rule `unit` (`Item* END`), with the re-tagging `rules`.
    pub fn of(g: &Grammar, unit: &str, rules: &[Retag]) -> Result<Cfg, String> {
        let unit = g
            .rule(unit)
            .ok_or_else(|| format!("the grammar has no rule {unit}"))?;
        let mut retag = HashMap::new();
        let mut ends = HashMap::new();
        let mut head_end = None;
        for (i, r) in rules.iter().enumerate() {
            for name in &r.rules {
                if r.token.is_none() && name == "head" {
                    head_end = Some((r.to.clone(), i));
                    continue;
                }
                let at = g
                    .rule(name)
                    .ok_or_else(|| format!("re-tagging rule {}: no rule {name}", r.name))?;
                match &r.token {
                    Some(t) => retag.insert((at, t.clone()), (r.to.clone(), i)),
                    None => ends.insert(at, (r.to.clone(), i)),
                };
            }
        }
        let mut c = Conv {
            g,
            cfg: Cfg::default(),
            terms: HashMap::new(),
            rules: HashMap::new(),
            helpers: HashMap::new(),
            work: Vec::new(),
            retag,
            used: BTreeSet::new(),
            head_end: None,
        };
        c.head_end = head_end.map(|(to, i): (String, usize)| (c.term(&to), i));
        let start = c.fresh("START".to_string(), unit);
        let end = c.term(Kind::End.name());
        let body = c.rule(unit, false);
        c.push(start, vec![Sym::T(end), Sym::N(body)]);
        while let Some((r, head, n)) = c.work.pop() {
            for alt in &g.rules[r].alts {
                if let Some(mut s) = c.seq(&alt.expr, head, r)? {
                    if let Some((to, i)) = ends.get(&r) {
                        c.used.insert(*i);
                        s.push(Sym::T(c.term(to)));
                    }
                    c.push(n, s);
                }
            }
        }
        if let Some(i) = (0..rules.len()).find(|i| !c.used.contains(i)) {
            let r = &rules[i];
            return Err(match &r.token {
                Some(t) => format!("re-tagging rule {} re-tags no read of {t}", r.name),
                None => format!("re-tagging rule {} ends no alternative", r.name),
            });
        }
        let mut cfg = c.cfg;
        cfg.start = start;
        cfg.prune();
        cfg.unleft();
        cfg.prune();
        Ok(cfg)
    }

    /// The productions of each nonterminal.
    pub fn by_lhs(&self) -> Vec<Vec<usize>> {
        let mut out = vec![Vec::new(); self.nts.len()];
        for (p, prod) in self.prods.iter().enumerate() {
            out[prod.lhs as usize].push(p);
        }
        out
    }

    /// Drops the productions that use a nonterminal that derives no string, and those of
    /// nonterminals the start does not reach.
    fn prune(&mut self) {
        let n = self.nts.len();
        // Productive nonterminals, by a work list over the productions that use each one.
        let mut uses: Vec<Vec<usize>> = vec![Vec::new(); n];
        let mut missing: Vec<usize> = Vec::with_capacity(self.prods.len());
        for (p, prod) in self.prods.iter().enumerate() {
            let mut k = 0;
            for s in &prod.rhs {
                if let Sym::N(m) = s {
                    uses[*m as usize].push(p);
                    k += 1;
                }
            }
            missing.push(k);
        }
        let mut productive = vec![false; n];
        let mut work: Vec<usize> = (0..self.prods.len()).filter(|&p| missing[p] == 0).collect();
        while let Some(p) = work.pop() {
            let lhs = self.prods[p].lhs as usize;
            if !productive[lhs] {
                productive[lhs] = true;
                for &q in &uses[lhs] {
                    missing[q] -= 1;
                    if missing[q] == 0 {
                        work.push(q);
                    }
                }
            }
        }
        let ok = |s: &Sym| !matches!(s, Sym::N(m) if !productive[*m as usize]);
        self.prods.retain(|p| p.rhs.iter().all(ok));
        // Reachable nonterminals, with a visited set.
        let by_lhs = self.by_lhs();
        let mut seen = vec![false; n];
        seen[self.start as usize] = true;
        let mut stack = vec![self.start as usize];
        while let Some(a) = stack.pop() {
            for &p in &by_lhs[a] {
                for s in &self.prods[p].rhs {
                    if let Sym::N(m) = s
                        && !seen[*m as usize]
                    {
                        seen[*m as usize] = true;
                        stack.push(*m as usize);
                    }
                }
            }
        }
        self.prods.retain(|p| seen[p.lhs as usize]);
    }

    /// Rewrites direct left recursion: `A = A x | y` becomes `A = y A~`, `A~ = x A~ | ε`. A
    /// production `A = A` adds no string and is dropped.
    fn unleft(&mut self) {
        let by_lhs = self.by_lhs();
        let mut prods = Vec::with_capacity(self.prods.len());
        for (a, ps) in by_lhs.iter().enumerate() {
            let a = a as u32;
            let left = |p: &usize| self.prods[*p].rhs.first() == Some(&Sym::N(a));
            if !ps.iter().any(left) {
                prods.extend(ps.iter().map(|&p| self.prods[p].clone()));
                continue;
            }
            self.nts.push(format!("{}~", self.nts[a as usize]));
            self.origin.push(self.origin[a as usize]);
            let tail = Sym::N((self.nts.len() - 1) as u32);
            let Sym::N(t) = tail else { unreachable!() };
            for &p in ps {
                let rhs = &self.prods[p].rhs;
                if left(&p) {
                    if rhs.len() > 1 {
                        let mut r = rhs[1..].to_vec();
                        r.push(tail);
                        prods.push(Prod { lhs: t, rhs: r });
                    }
                } else {
                    let mut r = rhs.clone();
                    r.push(tail);
                    prods.push(Prod { lhs: a, rhs: r });
                }
            }
            prods.push(Prod {
                lhs: t,
                rhs: Vec::new(),
            });
        }
        self.prods = prods;
    }

    /// The name of a symbol.
    pub fn name(&self, s: Sym) -> &str {
        match s {
            Sym::T(t) => &self.terms[t as usize],
            Sym::N(n) => &self.nts[n as usize],
        }
    }
}

/// The sets of each nonterminal.
#[derive(Clone, Debug)]
pub(crate) struct Sets {
    /// Whether it derives the empty string.
    pub(crate) nullable: Vec<bool>,
    /// The terminals its strings start with.
    pub(crate) first: Vec<Bits>,
    /// The terminals its strings end with.
    pub(crate) last: Vec<Bits>,
    /// The terminals that come just before it.
    pub(crate) before: Vec<Bits>,
    /// The terminals that come just after it.
    pub(crate) follow: Vec<Bits>,
}

impl Sets {
    /// The sets of `cfg`, each by a work list over the productions: a production is read again
    /// when a set it reads grows. A set over T terminals grows at most T times.
    pub(crate) fn of(cfg: &Cfg) -> Sets {
        let (n, t) = (cfg.nts.len(), cfg.terms.len());
        let mut s = Sets {
            nullable: vec![false; n],
            first: vec![Bits::new(t); n],
            last: vec![Bits::new(t); n],
            before: vec![Bits::new(t); n],
            follow: vec![Bits::new(t); n],
        };
        let mut uses: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (p, prod) in cfg.prods.iter().enumerate() {
            for x in &prod.rhs {
                if let Sym::N(m) = x {
                    uses[*m as usize].push(p);
                }
            }
        }
        let mut queued = vec![true; cfg.prods.len()];
        let mut work: Vec<usize> = (0..cfg.prods.len()).collect();
        while let Some(p) = work.pop() {
            queued[p] = false;
            let prod = &cfg.prods[p];
            let (nul, first) = s.ends(&prod.rhs, t, true);
            let (_, last) = s.ends(&prod.rhs, t, false);
            let a = prod.lhs as usize;
            let grew = (nul && !s.nullable[a]) | s.first[a].add(&first) | s.last[a].add(&last);
            s.nullable[a] |= nul;
            if grew {
                for &q in &uses[a] {
                    if !queued[q] {
                        queued[q] = true;
                        work.push(q);
                    }
                }
            }
        }
        let by_lhs = cfg.by_lhs();
        let end = cfg.terms.iter().position(|x| x == Kind::End.name());
        if let Some(end) = end {
            s.before[cfg.start as usize].insert(end);
        }
        let mut queued = vec![true; cfg.prods.len()];
        let mut work: Vec<usize> = (0..cfg.prods.len()).collect();
        while let Some(p) = work.pop() {
            queued[p] = false;
            let prod = &cfg.prods[p];
            let a = prod.lhs as usize;
            let mut grown = Vec::new();
            // Before: the end of the prefix, or before the left side when the prefix can be
            // empty.
            let (mut pre, mut pre_null) = (Bits::new(t), true);
            for &x in &prod.rhs {
                if let Sym::N(b) = x {
                    let mut add = pre.clone();
                    if pre_null {
                        add.union(&s.before[a]);
                    }
                    if s.before[b as usize].add(&add) {
                        grown.push(b as usize);
                    }
                }
                s.extend(&mut pre, &mut pre_null, x, t, false);
            }
            let (mut suf, mut suf_null) = (Bits::new(t), true);
            for &x in prod.rhs.iter().rev() {
                if let Sym::N(b) = x {
                    let mut add = suf.clone();
                    if suf_null {
                        add.union(&s.follow[a]);
                    }
                    if s.follow[b as usize].add(&add) {
                        grown.push(b as usize);
                    }
                }
                s.extend(&mut suf, &mut suf_null, x, t, true);
            }
            for b in grown {
                for &q in &by_lhs[b] {
                    if !queued[q] {
                        queued[q] = true;
                        work.push(q);
                    }
                }
            }
        }
        s
    }

    /// Whether `rhs` can be empty, and its first terminals (`first`) or its last.
    fn ends(&self, rhs: &[Sym], t: usize, first: bool) -> (bool, Bits) {
        let mut out = Bits::new(t);
        let mut nul = true;
        let mut walk = |x: &Sym| match *x {
            Sym::T(a) => {
                out.insert(a as usize);
                false
            }
            Sym::N(m) => {
                out.union(if first {
                    &self.first[m as usize]
                } else {
                    &self.last[m as usize]
                });
                self.nullable[m as usize]
            }
        };
        if first {
            nul = rhs.iter().all(&mut walk);
        } else {
            for x in rhs.iter().rev() {
                if !walk(x) {
                    nul = false;
                    break;
                }
            }
        }
        (nul, out)
    }

    /// Puts `x` at the end of a string (or at its start, `first`) whose last (first) terminals
    /// are `acc` and whose emptiness is `nul`.
    fn extend(&self, acc: &mut Bits, nul: &mut bool, x: Sym, t: usize, first: bool) {
        match x {
            Sym::T(a) => {
                *acc = Bits::new(t);
                acc.insert(a as usize);
                *nul = false;
            }
            Sym::N(m) => {
                let m = m as usize;
                let set = if first { &self.first[m] } else { &self.last[m] };
                if self.nullable[m] {
                    acc.union(set);
                } else {
                    *acc = set.clone();
                    *nul = false;
                }
            }
        }
    }
}

/// The core of an LLP(1,1) item: production, dot and the terminal after the dot ([`NONE`] at the
/// end of the input). The item of Vagner and Melichar also holds the terminal before the dot and
/// the stack the pair pushes. No step reads the terminal before: every step makes the item with
/// each terminal of the production's prefix, so it is left out, which divides the items by up to
/// the number of terminals. The stack is kept beside the core ([`Stacks`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Core {
    prod: u32,
    dot: u32,
    ahead: u32,
}

/// No terminal: the lookahead of the start item.
const NONE: u32 = u32::MAX;

/// What a step does to the stack.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Move {
    /// The closure: the stack is kept.
    Keep,
    /// A step back over a nullable symbol that the terminal after does not start: the symbol
    /// goes on top of the stack.
    Push(Sym),
    /// A step back over a symbol that starts the terminal after: the stack is that symbol.
    Reset(Sym),
}

/// The empty stack.
const EMPTY: u32 = 0;
/// The stack of a core that has stacks without bound.
const UNBOUNDED: u32 = 1;

/// The stacks, interned as a top symbol over a rest, so a push costs O(1).
struct Stacks {
    cells: Vec<(Sym, u32)>,
    ids: HashMap<(Sym, u32), u32>,
}

impl Stacks {
    fn new() -> Stacks {
        Stacks {
            cells: vec![(Sym::T(NONE), EMPTY), (Sym::T(NONE), UNBOUNDED)],
            ids: HashMap::new(),
        }
    }

    fn push(&mut self, top: Sym, rest: u32) -> u32 {
        let next = self.cells.len() as u32;
        let id = *self.ids.entry((top, rest)).or_insert(next);
        if id == next {
            self.cells.push((top, rest));
        }
        id
    }

    /// Stack `id` as the names of its symbols, top first, in brackets.
    fn text(&self, cfg: &Cfg, mut id: u32) -> String {
        if id == UNBOUNDED {
            return "[no bound]".to_string();
        }
        let mut names = Vec::new();
        while id != EMPTY {
            let (top, rest) = self.cells[id as usize];
            names.push(cfg.name(top));
            id = rest;
        }
        format!("[{}]", names.join(" "))
    }
}

/// The steps of the items.
struct Llp<'c> {
    cfg: &'c Cfg,
    sets: &'c Sets,
    by_lhs: Vec<Vec<usize>>,
}

impl Llp<'_> {
    fn before_dot(&self, c: Core) -> Option<Sym> {
        let dot = c.dot as usize;
        (dot > 0).then(|| self.cfg.prods[c.prod as usize].rhs[dot - 1])
    }

    /// The cores one step from `c`, with what each step does to the stack. When a nonterminal
    /// `B` is before the dot, the closure gives the final items of `B`'s productions; the dot
    /// then moves back over the symbol before it. Both steps read one item, so the items of all
    /// the item sets of Vagner and Melichar are the items these steps reach from the start item.
    ///
    /// laniusc's stack for a step back over `x` with `v` after it is `x` then the old stack, cut
    /// after the first symbol that can start `v`. Every symbol of the old stack but its bottom
    /// was pushed because it does not start the same `v`, and its bottom starts `v`; so the cut
    /// is the whole old stack under `x` when `x` is nullable and does not start `v`, and `x` alone
    /// when it starts `v`.
    fn steps(&self, c: Core, out: &mut Vec<(Core, Move)>) {
        let Some(sym) = self.before_dot(c) else {
            return;
        };
        let back = |ahead: u32| Core {
            prod: c.prod,
            dot: c.dot - 1,
            ahead,
        };
        match sym {
            Sym::T(a) => out.push((back(a), Move::Reset(sym))),
            Sym::N(b) => {
                let b = b as usize;
                out.extend(self.by_lhs[b].iter().map(|&q| {
                    let dot = self.cfg.prods[q].rhs.len() as u32;
                    (
                        Core {
                            prod: q as u32,
                            dot,
                            ahead: c.ahead,
                        },
                        Move::Keep,
                    )
                }));
                let first = &self.sets.first[b];
                out.extend(first.iter().map(|v| (back(v as u32), Move::Reset(sym))));
                if self.sets.nullable[b] && c.ahead != NONE && !first.has(c.ahead as usize) {
                    out.push((back(c.ahead), Move::Push(sym)));
                }
            }
        }
    }
}

/// What one check found.
#[derive(Clone, Debug, Default)]
pub struct Report {
    /// Nonterminals, productions and terminals of the grammar read.
    pub size: (usize, usize, usize),
    /// The lookaheads read as the empty string.
    pub dropped: BTreeSet<String>,
    /// The groups of nonterminals left recursive through each other.
    pub left: Vec<Vec<String>>,
    /// The LL(1) table cells with two productions or more, by PEG rule.
    pub ll1: BTreeMap<String, usize>,
    /// The item cores reached from the start item.
    pub cores: usize,
    /// The items reached, a core and a stack each; a core with stacks without bound counts once.
    pub items: usize,
    /// The distinct stacks.
    pub stacks: usize,
    /// The symbols a cycle of steps pushes without bound, by the PEG rule of the step.
    pub unbounded: BTreeMap<String, BTreeSet<String>>,
    /// One cycle of each component that pushes, as the nonterminals of its steps.
    pub cycles: BTreeSet<String>,
    /// The pairs of terminals in the pair table.
    pub pairs: usize,
    /// The pairs with two stacks or more, as text, by the PEG rules of their productions.
    pub conflicts: BTreeMap<String, Vec<String>>,
    /// How many pairs have two stacks or more.
    pub conflict_count: usize,
    /// How many of those have stacks without bound.
    pub unbounded_count: usize,
    /// The stacks of each pair with two stacks or more, by the pair as text.
    pub stacks_of: BTreeMap<String, Vec<String>>,
    /// How many of those have stacks that are one stack when each `@head` copy is read as the
    /// nonterminal it copies.
    pub head_only: usize,
    /// How many of the others have stacks of one symbol each: the pair starts a construct that
    /// the two tokens do not name.
    pub starts: usize,
    /// The terminals before each terminal, by name.
    pub before: BTreeMap<String, BTreeSet<String>>,
}

/// The strongly connected component of each node of `edges`, by Tarjan's algorithm with an
/// explicit stack in place of recursion.
fn components(edges: &[Vec<usize>]) -> Vec<usize> {
    let n = edges.len();
    let mut index = vec![usize::MAX; n];
    let mut low = vec![0; n];
    let mut on = vec![false; n];
    let mut comp = vec![usize::MAX; n];
    let mut stack = Vec::new();
    let (mut next, mut comps) = (0, 0);
    for root in 0..n {
        if index[root] != usize::MAX {
            continue;
        }
        let mut call = vec![(root, 0usize)];
        index[root] = next;
        low[root] = next;
        next += 1;
        stack.push(root);
        on[root] = true;
        while let Some(&mut (v, ref mut k)) = call.last_mut() {
            if let Some(&w) = edges[v].get(*k) {
                *k += 1;
                if index[w] == usize::MAX {
                    index[w] = next;
                    low[w] = next;
                    next += 1;
                    stack.push(w);
                    on[w] = true;
                    call.push((w, 0));
                } else if on[w] {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            call.pop();
            if let Some(&(u, _)) = call.last() {
                low[u] = low[u].min(low[v]);
            }
            if low[v] == index[v] {
                while let Some(w) = stack.pop() {
                    on[w] = false;
                    comp[w] = comps;
                    if w == v {
                        break;
                    }
                }
                comps += 1;
            }
        }
    }
    comp
}

/// The groups of nonterminals that can each start with another of the group (left recursion).
fn left_groups(cfg: &Cfg, sets: &Sets) -> Vec<Vec<String>> {
    let n = cfg.nts.len();
    let mut edges: Vec<Vec<usize>> = vec![Vec::new(); n];
    for p in &cfg.prods {
        for x in &p.rhs {
            match *x {
                Sym::N(m) => {
                    edges[p.lhs as usize].push(m as usize);
                    if !sets.nullable[m as usize] {
                        break;
                    }
                }
                Sym::T(_) => break,
            }
        }
    }
    let comp = components(&edges);
    let mut groups: BTreeMap<usize, Vec<String>> = BTreeMap::new();
    for v in 0..n {
        if edges[v].iter().any(|&w| comp[w] == comp[v]) {
            groups.entry(comp[v]).or_default().push(cfg.nts[v].clone());
        }
    }
    let mut out: Vec<Vec<String>> = groups.into_values().collect();
    for g in &mut out {
        g.sort();
    }
    out.sort();
    out
}

/// The cycle from core `i` through its push step to `j` and back to `i`, as the nonterminals of
/// the productions it passes. The search stays in the component of `i`, so the searches of all
/// components cost one pass over the steps.
fn cycle(
    cfg: &Cfg,
    cores: &[Core],
    grow: &[Vec<usize>],
    comp: &[usize],
    i: usize,
    j: usize,
) -> String {
    let mut parent: HashMap<usize, usize> = HashMap::from([(j, j)]);
    let mut queue = std::collections::VecDeque::from([j]);
    while let Some(v) = queue.pop_front() {
        if v == i {
            break;
        }
        for &w in &grow[v] {
            if comp[w] == comp[i] && !parent.contains_key(&w) {
                parent.insert(w, v);
                queue.push_back(w);
            }
        }
    }
    let mut path = vec![i];
    let mut v = i;
    while v != j {
        v = parent[&v];
        path.push(v);
    }
    path.push(i);
    path.reverse();
    let mut names: Vec<&str> = Vec::new();
    for v in path {
        let name = cfg.nts[cfg.prods[cores[v].prod as usize].lhs as usize].as_str();
        if names.last() != Some(&name) {
            names.push(name);
        }
    }
    names.join(" > ")
}

/// Checks the grammar `g` from rule `unit`, re-tagged by `rules`.
// Complexity tradeoff: the LL(1) table and the before sets cost O(P × T / 64) word operations
// for P productions and T terminals, against O(P × T) for sets of terminal numbers. The item
// cores are at most (positions × (T + 1)) and are found once each, with a visited map. A cycle
// of steps that pushes a symbol gives stacks without bound; Tarjan's components find those
// cycles in time linear in the steps, and every core they reach takes one stack, UNBOUNDED,
// so the work list ends. The other stacks are bounded by the paths between cycles, which may be
// many in a grammar built for it; each item is visited once.
//
// laniusc builds the item sets of Vagner and Melichar and reads the items out of them, with
// stacks as vectors, so it never ends on a grammar with a pushing cycle. Without one, the
// number of sets is still exponential in the grammar at worst, as for canonical LR(1); on the
// Zed grammar it passed 1700 sets with 660 still queued after 40 s. The pair table is the same,
// since each step reads one item.
pub fn check(g: &Grammar, unit: &str, rules: &[Retag]) -> Result<Report, String> {
    let cfg = Cfg::of(g, unit, rules)?;
    let sets = Sets::of(&cfg);
    let t = cfg.terms.len();
    let mut r = Report {
        size: (cfg.nts.len(), cfg.prods.len(), t),
        dropped: cfg.dropped.clone(),
        left: left_groups(&cfg, &sets),
        ..Report::default()
    };
    let rule_of = |nt: u32| g.rules[cfg.origin[nt as usize]].name.clone();
    // LL(1): the productions each (nonterminal, terminal) cell predicts.
    let mut cells: HashMap<(u32, usize), usize> = HashMap::new();
    for p in &cfg.prods {
        let (nul, mut predict) = sets.ends(&p.rhs, t, true);
        if nul {
            predict.union(&sets.follow[p.lhs as usize]);
        }
        for a in predict.iter() {
            *cells.entry((p.lhs, a)).or_default() += 1;
        }
    }
    for (&(nt, _), &k) in &cells {
        if k > 1 {
            *r.ll1.entry(rule_of(nt)).or_default() += 1;
        }
    }
    // The terminals before each terminal.
    for prod in &cfg.prods {
        let (mut acc, mut nul) = (Bits::new(t), true);
        for &x in &prod.rhs {
            if let Sym::T(a) = x {
                let mut b = acc.clone();
                if nul {
                    b.union(&sets.before[prod.lhs as usize]);
                }
                let names = r.before.entry(cfg.terms[a as usize].clone()).or_default();
                names.extend(b.iter().map(|u| cfg.terms[u].clone()));
            }
            sets.extend(&mut acc, &mut nul, x, t, false);
        }
    }
    // The cores the start reaches, and their steps.
    let llp = Llp {
        cfg: &cfg,
        sets: &sets,
        by_lhs: cfg.by_lhs(),
    };
    let start = llp.by_lhs[cfg.start as usize][0];
    let mut cores = vec![Core {
        prod: start as u32,
        dot: cfg.prods[start].rhs.len() as u32,
        ahead: NONE,
    }];
    let mut ids: HashMap<Core, usize> = HashMap::from([(cores[0], 0)]);
    let mut steps: Vec<Vec<(usize, Move)>> = Vec::new();
    let mut buf = Vec::new();
    while steps.len() < cores.len() {
        llp.steps(cores[steps.len()], &mut buf);
        let mut row = Vec::with_capacity(buf.len());
        for (c, m) in buf.drain(..) {
            let next = cores.len();
            let id = *ids.entry(c).or_insert(next);
            if id == next {
                cores.push(c);
            }
            row.push((id, m));
        }
        steps.push(row);
    }
    r.cores = cores.len();
    // Cycles of steps that keep or push, with a push in them: the stacks have no bound there,
    // and in every core those steps reach from them.
    let grow: Vec<Vec<usize>> = steps
        .iter()
        .map(|row| {
            let kept = row.iter().filter(|(_, m)| !matches!(m, Move::Reset(_)));
            kept.map(|&(j, _)| j).collect()
        })
        .collect();
    let comp = components(&grow);
    let mut unbounded = vec![false; cores.len()];
    let mut work = Vec::new();
    let mut shown: HashSet<usize> = HashSet::new();
    for (i, row) in steps.iter().enumerate() {
        for &(j, m) in row {
            if let Move::Push(s) = m
                && comp[i] == comp[j]
            {
                let rule = rule_of(cfg.prods[cores[i].prod as usize].lhs);
                r.unbounded
                    .entry(rule)
                    .or_default()
                    .insert(cfg.name(s).to_string());
                if shown.insert(comp[i]) {
                    r.cycles.insert(cycle(&cfg, &cores, &grow, &comp, i, j));
                }
                if !unbounded[i] {
                    unbounded[i] = true;
                    work.push(i);
                }
            }
        }
    }
    while let Some(i) = work.pop() {
        for &j in &grow[i] {
            if !unbounded[j] {
                unbounded[j] = true;
                work.push(j);
            }
        }
    }
    // The items: each core with each stack that reaches it.
    let mut stacks = Stacks::new();
    let first = if unbounded[0] { UNBOUNDED } else { EMPTY };
    let mut seen: HashSet<(usize, u32)> = HashSet::from([(0, first)]);
    let mut work = vec![(0, first)];
    let mut table: BTreeMap<(u32, u32), BTreeMap<u32, BTreeSet<u32>>> = BTreeMap::new();
    while let Some((i, s)) = work.pop() {
        let c = cores[i];
        // The terminal before the dot is the terminal `x` just passed: the pair is (x, ahead).
        if let Some(Sym::T(x)) = llp.before_dot(c)
            && c.ahead != NONE
        {
            let row = table.entry((x, c.ahead)).or_default();
            row.entry(s).or_default().insert(c.prod);
        }
        for &(j, m) in &steps[i] {
            let next = match m {
                _ if unbounded[j] => UNBOUNDED,
                Move::Keep => s,
                Move::Push(y) => stacks.push(y, s),
                Move::Reset(y) => stacks.push(y, EMPTY),
            };
            if seen.insert((j, next)) {
                work.push((j, next));
            }
        }
    }
    r.items = seen.len();
    r.stacks = stacks.cells.len() - 2;
    r.pairs = table.len();
    for ((x, y), row) in &table {
        if row.len() < 2 && !row.contains_key(&UNBOUNDED) {
            continue;
        }
        r.conflict_count += 1;
        let mut text = format!("{} {}", cfg.terms[*x as usize], cfg.terms[*y as usize]);
        if row.contains_key(&UNBOUNDED) {
            r.unbounded_count += 1;
            text.push_str(" (no bound)");
        }
        let mut by: BTreeSet<String> = BTreeSet::new();
        for prods in row.values() {
            by.extend(prods.iter().map(|&p| rule_of(cfg.prods[p as usize].lhs)));
        }
        for rule in by {
            r.conflicts.entry(rule).or_default().push(text.clone());
        }
        let all: Vec<String> = row.keys().map(|&s| stacks.text(&cfg, s)).collect();
        let merged: BTreeSet<String> = all.iter().map(|s| s.replace("@head", "")).collect();
        if merged.len() == 1 && !row.contains_key(&UNBOUNDED) {
            r.head_only += 1;
        } else if all.iter().all(|s| !s.contains(' ') && s != "[no bound]") {
            r.starts += 1;
        }
        r.stacks_of.insert(text, all);
    }
    Ok(r)
}

/// The terminals before both `a` and one of `others`: what keeps the token before from
/// deciding a re-tagging.
pub fn shared(r: &Report, a: &str, others: &[&str]) -> BTreeSet<String> {
    let empty = BTreeSet::new();
    let mine = r.before.get(a).unwrap_or(&empty);
    others
        .iter()
        .flat_map(|o| r.before.get(*o).unwrap_or(&empty).intersection(mine))
        .cloned()
        .collect()
}

/// The LL(1) cells of `r`, in all.
fn ll1_total(r: &Report) -> usize {
    r.ll1.values().sum()
}

/// The pair conflicts of `r` by kind.
fn kinds(r: &Report) -> String {
    let rest = r.conflict_count - r.unbounded_count - r.head_only - r.starts;
    format!(
        "{} with no bound, {} only by HEAD copies, {} where the second token starts a construct \
         the pair does not name, {} where the tails that end differ",
        r.unbounded_count, r.head_only, r.starts, rest
    )
}

/// Runs the tool.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    let spec = Spec::open(arg(args, 0, "llp SPEC_DIR [RULES]")?)?;
    let rules = match args.get(1) {
        Some(f) => read_rules(&read_text(f)?)?,
        None => read_rules(RULES)?,
    };
    let g = &spec.syntactic;
    let base = check(g, "Unit", &[])?;
    let (n, p, t) = base.size;
    say!(
        out,
        "grammar: {} PEG rules, {n} nonterminals, {p} productions, {t} terminals",
        g.rules.len()
    );
    say!(
        out,
        "lookaheads with no LLP form, read as the empty string: {}",
        base.dropped.len()
    );
    for d in &base.dropped {
        say!(out, "  {d}");
    }
    say!(
        out,
        "left recursion through other rules: {}",
        base.left.len()
    );
    for group in &base.left {
        say!(out, "  {}", group.join(" "));
    }
    say!(
        out,
        "cycles of steps that push without bound, by PEG rule: {}",
        base.unbounded.len()
    );
    for (rule, syms) in &base.unbounded {
        let syms: Vec<&str> = syms.iter().map(String::as_str).collect();
        say!(out, "  {rule}: pushes {}", syms.join(" "));
    }
    for c in &base.cycles {
        say!(out, "  cycle: {c}");
    }
    say!(
        out,
        "no re-tagging: LL(1) conflicts {} cores {} items {} stacks {} pairs {} pair conflicts {} \
         ({})",
        ll1_total(&base),
        base.cores,
        base.items,
        base.stacks,
        base.pairs,
        base.conflict_count,
        kinds(&base)
    );
    let mut last = base;
    for i in 0..rules.len() {
        let r = check(g, "Unit", &rules[..=i])?;
        let rule = &rules[i];
        let placed = match &rule.token {
            None => "a virtual token the depth scan places".to_string(),
            Some(token) => {
                let others: Vec<&str> = std::iter::once(token.as_str())
                    .chain(
                        rules[..i]
                            .iter()
                            .filter(|o| o.token == rule.token && o.to != rule.to)
                            .map(|o| o.to.as_str()),
                    )
                    .collect();
                let both = shared(&r, &rule.to, &others);
                if both.is_empty() {
                    "the token before decides".to_string()
                } else {
                    let both: Vec<String> = both.into_iter().collect();
                    format!(
                        "the token before does not decide: both after {}",
                        both.join(" ")
                    )
                }
            }
        };
        say!(
            out,
            "after {}: LL(1) conflicts {} pair conflicts {} ({:+}; {}); {placed}",
            rule.name,
            ll1_total(&r),
            r.conflict_count,
            r.conflict_count as i64 - last.conflict_count as i64,
            kinds(&r)
        );
        last = r;
    }
    say!(out, "LL(1) conflicts left, by PEG rule:");
    let mut rows: Vec<(&String, &usize)> = last.ll1.iter().collect();
    rows.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
    for (rule, k) in rows {
        say!(out, "  {k:5}  {rule}");
    }
    say!(out, "pair conflicts left, by PEG rule:");
    let mut rows: Vec<(&String, &Vec<String>)> = last.conflicts.iter().collect();
    rows.sort_by(|a, b| b.1.len().cmp(&a.1.len()).then(a.0.cmp(b.0)));
    for (rule, pairs) in rows {
        let some: Vec<&str> = pairs.iter().take(4).map(String::as_str).collect();
        say!(
            out,
            "  {:5}  {rule}   e.g. {}",
            pairs.len(),
            some.join(", ")
        );
        if let Some(stacks) = last.stacks_of.get(&pairs[0]) {
            say!(out, "         stacks of {}: {}", pairs[0], stacks.join(" "));
        }
    }
    say!(out, "RESULT: {} pair conflicts", last.conflict_count);
    Ok(true)
}
