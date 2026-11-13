//! The containment fuzz. `fuzz SPEC_DIR [N [SEED]]` generates N sentences per ring (default 300,
//! seed 1): sentences generated from ring k must parse at k with the same tree at every ring
//! above, and a generated sentence whose derivation satisfied every lookahead must parse at all.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashSet};
use std::ops::RangeBounds;

use zedc::parse::{Expr, Grammar, Kind, Parser, TOP};

use crate::random::Random;
use crate::spec::Spec;
use crate::syntax::{Token, Tokens, Tree};
use crate::text::{prefix, repr};
use crate::{Outcome, arg, say};

/// A sentence has at most this many literals: longer ones are thrown away.
const MAX_TOKENS: usize = 200;

/// The nesting depth from which generation takes only the shallowest choices.
const MAX_DEPTH: u32 = 3;

/// The words generation writes for a token kind.
fn sample(k: Kind) -> &'static [&'static str] {
    match k {
        Kind::Ident => &["a", "b", "x", "f", "T"],
        Kind::Int => &["1", "2"],
        Kind::Float => &["1.5"],
        Kind::Rat => &["3r"],
        Kind::Str => &["\"s\""],
        Kind::Atom => &["#a", "#b"],
        Kind::Annot => &["@fused"],
        Kind::Wild => &["_"],
        Kind::Keyword | Kind::Op | Kind::End => &[],
    }
}

/// Whether expanding the rule counts toward the depth at which generation turns to the
/// shallowest choices.
fn nests(rule: &str) -> bool {
    matches!(
        rule,
        "Expr"
            | "Expr12"
            | "Type"
            | "Pattern"
            | "Item"
            | "Block"
            | "OutPattern"
            | "GAlt"
            | "Args"
            | "Params"
            | "Postfix"
            | "Or"
            | "And"
            | "Additive"
            | "Multiplicative"
            | "Reduce"
            | "Path"
            | "KeyPath"
            | "TypePostfix"
            | "TypeAnd"
            | "TypeOr"
            | "TypeDiff"
            | "AndJoin"
    )
}

const NEVER: u32 = 1_000_000_000;

/// The least nesting depth of a derivation of each rule at a ring.
#[derive(Debug)]
struct Depths(Vec<u32>);

impl Depths {
    /// Knuth's generalization of Dijkstra's algorithm: a rule's depth is final when it is the
    /// least left, since an alternative's depth is never below that of a rule it needs. Each
    /// final rule reopens only the alternatives that refer to it.
    fn new(g: &Grammar, ring: u32) -> Depths {
        let mut d = Depths(vec![NEVER; g.rules.len()]);
        let mut users = vec![Vec::new(); g.rules.len()];
        for (r, rule) in g.rules.iter().enumerate() {
            for alt in rule.alts.iter().filter(|a| a.layer <= ring) {
                refs(&alt.expr, &mut |used| users[used].push((r, &alt.expr)));
            }
        }
        let mut done = vec![false; g.rules.len()];
        let mut heap = BinaryHeap::new();
        for (r, rule) in g.rules.iter().enumerate() {
            for alt in rule.alts.iter().filter(|a| a.layer <= ring) {
                let depth = d.of(&alt.expr);
                if depth < d.0[r] {
                    d.0[r] = depth;
                    heap.push(Reverse((depth, r)));
                }
            }
        }
        while let Some(Reverse((depth, r))) = heap.pop() {
            if done[r] || depth != d.0[r] {
                continue;
            }
            done[r] = true;
            for &(user, e) in &users[r] {
                let depth = d.of(e);
                if depth < d.0[user] {
                    d.0[user] = depth;
                    heap.push(Reverse((depth, user)));
                }
            }
        }
        d
    }

    /// The least nesting depth of a derivation of `e`.
    fn of(&self, e: &Expr) -> u32 {
        match e {
            Expr::Rule(r) => self.0[*r] + 1,
            Expr::Seq(items) => items.iter().map(|x| self.of(x)).max().unwrap_or(0),
            Expr::Choice(alts) => {
                let least = alts.iter().map(|x| self.of(x)).min();
                least.expect("a choice has alternatives")
            }
            Expr::Plus(x) | Expr::SetHead(x) | Expr::ClearHead(x) => self.of(x),
            Expr::Sep(items) => self.of(&items[1]),
            Expr::Lit(_)
            | Expr::Kind(_)
            | Expr::Head
            | Expr::Star(_)
            | Expr::Opt(_)
            | Expr::And(_)
            | Expr::Not(_)
            | Expr::Class(_)
            | Expr::Any
            | Expr::Undefined(_) => 0,
        }
    }
}

/// Calls `f` on every rule that `Depths::of` reads in `e`.
fn refs(e: &Expr, f: &mut impl FnMut(usize)) {
    match e {
        Expr::Rule(r) => f(*r),
        Expr::Seq(xs) | Expr::Choice(xs) => xs.iter().for_each(|x| refs(x, f)),
        Expr::Plus(x) | Expr::SetHead(x) | Expr::ClearHead(x) => refs(x, f),
        Expr::Sep(items) => refs(&items[1], f),
        Expr::Lit(_)
        | Expr::Kind(_)
        | Expr::Head
        | Expr::Star(_)
        | Expr::Opt(_)
        | Expr::And(_)
        | Expr::Not(_)
        | Expr::Class(_)
        | Expr::Any
        | Expr::Undefined(_) => {}
    }
}

/// Why a derivation stopped.
#[derive(Clone, Copy, Debug)]
enum Stop {
    /// A rule with no alternative at the ring was reached.
    Dead,
    /// The sentence passed `MAX_TOKENS` tokens.
    TooLong,
}

/// A lookahead the derivation passed: its position, `&` or `!`, its expression, `HEAD`.
type Look<'g> = (usize, bool, &'g Expr, bool);

/// The state of one derivation.
struct Gen<'g, 'f> {
    fuzz: &'f mut Fuzz<'g>,
    depths: &'g Depths,
    ring: u32,
    out: Vec<Token>,
    looks: Vec<Look<'g>>,
}

/// The generator.
struct Fuzz<'g> {
    syn: &'g Grammar,
    keywords: HashSet<String>,
    rnd: Random,
    depths: &'g BTreeMap<u32, Depths>,
}

fn token(kind: Kind, text: &str) -> Token {
    Token {
        kind,
        text: text.into(),
        line: 1,
        holes: Vec::new(),
    }
}

impl<'g> Gen<'g, '_> {
    fn pick<T: Copy>(&mut self, xs: &[T]) -> T {
        xs[self.fuzz.rnd.next_int(xs.len() as u64) as usize]
    }

    /// Those of `xs` that have the least depth, from the depth at which that is the rule.
    fn shallow(&self, xs: Vec<&'g Expr>, depth: u32) -> Vec<&'g Expr> {
        if depth <= MAX_DEPTH {
            return xs;
        }
        let of = |x: &&Expr| self.depths.of(x);
        let best = xs.iter().map(of).min().expect("a choice is not empty");
        xs.into_iter().filter(|x| of(x) == best).collect()
    }

    fn rule(&mut self, r: usize, depth: u32, head: bool) -> Result<(), Stop> {
        let rule = &self.fuzz.syn.rules[r];
        let ring = self.ring;
        let mut live: Vec<_> = rule.alts.iter().filter(|a| a.layer <= ring).collect();
        if live.is_empty() {
            return Err(Stop::Dead);
        }
        if depth > MAX_DEPTH {
            let of = |a: &&zedc::parse::Alt| self.depths.of(&a.expr);
            let best = live.iter().map(of).min().expect("not empty");
            live.retain(|a| of(a) == best);
        }
        let a = self.pick(&live);
        let inner = depth + u32::from(nests(&rule.name) && !a.pass);
        self.gen_of(&a.expr, inner, head)
    }

    /// The repetitions of `e`, a `*`, `+`, `?` or the loop of a `%`, each the sequence `body`.
    fn repeat(
        &mut self,
        e: &'g Expr,
        body: &'g [Expr],
        depth: u32,
        head: bool,
    ) -> Result<(), Stop> {
        let plus = matches!(e, Expr::Plus(_));
        let mut n = u32::from(plus);
        if depth <= MAX_DEPTH {
            n += u32::from(self.fuzz.rnd.next_double() < 0.2);
            n += u32::from(self.fuzz.rnd.next_double() < 0.05);
        }
        if matches!(e, Expr::Opt(_)) {
            n = n.min(1);
        }
        for i in 0..n {
            let mark = self.out.len();
            match body.iter().try_for_each(|x| self.gen_of(x, depth, head)) {
                Ok(()) => {}
                Err(Stop::Dead) => {
                    self.out.truncate(mark);
                    if plus && i == 0 {
                        return Err(Stop::Dead);
                    }
                    break;
                }
                Err(Stop::TooLong) => return Err(Stop::TooLong),
            }
        }
        Ok(())
    }

    fn gen_of(&mut self, e: &'g Expr, depth: u32, head: bool) -> Result<(), Stop> {
        match e {
            Expr::Lit(text) => {
                let letter = text.chars().next().is_some_and(char::is_alphabetic);
                let kind = if self.fuzz.keywords.contains(text) {
                    Kind::Keyword
                } else if letter {
                    Kind::Ident
                } else {
                    Kind::Op
                };
                self.out.push(token(kind, text));
                if self.out.len() > MAX_TOKENS {
                    return Err(Stop::TooLong);
                }
            }
            Expr::Rule(r) => self.rule(*r, depth, head)?,
            Expr::Kind(k) => {
                if !sample(*k).is_empty() {
                    let word = self.pick(sample(*k));
                    self.out.push(token(*k, word));
                }
            }
            Expr::Seq(items) => {
                for x in items {
                    self.gen_of(x, depth, head)?;
                }
            }
            Expr::Choice(alts) => {
                let opts = self.shallow(alts.iter().collect(), depth);
                let x = self.pick(&opts);
                self.gen_of(x, depth, head)?;
            }
            Expr::Star(x) | Expr::Plus(x) | Expr::Opt(x) => {
                let x: &'g Expr = x;
                self.repeat(e, std::slice::from_ref(x), depth, head)?;
            }
            Expr::Sep(items) => {
                self.gen_of(&items[1], depth, head)?;
                self.repeat(e, &items[..], depth, head)?;
            }
            Expr::And(x) => self.looks.push((self.out.len(), true, x, head)),
            Expr::Not(x) => self.looks.push((self.out.len(), false, x, head)),
            Expr::SetHead(x) => self.gen_of(x, depth, true)?,
            Expr::ClearHead(x) => self.gen_of(x, depth, false)?,
            Expr::Head | Expr::Class(_) | Expr::Any | Expr::Undefined(_) => {}
        }
        Ok(())
    }
}

impl<'g> Fuzz<'g> {
    /// A random sentence of rule `start` at `ring`, and the lookaheads its derivation passed.
    fn sentence(&mut self, ring: u32, start: usize) -> Result<(Tokens, Vec<Look<'g>>), Stop> {
        let depths = &self.depths[&ring];
        let mut gen_state = Gen {
            fuzz: self,
            depths,
            ring,
            out: Vec::new(),
            looks: Vec::new(),
        };
        gen_state.rule(start, 0, false)?;
        let (mut out, looks) = (gen_state.out, gen_state.looks);
        out.push(token(Kind::End, ""));
        Ok((Tokens(out), looks))
    }
}

/// Whether every lookahead the derivation passed holds on the finished sentence.
fn looks_hold(syn: &Grammar, toks: &Tokens, looks: &[Look<'_>], ring: u32) -> bool {
    let mut p = Parser::new(syn, ring, toks);
    looks
        .iter()
        .all(|&(at, want, e, head)| p.holds(e, at, head) == want)
}

/// The parse of `start` over all of `toks`, or none. `Unit` reads the `END` token itself.
fn whole(syn: &Grammar, ring: u32, start: usize, toks: &Tokens) -> Option<Tree> {
    let mut p = Parser::new(syn, ring, toks);
    let (end, root) = p.rule_node(start, 0, false)?;
    let unit = syn.rules[start].name == "Unit";
    let want = toks.0.len() - usize::from(!unit);
    (end == want).then(|| Tree {
        nodes: std::mem::take(&mut p.nodes),
        root,
    })
}

fn text_of(toks: &Tokens) -> String {
    let words: Vec<&str> = toks.0[..toks.0.len() - 1]
        .iter()
        .map(|t| t.text.as_str())
        .collect();
    prefix(&words.join(" "), 300).to_string()
}

/// The running counts.
#[derive(Default)]
struct Counts {
    total: usize,
    bad: usize,
    derived: usize,
    covered: HashSet<(usize, usize)>,
}

/// Generates `n` sentences of rule `start` at ring `k` and checks each, and says how many
/// parsed.
fn run_ring(
    fuzz: &mut Fuzz<'_>,
    k: u32,
    start: usize,
    n: usize,
    count_derived: bool,
    c: &mut Counts,
    out: &mut String,
) -> usize {
    let syn = fuzz.syn;
    let mut kept = 0;
    for _ in 0..n {
        let Ok((toks, looks)) = fuzz.sentence(k, start) else {
            continue;
        };
        let Some(t) = whole(syn, k, start, &toks) else {
            // A sentence whose derivation satisfied every lookahead, yet does not parse: an
            // earlier choice or a greedy repetition captured part of it.
            if count_derived && looks_hold(syn, &toks, &looks, k) {
                c.derived += 1;
                say!(out, "L{k} derived but rejected: {}", text_of(&toks));
            }
            continue;
        };
        kept += 1;
        c.total += 1;
        t.lines(&mut c.covered);
        for k2 in k + 1..=TOP {
            if !whole(syn, k2, start, &toks).is_some_and(|t2| t2.same(&t)) {
                c.bad += 1;
                say!(out, "L{k} -> L{k2} differs: {}", text_of(&toks));
                break;
            }
        }
    }
    kept
}

/// The keywords: the quoted words of the lexical grammar's `KeywordWord` line.
fn keywords(lex_text: &str) -> Result<HashSet<String>, String> {
    let line = lex_text
        .split('\n')
        .find(|l| l.starts_with("KeywordWord"))
        .ok_or("the lexical grammar has no KeywordWord line")?;
    let parts: Vec<&str> = line.split('\'').collect();
    let closed = parts.len().saturating_sub(1) & !1;
    Ok(parts[..closed]
        .iter()
        .skip(1)
        .step_by(2)
        .map(|w| w.to_string())
        .collect())
}

/// The lines of the grammar that no accepted sentence used, by rule name and alternative.
fn missed<'g>(syn: &'g Grammar, c: &Counts) -> BTreeSet<(&'g str, usize)> {
    let mut out = BTreeSet::new();
    for (r, rule) in syn.rules.iter().enumerate() {
        for (i, a) in rule.alts.iter().enumerate() {
            if !a.pass && !c.covered.contains(&(r, i)) {
                out.insert((rule.name.as_str(), i));
            }
        }
    }
    out
}

/// Runs the tool.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    let spec = Spec::open(arg(args, 0, "fuzz SPEC_DIR [N [SEED]]")?)?;
    let number = |i: usize, default: i64| -> Result<i64, String> {
        args.get(i).map_or(Ok(default), |a| {
            a.parse().map_err(|_| format!("not a number: {a}"))
        })
    };
    let n = number(1, 300)? as usize;
    let seed = number(2, 1)?;
    run_on(&spec, n, seed, out)
}

/// The rings of a grammar and the depths the generator reads at each.
struct Rings {
    keys: BTreeSet<u32>,
    depths: BTreeMap<u32, Depths>,
}

impl Rings {
    fn new(syn: &Grammar) -> Rings {
        let keys: BTreeSet<u32> = syn
            .rules
            .iter()
            .flat_map(|r| r.alts.iter().map(|a| a.layer))
            .collect();
        let depths = keys.iter().map(|k| (*k, Depths::new(syn, *k))).collect();
        Rings { keys, depths }
    }

    /// The generator for the syntactic grammar of `spec`.
    fn fuzz<'g>(&'g self, spec: &'g Spec, seed: i64) -> Result<Fuzz<'g>, String> {
        Ok(Fuzz {
            syn: &spec.syntactic,
            keywords: keywords(&spec.lex_text)?,
            rnd: Random::new(seed),
            depths: &self.depths,
        })
    }

    /// Generates `n` sentences of `Unit` at each ring of `which` and checks them.
    fn first_pass(
        &self,
        which: impl RangeBounds<u32>,
        fuzz: &mut Fuzz<'_>,
        n: usize,
        c: &mut Counts,
        out: &mut String,
    ) -> Result<(), String> {
        let unit = fuzz
            .syn
            .rule("Unit")
            .ok_or("the grammar has no rule Unit")?;
        for &k in self.keys.range(which) {
            let kept = run_ring(fuzz, k, unit, n, true, c, out);
            say!(out, "ring L{k}: generated {n}, accepted {kept}");
        }
        Ok(())
    }
}

/// The first pass of the fuzz alone at the rings `which`, the part that grows with `n`: the second
/// pass covers what this one missed, which shrinks as `n` grows. Gives how many sentences parsed.
pub fn first_pass(
    spec: &Spec,
    which: impl RangeBounds<u32>,
    n: usize,
    seed: i64,
    out: &mut String,
) -> Result<usize, String> {
    let rings = Rings::new(&spec.syntactic);
    let mut c = Counts::default();
    rings.first_pass(which, &mut rings.fuzz(spec, seed)?, n, &mut c, out)?;
    Ok(c.total)
}

/// Runs the fuzz on `spec`.
pub fn run_on(spec: &Spec, n: usize, seed: i64, out: &mut String) -> Outcome {
    let syn = &spec.syntactic;
    let rings = Rings::new(syn);
    let mut fuzz = rings.fuzz(spec, seed)?;
    let mut c = Counts::default();
    rings.first_pass(.., &mut fuzz, n, &mut c, out)?;
    // A second pass starts at the rule of each line the first pass missed, at every ring it is
    // live in. It checks containment only: a sentence of an inner rule, out of its context, may
    // fail a lookahead.
    let first: BTreeSet<&str> = missed(syn, &c).into_iter().map(|(r, _)| r).collect();
    for name in first {
        let r = syn.rule(name).expect("a rule of this grammar");
        for &k in &rings.keys {
            if syn.rules[r].alts.iter().any(|a| a.layer <= k) {
                run_ring(&mut fuzz, k, r, n / 10, false, &mut c, out);
            }
        }
    }
    let lines: Vec<String> = missed(syn, &c)
        .iter()
        .map(|(r, i)| format!("({}, {i})", repr(r)))
        .collect();
    say!(out, "grammar lines never exercised: [{}]", lines.join(", "));
    say!(
        out,
        "accepted {} containment failures {} derived but rejected {}",
        c.total,
        c.bad,
        c.derived
    );
    let ok = c.bad == 0 && c.derived == 0;
    say!(out, "RESULT: {}", if ok { "OK" } else { "FAIL" });
    Ok(ok)
}
