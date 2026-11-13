//! The trivial-model report of DESIGN.md sec:theories item 3, as the study prototype of plan
//! row TRIVIAL-models-study, kept where step L22.8 will use it.
//!
//! A trivial model has a carrier of one or two values, `#a` or `#a | #b`, and each function
//! field is a constant or a projection. On one value there is exactly one such model. On two
//! values a field of `n` arguments has `2 + n` choices (`#a`, `#b` and the `n` projections; a
//! field of no arguments is `#a` or `#b`).
//!
//! Under such a choice every term reduces to the end of one path from its root: a constant field
//! ends the path at its constant, a projection continues into its argument, and a binder ends it
//! at the binder. So an equation holds at every binding exactly when both sides end at the same
//! constant or the same binder, and `t1 != t2` holds at every binding exactly when the two sides
//! end at two different constants. A law whose body is one equation or one inequation is
//! therefore the set of "cubes" over its fields: partial choices under which both sides end
//! at the same symbol. A law body is read in negation normal form (`!` pushed onto the atoms,
//! `a.implies(b)` read as `!a || b`) and then as a conjunction of clauses, each an `||` of
//! atoms. A clause of one atom is a set of cubes; a clause of several is checked whole once all
//! but one of its fields are chosen, by a union-find with parities over the symbols its atoms end
//! at, in time linear in the clause.
//!
//! The models are the product over the groups of fields that a common law links; a field no law
//! names is free and is not enumerated. Within a group a depth-first search assigns the fields in
//! declaration order and keeps every constraint generalized-arc-consistent after each choice. A
//! group whose laws are single equations or inequations and whose fields and laws form a forest
//! (no cycle through two laws) never reaches a choice that leads to no model, so its search costs
//! work proportional to the models it lists. Any other group may (hardness tests); the default
//! report stops at the first such choice.

use std::cell::OnceCell;
use std::collections::hash_map::Entry;
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::fmt::Write as _;

/// A field of a theory: its name and how many arguments it takes.
pub struct Field {
    pub name: String,
    pub arity: usize,
}

/// The relation of an atom.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Rel {
    Eq,
    Ne,
}

/// A term of a law body, by index into [`Theory::terms`].
#[derive(Clone, Debug)]
pub enum Term {
    /// The law's binder of this index.
    Var(usize),
    /// A field applied to its arguments.
    App { field: usize, args: Vec<usize> },
}

/// `lhs == rhs` or `lhs != rhs`.
#[derive(Clone, Copy, Debug)]
pub struct Atom {
    pub rel: Rel,
    pub lhs: usize,
    pub rhs: usize,
}

/// A law body in negation normal form: `!` is pushed onto the atoms and `a.implies(b)` is read
/// as `!a || b`.
#[derive(Clone, Debug)]
pub enum Formula {
    Atom(Atom),
    And(Vec<Formula>),
    Or(Vec<Formula>),
}

impl Formula {
    /// The negation, by De Morgan's laws: linear in the formula.
    fn negate(self) -> Formula {
        match self {
            Formula::Atom(a) => Formula::Atom(Atom {
                rel: match a.rel {
                    Rel::Eq => Rel::Ne,
                    Rel::Ne => Rel::Eq,
                },
                ..a
            }),
            Formula::And(fs) => Formula::Or(fs.into_iter().map(Formula::negate).collect()),
            Formula::Or(fs) => Formula::And(fs.into_iter().map(Formula::negate).collect()),
        }
    }

    /// The atoms, in the order written.
    pub fn atoms(&self) -> Vec<Atom> {
        let mut out = Vec::new();
        let mut stack = vec![self];
        while let Some(f) = stack.pop() {
            match f {
                Formula::Atom(a) => out.push(*a),
                Formula::And(fs) | Formula::Or(fs) => stack.extend(fs.iter().rev()),
            }
        }
        out
    }

    /// The conjunctive normal form, written out: each clause an `||` of atoms. `work` counts the
    /// atoms written by distributing an `||` over an `&&`, the only step that is not linear in
    /// the law; `None` when the next such step would take the count past [`BUDGET`], before
    /// that step is taken.
    fn cnf(&self, work: &mut u64) -> Option<Vec<Vec<Atom>>> {
        match self {
            Formula::Atom(a) => Some(vec![vec![*a]]),
            Formula::And(fs) => {
                let mut out = Vec::new();
                for f in fs {
                    out.extend(f.cnf(work)?);
                }
                Some(out)
            }
            Formula::Or(fs) => {
                let mut acc: Vec<Vec<Atom>> = vec![Vec::new()];
                for f in fs {
                    let mut right = f.cnf(work)?;
                    if acc.len() == 1 && right.len() == 1 {
                        // One clause on each side: the operands are joined, nothing is copied.
                        acc[0].append(&mut right[0]);
                        continue;
                    }
                    // Each clause of the product joins one clause of each side, so each side's
                    // atoms are written once per clause of the other.
                    let atoms = |c: &[Vec<Atom>]| c.iter().map(Vec::len).sum::<usize>() as u64;
                    let step = atoms(&acc) * right.len() as u64 + atoms(&right) * acc.len() as u64;
                    *work = work.saturating_add(step);
                    if *work > BUDGET {
                        return None;
                    }
                    acc = acc
                        .iter()
                        .flat_map(|l| {
                            right.iter().map(move |r| {
                                let mut c = l.clone();
                                c.extend_from_slice(r);
                                c
                            })
                        })
                        .collect();
                }
                Some(acc)
            }
        }
    }
}

/// The steps of work the report may spend writing out one law's conjunctive normal form, each
/// step one atom written by distributing an `||` over an `&&`: the stand-in in this prototype
/// for the compile-time budget of QUESTIONS A54 (plan row MIX-budget), the one limit the
/// standing rules allow. A law with no `||` over an `&&` spends no steps, whatever its size.
pub const BUDGET: u64 = 1 << 20;

/// A law member.
pub struct Law {
    pub name: String,
    pub binders: Vec<String>,
    /// The body as written, for the report.
    pub text: String,
    pub body: Formula,
    /// The body as a conjunction of clauses, each an `||` of atoms; `None` when writing it
    /// out reached [`BUDGET`], and the report does not check the law.
    pub cnf: Option<Vec<Vec<Atom>>>,
}

impl Law {
    /// Whether the report does not check this law: writing out its conjunctive normal form
    /// reached [`BUDGET`].
    pub fn refused(&self) -> bool {
        self.cnf.is_none()
    }

    /// The clauses of a law that is not refused.
    pub fn clauses(&self) -> &[Vec<Atom>] {
        self.cnf.as_deref().expect("a refused law has no clauses")
    }
}

/// An interface with law members.
pub struct Theory {
    pub name: String,
    pub fields: Vec<Field>,
    /// Each field's index by name, so a law's names are read in O(1) each.
    field_index: HashMap<String, usize>,
    pub laws: Vec<Law>,
    pub terms: Vec<Term>,
}

/// The symbol a term ends at under a choice of every field it reaches.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Sym {
    Const(u32),
    Var(usize),
}

/// The choice of a field on two values: `0` is `#a`, `1` is `#b`, `2 + i` projects argument `i`.
pub type Choice = u32;

/// A side of an atom reduced until its first call of a field: the end symbol it reaches, or the
/// term of that call.
type Reached = Result<Sym, usize>;

/// The parity a clause's negated atom asks of its two sides' symbols: `==` negated is
/// "different" (1), `!=` negated is "equal" (0).
fn negated(rel: Rel) -> u8 {
    match rel {
        Rel::Eq => 1,
        Rel::Ne => 0,
    }
}

/// A union-find with the parity of each node to its root, on two values: parity 0 is "equal",
/// 1 "different". Union without ranks, with path compression: O(log) amortized per operation.
#[derive(Default)]
struct Parities {
    parent: Vec<usize>,
    parity: Vec<u8>,
}

impl Parities {
    /// A new node, its own root.
    fn add(&mut self) -> usize {
        self.parent.push(self.parent.len());
        self.parity.push(0);
        self.parent.len() - 1
    }

    /// The root of `x` and the parity of `x` to it.
    fn find(&mut self, x: usize) -> (usize, u8) {
        let (mut root, mut p) = (x, 0);
        while self.parent[root] != root {
            p ^= self.parity[root];
            root = self.parent[root];
        }
        // Path compression: each node on the path then points at the root, with its parity.
        let (mut y, mut py) = (x, p);
        while y != root {
            let (next, pn) = (self.parent[y], py ^ self.parity[y]);
            self.parent[y] = root;
            self.parity[y] = py;
            y = next;
            py = pn;
        }
        (root, p)
    }

    /// Records that `x` and `y` have parity `want`; false when that contradicts what is
    /// recorded.
    fn relate(&mut self, x: usize, y: usize, want: u8) -> bool {
        let ((rx, px), (ry, py)) = (self.find(x), self.find(y));
        if rx == ry {
            return px ^ py == want;
        }
        self.parent[rx] = ry;
        self.parity[rx] = px ^ py ^ want;
        true
    }
}

/// The symbols `#a`, `#b` and the binders a clause's sides end at, as nodes of a union-find
/// with parities: `#a` and `#b` are nodes 0 and 1, different; a binder gets a node when first
/// met, so the scratch is linear in the clause rather than in the law's binders.
struct Symbols {
    nodes: Parities,
    binder: HashMap<usize, usize>,
}

impl Default for Symbols {
    fn default() -> Self {
        let mut nodes = Parities::default();
        let (a, b) = (nodes.add(), nodes.add());
        nodes.relate(b, a, 1);
        Symbols {
            nodes,
            binder: HashMap::new(),
        }
    }
}

impl Symbols {
    fn node(&mut self, s: Sym) -> usize {
        match s {
            Sym::Const(c) => c as usize,
            Sym::Var(v) => *self.binder.entry(v).or_insert_with(|| self.nodes.add()),
        }
    }

    /// The root of symbol `s` and its parity to it.
    fn find_sym(&mut self, s: Sym) -> (usize, u8) {
        let x = self.node(s);
        self.nodes.find(x)
    }

    /// Records that `x` and `y` have parity `want`; false when that contradicts what is
    /// recorded.
    fn relate(&mut self, x: Sym, y: Sym, want: u8) -> bool {
        let (x, y) = (self.node(x), self.node(y));
        self.nodes.relate(x, y, want)
    }
}

/// The number of choices of a field of `arity` arguments.
pub fn choices(arity: usize) -> u32 {
    2 + arity as u32
}

impl Theory {
    pub fn new(name: &str) -> Self {
        Theory {
            name: name.to_string(),
            fields: Vec::new(),
            field_index: HashMap::new(),
            laws: Vec::new(),
            terms: Vec::new(),
        }
    }

    /// Adds a field of `arity` arguments.
    pub fn field(&mut self, name: &str, arity: usize) -> &mut Self {
        let prior = self.field_index.insert(name.to_string(), self.fields.len());
        assert!(prior.is_none(), "field {name} declared twice");
        self.fields.push(Field {
            name: name.to_string(),
            arity,
        });
        self
    }

    /// Adds a law with the binders named in `binders` (separated by spaces or commas) and the
    /// body `body`, written with `==`, `!=`, `&&`, `||`, `!`, `(a).implies(b)`, parentheses,
    /// field applications and binders.
    pub fn law(&mut self, name: &str, binders: &str, body: &str) -> &mut Self {
        let binders: Vec<String> = binders
            .split([' ', ','])
            .filter(|b| !b.is_empty())
            .map(str::to_string)
            .collect();
        let tokens = tokenize(body);
        let index: HashMap<&str, usize> = binders
            .iter()
            .enumerate()
            .map(|(i, b)| (b.as_str(), i))
            .collect();
        assert_eq!(
            index.len(),
            binders.len(),
            "law {name}: a binder named twice"
        );
        let mut p = Parser {
            theory: self,
            binders: index,
            tokens: &tokens,
            at: 0,
        };
        let parsed = p.or();
        assert_eq!(p.at, tokens.len(), "law {name}: text after the body");
        // Complexity tradeoff: a law is decided through its conjunctive normal form, linear in
        // the law when no `||` has an `&&` among its operands, and the product of the
        // operands' clause counts when one has. What is given up: writing the form out is
        // charged against BUDGET, the stand-in for A54's compile-time budget, which plan row
        // MIX-budget replaces. The charge is the work done, one step per atom written by
        // distributing an `||` over an `&&`, so a law with no such `||` is never refused,
        // whatever its size. A law whose writing reaches the budget is refused with its own
        // message (`render`), not checked. Why it cannot be avoided: deciding a law of the shape
        // `(..&&..) || (..&&..) || ...` on two values is coNP-complete in its size
        // (`hardness::an_or_of_ands_is_refused` gives the reduction from 3-SAT), so every method
        // is exponential on some law of that shape. Structural trigger: an `||` whose operands
        // include several `&&`s. Tests: `hardness::an_or_of_ands_is_refused`,
        // `hardness::the_work_limit_is_not_a_size_limit`; COMPLEXITY.md C32.
        let cnf = parsed.cnf(&mut 0);
        self.laws.push(Law {
            name: name.to_string(),
            binders,
            text: body.to_string(),
            body: parsed,
            cnf,
        });
        self
    }

    /// The field of this name.
    pub fn field_id(&self, name: &str) -> Option<usize> {
        self.field_index.get(name).copied()
    }

    /// The symbol `t` ends at when each field `f` it reaches is `choice(f)`.
    pub fn reduce(&self, mut t: usize, choice: impl Fn(usize) -> Choice) -> Sym {
        loop {
            match &self.terms[t] {
                Term::Var(v) => return Sym::Var(*v),
                Term::App { field, args } => {
                    let c = choice(*field);
                    if c < 2 {
                        return Sym::Const(c);
                    }
                    t = args[(c - 2) as usize];
                }
            }
        }
    }

    /// The fields law `l` names, in declaration order, each once.
    pub fn law_scope(&self, l: usize) -> Vec<usize> {
        self.atoms_scope(&self.laws[l].body.atoms())
    }

    /// The fields some atom of `atoms` names, each once, in declaration order.
    fn atoms_scope(&self, atoms: &[Atom]) -> Vec<usize> {
        let mut out = Vec::new();
        for a in atoms {
            self.term_fields(a.lhs, &mut out);
            self.term_fields(a.rhs, &mut out);
        }
        out.sort_unstable();
        out.dedup();
        out
    }

    fn atom_scope(&self, a: &Atom) -> Vec<usize> {
        self.atoms_scope(std::slice::from_ref(a))
    }

    /// Pushes the fields `t` names onto `out`, by an explicit stack.
    fn term_fields(&self, t: usize, out: &mut Vec<usize>) {
        let mut stack = vec![t];
        while let Some(t) = stack.pop() {
            match &self.terms[t] {
                Term::Var(_) => {}
                Term::App { field, args } => {
                    out.push(*field);
                    stack.extend(args.iter().copied());
                }
            }
        }
    }

    /// Whether law `l` holds at every binding on two values when each field `f` is `choice(f)`:
    /// whether each clause of its conjunctive normal form does. The law must not be refused.
    pub fn law_holds(&self, l: usize, choice: impl Fn(usize) -> Choice + Copy) -> bool {
        (0..self.laws[l].clauses().len()).all(|k| self.clause_holds(l, k, choice))
    }

    /// Whether clause `k` of law `l`, an `||` of atoms, holds at every binding on two values
    /// when each field `f` is `choice(f)`. It fails exactly when some binding makes every atom
    /// false, that is when the negated atoms can all hold together: each says that two of the
    /// symbols `#a`, `#b` and the binders are equal or different, which a union-find with the
    /// parity of each node to its root decides, with `#a` and `#b` different. Time linear in the
    /// clause up to a log factor: O(c log c) for a clause of c atoms.
    pub fn clause_holds(
        &self,
        l: usize,
        k: usize,
        choice: impl Fn(usize) -> Choice + Copy,
    ) -> bool {
        let mut symbols = Symbols::default();
        self.laws[l].clauses()[k].iter().any(|a| {
            let (x, y) = (self.reduce(a.lhs, choice), self.reduce(a.rhs, choice));
            !symbols.relate(x, y, negated(a.rel))
        })
    }

    /// The choices of field `f` among those `alive` allows under which clause `k` of law `l`
    /// fails, when every other field `g` is `choice(g)`. The atoms whose paths do not reach `f`
    /// are related once; for each choice of `f` only the atoms whose paths reach it are, each from
    /// where it reaches `f`, in a second union-find over the roots of the first. Each such atom
    /// holds a call of `f` with all its arguments, and the choices continue into different
    /// arguments, so the work is linear in the clause up to a log factor, however many arguments
    /// `f` takes; evaluating the whole clause once per choice would be the choices times the
    /// clause (`scaling::one_wide_field_scales`).
    pub fn clause_fails_for(
        &self,
        l: usize,
        k: usize,
        f: usize,
        alive: impl Fn(Choice) -> bool,
        choice: impl Fn(usize) -> Choice + Copy,
    ) -> Vec<Choice> {
        let mut base = Symbols::default();
        // The atoms whose paths reach `f`: each side's symbol, or the call of `f` it reaches.
        let mut reach: Vec<(Reached, Reached, u8)> = Vec::new();
        for a in &self.laws[l].clauses()[k] {
            let want = negated(a.rel);
            match (
                self.reduce_until(a.lhs, choice, f),
                self.reduce_until(a.rhs, choice, f),
            ) {
                (Ok(x), Ok(y)) => {
                    if !base.relate(x, y, want) {
                        // The clause holds whatever `f` is.
                        return Vec::new();
                    }
                }
                (x, y) => reach.push((x, y, want)),
            }
        }
        let with = |v: Choice| move |g: usize| if g == f { v } else { choice(g) };
        let end = |side: Reached, v: Choice| match side {
            Ok(s) => s,
            Err(_) if v < 2 => Sym::Const(v),
            Err(t) => match &self.terms[t] {
                Term::App { args, .. } => self.reduce(args[(v - 2) as usize], with(v)),
                Term::Var(_) => unreachable!("a call of f is an application"),
            },
        };
        (0..choices(self.fields[f].arity))
            .filter(|&v| alive(v))
            .filter(|&v| {
                // The second union-find, over the roots of the first: the clause fails under
                // `v` when the negated atoms that reach `f` agree with the rest.
                let mut local = Parities::default();
                let mut id: HashMap<usize, usize> = HashMap::new();
                reach.iter().all(|&(x, y, want)| {
                    let (rx, px) = base.find_sym(end(x, v));
                    let (ry, py) = base.find_sym(end(y, v));
                    let mut node = |r: usize| *id.entry(r).or_insert_with(|| local.add());
                    let (lx, ly) = (node(rx), node(ry));
                    local.relate(lx, ly, want ^ px ^ py)
                })
            })
            .collect()
    }

    /// The symbol `t` ends at when each field `g` it reaches is `choice(g)`, or the first call
    /// of field `f` its path reaches.
    fn reduce_until(&self, mut t: usize, choice: impl Fn(usize) -> Choice, f: usize) -> Reached {
        loop {
            match &self.terms[t] {
                Term::Var(v) => return Ok(Sym::Var(*v)),
                Term::App { field, .. } if *field == f => return Err(t),
                Term::App { field, args } => {
                    let c = choice(*field);
                    if c < 2 {
                        return Ok(Sym::Const(c));
                    }
                    t = args[(c - 2) as usize];
                }
            }
        }
    }

    /// Whether law `l` holds on one value, where every two terms are equal: its body with each
    /// `==` true and each `!=` false.
    pub fn law_holds_on_one_value(&self, l: usize) -> bool {
        fn eval(f: &Formula) -> bool {
            match f {
                Formula::Atom(a) => a.rel == Rel::Eq,
                Formula::And(fs) => fs.iter().all(eval),
                Formula::Or(fs) => fs.iter().any(eval),
            }
        }
        eval(&self.laws[l].body)
    }

    /// The paths of `t`: each symbol it may end at with the choices that make it end there.
    fn exits(&self, t: usize) -> Vec<(Sym, Vec<(usize, Choice)>)> {
        let mut out = Vec::new();
        let mut stack: Vec<(usize, Vec<(usize, Choice)>)> = vec![(t, Vec::new())];
        while let Some((t, cond)) = stack.pop() {
            match &self.terms[t] {
                Term::Var(v) => out.push((Sym::Var(*v), cond)),
                Term::App { field, args } => {
                    let fixed = cond
                        .binary_search_by_key(field, |&(f, _)| f)
                        .map(|i| cond[i].1);
                    match fixed {
                        Ok(c) if c < 2 => out.push((Sym::Const(c), cond)),
                        Ok(c) => stack.push((args[(c - 2) as usize], cond)),
                        Err(at) => {
                            // Each choice extends the condition by one entry, written at its
                            // final length so that no path is copied twice.
                            for c in 0..choices(args.len()) {
                                let mut next = Vec::with_capacity(cond.len() + 1);
                                next.extend_from_slice(&cond[..at]);
                                next.push((*field, c));
                                next.extend_from_slice(&cond[at..]);
                                if c < 2 {
                                    out.push((Sym::Const(c), next));
                                } else {
                                    stack.push((args[(c - 2) as usize], next));
                                }
                            }
                        }
                    }
                }
            }
        }
        out
    }

    /// One atom as constraints. Each side's paths are sorted by the symbol they end at, keyed so
    /// that the atom holds exactly when the two keys agree: for `==` the symbol itself, for `!=`
    /// the left constant and the other constant on the right, and no key for a binder. Then
    /// the sides are joined on the key, in O(p log p) for p paths. When the sides name a common
    /// field the join is also on that field's choice, and the atom is held as pairs of paths
    /// (`pair_form`).
    fn atom_form(&self, a: &Atom) -> AtomForm {
        let (mut lf, mut rf) = (Vec::new(), Vec::new());
        self.term_fields(a.lhs, &mut lf);
        self.term_fields(a.rhs, &mut rf);
        lf.sort_unstable();
        lf.dedup();
        rf.sort_unstable();
        rf.dedup();
        let shared = {
            let (mut i, mut j, mut any) = (0, 0, false);
            while i < lf.len() && j < rf.len() && !any {
                match lf[i].cmp(&rf[j]) {
                    std::cmp::Ordering::Less => i += 1,
                    std::cmp::Ordering::Greater => j += 1,
                    std::cmp::Ordering::Equal => any = true,
                }
            }
            any
        };
        if shared {
            return AtomForm::Pairs(self.pair_form(a, &lf, &rf));
        }
        let key = |side: Vec<(Sym, Vec<(usize, Choice)>)>, flip: bool| {
            let mut out: Vec<(Sym, Vec<(usize, Choice)>)> = side
                .into_iter()
                .filter_map(|(s, cond)| match (a.rel, s) {
                    (Rel::Eq, _) => Some((s, cond)),
                    (Rel::Ne, Sym::Const(c)) => {
                        Some((Sym::Const(if flip { 1 - c } else { c }), cond))
                    }
                    (Rel::Ne, Sym::Var(_)) => None,
                })
                .collect();
            out.sort_by_key(|&(s, _)| s);
            out
        };
        let (left, right) = (key(self.exits(a.lhs), false), key(self.exits(a.rhs), true));
        // The runs of equal keys on each side, walked together.
        let runs = |side: &[(Sym, Vec<(usize, Choice)>)]| {
            let mut out: Vec<(Sym, std::ops::Range<usize>)> = Vec::new();
            for (i, (s, _)) in side.iter().enumerate() {
                match out.last_mut() {
                    Some((t, r)) if t == s => r.end = i + 1,
                    _ => out.push((*s, i..i + 1)),
                }
            }
            out
        };
        let (lr, rr) = (runs(&left), runs(&right));
        let mut common: Vec<(std::ops::Range<usize>, std::ops::Range<usize>)> = Vec::new();
        let (mut i, mut j) = (0, 0);
        while i < lr.len() && j < rr.len() {
            match lr[i].0.cmp(&rr[j].0) {
                std::cmp::Ordering::Less => i += 1,
                std::cmp::Ordering::Greater => j += 1,
                std::cmp::Ordering::Equal => {
                    common.push((lr[i].1.clone(), rr[j].1.clone()));
                    i += 1;
                    j += 1;
                }
            }
        }
        if !common.is_empty() {
            // The sides name different fields, so every pair of paths is consistent and the
            // atom is exactly "the left side ends at s and the right side ends at s" for one
            // end symbol s: two constraints joined by s, linear in the paths. The field–constraint
            // graph gains the path left fields – s – right fields, with no cycle, so arc
            // consistency is as strong as on the pairs.
            // The paths in the common runs, moved, not copied, each with its run's index as the
            // value of the end symbol. The runs are in order, so one walk of a side finds them.
            let ends = |side: Vec<(Sym, Vec<(usize, Choice)>)>, on_right: bool| {
                let run = |v: usize| if on_right { &common[v].1 } else { &common[v].0 };
                let mut out = Vec::with_capacity((0..common.len()).map(|v| run(v).len()).sum());
                let mut v = 0;
                for (i, (_, cond)) in side.into_iter().enumerate() {
                    while v < common.len() && run(v).end <= i {
                        v += 1;
                    }
                    if v < common.len() && run(v).start <= i {
                        out.push((v as u32, cond));
                    }
                }
                out
            };
            let (l, r) = (ends(left, false), ends(right, true));
            return AtomForm::Split {
                dom: common.len() as u32,
                left: (lf, l),
                right: (rf, r),
            };
        }
        // The sides end at no common symbol: the atom never holds.
        AtomForm::Never
    }

    /// The decision tree of term `t`, as `exits` walks it: a node tests a field not chosen above
    /// it and has a child for each of its choices, and a leaf ends a path, with the key `key`
    /// gives the symbol it ends at. Fields are numbered by their place in `scope`. Built by an
    /// explicit stack in O(paths' choices), each node once.
    fn tree(&self, t: usize, scope: &[usize], key: impl Fn(Sym) -> Option<Sym>) -> Tree {
        enum Step {
            /// A node to make, reached by the choices on the stack, and the place in `kid`
            /// that holds it, `NONE` for the root.
            Visit(Result<Sym, usize>, usize),
            Fix(usize, Choice),
            Unfix(usize),
        }
        let mut tree = Tree::default();
        let mut fixed = vec![MENTION; scope.len()];
        let mut stack = vec![Step::Visit(Err(t), NONE)];
        while let Some(step) = stack.pop() {
            let (mut at, place) = match step {
                Step::Fix(s, c) => {
                    fixed[s] = c;
                    continue;
                }
                Step::Unfix(s) => {
                    fixed[s] = MENTION;
                    continue;
                }
                Step::Visit(at, place) => (at, place),
            };
            if place != NONE {
                tree.kid[place] = tree.test.len();
            }
            // Follow the fields chosen above to a symbol or to a field not chosen.
            let open = loop {
                let Err(term) = at else { break None };
                match &self.terms[term] {
                    Term::Var(v) => at = Ok(Sym::Var(*v)),
                    Term::App { field, args } => {
                        let s = scope.binary_search(field).expect("a field of the atom");
                        match fixed[s] {
                            MENTION => break Some((s, args)),
                            c if c < 2 => at = Ok(Sym::Const(c)),
                            c => at = Err(args[(c - 2) as usize]),
                        }
                    }
                }
            };
            match (open, at) {
                (Some((s, args)), _) => {
                    let first = tree.kid.len();
                    tree.test.push(s);
                    tree.key.push(None);
                    tree.kid_at.push(first..first + args.len() + 2);
                    tree.kid.resize(first + args.len() + 2, NONE);
                    stack.push(Step::Unfix(s));
                    for c in (0..choices(args.len())).rev() {
                        let target = if c < 2 {
                            Ok(Sym::Const(c))
                        } else {
                            Err(args[(c - 2) as usize])
                        };
                        stack.push(Step::Visit(target, first + c as usize));
                        stack.push(Step::Fix(s, c));
                    }
                }
                (None, Ok(sym)) => {
                    tree.test.push(NONE);
                    tree.key.push(key(sym));
                    tree.kid_at.push(0..0);
                }
                (None, Err(_)) => unreachable!("the loop ends at a symbol or an open field"),
            }
        }
        tree
    }

    /// An atom whose sides name a common field, as the pairs of paths that agree: numbered and
    /// written as runs of pair numbers, never one by one with their choices.
    ///
    /// Complexity tradeoff: the naive method writes out each pair of paths with equal keys that
    /// agree on the common fields, with the choices of both: the pairs times their length, cubic
    /// in the atom (`f1(..fd(x)..) == fd(..f1(x)..)` has d^2 + d + 1 pairs and about 2 d^3 / 3
    /// choices; d = 50 and 400: 42 and 18,711 million instructions for the default report, 442
    /// times). Here a pair is a number and the pairs are written as runs: the runs of one
    /// field's nodes do not nest, so a pair's cube holds a choice exactly when the pair lies in a
    /// run of that choice, and names a field exactly when it lies in a run of a node of that
    /// field. The engine keeps the runs, not the cubes (`Engine`).
    ///
    /// The walk. Naive (plan rows TRIVIAL-shared-atom, TRIVIAL-walk-index): the left side's tree,
    /// and at each left leaf the right side's tree under its `KeyIndex` entry for the leaf's key,
    /// following the fields the leaf chose. That costs left leaves times right nodes where most
    /// right subtrees hold no agreeing leaf, and one run per right node below a long left chain:
    /// steps or runs quadratic in m on the families of plan row TRIVIAL-walk-branches (brief,
    /// wide, same, ne and their mirrors; at m = 128 and 1024: 26 to 72 times the
    /// instructions). Here the walk goes over pairs of nodes (u, v), one of each side:
    /// - it follows each side's fields the other side's path already fixed;
    /// - a leaf against a subtree is the subtree's `KeyIndex` walk under its entry for the
    ///   leaf's key (O(min(chosen, needed) log) a check at each branch point);
    /// - on a field both test it enters the two children of each choice together, only for the
    ///   choices whose children may hold a pair (a list made once for each pair of classes; at a
    ///   node split against a node of that field, the lists of all the pairs of classes the
    ///   split node's children of the field make with it are made together);
    /// - on different fields it splits the side whose field the other side tests further down
    ///   (`Reach::first`), so the side tested sooner is split by the other side's fields first;
    /// - children are walked by class (`Tree::classes`): when the other side never tests the
    ///   split field, a child whose subtree holds the same keyed paths on the fields the other
    ///   tree tests as a sibling's that gave no pair is skipped; children with no leaf of a key
    ///   the other tree has are never entered;
    /// - sibling leaves of one key walk the other side once, with the split field held to the
    ///   set of their choices (`Tree::groups`), after the node's other children, so that the
    ///   engine's lists of the fields above do not start with the group's pairs.
    ///
    /// Measured (instructions of the default report, m = 128 and 1024): brief, wide, same, ne and
    /// their mirrors grow 7.5 to 7.8 times for a limit of 12.6, at most 1.3 times the naive walk
    /// (wide mirrored, 29.4 against 22.9 million at 1024); d = 50 and 400: 5 d^2 + 10 d steps
    /// and 3 d^2 + d runs, 5.2 and 252 million instructions (naive 6.9 and 510), 49 times for a
    /// limit of 108 (d^2 log d). Cost: O(S log S) for the trees, S the paths' choices,
    /// O(E log^2 E) for an index, built only when a lookup first needs it, O(N log N) for the
    /// classes, groups and depth tables of the N nodes, the steps, then O(R + D) for the engine's
    /// lists of the R runs. On the families of plan row TRIVIAL-walk-picks (`scaling::picks`),
    /// m^2 pairs of `h` nodes of distinct pairs of classes, the steps are 5 to 6.4 times the
    /// pairs. When the split node's nodes of the field lie deeper, below fields the other tree
    /// never tests (`q_j(h(..))`, `deep`), the lists are made together for that whole frontier
    /// (plan row TRIVIAL-walk-frontier): `deep` and `deeper` at m = 64 take 180626 and 255378
    /// steps for 25090 and 33410 pairs, where one list per pair of classes took 446482 and
    /// 521234, m^3. Not proved: a bound of the steps by pairs plus tree size on every tree; a
    /// way through a field both trees test is split, not batched. Structural trigger: an atom
    /// whose sides share a field. Tests:
    /// `scaling::a_shared_field_atom_scales`, `scaling::a_shared_field_atom_with_cut_subtrees_scales`,
    /// `scaling::the_shared_field_families_scale`, `scaling::the_joint_splits_scale`,
    /// `scaling::the_picks_scale`, with `brute`, `scaling::the_picks_agree_with_brute_force`,
    /// `scaling::the_frontier_agrees_with_brute_force` and the corpus for the verdicts;
    /// COMPLEXITY.md C32; plan rows TRIVIAL-shared-atom, TRIVIAL-walk-index,
    /// TRIVIAL-walk-branches, TRIVIAL-walk-picks, TRIVIAL-walk-frontier.
    fn pair_form(&self, a: &Atom, lf: &[usize], rf: &[usize]) -> PairForm {
        let mut scope = Vec::with_capacity(lf.len() + rf.len());
        scope.extend_from_slice(lf);
        scope.extend_from_slice(rf);
        scope.sort_unstable();
        scope.dedup();
        let key = |flip: bool| {
            move |s: Sym| match (a.rel, s) {
                (Rel::Eq, _) => Some(s),
                (Rel::Ne, Sym::Const(c)) => Some(Sym::Const(if flip { 1 - c } else { c })),
                (Rel::Ne, Sym::Var(_)) => None,
            }
        };
        let left = self.tree(a.lhs, &scope, key(false));
        let right = self.tree(a.rhs, &scope, key(true));
        let trees = [&left, &right];
        // Complexity tradeoff: an index costs O(E log^2 E) for its E entries, and E is bounded
        // only by the leaves' depths (a chain of d nodes above k keys has d k entries), while
        // the walk may never look a key up in one of the trees (one whose leaves all meet the
        // other side's leaves in joint splits: m^2 entries for a walk of O(m) pairs). So each
        // index is built at the walk's first lookup in it; whether the other tree has a key at
        // all is read from a sorted list of its keys, O(N log N) to build, O(log K) a lookup.
        let built = [OnceCell::new(), OnceCell::new()];
        let index = |side: usize| built[side].get_or_init(|| trees[side].index());
        let reach = [left.reach(scope.len()), right.reach(scope.len())];
        let keys = [left.keys(), right.keys()];
        let class = [
            left.classes(&right, &keys[1], scope.len()),
            right.classes(&left, &keys[0], scope.len()),
        ];
        let groups = [left.groups(&keys[1]), right.groups(&keys[0])];
        // For a left class and a right class whose nodes test one field: the choices whose two
        // children may hold a pair, in `joint_kids[joint[&(left class, right class)]]`, sorted.
        let mut joint: HashMap<(usize, usize), std::ops::Range<usize>> = HashMap::new();
        let mut joint_kids: Vec<Choice> = Vec::new();
        // For a node split against nodes of a field: the classes of its children of that field,
        // in `kin_class[kin_classes[..]]`, and their live children by choice and key (`Kin`),
        // sorted, in `kin[kin_records[..]]`.
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        enum Kin {
            /// A child that tests a field.
            Inner,
            /// A leaf of this key.
            Leaf(Sym),
            /// A child that tests a field, with a leaf of this key below.
            Below(Sym),
        }
        // For a node split against nodes of a field: the classes of its frontier of that field
        // (`kin_class`) and of the nodes passed on the way (`kin_path`).
        type Frontier = (std::ops::Range<usize>, std::ops::Range<usize>);
        let mut kin_classes: HashMap<(usize, usize, usize), Frontier> = HashMap::new();
        let mut kin_path: Vec<usize> = Vec::new();
        // The (side, class of the other side's node, class of a node) whose lists an outer batch
        // already decided, the node lying on the way from that batch's node to its frontier.
        let mut covered: HashSet<(usize, usize, usize)> = HashSet::new();
        let mut kin_records: HashMap<(usize, usize, usize), std::ops::Range<usize>> =
            HashMap::new();
        let mut kin: Vec<(Choice, Kin, usize)> = Vec::new();
        let mut kin_class: Vec<(usize, usize)> = Vec::new();
        // The (side, class of the other side's node, node) whose lists were made together.
        let mut batched: HashSet<(usize, usize, usize)> = HashSet::new();
        let mut found: Vec<(usize, Choice)> = Vec::new();
        enum Step {
            /// A node of each side, reached by the choices fixed so far.
            Prod(usize, usize),
            /// A node of side `.0` (0 left, 1 right) and its entry for the key of the other
            /// side's leaf, or of the group of leaves held (`held`).
            One(usize, usize, usize),
            /// The children of `u` (`side` 0) or `v` (`side` 1) on field `s`: first its
            /// children in the class order of `class[side]` from place `i`, then its groups of
            /// leaves from group `g`; `start` the pairs before the node, `last` the choice and
            /// first pair of the child entered last.
            Split {
                s: usize,
                u: usize,
                v: usize,
                side: usize,
                start: usize,
                g: usize,
                i: usize,
                last: Option<(Choice, usize)>,
            },
            /// The children of `u` and `v`, which both test field `s`, entered together: the
            /// choices `joint_kids[list]`, from place `i`.
            Joint {
                s: usize,
                u: usize,
                v: usize,
                start: usize,
                list: std::ops::Range<usize>,
                i: usize,
                last: Option<(Choice, usize)>,
            },
            /// The children of entry `e` of side `side`'s node of field `s` that a leaf of its
            /// key below them, from place `i` of `index(side).kids`.
            OneKids {
                side: usize,
                s: usize,
                e: usize,
                start: usize,
                i: usize,
                last: Option<(Choice, usize)>,
            },
            /// The same, for a node of the field `held` holds: only the children of the held
            /// choices, and no run of the node (the group's split writes it).
            HeldKids {
                side: usize,
                s: usize,
                e: usize,
                i: usize,
                last: Option<(Choice, usize)>,
            },
            /// The end of a group's walk: field `.0` is no longer held.
            Unhold(usize),
        }
        // The choices fixed by the paths of both sides so far, by place, and the places fixed.
        let mut fixed = vec![MENTION; scope.len()];
        let mut chosen: Vec<usize> = Vec::new();
        // While a group of leaves walks the other side: the field split (not fixed: a pair takes
        // one choice of it for each member), its side, and the members in `groups[side].member`;
        // `held_on` is false while a node of that field below is split by its members.
        let mut held: Option<(usize, usize, std::ops::Range<usize>)> = None;
        let mut held_on = false;
        // Whether entry `e` agrees with the choices so far and, while a group is held, needs
        // no choice of its field outside the members.
        let fits = |ix: &KeyIndex,
                    e: usize,
                    fixed: &[Choice],
                    chosen: &[usize],
                    held: Option<(usize, &[Choice])>| {
            ix.agrees(e, fixed, chosen)
                && held.is_none_or(|(s, member)| {
                    let needs = &ix.needs[ix.needs_at[e].clone()];
                    needs
                        .binary_search_by_key(&s, |&(p, _)| p)
                        .ok()
                        .is_none_or(|i| member.binary_search(&needs[i].1).is_ok())
                })
        };
        let (mut pairs, mut runs, mut steps) = (0, Vec::new(), 0u64);
        let mut stack = vec![Step::Prod(0, 0)];
        while let Some(step) = stack.pop() {
            steps += 1;
            let held_now = held
                .as_ref()
                .filter(|_| held_on)
                .map(|(s, side, r)| (*s, &groups[*side].member[r.clone()]));
            match step {
                Step::Prod(mut u, mut v) => {
                    // Follow the fields the other side already chose.
                    for (n, t) in [(&mut u, &left), (&mut v, &right)] {
                        while t.test[*n] != NONE && fixed[t.test[*n]] != MENTION {
                            *n = t.kid[t.kid_at[*n].start + fixed[t.test[*n]] as usize];
                            steps += 1;
                        }
                    }
                    let (fu, fv) = (left.test[u], right.test[v]);
                    if fu == NONE || fv == NONE {
                        // A leaf against a subtree: the subtree's walk under its entry for the
                        // leaf's key, if every path to that key agrees with the choices so far.
                        let (side, n, k) = if fu == NONE {
                            (1, v, left.key[u])
                        } else {
                            (0, u, right.key[v])
                        };
                        if let Some(e) = k.and_then(|k| index(side).entry(n, k))
                            && index(side).agrees(e, &fixed, &chosen)
                        {
                            stack.push(Step::One(side, n, e));
                        }
                        continue;
                    }
                    if fu == fv {
                        // Both test one field: enter the two children of each choice together,
                        // for the choices whose children may hold a pair. A class fixes, choice
                        // by choice, its children's classes, so which those are depends only on
                        // the two classes and is worked out once for each pair of classes.
                        //
                        // Complexity tradeoff: splitting one side and letting the other follow
                        // examines every live child of the split side at each pair of nodes, m^3
                        // steps for m^2 pairs of nodes of m children each holding O(1) pairs
                        // (`s(h(x0..xm)^m, y0..ym) == t(h(y0..ym)^m, x0..xm)`). Here a pair of
                        // nodes costs a hash lookup and one step per choice entered; a pair of
                        // classes costs, once, the smaller side's live children, each an O(1)
                        // test or an O(log E) index lookup.
                        let classes = (class[0].number[u], class[1].number[v]);
                        let list = match joint.get(&classes) {
                            Some(list) => list.clone(),
                            None => {
                                let begin = joint_kids.len();
                                let side = usize::from(class[1].live[v] < class[0].live[u]);
                                let n = [u, v][side];
                                let at = trees[side].kid_at[n].start;
                                let (lu, rv) = (left.kid_at[u].start, right.kid_at[v].start);
                                for &c in &class[side].order[at..at + class[side].live[n]] {
                                    let (a, b) =
                                        (left.kid[lu + c as usize], right.kid[rv + c as usize]);
                                    let may = class[0].number[a] != DEAD
                                        && class[1].number[b] != DEAD
                                        && match (left.test[a] == NONE, right.test[b] == NONE) {
                                            (true, true) => left.key[a] == right.key[b],
                                            (true, false) => left.key[a]
                                                .is_some_and(|k| index(1).entry(b, k).is_some()),
                                            (false, true) => right.key[b]
                                                .is_some_and(|k| index(0).entry(a, k).is_some()),
                                            (false, false) => true,
                                        };
                                    if may {
                                        joint_kids.push(c);
                                    }
                                }
                                steps += class[side].live[n] as u64;
                                joint_kids[begin..].sort_unstable();
                                joint.insert(classes, begin..joint_kids.len());
                                begin..joint_kids.len()
                            }
                        };
                        chosen.push(fu);
                        stack.push(Step::Joint {
                            s: fu,
                            u,
                            v,
                            start: pairs,
                            list,
                            i: 0,
                            last: None,
                        });
                        continue;
                    }
                    // Split the side whose field the other side tests further down (or never),
                    // so that the side tested sooner is split by the other side's fields before
                    // it is walked alone.
                    let side = usize::from(reach[0].first(fv, u) > reach[1].first(fu, v));
                    let s = [fu, fv][side];
                    // The other side's node w meets each child of the split node n that tests
                    // its field f: make the lists of all those pairs of classes at once.
                    //
                    // Complexity tradeoff: one by one, each pair of classes (class of w, class
                    // of a child b) costs min(live w, live b), so w against m children of m
                    // classes, each with m live children, costs m^2, and m such w cost m^3 for
                    // m^2 pairs of nodes (plan row TRIVIAL-walk-picks). Together, the children
                    // of n's children of f are indexed once for (n, f) by choice and key (`Kin`),
                    // O(K log K) for their K records, each internal child with the keys below
                    // it that the other tree has; then each live child of w is looked up in
                    // that index, O(log K) each plus the records it finds.
                    // A leaf below a child of w meets the index by its key; an internal child
                    // of w meets the leaves at its choice through the fewer of the keys below
                    // it and those leaves, at most one leaf per class of b live at that choice.
                    // So a batch costs O((live w + its choices kept + the smaller of the keys
                    // below and the leaves at each internal choice of w) log K), never more
                    // than the lists of all of n's classes of f made one by one, times a log;
                    // it runs only when those not made yet would cost one by one (`apart`)
                    // more than live w. The index is built once for (n, f) and only when
                    // a batch first needs it, with one record per entry of a node of n's
                    // frontier of f (below), and a node lies in the frontier of at most two such
                    // n (argued below), so all these indexes together cost
                    // O((N + E) log(N + E)) for the N nodes and E index entries.
                    // Counting the classes of n costs its children, once for (n, f), and the
                    // classes, once for (class of w, n): the split that follows pays as much.
                    //
                    // The frontier (plan row TRIVIAL-walk-frontier): w meets not only n's children
                    // of f but every node of f below n reached through nodes whose fields w's
                    // tree never tests, since the walk splits such a node, not w, and keeps w,
                    // until it meets the node of f (`Reach::first` is `usize::MAX` on w's side).
                    // So the batch takes that whole frontier, and the nodes passed on the way are
                    // marked covered for w's class: their own frontiers lie inside n's, so their
                    // splits against a node of w's class make no batch of their own. Before,
                    // with `q_j(h(..))` below n, each pair of classes made its list alone, m^3
                    // steps for m^2 pairs (`deep` of `scaling::picks`). Such a node is of one
                    // class with a sibling exactly when they hold the same set of children's
                    // classes, so the way is walked once for each class (a visited set), and
                    // the walk enters at least one node of each of those classes against w: the
                    // gather costs no more than the split that follows. A node of the way is met
                    // against w only by splitting its parent, which is then batched or covered
                    // for w's class, or by a joint step at a parent of a field both trees test;
                    // so the frontiers that hold a node are those of the nearest node above the
                    // way and of the way's first node, two (argued, not measured on all trees).
                    // A batch is never needed for the answer: a list it does not make is made
                    // alone when the walk reaches its pair. Not batched: a way through a field
                    // w's tree tests, where the walk splits w instead; on random small atoms the
                    // frontier costs up to 10% more steps than the children alone (inputs of
                    // `scaling::the_frontier_agrees_with_brute_force`: at most 20 more steps).
                    let (o, n, w) = (1 - side, [u, v][side], [u, v][1 - side]);
                    let (f, a) = (trees[o].test[w], class[o].number[w]);
                    if !covered.contains(&(side, a, class[side].number[n]))
                        && batched.insert((side, a, n))
                    {
                        let (t, cl) = (trees[side], &class[side]);
                        let never_tested =
                            |s: usize| reach[o].at_start[s] == reach[o].at_start[s + 1];
                        let (classes, path) = kin_classes
                            .entry((side, n, f))
                            .or_insert_with(|| {
                                let (start, path_start) = (kin_class.len(), kin_path.len());
                                let mut todo = vec![n];
                                let mut seen: HashSet<usize> = HashSet::new();
                                while let Some(x) = todo.pop() {
                                    for &b in &t.kid[t.kid_at[x].clone()] {
                                        let (s, number) = (t.test[b], cl.number[b]);
                                        if s == NONE || number == DEAD {
                                            continue;
                                        }
                                        if s == f {
                                            kin_class.push((number, b));
                                        } else if never_tested(s) && seen.insert(number) {
                                            kin_path.push(number);
                                            todo.push(b);
                                        }
                                    }
                                    steps += t.kid_at[x].len() as u64;
                                }
                                kin_class[start..].sort_unstable();
                                let mut j = start;
                                for i in start..kin_class.len() {
                                    if j == start || kin_class[i].0 != kin_class[j - 1].0 {
                                        kin_class[j] = kin_class[i];
                                        j += 1;
                                    }
                                }
                                kin_class.truncate(j);
                                (start..kin_class.len(), path_start..kin_path.len())
                            })
                            .clone();
                        for &x in &kin_path[path] {
                            covered.insert((side, a, x));
                        }
                        let key = |b: usize| if side == 1 { (a, b) } else { (b, a) };
                        // Per pair of classes, the smaller side's live children; together, the
                        // other side's node's children once and a lookup for each.
                        steps += classes.len() as u64;
                        let apart: usize = kin_class[classes.clone()]
                            .iter()
                            .filter(|&&(b, _)| !joint.contains_key(&key(b)))
                            .map(|&(_, bn)| class[o].live[w].min(cl.live[bn]))
                            .sum();
                        if apart > class[o].live[w] {
                            let records = kin_records
                                .entry((side, n, f))
                                .or_insert_with(|| {
                                    let start = kin.len();
                                    for &(bc, b) in &kin_class[classes.clone()] {
                                        let at = t.kid_at[b].start;
                                        for &c in &cl.order[at..at + cl.live[b]] {
                                            let k = t.kid[at + c as usize];
                                            if t.test[k] == NONE {
                                                let key = t.key[k].expect("a live leaf has a key");
                                                kin.push((c, Kin::Leaf(key), bc));
                                            } else {
                                                kin.push((c, Kin::Inner, bc));
                                                let ix = index(side);
                                                for e in ix.below[k].clone() {
                                                    if keys[o].binary_search(&ix.key[e]).is_ok() {
                                                        kin.push((c, Kin::Below(ix.key[e]), bc));
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    kin[start..].sort_unstable();
                                    steps += (kin.len() - start) as u64;
                                    start..kin.len()
                                })
                                .clone();
                            let (records, classes) = (&kin[records], &kin_class[classes]);
                            found.clear();
                            let find = |c: Choice, k: Kin| {
                                let lo = records.partition_point(|&(rc, rk, _)| (rc, rk) < (c, k));
                                let hi = lo
                                    + records[lo..]
                                        .partition_point(|&(rc, rk, _)| (rc, rk) == (c, k));
                                lo..hi
                            };
                            let at = trees[o].kid_at[w].start;
                            for &c in &class[o].order[at..at + class[o].live[w]] {
                                let k = trees[o].kid[at + c as usize];
                                steps += 1;
                                if trees[o].test[k] == NONE {
                                    let key = trees[o].key[k].expect("a live leaf has a key");
                                    for r in [find(c, Kin::Leaf(key)), find(c, Kin::Below(key))] {
                                        found.extend(records[r].iter().map(|&(_, _, b)| (b, c)));
                                    }
                                    continue;
                                }
                                let r = find(c, Kin::Inner);
                                found.extend(records[r].iter().map(|&(_, _, b)| (b, c)));
                                // Leaves of the split side's children at `c` with a key below
                                // `k`: the fewer of those leaves and of the keys below `k`.
                                let lo = find(c, Kin::Inner).end;
                                let hi = lo
                                    + records[lo..].partition_point(|&(rc, rk, _)| {
                                        rc == c && matches!(rk, Kin::Leaf(_))
                                    });
                                let ix = index(o);
                                if ix.below[k].len() < hi - lo {
                                    for e in ix.below[k].clone() {
                                        let r = find(c, Kin::Leaf(ix.key[e]));
                                        steps += 1;
                                        found.extend(records[r].iter().map(|&(_, _, b)| (b, c)));
                                    }
                                } else {
                                    for &(_, rk, b) in &records[lo..hi] {
                                        steps += 1;
                                        if let Kin::Leaf(key) = rk
                                            && ix.entry(k, key).is_some()
                                        {
                                            found.push((b, c));
                                        }
                                    }
                                }
                            }
                            found.sort_unstable();
                            let mut i = 0;
                            for &(b, _) in classes {
                                let j = i + found[i..].partition_point(|&(fb, _)| fb == b);
                                if let Entry::Vacant(slot) = joint.entry(key(b)) {
                                    let begin = joint_kids.len();
                                    joint_kids.extend(found[i..j].iter().map(|&(_, c)| c));
                                    slot.insert(begin..joint_kids.len());
                                }
                                i = j;
                            }
                        }
                    }
                    chosen.push(s);
                    stack.push(Step::Split {
                        s,
                        u,
                        v,
                        side,
                        start: pairs,
                        g: 0,
                        i: 0,
                        last: None,
                    });
                }
                Step::Joint {
                    s,
                    u,
                    v,
                    start,
                    list,
                    i,
                    last,
                } => {
                    if let Some((c, first)) = last
                        && pairs > first
                    {
                        runs.push((s, c, first, pairs));
                    }
                    if i == list.len() {
                        fixed[s] = MENTION;
                        chosen.pop();
                        if pairs > start {
                            runs.push((s, MENTION, start, pairs));
                        }
                        continue;
                    }
                    let c = joint_kids[list.start + i];
                    fixed[s] = c;
                    let (a, b) = (
                        left.kid[left.kid_at[u].start + c as usize],
                        right.kid[right.kid_at[v].start + c as usize],
                    );
                    stack.push(Step::Joint {
                        s,
                        u,
                        v,
                        start,
                        list,
                        i: i + 1,
                        last: Some((c, pairs)),
                    });
                    stack.push(Step::Prod(a, b));
                }
                Step::Split {
                    s,
                    u,
                    v,
                    side,
                    start,
                    g,
                    mut i,
                    last,
                } => {
                    let n = [u, v][side];
                    let at = trees[side].kid_at[n].clone();
                    let gat = groups[side].at[n].clone();
                    if let Some((c, first)) = last {
                        if pairs > first {
                            runs.push((s, c, first, pairs));
                        } else if !reach[1 - side].occurs(s, [u, v][1 - side]) {
                            // The other members of the class differ from this child only in the
                            // choice of `s`, which the other side never reads: no pair either.
                            i = class[side].end[at.start + i - 1] - at.start;
                        }
                    }
                    // The groups' leaves are walked after the other children; a group is a whole class.
                    while i < class[side].live[n]
                        && groups[side].grouped[at.start + class[side].order[at.start + i] as usize]
                    {
                        steps += 1;
                        i = class[side].end[at.start + i] - at.start;
                    }
                    if i >= class[side].live[n] && g < gat.len() {
                        // Leaves of one key: one walk of the other side under its entry for the
                        // key, with `s` held to their choices, for all of them.
                        let member = groups[side].group[gat.start + g].clone();
                        let leaf =
                            trees[side].kid[at.start + groups[side].member[member.start] as usize];
                        let (o, w) = (1 - side, [u, v][1 - side]);
                        stack.push(Step::Split {
                            s,
                            u,
                            v,
                            side,
                            start,
                            g: g + 1,
                            i,
                            last: None,
                        });
                        fixed[s] = MENTION;
                        chosen.pop();
                        if let Some(e) = trees[side].key[leaf].and_then(|k| index(o).entry(w, k))
                            && fits(
                                index(o),
                                e,
                                &fixed,
                                &chosen,
                                Some((s, &groups[side].member[member.clone()])),
                            )
                        {
                            held = Some((s, side, member));
                            held_on = true;
                            stack.push(Step::Unhold(s));
                            stack.push(Step::One(o, w, e));
                        } else {
                            chosen.push(s);
                        }
                        continue;
                    }
                    if i >= class[side].live[n] {
                        fixed[s] = MENTION;
                        chosen.pop();
                        if pairs > start {
                            runs.push((s, MENTION, start, pairs));
                        }
                        continue;
                    }
                    let c = class[side].order[at.start + i];
                    fixed[s] = c;
                    let kid = trees[side].kid[at.start + c as usize];
                    let (ku, kv) = if side == 0 { (kid, v) } else { (u, kid) };
                    stack.push(Step::Split {
                        s,
                        u,
                        v,
                        side,
                        start,
                        g,
                        i: i + 1,
                        last: Some((c, pairs)),
                    });
                    stack.push(Step::Prod(ku, kv));
                }
                Step::Unhold(s) => {
                    held = None;
                    held_on = false;
                    chosen.push(s);
                }
                Step::One(side, n, e) => {
                    let s = trees[side].test[n];
                    if s == NONE {
                        // One pair, or one for each member of the group held, each with its
                        // choice of the held field.
                        match held_now {
                            Some((h, member)) => {
                                for &c in member {
                                    pairs += 1;
                                    runs.push((h, c, pairs - 1, pairs));
                                }
                                steps += member.len() as u64;
                            }
                            None => pairs += 1,
                        }
                        continue;
                    }
                    let ix = index(side);
                    let kids = &ix.kids[ix.kids_at[e].clone()];
                    if fixed[s] == MENTION {
                        chosen.push(s);
                        if held_now.is_some_and(|(h, _)| h == s) {
                            held_on = false;
                            stack.push(Step::HeldKids {
                                side,
                                s,
                                e,
                                i: 0,
                                last: None,
                            });
                        } else {
                            stack.push(Step::OneKids {
                                side,
                                s,
                                e,
                                start: pairs,
                                i: 0,
                                last: None,
                            });
                        }
                    } else if let Ok(i) = kids.binary_search_by_key(&fixed[s], |&(c, _, _)| c)
                        && (kids.len() == 1 || fits(ix, kids[i].2, &fixed, &chosen, held_now))
                    {
                        // Inside a chain the chain start's needs already agreed; at a branch
                        // point each child starts a chain and is checked.
                        stack.push(Step::One(side, kids[i].1, kids[i].2));
                    }
                }
                Step::OneKids {
                    side,
                    s,
                    e,
                    start,
                    mut i,
                    last,
                } => {
                    if let Some((c, first)) = last
                        && pairs > first
                    {
                        runs.push((s, c, first, pairs));
                    }
                    let ix = index(side);
                    let kids = &ix.kids[ix.kids_at[e].clone()];
                    while i < kids.len()
                        && kids.len() > 1
                        && !fits(ix, kids[i].2, &fixed, &chosen, held_now)
                    {
                        steps += 1;
                        i += 1;
                    }
                    if i == kids.len() {
                        fixed[s] = MENTION;
                        chosen.pop();
                        if pairs > start {
                            runs.push((s, MENTION, start, pairs));
                        }
                        continue;
                    }
                    let (c, kid, kid_entry) = kids[i];
                    fixed[s] = c;
                    stack.push(Step::OneKids {
                        side,
                        s,
                        e,
                        start,
                        i: i + 1,
                        last: Some((c, pairs)),
                    });
                    stack.push(Step::One(side, kid, kid_entry));
                }
                Step::HeldKids {
                    side,
                    s,
                    e,
                    mut i,
                    last,
                } => {
                    if let Some((c, first)) = last
                        && pairs > first
                    {
                        runs.push((s, c, first, pairs));
                    }
                    let ix = index(side);
                    let kids = &ix.kids[ix.kids_at[e].clone()];
                    let (_, gside, member) = held.clone().expect("a group is held");
                    let member = &groups[gside].member[member];
                    fixed[s] = MENTION;
                    while i < kids.len()
                        && (member.binary_search(&kids[i].0).is_err()
                            || kids.len() > 1 && !ix.agrees(kids[i].2, &fixed, &chosen))
                    {
                        steps += 1;
                        i += 1;
                    }
                    if i == kids.len() {
                        chosen.pop();
                        held_on = true;
                        continue;
                    }
                    let (c, kid, kid_entry) = kids[i];
                    fixed[s] = c;
                    stack.push(Step::HeldKids {
                        side,
                        s,
                        e,
                        i: i + 1,
                        last: Some((c, pairs)),
                    });
                    stack.push(Step::One(side, kid, kid_entry));
                }
            }
        }
        PairForm {
            scope,
            pairs,
            runs,
            steps,
        }
    }
}

impl Theory {
    /// For an atom whose sides name a common field: the pairs of paths that agree, the runs
    /// that hold them, and the steps of the walk that numbered them; `None` for an atom split by
    /// end symbol.
    pub fn shared_atom_size(&self, a: &Atom) -> Option<(usize, usize, u64)> {
        match self.atom_form(a) {
            AtomForm::Pairs(form) => Some((form.pairs, form.runs.len(), form.steps)),
            AtomForm::Split { .. } | AtomForm::Never => None,
        }
    }
}

/// No node, place, list or pair.
const NONE: usize = usize::MAX;

/// The choice of a run of a node, holding the pairs whose cubes name its field; also no choice.
const MENTION: Choice = Choice::MAX;

/// The decision tree of one side of an atom, in preorder, so that a node's children come after
/// it. A node tests a field, by its place in the atom's scope, or is a leaf (`NONE`).
#[derive(Default)]
struct Tree {
    test: Vec<usize>,
    /// For each leaf, the key of the symbol it ends at.
    key: Vec<Option<Sym>>,
    /// For each node: its children, one for each choice of its field, in `kid`; none for a leaf.
    kid_at: Vec<std::ops::Range<usize>>,
    kid: Vec<usize>,
}

impl Tree {
    /// The keys of the leaves, sorted, each once: O(N log N) for the N nodes.
    fn keys(&self) -> Vec<Sym> {
        let mut keys: Vec<Sym> = self.key.iter().flatten().copied().collect();
        keys.sort_unstable();
        keys.dedup();
        keys
    }

    /// Where each field is tested: the end of each node's subtree in preorder, each node's
    /// depth, and for each place the nodes that test it, in order, with a sparse table of their
    /// depths, so that whether a subtree tests a field, and how deep below its root it first
    /// does, is a binary search and a lookup. O(N log N) for the N nodes.
    fn reach(&self, places: usize) -> Reach {
        let mut depth = vec![0; self.test.len()];
        for n in 0..self.test.len() {
            for &k in &self.kid[self.kid_at[n].clone()] {
                depth[k] = depth[n] + 1;
            }
        }
        let mut end = vec![0; self.test.len()];
        for n in (0..self.test.len()).rev() {
            end[n] = self.kid[self.kid_at[n].clone()]
                .iter()
                .map(|&k| end[k])
                .max()
                .unwrap_or(n + 1);
        }
        let mut at_start = vec![0; places + 1];
        for &s in self.test.iter().filter(|&&s| s != NONE) {
            at_start[s + 1] += 1;
        }
        for s in 0..places {
            at_start[s + 1] += at_start[s];
        }
        let mut next = at_start.clone();
        let mut at = vec![0; at_start[places]];
        for (n, &s) in self.test.iter().enumerate() {
            if s != NONE {
                at[next[s]] = n;
                next[s] += 1;
            }
        }
        // min_depth[j][i]: the least depth of at[i..i + 2^j]; a range within one place's nodes
        // is covered by two such spans.
        let mut min_depth = vec![at.iter().map(|&n| depth[n]).collect::<Vec<usize>>()];
        let mut span = 1;
        while 2 * span <= at.len() {
            let row = min_depth.last().expect("the first row");
            let next = (0..=at.len() - 2 * span)
                .map(|i| row[i].min(row[i + span]))
                .collect();
            min_depth.push(next);
            span *= 2;
        }
        Reach {
            end,
            depth,
            at_start,
            at,
            min_depth,
        }
    }

    /// Each node's choices grouped into classes of children with the same paths and keys, as
    /// far as the other tree can tell: a subtree is numbered by its shape, hash-consed from the
    /// last node, where a node of a field `other` never tests reads as the set of its children's
    /// numbers. Two children of one class hold the same keyed paths on the fields `other` tests.
    /// Children with no keyed leaf below (no pair below either) come last, after `live[n]`
    /// others, so that a split never enters them. O(N + C) hash lookups for the N nodes and C
    /// children.
    fn classes(&self, other: &Tree, keys: &[Sym], places: usize) -> Classes {
        #[derive(PartialEq, Eq, Hash)]
        enum Shape {
            Leaf(Sym),
            Test(usize, Vec<usize>),
            Any(Vec<usize>),
        }
        let mut tested = vec![false; places];
        for &s in other.test.iter().filter(|&&s| s != NONE) {
            tested[s] = true;
        }
        let mut number = vec![0; self.test.len()];
        let mut numbers: HashMap<Shape, usize> = HashMap::new();
        let mut live = vec![0; self.test.len()];
        let mut order = vec![0; self.kid.len()];
        let mut end = vec![0; self.kid.len()];
        let mut by_class: Vec<(usize, Choice)> = Vec::new();
        for n in (0..self.test.len()).rev() {
            // A leaf is numbered by its key alone, with no child to order.
            if self.test[n] == NONE {
                number[n] = match self.key[n].filter(|k| keys.binary_search(k).is_ok()) {
                    None => DEAD,
                    Some(k) => {
                        let next = numbers.len();
                        *numbers.entry(Shape::Leaf(k)).or_insert(next)
                    }
                };
                continue;
            }
            let at = self.kid_at[n].clone();
            by_class.clear();
            by_class.extend(
                self.kid[at.clone()]
                    .iter()
                    .enumerate()
                    .map(|(c, &k)| (number[k], c as Choice)),
            );
            by_class.sort_unstable();
            live[n] = by_class.partition_point(|&(k, _)| k != DEAD);
            number[n] = if live[n] == 0 {
                DEAD
            } else {
                let s = self.test[n];
                let shape = if tested[s] {
                    Shape::Test(s, self.kid[at.clone()].iter().map(|&k| number[k]).collect())
                } else {
                    // The sorted class numbers, each once.
                    let mut set: Vec<usize> = by_class.iter().map(|&(k, _)| k).collect();
                    set.dedup();
                    Shape::Any(set)
                };
                let next = numbers.len();
                *numbers.entry(shape).or_insert(next)
            };
            for (i, &(_, c)) in by_class.iter().enumerate() {
                order[at.start + i] = c;
            }
            for i in (0..by_class.len()).rev() {
                end[at.start + i] = if i + 1 < by_class.len() && by_class[i + 1].0 == by_class[i].0
                {
                    end[at.start + i + 1]
                } else {
                    at.start + i + 1
                };
            }
        }
        Classes {
            order,
            end,
            live,
            number,
        }
    }

    /// Each node's leaf children grouped by key: the groups of two or more leaves of one key
    /// (not `None`), each a sorted list of choices, and whether each child is in a group.
    /// O(C log C) for the C children.
    fn groups(&self, keys: &[Sym]) -> Groups {
        let mut groups = Groups {
            at: vec![0..0; self.test.len()],
            group: Vec::new(),
            member: Vec::new(),
            grouped: vec![false; self.kid.len()],
        };
        let mut leaves: Vec<(Sym, Choice)> = Vec::new();
        for n in 0..self.test.len() {
            let at = self.kid_at[n].clone();
            leaves.clear();
            leaves.extend(
                self.kid[at.clone()]
                    .iter()
                    .enumerate()
                    .filter_map(|(c, &k)| {
                        self.key[k]
                            .filter(|key| self.test[k] == NONE && keys.binary_search(key).is_ok())
                            .map(|key| (key, c as Choice))
                    }),
            );
            leaves.sort_unstable();
            let start = groups.group.len();
            let mut i = 0;
            while i < leaves.len() {
                let j = i + leaves[i..].partition_point(|&(k, _)| k == leaves[i].0);
                if j - i > 1 {
                    let first = groups.member.len();
                    for &(_, c) in &leaves[i..j] {
                        groups.member.push(c);
                        groups.grouped[at.start + c as usize] = true;
                    }
                    groups.group.push(first..groups.member.len());
                }
                i = j;
            }
            groups.at[n] = start..groups.group.len();
        }
        groups
    }
    /// The tree indexed by the keys of its leaves (`KeyIndex`). The children of a node come
    /// after it, so one pass from the last node builds each node's entries from its children's:
    /// O(E log E) for the E entries, which the leaves' depths bound. The lists of choices each
    /// chain start needs hold O(E log E) choices in all: a branch point copies at most its
    /// smallest child's list, and a leaf's entry lies below O(log E) smallest children. Writing
    /// what a branch point's children have in common looks up at most twice the choices of all
    /// children but the largest, so O(E log^2 E) for the lists (`KeyIndex::needs`).
    fn index(&self) -> KeyIndex {
        let mut index = KeyIndex {
            below: vec![0..0; self.test.len()],
            key: Vec::new(),
            node: Vec::new(),
            kids_at: Vec::new(),
            kids: Vec::new(),
            needs_at: Vec::new(),
            needs: Vec::new(),
            common_at: Vec::new(),
        };
        // (key, choice, child, child's entry) for each key below each child of one node.
        let mut merged: Vec<(Sym, Choice, usize, usize)> = Vec::new();
        for n in (0..self.test.len()).rev() {
            let start = index.key.len();
            if self.test[n] == NONE {
                if let Some(k) = self.key[n] {
                    index.push_entry(k, n);
                }
            } else {
                merged.clear();
                for (c, &kid) in self.kid[self.kid_at[n].clone()].iter().enumerate() {
                    for e in index.below[kid].clone() {
                        merged.push((index.key[e], c as Choice, kid, e));
                    }
                }
                merged.sort_unstable_by_key(|&(k, c, _, _)| (k, c));
                for (i, &(k, c, kid, e)) in merged.iter().enumerate() {
                    if i == 0 || merged[i - 1].0 != k {
                        index.push_entry(k, n);
                    }
                    let last = index.kids_at.len() - 1;
                    index.kids.push((c, kid, e));
                    index.kids_at[last].end = index.kids.len();
                }
            }
            index.below[n] = start..index.key.len();
            // A node's entries with two or more children start their children's chains: write
            // what each chain start needs, then what all of them need.
            for e in start..index.key.len() {
                if index.kids_at[e].len() > 1 {
                    for i in index.kids_at[e].clone() {
                        index.write_needs(self, index.kids[i].2);
                    }
                    index.write_common(e);
                }
            }
        }
        // The root's entries start chains too.
        for e in index.below[0].clone() {
            index.write_needs(self, e);
        }
        index
    }
}

/// Where one side's tree tests each field (`Tree::reach`).
struct Reach {
    /// For each node, the end of its subtree in preorder, and its depth.
    end: Vec<usize>,
    depth: Vec<usize>,
    /// For each place, the nodes that test it, in order, in `at[at_start[s]..at_start[s + 1]]`.
    at_start: Vec<usize>,
    at: Vec<usize>,
    /// `min_depth[j][i]`: the least depth of the nodes `at[i..i + 2^j]`.
    min_depth: Vec<Vec<usize>>,
}

impl Reach {
    /// The nodes of the subtree of node `n` that test place `s`, as a range of `at`: O(log) by
    /// binary search.
    fn within(&self, s: usize, n: usize) -> std::ops::Range<usize> {
        let at = &self.at[self.at_start[s]..self.at_start[s + 1]];
        let i = at.partition_point(|&m| m < n);
        let j = i + at[i..].partition_point(|&m| m < self.end[n]);
        self.at_start[s] + i..self.at_start[s] + j
    }

    /// Whether the subtree of node `n` tests place `s`: O(log) by binary search.
    fn occurs(&self, s: usize, n: usize) -> bool {
        let at = &self.at[self.at_start[s]..self.at_start[s + 1]];
        let i = at.partition_point(|&m| m < n);
        i < at.len() && at[i] < self.end[n]
    }

    /// How far below node `n` its subtree first tests place `s` (the least depth of such a
    /// node, less `n`'s), or `usize::MAX` if it never does: O(log) by the sparse table.
    fn first(&self, s: usize, n: usize) -> usize {
        let r = self.within(s, n);
        if r.is_empty() {
            return usize::MAX;
        }
        let j = r.len().ilog2() as usize;
        let row = &self.min_depth[j];
        row[r.start].min(row[r.end - (1 << j)]) - self.depth[n]
    }
}

/// Each node's leaf children grouped by key (`Tree::groups`): node `n`'s groups are
/// `group[at[n]]`, each a range of `member`, its choices in order; `grouped` is aligned with
/// `Tree::kid`.
struct Groups {
    at: Vec<std::ops::Range<usize>>,
    group: Vec<std::ops::Range<usize>>,
    member: Vec<Choice>,
    grouped: Vec<bool>,
}

/// Each node's choices grouped into classes (`Tree::classes`): the choices in `order`, aligned
/// with `Tree::kid`, a class's members next to each other, and for each place in `order` the
/// end of its class.
struct Classes {
    order: Vec<Choice>,
    end: Vec<usize>,
    /// For each node, how many of its children have a keyed leaf below (the first in `order`).
    live: Vec<usize>,
    /// For each node, its class: two nodes of one class hold the same keyed paths on the
    /// fields the other tree tests.
    number: Vec<usize>,
}

/// The class number of the subtrees with no keyed leaf (`Tree::classes`), after all others.
const DEAD: usize = usize::MAX;

/// One side's tree indexed by the keys of its leaves, for the walk of `pair_form`. An entry is a
/// node and one key of a leaf below it. The entries of a node with two or more children of its
/// key below are branch points; a chain is a node whose parent entry is a branch point (or the
/// root), then each next node while the entry has one child of its key, down to a branch point
/// or a leaf. Each entry starting a chain holds the choices that every path from it to a leaf of
/// its key makes: the choices along its chain, then those every child of the branch point at
/// its end needs.
struct KeyIndex {
    /// For each node, its entries, by key.
    below: Vec<std::ops::Range<usize>>,
    /// For each entry, its key and its node.
    key: Vec<Sym>,
    node: Vec<usize>,
    /// For each entry, its children with a leaf of the key below, as `(choice, child, child's
    /// entry)` in `kids[kids_at[e]]`, by choice.
    kids_at: Vec<std::ops::Range<usize>>,
    kids: Vec<(Choice, usize, usize)>,
    /// For each entry that starts a chain, the choices every path from it to a leaf of its key
    /// makes, as `(place in scope, choice)` in `needs[needs_at[e]]`, by place; for each branch
    /// point, those all its children need, in `needs[common_at[e]]`. Empty elsewhere.
    needs_at: Vec<std::ops::Range<usize>>,
    needs: Vec<(usize, Choice)>,
    common_at: Vec<std::ops::Range<usize>>,
}

impl KeyIndex {
    fn push_entry(&mut self, k: Sym, n: usize) {
        self.key.push(k);
        self.node.push(n);
        self.kids_at.push(self.kids.len()..self.kids.len());
        self.needs_at.push(0..0);
        self.common_at.push(0..0);
    }

    /// The entry of node `n` for key `k`, if a leaf of that key is below `n`.
    fn entry(&self, n: usize, k: Sym) -> Option<usize> {
        let below = self.below[n].clone();
        self.key[below.clone()]
            .binary_search(&k)
            .ok()
            .map(|i| below.start + i)
    }

    /// Writes what chain start `e` needs: the choices down its chain, each node's one child of
    /// the key, then what the branch point at its end has in common. O(L log L) for the L
    /// choices written; each chain is written once.
    fn write_needs(&mut self, tree: &Tree, mut e: usize) {
        let start = self.needs.len();
        let head = e;
        while self.kids_at[e].len() == 1 {
            let (c, _, kid_entry) = self.kids[self.kids_at[e].start];
            self.needs.push((tree.test[self.node[e]], c));
            e = kid_entry;
        }
        // A path tests each field at most once, so the chain's places and those below are
        // distinct.
        self.needs.extend_from_within(self.common_at[e].clone());
        self.needs[start..].sort_unstable();
        self.needs_at[head] = start..self.needs.len();
    }

    /// Writes what every child of branch point `e` needs: the choices in all of their lists.
    /// The children's choices of `e`'s own field differ, so none of them is common. Each choice
    /// of the shortest list is looked up in the others: O(m c log L), m the shortest list's
    /// length, c the children and L the longest list's length.
    fn write_common(&mut self, e: usize) {
        let Self {
            kids_at,
            kids,
            needs_at,
            needs,
            common_at,
            ..
        } = self;
        let kids = &kids[kids_at[e].clone()];
        let shortest = kids
            .iter()
            .map(|&(_, _, k)| needs_at[k].clone())
            .min_by_key(|r| r.len())
            .expect("a branch point has two or more children");
        let start = needs.len();
        for i in shortest {
            let (s, c) = needs[i];
            let in_all = kids.iter().all(|&(_, _, k)| {
                let list = &needs[needs_at[k].clone()];
                list.binary_search_by_key(&s, |&(p, _)| p)
                    .is_ok_and(|j| list[j].1 == c)
            });
            if in_all {
                needs.push((s, c));
            }
        }
        common_at[e] = start..needs.len();
    }

    /// Whether the left leaf, whose choices are `fixed` by place with `chosen` the places it
    /// chose, agrees with every choice chain start `e` needs. The shorter of the two lists is
    /// read and each of its places looked up in the other: O(min(|chosen|, |needs|) log).
    fn agrees(&self, e: usize, fixed: &[Choice], chosen: &[usize]) -> bool {
        let needs = &self.needs[self.needs_at[e].clone()];
        if chosen.len() < needs.len() {
            chosen.iter().all(|&s| {
                needs
                    .binary_search_by_key(&s, |&(p, _)| p)
                    .ok()
                    .is_none_or(|i| needs[i].1 == fixed[s])
            })
        } else {
            needs
                .iter()
                .all(|&(s, c)| fixed[s] == MENTION || fixed[s] == c)
        }
    }
}

/// An atom whose sides name a common field, as `pair_form` writes it.
struct PairForm {
    scope: Vec<usize>,
    pairs: usize,
    /// `(place in scope, choice, start, end)`: the pairs `start..end` below one node of the
    /// walk, whose cubes name the field (`MENTION`), or below one child, whose cubes hold that
    /// choice.
    runs: Vec<(usize, Choice, usize, usize)>,
    steps: u64,
}

/// One side of a split atom: its fields, and its paths, each with the value of the end symbol it
/// ends at.
type Side = (Vec<usize>, Vec<(u32, Vec<(usize, Choice)>)>);

/// An atom as the engine checks it.
enum AtomForm {
    /// Sides that name no common field: an end symbol of `dom` values, and for each side its
    /// fields and its paths, each with the value of the end symbol it ends at.
    Split { dom: u32, left: Side, right: Side },
    /// Sides that name a common field.
    Pairs(PairForm),
    /// Sides that end at no common symbol.
    Never,
}

/// A variable and one of its choices.
type Lit = (usize, Choice);

/// The cubes of one constraint, as the engine reads them.
enum CubeSet {
    /// Each cube written out.
    Listed(Vec<Vec<(usize, Choice)>>),
    /// One side of a split atom: the end symbol, and the side's paths, each with the end
    /// symbol's value that completes it to a cube.
    Ended(usize, Vec<(u32, Vec<(usize, Choice)>)>),
}

impl CubeSet {
    fn len(&self) -> usize {
        match self {
            CubeSet::Listed(cubes) => cubes.len(),
            CubeSet::Ended(_, paths) => paths.len(),
        }
    }

    /// The choices in all the cubes.
    fn choices(&self) -> usize {
        match self {
            CubeSet::Listed(cubes) => cubes.iter().map(Vec::len).sum(),
            CubeSet::Ended(_, paths) => paths.iter().map(|(_, path)| path.len() + 1).sum(),
        }
    }

    /// Cube `i`: its choices of fields, sorted by field, then the end symbol's choice, if any,
    /// whose variable comes after every field.
    fn cube(&self, i: usize) -> (&[Lit], Option<Lit>) {
        match self {
            CubeSet::Listed(cubes) => (&cubes[i], None),
            CubeSet::Ended(end, paths) => (&paths[i].1, Some((*end, paths[i].0))),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Token {
    Name(String),
    Open,
    Close,
    Comma,
    Eq,
    Ne,
    And,
    Or,
    Not,
    Dot,
}

fn tokenize(s: &str) -> Vec<Token> {
    let mut out = Vec::new();
    let b = s.as_bytes();
    let mut i = 0;
    while i < b.len() {
        let two = s.get(i..i + 2);
        match (b[i], two) {
            (b' ', _) => i += 1,
            (b'(', _) => (out.push(Token::Open), i += 1).1,
            (b')', _) => (out.push(Token::Close), i += 1).1,
            (b',', _) => (out.push(Token::Comma), i += 1).1,
            (_, Some("==")) => (out.push(Token::Eq), i += 2).1,
            (_, Some("!=")) => (out.push(Token::Ne), i += 2).1,
            (_, Some("&&")) => (out.push(Token::And), i += 2).1,
            (_, Some("||")) => (out.push(Token::Or), i += 2).1,
            (b'!', _) => (out.push(Token::Not), i += 1).1,
            (b'.', _) => (out.push(Token::Dot), i += 1).1,
            (c, _) if c.is_ascii_alphanumeric() || c == b'_' => {
                let start = i;
                while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                    i += 1;
                }
                out.push(Token::Name(s[start..i].to_string()));
            }
            (c, _) => panic!("unexpected {:?} in {s:?}", c as char),
        }
    }
    out
}

/// A parser of the law bodies the tests write; its input is the tests' own text, so it
/// recurses on the nesting of that text.
struct Parser<'a> {
    theory: &'a mut Theory,
    /// Each binder's index by name.
    binders: HashMap<&'a str, usize>,
    tokens: &'a [Token],
    at: usize,
}

impl Parser<'_> {
    fn eat(&mut self, t: &Token) -> bool {
        let hit = self.tokens.get(self.at) == Some(t);
        if hit {
            self.at += 1;
        }
        hit
    }

    /// `a || b || ...`.
    fn or(&mut self) -> Formula {
        let mut out = vec![self.and()];
        while self.eat(&Token::Or) {
            out.push(self.and());
        }
        flatten(out, false)
    }

    /// `a && b && ...`.
    fn and(&mut self) -> Formula {
        let mut out = vec![self.unary()];
        while self.eat(&Token::And) {
            out.push(self.unary());
        }
        flatten(out, true)
    }

    /// `!a`, `(a)`, `(a).implies(b)` or an atom.
    fn unary(&mut self) -> Formula {
        if self.eat(&Token::Not) {
            return self.unary().negate();
        }
        if !self.eat(&Token::Open) {
            return Formula::Atom(self.atom());
        }
        let mut f = self.or();
        assert!(self.eat(&Token::Close), "expected ) at token {}", self.at);
        while self.eat(&Token::Dot) {
            assert_eq!(
                self.tokens.get(self.at),
                Some(&Token::Name("implies".to_string())),
                "expected implies at token {}",
                self.at
            );
            self.at += 1;
            assert!(self.eat(&Token::Open), "expected ( after implies");
            let then = self.or();
            assert!(
                self.eat(&Token::Close),
                "expected ) after the argument of implies"
            );
            f = flatten(vec![f.negate(), then], false);
        }
        f
    }

    fn atom(&mut self) -> Atom {
        let lhs = self.term();
        let rel = if self.eat(&Token::Eq) {
            Rel::Eq
        } else {
            assert!(
                self.eat(&Token::Ne),
                "expected == or != at token {}",
                self.at
            );
            Rel::Ne
        };
        let rhs = self.term();
        Atom { rel, lhs, rhs }
    }

    fn term(&mut self) -> usize {
        let Some(Token::Name(name)) = self.tokens.get(self.at).cloned() else {
            panic!("expected a name at token {}", self.at);
        };
        self.at += 1;
        let term = if let Some(v) = self.binders.get(name.as_str()).copied() {
            Term::Var(v)
        } else {
            let field = self
                .theory
                .field_id(&name)
                .unwrap_or_else(|| panic!("{name} is neither a binder nor a field"));
            let mut args = Vec::new();
            if self.eat(&Token::Open) {
                args.push(self.term());
                while self.eat(&Token::Comma) {
                    args.push(self.term());
                }
                assert!(
                    self.eat(&Token::Close),
                    "expected ) after the arguments of {name}"
                );
            }
            assert_eq!(
                args.len(),
                self.theory.fields[field].arity,
                "{name} applied to the wrong number of arguments"
            );
            Term::App { field, args }
        };
        self.theory.terms.push(term);
        self.theory.terms.len() - 1
    }
}

/// One `&&` (`and`) or `||` of `parts`, with nested ones of the same kind merged into it.
fn flatten(parts: Vec<Formula>, and: bool) -> Formula {
    let mut out = Vec::new();
    for p in parts {
        match (p, and) {
            (Formula::And(fs), true) | (Formula::Or(fs), false) => out.extend(fs),
            (p, _) => out.push(p),
        }
    }
    match (out.len(), and) {
        (1, _) => out.pop().expect("one part"),
        (_, true) => Formula::And(out),
        (_, false) => Formula::Or(out),
    }
}

/// The groups of fields that common laws link.
pub struct Split {
    /// Each group's fields in declaration order; groups ordered by their first field.
    pub groups: Vec<Vec<usize>>,
    /// Each group's laws in declaration order.
    pub group_laws: Vec<Vec<usize>>,
    /// The fields no law names.
    pub free: Vec<usize>,
    /// The laws that name no field.
    pub closed: Vec<usize>,
}

/// Splits the fields of `t` into the groups that common laws link, by a breadth-first search
/// over fields and laws with a visited set for each: O(fields + the sizes of the laws).
pub fn split(t: &Theory) -> Split {
    let scopes: Vec<Vec<usize>> = (0..t.laws.len()).map(|l| t.law_scope(l)).collect();
    let mut laws_of: Vec<Vec<usize>> = vec![Vec::new(); t.fields.len()];
    for (l, scope) in scopes.iter().enumerate() {
        for &f in scope {
            laws_of[f].push(l);
        }
    }
    let mut seen_field = vec![false; t.fields.len()];
    let mut seen_law = vec![false; t.laws.len()];
    let (mut groups, mut group_laws, mut free) = (Vec::new(), Vec::new(), Vec::new());
    for start in 0..t.fields.len() {
        if seen_field[start] {
            continue;
        }
        if laws_of[start].is_empty() {
            seen_field[start] = true;
            free.push(start);
            continue;
        }
        seen_field[start] = true;
        let (mut fields, mut laws) = (vec![start], Vec::new());
        let mut queue = VecDeque::from([start]);
        while let Some(f) = queue.pop_front() {
            for &l in &laws_of[f] {
                if seen_law[l] {
                    continue;
                }
                seen_law[l] = true;
                laws.push(l);
                for &g in &scopes[l] {
                    if !seen_field[g] {
                        seen_field[g] = true;
                        fields.push(g);
                        queue.push_back(g);
                    }
                }
            }
        }
        fields.sort_unstable();
        laws.sort_unstable();
        groups.push(fields);
        group_laws.push(laws);
    }
    let closed = (0..t.laws.len())
        .filter(|&l| scopes[l].is_empty())
        .collect();
    Split {
        groups,
        group_laws,
        free,
        closed,
    }
}

/// How a constraint is checked.
enum Check {
    /// The partial choices under which it holds, kept in the engine: one atom, or one side of
    /// an atom with its end symbol.
    Cubes,
    /// One atom whose sides name a common field, as pairs of paths kept in the engine.
    Pairs,
    /// Clause `k` of the law, an `||` of several atoms, checked whole once at most one of its
    /// fields is open.
    Whole(usize),
}

/// A constraint over variables: the fields, then one end symbol for each atom split in two.
struct Constraint {
    law: usize,
    scope: Vec<usize>,
    check: Check,
}

/// Why a choice was removed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Reason {
    /// The search chose another value for the field.
    Chosen,
    /// The law of this constraint leaves the value without support.
    Law(usize),
}

/// A field left with no choice, and the constraint that removed its last one; `field` is
/// `None` when a whole law fails with all its fields chosen.
#[derive(Clone, Copy, Debug)]
struct Conflict {
    constraint: usize,
    field: Option<usize>,
}

/// A change to the cubes and pairs, logged so that it can be undone.
enum Undo {
    /// Cube `.0` was removed.
    Cube(usize),
    /// Pair `.0` was removed.
    Pair(usize),
    /// The chain of lists watching pair `.0`, which started at list `.1`, was emptied.
    Head(usize, usize),
    /// `list` watched pair `wit`, in run `run`, before the next list `next`, and moved on.
    Watch {
        list: usize,
        wit: usize,
        run: usize,
        next: usize,
    },
}

/// A set of numbers below a bound, as bits in levels of 64-bit words: a bit of a level above
/// the first says whether a word of the level below has a bit set. Finding the next number in
/// the set, adding one and removing one take O(log_64 n).
struct LiveSet {
    levels: Vec<Vec<u64>>,
}

impl LiveSet {
    /// The set of every number below `n`.
    fn new(n: usize) -> Self {
        let mut levels = Vec::new();
        let mut bits = n;
        loop {
            let words = bits.div_ceil(64);
            let mut level = vec![u64::MAX; words];
            if !bits.is_multiple_of(64) {
                level[words - 1] = (1 << (bits % 64)) - 1;
            }
            levels.push(level);
            if words <= 1 {
                return LiveSet { levels };
            }
            bits = words;
        }
    }

    /// The least number in the set not below `x`, `NONE` when there is none.
    fn next(&self, x: usize) -> usize {
        let (mut i, mut lvl) = (x, 0);
        // Up until a word holds a bit at or after the place reached...
        loop {
            let w = i / 64;
            let Some(&word) = self.levels[lvl].get(w) else {
                return NONE;
            };
            let bits = word & (u64::MAX << (i % 64));
            if bits != 0 {
                i = w * 64 + bits.trailing_zeros() as usize;
                break;
            }
            lvl += 1;
            if lvl == self.levels.len() {
                return NONE;
            }
            i = w + 1;
        }
        // ...then down by the first bit of each word.
        while lvl > 0 {
            lvl -= 1;
            i = i * 64 + self.levels[lvl][i].trailing_zeros() as usize;
        }
        i
    }

    fn remove(&mut self, x: usize) {
        let mut i = x;
        for level in &mut self.levels {
            level[i / 64] &= !(1 << (i % 64));
            if level[i / 64] != 0 {
                return;
            }
            i /= 64;
        }
    }

    fn insert(&mut self, x: usize) {
        let mut i = x;
        for level in &mut self.levels {
            let was = level[i / 64];
            level[i / 64] |= 1 << (i % 64);
            if was != 0 {
                return;
            }
            i /= 64;
        }
    }
}

/// `LiveSet` against a list of flags, by random removals and insertions from sets that keep
/// every number, one in 8 and one in 50,000, at sizes on both sides of each level's width (64,
/// 64^2 and 64^3 numbers).
#[test]
fn the_live_set_finds_the_next_number() {
    let mut rng = zed_tests::instances::Rng::new(0x011f_e5e7);
    for n in [0, 1, 63, 64, 65, 4095, 4096, 4097, 262_143, 262_145] {
        for keep in [1, 8, 50_000] {
            let mut set = LiveSet::new(n);
            let mut flags = vec![true; n];
            for (x, flag) in flags.iter_mut().enumerate() {
                if rng.below(keep) != 0 {
                    set.remove(x);
                    *flag = false;
                }
            }
            for _ in 0..1000 {
                if n > 0 {
                    let x = rng.below(n);
                    if flags[x] {
                        set.remove(x);
                    } else {
                        set.insert(x);
                    }
                    flags[x] = !flags[x];
                }
                let from = rng.below(n + 2);
                let next = (from..n).find(|&y| flags[y]).unwrap_or(NONE);
                assert_eq!(set.next(from), next, "next from {from} of {n}");
            }
        }
    }
}

/// The constraints of a theory and the choices left for each variable, with a trail to undo them.
/// The variables are the fields, then the end symbols, which the search never chooses: once
/// every field of an atom is chosen, each side has one path left, which fixes its end symbol.
///
/// A constraint of cubes is kept arc consistent incrementally. A cube that does not mention a
/// variable of the scope allows every choice of it, so a choice is supported while some live cube
/// uses it or some live cube does not mention its variable. Each choice counts the live cubes that
/// use it, each variable of the scope the live cubes that mention it, and each constraint its live
/// cubes. Removing a choice removes the cubes that use it and lowers these counts; a choice left
/// unsupported is removed in turn. The variables of a constraint are kept ordered by how many
/// live cubes mention them, so those that every live cube mentions are found without a scan. So
/// along one descent of the search each cube is removed at most once, and the work is linear in
/// the cubes, however many choices the descent makes.
///
/// A constraint of pairs, an atom whose sides name a common field, is kept arc consistent the
/// same way without writing its cubes out. Its pairs are numbers, and for each slot and choice a
/// list of runs holds the pairs whose cubes use that choice; one more list holds the pairs whose
/// cubes do not mention the slot's variable. A choice is supported while its list or that last
/// one has a live pair. Each list watches one live pair, its first, and the lists watching a
/// pair are chained from it. Removing a choice removes the live pairs of its list, found by a
/// set of live pairs that gives the next live one in O(log P), and moves each list that watched
/// one of them forward to its next live pair; a list with none left removes the choices it
/// supported. Along one descent a list's watch only moves forward, so its runs are passed once:
/// the work is the runs plus the pairs and the moves, each O(log P), not the cubes' choices.
struct Engine<'t> {
    theory: &'t Theory,
    /// The number of values of each variable.
    dom: Vec<u32>,
    cons: Vec<Constraint>,
    cons_of_law: Vec<Vec<usize>>,
    /// The constraints of whole clauses each variable is in.
    whole_of: Vec<Vec<usize>>,
    /// For each whole clause, how many of its fields still have more than one choice.
    open: Vec<u32>,
    offset: Vec<usize>,
    alive: Vec<bool>,
    size: Vec<u32>,
    /// The removals, in order: variable, choice, reason, and the length of `undo` then.
    trail: Vec<(usize, Choice, Reason, usize)>,
    /// The removals of `trail` whose cubes and pairs are already removed.
    head: usize,
    /// Every cube: its constraint and its choices, each with its count in `count` and the slot
    /// of its variable.
    cube_con: Vec<usize>,
    cube_start: Vec<usize>,
    cube_lits: Vec<(usize, Choice, usize, usize)>,
    cube_alive: Vec<bool>,
    /// The removals undone in reverse to undo the removals of `trail`.
    undo: Vec<Undo>,
    /// The pairs of every constraint of pairs, numbered from that constraint's first, and
    /// which of them are live.
    pair_live: LiveSet,
    /// For each slot of a constraint of pairs (`NONE` for one of cubes), its first list: one for
    /// each choice of its variable, then the list of the pairs that do not mention it. A list is
    /// the runs of pairs `runs[list_at[l]..list_at[l + 1]]`, and `list_slot[l]` is its slot.
    slot_list: Vec<usize>,
    list_slot: Vec<usize>,
    list_at: Vec<usize>,
    runs: Vec<(usize, usize)>,
    /// For each list, the first live pair in it, `NONE` when there is none, the run that holds
    /// it, and the next list watching the same pair; for each pair, the first list watching it.
    wit: Vec<usize>,
    wit_run: Vec<usize>,
    wit_next: Vec<usize>,
    watch_head: Vec<usize>,
    /// For each variable, the constraints of pairs it is in, each with its slot there.
    pair_slots: Vec<Vec<(usize, usize)>>,
    /// Buffers of `kill_pairs`: the pairs it removed that lists watched, and the lists it left
    /// with no live pair.
    unwatched: Vec<usize>,
    emptied: Vec<usize>,
    /// For each choice of each variable, by index like `alive`: the cubes that use it, in
    /// `uses[uses_at[i]..uses_at[i + 1]]`.
    uses: Vec<usize>,
    uses_at: Vec<usize>,
    /// For each constraint of cubes and each choice of a variable in its scope: the live cubes
    /// that use it.
    count: Vec<u32>,
    /// A slot is a variable in the scope of a constraint of cubes or of pairs: its variable and
    /// the index in `count` of its first choice. `slots_of[c]` is the range of constraint `c`.
    slot_var: Vec<(usize, usize)>,
    slots_of: Vec<std::ops::Range<usize>>,
    /// For each slot, the live cubes of its constraint that mention its variable.
    mention: Vec<u32>,
    /// For each constraint, its live cubes.
    live: Vec<u32>,
    /// The slots of each constraint, in `slots_of[c]`, ordered by `mention`; `pos` is the
    /// place of each slot in `order`. `bin[bin_of[c] + m]` is the first place in `order` of a
    /// slot of `c` with `mention` at least `m`, for `m` up to the cubes of `c` plus one.
    order: Vec<usize>,
    pos: Vec<usize>,
    bin: Vec<usize>,
    bin_of: Vec<usize>,
    /// The slots of the cube being removed, marked while it is.
    marked: Vec<bool>,
    queue: VecDeque<usize>,
    queued: Vec<bool>,
    /// The work done, for the tests: cubes removed and clauses checked.
    work: u64,
}

impl<'t> Engine<'t> {
    fn new(theory: &'t Theory) -> Self {
        let mut cons = Vec::new();
        let mut dom: Vec<u32> = theory.fields.iter().map(|f| choices(f.arity)).collect();
        let mut cubes_of: Vec<CubeSet> = Vec::new();
        let mut forms: Vec<Option<PairForm>> = Vec::new();
        let mut push = |cons: &mut Vec<Constraint>, c: Constraint, cubes, form| {
            cons.push(c);
            cubes_of.push(cubes);
            forms.push(form);
        };
        for (l, law) in theory.laws.iter().enumerate() {
            for (k, clause) in law.cnf.iter().flatten().enumerate() {
                match clause.as_slice() {
                    [a] => match theory.atom_form(a) {
                        AtomForm::Pairs(form) if form.pairs > 0 => push(
                            &mut cons,
                            Constraint {
                                law: l,
                                scope: form.scope.clone(),
                                check: Check::Pairs,
                            },
                            CubeSet::Listed(Vec::new()),
                            Some(form),
                        ),
                        // No pair: no cube, so every choice of the scope is removed at the start.
                        AtomForm::Pairs(_) | AtomForm::Never => push(
                            &mut cons,
                            Constraint {
                                law: l,
                                scope: theory.atom_scope(a),
                                check: Check::Cubes,
                            },
                            CubeSet::Listed(Vec::new()),
                            None,
                        ),
                        AtomForm::Split {
                            dom: values,
                            left,
                            right,
                        } => {
                            let end = dom.len();
                            dom.push(values);
                            for (mut scope, paths) in [left, right] {
                                scope.push(end);
                                push(
                                    &mut cons,
                                    Constraint {
                                        law: l,
                                        scope,
                                        check: Check::Cubes,
                                    },
                                    CubeSet::Ended(end, paths),
                                    None,
                                );
                            }
                        }
                    },
                    _ => push(
                        &mut cons,
                        Constraint {
                            law: l,
                            scope: theory.atoms_scope(clause),
                            check: Check::Whole(k),
                        },
                        CubeSet::Listed(Vec::new()),
                        None,
                    ),
                }
            }
        }
        let mut offset = Vec::with_capacity(dom.len() + 1);
        let mut total = 0;
        for &d in &dom {
            offset.push(total);
            total += d as usize;
        }
        offset.push(total);
        // The tables below are made at their final lengths, counted first, so that building
        // them allocates each once, in proportion to the cubes' choices.
        let of_cubes = || (0..cons.len()).filter(|&c| matches!(cons[c].check, Check::Cubes));
        let n_slots: usize = of_cubes().map(|c| cons[c].scope.len()).sum();
        let n_cubes: usize = of_cubes().map(|c| cubes_of[c].len()).sum();
        let n_lits: usize = of_cubes().map(|c| cubes_of[c].choices()).sum();
        let n_bins: usize = of_cubes().map(|c| cubes_of[c].len() + 2).sum();
        let mut cons_of_law = vec![Vec::new(); theory.laws.len()];
        let mut whole_of = vec![Vec::new(); dom.len()];
        let mut open = vec![0; cons.len()];
        let (mut slot_var, mut slots_of) =
            (Vec::with_capacity(n_slots), Vec::with_capacity(cons.len()));
        let mut n_counts = 0;
        let (mut cube_con, mut cube_start, mut cube_lits) = (
            Vec::with_capacity(n_cubes),
            Vec::with_capacity(n_cubes + 1),
            Vec::with_capacity(n_lits),
        );
        cube_start.push(0);
        let (mut live, mut bin, mut bin_of) = (
            vec![0; cons.len()],
            Vec::with_capacity(n_bins),
            Vec::with_capacity(cons.len()),
        );
        // The slot of each variable in the constraint being built.
        let mut slot = vec![usize::MAX; dom.len()];
        let (mut n_pairs, mut pair_slots) = (0, vec![Vec::new(); dom.len()]);
        let (mut slot_list, mut list_slot, mut list_at, mut runs) =
            (Vec::new(), Vec::new(), vec![0], Vec::new());
        for (c, con) in cons.iter().enumerate() {
            cons_of_law[con.law].push(c);
            let first_slot = slot_var.len();
            bin_of.push(bin.len());
            match con.check {
                Check::Whole(_) => {
                    for &f in &con.scope {
                        whole_of[f].push(c);
                    }
                    open[c] = con.scope.iter().filter(|&&f| dom[f] > 1).count() as u32;
                }
                Check::Cubes => {
                    for &f in &con.scope {
                        slot[f] = slot_var.len();
                        slot_var.push((f, n_counts));
                        slot_list.push(NONE);
                        n_counts += dom[f] as usize;
                    }
                    let cubes = &cubes_of[c];
                    for i in 0..cubes.len() {
                        cube_con.push(c);
                        let (path, end) = cubes.cube(i);
                        for &(f, v) in path.iter().chain(&end) {
                            let s = slot[f];
                            cube_lits.push((f, v, slot_var[s].1 + v as usize, s));
                        }
                        cube_start.push(cube_lits.len());
                    }
                    for &f in &con.scope {
                        slot[f] = usize::MAX;
                    }
                    live[c] = cubes.len() as u32;
                    // One bin for each count of mentions, 0 to the cubes, and one past the last.
                    bin.extend(std::iter::repeat_n(0, cubes.len() + 2));
                }
                Check::Pairs => {
                    let form = forms[c].take().expect("a constraint of pairs has its form");
                    let base = n_pairs;
                    n_pairs += form.pairs;
                    // The runs of each choice of each slot, gathered by a counting sort, then the
                    // gaps between the runs of the slot's nodes, which hold the pairs whose cubes
                    // do not mention it. Complexity tradeoff: a comparison sort of the runs is
                    // O(R log R) for R runs; the runs of one choice of one field never overlap
                    // and the walk writes each when it ends, so they come in order of their
                    // starts, and placing each in its bucket keeps that order: O(R + D), D the
                    // choices of the scope's fields with one MENTION bucket each.
                    let mut bucket = Vec::with_capacity(con.scope.len() + 1);
                    bucket.push(0);
                    for &f in &con.scope {
                        bucket.push(bucket[bucket.len() - 1] + dom[f] as usize + 1);
                    }
                    let at = |&(place, v, _, _): &(usize, Choice, usize, usize)| {
                        bucket[place]
                            + if v == MENTION {
                                dom[con.scope[place]] as usize
                            } else {
                                v as usize
                            }
                    };
                    let mut next = vec![0; bucket[con.scope.len()] + 1];
                    for run in &form.runs {
                        next[at(run) + 1] += 1;
                    }
                    for b in 1..next.len() {
                        next[b] += next[b - 1];
                    }
                    let mut held = vec![(0, 0, 0, 0); form.runs.len()];
                    for run in &form.runs {
                        let b = at(run);
                        held[next[b]] = *run;
                        next[b] += 1;
                    }
                    debug_assert!(
                        held.windows(2)
                            .all(|w| (w[0].0, w[0].1) != (w[1].0, w[1].1) || w[0].3 <= w[1].2),
                        "the runs of one choice come in order and do not overlap"
                    );
                    let mut i = 0;
                    for (place, &f) in con.scope.iter().enumerate() {
                        let s = slot_var.len();
                        slot_var.push((f, n_counts));
                        n_counts += dom[f] as usize;
                        pair_slots[f].push((c, s));
                        slot_list.push(list_slot.len());
                        for v in 0..dom[f] {
                            while i < held.len() && (held[i].0, held[i].1) == (place, v) {
                                runs.push((base + held[i].2, base + held[i].3));
                                i += 1;
                            }
                            list_slot.push(s);
                            list_at.push(runs.len());
                        }
                        let mut end = 0;
                        while i < held.len() && (held[i].0, held[i].1) == (place, MENTION) {
                            if held[i].2 > end {
                                runs.push((base + end, base + held[i].2));
                            }
                            end = held[i].3;
                            i += 1;
                        }
                        if end < form.pairs {
                            runs.push((base + end, base + form.pairs));
                        }
                        list_slot.push(s);
                        list_at.push(runs.len());
                    }
                    debug_assert_eq!(i, held.len(), "every run is of a slot of the scope");
                }
            }
            slots_of.push(first_slot..slot_var.len());
        }
        // Each list watches its first pair.
        let n_lists = list_slot.len();
        let (mut wit, mut wit_next, mut watch_head) = (
            vec![NONE; n_lists],
            vec![NONE; n_lists],
            vec![NONE; n_pairs],
        );
        let wit_run = list_at[..n_lists].to_vec();
        for l in 0..n_lists {
            if list_at[l] < list_at[l + 1] {
                let x = runs[list_at[l]].0;
                wit[l] = x;
                wit_next[l] = watch_head[x];
                watch_head[x] = l;
            }
        }
        // The cubes that use each choice, in one array by choice: count them, then fill each
        // choice's run from its end, the cubes from the last, so each run is in cube order.
        let mut uses_at = vec![0; total + 1];
        for &(f, v, _, _) in &cube_lits {
            uses_at[offset[f] + v as usize] += 1;
        }
        for i in 1..=total {
            uses_at[i] += uses_at[i - 1];
        }
        let mut uses = vec![0; n_lits];
        for k in (0..cube_con.len()).rev() {
            for &(f, v, _, _) in cube_lits[cube_start[k]..cube_start[k + 1]].iter().rev() {
                let i = offset[f] + v as usize;
                uses_at[i] -= 1;
                uses[uses_at[i]] = k;
            }
        }
        let mut count = vec![0; n_counts];
        let mut mention = vec![0; slot_var.len()];
        for &(_, _, i, s) in &cube_lits {
            count[i] += 1;
            mention[s] += 1;
        }
        // Order the slots of each constraint by `mention`, a counting sort.
        let mut order = vec![0; slot_var.len()];
        let mut pos = vec![0; slot_var.len()];
        for (c, range) in slots_of.iter().enumerate() {
            if !matches!(cons[c].check, Check::Cubes) {
                continue;
            }
            let b = bin_of[c];
            let n = live[c] as usize;
            for s in range.clone() {
                bin[b + mention[s] as usize + 1] += 1;
            }
            bin[b] = range.start;
            for m in 1..=n + 1 {
                bin[b + m] += bin[b + m - 1];
            }
            let mut next = bin[b..=b + n].to_vec();
            for s in range.clone() {
                let m = mention[s] as usize;
                order[next[m]] = s;
                pos[s] = next[m];
                next[m] += 1;
            }
        }
        let n_cons = cons.len();
        let n_cubes = cube_con.len();
        Engine {
            theory,
            size: dom.clone(),
            dom,
            cons,
            cons_of_law,
            whole_of,
            open,
            offset,
            alive: vec![true; total],
            trail: Vec::new(),
            head: 0,
            cube_con,
            cube_start,
            cube_lits,
            cube_alive: vec![true; n_cubes],
            undo: Vec::new(),
            pair_live: LiveSet::new(n_pairs),
            slot_list,
            list_slot,
            list_at,
            runs,
            wit,
            wit_run,
            wit_next,
            watch_head,
            pair_slots,
            unwatched: Vec::new(),
            emptied: Vec::new(),
            uses,
            uses_at,
            count,
            marked: vec![false; slot_var.len()],
            slot_var,
            slots_of,
            mention,
            live,
            order,
            pos,
            bin,
            bin_of,
            queue: VecDeque::new(),
            queued: vec![false; n_cons],
            work: 0,
        }
    }

    fn is_alive(&self, f: usize, c: Choice) -> bool {
        self.alive[self.offset[f] + c as usize]
    }

    fn remove(&mut self, f: usize, c: Choice, why: Reason) {
        let i = self.offset[f] + c as usize;
        debug_assert!(self.alive[i], "removing a choice twice");
        self.alive[i] = false;
        self.size[f] -= 1;
        if self.size[f] == 1 {
            for &w in &self.whole_of[f] {
                self.open[w] -= 1;
            }
        }
        self.trail.push((f, c, why, self.undo.len()));
    }

    /// Undoes the removals after the first `mark`, which must be a point where every removal
    /// before it had its cubes and pairs removed: the start of a choice or of a group.
    fn undo_to(&mut self, mark: usize) {
        if let Some(&(_, _, _, undone)) = self.trail.get(mark) {
            while self.undo.len() > undone {
                match self.undo.pop().expect("the list is longer than its mark") {
                    Undo::Cube(k) => {
                        self.cube_alive[k] = true;
                        let c = self.cube_con[k];
                        self.live[c] += 1;
                        for j in self.cube_start[k]..self.cube_start[k + 1] {
                            let (_, _, i, s) = self.cube_lits[j];
                            self.count[i] += 1;
                            self.raise(c, s);
                        }
                    }
                    Undo::Pair(x) => self.pair_live.insert(x),
                    Undo::Head(x, l) => self.watch_head[x] = l,
                    // The list was put first on the chain of its new pair, and every change
                    // made after it is undone already, so it is still first there.
                    Undo::Watch {
                        list,
                        wit,
                        run,
                        next,
                    } => {
                        if self.wit[list] != NONE {
                            self.watch_head[self.wit[list]] = self.wit_next[list];
                        }
                        self.wit[list] = wit;
                        self.wit_run[list] = run;
                        self.wit_next[list] = next;
                    }
                }
            }
        }
        while self.trail.len() > mark {
            let (f, c, _, _) = self.trail.pop().expect("the trail is longer than the mark");
            self.alive[self.offset[f] + c as usize] = true;
            self.size[f] += 1;
            if self.size[f] == 2 {
                for &w in &self.whole_of[f] {
                    self.open[w] += 1;
                }
            }
        }
        self.head = self.head.min(mark);
    }

    /// The one choice left for `f`, which must have exactly one.
    fn only(&self, f: usize) -> Choice {
        (0..self.dom[f])
            .find(|&c| self.is_alive(f, c))
            .expect("a chosen field keeps one choice")
    }

    fn enqueue(&mut self, c: usize) {
        if !self.queued[c] {
            self.queued[c] = true;
            self.queue.push_back(c);
        }
    }

    /// Starts constraint `c`: a choice no cube or pair of it supports is removed, and a whole
    /// clause is queued.
    fn start(&mut self, c: usize) -> Result<(), Conflict> {
        match self.cons[c].check {
            Check::Whole(_) => self.enqueue(c),
            Check::Pairs => {
                for s in self.slots_of[c].clone() {
                    let none = self.slot_list[s] + self.dom[self.slot_var[s].0] as usize;
                    if self.wit[none] == NONE {
                        self.remove_unsupported(c, none)?;
                    }
                }
            }
            Check::Cubes => {
                if self.slots_of[c].is_empty() && self.live[c] == 0 {
                    return Err(Conflict {
                        constraint: c,
                        field: None,
                    });
                }
                for s in self.slots_of[c].clone() {
                    if self.mention[s] == self.live[c] {
                        self.remove_unused(c, s)?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Removes the cubes of each removed choice and the choices left with no cube, and checks
    /// the whole clauses with at most one open field, until nothing changes or a variable is
    /// left with no choice.
    fn propagate(&mut self) -> Result<(), Conflict> {
        let result = self.run();
        if result.is_err() {
            self.clear_queue();
        }
        result
    }

    fn clear_queue(&mut self) {
        while let Some(d) = self.queue.pop_front() {
            self.queued[d] = false;
        }
    }

    fn run(&mut self) -> Result<(), Conflict> {
        loop {
            if self.head < self.trail.len() {
                let (f, v, _, _) = self.trail[self.head];
                self.head += 1;
                let i = self.offset[f] + v as usize;
                for u in self.uses_at[i]..self.uses_at[i + 1] {
                    let k = self.uses[u];
                    if self.cube_alive[k] {
                        self.kill(k)?;
                    }
                }
                for p in 0..self.pair_slots[f].len() {
                    let (c, s) = self.pair_slots[f][p];
                    self.kill_pairs(c, self.slot_list[s] + v as usize)?;
                }
                // A whole clause is checked again only when one of its fields is fixed: once at
                // most one is open, the choices it allows the open field do not change as that
                // field loses others, so checking it again then would be the choices times the
                // clause (`scaling::one_wide_field_scales`).
                if self.size[f] <= 1 {
                    for w in 0..self.whole_of[f].len() {
                        let c = self.whole_of[f][w];
                        if self.open[c] <= 1 {
                            self.enqueue(c);
                        }
                    }
                }
            } else if let Some(c) = self.queue.pop_front() {
                self.queued[c] = false;
                self.check_clause(c)?;
            } else {
                return Ok(());
            }
        }
    }

    /// Removes the live pairs of list `l` of constraint `c` of pairs, moves each list that
    /// watched one of them to its next live pair, and removes the choices left with no support
    /// by the lists left with none, in the order of the lists.
    fn kill_pairs(&mut self, c: usize, l: usize) -> Result<(), Conflict> {
        let mut unwatched = std::mem::take(&mut self.unwatched);
        let mut emptied = std::mem::take(&mut self.emptied);
        for r in self.list_at[l]..self.list_at[l + 1] {
            let (mut x, end) = self.runs[r];
            loop {
                x = self.pair_live.next(x);
                if x >= end {
                    break;
                }
                self.work += 1;
                self.pair_live.remove(x);
                self.undo.push(Undo::Pair(x));
                if self.watch_head[x] != NONE {
                    unwatched.push(x);
                }
                x += 1;
            }
        }
        // Every pair removed first, so that a list moves straight to a pair that stays live.
        for &x in &unwatched {
            let mut m = self.watch_head[x];
            self.undo.push(Undo::Head(x, m));
            self.watch_head[x] = NONE;
            while m != NONE {
                let next = self.wit_next[m];
                self.undo.push(Undo::Watch {
                    list: m,
                    wit: x,
                    run: self.wit_run[m],
                    next,
                });
                // Forward from `x` in its run, then through the runs after it.
                let (mut r, mut from, mut found) = (self.wit_run[m], x + 1, NONE);
                while r < self.list_at[m + 1] {
                    let (start, end) = self.runs[r];
                    let y = self.pair_live.next(from.max(start));
                    if y < end {
                        found = y;
                        break;
                    }
                    r += 1;
                    from = 0;
                }
                self.wit[m] = found;
                self.wit_run[m] = r;
                if found == NONE {
                    self.wit_next[m] = NONE;
                    emptied.push(m);
                } else {
                    self.wit_next[m] = self.watch_head[found];
                    self.watch_head[found] = m;
                }
                m = next;
            }
        }
        unwatched.clear();
        self.unwatched = unwatched;
        emptied.sort_unstable();
        let mut result = Ok(());
        for &m in &emptied {
            result = self.remove_unsupported(c, m);
            if result.is_err() {
                break;
            }
        }
        emptied.clear();
        self.emptied = emptied;
        result
    }

    /// Removes the choices that list `l` of constraint `c` of pairs supported, now that it has
    /// no live pair: its own choice when the list of pairs that do not mention the variable has
    /// none either, or, when `l` is that list, every choice whose own list has none.
    fn remove_unsupported(&mut self, c: usize, l: usize) -> Result<(), Conflict> {
        let s = self.list_slot[l];
        let f = self.slot_var[s].0;
        let first = self.slot_list[s];
        let none = first + self.dom[f] as usize;
        if self.wit[none] != NONE {
            return Ok(());
        }
        let lost = if l == none {
            0..self.dom[f]
        } else {
            (l - first) as Choice..(l - first + 1) as Choice
        };
        for v in lost {
            if self.wit[first + v as usize] == NONE && self.is_alive(f, v) {
                self.remove(f, v, Reason::Law(c));
                if self.size[f] == 0 {
                    return Err(Conflict {
                        constraint: c,
                        field: Some(f),
                    });
                }
            }
        }
        Ok(())
    }

    /// Removes cube `k` and every choice it leaves unsupported.
    fn kill(&mut self, k: usize) -> Result<(), Conflict> {
        self.work += 1;
        self.cube_alive[k] = false;
        self.undo.push(Undo::Cube(k));
        let c = self.cube_con[k];
        let lits = self.cube_start[k]..self.cube_start[k + 1];
        // Every count first, so that an undo, which restores them all, finds them all lowered.
        self.live[c] -= 1;
        for j in lits.clone() {
            let (_, _, i, s) = self.cube_lits[j];
            self.count[i] -= 1;
            self.lower(c, s);
            self.marked[s] = true;
        }
        // The slots every live cube now mentions are last in `order`. Those `k` did not mention
        // were mentioned by every live cube but `k`, and have just lost the support `k` gave all
        // their choices; those `k` mentioned are visited once for each choice of `k`.
        let top = self.bin[self.bin_of[c] + self.live[c] as usize];
        let mut result = Ok(());
        for p in top..self.slots_of[c].end {
            let s = self.order[p];
            if !self.marked[s] {
                result = self.remove_unused(c, s);
                if result.is_err() {
                    break;
                }
            }
        }
        for j in lits.clone() {
            self.marked[self.cube_lits[j].3] = false;
        }
        result?;
        for j in lits {
            let (f, v, i, s) = self.cube_lits[j];
            if self.count[i] == 0 && self.mention[s] == self.live[c] && self.is_alive(f, v) {
                self.remove(f, v, Reason::Law(c));
                if self.size[f] == 0 {
                    return Err(Conflict {
                        constraint: c,
                        field: Some(f),
                    });
                }
            }
        }
        Ok(())
    }

    /// Removes the choices of slot `s` of constraint `c` that no live cube uses, once every
    /// live cube of `c` mentions its variable.
    fn remove_unused(&mut self, c: usize, s: usize) -> Result<(), Conflict> {
        let (f, base) = self.slot_var[s];
        for v in 0..self.dom[f] {
            if self.count[base + v as usize] == 0 && self.is_alive(f, v) {
                self.remove(f, v, Reason::Law(c));
                if self.size[f] == 0 {
                    return Err(Conflict {
                        constraint: c,
                        field: Some(f),
                    });
                }
            }
        }
        Ok(())
    }

    /// Lowers `mention[s]` by one, keeping `order` sorted: `s` moves to the first place of its
    /// bin, which then becomes the last place of the bin below.
    fn lower(&mut self, c: usize, s: usize) {
        let b = self.bin_of[c] + self.mention[s] as usize;
        let first = self.bin[b];
        self.swap(s, first);
        self.bin[b] += 1;
        self.mention[s] -= 1;
    }

    /// Raises `mention[s]` by one, the reverse of `lower`.
    fn raise(&mut self, c: usize, s: usize) {
        let b = self.bin_of[c] + self.mention[s] as usize + 1;
        let last = self.bin[b] - 1;
        self.swap(s, last);
        self.bin[b] -= 1;
        self.mention[s] += 1;
    }

    /// Moves slot `s` to place `p` of `order`, and the slot there to the place of `s`.
    fn swap(&mut self, s: usize, p: usize) {
        let other = self.order[p];
        let q = self.pos[s];
        self.order.swap(p, q);
        self.pos[other] = q;
        self.pos[s] = p;
    }

    /// Checks whole clause `c` once at most one of its fields is open: with none open, whether
    /// it holds; with one, which of that field's choices it allows.
    fn check_clause(&mut self, c: usize) -> Result<(), Conflict> {
        let Check::Whole(k) = self.cons[c].check else {
            unreachable!("only whole clauses are queued")
        };
        if self.open[c] > 1 {
            return Ok(());
        }
        self.work += 1;
        let law = self.cons[c].law;
        let open = self.cons[c]
            .scope
            .iter()
            .copied()
            .find(|&f| self.size[f] > 1);
        match open {
            None => {
                if !self.theory.clause_holds(law, k, |g| self.only(g)) {
                    return Err(Conflict {
                        constraint: c,
                        field: None,
                    });
                }
            }
            Some(f) => {
                let theory = self.theory;
                let failing =
                    theory.clause_fails_for(law, k, f, |v| self.is_alive(f, v), |g| self.only(g));
                for v in failing {
                    self.remove(f, v, Reason::Law(c));
                }
                if self.size[f] == 0 {
                    return Err(Conflict {
                        constraint: c,
                        field: Some(f),
                    });
                }
            }
        }
        Ok(())
    }
}

/// Whether the default report stops at the first choice that leads to no model, or the search
/// runs to the end, as `@exhaustive` asks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Default,
    Exhaustive,
}

/// How the search of a group ended.
#[derive(Clone, Debug)]
pub enum End {
    /// The search ran to the end: `models` is every model of the group.
    Complete,
    /// The default report found two models and stopped.
    Several,
    /// The default report reached a choice that leads to no model and stopped; the text says
    /// which choices it had made and which laws left a field with nothing.
    Stopped(String),
    /// The group has a law the report does not check (`Law::refused`); this is the first.
    Refused(usize),
}

/// The search of one group.
pub struct GroupReport {
    pub fields: Vec<usize>,
    pub laws: Vec<usize>,
    /// The models found, each the choice of every field of the group in order.
    pub models: Vec<Vec<Choice>>,
    pub end: End,
    /// When the group has no model before any choice is made: the explanation.
    pub refuted: Option<String>,
    /// The choices tried by the search.
    pub nodes: u64,
    /// The choices tried that left some field with nothing.
    pub dead_ends: u64,
    /// The constraint work done: cubes removed and clauses checked.
    pub work: u64,
}

/// The trivial-model report of a theory.
pub struct Report {
    /// The first law that fails on one value, if one does.
    pub one_value_fails: Option<usize>,
    /// The laws that name no field and fail on two values.
    pub closed_fail: Vec<usize>,
    /// The laws not checked, since writing out their conjunctive normal form reached `BUDGET`.
    pub refused: Vec<usize>,
    pub free: Vec<usize>,
    pub groups: Vec<GroupReport>,
}

/// Runs the report on `t`.
pub fn report(t: &Theory, mode: Mode) -> Report {
    let one_value_fails = (0..t.laws.len()).find(|&l| !t.law_holds_on_one_value(l));
    let split = split(t);
    let refused: Vec<usize> = (0..t.laws.len()).filter(|&l| t.laws[l].refused()).collect();
    let closed_fail = split
        .closed
        .iter()
        .copied()
        .filter(|&l| !t.laws[l].refused() && !t.law_holds(l, |_| 0))
        .collect();
    let mut engine = Engine::new(t);
    let groups = split
        .groups
        .iter()
        .zip(&split.group_laws)
        .map(
            |(fields, laws)| match laws.iter().find(|&&l| t.laws[l].refused()) {
                Some(&l) => GroupReport {
                    fields: fields.clone(),
                    laws: laws.clone(),
                    models: Vec::new(),
                    end: End::Refused(l),
                    refuted: None,
                    nodes: 0,
                    dead_ends: 0,
                    work: 0,
                },
                None => search(&mut engine, fields, laws, mode),
            },
        )
        .collect();
    Report {
        one_value_fails,
        closed_fail,
        refused,
        free: split.free,
        groups,
    }
}

/// A frame of the depth-first search: the position of its field in the group, the next choice
/// to try, and the trail length before its choice.
struct Frame {
    pos: usize,
    next: Choice,
    mark: usize,
}

fn search(engine: &mut Engine, fields: &[usize], laws: &[usize], mode: Mode) -> GroupReport {
    let root = engine.trail.len();
    let work_before = engine.work;
    let mut out = GroupReport {
        fields: fields.to_vec(),
        laws: laws.to_vec(),
        models: Vec::new(),
        end: End::Complete,
        refuted: None,
        nodes: 0,
        dead_ends: 0,
        work: 0,
    };
    // Every constraint of the group's laws, those that name no field included.
    let started = laws.iter().try_for_each(|&l| {
        (0..engine.cons_of_law[l].len()).try_for_each(|i| engine.start(engine.cons_of_law[l][i]))
    });
    if let Err(conflict) = started.and_then(|()| engine.propagate()) {
        engine.clear_queue();
        out.refuted = Some(explain(engine, root, conflict));
        engine.undo_to(root);
        out.work = engine.work - work_before;
        return out;
    }
    let mut stack: Vec<Frame> = Vec::new();
    let mut from = 0;
    'search: loop {
        // Descend: the next field in declaration order with more than one choice left.
        match (from..fields.len()).find(|&i| engine.size[fields[i]] > 1) {
            Some(pos) => stack.push(Frame {
                pos,
                next: 0,
                mark: engine.trail.len(),
            }),
            None => {
                out.models
                    .push(fields.iter().map(|&f| engine.only(f)).collect());
                if mode == Mode::Default && out.models.len() == 2 {
                    out.end = End::Several;
                    break 'search;
                }
            }
        }
        // Try the next choice of the deepest frame, backtracking past exhausted ones.
        loop {
            let Some(top) = stack.last_mut() else {
                break 'search;
            };
            let (pos, mark) = (top.pos, top.mark);
            engine.undo_to(mark);
            let f = fields[pos];
            let arity = engine.theory.fields[f].arity;
            let Some(v) = (top.next..choices(arity)).find(|&v| engine.is_alive(f, v)) else {
                stack.pop();
                continue;
            };
            top.next = v + 1;
            out.nodes += 1;
            for w in 0..choices(arity) {
                if w != v && engine.is_alive(f, w) {
                    engine.remove(f, w, Reason::Chosen);
                }
            }
            match engine.propagate() {
                Ok(()) => {
                    from = pos + 1;
                    continue 'search;
                }
                Err(conflict) => {
                    out.dead_ends += 1;
                    if mode == Mode::Default {
                        out.end = End::Stopped(explain(engine, root, conflict));
                        break 'search;
                    }
                }
            }
        }
    }
    engine.undo_to(root);
    out.work = engine.work - work_before;
    out
}

/// The explanation of a conflict: the choices made, then every removal that led to it, in the
/// order they happened, each with the law that made it.
fn explain(engine: &Engine, root: usize, conflict: Conflict) -> String {
    let t = engine.theory;
    let trail = &engine.trail[root..];
    // The laws that removed choices of each field, read off the trail once.
    let mut removed_by: HashMap<usize, Vec<usize>> = HashMap::new();
    for &(f, _, why, _) in trail {
        match why {
            Reason::Law(c) => removed_by.entry(f).or_default().push(c),
            Reason::Chosen => {}
        }
    }
    // The removals that led here: from the empty field, back through the laws that removed
    // each choice to the other fields of those laws, each field once.
    let mut involved: HashSet<usize> = HashSet::new();
    let mut work: Vec<usize> = match conflict.field {
        Some(f) => vec![f],
        None => engine.cons[conflict.constraint].scope.clone(),
    };
    while let Some(f) = work.pop() {
        if involved.insert(f) {
            for &c in removed_by.get(&f).into_iter().flatten() {
                work.extend(engine.cons[c].scope.iter().copied().filter(|&h| h != f));
            }
        }
    }
    let mut out = String::new();
    // The removals of one choice are consecutive on the trail, so each chosen field is listed
    // once; the choice made is the one value the run did not remove. The last chosen field may
    // have lost that value too, in the conflict.
    let mut chosen: Vec<String> = Vec::new();
    let mut i = 0;
    while i < trail.len() {
        let (f, _, why, _) = trail[i];
        let mut j = i;
        while j < trail.len() && trail[j].0 == f && trail[j].2 == why {
            j += 1;
        }
        if why == Reason::Chosen {
            let mut removed = vec![false; engine.dom[f] as usize];
            for &(_, v, _, _) in &trail[i..j] {
                removed[v as usize] = true;
            }
            let made = removed
                .iter()
                .position(|&r| !r)
                .expect("a choice leaves one value") as Choice;
            chosen.push(format!("{}: {}", t.fields[f].name, show(t, f, made)));
        }
        i = j;
    }
    if !chosen.is_empty() {
        let _ = writeln!(out, "with {}", chosen.join(", "));
    }
    for &(f, v, why, _) in &engine.trail[root..] {
        // An end symbol is the engine's own variable, not written in the program.
        if f >= t.fields.len() {
            continue;
        }
        if let (true, Reason::Law(c)) = (involved.contains(&f), why) {
            let law = &t.laws[engine.cons[c].law];
            let _ = writeln!(
                out,
                "{} cannot be {}, by law {}: {}",
                t.fields[f].name,
                show(t, f, v),
                law.name,
                law.text
            );
        }
    }
    match conflict.field {
        Some(f) if f < t.fields.len() => {
            let _ = writeln!(out, "so no choice is left for {}", t.fields[f].name);
        }
        _ => {
            let law = &t.laws[engine.cons[conflict.constraint].law];
            let _ = writeln!(out, "so law {}: {} does not hold", law.name, law.text);
        }
    }
    out
}

/// A choice of field `f` as the program writes it.
pub fn show(t: &Theory, f: usize, c: Choice) -> String {
    let arity = t.fields[f].arity;
    let body = match c {
        0 => "#a".to_string(),
        1 => "#b".to_string(),
        p => param(arity, (p - 2) as usize),
    };
    match arity {
        0 => body,
        1 => format!("(x -> {body})"),
        n => {
            let params: Vec<String> = (0..n).map(|i| param(n, i)).collect();
            format!("(({}) -> {body})", params.join(", "))
        }
    }
}

fn param(arity: usize, i: usize) -> String {
    match arity {
        1..=3 => ["x", "y", "z"][i].to_string(),
        _ => format!("x{}", i + 1),
    }
}

fn names(t: &Theory, fields: &[usize]) -> String {
    let v: Vec<&str> = fields.iter().map(|&f| t.fields[f].name.as_str()).collect();
    v.join(", ")
}

fn model_line(t: &Theory, fields: &[usize], m: &[Choice]) -> String {
    let v: Vec<String> = fields
        .iter()
        .zip(m)
        .map(|(&f, &c)| format!("{}: {}", t.fields[f].name, show(t, f, c)))
        .collect();
    v.join(", ")
}

/// The report as text. Its length is O(fields + laws) in the default mode, plus one line per
/// model listed under `@exhaustive`.
pub fn render(t: &Theory, r: &Report) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "trivial models of {}", t.name);
    match r.one_value_fails {
        None => {
            let _ = writeln!(
                out,
                "  on one value, #a, with every field returning #a: every law holds."
            );
        }
        Some(l) => {
            let _ = writeln!(
                out,
                "  on one value, #a: law {} ({}) does not hold, since on one value every two \
                 values are equal.",
                t.laws[l].name, t.laws[l].text
            );
        }
    }
    let _ = writeln!(out, "  on two values, #a | #b:");
    for &l in &r.refused {
        let law = &t.laws[l];
        let _ = writeln!(
            out,
            "    law {} ({}) is not checked: the checker reached its compile-time work limit \
             ({BUDGET} steps) on this law. It checks a law as an `&&` of `||`s of \
             comparisons, and an `||` whose operands are `&&`s must be multiplied out to get \
             that form, as `(a && b) || (c && d)` is `(a || c) && (a || d) && (b || c) && \
             (b || d)`; this law multiplies out to more than the limit. Laws of this shape can \
             state any propositional formula, so no method checks all of them quickly. To have \
             it checked, split it into separate laws whose `||`s hold no `&&`s (for example \
             `(a && b) || c` is the two laws `a || c` and `b || c`), or state it as a \
             theorem and give its proof.",
            law.name, law.text
        );
    }
    for &l in &r.closed_fail {
        let _ = writeln!(
            out,
            "    law {} ({}) names no field and does not hold, so there is no model.",
            t.laws[l].name, t.laws[l].text
        );
    }
    // The count of models on two values, as a product of factors, when every list is complete.
    let mut factors: BTreeMap<u64, u64> = BTreeMap::new();
    let mut complete = r.closed_fail.is_empty() && r.refused.is_empty();
    for g in &r.groups {
        let law_names: Vec<&str> = g.laws.iter().map(|&l| t.laws[l].name.as_str()).collect();
        let s = if g.laws.len() == 1 { "" } else { "s" };
        let head = format!(
            "    {}, linked by law{s} {}:",
            names(t, &g.fields),
            law_names.join(", ")
        );
        if let Some(why) = &g.refuted {
            let _ = writeln!(out, "{head} no model.");
            for line in why.lines() {
                let _ = writeln!(out, "      {line}");
            }
            *factors.entry(0).or_default() += 1;
            continue;
        }
        match &g.end {
            End::Complete => {
                match g.models.len() {
                    0 => {
                        let _ = writeln!(out, "{head} no model.");
                    }
                    1 => {
                        let _ = writeln!(out, "{head} exactly one model,");
                    }
                    n => {
                        let _ = writeln!(out, "{head} {n} models,");
                    }
                }
                for m in &g.models {
                    let _ = writeln!(out, "      {}", model_line(t, &g.fields, m));
                }
                if g.dead_ends > 0 {
                    let _ = writeln!(
                        out,
                        "      The search made {} choices; {} of them led to no model.",
                        g.nodes, g.dead_ends
                    );
                }
                *factors.entry(g.models.len() as u64).or_default() += 1;
            }
            End::Refused(l) => {
                complete = false;
                let _ = writeln!(
                    out,
                    "{head} not decided, since law {} is not checked.",
                    t.laws[*l].name
                );
            }
            End::Several => {
                complete = false;
                let _ = writeln!(out, "{head} several models, for example");
                for m in &g.models {
                    let _ = writeln!(out, "      {}", model_line(t, &g.fields, m));
                }
            }
            End::Stopped(why) => {
                complete = false;
                match g.models.as_slice() {
                    [] => {
                        let _ = writeln!(out, "{head} not decided.");
                    }
                    ms => {
                        let _ = writeln!(out, "{head} at least {} model(s), for example", ms.len());
                        for m in ms {
                            let _ = writeln!(out, "      {}", model_line(t, &g.fields, m));
                        }
                    }
                }
                let _ = writeln!(
                    out,
                    "      The report stopped at a choice that leads to no model, so this list \
                     may be incomplete:"
                );
                for line in why.lines() {
                    let _ = writeln!(out, "        {line}");
                }
                let _ = writeln!(
                    out,
                    "      Whether laws like these have a model can take time exponential in \
                     the number of fields to decide, so the report does not search on by \
                     itself. To list every trivial model, at the cost of that search, write \
                     `@exhaustive` before the interface:"
                );
                let _ = writeln!(out, "        @exhaustive interface {}(T) {{ ... }}", t.name);
            }
        }
    }
    if !r.free.is_empty() {
        let n = r.free.len();
        let (each, verb) = if n == 1 {
            ("it", "is")
        } else {
            ("each", "are")
        };
        let _ = writeln!(
            out,
            "    {} {verb} named by no law: {each} may be any constant or any projection.",
            names(t, &r.free)
        );
        for &f in &r.free {
            *factors
                .entry(choices(t.fields[f].arity) as u64)
                .or_default() += 1;
        }
    }
    if complete {
        let count = if factors.contains_key(&0) {
            "0".to_string()
        } else {
            let parts: Vec<String> = factors
                .iter()
                .filter(|&(&b, _)| b != 1)
                .map(|(&b, &e)| {
                    if e == 1 {
                        b.to_string()
                    } else {
                        format!("{b}^{e}")
                    }
                })
                .collect();
            if parts.is_empty() {
                "1".to_string()
            } else {
                parts.join(" * ")
            }
        };
        let _ = writeln!(out, "  models on two values: {count}.");
        if count == "0" && r.one_value_fails.is_none() {
            let _ = writeln!(
                out,
                "  So the model on one value is the only trivial model."
            );
        }
    }
    out
}

/// Whether every group is in the proved fragment: each law is one equation or inequation, or a
/// conjunction of them, and the fields and the conjuncts form a forest.
pub fn in_forest_fragment(t: &Theory) -> bool {
    let mut parent: Vec<usize> = (0..t.fields.len()).collect();
    fn find(parent: &mut [usize], mut x: usize) -> usize {
        while parent[x] != x {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        x
    }
    for law in &t.laws {
        if law.refused() || law.clauses().iter().any(|clause| clause.len() != 1) {
            return false;
        }
        for clause in law.clauses() {
            let scope = t.atom_scope(&clause[0]);
            // A forest: no edge closes a cycle. The atom is a node joined to each of its fields.
            let atom = parent.len();
            parent.push(atom);
            for f in scope {
                let (x, y) = (find(&mut parent, atom), find(&mut parent, f));
                if x == y {
                    return false;
                }
                parent[x] = y;
            }
        }
    }
    true
}
