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
//! at the same symbol. A law that is a conjunction is one such set per conjunct; a law with `||`
//! is checked whole, once all but one of its fields are chosen.
//!
//! The models are the product over the groups of fields that a common law links; a field no law
//! names is free and is not enumerated. Within a group a depth-first search assigns the fields in
//! declaration order and keeps every constraint generalized-arc-consistent after each choice. A
//! group whose laws are single equations or inequations and whose fields and laws form a forest
//! (no cycle through two laws) never reaches a choice that leads to no model, so its search costs
//! work proportional to the models it lists. Any other group may (hardness tests); the default
//! report stops at the first such choice.

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

/// A law member: a disjunction of conjunctions of atoms over its binders.
pub struct Law {
    pub name: String,
    pub binders: Vec<String>,
    /// The body as written, for the report.
    pub text: String,
    pub body: Vec<Vec<Atom>>,
}

/// An interface with law members.
pub struct Theory {
    pub name: String,
    pub fields: Vec<Field>,
    pub laws: Vec<Law>,
    pub terms: Vec<Term>,
}

/// The symbol a term ends at under a choice of every field it reaches.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Sym {
    Const(u32),
    Var(usize),
}

/// The choice of a field on two values: `0` is `#a`, `1` is `#b`, `2 + i` projects argument `i`.
pub type Choice = u32;

/// The number of choices of a field of `arity` arguments.
pub fn choices(arity: usize) -> u32 {
    2 + arity as u32
}

impl Theory {
    pub fn new(name: &str) -> Self {
        Theory {
            name: name.to_string(),
            fields: Vec::new(),
            laws: Vec::new(),
            terms: Vec::new(),
        }
    }

    /// Adds a field of `arity` arguments.
    pub fn field(&mut self, name: &str, arity: usize) -> &mut Self {
        self.fields.push(Field {
            name: name.to_string(),
            arity,
        });
        self
    }

    /// Adds a law with the binders named in `binders` (separated by spaces or commas) and the
    /// body `body`, written with `==`, `!=`, `&&`, `||`, field applications and binders.
    pub fn law(&mut self, name: &str, binders: &str, body: &str) -> &mut Self {
        let binders: Vec<String> = binders
            .split([' ', ','])
            .filter(|b| !b.is_empty())
            .map(str::to_string)
            .collect();
        let tokens = tokenize(body);
        let mut p = Parser {
            theory: self,
            binders: &binders,
            tokens: &tokens,
            at: 0,
        };
        let parsed = p.body();
        assert_eq!(p.at, tokens.len(), "law {name}: text after the body");
        self.laws.push(Law {
            name: name.to_string(),
            binders,
            text: body.to_string(),
            body: parsed,
        });
        self
    }

    /// The field of this name.
    pub fn field_id(&self, name: &str) -> Option<usize> {
        self.fields.iter().position(|f| f.name == name)
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
        let mut out = Vec::new();
        for conj in &self.laws[l].body {
            for a in conj {
                self.term_fields(a.lhs, &mut out);
                self.term_fields(a.rhs, &mut out);
            }
        }
        out.sort_unstable();
        out.dedup();
        out
    }

    fn atom_scope(&self, a: &Atom) -> Vec<usize> {
        let mut out = Vec::new();
        self.term_fields(a.lhs, &mut out);
        self.term_fields(a.rhs, &mut out);
        out.sort_unstable();
        out.dedup();
        out
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

    /// Whether law `l` holds at every binding on two values when each field `f` is `choice(f)`.
    /// The binders the sides end at are enumerated, `2^m` bindings for `m` of them: a law with
    /// `||` over binders is checked as the program wrote it, binding by binding.
    pub fn law_holds(&self, l: usize, choice: impl Fn(usize) -> Choice + Copy) -> bool {
        let law = &self.laws[l];
        let ends: Vec<Vec<(Rel, Sym, Sym)>> = law
            .body
            .iter()
            .map(|conj| {
                conj.iter()
                    .map(|a| {
                        (
                            a.rel,
                            self.reduce(a.lhs, choice),
                            self.reduce(a.rhs, choice),
                        )
                    })
                    .collect()
            })
            .collect();
        let mut vars: Vec<usize> = ends
            .iter()
            .flatten()
            .flat_map(|&(_, l, r)| [l, r])
            .filter_map(|s| match s {
                Sym::Var(v) => Some(v),
                Sym::Const(_) => None,
            })
            .collect();
        vars.sort_unstable();
        vars.dedup();
        // Complexity tradeoff: a law with `||` is checked at each of the 2^m bindings of the m
        // binders its sides end at. What is given up: nothing; the cost is exponential in the
        // binders of one law as written, which is the work the law asks for on a two-value
        // carrier (a `test` table over the domain). Structural trigger: a law body with `||`.
        // Test: `hardness::nae_fano_has_no_model`; COMPLEXITY.md C31. A
        // complete solution would decide validity of the disjunction of equalities directly,
        // which is coNP-complete in the size of the law.
        let value = |s: Sym, bits: u64| match s {
            Sym::Const(c) => c as u64,
            Sym::Var(v) => {
                let i = vars
                    .binary_search(&v)
                    .expect("every ended-at binder is listed");
                (bits >> i) & 1
            }
        };
        (0..1u64 << vars.len()).all(|bits| {
            ends.iter().any(|conj| {
                conj.iter().all(|&(rel, l, r)| match rel {
                    Rel::Eq => value(l, bits) == value(r, bits),
                    Rel::Ne => value(l, bits) != value(r, bits),
                })
            })
        })
    }

    /// Whether law `l` holds on one value: some alternative has only equations.
    pub fn law_holds_on_one_value(&self, l: usize) -> bool {
        self.laws[l]
            .body
            .iter()
            .any(|conj| conj.iter().all(|a| a.rel == Rel::Eq))
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
                            for c in 0..choices(args.len()) {
                                let mut next = cond.clone();
                                next.insert(at, (*field, c));
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

    /// The cubes of one atom: the partial choices under which it holds at every binding.
    // Complexity tradeoff: the cubes pair the paths of the two sides, so one atom costs the
    // product of its sides' path counts, each at most twice its side's size. What is given up:
    // nothing, the set is exact. Structural trigger: an atom with many paths on both sides, as
    // two large terms. Test: `scaling::the_report_scales`; COMPLEXITY.md C31. A
    // complete solution groups the paths by symbol and keeps them as a product of two lists
    // rather than their pairs, which the arc-consistency step would then read per symbol.
    fn cubes(&self, a: &Atom) -> Vec<Vec<(usize, Choice)>> {
        let (left, right) = (self.exits(a.lhs), self.exits(a.rhs));
        let mut out = Vec::new();
        for (ls, lc) in &left {
            for (rs, rc) in &right {
                let good = match (a.rel, ls, rs) {
                    (Rel::Eq, _, _) => ls == rs,
                    (Rel::Ne, Sym::Const(x), Sym::Const(y)) => x != y,
                    (Rel::Ne, Sym::Var(_), _) | (Rel::Ne, _, Sym::Var(_)) => false,
                };
                if good && let Some(m) = merge(lc, rc) {
                    out.push(m);
                }
            }
        }
        out
    }
}

/// The union of two sorted partial choices, or `None` when they choose one field two ways.
fn merge(a: &[(usize, Choice)], b: &[(usize, Choice)]) -> Option<Vec<(usize, Choice)>> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].0.cmp(&b[j].0) {
            std::cmp::Ordering::Less => {
                out.push(a[i]);
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                out.push(b[j]);
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                if a[i].1 != b[j].1 {
                    return None;
                }
                out.push(a[i]);
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    Some(out)
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
    binders: &'a [String],
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

    fn body(&mut self) -> Vec<Vec<Atom>> {
        let mut out = vec![self.conj()];
        while self.eat(&Token::Or) {
            out.push(self.conj());
        }
        out
    }

    fn conj(&mut self) -> Vec<Atom> {
        let mut out = vec![self.atom()];
        while self.eat(&Token::And) {
            out.push(self.atom());
        }
        out
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
        let term = if let Some(v) = self.binders.iter().position(|b| *b == name) {
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
    /// One equation or inequation: the cubes under which it holds.
    Cubes(Vec<Vec<(usize, Choice)>>),
    /// A law with `||`, checked whole once at most one of its fields is open.
    Whole,
}

/// A constraint: one atom of a law without `||`, or a whole law with `||`.
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

/// The constraints of a theory and the choices left for each field, with a trail to undo them.
struct Engine<'t> {
    theory: &'t Theory,
    cons: Vec<Constraint>,
    cons_of: Vec<Vec<usize>>,
    cons_of_law: Vec<Vec<usize>>,
    offset: Vec<usize>,
    alive: Vec<bool>,
    size: Vec<u32>,
    trail: Vec<(usize, Choice, Reason)>,
    queue: VecDeque<usize>,
    queued: Vec<bool>,
    // Scratch of one revision, indexed like `alive` and by field.
    support: Vec<bool>,
    mentions: Vec<u32>,
    /// Revisions done, for the tests' count of work.
    revisions: u64,
}

impl<'t> Engine<'t> {
    fn new(theory: &'t Theory) -> Self {
        let mut cons = Vec::new();
        for (l, law) in theory.laws.iter().enumerate() {
            match law.body.as_slice() {
                [conj] => {
                    for a in conj {
                        cons.push(Constraint {
                            law: l,
                            scope: theory.atom_scope(a),
                            check: Check::Cubes(theory.cubes(a)),
                        });
                    }
                }
                _ => cons.push(Constraint {
                    law: l,
                    scope: theory.law_scope(l),
                    check: Check::Whole,
                }),
            }
        }
        let mut cons_of = vec![Vec::new(); theory.fields.len()];
        let mut cons_of_law = vec![Vec::new(); theory.laws.len()];
        for (c, con) in cons.iter().enumerate() {
            for &f in &con.scope {
                cons_of[f].push(c);
            }
            cons_of_law[con.law].push(c);
        }
        let mut offset = Vec::with_capacity(theory.fields.len() + 1);
        let mut total = 0;
        for f in &theory.fields {
            offset.push(total);
            total += choices(f.arity) as usize;
        }
        offset.push(total);
        let size = theory.fields.iter().map(|f| choices(f.arity)).collect();
        let n_cons = cons.len();
        Engine {
            theory,
            cons,
            cons_of,
            cons_of_law,
            offset,
            alive: vec![true; total],
            size,
            trail: Vec::new(),
            queue: VecDeque::new(),
            queued: vec![false; n_cons],
            support: vec![false; total],
            mentions: vec![0; theory.fields.len()],
            revisions: 0,
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
        self.trail.push((f, c, why));
    }

    fn undo_to(&mut self, mark: usize) {
        while self.trail.len() > mark {
            let (f, c, _) = self.trail.pop().expect("the trail is longer than the mark");
            self.alive[self.offset[f] + c as usize] = true;
            self.size[f] += 1;
        }
    }

    /// The one choice left for `f`, which must have exactly one.
    fn only(&self, f: usize) -> Choice {
        (0..choices(self.theory.fields[f].arity))
            .find(|&c| self.is_alive(f, c))
            .expect("a chosen field keeps one choice")
    }

    fn enqueue(&mut self, c: usize) {
        if !self.queued[c] {
            self.queued[c] = true;
            self.queue.push_back(c);
        }
    }

    /// Revises constraints until none removes a choice, or one leaves a field with none.
    fn propagate(&mut self) -> Result<(), Conflict> {
        while let Some(c) = self.queue.pop_front() {
            self.queued[c] = false;
            match self.revise(c) {
                Ok(changed) => {
                    for f in changed {
                        for i in 0..self.cons_of[f].len() {
                            let d = self.cons_of[f][i];
                            if d != c {
                                self.enqueue(d);
                            }
                        }
                    }
                }
                Err(conflict) => {
                    while let Some(d) = self.queue.pop_front() {
                        self.queued[d] = false;
                    }
                    return Err(conflict);
                }
            }
        }
        Ok(())
    }

    /// Removes the choices of constraint `c`'s fields that no allowed combination supports, and
    /// returns the fields that lost one. For cubes this is generalized arc consistency, in time
    /// linear in the cubes and the scope's choices.
    fn revise(&mut self, c: usize) -> Result<Vec<usize>, Conflict> {
        self.revisions += 1;
        let con = &self.cons[c];
        let mut changed = Vec::new();
        match &con.check {
            Check::Cubes(cubes) => {
                for &f in &con.scope {
                    self.mentions[f] = 0;
                    let (lo, hi) = (self.offset[f], self.offset[f + 1]);
                    self.support[lo..hi].fill(false);
                }
                let mut alive_cubes = 0u32;
                for cube in cubes {
                    if cube
                        .iter()
                        .all(|&(f, v)| self.alive[self.offset[f] + v as usize])
                    {
                        alive_cubes += 1;
                        for &(f, v) in cube {
                            self.support[self.offset[f] + v as usize] = true;
                            self.mentions[f] += 1;
                        }
                    }
                }
                if alive_cubes == 0 && con.scope.is_empty() {
                    return Err(Conflict {
                        constraint: c,
                        field: None,
                    });
                }
                let scope = con.scope.clone();
                for f in scope {
                    if alive_cubes > self.mentions[f] {
                        continue;
                    }
                    let mut lost = false;
                    for v in 0..choices(self.theory.fields[f].arity) {
                        let i = self.offset[f] + v as usize;
                        if self.alive[i] && !self.support[i] {
                            self.remove(f, v, Reason::Law(c));
                            lost = true;
                        }
                    }
                    if self.size[f] == 0 {
                        return Err(Conflict {
                            constraint: c,
                            field: Some(f),
                        });
                    }
                    if lost {
                        changed.push(f);
                    }
                }
            }
            Check::Whole => {
                let law = con.law;
                let open: Vec<usize> = con
                    .scope
                    .iter()
                    .copied()
                    .filter(|&f| self.size[f] > 1)
                    .collect();
                match open.as_slice() {
                    [] => {
                        if !self.theory.law_holds(law, |g| self.only(g)) {
                            return Err(Conflict {
                                constraint: c,
                                field: None,
                            });
                        }
                    }
                    [f] => {
                        let f = *f;
                        let mut failing = Vec::new();
                        for v in 0..choices(self.theory.fields[f].arity) {
                            if self.is_alive(f, v)
                                && !self
                                    .theory
                                    .law_holds(law, |g| if g == f { v } else { self.only(g) })
                            {
                                failing.push(v);
                            }
                        }
                        for &v in &failing {
                            self.remove(f, v, Reason::Law(c));
                        }
                        if self.size[f] == 0 {
                            return Err(Conflict {
                                constraint: c,
                                field: Some(f),
                            });
                        }
                        if !failing.is_empty() {
                            changed.push(f);
                        }
                    }
                    [_, _, ..] => {}
                }
            }
        }
        Ok(changed)
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
    /// The constraint revisions done, a count of the work.
    pub revisions: u64,
}

/// The trivial-model report of a theory.
pub struct Report {
    /// The first law that fails on one value, if one does.
    pub one_value_fails: Option<usize>,
    /// The laws that name no field and fail on two values.
    pub closed_fail: Vec<usize>,
    pub free: Vec<usize>,
    pub groups: Vec<GroupReport>,
}

/// Runs the report on `t`.
pub fn report(t: &Theory, mode: Mode) -> Report {
    let one_value_fails = (0..t.laws.len()).find(|&l| !t.law_holds_on_one_value(l));
    let split = split(t);
    let closed_fail = split
        .closed
        .iter()
        .copied()
        .filter(|&l| !t.law_holds(l, |_| 0))
        .collect();
    let mut engine = Engine::new(t);
    let groups = split
        .groups
        .iter()
        .zip(&split.group_laws)
        .map(|(fields, laws)| search(&mut engine, fields, laws, mode))
        .collect();
    Report {
        one_value_fails,
        closed_fail,
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
    let revisions_before = engine.revisions;
    let mut out = GroupReport {
        fields: fields.to_vec(),
        laws: laws.to_vec(),
        models: Vec::new(),
        end: End::Complete,
        refuted: None,
        nodes: 0,
        dead_ends: 0,
        revisions: 0,
    };
    // Every constraint of the group's laws, those that name no field included.
    for &l in laws {
        for i in 0..engine.cons_of_law[l].len() {
            let c = engine.cons_of_law[l][i];
            engine.enqueue(c);
        }
    }
    if let Err(conflict) = engine.propagate() {
        out.refuted = Some(explain(engine, root, conflict));
        engine.undo_to(root);
        out.revisions = engine.revisions - revisions_before;
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
            for i in 0..engine.cons_of[f].len() {
                let c = engine.cons_of[f][i];
                engine.enqueue(c);
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
    out.revisions = engine.revisions - revisions_before;
    out
}

/// The explanation of a conflict: the choices made, then every removal that led to it, in the
/// order they happened, each with the law that made it.
fn explain(engine: &Engine, root: usize, conflict: Conflict) -> String {
    let t = engine.theory;
    let trail = &engine.trail[root..];
    // The laws that removed choices of each field, read off the trail once.
    let mut removed_by: HashMap<usize, Vec<usize>> = HashMap::new();
    for &(f, _, why) in trail {
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
        let (f, _, why) = trail[i];
        let mut j = i;
        while j < trail.len() && trail[j].0 == f && trail[j].2 == why {
            j += 1;
        }
        if why == Reason::Chosen {
            let mut removed = vec![false; choices(t.fields[f].arity) as usize];
            for &(_, v, _) in &trail[i..j] {
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
    for &(f, v, why) in &engine.trail[root..] {
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
        Some(f) => {
            let _ = writeln!(out, "so no choice is left for {}", t.fields[f].name);
        }
        None => {
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
    for &l in &r.closed_fail {
        let _ = writeln!(
            out,
            "    law {} ({}) names no field and does not hold, so there is no model.",
            t.laws[l].name, t.laws[l].text
        );
    }
    // The count of models on two values, as a product of factors, when every list is complete.
    let mut factors: BTreeMap<u64, u64> = BTreeMap::new();
    let mut complete = r.closed_fail.is_empty();
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
        if law.body.len() != 1 {
            return false;
        }
        for a in &law.body[0] {
            let scope = t.atom_scope(a);
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
