//! The machine-word widening notice (DESIGN.md sec:domains and sec:diagnostics): a warning
//! at each integer operation whose operands each fit in a machine word, `i64`, while its
//! result may not, so the value it gives is held as a big integer.
//!
//! Each `int` expression gets the interval of its values, `int[lo..=hi]`, from its integer
//! literals (as the checker adopts them), the operators `+`, `-`, `*`, `div`, `mod` and `^`,
//! the names bound by `=` to one name, and the joins of `if`, `else` and a block's `return`.
//! Anything else, a parameter or a call among them, is any `int`, and so is a value past the
//! word: an operand already past the word was widened upstream or given, and only the
//! operation that crosses is reported. The left operand of `mod 2^k`, k at most 64, built
//! from `+`, `-`, `*` and unary `-`, is computed in wrapping arithmetic (sec:domains), and
//! nothing in it, or in the modulus, is reported.
//!
//! The warning names the value, the widths of the operands (the narrowest of `i8`, `i16`,
//! `i32` and `i64` that holds each) and the interval the operation gives, and shows the
//! derivation of each operand's interval from its literals and bindings, and the repair.
//! It does not stop the build.
//!
//! The intervals come from the syntax alone, with no narrowing by a test and no relation
//! between operands: see the complexity tradeoff at `Walk::compute`.
//!
//! Each node is evaluated once, in an order that puts each binding before its uses (an
//! explicit-stack depth-first search with a state per node), so the walk is linear in the
//! size of the unit. A derivation visits each node at most once per warning, so the output is
//! linear in its own size.

use std::collections::HashMap;

use zed_kernel::Value;

use crate::check::Info;
use crate::check::ty::Carrier;
use zedc_resolve::resolve::tables::Tables;
use zedc_resolve::resolve::{Ref, Resolution};
use zedc_syntax::ast::{Error, Expr, ExprKind, Note, Param, Stmt, StmtKind, StrPart, Target};
use zedc_syntax::lex::Span;

/// A closed interval of integers, both ends in the word.
type Word = (i64, i64);

/// What an expression computes, as far as its interval goes.
#[derive(Clone, Copy)]
enum Kind {
    /// An integer literal: its value, when it is an `int` in the word.
    Lit(Option<i64>),
    /// `+`, `-` or `*`.
    Ring(Ring),
    /// Unary `-`.
    Neg,
    /// `div`.
    Div,
    /// `mod` by anything but a power of two up to `2 ^ 64`.
    Mod,
    /// `mod 2^k`, k at most 64: its left operand wraps.
    Wrap(u32),
    /// `^`.
    Pow,
    /// The join of the first this many children: the branches of an `if`, both sides of an
    /// `else`, a block's `return`.
    Join(u32),
    /// A name: its binder.
    Name(Option<usize>),
    /// Any `int`, or no `int` at all.
    Top,
}

#[derive(Clone, Copy)]
enum Ring {
    Add,
    Sub,
    Mul,
}

/// One expression of the unit.
struct Node<'a> {
    e: &'a Expr,
    kind: Kind,
    /// The first child; the children made with the node are numbered consecutively from it.
    first: u32,
    /// The root expression it is part of: a binding's value, a pushed value, a body.
    root: u32,
    /// Whether it is inside the wrapping left operand of `mod 2^k`, or is that modulus.
    wrap: bool,
}

/// What a root expression is the value of.
#[derive(Clone, Copy)]
enum Label<'a> {
    Name(&'a str),
    Push(&'a str),
    Result(&'a str),
    Lambda,
    Other,
}

impl Label<'_> {
    fn text(self) -> String {
        match self {
            Label::Name(n) => format!("`{n}`"),
            Label::Push(p) => format!("the value pushed to `{p}`"),
            Label::Result(f) => format!("the result of `{f}`"),
            Label::Lambda => "the result of this function".to_string(),
            Label::Other => "this expression".to_string(),
        }
    }
}

/// A pending expression of the walk that builds the nodes.
enum Work<'a> {
    Expr(&'a Expr, u32),
    Stmts(&'a [Stmt]),
}

/// What an operation that crosses the word gives, within `i128` when that is known.
type Crossed = Option<(i128, i128)>;

/// An operation that crosses the word: its node and the interval it gives, when that is
/// known within `i128`.
struct Crossing {
    at: u32,
    gives: Crossed,
}

struct Walk<'t, 'a> {
    t: &'t Tables<'a>,
    adopt: &'t HashMap<Span, Value>,
    /// The literals that take, at run time, the carrier of a type variable (step L1.26a).
    follows: &'t HashMap<Span, Vec<(Carrier, Value)>>,
    nodes: Vec<Node<'a>>,
    labels: HashMap<u32, Label<'a>>,
    /// The value node of each binder bound by `=` to one name.
    binds: HashMap<usize, u32>,
    work: Vec<Work<'a>>,
}

/// The widening warnings of the resolved `unit`, whose check gave `info`: the pass alone, for
/// tests that time it.
pub fn of(unit: &[Stmt], res: &Resolution, info: &Info) -> Vec<Error> {
    warnings(&Tables::new(unit, res), unit, info)
}

/// The widening warnings of `unit`, sorted by place.
pub fn warnings(t: &Tables, unit: &[Stmt], info: &Info) -> Vec<Error> {
    let mut w = Walk {
        t,
        adopt: &info.adopt,
        follows: &info.follows,
        nodes: Vec::new(),
        labels: HashMap::new(),
        binds: HashMap::new(),
        work: vec![Work::Stmts(unit)],
    };
    while let Some(item) = w.work.pop() {
        match item {
            Work::Stmts(stmts) => {
                for s in stmts {
                    w.stmt(s);
                }
            }
            Work::Expr(e, at) => w.expand(e, at),
        }
    }
    let (values, crossings) = w.evaluate();
    // The nodes each derivation has shown, by the number of the warning that showed them.
    let mut seen = (0, vec![0; w.nodes.len()]);
    let mut out: Vec<Error> = crossings
        .iter()
        .map(|c| w.warning(c, &values, &mut seen))
        .collect();
    out.sort_by(|a, b| (a.span, &a.message).cmp(&(b.span, &b.message)));
    out
}

impl<'t, 'a> Walk<'t, 'a> {
    /// A new node for `e`, part of `root` (itself when `None`), to be expanded.
    fn node(&mut self, e: &'a Expr, root: Option<u32>, wrap: bool) -> u32 {
        let at = u32::try_from(self.nodes.len()).expect("a unit has fewer than 2^32 nodes");
        self.nodes.push(Node {
            e,
            kind: Kind::Top,
            first: 0,
            root: root.unwrap_or(at),
            wrap,
        });
        self.work.push(Work::Expr(e, at));
        at
    }

    /// A root expression with its label.
    fn root(&mut self, e: &'a Expr, label: Label<'a>) -> u32 {
        let at = self.node(e, None, false);
        self.labels.insert(at, label);
        at
    }

    fn params(&mut self, params: &'a [Param]) {
        for p in params {
            if let Some(d) = &p.default {
                self.root(d, Label::Other);
            }
        }
    }

    /// The roots of the statement `s`.
    fn stmt(&mut self, s: &'a Stmt) {
        match &s.kind {
            StmtKind::Bind { targets, value, .. } => match &targets[..] {
                [Target::Name(n, _)] => {
                    let at = self.root(value, Label::Name(n));
                    if let Some(&id) = self.t.ids.get(&(s.span, n.as_str())) {
                        self.binds.insert(id, at);
                    }
                }
                _ => {
                    self.root(value, Label::Other);
                }
            },
            StmtKind::Push { port, value } => {
                self.root(value, Label::Push(port));
            }
            StmtKind::Function(f) => {
                self.params(&f.params);
                self.root(&f.body, Label::Result(&f.name));
                for (a, b) in &f.tests {
                    self.root(a, Label::Other);
                    self.root(b, Label::Other);
                }
            }
            StmtKind::Expr(e) | StmtKind::While(e) | StmtKind::Until(e) => {
                self.root(e, Label::Other);
            }
            StmtKind::Return(es) => {
                for e in es {
                    self.root(e, Label::Other);
                }
            }
            StmtKind::Annotated { decl, .. } => self.stmt(decl),
            // A `mutable` binding's variable changes from step to step, so its name is any
            // `int`; its first value is still walked.
            StmtKind::Mutable(decl) => {
                if let StmtKind::Bind { value, .. } = &decl.kind {
                    self.root(value, Label::Other);
                }
            }
            StmtKind::IndexedDef(d) => {
                self.root(&d.value, Label::Other);
            }
            StmtKind::Initial(i) => {
                self.root(&i.value, Label::Other);
            }
            StmtKind::Struct(_)
            | StmtKind::Type(_)
            | StmtKind::Method(_)
            | StmtKind::Import(_)
            | StmtKind::Local(_)
            | StmtKind::UnitAnnot(_) => {}
        }
    }

    /// Gives node `at` its kind and children.
    fn expand(&mut self, e: &'a Expr, at: u32) {
        let (root, wrap) = {
            let n = &self.nodes[at as usize];
            (n.root, n.wrap)
        };
        let first = u32::try_from(self.nodes.len()).expect("a unit has fewer than 2^32 nodes");
        // Only `+`, `-`, `*`, unary `-` and literals wrap; any other child of a wrapping
        // node is computed exactly, and so reported.
        let kids = |w: &mut Self, es: &[&'a Expr], wrap: bool| {
            for c in es {
                w.node(c, Some(root), wrap && wraps(c));
            }
        };
        let kind = match &e.kind {
            ExprKind::Int { .. } => Kind::Lit(self.literal(e, false)),
            ExprKind::Unary("-", a) if matches!(a.kind, ExprKind::Int { .. }) => {
                Kind::Lit(self.literal(a, true))
            }
            ExprKind::Unary("-", a) => {
                kids(self, &[a], wrap);
                Kind::Neg
            }
            ExprKind::Binary(o, a, b) => {
                let ring = match *o {
                    "+" => Some(Ring::Add),
                    "-" => Some(Ring::Sub),
                    "*" => Some(Ring::Mul),
                    _ => None,
                };
                match (ring, *o, power_of_two(b)) {
                    (Some(r), _, _) => {
                        kids(self, &[a, b], wrap);
                        Kind::Ring(r)
                    }
                    (None, "mod", Some(k)) => {
                        kids(self, &[a], true);
                        self.node(b, Some(root), true);
                        Kind::Wrap(k)
                    }
                    (None, "mod", None) => {
                        kids(self, &[a, b], false);
                        Kind::Mod
                    }
                    (None, "div", _) => {
                        kids(self, &[a, b], false);
                        Kind::Div
                    }
                    (None, "^", _) => {
                        kids(self, &[a, b], false);
                        Kind::Pow
                    }
                    _ => {
                        kids(self, &[a, b], false);
                        Kind::Top
                    }
                }
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                kids(self, &[then, otherwise, cond], false);
                Kind::Join(2)
            }
            ExprKind::Else { of, default, .. } => {
                kids(self, &[of, default], false);
                Kind::Join(2)
            }
            ExprKind::Block(stmts) => {
                let (ret, rest) = match stmts.split_last() {
                    Some((last, rest)) if matches!(last.kind, StmtKind::Return(_)) => {
                        (Some(last), rest)
                    }
                    _ => (None, &stmts[..]),
                };
                self.work.push(Work::Stmts(rest));
                match ret.map(|r| &r.kind) {
                    Some(StmtKind::Return(es)) if es.len() == 1 => {
                        kids(self, &[&es[0]], false);
                        Kind::Join(1)
                    }
                    Some(StmtKind::Return(es)) => {
                        let es: Vec<&Expr> = es.iter().collect();
                        kids(self, &es, false);
                        Kind::Top
                    }
                    _ => Kind::Top,
                }
            }
            ExprKind::Name(_) => Kind::Name(match self.t.res.uses.get(&e.span) {
                Some(Ref::Bound(ids)) if ids.len() == 1 => Some(ids[0]),
                _ => None,
            }),
            ExprKind::Unary(_, a) | ExprKind::Is { of: a, .. } | ExprKind::Member { of: a, .. } => {
                kids(self, &[a], false);
                Kind::Top
            }
            ExprKind::Index(a, b) => {
                kids(self, &[a, b], false);
                Kind::Top
            }
            ExprKind::Call {
                callee,
                positional,
                named,
                ..
            } => {
                let mut es: Vec<&Expr> = vec![callee];
                es.extend(positional);
                es.extend(named.iter().map(|(_, e)| e));
                kids(self, &es, false);
                Kind::Top
            }
            ExprKind::Tuple(es) => {
                let es: Vec<&Expr> = es.iter().collect();
                kids(self, &es, false);
                Kind::Top
            }
            ExprKind::Str(parts) => {
                let es: Vec<&Expr> = parts
                    .iter()
                    .filter_map(|p| match p {
                        StrPart::Hole(e) => Some(e),
                        StrPart::Text(_) => None,
                    })
                    .collect();
                kids(self, &es, false);
                Kind::Top
            }
            ExprKind::Lambda { params, body } => {
                self.params(params);
                self.root(body, Label::Lambda);
                Kind::Top
            }
            // Resolution rejects the forms of the later layers before this walk.
            ExprKind::Float { .. }
            | ExprKind::Rat(_)
            | ExprKind::Bool(_)
            | ExprKind::Atom(_)
            | ExprKind::Record(_)
            | ExprKind::With { .. }
            | ExprKind::This
            | ExprKind::Match { .. }
            | ExprKind::Range(..)
            | ExprKind::In { .. }
            | ExprKind::Reduce { .. }
            | ExprKind::Read { .. }
            | ExprKind::Section(_)
            | ExprKind::Array(_)
            | ExprKind::Set(_)
            | ExprKind::Map(_)
            | ExprKind::For { .. }
            | ExprKind::Loop { .. }
            | ExprKind::Break(_)
            | ExprKind::Spread { .. }
            | ExprKind::SortKey { .. } => Kind::Top,
        };
        let n = &mut self.nodes[at as usize];
        n.kind = kind;
        // Only the children made above follow `first`: a block's statements and a lambda's
        // body are roots, made after them or pending on the work list.
        n.first = first;
    }

    /// The value of the integer literal `e`, negated when `neg`, if the checker leaves it an
    /// `int` and it is in the word.
    fn literal(&self, e: &Expr, neg: bool) -> Option<i64> {
        let ExprKind::Int { radix, digits, .. } = &e.kind else {
            return None;
        };
        if self.follows.contains_key(&e.span) {
            return None;
        }
        if let Some(v) = self.adopt.get(&e.span)
            && !matches!(v, Value::Int(_) | Value::Big(_))
        {
            return None;
        }
        let v = i128::try_from(magnitude(digits, *radix)?).ok()?;
        i64::try_from(if neg { -v } else { v }).ok()
    }

    /// The nodes whose values node `i`'s value is computed from.
    fn deps(&self, i: u32) -> impl DoubleEndedIterator<Item = u32> + '_ {
        let n = &self.nodes[i as usize];
        let kids = match n.kind {
            Kind::Ring(_) | Kind::Div | Kind::Mod | Kind::Pow => 2,
            Kind::Neg | Kind::Wrap(_) => 1,
            Kind::Join(k) => k,
            Kind::Lit(_) | Kind::Name(_) | Kind::Top => 0,
        };
        let bound = match n.kind {
            Kind::Name(Some(id)) => self.binds.get(&id).copied(),
            _ => None,
        };
        (n.first..n.first + kids).chain(bound)
    }

    /// The interval of each node, `None` for any `int` or none, and the operations that
    /// cross the word.
    fn evaluate(&self) -> (Vec<Option<Word>>, Vec<Crossing>) {
        const NEW: u8 = 0;
        const OPEN: u8 = 1;
        const DONE: u8 = 2;
        let mut state = vec![NEW; self.nodes.len()];
        let mut values: Vec<Option<Word>> = vec![None; self.nodes.len()];
        let mut crossings = Vec::new();
        let mut stack = Vec::new();
        for start in 0..self.nodes.len() as u32 {
            stack.push(start);
            while let Some(&i) = stack.last() {
                match state[i as usize] {
                    NEW => {
                        state[i as usize] = OPEN;
                        stack.extend(self.deps(i).filter(|&d| state[d as usize] == NEW));
                    }
                    OPEN => {
                        stack.pop();
                        state[i as usize] = DONE;
                        // A dependency still open is a cycle through bindings, which the
                        // checker rejects; it reads as any `int`.
                        let v = |d: u32| match state[d as usize] {
                            DONE => values[d as usize],
                            _ => None,
                        };
                        match self.compute(i, v) {
                            Ok(value) => values[i as usize] = value,
                            Err(gives) if !self.nodes[i as usize].wrap => {
                                crossings.push(Crossing { at: i, gives });
                            }
                            Err(_) => {}
                        }
                    }
                    _ => {
                        stack.pop();
                    }
                }
            }
        }
        (values, crossings)
    }

    /// Node `i`'s interval from its dependencies' values `v`, and, when its operands are in
    /// the word and its result is not, what the result is within `i128`, if known.
    // Complexity tradeoff: an interval here comes from the operands' intervals alone, with
    // no narrowing by a test and no relation between operands. What is given up: a value
    // that only a test or a caller bounds (a parameter, a call, a name narrowed by `if`) is
    // any `int` (`Kind::Name(None)`, `Kind::Top`), so an operation on it gets no warning
    // even when it does cross the word; and operands that are one value or related values
    // are taken as independent, so `x - x` with `x` in `int[lo..=hi]` gets
    // `int[lo - hi..=hi - lo]` and is warned of when that leaves the word, though the value
    // is 0. Why: narrowing by a test needs the facts that hold on each path, and relating
    // operands needs a relational domain over the names in scope, whose cost per operation
    // grows with the number of names (exponential in the worst case for Presburger
    // formulas), where an interval costs O(1) per node and the whole walk O(N). Triggered by
    // an operation on a parameter, call result or test-bounded name, or by an operation
    // whose operands share a name. Tests:
    // `l01_29_diagnostics::widen::a_parameter_is_not_bounded_and_does_not_warn`,
    // `l01_29_diagnostics::widen::a_difference_of_a_value_with_itself_is_read_as_a_range`.
    // COMPLEXITY.md row C-WIDEN. A complete solution is the Presburger store's forward
    // transfer over the definition graph, which narrows by tests and relates operands; it
    // replaces this walk at step L1.40b.
    fn compute(&self, i: u32, v: impl Fn(u32) -> Option<Word>) -> Result<Option<Word>, Crossed> {
        let n = &self.nodes[i as usize];
        let (a, b) = (n.first, n.first + 1);
        let fit = |h: (i128, i128)| match (i64::try_from(h.0), i64::try_from(h.1)) {
            (Ok(lo), Ok(hi)) => Ok(Some((lo, hi))),
            _ => Err(Some(h)),
        };
        match n.kind {
            Kind::Lit(x) => Ok(x.map(|x| (x, x))),
            Kind::Ring(r) => match (v(a), v(b)) {
                (Some(x), Some(y)) => fit(ring(r, x, y)),
                _ => Ok(None),
            },
            Kind::Neg => match v(a) {
                Some((lo, hi)) => fit((-(hi as i128), -(lo as i128))),
                None => Ok(None),
            },
            Kind::Div => match (v(a), v(b)) {
                (Some(x), Some(y)) => match div(x, y) {
                    Some(h) => fit(h),
                    None => Ok(None),
                },
                _ => Ok(None),
            },
            Kind::Mod => match (v(a), v(b)) {
                (Some(x), Some(y)) => Ok(rem(x, y)),
                _ => Ok(None),
            },
            Kind::Wrap(k) => {
                let m = 1i128 << k;
                match v(a) {
                    Some(x) if k <= 62 => Ok(rem(x, (m as i64, m as i64))),
                    _ => Ok(i64::try_from(m - 1).ok().map(|hi| (0, hi))),
                }
            }
            Kind::Pow => match (v(a), v(b)) {
                (Some(x), Some(y)) if y.0 >= 0 => match pow(x, y) {
                    Some(h) => fit(h),
                    None => Err(None),
                },
                _ => Ok(None),
            },
            Kind::Join(k) => {
                let mut out: Option<Word> = None;
                for c in n.first..n.first + k {
                    let Some((lo, hi)) = v(c) else {
                        return Ok(None);
                    };
                    out = Some(out.map_or((lo, hi), |(l, h)| (l.min(lo), h.max(hi))));
                }
                Ok(out)
            }
            Kind::Name(Some(id)) => Ok(self.binds.get(&id).and_then(|&r| v(r))),
            Kind::Name(None) | Kind::Top => Ok(None),
        }
    }

    /// The warning for crossing `c`.
    fn warning(&self, c: &Crossing, values: &[Option<Word>], seen: &mut (u32, Vec<u32>)) -> Error {
        let n = &self.nodes[c.at as usize];
        let op = op_text(n.e);
        let operands: Vec<u32> = self.deps(c.at).collect();
        let widths: Vec<String> = operands
            .iter()
            .filter_map(|&d| values[d as usize])
            .map(|w| format!("an {}", width(w)))
            .collect();
        let label = self.labels[&n.root].text();
        let message = format!(
            "{label} widens past a machine word: this `{op}` of {} gives a big integer",
            widths.join(" and ")
        );
        let gives = match c.gives {
            Some((lo, hi)) => format!("this `{op}` gives {}, past i64", interval(lo, hi)),
            None => format!("this `{op}` gives values past i64"),
        };
        let mut notes = vec![Note {
            span: n.e.span,
            text: gives,
        }];
        self.derivation(&operands, values, seen, &mut notes);
        notes.push(Note {
            span: n.e.span,
            text: "repair: if wrapping arithmetic is meant, reduce the value with \
                   `mod 2^k`, k at most 64"
                .to_string(),
        });
        Error {
            menu: String::new(),
            span: n.e.span,
            message,
            notes,
            row: None,
        }
    }

    /// The notes deriving the intervals of the nodes `from`: each literal, each use of a
    /// name and its binding, and each operation, once each.
    fn derivation(
        &self,
        from: &[u32],
        values: &[Option<Word>],
        seen: &mut (u32, Vec<u32>),
        notes: &mut Vec<Note>,
    ) {
        let mark = seen.0 + 1;
        seen.0 = mark;
        let seen = &mut seen.1;
        let mut stack: Vec<u32> = from.iter().rev().copied().collect();
        while let Some(j) = stack.pop() {
            if std::mem::replace(&mut seen[j as usize], mark) == mark {
                continue;
            }
            let n = &self.nodes[j as usize];
            let Some((lo, hi)) = values[j as usize] else {
                continue;
            };
            let d = interval(lo as i128, hi as i128);
            let text = match (n.kind, &n.e.kind) {
                (Kind::Lit(_), _) => format!("this literal is {d}"),
                (Kind::Name(Some(id)), ExprKind::Name(name)) => {
                    notes.push(Note {
                        span: n.e.span,
                        text: format!("`{name}` is {d} here"),
                    });
                    if let Some(&r) = self.binds.get(&id)
                        && seen[r as usize] != mark
                    {
                        let at = &self.nodes[r as usize];
                        notes.push(Note {
                            span: at.e.span,
                            text: format!("`{name}` is defined as this expression, {d}"),
                        });
                        stack.push(r);
                    }
                    continue;
                }
                (Kind::Join(_), ExprKind::If { .. }) => format!("this `if` gives {d}"),
                (Kind::Join(_), ExprKind::Else { .. }) => format!("this `else` gives {d}"),
                (Kind::Join(_), _) => format!("this block gives {d}"),
                _ => format!("this `{}` gives {d}", op_text(n.e)),
            };
            notes.push(Note {
                span: n.e.span,
                text,
            });
            stack.extend(self.deps(j).rev());
        }
    }
}

/// Whether `e` is computed in wrapping arithmetic when it is inside the left operand of
/// `mod 2^k`: `+`, `-`, `*`, unary `-` and literals (sec:domains).
fn wraps(e: &Expr) -> bool {
    matches!(
        e.kind,
        ExprKind::Binary("+" | "-" | "*", ..) | ExprKind::Unary("-", _) | ExprKind::Int { .. }
    )
}

/// The digits of an integer literal as a number, if it fits in 128 bits. The lexer has removed
/// the `_`, and the reading stops at the first digit past 128 bits, so a long literal is
/// neither copied nor read in full.
fn magnitude(digits: &str, radix: u32) -> Option<u128> {
    u128::from_str_radix(digits, radix).ok()
}

/// `k` when `e` is a power of two `2 ^ k` with k at most 64, written as one literal or as
/// `2 ^ k` of two literals.
fn power_of_two(e: &Expr) -> Option<u32> {
    let k = match &e.kind {
        ExprKind::Int { radix, digits, .. } => {
            let v = magnitude(digits, *radix)?;
            if !v.is_power_of_two() {
                return None;
            }
            v.trailing_zeros()
        }
        ExprKind::Binary("^", b, k) => match (&b.kind, &k.kind) {
            (
                ExprKind::Int { radix, digits, .. },
                ExprKind::Int {
                    radix: r,
                    digits: d,
                    ..
                },
            ) if magnitude(digits, *radix) == Some(2) => u32::try_from(magnitude(d, *r)?).ok()?,
            _ => return None,
        },
        _ => return None,
    };
    (k <= 64).then_some(k)
}

/// The operator of an operation node.
fn op_text(e: &Expr) -> &'static str {
    match &e.kind {
        ExprKind::Binary(o, ..) | ExprKind::Unary(o, _) => o,
        _ => "?",
    }
}

/// `int[lo..=hi]`, or the one value.
fn interval(lo: i128, hi: i128) -> String {
    if lo == hi {
        lo.to_string()
    } else {
        format!("int[{lo}..={hi}]")
    }
}

/// The narrowest of `i8`, `i16`, `i32` and `i64` that holds `w`.
fn width((lo, hi): Word) -> &'static str {
    let holds = |min: i64, max: i64| min <= lo && hi <= max;
    if holds(i8::MIN.into(), i8::MAX.into()) {
        "i8"
    } else if holds(i16::MIN.into(), i16::MAX.into()) {
        "i16"
    } else if holds(i32::MIN.into(), i32::MAX.into()) {
        "i32"
    } else {
        "i64"
    }
}

/// `x + y`, `x - y` or `x * y` over the intervals, exactly.
fn ring(r: Ring, (a, b): Word, (c, d): Word) -> (i128, i128) {
    let (a, b, c, d) = (a as i128, b as i128, c as i128, d as i128);
    match r {
        Ring::Add => (a + c, b + d),
        Ring::Sub => (a - d, b - c),
        Ring::Mul => {
            let ps = [a * c, a * d, b * c, b * d];
            (
                ps.into_iter().min().unwrap_or(0),
                ps.into_iter().max().unwrap_or(0),
            )
        }
    }
}

/// `x div y` (Euclidean) over the intervals, exactly, or `None` when `y` is only 0. For a
/// fixed divisor the quotient is monotone in the dividend, and for a fixed dividend it is
/// monotone in the divisor on each side of 0, so the ends are at the corners of the dividend
/// and of each side of the divisor.
fn div((a, b): Word, (c, d): Word) -> Option<(i128, i128)> {
    let mut divisors = Vec::new();
    if c <= -1 {
        divisors.extend([c, d.min(-1)]);
    }
    if d >= 1 {
        divisors.extend([c.max(1), d]);
    }
    let qs = divisors.iter().flat_map(|&y| {
        [a, b]
            .into_iter()
            .map(move |x| (x as i128).div_euclid(y as i128))
    });
    let (lo, hi) = qs.fold(None, |m: Option<(i128, i128)>, q| {
        Some(m.map_or((q, q), |(l, h)| (l.min(q), h.max(q))))
    })?;
    Some((lo, hi))
}

/// `x mod y` (Euclidean) over the intervals: the dividend itself shifted when one divisor
/// maps it without wrapping, else 0 up to the largest divisor's size less 1, or `None` when
/// `y` is only 0.
fn rem((a, b): Word, (c, d): Word) -> Option<Word> {
    if (c, d) == (0, 0) {
        return None;
    }
    if c == d
        && (b as i128 - a as i128) < c.unsigned_abs() as i128
        && a.wrapping_rem_euclid(c) <= b.wrapping_rem_euclid(c)
    {
        // `wrapping_rem_euclid` is exact: only `i64::MIN mod -1` overflows `rem_euclid`, and its
        // remainder is 0, which is what the wrapping form returns.
        return Some((a.wrapping_rem_euclid(c), b.wrapping_rem_euclid(c)));
    }
    let top = c.unsigned_abs().max(d.unsigned_abs()) - 1;
    let top = i64::try_from(top).expect("the size of an i64 less 1 is an i64");
    Some((0, if a >= 0 { top.min(b) } else { top }))
}

/// `x ^ n` over the intervals, with `n` at least 0, or `None` when a value is past `i128`.
/// For a fixed exponent the ends are at the base's ends or at 0; for a fixed base of size at
/// least 2 the size grows with the exponent, so the ends are at the two smallest and the two
/// largest exponents, one of each parity.
fn pow((a, b): Word, (el, eh): Word) -> Option<(i128, i128)> {
    let mut bases = vec![a, b];
    if a <= 0 && 0 <= b {
        bases.push(0);
    }
    let exps = [el, el.saturating_add(1), eh - 1, eh]
        .into_iter()
        .filter(|&k| el <= k && k <= eh);
    let mut out: Option<(i128, i128)> = None;
    for k in exps {
        for &x in &bases {
            let p = power(x as i128, k)?;
            out = Some(out.map_or((p, p), |(l, h)| (l.min(p), h.max(p))));
        }
    }
    out
}

/// `x ^ k`, `k` at least 0, or `None` past `i128`.
fn power(x: i128, k: i64) -> Option<i128> {
    match x {
        0 => Some(i128::from(k == 0)),
        1 => Some(1),
        -1 => Some(if k % 2 == 0 { 1 } else { -1 }),
        _ => x.checked_pow(u32::try_from(k).ok()?),
    }
}
