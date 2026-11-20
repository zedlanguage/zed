//! Where a loose atom goes from each expression of a function or lambda body (DESIGN.md
//! sec:failure, *Where a loose atom stops*; zed ATOM-BUBBLE-STUDY.md; plan row
//! CHK-index-else-bubble).
//!
//! A call checks its callee's needs on its own arguments ([`Ck::replay`](super::Ck)), and a
//! need may give atoms the body did not see when it was checked: `args[0]` in
//! `h(args) = args[0] ++ "!"` gives `#outOfBounds` once `args` is bound to `m.args`. Each such
//! atom goes where the expression that made it sends it in the body: to the body's result,
//! so the call gives it, as an operator or a call passes an atom on (rule 6 of
//! sec:type_resolution); nowhere, where an `else`, an `is` or a `==` handles it; or to a
//! place an atom may not reach, a statement, `_`, a display or a loop, where the check keeps
//! its rejection.
//!
//! [`Fates::build`] gives each expression of every body a [`Fate`], in one pass over the unit
//! from the outside in: a child's fate is its own step composed with its parent's. A binding
//! `y = e` sends `e`'s atoms where its readers send them, so each block is walked from its
//! last statement to its first, and every reader of `y` in the same body has its fate before
//! the binding is met. A reader in another body (a lambda that captures `y`), or one not
//! reached first, counts as a stop, which keeps the old rejection.
//!
//! Each step is conservative in the direction that keeps a rejection: a form this file does
//! not list as passing an atom on stops it, and a handler this file cannot read (a pattern
//! with parts) handles nothing, so the atom goes on as if unhandled.
//!
//! Complexity tradeoff: the naive way finds, for each need that gives an atom, the path from
//! the unit's root to its span and the readers of each binding on the path, by scanning the
//! unit: O(n) a need, O(n·m) for m needs. The table costs O(n + U) once for n expressions and
//! U name uses, built only when a check first meets such an atom (an error path), then O(1) a
//! lookup; its memory is one entry per expression. Each step is one or two operations on
//! atom sets, of the size of the atoms a pattern names.

use std::collections::HashMap;

use zed_kernel::types::Type as KType;
use zedc_resolve::resolve::Ref;
use zedc_resolve::resolve::tables::Tables;
use zedc_syntax::ast::{
    BinaryOp, Expr, ExprKind, Function, IndexKey, Param, Pattern, RangeEnd, Stmt, StmtKind,
    StrPart, Target,
};
use zedc_syntax::lex::Span;

use super::atom_pattern::matched_by;
use zedc_types::ty::atoms;

/// What stands at a place an atom may not reach, for the message that names it there
/// (plan row MSG-atom-stop-in-body). The first four are type errors at that place by DESIGN.md
/// sec:failure, *Where a loose atom stops*; the last is a place where DESIGN keeps the atom in
/// a type the program can name, as data in a display or the value of a loop, which this table
/// does not follow yet (plan row CHK-fate-unwalked-forms).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Boundary {
    /// `_ = e`: `_` drops no loose failure (crossing (7)).
    Underscore,
    /// An expression statement, whose value is dropped (crossing (7)).
    Statement,
    /// A write `p <- value` to a port (crossing (8)).
    Write { value: Span },
    /// The default `default` of a parameter under the written type `ty` (crossing (5)).
    Default { ty: Span, default: Span },
    /// Any other: a display, a loop, a reader in another body, `a, b = e`, a guard.
    Other,
}

/// The atoms `atoms` stop at the place `at`, where `how` stands.
#[derive(Clone, Debug)]
pub(super) struct Stop {
    pub atoms: KType,
    pub at: Span,
    pub how: Boundary,
}

/// Where the atoms that an expression's value holds go in its body: those of `drop` are
/// handled, those of each of `stops` reach the place it names, which an atom may not reach,
/// and every other atom reaches the body's result.
///
/// The atom sets of `drop` and of each stop are pairwise disjoint: a stop holds only atoms
/// no earlier stop holds, so an atom has one place where it is first stopped. That keeps the
/// list as short as the number of atom sets the body's patterns split the atoms into, plus
/// one, whatever the number of places that stop: every [`Fate::stop`] holds every atom, so
/// once one is in the list, a later one adds nothing ([`Fate::add_stops`]).
#[derive(Clone, Debug)]
pub(super) struct Fate {
    /// The atoms handled on the way.
    pub drop: KType,
    /// The atoms stopped on the way, each set with the first place that stops it.
    pub stops: Vec<Stop>,
}

impl Fate {
    /// The body's result itself: every atom reaches it.
    fn result() -> Fate {
        Fate {
            drop: KType::empty(),
            stops: Vec::new(),
        }
    }

    /// The place `at`, where `how` stands, which no atom may reach.
    fn stop(at: Span, how: Boundary) -> Fate {
        Fate {
            drop: KType::empty(),
            stops: vec![Stop {
                atoms: atoms(),
                at,
                how,
            }],
        }
    }

    /// A handler of every loose atom: `e else d`, `e is T`, `e == x`.
    fn drop_all() -> Fate {
        Fate {
            drop: atoms(),
            stops: Vec::new(),
        }
    }

    /// The atoms stopped on the way, wherever each is stopped.
    pub fn stopped(&self) -> KType {
        self.stops.iter().fold(KType::empty(), |s, x| &s | &x.atoms)
    }

    /// Adds `more` to the stops, each without the atoms `except` and those of an earlier
    /// stop, so the sets stay disjoint; a stop left with no atom is not kept.
    fn add_stops(&mut self, more: &[Stop], except: &KType) {
        for s in more {
            let atoms = &(&s.atoms - except) - &self.stopped();
            if !atoms.is_empty() {
                self.stops.push(Stop { atoms, ..s.clone() });
            }
        }
    }

    /// A handler of the atoms `k` on the way to `self`: `e else #a -> d`.
    fn handling(&self, k: &KType) -> Fate {
        let mut out = Fate {
            drop: &self.drop | k,
            stops: Vec::new(),
        };
        out.add_stops(&self.stops, k);
        out
    }

    /// `inner`, the fate of an expression in a body that a call in another body makes, then
    /// `self`, the fate of that call: the atoms `inner` sends to its body's result go on as
    /// `self` sends them. An atom is handled where it is first handled and stopped where it
    /// is first stopped, so the two compose as `drop = inner.drop ∪ (self.drop − inner.stop)`
    /// and `stop = inner.stop ∪ (self.stop − inner.drop)`, disjoint since each pair is; each
    /// atom of `stop` keeps the place that first stops it, `inner`'s before `self`'s.
    pub fn after(&self, inner: &Fate) -> Fate {
        let mut out = Fate {
            drop: &inner.drop | &(&self.drop - &inner.stopped()),
            stops: inner.stops.clone(),
        };
        out.add_stops(&self.stops, &inner.drop);
        out
    }
}

/// The fate of each expression of every body of a unit, by its text, with the body it lies
/// in. Where an expression shares its text with the one around it, the inner one's is kept.
pub(super) struct Fates {
    at: HashMap<Span, (Fate, u32)>,
}

impl Fates {
    /// The fates of the bodies of `unit`, whose binders' tables are `t`.
    pub fn build(t: &Tables, unit: &[Stmt]) -> Fates {
        // The readers of each binder of one name, from every use: O(U).
        let mut readers: HashMap<usize, Vec<Span>> = HashMap::new();
        for (span, r) in &t.res.uses {
            if let Ref::Bound(v) = r
                && let [b] = v.iter().copied().collect::<Vec<_>>()[..]
            {
                readers.entry(b).or_default().push(*span);
            }
        }
        // In the order of the text, so that the place a message names, the first reader's
        // stop, does not depend on the order of a hash map: O(U log U).
        readers.values_mut().for_each(|r| r.sort_unstable());
        let mut w = Walk {
            t,
            readers,
            at: HashMap::new(),
            bodies: 0,
        };
        // The unit's top level is a body of its own, whose statements no call reaches, so the
        // place of this stop is never named.
        let all = Span {
            start: 0,
            end: t.text.map_or(0, str::len),
        };
        w.stmts(unit, &Fate::stop(all, Boundary::Other), 0);
        Fates { at: w.at }
    }

    /// The fate of the expression at `span` in its body, if the unit has one there.
    pub fn of(&self, span: Span) -> Option<&Fate> {
        self.at.get(&span).map(|(f, _)| f)
    }
}

struct Walk<'t, 'a> {
    t: &'t Tables<'a>,
    readers: HashMap<usize, Vec<Span>>,
    at: HashMap<Span, (Fate, u32)>,
    bodies: u32,
}

impl Walk<'_, '_> {
    /// A new body, whose result is `f`'s or the lambda's, with its parameters' defaults.
    ///
    /// A default with no written type is a binding of its parameter (zed ATOM-BUBBLE-STUDY.md,
    /// "Parameter default, no written type": "the parameter takes the default's type, atom
    /// included"), so its atoms go where the parameter's readers in the body send them, and
    /// the body is walked first so that every reader has its fate. A default under a written
    /// type is checked against that type ("Parameter default": a type error at the default),
    /// so its atoms stop there, which keeps that rejection. Tests: `boundaries.rs`,
    /// `an_untyped_default_takes_the_atom_of_its_read`.
    fn body(&mut self, params: &[Param], e: &Expr) {
        self.bodies += 1;
        let b = self.bodies;
        self.expr(e, Fate::result(), b);
        for p in params {
            if let Some(d) = &p.default {
                let f = match &p.ty {
                    None => self.bound(self.t.id(p.span, &p.name), b),
                    Some(ty) => Fate::stop(
                        p.span,
                        Boundary::Default {
                            ty: ty.span,
                            default: d.span,
                        },
                    ),
                };
                self.expr(d, f, b);
            }
        }
    }

    fn function(&mut self, f: &Function) {
        self.body(&f.params, &f.body);
    }

    /// The statements of a block in body `b`, whose result `ret` is the block's value; from
    /// the last to the first, so that a binding's readers come before it.
    fn stmts(&mut self, ss: &[Stmt], ret: &Fate, b: u32) {
        for s in ss.iter().rev() {
            self.stmt(s, ret, b);
        }
    }

    fn stmt(&mut self, s: &Stmt, ret: &Fate, b: u32) {
        match &s.kind {
            StmtKind::Bind { targets, value } => {
                let f = match &targets[..] {
                    [Target::Name(n, _)] => self.bound(self.t.id(s.span, n), b),
                    // `_ = e` and `a, b = e` are boundaries of their own.
                    [Target::Wild] => Fate::stop(s.span, Boundary::Underscore),
                    _ => Fate::stop(s.span, Boundary::Other),
                };
                self.expr(value, f, b);
            }
            // `return e;`, or a trailing expression: the block's value.
            StmtKind::Return(es) if es.len() == 1 => self.expr(&es[0], ret.clone(), b),
            StmtKind::Return(es) => {
                let f = Fate::stop(s.span, Boundary::Other);
                es.iter().for_each(|e| self.expr(e, f.clone(), b))
            }
            StmtKind::Expr(e) => self.expr(e, Fate::stop(s.span, Boundary::Statement), b),
            StmtKind::Push { value, .. } => {
                let how = Boundary::Write { value: value.span };
                self.expr(value, Fate::stop(s.span, how), b)
            }
            StmtKind::While(e) | StmtKind::Until(e) => {
                self.expr(e, Fate::stop(s.span, Boundary::Other), b)
            }
            StmtKind::Function(f) => self.function(f),
            StmtKind::Method(m) => self.function(&m.function),
            StmtKind::Annotated { decl, .. } | StmtKind::Local(decl) => self.stmt(decl, ret, b),
            // An `initial` value is loop state and an indexed definition's value an entry of a
            // family (DESIGN.md sec:failure, crossings (6) and (2)): DESIGN keeps the atom in
            // their types, which this table does not follow, so an atom stops there, with
            // the keys and domains around it.
            StmtKind::Initial(i) => {
                let f = Fate::stop(s.span, Boundary::Other);
                self.keys(&i.keys, &f, b);
                self.expr(&i.value, f, b);
            }
            StmtKind::IndexedDef(d) => {
                let f = Fate::stop(s.span, Boundary::Other);
                self.keys(&d.keys, &f, b);
                self.expr(&d.value, f.clone(), b);
                for x in &d.boundary {
                    self.keys(&x.keys, &f, b);
                    self.expr(&x.value, f.clone(), b);
                }
            }
            StmtKind::Break
            | StmtKind::Struct(_)
            | StmtKind::Type(_)
            | StmtKind::Import(_)
            | StmtKind::UnitAnnot(_) => {}
        }
    }

    /// The keys `ks` of an indexed definition, a boundary value or an `initial` entry, each
    /// key and domain with the fate `f`.
    fn keys(&mut self, ks: &[IndexKey], f: &Fate, b: u32) {
        for k in ks {
            match k {
                IndexKey::In { set: e, .. } | IndexKey::At(e) => self.expr(e, f.clone(), b),
            }
        }
    }

    /// Where the value of a binding to binder `x` in body `b` sends its atoms: an atom is
    /// handled where every reader handles it, and stopped where some reader stops it. A
    /// binding read nowhere drops its value, atoms and all.
    fn bound(&self, x: usize, b: u32) -> Fate {
        let mut drop = atoms();
        let mut stops = Fate::result();
        for r in self.readers.get(&x).into_iter().flatten() {
            let f = match self.at.get(r) {
                Some((f, rb)) if *rb == b => f.clone(),
                _ => Fate::stop(*r, Boundary::Other),
            };
            drop = &drop & &f.drop;
            stops.add_stops(&f.stops, &KType::empty());
        }
        Fate {
            drop: &drop - &stops.stopped(),
            stops: stops.stops,
        }
    }

    /// Records `e`'s fate `f` in body `b`, then its parts'.
    fn expr(&mut self, e: &Expr, f: Fate, b: u32) {
        self.at.insert(e.span, (f.clone(), b));
        // A part of `e` whose atoms stop at `e`.
        let stop = || Fate::stop(e.span, Boundary::Other);
        match &e.kind {
            ExprKind::Int { .. }
            | ExprKind::Float { .. }
            | ExprKind::Rat(_)
            | ExprKind::Bool(_)
            | ExprKind::Atom(_)
            | ExprKind::Name(_)
            | ExprKind::This => {}
            ExprKind::Str(parts) => {
                for p in parts {
                    if let StrPart::Hole(h) = p {
                        self.expr(h, f.clone(), b);
                    }
                }
            }
            ExprKind::Unary(_, x) => self.expr(x, f, b),
            // `==` and `!=` test the atom; their value holds none.
            ExprKind::Binary(BinaryOp::Eq | BinaryOp::Ne, x, y) => {
                self.expr(x, Fate::drop_all(), b);
                self.expr(y, Fate::drop_all(), b);
            }
            ExprKind::Binary(_, x, y) | ExprKind::Index(x, y) => {
                self.expr(x, f.clone(), b);
                self.expr(y, f, b);
            }
            ExprKind::Call {
                callee,
                positional,
                named,
                ..
            } => {
                self.expr(callee, f.clone(), b);
                for a in positional.iter().chain(named.iter().map(|(_, a)| a)) {
                    self.expr(a, f.clone(), b);
                }
            }
            ExprKind::Member { of, .. } => self.expr(of, f, b),
            ExprKind::Is { of, .. } => self.expr(of, Fate::drop_all(), b),
            ExprKind::Else {
                of,
                pattern,
                default,
            } => {
                let handled = match pattern {
                    None => Fate::drop_all(),
                    Some(Pattern::Atom {
                        name,
                        fields,
                        items,
                        ..
                    }) => match matched_by(name, fields, items.as_deref()) {
                        Some(k) => f.handling(&k),
                        None => f.clone(),
                    },
                    Some(_) => f.clone(),
                };
                self.expr(of, handled, b);
                self.expr(default, f, b);
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                self.expr(cond, f.clone(), b);
                self.expr(then, f.clone(), b);
                self.expr(otherwise, f, b);
            }
            ExprKind::Block(ss) => self.stmts(ss, &f, b),
            ExprKind::In { of, set, .. } => {
                self.expr(of, f, b);
                self.expr(set, stop(), b);
            }
            ExprKind::Lambda { params, body } => self.body(params, body),
            ExprKind::Section(_, lambda) => self.expr(lambda, stop(), b),
            ExprKind::Match { of, arms } => {
                self.expr(of, stop(), b);
                for a in arms {
                    if let Some(g) = &a.guard {
                        self.expr(g, stop(), b);
                    }
                    self.expr(&a.body, f.clone(), b);
                }
            }
            // A display holds an atom as data, and a loop's frames and steps are not the
            // body's result: an atom stops there.
            ExprKind::Tuple(xs) | ExprKind::Array(xs) | ExprKind::Set(xs) => {
                xs.iter().for_each(|x| self.expr(x, stop(), b))
            }
            ExprKind::Map(kvs) => kvs.iter().for_each(|(k, v)| {
                self.expr(k, stop(), b);
                self.expr(v, stop(), b);
            }),
            ExprKind::Record(fs) => fs.iter().for_each(|(_, x)| self.expr(x, stop(), b)),
            // A `with` update's new values are fields of a record, and a remap's `into` levels
            // make the keys and values of a family: data, where an atom stops (as for a
            // display, above).
            ExprKind::With { of, updates } => {
                self.expr(of, stop(), b);
                updates.iter().for_each(|u| self.expr(&u.value, stop(), b));
            }
            ExprKind::Remap { of, levels, .. } => {
                self.expr(of, stop(), b);
                for l in levels.iter().flatten() {
                    for x in l.key.iter().chain(&l.reduce) {
                        self.expr(x, stop(), b);
                    }
                }
            }
            ExprKind::Read { of, .. } | ExprKind::Spread { of, .. } => self.expr(of, stop(), b),
            ExprKind::Reduce { of, op } => {
                self.expr(of, stop(), b);
                self.expr(op, stop(), b);
            }
            ExprKind::Range(x, end) => {
                self.expr(x, stop(), b);
                if let RangeEnd::Below(y) | RangeEnd::Through(y) = end {
                    self.expr(y, stop(), b);
                }
            }
            ExprKind::For {
                source,
                guard,
                body,
                ..
            } => {
                self.expr(source, stop(), b);
                if let Some(g) = guard {
                    self.expr(g, stop(), b);
                }
                self.expr(body, stop(), b);
            }
            ExprKind::Loop { body, .. } => self.expr(body, stop(), b),
            ExprKind::SortKey { key, .. } => {
                if let Some(k) = key {
                    self.expr(k, stop(), b);
                }
            }
        }
    }
}
