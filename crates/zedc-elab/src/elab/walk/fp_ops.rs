//! The terms of the operations on one level of a family that plan row FP-ops-run builds into
//! zedc as `map` is: the folds `x >< op`, `x.reduce(op)` and `x.sum`; `foldl` and `foldr`; and
//! the quantifiers `.any`, `.all` and `.find` (step L3.15a). The serial ones walk the level in
//! key order with the kernel's entry steps (`firstEntry`, `entryAfter`, and from the far end
//! `lastEntry`, `entryBefore`), each frame of a `gen` holding the entry it reached.

use std::sync::Arc;

use zed_kernel::term::{Evidence, Grade, GuardPos};
use zed_kernel::{Pattern as KPattern, Prim, Shared, Term, Value};
use zedc_syntax::ast::{BinaryOp, Expr, ExprKind};
use zedc_syntax::lex::Span;

use super::super::state::Elab;
use zedc_check::check::ty::Reducer;

/// A quantifier of step L3.15a.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Quantifier {
    /// `x.any(p)`.
    Any,
    /// `x.all(p)`.
    All,
    /// `x.find(p)`.
    Find,
}

impl Quantifier {
    /// The quantifier by its prelude word.
    pub(super) fn of(name: &str) -> Option<Quantifier> {
        match name {
            "any" => Some(Quantifier::Any),
            "all" => Some(Quantifier::All),
            "find" => Some(Quantifier::Find),
            _ => None,
        }
    }
}

fn var(v: &Arc<str>) -> Term {
    Term::Var(v.clone())
}

fn int(i: i64) -> Term {
    Term::Lit(Value::Int(i))
}

/// Component `i` of the tuple `t`.
fn part(t: Term, i: i64) -> Term {
    Term::Prim(Prim::TupleGet, vec![t, int(i)])
}

/// `true` while the entry `e` is one, `false` at the end of the level, the empty tuple.
fn not_at_end(e: Term) -> Term {
    Term::Match(
        Shared::new(e),
        vec![
            (KPattern::Tuple(Vec::new()), Term::Lit(Value::Bool(false))),
            (KPattern::Wild, Term::Lit(Value::Bool(true))),
        ],
    )
}

/// The last frame of the `gen` family `gn`, whose keys are `0 ..< count`.
fn last_frame(gn: &Arc<str>) -> Term {
    let n = Term::Prim(Prim::Count, vec![var(gn)]);
    Term::Prim(
        Prim::Get,
        vec![var(gn), Term::Prim(Prim::Sub, vec![n, int(1)])],
    )
}

impl<'a> Elab<'a> {
    /// The prelude operator a fold by `op` is, the operator section or the word `max` or
    /// `min` that the checker recorded at the fold's `span`; `None` for any other, which the
    /// checker rejects at its error.
    pub(super) fn reducer_prim(&self, op: &Expr, span: Span) -> Option<Prim> {
        match op.kind {
            ExprKind::Section(BinaryOp::Add, _) => Some(Prim::Add),
            ExprKind::Section(BinaryOp::Mul, _) => Some(Prim::Mul),
            ExprKind::Section(BinaryOp::And, _) => Some(Prim::And),
            ExprKind::Section(BinaryOp::Or, _) => Some(Prim::Or),
            _ => match self.info.reducers.get(&span) {
                Some(Reducer::Max) => Some(Prim::Max),
                Some(Reducer::Min) => Some(Prim::Min),
                _ => None,
            },
        }
    }

    /// The kernel `fold` by `p` of the one level of `family`, with the identity the checker
    /// found at the fold's `span` for the entries' one carrier; none for a fold with no
    /// identity there, which folds an empty level to `#empty` (a fold checked at two carriers
    /// whose empty folds differ is refused by the checker).
    pub(super) fn fold_one(&self, family: Term, p: Prim, span: Span) -> Term {
        let identity = self.info.reduce.get(&span).cloned();
        Term::Fold {
            family: Shared::new(family),
            op: Shared::new(Term::PrimFn(p)),
            identity: identity.map(|v| Shared::new(Term::Lit(v))),
            depth: 1,
            ev: Evidence::from([("assoc".into(), Grade::Axiom)]),
        }
    }

    /// `x.sum` on a family or `x.reduce(op)`: [`Self::fold_one`], where a loose atom `x`
    /// passes through, as the checker typed it.
    pub(super) fn member_fold(&mut self, x: Term, p: Prim, span: Span) -> Term {
        let xs = self.temp();
        let fold = self.fold_one(var(&xs), p, span);
        let body = Term::Match(
            Shared::new(var(&xs)),
            vec![(KPattern::AnyAtom, var(&xs)), (KPattern::Wild, fold)],
        );
        Term::Let(xs, Shared::new(x), Shared::new(body))
    }

    /// `x.foldl(init, f)`, or with `right` `x.foldr(f, init)`: the serial `gen` that DESIGN.md's
    /// method register gives (`initial acc = init; acc' = op(acc, m[t]);`), over the entries of
    /// the level in key order, from the far end for `foldr`, with `op(v, acc)`. Each frame is
    /// the pair `(e, acc)`, `e` the entry to fold next, `(k, v)`, or `()` past the end; the
    /// guard goes on while `e` is an entry, and the result is the accumulator of the last
    /// frame. A rank is folded in the order of its index, which is its key order. A loose atom
    /// `x` passes through, as at `map`.
    // Complexity tradeoff: n steps, each an entry step of the persistent map, O(log n), so
    // O(n log n), with the n frames kept in the `gen` family. The plan's first form read
    // `m[t]` by the rank `t`, the same O(log n) a step, and only on a rank; walking by entry
    // takes any keys at that cost. A kernel loop that kept only the last frame would save the
    // O(n) frames, but `gen`'s result is the family of every frame.
    pub(super) fn fold_dir_term(&mut self, x: Term, init: Term, f: Term, right: bool) -> Term {
        let (xs, g, fr, gn) = (self.temp(), self.temp(), self.temp(), self.temp());
        let (first, next) = match right {
            false => (Prim::FirstEntry, Prim::EntryAfter),
            true => (Prim::LastEntry, Prim::EntryBefore),
        };
        let entry = part(var(&fr), 0);
        let value = part(entry.clone(), 1);
        let args = match right {
            false => vec![part(var(&fr), 1), value],
            true => vec![value, part(var(&fr), 1)],
        };
        let step = Term::Prim(
            Prim::Tuple,
            vec![
                Term::Prim(next, vec![var(&xs), entry.clone()]),
                Term::App(Shared::new(var(&g)), args),
            ],
        );
        let frames = Term::Gen {
            init: Shared::new(Term::Prim(
                Prim::Tuple,
                vec![Term::Prim(first, vec![var(&xs)]), init],
            )),
            step: Shared::new(Term::Lam(vec![fr.clone()], Shared::new(step))),
            guard: Shared::new(Term::Lam(vec![fr], Shared::new(not_at_end(entry)))),
            pos: GuardPos::Before,
        };
        let run = Term::Let(
            gn.clone(),
            Shared::new(frames),
            Shared::new(part(last_frame(&gn), 1)),
        );
        let body = Term::Match(
            Shared::new(var(&xs)),
            vec![(KPattern::AnyAtom, var(&xs)), (KPattern::Wild, run)],
        );
        Term::Let(
            xs,
            Shared::new(x),
            Shared::new(Term::Let(g, Shared::new(f), Shared::new(body))),
        )
    }

    /// `x.any(p)`, `x.all(p)` or `x.find(p)` (step L3.15a): the entries asked in key order,
    /// stopping at the first that decides. Each frame of the `gen` is `(e, r, k)`: `e` the
    /// entry to ask next, or `()` past the end; `r` the answer so far, `p` at the entry before
    /// `e`, or at the start `false` (`true` for `all`); `k` that entry's key. The guard goes on
    /// while `e` is an entry and `r` is the start's answer, so it stops at the end, at the
    /// deciding entry, and at an atom `p` gives, which L3.15a makes the result. The result is
    /// the last frame's `r`; for `find`, its `k` when `r` is `true`, `#none` when it is
    /// `false`. A loose atom `x` passes through.
    // Complexity tradeoff: the walk asks k entries, k the position of the deciding one, each
    // step O(log n), so O(k log n) and never a read of the entries past it; a `fold` of the
    // answers, the naive form, asks all n. The k frames are kept in the `gen` family.
    pub(super) fn quantifier_term(&mut self, x: Term, f: Term, q: Quantifier) -> Term {
        let (xs, g, fr, gn, last) = (
            self.temp(),
            self.temp(),
            self.temp(),
            self.temp(),
            self.temp(),
        );
        let start = Value::Bool(q == Quantifier::All);
        let entry = part(var(&fr), 0);
        let step = Term::Prim(
            Prim::Tuple,
            vec![
                Term::Prim(Prim::EntryAfter, vec![var(&xs), entry.clone()]),
                Term::App(Shared::new(var(&g)), vec![part(entry.clone(), 1)]),
                part(entry.clone(), 0),
            ],
        );
        let guard = Term::Match(
            Shared::new(part(var(&fr), 1)),
            vec![
                (KPattern::Lit(start.clone()), not_at_end(entry)),
                (KPattern::Wild, Term::Lit(Value::Bool(false))),
            ],
        );
        let frames = Term::Gen {
            init: Shared::new(Term::Prim(
                Prim::Tuple,
                vec![
                    Term::Prim(Prim::FirstEntry, vec![var(&xs)]),
                    Term::Lit(start),
                    Term::Prim(Prim::Tuple, Vec::new()),
                ],
            )),
            step: Shared::new(Term::Lam(vec![fr.clone()], Shared::new(step))),
            guard: Shared::new(Term::Lam(vec![fr], Shared::new(guard))),
            pos: GuardPos::Before,
        };
        let answer = part(var(&last), 1);
        let result = match q {
            Quantifier::Any | Quantifier::All => answer,
            Quantifier::Find => Term::Match(
                Shared::new(answer.clone()),
                vec![
                    (KPattern::Lit(Value::Bool(true)), part(var(&last), 2)),
                    (
                        KPattern::Lit(Value::Bool(false)),
                        Term::Lit(Value::atom("none")),
                    ),
                    (KPattern::Wild, answer),
                ],
            ),
        };
        let run = Term::Let(
            gn.clone(),
            Shared::new(frames),
            Shared::new(Term::Let(
                last,
                Shared::new(last_frame(&gn)),
                Shared::new(result),
            )),
        );
        let body = Term::Match(
            Shared::new(var(&xs)),
            vec![(KPattern::AnyAtom, var(&xs)), (KPattern::Wild, run)],
        );
        Term::Let(
            xs,
            Shared::new(x),
            Shared::new(Term::Let(g, Shared::new(f), Shared::new(body))),
        )
    }
}
