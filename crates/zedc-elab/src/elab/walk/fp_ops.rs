//! The terms of the operations on one level of a family that plan row FP-ops-run builds into
//! zedc as `map` is: the folds `x >< op`, `x.reduce(op)` and `x.sum`; `foldl` and `foldr`; and
//! the quantifiers `.any`, `.all` and `.find` (step L3.15a). The serial ones walk the level in
//! key order with the kernel's entry steps (`firstEntry`, `entryAfter`, and from the far end
//! `lastEntry`, `entryBefore`), each frame of a `gen` holding the entry it reached. And the
//! string functions `split`, `lines` and `concat` (plan row FP-ops-strings), one kernel prim
//! each.

use std::sync::Arc;

use zed_kernel::term::{Evidence, Grade, GuardPos};
use zed_kernel::types::Type;
use zed_kernel::{Pattern as KPattern, Prim, Shared, Term, Universe, Value};
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

    /// The kernel `fold` by `p` of the one level of `family`, with the identity of the fold at
    /// `span` ([`Self::fold_identity`]); none for a fold with no identity there, which folds
    /// an empty level to `#empty`.
    pub(super) fn fold_one(&mut self, family: Term, p: Prim, span: Span) -> Term {
        let identity = self.fold_identity(span);
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

    /// `x.sum` on a type parameter, which the checker decided at each call ([`zedc_check::
    /// check::Info::generic_sums`]): a loose atom passes through, a tuple is summed by the
    /// prelude word of layer 1, and a family is folded by `(+)` as [`Self::member_fold`] folds
    /// it, with the identity of the fold at `span` in the body being made
    /// ([`Self::fold_identity`]). The checker accepts a tuple at a call only where
    /// `.sum` on that tuple is the word, and a family only where it is the fold, so the test
    /// picks the branch the call was checked by.
    // The test `is` the tuple universe also holds a keypath (`Value::Path`, `Universe::of`),
    // so a keypath checked as a family would take the tuple branch. No value a program's own
    // terms read is a keypath (TEST-generic-sum-branches), by the places one is made:
    // (a) the kernel's `reindex` passes one as the first argument of its key map and value
    // map, and `discard` as the first argument of its selector. The only such maps are built
    // by elaboration (`where_term`, `remap_term`, `group_term` in `walk.rs`), which bind that
    // argument to a temporary (`Elab::temp`) that no name in the source resolves to, and
    // read it only under `PathKey` and `PathLen`, which give one of its keys and its length.
    // (b) `Prim::Path` is written only as the body of such a key map, and the kernel takes
    // the key map's result apart into keys (`key_of`, `placed` in `eval.rs`). (c) The ZIR
    // readers make one only where the text or binary form holds one, which the writers give
    // only for a constant that was a keypath, and so by (a) and (b) only inside a key map.
    // That covers ZIR the writers made from checked terms, and no other: ZIR written by hand
    // or edited may hold a keypath anywhere, and the validator checks structure only, the
    // types of values being the checker's (DESIGN.md step L1.31), so a hand-made keypath
    // passed to this function takes the tuple branch. `Prim::Sum` then stops the run on it,
    // as it stops on a hand-made tuple of strings, and gives no value: the test
    // `l08_02_remaps::empty::a_keypath_written_into_zir_by_hand_stops_the_sum`.
    // So a keypath's keys are the only parts of it a program's terms see; a key is no
    // keypath, since a family's keys are the values its key maps and literals give, the
    // keys of a keypath among them, and so, by induction on the run, none is one. Hence the
    // receiver here, a value of the program's terms, is never a keypath.
    // Complexity tradeoff: the test `is` the tuple universe costs O(1) on a family (the
    // kernel's `Type::member` answers a family at its top) and O(k) on a tuple of k entries,
    // which `Prim::Sum` then reads in full, so the sum stays O(k) and the fold O(n). Naive, one
    // body elaborated per carrier the calls met: no test, but the body is copied once per kind
    // of call, and the program a library exports would depend on its callers.
    pub(super) fn generic_sum(&mut self, x: Term, span: Span) -> Term {
        let xs = self.temp();
        let fold = self.fold_one(var(&xs), Prim::Add, span);
        let tuples = Type::universe(Universe::Tuple);
        let body = Term::Match(
            Shared::new(var(&xs)),
            vec![
                (KPattern::AnyAtom, var(&xs)),
                (KPattern::Is(tuples), Term::Prim(Prim::Sum, vec![var(&xs)])),
                (KPattern::Wild, fold),
            ],
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

    /// `x.scan(op)` (step L5.3; DESIGN.md sec:reduction item 1): the family with `x`'s keys
    /// whose entry at the `i`-th key is the fold by `p` of the entries up to it, each such fold
    /// grouped as the kernel `fold` groups the whole level, by the canonical tree, so on floats
    /// too the last entry is `x >< op` and every entry is the fold of its prefix. The walk is
    /// a `gen` over the entries in key order; each frame is `(e, s, k, y)`: `e` the entry to
    /// take next, or `()` past the end; `s` the stack of the blocks the entries so far make;
    /// `k` and `y` the key of the entry just taken and the fold up to it. The result is the
    /// frames reindexed to `k -> y`. A loose atom `x` passes through, and an empty `x` is its
    /// own scan.
    // The canonical tree (DESIGN.md sec:reduction item 1; `CanonicalTree` in the kernel's
    // exact.rs) folds `n` entries as R(n) = R(n - p) ⊕ B(p), `p` the lowest set bit of `n`, and
    // a block of `2^j` entries as its left half ⊕ its right half. After `n` entries the stack
    // holds one block per set bit of `n`, the greatest at the bottom, each node
    // `(size, B, R, below)` with `B` the block's fold and `R` the fold of every entry up to
    // its end, R(n) for the top node. Taking entry `n + 1` pushes its leaf and merges the top
    // two blocks while their sizes are equal, which is the carry of adding 1 to `n`, so the
    // blocks are those of n + 1 with each merge `left ⊕ right`; then the new top's
    // `R = below.R ⊕ B` is R(n + 1) by the recurrence, since its block is B(p).
    // Complexity tradeoff: each entry costs one entry step, O(log n), and its merges; a merge
    // removes a block, so over the walk the merges number fewer than n, and the folds by `p`
    // fewer than 2n: O(n log n) with n outer frames and fewer than 2n inner ones. The naive
    // form, one kernel `fold` per prefix, gives the same values in O(n²) folds; a serial
    // left fold, O(n) folds, would round floats otherwise than `x >< op` does, against item 1.
    pub(super) fn scan_term(&mut self, x: Term, p: Prim) -> Term {
        let (xs, e0, n0, fr, n, gn, q, y) = (
            self.temp(),
            self.temp(),
            self.temp(),
            self.temp(),
            self.temp(),
            self.temp(),
            self.temp(),
            self.temp(),
        );
        let frame = |entry: Term, node: &Arc<str>| {
            tuple(vec![
                Term::Prim(Prim::EntryAfter, vec![var(&xs), entry.clone()]),
                var(node),
                part(entry, 0),
                part(var(node), 2),
            ])
        };
        let first = frame(var(&e0), &n0);
        let init = Term::Let(
            n0,
            Shared::new(self.scan_push(part(var(&e0), 1), tuple(Vec::new()), p)),
            Shared::new(first),
        );
        let entry = part(var(&fr), 0);
        let next = frame(entry.clone(), &n);
        let pushed = self.scan_push(part(entry.clone(), 1), part(var(&fr), 1), p);
        let step = Term::Let(n, Shared::new(pushed), Shared::new(next));
        let frames = Term::Gen {
            init: Shared::new(init),
            step: Shared::new(Term::Lam(vec![fr.clone()], Shared::new(step))),
            guard: Shared::new(Term::Lam(vec![fr], Shared::new(not_at_end(entry)))),
            pos: GuardPos::Before,
        };
        let scan = Term::Reindex {
            family: Shared::new(var(&gn)),
            kf: Shared::new(Term::Lam(
                vec![q.clone(), y.clone()],
                Shared::new(part(var(&y), 2)),
            )),
            vf: Shared::new(Term::Lam(vec![q, y.clone()], Shared::new(part(var(&y), 3)))),
            witness: zed_kernel::term::Witness::Residue,
        };
        let run = Term::Let(gn, Shared::new(frames), Shared::new(scan));
        let nonempty = Term::Match(
            Shared::new(var(&e0)),
            vec![
                (KPattern::Tuple(Vec::new()), var(&xs)),
                (KPattern::Wild, run),
            ],
        );
        let body = Term::Match(
            Shared::new(var(&xs)),
            vec![
                (KPattern::AnyAtom, var(&xs)),
                (
                    KPattern::Wild,
                    Term::Let(
                        e0,
                        Shared::new(Term::Prim(Prim::FirstEntry, vec![var(&xs)])),
                        Shared::new(nonempty),
                    ),
                ),
            ],
        );
        Term::Let(xs, Shared::new(x), Shared::new(body))
    }

    /// The stack of [`Self::scan_term`] after the leaf `v` is taken onto `stack`: a `gen`
    /// whose frames are `(size, B, below)`, from `(1, v, stack)`, each step folding the top
    /// node's block with `B`, `top.B ⊕ B` at twice the size, while the top's size is `size`;
    /// then the new node `(size, B, R, below)`, `R` being `B` on an empty stack and
    /// `below.R ⊕ B` on another.
    fn scan_push(&mut self, v: Term, stack: Term, p: Prim) -> Term {
        let (st, ig, m, below) = (self.temp(), self.temp(), self.temp(), self.temp());
        let op = |a: Term, b: Term| Term::Prim(p, vec![a, b]);
        let top = part(var(&st), 2);
        let step = tuple(vec![
            Term::Prim(Prim::Add, vec![part(var(&st), 0), part(var(&st), 0)]),
            op(part(top.clone(), 1), part(var(&st), 1)),
            part(top.clone(), 3),
        ]);
        let guard = Term::Match(
            Shared::new(top.clone()),
            vec![
                (KPattern::Tuple(Vec::new()), Term::Lit(Value::Bool(false))),
                (
                    KPattern::Wild,
                    Term::Prim(Prim::Eq, vec![part(top, 0), part(var(&st), 0)]),
                ),
            ],
        );
        let merges = Term::Gen {
            init: Shared::new(tuple(vec![int(1), v, stack])),
            step: Shared::new(Term::Lam(vec![st.clone()], Shared::new(step))),
            guard: Shared::new(Term::Lam(vec![st], Shared::new(guard))),
            pos: GuardPos::Before,
        };
        let block = part(var(&m), 1);
        let prefix = Term::Match(
            Shared::new(var(&below)),
            vec![
                (KPattern::Tuple(Vec::new()), block.clone()),
                (KPattern::Wild, op(part(var(&below), 2), block.clone())),
            ],
        );
        let node = tuple(vec![part(var(&m), 0), block, prefix, var(&below)]);
        Term::Let(
            ig.clone(),
            Shared::new(merges),
            Shared::new(Term::Let(
                m.clone(),
                Shared::new(last_frame(&ig)),
                Shared::new(Term::Let(
                    below,
                    Shared::new(part(var(&m), 2)),
                    Shared::new(node),
                )),
            )),
        )
    }

    /// `x.chunkBy(f)` (step L5.3; DESIGN.md sec:type_language, the `m.chunkBy(f)` row): the
    /// widening `reindex` `(k, v) ↦ ((run(k), k), v)`, `run` numbering from 0 the maximal runs
    /// of entries, in key order, at which `f` gives one value. The runs are found by a `gen`
    /// over the entries in key order; each frame is `(e, r, w, k, v)`: `e` the entry to take
    /// next, or `()` past the end; `k -> v` the entry just taken, `w` what `f` gives at it and
    /// `r` its run, the run before it when `w` is `==` to that entry's value, else the next.
    /// `==` takes an atom as data, as `group`'s keys do. A loose atom `x` passes through, and
    /// an empty `x` has no runs, so it is its own result.
    // Complexity tradeoff: n entry steps and one `reindex` of n frames, O(n log n), with one
    // call of `f` per entry. The naive form, a `group` by `f` and then a split of each group
    // where its keys are not adjacent, needs the rank of each key, O(n log n) too, with a
    // second pass.
    pub(super) fn chunk_by_term(&mut self, x: Term, f: Term) -> Term {
        let (xs, g, e0, fr, w, gn, q, y) = (
            self.temp(),
            self.temp(),
            self.temp(),
            self.temp(),
            self.temp(),
            self.temp(),
            self.temp(),
            self.temp(),
        );
        let frame = |entry: Term, run: Term| {
            tuple(vec![
                Term::Prim(Prim::EntryAfter, vec![var(&xs), entry.clone()]),
                run,
                var(&w),
                part(entry.clone(), 0),
                part(entry, 1),
            ])
        };
        let gives = |entry: Term| Term::App(Shared::new(var(&g)), vec![part(entry, 1)]);
        let init = Term::Let(
            w.clone(),
            Shared::new(gives(var(&e0))),
            Shared::new(frame(var(&e0), int(0))),
        );
        let entry = part(var(&fr), 0);
        let run = part(var(&fr), 1);
        let same = Term::Prim(Prim::Eq, vec![var(&w), part(var(&fr), 2)]);
        let next_run = Term::Match(
            Shared::new(same),
            vec![
                (KPattern::Lit(Value::Bool(true)), run.clone()),
                (KPattern::Wild, Term::Prim(Prim::Add, vec![run, int(1)])),
            ],
        );
        let step = Term::Let(
            w.clone(),
            Shared::new(gives(entry.clone())),
            Shared::new(frame(entry.clone(), next_run)),
        );
        let frames = Term::Gen {
            init: Shared::new(init),
            step: Shared::new(Term::Lam(vec![fr.clone()], Shared::new(step))),
            guard: Shared::new(Term::Lam(vec![fr], Shared::new(not_at_end(entry)))),
            pos: GuardPos::Before,
        };
        let key = Term::Prim(Prim::Path, vec![part(var(&y), 1), part(var(&y), 3)]);
        let chunks = Term::Reindex {
            family: Shared::new(var(&gn)),
            kf: Shared::new(Term::Lam(vec![q.clone(), y.clone()], Shared::new(key))),
            vf: Shared::new(Term::Lam(vec![q, y.clone()], Shared::new(part(var(&y), 4)))),
            witness: zed_kernel::term::Witness::Residue,
        };
        let run = Term::Let(gn, Shared::new(frames), Shared::new(chunks));
        let nonempty = Term::Match(
            Shared::new(var(&e0)),
            vec![
                (KPattern::Tuple(Vec::new()), var(&xs)),
                (KPattern::Wild, run),
            ],
        );
        let body = Term::Match(
            Shared::new(var(&xs)),
            vec![
                (KPattern::AnyAtom, var(&xs)),
                (
                    KPattern::Wild,
                    Term::Let(
                        e0,
                        Shared::new(Term::Prim(Prim::FirstEntry, vec![var(&xs)])),
                        Shared::new(nonempty),
                    ),
                ),
            ],
        );
        Term::Let(
            xs,
            Shared::new(x),
            Shared::new(Term::Let(g, Shared::new(f), Shared::new(body))),
        )
    }
}

/// The tuple of `parts`.
fn tuple(parts: Vec<Term>) -> Term {
    Term::Prim(Prim::Tuple, parts)
}

/// The prim of `split`, `lines` or `concat` (plan row FP-ops-strings), by its prelude word.
pub(super) fn strings_prim(word: &str) -> Option<Prim> {
    match word {
        "split" => Some(Prim::Split),
        "lines" => Some(Prim::Lines),
        "concat" => Some(Prim::Join),
        _ => None,
    }
}

/// `split(s, sep)`, `lines(s)` or `concat(pieces, sep: s)` (plan row FP-ops-strings, step
/// L3.2), from the operands in that order, the receiver of `x.w(…)` first: the kernel's prim,
/// with `sep` `""` when `concat` is given none. The checker accepted only these shapes. A loose
/// atom operand passes through the prim, as through any.
pub(super) fn strings_term(p: Prim, mut args: Vec<Term>) -> Term {
    if p == Prim::Join && args.len() == 1 {
        args.push(Term::Lit(Value::str("")));
    }
    Term::Prim(p, args)
}
