//! Remaps `m as (b1 -> … -> bn -> v) into (e1 -> … -> ek -> leaf)` (DESIGN.md
//! sec:remap_law): the binders name the source's key levels and its value, each output level's
//! key is an expression over them, and the leaf is the value kept, `_` to drop the values, or a
//! trailing key binder, sugar for `… -> bk -> _`. A level written `e >< (op)` is folded. The
//! keypath map must be one-to-one by the witness catalog (sec:grouping), or the remap must
//! truncate or fold; otherwise the remap is rejected with the menu of the diagnostics row
//! "Collision (T-Reindex)".

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

use crate::check::*;
use zedc_base::rejection::{Row, not_yet};
use zedc_syntax::ast::{RemapLevel, Target};

/// A remap whose source is checked or being checked: its levels' keys and leaf are checked one
/// after another with the binders in scope.
pub(in crate::check) struct RemapF<'a> {
    e: &'a Expr,
    binders: &'a [Target],
    levels: &'a [RemapLevel],
    /// Whether the source's type is in hand.
    sourced: bool,
    /// The source's key types, outermost first, then its value type; `None` where the source
    /// is not a family of as many levels as the pattern names, an error already given.
    src: Option<Vec<Ty>>,
    /// The type of each level's expression checked so far, in level order, `None` for `_`.
    tys: Vec<Option<Ty>>,
    /// The key binders by binding id, each to its place in the pattern: one lookup per name
    /// read in a key, where a scan of the binders would make a pattern of n levels O(n²).
    keys: HashMap<usize, usize>,
}

/// An atom of a key expression's linear form: key binder `i`, whole or its component `j`.
type Atom = (usize, Option<usize>);

/// A linear form over atoms with integer coefficients; the constant term is dropped, since a
/// shift does not change whether a map is one-to-one.
type Lin = BTreeMap<Atom, BigInt>;

/// Why a remap's keypath map is not shown one-to-one: the key binders it loses, in source
/// order, and the key expression the catalog refused, if a key expression transforms a key.
struct Lost<'a> {
    missing: Vec<usize>,
    culprit: Option<(&'a Expr, String)>,
}

/// What the walk in walk.rs does next for a remap: check the key expression of the next level
/// with the remap kept on its stack, or take the remap's type.
pub(in crate::check) enum RemapNext<'a> {
    Key(Box<RemapF<'a>>, &'a Expr),
    Done(Ty),
}

/// `Ck::reduce_end`, the fold of a family's level by an operator, passed in by walk.rs.
// Tradeoff: walk.rs imports this file for `RemapF`, so this file names nothing of walk.rs:
// a cycle between files is refused (DESIGN.md sec:units; the import graph of step S.1f), and
// a Zed port makes each file a unit. walk.rs drives the walk machine (`M`, `Frame`, `Job`)
// from `RemapNext` and passes its methods in as functions; moving `Frame` to a file of its
// own would not help, since `Frame::Remap` holds a `RemapF`. The cost is one indirect call
// per folded level or `group`. The graph also counts a call whose receiver it cannot type
// (`binders.len()`, `"residue".into()`) as a call of every method of that name written in
// walk.rs for a type of mod.rs; so the methods of `Args` are written with `Args` in mod.rs,
// and the method of `Ck` that checks a value passed into a parameter is `passes_into`, not
// `into`.
pub(in crate::check) type ReduceEnd<'t, 'a> = fn(&mut Ck<'t, 'a>, Reducer, &Ty, Span) -> Ty;

/// `Ck::apply`, the application of a signature to arguments, passed in by walk.rs as
/// `ReduceEnd` is.
pub(in crate::check) type Apply<'t, 'a> =
    fn(&mut Ck<'t, 'a>, Label<'_>, &Sig, Vec<Option<Arg<'a>>>, bool, Span) -> (Ty, Vec<usize>);

impl<'t, 'a> Ck<'t, 'a> {
    /// Starts the check of the remap `e`: the remap's state and its source, which walk.rs checks
    /// first.
    pub(super) fn remap_start(&mut self, e: &'a Expr) -> (Box<RemapF<'a>>, &'a Expr) {
        let ExprKind::Remap {
            of,
            binders,
            levels,
        } = &e.kind
        else {
            unreachable!("a remap")
        };
        let Some(binders) = binders else {
            unreachable!(
                "name resolution refuses an `into` without `as`, which binds by level name"
            )
        };
        let levels = levels.as_deref().unwrap_or(&[]);
        let n = binders.len().saturating_sub(1);
        let keys = (binders[..n].iter().enumerate())
            .filter_map(|(i, b)| match b {
                Target::Name(name, span) => Some((self.id(*span, name), i)),
                Target::Wild => None,
            })
            .collect();
        let s = RemapF {
            e,
            binders,
            levels,
            sourced: false,
            src: None,
            tys: Vec::new(),
            keys,
        };
        (Box::new(s), of)
    }

    /// The next step of the remap `s`, `t` the type of its source or of its last level.
    pub(super) fn remap_step(
        &mut self,
        mut s: Box<RemapF<'a>>,
        t: Ty,
        reduce: ReduceEnd<'t, 'a>,
    ) -> RemapNext<'a> {
        if !s.sourced {
            s.sourced = true;
            s.src = self.remap_source(&s, &t);
            let src = s.src.clone();
            for (b, ty) in s.binders.iter().zip(src.into_iter().flatten()) {
                if let Target::Name(name, span) = b {
                    let id = self.id(*span, name);
                    self.env.insert(id, ty);
                }
            }
            // `as` alone is the identity remap, which only names the levels.
            if s.levels.is_empty() {
                return RemapNext::Done(if s.src.is_some() { t } else { Ty::empty() });
            }
        } else {
            let at = s.tys.len();
            s.tys.push(s.levels[at].key.is_some().then_some(t));
        }
        while let Some(l) = s.levels.get(s.tys.len()) {
            match &l.key {
                Some(k) => {
                    return RemapNext::Key(s, k);
                }
                None => s.tys.push(None),
            }
        }
        let t = self.remap_end(&s, reduce);
        RemapNext::Done(t.unwrap_or_else(Ty::empty))
    }

    /// The source's key types, outermost first, then its value type, when `t`, the source's
    /// type, is a family of as many key levels as the remap `s` binds; else an error.
    fn remap_source(&mut self, s: &RemapF<'a>, t: &Ty) -> Option<Vec<Ty>> {
        let ExprKind::Remap { of, .. } = &s.e.kind else {
            unreachable!("a remap")
        };
        let n = s.binders.len() - 1;
        if n == 0 {
            self.error(
                s.e.span,
                "a remap's `as` pattern names the source's key levels and then its value, as \
                 `m as (k -> v)`",
            );
            return None;
        }
        let misses = &KType::atom("notFound") | &KType::atom("outOfBounds");
        let mut out = Vec::with_capacity(n + 1);
        let mut cur = t.clone();
        for depth in 0..n {
            if cur.dynamic && cur.fns.is_empty() {
                out.extend((depth..=n).map(|_| Ty::dynamic()));
                return Some(out);
            }
            let rest = cur.pieces().into_iter().any(|p| match p {
                Piece::Fn(sig) => !sig.data,
                Piece::Set(k) => !(&k - &misses).is_empty(),
                _ => true,
            });
            let fams = cur.fns.iter().filter(|g| g.data).collect::<Vec<_>>();
            if fams.is_empty() || rest {
                let shown = self.text(t);
                let msg = match depth {
                    0 => format!(
                        "a remap rearranges the keys of a family, and its source `{}` is {shown}",
                        self.src_text(of.span)
                    ),
                    _ => format!(
                        "this remap's `as` pattern names {n} key levels, and its source `{}`, \
                         {shown}, has {depth} at some keys",
                        self.src_text(of.span)
                    ),
                };
                self.error(of.span, msg);
                return None;
            }
            let keys = fams
                .iter()
                .flat_map(|g| g.arrows.iter().map(|a| &a.params[0]));
            let next = fams.iter().flat_map(|g| g.arrows.iter().map(|a| &a.result));
            out.push(Ty::union_all(keys));
            cur = Ty::union_all(next).without(&misses);
        }
        if cur.fns.iter().any(|g| g.data) {
            // Plan row REMAP-fewer-binders: binding a whole inner family as the value needs a
            // reindex over keypaths that stop above the leaves.
            self.error(
                s.e.span,
                not_yet(&format!(
                    "a remap whose `as` pattern names {n} key levels of a source with more"
                )),
            );
            return None;
        }
        out.push(cur);
        Some(out)
    }

    /// The source text at `span`, or nothing where the checker has no text.
    fn src_text(&self, span: Span) -> String {
        self.t
            .text
            .and_then(|t| t.get(span.start..span.end))
            .unwrap_or_default()
            .to_string()
    }

    /// The key binder `e` names, by its place in the `as` pattern of `s`.
    fn key_binder(&self, s: &RemapF<'a>, e: &Expr) -> Option<usize> {
        let ExprKind::Name(_) = &e.kind else {
            return None;
        };
        let Some(Ref::Bound(ids)) = self.t.res.uses.get(&e.span) else {
            return None;
        };
        if ids.len() != 1 {
            return None;
        }
        s.keys.get(&ids[0]).copied()
    }

    /// Whether `e` names the value binder of `s`.
    fn value_binder(&self, s: &RemapF<'a>, e: &Expr) -> bool {
        let (ExprKind::Name(_), Some(Target::Name(name, span))) = (&e.kind, s.binders.last())
        else {
            return false;
        };
        matches!(self.t.res.uses.get(&e.span), Some(Ref::Bound(ids)) if ids.len() == 1 && ids[0] == self.id(*span, name))
    }

    /// The remap `s` with every level checked: its type, and its plan in [`Info::remaps`].
    fn remap_end(&mut self, s: &RemapF<'a>, reduce: ReduceEnd<'t, 'a>) -> Option<Ty> {
        let src = s.src.as_ref()?;
        let last = s.levels.len() - 1;
        let leaf = &s.levels[last];
        let sugar = leaf.reduce.is_none()
            && (leaf.key.as_ref()).is_some_and(|k| self.key_binder(s, k).is_some());
        let truncate = leaf.key.is_none() || sugar;
        let keys: Vec<usize> = match sugar {
            true => (0..=last).collect(),
            false => (0..last).collect(),
        };
        if let Some(l) = s.levels[..last].iter().find(|l| l.key.is_none()) {
            self.error(
                l.span,
                "`_` stands only at the leaf of an `into` pattern, where it drops the values",
            );
            return None;
        }
        if leaf.reduce.is_some() && !sugar {
            self.error(
                leaf.span,
                "`><` folds a key level, and the last level of an `into` pattern is its leaf, the \
                 value kept",
            );
            return None;
        }
        if keys.is_empty() {
            self.error(
                s.e.span,
                "an `into` pattern keeps at least one key level before its leaf, as `into (k -> v)`",
            );
            return None;
        }
        if truncate && let Some(l) = s.levels.iter().find(|l| l.reduce.is_some()) {
            self.error(
                l.span,
                "this remap drops the values with its leaf, so there are none for `><` to fold",
            );
            return None;
        }
        let witness: Arc<str> = match truncate {
            true => "residue".into(),
            false => match self.injective(s, &keys, src) {
                Ok(w) => w,
                Err(lost) => {
                    self.collision(s, &keys, lost);
                    return None;
                }
            },
        };
        let ty = |j: usize| s.tys[j].clone().expect("a key level's type");
        let (kept, folded): (Vec<usize>, Vec<usize>) =
            (keys.iter()).partition(|&&j| s.levels[j].reduce.is_none());
        let mut folds = HashMap::new();
        let mut inner = match truncate {
            true => {
                let k = ty(*kept.last().expect("a kept level"));
                family(k.clone(), k)
            }
            false => s.tys[last].clone().expect("the leaf's type"),
        };
        for &j in folded.iter().rev() {
            let op = match s.levels[j].reduce.as_ref().map(|r| &r.kind) {
                Some(ExprKind::Section(op, _)) => *op,
                _ => unreachable!("name resolution refuses a `><` by a function"),
            };
            folds.insert(j, op);
            inner = reduce(
                self,
                Reducer::Op(op),
                &family(ty(j), inner),
                s.levels[j].span,
            );
        }
        let outer = match truncate {
            true => &kept[..kept.len() - 1],
            false => &kept[..],
        };
        for &j in outer.iter().rev() {
            inner = family(ty(j), inner);
        }
        let order = kept.iter().chain(&folded).copied().collect();
        self.info.remaps.insert(
            s.e.span,
            RemapPlan {
                order,
                kept: kept.len(),
                folds,
                leaf: (!truncate).then_some(last),
                witness,
            },
        );
        Some(inner)
    }

    /// The catalog entries that show the keypath map of the key levels `keys` of `s` one-to-one
    /// (sec:grouping), named as the kernel's reindex records them, or what it loses.
    ///
    /// The entries read here: literal key occurrence; tupling and permutation, a tuple key's
    /// components each recovered; integer affine maps of full column rank, which include the
    /// strictly monotone `k + 1` and `2*k`, the skew `(i, i + j)` and componentwise maps; `k mod
    /// p` on at most `p` contiguous integers; the pair `(k div s, k mod s)`; and affine packing
    /// `k1*s + k2` with each stride above the span of the keys beneath it. An exact-number key
    /// is read as an affine atom; a float key only where it occurs whole, since float arithmetic
    /// rounds. Any other key expression, and the value binder, recover no key (widening).
    // Complexity tradeoff: the affine entries are decided together by Gaussian elimination
    // over the integers, fraction-free, on the c key components and a atoms of the pattern:
    // O(c·a·min(c, a)) operations on integers of the pattern's coefficients. A naive test of
    // each subset of components for a unit vector would be exponential in c; the elimination
    // finds every atom the components determine at once. The pattern is program text, so c
    // and a are bounded by its length.
    fn injective(
        &mut self,
        s: &RemapF<'a>,
        keys: &[usize],
        src: &[Ty],
    ) -> Result<Arc<str>, Lost<'a>> {
        let mut comps = Vec::new();
        for &j in keys {
            let mut todo = vec![s.levels[j].key.as_ref().expect("a key level")];
            while let Some(e) = todo.pop() {
                match &e.kind {
                    ExprKind::Tuple(items) => todo.extend(items.iter().rev()),
                    _ => comps.push(e),
                }
            }
        }
        let mut rows: Vec<Lin> = Vec::new();
        let mut entries: Vec<&str> = Vec::new();
        let note = |entries: &mut Vec<&str>, name: &'static str| {
            if !entries.contains(&name) {
                entries.push(name);
            }
        };
        let mut divs: Vec<(usize, BigInt, &'a Expr)> = Vec::new();
        let mut mods: Vec<(usize, BigInt)> = Vec::new();
        for &c in &comps {
            if self.value_binder(s, c) {
                continue;
            }
            if let Some(i) = self.key_binder(s, c) {
                rows.push(Lin::from([((i, None), BigInt::one())]));
                note(&mut entries, "literal");
                continue;
            }
            if let ExprKind::Binary(op @ (BinaryOp::Mod | BinaryOp::IntDiv), x, p) = &c.kind
                && let Some(i) = self.key_binder(s, x)
                && let Some(p) = int_literal(p).filter(BigInt::is_positive)
                && self.subtype(&src[i], &Ty::carrier(Carrier::Int))
            {
                match op {
                    BinaryOp::Mod => {
                        if span_of(&src[i]).is_some_and(|w| w < p) {
                            rows.push(Lin::from([((i, None), BigInt::one())]));
                            note(&mut entries, "modulo");
                        }
                        mods.push((i, p));
                    }
                    _ => divs.push((i, p, c)),
                }
                continue;
            }
            let Some(lin) = self.linear(s, c, src) else {
                continue;
            };
            if lin.is_empty() {
                continue;
            }
            let whole = lin.len() == 1 && lin.values().all(|v| v.abs().is_one());
            match whole && lin.keys().all(|a| a.1.is_some()) && is_index(c) {
                true => note(&mut entries, "tupling"),
                false => note(&mut entries, "affine"),
            }
            if lin.len() > 1 && self.packs(&lin, src) {
                rows.extend(lin.keys().map(|&a| Lin::from([(a, BigInt::one())])));
                note(&mut entries, "packing");
            }
            rows.push(lin);
        }
        for (i, p, _) in &divs {
            if mods.contains(&(*i, p.clone())) {
                rows.push(Lin::from([((*i, None), BigInt::one())]));
                note(&mut entries, "divmod");
            }
        }
        let got = recovered(rows);
        let n = s.binders.len() - 1;
        let missing = (0..n)
            .filter(|&i| {
                if got.contains(&(i, None)) {
                    return false;
                }
                let arity = tuple_arity(&src[i]);
                !arity.is_some_and(|a| (0..a).all(|j| got.contains(&(i, Some(j)))))
            })
            .collect::<Vec<_>>();
        if missing.is_empty() {
            if entries.is_empty() {
                entries.push("literal");
            }
            return Ok(entries.join("+").into());
        }
        let transforms = comps
            .iter()
            .filter(|c| !self.value_binder(s, c) && self.key_binder(s, c).is_none())
            .copied()
            .collect::<Vec<_>>();
        let culprit = (transforms.iter())
            .find(|c| missing.iter().any(|&i| self.mentions(s, c, i)))
            .or(transforms.first())
            .map(|&c| (c, self.nearest(s, c, src)));
        Err(Lost { missing, culprit })
    }

    /// The linear form of the key expression `e` over the key binders of `s`, when it is one:
    /// a binder, a component `b[j]` of one, an integer literal, or a sum, difference, negation
    /// or literal multiple of these, with every atom an exact number where arithmetic is
    /// applied.
    fn linear(&self, s: &RemapF<'a>, e: &Expr, src: &[Ty]) -> Option<Lin> {
        let (lin, _) = self.affine(s, e)?;
        let arithmetic = !matches!(e.kind, ExprKind::Name(_) | ExprKind::Index(..));
        let exact = |a: &Atom| {
            let t = atom_type(&src[a.0], a.1);
            self.subtype(&t, &Ty::carrier(Carrier::Int))
                || self.subtype(&t, &Ty::carrier(Carrier::Rat))
        };
        (!arithmetic || lin.keys().all(exact)).then_some(lin)
    }

    /// The linear form and constant of `e`, read structurally (see [`Self::linear`]).
    fn affine(&self, s: &RemapF<'a>, e: &Expr) -> Option<(Lin, BigInt)> {
        if let Some(i) = self.key_binder(s, e) {
            return Some((Lin::from([((i, None), BigInt::one())]), BigInt::zero()));
        }
        match &e.kind {
            ExprKind::Int { .. } => Some((Lin::new(), int_literal(e)?)),
            ExprKind::Index(b, j) => {
                let i = self.key_binder(s, b)?;
                let j = usize::try_from(int_literal(j)?).ok()?;
                Some((Lin::from([((i, Some(j)), BigInt::one())]), BigInt::zero()))
            }
            ExprKind::Unary(UnaryOp::Neg, x) => {
                let (l, c) = self.affine(s, x)?;
                Some((scale(l, &BigInt::from(-1)), -c))
            }
            ExprKind::Binary(op @ (BinaryOp::Add | BinaryOp::Sub), x, y) => {
                let (mut l, c) = self.affine(s, x)?;
                let (r, d) = self.affine(s, y)?;
                let sign = BigInt::from(if *op == BinaryOp::Add { 1 } else { -1 });
                for (a, v) in scale(r, &sign) {
                    let sum = l.remove(&a).unwrap_or_default() + v;
                    if !sum.is_zero() {
                        l.insert(a, sum);
                    }
                }
                Some((l, c + sign * d))
            }
            ExprKind::Binary(BinaryOp::Mul, x, y) => {
                let ((l, c), (r, d)) = (self.affine(s, x)?, self.affine(s, y)?);
                match (l.is_empty(), r.is_empty()) {
                    (true, _) => Some((scale(r, &c), c * d)),
                    (_, true) => Some((scale(l, &d), c * d)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Whether the linear form `lin` packs its atoms by affine packing (sec:grouping): each an
    /// integer whose type lists its values, and, in order of their strides' magnitudes, each
    /// stride above the sum of the spans of the atoms beneath it, each span times its stride.
    fn packs(&self, lin: &Lin, src: &[Ty]) -> bool {
        let mut strides = Vec::with_capacity(lin.len());
        for (a, v) in lin {
            let t = atom_type(&src[a.0], a.1);
            if !self.subtype(&t, &Ty::carrier(Carrier::Int)) {
                return false;
            }
            let Some(w) = span_of(&t) else { return false };
            strides.push((v.abs(), w));
        }
        strides.sort();
        let mut beneath = BigInt::zero();
        for (stride, w) in strides {
            if stride <= beneath {
                return false;
            }
            beneath += stride * w;
        }
        true
    }

    /// Whether the expression `e` reads the key binder `i` of `s`.
    fn mentions(&self, s: &RemapF<'a>, e: &'a Expr, i: usize) -> bool {
        let mut todo = vec![e];
        while let Some(e) = todo.pop() {
            if self.key_binder(s, e) == Some(i) {
                return true;
            }
            super::super::blocking::kids(&e.kind, &mut |k| todo.push(k));
        }
        false
    }

    /// The catalog entry nearest the refused key expression `e`, and why it fails.
    fn nearest(&mut self, s: &RemapF<'a>, e: &'a Expr, src: &[Ty]) -> String {
        if let ExprKind::Binary(op @ (BinaryOp::Mod | BinaryOp::IntDiv), x, p) = &e.kind
            && let Some(i) = self.key_binder(s, x)
        {
            let (k, p) = (self.src_text(x.span), self.src_text(p.span));
            let shown = self.text(&src[i]);
            return match op {
                BinaryOp::Mod => format!(
                    "the nearest entry of the witness catalog, `k mod p` on at most `p` \
                     contiguous integers, does not apply: `{k}` is {shown}, more than {p} \
                     integers or not listed by its type."
                ),
                _ => format!(
                    "`{k} div {p}` sends {p} keys to each value; the nearest entry of the \
                     witness catalog is the pair `({k} div {p}, {k} mod {p})`."
                ),
            };
        }
        if self.affine(s, e).is_some_and(|(l, _)| l.len() > 1) {
            return format!(
                "the nearest entries of the witness catalog, integer affine maps of full column \
                 rank and affine packing with each stride above the span of the keys beneath it, \
                 do not apply to `{}`.",
                self.src_text(e.span)
            );
        }
        format!(
            "no entry of the witness catalog shows `{}` one-to-one; the nearest is a function \
             proved one-to-one.",
            self.src_text(e.span)
        )
    }

    /// Rejects the remap `s`, whose key levels `keys` lose the keys `lost`, with the menu of
    /// the diagnostics row "Collision (T-Reindex)" (DESIGN.md sec:remap_law, the worked
    /// collision; sec:diagnostics).
    fn collision(&mut self, s: &RemapF<'a>, keys: &[usize], lost: Lost<'a>) {
        let last = s.levels.len() - 1;
        let level = |j: usize| self.src_text(s.levels[j].span);
        let key = |j: usize| self.src_text(s.levels[j].key.as_ref().expect("a key").span);
        let names = |i: usize| match &s.binders[i] {
            Target::Name(n, _) => n.clone(),
            Target::Wild => "_".to_string(),
        };
        let written = keys.iter().map(|&j| level(j)).collect::<Vec<_>>();
        let leaf = level(last);
        let lost_names = lost.missing.iter().map(|&i| names(i)).collect::<Vec<_>>();
        let into = |extra: &[String], leaf: &str| {
            let all = (written.iter().cloned())
                .chain(extra.iter().cloned())
                .chain([leaf.to_string()]);
            format!("into ({})", all.collect::<Vec<_>>().join(" -> "))
        };
        let folded = lost_names
            .iter()
            .map(|n| format!("{n} >< op"))
            .collect::<Vec<_>>();
        let (orig, trunc) = (into(&[], &leaf), into(&lost_names, "_"));
        let (resid, fold) = (into(&lost_names, &leaf), into(&folded, &leaf));
        let one = |xs: Vec<String>| match xs.len() {
            1 => xs.into_iter().next().expect("one"),
            _ => format!("({})", xs.join(", ")),
        };
        let each = one(lost_names.clone());
        let merges = match keys.last() {
            Some(&j) => format!("merges each {}'s values", key(j)),
            None => "merges the values".to_string(),
        };
        let line = |label: &str, text: &str| format!("\n  {label:<29}{text}");
        let msg = match &lost.culprit {
            None => {
                let from = one((0..s.binders.len() - 1).map(names).collect());
                let onto = one(keys.iter().map(|&j| key(j)).collect());
                format!(
                    "Cannot map many values to one key: `{orig}`. Try `{trunc}` instead.\n  the \
                     `{from}` keypaths collapse onto `{onto}`, but their values survive.{}\n      \
                     keeps each {each} and drops its value{}\n      keeps each value under its \
                     {each}{}\n      {merges} with op, which must be associative",
                    line("drop the values too:", &trunc),
                    line("or keep the inner key:", &resid),
                    line("or say how the values merge:", &fold),
                )
            }
            Some((e, nearest)) => {
                let text = self.src_text(e.span);
                format!(
                    "Cannot show that `{text}` keeps the keys of `{each}` apart: `{orig}`. Try \
                     `{resid}` instead.\n  {nearest}{}\n      keeps each value under its \
                     {each}{}\n      keeps each {each} and drops its value{}\n      {merges} \
                     with op, which must be associative{}{}",
                    line("write the residue:", &resid),
                    line("or drop the values too:", &trunc),
                    line("or say how the values merge:", &fold),
                    line(
                        "or supply a witness:",
                        &format!(
                            "prove `{text}` one-to-one; an `@injective` claim counts only at \
                             proof grade"
                        ),
                    ),
                    line(
                        "or write the check:",
                        "`group` by the key, then a fold that keeps each key's one value and \
                         gives `#collision` where there are more",
                    ),
                )
            }
        };
        self.rejects_with(Row::Collision, s.e.span, msg, Vec::new());
    }

    /// `x.flatMap(f)` (DESIGN.md sec:grouping, "Multiple emissions are typed, not repaired";
    /// the bound table's `flatMap` row): on a family `K -> V0` whose function gives a family
    /// for each entry, the family `K -> (R -> V)`, the emitted list adjoined as an inner rank level
    /// under each key, possibly empty and never a missing key. The type is `t`, that of
    /// `x.map(f)`, which walk.rs gives, `at` the span of `f`;
    /// what `flatMap` adds is the demand that every entry's result be a list, a family whose
    /// keys are `0..<n` (sec:grouping: "`flatMap` on `K -> V0` with body `V0 -> Seq(V)` yields
    /// `K -> rank -> V`"; sec:verification's `R.flatMap(s -> choices.map(c -> step(s, c)))`
    /// maps over a list). A family with other keys is rejected, `map` being the word that keeps
    /// them.
    // Complexity tradeoff: one pass over the result type of `map_end`, O(arrows); no second
    // check of `f`.
    pub(super) fn flat_map_end(&mut self, t: Ty, at: Span) -> Ty {
        let misses = &KType::atom("notFound") | &KType::atom("outOfBounds");
        for p in t.pieces() {
            let Piece::Fn(sig) = p else { continue };
            if !sig.data {
                continue;
            }
            let all = Ty::union_all(sig.arrows.iter().map(|a| &a.result)).without(&misses);
            let entries = all.without_loose();
            // A dynamic entry, or one of a class not yet resolved, is checked where it is known.
            let families = (entries.pieces().iter()).all(|q| {
                matches!(q, Piece::Fn(s) if s.data && s.dense)
                    || matches!(q, Piece::Dyn | Piece::Var(_))
            });
            if !families {
                let shown = self.text(&entries);
                self.error_offering(
                    at,
                    format!(
                        "`flatMap` adjoins the list its function gives for each entry as a rank \
                         level, and this function gives {shown}"
                    ),
                    [
                        "repair: give a list for each entry, as `x -> [x, x + 1]`".to_string(),
                        "repair: use `map`, which keeps one value per entry, or the keys of a family \
                         it gives".to_string(),
                    ],
                );
                return Ty::empty();
            }
        }
        t
    }

    /// `x.group(f)` (DESIGN.md sec:grouping, the bound table's `group` row): on a family
    /// `K -> V` of one level, the family `W ->? (K -> V)`, `W` the type of `f` applied to `V`;
    /// each entry `k -> v` goes to `f(v) -> k -> v`, the remap `as (k -> v) into (f(v) -> k ->
    /// v)`, one-to-one by tupling since the key `k` is kept. With `rekey`, `x.rekey(f)` claims
    /// that `f` keeps the entries apart, and no witness of the catalog this step builds reads a
    /// key made from a value alone, so it is rejected with the menu of the diagnostics row
    /// "Collision (T-Reindex)": `group`, a witness, or the check.
    // Complexity tradeoff: the type is built from the union of the family's arrows, O(arrows),
    // as `map` does; the outer level's guarantee, the classes `f(m[k])` known statically, is
    // not computed (empty), which the bound table allows ("else empty").
    pub(super) fn group_end(
        &mut self,
        x: &Ty,
        recv: Span,
        f: Arg<'a>,
        span: Span,
        rekey: bool,
        apply: Apply<'t, 'a>,
    ) -> Ty {
        let word = if rekey { "rekey" } else { "group" };
        if rekey {
            let (r, g) = (self.src_text(recv), self.src_text(f.at.unwrap_or(span)));
            let call = format!("{r}.group({g})");
            let line = |label: &str, text: &str| format!("\n  {label:<29}{text}");
            let msg = format!(
                "Cannot show that `{g}` keeps the entries of `{r}` apart: `{r}.rekey({g})`. Try \
                 `{call}` instead.\n  two entries of `{r}` could give one key, and no witness \
                 of the catalog reads a key made from a value alone.{}\n      keeps each \
                 entry under its key in `{r}`, one level deeper{}{}",
                line("use group:", &call),
                line(
                    "or supply a witness:",
                    &format!(
                        "prove `{g}` one-to-one; an `@injective` claim counts only at proof grade"
                    ),
                ),
                line(
                    "or write the check:",
                    &format!(
                        "`{call}`, then a fold that keeps each key's one value and gives \
                         `#collision` where there are more"
                    ),
                ),
            );
            self.rejects_with(Row::Collision, span, msg, Vec::new());
            return Ty::empty();
        }
        if x.dynamic && x.fns.is_empty() {
            return Ty::dynamic();
        }
        let Some(fsig) = only_fn(&f.ty) else {
            let t = self.text(&f.ty);
            self.error_offering(
                f.at.unwrap_or(span),
                format!("`{word}` takes a function, and this value is {t}"),
                ["repair: pass a function of one parameter, as `x -> x.lower`".to_string()],
            );
            return Ty::empty();
        };
        let misses = &KType::atom("notFound") | &KType::atom("outOfBounds");
        let fams = x.fns.iter().filter(|g| g.data).collect::<Vec<_>>();
        let rest = x.pieces().into_iter().any(|p| match p {
            Piece::Fn(sig) => !sig.data,
            Piece::Set(k) => !(&k - &misses).is_empty(),
            _ => true,
        });
        if fams.is_empty() || rest {
            let t = self.text(x);
            self.error_offering(
                span,
                format!(
                    "`group` works on the entries of a family, and `{}` is {t}",
                    self.src_text(recv)
                ),
                [
                    "repair: call `group` on a family, as `[\"a\", \"B\"].group(w -> w.lower)`"
                        .to_string(),
                ],
            );
            return Ty::empty();
        }
        let keys = Ty::union_all(
            fams.iter()
                .flat_map(|g| g.arrows.iter().map(|a| &a.params[0])),
        );
        let values = Ty::union_all(fams.iter().flat_map(|g| g.arrows.iter().map(|a| &a.result)))
            .without(&misses);
        if values.fns.iter().any(|g| g.data) {
            // Plan row GROUP-nested: the kernel's reindex walks leaves, and `f` takes the whole
            // inner family `m[k]`; that needs a reindex over keypaths that stop above the
            // leaves, as REMAP-fewer-binders does.
            self.error(
                span,
                not_yet("`group` on a family whose entries are families"),
            );
            return Ty::empty();
        }
        let what = Label::Text("the function given to `group`");
        let w = apply(
            self,
            what,
            &fsig,
            vec![Some(Arg::of(values.clone()))],
            false,
            span,
        )
        .0;
        family(w, family(keys, values))
    }
}

/// A family `keys ->? values` that guarantees no key: its one arrow's result holds
/// `#notFound`, so a read of any key of `keys` may miss. A remap or `group` result holds only
/// the keys its entries reach, which the key type over-approximates; the guarantee is the
/// bound table's "else empty" (DESIGN.md sec:type_language), sound but not tight: a transpose
/// of a full rectangle has every key, and that tighter guarantee is not computed.
fn family(keys: Ty, values: Ty) -> Ty {
    let values = values.union(&Ty::set(KType::atom("notFound")));
    let mut sig = Sig::one(super::super::positional(1), vec![keys], values);
    sig.data = true;
    sig.dense = false;
    sig.note_held();
    Ty::func(Arc::new(sig))
}

/// The value of the integer literal `e`, `-` before it included.
fn int_literal(e: &Expr) -> Option<BigInt> {
    match &e.kind {
        ExprKind::Int { radix, digits } => match Value::int_text(digits, *radix).ok()?? {
            Value::Int(n) => Some(BigInt::from(n)),
            Value::Big(r) => r.to_integer().ok(),
            _ => None,
        },
        ExprKind::Unary(UnaryOp::Neg, x) => int_literal(x).map(|n| -n),
        _ => None,
    }
}

/// Whether `e` is a component read `b[j]`.
fn is_index(e: &Expr) -> bool {
    matches!(e.kind, ExprKind::Index(..))
}

/// `l` times `k`.
fn scale(l: Lin, k: &BigInt) -> Lin {
    match k.is_zero() {
        true => Lin::new(),
        false => l.into_iter().map(|(a, v)| (a, v * k)).collect(),
    }
}

/// The type of the atom `j` of a key of type `t`: the key, or its component `j`.
fn atom_type(t: &Ty, j: Option<usize>) -> Ty {
    let Some(j) = j else { return t.clone() };
    let parts = t.pieces().into_iter().filter_map(|p| match p {
        Piece::Tuple(row) => row.get(j).cloned(),
        _ => None,
    });
    Ty::union_all(&parts.collect::<Vec<_>>())
}

/// The number of components of every tuple a key of type `t` may be, when they all have one
/// number and `t` holds nothing else.
fn tuple_arity(t: &Ty) -> Option<usize> {
    let mut arity = None;
    for p in t.pieces() {
        let Piece::Tuple(row) = p else { return None };
        match arity {
            None => arity = Some(row.len()),
            Some(a) if a == row.len() => {}
            Some(_) => return None,
        }
    }
    arity
}

/// The largest minus the smallest integer of `t`, when its type lists them.
fn span_of(t: &Ty) -> Option<BigInt> {
    let vs = t.set.ints_listed()?;
    let ns = vs
        .iter()
        .map(|v| match v {
            Value::Int(n) => Some(BigInt::from(*n)),
            Value::Big(r) => r.to_integer().ok(),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    Some(ns.iter().max()? - ns.iter().min()?)
}

/// The atoms the rows determine: those whose unit vector is in the rows' span over the
/// rationals, read off the reduced row echelon form as the rows with one nonzero entry. Each
/// such atom is a rational combination of the key components, so the keypath recovers it.
// Complexity tradeoff: the elimination is sparse. Each atom keeps the set of rows holding it,
// so a pivot visits only the rows it must clear, and a pattern whose components each read their
// own binder (the common case: literal keys, a transpose) costs O(n log n) for n components.
// The dense form, which scanned every row for every atom, cost O(n²) on that case (measured:
// T(8n)/T(n) = 13.4 at n = 100 levels). Fill-in still costs what dense elimination costs.
fn recovered(mut rows: Vec<Lin>) -> BTreeSet<Atom> {
    let mut holders: BTreeMap<Atom, BTreeSet<usize>> = BTreeMap::new();
    for (r, row) in rows.iter().enumerate() {
        for a in row.keys() {
            holders.entry(*a).or_default().insert(r);
        }
    }
    let atoms = holders.keys().copied().collect::<Vec<_>>();
    let mut pivots = vec![false; rows.len()];
    for a in &atoms {
        let Some(p) = holders[a].iter().copied().find(|&r| !pivots[r]) else {
            continue;
        };
        pivots[p] = true;
        let pivot = rows[p].clone();
        let pv = pivot[a].clone();
        let clear = holders[a].iter().copied().filter(|&r| r != p);
        for r in clear.collect::<Vec<_>>() {
            let v = rows[r][a].clone();
            // row := pv·row − v·pivot, which clears `a` and keeps every entry an integer.
            let mut next = scale(std::mem::take(&mut rows[r]), &pv);
            for (b, w) in &pivot {
                let x = next.remove(b).unwrap_or_default() - &v * w;
                let held = holders.entry(*b).or_default();
                if x.is_zero() {
                    held.remove(&r);
                } else {
                    held.insert(r);
                    next.insert(*b, x);
                }
            }
            // Divide by the entries' gcd: without it the cross-multiplication doubles the
            // entries' bit length at each step on a row cleared by many pivots.
            let g = next.values().fold(BigInt::zero(), |g, x| g.gcd(x));
            if !g.is_zero() && !g.is_one() {
                next.values_mut().for_each(|x| *x /= &g);
            }
            rows[r] = next;
        }
    }
    // Not proved: that a row left with one nonzero entry is exactly an atom whose unit vector
    // lies in the rows' span. It holds if the loop leaves the rows in reduced row echelon form
    // (each pivot column cleared from every other row, the earlier pivot rows included, which
    // `holders` reaches since a pivot's entry in an earlier pivot column is already zero); the
    // argument is written here and tested on the catalog's cases and the benchmarks, not
    // checked by a proof tool.
    rows.iter()
        .filter(|r| r.len() == 1)
        .flat_map(|r| r.keys().copied())
        .collect()
}
