//! The standard operations on one level of a family that plan row FP-ops-run (author P229)
//! builds into zedc as `map` is (plan row MAP-pure-zed): `.count`, `.sum` and `.reduce(op)`,
//! the quantifiers `.any`, `.all` and `.find` (step L3.15a), and `.first` and `.last`
//! (DESIGN.md sec:corner_cases, "`first`/`last` are lexicographic").

use super::remap::Apply;
use crate::check::*;

/// How a program wrote a fold of one level, for the messages of [`Ck::fold_level`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::check) enum FoldForm {
    /// `x >< op`.
    Infix,
    /// `x.reduce(op)`, which DESIGN.md defines as `x >< op` (the method register's `reduce`
    /// row, `fold(m, op, ev)`).
    Reduce,
    /// `x.sum` on a family, `x >< (+)` (the method register's `sum` row).
    Sum,
}

impl FoldForm {
    /// The fold as code, quoted.
    pub(in crate::check) fn word(self) -> &'static str {
        match self {
            FoldForm::Infix => "`><`",
            FoldForm::Reduce => "`.reduce`",
            FoldForm::Sum => "`.sum`",
        }
    }

    /// The fold named in a sentence, before its operator.
    pub(in crate::check) fn fold_name(self) -> &'static str {
        match self {
            FoldForm::Infix => "a fold `><`",
            FoldForm::Reduce => "a fold `.reduce`",
            FoldForm::Sum => "a fold `.sum`",
        }
    }

    /// The fold by the operator written `written`, named in a sentence.
    pub(in crate::check) fn what(self, written: &str) -> String {
        match self {
            FoldForm::Infix => format!("a fold `><` by `{written}`"),
            FoldForm::Reduce => format!("a fold `.reduce({written})`"),
            FoldForm::Sum => "a fold `.sum`".to_string(),
        }
    }

    /// The fold by `written` of a small family, as a repair writes it.
    pub(in crate::check) fn example(self, written: &str) -> String {
        match self {
            FoldForm::Infix => format!("{{0 -> 1, 1 -> 2}} >< {written}"),
            FoldForm::Reduce => format!("{{0 -> 1, 1 -> 2}}.reduce({written})"),
            FoldForm::Sum => "{0 -> 1, 1 -> 2}.sum".to_string(),
        }
    }
}

/// A quantifier of step L3.15a.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::check) enum Quantifier {
    /// `x.any(p)`: whether `p` holds of some entry.
    Any,
    /// `x.all(p)`: whether `p` holds of every entry.
    All,
    /// `x.find(p)`: the first key, in key order, whose entry `p` holds of, or `#none`.
    Find,
}

impl Quantifier {
    /// The quantifier as a program writes it, quoted.
    pub(in crate::check) fn word(self) -> &'static str {
        match self {
            Quantifier::Any => "`any`",
            Quantifier::All => "`all`",
            Quantifier::Find => "`find`",
        }
    }

    /// The quantifier by its prelude word.
    pub(in crate::check) fn of(name: &str) -> Option<Quantifier> {
        match name {
            "any" => Some(Quantifier::Any),
            "all" => Some(Quantifier::All),
            "find" => Some(Quantifier::Find),
            _ => None,
        }
    }
}

// walk.rs imports this file (`FoldForm`, `Quantifier` and the methods below), so this file
// calls no method written in walk.rs: a cycle between files is refused (DESIGN.md sec:units;
// the import graph of step S.1f, which counts a call of a method written apart from its type
// as an import of the method's file). The fold of a level, `Ck::fold_level`, and its callers
// are in walk.rs; `takes_args`, which `map` in walk.rs calls too, is here; and `Ck::apply` is
// passed in, as to remap.rs (its `Apply`).
impl<'t, 'a> Ck<'t, 'a> {
    /// Whether `fsig`, the function given to the built-in `word`, can be called with `n`
    /// arguments by position: it needs no more than `n` and takes at least `n`. Any other is
    /// rejected at `at` with `shape`, a function of the right number of parameters, as the
    /// repair; the kernel calls a function with exactly the arguments given and does not
    /// curry, so a `map` by a function of two parameters would otherwise reach the evaluator.
    pub(super) fn takes_args(
        &mut self,
        word: &str,
        fsig: &Sig,
        n: usize,
        shape: &str,
        at: Span,
    ) -> bool {
        let needs = fsig.params.iter().filter(|p| p.default.is_none()).count();
        let has = fsig.params.len();
        if needs <= n && n <= has {
            return true;
        }
        let what = match n {
            1 => "one argument".to_string(),
            n => format!("{n} arguments"),
        };
        let why = match needs > n {
            true => format!("needs {needs}"),
            false => format!("takes {has}"),
        };
        self.error_offering(
            at,
            format!("{word} calls its function with {what}, and this function {why}"),
            [format!("repair: pass a function of {what}, as `{shape}`")],
        );
        false
    }

    /// The families `x` may be, for `word`, a built-in word on one level: each data function
    /// of `x`. A loose atom `x` may be passes through, and is not listed; `_` is reported as at
    /// `map`; any other value is rejected with `example`, the word on a family, as the repair,
    /// and so is a class, whose need this zedc does not record for these words. `None` after
    /// an error.
    pub(super) fn levels_of(
        &mut self,
        x: &Ty,
        word: &str,
        example: &str,
        span: Span,
    ) -> Option<Vec<Arc<Sig>>> {
        let mut sigs = Vec::new();
        for p in x.pieces() {
            match p {
                Piece::Fn(sig) if sig.data => sigs.push(sig),
                Piece::Dyn => self.any(word, span),
                Piece::Var(_) => {
                    let what = format!("{word} on a value whose type is a type parameter");
                    self.error(span, zedc_base::rejection::not_yet(&what));
                    return None;
                }
                p if p.is_atoms() => {}
                p => {
                    let t = self.text(&p.ty());
                    self.error_offering(
                        span,
                        format!("{word} reads the entries of a family, and this value is {t}"),
                        [format!("repair: call it on a family, as `{example}`")],
                    );
                    return None;
                }
            }
        }
        Some(sigs)
    }

    /// The entries of the families `sigs`: the union of their arrows' results, less the
    /// misses `#notFound` and `#outOfBounds`.
    // Not proved: an entry is never itself `#notFound` or `#outOfBounds`, as at `map_end`.
    fn entries_of(sigs: &[Arc<Sig>]) -> Ty {
        let misses = &KType::atom("notFound") | &KType::atom("outOfBounds");
        Ty::union_all(sigs.iter().flat_map(|s| s.arrows.iter().map(|a| &a.result))).without(&misses)
    }

    /// Whether the family `sig` has an entry in every value of its type: some arrow whose key
    /// type lists a key and whose result holds no miss, a key always present (as at
    /// [`Self::fold_level`]).
    fn never_empty(sig: &Sig) -> bool {
        let misses = &KType::atom("notFound") | &KType::atom("outOfBounds");
        (sig.arrows.iter()).any(|a| {
            a.params.first().is_some_and(|k| !k.lists_nothing())
                && (&a.result.atoms() & &misses) == KType::empty()
        })
    }

    /// `x.count`: the number of top-level entries, an `int`; a loose atom `x` passes through.
    pub(super) fn count_end(&mut self, x: &Ty, span: Span) -> Ty {
        let out = self.passing(x, "`count`", span, None);
        match self.levels_of(x, "`count`", "[1, 2].count", span) {
            Some(_) => out.union(&Ty::carrier(Carrier::Int)),
            None => Ty::empty(),
        }
    }

    /// `x.first`, or with `last` `x.last` (DESIGN.md sec:corner_cases): the leaf at the least
    /// (greatest) keypath, read level by level in key order. Its type is the union of the leaf
    /// types beneath every level, an entry that is a family being a level, and holds `#none`
    /// unless every level on the way has a key always present ([`Self::never_empty`]): `V` for
    /// `[3, 1, 4]`, `V | #none` for a `where` result. A loose atom `x` passes through.
    // Complexity tradeoff: each family type met is read once, O(arrows) each; the naive walk
    // that follows each level's entry type down again for every family above it would read a
    // type shared by several levels once per path to it. The walk takes a work list, each
    // signature pushed as often as an entry type above lists it, which a finite type bounds.
    pub(super) fn end_end(&mut self, x: &Ty, last: bool, span: Span) -> Ty {
        let word = if last { "`last`" } else { "`first`" };
        let example = if last {
            "[3, 1, 4].last"
        } else {
            "[3, 1, 4].first"
        };
        let out = self.passing(x, word, span, None);
        let Some(top) = self.levels_of(x, word, example, span) else {
            return Ty::empty();
        };
        let mut leaves = Ty::empty();
        let mut may_be_empty = false;
        let mut work = top;
        while let Some(sig) = work.pop() {
            may_be_empty |= !Self::never_empty(&sig);
            for p in Self::entries_of(std::slice::from_ref(&sig)).pieces() {
                match p {
                    Piece::Fn(inner) if inner.data => work.push(inner),
                    p => leaves = leaves.union(&p.ty()),
                }
            }
        }
        if may_be_empty {
            leaves = leaves.union(&Ty::set(KType::atom("none")));
        }
        out.union(&leaves)
    }

    /// `x.any(p)`, `x.all(p)` or `x.find(p)`, `p` checked (step L3.15a): `p` applied to each
    /// entry must give a `bool`; the result is a `bool`, or for `find` a key of `x` or
    /// `#none`. The entries are asked in key order and the first that decides ends the walk;
    /// an atom `p` gives at an entry before it is the result (L3.15a: "a failure of `p` at an
    /// entry before the deciding one is the result"), and so is an entry that is a loose atom,
    /// which passes through `p` as through any call. A loose atom `x` passes through. `apply`
    /// is `Ck::apply`, passed in by walk.rs.
    pub(super) fn quantifier_end(
        &mut self,
        x: &Ty,
        f: Arg<'a>,
        q: Quantifier,
        span: Span,
        apply: Apply<'t, 'a>,
    ) -> Ty {
        let word = q.word();
        let shape = "x -> x > 0";
        let name = &word[1..word.len() - 1];
        let out = self.passing(x, word, span, None);
        let Some(fsig) = only_fn(&f.ty) else {
            let t = self.text(&f.ty);
            self.error_offering(
                f.at.unwrap_or(span),
                format!("{word} takes a function, and this value is {t}"),
                [format!(
                    "repair: pass a function of one parameter, as `{shape}`"
                )],
            );
            return Ty::empty();
        };
        if !self.takes_args(word, &fsig, 1, shape, f.at.unwrap_or(span)) {
            return Ty::empty();
        }
        let example = format!("[1, 2].{name}({shape})");
        let Some(sigs) = self.levels_of(x, word, &example, span) else {
            return Ty::empty();
        };
        let all = Self::entries_of(&sigs);
        let entries = all.without_loose();
        let gives = match entries.lists_nothing() {
            true => Ty::empty(),
            false => {
                let what = Label::Text(match q {
                    Quantifier::Any => "the function given to `any`",
                    Quantifier::All => "the function given to `all`",
                    Quantifier::Find => "the function given to `find`",
                });
                apply(self, what, &fsig, vec![Some(Arg::of(entries))], false, span).0
            }
        };
        let verdict = gives.without_loose();
        if !verdict.lists_nothing() && !self.subtype(&verdict, &Ty::carrier(Carrier::Bool)) {
            let t = self.text(&verdict);
            self.error_offering(
                f.at.unwrap_or(span),
                format!("{word} asks its function of each entry, and this function gives {t}"),
                [
                    format!("repair: give a `bool` for each entry, as `{shape}`"),
                    "repair: handle the values that are not `bool` with `else`, as \
                     `x -> f(x) else false`"
                        .to_string(),
                ],
            );
            return Ty::empty();
        }
        let answer = match q {
            Quantifier::Any | Quantifier::All => Ty::carrier(Carrier::Bool),
            Quantifier::Find => {
                let misses = &KType::atom("notFound") | &KType::atom("outOfBounds");
                // The keys of the arrows that give an entry; an arrow that gives only a miss
                // lists keys the family does not hold.
                let keys = Ty::union_all(sigs.iter().flat_map(|s| {
                    (s.arrows.iter())
                        .filter(|a| !a.result.without(&misses).lists_nothing())
                        .map(|a| &a.params[0])
                }));
                keys.union(&Ty::set(KType::atom("none")))
            }
        };
        out.union(&answer)
            .union(&gives.loose_ty())
            .union(&all.loose_ty())
    }
}
