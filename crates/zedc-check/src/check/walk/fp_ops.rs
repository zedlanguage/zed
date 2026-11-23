//! The standard operations on one level of a family that plan row FP-ops-run (author P229)
//! builds into zedc as `map` is (plan row MAP-pure-zed): `.count`, `.sum` and `.reduce(op)`,
//! the quantifiers `.any`, `.all` and `.find` (step L3.15a), and `.first` and `.last`
//! (DESIGN.md sec:corner_cases, "`first`/`last` are lexicographic"); by plan row
//! FP-ops-scan, `.scan(op)` and `.chunkBy(f)` (step L5.3); the string functions `split`,
//! `lines` and `concat` of plan row FP-ops-strings (step L3.2); and, by plan row
//! FP-ops-concat-zip, `a ++ b` on lists and `a.zip(b)` (step L5.2).

use super::remap::{Apply, NeedFn};
use crate::check::*;

/// `Ck::fold_level`, the check of the fold of one level, passed in by walk.rs as `Apply` is.
pub(in crate::check) type FoldLevel<'t, 'a> =
    fn(&mut Ck<'t, 'a>, Reducer, &Ty, Span, Span, FoldForm) -> Ty;

/// Whether the family `sig` is an operand `++` takes: a list, keyed by the ranks `0`, `1`, …
/// ([`Dense::Ranks`]), or a family with no key, as `{}` (the ranks `0 ..< 0`) and an empty
/// range such as `3 ..< 3`, whose exact keys are none ([`Sig::keys`]). The fold repair of
/// `Ck::fold_dir_end` offers `a ++ [x]` exactly where this holds, so the repair checks
/// (types.rs `fold_refusal_repairs_fit_every_start_value_and_check`). O(arrows).
pub(in crate::check) fn joins_as_list(sig: &Sig) -> bool {
    sig.data
        && (sig.dense == Dense::Ranks
            || sig.arrows.iter().all(|a| a.params[0].is_empty())
            || (sig.keys.as_ref()).is_some_and(|k| written_ints(k).is_empty()))
}

/// The source text `c` of an operand before `.count` or `[i]`, in parentheses only where the
/// grammar needs them there, as the formatter writes it ([`zedc_syntax::format::code_as_receiver`];
/// author rule P191, plan row PRINT-repair-parens-minimal): `xs`, `xs.where(f)`, `"ab"` and
/// `#a` as written, `a + b` and `2` grouped. Before, the test on the characters outside brackets
/// grouped any token but a name or a `.`, so `"ab"` and `#a`, which need none. Text with a
/// comment or that does not read as one expression is grouped. O(length of `c`).
fn postfix_operand(c: &str) -> String {
    zedc_syntax::format::code_as_receiver(c).into_owned()
}

/// The operand `e`, written `c`, before a `.` or `::`: a string literal as written, whose
/// quotes [`postfix_operand`] would wrap in parentheses it does not need, any other operand
/// as [`postfix_operand`] writes it.
fn postfix_subject(e: Option<&Expr>, c: &str) -> String {
    match e.map(|e| &e.kind) {
        Some(ExprKind::Str(_)) => c.to_string(),
        _ => postfix_operand(c),
    }
}

/// The views that read the characters of the string `e`, written `c`, as repairs of a split by
/// the empty separator (DESIGN L3.2, author decision P314): its code points, its UTF-16 units
/// and its UTF-8 bytes, which of them are the characters a program means depending on the
/// string type.
pub(in crate::check) fn view_forms(e: Option<&Expr>, c: &str) -> [String; 3] {
    let s = postfix_subject(e, c);
    [
        format!("`{s}::codepoints`, the code points of `{s}`, each a `char32`"),
        format!("`{s}::chars`, its UTF-16 units, each a `char16`"),
        format!("`{s}::u8`, its UTF-8 bytes"),
    ]
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

// walk.rs imports this file (`Quantifier` and the methods below), so this file
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
    /// `map`; any other value is rejected with `example`, the word on a family, as the repair.
    /// A class never reaches here: walk.rs's `Ck::level_word` takes the variables of `x` out
    /// first, each as a need ([`NeedKind::Level`]) or as the type it is resolved to, and
    /// `strings_parts` passes its operand with the variables taken out. The `Piece::Var` arm
    /// stays for `zip_end`, which passes a variable for which `class_root` gives no class (plan
    /// row TEST-generic-operand-messages-reached: no test reaches it yet), and names the operand
    /// at `operand` by its code where it is on one line. `None` after an error.
    pub(super) fn levels_of(
        &mut self,
        x: &Ty,
        word: &str,
        example: &str,
        span: Span,
        operand: Option<Span>,
    ) -> Option<Vec<Arc<Sig>>> {
        let mut sigs = Vec::new();
        for p in x.pieces() {
            match p {
                Piece::Fn(sig) if sig.data => sigs.push(sig),
                Piece::Dyn => self.any(word, span),
                // The program may write no type parameter, so the operand's type is called
                // generic, as at `string_operand` (plan row MSG-generic-operand-wording).
                Piece::Var(_) => {
                    let what = match self.operand_text(operand) {
                        Some(c) => format!("{word} on `{c}`, whose type is generic here,"),
                        None => format!("{word} on a value whose type is generic here"),
                    };
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

    /// The entries of the families `sigs`: the union of the values they store
    /// ([`super::super::family_values`], which proves that a stored `#notFound` or
    /// `#outOfBounds` is kept and a miss is not). O(arrows).
    fn entries_of(sigs: &[Arc<Sig>]) -> Ty {
        let each: Vec<Ty> = sigs
            .iter()
            .map(|s| super::super::family_values(s))
            .collect();
        Ty::union_all(&each)
    }

    /// Whether the family `sig` has an entry in every value of its type: some exact arrow
    /// whose key type lists a key, a key always present. Only a partial arrow misses
    /// ([`super::super::family_values`]); an exact arrow whose result holds `#notFound`
    /// stores it, as `[#notFound]` does, and has its key.
    fn never_empty(sig: &Sig) -> bool {
        (sig.arrows.iter())
            .any(|a| !a.partial && a.params.first().is_some_and(|k| !k.lists_nothing()))
    }

    /// `x.count`: the number of top-level entries, an `int`; a loose atom `x` passes through.
    pub(super) fn count_end(&mut self, x: &Ty, span: Span) -> Ty {
        let out = self.passing(x, "`count`", span, None);
        match self.levels_of(x, "`count`", "[1, 2].count", span, None) {
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
        let Some(top) = self.levels_of(x, word, example, span, None) else {
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
        let Some(sigs) = self.levels_of(x, word, &example, span, None) else {
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
                // The keys of the arrows that store an entry; an arrow that gives only a miss
                // lists keys the family does not hold ([`super::super::family_values`]).
                let keys = Ty::union_all(sigs.iter().flat_map(|s| {
                    (s.arrows.iter())
                        .filter(|a| !a.value().lists_nothing())
                        .map(|a| &a.params[0])
                }));
                keys.union(&Ty::set(KType::atom("none")))
            }
        };
        out.union(&answer)
            .union(&gives.loose_ty())
            .union(&all.loose_ty())
    }

    /// `x.scan(op)`, `op` the operator section or the word `max` or `min` (step L5.3; the
    /// method register's `scan` row; DESIGN.md sec:type_language, the `m.scan(op)` row): each
    /// family `x` may be, with the same keys, each entry the fold by `op` of the entries up to
    /// it in key order. `op` is checked as the fold `x >< op` is (`fold`, `Ck::fold_level`,
    /// passed in by walk.rs): the operators whose associativity is built in, on the entries
    /// they take. A prefix holds its own entry, so it is never empty and no entry is `#empty`;
    /// each arrow keeps its keys and its misses, so the bounds ride through as at `map`. A
    /// loose atom `x` may be passes through. `site` is where the scan is written, which the
    /// fold's check records what it saw at; it is `span` but where a generic function's need
    /// is checked at a call at `span`.
    // Complexity tradeoff: the type is one fold check and one copy of each family's arrows,
    // O(arrows), as `map_end` makes; typing each prefix apart would cost a check per entry for
    // the same type, since every prefix folds entries of one type.
    pub(super) fn scan_end(
        &mut self,
        x: &Ty,
        op: Reducer,
        span: Span,
        site: Span,
        fold: FoldLevel<'t, 'a>,
    ) -> Ty {
        // Typed so that the import graph of step S.1f reads `form.word()` as `FoldForm::word`,
        // not as `Ck::word` of walk.rs, which would close a cycle walk.rs -> fp_ops.rs.
        let form: FoldForm = FoldForm::Scan;
        let out = self.passing(x, form.word(), span, None);
        let example = format!("[1, 2, 3].scan({})", op.written());
        let Some(sigs) = self.levels_of(x, form.word(), &example, span, None) else {
            return Ty::empty();
        };
        let folded = fold(self, op, &x.without_loose(), span, site, form);
        // `fold_level` gives the type of no value only after its error: a fold it accepts gives
        // the carrier, or `#empty` for a family with no entries.
        if folded.lists_nothing() {
            return Ty::empty();
        }
        // The `#empty` `fold_level` adds for a level that may be empty; no entry is an atom,
        // since `fold_level` takes only entries of the operator's carrier.
        let entry = folded.without(&KType::atom("empty"));
        let mut families = Ty::empty();
        for sig in sigs {
            let mut s = (*sig).clone();
            // Each arrow keeps its keys and whether it is partial, a partial one missing with
            // `#notFound` as before; its value is now the prefix's fold.
            for a in &mut s.arrows {
                let params = std::mem::take(&mut a.params);
                *a = a.remade(params, |_| entry.clone());
            }
            s.word = None;
            s.needs = Default::default();
            s.note_held();
            families = families.union(&Ty::func(Arc::new(s)));
        }
        out.union(&families)
    }

    /// `x.chunkBy(f)`, `f` checked (step L5.3; DESIGN.md sec:type_language, the `m.chunkBy(f)`
    /// row): the maximal runs of entries, in key order, on which `f` gives one value, each run
    /// under its index from 0, each entry kept under its own key: `[1, 1, 2].chunkBy(x -> x)`
    /// is `{0 -> {0 -> 1, 1 -> 1}, 1 -> {2 -> 2}}`. The result is `int ->? F`, `F` each family
    /// `x` may be with every key now optional, as after `where`. Gives the result and what `f`
    /// gives, which walk.rs checks is data, since the run's end is found by comparing it with
    /// `==`; `None` after an error. A loose atom `x` may be passes through. `apply` is
    /// `Ck::apply`, passed in by walk.rs.
    // Complexity tradeoff: one application of `f` to the union of the entries and one copy of
    // each family's arrows, O(arrows); the tighter guarantee of the bound table (each run holds
    // at least one entry, the runs are `0 ..< runs`) is not tracked by these types, which the
    // table allows ("else empty"), so the outer arrow is partial.
    pub(super) fn chunk_by_end(
        &mut self,
        x: &Ty,
        f: Arg<'a>,
        span: Span,
        apply: Apply<'t, 'a>,
    ) -> Option<(Ty, Ty)> {
        let word = "`chunkBy`";
        let shape = "x -> x.id";
        let at = f.at.unwrap_or(span);
        let out = self.passing(x, word, span, None);
        let Some(fsig) = only_fn(&f.ty) else {
            let t = self.text(&f.ty);
            self.error_offering(
                at,
                format!("{word} takes a function, and this value is {t}"),
                [format!(
                    "repair: pass a function of one parameter, as `{shape}`"
                )],
            );
            return None;
        };
        if !self.takes_args(word, &fsig, 1, shape, at) {
            return None;
        }
        let sigs = self.levels_of(x, word, "[1, 1, 2].chunkBy(x -> x)", span, None)?;
        let entries = Self::entries_of(&sigs);
        let gives = match entries.lists_nothing() {
            true => Ty::empty(),
            false => {
                let what = Label::Text("the function given to `chunkBy`");
                apply(self, what, &fsig, vec![Some(Arg::of(entries))], false, span).0
            }
        };
        let mut runs = Ty::empty();
        for sig in sigs {
            let mut s = (*sig).clone();
            // A run holds some of the keys, so each arrow is partial, with the values it
            // stored (FP-chunkby-runs-partial). Before, its result gained `#notFound` and it
            // stayed exact, which says every key is in each run and `#notFound` is stored.
            for a in &mut s.arrows {
                let params = std::mem::take(&mut a.params);
                *a = Arrow::partial_of(params, a.value().into_owned());
            }
            // A run holds some of the keys, which `Sig::keys` would not describe.
            s.dense = Dense::No;
            s.keys = None;
            s.word = None;
            s.needs = Default::default();
            s.note_held();
            runs = runs.union(&Ty::func(Arc::new(s)));
        }
        // The runs are ranked from 0, every rank present, so the keys are the ranks `0 ..< n`,
        // as a range's from `0` are (`Ck::range_end`).
        let int = Ty::carrier(Carrier::Int);
        let mut outer = Sig::one_partial(super::super::positional(1), vec![int], runs);
        outer.data = true;
        outer.dense = Dense::Ranks;
        outer.note_held();
        Some((out.union(&Ty::func(Arc::new(outer))), gives))
    }

    /// `split(s, sep)`, `lines(s)` or `concat(pieces, sep: s)` (plan row FP-ops-strings, step
    /// L3.2), each operand checked: `args` holds them in that order, `sep` of `concat` last
    /// when it is given. Each string operand must be a string, and the pieces of `concat` a
    /// family of strings; a family of families is rejected with `xss >< (++)` as the repair
    /// (author A105). `split` and `lines` give the rank `0 ..< n` of strings, `concat` a
    /// string. A loose atom of an operand passes through, as through any call. `split` gains
    /// `#emptySeparator` where its separator may be `""`, and one whose separator is always
    /// `""` is rejected (DESIGN L3.2, author decision P314).
    ///
    /// An operand whose type is a class not yet resolved, as a line of `m.stdin` in a function
    /// passed to `map` is, is checked at each call of the generic function, on the type the
    /// call gives it (plan row FP-ops-generic-strings, as `Ck::level_word` checks the one-level
    /// words): the parts that hold no such class are checked here, and the call records one
    /// need ([`NeedKind::Strings`]) of all its operands, which `meet` checks again with the
    /// class replaced by its type. The need is recorded only where the parts checked here gave
    /// no error, so a call never reports again what the definition reported. `need` is
    /// `Ck::need`, passed in by walk.rs as `apply` is to [`Self::quantifier_end`]: a call of it
    /// written here would close an import cycle (step S.1f, plan row
    /// S1F-check-limits-fp-ops-cycle).
    // Complexity tradeoff: the naive method, a need per class an operand holds, as
    // `level_word` makes one per variable, would check `split`'s separator piece by piece, and
    // `if b { "" } else { "," }` would then be rejected for its `""` alone where the whole
    // separator only may be empty (P314). One need of every operand checks the separator's
    // whole type at the call, at the same cost: O(size of the operands) here, and O(size of
    // the operands as the call binds them) at each call that `meet` checks it at. Proof that
    // the checks end: `meet` replaces the class the need is on, so each check of the need
    // reads one class fewer of the definition's, or classes of the caller, which a call of
    // the caller replaces in turn; the classes of a program are finite, and `need` records
    // each pair of a class and a use once (the visited set of P207), as at `level_word`.
    pub(super) fn strings_end(
        &mut self,
        word: &str,
        args: Vec<Arg<'a>>,
        span: Span,
        need: NeedFn<'t, 'a>,
    ) -> Ty {
        let sources = std::mem::take(&mut self.strings_from);
        let Some((args, generic)) = self.strings_classes(word, args, span) else {
            return Ty::empty();
        };
        let from = self.errors.len();
        let Some(out) = self.strings_parts(word, &args, &sources, span) else {
            return Ty::empty();
        };
        match generic {
            Some(r) if self.errors.len() == from => {
                let kind = NeedKind::Strings {
                    word: word.into(),
                    tys: args.iter().map(|a| a.ty.clone()).collect(),
                };
                out.union(&need(self, r, kind, true, span))
            }
            _ if word == "concat" => out.union(&Ty::carrier(Carrier::Str)),
            _ => out.union(&strings_rank()),
        }
    }

    /// For the need of `word` with the operand types `tys` that `meet` checks at the call at
    /// `span` ([`Ck::strings_from`]): the argument of that call that gives each operand its
    /// whole value, with its parameter's name and an example string (or family of strings) a
    /// repair writes in its place. For the pieces of `concat` that are no one argument's
    /// whole value, it is the argument that gives each entry its whole value, as `x` of
    /// `concat([x, x], sep: ",")`, and the example an entry. An operand that is not one
    /// parameter's whole value, as `d ++ ""` or `t[0]`, has none, and its repair stays in
    /// words: an argument changes such an operand only through the operation the body
    /// applies to it, so no argument written in its place is known to give the operand the
    /// example's value. The check of a value that flowed into a class has a frame of no call
    /// ([`CallFrame::call`]), and so no argument either. O(size of the operands).
    pub(super) fn strings_sources(
        &self,
        word: &str,
        tys: &[Ty],
        span: Span,
    ) -> Vec<Option<ArgRewrite<'a>>> {
        let Some(frame) = self.call_frames.last().filter(|f| f.call == Some(span)) else {
            return Vec::new();
        };
        let rewrite = |from: ArgFrom<'a>, example: &'static str| {
            from.map(|(arg, name)| ArgRewrite {
                arg,
                name,
                example,
                entry: false,
            })
        };
        (tys.iter().enumerate())
            .map(|(i, t)| match (word, i) {
                ("split", 0) => rewrite(frame.whole_arg(t), "\"a,b\""),
                ("split", _) => rewrite(frame.whole_arg(t), "\",\""),
                ("lines", _) => rewrite(frame.whole_arg(t), "\"a\\nb\""),
                (_, 0) => rewrite(frame.whole_arg(t), "[\"a\", \"b\"]").or_else(|| {
                    let sigs: Vec<Arc<Sig>> = (t.pieces().into_iter())
                        .filter_map(|p| match p {
                            Piece::Fn(sig) if sig.data => Some(sig),
                            _ => None,
                        })
                        .collect();
                    match sigs.is_empty() {
                        true => None,
                        false => rewrite(frame.whole_arg(&Self::entries_of(&sigs)), "\"a\"")
                            .map(|r| ArgRewrite { entry: true, ..r }),
                    }
                }),
                _ => rewrite(frame.whole_arg(t), "\", \""),
            })
            .collect()
    }

    /// The call the arguments of `with` were passed to, written with each replaced by its
    /// example, as code for a repair, where the call is on one line: `p("ab", ",")` for
    /// `p("ab", "")`. Every argument of `with` is of the one call `strings_sources` read them
    /// from, whose arguments lie apart in its text, so the edits, put in the order of the
    /// text, lie apart, as `edited` needs; two operands may be one argument, as both are `s` in
    /// `s.split(s)`, and that argument is written once, with the first one's example.
    fn call_with(&self, with: &[&ArgRewrite<'a>]) -> Option<String> {
        let call = with.first()?.arg.call;
        let mut edits: Vec<(Span, String)> = (with.iter())
            .map(|r| (r.arg.at, r.example.to_string()))
            .collect();
        edits.sort_by_key(|(s, _)| s.start);
        edits.dedup_by_key(|(s, _)| *s);
        let text = edited(self.t.text?, call, &edits.iter().collect::<Vec<_>>())?;
        let text = text.trim();
        (!text.contains('\n')).then(|| format!("`{text}`"))
    }

    /// An error at `at`, with the derivation of the expression there and then the repair
    /// `repair`, placed at the call `call` it rewrites ([`Self::call_with`]), else at `at`.
    fn error_repairing(&mut self, at: Span, message: String, repair: String, call: Option<Span>) {
        let mut notes = self.derive(&[at]);
        notes.push(Note {
            span: call.unwrap_or(at),
            text: repair.into(),
        });
        self.error_with(at, message, notes);
    }

    /// The operands of `word` with each class that is resolved to a type replaced by that
    /// type, and the root of the first class not yet resolved that the word reads: a string
    /// operand that is the class, the pieces of `concat` that are, or an entry of the pieces
    /// that is. A variable the word reads that names no class, a type variable of a signature,
    /// is not supported by this zedc. `None` after an error.
    // Complexity tradeoff: one walk of the operands' variables and one replacement, O(size of
    // the operands); a type a class is resolved to holds no variable (the invariant at
    // `Class::resolved`), so one replacement leaves only classes not yet resolved. The naive
    // method, a lookup of the class at each piece a check reads, costs the same and would be
    // made in every check below.
    #[allow(clippy::type_complexity)]
    fn strings_classes(
        &mut self,
        word: &str,
        mut args: Vec<Arg<'a>>,
        span: Span,
    ) -> Option<(Vec<Arg<'a>>, Option<usize>)> {
        if !args.iter().any(|a| a.ty.holds_vars()) {
            return Some((args, None));
        }
        let mut vars = Vars::default();
        for a in &args {
            a.ty.vars_in(&mut vars);
        }
        let mut resolved = Binds::new();
        let mut any = false;
        for v in &vars.order {
            if let Some(r) = self.class_root(v)
                && let Some(t) = self.classes[r].resolved.clone()
            {
                resolved.insert(v.clone(), t);
                any = true;
            }
        }
        if any {
            for a in &mut args {
                a.ty = a.ty.replace(&resolved);
            }
        }
        let mut generic = None;
        for (i, a) in args.iter().enumerate() {
            let pieces = word == "concat" && i == 0;
            let mut read: Vec<Arc<str>> = a.ty.vars.iter().cloned().collect();
            if pieces {
                let sigs: Vec<Arc<Sig>> = (a.ty.pieces().into_iter())
                    .filter_map(|p| match p {
                        Piece::Fn(sig) if sig.data => Some(sig),
                        _ => None,
                    })
                    .collect();
                read.extend(Self::entries_of(&sigs).vars.iter().cloned());
            }
            for v in &read {
                if let Some(r) = self.class_root(v) {
                    generic.get_or_insert(r);
                    continue;
                }
                let at = a.at.unwrap_or(span);
                let what = match (pieces, self.operand_text(a.at)) {
                    (true, Some(c)) => {
                        format!("`concat` of `{c}`, whose entries are of a generic type,")
                    }
                    (true, None) => {
                        "`concat` of a family whose entries are of a generic type".into()
                    }
                    (false, Some(c)) => format!("`{word}` on `{c}`, whose type is generic here,"),
                    (false, None) => format!("`{word}` on a value whose type is generic here"),
                };
                self.error(at, zedc_base::rejection::not_yet(&what));
                return None;
            }
        }
        Some((args, generic))
    }

    /// The checks of `strings_end` on the parts of the operands `args` that hold no class:
    /// gives the loose atoms that pass through and `#emptySeparator` where the separator may
    /// be `""`, and leaves out what the word itself gives. A class is checked at each call,
    /// by the need `strings_end` records. `None` after a rejection.
    fn strings_parts(
        &mut self,
        word: &str,
        args: &[Arg<'a>],
        sources: &[Option<ArgRewrite<'a>>],
        span: Span,
    ) -> Option<Ty> {
        let quoted = format!("`{word}`");
        let mut out = Ty::empty();
        let (pieces, strings) = match word {
            "concat" => (args.first(), &args[1..]),
            _ => (None, args),
        };
        for (i, a) in strings.iter().enumerate() {
            out = out.union(&self.passing(&a.ty, &quoted, span, a.at));
            let i = i + usize::from(pieces.is_some());
            if !self.string_operand(word, args, sources, i, span) {
                return None;
            }
        }
        if let ("split", [s, sep]) = (word, args) {
            // An empty separator has no answer, so it is the failure `#emptySeparator`, given
            // exactly where the separator's type holds `""`: a type that holds no `""`, as
            // `","` or a name bound to it, adds no atom, and one whose only value is `""` is
            // rejected. Each test reads the separator's type once, O(its size). A separator
            // that holds a class is tested at each call, on its whole type there.
            let value = sep.ty.without_loose();
            let empty = Value::str("");
            if value.vars.is_empty() {
                if !value.lists_nothing() && self.subtype(&value, &Ty::lit(&empty)) {
                    self.empty_separator(s, sep, sources, span);
                    return None;
                }
                if value.contains(&empty) {
                    out = out.union(&Ty::set(KType::atom("emptySeparator")));
                }
            }
        }
        let Some(p) = pieces else {
            return Some(out);
        };
        out = out.union(&self.passing(&p.ty, &quoted, span, p.at));
        let example = "concat([\"a\", \"b\"], sep: \", \")";
        // The pieces less their classes, which the need checks.
        let mut known = p.ty.clone();
        known.vars = VarSet::new();
        let sigs = self.levels_of(&known, &quoted, example, span, p.at)?;
        let at = p.at.unwrap_or(span);
        // The pieces as the program wrote them, where on one line, else by the parameter's
        // name in DESIGN step L3.2, `concat(pieces, sep: s)`, as at `strings_call`. Pieces with
        // no place in the program, as at a call of a generic function whose `concat` `meet`
        // checks on the types the call gives (plan row FP-ops-generic-strings), are named by
        // no name, since none of the callee's is in scope at the call: `None`.
        let code = p.at.map(|_| match self.operand_text(p.at) {
            Some(c) => postfix_subject(p.expr, &c),
            None => "pieces".to_string(),
        });
        let entries = Self::entries_of(&sigs);
        if !entries.loose_ty().lists_nothing() {
            let what = "`concat` of a family whose entries may be failure atoms";
            self.error(at, zedc_base::rejection::not_yet(what));
            return None;
        }
        // At a call of a generic function, whose `concat` `meet` checks on the types the call
        // gives, the argument that gives the pieces, or each entry, its whole value
        // ([`Self::strings_sources`]): the rejection marks it and names its parameter, and the
        // repair is the call with it replaced, where the call is on one line.
        let source = (sources.first().and_then(Option::as_ref)).filter(|_| p.at.is_none());
        let at = source.map_or(at, |r| r.arg.at);
        let rewritten = source.and_then(|r| self.call_with(&[r]));
        let call = source.map(|r| r.arg.call);
        for e in entries.pieces() {
            match e {
                Piece::Fn(ref sig) if sig.data => {
                    let message = match source {
                        Some(r) if r.entry => format!(
                            "`concat` joins a family of strings, and this value, passed as \
                             `{}`, is an entry of the family it joins and is {}, a family",
                            r.name,
                            self.text(&e.ty())
                        ),
                        Some(r) => format!(
                            "`concat` joins a family of strings, and this value, passed as \
                             `{}`, is {}, a family of families",
                            r.name,
                            self.text(&p.ty)
                        ),
                        None => format!(
                            "`concat` joins a family of strings, and this value is {}, a family \
                             of families",
                            self.text(&p.ty)
                        ),
                    };
                    let repair = match (&rewritten, &code) {
                        (Some(c), _) => format!("repair: write {c}"),
                        (None, Some(c)) => {
                            format!("repair: join the inner families first, as `{c} >< (++)`")
                        }
                        (None, None) => "repair: pass a family of strings to this call, joining \
                                         the inner families first with `>< (++)`"
                            .to_string(),
                    };
                    self.error_repairing(at, message, repair, call);
                    return None;
                }
                Piece::Dyn => self.any(&quoted, span),
                // An entry whose type is a class is checked at each call, by the need
                // `strings_end` records ([`Self::strings_classes`] found the class).
                Piece::Var(_) => {}
                e if self.subtype(&e.ty(), &Ty::carrier(Carrier::Str)) => {}
                e => {
                    let t = self.text(&e.ty());
                    let message = match source {
                        Some(r) if r.entry => format!(
                            "`concat` joins strings, and this value, passed as `{}`, is an entry \
                             of the family it joins and is {t}",
                            r.name
                        ),
                        Some(r) => format!(
                            "`concat` joins strings, and this family, passed as `{}`, has an \
                             entry that is {t}",
                            r.name
                        ),
                        None => {
                            format!("`concat` joins strings, and an entry of this family is {t}")
                        }
                    };
                    let repair = match (&rewritten, &code) {
                        (Some(c), _) => format!("repair: write {c}"),
                        (None, Some(c)) => format!(
                            "repair: make each entry a string, as `concat({c}.map(x -> String(x)))`"
                        ),
                        // An operand that is no argument's whole value, as `xs ++ ys`
                        // (`strings_sources`), or a call not on one line, has no rewrite.
                        (None, None) => "repair: pass a family of strings to this call".to_string(),
                    };
                    self.error_repairing(at, message, repair, call);
                    return None;
                }
            }
        }
        Some(out)
    }

    /// Whether `args[i]`, a string operand of the built-in `word` (`split`, `lines`, or the
    /// `sep` of `concat`) called at `span` with the operands `args`, may be only strings or
    /// loose atoms, beside the classes it holds; any other value is rejected. At a call of a
    /// generic function, `sources` holds the argument that gives each operand its whole value
    /// ([`Self::strings_sources`]): the rejection marks it and names its parameter, and the
    /// repair is the call with it replaced by a string.
    fn string_operand(
        &mut self,
        word: &str,
        args: &[Arg<'a>],
        sources: &[Option<ArgRewrite<'a>>],
        i: usize,
        span: Span,
    ) -> bool {
        let a = &args[i];
        let source = (sources.get(i).and_then(Option::as_ref)).filter(|_| a.at.is_none());
        let at = source.map_or(a.at.unwrap_or(span), |r| r.arg.at);
        for p in a.ty.without_loose().pieces() {
            match p {
                Piece::Dyn => self.any(&format!("`{word}`"), span),
                // A class, as the type of `l` of `m.stdin.map(l -> …)`, is checked at each call,
                // by the need `strings_end` records ([`Self::strings_classes`] found it).
                Piece::Var(_) => {}
                p if self.subtype(&p.ty(), &Ty::carrier(Carrier::Str)) => {}
                p => {
                    let t = self.text(&p.ty());
                    // The separator of `split` written `""` is replaced too, as at
                    // `string_example`: the repair would be rejected for it.
                    let empty_sep = (word == "split" && i == 0)
                        .then(|| sources.get(1).and_then(Option::as_ref))
                        .flatten()
                        .filter(|r| self.operand_text(Some(r.arg.at)).as_deref() == Some("\"\""));
                    let call = source.and_then(|r| {
                        let with: Vec<&ArgRewrite<'a>> = [r].into_iter().chain(empty_sep).collect();
                        self.call_with(&with)
                    });
                    let message = match source {
                        Some(r) => format!(
                            "`{word}` reads strings, and this value, passed as `{}`, is {t}",
                            r.name
                        ),
                        None => format!("`{word}` reads strings, and this value is {t}"),
                    };
                    let repair = match call {
                        Some(call) => format!("repair: write {call}"),
                        None => {
                            let example = self.string_example(word, args, i, span);
                            format!("repair: pass a string, as {example}")
                        }
                    };
                    let call = source.map(|r| r.arg.call);
                    self.error_repairing(at, message, repair, call);
                    return false;
                }
            }
        }
        true
    }

    /// The call of `word` at `span` with `args[i]` replaced by an example string, for the
    /// repair of an operand that is not one: the other operands as the program wrote them,
    /// where on one line, else by their parameters' names in DESIGN step L3.2 (`s`, `pieces`),
    /// and the call in the program's style, `w(…)` or `x.w(…)`, as at `strings_call` (plan row
    /// MSG-example-repairs). `lines` has no other operand.
    fn string_example(&self, word: &str, args: &[Arg<'a>], i: usize, span: Span) -> String {
        let method =
            !(self.operand_text(Some(span))).is_some_and(|c| c.starts_with(&format!("{word}(")));
        let written = |j: usize, or: &str| match args.get(j).and_then(|a| self.operand_text(a.at)) {
            Some(c) if j == 0 && method => postfix_subject(args[j].expr, &c),
            Some(c) => c,
            None => or.to_string(),
        };
        let (first, rest) = match (word, i) {
            // An empty separator as written is not copied, since the repair would be rejected.
            ("split", 0) => match written(1, "\",\"") {
                sep if sep == "\"\"" => ("\"a,b\"".to_string(), "\",\"".to_string()),
                sep => ("\"a,b\"".to_string(), sep),
            },
            ("split", _) => (written(0, "s"), "\",\"".to_string()),
            ("lines", _) => ("\"a\\nb\"".to_string(), String::new()),
            _ => (written(0, "pieces"), "sep: \", \"".to_string()),
        };
        match (method, rest.is_empty()) {
            (true, true) => format!("`{first}.{word}`"),
            (true, false) => format!("`{first}.{word}({rest})`"),
            (false, true) => format!("`{word}({first})`"),
            (false, false) => format!("`{word}({first}, {rest})`"),
        }
    }

    /// Rejects the `split` at `span` of the string `s` by `sep`, a separator that is always the
    /// empty string: every value that reaches it fails with `#emptySeparator`, and an operation
    /// that always fails is an error (DESIGN sec:failure; L3.2, author decision P314). The
    /// repairs name the views that read the characters of `s`, then a separator that is not
    /// empty, then the failure or `#bug` written in place of the call, as the other rejections
    /// of an operation that always fails offer them.
    fn empty_separator(
        &mut self,
        s: &Arg<'a>,
        sep: &Arg<'a>,
        sources: &[Option<ArgRewrite<'a>>],
        span: Span,
    ) {
        // At a call of a generic function, whose `split` `meet` checks on the types the call
        // gives (plan row FP-ops-generic-strings), the argument that gives the separator its
        // whole value ([`Self::strings_sources`]): the note marks it and names its parameter,
        // and the repair is the call with it replaced by a separator that is not empty.
        let source = (sources.get(1).and_then(Option::as_ref)).filter(|_| sep.at.is_none());
        let at = source.map_or(sep.at.unwrap_or(span), |r| r.arg.at);
        // At a call of a generic function `split` is not written at the call: `this call`.
        let call = match (self.operand_text(Some(span)), source) {
            (Some(c), _) => format!("`{c}`"),
            (None, Some(_)) => "this call".to_string(),
            (None, None) => "`split` here".to_string(),
        };
        let reason = match (sep.expr.map(|e| &e.kind), self.operand_text(sep.at)) {
            (Some(ExprKind::Str(_)), _) | (_, None) => "its separator is the empty string".into(),
            (_, Some(c)) => format!("its separator `{c}` is always the empty string"),
        };
        let rewritten = source.and_then(|r| self.call_with(&[r]));
        // The repairs that rewrite the `split` name its string by its code. A string with no
        // code here, as at a call of a generic function, is named by no name, which would not
        // be in scope at the call: the repair there is the call with its separator argument
        // replaced, and where no one argument gives the separator (`s.split(d ++ "")`, see
        // `strings_sources`) or the call is not on one line, a separator that is not empty.
        let rewrites: Vec<String> = match (rewritten, self.operand_text(s.at)) {
            (Some(c), _) => vec![format!("repair: write {c}")],
            (None, Some(subject)) => {
                // The call in the program's style: `split(s, sep)` as a function,
                // `s.split(sep)` as a method.
                let split = match call.starts_with("`split(") {
                    true => format!("`split({subject}, sep)`"),
                    false => format!("`{}.split(sep)`", postfix_subject(s.expr, &subject)),
                };
                (view_forms(s.expr, &subject).into_iter())
                    .map(|form| format!("repair: write {form}"))
                    .chain([format!(
                        "repair: write {split}, with a separator `sep` that is not empty"
                    )])
                    .collect()
            }
            (None, None) => {
                vec!["repair: pass a separator that is not empty to this call".to_string()]
            }
        };
        let text = match source {
            Some(r) => format!(
                "this argument, passed as `{}`, is the separator, which is always the empty \
                 string",
                r.name
            ),
            None => "this separator is always the empty string".to_string(),
        };
        let mut notes = vec![Note {
            span: at,
            text: text.into(),
        }];
        notes.extend(self.derive(&[at]));
        let menu = rewrites.into_iter().chain([
            "repair: write `#emptySeparator` in place of this call, where the failure is \
                 meant"
                .to_string(),
            "repair: write `#bug(\"…\")` in place of this call, where it is never meant to \
                 be reached"
                .to_string(),
        ]);
        notes.extend(menu.map(|text| Note {
            span,
            text: text.into(),
        }));
        self.rejects_with(
            Row::AlwaysFails,
            span,
            format!(
                "{call} always fails with `#emptySeparator`: {reason}, which is found at every \
                 position of the text, so there are no pieces to give"
            ),
            notes,
        );
    }

    /// The family at `at` as a repair writes it before `.` or `><`: the program's code, in
    /// parentheses where it needs them ([`postfix_operand`]), where it is on one line; else
    /// `xs`, the name DESIGN's method register gives a family (plan row MSG-example-repairs).
    pub(in crate::check) fn subject_text(&self, at: Option<Span>) -> String {
        (self.operand_text(at)).map_or_else(|| "xs".to_string(), |c| postfix_operand(&c))
    }

    /// [`Ck::subject_text`] of the family folded by the fold at `site` (`x.reduce(f)`,
    /// `x.scan(f)`, `x.sum`, `sum(x)` or `x >< f`).
    pub(in crate::check) fn fold_subject(&self, site: Span) -> String {
        self.subject_text(self.receivers.get(&site).copied())
    }

    /// The function at `at` as a repair writes it, where it is on one line; else `or`.
    pub(in crate::check) fn function_text(&self, at: Option<Span>, or: &str) -> String {
        self.operand_text(at).unwrap_or_else(|| or.to_string())
    }

    /// The bounds of the keys of the families `sigs` (DESIGN.md sec:type_language, the bound
    /// table): `L`, the keys each of them surely holds, and `U`, the keys any of them may
    /// hold. A key is sure where its arrow is not partial, as for a list display; a range, a
    /// `Lines` input or a `where` result guarantees no key. An exact arrow whose result holds
    /// `#notFound` stores it ([`super::super::family_values`]), as `[n, #notFound]` does, so
    /// its keys are sure. `sigs` is not empty.
    // Complexity tradeoff: one union per arrow and one meet per family, linear in the arrows;
    // the pairwise test of each family of one operand against each of the other's, which
    // `zip_end` would need without these two bounds, is quadratic in the families.
    fn key_bounds(sigs: &[Arc<Sig>]) -> (Ty, Ty) {
        let sure = |s: &Sig| {
            Ty::union_all(
                (s.arrows.iter())
                    .filter(|a| !a.partial)
                    .map(|a| &a.params[0]),
            )
        };
        let may = |s: &Sig| Ty::union_all(s.arrows.iter().map(|a| &a.params[0]));
        let mut l = sure(&sigs[0]);
        for s in &sigs[1..] {
            l = Ty::meet(&l, &sure(s));
        }
        let each: Vec<Ty> = sigs.iter().map(|s| may(s)).collect();
        let u = Ty::union_all(each.iter());
        (l, u)
    }

    /// The number of entries every family of `sigs` holds, where their key bounds are one
    /// finite set of integers, as for list displays: `[1, 2] ++ [3]` is then `(0 | 1 | 2) ->
    /// int` with each key sure. `None` where the count is not known.
    fn known_count(sigs: &[Arc<Sig>]) -> Option<usize> {
        let (l, u) = Self::key_bounds(sigs);
        let ints = Ty::carrier(Carrier::Int);
        (u.subtype(&ints) && u.subtype(&l))
            .then(|| u.set.ints_listed().map(|v| v.len()))
            .flatten()
    }

    /// The bounds `L` and `U` of [`Self::key_bounds`] as sets of ints, where every family of
    /// `sigs` has int keys: a family with exact keys ([`Sig::keys`]), as a range with literal
    /// ends, holds just those, each sure; any other gives its key types' listed ints, sure
    /// where the arrow is exact. A key type of infinitely many ints, as
    /// `int`, gives every int to `U` and none to `L`. `None` where a family may have a key
    /// that is not an int. `sigs` is not empty.
    ///
    /// Proof that `L` holds only keys every family holds and `U` every key any may hold:
    /// `Sig::keys` is the family's exact key set by its contract; a key type's ints are a
    /// literal set (`KType::ints_listed`), turned into pieces one for one, or infinite, whose
    /// ints lie in `top` and include those of the empty set. The infinite case loses no
    /// verdict where these sets are read, beside a family with exact keys (`zip_end`,
    /// `list_concat_end`): `zip` needs `U_a ⊆ L_b` and `U_b ⊆ L_a`; the `L` of the side with
    /// exact keys is finite, so the other side's `U` must be, so its `L`, so this side's `U`;
    /// so where a key type is infinite the exact test fails too. `list_concat_end` reads a
    /// count only where `L = U` exactly, which a set made larger or smaller here cannot fake.
    ///
    /// That argument in full, for any mix of families on each side (PROOF-range-end-known-
    /// values). Write `L*`, `U*` for the true sets and `L`, `U` for these. A kernel set of ints
    /// is a finite list or cofinite (`ints_listed` is `None` exactly then), so a key type is
    /// approximated only where it is infinite, and then `L ⊆ L*` (an infinite sure set read as
    /// empty) and `U ⊇ U*` (an infinite may set read as `top`); elsewhere they are equal. So
    /// each test `U_x ⊆ L_y` read here implies the true one: an accepted `zip` is accepted
    /// truly. Conversely, where any family of either side has an infinite key type, the true
    /// verdict fails too: a family's sure keys lie in its may keys (the sure arrows are some
    /// of its arrows), so that family makes its side's `U*` infinite, and the true tests then
    /// need the other side's `L*` infinite, so every family there has infinite sure keys and
    /// no exact keys, so that side's `U*` is infinite too, and the first side's `L*` must be
    /// infinite, so no family of either side has exact keys; but these sets are read only
    /// where one family has them (`keyed` in `zip_end`), a finite `L*` on its side. So the
    /// verdict read here equals the true one in every case.
    ///
    /// The message: where the region `U_from - L_to` were made larger by an infinite sure set
    /// read as empty, its least key could be one the other side holds, and the message would
    /// say "nothing shows" it is there. Claim: no family has an infinite sure set of int keys,
    /// so this never happens. Proof, by the sites that make a signature data (`data = true`,
    /// `data: true` and `data: <expr>` searched in every zedc crate, 2026-11-20, audit
    /// proofdoc2b); a site that copies `data` from another signature (`data: s.data` in the
    /// maps of ty.rs and walk.rs) keeps or substitutes its arrows, so it is covered by the
    /// site the signature came from, given that no data signature has an exact arrow on a
    /// type variable (each site below):
    /// - partial arrows only, so no sure key: `strings_rank`, the `Array` type in `Ck::make`
    ///   and `port` (a `Lines` input), all in mod.rs; `chunkBy` (here); `read_as_family` and
    ///   the families of remap.rs; a range (`Ck::range_end` in walk.rs); the errors family of
    ///   ty.rs (keys not ints). `Ck::key_outside` in walk.rs makes a family for the text of a
    ///   menu only;
    /// - a map or set display (`display_ty` in walk.rs): its sure keys are the union of its
    ///   keys that are one value each, a finite set. Before the audit proofdoc2b
    ///   (2026-11-20) a key of many values, `{ n -> 10 }` at `n: int`, was a sure key too:
    ///   the infinite sure set `int`, the case this paragraph needs; test
    ///   `l03_02_map_run::types::a_key_of_many_values_is_permitted_not_guaranteed`;
    /// - a list concat ([`Self::list_concat_end`]): exact keys `0 ..< n + m` or the finite
    ///   union `0 | … | n + m - 1`, else partial;
    /// - a `zip` (above and [`Self::zip_sig`]): partial where the keys are shown shared by
    ///   origin; else the sure key type is `U_a` or `U_b`, accepted only where `U_x ⊆ L_y`,
    ///   and since an infinite `U` is read as `top` and an infinite `L` as empty, that holds
    ///   only where both are finite; an operand of unresolved type records a need and is
    ///   checked again at each call with its type resolved (row ZIP-generic-operands), so
    ///   no variable reaches the arrow.
    ///
    /// So every sure set of int keys is finite, `of` reads it exactly, and the message is
    /// right. What the tests cannot catch: a site added later that makes a data signature
    /// with an exact arrow on an infinite int type; the search above must be made again then.
    // Complexity tradeoff: O(k log k) for a family whose key type lists k ints, as an array
    // display, the cost of its type, and O(1) for one with exact keys, against O(b - a) for
    // listing the keys of `a ..< b` as the naive way would (row RANGE-literal-keys); a meet
    // and a join of the piece sets per family, linear in their pieces.
    fn key_ints(sigs: &[Arc<Sig>]) -> Option<(IntervalSet, IntervalSet)> {
        let ints = Ty::carrier(Carrier::Int);
        // The ints of the key type `t`, which holds only ints.
        let of = |t: &Ty, infinite: IntervalSet| match t.set.ints_listed() {
            Some(vs) => IntervalSet::from_pieces(
                (vs.iter())
                    .map(|v| int_end(v).expect("a key type's int"))
                    .map(|e| (e.clone(), e))
                    .collect(),
            ),
            None => infinite,
        };
        let mut l: Option<IntervalSet> = None;
        let mut u = IntervalSet::empty();
        for s in sigs {
            let (sure, may) = match &s.keys {
                Some(k) => (written_ints(k), written_ints(k)),
                None => {
                    let (sure, may) = Self::key_bounds(std::slice::from_ref(s));
                    if !may.subtype(&ints) {
                        return None;
                    }
                    (
                        of(&sure, IntervalSet::empty()),
                        of(&may, IntervalSet::top()),
                    )
                }
            };
            l = Some(match l {
                None => sure,
                Some(l) => l.meet(&sure),
            });
            u = u.join(&may);
        }
        Some((l?, u))
    }

    /// The count of every list of `sigs` where one count fits them all, as
    /// [`Self::known_count`], reading exact keys ([`Sig::keys`]): `0 ..< 3` has 3 entries
    /// whatever its digits. `None` where the count is not one known number. Each family is a
    /// list ([`Self::list_concat_end`]), so its keys are `0 ..< n`; the count is `n` exactly
    /// where `L = U`, every key sure, and that set is empty or `[0, n - 1]`.
    // Complexity tradeoff: O(k log k) for listed keys and O(1) for exact ones (`key_ints`);
    // `known_count` alone would need the keys listed, O(n) for a range of n.
    // Why `L = U` and the set being `[0, n - 1]` give the count: `L` is the set of keys every
    // value surely holds and `U` the set it may hold, so `L = U` fixes the key set; a set of n
    // distinct ints with least 0 and greatest n - 1 that is one interval holds exactly n ints.
    // Tests: tests/steps/l03_15a_fp_ops_run cases.rs `a_range_with_literal_ends_has_exact_keys`
    // and `a_zip_of_ranges_with_unequal_keys_is_rejected`; chosen ranges only.
    fn ranks_count(sigs: &[Arc<Sig>]) -> Option<Num> {
        let (l, u) = Self::key_ints(sigs)?;
        if l != u {
            return None;
        }
        if u.is_empty() {
            return Some(Num::from(0i64));
        }
        match u.only()? {
            (Fin(lo), Fin(hi)) if *lo == Num::from(0i64) => Some(hi + &Num::from(1i64)),
            _ => None,
        }
    }

    /// `a ++ b` where an operand may be a family (step L5.2; DESIGN.md sec:joins, ordered
    /// concatenation): each family must be a list, its keys the ranks `0 ..< n`, and the
    /// result is the list of `a`'s entries and then `b`'s, the keys of `b` moved up by
    /// `a.count`. A loose atom of either operand passes through, `a`'s first. With every count
    /// known the keys are `0 ..< n + m`, each sure; otherwise the result is `int ->? V`, as a
    /// range is. A string beside a list, or a family whose keys are not ranks, as a `where`
    /// result, is rejected.
    ///
    /// `site` is where the `++` is written, which elaboration builds as a list join on
    /// success; `None` where `meet` checks a [`NeedKind::Concat`] at `span`, the `++` having
    /// been recorded where it is written. `need` is `Ck::need`, passed in as at
    /// [`Self::strings_end`].
    ///
    /// Each variable of an operand takes the `++` as `.sum` takes a variable
    /// (`Ck::level_word`, row FP-ops-concat-fold-acc): a class resolved to a type takes it on
    /// that type; one not yet resolved records it as a need on its class, met at each call of
    /// the generic function, and at each application of a lambda such as a fold's, on the
    /// type the call gives it; a variable with no class, which a written type parameter is,
    /// is not supported by this zedc. The rest of the operand takes it as it stands, and the
    /// results are joined: `++` is checked piece by piece, so the join of the pieces' results holds
    /// the whole's. A `++` with an operand that may be a family is a list join wherever it is
    /// met, since a string beside a list is rejected, so it is recorded at `site` with the
    /// need, before any call shows the variable's type.
    // Complexity tradeoff: one need or one recursion per variable of each operand, plus one
    // check of the rest, as at `level_word`; the check itself is O(arrows) per family. The
    // naive method, refusing a variable (what this did before row FP-ops-concat-fold-acc),
    // costs nothing but refuses every list built by `++` in a fold. Proof that the recursion
    // ends: the rest of an operand holds no variable, and a class is resolved to a type that
    // holds none (the invariant at `Class::resolved`), so each recursive call has one operand
    // fewer with a variable; `need` records each pair of a class and a use once, before it
    // checks the use on the values that flowed in (the visited set of P207), as at
    // `level_word`.
    pub(super) fn list_concat_end(
        &mut self,
        x: &Arg<'a>,
        y: &Arg<'a>,
        span: Span,
        site: Option<Span>,
        need: NeedFn<'t, 'a>,
    ) -> Ty {
        // Taken at once, so no other check reads it; given again to the checks of the
        // operand's pieces below, which are of the one call.
        let from = self.concat_from.take();
        for (side, this) in [x, y].into_iter().enumerate() {
            if this.ty.vars.is_empty() {
                continue;
            }
            let that = [x, y][1 - side];
            // The operand `this` with the type `t` in its place, `++` checked on it.
            let with = |ck: &mut Self, t: Ty| {
                let mut a = this.clone();
                a.ty = t;
                let (a, b) = if side == 0 { (&a, that) } else { (that, &a) };
                ck.concat_from = from;
                ck.list_concat_end(a, b, span, site, need)
            };
            let mut rest = this.ty.clone();
            rest.vars = VarSet::new();
            let mut out = match rest.is_empty() {
                true => Ty::empty(),
                false => with(self, rest),
            };
            for v in this.ty.vars.iter() {
                let t = match self
                    .class_root(v)
                    .map(|r| (r, self.classes[r].resolved.clone()))
                {
                    Some((_, Some(t))) => with(self, t),
                    Some((r, None)) => {
                        if let Some(s) = site
                            && !self.trying
                        {
                            self.info.list_concats.insert(s);
                        }
                        // The class is checked when it is resolved, with no frame of this call:
                        // the argument is kept for the repair there ([`Ck::concat_args`]).
                        if let Some((arg, first)) = from
                            && first == (side == 0)
                            && !self.trying
                        {
                            let on: Arc<str> = format!("${}", self.find(r)).into();
                            self.concat_args.insert((span, first, on), arg);
                        }
                        let kind = NeedKind::Concat {
                            other: that.ty.clone(),
                            first: side == 0,
                        };
                        need(self, r, kind, true, span)
                    }
                    None => {
                        self.generic_operand(this, span);
                        return Ty::empty();
                    }
                };
                out = out.union(&t);
            }
            return out;
        }
        let word = "`++`";
        let out =
            (self.passing(&x.ty, word, span, x.at)).union(&self.passing(&y.ty, word, span, y.at));
        let mut sides: Vec<Vec<Arc<Sig>>> = Vec::new();
        for (side, a) in [x, y].into_iter().enumerate() {
            let at = a.at.unwrap_or(span);
            let mut sigs = Vec::new();
            for p in a.ty.pieces() {
                match p {
                    Piece::Fn(sig) if joins_as_list(&sig) => sigs.push(sig),
                    Piece::Fn(sig) if sig.data => {
                        let t = self.text(&Ty::func(sig));
                        self.error_offering(
                            at,
                            format!(
                                "`++` joins lists, whose keys are the ranks `0`, `1`, …, and \
                                 this family is {t}, whose keys are not ranks"
                            ),
                            ["repair: join lists, as `[1, 2] ++ [3]`".to_string()],
                        );
                        return Ty::empty();
                    }
                    Piece::Dyn => self.any(word, span),
                    // No path reaches this arm (TEST-generic-operand-messages-reached). Proof:
                    // 1. `Ty::pieces_lazily` (zedc-types ty.rs) makes a `Piece::Var` only from
                    //    `a.ty.vars`, and no other piece is a `Piece::Var`.
                    // 2. The loop over both operands above returns whenever `x.ty.vars` or
                    //    `y.ty.vars` is not empty, so here both are empty.
                    // 3. So by 1 no piece of `a`, which is `x` or `y`, is a `Piece::Var`.
                    Piece::Var(_) => unreachable!("`list_concat_end` returned above for variables"),
                    p if p.is_atoms() => {}
                    p => {
                        let t = self.text(&p.ty());
                        // The repair with both operands as the program wrote them, where on
                        // one line, this one in a list (plan row MSG-example-repairs). The other
                        // operand keeps its place, so it takes parentheses only where `++`
                        // needs them there (author rule P191), as the formatter decides, and
                        // the parentheses the program wrote around it are kept.
                        let other = [x, y][1 - side];
                        let this = self.operand_text(a.at).unwrap_or_else(|| "x".to_string());
                        let other = match (self.operand_text(other.at), other.expr) {
                            (Some(c), Some(e))
                                if zedc_syntax::format::operand_needs_parens(
                                    e,
                                    BinaryOp::Concat,
                                    side == 0,
                                ) && !zedc_syntax::lex::in_parens(&c) =>
                            {
                                format!("({c})")
                            }
                            (Some(c), Some(_)) => c,
                            (Some(c), None) => postfix_operand(&c),
                            (None, _) => "xs".to_string(),
                        };
                        let form = match side {
                            0 => format!("[{this}] ++ {other}"),
                            _ => format!("{other} ++ [{this}]"),
                        };
                        // Checked at a call, the operand has no text of its own: where an
                        // argument written in the program is its whole value, the repair is
                        // that call with the argument put in a list, as `app(["s"])`, not
                        // the template `[x] ++ xs` (plan row MSG-concat-need-repair-template).
                        let at_call = match (a.at, from) {
                            (None, Some((arg, first))) if first == (side == 0) => (self
                                .operand_text(Some(arg.at)))
                            .map(|t| (arg.at, format!("[{t}]")))
                            .and_then(|e| edited(self.t.text?, arg.call, &[&e]))
                            .map(|t| t.trim().to_string())
                            .filter(|t| !t.contains('\n')),
                            _ => None,
                        };
                        let form = at_call.unwrap_or(form);
                        self.error_offering(
                            at,
                            format!(
                                "`++` joins two lists or two strings, and this value is {t}, \
                                 beside a list"
                            ),
                            [format!("repair: put the value in a list, as `{form}`")],
                        );
                        return Ty::empty();
                    }
                }
            }
            sides.push(sigs);
        }
        let [a, b] = <[_; 2]>::try_from(sides).expect("two operands");
        if a.is_empty() || b.is_empty() {
            return out;
        }
        let values = Self::entries_of(&a).union(&Self::entries_of(&b));
        let keyed = a.iter().chain(&b).any(|s| s.keys.is_some());
        // With an operand of exact keys, as `0 ..< 3`, the result's keys are `0 ..< n + m`
        // kept as two ends, the arrow the range's `int ->? V` (row RANGE-literal-keys). Proof:
        // the run's list holds `a`'s n entries at `0 ..< n` and `b`'s m at `n ..< n + m`, and
        // `ranks_count` gives each count exactly. Complexity tradeoff: O(1) for the two ends,
        // where listing the keys `0 | 1 | … | n + m - 1` as below would cost O(n + m) for
        // the text `0 ..< n` of O(log n) digits.
        let sig = match (keyed, Self::ranks_count(&a), Self::ranks_count(&b)) {
            (true, n, m) => {
                let int = vec![Ty::carrier(Carrier::Int)];
                let mut sig = Sig::one_partial(positional(1), int, values);
                if let (Some(n), Some(m)) = (n, m) {
                    let last = &(&n + &m) - &Num::from(1i64);
                    sig.keys = exact_keys(&IntervalSet::range(Fin(Num::from(0i64)), Fin(last)));
                }
                sig
            }
            _ => match (Self::known_count(&a), Self::known_count(&b)) {
                (Some(n), Some(m)) => {
                    let keys: Vec<Ty> = (0..(n + m) as i64)
                        .map(|i| Ty::lit(&Value::Int(i)))
                        .collect();
                    Sig::one(positional(1), vec![Ty::union_all(keys.iter())], values)
                }
                _ => Sig::one_partial(positional(1), vec![Ty::carrier(Carrier::Int)], values),
            },
        };
        let mut sig = sig;
        sig.data = true;
        sig.dense = Dense::Ranks;
        sig.note_held();
        if let Some(s) = site
            && !self.trying
        {
            self.info.list_concats.insert(s);
        }
        out.union(&Ty::func(Arc::new(sig)))
    }

    /// The error for `++` on the operand `a`, whose type is a variable of no class, as a
    /// written type parameter's. As at `levels_of`, the program may write no type parameter,
    /// so the operand's type is called generic. The error stands at the operand, where it has
    /// one, whose derivation says what it is, as a lambda's parameter given each entry of a
    /// family is (plan row MSG-concat-generic-lambda-param-no-note); else at the `++`, `span`.
    fn generic_operand(&mut self, a: &Arg<'a>, span: Span) {
        let what = match self.operand_text(a.at) {
            Some(c) => format!("`++` on `{c}`, whose type is generic here,"),
            None => "`++` on a value whose type is generic here".to_string(),
        };
        self.error(a.at.unwrap_or(span), zedc_base::rejection::not_yet(&what));
    }

    /// `a.zip(b)` (step L5.2; DESIGN.md sec:joins): the equality join on keys,
    /// `joinR(#assertEmpty, #keep, #assertEmpty)`, the family of the pairs `(a[k], b[k])`. Its
    /// two asserted-empty regions, the keys `a` may hold that `b` may lack and the reverse,
    /// must be proved empty: `U_a ⊆ L_b` and `U_b ⊆ L_a` (DESIGN.md sec:type_language, "One
    /// rule for every join"). An assertion not proved is a static error, which names one key
    /// the bounds admit into the region (sec:diagnostics, "Undischarged region assertion"):
    /// `[1, 2].zip([1])` holds key `1` on one side only, and a zip of two `Lines` inputs is
    /// rejected too, since nothing shows their counts equal. Proved, the four bounds are one
    /// set, so the result's keys are sure: for each operand `L ⊆ U` (`L` is a meet that
    /// includes the first family's sure keys, a union over some of its arrows, and `U` the
    /// union over all arrows of all families; [`Self::key_bounds`]), so
    /// `U_a ⊆ L_b ⊆ U_b ⊆ L_a ⊆ U_a`, and every key either side may hold is held by every
    /// family of both. A loose atom of either operand passes through. Tests:
    /// `l03_15a_fp_ops_run::cases::zip_pairs_equal_keys`,
    /// `a_zip_of_ranges_with_unequal_keys_is_rejected` and `concatenation_zip_and_its_law`.
    ///
    /// Each variable of an operand takes the `zip` as at [`Self::list_concat_end`] (row
    /// ZIP-generic-operands): a class resolved to a type takes it on that type; one not yet
    /// resolved records it as a need on its class ([`NeedKind::Zip`]), met at each call of the
    /// generic function on the type the call gives it, where the arguments' own expressions
    /// show whether they share their keys ([`Self::zip_shares_keys`]); a variable with no
    /// class, which a written type parameter is, is not supported by this zedc. `need` is
    /// `Ck::need`, passed in as at `list_concat_end`, so this file imports nothing of walk.rs.
    // Complexity tradeoff: the bounds over all the families each operand may be, two
    // subtype tests and one diff for the message, linear in the arrows (`key_bounds`); plus
    // one need or one recursion per variable of each operand, as at `list_concat_end`, whose
    // proof that the recursion ends holds here word for word (the rest of an operand and a
    // resolved class hold no variable, so each recursive call has one operand fewer with a
    // variable). The naive method, refusing a variable (what this did before the row), costs
    // nothing but refuses every generic function whose body zips its parameters.
    pub(super) fn zip_end(
        &mut self,
        x: &Arg<'a>,
        y: &Arg<'a>,
        span: Span,
        shared: bool,
        need: NeedFn<'t, 'a>,
    ) -> Ty {
        let classed = |ck: &Self, a: &Arg<'a>| a.ty.vars.iter().all(|v| ck.class_root(v).is_some());
        for (side, this) in [x, y].into_iter().enumerate() {
            // A variable of no class falls to `levels_of` below, which refuses it.
            if this.ty.vars.is_empty() || !classed(self, this) {
                continue;
            }
            let that = [x, y][1 - side];
            // Whether the operands come from one place is read here, where their expressions
            // are, and kept in the need: where it is met they may have none, as the
            // application of a lambda has none ([`NeedKind::Zip`]).
            let shared = shared || self.zip_one_origin(x, y);
            // The operand `this` with the type `t` in its place, `zip` checked on it.
            let with = |ck: &mut Self, t: Ty| {
                let mut a = this.clone();
                a.ty = t;
                let (a, b) = if side == 0 { (&a, that) } else { (that, &a) };
                ck.zip_end(a, b, span, shared, need)
            };
            let mut rest = this.ty.clone();
            rest.vars = VarSet::new();
            let mut out = match rest.is_empty() {
                true => Ty::empty(),
                false => with(self, rest),
            };
            for v in this.ty.vars.iter() {
                let Some(r) = self.class_root(v) else {
                    continue;
                };
                let t = match self.classes[r].resolved.clone() {
                    Some(t) => with(self, t),
                    None => {
                        let kind = NeedKind::Zip {
                            other: that.ty.clone(),
                            first: side == 0,
                            shared,
                        };
                        need(self, r, kind, true, span)
                    }
                };
                out = out.union(&t);
            }
            return out;
        }
        let word = "`zip`";
        let example = "[1, 2].zip([3, 4])";
        // A parameter declared a partial map is read as a family (`Ck::read_as_family`).
        let (xf, yf) = (
            self.read_as_family(x.expr, &x.ty, word),
            self.read_as_family(y.expr, &y.ty, word),
        );
        let (xt, yt) = (xf.as_ref().unwrap_or(&x.ty), yf.as_ref().unwrap_or(&y.ty));
        let out = (self.passing(xt, word, span, x.at)).union(&self.passing(yt, word, span, y.at));
        let Some(a) = self.levels_of(xt, word, example, x.at.unwrap_or(span), x.at) else {
            return Ty::empty();
        };
        let Some(b) = self.levels_of(yt, word, example, y.at.unwrap_or(span), y.at) else {
            return Ty::empty();
        };
        if a.is_empty() || b.is_empty() {
            return out;
        }
        let (la, ua) = Self::key_bounds(&a);
        let (lb, ub) = Self::key_bounds(&b);
        let texts = [self.operand_text(x.at), self.operand_text(y.at)];
        let names = [
            (texts[0].as_ref())
                .map_or("the family before `.zip`".to_string(), |c| format!("`{c}`")),
            (texts[1].as_ref()).map_or("the argument of `zip`".to_string(), |c| format!("`{c}`")),
        ];
        // The ranks both lists hold, offered where both operands' keys are integers.
        let ints = Ty::carrier(Carrier::Int);
        let ranks = (ua.subtype(&ints) && ub.subtype(&ints)).then(|| {
            let [p, q] = [0, 1].map(|i| {
                (texts[i].as_deref()).map_or(["xs", "ys"][i].to_string(), postfix_operand)
            });
            format!(
                "repair: pair the ranks both lists hold, as \
                 `(0 ..< min({p}.count, {q}.count)).map(i -> ({p}[i], {q}[i]))`"
            )
        });
        // Where an operand has exact keys, as a range with literal ends ([`Sig::keys`]), the
        // bounds are sets of ints and the tests are on them (row RANGE-literal-keys): the
        // keys of `0 ..< 3` are `[0, 2]`, two ends, not a key type. Complexity tradeoff: a
        // subset test and a difference of piece sets, linear in their pieces, O(1) for two
        // ranges; the naive way, each range's keys listed in its key type, costs O(b - a).
        let keyed = a.iter().chain(&b).any(|s| s.keys.is_some());
        let sets = match keyed {
            true => Self::key_ints(&a).zip(Self::key_ints(&b)),
            false => None,
        };
        // Whether the operands are shown to share their keys by where they come from, which
        // the bounds of their types cannot show (plan row ZIP-count-facts): read only where
        // the bounds leave a region, so a zip the bounds prove costs nothing more. `shared`
        // says the need this check meets was made where they were shown to.
        let mut shared_keys = None;
        for from in [0, 1] {
            // The least key of the region `U_from - L_to`, the keys `from` may hold that the
            // other side may lack, and whether `from` surely holds it and the other surely
            // not; `Err` where the region is empty, as the join needs.
            let found: Result<Option<(Value, bool)>, ()> = match &sets {
                Some(((la, ua), (lb, ub))) => {
                    let [(l_from, u_from), (l_to, u_to)] = match from {
                        0 => [(la, ua), (lb, ub)],
                        _ => [(lb, ub), (la, ua)],
                    };
                    let region = u_from.minus(l_to);
                    match region.first() {
                        None => Err(()),
                        // A region with no least key, as every int below 0, names none.
                        Some((Fin(k), _)) => {
                            let e = Fin(k.clone());
                            let sure = l_from.contains_end(&e) && !u_to.contains_end(&e);
                            Ok(Some((Value::from(k), sure)))
                        }
                        Some(_) => Ok(None),
                    }
                }
                None => {
                    let [(l_from, u_from), (l_to, u_to)] = match from {
                        0 => [(&la, &ua), (&lb, &ub)],
                        _ => [(&lb, &ub), (&la, &ua)],
                    };
                    match self.subtype(u_from, l_to) {
                        true => Err(()),
                        false => {
                            let region = u_from.diff(l_to);
                            let one =
                                (region.set.values_listed()).and_then(|vs| vs.into_iter().next());
                            Ok(one.map(|v| {
                                let sure = l_from.contains(&v) && !u_to.contains(&v);
                                (v, sure)
                            }))
                        }
                    }
                }
            };
            let Ok(one) = found else {
                continue;
            };
            if *shared_keys.get_or_insert_with(|| shared || self.zip_shares_keys(x, y, span)) {
                break;
            }
            let (a, b) = (&names[from], &names[1 - from]);
            let head = "`zip` pairs the entries at equal keys, and";
            let message = match &one {
                Some((v, true)) => {
                    let key = self.text(&Ty::lit(v));
                    format!("{head} key {key} is in {a} but not in {b}")
                }
                Some((v, false)) => {
                    let key = self.text(&Ty::lit(v));
                    format!("{head} nothing shows that key {key} of {a} is in {b}")
                }
                None => format!("{head} nothing shows that each key of {a} is in {b}"),
            };
            let same = "repair: give both operands the same keys, as `[1, 2].zip([3, 4])`";
            let menu = std::iter::once(same.to_string()).chain(ranks);
            self.error_offering(span, message, menu);
            return Ty::empty();
        }
        let pair = Ty::tuple(vec![Self::entries_of(&a), Self::entries_of(&b)]);
        // Shown to share their keys by their origins, the operands hold one set of keys `K`
        // in each run, which their types bound only as `L_a ∪ L_b ⊆ K ⊆ U_a ∩ U_b`: the keys
        // are typed `U_a ∩ U_b`, the arrow partial, and a read of a key outside `K` misses.
        // What either side's type knows of its keys' shape holds for `K`, as below.
        let mut sig = if shared_keys == Some(true) {
            Sig::one_partial(positional(1), vec![ua.meet(&ub)], pair)
        } else {
            Self::zip_sig(&sets, &a, &b, ua, ub, pair)
        };
        sig.data = true;
        // The two keyspaces were shown equal above, so what either side's type knows of its
        // keys holds for the pairs' keys: the ranks if either side is a list, else one
        // interval if either side is a range.
        let all = |side: &[Arc<Sig>], d: fn(Dense) -> bool| side.iter().all(|s| d(s.dense));
        let is_ranks = |d: Dense| d == Dense::Ranks;
        sig.dense = if all(&a, is_ranks) || all(&b, is_ranks) {
            Dense::Ranks
        } else if all(&a, Dense::interval) || all(&b, Dense::interval) {
            Dense::Interval
        } else {
            Dense::No
        };
        sig.note_held();
        out.union(&Ty::func(Arc::new(sig)))
    }

    /// The signature of a `zip` whose bounds proved both operands' keys one set
    /// ([`Self::zip_end`]).
    fn zip_sig(
        sets: &Option<KeyIntPair>,
        a: &[Arc<Sig>],
        b: &[Arc<Sig>],
        ua: Ty,
        ub: Ty,
        pair: Ty,
    ) -> Sig {
        // Shown above, `U_a ⊆ L_b ⊆ U_b ⊆ L_a ⊆ U_a`, so the four are one set, every key of
        // it in every family of both sides. An operand none of whose families has exact keys
        // writes that set as its key type `U`, a sure key type, as for two lists. Where both
        // have exact keys, the set is one interval (the `L` of a side with exact keys lies in
        // them, and equals `U`, which holds them), kept as two ends on the arrow `int ->?`.
        let plain = |side: &[Arc<Sig>]| side.iter().all(|s| s.keys.is_none());
        match (sets, plain(a), plain(b)) {
            (Some(((_, u), _)), false, false) => {
                let int = vec![Ty::carrier(Carrier::Int)];
                let mut sig = Sig::one_partial(positional(1), int, pair);
                sig.keys = exact_keys(u);
                sig
            }
            (_, _, true) => Sig::one(positional(1), vec![ub], pair),
            _ => Sig::one(positional(1), vec![ua], pair),
        }
    }
}

/// The lower and upper key sets of both operands of a `zip` ([`Ck::key_ints`]).
type KeyIntPair = ((IntervalSet, IntervalSet), (IntervalSet, IntervalSet));

/// The assumption [`Ck::keyspace`] reads a recursive call of a declared function under while
/// that function's record is found ([`Ck::record_fn`]): the function, and the parameter whose
/// keys its result is assumed to keep, or none, whose calls then give [`Space::Any`].
type Assume = Option<(usize, Option<usize>)>;

/// One step of [`Ck::keyspace`]'s walk.
enum KsTask<'a> {
    /// Read the keyspace of the expression.
    Eval(&'a Expr),
    /// The last `n` keyspaces read are the branches of the `if` at the span: join them.
    Join(Span, usize),
    /// The last keyspace read is the binder's value's: keep it.
    Memo(usize),
    /// The last keyspace read holds only under the assumption.
    Taint,
}

/// What [`Ck::ks_step`] makes of one expression.
enum KsStep<'a> {
    /// Its keyspace, and whether it holds only under the assumption.
    Done(Space, bool),
    /// Its keyspace is that expression's.
    Then(&'a Expr),
    /// Its keyspace is that expression's, read under the assumption.
    Assumed(&'a Expr),
    /// It is a name bound to that value: its keyspace is the value's, kept for the binder.
    Bind(usize, &'a Expr),
    /// It is an `if`: its keyspace is the branches' where they agree.
    Join(Span, [&'a Expr; 2]),
}

/// What a callee may be, for the keyspace record of its call ([`Ck::callee_record`]).
#[derive(Clone, Copy, PartialEq)]
enum Callee {
    /// A declared function, by its binder.
    Fn(usize),
    /// A lambda, by its span.
    Lambda(Span),
}

impl<'t, 'a> Ck<'t, 'a> {
    /// The keyspace of the value of `e` (plan row ZIP-count-facts; DESIGN.md sec:joins, "What
    /// proves two keyspaces equal"), and whether it holds only under `assume`. Two values whose
    /// keyspaces this gives equal, read in one run of one scope, hold the same keys. A form not
    /// listed gives a keyspace of its own, [`Space::Own`] at its span, equal to no other but
    /// itself, which is the safe answer: it proves nothing.
    ///
    /// Proof, by induction on the walk below, for two expressions read at one evaluation of
    /// the expression that holds them both (the operands of a `zip`, or a range and a read
    /// inside the lambda it is mapped with, which runs in the frame the range was read in):
    /// - A name with one binder in [`Ck::facts`] (`name = value`, bound once: Zed has no
    ///   assignment) holds the value `value` had where it was bound, so its keyspace is
    ///   `value`'s. The names inside `value` are resolved where it was bound, in a scope
    ///   around the reading one, so they name the same values from both operands.
    /// - Any other name with one binder, not a function: [`Space::Binder`], its own value. A
    ///   parameter, a port of `main` and a pattern's name hold one value in a run of their
    ///   scope.
    /// - `m.name` with no call and no function of the program named `name` reads a member
    ///   of one value: the same value for the same `m` ([`Space::Member`]). The members such a
    ///   form reads are the prelude's (`count`, `first`, a port of `MainArgs`): each a function
    ///   of its operand alone. The ports of `main` are read once, before the body runs, so
    ///   `m.stdin` is one value however often it is written (`zedc-elab`'s `main` binds each
    ///   port to its parameter once).
    /// - `a.map(f)` and `a.zip(b)` with the prelude's words keep the keys of `a`: `map` gives
    ///   an entry at each key of `a`, and a `zip` that checks has the keys both share.
    /// - `0 ..< x.count`, `x` a list ([`Dense::Ranks`]: its keys are `0 ..< n` for its count
    ///   `n`), has the keys of `x`. Any other range `a ..< b` or `a ..= b` holds the ints
    ///   between its ends, so two whose ends are the same ints the text fixes ([`Ck::known`],
    ///   proved there) or the same binders hold the same keys ([`Space::Range`]). A name whose
    ///   value is `x.count` is followed to it.
    /// - `if c { a } else { b }`: the value is one branch's, so where both have one keyspace
    ///   it is that one. Else it is a value of its own. A block that binds names and returns
    ///   one value has that value's keyspace.
    /// - A call whose callee is a declared function, a lambda, or a name bound to them (through
    ///   names and `if`s), each of which records that its result has the keys of its
    ///   parameter `i` ([`Ck::record_fn`]), has the keys of the argument at `i`. A callee
    ///   that may be several functions keeps the record only where all of them record the
    ///   same parameter, and its arguments are then placed by position only, as a call of a
    ///   value places them.
    /// - Under the assumption `(f, i)`, a call of `f` has the keys of its argument at `i`; that
    ///   is what [`Ck::record_fn`] proves by induction, and every keyspace read through it is
    ///   marked as holding only under the assumption, so it is never kept.
    ///
    /// The `if` and the calls are the only branching; a name's value is followed once per
    /// read ([`KsTask::Memo`] keeps it for the read, and for later reads when no assumption
    /// was used).
    // Complexity tradeoff: each name's binder is followed once per read and once in all where
    // no assumption is used (the memo), so n `zip`s of names each bound to a chain of `map`s
    // over k bindings cost O(n + k); the naive walk, each read following the chain again,
    // costs O(n k). A union-find of the classes, as the plan row describes, would merge the
    // classes as bindings are made, at the same O(α) per step, but only once the checker walks
    // a body's bindings in one pass with no backtracking, which it does not (a body may be
    // checked again per call); the memo by binder is its equivalent here, since each binder's
    // class is fixed by its value, which never changes.
    pub(super) fn keyspace(&mut self, e: &'a Expr, assume: Assume) -> (Space, bool) {
        let mut tasks = vec![KsTask::Eval(e)];
        let mut vals: Vec<(Space, bool)> = Vec::new();
        // The keyspace of each binder followed in this read, under its assumption: the visited
        // set that keeps each binder followed once (author P207).
        let mut local: HashMap<usize, (Space, bool)> = HashMap::new();
        while let Some(t) = tasks.pop() {
            match t {
                KsTask::Eval(x) => match self.ks_step(x, assume, &local) {
                    KsStep::Done(s, taint) => vals.push((s, taint)),
                    KsStep::Then(y) => tasks.push(KsTask::Eval(y)),
                    KsStep::Assumed(y) => {
                        tasks.push(KsTask::Taint);
                        tasks.push(KsTask::Eval(y));
                    }
                    KsStep::Bind(id, y) => {
                        tasks.push(KsTask::Memo(id));
                        tasks.push(KsTask::Eval(y));
                    }
                    KsStep::Join(span, [a, b]) => {
                        tasks.push(KsTask::Join(span, 2));
                        tasks.push(KsTask::Eval(b));
                        tasks.push(KsTask::Eval(a));
                    }
                },
                KsTask::Memo(id) => {
                    let v = vals.last().expect("a binder's value was read").clone();
                    if !v.1 {
                        self.keyspaces.memo.insert(id, v.0.clone());
                    }
                    local.insert(id, v);
                }
                KsTask::Taint => vals.last_mut().expect("a call was read").1 = true,
                KsTask::Join(span, n) => {
                    let parts = vals.split_off(vals.len() - n);
                    let taint = parts.iter().any(|p| p.1);
                    let mut known = parts.into_iter().map(|p| p.0).filter(|s| *s != Space::Any);
                    let joined = match known.next() {
                        None => Space::Any,
                        Some(s) if known.all(|t| t == s) => s,
                        Some(_) => Space::Own(span),
                    };
                    vals.push((joined, taint));
                }
            }
        }
        vals.pop().expect("the expression was read")
    }

    /// One step of [`Self::keyspace`] on `e`, the rules listed there.
    fn ks_step(
        &mut self,
        e: &'a Expr,
        assume: Assume,
        local: &HashMap<usize, (Space, bool)>,
    ) -> KsStep<'a> {
        let own = KsStep::Done(Space::Own(e.span), false);
        match &e.kind {
            ExprKind::Name(_) => {
                let Some(id) = self.one_binder(e.span) else {
                    return own;
                };
                if let Some((s, taint)) = local.get(&id) {
                    return KsStep::Done(s.clone(), *taint);
                }
                if let Some(s) = self.keyspaces.memo.get(&id) {
                    return KsStep::Done(s.clone(), false);
                }
                match self.facts.get(&id) {
                    Some(&v) => KsStep::Bind(id, v),
                    None if self.t.funcs.contains_key(&id) => own,
                    None => KsStep::Done(Space::Binder(id), false),
                }
            }
            ExprKind::Member {
                of,
                name,
                safe: false,
            } if !self.t.res.uses.contains_key(&e.span) => match self.one_binder(of.span) {
                Some(id) if matches!(of.kind, ExprKind::Name(_)) => {
                    KsStep::Done(Space::Member(id, name.clone()), false)
                }
                _ => own,
            },
            ExprKind::Call {
                callee,
                positional,
                named,
                curry: false,
                ..
            } => {
                if let ExprKind::Member {
                    of,
                    name,
                    safe: false,
                } = &callee.kind
                    && !matches!(self.t.res.uses.get(&callee.span), Some(Ref::Bound(_)))
                {
                    return match (name.as_str(), &positional[..], &named[..]) {
                        ("map" | "zip", [_], []) => KsStep::Then(of),
                        _ => own,
                    };
                }
                let receiver = match &callee.kind {
                    ExprKind::Member { of, .. } => Some(&**of),
                    _ => None,
                };
                let Some((record, direct)) = self.callee_record(callee, assume) else {
                    return own;
                };
                let arg = |i: usize| self.placed(record.0, direct, receiver, positional, named, i);
                match record.1 {
                    Recorded::Assumed(None) => KsStep::Done(Space::Any, true),
                    Recorded::Assumed(Some(i)) => arg(i).map_or(own, KsStep::Assumed),
                    Recorded::Kept(i) => arg(i).map_or(own, KsStep::Then),
                }
            }
            ExprKind::Range(lo, end) => {
                let (hi, through) = match end {
                    RangeEnd::Below(h) => (&**h, false),
                    RangeEnd::Through(h) => (&**h, true),
                    RangeEnd::Open => return own,
                };
                let zero = self.known(lo).value == Some(Value::from(0));
                if zero
                    && !through
                    && let Some(x) = self.count_of_list(hi)
                {
                    return KsStep::Then(x);
                }
                match (self.ks_end(lo), self.ks_end(hi)) {
                    (Some(a), Some(b)) => KsStep::Done(Space::Range(a, b, through), false),
                    _ => own,
                }
            }
            ExprKind::If {
                then, otherwise, ..
            } => KsStep::Join(e.span, [then, otherwise]),
            ExprKind::Block(_) => block_value(e).map_or(own, KsStep::Then),
            _ => own,
        }
    }

    /// The binder of the name or member at `span`, where it has one.
    pub(super) fn one_binder(&self, span: Span) -> Option<usize> {
        match self.t.res.uses.get(&span) {
            Some(Ref::Bound(ids)) if ids.len() == 1 => Some(ids[0]),
            _ => None,
        }
    }

    /// An end of a range as [`Space::Range`] holds it: the int the text fixes, else the
    /// binder of a name.
    fn ks_end(&mut self, e: &'a Expr) -> Option<KsEnd> {
        if let Some(v) = self.known(e).value {
            return Some(KsEnd::Val(v));
        }
        match e.kind {
            ExprKind::Name(_) => self.one_binder(e.span).map(KsEnd::Name),
            _ => None,
        }
    }

    /// The list `x` where `e` is `x.count`, the prelude's count, or a name bound to it,
    /// followed through `name = value` binders: `0 ..< e` then holds the keys of `x`
    /// ([`Dense::Ranks`]: the keys of a list are the ranks below its count).
    fn count_of_list(&self, mut e: &'a Expr) -> Option<&'a Expr> {
        // Each binder is followed once (author P207); the binders' values are acyclic, so
        // this holds only against a wrong table.
        let mut seen = HashSet::new();
        loop {
            match &e.kind {
                ExprKind::Name(_) => {
                    let id = self.one_binder(e.span)?;
                    if !seen.insert(id) {
                        return None;
                    }
                    e = self.facts.get(&id)?;
                }
                ExprKind::Member {
                    of,
                    name,
                    safe: false,
                } if name == "count" && !self.t.res.uses.contains_key(&e.span) => {
                    return self.is_list(of).then_some(&**of);
                }
                _ => return None,
            }
        }
    }

    /// Whether the checker found `e` a list: every family it may be has the ranks as keys
    /// ([`Dense::Ranks`]), and it is nothing else.
    fn is_list(&self, e: &Expr) -> bool {
        let Some((Some(t), _)) = self.seen.get(&e.span) else {
            return false;
        };
        let mut any = false;
        for p in t.pieces() {
            match p {
                Piece::Fn(sig) if sig.data && sig.dense == Dense::Ranks => any = true,
                _ => return false,
            }
        }
        any
    }

    /// What `callee` may be, and the parameter whose keys its result keeps, where every
    /// function it may be keeps the same one ([`Self::keyspace`]); with whether it names one
    /// declared function directly, by name or as a method, so that its arguments are placed
    /// as that function's parameters take them.
    fn callee_record(
        &self,
        callee: &'a Expr,
        assume: Assume,
    ) -> Option<((Callee, Recorded), bool)> {
        let direct = match self.one_binder(callee.span) {
            Some(id) if self.t.funcs.contains_key(&id) => Some(id),
            _ => None,
        };
        let mut fns = Vec::new();
        let mut todo = vec![callee];
        let mut seen = HashSet::new();
        while let Some(c) = todo.pop() {
            if !seen.insert(c.span) {
                continue;
            }
            match &c.kind {
                ExprKind::Lambda { body, .. } => fns.push(Callee::Lambda(body.span)),
                ExprKind::If {
                    then, otherwise, ..
                } => todo.extend([&**then, &**otherwise]),
                ExprKind::Block(_) => todo.push(block_value(c)?),
                ExprKind::Name(_) | ExprKind::Member { .. } => {
                    let id = self.one_binder(c.span)?;
                    match self.facts.get(&id) {
                        _ if self.t.funcs.contains_key(&id) => fns.push(Callee::Fn(id)),
                        Some(&v) => todo.push(v),
                        None => return None,
                    }
                }
                _ => return None,
            }
        }
        let mut record = None;
        for f in &fns {
            let r = match *f {
                Callee::Fn(id) if assume.is_some_and(|(a, _)| a == id) => {
                    Recorded::Assumed(assume?.1)
                }
                Callee::Fn(id) => Recorded::Kept((*self.keyspaces.fns.get(&id)?)?),
                Callee::Lambda(s) => Recorded::Kept((*self.keyspaces.lambdas.get(&s)?)?),
            };
            match record {
                None => record = Some(r),
                Some(q) if q == r => {}
                Some(_) => return None,
            }
        }
        let first = *fns.first()?;
        let direct = direct.is_some() && fns.len() == 1;
        Some(((first, record?), direct))
    }

    /// The argument a call places at the parameter `i` of `f`: the receiver at `0`, the
    /// positional arguments in order after it, a named one at the parameter of its name, as
    /// `fit` places them. Called through a value (`direct` false), a call's arguments are
    /// positional only. None where the call gives none there, as a default.
    fn placed(
        &self,
        f: Callee,
        direct: bool,
        receiver: Option<&'a Expr>,
        positional: &'a [Expr],
        named: &'a [(String, Expr)],
        i: usize,
    ) -> Option<&'a Expr> {
        if !direct {
            return match (receiver, named) {
                (None, []) => positional.get(i),
                _ => None,
            };
        }
        let Callee::Fn(id) = f else {
            return None;
        };
        let params = &self.t.funcs.get(&id)?.params;
        let skip = usize::from(receiver.is_some());
        match receiver {
            Some(r) if i == 0 => return Some(r),
            _ => {}
        }
        if let Some(p) = i.checked_sub(skip).and_then(|j| positional.get(j)) {
            return Some(p);
        }
        let name = &params.get(i)?.name;
        named.iter().find(|(n, _)| n == name).map(|(_, v)| v)
    }

    /// Records which parameter's keys the result of the declared function `fid` keeps, its
    /// body checked, then meets the keyspace needs of the calls of it met before
    /// ([`Self::ks_call`]). DESIGN.md sec:joins: "For recursion, assume the record, then
    /// check it."
    ///
    /// Proof that the record `i` holds: the second reading takes each recursive call to keep
    /// the keys of its argument at `i`, and finds the body's keyspace that of the parameter
    /// `i`. By induction on the depth of the recursion in a run that ends, a call at depth
    /// `d + 1` keeps them (the hypothesis), so the call at depth `d` does; a call with no
    /// recursive call inside it is the base case, read with no assumption used. The first
    /// reading, with recursive calls agreeing with anything ([`Space::Any`]), only proposes
    /// `i`, since the body is one parameter's keyspace at most at one `i`.
    pub(super) fn record_fn(&mut self, fid: usize, body: &'a Expr, ids: &[usize]) {
        let (s, _) = self.keyspace(body, Some((fid, None)));
        let at = |s: &Space| match s {
            Space::Binder(b) => ids.iter().position(|i| i == b),
            _ => None,
        };
        let record = at(&s).filter(|&i| {
            let (s, _) = self.keyspace(body, Some((fid, Some(i))));
            s == Space::Binder(ids[i])
        });
        self.keyspaces.fns.insert(fid, record);
        // A call queued inside the body itself may give the function a need of its own
        // parameters ([`Self::same_keys`]), which the calls read before it must meet too: so
        // the queue is read until the needs stop growing, without errors, then once more with
        // them. Each round but the last adds a need, of which there are at most p² for p
        // parameters.
        let calls = self.keyspaces.queued.remove(&fid).unwrap_or_default();
        loop {
            let before = self.keyspaces.needs.get(&fid).map_or(0, Vec::len);
            for &c in &calls {
                self.ks_meet(c, false);
            }
            if self.keyspaces.needs.get(&fid).map_or(0, Vec::len) == before {
                break;
            }
        }
        self.keyspaces.finished.insert(fid);
        for c in calls {
            self.ks_meet(c, true);
        }
    }

    /// Records which parameter's keys the result of the lambda with body `body` and
    /// parameters `ids` keeps ([`Self::record_fn`], with no recursion: a lambda has no name
    /// to call itself by).
    pub(super) fn record_lambda(&mut self, body: &'a Expr, ids: &[Option<usize>]) {
        let record = match self.keyspace(body, None).0 {
            Space::Binder(b) => ids.iter().position(|i| *i == Some(b)),
            _ => None,
        };
        self.keyspaces.lambdas.insert(body.span, record);
    }

    /// Notes that the parameter `entry` of the lambda `f` of `arity` parameters, mapped over
    /// `of` with `map`, `where` or `flatMap` (`arity` 1, `entry` 0) or folded over it with
    /// `foldl` (2, 1) or `foldr` (2, 0), takes `of`'s entries, for [`Self::within_count`] and
    /// for the ints a range's entries hold (`Ck::entry_range`, plan row
    /// RANGE-element-interval). Called before the lambda is checked, so each read of the
    /// parameter in its body sees it.
    pub(super) fn range_param(&mut self, of: &'a Expr, f: &'a Expr, arity: usize, entry: usize) {
        if let ExprKind::Lambda { params, .. } = &f.kind
            && params.len() == arity
            && let Some(p) = params.get(entry)
        {
            let id = self.id(p.span, &p.name);
            self.keyspaces.ranges.insert(id, of);
        }
    }

    /// The call at `span` of the declared function `fid`, by the name at `callee`, with its
    /// receiver and arguments: the arguments at each pair of parameters its body zips must
    /// share their keys ([`Keyspaces::needs`]). Checked now if the body has been, else once it
    /// is ([`Self::record_fn`]); a call read twice, as in a body checked again, once.
    pub(super) fn ks_call(
        &mut self,
        fid: usize,
        receiver: Option<&'a Expr>,
        positional: &'a [Expr],
        named: &'a [(String, Expr)],
        callee: Span,
        span: Span,
    ) {
        if !self.keyspaces.checked.insert(callee) {
            return;
        }
        let call = (fid, receiver, positional, named, span);
        match self.keyspaces.finished.contains(&fid) {
            true => self.ks_meet(call, true),
            false => self.keyspaces.queued.entry(fid).or_default().push(call),
        }
    }

    /// Meets the needs of the function of `call` there; with `report`, rejects a need not met.
    fn ks_meet(&mut self, call: KsCall<'a>, report: bool) {
        let (fid, receiver, positional, named, span) = call;
        let needs = self.keyspaces.needs.get(&fid).cloned().unwrap_or_default();
        for (i, j, zip) in needs {
            let f = Callee::Fn(fid);
            let a = self.placed(f, true, receiver, positional, named, i);
            let b = self.placed(f, true, receiver, positional, named, j);
            let met = match (a, b) {
                (Some(a), Some(b)) => {
                    let sa = self.keyspace(a, None).0;
                    let sb = self.keyspace(b, None).0;
                    // A need this call passes on to the caller's own parameters points at
                    // this call, which is where the caller's body zips them.
                    self.same_keys(&sa, &sb, span)
                }
                // A default is read at each call, in the function's frame: nothing shows its
                // keys those of another argument.
                _ => false,
            };
            if met || !report {
                continue;
            }
            self.ks_refuse(fid, i, j, zip, span, [a, b]);
        }
    }

    /// The error at the call at `span` of `fid`, whose body zips its parameters `i` and `j`
    /// at `zip`, whose arguments there, `args`, are not shown to share their keys.
    fn ks_refuse(
        &mut self,
        fid: usize,
        i: usize,
        j: usize,
        zip: Span,
        span: Span,
        args: [Option<&'a Expr>; 2],
    ) {
        let f = self.t.funcs[&fid];
        let [p, q] = [i, j].map(|k| f.params[k].name.clone());
        let texts = args.map(|e| e.and_then(|e| self.operand_text(Some(e.span))));
        let [a, b] = texts.clone().map(|t| match t {
            Some(c) => format!("`{c}`"),
            None => "the default".to_string(),
        });
        let x = texts[0]
            .as_deref()
            .map_or("xs".to_string(), postfix_operand);
        let message = format!(
            "`{}` zips its parameters `{p}` and `{q}`, so their arguments must have the same \
             keys, and nothing shows that {a} and {b} do",
            f.name
        );
        let mut notes = self.derive(&[span]);
        notes.push(Note {
            span: zip,
            text: format!("`{p}` and `{q}` are zipped here").into(),
        });
        let repair = format!(
            "repair: pass values with the same keys, as `{x}` and `{x}.map(f)`, or pair the \
             ranks both lists hold inside `{}`",
            f.name
        );
        notes.push(Note {
            span,
            text: repair.into(),
        });
        self.error_with(span, message, notes);
    }

    /// Whether the keyspaces `a` and `b` are one ([`Self::keyspace`]), or two parameters of a
    /// declared function whose body is still being checked, which then needs their arguments
    /// to share their keys at each call ([`Keyspaces::needs`], DESIGN.md sec:joins: "A zip of
    /// two parameters becomes a need checked at each call"); `zip` is the `zip` the need
    /// comes from.
    fn same_keys(&mut self, a: &Space, b: &Space, zip: Span) -> bool {
        if a == b && *a != Space::Any {
            return true;
        }
        let (Space::Binder(p), Space::Binder(q)) = (a, b) else {
            return false;
        };
        let ks = &mut self.keyspaces;
        let (Some(&(f, i)), Some(&(g, j))) = (ks.params.get(p), ks.params.get(q)) else {
            return false;
        };
        if f != g {
            return false;
        }
        let needs = ks.needs.entry(f).or_default();
        let has = needs
            .iter()
            .any(|&(x, y, _)| (x, y) == (i, j) || (x, y) == (j, i));
        match (has, ks.finished.contains(&f)) {
            (true, _) => true,
            (false, false) => {
                needs.push((i, j, zip));
                true
            }
            (false, true) => false,
        }
    }

    /// Whether the operands of the `zip` at `span` share their keys by where they come from
    /// ([`Self::keyspace`], [`Self::same_keys`]).
    fn zip_shares_keys(&mut self, x: &Arg<'a>, y: &Arg<'a>, span: Span) -> bool {
        let (Some(ex), Some(ey)) = (x.expr, y.expr) else {
            return false;
        };
        let a = self.keyspace(ex, None).0;
        let b = self.keyspace(ey, None).0;
        self.same_keys(&a, &b, span)
    }

    /// Whether the operands of a `zip` hold the same keys because they come from one place
    /// ([`Self::keyspace`]), as the two `l` of `pairUp(l, l)`. Unlike
    /// [`Self::zip_shares_keys`] it records no need on a function's parameters: two
    /// parameters are not one place, and their calls are checked through the need on their
    /// classes instead. Complexity tradeoff: two keyspace reads, as at `zip_shares_keys`.
    fn zip_one_origin(&mut self, x: &Arg<'a>, y: &Arg<'a>) -> bool {
        let (Some(ex), Some(ey)) = (x.expr, y.expr) else {
            return false;
        };
        let a = self.keyspace(ex, None).0;
        a != Space::Any && a == self.keyspace(ey, None).0
    }

    /// Whether the read `of[key]` finds its key in `of` because `key` is the parameter of a
    /// lambda mapped over `0 ..< e` (or filtered with `where`, or the entry parameter of one
    /// folded over it with `foldl` or `foldr`), with `e` the count `L.count`
    /// of a list `L`, or `min(…)` of operands one of which is `L.count`, and `of` has the keys
    /// of `L` (DESIGN.md sec:joins: "a read `x[i]` has no `#outOfBounds`").
    ///
    /// Proof: the lambda runs once for each entry of the range, with the entry's value, which
    /// for a range is its key, so `0 ≤ key < e`; `min` is at most each operand, so
    /// `e ≤ L.count`; `L`'s keys are the ranks `0 ..< L.count` ([`Dense::Ranks`]), so `key` is
    /// a key of `L`, read in the frame of the range (the lambda's body reads only binders of
    /// the scopes around it there, or its own); `of` has the same keys in that frame, by
    /// [`Self::keyspace`], so the read finds `key`.
    pub(super) fn within_count(&mut self, of: &'a Expr, key: Option<&'a Expr>) -> bool {
        let Some(key) = key else {
            return false;
        };
        let ExprKind::Name(_) = key.kind else {
            return false;
        };
        let Some(range) = (self.one_binder(key.span)).and_then(|id| self.keyspaces.ranges.get(&id))
        else {
            return false;
        };
        let ExprKind::Range(lo, RangeEnd::Below(hi)) = &range.kind else {
            return false;
        };
        if self.known(lo).value != Some(Value::from(0)) {
            return false;
        }
        let ends: Vec<&'a Expr> = match &hi.kind {
            ExprKind::Call {
                callee,
                positional,
                named,
                curry: false,
                ..
            } if named.is_empty()
                && matches!(&callee.kind, ExprKind::Name(n) if n == "min")
                && matches!(self.t.res.uses.get(&callee.span), Some(Ref::Prelude(_))) =>
            {
                positional.iter().collect()
            }
            _ => vec![&**hi],
        };
        let lists: Vec<&'a Expr> = ends
            .into_iter()
            .filter_map(|e| self.count_of_list(e))
            .collect();
        if lists.is_empty() {
            return false;
        }
        let at = self.keyspace(of, None).0;
        lists.into_iter().any(|l| self.keyspace(l, None).0 == at)
    }

    /// Rejects each use of a declared function whose body zips two of its parameters
    /// ([`Keyspaces::needs`]) as anything but a call by its name: passed as a value, it would
    /// be called where no need is checked (plan row ZIP-count-facts).
    pub(super) fn ks_escapes(&mut self) {
        if self.keyspaces.needs.values().all(Vec::is_empty) {
            return;
        }
        let mut found = Vec::new();
        for (span, r) in &self.t.res.uses {
            let Ref::Bound(ids) = r else {
                continue;
            };
            let needy = ids
                .iter()
                .find(|id| self.keyspaces.needs.get(id).is_some_and(|n| !n.is_empty()));
            if let Some(&id) = needy
                && !self.keyspaces.checked.contains(span)
            {
                found.push((*span, id));
            }
        }
        for (span, id) in found {
            let f = self.t.funcs[&id];
            let (i, j, _) = self.keyspaces.needs[&id][0];
            let what = format!(
                "passing `{}`, whose body zips its parameters `{}` and `{}`, as a value",
                f.name, f.params[i].name, f.params[j].name
            );
            self.error(span, zedc_base::rejection::not_yet(&what));
        }
    }
}

/// What a callee's record says of its result's keys ([`Ck::callee_record`]).
#[derive(Clone, Copy, PartialEq)]
enum Recorded {
    /// It keeps the keys of the parameter.
    Kept(usize),
    /// A recursive call, under the assumption ([`Assume`]).
    Assumed(Option<usize>),
}

#[cfg(test)]
mod tests {
    use super::postfix_operand;

    /// `postfix_operand` puts an operand in parentheses only where a postfix cannot follow it
    /// as written (row PRINT-repair-parens-minimal: `"ab"` and `#a` take none, a number
    /// literal does); a bracket in a string or a comment is not counted (row DRY-text-shared;
    /// the cases with one were wrong on the count on characters, `f("(") + 1` the way that
    /// changed what the repair means).
    #[test]
    fn an_operand_takes_parentheses_only_where_a_postfix_cannot_follow_it() {
        for (c, want) in [
            ("xs", "xs"),
            ("m.lines", "m.lines"),
            ("xs.where(f)", "xs.where(f)"),
            ("[1, 2]", "[1, 2]"),
            ("(0 ..< 3)", "(0 ..< 3)"),
            ("x'", "x'"),
            ("f(\")\")", "f(\")\")"),
            ("f(/* ) */ x)", "f(/* ) */ x)"),
            ("", ""),
            ("a + b", "(a + b)"),
            ("f(\"(\") + 1", "(f(\"(\") + 1)"),
            ("xs // c", "(xs // c)"),
            ("xs /* c */", "xs /* c */"),
            ("\"ab\"", "\"ab\""),
            ("#a", "#a"),
            ("2", "(2)"),
            ("-x", "(-x)"),
            ("x)", "(x))"),
            // Fragments that do not lex.
            ("f(\"a)", "(f(\"a))"),
        ] {
            assert_eq!(postfix_operand(c), want, "{c}");
        }
    }
}
