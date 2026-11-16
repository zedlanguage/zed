//! The standard operations on one level of a family that plan row FP-ops-run (author P229)
//! builds into zedc as `map` is (plan row MAP-pure-zed): `.count`, `.sum` and `.reduce(op)`,
//! the quantifiers `.any`, `.all` and `.find` (step L3.15a), and `.first` and `.last`
//! (DESIGN.md sec:corner_cases, "`first`/`last` are lexicographic"); by plan row
//! FP-ops-scan, `.scan(op)` and `.chunkBy(f)` (step L5.3); the string functions `split`,
//! `lines` and `concat` of plan row FP-ops-strings (step L3.2); and, by plan row
//! FP-ops-concat-zip, `a ++ b` on lists and `a.zip(b)` (step L5.2).

use super::remap::Apply;
use crate::check::*;

/// `Ck::fold_level`, the check of the fold of one level, passed in by walk.rs as `Apply` is.
pub(in crate::check) type FoldLevel<'t, 'a> =
    fn(&mut Ck<'t, 'a>, Reducer, &Ty, Span, Span, FoldForm) -> Ty;

/// The source text `c` of an operand, put in parentheses unless `.count` or `[i]` can follow
/// it as written: every character outside brackets is part of a name or a `.`, as in `xs`,
/// `m.lines`, `xs.where(f)`, `[1, 2]` or `(0 ..< 3)`.
fn postfix_operand(c: &str) -> String {
    let mut depth = 0i32;
    let mut plain = true;
    for ch in c.chars() {
        match ch {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            _ if depth == 0 => plain &= ch.is_alphanumeric() || matches!(ch, '_' | '\'' | '.'),
            _ => {}
        }
    }
    match plain {
        true => c.to_string(),
        false => format!("({c})"),
    }
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
    /// first, each as a need ([`NeedKind::Level`]) or as the type it is resolved to; the
    /// `Piece::Var` arm stays for a caller that did not. `None` after an error.
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
        let Some(sigs) = self.levels_of(x, form.word(), &example, span) else {
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
        let misses = &KType::atom("notFound") | &KType::atom("outOfBounds");
        let mut families = Ty::empty();
        for sig in sigs {
            let mut s = (*sig).clone();
            for a in &mut s.arrows {
                a.result = entry.union(&Ty::set(&a.result.atoms() & &misses));
            }
            s.word = None;
            s.needs = Vec::new();
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
        let sigs = self.levels_of(x, word, "[1, 1, 2].chunkBy(x -> x)", span)?;
        let entries = Self::entries_of(&sigs);
        let gives = match entries.lists_nothing() {
            true => Ty::empty(),
            false => {
                let what = Label::Text("the function given to `chunkBy`");
                apply(self, what, &fsig, vec![Some(Arg::of(entries))], false, span).0
            }
        };
        let not_found = Ty::set(KType::atom("notFound"));
        let mut runs = Ty::empty();
        for sig in sigs {
            let mut s = (*sig).clone();
            for a in &mut s.arrows {
                a.result = a.result.union(&not_found);
            }
            // A run holds some of the keys, which `Sig::keys` would not describe.
            s.dense = Dense::No;
            s.keys = None;
            s.word = None;
            s.needs = Vec::new();
            s.note_held();
            runs = runs.union(&Ty::func(Arc::new(s)));
        }
        // The runs are ranked from 0, every rank present, so the keys are the ranks `0 ..< n`,
        // as a range's from `0` are (`Ck::range_end`).
        let int = Ty::carrier(Carrier::Int);
        let mut outer = Sig::one(
            super::super::positional(1),
            vec![int],
            runs.union(&not_found),
        );
        outer.arrows[0].partial = true;
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
    pub(super) fn strings_end(&mut self, word: &str, args: Vec<Arg<'a>>, span: Span) -> Ty {
        let quoted = format!("`{word}`");
        let mut out = Ty::empty();
        let (pieces, strings) = match word {
            "concat" => (args.first(), &args[1..]),
            _ => (None, &args[..]),
        };
        for a in strings {
            out = out.union(&self.passing(&a.ty, &quoted, span, a.at));
            if !self.string_operand(word, a, span) {
                return Ty::empty();
            }
        }
        if let ("split", [s, sep]) = (word, &args[..]) {
            // An empty separator has no answer, so it is the failure `#emptySeparator`, given
            // exactly where the separator's type holds `""`: a type that holds no `""`, as
            // `","` or a name bound to it, adds no atom, and one whose only value is `""` is
            // rejected. Each test reads the separator's type once, O(its size).
            let value = sep.ty.without_loose();
            let empty = Value::str("");
            if !value.lists_nothing() && self.subtype(&value, &Ty::lit(&empty)) {
                self.empty_separator(s, sep, span);
                return Ty::empty();
            }
            if value.contains(&empty) {
                out = out.union(&Ty::set(KType::atom("emptySeparator")));
            }
        }
        let Some(p) = pieces else {
            return out.union(&strings_rank());
        };
        out = out.union(&self.passing(&p.ty, &quoted, span, p.at));
        let example = "concat([\"a\", \"b\"], sep: \", \")";
        let Some(sigs) = self.levels_of(&p.ty, &quoted, example, span) else {
            return Ty::empty();
        };
        let at = p.at.unwrap_or(span);
        let code = self.code(p.at).map(str::trim).unwrap_or("xs");
        let entries = Self::entries_of(&sigs);
        if !entries.loose_ty().lists_nothing() {
            let what = "`concat` of a family whose entries may be failure atoms";
            self.error(at, zedc_base::rejection::not_yet(what));
            return Ty::empty();
        }
        for e in entries.pieces() {
            match e {
                Piece::Fn(sig) if sig.data => {
                    let t = self.text(&p.ty);
                    self.error_offering(
                        at,
                        format!(
                            "`concat` joins a family of strings, and this value is {t}, a \
                             family of families"
                        ),
                        [format!(
                            "repair: join the inner families first, as `{code} >< (++)`"
                        )],
                    );
                    return Ty::empty();
                }
                Piece::Dyn => self.any(&quoted, span),
                Piece::Var(_) => {
                    let what = match self.code(p.at).map(str::trim).filter(|c| !c.contains('\n')) {
                        Some(c) => {
                            format!("`concat` of `{c}`, whose entries are of a generic type,")
                        }
                        None => "`concat` of a family whose entries are of a generic type".into(),
                    };
                    self.error(at, zedc_base::rejection::not_yet(&what));
                    return Ty::empty();
                }
                e if self.subtype(&e.ty(), &Ty::carrier(Carrier::Str)) => {}
                e => {
                    let t = self.text(&e.ty());
                    self.error_offering(
                        at,
                        format!("`concat` joins strings, and an entry of this family is {t}"),
                        [format!(
                            "repair: make each entry a string, as \
                             `concat({code}.map(x -> String(x)))`"
                        )],
                    );
                    return Ty::empty();
                }
            }
        }
        out.union(&Ty::carrier(Carrier::Str))
    }

    /// Whether `a`, a string operand of the built-in `word` (`split`, `lines`, or the `sep`
    /// of `concat`), may be only strings or loose atoms; any other value is rejected.
    fn string_operand(&mut self, word: &str, a: &Arg<'a>, span: Span) -> bool {
        let at = a.at.unwrap_or(span);
        for p in a.ty.without_loose().pieces() {
            match p {
                Piece::Dyn => self.any(&format!("`{word}`"), span),
                // The program may write no type parameter, as `l` of `m.stdin.map(l -> …)`, so
                // the operand is named by its code and its type called generic, the word for a
                // type decided where the function is applied (plan row
                // FAIL-l01-37a-split-snapshot).
                Piece::Var(_) => {
                    let what = match self.code(a.at).map(str::trim).filter(|c| !c.contains('\n')) {
                        Some(c) => format!("`{word}` on `{c}`, whose type is generic here,"),
                        None => format!("`{word}` on a value whose type is generic here"),
                    };
                    self.error(at, zedc_base::rejection::not_yet(&what));
                    return false;
                }
                p if self.subtype(&p.ty(), &Ty::carrier(Carrier::Str)) => {}
                p => {
                    let t = self.text(&p.ty());
                    let example = match word {
                        "split" => "`\"a,b\".split(\",\")`",
                        "lines" => "`\"a\\nb\".lines`",
                        _ => "`concat(xs, sep: \", \")`",
                    };
                    self.error_offering(
                        at,
                        format!("`{word}` reads strings, and this value is {t}"),
                        [format!("repair: pass a string, as {example}")],
                    );
                    return false;
                }
            }
        }
        true
    }

    /// Rejects the `split` at `span` of the string `s` by `sep`, a separator that is always the
    /// empty string: every value that reaches it fails with `#emptySeparator`, and an operation
    /// that always fails is an error (DESIGN sec:failure; L3.2, author decision P314). The
    /// repairs name the views that read the characters of `s`, then a separator that is not
    /// empty, then the failure or `#bug` written in place of the call, as the other rejections
    /// of an operation that always fails offer them.
    fn empty_separator(&mut self, s: &Arg<'a>, sep: &Arg<'a>, span: Span) {
        let at = sep.at.unwrap_or(span);
        let call = match self.operand_text(Some(span)) {
            Some(c) => format!("`{c}`"),
            None => "`split` here".to_string(),
        };
        let reason = match (sep.expr.map(|e| &e.kind), self.operand_text(sep.at)) {
            (Some(ExprKind::Str(_)), _) | (_, None) => "its separator is the empty string".into(),
            (_, Some(c)) => format!("its separator `{c}` is always the empty string"),
        };
        let subject = self.operand_text(s.at).unwrap_or_else(|| "s".to_string());
        // The call in the program's style: `split(s, sep)` as a function, `s.split(sep)` as a
        // method.
        let split = match call.starts_with("`split(") {
            true => format!("`split({subject}, sep)`"),
            false => format!("`{}.split(sep)`", postfix_subject(s.expr, &subject)),
        };
        let mut notes = vec![Note {
            span: at,
            text: "this separator is always the empty string".to_string(),
        }];
        notes.extend(self.derive(&[at]));
        let menu = view_forms(s.expr, &subject)
            .into_iter()
            .map(|form| format!("repair: write {form}"))
            .chain([
                format!("repair: write {split}, with a separator `sep` that is not empty"),
                "repair: write `#emptySeparator` in place of this call, where the failure is \
                 meant"
                    .to_string(),
                "repair: write `#bug(\"…\")` in place of this call, where it is never meant to \
                 be reached"
                    .to_string(),
            ]);
        notes.extend(menu.map(|text| Note { span, text }));
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

    /// The text of the operand at `at`, where it is on one line, for a message.
    fn operand_text(&self, at: Option<Span>) -> Option<String> {
        let c = self.code(at)?.trim();
        (!c.is_empty() && !c.contains('\n')).then(|| c.to_string())
    }

    /// The bounds of the keys of the families `sigs` (DESIGN.md sec:type_language, the bound
    /// table): `L`, the keys each of them surely holds, and `U`, the keys any of them may
    /// hold. A key is sure where its arrow is not partial and gives no miss, as for a list
    /// display; a range, a `Lines` input or a `where` result guarantees no key. `sigs` is not
    /// empty.
    // Complexity tradeoff: one union per arrow and one meet per family, linear in the arrows;
    // the pairwise test of each family of one operand against each of the other's, which
    // `zip_end` would need without these two bounds, is quadratic in the families.
    fn key_bounds(sigs: &[Arc<Sig>]) -> (Ty, Ty) {
        let misses = &KType::atom("notFound") | &KType::atom("outOfBounds");
        let sure = |s: &Sig| {
            Ty::union_all(
                (s.arrows.iter())
                    .filter(|a| !a.partial && (&a.result.atoms() & &misses) == KType::empty())
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
    /// where the arrow is total and gives no miss. A key type of infinitely many ints, as
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
    pub(super) fn list_concat_end(&mut self, x: &Arg<'a>, y: &Arg<'a>, span: Span) -> Ty {
        let word = "`++`";
        let out =
            (self.passing(&x.ty, word, span, x.at)).union(&self.passing(&y.ty, word, span, y.at));
        let mut sides: Vec<Vec<Arc<Sig>>> = Vec::new();
        for a in [x, y] {
            let at = a.at.unwrap_or(span);
            let mut sigs = Vec::new();
            for p in a.ty.pieces() {
                match p {
                    // `{}` holds no key, the ranks `0 ..< 0`, as does an empty range such as
                    // `3 ..< 3`, whose exact keys are none ([`Sig::keys`]).
                    Piece::Fn(sig)
                        if sig.data
                            && (sig.dense == Dense::Ranks
                                || sig.arrows.iter().all(|a| a.params[0].is_empty())
                                || (sig.keys.as_ref())
                                    .is_some_and(|k| written_ints(k).is_empty())) =>
                    {
                        sigs.push(sig)
                    }
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
                    Piece::Var(_) => {
                        let what = "`++` on a value whose type is a type parameter";
                        self.error(span, zedc_base::rejection::not_yet(what));
                        return Ty::empty();
                    }
                    p if p.is_atoms() => {}
                    p => {
                        let t = self.text(&p.ty());
                        self.error_offering(
                            at,
                            format!(
                                "`++` joins two lists or two strings, and this value is {t}, \
                                 beside a list"
                            ),
                            ["repair: put the value in a list, as `[x] ++ xs`".to_string()],
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
                let found = values.union(&Ty::set(KType::atom("notFound")));
                let mut sig = Sig::one(positional(1), vec![Ty::carrier(Carrier::Int)], found);
                sig.arrows[0].partial = true;
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
                _ => {
                    let found = values.union(&Ty::set(KType::atom("notFound")));
                    let mut sig = Sig::one(positional(1), vec![Ty::carrier(Carrier::Int)], found);
                    sig.arrows[0].partial = true;
                    sig
                }
            },
        };
        let mut sig = sig;
        sig.data = true;
        sig.dense = Dense::Ranks;
        sig.note_held();
        if !self.trying {
            self.info.list_concats.insert(span);
        }
        out.union(&Ty::func(Arc::new(sig)))
    }

    /// `a.zip(b)` (step L5.2; DESIGN.md sec:joins): the equality join on keys,
    /// `joinR(#assertEmpty, #keep, #assertEmpty)`, the family of the pairs `(a[k], b[k])`. Its
    /// two asserted-empty regions, the keys `a` may hold that `b` may lack and the reverse,
    /// must be proved empty: `U_a ⊆ L_b` and `U_b ⊆ L_a` (DESIGN.md sec:type_language, "One
    /// rule for every join"). An assertion not proved is a static error, which names one key
    /// the bounds admit into the region (sec:diagnostics, "Undischarged region assertion"):
    /// `[1, 2].zip([1])` holds key `1` on one side only, and a zip of two `Lines` inputs is
    /// rejected too, since nothing shows their counts equal. Proved, the four bounds are one
    /// set, so the result's keys are sure. A loose atom of either operand passes through.
    // Complexity tradeoff: the bounds over all the families each operand may be, two
    // subtype tests and one diff for the message, linear in the arrows (`key_bounds`).
    pub(super) fn zip_end(&mut self, x: &Arg<'a>, y: &Arg<'a>, span: Span) -> Ty {
        let word = "`zip`";
        let example = "[1, 2].zip([3, 4])";
        let out =
            (self.passing(&x.ty, word, span, x.at)).union(&self.passing(&y.ty, word, span, y.at));
        let Some(a) = self.levels_of(&x.ty, word, example, x.at.unwrap_or(span)) else {
            return Ty::empty();
        };
        let Some(b) = self.levels_of(&y.ty, word, example, y.at.unwrap_or(span)) else {
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
        // Shown above, `U_a ⊆ L_b ⊆ U_b ⊆ L_a ⊆ U_a`, so the four are one set, every key of
        // it in every family of both sides. An operand none of whose families has exact keys
        // writes that set as its key type `U`, a sure key type, as for two lists. Where both
        // have exact keys, the set is one interval (the `L` of a side with exact keys lies in
        // them, and equals `U`, which holds them), kept as two ends on the arrow `int ->?`.
        let plain = |side: &[Arc<Sig>]| side.iter().all(|s| s.keys.is_none());
        let mut sig = match (&sets, plain(&a), plain(&b)) {
            (Some(((_, u), _)), false, false) => {
                let found = pair.union(&Ty::set(KType::atom("notFound")));
                let mut sig = Sig::one(positional(1), vec![Ty::carrier(Carrier::Int)], found);
                sig.arrows[0].partial = true;
                sig.keys = exact_keys(u);
                sig
            }
            (_, _, true) => Sig::one(positional(1), vec![ub], pair),
            _ => Sig::one(positional(1), vec![ua], pair),
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
}
