//! Whether a stopping read of a range with no upper end ends (DESIGN.md sec:grammar, rule
//! Range; sec:diagnostics, row "Not proved to end"; plan row RANGE-open-ending-warn).
//!
//! `.first`, `.any(p)`, `.find(p)` and `.all(p)` after any number of `.map(f)` and `.where(q)`
//! links read the entries of `a ..` in key order up to the one that decides the read: one
//! the `where` links keep at which `p` holds (`.any`, `.find`), fails (`.all`), or any kept
//! entry (`.first`). The read is proved to end where the checker shows such an entry for
//! every value of the names the test reads, and is otherwise warned at.
//!
//! The proof. The entry of key `a + j` is read with `j` over `[0, ∞)`. Each `.map(x -> e)`
//! binds a name to `e` read with `x` the entry so far, each `.where(x -> e)` adds `e` as a
//! conjunct, and the deciding test, negated for `.all`, is the last conjunct: one kernel
//! term, of size linear in the text, since each entry is a name bound once (`Term::Let`).
//! `a` and the bodies are read only where they are made of integer literals, names
//! [`Ck::known`] gives an integer or boolean value, the entry, names of one binder whose type
//! holds only integers (each an input over the integers [`Ck::known`] gives it), the integer
//! operators a test is read by ([`arms::prim_of`]), `-`, `!` and `if`. Every input is then an
//! integer. Any other name, a call, a member read, a block or a lambda stops the proof. The
//! walk's own translation ([`Ck::term_for`]) is not used: it reads a name through the scopes
//! of the place the walk is at, and a read is judged once the walk is done.
//!
//! The preimage of `true` under the term (`zedc_preimage::preimage::preimage`) is a box, a
//! set for each input, that holds every point at which the term is `true`, marked exact when
//! every point of it is one. (a) Exact, with the set of each input other than `j` its whole
//! domain: for every value of those inputs, each `j` of the box's set, which is not empty
//! by (b), gives a point of the box, at which the read is decided, so the read ends. (b) Some
//! set of the box empty: no point makes the term `true`, so no entry decides the read, at any
//! value of the inputs, and the read never ends. (c) Otherwise the read is undetermined. The
//! fragment holds no loop and no call, and `div` and `mod` by zero fault, which ends the run,
//! so the entries before the deciding one each end.
//!
//! Complexity: one preimage of a term of size linear in the read's text, at each read once
//! (by its span); a generic body checked once per call records the read once.
//!
//! Incomplete where the box is not exact though an entry exists: `(n ..).find(x -> x >= n)`
//! decides at `n` for every `n`, but where the box of a test between two inputs is not
//! exact, the read is warned at; and a read through a call, as `(n ..).where(isPrime).first`,
//! is warned at, as the rule says (no entry is shown). The `relation` the preimage keeps for
//! a linear test that its box does not decide could prove more; it is not read yet.
//!
//! Tests: `l03_02_map_run::types::stopping_reads_of_an_open_range_are_proved_to_end_or_warned`.

use std::sync::Arc;

use zed_kernel::types::Type as KType;
use zed_kernel::{Prim, Shared, Term, Value};
use zedc_base::rejection::Row;
use zedc_int::int::Num;
use zedc_lattice::interval::{End, IntervalSet};
use zedc_preimage::preimage::{Demand, Domains, preimage};
use zedc_resolve::resolve::{Ref, open_stream};
use zedc_syntax::ast::{Error, Expr, ExprKind, Note, UnaryOp};
use zedc_syntax::lex::Span;

use super::{Ck, arms};

/// The word of a stopping read.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum OpenWord {
    First,
    Any,
    Find,
    All,
}

impl OpenWord {
    /// The word of the prelude member `name`, if it is a stopping read.
    pub(super) fn of(name: &str) -> Option<OpenWord> {
        Some(match name {
            "first" => OpenWord::First,
            "any" => OpenWord::Any,
            "find" => OpenWord::Find,
            "all" => OpenWord::All,
            _ => return None,
        })
    }
}

/// A stopping read of a range with no upper end: `of.word(test)`.
pub(super) struct OpenRead<'a> {
    pub(super) of: &'a Expr,
    pub(super) test: Option<&'a Expr>,
    pub(super) word: OpenWord,
}

/// The name of `j`, the key less the low end; no binder's name holds a space ([`arms::var`]).
const KEY: &str = "the key";

/// What the proof found.
enum Verdict<'a> {
    /// Some entry decides the read, case (a).
    Ends,
    /// No entry decides it, case (b).
    Never,
    /// The box decides nothing, case (c).
    Undecided,
    /// The text stops the proof at this part.
    Stopped(&'a Expr),
}

impl<'t, 'a> Ck<'t, 'a> {
    /// Records the read `of.name(positional)` at `span` when `of` is a stream over a range
    /// with no upper end and `name` the prelude's stopping read, once for its span.
    pub(super) fn note_open_read(
        &mut self,
        of: &'a Expr,
        name: &str,
        positional: &'a [Expr],
        span: Span,
    ) {
        let Some(word) = OpenWord::of(name) else {
            return;
        };
        if open_stream(of).is_none() {
            return;
        }
        let test = match (word, positional) {
            (OpenWord::First, []) => None,
            (OpenWord::First, _) => return,
            (_, [p]) => Some(p),
            _ => return,
        };
        self.open_reads
            .entry(span)
            .or_insert(OpenRead { of, test, word });
    }

    /// The warnings "Not proved to end" of the reads [`Self::note_open_read`] recorded.
    pub(super) fn open_read_warnings(&mut self) -> Vec<Error> {
        let reads = std::mem::take(&mut self.open_reads);
        let mut out = Vec::new();
        for (span, r) in reads {
            let verdict = self.open_read_verdict(&r);
            if let Some(w) = self.open_read_warning(span, &r, verdict) {
                out.push(w);
            }
        }
        out
    }

    /// Cases (a), (b) and (c) of the module's proof for `r`.
    fn open_read_verdict(&mut self, r: &OpenRead<'a>) -> Verdict<'a> {
        let Some((lo, links)) = open_stream(r.of) else {
            return Verdict::Undecided;
        };
        let key: Arc<str> = KEY.into();
        let mut inputs = Domains::new();
        inputs.insert(
            key.clone(),
            IntervalSet::range(End::Fin(Num::from(0i64)), End::PosInf),
        );
        let lo = match self.open_term(lo, None, &mut inputs) {
            Ok(t) => t,
            Err(e) => return Verdict::Stopped(e),
        };
        // The entries bound in order, and the tests on them.
        let mut lets: Vec<(Arc<str>, Term)> = vec![(
            "entry 0".into(),
            Term::Prim(Prim::Add, vec![lo, Term::Var(key.clone())]),
        )];
        let mut conds = Vec::new();
        for f in (links.iter().map(|l| (l.f, l.filter))).chain(r.test.map(|p| (p, true))) {
            let (f, filter) = f;
            let at = lets.last().expect("the entry is bound").0.clone();
            let t = match self.open_applied(f, &at, &mut inputs) {
                Ok(t) => t,
                Err(e) => return Verdict::Stopped(e),
            };
            if filter {
                conds.push(t);
            } else {
                lets.push((format!("entry {}", lets.len()).into(), t));
            }
        }
        if r.word == OpenWord::All
            && let Some(last) = conds.pop()
        {
            conds.push(Term::Prim(Prim::Not, vec![last]));
        }
        // `.first` with no `where` link: the first entry decides it.
        let Some(mut term) = (conds.into_iter()).reduce(|a, b| Term::Prim(Prim::And, vec![a, b]))
        else {
            return Verdict::Ends;
        };
        for (name, value) in lets.into_iter().rev() {
            term = Term::Let(name, Shared::new(value), Shared::new(term));
        }
        let p = preimage(&term, &inputs, &Demand::Bool(true));
        let set = |n: &Arc<str>| p.domains.0.get(n);
        if inputs.keys().any(|n| set(n).is_some_and(|s| s.is_empty())) {
            return Verdict::Never;
        }
        let whole = (inputs.iter())
            .filter(|(n, _)| **n != key)
            .all(|(n, d)| set(n).is_none_or(|s| s == d));
        match p.exact && whole {
            true => Verdict::Ends,
            false => Verdict::Undecided,
        }
    }

    /// The binder of `e`, a name, where it reads one and its type holds only integers.
    fn open_int_binder(&self, e: &Expr) -> Option<usize> {
        let Some(Ref::Bound(ids)) = self.t.res.uses.get(&e.span) else {
            return None;
        };
        // One binder, not the arrows of an overload set.
        let (1, Some(&id)) = (ids.len(), ids.front()) else {
            return None;
        };
        let ty = self.env.get(&id)?;
        let ints = ty.tuples.is_empty()
            && ty.fns.is_empty()
            && ty.vars.is_empty()
            && !ty.dynamic
            && ty.set.subtype(&KType::int());
        ints.then_some(id)
    }

    /// The term of `f`, a lambda of one parameter, applied to the entry named `at`: its body
    /// read with the parameter as `at`, or the part of `f` at which the proof stops.
    fn open_applied(
        &mut self,
        f: &'a Expr,
        at: &Arc<str>,
        inputs: &mut Domains,
    ) -> Result<Term, &'a Expr> {
        let ExprKind::Lambda { params, body } = &f.kind else {
            return Err(f);
        };
        let [param] = &params[..] else {
            return Err(f);
        };
        if param.tuple.is_some() || param.default.is_some() {
            return Err(f);
        }
        self.open_term(body, Some((&param.name, at)), inputs)
    }

    /// `e` as a kernel term over the fragment of the module's proof, the name `param.0` read
    /// as `param.1` and each other name of an integer binder as an input added to `inputs`; or
    /// the first part outside the fragment. The body holds no block or lambda, so a name
    /// `param.0` in it is the parameter. Iterative, so a deep body costs no stack.
    fn open_term(
        &mut self,
        e: &'a Expr,
        param: Option<(&str, &Arc<str>)>,
        inputs: &mut Domains,
    ) -> Result<Term, &'a Expr> {
        let mut done: Vec<Term> = Vec::new();
        let mut stack = vec![(e, false)];
        while let Some((x, ready)) = stack.pop() {
            if ready {
                let t = match &x.kind {
                    ExprKind::Binary(op, ..) => {
                        let b = done.pop().expect("a right operand");
                        let a = done.pop().expect("a left operand");
                        let p = arms::prim_of(*op).expect("checked before its operands");
                        Term::Prim(p, vec![a, b])
                    }
                    ExprKind::Unary(op, _) => {
                        let a = done.pop().expect("an operand");
                        let p = match op {
                            UnaryOp::Neg => Prim::Neg,
                            UnaryOp::Not => Prim::Not,
                        };
                        Term::Prim(p, vec![a])
                    }
                    ExprKind::If { .. } => {
                        let c = done.pop().expect("an `else` arm");
                        let b = done.pop().expect("a `then` arm");
                        let a = done.pop().expect("a condition");
                        Term::If(Shared::new(a), Shared::new(b), Shared::new(c))
                    }
                    _ => unreachable!("only operators wait for their operands"),
                };
                done.push(t);
                continue;
            }
            if let (ExprKind::Name(n), Some((p, at))) = (&x.kind, param)
                && n == p
            {
                done.push(Term::Var(at.clone()));
                continue;
            }
            match self.known(x).value {
                Some(v @ (Value::Int(_) | Value::Big(_) | Value::Bool(_))) => {
                    done.push(Term::Lit(v));
                    continue;
                }
                Some(_) => return Err(x),
                None => {}
            }
            match &x.kind {
                ExprKind::Name(n) => {
                    let Some(id) = self.open_int_binder(x) else {
                        return Err(x);
                    };
                    let name = arms::var(n, id);
                    let ints = self.known(x).ints;
                    inputs.entry(name.clone()).or_insert(ints);
                    done.push(Term::Var(name));
                }
                ExprKind::Binary(op, a, b) if arms::prim_of(*op).is_some() => {
                    stack.push((x, true));
                    stack.push((b, false));
                    stack.push((a, false));
                }
                ExprKind::Unary(_, a) => {
                    stack.push((x, true));
                    stack.push((a, false));
                }
                ExprKind::If {
                    cond,
                    then,
                    otherwise,
                } => {
                    stack.push((x, true));
                    stack.push((otherwise, false));
                    stack.push((then, false));
                    stack.push((cond, false));
                }
                _ => return Err(x),
            }
        }
        Ok(done.pop().expect("the term"))
    }

    /// The warning for `r` at `span` under `verdict`, or none where the read ends.
    fn open_read_warning(
        &self,
        span: Span,
        r: &OpenRead<'a>,
        verdict: Verdict<'a>,
    ) -> Option<Error> {
        let code = |e: &Expr| self.code(Some(e.span)).unwrap_or("the read");
        let read = self.code(Some(span)).unwrap_or("the read");
        let of = code(r.of);
        let tested = r.test.map(|p| match &p.kind {
            ExprKind::Lambda { body, .. } => code(body),
            _ => code(p),
        });
        let (fact, shown) = match (r.word, tested) {
            (OpenWord::All, Some(b)) => {
                (format!("makes `{b}` false"), format!("to make `{b}` false"))
            }
            (_, Some(b)) => (format!("makes `{b}` true"), format!("to make `{b}` true")),
            (_, None) => ("is kept".to_string(), "to be kept".to_string()),
        };
        let (headline, why) = match verdict {
            Verdict::Ends => return None,
            Verdict::Never => (
                format!("no entry of `{of}` {fact}"),
                "the read takes each entry in key order until one decides it, and none does, \
                 so it never stops"
                    .to_string(),
            ),
            Verdict::Undecided => (
                format!("no entry of `{of}` is shown {shown}"),
                format!(
                    "the integer solver finds no entry of `{of}` that {fact} for every value \
                     of the names the read reads"
                ),
            ),
            Verdict::Stopped(e) => (
                format!("no entry of `{of}` is shown {shown}"),
                format!(
                    "the proof reads integer literals, the entry, names of integers and the \
                     integer operators, and stops at `{}`",
                    code(e)
                ),
            ),
        };
        let lo = open_stream(r.of).map_or("a", |(lo, _)| code(lo));
        let repair = format!(
            "repair: give the range an upper end, as `{lo} ..< n` for an `n` that bounds the \
             search, or leave it, since a program may be meant never to end"
        );
        Some(Error {
            span,
            message: format!("`{read}` is not proved to end: {headline}"),
            notes: [why, repair]
                .into_iter()
                .map(|text| Note {
                    span,
                    text: text.into(),
                })
                .collect(),
            menu: String::new(),
            row: Some(Row::NotProvedToEnd),
        })
    }
}
