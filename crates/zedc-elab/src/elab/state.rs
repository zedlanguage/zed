//! The elaborator's state and the operations of elaboration that do not walk the unit: names,
//! errors, temporaries, types and `else` patterns. The walk over statements and expressions
//! ([`walk`](super::walk)) uses them.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use zed_kernel::types::Type as KType;
use zed_kernel::{Pattern as KPattern, Prim, Shared, Term, Value};

use zedc_base::rejection::Row;
use zedc_check::check::{Info, Misfit, Witness};
use zedc_resolve::resolve::tables::Tables;
use zedc_resolve::resolve::{Kind, Ref, prelude_layer};
use zedc_stage::defs::Test;
use zedc_syntax::ast::{Error, Expr, ExprKind, Pattern, Type};
use zedc_syntax::lex::Span;
use zedc_types::kernel_type::kernel_type;
use zedc_types::ty::Carrier;

use super::mark::Mark;

/// A binding of a scope: source name, kernel name, value.
pub(super) type Bind = (String, Arc<str>, Term);

pub(super) struct Elab<'a> {
    pub(super) t: Tables<'a>,
    /// Each binder's kernel name.
    pub(super) names: Vec<Arc<str>>,
    /// The checker's findings, which elaboration only reads.
    pub(super) info: &'a Info,
    /// The temporary each argument of a call that passes atoms is bound to, while the call is
    /// elaborated.
    pub(super) passing: HashMap<Span, Arc<str>>,
    /// The calls being guarded.
    pub(super) guarding: HashSet<Span>,
    /// The calls being read at a carrier ([`zedc_check::check::Fit::Read`]), each while it is
    /// elaborated.
    pub(super) reading: HashSet<Span>,
    /// The term of each component read a generic literal takes its carrier from
    /// ([`zedc_check::check::Witness`]), by the read's span: built once and shared.
    pub(super) reads: HashMap<Span, Shared>,
    /// Each operation on generic literals alone built once per carrier, by its span, with the
    /// witness its `match` is on (`walk::per_carrier`, L1.26a), whether each arm `is c` gives a
    /// value of carrier `c` (`+`, `-`, `*`, not `/` or `==`), and the carrier of the value of
    /// its last arm where it is known, so the operation it is an operand of finds them in O(1).
    pub(super) split: HashMap<Span, (&'a Witness, bool, Option<Carrier>)>,
    fresh: usize,
    pub(super) tests: Vec<Test>,
    pub(super) errors: Vec<Error>,
    /// The term a call leaving a parameter out binds it to, by the function's binder and the
    /// parameter's index.
    pub(super) defaults: HashMap<(usize, usize), Term>,
    /// The marks of a marked elaboration ([`elaborate_marked`](super::elaborate_marked)), `None` for an ordinary one.
    pub(super) marks: Option<Vec<Mark>>,
    /// The shared parts given their source sites so far ([`zed_kernel::sites::mark`]).
    pub(super) sited: HashSet<u64>,
    /// The output ports of the unit's `main`, `m.stdout` and `m.stderr` where it pushes to
    /// them, in the order of its header; empty when the unit has no `main`.
    pub(super) outputs: Vec<Arc<str>>,
}

impl<'a> Elab<'a> {
    pub(super) fn new(t: Tables<'a>, info: &'a Info) -> Self {
        let res = t.res;
        let mut count: HashMap<&str, usize> = HashMap::new();
        for b in &res.binders {
            *count.entry(&b.name).or_default() += 1;
        }
        let mut seen: HashMap<&str, usize> = HashMap::new();
        let outputs = t
            .funcs
            .values()
            .find_map(|f| f.ports())
            .map(|ports| ports.iter().map(|p| p.name.as_str().into()).collect())
            .unwrap_or_default();
        let names = res
            .binders
            .iter()
            .map(|b| {
                let k = seen.entry(&b.name).or_default();
                *k += 1;
                // A term names a prelude word of L1 by its bare name, so a binder of that name is
                // renamed; a word of a later layer never reaches a term, since its use stops the
                // unit at resolution, so a binder `rate` or `order` keeps its name.
                if count[b.name.as_str()] == 1 && prelude_layer(&b.name) != Some(1) {
                    b.name.as_str().into()
                } else {
                    format!("{}@{k}", b.name).into()
                }
            })
            .collect();
        Elab {
            t,
            names,
            info,
            passing: HashMap::new(),
            guarding: HashSet::new(),
            reading: HashSet::new(),
            reads: HashMap::new(),
            split: HashMap::new(),
            fresh: 0,
            tests: Vec::new(),
            errors: Vec::new(),
            defaults: HashMap::new(),
            marks: None,
            sited: HashSet::new(),
            outputs,
        }
    }

    /// The literal `v` of the constant `e`; marked when the elaboration is marked and `e` is
    /// an integer literal, whatever carrier it adopted.
    pub(super) fn constant(&mut self, e: &Expr, v: Value) -> Term {
        match &mut self.marks {
            Some(marks) if matches!(e.kind, ExprKind::Int { .. }) => {
                let m = Term::Lit(Value::Int(marks.len() as i64));
                marks.push(Mark {
                    span: e.span,
                    quotient: false,
                });
                Term::Prim(Prim::Neg, vec![Term::Lit(v), m])
            }
            _ => Term::Lit(v),
        }
    }

    pub(super) fn error<T>(&mut self, span: Span, message: impl Into<String>) -> Option<T> {
        self.error_in(None, span, message)
    }

    /// The error of a call's argument that does not fill a parameter of `who`, as the checker
    /// reports it too.
    pub(super) fn misfit<T>(&mut self, span: Span, misfit: Misfit, who: &str) -> Option<T> {
        self.error_in(misfit.row(), span, misfit.message(who))
    }

    pub(super) fn error_in<T>(
        &mut self,
        row: Option<Row>,
        span: Span,
        message: impl Into<String>,
    ) -> Option<T> {
        self.errors.push(Error {
            menu: String::new(),
            row,
            span,
            message: message.into(),
            notes: Vec::new(),
        });
        None
    }

    /// A fresh binder, `$k`: no written name starts with `$`, and the ZIR text form writes and
    /// reads it as it is (zir/text.rs).
    pub(super) fn temp(&mut self) -> Arc<str> {
        self.fresh += 1;
        format!("${}", self.fresh).into()
    }

    pub(super) fn id(&self, span: Span, name: &str) -> usize {
        self.t.id(span, name)
    }

    pub(super) fn name(&mut self, n: &str, span: Span) -> Option<Term> {
        match self.t.res.uses.get(&span) {
            Some(Ref::Bound(ids)) if ids.len() > 1 => self.error(
                span,
                format!(
                    "`{n}` names {} definitions, and this version of zedc does not yet choose among \
                     definitions that share a name. Give each of them a name of its own.",
                    ids.len()
                ),
            ),
            // The checker lets a port be named only where it is passed whole to a parameter
            // that is an output port ([`zedc_check::check`]); the parameter holds its name, and a
            // push to the parameter goes to the port of that name ([`Elab::push`]).
            Some(Ref::Bound(ids)) if self.t.res.binders[ids[0]].kind == Kind::Port => {
                Some(Term::Lit(Value::str(&self.t.res.binders[ids[0]].name)))
            }
            Some(Ref::Bound(ids)) => Some(Term::Var(self.names[ids[0]].clone())),
            Some(Ref::Prelude(w)) => Some(Term::Var(w.as_str().into())),
            // `main::files` outside `main`: a read of the port `main` opens under that name.
            Some(Ref::Main(p)) => Some(Term::Read(p.as_str().into())),
            Some(Ref::Unit { .. }) => {
                unreachable!("resolve sends a use of another unit's definition to step L2.4")
            }
            None => unreachable!("a resolved unit records every name"),
        }
    }

    /// The push of the value `v` to the target `port` of the push statement at `span`. A target
    /// that is a parameter, an output port passed to the function (DESIGN.md L1.19), holds the
    /// name of a port of `main` ([`Elab::name`]), and the push goes to the port of that name:
    /// `if out == "m.stdout" { m.stdout <- v } else { m.stderr <- v }`.
    // Complexity tradeoff: a push names its port statically in every later pass (the kernel's
    // world, ZIR, staging, preimages), so the port a parameter holds is chosen here among the
    // P ports `main` declares, P <= 2, by a chain of P - 1 tests: O(P) per push. Specializing
    // each function per port it is given would leave every later pass as it is too, but copies
    // a function once per tuple of ports, P^k copies for k output-port parameters, and gives each
    // copy's binders a second kernel name; making a port a value of the kernel would change every
    // later pass. Neither pays for itself while P <= 2.
    pub(super) fn push(&self, span: Span, port: &str, v: Term) -> Term {
        let v = Shared::new(v);
        let held = match self.t.res.uses.get(&span) {
            Some(Ref::Bound(ids)) if self.t.res.binders[ids[0]].kind == Kind::Param => ids[0],
            _ => return Term::Push(port.into(), v),
        };
        let Some((last, rest)) = self.outputs.split_last() else {
            // No `main` pushes to a port, so no call gives this parameter one: the checker
            // rejects any other argument, and the push is never reached.
            return Term::Push(port.into(), v);
        };
        let held = Term::Var(self.names[held].clone());
        rest.iter()
            .rev()
            .fold(Term::Push(last.clone(), v.clone()), |other, p| {
                Term::If(
                    Shared::new(Term::Prim(
                        Prim::Eq,
                        vec![held.clone(), Term::Lit(Value::str(p))],
                    )),
                    Shared::new(Term::Push(p.clone(), v.clone())),
                    Shared::new(other),
                )
            })
    }

    /// The declared function that `e` names, if it names exactly one.
    pub(super) fn declared(&self, e: &Expr) -> Option<usize> {
        match (&e.kind, self.t.res.uses.get(&e.span)) {
            (ExprKind::Name(_), Some(Ref::Bound(ids))) if ids.len() == 1 => {
                self.t.funcs.contains_key(&ids[0]).then_some(ids[0])
            }
            _ => None,
        }
    }

    /// The type a type expression denotes ([`kernel_type()`]); each name of a port in it is an
    /// error. Its bounds were checked by the checker, which reads every written type.
    pub(super) fn ty(&mut self, t: &Type) -> Option<KType> {
        let mut ports = Vec::new();
        let k = kernel_type(t, &mut ports, None);
        for (span, message) in ports {
            self.error::<()>(span, message);
        }
        k
    }

    /// An `else` pattern: an atom, its payload matched by position or by name; a field
    /// written `f:` binds `f`.
    ///
    /// Patterns nest as deep as the source, so the atoms still open wait on a stack. The
    /// parts are elaborated in written order, and the first refused part ends the atom and
    /// each atom around it, as the recursion did (step T2-mid).
    pub(super) fn pattern(&mut self, p: &Pattern) -> Option<KPattern> {
        let mut stack = Vec::new();
        let mut finished = self.pattern_open(p, &mut stack);
        loop {
            let Some(top) = stack.last_mut() else {
                return finished.expect("the pattern's result");
            };
            let step = match (top, finished.take()) {
                (_, Some(None)) => Err(None),
                (OpenPattern::Items { name, items, done }, k) => {
                    let items: &[Pattern] = items;
                    done.extend(k.flatten());
                    match items.get(done.len()) {
                        Some(item) => Ok(item),
                        None => Err(Some(KPattern::Atom((*name).into(), std::mem::take(done)))),
                    }
                }
                (
                    OpenPattern::Fields {
                        name,
                        fields,
                        span,
                        done,
                    },
                    k,
                ) => {
                    let fields: &[(String, Option<Pattern>)] = fields;
                    if let Some(Some(k)) = k {
                        done.push((fields[done.len()].0.as_str().into(), k));
                    }
                    loop {
                        match fields.get(done.len()) {
                            None => {
                                let fs = std::mem::take(done);
                                break Err(Some(KPattern::Fields((*name).into(), fs)));
                            }
                            Some((_, Some(sub))) => break Ok(sub),
                            Some((f, None)) => {
                                let b = self.names[self.id(*span, f)].clone();
                                done.push((f.as_str().into(), KPattern::Bind(b)));
                            }
                        }
                    }
                }
            };
            match step {
                Ok(part) => finished = self.pattern_open(part, &mut stack),
                Err(k) => {
                    stack.pop();
                    finished = Some(k);
                }
            }
        }
    }

    /// Opens the atom pattern `p` on `stack`; or, when its shape is refused, its result.
    fn pattern_open<'p>(
        &mut self,
        p: &'p Pattern,
        stack: &mut Vec<OpenPattern<'p>>,
    ) -> Option<Option<KPattern>> {
        let Pattern::Atom {
            name,
            fields,
            items,
            span,
        } = p
        else {
            unreachable!("resolve rejects the forms of layer L2")
        };
        if fields.is_empty() {
            stack.push(OpenPattern::Items {
                name,
                items,
                done: Vec::new(),
            });
            return None;
        }
        if !items.is_empty() {
            return Some(self.error(
                *span,
                "this atom's payload gives some values by position and some by name, and a \
                 payload is given all by position or all by name. Write every value by position, \
                 or every value with its name.",
            ));
        }
        if let Some(f) = repeated(fields.iter().map(|(f, _)| f.as_str())) {
            return Some(self.error(
                *span,
                format!(
                    "the pattern names `{f}` twice, and a pattern names each field of the \
                     payload once. Remove one of the two."
                ),
            ));
        }
        stack.push(OpenPattern::Fields {
            name,
            fields,
            span: *span,
            done: Vec::new(),
        });
        None
    }
}

/// An atom pattern being elaborated by [`Elab::pattern`]: by position, the patterns of the
/// items done; by name, the fields done.
enum OpenPattern<'p> {
    Items {
        name: &'p str,
        items: &'p [Pattern],
        done: Vec<KPattern>,
    },
    Fields {
        name: &'p str,
        fields: &'p [(String, Option<Pattern>)],
        span: Span,
        done: Vec<(Arc<str>, KPattern)>,
    },
}

/// A name that occurs twice in `names`.
fn repeated<'n>(names: impl Iterator<Item = &'n str>) -> Option<&'n str> {
    let mut seen = HashSet::new();
    names.into_iter().find(|n| !seen.insert(*n))
}
