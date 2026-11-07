//! The checker's walk over statements, expressions and declared functions, on a heap stack:
//! a program nested as deep as memory allows checks on a thread of any stack size.
//!
//! Each recursive call of the walk is a [`Job`]. What the caller does with the call's result
//! is a [`Frame`] pushed below the job, which reads the result from [`M::ret`] when the job
//! is done. A sequence of calls is one frame that starts the next call each time it resumes.
//! The jobs run in the order the calls ran, so the errors, the classes, the needs and the
//! records come out in the same order.

use std::rc::Rc;
use std::sync::Arc;

use super::arms::{Item, Node, Summarized, Translated, prim_of, var};
use super::*;
use zed_kernel::Shared;
use zedc_lattice::cell::Premises;
use zedc_lattice::lattice::Lattice;
use zedc_preimage::preimage::{Domains, LetIn, Lets, let_summary};
use zedc_preimage::product::{self, Product, Scope};

/// What a job gives back.
pub(super) enum Ret<'a> {
    /// Nothing yet, or a statement's result, which is nothing.
    None,
    Ty(Ty),
    Arg(Arg),
    Cond(Cond<'a>),
    Sig(Arc<Sig>),
}

/// A condition checked: its type, the facts it makes when it holds and when it does not, the
/// nodes of [`super::arms::Arms`] where it holds and where it does not, and the narrowing it
/// leaves in place.
pub(super) struct Cond<'a> {
    t: Ty,
    yes: Facts,
    no: Facts,
    sides: Sides,
    held: Held<'a>,
}

impl Cond<'_> {
    /// A condition that leaves nothing narrowed.
    fn of(t: Ty, yes: Facts, no: Facts, sides: Sides) -> Self {
        Cond {
            t,
            yes,
            no,
            sides,
            held: None,
        }
    }
}

/// The narrowing a condition leaves in place for the frame that reads it: the binders of its
/// facts where it holds (`true`) or where it fails (`false`), narrowed in their order, and what
/// restores them. A chain of `&&` keeps its left side narrowed while its right side is checked
/// and then narrows the right side's facts on top, so that each fact of the chain is narrowed
/// once and not once at each level of the chain (IS-chain-quad); `||` keeps where its sides
/// fail. The frame that reads the condition takes this narrowing over when it wants that side,
/// and restores it otherwise. Nothing is checked, and no error is derived, while a narrowing
/// is held: only `!`, `&&` and `||` apply to the condition's type, an application whose
/// arguments carry no site to derive.
type Held<'a> = Option<(bool, Saved<'a>)>;

/// What the type expected where an expression is checked says about it: the one function
/// type it is, if it is one, and the one numeric carrier it holds, if it holds one. Only
/// these decide how the expression is checked, so a frame keeps them and not the type.
#[derive(Default)]
pub(super) struct Want {
    fun: Option<Arc<Sig>>,
    num: Option<Carrier>,
}

impl Want {
    fn of(t: &Ty) -> Want {
        Want {
            fun: only_fn(t),
            num: t.numeric_carrier(),
        }
    }
}

impl<'a> Args<'a> {
    /// The arguments written in a call.
    fn of(positional: &'a [Expr], named: &'a [(String, Expr)]) -> Rc<Args<'a>> {
        Rc::new(Args {
            positional: positional.iter().map(ArgSrc::Expr).collect(),
            named: named
                .iter()
                .map(|(n, e)| (n.clone(), ArgSrc::Expr(e)))
                .collect(),
        })
    }

    fn all(&self) -> impl Iterator<Item = &ArgSrc<'a>> {
        self.positional
            .iter()
            .chain(self.named.iter().map(|(_, a)| a))
    }

    /// The expressions among the arguments, in written order.
    fn exprs(&self) -> Vec<&'a Expr> {
        self.all()
            .filter_map(|a| match a {
                ArgSrc::Expr(e) => Some(*e),
                ArgSrc::Got(_) => None,
            })
            .collect()
    }

    fn len(&self) -> usize {
        self.positional.len() + self.named.len()
    }

    /// Argument `k`, counting the positional ones first.
    fn nth(&self, k: usize) -> &ArgSrc<'a> {
        match self.positional.get(k) {
            Some(a) => a,
            None => &self.named[k - self.positional.len()].1,
        }
    }

    /// `x` added as argument `k` of `of` is: positional, or named as it is.
    fn push_as(&mut self, of: &Args<'a>, k: usize, x: ArgSrc<'a>) {
        match k.checked_sub(of.positional.len()) {
            None => self.positional.push(x),
            Some(i) => self.named.push((of.named[i].0.clone(), x)),
        }
    }

    fn get(&self, at: At) -> &ArgSrc<'a> {
        match at {
            At::Pos(i) => &self.positional[i],
            At::Named(i) => &self.named[i].1,
        }
    }

    /// Where the argument at `at` is written, or `call` for one checked before the call.
    fn span_at(&self, at: At, call: Span) -> Span {
        match self.get(at) {
            ArgSrc::Expr(e) => e.span,
            ArgSrc::Got(_) => call,
        }
    }
}

/// Where a parameter's argument is among a call's arguments.
#[derive(Clone, Copy)]
pub(super) enum At {
    Pos(usize),
    Named(usize),
}

pub(super) enum Job<'a> {
    /// An expression's type, recorded for derivations.
    Expr(&'a Expr),
    /// An expression's type where a type is wanted.
    At(&'a Expr, Want),
    /// An argument.
    Arg(&'a Expr, Want),
    /// A condition.
    Cond(&'a Expr),
    /// The statements of a scope; whether it is the unit's.
    Scope(&'a [Stmt], bool),
    /// A lambda's or a function's body.
    Body(&'a Expr, Want),
    /// A declared function's signature.
    Infer(&'a Function, Span),
    /// A caller waiting for the result of the jobs above it.
    K(Frame<'a>),
}

pub(super) enum Frame<'a> {
    /// Records the type of the expression.
    Seen(&'a Expr),
    /// Gives this type in place of the result.
    Const(Ty),
    /// Reports the error, if any, and gives nothing.
    Fail(Option<(Span, String)>),
    Str(Box<StrF<'a>>),
    Unary(&'static str, Span),
    Tuple(Box<TupleF<'a>>),
    Else1(&'a Expr),
    Else2(&'a Expr, Ty),
    If1(&'a Expr),
    If2 {
        then: &'a Expr,
        otherwise: &'a Expr,
        out: Ty,
        no: Facts,
        /// The node where the condition fails.
        fails: usize,
    },
    If3 {
        then: &'a Expr,
        otherwise: &'a Expr,
        out: Ty,
        a: Box<Ty>,
    },
    /// Restores what a narrowing changed, and gives the result through.
    Widen(Saved<'a>),
    CondIs(&'a Expr),
    CondNot(Span),
    CondAnd1 {
        op: &'static str,
        b: &'a Expr,
        span: Span,
    },
    CondAnd2(Box<CondAnd<'a>>),
    CondOf(&'a Expr),
    Logic1 {
        op: &'static str,
        b: &'a Expr,
        span: Span,
    },
    Logic2 {
        op: &'static str,
        span: Span,
        ta: Ty,
    },
    Bin1 {
        op: &'static str,
        b: &'a Expr,
        span: Span,
    },
    Bin2 {
        op: &'static str,
        b: &'a Expr,
        span: Span,
        x: Box<Arg>,
    },
    ArgOf(&'a Expr),
    Scope(Box<ScopeF<'a>>),
    Tests(Box<ScopeF<'a>>),
    TestArgs(Box<TestF<'a>>),
    TestWant(Box<TestF<'a>>, Ty),
    Bind(&'a Stmt),
    Declared(&'a Stmt),
    Pushed(&'a Stmt),
    InferGiven(Box<InferF<'a>>),
    InferDefaults(Box<InferF<'a>>),
    InferEnd(Box<InferF<'a>>),
    AtomArgs(Box<AtomF<'a>>),
    CallAlso {
        id: usize,
        from: usize,
        sig: Arc<Sig>,
    },
    Callee {
        callee: &'a Expr,
        positional: &'a [Expr],
        named: &'a [(String, Expr)],
        curry: bool,
        span: Span,
    },
    Word(&'a str, Span),
    Bits(Box<BitsF<'a>>),
    CallValue(Box<CallValueF<'a>>),
    CallSig(Box<CallSigF<'a>>),
    Member1(Box<MemberF<'a>>),
    Member2(Ty),
    Section {
        sig: Arc<Sig>,
        what: String,
        span: Span,
    },
    Index1 {
        k: &'a Expr,
        span: Span,
    },
    AtKey(Ty, Span),
    AtIndex(Ty, Option<usize>, Span),
    LambdaEnd {
        names: Vec<SParam>,
        /// The binder of the parameter in each slot, if a parameter takes it.
        ids: Vec<Option<usize>>,
        level: usize,
        tys: Vec<Ty>,
        /// The lambda's body.
        body: &'a Expr,
    },
    /// A parameter of a lambda bound to the type of its default.
    BindDefault(&'a Param),
    FitLambda(Box<FitF<'a>>),
    /// A lambda checked generic in its parameters, to be passed for the function type `e`
    /// as a declared function is.
    FitGeneric {
        e: Arc<Sig>,
        span: Span,
        order: Vec<Option<usize>>,
        extra: Vec<usize>,
    },
}

pub(super) struct StrF<'a> {
    parts: &'a [StrPart],
    /// The next part.
    i: usize,
    text: String,
    holes: Vec<Ty>,
    /// The hole being checked.
    hole: Option<&'a Expr>,
}

pub(super) struct TupleF<'a> {
    es: &'a [Expr],
    /// How many have been started; one more than `out` holds while one is checked.
    started: usize,
    out: Vec<Ty>,
    /// Whether each component is checked as data.
    data: bool,
}

pub(super) struct CondAnd<'a> {
    op: &'static str,
    span: Span,
    ta: Ty,
    ya: Facts,
    na: Facts,
    saved: Saved<'a>,
    /// The nodes where the first side holds and where it fails.
    sa: Sides,
}

/// The nodes of [`super::arms::Arms`] where a condition holds and where it fails.
pub(super) type Sides = (usize, usize);

pub(super) struct ScopeF<'a> {
    items: Vec<&'a Stmt>,
    order: Vec<usize>,
    /// The next statement in `order`, then the next item whose tests are checked.
    i: usize,
    top: bool,
    export: Option<&'a [Expr]>,
}

pub(super) struct TestF<'a> {
    f: &'a Function,
    sig: Arc<Sig>,
    case: usize,
    exprs: Vec<&'a Expr>,
    got: Vec<Option<Arg>>,
    waiting: bool,
}

pub(super) struct InferF<'a> {
    f: &'a Function,
    params: Vec<SParam>,
    ids: Vec<usize>,
    given: Vec<Option<Ty>>,
    level: usize,
    tys: Vec<Ty>,
    /// The parameter whose default is checked next.
    i: usize,
    /// While a default is checked: the class of its parameter's type, if it is one.
    waiting: Option<Option<usize>>,
    /// While a closed default is checked for `given`.
    closed: bool,
}

pub(super) struct AtomF<'a> {
    name: &'a str,
    positional: &'a [Expr],
    named: &'a [(String, Expr)],
    started: usize,
    items: Vec<Ty>,
    fields: BTreeMap<Arc<str>, Ty>,
}

pub(super) struct BitsF<'a> {
    w: &'a str,
    p: Prim,
    sig: Arc<Sig>,
    positional: &'a [Expr],
    named: &'a [(String, Expr)],
    span: Span,
    /// The operands placed so far, by parameter.
    slots: Vec<Option<(Arg, &'a Expr)>>,
    /// Whether every argument so far found a free parameter of its kind.
    fits: bool,
    /// How many arguments have been started; one more than placed while one is checked.
    started: usize,
    /// 1 when the receiver fills the first parameter, else 0.
    first: usize,
}

pub(super) struct CallValueF<'a> {
    what: Rc<str>,
    receiver: Option<Arg>,
    args: Rc<Args<'a>>,
    curry: bool,
    span: Span,
    out: Ty,
    checked: bool,
    /// The pieces not yet applied, the next last.
    pieces: Vec<Piece>,
    /// The signature recorded for the call, put once the arguments are found.
    call: Option<Arc<Sig>>,
    /// For a class's call, the arguments found so far, and the next one's index.
    found: Option<(Args<'a>, usize)>,
    waiting: bool,
}

pub(super) struct CallSigF<'a> {
    sig: Arc<Sig>,
    receiver: Option<Arg>,
    args: Rc<Args<'a>>,
    slots: Vec<Option<At>>,
    got: Vec<Option<Arg>>,
    missing: Vec<usize>,
    curry: bool,
    span: Span,
    what: Rc<str>,
    waiting: bool,
}

pub(super) struct MemberF<'a> {
    of: &'a Expr,
    name: &'a str,
    safe: bool,
    member: Span,
    positional: &'a [Expr],
    named: &'a [(String, Expr)],
    curry: bool,
    span: Span,
}

pub(super) struct FitF<'a> {
    params: &'a [Param],
    body: &'a Expr,
    e: Arc<Sig>,
    /// Each bounded variable of `e` that no parameter holds, bound to its whole bound.
    unheld: Binds,
    span: Span,
    order: Vec<Option<usize>>,
    extra: Vec<usize>,
    /// The arrow being checked, and whether its parameters are bound.
    a: usize,
    entered: bool,
    /// The next parameter of `extra` whose default is checked.
    x: usize,
    waiting: Option<FitWait>,
}

#[derive(Clone, Copy)]
pub(super) enum FitWait {
    Extra,
    Body,
}

/// The machine: the jobs left, the next on top, and the result of the last one done.
pub(super) struct M<'a> {
    stack: Vec<Job<'a>>,
    ret: Ret<'a>,
}

impl<'a> M<'a> {
    fn new() -> Self {
        M {
            stack: Vec::new(),
            ret: Ret::None,
        }
    }

    fn k(&mut self, f: Frame<'a>) {
        self.stack.push(Job::K(f));
    }

    fn job(&mut self, j: Job<'a>) {
        self.stack.push(j);
    }

    /// Jobs checking each expression in turn, their types unused.
    fn each(&mut self, es: Vec<&'a Expr>) {
        self.stack.extend(es.into_iter().rev().map(Job::Expr));
    }

    fn ty(&mut self, t: Ty) {
        self.ret = Ret::Ty(t);
    }

    fn take(&mut self) -> Ret<'a> {
        std::mem::replace(&mut self.ret, Ret::None)
    }

    fn take_ty(&mut self) -> Ty {
        match self.take() {
            Ret::Ty(t) => t,
            _ => unreachable!("the job above gives a type"),
        }
    }

    fn take_arg(&mut self) -> Arg {
        match self.take() {
            Ret::Arg(a) => a,
            _ => unreachable!("the job above gives an argument"),
        }
    }

    fn take_cond(&mut self) -> Cond<'a> {
        match self.take() {
            Ret::Cond(c) => c,
            _ => unreachable!("the job above gives a condition"),
        }
    }

    fn take_sig(&mut self) -> Arc<Sig> {
        match self.take() {
            Ret::Sig(s) => s,
            _ => unreachable!("the job above gives a signature"),
        }
    }
}

impl<'t, 'a> Ck<'t, 'a> {
    /// Checks the statements of the unit.
    pub(super) fn walk(&mut self, unit: &'a [Stmt]) {
        let mut m = M::new();
        m.job(Job::Scope(unit, true));
        self.drive(&mut m);
    }

    /// A call through a value of `f` with arguments already found, as a need of a generic
    /// function checked again at a call: what it gives. Its checks nest as deep as the needs
    /// they check, which do not follow the nesting of the text.
    pub(super) fn call_found(
        &mut self,
        f: &Ty,
        what: &str,
        args: Args<'a>,
        curry: bool,
        span: Span,
    ) -> Ty {
        let mut m = M::new();
        self.call_value(&mut m, f, what.into(), None, Rc::new(args), curry, span);
        self.drive(&mut m);
        m.take_ty()
    }

    fn drive(&mut self, m: &mut M<'a>) {
        while let Some(j) = m.stack.pop() {
            match j {
                Job::Expr(e) => {
                    m.k(Frame::Seen(e));
                    self.expr_of(m, e);
                }
                Job::At(e, w) => self.expr_at(m, e, w),
                Job::Arg(e, w) => self.arg(m, e, w),
                Job::Cond(e) => self.cond(m, e),
                Job::Scope(stmts, top) => self.scope(m, stmts, top),
                Job::Body(e, w) => match &e.kind {
                    ExprKind::Block(stmts) => self.scope(m, stmts, false),
                    _ => self.expr_at(m, e, w),
                },
                Job::Infer(f, span) => self.infer(m, f, span),
                Job::K(f) => self.resume(m, f),
            }
        }
    }

    /// A caller resumed with the result of the jobs above it.
    fn resume(&mut self, m: &mut M<'a>, f: Frame<'a>) {
        match f {
            Frame::Seen(e) => {
                let t = m.take_ty();
                let src = match &e.kind {
                    ExprKind::Name(_) => match self.t.res.uses.get(&e.span) {
                        Some(Ref::Bound(ids)) if ids.len() == 1 => Src::Name(ids[0]),
                        _ => Src::Other(e),
                    },
                    ExprKind::Call { callee, .. } => match self.declared(callee) {
                        Some(id) => Src::Call(id, e),
                        None => Src::Other(e),
                    },
                    _ => Src::Other(e),
                };
                // Each set is kept as made, never tested for emptiness here: `is_empty` looks a
                // type up in a memo ordered by contents, `O(n)` per comparison for a set of `n`
                // atoms that shares a prefix with others, so a test per node of a chain would
                // cost `O(n²)`.
                let (u, made) = match self.unnamed_of(e, &t, &src) {
                    Some((u, made)) => (Some(u), made),
                    None => (None, None),
                };
                let tried = self.tried.remove(&e.span);
                let outside = self.outside_of(e, &t, &src, tried);
                for (map, set) in [
                    (&mut self.unnamed, u),
                    (&mut self.made, made),
                    (&mut self.outside, outside),
                ] {
                    match set {
                        Some(set) => map.insert(e.span, set),
                        None => map.remove(&e.span),
                    };
                }
                // A tuple written out keeps no type of its own (`Seen`).
                let kept = (!matches!(e.kind, ExprKind::Tuple(_))).then(|| t.clone());
                self.seen.insert(e.span, (kept, src));
                m.ty(t);
            }
            Frame::Const(t) => {
                m.take();
                m.ty(t);
            }
            Frame::Fail(err) => {
                m.take();
                if let Some((span, message)) = err {
                    self.error(span, message);
                }
                m.ty(Ty::empty());
            }
            Frame::Str(s) => self.str_step(m, s),
            Frame::Unary(op, span) => {
                let x = m.take_arg();
                let sig = op_sig(op);
                let t = self
                    .apply(&format!("`{op}`"), &sig, vec![Some(x)], true, span)
                    .0;
                m.ty(t);
            }
            Frame::Tuple(s) => self.tuple_step(m, s),
            Frame::Else1(e) => {
                let v = m.take_ty();
                let ExprKind::Else {
                    pattern, default, ..
                } = &e.kind
                else {
                    unreachable!("an `else`")
                };
                if let (Some(ids), Some(p)) = (self.t.res.patterns.get(&e.span), pattern) {
                    self.bind_pattern(p, &v, ids.start);
                }
                m.k(Frame::Else2(e, v));
                m.job(Job::Expr(default));
            }
            Frame::Else2(e, v) => {
                let d = m.take_ty();
                let ExprKind::Else { pattern, .. } = &e.kind else {
                    unreachable!("an `else`")
                };
                let t = match pattern {
                    None => self.narrowed(&v, &Narrow::Loose, e.span).union(&d),
                    Some(Pattern::Atom {
                        name,
                        fields,
                        items,
                        ..
                    }) if fields.is_empty() && items.is_empty() => {
                        // A bare pattern matches the atom with any payload or none.
                        let narrow = Narrow::Atom(name.as_str().into());
                        self.narrowed(&v, &narrow, e.span).union(&d)
                    }
                    Some(_) => v.union(&d),
                };
                m.ty(t);
            }
            Frame::If1(e) => {
                let Cond {
                    t: c,
                    yes,
                    no,
                    sides: (holds, fails),
                    held,
                } = m.take_cond();
                // The condition is checked with nothing narrowed by its own tests, and its
                // derivation reads the origins of its names as they are outside it.
                self.release(held);
                let ExprKind::If {
                    cond,
                    then,
                    otherwise,
                } = &e.kind
                else {
                    unreachable!("an `if`")
                };
                let out = self.passing(&c, "the condition of `if`", cond.span);
                let what = "the condition of `if`";
                for p in c.pieces() {
                    let ok = match self.class_of(&p) {
                        Some(k) => self.restrict(k, Carrier::Bool.bit(), what, cond.span),
                        None => p.is_atoms() || p.carrier() == Some(Carrier::Bool),
                    };
                    if !ok {
                        let shown = self.show(&c);
                        let mut notes = self.derive(&[cond.span]);
                        notes.extend(self.reasons(&c));
                        self.error_with(cond.span, format!("{what} is {shown}, not bool"), notes);
                        break;
                    }
                }
                m.k(Frame::If2 {
                    then,
                    otherwise,
                    out,
                    no,
                    fails,
                });
                self.under(m, &yes, holds, then);
            }
            Frame::If2 {
                then,
                otherwise,
                out,
                no,
                fails,
            } => {
                let a = m.take_ty();
                m.k(Frame::If3 {
                    then,
                    otherwise,
                    out,
                    a: Box::new(a),
                });
                self.under(m, &no, fails, otherwise);
            }
            Frame::If3 {
                then,
                otherwise,
                out,
                a,
            } => {
                let b = m.take_ty();
                let t = self.branches(then, &a, otherwise, &b);
                m.ty(out.union(&t));
            }
            Frame::Widen(saved) => {
                let r = m.take();
                self.widen(saved);
                self.arms.leave();
                m.ret = r;
            }
            Frame::CondIs(e) => {
                let v = m.take_ty();
                let ExprKind::Is { of, ty, negated } = &e.kind else {
                    unreachable!("an `is`")
                };
                let t = denoted(ty);
                let bool_ = Ty::carrier(Carrier::Bool);
                let here = self.arms.here();
                let b = match (&of.kind, self.t.res.uses.get(&of.span)) {
                    (ExprKind::Name(_), Some(Ref::Bound(ids))) if ids.len() == 1 => ids[0],
                    _ => {
                        m.ret =
                            Ret::Cond(Cond::of(bool_, Facts::new(), Facts::new(), (here, here)));
                        return;
                    }
                };
                // The meet keeps the functions of `v` whole; the difference compares them with
                // those of `t`, reading the classes solved inside them ([`Ck::stale`]).
                // The reduced product reads no `is`: its scope is the one it is checked in.
                let yes = v.meet(&t);
                let no = self.narrowed(&v, &Narrow::Not(t), e.span);
                let (yes, no) = (
                    Facts::from([(b, yes, e.span)]),
                    Facts::from([(b, no, e.span)]),
                );
                m.ret = Ret::Cond(match negated {
                    false => Cond::of(bool_, yes, no, (here, here)),
                    true => Cond::of(bool_, no, yes, (here, here)),
                });
            }
            Frame::CondNot(span) => {
                let c = m.take_cond();
                let sig = op_sig("!");
                let t = self
                    .apply("`!`", &sig, vec![Some(Arg::of(c.t))], true, span)
                    .0;
                m.ret = Ret::Cond(Cond {
                    t,
                    yes: c.no,
                    no: c.yes,
                    sides: (c.sides.1, c.sides.0),
                    held: c.held.map(|(holds, saved)| (!holds, saved)),
                });
            }
            Frame::CondAnd1 { op, b, span } => {
                let a = m.take_cond();
                let and = op == "&&";
                let saved = self.narrow_side(a.held, if and { &a.yes } else { &a.no }, and);
                self.arms.enter(if and { a.sides.0 } else { a.sides.1 });
                m.k(Frame::CondAnd2(Box::new(CondAnd {
                    op,
                    span,
                    ta: a.t,
                    ya: a.yes,
                    na: a.no,
                    saved,
                    sa: a.sides,
                })));
                m.job(Job::Cond(b));
            }
            Frame::CondAnd2(s) => {
                let b = m.take_cond();
                let CondAnd {
                    op,
                    span,
                    ta,
                    ya,
                    na,
                    saved,
                    sa,
                } = *s;
                // `a`'s side stays narrowed and `b`'s is narrowed on top, as a frame reading
                // the whole condition would narrow them, in their order.
                let and = op == "&&";
                let more = self.narrow_side(b.held, if and { &b.yes } else { &b.no }, and);
                let saved = joined(saved, more);
                self.arms.leave();
                // `b` is checked where `a` holds for `&&`, and fails for `||`, so its nodes
                // are already within that one.
                let sb = b.sides;
                let sides = match and {
                    true => (sb.0, self.arms.join(sa.1, sb.1)),
                    false => (self.arms.join(sa.0, sb.0), sb.1),
                };
                let sig = op_sig("&&");
                let t = self
                    .apply(
                        &format!("`{op}`"),
                        &sig,
                        vec![Some(Arg::of(ta)), Some(Arg::of(b.t))],
                        true,
                        span,
                    )
                    .0;
                let (yes, no) = match and {
                    true => (joined(ya, b.yes), Facts::new()),
                    false => (Facts::new(), joined(na, b.no)),
                };
                m.ret = Ret::Cond(Cond {
                    t,
                    yes,
                    no,
                    sides,
                    held: Some((and, saved)),
                });
            }
            Frame::CondOf(e) => {
                let t = m.take_ty();
                let sides = self.test_nodes(e);
                m.ret = Ret::Cond(Cond::of(t, Facts::new(), Facts::new(), sides));
            }
            Frame::Logic1 { op, b, span } => {
                let a = m.take_cond();
                let and = op == "&&";
                let (first, at) = match and {
                    true => (a.yes, a.sides.0),
                    false => (a.no, a.sides.1),
                };
                m.k(Frame::Logic2 { op, span, ta: a.t });
                let saved = self.narrow_side(a.held, &first, and);
                self.within(m, saved, at, b);
            }
            Frame::Logic2 { op, span, ta } => {
                let tb = m.take_ty();
                let sig = op_sig("&&");
                let t = self
                    .apply(
                        &format!("`{op}`"),
                        &sig,
                        vec![Some(Arg::of(ta)), Some(Arg::of(tb))],
                        true,
                        span,
                    )
                    .0;
                m.ty(t);
            }
            Frame::Bin1 { op, b, span } => {
                let x = m.take_arg();
                m.k(Frame::Bin2 {
                    op,
                    b,
                    span,
                    x: Box::new(x),
                });
                m.job(Job::Arg(b, Want::default()));
            }
            Frame::Bin2 { op, b, span, x } => {
                let y = m.take_arg();
                let t = self.binary_end(op, *x, y, b, span);
                m.ty(t);
            }
            Frame::ArgOf(e) => {
                let t = m.take_ty();
                m.ret = Ret::Arg(Arg {
                    at: Some(e.span),
                    parts: parts(e),
                    ..Arg::of(t)
                });
            }
            Frame::Scope(s) => {
                m.take();
                self.scope_step(m, s);
            }
            Frame::Tests(s) => {
                m.take();
                self.tests_step(m, s);
            }
            Frame::TestArgs(s) => self.test_args(m, s),
            Frame::TestWant(s, result) => {
                let want = m.take_arg();
                self.equal(&Arg::of(result), &want);
                let TestF { f, sig, case, .. } = *s;
                self.test_case(m, f, sig, case + 1);
            }
            Frame::Bind(s) => {
                let v = m.take_ty();
                self.bind(s, v);
            }
            Frame::Declared(s) => {
                let sig = m.take_sig();
                let StmtKind::Function(f) = &s.kind else {
                    unreachable!("a function")
                };
                let id = self.id(s.span, &f.name);
                self.origin(id, s.span, Why::Declared(sig.clone()), None);
                self.env.insert(id, Ty::func(sig.clone()));
                self.put(Undo::Sig(id, Some(sig)));
            }
            Frame::Pushed(s) => {
                let t = m.take_ty();
                let StmtKind::Push { port, value } = &s.kind else {
                    unreachable!("a push")
                };
                if self.lines_out.contains(port) {
                    self.pushed(&t, value.span);
                }
            }
            Frame::InferGiven(s) => self.infer_given(m, s),
            Frame::InferDefaults(s) => self.infer_defaults(m, s),
            Frame::InferEnd(s) => {
                let result = m.take_ty();
                let InferF {
                    params,
                    ids,
                    tys,
                    level,
                    f,
                    ..
                } = *s;
                let ids: Vec<Option<usize>> = ids.into_iter().map(Some).collect();
                let sig = self.handled_sig(params, &ids, tys, result, &f.body);
                let sig = self.generalize(level, sig);
                m.ret = Ret::Sig(sig);
            }
            Frame::AtomArgs(s) => self.atom_step(m, s),
            Frame::CallAlso { id, from, sig } => {
                let out = m.take_ty();
                if let Some(o) = self.whence.get(&id).map(|o| o.span) {
                    let t = self.t;
                    let name = &t.funcs[&id].name;
                    self.also(from, o, |ck| {
                        format!("`{name}` is declared here, `{}`", ck.sig_text(&sig))
                    });
                }
                m.ty(out);
            }
            Frame::Callee {
                callee,
                positional,
                named,
                curry,
                span,
            } => {
                let f = m.take_ty();
                let what = match &callee.kind {
                    ExprKind::Name(n) => n.clone(),
                    _ => "this value".into(),
                };
                if let (ExprKind::Name(w), Some(Ref::Prelude(_))) =
                    (&callee.kind, self.t.res.uses.get(&callee.span))
                {
                    if let Some(p) = bit_prim(w) {
                        return self.bits(m, w, p, None, positional, named, curry, span);
                    }
                    if word_arity(w) != 1 {
                        let args = Args::of(positional, named);
                        return self.call_value(m, &f, what.into(), None, args, curry, span);
                    }
                    if named.is_empty() && !curry && positional.len() == 1 {
                        return self.word(m, w, positional, None, span);
                    }
                    // Elaboration reports named arguments and `...`.
                    let err = (named.is_empty() && !curry)
                        .then(|| (span, format!("`{w}` takes one argument")));
                    m.k(Frame::Fail(err));
                    m.each(Args::of(positional, named).exprs());
                    return;
                }
                let args = Args::of(positional, named);
                self.call_value(m, &f, what.into(), None, args, curry, span);
            }
            Frame::Word(w, span) => {
                let x = m.take_arg();
                let t = self.word_end(w, x, span);
                m.ty(t);
            }
            Frame::Bits(s) => self.bits_step(m, s),
            Frame::CallValue(s) => self.call_value_step(m, s),
            Frame::CallSig(s) => self.call_sig_step(m, s),
            Frame::Member1(s) => {
                let x = m.take_arg();
                self.member_end(m, *s, x);
            }
            Frame::Member2(atoms) => {
                let out = m.take_ty();
                m.ty(out.union(&atoms));
            }
            Frame::Section { sig, what, span } => {
                let x = m.take_arg();
                let n = sig.params.len();
                let mut args = vec![None; n];
                args[0] = Some(x);
                let missing: Vec<usize> = (1..n).collect();
                let t = self.partial(&sig, args, &missing, true, &what, span);
                m.ty(t);
            }
            Frame::Index1 { k, span } => {
                let v = m.take_ty();
                let ExprKind::Int { .. } = &k.kind else {
                    m.k(Frame::AtKey(v, span));
                    m.job(Job::Arg(k, Want::default()));
                    return;
                };
                let i = match literal(k).map(|l| l.value) {
                    Some(Value::Int(i)) => i,
                    _ => return m.ty(Ty::dynamic()),
                };
                m.k(Frame::AtIndex(v, usize::try_from(i).ok(), span));
                m.job(Job::Arg(k, Want::default()));
            }
            Frame::AtKey(v, span) => {
                let x = m.take_arg();
                let t = self.at_key(&v, x, span);
                m.ty(t);
            }
            Frame::AtIndex(v, i, span) => {
                let x = m.take_arg();
                let t = self.at_index(&v, i, x, span);
                m.ty(t);
            }
            Frame::LambdaEnd {
                names,
                ids,
                level,
                tys,
                body,
            } => {
                let result = m.take_ty();
                let sig = self.handled_sig(names, &ids, tys, result, body);
                let sig = self.generalize(level, sig);
                m.ty(Ty::func(sig));
            }
            Frame::BindDefault(p) => {
                let t = m.take_ty();
                let id = self.id(p.span, &p.name);
                self.env.insert(id, t);
            }
            Frame::FitLambda(s) => self.fit_step(m, s),
            Frame::FitGeneric {
                e,
                span,
                order,
                extra,
            } => {
                let t = m.take_ty();
                let s = only_fn(&t).expect("a lambda's type is a function type");
                if !self.fits_slot(&s, &e, "the lambda", span) {
                    let (s, e) = (self.sig_text(&s), self.sig_text(&e));
                    self.error(span, format!("the lambda is `{s}`, not `{e}`"));
                }
                self.fitted(span, order, extra);
                m.ty(Ty::func(e));
            }
        }
    }

    /// `e` checked with the binders of `facts` narrowed, in node `at` of [`super::arms::Arms`].
    fn under(&mut self, m: &mut M<'a>, facts: &Facts, at: usize, e: &'a Expr) {
        let saved = self.narrow(facts);
        self.within(m, saved, at, e);
    }

    /// `e` checked with the narrowing `saved` restores, in node `at` of [`super::arms::Arms`].
    fn within(&mut self, m: &mut M<'a>, saved: Saved<'a>, at: usize, e: &'a Expr) {
        self.arms.enter(at);
        m.k(Frame::Widen(saved));
        m.job(Job::Expr(e));
    }

    /// The binders of `facts`, the facts of a condition where it holds (`holds`) or where it
    /// fails, narrowed, and what restores them: the narrowing `held` the condition left in
    /// place when it is of that side, and otherwise `held` restored and `facts` narrowed anew.
    /// The facts of a side of `&&` where it fails, or of `||` where it holds, are none, and an
    /// `is` holds no narrowing, so the narrowing made anew is of at most one fact; a condition
    /// read whole, by `if` or by `&&` outside a condition, narrows its facts once.
    fn narrow_side(&mut self, held: Held<'a>, facts: &Facts, holds: bool) -> Saved<'a> {
        match held {
            Some((side, saved)) if side == holds => saved,
            held => {
                self.release(held);
                self.narrow(facts)
            }
        }
    }

    /// Restores the narrowing a condition left in place, if any.
    fn release(&mut self, held: Held<'a>) {
        if let Some((_, saved)) = held {
            self.widen(saved);
        }
    }

    /// The statements of one scope, in the order elaboration binds them; the export's type.
    fn scope(&mut self, m: &mut M<'a>, stmts: &'a [Stmt], top: bool) {
        let mut export = None;
        let mut items: Vec<&'a Stmt> = Vec::new();
        for s in stmts {
            match &s.kind {
                StmtKind::Return(es) => export = Some(&es[..]),
                _ => items.push(s),
            }
        }
        let Ok(order) = self.t.order(&items) else {
            return m.ty(Ty::dynamic());
        };
        let s = ScopeF {
            items,
            order,
            i: 0,
            top,
            export,
        };
        self.scope_step(m, Box::new(s));
    }

    fn scope_step(&mut self, m: &mut M<'a>, mut s: Box<ScopeF<'a>>) {
        if let Some(&k) = s.order.get(s.i) {
            let st = s.items[k];
            s.i += 1;
            m.k(Frame::Scope(s));
            return self.stmt(m, st);
        }
        if !s.top {
            return self.export(m, s.export);
        }
        for st in &s.items {
            if let StmtKind::Bind { targets, .. } = &st.kind
                && let [Target::Name(n, _)] = &targets[..]
                && let Some(ty) = self.env.get(&self.id(st.span, n))
            {
                self.put(Undo::Top(n.clone(), Some(ty.clone())));
            }
        }
        s.i = 0;
        self.tests_step(m, s);
    }

    /// The `test` tables of the scope's functions from item `s.i` on, then the export.
    fn tests_step(&mut self, m: &mut M<'a>, mut s: Box<ScopeF<'a>>) {
        while let Some(&st) = s.items.get(s.i) {
            s.i += 1;
            let StmtKind::Function(f) = &st.kind else {
                continue;
            };
            let id = self.id(st.span, &f.name);
            let Some(sig) = self.info.sigs.get(&id).cloned() else {
                continue;
            };
            if f.ports.is_some() {
                continue;
            }
            m.k(Frame::Tests(s));
            return self.test_case(m, f, sig, 0);
        }
        self.export(m, s.export);
    }

    fn export(&mut self, m: &mut M<'a>, export: Option<&'a [Expr]>) {
        match export {
            None => m.ty(Ty::tuple(Vec::new())),
            Some([e]) => m.job(Job::Expr(e)),
            Some(es) => self.tuple_step(
                m,
                Box::new(TupleF {
                    es,
                    started: 0,
                    out: Vec::new(),
                    data: false,
                }),
            ),
        }
    }

    /// The cases of `f`'s `test` tables from `case` on, each checked as a call, its expected
    /// value adopting as the right side of `==` does.
    fn test_case(&mut self, m: &mut M<'a>, f: &'a Function, sig: Arc<Sig>, case: usize) {
        for (c, (input, _)) in f.tests.iter().enumerate().skip(case) {
            let exprs: Vec<&'a Expr> = match (&input.kind, f.params.len()) {
                (_, 1) => vec![input],
                (ExprKind::Tuple(items), n) if items.len() == n => items.iter().collect(),
                _ => continue,
            };
            let s = TestF {
                f,
                sig,
                case: c,
                exprs,
                got: Vec::new(),
                waiting: false,
            };
            return self.test_args(m, Box::new(s));
        }
    }

    fn test_args(&mut self, m: &mut M<'a>, mut s: Box<TestF<'a>>) {
        if s.waiting {
            s.waiting = false;
            let x = m.take_arg();
            s.got.push(Some(x));
        }
        if let Some(&a) = s.exprs.get(s.got.len()) {
            s.waiting = true;
            m.k(Frame::TestArgs(s));
            return m.job(Job::Arg(a, Want::default()));
        }
        let (input, expected) = &s.f.tests[s.case];
        let args = std::mem::take(&mut s.got);
        let what = format!("`{}`", s.f.name);
        let (result, _) = self.apply(&what, &s.sig, args, false, input.span);
        m.k(Frame::TestWant(s, result));
        m.job(Job::Arg(expected, Want::default()));
    }

    fn stmt(&mut self, m: &mut M<'a>, s: &'a Stmt) {
        match &s.kind {
            // It has no type: it binds nothing and gives no value.
            StmtKind::UnitAnnot(_) => {}
            StmtKind::Struct(_)
            | StmtKind::Type(_)
            | StmtKind::Method(_)
            | StmtKind::Import(_)
            | StmtKind::Local(_)
            | StmtKind::Annotated { .. } => {
                unreachable!("resolve rejects the forms of layer L2")
            }
            StmtKind::Mutable(_)
            | StmtKind::IndexedDef(_)
            | StmtKind::While(_)
            | StmtKind::Until(_)
            | StmtKind::Expr(_) => unreachable!("resolve rejects the forms of layer L6"),
            StmtKind::Bind { value, .. } => {
                m.k(Frame::Bind(s));
                m.job(Job::Expr(value));
            }
            StmtKind::Function(f) => {
                m.k(Frame::Declared(s));
                m.job(Job::Infer(f, s.span));
            }
            StmtKind::Push { value, .. } => {
                m.k(Frame::Pushed(s));
                m.job(Job::Expr(value));
            }
            StmtKind::Return(_) => unreachable!("an export is not a binding"),
        }
    }

    /// The binding `s` of a value of `v`.
    fn bind(&mut self, s: &'a Stmt, v: Ty) {
        let StmtKind::Bind { targets, value, .. } = &s.kind else {
            unreachable!("a binding")
        };
        match &targets[..] {
            [Target::Name(n, _)] => {
                let id = self.id(s.span, n);
                self.origin(id, value.span, Why::Defined(v.clone()), Some(value.span));
                self.alias.insert(id, value.span);
                self.facts.insert(id, value);
                self.narrowed_at(id, value);
                self.arms.bind(id, plain(&v));
                self.env.insert(id, v);
            }
            [Target::Wild] => {
                let dropped = self.unnamed_in(&v, value.span);
                self.discard(dropped, value, None, s.span)
            }
            _ => {
                let n = targets.len();
                // The atoms of the whole value reach every component, so they are
                // dropped only when no target names them.
                if targets.iter().all(|t| *t == Target::Wild) {
                    let dropped = self.unnamed_in(&v, value.span);
                    self.discard(dropped, value, None, s.span);
                }
                let items = match &value.kind {
                    ExprKind::Tuple(items) if items.len() == n => Some(items),
                    _ => None,
                };
                for (i, target) in targets.iter().enumerate() {
                    let c = self.component(&v, i, n, value.span);
                    match target {
                        Target::Name(name, _) => {
                            let id = self.id(s.span, name);
                            let why = Why::Component(i, c.clone());
                            self.origin(id, value.span, why, Some(value.span));
                            self.env.insert(id, c);
                        }
                        Target::Wild => {
                            let own = v
                                .tuples
                                .iter()
                                .filter(|cs| cs.len() == n)
                                .fold(Ty::empty(), |a, cs| a.union(&cs[i]));
                            // A component of a value that is not a tuple display is
                            // followed no further: each of its loose atoms is unnamed.
                            let (dropped, part) = match items {
                                Some(items) => (self.unnamed_in(&own, items[i].span), &items[i]),
                                None => (own.loose(), value),
                            };
                            self.discard(dropped, part, Some(i), s.span);
                        }
                    }
                }
            }
        }
    }

    /// The signature of a declared function. A parameter with neither a type nor a closed
    /// default gets a class, which its uses narrow, the body checked once. When the function
    /// ends, each class of its level takes its type; a class merged with one of a function
    /// around it waits for that function.
    fn infer(&mut self, m: &mut M<'a>, f: &'a Function, span: Span) {
        let params: Vec<SParam> = f
            .params
            .iter()
            .enumerate()
            .map(|(i, p)| SParam {
                name: p.name.as_str().into(),
                positional: p.positional,
                default: p.default.as_ref().map(|d| {
                    let closed = self.t.uses_in(d.span, &[]).is_empty();
                    (self.id(span, &f.name), i, closed)
                }),
            })
            .collect();
        let ids: Vec<usize> = f.params.iter().map(|p| self.id(p.span, &p.name)).collect();
        let s = InferF {
            f,
            params,
            ids,
            given: Vec::new(),
            level: 0,
            tys: Vec::new(),
            i: 0,
            waiting: None,
            closed: false,
        };
        self.infer_given(m, Box::new(s));
    }

    /// The type each parameter's annotation or closed default gives it, in turn; then the
    /// parameters bound.
    fn infer_given(&mut self, m: &mut M<'a>, mut s: Box<InferF<'a>>) {
        if s.closed {
            s.closed = false;
            let t = m.take_ty();
            let mut out = Ty::empty();
            for piece in t.pieces() {
                out = out.union(&match piece.carrier() {
                    Some(c) => Ty::carrier(c),
                    None => piece.ty(),
                });
            }
            s.given.push(Some(out));
        }
        while let Some(p) = s.f.params.get(s.given.len()) {
            if let Some(t) = &p.ty {
                s.given.push(Some(denoted(t)));
                continue;
            }
            let Some(d) = p.default.as_ref() else {
                s.given.push(None);
                continue;
            };
            if !self.t.uses_in(d.span, &[]).is_empty() {
                s.given.push(None);
                continue;
            }
            s.closed = true;
            m.k(Frame::InferGiven(s));
            return m.job(Job::Expr(d));
        }
        let f = s.f;
        if let Some(ports) = &f.ports {
            for p in ports {
                let id = self.id(p.span, &p.name);
                if matches!(&p.ty.kind, TypeKind::Name(n) if n == "Lines") {
                    self.lines_out.insert(p.name.clone());
                }
                self.origin(id, p.span, Why::Port, None);
                self.env.insert(id, Ty::dynamic());
            }
        }
        self.level += 1;
        s.level = self.level;
        if self.pending.len() <= s.level {
            self.pending.push(Vec::new());
        }
        let given = std::mem::take(&mut s.given);
        for ((id, p), g) in s.ids.iter().zip(&f.params).zip(given) {
            let (t, why) = match (&p.ty, g) {
                (Some(a), Some(t)) if t == Ty::dynamic() => (t, Why::Untracked(a)),
                (Some(a), Some(t)) => {
                    let masks = self.masks(&t);
                    (t.clone(), Why::Typed(a, t, masks))
                }
                (None, Some(t)) => (t.clone(), Why::Default(t)),
                (_, None) => {
                    let k = self.class();
                    (Ty::var(format!("${k}").into()), Why::Untyped(k))
                }
            };
            self.origin(*id, p.span, why, None);
            let bound = match p.ty.is_none() && t.as_var().is_some() {
                true => self.param_ty(*id, t.clone()),
                false => t.clone(),
            };
            self.bind_param(*id, &t, &bound, f.body.span);
            self.env.insert(*id, bound);
            s.tys.push(t);
        }
        s.i = 0;
        self.infer_defaults(m, s);
    }

    /// A default that reads the other parameters, at its parameter's type, each in turn;
    /// then the body.
    fn infer_defaults(&mut self, m: &mut M<'a>, mut s: Box<InferF<'a>>) {
        if let Some(class) = s.waiting.take() {
            let dt = m.take_ty();
            let p = &s.f.params[s.i];
            let t = &s.tys[s.i];
            let d = p.default.as_ref().expect("a default");
            let what = format!("the default of `{}`", p.name);
            match class {
                Some(k) => {
                    if !self.flow(k, &dt, &what, d.span) {
                        let shown = self.show(t);
                        let mut notes = self.derive(&[d.span]);
                        notes.extend(self.reasons(t));
                        let dt = self.text(&dt);
                        self.error_with(d.span, format!("{what} is {dt}, not {shown}"), notes);
                    }
                }
                None => {
                    if !self.subtype(&dt, t) {
                        let why = dt.refused(t);
                        let (dt, t) = (self.text(&dt), self.text(t));
                        self.error(d.span, format!("{what} is {dt}, not {t}{why}"));
                    }
                }
            }
            s.i += 1;
        }
        while let Some(p) = s.f.params.get(s.i) {
            let Some(d) = &p.default else {
                s.i += 1;
                continue;
            };
            // A closed default of an undeclared parameter gave the parameter its type; one of
            // a declared parameter is checked at that type, as `scale: f64 = 2` is rejected.
            if p.ty.is_none() && self.t.uses_in(d.span, &[]).is_empty() {
                s.i += 1;
                continue;
            }
            let class = self.class_of_ty(&s.tys[s.i]);
            let job = match class {
                Some(_) => Job::Expr(d),
                None => Job::At(d, Want::of(&s.tys[s.i])),
            };
            s.waiting = Some(class);
            m.k(Frame::InferDefaults(s));
            return m.job(job);
        }
        let f = s.f;
        m.k(Frame::InferEnd(s));
        match &f.body.kind {
            ExprKind::Block(stmts) if !f.equation => m.job(Job::Scope(stmts, false)),
            _ => m.job(Job::Expr(&f.body)),
        }
    }

    /// An argument: a numeric literal kept unadopted, a function in a slot of function type
    /// fitted to it, else the expression's type.
    fn arg(&mut self, m: &mut M<'a>, e: &'a Expr, want: Want) {
        if let Some(l) = literal(e) {
            m.ret = Ret::Arg(Arg {
                ty: lit_ty(&l.value, l.neg()),
                lit: Some(l),
                at: Some(e.span),
                parts: None,
            });
            return;
        }
        m.k(Frame::ArgOf(e));
        m.job(Job::At(e, want));
    }

    /// `e`'s type where `want` is wanted: a lambda or a declared function in a slot of one
    /// function type is fitted to it, and a generic literal takes its one numeric carrier,
    /// where a plain literal of another carrier is rejected.
    fn expr_at(&mut self, m: &mut M<'a>, e: &'a Expr, want: Want) {
        if let Some(sig) = want.fun {
            if let ExprKind::Lambda { params, body } = &e.kind {
                return self.fit_lambda(m, params, body, sig, e.span);
            }
            if let Some(id) = self.declared(e) {
                let t = self.fit_declared(id, &sig, e.span);
                return m.ty(t);
            }
        }
        if let (Some(l), Some(c)) = (literal(e), want.num) {
            let from = self.info.errors.len();
            let t = self.adopt_to(&l, c);
            // A rejected literal is its own error: read at the carrier wanted, it causes no
            // second one where its type is checked.
            let t = match self.info.errors.len() > from {
                true => Ty::carrier(c),
                false => t,
            };
            return m.ty(t);
        }
        m.job(Job::Expr(e));
    }

    fn expr_of(&mut self, m: &mut M<'a>, e: &'a Expr) {
        match read_literal(e) {
            Ok(Some(l)) => {
                let t = match self.info.adopt.get(&l.span) {
                    Some(v) => lit_ty(v, l.neg()),
                    None => lit_ty(&l.value, l.neg()),
                };
                return m.ty(t);
            }
            Ok(None) => {}
            // A refused `-k` is walked on, and its literal `k` reports the refusal, once.
            Err(_) if matches!(e.kind, ExprKind::Unary(..)) => {}
            Err(r) => {
                self.error(e.span, unread_literal(&r));
                return m.ty(Ty::empty());
            }
        }
        match &e.kind {
            ExprKind::Record(_)
            | ExprKind::With { .. }
            | ExprKind::This
            | ExprKind::Match { .. } => {
                unreachable!("resolve rejects the forms of layer L2")
            }
            ExprKind::Range(..)
            | ExprKind::In { .. }
            | ExprKind::Reduce { .. }
            | ExprKind::Read { .. }
            | ExprKind::Section(_)
            | ExprKind::Array(_)
            | ExprKind::Set(_)
            | ExprKind::Map(_)
            | ExprKind::For { .. } => unreachable!("resolve rejects the forms of layer L3"),
            ExprKind::SortKey { .. } => unreachable!("resolve rejects the forms of layer L5"),
            ExprKind::Loop { .. } | ExprKind::Break(_) | ExprKind::Spread { .. } => {
                unreachable!("resolve rejects the forms of layer L6")
            }
            // A `rat` literal is decorated and keeps its carrier.
            ExprKind::Rat(s) => match Rat::decimal(s) {
                Ok(r) => m.ty(Ty::lit(&Value::rat(
                    r.expect("the lexer's rat text is a decimal"),
                ))),
                Err(r) => {
                    self.error(e.span, unread_literal(&r));
                    m.ty(Ty::empty())
                }
            },
            ExprKind::Int { .. } | ExprKind::Float(_) => m.ty(Ty::empty()),
            ExprKind::Bool(b) => m.ty(Ty::lit(&Value::Bool(*b))),
            ExprKind::Atom(a) => m.ty(Ty::set(KType::atom(a))),
            ExprKind::Str(parts) => {
                let s = StrF {
                    parts,
                    i: 0,
                    text: String::new(),
                    holes: Vec::new(),
                    hole: None,
                };
                self.str_step(m, Box::new(s));
            }
            ExprKind::Name(_) => {
                let t = self.name(e.span);
                m.ty(t);
            }
            ExprKind::Unary(op, a) => {
                m.k(Frame::Unary(op, e.span));
                m.job(Job::Arg(a, Want::default()));
            }
            ExprKind::Binary(op @ ("&&" | "||"), a, b) => {
                m.k(Frame::Logic1 {
                    op,
                    b,
                    span: e.span,
                });
                m.job(Job::Cond(a));
            }
            ExprKind::Binary(op, a, b) => {
                m.k(Frame::Bin1 {
                    op,
                    b,
                    span: e.span,
                });
                m.job(Job::Arg(a, Want::default()));
            }
            ExprKind::Call {
                callee,
                positional,
                named,
                curry,
            } => self.call(m, callee, positional, named, *curry, e.span),
            ExprKind::Index(of, k) => self.index(m, of, k, e.span),
            ExprKind::Tuple(items) => {
                let s = TupleF {
                    es: items,
                    started: 0,
                    out: Vec::new(),
                    data: true,
                };
                self.tuple_step(m, Box::new(s));
            }
            ExprKind::Lambda { params, body } => self.lambda(m, params, body),
            ExprKind::Is { of, .. } => {
                m.k(Frame::Const(Ty::carrier(Carrier::Bool)));
                m.job(Job::Expr(of));
            }
            ExprKind::Else { of, .. } => {
                m.k(Frame::Else1(e));
                m.job(Job::Expr(of));
            }
            ExprKind::Block(stmts) => m.job(Job::Scope(stmts, false)),
            ExprKind::If { cond, .. } => {
                m.k(Frame::If1(e));
                m.job(Job::Cond(cond));
            }
            ExprKind::Member { of, name, safe } => {
                let s = MemberF {
                    of,
                    name,
                    safe: *safe,
                    member: e.span,
                    positional: &[],
                    named: &[],
                    curry: false,
                    span: e.span,
                };
                self.member(m, of, s);
            }
        }
    }

    fn str_step(&mut self, m: &mut M<'a>, mut s: Box<StrF<'a>>) {
        if let Some(h) = s.hole.take() {
            let t = m.take_ty();
            self.data(&t, "interpolation", h.span, h.span);
            s.holes.push(t);
        }
        while let Some(p) = s.parts.get(s.i) {
            s.i += 1;
            match p {
                StrPart::Text(t) => s.text.push_str(t),
                StrPart::Hole(h) => {
                    s.hole = Some(h);
                    m.k(Frame::Str(s));
                    return m.job(Job::Expr(h));
                }
            }
        }
        if s.holes.is_empty() {
            return m.ty(Ty::lit(&Value::str(&s.text)));
        }
        let mut out = Ty::carrier(Carrier::Str);
        passed(&mut out, s.holes.iter());
        m.ty(out);
    }

    fn tuple_step(&mut self, m: &mut M<'a>, mut s: Box<TupleF<'a>>) {
        if s.started > s.out.len() {
            let t = m.take_ty();
            // A tuple written as a component has checked its own components, so it is data
            // where they are; checking it again would walk each nested tuple once per level.
            let e = &s.es[s.out.len()];
            if s.data && !matches!(e.kind, ExprKind::Tuple(_)) {
                self.data(&t, "a tuple", e.span, e.span);
            }
            s.out.push(t);
        }
        if let Some(e) = s.es.get(s.started) {
            s.started += 1;
            m.k(Frame::Tuple(s));
            return m.job(Job::Expr(e));
        }
        let cs = std::mem::take(&mut s.out);
        m.ty(Ty::of_row(match s.data {
            true => ty::Row::of_data(cs),
            false => ty::Row::new(cs),
        }));
    }

    /// A condition's type and the facts it makes when it holds and when it does not.
    fn cond(&mut self, m: &mut M<'a>, e: &'a Expr) {
        match &e.kind {
            ExprKind::Is { of, .. } => {
                m.k(Frame::CondIs(e));
                m.job(Job::Expr(of));
            }
            ExprKind::Unary("!", a) => {
                m.k(Frame::CondNot(e.span));
                m.job(Job::Cond(a));
            }
            ExprKind::Binary(op @ ("&&" | "||"), a, b) => {
                m.k(Frame::CondAnd1 {
                    op,
                    b,
                    span: e.span,
                });
                m.job(Job::Cond(a));
            }
            _ => {
                m.k(Frame::CondOf(e));
                m.job(Job::Expr(e));
            }
        }
    }

    /// The type of an `if` whose branches `then` and `otherwise` have the types `a` and `b`:
    /// their union; but where one branch is a literal `kn`, or of a class of generic literals
    /// only, as `1n + 1n` is, and the other's type is one class, the literal joins the class,
    /// generic, or the classes merge, and the `if` has the class's type (L1.26a).
    fn branches(&mut self, then: &Expr, a: &Ty, otherwise: &Expr, b: &Ty) -> Ty {
        for (e, t, other) in [(then, a, b), (otherwise, b, a)] {
            let Some(k) = self.class_of_ty(other) else {
                continue;
            };
            let joined = match self.class_of_ty(t) {
                Some(g) if self.classes[g].generic => self.merge(k, g, "an `if`", e.span),
                Some(_) => false,
                None => literal(exported(e))
                    .filter(|l| l.n)
                    .is_some_and(|l| self.join(k, &l.joining(), false)),
            };
            if joined {
                return other.clone();
            }
        }
        a.union(b)
    }

    /// A binary operator other than `&&` and `||` applied to its arguments `x` and `y`, the
    /// second written `b`.
    fn binary_end(
        &mut self,
        op: &'static str,
        mut x: Arg,
        mut y: Arg,
        b: &'a Expr,
        span: Span,
    ) -> Ty {
        // A `kn` operand is generic: it takes the carrier of the other operand, at run time
        // where that is a type variable (step L1.26a). Under `==` it follows as any literal.
        if !matches!(op, "==" | "!=") {
            for l in [&mut x.lit, &mut y.lit].into_iter().flatten() {
                l.generic = l.n;
            }
            // Two generic operands, as in `1n + 1n`, make a class of their own inside a
            // function: generic, it takes the carrier of what it meets, the first operand
            // taking it from a parameter of the class and the second following the first; it
            // takes int where it meets no carrier.
            if self.level > 0
                && let (Some(a), Some(b)) = (&x.lit, &y.lit)
                && a.n
                && b.n
            {
                let k = self.generic_class(a);
                x = Arg {
                    ty: Ty::var(format!("${k}").into()),
                    lit: None,
                    ..x
                };
            }
        }
        match op {
            "==" | "!=" => {
                self.data(&x.ty, &format!("`{op}`"), span, x.at.unwrap_or(span));
                self.data(&y.ty, &format!("`{op}`"), span, y.at.unwrap_or(span));
                self.equal(&x, &y);
                Ty::carrier(Carrier::Bool)
            }
            "<" | "<=" | ">" | ">=" => self.compare(op, x, y, span),
            _ => {
                // A divisor whose type holds no zero cannot fail with `#divByZero`.
                let nonzero = matches!(op, "/" | "div" | "mod")
                    && !y.ty.contains(&Value::Int(0))
                    && !y.ty.contains(&Value::rat(Rat::int(0.into())));
                let carried = [&x.ty, &y.ty]
                    .iter()
                    .any(|t| t.atoms().contains(&Value::atom("divByZero")));
                if op == "**" {
                    self.exponent(&x, &y, b, span);
                }
                let sig = op_sig(op);
                let r = self.apply(&format!("`{op}`"), &sig, vec![Some(x), Some(y)], true, span);
                if op == "*" {
                    // `*` and `/` take the same (f64, f64) and (rat, rat), and only `*` takes
                    // (int, int): `/` is defined where the product holds no `int`.
                    let quotient = !r.0.set.is_empty() && (&r.0.set & &KType::int()).is_empty();
                    *self.info.quotients.entry(span).or_insert(quotient) &= quotient;
                }
                match nonzero && !carried {
                    true => r.0.diff(&Ty::set(KType::atom("divByZero"))),
                    false => r.0,
                }
            }
        }
    }

    fn call(
        &mut self,
        m: &mut M<'a>,
        callee: &'a Expr,
        positional: &'a [Expr],
        named: &'a [(String, Expr)],
        curry: bool,
        span: Span,
    ) {
        if let ExprKind::Member { of, name, safe } = &callee.kind {
            let s = MemberF {
                of,
                name,
                safe: *safe,
                member: callee.span,
                positional,
                named,
                curry,
                span,
            };
            return self.member(m, of, s);
        }
        if let ExprKind::Atom(name) = &callee.kind {
            let s = AtomF {
                name,
                positional,
                named,
                started: 0,
                items: Vec::new(),
                fields: BTreeMap::new(),
            };
            return self.atom_step(m, Box::new(s));
        }
        if let Some(id) = self.declared(callee) {
            let sig = match self.env.get(&id) {
                Some(t) => only_fn(t),
                None => None,
            };
            let Some(sig) = sig else {
                return m.ty(Ty::dynamic());
            };
            let from = self.info.errors.len();
            m.k(Frame::CallAlso {
                id,
                from,
                sig: sig.clone(),
            });
            let what: Rc<str> = self.t.funcs[&id].name.as_str().into();
            let args = Args::of(positional, named);
            return self.call_sig(m, sig, true, None, args, curry, span, what);
        }
        m.k(Frame::Callee {
            callee,
            positional,
            named,
            curry,
            span,
        });
        m.job(Job::Expr(callee));
    }

    /// An atom with a payload: its items, then its fields; `s.started` arguments started.
    fn atom_step(&mut self, m: &mut M<'a>, mut s: Box<AtomF<'a>>) {
        if let Some(k) = s.started.checked_sub(1) {
            let t = m.take_ty();
            match k.checked_sub(s.positional.len()) {
                None => s.items.push(t),
                Some(i) => {
                    s.fields.insert(Arc::from(s.named[i].0.as_str()), t);
                }
            }
        }
        let (k, positional, named) = (s.started, s.positional, s.named);
        let next = match positional.get(k) {
            Some(e) => Some(e),
            None => named.get(k - positional.len()).map(|(_, e)| e),
        };
        if let Some(e) = next {
            s.started += 1;
            m.k(Frame::AtomArgs(s));
            return m.job(Job::Expr(e));
        }
        let AtomF {
            name,
            items,
            fields,
            ..
        } = *s;
        let mut t = Ty::set(KType::atom_with(name, &KType::top()));
        t.payloads
            .insert(name.into(), Some(vec![Shape::new(items, fields)]));
        m.ty(t);
    }

    /// A prelude word applied to one argument, the receiver or the only positional one.
    fn word(
        &mut self,
        m: &mut M<'a>,
        w: &'a str,
        positional: &'a [Expr],
        receiver: Option<Arg>,
        span: Span,
    ) {
        match receiver {
            Some(x) => {
                let t = self.word_end(w, x, span);
                m.ty(t);
            }
            None => {
                m.k(Frame::Word(w, span));
                m.job(Job::Arg(&positional[0], Want::default()));
            }
        }
    }

    fn word_end(&mut self, w: &str, x: Arg, span: Span) -> Ty {
        if w == "sum" {
            return self.sum(x, span);
        }
        if w == "String" {
            self.data(&x.ty, "`String`", span, x.at.unwrap_or(span));
        }
        let sig = word_sig(w);
        self.apply(&format!("`{w}`"), &sig, vec![Some(x)], true, span)
            .0
    }

    /// A call of the bit word `w`, the primitive `p` (step L1.39a): its arguments placed by
    /// the word's parameters, every one positional but `width`, then each operand checked
    /// against its domain, and the call applied with atoms passing. The signature is recorded
    /// at the call, so elaboration places named arguments and reports a call that does not fit
    /// it.
    #[allow(clippy::too_many_arguments)]
    fn bits(
        &mut self,
        m: &mut M<'a>,
        w: &'a str,
        p: Prim,
        receiver: Option<(Arg, &'a Expr)>,
        positional: &'a [Expr],
        named: &'a [(String, Expr)],
        curry: bool,
        span: Span,
    ) {
        let sig = bit_sig(p);
        self.put(Undo::Call(span, Some(sig.clone())));
        if curry {
            let args = Args::of(positional, named);
            return self.call_sig(
                m,
                sig,
                true,
                receiver.map(|r| r.0),
                args,
                true,
                span,
                w.into(),
            );
        }
        let mut slots = vec![None; sig.params.len()];
        let first = usize::from(receiver.is_some());
        if let Some(r) = receiver {
            slots[0] = Some(r);
        }
        let s = BitsF {
            w,
            p,
            sig,
            positional,
            named,
            span,
            slots,
            fits: true,
            started: 0,
            first,
        };
        self.bits_step(m, Box::new(s));
    }

    /// The arguments of a bit word's call, positional then named, each checked at its
    /// parameter's type and placed; then the domains and the application.
    fn bits_step(&mut self, m: &mut M<'a>, mut s: Box<BitsF<'a>>) {
        let npos = s.positional.len();
        // Argument `k`: its expression and the parameter it names or falls to, if any.
        let nth = |s: &BitsF<'a>, k: usize| -> (&'a Expr, Option<usize>) {
            match k.checked_sub(npos) {
                None => (&s.positional[k], Some(s.first + k)),
                Some(i) => {
                    let (name, e) = &s.named[i];
                    (e, s.sig.params.iter().position(|q| *q.name == **name))
                }
            }
        };
        if let Some(k) = s.started.checked_sub(1) {
            let a = m.take_arg();
            let (e, j) = nth(&s, k);
            let free = |q: &SParam, positional: bool| q.positional == positional;
            match j.filter(|&j| j < s.slots.len()) {
                Some(j) if k < npos && free(&s.sig.params[j], true) => s.slots[j] = Some((a, e)),
                Some(j) if k >= npos && free(&s.sig.params[j], false) && s.slots[j].is_none() => {
                    s.slots[j] = Some((a, e))
                }
                _ => s.fits = false,
            }
        }
        if s.started < npos + s.named.len() {
            let (e, j) = nth(&s, s.started);
            let want = match j.and_then(|j| s.sig.arrows[0].params.get(j)) {
                Some(t) => Want::of(t),
                None => Want::default(),
            };
            s.started += 1;
            m.k(Frame::Bits(s));
            return m.job(Job::Arg(e, want));
        }
        let BitsF {
            w,
            p,
            sig,
            span,
            slots,
            fits,
            ..
        } = *s;
        let Some(slots) = slots
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .filter(|_| fits)
        else {
            // Elaboration reports the call against the recorded signature.
            return m.ty(Ty::empty());
        };
        self.bit_domains(w, p, &slots, span);
        let args = slots.into_iter().map(|(a, _)| Some(a)).collect();
        let t = self.apply(&format!("`{w}`"), &sig, args, true, span).0;
        m.ty(t);
    }

    /// A call through a value: each function its type holds, applied; an atom passes.
    #[allow(clippy::too_many_arguments)]
    fn call_value(
        &mut self,
        m: &mut M<'a>,
        f: &Ty,
        what: Rc<str>,
        receiver: Option<Arg>,
        args: Rc<Args<'a>>,
        curry: bool,
        span: Span,
    ) {
        let out = self.passing(f, "a call", span);
        let mut pieces = f.pieces();
        // A class's calls are recorded with the arguments' types, found once.
        let class = pieces.iter().any(|p| self.class_of(p).is_some());
        let call = match f.fns.first() {
            Some(s) if f.fns.iter().all(|g| g.same_kinds(s)) => Some(s.clone()),
            _ => None,
        };
        pieces.reverse();
        let s = CallValueF {
            what,
            receiver,
            args,
            curry,
            span,
            out,
            checked: false,
            pieces,
            call,
            found: class.then(|| (Args::default(), 0)),
            waiting: false,
        };
        self.call_value_step(m, Box::new(s));
    }

    fn call_value_step(&mut self, m: &mut M<'a>, mut s: Box<CallValueF<'a>>) {
        if let Some((mut got, mut k)) = s.found.take() {
            if s.waiting {
                s.waiting = false;
                let x = ArgSrc::Got(Box::new(m.take_arg()));
                got.push_as(&s.args, k, x);
                k += 1;
            }
            while k < s.args.len() {
                let x = match s.args.nth(k) {
                    ArgSrc::Expr(e) => {
                        let e = *e;
                        s.found = Some((got, k));
                        s.waiting = true;
                        m.k(Frame::CallValue(s));
                        return m.job(Job::Arg(e, Want::default()));
                    }
                    ArgSrc::Got(x) => ArgSrc::Got(x.clone()),
                };
                got.push_as(&s.args, k, x);
                k += 1;
            }
            s.args = Rc::new(got);
        }
        if let Some(c) = s.call.take() {
            self.put(Undo::Call(s.span, Some(c)));
        }
        if s.waiting {
            s.waiting = false;
            let r = m.take_ty();
            s.out = s.out.union(&r);
        }
        let (span, curry) = (s.span, s.curry);
        while let Some(p) = s.pieces.pop() {
            match p {
                Piece::Fn(sig) => {
                    s.checked = true;
                    s.waiting = true;
                    let (receiver, args, what) =
                        (s.receiver.clone(), s.args.clone(), s.what.clone());
                    m.k(Frame::CallValue(s));
                    return self.call_sig(m, sig, false, receiver, args, curry, span, what);
                }
                Piece::Var(_) if let Some(k) = self.class_of(&p) => {
                    s.checked = true;
                    // No application, so no trial: the atoms from outside are unknown.
                    self.tried_at(span, None);
                    let ty_of = |a: &ArgSrc| match a {
                        ArgSrc::Got(x) => x.ty.clone(),
                        ArgSrc::Expr(_) => unreachable!("found above"),
                    };
                    let kind = NeedKind::Call {
                        what: s.what.as_ref().into(),
                        positional: s
                            .receiver
                            .iter()
                            .map(|x| x.ty.clone())
                            .chain(s.args.positional.iter().map(ty_of))
                            .collect(),
                        named: s
                            .args
                            .named
                            .iter()
                            .map(|(m, a)| (m.as_str().into(), ty_of(a)))
                            .collect(),
                        curry,
                    };
                    let r = self.need(k, kind, true, span);
                    s.out = s.out.union(&r);
                }
                Piece::Dyn => {
                    self.tried_at(span, None);
                    self.any(&format!("a call of `{}`", s.what), span);
                }
                Piece::Var(_) => {
                    self.tried_at(span, None);
                    s.out = s.out.union(&Ty::dynamic());
                }
                p if p.is_atoms() => {}
                p => {
                    let shown = self.text(&p.ty());
                    self.error(span, format!("`{}` is {shown}, not a function", s.what));
                }
            }
        }
        let out = std::mem::replace(&mut s.out, Ty::empty());
        if s.checked {
            return m.ty(out);
        }
        m.k(Frame::Const(out));
        m.each(s.args.exprs());
    }

    /// A call of a function of signature `sig`; `declared` when it is the declared function
    /// itself, whose defaults every call can fill, and not a value of its type, which fills
    /// only closed ones. A call whose arguments do not fit gives the unknown; elaboration
    /// reports it when the call is of the declared function or of one recorded signature, and
    /// this check otherwise.
    #[allow(clippy::too_many_arguments)]
    fn call_sig(
        &mut self,
        m: &mut M<'a>,
        sig: Arc<Sig>,
        declared: bool,
        receiver: Option<Arg>,
        args: Rc<Args<'a>>,
        curry: bool,
        span: Span,
        what: Rc<str>,
    ) {
        let sig = self.open(&sig);
        let n = sig.params.len();
        let mut slots: Vec<Option<At>> = vec![None; n];
        let mut next = 0;
        let has_receiver = receiver.is_some();
        if has_receiver {
            if n == 0 {
                let misfits = vec![(span, Misfit::NoReceiver)];
                return self.unfit(m, &sig, declared, &args, span, &what, misfits);
            }
            next = 1;
        }
        for i in 0..args.positional.len() {
            let misfit = match sig.params.get(next) {
                Some(p) if p.positional || !declared && sig.params.iter().all(|p| p.positional) => {
                    slots[next] = Some(At::Pos(i));
                    next += 1;
                    continue;
                }
                Some(p) => Misfit::Named(&p.name),
                None => Misfit::TooMany(n),
            };
            let misfits = vec![(args.span_at(At::Pos(i), span), misfit)];
            return self.unfit(m, &sig, declared, &args, span, &what, misfits);
        }
        // Each parameter's index by name, the first where a name repeats.
        let at: HashMap<&str, usize> = sig
            .params
            .iter()
            .enumerate()
            .rev()
            .map(|(j, p)| (&*p.name, j))
            .collect();
        for (i, (name, _)) in args.named.iter().enumerate() {
            let misfit = match at.get(&**name).copied() {
                None => Misfit::NoParam(name),
                Some(j) if sig.params[j].positional => Misfit::Positional(name),
                Some(j) if slots[j].is_some() || has_receiver && j == 0 => Misfit::Supplied(name),
                Some(j) => {
                    slots[j] = Some(At::Named(i));
                    continue;
                }
            };
            let misfits = vec![(args.span_at(At::Named(i), span), misfit)];
            return self.unfit(m, &sig, declared, &args, span, &what, misfits);
        }
        let missing: Vec<usize> = (0..n)
            .filter(|&j| slots[j].is_none() && !(has_receiver && j == 0))
            .collect();
        // As elaboration finds them: for `...`, the first positional parameter left out, or
        // that none is; for a declared function, each parameter left out with no default;
        // through a value, the first left out with no default it can fill.
        let misfits: Vec<(Span, Misfit)> = match curry {
            true => match missing.iter().find(|&&j| sig.params[j].positional) {
                Some(&j) => vec![(span, Misfit::CurriedPositional(&sig.params[j].name))],
                None if missing.is_empty() => vec![(span, Misfit::NothingLeftOut)],
                None => Vec::new(),
            },
            false if declared => (missing.iter())
                .filter(|&&j| sig.params[j].default.is_none())
                .map(|&j| (span, Misfit::Missing(&sig.params[j].name)))
                .collect(),
            false => (missing.iter())
                .find_map(|&j| {
                    let p = &sig.params[j];
                    match p.default {
                        Some((_, _, true)) => None,
                        Some((_, _, false)) => Some((span, Misfit::OpenDefault(&p.name))),
                        None => Some((span, Misfit::Missing(&p.name))),
                    }
                })
                .into_iter()
                .collect(),
        };
        if !misfits.is_empty() {
            return self.unfit(m, &sig, declared, &args, span, &what, misfits);
        }
        drop(at);
        let s = CallSigF {
            sig,
            receiver,
            args,
            slots,
            got: Vec::new(),
            missing,
            curry,
            span,
            what,
            waiting: false,
        };
        self.call_sig_step(m, Box::new(s));
    }

    /// The arguments of a call that fits, each at the parameter types of its slot; then the
    /// application.
    fn call_sig_step(&mut self, m: &mut M<'a>, mut s: Box<CallSigF<'a>>) {
        if s.waiting {
            s.waiting = false;
            let x = m.take_arg();
            s.got.push(Some(x));
        }
        while let Some(slot) = s.slots.get(s.got.len()).copied() {
            let j = s.got.len();
            let a = match slot {
                _ if j == 0 && s.receiver.is_some() => s.receiver.take(),
                Some(at) => match s.args.get(at) {
                    ArgSrc::Expr(e) => {
                        let e = *e;
                        let want = Ty::union_all(s.sig.arrows.iter().map(|ar| &ar.params[j]));
                        s.waiting = true;
                        m.k(Frame::CallSig(s));
                        return m.job(Job::Arg(e, Want::of(&want)));
                    }
                    ArgSrc::Got(x) => Some(Arg::clone(x)),
                },
                None => None,
            };
            s.got.push(a);
        }
        let args = std::mem::take(&mut s.got);
        let t = match s.curry {
            true => self.partial(&s.sig, args, &s.missing, false, &s.what, s.span),
            false => {
                let what = format!("`{}`", s.what);
                // Inside a function with a widened parameter, each call records the atoms it
                // gives from outside: its own when no argument holds a loose atom, else those
                // of a trial.
                let from_outside = !self.trying && self.replaying == 0 && !self.widened.is_empty();
                let with = from_outside.then(|| self.outside_args(&args)).flatten();
                let t = self.apply(&what, &s.sig, args, false, s.span).0;
                match with {
                    Some(with) => self.try_outside(&what, &s.sig, with, s.span),
                    None if from_outside => self.tried_at(s.span, Some(t.loose())),
                    None => {}
                }
                t
            }
        };
        m.ty(t);
    }

    /// A call whose arguments do not fit `sig`, for the reasons `misfits`. For the declared
    /// function and a call through a value with a recorded signature, which elaboration
    /// fills by the same rules, the errors of `misfits`, worded as elaboration words them,
    /// and the empty type; otherwise the unknown, with one error naming the signature.
    #[allow(clippy::too_many_arguments)]
    fn unfit(
        &mut self,
        m: &mut M<'a>,
        sig: &Sig,
        declared: bool,
        args: &Args<'a>,
        span: Span,
        what: &str,
        misfits: Vec<(Span, Misfit)>,
    ) {
        let found = args.all().any(|a| matches!(a, ArgSrc::Got(_)));
        if declared || !found && self.info.calls.contains_key(&span) {
            let who = match declared {
                true => what.to_string(),
                false => self.info.calls[&span].to_string(),
            };
            for (at, misfit) in misfits {
                let message = misfit.message(&who);
                let menu = misfit
                    .menu()
                    .into_iter()
                    .map(|text| Note { span: at, text });
                match misfit.row() {
                    Some(row) => self.rejects_with(row, at, message, menu.collect()),
                    None => self.error_with(at, message, Vec::new()),
                }
            }
            return m.ty(Ty::empty());
        }
        let message = format!(
            "`{what}` does not take these arguments: it is `{}`",
            self.sig_text(sig)
        );
        m.k(Frame::Fail(Some((span, message))));
        m.each(args.exprs());
    }

    /// `x.f(args)` and `x?.f(args)`: the call `f(x, args)`; `?.` passes `x`'s atoms around it.
    fn member(&mut self, m: &mut M<'a>, of: &'a Expr, s: MemberF<'a>) {
        m.k(Frame::Member1(Box::new(s)));
        m.job(Job::Arg(of, Want::default()));
    }

    fn member_end(&mut self, m: &mut M<'a>, s: MemberF<'a>, mut x: Arg) {
        let MemberF {
            of,
            name,
            safe,
            member,
            positional,
            named,
            curry,
            span,
        } = s;
        if safe {
            let atoms = x.ty.loose_ty();
            x = Arg::of(x.ty.without_loose());
            m.k(Frame::Member2(atoms));
        }
        match self.t.res.uses.get(&member) {
            Some(Ref::Bound(ids)) if ids.len() == 1 => {
                let id = ids[0];
                let f = self.env.get(&id).cloned().unwrap_or_else(Ty::dynamic);
                let args = Args::of(positional, named);
                if self.t.funcs.contains_key(&id) {
                    match only_fn(&f) {
                        Some(sig) => {
                            self.call_sig(m, sig, true, Some(x), args, curry, span, name.into())
                        }
                        None => m.ty(Ty::dynamic()),
                    }
                } else {
                    self.call_value(m, &f, name.into(), Some(x), args, curry, span);
                }
            }
            Some(Ref::Bound(_)) => m.ty(Ty::empty()),
            _ => match zedc_resolve::resolve::prelude_layer(name) {
                Some(1) if let Some(p) = bit_prim(name) => {
                    self.bits(m, name, p, Some((x, of)), positional, named, curry, span)
                }
                Some(1)
                    if positional.is_empty()
                        && named.is_empty()
                        && !curry
                        && word_arity(name) == 1 =>
                {
                    self.word(m, name, &[], Some(x), span)
                }
                Some(1) if word_arity(name) != 1 => {
                    let f = Ty::func(word_sig(name));
                    let args = Args::of(positional, named);
                    self.call_value(m, &f, name.into(), Some(x), args, curry, span);
                }
                _ => m.ty(Ty::dynamic()),
            },
        }
    }

    /// `f[k]` on a declared function is a section; `t[i]` with a literal `i` the tuple's
    /// component; else an application.
    fn index(&mut self, m: &mut M<'a>, of: &'a Expr, k: &'a Expr, span: Span) {
        if let Some(id) = self.declared(of) {
            let Some(sig) = self.env.get(&id).and_then(only_fn) else {
                m.k(Frame::Const(Ty::dynamic()));
                return m.job(Job::Expr(k));
            };
            // Elaboration rejects a section of a function of no parameters.
            if sig.params.is_empty() {
                m.k(Frame::Const(Ty::empty()));
                return m.job(Job::Expr(k));
            }
            let want = Ty::union_all(sig.arrows.iter().map(|a| &a.params[0]));
            let what = self.t.funcs[&id].name.clone();
            m.k(Frame::Section { sig, what, span });
            return m.job(Job::Arg(k, Want::of(&want)));
        }
        m.k(Frame::Index1 { k, span });
        m.job(Job::Expr(of));
    }

    /// A lambda with no expected type: its parameters positional, typed by their
    /// annotations; one without is generic, as a declared function's.
    fn lambda(&mut self, m: &mut M<'a>, params: &'a [Param], body: &'a Expr) {
        let names = params
            .iter()
            .map(|p| SParam {
                name: p.name.as_str().into(),
                positional: true,
                default: None,
            })
            .collect();
        self.lambda_sig(m, params.iter().map(Some), &[], names, body);
    }

    /// The signature of a lambda checked as a declared function's body is: each parameter of
    /// `slots` typed by its annotation, one without a type variable its uses constrain, and a
    /// slot no parameter takes a type variable nothing constrains; each parameter of `extra`
    /// typed by its default; the signature's parameters are `names`. Its function type is the
    /// result of the jobs pushed.
    fn lambda_sig(
        &mut self,
        m: &mut M<'a>,
        slots: impl Iterator<Item = Option<&'a Param>>,
        extra: &[&'a Param],
        names: Vec<SParam>,
        body: &'a Expr,
    ) {
        self.level += 1;
        let level = self.level;
        if self.pending.len() <= level {
            self.pending.push(Vec::new());
        }
        let (mut tys, mut ids) = (Vec::new(), Vec::new());
        for p in slots {
            let declared = p.and_then(|p| p.ty.as_ref());
            let t = match declared {
                Some(t) => denoted(t),
                None => Ty::var(format!("${}", self.class()).into()),
            };
            let id = p.map(|p| self.id(p.span, &p.name));
            if let Some(id) = id {
                let bound = match declared {
                    Some(_) => t.clone(),
                    None => self.param_ty(id, t.clone()),
                };
                self.bind_param(id, &t, &bound, body.span);
                self.env.insert(id, bound);
            }
            ids.push(id);
            tys.push(t);
        }
        m.k(Frame::LambdaEnd {
            names,
            ids,
            level,
            tys,
            body,
        });
        m.job(Job::Body(body, Want::default()));
        // The defaults are checked first, in order, each bound before the next.
        for &p in extra.iter().rev() {
            m.k(Frame::BindDefault(p));
            m.job(Job::Expr(p.default.as_ref().expect("a default")));
        }
    }

    /// A lambda in a slot of the function type `e`: its first parameters take `e`'s
    /// positional ones, in order, and the rest `e`'s named ones by name; a parameter `e`
    /// does not pass needs a default.
    fn fit_lambda(
        &mut self,
        m: &mut M<'a>,
        params: &'a [Param],
        body: &'a Expr,
        e: Arc<Sig>,
        span: Span,
    ) {
        let pos: Vec<usize> = (0..e.params.len())
            .filter(|&j| e.params[j].positional)
            .collect();
        let mut order: Vec<Option<usize>> = vec![None; e.params.len()];
        let mut extra = Vec::new();
        if params.len() < pos.len() {
            let shown = self.sig_text(&e);
            let menu = [format!(
                "repair: a lambda in the form `{shown}` passes, its first {} parameters taken by \
                 position",
                pos.len()
            )];
            self.rejects_offering(
                Row::ParameterKinds,
                span,
                format!(
                    "the lambda takes {} parameter{}, and `{shown}` passes {} by position",
                    params.len(),
                    if params.len() == 1 { "" } else { "s" },
                    pos.len()
                ),
                menu,
            );
            return m.ty(Ty::func(e));
        }
        for (i, p) in params.iter().enumerate() {
            if i < pos.len() {
                order[pos[i]] = Some(i);
                continue;
            }
            match e
                .params
                .iter()
                .position(|q| !q.positional && *q.name == *p.name)
            {
                Some(j) if order[j].is_none() => order[j] = Some(i),
                _ if p.default.is_some() => extra.push(i),
                _ => {
                    let free: Vec<String> = (0..e.params.len())
                        .filter(|&j| !e.params[j].positional && order[j].is_none())
                        .map(|j| format!("`{}`", e.params[j].name))
                        .collect();
                    let fix = match free.first() {
                        Some(f) => format!(": rename it {f}"),
                        None => String::new(),
                    };
                    let shown = self.sig_text(&e);
                    let menu = match free.first() {
                        Some(f) => format!("repair: rename `{}` to {f}", p.name),
                        None => format!("repair: a lambda in the form `{shown}` passes"),
                    };
                    self.rejects_offering(
                        Row::ParameterKinds,
                        p.span,
                        format!(
                            "the lambda's parameter `{}` is not a parameter of `{shown}`{fix}",
                            p.name
                        ),
                        [menu],
                    );
                    return m.ty(Ty::func(e));
                }
            }
        }
        if !e.held.is_empty() {
            // A bounded variable a parameter holds stands for whichever carrier the caller
            // passes, so a parameter of that type has no use of its own. The lambda is checked
            // as a declared function is, generic in its parameters, and passed as
            // `fit_declared` passes one: each use its body makes is checked at each carrier.
            let defaults: Vec<&'a Param> = extra.iter().map(|&i| &params[i]).collect();
            let slots: Vec<Option<&'a Param>> =
                order.iter().map(|o| o.map(|i| &params[i])).collect();
            let names = e.params.clone();
            m.k(Frame::FitGeneric {
                e,
                span,
                order,
                extra,
            });
            return self.lambda_sig(m, slots.into_iter(), &defaults, names, body);
        }
        // A bounded variable of `e` no parameter holds is fixed by no argument: the lambda may
        // return any carrier of its bound.
        let unheld = e.unheld();
        let s = FitF {
            params,
            body,
            e,
            unheld,
            span,
            order,
            extra,
            a: 0,
            entered: false,
            x: 0,
            waiting: None,
        };
        self.fit_step(m, Box::new(s));
    }

    /// For each arrow of the expected type in turn: the lambda's parameters bound to its
    /// parameter types, those it does not pass to their defaults, and the body checked at
    /// its result.
    fn fit_step(&mut self, m: &mut M<'a>, mut s: Box<FitF<'a>>) {
        match s.waiting.take() {
            Some(FitWait::Extra) => {
                let t = m.take_ty();
                let p = &s.params[s.extra[s.x]];
                let id = self.id(p.span, &p.name);
                self.env.insert(id, t);
                s.x += 1;
            }
            Some(FitWait::Body) => {
                let r = m.take_ty();
                let want = s.e.arrows[s.a].result.subst(&s.unheld);
                if !self.subtype(&r, &want) {
                    let why = r.refused(&want);
                    let (r, want, e) = (self.text(&r), self.text(&want), self.sig_text(&s.e));
                    self.error(
                        s.body.span,
                        format!("the lambda returns {r}, and `{e}` returns {want}{why}"),
                    );
                }
                s.a += 1;
                s.entered = false;
                s.x = 0;
            }
            None => {}
        }
        if s.a < s.e.arrows.len() {
            let arrow = &s.e.arrows[s.a];
            if !s.entered {
                s.entered = true;
                for (j, o) in s.order.iter().enumerate() {
                    if let Some(i) = o {
                        let p = &s.params[*i];
                        let mut t = arrow.params[j].clone();
                        if let Some(a) = &p.ty {
                            let a = denoted(a);
                            if !self.subtype(&t, &a) {
                                let why = t.refused(&a);
                                let (ta, tt) = (self.text(&a), self.text(&t));
                                let e = self.sig_text(&s.e);
                                self.error(
                                    p.span,
                                    format!(
                                        "the lambda's parameter `{}` is {ta}, and `{e}` passes {tt}{why}",
                                        p.name
                                    ),
                                );
                            }
                            t = a;
                        }
                        let id = self.id(p.span, &p.name);
                        self.env.insert(id, t);
                    }
                }
            }
            if let Some(&i) = s.extra.get(s.x) {
                let params = s.params;
                let d = params[i].default.as_ref().expect("a default");
                s.waiting = Some(FitWait::Extra);
                m.k(Frame::FitLambda(s));
                return m.job(Job::Expr(d));
            }
            let want = Want::of(&arrow.result.subst(&s.unheld));
            let body = s.body;
            s.waiting = Some(FitWait::Body);
            m.k(Frame::FitLambda(s));
            return m.job(Job::Body(body, want));
        }
        let FitF {
            e,
            span,
            order,
            extra,
            ..
        } = *s;
        self.fitted(span, order, extra);
        m.ty(Ty::func(e));
    }

    /// Records how the lambda at `span` was fitted, unless its parameters are the slots'
    /// in order with none left to a default.
    fn fitted(&mut self, span: Span, order: Vec<Option<usize>>, extra: Vec<usize>) {
        let identity = extra.is_empty() && order.iter().enumerate().all(|(j, o)| *o == Some(j));
        if !identity {
            self.put(Undo::Fit(span, Some(Fit::Lambda { order, extra })));
        }
    }
}

/// The expression a branch `e` gives: the one expression of a block of nothing else, else `e`.
fn exported(e: &Expr) -> &Expr {
    match &e.kind {
        ExprKind::Block(stmts) => match stmts.as_slice() {
            [
                Stmt {
                    kind: StmtKind::Return(es),
                    ..
                },
            ] if es.len() == 1 => &es[0],
            _ => e,
        },
        _ => e,
    }
}

/// The scalars and atoms of `ty`, when it holds nothing else.
fn plain(ty: &Ty) -> Option<KType> {
    (ty.tuples.is_empty() && ty.fns.is_empty() && ty.vars.is_empty() && !ty.dynamic)
        .then(|| ty.set.clone())
}

// The checker's side of the tests around an expression (`arms.rs`): the nodes of a condition
// and the ints the tests allow an operand. It is written here rather than beside `Arms`, so
// that `arms.rs` imports none of the checker's own files (step S.1f).
impl<'a> Ck<'_, 'a> {
    /// The ints `e` may be here: what its text shows ([`Ck::known`]) met with what the tests
    /// the walk is in show of it; and whether a test narrowed it.
    pub(super) fn ints_here(&mut self, e: &'a Expr) -> (IntervalSet, bool) {
        let k = self.known(e);
        if k.value.is_some() || self.arms.here() == 0 {
            return (k.ints, false);
        }
        let narrowed = self.ints_in_scope(e);
        let ints = k.ints.meet(&narrowed);
        let changed = ints != k.ints;
        (ints, changed)
    }

    /// The two nodes of the condition `e` checked here, where it holds and where it fails, with
    /// the products of its names taken from their types as they are here: a type an `is` has
    /// narrowed holds here, and may not where the scope is read.
    pub(super) fn test_nodes(&mut self, e: &'a Expr) -> (usize, usize) {
        let t = self.term(e);
        let fresh = t
            .vars
            .iter()
            .map(|(x, id)| {
                let p = match self.env.get(id).and_then(plain) {
                    Some(t) => Product::of_type(t),
                    None => Product::top(),
                };
                (x.clone(), p)
            })
            .collect();
        self.arms.test(e, fresh)
    }

    /// A note at each test the walk is in that bears on the operand `e`, innermost first, for a
    /// rejection whose operand a test narrowed ([`Arms::deciding`]): a test that changed a name
    /// `e` reads, or one the value of a name bound in an arm reads, where it was bound
    /// ([`Arms::bound`]), or one that changed a name such a test reads (`a == b` relates `b` to
    /// a test on `a`).
    ///
    /// [`Arms::deciding`]: super::arms::Arms::deciding
    /// [`Arms::bound`]: super::arms::Arms::bound
    pub(super) fn deciding_notes(&mut self, e: &'a Expr) -> Vec<Note> {
        let starts = self.read_names(e);
        self.arms
            .deciding(starts)
            .into_iter()
            .map(|(span, outcome, case)| Note {
                span,
                text: match case {
                    false => format!("this test is {outcome} here"),
                    true => format!("this test is {outcome} in one case here"),
                },
            })
            .collect()
    }

    /// The scope names `e` reads, each with the node it is read under: its own, under the node
    /// the walk is in, and those of the values of the names bound in an arm that it reads,
    /// through binders of binders, each binder once, under the node the binder was bound
    /// under, where its value is read ([`Item::Bound`]), and the inputs of a binder's summary
    /// under the node the walk is in, where they are read ([`Ck::with_bound`]).
    fn read_names(&mut self, e: &'a Expr) -> Vec<(Arc<str>, usize)> {
        let t = self.term(e);
        let here = self.arms.here();
        let mut out: Vec<(Arc<str>, usize)> =
            t.vars.iter().map(|(x, _)| (x.clone(), here)).collect();
        let mut seen = HashSet::new();
        let mut stack = t.binders.clone();
        while let Some(b) = stack.pop() {
            if !seen.insert(b) {
                continue;
            }
            let Some(&value) = self.facts.get(&b) else {
                continue;
            };
            // A binder with a summary is also read through it over its inputs here
            // ([`Ck::with_bound`]), so a test on an input since the binding bears on it.
            if let Some(Some(sum)) = self.arms.summaries.get(&b) {
                out.extend(sum.summary.vars().iter().map(|x| (x.clone(), here)));
            }
            let v = self.term(value);
            let at = self.arms.bound_at.get(&b).copied().unwrap_or(0);
            out.extend(v.vars.iter().map(|(x, _)| (x.clone(), at)));
            stack.extend_from_slice(&v.binders);
        }
        out.sort_unstable();
        out.dedup();
        out
    }

    /// The ints `e` may be in the scope of the node the walk is in.
    fn ints_in_scope(&mut self, e: &'a Expr) -> IntervalSet {
        let t = self.term(e);
        let here = self.arms.here();
        let mut wanted = vec![Item::Scope(here)];
        wanted.extend(t.binders.iter().map(|&b| Item::Bound(b)));
        self.settle(wanted);
        let s = self.arms.scopes[here].clone().expect("settled");
        let mut s = self.with_bound(s, &t.binders);
        s.eager_on(&t.term);
        product::forward(&t.term, &mut s).ints().clone()
    }

    /// `s` told of the values of `binders` it has no product of, each with the summary of its
    /// value over the inputs it reads ([`Ck::summarized`]), and of each input `s` has no
    /// product of: so a test of the name narrows its inputs, and a name read where a test has
    /// narrowed its inputs is narrowed by its summary over them ([`Scope::bind_summarized`]).
    /// With `y = n + 1; x = y + n`, a test of `x` narrows `n`, and `y` read under it lies where
    /// `n + 1` does over the narrowed `n`: one evaluation of `y`'s formed summary, `O(k)` for
    /// `k` inputs.
    fn with_bound(&mut self, mut s: Scope, binders: &[usize]) -> Scope {
        if s.bottom {
            return s;
        }
        for &b in binders {
            let (Some(p), Some(name)) = (self.arms.bound.get(&b), self.arms.names.get(&b)) else {
                continue;
            };
            if s.names.contains_key(name) {
                continue;
            }
            let (p, name) = (p.clone(), name.clone());
            let e = Shared::new(Term::Var(name.clone()));
            // Every input of a summary is in its map ([`Ck::summarize_value`]).
            let Some(sum) = self.summarized(b) else {
                s.bind(&name, p, &e);
                continue;
            };
            let mut doms = Domains::new();
            for (v, q) in sum
                .summary
                .vars()
                .iter()
                .filter_map(|v| Some((v, sum.inputs.get(v)?)))
            {
                if !s.names.contains_key(v) {
                    s.bind(v, q.clone(), &Shared::new(Term::Var(v.clone())));
                }
                doms.insert(v.clone(), q.ints().clone());
            }
            s.bind_summarized(&name, p, &e, &sum.summary, &doms);
        }
        s
    }

    /// Records, for the binder `b` of `value` bound here, the type here of each narrowed name
    /// the value reads ([`Ck::summarize_value`]): the type a summary of the value takes for
    /// it, which holds wherever `b` is read, since `b` is read only within the narrowing it was
    /// bound in, where a name is narrowed further or not at all. Nothing is recorded while no
    /// narrowing is in place. Costs the value's size, once.
    fn narrowed_at(&mut self, b: usize, value: &'a Expr) {
        if self.narrowings == 0 {
            return;
        }
        let t = self.term(value);
        for (_, id) in &t.vars {
            if (self.whence.get(id)).is_some_and(|o| matches!(o.why, Why::Narrowed(_)))
                && let Some(ty) = self.env.get(id)
            {
                self.narrowed_at.insert((b, *id), ty.clone());
            }
        }
    }

    /// The summary of the value of binder `b` ([`Summarized`]), made once for the binder from
    /// those of the binders its value reads, children first on an explicit stack, each entered
    /// once: the binders form a graph without cycles, as statements are checked in dependency
    /// order, and the memo is the visited set. A name the value reads is read through its
    /// binder's summary when it has one, and is otherwise an input: a binder over its product,
    /// a parameter over the ints of its type where `b` is bound ([`Ck::narrowed_at`]). Each
    /// summary is formed as it is made ([`LetPa::form`]), its parts formed before it, so that
    /// forming it adds their sums and does not walk them: a test reading any binder of a block,
    /// in any order, costs its own summary. Costs the size of each value read, once, and the
    /// merges of the inputs' maps and of the formed sums, each by input.
    ///
    /// [`Summarized`]: super::arms::Summarized
    /// [`LetPa::form`]: zedc_preimage::preimage::LetPa::form
    fn summarized(&mut self, b: usize) -> Option<Rc<Summarized>> {
        let mut entered = HashSet::new();
        let mut stack = vec![(b, false)];
        while let Some((c, ready)) = stack.pop() {
            if self.arms.summaries.contains_key(&c) || (!ready && !entered.insert(c)) {
                continue;
            }
            let Some(&value) = self.facts.get(&c) else {
                self.arms.summaries.insert(c, None);
                continue;
            };
            let t = self.term(value);
            if !ready {
                stack.push((c, true));
                stack.extend(t.binders.iter().map(|&d| (d, false)));
                continue;
            }
            let s = self.summarize_value(c, &t);
            self.arms.summaries.insert(c, s.map(Rc::new));
        }
        self.arms.summaries[&b].clone()
    }

    /// The summary of the value `t` of binder `b`, the summaries of the binders it reads made
    /// ([`Ck::summarized`]). Its inputs' map is the largest of those of the binders it reads,
    /// with the others' and its own inputs added: an input it reads itself takes its type
    /// where `b` is bound, at least as narrow as a binder it reads took.
    fn summarize_value(&self, b: usize, t: &Translated) -> Option<Summarized> {
        let int = KType::int();
        let mut inputs: imbl::OrdMap<Arc<str>, Product> = imbl::OrdMap::new();
        let mut own: Vec<(Arc<str>, Product)> = Vec::new();
        let mut lets = Lets::new();
        for (x, id) in &t.vars {
            let bound = self.arms.bound.get(id);
            if let Some(Some(sum)) = self.arms.summaries.get(id) {
                // `union` adds the smaller map to the larger.
                inputs = inputs.union(sum.inputs.clone());
                let ints = bound.map_or_else(IntervalSet::top, |p| p.ints().clone());
                let summary = sum.summary.clone();
                lets.insert(x.clone(), LetIn { summary, ints });
                continue;
            }
            let p = match bound {
                Some(p) => p.clone(),
                None if self.facts.contains_key(id) => continue,
                None => match self.param_type(b, *id).and_then(plain) {
                    Some(ty) => Product::of_type(ty),
                    None => continue,
                },
            };
            if p.ty.element.subtype(&int) && !p.is_empty() {
                own.push((x.clone(), p));
            }
        }
        // The domains of the inputs the value reads itself, and of the one input of each name
        // it reads through a summary over one, which a term of the value other than a sum
        // reads it through (`2 * y` is a sum, `y * y` is not); not those of every input of the
        // map, which would cost each binder of a chain the inputs of all before it.
        let mut domains = Domains::new();
        for l in lets.values() {
            let vars = l.summary.vars();
            if vars.len() == 1
                && let Some(v) = vars.iter().next()
                && let Some(p) = inputs.get(v)
            {
                domains.insert(v.clone(), p.ints().clone());
            }
        }
        for (x, p) in own {
            domains.insert(x.clone(), p.ints().clone());
            inputs.insert(x, p);
        }
        let summary = let_summary(&t.term, &domains, lets)?;
        summary.form();
        Some(Summarized { summary, inputs })
    }

    /// The type of the parameter `id` where binder `b` is bound: as recorded there when a
    /// narrowing was in place ([`Ck::narrowed_at`]); else, when a test has narrowed it since,
    /// its type before that narrowing; else its type.
    fn param_type(&self, b: usize, id: usize) -> Option<&Ty> {
        if let Some(ty) = self.narrowed_at.get(&(b, id)) {
            return Some(ty);
        }
        match self.whence.get(&id) {
            Some(o) if matches!(o.why, Why::Narrowed(_)) => self.unnarrowed.get(&id),
            _ => self.env.get(&id),
        }
    }

    /// Computes the scopes and binder products `wanted` needs, each once, on an explicit stack:
    /// an item is computed when every item it waits on is, and the memo is the visited set.
    fn settle(&mut self, wanted: Vec<Item>) {
        let mut entered = HashSet::new();
        let mut stack: Vec<(Item, bool)> = wanted.into_iter().map(|i| (i, false)).collect();
        while let Some((item, ready)) = stack.pop() {
            if self.computed(item) {
                continue;
            }
            if ready {
                self.compute(item);
            } else if entered.insert(item) {
                stack.push((item, true));
                for d in self.waits(item) {
                    if !self.computed(d) {
                        stack.push((d, false));
                    }
                }
            }
        }
    }

    fn computed(&self, item: Item) -> bool {
        match item {
            Item::Scope(n) => self.arms.scopes[n].is_some(),
            Item::Bound(b) => self.arms.bound.contains_key(&b),
        }
    }

    /// The items `item` is computed from.
    fn waits(&mut self, item: Item) -> Vec<Item> {
        match item {
            Item::Scope(n) => match self.arms.nodes[n] {
                Node::Root => Vec::new(),
                Node::Assume { parent, test, .. } => {
                    let t = self.term(test);
                    let mut out = vec![Item::Scope(parent)];
                    out.extend(t.binders.iter().map(|&b| Item::Bound(b)));
                    out
                }
                Node::Join(a, b) => vec![Item::Scope(a), Item::Scope(b)],
            },
            Item::Bound(b) => {
                let Some(&value) = self.facts.get(&b) else {
                    return Vec::new();
                };
                let t = self.term(value);
                let at = self.arms.bound_at.get(&b).copied().unwrap_or(0);
                let mut out = vec![Item::Scope(at)];
                out.extend(t.binders.iter().map(|&c| Item::Bound(c)));
                out
            }
        }
    }

    /// Computes `item` from the items it waits on. One still being computed, which only a
    /// cycle through binders could give, is read as saying nothing.
    fn compute(&mut self, item: Item) {
        match item {
            Item::Scope(n) => {
                let s = match self.arms.nodes[n] {
                    Node::Root => Scope::new([]).lazy(),
                    Node::Assume {
                        parent,
                        test,
                        outcome,
                        ..
                    } => {
                        let t = self.term(test);
                        let p = self.scope_or_root(parent);
                        // A bound name the scope has no product of is its value, and any other
                        // name any value of its type where the test is checked. A scope no
                        // state reaches is told of none: it stays unreachable.
                        let mut p = self.with_bound(p, &t.binders);
                        if let Node::Assume { fresh, .. } = &self.arms.nodes[n]
                            && !p.bottom
                        {
                            for (x, q) in fresh.iter() {
                                if !p.names.contains_key(x) {
                                    p.bind(x, q.clone(), &Shared::new(Term::Var(x.clone())));
                                }
                            }
                        }
                        // Not shown, so a failing test leaves the names as they were
                        // (`assume_case`): emptying each costs the names in scope.
                        //
                        // The scopes are lazy ([`Scope::lazy`]): a test that moves a hub, a name
                        // many spokes `ai >= n` mention, leaves the leaves `ai` to be settled
                        // where a read needs them, so `k` tests on a hub of `k` spokes cost `k`
                        // narrowings and the reads, not `k²` projections; a rejection's notes
                        // find the tests that changed a name by [`Arms::lookup`], not by a list
                        // per test of the names it changed, which is `k` names a test there.
                        //
                        // Complexity tradeoff: only a star's leaf is left to a read: a name
                        // whose conjuncts are each a bound on a sum of names, of coefficients
                        // one and minus one, with one hub, or with hubs each of whose other
                        // conjuncts is a leaf's, bounds the hub alone or mentions only hubs of
                        // the leaf (`Conjuncts::star`), such as `n >= m` for the hubs of
                        // `ai >= n && ai >= m`; such a star is projected with those conjuncts
                        // (`Conjuncts::core`). So `ai >= n && ai >= m` and `ai >= n + m` under
                        // `k` tests on `n` and `k` on `m` cost `O(k)`: 0.15, 0.28 and 0.52 s at
                        // `k` = 96, 192 and 384, and 0.11, 0.18, 0.33 and 1.51 s at `k` = 12,
                        // 24, 48 and 192 (2026-11-07, load 18); with `n >= m` above them, 0.05,
                        // 0.11, 0.22 and 0.43 s at `k` = 24 to 192, and 0.08, 0.17, 0.40 and
                        // 0.81 s at `k` = 12 to 96 for the sum (2026-11-07, load 23), where
                        // 0.09, 0.31, 1.16 and 4.91 s were `k²` before (wt/narrow-hub-rest at
                        // 68a03534). What is given up is time, not an answer: a scope that is
                        // not lazy projects each star of two hubs or more again when a conjunct
                        // among its hubs comes or goes, `k` stars a test there, about `k²`
                        // over `k` such tests; a conjunct at a hub that mentions a name no
                        // star's leaf there has as a hub keeps every leaf there in the forest,
                        // `k` blocks a test on the hub, as before; and a hub that comes to have
                        // such a leaf counts the names its other conjuncts mention. Why: the
                        // leaf of related hubs lies on a cycle of the relation, so its product
                        // is the projection of the star with the conjuncts among its hubs, not a
                        // cut at a box's corner. Trigger: many tests among two hubs that many
                        // stars share, in a scope that is not lazy; or a hub related to a name
                        // that is not a hub of its leaves.
                        // Test: `l01_39a_bit_words::scaling::related_hubs_settle_in_time_linear_in_the_tests`.
                        // COMPLEXITY.md C26. A complete solution keeps a feasible point and
                        // settles the cone of a read on demand (the design note of
                        // NARROW-hub-settle, revision of 2026-11-04).
                        let s = p.assume_case(&t.term, outcome, &Premises::new());
                        self.arms.before[n] = Some(p);
                        s
                    }
                    Node::Join(a, b) => self.scope_or_root(a).join(&self.scope_or_root(b)),
                };
                self.arms.scopes[n] = Some(s);
            }
            Item::Bound(b) => {
                let Some(&value) = self.facts.get(&b) else {
                    return;
                };
                let t = self.term(value);
                let at = self.arms.bound_at.get(&b).copied().unwrap_or(0);
                let s = self.scope_or_root(at);
                let mut s = self.with_bound(s, &t.binders);
                s.eager_on(&t.term);
                let mut p = product::forward(&t.term, &mut s);
                if let Some(ty) = self.arms.bound_ty.get(&b) {
                    p.ty.element = p.ty.element.meet(ty);
                }
                self.arms.bound.insert(b, p);
            }
        }
    }

    fn scope_or_root(&self, n: usize) -> Scope {
        self.arms.scopes[n]
            .clone()
            .unwrap_or_else(|| Scope::new([]).lazy())
    }

    /// `e` as a kernel term ([`Translated`]): its int and bool literals and the values its text
    /// shows ([`Ck::known`]), its names, its unary `-` and `!`, its integer operators, its
    /// comparisons, `&&` and `||`; anything else is a name of its own, by its span, which the
    /// scope knows nothing of. Built children first on an explicit stack, once for `e`.
    fn term(&mut self, e: &'a Expr) -> Rc<Translated> {
        if let Some(t) = self.arms.terms.get(&e.span) {
            return t.clone();
        }
        let (mut binders, mut vars) = (Vec::new(), Vec::new());
        let mut done: Vec<Term> = Vec::new();
        let mut stack = vec![(e, false)];
        while let Some((x, ready)) = stack.pop() {
            let opaque = || Term::Var(format!("?{}:{}", x.span.start, x.span.end).into());
            if ready {
                let t = match &x.kind {
                    ExprKind::Unary(o, _) => {
                        let a = done.pop().expect("an operand");
                        let p = if *o == "-" { Prim::Neg } else { Prim::Not };
                        Term::Prim(p, vec![a])
                    }
                    ExprKind::Binary(o, _, _) => {
                        let b = done.pop().expect("a second operand");
                        let a = done.pop().expect("a first operand");
                        Term::Prim(prim_of(o).expect("a translated operator"), vec![a, b])
                    }
                    _ => unreachable!("only operators wait on their operands"),
                };
                done.push(t);
                continue;
            }
            if let Some(v) = self.known(x).value {
                done.push(Term::Lit(v));
                continue;
            }
            match &x.kind {
                ExprKind::Bool(b) => done.push(Term::Lit(Value::Bool(*b))),
                ExprKind::Name(n) => match self.t.res.uses.get(&x.span) {
                    Some(Ref::Bound(ids)) if ids.len() == 1 => {
                        let id = ids[0];
                        let name = var(n, id);
                        if self.facts.contains_key(&id) {
                            binders.push(id);
                            self.arms.names.insert(id, name.clone());
                        }
                        vars.push((name.clone(), id));
                        done.push(Term::Var(name));
                    }
                    _ => done.push(opaque()),
                },
                ExprKind::Unary("-" | "!", a) => {
                    stack.push((x, true));
                    stack.push((a, false));
                }
                ExprKind::Binary(o, a, b) if prim_of(o).is_some() => {
                    stack.push((x, true));
                    stack.push((b, false));
                    stack.push((a, false));
                }
                _ => done.push(opaque()),
            }
        }
        binders.sort_unstable();
        binders.dedup();
        vars.sort_unstable();
        vars.dedup();
        let t = Rc::new(Translated {
            term: done.pop().expect("a term"),
            binders,
            vars,
        });
        self.arms.terms.insert(e.span, t.clone());
        t
    }
}
