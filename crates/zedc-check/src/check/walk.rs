//! The checker's walk over statements, expressions and declared functions, on a heap stack:
//! a program nested as deep as memory allows checks on a thread of any stack size.
//!
//! Each recursive call of the walk is a `Job`. What the caller does with the call's result
//! is a `Frame` pushed below the job, which reads the result from `M::ret` when the job
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

/// Checks a resolved unit.
pub fn check(unit: &[Stmt], res: &Resolution) -> Info {
    check_with(&Tables::new(unit, res), unit)
}

/// Checks a unit whose binder tables are `t`, as [`check`] does with tables it builds.
pub fn check_with<'a>(t: &Tables<'a>, unit: &'a [Stmt]) -> Info {
    KType::forget_emptiness();
    let mut ck = Ck::new(t);
    ck.bounds();
    ck.walk(unit);
    ck.finish();
    ck.info
        .errors
        .sort_by(|a, b| (a.span, &a.message).cmp(&(b.span, &b.message)));
    ck.info.errors.dedup();
    ck.info
}

/// The type of the binary operator `op` applied to arguments of the types `args`, with the
/// errors the application reports: how an operator treats loose and family atoms.
pub fn operator(op: &str, args: &[Ty]) -> (Ty, Vec<String>) {
    let res = zedc_resolve::resolve::resolve(&[]).expect("the empty unit resolves");
    let t = Tables::new(&[], &res);
    let mut ck = Ck::new(&t);
    let args = args.iter().map(|a| Some(Arg::of(a.clone()))).collect();
    let (out, _) = ck.apply(
        &format!("`{op}`"),
        &op_sig(op),
        args,
        true,
        Span { start: 0, end: 0 },
    );
    (out, ck.info.errors.into_iter().map(|e| e.message).collect())
}

/// What a job gives back.
pub(super) enum Ret<'a> {
    /// Nothing yet, or a statement's result, which is nothing.
    None,
    Ty(Ty),
    Arg(Arg<'a>),
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
    /// Reports the error, if any, with its repairs, and gives nothing.
    Fail(Option<(Span, String, Vec<String>)>),
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
        x: Box<Arg<'a>>,
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
    got: Vec<Option<Arg<'a>>>,
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
    slots: Vec<Option<(Arg<'a>, &'a Expr)>>,
    /// Whether every argument so far found a free parameter of its kind.
    fits: bool,
    /// How many arguments have been started; one more than placed while one is checked.
    started: usize,
    /// 1 when the receiver fills the first parameter, else 0.
    first: usize,
}

pub(super) struct CallValueF<'a> {
    what: Rc<str>,
    receiver: Option<Arg<'a>>,
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
    receiver: Option<Arg<'a>>,
    args: Rc<Args<'a>>,
    slots: Vec<Option<At>>,
    got: Vec<Option<Arg<'a>>>,
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

    fn take_arg(&mut self) -> Arg<'a> {
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
                if let Some((span, message, menu)) = err {
                    self.error_offering(span, message, menu);
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
                        notes.push(Note {
                            span: cond.span,
                            text: "repair: compare the value, so that the condition is a `bool`, \
                                   as `if x == 0 { … }` or `if x is int { … }`"
                                .to_string(),
                        });
                        self.error_with(
                            cond.span,
                            format!(
                                "{what} is {shown}, not bool: `if` chooses its branch by a \
                                 `bool`, and this condition may be another value"
                            ),
                            notes,
                        );
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
                let (yes, no) = self.atom_eq(e);
                m.ret = Ret::Cond(Cond::of(t, yes, no, sides));
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
                    expr: Some(e),
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
                    self.pushed(&t, port, value.span);
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
                self.join_narrowed(level);
                let strip = self.widened_other(&ids, &tys);
                let sig = self.handled_sig(params, &ids, tys, result, &f.body);
                let sig = self.generalize(level, sig, &strip);
                let sig = self.floors_into(sig, &ids);
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
                    _ => "the function called here".into(),
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
                    let err = (named.is_empty() && !curry).then(|| {
                        let n = positional.len();
                        let message = format!("`{w}` takes one argument, and this call passes {n}");
                        let menu = vec![format!("repair: pass one argument, as `{w}(x)`")];
                        (span, message, menu)
                    });
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
                self.join_narrowed(level);
                let strip = self.widened_other(&ids, &tys);
                let sig = self.handled_sig(names, &ids, tys, result, body);
                let sig = self.generalize(level, sig, &strip);
                let sig = self.floors_into(sig, &ids);
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
                    let menu = [format!(
                        "repair: change the lambda so that its parameters and its result have the \
                         types of `{e}`"
                    )];
                    self.error_offering(
                        span,
                        format!(
                            "the lambda is `{s}`, not `{e}`: it is passed where a function of that \
                             type is expected, and its own type does not fit that one"
                        ),
                        menu,
                    );
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
                unreachable!(
                    "name resolution rejects every struct, type, method, import, local and annotated definition before the checker reads the program"
                )
            }
            StmtKind::Mutable(_)
            | StmtKind::IndexedDef(_)
            | StmtKind::While(_)
            | StmtKind::Until(_)
            | StmtKind::Expr(_) => unreachable!(
                "name resolution rejects every mutable variable, indexed definition, while, until and expression statement before the checker reads the program"
            ),
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
                    self.open_params.insert(*id);
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
                        notes.extend(default_repairs(&p.name, &dt, &shown, d.span));
                        self.error_with(
                            d.span,
                            format!(
                                "{what} is {dt}, not {shown}: a default is a value of its \
                                 parameter's type"
                            ),
                            notes,
                        );
                    }
                }
                None => {
                    if !self.subtype(&dt, t) {
                        let why = dt.refused(t);
                        let (dt, t) = (self.text(&dt), self.text(t));
                        let menu = default_repairs(&p.name, &dt, &t, d.span);
                        self.error_offering(
                            d.span,
                            format!(
                                "{what} is {dt}, not {t}: a default is a value of its parameter's \
                                 type{why}"
                            ),
                            menu.into_iter().map(|n| n.text),
                        );
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
                expr: Some(e),
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
                unreachable!(
                    "name resolution rejects every record, with, this and match before the checker reads the program"
                )
            }
            ExprKind::Range(..)
            | ExprKind::In { .. }
            | ExprKind::Reduce { .. }
            | ExprKind::Read { .. }
            | ExprKind::Section(_)
            | ExprKind::Array(_)
            | ExprKind::Set(_)
            | ExprKind::Map(_)
            | ExprKind::For { .. } => unreachable!(
                "name resolution rejects every range, in, reduction, read, section, array, set, map and for before the checker reads the program"
            ),
            ExprKind::SortKey { .. } => unreachable!(
                "name resolution rejects every sort key before the checker reads the program"
            ),
            ExprKind::Loop { .. } | ExprKind::Break(_) | ExprKind::Spread { .. } => {
                unreachable!(
                    "name resolution rejects every loop, break and spread before the checker reads the program"
                )
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
        mut x: Arg<'a>,
        mut y: Arg<'a>,
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
                if op == "^" {
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
        receiver: Option<Arg<'a>>,
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

    fn word_end(&mut self, w: &str, x: Arg<'a>, span: Span) -> Ty {
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
        receiver: Option<(Arg<'a>, &'a Expr)>,
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
        receiver: Option<Arg<'a>>,
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
                    let got = |a: &ArgSrc| match a {
                        ArgSrc::Got(x) => (x.ty.clone(), x.at),
                        ArgSrc::Expr(_) => unreachable!("found above"),
                    };
                    let written: Vec<(Ty, Option<Span>)> = s
                        .receiver
                        .iter()
                        .map(|x| (x.ty.clone(), x.at))
                        .chain(s.args.positional.iter().map(got))
                        .chain(s.args.named.iter().map(|(_, a)| got(a)))
                        .collect();
                    let written: Vec<(&Ty, Option<Span>)> =
                        written.iter().map(|(t, at)| (t, *at)).collect();
                    self.note_widened(&kind, &written);
                    let r = self.need(k, kind, true, span);
                    s.out = s.out.union(&r);
                }
                Piece::Dyn => {
                    self.tried_at(span, None);
                    self.any(&format!("a call of {}", callee(&s.what)), span);
                }
                Piece::Var(_) => {
                    self.tried_at(span, None);
                    s.out = s.out.union(&Ty::dynamic());
                }
                p if p.is_atoms() => {}
                p => {
                    let shown = self.text(&p.ty());
                    let w = &s.what;
                    let menu = [format!(
                        "repair: call a function here, or write `{w}` without the parentheses \
                         if its value is meant"
                    )];
                    self.error_offering(
                        span,
                        format!(
                            "`{w}` is {shown}, not a function: this call applies `{w}` to \
                             arguments, and a value of type {shown} cannot be applied"
                        ),
                        menu,
                    );
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
        receiver: Option<Arg<'a>>,
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
                .map(|&j| {
                    (
                        span,
                        Misfit::Missing(&sig.params[j].name, sig.params[j].positional),
                    )
                })
                .collect(),
            false => (missing.iter())
                .find_map(|&j| {
                    let p = &sig.params[j];
                    match p.default {
                        Some((_, _, true)) => None,
                        Some((_, _, false)) => Some((span, Misfit::OpenDefault(&p.name))),
                        None => Some((span, Misfit::Missing(&p.name, p.positional))),
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
                let what = callee(&s.what);
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
                    .menu(&who, declared)
                    .into_iter()
                    .map(|text| Note { span: at, text });
                match misfit.row() {
                    Some(row) => self.rejects_with(row, at, message, menu.collect()),
                    None => self.error_with(at, message, menu.collect()),
                }
            }
            return m.ty(Ty::empty());
        }
        // The first misfit, the one elaboration would report first, explains the refusal.
        let (at, misfit) = misfits[0];
        let message = format!(
            "`{what}` here is a function of type `{}`, and the arguments of this call do not \
             fit its parameters: {}",
            self.sig_text(sig),
            misfit.message(what)
        );
        let menu = misfit.menu(what, false);
        m.k(Frame::Fail(Some((at, message, menu))));
        m.each(args.exprs());
    }

    /// `x.f(args)` and `x?.f(args)`: the call `f(x, args)`; `?.` passes `x`'s atoms around it.
    fn member(&mut self, m: &mut M<'a>, of: &'a Expr, s: MemberF<'a>) {
        m.k(Frame::Member1(Box::new(s)));
        m.job(Job::Arg(of, Want::default()));
    }

    fn member_end(&mut self, m: &mut M<'a>, s: MemberF<'a>, mut x: Arg<'a>) {
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
                    None => {
                        self.open_params.insert(id);
                        self.param_ty(id, t.clone())
                    }
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
                "repair: write the lambda with the parameters of `{shown}`, its first {} taken by \
                 position",
                pos.len()
            )];
            self.rejects_offering(
                Row::ParameterKinds,
                span,
                format!(
                    "the lambda takes {} parameter{}, and `{shown}` passes {} by position: the \
                     lambda is called as a function of type `{shown}` is, so it needs a \
                     parameter for each argument passed by position",
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
                        None => {
                            format!("repair: write the lambda with the parameters of `{shown}`")
                        }
                    };
                    let fix = format!(
                        "{fix}. The lambda is passed where a function of type `{shown}` is \
                         expected, and a call of it passes each named argument by its name, so \
                         each parameter the lambda does not take by position must have a name of \
                         `{shown}` or a default"
                    );
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
                    let menu = [
                        format!("repair: change the lambda's body so that it gives {want}"),
                        format!(
                            "repair: handle the values that are not {want} in the body, with \
                             `match` or with `else`"
                        ),
                    ];
                    self.error_offering(
                        s.body.span,
                        format!(
                            "the lambda returns {r}, and `{e}` returns {want}: the lambda is \
                             passed where a function of type `{e}` is expected, so its result must \
                             be {want}{why}"
                        ),
                        menu,
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
                                let name = &p.name;
                                let menu = [format!(
                                    "repair: declare `{name}` as {tt}, or with no type, so that it \
                                     takes every argument `{e}` passes"
                                )];
                                self.error_offering(
                                    p.span,
                                    format!(
                                        "the lambda's parameter `{name}` is {ta}, and `{e}` passes \
                                         {tt}: the lambda is called as a function of type `{e}` \
                                         is, so each parameter must take every value passed to \
                                         it{why}"
                                    ),
                                    menu,
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

/// What the input `v` of `sum`, of product `q` in a scope, adds there ([`images::Leaf`]).
fn leaf(sum: &Summarized, v: &Arc<str>, q: &Product) -> images::Leaf {
    // The summary holds where each input's integers lie within those it was made over
    // ([`Scope::bind_summarized`]).
    let holds = (sum.inputs.get(v)).is_some_and(|d| q.ints().is_subset(d.ints()));
    images::Leaf {
        shift: if holds {
            sum.summary.shift(v, q.ints())
        } else {
            zedc_preimage::preimage::Shift::ZERO
        },
        fails: usize::from(!holds),
        premises: q.premises(),
    }
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
                let ty = self.env.get(id);
                // A class a use has narrowed to int holds ints only, so a test narrows its
                // interval as it does a name of type int (CHK-need-bound).
                let int_class = ty
                    .and_then(|t| self.class_of_ty(t))
                    .is_some_and(|k| self.classes[k].mask == Carrier::Int.bit());
                let p = match ty.and_then(plain) {
                    Some(t) => Product::of_type(t),
                    None if int_class => Product::of_type(KType::int()),
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

    /// [`Ck::with_bound`] for a scope read once by a binder's value ([`Item::Bound`]), which no
    /// test narrows: each of `binders` is bound with its product met with its summary's values
    /// over the inputs `s` has, at their integers there, and the others at those the summary
    /// was formed over ([`Ck::read_image`]); the inputs are not bound and the binding keeps no
    /// summary.
    fn with_bound_read(&mut self, mut s: Scope, binders: &[usize]) -> Scope {
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
            let Some(sum) = self.summarized(b) else {
                s.bind(&name, p, &e);
                continue;
            };
            let (image, premises) = self.read_image(b, &sum, &s.names);
            match image {
                Some(image) => s.bind_within(&name, p, &e, image, &premises),
                None => s.bind(&name, p, &e),
            };
        }
        s
    }

    /// The integers the summary `sum` of binder `b` takes over the inputs the scope of names
    /// `names` has, at their integers there, and the others at those it was formed over, and
    /// the premises of the inputs the scope has: `None` for the integers when the summary does
    /// not hold there or was not formed over domains ([`leaf`]).
    ///
    /// The inputs are kept in a tree with the sum of their shifts, failures and premises
    /// ([`images::Read`]), found from the tree of `b`'s last read, or else of the read of the
    /// binder whose map of inputs `b`'s was made from, by setting the inputs where the two
    /// scopes' names, the two summaries' inputs ([`LetPa::changed_since`]) or their maps of
    /// inputs differ ([`images::updated`]); afresh from the inputs the scope has, found from
    /// the smaller of its names and the summary's inputs, when there is none, the summaries
    /// cannot be compared, or the differences are as many ([`images::fresh`]). Each read costs
    /// the lesser of the differences and the inputs, times `O(log k)`: a chain
    /// `x_k = x_(k-1) + q_k` under a test of each `q_k` reads `x_(k-1)` in the scope of `x_k`
    /// from `x_(k-2)` in that of `x_(k-1)`, which differ at `q_(k-1)`, in `O(log k)`, where
    /// reading its `k - 1` narrowed inputs cost `O(k)` a binding and the chain `Θ(d²)` (item
    /// PA-let-narrow-many). The result is the same either way.
    ///
    /// [`LetPa::changed_since`]: zedc_preimage::preimage::LetPa::changed_since
    fn read_image(
        &mut self,
        b: usize,
        sum: &Rc<Summarized>,
        names: &images::Names<Product>,
    ) -> (Option<IntervalSet>, Premises) {
        let vars = sum.summary.vars();
        let limit = vars.len().min(names.len());
        let base = (self.reads.get(&b)).or_else(|| sum.widest.and_then(|w| self.reads.get(&w)));
        let tree = base
            .and_then(|r| {
                let own: Box<dyn Iterator<Item = &Arc<str>>> = if Rc::ptr_eq(&r.sum, sum) {
                    Box::new(std::iter::empty())
                } else {
                    let terms = sum.summary.changed_since(&r.sum.summary)?;
                    Box::new(terms.chain(images::changed(&r.sum.inputs, &sum.inputs)))
                };
                let changed = own.chain(images::changed(&r.names, names));
                images::updated(&r.tree, changed, vars, names, limit, |v, q| leaf(sum, v, q))
            })
            .unwrap_or_else(|| images::fresh(vars, names, |v, q| leaf(sum, v, q)));
        let total = images::total(&tree);
        let read = images::Read {
            names: names.clone(),
            sum: sum.clone(),
            tree,
        };
        self.reads.insert(b, read);
        let image = (total.fails == 0)
            .then(|| sum.summary.image_shifted(&total.shift))
            .flatten();
        (image, total.premises)
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
        let mut widest: Option<(usize, usize)> = None;
        for (x, id) in &t.vars {
            let bound = self.arms.bound.get(id);
            if let Some(Some(sum)) = self.arms.summaries.get(id) {
                if widest.is_none_or(|(n, _)| sum.inputs.len() > n) {
                    widest = Some((sum.inputs.len(), *id));
                }
                // `union` adds the smaller map to the larger.
                inputs = inputs.union(sum.inputs.clone());
                let ints = bound.map_or_else(IntervalSet::top, |p| p.ints().clone());
                let summary = sum.summary.clone();
                lets.insert(
                    x.clone(),
                    LetIn {
                        summary,
                        ints,
                        read: None,
                    },
                );
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
        // map, which would cost each binder of a chain the inputs of all before it. The sum of
        // the value is formed over the domains of all of `inputs` below, each input's bounds
        // taken as its term is put in, so a summary over several inputs keeps them
        // ([`LetPa::form`], item PA-let-multi).
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
        summary.form(|v| inputs.get(v).map(Product::ints));
        Some(Summarized {
            summary,
            inputs,
            widest: widest.map(|(_, id)| id),
        })
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
                let mut s = self.with_bound_read(s, &t.binders);
                // A parameter the value reads that the scope has no product of is any value of
                // its type where `b` is bound ([`Ck::param_type`]), as [`Ck::summarize_value`]
                // takes it: so `q = n mod 4` with `n: int` is `int[0..=3]`, and a summary that
                // reads `q` as an input has its bounds. Costs the value's names, once.
                if !s.bottom {
                    for (x, id) in &t.vars {
                        if self.facts.contains_key(id) || s.names.contains_key(x) {
                            continue;
                        }
                        if let Some(ty) = self.param_type(b, *id).and_then(plain) {
                            s.bind(x, Product::of_type(ty), &Shared::new(Term::Var(x.clone())));
                        }
                    }
                }
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

/// The steps of class solving, of applying a signature and of fitting a function to a slot,
/// which re-enter the walk: a need checked again at a call checks a call through a value
/// ([`Ck::call_found`]).
impl<'t, 'a> Ck<'t, 'a> {
    /// Component `i` of `v`, destructured into `n` names: of each tuple shape, with `v`'s
    /// atoms, which `TupleGet` passes. A value of a class needs a tuple of `n` of each type
    /// the class meets.
    fn component(&mut self, v: &Ty, i: usize, n: usize, span: Span) -> Ty {
        let mut out = self.passing(v, "a tuple", span);
        for p in v.pieces() {
            match p {
                Piece::Tuple(cs) if cs.len() == n => out = out.union(&cs[i]),
                Piece::Dyn => {
                    if i == 0 {
                        self.any("destructuring", span);
                    }
                }
                Piece::Var(_) if let Some(k) = self.class_of(&p) => {
                    let kind = NeedKind::Destructure { i, n };
                    out = out.union(&self.need(k, kind, true, span));
                }
                Piece::Var(_) => out = out.union(&Ty::dynamic()),
                p if p.is_atoms() => {}
                p => {
                    if i == 0 {
                        let menu = [
                            format!("repair: give this binding a tuple of {n} components"),
                            "repair: bind the value to one name, as `t = …;`, and take it apart \
                             only where a test with `is` has shown it to be a tuple"
                                .to_string(),
                        ];
                        self.error_offering(
                            span,
                            format!(
                                "this value is {}, not a tuple of {n}: it is taken apart into {n} \
                                 names, one for each component, so it must be a tuple of {n} \
                                 components",
                                self.text(&p.ty())
                            ),
                            menu,
                        );
                    }
                }
            }
        }
        out
    }

    /// The call of `sig` at `span` applied again to `with`, from [`Self::outside_args`], with
    /// the checker's state restored after, as [`Self::repairs`] tries a call: the loose atoms
    /// it then gives are those that reach the call's value from outside, which
    /// [`Self::outside_of`] reads. It selects the arrow the call takes from outside for any
    /// callee, a declared function, a method, a function value passed to another function or
    /// computed: `r(x)`, `x.r()`, `x.r`, `ap(r, x)` and `(if c { r } else { r })(x)` alike. A
    /// trial the arguments do not pass leaves the call's atoms from outside unknown, so all
    /// its loose atoms. One more application per call that passes a loose atom inside a
    /// function with a widened parameter.
    fn try_outside(&mut self, what: &str, sig: &Sig, with: Vec<Option<Arg<'a>>>, span: Span) {
        let applied = self.applied.take();
        let saved = self.mark();
        self.trying = true;
        let (t, _) = self.apply(what, sig, with, false, span);
        let ok = self.info.errors.len() == saved.errors;
        self.trying = false;
        self.undo(&saved);
        self.applied = applied;
        self.tried_at(span, ok.then(|| t.loose()));
    }

    /// The signature `sig` of the function of `level`, which ends: each class of the level
    /// takes its type, a type variable of the signature named in order of appearance. The
    /// uses of a class that is a type variable join the signature as its needs; those of a
    /// class of one type are checked on it now. The needs lose the atoms of `strip`
    /// ([`Self::strip_widened`]).
    fn generalize(&mut self, level: usize, mut sig: Sig, strip: &[(usize, KType)]) -> Arc<Sig> {
        // The roots of this level, and the classes whose roots have a type by now: each of
        // the latter takes its root's type in `sig`. A class of a function around goes to
        // that function's list.
        let mut own = Vec::new();
        let mut done = Vec::new();
        for k in std::mem::take(&mut self.pending[level]) {
            let r = self.find(k);
            let at = self.classes[r].level;
            if self.classes[r].resolved.is_none() {
                if at < level {
                    self.pending[at].push(k);
                    continue;
                }
                self.resolve(r);
                own.push(r);
            }
            done.push(k);
        }
        let mut needs: Vec<(usize, Need)> = Vec::new();
        let mut now = Vec::new();
        for &r in &own {
            let uses = std::mem::take(&mut self.classes[r].uses);
            self.classes[r].known.clear();
            self.classes[r].orders.clear();
            self.classes[r].order_of = None;
            self.classes[r].data = false;
            match self.classes[r].resolved.clone() {
                Some(t) if t == Ty::var(format!("${r}").into()) => needs.extend(
                    uses.into_iter()
                        .map(|(s, n)| (s, self.strip_widened(n, strip))),
                ),
                Some(t) => now.extend(uses.into_iter().map(|(_, n)| (n, t.clone()))),
                None => unreachable!("resolved above"),
            }
        }
        for (n, t) in &now {
            self.check_on(n, t, n.span);
        }
        needs.sort_by_key(|(n, _)| *n);
        sig.needs = needs.into_iter().map(|(_, n)| n).collect();
        // Only the classes listed for this level are replaced here, not every class `sig`
        // holds. A type variable keeps its class's name `$k` until `finish`, so a function
        // around does not rewrite the signatures inside it at each depth (CHK-curried);
        // `finish` renames each signature it shows once. A class that takes another class's
        // variable is replaced at every depth of `sig`, so that its variable is found where
        // the signature's own are. A class that takes a type with no variable is replaced
        // only outside the functions `sig` holds: inside them its variable stays, and is read
        // as its type wherever a function's arrows are read ([`Self::open`], [`Self::stale`]),
        // and replaced once in what `finish` shows. Replacing it at every depth cost the
        // size of `sig` at each level, n^2 for n nested lambdas whose parameters each take a
        // carrier (ledger CHK-carrier, COMPLEXITY.md F77).
        // Complexity tradeoff: a class bound to another class's variable or to the unknown is
        // still replaced at every depth, O(size of `sig`) at each level that binds one, so n
        // nested lambdas that each bind such a class would cost n^2 (no such family measured);
        // reading it lazily needs each reading site to follow class-to-class links too.
        let mut deep = Binds::new();
        let mut outside = Binds::new();
        for k in done {
            let v: Arc<str> = format!("${k}").into();
            let t = self.classes[self.find(k)]
                .resolved
                .clone()
                .expect("resolved");
            if t.as_var() == Some(&v) {
                continue;
            }
            match is_solved(&t) {
                true => outside.insert(v, t),
                false => deep.insert(v, t),
            };
        }
        let mut sig = sig.replace(&deep).replace_outside(&outside);
        // The classes of this level that are type variables, named in order of appearance.
        // The names it holds, inside the functions it holds too, are taken; the facts of
        // those functions are shared, not walked again. A class `outside` replaced is still
        // inside those functions, and is no type variable.
        let facts = VarFacts::of(&sig);
        let mine: HashSet<Arc<str>> = own
            .iter()
            .map(|r| Arc::from(format!("${r}")))
            .filter(|v| facts.classes.contains(v) && !outside.contains_key(v))
            .collect();
        // The names before `free` are all taken.
        let mut n = facts.free;
        let mut mine_seen = BTreeSet::new();
        for v in sig.first_seen(&mine) {
            let r = class_id(&v).expect("a class variable");
            let name = loop {
                let name = var_name(n);
                n += 1;
                if !facts.names.contains(&name) {
                    break name;
                }
            };
            if self.classes[r].mask != EVERY {
                sig.bounds.insert(v.clone(), self.classes[r].mask);
            }
            self.classes[r].name = Some(name);
            mine_seen.insert(v);
        }
        // A type variable that does not reach the signature means nothing outside it.
        for &r in &own {
            if self.classes[r].name.is_none()
                && let Some(t) = &self.classes[r].resolved
                && t.vars.iter().any(|v| class_id(v).is_some())
            {
                self.classes[r].resolved = Some(Ty::dynamic());
            }
        }
        sig.own = mine_seen;
        sig.named = n;
        sig.facts = Default::default();
        sig.note_held();
        self.level -= 1;
        Arc::new(sig)
    }

    /// Joins each class of the function of `level` with what a test of it gave
    /// ([`Class::narrowed_to`]) where either of the two takes a carrier by now: a class of
    /// carriers holds no atom, so the test removed none of its values, and the uses of either
    /// restrict both. Two that may still take other values stay apart: the test's need on the
    /// one gives the other at each call.
    ///
    /// A test's class is newer than the class it tests, so the links, taken in the order of
    /// the classes tested, run from older to newer: one pass from the last link joins each
    /// class to a carrier class it leads to, and one from the first joins it to a carrier
    /// class it comes from. Two passes over the links: `O(n log n)` with the merges.
    fn join_narrowed(&mut self, level: usize) {
        let mut from: Vec<usize> = Vec::new();
        for i in 0..self.pending[level].len() {
            let r = self.find(self.pending[level][i]);
            if self.classes[r].level == level && !self.classes[r].narrowed_to.is_empty() {
                from.push(r);
            }
        }
        from.sort_unstable();
        from.dedup();
        let mut links: Vec<(usize, usize, Span)> = Vec::new();
        for &r in &from {
            self.touch(r);
            let to = std::mem::take(&mut self.classes[r].narrowed_to);
            links.extend(to.into_iter().map(|(j, span)| (r, j, span)));
        }
        let n = links.len();
        let mut joined = vec![false; n];
        for i in (0..n).rev().chain(0..n) {
            let (k, j, span) = links[i];
            let (k, j) = (self.find(k), self.find(j));
            if joined[i]
                || (k != j
                    && self.classes[k].mask & OTHER != 0
                    && self.classes[j].mask & OTHER != 0)
            {
                continue;
            }
            joined[i] = true;
            let (kt, jt) = (
                Ty::of_mask(self.classes[k].mask),
                Ty::of_mask(self.classes[j].mask),
            );
            if !self.merge(k, j, "the value tested", span) {
                let (kt, jt) = (self.show(&kt), self.show(&jt));
                let menu = [format!(
                    "repair: test for a type that the later uses take, or convert the value \
                     where it is used as {jt}"
                )];
                self.error_offering(
                    span,
                    format!(
                        "the value this test leaves is used as {jt}, and the value it tests as \
                         {kt}: the test narrows the value it tests, so both uses are of one \
                         value, and no value is both"
                    ),
                    menu,
                );
            }
        }
    }

    /// Merges classes `a` and `b`, as `what` at `span` requires; false, changing nothing, if
    /// they share no carrier. The shorter lists move into the longer, so that each item
    /// moves `O(log n)` times.
    fn merge(&mut self, a: usize, b: usize, what: &str, span: Span) -> bool {
        let (a, b) = (self.find(a), self.find(b));
        if a == b {
            return true;
        }
        let m = self.classes[a].mask & self.classes[b].mask;
        if m == 0 {
            return false;
        }
        self.touch(a);
        self.touch(b);
        let (root, child) = match self.classes[a].rank < self.classes[b].rank {
            true => (b, a),
            false => (a, b),
        };
        if self.classes[a].rank == self.classes[b].rank {
            self.classes[root].rank += 1;
        }
        // Each use of one class is checked on what flowed into the other.
        let mut cross: Vec<(Need, Ty, Span)> = Vec::new();
        for (x, y) in [(a, b), (b, a)] {
            for (_, n) in &self.classes[x].uses {
                for (t, at) in &self.classes[y].flowed {
                    cross.push((n.clone(), t.clone(), *at));
                }
            }
        }
        let lowered = self.classes[a].level != self.classes[b].level;
        let mut lits = std::mem::take(&mut self.classes[child].lits);
        let mut reasons = std::mem::take(&mut self.classes[child].reasons);
        let mut uses = std::mem::take(&mut self.classes[child].uses);
        let mut known = std::mem::take(&mut self.classes[child].known);
        let mut orders = std::mem::take(&mut self.classes[child].orders);
        let data = self.classes[child].data;
        let mut flowed = std::mem::take(&mut self.classes[child].flowed);
        let level = self.classes[child].level;
        let binder = self.classes[child].binder;
        let generic = self.classes[child].generic;
        let given = self.classes[child].given;
        let narrowed_to = std::mem::take(&mut self.classes[child].narrowed_to);
        let narrows = self.classes[child].narrows;
        self.classes[child].parent = root;
        let c = &mut self.classes[root];
        c.generic &= generic;
        // Its values are no longer those of one `min` or `max` use only.
        c.order_of = None;
        c.given &= given;
        c.narrowed_to.extend(narrowed_to);
        c.narrows |= narrows;
        c.binder = match (c.binder, binder) {
            (Some(a), Some(b)) if b.1.start <= a.1.start && a.1.end <= b.1.end => Some(b),
            (a, b) => a.or(b),
        };
        if c.uses.len() < uses.len() {
            std::mem::swap(&mut c.uses, &mut uses);
            std::mem::swap(&mut c.known, &mut known);
            std::mem::swap(&mut c.orders, &mut orders);
        }
        // A `min` or `max` use of a site both classes hold is joined into one. Each was
        // checked on what flowed into the other class above, so nothing is checked again.
        for (seq, mut n) in uses {
            if let NeedKind::Order {
                word, first, other, ..
            } = &mut n.kind
            {
                match c.orders.entry((word.clone(), *first, n.span)) {
                    Entry::Occupied(at) => {
                        if let NeedKind::Order { other: kept, .. } = &mut c.uses[*at.get()].1.kind {
                            *kept = one_shape_per_length(&kept.union(other));
                        }
                        continue;
                    }
                    Entry::Vacant(at) => {
                        at.insert(c.uses.len());
                    }
                }
            }
            c.uses.push((seq, n));
        }
        // The uses kept first keep their results, as a scan of the joined `uses` finds them.
        for (key, result) in known {
            c.known.entry(key).or_insert(result);
        }
        c.data |= data;
        if c.flowed.len() < flowed.len() {
            std::mem::swap(&mut c.flowed, &mut flowed);
        }
        c.flowed.extend(flowed);
        if c.lits.len() < lits.len() {
            std::mem::swap(&mut c.lits, &mut lits);
        }
        c.lits.extend(lits);
        if c.reasons.len() < reasons.len() {
            std::mem::swap(&mut c.reasons, &mut reasons);
        }
        c.reasons.extend(reasons);
        c.reasons.push(Reason {
            span,
            what: what.into(),
            takes: None,
        });
        c.mask = m;
        c.level = c.level.min(level);
        if lowered {
            let mut vars = Vars::default();
            for (_, n) in &self.classes[root].uses {
                n.vars_in(&mut vars);
            }
            let level = self.classes[root].level;
            self.lower(vars.order, level);
        }
        for (n, t, at) in &cross {
            self.check_on(n, t, *at);
        }
        true
    }

    /// Records that the use at `span` needs `kind` of each value of class `k`, and gives what
    /// the use gives: a new class at `k`'s level if `gives`, else nothing. The use is checked
    /// now on each tuple and function that flowed into the class; on the type the class
    /// takes, if that is not a type variable, when its function ends; else at each call of
    /// that function, on the type the call binds the variable to. A use the class has met
    /// already gives what it gave then, since what a use gives depends only on the type it is
    /// made of; so a call met twice checks its needs once.
    fn need(&mut self, k: usize, kind: NeedKind, gives: bool, span: Span) -> Ty {
        let r = self.find(k);
        let data = matches!(kind, NeedKind::Data(_));
        if data && self.classes[r].data {
            return Ty::empty();
        }
        let key = (kind, gives);
        if let Some(result) = self.classes[r].known.get(&key) {
            return result.clone();
        }
        let (kind, _) = key;
        if let NeedKind::Order {
            word, first, other, ..
        } = &kind
            && let Some(&i) = self.classes[r].orders.get(&(word.clone(), *first, span))
        {
            return self.join_order(r, i, &kind, other, span);
        }
        let level = self.classes[r].level;
        let result = gives.then(|| {
            let j = self.class();
            self.classes[j].level = level;
            self.classes[j].given = true;
            Ty::var(format!("${j}").into())
        });
        let need = Need {
            on: Ty::var(format!("${r}").into()),
            kind,
            result: result.clone(),
            span,
        };
        let mut vars = Vars::default();
        need.vars_in(&mut vars);
        self.lower(vars.order, level);
        let flowed = self.classes[r].flowed.clone();
        self.touch(r);
        self.needs += 1;
        let seq = self.needs;
        let class = &mut self.classes[r];
        if let NeedKind::Order { word, first, .. } = &need.kind {
            let at = class.uses.len();
            class.orders.insert((word.clone(), *first, span), at);
        }
        class.uses.push((seq, need.clone()));
        let given = result.clone().unwrap_or_else(Ty::empty);
        class.known.insert((need.kind.clone(), gives), given);
        class.data |= data;
        for (t, at) in &flowed {
            self.check_on(&need, t, *at);
        }
        result.unwrap_or_else(Ty::empty)
    }

    /// Joins the `min` or `max` use `kind`, at `span`, whose other operand is `other`, into
    /// the use of class `r` at index `i` of its uses, which has the same word and side: the
    /// use's other operand becomes the union of theirs, joined one shape per length as `min`
    /// and `max` join their operands (DESIGN.md sec:reduction, item 5), so a value checked
    /// against it is checked as against each. A chain of functions that passes a parameter
    /// on to `min` with a new literal tuple at each link then records one use, not one per
    /// link before it. The values that flowed into the class are checked against `kind`,
    /// which is what is new. Gives what the kept use gives.
    fn join_order(&mut self, r: usize, i: usize, kind: &NeedKind, other: &Ty, span: Span) -> Ty {
        let (on, result) = (
            &self.classes[r].uses[i].1.on,
            &self.classes[r].uses[i].1.result,
        );
        let (on, result) = (on.clone(), result.clone());
        let NeedKind::Order { other: old, .. } = &self.classes[r].uses[i].1.kind else {
            unreachable!("`orders` indexes `NeedKind::Order` uses")
        };
        let joined = one_shape_per_length(&old.union(other));
        if joined == *old {
            return result.unwrap_or_else(Ty::empty);
        }
        let need = Need {
            on,
            kind: kind.clone(),
            result: result.clone(),
            span,
        };
        let mut vars = Vars::default();
        need.vars_in(&mut vars);
        let level = self.classes[r].level;
        self.lower(vars.order, level);
        self.touch(r);
        let class = &mut self.classes[r];
        if let NeedKind::Order { other: old, .. } = &mut class.uses[i].1.kind {
            *old = joined;
        }
        let flowed = class.flowed.clone();
        for (t, at) in &flowed {
            self.check_on(&need, t, *at);
        }
        result.unwrap_or_else(Ty::empty)
    }

    /// Checks the use `n` of a class on `t`, which flowed into the class at `span` or which
    /// the class takes: what the use gives flows into the class of its result.
    fn check_on(&mut self, n: &Need, t: &Ty, span: Span) {
        let from = self.info.errors.len();
        let start = self.need_passed.len();
        let got = self.meet(n, t, &mut Binds::new(), span);
        // A use checked on a value that flowed in has no call whose argument gave the atoms.
        let passed: Vec<NeedPass> = self.need_passed.drain(start..).collect();
        for (inner, _, k) in passed {
            let atoms = Ty::set(k);
            let message = format!(
                "{inner} does not take {atoms}: an atom an argument holds passes by a call to the \
                 call's result, but this value reaches {inner} as no argument of a call, so the \
                 atom has nowhere to go"
            );
            let menu = [format!(
                "repair: handle {atoms} before the value reaches {inner}, with `else` or `match`"
            )];
            self.error_offering(n.span, message, menu);
        }
        if let Some(r) = &n.result
            && let Some(k) = self.class_of_ty(r)
            && !self.flow(k, &got, "this use", n.span)
        {
            let shown = self.show(r);
            let got = self.text(&got);
            let menu = [
                "repair: declare the types of the values this use reads, so that it is checked \
                 where it is written"
                    .to_string(),
            ];
            self.error_offering(
                n.span,
                format!(
                    "this use gives {got}, not {shown}: its result flows into a value that \
                     other uses have already made {shown}"
                ),
                menu,
            );
        }
        self.also(from, n.span, |_| "this use needs it here".to_string());
    }

    /// The use `n`, of a value of `on`, checked at `span` where the variables of the
    /// signature that holds it are bound as `binds`; a variable left unbound is unknown.
    /// Gives what the use gives; `binds` are as they were.
    fn meet(&mut self, n: &Need, on: &Ty, binds: &mut Binds, span: Span) -> Ty {
        let mut b = |ck: &Self, t: &Ty| bound(t, binds, |v| ck.is_class(v));
        let on = b(self, on);
        self.replaying += 1;
        let has_vars = |t: &Ty| {
            let f = t.var_facts();
            !f.classes.is_empty() || !f.names.is_empty()
        };
        self.need_args = match &n.kind {
            NeedKind::Call { positional, .. } => Some(positional.iter().map(has_vars).collect()),
            NeedKind::Index(t) => Some(vec![has_vars(t)]),
            _ => None,
        };
        let start = self.refused.len();
        let out = match &n.kind {
            NeedKind::Component { i, key } => self.at_index(&on, *i, Arg::of(key.clone()), span),
            NeedKind::Index(k) => self.at_key(&on, Arg::of(b(self, k)), span),
            NeedKind::Destructure { i, n } => self.component(&on, *i, *n, span),
            NeedKind::Call {
                what,
                positional,
                named,
                curry,
            } => {
                let args = Args {
                    positional: positional
                        .iter()
                        .map(|t| ArgSrc::Got(Box::new(Arg::of(b(self, t)))))
                        .collect(),
                    named: named
                        .iter()
                        .map(|(m, t)| (m.to_string(), ArgSrc::Got(Box::new(Arg::of(b(self, t))))))
                        .collect(),
                };
                self.call_found(&on, what, args, *curry, span)
            }
            NeedKind::Data(what) => {
                self.data(&on, what, span, span);
                Ty::empty()
            }
            NeedKind::Sum => self.sum(Arg::of(on.clone()), span),
            NeedKind::NoInt(d) => {
                self.no_int(&on, d, span);
                Ty::empty()
            }
            NeedKind::InDomain { .. } => Ty::empty(),
            NeedKind::Into { what, ty } => {
                self.into(&on, ty, what, span);
                Ty::empty()
            }
            NeedKind::Payload { atom, slot } => self.payload(&on, atom, slot, span),
            NeedKind::Narrow(narrow) => self.narrowed(&on, narrow, span),
            NeedKind::Order {
                what,
                word,
                other,
                first,
            } => {
                let other = b(self, other);
                let (x, y) = if *first { (&on, &other) } else { (&other, &on) };
                self.min_max_tuples(what, &word_sig(word), x, y, span)
            }
        };
        self.replaying -= 1;
        self.need_args = None;
        // Each argument the use's applications passed atoms of by is named by the variables
        // of its type in the need: an argument of no variable gives them to no call.
        for (what, i, k) in self.refused.drain(start..).collect::<Vec<_>>() {
            let t = match &n.kind {
                NeedKind::Call { positional, .. } => positional.get(i),
                NeedKind::Index(t) if i == 0 => Some(t),
                _ => None,
            };
            let mut vars = Vars::default();
            if let Some(t) = t {
                t.vars_in(&mut vars);
            }
            self.need_passed.push((what, vars.order, k));
        }
        out
    }

    /// Checks the needs of `sig`, named `what`, at a call at `span` that binds its variables
    /// as `binds`, in the order its body met them; binds what each use gives. A need on a
    /// value of type `_` fails, since the value may be any.
    ///
    /// A need met again inside its own check, as by `w(w)` for `w(f) = f(f)`, on the same type
    /// up to its variables, gives the least result: the inner use first gives nothing, and if
    /// the check took that, it runs once more with the inner use giving what the first run
    /// gave. The second result must lie within the first, which then holds every value the
    /// use may give; otherwise the result is not settled and it is an error. Met again on
    /// another type, it is an error, since the types could grow without end. So the checks
    /// nest at most as deep as the program has needs.
    ///
    /// A need on a variable of `defer`, or on what such a need gives, is left: the needs left
    /// are given back.
    fn replay(
        &mut self,
        what: &str,
        needs: &[Need],
        binds: &mut Binds,
        mut defer: BTreeSet<Arc<str>>,
        span: Span,
    ) -> Vec<Need> {
        let mut left = Vec::new();
        for n in needs {
            // A need on a parameter is checked with the call's arguments, by [`Self::floors_at`].
            if matches!(n.kind, NeedKind::InDomain { .. }) {
                continue;
            }
            if !defer.is_empty() {
                let mut vars = Vars::default();
                n.vars_in(&mut vars);
                if vars.order.iter().any(|v| defer.contains(v)) {
                    defer.extend(vars.order);
                    left.push(n.clone());
                    continue;
                }
            }
            let from = self.info.errors.len();
            let on = bound(&n.on, binds, |v| self.is_class(v));
            let shape = bound(&on, &mut Binds::new(), |v| self.is_class(v));
            let got = match self.open.iter_mut().find(|o| o.span == n.span) {
                _ if on.dynamic => {
                    self.any(&format!("{what}, which needs this of its argument,"), span);
                    Ty::empty()
                }
                Some(o) if o.shape == shape => {
                    o.used = true;
                    o.result.clone()
                }
                Some(o) => {
                    let t = o.shape.clone();
                    let (on, t) = (self.text(&on), self.text(&t));
                    let menu = [
                        "repair: declare the types of the function's parameters, so that the call \
                         inside it is checked at those types"
                            .to_string(),
                    ];
                    self.error_offering(
                        span,
                        format!(
                            "{what} needs this of its argument again inside its own check, on \
                             {on} where it was {t}: checking it there would need the same check \
                             at a larger type again, without end, so the checker stops here"
                        ),
                        menu,
                    );
                    Ty::empty()
                }
                None => {
                    // `meet` gives `binds` back as they were, so the second run starts from
                    // the same ones.
                    let errors = self.info.errors.len();
                    self.open.push(Open {
                        span: n.span,
                        shape,
                        result: Ty::empty(),
                        used: false,
                    });
                    let passing = self.need_passed.len();
                    let mut got = self.meet(n, &on, binds, span);
                    let used = self.open.last().is_some_and(|o| o.used);
                    if used && !got.is_empty() {
                        self.info.errors.truncate(errors);
                        self.need_passed.truncate(passing);
                        let o = self.open.last_mut().expect("the need just pushed");
                        o.result = got.clone();
                        let first = got;
                        got = self.meet(n, &on, binds, span);
                        if !self.subtype(&got, &first) {
                            let why = got.refused(&first);
                            let (got, first) = (self.text(&got), self.text(&first));
                            let menu = [
                                "repair: declare the result type of the function, so that its \
                                 body is checked against it"
                                    .to_string(),
                            ];
                            self.error_offering(
                                span,
                                format!(
                                    "{what} needs this of its argument again inside its own \
                                     check, and the result is not settled: it gives {got} \
                                     where the use inside gave {first}, so the use has no one \
                                     result the checker can find{why}"
                                ),
                                menu,
                            );
                        }
                    }
                    self.open.pop();
                    got
                }
            };
            // What the use gives is within its result: a variable there joins it, as for an
            // argument, and one it leaves unbound gives nothing.
            if let Some(r) = &n.result {
                if !self.sub(&got, r, binds) {
                    let why = got.refused(r);
                    let (got, r) = (self.text(&got), self.text(r));
                    let menu = [format!(
                        "repair: change the argument, so that {what} gives a value of {r} here"
                    )];
                    self.error_offering(
                        span,
                        format!(
                            "{what} gives {got} here, which is not {r}: the use requires a value \
                             of {r}{why}"
                        ),
                        menu,
                    );
                }
                for v in &r.vars {
                    binds.entry(v.clone()).or_insert_with(Ty::empty);
                }
            }
            self.also(from, n.span, |_| {
                format!("{what} needs this of its argument here")
            });
        }
        left
    }

    /// Checks that a value of `on` may be passed, by `what` at `span`, at a parameter of the
    /// closed type `ty`.
    fn into(&mut self, on: &Ty, ty: &Ty, what: &str, span: Span) {
        for piece in on.pieces() {
            let ok = match self.class_of(&piece) {
                _ if piece == Piece::Dyn => ty.dynamic,
                _ if matches!(piece, Piece::Var(_)) && self.class_of(&piece).is_none() => true,
                Some(k) => {
                    let ok = self.restrict(k, mask_of(ty), what, span);
                    let kind = NeedKind::Into {
                        what: what.into(),
                        ty: ty.clone(),
                    };
                    self.need(k, kind, false, span);
                    ok
                }
                None => match &piece {
                    Piece::Fn(s) if !s.needs.is_empty() => {
                        self.fit_needs(s, ty, &mut Binds::new(), what, span)
                    }
                    _ => self.sub(&piece.ty(), ty, &mut Binds::new()),
                },
            };
            if !ok {
                let p = self.show(&piece.ty());
                let why = on.of_piece(&piece).refused(ty);
                let ty = self.text(ty);
                let menu = [
                    format!("repair: pass {what} a value of {ty}"),
                    format!(
                        "repair: test the value with `is` first, as `if v is {ty} {{ … }}`, or \
                         handle the values that are not {ty} with `else` or `match`"
                    ),
                ];
                self.error_offering(
                    span,
                    format!(
                        "{what} does not take {p}, which is not {ty}: {what} takes only values of \
                         {ty}{why}"
                    ),
                    menu,
                );
            }
        }
    }

    /// Whether a function of `s`, whose body has needs, may be passed, by `what` at `span`,
    /// at a parameter of type `p`: `s` applied to the parameters of `p`'s one function type
    /// gives its result. The application reports its own errors.
    fn fit_needs(
        &mut self,
        s: &Arc<Sig>,
        p: &Ty,
        binds: &mut Binds,
        what: &str,
        span: Span,
    ) -> bool {
        let mut bare = (**s).clone();
        bare.needs = Vec::new();
        let [q] = p.fns.iter().collect::<Vec<_>>()[..] else {
            return false;
        };
        if !self.sub(&Ty::func(Arc::new(bare)), p, binds) {
            return false;
        }
        let q = q.replace(binds);
        let from = self.info.errors.len();
        let mut ok = true;
        for a in &q.arrows {
            let args = a.params.iter().map(|t| Some(Arg::of(t.clone()))).collect();
            let (r, _) = self.apply(what, s, args, false, span);
            ok &= self.subtype(&r, &a.result);
        }
        ok || self.info.errors.len() > from
    }

    /// The values of `t` flow into class `k`: a class merges with it, a carrier restricts it
    /// to that carrier, and a tuple or a function to other values; atoms change nothing, and
    /// a value of type `_`, which may be any, does not flow.
    fn flow(&mut self, k: usize, t: &Ty, what: &str, span: Span) -> bool {
        for p in t.pieces() {
            let ok = match (self.class_of(&p), p.carrier()) {
                (Some(j), _) => self.merge(k, j, what, span),
                _ if p == Piece::Dyn => false,
                _ if matches!(p, Piece::Var(_)) || p.is_atoms() => true,
                (None, Some(c)) => self.restrict(k, c.bit(), what, span),
                (None, None) => self.restrict(k, OTHER, what, span),
            };
            if !ok {
                return false;
            }
            if matches!(p, Piece::Tuple(_) | Piece::Fn(_)) {
                let r = self.find(k);
                let t = p.ty();
                let uses: Vec<Need> = self.classes[r]
                    .uses
                    .iter()
                    .map(|(_, n)| n.clone())
                    .collect();
                self.touch(r);
                self.classes[r].flowed.push((t.clone(), span));
                for n in &uses {
                    self.check_on(n, &t, span);
                }
            }
        }
        true
    }

    /// Binds the names of the pattern `p`, matched on a value of `v`, from the binder `next`
    /// on, in the order the resolver gave them: each to what the payloads of `v`'s atoms of
    /// the pattern's name hold there.
    ///
    /// The patterns nest as deep as the text, so the walk keeps its own stack: each pattern
    /// being matched, its atom, the type it is matched on (`None` for `v`), and its next slot.
    fn bind_pattern(&mut self, p: &Pattern, v: &Ty, mut next: usize) {
        let atom_of = |p: &Pattern| -> Arc<str> {
            let Pattern::Atom { name, .. } = p else {
                unreachable!(
                    "name resolution accepts no pattern but an atom pattern before the checker reads the program"
                )
            };
            name.as_str().into()
        };
        let mut stack: Vec<(&Pattern, Arc<str>, Option<Ty>, usize)> =
            vec![(p, atom_of(p), None, 0)];
        while let Some((p, atom, on, i)) = stack.last_mut() {
            let Pattern::Atom {
                fields,
                items,
                span,
                ..
            } = *p
            else {
                unreachable!(
                    "name resolution accepts no pattern but an atom pattern before the checker reads the program"
                )
            };
            let (slot, sub) = match fields.get(*i) {
                Some((f, sub)) => (Slot::Field(f.as_str().into()), sub.as_ref()),
                None => match items.get(*i - fields.len()) {
                    Some(sub) => (Slot::Item(*i - fields.len()), Some(sub)),
                    None => {
                        stack.pop();
                        continue;
                    }
                },
            };
            *i += 1;
            let t = self.payload(on.as_ref().unwrap_or(v), atom, &slot, *span);
            match sub {
                Some(sub) => stack.push((sub, atom_of(sub), Some(t), 0)),
                None => {
                    self.env.insert(next, t);
                    next += 1;
                }
            }
        }
    }

    /// What the payloads of the atoms named `atom` among the values of `v` hold at `slot`,
    /// for a pattern at `span`: what the shapes they were built with hold there, what a need
    /// gives on a type variable's class, and the unknown where it is not known.
    fn payload(&mut self, v: &Ty, atom: &Arc<str>, slot: &Slot, span: Span) -> Ty {
        let mut out = match v.shapes(atom) {
            Some(ss) => Ty::union_all(ss.iter().filter_map(|s| s.at(slot))),
            None => Ty::dynamic(),
        };
        if v.dynamic {
            out = out.union(&Ty::dynamic());
        }
        for x in &v.vars {
            let t = match self.class_of(&Piece::Var(x.clone())) {
                Some(k) => {
                    let kind = NeedKind::Payload {
                        atom: atom.clone(),
                        slot: slot.clone(),
                    };
                    self.need(k, kind, true, span)
                }
                None => Ty::dynamic(),
            };
            out = out.union(&t);
        }
        out
    }

    /// The facts `x == #a` makes on the name `x` where it holds and where it fails, either
    /// side written first, and swapped for `!=`: `x` is `#a` where they are equal and keeps
    /// its other values where not, as `x is #a` does (DESIGN.md sec:type_resolution: an `==`
    /// or `!=` handles the atom). Any other condition makes none.
    fn atom_eq(&mut self, e: &Expr) -> (Facts, Facts) {
        let ExprKind::Binary(op @ ("==" | "!="), a, b) = &e.kind else {
            return (Facts::new(), Facts::new());
        };
        let (name, atom) = match (&a.kind, &b.kind) {
            (ExprKind::Name(_), ExprKind::Atom(n)) => (a, n),
            (ExprKind::Atom(n), ExprKind::Name(_)) => (b, n),
            _ => return (Facts::new(), Facts::new()),
        };
        let (Some(Ref::Bound(ids)), Some((Some(v), _))) =
            (self.t.res.uses.get(&name.span), self.seen.get(&name.span))
        else {
            return (Facts::new(), Facts::new());
        };
        if ids.len() != 1 {
            return (Facts::new(), Facts::new());
        }
        let (id, v) = (ids[0], v.clone());
        let t = Ty::set(KType::atom(atom));
        let yes = Facts::from([(id, v.meet(&t), e.span)]);
        let no = Facts::from([(id, self.narrowed(&v, &Narrow::Not(t), e.span), e.span)]);
        match *op == "==" {
            true => (yes, no),
            false => (no, yes),
        }
    }

    /// What the test at `span` leaves of `v` where it fails, as `narrow` says. A type variable
    /// of a class a need gave ([`Class::given`]) leaves what a need gives, so `args[k] else ""`
    /// in the body of `r(fs, args, k)` holds no `#notFound` at a call that binds `args` to
    /// `CommandLine` (rule 3 of sec:type_resolution). One of a class that may still take other
    /// values leaves a class of its own the same way, joined back where either of the two
    /// takes a carrier ([`Ck::join_narrowed`]); any other variable is kept whole.
    fn narrowed(&mut self, v: &Ty, narrow: &Narrow, span: Span) -> Ty {
        let mut out = match narrow {
            Narrow::Loose => v.without_loose(),
            Narrow::Atom(name) => {
                let mut rest = v.diff(&Ty::set(any_payload(name)));
                rest.payloads.remove(name.as_ref());
                rest
            }
            Narrow::Not(t) => v.diff_with(t, &|w| self.stale(w)),
        };
        for x in &v.vars {
            let Some(k) = self.class_of(&Piece::Var(x.clone())).map(|k| self.find(k)) else {
                continue;
            };
            let given = self.classes[k].given;
            if !given && self.classes[k].mask & OTHER == 0 {
                continue;
            }
            out.vars.remove(x);
            let left = self.need(k, NeedKind::Narrow(narrow.clone()), true, span);
            // A class that may still take other values may yet take a carrier, and so hold
            // no atom: what the test gives then joins it ([`Ck::join_narrowed`]).
            if (!given || self.classes[k].narrows)
                && let Some(j) = self.class_of_ty(&left)
                && !self.classes[k].narrowed_to.iter().any(|&(i, _)| i == j)
            {
                self.touch(k);
                self.classes[k].narrowed_to.push((j, span));
                self.touch(j);
                self.classes[j].narrows = true;
            }
            out = out.union(&left);
        }
        out
    }

    /// `x ^ n` on an `int` `x` needs `n : int[0..]`, decided from the interval of `n`'s
    /// expression or the listed `int` values of its type. A class's values are not known here:
    /// an exponent of a type variable takes its ints at least 0 ([`Self::floor`]), and a base
    /// of one, under an exponent not shown to be at least 0, takes no int (CHK-need-bound).
    fn exponent(&mut self, x: &Arg<'a>, n: &Arg<'a>, e: &'a Expr, span: Span) {
        let int = KType::int();
        let ns = &n.ty.set & &int;
        let x_int = !(&x.ty.set & &int).is_empty();
        let x_generic = !x.ty.vars.is_empty();
        if !n.ty.vars.is_empty() && (x_int || x_generic) {
            let d = IntDomain {
                what: "`^` on an int takes an exponent in int[0..]".into(),
                below_two_pow: None,
            };
            self.floor(&n.ty, e, d, span);
        }
        if ns.is_empty() {
            return;
        }
        let (ints, narrowed) = self.ints_here(e);
        let at_least_zero =
            ints.is_subset(&IntervalSet::range(End::of(0), PosInf)) || listed_at_least_zero(&ns);
        if !at_least_zero && x_generic {
            let d = IntDomain {
                what: "`^` with an exponent not shown to be at least 0 takes no int base".into(),
                below_two_pow: None,
            };
            self.no_int_vars(&x.ty, &d, x.at.unwrap_or(span));
        }
        if !at_least_zero && x_int {
            let shown = match narrowed {
                true => format!("int{ints}"),
                false => self.show(&Ty::set(ns)),
            };
            let mut notes = Vec::new();
            if narrowed {
                notes.extend(self.deciding_notes(e));
            }
            notes.extend(self.derive(&[n.at.unwrap_or(span)]));
            notes.extend(exponent_repairs(span));
            self.error_with(
                span,
                format!(
                    "`^` on an int needs an exponent of at least 0, and this one is {shown}: an \
                     int raised to a negative power is a fraction, not an int"
                ),
                notes,
            );
        }
    }

    /// Records that the use at `span` takes the ints of the operand `e`, of type `t`, which
    /// holds a type variable, in the domain `d` (CHK-need-bound): nothing, when the tests the
    /// walk is in show it; a need of the function on the parameter `e` names, checked at each
    /// call with the caller's ints ([`Self::floors_at`]); else no int of the variables' values
    /// outside the domain.
    fn floor(&mut self, t: &Ty, e: &'a Expr, d: IntDomain, span: Span) {
        if ints_in(&d, &self.ints_here(e).0) {
            return;
        }
        match self.open_param(e) {
            // A trial application is undone; the application that stays records the need.
            Some(_) if self.trying => {}
            Some(id) => self.floor_on(
                id,
                Need {
                    on: Ty::empty(),
                    kind: NeedKind::InDomain {
                        domain: d,
                        param: 0,
                        via: None,
                    },
                    result: None,
                    span,
                },
            ),
            None => self.no_int_vars(t, &d, e.span),
        }
    }

    /// Records the [`NeedKind::InDomain`] need `n` on the open parameter `id`. The domains are
    /// nested, `int[0..]` holding every `int[0..<2 ^ w]` and a smaller `w` the smaller domain,
    /// so one need per binder decides each call: the smallest domain, from its first use.
    fn floor_on(&mut self, id: usize, n: Need) {
        let width = |n: &Need| match &n.kind {
            NeedKind::InDomain { domain, .. } => domain.below_two_pow.clone(),
            _ => None,
        };
        let smaller = match (self.floors.get(&id).map(width), width(&n)) {
            (None, _) => true,
            (Some(None), Some(_)) => true,
            (Some(Some(old)), Some(new)) => {
                new.0.surface_cmp(&old.0) == Some(std::cmp::Ordering::Less)
            }
            _ => false,
        };
        if smaller {
            self.floors.insert(id, n);
        }
    }

    /// The binder of the parameter of no declared type of a function being checked that `e`
    /// names, through names bound to names: the value of `e` is the caller's argument.
    fn open_param(&self, mut e: &'a Expr) -> Option<usize> {
        let mut seen = HashSet::new();
        loop {
            let ExprKind::Name(_) = &e.kind else {
                return None;
            };
            let id = match self.t.res.uses.get(&e.span) {
                Some(Ref::Bound(ids)) if ids.len() == 1 => ids[0],
                _ => return None,
            };
            if self.open_params.contains(&id) {
                return Some(id);
            }
            if !seen.insert(id) {
                return None;
            }
            e = self.facts.get(&id)?;
        }
    }

    /// Checks that a value of `t` holds no int, or only ints listed in the domain `d`, as its
    /// use at `span` needs (CHK-need-bound): a class takes the need on each of its values.
    fn no_int(&mut self, t: &Ty, d: &IntDomain, span: Span) {
        let ints = &t.set & &KType::int();
        if !ints.is_empty() && !listed_in(d, &ints) {
            let shown = self.show(&Ty::set(ints));
            let what = &d.what;
            let domain = domain_text(d);
            self.error_offering(
                span,
                format!(
                    "{what}, and this value may be {shown}: the checker cannot show that it lies \
                     in {domain}"
                ),
                domain_repairs(&domain),
            );
        }
        self.no_int_vars(t, d, span);
        if t.dynamic {
            self.any(&d.what, span);
        }
    }

    /// The need of [`Self::no_int`] on each type variable of `t`: on a class, recorded and
    /// checked on what flows into it; on its type, if it has one by now.
    fn no_int_vars(&mut self, t: &Ty, d: &IntDomain, span: Span) {
        for v in &t.vars {
            let k = class_id(v).filter(|&k| k < self.classes.len());
            let Some(r) = k.map(|k| self.find(k)) else {
                let what = &d.what;
                let domain = domain_text(d);
                self.error_offering(
                    span,
                    format!(
                        "{what}, and this value has the type `{v}`, which stands \
                         for whatever type the caller passes and may be any int: the checker cannot show that it lies in {domain}"
                    ),
                    domain_repairs(&domain),
                );
                continue;
            };
            match self.classes[r].resolved.clone() {
                Some(t) => self.no_int(&t, d, span),
                None => {
                    self.need(r, NeedKind::NoInt(d.clone()), false, span);
                }
            }
        }
    }

    /// `sig` with the [`NeedKind::InDomain`] needs recorded on its parameters, whose
    /// binders are `ids`, at their positions; the parameters are no longer open.
    fn floors_into(&mut self, sig: Arc<Sig>, ids: &[Option<usize>]) -> Arc<Sig> {
        let mut needs = Vec::new();
        for (j, id) in ids.iter().enumerate() {
            let Some(id) = id else { continue };
            self.open_params.remove(id);
            if let Some(mut n) = self.floors.remove(id) {
                if let NeedKind::InDomain { param, .. } = &mut n.kind {
                    *param = j;
                }
                needs.push(n);
            }
        }
        if needs.is_empty() {
            return sig;
        }
        let mut s = (*sig).clone();
        s.facts = Default::default();
        s.needs.extend(needs);
        Arc::new(s)
    }

    /// Checks each [`NeedKind::InDomain`] need of `sig`, called as `what` at `span`, on the
    /// argument at its parameter (CHK-need-bound): from the interval of the argument's
    /// expression and the listed ints of its type, as `^`'s exponent is. A parameter of no
    /// declared type of the function the call is in takes the need on, with the link of the
    /// call; a value of another type variable takes no int outside the domain. The parameters
    /// `leaving` are left to the function a partial call gives.
    fn floors_at(
        &mut self,
        what: &str,
        sig: &Sig,
        args: &[Option<Arg<'a>>],
        leaving: &[usize],
        span: Span,
    ) {
        let int = KType::int();
        for n in &sig.needs {
            let NeedKind::InDomain { domain, param, via } = &n.kind else {
                continue;
            };
            if leaving.contains(param) {
                continue;
            }
            let p = sig
                .params
                .get(*param)
                .map_or("?".into(), |p| p.name.clone());
            let takes = format!("{what} takes `{p}` in {}", domain_text(domain));
            let passed = IntDomain {
                what: takes.as_str().into(),
                below_two_pow: domain.below_two_pow.clone(),
            };
            // The calls that passed the value on, down to the use: O(calls), so made only for an
            // error, never at a call that meets the need.
            let chain = || {
                let mut chain = Vec::new();
                let mut v = via.as_deref();
                while let Some(l) = v {
                    chain.push(Note {
                        span: l.at,
                        text: l.text.to_string(),
                    });
                    v = l.next.as_deref();
                }
                chain.push(Note {
                    span: n.span,
                    text: format!("{} here", domain.what),
                });
                chain
            };
            let Some(a) = args.get(*param).and_then(Option::as_ref) else {
                // A parameter left out takes its default, whose value the call does not show.
                if sig.params.get(*param).is_some_and(|p| p.default.is_some()) {
                    let dom = domain_text(domain);
                    let message = format!(
                        "{takes}, and this call leaves `{p}` out, so `{p}` takes its default, \
                         which the checker cannot show lies in {dom}"
                    );
                    let mut notes = chain();
                    notes.extend(
                        [
                            format!("repair: pass `{p}` in this call, with a value in {dom}"),
                            format!("repair: give `{p}` a default in {dom}"),
                        ]
                        .into_iter()
                        .map(|text| Note { span, text }),
                    );
                    self.error_with(span, message, notes);
                }
                continue;
            };
            let generic = !a.ty.vars.is_empty();
            let ns = &a.ty.set & &int;
            let Some(e) = a.expr else {
                // The check of a need, as of `g(v)` in `ap(g, v) = g(v)`: the type alone.
                if generic {
                    self.no_int_vars(&a.ty, &passed, span);
                }
                if !ns.is_empty() && !listed_in(domain, &ns) {
                    let shown = self.show(&Ty::set(ns));
                    let message = format!("{takes}, and this `{p}` is {shown}{}", outside(domain));
                    let mut notes = chain();
                    notes.extend(passed_repairs(&p, domain, span));
                    self.error_with(span, message, notes);
                }
                continue;
            };
            let at = a.at.unwrap_or(e.span);
            if generic && !ints_in(domain, &self.ints_here(e).0) {
                match self.open_param(e) {
                    Some(_) if self.trying => {}
                    Some(id) => {
                        let name = match &e.kind {
                            ExprKind::Name(name) => name.to_string(),
                            _ => "this value".into(),
                        };
                        let link = Via {
                            at,
                            text: format!("`{name}` is passed on as `{p}` of {what} here").into(),
                            next: via.clone(),
                        };
                        let need = Need {
                            on: Ty::empty(),
                            kind: NeedKind::InDomain {
                                domain: domain.clone(),
                                param: 0,
                                via: Some(Arc::new(link)),
                            },
                            result: None,
                            span: n.span,
                        };
                        self.floor_on(id, need);
                    }
                    None => self.no_int_vars(&a.ty, &passed, at),
                }
            }
            let Some(r) = self.int_range(a, e) else {
                continue;
            };
            if range_in(domain, &r) {
                continue;
            }
            let shown = &r.shown;
            let mut notes = vec![Note {
                span: at,
                text: format!("`{p}` is this argument, {shown}"),
            }];
            if r.narrowed {
                notes.extend(self.deciding_notes(e));
            }
            self.derive_into(&[at], &mut notes);
            notes.extend(chain());
            notes.extend(passed_repairs(&p, domain, span));
            let message = format!("{takes}, and this `{p}` is {shown}{}", outside(domain));
            self.error_with(span, message, notes);
        }
    }

    /// Checks that a value of `t` is data, as `what` at `span` needs (L1.17): it holds no
    /// function at any depth. A function it holds is reported at `span` with the derivation of
    /// the expression at `from`, which gave the value.
    fn data(&mut self, t: &Ty, what: &str, span: Span, from: Span) {
        // A function held in the row of a tuple expression was reported at that tuple, with its
        // derivation: one error for one function, however many tuples and uses it then flows
        // through, each of which meets the same value, so that fixing the error fixes them all.
        if let Some(s) = t.unchecked_function() {
            let s = self.sig_text(s);
            let mut notes = self.derive(&[from]);
            notes.extend(data_repairs(span));
            self.error_with(
                span,
                format!(
                    "{what} takes data, and this value may hold a function, `{s}`: data is a \
                     value that holds no function at any depth"
                ),
                notes,
            );
        } else if let Some(w) = t.held_wide() {
            // `(..)` and `{..}` hold every tuple and struct, those that hold a function too: a
            // block that ends `return h, 1` gives one.
            let notes = data_repairs(span);
            self.error_with(
                span,
                format!(
                    "{what} takes data, and this value, of `{}`, may hold a function: data is a \
                     value that holds no function at any depth, and `{}` holds every value of \
                     its shape, functions too",
                    Ty::set(w.clone()),
                    Ty::set(w)
                ),
                notes,
            );
        }
        // A class, at any depth, needs data of each of its values. A row that holds no class
        // or unknown is not entered; nor is one whose classes were checked as data when it
        // was made, since a class keeps a data need once it has one and a second is nothing.
        // Of such a row only its unknown is reported, once, as each would be at this span.
        // A row shared by many paths is visited once.
        let mut rows = HashSet::new();
        // A payload shape that holds no class or unknown is not entered either, and a shape is
        // shared, so one met again by another path is not entered again.
        let mut shapes = HashSet::new();
        let mut stack = vec![t];
        while let Some(t) = stack.pop() {
            for r in (t.tuples.iter()).filter(|r| r.open() && rows.insert(r.addr())) {
                match r.data() {
                    true if r.dynamic() => self.any(what, span),
                    true => {}
                    false => stack.extend(r.iter()),
                }
            }
            for v in &t.vars {
                if let Some(k) = self.class_of(&Piece::Var(v.clone())) {
                    self.need(k, NeedKind::Data(what.into()), false, span);
                }
            }
            if t.dynamic {
                self.any(what, span);
            }
            // An atom expression does not check its payload as data, since a payload may hold
            // a function (DESIGN.md, `#atom(t)`), so its classes and unknowns are met here.
            let open = t.payloads.values().flatten().flatten().filter(|s| s.open());
            for s in open.filter(|s| shapes.insert(s.as_ptr())) {
                stack.extend(&s.items);
                stack.extend(s.fields.values());
            }
        }
    }

    /// An ordering: two values of one carrier, or two tuples of one length; atoms pass.
    fn compare(&mut self, op: &str, x: Arg<'a>, y: Arg<'a>, span: Span) -> Ty {
        let what = format!("`{op}`");
        if x.ty.tuples.is_empty() && y.ty.tuples.is_empty() {
            return self
                .apply(&what, &op_sig("<"), vec![Some(x), Some(y)], true, span)
                .0;
        }
        let out = self.passing(&x.ty, &what, span);
        let out = out.union(&self.passing(&y.ty, &what, span));
        self.components(&what, &x.ty.without_loose(), &y.ty.without_loose(), span);
        out.union(&Ty::carrier(Carrier::Bool))
    }

    /// Checks that each value of `a` compares with each of `b` (sec:order): two numbers of one
    /// carrier or two values of one other kind, the atoms as data, and two tuples component by
    /// component as far as the shorter goes, since a proper prefix comes first.
    fn components(&mut self, what: &str, a: &Ty, b: &Ty, span: Span) {
        let refuse = |ck: &mut Self, p: &Piece, q: &str| {
            let p = ck.text(&p.ty());
            ck.error(span, format!("{what} does not compare {p} with {q}"));
        };
        for (s, t) in [(a, b), (b, a)] {
            let atoms = !s.atoms().is_empty();
            for p in t.pieces() {
                let ok = match self.class_of(&p) {
                    Some(k) if !s.tuples.is_empty() => self.restrict(k, OTHER, what, span),
                    Some(_) => true,
                    None => match &p {
                        Piece::Dyn => false,
                        Piece::Var(_) | Piece::Tuple(_) => true,
                        _ if !s.tuples.is_empty() => false,
                        _ => !atoms || p.is_atoms() || p.carrier().is_none(),
                    },
                };
                if !ok {
                    let q = if s.tuples.is_empty() {
                        "an atom"
                    } else {
                        "a tuple"
                    };
                    return refuse(self, &p, q);
                }
            }
        }
        for s in &a.tuples {
            for t in &b.tuples {
                for (c, d) in s.iter().zip(t) {
                    self.components(what, c, d, span);
                }
            }
        }
        let rest = |t: &Ty| Ty {
            tuples: Vec::new(),
            ..t.without_atoms()
        };
        let (x, y) = (rest(a), rest(b));
        if !x.is_empty() && !y.is_empty() {
            self.apply(
                what,
                &op_sig("<"),
                vec![Some(Arg::of(x)), Some(Arg::of(y))],
                true,
                span,
            );
        }
    }

    /// `min` or `max`, whose signature is `sig`, applied to `x` and `y`, one of them holding a
    /// tuple (DESIGN.md sec:reduction, item 5): two tuples of one length, each pair of
    /// components two numbers of one kind or two tuples checked the same way, and no atom in a
    /// component. The result is one of the two, so its type joins the tuple shapes of each
    /// length of theirs, and where one is a class and nothing else, it is what the class's use
    /// gives, which a call joins in the same way ([`Ck::order_given`]). The tuple
    /// shapes of one length on each side are joined position by position, so each level is read
    /// once rather than once per pair of shapes, and a pair of component types met again
    /// through shared rows is not read again: the check is linear in the types read.
    fn min_max_tuples(&mut self, what: &str, sig: &Sig, x: &Ty, y: &Ty, span: Span) -> Ty {
        // Called through a function value, a message names the word as well as the value.
        let who = match sig.word.as_deref() {
            Some(w) if what != format!("`{w}`") => format!("{what}, which is `{w}`,"),
            _ => what.to_string(),
        };
        let mut todo = vec![(x.clone(), y.clone())];
        let mut seen = HashSet::new();
        // What the application gives, where one operand is a class and nothing else and the
        // other is closed: what the class's use gives ([`Ck::order_given`]).
        let mut given = None;
        while let Some(pair) = todo.pop() {
            let outer = seen.is_empty();
            if seen.contains(&pair) {
                continue;
            }
            let (a, b) = &pair;
            let atoms = &a.atoms() | &b.atoms();
            let rest = |t: &Ty, open: bool| {
                Ty {
                    tuples: Vec::new(),
                    vars: if open {
                        BTreeSet::new()
                    } else {
                        t.vars.clone()
                    },
                    ..t.without_atoms()
                }
                .is_empty()
            };
            // A class met with a tuple may hold a tuple: it keeps the carriers that are not
            // numbers, as an operand of `<` does (`components`), and records the use, so each
            // value that flows into it, and each call of the function it belongs to, checks
            // this application again with what the class then holds. `open[i]` says that
            // side's variables are all such classes.
            let mut open = [false; 2];
            for (i, (t, u)) in [(a, b), (b, a)].into_iter().enumerate() {
                if u.tuples.is_empty() || t.vars.is_empty() {
                    continue;
                }
                let classes: Option<Vec<usize>> = t
                    .vars
                    .iter()
                    .map(|v| self.class_of(&Piece::Var(v.clone())))
                    .collect();
                let Some(classes) = classes else {
                    continue;
                };
                open[i] = true;
                for k in classes {
                    if !self.restrict(k, OTHER, what, span) {
                        open[i] = false;
                        continue;
                    }
                    let kind = NeedKind::Order {
                        what: what.into(),
                        word: sig.word.clone().unwrap_or_default(),
                        other: u.clone(),
                        first: i == 0,
                    };
                    if outer && u.closed() && self.class_of_ty(t).is_some() {
                        given = Some(self.order_given(k, kind, what, sig, span));
                    } else {
                        self.need(k, kind, false, span);
                    }
                }
            }
            // A side that is classes only, against tuples: the call checks what the classes hold.
            let only = |t: &Ty, open: bool| open && t.tuples.is_empty() && rest(t, true);
            if !atoms.is_empty() {
                let atoms = self.text(&Ty::set(atoms));
                self.error_offering(
                    span,
                    format!(
                        "{who} does not order {atoms} in a tuple: it compares tuples component by \
                         component, and an atom has no order among the numbers; handle it before \
                         {what}"
                    ),
                    [format!(
                        "repair: replace {atoms} by a number before {what}, with `match` or \
                         `else`, as `v else {atoms} -> 0`"
                    )],
                );
            } else if a.tuples.is_empty() && b.tuples.is_empty() {
                self.apply(
                    what,
                    sig,
                    vec![Some(Arg::of(a.clone())), Some(Arg::of(b.clone()))],
                    true,
                    span,
                );
            } else if only(a, open[0]) || only(b, open[1]) {
                // Nothing more to check here.
            } else if a.tuples.is_empty()
                || b.tuples.is_empty()
                || !rest(a, open[0])
                || !rest(b, open[1])
            {
                let (s, t) = (self.text(a), self.text(b));
                self.error_offering(
                    span,
                    format!("{who} does not take {s} and {t}: it takes two tuples or two numbers"),
                    ["repair: pass two numbers, or two tuples of the same length".to_string()],
                );
            } else {
                // The components at each position of the shapes of each length.
                let mut by_len: BTreeMap<usize, [Vec<&[Ty]>; 2]> = BTreeMap::new();
                for (side, t) in [a, b].into_iter().enumerate() {
                    for row in &t.tuples {
                        by_len.entry(row.len()).or_default()[side].push(row);
                    }
                }
                for (n, [s, t]) in by_len {
                    if s.is_empty() || t.is_empty() {
                        let (s, t) = (self.text(a), self.text(b));
                        self.error_offering(
                            span,
                            format!(
                                "{who} does not take {s} and {t}: a tuple of {n} components has \
                                 none of its length to compare with"
                            ),
                            [format!(
                                "repair: pass two tuples of the same length, both of {n} \
                                 components or both of another length"
                            )],
                        );
                        continue;
                    }
                    for i in 0..n {
                        let join = |rows: &[&[Ty]]| Ty::union_all(rows.iter().map(|r| &r[i]));
                        todo.push((join(&s), join(&t)));
                    }
                }
            }
            seen.insert(pair);
        }
        given.unwrap_or_else(|| one_shape_per_length(&x.union(y)))
    }

    /// What `min` or `max`, named `what`, of signature `sig`, gives where one operand is the
    /// class `k` and nothing else and the other, `kind`'s, is closed: a variable whose values
    /// are the join of the two operands' tuple shapes (DESIGN.md sec:reduction, item 5), which
    /// a call binds by checking `kind` on what it binds `k` to. A union would keep each tuple
    /// shape apart and so grow by one shape at each call a chain passes the result through.
    ///
    /// Where `k` is itself what a use of the same word and side gave and holds nothing else,
    /// `min(min(a, c), d)`, the new operand is joined into that use, which then gives the join
    /// of `a`, `c` and `d`, and `c` against `d` is checked here: so a chain of calls that
    /// passes the result on keeps one use, not one per link before it.
    fn order_given(&mut self, k: usize, kind: NeedKind, what: &str, sig: &Sig, span: Span) -> Ty {
        let r = self.find(k);
        let NeedKind::Order {
            word, other, first, ..
        } = &kind
        else {
            unreachable!("`min_max_tuples` makes an `Order` use")
        };
        if let Some((s, key)) = self.classes[r].order_of.clone()
            && key.0 == *word
            && key.1 == *first
        {
            let s = self.find(s);
            if let Some(&i) = self.classes[s].orders.get(&key) {
                let NeedKind::Order { other: old, .. } = &self.classes[s].uses[i].1.kind else {
                    unreachable!("`orders` indexes `NeedKind::Order` uses")
                };
                let old = old.clone();
                let (x, y) = if *first { (&old, other) } else { (other, &old) };
                self.min_max_tuples(what, sig, x, y, span);
                let other = other.clone();
                return self.join_order(s, i, &kind, &other, span);
            }
        }
        let (word, first) = (word.clone(), *first);
        let before = self.classes.len();
        let out = self.need(k, kind, true, span);
        if let Some(j) = self.class_of_ty(&out)
            && j >= before
        {
            self.touch(j);
            self.classes[j].order_of = Some((r, (word, first, span)));
        }
        out
    }

    /// Checks each operand of the bit word or integer machine operation `w` against its domain
    /// (DESIGN.md sec:domains, sec:linalg): `int[0..]` for every one but the `x` of `shl` and
    /// `shr`, `int[0..<2 ^ width]` for the operands read as `width` digits, `int[0..<width]`
    /// for the `k` of a funnel shift, and a multiple of 8 for the width of `byteSwap`. An operand
    /// is rejected when its int part is not shown to lie in the domain, from its listed values or
    /// the interval of its expression, as `^`'s exponent is.
    fn bit_domains(&mut self, w: &str, p: Prim, slots: &[(Arg<'a>, &'a Expr)], span: Span) {
        let names = zed_kernel::bits::params(p);
        let shift = matches!(p, Prim::Shl | Prim::Shr);
        let nonneg = IntervalSet::range(End::of(0), PosInf);
        let ranges: Vec<Option<IntRange>> =
            slots.iter().map(|(a, e)| self.int_range(a, e)).collect();
        let mut fine = true;
        for (i, (((a, e), r), name)) in slots.iter().zip(&ranges).zip(names).enumerate() {
            if shift && i == 0 {
                continue;
            }
            if !a.ty.vars.is_empty() {
                let d = IntDomain {
                    what: format!("`{w}` takes `{name}` in int[0..]").into(),
                    below_two_pow: None,
                };
                self.floor(&a.ty, e, d, span);
            }
            let Some(r) = r else { continue };
            if r.ints.is_subset(&nonneg) {
                continue;
            }
            fine = false;
            let at = a.at.unwrap_or(e.span);
            let shown = &r.shown;
            let mut notes = vec![Note {
                span: at,
                text: format!("`{name}` is this operand, {shown}"),
            }];
            if r.narrowed {
                notes.extend(self.deciding_notes(e));
            }
            self.derive_into(&[at], &mut notes);
            notes.extend(
                domain_repairs("int[0..]")
                    .into_iter()
                    .map(|text| Note { span, text }),
            );
            self.error_with(
                span,
                format!(
                    "`{w}` takes `{name}` in int[0..], and this `{name}` is {shown}: `{w}` reads \
                     `{name}` as binary digits, and an int below 0 has no finite row of them"
                ),
                notes,
            );
        }
        if !fine || !zed_kernel::bits::has_width(p) {
            return;
        }
        let last = slots.len() - 1;
        // An operand of a type variable read as `width` digits, under a width of an int type,
        // takes the ints below `2 ^ w`, `w` the smallest width, as a need on its parameter.
        // The other relations to `width` are between two operands, which a need on one
        // parameter does not carry: an operand of a type variable in one is rejected here
        // (CHK-need-bound).
        let two_pow = zed_kernel::bits::below_two_pow_width(p);
        let smallest = match slots[last].0.ty.vars.is_empty() {
            true => (ranges[last].as_ref()).and_then(|r| r.extreme(std::cmp::Ordering::Less)),
            false => None,
        };
        let related = (two_pow.iter().copied())
            .chain(zed_kernel::bits::below_width(p))
            .chain([last]);
        for i in related {
            let (a, e) = &slots[i];
            if a.ty.vars.is_empty() {
                continue;
            }
            let (name, at) = (names[i], a.at.unwrap_or(e.span));
            if let Some(s) = smallest.as_ref().filter(|_| two_pow.contains(&i)) {
                let d = IntDomain {
                    what: format!("`{w}` takes `{name}` in int[0..<2 ^ width]").into(),
                    below_two_pow: Some(Width(s.clone())),
                };
                self.floor(&a.ty, e, d, span);
                continue;
            }
            let mut notes = vec![Note {
                span: at,
                text: format!("`{name}` is this operand, of no declared type"),
            }];
            self.derive_into(&[at], &mut notes);
            notes.push(Note {
                span: at,
                text: format!(
                    "repair: declare the type of `{name}` where it is bound, as \
                     `{name}: int[0..<2 ^ 32]`"
                ),
            });
            let checks = match i == last {
                true => "its operands".to_string(),
                false => format!("`{name}`"),
            };
            self.error_with(
                span,
                format!(
                    "`{w}` checks {checks} against `width`, and `{name}` has no declared type \
                     here, so its values are whatever the caller passes; the checker does not \
                     follow this check back to each caller, so it needs the type of `{name}` \
                     declared"
                ),
                notes,
            );
            return;
        }
        let (wa, we) = &slots[last];
        let Some(rw) = &ranges[last] else {
            return;
        };
        let width = (wa.at.unwrap_or(we.span), rw.shown.as_str());
        if zed_kernel::bits::whole_bytes(p) && !whole_bytes(rw) {
            let (aw, sw) = width;
            let mut notes = vec![Note {
                span: aw,
                text: format!("`width` is this operand, {sw}"),
            }];
            self.derive_into(&[aw], &mut notes);
            notes.push(Note {
                span,
                text: "repair: pass a `width` that is a multiple of 8, such as 8, 16, 32 or 64"
                    .to_string(),
            });
            self.error_with(
                span,
                format!(
                    "`{w}` takes `width` a multiple of 8, and this `width` is {sw}: `{w}` works on \
                     whole bytes, and the checker found that this `width` may not be a whole \
                     number of bytes"
                ),
                notes,
            );
            return;
        }
        let smallest = rw.extreme(std::cmp::Ordering::Less);
        // An operand lies below `2 ^ width` when its largest value does below the smallest
        // width, and below `width` when its largest value is less than the smallest width.
        for (i, two_pow) in zed_kernel::bits::below_two_pow_width(p)
            .iter()
            .map(|&i| (i, true))
            .chain(zed_kernel::bits::below_width(p).map(|i| (i, false)))
        {
            let ((a, e), Some(r)) = (&slots[i], &ranges[i]) else {
                continue;
            };
            let below = r
                .extreme(std::cmp::Ordering::Greater)
                .zip(smallest.as_ref())
                .is_some_and(|(h, l)| match two_pow {
                    true => zed_kernel::bits::below_two_pow(&h, l),
                    false => h
                        .as_integer()
                        .zip(l.as_integer())
                        .is_some_and(|(h, l)| h < l),
                });
            if !below {
                let needs = if two_pow {
                    "int[0..<2 ^ width]"
                } else {
                    "int[0..<width]"
                };
                let operand = (a.at.unwrap_or(e.span), r.shown.as_str());
                self.width_error(w, names[i], needs, operand, width, span);
            }
        }
    }

    /// The integers an argument may be, when its type has an int part: an interval holding them,
    /// the values themselves when its type lists them or its text shows its value, and how to
    /// show them. The interval is what the text shows (see [`Known`]), met with what the tests
    /// the walk is in show of it ([`Ck::ints_here`]) and with the listed
    /// values, a value past `i64` read as the end of the interval on its side.
    fn int_range(&mut self, a: &Arg<'a>, e: &'a Expr) -> Option<IntRange> {
        let ns = &a.ty.set & &KType::int();
        if ns.is_empty() {
            return None;
        }
        let k = self.known(e);
        let (mut ints, narrowed) = self.ints_here(e);
        let listed = ns.ints_listed();
        let shown_as_type = listed.is_some();
        let values = match listed {
            Some(vs) => {
                let piece = |v: &Value| match v {
                    Value::Int(n) => (End::of(*n), End::of(*n)),
                    Value::Big(n) => (Fin(Num::from(&**n)), Fin(Num::from(&**n))),
                    _ => (NegInf, PosInf),
                };
                ints = ints.meet(&IntervalSet::from_pieces(vs.iter().map(piece).collect()));
                Some(vs)
            }
            None => k.value.map(|v| vec![v]),
        };
        let shown = match &values {
            _ if shown_as_type || ints == IntervalSet::top() => self.show(&Ty::set(ns)),
            Some(vs) => vs[0].to_string(),
            None => format!("int{ints}"),
        };
        Some(IntRange {
            ints,
            values,
            shown,
            narrowed,
        })
    }
    /// `sig`, named `what`, applied at `span` to `args`, which leave out the parameters
    /// `missing`: the function of those parameters, each a positional one with no default
    /// when `section`, whose types and needs are `sig`'s with the variables the arguments
    /// bind replaced. The needs on the variables of the parameters left out are checked at
    /// its calls.
    fn partial(
        &mut self,
        sig: &Sig,
        args: Vec<Option<Arg<'a>>>,
        missing: &[usize],
        section: bool,
        what: &str,
        span: Span,
    ) -> Ty {
        let mut out = vec![false; sig.params.len()];
        missing.iter().for_each(|&j| out[j] = true);
        let (mut given, mut left) = (Vars::default(), Vars::default());
        for a in &sig.arrows {
            for (j, p) in a.params.iter().enumerate() {
                p.vars_in(if out[j] { &mut left } else { &mut given });
            }
        }
        let given: BTreeSet<Arc<str>> = given.order.into_iter().collect();
        self.defer = left
            .order
            .into_iter()
            .filter(|v| !given.contains(v))
            .collect();
        self.leaving = missing.to_vec();
        let (result, kept) = self.apply(&callee(what), sig, args, false, span);
        let Some((binds, needs)) = self.applied.take() else {
            return result;
        };
        if missing.is_empty() {
            return result;
        }
        let params = missing
            .iter()
            .map(|&j| match section {
                true => SParam {
                    positional: true,
                    default: None,
                    ..sig.params[j].clone()
                },
                false => sig.params[j].clone(),
            })
            .collect();
        let arrows = kept
            .iter()
            .map(|&k| Arrow {
                params: missing
                    .iter()
                    .map(|&j| sig.arrows[k].params[j].clone())
                    .collect(),
                result: sig.arrows[k].result.clone(),
            })
            .collect();
        // A parameter left out keeps its need on its ints, at its place in the rest.
        let mut needs = needs;
        for n in &sig.needs {
            if let NeedKind::InDomain { param, .. } = &n.kind
                && let Some(i) = missing.iter().position(|j| j == param)
            {
                let mut n = n.clone();
                if let NeedKind::InDomain { param, .. } = &mut n.kind {
                    *param = i;
                }
                needs.push(n);
            }
        }
        let mut rest = Sig {
            params,
            arrows,
            bounds: sig.bounds.clone(),
            data: false,
            // A word applied to fewer arguments than its arity is not the word: `min` and `max`
            // take two tuples only when both are given (sec:reduction, item 5).
            word: None,
            needs,
            own: sig.own.clone(),
            held: BTreeSet::new(),
            named: sig.named,
            facts: Default::default(),
        };
        // A variable only the arguments given held is held by no parameter of the rest.
        rest.note_held();
        Ty::func(Arc::new(rest.replace(&binds)))
    }

    /// `v[x]` with `x` no literal: an application of each function `v` may be, and a
    /// computed index of each tuple `v` may be.
    fn at_key(&mut self, v: &Ty, x: Arg<'a>, span: Span) -> Ty {
        let mut out = self.passing(v, "a call", span);
        for p in v.pieces() {
            match p {
                Piece::Tuple(cs) => {
                    let r = self.tuple_at(&cs, &x, span);
                    out = out.union(&r);
                }
                Piece::Fn(sig) => {
                    let r = self
                        .apply("this function", &sig, vec![Some(x.clone())], false, span)
                        .0;
                    out = out.union(&r);
                }
                Piece::Var(_) if let Some(k) = self.class_of(&p) => {
                    let kind = NeedKind::Index(x.ty.clone());
                    self.note_widened(&kind, &[(&x.ty, x.at)]);
                    let r = self.need(k, kind, true, span);
                    out = out.union(&r);
                }
                Piece::Dyn => self.any("an application", span),
                Piece::Var(_) => out = out.union(&Ty::dynamic()),
                p if p.is_atoms() => {}
                p => {
                    let shown = self.text(&p.ty());
                    self.error_offering(
                        span,
                        format!(
                            "this value is {shown}, not a function: this call applies it to an \
                             argument, and a value of type {shown} cannot be applied"
                        ),
                        ["repair: call a function here, or drop the argument list after the value"
                            .to_string()],
                    );
                }
            }
        }
        out
    }

    /// `v[i]` with the literal `x`, `i` if it is a component number: a tuple's component, or
    /// a family's entry.
    fn at_index(&mut self, v: &Ty, i: Option<usize>, x: Arg<'a>, span: Span) -> Ty {
        let mut out = self.passing(v, "an index", span);
        let shown = x.ty.to_string();
        for p in v.pieces() {
            match p {
                Piece::Fn(sig) if sig.data => {
                    let r = self
                        .apply("this family", &sig, vec![Some(x.clone())], true, span)
                        .0;
                    out = out.union(&r);
                }
                Piece::Tuple(cs) => match i.and_then(|i| cs.get(i)) {
                    Some(c) => out = out.union(c),
                    None => {
                        let tuple = self.text(&Ty::of_row(cs.clone()));
                        self.no_component(&tuple, cs.len(), &shown, span);
                    }
                },
                Piece::Var(_) if let Some(k) = self.class_of(&p) => {
                    let kind = NeedKind::Component {
                        i,
                        key: x.ty.clone(),
                    };
                    out = out.union(&self.need(k, kind, true, span));
                }
                Piece::Dyn => self.any(&format!("`[{shown}]`"), span),
                Piece::Var(_) => out = out.union(&Ty::dynamic()),
                p if p.is_atoms() => {}
                p => {
                    let t = self.text(&p.ty());
                    self.error_offering(
                        span,
                        format!(
                            "`[{shown}]` takes a tuple, not {t}: an index picks a component of a \
                             tuple or an entry of a family, and {t} has neither"
                        ),
                        [format!(
                            "repair: index a tuple or a family, or drop `[{shown}]`"
                        )],
                    )
                }
            }
        }
        out
    }

    /// A declared function in a slot of the function type `e`: the same number of positional
    /// parameters and the same named ones, in any order, and types that fit.
    fn fit_declared(&mut self, id: usize, e: &Arc<Sig>, span: Span) -> Ty {
        let f = self.t.funcs[&id];
        let own = self.env.get(&id).cloned().unwrap_or_else(Ty::dynamic);
        let Some(s) = only_fn(&own) else {
            return own;
        };
        let pos = |s: &Sig| s.params.iter().filter(|p| p.positional).count();
        let mut from = Vec::new();
        let mut k = 0;
        let mut ok = pos(&s) == pos(e) && s.params.len() == e.params.len();
        let epos: Vec<usize> = (0..e.params.len())
            .filter(|&j| e.params[j].positional)
            .collect();
        for p in &s.params {
            if !ok {
                break;
            }
            if p.positional {
                from.push(epos[k]);
                k += 1;
            } else {
                match e
                    .params
                    .iter()
                    .position(|q| !q.positional && q.name == p.name)
                {
                    Some(j) => from.push(j),
                    None => ok = false,
                }
            }
        }
        if !ok {
            let names: Vec<&str> = f.params.iter().map(|p| p.name.as_str()).collect();
            let call: Vec<String> = names.iter().map(|n| format!("{n}: {n}")).collect();
            let shown = self.sig_text(e);
            let menu = [
                format!(
                    "repair: declare the parameters of `{}` as `{shown}` passes them, with \
                     `positional` where it passes by position",
                    f.name
                ),
                format!(
                    "repair: pass a lambda, `({}) -> {}({})`",
                    names.join(", "),
                    f.name,
                    call.join(", ")
                ),
            ];
            self.rejects_offering(
                Row::ParameterKinds,
                span,
                format!(
                    "the parameters of `{}` ({}) do not fit `{shown}`: declare them as it passes them, \
                     with `positional` where it passes by position, or pass a lambda, ({}) -> {}({})",
                    f.name,
                    s.params
                        .iter()
                        .map(|p| match p.positional {
                            true => format!("positional {}", p.name),
                            false => p.name.to_string(),
                        })
                        .collect::<Vec<_>>()
                        .join(", "),
                    names.join(", "),
                    f.name,
                    call.join(", ")
                ),
                menu,
            );
            return Ty::func(e.clone());
        }
        // `s` with its parameters in `e`'s order.
        let mut inv = vec![0; from.len()];
        for (i, &j) in from.iter().enumerate() {
            inv[j] = i;
        }
        let permuted = Sig {
            bounds: s.bounds.clone(),
            data: s.data,
            word: s.word.clone(),
            needs: s.needs.clone(),
            own: s.own.clone(),
            held: s.held.clone(),
            named: s.named,
            facts: Default::default(),
            params: e.params.clone(),
            arrows: s
                .arrows
                .iter()
                .map(|a| Arrow {
                    params: inv.iter().map(|&i| a.params[i].clone()).collect(),
                    result: a.result.clone(),
                })
                .collect(),
        };
        let what = format!("`{}`", f.name);
        let permuted = Arc::new(permuted);
        if !self.fits_slot(&permuted, e, &what, span) {
            // The cover of rule 6 the checker refuses, if that is why ([`ty::why_unfit`]).
            let why = match permuted.needs.is_empty() {
                true => ty::why_unfit_with(&permuted, e, &|v| self.stale(v))
                    .map_or_else(String::new, |w| format!(": {w}")),
                false => String::new(),
            };
            let (s, e) = (self.sig_text(&s), self.sig_text(e));
            let why = match why.is_empty() {
                true => ": it is passed where a function of that type is expected, and its own \
                         type does not fit that one"
                    .to_string(),
                false => why,
            };
            let name = &f.name;
            self.error_offering(
                span,
                format!("`{name}` is `{s}`, not `{e}`{why}"),
                [
                    format!("repair: pass a function of type `{e}` in place of `{name}`"),
                    format!(
                        "repair: pass a lambda of type `{e}` that calls `{name}` with the \
                         arguments it takes"
                    ),
                ],
            );
        }
        if from.iter().enumerate().any(|(i, &j)| i != j) {
            self.put(Undo::Fit(span, Some(Fit::Adapter { from })));
        }
        Ty::func(e.clone())
    }

    /// Whether the function `s`, named `what` in messages, with its parameters in the order of
    /// the function type `e`'s, fits a slot of `e`: as a type, or, when its body makes uses of
    /// its type variables, by those uses checked on the types `e` passes. False only when no
    /// error says why.
    fn fits_slot(&mut self, s: &Arc<Sig>, e: &Arc<Sig>, what: &str, span: Span) -> bool {
        match s.needs.is_empty() {
            true => ty::fits_sig_with(s, e, &|v| self.stale(v)),
            false => {
                let p = Ty::func(e.clone());
                self.fit_needs(s, &p, &mut Binds::new(), what, span)
            }
        }
    }

    /// The repairs of a rejected application the checker discharges: each argument wrapped
    /// in a prelude word, when the application then checks, tried with the checker's state
    /// restored after. At an operator or a call of a prelude word the wrapped argument keeps
    /// its place, so a failure of the word, `#inexact` of `f64(r)`, passes by as it does where
    /// the repair is written (rule 6 of sec:type_resolution): `max(f64(r), x)` as
    /// `f64(r) + x`. At a call of a declared function it has none, so a word whose failure the
    /// parameter does not take is not offered: `discount(price: int("12"))`. The trial sees
    /// the application, not where its result goes. An argument of a class is wrapped as a value
    /// of the carriers the class still holds. A name is shown wrapped, `f64(r)`, and anything
    /// else as the word around the place shown: the menu of the row for two numeric values
    /// with no common carrier (DESIGN.md sec:diagnostics). A `rat` literal is offered the
    /// literals of the other carriers that are the same number exactly, `1.0` for `1r`, in
    /// place of the words ([`rat_forms`]).
    fn repairs(
        &mut self,
        what: &str,
        sig: &Sig,
        args: &[Option<Arg<'a>>],
        pass: bool,
        span: Span,
    ) -> Vec<Note> {
        let mut out = Vec::new();
        if self.trying {
            return out;
        }
        // A word is called by its name and has its own signature; a declared function may
        // share the name only with a signature of its own.
        let word = what
            .strip_prefix('`')
            .and_then(|w| w.strip_suffix('`'))
            .is_some_and(|w| sig.word.as_deref() == Some(w));
        let kept = pass || word;
        for (i, a) in args.iter().enumerate() {
            let Some(Arg {
                lit: None,
                at: Some(at),
                ty,
                ..
            }) = a
            else {
                continue;
            };
            let held = match self.class_of_ty(ty) {
                Some(r) if self.classes[r].mask & OTHER == 0 => Ty::of_mask(self.classes[r].mask),
                _ => ty.clone(),
            };
            let t = self.t;
            let (name, written) = match self.seen.get(at) {
                Some((_, Src::Name(id))) => (Some(&t.res.binders[*id].name), None),
                Some((_, Src::Other(e))) => (None, rat_forms(e)),
                _ => (None, None),
            };
            if let Some(forms) = written {
                for (ty, text) in forms {
                    if self.repaired(what, sig, args, (i, ty, kept.then_some(*at)), pass, span) {
                        out.push(Note { span: *at, text });
                    }
                }
                continue;
            }
            for w in ["String", "int", "rat", "f64"] {
                let Some(r) = converted(&word_sig(w), &held) else {
                    continue;
                };
                if self.repaired(what, sig, args, (i, r, kept.then_some(*at)), pass, span) {
                    let text = match name {
                        Some(n) => format!("repair: write `{w}({n})`; the checker accepts that"),
                        None => format!("repair: wrap this in `{w}(…)`; the checker accepts that"),
                    };
                    out.push(Note { span: *at, text });
                }
            }
        }
        out
    }

    /// Whether the application of `sig` to `args` checks with argument `i` replaced by a
    /// value of type `ty` at the place `at`, if any, tried with the checker's state restored after.
    fn repaired(
        &mut self,
        what: &str,
        sig: &Sig,
        args: &[Option<Arg<'a>>],
        (i, ty, at): (usize, Ty, Option<Span>),
        pass: bool,
        span: Span,
    ) -> bool {
        let mut with = args.to_vec();
        with[i] = Some(Arg { at, ..Arg::of(ty) });
        let saved = self.mark();
        self.trying = true;
        self.apply(what, sig, with, pass, span);
        let ok = self.info.errors.len() == saved.errors;
        self.trying = false;
        self.undo(&saved);
        ok
    }

    /// Applies `sig` to `args`, a missing one filled by its default. When `pass` holds, as
    /// for an operator or a prelude word, an argument's atoms pass through, two arguments'
    /// merged into `#errs`. Gives the result and the arrows kept.
    fn apply(
        &mut self,
        what: &str,
        sig: &Sig,
        mut args: Vec<Option<Arg<'a>>>,
        pass: bool,
        span: Span,
    ) -> (Ty, Vec<usize>) {
        let mut out = Ty::empty();
        let need_args = self.need_args.take();
        let leaving = std::mem::take(&mut self.leaving);
        if (sig.needs.iter()).any(|n| matches!(n.kind, NeedKind::InDomain { .. })) {
            self.floors_at(what, sig, &args, &leaving, span);
        }
        if pass {
            let atoms: Vec<Ty> = args
                .iter()
                .flatten()
                .filter(|a| a.lit.is_none())
                .map(|a| a.ty.loose_ty())
                .collect();
            passed(&mut out, atoms.iter());
            for a in args.iter_mut().flatten() {
                a.ty = a.ty.without_loose();
            }
        } else {
            let mut atoms = Vec::new();
            for (i, a) in args.iter_mut().enumerate() {
                let Some(a) = a else {
                    continue;
                };
                let loose = a.ty.loose();
                let from_need = need_args.as_ref().is_some_and(|v| v.get(i) == Some(&true));
                if loose.is_empty() || (a.at.is_none() && !from_need) {
                    continue;
                }
                // Rule 6 treats each region of the argument apart: the atoms every arrow
                // omits pass by, and the rest stay in the argument to select an arrow.
                let refused = self.refused(sig, i, &loose);
                if refused.is_empty() {
                    continue;
                }
                let Some(at) = a.at else {
                    // A check of a need, as of `f(v)` in `ap(f, v) = f(v)`: the atoms pass by
                    // at the call whose argument gave them, which [`Self::apply_one`] finds.
                    atoms.push(a.ty.of_piece(&Piece::Set(refused.clone())));
                    a.ty = a.ty.without(&refused);
                    self.refused.push((what.into(), i, refused));
                    continue;
                };
                if refused == loose {
                    atoms.push(a.ty.loose_ty());
                    a.ty = a.ty.without_loose();
                } else {
                    atoms.push(a.ty.of_piece(&Piece::Set(refused.clone())));
                    a.ty = a.ty.without(&refused);
                }
                self.pass_at(span, at, &refused);
            }
            passed(&mut out, atoms.iter());
        }
        // `min` and `max` take two tuples, wherever they are called from; they are told apart by
        // the word the signature is, not by its arrows, which `+`, `-` and `*` share.
        if let [Some(x), Some(y)] = args.as_slice()
            && (!x.ty.tuples.is_empty() || !y.ty.tuples.is_empty())
            && matches!(sig.word.as_deref(), Some("min" | "max"))
        {
            let t = self.min_max_tuples(what, sig, &x.ty, &y.ty, span);
            return (out.union(&t), Vec::new());
        }
        let defer = std::mem::take(&mut self.defer);
        let passing = self.need_passed.len();
        let refusals = self.lit_refused.len();
        let r = match (sig.arrows.len(), self.first_taking(sig, &args, pass)) {
            (1, _) => self.apply_one(what, sig, 0, &args, defer, span),
            (_, Some(k)) => self.apply_one(what, sig, k, &args, defer, span),
            _ => {
                let r = self.apply_many(what, sig, &mut args, span);
                self.applied = None;
                r
            }
        };
        // What a check of a need left when the application failed before taking it.
        self.need_passed.truncate(passing);
        // A literal refused is its own error, and the application's none.
        for refused in self.lit_refused.split_off(refusals) {
            self.literal_refused(what, sig, &args, refused, pass, span);
        }
        match r {
            Ok((t, kept)) => (out.union(&t), kept),
            Err(message) => {
                self.applied = None;
                let mut notes = self.applied(what, sig, &args, span);
                let mut seen: HashSet<Note> = notes.iter().cloned().collect();
                for a in args.iter().flatten() {
                    for n in self.reasons(&a.ty) {
                        if seen.insert(n.clone()) {
                            notes.push(n);
                        }
                    }
                }
                notes.extend(self.repairs(what, sig, &args, pass, span));
                if self.no_arrow_at_carrier(what, sig, &args) {
                    self.rejects_with(Row::NoArrowAtCarrier, span, message, notes);
                } else if self.no_common_carrier(sig, &args) {
                    self.rejects_with(Row::NoCommonCarrier, span, message, notes);
                } else {
                    self.error_with(span, message, notes);
                }
                (out, Vec::new())
            }
        }
    }

    /// Reports a literal of `args` rejected at a parameter of `sig` with the message `m` at
    /// `s`: in the row of an operator with no arrow at its operands' carrier where that holds
    /// (`7 / 2`); in the row of two numbers with no common carrier where that holds
    /// (`q + 1.5` with `q: int`), with the application's derivation and the casts of the other
    /// operands the checker accepts, `f64(q)`, where the message holds the literal's own
    /// forms; and in no row otherwise.
    fn literal_refused(
        &mut self,
        what: &str,
        sig: &Sig,
        args: &[Option<Arg<'a>>],
        (s, m): (Span, String),
        pass: bool,
        span: Span,
    ) {
        if self.no_arrow_at_carrier(what, sig, args) {
            let notes = self.derive(&[s]);
            self.rejects_with(Row::NoArrowAtCarrier, s, m, notes);
        } else if self.no_common_carrier(sig, args) {
            let mut notes = Vec::new();
            if !self.trying {
                notes = self.applied(what, sig, args, span);
                let mut seen: HashSet<Note> = notes.iter().cloned().collect();
                for a in args.iter().flatten() {
                    for n in self.reasons(&a.ty) {
                        if seen.insert(n.clone()) {
                            notes.push(n);
                        }
                    }
                }
                notes.extend(self.repairs(what, sig, args, pass, span));
            }
            self.rejects_with(Row::NoCommonCarrier, s, m, notes);
        } else {
            self.error(s, m);
        }
    }

    fn apply_one(
        &mut self,
        what: &str,
        sig: &Sig,
        k: usize,
        args: &[Option<Arg<'a>>],
        defer: BTreeSet<Arc<str>>,
        span: Span,
    ) -> Result<(Ty, Vec<usize>), String> {
        let arrow = &sig.arrows[k];
        let fail = |ck: &Self| Err(ck.rejected(what, args));
        let mut binds = Binds::new();
        let mut grouped = vec![false; args.len()];
        // The arguments each bounded variable stands at, in one pass over the arguments: one
        // pass per variable over every argument cost `O(v a)`.
        let mut at_of: HashMap<&str, Vec<usize>> = HashMap::new();
        for (i, (p, a)) in arrow.params.iter().zip(args).enumerate() {
            if let Some(v) = p.as_var().filter(|_| a.is_some()) {
                at_of.entry(&**v).or_default().push(i);
            }
        }
        for (v, &m) in &sig.bounds {
            let at = at_of.remove(&**v).unwrap_or_default();
            let lit_at = at
                .iter()
                .any(|&i| args[i].as_ref().is_some_and(|a| a.lit.is_some()));
            if at.len() < 2 && !lit_at {
                continue;
            }
            let (mut carriers, mut classes, mut lits) = (0u8, Vec::new(), Vec::new());
            let mut valued = false;
            for &i in &at {
                grouped[i] = true;
                let a = args[i].as_ref().expect("an argument");
                if let Some(l) = &a.lit {
                    lits.push(l.clone());
                    continue;
                }
                for p in a.ty.pieces() {
                    valued = true;
                    match (self.class_of(&p), p.carrier()) {
                        (Some(k), _) => classes.push(k),
                        _ if matches!(p, Piece::Var(_)) => {}
                        (None, Some(c)) => carriers |= c.bit(),
                        (None, None) => return fail(self),
                    }
                }
            }
            let bound = match (carriers.count_ones(), classes.first()) {
                (n, _) if n > 1 => return fail(self),
                (1, _) => {
                    let c = Carrier::of_mask(carriers).next().expect("one carrier");
                    if m & carriers == 0 {
                        return fail(self);
                    }
                    for &k in &classes {
                        if !self.restrict(k, c.bit(), what, span) {
                            return fail(self);
                        }
                    }
                    for l in &lits {
                        if lit_carrier(&l.value) != c && !adoptable(l, c) {
                            return fail(self);
                        }
                        self.adopt_to(l, c);
                    }
                    Ty::carrier(c)
                }
                (_, Some(&k)) => {
                    for &j in &classes[1..] {
                        if !self.merge(k, j, what, span) {
                            return fail(self);
                        }
                    }
                    if !self.restrict(k, m, what, span) {
                        return fail(self);
                    }
                    for l in &lits {
                        if !self.join(k, &self.joining(l), false) {
                            return fail(self);
                        }
                    }
                    Ty::var(format!("${}", self.find(k)).into())
                }
                _ if !lits.is_empty() => {
                    // The carrier of the bound its literals adopt fewest times to.
                    let adoptions = |c: Carrier| {
                        lits.iter()
                            .all(|l| adoptable(l, c))
                            .then(|| lits.iter().filter(|l| lit_carrier(&l.value) != c).count())
                    };
                    let Some(c) = Carrier::of_mask(m)
                        .filter_map(|c| adoptions(c).map(|n| (n, c)))
                        .min_by_key(|&(n, _)| n)
                        .map(|(_, c)| c)
                    else {
                        return fail(self);
                    };
                    for l in &lits {
                        self.adopt_to(l, c);
                    }
                    Ty::carrier(c)
                }
                // Every value of the arguments here passed by under rule 6 (`add(w(n), w(n))`
                // with `w` giving atoms only): the call never takes place, so the variable
                // binds to no value.
                _ if !valued => Ty::empty(),
                _ => Ty::dynamic(),
            };
            binds.insert(v.clone(), bound);
        }
        for (i, a) in args.iter().enumerate() {
            let Some(a) = a else {
                continue;
            };
            if grouped[i] {
                continue;
            }
            let p = &arrow.params[i];
            let generic = match p.as_var().is_some() {
                true => self.generic_parts(a),
                false => None,
            };
            let a = &match generic {
                Some(ty) => Cow::Owned(Arg {
                    ty,
                    parts: None,
                    ..a.clone()
                }),
                None => Cow::Borrowed(a),
            };
            // A parameter that is a class of the function around: the argument flows into it.
            if let Some(k) = self.class_of_ty(p) {
                let ok = match &a.lit {
                    Some(l) => self.join(k, &self.joining(l), false),
                    None => self.flow(k, &a.ty, what, span),
                };
                if !ok {
                    return fail(self);
                }
                continue;
            }
            let ty = match adopted(a, p) {
                // A literal that cannot adopt is its own error, and the application's none.
                Err((s, m)) => {
                    self.lit_refused.push((s, m));
                    continue;
                }
                Ok(Some((t, ads))) => {
                    for (s, v) in ads {
                        self.put(Undo::Adopt(s, Some(v)));
                    }
                    Cow::Owned(t)
                }
                Ok(None) => Cow::Borrowed(&a.ty),
            };
            if a.lit.is_some() {
                if !self.sub(&ty, p, &mut binds) {
                    let why = ty.refused(p);
                    return Err(self.rejected_because(what, args, &why));
                }
                continue;
            }
            for piece in ty.pieces() {
                let ok = match self.class_of(&piece) {
                    _ if piece == Piece::Dyn => p.dynamic,
                    Some(_) if p.dynamic => true,
                    Some(_) if !p.vars.is_empty() => self.sub(&ty.of_piece(&piece), p, &mut binds),
                    Some(k) => {
                        if !p.tuples.is_empty() || !p.fns.is_empty() {
                            let kind = NeedKind::Into {
                                what: what.into(),
                                ty: p.clone(),
                            };
                            self.need(k, kind, false, span);
                        }
                        self.restrict(k, mask_of(p), what, span)
                    }
                    None => match &piece {
                        Piece::Fn(s) if !s.needs.is_empty() && !p.fns.is_empty() => {
                            self.fit_needs(s, p, &mut binds, what, span)
                        }
                        _ => self.sub(&ty.of_piece(&piece), p, &mut binds),
                    },
                };
                if !ok {
                    return Err(self.rejected_at(what, args, Some((i, &piece, p))));
                }
            }
        }
        // The variables of the parameters of a function the call gives, which only its calls
        // bind: the needs on them are its own.
        let partial = !defer.is_empty();
        let mut defer = defer;
        let mut taken = Vars::default();
        arrow.params.iter().for_each(|p| p.vars_in(&mut taken));
        let mut inner = Vars::default();
        for s in &arrow.result.fns {
            s.arrows
                .iter()
                .for_each(|a| a.params.iter().for_each(|p| p.vars_in(&mut inner)));
        }
        defer.extend(inner.order.into_iter().filter(|v| !taken.contains(v)));
        let passing = self.need_passed.len();
        let mut left = self.replay(what, &sig.needs, &mut binds, defer, span);
        // Each bounded variable's binding is within its bound, and of one carrier, or of
        // other values only: the arrows of an operator each take one. So the classes in it
        // merge, and what else it holds flows into them.
        for (v, &m) in &sig.bounds {
            let Some(t) = binds.get(v).cloned() else {
                continue;
            };
            let mut kinds = 0u8;
            let mut class: Option<usize> = None;
            let mut rest = Ty::empty();
            for piece in t.pieces() {
                let ok = match (self.class_of(&piece), piece.carrier()) {
                    (Some(k), _) => {
                        self.restrict(k, m, what, span)
                            && match class {
                                Some(c) => self.merge(c, k, what, span),
                                None => {
                                    class = Some(k);
                                    true
                                }
                            }
                    }
                    _ if piece == Piece::Dyn => false,
                    _ if matches!(piece, Piece::Var(_)) => true,
                    (None, Some(c)) => {
                        kinds |= c.bit();
                        rest = rest.union(&piece.ty());
                        m & c.bit() != 0
                    }
                    (None, None) => {
                        kinds |= OTHER;
                        rest = rest.union(&piece.ty());
                        m & OTHER != 0
                    }
                };
                if !ok || kinds.count_ones() > 1 {
                    return fail(self);
                }
            }
            if let Some(c) = class
                && kinds != 0
                && !self.flow(c, &rest, what, span)
            {
                return fail(self);
            }
        }
        binds.retain(|v, _| !self.is_class(v));
        let mut out = Ty::empty();
        let given: Vec<&Arg> = args.iter().flatten().collect();
        if given.iter().any(|a| a.ty.dynamic) {
            out = out.union(&Ty::dynamic());
        }
        if given
            .iter()
            .all(|a| a.lit.is_some() || a.ty.pieces().iter().any(|p| *p != Piece::Dyn))
        {
            let result = close(&arrow.result.replace(&binds), sig, |v| self.is_class(v));
            out = out.union(&match partial {
                true => result,
                false => {
                    let needs = left.iter().map(|n| n.replace(&binds)).collect();
                    let (held, now) = hold(&result, needs, |v| self.is_class(v));
                    self.replay(what, &now, &mut binds, BTreeSet::new(), span);
                    left.clear();
                    held
                }
            });
        }
        out = out.union(&self.pass_needs(what, &arrow.params, args, passing, span)?);
        self.applied = Some((binds, left));
        Ok((out, vec![0]))
    }

    /// [`Self::apply`] of a signature of several arrows, each over one carrier or a tuple:
    /// an operator, a prelude word, or a section of one. The classes of the arguments merge,
    /// since every arrow takes one carrier for all its parameters, and its literals join
    /// them; without a class, each literal adopts the carrier of its parameter on the
    /// arrows that adopt fewest. Then the arguments' pieces are taken in turn, each state
    /// the arrows still alive and the carriers they allow where the class stands
    /// ([`ClassAt`]): a state per such pair, not per combination of pieces.
    fn apply_many(
        &mut self,
        what: &str,
        sig: &Sig,
        args: &mut [Option<Arg<'a>>],
        span: Span,
    ) -> Result<(Ty, Vec<usize>), String> {
        let mut class = None;
        for a in args.iter().flatten() {
            for p in a.ty.pieces() {
                if let Some(k) = self.class_of(&p) {
                    match class {
                        None => class = Some(k),
                        Some(c) => {
                            if !self.merge(c, k, what, span) {
                                return Err(self.rejected(what, args));
                            }
                        }
                    }
                }
            }
        }
        let kept: Vec<usize> = match class {
            Some(k) => {
                for a in args.iter().flatten() {
                    if let Some(l) = &a.lit
                        && !self.join(k, l, false)
                    {
                        return Err(self.rejected(what, args));
                    }
                }
                (0..sig.arrows.len()).collect()
            }
            None => match self.fewest(what, sig, args)? {
                Some(kept) => kept,
                // Reported: no value, as a rejected application gives, so that no operator
                // around it reports it again.
                None => return Ok((Ty::empty(), Vec::new())),
            },
        };
        // The states: the arrows alive, whether a piece was unknown, the class's place, and
        // the first pieces that reached it, by argument.
        type State = (Vec<usize>, bool, ClassAt, Vec<Option<Piece>>);
        let mut states: Vec<State> = vec![(kept.clone(), false, None, Vec::new())];
        for (i, a) in args.iter().enumerate() {
            let pieces: Vec<Option<Piece>> = match a {
                None => vec![None],
                Some(a) if a.lit.is_some() && class.is_some() => {
                    vec![Some(Piece::Var(format!("${}", class.unwrap()).into()))]
                }
                Some(a) => a.ty.pieces().into_iter().map(Some).collect(),
            };
            let mut next: Vec<State> = Vec::new();
            for (alive, dyn_, at, path) in &states {
                for p in &pieces {
                    let mut at = at.clone();
                    let (alive, dyn_) = match p {
                        None => (alive.clone(), *dyn_),
                        // A class may still take any value its mask allows, so it keeps
                        // every arrow; the restriction after the arguments narrows it.
                        Some(p) if self.class_of(p).is_some() => {
                            let m = at.get_or_insert_with(|| vec![EVERY; sig.arrows.len()]);
                            for &j in alive {
                                m[j] &= mask_of(&sig.arrows[j].params[i]);
                            }
                            (alive.clone(), *dyn_)
                        }
                        Some(Piece::Var(_)) => (alive.clone(), true),
                        Some(p) => {
                            let alive = alive
                                .iter()
                                .copied()
                                .filter(|&k| {
                                    self.sub(&p.ty(), &sig.arrows[k].params[i], &mut Binds::new())
                                })
                                .collect();
                            (alive, *dyn_)
                        }
                    };
                    // Two paths to one set of arrows are one state only when the class stands
                    // where it meets the same carriers on each: `(line else 0) + bump` has the
                    // paths `(int, int)` and `($k, int)`, and the second restricts the class.
                    let same_at = |o: &ClassAt| match (o, &at) {
                        (None, None) => true,
                        (Some(x), Some(y)) => alive.iter().all(|&j| x[j] == y[j]),
                        _ => false,
                    };
                    if !next
                        .iter()
                        .any(|s| s.0 == alive && s.1 == dyn_ && same_at(&s.2))
                    {
                        let mut path = path.clone();
                        path.push(p.clone());
                        next.push((alive, dyn_, at, path));
                    }
                }
            }
            states = next;
        }
        let mut out = Ty::empty();
        for (alive, dyn_, at, path) in &states {
            let shown = |ck: &Self| {
                let shown: Vec<String> = path
                    .iter()
                    .map(|p| p.as_ref().map_or_else(|| "_".into(), |p| ck.show(&p.ty())))
                    .collect();
                let pieces: Vec<Option<Ty>> =
                    path.iter().map(|p| p.as_ref().map(Piece::ty)).collect();
                let pieces: Vec<Option<&Ty>> = pieces.iter().map(Option::as_ref).collect();
                let why = refused_among(sig, &kept, &pieces);
                super::does_not_take(what, &shown.join(", "), &why)
            };
            match (class, at) {
                (Some(k), Some(at)) => {
                    let m = alive.iter().fold(0, |m, &j| m | at[j]);
                    if alive.is_empty() || !self.restrict(k, m, what, span) {
                        return Err(shown(self));
                    }
                    if *dyn_ {
                        out = out.union(&Ty::dynamic());
                        continue;
                    }
                    let r = self.find(k);
                    let km = self.classes[r].mask;
                    let rel: Vec<(&Arrow, u8)> = alive
                        .iter()
                        .map(|&j| (&sig.arrows[j], at[j]))
                        .filter(|&(_, m)| m & km != 0)
                        .collect();
                    let follows = rel.iter().all(|&(a, m)| {
                        m.count_ones() == 1
                            && Carrier::of_mask(m)
                                .next()
                                .is_some_and(|c| self.subtype(&Ty::carrier(c), &a.result))
                    });
                    if follows {
                        out = out.union(&Ty::var(format!("${r}").into()));
                        for (a, _) in &rel {
                            out = out.union(&a.result.of_piece(&Piece::Set(a.result.atoms())));
                        }
                    } else {
                        for (a, _) in &rel {
                            out = out.union(&close(&a.result, sig, |v| self.is_class(v)));
                        }
                    }
                }
                _ if *dyn_ => out = out.union(&Ty::dynamic()),
                _ => {
                    let Some(&j) = alive.first() else {
                        return Err(shown(self));
                    };
                    let a = &sig.arrows[j];
                    let mut binds = Binds::new();
                    for (p, t) in path.iter().zip(&a.params) {
                        if let Some(p) = p {
                            self.sub(&p.ty(), t, &mut binds);
                        }
                    }
                    out = out.union(&close(&a.result.subst(&binds), sig, |v| self.is_class(v)));
                }
            }
        }
        Ok((out, kept))
    }

    /// Reports `sum` at `span` given `shown`, which is not a tuple of numbers.
    fn sum_refused(&mut self, shown: &str, span: Span) {
        self.error_offering(
            span,
            format!(
                "`sum` does not take ({shown}): `sum` adds the components of a tuple, and they \
                 must all be numbers"
            ),
            [
                "repair: pass a tuple whose components are all numbers, as `sum((1, 2, 3))`"
                    .to_string(),
            ],
        );
    }

    /// `sum` of a tuple: its components added in turn, `0` for the empty tuple; atoms pass.
    fn sum(&mut self, x: Arg<'a>, span: Span) -> Ty {
        let t = &x.ty;
        let mut out = self.passing(t, "`sum`", span);
        let add = op_sig("+");
        for p in t.pieces() {
            match p {
                Piece::Tuple(cs) => {
                    // A component that holds a value of no number is the tuple's fault, not
                    // that of one `+`, so the message names the tuple.
                    let not_number = |p: &Piece| {
                        !matches!(p, Piece::Var(_))
                            && !p.is_atoms()
                            && !p.carrier().is_some_and(Carrier::numeric)
                    };
                    if cs.iter().any(|c| c.pieces().iter().any(not_number)) {
                        let shown: Vec<String> = cs.iter().map(|c| self.text(c)).collect();
                        self.sum_refused(&shown.join(", "), span);
                        continue;
                    }
                    // The components as `+` takes them: a literal written in the tuple stays
                    // one, and adopts the carrier of the others, which are added first. Each
                    // `+` takes its two operands in the order they are written, as a message
                    // shows them.
                    let args = components(&x, cs.len())
                        .unwrap_or_else(|| cs.iter().cloned().map(Arg::of).collect());
                    let mut args: Vec<(usize, Arg)> = args.into_iter().enumerate().collect();
                    args.sort_by_key(|(_, a)| a.lit.is_some());
                    let mut args = args.into_iter();
                    let Some((mut at, mut acc)) = args.next() else {
                        out = out.union(&Ty::lit(&Value::Int(0)));
                        continue;
                    };
                    for (i, c) in args {
                        let pair = if i < at { [c, acc] } else { [acc, c] };
                        let ty = self
                            .apply("`+` in `sum`", &add, pair.map(Some).to_vec(), true, span)
                            .0;
                        (at, acc) = (at.min(i), Arg::of(ty));
                    }
                    let acc = acc.ty;
                    if let Some(c) = acc.pieces().iter().find(|p| {
                        !matches!(p, Piece::Var(_))
                            && !p.is_atoms()
                            && !p.carrier().is_some_and(Carrier::numeric)
                    }) {
                        let shown = self.text(&c.ty());
                        self.sum_refused(&shown, span);
                    }
                    out = out.union(&acc);
                }
                Piece::Dyn => self.any("`sum`", span),
                // A class takes the use as a need, checked on each value that flows into it
                // and at each call of a generic function (CHK-need-bound).
                Piece::Var(v) => {
                    let r = class_id(&v).filter(|&k| k < self.classes.len());
                    let r = r.map(|k| self.find(k));
                    let given = match r.map(|r| (r, self.classes[r].resolved.clone())) {
                        Some((_, Some(t))) => self.sum(Arg::of(t), span),
                        Some((r, None)) => self.need(r, NeedKind::Sum, true, span),
                        None => Ty::dynamic(),
                    };
                    out = out.union(&given);
                }
                p if p.is_atoms() => {}
                p => {
                    let shown = self.text(&p.ty());
                    self.sum_refused(&shown, span)
                }
            }
        }
        out
    }
}

/// The repairs of a default of type `got` for the parameter `name` of type `want`, each placed
/// at the default, `span`.
fn default_repairs(name: &str, got: &str, want: &str, span: Span) -> Vec<Note> {
    [
        format!("repair: write a default of type {want}"),
        format!("repair: declare `{name}` with a type that holds {got} as well, as `{name}: {want} | {got}`"),
    ]
    .into_iter()
    .map(|text| Note { span, text })
    .collect()
}

/// The repairs of an int `^` whose exponent may be below 0, at `span`.
fn exponent_repairs(span: Span) -> Vec<Note> {
    [
        "repair: test the exponent first, as `if n >= 0 { x ^ n } else { … }`, so that inside \
         the branch it is at least 0",
        "repair: declare the exponent with a type of no int below 0, as `n: int[0..]`",
    ]
    .into_iter()
    .map(|text| Note {
        span,
        text: text.to_string(),
    })
    .collect()
}

/// The repairs of a value that may lie outside the ints `domain` a use needs.
fn domain_repairs(domain: &str) -> Vec<String> {
    vec![
        format!(
            "repair: test the value first, as `if v is {domain} {{ … }} else {{ … }}`, so that \
             inside the branch it lies in {domain}"
        ),
        format!("repair: declare the value with a type in {domain}, as `v: {domain}`"),
    ]
}

/// The callee of a call as a message names it: a name in code quotes, and the words that
/// stand for a callee written as an expression as they are.
fn callee(what: &str) -> String {
    match what.contains(' ') {
        true => what.to_string(),
        false => format!("`{what}`"),
    }
}

/// The repairs of a value that holds a function where data is taken, at `span`.
fn data_repairs(span: Span) -> Vec<Note> {
    [
        "repair: call the function before the value gets here, so that the value holds its \
         result and not the function",
        "repair: keep the function under its own name, out of the value",
    ]
    .into_iter()
    .map(|text| Note {
        span,
        text: text.to_string(),
    })
    .collect()
}

/// Why an argument outside the ints `d` is refused: the use it reaches needs ints in `d`.
fn outside(d: &IntDomain) -> String {
    format!(
        ": a value outside {} would reach a use that does not take it",
        domain_text(d)
    )
}

/// The repairs of an argument `p` that may lie outside the ints `d` its use needs.
fn passed_repairs(p: &str, d: &IntDomain, span: Span) -> Vec<Note> {
    let dom = domain_text(d);
    [
        format!(
            "repair: test the argument first, as `if v is {dom} {{ … }} else {{ … }}`, and pass \
             it as `{p}` inside the branch"
        ),
        format!("repair: declare the value passed as `{p}` with a type in {dom}"),
    ]
    .into_iter()
    .map(|text| Note { span, text })
    .collect()
}
