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

use super::*;

/// What a job gives back.
pub(super) enum Ret {
    /// Nothing yet, or a statement's result, which is nothing.
    None,
    Ty(Ty),
    Arg(Arg),
    /// A condition's type and the facts it makes when it holds and when it does not.
    Cond(Ty, Facts, Facts),
    Sig(Arc<Sig>),
}

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

/// The positional and named arguments of a call, shared by the frames that read them.
#[derive(Default)]
pub(super) struct Args<'a> {
    pub(super) positional: Vec<ArgSrc<'a>>,
    pub(super) named: Vec<(String, ArgSrc<'a>)>,
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

/// What [`Ck::narrow`] changed, for [`Ck::widen`] to restore.
pub(super) type Saved<'a> = Vec<(usize, Option<Ty>, Option<Rc<Origin<'a>>>)>;

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
        otherwise: &'a Expr,
        out: Ty,
        no: Facts,
    },
    If3(Ty),
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
    CondOf,
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
        level: usize,
        tys: Vec<Ty>,
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
}

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
    ret: Ret,
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

    fn take(&mut self) -> Ret {
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

    fn take_cond(&mut self) -> (Ty, Facts, Facts) {
        match self.take() {
            Ret::Cond(t, y, n) => (t, y, n),
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
                for (map, set) in [(&mut self.unnamed, u), (&mut self.made, made)] {
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
                    None => v.without_loose().union(&d),
                    Some(Pattern::Atom {
                        name,
                        fields,
                        items,
                        ..
                    }) if fields.is_empty() && items.is_empty() => {
                        // A bare pattern matches the atom with any payload or none.
                        let mut rest = v.diff(&Ty::set(any_payload(name)));
                        rest.payloads.remove(name.as_str());
                        rest.union(&d)
                    }
                    Some(_) => v.union(&d),
                };
                m.ty(t);
            }
            Frame::If1(e) => {
                let (c, yes, no) = m.take_cond();
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
                m.k(Frame::If2 { otherwise, out, no });
                self.under(m, &yes, then);
            }
            Frame::If2 { otherwise, out, no } => {
                let a = m.take_ty();
                m.k(Frame::If3(out.union(&a)));
                self.under(m, &no, otherwise);
            }
            Frame::If3(out) => {
                let b = m.take_ty();
                m.ty(out.union(&b));
            }
            Frame::Widen(saved) => {
                let r = m.take();
                self.widen(saved);
                m.ret = r;
            }
            Frame::CondIs(e) => {
                let v = m.take_ty();
                let ExprKind::Is { of, ty, negated } = &e.kind else {
                    unreachable!("an `is`")
                };
                let t = denoted(ty);
                let bool_ = Ty::carrier(Carrier::Bool);
                let b = match (&of.kind, self.t.res.uses.get(&of.span)) {
                    (ExprKind::Name(_), Some(Ref::Bound(ids))) if ids.len() == 1 => ids[0],
                    _ => {
                        m.ret = Ret::Cond(bool_, Vec::new(), Vec::new());
                        return;
                    }
                };
                let (yes, no) = (vec![(b, v.meet(&t), e.span)], vec![(b, v.diff(&t), e.span)]);
                m.ret = match negated {
                    false => Ret::Cond(bool_, yes, no),
                    true => Ret::Cond(bool_, no, yes),
                };
            }
            Frame::CondNot(span) => {
                let (t, yes, no) = m.take_cond();
                let sig = op_sig("!");
                let t = self
                    .apply("`!`", &sig, vec![Some(Arg::of(t))], true, span)
                    .0;
                m.ret = Ret::Cond(t, no, yes);
            }
            Frame::CondAnd1 { op, b, span } => {
                let (ta, ya, na) = m.take_cond();
                let first = if op == "&&" { &ya } else { &na };
                let saved = self.narrow(first);
                m.k(Frame::CondAnd2(Box::new(CondAnd {
                    op,
                    span,
                    ta,
                    ya,
                    na,
                    saved,
                })));
                m.job(Job::Cond(b));
            }
            Frame::CondAnd2(s) => {
                let (tb, yb, nb) = m.take_cond();
                let CondAnd {
                    op,
                    span,
                    ta,
                    ya,
                    na,
                    saved,
                    ..
                } = *s;
                self.widen(saved);
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
                m.ret = if op == "&&" {
                    Ret::Cond(t, [ya, yb].concat(), Vec::new())
                } else {
                    Ret::Cond(t, Vec::new(), [na, nb].concat())
                };
            }
            Frame::CondOf => {
                let t = m.take_ty();
                m.ret = Ret::Cond(t, Vec::new(), Vec::new());
            }
            Frame::Logic1 { op, b, span } => {
                let (ta, ya, na) = m.take_cond();
                let first = if op == "&&" { ya } else { na };
                m.k(Frame::Logic2 { op, span, ta });
                self.under(m, &first, b);
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
                    params, tys, level, ..
                } = *s;
                let sig = self.generalize(level, Sig::one(params, tys, result));
                m.ret = Ret::Sig(sig);
            }
            Frame::AtomArgs(s) => self.atom_step(m, s),
            Frame::CallAlso { id, from, sig } => {
                let out = m.take_ty();
                if let Some(o) = self.whence.get(&id).map(|o| o.span) {
                    let t = self.t;
                    let name = &t.funcs[&id].name;
                    self.also(from, o, || format!("`{name}` is declared here, `{sig}`"));
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
            Frame::LambdaEnd { names, level, tys } => {
                let result = m.take_ty();
                let sig = self.generalize(level, Sig::one(names, tys, result));
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
                    self.error(span, format!("the lambda is `{s}`, not `{e}`"));
                }
                self.fitted(span, order, extra);
                m.ty(Ty::func(e));
            }
        }
    }

    /// `e` checked with the binders of `facts` narrowed.
    fn under(&mut self, m: &mut M<'a>, facts: &Facts, e: &'a Expr) {
        let saved = self.narrow(facts);
        m.k(Frame::Widen(saved));
        m.job(Job::Expr(e));
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
            self.env.insert(*id, t.clone());
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
                        self.error_with(d.span, format!("{what} is {dt}, not {shown}"), notes);
                    }
                }
                None => {
                    if !dt.subtype(t) {
                        let why = dt.refused(t);
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
            if self.t.uses_in(d.span, &[]).is_empty() {
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
                ty: lit_ty(&l.value, l.neg),
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
    /// function type is fitted to it, and a numeric literal adopts its one carrier.
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
            let t = self.adopt_to(&l, c);
            return m.ty(t);
        }
        m.job(Job::Expr(e));
    }

    fn expr_of(&mut self, m: &mut M<'a>, e: &'a Expr) {
        if let Some(l) = literal(e) {
            let t = match self.info.adopt.get(&l.span) {
                Some(v) => lit_ty(v, l.neg),
                None => lit_ty(&l.value, l.neg),
            };
            return m.ty(t);
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
            ExprKind::Rat(s) => m.ty(Ty::lit(&Value::rat(
                Rat::decimal(s).expect("the lexer's rat text is a decimal"),
            ))),
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
            self.data(&t, "interpolation", h.span);
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
                self.data(&t, "a tuple", e.span);
            }
            s.out.push(t);
        }
        if let Some(e) = s.es.get(s.started) {
            s.started += 1;
            m.k(Frame::Tuple(s));
            return m.job(Job::Expr(e));
        }
        m.ty(Ty::tuple(std::mem::take(&mut s.out)));
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
                m.k(Frame::CondOf);
                m.job(Job::Expr(e));
            }
        }
    }

    /// A binary operator other than `&&` and `||` applied to its arguments `x` and `y`, the
    /// second written `b`.
    fn binary_end(&mut self, op: &'static str, x: Arg, y: Arg, b: &'a Expr, span: Span) -> Ty {
        match op {
            "==" | "!=" => {
                self.data(&x.ty, &format!("`{op}`"), span);
                self.data(&y.ty, &format!("`{op}`"), span);
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
            .insert(name.into(), Some(vec![Shape { items, fields }]));
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
            self.data(&x.ty, "`String`", span);
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
                Piece::Dyn => self.any(&format!("a call of `{}`", s.what), span),
                Piece::Var(_) => s.out = s.out.union(&Ty::dynamic()),
                p if p.is_atoms() => {}
                p => {
                    self.error(span, format!("`{}` is {}, not a function", s.what, p.ty()));
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
                self.apply(&what, &s.sig, args, false, s.span).0
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
                match misfit.row() {
                    Some(row) => self.rejects_with(row, at, message, Vec::new()),
                    None => self.error_with(at, message, Vec::new()),
                }
            }
            return m.ty(Ty::empty());
        }
        let message = format!("`{what}` does not take these arguments: it is `{sig}`");
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
            _ => match crate::resolve::prelude_layer(name) {
                Some(1) if let Some(p) = bit_prim(name) => {
                    self.bits(m, name, p, Some((x, of)), positional, named, curry, span)
                }
                Some(1) if positional.is_empty() && named.is_empty() && !curry => {
                    self.word(m, name, &[], Some(x), span)
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
        let mut tys = Vec::new();
        for p in slots {
            let t = match p.and_then(|p| p.ty.as_ref()) {
                Some(t) => denoted(t),
                None => Ty::var(format!("${}", self.class()).into()),
            };
            if let Some(p) = p {
                let id = self.id(p.span, &p.name);
                self.env.insert(id, t.clone());
            }
            tys.push(t);
        }
        m.k(Frame::LambdaEnd { names, level, tys });
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
            self.rejects(
                Row::ParameterKinds,
                span,
                format!(
                    "the lambda takes {} parameter{}, and `{e}` passes {} by position",
                    params.len(),
                    if params.len() == 1 { "" } else { "s" },
                    pos.len()
                ),
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
                    self.rejects(
                        Row::ParameterKinds,
                        p.span,
                        format!(
                            "the lambda's parameter `{}` is not a parameter of `{e}`{fix}",
                            p.name
                        ),
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
                if !r.subtype(&want) {
                    let why = r.refused(&want);
                    self.error(
                        s.body.span,
                        format!("the lambda returns {r}, and `{}` returns {want}{why}", s.e),
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
                            if !t.subtype(&a) {
                                let why = t.refused(&a);
                                self.error(
                                    p.span,
                                    format!(
                                        "the lambda's parameter `{}` is {a}, and `{}` passes {t}{why}",
                                        p.name, s.e
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
