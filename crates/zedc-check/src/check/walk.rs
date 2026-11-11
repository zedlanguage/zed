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
use zedc_resolve::resolve::tables::recursion;

/// Checks a resolved unit.
pub fn check(unit: &[Stmt], res: &Resolution) -> Info {
    check_text(unit, res, None)
}

/// [`check`], with the unit's text when it is known, which a message quotes: the line each
/// fix of a rejected literal rewrites.
pub fn check_text(unit: &[Stmt], res: &Resolution, text: Option<&str>) -> Info {
    check_with(&Tables::with_text(unit, res, text), unit)
}

/// Checks a unit whose binder tables are `t`, as [`check`] does with tables it builds.
pub fn check_with<'a>(t: &Tables<'a>, unit: &'a [Stmt]) -> Info {
    // Complexity tradeoff (COMPLEXITY.md F32): emptiness results kept for the whole thread let
    // a unit checked after an equal one look up keys equal to its types but built apart, each
    // compared in full, O(n²) for a unit of size n. Dropping them here shares results within
    // one unit only: an equal later unit decides them again, O(n) more work, rather than
    // compare them. Keying by identity instead loses the reuse within a unit that the L1.23
    // tuple-difference test needs.
    KType::forget_emptiness();
    // The types the messages write put their definitions in one table, which `Ck::finish`
    // lays out message by message.
    let _defs = defs::collect();
    // The type variables of the signatures and messages are named apart from every name the
    // unit binds, in any scope: a field is not in scope, so its name is free.
    let _names = ty::ProgramNames::hold(
        (t.res.binders.iter())
            .filter(|b| b.kind != zedc_resolve::resolve::Kind::Field)
            .map(|b| b.name.as_str()),
    );
    let mut ck = Ck::new(t);
    ck.bounds();
    ck.walk(unit);
    ck.finish();
    #[cfg(debug_assertions)]
    clean_check::flush();
    ck.info
        .errors
        .sort_by(|a, b| (a.span, &a.message, &a.menu).cmp(&(b.span, &b.message, &b.menu)));
    ck.info.errors.dedup();
    ck.info
}

/// The type of the binary operator `op` applied to arguments of the types `args`, with the
/// errors the application reports: how an operator treats loose and family atoms.
pub fn operator(op: &str, args: &[Ty]) -> (Ty, Vec<String>) {
    let res = zedc_resolve::resolve::resolve(&[]).expect("the empty unit resolves");
    let t = Tables::new(&[], &res);
    let _defs = defs::collect();
    let mut ck = Ck::new(&t);
    let args = args.iter().map(|a| Some(Arg::of(a.clone()))).collect();
    let demand = match op {
        "&&" | "||" => Demand::First,
        _ => Demand::All,
    };
    let (out, _) = ck.apply_demanding(
        &format!("`{op}`"),
        &op_sig(op),
        args,
        true,
        demand,
        Span { start: 0, end: 0 },
    );
    let text = ck.t.text;
    let messages = (ck.errors.into_iter())
        .map(|f| {
            let mut e = f.written(text);
            lay_out(&mut e.message, &mut e.notes, &mut e.menu);
            e.message + &e.menu
        })
        .collect();
    (out, messages)
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
        /// The node of the `if`, and the nodes where the condition holds and where it fails.
        nodes: (usize, usize, usize),
        /// Whether each branch is unreachable by its names' types ([`unreachable()`]).
        dead: (bool, bool),
    },
    If3 {
        then: &'a Expr,
        otherwise: &'a Expr,
        out: Ty,
        a: Box<Ty>,
        nodes: (usize, usize, usize),
        dead: (bool, bool),
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
    /// A binding, with the number of errors before its value is checked.
    Bind(&'a Stmt, usize),
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
        of: Span,
        span: Span,
    },
    /// A read `v[k]`: the type of `v`, the span of `v` and the span of the read.
    AtKey(Ty, Span, Span),
    /// A read `v[i]` with a literal `i`: as [`Frame::AtKey`], with `i` if it is a component number.
    AtIndex(Ty, Option<usize>, Span, Span),
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
    /// While a closed default is checked for `given`: the number of errors before it.
    closed: Option<usize>,
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
        // A statement other than a binding drops the errors of its operations on literals
        // that met a carrier here.
        self.drop_met(0);
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
                if self.main_tails.contains(&e.span) {
                    self.status_in_range(e, &t);
                }
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
                // A negated literal is a literal (L1.26a): `-3r` is the value -3 at `rat`, as
                // `3r` is 3, so a divisor `-3r` holds no zero. An `int` or `f64` literal under
                // `-` is read whole by `read_literal`; a `rat` literal keeps its carrier and
                // comes here.
                if op == "-"
                    && let Some(ExprKind::Rat(d)) = x.expr.map(|e| &e.kind)
                    && let Ok(Some(r)) = Rat::decimal(d)
                {
                    m.ty(lit_ty(&Value::rat(r), true));
                    return;
                }
                // A `-` of an operation on literals alone at the top level is one too, and
                // takes the carrier of what it meets, as `-(1 + 2)` in `-(1 + 2) * 0.5f64`
                // ([`Self::lit_op_meets`]).
                let from = self.errors.len();
                if self.level == 0
                    && op == "-"
                    && x.expr.is_some_and(|e| self.lit_ops.contains(&e.span))
                {
                    self.lit_ops.insert(span);
                    if x.expr.is_some_and(|e| self.lit_open.contains(&e.span)) {
                        self.lit_open.insert(span);
                    }
                }
                let sig = op_sig(op);
                let t = self
                    .apply(&format!("`{op}`"), &sig, vec![Some(x)], true, span)
                    .0;
                self.lit_wrote(span, from);
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
                    dead: (unreachable(&yes), unreachable(&no)),
                    no,
                    nodes: (self.arms.here(), holds, fails),
                });
                self.under(m, &yes, holds, then);
            }
            Frame::If2 {
                then,
                otherwise,
                out,
                no,
                nodes,
                dead,
            } => {
                let a = m.take_ty();
                m.k(Frame::If3 {
                    then,
                    otherwise,
                    out,
                    a: Box::new(a),
                    nodes,
                    dead,
                });
                self.under(m, &no, nodes.2, otherwise);
            }
            Frame::If3 {
                then,
                otherwise,
                out,
                a,
                nodes: (at, holds, fails),
                dead,
            } => {
                let b = m.take_ty();
                // An unreachable branch is still checked, and adds nothing to the result
                // (sec:constraints: an arm a narrowing test makes bottom adds nothing to the join).
                // The reduced product is asked only of a branch whose type adds something to
                // the other's: there alone its answer changes the result ([`Ck::no_state_reaches`]).
                let dead = (
                    dead.0 || (!a.subtype(&b) && self.no_state_reaches(at, holds)),
                    dead.1 || (!b.subtype(&a) && self.no_state_reaches(at, fails)),
                );
                let t = match dead {
                    (true, true) => Ty::empty(),
                    (true, false) => b,
                    (false, true) => *a,
                    (false, false) => self.branches(then, &a, otherwise, &b),
                };
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
                    .apply_demanding(
                        &format!("`{op}`"),
                        &sig,
                        vec![Some(Arg::of(ta)), Some(Arg::of(b.t))],
                        true,
                        Demand::First,
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
                    .apply_demanding(
                        &format!("`{op}`"),
                        &sig,
                        vec![Some(Arg::of(ta)), Some(Arg::of(tb))],
                        true,
                        Demand::First,
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
                    parts: parts(e, self.t.text),
                    branches: branch_lits(e, self.t.text, &self.kept_ops),
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
            Frame::Bind(s, before) => {
                let v = m.take_ty();
                self.bind(s, v, before);
            }
            Frame::Declared(s) => {
                let sig = m.take_sig();
                let StmtKind::Function(f) = &s.kind else {
                    unreachable!("a function")
                };
                if f.main.is_some() {
                    self.exit_status(f, &sig);
                }
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
                    self.also_notes(from, |ck| {
                        built(1);
                        let mut notes = vec![Note {
                            span: o,
                            text: ck.declared_step(id, &sig),
                        }];
                        ck.declared_emptied(id, &mut notes);
                        notes
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
            Frame::Index1 { k, of, span } => {
                let v = m.take_ty();
                let ExprKind::Int { .. } = &k.kind else {
                    m.k(Frame::AtKey(v, of, span));
                    m.job(Job::Arg(k, Want::default()));
                    return;
                };
                let i = match literal(k, None).map(|l| l.value) {
                    Some(Value::Int(i)) => i,
                    _ => return m.ty(Ty::dynamic()),
                };
                m.k(Frame::AtIndex(v, usize::try_from(i).ok(), of, span));
                m.job(Job::Arg(k, Want::default()));
            }
            Frame::AtKey(v, of, span) => {
                let x = m.take_arg();
                let dense = self.dense_read(&v, span);
                let t = self.at_key(&v, x, Some(of), span, dense);
                m.ty(t);
            }
            Frame::AtIndex(v, i, of, span) => {
                let x = m.take_arg();
                let dense = self.dense_read(&v, span);
                let t = self.at_index(&v, i, x, Some(of), span, dense);
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
        // A cycle is a recursion, rejected until layer L6 (`recursion`). Every other statement
        // is still checked, one that uses a statement of a cycle among them too: stopping at the
        // cycle left the scope's other definitions with no signature and their errors
        // unreported. Each name the cycle defines has no value, as a rejected expression gives
        // (`Frame::Fail`), so a use of it adds no error of its own.
        let (order, cycles) = self.t.order_around_cycles(&items);
        for cycle in cycles {
            let (span, message) = recursion(&items, &cycle);
            self.error_with(span, message, Vec::new());
            for &k in &cycle {
                let st = items[k];
                match &st.kind {
                    StmtKind::Function(f) => {
                        let id = self.id(st.span, &f.name);
                        self.env.insert(id, Ty::empty());
                    }
                    StmtKind::Bind { targets, .. } => {
                        for t in targets {
                            if let Target::Name(n, _) = t {
                                let id = self.id(st.span, n);
                                self.env.insert(id, Ty::empty());
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
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
            if f.main.is_some() {
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
                m.k(Frame::Bind(s, self.errors.len()));
                m.job(Job::Expr(value));
            }
            StmtKind::Function(f) => {
                if f.main.is_some() {
                    self.main_tails(&f.body);
                }
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

    /// The binding `s` of a value of `v`, whose check found the errors after the first
    /// `before`.
    fn bind(&mut self, s: &'a Stmt, v: Ty, before: usize) {
        let StmtKind::Bind { targets, value, .. } = &s.kind else {
            unreachable!("a binding")
        };
        if self.level == 0 {
            self.drop_met(before);
            // Each target is bound to its component where the value is a tuple display of
            // as many components, `a, b = (0.5, 1)`; `_` names none.
            let name = |t: &'a Target| match t {
                Target::Name(n, _) => n.as_str(),
                Target::Wild => "_",
            };
            let mut found = match (&targets[..], &value.kind) {
                ([t], _) => unfixed_parts(value, name(t), true, self.t.text),
                (ts, ExprKind::Tuple(items)) if items.len() == ts.len() => (ts.iter().zip(items))
                    .flat_map(|(t, x)| unfixed_parts(x, name(t), false, self.t.text))
                    .collect(),
                _ => Vec::new(),
            };
            // The literals the value ends in through a branch, a block, an index or a call,
            // for every form of the targets; a literal in a called body may stand before the
            // binding in the text, and the parts are put back in the order of the text.
            let tails = self.unfixed_tails(value, &v);
            if !tails.is_empty() {
                found.extend(tails);
                found.sort_by_key(|(p, _, _)| p.start);
            }
            let what = match &targets[..] {
                [Target::Name(n, _)] => format!("the value of `{n}`"),
                [_] => "the value".to_string(),
                ts => format!(
                    "the value bound to `{}`",
                    ts.iter().map(name).collect::<Vec<_>>().join(", ")
                ),
            };
            self.rejects_unfixed(before, found, &what);
        }
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
            closed: None,
        };
        self.infer_given(m, Box::new(s));
    }

    /// Rejects each part of a value bound to a name with nothing to give its literals a
    /// carrier, of the list `parts` of the part, the place and the message, in the order of the
    /// text ([`unfixed_parts`]) (row UnfixedDecimal). The errors the value's check found,
    /// those after the first `before`, are dropped where they lie in a rejected part: there an
    /// operator met an operation on integer literals typed `int`, as `/` meets `1 + 2` in
    /// `y = (1 + 2) / 3`, which is rejected as the value's `/`, not as its operands (step
    /// L1.26a). An error in another part, `y = (0.5, 1 + "a")`, stays.
    ///
    /// Complexity tradeoff: the naive test of each error against each part costs their
    /// product, the square of the width over a wide tuple with an error in each component.
    /// The parts lie apart in the order of the text, so each error looks up the last part
    /// that starts at or before it by binary search, `O(e log p)` for `e` errors and `p` parts.
    fn rejects_unfixed(&mut self, before: usize, parts: Vec<(Span, Span, Msg)>, what: &str) {
        if parts.is_empty() {
            return;
        }
        let found = self.errors.split_off(before);
        let inside = |e: &Found| {
            let k = parts.partition_point(|(p, _, _)| p.start <= e.span.start);
            (k.checked_sub(1)).is_some_and(|k| e.span.end <= parts[k].0.end)
        };
        let kept: Vec<Found> = found.into_iter().filter(|e| !inside(e)).collect();
        self.errors.extend(kept);
        let parts = parts.into_iter().map(|(_, at, m)| (at, m)).collect();
        self.reject_unfixed(&what, parts);
    }

    /// Rejects the literals of `parts`, each its place and its message, in the order of the
    /// text, all in `what` (row UnfixedDecimal): one part with its derivation, as
    /// [`Self::reject`]; two or more in one message ([`grouped`]), each part's derivation
    /// after its step, with no step written twice.
    fn reject_unfixed(&mut self, what: &dyn fmt::Display, parts: Vec<(Span, Msg)>) {
        let Some(&(at, _)) = parts.first() else {
            return;
        };
        if parts.len() == 1 {
            let (at, m) = parts.into_iter().next().expect("one part");
            let notes = self.derive(&[at]);
            return self.reject(Some(Row::UnfixedDecimal), at, m, notes);
        }
        let sites: Vec<Span> = parts.iter().map(|(s, _)| *s).collect();
        let (m, steps) = grouped(what, parts);
        // A part's derivation that only shows the part itself repeats its step, and is left
        // out; the rest follow the part's step, each once.
        let mut shown = HashSet::new();
        let mut notes = Vec::with_capacity(steps.len());
        for (site, step) in sites.into_iter().zip(steps) {
            notes.push(step);
            for n in self.derive(&[site]) {
                if n.span != site && shown.insert(n.clone()) {
                    notes.push(n);
                }
            }
        }
        self.reject(Some(Row::UnfixedDecimal), at, m, notes);
    }

    /// The decimal literals with no suffix that the value `x`, bound outside every function
    /// and of type `t`, ends in where nothing gives them a carrier, other than those
    /// [`unfixed_parts`] reads (DESIGN.md L1.26a: "`y = g(c)` is rejected at the `2.5`, which
    /// nothing fixes"; L1.26b: "Where nothing fixes its carrier a decimal literal is
    /// rejected"). A value ends in each branch of an `if`, the value of a block, each component
    /// of a tuple display, each payload of an atom, each component of a tuple display that is
    /// indexed, and what a declared function it calls returns, each read the same way in turn:
    /// `0.5` in `y = if c { 0.5 } else { 1 }`, in `y = (0.5, 1)[0]`, and in `y = f()` with
    /// `f() = 0.5`. Outside a function nothing gives such a literal a carrier, since it is no
    /// operand. In a function's body it may join the class of a parameter, as `0.5` does in
    /// `g(x) = if x > 0 { x } else { 0.5 }`, where the call's arguments fix it, `y = g(x:
    /// 1.0f64)`: so a literal reached through a call is rejected only where the type at its
    /// place holds its value alone, not every `f64`, or where it is in a payload. `x` itself,
    /// and its tuple components and payloads that are reached through none of these, are
    /// [`unfixed_parts`]'s. Each message names the literal with each carrier it fits, and the
    /// call it came through. Each part is a literal's site, with its message.
    ///
    /// Complexity tradeoff: the naive way reads the body of a called function at every call,
    /// a function called inside the functions it calls again and again, which grows with the
    /// number of paths through the calls, exponential in their depth; and it reads the bodies
    /// again for each binding that calls them, so `b` bindings each calling the last of a
    /// chain of `m` functions cost `O(b m)`. Here a body is entered only where the type at the
    /// call holds an `f64` value alone and the body can end in a decimal literal
    /// ([`Self::tail_reach`]); the bodies a call outside every function reaches are read once
    /// for each function, place (in a payload or not) and type at the call, each body once
    /// ([`Self::call_tails`]), and a later call with the same three looks the literals up. A
    /// binding costs the size of its own value, the literals its calls reach, and the hash of
    /// the type at each call. Calls of one function at `k` types each read its bodies again:
    /// `O(k s)` for bodies of size `s`, a literal reached at each type a rejection.
    fn unfixed_tails(&mut self, x: &'a Expr, t: &Ty) -> Vec<(Span, Span, Msg)> {
        let src = self.t.text;
        let mut out = Vec::new();
        // A literal reached through two calls is one rejection.
        let mut sites: HashSet<Span> = HashSet::new();
        for (e, call) in self.tails(x, t.clone(), false, false, None) {
            let Some(l) = literal(e, src) else { continue };
            if !sites.insert(l.site) {
                continue;
            }
            let cs: Vec<Carrier> = [Carrier::F64, Carrier::Rat]
                .into_iter()
                .filter(|&c| fits(&l, c))
                .collect();
            let mut m = unfixed(&l, &cs, None);
            if let Some(c) = call {
                let callee = match &c.kind {
                    ExprKind::Call { callee, .. } => callee.span,
                    _ => c.span,
                };
                let name = src.map_or("", |s| &s[callee.start..callee.end]);
                m.text
                    .push_str(&format!("; the value holds it through a call of `{name}`"));
            }
            out.push((l.site, l.site, m));
        }
        out
    }

    /// The literals [`Self::unfixed_tails`] rejects in `x` of type `t`, each with the call
    /// outside every function it is reached through, if any. `deep` and `payload` say whether
    /// `x` is reached through a branch, a block, an index or a call, and whether it is in a
    /// payload. `inside` is the declared function whose body `x` is, read for
    /// [`Self::call_tails`]; there the calls are followed into their bodies, each body once.
    /// Outside every function each call's literals are those of [`Self::call_tails`].
    fn tails(
        &mut self,
        x: &'a Expr,
        t: Ty,
        deep: bool,
        payload: bool,
        inside: Option<usize>,
    ) -> Vec<(&'a Expr, Option<&'a Expr>)> {
        let src = self.t.text;
        let in_call = inside.is_some();
        let mut out = Vec::new();
        let mut seen: HashSet<usize> = inside.into_iter().collect();
        // Each place: its expression, whether it is reached through a branch, a block, an
        // index or a call, whether it is in a payload, and the type at it.
        let mut todo: Vec<(&'a Expr, bool, bool, Ty)> = vec![(x, deep, payload, t)];
        while let Some((e, deep, payload, ty)) = todo.pop() {
            match self.tail_of(e, src) {
                Tail::Lit(l) => {
                    let alone = || {
                        let s = Ty::set(ty.set.clone());
                        lit_ty(&l.value, l.neg()).subtype(&s)
                            && !Ty::carrier(Carrier::F64).subtype(&s)
                    };
                    if deep
                        && l.bare
                        && lit_carrier(&l.value) == Carrier::F64
                        && (payload || !in_call || alone())
                    {
                        out.push((e, None));
                    }
                }
                Tail::Branches(es) => {
                    todo.extend(es.into_iter().rev().map(|e| (e, true, payload, ty.clone())))
                }
                Tail::Components(items, by) => {
                    let n = items.len();
                    let deep = deep || by;
                    for (i, it) in items.iter().enumerate().rev() {
                        let c = (ty.tuples.iter())
                            .filter(|r| r.len() == n)
                            .fold(Ty::empty(), |a, r| a.union(&r[i]));
                        todo.push((it, deep, payload, c));
                    }
                }
                Tail::Indexed(items) => {
                    todo.extend((items.iter().rev()).map(|it| (it, true, payload, Ty::empty())))
                }
                Tail::Payload(es) => {
                    todo.extend(es.into_iter().rev().map(|e| (e, deep, true, Ty::empty())))
                }
                Tail::Call(id) => {
                    if !decimal_alone(&ty) || !self.tail_reach(id) {
                        continue;
                    }
                    if in_call {
                        if seen.insert(id) {
                            todo.push((&self.t.funcs[&id].body, true, payload, ty));
                        }
                    } else {
                        let found = self.call_tails(id, payload, ty);
                        out.extend(found.iter().map(|&l| (l, Some(e))));
                    }
                }
                Tail::None => {}
            }
        }
        out
    }

    /// The literals [`Self::unfixed_tails`] rejects in the body of the declared function `id`
    /// called outside every function, in a payload or not, where the type at the call is `t`:
    /// read once for each of the three ([`Self::tails`]), then looked up.
    fn call_tails(&mut self, id: usize, payload: bool, t: Ty) -> Rc<[&'a Expr]> {
        let key = (id, payload, t);
        if let Some(found) = self.tail_calls.get(&key) {
            return found.clone();
        }
        let body = &self.t.funcs[&id].body;
        let found: Rc<[&'a Expr]> = (self.tails(body, key.2.clone(), true, payload, Some(id)))
            .into_iter()
            .map(|(e, _)| e)
            .collect();
        self.tail_calls.insert(key, found.clone());
        found
    }

    /// Whether the body of the declared function `id` can end in a decimal literal with no
    /// suffix, directly or through the declared functions it ends in a call of, as
    /// [`Self::unfixed_tails`] reads a value ([`Self::tail_of`]).
    ///
    /// Complexity tradeoff: the naive way reads the bodies at each question, the size of every
    /// body reached each time. Here the first question reads each body once, marks those that
    /// end in such a literal, and carries the mark to the functions that end in a call of a
    /// marked one along the calls reversed, each function and call once; each later question
    /// is a lookup: `O(s)` once for the size `s` of the bodies, then `O(1)`.
    fn tail_reach(&mut self, id: usize) -> bool {
        if self.tail_reach.is_none() {
            let src = self.t.text;
            let mut callers: HashMap<usize, Vec<usize>> = HashMap::new();
            let mut marked: HashSet<usize> = HashSet::new();
            for (&f, func) in &self.t.funcs {
                let mut todo = vec![&func.body];
                while let Some(e) = todo.pop() {
                    match self.tail_of(e, src) {
                        Tail::Lit(l) => {
                            if l.bare && lit_carrier(&l.value) == Carrier::F64 {
                                marked.insert(f);
                            }
                        }
                        Tail::Branches(es) | Tail::Payload(es) => todo.extend(es),
                        Tail::Components(items, _) | Tail::Indexed(items) => todo.extend(items),
                        Tail::Call(g) => callers.entry(g).or_default().push(f),
                        Tail::None => {}
                    }
                }
            }
            let mut todo: Vec<usize> = marked.iter().copied().collect();
            while let Some(g) = todo.pop() {
                for &f in callers.get(&g).into_iter().flatten() {
                    if marked.insert(f) {
                        todo.push(f);
                    }
                }
            }
            self.tail_reach = Some(marked);
        }
        self.tail_reach.as_ref().is_some_and(|m| m.contains(&id))
    }

    /// What `e` ends in, one step down, as [`Self::unfixed_tails`] reads a value: a literal;
    /// the branches of an `if`; the value of a block, one or the components of several; the
    /// components of a tuple display, of one indexed; the payload of an atom; a call of a
    /// declared function; or none of these. It costs the number of the parts it names.
    fn tail_of(&self, e: &'a Expr, src: Option<&str>) -> Tail<'a> {
        if let Some(l) = literal(e, src) {
            return Tail::Lit(l);
        }
        match &e.kind {
            ExprKind::If {
                then, otherwise, ..
            } => Tail::Branches(vec![then, otherwise]),
            ExprKind::Block(stmts) => match stmts.last().map(|s| &s.kind) {
                Some(StmtKind::Return(es)) if es.len() == 1 => Tail::Branches(vec![&es[0]]),
                Some(StmtKind::Return(es)) => Tail::Components(es, true),
                _ => Tail::None,
            },
            ExprKind::Tuple(items) => Tail::Components(items, false),
            ExprKind::Index(base, _) => match &base.kind {
                ExprKind::Tuple(items) => Tail::Indexed(items),
                _ => Tail::None,
            },
            ExprKind::Call {
                callee,
                positional,
                named,
                curry: false,
            } if matches!(callee.kind, ExprKind::Atom(_)) => Tail::Payload(
                positional
                    .iter()
                    .chain(named.iter().map(|(_, v)| v))
                    .collect(),
            ),
            ExprKind::Call {
                callee,
                curry: false,
                ..
            } => self.declared(callee).map_or(Tail::None, Tail::Call),
            _ => Tail::None,
        }
    }

    /// The type each parameter's annotation or closed default gives it, in turn; then the
    /// parameters bound.
    fn infer_given(&mut self, m: &mut M<'a>, mut s: Box<InferF<'a>>) {
        if let Some(before) = s.closed.take() {
            let t = m.take_ty();
            // A default that reads no parameter is bound to its parameter as a value is to a
            // name, and nothing gives a decimal literal in it a carrier: `rate = 0.2` is
            // rejected as `rate = 0.2;` is (step L1.26b).
            let p = &s.f.params[s.given.len()];
            let d = p.default.as_ref().expect("a closed default");
            self.drop_met(before);
            let what = format!("the default of `{}`", p.name);
            self.rejects_unfixed(before, unfixed_parts(d, &p.name, true, self.t.text), &what);
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
            s.closed = Some(self.errors.len());
            m.k(Frame::InferGiven(s));
            return m.job(Job::Expr(d));
        }
        let f = s.f;
        if let Some(ports) = f.ports() {
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
            // A field of `main`'s argument is declared by the parameter `m: MainArgs`, where
            // its type sits (the builder's `main_header`); with no parameter, at its use.
            let site = match (&f.main, &p.ty) {
                (Some(_), Some(a)) if a.span.start < a.span.end => a.span,
                _ => p.span,
            };
            self.origin(*id, site, why, None);
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
                        let both =
                            format!("{} | {}", self.show_in_union(t), self.text_in_union(&dt));
                        let dt = self.text(&dt);
                        notes.extend(default_repairs(&p.name, &dt, &shown, &both, d.span));
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
                        let both =
                            format!("{} | {}", self.text_in_union(t), self.text_in_union(&dt));
                        let (dt, t) = (self.text(&dt), self.text(t));
                        let menu = default_repairs(&p.name, &dt, &t, &both, d.span);
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

    /// Records where the program writes the literal `l` ([`Ck::spells`]): a zero under `-`, as
    /// `-0`, also with its `-`, since its value has no sign.
    fn spells_lit(&mut self, l: &Lit) {
        self.spells(&l.value, l.span);
        if l.neg() && is_zero(&l.value) {
            self.spells(&l.value, l.site);
        }
    }

    /// An argument: a numeric literal kept unadopted, a function in a slot of function type
    /// fitted to it, else the expression's type.
    fn arg(&mut self, m: &mut M<'a>, e: &'a Expr, want: Want) {
        if let Some(l) = literal(e, self.t.text) {
            self.spells_lit(&l);
            m.ret = Ret::Arg(Arg {
                ty: lit_ty(&l.value, l.neg()),
                lit: Some(l),
                at: Some(e.span),
                expr: Some(e),
                parts: None,
                branches: None,
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
        if let (Some(l), Some(c)) = (literal(e, self.t.text), want.num) {
            self.spells_lit(&l);
            let from = self.errors.len();
            let t = self.adopt_to(&l, c);
            // A rejected literal is its own error: read at the carrier wanted, it causes no
            // second one where its type is checked.
            let t = match self.errors.len() > from {
                true => Ty::carrier(c),
                false => t,
            };
            return m.ty(t);
        }
        m.job(Job::Expr(e));
    }

    fn expr_of(&mut self, m: &mut M<'a>, e: &'a Expr) {
        match read_literal(e, self.t.text) {
            Ok(Some(l)) => {
                self.spells_lit(&l);
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
                Ok(r) => {
                    let v = Value::rat(r.expect("the lexer's rat text is a decimal"));
                    self.spells(&v, e.span);
                    m.ty(Ty::lit(&v))
                }
                Err(r) => {
                    self.error(e.span, unread_literal(&r));
                    m.ty(Ty::empty())
                }
            },
            ExprKind::Int { .. } | ExprKind::Float { .. } => m.ty(Ty::empty()),
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
                // `-0r` is the value `0r`; its `-` is kept for the messages that print it.
                if *op == "-" && zero_rat(a) {
                    self.spells(&Value::rat(Rat::int(0.into())), e.span);
                }
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
            // A hole gives no carrier to a literal its value ends in through a branch, a
            // block, an index or a call either, `"${if c { 0.5 } else { 1 }}"`. In a
            // function's body such a literal may join a parameter's class, which the call
            // fixes, so only holes outside every function are read so.
            if self.level == 0 {
                let found = (self.unfixed_tails(h, &t).into_iter())
                    .map(|(_, at, m)| (at, m))
                    .collect();
                self.reject_unfixed(&"the interpolation", found);
            }
            s.holes.push(t);
        }
        while let Some(p) = s.parts.get(s.i) {
            s.i += 1;
            match p {
                StrPart::Text(t) => s.text.push_str(t),
                StrPart::Hole(h) => {
                    // A hole takes every carrier, as `String` does, so it gives a literal
                    // none: `"${0.5}"` is rejected, and `"${1}"` is an `int` (step L1.26b);
                    // so is a decimal in a component of a tuple or a payload of an atom
                    // there, `"${(0.5, 1)}"`. The walk costs the size of the hole
                    // ([`value_parts`]).
                    for (x, _) in value_parts(h).leaves {
                        if let Some(l) = literal(x, self.t.text).filter(|l| l.bare)
                            && lit_carrier(&l.value) != Carrier::Int
                        {
                            let notes = self.derive(&[l.site]);
                            let m = unfixed(&l, &[Carrier::F64, Carrier::Rat], None);
                            self.reject(Some(Row::UnfixedDecimal), l.site, m, notes);
                        }
                    }
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
    /// their union; but where one branch is a literal without a suffix, or of a class of generic literals
    /// only, as `1 + 1` is inside a function, and the other's type is one class, beside atoms
    /// or alone ([`Ck::class_beside_atoms`]), the literal joins the class,
    /// generic, or the classes merge, and the `if` has the class's type (L1.26a). An operation
    /// on integer literals alone whose other branch is of no class keeps its value instead.
    fn branches(&mut self, then: &Expr, a: &Ty, otherwise: &Expr, b: &Ty) -> Ty {
        // An operation on integer literals alone keeps its value in an `if` (L1.26a: "an
        // operation on literals alone keeps its value in an `if`, so `if c { 1 + 1 } else {
        // 1.5 }` is `2 | 1.5`") where the other branch is a literal, another such operation,
        // a carrier or a union of values: it is its value, as a lone literal there is, so
        // `if c { 2 + 1 } else { 1 }` is `1 | 3`. Its own class, which nothing else joins,
        // takes `int` where nothing fixes it, so at run time it is that `int`. Where the `if`
        // is an argument, the operation is one of its branches ([`branch_lits`]) and takes
        // the carrier of its use as it would alone: `h(if c { 1 + 1 } else { 1 })` at an
        // `f64` parameter is `2.0 | 1.0`, and where the `if` meets a class, the operation's
        // class merges with it. So each kept operation's class is recorded ([`Ck::kept_ops`]),
        // and the entry of one not kept is removed, so that a stale entry is never read.
        let (ka, kb) = (self.kept(then, a), self.kept(otherwise, b));
        let free =
            |ck: &Self, k: &Option<Ty>, t: &Ty| k.is_some() || ck.class_beside_atoms(t).is_none();
        let keep = (ka.is_some() || kb.is_some()) && free(self, &ka, a) && free(self, &kb, b);
        for (e, k, t) in [(then, &ka, a), (otherwise, &kb, b)] {
            let span = exported(e).span;
            match (keep && k.is_some()).then(|| self.class_of_ty(t)).flatten() {
                Some(c) => self.kept_ops.insert(span, c),
                None => self.kept_ops.remove(&span),
            };
        }
        if keep {
            return ka.as_ref().unwrap_or(a).union(kb.as_ref().unwrap_or(b));
        }
        // The other branch may hold atoms beside its class, `T | #divByZero` for `(1 + x) /
        // (x * y)`: the literal joins the class all the same ("as a branch of an `if` whose
        // other branch is of a class"), and the atoms stay in the result.
        for (e, t, other) in [(then, a, b), (otherwise, b, a)] {
            let Some(k) = self.class_beside_atoms(other) else {
                continue;
            };
            let joined = match self.class_of_ty(t) {
                Some(g) if self.classes[g].generic => self.merge(k, g, "an `if`", e.span),
                Some(_) => false,
                None => literal(exported(e), None)
                    .filter(|l| l.bare)
                    .is_some_and(|l| self.join(k, &l.joining(), false)),
            };
            if joined {
                return other.clone();
            }
        }
        a.union(b)
    }

    /// The value of the branch `e`, of type `t`, as a literal type, when `e` is an operation on
    /// integer literals alone with no `/`, as `1 + 1`, typed as the class of literals of its
    /// own that such an operation makes inside a function: `2`. `None` for anything else,
    /// and where its value is no number, as `2 ^ -1`. A `/`, a decimal literal or a `rat` one makes
    /// no such value ([`literals_alone`]): a `/` of literals that meets no carrier is rejected, and
    /// a decimal has no value until its carrier is fixed (L1.26b).
    // Complexity tradeoff: one walk of the operation to see that it holds integer literals
    // alone and one to fold it, O(its size), at the one `if` whose branch it is; an operation
    // is the branch of at most one `if`, so a nest of them costs O(n) in all. The naive
    // form, typing the branch by its class, joins the other branch's literal to that class
    // and gives `int`, or rejects a decimal there.
    fn kept(&self, e: &Expr, t: &Ty) -> Option<Ty> {
        let k = self.class_of_ty(t)?;
        if !self.classes[self.find(k)].generic {
            return None;
        }
        let e = exported(e);
        let (ls, rat, _) = literals_alone(e, None)?;
        let ints = ls
            .iter()
            .all(|l| l.bare && lit_carrier(&l.value) == Carrier::Int);
        if !ints || rat {
            return None;
        }
        folded(e, Carrier::Int).map(|v| Ty::lit(&v))
    }

    /// Whether the branch `b` of an `if` of literals joins the class `k`, as `what` at `span`
    /// requires: a literal as a lone literal does ([`Ck::joining`]), and an operation on
    /// literals alone by its class, which merges with `k` as the operation alone would.
    fn branch_joins(&mut self, k: usize, b: &Branch, what: &str, span: Span) -> bool {
        match b {
            Branch::Lit(l) => self.join(k, &self.joining(l), false),
            Branch::Op { class, .. } => self.merge(k, *class, what, span),
        }
    }

    /// At the top level, an operation on bare literals alone, as `3 + 4`, is typed as it is
    /// walked, `int` where its arrows take one, since nothing in it gives a carrier; but it is
    /// a literal too, and takes the carrier of what it meets (DESIGN.md sec:diagnostics, "A
    /// `/` of integer literals": "an operation on literals alone is an `int` only where
    /// nothing at all gives it a carrier"). So where the operator `op` at `span` has one
    /// operand `x` or `y` that is such an operation and the other of one numeric carrier other
    /// than `int`, each literal of the operation adopts that carrier and the operand takes its
    /// type: in `q = (1.0f64 + 2) / (3 + 4)`, `3 + 4` is an `f64`, in `(1 + 2) < 0.5f64`,
    /// `1 + 2` is, and in `y = 1.0f64 + 7 / 2`, `7 / 2` is. The operators are the arithmetic
    /// ones but `^`, whose exponent need not have the carrier of its base, and the
    /// comparisons. An operation of `+`, `-`, `*`, `/` or `^` on two such operands, and a `-`
    /// of one, is recorded as one ([`Ck::lit_ops`]). A `/` of two integer literals, which no
    /// arrow of `/` takes, and a negative exponent of the `int` power are rejected as they are
    /// walked; the errors are dropped where the operation meets a carrier
    /// ([`Ck::lit_wrote`], [`Ck::drop_met`]).
    ///
    /// An operation is left as it was where its value at the carrier is no value of it
    /// ([`folded`]), as `1r + 1 / 0`, whose `/` always fails: its rejection stands. A `rat`
    /// does not reach a `^`, which has no arrow at `rat`.
    ///
    /// Complexity tradeoff: the naive test walks each operand to see whether it holds literals
    /// alone, which costs the depth of the operation at each operator, the square of the
    /// depth over a nest of them. Each operation is recorded as it ends, from its two operands'
    /// entries, so the test is one lookup, and the literals of an operation are walked once,
    /// when it takes its carrier: after that the operand is of that carrier, and the operation
    /// around it holds a value of a carrier, not literals alone. The walk that folds an
    /// operation holding a `/` or a `^` costs its size again, once.
    fn lit_op_meets(&mut self, op: &str, x: &mut Arg<'a>, y: &mut Arg<'a>, span: Span) {
        let op_of = |a: &Arg| a.expr.is_some_and(|e| self.lit_ops.contains(&e.span));
        let bare = |a: &Arg| a.lit.as_ref().is_some_and(|l| l.bare);
        let (ox, oy) = (op_of(x), op_of(y));
        if (ox || bare(x)) && (oy || bare(y)) {
            if matches!(op, "+" | "-" | "*" | "/" | "^") {
                self.lit_ops.insert(span);
                // Its value has no type until it meets a carrier where it holds a `/` or a
                // decimal ([`Ck::lit_open`]): one lookup per operand.
                let open = |a: &Arg| {
                    a.expr.is_some_and(|e| self.lit_open.contains(&e.span))
                        || (a.lit.as_ref())
                            .is_some_and(|l| l.bare && lit_carrier(&l.value) == Carrier::F64)
                };
                if op == "/" || open(x) || open(y) {
                    self.lit_open.insert(span);
                    for e in [x.expr, y.expr].into_iter().flatten() {
                        self.lit_open_within(e);
                    }
                }
            }
            return;
        }
        if op == "^" {
            return;
        }
        let (side, other) = match (ox, oy) {
            (true, false) => (x, &*y),
            (false, true) => (y, &*x),
            _ => return,
        };
        let Some(c) = other.ty.numeric_carrier().filter(|&c| c != Carrier::Int) else {
            return;
        };
        let Some(e) = side.expr else {
            return;
        };
        if self.lit_takes(e, c) {
            side.ty = Ty::carrier(c);
        }
    }

    /// Each operation in `e`, an operand of an operation on literals alone that has no type
    /// until it meets a carrier, recorded as having none too ([`Ck::lit_open`]): in
    /// `(1 + 2) / (3 + 4)`, `1 + 2` takes the carrier of what it meets, the `/`, and is not
    /// an `int` there (DESIGN.md sec:diagnostics, "A `/` of integer literals").
    ///
    /// Complexity tradeoff: the naive way walks all of `e` at each operation around it, the
    /// square of the depth over a nest of them. An operation recorded here has all the
    /// operations in it recorded too, since each is recorded with its operands, so the walk
    /// stops at one: each operation is walked once until it takes a carrier
    /// ([`Ck::lit_takes`]), which removes all of it at once.
    fn lit_open_within(&mut self, e: &Expr) {
        let mut todo = vec![e];
        while let Some(e) = todo.pop() {
            if literal(e, None).is_some() || !self.lit_open.insert(e.span) {
                continue;
            }
            match &e.kind {
                ExprKind::Binary(_, a, b) => todo.extend([&**a, &**b]),
                ExprKind::Unary("-", a) => todo.push(a),
                _ => {}
            }
        }
    }

    /// Each literal of `e`, an operation on bare literals alone ([`Ck::lit_ops`]), adopting
    /// `c`, each of its operations of type `c` where a derivation names it ([`Ck::seen`],
    /// [`Ck::lit_open`]), and the errors its operations wrote as they were walked dropped
    /// ([`Ck::lit_wrote`]); `false`, with nothing changed, where `e` holds a `^` and `c` is
    /// `rat`, which no arrow of `^` takes, or where `e` holds a `/` or a `^` and its value at
    /// `c` is no value of `c` ([`folded`]), as `1 / 0` at `rat`: the rejection of the
    /// operation stands. It costs the size of `e`, twice where it holds a `/` or a `^`.
    fn lit_takes(&mut self, e: &Expr, c: Carrier) -> bool {
        let mut nodes = Vec::new();
        let (mut div, mut pow) = (false, false);
        let mut todo = vec![e];
        while let Some(e) = todo.pop() {
            nodes.push(e);
            if literal(e, None).is_some() {
                continue;
            }
            match &e.kind {
                ExprKind::Binary(op, a, b) => {
                    div |= *op == "/";
                    pow |= *op == "^";
                    todo.extend([&**b, &**a]);
                }
                ExprKind::Unary("-", a) => todo.push(a),
                _ => {}
            }
        }
        if (pow && c == Carrier::Rat) || ((div || pow) && folded(e, c).is_none()) {
            return false;
        }
        let live = !self.trying && self.replaying == 0;
        for e in nodes {
            if let Some(l) = literal(e, self.t.text) {
                self.adopt_to(&l, c);
                continue;
            }
            // Each operation in it is of the carrier now, which a derivation names, and not
            // the type the walk found before it met one.
            self.lit_open.remove(&e.span);
            if let Some((kept @ Some(_), _)) = self.seen.get_mut(&e.span) {
                *kept = Some(Ty::carrier(c));
            }
            if live && let Some(r) = self.lit_written.remove(&e.span) {
                self.lit_dropped.insert(r.start, r.end);
            }
        }
        true
    }

    /// At the top level, each argument of `args` that is an operation on bare literals alone
    /// ([`Ck::lit_ops`]), at a parameter that every arrow of `sig` declares of one numeric
    /// carrier other than `int`, takes that carrier, as a literal does at a declared type
    /// (DESIGN.md sec:domains: a use fixes a literal's carrier "at a declared type, that
    /// type's", and "an operation on literals alone ... is a literal too, and takes the
    /// carrier of what it meets"): with `f(x: f64)`, in `f(x: 1 / 2)` the `/` is an `f64`
    /// and `x` is `0.5`, and the rejection the `/` wrote as it was walked is dropped. An
    /// operator's arrows differ in their carriers, so this leaves its operands to
    /// [`Ck::lit_op_meets`]; a generic parameter gives no carrier, so `inc(x: 1 / 2)` is
    /// rejected still. Where the operation's value at the carrier is no value of it
    /// ([`Ck::lit_takes`]), its rejection stands.
    ///
    /// It costs one lookup per argument and one read of each arrow's parameter there, and
    /// [`Ck::lit_takes`] walks an operation once: after it the argument is of a carrier.
    fn lit_args_take(&mut self, sig: &Sig, args: &mut [Option<Arg<'a>>]) {
        for (i, a) in args.iter_mut().enumerate() {
            let Some(a) = a else {
                continue;
            };
            let Some(e) = a.expr.filter(|e| self.lit_ops.contains(&e.span)) else {
                continue;
            };
            let mut at = (sig.arrows.iter())
                .map(|arrow| arrow.params.get(i).and_then(|p| p.numeric_carrier()));
            let Some(Some(c)) = at.next() else {
                continue;
            };
            if c == Carrier::Int || !at.all(|d| d == Some(c)) {
                continue;
            }
            if self.lit_takes(e, c) {
                a.ty = Ty::carrier(c);
            }
        }
    }

    /// The errors after the first `from` that the operation at `span` wrote, recorded where it
    /// is an operation on literals alone at the top level ([`Ck::lit_written`]) and the check
    /// is not a repair's trial nor a run again of a function's body, whose errors are dropped
    /// with it.
    fn lit_wrote(&mut self, span: Span, from: usize) {
        let to = self.errors.len();
        if self.level == 0
            && to > from
            && !self.trying
            && self.replaying == 0
            && self.lit_ops.contains(&span)
        {
            self.lit_written.insert(span, from..to);
            self.lit_order.push(span);
        }
    }

    /// Drops the errors of the operations on literals alone that met a carrier
    /// ([`Ck::lit_op_meets`]) of the statement whose check wrote the errors after the first
    /// `before`, and forgets the errors its operations wrote: the statement has ended.
    ///
    /// Complexity tradeoff: the naive way removes each dropped range from the errors in turn,
    /// shifting the errors after it, the product of the ranges and the errors. The ranges of
    /// the statement are the last ones in the order of the errors, so they are split off
    /// the map, the errors after `before` split off once and the kept ones put back in one
    /// pass, `O(k log k + e)` for `k` ranges and `e` errors.
    fn drop_met(&mut self, before: usize) {
        while let Some(&s) = self.lit_order.last() {
            match self.lit_written.get(&s) {
                Some(r) if r.start < before => break,
                Some(_) => {
                    self.lit_written.remove(&s);
                }
                None => {}
            }
            self.lit_order.pop();
        }
        let dropped = self.lit_dropped.split_off(&before);
        if dropped.is_empty() {
            return;
        }
        let found = self.errors.split_off(before);
        let mut ranges = dropped.into_iter().peekable();
        for (i, e) in found.into_iter().enumerate() {
            let at = before + i;
            while ranges.next_if(|&(_, end)| end <= at).is_some() {}
            if !ranges.peek().is_some_and(|&(start, _)| start <= at) {
                self.errors.push(e);
            }
        }
    }

    /// At the top level, the components of two tuple displays `x` and `y` of one shape that
    /// `==` or `!=` compares, where one of a pair is an operation on bare literals alone
    /// ([`Ck::lit_ops`]) and the other is of one numeric carrier other than `int`: the
    /// operation takes that carrier, as it would where the pair were compared alone (step
    /// L1.26a: "two tuples compare component by component, each pair under this rule", and an
    /// operation on literals alone "takes the carrier of what it meets"). In
    /// `(1 + 2, 0) == (3.0f64, 0)`, `1 + 2` is an `f64`. The display's type is made again with
    /// the new components. A literal with no suffix gives no carrier.
    ///
    /// Complexity tradeoff: each pair is one lookup of each component's type, found as it was
    /// walked ([`Ck::seen`]), so the pairs cost the size of the displays, and an operation's
    /// literals are walked once ([`Ck::lit_takes`]); each display changed is made again once,
    /// bottom up, which costs its size, not the size times the depth that making it again at
    /// each changed component would.
    fn lit_pairs(&mut self, x: &mut Arg<'a>, y: &mut Arg<'a>) {
        let (Some(a), Some(b)) = (x.expr, y.expr) else {
            return;
        };
        if !matches!((&a.kind, &b.kind), (ExprKind::Tuple(_), ExprKind::Tuple(_))) {
            return;
        }
        let Some(pairs) = paired(a, b) else {
            return;
        };
        let mut new: HashMap<Span, Ty> = HashMap::new();
        for (p, q) in pairs {
            for (side, other) in [(p, q), (q, p)] {
                if !self.lit_ops.contains(&side.span)
                    || self.lit_ops.contains(&other.span)
                    || literal(other, None).is_some_and(|l| l.bare)
                {
                    continue;
                }
                let found = self.seen.get(&other.span).and_then(|(t, _)| t.as_ref());
                let Some(c) = found.and_then(Ty::numeric_carrier) else {
                    continue;
                };
                if c != Carrier::Int && self.lit_takes(side, c) {
                    new.insert(side.span, Ty::carrier(c));
                }
            }
        }
        if !new.is_empty() {
            x.ty = retyped(&x.ty, a, &new);
            y.ty = retyped(&y.ty, b, &new);
        }
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
        // An operand that is a literal without a suffix is generic: it takes the carrier of the
        // other operand, at run time where that is a type variable (step L1.26a). Under `==`
        // it follows as any literal.
        if !matches!(op, "==" | "!=") {
            for l in [&mut x.lit, &mut y.lit].into_iter().flatten() {
                l.generic = l.bare;
            }
            // Two generic operands, as in `1 + 2`, make a class of their own inside a
            // function: generic, it takes the carrier of what it meets, the first operand
            // taking it from a parameter of the class and the second following the first; it
            // takes int where it meets no carrier.
            if self.level > 0
                && let (Some(a), Some(b)) = (&x.lit, &y.lit)
                && a.bare
                && b.bare
            {
                let k = self.generic_class(a);
                x = Arg {
                    ty: Ty::var(format!("${k}").into()),
                    lit: None,
                    ..x
                };
            }
        }
        if self.level == 0
            && matches!(
                op,
                "+" | "-" | "*" | "/" | "^" | "<" | "<=" | ">" | ">=" | "==" | "!="
            )
        {
            self.lit_op_meets(op, &mut x, &mut y, span);
        }
        match op {
            "==" | "!=" => {
                if self.level == 0 {
                    self.lit_pairs(&mut x, &mut y);
                }
                // A call of literal values alone compared with a value of one carrier, `f64`
                // or `rat`, is read at that carrier, as at an arithmetic operator: `x == g(c)`
                // with `x: f64` and `g` of type `(bool) -> 1 | 2` compares two `f64`s
                // ([`read_call`]; L1.26a). One read of the call's listed values.
                for flip in [false, true] {
                    let (a, other) = match flip {
                        false => (&x, &y),
                        true => (&y, &x),
                    };
                    match read_call(a, &other.ty) {
                        Some(Ok((t, c))) => {
                            let e = a.expr.expect("a call read at a carrier");
                            self.put(Undo::Fit(e.span, Some(Fit::Read(c))));
                            match flip {
                                false => x.ty = t,
                                true => y.ty = t,
                            }
                        }
                        Some(Err((v, c))) => {
                            let args = [Some(x.clone()), Some(y.clone())];
                            let m = self.unread_call(&format!("`{op}`"), &args, a, &v, c, true);
                            self.error(span, m);
                            return Ty::carrier(Carrier::Bool);
                        }
                        None => {}
                    }
                }
                let from = self.errors.len();
                self.data(&x.ty, &format!("`{op}`"), span, x.at.unwrap_or(span));
                self.data(&y.ty, &format!("`{op}`"), span, y.at.unwrap_or(span));
                let op = if op == "==" { "==" } else { "!=" };
                self.comparing = Some(Comparison {
                    op,
                    ats: [x.at, y.at],
                    exprs: [x.expr, y.expr],
                    span,
                    from,
                });
                self.equal(&x, &y);
                self.comparing = None;
                for (l, v, left) in [(&x, &y, true), (&y, &x, false)] {
                    if let (Some(lit), None) = (&l.lit, &v.lit)
                        && lit.bare
                    {
                        self.eq_sides.insert(lit.site, (op, v.at, left));
                        if self.class_of_ty(&v.ty).is_none() && holds_no_number(&[&v.ty]) {
                            self.never_equal(lit, &v.ty);
                        }
                    }
                }
                Ty::carrier(Carrier::Bool)
            }
            "<" | "<=" | ">" | ">=" => self.compare(op, x, y, span),
            _ => {
                let from = self.errors.len();
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
                let zero = match op {
                    "/" | "div" | "mod" => self.zero_divisor(op, &x, &y, b),
                    _ => None,
                };
                // The dividend as the program writes it, for the repair.
                let dividend = match (&x.lit, x.expr.map(|e| &e.kind)) {
                    (Some(l), _) => l.written().to_string(),
                    (None, Some(ExprKind::Name(n))) => n.clone(),
                    _ => "…".to_string(),
                };
                let sig = op_sig(op);
                let r = self.apply(&format!("`{op}`"), &sig, vec![Some(x), Some(y)], true, span);
                if let Some(why) = zero
                    && r.0.atoms().contains(&Value::atom("divByZero"))
                {
                    self.divides_by_zero(op, why, &dividend, b, span);
                }
                self.lit_wrote(span, from);
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
        if let Some(id) = self.declared(callee)
            && let Some(t) = self.env.get(&id)
            && let Some(sig) = only_fn(t)
        {
            let from = self.errors.len();
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
        m.ty(Ty::atom_of(name, items, fields));
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

    fn word_end(&mut self, w: &str, mut x: Arg<'a>, span: Span) -> Ty {
        if w == "sum" {
            return self.sum(x, span);
        }
        // A decimal with no suffix as the operand of a cast at the top level, as in
        // `f64(0.1)`, is rejected, since a cast fixes no carrier for its operand (step L1.26b).
        // A fix that writes it with a carrier at which the cast always fails is not offered
        // (DESIGN.md sec:domains: "A cast `f64(9007199254740993r)` is never offered [...] since
        // the integer has no exact `f64`, so the cast gives `#inexact` for its one input"):
        // `f64(0.1)` lists `f64(0.1f64)` alone, since `0.1r` has no exact `f64`, and `f64(0.5)`
        // lists `0.5f64` and `0.5r`. The operand then takes the first carrier left, so the call
        // is typed as with it. Each carrier's value is cast once, as
        // [`Self::always_fails_word`] casts it, at the cost it names.
        if self.level == 0
            && let Some(l) =
                (x.lit.clone()).filter(|l| l.bare && lit_carrier(&l.value) == Carrier::F64)
            && let Some(p) = zedc_base::interp::prim(w)
        {
            let sig = word_sig(w);
            let cs: Vec<Carrier> = [Carrier::F64, Carrier::Rat]
                .into_iter()
                .filter(|&c| {
                    lit_value(&l, c).is_some_and(|v| {
                        sig.arrows.iter().any(|a| a.params[0].contains(&v))
                            && !matches!(run(p, &v), Some(Value::Atom(_)))
                    })
                })
                .collect();
            if let [c, ..] = cs[..] {
                let notes = self.derive(&[l.site]);
                let m = unfixed(&l, &cs, None);
                self.reject(Some(Row::UnfixedDecimal), l.site, m, notes);
                self.adopt_to(&l, c);
                x.lit = None;
                x.ty = Ty::carrier(c);
            }
        }
        if w == "String" {
            self.data(&x.ty, "`String`", span, x.at.unwrap_or(span));
            // `String` takes every carrier, so it gives a literal none: an integer literal is
            // `int`, and a decimal one, as in `String(0.5)`, is rejected (step L1.26b).
            if let Some(l) = x.lit.as_ref().filter(|l| l.bare)
                && lit_carrier(&l.value) != Carrier::Int
            {
                let notes = self.derive(&[l.site]);
                let m = unfixed(l, &[Carrier::F64, Carrier::Rat], None);
                self.reject(Some(Row::UnfixedDecimal), l.site, m, notes);
            }
        }
        let sig = word_sig(w);
        let values = self.operand_values(&x);
        let at = x.at.unwrap_or(span);
        let r = self
            .apply(&format!("`{w}`"), &sig, vec![Some(x)], true, span)
            .0;
        if let Some(values) = values {
            self.always_fails_word(w, values, &r, at, span);
        }
        r
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
        m.k(Frame::Index1 {
            k,
            of: of.span,
            span,
        });
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
                "repair: write the lambda with the parameters of `{shown}`{DECLARE}, its first {} \
                 taken by position",
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
        // Each parameter of `e` passed by name, by its name, the first where a name repeats: a
        // search of `e`'s parameters for each of the lambda's cost `O(n^2)` for `n` of them.
        let named: HashMap<&str, usize> = (e.params.iter().enumerate().rev())
            .filter(|(_, q)| !q.positional)
            .map(|(j, q)| (&*q.name, j))
            .collect();
        for (i, p) in params.iter().enumerate() {
            if i < pos.len() {
                order[pos[i]] = Some(i);
                continue;
            }
            match named.get(p.name.as_str()).copied() {
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
                            format!(
                                "repair: write the lambda with the parameters of `{shown}`{DECLARE}"
                            )
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
                                    "repair: declare `{name}` as {tt}{DECLARE}, or with no type, so that it \
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

/// The branches `e`'s value comes from when `e` is an `if` whose every branch, at any depth
/// of `if`, is a numeric literal or an operation on integer literals alone that keeps its
/// value there ([`Ck::kept_ops`], whose entries `kept` gives), as `if c { 2 } else { 1 }`,
/// `if a { 1 } else if b { 2 } else { -3 }` or `if c { 2 + 1 } else { 1 }`; `None` when `e` is
/// no `if` or a branch is anything else. Each is fixed where the value is used as it would be
/// alone (L1.26a: "each keeps its own value and is fixed where the result is used").
// Complexity tradeoff: one walk over the `if`s of `e` with its own stack, O(n) in its
// branches, which a nest of `if`s as deep as the text cannot overflow; it stops at the first
// branch that is neither. An operation is walked twice more, to read its literals and to
// fold it, O(its size); the `if` it is a branch of is one argument, so this is once. The
// naive form, the union type of the branches tested against the parameter, needs no walk but
// cannot fix a literal's carrier, since a type `2 | 1` holds the values, not the literals
// that wrote them. Tests: `l01_26a_generic_literals::lit_branches` and
// `l01_26a_generic_literals::lit_branch_ops`.
fn branch_lits<'e>(
    e: &'e Expr,
    src: Option<&str>,
    kept: &HashMap<Span, usize>,
) -> Option<Rc<[Branch<'e>]>> {
    if !matches!(exported(e).kind, ExprKind::If { .. }) {
        return None;
    }
    let mut out = Vec::new();
    let mut todo = vec![e];
    while let Some(x) = todo.pop() {
        let x = exported(x);
        if let Some(l) = literal(x, src) {
            out.push(Branch::Lit(l));
            continue;
        }
        if let Some(&class) = kept.get(&x.span) {
            out.push(Branch::Op {
                e: x,
                value: folded(x, Carrier::Int)?,
                lits: literals_alone(x, src)?.0.into(),
                class,
            });
            continue;
        }
        let ExprKind::If {
            then, otherwise, ..
        } = &x.kind
        else {
            return None;
        };
        todo.extend([&**otherwise, &**then]);
    }
    Some(out.into())
}

/// The argument `a` read at the parameter `p` where `a` is a call whose type lists numeric
/// literal values alone and `p` holds numbers of one carrier, `f64` or `rat`: the type of the
/// values read at that carrier, and the carrier. With `g(positional c: bool) = if c { 2 }
/// else { 1 }`, of type `(bool) -> 1 | 2`, `g(c)` at an `f64` parameter is `2.0 | 1.0`
/// (L1.26a: "each keeps its own value and is fixed where the result is used", and "`z: f64 =
/// g(c)` read both branches at `f64`"). An integer value is read at `f64` or `rat` where it is
/// exactly one, and a decimal one only at `f64`, which its value at run time already is: read
/// at `rat` it would be the `f64`'s value, not the decimal's. `None` where the call is not
/// read so, which leaves it to the check every argument has; `Some(Err((v, c)))` where every
/// value is a number but `v` is not read at `c`: an integer with no exact value at `c`, as a
/// lone integer literal there has none (sec:diagnostics: "an integer literal takes a
/// carrier only where that carrier holds it exactly"), or a decimal at `rat`. A name, `y`
/// after `y = g(c)`, is no call and is not read: its value is fixed where it is bound
/// ("bound to a name alone").
// Complexity tradeoff: O(v log v) for the `v` values the type lists, each cast once and the
// singletons joined in pairs (`Ty::union_all`); the listing itself costs the size of the type
// ([`KType::values_listed`]). The naive form, the type `1 | 2` tested against `f64`, rejects
// the call, since an `int` value is no `f64`. Joining the singletons one at a time instead
// copies the union so far at each, O(v²) element copies; `lit_branch_ops::scaling` does not
// catch that form (8.1 times for 8 times the size), since checking the `g` that gives the
// values costs far more per value (COMPLEXITY.md F164).
pub(super) fn read_call(a: &Arg, p: &Ty) -> Option<Result<(Ty, Carrier), (Value, Carrier)>> {
    // The cheap test first: every operator application with an argument of no literal asks
    // ([`Ck::fewest`]), and few such arguments are calls.
    if p.dynamic || !p.vars.is_empty() || lone_call(a).is_none() {
        return None;
    }
    let held = [Carrier::Int, Carrier::Rat, Carrier::F64]
        .into_iter()
        .filter(|c| !(&p.set & &c.ty()).is_empty());
    let c = match held.collect::<Vec<_>>()[..] {
        [c @ (Carrier::F64 | Carrier::Rat)] => c,
        _ => return None,
    };
    let vs = call_values(a)?;
    Some(read_at(&vs, c)?.map(|t| (t, c)).map_err(|v| (v, c)))
}

/// The call `a` is, where it is one and holds no literal ([`Arg::branches`], [`Arg::parts`]).
fn lone_call<'e>(a: &Arg<'e>) -> Option<&'e Expr> {
    let e = a
        .expr
        .filter(|_| a.lit.is_none() && a.branches.is_none() && a.parts.is_none())?;
    matches!(exported(e).kind, ExprKind::Call { .. }).then_some(e)
}

/// The values `a` may give where it is a call whose type lists values alone, as `g(c)` of
/// type `1 | 2`: the call [`read_call`] and [`Ck::apply_one`] may read at a carrier. `None`
/// where `a` is no call, is a literal or holds one ([`Arg::branches`], [`Arg::parts`]), or
/// its type is not a list of values.
fn call_values(a: &Arg) -> Option<Vec<Value>> {
    lone_call(a)?;
    let t = &a.ty;
    if !t.tuples.is_empty() || !t.fns.is_empty() || !t.vars.is_empty() || t.dynamic {
        return None;
    }
    t.set.values_listed().filter(|vs| !vs.is_empty())
}

/// The values `vs` a call gives read at the carrier `c`, `f64` or `rat`, as [`read_call`]
/// says: the type of the values read, `Err(v)` with the first value `v` not read at `c`, or
/// `None` where a value is no number or every value is of `c` already.
fn read_at(vs: &[Value], c: Carrier) -> Option<Result<Ty, Value>> {
    // Values of the carrier already, as `2.5` at `f64`, need no read.
    if vs.iter().all(|v| lit_carrier(v) == c) {
        return None;
    }
    let cast = match c {
        Carrier::F64 => Prim::CastF64,
        _ => Prim::CastRat,
    };
    let mut ts = Vec::with_capacity(vs.len());
    // The first value not read: an integer with no exact value at `c`, or a decimal at `rat`.
    let mut unread = None;
    for v in vs {
        let r = match v {
            _ if lit_carrier(v) == c => Some(v.clone()),
            Value::Int(_) | Value::Big(_) => {
                Some(run(cast, v)?).filter(|r| !matches!(r, Value::Atom(_)))
            }
            // At `rat`: a decimal a call gives is the `f64` it was read as.
            Value::Float(_) => None,
            _ => return None,
        };
        match r {
            Some(r) => ts.push(Ty::lit(&r)),
            None => unread = unread.or(Some(v)),
        }
    }
    Some(match unread {
        Some(v) => Err(v.clone()),
        None => Ok(Ty::union_all(&ts)),
    })
}

/// Whether the branch where `facts` hold is unreachable: a test narrows a name to a type with
/// no value, as `x is Never`, or `x is bool` for an `int`. O(1) per fact. A branch no value
/// reaches by the tests on ints, as `x > 0 && x < 0`, is found by [`Ck::no_state_reaches`].
fn unreachable(facts: &Facts) -> bool {
    // Complexity tradeoff: a narrowed type counts as empty only when it lists no value
    // (`Ty::lists_nothing`); one that only the kernel's search proves empty leaves its branch
    // reachable and its type in the join. A meet of tuple types empties at once (`Row::new`),
    // so `x is (bool, int)` for `x: (int, int)` is unreachable; what is left is a type empty
    // by recursion or by a meet in an atom's payload or a family, none of which a type an L1
    // program writes holds. Why: the search costs up to the size of the type per test.
    // Trigger: an `is` against such a type, from the layers that write them. Tests:
    // `l01_26_type_resolution::never::a_test_against_never_is_accepted`,
    // `a_branch_no_value_reaches_adds_nothing_to_the_result`. COMPLEXITY.md C34. The complete
    // solution asks `Ty::is_empty` with the kernel's memoized search.
    facts.iter().any(|(_, t, _)| t.lists_nothing())
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
    /// Checks that `e`, of type `t`, an expression whose value is the result of `main`
    /// ([`Ck::main_tails`]), gives an `int` in `0..=255`, the range of an exit status: by the
    /// values its type lists, or by the ints its text and the tests around it show
    /// ([`Ck::ints_here`]). Its other values are checked by [`Ck::exit_status`].
    pub(super) fn status_in_range(&mut self, e: &'a Expr, t: &Ty) {
        let ints = &t.without_loose().set & &KType::int();
        if ints.is_empty() {
            return;
        }
        let in_byte = |v: &Value| {
            v.surface_cmp(&Value::Int(0))
                .is_some_and(|o| o != std::cmp::Ordering::Less)
                && v.surface_cmp(&Value::Int(255))
                    .is_some_and(|o| o != std::cmp::Ordering::Greater)
        };
        if ints.ints_listed().is_some_and(|vs| vs.iter().all(in_byte)) {
            return;
        }
        let (got, narrowed) = self.ints_here(e);
        if got.is_subset(&IntervalSet::of(0, 255)) {
            return;
        }
        let code = self
            .t
            .text
            .map_or("this value", |s| &s[e.span.start..e.span.end]);
        // Listed values none of which is in the range, as a literal `256`: the value is known
        // to be outside, and the repair is another value.
        if ints.ints_listed().is_some_and(|vs| !vs.iter().any(in_byte)) {
            let message = format!(
                "`main` gives `{code}`, which is {}, and the result of `main` is the program's \
                 exit status, a number from 0 to 255",
                self.show(&Ty::set(ints))
            );
            let menu = [
                "repair: give a status from 0 to 255, as `0` for success or `1` for a \
                         failure"
                    .to_string(),
            ];
            self.error_offering(e.span, message, menu);
            return;
        }
        let shown = match narrowed {
            true => format!("int{got}"),
            false => self.show(&Ty::set(ints)),
        };
        let message = format!(
            "`main` gives `{code}`, which is {shown}, and the result of `main` is the program's \
             exit status, a number from 0 to 255: this zedc does not show that `{code}` is in \
             that range"
        );
        // A name or a literal is written as it is; anything else in parentheses, and bound to
        // a name before a test that reads it more than once. The clamp is written as an `if`
        // chain, since this zedc does not compile `.clamp` yet (DESIGN.md sec:ports offers
        // `code.clamp(0, 255)`).
        let simple = code.chars().all(|c| c.is_alphanumeric() || c == '_');
        let (operand, bind, name) = match simple {
            true => (code.to_string(), String::new(), code),
            false => (format!("({code})"), format!("code = {code}; "), "code"),
        };
        let menu = [
            format!(
                "repair: clamp it into the range, as `{bind}if {name} < 0 {{ 0 }} else if {name} \
                 > 255 {{ 255 }} else {{ {name} }}`"
            ),
            format!("repair: take it modulo 256, as `{operand} mod 256`"),
            format!(
                "repair: give a fixed status outside the range, as `{bind}if {name} >= 0 && \
                 {name} <= 255 {{ {name} }} else {{ 1 }}`"
            ),
        ];
        self.error_offering(e.span, message, menu);
    }

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

    /// Whether no value reaches node `n`, an arm of a condition checked at node `here`, by the
    /// tests on the ints of the names around it, as `x > 0 && x < 0` with `x: int`, though the
    /// type of each name there lists values. Where no value reaches `here` either, as in an
    /// arm already unreachable, it is not: there the arms are checked as usual. A condition
    /// with no test the scopes read, as an `is` test, makes no node of its own.
    fn no_state_reaches(&mut self, here: usize, n: usize) -> bool {
        if n == here {
            return false;
        }
        // Complexity tradeoff: an arm whose type adds something to the other arm's is asked
        // whether some state of its parent's scope reaches its test ([`Scope::reaches`]): one
        // copy of the parent's scope narrowed by the test, stopping at the first case some state
        // reaches, with no join of the cases and no scope stored for the arm. An arm whose type
        // adds nothing is not asked, since its answer changes no result: so `else { 0 }` under a
        // nest of tests on hubs asks nothing. What is given up: when each arm's type lies within
        // the other's, a scope no value reaches by either arm (which only a scope wider than its
        // states gives) keeps the arms' type and is not `Never`. Why: the bottom is known only
        // by narrowing, and narrowing by a negated test on a hub, `!(ai >= n && ai >= m)`, touches
        // the stars at the hub. Trigger: a nest of tests on hubs whose `else` arms each add a
        // type of their own, as `else { #s1 }`, `else { #s2 }`, ...: `k` = 24 and 192 took 16.6
        // times the bytes for 8 times the size (2026-11-09, load 18; 0.97 s with the question
        // switched off), above the limit of 14.5 but far below the 64 of a square; follow-up
        // NARROW-negated-star, which also covers the read under such an arm that was already
        // 20.1 times before this change (`else { popCount(ai) }`, `k` = 12 and 96). Asking every
        // arm, without the subtype test, made
        // `l01_39a_bit_words::scaling::two_hubs_on_one_block_settle_in_time_linear_in_the_tests`
        // take 19.8 times the instructions. Test:
        // `l01_26_type_resolution::scaling::a_chain_of_tests_is_linear_in_its_length`.
        // COMPLEXITY.md C34.
        self.settle(vec![Item::Scope(here)]);
        if self.arms.scopes[here].as_ref().is_some_and(|s| s.bottom) {
            return false;
        }
        // The arm's node is an assumption, or the join of the nodes of the ways a condition
        // with `||` holds, or with `&&` fails, which share nodes: each is visited once.
        let mut seen = HashSet::new();
        let mut work = vec![n];
        while let Some(k) = work.pop() {
            if !seen.insert(k) {
                continue;
            }
            if let Some(s) = &self.arms.scopes[k] {
                if !s.bottom {
                    return false;
                }
                continue;
            }
            match self.arms.nodes[k] {
                Node::Root => return false,
                Node::Join(a, b) => work.extend([a, b]),
                Node::Assume { outcome, .. } => {
                    let wanted = self.waits(Item::Scope(k));
                    self.settle(wanted);
                    let (p, t) = self.assumed(k);
                    if p.reaches(&t.term, outcome, &Premises::new()) {
                        return false;
                    }
                }
            }
        }
        true
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
    /// Complexity tradeoff: naive version, every input of the summary read at each binding
    /// (subset check, term bounds and premises), O(k) a read and Θ(d²) for the chain (2,275
    /// term bounds at d = 64, 132,867 at d = 512). Used: the persistent tree of the last read,
    /// updated at the inputs that differ, O(m log k) for m differences (323 and 2,563 at the
    /// same sizes; COMPLEXITY.md row PA-let-narrow-many). Tradeoffs: memory, one read (a copy
    /// in O(1) of the scope's names and a tree of O(k) nodes, shared with the reads it was
    /// made from) kept per binder until the walk ends; when the differences reach the inputs
    /// the read is made afresh, which costs what the naive read did.
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
    /// Complexity tradeoff: naive version, the summary of a binder made afresh at each test
    /// that reads it, through the summaries of all the binders it reads, O(d) a test and
    /// O(d²) for a block of d tested bindings (measured with the memo cleared before each
    /// test: 0.23 to 19.4 billion instructions at d = 64 to 1024). Used: one summary per
    /// binder, kept in `Arms::summaries` for the walk, O(size of its value) once, so the block
    /// is O(d) (0.16 to 2.54 billion instructions; COMPLEXITY.md row PA-let-check). Tradeoffs:
    /// memory, one summary per binder until the walk ends; a summary is made where the binder
    /// is first read and keeps the input types of that place ([`Ck::narrowed_at`]), which is
    /// sound because a binder is read only within the narrowing it was bound in.
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
                    Node::Assume { outcome, .. } => {
                        let (p, t) = self.assumed(n);
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
                        // the leaf and satellites of them, names each of whose conjuncts
                        // relates it to one other name (`Conjuncts::star`), such as `n >= m`
                        // for the hubs of `ai >= n && ai >= m`; such a star is projected with
                        // those conjuncts (`Conjuncts::core`). So `ai >= n && ai >= m` and
                        // `ai >= n + m` under `k` tests on `n` and `k` on `m` cost `O(k)`: 0.15,
                        // 0.28 and 0.52 s at `k` = 96, 192 and 384, and 0.11, 0.18, 0.33 and
                        // 1.51 s at `k` = 12, 24, 48 and 192 (2026-11-07, load 18); with
                        // `n >= m` above them, 0.05, 0.11, 0.22 and 0.43 s at `k` = 24 to 192,
                        // and 0.08, 0.17, 0.40 and 0.81 s at `k` = 12 to 96 for the sum
                        // (2026-11-07, load 23), where 0.09, 0.31, 1.16 and 4.91 s were `k²`
                        // before (wt/narrow-hub-rest at 68a03534). What is given up is time,
                        // not an answer: a scope that is not lazy projects each star of two
                        // hubs or more again when a conjunct among its hubs comes or goes, `k`
                        // stars a test there, about `k²` over `k` such tests; a conjunct at a
                        // hub that mentions a name no star's leaf there has as a hub, and that
                        // is no satellite of them, keeps every leaf there in the forest, `k`
                        // blocks a test on the hub, as before; and a hub that comes to have
                        // such a leaf counts the names its other conjuncts mention. Why: the
                        // leaf of related hubs lies on a cycle of the relation, so its product
                        // is the projection of the star with the conjuncts among its hubs, not
                        // a cut at a box's corner. Trigger: many tests among two hubs that many
                        // stars share, in a scope that is not lazy; or a hub related to a name
                        // that is not a hub of its leaves nor a satellite of them.
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

    /// The scope node `n`, an `Assume` whose items are computed ([`Ck::waits`]), narrows by its
    /// test, and the test.
    fn assumed(&mut self, n: usize) -> (Scope, Rc<Translated>) {
        let Node::Assume { parent, test, .. } = self.arms.nodes[n] else {
            unreachable!("an assumption")
        };
        let t = self.term(test);
        let p = self.scope_or_root(parent);
        // A bound name the scope has no product of is its value, and any other name any value
        // of its type where the test is checked. A scope no state reaches is told of none: it
        // stays unreachable.
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
        (p, t)
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
                                self.show(&p.ty())
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
        let ok = self.errors.len() == saved.errors;
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
        // Levels nest: the one that ends is the innermost, so that `self.gens[level]` below
        // expires every entry of [`Self::clean`] that may hold a class this names.
        debug_assert_eq!(
            level, self.level,
            "the level that ends is the innermost one"
        );
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
        // Naive version, the one used for these classes: replaced at every depth, O(size of
        // `sig`) per level; read lazily, replaced once, O(size of `sig`) in all (inferred).
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
            let name = fresh_name(Names::Variables, &mut n, |name| facts.names.contains(name));
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
        // The rows [`Self::clean`] found at this level may hold its classes, which it named.
        self.ends += 1;
        if self.gens.len() <= level {
            self.gens.resize(level + 1, 0);
        }
        self.gens[level] = self.ends;
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
    // Complexity tradeoff (COMPLEXITY.md row F119): the naive version passes over the links
    // until no join changes a class, O(n²) for a chain of n links where each pass moves a
    // carrier one link (inferred). Used: the roots sorted and deduplicated once, then one pass
    // last to first and one first to last, O(n log n). Precondition: links run from older to
    // newer classes, which holds since a test's class is made after the class it tests.
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
        let from = self.errors.len();
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
        let on = self.bound(on, binds);
        self.replaying += 1;
        self.need_args = match &n.kind {
            NeedKind::Call { positional, .. } => {
                Some(positional.iter().map(Ty::holds_vars).collect())
            }
            NeedKind::Index(t) => Some(vec![t.holds_vars()]),
            _ => None,
        };
        let start = self.refused.len();
        let out = match &n.kind {
            NeedKind::Component { i, key } => {
                self.at_index(&on, *i, Arg::of(key.clone()), None, span, false)
            }
            NeedKind::Index(k) => {
                let k = Arg::of(self.bound(k, binds));
                self.at_key(&on, k, None, span, false)
            }
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
                        .map(|t| ArgSrc::Got(Box::new(Arg::of(self.bound(t, binds)))))
                        .collect(),
                    named: named
                        .iter()
                        .map(|(m, t)| {
                            (
                                m.to_string(),
                                ArgSrc::Got(Box::new(Arg::of(self.bound(t, binds)))),
                            )
                        })
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
                let other = self.bound(other, binds);
                let (x, y) = if *first { (&on, &other) } else { (&other, &on) };
                self.min_max_tuples(what, &word_sig(word), x, y, [None, None], span)
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
            let from = self.errors.len();
            let on = self.bound(&n.on, binds);
            let shape = self.bound(&on, &mut Binds::new());
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
                    let errors = self.errors.len();
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
                        self.errors.truncate(errors);
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
                    binds.or_insert_with(v.clone(), Ty::empty);
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
            let ok = self.piece_into(&piece, ty, what, span);
            if !ok {
                let p = self.show(&piece.ty());
                let why = on.of_piece(&piece).refused(ty);
                // After `is` a type stands as a union operand: a function type is parenthesized.
                let is_ty = self.text_in_union(ty);
                let ty = self.text(ty);
                let menu = [
                    format!("repair: pass {what} a value of {ty}"),
                    format!(
                        "repair: test the value with `is` first, as `if v is {is_ty} {{ … }}`{DECLARE}, \
                         or handle the values that are not {ty} with `else` or `match`"
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

    /// Whether a value of the one piece `piece` may be passed, by `what` at `span`, at a
    /// parameter of the closed type `ty`: a class is restricted to the carriers of `ty`, and a
    /// tuple whose components hold classes, as `(1, 2)` of literals without a suffix, is
    /// passed component by component where `ty` is one tuple shape of its length.
    fn piece_into(&mut self, piece: &Piece, ty: &Ty, what: &str, span: Span) -> bool {
        match self.class_of(piece) {
            _ if *piece == Piece::Dyn => ty.dynamic,
            _ if matches!(piece, Piece::Var(_)) && self.class_of(piece).is_none() => true,
            Some(k) => {
                let ok = self.restrict(k, mask_of(ty), what, span);
                let kind = NeedKind::Into {
                    what: what.into(),
                    ty: ty.clone(),
                };
                self.need(k, kind, false, span);
                ok
            }
            None => match piece {
                Piece::Fn(s) if !s.needs.is_empty() => {
                    self.fit_needs(s, ty, &mut Binds::new(), what, span)
                }
                Piece::Tuple(r) if r.open() => match &ty.pieces()[..] {
                    [Piece::Tuple(q)] if q.len() == r.len() => r
                        .iter()
                        .zip(q.iter())
                        .all(|(c, t)| c.pieces().iter().all(|p| self.piece_into(p, t, what, span))),
                    _ => self.sub(&piece.ty(), ty, &mut Binds::new()),
                },
                _ => self.sub(&piece.ty(), ty, &mut Binds::new()),
            },
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
        let from = self.errors.len();
        let mut ok = true;
        for a in &q.arrows {
            let args = a.params.iter().map(|t| Some(Arg::of(t.clone()))).collect();
            let (r, _) = self.apply(what, s, args, false, span);
            ok &= self.subtype(&r, &a.result);
        }
        ok || self.errors.len() > from
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
            // The value's type is written, and the part, when that is not all of it, as for
            // `(int, (..))`, whose part `(..)` is not the type of the value.
            let notes = data_repairs(span);
            let value = self.shown(t).to_string();
            let part = Ty::set(w).to_string();
            let holds = match value == part {
                true => String::new(),
                false => format!(" holds `{part}`, which"),
            };
            self.error_with(
                span,
                format!(
                    "{what} takes data, and this value, of `{value}`, may hold a function: data \
                     is a value that holds no function at any depth, and `{value}`{holds} holds \
                     every value of its shape, functions too"
                ),
                notes,
            );
        }
        // A class, at any depth, needs data of each of its values. A row that holds no class
        // or unknown is not entered; nor is one whose classes were checked as data when it
        // was made, since a class keeps a data need once it has one and a second is nothing.
        // Of such a row only its unknown is reported, once, as each would be at this span.
        // A row shared by many paths is visited once. Nor is a row or shape that an earlier
        // check entered ([`Self::data_checked`]) entered again: of the rows `p(s, v) = (s, (s,
        // v))` called `n` times nests, the `k`th call's need meets the `k` rows of `s`, which
        // the call before entered, so the calls cost `O(n)` in all and not `O(n^2)`.
        let mut rows = HashSet::new();
        // A payload shape that holds no class or unknown is not entered either, and a shape is
        // shared, so one met again by another path is not entered again.
        let mut shapes = HashSet::new();
        // The rows and shapes entered that hold no unknown, for `data_checked` once each class
        // they hold has its need.
        let mut entered = Vec::new();
        let mut stack = vec![t];
        while let Some(t) = stack.pop() {
            for r in (t.tuples.iter()).filter(|r| r.open() && rows.insert(r.node())) {
                match r.data() {
                    true if r.dynamic() => self.any(what, span),
                    true => {}
                    false if self.data_checked.contains(&r.node()) => {}
                    false => {
                        if !r.dynamic() {
                            entered.push(r.node());
                        }
                        stack.extend(r.iter());
                    }
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
            for s in open.filter(|s| shapes.insert(s.node())) {
                if self.data_checked.contains(&s.node()) {
                    continue;
                }
                if !s.dynamic() {
                    entered.push(s.node());
                }
                stack.extend(&s.items);
                stack.extend(s.fields.values());
            }
        }
        for n in entered {
            if self.data_checked.insert(n) && self.trying {
                self.log.push(Undo::DataChecked(n, false));
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
        let (a, b) = (x.ty.without_loose(), y.ty.without_loose());
        // An operand with no value: nothing is compared, and the comparison gives no value, but
        // each value of the other operand is still checked as `<` takes it.
        match (a.is_empty(), b.is_empty()) {
            (true, _) => self.compared_alone(&what, &b, true, span),
            (_, true) => self.compared_alone(&what, &a, false, span),
            _ => {
                self.components(&what, &a, &b, span);
                return out.union(&Ty::carrier(Carrier::Bool));
            }
        }
        out
    }

    /// Checks each value of `t`, an operand of the ordering `what` whose other operand has no
    /// value, the first operand where `none_first` does not hold: each number, string or bool
    /// at the top or in a component of a tuple at any depth against the arrows of `<`, beside
    /// `Never`, so that a function among them is rejected. Atoms pass. A row shared by many
    /// paths is visited once, so the check is linear in the rows of `t`.
    fn compared_alone(&mut self, what: &str, t: &Ty, none_first: bool, span: Span) {
        let sig = op_sig("<");
        // Keyed by the row's address (`Row::addr`): every row met is borrowed from `t`, which
        // stays borrowed for the whole walk, so no key names a freed row, and the set is only
        // read by `insert`, never iterated; the order of the checks is the stack's.
        let mut rows = HashSet::new();
        let mut stack = vec![t];
        while let Some(t) = stack.pop() {
            for r in (t.tuples.iter()).filter(|r| rows.insert(r.addr())) {
                stack.extend(r.iter());
            }
            let rest = Ty {
                tuples: Vec::new(),
                ..t.without_atoms()
            };
            if rest.is_empty() {
                continue;
            }
            let args = match none_first {
                true => [Ty::empty(), rest],
                false => [rest, Ty::empty()],
            };
            let args = args.into_iter().map(|t| Some(Arg::of(t))).collect();
            self.apply(what, &sig, args, true, span);
        }
    }

    /// Checks that each value of `a` compares with each of `b` (sec:order): two numbers of one
    /// carrier or two values of one other kind, the atoms as data, and two tuples component by
    /// component as far as the shorter goes, since a proper prefix comes first.
    ///
    /// Two tuples both reach position `i` exactly when each has more than `i` components, so
    /// the pairs of components met at `i` are every component `i` of `a`'s tuples against
    /// every one of `b`'s: the check reads the union of each side's, once, not each pair of
    /// tuples, which cost `n²` pairs for `n` tuples a side and `n³` for tuples of lengths 1 to
    /// `n`. A pair of component types met again, as through rows shared by many paths, is not
    /// read again: `n` levels that each hold the one below twice cost `n`, not `2^n`
    /// (CHK-components-pairs). The pairs are checked on a heap stack in the order a recursion
    /// would: a pair's own pieces, then its components position by position, then its rest.
    ///
    /// Complexity tradeoff: naive version, every pair of tuples read and each pair's
    /// components recursively, with no visited set: O(n²) pairs for `n` tuples a side (`x < x`
    /// over 800 shapes took 39.9 s), O(n³) for lengths 1 to `n`, `2^n` through shared rows.
    /// Used: one union of each side's components per position and a set of the pairs of
    /// component types read, O(n) in the types read. Tradeoffs: the set's memory, one pair of
    /// types per pair read; a failure is reported for the two unions met, as for `x < y` with
    /// `x: int | f64`, each piece that does not compare named once, not once per pair of
    /// tuples. COMPLEXITY.md row F140.
    fn components(&mut self, what: &str, a: &Ty, b: &Ty, span: Span) {
        enum Step {
            Pair(Ty, Ty),
            Rest(Ty, Ty),
        }
        let rest = |t: &Ty| Ty {
            tuples: Vec::new(),
            ..t.without_atoms()
        };
        let mut seen = HashSet::from([(a.clone(), b.clone())]);
        let mut todo = vec![Step::Pair(a.clone(), b.clone())];
        while let Some(step) = todo.pop() {
            let (a, b) = match step {
                Step::Rest(x, y) => {
                    self.apply(
                        what,
                        &op_sig("<"),
                        vec![Some(Arg::of(x)), Some(Arg::of(y))],
                        true,
                        span,
                    );
                    continue;
                }
                Step::Pair(a, b) => (a, b),
            };
            // Each piece refused is reported once, since a pair here may join many pairs of tuples.
            let (mut refused, mut said) = (Vec::new(), HashSet::new());
            for (s, t) in [(&a, &b), (&b, &a)] {
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
                        let p = self.text(&p.ty());
                        let message = format!("{what} does not compare {p} with {q}");
                        if said.insert(message.clone()) {
                            refused.push(message);
                        }
                    }
                }
            }
            if !refused.is_empty() {
                for message in refused {
                    self.error(span, message);
                }
                continue;
            }
            let (x, y) = (rest(&a), rest(&b));
            if !x.is_empty() && !y.is_empty() {
                todo.push(Step::Rest(x, y));
            }
            // The components at each position, of the tuples of each side long enough to have one.
            let mut at: Vec<[Vec<&Ty>; 2]> = Vec::new();
            for (side, t) in [&a, &b].into_iter().enumerate() {
                for row in &t.tuples {
                    if at.len() < row.len() {
                        at.resize_with(row.len(), Default::default);
                    }
                    for (i, c) in row.iter().enumerate() {
                        at[i][side].push(c);
                    }
                }
            }
            let met = at
                .into_iter()
                .filter(|[s, t]| !s.is_empty() && !t.is_empty());
            for [s, t] in met.rev() {
                let pair = (Ty::union_all(s), Ty::union_all(t));
                if seen.insert(pair.clone()) {
                    todo.push(Step::Pair(pair.0, pair.1));
                }
            }
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
    fn min_max_tuples(
        &mut self,
        what: &str,
        sig: &Sig,
        x: &Ty,
        y: &Ty,
        written: [Option<Rc<[Part]>>; 2],
        span: Span,
    ) -> Ty {
        // Called through a function value, a message names the word as well as the value.
        let who = match sig.word.as_deref() {
            Some(w) if what != format!("`{w}`") => format!("{what}, which is `{w}`,"),
            _ => what.to_string(),
        };
        let written = written.map(|w| w.map(Part::Tuple));
        let mut todo = vec![(x.clone(), y.clone(), written.clone())];
        // The decimal literals with no suffix written as components that meet only such
        // literals, with their messages.
        let mut unfixed_found: Vec<(Span, Msg)> = Vec::new();
        let mut seen = HashSet::new();
        // What the application gives, where one operand is a class and nothing else and the
        // other is closed: what the class's use gives ([`Ck::order_given`]).
        let mut given = None;
        while let Some((a, b, at)) = todo.pop() {
            let pair = (a, b);
            let outer = seen.is_empty();
            // A pair with literals written in it is checked each time, since each literal
            // adopts a carrier of its own.
            let lits = at.iter().any(Option::is_some);
            if !lits && seen.contains(&pair) {
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
                // A literal written as a component stays one, and adopts the carrier of the
                // component it is paired with, as it would as an argument alone: the `1` in
                // `min((0.5f64, 1), (1, 2))` is an `f64`.
                // Two literals with no suffix, one of them a decimal, give each other no
                // carrier: each such decimal is rejected, all of them in one message at the
                // end, and is read here as the `f64` of the first fix, so that nothing else
                // is rejected for it.
                let lits = at.each_ref().map(|w| match w {
                    Some(Part::Lit(l)) if l.bare => Some(l),
                    _ => None,
                });
                let mut fixed: [Option<Lit>; 2] = [None, None];
                if let [Some(l), Some(m)] = lits {
                    for (side, l) in [l, m].into_iter().enumerate() {
                        if lit_carrier(&l.value) == Carrier::F64 {
                            let cs: Vec<Carrier> = [Carrier::F64, Carrier::Rat]
                                .into_iter()
                                .filter(|&c| fits(l, c))
                                .collect();
                            unfixed_found.push((l.site, unfixed(l, &cs, None)));
                            fixed[side] = Some(Lit {
                                bare: false,
                                ..l.clone()
                            });
                        }
                    }
                }
                let arg = |t: &Ty, w: &Option<Part>, fixed: Option<Lit>| match w {
                    Some(Part::Lit(l)) => Arg {
                        lit: Some(fixed.unwrap_or_else(|| l.clone())),
                        ..Arg::of(t.clone())
                    },
                    _ => Arg::of(t.clone()),
                };
                let [f0, f1] = fixed;
                self.apply(
                    what,
                    sig,
                    vec![Some(arg(a, &at[0], f0)), Some(arg(b, &at[1], f1))],
                    true,
                    span,
                );
            } else if only(a, open[0]) || only(b, open[1]) {
                // Nothing more to check here.
            } else if a.is_empty() || b.is_empty() {
                // One operand has no value, so nothing is compared, but each value of the other
                // is still checked as the word takes it: its numbers by the arrows, beside
                // `Never`, and each tuple's components in turn, joined by length and position
                // as for two tuples below.
                let none_first = a.is_empty();
                let other = if none_first { b } else { a };
                let pair = |t: Ty| match none_first {
                    true => (Ty::empty(), t),
                    false => (t, Ty::empty()),
                };
                let numbers = Ty {
                    tuples: Vec::new(),
                    ..other.without_atoms()
                };
                if !numbers.is_empty() {
                    let (x, y) = pair(numbers);
                    self.apply(
                        what,
                        sig,
                        vec![Some(Arg::of(x)), Some(Arg::of(y))],
                        true,
                        span,
                    );
                }
                let mut by_len: BTreeMap<usize, Vec<&[Ty]>> = BTreeMap::new();
                for row in &other.tuples {
                    by_len.entry(row.len()).or_default().push(row);
                }
                for (n, rows) in by_len {
                    for i in 0..n {
                        let (s, t) = pair(Ty::union_all(rows.iter().map(|r| &r[i])));
                        todo.push((s, t, [None, None]));
                    }
                }
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
                    // The parts written at each position, where a side is one tuple display
                    // of this length.
                    let written = |side: usize, rows: &[&[Ty]]| match &at[side] {
                        Some(Part::Tuple(ps)) if rows.len() == 1 && ps.len() == n => {
                            Some(ps.clone())
                        }
                        _ => None,
                    };
                    let (ws, wt) = (written(0, &s), written(1, &t));
                    for i in 0..n {
                        let join = |rows: &[&[Ty]]| Ty::union_all(rows.iter().map(|r| &r[i]));
                        let part = |w: &Option<Rc<[Part]>>| match w.as_ref().map(|ps| &ps[i]) {
                            Some(Part::Other) | None => None,
                            Some(p) => Some(p.clone()),
                        };
                        todo.push((join(&s), join(&t), [part(&ws), part(&wt)]));
                    }
                }
            }
            seen.insert(pair);
        }
        unfixed_found.sort_by_key(|(s, _)| s.start);
        self.reject_unfixed(&format_args!("the arguments of {what}"), unfixed_found);
        // With an operand of no value the word gives none.
        if x.is_empty() || y.is_empty() {
            return Ty::empty();
        }
        // A literal written in a tuple display has the type of the value it adopted.
        let [x, y] = [(x, &written[0]), (y, &written[1])].map(|(t, w)| match w {
            Some(Part::Tuple(ps)) => with_adoptions(t, ps, &self.info.adopt),
            _ => t.clone(),
        });
        given.unwrap_or_else(|| one_shape_per_length(&x.union(&y)))
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
                self.min_max_tuples(what, sig, x, y, [None, None], span);
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
    /// `shr`, `int[0..<2^width]` for the operands read as `width` digits, `int[0..<width]`
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
                    what: format!("`{w}` takes `{name}` in int[0..<2^width]").into(),
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
                     `{name}: int[0..<2^32]`"
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
                    "int[0..<2^width]"
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
            dense: false,
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

    /// Whether the read `v[k]` at `span` is of a family whose keys are one integer interval,
    /// every key present, so that it misses with `#outOfBounds` (DESIGN.md sec:type_language,
    /// the `m[k]` row): `v` is such a family or a tuple, and is one at least once. A variable
    /// or an unknown value may be a family that misses with `#notFound`, so it reads as one.
    /// The verdict is recorded for the elaborator, which writes the read that answers
    /// `#outOfBounds`; a site checked twice keeps it only if both checks gave it.
    fn dense_read(&mut self, v: &Ty, span: Span) -> bool {
        let mut family = false;
        let mut dense = true;
        for p in v.pieces() {
            match p {
                Piece::Fn(sig) => {
                    family = true;
                    dense &= sig.data && sig.dense;
                }
                Piece::Tuple(_) => {}
                p if p.is_atoms() => {}
                _ => dense = false,
            }
        }
        let dense = family && dense;
        *self.info.dense.entry(span).or_insert(dense) &= dense;
        dense
    }

    /// `v[x]` with `x` no literal: an application of each function `v` may be, and a
    /// computed index of each tuple `v` may be. With `dense`, a family misses with
    /// `#outOfBounds` ([`Self::dense_read`]). With `of`, the span of `v` as written, a key
    /// outside a function's keys is rejected ([`Self::key_outside`]).
    fn at_key(&mut self, v: &Ty, x: Arg<'a>, of: Option<Span>, span: Span, dense: bool) -> Ty {
        let mut out = self.passing(v, "a call", span);
        for p in v.pieces() {
            match p {
                Piece::Tuple(cs) => {
                    let r = self.tuple_at(&cs, &x, span);
                    out = out.union(&r);
                }
                Piece::Fn(sig) => {
                    if let Some(r) = self.key_outside(&sig, &x, of, span, dense) {
                        out = out.union(&r);
                        continue;
                    }
                    let r = self
                        .apply("this function", &sig, vec![Some(x.clone())], false, span)
                        .0;
                    let r = if dense { out_of_bounds(r, &x.ty) } else { r };
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
    /// a family's entry. With `dense`, a family misses with `#outOfBounds`
    /// ([`Self::dense_read`]).
    fn at_index(
        &mut self,
        v: &Ty,
        i: Option<usize>,
        x: Arg<'a>,
        of: Option<Span>,
        span: Span,
        dense: bool,
    ) -> Ty {
        let mut out = self.passing(v, "an index", span);
        let shown = x.ty.to_string();
        for p in v.pieces() {
            match p {
                Piece::Fn(sig) if sig.data => {
                    if let Some(r) = self.key_outside(&sig, &x, of, span, dense) {
                        out = out.union(&r);
                        continue;
                    }
                    let r = self
                        .apply("this family", &sig, vec![Some(x.clone())], true, span)
                        .0;
                    let r = if dense { out_of_bounds(r, &x.ty) } else { r };
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
                     `positional` where it passes by position{DECLARE}",
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
            dense: s.dense,
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
                        "repair: pass a lambda of type `{e}`{DECLARE} that calls `{name}` with \
                         the arguments it takes"
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
                Some((_, Src::Other(e))) => (None, rat_forms(e, self.t.text)),
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
        self.rough = true;
        self.apply(what, sig, with, pass, span);
        let ok = self.errors.len() == saved.errors;
        self.rough = false;
        self.trying = false;
        self.undo(&saved);
        ok
    }

    /// Applies `sig` to `args`, a missing one filled by its default. When `pass` holds, as
    /// for an operator or a prelude word, an argument's atoms pass through, two arguments'
    /// merged into `#errs`. Gives the result and the arrows kept. An operator, a prelude word
    /// and a lookup in a family need every argument's value; a function's body reads what its
    /// result says ([`Demand`]).
    fn apply(
        &mut self,
        what: &str,
        sig: &Sig,
        args: Vec<Option<Arg<'a>>>,
        pass: bool,
        span: Span,
    ) -> (Ty, Vec<usize>) {
        let demand = match pass || sig.data || sig.word.is_some() {
            true => Demand::All,
            false => Demand::Body,
        };
        self.apply_demanding(what, sig, args, pass, demand, span)
    }

    /// [`Self::apply`], the arguments the call needs the values of given by `demand`.
    fn apply_demanding(
        &mut self,
        what: &str,
        sig: &Sig,
        mut args: Vec<Option<Arg<'a>>>,
        pass: bool,
        demand: Demand,
        span: Span,
    ) -> (Ty, Vec<usize>) {
        // An argument with no value that the call does not need: the call still gives what
        // its arrow gives there. Read before the atoms that pass by are taken out, since an
        // argument left with no value by them is one whose every value passes by.
        //
        // Complexity tradeoff: a call of a function whose body reads an argument of no value
        // on every path still gets its arrow's result, not `Never`: `g(positional x: int) =
        // x + 1` with `g(n)`, `n: Never`, is `int` (sound, less precise). Naive (complete)
        // version: a demand analysis of each body, which parameters it reads on every path,
        // one pass over the body per function and arrow and a fixpoint through recursive
        // calls (not built; cost inferred, at least linear in all bodies per arrow). Used:
        // only an operator, a prelude word, a family lookup (`Demand::All`) and the first
        // operand of `&&` and `||` (`Demand::First`) make the call `Never`; one `Vec<bool>`
        // of the arguments per call, O(arguments). Trigger: a declared or bounded parameter
        // read on every path. Test:
        // `l01_26_type_resolution::never::a_call_with_an_argument_of_no_value_has_its_substituted_result`.
        // COMPLEXITY.md row C36.
        if self.level == 0 {
            self.lit_args_take(sig, &mut args);
        }
        let unneeded: Vec<bool> = (args.iter().enumerate())
            .map(|(i, a)| {
                a.as_ref()
                    .is_some_and(|a| a.lit.is_none() && a.ty.is_empty() && !demand.needs(i))
            })
            .collect();
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
            let written = [x.parts.clone(), y.parts.clone()];
            let t = self.min_max_tuples(what, sig, &x.ty, &y.ty, written.clone(), span);
            return (out.union(&t), Vec::new());
        }
        let defer = std::mem::take(&mut self.defer);
        let passing = self.need_passed.len();
        let refusals = self.lit_refused.len();
        let made = self.top_parts.len();
        let r = match (sig.arrows.len(), self.first_taking(sig, &args, pass)) {
            (1, _) => self.apply_one(what, sig, 0, &args, &unneeded, defer, span),
            (_, Some(k)) => self.apply_one(what, sig, k, &args, &unneeded, defer, span),
            _ => {
                let r = self.apply_many(what, sig, &mut args, &unneeded, span);
                self.applied = None;
                r
            }
        };
        // The literals of tuple arguments outside every function take the carriers the
        // application gave their classes, and the result names those types.
        let r = match self.top_parts.len() > made {
            true => {
                self.resolve_top_parts(made);
                r.map(|(t, kept)| (self.solved(&t), kept))
            }
            false => r,
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
    /// (`x / 2` with `x: int`); in the row of a literal at a carrier it cannot take where the
    /// operands have no common carrier (`q * 2.0` with `q: int`), with the application's
    /// derivation and the casts of the other operands the checker accepts, `f64(q)`, where the
    /// message holds the literal's own forms, and with the message naming the operator and
    /// the operand of carrier `int` where a decimal literal meets one (DESIGN.md
    /// sec:diagnostics, the worked example at an operator); and in no row otherwise.
    fn literal_refused(
        &mut self,
        what: &str,
        sig: &Sig,
        args: &[Option<Arg<'a>>],
        (s, mut m): (Span, Msg),
        pass: bool,
        span: Span,
    ) {
        // A decimal literal beside an operand that is an `int` gets the worked message of
        // sec:diagnostics, which names the operand: an operand whose numbers are `int`s, as
        // `n` bound to `1`, or of a class that holds `int` alone.
        let lit = args
            .iter()
            .flatten()
            .find_map(|a| a.lit.as_ref().filter(|l| l.site == s));
        let int = |ck: &Self, t: &Ty| {
            t.numeric_carrier() == Some(Carrier::Int)
                || ck.class_of_ty(t).is_some_and(|r| {
                    let r = ck.find(r);
                    ck.classes[r].mask == Carrier::Int.bit()
                })
        };
        let other = args
            .iter()
            .flatten()
            .find(|a| a.lit.is_none() && int(self, &a.ty));
        if let (Some(l), Some(o)) = (lit, other)
            && l.bare
            && lit_carrier(&l.value) == Carrier::F64
        {
            let t = self.t;
            let name = match o.at.and_then(|at| Some((at, self.seen.get(&at)?))) {
                Some((at, (_, Src::Name(id)))) => Some((t.res.binders[*id].name.as_str(), at)),
                _ => None,
            };
            // The operator's symbol, and whether the literal is its left operand, where it is
            // a binary arithmetic operator.
            let op = what
                .strip_prefix('`')
                .and_then(|w| w.strip_suffix('`'))
                .filter(|o| matches!(*o, "+" | "-" | "*" | "/") && args.len() == 2)
                .map(|o| {
                    (
                        o,
                        args[0]
                            .as_ref()
                            .and_then(|a| a.lit.as_ref())
                            .is_some_and(|a| a.site == s),
                    )
                });
            m = decimal_at_int(l, what, name, op);
        }
        if self.no_arrow_at_carrier(what, sig, args) {
            let notes = self.derive(&[s]);
            self.reject(Some(Row::NoArrowAtCarrier), s, m, notes);
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
            self.reject(Some(Row::LiteralCarrier), s, m, notes);
        } else {
            // A refused literal is a literal at a carrier it cannot take, whatever else the
            // application holds.
            let notes = self.derive(&[s]);
            self.reject(Some(Row::LiteralCarrier), s, m, notes);
        }
    }

    /// The rejection of `what` applied to `args` where the argument `a`, a call of literal
    /// values ([`call_values`]), may give the value `v` that is not read at the carrier `c`
    /// ([`read_at`]): an integer `c` does not hold exactly, or a decimal at `rat`. The carrier
    /// is that of `a`'s parameter, or, where `shared` holds, that of the other arguments at
    /// the same type variable, as the other operand of `x * g(c)`.
    pub(super) fn unread_call(
        &self,
        what: &str,
        args: &[Option<Arg>],
        a: &Arg,
        v: &Value,
        c: Carrier,
        shared: bool,
    ) -> String {
        let c = c.name();
        let call = match (a.expr, self.t.text) {
            (Some(e), Some(t)) => &t[e.span.start..e.span.end],
            _ => "the call",
        };
        let (takes, change) = match shared {
            false => (
                format!("that {what} takes here"),
                format!("give this parameter of {what}"),
            ),
            true => (
                format!("of the other arguments of {what} here"),
                format!("give the other arguments of {what}"),
            ),
        };
        let why = match v {
            Value::Float(_) => format!(
                ": `{call}` may give the decimal {v}, which nothing fixes where it is written, \
                 so it is an `f64` there; an `f64` is not read as the `rat` {takes}, since a \
                 call gives that `f64`, not the decimal written. Write that decimal with the \
                 suffix `r` where it is written, as {v}r, or {change} the type `f64`"
            ),
            _ => format!(
                ": `{call}` may give the integer {v}, which `{c}` does not hold exactly, so it \
                 cannot be read as the `{c}` {takes}; an integer a call gives is read at `{c}` \
                 only where `{c}` holds it exactly, as an integer literal is. Make that value \
                 one `{c}` holds exactly where it is written, or {change} a type that holds \
                 {v}, such as `int`"
            ),
        };
        self.rejected_because(what, args, &why)
    }

    /// Binds each variable of the parameter `p` that no other argument binds to `Never`, for an
    /// argument with no value: a union with the empty type, so the same in any order.
    fn bind_never(&self, p: &Ty, binds: &mut Binds) {
        let mut vars = Vars::default();
        p.vars_in(&mut vars);
        for v in vars.order.into_iter().filter(|v| !self.is_class(v)) {
            binds.or_insert_with(v, Ty::empty);
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn apply_one(
        &mut self,
        what: &str,
        sig: &Sig,
        k: usize,
        args: &[Option<Arg<'a>>],
        unneeded: &[bool],
        defer: BTreeSet<Arc<str>>,
        span: Span,
    ) -> Result<(Ty, Vec<usize>), String> {
        let arrow = &sig.arrows[k];
        let fail = |ck: &Self| Err(ck.rejected(what, args));
        let mut binds = Binds::new();
        let mut grouped = vec![false; args.len()];
        // The arguments each bounded variable stands at, in one pass over the arguments: one
        // pass per variable over every argument cost `O(v a)`.
        // Complexity tradeoff (COMPLEXITY.md F65): naive, a scan of the `a` arguments for each
        // of the `v` bounded variables, O(v·a); used, one pass grouping them in a hash map,
        // O(a + v) expected, plus one `Vec` of positions per variable.
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
            // The branches of an `if` of literals, `x / (if c { 2 } else { -3 })`: each takes
            // the carrier or joins the class of the other arguments as a lone literal does.
            // Where the other arguments give neither, they are their own values' carriers, as
            // before. Complexity tradeoff: each branch is read once here and adopted or joined
            // once below, O(n) in the branches; the naive form reads the arguments' type
            // `2 | -3`, whose `int` meets the `rat` of `x` and rejects the call.
            let mut branched: Vec<&Arg> = Vec::new();
            let mut called: Vec<(&Arg, Vec<Value>)> = Vec::new();
            for &i in &at {
                grouped[i] = true;
                let a = args[i].as_ref().expect("an argument");
                if let Some(l) = &a.lit {
                    lits.push(l.clone());
                    continue;
                }
                if a.branches.is_some() {
                    valued = true;
                    branched.push(a);
                    continue;
                }
                if let Some(vs) = call_values(a) {
                    valued = true;
                    called.push((a, vs));
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
            // A call of literal values alone, `x * g(c)` with `x: f64` and `g` of type `(bool)
            // -> 1 | 2`, is read at the one carrier, `f64` or `rat`, of the other arguments, as
            // at a parameter of that carrier ([`read_call`]; L1.26a: "each keeps its own value
            // and is fixed where the result is used"). Elsewhere its values are their own
            // carriers, as before: `g(c) * g(c)` is an `int`. Each call is read once, O(v log v)
            // in the values its type lists ([`read_at`]).
            let one = match Carrier::of_mask(carriers).collect::<Vec<_>>()[..] {
                [c @ (Carrier::F64 | Carrier::Rat)] if classes.is_empty() => Some(c),
                _ => None,
            };
            for (a, vs) in called {
                match one.and_then(|c| Some((c, read_at(&vs, c)?))) {
                    Some((c, Ok(_))) => {
                        let e = a.expr.expect("a call read at a carrier");
                        self.put(Undo::Fit(e.span, Some(Fit::Read(c))));
                    }
                    Some((c, Err(v))) => {
                        return Err(self.unread_call(what, args, a, &v, c, true));
                    }
                    None => {
                        for p in a.ty.pieces() {
                            match p.carrier() {
                                Some(c) => carriers |= c.bit(),
                                None => return fail(self),
                            }
                        }
                    }
                }
            }
            // A branch that is an operation on literals alone, `if c { 2 + 1 } else { 1 }`,
            // brings its own class, which takes the carrier or merges with the class of the
            // other arguments, as the operation alone would.
            let given = carriers != 0 || !classes.is_empty();
            for ls in branched.iter().filter_map(|a| a.branches.as_ref()) {
                for b in ls.iter() {
                    match (given, b) {
                        (true, Branch::Lit(l)) => lits.push(l.clone()),
                        (true, Branch::Op { class, .. }) => classes.push(*class),
                        (false, b) => carriers |= lit_carrier(b.value()).bit(),
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
                    // Literals alone, as in `inc(x: 2.5)`: the carriers of the bound that
                    // every literal takes. Inside a function they make a class of their own,
                    // which takes the carrier of what the result meets, and `int` or a
                    // rejection where it meets none ([`Ck::resolve`]). Outside one nothing
                    // else gives them a carrier: integer literals alone are `int` where the
                    // bound holds it, one carrier left is taken, and with two or more the
                    // first decimal literal, or else the first literal, is rejected.
                    let takes: Vec<Carrier> = Carrier::of_mask(m)
                        .filter(|&c| lits.iter().all(|l| fits(l, c)))
                        .collect();
                    let ints = lits.iter().all(|l| lit_carrier(&l.value) == Carrier::Int);
                    match takes[..] {
                        [] => return fail(self),
                        _ if self.level > 0 && self.replaying == 0 => {
                            let k = self.class();
                            self.classes[k].generic = true;
                            if !self.restrict(k, m, what, span) {
                                return fail(self);
                            }
                            for l in &lits {
                                if !self.join(k, &l.joining(), false) {
                                    return fail(self);
                                }
                            }
                            Ty::var(format!("${}", self.find(k)).into())
                        }
                        _ => {
                            let c = match takes[..] {
                                _ if ints && takes.contains(&Carrier::Int) => Carrier::Int,
                                [c] => c,
                                [c, ..] => {
                                    let l = (lits.iter())
                                        .find(|l| lit_carrier(&l.value) == Carrier::F64)
                                        .unwrap_or(&lits[0]);
                                    let notes = self.derive(&[l.site]);
                                    let m = unfixed(l, &takes, None);
                                    self.reject(Some(Row::UnfixedDecimal), l.site, m, notes);
                                    c
                                }
                                [] => unreachable!("a carrier every literal takes"),
                            };
                            for l in &lits {
                                self.adopt_to(l, c);
                            }
                            Ty::carrier(c)
                        }
                    }
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
                // The branches of an `if` of literals each join it as a lone literal does.
                let ok = match (&a.lit, &a.branches) {
                    (Some(l), _) => self.join(k, &self.joining(l), false),
                    (None, Some(ls)) => ls.iter().all(|b| self.branch_joins(k, b, what, span)),
                    (None, None) => self.flow(k, &a.ty, what, span),
                };
                if !ok {
                    return fail(self);
                }
                continue;
            }
            let ty = match adopted(a, p, self.rough) {
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
                // A call of literal values alone is read at the parameter's carrier.
                Ok(None) => match read_call(a, p) {
                    Some(Ok((t, c))) => {
                        let e = a.expr.expect("a call read at a carrier");
                        self.put(Undo::Fit(e.span, Some(Fit::Read(c))));
                        Cow::Owned(t)
                    }
                    Some(Err((v, c))) => {
                        return Err(self.unread_call(what, args, a, &v, c, false));
                    }
                    None => Cow::Borrowed(&a.ty),
                },
            };
            if a.lit.is_some() {
                if !self.sub(&ty, p, &mut binds) {
                    let why = ty.refused(p);
                    return Err(self.rejected_because(what, args, &why));
                }
                continue;
            }
            // An argument with no value, `Never`, is in every parameter type and gives each
            // variable of its parameter no value: the variable is bound to `Never` unless
            // another argument binds it, and a need on it is checked on `Never`, not on the
            // unknown. Binding is a union, so this is the same in any order of the arguments.
            if ty.is_empty() {
                self.bind_never(p, &mut binds);
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
        //
        // A bounded variable stands for a carrier, not for the values the arguments hold
        // (DESIGN.md step L1.26: a call "checks that its arguments' carriers are one
        // carrier in the bound"): the body's operators make new values of that carrier. So
        // each scalar piece of the binding is widened to its whole carrier before the result
        // is read. Bound to the arguments' own values, `f(x, p) = x + p[0]` called as
        // `f(x: 1r, p: (2r, 1))` gave `1r | 2r`, the two literals the call passes, for a value
        // `3r` outside it (LIT-generic-parts-type). Classes, variables and other values stay
        // as they are. Complexity tradeoff (COMPLEXITY.md F165): naive, a second walk over the
        // binding after this check, O(p) for p pieces, reading each piece's class and carrier
        // again; used, the widened binding built in the pass this check makes already, O(p),
        // one union per piece.
        for (v, &m) in &sig.bounds {
            let Some(t) = binds.get(v).cloned() else {
                continue;
            };
            let mut kinds = 0u8;
            let mut class: Option<usize> = None;
            let mut rest = Ty::empty();
            let mut whole = Ty::empty();
            for piece in t.pieces() {
                let (of, carrier) = (self.class_of(&piece), piece.carrier());
                whole = whole.union(&match (of, carrier) {
                    (None, Some(c)) => Ty::carrier(c),
                    _ => piece.ty(),
                });
                let ok = match (of, carrier) {
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
            binds.insert(v.clone(), whole);
        }
        binds.retain(|v, _| !self.is_class(v));
        let mut out = Ty::empty();
        let given: Vec<&Arg> = args.iter().flatten().collect();
        if given.iter().any(|a| a.ty.dynamic) {
            out = out.union(&Ty::dynamic());
        }
        // The call takes place when each argument has a value: one whose every value passed by
        // leaves it untaken, and so does one of type `Never` that the call needs. One of type
        // `Never` that a function's body reads only where its result says (`y` in
        // `k(x, y) = y` with `k(n, 1)`) does not: the result is the arrow's, with the
        // parameter's variables bound to `Never`, so it is `Never` only where that argument
        // reaches it on every path.
        if args.iter().zip(unneeded).all(|(a, &unneeded)| {
            a.as_ref().is_none_or(|a| {
                unneeded || a.lit.is_some() || a.ty.pieces().iter().any(|p| *p != Piece::Dyn)
            })
        }) {
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
        if self.level == 0 && self.replaying == 0 && !self.trying {
            self.unfixed_args(what, sig, k, args, &grouped);
        }
        self.applied = Some((binds, left));
        Ok((out, vec![0]))
    }

    /// Rejects each decimal literal with no suffix, alone, in a tuple display or in the
    /// payload of an atom, in an argument of the arrow `k` of `sig`, called as `what`, where
    /// nothing gives it a carrier, outside a function (row UnfixedDecimal; DESIGN.md step
    /// L1.26b: an unfixed decimal is rejected wherever it stands): `0.5` in `y = id(x: 0.5)`,
    /// in `y = id(x: (0.5, 1))` and in `y = id(x: #bad(0.5))` with `id(x) = x`. The literal
    /// stands at a variable of the arrow, which the arrow takes in any carrier; it is fixed
    /// where another argument reaches that variable, or a variable a need of the signature
    /// ties to it, other than through literals with no suffix: `x` gives `p[0]` its carrier
    /// in `y = f(x: 1.0f64, p: (0.5, 1))` with `f(x, p) = x + p[0]`. Another component of the
    /// tuple display the literal stands in, where the display reaches the variable whole, fixes
    /// nothing for it: in `id(x: (0.5f64, 0.5))` the components are apart, and the second is
    /// rejected. A parameter of a written type gives the literal its carrier ([`adopted`]),
    /// and the literals at a bounded variable alone, `inc(x: 2.5)`, are taken where the
    /// arguments are grouped (`grouped`). Nothing gives a literal in the payload of an atom a
    /// carrier, as at a binding ([`unfixed_parts`]). The fixes write the literal with each
    /// carrier the bounds of those variables take, and name the value the literal then is,
    /// since the binder's would need a call of the program's function; two or more are
    /// rejected in one message ([`Self::reject_unfixed`]).
    ///
    /// Complexity tradeoff: the naive way asks, for each literal, whether any other argument
    /// reaches its variable through the needs, a walk of the arguments and the needs for each
    /// literal, `O(l (a + n))`. Here one walk of the arguments' parts and the needs' variables
    /// puts the variables in sets that a need ties together (union by size with path
    /// halving), each set marked fixed once with the place that fixed it first and whether
    /// another place did too, then each literal looks up its set: `O(a + n + l)` times the
    /// inverse Ackermann function, for `a` parts, `n` variables in needs and `l` literals.
    /// The walks keep their own stacks, since tuple displays nest as deep as the text.
    fn unfixed_args(
        &mut self,
        what: &str,
        sig: &Sig,
        k: usize,
        args: &[Option<Arg<'a>>],
        grouped: &[bool],
    ) {
        enum Src<'p, 'e> {
            Lit(&'p Lit),
            Parts(&'p [Part], Option<&'e Expr>),
            Other(Option<&'e Expr>),
        }
        // The component `i` of the tuple display `e`, where it is one.
        fn item(e: Option<&Expr>, i: usize) -> Option<&Expr> {
            match e.map(|e| &e.kind) {
                Some(ExprKind::Tuple(items)) => items.get(i),
                _ => None,
            }
        }
        fn of<'p, 'e>(part: &'p Part, e: Option<&'e Expr>) -> Src<'p, 'e> {
            match part {
                Part::Lit(l) => Src::Lit(l),
                Part::Tuple(ps) => Src::Parts(ps, e),
                Part::Other => Src::Other(e),
            }
        }
        let mut sets = VarSets::default();
        for need in &sig.needs {
            let mut vs = Vars::default();
            need.vars_in(&mut vs);
            let mut it = vs.order.iter();
            if let Some(first) = it.next() {
                let a = sets.id(first);
                for v in it {
                    let b = sets.id(v);
                    sets.union(a, b);
                }
            }
        }
        // Each literal at a variable, with the place it reached the variable from: an
        // argument, or a part of one at a component of a written type.
        let mut lits: Vec<(usize, usize, &Lit)> = Vec::new();
        // The literals in payloads of atoms, which nothing gives a carrier.
        let mut payloads: Vec<Lit> = Vec::new();
        let src_text = self.t.text;
        let in_payloads = |e: Option<&Expr>, out: &mut Vec<Lit>| {
            let Some(e) = e else {
                return;
            };
            for (x, _) in value_parts(e).leaves {
                if let Some(l) = literal(x, src_text).filter(|l| l.bare)
                    && lit_carrier(&l.value) == Carrier::F64
                    && x.span != e.span
                {
                    out.push(l);
                }
            }
        };
        let mut place = 0;
        let arrow = &sig.arrows[k];
        for (i, (a, p)) in args.iter().zip(&arrow.params).enumerate() {
            let Some(a) = a else {
                continue;
            };
            if grouped[i] {
                sets.fix_all(p);
                continue;
            }
            let src = match (&a.lit, &a.parts) {
                (Some(l), _) => Src::Lit(l),
                (None, Some(ps)) => Src::Parts(ps, a.expr),
                (None, None) => Src::Other(a.expr),
            };
            let mut todo = vec![(src, p)];
            while let Some((src, w)) = todo.pop() {
                let Some(v) = w.as_var() else {
                    // A written type: each component of a tuple display stands at its
                    // component, where the type has one shape of that length.
                    match src {
                        Src::Parts(ps, e) => match shapes([w], ps.len())[..] {
                            [cs] => todo.extend(
                                (ps.iter().zip(cs).enumerate())
                                    .map(|(j, (part, c))| (of(part, item(e, j)), c)),
                            ),
                            _ => {
                                sets.fix_all(w);
                                let mut inner = vec![(ps, e)];
                                while let Some((ps, e)) = inner.pop() {
                                    for (j, part) in ps.iter().enumerate() {
                                        match part {
                                            Part::Tuple(qs) => inner.push((qs, item(e, j))),
                                            Part::Other => in_payloads(item(e, j), &mut payloads),
                                            Part::Lit(_) => {}
                                        }
                                    }
                                }
                            }
                        },
                        Src::Other(e) => {
                            sets.fix_all(w);
                            in_payloads(e, &mut payloads);
                        }
                        Src::Lit(_) => sets.fix_all(w),
                    }
                    continue;
                };
                // The whole argument, or part, flows into the variable `v` from one place:
                // each literal in it with no suffix stands there, and anything else fixes
                // `v` for the literals that reach it from other places.
                place += 1;
                let v = sets.id(v);
                let mut inner: Vec<Src> = vec![src];
                while let Some(src) = inner.pop() {
                    match src {
                        Src::Lit(l) if !l.bare => sets.fix_by(v, place),
                        Src::Lit(l) if lit_carrier(&l.value) == Carrier::F64 => {
                            lits.push((v, place, l))
                        }
                        Src::Lit(_) => {}
                        Src::Parts(ps, e) => inner
                            .extend((ps.iter().enumerate()).map(|(j, part)| of(part, item(e, j)))),
                        Src::Other(e) => {
                            sets.fix_by(v, place);
                            in_payloads(e, &mut payloads);
                        }
                    }
                }
            }
        }
        if lits.is_empty() && payloads.is_empty() {
            return;
        }
        // The carriers each set's bounds take: every carrier where none is bounded.
        let mut takes = vec![u8::MAX; sets.up.len()];
        for (v, &m) in &sig.bounds {
            if let Some(&i) = sets.ix.get(v) {
                let r = sets.find(i);
                takes[r] &= m;
            }
        }
        let mut found: Vec<(Span, Msg)> = Vec::new();
        for (v, from, l) in lits {
            let r = sets.find(v);
            if sets.fixed_for(r, from) || self.is_class(&sets.names[v]) {
                continue;
            }
            let cs: Vec<Carrier> = [Carrier::F64, Carrier::Rat]
                .into_iter()
                .filter(|&c| takes[r] & c.bit() != 0 && fits(l, c))
                .collect();
            // No carrier of a decimal is taken there: the call is refused for its bounds,
            // `min` in `g((0.5, 1.0))` with `g(positional a) = min(a, (1, 2))`, and a
            // rejection with no fix would only repeat it.
            if cs.is_empty() {
                continue;
            }
            found.push((l.site, unfixed(l, &cs, None)));
        }
        for l in &payloads {
            let cs: Vec<Carrier> = [Carrier::F64, Carrier::Rat]
                .into_iter()
                .filter(|&c| fits(l, c))
                .collect();
            found.push((l.site, unfixed(l, &cs, None)));
        }
        found.sort_by_key(|(s, _)| s.start);
        self.reject_unfixed(&format_args!("the arguments of `{what}`"), found);
    }

    /// [`Self::apply`] of a signature of several arrows, each over one carrier or a tuple:
    /// an operator, a prelude word, or a section of one. The classes of the arguments merge,
    /// since every arrow takes one carrier for all its parameters, and its literals join
    /// them; without a class, each literal adopts the carrier of its parameter on the
    /// arrows that adopt fewest. Then the arguments' pieces are taken in turn, each state
    /// the arrows still alive and the carriers they allow where the class stands
    /// ([`ClassAt`]): a state per such pair, not per combination of pieces.
    // Complexity tradeoff (COMPLEXITY.md row ISSUE1-tvar-else): naive version, a state per
    // combination of the arguments' pieces, O(p^a) for a arguments of p pieces. Used: states
    // merged by (arrows alive, `ClassAt`), O(a p s A) for A arrows and s states, s bounded by
    // the arrows and carriers and independent of the program's size. Tradeoff: states merge
    // only when both parts are equal, so an operator's s can double the count keyed by arrows
    // alone (the class's restriction is kept on each path).
    fn apply_many(
        &mut self,
        what: &str,
        sig: &Sig,
        args: &mut [Option<Arg<'a>>],
        unneeded: &[bool],
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
                // A literal joins the class, and so does each branch of an `if` of literals,
                // which has no other operand and takes the class's carrier from a parameter
                // of it, as a lone literal argument does ([`Lit::joining`]).
                for a in args.iter().flatten() {
                    if let Some(l) = &a.lit
                        && !self.join(k, l, false)
                    {
                        return Err(self.rejected(what, args));
                    }
                    for b in a.branches.iter().flat_map(|ls| ls.iter()) {
                        if !self.branch_joins(k, b, what, span) {
                            return Err(self.rejected(what, args));
                        }
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
        // An argument with no value, of type `Never` or of atoms that all pass by, has no piece
        // and keeps every arrow, so each value of the other arguments is still checked against
        // the arrows: `h(1) + u` with `h(1)` of type `Never` and `u` of `int | true` is
        // rejected for `true`. The application then takes place on no value and gives none,
        // unless the call needs none of those arguments (`unneeded`).
        let no_value: Vec<bool> = (args.iter())
            .map(|a| {
                a.as_ref()
                    .is_some_and(|a| a.lit.is_none() && a.ty.is_empty())
            })
            .collect();
        // The states: the arrows alive, whether a piece was unknown, the class's place, and
        // the first pieces that reached it, by argument.
        type State = (Vec<usize>, bool, ClassAt, Vec<Option<Piece>>);
        let mut states: Vec<State> = vec![(kept.clone(), false, None, Vec::new())];
        for (i, a) in args.iter().enumerate() {
            let pieces: Vec<Option<Piece>> = match a {
                None => vec![None],
                // An argument of no value keeps every arrow; an argument of type `Never` the
                // call does not need is one of them.
                Some(_) if no_value[i] => vec![None],
                Some(a) if (a.lit.is_some() || a.branches.is_some()) && class.is_some() => {
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
                // The call's literals are printed as written there.
                let shown: Vec<String> = ck.near(Some(span), |ck| {
                    (path.iter().zip(&no_value))
                        .map(|(p, &none)| match p {
                            Some(p) => ck.show(&p.ty()),
                            None if none => ck.show(&Ty::empty()),
                            None => "_".into(),
                        })
                        .collect()
                });
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
                    for ((p, t), &u) in path.iter().zip(&a.params).zip(unneeded) {
                        match p {
                            Some(p) => {
                                self.sub(&p.ty(), t, &mut binds);
                            }
                            None if u => self.bind_never(t, &mut binds),
                            None => {}
                        }
                    }
                    out = out.union(&close(&a.result.subst(&binds), sig, |v| self.is_class(v)));
                }
            }
        }
        // With an argument of no value that the call needs, the application never takes place:
        // it gives no value, whatever its arrows would give. With only arguments of type
        // `Never` it does not need, it gives what its arrow gives with them bound to `Never`.
        match (no_value.iter().zip(unneeded)).any(|(&none, &u)| none && !u) {
            true => Ok((Ty::empty(), kept)),
            false => Ok((out, kept)),
        }
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
/// at the default, `span`; `both` is the text of their union, `want | got`, each operand
/// parenthesized where it needs to be.
fn default_repairs(name: &str, got: &str, want: &str, both: &str, span: Span) -> Vec<Note> {
    [
        format!("repair: write a default of type {want}"),
        format!(
            "repair: declare `{name}` with a type that holds {got} as well, as `{name}: {both}`{DECLARE}"
        ),
    ]
    .into_iter()
    .map(|text| Note { span, text })
    .collect()
}

/// The repairs of an int `^` whose exponent may be below 0, at `span`.
fn exponent_repairs(span: Span) -> Vec<Note> {
    [
        "repair: test the exponent first, as `if n >= 0 { x^n } else { … }`, so that inside \
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

/// Why a divisor is always zero, as [`Ck::zero_divisor`] finds it.
enum Zero {
    /// It is the literal `0`, or `0r`.
    Literal,
    /// Its type, written here, holds no value but zero.
    Type(String),
    /// The int value its text folds to is `0`.
    Folded,
    /// The tests the walk is in leave it only `0`.
    Tests,
    /// Its names cancel and its constants, if it has any (the flag), add to zero: each name, in
    /// order of first use, is added as often as it is subtracted.
    Cancels(Vec<String>, bool),
}

/// Whether `v` is the int or rat zero.
fn is_zero(v: &Value) -> bool {
    match v {
        Value::Int(n) => *n == 0,
        Value::Rat(r) => r.is_zero(),
        _ => false,
    }
}

/// Whether `e` is a `rat` literal of value zero, as `0r`, `0.00r` or `0e9r`: one whose digits
/// before its exponent are all `0`.
// Complexity tradeoff: one pass over the literal's text, O(its length), reading no digit into
// a number; reading its value with `Rat::decimal`, as the walk does once, costs that again and
// more for a large exponent.
fn zero_rat(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Rat(d) => (d.split(['e', 'E']).next()).is_some_and(|m| {
            m.bytes().all(|c| c == b'0' || c == b'.') && m.bytes().any(|c| c == b'0')
        }),
        _ => false,
    }
}

/// The exact rational value of an int or rat `v`.
fn as_rat(v: &Value) -> Option<Rat> {
    match v {
        Value::Int(n) => Some(Rat::int((*n).into())),
        Value::Big(r) | Value::Rat(r) => Some((**r).clone()),
        _ => None,
    }
}

// The rule "Operation that always fails" (DESIGN.md sec:failure) for the built-in operations
// whose operands the checker's own algebra decides: a division by a divisor that is always zero,
// a cast or conversion word whose every operand value fails, and a read whose key is never one
// of the map's keys (R11). A call of a user function is not judged: the checker never runs it.
impl<'a> Ck<'_, 'a> {
    /// Why the divisor `y` of `x op y` (`b` as written) is always zero, if the checker shows it.
    /// `/` on `f64` has no `#divByZero`, so a divisor that may be `f64` is not judged, nor is
    /// an operand whose type lists nothing (the operation is never reached).
    fn zero_divisor(&mut self, op: &str, x: &Arg<'a>, y: &Arg<'a>, b: &'a Expr) -> Option<Zero> {
        if x.ty.lists_nothing() || y.ty.lists_nothing() {
            return None;
        }
        let f64 = Ty::carrier(Carrier::F64);
        if op == "/" && (x.ty.meets(&f64) || y.ty.meets(&f64)) {
            return None;
        }
        let unsigned = match &b.kind {
            ExprKind::Unary("-", a) => a,
            _ => b,
        };
        if y.lit.as_ref().is_some_and(|l| is_zero(&l.value)) || zero_rat(unsigned) {
            return Some(Zero::Literal);
        }
        if self.known(b).value.as_ref().is_some_and(is_zero) {
            return Some(Zero::Folded);
        }
        let value = y.ty.without_atoms();
        if value.closed() && !value.lists_nothing() {
            let zeros = Ty::lit(&Value::Int(0)).union(&Ty::lit(&Value::rat(Rat::int(0.into()))));
            if value.subtype(&zeros) {
                // Its zero printed as the divisor writes it, `-0r` in `x / (if c { -0r } else
                // { 0r })`, which writes it first.
                // The chain of names is walked once per such division, O(its length), which is
                // also the length of the derivation the message prints.
                let at = self.written_at(b.span, &mut HashMap::new());
                let text = self.near(Some(at), |ck| ck.text(&y.ty));
                return Some(Zero::Type(text));
            }
            // The narrowing of the tests reads values as ints, so it is read only for an int
            // divisor.
            if value.subtype(&Ty::carrier(Carrier::Int)) {
                let (ints, narrowed) = self.ints_here(b);
                if ints == IntervalSet::single(0) {
                    return Some(if narrowed { Zero::Tests } else { Zero::Folded });
                }
            }
        }
        self.cancels(b)
            .map(|(names, constants)| Zero::Cancels(names, constants))
    }

    /// The names of `e`, in order of first use, and whether it has constants, when `e` is a sum of names and constants under
    /// `+`, `-` and unary `-` in which each name is added as often as it is subtracted and the
    /// constants add to zero, as in `x - x` or `(a + 1) - (1 + a)`. One pass over `e` on an
    /// explicit stack, each node once.
    ///
    /// Complexity tradeoff: the naive test of "always zero" evaluates `e` at every value of
    /// its names, which is unbounded. Used: the linear form of `e` over `+` and `-`, one count
    /// per name, O(n) for n nodes, and the constants added in pairs, a balanced tree, O(M(S)
    /// log n) for S digits in all, where adding them left to right is O(n·S). Given up: a
    /// product, as in `2 * x - x - x`, a name bound to a value that is not a constant, as in
    /// `z = x - x`, and any call: such a divisor is not shown zero, and its division keeps
    /// `#divByZero`. COMPLEXITY.md row C38.
    fn cancels(&mut self, e: &'a Expr) -> Option<(Vec<String>, bool)> {
        let mut counts: HashMap<usize, (usize, i64)> = HashMap::new();
        let mut names: Vec<String> = Vec::new();
        let mut constants: Vec<Rat> = Vec::new();
        let mut stack = vec![(e, false)];
        while let Some((x, neg)) = stack.pop() {
            match &x.kind {
                ExprKind::Binary(o @ ("+" | "-"), a, b) => {
                    stack.push((b, neg ^ (*o == "-")));
                    stack.push((a, neg));
                }
                ExprKind::Unary("-", a) => stack.push((a, !neg)),
                ExprKind::Rat(d) => {
                    let r = Rat::decimal(d).ok()??;
                    constants.push(if neg { r.neg() } else { r });
                }
                _ => {
                    if let Some(v) = self.known(x).value {
                        let r = as_rat(&v)?;
                        constants.push(if neg { r.neg() } else { r });
                        continue;
                    }
                    let ExprKind::Name(n) = &x.kind else {
                        return None;
                    };
                    let id = match self.t.res.uses.get(&x.span) {
                        Some(Ref::Bound(ids)) if ids.len() == 1 => ids[0],
                        _ => return None,
                    };
                    let next = names.len();
                    let (_, c) = counts.entry(id).or_insert_with(|| {
                        names.push(n.clone());
                        (next, 0)
                    });
                    *c = c.checked_add(if neg { -1 } else { 1 })?;
                }
            }
        }
        if names.is_empty() || counts.values().any(|&(_, c)| c != 0) {
            return None;
        }
        while constants.len() > 1 {
            let mut next = Vec::with_capacity(constants.len().div_ceil(2));
            let mut it = constants.into_iter();
            while let Some(a) = it.next() {
                next.push(match it.next() {
                    Some(b) => a.add(&b).ok()?,
                    None => a,
                });
            }
            constants = next;
        }
        let had = !constants.is_empty();
        constants.iter().all(Rat::is_zero).then_some((names, had))
    }

    /// Rejects `x op y` at `span`, `dividend` the dividend as the program writes it (its literal
    /// or its name, else `…`) and `b` the divisor as written, whose divisor is always zero for
    /// the reason `why`: every value that reaches it fails with `#divByZero`.
    fn divides_by_zero(&mut self, op: &str, why: Zero, dividend: &str, b: &'a Expr, span: Span) {
        let (result, kind) = match op {
            "/" => ("a rat", "rat"),
            _ => ("an int", "int"),
        };
        let mut notes = Vec::new();
        let reason = match why {
            // The literal as the program writes it, `0_0` or `0r`.
            Zero::Literal if is_literal(b) => {
                format!(
                    "its divisor is the literal {}",
                    Operand::Literal(b, self.t.text)
                )
            }
            Zero::Literal => "its divisor is the literal 0".to_string(),
            Zero::Type(t) => format!("its divisor has the type `{t}`, whose only value is 0"),
            Zero::Folded => "its divisor is built from constants and works out to 0".to_string(),
            Zero::Tests => {
                notes.extend(self.deciding_notes(b));
                "the tests around it leave its divisor only the value 0".to_string()
            }
            Zero::Cancels(names, constants) => {
                let each = match names.len() {
                    1 => "",
                    _ => "each of ",
                };
                let names = names
                    .iter()
                    .map(|n| format!("`{n}`"))
                    .collect::<Vec<_>>()
                    .join(", ");
                let constants = match constants {
                    true => ", and its constants add up to 0",
                    false => "",
                };
                format!(
                    "its divisor adds {each}{names} as often as it subtracts it{constants}, which \
                     makes it 0 for every value of {names}"
                )
            }
        };
        notes.push(Note {
            span: b.span,
            text: "this divisor is always 0".to_string(),
        });
        notes.extend(self.derive(&[b.span]));
        let menu = [
            format!(
                "repair: divide by a value that can be other than 0, such as a parameter `d: {kind}`: \
                 `{dividend} {op} d`"
            ),
            "repair: write `#divByZero` in place of this division, where the failure is meant"
                .to_string(),
            "repair: write `#bug(\"…\")` in place of this division, where it is never meant to \
             be reached"
                .to_string(),
        ];
        notes.extend(menu.into_iter().map(|text| Note { span, text }));
        self.rejects_with(
            Row::AlwaysFails,
            span,
            format!(
                "`{op}` here always fails with `#divByZero`: {reason}, so no value that reaches \
                 it gives {result}"
            ),
            notes,
        );
    }

    /// The values the operand `x` of a word may take, when the checker can list them, and the
    /// literal as written when it is one: a literal, in each carrier a bare integer literal may
    /// adopt, or the values of a type that lists them one by one (`"a" | "b"`). A bare decimal
    /// literal is left out: it is rejected as a literal with no carrier. Linear in the size of
    /// the type.
    fn operand_values(&self, x: &Arg<'a>) -> Option<(Vec<Value>, Option<String>)> {
        if let Some(l) = &x.lit {
            let v = neg_value(&l.value, l.neg());
            let mut values = vec![v.clone()];
            if l.bare {
                // A bare integer literal is generic: `7` may be an int, a rat or an f64, so the
                // word fails always only if it fails on each.
                let r = matches!(v, Value::Int(_) | Value::Big(_)).then(|| as_rat(&v))??;
                if let Ok(f) = r.to_f64() {
                    values.push(Value::float(f));
                }
                values.push(Value::rat(r));
            }
            return Some((values, Some(l.written().to_string())));
        }
        let value = x.ty.without_atoms();
        if value.lists_nothing() {
            return None;
        }
        Some((value.kernel()?.values_listed()?, None))
    }

    /// Rejects the word `w` applied at `span` to an operand at `at` whose values are `values`,
    /// `written` when it is a literal, and whose result is `r`, when every value the word takes
    /// fails with an atom. A value the kernel cannot convert for want of memory leaves the call
    /// unjudged.
    ///
    /// Complexity tradeoff: the cast is run on each listed value, which costs what the cast
    /// costs when the program runs, O(d^1.47) for a literal of d digits (COMPLEXITY.md K41),
    /// and O(V) such casts for V listed values. No cheaper test decides whether a long digit
    /// string is exact in the target format. COMPLEXITY.md row C39.
    fn always_fails_word(
        &mut self,
        w: &str,
        (values, written): (Vec<Value>, Option<String>),
        r: &Ty,
        at: Span,
        span: Span,
    ) {
        if r.atoms().is_empty() {
            return;
        }
        let Some(p) = zedc_base::interp::prim(w) else {
            return;
        };
        let sig = word_sig(w);
        let mut fails = Vec::new();
        for v in values {
            if !sig.arrows.iter().any(|a| a.params[0].contains(&v)) {
                continue;
            }
            match run(p, &v) {
                Some(a @ Value::Atom(_)) => fails.push((v, a)),
                Some(_) | None => return,
            }
        }
        let Some((first, _)) = fails.first() else {
            return;
        };
        let carrier = match first {
            Value::Str(_) => "String".to_string(),
            v => lit_carrier(v).name().to_string(),
        };
        let atoms = fails
            .iter()
            .map(|(_, a)| a.to_string())
            .collect::<BTreeSet<_>>();
        let atoms = atoms.into_iter().collect::<Vec<_>>().join(" | ");
        let written = written.or_else(|| match &fails[..] {
            [(v, _)] => Some(self.text(&Ty::lit(v))),
            _ => None,
        });
        let shown = match &written {
            Some(text) => format!("its operand `{text}` gives `{atoms}`"),
            None => format!(
                "each value its operand may be fails: {}",
                fails
                    .iter()
                    .map(|(v, a)| format!("`{}` gives `{a}`", self.text(&Ty::lit(v))))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        };
        let mut notes = vec![Note {
            span: at,
            text: format!("`{w}` cannot convert this operand"),
        }];
        notes.extend(self.derive(&[at]));
        let menu = [
            format!(
                "repair: convert a value known only when the program runs, such as a parameter \
                 `s: {carrier}`: `{w}(s)` gives the result where `s` converts and `{atoms}` where it \
                 does not"
            ),
            format!("repair: write `{atoms}` in place of this call, where the failure is meant"),
            "repair: write `#bug(\"…\")` in place of this call, where it is never meant to be \
             reached"
                .to_string(),
        ];
        notes.extend(menu.into_iter().map(|text| Note { span, text }));
        self.rejects_with(
            Row::AlwaysFails,
            span,
            format!("`{w}` here always fails: {shown}, so this call never gives a value"),
            notes,
        );
    }

    /// The type of the read of the function `sig` at the key `x`, `of` the span of the map as
    /// written, when `x` is never one of its keys (R11): the read is rejected and typed as the
    /// map's entries, so nothing after it fails again. None when the key may be one of them,
    /// or when there is no written map (a replayed need).
    fn key_outside(
        &mut self,
        sig: &Sig,
        x: &Arg<'a>,
        of: Option<Span>,
        span: Span,
        dense: bool,
    ) -> Option<Ty> {
        let of = of?;
        if sig.params.is_empty() || x.ty.lists_nothing() {
            return None;
        }
        let keys = Ty::union_all(sig.arrows.iter().map(|a| &a.params[0]));
        if x.ty.meets(&keys) {
            return None;
        }
        let miss = match dense {
            true => "#outOfBounds",
            false => "#notFound",
        };
        let entries = Ty::union_all(sig.arrows.iter().map(|a| &a.result))
            .without(&(&KType::atom("notFound") | &KType::atom("outOfBounds")));
        let (key, keys_text, entry) = (self.text(&x.ty), self.text(&keys), self.text(&entries));
        let at = x.at.unwrap_or(span);
        let mut notes = vec![Note {
            span: of,
            text: format!("this map has the keys `{keys_text}`, which hold no `{key}`"),
        }];
        notes.extend(self.derive(&[at, of]));
        let mut menu = vec![format!("repair: read the map with a key in `{keys_text}`")];
        if !dense {
            // The key's carriers and atoms, so the wider keys are a type the program can write
            // for any key of the key's kind, not only the literal read here.
            let wider = [
                Carrier::Bool,
                Carrier::Int,
                Carrier::F64,
                Carrier::Rat,
                Carrier::Str,
            ]
            .into_iter()
            .map(Ty::carrier)
            .filter(|c| x.ty.meets(c))
            .fold(Ty::set(x.ty.atoms()), |t, c| t.union(&c));
            let wider = self.text(&keys.union(&wider));
            menu.push(format!(
                "repair: declare the map with the wider keys `{wider} ->? {entry}`, and handle \
                 `#notFound` where the key is missing"
            ));
        }
        menu.push(format!(
            "repair: write `{miss}` in place of this read, where the miss is meant"
        ));
        menu.push(
            "repair: write `#bug(\"…\")` in place of this read, where it is never meant to be \
             reached"
                .to_string(),
        );
        notes.extend(menu.into_iter().map(|text| Note { span, text }));
        self.rejects_with(
            Row::KeyOutsideBound,
            span,
            format!(
                "this read can never find its key: the key is `{key}` and the map's keys are \
                 `{keys_text}`, which share no value, so the read can only give `{miss}`"
            ),
            notes,
        );
        Some(entries)
    }
}

/// `r`, the entry type of a read of a family whose keys are one integer interval, every key
/// present, with its miss `#notFound` written `#outOfBounds` (DESIGN.md sec:type_language, the
/// `m[k]` row). A `#notFound` the key `key` brings is passed by, not a miss, so it stays.
fn out_of_bounds(r: Ty, key: &Ty) -> Ty {
    let not_found = KType::atom("notFound");
    if (&r.atoms() & &not_found).is_empty() {
        return r;
    }
    let r = match (&key.loose() & &not_found).is_empty() {
        true => r.without(&not_found),
        false => r,
    };
    r.union(&Ty::set(KType::atom("outOfBounds")))
}

/// The type `t` of the tuple display `e`, with the component of each span of `new` of the
/// type `new` gives it, made bottom up: a display's type is the row of its components'
/// types ([`Ck::tuple_step`]). The walk keeps its own stack, since displays nest as deep as
/// the text; it costs the size of `e`.
fn retyped(t: &Ty, e: &Expr, new: &HashMap<Span, Ty>) -> Ty {
    enum Step<'e> {
        Visit(Ty, &'e Expr),
        Make(bool, usize),
    }
    let mut todo = vec![Step::Visit(t.clone(), e)];
    let mut out: Vec<Ty> = Vec::new();
    while let Some(step) = todo.pop() {
        match step {
            Step::Visit(t, e) => {
                if let Some(n) = new.get(&e.span) {
                    out.push(n.clone());
                    continue;
                }
                match (&e.kind, &t.tuples[..]) {
                    (ExprKind::Tuple(es), [row]) => {
                        let cs = row.to_vec();
                        if cs.len() != es.len() {
                            out.push(t);
                            continue;
                        }
                        todo.push(Step::Make(row.data(), cs.len()));
                        todo.extend(cs.into_iter().zip(es).rev().map(|(c, e)| Step::Visit(c, e)));
                    }
                    _ => out.push(t),
                }
            }
            Step::Make(data, n) => {
                let cs = out.split_off(out.len() - n);
                out.push(Ty::of_row(match data {
                    true => ty::Row::of_data(cs),
                    false => ty::Row::new(cs),
                }));
            }
        }
    }
    out.pop().expect("one type")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A trial that enters a row is undone with the memos of the rows it entered: the data
    /// check of `($k, 1)` in a trial gives class `k` its data need and enters the row in
    /// [`Ck::data_checked`], and [`Ck::bound`] records the row in [`Ck::clean`]; undone, the
    /// class has no need and neither memo holds the row, so a check after the trial enters the
    /// row again and gives the class its need again (CK-data-memo). Kept after the trial, the
    /// memo would let that check pass the row by and the class would never need data.
    #[test]
    fn a_trial_undone_after_the_memo_entered_a_row_leaves_no_memo() {
        let res = zedc_resolve::resolve::resolve(&[]).expect("the empty unit resolves");
        let t = Tables::new(&[], &res);
        let mut ck = Ck::new(&t);
        let k = ck.class();
        let row = Ty::tuple(vec![
            Ty::var(format!("${k}").into()),
            Ty::lit(&Value::int(1.into())),
        ]);
        let node = row.tuples[0].node();
        let at = Span { start: 1, end: 2 };
        let saved = ck.mark();
        ck.trying = true;
        ck.data(&row, "a tuple", at, at);
        assert_eq!(ck.bound(&row, &mut Binds::new()), row);
        assert!(ck.classes[k].data);
        assert!(ck.data_checked.contains(&node));
        assert!(ck.is_clean(node));
        ck.trying = false;
        ck.undo(&saved);
        assert!(!ck.classes[k].data);
        assert!(!ck.data_checked.contains(&node));
        assert!(!ck.clean.contains_key(&node));
        ck.data(&row, "a tuple", at, at);
        assert!(ck.classes[k].data);
        assert!(ck.data_checked.contains(&node));
    }

    /// A row the memo of clean rows found clean at a level is walked again once that level
    /// ends: the end names the level's classes, which then no longer last, so [`Ck::bound`]
    /// at the level around binds the variable the row holds (CK-data-memo). Kept past the
    /// end, the entry would pass the row by and leave the named variable unbound.
    #[test]
    fn a_row_found_clean_is_walked_again_after_its_level_ends() {
        let res = zedc_resolve::resolve::resolve(&[]).expect("the empty unit resolves");
        let t = Tables::new(&[], &res);
        let mut ck = Ck::new(&t);
        ck.level += 1;
        ck.pending.push(Vec::new());
        let k = ck.class();
        let v: Arc<str> = format!("${k}").into();
        let row = Ty::tuple(vec![Ty::var(v.clone()), Ty::lit(&Value::int(1.into()))]);
        let node = row.tuples[0].node();
        assert_eq!(ck.bound(&row, &mut Binds::new()), row);
        assert!(ck.is_clean(node));
        let sig = Sig {
            params: vec![SParam {
                name: "x".into(),
                positional: true,
                default: None,
            }],
            arrows: vec![Arrow {
                params: vec![row.clone()],
                result: Ty::empty(),
            }],
            bounds: BTreeMap::new(),
            data: false,
            dense: false,
            word: None,
            needs: Vec::new(),
            own: BTreeSet::new(),
            held: BTreeSet::new(),
            named: 0,
            facts: Default::default(),
        };
        ck.generalize(1, sig, &[]);
        assert_eq!(ck.level, 0);
        assert!(ck.classes[k].name.is_some());
        assert!(!ck.is_clean(node));
        let mut dynamic = Binds::new();
        dynamic.insert(v, Ty::dynamic());
        assert_eq!(ck.bound(&row, &mut Binds::new()), row.replace(&dynamic));
    }
}
