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
use zedc_preimage::product::{self, NameProducts, Product, RootFailure, Scope};

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
    let mut ck = Ck::new(t, Ck::fixes_checked);
    // A misused output port stops the check, as the builder's rejection of a read of `m.stdout`
    // stops the build: the walk would read the port as the value of its type, and its errors,
    // a port given to `len` among them, would offer repairs that read the port.
    let ports = super::ports::ports(t);
    let stop = !ports.errors.is_empty();
    for (span, message, notes) in ports.errors {
        ck.error_with(span, message, notes);
    }
    ck.port_params = ports.params;
    if !stop {
        ck.bounds();
        ck.walk(unit);
    }
    // A function marked `@nonblocking` that can block (DESIGN.md sec:ports), decided from the
    // fact found once for every function: one lookup per mark.
    let (blocking, marked) = super::blocking::facts_and_marks(t, unit);
    for (span, message, notes) in super::blocking::marked_errors(&blocking, &marked, t.res, t.text)
    {
        ck.rejects_with(Row::NonblockingCanBlock, span, message, notes);
    }
    ck.finish();
    #[cfg(debug_assertions)]
    clean_check::flush();
    // Every headline is a sentence, so two errors that differ only by its period are one.
    ck.info.errors.iter_mut().for_each(Error::sentence);
    ck.info
        .errors
        .sort_by(|a, b| (a.span, &a.message, &a.menu).cmp(&(b.span, &b.message, &b.menu)));
    ck.info.errors.dedup();
    ck.info.blocking = blocking;
    ck.info
}

/// [`check_text`] with the name the unit's first statement binds given the type `given`, and
/// that statement not checked: how a test gives a name the type of a named atom family
/// (`Ty::named`), which no source form gives until `type` declarations do (step L2.5).
#[doc(hidden)]
pub fn check_given(unit: &[Stmt], res: &Resolution, text: &str, given: Ty) -> Info {
    let t = Tables::with_text(unit, res, Some(text));
    KType::forget_emptiness();
    let _defs = defs::collect();
    let _names = ty::ProgramNames::hold(
        (t.res.binders.iter())
            .filter(|b| b.kind != zedc_resolve::resolve::Kind::Field)
            .map(|b| b.name.as_str()),
    );
    let (first, rest) = unit.split_first().expect("a unit with a first statement");
    let id = (res.binders.iter())
        .position(|b| b.span == first.span)
        .expect("the first statement binds a name");
    let mut ck = Ck::new(&t, Ck::fixes_checked);
    ck.env.insert(id, given);
    ck.bounds();
    ck.walk(rest);
    ck.finish();
    ck.info.errors.iter_mut().for_each(Error::sentence);
    ck.info.errors.dedup();
    ck.info
}

/// The type of the operator `op` applied to arguments of the types `args`, with the errors the
/// application reports: how an operator treats loose and family atoms.
pub fn operator(op: Operator, args: &[Ty]) -> (Ty, Vec<String>) {
    let res = zedc_resolve::resolve::resolve(&[]).expect("the empty unit resolves");
    let t = Tables::new(&[], &res);
    let _defs = defs::collect();
    let mut ck = Ck::new(&t, Ck::fixes_checked);
    let args = args.iter().map(|a| Some(Arg::of(a.clone()))).collect();
    let demand = match op {
        Operator::Binary(BinaryOp::And | BinaryOp::Or) => Demand::First,
        Operator::Binary(
            BinaryOp::Eq
            | BinaryOp::Ne
            | BinaryOp::Lt
            | BinaryOp::Le
            | BinaryOp::Gt
            | BinaryOp::Ge
            | BinaryOp::Add
            | BinaryOp::Sub
            | BinaryOp::Concat
            | BinaryOp::Mul
            | BinaryOp::Div
            | BinaryOp::IntDiv
            | BinaryOp::Mod
            | BinaryOp::Pow,
        )
        | Operator::Unary(UnaryOp::Neg | UnaryOp::Not) => Demand::All,
    };
    let (out, _) = ck.apply_demanding(
        Label::Operator(op),
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
    Unary(UnaryOp, Span),
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
        op: BinaryOp,
        b: &'a Expr,
        span: Span,
    },
    CondAnd2(Box<CondAnd<'a>>),
    CondOf(&'a Expr),
    Logic1 {
        op: BinaryOp,
        b: &'a Expr,
        span: Span,
    },
    Logic2 {
        op: BinaryOp,
        span: Span,
        ta: Ty,
    },
    Bin1 {
        op: BinaryOp,
        b: &'a Expr,
        span: Span,
    },
    Bin2 {
        op: BinaryOp,
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
        positional: &'a [Expr],
        named: &'a [(String, Expr)],
        span: Span,
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
    op: BinaryOp,
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

/// A call of a prelude word that is not a bit word: `w(positional, named)`, or
/// `x.w(positional, named)` with `receiver` the value of `x` and its expression.
struct PreludeCall<'a> {
    w: &'a str,
    receiver: Option<(Arg<'a>, &'a Expr)>,
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
                if op == UnaryOp::Neg
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
                    && op == UnaryOp::Neg
                    && x.expr.is_some_and(|e| self.lit_ops.contains(&e.span))
                {
                    self.lit_ops.insert(span);
                    if x.expr.is_some_and(|e| self.lit_open.contains(&e.span)) {
                        self.lit_open.insert(span);
                    }
                }
                let sig = op_sig(Operator::Unary(op));
                let at = x.expr.map(|e| e.span);
                let t = self
                    .apply(
                        Label::Operator(Operator::Unary(op)),
                        &sig,
                        vec![Some(x)],
                        true,
                        span,
                    )
                    .0;
                self.lit_wrote(span, from);
                // A `-` of an operation of which the text gives something at `rat` gives as much
                // ([`Self::rat_folded`]).
                if op == UnaryOp::Neg
                    && (t.numeric_carrier() == Some(Carrier::Rat)
                        || self.class_beside_atoms(&t).is_some())
                    && let Some(fact) = at.and_then(|at| self.rat_folds.get(&at)).cloned()
                    && let Some(fact) = rat_step(Prim::Neg, Some(fact), None)
                {
                    self.rat_folds.insert(span, fact);
                }
                // The fixes carried up from the operand, as `(-0.5 ^ 1.0r) + 2.5f64` carries the
                // fix of `^` past the `-`, are checked under the `-` with the type they give the
                // operand ([`Self::pending_settled`]); one trial per type carried.
                let carried = at.and_then(|at| Some((at, self.carried.remove(&at)?)));
                self.carried.remove(&span);
                if let Some((at, carried)) = carried {
                    let mut up = HashMap::new();
                    for c in carried {
                        let arg = Arg {
                            at: Some(at),
                            ..Arg::of(c.ty)
                        };
                        let name = Label::Operator(Operator::Unary(op));
                        let (ty, needs) =
                            self.trial(|ck| ck.apply(name, &sig, vec![Some(arg)], true, span).0);
                        match needs.is_some_and(|n| n.is_empty()) {
                            true if ty != t => carry_joined(&mut up, ty, c.fixes),
                            true => {}
                            false => c.fixes.iter().for_each(|p| self.fix_dropped(p)),
                        }
                    }
                    self.carried_up(span, up);
                }
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
                self.looped_condition(cond);
                let out = self.passing(&c, "the condition of `if`", cond.span, Some(cond.span));
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
                let sig = op_sig(Operator::Unary(UnaryOp::Not));
                let t = self
                    .apply(
                        Label::Operator(Operator::Unary(UnaryOp::Not)),
                        &sig,
                        vec![Some(Arg::of(c.t))],
                        true,
                        span,
                    )
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
                let and = op == BinaryOp::And;
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
                let and = op == BinaryOp::And;
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
                let sig = op_sig(Operator::Binary(BinaryOp::And));
                let t = self
                    .apply_demanding(
                        Label::Operator(Operator::Binary(op)),
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
                let and = op == BinaryOp::And;
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
                let sig = op_sig(Operator::Binary(BinaryOp::And));
                let t = self
                    .apply_demanding(
                        Label::Operator(Operator::Binary(op)),
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
                    parts: parts(e, self.t.text, &self.kept_ops),
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
                let param = match self.t.res.uses.get(&s.span) {
                    Some(Ref::Bound(ids)) => self.port_params.contains(&ids[0]),
                    _ => false,
                };
                if param || self.lines_out.contains(port) {
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
            Frame::CallAlso {
                id,
                from,
                sig,
                positional,
                named,
                span,
            } => {
                let out = m.take_ty();
                if let Some(o) = self.whence.get(&id).map(|o| o.span) {
                    // Only the call's own refusal, not an error inside an argument, says
                    // which argument is in a part a parameter's type takes away.
                    let refused = (self.errors.get(from..))
                        .is_some_and(|es| es.iter().any(|e| e.span == span));
                    self.also_notes(from, |ck| {
                        built(1);
                        let mut notes = vec![Note {
                            span: o,
                            text: ck.declared_step(id, &sig),
                        }];
                        ck.declared_emptied(id, &mut notes);
                        if refused {
                            ck.subtracted_args(id, positional, named, &mut notes);
                        }
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
                    _ => self.callee_code(callee, span).unwrap_or(CALLED_HERE).into(),
                };
                if let (ExprKind::Name(w), Some(Ref::Prelude(_))) =
                    (&callee.kind, self.t.res.uses.get(&callee.span))
                {
                    if let Some(p) = bit_prim(w) {
                        return self.bits(m, w, p, None, positional, named, curry, span);
                    }
                    let call = PreludeCall {
                        w,
                        receiver: None,
                        positional,
                        named,
                        curry,
                        span,
                    };
                    return self.prelude_call(m, &f, call);
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
                _ => items.push(s.bare()),
            }
        }
        // A cycle is a recursion, rejected until layer L6 (`recursion`). Every other statement
        // is still checked, one that uses a statement of a cycle among them too: stopping at the
        // cycle left the scope's other definitions with no signature and their errors
        // unreported. Each name the cycle defines has no value, as a rejected expression gives
        // (`Frame::Fail`), so a use of it adds no error of its own.
        let (order, cycles) = self.t.order_around_cycles(&items);
        for (report, cycle) in self
            .t
            .cycle_reports(&items, &cycles)
            .into_iter()
            .zip(&cycles)
        {
            match report.row {
                Some(row) => self.rejects_with(row, report.span, report.message, report.notes),
                None => self.error_with(report.span, report.message, report.notes),
            }
            for &k in cycle {
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
        let (result, _) = self.apply(Label::Text(&what), &s.sig, args, false, input.span);
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
            | StmtKind::Local(_) => {
                unreachable!(
                    "name resolution rejects every struct, type, method, import and local definition before the checker reads the program"
                )
            }
            StmtKind::Annotated { .. } => {
                unreachable!("a scope holds the declaration of an annotated one, `Stmt::bare`")
            }
            StmtKind::IndexedDef(_)
            | StmtKind::Initial(_)
            | StmtKind::While(_)
            | StmtKind::Until(_)
            | StmtKind::Expr(_) => unreachable!(
                "name resolution rejects every `initial` statement, indexed definition, while, until and expression statement before the checker reads the program"
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
    fn bind(&mut self, s: &'a Stmt, mut v: Ty, before: usize) {
        let StmtKind::Bind { targets, value, .. } = &s.kind else {
            unreachable!("a binding")
        };
        // Each target is bound to its component where the value is a tuple display of
        // as many components, `a, b = (0.5, 1)`; `_` names none.
        let name = |t: &'a Target| match t {
            Target::Name(n, _) => n.as_str(),
            Target::Wild => "_",
        };
        let text = self.t.text;
        let parts = || match (&targets[..], &value.kind) {
            ([t], _) => unfixed_parts(value, name(t), true, text),
            (ts, ExprKind::Tuple(items)) if items.len() == ts.len() => (ts.iter().zip(items))
                .flat_map(|(t, x)| unfixed_parts(x, name(t), false, text))
                .collect(),
            _ => Vec::new(),
        };
        let what = match &targets[..] {
            [Target::Name(n, _)] => format!("the value of `{n}`"),
            [_] => "the value".to_string(),
            ts => format!(
                "the value bound to `{}`",
                ts.iter().map(name).collect::<Vec<_>>().join(", ")
            ),
        };
        if self.level == 0 {
            self.drop_met(before);
            let mut found = parts();
            // The literals the value ends in through a branch, a block, an index or a call,
            // for every form of the targets; a literal in a called body may stand before the
            // binding in the text, and the parts are put back in the order of the text.
            let tails = self.unfixed_tails(value, &v);
            if !tails.is_empty() {
                found.extend(tails);
                found.sort_by_key(|(p, _, _)| p.start);
            }
            self.rejects_unfixed(before, found, &what);
        } else {
            let names: Vec<&str> = targets.iter().map(name).collect();
            let bound = format!("the binding of `{}`", names.join(", "));
            let (rejected, binds) = self.fix_bound(&v, value.span, &bound);
            if !rejected.is_empty() {
                self.reject_bound(before, rejected, parts(), &what);
            }
            // The name reads as the carrier it takes, as one outside every function does: a
            // use of it then meets an `int`, not a class it could narrow.
            v = v.replace_outside(&binds);
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

    /// Fixes, at `span`, where a name in a body is bound to the value `v`, the carrier of each
    /// class of literals alone that `v` holds outside the functions it holds: a name has one
    /// value and one type, fixed where it is bound, and no read of it gives it a carrier
    /// (QUESTIONS A63, author, 2026-11-13; DESIGN.md sec:diagnostics). So with `b = 2^62`, `b`
    /// is an `int`, and `c = b + 0.5f64` is rejected at the `+`, as it is outside every
    /// function; with `q = 1.5 + 1`, `q` is rejected at its binding. The carrier is the one
    /// [`Ck::lits_take`] gives when the function ends, so a class that no later use narrows
    /// resolves as it did. `what` names the binding in the reason the class records. Returns
    /// the literals rejected, each with the carriers left, and each class variable of `v` whose
    /// class is left one carrier, bound to it, so the name reads as that carrier. A rejected
    /// class takes `f64` where it may, else the first carrier left, as a binding outside
    /// every function is read after its rejection, so it is not rejected a second time when
    /// it resolves. Left as they are: a class of a parameter (`binder`) or merged with one
    /// (not `generic`), which a call gives its carrier, and one with no literal that fixes a
    /// carrier (as [`Ck::resolve`] reads it).
    // Complexity tradeoff: the classes are found by a walk of `v` outside its functions that
    // enters each row and shape once in the whole body ([`Ty::vars_outside`] with the
    // function's own [`Vars`], `Ck::bound`), so the walks of a body's n bindings cost
    // O(size of the types they make) in all, plus the variables at the top of each value,
    // read again at each binding, O(width of `v`). A fresh walk at each binding re-enters
    // the shapes an earlier binding shares: `t1 = #a(t0, t0); t2 = #a(t1, t1); …` costs
    // O(n²) (ATOM-nested-sq). A variable met at an earlier binding is not examined again
    // unless it is at the top of `v`: its class was fixed there, or left to a call or to the
    // function's end, and a later binding that adds to it holds it, or a variable merged
    // with it, at the top or in a shape it makes. Each class costs a find, O(α(N)), and at
    // most three passes over its l literals ([`Ck::lits_take`]), O(l); the name's type is
    // rebuilt with the carriers in place, O(size of `v` outside the shapes holding no
    // variable bound). A class of literals alone reaches one binding: the name then reads
    // as its carrier, so in `b1 = b0 + 1; b2 = b1 + 1; …` each `+` meets an `int` and makes
    // no class, and each literal is passed over a constant number of times in all. The
    // method before this change waited for the function's end and resolved each class once,
    // O(l), but let a later use give the name its carrier, which A63 forbids.
    fn fix_bound(&mut self, v: &Ty, span: Span, what: &str) -> (Vec<(Lit, Vec<Carrier>)>, Binds) {
        let level = self.level;
        if self.bound.len() <= level {
            self.bound.resize_with(level + 1, Vars::default);
        }
        let met = self.bound[level].order.len();
        v.vars_outside(&mut self.bound[level]);
        let found: Vec<Arc<str>> = (self.bound[level].order[met..].iter())
            .chain(v.vars.iter())
            .cloned()
            .collect();
        let numbers = [Carrier::Int, Carrier::F64, Carrier::Rat, Carrier::F32]
            .iter()
            .fold(0, |m, c| m | c.bit());
        // The carrier each class takes, by its root, or none where it is left as it is.
        let mut fixed: HashMap<usize, Option<Carrier>> = HashMap::new();
        let mut rejected = Vec::new();
        let mut binds = Vec::new();
        for x in found {
            let Some(r) = class_id(&x).filter(|&k| k < self.classes.len()) else {
                continue;
            };
            let r = self.find(r);
            let takes = match fixed.get(&r) {
                Some(&t) => t,
                None => {
                    let t = self.fix_class(r, span, what, &mut rejected, numbers);
                    fixed.insert(r, t);
                    t
                }
            };
            if let Some(c) = takes {
                binds.push((x, Ty::carrier(c)));
            }
        }
        (rejected, binds.into_iter().collect())
    }

    /// The carrier the class `r` takes where a name is bound to it at `span`
    /// ([`Self::fix_bound`]), with the literal pushed to `rejected` where nothing gives it
    /// one, if `r` is a class of literals alone with a literal that fixes a carrier (of the
    /// carriers `numbers`), and one carrier is left.
    fn fix_class(
        &mut self,
        r: usize,
        span: Span,
        what: &str,
        rejected: &mut Vec<(Lit, Vec<Carrier>)>,
        numbers: u8,
    ) -> Option<Carrier> {
        let c = &self.classes[r];
        let fixes = c.mask & numbers != 0
            && (c.lits.iter()).any(|(l, follows)| !follows && (!l.generic || l.witness));
        if c.resolved.is_some() || !c.generic || c.binder.is_some() || !fixes {
            return None;
        }
        let takes = match self.lits_take(r) {
            LitsTake::Int => Carrier::Int,
            LitsTake::F64 => Carrier::F64,
            LitsTake::Left => {
                let mask = self.classes[r].mask;
                return (mask & OTHER == 0 && mask.count_ones() == 1)
                    .then(|| Carrier::of_mask(mask).next().expect("one carrier"));
            }
            LitsTake::Rejected(l, left) => {
                let c = match left.contains(&Carrier::F64) {
                    true => Carrier::F64,
                    false => left[0],
                };
                rejected.push((l, left));
                c
            }
        };
        let fixed = self.restrict_asking(r, takes.bit(), what, span, false);
        debug_assert!(fixed, "a class may take the carrier its literals take");
        Some(takes)
    }

    /// Rejects, at a binding in a body, the literals `rejected` that nothing gives a carrier,
    /// each with the carriers left ([`Self::fix_bound`]). One in a part of the value that
    /// [`unfixed_parts`] finds, of `parts` in the order of the text, is rejected as that part
    /// of a binding outside every function is ([`Self::rejects_unfixed`]), with the fixes
    /// written as the binding, `q = 1.5f64 + 1;    q is 2.5`; another, which the value reaches
    /// through a branch or a call, as [`Ck::resolve`] rejects it. The errors after the first
    /// `before` are those of the value's check; `what` names the value.
    // Complexity tradeoff: the parts lie apart in the order of the text, so each literal finds
    // its part by binary search, O(r log p) for r literals and p parts; the naive test of each
    // literal against each part costs O(r p), the square of the width of a tuple display.
    fn reject_bound(
        &mut self,
        before: usize,
        rejected: Vec<(Lit, Vec<Carrier>)>,
        parts: Vec<(Span, Span, Msg)>,
        what: &str,
    ) {
        let mut taken = vec![false; parts.len()];
        let mut alone = Vec::new();
        for (l, left) in rejected {
            let k = parts.partition_point(|(p, _, _)| p.start <= l.site.start);
            match k.checked_sub(1) {
                Some(k) if l.site.end <= parts[k].0.end => taken[k] = true,
                _ => alone.push((l, left)),
            }
        }
        let parts = (parts.into_iter().zip(taken))
            .filter_map(|(p, t)| t.then_some(p))
            .collect();
        self.rejects_unfixed(before, parts, what);
        for (l, left) in alone {
            let notes = self.derive(&[l.site]);
            let m = unfixed(&l, &left);
            self.reject(Some(Row::UnfixedDecimal), l.site, m, notes);
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
        let n = parts.len();
        let head = format!(
            "{n} parts of {what} are literals that nothing here gives a carrier, and Zed does \
             not choose one for them; the steps below give each one"
        );
        let (m, steps) = grouped(head, parts);
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
            let mut m = unfixed(&l, &cs);
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
                    if deep && l.bare && is_decimal(&l.value) && (payload || !in_call || alone()) {
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
                            if l.bare && is_decimal(&l.value) {
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
        // A port has no origin for a derivation to show: the builder rejects every read of an
        // output port, as `m.stdout` written as a value, and the one use it lets through, a port
        // passed whole to a parameter that is an output port ([`super::ports`]), is no read.
        if let Some(ports) = f.ports() {
            for p in ports {
                let id = self.id(p.span, &p.name);
                if matches!(&p.ty.kind, TypeKind::Name(n) if n == "Lines") {
                    self.lines_out.insert(p.name.clone());
                }
                // Its declared type, `Lines`, which a parameter it is passed to declares.
                self.env.insert(id, denoted(&p.ty));
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
                    self.defaults.insert(d.span, p.name.as_str().into());
                    if !self.flow(k, &dt, &what, d.span, d.span) {
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
                if *op == UnaryOp::Neg && zero_rat(a) {
                    self.spells(&Value::rat(Rat::int(0.into())), e.span);
                }
                m.k(Frame::Unary(*op, e.span));
                m.job(Job::Arg(a, Want::default()));
            }
            ExprKind::Binary(op @ (BinaryOp::And | BinaryOp::Or), a, b) => {
                m.k(Frame::Logic1 {
                    op: *op,
                    b,
                    span: e.span,
                });
                m.job(Job::Cond(a));
            }
            ExprKind::Binary(op, a, b) => {
                m.k(Frame::Bin1 {
                    op: *op,
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
                            let m = unfixed(&l, &[Carrier::F64, Carrier::Rat]);
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
            ExprKind::Unary(UnaryOp::Not, a) => {
                m.k(Frame::CondNot(e.span));
                m.job(Job::Cond(a));
            }
            ExprKind::Binary(op @ (BinaryOp::And | BinaryOp::Or), a, b) => {
                m.k(Frame::CondAnd1 {
                    op: *op,
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
        let (ls, rat) = literals_alone(e, None)?;
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
    pub(super) fn branch_joins(&mut self, k: usize, b: &Branch, what: &str, span: Span) -> bool {
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
    /// ([`folded`]), as `1r + 1 / 0`, whose `/` always fails: its rejection stands. At `rat`
    /// each `^` in it takes an `int` exponent, so it takes `rat` only where each exponent is an
    /// integer literal, which keeps the carrier `int`: `(3/2)^-2 * 1r` is `4/9`.
    ///
    /// Complexity tradeoff: the naive test walks each operand to see whether it holds literals
    /// alone, which costs the depth of the operation at each operator, the square of the
    /// depth over a nest of them. Each operation is recorded as it ends, from its two operands'
    /// entries, so the test is one lookup, and the literals of an operation are walked once,
    /// when it takes its carrier: after that the operand is of that carrier, and the operation
    /// around it holds a value of a carrier, not literals alone. The walk that folds an
    /// operation holding a `/` or a `^` costs its size again, once.
    fn lit_op_meets(&mut self, op: BinaryOp, x: &mut Arg<'a>, y: &mut Arg<'a>, span: Span) {
        let op_of = |a: &Arg| a.expr.is_some_and(|e| self.lit_ops.contains(&e.span));
        let bare = |a: &Arg| a.lit.as_ref().is_some_and(|l| l.bare);
        let (ox, oy) = (op_of(x), op_of(y));
        if (ox || bare(x)) && (oy || bare(y)) {
            if matches!(
                op,
                BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Pow
            ) {
                // Its value has no type until it meets a carrier where it holds a `/` or a
                // decimal ([`Ck::lit_open`]): one lookup per operand.
                let open = |a: &Arg| {
                    a.expr.is_some_and(|e| self.lit_open.contains(&e.span))
                        || (a.lit.as_ref()).is_some_and(|l| l.bare && is_decimal(&l.value))
                };
                let opened = op == BinaryOp::Div || open(x) || open(y);
                // A trial records nothing here, as nothing undoes it, and one whose operation
                // has no type until its value meets a carrier fails, since it does not see
                // where the value goes ([`Self::tried`]).
                if self.trying {
                    self.opened |= opened;
                    return;
                }
                self.lit_ops.insert(span);
                if opened {
                    self.lit_open.insert(span);
                    for e in [x.expr, y.expr].into_iter().flatten() {
                        self.lit_open_within(e);
                    }
                }
            }
            return;
        }
        if op == BinaryOp::Pow {
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
                ExprKind::Unary(UnaryOp::Neg, a) => todo.push(a),
                _ => {}
            }
        }
    }

    /// Each literal of `e`, an operation on bare literals alone ([`Ck::lit_ops`]), adopting
    /// `c`, each of its operations of type `c` where a derivation names it ([`Ck::seen`],
    /// [`Ck::lit_open`]), and the errors its operations wrote as they were walked dropped
    /// ([`Ck::lit_wrote`]); at `rat` the exponent of each `^`, an integer literal, adopts `int`,
    /// which `^` takes there. `false`, with nothing changed, where `e` holds a `/` or a `^` and
    /// its value at `c` is no value of `c` ([`folded`]), as `1 / 0` at `rat`, or `(3/2)^(1 + 1)`
    /// at `rat`, whose exponent would be a `rat`: the rejection of the operation stands. It
    /// costs the size of `e`, twice where it holds a `/` or a `^`; in a repair's trial
    /// ([`Self::tried`]), which changes nothing that lasts, what it finds is read from
    /// [`Self::lit_fit`] instead.
    fn lit_takes(&mut self, e: &Expr, c: Carrier) -> bool {
        if self.trying {
            let (takes, refused) = self.lit_fit(e, c);
            // A literal that is not exactly a `c` is rejected as below, which fails the trial.
            if takes && let Some(l) = refused {
                self.adopt_to(&l, c);
            }
            return takes;
        }
        let mut nodes = Vec::new();
        let (mut div, mut pow) = (false, false);
        let mut todo = vec![(e, c)];
        while let Some((e, at)) = todo.pop() {
            nodes.push((e, at));
            if literal(e, None).is_some() {
                continue;
            }
            match &e.kind {
                ExprKind::Binary(op, a, b) => {
                    div |= *op == BinaryOp::Div;
                    pow |= *op == BinaryOp::Pow;
                    // At `rat` a `^` takes an `int` exponent, which keeps its carrier ([`folded`]).
                    let k = if *op == BinaryOp::Pow && c == Carrier::Rat {
                        Carrier::Int
                    } else {
                        at
                    };
                    todo.extend([(&**b, k), (&**a, at)]);
                }
                ExprKind::Unary(UnaryOp::Neg, a) => todo.push((a, at)),
                _ => {}
            }
        }
        if (div || pow) && !self.lit_fit(e, c).0 {
            return false;
        }
        let live = !self.trying && self.replaying == 0;
        for (e, at) in nodes {
            if let Some(l) = literal(e, self.t.text) {
                match at == c {
                    true => _ = self.adopt_to(&l, c),
                    // An exponent keeps its own carrier, whatever the walk gave it before.
                    false => self.put(Undo::Adopt(l.span, None)),
                }
                continue;
            }
            // Each operation in it is of the carrier now, which a derivation names, and not
            // the type the walk found before it met one.
            // A trial ([`Self::tried`]) changes neither, as nothing undoes it.
            if self.trying {
                continue;
            }
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

    /// What [`Self::lit_takes`] finds of `e`, an operation on bare literals alone, taking `c`:
    /// whether it takes it, and the first of its literals that is not exactly a `c`, which
    /// [`Self::adopt_to`] rejects. Both are read off `e` and `c` alone, so what each operation
    /// in `e` is at `c` is kept ([`Ck::lit_fits`]), and the walk stops at an operation kept
    /// already.
    ///
    /// Complexity tradeoff: the naive way, the walk and the fold of all of `e` in each trial,
    /// costs the size of `e` per trial. Over a nest of `n` operations, each rejected as it is
    /// walked with a fix whose trial gives the operation below it a carrier, as in
    /// `((1 + 1) / 1 + 1) / 1`, that is O(n²) (test
    /// `l01_26a_generic_literals::scaling::an_argument_of_divisions_of_literals_nested_deep_takes_its_carrier_in_linear_time`).
    /// Kept by operation and carrier, each operation is read once per carrier, at three
    /// carriers at most: one kernel operation on its operands' values, besides copying them.
    fn lit_fit(&mut self, e: &Expr, c: Carrier) -> (bool, Option<Lit>) {
        enum Step<'e> {
            Visit(&'e Expr),
            // The exponent of a `^` at `rat`, read at `int` ([`folded`]).
            Exponent(&'e Expr),
            Done(&'e Expr, Option<Prim>, usize, bool, bool),
        }
        let mut todo = vec![Step::Visit(e)];
        let mut fits: Vec<LitFit> = Vec::new();
        while let Some(step) = todo.pop() {
            match step {
                Step::Visit(x) => {
                    if let Some(f) = self.lit_fits.get(&(x.span, c)) {
                        fits.push(f.clone());
                        continue;
                    }
                    if let Some(l) = literal(x, None) {
                        let refused = literal(x, self.t.text).filter(|l| adopt(l, c).is_err());
                        fits.push(LitFit {
                            value: lit_value(&l, c).map(RatFact::Value),
                            div: false,
                            pow: false,
                            refused,
                        });
                        continue;
                    }
                    match &x.kind {
                        ExprKind::Binary(BinaryOp::Pow, a, b) if c == Carrier::Rat => {
                            todo.extend([
                                Step::Done(x, Some(Prim::Pow), 2, false, true),
                                Step::Exponent(b),
                                Step::Visit(a),
                            ])
                        }
                        ExprKind::Binary(op, a, b) => todo.extend([
                            Step::Done(
                                x,
                                binary_prim(*op),
                                2,
                                *op == BinaryOp::Div,
                                *op == BinaryOp::Pow,
                            ),
                            Step::Visit(b),
                            Step::Visit(a),
                        ]),
                        ExprKind::Unary(UnaryOp::Neg, a) => todo.extend([
                            Step::Done(x, Some(Prim::Neg), 1, false, false),
                            Step::Visit(a),
                        ]),
                        // A `rat` literal, `2r`, is a value of `rat` alone ([`folded`]).
                        kind => fits.push(LitFit {
                            value: match kind {
                                ExprKind::Rat(d) if c == Carrier::Rat => Rat::decimal(d)
                                    .ok()
                                    .flatten()
                                    .map(Value::rat)
                                    .map(RatFact::Value),
                                _ => None,
                            },
                            div: false,
                            pow: false,
                            refused: None,
                        }),
                    }
                }
                Step::Exponent(b) => fits.push(LitFit {
                    value: rat_exponent(b).map(RatFact::Value),
                    div: false,
                    pow: false,
                    refused: None,
                }),
                Step::Done(x, p, n, div, pow) => {
                    let parts = fits.split_off(fits.len() - n);
                    // At `rat` a power is not computed ([`rat_step`]); at `int` and `f64` the
                    // operands' values give the kernel's.
                    let value = match (p, c) {
                        (Some(p), Carrier::Rat) => {
                            let y = parts.get(1).and_then(|f| f.value.clone());
                            rat_step(p, parts[0].value.clone(), y)
                        }
                        (Some(p), _) => (parts.iter())
                            .map(|f| match &f.value {
                                Some(RatFact::Value(v)) => Some(v.clone()),
                                _ => None,
                            })
                            .collect::<Option<Vec<Value>>>()
                            .and_then(|vs| prim_folded(p, vs))
                            .map(RatFact::Value),
                        (None, _) => None,
                    };
                    let fit = LitFit {
                        value,
                        div: div || parts.iter().any(|f| f.div),
                        pow: pow || parts.iter().any(|f| f.pow),
                        refused: parts.into_iter().find_map(|f| f.refused),
                    };
                    self.lit_fits.insert((x.span, c), fit.clone());
                    fits.push(fit);
                }
            }
        }
        let f = fits.pop().expect("one fit for `e`");
        let takes = !((f.div || f.pow) && f.value.is_none());
        (takes, f.refused)
    }

    /// At the top level, each argument of `args` that is an operation on bare literals alone
    /// ([`Ck::lit_ops`]), at a parameter that every arrow of `sig` declares of one numeric
    /// carrier other than `int`, takes that carrier, as a literal does at a declared type
    /// (DESIGN.md sec:domains: a use fixes a literal's carrier "at a declared type, that
    /// type's", and "an operation on literals alone ... is a literal too, and takes the
    /// carrier of what it meets"): with `f(x: f64)`, in `f(x: 1 / 2)` the `/` is an `f64`
    /// and `x` is `0.5`, and the rejection the `/` wrote as it was walked is dropped. At a
    /// parameter the arrows declare of float formats alone, `f64` among them, it takes `f64`,
    /// as a bare literal does there ([`floats_take_f64`]): `sqrt(-0.0 - 1e-300)` is the `sqrt`
    /// of an `f64`. An operator's arrows differ in their carriers, so this leaves its operands
    /// to [`Ck::lit_op_meets`]; a generic parameter gives no carrier, so `inc(x: 1 / 2)` is
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
            let at: Option<Vec<Carrier>> = (sig.arrows.iter())
                .map(|arrow| arrow.params.get(i).and_then(|p| p.numeric_carrier()))
                .collect();
            let Some(at) = at else {
                continue;
            };
            let c = match at[..] {
                [c, ..] if c != Carrier::Int && at.iter().all(|&d| d == c) => c,
                _ if floats_take_f64(&at) => Carrier::F64,
                _ => continue,
            };
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
    /// second written `b`, recorded as the construct being checked ([`Self::as_written`]).
    fn binary_end(&mut self, op: BinaryOp, x: Arg<'a>, y: Arg<'a>, b: &'a Expr, span: Span) -> Ty {
        self.as_written(Construct::Binary(op, b), vec![Some(x), Some(y)], span)
    }

    /// [`Self::binary_end`] checked.
    fn binary_op(
        &mut self,
        op: BinaryOp,
        mut x: Arg<'a>,
        mut y: Arg<'a>,
        b: &'a Expr,
        span: Span,
    ) -> Ty {
        // An operand that is a literal without a suffix is generic: it takes the carrier of the
        // other operand, at run time where that is a type variable (step L1.26a). Under `==`
        // it follows as any literal.
        if !matches!(op, BinaryOp::Eq | BinaryOp::Ne) {
            for l in [&mut x.lit, &mut y.lit].into_iter().flatten() {
                l.generic = l.bare;
            }
            // An integer exponent of `^` on a base whose value the text gives, or gives as no
            // zero, does not restrict the base's carrier: `^` takes (rat, int), so in
            // `(3/2)^-2` the `-2` leaves the base free to be a `rat` ([`Lit::exponent`]). A base
            // of unknown value, as a parameter in `p(positional b) = b ^ -1`, keeps the exponent
            // in its class: at `rat` it could be `0r` and give `#divByZero`, which the class's
            // result would then carry at every carrier. O(1): what the text gives of the base
            // is a lookup ([`Self::rat_fact`]).
            if op == BinaryOp::Pow
                && x.expr.is_some_and(|a| {
                    self.rat_fact(a)
                        .is_some_and(|f| matches!(f, RatFact::Value(_)) || f.nonzero())
                })
                && let Some(l) = &mut y.lit
                && l.bare
                && lit_carrier(&l.value) == Carrier::Int
            {
                l.exponent = true;
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
                BinaryOp::Add
                    | BinaryOp::Sub
                    | BinaryOp::Mul
                    | BinaryOp::Div
                    | BinaryOp::Pow
                    | BinaryOp::Lt
                    | BinaryOp::Le
                    | BinaryOp::Gt
                    | BinaryOp::Ge
                    | BinaryOp::Eq
                    | BinaryOp::Ne
            )
        {
            self.lit_op_meets(op, &mut x, &mut y, span);
        }
        match op {
            BinaryOp::Eq | BinaryOp::Ne => {
                if self.level == 0 {
                    self.lit_pairs(&mut x, &mut y);
                }
                // A call or an `if` that lists values compared with a value of one carrier, `f64`,
                // `f32` or `rat`, is read at that carrier, as at an arithmetic operator: `x == g(c)`
                // with `x: f64` and `g` of type `(bool) -> 1 | 2` compares two `f64`s
                // ([`read_ty`]; L1.26a). One read of the listed values. Where the parts the
                // two operands hold whole are of one such carrier, both are read at it, as at
                // an arithmetic operator ([`Self::fewest`]): `g(c, x) == g(d, x)` with `g` of
                // type `(bool, f64) -> 1 | f64` compares two `f64`s.
                // The parts are found only where an operand is read, as in [`Self::fewest`].
                let whole: BTreeSet<Carrier> = if [&x, &y]
                    .into_iter()
                    .any(|a| self.readable(a) && lists_a_number(&a.ty))
                {
                    [&x, &y]
                        .into_iter()
                        .filter(|a| a.lit.is_none() && a.branches.is_none() && a.parts.is_none())
                        .flat_map(|a| whole_carriers(&a.ty))
                        .collect()
                } else {
                    BTreeSet::new()
                };
                let one = match whole.iter().collect::<Vec<_>>()[..] {
                    [&c @ (Carrier::F64 | Carrier::F32 | Carrier::Rat)] => Some(Ty::carrier(c)),
                    _ => None,
                };
                for flip in [false, true] {
                    let (a, other) = match flip {
                        false => (&x, &y),
                        true => (&y, &x),
                    };
                    match self.read_arg(a, one.as_ref().unwrap_or(&other.ty)) {
                        Some(Ok((t, c, ads))) => {
                            for (s, v) in ads {
                                self.put(Undo::Adopt(s, Some(v)));
                            }
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
                // Whether each operand's cast to `f64` is exact, for the repairs of a rejected
                // comparison ([`Comparison::exact`]). Cost: one read of what the text shows of an
                // operand ([`Self::exact_in_f64`]), only where it has an int part and the other
                // side may be an `f64` or is a decimal literal, the one case a cast to `f64`
                // repairs; `n == 1` or `n == m` of ints reads nothing.
                let mut exact = [false; 2];
                for (s, (a, b)) in [(&x, &y), (&y, &x)].into_iter().enumerate() {
                    let f64_side = !(&b.ty.set & &KType::f64()).is_empty()
                        || b.lit
                            .as_ref()
                            .is_some_and(|l| matches!(l.value, Value::Float(_)));
                    exact[s] = f64_side && self.exact_in_f64(a);
                }
                self.comparing = Some(Comparison {
                    op,
                    ats: [x.at, y.at],
                    exprs: [x.expr, y.expr],
                    exact,
                    span,
                    from,
                });
                self.equal(&x, &y);
                self.comparing = None;
                for (l, v, left) in [(&x, &y, true), (&y, &x, false)] {
                    if let (Some(lit), None) = (&l.lit, &v.lit)
                        && lit.bare
                    {
                        if !self.trying {
                            self.eq_sides.insert(lit.site, (op, v.at, left));
                        }
                        if self.class_of_ty(&v.ty).is_none() && holds_no_number(&[&v.ty]) {
                            self.never_equal(lit, &v.ty);
                        }
                    }
                }
                Ty::carrier(Carrier::Bool)
            }
            BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => {
                self.compare(op, x, y, span)
            }
            BinaryOp::And | BinaryOp::Or => {
                unreachable!("`&&` and `||` are walked as conditions, by `Frame::Logic1`")
            }
            BinaryOp::Add
            | BinaryOp::Sub
            | BinaryOp::Concat
            | BinaryOp::Mul
            | BinaryOp::Div
            | BinaryOp::IntDiv
            | BinaryOp::Mod
            | BinaryOp::Pow => {
                let from = self.errors.len();
                // A divisor whose type holds no zero cannot fail with `#divByZero`, nor can an
                // int divisor the tests it is under keep from zero, as `d` in the arm of
                // `if d != 0` (DESIGN.md L1.26, the interval of a name in an arm, L1.24). The
                // tests are read only where the type holds a zero.
                //
                // Cost (NARROW-ne-divisor). The arm's scope already holds `d` without 0
                // (`Scope::assume` takes the complement of a literal for a direct test), so
                // nothing in `zedc-preimage` changes, against the plan row's pointer there.
                // Each division reads that scope once: one settle of the arm's scope and one
                // forward evaluation of the divisor's term, as `total_power` below pays for
                // an exponent; outside every arm `ints_here` returns at once. A read per arm
                // opened above the division, the naive way to ask each test, costs O(n) a
                // division and O(n^2) for n chained tests. Measured
                // (`l01_26_type_resolution::divisors::chained_tests_and_divisions_check_in_linear_time`,
                // n = 100 and 800 chained `if d != 0` arms each dividing by `d`): 8.0 times
                // the work and 8.0 times the bytes; the per-arm read, 38.2 times the bytes.
                //
                // A `rat` divisor is read the same way (NARROW-ne-rat-divisor), by the type its
                // product has in the arm's scope: `r != 0r` and the `else` of `r == 0r` take
                // `0r` out of it as `d != 0` takes 0 out of the interval, and a comparison with
                // a literal that `0r` fails takes it out too (`Scope::atom_names`); a literal
                // with no suffix is read at the carrier it adopts beside `r` (`Ck::term`).
                // The same one read per division, so the cost above holds; measured by
                // `chained_rat_tests_and_divisions_check_in_linear_time`.
                let divides = matches!(op, BinaryOp::Div | BinaryOp::IntDiv | BinaryOp::Mod);
                let rat_zero = Value::rat(Rat::int(0.into()));
                let carried_only = |c| y.ty.without_atoms().subtype(&Ty::carrier(c));
                let int_divisor = carried_only(Carrier::Int);
                let mut nonzero = divides
                    && ((!y.ty.contains(&Value::Int(0)) && !y.ty.contains(&rat_zero))
                        || (int_divisor && !self.ints_here(b).0.contains(0))
                        || (carried_only(Carrier::Rat) && !self.may_be_here(b, &rat_zero)));
                // An int divisor whose range holds 0 under the tests: whether a state reaches
                // it at 0 at all, the written constraints evaluated at the integer roots of
                // the divisor (QUESTIONS A81, `Scope::zero_reached`). Outside every test, or
                // for a divisor the text gives a value, the range is the answer. Complexity
                // tradeoff: evaluating the constraints at each member of the range costs one
                // evaluation per member (10^9 for `0..=1000000000`); at the roots, after Cucker,
                // Koiran and Smale 1999, it costs one per root, and the roots of `t` terms of
                // `B` bits cost O(t^3) evaluations of the divisor, whatever its degree.
                if divides
                    && !nonzero
                    && int_divisor
                    && self.arms.here() != 0
                    && self.known(b).value.is_none()
                {
                    let (reached, failures) = self.zero_reached_here(b);
                    match failures.into_iter().next() {
                        Some(f) => self.root_constraint_fails(b, span, &f),
                        None => nonzero = !reached,
                    }
                }
                // A `rat` power fails only for `0r` to a negative power.
                let total_power = op == BinaryOp::Pow
                    && (!x.ty.contains(&rat_zero)
                        || self.ints_here(b).0.is_subset(&at_least_zero()));
                let carried = [&x.ty, &y.ty]
                    .iter()
                    .any(|t| t.atoms().contains(&Value::atom("divByZero")));
                if op == BinaryOp::Pow {
                    self.exponent(&x, &y, b, span);
                }
                let zero = if divides {
                    self.zero_divisor(op, &x, &y, b)
                } else {
                    None
                };
                // The dividend as the program writes it, for the repair.
                let dividend = match (&x.lit, x.expr.map(|e| &e.kind)) {
                    (Some(l), _) => l.written().to_string(),
                    (None, Some(ExprKind::Name(n))) => n.clone(),
                    _ => "…".to_string(),
                };
                let mut sig = op_sig(Operator::Binary(op));
                // A decimal literal base with no suffix meets an `int` exponent at `rat`, its
                // one carrier there (DESIGN.md L1.17, `0.5 ^ n`): the arrow `f32 ^ int` is for
                // a base already an `f32`, and the literal does not take `f32` through it.
                if op == BinaryOp::Pow
                    && x.lit
                        .as_ref()
                        .is_some_and(|l| l.bare && is_decimal(&l.value))
                {
                    let mixed = [Ty::carrier(Carrier::F32), Ty::carrier(Carrier::Int)];
                    sig.arrows.retain(|a| a.params != mixed);
                }
                let a = x.expr;
                let r = self.apply(
                    Label::Operator(Operator::Binary(op)),
                    &sig,
                    vec![Some(x), Some(y)],
                    true,
                    span,
                );
                // An operation at `rat` on `rat` literals and such operations has the value
                // the kernel gives it: where that is a number, it fails with no
                // `#divByZero`, as `1r / (2r/3r)` and `(2r/3r)^-2` do not.
                let folds = a.is_some_and(|a| self.rat_folded(op, a, b, span, &r.0));
                if let Some(why) = zero
                    && r.0.atoms().contains(&Value::atom("divByZero"))
                {
                    self.divides_by_zero(op, why, &dividend, b, span);
                }
                self.lit_wrote(span, from);
                if op == BinaryOp::Mul {
                    // `*` and `/` take the same (f64, f64) and (rat, rat), and only `*` takes
                    // (int, int): `/` is defined where the product holds no `int`.
                    let quotient = !r.0.set.is_empty() && (&r.0.set & &KType::int()).is_empty();
                    if !self.trying {
                        *self.info.quotients.entry(span).or_insert(quotient) &= quotient;
                    }
                }
                match (nonzero || total_power || folds) && !carried {
                    true => r.0.diff(&Ty::set(KType::atom("divByZero"))),
                    false => r.0,
                }
            }
        }
    }

    /// Whether the operation `op` at `span` on `a` and `b`, of type `t`, is at `rat`, or in a
    /// class of literals that may resolve to `rat`, and the text shows it gives no `#divByZero`
    /// there. What the text gives of an operand ([`Self::rat_fact`]) is its value where it is a
    /// `rat` literal, a bare literal at `rat` or a sum, difference, product or quotient of such
    /// values, and that it is no zero where it is a power of a base that is no zero; a `^`'s
    /// exponent is known where it is an `int` literal. The operation's own fact is kept
    /// ([`Ck::rat_folds`]): a value by the kernel's one evaluator as A54 permits
    /// ([`prim_folded`]), unless the operation gives an atom, as `1r / (1r - 1r)` does.
    ///
    /// A power's value is not computed, except at a base of `0`, `1` or `-1`, which the kernel
    /// reads from the exponent's sign alone: `3^e` with `e` defined as `200000` would build a
    /// value the size of `e`, which the text does not show (`a_constant_no_bit_word_reads_is_
    /// not_folded`). A power of a base that is no zero is no zero, which is all a later `/` or
    /// `^` needs to rule `#divByZero` out.
    ///
    /// Complexity tradeoff (COMPLEXITY.md POW-rat-literal-ops): each operand's fact is a lookup
    /// of the one kept for it, or one literal's reading, so an operation costs at most one
    /// kernel operation that is not a power, and a chain of n operations O(n) of them; the
    /// naive [`folded`] of each operation's whole text would cost O(n^2) over a chain, and
    /// folding each power O(value of its exponent).
    fn rat_folded(&mut self, op: BinaryOp, a: &Expr, b: &Expr, span: Span, t: &Ty) -> bool {
        // A class of literals may resolve to `rat`: the operands' values are the same at each
        // carrier, so a base or divisor known to be no zero rules `#divByZero` out there too.
        if t.numeric_carrier() != Some(Carrier::Rat) && self.class_beside_atoms(t).is_none() {
            return false;
        }
        let Some(p) = binary_prim(op).filter(|_| {
            matches!(
                op,
                BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Pow
            )
        }) else {
            return false;
        };
        let x = self.rat_fact(a);
        let y = match op {
            BinaryOp::Pow => rat_exponent(b).map(RatFact::Value),
            _ => self.rat_fact(b),
        };
        // Only the divisor of a `/` can give `#divByZero`: one known to be no zero rules it out
        // whatever the dividend is, as in `n / (2r/3r)`. A dividend the text does not give may
        // carry atoms of its own, so the quotient is kept as no fact.
        if op == BinaryOp::Div && x.is_none() {
            return y.is_some_and(|y| y.nonzero());
        }
        let Some(fact) = rat_step(p, x, y) else {
            return false;
        };
        self.rat_folds.insert(span, fact);
        true
    }

    /// What the text gives of `e` at `rat`: the value of a literal, perhaps under `-`, read at
    /// `rat`, or what [`Self::rat_folded`] kept for an operation. O(1).
    fn rat_fact(&self, e: &Expr) -> Option<RatFact> {
        if let Some(f) = self.rat_folds.get(&e.span) {
            return Some(f.clone());
        }
        let rat = |x: &Expr| matches!(x.kind, ExprKind::Rat(_));
        match &e.kind {
            ExprKind::Unary(UnaryOp::Neg, x) if rat(x) => folded(e, Carrier::Rat),
            _ if rat(e) => folded(e, Carrier::Rat),
            _ => literal(e, None).and_then(|l| lit_value(&l, Carrier::Rat)),
        }
        .map(RatFact::Value)
    }

    /// The one carrier `e`'s value has where the walk read it, if it knows one: the carrier
    /// the literal `e` adopted, as `0` in `r == 0` adopts `rat` with `r: rat`, or with `deep`
    /// the one the leftmost literal of an operation on literals adopted, as all its literals
    /// adopt one; else the one carrier of the type the walk last gave `e`, or of its class of
    /// literals while the class is open. `deep` costs the depth of `e`'s leftmost path, so
    /// [`Self::term`] asks it only of an expression whose operands it then does not visit.
    fn carrier_here(&self, e: &Expr, deep: bool) -> Option<Carrier> {
        let mut x = e;
        if deep {
            while let ExprKind::Unary(_, a) | ExprKind::Binary(_, a, _) = &x.kind {
                x = a;
            }
        }
        if let Some(l) = literal(x, None)
            && let Some(v) = self.info.adopt.get(&l.span)
        {
            return Some(lit_carrier(v));
        }
        let t = self.seen.get(&e.span)?.0.as_ref()?;
        let mask = match self.class_beside_atoms(t) {
            Some(k) => self.classes[k].mask,
            None => mask_of(t),
        };
        Carrier::ALL.into_iter().find(|c| c.bit() == mask)
    }

    /// The `rat` value of `e`, at `rat` ([`Self::carrier_here`]): a literal, perhaps under
    /// `-`, or what [`Self::rat_folded`] kept of an operation on literals, as `-1r/2r`, or
    /// `1/2` beside a `rat`, for [`Self::term`] to read a test such as `r != 0r`, `r == 0` or
    /// `r <= -1/2` as one on a literal (NARROW-ne-rat-divisor). O(1).
    fn rat_literal(&self, e: &Expr) -> Option<Value> {
        let rat = matches!(e.kind, ExprKind::Rat(_))
            || matches!(&e.kind, ExprKind::Unary(UnaryOp::Neg, x) if matches!(x.kind, ExprKind::Rat(_)))
            || self.carrier_here(e, false) == Some(Carrier::Rat);
        match self.rat_fact(e).filter(|_| rat)? {
            RatFact::Value(v) => Some(v),
            RatFact::Range(_) => None,
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
                positional,
                named,
                span,
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

    /// The call `c` of a prelude word, `f` its type. A call with as many arguments as the word
    /// has parameters, the value before the dot counted, is the word applied to them: one by
    /// [`Self::word`], two or three by [`Self::call_value`]. Named arguments and `...` are
    /// reported by elaboration, which says that a word's parameters have no names. Any other
    /// count is an error that names the word and its parameters as DESIGN.md writes them
    /// ([`Self::word_count`]), where [`Self::call_value`] would name the parameters `x0`, `x1`
    /// of the word's signature and print the word as its type, and where `y.sqrt(2.0)` was
    /// given no type and no error at all.
    fn prelude_call(&mut self, m: &mut M<'a>, f: &Ty, c: PreludeCall<'a>) {
        let k = word_arity(c.w);
        let n = c.positional.len() + usize::from(c.receiver.is_some());
        let (receiver, of) = c.receiver.unzip();
        if c.named.is_empty() && !c.curry && n == k {
            return match k {
                1 => self.word(m, c.w, c.positional, receiver, c.span),
                _ => {
                    let args = Args::of(c.positional, c.named);
                    self.call_value(m, f, c.w.into(), receiver, args, false, c.span)
                }
            };
        }
        let err = (c.named.is_empty() && !c.curry)
            .then(|| self.word_count(c.w, of, c.positional, c.span));
        m.k(Frame::Fail(err));
        m.each(Args::of(c.positional, c.named).exprs());
    }

    /// The error of the call at `span` of the prelude word `w` with the arguments `of`, the
    /// expression before the dot, and `positional`, whose number is not the word's: its place,
    /// its message and its repairs. The message names the word and its parameters and shows the
    /// call as written, "`fma` takes 3 arguments, `fma(a, b, c)`, and `fma(x, x)` passes 2.";
    /// a call with too many arguments is rewritten with the first ones alone, as `sqrt(1.0)`
    /// for `sqrt(1.0, 2.0)`, and a call with too few names the missing parameters, as
    /// `fma(x, x, c)`. Complexity tradeoff: the naive way, the call checked against the word's
    /// signature as a call of a function value, finds the same count in O(n) for `n`
    /// arguments but reports it as a parameter given no value or an argument too many, in the
    /// words of the signature. Used: the count compared once, O(1), and the message written
    /// from at most the word's three arguments and the call's text, O(length of the call).
    fn word_count(
        &self,
        w: &str,
        of: Option<&Expr>,
        positional: &[Expr],
        span: Span,
    ) -> (Span, String, Vec<String>) {
        let params = word_params(w);
        let k = params.len();
        let n = positional.len() + usize::from(of.is_some());
        let takes = match k {
            1 => "one argument".to_string(),
            _ => format!("{k} arguments"),
        };
        let one_line = |c: &'a str| (!c.contains('\n')).then_some(c);
        let whole = params.join(", ");
        let passes = match self.code(Some(span)).and_then(one_line) {
            Some(c) => format!("`{c}` passes {n}"),
            None => format!("this call passes {n}"),
        };
        let mut message = format!("`{w}` takes {takes}, `{w}({whole})`, and {passes}.");
        let mut menu = Vec::new();
        // The value before the dot is the first argument, which the count includes.
        if let Some(x) = of.and_then(|e| self.code(Some(e.span))).and_then(one_line) {
            menu.push(format!(
                "`{x}` before `.{w}` is the first argument of `{w}`"
            ));
        }
        // The arguments as written, the value before the dot first; none where one is not on
        // one line or the checker has no text.
        let written: Option<Vec<&str>> = (of.into_iter().chain(positional))
            .take(k)
            .map(|e| self.code(Some(e.span)).and_then(one_line))
            .collect();
        match written {
            Some(written) if n > k => {
                let call = format!("{w}({})", written.join(", "));
                message.push_str(&format!(" Try `{call}` instead."));
                menu.push(format!("repair: `{call}`"));
            }
            Some(written) => {
                let missing = &params[n..];
                let all: Vec<&str> = written.into_iter().chain(missing.iter().copied()).collect();
                let call = format!("{w}({})", all.join(", "));
                let named = match missing {
                    [p] => format!("`{p}`"),
                    [rest @ .., last] => {
                        let rest: Vec<String> = rest.iter().map(|p| format!("`{p}`")).collect();
                        format!("{} and `{last}`", rest.join(", "))
                    }
                    [] => unreachable!("a call with fewer arguments than parameters"),
                };
                menu.push(format!("repair: give {named} a value, as `{call}`"));
            }
            None => menu.push(format!("repair: pass {takes}, as `{w}({whole})`")),
        }
        (span, message, menu)
    }

    /// The prelude word `w` applied to one argument `x`, recorded as the construct being
    /// checked ([`Self::as_written`]).
    fn word_end(&mut self, w: &'a str, x: Arg<'a>, span: Span) -> Ty {
        self.as_written(Construct::Word(w), vec![Some(x)], span)
    }

    /// [`Self::word_end`] checked.
    fn word_applied(&mut self, w: &'a str, mut x: Arg<'a>, span: Span) -> Ty {
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
        // [`Self::word_atoms`] casts it, at the cost it names.
        if self.level == 0
            && let Some(l) = (x.lit.clone()).filter(|l| l.bare && is_decimal(&l.value))
            && let Some(p) = zedc_base::interp::prim(w)
        {
            let sig = word_sig(w);
            // A word that takes float formats alone, `f64` among them, as `sqrt` does, gives
            // the literal `f64` (author decision, 2026-11-12, [`floats_take_f64`]):
            // `sqrt(2.0)` is `sqrt(2.0f64)`.
            let takes: Vec<Carrier> = [Carrier::F64, Carrier::Rat, Carrier::F32]
                .into_iter()
                .filter(|&c| (sig.arrows.iter()).any(|a| a.params[0] == Ty::carrier(c)))
                .collect();
            let floats = floats_take_f64(&takes);
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
                if !floats {
                    let notes = self.derive(&[l.site]);
                    let m = unfixed(&l, &cs);
                    self.reject(Some(Row::UnfixedDecimal), l.site, m, notes);
                }
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
                let m = unfixed(l, &[Carrier::F64, Carrier::Rat]);
                self.reject(Some(Row::UnfixedDecimal), l.site, m, notes);
            }
            // So is one a branch of an `if` of literals gives, `String(if c { 1 } else
            // { 2.5 })`, and one a call gives through its body, `String(g(c))` with
            // `g(positional c: bool) = if c { 1 } else { 2.5 }` ([`Self::unfixed_calls`]).
            let bs = x.branches.iter().flat_map(|bs| bs.iter());
            let found: Vec<(Span, Msg)> = (bs.filter_map(|b| match b {
                Branch::Lit(l) if l.bare && lit_carrier(&l.value) != Carrier::Int => Some(l),
                _ => None,
            }))
            .map(|l| (l.site, unfixed(l, &[Carrier::F64, Carrier::Rat])))
            .collect();
            self.reject_unfixed(&"the argument of `String`", found);
            if x.lit.is_none() {
                let args = [Some(x.clone())];
                self.unfixed_calls("`String`", &word_sig(w), &args);
            }
        }
        let sig = match w {
            "f64" => int_cast_sig(Carrier::F64, self.int_cast(&x, Carrier::F64)),
            "f32" => int_cast_sig(Carrier::F32, self.int_cast(&x, Carrier::F32)),
            _ => word_sig(w),
        };
        let values = self.operand_values(&x);
        let carried = x.ty.atoms();
        let at = x.at.unwrap_or(span);
        if w == "rat" {
            self.rat_takes_int(&x, span);
        }
        let no_zero = w == "rat" && self.ints_without_zero(&x);
        let mut r = self
            .apply(
                Label::Text(&format!("`{w}`")),
                &sig,
                vec![Some(x)],
                true,
                span,
            )
            .0;
        if no_zero && let Some(zero) = KType::lit(&Value::rat(Rat::int(0.into()))) {
            r.set = &r.set - &zero;
        }
        match values {
            Some(values) => self.word_atoms(w, values, r, &carried, at, span),
            None => r,
        }
    }

    /// Takes the operand `x` of `rat` at `span` at `int` if it is an operation on integer
    /// literals alone written in place, as `2^64 + 13` in `rat(2^64 + 13)`: `rat` of an int is
    /// exact and gives no atom (QUESTIONS A36: a cast keeps an atom only where its operand can
    /// give it), and nothing else reads the class, so it takes `int` when its function ends
    /// ([`Ck::lits_take`]). Such a class keeps the float formats among its carriers until then,
    /// and at `f64` `2^2000` is the infinity, of which `rat` is `#invalid`, so the atom of the
    /// `f64` arrow is dropped by taking the class at `int` now, not by dropping it alone. A name
    /// bound to such an operation, `b` with `b = 2^64 + 13`, is an `int` already, fixed where
    /// it is bound (QUESTIONS A63, [`Self::fix_bound`]). Left as they are: a class that holds a
    /// bare decimal literal, or a `/`, as `rat(1 / 2)`, which no use took `int` from but its
    /// own operation, and which is rejected for want of a carrier when its function ends; and
    /// a class of a parameter (`binder`) or merged with one (not `generic`), which may hold any
    /// value of its carrier, a NaN among them.
    // Complexity tradeoff: naive version, a range of the value at each float carrier read
    // from the text, which would keep `rat(b)` exact at `f64` too but must bound every
    // intermediate value (`2^2000 - 2^2000` is a NaN at `f64`) through every name read, O(size
    // of the expressions read) per cast. Used: the class's flags and one restriction of its
    // mask, O(α(N)) for the find in a union of N classes. Before names were fixed where they
    // are bound (LIT-name-int-fixed), this also rejected the cast where a later use had taken
    // `int` from the class; that use is now rejected itself, at the use.
    fn rat_takes_int(&mut self, x: &Arg<'a>, span: Span) {
        let Some(k) = self.class_beside_atoms(&x.ty) else {
            return;
        };
        let c = &self.classes[k];
        if c.generic && c.binder.is_none() && !c.decimal {
            self.restrict_asking(k, Carrier::Int.bit(), "`rat`", span, false);
        }
    }

    /// Whether the operand `x` of `rat` holds ints alone, none of them 0, by its type, its
    /// text and the tests the walk is in, as `x` with `x = 2`, or `n` under `if n > 0`. `rat`
    /// of an int is exact, so it then gives no `0r`, and `1r / rat(x)` and `rat(x)^-1` cannot
    /// fail (DESIGN.md step L1.17). A `rat`, `f64` or string operand may give `0r`. Cost: that
    /// of [`Self::ints_of`], as for [`Self::exact_in_f64`].
    fn ints_without_zero(&mut self, x: &Arg<'a>) -> bool {
        let others = [KType::rat(), KType::f64(), KType::f32(), KType::string()];
        if x.ty.numeric_carrier() != Some(Carrier::Int)
            || others.iter().any(|t| !(&x.ty.set & t).lists_nothing())
        {
            return false;
        }
        let Some(e) = x.expr else {
            return false;
        };
        let ns = &x.ty.set & &KType::int();
        !self.ints_of(&ns, e).0.contains(0)
    }

    /// Whether every int the operand `x` of `f64` may be lies within ±2^53, so that its cast is
    /// exact (DESIGN.md "Casts are domain proofs"): the ints its text shows, met with what the
    /// tests the walk is in show of it and with the values its type lists ([`Self::ints_of`]).
    /// An operand with no int part, or with no expression to read, is not shown to be. Unlike
    /// [`Self::int_range`], it builds no text to show the ints. Cost: one read of what the text
    /// shows and one narrowing by the enclosing tests (COMPLEXITY.md C26, F175), the work a bit
    /// word's operand takes; building the text as well would print a type at each cast.
    fn exact_in_f64(&mut self, x: &Arg<'a>) -> bool {
        self.int_cast(x, Carrier::F64) == IntCast::Exact
    }

    /// What the checker proves of the ints the operand `x` of the cast to the float format `c`
    /// may be: that each lies within ±[`exact_int_bound`] of `c`, as [`Self::exact_in_f64`] says
    /// for `f64`, so the cast is exact; or else that each lies within the format's largest finite
    /// value, so it is not `#overflow` (A36). Both are read from one interval: the naive way,
    /// a separate read for each fact, would walk the text and the enclosing tests twice. Cost:
    /// one [`Self::ints_of`] and two subset tests against one interval, `O(log p)` each for `p`
    /// pieces ([`IntervalSet::is_subset`]).
    fn int_cast(&mut self, x: &Arg<'a>, c: Carrier) -> IntCast {
        let ns = &x.ty.set & &KType::int();
        let Some(e) = x.expr.filter(|_| !ns.is_empty()) else {
            return IntCast::Unproved;
        };
        let (ints, _, _) = self.ints_of(&ns, e);
        let b = exact_int_bound(c);
        if ints.is_subset(&IntervalSet::of(-b, b)) {
            return IntCast::Exact;
        }
        let m = largest_float_int(c);
        match ints.is_subset(&IntervalSet::range(Fin(-&m), Fin(m))) {
            true => IntCast::InRange,
            false => IntCast::Unproved,
        }
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
        let t = self
            .apply(Label::Text(&format!("`{w}`")), &sig, args, true, span)
            .0;
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
        let out = self.passing(f, "a call", span, None);
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
                    // A call takes a function, which no carrier holds: a class of carriers
                    // alone, as the literal `2` of `(1, 2)` read by `p[1](p[0])`, cannot
                    // be called. A class that may still hold a function is left as it is,
                    // as a variable of the body is, and its call is checked where the
                    // function is known.
                    if self.classes[self.find(k)].mask & OTHER == 0 {
                        let shown = self.show(&p.ty());
                        self.not_a_function(&s.what, &shown, span);
                        continue;
                    }
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
                    self.not_a_function(&s.what, &shown, span);
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

    /// The error of a call at `span` of `w`, a value of the type shown as `shown` that is not
    /// a function.
    fn not_a_function(&mut self, w: &str, shown: &str, span: Span) {
        let w = callee(w);
        let menu = [format!(
            "repair: call a function here, or write {w} without the parentheses of the call if \
             its value is meant"
        )];
        self.error_offering(
            span,
            format!(
                "{w} is {shown}, not a function: this call applies {w} to arguments, and a \
                 value of type {shown} cannot be applied"
            ),
            menu,
        );
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
                let form = Construct::Call(what.as_str().into(), s.sig.clone());
                let t = self.as_written(form, args, s.span);
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
            if !self.trying {
                self.failed.insert(span);
            }
            return m.ty(Ty::empty());
        }
        // The first misfit, the one elaboration would report first, explains the refusal.
        let (at, misfit) = misfits[0];
        let message = format!(
            "{} here is a function of type `{}`, and the arguments of this call do not fit its \
             parameters: {}",
            callee(what),
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
                Some(1) => {
                    let f = Ty::func(word_sig(name));
                    let call = PreludeCall {
                        w: name,
                        receiver: Some((x, of)),
                        positional,
                        named,
                        curry,
                        span,
                    };
                    self.prelude_call(m, &f, call);
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
pub(super) fn branch_lits<'e>(
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

/// A value of type `t` read at the parameter `p` where `p` holds numbers of one carrier, `f64`
/// or `rat`, and `t` lists each of its values outside that carrier, as `1 | 2` or `1 | f64`
/// at `f64` ([`listed_outside`]): `t` with each listed value read at the carrier, and the
/// carrier. With `g(positional c: bool) = if c { 2 } else { 1 }`, of type `(bool) -> 1 | 2`,
/// `g(c)` at an `f64` parameter is `2.0 | 1.0` (L1.26a: "each keeps its own value and is
/// fixed where the result is used", and "`z: f64 = g(c)` read both branches at `f64`"); with
/// `g(positional c: bool, positional x: f64) = if c { x } else { 1 }`, of type `(bool, f64)
/// -> 1 | f64`, `g(c, x)` there is `f64` (sec:type_resolution, rule 3: "each value keeps its
/// own carrier, the literal `1` taking its carrier where the result is used"). An integer
/// value is read at `f64`, `f32` or `rat` where it is exactly one, and a decimal one only at `f64`,
/// which its value at run time already is: read at `rat` it would be the `f64`'s value, not
/// the decimal's. `None` where `t` is not read so, which leaves it to the check every
/// argument has: a part outside the carrier that is not a list of values, as the `int` of
/// `int | f64`, has no value to read. `Some(Err((v, c)))` where every value outside the
/// carrier is a number but `v` is not read at `c`: an integer with no exact value at `c`, as
/// a lone integer literal there has none (sec:diagnostics: "an integer literal takes a
/// carrier only where that carrier holds it exactly"), or a decimal at `rat`. Only the
/// argument [`Ck::readable`] finds is read so: a name, `y` after `y = g(c)`, is not, since
/// its value is fixed where it is bound ("bound to a name alone"). A decimal at `rat` that literals
/// written as branches of an `if` give is adopted there ([`Ck::read_adopting`]).
// Complexity tradeoff: O(v log v) for the `v` values the type lists outside the carrier, each
// cast once and the singletons joined in pairs (`Ty::union_all`); the listing itself costs
// the size of the type ([`KType::values_listed`]). The naive form, the type `1 | 2` tested
// against `f64`, rejects the call, since an `int` value is no `f64`. Joining the singletons
// one at a time instead copies the union so far at each, O(v²) element copies;
// `lit_branch_ops::scaling` does not catch that form (8.1 times for 8 times the size), since
// checking the `g` that gives the values costs far more per value (COMPLEXITY.md F164).
pub(super) fn read_ty(t: &Ty, p: &Ty) -> Option<Result<(Ty, Carrier), (Value, Carrier)>> {
    let c = read_carrier(p)?;
    Some(read_at(t, c)?.map(|t| (t, c)).map_err(|v| (v, c)))
}

/// An argument read at a carrier ([`Ck::read_arg`]): its type read there, the carrier and the
/// literals adopted at it, or the value no value of the carrier equals and the carrier.
type ReadArg = Result<(Ty, Carrier, Adoptions), (Value, Carrier)>;

/// The carrier [`read_ty`] reads at, where `p` holds numbers of one carrier, `f64`, `f32` or `rat`,
/// and no type variable or `_`.
fn read_carrier(p: &Ty) -> Option<Carrier> {
    if p.dynamic || !p.vars.is_empty() {
        return None;
    }
    let held = [Carrier::Int, Carrier::Rat, Carrier::F64, Carrier::F32]
        .into_iter()
        .filter(|c| !(&p.set & &c.ty()).is_empty());
    match held.collect::<Vec<_>>()[..] {
        [c @ (Carrier::F64 | Carrier::F32 | Carrier::Rat)] => Some(c),
        _ => None,
    }
}

/// Whether `t` holds values alone: no tuple shape, function, type variable or `_`.
fn values_alone(t: &Ty) -> bool {
    t.tuples.is_empty() && t.fns.is_empty() && t.vars.is_empty() && !t.dynamic
}

/// The values of `t` outside the carrier `c`, where `t` is [`values_alone`] and lists each of them,
/// one or more: `[1]` for `1 | f64` and `[1, 2]` for `1 | 2` at `f64`; `None` for `f64`, which
/// has none, and for `int | f64`, whose `int` is no list.
fn listed_outside(t: &Ty, c: Carrier) -> Option<Vec<Value>> {
    if !values_alone(t) {
        return None;
    }
    (&t.set - &c.ty())
        .values_listed()
        .filter(|vs| !vs.is_empty())
}

/// Whether `t` lists a number: one or more values of some numeric carrier, each listed, as
/// `1 | f64` lists `1` and `int | f64` lists none.
fn lists_a_number(t: &Ty) -> bool {
    [Carrier::Int, Carrier::Rat, Carrier::F64, Carrier::F32]
        .into_iter()
        .any(|c| {
            (&t.set & &c.ty())
                .values_listed()
                .is_some_and(|vs| !vs.is_empty())
        })
}

/// The numeric carriers of which `t` holds a part whole, not as a list of values: `f64` for
/// `1 | f64` and for `f64`, none for `1 | 2`, `int` and `f64` for `int | f64`.
fn whole_carriers(t: &Ty) -> impl Iterator<Item = Carrier> + '_ {
    [Carrier::Int, Carrier::Rat, Carrier::F64, Carrier::F32]
        .into_iter()
        .filter(|c| {
            let part = &t.set & &c.ty();
            !part.is_empty() && part.values_listed().is_none()
        })
}

/// The parts of the [`values_alone`] type `t` that arrows may take apart, as [`Ck::fewest`] splits
/// them: each value of a part that lists its values, and else the part whole, for the numbers
/// of each numeric carrier and for the other values. `1 | f64` gives `1` and `f64`.
fn taken_apart(t: &Ty) -> Vec<Ty> {
    let numeric = [Carrier::Int, Carrier::Rat, Carrier::F64, Carrier::F32];
    let all = numeric.iter().fold(KType::empty(), |s, c| &s | &c.ty());
    let parts = numeric.iter().map(|c| &t.set & &c.ty());
    let mut out = Vec::new();
    for part in parts.chain([&t.set - &all]) {
        if part.is_empty() {
            continue;
        }
        match part.values_listed() {
            Some(vs) => out.extend(vs.iter().map(Ty::lit)),
            None => out.push(Ty::set(part)),
        }
    }
    out
}

/// The call `a` is, where it is one and holds no literal ([`Arg::branches`], [`Arg::parts`]).
fn lone_call<'e>(a: &Arg<'e>) -> Option<&'e Expr> {
    let e = a
        .expr
        .filter(|_| a.lit.is_none() && a.branches.is_none() && a.parts.is_none())?;
    matches!(exported(e).kind, ExprKind::Call { .. }).then_some(e)
}

/// The values `a` may give where it is a call whose type lists values alone, as `g(c)` of
/// type `1 | 2`: the decimals among them are those [`Ck::unfixed_calls`] looks for. `None`
/// where `a` is no call, is a literal or holds one ([`Arg::branches`], [`Arg::parts`]), or
/// its type is not a list of values.
fn call_values(a: &Arg) -> Option<Vec<Value>> {
    lone_call(a)?;
    let t = &a.ty;
    if !values_alone(t) {
        return None;
    }
    t.set.values_listed().filter(|vs| !vs.is_empty())
}

/// The type `t` read at the carrier `c`, `f64`, `f32` or `rat`, as [`read_ty`] says: `t` with each
/// value it lists outside `c` read at `c`, `Err(v)` with the first value `v` not read at `c`,
/// or `None` where `t` lists no value outside `c` ([`listed_outside`]) or one of them is no
/// number.
fn read_at(t: &Ty, c: Carrier) -> Option<Result<Ty, Value>> {
    let vs = listed_outside(t, c)?;
    let cast = match c {
        Carrier::F64 => Prim::CastF64,
        Carrier::F32 => Prim::CastF32,
        _ => Prim::CastRat,
    };
    // The part already of the carrier, as the `f64` of `1 | f64` or the `2.5` of `1 | 2.5` at
    // `f64`, needs no read.
    let mut ts = vec![Ty::set(&t.set & &c.ty())];
    // The first value not read: an integer with no exact value at `c`, or a decimal at `rat`.
    let mut unread = None;
    for v in &vs {
        let r = match v {
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
        // A question refused behind the value is named before the derivation, as at `^`.
        let mut notes = self.refused_notes(e);
        self.derive_into(&[e.span], &mut notes);
        notes.extend(menu.into_iter().map(|text| Note { span: e.span, text }));
        self.error_with(e.span, message, notes);
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

    /// The interval of each name written in `e` that a test the walk is in narrows, by the
    /// name's span, as `int[0..]` for `k` in the arm of `if k >= 0` (POW-nonneg-power), for the
    /// derivation of a rejection of `e` ([`Ck::derive_narrowed`]). Read only for a rejection:
    /// one [`Self::ints_here`] per name of `e`, O(m) reads for `m` names, against the one read of
    /// `e` itself the check made; a name in a value a name of `e` is bound to is not read, since
    /// its note stands where it is bound, where the tests here may not hold.
    fn narrowed_names(&mut self, e: &'a Expr) -> HashMap<Span, String> {
        let mut out = HashMap::new();
        if self.trying || self.arms.here() == 0 {
            return out;
        }
        let mut stack = vec![e];
        while let Some(x) = stack.pop() {
            match &x.kind {
                ExprKind::Name(_) => {
                    let (ints, narrowed) = self.ints_here(x);
                    if narrowed {
                        out.insert(x.span, format!("int{ints}"));
                    }
                }
                ExprKind::Unary(_, a) => stack.push(a),
                ExprKind::Binary(_, a, b) => stack.extend([&**a, &**b]),
                ExprKind::If {
                    cond,
                    then,
                    otherwise,
                } => stack.extend([&**cond, &**then, &**otherwise]),
                ExprKind::Block(stmts) => {
                    for s in stmts {
                        match &s.kind {
                            StmtKind::Bind { value, .. } => stack.push(value),
                            StmtKind::Return(es) => stack.extend(es),
                            _ => {}
                        }
                    }
                }
                ExprKind::Call {
                    positional, named, ..
                } => stack.extend(positional.iter().chain(named.iter().map(|(_, a)| a))),
                _ => {}
            }
        }
        out
    }

    /// The two nodes of the condition `e` checked here, where it holds and where it fails, with
    /// the products of its names taken from their types as they are here: a type an `is` has
    /// narrowed holds here, and may not where the scope is read.
    pub(super) fn test_nodes(&mut self, e: &'a Expr) -> (usize, usize) {
        let t = self.term(e);
        let fresh = self.fresh(&t);
        self.arms.test(e, fresh)
    }

    /// Keeps the refusal of the condition `e` of an `if` for each outcome when its `||`
    /// alternatives limit each other's ranges in a loop ([`Scope::looped_test`]), which
    /// [`Ck::finish`] rejects (DESIGN.md step L1.39 and sec:diagnostics). The walk narrows a
    /// condition one comparison at a time, joining at each `||`, and so runs no such loop;
    /// the class is still a property of the condition as written, whether or not an arm is
    /// read, over the ranges its names have where the `if` is (the box of the class: an outer
    /// test can make a bound finite, and the message shows the values). Only a condition that
    /// joins tests by `&&`, `||` or `!` is read: one translation, the scope where the `if` is,
    /// settled as any read there settles it, and one classification, O(s + N log N) for `s`
    /// nodes and `N` atom terms.
    pub(super) fn looped_condition(&mut self, e: &'a Expr) {
        let joined = matches!(
            e.kind,
            ExprKind::Binary(BinaryOp::And | BinaryOp::Or, ..) | ExprKind::Unary(UnaryOp::Not, _)
        );
        if !joined || self.trying {
            return;
        }
        let t = self.term(e);
        let here = self.arms.here();
        let scope = match here {
            0 => Scope::new(self.fresh(&t)),
            _ => {
                let mut wanted = vec![Item::Scope(here)];
                wanted.extend(t.binders.iter().map(|&b| Item::Bound(b)));
                self.settle(wanted);
                let s = self.arms.scopes[here].clone().expect("settled");
                self.with_bound(s, &t.binders)
            }
        };
        for outcome in [true, false] {
            if let Some(r) = scope.looped_test(&t.term, outcome) {
                self.refused_at.entry((e.span, r)).or_default();
            }
        }
    }

    /// The products of the names of `t` taken from their types as they are here.
    fn fresh(&self, t: &Translated) -> Vec<(Arc<str>, Product)> {
        t.vars
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
            .collect()
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
                Node::Assume { test, outcome, .. } => {
                    let wanted = self.waits(Item::Scope(k));
                    self.settle(wanted);
                    let (p, t) = self.assumed(k);
                    // The questions the test asked and the solver refused are the test's,
                    // as when its arm's scope is stored (DESIGN.md L1.39).
                    let (reached, refused) = p.reaches(&t.term, outcome, &Premises::new());
                    self.place_refusals(test.span, &p.refusals, &refused);
                    if reached {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// The ints `e` may be in the scope of the node the walk is in.
    fn ints_in_scope(&mut self, e: &'a Expr) -> IntervalSet {
        self.read_in_scope(e).0.ints().clone()
    }

    /// Whether `e` may be `v` here, as far as the tests the walk is in show: false only where a
    /// test keeps `v` from it, as `r != 0r` keeps `0r` from `r` in its arm. Outside every arm,
    /// or where the text shows the value of `e`, the tests say nothing and the answer is true.
    fn may_be_here(&mut self, e: &'a Expr, v: &Value) -> bool {
        if self.known(e).value.is_some() || self.arms.here() == 0 {
            return true;
        }
        self.read_in_scope(e).0.contains(v)
    }

    /// A note for each step of the derivation of each question the integer solver refused in
    /// the scope `e` is read in ([`Ck::ints_here`]) whose constraint mentions a binding `e` reads
    /// ([`Ck::read_names`]; an inner name that shadows an outer one is another binding), for a rejection of the value of `e`: such a question leaves the
    /// value wider than the tests may make it, so it may be behind the rejection, which names
    /// it as its warning would in a unit the checker accepts (DESIGN.md L1.39). Each note is
    /// at the place the program asks the question ([`Ck::asked_at`]). None where the read
    /// does not take the scope, a value the text shows or a read outside every test, and none
    /// while a repair is tried, whose derivations are not written ([`Ck::derive_into`]).
    ///
    /// Complexity tradeoff: the questions are found through the scope's index of them by binding
    /// ([`Scope::refused_on`]), O(m log k) for the m names `e` reads among k questions, and
    /// not by reading each question of the scope, O(k) for each rejection, which `r`
    /// rejections under `k` refused tests would make O(r k). The read is taken again, at the
    /// cost of the read [`Ck::ints_here`] took, only for a rejection. Tests:
    /// `l01_29_diagnostics::refused_in_rejection::many_rejections_under_many_refused_tests_scale`
    /// and `l01_39_reduced_product::refused::finding_the_refusals_on_many_names_scales`.
    pub(super) fn refused_notes(&mut self, e: &'a Expr) -> Vec<Note> {
        if self.trying || self.known(e).value.is_some() || self.arms.here() == 0 {
            return Vec::new();
        }
        let (_, s) = self.read_in_scope(e);
        if s.refusals.is_empty() {
            return Vec::new();
        }
        let names = self.read_names(e);
        let mut notes = Vec::new();
        for (r, kept) in s.refused_on(names.iter().map(|(n, _)| &**n)) {
            let span = self.asked_at(r, e.span);
            notes.extend((r.derivation(kept).into_iter()).map(|text| Note { span, text }));
        }
        notes
    }

    /// Where the program asks `r`, a question refused in the scope a value read at `read` is
    /// read in: the last place before the read that the walk placed it at
    /// ([`Ck::place_refusals`]), the test whose arm the read is in or the read itself, or the
    /// read where the walk placed it at none. O(log p) in the p places of `r`.
    fn asked_at(&self, r: &Refused, read: Span) -> Span {
        let last = Span {
            start: read.start,
            end: usize::MAX,
        };
        (self.asked_where.get(r))
            .and_then(|at| at.range(..=last).next_back())
            .copied()
            .unwrap_or(read)
    }

    /// The values `e` may have in the scope of the node the walk is in, and the scope as the
    /// read leaves it, with the questions the read refused.
    fn read_in_scope(&mut self, e: &'a Expr) -> (Product, Scope) {
        let t = self.term(e);
        let here = self.arms.here();
        let mut wanted = vec![Item::Scope(here)];
        wanted.extend(t.binders.iter().map(|&b| Item::Bound(b)));
        self.settle(wanted);
        let s = self.arms.scopes[here].clone().expect("settled");
        let before = s.refusals.clone();
        let mut s = self.with_bound(s, &t.binders);
        s.eager_on(&t.term);
        let p = product::forward(&t.term, &mut s);
        self.place_refusals(e.span, &before, &s.refusals);
        (p, s)
    }

    /// Whether the int `e` may be 0 in the scope of the node the walk is in, with the roots at
    /// which a written constraint gave neither `true` nor `false` ([`Scope::zero_reached`]).
    /// The questions the read refuses are those [`Ck::read_in_scope`] placed for `e` already.
    fn zero_reached_here(&mut self, e: &'a Expr) -> (bool, imbl::OrdSet<RootFailure>) {
        let t = self.term(e);
        let here = self.arms.here();
        let mut wanted = vec![Item::Scope(here)];
        wanted.extend(t.binders.iter().map(|&b| Item::Bound(b)));
        self.settle(wanted);
        let s = self.arms.scopes[here].clone().expect("settled");
        let mut s = self.with_bound(s, &t.binders);
        s.eager_on(&t.term);
        s.zero_reached(&t.term, &Premises::new())
    }

    /// Rejects the division at `span` by `b`, an int divisor that is 0 at the root `f.root`
    /// of `f.name`, where the written constraint `f.constraint` gives `f.gave` and so neither
    /// rules the root out nor lets it through (DESIGN.md sec:diagnostics, QUESTIONS A81).
    fn root_constraint_fails(&mut self, b: &'a Expr, span: Span, f: &RootFailure) {
        let text = |s: Span| self.t.text.map(|t| t[s.start..s.end].to_string());
        let divisor =
            text(b.span).map_or_else(|| "the divisor".to_string(), |d| unparen(&d).to_string());
        let division = text(span).unwrap_or_else(|| "the division".to_string());
        let (name, root, constraint, gave) = (&f.name, f.root, unparen(&f.constraint), &f.gave);
        let message = format!(
            "`{division}` may divide by 0: `{constraint}` gives `{gave}` at `{name} = {root}`, a \
             root of `{divisor} == 0`"
        );
        let mut notes = vec![
            Note {
                span: b.span,
                text: format!(
                    "the division fails with `#divByZero` where `{divisor} == 0`; its integer \
                     roots in the range the tests leave `{name}` are the only values of `{name}` \
                     that reach it, and `{name} = {root}` is one"
                ),
            },
            Note {
                span: b.span,
                text: format!(
                    "the tests around the division include `{constraint}`, evaluated at \
                     `{name} = {root}` to see whether that root reaches the division; it gives \
                     `{gave}`, which is neither `true` nor `false`, so it does not say"
                ),
            },
        ];
        notes.extend(self.derive(&[b.span]));
        let menu = [
            format!(
                "repair: write `{constraint}` so that it gives `true` or `false` at \
                 `{name} = {root}`"
            ),
            "repair: annotate the declaration `@exact`".to_string(),
            format!(
                "repair: give `{name}` a listed set of values in its type, as `{name}: {{…}}` \
                 with each value it takes"
            ),
        ];
        notes.extend(menu.into_iter().map(|text| Note { span, text }));
        self.rejects_with(Row::RootConstraintFails, span, message, notes);
    }

    /// Keeps each question refused in `after`, the refusals of a scope, and not in `before`,
    /// those of the scope it was made from, as asked at `at`: the test that narrowed it, or the
    /// read that settled it (DESIGN.md L1.39, a refused question is reported where the program
    /// asks it). The same question asked again at `at` keeps the meet of its sets
    /// ([`product::kept_meet`]), whatever order the two were met in. Costs what the two maps
    /// do not share, as `imbl`'s diff skips shared subtrees: O(d log k) for `d` new questions
    /// among `k`, so a scope with many refusals each read once is not read again in full.
    fn place_refusals(
        &mut self,
        at: Span,
        before: &imbl::OrdMap<Refused, Kept>,
        after: &imbl::OrdMap<Refused, Kept>,
    ) {
        for d in before.diff(after) {
            let imbl::ordmap::DiffItem::Add(r, kept) = d else {
                continue;
            };
            match self.refused_at.entry((at, r.clone())) {
                std::collections::btree_map::Entry::Vacant(v) => {
                    v.insert(kept.clone());
                    self.asked_where.entry(r.clone()).or_default().insert(at);
                }
                std::collections::btree_map::Entry::Occupied(mut o) => {
                    let met = product::kept_meet(o.get(), kept);
                    o.insert(met);
                }
            }
        }
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
        names: &NameProducts,
    ) -> (Option<IntervalSet>, Premises) {
        let vars = sum.summary.vars();
        let limit = vars.len().min(names.len());
        let base = (self.reads.get(&b)).or_else(|| sum.widest.and_then(|w| self.reads.get(&w)));
        let leaf_of = |v: &Arc<str>| {
            let q = vars.contains(v).then(|| names.read(v)).flatten()?;
            Some(leaf(sum, v, &q))
        };
        // Complexity tradeoff: the diff below stops at `limit`, so a read never walks the
        // whole difference of the two scopes, which is Θ(n²) over a chain of `n` difference
        // tests (`x_i >= x_(i-1) + 1`), each of which moves the product of every name on the
        // path. A summary of `k` inputs under such a chain still resets Θ(min(m, k)) leaves a
        // read for `m` names changed, Θ(n²) over the chain when `k` is about `n`: each is an
        // input whose product the solver changed, which moves the image, so an exact read
        // from the map must visit it. Reading every input by name at every read costs Θ(k) a
        // read, twice as much there. Measured before the checker admitted difference paths
        // (WALK-read-image-n2, `zedc test` at n = 16 and 128): one input, 28 and 252 names
        // read, where the whole difference is 133 and 8,253; `n` inputs, 150 and 8,382,
        // against 241 and 16,257 by name.
        //
        // Complexity tradeoff: naive version, `names` taken as the exact map through
        // `NameProducts`'s `Deref`, which builds the whole map, O(n log² n), for each scope
        // version a binder is read in, Θ(n² log² n) over a chain of n difference tests the
        // checker admits as one path. Used: each input read by name (`NameProducts::read`,
        // O(log² n)), and the names changed since the last read from the diff of the base
        // maps and, when the paths moved, the inputs on a path (`NameProducts::changed`,
        // O(k log n)): O(min(m, k) log² n) a read for m names changed. Measured (`zedc check`,
        // the chain with `w_i = y + x_i` for `y = x_0 + 1`, n = 16 and 128): this read built
        // the map 15 and 127 times before and builds it none after; with `Relation::state_fresh`
        // as well, the check does 9.5 times the instructions at n = 128 as at 16, where it did
        // 31 times with neither and 21 on main, which takes no test of the checker onto a path.
        // COMPLEXITY.md row WALK-read-image-n2.
        let tree = base
            .and_then(|r| {
                let own: Box<dyn Iterator<Item = &Arc<str>>> = if Rc::ptr_eq(&r.sum, sum) {
                    Box::new(std::iter::empty())
                } else {
                    let terms = sum.summary.changed_since(&r.sum.summary)?;
                    Box::new(terms.chain(images::changed(&r.sum.inputs, &sum.inputs)))
                };
                let changed = own.chain(names.changed(&r.names, vars));
                images::updated_with(&r.tree, changed, limit, leaf_of)
            })
            .unwrap_or_else(|| {
                // The smaller of the inputs and the names, as `images::fresh`.
                let here: Box<dyn Iterator<Item = &Arc<str>>> = if vars.len() <= names.len() {
                    Box::new(vars.iter())
                } else {
                    Box::new(names.keys().filter(|v| vars.contains(*v)))
                };
                images::fresh_with(here.filter_map(|v| Some((v, leaf_of(v)?))))
            });
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
                    Node::Assume {
                        parent,
                        test,
                        outcome,
                        ..
                    } => {
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
                        // The questions refused here and not in the parent's scope are this
                        // test's: those the binders it reads asked as they were told of, and
                        // its own narrowing's. A join asks none of its own; it keeps both
                        // sides' ([`Scope::join`]).
                        let before = (self.arms.scopes[parent].as_ref())
                            .map(|q| q.refusals.clone())
                            .unwrap_or_default();
                        self.place_refusals(test.span, &before, &s.refusals);
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
                let before = s.refusals.clone();
                let mut s = self.with_bound_read(s, &t.binders);
                // A parameter the value reads that the scope has no product of is any value of
                // its type where `b` is bound ([`Ck::param_type`]), as [`Ck::summarize_value`]
                // takes it: so `q = n mod 4` with `n: int` is `int[0..=3]`, and a summary that
                // reads `q` as an input has its bounds. Costs the value's names, once.
                if !s.bottom {
                    for (x, id) in &t.vars {
                        if self.facts.contains_key(id) {
                            continue;
                        }
                        let Some(ty) = self.param_type(b, *id).and_then(plain) else {
                            continue;
                        };
                        match s.names.contains_key(x) {
                            false => {
                                s.bind(x, Product::of_type(ty), &Shared::new(Term::Var(x.clone())));
                            }
                            // One a join holds of no type, as from a side that never read it.
                            true => s.meet_type(x, &ty),
                        }
                    }
                }
                s.eager_on(&t.term);
                let mut p = product::forward(&t.term, &mut s);
                if let Some(ty) = self.arms.bound_ty.get(&b) {
                    p.ty.element = p.ty.element.meet(ty);
                }
                self.place_refusals(value.span, &before, &s.refusals);
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
                match p.names.contains_key(x) {
                    false => {
                        p.bind(x, q.clone(), &Shared::new(Term::Var(x.clone())));
                    }
                    // One a join holds of no type, as from a side that never read it.
                    true => p.meet_type(x, &q.ty.element),
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
    /// shows ([`Ck::known`]), its `rat` literals ([`Ck::rat_literal`]), its names, its unary `-`
    /// and `!`, its integer operators, its comparisons, `&&` and `||`; anything else is a name
    /// of its own, by its span, which the scope knows nothing of. Built children first on an
    /// explicit stack, once for `e`.
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
                        let p = match o {
                            UnaryOp::Neg => Prim::Neg,
                            UnaryOp::Not => Prim::Not,
                        };
                        Term::Prim(p, vec![a])
                    }
                    ExprKind::Binary(o, _, _) => {
                        let b = done.pop().expect("a second operand");
                        let a = done.pop().expect("a first operand");
                        Term::Prim(prim_of(*o).expect("a translated operator"), vec![a, b])
                    }
                    _ => unreachable!("only operators wait on their operands"),
                };
                done.push(t);
                continue;
            }
            // A value the text shows at `int` ([`Ck::known`]) is that `int` only where `x` is
            // one, or has no carrier yet: `0` in `r == 0` is `0r` with `r: rat`, and with
            // `r: f64` a value the scope does not model, so a name of its own. Read as the
            // `int` `0`, the test would empty `r`'s type where it holds and drop that arm, and
            // with it the `#divByZero` of `x / r + 1r` there (NARROW-ne-rat-divisor). The
            // operands of such an `x` are not visited.
            if let Some(v) = self.known(x).value {
                done.push(match self.carrier_here(x, true) {
                    None | Some(Carrier::Int) => Term::Lit(v),
                    Some(Carrier::Rat) => match self.rat_fact(x) {
                        Some(RatFact::Value(v)) => Term::Lit(v),
                        _ => opaque(),
                    },
                    Some(_) => opaque(),
                });
                continue;
            }
            if let Some(v) = self.rat_literal(x) {
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
                ExprKind::Unary(UnaryOp::Neg | UnaryOp::Not, a) => {
                    stack.push((x, true));
                    stack.push((a, false));
                }
                ExprKind::Binary(o, a, b) if prim_of(*o).is_some() => {
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
        let mut out = self.passing(v, "a tuple", span, None);
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
                        let shown = self.show(&p.ty());
                        let message = match self.code(Some(span)) {
                            Some(code) => format!(
                                "Cannot take `{code} : {shown}` apart into {n} names: it is not a \
                                 tuple of {n}"
                            ),
                            None => format!(
                                "Cannot take a value of {shown} apart into {n} names: it is not a \
                                 tuple of {n}"
                            ),
                        };
                        self.error_offering(span, message, menu);
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
        let (t, _) = self.apply(Label::Text(what), sig, with, false, span);
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
            self.check_on(n, t, n.span, None);
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
        if let Some(b) = self.bound.get_mut(level) {
            *b = Vars::default();
        }
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
    fn merge(&mut self, named_a: usize, named_b: usize, what: &str, span: Span) -> bool {
        let (a, b) = (self.find(named_a), self.find(named_b));
        if a == b {
            return true;
        }
        let m = self.classes[a].mask & self.classes[b].mask;
        if m == 0 {
            return false;
        }
        self.touch(a);
        self.touch(b);
        let reason = Reason {
            span,
            what: what.into(),
            takes: None,
        };
        match self.classes[a].size <= self.classes[b].size {
            true => self.link_proof(named_a, named_b, reason.clone()),
            false => self.link_proof(named_b, named_a, reason.clone()),
        }
        let (root, child) = match self.classes[a].rank < self.classes[b].rank {
            true => (b, a),
            false => (a, b),
        };
        if self.classes[a].rank == self.classes[b].rank {
            self.classes[root].rank += 1;
        }
        // Each use of one class is checked on what flowed into the other.
        let mut cross: Vec<(Need, Inflow)> = Vec::new();
        for (x, y) in [(a, b), (b, a)] {
            for (_, n) in &self.classes[x].uses {
                for v in &self.classes[y].flowed {
                    cross.push((n.clone(), v.clone()));
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
        let binder = self.classes[child].binder.clone();
        let generic = self.classes[child].generic;
        let asked = self.classes[child].asked;
        let floats = self.classes[child].floats;
        let decimal = self.classes[child].decimal;
        let given = self.classes[child].given;
        let narrowed_to = std::mem::take(&mut self.classes[child].narrowed_to);
        let narrows = self.classes[child].narrows;
        let size = self.classes[child].size;
        self.classes[child].parent = root;
        let c = &mut self.classes[root];
        c.size += size;
        c.generic &= generic;
        c.asked |= asked;
        c.floats |= floats;
        c.decimal |= decimal;
        // Its values are no longer those of one `min` or `max` use only.
        c.order_of = None;
        c.given &= given;
        c.narrowed_to.extend(narrowed_to);
        c.narrows |= narrows;
        c.binder = match (c.binder.take(), binder) {
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
        c.reasons.push(reason);
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
        for (n, v) in &cross {
            self.check_on(n, &v.ty, v.at, Some(v));
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
        for v in &flowed {
            self.check_on(&need, &v.ty, v.at, Some(v));
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
        for v in &flowed {
            self.check_on(&need, &v.ty, v.at, Some(v));
        }
        result.unwrap_or_else(Ty::empty)
    }

    /// Checks the use `n` of a class on `t`, which flowed into the class at `span` as the
    /// value `came` or which the class takes: what the use gives flows into the class of its
    /// result. A rejection of a value that flowed in names where it comes from and each merge
    /// that brought it to the use (MSG-flow-origin).
    fn check_on(&mut self, n: &Need, t: &Ty, span: Span, came: Option<&Inflow>) {
        let from = self.errors.len();
        let start = self.need_passed.len();
        self.call_frames.push(CallFrame::default());
        let got = self.meet(n, t, &mut Binds::new(), span);
        self.call_frames.pop();
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
            && !self.flow(k, &got, "this use", n.span, n.span)
        {
            let shown = self.show(r);
            let got = self.text(&got);
            let one_line = |s: Option<&'a str>| s.filter(|c| !c.contains('\n'));
            let used = one_line(self.code(Some(n.span)));
            let value = came
                .filter(|v| v.from != n.span)
                .and_then(|v| one_line(self.code(Some(v.from))));
            let message = match (used, value) {
                (Some(u), Some(v)) => {
                    format!("`{u}` gives {got} on the value `{v}`, but other uses need {shown}")
                }
                (Some(u), None) => format!("`{u}` gives {got}, but other uses need {shown}"),
                (None, _) => format!(
                    "this use gives {got}, not {shown}: its result flows into a value that \
                     other uses have already made {shown}"
                ),
            };
            let mut menu = Vec::new();
            if let Some(v) = came
                && !self.trying
            {
                menu.extend(self.default_repair(n, v));
            }
            menu.push(
                "repair: declare the types of the values this use reads, so that it is checked \
                 where it is written"
                    .to_string(),
            );
            self.error_offering(n.span, message, menu);
        }
        self.also(from, n.span, |_| "this use needs it here".to_string());
        if let Some(v) = came {
            self.also_notes(from, |ck| ck.came_from(n, v));
        }
    }

    /// The class of the use `n`'s value, as it was when the use was recorded: the class the
    /// merges are followed to.
    fn use_class(n: &Need) -> Option<usize> {
        n.on.as_var().and_then(|v| class_id(v))
    }

    /// The notes that say where the value `v` comes from, when it is not the use `n` itself,
    /// and each merge on the way from the class it entered to the class of `n`'s value, in
    /// order.
    fn came_from(&self, n: &Need, v: &Inflow) -> Vec<Note> {
        let mut out = Vec::new();
        if v.from != n.span {
            let text = match (self.code(Some(v.from)), self.code(Some(n.span))) {
                (Some(c), Some(u)) if !c.contains('\n') && !u.contains('\n') => {
                    format!("`{c}` comes from here and reaches `{u}`")
                }
                _ => "the value comes from here".to_string(),
            };
            built(1);
            out.push(Note { span: v.from, text });
        }
        if let Some(u) = Self::use_class(n) {
            for r in self.merges_between(v.class, u) {
                // A default is named with its parameter, in the program's words.
                let default = self.defaults.get(&r.span).zip(self.code(Some(r.span)));
                out.push(match default {
                    Some((name, d)) if !d.contains('\n') => {
                        built(1);
                        Note {
                            span: r.span,
                            text: format!(
                                "the default `{name} = {d}` gives `{name}` the type of `{d}`"
                            ),
                        }
                    }
                    _ => r.note(),
                });
            }
        }
        out
    }

    /// The repair of a rejection of the use `n` on the value `v` whose way to the use runs
    /// through a default of a parameter, checked at the parameter's type: the parameter with
    /// no default, which a call that leaves it out then passes, as the declaration rewritten.
    /// The last such default on the way, nearest the use: the way runs from the parameter
    /// the value was passed as to the class of the use, so the last default is the one that
    /// reads a value the calls can name, while an earlier one reads another parameter, as
    /// `h2 = h1` does; none if there is none.
    fn default_repair(&self, n: &Need, v: &Inflow) -> Option<String> {
        let u = Self::use_class(n)?;
        let (span, name) = self
            .merges_between(v.class, u)
            .iter()
            .rev()
            .find_map(|r| Some((r.span, self.defaults.get(&r.span)?)))?;
        let default = self.code(Some(span))?;
        let rewritten = self.t.text.and_then(|text| {
            let before = text.get(..span.start)?.trim_end().strip_suffix('=')?;
            let cut = before.trim_end().len();
            let line_start = text[..cut].rfind('\n').map_or(0, |i| i + 1);
            let line_end = text[span.end..]
                .find('\n')
                .map_or(text.len(), |i| span.end + i);
            let line = format!("{}{}", &text[line_start..cut], &text[span.end..line_end]);
            Some(line.trim().to_string())
        });
        let pass = format!("pass `{default}` as `{name}` in each call that leaves `{name}` out");
        Some(match rewritten {
            Some(d) if !default.contains('\n') => {
                format!("repair: write `{name}` with no default, as `{d}`, and {pass}")
            }
            _ => format!("repair: write `{name}` with no default, and {pass}"),
        })
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
        // Each positional argument of the use that is a parameter of the call whose need it
        // is comes from that call's argument, where one parameter alone holds its variables.
        self.need_from = match (&n.kind, self.call_frames.last()) {
            (NeedKind::Call { positional, .. }, Some(frame)) if !frame.args.is_empty() => {
                Some(positional.iter().map(|t| frame.from(t)).collect())
            }
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
            NeedKind::Power(p) => {
                self.power_on(&on, p, span);
                Ty::empty()
            }
            NeedKind::InDomain { .. } => Ty::empty(),
            NeedKind::Into { what, ty } => {
                let from = self.call_frames.last().and_then(|f| f.named(&n.on));
                self.into(&on, ty, what, from, span);
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
        self.need_from = None;
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
                if !self.gives_within(&got, r, binds, what, span) {
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

    /// Whether what a use gave in a replay, `got`, lies within the use's result `r`, binding
    /// the variables of `r` as `binds`. A class of `got`, as of the literal `1` of `(1, 2)`
    /// read by `p[0]`, stands for a value its carriers hold, so at a closed `r` it is passed
    /// as at a parameter of that type ([`Self::piece_into`]): `r` restricts its carriers,
    /// `int` in `if p[0] < 5 { p[0] } else { 0 }`, as the literal is restricted at `h(1)` of
    /// the same body. The cost is that of the pieces of `got`.
    fn gives_within(
        &mut self,
        got: &Ty,
        r: &Ty,
        binds: &mut Binds,
        what: &str,
        span: Span,
    ) -> bool {
        if self.sub(got, r, binds) {
            return true;
        }
        if r.dynamic || !r.vars.is_empty() {
            return false;
        }
        got.pieces().iter().all(|p| match self.class_of(p) {
            Some(_) => self.piece_into(p, r, what, span),
            None => self.sub(&p.ty(), r, binds),
        })
    }

    /// Checks that a value of `on` may be passed, by `what` at `span`, at a parameter of the
    /// closed type `ty`. `from` is the argument of the call being checked that the value came
    /// from, with the name of the parameter that takes it: the `is` repair tests it, in the
    /// program's code, bound first to that name where it is not a name a test narrows
    /// ([`test_repair`], MSG-is-repair-v).
    fn into(
        &mut self,
        on: &Ty,
        ty: &Ty,
        what: &str,
        from: Option<(Forwarded<'a>, Arc<str>)>,
        span: Span,
    ) {
        for piece in on.pieces() {
            let ok = self.piece_into(&piece, ty, what, span);
            if !ok {
                let p = self.show(&piece.ty());
                let why = on.of_piece(&piece).refused(ty);
                let held_fn = ty.held_function().is_some();
                let keeps = on.meets(ty);
                // After `is` a type stands as a union operand: a function type is parenthesized.
                let is_ty = self.text_in_union(ty);
                let ty = self.text(ty);
                let test = (from.as_ref()).and_then(|(f, p)| {
                    let code = self.code(Some(f.at))?;
                    let narrows = f.expr.is_some_and(|e| self.tested(e).is_some());
                    let call = self.call_parts(f.call, f.at);
                    let is = |a: &str| format!("{a} is {is_ty}");
                    Some(test_repair(p, &is, (code, narrows), call))
                });
                // `is` cannot test a type that holds a function, which shows no type at run
                // time (the elaborator refuses it), and a test that no value of `on` passes
                // leaves a branch that never runs: no test is offered for either.
                let test = match test {
                    _ if held_fn || !keeps => None,
                    Some(r) => Some(format!("{}{DECLARE}", repair_note(&r))),
                    None => Some(format!(
                        "repair: test the value with `is {is_ty}` first{DECLARE}"
                    )),
                };
                let mut menu = vec![format!("repair: pass {what} a value of {ty}")];
                menu.extend(test);
                menu.push(format!(
                    "repair: handle the values that are not {ty} with `else` or `match`"
                ));
                self.error_offering(
                    span,
                    format!("{what} does not take {p}, only {ty}{why}"),
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
            let (r, _) = self.apply(Label::Text(what), s, args, false, span);
            ok &= self.subtype(&r, &a.result);
        }
        ok || self.errors.len() > from
    }

    /// The values of `t` flow into class `k`: a class merges with it, a carrier restricts it
    /// to that carrier, and a tuple or a function to other values; atoms change nothing, and
    /// a value of type `_`, which may be any, does not flow. The value is the expression at
    /// `from`, which a rejection names as where it comes from.
    fn flow(&mut self, k: usize, t: &Ty, what: &str, span: Span, from: Span) -> bool {
        for p in t.pieces() {
            let ok = match (self.class_of(&p), p.carrier()) {
                (Some(j), _) => {
                    // The class the type names, not its root, so that the proof forest
                    // ([`Ck::link_proof`]) has the merge between the two the program joined.
                    let named = match &p {
                        Piece::Var(v) => class_id(v),
                        _ => None,
                    };
                    self.merge(k, named.unwrap_or(j), what, span)
                }
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
                let uses: Vec<Need> = self.classes[r]
                    .uses
                    .iter()
                    .map(|(_, n)| n.clone())
                    .collect();
                let v = Inflow {
                    ty: p.ty(),
                    at: span,
                    from,
                    class: k,
                };
                self.touch(r);
                self.classes[r].flowed.push(v.clone());
                for n in &uses {
                    self.check_on(n, &v.ty, span, Some(&v));
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
        let ExprKind::Binary(op @ (BinaryOp::Eq | BinaryOp::Ne), a, b) = &e.kind else {
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
        match *op == BinaryOp::Eq {
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
    /// an exponent of a type variable takes its ints at least 0, at each call where it is a
    /// parameter ([`Self::floor_on`]) and otherwise as listed ints, and a base of one, under an
    /// exponent not shown to be at least 0, takes no int at all (CHK-need-bound). Each
    /// rejection shows the exponent, and its repairs are written in the program's code
    /// ([`Self::power_repairs`]).
    fn exponent(&mut self, x: &Arg<'a>, n: &Arg<'a>, e: &'a Expr, span: Span) {
        let int = KType::int();
        let ns = &n.ty.set & &int;
        let x_int = !(&x.ty.set & &int).is_empty();
        let x_generic = !x.ty.vars.is_empty();
        let floor = !n.ty.vars.is_empty() && (x_int || x_generic);
        if !floor && ns.is_empty() {
            return;
        }
        let (ints, narrowed) = self.ints_here(e);
        let shown_at_least_zero = ints.is_subset(&at_least_zero());
        if floor && !shown_at_least_zero {
            match self.open_param(e) {
                // A trial application is undone; the application that stays records the need.
                Some(_) if self.trying => {}
                Some(id) => {
                    let domain = IntDomain {
                        what: "`^` on an int takes an exponent in int[0..]".into(),
                        below_two_pow: None,
                        name: "exponent".into(),
                    };
                    let need = Need {
                        on: Ty::empty(),
                        kind: NeedKind::InDomain {
                            domain,
                            param: 0,
                            via: None,
                        },
                        result: None,
                        span,
                    };
                    self.floor_on(id, need);
                }
                None => {
                    let p = self.power_use(x, n, e, span, None, false, Vec::new());
                    self.power_vars(&n.ty, &Arc::new(p), e.span);
                }
            }
        }
        if ns.is_empty() || shown_at_least_zero || listed_at_least_zero(&ns) {
            return;
        }
        let shown = match narrowed {
            true => format!("int{ints}"),
            false => self.show(&Ty::set(ns.clone())),
        };
        // Every value of the exponent below 0: a test of it leaves nothing to raise.
        let negative = ints.meet(&at_least_zero()).is_empty()
            || ns.ints_listed().is_some_and(|vs| {
                vs.iter()
                    .all(|v| v.surface_cmp(&Value::Int(0)) == Some(std::cmp::Ordering::Less))
            });
        let mut steps = Vec::new();
        if narrowed {
            steps.extend(self.deciding_notes(e));
        }
        steps.extend(self.refused_notes(e));
        let shown_here = self.narrowed_names(e);
        let mut derived = Vec::new();
        self.derive_narrowed(&[n.at.unwrap_or(span)], &shown_here, &mut derived);
        steps.extend(derived);
        let p =
            Arc::new(self.power_use(x, n, e, span, Some(shown.as_str().into()), negative, steps));
        if x_generic {
            self.power_vars(&x.ty, &p, x.at.unwrap_or(span));
        }
        if x_int {
            let mut steps = p.steps.to_vec();
            let base = self.show(&Ty::set(&x.ty.set & &int));
            // A base that is no literal has its own derivation, as `x` defined as `2`.
            if x.lit.is_none()
                && let Some(xs) = x.at
            {
                steps.extend(self.derive(&[xs]));
            }
            self.power_rejects(&p, (&base, &shown), steps, span);
        }
    }

    /// The need of the int `x ^ n` at `span`, whose exponent `n`, the expression `e`, is not
    /// shown to be at least 0: on the base, with the exponent as shown, whether every value
    /// of it is below 0 and the steps of its derivation; on the exponent, with `exponent`
    /// `None`. Its repairs are written from it when it fails ([`Self::power_repairs`]).
    #[allow(clippy::too_many_arguments)]
    fn power_use(
        &self,
        x: &Arg<'a>,
        n: &Arg<'a>,
        e: &'a Expr,
        span: Span,
        exponent: Option<Arc<str>>,
        negative: bool,
        steps: Vec<Note>,
    ) -> PowerUse {
        let param = (x.expr)
            .filter(|b| self.open_param(b).is_some())
            .and_then(|b| match &b.kind {
                ExprKind::Name(name) => Some(name.to_string().into()),
                _ => None,
            });
        PowerUse {
            exponent,
            base: x.at,
            exponent_at: n.at,
            at: span,
            negative,
            steps: steps.into(),
            param,
            tested: self.tested(e).map(Into::into),
            test: !negative && n.ty.vars.is_empty(),
            exponent_takes_float: n.lit.is_some() || !n.ty.vars.is_empty(),
            base_takes_float: !x.ty.vars.is_empty() || x.lit.is_some(),
            base_int: x.ty.numeric_carrier() == Some(Carrier::Int),
            base_var: match (x.ty.vars.len(), x.ty.vars.first()) {
                (1, Some(v)) => Some(v.clone()),
                _ => None,
            },
        }
    }

    /// The need `p` of an int `^` on each type variable of `t`, its base or its exponent
    /// (CHK-need-bound): on a class, recorded and checked on what flows into it
    /// ([`Self::power_on`]); on its type, if it has one by now. A variable of a signature
    /// stands for whatever type the caller passes, an int among them.
    fn power_vars(&mut self, t: &Ty, p: &Arc<PowerUse>, span: Span) {
        for v in &t.vars {
            let Some(r) = self.class_root(v) else {
                let what = match (&p.exponent, self.code(p.base)) {
                    (Some(_), Some(b)) => format!("the base `{b}`"),
                    (Some(_), None) => "the base".into(),
                    (None, _) => "the exponent".into(),
                };
                let note = format!(
                    "{what} has the type `{v}`, which stands for whatever type the caller passes \
                     and may be any int"
                );
                self.power_error(p, "int", note, span);
                continue;
            };
            match self.classes[r].resolved.clone() {
                Some(t) => self.power_on(&t, p, span),
                None => {
                    self.need(r, NeedKind::Power(p.clone()), false, span);
                }
            }
        }
    }

    /// Checks the need `p` of an int `^` on a value of `t` that is its base or its exponent
    /// (CHK-need-bound): a base holds no int, and an exponent holds no int or only ints listed
    /// at least 0.
    fn power_on(&mut self, t: &Ty, p: &Arc<PowerUse>, span: Span) {
        let ints = &t.set & &KType::int();
        let refused = match p.exponent {
            Some(_) => !ints.is_empty(),
            None => !ints.is_empty() && !listed_at_least_zero(&ints),
        };
        if refused {
            let shown = self.show(&Ty::set(ints));
            let note = match (&p.exponent, self.code(p.base)) {
                (Some(_), Some(b)) => format!("the base `{b}` is {shown} here"),
                (Some(_), None) => format!("the base is {shown} here"),
                (None, _) => format!("the exponent is {shown} here"),
            };
            self.power_error(p, &shown, note, span);
        }
        self.power_vars(t, p, span);
        if t.dynamic {
            self.any("`^` on an int", span);
        }
    }

    /// The error of the need `p` of an int `^` at `span`, where its base or its exponent, as
    /// `note` says, may be `shown`: the exponent the `^` shows, or else `shown`, then the
    /// steps of the exponent's derivation, or else of the value at `span`, and the repairs.
    fn power_error(&mut self, p: &PowerUse, shown: &str, note: String, span: Span) {
        let mut notes = vec![Note { span, text: note }];
        match p.exponent {
            Some(_) => notes.extend(p.steps.iter().cloned()),
            None => self.derive_into(&[span], &mut notes),
        }
        // On the base, `shown` is the base's ints; on the exponent, the exponent's.
        let (base, exponent) = match p.exponent.clone() {
            Some(e) => (shown.to_string(), e.to_string()),
            None => ("int".to_string(), shown.to_string()),
        };
        self.power_rejects(p, (&base, &exponent), notes, span);
    }

    /// The error at `span` of the int power `p`, whose base and exponent show as `shown`, with
    /// the notes `notes` and then its repairs ([`Self::power_repairs`]), the headline ending
    /// with the first one still offered ([`Msg::noted`]). A repair on a `rat` or a float
    /// changes the power's type, so it is checked where it is written ([`Self::power_swapped`]):
    /// left out where that rejects it, as `2r^k` in the exponent of `2^(2^k)`, and otherwise
    /// pending for the construct around it ([`Self::note_offered`]), which drops it where it
    /// rejects a `rat` or a float in that place, as `n + 2r^k` for an int `n`.
    ///
    /// Complexity tradeoff: one check of a construct per repair that changes the type, at
    /// most three, and only for a power that is rejected. The naive way, checking the whole
    /// statement again with each repair written in, costs the statement per repair, and a
    /// statement of n rejected powers O(n²); the construct's check costs its own operands'
    /// types alone, which are already known. Not seen: a use of the power after the
    /// construct that holds it, as a binding of it used as an int later, which the pending
    /// fixes of every construct do not see either ([`Pending`]).
    fn power_rejects(
        &mut self,
        p: &PowerUse,
        shown: (&str, &str),
        mut notes: Vec<Note>,
        span: Span,
    ) {
        let (mut kept, mut dropped) = (Vec::new(), false);
        for (r, swap) in self.power_repairs(p) {
            let note = Note {
                span,
                text: repair_note(&r),
            };
            match swap.map(|s| self.power_swapped(p, s)) {
                Some(Some(None)) => {
                    dropped = true;
                    continue;
                }
                Some(Some(got)) => self.note_offered(&note, got),
                _ => {}
            }
            kept.push((r, note));
        }
        // With the program's text, the headline's repair is written when the check ends
        // ([`Msg::written`]), so that one the construct around the power drops is not offered
        // there either; each repair stands for the power at `p.at` rewritten whole. Without
        // the text, the one repair is in words and the headline ends with it now.
        let first = match self.t.text {
            Some(_) => None,
            None => kept.first().map(|(r, _)| r),
        };
        let noted = (kept.iter())
            .filter(|_| first.is_none())
            .filter_map(|((code, tail), note)| {
                Some(NotedRepair {
                    note: note.clone(),
                    at: p.at,
                    fix: Rewrite::new(&[(p.at, code)], &"", code)?,
                    tail: tail.clone(),
                })
            })
            .collect();
        let (base, exponent) = shown;
        let text = power_message(
            (self.code(p.base), base),
            (self.code(p.exponent_at), exponent),
            p.negative,
            first,
        );
        let no_repair = kept.is_empty();
        notes.extend(kept.into_iter().map(|(_, note)| note));
        let mut m = Msg::noted(text, noted);
        // Every repair left out, the headline says that none is offered, as for a menu.
        m.dropped = dropped && no_repair;
        self.reject(None, span, m, notes);
    }

    /// Whether the repair of the int power `p` that writes a value of the carrier `c` as its
    /// operand `i`, the base 0 or the exponent 1, checks where it is written: as
    /// [`Self::written_with`] gives it, in the power itself where it is the construct being
    /// checked ([`Self::written`]), or else in that construct where the power is one of its
    /// operands, given the `rat` or float the repaired power is; `None` where it is neither, or
    /// a repair is being tried. One check of the construct.
    fn power_swapped(
        &mut self,
        p: &PowerUse,
        (i, c): (usize, Carrier),
    ) -> Option<Option<(Ty, Vec<Span>)>> {
        if self.trying {
            return None;
        }
        // A `rat` base to an int exponent gives a `rat`; a float anywhere gives a float.
        let result = match (i, c) {
            (0, Carrier::Rat) => Carrier::Rat,
            _ => Carrier::F64,
        };
        let Some(w) = self.written.clone() else {
            // The need of a literal's class is checked when the class takes its type, after
            // the walk, with no construct being checked: the power's value has the base's
            // class, whose carriers left then say whether every use of it takes the `rat` or
            // the float, as `2r^-3` does not in `2^-3 + k` for an int `k`.
            let r = self.class_root(p.base_var.as_deref()?)?;
            return (self.classes[r].mask & result.bit() == 0).then_some(None);
        };
        if w.span == p.at && matches!(w.form, Construct::Binary(BinaryOp::Pow, _)) {
            let at = [p.base, p.exponent_at][i];
            let with = Arg {
                at,
                ..Arg::of(Ty::carrier(c))
            };
            return self.written_with(&w.form.what(), w.span, i, with);
        }
        let j = (w.args.iter()).position(|a| a.as_ref().and_then(|a| a.at) == Some(p.at))?;
        let with = Arg {
            at: Some(p.at),
            ..Arg::of(Ty::carrier(result))
        };
        self.written_with(&w.form.what(), w.span, j, with)
    }

    /// The repairs of the int power `p`, whose exponent is not shown to be at least 0, each
    /// the power rewritten in full in the program's code: on floats, which take a negative
    /// exponent, with an int literal base or exponent written as a float literal, or with a
    /// base parameter declared a float; where the exponent may be at least 0 and is no class
    /// of literals, which a test does not narrow, a test of it, of a name bound in the body or
    /// of a new name that holds it ([`fresh`]); and, last, on a `rat`, exact for an exponent
    /// of either sign, with an int base written `2r` for the literal `2` and `rat(x)` for
    /// anything else, a cast that cannot fail. No repair casts an int to a float: `f64(k)` may
    /// fail, with `#inexact`. Without the program's text, the test in words. Each repair on a
    /// `rat` or a float comes with the operand it rewrites, the base 0 or the exponent 1, and
    /// the carrier it writes there, which [`Self::power_swapped`] checks.
    fn power_repairs(&self, p: &PowerUse) -> Vec<(Repair, Option<(usize, Carrier)>)> {
        let (test, span) = (p.test, p.at);
        let words = || match test {
            true => vec![(
                (
                    "if … >= 0 { … } else { … }".to_string(),
                    ", with the exponent tested and raised to inside the branch".to_string(),
                ),
                None,
            )],
            false => Vec::new(),
        };
        let (Some(xs), Some(ns)) = (p.base, p.exponent_at) else {
            return words();
        };
        let (Some(bt), Some(et), Some(power)) = (
            self.code(Some(xs)),
            self.code(Some(ns)),
            self.code(Some(span)),
        ) else {
            return words();
        };
        if xs.end > ns.start {
            return words();
        }
        // The power with each part at a span written as its text, the parts in the order of
        // the text and inside the power.
        let rewrite = |parts: &[(Span, &str)]| -> Option<String> {
            let src = self.t.text?;
            let mut out = String::new();
            let mut at = span.start;
            for (s, with) in parts {
                out.push_str(src.get(at..s.start)?);
                out.push_str(with);
                at = s.end;
            }
            out.push_str(src.get(at..span.end)?);
            Some(out)
        };
        // An exponent that is a literal or holds a type variable takes a float as it is.
        let takes_float = p.exponent_takes_float;
        let mut out = Vec::new();
        let param = p.param.as_deref();
        let pass = match &param {
            Some(b) => format!(", and pass a float as `{b}` at each call"),
            None => String::new(),
        };
        match &param {
            Some(b) if takes_float => {
                out.push(((format!("{b}: f64"), pass.clone()), Some((0, Carrier::F64))));
            }
            None if takes_float && int_literal(bt) => {
                if let Some(p) = rewrite(&[(xs, &format!("{bt}.0f64"))]) {
                    out.push(((p, String::new()), Some((0, Carrier::F64))));
                }
            }
            _ => {}
        }
        // The exponent is written with its carrier, `2^-3.0f64`: an unfixed `-3.0` takes none
        // in an operation on literals alone, `c = 2^-3.0` at the top level, and `f64` is the
        // carrier [`Self::power_swapped`] checks.
        if p.base_takes_float
            && int_literal(et.strip_prefix('-').unwrap_or(et))
            && let Some(p) = rewrite(&[(ns, &format!("{et}.0f64"))])
        {
            out.push(((p, pass), Some((1, Carrier::F64))));
        }
        if test {
            match &p.tested {
                Some(k) => out.push((
                    (
                        format!("if {k} >= 0 {{ {power} }} else {{ … }}"),
                        String::new(),
                    ),
                    None,
                )),
                None => {
                    // `exponent = exponent - 1` would define the name in terms of itself.
                    let q = fresh("exponent", &[et, power]);
                    if let Some(p) = rewrite(&[(ns, &q)]) {
                        let et = unparen(et);
                        out.push((
                            (
                                format!("{q} = {et}; if {q} >= 0 {{ {p} }} else {{ … }}"),
                                String::new(),
                            ),
                            None,
                        ));
                    }
                }
            }
        }
        // The exact power: a `rat` takes an int exponent of either sign, and an int widens to
        // a `rat` with no failure, an int literal by its `r` suffix and anything else by `rat`.
        // A base whose type holds a variable and that is no int literal is left: `rat` of it
        // may be a float, which `rat` may refuse with `#invalid`.
        if int_literal(bt) || p.base_int {
            let base = match int_literal(bt) {
                true => format!("{bt}r"),
                false => format!("rat({})", unparen(bt)),
            };
            if let Some(p) = rewrite(&[(xs, &base)]) {
                out.push(((p, String::new()), Some((0, Carrier::Rat))));
            }
        }
        out
    }

    /// The program's code at `at`, if the checker has the program's text.
    fn code(&self, at: Option<Span>) -> Option<&'a str> {
        let at = at?;
        self.t.text?.get(at.start..at.end)
    }

    /// The code of `callee`, the callee of the call at `span`, as the program writes it: with
    /// the parentheses around it, which the tree does not keep, as `(if c { f } else { g })`;
    /// none when the checker has no text or the code runs over more than one line, which a
    /// headline cannot show.
    fn callee_code(&self, callee: &Expr, span: Span) -> Option<&'a str> {
        let text = self.t.text?;
        // Each `(` between the call's start and the callee's opens one pair around it.
        let opened = text
            .get(span.start..callee.span.start)?
            .matches('(')
            .count();
        let mut end = callee.span.end;
        for _ in 0..opened {
            let rest = text.get(end..)?;
            let blank = rest.len() - rest.trim_start().len();
            end += blank + rest[blank..].strip_prefix(')').map(|_| 1)?;
        }
        text.get(span.start..end).filter(|c| !c.contains('\n'))
    }

    /// The name `e` is, where it is bound once, so that a test of it narrows it.
    fn tested(&self, e: &Expr) -> Option<String> {
        let ExprKind::Name(name) = &e.kind else {
            return None;
        };
        matches!(self.t.res.uses.get(&e.span), Some(Ref::Bound(ids)) if ids.len() == 1)
            .then(|| name.to_string())
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
            let domain = domain_text(d);
            let why = format!("the checker cannot show that this value lies in {domain}");
            self.domain_error(d, &shown, why, span);
        }
        self.no_int_vars(t, d, span);
        if t.dynamic {
            self.any(&d.what, span);
        }
    }

    /// The error of a value at `span`, of the type `shown`, that the checker cannot show lies
    /// in the ints `d` its use takes, for the reason `why`: the headline shows the value's code
    /// and type and the test that keeps it in `d`, of a new name `d.name` bound to it. The value
    /// is of a type variable here, or of a class resolved since, and a test narrows only a name
    /// whose values are all ints, so the repair declares `int` each parameter it is computed from.
    fn domain_error(&mut self, d: &IntDomain, shown: &str, why: String, span: Span) {
        let mut notes = self.derive(&[span]);
        notes.push(Note { span, text: why });
        let code = self.code(Some(span));
        let within = Within::of(d);
        let first = code.map(|c| {
            let (test, _) = test_repair(&d.name, &|a| within.test(a), (c, false), None);
            let tail = format!(
                ", with each parameter in `{}` declared `int` and `{}` passed inside the branch",
                unparen(c),
                fresh(&d.name, &[c])
            );
            (test, tail)
        });
        let pass = format!("repair: pass as `{}` a value in {}", d.name, domain_text(d));
        let menu = (first.iter().map(repair_note)).chain([pass]);
        notes.extend(menu.map(|text| Note { span, text }));
        let piece = format!("{} : {shown}", code.unwrap_or("…"));
        self.error_with(span, domain_message(&d.what, &piece, first.as_ref()), notes);
    }

    /// The need of [`Self::no_int`] on each type variable of `t`: on a class, recorded and
    /// checked on what flows into it; on its type, if it has one by now.
    fn no_int_vars(&mut self, t: &Ty, d: &IntDomain, span: Span) {
        for v in &t.vars {
            let Some(r) = self.class_root(v) else {
                let why = format!(
                    "`{v}` stands for whatever type the caller passes, which may be any int"
                );
                self.domain_error(d, v.as_ref(), why, span);
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
        from: Option<&[Option<Forwarded<'a>>]>,
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
                name: (*p).into(),
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
                    let message = match self.code(Some(span)) {
                        Some(call) => format!("{takes}: `{call}` leaves out `{p}`."),
                        None => format!("{takes}: this call leaves out `{p}`."),
                    };
                    let mut notes = chain();
                    notes.extend(
                        [
                            format!(
                                "`{p}` takes its default, which the checker cannot show lies \
                                 in {dom}"
                            ),
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
                    let shown = self.show(&Ty::set(ns.clone()));
                    // The argument of the call around that gave the value, as `-1` in
                    // `ap(h, -1)` (MSG-forwarded-repair): the message and the repairs name it,
                    // not `p`, which belongs to the function passed, nor the parameter of the
                    // function called that passed it on.
                    let given = (from.and_then(|f| f.get(*param).copied().flatten()))
                        .and_then(|f| Some((f, self.code(Some(f.at))?)));
                    let Some((f, code)) = given else {
                        let mut notes = chain();
                        notes.push(outside(domain, span));
                        let (first, repairs) =
                            passed_repairs(&p, &Within::of(domain), None, None, false, None, span);
                        notes.extend(repairs);
                        let piece = format!("{p} : {shown}");
                        let message = domain_message(&takes, &piece, first.as_ref());
                        self.error_with(span, message, notes);
                        continue;
                    };
                    let mut notes = vec![Note {
                        span: f.at,
                        text: format!("`{code}` reaches {what} as `{p}`"),
                    }];
                    notes.extend(chain());
                    notes.push(outside(domain, span));
                    let outside_all = (ns.ints_listed())
                        .is_some_and(|vs| vs.iter().all(|v| !value_in(domain, v)));
                    let arg =
                        Some(code).map(|c| (c, f.expr.is_some_and(|e| self.tested(e).is_some())));
                    let call = self.call_parts(f.call, f.at);
                    let (first, repairs) = passed_repairs(
                        &p,
                        &Within::of(domain),
                        arg,
                        call,
                        outside_all,
                        Some(code),
                        f.call,
                    );
                    notes.extend(repairs);
                    let piece = self.annotated(f.call, f.at, &shown);
                    self.error_with(span, domain_message(&takes, &piece, first.as_ref()), notes);
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
            notes.extend(self.refused_notes(e));
            self.derive_into(&[at], &mut notes);
            let outside_all = match &r.values {
                Some(vs) => vs.iter().all(|v| !value_in(domain, v)),
                None => r.ints.meet(&at_least_zero()).is_empty(),
            };
            let arg = self.code(Some(at)).map(|c| (c, self.tested(e).is_some()));
            let call = self.call_parts(span, at);
            notes.extend(chain());
            notes.push(outside(domain, span));
            let (first, repairs) =
                passed_repairs(&p, &Within::of(domain), arg, call, outside_all, None, span);
            notes.extend(repairs);
            let piece = self.annotated(span, at, shown);
            self.error_with(span, domain_message(&takes, &piece, first.as_ref()), notes);
        }
    }

    /// The code at `span` with its part at `at` annotated with the type `shown`, as
    /// `popCount(n : int)`; the part alone where `at` does not lie in `span`, and `… : int`
    /// where the checker has no code. A literal whose type shows as the literal itself is
    /// annotated `int`, as `bitAnd(-1 : int, 1)`.
    fn annotated(&self, span: Span, at: Span, shown: &str) -> String {
        let part = match self.code(Some(at)) {
            Some(c) if c == shown => format!("{c} : int"),
            Some(c) => format!("{c} : {shown}"),
            None => return format!("… : {shown}"),
        };
        match self.call_parts(span, at) {
            Some((_, before, after)) => format!("{before}{part}{after}"),
            None => part,
        }
    }

    /// The code at `span` with each of its parts `parts`, in order and apart, annotated with
    /// its type, as `funnelShl(3, 5, n : int[0..9], width: w : int[0..8])`; the first part
    /// alone annotated ([`Ck::annotated`]) where the checker lacks the code of one of them.
    fn annotated_parts(&self, span: Span, parts: &[(Span, &str)]) -> String {
        let whole = (self.t.text)
            .zip(self.code(Some(span)))
            .and_then(|(src, _)| {
                let mut out = String::new();
                let mut from = span.start;
                for &(at, shown) in parts {
                    if at.start < from || span.end < at.end {
                        return None;
                    }
                    let c = self.code(Some(at))?;
                    out.push_str(src.get(from..at.start)?);
                    match c == shown {
                        true => out.push_str(&format!("{c} : int")),
                        false => out.push_str(&format!("{c} : {shown}")),
                    }
                    from = at.end;
                }
                out.push_str(src.get(from..span.end)?);
                Some(out)
            });
        whole.unwrap_or_else(|| self.annotated(span, parts[0].0, parts[0].1))
    }

    /// The call at `span` as written, and its code before and after its argument at `at`.
    fn call_parts(&self, span: Span, at: Span) -> Option<Call<'a>> {
        if at.start < span.start || span.end < at.end {
            return None;
        }
        let src = self.t.text?;
        let (before, after) = (src.get(span.start..at.start)?, src.get(at.end..span.end)?);
        Some((self.code(Some(span))?, before, after))
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
    fn compare(&mut self, op: BinaryOp, x: Arg<'a>, y: Arg<'a>, span: Span) -> Ty {
        let what = Label::Operator(Operator::Binary(op));
        let scalars = x.ty.tuples.is_empty() && y.ty.tuples.is_empty();
        // Two numbers of no common carrier, each written in the program and neither a literal,
        // as `x[1] < y[1]` of an `int` and a `rat`, get the message of two tuples' components
        // that do not compare, the pair as code with its types and the repair the comparison
        // rewritten (DESIGN.md sec:diagnostics, "A short headline, the detail in the notes"):
        // the code of each operand stands for its name. A literal gets its own forms, which
        // the application offers, and an operand of a class or a type variable is checked
        // there too (MSG-concise-no-common-carrier).
        // An operand read at a carrier ([`Self::read_whole`]), as `g(b, x)` of type `1 | f64`,
        // stands for the carrier it holds whole, at which its listed values are read: `g(b, x)
        // < gr(b, r)` with `gr(b, r)` of type `1 | rat` compares an `f64` with a `rat` (DESIGN.md
        // step L1.26a, rule 3).
        let sided = |a: &Arg<'a>| match self.unordered_operand(a) {
            Some(code) => Some((code, a.ty.without_loose())),
            None => {
                let c = self.read_whole(a)?;
                let code = self.code(a.at).filter(|c| !c.contains('\n'))?;
                Some((code, Ty::carrier(c)))
            }
        };
        let sides = [&x, &y].map(|a| scalars.then(|| sided(a)).flatten());
        if let [Some((cx, a)), Some((cy, b))] = sides
            && no_common_carrier(&a, &b)
        {
            let out = self.passing(&x.ty, what.text(), span, x.at);
            let out = out.union(&self.passing(&y.ty, what.text(), span, y.at));
            let sides = OrderSides {
                names: [Some(cx), Some(cy)],
                ats: [x.at, y.at],
                plain: [a.atoms().is_empty(), b.atoms().is_empty()],
                exact: [self.exact_in_f64(&x), self.exact_in_f64(&y)],
            };
            self.components(what, &sides, &a, &b, span);
            return out.union(&Ty::carrier(Carrier::Bool));
        }
        if scalars {
            return self
                .apply(
                    what,
                    &op_sig(Operator::Binary(BinaryOp::Lt)),
                    vec![Some(x), Some(y)],
                    true,
                    span,
                )
                .0;
        }
        let out = self.passing(&x.ty, what.text(), span, x.at);
        let out = out.union(&self.passing(&y.ty, what.text(), span, y.at));
        let (a, b) = (x.ty.without_loose(), y.ty.without_loose());
        // An operand with no value: nothing is compared, and the comparison gives no value, but
        // each value of the other operand is still checked as `<` takes it.
        match (a.is_empty(), b.is_empty()) {
            (true, _) => self.compared_alone(what, &b, true, span),
            (_, true) => self.compared_alone(what, &a, false, span),
            _ => {
                let tables = self.t;
                let name = |at: Option<Span>| match at.and_then(|at| self.seen.get(&at)) {
                    Some((_, Src::Name(id))) => Some(tables.res.binders[*id].name.as_str()),
                    _ => None,
                };
                let sides = OrderSides {
                    names: [name(x.at), name(y.at)],
                    ats: [x.at, y.at],
                    plain: [a.atoms().is_empty(), b.atoms().is_empty()],
                    exact: [false; 2],
                };
                self.components(what, &sides, &a, &b, span);
                return out.union(&Ty::carrier(Carrier::Bool));
            }
        }
        out
    }

    /// The code of `a`, an operand of an ordering, where the message of two numbers that do not
    /// compare names it as code ([`Ck::compare`]): an operand written on one line, of numbers of
    /// known carriers alone apart from atoms, no class, type variable or unknown, and not a
    /// literal, whose own forms the application offers instead. Nor an operand that holds
    /// literals, or that the application may read at the other operand's carrier
    /// ([`Self::readable`], asked before [`lists_a_number`] as in [`Self::read_arg`]), as `g(c)`
    /// of type `1 | 2` or `1 | f64`.
    fn unordered_operand(&self, a: &Arg<'a>) -> Option<&'a str> {
        let t = &a.ty;
        let read =
            a.branches.is_some() || a.parts.is_some() || (self.readable(a) && lists_a_number(t));
        if a.lit.is_some() || read || t.dynamic || !t.vars.is_empty() || !only_numbers(t) {
            return None;
        }
        if self.class_of_ty(&t.without_loose()).is_some() {
            return None;
        }
        let at = a.at?;
        if let Some((_, Src::Other(e))) = self.seen.get(&at)
            && rat_forms(e, self.t.text).is_some()
        {
            return None;
        }
        self.code(Some(at)).filter(|c| !c.contains('\n'))
    }

    /// Checks each value of `t`, an operand of the ordering `what` whose other operand has no
    /// value, the first operand where `none_first` does not hold: each number, string or bool
    /// at the top or in a component of a tuple at any depth against the arrows of `<`, beside
    /// `Never`, so that a function among them is rejected. Atoms pass. A row shared by many
    /// paths is visited once, so the check is linear in the rows of `t`.
    fn compared_alone(&mut self, what: Label<'_>, t: &Ty, none_first: bool, span: Span) {
        let sig = op_sig(Operator::Binary(BinaryOp::Lt));
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
    /// component as far as the shorter goes, since a proper prefix comes first. `sides` names
    /// the operands of the comparison `what`, whose values `a` and `b` are, for the message.
    ///
    /// Two tuples both reach position `i` exactly when each has more than `i` components, so
    /// the pairs of components met at `i` are every component `i` of `a`'s tuples against
    /// every one of `b`'s: the check reads the union of each side's, once, not each pair of
    /// tuples, which cost `n²` pairs for `n` tuples a side and `n³` for tuples of lengths 1 to
    /// `n`. A pair of component types met again, as through rows shared by many paths, is not
    /// read again: `n` levels that each hold the one below twice cost `n`, not `2^n`
    /// (CHK-components-pairs). The pairs are checked on a heap stack in the order a recursion
    /// would: a pair's own pieces, then its components position by position, then its rest.
    /// Each pair read keeps the pair it was met in and its position there, so that a pair that
    /// does not compare is reported with the place that reaches it ([`Ck::not_compared`]).
    ///
    /// Complexity tradeoff: naive version, every pair of tuples read and each pair's
    /// components recursively, with no visited set: O(n²) pairs for `n` tuples a side (`x < x`
    /// over 800 shapes took 39.9 s), O(n³) for lengths 1 to `n`, `2^n` through shared rows.
    /// Used: one union of each side's components per position and a set of the pairs of
    /// component types read, O(n) in the types read. Tradeoffs: the set's memory, one pair of
    /// types per pair read, and an entry of the list of pairs met, one position and one index
    /// each, from which the place of a failure is read back only when one is found; a failure
    /// is reported once for the two unions met, as for `x < y` with `x: int | f64`, not once
    /// per pair of tuples. COMPLEXITY.md row F140.
    fn components(&mut self, what: Label<'_>, sides: &OrderSides, a: &Ty, b: &Ty, span: Span) {
        enum Step {
            Pair(usize),
            Rest(usize, Box<(Ty, Ty)>),
        }
        let rest = |t: &Ty| Ty {
            tuples: Vec::new(),
            ..t.without_atoms()
        };
        let mut seen = HashSet::from([(a.clone(), b.clone())]);
        let mut met = vec![Met {
            up: usize::MAX,
            at: 0,
            ty: [a.clone(), b.clone()],
        }];
        let mut todo = vec![Step::Pair(0)];
        while let Some(step) = todo.pop() {
            let k = match step {
                Step::Rest(k, rests) => {
                    let (x, y) = *rests;
                    let mark = self.mark();
                    let args = vec![Some(Arg::of(x.clone())), Some(Arg::of(y.clone()))];
                    self.apply(
                        what,
                        &op_sig(Operator::Binary(BinaryOp::Lt)),
                        args,
                        true,
                        span,
                    );
                    if self.errors.len() > mark.errors {
                        // The arrows of `<` alone say only that none takes the two; the
                        // message names the place and the repairs instead.
                        self.undo(&mark);
                        self.not_compared(what, sides, &met, k, Unordered::Kinds(x, y), span);
                    }
                    continue;
                }
                Step::Pair(k) => k,
            };
            let [a, b] = &met[k].ty;
            // Each piece refused is named once, since a pair here may join many pairs of tuples.
            let (mut refused, mut said) = ([Vec::new(), Vec::new()], HashSet::new());
            for (s, t) in [(a, b), (b, a)] {
                let atoms = !s.atoms().is_empty();
                for p in t.pieces() {
                    let ok = match self.class_of(&p) {
                        Some(k) if !s.tuples.is_empty() => {
                            self.restrict(k, OTHER, what.text(), span)
                        }
                        Some(_) => true,
                        None => match &p {
                            Piece::Dyn => false,
                            Piece::Var(_) | Piece::Tuple(_) => true,
                            _ if !s.tuples.is_empty() => false,
                            _ => !atoms || p.is_atoms() || p.carrier().is_none(),
                        },
                    };
                    if !ok {
                        let with = usize::from(s.tuples.is_empty());
                        let p = self.text(&p.ty());
                        if said.insert((with, p.clone())) {
                            refused[with].push(p);
                        }
                    }
                }
            }
            if refused.iter().any(|r| !r.is_empty()) {
                self.not_compared(what, sides, &met, k, Unordered::Refused(refused), span);
                continue;
            }
            let (x, y) = (rest(a), rest(b));
            // The components at each position, of the tuples of each side long enough to have one.
            let mut at: Vec<[Vec<&Ty>; 2]> = Vec::new();
            for (side, t) in [a, b].into_iter().enumerate() {
                for row in &t.tuples {
                    if at.len() < row.len() {
                        at.resize_with(row.len(), Default::default);
                    }
                    for (i, c) in row.iter().enumerate() {
                        at[i][side].push(c);
                    }
                }
            }
            let pairs: Vec<_> = (at.into_iter().enumerate())
                .filter(|(_, [s, t])| !s.is_empty() && !t.is_empty())
                .map(|(i, [s, t])| (i, [Ty::union_all(s), Ty::union_all(t)]))
                .collect();
            if !x.is_empty() && !y.is_empty() {
                todo.push(Step::Rest(k, Box::new((x, y))));
            }
            for (i, [s, t]) in pairs.into_iter().rev() {
                if seen.insert((s.clone(), t.clone())) {
                    todo.push(Step::Pair(met.len()));
                    met.push(Met {
                        up: k,
                        at: i,
                        ty: [s, t],
                    });
                }
            }
        }
    }

    /// Whether each value of `a` compares with each of `b` under the ordering `what`
    /// ([`Ck::components`]), tried and undone.
    fn compares(&mut self, what: Label<'_>, a: &Ty, b: &Ty, span: Span) -> bool {
        let (mark, was) = (self.mark(), self.trying);
        self.trying = true;
        let sides = OrderSides {
            names: [None; 2],
            ats: [None; 2],
            plain: [false; 2],
            exact: [false; 2],
        };
        self.components(what, &sides, a, b, span);
        let ok = self.errors.len() == mark.errors;
        self.trying = was;
        self.undo(&mark);
        ok
    }

    /// Rejects the ordering `what`, whose operands `sides` names, at the pair `met[k]` of
    /// values that do not compare for the reason `why`: a headline that shows the pair as code
    /// annotated with its types and ends with the first repair, then a short note for each
    /// step that reaches the pair through tuples compared component by component, the reason,
    /// and the repairs (DESIGN.md sec:diagnostics, "A short headline, the detail in the
    /// notes"). A repair casts one side's numbers to the other's kind with a cast that cannot
    /// fail or lose information ([`cast_widening`]), or compares a component of a tuple met by
    /// a value that is not one; each is tried before it is offered, and each is written as the
    /// whole comparison rewritten, `(x[0], rat(x[1])) < y`, so it is offered only where each
    /// level on the way holds one tuple shape, which one tuple written out can stand for.
    ///
    /// Complexity tradeoff: the earlier message named the place and what to write there,
    /// `rat(x[1][0])` in place of `x[1][0]`, O(d) in the depth `d`; a repair is now the whole
    /// comparison rewritten, which writes every other component of each tuple on the way with
    /// the indices that reach it, O(w·d²) characters for `d` levels of `w` components, the size
    /// of the expression the program then holds, so no shorter text states it. It is written
    /// into one buffer, outer levels first, so no level's text is copied again. A step names
    /// only the position it goes down by, so the notes are O(d) beside the repairs. Each repair
    /// is a trial of [`Ck::components`] on the pair, at most three casts a side and one trial
    /// per component of a tuple met by a value that is not one, which is a tuple of none; so
    /// each trial reads only pieces that are not tuples. COMPLEXITY.md row F140.
    fn not_compared(
        &mut self,
        what: Label<'_>,
        sides: &OrderSides,
        met: &[Met],
        k: usize,
        why: Unordered,
        span: Span,
    ) {
        use std::fmt::Write as _;
        const ENDS: [&str; 2] = ["left", "right"];
        if self.trying {
            // A trial only counts the errors.
            self.error_with(
                span,
                format!("{what} does not compare its operands"),
                Vec::new(),
            );
            return;
        }
        // The pairs met on the way from the operands down to `met[k]`, outermost first.
        let mut up = Vec::new();
        let mut i = k;
        while met[i].up != usize::MAX {
            i = met[i].up;
            up.push(i);
        }
        up.reverse();
        // The position each pair below the operands lies at in the pair above it: none when
        // `met[k]` is the operands themselves.
        let below = (up.iter().skip(1).chain([&k])).filter(|_| !up.is_empty());
        let path: Vec<usize> = below.map(|&i| met[i].at).collect();
        let path = &path[..];
        let ty = &met[k].ty;
        let op = match what {
            Label::Operator(o) => o.as_str(),
            Label::Text(_) | Label::SumPlus(_) => what.text().trim_matches('`'),
        };
        // The value at `p` on side `s`, as code where the operand's text is known.
        let code = |s: usize, p: &[usize]| sides.names[s].map(|c| format!("{c}{}", Place(p)));
        let label = |s: usize, p: &[usize]| match (code(s, p), p) {
            (Some(c), _) => format!("`{c}`"),
            (None, []) => format!("the {} operand", ENDS[s]),
            (None, _) => format!("component `{}` of the {} operand", Place(p), ENDS[s]),
        };
        // Side `s` written again with the value at `path` written as `leaf`: as `leaf` itself at
        // the operands, else as a tuple at each level on the way, each other component read
        // from the operand; none where a level holds anything but one tuple shape, or where
        // the operand may be an atom, which no tuple written out holds.
        let rewrite = |s: usize, leaf: &str| -> Option<String> {
            let base = sides.names[s]?;
            if path.is_empty() {
                return Some(leaf.to_string());
            }
            if !sides.plain[s] {
                return None;
            }
            let rows = (up.iter().map(|&i| &met[i].ty[s]))
                .map(|t| match &t.tuples[..] {
                    [row] if t.pieces().len() == 1 => Some(row.len()),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()?;
            let mut out = String::new();
            let other = |out: &mut String, j: usize, c: usize| {
                let _ = write!(out, "{base}{}[{c}]", Place(&path[..j]));
            };
            for (j, &at) in path.iter().enumerate() {
                out.push('(');
                for c in 0..at {
                    other(&mut out, j, c);
                    out.push_str(", ");
                }
            }
            out.push_str(leaf);
            for (j, &at) in path.iter().enumerate().rev() {
                for c in at + 1..rows[j] {
                    out.push_str(", ");
                    other(&mut out, j, c);
                }
                if rows[j] == 1 {
                    out.push(',');
                }
                out.push(')');
            }
            Some(out)
        };
        // The repairs, each tried on the pair and written as the whole comparison: a cast of
        // one side's values that are not tuples that cannot fail or lose information on any of
        // them, or a component of one side that is one tuple shape, against the other side,
        // which holds no tuple.
        let whole = |s: usize, side: String| {
            let other = sides.names[1 - s]?;
            Some(match s {
                0 => format!("{side} {op} {other}"),
                _ => format!("{other} {op} {side}"),
            })
        };
        let mut repairs = Vec::new();
        if let Unordered::Kinds(x, y) = &why {
            let rests = [x, y];
            for (s, rest) in rests.into_iter().enumerate() {
                for w in ["int", "rat", "f64"] {
                    let exact = path.is_empty() && sides.exact[s];
                    let Some(r) = widening(w, rest, exact).filter(|r| r != rest) else {
                        continue;
                    };
                    let Some(at) = code(s, path) else {
                        continue;
                    };
                    let pair = if s == 0 { [&r, y] } else { [x, &r] };
                    // Tried first: the rewrite is written only for a repair that is offered.
                    if self.compares(what, pair[0], pair[1], span)
                        && let Some(text) =
                            rewrite(s, &format!("{w}({at})")).and_then(|t| whole(s, t))
                    {
                        repairs.push(text);
                    }
                }
            }
        }
        for s in 0..2 {
            let other = &ty[1 - s];
            let row = match &ty[s].tuples[..] {
                [row] if ty[s].pieces().len() == 1 && other.tuples.is_empty() => row,
                _ => continue,
            };
            let Some(at) = code(s, path) else {
                continue;
            };
            for (i, c) in row.iter().enumerate() {
                if c.tuples.is_empty()
                    && self.compares(what, c, other, span)
                    && let Some(text) = rewrite(s, &format!("{at}[{i}]")).and_then(|t| whole(s, t))
                {
                    repairs.push(text);
                }
            }
        }
        let shown = ty.each_ref().map(|t| self.text(t));
        let (l, r) = (label(0, path), label(1, path));
        let (l0, r0) = (label(0, &[]), label(1, &[]));
        // Each value of the pair with its type: as code where the operand is a name, `x[1] : int`,
        // else named, component `[1]` of the right operand (`true`).
        let typed = |s: usize| match code(s, path) {
            Some(c) => format!("`{c} : {}`", shown[s]),
            None => format!("{} (`{}`)", label(s, path), shown[s]),
        };
        // The comparison as written, where the source is known and on one line.
        let written = (self.t.text)
            .and_then(|t| t.get(span.start..span.end))
            .filter(|w| !w.contains('\n'));
        // The pair as code with its types, `x[1] : int < y[1] : rat`, and the comparison it
        // lies in where it is not the operands themselves.
        let pair = fmt::from_fn(|f| {
            match (code(0, path), code(1, path)) {
                (Some(a), Some(b)) => write!(f, "`{a} : {} {op} {b} : {}`", shown[0], shown[1])?,
                _ => write!(f, "{} with {}", typed(0), typed(1))?,
            }
            match (path, written, code(0, path).zip(code(1, path))) {
                ([], _, Some(_)) | (_, None, _) => Ok(()),
                (_, Some(w), _) => write!(f, " in `{w}`"),
            }
        });
        // Two operands of one type, as `x < x` with `x: (int | f64,)`, are not of unequal types:
        // two of the values that type holds do not compare.
        let head = match shown[0] == shown[1] {
            true => "Cannot compare the values of one type with each other",
            false => "Cannot compare unequal types",
        };
        let message = match repairs.first() {
            Some(first) => format!("{head}: {pair}. Try `{first}` instead."),
            None => format!("{head}: {pair}."),
        };
        // An operand compared with itself, as `x < x`, is named once.
        let one = l == r;
        // With no repair to write, the type of an operand has to change.
        let change = match (one, path) {
            (true, []) => {
                format!("change the type of {l} so that its values compare with each other")
            }
            (true, _) => {
                format!("change the type of {l0} so that the values of {l} compare with each other")
            }
            (false, []) => format!("change the type of {l} or {r} so that the two compare"),
            (false, _) => format!("change the type of {l0} or {r0} so that {l} and {r} compare"),
        };
        let types = match one && shown[0] == shown[1] {
            true => typed(0),
            false => format!("{} with {}", typed(0), typed(1)),
        };
        let mut notes = self.derive(&sides.ats.into_iter().flatten().collect::<Vec<_>>());
        let mut step = |text: String| notes.push(Note { span, text });
        if let Some((&last, inner)) = path.split_last() {
            step(format!(
                "{what} compares two tuples component by component, as far as the shorter goes"
            ));
            for i in inner {
                step(format!(
                    "components `[{i}]` are tuples, compared the same way"
                ));
            }
            step(format!("{what} compares components `[{last}]`: {types}"));
        }
        step(match &why {
            Unordered::Kinds(x, y) => {
                let mut text = format!(
                    "{what} compares only two numbers of one kind or two values of one other kind"
                );
                if x != &ty[0] || y != &ty[1] {
                    let (x, y) = (self.text(x), self.text(y));
                    let _ = write!(text, ", not `{x}` with `{y}`");
                }
                text
            }
            Unordered::Refused(refused) => {
                let mut text = String::new();
                for (ps, with) in refused.iter().zip(["a tuple", "an atom"]) {
                    if ps.is_empty() {
                        continue;
                    }
                    if !text.is_empty() {
                        text.push_str("; ");
                    }
                    let _ = write!(text, "{what} compares {with} only with {with}, not ");
                    for (j, p) in ps.iter().enumerate() {
                        if j > 0 {
                            text.push_str(if j + 1 == ps.len() { " or " } else { ", " });
                        }
                        let _ = write!(text, "`{p}`");
                    }
                }
                text
            }
        });
        for text in &repairs {
            step(format!("repair: `{text}`"));
        }
        if repairs.is_empty() {
            step(format!("repair: {change}"));
        }
        self.error_with(span, message, notes);
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
        written: [Option<Rc<[Part<'a>]>>; 2],
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
            // A pair with no tuple on either side is checked each time as well: it pushes no
            // pair, so `seen` neither ends the walk nor saves more than its own check, whose
            // errors and needs are kept once (`errors.dedup`, `need`'s `known`).
            // Complexity tradeoff (COMPLEXITY.md F113): looking such a pair up in `seen` costs
            // the size of its sets when an equal pair made apart is there, as the components
            // `0 | 1 | ... | n` at the two ends of `(n, 0.5f64, n)` in a chain of `n` tuple
            // `min`s are, so `n` per link and `n^2` for the chain. Used: checking it again,
            // as the chain's links would cost anyway.
            let scalar = pair.0.tuples.is_empty() && pair.1.tuples.is_empty();
            if !lits && !scalar && seen.contains(&pair) {
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
                        if is_decimal(&l.value) {
                            let cs: Vec<Carrier> = [Carrier::F64, Carrier::Rat]
                                .into_iter()
                                .filter(|&c| fits(l, c))
                                .collect();
                            unfixed_found.push((l.site, unfixed(l, &cs)));
                            fixed[side] = Some(Lit {
                                bare: false,
                                ..l.clone()
                            });
                        }
                    }
                }
                // An `if` of literals written as a component, `if c { 2 + 1 } else { 1 }`,
                // keeps its branches, each of which adopts as a lone literal would.
                let arg = |t: &Ty, w: &Option<Part<'a>>, fixed: Option<Lit>| match w {
                    Some(Part::Lit(l)) => Arg {
                        lit: Some(fixed.unwrap_or_else(|| l.clone())),
                        ..Arg::of(t.clone())
                    },
                    Some(Part::Branches(bs)) => Arg {
                        branches: Some(bs.clone()),
                        ..Arg::of(t.clone())
                    },
                    _ => Arg::of(t.clone()),
                };
                let [f0, f1] = fixed;
                self.apply(
                    Label::Text(what),
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
                        Label::Text(what),
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
                    format!("{who} does not take {s} and {t}, only two tuples or two numbers"),
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
                                "{who} does not take {s} and {t}: no tuple of {n} on the other side"
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
                        let part = |w: &Option<Rc<[Part<'a>]>>| match w.as_ref().map(|ps| &ps[i]) {
                            Some(Part::Other) | None => None,
                            Some(p) => Some(p.clone()),
                        };
                        todo.push((join(&s), join(&t), [part(&ws), part(&wt)]));
                    }
                }
            }
            if !scalar {
                seen.insert(pair);
            }
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
    /// the interval of its expression, as `^`'s exponent is. Each rejection names the domain at
    /// the smallest width, and repairs the operand with a test that keeps it there, or the width
    /// with a test, or a literal width rewritten, that holds the other operands
    /// (MSG-width-headline).
    fn bit_domains(&mut self, w: &str, p: Prim, slots: &[(Arg<'a>, &'a Expr)], span: Span) {
        let names = zed_kernel::bits::params(p);
        let shift = matches!(p, Prim::Shl | Prim::Shr);
        let nonneg = IntervalSet::range(End::of(0), PosInf);
        let ranges: Vec<Option<IntRange>> =
            slots.iter().map(|(a, e)| self.int_range(a, e)).collect();
        let last = slots.len() - 1;
        let has_width = zed_kernel::bits::has_width(p);
        let two_pow = zed_kernel::bits::below_two_pow_width(p);
        let below_width = zed_kernel::bits::below_width(p);
        // The smallest width, if the width is of an int type and at least 0: a test that keeps
        // an operand below `2 ^ w`, or a `k` below `w`, keeps it there at every width.
        let smallest = match slots[last].0.ty.vars.is_empty() {
            true => (ranges[last].as_ref())
                .and_then(|r| r.extreme(std::cmp::Ordering::Less))
                .filter(|s| s.surface_cmp(&Value::Int(0)).is_some_and(|o| o.is_ge())),
            false => None,
        };
        // The width, where it is one value: an operand's domain is then written and tested at
        // it; else the domain is written at `width`, and only the width is tested.
        let exact = (smallest.clone()).filter(|s| {
            (ranges[last].as_ref())
                .and_then(|r| r.extreme(std::cmp::Ordering::Greater))
                .is_some_and(|h| h.surface_cmp(s).is_some_and(|o| o.is_eq()))
        });
        // The ints a test of the width keeps it in, so that it holds the other operands.
        let width_within = (has_width.then(|| least_width(p, slots, &ranges)))
            .flatten()
            .map(|l| Within::width(p, l));
        // The domain of operand `i` as a message writes it, and whether a test keeps the
        // operand in it: one at an exact width, or the width's own, or `int[0..]`.
        let within_of = |i: usize| -> (Within, bool) {
            let range = |below| Within::Range { low: 0, below };
            let nonempty = |s: &Value| s.surface_cmp(&Value::Int(1)).is_some_and(|o| o.is_ge());
            if two_pow.contains(&i) {
                let s = exact.clone();
                (range(Some(Bound::TwoPow(s.clone()))), s.is_some())
            } else if below_width == Some(i) {
                let s = exact.clone().filter(nonempty);
                (range(Some(Bound::Width(s.clone()))), s.is_some())
            } else if has_width && i == last {
                match &width_within {
                    Some(wi) => (wi.clone(), true),
                    None => (range(None), false),
                }
            } else {
                (range(None), true)
            }
        };
        let mut fine = true;
        for (i, (((a, e), r), name)) in slots.iter().zip(&ranges).zip(names).enumerate() {
            if shift && i == 0 {
                continue;
            }
            if !a.ty.vars.is_empty() {
                let d = IntDomain {
                    what: format!("`{w}` takes `{name}` in int[0..]").into(),
                    below_two_pow: None,
                    name: (*name).into(),
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
            notes.extend(self.refused_notes(e));
            self.derive_into(&[at], &mut notes);
            notes.push(Note {
                span,
                text: format!(
                    "`{w}` reads `{name}` as binary digits, and an int below 0 has no finite \
                     row of them"
                ),
            });
            // No test is offered where the checks that follow would still refuse what it
            // keeps: an operand bounded by a width not shown to be at least 0, and a width
            // whose other operands have no largest value.
            let (shown_within, testable) = within_of(i);
            let arg =
                (self.code(Some(at)).filter(|_| testable)).map(|c| (c, self.tested(e).is_some()));
            let call = self.call_parts(span, at);
            let outside_all = shown_within.holds_none_of(r);
            let (mut first, mut repairs) =
                passed_repairs(name, &shown_within, arg, call, outside_all, None, span);
            if has_width && i == last {
                let rewrite =
                    (width_within.as_ref()).and_then(|wi| self.width_rewrite(span, at, wi));
                repairs.splice(first.is_some() as usize..first.is_some() as usize, {
                    (rewrite.iter().map(repair_note)).map(|text| Note { span, text })
                });
                first = first.or(rewrite);
            }
            notes.extend(repairs);
            let takes = format!("`{w}` takes `{name}` {}", shown_within.takes());
            let piece = self.annotated(span, at, shown);
            self.error_with(span, domain_message(&takes, &piece, first.as_ref()), notes);
        }
        if !fine || !has_width {
            return;
        }
        // An operand of a type variable read as `width` digits, under a width of an int type,
        // takes the ints below `2 ^ w`, `w` the smallest width, as a need on its parameter.
        // The other relations to `width` are between two operands, which a need on one
        // parameter does not carry: an operand of a type variable in one is rejected here
        // (CHK-need-bound), with the test that holds the relation and each parameter it reads
        // declared `int`.
        let related = (two_pow.iter().copied()).chain(below_width).chain([last]);
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
                    name: name.into(),
                };
                self.floor(&a.ty, e, d, span);
                continue;
            }
            let mut notes = vec![Note {
                span: at,
                text: format!("`{name}` is this operand, of no declared type"),
            }];
            self.derive_into(&[at], &mut notes);
            let checks = match i == last {
                true => "its operands".to_string(),
                false => format!("`{name}`"),
            };
            notes.push(Note {
                span,
                text: format!(
                    "`{w}` checks {checks} against `width`, and the checker does not follow a \
                     check between two operands back to each caller, so the type of `{name}` \
                     is needed here"
                ),
            });
            let (shown_within, testable) = within_of(i);
            let code = self.code(Some(at)).filter(|_| testable);
            let arg = code.map(|c| (c, self.tested(e).is_some()));
            let call = self.call_parts(span, at);
            let (mut first, mut repairs) =
                passed_repairs(name, &shown_within, arg, call, false, None, span);
            // A test narrows only a name whose values are all ints.
            if let (Some((test, tail)), Some(c)) = (&mut first, code) {
                *tail = format!(", with each parameter in `{}` declared `int`", unparen(c));
                repairs[0].text = repair_note(&(test.clone(), tail.clone()));
            }
            notes.extend(repairs);
            let takes = format!("`{w}` takes `{name}` {}", shown_within.takes());
            let piece = self.annotated(span, at, &self.show(&a.ty));
            self.error_with(span, domain_message(&takes, &piece, first.as_ref()), notes);
            return;
        }
        let (wa, we) = &slots[last];
        let Some(rw) = &ranges[last] else {
            return;
        };
        let aw = wa.at.unwrap_or(we.span);
        if zed_kernel::bits::whole_bytes(p) && !whole_bytes(rw) {
            let sw = rw.shown.as_str();
            let mut notes = vec![Note {
                span: aw,
                text: format!("`width` is this operand, {sw}"),
            }];
            self.derive_into(&[aw], &mut notes);
            notes.push(Note {
                span,
                text: format!("`{w}` works on whole bytes"),
            });
            let within = width_within.unwrap_or(Within::Bytes(vec![8, 16, 32, 64]));
            let arg = self.code(Some(aw)).map(|c| (c, self.tested(we).is_some()));
            let call = self.call_parts(span, aw);
            let outside_all = within.holds_none_of(rw);
            let (first, mut repairs) =
                passed_repairs("width", &within, arg, call, outside_all, None, span);
            let rewrite = self.width_rewrite(span, aw, &within);
            let at = first.is_some() as usize;
            repairs.splice(at..at, {
                (rewrite.iter().map(repair_note)).map(|text| Note { span, text })
            });
            notes.extend(repairs);
            let takes = format!("`{w}` takes `width` {}", within.takes());
            let piece = self.annotated(span, aw, sw);
            let first = first.or(rewrite);
            self.error_with(span, domain_message(&takes, &piece, first.as_ref()), notes);
            return;
        }
        let Some(s) = smallest else {
            return;
        };
        // An operand lies below `2 ^ width` when its largest value does below the smallest
        // width, and below `width` when its largest value is less than the smallest width.
        let bounded = (two_pow.iter().map(|&i| (i, Bound::TwoPow(Some(s.clone())))))
            .chain(below_width.map(|i| (i, Bound::Width(Some(s.clone())))));
        for (i, bound) in bounded {
            let ((a, e), Some(r)) = (&slots[i], &ranges[i]) else {
                continue;
            };
            let at_smallest = Within::Range {
                low: 0,
                below: Some(bound),
            };
            let below =
                (r.extreme(std::cmp::Ordering::Greater)).is_some_and(|h| at_smallest.holds(&h));
            if !below {
                let operand = (a.at.unwrap_or(e.span), *e, r);
                let within = within_of(i);
                self.width_error(
                    w,
                    names[i],
                    within,
                    operand,
                    (aw, *we, rw),
                    &width_within,
                    span,
                );
            }
        }
    }

    /// The error for the operand `name` of `w`, at `ax`, not shown to lie below the bound the
    /// smallest width, at `aw`, sets it: each place with its expression and its ints. `within`
    /// is its domain, at the width where the width is one value, else at `width`, and the flag
    /// says that a test of the operand keeps it there. The repairs test the operand, test the
    /// width or rewrite a literal width so that it holds the other operands, `width_within`,
    /// and pass a value in `within`.
    #[allow(clippy::too_many_arguments)]
    fn width_error(
        &mut self,
        w: &str,
        name: &str,
        (within, testable): (Within, bool),
        (ax, ex, rx): (Span, &'a Expr, &IntRange),
        (aw, ew, rw): (Span, &'a Expr, &IntRange),
        width_within: &Option<Within>,
        span: Span,
    ) {
        let (sx, sw) = (rx.shown.as_str(), rw.shown.as_str());
        let mut notes = vec![
            Note {
                span: ax,
                text: format!("`{name}` is this operand, {sx}"),
            },
            Note {
                span: aw,
                text: format!("`width` is this operand, {sw}"),
            },
        ];
        self.derive_into(&[ax, aw], &mut notes);
        let arg =
            (self.code(Some(ax)).filter(|_| testable)).map(|c| (c, self.tested(ex).is_some()));
        let call = self.call_parts(span, ax);
        let outside_all = within.holds_none_of(rx);
        let (test, mut repairs) = passed_repairs(name, &within, arg, call, outside_all, None, span);
        // The width that holds every other operand: a literal rewritten, else a test of it.
        let widened = width_within.as_ref().and_then(|wi| {
            self.width_rewrite(span, aw, wi).or_else(|| {
                let arg = self.code(Some(aw)).map(|c| (c, self.tested(ew).is_some()));
                let call = self.call_parts(span, aw);
                let (t, _) =
                    passed_repairs("width", wi, arg, call, wi.holds_none_of(rw), None, span);
                t
            })
        });
        let width_note = match &widened {
            Some(r) => repair_note(r),
            None => {
                "repair: pass a larger `width`, if the operation is meant on a wider word".into()
            }
        };
        let at = test.is_some() as usize;
        repairs.insert(
            at,
            Note {
                span,
                text: width_note,
            },
        );
        notes.extend(repairs);
        let takes = format!("`{w}` takes `{name}` {}", within.takes());
        let piece = match self.code(Some(aw)).is_some_and(int_literal) {
            true => self.annotated(span, ax, sx),
            false => self.annotated_parts(span, &[(ax, sx), (aw, sw)]),
        };
        let first = test.or(widened);
        self.error_with(span, domain_message(&takes, &piece, first.as_ref()), notes);
    }

    /// The call at `span` with its width at `at`, an int literal, rewritten as the least width
    /// `within` holds, as `byteSwap(x, width: 16)` for `width: 12`; none where the width is not
    /// a literal.
    fn width_rewrite(&self, span: Span, at: Span, within: &Within) -> Option<Repair> {
        let code = self.code(Some(at))?;
        if !int_literal(code.strip_prefix('-').unwrap_or(code)) {
            return None;
        }
        let (_, before, after) = self.call_parts(span, at)?;
        Some((format!("{before}{}{after}", within.least()), String::new()))
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
        let (ints, narrowed, listed) = self.ints_of(&ns, e);
        let shown_as_type = listed.is_some();
        let values = listed.or_else(|| k.value.map(|v| vec![v]));
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

    /// The interval of [`Self::int_range`] for an operand `e` whose type's int part is `ns`,
    /// whether the tests the walk is in narrowed it, and the values `ns` lists.
    fn ints_of(&mut self, ns: &KType, e: &'a Expr) -> (IntervalSet, bool, Option<Vec<Value>>) {
        let (mut ints, narrowed) = self.ints_here(e);
        let listed = ns.ints_listed();
        if let Some(vs) = &listed {
            let piece = |v: &Value| match v {
                Value::Int(n) => (End::of(*n), End::of(*n)),
                Value::Big(n) => (Fin(Num::from(&**n)), Fin(Num::from(&**n))),
                _ => (NegInf, PosInf),
            };
            ints = ints.meet(&IntervalSet::from_pieces(vs.iter().map(piece).collect()));
        }
        (ints, narrowed, listed)
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
        let (result, kept) = self.apply(Label::Text(&callee(what)), sig, args, false, span);
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
        let mut out = self.passing(v, "a call", span, of);
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
                        .apply(
                            Label::Text("this function"),
                            &sig,
                            vec![Some(x.clone())],
                            false,
                            span,
                        )
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
        let mut out = self.passing(v, "an index", span, of);
        let shown = x.ty.to_string();
        for p in v.pieces() {
            match p {
                Piece::Fn(sig) if sig.data => {
                    if let Some(r) = self.key_outside(&sig, &x, of, span, dense) {
                        out = out.union(&r);
                        continue;
                    }
                    let r = self
                        .apply(
                            Label::Text("this family"),
                            &sig,
                            vec![Some(x.clone())],
                            true,
                            span,
                        )
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
                    let r = self.need(k, kind, true, span);
                    self.bind_component(v, k, i, &r, span);
                    out = out.union(&r);
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

    /// The message of the operator `what`, of signature `sig`, applied to `args`, where one of
    /// its two operands is a `rat` literal and the other a number of no carrier in common with
    /// it, as `n * -3r` of an `int` (DESIGN.md sec:diagnostics, row "Two numeric values with no
    /// common carrier"): "The suffix makes the literal `-3r` a `rat`, never `int`", as the
    /// message of an `f64` literal beside a `rat` says, with the literal's place. `None`
    /// otherwise, and in a trial ([`Self::trying`]), where the rejection stands at the
    /// operator: at the literal it would lie inside an argument a repair leaves as it was, which
    /// [`Self::written_with`] reads as an error of that argument, so a cast of the other operand
    /// that leaves the literal refused would pass as a repair, as `f64(y)` for `y * 0.1r`.
    /// Cost: the two operands' carriers and the literal's text.
    fn forced_rat(
        &self,
        what: Label<'_>,
        sig: &Sig,
        args: &[Option<Arg<'a>>],
    ) -> Option<(Span, String)> {
        if self.trying {
            return None;
        }
        let binary = matches!(
            what.operator(),
            Some(Operator::Binary(
                BinaryOp::Add
                    | BinaryOp::Sub
                    | BinaryOp::Mul
                    | BinaryOp::Div
                    | BinaryOp::Lt
                    | BinaryOp::Le
                    | BinaryOp::Gt
                    | BinaryOp::Ge
            ))
        );
        if !binary || args.len() != 2 || !self.no_common_carrier(sig, args) {
            return None;
        }
        let rat_lit = |a: &Arg<'a>| {
            let at = a.at?;
            match self.seen.get(&at) {
                Some((_, Src::Other(e))) if rat_forms(e, None).is_some() => Some(at),
                _ => None,
            }
        };
        let [Some(x), Some(y)] = args else {
            return None;
        };
        let (at, other) = match (rat_lit(x), rat_lit(y)) {
            (Some(at), None) => (at, y),
            (None, Some(at)) => (at, x),
            _ => return None,
        };
        let mask = self.numbers_of(other)?;
        let cs: Vec<Carrier> = (Carrier::ALL.into_iter())
            .filter(|c| mask & c.bit() != 0)
            .collect();
        if cs.is_empty() || cs.contains(&Carrier::Rat) {
            return None;
        }
        let names = carrier_names(&cs);
        let text = quoting(
            &format_args!(
                "The suffix makes the literal `{}` a `rat`, never `{names}`",
                self.code(Some(at))?
            ),
            || format!("The suffix makes this literal a `rat`, never `{names}`"),
        );
        Some((at, text))
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
    /// place of the words ([`rat_forms`]). Each comes with what its trial gave, which
    /// [`Self::note_offered`] records where the note is offered, and with the fix that writes
    /// it in the program's text, which a message offers in its place.
    ///
    /// The repairs of a literal argument come first, whichever argument it is: the literal a
    /// cast gives written in its place, `8` for `"8"` or `1` for `1r`, or the cast where no
    /// literal writes its value, `rat("1/3")`; the repairs of the other arguments, casts,
    /// come after them. A repair of a literal keeps the type of every other argument, while
    /// a cast of another argument changes what the application computes, as
    /// `String(n) < "8"` does, which orders the text `"10"` before `"8"` (row
    /// REPAIR-compare-order). Within each kind the order is the arguments' and then the
    /// words'. Complexity tradeoff: none; the two kinds are kept in two lists and joined
    /// once, O(r) for `r` repairs, where the naive order, one list in argument order, costs
    /// the same and puts the cast of an earlier argument first.
    fn repairs(
        &mut self,
        what: Label<'_>,
        sig: &Sig,
        args: &[Option<Arg<'a>>],
        pass: bool,
        span: Span,
    ) -> Vec<Repaired> {
        let mut out = Vec::new();
        if self.trying {
            return out;
        }
        // The literal repairs, offered before `out`, the casts.
        let mut literals = Vec::new();
        // A word is called by its name and has its own signature; a declared function may
        // share the name only with a signature of its own.
        let word = what
            .text()
            .strip_prefix('`')
            .and_then(|w| w.strip_suffix('`'))
            .is_some_and(|w| sig.word.as_deref() == Some(w));
        let kept = pass || word;
        // A numeric cast word, `int(b)`, is not offered its argument as text, `int(String(b))`
        // (row MSG-apply-try-headline). The repair is tried only where some value of `b` has
        // no arrow of the cast, a `bool`, an atom or a tuple, and the text of such a value
        // never reads as a number, so the repaired call gives `#invalid` for it: `int(true)`
        // becomes `int("true")`. It checks, as `#invalid` is in the type of the cast from
        // text, but it is a conversion that can fail, which no repair offers, and it changes
        // what the call computes. Values the cast takes, as `1` in `f64(g(true))` with `g`
        // giving `1 | true`, need no repair.
        let cast_word = word
            && Carrier::NUMBERS
                .iter()
                .any(|c| sig.word.as_deref() == Some(c.name()));
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
            let (name, written, literal) = match self.seen.get(at) {
                Some((_, Src::Name(id))) => (Some(&t.res.binders[*id].name), None, false),
                Some((_, Src::Other(e))) => (
                    None,
                    rat_forms(e, self.t.text),
                    is_literal(e) || matches!(e.kind, ExprKind::Str(_)),
                ),
                _ => (None, None, false),
            };
            let a = a.as_ref().expect("an argument");
            if let Some(forms) = written {
                for (ty, lit, text) in forms {
                    // The form is offered for its own carrier: `1` for `1r` where an `int` is
                    // taken, not where an `f64` is, which `1.0` is offered for, though `1`
                    // checks there too.
                    let at_carrier = Arg {
                        at: kept.then_some(*at),
                        ..Arg::of(ty.clone())
                    };
                    if self
                        .repaired(what, sig, args, (i, at_carrier), pass, span)
                        .is_none()
                    {
                        continue;
                    }
                    // An `f64` literal whose operation then has no type until its value meets
                    // a carrier, as `2.5` in `1 ^ 2.5`, is written with its suffix, `2.5f64`.
                    let f64 = ty.numeric_carrier() == Some(Carrier::F64);
                    let suffixed = (lit.as_ref().filter(|_| f64))
                        .and_then(|l| shown(&format_args!("{l}f64")).ok())
                        .map(|s| {
                            let text = quoting(
                                &format_args!("repair: write `{s}`; the checker accepts that"),
                                || {
                                    "repair: write this literal as an `f64` literal with its \
                                     suffix; the checker accepts that"
                                        .to_string()
                                },
                            );
                            (Some(s), text)
                        });
                    let carrier = ty.numeric_carrier();
                    for (lit, text) in std::iter::once((lit, text)).chain(suffixed) {
                        // The literal as the repair writes it, where the checker reads it alone.
                        let was = self.t.text.and_then(|s| s.get(at.start..at.end));
                        let with = match (&lit, was) {
                            (Some(lit), Some(was)) => match self.written_arg(lit, was, a, *at) {
                                Mapped::Args(mut one) => one.pop().flatten(),
                                _ => None,
                            },
                            _ => None,
                        };
                        let with = with.unwrap_or(Arg {
                            at: kept.then_some(*at),
                            ..Arg::of(ty.clone())
                        });
                        if let Some(got) = self.repaired(what, sig, args, (i, with), pass, span) {
                            // The fix writes the literal of the form, `-3` for `-3r`.
                            let fix = (lit.as_deref().zip(carrier)).and_then(|(l, c)| {
                                let holds =
                                    format_args!("the literal is then the {} {l}", c.name());
                                Rewrite::new(&[(*at, &l)], &holds, &l)
                            });
                            literals.push(Repaired {
                                note: Note { span: *at, text },
                                got,
                                fix,
                            });
                            break;
                        }
                    }
                }
                continue;
            }
            for w in ["String", "int", "rat", "f64"] {
                if cast_word && w == "String" {
                    continue;
                }
                let Some(r) = self
                    .wrapped(w, a, &held, *at)
                    .filter(|r| r.atoms() == held.atoms())
                else {
                    continue;
                };
                let with = Arg {
                    at: kept.then_some(*at),
                    ..Arg::of(r)
                };
                if let Some(got) = self.repaired(what, sig, args, (i, with), pass, span) {
                    if w == "String"
                        && self.takes_some(
                            what,
                            sig,
                            args,
                            (i, &held, kept.then_some(*at)),
                            pass,
                            span,
                        )
                    {
                        continue;
                    }
                    // On a literal the cast cannot fail on, the repair writes the literal the
                    // cast gives, `8` for `int("8")`, which says the same (REPAIR-literal-cast).
                    if literal
                        && let Some(lit) = self.literal_repair(w, a, &held, *at)
                        && let Some(got) = self.repaired(what, sig, args, (i, lit.arg), pass, span)
                    {
                        let text = quoting(
                            &format_args!("repair: write `{}`; the checker accepts that", lit.text),
                            || {
                                format!(
                                    "repair: write the literal `{w}(…)` gives on this one; the \
                                     checker accepts that"
                                )
                            },
                        );
                        let holds = format_args!("the literal is then the {w} {}", lit.text);
                        literals.push(Repaired {
                            note: Note { span: *at, text },
                            got,
                            fix: Rewrite::new(&[(*at, &lit.text)], &holds, &lit.text),
                        });
                        continue;
                    }
                    let text = match name {
                        Some(n) => format!("repair: write `{w}({n})`; the checker accepts that"),
                        None => format!("repair: wrap this in `{w}(…)`; the checker accepts that"),
                    };
                    // The fix casts the argument where it stands, `rat(n)`.
                    let fix = self.code(Some(*at)).and_then(|c| {
                        let open = format!("{w}(");
                        let holds = format_args!("{c} is cast to {w}");
                        let alone = format_args!("{w}({c})");
                        let edits: [(Span, &dyn fmt::Display); 2] =
                            [(point(at.start), &open), (point(at.end), &")")];
                        Rewrite::new(&edits, &holds, &alone)
                    });
                    // A cast of a literal no literal writes, `rat("1/3")`, rewrites only the
                    // literal too.
                    let to = if literal { &mut literals } else { &mut out };
                    to.push(Repaired {
                        note: Note { span: *at, text },
                        got,
                        fix,
                    });
                }
            }
        }
        literals.append(&mut out);
        literals
    }

    /// Whether the application takes, as written, some value of argument `i`, of type `held`
    /// and shown at `at` as [`Self::repairs`] shows it, that `String` would change: a value
    /// that is neither text nor an atom. A repair `String(a)` is offered only where it takes
    /// none (row MSG-headline-l01_26). `String(k)` for a key `k: int | bool` of a map keyed
    /// `int | String` checks, but it reads the key `5` as `"5"`, another key, so it changes what
    /// the read gives for every key the map already took: a conversion, not a cast that keeps
    /// the program's meaning (DESIGN.md sec:diagnostics, "A repair never narrows a type").
    /// Where no value is taken, as in `len(x)` with `x: int`, the call has no meaning to keep,
    /// and `len(String(x))` is offered. A numeric cast keeps the number, so `rat(x)` needs no
    /// such test; `String` keeps text as it is, and atoms pass by the cast.
    ///
    /// Complexity tradeoff: the naive test tries each value of `held`, which a type does not
    /// list; used: the application is tried once per piece of `held` (a carrier, the other
    /// scalars, a tuple shape, a function), with that piece alone at `i`, stopping at the first
    /// piece taken. For p pieces that is p trials, each of the application with one piece where
    /// the trial of `String(a)` had one piece too, so O(p) times that trial, linear in the
    /// argument's type. Measured on a union of k tuple lengths, k ≈ √(2n), a trial costs about
    /// the same at n = 800 and 6400, and the check grows 5.9 times at 8n, against 6.3 without
    /// this test (scaling test `a_text_repair_of_many_shapes_scales` in
    /// tests/steps/l01_29_diagnostics). It runs only where `String(a)` itself checks.
    fn takes_some(
        &mut self,
        what: Label<'_>,
        sig: &Sig,
        args: &[Option<Arg<'a>>],
        (i, held, at): (usize, &Ty, Option<Span>),
        pass: bool,
        span: Span,
    ) -> bool {
        let changed = held.without_atoms().without(&Carrier::Str.ty());
        changed.pieces().iter().any(|p| {
            let with = Arg {
                at,
                ..Arg::of(changed.of_piece(p))
            };
            self.repaired(what, sig, args, (i, with), pass, span)
                .is_some()
        })
    }

    /// The type of the argument `a` at `at`, of type `held`, wrapped in the prelude word `w`, where
    /// that application checks as written, tried with the checker's state restored after;
    /// `None` where it does not. The wrap is applied as the checker applies it where the
    /// repair is written ([`Self::word_end`]), so a repair is offered only where its own call
    /// checks too: with `g(positional c: bool) = if c { 1 } else { 2.5 }`, `int(g(c))` is
    /// rejected at the `2.5`, which nothing gives a carrier, and is not offered for
    /// `scalar(g(c))`, although each value of `g(c)` has an arrow of `int` ([`converted`], the
    /// naive form, which splits the type alone and cannot tell `2.5` from `2.5f64`); and
    /// `String(g(c))` is rejected there too, as `String(0.5)` is. Complexity tradeoff: one
    /// application of a word of at most five arrows to one argument, the cost of checking the
    /// call as written, for each of the four words at each rejected application.
    pub(super) fn wrapped(
        &mut self,
        w: &'static str,
        a: &Arg<'a>,
        held: &Ty,
        at: Span,
    ) -> Option<Ty> {
        let arg = Arg {
            ty: held.clone(),
            ..a.clone()
        };
        self.tried(|ck| ck.word_end(w, arg, at))
    }

    /// The literal that the cast `w` gives on the literal argument `a` at `at`, of type `held`,
    /// as the program writes it, with the argument it is where the checker reads it alone
    /// ([`Self::written_arg`]): `8` for `int("8")`, which says the same as the cast and is
    /// what a repair offers in its place (row REPAIR-literal-cast). `None` where `held` is not
    /// one value, the cast gives an atom on it, or the value has no literal the checker reads
    /// back, as `rat("1/3")`, whose `rat` no decimal literal writes; the repair is then the
    /// cast. A `rat` is written with its point where that is no longer ([`plain_rat`]).
    ///
    /// Complexity tradeoff: the naive repair writes the cast around the literal, O(1), and
    /// shows a call that cannot fail as if it could. This runs the cast once on the one value,
    /// O(d^1.47) for a literal of d digits, as [`Self::word_atoms`] already does for the same
    /// call (COMPLEXITY.md row C39), prints the result, O(d), and reads it back, O(d).
    fn literal_repair(&mut self, w: &str, a: &Arg<'a>, held: &Ty, at: Span) -> Option<Literal<'a>> {
        let [v] = held.kernel()?.values_listed()?.try_into().ok()?;
        let x = run(zedc_base::interp::prim(w)?, &v)?;
        if matches!(x, Value::Atom(_)) {
            return None;
        }
        let text = self.text(&Ty::lit(&x));
        let text = match x {
            Value::Rat(_) => plain_rat(&text).unwrap_or(text),
            _ => text,
        };
        let was = self.t.text?.get(at.start..at.end)?;
        match self.written_arg(&text, was, a, at) {
            Mapped::Args(mut one) => Some(Literal {
                arg: one.pop().flatten()?,
                text,
            }),
            _ => None,
        }
    }

    /// `f` run as a trial: its result where it adds no error, refuses no literal and makes no
    /// operation on literals alone whose value has no type until it meets a carrier
    /// ([`Self::opened`]), `None` where it does, with the checker's state restored after
    /// either way, as a repair is tried ([`Self::trying`], [`Self::rough`]). What it reads of
    /// the comparison being checked ([`Self::comparing`]) is kept for after it.
    pub(super) fn tried<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> Option<T> {
        match self.trial(f) {
            (t, Some(found)) if found.is_empty() => Some(t),
            _ => None,
        }
    }

    /// `f` run as a trial, as [`Self::tried`] runs it: its result, with the spans of the
    /// errors it adds and the literals it refuses, or `None` for those where it makes an
    /// operation on literals alone whose value has no type until it meets a carrier
    /// ([`Self::opened`]) or drops an error found before it. O(what `f` costs).
    fn trial<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> (T, Option<Vec<Span>>) {
        let saved = self.mark();
        let refused = self.lit_refused.len();
        let trying = std::mem::replace(&mut self.trying, true);
        let rough = std::mem::replace(&mut self.rough, true);
        let comparing = self.comparing;
        let opened = std::mem::replace(&mut self.opened, false);
        let t = f(self);
        let found = match (self.opened, self.errors.get(saved.errors..)) {
            (false, Some(errors)) => Some(
                (errors.iter().map(|e| e.span))
                    .chain(
                        self.lit_refused
                            .get(refused..)
                            .unwrap_or(&[])
                            .iter()
                            .map(|r| r.0),
                    )
                    .collect(),
            ),
            _ => None,
        };
        self.opened = opened;
        self.comparing = comparing;
        self.rough = rough;
        self.trying = trying;
        self.lit_refused.truncate(refused);
        self.undo(&saved);
        (t, found)
    }

    /// The construct `form` applied to `args`, as the program writes them, at `span`,
    /// recorded while it is checked, so that each fix offered for a rejection in it is
    /// checked by checking it again with the fix in place ([`Self::fixes_checked`]). A trial
    /// records nothing: its rejections offer no fix.
    ///
    /// Complexity tradeoff: the record copies the arguments' types, O(their size), at each
    /// operator and prelude word, which the check of the construct reads in full anyway.
    /// Keeping them only where a rejection comes would need them before the check changes
    /// them (a literal adopts a carrier, a call is read at one), which is when they are
    /// copied here.
    fn as_written(&mut self, form: Construct<'a>, args: Vec<Option<Arg<'a>>>, span: Span) -> Ty {
        if self.trying {
            return self.construct(form, args, span);
        }
        let w = Rc::new(Written {
            form: form.clone(),
            args: args.clone(),
            span,
        });
        let outer = self.written.replace(w.clone());
        let (errors, pending) = (self.errors.len(), self.pending_fixes.len());
        let t = self.construct(form, args, span);
        self.written = outer;
        // The fixes kept in the arguments that change their types, from the arguments' own
        // checks just before this one.
        let mut carried = Vec::new();
        for (i, a) in w.args.iter().enumerate() {
            if let Some(at) = a.as_ref().and_then(|a| a.at) {
                carried.extend(
                    self.carried
                        .remove(&at)
                        .into_iter()
                        .flatten()
                        .map(|c| (i, c)),
                );
            }
        }
        // A check of this span before, as a function's body is checked at each call, carries
        // nothing to this one.
        self.carried.remove(&span);
        if self.pending_fixes.len() > pending || !carried.is_empty() {
            self.pending_settled(&w, &t, errors, pending, carried);
        }
        t
    }

    /// Settles the fixes [`Self::fixes_checked`] kept pending in the construct `w`, whose own
    /// check gave the type `t` and added the errors from `errors` on and the pending fixes
    /// from `pending` on, and the fixes `carried` of its arguments, each by the index of the
    /// argument whose type they change ([`Carry`]): a pending fix whose check as written
    /// rejected a span the construct's own check does not reject is dropped from its
    /// rejection's menu, as are carried ones where the construct, checked with the type they
    /// give its argument, adds an error other than those; and where that leaves none the
    /// message says that none is offered ([`Msg::dropped`]). The fixes kept whose type for
    /// the construct is not `t` are carried on to the construct `w` is an argument of.
    ///
    /// Complexity tradeoff: one pass over the construct's errors to index them by span, then
    /// O(1) expected per span a fix needs; the arguments' places sorted once, O(a log a), so
    /// the argument an error lies in is a binary search. The types carried into the
    /// arguments are checked in rounds, each giving an argument at most one type: at a call
    /// whose parameters are checked apart ([`params_apart`]) a round is one check of a call
    /// of one parameter per argument and one check of the whole call
    /// ([`Self::carried_together`]), O(the call) for the round; elsewhere one check of the
    /// construct per type carried ([`Self::carried_alone`]). Fixes that give an argument one
    /// type are checked together, and the groups join smaller into larger, so a fix moves
    /// O(log fixes) times in all. The naive ways: one check of the call per argument
    /// carrying a fix, as before MSG-many-args-repair-loop, is quadratic in a call of n
    /// arguments each with its own rejection, `f(k * 0.5, k * 0.5, …)` (31 times the
    /// instructions at 8 times the arguments); checking the whole statement again with the
    /// fix written in costs the statement per fix, quadratic in a statement of many
    /// rejections; one check per carried fix is quadratic in a nest of n operations each
    /// with its own rejection, as `((1 + 1) / 1 + 1) / 1 …` before its literals meet a
    /// carrier, where each fix rides up every level; and scanning the construct's errors for
    /// each span needed is O(errors × spans), quadratic in the arguments of one call. Still
    /// quadratic: a call whose parameters share a type variable, or has bounds or several
    /// arrows, is checked once per argument carrying a fix (MSG-many-args-generic).
    fn pending_settled(
        &mut self,
        w: &Written<'a>,
        t: &Ty,
        errors: usize,
        pending: usize,
        carried: Vec<(usize, Carry)>,
    ) {
        let settled = self.pending_fixes.split_off(pending);
        let from = errors.min(self.errors.len());
        let found: HashSet<Span> = (self.errors[from..].iter())
            .flat_map(|e| std::iter::once(e.span).chain(e.also.iter().copied()))
            .collect();
        let mut up = HashMap::new();
        for p in settled {
            // A fix that leaves its own rejection, as `int(n) * 0.5` for `n * 0.5`, fixes nothing.
            let own = self.found(p.id).map(|e| e.span);
            match p.needs.iter().all(|s| found.contains(s) && Some(*s) != own) {
                true if p.ty != *t => carry_joined(&mut up, p.ty.clone(), vec![p]),
                true => {}
                false => self.fix_dropped(&p),
            }
        }
        // The arguments' places in the order of the text, each with its index: the argument
        // a span lies in is one binary search ([`arg_holding`]).
        let mut ats: Vec<(Span, usize)> = (w.args.iter().enumerate())
            .filter_map(|(j, a)| Some((a.as_ref()?.at?, j)))
            .collect();
        ats.sort_unstable_by_key(|&(s, _)| (s.start, s.end));
        // The `r`th round holds the `r`th type carried into each argument, so that no round
        // gives an argument two types.
        let mut rounds: Vec<Vec<(usize, Carry)>> = Vec::new();
        let mut taken = vec![0; w.args.len()];
        for (i, c) in carried {
            if w.args[i].as_ref().and_then(|a| a.at).is_none() {
                continue;
            }
            if rounds.len() == taken[i] {
                rounds.push(Vec::new());
            }
            rounds[taken[i]].push((i, c));
            taken[i] += 1;
        }
        // The construct's own check rejected nothing outside its arguments, as a call no arrow
        // takes, so one argument's fix does not settle an error another argument gave.
        let apart = matches!(&w.form, Construct::Call(_, sig) if params_apart(sig))
            && found.iter().all(|&s| arg_holding(&ats, s).is_some());
        for round in rounds {
            let left = match apart {
                true => self.carried_together(w, t, &found, &ats, round, &mut up),
                false => round,
            };
            for (i, c) in left {
                match self.carried_alone(w, &found, &ats, i, &c) {
                    Some(ty) if ty != *t => carry_joined(&mut up, ty, c.fixes),
                    Some(_) => {}
                    None => c.fixes.iter().for_each(|p| self.fix_dropped(p)),
                }
            }
        }
        self.carried_up(w.span, up);
    }

    /// The construct `w` checked with each argument `i` of `round` given the type `ty` its
    /// carried fixes give it ([`Carry`]): its type and the spans of the errors it adds, or `None`
    /// for those as [`Self::trial`] gives them. One check of the construct.
    fn carried_check(
        &mut self,
        w: &Written<'a>,
        round: &[(usize, &Ty)],
    ) -> (Ty, Option<Vec<Span>>) {
        // The arguments not replaced copied, the replaced ones not.
        let mut with: Vec<Option<&Ty>> = vec![None; w.args.len()];
        for &(i, ty) in round {
            with[i] = Some(ty);
        }
        let args = (w.args.iter().zip(with))
            .map(|(a, ty)| match ty {
                Some(ty) => Some(Arg {
                    at: a.as_ref().and_then(|a| a.at),
                    ..Arg::of(ty.clone())
                }),
                None => a.clone(),
            })
            .collect();
        let form = w.form.clone();
        self.trial(|ck| ck.construct(form, args, w.span))
    }

    /// The type the construct `w` has with the fixes `c` carried into its argument `i`, where
    /// it then adds no error but those its own check `found`, each inside another argument
    /// (`ats`, [`arg_holding`]); `None` where it adds another. One check of the construct and
    /// a binary search per error it adds.
    fn carried_alone(
        &mut self,
        w: &Written<'a>,
        found: &HashSet<Span>,
        ats: &[(Span, usize)],
        i: usize,
        c: &Carry,
    ) -> Option<Ty> {
        let (ty, needs) = self.carried_check(w, &[(i, &c.ty)]);
        let apart = |s: &Span| found.contains(s) && arg_holding(ats, *s).is_some_and(|j| j != i);
        needs
            .is_some_and(|needs| needs.iter().all(apart))
            .then_some(ty)
    }

    /// Settles the fixes of `round`, each carried into its own argument of the call `w`
    /// whose parameters are checked apart ([`params_apart`]) and whose own check gave the
    /// type `t` and rejected only `found`, all inside its arguments, as a check of the call
    /// with each alone settles them ([`Self::carried_alone`]): the call is rejected with an
    /// argument's fixes where its parameter does not take the type they give it, the rest of
    /// the call as written, so a check of a call of that parameter alone rejects them; the
    /// others are kept, with the type one check of the call with all of them in place gives,
    /// which is the type a check with each alone gives, since none of their arguments has a
    /// loose atom to pass on to it. Gives the fixes it leaves to [`Self::carried_alone`]: all
    /// of them where an argument of the round has a loose atom or a type with a variable or
    /// an unknown, or a check of a parameter alone is a trial with no verdict, and those kept
    /// where the check with all of them adds an error the call's own check did not, or one
    /// inside an argument of theirs. O(the call's check) for the round, besides one check of
    /// a call of one parameter per fix.
    fn carried_together(
        &mut self,
        w: &Written<'a>,
        t: &Ty,
        found: &HashSet<Span>,
        ats: &[(Span, usize)],
        round: Vec<(usize, Carry)>,
        up: &mut HashMap<Ty, Vec<Pending>>,
    ) -> Vec<(usize, Carry)> {
        let Construct::Call(what, sig) = &w.form else {
            return round;
        };
        let plain = |ty: &Ty| ty.closed() && ty.loose().is_empty();
        let plain = (round.iter())
            .all(|(i, c)| plain(&c.ty) && w.args[*i].as_ref().is_some_and(|a| plain(&a.ty)));
        if round.len() < 2 || !plain {
            return round;
        }
        let mut takes = Vec::with_capacity(round.len());
        for (i, c) in &round {
            let alone = param_alone(sig, *i);
            let at = w.args[*i].as_ref().and_then(|a| a.at);
            let arg = Some(Arg {
                at,
                ..Arg::of(c.ty.clone())
            });
            match self
                .trial(|ck| ck.apply(Label::Text(what), &alone, vec![arg], false, w.span))
                .1
            {
                Some(needs) => takes.push(needs.is_empty()),
                None => return round,
            }
        }
        let mut kept = Vec::with_capacity(round.len());
        for ((i, c), takes) in round.into_iter().zip(takes) {
            match takes {
                true => kept.push((i, c)),
                false => c.fixes.iter().for_each(|p| self.fix_dropped(p)),
            }
        }
        let tys: Vec<(usize, &Ty)> = kept.iter().map(|(i, c)| (*i, &c.ty)).collect();
        let (ty, needs) = self.carried_check(w, &tys);
        let mut held = vec![false; w.args.len()];
        kept.iter().for_each(|(i, _)| held[*i] = true);
        let apart = |s: &Span| found.contains(s) && arg_holding(ats, *s).is_some_and(|j| !held[j]);
        if !needs.is_some_and(|needs| needs.iter().all(apart)) {
            return kept;
        }
        if ty != *t {
            for (_, c) in kept {
                carry_joined(up, ty.clone(), c.fixes);
            }
        }
        Vec::new()
    }

    /// The fixes `up` by the type they give the construct at `span`, carried to the construct
    /// it is an argument of ([`Self::carried`]).
    fn carried_up(&mut self, span: Span, up: HashMap<Ty, Vec<Pending>>) {
        if !up.is_empty() {
            let up = up.into_iter().map(|(ty, fixes)| Carry { ty, fixes });
            self.carried.insert(span, up.collect());
        }
    }

    /// The error [`Found::id`] `id`, where it is still found: the errors keep the order they
    /// were found in, so a binary search, O(log errors).
    fn found(&self, id: usize) -> Option<&Found> {
        let i = self.errors.binary_search_by_key(&id, |e| e.id).ok()?;
        Some(&self.errors[i])
    }

    /// Drops the fix `p` from the menu of its rejection, which the errors hold in the order
    /// they were found in ([`Found::id`]), found by binary search, O(log errors); where that
    /// leaves none the message says that none is offered ([`Msg::dropped`]).
    fn fix_dropped(&mut self, p: &Pending) {
        let Ok(i) = self.errors.binary_search_by_key(&p.id, |e| e.id) else {
            return;
        };
        let e = &mut self.errors[i];
        match &p.offer {
            Offer::Edits(edits) => {
                if let Some(k) = e.m.fixes.iter().position(|f| f.edits == *edits) {
                    e.m.fixes.remove(k);
                    e.m.dropped |= e.m.fixes.is_empty();
                }
            }
            Offer::Note(at, text) => {
                e.notes.retain(|n| n.span != *at || n.text != *text);
                (e.m.noted).retain(|r| r.note.span != *at || r.note.text != *text);
                e.m.dropped |=
                    e.m.fixes.is_empty() && !e.notes.iter().any(|n| n.text.starts_with("repair:"));
            }
        }
    }

    /// The construct `form` applied to `args` at `span`, checked.
    fn construct(&mut self, form: Construct<'a>, mut args: Vec<Option<Arg<'a>>>, span: Span) -> Ty {
        match form {
            Construct::Binary(op, b) => {
                let y = args.pop().flatten().expect("two operands");
                let x = args.pop().flatten().expect("two operands");
                self.binary_op(op, x, y, b, span)
            }
            Construct::Word(w) => {
                let x = args.pop().flatten().expect("an argument");
                self.word_applied(w, x, span)
            }
            Construct::Call(what, sig) => self.apply(Label::Text(&what), &sig, args, false, span).0,
        }
    }

    /// The construct being checked ([`Self::written`]), when it is the application at `span`
    /// named `what`, checked with its argument `i` replaced by `with`: its type and the
    /// errors it then has, each inside another argument ([`Pending::needs`]), or `None` where
    /// it has another; `None` where it is not that application.
    fn written_with(
        &mut self,
        what: &str,
        span: Span,
        i: usize,
        with: Arg<'a>,
    ) -> Option<Option<(Ty, Vec<Span>)>> {
        let w = self.written.clone()?;
        if w.span != span || w.form.what() != what || i >= w.args.len() {
            return None;
        }
        let mut args = w.args.clone();
        args[i] = Some(with);
        let form = w.form.clone();
        let (ty, needs) = self.trial(|ck| ck.construct(form, args, span));
        let within = |at: Span, s: Span| at.start <= s.start && s.end <= at.end;
        let others: Vec<Span> = (w.args.iter().enumerate())
            .filter(|&(j, _)| j != i)
            .filter_map(|(_, a)| a.as_ref()?.at)
            .collect();
        let apart = |s: &Span| others.iter().any(|&a| within(a, *s));
        Some(needs.filter(|n| n.iter().all(apart)).map(|n| (ty, n)))
    }

    /// The type of `x[i]` for the argument `x` written at `at`, as a repair writes it, read
    /// as the program's own `x[i]` is ([`Self::at_index`]); `None` where that read is
    /// rejected. One read of `x`'s pieces.
    pub(super) fn component_read(&mut self, x: &Arg<'a>, i: usize, at: Span) -> Option<Ty> {
        let k = Arg::of(Ty::lit(&Value::int(i.into())));
        self.tried(|ck| ck.at_index(&x.ty, Some(i), k, None, at, false))
    }

    /// Whether the construct being checked ([`Self::written`]), when it is the one at `span`,
    /// checks with its argument written at `at` replaced by a value of the type `with` gives
    /// for it, as a repair writes a cast or a component in its place: `Some(false)` where
    /// `with` gives none (the cast always fails) or the construct is rejected with it, `None`
    /// where the construct is not the one at `span` or has no argument at `at`. One check
    /// of the construct, besides what `with` costs.
    pub(super) fn operand_replaced(
        &mut self,
        span: Span,
        at: Span,
        with: impl FnOnce(&mut Self, &Arg<'a>) -> Option<Ty>,
    ) -> Option<bool> {
        let w = self.written.clone()?;
        if w.span != span {
            return None;
        }
        let i = (w.args.iter()).position(|a| a.as_ref().and_then(|a| a.at) == Some(at))?;
        let Some(ty) = with(self, w.args[i].as_ref()?) else {
            return Some(false);
        };
        // The other arguments copied, the replaced one not: a tuple operand replaced by one
        // of its components is not copied once per component.
        let mut ty = Some(ty);
        let args = (w.args.iter().enumerate())
            .map(|(j, a)| match j == i {
                true => ty.take().map(|ty| Arg {
                    at: Some(at),
                    ..Arg::of(ty)
                }),
                false => a.clone(),
            })
            .collect();
        let form = w.form.clone();
        Some(self.tried(|ck| ck.construct(form, args, span)).is_some())
    }

    /// `==` and `!=`: any two values; a literal meets the other side's type by the rule of a
    /// parameter ([`Ck::follow`], [`expected`]), so `x == 1` is true at `x = 1.0` and
    /// `x == 1.5` with `x: int` is rejected; of two literals one without a suffix takes the
    /// other's carrier, and two without one are rejected where one is a decimal (`1 == 1.0`),
    /// since nothing gives it a carrier. Two tuples of one length are
    /// paired component by component, at any depth, across every tuple shape of that length a
    /// side's type holds, as [`adopted`] pairs them: `p == (1, 2)` with
    /// `p: (f64, f64) | (String, f64)` reads both literals at `f64`.
    ///
    /// The tuples nest as deep as the text, so the pairs wait on a stack, each with whether it
    /// is inside a tuple. Each side borrows its component types, one per shape, so a tuple
    /// nested d deep at s shapes costs O(d·s) and not a copy of each level's type.
    fn equal(&mut self, x: &Arg<'a>, y: &Arg<'a>) {
        let from = self.errors.len();
        self.pair(side(x), side(y));
        if !self.trying {
            self.equal_repairs(from, x, y);
            self.equal_repairs(from, y, x);
        }
    }

    /// The derivation and repairs of the rejection, among the errors from the `from`th on, of
    /// the literal `l` compared by `==` with the value `v` of other carriers in the row of a
    /// literal at a carrier it cannot take (`n == 1.5` with `n: int`): `v`'s derivation, the
    /// literal, and each cast of `v` with which the comparison checks, tried with the
    /// checker's state restored after, `f64(n)`. One trial per cast word.
    fn equal_repairs(&mut self, from: usize, l: &Arg<'a>, v: &Arg<'a>) {
        let (Some(lit), None, Some(at)) = (&l.lit, &v.lit, v.at) else {
            return;
        };
        let Some(k) = (from..self.errors.len()).find(|&k| {
            let e = &self.errors[k];
            e.span == lit.site && e.row == Some(Row::LiteralCarrier)
        }) else {
            return;
        };
        let mut notes = self.derive(&[at]);
        notes.push(Note {
            span: lit.span,
            text: literal_note(lit.written(), lit_ty(&lit.value, lit.neg())),
        });
        let held = match self.class_of_ty(&v.ty) {
            Some(r) if self.classes[r].mask & OTHER == 0 => Ty::of_mask(self.classes[r].mask),
            _ => v.ty.clone(),
        };
        let t = self.t;
        let name = match self.seen.get(&at) {
            Some((_, Src::Name(id))) => Some(&t.res.binders[*id].name),
            _ => None,
        };
        let op = self.comparing.as_ref().map(|c| c.op);
        // `v` is one of the operands of the comparison, found by its expression.
        let exact = self.comparing.as_ref().is_some_and(|c| {
            (0..2).any(|s| {
                c.exact[s]
                    && matches!((v.expr, c.exprs[s]), (Some(a), Some(b)) if std::ptr::eq(a, b))
            })
        });
        let lit_text = lit.written().to_string();
        let mut fixes = Vec::new();
        for w in ["int", "rat", "f64"] {
            let Some(r) = widening(w, &held, exact) else {
                continue;
            };
            // As written where the comparison is the construct being checked: the cast
            // applied to the operand, then the comparison with it in place
            // ([`Ck::operand_replaced`]); else the comparison with a value of the cast's type.
            let written = match self.comparing {
                Some(c) => self.operand_replaced(c.span, at, |ck, a| ck.wrapped(w, a, &held, at)),
                None => None,
            };
            let ok = written.unwrap_or_else(|| {
                let cast = Arg {
                    at: Some(at),
                    ..Arg::of(r)
                };
                self.tried(|ck| ck.equal(l, &cast)).is_some()
            });
            if ok {
                let text = match name {
                    Some(n) => format!("repair: write `{w}({n})`; the checker accepts that"),
                    None => format!("repair: wrap this in `{w}(…)`; the checker accepts that"),
                };
                notes.push(Note { span: at, text });
                // The comparison rewritten with the cast, `rat(n) == 1.5`, where the operand
                // is a name; the headline ends with the first.
                if let (Some(n), Some(op)) = (name, op) {
                    let alone = match lit.span.start < at.start {
                        true => format!("{lit_text} {op} {w}({n})"),
                        false => format!("{w}({n}) {op} {lit_text}"),
                    };
                    fixes.push(Rewrite::new(
                        &[
                            (point(at.start), &format_args!("{w}(")),
                            (point(at.end), &")"),
                        ],
                        &format_args!("{n} is cast to {w}"),
                        &alone,
                    ));
                }
            }
        }
        // The headline shows the comparison as code, `n : int == 1.5`, where the operand is a
        // name and the headline names the literal alone.
        let pair = match (name, op) {
            (Some(n), Some(op)) => {
                let shown = self.text(&held);
                Some(match lit.span.start < at.start {
                    true => format!("`{lit_text} {op} {n} : {shown}`"),
                    false => format!("`{n} : {shown} {op} {lit_text}`"),
                })
            }
            _ => None,
        };
        let e = &mut self.errors[k];
        e.notes = notes;
        if let Some(pair) = pair
            && let Some((head, _)) = e.m.text.split_once(": the literal `")
        {
            e.m.text = format!("{head}: {pair}.");
        }
        e.m.fixes.extend(fixes.into_iter().flatten());
    }

    /// [`Ck::equal`] of the two sides `x` and `y`. Inside an `==` or `!=` ([`Ck::comparing`]),
    /// each pair of components with no literal on either side, and each literal with a suffix
    /// with what it is compared with, is checked for a common carrier
    /// ([`no_common_carrier`]); of the pairs that have none, the first in written order is
    /// rejected ([`Ck::apart`]). The stack pops a tuple's components last first, so that pair
    /// is the last one met. Each pair keeps its place as an entry of `places`, the place of
    /// its tuple and its index there, so only the place of the pair rejected is put in words.
    fn pair(&mut self, x: Side<'_>, y: Side<'_>) {
        // The place of the operands themselves.
        const TOP: usize = usize::MAX;
        let mut places: Vec<(usize, usize)> = Vec::new();
        let mut last: Option<(usize, Ty, Ty)> = None;
        let checking = self.comparing.is_some();
        let mut leaf = |at: usize, xt: &[&Ty], yt: &[&Ty]| {
            if checking {
                let a = Ty::union_all(xt.iter().copied());
                let b = Ty::union_all(yt.iter().copied());
                if no_common_carrier(&a, &b) {
                    last = Some((at, a, b));
                }
            }
        };
        let mut stack = vec![(x, y, false, TOP)];
        while let Some(((xt, xl, xp), (yt, yl, yp), inner, at)) = stack.pop() {
            match (xl, yl) {
                (Some(l), Some(m)) => {
                    let (lc, mc) = (lit_carrier(&l.value), lit_carrier(&m.value));
                    // A literal with a suffix fixes the other's carrier. Of two without one,
                    // two integers are `int`, and a decimal is given no carrier by the
                    // other, which takes the carrier of its use too: it is rejected.
                    match (l.bare, m.bare) {
                        (true, true) if lc == Carrier::Int && mc == Carrier::Int => {}
                        (true, true) => {
                            let d = if lc == Carrier::F64 { l } else { m };
                            let notes = [l, m]
                                .map(|l| Note {
                                    span: l.span,
                                    text: literal_note(l.written(), lit_ty(&l.value, l.neg())),
                                })
                                .to_vec();
                            let m = unfixed(d, &[Carrier::F64, Carrier::Rat]);
                            self.reject(Some(Row::UnfixedDecimal), d.site, m, notes);
                        }
                        (true, false) => {
                            self.adopt_to(l, mc);
                        }
                        (false, true) => {
                            self.adopt_to(m, lc);
                        }
                        (false, false) => {}
                    }
                }
                // A literal with a suffix is a value of its carrier like any other.
                (Some(l), None) => {
                    if !l.bare {
                        leaf(at, &[&Ty::carrier(lit_carrier(&l.value))], &yt);
                    }
                    self.follow(l, &yt, inner, 1);
                }
                (None, Some(m)) => {
                    if !m.bare {
                        leaf(at, &xt, &[&Ty::carrier(lit_carrier(&m.value))]);
                    }
                    self.follow(m, &xt, inner, 0);
                }
                (None, None) if xp.is_none() && yp.is_none() => leaf(at, &xt, &yt),
                (None, None) => {
                    let n = xp.or(yp).map_or(0, <[Part]>::len);
                    let (Some(xs), Some(ys)) = (sides(&xt, xp, n), sides(&yt, yp, n)) else {
                        leaf(at, &xt, &yt);
                        continue;
                    };
                    for (i, (a, b)) in xs.zip(ys).enumerate() {
                        places.push((at, i));
                        stack.push((a, b, true, places.len() - 1));
                    }
                }
            }
        }
        if let Some((mut at, a, b)) = last {
            let mut path = Vec::new();
            while at != TOP {
                let (up, i) = places[at];
                path.push(i);
                at = up;
            }
            path.reverse();
            self.apart(&path, &a, &b);
        }
    }

    /// Rejects the `==` or `!=` being checked ([`Ck::comparing`]) whose operands, or whose
    /// components at the place `path` (indices from the operands down), are of the types `a`
    /// and `b`, which share no value at any carrier ([`no_common_carrier`]), unless the
    /// operands' own checks rejected something first. The comparison always gives the same
    /// answer. At the operands themselves the repairs are, first, the literal a cast that
    /// cannot fail gives on a literal operand, written in its place ([`Ck::literal_repair`]),
    /// `n == 8` for `n == "8"`, which keeps the other operand's type, as [`Ck::repairs`]
    /// puts such a repair first for `<` (row REPAIR-compare-order), or, where no literal
    /// writes that value, the cast kept around the literal, `r == rat("1/3")` (row
    /// REPAIR-eq-kept-cast); then each cast of one
    /// operand that makes the two meet, except the cast whose literal is offered; then each
    /// component of a tuple operand that may equal the other operand; with none, or inside
    /// the operands, the answer it always gives.
    fn apart(&mut self, path: &[usize], a: &Ty, b: &Ty) {
        let Some(Comparison {
            op,
            ats,
            exprs,
            exact,
            span,
            from,
        }) = self.comparing
        else {
            return;
        };
        if self.errors.len() != from {
            return;
        }
        let tables = self.t;
        let labels = [0, 1].map(|s| match ats[s].and_then(|at| self.seen.get(&at)) {
            Some((_, Src::Name(id))) => Some(Operand::Name(&tables.res.binders[*id].name)),
            _ => exprs[s]
                .filter(|_| path.is_empty())
                .and_then(|e| match &e.kind {
                    // A string literal is named as the program writes it, where that is one
                    // line with no backtick to end the code span around it, `"8"`.
                    ExprKind::Str(_) => (tables.text)
                        .and_then(|t| t.get(e.span.start..e.span.end))
                        .filter(|w| !w.contains(['\n', '`']))
                        .map(Operand::Text),
                    _ => is_literal(e).then_some(Operand::Literal(e, tables.text)),
                }),
        });
        let sides = [a, b];
        let mut fixes = [Vec::new(), Vec::new()];
        if path.is_empty() {
            let widened = sides.map(widened);
            // The literals first, each tried below where a cast is written; only where the
            // message is shown, since the trial that finds the literal is what writes it.
            for s in (0..2).filter(|_| !self.trying) {
                let literal =
                    exprs[s].is_some_and(|e| is_literal(e) || matches!(e.kind, ExprKind::Str(_)));
                let Some(other) = widened[1 - s].as_ref().filter(|_| literal) else {
                    continue;
                };
                let words = [
                    ("int", Carrier::Int),
                    ("rat", Carrier::Rat),
                    ("f64", Carrier::F64),
                ];
                for (w, c) in words {
                    if widened_meets(&Ty::carrier(c), other) {
                        fixes[0].push(Fix::Literal(s, w));
                    }
                }
            }
            for s in 0..2 {
                let Some(other) = &widened[1 - s] else {
                    continue;
                };
                for w in ["int", "rat", "f64"] {
                    if let Some(r) = widening(w, sides[s], exact[s])
                        && widened_meets(&r, other)
                    {
                        fixes[0].push(Fix::Cast(s, w));
                    }
                }
            }
            for s in 0..2 {
                let Some(other) = &widened[1 - s] else {
                    continue;
                };
                let values = sides[s].without_atoms();
                let u = values.set.universes();
                let tuples_only = !u.bases.iter().any(|&b| b) && !u.rest;
                let width = (values.tuples.iter().map(|r| r.len()).min())
                    .filter(|_| tuples_only)
                    .unwrap_or(0);
                for i in 0..width {
                    let c = Ty::union_all(values.tuples.iter().map(|r| &r[i]));
                    if widened_meets(&c, other) {
                        fixes[1].push(Fix::Component(s, i));
                    }
                }
            }
        }
        // Each fix checked as written: the comparison checked again with the cast operand, or
        // its component, in place of the operand ([`Ck::operand_replaced`]); a fix with which
        // it is rejected is dropped, and with none left the answer is offered.
        // Complexity tradeoff: at most six casts and one component per index of the narrower
        // tuple, each one trial of the comparison with one operand replaced, which costs the
        // size of the other operand and of the replacement, never the replaced tuple again
        // (test `l01_29_diagnostics::scaling::checking_the_components_offered_for_a_wide_tuple_scales`).
        // The naive way, checking the program again with each fix written in, costs the
        // size of the program per fix. A literal fix adds at most three more trials, each
        // after one run of its cast on the literal's one value ([`Ck::literal_repair`]) (test
        // `l01_29_diagnostics::scaling::offering_the_literal_first_in_comparisons_scales`);
        // where no literal writes the value, one application of the cast to the literal
        // ([`Ck::wrapped`]) besides, the cost of checking `rat("1/3")` as written (test
        // `l01_29_diagnostics::scaling::offering_the_cast_of_a_literal_in_comparisons_scales`).
        // The text of each literal kept, by side and word.
        let mut literals: Vec<(usize, &str, String)> = Vec::new();
        if !self.trying {
            for group in &mut fixes {
                let mut kept = Vec::new();
                for fix in std::mem::take(group) {
                    let (Fix::Cast(s, _) | Fix::Literal(s, _) | Fix::Component(s, _)) = fix;
                    // A cast whose literal is offered is not offered beside it.
                    if let Fix::Cast(_, w) = fix
                        && literals.iter().any(|&(t, v, _)| (t, v) == (s, w))
                    {
                        continue;
                    }
                    let mut text = None;
                    let checks = ats[s].and_then(|at| {
                        self.operand_replaced(span, at, |ck, a| match fix {
                            Fix::Cast(_, w) => ck.wrapped(w, a, &a.ty, at),
                            Fix::Literal(s, w) => match ck.literal_repair(w, a, &a.ty, at) {
                                Some(l) => {
                                    // A `rat` literal's digits as the program writes them,
                                    // `0.5_0` for `0.5_0r`, as [`Ck::repairs`] writes them
                                    // ([`rat_forms`]); the value is the one checked, as both
                                    // run the cast `w` on the one number (row
                                    // RED-written-compare). O(d) for d digits.
                                    let written = (exprs[s].and_then(|e| rat_forms(e, ck.t.text)))
                                        .and_then(|forms| {
                                            forms.into_iter().find_map(|(ty, lit, _)| {
                                                lit.filter(|_| {
                                                    ty.numeric_carrier().map(Carrier::name)
                                                        == Some(w)
                                                })
                                            })
                                        });
                                    text = Some(written.unwrap_or(l.text));
                                    Some(l.arg.ty)
                                }
                                // No literal writes the value, as for `rat("1/3")`: the cast
                                // kept around the literal, where it gives no atom the literal
                                // lacks, so it cannot fail on it, as [`Ck::repairs`] offers
                                // `r < rat("1/3")` (row REPAIR-eq-kept-cast).
                                None => {
                                    let r = (ck.wrapped(w, a, &a.ty, at))
                                        .filter(|r| r.atoms() == a.ty.atoms())?;
                                    text = Some(format!("{w}({})", ck.code(Some(at))?));
                                    Some(r)
                                }
                            },
                            Fix::Component(_, i) => ck.component_read(a, i, at),
                        })
                    });
                    match (fix, text) {
                        (Fix::Literal(_, w), Some(t)) if checks == Some(true) => {
                            literals.push((s, w, t));
                        }
                        (Fix::Literal(..), _) => continue,
                        _ if checks == Some(false) => continue,
                        _ => {}
                    }
                    kept.push(fix);
                }
                *group = kept;
            }
        }
        let [fixes, components] = fixes;
        let groups = [
            (fixes, "to compare the numbers"),
            (components, "to compare a component"),
        ];
        let answer = groups.iter().all(|(rs, _)| rs.is_empty());
        let shown = sides.map(|t| self.shown(&t.carriers()));
        let ends = ["left", "right"];
        let named = match &labels {
            [Some(l), Some(m)] if path.is_empty() => Some((l, m)),
            _ => None,
        };
        // The literal a kept literal fix writes; every one kept has one.
        let literal = |s: usize, w: &str| {
            (literals.iter())
                .find(|&&(t, v, _)| (t, v) == (s, w))
                .map_or("…", |(_, _, text)| text.as_str())
        };
        let form = |f: &mut fmt::Formatter<'_>, r: Fix| match (named, r) {
            (Some((_, m)), Fix::Literal(0, w)) => write!(f, "`{} {op} {m}`", literal(0, w)),
            (Some((l, _)), Fix::Literal(s, w)) => write!(f, "`{l} {op} {}`", literal(s, w)),
            (None, Fix::Literal(s, w)) => {
                write!(f, "`{}` in place of the {} operand", literal(s, w), ends[s])
            }
            (Some((l, m)), Fix::Cast(0, w)) => write!(f, "`{w}({l}) {op} {m}`"),
            (Some((l, m)), Fix::Cast(_, w)) => write!(f, "`{l} {op} {w}({m})`"),
            (Some((l, m)), Fix::Component(0, i)) => write!(f, "`{l}[{i}] {op} {m}`"),
            (Some((l, m)), Fix::Component(_, i)) => write!(f, "`{l} {op} {m}[{i}]`"),
            (None, Fix::Cast(s, w)) => write!(f, "`{w}(…)` around the {} operand", ends[s]),
            (None, Fix::Component(s, i)) => write!(f, "`[{i}]` after the {} operand", ends[s]),
        };
        let in_place = |f: &mut fmt::Formatter<'_>| {
            write!(f, "`{}` in place of ", op != BinaryOp::Eq)?;
            match named {
                Some((l, m)) => write!(f, "`{l} {op} {m}`"),
                None => f.write_str("the comparison"),
            }
        };
        // The headline (DESIGN.md sec:diagnostics, "A short headline"): the comparison as code
        // with the type of each side, `x : int == y : f64`, where both sides are named; else
        // each side described with its type. It ends with the first repair, or the answer.
        let message = quoting(
            &fmt::from_fn(|f| {
                write!(f, "No value is both `{}` and `{}`: ", shown[0], shown[1])?;
                let code = |s: usize| match (&labels[s], path) {
                    (Some(l), []) => Some(format!("{l} : {}", shown[s])),
                    (Some(l @ Operand::Name(_)), _) => {
                        Some(format!("{l}{} : {}", Place(path), shown[s]))
                    }
                    _ => None,
                };
                match (code(0), code(1)) {
                    (Some(a), Some(b)) => write!(f, "`{a} {op} {b}`")?,
                    _ => {
                        for (s, end) in ends.iter().enumerate() {
                            if s == 1 {
                                write!(f, " compared by `{op}` with ")?;
                            }
                            match (code(s), path) {
                                (Some(c), _) => write!(f, "`{c}`")?,
                                (None, []) => write!(f, "the {} operand", end)?,
                                (None, _) => {
                                    write!(f, "component `{}` of the {} operand", Place(path), end)?
                                }
                            }
                        }
                    }
                }
                if answer {
                    let a = op != BinaryOp::Eq;
                    return write!(f, " is always `{a}`. Try `{a}` instead.");
                }
                f.write_str(" always gives the same answer. Try ")?;
                write_repairs(f, &groups, form)?;
                f.write_str(" instead.")
            }),
            || {
                format!(
                    "the two sides of this `{op}` share no value, so the comparison always \
                     gives the same answer"
                )
            },
        );
        let row = match sides.iter().all(|t| only_numbers(t)) {
            true => Row::NoCommonCarrier,
            false => Row::EqNoCommonCarrier,
        };
        let mut notes = self.derive(&ats.into_iter().flatten().collect::<Vec<_>>());
        // The menu again as repair steps, in the order the message lists it.
        let repairs = groups.iter().flat_map(|(rs, _)| rs.iter());
        notes.extend(repairs.map(|&r| Note {
            span,
            text: format!("repair: write {}", fmt::from_fn(|f| form(f, r))),
        }));
        if answer {
            let text = format!("repair: write {}", fmt::from_fn(in_place));
            notes.push(Note { span, text });
        }
        self.rejects_with(row, span, message, notes);
    }

    /// Whether the application of `sig` to `args`, named `what`, checks with argument `i`
    /// replaced by `with`, tried with the checker's state restored after: as written, where
    /// it is the construct being checked ([`Self::written_with`]), with the type it then has
    /// and the errors left in its other arguments, else as an application, with neither.
    fn repaired(
        &mut self,
        what: Label<'_>,
        sig: &Sig,
        args: &[Option<Arg<'a>>],
        (i, with): (usize, Arg<'a>),
        pass: bool,
        span: Span,
    ) -> Option<Option<(Ty, Vec<Span>)>> {
        if let Some(got) = self.written_with(what.text(), span, i, with.clone()) {
            return got.map(Some);
        }
        let mut args = args.to_vec();
        args[i] = Some(with);
        self.tried(|ck| ck.apply(what, sig, args, pass, span))
            .map(|_| None)
    }

    /// The notes of the repairs `repairs`, each recorded as offered ([`Self::note_offered`]).
    fn offered(&mut self, repairs: Vec<Repaired>) -> Vec<Note> {
        (repairs.into_iter())
            .map(|r| {
                self.note_offered(&r.note, r.got);
                r.note
            })
            .collect()
    }

    /// The note `note`, a repair [`Self::repaired`] checked as written, which gave the
    /// construct being checked the type and left the errors of `got`, pending for the
    /// rejection about to be found ([`Pending`]); nothing where it was not checked as written
    /// or a repair is being tried.
    fn note_offered(&mut self, note: &Note, got: Option<(Ty, Vec<Span>)>) {
        if let (false, Some((ty, needs))) = (self.trying, got) {
            self.pending_fixes.push(Pending {
                id: self.next_found,
                offer: Offer::Note(note.span, note.text.clone()),
                needs,
                ty,
            });
        }
    }

    /// `m`'s fixes, for a rejection at `span`, each checked as written: where the rejection
    /// lies in the construct being checked ([`Self::written`]) and a fix rewrites its
    /// arguments alone, the construct is checked again with the arguments the fix writes, and
    /// a fix where that adds an error is dropped, except one where it adds errors only inside
    /// arguments the fix does not edit: that one is kept where the construct's own check
    /// rejects those too ([`Pending`], [`Self::pending_settled`]), so each rejected argument
    /// of `f(1.0f64, 1.0f64)` offers its own fix. A fix that writes anything else is kept as
    /// it is: one in a part of an argument, `(1 + 0.5r)` for `(1 + 0.5)`, or one that
    /// rewrites the whole comparison. Where every fix is dropped the message says that none is
    /// offered ([`Msg::dropped`]).
    ///
    /// Complexity tradeoff: one check of the construct per fix, each the cost of checking it
    /// once, so a rejection with k fixes costs k + 1 checks of its construct, k at most the
    /// carriers a literal can take (DESIGN.md sec:diagnostics), at most 3 per argument. The
    /// naive way, checking the whole program again with each fix in place, costs the size of
    /// the program per fix; a fix rewrites one construct's arguments, and the rest of the
    /// program reads only that construct's type, which the trial gives. A rejection outside
    /// a recorded construct keeps its fixes unchecked.
    pub(super) fn fixes_checked(&mut self, span: Span, m: &mut Msg) {
        let Some(w) = self.written.clone() else {
            return;
        };
        let Some(src) = self.t.text else {
            return;
        };
        if span.start < w.span.start || w.span.end < span.end {
            return;
        }
        let fixes = std::mem::take(&mut m.fixes);
        let made = fixes.len();
        for fix in fixes {
            let keep = match self.fix_args(&w, &fix, src) {
                Mapped::Args(args) => {
                    let (form, at) = (w.form.clone(), w.span);
                    // Errors only inside arguments the fix leaves as they are, as the other
                    // rejected arguments of `f(1.0f64, 1.0f64)`, are the construct's own where
                    // its check rejects them too, which is known when it ends; and the type
                    // the fix gives the construct is checked where the construct is used then.
                    let (ty, needs) = self.trial(|ck| ck.construct(form, args, at));
                    // Complexity tradeoff: the naive test of each argument against each edit,
                    // and of each error against each argument, costs their products, the
                    // square of the width where one fix rewrites every argument of a wide
                    // call (`f(1.0f64, …, 1.0f64)`, [`Self::literals_refused`]). Used: the
                    // edits and the arguments sorted by where they start, each looked up by
                    // binary search, O((a + e + n) log(a + e)) for `a` arguments, `e` edits
                    // and `n` errors.
                    let sorted = in_text_order(&fix.edits);
                    let mut others: Vec<Span> = (w.args.iter().flatten())
                        .filter_map(|a| a.at)
                        .filter(|&a| edits_in(&sorted, a).next().is_none())
                        .collect();
                    others.sort_by_key(|a| (a.start, a.end));
                    let apart = |s: &Span| lies_in(&others, *s);
                    let keep = needs.as_ref().is_some_and(|n| n.iter().all(apart));
                    if keep {
                        self.pending_fixes.push(Pending {
                            id: self.next_found,
                            offer: Offer::Edits(fix.edits.clone()),
                            needs: needs.unwrap_or_default(),
                            ty,
                        });
                    }
                    keep
                }
                Mapped::Fails => false,
                Mapped::Unread => true,
            };
            if keep {
                m.fixes.push(fix);
            }
        }
        m.dropped |= made > 0 && m.fixes.is_empty();
    }

    /// The arguments of the construct `w` with the fix `fix` written in the program's text
    /// `src`, where each of its edits lies in an argument and rewrites it to one the checker
    /// reads alone ([`Self::written_arg`]).
    fn fix_args(&mut self, w: &Written<'a>, fix: &Rewrite, src: &str) -> Mapped<'a> {
        // Complexity tradeoff: the naive test of each edit against each argument costs their
        // product, the square of the width where one fix rewrites every argument of a wide
        // call. Used: the edits sorted by where they start, and those of each argument found
        // by binary search, O((a + e) log e) for `a` arguments and `e` edits.
        let sorted = in_text_order(&fix.edits);
        let mut placed = vec![false; sorted.len()];
        let mut each = Vec::new();
        for (i, a) in w.args.iter().enumerate() {
            let Some((a, at)) = a.as_ref().and_then(|a| Some((a, a.at?))) else {
                continue;
            };
            let edits: Vec<&(Span, String)> = edits_in(&sorted, at)
                .map(|(k, e)| {
                    placed[k] = true;
                    e
                })
                .collect();
            if !edits.is_empty() {
                each.push((i, a, at, edits));
            }
        }
        if placed.contains(&false) {
            return Mapped::Unread;
        }
        let mut args = w.args.clone();
        for (i, a, at, edits) in each {
            let Some(text) = edited(src, at, &edits) else {
                return Mapped::Unread;
            };
            let Some(was) = src.get(at.start..at.end) else {
                return Mapped::Unread;
            };
            match self.written_arg(&text, was, a, at) {
                Mapped::Args(mut one) => args[i] = one.pop().flatten(),
                other => return other,
            }
        }
        Mapped::Args(args)
    }

    /// The argument `a`, written `was` at `at`, as the program writes it in place of `was`
    /// the text `text`, where the checker reads that alone: `a` in a cast or conversion
    /// word, as `f64(0xFF)` or `rat(n)`, which fails where the word's application does
    /// ([`Self::wrapped`]); a component of `a`, as `x[1]` ([`Self::component`]); a numeric
    /// literal, perhaps under one `-`; a `rat` literal; a string literal without holes;
    /// `true` or `false`.
    fn written_arg(&mut self, text: &str, was: &str, a: &Arg<'a>, at: Span) -> Mapped<'a> {
        if let Some(i) = (text.strip_prefix(was))
            .and_then(|r| r.strip_prefix('['))
            .and_then(|r| r.strip_suffix(']'))
            .and_then(|r| r.parse::<usize>().ok())
        {
            return match self.component_read(a, i, at) {
                Some(ty) => Mapped::Args(vec![Some(Arg {
                    at: Some(at),
                    ..Arg::of(ty)
                })]),
                None => Mapped::Fails,
            };
        }
        if let Some(inner) = text.strip_suffix(')')
            && let Some((w, rest)) = inner.split_once('(')
            && rest == was
        {
            let Some(w) = ["String", "int", "rat", "f64"]
                .into_iter()
                .find(|&x| x == w)
            else {
                return Mapped::Unread;
            };
            return match self.wrapped(w, a, &a.ty, at) {
                Some(ty) => Mapped::Args(vec![Some(Arg {
                    at: Some(at),
                    ..Arg::of(ty)
                })]),
                None => Mapped::Fails,
            };
        }
        let Ok(tokens) = lex(text) else {
            return Mapped::Unread;
        };
        let (neg, rest) = match tokens.as_slice() {
            [t, rest @ ..] if matches!(t.tok, Tok::Op("-")) => (true, rest),
            all => (false, all),
        };
        let [t] = rest else {
            return Mapped::Unread;
        };
        // The literal's span, without its `-`, which is one char long at its start.
        if neg && at.end - at.start < 2 {
            return Mapped::Unread;
        }
        let span = Span {
            start: at.start + usize::from(neg),
            end: at.end,
        };
        let number = |kind| {
            let mut l = read_literal(&Expr { kind, span }, None).ok()??;
            l.site = at;
            Some(Arg {
                ty: lit_ty(&l.value, l.neg()),
                lit: Some(l),
                at: Some(at),
                ..Arg::of(Ty::empty())
            })
        };
        let arg = match &t.tok {
            Tok::Int { radix, digits } => number(ExprKind::Int {
                radix: *radix,
                digits: Arc::clone(digits),
            }),
            Tok::Float { digits, forced } => number(ExprKind::Float {
                digits: Arc::clone(digits),
                forced: *forced,
            }),
            Tok::Rat(d) => match Rat::decimal(d) {
                Ok(Some(r)) => Some(Arg {
                    at: Some(at),
                    ..Arg::of(lit_ty(&Value::rat(r), neg))
                }),
                _ => None,
            },
            Tok::Str(parts) if !neg => match parts.as_slice() {
                [] => Some(Value::str("")),
                [zedc_syntax::lex::Part::Text(s)] => Some(Value::str(s)),
                _ => None,
            }
            .map(|v| Arg {
                at: Some(at),
                ..Arg::of(Ty::lit(&v))
            }),
            Tok::Keyword(k @ ("true" | "false")) if !neg => Some(Arg {
                at: Some(at),
                ..Arg::of(Ty::lit(&Value::Bool(*k == "true")))
            }),
            _ => None,
        };
        match arg {
            Some(a) => Mapped::Args(vec![Some(a)]),
            None => Mapped::Unread,
        }
    }

    /// Applies `sig` to `args`, a missing one filled by its default. When `pass` holds, as
    /// for an operator or a prelude word, an argument's atoms pass through, two arguments'
    /// merged into `#errs`. Gives the result and the arrows kept. An operator, a prelude word
    /// and a lookup in a family need every argument's value; a function's body reads what its
    /// result says ([`Demand`]).
    fn apply(
        &mut self,
        what: Label<'_>,
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

    /// Whether an application refused here follows an error already reported, outside a
    /// trial: an argument has no value and is a call whose arguments do not fit, or an
    /// application that took its empty type from one ([`Ck::failed`]). `f(true) + "a"`, with
    /// `f(b: bool) = 7` called by position, has the one error of the call, and no second one
    /// saying that `+` does not take `(Never, "a")`, where `Never` says only that the checker
    /// gave the call no value.
    ///
    /// Complexity tradeoff: one lookup in a hash set per argument, only when the application
    /// is refused or gives the empty type, O(arguments). The naive way, a search of the errors
    /// reported for one inside each argument's text, is O(errors) per refused application and
    /// O(n²) over a line of n refused operations; the set holds one span per misfit call and
    /// per application its empty type flows into. A name defined as such a call, `y` after
    /// `y = f(true)`, is followed to its definition by one more lookup.
    fn follows_error(&self, args: &[Option<Arg<'a>>]) -> bool {
        let failed = |e: &Expr| {
            self.failed.contains(&e.span)
                || match self.seen.get(&e.span) {
                    Some((_, Src::Name(id))) => self.whence.get(id).is_some_and(|o| {
                        matches!(o.why, Why::Defined(_))
                            && o.from.is_some_and(|f| self.failed.contains(&f))
                    }),
                    _ => false,
                }
        };
        !self.trying
            && (args.iter().flatten()).any(|a| a.ty.is_empty() && a.expr.is_some_and(failed))
    }

    /// [`Self::apply`], the arguments the call needs the values of given by `demand`.
    fn apply_demanding(
        &mut self,
        what: Label<'_>,
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
        let need_from = self.need_from.take();
        let leaving = std::mem::take(&mut self.leaving);
        if (sig.needs.iter()).any(|n| matches!(n.kind, NeedKind::InDomain { .. })) {
            self.floors_at(
                what.text(),
                sig,
                &args,
                &leaving,
                need_from.as_deref(),
                span,
            );
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
                    self.refused.push((what.text().into(), i, refused));
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
            let t = self.min_max_tuples(what.text(), sig, &x.ty, &y.ty, written.clone(), span);
            return (out.union(&t), Vec::new());
        }
        let defer = std::mem::take(&mut self.defer);
        let passing = self.need_passed.len();
        let refusals = self.lit_refused.len();
        let made = self.top_parts.len();
        let r = match (sig.arrows.len(), self.first_taking(sig, &args, pass)) {
            (1, _) => self.apply_one(what.text(), sig, 0, &args, &unneeded, defer, span),
            (_, Some(k)) => self.apply_one(what.text(), sig, k, &args, &unneeded, defer, span),
            _ => {
                let r = self.apply_many(what.text(), sig, &mut args, &unneeded, span);
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
        // The literals refused are their own error where the application takes the other
        // arguments; where it refuses another argument too, as `h(1.0f64, true)` at two
        // `rat` parameters, they are steps of the application's one error, which lists every
        // argument (MSG-many-args-one-error). A trial keeps them apart: its verdict is the
        // spans rejected, the same either way.
        let mut refused = self.lit_refused.split_off(refusals);
        if r.is_ok() || self.trying {
            self.literals_refused(what, sig, &args, std::mem::take(&mut refused), pass, span);
        }
        match r {
            Ok((t, kept)) => {
                let t = out.union(&t);
                // `f(true) + 1.5f64` takes the `Never` of the rejected call and gives it.
                if t.is_empty() && self.follows_error(&args) {
                    self.failed.insert(span);
                }
                (t, kept)
            }
            Err(_) if self.follows_error(&args) => {
                self.applied = None;
                if out.is_empty() {
                    self.failed.insert(span);
                }
                (out, Vec::new())
            }
            Err(message) => {
                self.applied = None;
                refused.sort_by_key(|(s, _)| (s.start, s.end));
                let also: Vec<Span> = refused.iter().map(|(s, _)| *s).collect();
                let mut notes: Vec<Note> = (refused.into_iter())
                    .map(|(span, m)| Note { span, text: m.text })
                    .collect();
                notes.extend(self.applied(what.text(), sig, &args, span));
                let mut seen: HashSet<Note> = notes.iter().cloned().collect();
                for a in args.iter().flatten() {
                    for n in self.reasons(&a.ty) {
                        if seen.insert(n.clone()) {
                            notes.push(n);
                        }
                    }
                }
                let repairs = self.repairs(what, sig, &args, pass, span);
                // A `rat` literal beside a number of another carrier, as `-3r` in `n * -3r`, gets
                // the message of a literal whose suffix forces its carrier, with the repairs as
                // fixes written in the program's text (MSG-concise-no-common-carrier). The
                // message names the literal, so the literal's own forms come first, `n * -3`
                // before `rat(n) * -3r`; each cast is a step as well, as in the row of a literal
                // at a carrier it cannot take ([`Self::literals_refused`]).
                if let Some((at, text)) = self.forced_rat(what, sig, &args) {
                    let (own, casts): (Vec<_>, Vec<_>) =
                        repairs.into_iter().partition(|r| r.note.span == at);
                    let mut fixes: Vec<_> = own.into_iter().map(|r| r.fix).collect();
                    for r in casts {
                        self.note_offered(&r.note, r.got);
                        notes.push(r.note);
                        fixes.push(r.fix);
                    }
                    self.reject(Some(Row::NoCommonCarrier), at, Msg::new(text, fixes), notes);
                    return (out, Vec::new());
                }
                // Every rejected application ends its headline with its first repair, as the
                // whole call rewritten: `sqrt(f64(n))`, `rat(x) + y`, `h(f64(y))`, and
                // `sum((rat(x), y))` for the `+` that `sum` applies, whose components are not
                // an expression of their own ([`Label::SumPlus`]) (DESIGN.md sec:diagnostics,
                // "A short headline"; row MSG-apply-try-headline). The repair is the first of
                // the notes that the program's text can show, and the headline is written
                // when the check ends ([`Msg::written`]), so a repair a later check drops
                // from the notes ([`Ck::fix_dropped`]) leaves the headline too. A prelude
                // word applied to one name that no repair fits, as `sqrt(n)` with `n` an
                // `int` that may lie above 2^53, where `f64(n)` is inexact and no repair
                // narrows, gets the repair of a comparison with no cast: a change of the
                // type, a note with no rewrite. Cost: the naive way writes each repair's call
                // as it is found, the length of the call for each of r repairs, for errors a
                // later step may drop; used: each repair's note is copied once, O(r) beside
                // the r notes already built, and only the first is written, once the length
                // of the call, for the errors kept (as the menu, [`Ck::reject`]).
                let word = (what.text().strip_prefix('`'))
                    .and_then(|w| w.strip_suffix('`'))
                    .filter(|w| sig.word.as_deref() == Some(*w))
                    .is_some_and(|w| zedc_resolve::resolve::prelude_layer(w).is_some());
                if repairs.is_empty()
                    && word
                    && let [Some(Arg { at: Some(at), .. })] = &args[..]
                    && let Some((_, Src::Name(id))) = self.seen.get(at)
                {
                    let n = &self.t.res.binders[*id].name;
                    let text = format!("repair: change the type of `{n}` so that {what} takes it");
                    notes.push(Note { span: *at, text });
                }
                let call = match what {
                    Label::SumPlus(call) => call,
                    _ => span,
                };
                let mut noted = Vec::new();
                for r in repairs {
                    self.note_offered(&r.note, r.got);
                    if let Some(fix) = r.fix {
                        let note = r.note.clone();
                        noted.push(NotedRepair {
                            note,
                            at: call,
                            fix,
                            tail: String::new(),
                        });
                    }
                    notes.push(r.note);
                }
                let row = if self.no_arrow_at_carrier(what, sig, &args) {
                    Some(Row::NoArrowAtCarrier)
                } else if self.no_common_carrier(sig, &args) {
                    Some(Row::NoCommonCarrier)
                } else {
                    None
                };
                self.reject(row, span, Msg::noted(message, noted), notes);
                if let Some(e) = self.errors.last_mut().filter(|_| !also.is_empty()) {
                    e.also = also;
                }
                (out, Vec::new())
            }
        }
    }

    /// Reports the literals of `args` rejected at parameters of `sig`, each with its place and
    /// its message: in the row of an operator with no arrow at its operands' carrier where that
    /// holds (`x / 2` with `x: int`); in the row of a literal at a carrier it cannot take where
    /// the operands have no common carrier (`q * 2.0` with `q: int`), with the application's
    /// derivation and the casts of the other operands the checker accepts, `f64(q)`, where the
    /// message holds the literal's own forms, and with the message naming the operator and
    /// the operand of carrier `int` where a decimal literal meets one (DESIGN.md
    /// sec:diagnostics, the worked example at an operator); and in no row otherwise. One
    /// literal is its own error; two or more of one application are one error, whose steps
    /// are each literal's message and whose fixes make the fix of each literal at once
    /// ([`grouped`]), `f(1.0f64, 1.0f64)` at two `int` parameters.
    ///
    /// Complexity tradeoff: the naive way, each literal its own error with the rows and the
    /// application's notes decided for it, costs O(n) per literal for `n` arguments, as does
    /// finding the literal among them, so O(n²) per application; and each error's fix,
    /// checked by checking the whole call again ([`Self::fixes_checked`]) where the other
    /// literals are refused again, makes `f(1.0f64, …, 1.0f64)` cost O(n³) and write the call
    /// once per literal, Θ(n²) bytes. Used: the rows, the operand of carrier `int` and a map
    /// from each literal's place to it are made once per application, O(n), and the literals
    /// are one error with one fix of each rank, checked by one check of the call; the message
    /// writes the call once per fix. Test:
    /// `l01_29_diagnostics::scaling::many_literal_arguments_refused_at_their_parameters_scale`.
    fn literals_refused(
        &mut self,
        what: Label<'_>,
        sig: &Sig,
        args: &[Option<Arg<'a>>],
        mut refused: Vec<(Span, Msg)>,
        pass: bool,
        span: Span,
    ) {
        if refused.is_empty() {
            return;
        }
        // A decimal literal beside an operand that is an `int` gets the worked message of
        // sec:diagnostics, which names the operand: an operand whose numbers are `int`s, as
        // `n` bound to `1`, or of a class that holds `int` alone.
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
        let t = self.t;
        let name = other
            .and_then(|o| o.at)
            .and_then(|at| match self.seen.get(&at) {
                Some((_, Src::Name(id))) => Some((t.res.binders[*id].name.as_str(), at)),
                _ => None,
            });
        // The operator's symbol, where it is a binary arithmetic operator or an ordering, each
        // of which has arrows at `rat` and at `f64`.
        let op = match what.operator() {
            Some(Operator::Binary(
                o @ (BinaryOp::Add
                | BinaryOp::Sub
                | BinaryOp::Mul
                | BinaryOp::Div
                | BinaryOp::Lt
                | BinaryOp::Le
                | BinaryOp::Gt
                | BinaryOp::Ge),
            )) if args.len() == 2 => Some(o),
            Some(Operator::Binary(
                BinaryOp::Or
                | BinaryOp::And
                | BinaryOp::Eq
                | BinaryOp::Ne
                | BinaryOp::Lt
                | BinaryOp::Le
                | BinaryOp::Gt
                | BinaryOp::Ge
                | BinaryOp::Add
                | BinaryOp::Sub
                | BinaryOp::Concat
                | BinaryOp::Mul
                | BinaryOp::Div
                | BinaryOp::IntDiv
                | BinaryOp::Mod
                | BinaryOp::Pow,
            ))
            | Some(Operator::Unary(UnaryOp::Neg | UnaryOp::Not))
            | None => None,
        };
        let lits: HashMap<Span, &Lit> = (args.iter().flatten())
            .filter_map(|a| a.lit.as_ref().map(|l| (l.site, l)))
            .collect();
        let left = args[0]
            .as_ref()
            .and_then(|a| a.lit.as_ref())
            .map(|l| l.site);
        if let Some(o) = other {
            // `f64(n)` is offered where the checker proves `n` lies within ±2^53, where it is
            // exact (DESIGN.md "Casts are domain proofs"); it is never offered otherwise. The
            // proof is asked once, at the first decimal literal, for all of them.
            let mut exact = None;
            for (s, m) in &mut refused {
                let Some(l) = lits.get(s).filter(|l| is_decimal(&l.value)) else {
                    continue;
                };
                let exact = *exact
                    .get_or_insert_with(|| name.is_some() && op.is_some() && self.exact_in_f64(o));
                let op = op.map(|o| (o, left == Some(*s)));
                match l.bare {
                    true => *m = decimal_at_int(l, what.text(), name, op, exact),
                    false => {
                        if let (true, Some((n, at)), Some((op, left))) = (exact, name, op) {
                            m.fixes.extend(f64_cast_fix(l, n, at, op, left));
                        }
                    }
                }
            }
        }
        let row = match self.no_arrow_at_carrier(what, sig, args) {
            true => Row::NoArrowAtCarrier,
            false => Row::LiteralCarrier,
        };
        // Where the operands have no common carrier, the application's derivation and
        // repairs, once for all its literals; otherwise each literal's own derivation.
        let applied = row == Row::LiteralCarrier && self.no_common_carrier(sig, args);
        let mut notes = Vec::new();
        if applied && !self.trying {
            notes = self.applied(what.text(), sig, args, span);
            let mut seen: HashSet<Note> = notes.iter().cloned().collect();
            for a in args.iter().flatten() {
                for n in self.reasons(&a.ty) {
                    if seen.insert(n.clone()) {
                        notes.push(n);
                    }
                }
            }
            let repairs = self.repairs(what, sig, args, pass, span);
            notes.extend(self.offered(repairs));
        }
        if refused.len() == 1 {
            let (s, m) = refused.pop().expect("one literal");
            if !applied {
                notes = self.derive(&[s]);
            }
            return self.reject(Some(row), s, m, notes);
        }
        refused.sort_by_key(|(s, _)| (s.start, s.end));
        let at = refused[0].0;
        let sites: Vec<Span> = refused.iter().map(|(s, _)| *s).collect();
        let also = sites[1..].to_vec();
        let n = refused.len();
        let whose = match what.operator() {
            Some(_) => "operands",
            None => "arguments",
        };
        let head = format!("{n} {whose} of {what} are literals at carriers they cannot take");
        let (m, steps) = grouped(head, refused);
        // Each literal's step, then its derivation, with no step written twice and none that
        // only shows the literal again; the application's notes after them all.
        let mut shown: HashSet<Note> = notes.iter().cloned().collect();
        let mut all = Vec::with_capacity(steps.len() + notes.len());
        for (site, step) in sites.into_iter().zip(steps) {
            all.push(step);
            if !applied {
                for n in self.derive(&[site]) {
                    if n.span != site && shown.insert(n.clone()) {
                        all.push(n);
                    }
                }
            }
        }
        all.extend(notes);
        self.reject(Some(row), at, m, all);
        if let Some(e) = self.errors.last_mut() {
            e.also = also;
        }
    }

    /// The rejection of `what` applied to `args` where the argument `a`, a call or an `if`
    /// whose listed values are read at a carrier ([`Ck::readable`]), may give the value `v`
    /// that is not read at the carrier `c` ([`read_at`]): an integer no value of `c` equals,
    /// or a decimal at `rat`. The carrier is that of `a`'s parameter, or, where `shared`
    /// holds, that of the other arguments at the same type variable, as the other operand of
    /// `x * g(c)`. Short, as sec:diagnostics asks. An integer gets the headline of an integer
    /// literal no value of `c` equals, "No `f64` equals 9007199254740993, which `gb(b, x)`
    /// may give.", as `g(b, x) + 9007199254740993` does, with no repair: none rewrites the
    /// call, and no cast of `v` to `c` is exact. A decimal gets two repairs, neither a cast.
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
        // A call is shown as written; an `if` is named, since its text, often long, is the
        // span the message stands at.
        let call = match (a.expr, self.t.text) {
            (Some(e), _) if matches!(exported(e).kind, ExprKind::If { .. }) => {
                "the `if`".to_string()
            }
            (Some(e), Some(t)) => format!("`{}`", &t[e.span.start..e.span.end]),
            _ => "the call".to_string(),
        };
        let change = match shared {
            false => format!("give this parameter of {what}"),
            true => format!("give the other arguments of {what}"),
        };
        let why = match v {
            Value::Float(_) => format!(
                ": {call} may give the decimal {v}, an `f64` where it is written, and no \
                 `f64` is read as a `rat`. Write {v}r where it is written, or {change} the \
                 type `f64`"
            ),
            // Complexity tradeoff (NUM-no-panic-built): an integer beyond 64 bits is named as
            // its type names it ([`Rat::integer_text`]), its digits or, where shorter, its
            // powers, decided from the exponents in O(the text). Naively writing its digits
            // cost O(n log^2 n) in the value's bits n, 95,425 digits for `3^200000`, and
            // stopped zedc on `2^2^100`, whose digits no memory holds.
            Value::Big(n) => {
                let n = n.integer_text();
                return format!("No `{c}` equals {n}, which {call} may give");
            }
            _ => return format!("No `{c}` equals {v}, which {call} may give"),
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
        let errors = self.errors.len();
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
            let mut called: Vec<&Arg> = Vec::new();
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
                // [`Self::readable`] before [`lists_a_number`], as in [`Self::read_arg`].
                if values_alone(&a.ty) && self.readable(a) && lists_a_number(&a.ty) {
                    valued = true;
                    // The part it holds whole, the `f64` of `1 | f64`, is the carrier it
                    // brings, so that `add(g(c, x), g(c, x))` is read at `f64` as
                    // `g(c, x) + g(c, x)` is ([`Ck::fewest`]).
                    for c in whole_carriers(&a.ty) {
                        carriers |= c.bit();
                    }
                    called.push(a);
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
            // A call or an `if` that lists values, `x * g(c)` with `x: f64` and `g` of type `(bool)
            // -> 1 | 2`, is read at the one carrier, `f64`, `f32` or `rat`, of the other arguments and
            // of the parts the calls hold whole, as at a parameter of that carrier ([`read_ty`]; L1.26a: "each keeps its own value
            // and is fixed where the result is used"). Elsewhere its values are their own
            // carriers, as before: `g(c) * g(c)` is an `int`. Each call is read once, O(v log v)
            // in the values its type lists ([`read_at`]).
            let one = match Carrier::of_mask(carriers).collect::<Vec<_>>()[..] {
                [c @ (Carrier::F64 | Carrier::F32 | Carrier::Rat)] if classes.is_empty() => Some(c),
                _ => None,
            };
            for a in called {
                match one.and_then(|c| Some((c, self.read_adopting(a, c)?))) {
                    Some((c, Ok((_, ads)))) => {
                        for (s, v) in ads {
                            self.put(Undo::Adopt(s, Some(v)));
                        }
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
                (n, _) if n > 1 => {
                    return match self.shown_whole(sig, args) {
                        Some(whole) => Err(self.rejected(what, &whole)),
                        None => fail(self),
                    };
                }
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
                    // first decimal literal, or else the first literal, is rejected, unless they are
                    // float formats alone, `f64` among them, which take `f64` ([`floats_take_f64`]).
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
                                // Float formats alone, `f64` among them, take `f64`.
                                [c, ..] if floats_take_f64(&takes) => c,
                                [c, ..] => {
                                    let l = (lits.iter())
                                        .find(|l| is_decimal(&l.value))
                                        .unwrap_or(&lits[0]);
                                    let notes = self.derive(&[l.site]);
                                    let m = unfixed(l, &takes);
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
                true => match self.generic_parts(a, what, span) {
                    Ok(t) => t,
                    Err(()) => return fail(self),
                },
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
                    (None, None) => {
                        // Into the parameter's own class, where a rejection starts the merges it
                        // lists ([`Ck::came_from`]).
                        let own = p.as_var().and_then(|v| class_id(v)).unwrap_or(k);
                        self.flow(own, &a.ty, what, span, a.at.unwrap_or(span))
                    }
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
                Ok(None) => match self.read_arg(a, p) {
                    Some(Ok((t, c, ads))) => {
                        for (s, v) in ads {
                            self.put(Undo::Adopt(s, Some(v)));
                        }
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
                    // A call of values whose numbers the parameter would read at its carrier
                    // but for a value that is no number, as `h(gi(true))` with `h` taking an
                    // `f64` and `gi(true)` of type `1 | true` ([`read_call`]): the message
                    // names the value that is no number and that the parameter does not
                    // take, `true`, not the `1` it would read.
                    let piece = match piece.carrier() {
                        Some(c) if c.numeric() && call_values(a).is_some() => {
                            (ty.pieces().into_iter())
                                .find(|q| {
                                    !q.carrier().is_some_and(Carrier::numeric)
                                        && self.class_of(q).is_none()
                                        && !matches!(q, Piece::Dyn | Piece::Var(_))
                                        && !self.sub(&ty.of_piece(q), p, &mut Binds::new())
                                })
                                .unwrap_or(piece)
                        }
                        _ => piece,
                    };
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
        // The arguments of this call, for a repair of a need of a function it passes to name
        // the argument it passes on, as `-1` of `ap(h, -1)` (MSG-forwarded-repair). A call of
        // no needs has none to name.
        let forwarded = (arrow.params.iter().zip(args))
            .take(if sig.needs.is_empty() { 0 } else { args.len() })
            .map(|(_, a)| {
                a.as_ref().and_then(|a| {
                    Some(Forwarded {
                        call: span,
                        at: a.at?,
                        expr: a.expr,
                    })
                })
            })
            .collect();
        let names = sig.params.iter().map(|p| p.name.clone()).collect();
        self.call_frames
            .push(CallFrame::new(&arrow.params, forwarded, names));
        let mut left = self.replay(what, &sig.needs, &mut binds, defer, span);
        let frame = self.call_frames.pop();
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
        // as they are. Complexity tradeoff (COMPLEXITY.md F170): naive, a second walk over the
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
                && !self.flow(c, &rest, what, span, span)
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
                    self.call_frames.extend(frame);
                    self.replay(what, &now, &mut binds, BTreeSet::new(), span);
                    self.call_frames.pop();
                    left.clear();
                    held
                }
            });
        }
        out = out.union(&self.pass_needs(what, &arrow.params, args, passing, span)?);
        // A call this application already rejected, as `g((1.5, 2))` where the body needs an
        // `int` of `p[0]`, gets no rejection of its unfixed literals: the error stands with
        // every carrier of the literal, so each fix would be rejected, and the call has one
        // error, as `g(1.5)` has.
        if self.level == 0 && self.replaying == 0 && !self.trying && self.errors.len() == errors {
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
            Parts(&'p [Part<'e>], Option<&'e Expr>),
            Other(Option<&'e Expr>),
        }
        // The component `i` of the tuple display `e`, where it is one.
        fn item(e: Option<&Expr>, i: usize) -> Option<&Expr> {
            match e.map(|e| &e.kind) {
                Some(ExprKind::Tuple(items)) => items.get(i),
                _ => None,
            }
        }
        fn of<'p, 'e>(part: &'p Part<'e>, e: Option<&'e Expr>) -> Src<'p, 'e> {
            match part {
                Part::Lit(l) => Src::Lit(l),
                Part::Tuple(ps) => Src::Parts(ps, e),
                Part::Branches(_) | Part::Other => Src::Other(e),
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
                    && is_decimal(&l.value)
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
                                            Part::Lit(_) | Part::Branches(_) => {}
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
                        Src::Lit(l) if is_decimal(&l.value) => lits.push((v, place, l)),
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
        // The literals of tuple arguments whose classes ([`Self::generic_parts`]) a use in the
        // body asked for one carrier of a decimal as the call was replayed
        // ([`Self::gives_within`]): `p[0] + 1r` makes the `1.5` of `h((1.5, 2))` a rat, as it
        // makes the `1.5` of `h(1.5)` one, and [`Self::resolve_top_parts`] gives it that
        // carrier.
        // Complexity tradeoff (COMPLEXITY.md row F189): naive version, a scan of the classes
        // for each unfixed literal, O(l c) for l literals and c classes, or a read of each
        // entry of `top_parts`, O(c l) once classes merge. Used: each class read once, by its
        // root, into a set of spans each literal looks up once, O(c + l). Tradeoff: one set
        // per application outside every function, empty where it has no literal component.
        // The float formats alone, `f64` among them, count as one: they take `f64`
        // ([`floats_take_f64`]), so `p[0] ^ 2.0` makes the `1.5` an `f64`, as `p ^ 2.0` makes
        // the `1.5` of `h(1.5)` one.
        let floats = Carrier::F64.bit() | Carrier::F32.bit();
        let decimal = floats | Carrier::Rat.bit();
        let roots: HashSet<usize> = self.top_parts.iter().map(|&k| self.find(k)).collect();
        let fixed: HashSet<Span> = (roots.into_iter())
            .map(|r| &self.classes[r])
            .filter(|c| {
                let m = c.mask & decimal;
                c.asked && (m.count_ones() == 1 || m == floats)
            })
            .flat_map(|c| c.lits.iter().map(|(l, _)| l.span))
            .collect();
        let mut found: Vec<(Span, Msg)> = Vec::new();
        for (v, from, l) in lits {
            let r = sets.find(v);
            if sets.fixed_for(r, from) || self.is_class(&sets.names[v]) || fixed.contains(&l.span) {
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
            found.push((l.site, unfixed(l, &cs)));
        }
        for l in &payloads {
            let cs: Vec<Carrier> = [Carrier::F64, Carrier::Rat]
                .into_iter()
                .filter(|&c| fits(l, c))
                .collect();
            found.push((l.site, unfixed(l, &cs)));
        }
        found.sort_by_key(|(s, _)| s.start);
        self.reject_unfixed(&format_args!("the arguments of {what}"), found);
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
                        && !self.join(k, l, l.exponent)
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
            // An integer exponent of `^` keeps the arrows whose exponent it fits exactly
            // ([`Lit::exponent`]), and stands for itself, not for the class.
            let exponent =
                (a.as_ref().and_then(|a| a.lit.as_ref())).filter(|l| l.exponent && class.is_some());
            let pieces: Vec<Option<Piece>> = match a {
                None => vec![None],
                // An argument of no value keeps every arrow; an argument of type `Never` the
                // call does not need is one of them.
                Some(_) if no_value[i] => vec![None],
                Some(a)
                    if (a.lit.is_some() || a.branches.is_some())
                        && class.is_some()
                        && exponent.is_none() =>
                {
                    vec![Some(Piece::Var(format!("${}", class.unwrap()).into()))]
                }
                Some(a) => a.ty.pieces().into_iter().map(Some).collect(),
            };
            let mut next: Vec<State> = Vec::new();
            for (alive, dyn_, at, path) in &states {
                for p in &pieces {
                    let mut at = at.clone();
                    let (alive, dyn_) = match p {
                        _ if let Some(l) = exponent => {
                            let alive = (alive.iter().copied())
                                .filter(|&j| {
                                    (sig.arrows[j].params[i].numeric_carrier())
                                        .is_some_and(|c| fits(l, c))
                                })
                                .collect();
                            (alive, *dyn_)
                        }
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
                // Two carriers held whole beside a read argument: the message shows the
                // carriers ([`Self::shown_whole`]).
                if let Some(whole) = ck.shown_whole(sig, args) {
                    return ck.rejected(what, &whole);
                }
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
            format!("`sum` does not take ({shown}): it adds only numbers"),
            [
                "repair: pass a tuple whose components are all numbers, as `sum((1, 2, 3))`"
                    .to_string(),
            ],
        );
    }

    /// `sum` of a tuple: its components added in turn, `0` for the empty tuple; atoms pass.
    fn sum(&mut self, x: Arg<'a>, span: Span) -> Ty {
        let t = &x.ty;
        let mut out = self.passing(t, "`sum`", span, x.at);
        let add = op_sig(Operator::Binary(BinaryOp::Add));
        for p in t.pieces() {
            match p {
                Piece::Tuple(cs) => {
                    // A component that holds a value of no number is the tuple's fault, not
                    // that of one `+`, so the message names the tuple. A component of `_`,
                    // whose values the checker does not track, is left to `+`, which decides
                    // it as it decides `x.a + 1`: `sum` takes what a chain of `+` takes.
                    let not_number = |p: &Piece| {
                        !matches!(p, Piece::Var(_) | Piece::Dyn)
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
                    // shows them. A component of a tuple written here, as in `sum((a, b))`,
                    // is an operand as written, with its own derivation.
                    let mut args = components(&x, cs.len())
                        .unwrap_or_else(|| cs.iter().cloned().map(Arg::of).collect());
                    if let Some(ExprKind::Tuple(es)) = x.expr.map(|e| &e.kind)
                        && es.len() == args.len()
                    {
                        for (a, e) in args.iter_mut().zip(es) {
                            (a.at, a.expr) = (Some(e.span), Some(e));
                        }
                    }
                    let mut args: Vec<(usize, Arg)> = args.into_iter().enumerate().collect();
                    args.sort_by_key(|(_, a)| a.lit.is_some());
                    let mut args = args.into_iter();
                    let Some((mut at, mut acc)) = args.next() else {
                        out = out.union(&Ty::lit(&Value::Int(0)));
                        continue;
                    };
                    // Each `+` is reported where its operands are written, from the first to
                    // the last of the components it adds, as a written `+` is from its left
                    // operand to its right one; at the call when the tuple is not written.
                    let mut written = acc.at;
                    for (i, c) in args {
                        let site = written.zip(c.at).map(|(a, b)| Span {
                            start: a.start.min(b.start),
                            end: a.end.max(b.end),
                        });
                        let pair = if i < at { [c, acc] } else { [acc, c] };
                        let ty = self
                            .apply(
                                Label::SumPlus(span),
                                &add,
                                pair.map(Some).to_vec(),
                                true,
                                site.unwrap_or(span),
                            )
                            .0;
                        (at, acc, written) = (at.min(i), Arg::of(ty), site);
                    }
                    // The sum is a number: each `+` gives a number, a class or the atoms that
                    // pass, and a `+` that fails reports its own error and gives only the atoms.
                    out = out.union(&acc.ty);
                }
                Piece::Dyn => self.any("`sum`", span),
                // A class takes the use as a need, checked on each value that flows into it
                // and at each call of a generic function (CHK-need-bound).
                Piece::Var(v) => {
                    let r = self.class_root(&v);
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

/// A repair of an int `^`: the rewritten code, and the words that follow it, or none.
type Repair = (String, String);

/// The note of the repair `r`, as "repair: `b: f64`, and pass a float as `b` at each call".
fn repair_note((code, tail): &Repair) -> String {
    format!("repair: `{code}`{tail}")
}

/// The headline of an int `^` whose exponent is not shown to be at least 0: the power's code,
/// each part annotated with its type, as `2 : int ^ k : -1`, then the first repair, if there
/// is one, as "Try `2.0f64^-1` instead.". Each part is its code, if the checker has it, and
/// its type as shown; a literal whose type shows as the literal itself is annotated `int`.
/// `negative` says that every value of the exponent is below 0.
fn power_message(
    base: (Option<&str>, &str),
    exponent: (Option<&str>, &str),
    negative: bool,
    first: Option<&Repair>,
) -> String {
    let part = |(code, ty): (Option<&str>, &str)| match code {
        Some(c) if c == ty => format!("{c} : int"),
        Some(c) => format!("{c} : {ty}"),
        None => format!("… : {ty}"),
    };
    let what = match negative {
        true => "a negative exponent",
        false => "an exponent that may be negative",
    };
    let try_ = match first {
        Some((code, tail)) => format!(" Try `{code}` instead{tail}."),
        None => String::new(),
    };
    format!(
        "Int power with {what}: `{} ^ {}`.{try_}",
        part(base),
        part(exponent)
    )
}

/// Whether `s` is an integer literal in decimal digits, as `2` or `1_000`, which a float
/// literal of the same value writes with `.0` after it.
fn int_literal(s: &str) -> bool {
    s.bytes().next().is_some_and(|b| b.is_ascii_digit())
        && s.bytes().all(|b| b.is_ascii_digit() || b == b'_')
}

/// The code `s` without the parentheses around the whole of it, if it has them, as `n - 5`
/// for `(n - 5)`; `(a) + (b)` is kept. One pass over `s`.
fn unparen(s: &str) -> &str {
    let Some(inner) = s.strip_prefix('(').and_then(|s| s.strip_suffix(')')) else {
        return s;
    };
    let mut depth = 0usize;
    for b in inner.bytes() {
        match b {
            b'(' => depth += 1,
            b')' if depth == 0 => return s,
            b')' => depth -= 1,
            _ => {}
        }
    }
    inner
}

/// The words that name a callee written as an expression when its code cannot be shown: the
/// checker has no text, or the code runs over more than one line.
const CALLED_HERE: &str = "the function called here";

/// The callee of a call as a message names it: its name or code in code quotes, and the
/// words [`CALLED_HERE`] as they are.
fn callee(what: &str) -> String {
    match what == CALLED_HERE {
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
fn outside(d: &IntDomain, span: Span) -> Note {
    let text = format!(
        "a value outside {} would reach a use that does not take it",
        domain_text(d)
    );
    Note { span, text }
}

/// A call's code as written, and its code before and after one argument.
type Call<'s> = (&'s str, &'s str, &'s str);

/// The ints a test keeps an argument within, as a message writes them and as the program's code
/// tests them: a comparison, never a refinement such as `is int[0..<2^8]`, which this zedc does
/// not compile.
#[derive(Clone)]
enum Within {
    /// The ints from `low`, and below `below` where it is given: `int[0..<2^8]`, tested as
    /// `n >= 0 && n < 2^8`, or `int[3..]`, tested as `n >= 3`.
    Range { low: i64, below: Option<Bound> },
    /// The multiples of 8 a width of `byteSwap` takes, tested one by one, as
    /// `w == 16 || w == 32 || w == 64`: the checker reads a multiple of 8 from listed values
    /// only, and Zed has no remainder operator to test it with. In increasing order, never
    /// empty.
    Bytes(Vec<i64>),
}

/// The end of a [`Within::Range`] that no int it holds reaches, at the width `w`, or at the
/// width written `width` where the call's width is not one known value: such a range is
/// written, never tested, and holds no value the checker could show to lie in it.
#[derive(Clone)]
enum Bound {
    /// `2 ^ w`, for an operand read as `w` binary digits.
    TwoPow(Option<Value>),
    /// `w` itself, for the `k` of a funnel shift of width `w`.
    Width(Option<Value>),
}

impl std::fmt::Display for Bound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Bound::TwoPow(Some(w)) => write!(f, "2^{w}"),
            Bound::TwoPow(None) => write!(f, "2^width"),
            Bound::Width(Some(w)) => write!(f, "{w}"),
            Bound::Width(None) => write!(f, "width"),
        }
    }
}

impl Within {
    /// The ints of the domain `d`, as its test keeps them.
    fn of(d: &IntDomain) -> Within {
        Within::Range {
            low: 0,
            below: (d.below_two_pow.as_ref()).map(|w| Bound::TwoPow(Some(w.0.clone()))),
        }
    }

    /// The widths of the operation `p` from `least`, the least width that holds its other
    /// operands ([`least_width`]): for `byteSwap`, each of 8, 16, 32 and 64 from `least`, or
    /// else the multiple of 8 next from it.
    fn width(p: Prim, least: i64) -> Within {
        if !zed_kernel::bits::whole_bytes(p) {
            return Within::Range {
                low: least,
                below: None,
            };
        }
        let listed: Vec<i64> = [8, 16, 32, 64]
            .into_iter()
            .filter(|&b| b >= least)
            .collect();
        match listed.is_empty() {
            true => Within::Bytes(vec![(least + 7) / 8 * 8]),
            false => Within::Bytes(listed),
        }
    }

    /// The least int it holds: the width a literal width is rewritten as.
    fn least(&self) -> i64 {
        match self {
            Within::Range { low, .. } => *low,
            Within::Bytes(vs) => vs[0],
        }
    }

    /// Whether it holds the int `v`.
    fn holds(&self, v: &Value) -> bool {
        let ge = |b: i64| (v.surface_cmp(&Value::Int(b))).is_some_and(|o| o.is_ge());
        match self {
            Within::Range { low, below } => {
                ge(*low)
                    && match below {
                        None => true,
                        Some(Bound::TwoPow(Some(w))) => zed_kernel::bits::below_two_pow(v, w),
                        Some(Bound::Width(Some(w))) => v.surface_cmp(w).is_some_and(|o| o.is_lt()),
                        Some(Bound::TwoPow(None) | Bound::Width(None)) => false,
                    }
            }
            Within::Bytes(vs) => vs
                .iter()
                .any(|&b| v.surface_cmp(&Value::Int(b)).is_some_and(|o| o.is_eq())),
        }
    }

    /// Whether it holds none of the ints of `r`, so that a test of the operand leaves nothing
    /// to pass. A range holds none of an interval when the least int of the interval from its
    /// `low` is not below its bound: one search of the pieces, O(log p) for p pieces, against
    /// O(p) for testing each piece; listed values are each tested once, O(v), and the 4 widths
    /// of `byteSwap` each searched for, O(log p).
    fn holds_none_of(&self, r: &IntRange) -> bool {
        if let Some(vs) = &r.values {
            return !vs.iter().any(|v| self.holds(v));
        }
        match self {
            Within::Range { low, .. } => {
                let from = End::of(*low);
                match r.ints.piece_at_or_above(&from) {
                    None => true,
                    Some((Fin(a), _)) if *a > Num::from(*low) => !self.holds(&Value::from(a)),
                    Some(_) => !self.holds(&Value::Int(*low)),
                }
            }
            Within::Bytes(vs) => !vs.iter().any(|&b| r.ints.contains(b)),
        }
    }

    /// The ints as a message writes them after "takes `x`", as "in int[0..<2^8]" or "a
    /// multiple of 8 in int[0..]": the bound 0 written, so that a negative multiple of 8 does not
    /// seem to be in it.
    fn takes(&self) -> String {
        match self {
            Within::Range { low, below: None } => format!("in int[{low}..]"),
            Within::Range {
                low,
                below: Some(b),
            } => format!("in int[{low}..<{b}]"),
            Within::Bytes(_) => "a multiple of 8 in int[0..]".into(),
        }
    }

    /// A value in the ints, as a repair writes it after "pass": "a value in int[0..]", or "a
    /// multiple of 8 in int[0..], as 8, 16, 32 or 64".
    fn value(&self) -> String {
        match self {
            Within::Range { .. } => format!("a value {}", self.takes()),
            Within::Bytes(vs) => {
                let vs: Vec<String> = vs.iter().map(i64::to_string).collect();
                format!("{}, as {}", self.takes(), or_list(&vs))
            }
        }
    }

    /// The test of the name `a` that holds it within the ints inside its branch.
    fn test(&self, a: &str) -> String {
        match self {
            Within::Range { low, below: None } => format!("{a} >= {low}"),
            Within::Range {
                low,
                below: Some(b),
            } => format!("{a} >= {low} && {a} < {b}"),
            Within::Bytes(vs) => (vs.iter().map(|v| format!("{a} == {v}")))
                .collect::<Vec<_>>()
                .join(" || "),
        }
    }
}

/// The least width of the operation `p` that holds its operands other than the width: the
/// most binary digits of an operand read as `width` digits, and one more than the largest `k`
/// of a funnel shift; none where one of them is of a type variable or has no largest value.
/// One pass over the operands.
fn least_width(p: Prim, slots: &[(Arg<'_>, &Expr)], ranges: &[Option<IntRange>]) -> Option<i64> {
    let largest = |i: usize| -> Option<Value> {
        match slots[i].0.ty.vars.is_empty() {
            true => ranges[i].as_ref()?.extreme(std::cmp::Ordering::Greater),
            false => None,
        }
    };
    let positive = |v: &Value| v.surface_cmp(&Value::Int(0)).is_some_and(|o| o.is_gt());
    let mut least = 0i64;
    for &i in zed_kernel::bits::below_two_pow_width(p) {
        let h = largest(i)?;
        if positive(&h) {
            let bits = h.as_integer()?.to_integer().ok()?.bits();
            least = least.max(i64::try_from(bits).ok()?);
        }
    }
    if let Some(i) = zed_kernel::bits::below_width(p) {
        let h = largest(i)?;
        if h.surface_cmp(&Value::Int(0)).is_some_and(|o| o.is_ge()) {
            let Value::Int(k) = h else { return None };
            least = least.max(k.checked_add(1)?);
        }
    }
    Some(least)
}

/// The texts `vs` joined as "8, 16, 32 or 64".
fn or_list(vs: &[String]) -> String {
    match vs {
        [] => String::new(),
        [one] => one.clone(),
        [rest @ .., last] => format!("{} or {last}", rest.join(", ")),
    }
}

/// The repairs of an argument `p` that may lie outside the ints `within` its use needs, each in
/// the program's code: `arg` is the argument's code, with whether it is a name a test narrows
/// ([`Ck::tested`]), and `outside_all` says that no value of it lies in `within`, so that a test
/// of it leaves nothing to pass. A name a test does not narrow, or an expression, is first bound
/// to a new name ([`test_repair`]). `call` is the call's code, which the test then holds in
/// full. `given` is the argument of the call that a function's parameter `p` takes the value
/// from, where the call passes it on (MSG-forwarded-repair). Gives the test, the repair a
/// headline shows, if there is one, and the notes of every repair.
fn passed_repairs(
    p: &str,
    within: &Within,
    arg: Option<(&str, bool)>,
    call: Option<Call<'_>>,
    outside_all: bool,
    given: Option<&str>,
    span: Span,
) -> (Option<Repair>, Vec<Note>) {
    let value = within.value();
    let test = (!outside_all)
        .then(|| arg.map(|a| test_repair(p, &|a| within.test(a), a, call)))
        .flatten();
    let pass = match given {
        Some(code) => format!("repair: pass {value} where this call passes `{code}`"),
        None => format!("repair: pass as `{p}` {value}"),
    };
    let notes = (test.iter().map(repair_note))
        .chain([pass])
        .map(|text| Note { span, text })
        .collect();
    (test, notes)
}

/// The test of the argument `a` of `p` that keeps it in what `test` tests of a name inside its
/// branch, in the program's code: of `a` itself where it is a name a test narrows (the flag),
/// else of a new name bound to it, `p` or `p` with a number ([`fresh`]); holding `call` with
/// `a`, or the new name, in place, where the call is known.
fn test_repair(
    p: &str,
    test: &dyn Fn(&str) -> String,
    (a, narrows): (&str, bool),
    call: Option<Call<'_>>,
) -> Repair {
    if narrows {
        return match call {
            Some((call, ..)) => (
                format!("if {} {{ {call} }} else {{ … }}", test(a)),
                String::new(),
            ),
            None => (
                format!("if {} {{ … }} else {{ … }}", test(a)),
                format!(", with `{a}` passed as `{p}` inside the branch"),
            ),
        };
    }
    let q = fresh(p, &[a, call.map_or("", |(c, ..)| c)]);
    let bound = format!("{q} = {}; if {}", unparen(a), test(&q));
    match call {
        Some((_, before, after)) => (
            format!("{bound} {{ {before}{q}{after} }} else {{ … }}"),
            String::new(),
        ),
        None => (
            format!("{bound} {{ … }} else {{ … }}"),
            format!(", with `{q}` passed inside the branch"),
        ),
    }
}

/// `p`, or `p` followed by the least number from 2 that makes a name no word of `texts`
/// spells, as `n2` for `n = n - 1`, which would define `n` in terms of itself: a name bound
/// to the argument then neither reads itself nor shadows a name the call reads.
///
/// Complexity tradeoff: testing each number against the texts afresh costs their length per
/// number tried, O(L·k); one pass collecting their words, then one hash lookup per number,
/// costs O(L + k), and k is at most one more than the number of words.
fn fresh(p: &str, texts: &[&str]) -> String {
    let words: HashSet<&str> = (texts.iter())
        .flat_map(|t| t.split(|c: char| !(c.is_alphanumeric() || c == '_')))
        .collect();
    if !words.contains(p) {
        return p.to_string();
    }
    (2..)
        .map(|k| format!("{p}{k}"))
        .find(|q| !words.contains(q.as_str()))
        .expect("a number past the words of the texts")
}

/// The headline of a use that takes the ints of a domain, `takes` as "`popCount` takes `x` in
/// int[0..]", at the code `piece` annotated with its type, as `popCount(n : int)`, then the
/// first repair, if there is one, as "Try `if n >= 0 { popCount(n) } else { … }` instead.".
fn domain_message(takes: &str, piece: &str, first: Option<&Repair>) -> String {
    match first {
        Some((code, tail)) => format!("{takes}: `{piece}`. Try `{code}` instead{tail}."),
        None => format!("{takes}: `{piece}`."),
    }
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

/// The operand of a word as [`Ck::word_atoms`] reads it ([`Ck::operand_values`]).
enum WordOperand {
    /// A literal's values, at most three, and the literal as written.
    Values(Vec<Value>, Option<String>),
    /// A type without its atoms, whose values are not listed yet.
    Type(Ty),
}

impl WordOperand {
    /// The operand's values, if the checker can list them, and the literal as written.
    // Complexity tradeoff: the values of a type are listed here, after the word's result is
    // known to hold an atom, not where the operand is read. Listed there, each call of a word
    // that gives no atom, such as `String` and its repair trials, listed its operand for
    // nothing: for `x + (0.50r, ..., (n-1).50r)` with `x: String`, the trial `String((...))`
    // listed the one value of the tuple, 47 M of the checker's 127 M instructions at n = 400
    // (PERF-tuple-print). Listing costs O(L) per value of length L (COMPLEXITY.md K116);
    // deferred, it costs nothing for a word that gives no atom, and the same for one that
    // does. The operand's type is kept without its atoms either way, O(size of the type).
    fn listed(self) -> Option<(Vec<Value>, Option<String>)> {
        match self {
            WordOperand::Values(values, written) => Some((values, written)),
            WordOperand::Type(t) => Some((t.kernel()?.values_listed()?, None)),
        }
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
    fn zero_divisor(
        &mut self,
        op: BinaryOp,
        x: &Arg<'a>,
        y: &Arg<'a>,
        b: &'a Expr,
    ) -> Option<Zero> {
        if x.ty.lists_nothing() || y.ty.lists_nothing() {
            return None;
        }
        let f64 = Ty::carrier(Carrier::F64);
        if op == BinaryOp::Div && (x.ty.meets(&f64) || y.ty.meets(&f64)) {
            return None;
        }
        let unsigned = match &b.kind {
            ExprKind::Unary(UnaryOp::Neg, a) => a,
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
                ExprKind::Binary(o @ (BinaryOp::Add | BinaryOp::Sub), a, b) => {
                    stack.push((b, neg ^ (*o == BinaryOp::Sub)));
                    stack.push((a, neg));
                }
                ExprKind::Unary(UnaryOp::Neg, a) => stack.push((a, !neg)),
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
    fn divides_by_zero(
        &mut self,
        op: BinaryOp,
        why: Zero,
        dividend: &str,
        b: &'a Expr,
        span: Span,
    ) {
        let (result, kind) = match op {
            BinaryOp::Div => ("a rat", "rat"),
            BinaryOp::IntDiv | BinaryOp::Mod => ("an int", "int"),
            BinaryOp::Or
            | BinaryOp::And
            | BinaryOp::Eq
            | BinaryOp::Ne
            | BinaryOp::Lt
            | BinaryOp::Le
            | BinaryOp::Gt
            | BinaryOp::Ge
            | BinaryOp::Add
            | BinaryOp::Sub
            | BinaryOp::Concat
            | BinaryOp::Mul
            | BinaryOp::Pow => unreachable!("only a division has a divisor"),
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

    /// The operand `x` of a word as [`Self::word_atoms`] reads it, when the checker can list its
    /// values: a literal, in each carrier a bare integer literal may adopt, with the literal as
    /// written, or a type that may list its values one by one (`"a" | "b"`), listed only if
    /// the word may give an atom ([`WordOperand::listed`]). A bare decimal literal is left out: it
    /// is rejected as a literal with no carrier. Linear in the size of the type.
    fn operand_values(&self, x: &Arg<'a>) -> Option<WordOperand> {
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
            return Some(WordOperand::Values(values, Some(l.written().to_string())));
        }
        let value = x.ty.without_atoms();
        if value.lists_nothing() {
            return None;
        }
        Some(WordOperand::Type(value))
    }

    /// The result `r` of the word `w` applied at `span` to an operand at `at` whose values are
    /// `values`, `written` when it is a literal, and which carries the atoms `carried`, with each
    /// atom of the word that no value gives taken out (DESIGN.md sec:failure: an atom-making
    /// operation is typed from the inputs that reach it, a literal's domain being the singleton
    /// of its value). When every value the word takes fails, the call is rejected and `r` kept,
    /// so that nothing after it fails again. A value the kernel cannot convert for want of
    /// memory leaves `r` as it is.
    ///
    /// Complexity tradeoff: the naive method types the call from the word's signature alone, in
    /// O(1), and so lists `#inexact` and `#overflow` for `f64(3r)`, which never gives either
    /// (item CAST-literal-exact). The method used runs the cast on each listed value, at most 3
    /// for a literal (a bare integer as int, f64 and rat), and O(V) casts for V listed values.
    /// Each costs what the cast costs when the program runs: O(d^1.47) for a literal of d digits
    /// (COMPLEXITY.md K41), and no cheaper test decides whether a long digit string is exact in
    /// the target format. A `rat` written with an exponent, `1e400000r`, holds its powers of 2
    /// and 5 as exponents, and the kernel decides both atoms from them without building the
    /// power (`beyond_float` compares magnitudes by bounds, `exact_f64` tests the dyadic shape
    /// first), so its cast does not grow with the exponent. COMPLEXITY.md row C39.
    fn word_atoms(
        &mut self,
        w: &str,
        operand: WordOperand,
        r: Ty,
        carried: &KType,
        at: Span,
        span: Span,
    ) -> Ty {
        if r.atoms().is_empty() {
            return r;
        }
        let Some(p) = zedc_base::interp::prim(w) else {
            return r;
        };
        let Some((values, written)) = operand.listed() else {
            return r;
        };
        let sig = word_sig(w);
        let mut fails = Vec::new();
        let mut converts = false;
        for v in values {
            if !sig.arrows.iter().any(|a| a.params[0].contains(&v)) {
                continue;
            }
            match run(p, &v) {
                Some(a @ Value::Atom(_)) => fails.push((v, a)),
                Some(_) => converts = true,
                None => return r,
            }
        }
        if converts {
            // Union of the atoms the values gave, each in O(1); an atom with no kernel type
            // leaves the result as it is.
            let mut given = carried.clone();
            for (_, a) in &fails {
                let Some(t) = KType::lit(a) else {
                    return r;
                };
                given = &given | &t;
            }
            let unused = &r.atoms() - &given;
            return r.without(&unused);
        }
        let Some((first, _)) = fails.first() else {
            return r;
        };
        let carrier = match first {
            Value::Str(_) => "String".to_string(),
            v => lit_carrier(v).name().to_string(),
        };
        // In the order of a union (`order::cmp`, DESIGN.md sec:diagnostics), each once.
        let mut atoms: Vec<&Value> = fails.iter().map(|(_, a)| a).collect();
        atoms.sort_by(|a, b| zed_kernel::types::order::cmp_values(a, b));
        atoms.dedup();
        let atoms = atoms.iter().map(|a| a.to_string()).collect::<Vec<_>>();
        let atoms = atoms.join(" | ");
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
        r
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

// Operands::adoptions, Ck::generic_parts, Ck::fewest and parts are here, not in mod.rs, since they call
// branch_lits, read_ty and Ck::branch_joins: in mod.rs they would make an import cycle (step S.1f).
impl Operands {
    /// Pairs the operands as `x == e` does, in a checker of the empty unit, and gives the
    /// number of literals that adopt a carrier.
    #[doc(hidden)]
    pub fn adoptions(&self) -> usize {
        let res = zedc_resolve::resolve::resolve(&[]).expect("the empty unit resolves");
        let t = Tables::new(&[], &res);
        let mut ck = Ck::new(&t, Ck::fixes_checked);
        let (lit, parts) = (
            literal(&self.e, None),
            parts(&self.e, None, &HashMap::new()),
        );
        let y = (vec![&self.et], lit.as_ref(), parts.as_deref());
        ck.pair((vec![&self.x], None, None), y);
        ck.info.adopt.len()
    }
}

impl<'t, 'a> Ck<'t, 'a> {
    /// The type of the tuple argument `a` at a parameter that is a type variable, with each
    /// literal without a suffix written as a component of it, at any depth, made a class of
    /// its own that the literal joins, generic (L1.26a): the component joins the class of what
    /// it meets in
    /// the function's body, and takes int where it meets no carrier. Outside every function
    /// the class is one of the application's, and takes its type when the application ends
    /// ([`Self::resolve_top_parts`]): the `2` in `y = f(x: 1r, p: (2, 1))`, with
    /// `f(x, p) = x + p[0]`, is a `rat`. `None` where no such literal is written.
    ///
    /// The tuples nest as deep as the text, so the walk keeps its own stack, as [`adopted`]
    /// does; it costs the size of the tuple's text.
    ///
    /// An `if` of literals written as a component, `(x, if c { 2 + 1 } else { 1 })`, is made a
    /// class of its own in the same way, which each branch joins as the branches of an
    /// argument join the class of a parameter ([`Ck::branch_joins`]). `Err` where a branch
    /// cannot join it, which `what` at `span` reports.
    fn generic_parts(&mut self, a: &Arg, what: &str, span: Span) -> Result<Option<Ty>, ()> {
        let Some(parts) = (a.parts.as_deref()).filter(|_| self.replaying == 0) else {
            return Ok(None);
        };
        let Some(comps) = only_tuple(&a.ty, parts.len()) else {
            return Ok(None);
        };
        let mut stack = vec![OpenTuple {
            parts,
            comps,
            want: Vec::new(),
            out: Vec::new(),
        }];
        let mut made = false;
        loop {
            let open = stack.last_mut().expect("an open tuple");
            let i = open.out.len();
            if i == open.parts.len() {
                let t = Ty::tuple(stack.pop().expect("an open tuple").out);
                match stack.last_mut() {
                    None => return Ok(made.then_some(t)),
                    Some(up) => up.out.push(t),
                }
                continue;
            }
            let c = &open.comps[i];
            match &open.parts[i] {
                Part::Lit(l) if l.bare => {
                    let k = self.generic_class(l);
                    if self.level == 0 {
                        self.top_parts.push(k);
                    }
                    made = true;
                    let open = stack.last_mut().expect("an open tuple");
                    open.out.push(Ty::var(format!("${k}").into()));
                }
                Part::Branches(bs) => {
                    let k = self.class();
                    self.classes[k].generic = true;
                    for b in bs.iter() {
                        if !self.branch_joins(k, b, what, span) {
                            return Err(());
                        }
                    }
                    if self.level == 0 {
                        self.top_parts.push(k);
                    }
                    made = true;
                    let open = stack.last_mut().expect("an open tuple");
                    open.out.push(Ty::var(format!("${k}").into()));
                }
                Part::Tuple(inner) => match only_tuple(c, inner.len()) {
                    Some(cs) => stack.push(OpenTuple {
                        parts: inner,
                        comps: cs,
                        want: Vec::new(),
                        out: Vec::new(),
                    }),
                    None => open.out.push(c.clone()),
                },
                _ => open.out.push(c.clone()),
            }
        }
    }

    /// The first value of an argument of `args` that no arrow of `sig` takes at its place,
    /// with the argument's index: a piece of its type, as `true` of `gi(true)` of type
    /// `1 | true` at `+`, or `None` in place of the piece where no arrow takes any value of
    /// the argument, as `u` of type `int | true` at `/`, whose whole type is then named. A
    /// literal, a tuple or an `if` of literals takes its type from the arrow, and a class, a
    /// variable and the unknown may be any value, so none of them gives one; a parameter that
    /// is a bounded variable takes the numbers of its bound. A value whose check at an arrow
    /// was refused, not decided, may be taken there: a refusal claims nothing about the
    /// types ([`Ty::refused`]), so the application's message gives the refusal's cause
    /// instead (`refused_among`). O(A p) tests for A arrows and p pieces.
    fn taken_by_none(&self, sig: &Sig, args: &[Option<Arg<'a>>]) -> Option<(usize, Option<Piece>)> {
        let may_take = |t: &Ty, q: &Piece, p: &Ty| {
            p.dynamic
                || match p.as_var() {
                    Some(v) => (sig.bounds.get(v))
                        .is_none_or(|&m| q.carrier().is_some_and(|c| c.bit() & m != 0)),
                    None if !p.vars.is_empty() => true,
                    None => {
                        let s = t.of_piece(q);
                        s.sub(p, &mut Binds::new()) || !s.refused(p).is_empty()
                    }
                }
        };
        args.iter().enumerate().find_map(|(i, a)| {
            let a = a
                .as_ref()
                .filter(|a| a.lit.is_none() && a.parts.is_none() && a.branches.is_none())?;
            let none = |q: &Piece| {
                !matches!(q, Piece::Dyn | Piece::Var(_))
                    && self.class_of(q).is_none()
                    && (sig.arrows.iter())
                        .all(|ar| ar.params.get(i).is_some_and(|p| !may_take(&a.ty, q, p)))
            };
            let pieces = a.ty.pieces();
            let q = pieces.iter().find(|q| none(q))?;
            let all = pieces.iter().all(none);
            Some((i, (!all).then(|| q.clone())))
        })
    }

    /// Whether the argument `a` is one whose listed values are read at a carrier where it is
    /// used ([`read_ty`]): a call, as `g(c)`, or an `if` that is no `if` of literals alone
    /// ([`Arg::branches`]) and each branch of which, at any depth, is a call, a literal, an
    /// operation on literals alone, or a value whose type lists no number, as `x: f64` in
    /// `if c { x } else { 1 }`, which is `1 | f64` (sec:type_resolution, rule 3: "the literal
    /// `1` taking its carrier where the result is used"). A name, `y` after `y = g(c)` or `y
    /// = 1`, is not read, alone or as a branch: its value is fixed where it is bound ("bound
    /// to a name alone"), and reading it would convert it.
    // Complexity tradeoff: one visit of each branch, at any depth, of the `if`, with one
    // listing of the type of a branch that is no call, literal or `if`, O(the size of the
    // `if`'s tree of branches and of those types), and a call costs O(1). A nested `if` is
    // visited again only by an argument that holds it whole, so an argument `if` nested d
    // deep costs O(d). The naive form, a lone call alone, rejects
    // `h(if c { x } else { 1 })`, the rule's own example.
    fn readable(&self, a: &Arg) -> bool {
        let Some(e) = a
            .expr
            .filter(|_| a.lit.is_none() && a.branches.is_none() && a.parts.is_none())
        else {
            return false;
        };
        let mut todo = vec![(e, true)];
        while let Some((x, top)) = todo.pop() {
            let x = exported(x);
            match &x.kind {
                ExprKind::Call { .. } => {}
                ExprKind::If {
                    then, otherwise, ..
                } => todo.extend([(&**otherwise, false), (&**then, false)]),
                _ if top => return false,
                _ if self.kept_ops.contains_key(&x.span) => {}
                _ if literal(x, self.t.text).is_some() => {}
                _ => match self.seen.get(&x.span) {
                    Some((Some(t), _)) if !lists_a_number(t) => {}
                    _ => return false,
                },
            }
        }
        true
    }

    /// The one carrier, `f64`, `f32` or `rat`, of the part that the argument `a`, read at a carrier
    /// ([`Self::readable`]), holds whole beside the values it lists: `f64` for `g(b, x)` of type
    /// `1 | f64`. `None` for any other argument.
    fn read_whole(&self, a: &Arg) -> Option<Carrier> {
        if !values_alone(&a.ty) || !self.readable(a) || !lists_a_number(&a.ty) {
            return None;
        }
        match whole_carriers(&a.ty).collect::<Vec<_>>()[..] {
            [c @ (Carrier::F64 | Carrier::F32 | Carrier::Rat)] => Some(c),
            _ => None,
        }
    }

    /// The arguments of a refused application of `sig` as its message shows them, where the
    /// parts its arguments hold whole are of two or more carriers and some argument read at a
    /// carrier holds one of them, as `g(b, x) + gr(b, r)` with `g(b, x)` of type `1 | f64`
    /// and `gr(b, r)` of `1 | rat` (DESIGN.md step L1.26a, rule 3: the application is
    /// refused): each such argument is shown as the carrier it holds whole ([`Self::read_whole`]),
    /// `(f64, rat)`, since its listed values are read at that carrier and the two carriers are
    /// what no arrow takes, not the `1` a check of each value apart meets first. `None` where
    /// this does not hold, or where some arrow takes the parts shown.
    // Complexity tradeoff: asked only once an application is refused, O(n) for the n
    // arguments' types and O(A n) subtype tests for the A arrows; the naive message, the
    // first pair of values that no arrow takes, needs nothing more and names the listed `1`.
    fn shown_whole(&self, sig: &Sig, args: &[Option<Arg<'a>>]) -> Option<Vec<Option<Arg<'a>>>> {
        let generic = |a: &Arg| {
            a.lit.as_ref().is_some_and(|l| l.bare) || a.parts.is_some() || a.branches.is_some()
        };
        if args.iter().flatten().count() < 2 || args.iter().flatten().any(generic) {
            return None;
        }
        let whole: BTreeSet<Carrier> = (args.iter().flatten())
            .flat_map(|a| whole_carriers(&a.ty))
            .collect();
        if whole.len() < 2 {
            return None;
        }
        let mut read = false;
        let shown: Vec<Option<Arg<'a>>> = (args.iter())
            .map(|a| {
                let a = a.as_ref()?;
                Some(match self.read_whole(a) {
                    Some(c) => {
                        read = true;
                        Arg {
                            ty: Ty::carrier(c),
                            ..a.clone()
                        }
                    }
                    None => a.clone(),
                })
            })
            .collect();
        // A parameter that is a bounded variable takes the arguments at it only where they are
        // one type of numbers of its bound, as `add(a, b)` of type `(T, T) -> T`.
        let taken = sig.arrows.iter().any(|arrow| {
            let mut at_var: HashMap<&str, &Ty> = HashMap::new();
            (shown.iter().zip(&arrow.params)).all(|(a, p)| {
                let Some(a) = a else {
                    return true;
                };
                match p.as_var().and_then(|v| Some((v, sig.bounds.get(v)?))) {
                    Some((v, &m)) => {
                        let bits = (a.ty.pieces().iter())
                            .try_fold(0u8, |b, q| Some(b | q.carrier()?.bit()));
                        let t = *at_var.entry(&**v).or_insert(&a.ty);
                        bits.is_some_and(|b| b & !m == 0) && t.subtype(&a.ty) && a.ty.subtype(t)
                    }
                    None => p.dynamic || self.sub(&a.ty, p, &mut Binds::new()),
                }
            })
        });
        (read && !taken).then_some(shown)
    }

    /// The argument `a` read at the parameter `p` where [`Self::readable`] finds it is read
    /// at a carrier: [`read_ty`] of its type, with the adoptions of [`Self::read_adopting`].
    pub(super) fn read_arg(&self, a: &Arg, p: &Ty) -> Option<ReadArg> {
        // The cheap tests first: every operator application with an argument of no literal
        // asks, and few such arguments list a number. Complexity tradeoff (COMPLEXITY.md
        // F181): whether the argument is a call or an `if` ([`Self::readable`]) is O(1) for
        // any other argument, and is asked before [`lists_a_number`], which lists the values
        // of the type, O(v) for `v` values. Asked the other way round, each `min` of a chain
        // `a{i} = min(a{i - 1}, (i, 0.5f64, i))` listed the `i` values of its first
        // component, a name and no call, O(n²) bytes in all (44 times the bytes at 8 times
        // the length, MINMAX-chain-bytes-main).
        if p.dynamic || !p.vars.is_empty() || !self.readable(a) || !lists_a_number(&a.ty) {
            return None;
        }
        Some(match read_ty(&a.ty, p)? {
            Ok((t, c)) => Ok((t, c, Adoptions::new())),
            Err((v, c)) => (self.adopting(a, &v, c).map(|(t, ads)| (t, c, ads))).ok_or((v, c)),
        })
    }

    /// The argument `a`, which [`Self::readable`] finds is read, read at the carrier `c`:
    /// [`read_at`] of its type, with the adoptions that reading makes. A decimal the `if`
    /// that `a` is may give at `rat`, which [`read_at`] refuses, is taken where every such
    /// decimal is a literal with no suffix written as a branch of that `if` or of an `if` in
    /// it: each adopts `rat` exactly, as it would alone at a `rat` parameter (DESIGN.md step
    /// L1.26a, rule 3: "the literal `1` taking its carrier where the result is used"), and
    /// the `if` is read at `rat`, as in `h(if b { r } else { 2.5 })` with `r: rat`. A decimal
    /// a call gives is the `f64` it was read as, and is still refused.
    pub(super) fn read_adopting(
        &self,
        a: &Arg,
        c: Carrier,
    ) -> Option<Result<(Ty, Adoptions), Value>> {
        Some(match read_at(&a.ty, c)? {
            Ok(t) => Ok((t, Adoptions::new())),
            Err(v) => self.adopting(a, &v, c).ok_or(v),
        })
    }

    /// The argument `a` read at `c` where [`read_at`] refuses its value `v`: a decimal at `rat`
    /// that literals of the `if` `a` is give alone ([`Self::decimals_at_rat`]).
    fn adopting(&self, a: &Arg, v: &Value, c: Carrier) -> Option<(Ty, Adoptions)> {
        match (v, c) {
            (Value::Float(_), Carrier::Rat) => self.decimals_at_rat(a),
            _ => None,
        }
    }

    /// The `if` that `a` is, with each decimal literal written as a branch adopted at `rat`
    /// and its other values read at `rat`, or `None` where a decimal may come from elsewhere:
    /// a call or another branch whose type holds an `f64`, or a decimal with a suffix.
    // Complexity tradeoff: one walk over the `if`'s tree of branches, each visited once, an
    // adoption per decimal literal (O(n^1.47) in its digits, COMPLEXITY.md K41, as any decimal
    // literal at `rat` costs), then the n singletons joined in pairs, O(n log n), and one
    // read of the result ([`read_at`]). The naive form, [`read_at`] alone, refuses the `if`,
    // since it does not know where its decimals come from.
    fn decimals_at_rat(&self, a: &Arg) -> Option<(Ty, Adoptions)> {
        let e = a.expr?;
        let f64_ty = Carrier::F64.ty();
        let mut ads = Adoptions::new();
        let mut ts = vec![Ty::set(&a.ty.set - &f64_ty)];
        let mut todo = vec![e];
        while let Some(x) = todo.pop() {
            let x = exported(x);
            if let ExprKind::If {
                then, otherwise, ..
            } = &x.kind
            {
                todo.extend([&**otherwise, &**then]);
                continue;
            }
            match literal(x, self.t.text) {
                Some(l) if is_decimal(&l.value) => {
                    if !l.bare {
                        return None;
                    }
                    let v = adopt(&l, Carrier::Rat).ok()??;
                    ts.push(lit_ty(&v, l.neg()));
                    ads.push((l.span, v));
                }
                Some(_) => {}
                // A kept operation is on integer literals alone ([`Ck::kept_ops`]).
                None if self.kept_ops.contains_key(&x.span) => {}
                None => match self.seen.get(&x.span) {
                    Some((Some(t), _)) if (&t.set & &f64_ty).is_empty() => {}
                    _ => return None,
                },
            }
        }
        let t = Ty::union_all(&ts);
        match read_at(&t, Carrier::Rat) {
            None => Some((t, ads)),
            Some(Ok(t)) => Some((t, ads)),
            Some(Err(_)) => None,
        }
    }

    /// The arrows of `sig` whose adoptions of the literal arguments are fewest, all the
    /// same, with those adoptions made and the arguments retyped.
    /// `None` when a literal adopts no arrow's carrier exactly, which is reported.
    fn fewest(
        &mut self,
        what: &str,
        sig: &Sig,
        args: &mut [Option<Arg<'a>>],
    ) -> Result<Option<Vec<usize>>, String> {
        // Per arrow: its adoptions, the calls of literal values it reads at a carrier, and
        // each argument a literal of which adopts or a call that is read, retyped.
        type Best = (Adoptions, Vec<(Span, Carrier)>, Vec<(usize, Ty)>);
        let mut best: Option<Best> = None;
        let mut kept = Vec::new();
        let mut adopt_error = None;
        // A call of literal values that gives a value the carrier of an arrow the other
        // arguments fit does not hold: the argument, the value and the carrier.
        let mut unread = None;
        // Per literal argument without a suffix: the carriers of its parameter on the arrows
        // the other arguments fit, `None` once one of them is generic.
        let mut takes: BTreeMap<usize, Option<u8>> = BTreeMap::new();
        // A call or an `if` that lists values, each value or part of one carrier of which an arrow the other arguments
        // meet takes as it is, as `g(c)` of type `1 | 2.5` for `g(positional c: bool) = if
        // c { 1 } else { 2.5f64 }` at `f64(…)`, whose `1` the `int` arrow takes and whose
        // `2.5` the `f64` arrow does, is split among those arrows value by value, as
        // `f64(if c { 1 } else { 2.5f64 })` is, and is read at no carrier: the `int` arrow,
        // which reads nothing, would otherwise be the one arrow kept, and the `2.5` would
        // find none. A call some value of which no such arrow takes is read: in `x * g(c)`
        // with `x: f64`, the `1` of `g(c)` is read at `f64`, and so in `1.0f64 + g(c)`. A
        // literal with no suffix among the other arguments, or a tuple or an `if` of them,
        // takes its carrier from the arrow, so no arrow is known to take a value of the call
        // beside it, and the call is read as before: `1 + g(c)`.
        // Complexity tradeoff: O(A v) subtype tests of one value each, for the A arrows and
        // the v values the call's type lists, as the reads below cost; the naive form, the
        // reads alone, keeps the arrow that reads nothing and rejects the call.
        let generic = |a: &Arg| {
            a.lit.as_ref().is_some_and(|l| l.bare) || a.parts.is_some() || a.branches.is_some()
        };
        // The arguments whose listed values are read at a carrier where they are used
        // ([`Self::readable`]), found once for every arrow. [`Self::readable`] is asked before
        // [`lists_a_number`], as in [`Self::read_arg`].
        let read: Vec<bool> = (args.iter())
            .map(|a| {
                a.as_ref().is_some_and(|a| {
                    values_alone(&a.ty) && self.readable(a) && lists_a_number(&a.ty)
                })
            })
            .collect();
        // Two or more operands, one of which lists values beside a part of one carrier it holds
        // whole, as `g(b, x) + g(b, x)` with `g(b, x)` of type `1 | f64`: the application is
        // at that carrier, the one carrier of the parts the operands hold whole, `f64` there,
        // and every listed value of each operand is read at it, as it would be beside an
        // `f64` operand (DESIGN.md step L1.26a). Its arrows are those that take that carrier
        // at each operand that is no literal; a bare literal adopts it as beside any `f64`.
        // Where the whole parts are of two carriers, as `int` and `f64` in `n + g(b, x)` with
        // `n: int`, or of none, there is no such carrier and the operands are split or read
        // as below.
        // Complexity tradeoff: the carrier is found from each operand's type once and each
        // operand is read at it once, O(Σ v log v) for the v values each operand lists, with
        // no pair of values formed. The naive form, each pair of values of two operands
        // checked as it would be alone, costs O(v₁ v₂) pairs and gives `int | f64` for
        // `g(b, x) + g(b, x)`, a carrier chosen at run time by two operands at once, which no
        // other application has.
        // The parts are found only where some operand is read, so an application of no read
        // operand lists no type's values here, as [`Self::read_arg`] asks [`Self::readable`]
        // first (MINMAX-chain-bytes-main).
        let one = if read.contains(&true) && args.iter().flatten().count() > 1 {
            let whole: BTreeSet<Carrier> = (args.iter().flatten())
                .filter(|a| !generic(a))
                .flat_map(|a| whole_carriers(&a.ty))
                .collect();
            match whole.iter().collect::<Vec<_>>()[..] {
                [&c @ (Carrier::F64 | Carrier::F32 | Carrier::Rat)] => Some(c),
                _ => None,
            }
        } else {
            None
        };
        let split: Vec<bool> = (args.iter().enumerate())
            .map(|(i, a)| {
                let Some(a) = a.as_ref().filter(|_| read[i] && one.is_none()) else {
                    return false;
                };
                if args.iter().flatten().any(generic) {
                    return false;
                }
                let meeting: Vec<&Ty> = (sig.arrows.iter())
                    .filter(|arrow| {
                        (args.iter().zip(&arrow.params)).all(|(a, p)| {
                            a.as_ref().is_none_or(|a| a.ty.is_empty() || a.ty.meets(p))
                        })
                    })
                    .map(|arrow| &arrow.params[i])
                    .collect();
                // Each value it lists, and each part of one carrier it holds whole, as the
                // `f64` of `1 | f64`, is taken as it is by some arrow.
                taken_apart(&a.ty)
                    .iter()
                    .all(|t| meeting.iter().any(|p| p.dynamic || t.subtype(p)))
            })
            .collect();
        for (k, arrow) in sig.arrows.iter().enumerate() {
            if let Some(c) = one
                && !(args.iter().zip(&arrow.params)).all(|(a, p)| {
                    a.as_ref()
                        .is_none_or(|a| generic(a) || p.dynamic || Ty::carrier(c).subtype(p))
                })
            {
                continue;
            }
            let mut need = Adoptions::new();
            let mut retyped = Vec::new();
            // An arrow no other argument can fit is no candidate, and its literals are not
            // adopted: a decimal literal's adoption at `rat` reads its digits (COMPLEXITY.md
            // K41), as at the `rat` arrow of `n + 0.5` with `n` an int.
            // A call or an `if` that lists values, `g(c)` of type `1 | 2` or `1 | f64`, is read at the
            // parameter's carrier, `f64`, `f32` or `rat`, as at a declared parameter ([`read_ty`];
            // L1.26a: "each keeps its own value and is fixed where the result is used"): in
            // `x * g(c)` with `x: f64` it is an `f64` at the `f64` arrow. Complexity
            // tradeoff: each such argument is read once per arrow, O(A v log v) for A arrows
            // and v values its type lists; A is at most five for an operator.
            let mut reads = Vec::new();
            let mut called = Vec::new();
            let mut ok = (args.iter().zip(&arrow.params).enumerate()).all(|(i, (a, p))| match a {
                // Read before the type meets `p`: `1 | 2.5` meets `f64` at its `2.5`, and its
                // `1` is read; a call split among the arrows (`split`) is not.
                Some(a)
                    if a.lit.is_none() && a.parts.is_none() && a.branches.is_none() && split[i] =>
                {
                    a.ty.is_empty() || a.ty.meets(p)
                }
                Some(a) if a.lit.is_none() && a.parts.is_none() && a.branches.is_none() => {
                    match (read[i].then(|| read_carrier(p)).flatten()).and_then(|c| {
                        Some(
                            self.read_adopting(a, c)?
                                .map(|r| (r, c))
                                .map_err(|v| (v, c)),
                        )
                    }) {
                        Some(r) => {
                            called.push((i, r));
                            true
                        }
                        None => a.ty.is_empty() || a.ty.meets(p),
                    }
                }
                _ => true,
            });
            if !ok {
                continue;
            }
            let mut error = None;
            // The calls read, in the order of their arguments, met again in that order.
            let mut called = called.into_iter().peekable();
            for (i, (a, p)) in args.iter().zip(&arrow.params).enumerate() {
                let Some(a) = a else {
                    continue;
                };
                if a.lit.is_none() && a.parts.is_none() && a.branches.is_none() {
                    match called.next_if(|(j, _)| *j == i).map(|(_, r)| r) {
                        Some(Ok(((t, ads), c))) => {
                            let e = a.expr.expect("a call read at a carrier");
                            need.extend(ads);
                            reads.push((e.span, c));
                            retyped.push((i, t));
                        }
                        Some(Err((v, c))) => {
                            unread.get_or_insert((i, v, c));
                            ok = false;
                        }
                        None => {}
                    }
                    continue;
                }
                if self.subtype(&a.ty, p) || p.dynamic {
                    continue;
                }
                match adopted(a, p, self.rough) {
                    Ok(Some((t, ads))) if self.subtype(&t, p) => {
                        need.extend(ads);
                        retyped.push((i, t));
                    }
                    Err(e) => {
                        error.get_or_insert(e);
                    }
                    // Kept as it is, the argument is checked as any argument is.
                    _ => ok &= a.ty.meets(p),
                }
            }
            // The message names a literal's rejection at an arrow the other arguments fit:
            // `x + 0.1` with `x: rat` at rat, not at int; and of two literals of two
            // carriers, as at `==`, the integer's, or else the decimal's: `1 + 0.5` at `1`.
            // A literal of a branch counts as one: in
            // `min(if c { 9007199254740993 } else { 1 }, 0.5f64)` the message names the
            // integer, which has no exact `f64`, not the `0.5f64` the `int` arrow rejects.
            if let Some(e) = error {
                let rank = |s: Span| {
                    args.iter()
                        .flatten()
                        .flat_map(|a| {
                            let bs = a.branches.iter().flat_map(|bs| bs.iter());
                            a.lit.iter().chain(bs.flat_map(|b| match b {
                                Branch::Lit(l) => std::slice::from_ref(l),
                                Branch::Op { lits, .. } => &lits[..],
                            }))
                        })
                        .find(|l| l.site == s)
                        .map_or(3, |l| match lit_carrier(&l.value) {
                            Carrier::Int => 0,
                            Carrier::F64 => 1,
                            _ => 2,
                        })
                };
                if ok
                    && adopt_error
                        .as_ref()
                        .is_none_or(|(t, _)| rank(e.0) < rank(*t))
                {
                    adopt_error = Some(e);
                }
                continue;
            }
            if !ok {
                continue;
            }
            for (i, (a, p)) in args.iter().zip(&arrow.params).enumerate() {
                if let Some(a) = a
                    && (a.lit.as_ref().is_some_and(|l| l.bare) || a.branches.is_some())
                {
                    let m = takes.entry(i).or_insert(Some(0));
                    *m = m
                        .filter(|_| !p.dynamic && p.vars.is_empty())
                        .map(|m| m | mask_of(p));
                }
            }
            // A read counts as an adoption: `g(c) * g(c)` takes the `int` arrow, which
            // reads nothing.
            let count = need.len() + reads.len();
            match &best {
                Some((n, r, _)) if n.len() + r.len() < count => {}
                Some((n, r, _)) if *n == need && *r == reads => kept.push(k),
                Some((n, r, _)) if n.len() + r.len() == count => {}
                _ => {
                    best = Some((need, reads, retyped));
                    kept = vec![k];
                }
            }
        }
        let Some((need, reads, retyped)) = best else {
            if let Some((i, v, c)) = unread {
                let a = args[i].as_ref().expect("a call read at a carrier");
                return Err(self.unread_call(what, args, a, &v, c, true));
            }
            // A value of an argument that no arrow takes, as `true` of `gi(true)` of type
            // `1 | true` in `1.0f64 + gi(true)`: the application fails whatever carrier its
            // literals take, so the message is the application's and names that value, not a
            // literal refused at the arrow the argument's other value, `1`, chose.
            if let Some((i, piece)) = self.taken_by_none(sig, args) {
                let p = &sig.arrows[0].params[i];
                return Err(self.rejected_at(what, args, piece.as_ref().map(|q| (i, q, p))));
            }
            if let Some((s, m)) = adopt_error {
                self.lit_refused.push((s, m));
                return Ok(None);
            }
            // No arrow met an argument, which may rest on a refused check that it is empty.
            let tys: Vec<Option<&Ty>> = args
                .iter()
                .map(|a| a.as_ref().filter(|a| a.lit.is_none()).map(|a| &a.ty))
                .collect();
            let all: Vec<usize> = (0..sig.arrows.len()).collect();
            let why = refused_among(sig, &all, &tys);
            if why.is_empty()
                && let Some(whole) = self.shown_whole(sig, args)
            {
                return Err(self.rejected(what, &whole));
            }
            return Err(self.rejected_because(what, args, &why));
        };
        // A literal that two or more of the word's numeric carriers take, and that nothing
        // else here gives one, as `abs(0.5)` or `String(0.5)`: an integer literal is `int`
        // where `int` is among them, float formats alone, `f64` among them, take `f64`, as
        // `sqrt(2.0)` does ([`floats_take_f64`]), and otherwise it is rejected (steps L1.26a and
        // L1.26b). One value gives one error: of two such operands, as in `0.5 * 2.0`, the first
        // decimal literal, or else the first literal, is rejected. A branch of an `if` of
        // literals is a literal there as it is alone: `f64(if c { 1 } else { 2.5 })` is
        // rejected at the `2.5`, as `f64(0.5)` is, and `f64(if c { 1 } else { 2 })` is an
        // `int` at the `int` arrow.
        let unfixed_lits = takes.iter().flat_map(|(&i, m)| {
            let found = (m.zip(args.get(i).and_then(Option::as_ref))).map(|(m, a)| {
                let bs = a.branches.iter().flat_map(|bs| bs.iter());
                let ls = a.lit.iter().chain(bs.filter_map(|b| match b {
                    Branch::Lit(l) if l.bare => Some(l),
                    _ => None,
                }));
                let left: Vec<Carrier> = Carrier::of_mask(m).filter(|c| c.numeric()).collect();
                ls.filter_map(move |l| {
                    let int = lit_carrier(&l.value) == Carrier::Int && left.contains(&Carrier::Int);
                    (!int && left.len() > 1 && !floats_take_f64(&left)).then(|| (l, left.clone()))
                })
            });
            found.into_iter().flatten()
        });
        let mut first = None;
        for (l, left) in unfixed_lits {
            let decimal = is_decimal(&l.value);
            if first.is_none() || decimal {
                first = Some((l.clone(), left));
            }
            if decimal {
                break;
            }
        }
        let rejected = first.is_some();
        if let Some((l, left)) = first {
            let notes = self.derive(&[l.site]);
            self.reject(Some(Row::UnfixedDecimal), l.site, unfixed(&l, &left), notes);
        }
        // A call rejected so gives no value, as a rejected application gives, so that the
        // arrows it then meets do not report it again: `1 + g(c)`.
        if !rejected && self.unfixed_calls(what, sig, args) {
            return Ok(None);
        }
        for (i, t) in retyped {
            if let Some(a) = &mut args[i] {
                a.ty = t;
            }
        }
        for (s, v) in need {
            self.put(Undo::Adopt(s, Some(v)));
        }
        for (s, c) in reads {
            self.put(Undo::Fit(s, Some(Fit::Read(c))));
        }
        Ok(Some(kept))
    }

    /// Rejects the decimal literals with no suffix that a call among `args` may give through
    /// its body, where the arrows of `sig` that the other arguments meet hold both `f64` and
    /// `rat` at its place, so that nothing gives them a carrier: `f64(g(c))` with `g(positional c: bool) = if c { 1 } else { 2.5 }` is
    /// rejected at the `2.5`, as `f64(0.5)` is (L1.26b: "Where nothing fixes its carrier a
    /// decimal literal is rejected"), and as `y = g(c)` is (L1.26a). One arrow at one
    /// carrier fixes it: `x * g(c)` with `x: f64` reads the call at `f64`. A generic
    /// parameter fixes none here; the call is the function's, whose use fixes it.
    /// Inside a function too: `k(positional d: bool) = f64(g(d))` is rejected, since only a
    /// call whose type lists values alone is read, and a value `g` gives from a parameter of
    /// `k` would make its type list that parameter's class, as in `f64(g(d, x))` with
    /// `g(positional c: bool, positional x) = if c { x } else { 0.5 }`. Whether it rejected
    /// one.
    // Complexity tradeoff: the arguments' types are met with the A arrows' parameters,
    // O(A k) meets for k arguments, only for a call whose type lists a decimal value; the
    // literals are found as a binding finds them ([`Self::unfixed_tails`], which reads each
    // body once per function and type). The naive form, the call's type alone, cannot tell
    // `2.5` from `2.5f64`, since both are the value `2.5`.
    fn unfixed_calls(&mut self, what: &str, sig: &Sig, args: &[Option<Arg<'a>>]) -> bool {
        let mut any = false;
        for (i, a) in args.iter().enumerate() {
            let Some(a) = a else { continue };
            let Some(e) = lone_call(a) else { continue };
            let decimal = |vs: Vec<Value>| vs.iter().any(|v| matches!(v, Value::Float(_)));
            if !call_values(a).is_some_and(decimal) {
                continue;
            }
            let (mut f64, mut rat) = (false, false);
            let mut generic = false;
            for arrow in &sig.arrows {
                let others = (args.iter().zip(&arrow.params).enumerate()).all(|(j, (b, p))| {
                    j == i
                        || b.as_ref().is_none_or(|b| {
                            b.lit.is_some()
                                || b.parts.is_some()
                                || b.branches.is_some()
                                || b.ty.is_empty()
                                || b.ty.meets(p)
                        })
                });
                if !others {
                    continue;
                }
                let p = &arrow.params[i];
                if !p.vars.is_empty() {
                    generic = true;
                    break;
                }
                // A parameter of every type, as of `String`, takes every carrier, so it gives
                // none: `String(g(c))` is rejected at the `2.5`, as `String(0.5)` is.
                f64 |= p.dynamic || !(&p.set & &Carrier::F64.ty()).is_empty();
                rat |= p.dynamic || !(&p.set & &Carrier::Rat.ty()).is_empty();
            }
            if generic || !(f64 && rat) {
                continue;
            }
            let found: Vec<(Span, Msg)> = (self.unfixed_tails(e, &a.ty).into_iter())
                .map(|(_, at, m)| (at, m))
                .collect();
            any |= !found.is_empty();
            self.reject_unfixed(&format!("the argument of {what}"), found);
        }
        any
    }
}

/// The literals written in the tuple `e`, by component, at any depth, and the `if`s of
/// literals there ([`branch_lits`], whose operations `kept` gives); `None` when `e` is not a
/// tuple or holds neither. The tuples nest as deep as the text, so the walk keeps its own
/// stack: each open tuple's items, the next one, its parts so far, and whether one is a
/// literal or an `if` of them at some depth.
// Complexity tradeoff: each component is read once, and [`branch_lits`] walks only a
// component that is an `if`, once, O(its size), so the walk is O(the tuple's text). The
// naive form, the component's type `1 | 3` tested against the parameter's `f64`, needs no
// walk but rejects the call, since that type holds the values, not the literals that wrote
// them.
fn parts<'e>(
    e: &'e Expr,
    src: Option<&str>,
    kept: &HashMap<Span, usize>,
) -> Option<Rc<[Part<'e>]>> {
    let ExprKind::Tuple(items) = &e.kind else {
        return None;
    };
    let mut stack: Vec<(&[Expr], usize, Vec<Part>, bool)> = vec![(items, 0, Vec::new(), false)];
    loop {
        let (items, next, ps, any) = stack.last_mut().expect("an open tuple");
        let Some(item) = items.get(*next) else {
            let (_, _, ps, any) = stack.pop().expect("an open tuple");
            let ps: Rc<[Part]> = ps.into();
            match stack.last_mut() {
                None => return any.then_some(ps),
                Some(up) => {
                    up.2.push(if any { Part::Tuple(ps) } else { Part::Other });
                    up.3 |= any;
                }
            }
            continue;
        };
        *next += 1;
        match (literal(item, src), &item.kind) {
            (Some(l), _) => {
                ps.push(Part::Lit(l));
                *any = true;
            }
            (None, ExprKind::Tuple(inner)) => stack.push((inner, 0, Vec::new(), false)),
            (None, _) => match branch_lits(item, src, kept) {
                Some(bs) => {
                    ps.push(Part::Branches(bs));
                    *any = true;
                }
                None => ps.push(Part::Other),
            },
        }
    }
}

/// The operands of an ordering, for its messages: each one's name where it is a name, and
/// where it is.
struct OrderSides<'n> {
    names: [Option<&'n str>; 2],
    ats: [Option<Span>; 2],
    /// Whether each operand holds no atom, so that a tuple written out can stand for it.
    plain: [bool; 2],
    /// Whether each operand is an int the checker shows lies within ±2^53, so that `f64` of it
    /// is exact ([`Ck::exact_in_f64`]): a repair may cast it, where it is not a tuple.
    exact: [bool; 2],
}

/// A pair of component types an ordering compares ([`Ck::components`]): the types, and the
/// index of the pair it was met in, `usize::MAX` for the operands, with its position there.
struct Met {
    up: usize,
    at: usize,
    ty: [Ty; 2],
}

/// A repair of a rejected application ([`Ck::repairs`]): its note, what its trial gave, and the
/// fix that writes it in the program's text, where the text shows it.
struct Repaired {
    note: Note,
    got: Option<(Ty, Vec<Span>)>,
    fix: Option<Rewrite>,
}

/// The literal a cast gives on a literal argument ([`Ck::literal_repair`]): its text as the
/// program writes it, and the argument it is where the checker reads it alone.
struct Literal<'a> {
    text: String,
    arg: Arg<'a>,
}

/// The `rat` literal `text`, written `meKr` as a type prints it (`5e-1r`, `125e-2r`, `1e3r`),
/// with its point in place of the exponent, `0.5r` or `1.25r`, where that is no longer;
/// `None` where it is longer, as `1000r` for `1e3r` or `0.0001r` for `1e-4r`, or where
/// `text` has no exponent. As `Rat::integer_text` chooses between digits and powers, the
/// shorter of the two forms is written, a tie going to the point, which the program's own
/// literals use. The length of the form with the point is counted before it is built, so a
/// literal `1e400000r` costs its own length, O(|text|), and not the exponent's.
fn plain_rat(text: &str) -> Option<String> {
    let body = text.strip_suffix('r')?;
    let (sign, body) = match body.strip_prefix('-') {
        Some(b) => ("-", b),
        None => ("", body),
    };
    let (m, k) = body.split_once('e')?;
    let (point, k) = match k.strip_prefix('-') {
        Some(k) => (true, k),
        None => (false, k),
    };
    let k: usize = k.parse().ok()?;
    // The digits of `m` with `k` zeros after them; or with the point `k` places from their
    // end, preceded by `0.` and zeros where it falls before them.
    let len = match point {
        false => m.len().checked_add(k)?,
        true if k < m.len() => m.len() + 1,
        true => k.checked_add(2)?,
    };
    if len > body.len() {
        return None;
    }
    let plain = match point {
        false => format!("{m}{}", "0".repeat(k)),
        true if k < m.len() => format!("{}.{}", &m[..m.len() - k], &m[m.len() - k..]),
        true => format!("0.{}{m}", "0".repeat(k - m.len())),
    };
    Some(format!("{sign}{plain}r"))
}

/// Why a pair of values does not compare under an ordering.
enum Unordered {
    /// The values of each side that are not tuples, numbers of two kinds or two values of two
    /// other kinds.
    Kinds(Ty, Ty),
    /// The pieces of either side met by a tuple, then those met by an atom.
    Refused([Vec<String>; 2]),
}

/// Joins the fixes `fixes` to those of `up` that give a construct the type `ty` ([`Carry`]),
/// the smaller group appended to the larger, so a fix moves O(log fixes) times however many
/// joins it goes through.
fn carry_joined(up: &mut HashMap<Ty, Vec<Pending>>, ty: Ty, mut fixes: Vec<Pending>) {
    let group = up.entry(ty).or_default();
    if group.len() < fixes.len() {
        std::mem::swap(group, &mut fixes);
    }
    group.append(&mut fixes);
}

/// The edits `edits` sorted by where they start, and then by where they end, as a corrected
/// line writes them ([`Rewrite::line`]). O(e log e).
fn in_text_order(edits: &[(Span, String)]) -> Vec<&(Span, String)> {
    let mut sorted: Vec<&(Span, String)> = edits.iter().collect();
    sorted.sort_by_key(|(s, _)| (s.start, s.end));
    sorted
}

/// The edits of `sorted` ([`in_text_order`]) that lie in `at`, each with its place in
/// `sorted`: a binary search for the first that starts in `at`, then those after it that do.
/// O(log e + the edits that start in `at`).
fn edits_in<'s, 'e>(
    sorted: &'s [&'e (Span, String)],
    at: Span,
) -> impl Iterator<Item = (usize, &'e (Span, String))> + 's {
    let from = sorted.partition_point(|(s, _)| s.start < at.start);
    (sorted[from..].iter().enumerate())
        .take_while(move |(_, (s, _))| s.start <= at.end)
        .filter(move |(_, (s, _))| s.end <= at.end)
        .map(move |(k, e)| (from + k, *e))
}

/// Whether `s` lies in one of the spans `sorted`, sorted by where they start and then by where
/// they end, that lie apart in the text, as the arguments of one construct do: the last of
/// them that starts at or before `s` is the one it may lie in. O(log n).
fn lies_in(sorted: &[Span], s: Span) -> bool {
    let k = sorted.partition_point(|a| a.start <= s.start);
    (k.checked_sub(1)).is_some_and(|k| s.end <= sorted[k].end)
}

/// The index of the argument whose place, in `sorted` as [`lies_in`] reads its spans, `s` lies
/// in, if one holds it. O(log n).
fn arg_holding(sorted: &[(Span, usize)], s: Span) -> Option<usize> {
    let k = sorted
        .partition_point(|(a, _)| a.start <= s.start)
        .checked_sub(1)?;
    let (a, j) = sorted[k];
    (s.end <= a.end).then_some(j)
}

/// The signature of a call of `sig` with its parameter `j` alone, for a signature whose
/// parameters are checked apart ([`params_apart`]): its parameter `j` and the result of its
/// one arrow. O(the size of those).
fn param_alone(sig: &Sig, j: usize) -> Sig {
    let arrow = &sig.arrows[0];
    Sig {
        params: vec![sig.params[j].clone()],
        arrows: vec![Arrow {
            params: vec![arrow.params[j].clone()],
            result: arrow.result.clone(),
        }],
        bounds: BTreeMap::new(),
        data: sig.data,
        dense: sig.dense,
        word: None,
        needs: Vec::new(),
        own: BTreeSet::new(),
        held: BTreeSet::new(),
        named: sig.named,
        facts: Default::default(),
    }
}

/// Whether a call of `sig` checks each argument against its parameter apart from the others:
/// one arrow, no type variable of its own or bounded, no need of the body, not a prelude word
/// or a family, and parameters and result that hold no variable or unknown ([`Ty::closed`]),
/// so an argument's type changes neither what another argument meets nor the result.
/// O(the arrow's parameters).
fn params_apart(sig: &Sig) -> bool {
    match sig.arrows.as_slice() {
        [arrow] => {
            sig.own.is_empty()
                && sig.bounds.is_empty()
                && sig.needs.is_empty()
                && sig.word.is_none()
                && !sig.data
                && arrow.result.closed()
                && arrow.params.iter().all(Ty::closed)
        }
        _ => false,
    }
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
        let mut ck = Ck::new(&t, Ck::fixes_checked);
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
        let mut ck = Ck::new(&t, Ck::fixes_checked);
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

    /// A `rat` literal is written with its point where that is no longer than its exponent
    /// form, a tie going to the point, and keeps the exponent form where that is shorter
    /// (row REPAIR-literal-cast).
    #[test]
    fn a_rat_literal_is_written_with_its_point_where_that_is_no_longer() {
        let cases = [
            ("5e-1r", Some("0.5r")),
            ("-5e-1r", Some("-0.5r")),
            ("125e-2r", Some("1.25r")),
            ("125e-1r", Some("12.5r")),
            ("5e-2r", Some("0.05r")),
            ("1e1r", Some("10r")),
            // Ties: `12e2r` and `1200r` are as long, as are `1e-2r` and `0.01r`.
            ("12e2r", Some("1200r")),
            ("1e3r", None),
            ("1e-4r", None),
            ("-1e-4r", None),
            ("1e-2r", Some("0.01r")),
            // No exponent, as `8r`, or not a `rat` literal at all.
            ("8r", None),
            ("8", None),
            ("1e400000r", None),
            ("1e-400000r", None),
        ];
        for (text, want) in cases {
            assert_eq!(plain_rat(text).as_deref(), want, "{text}");
        }
    }
}
