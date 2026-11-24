//! Elaboration's walk over statements and expressions, on a heap stack: a unit nested as
//! deep as memory allows elaborates on a thread of any stack size.
//!
//! Each recursive call of the walk is a [`Job`]. What the caller does with the call's result
//! is a [`Frame`] pushed below the job, which reads the result from [`M::ret`] when the job
//! is done. A loop of calls is one frame that starts the next call each time it resumes, and
//! [`M::seq`] runs a list of expressions for the frame below it. The jobs run in the order
//! the calls of the recursive walk ran, and each stops where that walk returned early, so the
//! errors, the temporaries and the marks come out in the same order.

mod fp_ops;

use std::collections::{BTreeSet, HashMap, HashSet};
use std::mem;
use std::sync::Arc;

use zed_kernel::num::LiteralRounding;
use zed_kernel::types::Type as KType;
use zed_kernel::{Pattern as KPattern, Prim, Rat, Shared, Term, Value};

use zedc_base::rejection::not_yet;
use zedc_check::check::{self, CalledKind, Fit, Misfit};
use zedc_resolve::resolve::topo::topo;
use zedc_resolve::resolve::{Ref, open_stream, prelude_layer};
use zedc_stage::defs::Test;
use zedc_syntax::ast::{
    BinaryOp, Error, Expr, ExprKind, Function, Note, Pattern, PortName, RangeEnd, Stmt, StmtKind,
    StrPart, Target, TestPorts, UnaryOp,
};
use zedc_syntax::lex::{Span, unread_literal};

use super::instances::{Dropped, Env, Local};
use super::mark::{Kind, Mark, Slot, arithmetic, mark_of, mutable, op_mark};
use super::state::{Bind, Elab};
use fp_ops::Quantifier;
use zedc_check::check::ty::{Carrier, Sig};
use zedc_syntax::ast::Param;

/// The inputs a row of `main`'s table gives, by the position of each in a key that is a tuple:
/// standard input, the arguments one per line, the environment as a function of the name, and
/// the files as a function of the path (DESIGN.md sec:syntax_tour, `test`), each the field of
/// `MainArgs` that gives it, or `main::files`.
pub const MAIN_KEY: [&str; 4] = ["stdin", "args", "env", "main::files"];

/// What a job gives back.
enum Ret {
    /// Nothing yet.
    None,
    /// An expression's or a block's term.
    T(Option<Term>),
    /// The terms of a list of expressions, as far as they ran.
    Got(Vec<Option<Term>>),
    /// A scope's bindings and export.
    Scope(Option<(Vec<Bind>, Option<Term>)>),
    /// A statement's bindings.
    Stmt(Option<Vec<Bind>>),
    /// Whether a function's test tables elaborated.
    Tests(bool),
}

enum Job<'a> {
    /// An expression's term.
    Expr(&'a Expr),
    /// A block's term.
    Block(&'a [Stmt]),
    /// The statements of a scope; whether it is the unit's.
    Scope(&'a [Stmt], bool),
    /// A caller waiting for the result of the jobs above it.
    K(Frame<'a>),
}

/// The heap stack and the result of the last job done.
struct M<'a> {
    stack: Vec<Job<'a>>,
    ret: Ret,
}

impl<'a> M<'a> {
    fn take(&mut self) -> Ret {
        mem::replace(&mut self.ret, Ret::None)
    }

    fn t(&mut self) -> Option<Term> {
        match self.take() {
            Ret::T(t) => t,
            _ => unreachable!("a term"),
        }
    }

    fn got(&mut self) -> Vec<Option<Term>> {
        match self.take() {
            Ret::Got(got) => got,
            _ => unreachable!("a list of terms"),
        }
    }

    fn k(&mut self, f: Frame<'a>) {
        self.stack.push(Job::K(f));
    }

    fn give(&mut self, t: Option<Term>) {
        self.ret = Ret::T(t);
    }

    /// Runs `exprs` in order, then gives their terms; with `stop`, stops after the first
    /// that fails, as a `collect` into an `Option` does.
    fn seq(&mut self, mut exprs: Vec<&'a Expr>, stop: bool) {
        exprs.reverse();
        match exprs.pop() {
            None => self.ret = Ret::Got(Vec::new()),
            Some(first) => {
                self.k(Frame::Seq(Box::new(SeqF {
                    left: exprs,
                    got: Vec::new(),
                    stop,
                })));
                self.stack.push(Job::Expr(first));
            }
        }
    }

    /// A lambda's body: a block's term, or an expression's.
    fn body(&mut self, body: &'a Expr) {
        self.stack.push(match &body.kind {
            ExprKind::Block(stmts) => Job::Block(stmts),
            _ => Job::Expr(body),
        });
    }
}

/// All of `got`, if each is there.
fn all(got: Vec<Option<Term>>) -> Option<Vec<Term>> {
    got.into_iter().collect()
}

/// A list of expressions being run.
struct SeqF<'a> {
    /// Those not run yet, last first.
    left: Vec<&'a Expr>,
    got: Vec<Option<Term>>,
    stop: bool,
}

enum Frame<'a> {
    Seq(Box<SeqF<'a>>),
    /// A unary operator, by its expression, once its operand is elaborated.
    Unary(Prim, &'a Expr),
    /// A call read at a carrier ([`Fit::Read`]), by its span, once elaborated: the cast to it.
    Read(Span, Prim),
    /// A value rebuilt for a type holding a partial function type ([`Fit::Coerce`]), by its
    /// span, once elaborated.
    Coerce(Span, &'a check::Coercion),
    /// A generic literal of [`check::Info::witness`], by its span, once elaborated: it takes
    /// the carrier of the value of the parameter of that binder.
    Witness(Span, &'a check::Witness),
    Binary(&'a Expr),
    Tuple,
    Is(&'a Expr),
    Else(&'a Expr),
    If(&'a Expr),
    Str(&'a [StrPart]),
    Pass(Box<PassF<'a>>),
    PassCall(Box<PassF<'a>>),
    /// A block, with the number of `inst.locals` when it starts: those after are its own.
    Block(usize),
    Scope(Box<ScopeF<'a>>),
    Export(Box<ScopeF<'a>>),
    Bind(&'a Stmt),
    Push(&'a Stmt),
    FnDefault(Box<FnF<'a>>),
    FnBody(Box<FnF<'a>>),
    FnTests(Box<FnF<'a>>),
    TestArgs(Box<TestsF<'a>>),
    TestWant(Box<TestsF<'a>>, Option<Vec<Term>>),
    /// A call through the value of its callee, once the callee is elaborated.
    CallOf(Call<'a>),
    /// An atom's payload: the atom's name and its fields.
    AtomArgs(&'a str, &'a [(String, Expr)]),
    /// A call through a value of no known signature: the value and the receiver.
    ValueArgs(Term, Option<Term>),
    /// A family whose keys are one integer interval, applied to the key being elaborated and
    /// then to the keys after it: its read `at(f, k)`, then one read per later key
    /// ([`Elab::call_value`]).
    AtArg(Term, &'a [Expr]),
    /// A call through a value that the function called places ([`Elab::placed_call`]): the
    /// value, the receiver, and the call's shape with, for a curried call, its result's list.
    PlacedArgs(Term, Option<Term>, Box<Placing>),
    Fill(Box<FillF<'a>>),
    ValueDefault(Box<FillF<'a>>),
    DeclDefault(Box<FillF<'a>>),
    MemberOf(Box<Member<'a>>),
    /// A member call made, wrapped for `?.` by the receiver's temporary and value.
    MemberEnd(Option<(Arc<str>, Term)>),
    /// `f[k]` of the declared function `f`, written at the span.
    IndexDeclared(usize, &'a Expr, Span),
    Index(&'a Expr, Span),
    FitBody(Box<FitF<'a>>),
    FitExtras(Box<FitF<'a>>, Term),
    Lambda(Vec<Arc<str>>),
    /// A display's parts elaborated: an array's elements, a set's, or a map's keys and
    /// values in turn (step L3.2).
    Display(Display),
    /// `x.map(f)`, or `x.where(f)` when the flag is set, once `f` is elaborated: `x`'s term
    /// (step L3.2).
    MapFn(Term, bool),
    /// `x.foldl(init, f)` or, when the flag is set, `x.foldr(f, init)`, once both arguments are
    /// elaborated, in the order written: `x`'s term (step L3.3).
    FoldDir(Term, bool),
    /// `x.group(f)`, `f` being elaborated: the term of `x` (`group_term`).
    Group(Term),
    /// `x.chunkBy(f)`, `f` being elaborated: the term of `x` (`chunk_by_term`, step L5.3).
    ChunkBy(Term),
    /// `m >< (op)` once `m` is elaborated: the operator and the span of the fold.
    Fold(Prim, Span),
    /// `x.any(p)`, `x.all(p)` or `x.find(p)` once `p` is elaborated: `x`'s term (step
    /// L3.15a).
    Quantify(Term, Quantifier),
    /// A stream over `a ..` read by `.first` (`None`) or a quantifier, once the range, each
    /// link's function and the quantifier's are elaborated, in that order: whether each link
    /// is `.where` (plan row RANGE-open-walk, `stream_term`).
    Stream(Vec<bool>, Option<Quantifier>),
    /// `split`, `lines` or `concat`, its prim, once its operands are elaborated: the term of
    /// the receiver of `x.w(…)`, which comes first (plan row FP-ops-strings); and
    /// `round(x, ties: …)`, its one operand (plan row CAST-round-whole).
    Strings(Option<Term>, Prim),
    /// `x.zip(y)` once `y` is elaborated: `x`'s term (step L5.2).
    Zip(Term),
    /// A remap once its source and its levels' expressions are elaborated, in that order.
    Remap(&'a Expr),
    /// `k in m` once both are elaborated: whether it is `not in`.
    In(bool),
    /// `a ..< b` or `a ..= b` once both ends are elaborated: whether the high end is
    /// inclusive.
    Range(bool),
    /// `a ..` once its low end is elaborated.
    RangeFrom,
    /// An expression done, by its span: its term's nodes that have no site take this one
    /// (plan row RT-sites).
    Site(Span),
    /// An expression or declaration done that changed the fold identities in force: what
    /// it changed (`identities::Elab::enter_expr`).
    Env(super::identities::Saved),
}

/// Which display a [`Frame::Display`] builds.
#[derive(Clone, Copy)]
enum Display {
    Array,
    Set,
    Map,
}

/// A call that passes atoms ([`Elab::passes`]): its arguments that do, each bound to a
/// temporary, then the call itself.
struct PassF<'a> {
    e: &'a Expr,
    /// Each argument whose atoms may pass, with the atoms that pass.
    args: Vec<(&'a Expr, &'a KType)>,
    lets: Vec<(Arc<str>, Option<Term>)>,
}

/// A scope's statements, run in dependency order.
struct ScopeF<'a> {
    items: Vec<&'a Stmt>,
    /// The statements' order, last first.
    order: Vec<usize>,
    top: bool,
    /// The statement being elaborated, an index into `items`.
    at: usize,
    /// The number of folds left undecided before it ([`super::instances::Instancing::
    /// undecided`]); at the top level, those after are attributed to its bindings.
    undecided: usize,
    binds: Vec<Bind>,
    ok: bool,
    export: Option<&'a [Expr]>,
}

/// A function declaration: its defaults, its body and its tests.
struct FnF<'a> {
    s: &'a Stmt,
    f: &'a Function,
    top: bool,
    id: usize,
    params: Vec<Arc<str>>,
    /// Each parameter's index, by its binder.
    at: HashMap<usize, usize>,
    /// The parameter whose default is next looked at, or being elaborated.
    j: usize,
    /// The parameters the default being elaborated reads.
    reads: Vec<Arc<str>>,
    thunks: Vec<Bind>,
    ok: bool,
    body: Option<Term>,
    /// The number of folds left undecided when the body starts, then the body's own
    /// ([`super::instances::Instancing::undecided`]).
    undecided_from: usize,
    undecided: Vec<Span>,
}

/// A function's test tables, case by case.
struct TestsF<'a> {
    f: &'a Function,
    id: usize,
    /// The case being elaborated.
    i: usize,
    /// The first of `f.given` whose rows do not end before the case: the clause that gives
    /// the case its ports, if its rows hold the case.
    g: usize,
    ok: bool,
}

impl<'a> TestsF<'a> {
    /// The clause `test with p = e, …` of the table that holds the case, if it has one.
    // Complexity tradeoff: a search of `f.given` for each case costs O(cases · tables); the
    // cases come in written order, and so do the clauses, so `g` only moves forward, O(cases +
    // tables) over the function.
    fn clause(&mut self) -> Option<&'a TestPorts> {
        let given = &self.f.given;
        while given.get(self.g).is_some_and(|g| g.rows.end <= self.i) {
            self.g += 1;
        }
        given.get(self.g).filter(|g| g.rows.contains(&self.i))
    }
}

/// The input of [`MAIN_KEY`] a port of a clause gives: `main::files` gives `main::files`, and
/// `main::stdin`, `main::args` and `main::env` their own names. The builder accepts no other
/// field of `main` (on another function's table, only `main::files`), and the resolver no name.
fn main_field(port: &PortName) -> Option<&'static str> {
    match port {
        PortName::Main(f, _) => MAIN_KEY
            .iter()
            .copied()
            .find(|k| k.strip_prefix("main::").unwrap_or(k) == f),
        PortName::Name(..) => None,
    }
}

/// The arguments of a call.
#[derive(Clone, Copy)]
struct Call<'a> {
    positional: &'a [Expr],
    named: &'a [(String, Expr)],
    curry: bool,
    span: Span,
}

/// `x.f(args)` or `x?.f(args)`, waiting for `x`.
struct Member<'a> {
    name: &'a str,
    safe: bool,
    member: Span,
    call: Call<'a>,
    /// Whether `x` is a literal, a value with no fields, so `.f` can only be a call.
    literal: bool,
}

/// The literals of a call that the function called places ([`Elab::placed_call`]): the call's
/// `shape`, as [`Prim::CallNamed`] reads it, and for a curried call `curried`, its result's
/// parameter list `(table, m, q)`: the table [`Prim::Place`] reads, the number `m` of named
/// parameters the call leaves out, and the number `q` of those with a default.
pub(super) struct Placing {
    shape: Value,
    curried: Option<(Value, usize, usize)>,
}

/// The [`Placing`] of a call with `k` arguments by position, a receiver counted, the named
/// arguments `named` in the order written, and for a curried call `left`, the named
/// parameters it leaves out in the order of the function's list, each with whether it has a
/// default. The arguments the call passes are those written, then one for each of `left`,
/// then one flag for each of `left` with a default ([`Elab::placed_call`]).
// Complexity tradeoff: the names are sorted here, once per call written, O((a + l) log (a + l))
// for a named arguments and l left out, so that each run of the call merges them with the
// function's sorted names in O(p + a + l), where a search of the parameter list for each name
// at each run costs O(p·(a + l)).
fn placing(k: usize, named: &[&str], left: Option<&[(&str, bool)]>) -> Placing {
    let given = named.len();
    let mut q = 0;
    let mut names: Vec<(Value, i64, i64)> = (named.iter().enumerate())
        .map(|(i, n)| (Value::str(n), i as i64, -1))
        .collect();
    for (i, &(n, defaulted)) in left.unwrap_or_default().iter().enumerate() {
        let flag = match defaulted {
            true => {
                q += 1;
                q - 1
            }
            false => -1,
        };
        names.push((Value::str(n), (given + i) as i64, flag));
    }
    names.sort_unstable();
    let (mut sorted, mut at, mut opt) = (Vec::new(), Vec::new(), Vec::new());
    for (n, i, flag) in names {
        sorted.push(n);
        at.push(Value::Int(i));
        opt.push(Value::Int(flag));
    }
    let mut shape = vec![Value::Int(k as i64), Value::tuple(sorted), Value::tuple(at)];
    if q > 0 {
        shape.push(Value::tuple(opt));
    }
    let curried = left.map(|left| {
        let mut own: Vec<(Value, usize)> = (left.iter().enumerate())
            .map(|(i, &(n, _))| (Value::str(n), i))
            .collect();
        own.sort_unstable();
        let (own, places): (Vec<Value>, Vec<Value>) = (own.into_iter())
            .map(|(n, i)| (n, Value::Int(i as i64)))
            .unzip();
        let table = Value::tuple(vec![
            Value::Int(left.len() as i64),
            Value::tuple(own),
            Value::tuple(places),
            Value::tuple(left.iter().map(|&(_, d)| Value::Bool(d)).collect()),
        ]);
        (table, left.len(), q as usize)
    });
    Placing {
        shape: Value::tuple(shape),
        curried,
    }
}

/// What a call's arguments fill.
enum Callee<'a> {
    /// A value, with the signature the checker gives it.
    Value(Term, &'a Sig),
    /// A declared function, by its binder.
    Declared(usize, &'a Function),
}

impl<'a> Callee<'a> {
    fn len(&self) -> usize {
        match self {
            Callee::Value(_, sig) => sig.params.len(),
            Callee::Declared(_, f) => f.params.len(),
        }
    }

    /// Parameter `j`'s name and whether it is passed by position.
    fn param(&self, j: usize) -> (&'a str, bool) {
        match *self {
            Callee::Value(_, sig) => (&sig.params[j].name, sig.params[j].positional),
            Callee::Declared(_, f) => (&f.params[j].name, f.params[j].positional),
        }
    }

    /// What the call names, for the repairs of a misfit: a prelude word, a value, or a declared
    /// function, as the checker's `unfit` tells them apart.
    fn called(&self) -> CalledKind {
        match self {
            Callee::Value(_, sig) if sig.word.is_some() => CalledKind::Word,
            Callee::Value(..) => CalledKind::Value,
            Callee::Declared(..) => CalledKind::Declared,
        }
    }

    /// How an error names the function called.
    fn who(&self) -> String {
        match self {
            Callee::Value(_, sig) => sig.who(),
            Callee::Declared(_, f) => f.name.clone(),
        }
    }
}

/// A call's parameters being filled, by its arguments and then by its defaults.
struct FillF<'a> {
    callee: Callee<'a>,
    call: Call<'a>,
    slots: Vec<Option<Term>>,
    /// The next parameter a positional argument fills.
    next: usize,
    /// The next positional argument and the next named one.
    pi: usize,
    ni: usize,
    /// Each parameter's index by name, the first where a name repeats, once a named argument
    /// is met.
    at: Option<HashMap<&'a str, usize>>,
    /// The parameter, or for a declared function's default the index into `missing`, being
    /// filled.
    pending: usize,
    ok: bool,
    /// The parameters left out.
    missing: Vec<usize>,
    /// The defaults left to fill, last first: parameters for a value, indices into `missing`
    /// for a declared function.
    order: Vec<usize>,
    /// A declared function's defaults filled, with the parameters they bind.
    defaults: Vec<(Arc<str>, Term)>,
}

/// A lambda fitted to the function type its slot expects.
struct FitF<'a> {
    params: &'a [Param],
    names: Vec<Arc<str>>,
    extra: &'a [usize],
}

impl<'a> Elab<'a> {
    /// The statements of one scope: its bindings in dependency order, and its export. `top`
    /// is the unit's top level, where a function's `test` table is elaborated.
    pub(super) fn scope(
        &mut self,
        stmts: &'a [Stmt],
        top: bool,
    ) -> Option<(Vec<Bind>, Option<Term>)> {
        let mut m = M {
            stack: vec![Job::Scope(stmts, top)],
            ret: Ret::None,
        };
        self.run(&mut m);
        match m.take() {
            Ret::Scope(s) => s,
            _ => unreachable!("a scope's result"),
        }
    }

    /// The body of the declared function `f` alone, without its defaults and its test
    /// tables, which the declaration's own elaboration made: for a body of its own at the
    /// fold identities `self.inst.env` holds (REDUCE-generic-identity, `instances`).
    pub(super) fn body_term(&mut self, f: &'a Function) -> Option<Term> {
        let mut m = M {
            stack: vec![match &f.body.kind {
                ExprKind::Block(stmts) if !f.equation => Job::Block(stmts),
                _ => Job::Expr(&f.body),
            }],
            ret: Ret::None,
        };
        self.run(&mut m);
        m.t()
    }

    /// The term of the name `n` at `span`. A name of a function (or of a name bound to one,
    /// `Instancing::alias`) that is called, or passed to a call that decides its folds, is the
    /// body made at that call's identities (REDUCE-generic-identity-values,
    /// `Instancing::callee_at`, `Instancing::value_at`); any other name is [`Elab::name`]'s.
    /// Here rather than in `name`, so that state.rs, which holds `Elab`, calls nothing of
    /// identities.rs, which imports it (step S.1f).
    fn named(&mut self, n: &str, span: Span) -> Option<Term> {
        if let Some(Ref::Bound(ids)) = self.t.res.uses.get(&span)
            && ids.len() == 1
        {
            let id = self.target(ids[0]);
            if let Some(at) = self.inst.callee_at.remove(&span) {
                return Some(Term::Var(self.fkernel(id, at)));
            }
            if let Some(at) = self.inst.value_at.remove(&span) {
                let fv = Term::Var(self.value_kernel(id, at));
                return self.placed_value(id, fv, span);
            }
            let fv = self.name(n, span)?;
            return self.placed_value(id, fv, span);
        }
        self.name(n, span)
    }

    /// `fv`, the value of the binder `id`, with the parameter list of the function it is
    /// ([`Elab::place_term`]) where the unit has a call that the function called places, so
    /// that the call finds the list; `fv` alone elsewhere, so a unit without such a call
    /// compiles as before. A use before the function's defaults are elaborated (a cycle of
    /// functions, one used as a value in the other) is refused as not yet built.
    // Complexity tradeoff: each value use of a declared function costs O(p log p) more here
    // for p parameters, and the table is one literal shared by every closure made from it
    // (`Value` is reference-counted), so a closure costs O(1) more.
    fn placed_value(&mut self, id: usize, fv: Term, span: Span) -> Option<Term> {
        let Some(&f) = self.t.funcs.get(&id) else {
            return Some(fv);
        };
        if self.info.placed.is_empty() {
            return Some(fv);
        }
        match self.place_term(id, f, fv) {
            Some(t) => Some(t),
            None => self.error(
                span,
                format!(
                    "`{}` is used as a value before its defaults are built, which this version \
                     of zedc does not yet do. Call `{}` by its name here.",
                    f.name, f.name
                ),
            ),
        }
    }

    /// The term of the expression `e` alone: the lambda of a binding `f = x -> …` made at the
    /// fold identities `self.inst.env` holds (`Elab::instance_body`).
    fn expr_term(&mut self, e: &'a Expr) -> Option<Term> {
        let mut m = M {
            stack: vec![Job::Expr(e)],
            ret: Ret::None,
        };
        self.run(&mut m);
        m.t()
    }

    /// Ends a block whose functions from `mark` on in `inst.locals` are its own: makes the
    /// bodies their calls queued (`Self::fkernel`), and those the bodies' calls queue in turn,
    /// and binds each in the block's bindings `s` after the function's written body. The folds
    /// the bodies leave undecided are the enclosing statement's, and so are the written body's
    /// if a term outside it names it; else the written body is not run, and its folds need no
    /// identity. It is here, not in [`bodies`](super::bodies), since it runs the walk while
    /// the walk runs it: the files' imports form no cycle (step S.1f).
    // Complexity tradeoff: each body costs one elaboration of the function, as for a
    // top-level function; the bodies to make are found by a stack of the functions whose
    // queue is not empty (`inst.pending`), each pushed when its queue fills and popped once,
    // where a scan of the block's functions after each body costs O(bodies × functions). The
    // entries of functions declared around the block are set aside and put back, O(1) each,
    // where a search past them for the block's own would cost O(outer) per body. The bodies
    // are placed in one pass over the bindings with a map from kernel name to function,
    // O(b + l + bodies) for b bindings and l functions, against O(b · l) for a search of the
    // bindings and a splice for each function.
    fn place_locals(
        &mut self,
        mark: usize,
        s: Option<(Vec<Bind>, Option<Term>)>,
    ) -> Option<(Vec<Bind>, Option<Term>)> {
        if self.inst.locals.len() == mark {
            return s;
        }
        // Each index below `mark` was in `pending` before the block started or was pushed by
        // a call in it; those at or above it are the block's own, since `locals` had `mark`
        // entries when the block started.
        let mut outer = Vec::new();
        while let Some(i) = self.inst.pending.pop() {
            if i < mark {
                outer.push(i);
                continue;
            }
            while let Some((kernel, env)) = self.inst.locals[i].queue.pop() {
                let (id, stmt) = (self.inst.locals[i].id, self.inst.locals[i].stmt);
                let (term, sites) = self.instance_body(id, stmt, env);
                self.inst.undecided.extend(sites);
                if let Some(term) = term {
                    self.inst.locals[i].done.push((kernel, term));
                }
            }
        }
        self.inst.pending = outer;
        // A written body named by a run one is run (`Instancing::written_named`); a function
        // declared around the block that one names is named from here.
        let mut todo: Vec<usize> = (mark..self.inst.locals.len())
            .filter(|&i| self.inst.locals[i].used)
            .collect();
        while let Some(j) = todo.pop() {
            for i in mem::take(&mut self.inst.locals[j].names) {
                if i < mark {
                    let id = self.inst.locals[i].id;
                    self.inst.written_named(id);
                } else if !mem::replace(&mut self.inst.locals[i].used, true) {
                    todo.push(i);
                }
            }
        }
        let mine = self.inst.locals.split_off(mark);
        let mut by_kernel: HashMap<Arc<str>, Local<'a>> = HashMap::with_capacity(mine.len());
        for mut l in mine.into_iter().rev() {
            match l.prev {
                Some(p) => self.inst.local_at.insert(l.id, p),
                None => self.inst.local_at.remove(&l.id),
            };
            if l.used {
                self.inst.undecided.append(&mut l.written);
            }
            by_kernel.insert(self.names[l.id].clone(), l);
        }
        let (binds, last) = s?;
        let mut placed = Vec::with_capacity(binds.len());
        for b in binds {
            let Some(mut l) = by_kernel.remove(&b.1) else {
                placed.push(b);
                continue;
            };
            // A written body no term names is dropped: it is never run, and the folds no call
            // decided in it would make `Self::check_instances` refuse every definition that
            // holds the block. `Self::check_dropped` refuses a kept term that names it all the
            // same, which an edge `written_named` missed would give.
            if l.used {
                placed.push(b);
            } else {
                let sites = mem::take(&mut l.written);
                let stmt = l.stmt;
                self.inst.dropped.insert(b.1, Dropped { stmt, sites });
            }
            let name = &self.t.res.binders[l.id].name;
            placed.extend((l.done.into_iter()).map(|(k, t)| (name.to_string(), k, t)));
        }
        assert!(
            by_kernel.is_empty(),
            "a block binds each function it declares"
        );
        Some((placed, last))
    }

    /// The body of the function `id`, declared by `s` or bound by `s` to a lambda, at the
    /// identities `env`, as a lambda, with the folds it left undecided. Each binder of the
    /// function's statement other than the function's own is given a fresh kernel name while its
    /// body is elaborated, as kernel names are unique in the unit (stage `mix` and a default's
    /// `let` rely on it), then given back.
    // Complexity tradeoff: each body costs one elaboration of the function, O(s) for a
    // function of size s, and one search of the binders by start, O(log b); the bodies are
    // as many as the distinct lists of identities the calls decide, at most the calls. The
    // naive form, one copy of the elaborated body with its names renamed by a walk of the
    // term, would cost the same O(s) but must know every form of the kernel that binds a name.
    pub(super) fn instance_body(
        &mut self,
        id: usize,
        s: &'a Stmt,
        env: Env,
    ) -> (Option<Term>, Vec<Span>) {
        // A declared function, or a lambda bound to a name (`Instancing::end_bound`).
        let (f, value) = match &s.kind {
            StmtKind::Function(f) => (Some(f), None),
            StmtKind::Bind { value, .. } => (None, Some(value)),
            _ => unreachable!("an instanced function is a declaration or a binding"),
        };
        if self.inst.by_start.is_empty() {
            let mut by_start: Vec<_> = (self.t.res.binders.iter().enumerate())
                .map(|(i, b)| (b.span.start, b.span.end, i))
                .collect();
            by_start.sort_unstable();
            self.inst.by_start = by_start;
        }
        let lo = (self.inst.by_start).partition_point(|&(start, ..)| start < s.span.start);
        let mut map: HashMap<Arc<str>, Arc<str>> = HashMap::new();
        let mut given_back = Vec::new();
        for k in lo..self.inst.by_start.len() {
            let (start, end, b) = self.inst.by_start[k];
            if start >= s.span.end {
                break;
            }
            if end > s.span.end || b == id {
                continue;
            }
            let fresh: Arc<str> =
                format!("{}@{}", self.t.res.binders[b].name, self.inst.next).into();
            self.inst.next += 1;
            let old = mem::replace(&mut self.names[b], fresh.clone());
            map.insert(old.clone(), fresh);
            given_back.push((b, old));
        }
        let defaults: Vec<(usize, Term)> = (0..f.map_or(0, |f| f.params.len()))
            .filter_map(|j| Some((j, self.defaults.get(&(id, j))?.clone())))
            .collect();
        for (j, t) in &defaults {
            self.defaults.insert((id, *j), renamed(t, &map));
        }
        let reads = mem::take(&mut self.reads);
        // The body's identities came from its call, which took them ([`Self::fkernel`]):
        // no built-in call around the body provides them.
        let outer = mem::replace(&mut self.inst.env, env);
        let pushed = mem::take(&mut self.inst.pushed);
        let opaque = mem::replace(&mut self.inst.opaque, 0);
        let mark = self.inst.undecided.len();
        let term = match (f, value) {
            (Some(f), _) => {
                let body = self.body_term(f);
                let params: Vec<Arc<str>> = (f.params.iter())
                    .map(|p| self.names[self.id(p.span, &p.name)].clone())
                    .collect();
                body.map(|body| Term::Lam(params, Shared::new(body)))
            }
            // The lambda takes the identities of `env`, as a lambda a built-in runs in place
            // takes those of its call.
            (None, Some(value)) => {
                self.inst.in_place.insert(value.span);
                self.expr_term(value)
            }
            (None, None) => unreachable!("a declaration or a binding"),
        };
        let sites = self.inst.undecided.split_off(mark);
        self.inst.env = outer;
        self.inst.pushed = pushed;
        self.inst.opaque = opaque;
        self.reads = reads;
        for (j, t) in defaults {
            self.defaults.insert((id, j), t);
        }
        for (b, old) in given_back {
            self.names[b] = old;
        }
        (term, sites)
    }

    /// Runs the jobs of `m` to the end, leaving the result in `m.ret`.
    fn run(&mut self, m: &mut M<'a>) {
        while let Some(job) = m.stack.pop() {
            match job {
                Job::Expr(e) => {
                    if zed_kernel::sites::recording() {
                        m.k(Frame::Site(e.span));
                    }
                    if !self.info.split_folds.is_empty()
                        && let Some(saved) = self.enter_expr(e)
                    {
                        m.k(Frame::Env(saved));
                    }
                    self.expr(m, e)
                }
                Job::Block(stmts) => {
                    m.k(Frame::Block(self.inst.locals.len()));
                    self.start_scope(m, stmts, false);
                }
                Job::Scope(stmts, top) => self.start_scope(m, stmts, top),
                Job::K(f) => self.resume(m, f),
            }
        }
    }

    fn start_scope(&mut self, m: &mut M<'a>, stmts: &'a [Stmt], top: bool) {
        let (items, export) = Stmt::split_export(stmts);
        let mut order = match self.t.order(&items) {
            Ok(order) => order,
            Err(cycles) => {
                // The checker reports each cycle too, in the same words, and checks the rest of
                // the scope; a unit keeps one copy of each error. Why the two copies are equal
                // in the fields `finish` (elab.rs) compares, span, message, menu and row:
                // the checker's `scope` (zedc-check check/walk.rs) builds `items` as here
                // (each statement but `Return`, `Stmt::bare`), and its `order_around_cycles`
                // and `order` here both run `place` then `cycles` (zedc-resolve topo.rs) on
                // the same `deps`, so both get the same cycles and `cycle_reports` the same
                // reports. The checker passes each through `reject_as_written`, a `Msg` with
                // no fixes and no noted repair, which `Msg::written` gives back with a period
                // added to the headline and an empty menu; `Error::sentence` adds the same
                // period to this copy in `finish`. `reject_as_written` keeps the message and
                // notes as written, with no `$k` replaced (`Ck::named`) and no part laid out
                // (`lay_out`): a headline can quote the program's text (`Tables::header`, the
                // head of an overload, with a default such as `s = "$0"`), and when the checker
                // read that `$0` as a class the two copies differed and both were printed
                // (test `l01_29_diagnostics::overload_cycles::
                // a_dollar_in_the_head_of_an_overload_in_a_cycle_is_quoted_as_written`).
                for report in self.t.cycle_reports(&items, &cycles) {
                    self.errors.push(Error {
                        menu: String::new(),
                        row: report.row,
                        span: report.span,
                        message: report.message,
                        notes: report.notes,
                    });
                }
                m.ret = Ret::Scope(None);
                return;
            }
        };
        order.reverse();
        let sf = ScopeF {
            items,
            order,
            top,
            at: 0,
            undecided: 0,
            binds: Vec::new(),
            ok: true,
            export,
        };
        self.scope_step(m, Box::new(sf));
    }

    fn scope_step(&mut self, m: &mut M<'a>, mut sf: Box<ScopeF<'a>>) {
        if let Some(i) = sf.order.pop() {
            let (s, top) = (sf.items[i], sf.top);
            sf.at = i;
            sf.undecided = self.inst.undecided.len();
            m.k(Frame::Scope(sf));
            self.stmt(m, s, top);
            return;
        }
        match sf.export {
            None => m.ret = Ret::Scope(sf.ok.then(|| (mem::take(&mut sf.binds), None))),
            Some(es) => {
                m.k(Frame::Export(sf));
                m.seq(es.iter().collect(), false);
            }
        }
    }

    fn stmt(&mut self, m: &mut M<'a>, s: &'a Stmt, top: bool) {
        match &s.kind {
            // It binds nothing; step L7.3 reads it from the resolution to drop the log lines.
            StmtKind::UnitAnnot(_) => m.ret = Ret::Stmt(Some(Vec::new())),
            StmtKind::Struct(_)
            | StmtKind::Type(_)
            | StmtKind::Method(_)
            | StmtKind::Import(_)
            | StmtKind::Local(_) => {
                unreachable!("resolve rejects the forms of layer L2")
            }
            StmtKind::Annotated { .. } => {
                unreachable!("a scope holds the declaration of an annotated one, `Stmt::bare`")
            }
            StmtKind::IndexedDef(_)
            | StmtKind::Initial(_)
            | StmtKind::While(_)
            | StmtKind::Until(_)
            | StmtKind::Break => unreachable!("resolve rejects the forms of layer L6"),
            // A call that pushes to a port, its value dropped as `_ = e;` drops it.
            StmtKind::Expr(value) => {
                m.k(Frame::Bind(s));
                m.stack.push(Job::Expr(value));
            }
            StmtKind::Bind { value, targets } => {
                if let [Target::Name(n, _)] = &targets[..]
                    && !self.info.split_folds.is_empty()
                {
                    let id = self.id(s.span, n);
                    // `f = top`: a call of `f` is a call of `top`, which takes a body at the
                    // call's identities, and the binding is not made
                    // (REDUCE-generic-identity-values).
                    if let Some(to) = self.instanced(value) {
                        self.inst.alias.insert(id, to);
                        m.ret = Ret::Stmt(Some(Vec::new()));
                        return;
                    }
                    // `f = x -> top(x)` in a block: its calls decide the folds its written
                    // body leaves undecided, as a block's declared function's do
                    // (`Instancing::end_bound`).
                    if !top && matches!(value.kind, ExprKind::Lambda { .. }) {
                        self.inst.declare_local(id, s);
                    }
                }
                m.k(Frame::Bind(s));
                m.stack.push(Job::Expr(value));
            }
            StmtKind::Function(f) => {
                let id = self.id(s.span, &f.name);
                let mut params = Vec::new();
                for p in &f.params {
                    params.push(self.names[self.id(p.span, &p.name)].clone());
                }
                // A default other than a literal or a name is a definition of its own, `f$x`, a
                // function of the parameters it reads, so a call leaving it out calls it rather
                // than holding a copy of it, and defaults that call functions with defaults stay
                // linear in size. A literal or a name is copied: no copy is captured, the kernel
                // names being unique in the unit.
                // Complexity tradeoff (COMPLEXITY.md F2, F23): the naive form copies the
                // default into every call that leaves it out, exponential in the length of a
                // chain of functions whose defaults call the previous one twice (2.9 million
                // characters at 16). One definition per default keeps the unit linear in
                // size, at the cost of one more definition and one call per use. The reads of
                // the defaults find their parameter in the map `at`, O(1) each, where a search
                // of the parameter list cost O(reads × params); the map costs O(params) memory.
                let at: HashMap<usize, usize> = (f.params.iter().enumerate())
                    .map(|(i, p)| (self.id(p.span, &p.name), i))
                    .collect();
                let ff = FnF {
                    s,
                    f,
                    top,
                    id,
                    params,
                    at,
                    j: 0,
                    reads: Vec::new(),
                    thunks: Vec::new(),
                    ok: true,
                    body: None,
                    undecided_from: 0,
                    undecided: Vec::new(),
                };
                // A function declared in a block takes no fold identity from around it
                // (`identities::Elab::enter_expr`).
                if !top && !self.info.split_folds.is_empty() {
                    let saved = self.clear_env();
                    m.k(Frame::Env(saved));
                    if self.info.split_needs.contains_key(&id) {
                        self.inst.declare_local(id, s);
                    }
                }
                self.fn_default(m, Box::new(ff));
            }
            StmtKind::Push { value, .. } => {
                m.k(Frame::Push(s));
                m.stack.push(Job::Expr(value));
            }
            StmtKind::Return(_) => unreachable!("an export is not a binding"),
        }
    }

    /// The next default of a function declaration, or its body once they are done.
    fn fn_default(&mut self, m: &mut M<'a>, mut ff: Box<FnF<'a>>) {
        let f = ff.f;
        while let Some(p) = f.params.get(ff.j) {
            let Some(d) = &p.default else {
                ff.j += 1;
                continue;
            };
            let read: BTreeSet<usize> = (self.t.uses_in(d.span, &[]).into_iter())
                .filter_map(|b| ff.at.get(&b).copied())
                .collect();
            ff.reads = read.into_iter().map(|i| ff.params[i].clone()).collect();
            m.k(Frame::FnDefault(ff));
            m.stack.push(Job::Expr(d));
            return;
        }
        ff.undecided_from = self.inst.undecided.len();
        m.k(Frame::FnBody(ff));
        m.stack.push(match &f.body.kind {
            ExprKind::Block(stmts) if !f.equation => Job::Block(stmts),
            _ => Job::Expr(&f.body),
        });
    }

    /// The cases of `f`'s `test` tables: a key is the argument, or for a function of several
    /// parameters the tuple of its arguments in declaration order.
    fn tests(&mut self, m: &mut M<'a>, f: &'a Function, id: usize, span: Span, top: bool) {
        if f.tests.is_empty() {
            m.ret = Ret::Tests(true);
            return;
        }
        if !top {
            self.error::<()>(
                span,
                format!(
                    "`{}` has a test table, which belongs to a function at the unit's top level",
                    f.name
                ),
            );
            m.ret = Ret::Tests(false);
            return;
        }
        let tf = TestsF {
            f,
            id,
            i: 0,
            g: 0,
            ok: true,
        };
        self.test_case(m, Box::new(tf));
    }

    /// The next case of a function's test tables.
    fn test_case(&mut self, m: &mut M<'a>, mut tf: Box<TestsF<'a>>) {
        let f = tf.f;
        while let Some((input, _)) = f.tests.get(tf.i) {
            // A row of `main` is keyed by the fields of `MainArgs`, not by the fields its body
            // reads (DESIGN.md sec:syntax_tour, `test`): standard input as a String, or the
            // tuple `(stdin, args, env, files)` of [`MAIN_KEY`], items left off its end empty.
            let args = match (&input.kind, f.params.len()) {
                (ExprKind::Tuple(items), _) if f.main.is_some() => {
                    if items.len() > MAIN_KEY.len() {
                        tf.ok = false;
                        self.error::<()>(
                            input.span,
                            format!(
                                "a test key of `main` is the standard input of the run, as a \
                                 String, or the tuple `(stdin, args, env, files)` of its inputs, \
                                 with the items left off its end empty, and this key has {} \
                                 items",
                                items.len()
                            ),
                        );
                        tf.i += 1;
                        continue;
                    }
                    items.iter().collect()
                }
                _ if f.main.is_some() => vec![input],
                (_, 1) => vec![input],
                (ExprKind::Tuple(items), n) if items.len() == n => items.iter().collect(),
                (_, n) => {
                    tf.ok = false;
                    self.error::<()>(
                        input.span,
                        format!(
                            "a test key of `{}` is the tuple of its {n} arguments",
                            f.name
                        ),
                    );
                    tf.i += 1;
                    continue;
                }
            };
            // A row takes the inputs of `main` its table's clause gives after those of its key
            // (DESIGN.md sec:ports, "A test table gives a port its values"), and an input both
            // give is given twice; the key of another function's row gives none of them.
            let mut args = args;
            if let Some(clause) = tf.clause() {
                let keyed = match f.main {
                    Some(_) => &MAIN_KEY[..args.len()],
                    None => &MAIN_KEY[..0],
                };
                let twice = (clause.ports.iter())
                    .find(|p| main_field(&p.port).is_some_and(|k| keyed.contains(&k)));
                if let Some(p) = twice {
                    tf.ok = false;
                    self.error::<()>(
                        input.span,
                        format!(
                            "this row's key gives `{}`, and so does its table's `test with`; \
                             give it once, in the key or in the clause",
                            p.port
                        ),
                    );
                    tf.i += 1;
                    continue;
                }
                let given = clause
                    .ports
                    .iter()
                    .filter(|p| main_field(&p.port).is_some());
                args.extend(given.map(|p| &p.value));
            }
            m.k(Frame::TestArgs(tf));
            m.seq(args, true);
            return;
        }
        m.ret = Ret::Tests(tf.ok);
    }

    /// The call a row of `f`'s table makes, `callee` applied to `args`, the row's key `input`
    /// elaborated, as a call expression makes it: an argument whose loose atoms the parameter
    /// does not take passes them by (rule 6 of sec:type_resolution), as the checker recorded
    /// for the row's call, which it checks at `input`'s span.
    fn row_call(
        &mut self,
        f: &Function,
        input: &Expr,
        callee: Shared,
        mut args: Vec<Term>,
    ) -> Term {
        let info = self.info;
        let Some(at) = info.passes.get(&input.span) else {
            return Term::App(callee, args);
        };
        let spans: Vec<Span> = match (&input.kind, f.params.len()) {
            (ExprKind::Tuple(items), n) if n != 1 => items.iter().map(|e| e.span).collect(),
            _ => vec![input.span],
        };
        let mut lets = Vec::with_capacity(at.len());
        let mut ks = Vec::with_capacity(at.len());
        for (a, s) in args.iter_mut().zip(&spans) {
            if let Some(k) = at.get(s) {
                let t = self.temp();
                lets.push((t.clone(), std::mem::replace(a, Term::Var(t))));
                ks.push(k);
            }
        }
        self.guard(lets, ks.into_iter(), Term::App(callee, args))
    }

    fn expr(&mut self, m: &mut M<'a>, e: &'a Expr) {
        if let Some(t) = self.passing.get(&e.span) {
            m.give(Some(Term::Var(t.clone())));
            return;
        }
        let info = self.info;
        if let Some(at) = info.passes.get(&e.span)
            && self.guarding.insert(e.span)
        {
            self.passes(m, e, at);
            return;
        }
        match info.fits.get(&e.span) {
            // A call of literal values read at a carrier: the call, then its value cast,
            // which the checker proved exact for each value the call gives.
            Some(Fit::Read(c)) => {
                if self.reading.insert(e.span) {
                    let p = match c {
                        check::ty::Carrier::Rat => Prim::CastRat,
                        check::ty::Carrier::F32 => Prim::CastF32,
                        _ => Prim::CastF64,
                    };
                    m.k(Frame::Read(e.span, p));
                    m.stack.push(Job::Expr(e));
                    return;
                }
            }
            // A value passed where a type holding a partial function type is expected: the
            // value, then rebuilt so that each function it holds there tests its domain.
            Some(Fit::Coerce(c)) => {
                if self.coercing.insert(e.span) {
                    m.k(Frame::Coerce(e.span, c));
                    m.stack.push(Job::Expr(e));
                    return;
                }
            }
            Some(fit) => {
                self.fit(m, e, fit);
                return;
            }
            None => {}
        }
        if let Some(s) = lit_span(e)
            && let Some(w) = info.witness.get(&s)
            && self.guarding.insert(s)
        {
            m.k(Frame::Witness(s, w));
            m.stack.push(Job::Expr(e));
            return;
        }
        if let Some(v) = info.adopt.get(&e.span) {
            let t = self.constant(e, v.clone());
            m.give(Some(t));
            return;
        }
        let lit = |v: Value| Some(Term::Lit(v));
        let t = match &e.kind {
            ExprKind::Record(_)
            | ExprKind::With { .. }
            | ExprKind::This
            | ExprKind::Match { .. } => {
                unreachable!("resolve rejects the forms of layer L2")
            }
            ExprKind::Read { .. } | ExprKind::For { .. } => {
                unreachable!("resolve rejects the forms of layer L3 not built yet")
            }
            ExprKind::Range(from, to) => {
                let (hi, through) = match to {
                    RangeEnd::Below(b) => (b, false),
                    RangeEnd::Through(b) => (b, true),
                    // `a ..`, which resolution admits only where a key, `in` or `.first` reads
                    // it: `rangeFrom(a)`, kept as its low end (plan row RANGE-open).
                    RangeEnd::Open => {
                        m.k(Frame::RangeFrom);
                        m.seq(vec![&**from], false);
                        return;
                    }
                };
                m.k(Frame::Range(through));
                m.seq(vec![&**from, &**hi], false);
                return;
            }
            // A section outside `><` is the lambda it stands for (`ExprKind::Section`).
            ExprKind::Section(_, lambda) => {
                m.stack.push(Job::Expr(lambda));
                return;
            }
            ExprKind::Remap { of, levels, .. } => {
                // `as` alone only names the levels: the remap is its source.
                if levels.as_ref().is_none_or(|l| l.is_empty()) {
                    m.stack.push(Job::Expr(of));
                    return;
                }
                // Without a plan the checker has rejected the remap, at its error.
                if !self.info.remaps.contains_key(&e.span) {
                    m.give(None);
                    return;
                }
                let keys = levels.iter().flatten().filter_map(|l| l.key.as_ref());
                m.k(Frame::Remap(e));
                m.seq([&**of].into_iter().chain(keys).collect(), false);
                return;
            }
            ExprKind::Array(items) => {
                m.k(Frame::Display(Display::Array));
                m.seq(items.iter().collect(), false);
                return;
            }
            ExprKind::Set(items) => {
                m.k(Frame::Display(Display::Set));
                m.seq(items.iter().collect(), false);
                return;
            }
            ExprKind::Map(entries) => {
                m.k(Frame::Display(Display::Map));
                m.seq(entries.iter().flat_map(|(k, v)| [k, v]).collect(), false);
                return;
            }
            ExprKind::Reduce { of, op } => {
                // The checker rejects a fold by any other operator, at its error.
                let Some(p) = self.reducer_prim(op, e.span) else {
                    m.give(None);
                    return;
                };
                m.k(Frame::Fold(p, e.span));
                m.stack.push(Job::Expr(of));
                return;
            }
            ExprKind::In { of, set, negated } => {
                m.k(Frame::In(*negated));
                m.seq(vec![&**of, &**set], false);
                return;
            }
            ExprKind::SortKey { .. } => unreachable!("resolve rejects the forms of layer L5"),
            ExprKind::Loop { .. } | ExprKind::Spread { .. } => {
                unreachable!("resolve rejects the forms of layer L6")
            }
            // The lexer has removed the `_` from a literal's digits, so they are read where they
            // are, not copied.
            ExprKind::Int { radix, digits, .. } => match Value::int_text(digits, *radix) {
                Ok(v) => Some(self.constant(e, v.expect("the lexer's digits"))),
                Err(r) => self.error(e.span, unread_literal(&r, "int")),
            },
            // A literal with the suffix `f32` is read at `f32`; any other at `f64`, the format a
            // decimal no use fixes takes (DESIGN.md L1.26a).
            // Only the AST builder makes an `ExprKind::Float`, from the lexer's `Tok::Float`,
            // whose digits are always a decimal (`literal_f64`; tested by zed-kernel's
            // `the_lexer_s_float_and_decimal_forms_are_read`).
            ExprKind::Float { digits: s, forced } => match Value::literal_float(s, *forced)
                .expect("the lexer's float text is a decimal")
            {
                Ok(v) => Some(self.constant(e, v)),
                // Without a suffix the literal could have taken `rat`, where it is exact
                // (DESIGN.md L1.26b), and it is reported here where it stayed at `f64`, as in
                // `t() = 1e400;`, also when the checker rejected the unit elsewhere, so both
                // errors come in one compilation (MSG-range-error-not-hidden). It is not
                // reported again inside the span of a checker's error, where the checker has
                // reported it where it decided its carrier, as in `h(1e400)` at an `f64`
                // parameter, or rejected an expression around it, where its carrier may not be
                // decided; nor at a literal of a class the checker reported at another of its
                // literals, as `y = 1e400 + 1e400` at the first (with the fix
                // `1e400r + 1e400`), while a literal of another class in the same statement keeps
                // its range error (MSG-range-error-class-spans). The term stands in and is never
                // run.
                Err(LiteralRounding::Infinite | LiteralRounding::Zero)
                    if forced.is_none() && self.in_checker_error(e.span) =>
                {
                    lit(Value::float(f64::INFINITY))
                }
                Err(r @ (LiteralRounding::Infinite | LiteralRounding::Zero)) => {
                    self.error(e.span, check::float_range(s, *forced, &r))
                }
                Err(LiteralRounding::TooLarge(_)) => {
                    unreachable!("a float literal is read with no memory asked for")
                }
            },
            ExprKind::Rat(s) => match Rat::decimal(s) {
                Ok(r) => {
                    let v = Value::rat(r.expect("the lexer's rat text is a decimal"));
                    Some(self.constant(e, v))
                }
                Err(r) => self.error(e.span, unread_literal(&r, "rat")),
            },
            ExprKind::Bool(b) => lit(Value::Bool(*b)),
            ExprKind::Atom(a) => lit(Value::atom(a)),
            ExprKind::Str(parts) => {
                let holes = parts.iter().filter_map(|p| match p {
                    StrPart::Hole(h) => Some(h),
                    StrPart::Text(_) => None,
                });
                m.k(Frame::Str(parts));
                m.seq(holes.collect(), true);
                return;
            }
            ExprKind::Name(n) => self.named(n, e.span),
            ExprKind::Unary(op, a) => {
                let p = match op {
                    UnaryOp::Neg => Prim::Neg,
                    UnaryOp::Not => Prim::Not,
                };
                m.k(Frame::Unary(p, e));
                m.stack.push(Job::Expr(a));
                return;
            }
            ExprKind::Binary(_, l, r) => {
                m.k(Frame::Binary(e));
                m.seq(vec![l, r], false);
                return;
            }
            ExprKind::Call {
                callee,
                positional,
                named,
                curry,
                ..
            } => {
                let call = Call {
                    positional,
                    named,
                    curry: *curry,
                    span: e.span,
                };
                self.call(m, callee, call);
                return;
            }
            ExprKind::Index(of, k) => {
                match self.declared(of) {
                    Some(id) => {
                        m.k(Frame::IndexDeclared(id, of, e.span));
                        m.stack.push(Job::Expr(k));
                    }
                    None => {
                        m.k(Frame::Index(k, e.span));
                        m.seq(vec![of, k], false);
                    }
                }
                return;
            }
            ExprKind::Tuple(items) => {
                m.k(Frame::Tuple);
                m.seq(items.iter().collect(), false);
                return;
            }
            ExprKind::Lambda { params, body } => {
                let mut names = Vec::new();
                for p in params {
                    if let Some(d) = &p.default {
                        let t = self.error(
                            d.span,
                            "a lambda's parameter has a default only where an expected \
                             function type leaves it out",
                        );
                        m.give(t);
                        return;
                    }
                    names.push(self.names[self.id(p.span, &p.name)].clone());
                }
                m.k(Frame::Lambda(names));
                m.body(body);
                return;
            }
            ExprKind::Is { of, .. } => {
                m.k(Frame::Is(e));
                m.stack.push(Job::Expr(of));
                return;
            }
            ExprKind::Else { of, default, .. } => {
                m.k(Frame::Else(e));
                m.seq(vec![of, default], false);
                return;
            }
            ExprKind::Block(stmts) => {
                m.stack.push(Job::Block(stmts));
                return;
            }
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                m.k(Frame::If(e));
                m.seq(vec![cond, then, otherwise], false);
                return;
            }
            ExprKind::Member { of, name, safe } => {
                let call = Call {
                    positional: &[],
                    named: &[],
                    curry: false,
                    span: e.span,
                };
                self.member(m, of, name, *safe, e.span, call);
                return;
            }
        };
        m.give(t);
    }

    /// The call `e`, some of whose arguments, at `at`, hold loose atoms their parameter does not
    /// take (rule 6 of sec:type_resolution): the arguments are bound first, and an atom in any
    /// of them is the call's value, those of several merged as a primitive merges them.
    fn passes(&mut self, m: &mut M<'a>, e: &'a Expr, at: &'a HashMap<Span, KType>) {
        let mut args: Vec<&'a Expr> = Vec::new();
        if let ExprKind::Call {
            callee,
            positional,
            named,
            ..
        } = &e.kind
        {
            if let ExprKind::Member { of, .. } = &callee.kind {
                args.push(of);
            }
            args.extend(positional);
            args.extend(named.iter().map(|(_, a)| a));
        }
        let args = args
            .into_iter()
            .filter_map(|a| at.get(&a.span).map(|k| (a, k)))
            .collect();
        let pf = PassF {
            e,
            args,
            lets: Vec::new(),
        };
        self.pass_step(m, Box::new(pf));
    }

    fn pass_step(&mut self, m: &mut M<'a>, mut pf: Box<PassF<'a>>) {
        match pf.args.get(pf.lets.len()) {
            Some(&(a, _)) => {
                let t = self.temp();
                pf.lets.push((t, None));
                m.k(Frame::Pass(pf));
                m.stack.push(Job::Expr(a));
            }
            None => {
                let e = pf.e;
                m.k(Frame::PassCall(pf));
                m.stack.push(Job::Expr(e));
            }
        }
    }

    /// The call of [`Elab::passes`], its arguments bound.
    fn pass_end(&mut self, pf: PassF<'a>, call: Option<Term>) -> Option<Term> {
        for (a, _) in &pf.args {
            self.passing.remove(&a.span);
        }
        let call = call?;
        let lets: Vec<(Arc<str>, Term)> = pf
            .lets
            .into_iter()
            .map(|(t, x)| x.map(|x| (t, x)))
            .collect::<Option<_>>()?;
        Some(self.guard(lets, pf.args.iter().map(|&(_, k)| k), call))
    }

    /// `call`, whose arguments that pass atoms are bound as `lets`, each paired in order with
    /// the atoms of `ks` that pass: an atom in any of them is the value, those of several
    /// merged as a primitive merges them, and otherwise `call` runs.
    fn guard<'k>(
        &mut self,
        lets: Vec<(Arc<str>, Term)>,
        ks: impl Iterator<Item = &'k KType>,
        mut call: Term,
    ) -> Term {
        let v = |n: &Arc<str>| Term::Var(n.clone());
        // An argument whose atoms pass only in part (rule 6 treats each region apart): its
        // failure is the argument when it is one of those atoms, and otherwise `false`, which
        // no merge below takes for an atom.
        let mut merges = Vec::new();
        let mut fails = Vec::with_capacity(lets.len());
        for ((t, _), k) in lets.iter().zip(ks) {
            if *k == check::ty::atoms() {
                fails.push(t.clone());
                continue;
            }
            let g = self.temp();
            let own = Term::Match(
                Shared::new(v(t)),
                vec![
                    (KPattern::Is(k.clone()), v(t)),
                    (KPattern::Wild, Term::Lit(Value::Bool(false))),
                ],
            );
            merges.push((g.clone(), own));
            fails.push(g);
        }
        // Each argument's failure merged with those before it, each merge bound after the
        // arguments.
        let mut fail: Option<Arc<str>> = None;
        for t in &fails {
            fail = Some(match fail {
                None => t.clone(),
                Some(f) => {
                    let g = self.temp();
                    let both = Term::Match(
                        Shared::new(v(&f)),
                        vec![
                            (KPattern::AnyAtom, Term::Prim(Prim::Add, vec![v(&f), v(t)])),
                            (KPattern::Wild, v(t)),
                        ],
                    );
                    let merged = Term::Match(
                        Shared::new(v(t)),
                        vec![(KPattern::AnyAtom, both), (KPattern::Wild, v(&f))],
                    );
                    merges.push((g.clone(), merged));
                    g
                }
            });
        }
        if let Some(f) = fail {
            call = Term::Match(
                Shared::new(v(&f)),
                vec![(KPattern::AnyAtom, v(&f)), (KPattern::Wild, call)],
            );
        }
        lets.into_iter()
            .chain(merges)
            .rev()
            .fold(call, |body, (t, x)| {
                Term::Let(t, Shared::new(x), Shared::new(body))
            })
    }

    fn call(&mut self, m: &mut M<'a>, callee: &'a Expr, call: Call<'a>) {
        if let ExprKind::Member { of, name, safe } = &callee.kind {
            self.member(m, of, name, *safe, callee.span, call);
            return;
        }
        if let ExprKind::Atom(name) = &callee.kind {
            self.atom(m, name, call);
            return;
        }
        // `sum(x)` is `x.sum` (DESIGN.md sec:lexical, the row of `.`); where the checker took
        // it as the method's check (`Ck::word_applied`), it is elaborated as the method is.
        if let ExprKind::Name(n) = &callee.kind
            && n == "sum"
            && let [x] = call.positional
            && call.named.is_empty()
            && !call.curry
            && (self.info.generic_sums.contains(&call.span)
                || self.info.family_sums.contains(&call.span))
        {
            let call = Call {
                positional: &[],
                ..call
            };
            self.member(m, x, n, false, callee.span, call);
            return;
        }
        if let Some(id) = self.declared(callee) {
            let f = self.t.funcs[&id];
            self.call_with(m, Callee::Declared(id, f), None, call);
            return;
        }
        // `round(x, ties: #away)` is the primitive `RoundTiesAway` and `round(x, ties: #even)`
        // is `round(x)` (DESIGN.md sec:facets, "Rounding to a whole number"); the checker
        // rejected `ties:` given anything but one of the two atoms written in place.
        if let ExprKind::Name(n) = &callee.kind
            && n == "round"
            && matches!(self.t.res.uses.get(&callee.span), Some(Ref::Prelude(_)))
            && let [x] = call.positional
            && let [(t, rule)] = call.named
            && t == "ties"
            && !call.curry
            && let ExprKind::Atom(rule) = &rule.kind
        {
            let p = match rule.as_str() {
                "away" => Prim::RoundTiesAway,
                _ => Prim::Round,
            };
            m.k(Frame::Strings(None, p));
            m.seq(vec![x], false);
            return;
        }
        // `split(s, sep)`, `lines(s)` and `concat(pieces, sep: s)` where the name is the
        // prelude's (plan row FP-ops-strings), built in as `map` is.
        if let ExprKind::Name(n) = &callee.kind
            && let Some(p) = fp_ops::strings_prim(n)
            && matches!(self.t.res.uses.get(&callee.span), Some(Ref::Prelude(_)))
        {
            self.strings(m, None, p, call);
            return;
        }
        // A lambda bound in a block takes the body made at this call's identities
        // (`Elab::name`).
        if self.instanced(callee).is_some() {
            self.inst.callee_at.insert(callee.span, call.span);
        }
        m.k(Frame::CallOf(call));
        m.stack.push(Job::Expr(callee));
    }

    /// `split`, `lines` or `concat`, the prim `p`, with `receiver` the term of `x` in
    /// `x.w(…)`: the operands by position, then `sep` by name ([`Frame::Strings`]). The checker
    /// rejected any other shape, so none reaches here; one that does gives no term.
    fn strings(&mut self, m: &mut M<'a>, receiver: Option<Term>, p: Prim, call: Call<'a>) {
        let given = usize::from(receiver.is_some()) + call.positional.len();
        let fits = !call.curry
            && match p {
                Prim::Split => given == 2 && call.named.is_empty(),
                Prim::Lines => given == 1 && call.named.is_empty(),
                _ => {
                    given == 1
                        && call.named.iter().all(|(n, _)| n == "sep")
                        && call.named.len() <= 1
                }
            };
        if !fits {
            m.give(None);
            return;
        }
        let exprs = (call.positional.iter())
            .chain(call.named.iter().map(|(_, e)| e))
            .collect();
        m.k(Frame::Strings(receiver, p));
        m.seq(exprs, false);
    }

    /// An atom with a payload, `#name(a, b)` by position or `#name(f: a)` by name.
    fn atom(&mut self, m: &mut M<'a>, name: &'a str, call: Call<'a>) {
        let Call {
            positional,
            named,
            curry,
            span,
        } = call;
        if curry {
            let t = self.error(
                span,
                "`...` leaves a function's other named parameters open, and an atom has no \
                 parameters to leave open. Remove the `...`.",
            );
            m.give(t);
            return;
        }
        if !positional.is_empty() && !named.is_empty() {
            let t = self.error(
                span,
                "this atom's payload gives some values by position and some by name, and a \
                 payload is given all by position or all by name. Write every value by position, \
                 or every value with its name.",
            );
            m.give(t);
            return;
        }
        let args = positional.iter().chain(named.iter().map(|(_, a)| a));
        m.k(Frame::AtomArgs(name, named));
        m.seq(args.collect(), false);
    }

    /// A call through a value other than a declared function. With the signature the
    /// checker gives the value, named arguments, closed defaults and `...` work as for a
    /// declared function; without one, the arguments are positional.
    fn call_value(&mut self, m: &mut M<'a>, f: Term, receiver: Option<Term>, call: Call<'a>) {
        let info = self.info;
        // A family whose keys are one integer interval applied to keys is the read of one
        // level per key, each missing with `#outOfBounds` (the checker's verdict at the call,
        // given only where every level is such a family; row KERNEL-family-call): `sq(n)` is
        // written as `sq[n]` is ([`Frame::Index`]), and `g(i, j)` as `g[i][j]`.
        if let (None, [k, rest @ ..], true, false) = (
            &receiver,
            call.positional,
            call.named.is_empty(),
            call.curry,
        ) && info.dense.get(&call.span) == Some(&true)
        {
            m.k(Frame::AtArg(f, rest));
            return m.stack.push(Job::Expr(k));
        }
        let Some(sig) = info.calls.get(&call.span) else {
            if !call.named.is_empty() || call.curry {
                let t = self.error(
                    call.span,
                    "named arguments and `...` need the parameter names of the function \
                     called, which a prelude word and a value of unknown type do not give",
                );
                m.give(t);
                return;
            }
            m.k(Frame::ValueArgs(f, receiver));
            m.seq(call.positional.iter().collect(), false);
            return;
        };
        // A curried call's result may reach a call that the function called places, in a unit
        // with one, so it carries its own list there (row CALL-curried-placed). The function
        // it calls has a list too: a declared function used as a value has one in such a unit
        // ([`Self::placed_value`]), and so does a curried call's result; a lambda's parameters
        // are positional, so no curried call names them, and a prelude word gives no names.
        if info.placed.contains(&call.span) || (call.curry && !info.placed.is_empty()) {
            return self.placed_call(m, f, receiver, call, sig);
        }
        self.call_with(m, Callee::Value(f, sig), receiver, call);
    }

    /// A call through a value that the function the value holds places when the call runs
    /// (DESIGN.md sec:values_morphisms, "The function called places the arguments";
    /// `check::Info::placed`): `callNamed(shape, f, args…)`, the arguments as written, the
    /// positional ones first, then the named ones in the order written, each evaluated in
    /// that order. `shape` is `(k, names, at)`: the number of positional arguments, the
    /// receiver counted, the names sorted, and the index among the named arguments of each
    /// sorted name, as [`Prim::CallNamed`] reads it.
    ///
    /// A curried call (`...`) gives the function of the named parameters that the function
    /// held leaves out, with that function's defaults (row CALL-curried-placed): those of
    /// `sig`, the signature the checker records for the call, that it does not fill, in `sig`'s
    /// order, `l…`. Its value is `place(table, l… -> callNamed(shape, f, args…, l…))`, its own
    /// list `table` naming the `l…`, so that a call of it is placed by its names too. Where
    /// some of the `l…` have a default, it is `place(table, l… -> fill(l…, false…), fill)`
    /// with `fill(l…, d…) = callNamed(shape, f, args…, l…, d…)`: `shape`'s `opt` gives each
    /// defaulted `l` its flag `d`, so that a call of the result that leaves `l` out leaves it
    /// out of the call of `f` too, which fills it with its own default.
    ///
    /// Why the function held fills them, and not the result: every function the value may hold
    /// takes the names the result takes (the checker checks each), but each may fill a name
    /// left out with its own default, or take more parameters that the call leaves out; the
    /// names alone, passed on, say which. `sig` gives only which names the result takes, the
    /// same for every such function, and which have a default (a call of the result leaving
    /// out one with none in `sig` is refused, as it is for the function of `sig`).
    // Complexity tradeoff: the names given are a set, O(a) to build, so finding those left out
    // is O(p), where a search of the call's names for each parameter is O(p·a); [`placing`]
    // sorts the names once per call written.
    fn placed_call(
        &mut self,
        m: &mut M<'a>,
        f: Term,
        receiver: Option<Term>,
        call: Call<'a>,
        sig: &Sig,
    ) {
        let k = usize::from(receiver.is_some()) + call.positional.len();
        let named: Vec<&str> = call.named.iter().map(|(n, _)| n.as_str()).collect();
        // The parameters left out, each with whether it has a default.
        let left: Option<Vec<(&str, bool)>> = call.curry.then(|| {
            let given: HashSet<&str> = named.iter().copied().collect();
            (sig.params.iter().skip(k))
                .filter(|p| !given.contains(&*p.name))
                .map(|p| (&*p.name, p.default.is_some()))
                .collect()
        });
        let placing = placing(k, &named, left.as_deref());
        m.k(Frame::PlacedArgs(f, receiver, Box::new(placing)));
        let args = (call.positional.iter()).chain(call.named.iter().map(|(_, e)| e));
        m.seq(args.collect(), false);
    }

    /// The term of a call [`Self::placed_call`] began, once its arguments `ts` are
    /// elaborated: `callNamed(shape, f, receiver?, ts…)`, or for a curried call its result.
    // Complexity: O(a + l) terms for a arguments and l parameters left out.
    fn placed_args(
        &mut self,
        f: Term,
        receiver: Option<Term>,
        placing: Placing,
        ts: Vec<Term>,
    ) -> Term {
        let Placing { shape, curried } = placing;
        let mut args = vec![Term::Lit(shape)];
        let Some((table, l, q)) = curried else {
            args.push(f);
            args.extend(receiver);
            args.extend(ts);
            return Term::Prim(Prim::CallNamed, args);
        };
        // The function value is bound once, outside the result's lambda, as the curried call
        // through `Callee::Value` binds it.
        let fv = self.temp();
        let ls: Vec<Arc<str>> = (0..l).map(|_| self.temp()).collect();
        let ds: Vec<Arc<str>> = (0..q).map(|_| self.temp()).collect();
        let var = |x: &Arc<str>| Term::Var(x.clone());
        args.push(Term::Var(fv.clone()));
        args.extend(receiver);
        args.extend(ts);
        args.extend(ls.iter().map(var));
        args.extend(ds.iter().map(var));
        let call = Term::Prim(Prim::CallNamed, args);
        let table = Term::Lit(table);
        let result = match q {
            0 => Term::Prim(Prim::Place, vec![table, Term::Lam(ls, Shared::new(call))]),
            _ => {
                let fill = self.temp();
                let mut pass: Vec<Term> = ls.iter().map(var).collect();
                pass.extend((0..q).map(|_| Term::Lit(Value::Bool(false))));
                let own = Term::App(Shared::new(Term::Var(fill.clone())), pass);
                let mut params = ls.clone();
                params.extend(ds);
                let place = Term::Prim(
                    Prim::Place,
                    vec![
                        table,
                        Term::Lam(ls, Shared::new(own)),
                        Term::Var(fill.clone()),
                    ],
                );
                let fill_lam = Term::Lam(params, Shared::new(call));
                Term::Let(fill, Shared::new(fill_lam), Shared::new(place))
            }
        };
        Term::Let(fv, Shared::new(f), Shared::new(result))
    }

    /// The value of the declared function `id` with its parameter list, `place(table, f)` or
    /// `place(table, f, fill)` ([`Prim::Place`]), where `fv` is the function: in a unit with
    /// a call that the function called places, each declared function used as a value is
    /// this (`check::Info::placed`). `table` is `(p, names, places, defaulted)`, the names
    /// sorted; `fill` takes the parameters, then one flag for each defaulted parameter, true
    /// where the call leaves it out, and fills each such parameter in declaration order with
    /// its default as a call of `f` by its name fills it, then calls `fv`. None while a
    /// default is not yet elaborated: in the default itself.
    // Complexity tradeoff: O(p log p) for p parameters, once per function, to sort the names;
    // the fill holds each default's term as a call by name holds it (a literal, a name, or a
    // call of the default's own definition), so it is O(p) in size.
    pub(super) fn place_term(&mut self, id: usize, f: &'a Function, fv: Term) -> Option<Term> {
        let n = f.params.len();
        let mut names: Vec<(Value, usize)> = (f.params.iter().enumerate())
            .map(|(j, p)| (Value::str(&p.name), j))
            .collect();
        names.sort_unstable();
        let (names, places): (Vec<Value>, Vec<Value>) = (names.into_iter())
            .map(|(x, j)| (x, Value::Int(j as i64)))
            .unzip();
        let defaulted: Vec<bool> = f.params.iter().map(|p| p.default.is_some()).collect();
        let table = Value::tuple(vec![
            Value::Int(n as i64),
            Value::tuple(names),
            Value::tuple(places),
            Value::tuple(defaulted.iter().map(|&d| Value::Bool(d)).collect()),
        ]);
        let mut args = vec![Term::Lit(table), fv.clone()];
        if defaulted.contains(&true) {
            let mut params: Vec<Arc<str>> = f.params.iter().map(|p| self.kname(p)).collect();
            // The defaulted parameters, each after the defaulted ones its default reads, as
            // `declared_defaults` orders those a call by name leaves out: an order of all of
            // them is one of any subset, since a parameter given keeps its value. The flags
            // are the lambda's parameters in declaration order; a cycle leaves that order,
            // and a call that leaves out every parameter of the cycle reads one unfilled.
            let ds: Vec<usize> = (0..n).filter(|&j| defaulted[j]).collect();
            let at: HashMap<usize, usize> = (ds.iter().enumerate())
                .map(|(i, &j)| (self.id(f.params[j].span, &f.params[j].name), i))
                .collect();
            let deps: Vec<Vec<usize>> = (ds.iter())
                .map(|&j| {
                    let d = f.params[j].default.as_ref().expect("defaulted");
                    let mut deps: Vec<usize> = (self.t.uses_in(d.span, &[]).into_iter())
                        .filter_map(|b| at.get(&b).copied())
                        .collect();
                    zed_collections::sorted::sort_dedup(&mut deps);
                    deps
                })
                .collect();
            let order = topo(&deps).unwrap_or_else(|_| (0..ds.len()).collect());
            let flags: Vec<Arc<str>> = ds.iter().map(|_| self.temp()).collect();
            let mut fills = Vec::new();
            for i in order {
                let j = ds[i];
                let d = self.defaults.get(&(id, j))?.clone();
                fills.push((self.kname(&f.params[j]), flags[i].clone(), d));
            }
            params.extend(flags);
            let call = Term::App(Shared::new(fv), self.param_vars(f));
            let body = fills.into_iter().rev().fold(call, |body, (x, flag, d)| {
                let kept = Term::Var(x.clone());
                let filled = Term::If(
                    Shared::new(Term::Var(flag)),
                    Shared::new(d),
                    Shared::new(kept),
                );
                Term::Let(x, Shared::new(filled), Shared::new(body))
            });
            args.push(Term::Lam(params, Shared::new(body)));
        }
        Some(Term::Prim(Prim::Place, args))
    }

    /// A call of `callee`, a value with a signature or a declared function; `receiver` fills
    /// its first parameter, of either kind.
    fn call_with(
        &mut self,
        m: &mut M<'a>,
        callee: Callee<'a>,
        receiver: Option<Term>,
        call: Call<'a>,
    ) {
        let n = callee.len();
        let mut slots: Vec<Option<Term>> = vec![None; n];
        let mut next = 0;
        if let Some(r) = receiver {
            if n == 0 {
                let who = callee.who();
                let t = self.misfit(call.span, Misfit::NoReceiver, &who, callee.called());
                m.give(t);
                return;
            }
            slots[0] = Some(r);
            next = 1;
        }
        let ff = FillF {
            callee,
            call,
            slots,
            next,
            pi: 0,
            ni: 0,
            at: None,
            pending: 0,
            ok: true,
            missing: Vec::new(),
            order: Vec::new(),
            defaults: Vec::new(),
        };
        self.fill(m, Box::new(ff));
    }

    /// In a marked elaboration, where the argument `a` filling parameter `j` of `callee` is a
    /// numeric literal under at most one `-`, the range the parameter is declared with and its
    /// type in each arrow, for the mark of the literal ([`Slot`], plan row
    /// TESTS-L25.8-neighbors). `j` indexes the declared parameters, which the signature's
    /// parameters follow in order. An ordinary elaboration keeps nothing. O(arrows) clones of
    /// a type, each O(1) or its size, per such argument.
    fn note_slot(&mut self, callee: &Callee<'a>, j: usize, a: &Expr) {
        if self.marks.is_none() {
            return;
        }
        let (inner, neg) = match &a.kind {
            ExprKind::Unary(UnaryOp::Neg, x) => (&**x, true),
            _ => (a, false),
        };
        if !numeric(inner) {
            return;
        }
        let sig: &Sig = match *callee {
            Callee::Value(_, sig) => sig,
            Callee::Declared(id, _) => match self.info.sigs.get(&id) {
                Some(sig) => sig,
                None => return,
            },
        };
        let Some(param) = sig.params.get(j) else {
            return;
        };
        let range = (param.range.as_ref()).and_then(|r| r.int()).cloned();
        let tys: Option<Arc<[_]>> = (sig.arrows.iter())
            .map(|arrow| arrow.params.get(j).cloned())
            .collect();
        if let Some(tys) = tys {
            self.slots.insert(inner.span, Slot { range, tys, neg });
        }
    }

    /// The next argument of a call, or what follows once they are all elaborated.
    fn fill(&mut self, m: &mut M<'a>, mut ff: Box<FillF<'a>>) {
        let n = ff.callee.len();
        if let Some(a) = ff.call.positional.get(ff.pi) {
            let t = if ff.next >= n {
                let who = ff.callee.who();
                self.misfit(a.span, Misfit::TooMany(n), &who, ff.callee.called())
            } else if let (name, false) = ff.callee.param(ff.next) {
                let who = ff.callee.who();
                self.misfit(a.span, Misfit::Named(name), &who, ff.callee.called())
            } else {
                self.note_slot(&ff.callee, ff.next, a);
                ff.pending = ff.next;
                ff.next += 1;
                ff.pi += 1;
                m.k(Frame::Fill(ff));
                m.stack.push(Job::Expr(a));
                return;
            };
            m.give(t);
            return;
        }
        if let Some((name, a)) = ff.call.named.get(ff.ni) {
            let callee = &ff.callee;
            let at = ff
                .at
                .get_or_insert_with(|| (0..n).rev().map(|j| (callee.param(j).0, j)).collect());
            let t = match at.get(name.as_str()).copied() {
                None => {
                    let who = ff.callee.who();
                    self.misfit(a.span, Misfit::NoParam(name), &who, ff.callee.called())
                }
                Some(j) if ff.callee.param(j).1 => {
                    let who = ff.callee.who();
                    self.misfit(a.span, Misfit::Positional(name), &who, ff.callee.called())
                }
                Some(j) if ff.slots[j].is_some() => {
                    let who = ff.callee.who();
                    self.misfit(a.span, Misfit::Supplied(name), &who, ff.callee.called())
                }
                Some(j) => {
                    self.note_slot(&ff.callee, j, a);
                    ff.pending = j;
                    ff.ni += 1;
                    m.k(Frame::Fill(ff));
                    m.stack.push(Job::Expr(a));
                    return;
                }
            };
            m.give(t);
            return;
        }
        if !ff.ok {
            m.give(None);
            return;
        }
        ff.missing = (0..n).filter(|&j| ff.slots[j].is_none()).collect();
        let span = ff.call.span;
        if ff.call.curry {
            if let Some(&j) = ff.missing.iter().find(|&&j| ff.callee.param(j).1) {
                // Elaboration has no code of the arguments at hand, so its menu writes `…` for
                // the arguments before the parameter; the checker's menu writes their code, and
                // its copy is the one kept where both report.
                let misfit = Misfit::CurriedPositional {
                    name: ff.callee.param(j).0,
                    at: j,
                    before: (j > 0).then_some("…"),
                    after: j + 1 < n,
                };
                let who = ff.callee.who();
                let t = self.misfit(span, misfit, &who, ff.callee.called());
                m.give(t);
                return;
            }
            if ff.missing.is_empty() {
                let who = ff.callee.who();
                let t = self.misfit(span, Misfit::NothingLeftOut, &who, ff.callee.called());
                m.give(t);
                return;
            }
            let FillF {
                callee,
                slots,
                missing,
                next,
                ..
            } = *ff;
            let t = match callee {
                // In a unit with a call that the function called places, the result may reach
                // one, so it carries its own list as the curried call through a value that its
                // function places does ([`Self::placed_call`]): the function's placed value
                // ([`Self::place_term`]) called by `callNamed` (row CALL-curried-placed).
                // `next` arguments came by position, a receiver counted; every parameter after
                // them is given by name or left out, the curry having refused a positional one
                // left out. O(p + a log a) more, once per call written; none while a default
                // is not yet built, as `placed_value` (inside the default itself).
                Callee::Declared(id, f) => {
                    let callee = self.fref(id, span);
                    let placed = match self.info.placed.is_empty() {
                        true => None,
                        false => self.place_term(id, f, (*callee).clone()),
                    };
                    match placed {
                        Some(fv) => {
                            let named: Vec<&str> = (next..n)
                                .filter(|&j| slots[j].is_some())
                                .map(|j| f.params[j].name.as_str())
                                .collect();
                            let left: Vec<(&str, bool)> = (missing.iter())
                                .map(|&j| {
                                    let p = &f.params[j];
                                    (p.name.as_str(), p.default.is_some())
                                })
                                .collect();
                            let placing = placing(next, &named, Some(&left));
                            let ts = slots.into_iter().flatten().collect();
                            self.placed_args(fv, None, placing, ts)
                        }
                        None => {
                            let params =
                                missing.iter().map(|&j| self.kname(&f.params[j])).collect();
                            let call = Term::App(callee, self.param_vars(f));
                            let body = self.supplied(f, slots, call);
                            Term::Lam(params, Shared::new(body))
                        }
                    }
                }
                Callee::Value(f, _) => {
                    // The function value is bound once, outside the lambda.
                    let fv = self.temp();
                    let temps: Vec<Arc<str>> = missing.iter().map(|_| self.temp()).collect();
                    let mut k = 0;
                    let args = slots
                        .into_iter()
                        .map(|s| {
                            s.unwrap_or_else(|| {
                                k += 1;
                                Term::Var(temps[k - 1].clone())
                            })
                        })
                        .collect();
                    let call = Term::App(Shared::new(Term::Var(fv.clone())), args);
                    Term::Let(
                        fv,
                        Shared::new(f),
                        Shared::new(Term::Lam(temps, Shared::new(call))),
                    )
                }
            };
            m.give(Some(t));
            return;
        }
        match ff.callee {
            Callee::Value(..) => {
                ff.order = ff.missing.iter().rev().copied().collect();
                self.value_default(m, ff);
            }
            Callee::Declared(id, f) => self.declared_defaults(m, ff, id, f),
        }
    }

    /// The next closed default of a call through a value, or the call once they are filled.
    fn value_default(&mut self, m: &mut M<'a>, mut ff: Box<FillF<'a>>) {
        let Callee::Value(_, sig) = ff.callee else {
            unreachable!("a call through a value")
        };
        if let Some(j) = ff.order.pop() {
            let p = &sig.params[j];
            let t = match p.default {
                Some((fid, idx, true)) => {
                    let f = self.t.funcs[&fid];
                    let d = f.params[idx].default.as_ref().expect("a default");
                    ff.pending = j;
                    m.k(Frame::ValueDefault(ff));
                    m.stack.push(Job::Expr(d));
                    return;
                }
                Some((_, _, false)) => unreachable!(
                    "the checker marks a call that leaves out a default reading a name as one \
                     the function called places (`open_left_out`)"
                ),
                None => self.misfit(
                    ff.call.span,
                    Misfit::Missing(&p.name, j, p.positional),
                    &sig.who(),
                    ff.callee.called(),
                ),
            };
            m.give(t);
            return;
        }
        let FillF { callee, slots, .. } = *ff;
        let Callee::Value(f, _) = callee else {
            unreachable!("a call through a value")
        };
        let args = slots.into_iter().map(|s| s.expect("filled")).collect();
        m.give(Some(Term::App(Shared::new(f), args)));
    }

    /// A saturated call of a declared function, with arguments left out: their defaults in
    /// an order where each follows the defaulted parameters it reads.
    fn declared_defaults(
        &mut self,
        m: &mut M<'a>,
        mut ff: Box<FillF<'a>>,
        id: usize,
        f: &'a Function,
    ) {
        let fname = &f.name;
        if ff.missing.is_empty() {
            let args = ff.slots.drain(..).map(|s| s.expect("supplied")).collect();
            let callee = self.fref(id, ff.call.span);
            m.give(Some(Term::App(callee, args)));
            return;
        }
        let mut ok = true;
        for &j in &ff.missing {
            if f.params[j].default.is_none() {
                ok = false;
                self.misfit::<()>(
                    ff.call.span,
                    Misfit::Missing(&f.params[j].name, j, f.params[j].positional),
                    fname,
                    CalledKind::Declared,
                );
            }
        }
        if !ok {
            m.give(None);
            return;
        }
        let at: HashMap<usize, usize> = (ff.missing.iter().enumerate())
            .map(|(i, &j)| (self.id(f.params[j].span, &f.params[j].name), i))
            .collect();
        let deps: Vec<Vec<usize>> = (ff.missing.iter())
            .map(|&j| {
                let d = f.params[j].default.as_ref().expect("checked");
                let mut deps: Vec<usize> = (self.t.uses_in(d.span, &[]).into_iter())
                    .filter_map(|b| at.get(&b).copied())
                    .collect();
                zed_collections::sorted::sort_dedup(&mut deps);
                deps
            })
            .collect();
        match topo(&deps) {
            Ok(order) => {
                ff.order = order.into_iter().rev().collect();
                self.decl_default(m, ff);
            }
            Err(cycle) => {
                let names: Vec<String> = (cycle.iter())
                    .map(|&i| format!("`{}`", f.params[ff.missing[i]].name))
                    .collect();
                let t = self.error(
                    ff.call.span,
                    format!(
                        "the defaults of {} read each other in a cycle, so none of them can be \
                         computed first. Write one of them without reading the others.",
                        names.join(", ")
                    ),
                );
                m.give(t);
            }
        }
    }

    /// The next default of a call of a declared function, or the call once they are filled.
    fn decl_default(&mut self, m: &mut M<'a>, mut ff: Box<FillF<'a>>) {
        let Callee::Declared(id, f) = ff.callee else {
            unreachable!("a call of a declared function")
        };
        while let Some(i) = ff.order.pop() {
            let j = ff.missing[i];
            let p = &f.params[j];
            match self.defaults.get(&(id, j)) {
                Some(t) => {
                    let d = t.clone();
                    ff.defaults.push((self.kname(p), d));
                }
                // A call inside the function's own declaration, before its defaults are bound.
                None => {
                    ff.pending = i;
                    m.k(Frame::DeclDefault(ff));
                    m.stack
                        .push(Job::Expr(p.default.as_ref().expect("checked")));
                    return;
                }
            }
        }
        let callee = self.fref(id, ff.call.span);
        let FillF {
            slots, defaults, ..
        } = *ff;
        let body = (defaults.into_iter().rev())
            .fold(Term::App(callee, self.param_vars(f)), |body, (k, d)| {
                Term::Let(k, Shared::new(d), Shared::new(body))
            });
        m.give(Some(self.supplied(f, slots, body)));
    }

    /// A parameter's kernel name.
    fn kname(&self, p: &Param) -> Arc<str> {
        self.names[self.id(p.span, &p.name)].clone()
    }

    /// Each parameter of `f`, as a term.
    fn param_vars(&self, f: &Function) -> Vec<Term> {
        f.params.iter().map(|p| Term::Var(self.kname(p))).collect()
    }

    /// `body` with the arguments supplied bound to the parameters they fill.
    fn supplied(&self, f: &Function, slots: Vec<Option<Term>>, body: Term) -> Term {
        (slots.into_iter().zip(&f.params).rev()).fold(body, |body, (s, p)| match s {
            Some(t) => Term::Let(self.kname(p), Shared::new(t), Shared::new(body)),
            None => body,
        })
    }

    /// `x.f(args)` and `x?.f(args)`: the uniform call `f(x, args)`, `?.` passing an atom `x`
    /// through. Without parentheses the arguments are empty.
    fn member(
        &mut self,
        m: &mut M<'a>,
        of: &'a Expr,
        name: &'a str,
        safe: bool,
        member: Span,
        call: Call<'a>,
    ) {
        if !safe && self.stream_read(m, of, name, member, &call) {
            return;
        }
        let mb = Member {
            name,
            safe,
            member,
            call,
            literal: matches!(
                of.kind,
                ExprKind::Int { .. }
                    | ExprKind::Float { .. }
                    | ExprKind::Rat(_)
                    | ExprKind::Str(_)
                    | ExprKind::Bool(_)
                    | ExprKind::Atom(_)
            ),
        };
        m.k(Frame::MemberOf(Box::new(mb)));
        m.stack.push(Job::Expr(of));
    }

    /// `s.first`, `s.any(p)`, `s.all(p)` or `s.find(p)` on `s` a stream over a range with no
    /// upper end, `(a ..).where(q).map(f)` (`open_stream`, which resolution admitted), every
    /// member the prelude's: the walk of `stream_term` begun, and `true`. `(a ..).first` with
    /// no link is the range's low end (plan row RANGE-open) and any other read is elaborated
    /// as written, `false`.
    fn stream_read(
        &mut self,
        m: &mut M<'a>,
        of: &'a Expr,
        name: &str,
        member: Span,
        call: &Call<'a>,
    ) -> bool {
        let Some((_, links)) = open_stream(of) else {
            return false;
        };
        let consumer = match (name, call.positional) {
            ("first", []) if !links.is_empty() && call.span == member => None,
            ("any" | "all" | "find", [_]) if call.named.is_empty() && !call.curry => {
                Quantifier::of(name)
            }
            _ => return false,
        };
        let bound = |span: &Span| matches!(self.t.res.uses.get(span), Some(Ref::Bound(_)));
        if bound(&member) || links.iter().any(|l| bound(&l.member)) {
            return false;
        }
        let range = links.first().map_or(of, |l| l.of);
        let parts = (std::iter::once(range).chain(links.iter().map(|l| l.f)))
            .chain(call.positional.first())
            .collect();
        m.k(Frame::Stream(
            links.iter().map(|l| l.filter).collect(),
            consumer,
        ));
        m.seq(parts, false);
        true
    }

    /// The call of [`Elab::member`], its receiver `x` elaborated.
    /// The family a display builds from its parts' terms `ts` (step L3.2): the entries in
    /// pairs, key then value, to [`Prim::Entries`]. An array's keys are its positions; a set
    /// keys each element by itself, each element bound once so that it is evaluated once.
    fn display(&mut self, d: Display, ts: Vec<Term>) -> Term {
        match d {
            Display::Map => Term::Prim(Prim::Entries, ts),
            Display::Array => {
                let mut args = Vec::with_capacity(2 * ts.len());
                for (i, t) in ts.into_iter().enumerate() {
                    args.push(Term::Lit(Value::Int(i as i64)));
                    args.push(t);
                }
                Term::Prim(Prim::Entries, args)
            }
            Display::Set => {
                let names: Vec<Arc<str>> = ts.iter().map(|_| self.temp()).collect();
                let args = (names.iter())
                    .flat_map(|n| [Term::Var(n.clone()), Term::Var(n.clone())])
                    .collect();
                let body = Term::Prim(Prim::Entries, args);
                // The bindings, innermost last: O(n) for n elements.
                (names.into_iter().zip(ts).rev()).fold(body, |b, (n, t)| {
                    Term::Let(n, Shared::new(t), Shared::new(b))
                })
            }
        }
    }

    /// The kernel term of the remap `e` (DESIGN.md sec:remap_law), from the terms of its
    /// source and of its levels' expressions in level order: a `reindex` whose key map builds
    /// the kept levels' keys and then the folded levels', and whose value map is the leaf;
    /// then a `fold` for each folded level, innermost first. A truncation keys each leaf by
    /// the kept keys and then every key binder, so no two leaves meet, and a `discard` keeps
    /// the keypaths' kept part as set leaves.
    fn remap_term(&mut self, e: &'a Expr, got: Vec<Option<Term>>) -> Option<Term> {
        let ExprKind::Remap {
            binders, levels, ..
        } = &e.kind
        else {
            unreachable!("a remap")
        };
        let plan = self.info.remaps.get(&e.span)?.clone();
        let binders = binders
            .as_deref()
            .expect("a planned remap has an `as` pattern");
        let levels = levels
            .as_deref()
            .expect("a planned remap has an `into` pattern");
        let mut got = all(got)?.into_iter();
        let of = got.next().expect("the source's term");
        let mut at: Vec<Option<Term>> = (levels.iter())
            .map(|l| {
                l.key
                    .as_ref()
                    .map(|_| got.next().expect("a term per level"))
            })
            .collect();
        let (p, x) = (self.temp(), self.temp());
        let n = binders.len() - 1;
        // A value binder that may take a family reads the entry at depth `n` out of the tuple
        // of one that holds it (`RemapPlan::boxed`).
        let of = match plan.boxed {
            true => self.boxed_at(of, n),
            false => of,
        };
        let value = || match plan.boxed {
            true => Term::Prim(
                Prim::TupleGet,
                vec![Term::Var(x.clone()), Term::Lit(Value::Int(0))],
            ),
            false => Term::Var(x.clone()),
        };
        // One kernel name per binder, `_` too: a `_` gets a fresh name (`temp`), so the lets of
        // `lam` bind every key of the keypath, `p[0]` to `p[n - 1]`, and `names[..n]`, which a
        // truncation keys its leaves by, is the whole keypath; a written binder's name is its
        // own (`self.names`, one per binder), so no two lets of `lam` share a name.
        let names: Vec<Arc<str>> = (binders.iter())
            .map(|b| match b {
                Target::Name(name, span) => self.names[self.id(*span, name)].clone(),
                Target::Wild => self.temp(),
            })
            .collect();
        // `(p, x) ↦ let b1 = p[0]; …; let bn = p[n - 1]; let v = x; body`.
        let lam = |body: Term| {
            let mut t = body;
            for (i, name) in names.iter().enumerate().rev() {
                let v = match i < n {
                    true => Term::Prim(
                        Prim::PathKey,
                        vec![Term::Var(p.clone()), Term::Lit(Value::Int(i as i64))],
                    ),
                    false => value(),
                };
                t = Term::Let(name.clone(), Shared::new(v), Shared::new(t));
            }
            Term::Lam(vec![p.clone(), x.clone()], Shared::new(t))
        };
        let mut keys: Vec<Term> = (plan.order.iter())
            .map(|&j| at[j].take().expect("a key level's term"))
            .collect();
        let (vf, witness) = match plan.leaf {
            Some(l) => (
                at[l].take().expect("the leaf's term"),
                zed_kernel::term::Witness::Catalog(plan.witness.clone()),
            ),
            None => {
                let vars = names[..n].iter().map(|b| Term::Var(b.clone()));
                keys.push(match n {
                    1 => Term::Var(names[0].clone()),
                    _ => Term::Prim(Prim::Tuple, vars.collect()),
                });
                (
                    Term::Lit(Value::Bool(true)),
                    zed_kernel::term::Witness::Residue,
                )
            }
        };
        let mut t = Term::Reindex {
            family: Shared::new(of),
            kf: Shared::new(lam(Term::Prim(Prim::Path, keys))),
            vf: Shared::new(lam(vf)),
            witness,
        };
        if plan.leaf.is_none() {
            let (q, en) = (self.temp(), self.temp());
            let at_kept = Term::Prim(
                Prim::Eq,
                vec![
                    Term::Prim(Prim::PathLen, vec![Term::Var(q.clone())]),
                    Term::Lit(Value::Int(plan.kept as i64)),
                ],
            );
            let sel = Term::If(
                Shared::new(at_kept),
                Shared::new(Term::Lit(Value::atom("boundary"))),
                Shared::new(Term::Lit(Value::Bool(true))),
            );
            t = Term::Discard {
                family: Shared::new(t),
                sel: Shared::new(Term::Lam(vec![q, en], Shared::new(sel))),
            };
        }
        let mut depth = plan.order.len();
        for &j in plan.order[plan.kept..].iter().rev() {
            let op = match plan.folds[&j] {
                o @ (BinaryOp::Add | BinaryOp::Mul | BinaryOp::And | BinaryOp::Or) => o.prim(),
                // The checker rejects a fold by any other operator, at its error.
                _ => return None,
            };
            let identity = self.fold_identity(levels[j].span);
            t = Term::Fold {
                family: Shared::new(t),
                op: Shared::new(Term::PrimFn(op)),
                identity: identity.map(|v| Shared::new(Term::Lit(v))),
                depth,
                ev: zed_kernel::term::Evidence::from([(
                    "associative".into(),
                    zed_kernel::term::Grade::Axiom,
                )]),
            };
            depth -= 1;
        }
        Some(t)
    }

    /// The family `t` with each entry at depth `depth` held in a tuple of one, so a `reindex`,
    /// which walks leaves, stops at that depth and binds a row whole (plan row
    /// REMAP-fewer-binders): `let s = t; fam k in s: …` down to `(s[k],)`, a `fam` per level.
    /// An empty family above that depth stays empty, a keypath that ends early, as without the
    /// boxing. The checker gives a family at every level above `depth`.
    // Complexity tradeoff: one pass over the entries down to `depth`, each read by `Get` in the
    // ordered map, O(e log e) for e entries, which the `reindex` after it costs too; a reindex
    // with a depth of its own would skip the pass but needs a new kernel term, read by every
    // crate that walks terms.
    fn boxed_at(&mut self, t: Term, depth: usize) -> Term {
        if depth == 0 {
            return Term::Prim(Prim::Tuple, vec![t]);
        }
        let (s, k) = (self.temp(), self.temp());
        let entry = Term::Prim(Prim::Get, vec![Term::Var(s.clone()), Term::Var(k.clone())]);
        let body = self.boxed_at(entry, depth - 1);
        let fam = Term::Fam {
            domain: Shared::new(Term::Var(s.clone())),
            var: k,
            body: Shared::new(body),
        };
        Term::Let(s, Shared::new(t), Shared::new(fam))
    }

    /// `x.group(f)` on a family of one level (DESIGN.md sec:grouping): the widening
    /// `reindex` that sends the entry `k -> v` to the keypath `(f(v), k)` and keeps `v`, one to
    /// one by tupling, since `k` is kept.
    // Complexity tradeoff: one `reindex` over the n leaves, O(n log n) into the ordered map,
    // against a hash grouping's O(n) expected; the kernel's families are ordered maps, and the
    // result is read in key order.
    fn group_term(&mut self, x: Term, f: Term) -> Term {
        let (g, p, v) = (self.temp(), self.temp(), self.temp());
        let class = Term::App(
            Shared::new(Term::Var(g.clone())),
            vec![Term::Var(v.clone())],
        );
        let k = Term::Prim(
            Prim::PathKey,
            vec![Term::Var(p.clone()), Term::Lit(Value::Int(0))],
        );
        let kf = Term::Lam(
            vec![p.clone(), v.clone()],
            Shared::new(Term::Prim(Prim::Path, vec![class, k])),
        );
        let vf = Term::Lam(vec![p, v.clone()], Shared::new(Term::Var(v)));
        let t = Term::Reindex {
            family: Shared::new(x),
            kf: Shared::new(kf),
            vf: Shared::new(vf),
            witness: zed_kernel::term::Witness::Residue,
        };
        Term::Let(g, Shared::new(f), Shared::new(t))
    }

    fn member_call(&mut self, m: &mut M<'a>, mb: Member<'a>, x: Term) {
        let Member {
            name,
            safe,
            member,
            call,
            literal,
        } = mb;
        let (receiver, wrap) = if safe {
            let t = self.temp();
            (Term::Var(t.clone()), Some((t, x)))
        } else {
            (x, None)
        };
        let error = match self.t.res.uses.get(&member) {
            Some(Ref::Bound(ids)) if ids.len() > 1 => format!(
                "`{name}` names {} definitions, and this version of zedc does not yet choose among \
                 definitions that share a name. Give each of them a name of its own.",
                ids.len()
            ),
            Some(Ref::Bound(ids)) if self.t.funcs.contains_key(&self.target(ids[0])) => {
                let id = self.target(ids[0]);
                let f = self.t.funcs[&id];
                m.k(Frame::MemberEnd(wrap));
                self.call_with(m, Callee::Declared(id, f), Some(receiver), call);
                return;
            }
            Some(Ref::Bound(ids)) => {
                // A name bound to a lambda in a block takes the body made at this call's
                // identities (`Elab::fkernel`); any other names its written body.
                let id = self.target(ids[0]);
                let f = Term::Var(self.fkernel(id, call.span));
                m.k(Frame::MemberEnd(wrap));
                self.call_value(m, f, Some(receiver), call);
                return;
            }
            _ => match prelude_layer(name) {
                // `.sum` on a type parameter, a family at some calls and a tuple at others: the
                // value is tested at run time (row FAIL-generic-sum-method).
                Some(1) if name == "sum" && self.info.generic_sums.contains(&call.span) => {
                    let t = self.generic_sum(receiver, call.span);
                    m.k(Frame::MemberEnd(wrap));
                    m.give(Some(t));
                    return;
                }
                // `.sum` on a family, `x >< (+)`, which the checker recorded by the call's span.
                Some(1) if name == "sum" && self.info.family_sums.contains(&call.span) => {
                    let t = self.member_fold(receiver, Prim::Add, call.span);
                    m.k(Frame::MemberEnd(wrap));
                    m.give(Some(t));
                    return;
                }
                Some(1) => {
                    let f = Term::Var(name.into());
                    m.k(Frame::MemberEnd(wrap));
                    self.call_value(m, f, Some(receiver), call);
                    return;
                }
                // `map` and `where` are built in for now (author P221; plan row MAP-pure-zed);
                // the checker rejects any other argument list.
                // `flatMap` (step L4.1) is the term of `map`: the family each entry's function
                // gives is the inner level; the checker demands that it be a family.
                Some(_) if name == "map" || name == "where" || name == "flatMap" => {
                    match call.positional {
                        [f] if call.named.is_empty() && !call.curry => {
                            m.k(Frame::MemberEnd(wrap));
                            m.k(Frame::MapFn(receiver, name == "where"));
                            m.stack.push(Job::Expr(f));
                            return;
                        }
                        _ => {
                            m.give(None);
                            return;
                        }
                    }
                }
                // `foldl` and `foldr` are built in as `map` is (step L3.3); the checker rejects
                // any other argument list.
                Some(_) if name == "foldl" || name == "foldr" => match call.positional {
                    [a, b] if call.named.is_empty() && !call.curry => {
                        m.k(Frame::MemberEnd(wrap));
                        m.k(Frame::FoldDir(receiver, name == "foldr"));
                        m.seq(vec![a, b], false);
                        return;
                    }
                    _ => {
                        m.give(None);
                        return;
                    }
                },
                // `group` is built in as `map` is (step L4.1); the checker rejects every
                // `rekey` and any other argument list.
                Some(_) if name == "group" => match call.positional {
                    [f] if call.named.is_empty() && !call.curry => {
                        m.k(Frame::MemberEnd(wrap));
                        m.k(Frame::Group(receiver));
                        m.stack.push(Job::Expr(f));
                        return;
                    }
                    _ => {
                        m.give(None);
                        return;
                    }
                },
                // `.count`, `.first` and `.last` are built in as `map` is (plan row FP-ops-run):
                // the kernel's `count`, `first` and `last`, which pass a loose atom through.
                Some(_) if matches!(name, "count" | "first" | "last") => {
                    let p = match name {
                        "count" => Prim::Count,
                        "first" => Prim::First,
                        _ => Prim::Last,
                    };
                    m.k(Frame::MemberEnd(wrap));
                    m.give(Some(Term::Prim(p, vec![receiver])));
                    return;
                }
                // `.reduce(op)`, `x >< op`; for a function not a section, the checker recorded
                // the prelude word `max` or `min` it is by the call's span.
                Some(_) if name == "reduce" => match call.positional {
                    [op] if call.named.is_empty() && !call.curry => {
                        let t = (self.reducer_prim(op, call.span))
                            .map(|p| self.member_fold(receiver, p, call.span));
                        m.k(Frame::MemberEnd(wrap));
                        m.give(t);
                        return;
                    }
                    _ => {
                        m.give(None);
                        return;
                    }
                },
                // `.scan(op)` (step L5.3, plan row FP-ops-scan), its operator found as
                // `reduce`'s is.
                Some(_) if name == "scan" => match call.positional {
                    [op] if call.named.is_empty() && !call.curry => {
                        let t =
                            (self.reducer_prim(op, call.span)).map(|p| self.scan_term(receiver, p));
                        m.k(Frame::MemberEnd(wrap));
                        m.give(t);
                        return;
                    }
                    _ => {
                        m.give(None);
                        return;
                    }
                },
                // `.chunkBy(f)` (step L5.3, plan row FP-ops-scan), built in as `group` is.
                Some(_) if name == "chunkBy" => match call.positional {
                    [f] if call.named.is_empty() && !call.curry => {
                        m.k(Frame::MemberEnd(wrap));
                        m.k(Frame::ChunkBy(receiver));
                        m.stack.push(Job::Expr(f));
                        return;
                    }
                    _ => {
                        m.give(None);
                        return;
                    }
                },
                // The quantifiers of step L3.15a, built in as `map` is.
                Some(_) if let Some(q) = Quantifier::of(name) => match call.positional {
                    [f] if call.named.is_empty() && !call.curry => {
                        m.k(Frame::MemberEnd(wrap));
                        m.k(Frame::Quantify(receiver, q));
                        m.stack.push(Job::Expr(f));
                        return;
                    }
                    _ => {
                        m.give(None);
                        return;
                    }
                },
                // `s.split(sep)`, `s.lines` and `xs.concat(sep: s)` (plan row FP-ops-strings),
                // built in as `map` is; the checker rejects any other argument list.
                Some(_) if let Some(p) = fp_ops::strings_prim(name) => {
                    m.k(Frame::MemberEnd(wrap));
                    self.strings(m, Some(receiver), p, call);
                    return;
                }
                // `x.zip(y)` (step L5.2); the checker rejects any other argument list.
                Some(_) if name == "zip" => match call.positional {
                    [y] if call.named.is_empty() && !call.curry => {
                        m.k(Frame::MemberEnd(wrap));
                        m.k(Frame::Zip(receiver));
                        m.stack.push(Job::Expr(y));
                        return;
                    }
                    _ => {
                        m.give(None);
                        return;
                    }
                },
                Some(_) => not_yet(&format!("the prelude word `{name}`")),
                // A literal has no fields, so `.name` can only call a function `name`, and
                // none is in scope: the resolver's short headline, the rule in a note
                // (DESIGN.md sec:diagnostics, "A short headline, the detail in the notes").
                None if literal => {
                    self.errors.push(Error {
                        menu: String::new(),
                        row: None,
                        span: member,
                        message: zedc_resolve::resolve::undefined(name),
                        notes: vec![Note {
                            span: member,
                            text: format!(
                                "`.{name}` after a literal calls the function `{name}` with the \
                                 literal as its first argument, since a literal has no fields, \
                                 and no function `{name}` is in scope"
                            )
                            .into(),
                        }],
                    });
                    m.give(None);
                    return;
                }
                None => {
                    format!(
                        "`{name}` is not a function in scope, and reading a field with `.{name}` \
                         is part of the Zed language but is not supported by this version of \
                         zedc. Call a function in scope, or correct the name if it is misspelled."
                    )
                }
            },
        };
        let t = self.error(member, error);
        m.give(t);
    }

    /// A function argument fitted to the function type its slot expects: a lambda whose
    /// parameters are in another order or carry defaults, or a declared function whose
    /// named parameters are in another order.
    fn fit(&mut self, m: &mut M<'a>, e: &'a Expr, fit: &'a Fit) {
        // A section is fitted as the lambda it stands for (`ExprKind::Section`).
        if let ExprKind::Section(_, lambda) = &e.kind {
            return self.fit(m, lambda, fit);
        }
        match (fit, &e.kind) {
            (Fit::Lambda { order, extra }, ExprKind::Lambda { params, body }) => {
                let mut names = Vec::new();
                for o in order {
                    names.push(match o {
                        Some(i) => self.kname(&params[*i]),
                        None => self.temp(),
                    });
                }
                let ff = FitF {
                    params,
                    names,
                    extra,
                };
                m.k(Frame::FitBody(Box::new(ff)));
                m.body(body);
            }
            (
                Fit::Adapter {
                    from,
                    domain,
                    result,
                },
                _,
            ) => {
                let ExprKind::Name(n) = &e.kind else {
                    unreachable!("an adapter is recorded on a name")
                };
                let t = self.named(n, e.span).map(|f| {
                    let temps: Vec<Arc<str>> = from.iter().map(|_| self.temp()).collect();
                    let args = from.iter().map(|&j| Term::Var(temps[j].clone())).collect();
                    let call = Term::App(Shared::new(f), args);
                    let call = match result {
                        Some(c) => self.coerce(call, c),
                        None => call,
                    };
                    let body = match domain {
                        Some(d) => in_domain(d, &temps, call),
                        None => call,
                    };
                    Term::Lam(temps, Shared::new(body))
                });
                m.give(t);
            }
            _ => unreachable!("a lambda fit is recorded on a lambda"),
        }
    }

    /// `v` rebuilt by `c` ([`check::Coercion`]): a function as a lambda that calls it where
    /// its arguments are in its domain and gives `#notFound` elsewhere ([`in_domain`]), its
    /// result rebuilt in turn; a tuple as the tuple of its components, each rebuilt where `c`
    /// says; a family as the family of its entries, each rebuilt. Each value is bound to a
    /// temporary once and read from it.
    ///
    /// Cost: O(size of `c`) terms. The nodes of `c` are listed breadth first, so that each
    /// node's children come after it, then built from the last to the first, each from its
    /// children's terms, without recursion, since `c` nests as deep as the types it follows.
    fn coerce(&mut self, v: Term, c: &check::Coercion) -> Term {
        struct Node<'c> {
            c: &'c check::Coercion,
            x: Arc<str>,
            kids: Vec<Option<usize>>,
        }
        let mut ns = vec![Node {
            c,
            x: self.temp(),
            kids: Vec::new(),
        }];
        let mut i = 0;
        while i < ns.len() {
            let kids: Vec<Option<&check::Coercion>> = match ns[i].c {
                check::Coercion::Fn { result, .. } => vec![result.as_deref()],
                check::Coercion::Tuple(cs) => cs.iter().map(Option::as_ref).collect(),
                check::Coercion::Entries(c) => vec![Some(&**c)],
            };
            let mut at = Vec::with_capacity(kids.len());
            for k in kids {
                at.push(k.map(|c| {
                    let x = self.temp();
                    ns.push(Node {
                        c,
                        x,
                        kids: Vec::new(),
                    });
                    ns.len() - 1
                }));
            }
            ns[i].kids = at;
            i += 1;
        }
        let mut built: Vec<Option<Term>> = (0..ns.len()).map(|_| None).collect();
        for i in (0..ns.len()).rev() {
            let x = || Term::Var(ns[i].x.clone());
            // The term `input` rebuilt by the child at `kid`, if there is one.
            let mut by = |kid: Option<usize>, input: Term| match kid {
                Some(j) => {
                    let body = built[j].take().expect("a child is built before its parent");
                    Term::Let(ns[j].x.clone(), Shared::new(input), Shared::new(body))
                }
                None => input,
            };
            let t = match ns[i].c {
                check::Coercion::Fn { arity, domain, .. } => {
                    let temps: Vec<Arc<str>> = (0..*arity).map(|_| self.temp()).collect();
                    let args = temps.iter().map(|t| Term::Var(t.clone())).collect();
                    let call = by(ns[i].kids[0], Term::App(Shared::new(x()), args));
                    let body = match domain {
                        Some(d) => in_domain(d, &temps, call),
                        None => call,
                    };
                    Term::Lam(temps, Shared::new(body))
                }
                check::Coercion::Tuple(cs) => {
                    let parts = (0..cs.len())
                        .map(|k| {
                            let at = Term::Lit(Value::Int(k as i64));
                            by(ns[i].kids[k], Term::Prim(Prim::TupleGet, vec![x(), at]))
                        })
                        .collect();
                    Term::Prim(Prim::Tuple, parts)
                }
                // The family over its own keys, each entry rebuilt, an atom entry kept as it
                // is (the proof PROOF-family-entry-place at `entries_alike`, zedc-check), as
                // `map` builds a family ([`Elab::map_term`]). O(entries) at run time.
                check::Coercion::Entries(_) => {
                    let (k, e) = (self.temp(), self.temp());
                    let entry = Term::Prim(Prim::Get, vec![x(), Term::Var(k.clone())]);
                    let kept = Term::Match(
                        Shared::new(Term::Var(e.clone())),
                        vec![
                            (KPattern::AnyAtom, Term::Var(e.clone())),
                            (KPattern::Wild, by(ns[i].kids[0], Term::Var(e.clone()))),
                        ],
                    );
                    Term::Fam {
                        domain: Shared::new(x()),
                        var: k,
                        body: Shared::new(Term::Let(e, Shared::new(entry), Shared::new(kept))),
                    }
                }
            };
            built[i] = Some(t);
        }
        let top = built[0].take().expect("the value's term");
        Term::Let(ns[0].x.clone(), Shared::new(v), Shared::new(top))
    }

    /// Takes up a caller where its job left off.
    fn resume(&mut self, m: &mut M<'a>, f: Frame<'a>) {
        match f {
            Frame::Site(span) => {
                if let Ret::T(Some(t)) = &m.ret {
                    let span = zed_kernel::sites::Span {
                        start: span.start,
                        end: span.end,
                    };
                    zed_kernel::sites::mark(t, span, &mut self.sited);
                }
            }
            Frame::Env(saved) => self.leave_expr(saved),
            Frame::Seq(mut sf) => {
                let t = m.t();
                let failed = t.is_none();
                sf.got.push(t);
                match sf.left.pop() {
                    Some(next) if !(sf.stop && failed) => {
                        m.k(Frame::Seq(sf));
                        m.stack.push(Job::Expr(next));
                    }
                    _ => m.ret = Ret::Got(sf.got),
                }
            }
            Frame::Unary(p, e) => {
                let t = m.t().map(|a| self.unary(p, e, a));
                m.give(t);
            }
            Frame::Read(s, p) => {
                self.reading.remove(&s);
                let t = m.t().map(|a| Term::Prim(p, vec![a]));
                m.give(t);
            }
            Frame::Coerce(s, c) => {
                self.coercing.remove(&s);
                let t = m.t().map(|v| self.coerce(v, c));
                m.give(t);
            }
            Frame::Witness(s, w) => {
                self.guarding.remove(&s);
                let t = m.t().map(|own| self.witnessed(s, w, own));
                m.give(t);
            }
            Frame::Binary(e) => {
                let t = self.binary(e, m.got());
                m.give(t);
            }
            Frame::Tuple => {
                let t = all(m.got()).map(|ts| Term::Prim(Prim::Tuple, ts));
                m.give(t);
            }
            Frame::Display(d) => {
                let t = all(m.got()).map(|ts| self.display(d, ts));
                m.give(t);
            }
            Frame::MapFn(x, filter) => {
                let t = m.t().map(|f| match filter {
                    true => self.where_term(x, f),
                    false => self.map_term(x, f),
                });
                m.give(t);
            }
            Frame::Strings(receiver, p) => {
                let t = all(m.got()).map(|ts| {
                    let args = receiver.into_iter().chain(ts).collect();
                    fp_ops::strings_term(p, args)
                });
                m.give(t);
            }
            Frame::FoldDir(x, right) => {
                let t = all(m.got()).map(|ts| {
                    let [a, b]: [Term; 2] = ts.try_into().expect("two arguments");
                    match right {
                        false => self.fold_dir_term(x, a, b, false),
                        true => self.fold_dir_term(x, b, a, true),
                    }
                });
                m.give(t);
            }
            Frame::Fold(p, span) => {
                let t = m.t().map(|family| self.fold_one(family, p, span));
                m.give(t);
            }
            Frame::Quantify(x, q) => {
                let t = m.t().map(|f| self.quantifier_term(x, f, q));
                m.give(t);
            }
            Frame::Stream(filters, q) => {
                let t = all(m.got()).map(|ts| {
                    let mut ts = ts.into_iter();
                    let src = ts.next().expect("the range");
                    let fs = (filters.into_iter())
                        .map(|w| (ts.next().expect("a link's function"), w))
                        .collect();
                    let consumer = q.map(|q| (q, ts.next().expect("the quantifier's function")));
                    self.stream_term(src, fs, consumer)
                });
                m.give(t);
            }
            Frame::Zip(x) => {
                let t = m.t().map(|y| self.zip_term(x, y));
                m.give(t);
            }
            Frame::Group(x) => {
                let t = m.t().map(|f| self.group_term(x, f));
                m.give(t);
            }
            Frame::ChunkBy(x) => {
                let t = m.t().map(|f| self.chunk_by_term(x, f));
                m.give(t);
            }
            Frame::Remap(e) => {
                let got = m.got();
                let t = self.remap_term(e, got);
                m.give(t);
            }
            Frame::In(negated) => {
                let t = all(m.got()).map(|ts| {
                    let has = Term::Prim(Prim::Has, ts);
                    match negated {
                        true => Term::Prim(Prim::Not, vec![has]),
                        false => has,
                    }
                });
                m.give(t);
            }
            // `a ..= b` is `range(a, b + 1)`; `+` builds a wider integer past `i64`.
            Frame::Range(through) => {
                let t = all(m.got()).map(|mut ts| {
                    if through {
                        let b = ts.pop().expect("a high end");
                        ts.push(Term::Prim(Prim::Add, vec![b, Term::Lit(Value::Int(1))]));
                    }
                    Term::Prim(Prim::Range, ts)
                });
                m.give(t);
            }
            Frame::RangeFrom => {
                let t = all(m.got()).map(|ts| Term::Prim(Prim::RangeFrom, ts));
                m.give(t);
            }
            Frame::Is(e) => {
                let ExprKind::Is { ty, negated, .. } = &e.kind else {
                    unreachable!("an `is`")
                };
                let v = m.t();
                let t = self.ty(ty);
                let t = self.is(v, t, ty.span, *negated);
                m.give(t);
            }
            Frame::Else(e) => {
                let ExprKind::Else { pattern, .. } = &e.kind else {
                    unreachable!("an `else`")
                };
                let got = m.got();
                let t = self.else_(got, pattern.as_ref());
                m.give(t);
            }
            Frame::If(e) => {
                let ExprKind::If {
                    cond,
                    then,
                    otherwise,
                } = &e.kind
                else {
                    unreachable!("an `if`")
                };
                let t = all(m.got()).map(|ts| {
                    let [c, a, b]: [Term; 3] = ts.try_into().expect("three terms");
                    // A written `if` is marked around its term (MUTATION.md H9).
                    let mark = Mark {
                        parts: [cond.span, then.span, otherwise.span],
                        ..Mark::on(e.span, Kind::If)
                    };
                    self.wrap_mark(if_(c, a, b), mark)
                });
                m.give(t);
            }
            Frame::Str(parts) => {
                let t = all(m.got()).map(|holes| string(parts, holes));
                m.give(t);
            }
            Frame::Pass(mut pf) => {
                let x = m.t();
                let (a, _) = pf.args[pf.lets.len() - 1];
                let last = pf.lets.last_mut().expect("the argument's temporary");
                last.1 = x;
                self.passing.insert(a.span, last.0.clone());
                self.pass_step(m, pf);
            }
            Frame::PassCall(pf) => {
                let call = m.t();
                self.guarding.remove(&pf.e.span);
                let t = self.pass_end(*pf, call);
                m.give(t);
            }
            Frame::Block(mark) => {
                let Ret::Scope(s) = m.take() else {
                    unreachable!("a scope's result")
                };
                let s = self.place_locals(mark, s);
                let t = s.map(|(binds, export)| {
                    let body = export.unwrap_or(Term::Prim(Prim::Tuple, Vec::new()));
                    binds.into_iter().rev().fold(body, |body, (_, k, t)| {
                        Term::Let(k, Shared::new(t), Shared::new(body))
                    })
                });
                m.give(t);
            }
            Frame::Scope(mut sf) => {
                let Ret::Stmt(binds) = m.take() else {
                    unreachable!("a statement's result")
                };
                // A top-level statement's folds no call decided, from its defaults and its
                // test rows (its body's are its function's, `Frame::FnTests`), are attributed
                // to each of its bindings, for `Elab::check_instances`.
                if sf.top {
                    let sites = self.inst.undecided.split_off(sf.undecided);
                    let kernels = binds.iter().flatten().map(|(_, k, _)| k);
                    self.inst.attribute(kernels, sites);
                }
                match binds {
                    Some(binds) => sf.binds.extend(binds),
                    None => {
                        sf.ok = false;
                        // The first top-level definition that gave no term, which `lower`
                        // names when no error says why (FAIL-elab-none-without-error).
                        if sf.top {
                            self.dropped.get_or_insert(sf.items[sf.at]);
                        }
                    }
                }
                self.scope_step(m, sf);
            }
            Frame::Export(sf) => {
                let s = all(m.got()).and_then(|mut ts| {
                    let export = if ts.len() == 1 {
                        ts.pop().expect("one")
                    } else {
                        Term::Prim(Prim::Tuple, ts)
                    };
                    sf.ok.then_some((sf.binds, Some(export)))
                });
                m.ret = Ret::Scope(s);
            }
            Frame::Bind(s) => {
                let v = m.t();
                self.inst.end_bound(s);
                m.ret = Ret::Stmt(v.map(|v| self.bind(s, v)));
            }
            Frame::Push(s) => {
                let StmtKind::Push { port, .. } = &s.kind else {
                    unreachable!("a push")
                };
                let out = m.t().map(|v| {
                    let t = self.temp();
                    vec![(t.to_string(), t, self.push(s.span, port, v))]
                });
                m.ret = Ret::Stmt(out);
            }
            Frame::FnDefault(mut ff) => {
                match m.t() {
                    None => ff.ok = false,
                    Some(t) => {
                        let j = ff.j;
                        // A marked constant (`elaborate_marked`) is a literal here too, so
                        // marking leaves the shape alone.
                        let marked = matches!(&t, Term::Prim(Prim::Neg, xs) if xs.len() == 2);
                        let at_call = if matches!(t, Term::Lit(_) | Term::Var(_)) || marked {
                            t
                        } else {
                            let k: Arc<str> =
                                format!("{}${}", self.names[ff.id], ff.params[j]).into();
                            let reads = mem::take(&mut ff.reads);
                            let args = reads.iter().map(|r| Term::Var(r.clone())).collect();
                            (ff.thunks).push((
                                k.to_string(),
                                k.clone(),
                                Term::Lam(reads, Shared::new(t)),
                            ));
                            Term::App(Shared::new(Term::Var(k)), args)
                        };
                        self.defaults.insert((ff.id, j), at_call);
                    }
                }
                ff.j += 1;
                self.fn_default(m, ff);
            }
            Frame::FnBody(mut ff) => {
                ff.body = m.t();
                ff.undecided = self.inst.undecided.split_off(ff.undecided_from);
                let (f, id, span, top) = (ff.f, ff.id, ff.s.span, ff.top);
                m.k(Frame::FnTests(ff));
                self.tests(m, f, id, span, top);
            }
            Frame::FnTests(ff) => {
                let Ret::Tests(tests) = m.take() else {
                    unreachable!("a test table's result")
                };
                let FnF {
                    f,
                    top,
                    id,
                    params,
                    thunks,
                    ok,
                    body,
                    undecided,
                    ..
                } = *ff;
                // The body's folds no call decided are the function's own at the top level,
                // and the enclosing statement's in a block.
                // A block's function whose calls decide folds keeps its own until the block
                // ends, when they are refused only if the written body is named
                // (`Self::place_locals`).
                match top {
                    true => self.inst.attribute([&self.names[id]], undecided),
                    false => {
                        if let Some(sites) = self.inst.end_written(id, undecided) {
                            self.inst.undecided.extend(sites);
                        }
                    }
                }
                let out = body.filter(|_| tests && ok).map(|body| {
                    let mut out = vec![(
                        f.name.clone(),
                        self.names[id].clone(),
                        Term::Lam(params, Shared::new(body)),
                    )];
                    out.extend(thunks);
                    out
                });
                m.ret = Ret::Stmt(out);
            }
            Frame::TestArgs(tf) => {
                let args = all(m.got());
                let expected = &tf.f.tests[tf.i].1;
                m.k(Frame::TestWant(tf, args));
                m.stack.push(Job::Expr(expected));
            }
            Frame::TestWant(mut tf, args) => {
                let want = m.t();
                let (input, expected) = &tf.f.tests[tf.i];
                match (args, want) {
                    (Some(args), Some(want)) => {
                        let case = Span {
                            start: input.span.start,
                            end: expected.span.end,
                        };
                        // The row's call is checked at its key ([`Self::row_call`]), where
                        // the checker decided the identities of the folds it runs.
                        let kernel = self.fkernel(tf.id, input.span);
                        let callee = Shared::new(Term::Var(kernel.clone()));
                        // The inputs of `main` a clause gives the row, by field; their values
                        // end `args`, and the call takes the key's alone.
                        let ports: Vec<&'static str> = (tf.clause().into_iter())
                            .flat_map(|c| &c.ports)
                            .filter_map(|p| main_field(&p.port))
                            .collect();
                        let keyed = args[..args.len() - ports.len()].to_vec();
                        let call = self.row_call(tf.f, input, callee, keyed);
                        self.tests.push(Test {
                            function: tf.f.name.clone(),
                            kernel,
                            check: Term::Prim(Prim::Eq, vec![call, want.clone()]),
                            args,
                            ports,
                            want,
                            span: case,
                        });
                    }
                    _ => tf.ok = false,
                }
                tf.i += 1;
                self.test_case(m, tf);
            }
            Frame::CallOf(call) => match m.t() {
                Some(f) => self.call_value(m, f, None, call),
                None => m.give(None),
            },
            Frame::AtomArgs(name, named) => {
                let t = all(m.got()).map(|ts| {
                    let fields = named.iter().map(|(f, _)| Value::str(f)).collect();
                    let mut args =
                        vec![Term::Lit(Value::str(name)), Term::Lit(Value::Tuple(fields))];
                    args.extend(ts);
                    Term::Prim(Prim::Atom, args)
                });
                m.give(t);
            }
            Frame::ValueArgs(f, receiver) => {
                let t = all(m.got()).map(|ts| {
                    let mut args: Vec<Term> = receiver.into_iter().collect();
                    args.extend(ts);
                    Term::App(Shared::new(f), args)
                });
                m.give(t);
            }
            Frame::AtArg(f, rest) => {
                let t = m.t().map(|k| Term::Prim(Prim::At, vec![f, k]));
                match (t, rest) {
                    (Some(t), [k, rest @ ..]) => {
                        m.k(Frame::AtArg(t, rest));
                        m.stack.push(Job::Expr(k));
                    }
                    (t, _) => m.give(t),
                }
            }
            Frame::PlacedArgs(f, receiver, placing) => {
                let t = all(m.got()).map(|ts| self.placed_args(f, receiver, *placing, ts));
                m.give(t);
            }
            Frame::Fill(mut ff) => {
                let t = m.t();
                ff.ok &= t.is_some();
                ff.slots[ff.pending] = t;
                self.fill(m, ff);
            }
            Frame::ValueDefault(mut ff) => match m.t() {
                Some(t) => {
                    ff.slots[ff.pending] = Some(t);
                    self.value_default(m, ff);
                }
                None => m.give(None),
            },
            Frame::DeclDefault(mut ff) => match m.t() {
                Some(d) => {
                    let Callee::Declared(_, f) = ff.callee else {
                        unreachable!("a call of a declared function")
                    };
                    let k = self.kname(&f.params[ff.missing[ff.pending]]);
                    ff.defaults.push((k, d));
                    self.decl_default(m, ff);
                }
                None => m.give(None),
            },
            Frame::MemberOf(mb) => match m.t() {
                Some(x) => self.member_call(m, *mb, x),
                None => m.give(None),
            },
            Frame::MemberEnd(wrap) => {
                let t = m.t().map(|call| match wrap {
                    None => call,
                    Some((t, x)) => Term::Let(
                        t.clone(),
                        Shared::new(x),
                        Shared::new(Term::Match(
                            Shared::new(Term::Var(t.clone())),
                            vec![(KPattern::AnyAtom, Term::Var(t)), (KPattern::Wild, call)],
                        )),
                    ),
                });
                m.give(t);
            }
            Frame::IndexDeclared(id, of, at) => {
                let t = match m.t() {
                    None => None,
                    Some(k) => {
                        let f = self.t.funcs[&id];
                        match f.params.len() {
                            0 => {
                                self.errors.push(Error {
                                    menu: String::new(),
                                    row: None,
                                    span: of.span,
                                    message: format!(
                                        "`{0}` takes no arguments, and this indexes it with \
                                         one. Write `{0}` without the index, or give `{0}` a \
                                         parameter for it.",
                                        f.name
                                    ),
                                    notes: vec![Note {
                                        span: self.t.res.binders[id].span,
                                        text: format!(
                                            "`{}` is declared here with no parameters",
                                            f.name
                                        )
                                        .into(),
                                    }],
                                });
                                None
                            }
                            1 => Some(Term::App(self.fref(id, at), vec![k])),
                            n => {
                                let rest: Vec<Arc<str>> = (1..n).map(|_| self.temp()).collect();
                                let mut args = vec![k];
                                args.extend(rest.iter().map(|r| Term::Var(r.clone())));
                                let callee = self.fref(id, at);
                                Some(Term::Lam(rest, Shared::new(Term::App(callee, args))))
                            }
                        }
                    }
                };
                m.give(t);
            }
            Frame::Index(k, span) => {
                // A read the checker found to be of a family whose keys are one integer
                // interval, every key present, misses with `#outOfBounds` (DESIGN.md
                // sec:type_language, the `m[k]` row).
                let dense = self.info.dense.get(&span) == Some(&true);
                // A bracket on a value that may be a function gives it one argument: an
                // application, or the section over the other parameters of a function of
                // several (`Info::brackets`; the kernel reads a tuple or a family applied to
                // one key, so a value that may be either is applied too).
                let count = self.info.brackets.get(&span).copied();
                let t = all(m.got()).map(|ts| {
                    let [v, i]: [Term; 2] = ts.try_into().expect("two terms");
                    match (&k.kind, count) {
                        _ if dense => Term::Prim(Prim::At, vec![v, i]),
                        (_, Some(n)) if n > 1 => self.bracket_section(v, i, n),
                        (_, Some(_)) => Term::App(Shared::new(v), vec![i]),
                        (ExprKind::Int { .. }, None) => Term::Prim(Prim::TupleGet, vec![v, i]),
                        _ => Term::App(Shared::new(v), vec![i]),
                    }
                });
                m.give(t);
            }
            Frame::FitBody(ff) => match m.t() {
                Some(body) => {
                    let ds = ff.extra.iter().rev().map(|&i| {
                        ff.params[i]
                            .default
                            .as_ref()
                            .expect("an extra has a default")
                    });
                    let ds = ds.collect();
                    m.k(Frame::FitExtras(ff, body));
                    m.seq(ds, true);
                }
                None => m.give(None),
            },
            Frame::FitExtras(ff, body) => {
                let t = all(m.got()).map(|ds| {
                    let FitF {
                        params,
                        names,
                        extra,
                    } = *ff;
                    let body = (extra.iter().rev().zip(ds)).fold(body, |body, (&i, d)| {
                        Term::Let(self.kname(&params[i]), Shared::new(d), Shared::new(body))
                    });
                    Term::Lam(names, Shared::new(body))
                });
                m.give(t);
            }
            Frame::Lambda(names) => {
                let t = m.t().map(|body| Term::Lam(names, Shared::new(body)));
                m.give(t);
            }
        }
    }

    /// The section `v[i]` of the function `v` of `n` parameters, `n` above one: `v` and `i`
    /// evaluated once, in that order, and the function of the other `n - 1` parameters that
    /// applies `v` to `i` and them, as the bracket on a declared function is
    /// (`Frame::IndexDeclared`).
    fn bracket_section(&mut self, v: Term, i: Term, n: usize) -> Term {
        let (f, k) = (self.temp(), self.temp());
        let rest: Vec<Arc<str>> = (1..n).map(|_| self.temp()).collect();
        let mut args = vec![Term::Var(k.clone())];
        args.extend(rest.iter().map(|r| Term::Var(r.clone())));
        let call = Term::App(Shared::new(Term::Var(f.clone())), args);
        let lam = Term::Lam(rest, Shared::new(call));
        let inner = Term::Let(k, Shared::new(i), Shared::new(lam));
        Term::Let(f, Shared::new(v), Shared::new(inner))
    }

    /// A binary operator's term, its operands elaborated.
    fn binary(&mut self, e: &'a Expr, got: Vec<Option<Term>>) -> Option<Term> {
        let ExprKind::Binary(op, l, r) = &e.kind else {
            unreachable!("a binary operator")
        };
        let [a, b]: [Option<Term>; 2] = got.try_into().expect("two operands");
        let (a, b) = (a?, b?);
        if *op == BinaryOp::Concat && self.info.list_concats.contains(&e.span) {
            return Some(self.list_concat_term(a, b));
        }
        let t = |v: bool| Term::Lit(Value::Bool(v));
        // `&&` and `||` are marked around the `if` they elaborate to (MUTATION.md H7).
        let gap = Span {
            start: l.span.end,
            end: r.span.start,
        };
        let bool_mark = |or| Mark {
            parts: [l.span, r.span, e.span],
            ..Mark::on(gap, Kind::Bool { or })
        };
        let p = match *op {
            BinaryOp::Or => return Some(self.wrap_mark(if_(a, t(true), b), bool_mark(true))),
            BinaryOp::And => return Some(self.wrap_mark(if_(a, b, t(false)), bool_mark(false))),
            op => op.prim(),
        };
        let mut args = vec![a, b];
        if let Some(marks) = &mut self.marks
            && mutable(p)
        {
            // An arithmetic operand of an arithmetic operator is not the root of its
            // expression (MUTATION.md H6).
            if arithmetic(p) {
                for (o, t) in [l, r].into_iter().zip(&args) {
                    if is_arithmetic(o)
                        && let Some(k) = op_mark(t)
                    {
                        marks[k].inner = true;
                    }
                }
            }
            args.push(Term::Lit(Value::Int(marks.len() as i64)));
            marks.push(Mark {
                quotient: self.info.quotients.get(&e.span) == Some(&true),
                ints: self.info.ints.get(&e.span) == Some(&true),
                literal: [numeric(l), numeric(r)],
                parts: [l.span, r.span, e.span],
                ..Mark::on(gap, Kind::Op)
            });
        }
        let w = match (self.split_of(l), self.split_of(r)) {
            (Some(a), Some(b)) if same_witness(a.0, b.0) => Some((a.0, a.1 && b.1)),
            (Some((w, true)), None) => {
                let own = self.own_carrier(l, &args[0]);
                (self.follow_split(r, w, own, &mut args, 1)).then_some((w, true))
            }
            (None, Some((w, true))) => {
                let own = self.own_carrier(r, &args[1]);
                (self.follow_split(l, w, own, &mut args, 0)).then_some((w, true))
            }
            _ => None,
        };
        let Some((w, keeps)) = w else {
            return Some(self.follow(l, r, p, args));
        };
        let own = [self.own_carrier(l, &args[0]), self.own_carrier(r, &args[1])];
        let own = without_int(p, own, &mut args[..2]);
        let (kept, own) = carried(p, own, &args);
        Some(match per_carrier(p, args, 2) {
            Ok(t) => {
                self.split.insert(e.span, (w, keeps && kept, own));
                t
            }
            Err(args) => Term::Prim(p, args),
        })
    }

    /// Whether the operand `o` at `args[at]` is a literal that takes the carrier of the other
    /// operand's value (`Info::follows`), the other operand being split on `w` with each arm
    /// `is c` of carrier `c` ([`Elab::split`]); if so, `args[at]` becomes the literal split on
    /// `w` with the other operand's patterns, which picks in every case the value
    /// [`Elab::follow`] would pick, and both operands are then split on `w`. `2 + 0` in a
    /// generic definition is such a case: the checker gives `2` the parameter as its witness and
    /// has `0` follow `2`. `other` is the carrier of the value of the other operand's last arm,
    /// and without it the operand is not split.
    ///
    /// The same value: in the arm `is c`, the other operand's value is of carrier `c` and the
    /// literal takes its value at `c` where `Info::follows` lists `c`, else its own, as `follow`
    /// does at that value; in the last arm the other operand's value is of carrier `other`, and
    /// the literal takes its value at `other` where listed, else its own. The patterns need not
    /// be the literal's carriers (STAGE-generic-fold-div): `1` in `1.5 + 1` lists `f64`, which
    /// the decimal's arms leave to their last, and the exponent `2` in `(2 + 1) ^ 2` lists `f64`
    /// and `f32` alone, keeping its own `int` at `rat`. The last arm's carrier is not always the
    /// literal's own either: in `1 / 2` the checker gives `1` the value `1.0` at a value of no
    /// carrier of the patterns, as `/` takes no `int`, and `2`, following it, then takes `2.0`.
    // Complexity tradeoff: each listed carrier's pattern built once and compared with each of
    // the other operand's, O(C²) comparisons for C ≤ 4 numeric carriers, against the O(C) arms
    // `follow` builds anyway; the `let` of `follow` is not built. Before (STAGE-generic-fold):
    // O(C) by requiring the patterns to be the listed carriers in order, which left a decimal
    // and an exponent to `follow`.
    fn follow_split(
        &mut self,
        o: &Expr,
        w: &check::Witness,
        other: Option<Carrier>,
        args: &mut [Term],
        at: usize,
    ) -> bool {
        let Some(s) = lit_span(o).filter(|s| !self.info.witness.contains_key(s)) else {
            return false;
        };
        let (Some(values), Some(arms), Some(other)) =
            (self.info.follows.get(&s), arms_of(&args[1 - at]), other)
        else {
            return false;
        };
        let listed: Vec<(KPattern, &Value)> = (values.iter())
            .map(|(c, v)| (KPattern::Is(c.ty()), v))
            .collect();
        let own = &args[at];
        let split = (arms.iter())
            .map(|(q, _)| {
                let v = match q {
                    KPattern::Wild => values.iter().find(|(c, _)| *c == other).map(|(_, v)| v),
                    q => listed.iter().find(|(p, _)| p == q).map(|&(_, v)| v),
                };
                let t = match v {
                    Some(v) => marked_as(own, v.clone()),
                    None => own.clone(),
                };
                (q.clone(), t)
            })
            .collect();
        args[at] = Term::Match(self.witness_term(w), split);
        true
    }

    /// The carrier of the value of the last arm of `t`, the term of `e`, where `e` is a
    /// generic literal taking its carrier from a witness, or an operation on such literals
    /// alone built once per carrier ([`Elab::split_of`]), and that carrier is known: the
    /// literal's own value, marked or not, or the operation's as [`Elab::split`] holds it.
    fn own_carrier(&self, e: &Expr, t: &Term) -> Option<Carrier> {
        match lit_span(e) {
            Some(_) => lit_carrier(&arms_of(t)?.last()?.1),
            None => self.split.get(&e.span)?.2,
        }
    }

    /// The unary operator `p` of `e` on its operand's term `a`: built once per carrier when
    /// the operand is an operation on generic literals alone ([`per_carrier`]).
    fn unary(&mut self, p: Prim, e: &'a Expr, a: Term) -> Term {
        let ExprKind::Unary(_, operand) = &e.kind else {
            unreachable!("a unary operator")
        };
        // A negated literal is one literal (`lit_span`), its carrier taken as a whole.
        let w = lit_span(e)
            .is_none()
            .then(|| self.split_of(operand))
            .flatten();
        // An arithmetic expression under a written `-` is not the root where H6 inserts one
        // (MUTATION.md H6: that would give the removal of the `-` again).
        if p == Prim::Neg
            && is_arithmetic(operand)
            && let Some(k) = op_mark(&a)
            && let Some(marks) = &mut self.marks
        {
            marks[k].inner = true;
        }
        let Some((w, keeps)) = w else {
            // A written `-` or `!` not on a literal is marked (MUTATION.md H5 and H8). On an
            // operand built once per carrier (an operation on generic literals alone) it is
            // not: the build stage folds such an operation to a constant, and the literals in
            // it are marked.
            let t = Term::Prim(p, vec![a]);
            if numeric(e) || !matches!(p, Prim::Neg | Prim::Not) {
                return t;
            }
            let mark = Mark {
                parts: [operand.span, e.span, e.span],
                ..Mark::on(e.span, Kind::Unary)
            };
            return self.wrap_mark(t, mark);
        };
        let own = self.own_carrier(operand, &a).filter(|_| keeps_carrier(p));
        match per_carrier(p, vec![a], 1) {
            Ok(t) => {
                self.split
                    .insert(e.span, (w, keeps && keeps_carrier(p), own));
                t
            }
            Err(args) => Term::Prim(p, args),
        }
    }

    /// What gives `e` its carrier when `e` is a generic literal with no other operand
    /// ([`check::Info::witness`]) or an operation on such literals alone built once per
    /// carrier ([`Elab::split`]): its term is then `match w { is c -> …, _ -> … }` on the value
    /// of that witness `w`. With it, whether each arm gives a value of the arm's carrier, as a
    /// literal's arms do.
    fn split_of(&self, e: &Expr) -> Option<(&'a check::Witness, bool)> {
        match lit_span(e) {
            Some(s) => self.info.witness.get(&s).map(|w| (w, true)),
            None => self.split.get(&e.span).map(|&(w, keeps, _)| (w, keeps)),
        }
    }

    /// The primitive `p` on `args`, of the operands `l` and `r`, when one operand is a literal
    /// that takes the carrier of a type variable (`Info::follows`): a literal compared by `==`
    /// or `!=` (DESIGN.md L1.26) or a generic one, written without a suffix (L1.26a). The
    /// other operand is bound first, and the literal takes the carrier of its value, `x == 1`
    /// and `x + 1` reading `1.0` where `x` is an `f64`.
    /// The literal is a constant, so evaluating the other operand first changes nothing.
    fn follow(&mut self, l: &Expr, r: &Expr, p: Prim, mut args: Vec<Term>) -> Term {
        let follows = &self.info.follows;
        // An exponent that is an operation on integer literals alone, `(1 + 1)` in `x ^ (1 + 1)`,
        // follows as a literal, by its own span (plan row LIT-rat-int-op-exponent): an `f64`
        // base has no `int` power at run time. One more lookup per operand, O(1).
        let Some((at, values)) = [l, r].into_iter().enumerate().find_map(|(i, e)| {
            let s = Some(lit_span(e).unwrap_or(e.span))
                .filter(|s| !self.info.witness.contains_key(s))?;
            Some((i, follows.get(&s)?))
        }) else {
            return Term::Prim(p, args);
        };
        let other = self.temp();
        let x = mem::replace(&mut args[1 - at], Term::Var(other.clone()));
        // The literal's own term, which a marked elaboration marks, is the last arm; each other
        // arm carries the same mark ([`marked_as`]), so a mutant of the constant replaces it at
        // every carrier.
        let own = mem::replace(&mut args[at], Term::Var(other.clone()));
        // An exponent that is an operation is bound once and each other arm casts its value, so
        // that a mutant of a literal inside it, which changes that one term, changes the
        // exponent at every carrier, not only in the last arm (plan row
        // MUTATE-follows-operation). The cast gives the arm's constant: the exponent is an `int`
        // and the follows map lists for an exponent `f64` alone, where the `int` is exact there
        // (`check::takes_carrier`: `f32 ^ int` is an arrow, so at `f32` the exponent keeps its
        // `int`, plan row DOC-lit-follows-exponent-f32); at any other carrier the arm keeps its
        // constant. Built so with or without marks, since the mutants are placed
        // by the paths of the elaboration without them (`zedc::mutate`).
        // Complexity tradeoff: O(1) nodes per arm, a `Var` and a cast, against a copy of the
        // exponent's term per arm, O(size) each; one `let` more. The old arms were constants,
        // the casts now run where the stage does not fold the call: one cast of an `int` per
        // evaluation, O(1).
        let operation = lit_span([l, r][at]).is_none();
        let (own, bound) = match operation {
            true => {
                let e = self.temp();
                (Term::Var(e.clone()), Some((e, own)))
            }
            false => (own, None),
        };
        let mut arms: Vec<(KPattern, Term)> = values
            .iter()
            .map(|(c, v)| {
                let cast = match c {
                    Carrier::F64 => Some(Prim::CastF64),
                    _ => None,
                };
                let t = match cast.filter(|_| operation) {
                    Some(p) => Term::Prim(p, vec![own.clone()]),
                    None => marked_as(&own, v.clone()),
                };
                (KPattern::Is(c.ty()), t)
            })
            .collect();
        arms.push((KPattern::Wild, own));
        args[at] = Term::Match(Shared::new(Term::Var(other.clone())), arms);
        let mut t = Term::Prim(p, args);
        if let Some((e, own)) = bound {
            t = Term::Let(e, Shared::new(own), Shared::new(t));
        }
        Term::Let(other, Shared::new(x), Shared::new(t))
    }

    /// The generic literal at `s`, of term `own`, taking the carrier of the value of `w`, a
    /// parameter or a component of one (L1.26a): its value at each carrier of
    /// [`check::Info::follows`] that the value of `w` has, else its own.
    fn witnessed(&mut self, s: Span, w: &check::Witness, own: Term) -> Term {
        let mut arms: Vec<(KPattern, Term)> = self.info.follows[&s]
            .iter()
            .map(|(c, v)| (KPattern::Is(c.ty()), marked_as(&own, v.clone())))
            .collect();
        arms.push((KPattern::Wild, own));
        Term::Match(self.witness_term(w), arms)
    }

    /// The value of `w` as a term, shared: a parameter's name, or the component read from the
    /// value of the witness it is read from, as the read `v[i]` in the body is
    /// (`Frame::Index`).
    // Complexity tradeoff: a term built for each literal copies the d reads of a component
    // nested d deep, O(d) per literal, linear in the text too, since each literal stands beside
    // a read of d steps written in the body, but the elaborated unit then holds L copies for L
    // literals; used: each read's term built once, one step on the shared term of the value it
    // is read from, O(1) per literal and per read, and the unit holds each read once.
    fn witness_term(&mut self, w: &check::Witness) -> Shared {
        let mut steps = Vec::new();
        let mut at = w;
        let mut term = loop {
            match at {
                check::Witness::Param(id) => {
                    break Shared::new(Term::Var(self.names[*id].clone()));
                }
                check::Witness::Component { of, i, read } => match self.reads.get(read) {
                    Some(t) => break t.clone(),
                    None => {
                        steps.push((*i, *read));
                        at = of;
                    }
                },
            }
        };
        for (i, read) in steps.into_iter().rev() {
            let v = self.temp();
            let get = match self.info.dense.get(&read) == Some(&true) {
                true => Prim::At,
                false => Prim::TupleGet,
            };
            let k = Term::Lit(Value::Int(i as i64));
            let body = Term::Prim(get, vec![Term::Var(v.clone()), k]);
            term = Shared::new(Term::Let(v, term, Shared::new(body)));
            self.reads.insert(read, term.clone());
        }
        term
    }

    /// `v is t`, its operand and type elaborated.
    fn is(&mut self, v: Option<Term>, t: Option<KType>, at: Span, negated: bool) -> Option<Term> {
        let (v, t) = (v?, t?);
        if !t.decidable() {
            return self.error(
                at,
                "`is` tests a value against a type when the program runs, and a function \
                 value does not show its type then. Test against a type that is not a \
                 function type, or remove the `is`.",
            );
        }
        let arms = [(KPattern::Is(t), true), (KPattern::Wild, false)];
        Some(Term::Match(
            Shared::new(v),
            arms.map(|(p, b)| (p, Term::Lit(Value::Bool(b != negated))))
                .to_vec(),
        ))
    }

    /// `v else d`, with its pattern, its operands elaborated.
    fn else_(&mut self, got: Vec<Option<Term>>, pattern: Option<&Pattern>) -> Option<Term> {
        let [v, d]: [Option<Term>; 2] = got.try_into().expect("two operands");
        let pat = match pattern {
            // A bare pattern matches the atom with any payload or none, as the checker's
            // narrowing removes it (DESIGN.md L1.27).
            Some(Pattern::Atom {
                name,
                fields,
                items: None,
                ..
            }) if fields.is_empty() => Some(Some(KPattern::Is(check::any_payload(name)))),
            Some(p) => self.pattern(p).map(Some),
            None => Some(None),
        };
        let (v, d, pat) = (v?, d?, pat?);
        let t = self.temp();
        let arm = pat.unwrap_or(KPattern::AnyAtom);
        Some(Term::Match(
            Shared::new(v),
            vec![(arm, d), (KPattern::Bind(t.clone()), Term::Var(t))],
        ))
    }

    /// The bindings of `targets = v`.
    fn bind(&mut self, s: &'a Stmt, v: Term) -> Vec<Bind> {
        let targets = match &s.kind {
            StmtKind::Bind { targets, .. } => targets,
            // An expression statement binds its value to a name no program writes, as `_`.
            StmtKind::Expr(_) => {
                let t = self.temp();
                return vec![(t.to_string(), t, v)];
            }
            _ => unreachable!("a binding or an expression statement"),
        };
        let mut out = Vec::new();
        match &targets[..] {
            [Target::Name(n, _)] => {
                let k = self.names[self.id(s.span, n)].clone();
                out.push((n.clone(), k, v));
            }
            [Target::Wild] => {
                let t = self.temp();
                out.push((t.to_string(), t, v));
            }
            _ => {
                let t = self.temp();
                out.push((t.to_string(), t.clone(), v));
                for (i, target) in targets.iter().enumerate() {
                    if let Target::Name(n, _) = target {
                        let k = self.names[self.id(s.span, n)].clone();
                        let get = Term::Prim(
                            Prim::TupleGet,
                            vec![Term::Var(t.clone()), Term::Lit(Value::Int(i as i64))],
                        );
                        out.push((n.clone(), k, get));
                    }
                }
            }
        }
        out
    }
}

/// Interpolation: the nonempty parts joined by `++`, each hole `String(hole)`.
fn string(parts: &[StrPart], holes: Vec<Term>) -> Term {
    let mut holes = holes.into_iter();
    let mut terms = Vec::new();
    for p in parts {
        match p {
            StrPart::Text(t) if t.is_empty() => {}
            StrPart::Text(t) => terms.push(Term::Lit(Value::str(t))),
            StrPart::Hole(_) => {
                let h = holes.next().expect("a hole's term");
                terms.push(Term::App(Shared::new(Term::Var("String".into())), vec![h]));
            }
        }
    }
    let mut terms = terms.into_iter();
    let first = terms.next().unwrap_or(Term::Lit(Value::str("")));
    terms.fold(first, |a, b| Term::Prim(Prim::Concat, vec![a, b]))
}

/// The span of the numeric literal `e` is, under any `-`, as the checker records it.
fn lit_span(e: &Expr) -> Option<Span> {
    let inner = match &e.kind {
        ExprKind::Unary(UnaryOp::Neg, a) => &**a,
        _ => e,
    };
    matches!(inner.kind, ExprKind::Int { .. } | ExprKind::Float { .. }).then_some(inner.span)
}

/// Whether `e` is a numeric literal, `int`, decimal or `rat`, under at most one `-`: a
/// constant a mutant changes by its neighbors (MUTATION.md H4), not by the mutants of an
/// operator on it (H2, H5).
fn numeric(e: &Expr) -> bool {
    let inner = match &e.kind {
        ExprKind::Unary(UnaryOp::Neg, a) => &**a,
        _ => e,
    };
    matches!(
        inner.kind,
        ExprKind::Int { .. } | ExprKind::Float { .. } | ExprKind::Rat(_)
    )
}

/// Whether `e` is written with an arithmetic operator at its top (`mark::arithmetic`).
fn is_arithmetic(e: &Expr) -> bool {
    use BinaryOp::*;
    matches!(
        e.kind,
        ExprKind::Binary(Add | Sub | Mul | Div | IntDiv | Mod | Pow, _, _)
    )
}

/// Whether the witnesses `a` and `b` give the same value at run time: the same parameter, or
/// the same read `v[i]` of the body. A read's span names one read of the source, and so its
/// receiver too, so comparing `i` and the span is enough, O(1) however deep the read is nested.
fn same_witness(a: &check::Witness, b: &check::Witness) -> bool {
    use check::Witness::{Component, Param};
    match (a, b) {
        (Param(x), Param(y)) => x == y,
        (Component { i, read, .. }, Component { i: j, read: r, .. }) => i == j && read == r,
        _ => false,
    }
}

/// The primitive `p` on `args`, whose first `n` (one or two) are each an operation on generic
/// literals alone, or one such literal, on one witness `w` (L1.26a): each is
/// `match w { is c -> v_c, …, _ -> own }` with the same patterns in the same order. Built once
/// per carrier: `match w { is c -> p(v_c, …, rest), …, _ -> p(own, …, rest) }`, where `rest`
/// is what follows the `n` operands (a mutation mark, `elab::mark`), in every arm, so that a
/// mutant of the operator replaces it at every carrier. `Err(args)` when the operands are not
/// of that form.
///
/// Each value of `w` takes, in each operand, the arm of the same pattern, since the patterns
/// are the same in the same order and `w` reads a parameter or a component of one, which
/// cannot fail where the body's own read does not; so `p` on the operands' arms gives what `p`
/// on the operands gives. The operands of `p` are then constants in each arm, and the build
/// stage (`stage::mix`) folds the arm as it folds the operation in a body at `int`: `2 + 0` and
/// `2 - 0` become the one term `match w { is f64 -> 2.0, …, _ -> 2 }`, so a mutant that swaps
/// them is skipped (L25.8), and the operation is run once at run time, not one `match` per
/// literal.
// Complexity tradeoff: the method of F85 builds one `match` per literal and leaves the
// operation on top, O(L·C) nodes for L literals and C carriers (C ≤ 6); the build stage cannot
// fold an operation whose operands are `match`es on a value not known at build. Used: the
// operands' arms moved into one `match` per operation, no term copied, O(n·C) per operation of
// n operands, so O(L·C) nodes over an operation on L literals, as before, and one witness read
// at run time where there were L. Not taken: a `match` per carrier around the whole body (the
// body specialized per carrier), which copies the body C times and is no smaller than this
// where only operations on literals alone fold.
fn per_carrier(p: Prim, mut args: Vec<Term>, n: usize) -> Result<Term, Vec<Term>> {
    let Some(first) = arms_of(&args[0]) else {
        return Err(args);
    };
    let same = args[1..n].iter().all(|t| {
        arms_of(t).is_some_and(|arms| {
            arms.len() == first.len() && arms.iter().zip(first).all(|(a, b)| a.0 == b.0)
        })
    });
    if !same {
        return Err(args);
    }
    let rest = args.split_off(n);
    let mut scrutinee = None;
    let mut columns = Vec::with_capacity(n);
    for mut t in args {
        let Term::Match(s, arms) = &mut t else {
            unreachable!("each operand is a `match`, checked above")
        };
        scrutinee.get_or_insert_with(|| s.clone());
        columns.push(mem::take(arms).into_iter());
    }
    let count = columns[0].len();
    let arms = (0..count)
        .map(|_| {
            let mut pattern = None;
            let mut ops: Vec<Term> = (columns.iter_mut())
                .map(|c| {
                    let (q, t) = c.next().expect("operands with as many arms, checked above");
                    pattern.get_or_insert(q);
                    t
                })
                .collect();
            // The mark, one integer literal, in every arm: a mutant of the operator replaces it
            // at every carrier (`zedc::mutate`, L25.8), as it does the operation written once.
            ops.extend(rest.iter().cloned());
            let pattern = pattern.expect("at least one operand");
            (pattern, Term::Prim(p, ops))
        })
        .collect();
    let scrutinee = scrutinee.expect("at least one operand");
    Ok(Term::Match(scrutinee, arms))
}

/// For `p` on the operands of terms `args`, each built once per carrier on one witness
/// ([`per_carrier`]), the values of their last arms of carriers `own` where known
/// ([`Elab::own_carrier`]): whether `p` on the operands' arms `is c` gives a value of carrier
/// `c`, and the carrier of its value in the last arm, where known ([`Elab::split`]). `+`, `-`
/// and `*` keep the carrier, and the last arm's is the operands' where they agree. `/` keeps it
/// where no pattern is `is int` and the divisor is a nonzero literal; its last arm's carrier is
/// unknown where both operands are `int`s there, since `/` has no arrow at `int` (DESIGN
/// sec:lexical), and [`without_int`] has removed that arm wherever it could. `^` keeps it where
/// the exponent is a whole-number literal, in each arm an `int` or a float of the base's carrier
/// there (DESIGN sec:power: `int ^ k` is an `int` for `k ≥ 0`, `rat`, `f32` and `f64` to an `int`
/// power keep theirs). Elsewhere `(false, None)`: a literal following the operation then takes
/// the old path ([`Elab::follow`]), which keeps the value, one merge missed.
// Complexity tradeoff: O(C) for the C ≤ 4 arms of the divisor or exponent, against the O(C)
// arms `per_carrier` builds; a divisor or exponent that is an operation is not evaluated
// (that would be the build stage's work), so `1 / (2 + 1)` is built once per carrier but a
// literal following it takes the old path.
fn carried(p: Prim, own: [Option<Carrier>; 2], args: &[Term]) -> (bool, Option<Carrier>) {
    let [lo, ro] = own;
    let same = lo.filter(|_| lo == ro);
    let every = |t: &Term, f: &dyn Fn(&KPattern, &Value) -> bool| {
        arms_of(t)
            .is_some_and(|arms| (arms.iter()).all(|(q, t)| lit_value(t).is_some_and(|v| f(q, v))))
    };
    match p {
        Prim::Add | Prim::Sub | Prim::Mul => (true, same),
        Prim::Div => {
            let int = KPattern::Is(Carrier::Int.ty());
            let kept = arms_of(&args[0]).is_some_and(|a| a.iter().all(|(q, _)| *q != int))
                && every(&args[1], &|_, v| nonzero(v));
            let own = same.filter(|c| *c != Carrier::Int);
            (kept, own.filter(|_| kept))
        }
        Prim::Pow => {
            // The base's carrier in the arm `q`: `c` for `is c`, its own in the last arm.
            let at = |q: &KPattern, c: Carrier| match q {
                KPattern::Wild => lo == Some(c),
                q => *q == KPattern::Is(c.ty()),
            };
            let whole = |x: f64| x >= 0.0 && x.fract() == 0.0;
            let kept = every(&args[1], &|q, v| match v {
                Value::Int(k) => *k >= 0,
                Value::Big(k) => !k.is_negative(),
                Value::Float(x) => at(q, Carrier::F64) && whole(x.get()),
                Value::Float32(x) => at(q, Carrier::F32) && whole(f64::from(x.get())),
                _ => false,
            });
            (kept, lo.filter(|_| kept))
        }
        _ => (false, None),
    }
}

/// The two operands `args` of the arithmetic operator `p`, each built once per carrier on one
/// witness, laid out with no last arm at `int` where that arm could only stop: where their last
/// arms, of carriers `own`, give an `int` and a value of another carrier `c`, as `1 + 1.5` does,
/// or two `int`s under `/`, as `1 / 2` does (plan row STAGE-generic-fold-int-arm). The new
/// carriers of the last arms are returned, `own` where nothing changed.
///
/// The kernel has no `+`, `-`, `*` or `/` on an `int` and a value of another carrier, nor `/` on
/// two `int`s (`/` has no arrow at `int`, DESIGN sec:lexical; `zed_kernel::eval`), so a value of
/// the witness reaching that last arm would stop the program with a bug in zedc. The checker
/// accepts no such program but under `==` and `!=`: a decimal or a `/` among the literals
/// removes `int` from the class the witness belongs to (DESIGN step L1.26a), except under a
/// comparison, which keeps it (claim (2) below). The value
/// of every value of the witness that does reach the operation is unchanged: the operands are
/// laid out on the patterns of the one whose last arm is at `c` (at `/` on two `int`s, `c` is
/// `f64`, a decimal's own format), less `is c`, each taking its arm `is q` at each `is q`, and
/// its value at `c` (its last arm, or its arm `is c`) in the new last arm. Where an operand has
/// no arm for a pattern, nothing changes and the operation keeps its value, one merge missed.
// Complexity tradeoff: O(C²) pattern comparisons for the C ≤ 4 arms of each operand, against
// the O(C) arms `per_carrier` builds; each arm moved, not copied. Not taken: the checker giving
// these literals a value at another carrier in the last arm, as it gives `1.0` in `x == 1 / 2`;
// the arm is dropped rather than given a value no run should reach outside a comparison.
// The claim split (PROOF-sweep-front-end, FAIL-generic-eq-int-witness). (1) Every witness
// value of a carrier other than `int` gets the value it had: derived above, arm by arm. (2) An
// `int` value of the witness, or a value of no number, that reaches the new last arm gets the
// value DESIGN gives, in two cases. (2a) The operation is an operand of `==` or `!=` with the
// class, which keeps `int` in it (L1.26a, "without removing carriers from it"): the operation
// holds a `/` or a decimal, so it takes no value at `int` (`/` has no arrow at `int`, a
// decimal is never an `int`) and keeps its value at `c`, never an `int`, and the run compares
// the `int` with it, which `Value::surface_eq` gives as `false` whatever the two values
// (`number_eq`, numbers of two kinds), `true` under `!=`; a value of no number, as `"a"`, is
// unequal to every number (`param_follows`, `g("a")` with `x == 1 / 2`). That is the value of
// `x == 0.5` and of `x == 4 / 2` at an `int` (`l01_26a_generic_literals::param_follows`), and
// `x == 3 / 2 * 2` is `false` at `f(3)` though `3 / 2 * 2` is whole, as `x == 3.0` is; the declared
// `x: int` is refused, since at one declared carrier a literal takes it exactly or not at all. The
// old arm stopped there (`1 / 2` has no arrow at `int`), a bug in zedc. (2b) Any other use: the
// checker takes `int` out of the class and refuses the call at an `int`, so no `int` reaches the
// arm, a claim of the checker, not of this rewrite, tested for an `if` branch, a call's argument, a
// tuple, a list, `<` and the arithmetic operators. Row FAIL-generic-eq-int-witness proposed
// refusing the call at `int` under `==` too; not taken, since that would remove `int` from the
// class by a comparison. Evidence: `l01_26a_generic_literals::operations` (`FOLDED`, each body's
// value against a declared carrier; the two `int` tests) and `l25_08_mutate::examples`.
fn without_int(p: Prim, own: [Option<Carrier>; 2], args: &mut [Term]) -> [Option<Carrier>; 2] {
    use Carrier::{F64, Int};
    if !matches!(p, Prim::Add | Prim::Sub | Prim::Mul | Prim::Div) {
        return own;
    }
    let c = match own {
        [Some(Int), Some(Int)] if p == Prim::Div => F64,
        [Some(Int), Some(c)] | [Some(c), Some(Int)] if c != Int => c,
        _ => return own,
    };
    let is_c = KPattern::Is(c.ty());
    let from = own.iter().position(|o| *o == Some(c)).unwrap_or(0);
    let Some(arms) = arms_of(&args[from]) else {
        return own;
    };
    let target: Vec<KPattern> = (arms.iter())
        .map(|(q, _)| q.clone())
        .filter(|q| *q != KPattern::Wild && *q != is_c)
        .collect();
    // Each operand's arm for each pattern of `target`, then for the new last arm; every lookup
    // is made before any arm is moved, so a missing arm leaves both operands as they were.
    let mut picks = Vec::with_capacity(args.len());
    for (t, o) in args.iter().zip(own) {
        let Some(arms) = arms_of(t) else {
            return own;
        };
        let find = |q: &KPattern| arms.iter().position(|(a, _)| a == q);
        let last = match o == Some(c) {
            true => Some(arms.len() - 1),
            false => find(&is_c),
        };
        let Some(at) = target
            .iter()
            .map(find)
            .chain([last])
            .collect::<Option<Vec<_>>>()
        else {
            return own;
        };
        picks.push(at);
    }
    let patterns = target.into_iter().chain([KPattern::Wild]);
    for (t, at) in args.iter_mut().zip(picks) {
        let Term::Match(_, arms) = t else {
            unreachable!("each operand is a `match`, checked above")
        };
        let mut old: Vec<Option<Term>> = mem::take(arms).into_iter().map(|a| Some(a.1)).collect();
        *arms = (patterns.clone().zip(at))
            .map(|(q, i)| (q, old[i].take().expect("each arm picked once")))
            .collect();
    }
    [Some(c), Some(c)]
}

/// The arms of `t` when it is a `match` whose last arm matches every value, as the term of a
/// generic literal taking a carrier is ([`Elab::witnessed`], [`per_carrier`]).
fn arms_of(t: &Term) -> Option<&[(KPattern, Term)]> {
    match t {
        Term::Match(_, arms) if matches!(arms.last(), Some((KPattern::Wild, _))) => Some(arms),
        _ => None,
    }
}

/// The carrier of the literal `t`, marked or not ([`Elab::constant`]): `int` for an integer,
/// `f64` for a decimal or for an integer the checker reads as `f64`, as `1` in `1 / 2`, and
/// `rat` or `f32` for a literal that took that carrier from the operand it follows
/// ([`Elab::follow_split`]). `None` for any other term, and the operation is then not split,
/// which keeps its value (`Elab::follow`).
fn lit_carrier(t: &Term) -> Option<Carrier> {
    match lit_value(t)? {
        Value::Int(_) | Value::Big(_) => Some(Carrier::Int),
        Value::Rat(_) => Some(Carrier::Rat),
        Value::Float(_) => Some(Carrier::F64),
        Value::Float32(_) => Some(Carrier::F32),
        _ => None,
    }
}

/// The value of the literal `t`, marked or not ([`Elab::constant`]).
fn lit_value(t: &Term) -> Option<&Value> {
    let t = match t {
        Term::Prim(Prim::Neg, a) if mark_of(t).is_some() => &a[0],
        t => t,
    };
    match t {
        Term::Lit(v) => Some(v),
        _ => None,
    }
}

/// Whether the number `v` is not zero: a divisor that gives `/` a value of its carrier, not
/// `#divByZero` (DESIGN sec:power, author decision POW-domains).
fn nonzero(v: &Value) -> bool {
    match v {
        Value::Int(n) => *n != 0,
        Value::Big(r) | Value::Rat(r) => !r.is_zero(),
        Value::Float(x) => x.get() != 0.0,
        Value::Float32(x) => x.get() != 0.0,
        _ => false,
    }
}

/// The literal `v` at another carrier of the generic literal whose own term is `own`, marked
/// with `own`'s mark where `own` is a marked constant ([`Elab::constant`]): an arm of
/// [`Elab::witnessed`], [`Elab::follow`] or [`Elab::follow_split`], so that a mutant of the
/// constant replaces it in every arm, at each arm's carrier (L25.8, plan row
/// MUTATE-generic-constants). Unmarked elsewhere, as the elaboration without marks builds it.
// Complexity tradeoff: O(1), the mark one integer literal; a copy of `own` with its value set
// would copy the whole of `own` per arm where `own` is an operation, as an exponent `(1 + 1)`
// is.
fn marked_as(own: &Term, v: Value) -> Term {
    match own {
        Term::Prim(Prim::Neg, a) if mark_of(own).is_some() => {
            Term::Prim(Prim::Neg, vec![Term::Lit(v), a[1].clone()])
        }
        _ => Term::Lit(v),
    }
}

/// Whether the unary operator `p` on a value of one numeric carrier gives a value of that
/// carrier: negation does, and the others are left out, an operation on a split operand then
/// only missing a merge, never a wrong value. A binary operator: [`carried`].
fn keeps_carrier(p: Prim) -> bool {
    matches!(p, Prim::Add | Prim::Sub | Prim::Mul | Prim::Neg)
}

fn if_(c: Term, a: Term, b: Term) -> Term {
    Term::If(Shared::new(c), Shared::new(a), Shared::new(b))
}

/// `t`, a default's term at a call ([`Elab::defaults`]), with each name of `map` renamed: a
/// literal, a marked literal, a parameter's name, or a call of the default's own definition on
/// parameters' names, the shapes `Frame::FnDefault` makes.
fn renamed(t: &Term, map: &HashMap<Arc<str>, Arc<str>>) -> Term {
    let name = |x: &Arc<str>| map.get(x).unwrap_or(x).clone();
    match t {
        Term::Var(x) => Term::Var(name(x)),
        Term::App(f, args) => Term::App(
            f.clone(),
            (args.iter())
                .map(|a| match a {
                    Term::Var(x) => Term::Var(name(x)),
                    a => a.clone(),
                })
                .collect(),
        ),
        t => t.clone(),
    }
}

/// `call` where the arguments `xs` are in the domain `d` of the function it calls, and
/// `#notFound` elsewhere: the body of the lambda through which a function of exact arrows is
/// passed as a partial function type ([`Fit::Adapter`]; DESIGN.md sec:type_language,
/// "Morphism types carry two domain bounds"). The arguments are in it when some arrow's
/// parameter types each hold its argument, and each argument whose parameter declares a range
/// lies in it; the range is read only once the type test passed, since a range is declared
/// only on an `int` parameter.
///
/// Complexity tradeoff: the term has one type test per parameter per arrow and two
/// comparisons per ranged parameter, O(arrows · parameters) in size and at each call, each
/// test after the first false one skipped. A naive form that copied the miss into each
/// failing branch of nested matches would grow as the product of the arrows' sizes; the
/// conjunctions and the disjunction here are `if`s that give a boolean, so nothing is copied.
fn in_domain(d: &check::Domain, xs: &[Arc<str>], call: Term) -> Term {
    let yes = || Term::Lit(Value::Bool(true));
    let no = || Term::Lit(Value::Bool(false));
    let x = |j: usize| Term::Var(xs[j].clone());
    let is = |j: usize, k: &KType| {
        Term::Match(
            Shared::new(x(j)),
            vec![(KPattern::Is(k.clone()), yes()), (KPattern::Wild, no())],
        )
    };
    let and = |a: Term, b: Term| Term::If(Shared::new(a), Shared::new(b), Shared::new(no()));
    let typed = (d.arrows.iter()).rev().fold(no(), |rest, arrow| {
        let this = (arrow.iter().enumerate())
            .rev()
            .fold(yes(), |rest, (j, k)| and(is(j, k), rest));
        Term::If(Shared::new(this), Shared::new(yes()), Shared::new(rest))
    });
    let ranged = (d.ranges.iter().enumerate())
        .rev()
        .fold(yes(), |rest, (j, r)| {
            let Some(r) = r else { return rest };
            let le = |a: Term, b: Term| Term::Prim(Prim::Le, vec![a, b]);
            let low = r.low.clone().map(|v| le(Term::Lit(v), x(j)));
            let high = r.high.clone().map(|v| le(x(j), Term::Lit(v)));
            [low, high]
                .into_iter()
                .flatten()
                .rev()
                .fold(rest, |rest, t| and(t, rest))
        });
    Term::If(
        Shared::new(and(typed, ranged)),
        Shared::new(call),
        Shared::new(Term::Lit(Value::atom("notFound"))),
    )
}
