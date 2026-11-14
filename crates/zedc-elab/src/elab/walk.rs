//! Elaboration's walk over statements and expressions, on a heap stack: a unit nested as
//! deep as memory allows elaborates on a thread of any stack size.
//!
//! Each recursive call of the walk is a [`Job`]. What the caller does with the call's result
//! is a [`Frame`] pushed below the job, which reads the result from [`M::ret`] when the job
//! is done. A loop of calls is one frame that starts the next call each time it resumes, and
//! [`M::seq`] runs a list of expressions for the frame below it. The jobs run in the order
//! the calls of the recursive walk ran, and each stops where that walk returned early, so the
//! errors, the temporaries and the marks come out in the same order.

use std::collections::{BTreeSet, HashMap};
use std::mem;
use std::sync::Arc;

use zed_kernel::num::{FloatFormat, LiteralRounding, show_f32, show_f64};
use zed_kernel::types::Type as KType;
use zed_kernel::{Pattern as KPattern, Prim, Rat, Shared, Term, Value};

use zedc_base::rejection::not_yet;
use zedc_check::check::{self, Fit, Misfit};
use zedc_resolve::resolve::topo::topo;
use zedc_resolve::resolve::{Ref, prelude_layer};
use zedc_stage::defs::Test;
use zedc_syntax::ast::{
    BinaryOp, Error, Expr, ExprKind, Function, Note, Pattern, PortName, Stmt, StmtKind, StrPart,
    Target, TestPorts, UnaryOp,
};
use zedc_syntax::lex::{Span, unread_literal};

use super::mark::{Mark, mark_of, mutable};
use super::state::{Bind, Elab};
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
    /// A generic literal of [`check::Info::witness`], by its span, once elaborated: it takes
    /// the carrier of the value of the parameter of that binder.
    Witness(Span, &'a check::Witness),
    Binary(&'a Expr),
    Tuple,
    Is(&'a Expr),
    Else(&'a Expr),
    If,
    Str(&'a [StrPart]),
    Pass(Box<PassF<'a>>),
    PassCall(Box<PassF<'a>>),
    Block,
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
    Fill(Box<FillF<'a>>),
    ValueDefault(Box<FillF<'a>>),
    DeclDefault(Box<FillF<'a>>),
    MemberOf(Box<Member<'a>>),
    /// A member call made, wrapped for `?.` by the receiver's temporary and value.
    MemberEnd(Option<(Arc<str>, Term)>),
    IndexDeclared(usize, &'a Expr),
    Index(&'a Expr, Span),
    FitBody(Box<FitF<'a>>),
    FitExtras(Box<FitF<'a>>, Term),
    Lambda(Vec<Arc<str>>),
    /// An expression done, by its span: its term's nodes that have no site take this one
    /// (plan row RT-sites).
    Site(Span),
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
        while let Some(job) = m.stack.pop() {
            match job {
                Job::Expr(e) => {
                    if zed_kernel::sites::recording() {
                        m.k(Frame::Site(e.span));
                    }
                    self.expr(&mut m, e)
                }
                Job::Block(stmts) => {
                    m.k(Frame::Block);
                    self.start_scope(&mut m, stmts, false);
                }
                Job::Scope(stmts, top) => self.start_scope(&mut m, stmts, top),
                Job::K(f) => self.resume(&mut m, f),
            }
        }
        match m.take() {
            Ret::Scope(s) => s,
            _ => unreachable!("a scope's result"),
        }
    }

    fn start_scope(&mut self, m: &mut M<'a>, stmts: &'a [Stmt], top: bool) {
        let mut export = None;
        let mut items: Vec<&'a Stmt> = Vec::new();
        for s in stmts {
            match &s.kind {
                StmtKind::Return(es) => export = Some(&es[..]),
                _ => items.push(s.bare()),
            }
        }
        let mut order = match self.t.order(&items) {
            Ok(order) => order,
            Err(cycles) => {
                // The checker reports each cycle too, in the same words, and checks the rest of
                // the scope; a unit keeps one copy of each error.
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
            binds: Vec::new(),
            ok: true,
            export,
        };
        self.scope_step(m, Box::new(sf));
    }

    fn scope_step(&mut self, m: &mut M<'a>, mut sf: Box<ScopeF<'a>>) {
        if let Some(i) = sf.order.pop() {
            let (s, top) = (sf.items[i], sf.top);
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
            | StmtKind::Expr(_) => unreachable!("resolve rejects the forms of layer L6"),
            StmtKind::Bind { value, .. } => {
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
                };
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
            // The lexer has removed the `_` from a literal's digits, so they are read where they
            // are, not copied.
            ExprKind::Int { radix, digits, .. } => match Value::int_text(digits, *radix) {
                Ok(v) => Some(self.constant(e, v.expect("the lexer's digits"))),
                Err(r) => self.error(e.span, unread_literal(&r)),
            },
            // A literal with the suffix `f32` is read at `f32`; any other at `f64`, the format a
            // decimal no use fixes takes (DESIGN.md L1.26a).
            ExprKind::Float { digits: s, forced } => match Value::literal_float(s, *forced) {
                Ok(v) => lit(v),
                Err(LiteralRounding::Infinite) => {
                    let (f, max) = float_bounds(*forced, false);
                    self.error(
                        e.span,
                        format!(
                            "`{s}` is larger than the largest {f}, {max}, so as an {f} it rounds \
                             to infinity. Write `{s}r` for the exact rational, or a number \
                             within the range of {f}."
                        ),
                    )
                }
                Err(LiteralRounding::Zero) => {
                    let (f, least) = float_bounds(*forced, true);
                    self.error(
                        e.span,
                        format!(
                            "`{s}` is not zero, and it lies nearer to zero than to the least \
                             positive {f}, {least}, so as an {f} it rounds to zero. Write `{s}r` \
                             for the exact rational, or `0.0` if zero is meant."
                        ),
                    )
                }
                Err(LiteralRounding::TooLarge(_)) => {
                    unreachable!("a float literal is read with no memory asked for")
                }
            },
            ExprKind::Rat(s) => match Rat::decimal(s) {
                Ok(r) => lit(Value::rat(r.expect("the lexer's rat text is a decimal"))),
                Err(r) => self.error(e.span, unread_literal(&r)),
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
            ExprKind::Name(n) => self.name(n, e.span),
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
                        m.k(Frame::IndexDeclared(id, of));
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
                m.k(Frame::If);
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
        if let Some(id) = self.declared(callee) {
            let f = self.t.funcs[&id];
            self.call_with(m, Callee::Declared(id, f), None, call);
            return;
        }
        m.k(Frame::CallOf(call));
        m.stack.push(Job::Expr(callee));
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
        self.call_with(m, Callee::Value(f, sig), receiver, call);
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
                let t = self.misfit(call.span, Misfit::NoReceiver, &who);
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

    /// The next argument of a call, or what follows once they are all elaborated.
    fn fill(&mut self, m: &mut M<'a>, mut ff: Box<FillF<'a>>) {
        let n = ff.callee.len();
        if let Some(a) = ff.call.positional.get(ff.pi) {
            let t = if ff.next >= n {
                let who = ff.callee.who();
                self.misfit(a.span, Misfit::TooMany(n), &who)
            } else if let (name, false) = ff.callee.param(ff.next) {
                let who = ff.callee.who();
                self.misfit(a.span, Misfit::Named(name), &who)
            } else {
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
                    self.misfit(a.span, Misfit::NoParam(name), &who)
                }
                Some(j) if ff.callee.param(j).1 => {
                    let who = ff.callee.who();
                    self.misfit(a.span, Misfit::Positional(name), &who)
                }
                Some(j) if ff.slots[j].is_some() => {
                    let who = ff.callee.who();
                    self.misfit(a.span, Misfit::Supplied(name), &who)
                }
                Some(j) => {
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
                let name = ff.callee.param(j).0;
                let who = ff.callee.who();
                let t = self.misfit(span, Misfit::CurriedPositional(name), &who);
                m.give(t);
                return;
            }
            if ff.missing.is_empty() {
                let who = ff.callee.who();
                let t = self.misfit(span, Misfit::NothingLeftOut, &who);
                m.give(t);
                return;
            }
            let FillF {
                callee,
                slots,
                missing,
                ..
            } = *ff;
            let t = match callee {
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
                Callee::Declared(id, f) => {
                    let params = missing.iter().map(|&j| self.kname(&f.params[j])).collect();
                    let body = self.supplied(f, slots, Term::App(self.fv(id), self.param_vars(f)));
                    Term::Lam(params, Shared::new(body))
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
                Some((_, _, false)) => {
                    self.misfit(ff.call.span, Misfit::OpenDefault(&p.name), &sig.who())
                }
                None => self.misfit(
                    ff.call.span,
                    Misfit::Missing(&p.name, p.positional),
                    &sig.who(),
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
            m.give(Some(Term::App(self.fv(id), args)));
            return;
        }
        let mut ok = true;
        for &j in &ff.missing {
            if f.params[j].default.is_none() {
                ok = false;
                self.misfit::<()>(
                    ff.call.span,
                    Misfit::Missing(&f.params[j].name, f.params[j].positional),
                    fname,
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
                deps.sort_unstable();
                deps.dedup();
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
        let FillF {
            slots, defaults, ..
        } = *ff;
        let body = (defaults.into_iter().rev()).fold(
            Term::App(self.fv(id), self.param_vars(f)),
            |body, (k, d)| Term::Let(k, Shared::new(d), Shared::new(body)),
        );
        m.give(Some(self.supplied(f, slots, body)));
    }

    /// A parameter's kernel name.
    fn kname(&self, p: &Param) -> Arc<str> {
        self.names[self.id(p.span, &p.name)].clone()
    }

    /// The declared function `id`, as a term.
    fn fv(&self, id: usize) -> Shared {
        Shared::new(Term::Var(self.names[id].clone()))
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

    /// The call of [`Elab::member`], its receiver `x` elaborated.
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
            Some(Ref::Bound(ids)) if self.t.funcs.contains_key(&ids[0]) => {
                let (id, f) = (ids[0], self.t.funcs[&ids[0]]);
                m.k(Frame::MemberEnd(wrap));
                self.call_with(m, Callee::Declared(id, f), Some(receiver), call);
                return;
            }
            Some(Ref::Bound(ids)) => {
                let f = Term::Var(self.names[ids[0]].clone());
                m.k(Frame::MemberEnd(wrap));
                self.call_value(m, f, Some(receiver), call);
                return;
            }
            _ => match prelude_layer(name) {
                Some(1) => {
                    let f = Term::Var(name.into());
                    m.k(Frame::MemberEnd(wrap));
                    self.call_value(m, f, Some(receiver), call);
                    return;
                }
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
                            ),
                        }],
                    });
                    m.give(None);
                    return;
                }
                None => {
                    format!(
                        "`{name}` is not a function in scope, and reading a field with `.{name}` \
                         is part of the Zed language that this version of zedc does not compile \
                         yet. Call a function in scope, or correct the name if it is misspelled."
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
            (Fit::Adapter { from }, _) => {
                let ExprKind::Name(n) = &e.kind else {
                    unreachable!("an adapter is recorded on a name")
                };
                let t = self.name(n, e.span).map(|f| {
                    let temps: Vec<Arc<str>> = from.iter().map(|_| self.temp()).collect();
                    let args = from.iter().map(|&j| Term::Var(temps[j].clone())).collect();
                    Term::Lam(temps, Shared::new(Term::App(Shared::new(f), args)))
                });
                m.give(t);
            }
            _ => unreachable!("a lambda fit is recorded on a lambda"),
        }
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
            Frame::If => {
                let t = all(m.got()).map(|ts| {
                    let [c, a, b]: [Term; 3] = ts.try_into().expect("three terms");
                    if_(c, a, b)
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
            Frame::Block => {
                let Ret::Scope(s) = m.take() else {
                    unreachable!("a scope's result")
                };
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
                match binds {
                    Some(binds) => sf.binds.extend(binds),
                    None => sf.ok = false,
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
                    id,
                    params,
                    thunks,
                    ok,
                    body,
                    ..
                } = *ff;
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
                        let kernel = self.names[tf.id].clone();
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
            Frame::IndexDeclared(id, of) => {
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
                                        ),
                                    }],
                                });
                                None
                            }
                            1 => Some(Term::App(self.fv(id), vec![k])),
                            n => {
                                let rest: Vec<Arc<str>> = (1..n).map(|_| self.temp()).collect();
                                let mut args = vec![k];
                                args.extend(rest.iter().map(|r| Term::Var(r.clone())));
                                Some(Term::Lam(rest, Shared::new(Term::App(self.fv(id), args))))
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
                let t = all(m.got()).map(|ts| {
                    let [v, i]: [Term; 2] = ts.try_into().expect("two terms");
                    match &k.kind {
                        _ if dense => Term::Prim(Prim::At, vec![v, i]),
                        ExprKind::Int { .. } => Term::Prim(Prim::TupleGet, vec![v, i]),
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

    /// A binary operator's term, its operands elaborated.
    fn binary(&mut self, e: &'a Expr, got: Vec<Option<Term>>) -> Option<Term> {
        let ExprKind::Binary(op, l, r) = &e.kind else {
            unreachable!("a binary operator")
        };
        let [a, b]: [Option<Term>; 2] = got.try_into().expect("two operands");
        let (a, b) = (a?, b?);
        let t = |v: bool| Term::Lit(Value::Bool(v));
        let p = match *op {
            BinaryOp::Or => return Some(if_(a, t(true), b)),
            BinaryOp::And => return Some(if_(a, b, t(false))),
            BinaryOp::Eq => Prim::Eq,
            BinaryOp::Ne => Prim::Ne,
            BinaryOp::Lt => Prim::Lt,
            BinaryOp::Le => Prim::Le,
            BinaryOp::Gt => Prim::Gt,
            BinaryOp::Ge => Prim::Ge,
            BinaryOp::Add => Prim::Add,
            BinaryOp::Sub => Prim::Sub,
            BinaryOp::Mul => Prim::Mul,
            BinaryOp::Div => Prim::Div,
            BinaryOp::IntDiv => Prim::IntDiv,
            BinaryOp::Mod => Prim::Mod,
            BinaryOp::Pow => Prim::Pow,
            BinaryOp::Concat => Prim::Concat,
        };
        let mut args = vec![a, b];
        if let Some(marks) = &mut self.marks
            && mutable(p)
        {
            args.push(Term::Lit(Value::Int(marks.len() as i64)));
            marks.push(Mark {
                span: Span {
                    start: l.span.end,
                    end: r.span.start,
                },
                quotient: self.info.quotients.get(&e.span) == Some(&true),
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
        let own = Some(self.own_carrier(l, &args[0]))
            .filter(|c| keeps_carrier(p) && *c == self.own_carrier(r, &args[1]))
            .flatten();
        Some(match per_carrier(p, args, 2) {
            Ok(t) => {
                self.split
                    .insert(e.span, (w, keeps && keeps_carrier(p), own));
                t
            }
            Err(args) => Term::Prim(p, args),
        })
    }

    /// Whether the operand `o` at `args[at]` is a literal that takes the carrier of the other
    /// operand's value (`Info::follows`), the other operand being split on `w` with each arm
    /// `is c` of carrier `c` ([`Elab::split`]) and the literal's carriers the patterns of those
    /// arms; if so, `args[at]` becomes the literal taking the carrier of `w`'s value instead,
    /// which picks in every case the value [`Elab::follow`] would pick, and both operands are then
    /// split on `w`. `2 + 0` in a generic definition is such a case: the checker gives `2` the
    /// parameter as its witness and has `0` follow `2`. `other` is the carrier of the value of
    /// the other operand's last arm, and without it the operand is not split.
    ///
    /// The same value: where `w`'s value is of a carrier `c` of the patterns, the other operand's
    /// value is of carrier `c` and the literal takes its value at `c` either way; elsewhere the
    /// other operand's value is that of its last arm, of carrier `other`, and the literal takes
    /// its value at `other` where `Info::follows` lists it and keeps its own value elsewhere,
    /// as `follow` does. That carrier is not always the literal's own: in `1 / 2` the checker
    /// gives `1` the value `1.0` at a value of no carrier of the patterns, as `/` takes no
    /// `int`, and `2`, following it, then takes `2.0`.
    // Complexity tradeoff: O(C) pattern comparisons for C ≤ 6 carriers, against the O(C) arms
    // `follow` builds anyway; the `let` of `follow` is not built.
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
        let same = arms.len() == values.len() + 1
            && (values.iter().zip(arms)).all(|((c, _), (q, _))| *q == KPattern::Is(c.ty()));
        if same {
            let own = mem::replace(&mut args[at], Term::Lit(Value::Bool(false)));
            let own = match values.iter().find(|(c, _)| *c == other) {
                Some((_, v)) => with_value(own, v.clone()),
                None => own,
            };
            args[at] = self.witnessed(s, w, own);
        }
        same
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
        let Some((w, keeps)) = w else {
            return Term::Prim(p, vec![a]);
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
        let mut arms: Vec<(KPattern, Term)> = values
            .iter()
            .map(|(c, v)| (KPattern::Is(c.ty()), Term::Lit(v.clone())))
            .collect();
        // The literal's own term, which a marked elaboration marks, is the last arm.
        let own = mem::replace(&mut args[at], Term::Var(other.clone()));
        arms.push((KPattern::Wild, own));
        args[at] = Term::Match(Shared::new(Term::Var(other.clone())), arms);
        Term::Let(other, Shared::new(x), Shared::new(Term::Prim(p, args)))
    }

    /// The generic literal at `s`, of term `own`, taking the carrier of the value of `w`, a
    /// parameter or a component of one (L1.26a): its value at each carrier of
    /// [`check::Info::follows`] that the value of `w` has, else its own.
    fn witnessed(&mut self, s: Span, w: &check::Witness, own: Term) -> Term {
        let mut arms: Vec<(KPattern, Term)> = self.info.follows[&s]
            .iter()
            .map(|(c, v)| (KPattern::Is(c.ty()), Term::Lit(v.clone())))
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
                items,
                ..
            }) if fields.is_empty() && items.is_empty() => {
                Some(Some(KPattern::Is(check::any_payload(name))))
            }
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
        let StmtKind::Bind { targets, .. } = &s.kind else {
            unreachable!("a binding")
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

/// The arms of `t` when it is a `match` whose last arm matches every value, as the term of a
/// generic literal taking a carrier is ([`Elab::witnessed`], [`per_carrier`]).
fn arms_of(t: &Term) -> Option<&[(KPattern, Term)]> {
    match t {
        Term::Match(_, arms) if matches!(arms.last(), Some((KPattern::Wild, _))) => Some(arms),
        _ => None,
    }
}

/// The carrier of the literal `t`, marked or not ([`Elab::constant`]), where it is one a
/// generic literal's own value has: `int` for an integer, `f64` for a decimal or for an
/// integer the checker reads as `f64`, as `1` in `1 / 2`. `None` for any other term, and the
/// operation is then not split, which keeps its value (`Elab::follow`).
fn lit_carrier(t: &Term) -> Option<Carrier> {
    let t = match t {
        Term::Prim(Prim::Neg, a) if mark_of(t).is_some() => &a[0],
        t => t,
    };
    match t {
        Term::Lit(Value::Int(_) | Value::Big(_)) => Some(Carrier::Int),
        Term::Lit(Value::Float(_)) => Some(Carrier::F64),
        _ => None,
    }
}

/// The literal `own`, a constant's term ([`Elab::constant`]), with the value `v`: marked as
/// `own` is, so that a mutant of the constant replaces it (L25.8).
fn with_value(mut own: Term, v: Value) -> Term {
    if mark_of(&own).is_some()
        && let Term::Prim(Prim::Neg, a) = &mut own
    {
        a[0] = Term::Lit(v);
        return own;
    }
    Term::Lit(v)
}

/// Whether `p` on values of one numeric carrier gives a value of that carrier: `+`, `-`, `*`
/// and negation do; `/` on two `int`s gives a `rat`, a comparison a `bool`, and the others are
/// left out, an operation on a split operand then only missing a merge, never a wrong value.
fn keeps_carrier(p: Prim) -> bool {
    matches!(p, Prim::Add | Prim::Sub | Prim::Mul | Prim::Neg)
}

fn if_(c: Term, a: Term, b: Term) -> Term {
    Term::If(Shared::new(c), Shared::new(a), Shared::new(b))
}

/// The name of the format a float literal with the suffix `forced` is read at, and its largest
/// finite value, or its least positive one when `least`, as a message names them.
fn float_bounds(forced: Option<FloatFormat>, least: bool) -> (&'static str, String) {
    match (forced, least) {
        (Some(FloatFormat::F32), false) => ("f32", show_f32(f32::MAX)),
        (Some(FloatFormat::F32), true) => ("f32", show_f32(f32::from_bits(1))),
        (_, false) => ("f64", show_f64(f64::MAX)),
        (_, true) => ("f64", show_f64(f64::from_bits(1))),
    }
}
