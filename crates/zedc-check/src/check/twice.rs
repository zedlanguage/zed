//! Two pushes to one port in one run (DESIGN.md step L1.19, plan row PORT-push-twice-static):
//! "two pushes to one port that may both run in one wave are rejected at compile time, at the
//! second push, since keyed and multi-site pushes arrive at step L7.2, and a wave never stops
//! for a push the checker could have counted. The count is taken along each path of `main`'s
//! body: a block adds the counts of its statements, an `if` or `match` takes the largest count
//! among its branches, and a call of a function with an output port parameter counts the
//! pushes the function's body makes to that parameter, so two push sites on two branches of
//! one `if` or `match` are one push and are accepted, while two `if` statements whose
//! conditions exclude each other are counted as two and are rejected; the message names both
//! pushes and the port, and its menu offers one family of strings pushed once, and one `if` or
//! `match` whose branches each push once."
//!
//! A path's count of a port is 0 or 1 here: the state of a path is the first push to each port
//! on it, and a push that meets one already there is the second, rejected where it stands. The
//! largest count of two branches is then the union of their states. Each function with an
//! output port parameter is walked the same way, its parameters standing for ports: a second
//! push in its body is rejected there, and a call of it pushes, at the call, to the port each
//! parameter it pushes to is given. Three cases the rule's text leaves open, each read as
//! "may both run in one wave":
//! - the body of a `for` or a `loop` may run more than once, so a push in it meets
//!   itself;
//! - an operand of an `else` and its default may both run, so they are walked one after the
//!   other, the default as a branch that may not run;
//! - a call of a function whose count is being taken (a recursive call) pushes once to each
//!   of its output ports, the least a call that pushes can do: `f` pushing and then calling
//!   itself is rejected, `f` pushing in one branch and calling itself in the other is not.
//!   The run's own guard (`crates/zedc/src/run.rs`) still stops a run that pushes twice past
//!   these counts, as a bug in zedc.
//!
//! This zedc refuses `match`, `for` and `loop` before the check (`zedc-resolve`, "not supported
//! by this version of zedc"), so the walk of their arms and bodies here is reached by no
//! program yet and has no test of its own; it is kept so that the rule holds when they are
//! compiled, and those steps add its tests.
//!
//! The body of a lambda is not walked: [`super::ports::ports`] rejects a function with output
//! port parameters named other than as a callee, so a lambda reaches no port.
//!
//! Complexity tradeoff: naive, a call is walked through its callee's body at each call, O(size
//! of the callee) per call and exponential in the depth of nested calls; used, each function's
//! pushes are found once (memoized by its binder, the in-progress mark breaking cycles) and a
//! call applies them, O(output port parameters of the callee) per call.
//!
//! A path's state is one map of the ports pushed on it, changed in place, each change logged.
//! Naive, the map is copied at each branch, O(P) per branch for P ports pushed, O(size · P) in
//! all, the square of the text for a function of many output port parameters each pushed in an
//! `if` of its own. Used: the branches of an `if` or `match` are walked one after another on
//! the one map; each but the longest in the text has its changes undone at its end, from the
//! log, and added again at the join, and the longest is walked last and its changes kept. A
//! push undone and added again lies in a branch at most half as long as the branches around
//! it, so it is moved at most log2(size) times, and the walk is O(size log size) (the
//! heavy-path argument of Sleator and Tarjan, "A data structure for dynamic trees", J. Comput.
//! Syst. Sci. 26(3), 1983, doi:10.1016/0022-0000(83)90006-5). A loop body is walked once, not
//! twice: a second walk would meet only the pushes the first one added, each at itself, so
//! those, read from the log past the loop's start, are pushed again directly, where walking
//! each body twice costs 2^d walks of a body nested d loops deep. A loop around another reads
//! past the part of the log the inner one read ([`Walk::looped`]): each push there was pushed
//! again already, and again would give the same error at the same place. So each entry of the
//! log is read by one loop end, O(size log size) with the moves at joins. Measured by
//! `bench::many_ports_each_pushed_in_an_if_are_counted_in_n_log_n_time` in the l01_19 benches.
//!
//! The walk runs from an explicit stack of tasks, not the call stack: an expression nested
//! 100,000 deep, or a chain of 4,000 helpers each calling the next (`statement_chain` in the
//! l01_19 benches), would overflow it. A call of a function not yet
//! summed up puts the walk of that function's body on the same stack, the caller's path saved,
//! and is taken again when the sum is known.

use std::collections::{HashMap, HashSet};

use zedc_resolve::resolve::tables::Tables;
use zedc_resolve::resolve::{Kind, NamedCall, Ref};
use zedc_syntax::ast::{Expr, ExprKind, Function, Note, Stmt, StmtKind, StrPart};
use zedc_syntax::lex::Span;

use super::ports::Ports;

/// A push: its text and the text the message names the port by.
type Pushed = (Span, String);

/// The first push on a path to each port, by the port's binder.
type Path = HashMap<usize, Pushed>;

/// Each change to a [`Path`] in the order made: the port and the push it replaced, or `None`
/// where the port was added.
type Log = Vec<(usize, Option<Pushed>)>;

/// Parts of a [`Log`], each from its first index up to its second.
type Parts = Vec<(usize, usize)>;

/// Each second push to one port in one run in the unit whose tables are `t`, as an error: its
/// place, its headline and its notes.
pub fn twice<'a>(t: &Tables<'a>, ports: &Ports) -> Vec<(Span, String, Vec<Note>)> {
    let mut w = Walk {
        t,
        ports,
        calls: t.res.calls.iter().map(|c| (c.span, c)).collect(),
        done: HashMap::new(),
        busy: HashSet::new(),
        errors: Vec::new(),
        reported: HashSet::new(),
        tasks: Vec::new(),
        path: Path::new(),
        log: Vec::new(),
        forks: Vec::new(),
        loops: Vec::new(),
        looped: Vec::new(),
        callers: Vec::new(),
    };
    for (&f, &decl) in &t.funcs {
        let decl: &'a Function = decl;
        if decl.main.is_some() {
            w.path = Path::new();
            w.log.clear();
            w.looped.clear();
            w.tasks.push(Task::Expr(&decl.body));
            w.run();
        } else if ports.writers.contains(&f) && !w.done.contains_key(&f) {
            w.enter(f);
            w.run();
        }
    }
    w.errors.sort_by_key(|e| (e.0.start, e.0.end));
    w.errors
}

/// A step of the walk, taken from the stack [`Walk::tasks`].
enum Task<'a> {
    Expr(&'a Expr),
    Stmt(&'a Stmt),
    /// The push of the statement, its value walked.
    Push(&'a Stmt, &'a str),
    /// The call at this place, its callee and arguments walked.
    Call(Span),
    /// The start of branches: the path now is where each begins.
    Fork,
    /// The end of one branch.
    Arm,
    /// The end of the branches: the path is the union of theirs.
    Join,
    /// The start and the end of a loop's body.
    LoopStart,
    LoopEnd,
    /// The start and the end of the body of the function, whose pushes are summed up.
    FnStart(usize),
    FnEnd(usize),
}

struct Walk<'t, 'a> {
    t: &'t Tables<'a>,
    ports: &'t Ports,
    /// Each call whose callee is a name, by the text of the call.
    calls: HashMap<Span, &'a NamedCall>,
    /// The output port parameters each function pushes to on some path of its body, with the
    /// first such push, by the function's binder.
    done: HashMap<usize, Vec<(usize, Span)>>,
    /// The functions whose pushes are being found.
    busy: HashSet<usize>,
    errors: Vec<(Span, String, Vec<Note>)>,
    /// The second pushes already rejected, so that a function reached again rejects each once.
    reported: HashSet<Span>,
    tasks: Vec<Task<'a>>,
    /// The path the walk is on.
    path: Path,
    /// Each change to [`Self::path`] in the order made, with the value it replaced, so that a
    /// branch's changes are undone by popping them.
    log: Log,
    /// For each `Fork` not yet joined: the length of the log where its branches begin, and the
    /// pushes the branches ended so far added, each branch's undone at its end.
    forks: Vec<(usize, Vec<(usize, Pushed)>)>,
    /// For each loop body being walked: the length of the log where it begins.
    loops: Vec<usize>,
    /// The parts of the log the end of a loop has read, in order and apart: a loop around it
    /// reads past them, since each push there was already pushed again.
    looped: Parts,
    /// For each function body being walked: the path, log and parts read of the walk it
    /// interrupted.
    callers: Vec<(Path, Log, Parts)>,
}

impl<'a> Walk<'_, 'a> {
    /// Puts the walk of the body of the function `f` on the stack.
    fn enter(&mut self, f: usize) {
        let decl: &'a Function = self.t.funcs[&f];
        self.tasks
            .extend([Task::FnEnd(f), Task::Expr(&decl.body), Task::FnStart(f)]);
    }

    /// The output port parameters the function `f`, being summed up, pushes to on some path of
    /// its body: for a recursive call, each of them, once (module comment).
    fn recursive(&self, f: usize) -> Vec<(usize, Span)> {
        let t = self.t;
        (t.funcs[&f].params.iter())
            .filter_map(|p| t.ids.get(&(p.span, p.name.as_str())).copied())
            .filter(|b| self.ports.params.contains(b))
            .map(|b| (b, t.funcs[&f].body.span))
            .collect()
    }

    /// Takes the tasks until the stack is empty.
    fn run(&mut self) {
        while let Some(task) = self.tasks.pop() {
            match task {
                Task::Expr(e) => self.expr(e),
                Task::Stmt(s) => self.stmt(s),
                Task::Push(s, port) => {
                    // A generation's push `x' <- v` writes no port.
                    if !port.ends_with('\'')
                        && let Some(b) = self.port_at(s.span)
                    {
                        self.push(b, port.to_string(), s.span);
                    }
                }
                Task::Call(at) => self.call(at),
                Task::Fork => self.forks.push((self.log.len(), Vec::new())),
                Task::Arm => {
                    let mark = self.forks.last().expect("an open fork").0;
                    // Each port is added once after the mark: a branch inside that undid it
                    // also popped its entry.
                    let added: Vec<(usize, Pushed)> = (self.log[mark..].iter())
                        .filter(|(_, old)| old.is_none())
                        .map(|&(b, _)| (b, self.path[&b].clone()))
                        .collect();
                    self.undo(mark);
                    self.forks.last_mut().expect("an open fork").1.extend(added);
                }
                Task::Join => {
                    // The union keeps, for a port pushed on several branches, the first of
                    // those pushes in the text, the one the message names.
                    let (_, ended) = self.forks.pop().expect("an open fork");
                    for (b, v) in ended {
                        match self.path.get(&b) {
                            None => {
                                self.path.insert(b, v);
                                self.log.push((b, None));
                            }
                            Some(now) if v.0.start < now.0.start => {
                                let old = self.path.insert(b, v);
                                self.log.push((b, old));
                            }
                            Some(_) => {}
                        }
                    }
                }
                Task::LoopStart => self.loops.push(self.log.len()),
                Task::LoopEnd => {
                    let mark = self.loops.pop().expect("an open loop");
                    let mut parts = Vec::new();
                    let mut end = self.log.len();
                    while let Some(&(a, z)) = self.looped.last()
                        && a >= mark
                    {
                        self.looped.pop();
                        parts.push((z, end));
                        end = a;
                    }
                    parts.push((mark, end));
                    let added: Vec<(usize, Pushed)> = (parts.into_iter().rev())
                        .flat_map(|(a, z)| self.log[a..z].iter())
                        .filter(|(_, old)| old.is_none())
                        .map(|&(b, _)| (b, self.path[&b].clone()))
                        .collect();
                    for (b, (s, name)) in added {
                        self.push(b, name, s);
                    }
                    self.looped.push((mark, self.log.len()));
                }
                Task::FnStart(f) => {
                    self.busy.insert(f);
                    self.callers.push((
                        std::mem::take(&mut self.path),
                        std::mem::take(&mut self.log),
                        std::mem::take(&mut self.looped),
                    ));
                }
                Task::FnEnd(f) => {
                    let (caller, log, looped) = self.callers.pop().expect("an open function");
                    self.log = log;
                    self.looped = looped;
                    let p = std::mem::replace(&mut self.path, caller);
                    let mut pushed: Vec<(usize, Span)> =
                        p.into_iter().map(|(b, (s, _))| (b, s)).collect();
                    pushed.sort_unstable_by_key(|&(b, s)| (s.start, b));
                    self.busy.remove(&f);
                    self.done.insert(f, pushed);
                }
            }
        }
    }

    /// Undoes the changes to the path past the log's length `mark`.
    fn undo(&mut self, mark: usize) {
        while self.log.len() > mark {
            let (b, old) = self.log.pop().expect("an entry past the mark");
            match old {
                Some(v) => self.path.insert(b, v),
                None => self.path.remove(&b),
            };
        }
        // A loop read past the mark lies in the branch undone: a loop around the branch ends
        // after it.
        while self.looped.last().is_some_and(|&(a, _)| a >= mark) {
            self.looped.pop();
        }
    }

    /// A push at `at` to the port `b`, named `name`, on the path of the walk.
    fn push(&mut self, b: usize, name: String, at: Span) {
        let Some((first, _)) = self.path.get(&b).cloned() else {
            self.path.insert(b, (at, name));
            self.log.push((b, None));
            return;
        };
        if !self.reported.insert(at) {
            return;
        }
        let text = self.t.text;
        let code = |s: Span| {
            text.and_then(|x| x.get(s.start..s.end))
                .filter(|c| !c.contains('\n'))
                .map_or_else(String::new, |c| format!(" `{c}`"))
        };
        let pushes = if first == at {
            format!(
                "more than once in one run: the push{} lies in a loop",
                code(at)
            )
        } else {
            format!(
                "twice in one run: by{} and then by{}",
                code(first),
                code(at)
            )
        };
        self.errors.push((
            at,
            format!(
                "`{name}` may be pushed to {pushes}, and a port takes one push per run, which \
                 holds everything it writes."
            ),
            vec![
                Note {
                    span: first,
                    text: format!("the first push to `{name}`").into(),
                },
                Note {
                    span: at,
                    text: format!(
                        "repair: gather the lines into one family of strings and push it once, \
                         as `{name} <- lines;`"
                    )
                    .into(),
                },
                Note {
                    span: at,
                    text: "repair: one `if` or `match` whose branches each push once".into(),
                },
            ],
        ));
    }

    /// The port of `main`, or the output port parameter, that the name used at `s` names.
    fn port_at(&self, s: Span) -> Option<usize> {
        let Some(Ref::Bound(ids)) = self.t.res.uses.get(&s) else {
            return None;
        };
        let b = ids[0];
        (self.t.res.binders[b].kind == Kind::Port || self.ports.params.contains(&b)).then_some(b)
    }

    /// Puts on the stack the walk of the branches `arms`, each from the path where they begin,
    /// then the union of their pushes, the largest count of each port among them. With one
    /// arm, the other branch is one that pushes nothing. The longest branch in the text is
    /// walked last and its pushes kept; each other one's are undone at its end and added again
    /// at the join (module comment).
    fn branches(&mut self, arms: impl Iterator<Item = &'a Expr>) {
        let arms: Vec<&'a Expr> = arms.collect();
        let long = (0..arms.len()).max_by_key(|&i| arms[i].span.end - arms[i].span.start);
        self.tasks.push(Task::Join);
        if let Some(i) = long {
            self.tasks.push(Task::Expr(arms[i]));
        }
        for j in (0..arms.len()).rev().filter(|&j| Some(j) != long) {
            self.tasks.extend([Task::Arm, Task::Expr(arms[j])]);
        }
        self.tasks.push(Task::Fork);
    }

    /// Puts on the stack the walk of `es` in order: the first is taken first.
    fn exprs(&mut self, es: impl DoubleEndedIterator<Item = &'a Expr>) {
        self.tasks.extend(es.rev().map(Task::Expr));
    }

    fn stmt(&mut self, s: &'a Stmt) {
        match &s.kind {
            StmtKind::Bind { value, .. } => self.tasks.push(Task::Expr(value)),
            StmtKind::Initial(i) => self.tasks.push(Task::Expr(&i.value)),
            StmtKind::Local(s) => self.tasks.push(Task::Stmt(s)),
            StmtKind::IndexedDef(d) => self.tasks.push(Task::Expr(&d.value)),
            StmtKind::While(e) | StmtKind::Until(e) | StmtKind::Expr(e) => {
                self.tasks.push(Task::Expr(e));
            }
            StmtKind::Return(es) => self.exprs(es.iter()),
            StmtKind::Push { port, value } => {
                self.tasks
                    .extend([Task::Push(s, port.as_str()), Task::Expr(value)]);
            }
            StmtKind::Annotated { decl, .. } => self.tasks.push(Task::Stmt(decl)),
            StmtKind::Break
            | StmtKind::Function(_)
            | StmtKind::Struct(_)
            | StmtKind::Type(_)
            | StmtKind::Method(_)
            | StmtKind::Import(_)
            | StmtKind::UnitAnnot(_) => {}
        }
    }

    /// Puts on the stack the walk of `e`, its parts in the order they run.
    fn expr(&mut self, e: &'a Expr) {
        match &e.kind {
            ExprKind::Int { .. }
            | ExprKind::Float { .. }
            | ExprKind::Rat(_)
            | ExprKind::Bool(_)
            | ExprKind::Atom(_)
            | ExprKind::Name(_)
            | ExprKind::This
            | ExprKind::Lambda { .. }
            | ExprKind::SortKey { key: None, .. } => {}
            ExprKind::Str(parts) => {
                let holes: Vec<&'a Expr> = (parts.iter())
                    .filter_map(|part| match part {
                        StrPart::Hole(h) => Some(h),
                        _ => None,
                    })
                    .collect();
                self.exprs(holes.into_iter());
            }
            ExprKind::Unary(_, a)
            | ExprKind::Member { of: a, .. }
            | ExprKind::Is { of: a, .. }
            | ExprKind::Read { of: a, .. }
            | ExprKind::Section(_, a)
            | ExprKind::Spread { of: a, .. }
            | ExprKind::SortKey { key: Some(a), .. } => self.tasks.push(Task::Expr(a)),
            ExprKind::Binary(_, a, b)
            | ExprKind::Index(a, b)
            | ExprKind::In { of: a, set: b, .. }
            | ExprKind::Reduce { of: a, op: b } => self.exprs([&**a, &**b].into_iter()),
            ExprKind::Range(a, end) => {
                self.exprs(
                    [Some(&**a), end.bound().map(|v| &**v)]
                        .into_iter()
                        .flatten(),
                );
            }
            ExprKind::Tuple(es) | ExprKind::Array(es) | ExprKind::Set(es) => {
                self.exprs(es.iter());
            }
            ExprKind::Record(fs) => self.exprs(fs.iter().map(|(_, x)| x)),
            ExprKind::Map(kvs) => self.exprs(kvs.iter().flat_map(|(k, v)| [k, v])),
            ExprKind::With { of, updates } => {
                self.exprs(std::iter::once(&**of).chain(updates.iter().map(|u| &u.value)));
            }
            ExprKind::Remap { of, levels, .. } => {
                let parts = (levels.iter().flatten()).flat_map(|l| l.key.iter().chain(&l.reduce));
                let all: Vec<&'a Expr> = std::iter::once(&**of).chain(parts).collect();
                self.exprs(all.into_iter());
            }
            ExprKind::Block(ss) => self.tasks.extend(ss.iter().rev().map(Task::Stmt)),
            ExprKind::If {
                cond,
                then,
                otherwise,
            } => {
                self.branches([&**then, &**otherwise].into_iter());
                self.tasks.push(Task::Expr(cond));
            }
            ExprKind::Match { of, arms } => {
                self.branches(arms.iter().map(|a| &a.body));
                // A guard runs before its arm's body is chosen; counted on the path before
                // the arms, as a push in a guard may run whichever arm is taken.
                let guards = arms.iter().filter_map(|a| a.guard.as_ref());
                let all: Vec<&'a Expr> = std::iter::once(&**of).chain(guards).collect();
                self.exprs(all.into_iter());
            }
            ExprKind::Else { of, default, .. } => {
                // The default runs after its operand, or not at all: one arm, the other
                // pushing nothing.
                self.branches(std::iter::once(&**default));
                self.tasks.push(Task::Expr(of));
            }
            ExprKind::For {
                source,
                guard,
                body,
                ..
            } => {
                self.tasks.push(Task::LoopEnd);
                self.exprs(guard.as_deref().into_iter().chain([&**body]));
                self.tasks.extend([Task::LoopStart, Task::Expr(source)]);
            }
            ExprKind::Loop { body, .. } => {
                self.tasks
                    .extend([Task::LoopEnd, Task::Expr(body), Task::LoopStart]);
            }
            ExprKind::Call {
                callee,
                positional,
                named,
                ..
            } => {
                self.tasks.push(Task::Call(e.span));
                let args = positional.iter().chain(named.iter().map(|(_, x)| x));
                let all: Vec<&'a Expr> = std::iter::once(&**callee).chain(args).collect();
                self.exprs(all.into_iter());
            }
        }
    }

    fn callees(&self, c: &NamedCall) -> impl Iterator<Item = usize> + '_ {
        let ids = match self.t.res.uses.get(&c.callee) {
            Some(Ref::Bound(ids)) => Some(ids),
            _ => None,
        };
        ids.into_iter().flat_map(|ids| ids.iter().copied())
    }

    /// The call at `at`, of a function with output port parameters: a push, at the call, to
    /// the port given to each parameter the function pushes to. Where a callee is not yet
    /// summed up, its body's walk is put on the stack, then this call again.
    fn call(&mut self, at: Span) {
        let Some(&c) = self.calls.get(&at) else {
            return;
        };
        let fs: Vec<usize> = self
            .callees(c)
            .filter(|f| self.ports.writers.contains(f))
            .collect();
        if let Some(&f) = (fs.iter()).find(|f| !self.done.contains_key(f) && !self.busy.contains(f))
        {
            self.tasks.push(Task::Call(at));
            self.enter(f);
            return;
        }
        for f in fs {
            let pushed = match self.done.get(&f) {
                Some(d) => d.clone(),
                None => self.recursive(f),
            };
            for (q, _) in pushed {
                let Some(&arg) = self.ports.args.get(&(at, q)) else {
                    continue;
                };
                let Some(b) = self.port_at(arg) else {
                    continue;
                };
                let name = (self.t.text)
                    .and_then(|x| x.get(arg.start..arg.end))
                    .map_or_else(|| self.t.res.binders[b].name.clone(), str::to_string);
                self.push(b, name, at);
            }
        }
    }
}
