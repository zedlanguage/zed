//! Staging (DESIGN.md sec:staging, step L1.28): which terms the build evaluates, and when
//! the build specializes a function on the values of a parameter.
//!
//! A term is a build-stage term when every name it reads is a build-stage definition or a
//! prelude word and it reads no port; a port input and a function parameter are run-stage.
//! `mix` evaluates the demanded build-stage terms to literals and leaves the rest to run.
//! A term is demanded when the residual program or a test reads it, so a definition nothing
//! reads is never evaluated, and a diverging one cannot stop the build. A build-stage term
//! whose evaluation fails or runs out of fuel is left to run whole, where the failure is
//! reported in the ordinary way.
//!
//! The Trick: `split` specializes a function on a run-stage parameter only when the
//! parameter's domain is finite and at most `SPLIT_CAP` values, `int[0..=256]` but not
//! `int`. Each value gets a copy of the body mixed with the parameter known, and the
//! general body stays as the last arm.

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Pattern, Term, Value, World};

use crate::elab::Unit;
use crate::interp;

/// The fuel of each build-stage evaluation.
pub const BUILD_FUEL: u64 = 1_000_000;

/// The most values the Trick splits a parameter into.
pub const SPLIT_CAP: usize = 1024;

/// When a term is evaluated.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Stage {
    /// By the build.
    Build,
    /// By the run.
    Run,
}

/// What `mix` did.
#[derive(Clone, Default, PartialEq, Eq, Debug)]
pub struct Report {
    /// The definitions the build evaluated, by source name.
    pub built: Vec<String>,
    /// The definitions nothing demanded, which the build did not evaluate.
    pub unread: Vec<String>,
    /// The build-stage terms left to run, each printed with why.
    pub left: Vec<(String, String)>,
}

/// The names `t` reads and does not bind.
pub fn free(t: &Term) -> BTreeSet<Arc<str>> {
    let mut out = BTreeSet::new();
    free_in(t, &mut Vec::new(), &mut out);
    out
}

fn free_in(t: &Term, bound: &mut Vec<Arc<str>>, out: &mut BTreeSet<Arc<str>>) {
    let mut under = |names: &[Arc<str>], t: &Term, bound: &mut Vec<Arc<str>>| {
        let n = bound.len();
        bound.extend(names.iter().cloned());
        free_in(t, bound, out);
        bound.truncate(n);
    };
    match t {
        Term::Lit(_) | Term::PrimFn(_) | Term::Read(_) => {}
        Term::Var(x) => {
            if !bound.contains(x) {
                out.insert(x.clone());
            }
        }
        Term::Lam(ps, b) => under(ps, b, bound),
        Term::Let(x, e, b) => {
            under(&[], e, bound);
            under(std::slice::from_ref(x), b, bound);
        }
        Term::Match(s, arms) => {
            under(&[], s, bound);
            for (p, a) in arms {
                under(&binds(p), a, bound);
            }
        }
        Term::Fam { domain, var, body } => {
            under(&[], domain, bound);
            under(std::slice::from_ref(var), body, bound);
        }
        Term::Fix {
            init,
            step,
            this,
            key,
            kind,
            ..
        } => {
            under(&[], init, bound);
            let names = [this.clone(), key.clone()];
            under(&names, step, bound);
            if let zed_kernel::FixKind::Lattice { join } = kind {
                under(&names, join, bound);
            }
        }
        _ => {
            for c in children(t) {
                under(&[], c, bound);
            }
        }
    }
}

/// The subterms of a term that binds nothing.
fn children(t: &Term) -> Vec<&Term> {
    match t {
        Term::App(f, args) => std::iter::once(&**f).chain(args).collect(),
        Term::Prim(_, args) => args.iter().collect(),
        Term::If(c, a, b) => vec![c, a, b],
        Term::Reindex { family, kf, vf, .. } => vec![family, kf, vf],
        Term::Discard { family, sel } => vec![family, sel],
        Term::Fold {
            family,
            op,
            identity,
            ..
        } => [family, op]
            .into_iter()
            .chain(identity)
            .map(|t| &**t)
            .collect(),
        Term::Gen {
            init, step, guard, ..
        } => vec![init, step, guard],
        Term::Push(_, t) => vec![t],
        _ => Vec::new(),
    }
}

/// The names `p` binds.
fn binds(p: &Pattern) -> Vec<Arc<str>> {
    match p {
        Pattern::Bind(x) => vec![x.clone()],
        Pattern::Atom(_, ps) | Pattern::Tuple(ps) => ps.iter().flat_map(binds).collect(),
        Pattern::Fields(_, fs) => fs.iter().flat_map(|(_, p)| binds(p)).collect(),
        _ => Vec::new(),
    }
}

/// Whether `t` reads or writes a port.
fn effects(t: &Term) -> bool {
    match t {
        Term::Read(_) | Term::Push(..) => true,
        Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) => false,
        Term::Lam(_, b) => effects(b),
        Term::Let(_, e, b) => effects(e) || effects(b),
        Term::Match(s, arms) => effects(s) || arms.iter().any(|(_, a)| effects(a)),
        Term::Fam { domain, body, .. } => effects(domain) || effects(body),
        Term::Fix { init, step, .. } => effects(init) || effects(step),
        _ => children(t).into_iter().any(effects),
    }
}

/// The stage of each definition of `unit`, by source name, in order.
pub fn color(unit: &Unit) -> Vec<(String, Stage)> {
    let mut m = Mixer::new(BUILD_FUEL);
    unit.defs
        .iter()
        .map(|d| {
            let stage = m.stage(&d.term);
            m.bind(d.kernel.clone(), stage, &d.term);
            (d.name.clone(), stage)
        })
        .collect()
}

/// `unit` with its demanded build-stage terms evaluated, keeping the definitions `roots`
/// and the tests read.
pub fn mix(unit: &Unit, roots: &[&str], fuel: u64) -> (Unit, Report) {
    let mut demanded: BTreeSet<Arc<str>> = unit
        .defs
        .iter()
        .filter(|d| roots.contains(&d.name.as_str()))
        .map(|d| d.kernel.clone())
        .collect();
    for t in &unit.tests {
        for term in std::iter::once(&t.check).chain(&t.args).chain([&t.want]) {
            demanded.extend(free(term));
        }
    }
    for d in unit.defs.iter().rev() {
        if demanded.contains(&d.kernel) {
            demanded.extend(free(&d.term));
        }
    }
    let mut m = Mixer::new(fuel);
    let mut out = Unit {
        defs: Vec::new(),
        tests: unit.tests.clone(),
    };
    for d in &unit.defs {
        if !demanded.contains(&d.kernel) {
            m.report.unread.push(d.name.clone());
            continue;
        }
        let term = m.mix(&d.term);
        if matches!(term, Term::Lit(_)) && term != d.term {
            m.report.built.push(d.name.clone());
        }
        let stage = m.known(&term);
        m.bind(d.kernel.clone(), stage, &term);
        out.defs.push(crate::elab::Def { term, ..d.clone() });
    }
    (out, m.report)
}

/// The domain of a parameter.
#[derive(Clone, Debug)]
pub enum Domain {
    /// The values of a type.
    Type(Type),
    /// The integers between two bounds, either of which may be absent.
    Ints(Option<i64>, Option<i64>),
}

/// What the Trick decides for a parameter.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Choice {
    /// Specialize on each of these values.
    Split(Vec<Value>),
    /// Do not specialize, for this reason.
    Keep(String),
}

/// The Trick: split on `d` only when it is finite and at most `cap` values.
pub fn trick(d: &Domain, cap: usize) -> Choice {
    match d {
        Domain::Type(t) => match t.values(cap) {
            Some(vs) => Choice::Split(vs),
            None => Choice::Keep(format!("the domain `{t}` is not at most {cap} values")),
        },
        Domain::Ints(Some(lo), Some(hi)) => {
            let n = (i128::from(*hi) - i128::from(*lo) + 1).max(0);
            if n <= cap as i128 {
                Choice::Split((*lo..=*hi).map(Value::Int).collect())
            } else {
                Choice::Keep(format!(
                    "the domain [{lo}..={hi}] is {n} values, over {cap}"
                ))
            }
        }
        Domain::Ints(..) => Choice::Keep("an unbounded integer domain is infinite".into()),
    }
}

/// The function `name` of `unit` split on its parameter `param` over `d`, each arm its body
/// mixed with the parameter known, and the general body last; or why the Trick keeps it.
pub fn split(
    unit: &Unit,
    name: &str,
    param: usize,
    d: &Domain,
    fuel: u64,
) -> Result<(Term, Report), String> {
    let at = unit
        .defs
        .iter()
        .position(|d| d.name == name)
        .ok_or_else(|| format!("no definition `{name}`"))?;
    let Term::Lam(ps, body) = &unit.defs[at].term else {
        return Err(format!("`{name}` is not a function"));
    };
    let p = ps
        .get(param)
        .ok_or_else(|| format!("`{name}` has no parameter {param}"))?
        .clone();
    let values = match trick(d, SPLIT_CAP) {
        Choice::Split(vs) => vs,
        Choice::Keep(why) => return Err(why),
    };
    let mut m = Mixer::new(fuel);
    for d in &unit.defs[..at] {
        let stage = m.stage(&d.term);
        m.bind(d.kernel.clone(), stage, &d.term);
    }
    let n = m.scope.len();
    for q in ps {
        m.bind(q.clone(), Stage::Run, &Term::Var(q.clone()));
    }
    let mut arms = Vec::new();
    for v in values {
        m.bind(p.clone(), Stage::Build, &Term::Lit(v.clone()));
        arms.push((Pattern::Lit(v), m.mix(body)));
        m.scope.pop();
    }
    arms.push((Pattern::Wild, m.mix(body)));
    m.scope.truncate(n);
    let lam = Term::Lam(
        ps.clone(),
        Arc::new(Term::Match(Arc::new(Term::Var(p)), arms)),
    );
    Ok((lam, m.report))
}

/// A name in scope: its term when it is build-stage, else nothing.
type Scope = Vec<(Arc<str>, Option<Term>)>;

struct Mixer {
    scope: Scope,
    fuel: u64,
    report: Report,
}

impl Mixer {
    fn new(fuel: u64) -> Self {
        Mixer {
            scope: Vec::new(),
            fuel,
            report: Report::default(),
        }
    }

    fn bind(&mut self, name: Arc<str>, stage: Stage, t: &Term) {
        let known = (stage == Stage::Build).then(|| t.clone());
        self.scope.push((name, known));
    }

    /// The stage a name bound to the mixed term `t` has: build when `t` is a literal or a
    /// build-stage function, run when it is left to run, so that nothing evaluates it again.
    fn known(&self, t: &Term) -> Stage {
        match t {
            Term::Lit(_) => Stage::Build,
            Term::Lam(..) | Term::PrimFn(_) | Term::Var(_) => self.stage(t),
            _ => Stage::Run,
        }
    }

    fn unknown(&mut self, names: &[Arc<str>]) {
        for x in names {
            self.scope.push((x.clone(), None));
        }
    }

    /// The innermost binding of `x`: `None` for a name the scope does not bind.
    fn lookup(&self, x: &str) -> Option<&Option<Term>> {
        self.scope
            .iter()
            .rev()
            .find(|(n, _)| &**n == x)
            .map(|(_, t)| t)
    }

    fn stage(&self, t: &Term) -> Stage {
        let known = free(t).iter().all(|x| match self.lookup(x) {
            Some(t) => t.is_some(),
            None => interp::word(x),
        });
        if known && !effects(t) {
            Stage::Build
        } else {
            Stage::Run
        }
    }

    /// The value of the build-stage term `t`, under the bindings it needs.
    fn eval(&self, t: &Term) -> Result<Value, String> {
        let mut need = free(t);
        let mut lets = Vec::new();
        for (x, known) in self.scope.iter().rev() {
            if let Some(e) = known
                && need.remove(x)
            {
                need.extend(free(e));
                lets.push((x.clone(), e.clone()));
            }
        }
        let closed = lets.into_iter().fold(t.clone(), |body, (x, e)| {
            Term::Let(x, Arc::new(e), Arc::new(body))
        });
        Evaluator::new(World::new())
            .with_fuel(self.fuel)
            .run(&interp::prelude(closed))
            .map_err(|e| e.to_string())
    }

    /// `t` with its build-stage subterms evaluated.
    fn mix(&mut self, t: &Term) -> Term {
        let function = |t: &Term| matches!(t, Term::Lam(..) | Term::PrimFn(_));
        let value = match t {
            Term::Lit(_) | Term::PrimFn(_) | Term::Lam(..) => false,
            Term::Var(x) => matches!(self.lookup(x), Some(Some(e)) if !function(e)),
            _ => true,
        };
        if value && self.stage(t) == Stage::Build {
            return match self.eval(t) {
                Ok(v) => Term::Lit(v),
                Err(why) => {
                    self.report.left.push((t.to_string(), why));
                    t.clone()
                }
            };
        }
        let under = |m: &mut Mixer, names: &[Arc<str>], t: &Term| {
            let n = m.scope.len();
            m.unknown(names);
            let out = m.mix(t);
            m.scope.truncate(n);
            out
        };
        let a = |t: Term| Arc::new(t);
        match t {
            Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => t.clone(),
            Term::Lam(ps, b) => Term::Lam(ps.clone(), a(under(self, ps, b))),
            Term::Let(x, e, b) => {
                if self.stage(e) == Stage::Build && !free(b).contains(x) {
                    self.report.unread.push(x.to_string());
                    return self.mix(b);
                }
                let e = self.mix(e);
                let stage = self.known(&e);
                self.bind(x.clone(), stage, &e);
                let body = self.mix(b);
                self.scope.pop();
                if matches!(e, Term::Lit(_)) && !free(&body).contains(x) {
                    return body;
                }
                Term::Let(x.clone(), a(e), a(body))
            }
            Term::If(c, x, y) => match self.mix(c) {
                Term::Lit(Value::Bool(true)) => self.mix(x),
                Term::Lit(Value::Bool(false)) => self.mix(y),
                atom @ Term::Lit(Value::Atom(_)) => atom,
                c => Term::If(a(c), a(self.mix(x)), a(self.mix(y))),
            },
            Term::App(f, args) => {
                Term::App(a(self.mix(f)), args.iter().map(|x| self.mix(x)).collect())
            }
            Term::Prim(p, args) => Term::Prim(*p, args.iter().map(|x| self.mix(x)).collect()),
            Term::Match(s, arms) => Term::Match(
                a(self.mix(s)),
                arms.iter()
                    .map(|(p, x)| (p.clone(), under(self, &binds(p), x)))
                    .collect(),
            ),
            Term::Fam { domain, var, body } => Term::Fam {
                domain: a(self.mix(domain)),
                var: var.clone(),
                body: a(under(self, std::slice::from_ref(var), body)),
            },
            Term::Reindex {
                family,
                kf,
                vf,
                witness,
            } => Term::Reindex {
                family: a(self.mix(family)),
                kf: a(self.mix(kf)),
                vf: a(self.mix(vf)),
                witness: witness.clone(),
            },
            Term::Discard { family, sel } => Term::Discard {
                family: a(self.mix(family)),
                sel: a(self.mix(sel)),
            },
            Term::Fold {
                family,
                op,
                identity,
                depth,
                ev,
            } => Term::Fold {
                family: a(self.mix(family)),
                op: a(self.mix(op)),
                identity: identity.as_ref().map(|i| a(self.mix(i))),
                depth: *depth,
                ev: ev.clone(),
            },
            Term::Gen {
                init,
                step,
                guard,
                pos,
            } => Term::Gen {
                init: a(self.mix(init)),
                step: a(self.mix(step)),
                guard: a(self.mix(guard)),
                pos: *pos,
            },
            // A recursion's binders are left as written; recursion arrives at L6.
            Term::Fix { .. } => t.clone(),
            Term::Push(port, x) => Term::Push(port.clone(), a(self.mix(x))),
        }
    }
}
