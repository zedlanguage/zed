//! Binder normalization: each local binder is renamed to its de Bruijn level, the number of
//! binders enclosing it, so that two terms that differ only in local names become one term.
//!
//! The rule renames one binder per step: the first binder in preorder that still carries its
//! written name. Every binder before it in preorder is already canonical, so the binders
//! enclosing it are too, and no binder inside its scope is: the new name cannot be captured,
//! and a written binder of the same name inside the scope shadows the old name as before.

use std::sync::Arc;

use zed_kernel::term::{FixKind, Pattern, Term};

/// The canonical name of the binder at de Bruijn level `level`. It starts with U+0000, which no
/// written name contains: the lexer rejects the character in source text.
pub fn level_name(level: usize) -> Arc<str> {
    format!("\0{level}").into()
}

/// The level a canonical binder name stands for, or `None` for a written name.
pub fn level_of(name: &str) -> Option<usize> {
    name.strip_prefix('\0')?.parse().ok()
}

/// One rewrite: the first written binder in preorder renamed to its level, with its written
/// name and preorder index returned for the hint facet. `None` when every binder is canonical.
pub fn step(t: &Term) -> Option<(Term, usize, Arc<str>)> {
    let (t, name) = rename_first(t, 0)?;
    // The canonical binders are the binders before the renamed one in preorder, and it.
    let index = (count(&t) - written(&t) - 1) as usize;
    Some((t, index, name))
}

/// The binders that still carry their written names: the rank of the rule.
pub fn written(t: &Term) -> u64 {
    let mut n = 0;
    each_binder(t, &mut |name| n += u64::from(level_of(name).is_none()));
    n
}

/// All the binders of `t`.
fn count(t: &Term) -> u64 {
    let mut n = 0;
    each_binder(t, &mut |_| n += 1);
    n
}

/// Calls `f` on the name of every binder of `t`, in preorder. The terms still to walk wait on a
/// heap stack, so a deep term does not grow the thread's stack.
fn each_binder(t: &Term, f: &mut impl FnMut(&str)) {
    enum Job<'t> {
        Term(&'t Term),
        Name(&'t str),
        Pattern(&'t Pattern),
    }
    let mut todo = vec![Job::Term(t)];
    while let Some(job) = todo.pop() {
        let t = match job {
            Job::Name(x) => {
                f(x);
                continue;
            }
            Job::Pattern(p) => {
                each_pattern(p, &mut |p| {
                    if let Pattern::Bind(x) = p {
                        f(x)
                    }
                });
                continue;
            }
            Job::Term(t) => t,
        };
        match t {
            Term::Lam(params, body) => {
                params.iter().for_each(|p| f(p));
                todo.push(Job::Term(body));
            }
            Term::Let(x, e, body)
            | Term::Fam {
                domain: e,
                var: x,
                body,
            } => todo.extend([Job::Term(body), Job::Name(x), Job::Term(e)]),
            Term::Match(e, arms) => {
                for (p, arm) in arms.iter().rev() {
                    todo.extend([Job::Term(arm), Job::Pattern(p)]);
                }
                todo.push(Job::Term(e));
            }
            Term::Fix {
                init,
                step,
                this,
                key,
                kind: FixKind::Definedness,
                ..
            } => todo.extend([
                Job::Term(step),
                Job::Name(key),
                Job::Name(this),
                Job::Term(init),
            ]),
            _ => {
                let start = todo.len();
                each_child(t, |c| todo.push(Job::Term(c)));
                todo[start..].reverse();
            }
        }
    }
}

/// Calls `f` on `p` and each pattern inside it, in preorder, keeping the patterns still to
/// visit on a heap stack.
fn each_pattern<'p>(p: &'p Pattern, f: &mut impl FnMut(&'p Pattern)) {
    let mut todo = vec![p];
    while let Some(p) = todo.pop() {
        f(p);
        match p {
            Pattern::Atom(_, ps) | Pattern::Tuple(ps) => todo.extend(ps.iter().rev()),
            Pattern::Fields(_, fs) => todo.extend(fs.iter().rev().map(|(_, p)| p)),
            Pattern::Wild
            | Pattern::Bind(_)
            | Pattern::Lit(_)
            | Pattern::AnyAtom
            | Pattern::Is(_) => {}
        }
    }
}

/// The names a pattern binds, left to right.
pub fn pattern_binds(p: &Pattern) -> Vec<Arc<str>> {
    let mut out = Vec::new();
    each_pattern(p, &mut |p| {
        if let Pattern::Bind(x) = p {
            out.push(x.clone())
        }
    });
    out
}

/// The subterms of a term that binds nothing, in order.
fn children(t: &Term) -> Vec<&Term> {
    let mut out = Vec::new();
    each_child(t, |c| out.push(c));
    out
}

/// Calls `f` on each subterm of a term that binds nothing, in order.
fn each_child<'t>(t: &'t Term, mut f: impl FnMut(&'t Term)) {
    match t {
        Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => {}
        Term::App(g, args) => {
            f(g);
            args.iter().for_each(f);
        }
        Term::Prim(_, args) => args.iter().for_each(f),
        Term::If(c, a, b) => [c, a, b].into_iter().for_each(|t| f(t)),
        Term::Reindex { family, kf, vf, .. } => [family, kf, vf].into_iter().for_each(|t| f(t)),
        Term::Discard { family, sel } => [family, sel].into_iter().for_each(|t| f(t)),
        Term::Fold {
            family,
            op,
            identity,
            ..
        } => [family, op].into_iter().chain(identity).for_each(|t| f(t)),
        Term::Fix {
            init, step, kind, ..
        } => {
            f(init);
            f(step);
            if let FixKind::Lattice { join } = kind {
                f(join);
            }
        }
        Term::Gen {
            init, step, guard, ..
        } => [init, step, guard].into_iter().for_each(|t| f(t)),
        Term::Push(_, v) => f(v),
        Term::Lam(..) | Term::Let(..) | Term::Match(..) | Term::Fam { .. } => {
            unreachable!("binding forms are handled by the caller")
        }
    }
}

/// `t` with each child replaced by `f(child)`, for a term that binds nothing.
fn map_children(t: &Term, f: &mut impl FnMut(&Term) -> Term) -> Term {
    let a = |t: &Arc<Term>, f: &mut dyn FnMut(&Term) -> Term| Arc::new(f(t));
    match t {
        Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => t.clone(),
        Term::App(g, args) => Term::App(a(g, f), args.iter().map(&mut *f).collect()),
        Term::Prim(p, args) => Term::Prim(*p, args.iter().map(f).collect()),
        Term::If(c, x, y) => Term::If(a(c, f), a(x, f), a(y, f)),
        Term::Reindex {
            family,
            kf,
            vf,
            witness,
        } => Term::Reindex {
            family: a(family, f),
            kf: a(kf, f),
            vf: a(vf, f),
            witness: witness.clone(),
        },
        Term::Discard { family, sel } => Term::Discard {
            family: a(family, f),
            sel: a(sel, f),
        },
        Term::Fold {
            family,
            op,
            identity,
            depth,
            ev,
        } => Term::Fold {
            family: a(family, f),
            op: a(op, f),
            identity: identity.as_ref().map(|i| a(i, f)),
            depth: *depth,
            ev: ev.clone(),
        },
        Term::Fix {
            init,
            step,
            this,
            key,
            kind,
            ev,
        } => Term::Fix {
            init: a(init, f),
            step: a(step, f),
            this: this.clone(),
            key: key.clone(),
            kind: match kind {
                FixKind::Lattice { join } => FixKind::Lattice { join: a(join, f) },
                FixKind::Definedness => FixKind::Definedness,
            },
            ev: ev.clone(),
        },
        Term::Gen {
            init,
            step,
            guard,
            pos,
        } => Term::Gen {
            init: a(init, f),
            step: a(step, f),
            guard: a(guard, f),
            pos: *pos,
        },
        Term::Push(port, v) => Term::Push(port.clone(), a(v, f)),
        Term::Lam(..) | Term::Let(..) | Term::Match(..) | Term::Fam { .. } => {
            unreachable!("binding forms are handled by the caller")
        }
    }
}

/// One group of names bound together, at levels `depth`, `depth + 1`, …, with its first
/// written name renamed.
struct Renamed {
    /// The group with the name renamed.
    names: Vec<Arc<str>>,
    /// The position of the renamed name in the group.
    at: usize,
    /// Its written name.
    old: Arc<str>,
    /// Whether a later name of the group binds the same written name, so that the renamed
    /// binder's scope holds none of its occurrences.
    shadowed: bool,
}

impl Renamed {
    fn of(names: &[Arc<str>], depth: usize) -> Option<Self> {
        let at = names.iter().position(|x| level_of(x).is_none())?;
        let old = names[at].clone();
        let mut renamed = names.to_vec();
        renamed[at] = level_name(depth + at);
        let shadowed = names[at + 1..].contains(&old);
        Some(Renamed {
            names: renamed,
            at,
            old,
            shadowed,
        })
    }

    fn level(&self) -> &Arc<str> {
        &self.names[self.at]
    }

    /// The scope `body` with the renamed binder's occurrences renamed.
    fn scope(&self, body: &Term) -> Term {
        if self.shadowed {
            body.clone()
        } else {
            rename(body, &self.old, self.level())
        }
    }
}

/// Renames the first written binder in preorder at binder depth `depth`. Returns the new term
/// and the binder's written name.
fn rename_first(t: &Term, depth: usize) -> Option<(Term, Arc<str>)> {
    let arc = |t: Term| Arc::new(t);
    match t {
        Term::Lam(params, body) => {
            if let Some(r) = Renamed::of(params, depth) {
                let body = r.scope(body);
                return Some((Term::Lam(r.names, arc(body)), r.old));
            }
            let (body, old) = rename_first(body, depth + params.len())?;
            Some((Term::Lam(params.clone(), arc(body)), old))
        }
        Term::Let(x, e, body) => {
            if let Some((e, old)) = rename_first(e, depth) {
                return Some((Term::Let(x.clone(), arc(e), body.clone()), old));
            }
            if level_of(x).is_none() {
                let new = level_name(depth);
                let body = rename(body, x, &new);
                return Some((Term::Let(new, e.clone(), arc(body)), x.clone()));
            }
            let (body, old) = rename_first(body, depth + 1)?;
            Some((Term::Let(x.clone(), e.clone(), arc(body)), old))
        }
        Term::Match(e, arms) => {
            if let Some((e, old)) = rename_first(e, depth) {
                return Some((Term::Match(arc(e), arms.clone()), old));
            }
            for (k, (p, arm)) in arms.iter().enumerate() {
                let binds = pattern_binds(p);
                let new_arm = if let Some(r) = Renamed::of(&binds, depth) {
                    let p = rename_pattern_bind(p, &mut r.at.clone(), r.level());
                    Some(((p, r.scope(arm)), r.old))
                } else {
                    rename_first(arm, depth + binds.len()).map(|(arm, old)| ((p.clone(), arm), old))
                };
                if let Some((arm, old)) = new_arm {
                    let mut arms = arms.clone();
                    arms[k] = arm;
                    return Some((Term::Match(e.clone(), arms), old));
                }
            }
            None
        }
        Term::Fam { domain, var, body } => {
            if let Some((d, old)) = rename_first(domain, depth) {
                let t = Term::Fam {
                    domain: arc(d),
                    var: var.clone(),
                    body: body.clone(),
                };
                return Some((t, old));
            }
            if level_of(var).is_none() {
                let new = level_name(depth);
                let t = Term::Fam {
                    domain: domain.clone(),
                    var: new.clone(),
                    body: arc(rename(body, var, &new)),
                };
                return Some((t, var.clone()));
            }
            let (b, old) = rename_first(body, depth + 1)?;
            let t = Term::Fam {
                domain: domain.clone(),
                var: var.clone(),
                body: arc(b),
            };
            Some((t, old))
        }
        Term::Fix {
            init,
            step,
            this,
            key,
            kind: FixKind::Definedness,
            ev,
        } => {
            let fix = |init: &Arc<Term>, this: &Arc<str>, key: &Arc<str>, step: Term| Term::Fix {
                init: init.clone(),
                step: arc(step),
                this: this.clone(),
                key: key.clone(),
                kind: FixKind::Definedness,
                ev: ev.clone(),
            };
            if let Some((i, old)) = rename_first(init, depth) {
                return Some((fix(&arc(i), this, key, (**step).clone()), old));
            }
            if let Some(r) = Renamed::of(&[this.clone(), key.clone()], depth) {
                let step = r.scope(step);
                return Some((fix(init, &r.names[0], &r.names[1], step), r.old));
            }
            let (s, old) = rename_first(step, depth + 2)?;
            Some((fix(init, this, key, s), old))
        }
        _ => {
            let kids = children(t);
            let k = kids.iter().position(|c| written(c) > 0)?;
            let (new, old) = rename_first(kids[k], depth)?;
            let mut i = 0;
            let t = map_children(t, &mut |c| {
                i += 1;
                if i - 1 == k { new.clone() } else { c.clone() }
            });
            Some((t, old))
        }
    }
}

/// `p` with its `i`-th binder (left to right) renamed to `new`; `i` counts down as binders
/// are passed.
fn rename_pattern_bind(p: &Pattern, i: &mut usize, new: &Arc<str>) -> Pattern {
    match p {
        Pattern::Bind(x) => {
            let hit = *i == 0;
            *i = i.wrapping_sub(1);
            Pattern::Bind(if hit { new.clone() } else { x.clone() })
        }
        Pattern::Atom(name, ps) => Pattern::Atom(
            name.clone(),
            ps.iter().map(|p| rename_pattern_bind(p, i, new)).collect(),
        ),
        Pattern::Tuple(ps) => {
            Pattern::Tuple(ps.iter().map(|p| rename_pattern_bind(p, i, new)).collect())
        }
        Pattern::Fields(name, fs) => Pattern::Fields(
            name.clone(),
            fs.iter()
                .map(|(f, p)| (f.clone(), rename_pattern_bind(p, i, new)))
                .collect(),
        ),
        Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => p.clone(),
    }
}

/// `t` with the free occurrences of the variable `old` renamed to `new`. A binder of `old`
/// inside `t` shadows it below.
fn rename(t: &Term, old: &str, new: &Arc<str>) -> Term {
    let arc = |t: Term| Arc::new(t);
    let under = |names: &[&str], body: &Term| {
        if names.contains(&old) {
            body.clone()
        } else {
            rename(body, old, new)
        }
    };
    match t {
        Term::Var(x) if &**x == old => Term::Var(new.clone()),
        Term::Lam(params, body) => {
            let names: Vec<&str> = params.iter().map(|p| &**p).collect();
            Term::Lam(params.clone(), arc(under(&names, body)))
        }
        Term::Let(x, e, body) => {
            Term::Let(x.clone(), arc(rename(e, old, new)), arc(under(&[x], body)))
        }
        Term::Match(e, arms) => Term::Match(
            arc(rename(e, old, new)),
            arms.iter()
                .map(|(p, arm)| {
                    let binds = pattern_binds(p);
                    let names: Vec<&str> = binds.iter().map(|x| &**x).collect();
                    (p.clone(), under(&names, arm))
                })
                .collect(),
        ),
        Term::Fam { domain, var, body } => Term::Fam {
            domain: arc(rename(domain, old, new)),
            var: var.clone(),
            body: arc(under(&[var], body)),
        },
        Term::Fix {
            init,
            step,
            this,
            key,
            kind: FixKind::Definedness,
            ev,
        } => Term::Fix {
            init: arc(rename(init, old, new)),
            step: arc(under(&[this, key], step)),
            this: this.clone(),
            key: key.clone(),
            kind: FixKind::Definedness,
            ev: ev.clone(),
        },
        _ => map_children(t, &mut |c| rename(c, old, new)),
    }
}

/// `t` with every binder renamed as the rule renames them one per step, in one walk: each
/// written binder gets its level, and each variable the name of the binder it means. A binder
/// already canonical keeps its name, as the rule leaves it. `O(t log t)` for a term of size `t`.
pub fn canonical(t: &Term) -> Term {
    Levels::default().term(t)
}

/// The names in scope during the walk: each written name to the new names of the binders of
/// that name around the current subterm, innermost last.
#[derive(Default)]
struct Levels {
    scope: std::collections::BTreeMap<Arc<str>, Vec<Arc<str>>>,
}

/// A step of [`Levels::term`]'s walk, on its heap stack.
enum Walk<'t> {
    /// Rename `t`, `depth` binders deep, and put the result on the results.
    Term(&'t Term, usize),
    /// The binding term `t`, whose first child is on the results: bring its names into scope
    /// and walk the scope.
    Scope(&'t Term, usize),
    /// The arm `arm` of a `match`, `depth` binders deep: bring the names of `p` into scope and
    /// walk it.
    Arm(&'t Pattern, &'t Term, usize),
    /// The scope of the binding term `t` is on the results: take its names out of scope and
    /// build it.
    Close(&'t Term),
    /// The arm of pattern `p`, which binds `names`, is on the results: take the names out of
    /// scope and put the arm, its pattern renamed, on the arms.
    CloseArm(&'t Pattern, Vec<Arc<str>>),
    /// The scrutinee and the arms of the `match` `t` are on the results and the arms: build it.
    Match(&'t Term),
    /// The `k` children of `t`, which binds nothing, are on the results: build it.
    Map(&'t Term, usize),
}

impl Levels {
    /// Brings `names`, bound together at levels `depth`, `depth + 1`, …, into scope in order,
    /// so that a later name of the group shadows an earlier one. A canonical name keeps its
    /// name; a written one gets its level.
    fn bind(&mut self, names: &[Arc<str>], depth: usize) {
        for (i, x) in names.iter().enumerate() {
            let new = match level_of(x) {
                Some(_) => x.clone(),
                None => level_name(depth + i),
            };
            self.scope.entry(x.clone()).or_default().push(new);
        }
    }

    /// Takes `names` out of scope again, in the reverse order, and returns their new names in
    /// order.
    fn unbind(&mut self, names: &[Arc<str>]) -> Vec<Arc<str>> {
        let mut new = Vec::with_capacity(names.len());
        for x in names.iter().rev() {
            let stack = self.scope.get_mut(x).expect("bound by `bind`");
            new.push(stack.pop().expect("bound by `bind`"));
            if stack.is_empty() {
                self.scope.remove(x);
            }
        }
        new.reverse();
        new
    }

    /// `t` renamed. The terms still to rename and the terms to build wait on heap stacks, so a
    /// deep term does not grow the thread's stack; the walk visits the subterms in the order
    /// of the recursion it replaces, so the names come out the same.
    fn term(&mut self, t: &Term) -> Term {
        let arc = |t: Term| Arc::new(t);
        let mut todo = vec![Walk::Term(t, 0)];
        let mut done: Vec<Term> = Vec::new();
        let mut arms: Vec<(Pattern, Term)> = Vec::new();
        while let Some(w) = todo.pop() {
            match w {
                Walk::Term(t, depth) => match t {
                    Term::Var(x) => done.push(match self.scope.get(x).and_then(|s| s.last()) {
                        Some(n) => Term::Var(n.clone()),
                        None => t.clone(),
                    }),
                    Term::Lit(_) | Term::PrimFn(_) | Term::Read(_) => done.push(t.clone()),
                    Term::Lam(params, body) => {
                        self.bind(params, depth);
                        todo.push(Walk::Close(t));
                        todo.push(Walk::Term(body, depth + params.len()));
                    }
                    Term::Let(_, e, _)
                    | Term::Fam { domain: e, .. }
                    | Term::Fix {
                        init: e,
                        kind: FixKind::Definedness,
                        ..
                    } => todo.extend([Walk::Scope(t, depth), Walk::Term(e, depth)]),
                    Term::Match(e, ms) => {
                        todo.push(Walk::Match(t));
                        todo.extend(ms.iter().rev().map(|(p, arm)| Walk::Arm(p, arm, depth)));
                        todo.push(Walk::Term(e, depth));
                    }
                    _ => {
                        let at = todo.len();
                        todo.push(Walk::Map(t, 0));
                        each_child(t, |c| todo.push(Walk::Term(c, depth)));
                        let k = todo.len() - at - 1;
                        todo[at] = Walk::Map(t, k);
                        todo[at + 1..].reverse();
                    }
                },
                Walk::Scope(t, depth) => {
                    let (n, body) = match t {
                        Term::Let(x, _, body) | Term::Fam { var: x, body, .. } => {
                            self.bind(std::slice::from_ref(x), depth);
                            (1, body)
                        }
                        Term::Fix {
                            this, key, step, ..
                        } => {
                            self.bind(&[this.clone(), key.clone()], depth);
                            (2, step)
                        }
                        _ => unreachable!("only a binding term has a scope"),
                    };
                    todo.push(Walk::Close(t));
                    todo.push(Walk::Term(body, depth + n));
                }
                Walk::Arm(p, arm, depth) => {
                    let names = pattern_binds(p);
                    self.bind(&names, depth);
                    let inner = depth + names.len();
                    todo.push(Walk::CloseArm(p, names));
                    todo.push(Walk::Term(arm, inner));
                }
                Walk::Close(t) => {
                    let body = arc(done.pop().expect("the scope"));
                    let built = match t {
                        Term::Lam(params, _) => Term::Lam(self.unbind(params), body),
                        Term::Let(x, ..) => {
                            let [new] = self.one(x);
                            Term::Let(new, arc(done.pop().expect("the bound term")), body)
                        }
                        Term::Fam { var, .. } => {
                            let [new] = self.one(var);
                            Term::Fam {
                                domain: arc(done.pop().expect("the domain")),
                                var: new,
                                body,
                            }
                        }
                        Term::Fix { this, key, ev, .. } => {
                            let [key] = self.one(key);
                            let [this] = self.one(this);
                            Term::Fix {
                                init: arc(done.pop().expect("the domain")),
                                step: body,
                                this,
                                key,
                                kind: FixKind::Definedness,
                                ev: ev.clone(),
                            }
                        }
                        _ => unreachable!("only a binding term is closed"),
                    };
                    done.push(built);
                }
                Walk::CloseArm(p, names) => {
                    let new = self.unbind(&names);
                    let arm = done.pop().expect("the arm");
                    arms.push((set_binds(p, &mut new.iter()), arm));
                }
                Walk::Match(t) => {
                    let Term::Match(_, ms) = t else {
                        unreachable!("a `match` is built from its arms")
                    };
                    let built = arms.split_off(arms.len() - ms.len());
                    let e = arc(done.pop().expect("the scrutinee"));
                    done.push(Term::Match(e, built));
                }
                Walk::Map(t, k) => {
                    let mut kids = done.drain(done.len() - k..);
                    let built = map_children(t, &mut |_| kids.next().expect("each child"));
                    drop(kids);
                    done.push(built);
                }
            }
        }
        done.pop().expect("the renamed term")
    }

    /// Takes the one name `x` out of scope again, and returns its new name.
    fn one(&mut self, x: &Arc<str>) -> [Arc<str>; 1] {
        let stack = self.scope.get_mut(x).expect("bound by `bind`");
        let new = stack.pop().expect("bound by `bind`");
        if stack.is_empty() {
            self.scope.remove(x);
        }
        [new]
    }
}

/// `p` with its binders, left to right, named by `names` in turn. The patterns still to visit
/// and to build wait on heap stacks.
fn set_binds<'a>(p: &Pattern, names: &mut impl Iterator<Item = &'a Arc<str>>) -> Pattern {
    enum Job<'p> {
        Visit(&'p Pattern),
        Build(&'p Pattern, usize),
    }
    let mut todo = vec![Job::Visit(p)];
    let mut done: Vec<Pattern> = Vec::new();
    while let Some(job) = todo.pop() {
        match job {
            Job::Visit(p) => match p {
                Pattern::Bind(_) => done.push(Pattern::Bind(
                    names.next().expect("one name per binder").clone(),
                )),
                Pattern::Atom(_, ps) | Pattern::Tuple(ps) => {
                    todo.push(Job::Build(p, ps.len()));
                    todo.extend(ps.iter().rev().map(Job::Visit));
                }
                Pattern::Fields(_, fs) => {
                    todo.push(Job::Build(p, fs.len()));
                    todo.extend(fs.iter().rev().map(|(_, p)| Job::Visit(p)));
                }
                Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => {
                    done.push(p.clone())
                }
            },
            Job::Build(p, k) => {
                let mut kids = done.drain(done.len() - k..);
                let built = match p {
                    Pattern::Atom(name, _) => Pattern::Atom(name.clone(), kids.by_ref().collect()),
                    Pattern::Tuple(_) => Pattern::Tuple(kids.by_ref().collect()),
                    Pattern::Fields(name, fs) => Pattern::Fields(
                        name.clone(),
                        fs.iter()
                            .map(|(f, _)| (f.clone(), kids.next().expect("each field")))
                            .collect(),
                    ),
                    _ => unreachable!("only a pattern with parts is built"),
                };
                drop(kids);
                done.push(built);
            }
        }
    }
    done.pop().expect("the renamed pattern")
}
