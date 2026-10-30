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

/// Calls `f` on the name of every binder of `t`, in preorder.
fn each_binder(t: &Term, f: &mut impl FnMut(&str)) {
    match t {
        Term::Lam(params, body) => {
            params.iter().for_each(|p| f(p));
            each_binder(body, f);
        }
        Term::Let(x, e, body) => {
            each_binder(e, f);
            f(x);
            each_binder(body, f);
        }
        Term::Match(e, arms) => {
            each_binder(e, f);
            for (p, arm) in arms {
                pattern_binds(p).iter().for_each(|x| f(x));
                each_binder(arm, f);
            }
        }
        Term::Fam { domain, var, body } => {
            each_binder(domain, f);
            f(var);
            each_binder(body, f);
        }
        Term::Fix {
            init,
            step,
            this,
            key,
            kind: FixKind::Definedness,
            ..
        } => {
            each_binder(init, f);
            f(this);
            f(key);
            each_binder(step, f);
        }
        _ => children(t).into_iter().for_each(|c| each_binder(c, f)),
    }
}

/// The names a pattern binds, left to right.
pub fn pattern_binds(p: &Pattern) -> Vec<Arc<str>> {
    fn go(p: &Pattern, out: &mut Vec<Arc<str>>) {
        match p {
            Pattern::Bind(x) => out.push(x.clone()),
            Pattern::Atom(_, ps) | Pattern::Tuple(ps) => ps.iter().for_each(|p| go(p, out)),
            Pattern::Fields(_, fs) => fs.iter().for_each(|(_, p)| go(p, out)),
            Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => {}
        }
    }
    let mut out = Vec::new();
    go(p, &mut out);
    out
}

/// The subterms of a term that binds nothing, in order.
fn children(t: &Term) -> Vec<&Term> {
    match t {
        Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => vec![],
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
        Term::Fix {
            init, step, kind, ..
        } => match kind {
            FixKind::Lattice { join } => vec![init, step, join],
            FixKind::Definedness => vec![init, step],
        },
        Term::Gen {
            init, step, guard, ..
        } => vec![init, step, guard],
        Term::Push(_, v) => vec![v],
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
    Levels::default().term(t, 0)
}

/// The names in scope during the walk: each written name to the new names of the binders of
/// that name around the current subterm, innermost last.
#[derive(Default)]
struct Levels {
    scope: std::collections::BTreeMap<Arc<str>, Vec<Arc<str>>>,
}

impl Levels {
    /// The new names of `names`, bound together at levels `depth`, `depth + 1`, …, brought
    /// into scope in order, so that a later name of the group shadows an earlier one.
    fn bind(&mut self, names: &[Arc<str>], depth: usize) -> Vec<Arc<str>> {
        let new: Vec<Arc<str>> = names
            .iter()
            .enumerate()
            .map(|(i, x)| match level_of(x) {
                Some(_) => x.clone(),
                None => level_name(depth + i),
            })
            .collect();
        for (x, n) in names.iter().zip(&new) {
            self.scope.entry(x.clone()).or_default().push(n.clone());
        }
        new
    }

    /// Takes `names` out of scope again, in the reverse order.
    fn unbind(&mut self, names: &[Arc<str>]) {
        for x in names.iter().rev() {
            let stack = self.scope.get_mut(x).expect("bound by `bind`");
            stack.pop();
            if stack.is_empty() {
                self.scope.remove(x);
            }
        }
    }

    /// `body` with `names` in scope at levels from `depth`, and the new names.
    fn under(&mut self, names: &[Arc<str>], depth: usize, body: &Term) -> (Vec<Arc<str>>, Term) {
        let new = self.bind(names, depth);
        let body = self.term(body, depth + names.len());
        self.unbind(names);
        (new, body)
    }

    fn term(&mut self, t: &Term, depth: usize) -> Term {
        let arc = |t: Term| Arc::new(t);
        match t {
            Term::Var(x) => match self.scope.get(x).and_then(|s| s.last()) {
                Some(n) => Term::Var(n.clone()),
                None => t.clone(),
            },
            Term::Lam(params, body) => {
                let (new, body) = self.under(params, depth, body);
                Term::Lam(new, arc(body))
            }
            Term::Let(x, e, body) => {
                let e = self.term(e, depth);
                let (new, body) = self.under(std::slice::from_ref(x), depth, body);
                Term::Let(new[0].clone(), arc(e), arc(body))
            }
            Term::Match(e, arms) => {
                let e = self.term(e, depth);
                let arms = arms
                    .iter()
                    .map(|(p, arm)| {
                        let binds = pattern_binds(p);
                        let (new, arm) = self.under(&binds, depth, arm);
                        (set_binds(p, &mut new.iter()), arm)
                    })
                    .collect();
                Term::Match(arc(e), arms)
            }
            Term::Fam { domain, var, body } => {
                let domain = arc(self.term(domain, depth));
                let (new, body) = self.under(std::slice::from_ref(var), depth, body);
                Term::Fam {
                    domain,
                    var: new[0].clone(),
                    body: arc(body),
                }
            }
            Term::Fix {
                init,
                step,
                this,
                key,
                kind: FixKind::Definedness,
                ev,
            } => {
                let init = arc(self.term(init, depth));
                let (new, step) = self.under(&[this.clone(), key.clone()], depth, step);
                Term::Fix {
                    init,
                    step: arc(step),
                    this: new[0].clone(),
                    key: new[1].clone(),
                    kind: FixKind::Definedness,
                    ev: ev.clone(),
                }
            }
            _ => map_children(t, &mut |c| self.term(c, depth)),
        }
    }
}

/// `p` with its binders, left to right, named by `names` in turn.
fn set_binds<'a>(p: &Pattern, names: &mut impl Iterator<Item = &'a Arc<str>>) -> Pattern {
    let mut all = |ps: &[Pattern]| ps.iter().map(|p| set_binds(p, names)).collect();
    match p {
        Pattern::Bind(_) => Pattern::Bind(names.next().expect("one name per binder").clone()),
        Pattern::Atom(name, ps) => Pattern::Atom(name.clone(), all(ps)),
        Pattern::Tuple(ps) => Pattern::Tuple(all(ps)),
        Pattern::Fields(name, fs) => Pattern::Fields(
            name.clone(),
            fs.iter()
                .map(|(f, p)| (f.clone(), set_binds(p, names)))
                .collect(),
        ),
        Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => p.clone(),
    }
}
