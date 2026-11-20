//! Binder normalization: each local binder is renamed to its de Bruijn level, the number of
//! binders enclosing it, so that two terms that differ only in local names become one term.
//!
//! A binder is canonical when it is spelled as its own level. A binder spelled as another level,
//! `\05` at level 0 (no source text spells one, but a term that already holds level names can),
//! counts as written and is renamed like any written binder (FAIL-kernel-canon-misplaced-level,
//! the fault commit 0a516f19c fixed in the ZIR rule): otherwise `\x. x` and `\05. \05` would get
//! two addresses.
//!
//! The rule renames one binder per step: the first binder in preorder that is not canonical.
//! Every binder before it in preorder is canonical, so the binders enclosing it are too, and
//! their levels are below its own. A binder inside its scope, or later in its own group, can be
//! spelled as its new level, though, and would capture the renamed uses; so the step also gives
//! each binder spelled as a level in that scope its own level, and the scope is renamed by a
//! walk that resolves each use through the binders around it (the walk of [`canonical`],
//! keeping written names), not by substituting one name for another. A written binder inside
//! the scope keeps its name, and one of the old name shadows it as before. The rank still falls
//! by one at least.

use std::sync::Arc;

use zed_kernel::term::walk::{Built, kids, rebuild};
use zed_kernel::term::{FixKind, Pattern, Shared, Term};

/// Whether the binder `name` at level `level` is canonical: spelled as `level` itself.
fn canonical_at(name: &str, level: usize) -> bool {
    level_of(name) == Some(level)
}

/// The position in `names`, bound together at levels `depth`, `depth + 1`, …, of the first
/// name that is not canonical.
fn misplaced(names: &[Arc<str>], depth: usize) -> Option<usize> {
    (0..names.len()).find(|&i| !canonical_at(&names[i], depth + i))
}

/// The canonical name of the binder at de Bruijn level `level`. It starts with U+0000, which no
/// written name contains: the lexer rejects the character in source text.
pub fn level_name(level: usize) -> Arc<str> {
    format!("\0{level}").into()
}

/// The level a canonical binder name stands for, or `None` for a written name.
pub fn level_of(name: &str) -> Option<usize> {
    name.strip_prefix('\0')?.parse().ok()
}

/// One rewrite: the first binder in preorder that is not canonical renamed to its level, with
/// its written name and preorder index returned for the hint facet. `None` when every binder
/// is canonical.
pub fn step(t: &Term) -> Option<(Term, usize, Arc<str>)> {
    // The index counts the binders before the renamed one in preorder. It is read off `t`
    // before the step: a canonical binder can follow the renamed one in preorder (`\05. \01.`),
    // so the binders still written afterward do not give it.
    let (mut k, mut index) = (0, None);
    each_binder(t, &mut |name, level| {
        if index.is_none() && !canonical_at(name, level) {
            index = Some(k);
        }
        k += 1;
    });
    let (t, name) = rename_first(t, 0)?;
    Some((t, index.expect("a binder to rename"), name))
}

/// The binders that are not canonical: the rank of the rule.
pub fn written(t: &Term) -> u64 {
    written_at(t, 0)
}

/// The binders of `t`, which stands `depth` binders deep, that are not canonical.
fn written_at(t: &Term, depth: usize) -> u64 {
    let mut n = 0;
    each_binder_at(t, depth, &mut |name, level| {
        n += u64::from(!canonical_at(name, level))
    });
    n
}

/// Calls `f` on the name and level of every binder of `t`, in preorder.
fn each_binder(t: &Term, f: &mut impl FnMut(&str, usize)) {
    each_binder_at(t, 0, f)
}

/// [`each_binder`] on `t` standing `depth` binders deep. The terms still to walk wait on a
/// heap stack, so a deep term does not grow the thread's stack.
fn each_binder_at(t: &Term, depth: usize, f: &mut impl FnMut(&str, usize)) {
    enum Job<'t> {
        Term(&'t Term, usize),
        Name(&'t str, usize),
        Pattern(&'t Pattern, usize),
    }
    let mut todo = vec![Job::Term(t, depth)];
    while let Some(job) = todo.pop() {
        let (t, depth) = match job {
            Job::Name(x, level) => {
                f(x, level);
                continue;
            }
            Job::Pattern(p, depth) => {
                let mut level = depth;
                p.binders(|x| {
                    f(x, level);
                    level += 1;
                });
                continue;
            }
            Job::Term(t, depth) => (t, depth),
        };
        match t {
            Term::Lam(params, body) => {
                params.iter().enumerate().for_each(|(i, p)| f(p, depth + i));
                todo.push(Job::Term(body, depth + params.len()));
            }
            Term::Let(x, e, body)
            | Term::Fam {
                domain: e,
                var: x,
                body,
            } => todo.extend([
                Job::Term(body, depth + 1),
                Job::Name(x, depth),
                Job::Term(e, depth),
            ]),
            Term::Match(e, arms) => {
                for (p, arm) in arms.iter().rev() {
                    let inner = depth + crate::zir::binds(p);
                    todo.extend([Job::Term(arm, inner), Job::Pattern(p, depth)]);
                }
                todo.push(Job::Term(e, depth));
            }
            Term::Fix {
                init,
                step,
                this,
                key,
                kind: FixKind::Definedness,
                ..
            } => todo.extend([
                Job::Term(step, depth + 2),
                Job::Name(key, depth + 1),
                Job::Name(this, depth),
                Job::Term(init, depth),
            ]),
            _ => {
                let start = todo.len();
                each_child(t, |c| todo.push(Job::Term(c, depth)));
                todo[start..].reverse();
            }
        }
    }
}

/// The subterms of a term that binds nothing, in order.
fn children(t: &Term) -> Vec<&Term> {
    let mut out = Vec::new();
    each_child(t, |c| out.push(c));
    out
}

/// Calls `f` on each subterm of a term that binds nothing, in order: the parts
/// [`kids`] gives, each of which such a term binds nothing over.
pub(crate) fn each_child<'t>(t: &'t Term, mut f: impl FnMut(&'t Term)) {
    binds_nothing(t);
    kids(t, |k, _| f(k.term()));
}

/// `t` with each child replaced by `f(child)`, in order, for a term that binds nothing: the
/// parts [`kids`] gives, put back by [`rebuild`].
pub(crate) fn map_children(t: &Term, f: &mut impl FnMut(&Term) -> Term) -> Term {
    binds_nothing(t);
    let mut parts = Vec::new();
    kids(t, |k, _| parts.push(Built::Term(f(k.term()))));
    rebuild(t, parts)
}

/// Stops on a term that binds a name over a part, which each caller of [`each_child`] and
/// [`map_children`] handles itself; a definedness `fix`, which binds `this` and `key` over its
/// step, is one (the copy of the kernel's walk kept here before row DRY-text-shared let it
/// through as binding nothing; no caller passed one).
fn binds_nothing(t: &Term) {
    if let Term::Lam(..)
    | Term::Let(..)
    | Term::Match(..)
    | Term::Fam { .. }
    | Term::Fix {
        kind: FixKind::Definedness,
        ..
    } = t
    {
        unreachable!("binding forms are handled by the caller")
    }
}

/// The binder group `names`, bound together at levels `depth`, `depth + 1`, …, with the name at
/// `at` renamed to its level, and `body`, the group's scope, renamed to match: the group's new
/// names and the new scope. The binders in the scope, and the group's other names, that are
/// spelled as a level get their own level, and written ones keep their names, so the new name
/// is not captured (see the module comment). `O(s log s)` for a scope of size `s`.
fn renamed_scope(
    names: &[Arc<str>],
    at: usize,
    depth: usize,
    body: &Term,
) -> (Vec<Arc<str>>, Term) {
    let mut walk = Levels {
        scope: Default::default(),
        mode: Mode::Written,
    };
    for (i, x) in names.iter().enumerate() {
        let new = if i == at {
            level_name(depth + i)
        } else {
            walk.new_name(x, depth + i)
        };
        walk.scope.entry(x.clone()).or_default().push(new);
    }
    // A use in the scope that no binder of the walk binds is either bound by a binder outside
    // the scope, which is canonical (every binder before this one in preorder is), so its
    // level is below `depth` and below every new name given here; or free in the whole term.
    // A free use spelled as a level could meet a binder's new name, so the rules are defined
    // only on terms with none: `canonicalize` refuses the others (`Levels::refuse_free_level`)
    // before an address is taken, and the one-pass walk agrees with these steps on the rest.
    let body = walk.term_at(body, depth + names.len());
    (walk.unbind(names), body)
}

/// Renames the first binder in preorder that is not canonical, at binder depth `depth`.
/// Returns the new term and the binder's name as it was.
fn rename_first(t: &Term, depth: usize) -> Option<(Term, Arc<str>)> {
    let arc = Shared::new;
    match t {
        Term::Lam(params, body) => {
            if let Some(at) = misplaced(params, depth) {
                let (names, body) = renamed_scope(params, at, depth, body);
                return Some((Term::Lam(names, arc(body)), params[at].clone()));
            }
            let (body, old) = rename_first(body, depth + params.len())?;
            Some((Term::Lam(params.clone(), arc(body)), old))
        }
        Term::Let(x, e, body) => {
            if let Some((e, old)) = rename_first(e, depth) {
                return Some((Term::Let(x.clone(), arc(e), body.clone()), old));
            }
            if !canonical_at(x, depth) {
                let (mut new, body) = renamed_scope(std::slice::from_ref(x), 0, depth, body);
                let new = new.pop().expect("one name");
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
                let binds = p.bound_names();
                let new_arm = if let Some(at) = misplaced(&binds, depth) {
                    let (names, arm) = renamed_scope(&binds, at, depth, arm);
                    Some(((set_binds(p, &mut names.iter()), arm), binds[at].clone()))
                } else {
                    rename_first(arm, depth + binds.len()).map(|(arm, old)| ((p.clone(), arm), old))
                };
                if let Some((arm, old)) = new_arm {
                    // The other arms are cloned and the new one moved in: cloning all the arms
                    // first would copy the old arm too, once per level of nested `match`es.
                    let mut arm = Some(arm);
                    let arms = (0..arms.len())
                        .map(|j| match arm.take_if(|_| j == k) {
                            Some(arm) => arm,
                            None => arms[j].clone(),
                        })
                        .collect();
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
            if !canonical_at(var, depth) {
                let (mut new, body) = renamed_scope(std::slice::from_ref(var), 0, depth, body);
                let t = Term::Fam {
                    domain: domain.clone(),
                    var: new.pop().expect("one name"),
                    body: arc(body),
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
            let fix = |init: &Shared, this: &Arc<str>, key: &Arc<str>, step: Term| Term::Fix {
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
            let group = [this.clone(), key.clone()];
            if let Some(at) = misplaced(&group, depth) {
                let (names, step) = renamed_scope(&group, at, depth, step);
                return Some((fix(init, &names[0], &names[1], step), group[at].clone()));
            }
            let (s, old) = rename_first(step, depth + 2)?;
            Some((fix(init, this, key, s), old))
        }
        _ => {
            // Complexity tradeoff: the first child holding a binder to rename is found by trying
            // each child in turn, not by counting each child's written binders first (the method
            // before FAIL-kernel-canon-misplaced-level): a count walks the child, and descending
            // `n` calls deep counted again at every level, O(n²) on a chain of calls. Trying
            // walks a child that holds none once and stops at the first that holds one, so the
            // search costs O(t) over the whole step. Nothing is given up.
            let kids = children(t);
            let (k, (new, old)) = kids
                .iter()
                .enumerate()
                .find_map(|(k, c)| Some((k, rename_first(c, depth)?)))?;
            // The renamed child is moved in, not cloned: a call's arguments are held inline, so a
            // clone copies the whole child, and one per level of a chain of calls was O(n²). The
            // other children are cloned, each node at most once in a step, since the children
            // beside the path to the renamed binder are disjoint: O(t).
            let (mut i, mut new) = (0, Some(new));
            let t = map_children(t, &mut |c| {
                i += 1;
                match new.take_if(|_| i - 1 == k) {
                    Some(new) => new,
                    None => c.clone(),
                }
            });
            Some((t, old))
        }
    }
}

/// `t` with every binder renamed as the rule renames them one per step, in one walk: each
/// binder that is not canonical gets its level, and each variable the name of the binder it
/// means. A binder already canonical keeps its name, as the rule leaves it. `O(t log t)` for a
/// term of size `t`.
pub fn canonical(t: &Term) -> Term {
    Levels::default().term_at(t, 0)
}

/// What [`keyed`] renames a free name to, `None` to keep it.
pub type FreeNames<'a> = dyn Fn(&str) -> Option<Arc<str>> + 'a;

/// `t` with every binder renamed as [`canonical`] renames it, keeping the name it was written
/// with, and every free name `free` maps renamed: the form a query key reads (step L1.30,
/// `zedc::query::Db::cone`). A binder at level `l` written `x` is named `\0l:x`, where `x` is
/// the binder's written name with elaboration's number dropped: `n` for `n@2`, and `$` for a
/// temporary `$7`. Those numbers count the binders of the whole unit (`Elab::new` and
/// `Elab::temp` in zedc-elab), so they change when a definition moves among the others; the
/// levels keep apart the binders the numbers kept apart. The written name stays because a
/// result can print it (`m.stdin` in a row of `main`'s table, after `main(m: MainArgs)`), so
/// two terms that differ only in a binder's written name keep two keys
/// (FAIL-queries-reorder). `O(t log t)` for a term of size `t`, as [`canonical`].
pub fn keyed(t: &Term, free: &FreeNames<'_>) -> Term {
    Levels {
        scope: Default::default(),
        mode: Mode::Keyed(free),
    }
    .term_at(t, 0)
}

/// The binder name `x` with the number elaboration gave it dropped: the part before `@` of
/// `x@k` ([`written_name`](zed_kernel::text::ident::written_name)), and `$` for a temporary
/// `$k`, which `written_name` keeps whole: here every temporary keys alike, so two terms that
/// differ only in which temporary they use get one key. A written name holds neither `@`
/// nor `$`.
fn unnumbered(x: &str) -> &str {
    match zed_kernel::text::ident::written_name(x) {
        w if w.starts_with('$') => "$",
        w => w,
    }
}

/// The names in scope during the walk: each written name to the new names of the binders of
/// that name around the current subterm, innermost last, and how the binders are named.
#[derive(Default)]
struct Levels<'f> {
    scope: std::collections::BTreeMap<Arc<str>, Vec<Arc<str>>>,
    mode: Mode<'f>,
}

/// The name [`Levels`] gives a binder whose name is not a level. A binder spelled as a level
/// gets its own level in every mode.
#[derive(Default)]
enum Mode<'f> {
    /// Its level: [`canonical`].
    #[default]
    Canonical,
    /// Its level with its written name kept, and free names renamed by the map: [`keyed`].
    Keyed(&'f FreeNames<'f>),
    /// Its written name: the scope of one step of the rule ([`renamed_scope`]).
    Written,
}

/// A step of [`Levels::term_at`]'s walk, on its heap stack.
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

impl Levels<'_> {
    /// Brings `names`, bound together at levels `depth`, `depth + 1`, …, into scope in order,
    /// so that a later name of the group shadows an earlier one, each with the name
    /// [`Levels::new_name`] gives it.
    fn bind(&mut self, names: &[Arc<str>], depth: usize) {
        for (i, x) in names.iter().enumerate() {
            let new = self.new_name(x, depth + i);
            self.scope.entry(x.clone()).or_default().push(new);
        }
    }

    /// The new name of the binder `x` at level `level`: its level when `x` is spelled as a level
    /// (`x` itself when it is that level already), else as the mode says.
    fn new_name(&self, x: &Arc<str>, level: usize) -> Arc<str> {
        match (level_of(x), &self.mode) {
            (Some(l), _) if l == level => x.clone(),
            (Some(_), _) | (None, Mode::Canonical) => level_name(level),
            (None, Mode::Keyed(_)) => format!("\0{}:{}", level, unnumbered(x)).into(),
            (None, Mode::Written) => x.clone(),
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
    /// of the recursion it replaces, so the names come out the same. `t` stands `depth` binders
    /// deep.
    fn term_at(&mut self, t: &Term, depth: usize) -> Term {
        let arc = Shared::new;
        let mut todo = vec![Walk::Term(t, depth)];
        let mut done: Vec<Term> = Vec::new();
        let mut arms: Vec<(Pattern, Term)> = Vec::new();
        while let Some(w) = todo.pop() {
            match w {
                Walk::Term(t, depth) => match t {
                    Term::Var(x) => done.push(match self.scope.get(x).and_then(|s| s.last()) {
                        Some(n) => Term::Var(n.clone()),
                        None => match match self.mode {
                            Mode::Keyed(free) => free(x),
                            _ => None,
                        } {
                            Some(n) => Term::Var(n),
                            None => {
                                self.refuse_free_level(x);
                                t.clone()
                            }
                        },
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
                    let names = p.bound_names();
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

    /// Stops the compiler when `x`, a name no binder around it binds, is spelled as a level in
    /// a walk of a whole term ([`canonical`], [`keyed`]). Such a name is free in the whole
    /// term, and it would be written exactly as the bound variable of that level
    /// (`\x. \y. \z. \w. \02` and `\x. \y. \z. \w. z` would be one term, and so have one
    /// address), so the address or key would not tell two different terms apart. No producer
    /// makes one: source text cannot spell U+0000 (the lexer rejects it), elaboration names
    /// binders `x`, `x@k` and `$k`, and every other `\0` name made in the crates has a letter
    /// after the U+0000. That evidence is not a proof, so the case is refused here rather than
    /// relied on (P246): a wrong address is never given, and the cost is one prefix test per
    /// free name. The step walk ([`Mode::Written`]) starts inside the term, where a name
    /// spelled as a level is bound by a canonical binder outside the scope it walks, so it is
    /// not checked there; the rules agree with [`canonical`] on every term this check admits.
    fn refuse_free_level(&self, x: &str) {
        if !matches!(self.mode, Mode::Written) && level_of(x).is_some() {
            panic!(
                "compiler fault: the canonicalizer was given a term in which the free name \
                 {x:?} is spelled as a binder level, so its address could equal that of a \
                 different term"
            );
        }
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

/// `p` with its binders, left to right, named by `names` in turn: a copy (`Clone` keeps its
/// own heap stack) renamed in place.
fn set_binds<'a>(p: &Pattern, names: &mut impl Iterator<Item = &'a Arc<str>>) -> Pattern {
    let mut q = p.clone();
    q.rename_binders(|x| *x = names.next().expect("one name per binder").clone());
    q
}
