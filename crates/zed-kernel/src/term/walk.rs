//! `Clone`, `==` and `Debug` of [`Term`] and [`Pattern`], each keeping its own stack on the
//! heap, so a term of any depth is copied, compared and written on a small stack (COMPLEXITY.md
//! K39). Each costs O(size): a copy shares every [`Shared`] subterm, `==` reads a pair of shared
//! subterms once, and `Debug` writes each part once.

use std::collections::HashSet;
use std::fmt;
use std::sync::Arc;

use super::{FixKind, Pattern, Shared, Term};

/// Copies `t` with the parts that are not shared, the arguments of calls and primitives and
/// the arms of a `match`, copied too; a [`Shared`] subterm is a reference count.
fn shallow(t: &Term) -> Term {
    match t {
        Term::Lit(v) => Term::Lit(v.clone()),
        Term::Var(x) => Term::Var(x.clone()),
        Term::Lam(xs, b) => Term::Lam(xs.clone(), b.clone()),
        Term::PrimFn(p) => Term::PrimFn(*p),
        Term::Let(x, a, b) => Term::Let(x.clone(), a.clone(), b.clone()),
        Term::If(a, b, c) => Term::If(a.clone(), b.clone(), c.clone()),
        Term::Fam { domain, var, body } => Term::Fam {
            domain: domain.clone(),
            var: var.clone(),
            body: body.clone(),
        },
        Term::Reindex {
            family,
            kf,
            vf,
            witness,
        } => Term::Reindex {
            family: family.clone(),
            kf: kf.clone(),
            vf: vf.clone(),
            witness: witness.clone(),
        },
        Term::Discard { family, sel } => Term::Discard {
            family: family.clone(),
            sel: sel.clone(),
        },
        Term::Fold {
            family,
            op,
            identity,
            depth,
            ev,
        } => Term::Fold {
            family: family.clone(),
            op: op.clone(),
            identity: identity.clone(),
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
            init: init.clone(),
            step: step.clone(),
            this: this.clone(),
            key: key.clone(),
            kind: kind.clone(),
            ev: ev.clone(),
        },
        Term::Gen {
            init,
            step,
            guard,
            pos,
        } => Term::Gen {
            init: init.clone(),
            step: step.clone(),
            guard: guard.clone(),
            pos: *pos,
        },
        Term::Read(x) => Term::Read(x.clone()),
        Term::Push(x, v) => Term::Push(x.clone(), v.clone()),
        Term::App(..) | Term::Prim(..) | Term::Match(..) => {
            unreachable!("a term with parts of its own is copied by `copy`")
        }
    }
}

/// What is left of a copy: a part to copy, or a node whose parts are copied, to rebuild.
enum Part<'a> {
    Term(&'a Term),
    Pattern(&'a Pattern),
    Rebuild(&'a Term),
    RebuildPattern(&'a Pattern),
}

/// The copies of the parts read so far, in the order read.
#[derive(Default)]
struct Copied {
    terms: Vec<Term>,
    patterns: Vec<Pattern>,
}

impl Copied {
    fn last_terms(&mut self, n: usize) -> Vec<Term> {
        self.terms.split_off(self.terms.len() - n)
    }

    fn last_patterns(&mut self, n: usize) -> Vec<Pattern> {
        self.patterns.split_off(self.patterns.len() - n)
    }
}

/// Copies `first` in a loop: each node with parts of its own is rebuilt once they are copied.
fn copy(first: Part<'_>) -> Copied {
    let mut todo = vec![first];
    let mut done = Copied::default();
    while let Some(c) = todo.pop() {
        match c {
            Part::Term(t) => match t {
                Term::App(_, args) | Term::Prim(_, args) => {
                    todo.push(Part::Rebuild(t));
                    todo.extend(args.iter().rev().map(Part::Term));
                }
                Term::Match(_, arms) => {
                    todo.push(Part::Rebuild(t));
                    for (p, b) in arms.iter().rev() {
                        todo.extend([Part::Term(b), Part::Pattern(p)]);
                    }
                }
                _ => done.terms.push(shallow(t)),
            },
            Part::Rebuild(t) => {
                let t = match t {
                    Term::App(f, args) => Term::App(f.clone(), done.last_terms(args.len())),
                    Term::Prim(p, args) => Term::Prim(*p, done.last_terms(args.len())),
                    Term::Match(e, arms) => {
                        let bodies = done.last_terms(arms.len());
                        let patterns = done.last_patterns(arms.len());
                        Term::Match(e.clone(), patterns.into_iter().zip(bodies).collect())
                    }
                    _ => unreachable!("only a term with parts of its own is rebuilt"),
                };
                done.terms.push(t);
            }
            Part::Pattern(p) => match p {
                Pattern::Atom(_, ps) | Pattern::Tuple(ps) => {
                    todo.push(Part::RebuildPattern(p));
                    todo.extend(ps.iter().rev().map(Part::Pattern));
                }
                Pattern::Fields(_, fs) => {
                    todo.push(Part::RebuildPattern(p));
                    todo.extend(fs.iter().rev().map(|(_, p)| Part::Pattern(p)));
                }
                Pattern::Wild => done.patterns.push(Pattern::Wild),
                Pattern::Bind(x) => done.patterns.push(Pattern::Bind(x.clone())),
                Pattern::Lit(v) => done.patterns.push(Pattern::Lit(v.clone())),
                Pattern::AnyAtom => done.patterns.push(Pattern::AnyAtom),
                Pattern::Is(t) => done.patterns.push(Pattern::Is(t.clone())),
            },
            Part::RebuildPattern(p) => {
                let p = match p {
                    Pattern::Atom(name, ps) => {
                        Pattern::Atom(name.clone(), done.last_patterns(ps.len()))
                    }
                    Pattern::Tuple(ps) => Pattern::Tuple(done.last_patterns(ps.len())),
                    Pattern::Fields(name, fs) => {
                        let ps = done.last_patterns(fs.len());
                        let fields = fs.iter().map(|(k, _)| k.clone()).zip(ps).collect();
                        Pattern::Fields(name.clone(), fields)
                    }
                    _ => unreachable!("only a pattern with parts of its own is rebuilt"),
                };
                done.patterns.push(p);
            }
        }
    }
    done
}

impl Clone for Term {
    fn clone(&self) -> Term {
        copy(Part::Term(self))
            .terms
            .pop()
            .expect("a copy leaves the one term copied")
    }
}

impl Clone for Pattern {
    fn clone(&self) -> Pattern {
        copy(Part::Pattern(self))
            .patterns
            .pop()
            .expect("a copy leaves the one pattern copied")
    }
}

/// A pair of parts still to compare.
enum Pair<'a> {
    Terms(&'a Term, &'a Term),
    Patterns(&'a Pattern, &'a Pattern),
}

/// The pairs of parts left to compare, and the pairs of shared subterms already queued.
#[derive(Default)]
struct Comparing<'a> {
    todo: Vec<Pair<'a>>,
    // Complexity tradeoff: a pair of shared subterms is hashed once per meeting, a constant
    // cost on every comparison, so that a term that is a DAG compares in O(distinct pairs)
    // rather than O(paths), which grows exponentially with depth.
    queued: HashSet<(u64, u64)>,
}

impl<'a> Comparing<'a> {
    /// Queues two shared subterms, unless they are one subterm or the pair is queued already.
    fn shared(&mut self, a: &'a Shared, b: &'a Shared) {
        let (x, y) = (a.id(), b.id());
        if x != y && self.queued.insert((x, y)) {
            self.todo.push(Pair::Terms(a, b));
        }
    }

    fn terms(&mut self, a: &'a [Term], b: &'a [Term]) -> bool {
        a.len() == b.len() && {
            self.todo
                .extend(a.iter().zip(b).map(|(a, b)| Pair::Terms(a, b)));
            true
        }
    }

    fn patterns(&mut self, a: &'a [Pattern], b: &'a [Pattern]) -> bool {
        a.len() == b.len() && {
            self.todo
                .extend(a.iter().zip(b).map(|(a, b)| Pair::Patterns(a, b)));
            true
        }
    }

    /// Compares the parts of `a` and `b` that hold no term or pattern, and queues the rest;
    /// false when they differ.
    fn step(&mut self, a: &'a Term, b: &'a Term) -> bool {
        match (a, b) {
            (Term::Lit(x), Term::Lit(y)) => x == y,
            (Term::Var(x), Term::Var(y)) | (Term::Read(x), Term::Read(y)) => x == y,
            (Term::PrimFn(p), Term::PrimFn(q)) => p == q,
            (Term::Lam(xs, a), Term::Lam(ys, b)) => {
                self.shared(a, b);
                xs == ys
            }
            (Term::Push(x, a), Term::Push(y, b)) => {
                self.shared(a, b);
                x == y
            }
            (Term::App(f, xs), Term::App(g, ys)) => {
                self.shared(f, g);
                self.terms(xs, ys)
            }
            (Term::Prim(p, xs), Term::Prim(q, ys)) => p == q && self.terms(xs, ys),
            (Term::Let(x, a, b), Term::Let(y, c, d)) => {
                self.shared(a, c);
                self.shared(b, d);
                x == y
            }
            (Term::If(a, b, c), Term::If(d, e, g)) => {
                self.shared(a, d);
                self.shared(b, e);
                self.shared(c, g);
                true
            }
            (Term::Match(e, xs), Term::Match(g, ys)) => {
                self.shared(e, g);
                xs.len() == ys.len() && {
                    for ((p, s), (q, t)) in xs.iter().zip(ys) {
                        self.todo.extend([Pair::Patterns(p, q), Pair::Terms(s, t)]);
                    }
                    true
                }
            }
            (
                Term::Fam { domain, var, body },
                Term::Fam {
                    domain: d,
                    var: v,
                    body: b,
                },
            ) => {
                self.shared(domain, d);
                self.shared(body, b);
                var == v
            }
            (
                Term::Reindex {
                    family,
                    kf,
                    vf,
                    witness,
                },
                Term::Reindex {
                    family: g,
                    kf: k,
                    vf: v,
                    witness: w,
                },
            ) => {
                self.shared(family, g);
                self.shared(kf, k);
                self.shared(vf, v);
                witness == w
            }
            (Term::Discard { family, sel }, Term::Discard { family: g, sel: s }) => {
                self.shared(family, g);
                self.shared(sel, s);
                true
            }
            (
                Term::Fold {
                    family,
                    op,
                    identity,
                    depth,
                    ev,
                },
                Term::Fold {
                    family: g,
                    op: o,
                    identity: i,
                    depth: d,
                    ev: e,
                },
            ) => {
                self.shared(family, g);
                self.shared(op, o);
                depth == d
                    && ev == e
                    && match (identity, i) {
                        (Some(a), Some(b)) => {
                            self.shared(a, b);
                            true
                        }
                        (None, None) => true,
                        _ => false,
                    }
            }
            (
                Term::Fix {
                    init,
                    step,
                    this,
                    key,
                    kind,
                    ev,
                },
                Term::Fix {
                    init: i,
                    step: s,
                    this: t,
                    key: k,
                    kind: c,
                    ev: e,
                },
            ) => {
                self.shared(init, i);
                self.shared(step, s);
                this == t
                    && key == k
                    && ev == e
                    && match (kind, c) {
                        (FixKind::Lattice { join: a }, FixKind::Lattice { join: b }) => {
                            self.shared(a, b);
                            true
                        }
                        (FixKind::Definedness, FixKind::Definedness) => true,
                        _ => false,
                    }
            }
            (
                Term::Gen {
                    init,
                    step,
                    guard,
                    pos,
                },
                Term::Gen {
                    init: i,
                    step: s,
                    guard: g,
                    pos: p,
                },
            ) => {
                self.shared(init, i);
                self.shared(step, s);
                self.shared(guard, g);
                pos == p
            }
            _ => false,
        }
    }

    /// As [`Comparing::step`], for two patterns.
    fn step_patterns(&mut self, a: &'a Pattern, b: &'a Pattern) -> bool {
        match (a, b) {
            (Pattern::Wild, Pattern::Wild) | (Pattern::AnyAtom, Pattern::AnyAtom) => true,
            (Pattern::Bind(x), Pattern::Bind(y)) => x == y,
            (Pattern::Lit(x), Pattern::Lit(y)) => x == y,
            (Pattern::Is(s), Pattern::Is(t)) => s == t,
            (Pattern::Atom(x, ps), Pattern::Atom(y, qs)) => x == y && self.patterns(ps, qs),
            (Pattern::Tuple(ps), Pattern::Tuple(qs)) => self.patterns(ps, qs),
            (Pattern::Fields(x, fs), Pattern::Fields(y, gs)) => {
                x == y
                    && fs.len() == gs.len()
                    && fs.iter().zip(gs).all(|((k, p), (l, q))| {
                        self.todo.push(Pair::Patterns(p, q));
                        k == l
                    })
            }
            _ => false,
        }
    }

    /// Whether every pair queued, and every pair of parts below it, is equal.
    fn run(mut self, first: Pair<'a>) -> bool {
        self.todo.push(first);
        while let Some(pair) = self.todo.pop() {
            let same = match pair {
                Pair::Terms(a, b) => self.step(a, b),
                Pair::Patterns(a, b) => self.step_patterns(a, b),
            };
            if !same {
                return false;
            }
        }
        true
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Term) -> bool {
        Comparing::default().run(Pair::Terms(self, other))
    }
}

impl PartialEq for Pattern {
    fn eq(&self, other: &Pattern) -> bool {
        Comparing::default().run(Pair::Patterns(self, other))
    }
}

/// What is left to write of a term's `Debug` text.
enum Show<'a> {
    Text(&'static str),
    /// A part that holds no term or pattern, written by its own `Debug`.
    Leaf(&'a dyn fmt::Debug),
    Term(&'a Term),
    Pattern(&'a Pattern),
    Arm(&'a (Pattern, Term)),
    Field(&'a (Arc<str>, Pattern)),
}

/// Queues `parts`, written in the order given.
fn put<'a, const N: usize>(todo: &mut Vec<Show<'a>>, parts: [Show<'a>; N]) {
    todo.extend(parts.into_iter().rev());
}

/// Queues `[a, b, …]`, each item written by `each`.
fn list<'a, T>(todo: &mut Vec<Show<'a>>, items: &'a [T], each: fn(&'a T) -> Show<'a>) {
    todo.push(Show::Text("]"));
    for (i, x) in items.iter().enumerate().rev() {
        todo.push(each(x));
        if i > 0 {
            todo.push(Show::Text(", "));
        }
    }
    todo.push(Show::Text("["));
}

/// Queues the text of `t`.
fn show_term<'a>(t: &'a Term, todo: &mut Vec<Show<'a>>) {
    use Show::{Leaf, Text};
    let tm = |s: &'a Shared| Show::Term(s);
    match t {
        Term::Lit(v) => put(todo, [Text("Lit("), Leaf(v), Text(")")]),
        Term::Var(x) => put(todo, [Text("Var("), Leaf(x), Text(")")]),
        Term::Read(x) => put(todo, [Text("Read("), Leaf(x), Text(")")]),
        Term::PrimFn(p) => put(todo, [Text("PrimFn("), Leaf(p), Text(")")]),
        Term::Lam(xs, b) => put(todo, [Text("Lam("), Leaf(xs), Text(", "), tm(b), Text(")")]),
        Term::Push(x, v) => put(todo, [Text("Push("), Leaf(x), Text(", "), tm(v), Text(")")]),
        Term::App(f, args) => {
            todo.push(Text(")"));
            list(todo, args, Show::Term);
            put(todo, [Text("App("), tm(f), Text(", ")]);
        }
        Term::Prim(p, args) => {
            todo.push(Text(")"));
            list(todo, args, Show::Term);
            put(todo, [Text("Prim("), Leaf(p), Text(", ")]);
        }
        Term::Let(x, a, b) => put(
            todo,
            [
                Text("Let("),
                Leaf(x),
                Text(", "),
                tm(a),
                Text(", "),
                tm(b),
                Text(")"),
            ],
        ),
        Term::If(a, b, c) => put(
            todo,
            [
                Text("If("),
                tm(a),
                Text(", "),
                tm(b),
                Text(", "),
                tm(c),
                Text(")"),
            ],
        ),
        Term::Match(e, arms) => {
            todo.push(Text(")"));
            list(todo, arms, Show::Arm);
            put(todo, [Text("Match("), tm(e), Text(", ")]);
        }
        Term::Fam { domain, var, body } => put(
            todo,
            [
                Text("Fam { domain: "),
                tm(domain),
                Text(", var: "),
                Leaf(var),
                Text(", body: "),
                tm(body),
                Text(" }"),
            ],
        ),
        Term::Reindex {
            family,
            kf,
            vf,
            witness,
        } => put(
            todo,
            [
                Text("Reindex { family: "),
                tm(family),
                Text(", kf: "),
                tm(kf),
                Text(", vf: "),
                tm(vf),
                Text(", witness: "),
                Leaf(witness),
                Text(" }"),
            ],
        ),
        Term::Discard { family, sel } => put(
            todo,
            [
                Text("Discard { family: "),
                tm(family),
                Text(", sel: "),
                tm(sel),
                Text(" }"),
            ],
        ),
        Term::Fold {
            family,
            op,
            identity,
            depth,
            ev,
        } => {
            put(
                todo,
                [
                    Text(", depth: "),
                    Leaf(depth),
                    Text(", ev: "),
                    Leaf(ev),
                    Text(" }"),
                ],
            );
            match identity {
                Some(i) => put(todo, [Text("Some("), tm(i), Text(")")]),
                None => todo.push(Text("None")),
            }
            put(
                todo,
                [
                    Text("Fold { family: "),
                    tm(family),
                    Text(", op: "),
                    tm(op),
                    Text(", identity: "),
                ],
            );
        }
        Term::Fix {
            init,
            step,
            this,
            key,
            kind,
            ev,
        } => {
            put(todo, [Text(", ev: "), Leaf(ev), Text(" }")]);
            match kind {
                FixKind::Lattice { join } => {
                    put(todo, [Text("Lattice { join: "), tm(join), Text(" }")])
                }
                FixKind::Definedness => todo.push(Text("Definedness")),
            }
            put(
                todo,
                [
                    Text("Fix { init: "),
                    tm(init),
                    Text(", step: "),
                    tm(step),
                    Text(", this: "),
                    Leaf(this),
                    Text(", key: "),
                    Leaf(key),
                    Text(", kind: "),
                ],
            );
        }
        Term::Gen {
            init,
            step,
            guard,
            pos,
        } => put(
            todo,
            [
                Text("Gen { init: "),
                tm(init),
                Text(", step: "),
                tm(step),
                Text(", guard: "),
                tm(guard),
                Text(", pos: "),
                Leaf(pos),
                Text(" }"),
            ],
        ),
    }
}

/// Queues the text of `p`.
fn show_pattern<'a>(p: &'a Pattern, todo: &mut Vec<Show<'a>>) {
    use Show::{Leaf, Text};
    match p {
        Pattern::Wild => todo.push(Text("Wild")),
        Pattern::AnyAtom => todo.push(Text("AnyAtom")),
        Pattern::Bind(x) => put(todo, [Text("Bind("), Leaf(x), Text(")")]),
        Pattern::Lit(v) => put(todo, [Text("Lit("), Leaf(v), Text(")")]),
        Pattern::Is(t) => put(todo, [Text("Is("), Leaf(t), Text(")")]),
        Pattern::Atom(name, ps) => {
            todo.push(Text(")"));
            list(todo, ps, Show::Pattern);
            put(todo, [Text("Atom("), Leaf(name), Text(", ")]);
        }
        Pattern::Tuple(ps) => {
            todo.push(Text(")"));
            list(todo, ps, Show::Pattern);
            todo.push(Text("Tuple("));
        }
        Pattern::Fields(name, fs) => {
            todo.push(Text(")"));
            list(todo, fs, Show::Field);
            put(todo, [Text("Fields("), Leaf(name), Text(", ")]);
        }
    }
}

/// Writes the queued text: the one line a derived `Debug` writes for `{:?}`, under `{:#?}` too.
fn run(mut todo: Vec<Show<'_>>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    while let Some(s) = todo.pop() {
        match s {
            Show::Text(s) => f.write_str(s)?,
            Show::Leaf(x) => write!(f, "{x:?}")?,
            Show::Term(t) => show_term(t, &mut todo),
            Show::Pattern(p) => show_pattern(p, &mut todo),
            Show::Arm((p, t)) => put(
                &mut todo,
                [
                    Show::Text("("),
                    Show::Pattern(p),
                    Show::Text(", "),
                    Show::Term(t),
                    Show::Text(")"),
                ],
            ),
            Show::Field((k, p)) => put(
                &mut todo,
                [
                    Show::Text("("),
                    Show::Leaf(k),
                    Show::Text(", "),
                    Show::Pattern(p),
                    Show::Text(")"),
                ],
            ),
        }
    }
    Ok(())
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        run(vec![Show::Term(self)], f)
    }
}

impl fmt::Debug for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        run(vec![Show::Pattern(self)], f)
    }
}
