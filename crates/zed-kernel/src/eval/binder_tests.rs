//! Plan row TEST-reads-binder-forms: [`super::made::reads`] leaves out a name read in a lambda
//! body where a binder [`kids`] reports scopes it, so it is right only if `kids` reports, for
//! each form, exactly the names the evaluator binds over each part. These tests check `kids`
//! form by form against the binding sites of `eval.rs`, and `reads` against a free-name walk
//! by recursion on the tree written from those sites, not from `kids`: equal on a tree, a
//! superset where a node is reached twice. Each was seen to fail with that form's binders
//! broken in `kids` (the negative controls, run once and not kept; the running log has them).

use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use crate::term::build::{app, lam, let_, lit, prim, var};
use crate::term::walk::{Built, Kid, kids, rebuild};
use crate::term::{Evidence, FixKind, GuardPos, Pattern, Prim, Shared, Term, Witness};
use crate::value::Value;
use zed_hash::Xorshift64;

/// The names `p` binds, each match of a `Bind`, by recursion: `matches` binds every `Bind` of a
/// pattern that matches (eval.rs `matches_any`, `matches`), and no other pattern binds.
fn pattern_names(p: &Pattern, out: &mut Vec<Arc<str>>) {
    match p {
        Pattern::Bind(x) => out.push(x.clone()),
        Pattern::Atom(_, ps) | Pattern::Tuple(ps) => ps.iter().for_each(|p| pattern_names(p, out)),
        Pattern::Fields(_, fs) => fs.iter().for_each(|(_, p)| pattern_names(p, out)),
        Pattern::Wild | Pattern::Lit(_) | Pattern::AnyAtom | Pattern::Is(_) => {}
    }
}

/// The free names of `t` under the names `bound`, by recursion on the tree, each binder written
/// out from where the evaluator binds (eval.rs): `apply` binds a closure's parameters over its
/// body; `Wait::Let` binds a `let`'s name over its body, its value evaluated outside; each
/// `match` arm runs in a copy of the environment with its pattern's names; `fam` binds its key
/// over its body per entry, its domain evaluated outside; a definedness `fix`'s `attempt` binds
/// `this` and `key` over its step; every other part (a lattice `fix`'s init, step and join
/// included) is an operand evaluated in the environment around it. Every field is named, so a
/// part added to a form fails to compile here until it is placed.
fn tree_free(t: &Term, bound: &mut Vec<Arc<str>>, out: &mut BTreeSet<Arc<str>>) {
    fn under(
        t: &Term,
        names: &[Arc<str>],
        bound: &mut Vec<Arc<str>>,
        out: &mut BTreeSet<Arc<str>>,
    ) {
        // A node [`upper_of`] marks is read with no name bound, its binder's included.
        if APART.with(|a| a.borrow().contains(&(t as *const Term))) {
            tree_free(t, &mut Vec::new(), out);
            return;
        }
        let n = bound.len();
        bound.extend(names.iter().cloned());
        tree_free(t, bound, out);
        bound.truncate(n);
    }
    let none: &[Arc<str>] = &[];
    match t {
        Term::Var(x) => {
            if !bound.contains(x) {
                out.insert(x.clone());
            }
        }
        Term::Lit(_) | Term::PrimFn(_) | Term::Read(_) => {}
        Term::Lam(xs, b) => under(b, xs, bound, out),
        Term::App(f, args) => {
            under(f, none, bound, out);
            args.iter().for_each(|a| under(a, none, bound, out));
        }
        Term::Prim(_, args) => args.iter().for_each(|a| under(a, none, bound, out)),
        Term::Let(x, e, b) => {
            under(e, none, bound, out);
            under(b, std::slice::from_ref(x), bound, out);
        }
        Term::If(c, a, b) => [c, a, b]
            .into_iter()
            .for_each(|s| under(s, none, bound, out)),
        Term::Match(e, arms) => {
            under(e, none, bound, out);
            for (p, body) in arms {
                let mut names = Vec::new();
                pattern_names(p, &mut names);
                under(body, &names, bound, out);
            }
        }
        Term::Fam { domain, var, body } => {
            under(domain, none, bound, out);
            under(body, std::slice::from_ref(var), bound, out);
        }
        Term::Reindex {
            family,
            kf,
            vf,
            witness: _,
        } => [family, kf, vf]
            .into_iter()
            .for_each(|s| under(s, none, bound, out)),
        Term::Discard { family, sel } => [family, sel]
            .into_iter()
            .for_each(|s| under(s, none, bound, out)),
        Term::Fold {
            family,
            op,
            identity,
            depth: _,
            ev: _,
        } => [Some(family), Some(op), identity.as_ref()]
            .into_iter()
            .flatten()
            .for_each(|s| under(s, none, bound, out)),
        Term::Fix {
            init,
            step,
            this,
            key,
            kind,
            ev: _,
        } => {
            under(init, none, bound, out);
            match kind {
                FixKind::Definedness => under(step, &[this.clone(), key.clone()], bound, out),
                FixKind::Lattice { join } => {
                    under(step, none, bound, out);
                    under(join, none, bound, out);
                }
            }
        }
        Term::Gen {
            init,
            step,
            guard,
            pos: _,
        } => [init, step, guard]
            .into_iter()
            .for_each(|s| under(s, none, bound, out)),
        Term::Push(_, v) => under(v, none, bound, out),
    }
}

fn free_of(t: &Term) -> Vec<String> {
    let mut out = BTreeSet::new();
    tree_free(t, &mut Vec::new(), &mut out);
    out.iter().map(|x| x.to_string()).collect()
}

std::thread_local! {
    /// The nodes [`tree_free`] reads with no name bound: empty but inside [`upper_of`].
    static APART: std::cell::RefCell<HashSet<*const Term>> = Default::default();
}

/// An upper bound on `reads` of `t` where parts are shared: the tree walk's free names, with no
/// name bound at a node that two or more references reach anywhere in `t`. `reads` reads a
/// node reached twice in its region with no name bound, and every other node under the
/// binders of the one path to it within the region, then takes a nested lambda's parameters
/// and the names bound around it out of its set; a node reached twice in `t` is reached twice
/// in a region or once in each of two, so `reads` binds at least what this binds, and gives
/// at most these names. Tighter than every variable of `t`: a name read only where a binder
/// on its one path binds it is left out.
fn upper_of(t: &Term) -> Vec<String> {
    let mut count: HashMap<*const Term, u32> = HashMap::new();
    let mut stack = vec![t];
    while let Some(u) = stack.pop() {
        kids(u, |k, _| match k {
            Kid::Inline(v) => stack.push(v),
            Kid::Shared(s) => {
                let n = count.entry(&**s as *const Term).or_insert(0);
                *n += 1;
                if *n == 1 {
                    stack.push(s);
                }
            }
        });
    }
    let apart = (count.into_iter()).filter_map(|(p, n)| (n >= 2).then_some(p));
    APART.with(|a| *a.borrow_mut() = apart.collect());
    let mut out = BTreeSet::new();
    tree_free(t, &mut Vec::new(), &mut out);
    APART.with(|a| a.borrow_mut().clear());
    out.iter().map(|x| x.to_string()).collect()
}

fn reads_of(t: Term) -> Vec<String> {
    super::made::reads(&Shared::new(t))
        .iter()
        .map(|x| x.to_string())
        .collect()
}

/// `reads` of `t` as a lambda body, checked equal to the tree walk and to `want`.
fn exact(t: Term, want: &[&str]) {
    let tree = free_of(&t);
    let got = reads_of(t);
    assert_eq!(got, tree, "reads against the tree walk");
    assert_eq!(got, want, "reads against the names written");
}

fn sh(t: Term) -> Shared {
    Shared::new(t)
}

fn add(a: Term, b: Term) -> Term {
    prim(Prim::Add, vec![a, b])
}

fn fix(init: Term, step: Term, this: &str, key: &str, kind: FixKind) -> Term {
    Term::Fix {
        init: sh(init),
        step: sh(step),
        this: this.into(),
        key: key.into(),
        kind,
        ev: Evidence::new(),
    }
}

fn lattice(join: Term) -> FixKind {
    FixKind::Lattice { join: sh(join) }
}

fn fam(domain: Term, i: &str, body: Term) -> Term {
    Term::Fam {
        domain: sh(domain),
        var: i.into(),
        body: sh(body),
    }
}

fn bind(x: &str) -> Pattern {
    Pattern::Bind(x.into())
}

/// The names `kids` reports over each part of `t`, in its order.
fn kid_binds(t: &Term) -> Vec<Vec<String>> {
    let mut out = Vec::new();
    kids(t, |_, b| {
        let mut names = Vec::new();
        b.each(|x| names.push(x.to_string()));
        out.push(names);
    });
    out
}

/// `kids` reports, for every form, the names the evaluator binds over each part, as
/// [`tree_free`] lists them, and no others.
#[test]
fn kids_reports_the_names_the_evaluator_binds_over_each_part_of_every_form() {
    let v = || var("v");
    let none: Vec<String> = Vec::new();
    let names = |xs: &[&str]| -> Vec<String> { xs.iter().map(|x| x.to_string()).collect() };
    let cases: Vec<(&str, Term, Vec<Vec<String>>)> = vec![
        ("var", v(), vec![]),
        ("lit", lit(1i64), vec![]),
        ("primfn", Term::PrimFn(Prim::Add), vec![]),
        ("read", Term::Read("p".into()), vec![]),
        ("lam", lam(&["a", "b"], v()), vec![names(&["a", "b"])]),
        ("app", app(v(), vec![v(), v()]), vec![none.clone(); 3]),
        ("prim", add(v(), v()), vec![none.clone(); 2]),
        (
            "let",
            let_("x", v(), v()),
            vec![none.clone(), names(&["x"])],
        ),
        (
            "if",
            Term::If(sh(v()), sh(v()), sh(v())),
            vec![none.clone(); 3],
        ),
        (
            "match",
            Term::Match(
                sh(v()),
                vec![
                    (
                        Pattern::Tuple(vec![
                            bind("p"),
                            Pattern::Atom("a".into(), vec![bind("q"), Pattern::Wild]),
                            Pattern::Fields("s".into(), vec![("f".into(), bind("r"))]),
                            Pattern::Lit(Value::Int(0)),
                            Pattern::AnyAtom,
                        ]),
                        v(),
                    ),
                    (Pattern::Wild, v()),
                    (bind("z"), v()),
                ],
            ),
            vec![
                none.clone(),
                names(&["p", "q", "r"]),
                none.clone(),
                names(&["z"]),
            ],
        ),
        ("fam", fam(v(), "i", v()), vec![none.clone(), names(&["i"])]),
        (
            "reindex",
            Term::Reindex {
                family: sh(v()),
                kf: sh(v()),
                vf: sh(v()),
                witness: Witness::Residue,
            },
            vec![none.clone(); 3],
        ),
        (
            "discard",
            Term::Discard {
                family: sh(v()),
                sel: sh(v()),
            },
            vec![none.clone(); 2],
        ),
        (
            "fold",
            Term::Fold {
                family: sh(v()),
                op: sh(v()),
                identity: None,
                depth: 1,
                ev: Evidence::new(),
            },
            vec![none.clone(); 2],
        ),
        (
            "fold with identity",
            Term::Fold {
                family: sh(v()),
                op: sh(v()),
                identity: Some(sh(v())),
                depth: 1,
                ev: Evidence::new(),
            },
            vec![none.clone(); 3],
        ),
        (
            "definedness fix",
            fix(v(), v(), "this", "k", FixKind::Definedness),
            vec![none.clone(), names(&["this", "k"])],
        ),
        (
            "lattice fix",
            fix(v(), v(), "this", "k", lattice(v())),
            vec![none.clone(); 3],
        ),
        (
            "gen",
            Term::Gen {
                init: sh(v()),
                step: sh(v()),
                guard: sh(v()),
                pos: GuardPos::After,
            },
            vec![none.clone(); 3],
        ),
        ("push", Term::Push("p".into(), sh(v())), vec![none.clone()]),
    ];
    for (form, t, want) in cases {
        assert_eq!(kid_binds(&t), want, "{form}");
    }
}

#[test]
fn a_lambda_binds_its_parameters_over_its_body_only() {
    exact(lam(&["a", "b"], add(var("a"), var("c"))), &["c"]);
    // Nested and shadowed: the inner `a` is the inner parameter; the outer body reads `b`.
    let inner = lam(&["a"], add(var("a"), var("b")));
    exact(lam(&["b"], app(inner.clone(), vec![var("a")])), &["a"]);
    exact(app(inner, vec![var("a")]), &["a", "b"]);
    // A parameter bound twice, by two lambdas, is still bound under the inner one.
    exact(lam(&["x"], lam(&["x"], var("x"))), &[]);
}

#[test]
fn a_let_binds_its_name_over_its_body_not_its_value() {
    exact(let_("x", var("x"), var("x")), &["x"]);
    exact(let_("x", var("y"), add(var("x"), var("z"))), &["y", "z"]);
    // Shadowed: the inner `let` reads the outer `x` in its value.
    exact(let_("x", var("a"), let_("x", var("x"), var("x"))), &["a"]);
    // Beside the `let`, the name is free.
    exact(add(let_("x", lit(0i64), var("x")), var("x")), &["x"]);
}

#[test]
fn a_match_arm_binds_its_pattern_names_over_that_arm_only() {
    let pat = Pattern::Tuple(vec![
        bind("p"),
        Pattern::Atom("a".into(), vec![bind("q")]),
        Pattern::Fields("s".into(), vec![("f".into(), bind("r"))]),
    ]);
    let all = || add(var("p"), add(var("q"), add(var("r"), var("w"))));
    let m = Term::Match(
        sh(var("s")),
        vec![
            (pat, all()),
            (Pattern::Wild, var("v")),
            (bind("w"), var("w")),
        ],
    );
    // The scrutinee reads `s`; the first arm binds `p`, `q` and `r` and reads `w`; the wild arm
    // reads `v`; the third arm binds the `w` it reads.
    exact(m, &["s", "v", "w"]);
    // The scrutinee is outside every arm's names.
    exact(
        Term::Match(sh(var("w")), vec![(bind("w"), var("w"))]),
        &["w"],
    );
    // A pattern that binds nothing: a literal, `#_`, `is T` and `_` arms.
    let none = Term::Match(
        sh(lit(0i64)),
        vec![
            (Pattern::Lit(Value::Int(0)), var("a")),
            (Pattern::AnyAtom, var("b")),
            (Pattern::Is(crate::types::Type::int()), var("c")),
            (Pattern::Wild, var("d")),
        ],
    );
    exact(none, &["a", "b", "c", "d"]);
    // Nested matches, the inner arm's name shadowing the outer one's.
    let inner = Term::Match(sh(var("y")), vec![(bind("y"), add(var("y"), var("z")))]);
    exact(
        Term::Match(sh(var("s")), vec![(bind("y"), inner)]),
        &["s", "z"],
    );
}

#[test]
fn a_fam_binds_its_key_over_its_body_not_its_domain() {
    exact(fam(var("i"), "i", add(var("i"), var("y"))), &["i", "y"]);
    exact(fam(var("d"), "i", fam(var("i"), "i", var("i"))), &["d"]);
}

#[test]
fn a_definedness_fix_binds_this_and_key_over_its_step_only() {
    let step = || add(app(var("this"), vec![var("k")]), var("y"));
    exact(
        fix(var("this"), step(), "this", "k", FixKind::Definedness),
        &["this", "y"],
    );
    exact(
        fix(var("k"), step(), "this", "k", FixKind::Definedness),
        &["k", "y"],
    );
    // Nested, the inner `this` naming the inner family.
    let inner = fix(var("this"), var("this"), "this", "k", FixKind::Definedness);
    exact(
        fix(lit(0i64), inner, "this", "j", FixKind::Definedness),
        &[],
    );
}

#[test]
fn a_lattice_fix_binds_nothing_over_its_init_step_or_join() {
    let t = fix(var("this"), var("this"), "this", "k", lattice(var("k")));
    exact(t, &["k", "this"]);
    // Under a definedness fix of the same names, the lattice's reads are bound by it.
    let inner = fix(lit(0i64), var("this"), "this", "k", lattice(var("k")));
    exact(
        fix(lit(0i64), inner, "this", "k", FixKind::Definedness),
        &[],
    );
}

#[test]
fn the_forms_that_bind_nothing_leave_every_name_free() {
    let r = |x: &str| sh(var(x));
    exact(app(var("f"), vec![var("a")]), &["a", "f"]);
    exact(Term::If(r("c"), r("a"), r("b")), &["a", "b", "c"]);
    let reindex = Term::Reindex {
        family: r("f"),
        kf: r("g"),
        vf: r("h"),
        witness: Witness::Residue,
    };
    exact(reindex, &["f", "g", "h"]);
    exact(
        Term::Discard {
            family: r("f"),
            sel: r("s"),
        },
        &["f", "s"],
    );
    let fold = |identity| Term::Fold {
        family: r("f"),
        op: r("o"),
        identity,
        depth: 1,
        ev: Evidence::new(),
    };
    exact(fold(None), &["f", "o"]);
    exact(fold(Some(r("e"))), &["e", "f", "o"]);
    let generations = Term::Gen {
        init: r("i"),
        step: r("s"),
        guard: r("g"),
        pos: GuardPos::Before,
    };
    exact(generations, &["g", "i", "s"]);
    exact(Term::Push("p".into(), r("v")), &["v"]);
    exact(Term::Read("p".into()), &[]);
}

/// A binder form by name, and the term it makes with a given part under it.
type Binder = (&'static str, fn(Shared) -> Term);

/// The binders of one name `x` over a part, as each form writes it; the last binds nothing.
fn binders() -> Vec<Binder> {
    vec![
        ("lam", |n| Term::Lam(vec!["x".into()], n)),
        ("let", |n| Term::Let("x".into(), sh(lit(0i64)), n)),
        ("match", |n| {
            Term::Match(sh(lit(0i64)), vec![(bind("x"), Term::clone(&n))])
        }),
        ("fam", |n| Term::Fam {
            domain: sh(lit(0i64)),
            var: "x".into(),
            body: n,
        }),
        ("definedness fix", |n| Term::Fix {
            init: sh(lit(0i64)),
            step: n,
            this: "x".into(),
            key: "j".into(),
            kind: FixKind::Definedness,
            ev: Evidence::new(),
        }),
        ("lattice fix", |n| Term::Fix {
            init: sh(lit(0i64)),
            step: n,
            this: "x".into(),
            key: "j".into(),
            kind: FixKind::Lattice {
                join: sh(lit(0i64)),
            },
            ev: Evidence::new(),
        }),
    ]
}

/// A node shared under two binders, of every pair of forms, is read under no scope: `reads`
/// keeps every name the tree walk finds and adds only names the node reads (here `x`, bound
/// above it by one or both), never drops one. The `match` arm holds its body in place, so its
/// copy of the node is a second node of the same term: there the result is exact.
#[test]
fn a_node_under_two_binders_keeps_every_name_either_needs() {
    for (a, wrap_a) in binders() {
        for (b, wrap_b) in binders() {
            let node = sh(add(var("x"), var("y")));
            let t = prim(
                Prim::Tuple,
                vec![wrap_a(node.clone()), wrap_b(node.clone())],
            );
            let tree = free_of(&t);
            let got = reads_of(t);
            let what = format!("{a} and {b}");
            assert!(
                tree.iter().all(|x| got.contains(x)),
                "{what}: {got:?} ⊉ {tree:?}"
            );
            assert!(got.iter().all(|x| x == "x" || x == "y"), "{what}: {got:?}");
            assert!(got.iter().any(|i| i == "y"), "{what}: {got:?}");
        }
    }
}

/// A body shared by two lambdas of different parameters, and by a lambda and the region around
/// it, keeps one set, the body's, found in either order.
#[test]
fn a_body_shared_by_two_lambdas_has_one_set_whichever_is_read_first() {
    for first in [0, 1, 2] {
        let body = sh(add(var("x"), var("y")));
        let f = Term::Lam(vec!["x".into()], body.clone());
        let g = Term::Lam(vec!["y".into()], body.clone());
        let top = prim(Prim::Tuple, vec![f, g, Term::clone(&body)]);
        let top = sh(Term::Let("x".into(), sh(lit(0i64)), sh(top)));
        let names = |s: &Shared| -> Vec<String> {
            super::made::reads(s)
                .iter()
                .map(|x| x.to_string())
                .collect()
        };
        match first {
            0 => assert_eq!(names(&body), ["x", "y"]),
            1 => assert_eq!(names(&top), ["y"]),
            _ => {}
        }
        // `top` binds `x` around the tuple: `f` adds `y`, `g` adds `x` (bound by the `let`),
        // and the copy of the body in place reads `y` under the `let`.
        assert_eq!(names(&top), ["y"], "{first}");
        assert_eq!(names(&body), ["x", "y"], "{first}");
    }
}

/// A small generator of terms over the first `names` of [`NAMES`], each form of the kernel and
/// its binders, so that a name is often both bound and read and binders shadow each other.
/// With `share`, a part is often a node made before; with `nest`, a part is often one node read
/// at three to five depths under binders of one name ([`Gen::nest`]). With 4 names and no
/// `nest`, it draws what it drew before row TEST-reads-deep-sharing, seed for seed. Its draws
/// are xorshift64's ([`Xorshift64`]), kept for that: the terms are pinned to the seeds.
struct Gen {
    rng: Xorshift64,
    pool: Vec<Shared>,
    share: bool,
    names: u64,
    nest: bool,
}

const NAMES: [&str; 6] = ["x", "y", "this", "k", "a", "b"];

impl Gen {
    fn name(&mut self) -> &'static str {
        NAMES[self.rng.below(self.names) as usize]
    }

    /// One node `s` read at each of three to five nested binders of one name `x`, each binder
    /// a form drawn in turn (a lambda, a `let`, a `fam`, a `match` arm, a definedness `fix`),
    /// and also read outside each as its operand (the `let`'s value, the domain, the
    /// scrutinee, the `fix`'s init): `s` is reached under every depth of binders of `x` from
    /// none to five, by a path that binds `x` and one that does not.
    fn nest(&mut self, d: u32) -> Term {
        let s = self.sub(d);
        let x: Arc<str> = self.name().into();
        let mut t = Term::If(sh(var(self.name())), s.clone(), s.clone());
        for _ in 0..3 + self.rng.below(3) {
            let body = sh(Term::If(sh(var(self.name())), s.clone(), sh(t)));
            t = match self.rng.below(5) {
                0 => Term::Lam(vec![x.clone()], body),
                1 => Term::Let(x.clone(), s.clone(), body),
                2 => Term::Fam {
                    domain: s.clone(),
                    var: x.clone(),
                    body,
                },
                3 => Term::Match(
                    s.clone(),
                    vec![(Pattern::Bind(x.clone()), Shared::unwrap_or_clone(body))],
                ),
                _ => Term::Fix {
                    init: s.clone(),
                    step: body,
                    this: x.clone(),
                    key: self.name().into(),
                    kind: FixKind::Definedness,
                    ev: Evidence::new(),
                },
            };
        }
        t
    }

    fn sub(&mut self, depth: u32) -> Shared {
        if self.share && !self.pool.is_empty() && self.rng.below(3) == 0 {
            let i = self.rng.below(self.pool.len() as u64) as usize;
            return self.pool[i].clone();
        }
        let s = sh(self.term(depth));
        self.pool.push(s.clone());
        s
    }

    fn pattern(&mut self, depth: u32) -> Pattern {
        match if depth == 0 {
            self.rng.below(3)
        } else {
            self.rng.below(7)
        } {
            0 => Pattern::Wild,
            1 => bind(self.name()),
            2 => Pattern::AnyAtom,
            3 => Pattern::Atom("a".into(), vec![self.pattern(depth - 1)]),
            4 => Pattern::Fields("s".into(), vec![("f".into(), self.pattern(depth - 1))]),
            5 => Pattern::Tuple(vec![self.pattern(depth - 1), self.pattern(depth - 1)]),
            _ => Pattern::Lit(Value::Int(0)),
        }
    }

    fn term(&mut self, depth: u32) -> Term {
        if depth == 0 {
            return match self.rng.below(3) {
                0 => lit(0i64),
                _ => var(self.name()),
            };
        }
        let d = depth - 1;
        if self.nest && self.rng.below(6) == 0 {
            return self.nest(d);
        }
        match self.rng.below(16) {
            0 => var(self.name()),
            1 => {
                let xs = [self.name(), self.name()];
                let k = 1 + self.rng.below(2) as usize;
                Term::Lam(xs[..k].iter().map(|&x| x.into()).collect(), self.sub(d))
            }
            2 => Term::App(self.sub(d), vec![self.term(d)]),
            3 => prim(Prim::Tuple, vec![self.term(d), self.term(d)]),
            4 => Term::Let(self.name().into(), self.sub(d), self.sub(d)),
            5 => Term::If(self.sub(d), self.sub(d), self.sub(d)),
            6 => {
                let s = self.sub(d);
                let arms = (0..1 + self.rng.below(2))
                    .map(|_| (self.pattern(2), self.term(d)))
                    .collect();
                Term::Match(s, arms)
            }
            7 => Term::Fam {
                domain: self.sub(d),
                var: self.name().into(),
                body: self.sub(d),
            },
            8 => Term::Reindex {
                family: self.sub(d),
                kf: self.sub(d),
                vf: self.sub(d),
                witness: Witness::Residue,
            },
            9 => Term::Discard {
                family: self.sub(d),
                sel: self.sub(d),
            },
            10 => Term::Fold {
                family: self.sub(d),
                op: self.sub(d),
                identity: (self.rng.below(2) == 0).then(|| self.sub(d)),
                depth: 1,
                ev: Evidence::new(),
            },
            11 | 12 => {
                let (init, step) = (self.sub(d), self.sub(d));
                let kind = match self.rng.below(2) {
                    0 => FixKind::Definedness,
                    _ => FixKind::Lattice { join: self.sub(d) },
                };
                Term::Fix {
                    init,
                    step,
                    this: self.name().into(),
                    key: self.name().into(),
                    kind,
                    ev: Evidence::new(),
                }
            }
            13 => Term::Gen {
                init: self.sub(d),
                step: self.sub(d),
                guard: self.sub(d),
                pos: GuardPos::After,
            },
            14 => Term::Push("p".into(), self.sub(d)),
            _ => lit(1i64),
        }
    }
}

/// The names `t` holds as variables, every one.
fn every_var(t: &Term, out: &mut BTreeSet<String>) {
    if let Term::Var(x) = t {
        out.insert(x.to_string());
    }
    kids(t, |k, _| match k {
        Kid::Shared(s) => every_var(s, out),
        Kid::Inline(u) => every_var(u, out),
    });
}

/// On 20,000 trees of every form, `reads` is the tree walk's set exactly; on 20,000 terms whose
/// parts are shared at random, it holds the tree walk's set and only names the term reads.
#[test]
fn reads_agrees_with_a_walk_of_the_tree_on_random_terms() {
    for share in [false, true] {
        for seed in 1..=20_000u64 {
            let mut g = Gen {
                rng: Xorshift64::new(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1),
                pool: Vec::new(),
                share,
                names: 4,
                nest: false,
            };
            let t = g.term(5);
            let tree = free_of(&t);
            let mut vars = BTreeSet::new();
            every_var(&t, &mut vars);
            let got = reads_of(t.clone());
            match share {
                false => assert_eq!(got, tree, "seed {seed}: {t:?}"),
                true => {
                    assert!(
                        tree.iter().all(|x| got.contains(x)),
                        "seed {seed}: {got:?} ⊉ {tree:?}: {t:?}"
                    );
                    assert!(got.iter().all(|x| vars.contains(x)), "seed {seed}: {t:?}");
                }
            }
        }
    }
}

/// On 20,000 terms over six names, of depth 3 to 6 by seed, whose parts are shared at random
/// and often one node is read under three to five nested binders of one name
/// ([`Gen::nest`]): `reads` holds the tree walk's set and lies within [`upper_of`], which
/// leaves out a name read only where the binders on its one path bind it (row
/// TEST-reads-deep-sharing). Seen to fail with `scoped_names` reading every shared node
/// inside a node reached twice apart too, which the test above misses.
#[test]
fn reads_lies_between_the_tree_walk_and_the_shared_bound_on_deeply_shared_terms() {
    for seed in 1..=20_000u64 {
        let mut g = Gen {
            rng: Xorshift64::new(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1),
            pool: Vec::new(),
            share: true,
            names: NAMES.len() as u64,
            nest: true,
        };
        let t = g.term(3 + (seed % 4) as u32);
        let tree = free_of(&t);
        let upper = upper_of(&t);
        let got = reads_of(t.clone());
        assert!(
            tree.iter().all(|x| got.contains(x)),
            "seed {seed}: {got:?} ⊉ {tree:?}: {t:?}"
        );
        assert!(
            got.iter().all(|x| upper.contains(x)),
            "seed {seed}: {got:?} ⊈ {upper:?}: {t:?}"
        );
    }
}

/// [`Pattern::binders`], [`Pattern::bound_names`] and [`Pattern::rename_binders`] reach the
/// names [`pattern_names`] finds by recursion, in its order (the order written, which numbers
/// a ZIR `match` arm's arguments), on a pattern of every kind with two fields and on 5,000
/// random patterns; renaming keeps the shape. On a tuple nested 100,000 deep, which the
/// recursion would not survive, the names come in the order built. Seen to fail with the
/// children pushed without `rev()`, as the binder count in `zedc::zir::binds` pushes them.
#[test]
fn a_pattern_gives_and_renames_its_binders_in_the_order_written() {
    let check = |p: &Pattern, what: &str| {
        let mut want = Vec::new();
        pattern_names(p, &mut want);
        let mut got = Vec::new();
        p.binders(|x| got.push(x.clone()));
        assert_eq!(got, want, "{what}: {p:?}");
        assert_eq!(p.bound_names(), want, "{what}: {p:?}");
        let mut q = p.clone();
        let mut k = 0;
        q.rename_binders(|x| {
            *x = format!("n{k}").into();
            k += 1;
        });
        let mut renamed = Vec::new();
        pattern_names(&q, &mut renamed);
        let numbered: Vec<Arc<str>> = (0..k).map(|i| format!("n{i}").into()).collect();
        assert_eq!(renamed, numbered, "{what}: {p:?}");
        let mut back = want.iter();
        q.rename_binders(|x| *x = back.next().expect("one name per binder").clone());
        assert!(q == *p, "{what}: {q:?} is not {p:?}");
    };
    check(
        &Pattern::Tuple(vec![
            bind("x"),
            Pattern::Fields(
                "s".into(),
                vec![("f".into(), bind("y")), ("g".into(), bind("k"))],
            ),
            Pattern::Atom("a".into(), vec![Pattern::Wild, bind("a"), Pattern::AnyAtom]),
            Pattern::Lit(Value::Int(0)),
            Pattern::Is(crate::types::Type::int()),
            bind("b"),
        ]),
        "every kind",
    );
    for seed in 1..=5_000u64 {
        let mut g = Gen {
            rng: Xorshift64::new(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1),
            pool: Vec::new(),
            share: false,
            names: 6,
            nest: false,
        };
        check(&g.pattern(6), &format!("seed {seed}"));
    }
    let depth = 100_000;
    let mut deep = Pattern::Wild;
    for i in 0..depth {
        deep = Pattern::Tuple(vec![bind(&format!("x{i}")), deep]);
    }
    let mut got = Vec::new();
    deep.binders(|x| got.push(x.clone()));
    let want: Vec<Arc<str>> = (0..depth).rev().map(|i| format!("x{i}").into()).collect();
    assert_eq!(got, want);
    let mut k = 0;
    deep.rename_binders(|x| {
        *x = format!("n{k}").into();
        k += 1;
    });
    assert_eq!(k, depth);
}

/// A term of each form with parts, its `i`th part `part(i)` in the order the form's fields are
/// written, which is the order the walks `kids` replaced (in `zedc-zir` canon/binders.rs and
/// `zedc-preimage` address.rs) gave them.
fn every_form(part: &dyn Fn(i64) -> Term) -> Vec<Term> {
    let s = |i| sh(part(i));
    vec![
        Term::Lam(vec!["x".into()], s(0)),
        Term::App(s(0), vec![part(1), part(2)]),
        prim(Prim::Tuple, vec![part(0), part(1)]),
        Term::Let("x".into(), s(0), s(1)),
        Term::If(s(0), s(1), s(2)),
        Term::Match(s(0), vec![(bind("x"), part(1)), (Pattern::Wild, part(2))]),
        Term::Fam {
            domain: s(0),
            var: "x".into(),
            body: s(1),
        },
        Term::Reindex {
            family: s(0),
            kf: s(1),
            vf: s(2),
            witness: Witness::Residue,
        },
        Term::Discard {
            family: s(0),
            sel: s(1),
        },
        Term::Fold {
            family: s(0),
            op: s(1),
            identity: Some(s(2)),
            depth: 1,
            ev: Evidence::new(),
        },
        Term::Fold {
            family: s(0),
            op: s(1),
            identity: None,
            depth: 1,
            ev: Evidence::new(),
        },
        fix(part(0), part(1), "this", "k", FixKind::Definedness),
        fix(part(0), part(1), "this", "k", lattice(part(2))),
        Term::Gen {
            init: s(0),
            step: s(1),
            guard: s(2),
            pos: GuardPos::After,
        },
        Term::Push("p".into(), s(0)),
    ]
}

/// Row DRY-text-shared made `kids` and `rebuild` the one walk over a term's parts: `kids` gives
/// each form's parts in the order its fields are written, `rebuild` puts parts back in that
/// order, and `rebuild(t, kids(t))` is `t`, holding each node given as a node. Seen red with
/// `rebuild` reading a `let`'s value and body the other way round.
#[test]
fn rebuild_puts_back_the_parts_kids_gives_in_the_same_order() {
    let lits = every_form(&|i| lit(i));
    let moved = every_form(&|i| lit(100 + i));
    for (t, want) in lits.iter().zip(&moved) {
        let mut got = Vec::new();
        kids(t, |k, _| got.push(k.term().clone()));
        let n = got.len() as i64;
        assert_eq!(got, (0..n).map(lit).collect::<Vec<_>>(), "{t:?}");
        let parts = (0..n).map(|i| Built::Term(lit(100 + i)));
        assert_eq!(&rebuild(t, parts), want, "{t:?}");
    }
    for seed in 1..=20_000u64 {
        let mut g = Gen {
            rng: Xorshift64::new(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1),
            pool: Vec::new(),
            share: true,
            names: 4,
            nest: true,
        };
        let t = g.term(5);
        let (mut held, mut parts, mut fresh) = (Vec::new(), Vec::new(), Vec::new());
        kids(&t, |k, _| {
            if let Kid::Shared(s) = k {
                held.push(s.id());
            }
            parts.push(match k {
                Kid::Shared(s) => Built::Shared(s.clone()),
                Kid::Inline(u) => Built::Term(u.clone()),
            });
            fresh.push(Built::Term(k.term().clone()));
        });
        let back = rebuild(&t, parts);
        assert_eq!(back, t, "seed {seed}");
        let mut ids = Vec::new();
        kids(&back, |k, _| {
            if let Kid::Shared(s) = k {
                ids.push(s.id());
            }
        });
        assert_eq!(ids, held, "seed {seed}: each node given is held");
        assert_eq!(rebuild(&t, fresh), t, "seed {seed}");
    }
}
