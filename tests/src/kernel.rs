//! Builders for kernel terms and values, shared by the step tests that construct the terms a
//! program elaborates to (M0.9, M0.10).

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::{Evidence, Family, FixKind, Pattern, Prim, Term, Value, Witness};

/// Wraps a term for a field that holds a shared subterm.
pub fn rc(t: Term) -> Arc<Term> {
    Arc::new(t)
}

/// A string value.
pub fn s(x: &str) -> Value {
    Value::str(x)
}

/// `f[k]`: the entry of family `f` at top-level key `k`.
pub fn get(f: Term, k: Term) -> Term {
    prim(Prim::Get, vec![f, k])
}

/// A keypath built from its keys.
pub fn path(keys: Vec<Term>) -> Term {
    prim(Prim::Path, keys)
}

/// The `i`th key of keypath `p`.
pub fn key(p: Term, i: i64) -> Term {
    prim(Prim::PathKey, vec![p, lit(i)])
}

/// The `i`th component of tuple `t`.
pub fn nth(t: Term, i: i64) -> Term {
    prim(Prim::TupleGet, vec![t, lit(i)])
}

/// `a + b`.
pub fn add(a: Term, b: Term) -> Term {
    prim(Prim::Add, vec![a, b])
}

/// `reindex(F, kf, vf)` with a residue witness.
pub fn reindex(family: Term, kf: Term, vf: Term) -> Term {
    Term::Reindex {
        family: rc(family),
        kf: rc(kf),
        vf: rc(vf),
        witness: Witness::Residue,
    }
}

/// `fold(F, op, ev)` over a one-level `F`, with `identity` as the empty-level result when
/// given.
pub fn fold(family: Term, op: Term, identity: Option<Term>) -> Term {
    fold_at(family, 1, op, identity)
}

/// `fold(F, op, ev)` over an `F` of `depth` key levels, collapsing the innermost.
pub fn fold_at(family: Term, depth: usize, op: Term, identity: Option<Term>) -> Term {
    Term::Fold {
        family: rc(family),
        op: rc(op),
        identity: identity.map(rc),
        depth,
        ev: Evidence::new(),
    }
}

/// `discard(F, sel)`.
pub fn discard(family: Term, sel: Term) -> Term {
    Term::Discard {
        family: rc(family),
        sel: rc(sel),
    }
}

/// `fam(D, var -> body)`.
pub fn fam(domain: Term, var: &str, body: Term) -> Term {
    Term::Fam {
        domain: rc(domain),
        var: var.into(),
        body: rc(body),
    }
}

/// `true` unless `e` is `#notFound`: the membership test a lookup gives.
pub fn found(e: Term) -> Term {
    Term::Match(
        rc(e),
        vec![
            (Pattern::Atom("notFound".into(), vec![]), lit(false)),
            (Pattern::Wild, lit(true)),
        ],
    )
}

/// `group(f)` of (sec:kernel): each leaf `(k, v)` moves to keypath `(f(v), k)`.
pub fn group_by(family: Term, f: impl Fn(Term) -> Term) -> Term {
    let kf = lam(&["p", "v"], path(vec![f(var("v")), key(var("p"), 0)]));
    reindex(family, kf, lam(&["p", "v"], var("v")))
}

/// A document as `line -> position -> word`, the shape `split` gives.
pub fn lines_of(text: &[&[&str]]) -> Value {
    let mut leaves = Vec::new();
    for (i, line) in text.iter().enumerate() {
        for (j, w) in line.iter().enumerate() {
            leaves.push((vec![Value::Int(i as i64), Value::Int(j as i64)], s(w)));
        }
    }
    Value::Family(Family::from_leaves(leaves).unwrap())
}

// Derived forms. Each builder binds fresh names, so a term the caller passes in is never
// captured by a binder the builder adds.

static FRESH: AtomicUsize = AtomicUsize::new(0);

/// A variable name no other builder or caller uses: `stem` with a numeric suffix after `'`,
/// which a Zed identifier cannot contain.
pub fn fresh(stem: &str) -> String {
    format!("{stem}'{}", FRESH.fetch_add(1, Ordering::Relaxed))
}

/// A function of `N` fresh parameters, whose body `body` builds from the parameters.
pub fn func<const N: usize>(body: impl FnOnce([Term; N]) -> Term) -> Term {
    let names: [String; N] = std::array::from_fn(|i| fresh(&format!("x{i}")));
    let params: Vec<&str> = names.iter().map(String::as_str).collect();
    let vars = std::array::from_fn(|i| var(&names[i]));
    lam(&params, body(vars))
}

/// A binary primitive applied.
pub fn bin(p: Prim, a: Term, b: Term) -> Term {
    prim(p, vec![a, b])
}

/// `a - b`.
pub fn sub(a: Term, b: Term) -> Term {
    bin(Prim::Sub, a, b)
}

/// `a * b`.
pub fn mul(a: Term, b: Term) -> Term {
    bin(Prim::Mul, a, b)
}

/// `a div b`, Euclidean.
pub fn idiv(a: Term, b: Term) -> Term {
    bin(Prim::IntDiv, a, b)
}

/// `a mod b`, Euclidean.
pub fn modulo(a: Term, b: Term) -> Term {
    bin(Prim::Mod, a, b)
}

/// `a == b`.
pub fn eq(a: Term, b: Term) -> Term {
    bin(Prim::Eq, a, b)
}

/// `a < b`.
pub fn lt(a: Term, b: Term) -> Term {
    bin(Prim::Lt, a, b)
}

/// `a <= b`.
pub fn le(a: Term, b: Term) -> Term {
    bin(Prim::Le, a, b)
}

/// `a && b`, strict in both operands, as the kernel primitive is.
pub fn and(a: Term, b: Term) -> Term {
    bin(Prim::And, a, b)
}

/// `!a`.
pub fn not(a: Term) -> Term {
    prim(Prim::Not, vec![a])
}

/// A failure atom with no payload.
pub fn atom(name: &str) -> Term {
    lit(Value::atom(name))
}

/// `F.count`: the number of top-level entries.
pub fn count(f: Term) -> Term {
    prim(Prim::Count, vec![f])
}

/// `fam(D, i -> body(i))`.
pub fn fam_with(domain: Term, body: impl FnOnce(Term) -> Term) -> Term {
    let i = fresh("i");
    fam(domain, &i, body(var(&i)))
}

/// `discard(F, (p, e) -> sel(p, e))`.
pub fn discard_with(family: Term, sel: impl FnOnce(Term, Term) -> Term) -> Term {
    discard(family, func(|[p, e]| sel(p, e)))
}

/// `F.map(f)`: `reindex(F, (p, v) -> p, (p, v) -> f(v))`.
pub fn map(family: Term, f: impl FnOnce(Term) -> Term) -> Term {
    reindex(family, func(|[p, _]| p), func(|[_, v]| f(v)))
}

/// The keys of `F` as a set.
pub fn keyset(family: Term) -> Term {
    fam_with(family, |k| k)
}

/// `a ⊎ b` of the law catalog: the union of two families whose leaf keypaths, all of length
/// `depth`, are disjoint. Overlapping keypaths are a collision, unlike the kernel's `Union`,
/// which merges two equal leaves.
pub fn disjoint_union(a: Term, b: Term, depth: usize) -> Term {
    let tagged = fam_with(lit(Value::Family(Family::set([0i64, 1]))), |t| {
        if_(eq(t, lit(0)), a, b)
    });
    reindex(
        tagged,
        func(|[p, _]| path((1..=depth as i64).map(|i| key(p.clone(), i)).collect())),
        func(|[_, v]| v),
    )
}

/// The dense rank of `x` among the classes `f(v)` of `F`'s entries: how many distinct classes
/// `c` have `less(c, x)`. With `less` a strict total order this is the densified sort order.
pub fn rank_of(
    family: Term,
    f: &dyn Fn(Term) -> Term,
    less: &dyn Fn(Term, Term) -> Term,
    x: Term,
) -> Term {
    count(discard_with(group_by(family, f), |q, _| less(key(q, 0), x)))
}

/// `F.rank` by sort key `f`: the widen `k -> (rank(f(v)), k)` of (sec:order), keeping the
/// original key beneath the rank so that tied entries stay a group in key order.
pub fn rank_widen(
    family: Term,
    f: &dyn Fn(Term) -> Term,
    less: &dyn Fn(Term, Term) -> Term,
) -> Term {
    let kf = func(|[p, v]| path(vec![rank_of(family.clone(), f, less, f(v)), key(p, 0)]));
    reindex(family, kf, func(|[_, v]| v))
}

/// `F.scan(op)` as the prefix-fold family: entry `i` is the fold of the entries at keys
/// `<= i`.
pub fn scan(family: Term, op: Term) -> Term {
    fam_with(family.clone(), |i| {
        fold(discard_with(family, |p, _| le(key(p, 0), i)), op, None)
    })
}

/// A definedness `fix` over the keys of `domain`; `body(this, k)` is the entry at `k`.
pub fn fix_defined(domain: Term, body: impl FnOnce(Term, Term) -> Term) -> Term {
    let (this, k) = (fresh("this"), fresh("k"));
    Term::Fix {
        init: rc(domain),
        step: rc(body(var(&this), var(&k))),
        this: this.as_str().into(),
        key: k.as_str().into(),
        kind: FixKind::Definedness,
        ev: Evidence::new(),
    }
}

/// A lattice `fix` from `init`, iterating `x := join(x, step(x))`.
pub fn fix_lattice(init: Term, step: Term, join: Term) -> Term {
    Term::Fix {
        init: rc(init),
        step: rc(step),
        this: "".into(),
        key: "".into(),
        kind: FixKind::Lattice { join: rc(join) },
        ev: Evidence::new(),
    }
}

/// `xs.foldl(init, op)` over a sequence `0..n -> x`: `op(…op(op(init, x0), x1)…, x(n-1))`,
/// written as the definedness fix of its accumulators.
pub fn foldl(seq: Term, init: Term, op: Term) -> Term {
    let accs = fix_defined(seq.clone(), |this, i| {
        let prev = if_(
            eq(i.clone(), lit(0)),
            init.clone(),
            get(this, sub(i.clone(), lit(1))),
        );
        app(op, vec![prev, get(seq.clone(), i)])
    });
    let n = count(seq);
    if_(eq(n.clone(), lit(0)), init, get(accs, sub(n, lit(1))))
}

/// `xs.foldr(op, init)` over a sequence `0..n -> x`: `op(x0, op(x1, …op(x(n-1), init)…))`.
pub fn foldr(seq: Term, op: Term, init: Term) -> Term {
    let n = count(seq.clone());
    let accs = fix_defined(seq.clone(), |this, i| {
        let next = if_(
            eq(i.clone(), sub(n.clone(), lit(1))),
            init.clone(),
            get(this, add(i.clone(), lit(1))),
        );
        app(op, vec![get(seq, i), next])
    });
    if_(eq(n, lit(0)), init, get(accs, lit(0)))
}

/// `flip(op)`: `(x, y) -> op(y, x)`.
pub fn flip(op: Term) -> Term {
    func(|[x, y]| app(op, vec![y, x]))
}

/// `x.refine(p)`: `x` where `p(x)` is `true`, `#invalid` where it is `false`. A failure atom
/// in `x` flows out unchanged, as through every catalog operation (sec:failure), and a failure
/// `p` returns is the result.
pub fn refine(x: Term, p: Term) -> Term {
    let name = fresh("x");
    let x_ = var(&name);
    let_(
        &name,
        x,
        unless_atom(
            x_.clone(),
            if_(app(p, vec![x_.clone()]), x_, atom("invalid")),
        ),
    )
}

/// `v` itself when it is an atom, `then` otherwise: how a helper passes a failure through.
pub fn unless_atom(v: Term, then: Term) -> Term {
    Term::Match(
        Arc::new(v.clone()),
        vec![(Pattern::AnyAtom, v), (Pattern::Wild, then)],
    )
}
