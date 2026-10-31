/// Builders for kernel terms and values, shared by the step tests that construct the terms a
/// program elaborates to (M0.9, M0.10).
library;

import 'package:zed/kernel.dart';

/// A string value.
Value s(String x) => Str(x);

/// The error `term` stops with; fails when it has a value.
KernelError evalError(Term term, [Evaluator? evaluator]) {
  try {
    final v = (evaluator ?? Evaluator(World())).run(term);
    throw StateError('expected an error, got $v');
  } on KernelError catch (e) {
    return e;
  }
}

/// `f[k]`: the entry of family `f` at top-level key `k`.
Term get(Term f, Term k) => prim(Prim.get, [f, k]);

/// A keypath built from its keys.
Term path(List<Term> keys) => prim(Prim.path, keys);

/// The `i`th key of keypath `p`.
Term key(Term p, int i) => prim(Prim.pathKey, [p, lit(i)]);

/// The `i`th component of tuple `t`.
Term nth(Term t, int i) => prim(Prim.tupleGet, [t, lit(i)]);

/// `a + b`.
Term add(Term a, Term b) => prim(Prim.add, [a, b]);

/// `reindex(F, kf, vf)` with a residue witness.
Term reindex(Term family, Term kf, Term vf) => Reindex(family, kf, vf, const Residue());

/// `fold(F, op, ev)` over a one-level `F`, with `identity` as the empty-level result when
/// given.
Term fold(Term family, Term op, [Term? identity]) => foldAt(family, 1, op, identity);

/// `fold(F, op, ev)` over an `F` of `depth` key levels, collapsing the innermost.
Term foldAt(Term family, int depth, Term op, [Term? identity]) =>
    Fold(family, op, identity, depth, const {});

/// `discard(F, sel)`.
Term discard(Term family, Term sel) => Discard(family, sel);

/// `fam(D, variable -> body)`.
Term fam(Term domain, String variable, Term body) => Fam(domain, variable, body);

/// `true` unless `e` is `#notFound`: the membership test a lookup gives.
Term found(Term e) => Match(e, [(const AtomP('notFound'), lit(false)), (const WildP(), lit(true))]);

/// `group(f)` of (sec:kernel): each leaf `(k, v)` moves to keypath `(f(v), k)`.
Term groupBy(Term family, Term Function(Term) f) {
  final kf = lam(['p', 'v'], path([f(var_('v')), key(var_('p'), 0)]));
  return reindex(family, kf, lam(['p', 'v'], var_('v')));
}

/// A document as `line -> position -> word`, the shape `split` gives.
Value linesOf(List<List<String>> text) => Family.fromLeaves([
  for (var i = 0; i < text.length; i++)
    for (var j = 0; j < text[i].length; j++) ([Int(i), Int(j)], s(text[i][j])),
]);

// Derived forms. Each builder binds fresh names, so a term the caller passes in is never
// captured by a binder the builder adds.

var _fresh = 0;

/// A variable name no other builder or caller uses: `stem` with a numeric suffix after `'`,
/// which a Zed identifier cannot contain.
String fresh(String stem) => "$stem'${_fresh++}";

/// A function of `n` fresh parameters, whose body `body` builds from the parameters.
Term func(int n, Term Function(List<Term> xs) body) {
  final names = [for (var i = 0; i < n; i++) fresh('x$i')];
  return lam(names, body([for (final x in names) var_(x)]));
}

/// A binary primitive applied.
Term bin(Prim p, Term a, Term b) => prim(p, [a, b]);

/// `a - b`.
Term sub(Term a, Term b) => bin(Prim.sub, a, b);

/// `a * b`.
Term mul(Term a, Term b) => bin(Prim.mul, a, b);

/// `a div b`, Euclidean.
Term idiv(Term a, Term b) => bin(Prim.intDiv, a, b);

/// `a mod b`, Euclidean.
Term modulo(Term a, Term b) => bin(Prim.mod, a, b);

/// `a == b`.
Term eq(Term a, Term b) => bin(Prim.eq, a, b);

/// `a < b`.
Term lt(Term a, Term b) => bin(Prim.lt, a, b);

/// `a <= b`.
Term le(Term a, Term b) => bin(Prim.le, a, b);

/// `a && b`, strict in both operands, as the kernel primitive is.
Term and(Term a, Term b) => bin(Prim.and, a, b);

/// `!a`.
Term not(Term a) => prim(Prim.not, [a]);

/// A failure atom with no payload.
Term atom(String name) => lit(Atom(name));

/// `F.count`: the number of top-level entries.
Term count(Term f) => prim(Prim.count, [f]);

/// `fam(D, i -> body(i))`.
Term famWith(Term domain, Term Function(Term) body) {
  final i = fresh('i');
  return fam(domain, i, body(var_(i)));
}

/// `discard(F, (p, e) -> sel(p, e))`.
Term discardWith(Term family, Term Function(Term p, Term e) sel) =>
    discard(family, func(2, (x) => sel(x[0], x[1])));

/// `F.map(f)`: `reindex(F, (p, v) -> p, (p, v) -> f(v))`.
Term map(Term family, Term Function(Term) f) =>
    reindex(family, func(2, (x) => x[0]), func(2, (x) => f(x[1])));

/// The keys of `F` as a set.
Term keyset(Term family) => famWith(family, (k) => k);

/// `a ⊎ b` of the law catalog: the union of two families whose leaf keypaths, all of length
/// `depth`, are disjoint. Overlapping keypaths are a collision, unlike the kernel's `Union`,
/// which merges two equal leaves.
Term disjointUnion(Term a, Term b, int depth) {
  final tagged = famWith(lit(Family.set([const Int(0), const Int(1)])), (t) {
    return if_(eq(t, lit(0)), a, b);
  });
  return reindex(
    tagged,
    func(2, (x) => path([for (var i = 1; i <= depth; i++) key(x[0], i)])),
    func(2, (x) => x[1]),
  );
}

/// The dense rank of `x` among the classes `f(v)` of `F`'s entries: how many distinct classes
/// `c` have `less(c, x)`. With `less` a strict total order this is the densified sort order.
Term rankOf(Term family, Term Function(Term) f, Term Function(Term, Term) less, Term x) =>
    count(discardWith(groupBy(family, f), (q, _) => less(key(q, 0), x)));

/// `F.rank` by sort key `f`: the widen `k -> (rank(f(v)), k)` of (sec:order), keeping the
/// original key beneath the rank so that tied entries stay a group in key order.
Term rankWiden(Term family, Term Function(Term) f, Term Function(Term, Term) less) {
  final kf = func(2, (x) => path([rankOf(family, f, less, f(x[1])), key(x[0], 0)]));
  return reindex(family, kf, func(2, (x) => x[1]));
}

/// `F.scan(op)` as the prefix-fold family: entry `i` is the fold of the entries at keys
/// `<= i`.
Term scan(Term family, Term op) =>
    famWith(family, (i) => fold(discardWith(family, (p, _) => le(key(p, 0), i)), op));

/// A definedness `fix` over the keys of `domain`; `body(self, k)` is the entry at `k`.
Term fixDefined(Term domain, Term Function(Term self, Term k) body) {
  final self = fresh('this'), k = fresh('k');
  return Fix(domain, body(var_(self), var_(k)), self, k, const Definedness(), const {});
}

/// A lattice `fix` from `init`, iterating `x := join(x, step(x))`.
Term fixLattice(Term init, Term step, Term join) =>
    Fix(init, step, '', '', Lattice(join), const {});

/// `xs.foldl(init, op)` over a sequence `0..n -> x`: `op(…op(op(init, x0), x1)…, x(n-1))`,
/// written as the definedness fix of its accumulators.
Term foldl(Term seq, Term init, Term op) {
  final accs = fixDefined(seq, (self, i) {
    final prev = if_(eq(i, lit(0)), init, get(self, sub(i, lit(1))));
    return app(op, [prev, get(seq, i)]);
  });
  final n = count(seq);
  return if_(eq(n, lit(0)), init, get(accs, sub(n, lit(1))));
}

/// `xs.foldr(op, init)` over a sequence `0..n -> x`: `op(x0, op(x1, …op(x(n-1), init)…))`.
Term foldr(Term seq, Term op, Term init) {
  final n = count(seq);
  final accs = fixDefined(seq, (self, i) {
    final next = if_(eq(i, sub(n, lit(1))), init, get(self, add(i, lit(1))));
    return app(op, [get(seq, i), next]);
  });
  return if_(eq(n, lit(0)), init, get(accs, lit(0)));
}

/// `flip(op)`: `(x, y) -> op(y, x)`.
Term flip(Term op) => func(2, (x) => app(op, [x[1], x[0]]));

/// `x.refine(p)`: `x` where `p(x)` is `true`, `#invalid` where it is `false`. A failure atom
/// in `x` flows out unchanged, as through every catalog operation (sec:failure), and a failure
/// `p` returns is the result.
Term refine(Term x, Term p) {
  final name = fresh('x');
  final v = var_(name);
  return let_(name, x, unlessAtom(v, if_(app(p, [v]), v, atom('invalid'))));
}

/// `v` itself when it is an atom, `then` otherwise: how a helper passes a failure through.
Term unlessAtom(Term v, Term then) => Match(v, [(const AnyAtomP(), v), (const WildP(), then)]);
