/// Step L1.23: recursive definitions: the plan's four (`Tree` and `W` accepted, `Nest` and `T`
/// rejected at the definition), the other ways a definition is rejected, and emptiness and
/// subtyping of recursive types, where the check is coinductive. The four definitions are
/// written here as kernel definition groups: `type` declarations, which elaborate to them,
/// join at L2.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/src/kernel/rec.dart' as rec;

import '../../support/scaling.dart';

rec.Def def(String name, List<String> params, rec.Expr body) => rec.Def(name, params, body);

rec.Expr r(int i, [List<rec.Expr> args = const []]) => rec.Ref(i, args);

rec.Expr ty(Type t) => rec.Given(t);

rec.Expr atom(String name, List<rec.Expr> items) => rec.Atom(name, items);

rec.Expr bare(String name) => ty(Type.atom(name));

rec.Expr or(List<rec.Expr> xs) => rec.Union(xs);

rec.Expr p() => rec.Param(0);

/// The one type of a group with no parameters.
Type one(List<rec.Def> defs) => rec.Group(defs).instance([])[0];

rec.Rejection rejection(List<rec.Def> defs) {
  try {
    rec.Group(defs);
  } on rec.Rejection catch (e) {
    return e;
  }
  throw StateError('the group was accepted');
}

String rejected(List<rec.Def> defs) => rejection(defs).message;

/// `type Tree(A) = #leaf(A) | #fork(Tree(A), Tree(A))`.
rec.Group tree() {
  rec.Expr t() => r(0, [p()]);
  return rec.Group([
    def(
      'Tree',
      ['A'],
      or([
        atom('leaf', [p()]),
        atom('fork', [t(), t()]),
      ]),
    ),
  ]);
}

Value leaf(Value v) => Atom('leaf', [v]);

Value fork(Value l, Value r) => Atom('fork', [l, r]);

/// `type L = #nil | #cons(A, L)` at `a`.
Type list(Type a) => one([
  def(
    'L',
    [],
    or([
      bare('nil'),
      atom('cons', [ty(a), r(0)]),
    ]),
  ),
]);

void main() {
  test("the plan's definitions", () {
    // `Tree` is guarded by its atoms and passes `A` unchanged.
    final t = tree().instance([Type.integer])[0];
    expect('$t', 'Tree(int)');
    final v = fork(leaf(const Int(1)), fork(leaf(const Int(2)), leaf(const Int(3))));
    expect(t.contains(v), isTrue);
    expect(t.contains(fork(leaf(const Int(1)), leaf(Str('x')))), isFalse);
    expect(t.isEmpty, isFalse);
    // `type W = (W) -> int`: the recursive occurrence is in a guarantee, but the value type
    // is not empty and does not mention `W`.
    expect(one([def('W', [], rec.Expr.exact(r(0), ty(Type.integer)))]).isEmpty, isFalse);
    // `type Nest(A) = #leaf(A) | #node(Nest((A, A)))` changes its parameter.
    final pair = rec.Tuple([p(), p()]);
    final nest = def(
      'Nest',
      ['A'],
      or([
        atom('leaf', [p()]),
        atom('node', [
          r(0, [pair]),
        ]),
      ]),
    );
    expect(
      rejected([nest]),
      'the type `Nest` is not regular: its recursive occurrence `Nest((A, A))` changes the '
      'parameters, so the type has no end of components',
    );
    // `type T = (T) -> (#a & #b)` would be inhabited exactly when it is empty.
    final tt = rec.Expr.exact(r(0), rec.And([bare('a'), bare('b')]));
    expect(
      rejected([def('T', [], tt)]),
      'the type `T` is not monotone in emptiness: a recursive occurrence stands in the '
      'guaranteed domain of a morphism type whose value type may be empty or mentions the '
      'group',
    );
  });

  test('other rejections', () {
    rec.Expr n() => r(0);
    // Not contractive: alone, and through a second definition.
    expect(
      rejected([
        def('N', [], or([n(), ty(Type.integer)])),
      ]),
      contains('not contractive'),
    );
    final mutual = [
      def('A', [], r(1)),
      def('B', [], or([r(0), ty(Type.integer)])),
    ];
    expect(rejected(mutual), contains('`A` is not contractive'));
    // Under a complement, to the right of `\`, and in a guarantee whose value is the group.
    final underNot = atom('a', [rec.Not(n())]);
    expect(rejected([def('N', [], underNot)]), contains('under a complement'));
    final diff = rec.Diff(ty(Type.integer), atom('b', [n()]));
    expect(rejected([def('N', [], diff)]), contains('to the right of `\\`'));
    expect(rejected([def('U', [], rec.Expr.exact(n(), n()))]), contains('guaranteed domain'));
    // A value type that a parameter can make empty: `type F(A) = (F(A)) -> A`, and one that a
    // larger argument shrinks, `(H(A)) -> (int \ A)`.
    rec.Expr self() => r(0, [p()]);
    expect(
      rejected([
        def('F', ['A'], rec.Expr.exact(self(), p())),
      ]),
      contains('guaranteed'),
    );
    final shrinking = rec.Diff(ty(Type.integer), p());
    expect(
      rejected([
        def('H', ['A'], rec.Expr.exact(self(), shrinking)),
      ]),
      contains('guaranteed'),
    );
    // Parameters that differ across a group.
    final uneven = [
      def(
        'A',
        ['X'],
        atom('a', [
          r(1, [p()]),
        ]),
      ),
      def('B', [], atom('b', [r(0)])),
    ];
    expect(rejected(uneven), contains('takes other parameters'));
  });

  test('accepted neighbors of the rejections', () {
    // `(G(A)) -> (A | int)` is never empty, and a guarantee with a nonrecursive value is
    // admitted however deep the occurrence.
    final g = rec.Expr.exact(r(0, [p()]), or([p(), ty(Type.integer)]));
    rec.Group([
      def('G', ['A'], g),
    ]);
    // A recursive occurrence in a permission only, under no complement.
    rec.Group([def('P', [], rec.Morphism(ty(Type.empty), r(0), r(0)))]);
    // One definition naming another bare, the other guarded: the cycle has a constructor.
    final ab = rec.Group([
      def('A', [], r(1)),
      def(
        'B',
        [],
        or([
          atom('b', [r(0)]),
          ty(Type.integer),
        ]),
      ),
    ]).instance([]);
    expect(ab[0].equiv(ab[1]), isTrue);
    expect(ab[0].contains(const Atom('b', [Int(1)])), isTrue);
  });

  test('emptiness is coinductive', () {
    // Values are finite, so a type each of whose values holds a smaller one is empty.
    expect(
      one([
        def('E', [], atom('e', [r(0)])),
      ]).isEmpty,
      isTrue,
    );
    final stream = one([
      def('S', [], rec.Tuple([ty(Type.integer), r(0)])),
    ]);
    expect(stream.isEmpty, isTrue);
    // A tree with no leaf type has no leaf, so no tree.
    expect(tree().instance([Type.empty])[0].isEmpty, isTrue);
    expect(tree().instance([Type.atom('x')])[0].isEmpty, isFalse);
    // A meet in a component is kept unevaluated while the body is built:
    // `type M = #z | #a(M & (#z | #a(_)))` holds `#a(#z)`, and without `#z` it is empty.
    rec.Expr shaped() => rec.And([
      r(0),
      or([
        bare('z'),
        atom('a', [ty(Type.top)]),
      ]),
    ]);
    final m = one([
      def(
        'M',
        [],
        or([
          bare('z'),
          atom('a', [shaped()]),
        ]),
      ),
    ]);
    final az = const Atom('a', [Atom('z')]);
    expect(m.contains(az) && !m.isEmpty, isTrue);
    expect(m.contains(const Atom('a', [Int(1)])), isFalse);
    expect(
      one([
        def('M', [], atom('a', [shaped()])),
      ]).isEmpty,
      isTrue,
    );
  });

  test('recursive subtyping', () {
    final ints = list(Type.integer);
    final wider = list(Type.integer | Type.string);
    expect(ints.subtype(wider) && !wider.subtype(ints), isTrue);
    // Two definitions of one set are one type.
    expect(ints.equiv(list(Type.integer)), isTrue);
    // Even and odd lengths together are every list, and neither alone is.
    final even = one([
      def(
        'Even',
        [],
        or([
          bare('nil'),
          atom('cons', [
            ty(Type.integer),
            atom('cons', [ty(Type.integer), r(0)]),
          ]),
        ]),
      ),
    ]);
    final odd = Type.atomWith('cons', Type.tuple([Type.integer, even]));
    expect((even | odd).equiv(ints), isTrue);
    expect(even.subtype(ints) && !ints.subtype(even), isTrue);
    expect((even & odd).isEmpty, isTrue);
    // `W` is one type however it is written; `(W) -> int` is not `(W) -> String`.
    Type w(Type v) => one([def('W', [], rec.Expr.exact(r(0), ty(v)))]);
    expect(w(Type.integer).equiv(w(Type.integer)), isTrue);
    expect(w(Type.integer).subtype(w(Type.string)), isFalse);
    // A tree of a subtype is a subtype of the tree.
    final small = tree().instance([Type.lit(const Int(0))!])[0];
    final big = tree().instance([Type.integer])[0];
    expect(small.subtype(big) && !big.subtype(small), isTrue);
  });

  test('a result resting on a false assumption is dropped', () {
    // Deciding the list assumes it empty, which makes its `#cons` payload empty for a moment;
    // the list then has `#nil`, so that answer must not be kept.
    final l = list(Type.integer);
    expect(l.isEmpty, isFalse);
    expect(Type.tuple([Type.integer, l]).isEmpty, isFalse);
    expect(Type.atomWith('cons', Type.tuple([Type.integer, l])).isEmpty, isFalse);
  });

  test('recursive types are decidable unless they bound functions', () {
    expect(tree().instance([Type.integer])[0].decidable, isTrue);
    final f = Type.exact(Type.integer, Type.integer);
    expect(tree().instance([f])[0].decidable, isFalse);
    expect(one([def('W', [], rec.Expr.exact(r(0), ty(Type.integer)))]).decidable, isFalse);
  });

  test('recursive definitions scale', () {
    // The check for contractiveness searches the definitions' graph once, by Tarjan's
    // components, rather than from each definition in turn, which took `O(d²)` steps for a
    // chain of `d` definitions. A body nested `d` deep shares its parts kept unevaluated,
    // which know whether they mention the group, names a part only when it is printed, and
    // tests an atom's payload in place, rather than copying, walking or naming each part
    // once per level, `O(d²)`. Unfolding the chain recurses once per definition, so the
    // checks at definition are also timed on their own, on a longer chain, where a search
    // from each definition would outweigh the rest.
    List<rec.Def> chain(int d) => [
      for (var i = 0; i < d; i++)
        def('T$i', [], i + 1 < d ? or([r(i + 1), bare('a$i')]) : bare('end')),
    ];
    check('chain of definitions', 100, (d) {
      expect(one(chain(d)).contains(const Atom('end')), isTrue);
    });
    check('checking a chain of definitions', 1000, (d) => rec.Group(chain(d)));
    check('nested body', 100, (d) {
      rec.Expr body = rec.Tuple([r(0), ty(Type.integer)]);
      for (var i = 0; i < d; i++) {
        body = atom('n', [body]);
      }
      final t = one([
        def('T', [], or([body, bare('z')])),
      ]);
      Value v = const Tuple([Atom('z'), Int(1)]);
      for (var i = 0; i < d; i++) {
        v = Atom('n', [v]);
      }
      expect(t.contains(v), isTrue);
    });
  });

  test('the lowest definition on a cycle is named', () {
    // `A = B | int` reaches the cycle `B = C | int`, `C = B | #c` but is not on it.
    rec.Expr b() => r(1);
    rec.Expr c() => r(2);
    var e = rejection([
      def('A', [], or([b(), ty(Type.integer)])),
      def('B', [], or([c(), ty(Type.integer)])),
      def('C', [], or([b(), bare('c')])),
    ]);
    expect(e.def, 1, reason: e.message);
    expect(e.message, contains('`B` is not contractive'));
    // Two cycles: `{B, C}` is completed first, and `A`, the lowest, is named.
    e = rejection([
      def('A', [], or([b(), r(0)])),
      def('B', [], or([c(), ty(Type.integer)])),
      def('C', [], or([b(), bare('c')])),
    ]);
    expect(e.def, 0);
    // A definition naming itself is a cycle of one, and a guarded cycle is none.
    e = rejection([
      def('A', [], atom('a', [r(1)])),
      def('B', [], or([r(1), bare('b')])),
    ]);
    expect(e.def, 1);
    rec.Group([
      def('A', [], atom('a', [r(1)])),
      def('B', [], or([r(0), bare('b')])),
    ]);
  });

  test('products of recursive types', () {
    // Deciding these meets one type per state of the product of the definitions, or per set
    // of states of a definition whose alternatives overlap: 30 states for 2, 3 and 5, about
    // 1000 types for the third item from the end. Both grow exponentially with the
    // definitions and the item, as emptiness of regular tree types can (DESIGN.md L1.23).
    final six = multiple(2) & multiple(3) & multiple(5);
    expect(six.subtype(multiple(30)) && multiple(30).subtype(six), isTrue);
    expect((multiple(2) & multiple(3)).subtype(multiple(12)), isFalse);
    expect(multiple(4).subtype(multiple(6)), isFalse);
    for (var n = 1; n <= 3; n++) {
      expect(nthFromEnd(n).subtype(nthFromEnd(n)), isTrue, reason: 'n = $n');
      if (n < 3) expect(nthFromEnd(n).equiv(nthFromEnd(n + 1)), isFalse, reason: 'n = $n');
    }
  });
}

/// Lists of int whose length is a multiple of `p`.
Type multiple(int p) {
  var body = r(0);
  for (var i = 0; i < p; i++) {
    body = atom('cons', [ty(Type.integer), body]);
  }
  return one([
    def('M', [], or([bare('nil'), body])),
  ]);
}

/// Lists of int whose `n`-th item from the end is `1`, guessed where it is.
Type nthFromEnd(int n) => rec.Group([
  def('R0', [], bare('nil')),
  for (var k = 1; k < n; k++) def('R$k', [], atom('cons', [ty(Type.integer), r(k - 1)])),
  def(
    'G',
    [],
    or([
      atom('cons', [ty(Type.integer), r(n)]),
      atom('cons', [ty(Type.lit(const Int(1))!), r(n - 1)]),
    ]),
  ),
]).instance([]).last;
