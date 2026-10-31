/// Step L1.22: the printed forms of types: the universes, the scalar part's finite and
/// cofinite sets, tuple clauses, atoms and morphism bounds.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

Type lit(Value v) => Type.lit(v)!;

void main() {
  test('the extremes and the base types', () {
    expect('${Type.top}', '_');
    expect('${Type.empty}', '(|)');
    expect('${Type.integer | Type.string}', '(| int String)');
    expect('${Type.integer & Type.string}', '(|)');
    final three = lit(const Int(3));
    expect('${Type.integer - three}', r'(\ int 3)');
    expect('${three | lit(const Int(1))}', '(| 1 3)');
    expect('${Type.integer - (Type.integer - three)}', '3');
    expect('${lit(const Bool(true))}', 'true');
    expect('${Type.boolean - lit(const Bool(true))}', 'false');
  });

  test('complement is taken within each universe', () {
    // `!int` keeps every other scalar and every tuple, struct and morphism.
    expect('${~Type.integer}', '(| bool rat f64 String #_ tuple struct morphism)');
    final notInt = ~Type.integer;
    expect(notInt.contains(const Tuple([Int(1)])), isTrue);
    expect(notInt.contains(Str('1')), isTrue);
    expect(notInt.functions, isTrue);
    expect(notInt.contains(const Int(1)), isFalse);
    for (final u in Universe.values) {
      expect(Type.universe(u).part(u), Type.universe(u));
    }
    expect(Type.unionAll(Universe.values.map(Type.universe)), Type.top);
  });

  test('atoms are scalars named one by one', () {
    final (a, b) = (Type.atom('a'), Type.atom('b'));
    expect('${a | b}', '(| #a #b)');
    final atoms =
        Type.universe(Universe.scalar) -
        (Type.boolean | Type.integer | Type.rational | Type.f64 | Type.string);
    expect('$atoms', '#_');
    expect('${atoms - a}', r'(\ #_ #a)');
    final pair = Type.tuple([Type.integer, Type.string]);
    final with_ = Type.atomWith('ioError', pair);
    expect('$with_', '(#ioError (tuple int String))');
    expect(with_.contains(Atom('ioError', [const Int(2), Str('disk')])), isTrue);
    expect(with_.contains(const Atom('ioError')), isFalse);
    // A payload is a tuple or a struct: a scalar payload type contributes nothing.
    expect(Type.atomWith('a', Type.integer), Type.empty);
  });

  test('tuples meet componentwise and lengths are disjoint', () {
    Type p(Type a, Type b) => Type.tuple([a, b]);
    final num = Type.integer | Type.f64;
    // Tuple types of one length are not met when built: the meet is equal to the
    // componentwise one as a set, and disjoint components make it empty.
    final meet = p(num, Type.top) & p(Type.integer, Type.string);
    expect(meet.equiv(p(Type.integer, Type.string)), isTrue, reason: '$meet');
    expect(meet.equiv(p(num, Type.string)), isFalse, reason: '$meet');
    expect((p(Type.integer, Type.string) & p(Type.string, Type.top)).isEmpty, isTrue);
    // Two lengths are disjoint as built.
    expect(p(Type.integer, Type.top) & Type.tuple([Type.top]), Type.empty);
    expect('${Type.tuple([])}', '(tuple)');
    expect(
      '${Type.universe(Universe.tuple) - p(Type.integer, Type.integer)}',
      '(& tuple (! (tuple int int)))',
    );
    // `(X & t) | (X & !t)` is `X`.
    final t = p(Type.integer, Type.integer);
    final x = Type.tuple([Type.boolean]);
    final tuples = Type.universe(Universe.tuple);
    expect((x - t) | (x & t), Type.tuple([Type.boolean]));
    expect((tuples - t) | t, tuples);
    // Two clauses merge only when the rest of them is equal: `(t & !u) | !t` is `!u` only
    // because `u` is within `t`, and `t | (u & !t)` is `t | u`.
    Value tup(Value v) => Tuple([v]);
    final one = Type.tuple([lit(const Int(1))]);
    final (t1, u) = (Type.tuple([Type.integer]), Type.tuple([Type.string]));
    for (final y in [(t1 - one) | (tuples - t1), (tuples - t1) | (t1 - one)]) {
      expect(y.contains(tup(const Int(1))), isFalse, reason: '$y');
      expect(y.contains(tup(const Int(2))) && y.contains(tup(Str('a'))), isTrue);
    }
    // Both orders of the two clauses, which reach the two cases of the merge.
    for (final y in [t1 | (u - t1), u | (t1 - u)]) {
      expect(y.contains(tup(const Int(1))) && y.contains(tup(Str('a'))), isTrue);
      expect(y.contains(tup(const Bool(true))), isFalse, reason: '$y');
    }
  });

  test('morphism types carry two domain bounds', () {
    final (k, v) = (Type.integer, Type.string);
    expect('${Type.exact(k, v)}', '(-> int String)');
    expect('${Type.partial(k, v)}', '(->? int String)');
    final ab = Type.atom('a') | Type.atom('b');
    expect('${Type.morphism(Type.atom('a'), ab, v)}', '(-> #a (| #a #b) String)');
    // A run-time test can decide membership in every morphism or none, and in nothing
    // between.
    final f = Type.exact(k, v);
    expect(f.decidable, isFalse);
    expect((Type.integer | f).decidable, isFalse);
    expect(Type.tuple([f]).decidable, isFalse);
    expect((f | ~f).decidable && (f | ~f).functions, isTrue);
    expect((f & ~f).decidable && !(f & ~f).functions, isTrue);
    expect(Type.universe(Universe.morphism).functions, isTrue);
  });
}
