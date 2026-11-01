/// Step L1.23: semantic subtyping. `a <: b` iff `a & !b` is empty, decided by a memoized
/// coinductive check; recursive definitions are checked for contractivity, regularity and
/// monotonicity in emptiness when they are defined.
///
/// The spec's subtyping examples, and identities of the algebra that the representation does
/// not make structural, decided as type equality: subtyping both ways.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

Type lit(Value v) => Type.lit(v)!;

Type ints(List<int> ns) => ns.fold(Type.empty, (t, n) => t | lit(Int(n)));

Type strs(List<String> ss) => ss.fold(Type.empty, (t, s) => t | lit(Str(s)));

void main() {
  test('morphism variance', () {
    final (int, string) = (Type.integer, Type.string);
    // sec:type_language: `{"a","b"} -> int <: String ->? int`.
    final ab = Type.exact(strs(['a', 'b']), int);
    expect(ab.subtype(Type.partial(string, int)), isTrue);
    // A wider exact domain is not a subtype of a narrower one, nor the reverse.
    final small = ints([0, 1, 2]);
    final whole = Type.exact(int, int);
    final part = Type.exact(small, int);
    expect(whole.subtype(part), isFalse);
    expect(part.subtype(whole), isFalse);
    // Both are partial maps over `int`; a partial map is neither.
    final partial = Type.partial(int, int);
    expect(whole.subtype(partial) && part.subtype(partial), isTrue);
    expect(partial.subtype(whole), isFalse);
    // Covariant in the value type.
    final toSmall = Type.exact(int, small);
    expect(toSmall.subtype(whole) && !whole.subtype(toSmall), isTrue);
    // An empty guarantee in the supertype places no requirement.
    final g = Type.morphism(small, int, int);
    expect(g.subtype(partial) && !partial.subtype(g), isTrue);
    // A guarantee wider than the permission admits no morphism.
    expect(Type.morphism(int, small, int).isEmpty, isTrue);
    // A key promised with no value to give it admits none; with no key promised, the empty
    // morphism remains, and it is in every partial map type.
    expect(Type.exact(small, Type.empty).isEmpty, isTrue);
    final none = Type.partial(int, Type.empty);
    expect(none.isEmpty, isFalse);
    expect(none.subtype(Type.partial(string, string)), isTrue);
    expect(none.subtype(Type.exact(string, string)), isFalse);
    // Every morphism type is in the morphism universe.
    expect(whole.subtype(Type.universe(Universe.morphism)), isTrue);
    expect(Type.universe(Universe.morphism).subtype(whole), isFalse);
  });

  test('flow narrowing is set arithmetic', () {
    // sec:type_language: the false branch of `v is T` is at `old \ T`.
    final old = Type.integer | Type.string | Type.atom('none');
    expect((old - Type.integer).equiv(Type.string | Type.atom('none')), isTrue);
    expect((old & Type.integer).equiv(Type.integer), isTrue);
    // Narrowing by a type outside `old` leaves it, and no value is in both.
    expect((old - Type.boolean).equiv(old), isTrue);
    expect((old & Type.boolean).isEmpty, isTrue);
  });

  test('tuple identities', () {
    final (a, b, c, d) = (
      Type.integer,
      Type.string | ints([0]),
      ints([0, 1]),
      Type.atom('a') | Type.string,
    );
    const t = Type.tuple;
    // Distributivity: a union in a component is a union of tuples.
    final joined = t([a | b, c]);
    final split = t([a, c]) | t([b, c]);
    expect(joined, isNot(split), reason: 'the two forms are not one representation');
    expect(joined.equiv(split), isTrue);
    // Tuples meet componentwise.
    final met = t([a, b]) & t([c, d]);
    expect(met.equiv(t([a & c, b & d])), isTrue);
    // The complement of a pair, among pairs, is a pair with some component outside.
    final pairs = t([Type.top, Type.top]);
    final outside = t([~a, Type.top]) | t([Type.top, ~b]);
    expect((pairs - t([a, b])).equiv(outside), isTrue);
    // A pair is covered by two pairs that split it in one component, not by two that split it
    // in different components.
    final square = t([c, c]);
    final rows =
        t([
          ints([0]),
          c,
        ]) |
        t([
          ints([1]),
          c,
        ]);
    expect(square.subtype(rows), isTrue);
    final corners =
        t([
          ints([0]),
          ints([0]),
        ]) |
        t([
          ints([1]),
          ints([1]),
        ]);
    expect(square.subtype(corners), isFalse);
    // A tuple with an empty component is empty, and tuples of two lengths are disjoint.
    expect(t([a, a & Type.string]).isEmpty, isTrue);
    expect((t([a]) & t([a, a])).isEmpty, isTrue);
  });

  test('boolean identities', () {
    final (a, b, c) = (
      Type.integer | Type.tuple([Type.string]),
      ints([0]) | Type.tuple([Type.top]) | Type.atom('x'),
      Type.tuple([Type.integer]) | Type.boolean,
    );
    // De Morgan, distributivity, absorption and the difference as a meet.
    expect((~(a | b)).equiv(~a & ~b), isTrue);
    expect((~(a & b)).equiv(~a | ~b), isTrue);
    expect((a & (b | c)).equiv((a & b) | (a & c)), isTrue);
    expect((a | (b & c)).equiv((a | b) & (a | c)), isTrue);
    expect((a | (a & b)).equiv(a), isTrue);
    expect((a - b).equiv(a & ~b), isTrue);
    // Order: the meet is below each side, the join above, and `_` and the empty type are the
    // ends.
    expect((a & b).subtype(a) && a.subtype(a | b), isTrue);
    expect(Type.empty.subtype(a) && a.subtype(Type.top), isTrue);
    expect(!Type.top.subtype(a) && !a.isEmpty, isTrue);
    expect((a & ~a).isEmpty, isTrue);
  });

  test('atom payloads', () {
    const t = Type.tuple;
    final p = Type.atomWith('p', t([Type.integer]));
    final q = Type.atomWith(
      'p',
      t([
        ints([0]),
      ]),
    );
    expect(q.subtype(p) && !p.subtype(q), isTrue);
    // An atom whose payload type is empty has no value, but its bare atom remains.
    expect(Type.atomWith('p', t([Type.empty])).isEmpty, isTrue);
    expect((Type.atom('p') | Type.atomWith('p', Type.empty)).isEmpty, isFalse);
    // Payloads of one name split as tuples do.
    final split =
        Type.atomWith(
          'p',
          t([
            ints([0]),
          ]),
        ) |
        Type.atomWith(
          'p',
          t([
            Type.integer - ints([0]),
          ]),
        );
    expect(split.equiv(p), isTrue);
  });
}
