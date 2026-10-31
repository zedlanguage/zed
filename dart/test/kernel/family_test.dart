import 'package:test/test.dart';
import 'package:zed/kernel.dart';

Keypath kp(List<String> keys) => [for (final k in keys) Str(k)];

Object attempt(Family Function() build) {
  try {
    return build();
  } on KernelError catch (e) {
    return e;
  }
}

void main() {
  test('leaves round-trip in keypath order', () {
    final f = Family.fromLeaves([
      (kp(['b', 'x']), const Int(2)),
      (kp(['a']), const Int(1)),
      (kp(['b', 'y']), const Int(3)),
    ]);
    expect(f.toString(), '{"a" -> 1, "b" -> {"x" -> 2, "y" -> 3}}');
    expect(
      [for (final (p, v) in f.leaves()) (Path(p), v)],
      [
        (Path(kp(['a'])), const Int(1)),
        (Path(kp(['b', 'x'])), const Int(2)),
        (Path(kp(['b', 'y'])), const Int(3)),
      ],
    );
  });

  test('two writers for one keypath collide', () {
    final err = attempt(
      () => Family.fromLeaves([
        (kp(['a']), const Int(1)),
        (kp(['a']), const Int(1)),
      ]),
    );
    expect(err, CollisionError(kp(['a'])));
  });

  test('a leaf above a subtree collides in either order', () {
    final leafFirst = attempt(
      () => Family.fromLeaves([
        (kp(['a']), const Int(1)),
        (kp(['a', 'b']), const Int(2)),
      ]),
    );
    expect(leafFirst, CollisionError(kp(['a', 'b'])));
    final subtreeFirst = attempt(
      () => Family.fromLeaves([
        (kp(['a', 'b']), const Int(2)),
        (kp(['a']), const Int(1)),
      ]),
    );
    expect(subtreeFirst, CollisionError(kp(['a'])));
  });

  test('an empty keypath is rejected', () {
    expect(
      attempt(() => Family.fromLeaves([(<Value>[], const Int(1))])),
      const EmptyKeypathError(),
    );
  });

  test('an empty inner level drops its key', () {
    final f = Family.of([(Str('a'), const Int(1)), (Str('b'), const Family.empty())]);
    expect(f.toString(), '{"a" -> 1}');
    expect(f.length, 1);
    expect(f.isEmpty, isFalse);
    expect(const Family.empty().isEmpty, isTrue);
  });

  test('a set maps each key to itself', () {
    final s = Family.set([const Int(3), const Int(1)]);
    expect(s.toString(), '{1, 3}', reason: 'a set is written by its members');
    expect(s[const Int(3)], const Int(3));
    expect(s.keys.toList(), [const Int(1), const Int(3)]);
    expect(s.entries.length, 2);
  });

  test('a literal with a repeated key throws', () {
    expect(
      () => Family.of([(Str('a'), const Int(1)), (Str('a'), const Int(2))]),
      throwsA(isA<ArgumentError>().having((e) => e.message, 'message', contains('repeats a key'))),
    );
  });

  test('the two zeros are one key', () {
    Value neg() => Float(-0.0);
    final f = Family.fromLeaves([
      ([neg()], const Int(1)),
    ]);
    expect(f.toString(), '{0.0 -> 1}', reason: "the key holds 0.0's bits");
    expect(f[Float(0.0)], const Int(1));
    expect(f[neg()], const Int(1));
    final both = [
      ([neg()], const Int(1)),
      ([Float(0.0)], const Int(2)),
    ];
    expect(attempt(() => Family.fromLeaves(both)), isA<CollisionError>());
    // At any depth: inside a tuple key, and at an inner level.
    Value t(double z) => Tuple([Str('x'), Float(z)]);
    final g = Family.fromLeaves([
      ([t(-0.0), neg()], const Int(3)),
    ]);
    expect(g.toString(), '{("x", 0.0) -> {0.0 -> 3}}');
    expect(Family.set([neg(), Float(0.0)]).length, 1);
  });
}
