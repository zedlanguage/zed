/// The unit checks of the revision table: forward transfer contains every result and is exact
/// on single finite pieces, backward transfer keeps every operand that can give the result,
/// and the reductions keep every common member.
library;

import 'package:test/test.dart';
import 'package:zed/store.dart';

const windowLo = -12, windowHi = 12;

/// Every interval with endpoints in -4..=4 or infinite, and some unions.
List<IntervalSet> operands() {
  final ends = <End>[negInf, for (var v = -4; v <= 4; v++) Fin(v), posInf];
  return [
    const IntervalSet.empty(),
    for (final lo in ends)
      for (final hi in ends)
        if (lo <= hi && lo != posInf && hi != negInf) IntervalSet.range(lo, hi),
    IntervalSet.of(-4, -2).join(IntervalSet.of(2, 3)),
    IntervalSet.single(-3).join(IntervalSet.single(0)).join(IntervalSet.single(4)),
  ];
}

/// The members of `s` in the test window, which every finite endpoint of [operands] lies well
/// inside.
List<int> members(IntervalSet s) => [
  for (var v = windowLo; v <= windowHi; v++)
    if (s.contains(v)) v,
];

int? apply(Op op, int x, int y) => switch (op) {
  Op.add => x + y,
  Op.sub => x - y,
  Op.neg => -x,
  Op.mul => x * y,
  Op.div => y == 0 ? null : divEuclid(x, y),
  Op.mod => y == 0 ? null : x % y,
  Op.abs => x.abs(),
  Op.min => x < y ? x : y,
  Op.max => x > y ? x : y,
  _ => _pow(x, op.k),
};

int _pow(int x, int k) {
  var p = 1;
  for (var i = 0; i < k; i++) {
    p *= x;
  }
  return p;
}

const ops = [
  Op.add,
  Op.sub,
  Op.neg,
  Op.mul,
  Op.pow(0),
  Op.pow(2),
  Op.pow(3),
  Op.div,
  Op.mod,
  Op.abs,
  Op.min,
  Op.max,
];

bool finitePiece(IntervalSet s) => switch (s.pieces) {
  [(Fin(), Fin())] => true,
  _ => false,
};

void main() {
  test('forward transfer contains every result in the window', () {
    for (final op in ops) {
      for (final x in operands()) {
        for (final y in operands()) {
          final f = forward(op, x, y);
          final ys = op.arity == 1 ? [0] : members(y);
          for (final a in members(x)) {
            for (final b in ys) {
              if (apply(op, a, b) case final r?) {
                expect(f.contains(r), isTrue, reason: '$op $x $y: $a, $b -> $r not in $f');
              }
            }
          }
        }
      }
    }
  });

  test('forward transfer is exact on finite intervals except mod', () {
    // On operands of one finite piece, the result's hull is the hull of the image.
    for (final op in ops.where((op) => op != Op.mod)) {
      for (final x in operands().where(finitePiece)) {
        for (final y in operands().where(finitePiece)) {
          final ys = op.arity == 1 ? [0] : members(y);
          final image = [
            for (final a in members(x))
              for (final b in ys) ?apply(op, a, b),
          ];
          final want = image.isEmpty
              ? const IntervalSet.empty()
              : IntervalSet.of(
                  image.reduce((m, v) => m < v ? m : v),
                  image.reduce((m, v) => m > v ? m : v),
                );
          expect(forward(op, x, y).hull(), want, reason: '$op $x $y');
        }
      }
    }
  });

  test('backward transfer keeps every operand that can give the result', () {
    final zs = operands();
    final all = operands();
    for (final op in ops) {
      for (var arg = 0; arg < op.arity; arg++) {
        for (final x in all) {
          for (var iy = 0; iy < all.length; iy += 3) {
            final y = all[iy];
            for (var iz = 0; iz < zs.length; iz += 2) {
              final z = zs[iz];
              final got = backward(op, arg, x, y, z);
              expect(got.isSubset(arg == 0 ? x : y), isTrue);
              final ys = op.arity == 1 ? [0] : members(y);
              for (final a in members(x)) {
                for (final b in ys) {
                  final r = apply(op, a, b);
                  if (r == null) continue;
                  final kept = arg == 0 ? a : b;
                  if (z.contains(r) && !got.contains(kept)) {
                    fail('$op arg $arg: x $x y $y z $z: $a, $b -> $r lost from $got');
                  }
                }
              }
            }
          }
        }
      }
    }
  });

  test('a product with a possible zero gives no bound', () {
    // Projected onto an operand, a product of independent operands gives no bound when both
    // the other operand and the result may be 0 (sec:constraints).
    final z = IntervalSet.of(0, 10);
    final x = IntervalSet.top();
    expect(backward(Op.mul, 0, x, IntervalSet.of(0, 3), z), x);
    expect(backward(Op.mul, 0, x, IntervalSet.of(1, 3), z), IntervalSet.of(0, 10));
  });

  test('the reductions keep every common member and tighten the endpoints', () {
    // The interval keeps every member of both and loses only members outside the class; each
    // finite endpoint of the result is a member of the class. An interval cannot hold the
    // intersection exactly: [..=-4] with 0 mod 2 keeps -5.
    for (final x in operands()) {
      for (var m = 0; m <= 5; m++) {
        for (var r = -2; r <= 4; r++) {
          final c = Congruence(m, r);
          final (x2, c2) = reduceCongruence(x, c);
          expect(x2.isSubset(x), isTrue, reason: '$x $c');
          for (var v = windowLo; v <= windowHi; v++) {
            if (x.contains(v) && c.contains(v)) {
              expect(x2.contains(v) && c2.contains(v), isTrue, reason: '$x $c lost $v');
            }
          }
          for (final (lo, hi) in x2.pieces) {
            for (final e in [lo, hi]) {
              if (e case Fin(:final v)) {
                expect(c.contains(v), isTrue, reason: '$x $c: endpoint $v of $x2');
              }
            }
          }
        }
      }
      final (x2, s2) = reduceFinite(x, FiniteSet.of([-3, 0, 1, 7]));
      expect(members(x2), [...s2.members!]);
    }
    final (x, _) = reduceCongruence(IntervalSet.range(negInf, const Fin(-4)), Congruence(3, 1));
    expect(x, IntervalSet.range(negInf, const Fin(-5)));
  });
}
