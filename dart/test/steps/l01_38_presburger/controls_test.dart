/// Relations of any size, the undecided fragment, and controls: each check of `random` rejects
/// a wrong answer.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart' hide Atom;
import 'package:zed/presburger.dart';
import 'package:zed/store.dart' show BoolDemand, Domains, IntervalSet, preimage, relations;

import 'checks.dart';

const x = Var('x');

/// `x < 3`.
const belowThree = PrimApp(Prim.lt, [x, Lit(Int(3))]);

Lin sym(String n) => Lin.atom(Sym(n));

Lin k(int c) => Lin.constant(BigInt.from(c));

void main() {
  test('a relation of any size is decided', () {
    // The sum of 40 symbols: there is no limit on the atoms.
    final sum = Con(
      [for (var i = 0; i < 40; i++) sym('a$i')].fold(k(-50), (l, a) => l.plus(a)),
      Rel.ge,
    );
    final m = satisfiable(sum)!;
    expect(sum.holds(m), isTrue);
    final r = Relation.of(sum);
    expect(entails(r, r), isA<Proved>());
    // 200 constraints over one symbol, and the last one false with them.
    final many = <Formula>[for (var c = 0; c < 200; c++) Con.ge(sym('x'), k(c))];
    expect(satisfiable(Formula.and(many)), isNotNull);
    many.add(Con.ge(k(198), sym('x')));
    expect(satisfiable(Formula.and(many)), isNull);
    // The preimage of a sum of 40 inputs has its relation, and its box.
    final inputs = [for (var i = 0; i < 40; i++) 'a$i'];
    final total = [for (final n in inputs) Var(n) as Term]
        .reduce((a, b) => PrimApp(Prim.add, [a, b]));
    final t = PrimApp(Prim.lt, [total, lit(50)]);
    final doms = Domains()..addAll({for (final n in inputs) n: IntervalSet.of(0, 1000)});
    final p = preimage(t, doms, const BoolDemand(true));
    expect(p.relation != null && !p.exact, isTrue);
    expect(
      p.domains.values.every((d) => d == IntervalSet.of(0, 49)),
      isTrue,
      reason: '${p.domains}',
    );
  });

  test('a question between the shadows is undecided and the written constraint kept', () {
    // Pugh's example: 27 <= 11x + 13y <= 45, -10 <= 7x - 9y <= 4 has no integer point, its dark
    // shadow is empty and its real shadow is not.
    Lin l(int a, int b, int c) =>
        sym('x').times(BigInt.from(a)).plus(sym('y').times(BigInt.from(b))).plus(k(c));
    Formula ge0(Lin l) => Con.ge(l, k(0));
    final pugh = Formula.and([
      ge0(l(11, 13, -27)),
      ge0(l(-11, -13, 45)),
      ge0(l(7, -9, 10)),
      ge0(l(-7, 9, 4)),
    ]);
    expect(() => satisfiable(pugh), throwsA(isA<Over>()));
    final e = entails(Relation.of(pugh), const Relation.of(Formula.bottom));
    expect(e, isA<Undecided>());
    expect('$e', 'undecided: outside the fragment the Omega test decides');
  });

  test('each check rejects a wrong answer', () {
    const t = belowThree;
    final rs = relations([t], names, false)!;
    expect(checkPoints(rs[0], t, names), isNull);
    // The relation of `x < 4` in its place.
    final wrong = relations(
      [
        PrimApp(Prim.lt, [x, lit(4)]),
      ],
      names,
      false,
    )!;
    expect(checkPoints(wrong[0], t, names), isNotNull);
    // A model outside the test, and no model where there is one.
    expect(checkModel([3, 0], t, names), isNotNull);
    expect(checkModel(null, t, names), isNotNull);
    expect(checkModel([2, 0], t, names), isNull);
    // A projection one short, and one past the hull.
    final right = [IntervalSet.of(-5, 2), IntervalSet.of(-5, 5)];
    expect(checkProjection(right, t, names), isNull);
    expect(checkProjection([IntervalSet.of(-5, 1), right[1]], t, names), isNotNull);
    expect(checkProjection([IntervalSet.of(-5, 3), right[1]], t, names), isNotNull);
    // A proof the window refutes, and a countermodel that is none.
    const g = PrimApp(Prim.lt, [x, Lit(Int(2))]);
    expect(checkEntailment(const Proved([]), t, g, names), isNotNull);
    Model at(int v) => Model()..[Sym('x')] = BigInt.from(v);
    expect(checkEntailment(Refuted(at(0)), t, g, names), isNotNull);
    expect(checkEntailment(Refuted(at(2)), t, g, names), isNull);
  });
}
