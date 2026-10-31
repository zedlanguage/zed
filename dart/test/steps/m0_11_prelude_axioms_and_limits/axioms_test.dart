/// Every axiom holds on the finite-model harness's instances of its carrier (step M0.10), run
/// on the reference evaluator; each kind of law has a false claim the same check refutes; and
/// the prelude's copy of the table is the one in `lib/axioms.dart`.
library;

import 'dart:io';

import 'package:test/test.dart';
import 'package:zed/axioms.dart';
import 'package:zed/kernel.dart';

import '../../support/check.dart';
import '../../support/instances.dart';
import '../../support/support.dart';

/// The harness's values of a carrier: the rung 6 integers and floats, both booleans, and the
/// strings over `a`, `b` of length at most 3.
List<Value> values(Carrier c) => switch (c) {
  Carrier.int => [for (final n in bmcInts()) Int(n)],
  Carrier.f64 => bmcFloatValues(),
  Carrier.bool => const [Bool(false), Bool(true)],
  Carrier.string => [
    for (final s in shortlex(['a', 'b'], 3)) Str(s.join()),
  ],
};

const _prims = {
  '+': Prim.add,
  '++': Prim.concat,
  '-': Prim.sub,
  '*': Prim.mul,
  'neg': Prim.neg,
  'min': Prim.min,
  'max': Prim.max,
  '&&': Prim.and,
  '||': Prim.or,
  '!': Prim.not,
  '==': Prim.eq,
  '!=': Prim.ne,
  '<': Prim.lt,
  '<=': Prim.le,
  '>': Prim.gt,
  '>=': Prim.ge,
};

/// The kernel term of `op` applied to `args`. `square` is not an operator: it is here so the
/// controls can claim a law of a unary function that does not have it.
Term call(String op, List<Term> args) => op == 'square'
    ? prim(Prim.mul, [args[0], args[0]])
    : prim(_prims[op] ?? (throw ArgumentError('no kernel primitive for `$op`')), args);

Value run(String op, List<Value> args) => eval(call(op, [for (final v in args) Lit(v)]));

bool holds(String op, List<Value> args) => run(op, args) == const Bool(true);

bool le(Value a, Value b) => holds('<=', [a, b]);

/// Checks `a` on every instance; returns how many were run, or throws the first
/// counterexample.
int check(Axiom a) {
  final vs = values(a.carrier);
  final op = a.op;
  var n = 0;
  void eq(String what, Term l, Term r) {
    n++;
    final (x, y) = (outcome(l), outcome(r));
    if (!agree(x, y)) throw '$what: $x against $y';
  }

  void must(bool ok, String what) {
    n++;
    if (!ok) throw what;
  }

  final pairs = [
    for (final x in vs)
      for (final y in vs) (x, y),
  ];
  final triples = [
    for (final (x, y) in pairs)
      for (final z in vs) (x, y, z),
  ];
  switch (a.law) {
    case Plain.associative:
      for (final (x, y, z) in triples) {
        final l = call(op, [
          call(op, [Lit(x), Lit(y)]),
          Lit(z),
        ]);
        final r = call(op, [
          Lit(x),
          call(op, [Lit(y), Lit(z)]),
        ]);
        eq('$x, $y, $z', l, r);
      }
    case Plain.commutative:
      for (final (x, y) in pairs) {
        eq('$x, $y', call(op, [Lit(x), Lit(y)]), call(op, [Lit(y), Lit(x)]));
      }
    case Plain.idempotent:
      for (final x in vs) {
        eq('$x', call(op, [Lit(x), Lit(x)]), Lit(x));
      }
    case Identity(:final e) || Zero(z: final e):
      for (final x in vs) {
        final out = a.law is Identity ? x : e;
        eq('$e left of $x', call(op, [Lit(e), Lit(x)]), Lit(out));
        eq('$e right of $x', call(op, [Lit(x), Lit(e)]), Lit(out));
      }
    case Inverse(:final g):
      for (final x in vs) {
        eq(
          '$g after, $x',
          call(g, [
            call(op, [Lit(x)]),
          ]),
          Lit(x),
        );
        eq(
          '$g before, $x',
          call(op, [
            call(g, [Lit(x)]),
          ]),
          Lit(x),
        );
      }
    case LeftDistributesOver(:final add) || RightDistributesOver(:final add):
      final left = a.law is LeftDistributesOver;
      Term mul(Term p, Term q) => left ? call(op, [p, q]) : call(op, [q, p]);
      for (final (x, y, z) in triples) {
        final l = mul(Lit(x), call(add, [Lit(y), Lit(z)]));
        final r = call(add, [mul(Lit(x), Lit(y)), mul(Lit(x), Lit(z))]);
        eq('$x, $y, $z', l, r);
      }
    case Monotone(:final signs):
      var all = <List<Value>>[[]];
      for (var i = 0; i < signs.length; i++) {
        all = [
          for (final p in all)
            for (final x in vs) [...p, x],
        ];
      }
      for (var i = 0; i < signs.length; i++) {
        for (final args in all) {
          for (final b in vs.where((b) => le(args[i], b))) {
            final moved = [...args]..[i] = b;
            final (fa, fb) = (run(op, args), run(op, moved));
            final ok = switch (signs[i]) {
              Tonicity.up => le(fa, fb),
              Tonicity.down => le(fb, fa),
            };
            must(ok, 'argument $i from ${args[i]} to $b: $fa then $fb');
          }
        }
      }
    case Plain.injective:
      for (final (x, y) in pairs) {
        must(x == y || run(op, [x]) != run(op, [y]), '$x and $y meet');
      }
    case Plain.reflexive || Plain.irreflexive:
      for (final x in vs) {
        must(holds(op, [x, x]) == (a.law == Plain.reflexive), '$x');
      }
    case Plain.symmetric || Plain.antisymmetric || Plain.total:
      for (final (x, y) in pairs) {
        final (xy, yx) = (holds(op, [x, y]), holds(op, [y, x]));
        final ok = switch (a.law) {
          Plain.symmetric => !xy || yx,
          Plain.antisymmetric => !(xy && yx) || x == y,
          _ => xy || yx,
        };
        must(ok, '$x, $y');
      }
    case Plain.transitive:
      for (final (x, y, z) in triples) {
        must(!holds(op, [x, y]) || !holds(op, [y, z]) || holds(op, [x, z]), '$x, $y, $z');
      }
  }
  return n;
}

/// The kind of a law, whatever its argument.
Object kind(Law law) => law is Plain ? law : law.runtimeType;

/// An axiom as the prelude writes it.
String zedLine(Axiom a) {
  String c(Value k) => switch (k) {
    Str(:final text) => '"$text"',
    Bool(:final value) => '$value',
    Float(:final x) => '$x',
    _ => '$k',
  };
  final law = switch (a.law) {
    Plain p => '#${p.name}',
    Identity(:final e) => '#identity(${c(e)})',
    Zero(:final z) => '#zero(${c(z)})',
    Inverse(:final g) => '#inverse("$g")',
    LeftDistributesOver(:final add) => '#leftDistributesOver("$add")',
    RightDistributesOver(:final add) => '#rightDistributesOver("$add")',
    Monotone(:final signs) => '#monotone([${signs.map((t) => '#${t.name}').join(', ')}])',
  };
  return 'Axiom(op: "${a.op}", carrier: #${a.carrier.name}, law: $law),';
}

void main() {
  test('every axiom holds on the harness instances', () {
    var total = 0;
    for (final a in axioms) {
      try {
        total += check(a);
      } on String catch (why) {
        fail('${a.op} at ${a.carrier}: ${a.law} fails on $why');
      }
    }
    expect(axioms.length, 82);
    expect(total, greaterThan(50000));
  });

  test('a false claim of each kind is refuted', () {
    Axiom claim(String op, Carrier carrier, Law law) => (op: op, carrier: carrier, law: law);
    final controls = [
      claim('+', Carrier.f64, Plain.associative), // 0.1 + 0.2 + 0.3
      claim('++', Carrier.string, Plain.commutative),
      claim('+', Carrier.int, Plain.idempotent),
      claim('+', Carrier.f64, Identity(Float(0.0))), // -0.0 + 0.0 is 0.0
      claim('*', Carrier.f64, Zero(Float(0.0))), // 0.0 * inf is NaN
      claim('square', Carrier.int, const Inverse('neg')),
      claim('+', Carrier.int, const LeftDistributesOver('*')),
      claim('-', Carrier.int, const RightDistributesOver('*')),
      claim('-', Carrier.int, const Monotone([Tonicity.up, Tonicity.up])),
      claim('square', Carrier.int, Plain.injective),
      claim('<', Carrier.int, Plain.reflexive),
      claim('<=', Carrier.int, Plain.irreflexive),
      claim('<', Carrier.int, Plain.symmetric),
      claim('!=', Carrier.int, Plain.antisymmetric),
      claim('!=', Carrier.int, Plain.transitive),
      claim('<', Carrier.int, Plain.total),
    ];
    for (final c in controls) {
      expect(() => check(c), throwsA(isA<String>()), reason: '${c.op}: ${c.law} not refuted');
    }
    // Every kind of law has a control.
    final kinds = {for (final c in controls) kind(c.law)};
    for (final a in axioms) {
      expect(kinds, contains(kind(a.law)));
    }
  });

  test('the prelude copy is the table', () {
    final prelude = [
      for (final l in File(
        '${packageDir.parent.path}/zed/prelude/axioms.zed',
      ).readAsLinesSync().map((l) => l.trim()))
        if (l.startsWith('Axiom(')) l,
    ];
    expect(prelude, axioms.map(zedLine).toList());
  });
}
