/// Binder normalization: definitions that differ only in local names share an address, and
/// every other difference changes it. Checked by hand on ordinary definitions and against an
/// independent alpha-equivalence test (de Bruijn indices) on random terms.
library;

import 'package:test/test.dart';
import 'package:zed/address.dart';
import 'package:zed/canon.dart';
import 'package:zed/kernel.dart';
import 'package:zed/src/canon/binders.dart' as binders;

import '../../support/instances.dart';
import 'harness.dart';

Term field(String v, String f) => prim(Prim.get, [var_(v), lit(f)]);

/// `fam(lines, v -> v.qty * v.price)` folded with `+`: an invoice total.
Term invoice(String v, {String lines = 'lines', String price = 'price', Term? identity}) => Fold(
  Fam(var_(lines), v, prim(Prim.mul, [field(v, 'qty'), field(v, price)])),
  const PrimFn(Prim.add),
  identity ?? lit(0),
  1,
  const {},
);

/// Fibonacci by definedness: `this` and the key are binders of the step. `call` is the name
/// the step calls and `key` the name it reads as the key.
Term fibStep(String self, String n, String call, String key) => Fix(
  var_('upTo'),
  if_(
    prim(Prim.lt, [var_(key), lit(2)]),
    var_(key),
    prim(Prim.add, [
      app(var_(call), [
        prim(Prim.sub, [var_(key), lit(1)]),
      ]),
      app(var_(call), [
        prim(Prim.sub, [var_(key), lit(2)]),
      ]),
    ]),
  ),
  self,
  n,
  const Definedness(),
  const {},
);

const bound = ['a', 'b', 'x'];
const free = ['price', 'qty'];

/// A random term over the binding forms the canonicalizer renames. `names` picks the written
/// name of each binder from its own stream, so two calls with one `shape` seed and different
/// `names` seeds give terms of one shape and different names.
Term random(Rng shape, Rng names, int depth, List<String> scope) {
  if (depth == 0 || shape.below(4) == 0) {
    final k = shape.below(3);
    if (k == 0 && scope.isNotEmpty) {
      // A binder by its position in scope, written by its name.
      return var_(scope[scope.length - 1 - shape.below(scope.length)]);
    }
    return k == 1 ? var_(free[shape.below(2)]) : lit(shape.int_(0, 2));
  }
  Term sub() => random(shape, names, depth - 1, scope);
  Term under(List<String> xs) {
    scope.addAll(xs);
    final body = sub();
    scope.length -= xs.length;
    return body;
  }

  switch (shape.below(6)) {
    case 0:
      final n = 1 + shape.below(2);
      final ps = [for (var i = 0; i < n; i++) names.pick(bound)];
      return lam(ps, under(ps));
    case 1:
      final x = names.pick(bound);
      final e = sub();
      return let_(x, e, under([x]));
    case 2:
      final e = sub();
      final x = names.pick(bound);
      final arm = under([x]);
      final other = sub();
      return Match(e, [
        (TupleP([BindP(x), const WildP()]), arm),
        (const WildP(), other),
      ]);
    case 3:
      final d = sub();
      final x = names.pick(bound);
      return Fam(d, x, under([x]));
    case 4:
      final f = sub();
      return app(f, [sub()]);
    default:
      final a = sub();
      return prim(Prim.add, [a, sub()]);
  }
}

/// An independent rendering of a term's alpha-class: each bound variable written as its de
/// Bruijn index, counted outward from the use, and each free one by name.
String indices(Term t, List<String> env) {
  String under(List<String> names, Term body) {
    env.addAll(names);
    final s = indices(body, env);
    env.length -= names.length;
    return s;
  }

  return switch (t) {
    Lit(:final value) => '$value',
    Var(:final name) => switch (env.lastIndexOf(name)) {
      < 0 => '\$$name',
      final i => '#${env.length - 1 - i}',
    },
    Lam(:final params, :final body) => '(\\${params.length} ${under(params, body)})',
    App(:final f, :final args) => '(${indices(f, env)} ${indices(args[0], env)})',
    PrimApp(:final args) => '(+ ${indices(args[0], env)} ${indices(args[1], env)})',
    Let(:final name, :final value, :final body) =>
      '(let ${indices(value, env)} ${under([name], body)})',
    Match(
      :final scrutinee,
      arms: [(TupleP(items: [BindP(:final name), _]), final arm), (_, final other)],
    ) =>
      '(match ${indices(scrutinee, env)} ${under([name], arm)} ${indices(other, env)})',
    Fam(:final domain, :final variable, :final body) =>
      '(fam ${indices(domain, env)} ${under([variable], body)})',
    _ => throw StateError('the generator makes no other form'),
  };
}

/// `canonicalize` renames every binder in one pass; the rules rename one per step. Both must
/// give the same definition.
void onePassIsStepwise(Term t) {
  final d = def('f', t);
  final onePass = canonicalize(d);
  while (rules.any((r) => r.apply(d))) {}
  expect(onePass == d, isTrue);
}

void main() {
  test('an invoice total has one address whatever its line is called', () {
    final a = addr(def('total', invoice('line')));
    expect(addr(def('total', invoice('row'))), a);
    expect(addr(def('total', invoice('lines'))), a);
    // The free name `lines`, the definition's own name and a field name are part of the
    // interface: each changes the address.
    expect(addr(def('total', invoice('line', lines: 'items'))), isNot(a));
    expect(addr(def('subtotal', invoice('line'))), isNot(a));
    expect(addr(def('total', invoice('line', price: 'cost'))), isNot(a));
  });

  test('shadowing decides which binder a name means', () {
    // `fee -> (fee -> fee)` returns the inner argument, `fee -> (amount -> fee)` the outer.
    final inner = lam(['fee'], lam(['fee'], var_('fee')));
    final outer = lam(['fee'], lam(['amount'], var_('fee')));
    final inner2 = lam(['a'], lam(['b'], var_('b')));
    expect(addr(def('f', inner)), addr(def('f', inner2)));
    expect(addr(def('f', inner)), isNot(addr(def('f', outer))));
    // Two parameters of one name: the later one is meant.
    expect(
      addr(def('snd', lam(['x', 'x'], var_('x')))),
      addr(def('snd', lam(['p', 'q'], var_('q')))),
    );
    // `rate = 3; rate = rate * 2; rate` reads the first rate in the second binding's value.
    Term rebound(String a, String b) =>
        let_(a, lit(3), let_(b, prim(Prim.mul, [var_(a), lit(2)]), var_(b)));
    expect(addr(def('r', rebound('rate', 'rate'))), addr(def('r', rebound('x', 'y'))));
    // A local that shadows a free name hides it; the free name elsewhere is still the free one.
    final shadowFree = let_('tax', lit(1), var_('tax'));
    final freeTax = let_('t', lit(1), var_('tax'));
    expect(addr(def('v', shadowFree)), isNot(addr(def('v', freeTax))));
  });

  test('pattern and recursion binders are normalized', () {
    // `match status { (code, _) -> code, _ -> 0 }`, with the code called two ways.
    Term m(String c) => Match(var_('status'), [
      (TupleP([BindP(c), const WildP()]), var_(c)),
      (const WildP(), lit(0)),
    ]);
    expect(addr(def('code', m('code'))), addr(def('code', m('c'))));
    // A pattern binding the same name twice means the later one.
    Term pair(String a, String b, String use) => Match(var_('p'), [
      (TupleP([BindP(a), BindP(b)]), var_(use)),
    ]);
    expect(addr(def('s', pair('x', 'x', 'x'))), addr(def('s', pair('a', 'b', 'b'))));
    expect(addr(def('s', pair('x', 'x', 'x'))), isNot(addr(def('s', pair('a', 'b', 'a')))));
    Term fib(String self, String n) => fibStep(self, n, self, n);
    expect(addr(def('fib', fib('fib', 'n'))), addr(def('fib', fib('f', 'k'))));
    expect(
      addr(def('fib', fib('fib', 'n'))),
      isNot(addr(def('fib', fibStep('fib', 'n', 'n', 'fib')))),
    );
  });

  test('a dependency change changes its dependents but a local rename does not', () {
    // `due = total * 1.08`, where `total` is the invoice definition above.
    final due = def('due', prim(Prim.mul, [var_('total'), lit(1.08)]));
    final totalA = addr(def('total', invoice('line')));
    final totalB = addr(def('total', invoice('row')));
    final totalC = addr(def('total', invoice('line', identity: lit(-5))));
    ContentAddress at(ContentAddress t) => address(due, (n) => n == 'total' ? t : null);
    expect(at(totalA), at(totalB));
    expect(at(totalA), isNot(at(totalC)));
    expect(at(totalA), isNot(addr(due)));
  });

  test('literals are hashed by their exact value', () {
    ContentAddress l(Value v) => addr(def('k', Lit(v)));
    expect(l(Float(0.0)), isNot(l(Float(-0.0))));
    expect(l(Float(double.nan)), l(Float(-double.nan)));
    expect(l(const Int(1)), isNot(l(Float(1.0))));
    expect(l(Str('empty')), isNot(l(const Atom('empty'))));
    expect(l(const Tuple([])), isNot(l(const Path([]))));
  });

  test('the rename step records the written name and its place', () {
    final (t, i, w) = binders.step(lam(['acc'], let_('x', var_('acc'), var_('x'))))!;
    expect((i, w), (0, 'acc'));
    final (_, j, v) = binders.step(t)!;
    expect((j, v), (1, 'x'));
    expect(levelOf(levelName(7)), 7);
    expect(levelOf('x'), isNull);
  });

  test('addresses agree with an independent alpha-equivalence test', () {
    var (same, differ) = (0, 0);
    for (var seed = 0; seed < randomInstances * 4; seed++) {
      Term make(int names) => random(Rng(seed), Rng(names), 4, []);
      final (s, t) = (make(seed ^ 0x51), make(seed ^ 0x9e));
      final alpha = indices(s, []) == indices(t, []);
      expect(addr(def('f', s)) == addr(def('f', t)), alpha, reason: 'seed $seed');
      if (alpha) {
        same++;
      } else {
        differ++;
      }
    }
    // Both outcomes occur often enough for the agreement to mean something.
    expect(same > 300 && differ > 300, isTrue, reason: '$same alike, $differ different');
  });

  test('the normal form is the rules applied one step at a time', () {
    for (var seed = 0; seed < randomInstances; seed++) {
      onePassIsStepwise(random(Rng(seed), Rng(~seed), 4, []));
    }
    // A step reading `this` and the key, which are bound in that order.
    onePassIsStepwise(
      Fix(
        var_('upTo'),
        app(var_('fib'), [
          prim(Prim.sub, [var_('n'), lit(1)]),
        ]),
        'fib',
        'n',
        const Definedness(),
        const {},
      ),
    );
    // `(x -> x)(x)`: the last `x` is outside the binder's scope and stays free.
    onePassIsStepwise(app(lam(['x'], var_('x')), [var_('x')]));
    // A binder already carrying a level name, though not its own level, keeps it.
    final level = levelName(5);
    onePassIsStepwise(lam(['y', level], prim(Prim.add, [var_('y'), var_(level)])));
  });
}
