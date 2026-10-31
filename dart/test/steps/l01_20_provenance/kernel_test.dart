/// Fact addresses in kernel terms: calls, higher-order calls, and every region form.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import '../../support/kernel.dart';
import 'provenance.dart';

/// The keypaths of `facts`.
List<List<Value>> keypaths(Iterable<Fact> facts) => [for (final f in facts) f.address.keypath];

void main() {
  test('two calls of one function are two facts', () {
    // let shipping = w -> w * 3 + 5 in shipping(2) + shipping(10)
    final body = add(mul(var_('w'), lit(3)), lit(5));
    final t = let_(
      'shipping',
      lam(['w'], body),
      add(app(var_('shipping'), [lit(2)]), app(var_('shipping'), [lit(10)])),
    );
    final (v, p) = trace(t);
    expect(v, const Int(46));
    unique(p);
    final calls = at(p, '$body');
    expect(calls, hasLength(2));
    // Same node, same keypath: only the call site tells them apart.
    expect(calls[0].address.keypath, calls[1].address.keypath);
    expect(calls[0].address.node.position, calls[1].address.node.position);
    expect(calls[0].address.node, isNot(calls[1].address.node));
    expect([for (final f in calls) f.value], [const Int(11), const Int(35)]);
  });

  test('a function called through another is named by both call sites', () {
    // let twice = (f, x) -> f(f(x)) in twice(y -> y * 2, 3) + twice(y -> y * 2, 4)
    final twice = lam(
      ['f', 'x'],
      app(var_('f'), [
        app(var_('f'), [var_('x')]),
      ]),
    );
    final double = lam(['y'], mul(var_('y'), lit(2)));
    final t = let_(
      'twice',
      twice,
      add(app(var_('twice'), [double, lit(3)]), app(var_('twice'), [double, lit(4)])),
    );
    final (v, p) = trace(t);
    expect(v, const Int(28));
    unique(p);
    final doubled = at(p, '(y * 2)');
    expect(doubled, hasLength(4));
    // Each instance is two calls deep: the call of `twice`, then a call of `f` inside it.
    expect(doubled.every((f) => f.address.node.length == 3), isTrue);
  });

  test('an atom passed through functions keeps its literal as origin', () {
    // let pass = x -> x; let wrap = x -> pass(x) in wrap(#late)
    final t = let_(
      'pass',
      lam(['x'], var_('x')),
      let_('wrap', lam(['x'], app(var_('pass'), [var_('x')])), app(var_('wrap'), [atom('late')])),
    );
    final (v, p) = trace(t);
    expect(v, const Atom('late'));
    unique(p);
    expect(origins(p, p.result), [('#late', '#late')]);
  });

  test('a failure bound by a match arm keeps its origin', () {
    // match int("7.5x") { #inexact -> 0; n -> n + 1 }: the sum read the cast through `n`.
    final t = Match(prim(Prim.castInt, [lit(s('7.5x'))]), [
      (const LitP(Atom('inexact')), lit(0)),
      (const BindP('n'), add(var_('n'), lit(1))),
    ]);
    final (v, p) = trace(t);
    expect(v, const Atom('invalid'));
    unique(p);
    expect(origins(p, p.result), [('int("7.5x")', '#invalid')]);
  });

  test('a merged failure names the origin of each member', () {
    // let price = int("12x"); let qty = 3 div 0 in price * qty
    final t = let_(
      'price',
      prim(Prim.castInt, [lit(s('12x'))]),
      let_('qty', idiv(lit(3), lit(0)), mul(var_('price'), var_('qty'))),
    );
    final (v, p) = trace(t);
    expect(v.errs?.length, 2, reason: '$v');
    unique(p);
    final o = origins(p, p.result);
    expect(o, hasLength(2));
    expect(o.any((x) => x.$1.contains('div')), isTrue, reason: '$o');
    expect(o.any((x) => x.$1.contains('12x')), isTrue, reason: '$o');
  });

  test('word count has a fact per word and per group', () {
    final doc = linesOf([
      ['to', 'be', 'or'],
      ['not', 'to', 'be'],
    ]);
    // Each word to `word -> line -> 1`, then summed over the lines.
    final kf = lam(['p', 'w'], path([var_('w'), key(var_('p'), 0)]));
    final ones = reindex(lit(doc), kf, lam(['p', 'w'], lit(1)));
    final (v, p) = trace(foldAt(ones, 2, const PrimFn(Prim.add)));
    expect('$v', '{"be" -> 2, "not" -> 1, "or" -> 1, "to" -> 2}');
    unique(p);
    // The value function runs once per word, keyed by the word's line and position.
    final words = keypaths(at(p, '1'));
    expect(words, hasLength(6));
    expect(words, contains(equals([const Int(0), const Int(1), const Int(2)])));
  });

  test('a combine step is named by its group and index', () {
    // Per customer, the order totals summed by a written function.
    final orders = Family.fromLeaves([
      ([s('ann'), const Int(1)], const Int(5)),
      ([s('ann'), const Int(2)], const Int(7)),
      ([s('ann'), const Int(3)], const Int(9)),
      ([s('bob'), const Int(4)], const Int(2)),
      ([s('bob'), const Int(5)], const Int(4)),
    ]);
    final plus = lam(['a', 'b'], add(var_('a'), var_('b')));
    final (v, p) = trace(foldAt(lit(orders), 2, plus));
    expect('$v', '{"ann" -> 21, "bob" -> 6}');
    unique(p);
    final steps = [for (final k in keypaths(at(p, '(a + b)'))) '$k']..sort();
    expect(steps, ['[0, "ann", 0]', '[0, "ann", 1]', '[0, "bob", 0]']);
  });

  test('a selector runs once per key at every level', () {
    // Keep the teams and players whose score is above 3; teams always pass.
    final scores = Family.fromLeaves([
      ([s('red'), s('ada')], const Int(5)),
      ([s('red'), s('bo')], const Int(2)),
      ([s('blue'), s('cy')], const Int(4)),
    ]);
    final sel = lam([
      'p',
      'v',
    ], if_(eq(prim(Prim.pathLen, [var_('p')]), lit(1)), lit(true), lt(lit(3), var_('v'))));
    final (v, p) = trace(discard(lit(scores), sel));
    expect('$v', '{"blue" -> {"cy" -> 4}, "red" -> {"ada" -> 5}}');
    unique(p);
    expect(at(p, '(3 < v)'), hasLength(3));
  });

  test('a family body runs once per key', () {
    final t = fam(
      lit(
        Family.set([
          for (final n in [1, 2, 3]) Int(n),
        ]),
      ),
      'n',
      mul(var_('n'), var_('n')),
    );
    final (v, p) = trace(t);
    expect('$v', '{1 -> 1, 2 -> 4, 3 -> 9}');
    unique(p);
    expect(keypaths(at(p, '(n * n)')), [
      for (final n in [1, 2, 3]) [const Int(0), Int(n)],
    ]);
  });

  test('a lattice fixpoint names each iterate', () {
    // Airports reachable from cdg: the `to` of each route whose `from` is reached.
    final routes = Family.set([
      for (final (a, b) in [('cdg', 'lhr'), ('lhr', 'jfk'), ('jfk', 'sfo'), ('syd', 'akl')])
        Tuple([s(a), s(b)]),
    ]);
    final fromReached = discard(
      lit(routes),
      lam(['p', 'e'], found(get(var_('r'), nth(var_('e'), 0)))),
    );
    final step = lam(['r'], fam(groupBy(fromReached, (e) => nth(e, 1)), 'k', var_('k')));
    final t = fixLattice(lit(Family.set([s('cdg')])), step, const PrimFn(Prim.union));
    final (v, p) = trace(t);
    expect('$v', '{"cdg", "jfk", "lhr", "sfo"}');
    unique(p);
    // The step ran four times, the last finding nothing new.
    final terms = p.terms();
    final iterates = <List<Value>>[];
    for (final f in p.facts) {
      if (terms[f.address.node.position] is! Fam) continue;
      if (iterates.isEmpty || '${iterates.last}' != '${f.address.keypath}') {
        iterates.add(f.address.keypath);
      }
    }
    expect(iterates, [
      for (var i = 0; i < 4; i++) [const Int(0), Int(i)],
    ]);
  });

  test('a definedness entry is one fact however many attempts it took', () {
    final domain = lit(Family.set([for (var i = 0; i <= 12; i++) Int(i)]));
    final fib = fixDefined(domain, (self, i) {
      Term at(int d) => get(self, sub(i, lit(d)));
      return if_(lt(i, lit(2)), i, add(at(1), at(2)));
    });
    final (v, p) = trace(fib);
    expect((v as Family)[const Int(12)], const Int(144));
    unique(p);
    // One `if` per entry: the attempts that read an undefined entry were dropped.
    final terms = p.terms();
    expect(p.facts.where((f) => terms[f.address.node.position] is If), hasLength(13));
  });

  test('a generation names its step and guard by t', () {
    // Halve 40 while it is even: 40, 20, 10, 5.
    final t = Gen(
      lit(40),
      lam(['x'], idiv(var_('x'), lit(2))),
      lam(['x'], eq(modulo(var_('x'), lit(2)), lit(0))),
      GuardPos.before,
    );
    final (v, p) = trace(t);
    expect('$v', '{0 -> 40, 1 -> 20, 2 -> 10, 3 -> 5}');
    unique(p);
    final steps = at(p, '(x div 2)');
    expect(keypaths(steps), [
      for (final t in [1, 2, 3]) [const Int(0), Int(t)],
    ]);
    expect(at(p, '((x mod 2) == 0)'), hasLength(4));
    expect([for (final f in steps) f.value], [const Int(20), const Int(10), const Int(5)]);
    // The step making generation 2 read generation 1's fact.
    expect(p.facts[steps[1].inputs.first].value, const Int(20));
  });

  test('every keypath starts with the wave stamp', () {
    final t = fam(lit(Family.set([const Int(1), const Int(2)])), 'n', add(var_('n'), lit(1)));
    final ev = Evaluator(World(), provenanceRoot: const [Int(7)]);
    ev.run(t);
    expect(ev.provenance!.facts.every((f) => f.address.keypath.first == const Int(7)), isTrue);
  });

  test('without the request nothing is recorded and the value is the same', () {
    final t = let_('f', lam(['x'], add(var_('x'), lit(1))), app(var_('f'), [lit(1)]));
    final ev = Evaluator(World());
    expect(ev.run(t), trace(t).$1);
    expect(ev.provenance, isNull);
  });
}
