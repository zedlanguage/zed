/// Which changes to a graph keep its address, and which change it.
library;

import 'package:test/test.dart';
import 'package:zed/zir.dart';

import 'zir.dart';

/// An optional discount: the arm that has one subtracts it, the other passes the price on.
const discount = '''
zir 1
r region function ((| #none (#some (tuple int))); int in [0..] hint name "price")
r.0 match [#some(off), #none] (r^0, r^1) -> (int)
r.0/0 region match (int; int in [0..] hint name "price")
r.0/0.0 prim - (r.0/0^1, r.0/0^0) -> (int)
r.0/0 results (r.0/0.0^0)
r.0/1 region match (int in [0..] hint name "price")
r.0/1 results (r.0/1^0)
r results (r.0^0)
''';

/// [discount] with `from` replaced by `to`, which must occur in it.
Region with_(String from, String to) {
  expect(discount, contains(from));
  return graph(discount.replaceAll(from, to));
}

/// A graph of one function region with the one argument `e`, which it returns.
String one(String e) => 'zir 1\nr region function ($e)\nr results (r^0)\n';

void main() {
  test('renamed binders keep the address', () {
    final a = address(graph(discount));
    expect(address(with_('#some(off)', '#some(d)')), a);
    // A pair pattern's binders, renamed together and apart.
    Region pair(String p) => graph(
      'zir 1\nr region function (tuple)\nr.0 match [$p] (r^0) -> (int)\nr.0/0 region match (int; int)\nr.0/0.0 prim + (r.0/0^0, r.0/0^1) -> (int)\nr.0/0 results (r.0/0.0^0)\nr results (r.0^0)\n',
    );
    expect(address(pair('(x, y)')), address(pair('(lo, hi)')));
    expect(address(pair('(y, x)')), address(pair('(x, y)')));
    // Each binder takes its own level: the second is the one argument before it.
    final m = canonicalize(pair('(lo, hi)')).nodes[0].op as MatchOp;
    expect(pattern(m.patterns[0]), '(\u{0}0, \u{0}1)');
    // A match one region down, inside a function's body.
    Region inner(String a, String b) => graph(
      'zir 1\nr region function ()\nr.0 lambda () -> ((-> tuple int))\nr.0/0 region function (tuple)\nr.0/0.0 match [($a, $b)] (r.0/0^0) -> (int)\nr.0/0.0/0 region match (int; int)\nr.0/0.0/0 results (r.0/0.0/0^1)\nr.0/0 results (r.0/0.0^0)\nr results (r.0^0)\n',
    );
    expect(address(inner('key', 'count')), address(inner('k', 'n')));
    // Binding where a literal was matched is a different graph.
    expect(address(pair('(x, =0)')), isNot(address(pair('(x, y)'))));
  });

  test('hints do not reach the address', () {
    final a = address(graph(discount));
    expect(address(with_('hint name "price")\nr.0 ', 'hint name "cost")\nr.0 ')), a);
    expect(address(graph(discount.replaceAll(' hint name "price"', ''))), a);
  });

  test('facet order and repeats do not reach the address', () {
    final a = address(graph(one('int facet units "cents" facet currency "EUR"')));
    expect(address(graph(one('int facet currency "EUR" facet units "cents"'))), a);
    expect(
      address(graph(one('int facet units "cents" facet currency "EUR" facet units "cents"'))),
      a,
    );
    expect(address(graph(one('int facet units "cents" facet currency "USD"'))), isNot(a));
    expect(address(graph(one('int facet units "cents"'))), isNot(a));
  });

  test('one set of integers has one address', () {
    // The odd quarter-steps from 1 to 9, spelled three ways.
    final a = address(graph(one('int in [0..=10] class 1 mod 4')));
    expect(address(graph(one('int in [1..=9] class 1 mod 4'))), a);
    expect(address(graph(one('int set {1, 5, 9}'))), a);
    expect(address(graph(one('int set {1, 5}'))), isNot(a));
    // No facts and the facts every integer meets are one domain.
    expect(address(graph(one('int'))), address(graph(one('int in [..]'))));
  });

  test('values reach the address', () {
    final a = address(graph(discount));
    for (final (from, to) in [
      ('prim -', 'prim +'),
      ('(r.0/0^1, r.0/0^0)', '(r.0/0^0, r.0/0^1)'),
      ('(int; int in [0..] hint', '(int; int in [1..] hint'),
      ('#some(off), #none', '#some(off), #_'),
      ('r results (r.0^0)', 'r results (r.0^0, 0)'),
    ]) {
      expect(address(with_(from, to)), isNot(a), reason: '$from -> $to');
    }
    Region port(String p) => graph(
      'zir 1\nr region port (state $p)\nr.0 port read $p (r^0) -> (String; state $p)\nr results (r.0^1)\n',
    );
    expect(address(port('in')), isNot(address(port('keys'))));
  });

  test('the normal form', () {
    final g = graph(discount);
    final n = canonicalize(g);
    expect(sameGraph(canonicalize(n), n), isTrue);
    final r = ranks(n);
    expect([r[0], r[1], r[3]], [0, 0, 0]);
    // The binder is renamed to level 0, and every hint, its written name's among them, is gone.
    expect(pattern((n.nodes[0].op as MatchOp).patterns[0]), '#some(\u{0}0)');
    expect((n.nodes[0].regions[0].args[0] as ValueEdge).facets, isEmpty);
    // The normal form is what the binary form carries, and it reads back.
    expect(sameGraph(decode(encode(n)), n), isTrue);
    expect('${address(g)}', hasLength(64), reason: '64 lowercase hex digits');
  });

  test('the address is pinned', () {
    // The binary form fixes its own layout (little-endian 64-bit words, floats by their
    // IEEE-754 bits, big numbers in decimal), so this hash is the same on every machine.
    expect(
      '${address(graph(discount))}',
      '800ef82a27b7bce0e3dbb8d28e72373e6e875532698f89294af97adbb2847b41',
    );
  });

  test('every NaN is one word', () {
    const nanConst =
        'zir 1\nr region function ()\nr.0 prim tuple (nan, 1.5) -> (_)\nr results (r.0^0)\n';
    // A NaN with another payload reads as the one NaN, and is written as the fixed word.
    final word = [for (var i = 0; i < 8; i++) (nanBits >> (8 * i)) & 0xff];
    final bytes = encode(graph(nanConst));
    final at = Iterable<int>.generate(bytes.length - 7)
        .firstWhere((i) => Iterable<int>.generate(8).every((j) => bytes[i + j] == word[j]));
    bytes[at] ^= 1;
    final g = decode(bytes);
    expect(encode(g)[at], word[0]);
    expect(address(g), address(graph(nanConst)));
  });
}
