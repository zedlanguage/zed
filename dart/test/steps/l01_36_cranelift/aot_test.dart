/// The object writer shares the JIT's generator: the object file of a graph exports
/// `zed_root`, imports the runtime's hooks, and is the same bytes on every build.
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/kernel.dart';
import 'package:zed/native.dart' as native;

import 'native.dart';

Term program() =>
    let_('f', lam(['x'], prim(Prim.concat, [var_('x'), lit('!')])), app(var_('f'), [lit('hi')]));

bool contains(List<int> hay, String needle) => latin1.decode(hay).contains(needle);

void main() {
  test('the object file is reproducible and names its symbols', () {
    final (g, p) = planned(program());
    final a = native.object(g, p);
    final b = native.object(g, p);
    expect(a, b);
    for (final sym in ['zed_root', 'rt_node', 'rt_inc', 'rt_dec', 'rt_register']) {
      expect(contains(a, sym), isTrue, reason: sym);
    }
    expect(contains(a, 'rt_nonexistent'), isFalse, reason: 'the search can fail');
    expect(a.sublist(0, 4), [0x7f, ...'ELF'.codeUnits]);
  });
}
