/// Strings are ropes: a concatenation of two strings links them in a new cell without
/// copying, the length of a rope is counted without flattening it, and the bytes are copied
/// once, when the value leaves the program.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

import 'native.dart';

void main() {
  test('concatenation links ropes and copies once at the end', () {
    // ((("ab" ++ "cd") ++ "ef") ++ "gh"), and its length.
    var s = lit('ab');
    for (final part in ['cd', 'ef', 'gh']) {
      s = prim(Prim.concat, [s, lit(part)]);
    }
    final o = run(s);
    expect(o.value, kernel(s));
    expect((o.kernelCalls, o.stats.copied), (0, 8));
    final n = run(prim(Prim.len, [s]));
    expect('${n.value}', '8');
    expect((n.kernelCalls, n.stats.copied), (0, 0));
  });

  test('a string two uses borrow is neither counted nor copied', () {
    final t = let_(
      's',
      prim(Prim.concat, [lit('na'), lit('ïve')]),
      prim(Prim.tuple, [
        prim(Prim.len, [var_('s')]),
        prim(Prim.upper, [var_('s')]),
      ]),
    );
    final o = run(t);
    expect(o.value, kernel(t));
    expect('${o.value}', '(5, "NAÏVE")');
    // Both uses borrow the string, so its count is never written above 1; Upper runs in the
    // kernel, the one kernel call.
    expect((o.kernelCalls, o.stats.shared, o.stats.increments), (1, 0, 0));
  });

  test('a string owned twice is shared, not copied', () {
    final t = let_(
      's',
      prim(Prim.concat, [lit('ab'), lit('c')]),
      prim(Prim.tuple, [var_('s'), var_('s')]),
    );
    final o = run(t);
    expect('${o.value}', '("abc", "abc")');
    expect((o.kernelCalls, o.stats.shared, o.stats.increments), (0, 1, 1));
  });
}
