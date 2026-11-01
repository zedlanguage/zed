/// The keys: a content hash of the parts, with the parts' boundaries in it.
library;

import 'dart:convert';

import 'package:test/test.dart';
import 'package:zed/query.dart';

List<int> b(String s) => utf8.encode(s);

void main() {
  test('equal parts give equal keys and one byte changes the key', () {
    final a = key('front', [b('x = 1;\n')]);
    expect(a, key('front', [b('x = 1;\n')]));
    expect(a, isNot(key('front', [b('x = 2;\n')])));
    expect(a, isNot(key('row', [b('x = 1;\n')])));
    // Names of one length differ in their bytes, not only in their length prefix.
    expect(key('row', [b('x')]), isNot(key('run', [b('x')])));
  });

  test("the parts' boundaries are hashed", () {
    expect(key('row', [b('ab'), b('c')]), isNot(key('row', [b('a'), b('bc')])));
    expect(key('row', [b('ab')]), isNot(key('row', [b('ab'), b('')])));
  });
}
