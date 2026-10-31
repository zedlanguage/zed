/// The lexing of strings at the rule of low complexity (DESIGN.md Part G).
library;

import 'package:test/test.dart';
import 'package:zed/lex.dart';

import '../../support/scaling.dart';
import 'parts.dart';

/// A `"""` string of `n` indented lines, each holding a hole.
String lines(int n) => '"""\n${[for (var i = 0; i < n; i++) '    line \${$i}\n'].join()}    """';

/// A string whose holes nest `d` deep: `"${"${…"${0}"…}"}"`.
String nested(int d) {
  var s = '0';
  for (var i = 0; i < d; i++) {
    s = '"\${$s}"';
  }
  return s;
}

void main() {
  test('a long indented string scales', () {
    // Each character was tested against every line's cut of indentation.
    check('a """ string of n lines', 1000, (n) {
      expect(parts(lines(n)), hasLength(2 * n));
    });
    final p = parts(lines(2));
    expect([p[0], p[2]], ['line ', '\nline ']);
    expect(p[1].startsWith(r'${Int') && p[3].startsWith(r'${Int'), isTrue, reason: '$p');
  });

  test('nested holes scale', () {
    // Each hole was scanned for its `}` once for each hole around it, and its text searched
    // for a line break as many times.
    check('a string with holes nested d deep', 500, (d) {
      expect(stringParts(nested(d)), hasLength(1));
    });
    expect(stringParts(nested(2)), [
      const Hole(
        [
          (
            tok: Str([
              Hole([(tok: Int(10, '0'), span: (start: 6, end: 7))], (start: 4, end: 8)),
            ]),
            span: (start: 3, end: 9),
          ),
        ],
        (start: 1, end: 10),
      ),
    ]);
  });
}
