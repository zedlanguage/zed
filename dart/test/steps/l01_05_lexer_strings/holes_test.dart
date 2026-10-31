/// Step L1.5: `${…}` holes, which split a string into parts, each hole lexed into its tokens.
library;

import 'package:test/test.dart';
import 'package:zed/lex.dart';

import '../../support/support.dart';
import 'parts.dart';

void main() {
  test('a hole splits the string and holds tokens', () {
    expect(parts(r'"Hello, ${name}!"'), ['Hello, ', r'${Name("name")}', '!']);
    expect(parts(r'"${count}"'), [r'${Name("count")}']);
    expect(parts(r'"${a}${b}"'), [r'${Name("a")}', r'${Name("b")}']);
    expect(parts(r'"total ${1_000}"'), ['total ', r'${Int { radix: 10, digits: "1000" }}']);
  });

  test('a string or comment inside a hole follows its own rules', () {
    // The `}` in the inner string and the comment do not close the hole.
    expect(parts(r'"tag: ${label "}" /* } */}."'), [
      'tag: ',
      r'${Name("label") Str([Text("}")])}',
      '.',
    ]);
    // A hole inside a string inside a hole.
    expect(stringParts(r'"a ${"b ${c}"}"'), [
      const TextPart('a '),
      const Hole(
        [
          (
            tok: Str([
              TextPart('b '),
              Hole([(tok: Name('c'), span: (start: 10, end: 11))], (start: 8, end: 12)),
            ]),
            span: (start: 5, end: 13),
          ),
        ],
        (start: 3, end: 14),
      ),
    ]);
  });

  test('hole token spans index the whole file', () {
    const src = r'greeting "Hi ${who}"';
    final toks = lex(src);
    if (toks case [
      _,
      (tok: Str(parts: [_, Hole(:final tokens, :final span)]), span: final whole),
    ]) {
      expect(src.substring(span.start, span.end), r'${who}');
      expect(src.substring(tokens[0].span.start, tokens[0].span.end), 'who');
      expect(src.substring(whole.start, whole.end), r'"Hi ${who}"');
    } else {
      fail('$toks');
    }
  });

  test('a hole in a triple-quoted string may span lines and is not stripped', () {
    const src = '"""\n    id: \${\n  user // the account\n    }\n    """';
    expect(parts(src), ['id: ', r'${Name("user")}']);
  });

  test('malformed holes', () {
    expectOutput(
      'l01_05_lexer_strings',
      'malformed_holes',
      malformed([
        r'"${name"',
        r'"${x // c}"',
        '"\${x\n}"',
        r'"${"inner}"',
        r'"${x /* open }"',
        '"""\n  \${x}\n    """',
      ]),
    );
  });
}
