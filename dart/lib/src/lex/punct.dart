/// Keywords, atoms, annotations, and operators (step L1.6):
///
/// ```peg
/// AtomLit  = '#' Name
/// AnnotLit = '@' Name
/// Keyword  = KeywordWord !XID_CONTINUE
/// Operator = '->?' | '->' | '...' | '..<' | '..=' | '..' | … | [+\-*/<>=!&|\\:,;.?()\[\]{}]
/// ```
///
/// `where` and `sep` are reserved only by position, so the lexer reads them as names and the
/// parser matches them by their text.
library;

import 'text.dart';

/// The keywords, as the grammar lists them.
const keywords = [
  'struct', 'type', 'interface', 'grammar', 'matching', 'import', 'asc', 'as', 'into', 'local', //
  'for', 'in', 'not', 'loop', 'until', 'while', 'break', 'match', 'if', 'else', 'is', 'mutable',
  'positional', 'with', 'return', 'test', 'law', 'proof', 'emit', 'this', 'desc', 'div', 'mod',
  'true', 'false', 'unordered',
];

/// The operators, longest first where one is a prefix of another.
const operators = [
  '->?', '->', '...', '..<', '..=', '..', '?.', '*.', '**', '++', '<-', '<=', '>=', '><', '==', //
  '!=', '&&', '||', '::', '+', '-', '*', '/', '<', '>', '=', '!', '&', '|', r'\', ':', ',', ';',
  '.', '?', '(', ')', '[', ']', '{', '}',
];

final _keywords = keywords.toSet();

/// The keyword that is the whole of `word`, a name, if it is one.
String? keyword(String word) => _keywords.contains(word) ? word : null;

/// The operator starting at byte `pos` of `text`, if one starts there.
String? operator(Text text, int pos) {
  for (final op in operators) {
    if (text.startsWith(op, pos)) return op;
  }
  return null;
}
