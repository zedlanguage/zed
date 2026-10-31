/// Comments:
///
/// ```peg
/// Comment      = '//' (!'\n' ANY)* | BlockComment
/// BlockComment = '/*' (BlockComment | !'*/' ANY)* '*/'
/// ```
///
/// Block comments nest, so commenting out a region that already holds one works.
library;

import '../../lex.dart';
import 'text.dart';

/// The end of the comment starting at byte `pos` of `text`, if one starts there; throws a
/// [LexError] for a block comment that is not closed.
int? comment(Text text, int pos) {
  if (text.startsWith('//', pos)) {
    final k = text.indexOf('\n', pos);
    return k < 0 ? text.length : k;
  }
  if (!text.startsWith('/*', pos)) return null;
  var depth = 0;
  // Every byte of `*/` and `/*` is ASCII, so stepping a byte at a time inside a code point
  // never matches.
  for (var i = pos; i < text.length;) {
    if (text.startsWith('/*', i)) {
      depth++;
      i += 2;
    } else if (text.startsWith('*/', i)) {
      depth--;
      i += 2;
      if (depth == 0) return i;
    } else {
      i++;
    }
  }
  throw LexError(BadComment('the block comment is not closed ($depth `*/` missing)'), (
    start: pos,
    end: text.length,
  ));
}
