/// The documentation's fences (step L1.7): DESIGN.md and EXAMPLES.md are the first test suite
/// (DESIGN.md Part G, "The document is the first test suite").
///
/// A fence is the text between a line ```` ```zed ```` and the next line ```` ``` ````, as
/// written, indentation included. A ✗ on a line marks the line the checker must reject; a ✗ on
/// a line that is wholly a `//` comment marks a rejected variant instead, which is left out of
/// the fence's marks and is checked as its own fixture.
library;

/// A fence and where it starts: the line of its ```` ```zed ````, counted from 1; the line just
/// before that one, which a fixture file uses for the fence's header; and the lines between the
/// delimiters, joined by `\n`.
typedef Fence = ({int line, String before, String text});

/// The fences tagged `zed` in `markdown`, in order. A fence that is never closed runs to the end
/// of the text.
List<Fence> extract(String markdown) {
  final lines = markdown.split('\n');
  final out = <Fence>[];
  for (var i = 0; i < lines.length; i++) {
    if (lines[i].trim() != '```zed') continue;
    var end = i + 1;
    while (end < lines.length && lines[end].trim() != '```') {
      end++;
    }
    out.add((
      line: i + 1,
      before: i > 0 ? lines[i - 1] : '',
      text: lines.sublist(i + 1, end).join('\n'),
    ));
    i = end;
  }
  return out;
}

/// The ✗ marks of a fence, by line within it, counted from 1: the lines the checker must
/// reject, and the lines that are wholly a comment, rejected variants each with its own
/// fixture.
typedef Marks = ({List<int> lines, List<int> variants});

/// The ✗ marks of the fence `text`.
Marks marks(String text) {
  final Marks m = (lines: [], variants: []);
  for (final (k, line) in text.split('\n').indexed) {
    if (!line.contains('✗')) continue;
    (line.trimLeft().startsWith('//') ? m.variants : m.lines).add(k + 1);
  }
  return m;
}

final _label = RegExp(r'^// layer L(\d+)(?![\p{Alphabetic}\p{N}_])', unicode: true);

/// The layer a `// layer Lk` comment line in `text` names, the highest if it names several.
int? label(String text) {
  int? best;
  for (final line in text.split('\n')) {
    if (_label.firstMatch(line.trim()) case final m?) {
      final k = int.parse(m[1]!);
      if (best == null || k > best) best = k;
    }
  }
  return best;
}
