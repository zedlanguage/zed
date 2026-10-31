/// 20 taint demo, the fixed program: sanitize assumed to HTML-escape & < > " ' (as &amp; &lt;
/// &gt; &quot; &#39;), the corpus's stated assumption.
library;

import 'zedrt.dart';

String sanitize(String s) => s
    .replaceAll('&', '&amp;')
    .replaceAll('<', '&lt;')
    .replaceAll('>', '&gt;')
    .replaceAll('"', '&quot;')
    .replaceAll("'", '&#39;');

void main(List<String> args) {
  for (final l in readLines(args[0])) {
    print('<li>${sanitize(l)}</li>');
  }
}
