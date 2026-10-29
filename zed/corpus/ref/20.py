"""20 taint demo, the fixed program: sanitize assumed to HTML-escape
& < > " ' (as &amp; &lt; &gt; &quot; &#39;), the corpus's stated assumption."""
import sys
from zedrt import read_lines


def sanitize(s):
    return (s.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
             .replace('"', '&quot;').replace("'", '&#39;'))


for l in read_lines(sys.argv[1]):
    print('<li>' + sanitize(l) + '</li>')
