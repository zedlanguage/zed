"""22 top-K: score descending, then name ascending (code-point order)."""
import sys
from zedrt import read_lines
es = []
for l in read_lines(sys.argv[1]):
    w = l.split(' ')
    es.append((w[0], int(w[1])))
es.sort(key=lambda e: (-e[1], e[0]))
for i, (n, s) in enumerate(es[:3]):
    print('%d %s %d' % (i + 1, n, s))
