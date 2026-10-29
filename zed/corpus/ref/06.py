"""06 matrix multiply. Zed rules used: each product x * y is one IEEE
multiplication; the `+` reduction over a float family is the exact sum
rounded once (fsum); floats print by zedrt.fmt."""
import sys
from zedrt import read_lines, fmt, fsum
rows = [[float(t) for t in l.split(' ')] for l in read_lines(sys.argv[1])]
n, m, p = (int(t) for t in read_lines(sys.argv[1])[0].split(' '))
a = rows[1:1 + n]
b = rows[1 + n:1 + n + m]
for row in a:
    print(' '.join(fmt(fsum([row[c] * b[c][k] for c in range(m)])) for k in range(p)))
