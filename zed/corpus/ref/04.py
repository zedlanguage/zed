"""04 running variance. Zed rules used: a float `+` scan entry is the exact
prefix sum rounded once (fsum); `/`, `*`, `-` are IEEE binary64; floats print
by the shortest round-trip rule (zedrt.fmt); "${x}" is String(x); f64(s)
reads the input text."""
import sys
from zedrt import read_lines, fmt, fsum
xs = [float(l) for l in read_lines(sys.argv[1])]
for i, x in enumerate(xs):
    n = fsum([1.0] * (i + 1))
    s1 = fsum(xs[:i + 1])
    s2 = fsum([v * v for v in xs[:i + 1]])
    m = s1 / n
    print(fmt(x), fmt(m), fmt(s2 / n - m * m))
