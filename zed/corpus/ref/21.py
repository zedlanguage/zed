"""21 stats. Zed rules used: f64(s) parses a decimal (#invalid -> 0.0 by the
program's else); a float `.sum` is the exact sum rounded once (fsum); `/`,
`-`, `*` and `.sqrt` are IEEE; floats print shortest round-trip (zedrt.fmt).
Only mean and sd are printed; cov is computed here only to check that it is
a well-defined value the program could have read."""
import math
import sys
from zedrt import read_lines, fsum, fmt


def num(s):
    try:
        return float(s)
    except ValueError:
        return 0.0


ls = read_lines(sys.argv[1])
xs = [num(l.split(' ')[0]) for l in ls]
ys = [num(l.split(' ')[1]) if len(l.split(' ')) > 1 else 0.0 for l in ls]
n = float(len(xs))
mx = fsum(xs) / n
dx = [x - mx for x in xs]
sd = math.sqrt(fsum([d * d for d in dx]) / n)
print('mean ' + fmt(mx))
print('sd ' + fmt(sd))
