"""05 maximum prefix sum: max(0, max of prefix sums), the fold with state
(sum, best) started at (0, 0), and the total."""
import sys
from zedrt import read_lines
xs = [int(l) for l in read_lines(sys.argv[1])]
pre, s = [], 0
for x in xs:
    s += x
    pre.append(s)
direct = max(0, max(pre, default=0))
s, b = 0, 0
for x in xs:
    s, b = s + x, max(b, s + x)
print(direct, b, s)
