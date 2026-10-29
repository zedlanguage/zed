"""26 heat stencil. Zed rule used: div is Euclidean; the divisor here is 4
(positive), where Euclidean div equals Python's floor division."""
import sys
from zedrt import read_lines
ls = read_lines(sys.argv[1])
steps = int(ls[0])
u = [[int(x) for x in ls[1].split(' ')]]
n = len(u[0])
for t in range(1, steps + 1):
    p = u[-1]
    u.append([p[i] if i == 0 or i == n - 1 else p[i] + (p[i - 1] - 2 * p[i] + p[i + 1]) // 4
              for i in range(n)])
for t in (0, 1, 2, steps):
    print('t=%d: %s' % (t, ' '.join(map(str, u[t]))))
