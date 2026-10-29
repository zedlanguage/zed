"""27 parent chains: root and depth per node, nodes in code-point order."""
import sys
from zedrt import read_lines
par = {}
for l in read_lines(sys.argv[1]):
    c, p = l.split(' ')
    par.setdefault(c, p)          # group then first: the first line for a child wins
for v in sorted(par):
    r, d = v, 0
    while par.get(r, '-') != '-':
        r, d = par[r], d + 1
    print('%s %s %d' % (v, r, d))
