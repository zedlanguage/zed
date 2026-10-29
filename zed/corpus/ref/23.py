"""23 join zoo. Keys in int order; a missing side prints '-'; amounts per
id are summed (group then sum). Output order: the four join blocks, then
the difference lines, then the range-split check."""
import sys
from zedrt import read_lines
o, p = {}, {}
for l in read_lines(sys.argv[1]):
    s, i, n = l.split(' ')
    d = o if s == 'O' else p
    d[int(i)] = d.get(int(i), 0) + int(n)
g = lambda d, k: str(d[k]) if k in d else '-'
for k in sorted(o):
    if k in p:
        print('inner %d %d %d' % (k, o[k], p[k]))
for k in sorted(o):
    print('left %d %d %s' % (k, o[k], g(p, k)))
for k in sorted(p):
    print('right %d %s %d' % (k, g(o, k), p[k]))
for k in sorted(set(o) | set(p)):
    print('outer %d %s %s' % (k, g(o, k), g(p, k)))
onlyL = sorted(set(o) - set(p))
onlyR = sorted(set(p) - set(o))
j = lambda ks: ' '.join(map(str, ks))
print('unpaid ' + j(onlyL))
print('unordered ' + j(onlyR))
print('symdiff ' + j(sorted(onlyL + onlyR)))
low = {k: v for k, v in o.items() if k < 10}
high = {k: v for k, v in o.items() if k >= 10}
print('rejoined ' + ('equal' if {**low, **high} == o else 'different'))
