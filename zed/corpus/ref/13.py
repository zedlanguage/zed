"""13 connectivity by a classic union-find (path halving, union by size):
the reference the library's certified path must agree with. Node count is
max node id on an edge + 1; a queried node outside that range is alone."""
import sys
from zedrt import read_lines
edges, qs = [], []
for l in read_lines(sys.argv[1]):
    w = l.split(' ')
    if w[0] == '?':
        qs.append((int(w[1]), int(w[2])))
    else:
        edges.append((int(w[0]), int(w[1])))
n = max((max(a, b) for a, b in edges), default=-1) + 1
parent, size = list(range(n)), [1] * n


def find(x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x


for a, b in edges:
    ra, rb = find(a), find(b)
    if ra != rb:
        if size[ra] < size[rb]:
            ra, rb = rb, ra
        parent[rb] = ra
        size[ra] += size[rb]
root = lambda x: find(x) if x < n else ('alone', x)
for a, b in qs:
    print(a, b, 'yes' if root(a) == root(b) else 'no')
print('components', len({find(v) for v in range(n)}))
