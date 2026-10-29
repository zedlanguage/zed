"""14 single-linkage clustering to k clusters, recomputing all pairs each
step: the closest pair of points in different clusters, ties broken by
(distance², smaller label, larger label) in natural tuple order; the larger
label is renamed to the smaller. n - k merges (none if k >= n)."""
import sys
from zedrt import read_lines
lines = read_lines(sys.argv[1])
k = int(lines[0])
pts = [tuple(int(t) for t in l.split(' ')) for l in lines[1:]]
label = list(range(len(pts)))
for _ in range(max(0, len(pts) - k)):
    best = min(((pts[i][0] - pts[j][0]) ** 2 + (pts[i][1] - pts[j][1]) ** 2,
                min(label[i], label[j]), max(label[i], label[j]))
               for i in range(len(pts)) for j in range(len(pts))
               if i < j and label[i] != label[j])
    _, a, b = best
    label = [a if l == b else l for l in label]
for c in sorted(set(label)):
    print('%d: %s' % (c, ' '.join(str(i) for i, l in enumerate(label) if l == c)))
