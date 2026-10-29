"""24 weighted pick: least i with cumul[i] > q, by bisect_right on the prefix
sums (the program's binary search must agree), or none when q >= total."""
import bisect
import itertools
import sys
from zedrt import read_lines
ls = read_lines(sys.argv[1])
w = [int(x) for x in ls[0].split(' ')]
cumul = list(itertools.accumulate(w))
total = cumul[-1] if cumul else 0
for l in ls[1:]:
    q = int(l)
    print('%d none' % q if q >= total else '%d %d' % (q, bisect.bisect_right(cumul, q)))
