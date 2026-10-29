"""02 histogram. Both columns are computed independently, as the two
spellings are; rows for lengths 1..=maxLen, a missing scatter key printing 0."""
import sys
from zedrt import read_lines
words = [w for w in ' '.join(read_lines(sys.argv[1])).split(' ') if w != '']
hist_a = {}
for w in words:
    hist_a[len(w)] = hist_a.get(len(w), 0) + 1
max_len = max((len(w) for w in words), default=0)
for n in range(1, max_len + 1):
    hist_b = sum(1 for w in words if len(w) == n)
    print(n, hist_a.get(n, 0), hist_b)
