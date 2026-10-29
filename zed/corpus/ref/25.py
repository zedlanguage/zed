"""25 autocorrelation over the valid range i in 0..<n - l, lags 0..=3."""
import sys
from zedrt import read_lines
xs = [int(x) for x in read_lines(sys.argv[1])[0].split(' ')]
n = len(xs)
for l in range(4):
    print('%d %d' % (l, sum(xs[i] * xs[i + l] for i in range(n - l))))
