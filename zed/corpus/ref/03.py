"""03 edit distance, top-down memoized and bottom-up; a line with one word
gives b = "" (w[1] else ""); a line starting with a space gives a = ""."""
import sys
from functools import lru_cache
from zedrt import read_lines


def top_down(a, b):
    @lru_cache(maxsize=None)
    def go(i, j):
        if i == 0:
            return j
        if j == 0:
            return i
        return min(go(i - 1, j) + 1, go(i, j - 1) + 1,
                   go(i - 1, j - 1) + (0 if a[i - 1] == b[j - 1] else 1))
    return go(len(a), len(b))


def bottom_up(a, b):
    d = [[0] * (len(b) + 1) for _ in range(len(a) + 1)]
    for i in range(len(a) + 1):
        for j in range(len(b) + 1):
            if i == 0:
                d[i][j] = j
            elif j == 0:
                d[i][j] = i
            else:
                d[i][j] = min(d[i - 1][j] + 1, d[i][j - 1] + 1,
                              d[i - 1][j - 1] + (0 if a[i - 1] == b[j - 1] else 1))
    return d[len(a)][len(b)]


for line in read_lines(sys.argv[1]):
    w = line.split(' ')
    a = w[0] if len(w) > 0 else ''
    b = w[1] if len(w) > 1 else ''
    print(a, b, top_down(a, b), bottom_up(a, b))
