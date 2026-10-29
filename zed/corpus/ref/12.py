"""12 CYK over the bracket grammar, transcribed from the program, checked
against a direct balanced-bracket test on every substring."""
import sys
from zedrt import read_lines


def balanced(s):
    d = 0
    for c in s:
        d += 1 if c == '(' else -1 if c == ')' else 0
        if d < 0 or c not in '()':
            return False
    return d == 0 and s != ''


def cyk(s):
    n = len(s)
    t = {}
    for w in range(1, n + 1):
        for i in range(0, n - w + 1):
            if w == 1:
                t[w, i] = (False, False, s[i] == '(', s[i] == ')')
            else:
                acc = (False, False, False, False)
                for k in range(1, w):
                    x, y = t[k, i], t[w - k, i + k]
                    j = (x[2] and (y[3] or y[1]) or x[0] and y[0], x[0] and y[3], False, False)
                    acc = tuple(a or b for a, b in zip(acc, j))
                t[w, i] = acc
    return t


for line in read_lines(sys.argv[1]):
    t = cyk(line)
    whole = len(line) > 0 and t[len(line), 0][0]
    count = sum(1 for v in t.values() if v[0])
    assert whole == balanced(line)
    assert count == sum(1 for (w, i) in t if balanced(line[i:i + w]))
    print('%s %d %s' % ('balanced' if whole else 'unbalanced', count, line))
