"""30 client/server, run as one process. The struct grammars are phrase
level: whitespace between elements is skipped. A parse failure reports the
farthest position any alternative reached (the same assumption as 07).
serialize writes the elements with no whitespace."""
import re
import sys
from zedrt import read_lines
prices = {'apple': 3, 'pear': 5, 'plum': 2}


def ws(s, i):
    while i < len(s) and s[i] in ' \t':
        i += 1
    return i


def lit(s, i, w):
    i = ws(s, i)
    return (i + len(w), i) if s.startswith(w, i) else (None, i)


def tok(s, i, rx):
    i = ws(s, i)
    m = re.compile(rx).match(s, i)
    return (m.end(), i, m.group()) if m else (None, i, None)


def parse(s):
    far = 0
    for kind in ('get', 'buy'):
        j, at = lit(s, 0, kind)
        if j is None:
            far = max(far, at)
            continue
        j, at, item = tok(s, j, r'[A-Za-z]+')
        if j is None:
            far = max(far, at)
            continue
        qty = None
        if kind == 'buy':
            j, at, qty = tok(s, j, r'[0-9]+')
            if j is None:
                far = max(far, at)
                continue
        j = ws(s, j)
        if j != len(s):
            far = max(far, j)
            continue
        return (kind, item, qty)
    return far


for l in read_lines(sys.argv[1]):
    r = parse(l)
    if isinstance(r, int):
        print('bad request at %d' % r)
        continue
    kind, item, qty = r
    q = 1 if kind == 'get' else int(qty)
    print('%s=%d' % (item, prices[item] * q) if item in prices else 'missing:' + item)
