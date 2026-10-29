"""10 HH:MM matcher. The output is the language of ([01][0-9]|2[0-3]):[0-5][0-9]
from Python's re; the script also runs the program's own algorithm
(Brzozowski derivatives, transcribed from 10-regex-matcher/regex.zed) and
stops if the two disagree on any line."""
import re
import sys
from zedrt import read_lines


def nullable(r):
    k = r[0]
    if k in ('void', 'lit', 'range'):
        return False
    if k in ('eps', 'star'):
        return True
    if k == 'seq':
        return nullable(r[1]) and nullable(r[2])
    return nullable(r[1]) or nullable(r[2])


def deriv(r, ch):
    k = r[0]
    if k in ('void', 'eps'):
        return ('void',)
    if k == 'lit':
        return ('eps',) if r[1] == ch else ('void',)
    if k == 'range':
        return ('eps',) if r[1] <= ch <= r[2] else ('void',)
    if k == 'seq':
        d = ('seq', deriv(r[1], ch), r[2])
        return ('alt', d, deriv(r[2], ch)) if nullable(r[1]) else d
    if k == 'alt':
        return ('alt', deriv(r[1], ch), deriv(r[2], ch))
    return ('seq', deriv(r[1], ch), r)


def matches(r, s):
    for c in s:
        r = deriv(r, c)
    return nullable(r)


rng = lambda a, b: ('range', a, b)
hhmm = ('seq', ('alt', ('seq', rng('0', '1'), rng('0', '9')), ('seq', ('lit', '2'), rng('0', '3'))),
        ('seq', ('lit', ':'), ('seq', rng('0', '5'), rng('0', '9'))))
pat = re.compile(r'([01][0-9]|2[0-3]):[0-5][0-9]')
for line in read_lines(sys.argv[1]):
    ok = bool(pat.fullmatch(line))
    assert ok == matches(hhmm, line), line
    print(('yes ' if ok else 'no ') + line)
