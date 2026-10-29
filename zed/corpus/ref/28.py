"""28 precedence climbing (shunting-yard with the same pop rule) modulo
65536. Zed rule used: mod is Euclidean, which for a positive modulus is
Python's %."""
import sys
from zedrt import read_lines
M = 65536
prec = {'+': 1, '-': 1, '*': 2, '^': 3}


def apply(o, a, b):
    if o == '+':
        return (a + b) % M
    if o == '-':
        return (a - b) % M
    if o == '*':
        return (a * b) % M
    return pow(a, b, M) if b > 0 else 1


def ev(l):
    vals, ops = [], []

    def red():
        b, a = vals.pop(), vals.pop()
        vals.append(apply(ops.pop(), a, b))
    for tok in l.split(' '):
        if tok in prec:
            while ops and (prec[ops[-1]] > prec[tok] or (prec[ops[-1]] == prec[tok] and tok != '^')):
                red()
            ops.append(tok)
        else:
            vals.append(int(tok) % M)
    while ops:
        red()
    return vals[0]


for l in read_lines(sys.argv[1]):
    print('%s = %d' % (l, ev(l)))
