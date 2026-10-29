"""Helpers the reference scripts share: the Zed rules their outputs depend on.

- fmt(x): how Zed prints a value.  Floats follow DESIGN.md line 320: the
  shortest digits that round-trip, in fixed notation when the decimal exponent
  is in -6..<21 (at least one digit on each side of the point), otherwise one
  digit, a point, the remaining digits ('0' if none), 'e', and the exponent
  ('-' only when negative); special values print inf, -inf, nan.  Ints print in
  decimal; bools print true/false.
- fsum(xs): a float `+` fold or scan entry is the exact sum rounded once
  (DESIGN.md line 320), which is math.fsum.
- tree(xs, op): every other float fold uses the canonical tree of line 320.
- natural order (sec:order) for the keys these programs use: ints ascending,
  strings by code point (Python's str order), tuples lexicographically.
- read_lines(path): stdin as Lines, the lines of the input with the final
  newline not starting an extra empty line.
"""
import math
from decimal import Decimal


def fmt_float(x):
    if math.isnan(x):
        return 'nan'
    if math.isinf(x):
        return 'inf' if x > 0 else '-inf'
    if x == 0.0:
        return '-0.0' if math.copysign(1.0, x) < 0 else '0.0'
    sign, digits, exp = Decimal(repr(x)).as_tuple()
    ds = ''.join(map(str, digits)).rstrip('0') or '0'
    # repr's exponent applies to the full digit string; recompute after strip
    nd = len(digits)
    e10 = nd - 1 + exp                  # decimal exponent of the first digit
    s = '-' if sign else ''
    if -6 <= e10 < 21:
        if e10 >= 0:
            ip = ds[:e10 + 1].ljust(e10 + 1, '0')
            fp = ds[e10 + 1:] or '0'
        else:
            ip = '0'
            fp = '0' * (-e10 - 1) + ds
        return s + ip + '.' + fp
    return s + ds[0] + '.' + (ds[1:] or '0') + 'e' + str(e10)


def fmt(v):
    if isinstance(v, bool):
        return 'true' if v else 'false'
    if isinstance(v, float):
        return fmt_float(v)
    return str(v)


def fsum(xs):
    return math.fsum(xs)


def tree(xs, op):
    """Canonical float tree (DESIGN.md line 320) over xs in level order."""
    n = len(xs)
    if n == 0:
        raise ValueError('#empty')
    if n == 1:
        return xs[0]
    if n & (n - 1) == 0:
        h = n // 2
        return op(tree(xs[:h], op), tree(xs[h:], op))
    p = n & -n                          # largest power of two dividing n
    return op(tree(xs[:n - p], op), tree(xs[n - p:], op))


def read_lines(path):
    with open(path, encoding='utf-8') as f:
        text = f.read()
    if text == '':
        return []
    if text.endswith('\n'):
        text = text[:-1]
    return text.split('\n')


if __name__ == '__main__':
    # self-test of the printing rule and the canonical tree
    cases = [(1.0, '1.0'), (0.1, '0.1'), (-0.0, '-0.0'), (1e21, '1.0e21'),
             (1e20, '100000000000000000000.0'), (1.5e-7, '1.5e-7'),
             (1e-6, '0.000001'), (123.456, '123.456'), (2.5e-5, '0.000025'),
             (float('inf'), 'inf'), (float('nan'), 'nan')]
    for x, want in cases:
        got = fmt_float(x)
        assert got == want, (x, got, want)
    order = tree(list('abcdef'), lambda a, b: '(' + a + b + ')')
    assert order == '(((ab)(cd))(ef))', order
    print('zedrt self-test ok')
