"""17 sensor windows. Zed rules used: int() of a non-integer is #invalid,
so `else -1` and the where drop the line; the assumed window signature puts
a reading in the window starting at t div 10 * 10 (Euclidean div, t >= 0
here), windows in start order, absent when empty; groups in sensor-name
order; the output is the batch result, which the streaming plan must equal."""
import sys
from zedrt import read_lines


def num(s):
    try:
        return int(s)
    except (ValueError, TypeError):
        return -1


wins = {}
for l in read_lines(sys.argv[1]):
    w = l.split(' ')
    t = num(w[0] if len(w) > 0 else '')
    s = w[1] if len(w) > 1 else ''
    v = num(w[2] if len(w) > 2 else '')
    if t >= 0 and v >= 0:
        wins.setdefault(t // 10 * 10, {}).setdefault(s, []).append(v)
for w in sorted(wins):
    print('%d: %s' % (w, '; '.join('%s n=%d sum=%d max=%d' % (s, len(vs), sum(vs), max(vs))
                                   for s, vs in sorted(wins[w].items()))))
