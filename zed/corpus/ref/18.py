"""18 windowed word frequency: window start t div 5 * 5, words case folded,
empty pieces (from double spaces) dropped, words in code-point order."""
import sys
from zedrt import read_lines
wins = {}
for l in read_lines(sys.argv[1]):
    w = l.split(' ')
    try:
        t = int(w[0])
    except ValueError:
        continue
    for x in w[1:]:
        if x != '':
            c = wins.setdefault(t // 5 * 5, {})
            c[x.lower()] = c.get(x.lower(), 0) + 1
for w in sorted(wins):
    print('%d: %s' % (w, ' '.join('%s=%d' % kv for kv in sorted(wins[w].items()))))
