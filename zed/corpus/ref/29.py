"""29 late-arrival dedup, under the window rule this corpus assumes:
readings are taken in arrival order (the input's line order); the
watermark is the largest event time seen so far minus the lateness 5; a
reading is dropped (late: #drop) when its window's end, start + 10, is at or
below the watermark at its arrival. Kept readings are deduplicated per
window and id, first arrival wins (group then first). Windows print in
start order, ids in code-point order."""
import sys
from zedrt import read_lines
wins, top = {}, None
for l in read_lines(sys.argv[1]):
    i, t, v = l.split(' ')
    t, v = int(t), int(v)
    start = t // 10 * 10
    wm = None if top is None else top - 5
    top = t if top is None else max(top, t)
    if wm is not None and start + 10 <= wm:
        continue
    wins.setdefault(start, {}).setdefault(i, v)
for w in sorted(wins):
    print('%d: %s' % (w, ' '.join('%s=%d' % kv for kv in sorted(wins[w].items()))))
