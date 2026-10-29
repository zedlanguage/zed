"""16 game tick: per tick, each player's moves are summed first (the
reducer's coalescing), then applied once and clamped to 0..=10. Players
start at 5 and are listed in name order; one line per tick 0..=last."""
import sys
from zedrt import read_lines
evs = [l.split(' ') for l in read_lines(sys.argv[1])]
moves = {}
for t, p, dx in evs:
    moves[int(t), p] = moves.get((int(t), p), 0) + int(dx)
players = sorted({p for _, p, _ in evs})
last = max((int(t) for t, _, _ in evs), default=-1)
pos = {p: 5 for p in players}
for t in range(last + 1):
    pos = {p: min(10, max(0, x + moves.get((t, p), 0))) for p, x in pos.items()}
    print(t, ' '.join('%s=%d' % (p, pos[p]) for p in players))
