"""19 bank ledger. A withdrawal above the balance turns the balance into
the failure (tx index, shortfall); a failed balance stays that failure
through later transactions (atom pass-through). Accounts print in name
order; the total and count are over the accounts whose balance is an int."""
import sys
from zedrt import read_lines
accts = {}
for t, l in enumerate(read_lines(sys.argv[1])):
    w = l.split(' ')
    kind, i = w[0], w[1] if len(w) > 1 else ''
    amt = int(w[2]) if len(w) > 2 else 0
    if kind == 'open':
        accts[i] = 0
    elif kind == 'dep' and isinstance(accts[i], int):
        accts[i] += amt
    elif kind == 'wd' and isinstance(accts[i], int):
        accts[i] = ('insufficient', t, amt - accts[i]) if amt > accts[i] else accts[i] - amt
for i in sorted(accts):
    v = accts[i]
    print('%s: insufficient at tx %d, short %d' % (i, v[1], v[2]) if isinstance(v, tuple) else '%s: %d' % (i, v))
good = [v for v in accts.values() if isinstance(v, int)]
print('total %d over %d accounts, %d failed' % (sum(good), len(good), len(accts) - len(good)))
