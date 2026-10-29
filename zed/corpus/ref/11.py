"""11 CSV fields by a three-state quote machine, run serially (the reference
for the scan of transition tables). A comma separates when the state before
it is not 1 (inside quotes); fields are the text between separators."""
import sys
from zedrt import read_lines
NEXT = {'"': (1, 2, 1)}
OTHER = (0, 1, 0)
for line in read_lines(sys.argv[1]):
    st, before = 0, []
    for c in line:
        before.append(st)
        st = NEXT.get(c, OTHER)[st]
    seps = [i for i, c in enumerate(line) if c == ',' and before[i] != 1]
    cuts = [-1] + seps + [len(line)]
    fs = [line[cuts[k] + 1:cuts[k + 1]] for k in range(len(cuts) - 1)]
    print('%d %s' % (len(fs), ' '.join('[' + f + ']' for f in fs)))
