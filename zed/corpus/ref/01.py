"""01 word count. Zed rules used: split(" ") keeps empty pieces (removed by
the where); group keys are the lower-cased words; a push of a String-keyed
map into stdout is in the keys' natural order, code-point order (sec:order)."""
import sys
from zedrt import read_lines
words = [w for w in ' '.join(read_lines(sys.argv[1])).split(' ') if w != '']
counts = {}
for w in words:
    counts[w.lower()] = counts.get(w.lower(), 0) + 1
for w in sorted(counts):
    print(w, counts[w])
