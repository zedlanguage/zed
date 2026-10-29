"""09 equality against a canonical form: lower-case, then remove '-' and ' '."""
import sys
from zedrt import read_lines


def canon(s):
    return ''.join(''.join(s.lower().split('-')).split(' '))


for line in read_lines(sys.argv[1]):
    parts = line.split(' | ')
    a = parts[0] if len(parts) > 0 else ''
    b = parts[1] if len(parts) > 1 else ''
    print(('same: ' if canon(a) == canon(b) else 'different: ') + a + ' | ' + b)
