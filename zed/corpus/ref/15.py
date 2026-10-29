"""15 spreadsheet: after each edit, every cell's value in name order
(code-point order). A term is an integer when int() reads it, else a cell
name; an empty cell is 0. #set inserts or replaces."""
import sys
from zedrt import read_lines


def value(sheet, name):
    if name not in sheet:
        return 0
    total = 0
    for t in sheet[name].split('+'):
        try:
            total += int(t)
        except ValueError:
            total += value(sheet, t)
    return total


sheet = {}
for l in read_lines(sys.argv[1]):
    parts = l.split(' = ')
    sheet[parts[0]] = parts[1] if len(parts) > 1 else '0'
    print(' '.join('%s=%d' % (c, value(sheet, c)) for c in sorted(sheet)))
