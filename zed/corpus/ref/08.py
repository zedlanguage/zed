"""08 percent-decoding fused with UTF-8 decoding: the two recurrences of the
program, run in order. hexVal of a character that is not a hex digit is 0
(indexOf gives #none, `else 0`). A byte sequence cut short by a #char or by the
end of the line is dropped; a stray continuation byte is dropped; a byte
expected as a continuation is taken as one whatever its high bits are."""
import sys
from zedrt import read_lines

HEX = '0123456789ABCDEF'


def hexval(c):
    return HEX.index(c.upper()) if c is not None and c.upper() in HEX and len(c) == 1 else 0


def decode(s):
    skip, prev = [], 0
    for i, c in enumerate(s):
        cur = 2 if c == '%' and prev == 0 else max(prev - 1, 0)
        skip.append(cur)
        prev = cur
    toks = []
    for i, c in enumerate(s):
        if (skip[i - 1] if i > 0 else 0) == 0:
            if c == '%':
                at = lambda k: s[k] if k < len(s) else None
                toks.append(('byte', hexval(at(i + 1)) * 16 + hexval(at(i + 2))))
            else:
                toks.append(('char', c))
    need, cp, out = 0, 0, []
    for kind, v in toks:
        if kind == 'char':
            need, cp = 0, 0
            out.append(v)
        elif need == 0:
            b = v
            if b < 128:
                out.append(chr(b))
            elif b < 192:
                pass
            elif b < 224:
                need, cp = 1, b % 32
            elif b < 240:
                need, cp = 2, b % 16
            else:
                need, cp = 3, b % 8
        else:
            cp = cp * 64 + v % 64
            if need == 1:
                out.append(chr(cp))
                need, cp = 0, 0
            else:
                need -= 1
    return ''.join(out)


for line in read_lines(sys.argv[1]):
    print(decode(line))
