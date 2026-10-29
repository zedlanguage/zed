"""07 JSON parser. Implements the grammar of 07-json-parser/json.zed with the
Zed rules this output depends on:
- struct grammars skip whitespace (space, tab) between elements; token types
  (JsonStr, JsonNum, JsonLit) are exact; nothing is skipped before the first
  element or after the document's end, which must be the end of the line;
- union alternatives are tried in declared order (they are disjoint by their
  first character, so the choice rule picks the only match);
- X* sep "," is zero or more X separated by ",", no trailing separator;
- serialize writes the matched text of every token and the literal
  scaffolding, with no whitespace;
- the #syntaxError position is the farthest code-point offset at which the
  parse failed, after skipping whitespace (an assumption; see LEDGER.md).
"""
import sys
from zedrt import read_lines


class Fail(Exception):
    pass


class P:
    def __init__(self, s):
        self.s, self.far = s, 0

    def fail(self, i):
        self.far = max(self.far, i)
        raise Fail()

    def ws(self, i):
        while i < len(self.s) and self.s[i] in ' \t':
            i += 1
        return i

    def lit(self, i, t):
        if self.s.startswith(t, i):
            return i + len(t)
        self.fail(i)

    def json(self, i):
        for alt in (self.obj, self.arr, self.str_, self.num, self.kw):
            try:
                return alt(i)
            except Fail:
                pass
        self.fail(i)

    def seplist(self, i, item, close):
        out = []
        try:
            j, v = item(self.ws(i))
            out.append(v)
            i = j
            while True:
                try:
                    j = self.lit(self.ws(i), ',')
                    j, v = item(self.ws(j))
                    out.append(v)
                    i = j
                except Fail:
                    break
        except Fail:
            pass
        return self.lit(self.ws(i), close), out

    def kv(self, i):
        i, k = self.str_(i)
        i = self.lit(self.ws(i), ':')
        i, v = self.json(self.ws(i))
        return i, k + ':' + v

    def obj(self, i):
        i = self.lit(i, '{')
        i, es = self.seplist(i, self.kv, '}')
        return i, '{' + ','.join(es) + '}'

    def arr(self, i):
        i = self.lit(i, '[')
        i, es = self.seplist(i, self.json, ']')
        return i, '[' + ','.join(es) + ']'

    def str_(self, i):
        j = self.lit(i, '"')
        while j < len(self.s) and (self.s[j].isalnum() and self.s[j].isascii() or self.s[j] == ' '):
            j += 1
        j = self.lit(j, '"')
        return j, self.s[i:j]

    def num(self, i):
        j = i
        if self.s.startswith('-', j):
            j += 1
        k = j
        while k < len(self.s) and self.s[k].isdigit():
            k += 1
        if k == j:
            self.fail(k)
        if self.s.startswith('.', k):
            m = k + 1
            while m < len(self.s) and self.s[m].isdigit():
                m += 1
            if m > k + 1:
                k = m
            else:
                self.far = max(self.far, k + 1)
        return k, self.s[i:k]

    def kw(self, i):
        for w in ('true', 'false', 'null'):
            if self.s.startswith(w, i):
                return i + len(w), w
        self.fail(i)


for line in read_lines(sys.argv[1]):
    p = P(line)
    try:
        end, v = p.json(0)
        if end != len(line):
            p.fail(end)
        print(v)
    except Fail:
        print('error at %d' % p.far)
