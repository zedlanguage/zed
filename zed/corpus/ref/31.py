"""31 tiny typechecker, written independently of the Zed program's
structure: a classic recursive-descent-free RPN parser, a dict symbol table
with duplicate detection, and Kleene iteration of the type equations from
all-unknown. Diagnostics per declaration line, in the check-name order
cyclic, duplicate, malformed, type, unbound (code-point order of the names);
typings in name order (code-point)."""
import sys
from zedrt import read_lines

BAD = ('bad',)


def parse(l):
    w = l.split(' ')
    st = []
    for tok in w[2:]:
        if tok in ('+', '=='):
            b = st.pop() if st else BAD
            a = st.pop() if st else BAD
            st.append(('add' if tok == '+' else 'eq', a, b))
        elif tok == '?':
            e = st.pop() if st else BAD
            t = st.pop() if st else BAD
            c = st.pop() if st else BAD
            st.append(('cond', c, t, e))
        elif tok in ('true', 'false'):
            st.append(('bool',))
        else:
            try:
                int(tok)
                st.append(('num',))
            except ValueError:
                st.append(('var', tok))
    ok = len(w) > 1 and w[1] == '=' and len(st) == 1
    return w[0], (st[0] if ok else BAD)


def fv(e):
    if e[0] == 'var':
        return [e[1]]
    return [x for k in e[1:] if isinstance(k, tuple) for x in fv(k)]


def lift(a, b, ok):
    if 'error' in (a, b):
        return 'error'
    if 'unknown' in (a, b):
        return 'unknown'
    return ok


def infer(e, ty):
    k = e[0]
    if k == 'num':
        return 'int'
    if k == 'bool':
        return 'bool'
    if k == 'var':
        return ty.get(e[1], 'error')
    if k == 'bad':
        return 'error'
    xs = [infer(s, ty) for s in e[1:]]
    if k == 'add':
        return lift(xs[0], xs[1], 'int' if xs == ['int', 'int'] else 'error')
    if k == 'eq':
        return lift(xs[0], xs[1], 'bool' if xs[0] == xs[1] else 'error')
    c, a, b = xs
    return lift(c, lift(a, b, a), a if c == 'bool' and a == b else 'error')


decls = [(i + 1,) + parse(l) for i, l in enumerate(read_lines(sys.argv[1]))]
lines = {}
for line, name, e in decls:
    lines.setdefault(name, []).append(line)
defn = {line: e for line, name, e in decls}
ty = {n: 'unknown' for n in lines}
while True:
    new = {n: infer(defn[ls[0]], ty) if len(ls) == 1 else 'error' for n, ls in lines.items()}
    if new == ty:
        break
    ty = new
for n in sorted(ty):
    print('%s : %s' % (n, ty[n]))
clean = lambda x: x in lines and len(lines[x]) == 1 and ty[x] != 'error'
for line, name, e in decls:
    ls = lines[name]
    mine = len(ls) == 1
    names = fv(e)
    ub = [x for x in names if x not in lines]
    if mine and ty[name] == 'unknown':
        print('line %d: %s is cyclic' % (line, name))
    if not mine and line != ls[0]:
        print('line %d: duplicate %s (first at line %d)' % (line, name, ls[0]))
    if e == BAD:
        print('line %d: malformed %s' % (line, name))
    if mine and e != BAD and ty[name] == 'error' and all(clean(x) for x in names):
        print('line %d: type error in %s' % (line, name))
    if ub:
        print('line %d: unbound %s' % (line, ', '.join(ub)))
