#!/usr/bin/env python3
"""The M0.8 audit: which grammar alternatives and which defined words a program needs.

An alternative is needed when the program stops parsing, or parses to a different tree,
with that alternative removed from the grammar. Every alternative is tried this way, so the
list is exact for the parser of DESIGN.md sec:grammar rather than a guess from token shapes.
The defined words come from the spec's layer checker (`layer.py -v`).

Usage: audit.py SPEC_GRAMMAR_DIR PROGRAM.zed [--checklist ZED0.md]
  SPEC_GRAMMAR_DIR is the spec repository's tools/grammar. The audit runs by hand, like
  the corpus layer check (LEDGER.md), since CI does not read the spec repository.
Prints one line per needed alternative, `L<layer> <rule>#<index> <grammar text>`, then the
words, then the highest layer met. With --checklist, also checks that the checklist names
every needed alternative (as `Rule#i`) and every word (in backticks), and exits 1 if not.
"""
import os
import subprocess
import sys

sys.dont_write_bytecode = True
gdir, main = sys.argv[1], os.path.abspath(sys.argv[2])
checklist = sys.argv[4] if len(sys.argv) > 4 and sys.argv[3] == '--checklist' else None
sys.path.insert(0, gdir)
import layer  # noqa: E402
import ring  # noqa: E402
from check import LINE, TOP, lex, parse, peg_fences, read_grammar  # noqa: E402

lexg, syng = peg_fences(ring.DESIGN)[:2]
lexrules = read_grammar(lexg)[0]
synrules = read_grammar(syng)[0]
lines = [l for l in syng.split('\n') if l.strip()]
units = layer.program_units(main)
toks = [lex(lexrules, open(u, encoding='utf-8').read().replace('…', 'elided')) for u in units]
full = [parse(synrules, lexrules, t, TOP, 'Unit')[0] for t in toks]
assert all(t is not None for t in full), 'the program does not parse'

needed = []
for rule, alts in synrules.items():
    for i, (expr, lay, _) in enumerate(alts):
        trimmed = dict(synrules)
        trimmed[rule] = alts[:i] + alts[i + 1:]
        if any(parse(trimmed, lexrules, t, TOP, 'Unit')[0] != f for t, f in zip(toks, full)):
            needed.append((lay, rule, i))

# The grammar text of alternative i of a rule: the rule's i-th line, as check.py reads it.
text = {}
cur, n = None, 0
for l in lines:
    m = LINE.match(l)
    if m.group('rule'):
        cur, n = m.group('rule'), 0
    else:
        n += 1
    text[(cur, n)] = m.group('body')
for lay, rule, i in sorted(needed):
    print('L%d %s#%d %s' % (lay, rule, i, text.get((rule, i), '')[:110]))
words = subprocess.run([sys.executable, '-B', os.path.join(gdir, 'layer.py'), '-v', main],
                       capture_output=True, text=True).stdout
print(words)
print('highest grammar layer: L%d' % max(l for l, _, _ in needed))

if checklist:
    listed = open(checklist, encoding='utf-8').read()
    found = ['%s#%d' % (r, i) for _, r, i in needed]
    found += [l.split()[1] for l in words.split('\n') if l.startswith('      L')]
    missing = [w for w in found if '`%s`' % w not in listed]
    print('checklist: %d needed, %d missing %s' % (len(found), len(missing), ' '.join(missing)))
    sys.exit(1 if missing else 0)
