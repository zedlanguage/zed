#!/usr/bin/env python3
"""Copy the `zed` fences of the spec's DESIGN.md and EXAMPLES.md into design.md and
examples.md here, each under a header naming its source line and its layer (step L1.7).

CI does not read the spec repository, so the copies are the fixtures; run this by hand after
the spec changes.  The layer is computed with the spec's grammar tools, as the M0.4 layer
checker computes a corpus program's: the lowest ring at which the fence parses (as a Unit,
or else under the documentation notation), raised to the layer of any defined word it uses
(the table of sec:grammar) and to a `// layer Lk` label.

Usage: sync.py [--check] [SPEC_DIR]   (default ../../../zed from this file; --check writes
nothing and exits 1 if a copy is out of date)
"""
import os
import re
import sys
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
args = [a for a in sys.argv[1:] if a != '--check']
SPEC = os.path.abspath(args[0] if args else os.path.join(HERE, '..', '..', '..', 'zed'))
sys.path.insert(0, os.path.join(SPEC, 'tools', 'grammar'))
import ring                                                    # noqa: E402
import layer                                                   # noqa: E402
from check import peg_fences, read_grammar, lex, parse, Parser, TOP   # noqa: E402
from fences import fences                                      # noqa: E402


def grammars():
    lexg, syng, docg = peg_fences(ring.DESIGN)[:3]
    lexrules = read_grammar(lexg)[0]
    synrules = read_grammar(syng)[0]
    allrules = dict(synrules)
    allrules.update(read_grammar(docg)[0])
    return lexrules, synrules, allrules


def label_of(line):
    """The layer a `// layer Lk` line names.  A fence's label may be on any line, since its
    first line is usually its `// [d4]` header; layer.py reads only a program's first line."""
    m = re.fullmatch(r'\s*// layer L(\d+)\b.*', line)
    return int(m.group(1)) if m else None


def layer_of(text, g):
    """(layer, ring, (word layer, word), label, doc) of a fence."""
    lexrules, synrules, allrules = g
    toks = lex(lexrules, text.replace('…', 'elided'))
    doc = False
    rules, start = synrules, 'Unit'
    if parse(rules, lexrules, toks, TOP, start)[0] is None:
        rules, start, doc = allrules, 'DocFence', True
    rng = next(k for k in range(1, TOP + 1) if parse(rules, lexrules, toks, k, start)[0] is not None)
    tree = Parser(rules, TOP, toks, False).rule(start, 0, False)[1][0]
    unit = layer.Unit.__new__(layer.Unit)
    unit.trees = [(tree, toks)]
    unit._holes(toks, lexrules, synrules)
    hits, _ = layer.analyse([unit])
    word = max(hits)[:2] if hits else (1, None)
    label = max(label_of(line) or 0 for line in text.split('\n')) or None
    return max(rng, word[0], label or 0), rng, word, label, doc


def render(path, g):
    name = os.path.basename(path)
    out = ['<!-- The `zed` fences of the spec\'s %s, copied by sync.py: do not edit. -->' % name]
    for _, line, text in fences(path):
        lay, rng, word, label, doc = layer_of(text, g)
        why = 'ring L%d, word %s, label %s' % (
            rng, 'L%d (%s)' % word if word[1] else 'none', 'L%d' % label if label else 'none')
        out += ['', '<!-- %s:%d layer L%d: %s%s -->' % (name, line, lay, why,
                                                         ', documentation notation' if doc else ''),
                '```zed', text, '```']
    return '\n'.join(out) + '\n'


def main():
    g = grammars()
    stale = 0
    for doc in ('DESIGN.md', 'EXAMPLES.md'):
        want = render(os.path.join(SPEC, doc), g)
        dest = os.path.join(HERE, doc.split('.')[0].lower() + '.md')
        have = open(dest, encoding='utf-8').read() if os.path.exists(dest) else None
        if have != want:
            stale += 1
            print('%s is %s' % (os.path.basename(dest), 'out of date' if '--check' in sys.argv else 'written'))
            if '--check' not in sys.argv:
                open(dest, 'w', encoding='utf-8').write(want)
    sys.exit(1 if stale and '--check' in sys.argv else 0)


if __name__ == '__main__':
    main()
