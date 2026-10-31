#!/usr/bin/env python3
"""Writes dart/lib/src/unicode_tables.dart, the tables of Unicode normalization the Dart source
loader reads (step L1.1), from a copy of the Unicode Character Database: each code point's
canonical combining class, its full canonical decomposition, and the pairs that canonical
composition joins.

Usage: python3 -B tools/unicode_tables.py [UCD directory, default /usr/share/unicode/ucd]
"""
import pathlib, re, sys, textwrap

ucd = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else "/usr/share/unicode/ucd")
version = re.search(r"NormalizationTest-([\d.]+)\.txt",
                    (ucd / "NormalizationTest.txt").read_text().splitlines()[0]).group(1)

ccc, mapping = {}, {}
for line in (ucd / "UnicodeData.txt").read_text().splitlines():
    f = line.split(";")
    cp = int(f[0], 16)
    if int(f[3]):
        ccc[cp] = int(f[3])
    if f[5] and not f[5].startswith("<"):
        mapping[cp] = [int(x, 16) for x in f[5].split()]

excluded = set()
for line in (ucd / "DerivedNormalizationProps.txt").read_text().splitlines():
    body = line.split("#")[0].split(";")
    if len(body) == 2 and body[1].strip() == "Full_Composition_Exclusion":
        lo, _, hi = body[0].strip().partition("..")
        excluded.update(range(int(lo, 16), int(hi or lo, 16) + 1))

def full(cp):
    return [y for x in mapping[cp] for y in (full(x) if x in mapping else [x])]

ranges = []
for cp in sorted(ccc):
    if ranges and ranges[-1][1] == cp - 1 and ranges[-1][2] == ccc[cp]:
        ranges[-1][1] = cp
    else:
        ranges.append([cp, cp, ccc[cp]])
decomp = [n for cp in sorted(mapping) for n in (cp, len(full(cp)), *full(cp))]
pairs = [n for cp in sorted(mapping) if cp not in excluded and len(mapping[cp]) == 2
         for n in (*mapping[cp], cp)]

def literal(name, doc, numbers):
    words = [format(n, "x") for n in numbers]
    lines, cur = [], ""
    for w in words:
        if len(cur) + len(w) + 1 > 90:
            lines.append(cur)
            cur = ""
        cur += w + " "
    lines.append(cur)
    body = "\n".join(f"    '{l}'" for l in lines)
    doc = "\n".join("/// " + l for l in textwrap.wrap(doc, 96))
    return f"{doc}\nconst {name} =\n{body};\n"

out = f"""// Written by tools/unicode_tables.py from the Unicode {version} character database. Do not
// edit; run the tool again for a new version of Unicode.

/// The version of Unicode the tables are of.
const unicodeVersion = '{version}';

""" + "\n".join([
    literal("combiningClasses", "Runs of code points with one nonzero canonical combining "
            "class, in hexadecimal: first, last, class.", [n for r in ranges for n in r]),
    literal("decompositions", "Each code point with a canonical decomposition, the length of "
            "its full decomposition, and that decomposition, in hexadecimal.", decomp),
    literal("compositions", "The pairs canonical composition joins, and what each pair "
            "becomes, in hexadecimal.", pairs),
])
path = pathlib.Path(__file__).resolve().parent.parent / "dart/lib/src/unicode_tables.dart"
path.write_text(out)
print(f"Unicode {version}: {len(ranges)} class runs, {len(mapping)} decompositions, "
      f"{len(pairs) // 3} compositions")
