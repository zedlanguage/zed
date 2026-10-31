#!/usr/bin/env python3
"""Writes dart/lib/src/unicode_tables.dart, the Unicode tables the Dart source loader and lexer
read (steps L1.1 and L1.2), from a copy of the Unicode Character Database: each code point's
canonical combining class, its full canonical decomposition, the pairs that canonical
composition joins, the XID_Start and XID_Continue properties, each code point's script and
script extensions, and the code points a quoted character shows as an escape.

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

def runs(values):
    """Runs of consecutive code points with one value, as first, last, value."""
    out = []
    for cp in sorted(values):
        if out and out[-1][1] == cp - 1 and out[-1][2] == values[cp]:
            out[-1][1] = cp
        else:
            out.append([cp, cp, values[cp]])
    return out

def ranged(file, keep=lambda v: True):
    """The code points of each value of a file of `first..last ; value` lines."""
    out = {}
    for line in (ucd / file).read_text().splitlines():
        body = line.split("#")[0].split(";")
        if len(body) < 2:
            continue
        lo, _, hi = body[0].strip().partition("..")
        v = body[1].strip()
        if keep(v):
            for cp in range(int(lo, 16), int(hi or lo, 16) + 1):
                out[cp] = v
    return out

# A code point has many properties, so each property is read on its own.
xid_start = {cp: 1 for cp in ranged("DerivedCoreProperties.txt", lambda v: v == "XID_Start")}
xid_continue = {cp: 1 for cp in ranged("DerivedCoreProperties.txt", lambda v: v == "XID_Continue")}
# The characters a quoted character shows as `\\u{…}`: a control, private use, format or
# unassigned character, white space, a grapheme extender, or a default-ignorable character.
escaped = {cp: 1 for cp, v in ranged("extracted/DerivedGeneralCategory.txt").items()
           if v in ("Cc", "Co", "Cf", "Cn")}
for cp, v in ranged("PropList.txt", lambda v: v == "White_Space").items():
    escaped[cp] = 1
for p in ("Grapheme_Extend", "Default_Ignorable_Code_Point"):
    for cp in ranged("DerivedCoreProperties.txt", lambda v: v == p):
        escaped[cp] = 1
long = {}
for line in (ucd / "PropertyValueAliases.txt").read_text().splitlines():
    f = [x.strip() for x in line.split("#")[0].split(";")]
    if len(f) >= 3 and f[0] == "sc":
        long[f[1]] = f[2]
script_names = sorted(set(long.values()))
index = {n: i for i, n in enumerate(script_names)}
script = {cp: index[v] for cp, v in ranged("Scripts.txt").items()}
ext_sets = sorted({v for v in ranged("ScriptExtensions.txt").values()})
ext = {cp: ext_sets.index(v) for cp, v in ranged("ScriptExtensions.txt").items()}

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
    literal("xidStart", "Runs of code points with the XID_Start property, in hexadecimal: "
            "first, last, 1.", [n for r in runs(xid_start) for n in r]),
    literal("xidContinue", "Runs of code points with the XID_Continue property, in "
            "hexadecimal: first, last, 1.", [n for r in runs(xid_continue) for n in r]),
    literal("scripts", "Runs of code points of one script, in hexadecimal: first, last, and "
            "the index of the script in `scriptNames`; a code point in no run is of the script "
            "Unknown.", [n for r in runs(script) for n in r]),
    literal("scriptExtensions", "Runs of code points with one Script_Extensions value, in "
            "hexadecimal: first, last, and the index of the value in `scriptExtensionSets`; a "
            "code point in no run has its script as its only extension.",
            [n for r in runs(ext) for n in r]),
    literal("escapedInQuotes", "Runs of code points a quoted character shows as an escape, in "
            "hexadecimal: first, last, 1.", [n for r in runs(escaped) for n in r]),
    "/// The names of the scripts.\nconst scriptNames = [\n"
    + "".join(f"  '{n}',\n" for n in script_names) + "];\n",
    "/// The values of the Script_Extensions property, each a list of indexes in `scriptNames`."
    "\nconst scriptExtensionSets = [\n"
    + "".join(f"  [{', '.join(str(index[long[a]]) for a in v.split())}],\n" for v in ext_sets)
    + "];\n",
])
path = pathlib.Path(__file__).resolve().parent.parent / "dart/lib/src/unicode_tables.dart"
path.write_text(out)
print(f"Unicode {version}: {len(ranges)} class runs, {len(mapping)} decompositions, "
      f"{len(pairs) // 3} compositions, {len(script_names)} scripts, "
      f"{len(ext_sets)} extension sets")
