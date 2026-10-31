#!/usr/bin/env python3
"""Rewrites the "Code size per file" table of RUST_VS_ZED.md: the bytes of every tracked Rust
file and, once ported, of the Dart files tools/dart_map.txt pairs with it.

dart_map.txt has one line per Dart file: `<dart path> <rust path>`, both relative to zed-impl.
Several Dart files may port one Rust file; their sizes add up in its row.

Usage: python3 -B tools/sizes.py
"""
import pathlib, re, subprocess

impl = pathlib.Path(__file__).resolve().parent.parent
rust = subprocess.run(["git", "ls-files", "*.rs"], cwd=impl, capture_output=True, text=True,
                      check=True).stdout.split()
dart = {}
for line in (impl / "tools" / "dart_map.txt").read_text().splitlines():
    if line.strip() and not line.startswith("#"):
        d, r = line.split()
        if r not in rust:
            raise SystemExit(f"dart_map.txt: no Rust file {r}")
        dart.setdefault(r, []).append(d)

def size(p):
    return (impl / p).stat().st_size

rows, rtot, dtot, rported = [], 0, 0, 0
for r in sorted(rust):
    rb = size(r)
    rtot += rb
    ds = dart.get(r, [])
    if ds:
        db = sum(size(d) for d in ds)
        dtot += db
        rported += rb
        names = "<br>".join(f"`{d.removeprefix('dart/')}`" for d in ds)
        rows.append(f"| `{r}` | {rb:,} | {names} | {db:,} | {db / rb:.2f} |")
    else:
        rows.append(f"| `{r}` | {rb:,} | | | |")

ratio = f"{dtot / rported:.2f}" if rported else ""
table = "\n".join([
    "| Rust file | bytes | Dart files | bytes | Dart / Rust |",
    "|---|---:|---|---:|---:|",
    *rows,
    f"| **all {len(rust)} Rust files** | **{rtot:,}** | | | |",
    f"| **the Rust files ported so far** | **{rported:,}** | | **{dtot:,}** | **{ratio}** |",
])
doc = impl / "RUST_VS_ZED.md"
text = doc.read_text()
text, n = re.subn(r"(<!-- sizes -->\n)(?:.*?\n)?(<!-- /sizes -->)",
                  lambda m: m.group(1) + table + "\n" + m.group(2), text, flags=re.S)
if n != 1:
    raise SystemExit("RUST_VS_ZED.md: no <!-- sizes --> block")
doc.write_text(text)
print(f"{len(rust)} Rust files, {rtot:,} bytes; ported {rported:,} -> Dart {dtot:,}")
