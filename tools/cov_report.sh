#!/bin/bash
# Usage: tools/cov_report.sh [--base <rev>] [--bins <dir>] <profile dir>
# Prints the coverage of a `tools/run_tests.sh --cov <profile dir>` run (TOOLS-coverage-region-
# report): region, branch and line coverage per crate and per changed file, then each region of a
# changed function that no test ran. A report only, with no threshold (DECIDE-coverage-gate):
# exit 0 when it printed, 2 on a usage error or when there is nothing to read.
#  - The profiles: every <profile dir>/*.profraw, merged by the toolchain's `llvm-profdata merge
#    -sparse` into <profile dir>/merged.profdata. The toolchain's own llvm-profdata and llvm-cov
#    (component llvm-tools, rust-toolchain.toml), since the system's are of an older LLVM that
#    refuses this compiler's raw profiles.
#  - The binaries: the executable files of <dir> (default build/cov/debug/deps, where a coverage
#    run builds) that hold a __llvm_covmap section, so only the instrumented ones.
#  - A crate: the files under crates/<name>/, or under the first two parts of any other path in
#    the checkout (tests/steps, tools/icount); files outside the checkout (the standard library,
#    the registry) are left out.
#  - Changed: the .rs files that `git diff <rev>` names (default the merge base of HEAD and
#    origin/main), so uncommitted changes count, and their changed lines, from the hunks of
#    `git diff -U0` (a hunk that only deletes marks the lines on both sides of the deletion).
#  - A changed function: one with a code region in a changed file whose lines, from its first
#    region to its last, hold a changed line. Its uncovered regions are the code regions that no
#    copy of it ran: a generic function has one copy per type, and a region counts as run when
#    any copy ran it, as llvm-cov's line counts do. Each is printed as file:line:col-line:col with
#    the first line of its function; the toolchain has no demangler, so no function name.
# Branch counts need the build flag `-Z coverage-options=branch`, which tools/run_tests.sh --cov
# adds; a build without it shows "-" for branches.
# Cost: one merge and two llvm-cov exports, the second restricted to the changed files, so its
# JSON grows with them and not with the workspace.
set -euo pipefail
base=
bins=
while [ $# -gt 0 ]; do
  case $1 in
    --base)
      base=${2:?--base needs a revision}
      shift 2
      ;;
    --bins)
      bins=${2:?--bins needs a directory}
      shift 2
      ;;
    -*)
      echo "cov_report: unknown option $1 (usage: tools/cov_report.sh [--base <rev>] [--bins <dir>] <profile dir>)" >&2
      exit 2
      ;;
    *) break ;;
  esac
done
[ $# = 1 ] || {
  echo "usage: tools/cov_report.sh [--base <rev>] [--bins <dir>] <profile dir>" >&2
  exit 2
}
prof=$1
root=$(git rev-parse --show-toplevel)
bins=${bins:-$root/build/cov/debug/deps}
tools=$(rustc --print sysroot)/lib/rustlib/x86_64-unknown-linux-gnu/bin
shopt -s nullglob
raw=("$prof"/*.profraw)
[ ${#raw[@]} -gt 0 ] || {
  echo "cov_report: no .profraw files in $prof" >&2
  exit 2
}
objs=()
for f in "$bins"/*; do
  # Not `readelf | grep -q`: grep stops at the first match, readelf then dies of SIGPIPE, and
  # pipefail makes the pipeline fail.
  [ -f "$f" ] && [ -x "$f" ] && [[ $(readelf -S -W "$f" 2>/dev/null) == *__llvm_covmap* ]] && objs+=("$f")
done
[ ${#objs[@]} -gt 0 ] || {
  echo "cov_report: no instrumented binary in $bins" >&2
  exit 2
}
merged=$prof/merged.profdata
"$tools/llvm-profdata" merge -sparse "${raw[@]}" -o "$merged"
# The -object list: llvm-cov takes the first binary bare and each other one after -object.
cov() {
  local o=(-instr-profile="$merged" "${objs[0]}")
  for f in "${objs[@]:1}"; do o+=(-object "$f"); done
  "$tools/llvm-cov" export -format=text "${o[@]}" "$@"
}
if [ -z "$base" ]; then
  base=$(git merge-base HEAD origin/main 2>/dev/null) || base=
fi
# changed: {"<relative path>": [[first, last], ...]} for each changed .rs file that exists.
changed='{}'
if [ -n "$base" ]; then
  while IFS= read -r f; do
    [ -f "$root/$f" ] || continue
    ranges=$(git -C "$root" diff -U0 "$base" -- "$f" | awk '
      /^@@/ {
        split($3, p, ","); a = substr(p[1], 2) + 0; n = (2 in p) ? p[2] + 0 : 1
        if (n == 0) { printf "[%d,%d]\n", a, a + 1 } else { printf "[%d,%d]\n", a, a + n - 1 }
      }' | jq -s -c .)
    changed=$(jq -c --arg f "$f" --argjson r "$ranges" '. + {($f): $r}' <<<"$changed")
  done < <(git -C "$root" diff --name-only "$base" -- '*.rs')
fi
summary=$(cov -summary-only)
echo "coverage per crate: regions, branches, lines (covered/total)"
jq -r --arg root "$root/" '
  def part: if .count == 0 then "-" else "\(.covered)/\(.count) \(.covered * 1000 / .count | floor / 10)%" end;
  def add(a; b): {count: (a.count + b.count), covered: (a.covered + b.covered)};
  [.data[0].files[] | select(.filename | startswith($root))
   | (.filename | ltrimstr($root) | split("/")) as $p
   | {crate: ($p[0:2] | join("/")), s: .summary}]
  | group_by(.crate)[]
  | reduce .[] as $x ({crate: .[0].crate, r: {count: 0, covered: 0}, b: {count: 0, covered: 0}, l: {count: 0, covered: 0}};
      .r = add(.r; $x.s.regions) | .b = add(.b; $x.s.branches) | .l = add(.l; $x.s.lines))
  | "  \(.crate)  regions \(.r | part)  branches \(.b | part)  lines \(.l | part)"' <<<"$summary"
if [ -z "$base" ]; then
  echo "no base revision (no origin/main): changed files not reported"
  exit 0
fi
echo "changed files against $(git -C "$root" rev-parse --short "$base"): regions, branches, lines"
if [ "$changed" = '{}' ]; then
  echo "  none"
  exit 0
fi
jq -r --arg root "$root/" --argjson ch "$changed" '
  def part: if .count == 0 then "-" else "\(.covered)/\(.count) \(.covered * 1000 / .count | floor / 10)%" end;
  [.data[0].files[] | (.filename | ltrimstr($root)) as $f | select($ch | has($f))
   | "  \($f)  regions \(.summary.regions | part)  branches \(.summary.branches | part)  lines \(.summary.lines | part)"]
  | if length == 0 then "  none built into an instrumented binary" else .[] end' <<<"$summary"
echo "uncovered regions in changed functions"
files=()
while IFS= read -r f; do files+=("$root/$f"); done < <(jq -r 'keys[]' <<<"$changed")
cov "${files[@]}" | jq -r --arg root "$root/" --argjson ch "$changed" '
  # Each code region (kind 0) of a changed file, with its function and whether any copy ran it.
  [.data[0].functions[] | . as $fn
   | [.regions[] | select(.[7] == 0) | {f: ($fn.filenames[.[5]] | ltrimstr($root)), r: .}
      | .f as $f | select($ch | has($f))] as $rs
   | ($rs | group_by(.f))[]
   | (map(.r[0]) | min) as $lo | (map(.r[2]) | max) as $hi | .[0].f as $f
   | select(any($ch[$f][]; .[0] <= $hi and .[1] >= $lo))
   | .[] | {f, at: $lo, k: (.r[0:4]), n: .r[4]}]
  | group_by([.f, .k])
  | map(select(all(.n == 0)) | .[0])
  | sort_by(.f, .k)
  | if length == 0 then "  none" else .[] | "  \(.f):\(.k[0]):\(.k[1])-\(.k[2]):\(.k[3]) (function at line \(.at))" end'
