#!/bin/bash
# The checks a branch passes before it is pushed to main (MERGE-import-cycle-check,
# MERGE-dependent-groups). Usage, from a checkout's root, through zrun:
#   /home/luke/Work/wt/zrun tools/merge_check.sh [--base <rev>] [--list | --groups] [jobs]
# It takes the files the branch changes since its merge base with <rev> (origin/main by default;
# fetch first), and
#  1. when a file under crates/<crate>/src changed: adds the group s_01f_import_graph to the
#     tests below. It runs the import graph checker, `zed_tools::imports::run`, the function the
#     binary `zed-tools --bin imports` calls, over the src of every crate with no KNOWN_CYCLES
#     entry, and fails on any cycle not in KNOWN_CYCLES. The binary is not built here: `cargo run
#     -p zed-tools` (or `cargo build --workspace --bin imports`) gives the compiler crates other
#     features than the test build, recompiles them and overwrites the dylibs every test binary
#     loads (measured 2026-11-16: 15 workspace crates Dirty), and a release build is cold in a
#     new worktree, since the central build has no release profile;
#  2. runs, with tools/run_tests.sh --only, every test group of every workspace package that
#     depends on a changed package, directly or through others, and of the changed packages
#     themselves. The packages and their dependencies come from `cargo metadata`; nothing is
#     listed by hand. A file belongs to the package whose directory holds it most deeply, except
#     a file in the directory of a [[test]] target's main file other than the package's root or
#     src (tests/steps/<step>/), which selects that test target alone: no package depends on a
#     [[test]] target, so a change there reaches nothing else. A file
#     that a Rust source names in `#[path = "…"]`, `include!("…")`, `include_str!("…")` or
#     `include_bytes!("…")` counts as a change to that source too (tests/src/seed.rs is compiled
#     into the unit tests of seven crates, zed/grammar/*.peg into zedc-syntax), to a fixed point.
#     A change to Cargo.toml, Cargo.lock, .cargo/ or rust-toolchain* selects every package.
#     A group is the test binary of a target with `test = true` and no required features (so not
#     tests/full, which needs --full): a lib's or bin's unit tests, named after the target, and
#     each [[test]]; a selected group g selects the piece short-g too, where one exists (the
#     short-addresses build of l01_37a_short_addresses and l01_37_oracle).
# It exits 0 when every check passes or nothing needs one (a change to docs alone), 1 otherwise.
# --groups prints the selection and stops; --list also passes it to tools/run_tests.sh --list,
# which builds it and prints the pieces. Neither runs a test. jobs is passed to tools/run_tests.sh (default 6), whose pieces each keep its limit.
# Tracked files must be committed: the check is of HEAD, not of the working tree.
# Not covered: files that tests read at run time outside the package that holds them (the plan
# docs/plan_dag.md, read by l01_26_type_resolution::op_table; tools/run_tests.sh, read by the
# zed_tests unit tests), and tests/full.
# Cost: one `cargo metadata --no-deps`, one grep over the workspace's .rs files for the include
# forms, and a closure over the package graph, O(packages + edges) per round; the tests dominate.
# A change to a compiler crate selects nearly every group, since zedc, zed-tools, zed-native and
# zed-tests all depend on the compiler crates.
base=origin/main list= groups_only= jobs=6
while [ $# -gt 0 ]; do
  case $1 in
    --base) base=$2; shift ;;
    --list) list=--list ;;
    --groups) groups_only=1 ;;
    [0-9]*) jobs=$1 ;;
    *) echo "usage: tools/merge_check.sh [--base <rev>] [--list | --groups] [jobs]" >&2; exit 2 ;;
  esac
  shift
done
[ -x tools/run_tests.sh ] || { echo "run from a checkout's root" >&2; exit 2; }
if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
  echo "merge check: tracked files have uncommitted changes; commit them first" >&2
  exit 1
fi
mb=$(git merge-base "$base" HEAD) || { echo "merge check: no merge base with $base" >&2; exit 1; }
mapfile -t changed < <(git diff --name-only "$mb" HEAD)
echo "merge check: ${#changed[@]} files changed since $(git rev-parse --short "$mb") ($base)"
[ ${#changed[@]} -gt 0 ] || exit 0

meta=$(cargo metadata --no-deps --format-version 1 -q) || { echo "merge check: cargo metadata failed" >&2; exit 1; }
wsroot=$(jq -r .workspace_root <<<"$meta")
# Each workspace package as `<dir relative to the root> <name>`, deepest directories first.
mapfile -t pkgdirs < <(jq -r --arg r "$wsroot/" '.packages[] |
  "\(.manifest_path | ltrimstr($r) | rtrimstr("Cargo.toml") | rtrimstr("/")) \(.name)"' <<<"$meta" |
  awk '{ print length($1), $0 }' | sort -rn | cut -d' ' -f2-)
# Each directory that holds a [[test]] target's main file, apart from its package's root and
# src, as `<dir> <group>`: a file there is a change to those test targets alone, which no package
# depends on (tests/steps/<step>/ in zed-tests).
mapfile -t testdirs < <(jq -r --arg r "$wsroot/" '.packages[] | (.manifest_path | ltrimstr($r)
  | rtrimstr("Cargo.toml") | rtrimstr("/")) as $p | .targets[] | select(.kind == ["test"] and .test
  and ((.["required-features"] // []) == [])) | (.src_path | ltrimstr($r) | sub("/[^/]*$"; "")) as $d
  | select($d != $p and $d != ($p + "/src") and $d != ($p | if . == "" then "src" else . end))
  | "\($d) \(.name | gsub("-"; "_"))"' <<<"$meta")

# The include forms: one grep over the workspace's Rust sources, as `<source> <named path>` with
# the path resolved against the source's directory and, for #[path] in a file that is not
# lib.rs, main.rs or mod.rs, against its own module directory too.
# A #[path] inside inline modules is relative to that directory followed by the inline modules'
# names (the Rust reference, "The path attribute"), which a grep cannot see. So for a #[path]
# whose path is `../` m times and then `rest`, under the base B (the directory, or the directory
# and the stem): with k inline modules the file is B/<k names>/rest when k >= m, and the j-th
# parent of B followed by rest, j = m - k, when k < m. The first are the files under B whose path
# ends in /rest: under_rest[rest] holds their bases B, and a changed file looks up each of its
# path's suffixes there (as many lookups as it has path components). The second, j = 1..m, are
# exact entries in includers, as is k = 0. This selects every file the attribute can name with
# any inline modules, and more only when such a file exists under B, which costs extra tests and
# never misses one. Testing each changed file against each attribute instead would cost
# O(changed files x attributes).
declare -A includers=() under_rest=()
while IFS= read -r hit; do
  src=${hit%%:*}
  lit=${hit#*\"}
  lit=${lit%%\"*}
  dir=$(dirname "$src")
  for at in "$dir/$lit" "$dir/$(basename "$src" .rs)/$lit"; do
    rel=$(realpath -m --relative-to=. "$at")
    includers[$rel]+="$src "
  done
  [[ $hit == *'#['* && $lit != /* ]] || continue
  IFS=/ read -ra parts <<<"$lit"
  m=0 kept=()
  for c in "${parts[@]}"; do
    case $c in
      '' | .) ;;
      ..) if [ ${#kept[@]} -gt 0 ]; then unset 'kept[-1]'; else m=$((m + 1)); fi ;;
      *) kept+=("$c") ;;
    esac
  done
  rest=$(IFS=/; echo "${kept[*]}")
  [ -n "$rest" ] || continue
  for b in "$dir" "$dir/$(basename "$src" .rs)"; do
    b=$(realpath -m --relative-to=. "$b")
    under_rest[$rest]+="$b|$src "
    up=
    for ((j = 1; j <= m; j++)); do
      up+=../
      includers[$(realpath -m --relative-to=. "$b/$up$rest")]+="$src "
    done
  done
done < <(command grep -a -rnoE --include='*.rs' '(#\[path *= *"[^"]+"|include(_str|_bytes)?!\("[^"]+")' \
  $(printf '%s\n' "${pkgdirs[@]}" | cut -d' ' -f1 | command grep -a . | sort -u) | cut -d: -f1,3-)
# The sources whose #[path] can name the file $1 through inline modules: for each suffix s of its
# path after a /, or the whole path, each base B in under_rest[s] that the path starts with,
# followed by at least the separator (B/<names>/s, no names allowed).
inline_includers() {
  local f=$1 s=$1 e b
  while :; do
    for e in ${under_rest[$s]}; do
      b=${e%%|*}
      if [ "$b" = . ] || { [[ $f == "$b"/* ]] && [ $((${#b} + 1 + ${#s})) -le ${#f} ]; }; then
        echo "${e#*|}"
      fi
    done
    [[ $s == */* ]] || break
    s=${s#*/}
  done
}

declare -A seen=() pkgs=() direct=()
crate_srcs=() all=
queue=("${changed[@]}")
while [ ${#queue[@]} -gt 0 ]; do
  f=${queue[0]}
  queue=("${queue[@]:1}")
  [ -n "${seen[$f]}" ] && continue
  seen[$f]=1
  case $f in
    Cargo.toml | Cargo.lock | .cargo/* | rust-toolchain*) all=1 ;;
  esac
  if [[ $f =~ ^crates/([^/]+)/src/ ]] && [[ " ${crate_srcs[*]} " != *" crates/${BASH_REMATCH[1]}/src "* ]]; then
    [ -d "crates/${BASH_REMATCH[1]}/src" ] && crate_srcs+=("crates/${BASH_REMATCH[1]}/src")
  fi
  hit=
  for td in "${testdirs[@]}"; do
    if [[ $f == "${td%% *}"/* ]]; then
      direct[${td#* }]=1
      hit=1
    fi
  done
  for pd in "${pkgdirs[@]}"; do
    [ -n "$hit" ] && break
    d=${pd%% *}
    if [ -z "$d" ] || [[ $f == "$d"/* ]]; then
      # The root manifest's own package, if any, owns only what no member holds.
      [ -n "$d" ] && pkgs[${pd#* }]=1
      break
    fi
  done
  for s in ${includers[$f]} $(inline_includers "$f"); do queue+=("$s"); done
done

[ ${#crate_srcs[@]} -gt 0 ] && echo "merge check: changed crate sources ${crate_srcs[*]}: s_01f_import_graph runs the imports tool over every crate"
# The changed packages and every package that depends on one of them, by any kind of dependency.
selected=$(jq -r --arg all "$all" --arg seed "${!pkgs[*]}" '
  [.packages[].name] as $members
  | (if $all == "1" then $members else ($seed | split(" ") | map(select(. != ""))) end) as $start
  | [.packages[] | {name, deps: [.dependencies[].name | select(. as $d | $members | index($d))]}] as $g
  | {set: $start, todo: $start}
  | until(.todo == [];
      .todo as $t | .set as $s
      | ([$g[] | select(.name as $n | ($s | index($n) | not)) | select(any(.deps[]; . as $d | $t | index($d))) | .name]) as $new
      | {set: ($s + $new), todo: $new})
  | .set | unique | join(" ")' <<<"$meta")
echo "merge check: changed packages: ${!pkgs[*]}${all:+ (a workspace file: all)}"
echo "merge check: with their dependents: $selected"

groups=$(jq -r --arg sel " $selected " '.packages[] | select(.name as $n | $sel | contains(" \($n) "))
  | .targets[] | select(.test and ((.["required-features"] // []) == [])
                        and (.kind | index("custom-build") or index("example") or index("bench") | not))
  | .name | gsub("-"; "_")' <<<"$meta")
[ ${#direct[@]} -gt 0 ] && echo "merge check: test targets changed alone: ${!direct[*]}"
groups+=$'\n'$(printf '%s\n' "${!direct[@]}")
[ ${#crate_srcs[@]} -gt 0 ] && groups+=$'\ns_01f_import_graph'
# A test target built with the feature short-addresses runs as the piece short-<group> too.
groups=$(command grep -a . <<<"$groups" | sort -u)
[ -n "$groups" ] && groups+=$'\n'$(sed 's/^/short-/' <<<"$groups")
groups=$(command grep -a . <<<"$groups" | sort -u | paste -sd'|')
if [ -z "$groups" ]; then
  echo "merge check: no package changed; no tests to run"
  exit 0
fi
echo "merge check: groups: ${groups//|/ }"
[ -n "$groups_only" ] && exit 0
tools/run_tests.sh --only "^($groups)\$" $list "$jobs" || { echo "merge check: FAILED: tests (above)" >&2; exit 1; }
echo "merge check: passed"
