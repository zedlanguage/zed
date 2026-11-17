#!/bin/bash
# The checks a branch passes before it is pushed to main (MERGE-import-cycle-check,
# MERGE-dependent-groups, MERGE-push-race). Usage, from a checkout's root, through zrun:
#   /home/luke/Work/wt/zrun tools/merge_check.sh [--base <rev>] [--record <file>] [--reads <dir>] [--list | --groups] [jobs]
# It takes the files the branch changes since its merge base with <rev> (origin/main by default;
# fetch first), both paths of a rename, and
#  0. when tools/merge_check.sh, tools/test_merge_check.sh or tools/run_tests.sh changed: runs both
#     parts of tools/test_merge_check.sh, select and record, at once, each under the limit of a
#     piece of tools/run_tests.sh (max(20, 20 × load / cores) s), and fails if either fails
#     (MERGE-tools-self-tests). They test this script on a toy workspace, about 12 s each;
#     tools/run_tests.sh is in the list because this script's cases depend on its --only and
#     --trace, which the toy's stub imitates. Their result is not recorded: they run on every
#     check of such a branch;
#  1. when a file under crates/<crate>/src changed: adds the group s_01f_import_graph to the
#     tests below. It runs the import graph checker, `zed_tools::imports::run`, the function the
#     binary `zed-tools --bin imports` calls, over the src of every crate with no KNOWN_CYCLES
#     entry, and fails on any cycle not in KNOWN_CYCLES. The binary is not built here: `cargo run
#     -p zed-tools` (or `cargo build --workspace --bin imports`) gives the compiler crates other
#     features than the test build, recompiles them and overwrites the dylibs every test binary
#     loads (measured 2026-11-16: 15 workspace crates Dirty; in a worktree with build/LIBHASH it
#     writes a second set of dylibs instead, see zrun, at the same cost), and a release build is
#     cold in a new worktree, since the central build has no release profile;
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
#     The pieces of the full battery are groups too, each named full-<piece> after its folder
#     tests/full/<piece>/, as tools/run_tests.sh names them. A file under tests/full/<piece>/
#     selects that piece alone, and any other file under tests/full/ (main.rs) every piece
#     (MERGE-runtime-inputs). All pieces are one test binary, built in the package whose [[test]]
#     target's main file lies in tests/full/ (zed-tests), so when that package is selected (a
#     change to it, or to any package it depends on, a compiler crate) every piece is selected
#     (MERGE-full-by-dependency). The pieces run after the local groups, in a call of their own,
#     tools/run_tests.sh --full --only, and are recorded and mapped (2a, 3) as the local groups
#     are; the messages name them apart, as tests/full pieces;
#  2a. with --reads <dir>: adds every group whose pieces read at run time a path the branch's
#     change can affect, by the rule of "The record" below, from the map <dir>/<group>.reads (a
#     line `commit <sha>`, the commit it was traced at, then the paths the group's pieces named),
#     and names the groups and tests/full pieces of the workspace the map has no file for (new
#     since, or never traced with --record). A change to docs/plan_dag.md alone so selects l01_26_type_resolution and
#     m0_03_grammar_tools, which read it, where by compilation it selects nothing. After a passing
#     run with --record, each group that ran gets its map file written again from the trace. The
#     map is shared by every worktree (merge-push.sh passes /home/luke/Work/wt/merge-reads), so a
#     group's entry is from the last check that ran it, at whichever commit; a group whose reads
#     changed since can be missed until it runs again, and step 3 below covers the groups of the
#     record from their own trace. Cost: one pass over the map, O(map size) (2.3 MB for 280
#     groups);
#  3. with --record <file>: runs the tests under tools/run_tests.sh --trace, and when they pass
#     writes to <file> the commit checked, the groups that passed and the paths each group's
#     pieces read at run time. A later run with the same <file>, after the branch is rebased on a
#     main that moved (tools/../wt/merge-push.sh does this after a refused push), runs only the
#     selected groups that did not pass then or whose inputs changed since; see "The record".
# It exits 0 when every check passes or nothing needs one (a change to docs alone), 1 otherwise.
# --groups prints the selection, and with --record what would run, and stops; --list also passes
# the selection to tools/run_tests.sh --list, which builds it and prints the pieces. Neither runs a
# test or writes the record. jobs is passed to tools/run_tests.sh (default 6), whose pieces each
# keep its limit.
# Tracked files must be committed: the check is of HEAD, not of the working tree.
# Not covered: without --reads, files that tests read at run time outside the package that holds
# them (the plan docs/plan_dag.md, read by l01_26_type_resolution::op_table; tools/run_tests.sh,
# read by the zed_tests unit tests), which step 2a selects by. Step 3 covers them for the groups
# of the record.
# Cost: one `cargo metadata --no-deps`, one grep over the workspace's .rs files for the include
# forms, and a closure over the package graph, O(packages + edges) per round; the tests dominate.
# A change to a compiler crate selects nearly every group, since zedc, zed-tools, zed-native and
# zed-tests all depend on the compiler crates.
#
# The record. Let T_old be the commit whose check passed, S_old the groups that passed there, H
# the commit checked now, M its base, S_new the groups the files changed from M to H select, and
# D the files that differ between T_old and H (`git diff T_old H`, which holds every change main
# brought in by the rebase and every change made while resolving it). A group g of S_new runs
# again unless g is in S_old and g is not touched by D: no file of D is selected by step 2 to g
# (a file g is compiled from, by package, include form or workspace file); no file of D is a path
# g's pieces named at run time at T_old; no directory they named (listed, opened or stat'ed), the
# root included, gained or lost an entry or saw one change type: the parent directory of each file
# of D that was added, deleted or changed type, and, going up, the parent of each directory that
# came into or went out of existence with it (git tracks no empty directory, so a directory
# exists at a commit when a tracked file lies under it there); and they read
# nothing the trace could not name (`*`: a relative path in a call strace shows without its
# directory, or .git, whose answers change with every commit). Proof that skipping such a g is
# sound: g's test binaries are built from files step 2 maps to g, none of which differs between
# T_old and H, so they are the same programs. Each piece, deterministic given its binary, its
# environment and what its file system calls return, made at T_old only the calls the trace
# shows. A call's result depends only on the paths it names: for a file, its content, mode and
# whether it exists; for a directory, whether it exists and, when listed, the names in it and
# their types, which change only when an entry directly in it is added, deleted or changes type
# (a rename is both, with --no-renames); a file deeper down is named by its own path when it is
# read, and changes a directly held entry only when it creates or removes the directories above
# it. Until MERGE-runtime-inputs this rule took every directory above such a file, the root
# included, so a new docs/<file>.md re-ran the 51 groups (of 280, 2026-11-16) that stat the root.
# No such change happened to any path a piece named, so at H it makes the same calls with the same
# results and passes as it passed at T_old. Symbolic links would break the step "a file's content
# is read through its own path", so a HEAD that tracks one runs every group. Not covered by this
# proof: a test whose result depends on something other than its inputs (time, a random seed it
# draws itself, the load), which can fail on any run; and changes outside the checkout (the
# toolchain installed, the system's libraries), which step 2 does not cover either. A change
# under tools/ (the test runner itself) since T_old runs every group of S_new. A group not in
# S_new is not run, as in step 2: its compiled inputs at H are those at M, where main's own
# check passed it (its run-time reads are the gap MERGE-runtime-inputs names, above).
# Tracing adds about 40 ms to each piece (measured on 384 pieces; see tools/run_tests.sh
# --trace), some 100 s of piece time over a check of 2,500 pieces, against a full check of 7 to
# 10 minutes saved each time a push is refused and the new commits on main touch no group run.
# Reading the tests' sources for the files they open was the other way: it costs nothing at run
# time but cannot see a walk of a directory or a name made at run time (fences.rs's root(),
# zed-tools' impl_root(), one_engine's walk of the checkout), so it would skip groups unsoundly.
# The record is written only after a pass on a clean, unmoved HEAD, and is
# read only when it ends with its last line `end`, so a run stopped while writing it leaves a
# record that is ignored, which runs every selected group.
base=origin/main list= groups_only= jobs=6 record= reads=
usage="usage: tools/merge_check.sh [--base <rev>] [--record <file>] [--reads <dir>] [--list | --groups] [jobs]"
while [ $# -gt 0 ]; do
  case $1 in
    --base) base=$2; shift ;;
    --record)
      [ -n "$2" ] || { echo "$usage" >&2; exit 2; }
      record=$2
      shift
      ;;
    --reads)
      [ -n "$2" ] || { echo "$usage" >&2; exit 2; }
      reads=$2
      shift
      ;;
    --list) list=--list ;;
    --groups) groups_only=1 ;;
    [0-9]*) jobs=$1 ;;
    *) echo "$usage" >&2; exit 2 ;;
  esac
  shift
done
[ -x tools/run_tests.sh ] || { echo "run from a checkout's root" >&2; exit 2; }
if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
  echo "merge check: tracked files have uncommitted changes; commit them first" >&2
  exit 1
fi
head=$(git rev-parse HEAD)
mb=$(git merge-base "$base" HEAD) || { echo "merge check: no merge base with $base" >&2; exit 1; }
# --no-renames: a file moved from one package to another changes both.
mapfile -t changed < <(git diff --no-renames --name-only "$mb" HEAD)
echo "merge check: ${#changed[@]} files changed since $(git rev-parse --short "$mb") ($base)"
[ ${#changed[@]} -gt 0 ] || exit 0
selftest=
for f in "${changed[@]}"; do
  case $f in tools/merge_check.sh | tools/test_merge_check.sh | tools/run_tests.sh) selftest=1 ;; esac
done

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
# The package the full battery is built in: the one with a target whose main file lies in
# tests/full/ (zed-tests). Its pieces are the folders tests/full/<piece>/ at HEAD.
fullpkg=$(jq -r --arg f "$wsroot/tests/full/" '.packages[] | select(any(.targets[]; .src_path
  | startswith($f))) | .name' <<<"$meta")
fullpieces=$(for d in tests/full/*/; do [ -d "$d" ] && d=${d%/} && echo "full-${d#tests/full/}"; done | sort)

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

# Prints the paths whose reads at run time a change from commit $1 to commit $2 can affect, one per
# line, given the lines `<status>\t<path>` of `git diff --no-renames --name-status $1 $2` on stdin
# (see "The record" in the header): each changed path; for a path added, deleted or changed in
# type (status A, D or T), its parent directory ("." for the root), and going up, while the
# directory just printed exists at one of the two commits and not at the other, its parent too;
# and `*`, which a read of anything matched. O(directories at $1 and $2 + changed paths × depth).
touched_keys() {
  awk 'FILENAME == ARGV[1] { o[$0] = 1; next }
       FILENAME == ARGV[2] { n[$0] = 1; next }
       { split($0, s, "\t"); p = substr($0, length(s[1]) + 2); print p
         if (s[1] == "M") next
         do { if (!sub(/\/[^\/]*$/, "", p)) p = "."; print p } while (p != "." && (p in o) != (p in n)) }
       END { print "*" }' <(git ls-tree -r -d --name-only "$1") <(git ls-tree -r -d --name-only "$2") -
}

# Sets sel to the groups that the changed files "$@" select, one per line, sorted: each local
# group g, short-g for each, and full-<piece> for each piece of tests/full; and prints how, each
# line headed "merge check$label:".
select_groups() {
  local -A seen=() pkgs=() direct=() full=()
  local crate_srcs=() all= full_all= queue=("$@") f hit td pd d s p selected groups
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
    # tests/full is one [[test]] target that needs a feature, which no package depends on.
    if [[ $f == tests/full/* ]]; then
      hit=1
      p=${f#tests/full/}
      if [[ $p == */* ]]; then full[${p%%/*}]=1; else full_all=1; fi
    fi
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

  [ ${#crate_srcs[@]} -gt 0 ] && echo "merge check$label: changed crate sources ${crate_srcs[*]}: s_01f_import_graph runs the imports tool over every crate"
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
  echo "merge check$label: changed packages: ${!pkgs[*]}${all:+ (a workspace file: all)}"
  echo "merge check$label: with their dependents: $selected"
  # The full battery is one binary of $fullpkg: a change that reaches the package reaches every
  # piece. A finer split, by what each piece's module uses, would need the crates each module
  # names, which cargo metadata does not give; not done.
  if [ -n "$fullpkg" ] && [[ " $selected " == *" $fullpkg "* ]]; then
    full_all=1
    echo "merge check$label: $fullpkg, the package tests/full is built in, is selected: every piece of tests/full"
  fi

  groups=$(jq -r --arg sel " $selected " '.packages[] | select(.name as $n | $sel | contains(" \($n) "))
    | .targets[] | select(.test and ((.["required-features"] // []) == [])
                          and (.kind | index("custom-build") or index("example") or index("bench") | not))
    | .name | gsub("-"; "_")' <<<"$meta")
  [ ${#direct[@]} -gt 0 ] && echo "merge check$label: test targets changed alone: ${!direct[*]}"
  # The pieces of tests/full selected, those whose folder exists at HEAD.
  local fullsel=$fullpieces
  [ -n "$full_all" ] || fullsel=$(for p in "${!full[@]}"; do [ -d "tests/full/$p" ] && echo "full-$p"; done | sort)
  groups+=$'\n'$(printf '%s\n' "${!direct[@]}")
  [ ${#crate_srcs[@]} -gt 0 ] && groups+=$'\ns_01f_import_graph'
  # A test target built with the feature short-addresses runs as the piece short-<group> too.
  groups=$(command grep -a . <<<"$groups" | sort -u)
  [ -n "$groups" ] && groups+=$'\n'$(sed 's/^/short-/' <<<"$groups")
  sel=$(command grep -a . <<<"$groups"$'\n'"$fullsel" | sort -u)
}

# The local groups of the groups $1 (one per line), and the pieces of tests/full among them with
# full- taken off, as a message names them: `local` prints the first, `full` the second.
part_of() {
  if [ "$1" = local ]; then
    command grep -a -v '^full-' <<<"$2" | command grep -a .
  else
    command grep -a '^full-' <<<"$2" | sed 's/^full-//'
  fi
}
# ` tests/full pieces: <pieces>` for the pieces of tests/full among the groups $1, or nothing.
full_note() {
  local p
  p=$(part_of full "$1")
  [ -z "$p" ] || echo "; tests/full pieces: $(paste -sd' ' <<<"$p")"
}

label=
select_groups "${changed[@]}"
# Step 2a: the groups of the map that read a path the branch's change can affect, among the
# groups the workspace has now (g, or short-g for a group g, or full-<piece>), and the groups it
# has no file for.
if [ -n "$reads" ]; then
  known=$(jq -r '.packages[].targets[] | select(.test and ((.["required-features"] // []) == [])
    and (.kind | index("custom-build") or index("example") or index("bench") | not))
    | .name | gsub("-"; "_")' <<<"$meta"; echo "$fullpieces")
  known=$(command grep -a . <<<"$known" | sort -u)
  mapped=$(for f in "$reads"/*.reads; do [ -f "$f" ] && basename "$f" .reads; done | sort -u)
  rsel=
  if [ -n "$mapped" ]; then
    rsel=$(git diff --no-renames --name-status "$mb" HEAD | touched_keys "$mb" HEAD |
      awk 'NR == FNR { k[$0] = 1; next } FNR > 1 && ($0 in k) { g = FILENAME; sub(/.*\//, "", g)
           sub(/\.reads$/, "", g); print g; nextfile }' - "$reads"/*.reads |
      awk 'NR == FNR { k[$0] = 1; next } ($0 in k) || (/^short-/ && (substr($0, 7) in k))' <(echo "$known") - | sort -u)
  fi
  r=$(part_of local "$rsel")
  echo "merge check: groups that read at run time a path the change can affect (map $reads):${r:+ $(paste -sd' ' <<<"$r")}$(full_note "$rsel")"
  uncovered=$(comm -23 <(echo "$known") <(echo "$mapped") | command grep -a .)
  u=$(part_of local "$uncovered")
  [ -z "$u" ] || echo "merge check: the map has no reads of $(wc -l <<<"$u") groups, which only compilation selects: $(paste -sd' ' <<<"$u")"
  u=$(part_of full "$uncovered")
  [ -z "$u" ] || echo "merge check: the map has no reads of $(wc -l <<<"$u") tests/full pieces, which only compilation selects: $(paste -sd' ' <<<"$u")"
  sel=$(command grep -a . <<<"$sel"$'\n'"$rsel" | sort -u)
fi
if [ -z "$sel" ] && [ -z "$selftest" ]; then
  echo "merge check: no package changed; no tests to run"
  exit 0
fi
snew=$sel
s=$(part_of local "$snew")
echo "merge check: groups:${s:+ $(paste -sd' ' <<<"$s")}"
s=$(part_of full "$snew")
[ -z "$s" ] || echo "merge check: tests/full pieces: $(paste -sd' ' <<<"$s")"
[ -z "$selftest" ] || echo "merge check: a file tools/test_merge_check.sh tests changed: both its parts run"

# The record (see the header): `<commit>`, then `group <g>` for each group that passed there, then
# `read <g> <path>` for each path g's pieces named, relative to the root ("." for the root itself,
# "*" for a read of anything, see tools/run_tests.sh --trace), then `end`. torun is
# S_new ∩ (S_D ∪ not S_old); keep is S_old \ S_D.
torun=$snew keep=
if [ -n "$record" ] && [ -n "$snew" ]; then
  told=
  [ -f "$record" ] && [ "$(tail -n 1 "$record")" = end ] && told=$(head -n 1 "$record")
  if [ -z "$told" ]; then
    echo "merge check: no record in $record: every selected group runs"
  elif ! git cat-file -e "$told^{commit}" 2>/dev/null; then
    echo "merge check: the record's commit $told is not in this repository: every selected group runs"
  elif git ls-files -s | awk '$1 == "120000" { f = 1; exit } END { exit !f }'; then
    # The trace names the path a piece opened, not the file a symbolic link leads to, so a change
    # to that file would be missed (none is tracked as of 2026-11-16).
    echo "merge check: HEAD tracks a symbolic link: every selected group runs"
  else
    # Each line `<status> <path>`; with --no-renames the status is A, D, M or T (a change of type).
    mapfile -t dstat < <(git diff --no-renames --name-status "$told" HEAD)
    dfiles=("${dstat[@]#*$'\t'}")
    if printf '%s\n' "${dfiles[@]}" | command grep -a -q '^tools/'; then
      echo "merge check: tools/ changed since the record's commit $(git rev-parse --short "$told"): every selected group runs"
    else
      sold=$(awk '$1 == "group" { print $2 }' "$record" | sort -u)
      sd=
      if [ ${#dfiles[@]} -gt 0 ]; then
        label=" (since the record's commit $(git rev-parse --short "$told"))"
        select_groups "${dfiles[@]}"
        sd=$sel
        # The groups of the record that may read differently now: those that named a path
        # touched_keys prints for D (a file of D, whatever its change; a directory that gained or
        # lost an entry; `*`). Each such path is a key, and one pass over the record looks each
        # read up, O(|D| x depth + |record|) where testing each read against each file of D would
        # cost O(|D| x |record|).
        sd+=$'\n'$(printf '%s\n' "${dstat[@]}" | touched_keys "$told" HEAD | awk '
          NR == FNR { k[$0] = 1; next }
          $1 == "read" && (substr($0, length($2) + 7) in k) { print $2 }' - "$record")
        sd=$(command grep -a . <<<"$sd" | sort -u)
      fi
      torun=$(comm -12 <(echo "$snew") <(sort -u <(echo "$sd") <(comm -23 <(echo "$snew") <(echo "$sold")) | command grep -a .))
      keep=$(comm -23 <(echo "$sold") <(echo "$sd") | command grep -a .)
      echo "merge check: ${#dfiles[@]} files changed since the record's commit $(git rev-parse --short "$told"); passed there and not touched since: $(paste -sd' ' <<<"$keep")"
    fi
  fi
  s=$(part_of local "$torun")
  echo "merge check: to run:${s:+ $(paste -sd' ' <<<"$s")}"
  s=$(part_of full "$torun")
  [ -z "$s" ] || echo "merge check: tests/full pieces to run: $(paste -sd' ' <<<"$s")"
fi
[ -n "$groups_only" ] && exit 0
[ -z "$list" ] || record=

# Writes the record for HEAD: the groups of keep with their reads from the old record, and the
# groups of torun, which just passed, with the reads of their pieces in the trace directories
# "$@" (one for each call of run_tests.sh, which empties its directory's file groups first).
# A piece reads for each of its group, step and name that is in torun (run_tests.sh --only
# selects it by any of the three). Written to <file>.new, then moved over <file>, so a reader
# sees the old record or the new one; and only when HEAD is the commit checked and its tracked
# files are unchanged, as otherwise the record would name a commit that did not pass.
write_record() {
  if [ "$(git rev-parse HEAD)" != "$head" ] || [ -n "$(git status --porcelain --untracked-files=no)" ]; then
    echo "merge check: HEAD or its files changed during the check; the record is not written"
    return
  fi
  {
    echo "$head"
    command grep -a . <<<"$keep"$'\n'"$torun" | sort -u | sed 's/^/group /'
    {
      [ -z "$keep" ] || awk 'NR == FNR { k[$0] = 1; next } $1 == "read" && ($2 in k)' <(echo "$keep") "$record"
      [ -z "$torun" ] || awk 'NR == FNR { r[$0] = 1; next }
        { dir = FILENAME; sub(/\/groups$/, "", dir); f = $1; gsub("/", "_", f); f = dir "/" f ".reads"
          for (i = 1; i <= 3; i++) if ($i in r && !seen[$i]++) gs[n++] = $i
          while ((getline p < f) > 0) for (j = 0; j < n; j++) print "read " gs[j] " " p
          close(f); n = 0; delete seen }' <(echo "$torun") "${@/%//groups}"
    } | sort -u
    echo end
  } >"$record.new" && mv "$record.new" "$record"
  echo "merge check: record of $(git rev-parse --short "$head") written to $record"
}

# Writes the map file <reads>/<g>.reads of each group g of torun from the record just written, in
# place, as the record is written. A check that reads the map during the few milliseconds of the
# write can miss that group's newest paths; its step 3 still re-runs by the record's own trace.
# (Writing a new file and moving it over the old would close that window, but a script here
# never moves a file over another by a path built from variables.)
write_reads() {
  [ -n "$reads" ] && [ -n "$torun" ] && [ "$(head -n 1 "$record")" = "$head" ] || return 0
  mkdir -p "$reads" || return 0
  awk -v dir="$reads" -v head="$head" '
    NR == FNR { r[$0] = 1; print "commit " head >(dir "/" $0 ".reads"); next }
    $1 == "read" && ($2 in r) { print substr($0, length($2) + 7) >(dir "/" $2 ".reads") }' \
    <(echo "$torun") "$record" || return 0
  echo "merge check: the map's reads of $(wc -l <<<"$torun") groups written to $reads"
}

# Step 0: the toy cases of this script, each part under the limit of a piece of run_tests.sh.
if [ -n "$selftest" ] && [ -z "$list" ]; then
  slog=$(git rev-parse --path-format=absolute --git-path merge-check-self)
  read -r load _ </proc/loadavg
  limit=$(awk -v l="$load" -v c="$(nproc)" 'BEGIN { x = 20 * l / c; print (x > 20 ? int(x + 1) : 20) }')
  timeout -k 5 "$limit" tools/test_merge_check.sh select >"$slog-select.log" 2>&1 &
  p1=$!
  timeout -k 5 "$limit" tools/test_merge_check.sh record >"$slog-record.log" 2>&1 &
  p2=$!
  wait $p1
  r1=$?
  wait $p2
  r2=$?
  for part in select record; do
    [ "$part" = select ] && rc=$r1 || rc=$r2
    if [ "$rc" -ne 0 ]; then
      cat "$slog-$part.log"
      echo "merge check: FAILED: tools/test_merge_check.sh $part, rc=$rc (limit ${limit}s; log $slog-$part.log)" >&2
    fi
  done
  [ "$r1" -eq 0 ] && [ "$r2" -eq 0 ] || exit 1
  echo "merge check: tools/test_merge_check.sh select and record passed"
fi

if [ -n "$snew" ] && [ -z "$torun" ]; then
  echo "merge check: passed (every selected group passed at the record's commit, with the same inputs)"
  write_record
  exit 0
fi
# The local groups run first, then the pieces of tests/full in a call with --full, each call with
# a trace directory of its own; the record is written once both passed.
tdirs=()
for kind in local full; do
  run=$(part_of "$kind" "$torun")
  [ -n "$run" ] || continue
  trace=() full=()
  [ "$kind" = full ] && run=$(sed 's/^/full-/' <<<"$run") && full=(--full)
  if [ -n "$record" ]; then
    tdir=$(git rev-parse --path-format=absolute --git-path "merge-check-trace${full:+-full}")
    trace=(--trace "$tdir")
    tdirs+=("$tdir")
  fi
  tools/run_tests.sh "${full[@]}" --only "^($(paste -sd'|' <<<"$run"))\$" "${trace[@]}" $list "$jobs" ||
    { echo "merge check: FAILED: $([ "$kind" = full ] && echo tests/full || echo tests) (above)" >&2; exit 1; }
done
[ -z "$record" ] || [ ${#tdirs[@]} -eq 0 ] || { write_record "${tdirs[@]}"; write_reads; }
echo "merge check: passed"
