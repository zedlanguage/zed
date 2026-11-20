#!/bin/bash
# The checks a branch passes before it is pushed to main (MERGE-import-cycle-check,
# MERGE-dependent-groups, MERGE-push-race). Usage, from a checkout's root, through zrun:
#   /home/luke/Work/wt/zrun tools/merge_check.sh [--base <rev>] [--record <file>] [--reads <dir>] [--list | --groups] [jobs]
# It takes the files the branch changes since its merge base with <rev> (origin/main by default;
# fetch first), both paths of a rename, and
#  0. when tools/merge_check.sh, tools/test_merge_check.sh, tools/run_tests.sh or
#     tools/spec_groups.sh changed: runs both
#     parts of tools/test_merge_check.sh, select and record, at once, each under the limit of a
#     piece of tools/run_tests.sh (max(20, 20 × load / cores) s), and fails if either fails
#     (MERGE-tools-self-tests). They test this script on a toy workspace, about 12 s each;
#     tools/run_tests.sh is in the list because this script's cases depend on its --only and
#     --trace, which the toy's stub imitates. Their result is not recorded: they run on every
#     check of such a branch. tools/test_lib.sh, which both test scripts source, is in this list
#     and the next;
#  0b. when tools/run_tests.sh, tools/test_run_tests.sh or tools/test_lib.sh changed: runs every
#     part of tools/test_run_tests.sh, list then select then table (select and table read the
#     table list publishes, in one log directory), and fresh, short, copy, concurrent and trace beside
#     that chain (each in a log directory of its own), each part under max(60, the piece limit) s:
#     the header of test_run_tests.sh gives each part 60 s, and list alone took 30 to 57 s at load
#     36 to 76. The parts start after the build of the tests they list, which runs first with no
#     limit, before step 0's timed parts too. Fails if the build or any part fails
#     (TOOL-merge-check-run-tests-self: until 2026-11-20 a change
#     to the test runner landed without its own tests, cc7961f67 tested by hand). Not recorded
#     either;
#  0a. when a Cargo.toml or Cargo.lock changed: fails if some workspace package, built alone
#     (`cargo tree -p <package>`, dev-dependencies included), gets a crate with features the
#     workspace build (`cargo tree --workspace`) does not give it. tools/run_tests.sh --only
#     makes the same comparison for the packages it builds and refuses on a difference, since a
#     dylib's file name does not change with its features (BUILD-clif-feature-parity: zed-clif
#     alone lacked hashbrown's defaults, so a re-check that ran without zed-clif's groups failed
#     on main). Packages one at a time suffice: Cargo's feature resolution only adds features as
#     packages join a build, so if each package alone gets the workspace's features, so does any
#     set of them. Cost: 27 runs of cargo tree, about 6 s (measured 2026-11-17). Skipped with
#     --groups and --list;
#  1. when a file under crates/<crate>/src changed: adds the group s_01f_import_graph to the
#     tests below. It runs the import graph checker, `zed_tools::imports::run`, the function the
#     binary `zed-tools --bin imports` calls, over the src of every crate with no KNOWN_CYCLES
#     entry, and fails on any cycle not in KNOWN_CYCLES. The binary is not built here: `cargo run
#     -p zed-tools` (or `cargo build --workspace --bin imports`) gives the compiler crates other
#     features than the test build, recompiles them and overwrites the dylibs every test binary
#     loads (measured 2026-11-16: 15 workspace crates Dirty; in a worktree with build/LIBHASH it
#     writes a second set of dylibs instead, see zrun, at the same cost), and a release build is
#     cold in a new worktree, since the central build has no release profile;
#  1a. runs `cargo clippy -p <package>... --all-targets -- -D warnings` on the packages step 2
#     selects: the changed packages and their dependents, as narrowed there, and each package a
#     test target of which is selected alone (a file under tests/steps/<step>/, or the narrowing's
#     targets of zed-tests), and fails on any warning (TOOLS-merge-check-clippy: two clippy errors
#     of `clippy --workspace --all-targets -D warnings` reached main this way, b67782af2 and
#     24cd9473d). A package's lints depend only on its own sources and the packages it depends
#     on (a deprecated or changed item), so the dependents cover what a change can newly warn
#     about; the narrowing of step 2 leaves out of zed-tests only targets that name none of the
#     changed packages, by that step's assumption. Not covered, as by the workspace command: the
#     pieces of tests/full, whose target needs the feature full. Cost (2026-11-20, load 50): 74 s
#     for the first run in a new worktree over 21 packages, since the central build holds no
#     clippy output, then 2 s with nothing changed; a check runs on metadata alone, so it does not
#     touch the dylibs and test binaries that step 2 builds. Run before the tests. A change to
#     the root's clippy.toml or .clippy.toml selects every package for clippy, and no test. With
#     --record, the packages whose clippy passed are recorded and skipped later by the rule of
#     "The record" (in the toy of tools/test_merge_check.sh, clippy on every run of its record
#     part took it from 12.2 to 20.6 s, over the 20 s limit at low load). Skipped with --groups
#     and --list;
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
#     short-addresses build of the groups `tools/run_tests.sh --short-groups` prints).
#     The pieces of the full battery are groups too, each named full-<piece> after its folder
#     tests/full/<piece>/, as tools/run_tests.sh names them. A file under tests/full/<piece>/
#     selects that piece alone, and any other file under tests/full/ (main.rs) every piece
#     (MERGE-runtime-inputs). All pieces are one test binary, built in the package whose [[test]]
#     target's main file lies in tests/full/ (zed-tests), so when that package is selected (a
#     change to it, or to any package it depends on, a compiler crate) every piece is selected
#     (MERGE-full-by-dependency), with one narrowing (MERGE-dep-by-target): when none of that
#     package's own files changed, it is left out of the closure, and of its targets only those
#     whose sources use a changed package are selected. Its crate names for the changed packages
#     (a dependency's rename or lib name, zed_tools) are the words; a file of its lib (tests/src)
#     uses them when its code names one, names a word that an earlier such file adds (its module
#     name, its macro_rules! macros, the types it implements traits for and does not define),
#     names `super` below such a file, or includes such a file; to a fixed point. Then each other
#     .rs file of the package that names a word is a change to its test target or tests/full
#     piece, as above, and when some lib file uses them the lib's unit tests and the packages
#     that depend on the package (zed-benches) are selected too. The package is selected whole
#     instead when the lib's root file uses them; when such a file belongs to no test target or
#     is included into another package; and when a package of the closure has a build script or,
#     in its files or those it includes, at HEAD or at the base, an attribute that puts code into
#     every binary that links it (#[no_mangle], #[export_name], #[link_section], #[used],
#     #[global_allocator], a constructor), whose effect does not depend on any name. Every
#     compiler crate reaches zed-native, which has both, so this narrows only changes to the
#     package's other dependencies, zed-tools and zed-corpus-ref (2026-11-17: a change to
#     zed-tools selects 92 groups and no tests/full piece, where it selected 222 and all 6). Not proved: that a test
#     binary's behavior depends on code of a crate it links only through the names its sources
#     name. A name built by a macro from pieces (`concat_idents!`, `paste!`), or code reached
#     only through a trait object or generic made elsewhere, would break it; the lib's files
#     that make such values name the crate and are taken. Words in strings and block comments,
#     and the type parameter of a blanket impl, only select more. A word in a `//` comment
#     (doc comments too, as no doc test runs) and a `mod <name>;` line select nothing. A
#     #[path] through inline modules in a linked package is not followed by the attribute check.
#     The pieces run after the local groups, in a call of their own,
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
#     writes to <file> the commit checked, the commit of the spec checkout (tools/spec_groups.sh
#     --commit), the groups that passed and the paths each group's pieces read at run time. A later run with the same <file>, after the branch is rebased on a
#     main that moved (tools/../wt/merge-push.sh does this after a refused push), runs only the
#     selected groups that did not pass then or whose inputs changed since; see "The record".
#     It also fails when a group whose pieces read a file of the spec checkout (spec:<path> in
#     the trace) is not one tools/spec_groups.sh names, since a change to the spec would then not
#     run it (MERGE-spec-reads-map: l01_09, l01_10 and l01_12 were missed so, and spec commit
#     1d06e2e left main red).
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
# zed-tests all depend on the compiler crates. The narrowing of step 2 adds a grep of the
# package's .rs files per round of its fixed point (3 rounds, 1 to 2 s, for a change to
# zed-tools on 2026-11-17).
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
# directory, or .git, whose answers change with every commit); and it read no file of the spec
# checkout (spec:<path>), or the spec checkout is at the commit the record names, with no
# uncommitted change to a tracked file at either check (MERGE-spec-push-check: until then a spec
# commit pushed after T_old was invisible to the record, and its groups were skipped). Proof that skipping such a g is
# sound: g's test binaries are built from files step 2 maps to g, none of which differs between
# T_old and H, so they are the same programs, except, under the narrowing of step 2, in code of
# a linked crate that g's sources do not name, on which g's behavior does not depend by that
# step's assumption (not proved). Each piece, deterministic given its binary, its
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
# By its own path: tools/test_merge_check.sh runs this script in a toy repository.
. "${BASH_SOURCE[0]%/*}/lib.sh" || exit 2
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
# The commit of the spec checkout the tests read, kept in the record (see "The record"); empty
# when unknown. A toy checkout without tools/spec_groups.sh has none.
spec_at=
[ ! -x tools/spec_groups.sh ] || spec_at=$(tools/spec_groups.sh --commit)
mb=$(git merge-base "$base" HEAD) || { echo "merge check: no merge base with $base" >&2; exit 1; }
# --no-renames: a file moved from one package to another changes both.
mapfile -t changed < <(git diff --no-renames --name-only "$mb" HEAD)
echo "merge check: ${#changed[@]} files changed since $(git rev-parse --short "$mb") ($base)"
[ ${#changed[@]} -gt 0 ] || exit 0
selftest= rtself=
for f in "${changed[@]}"; do
  case $f in tools/merge_check.sh | tools/test_merge_check.sh | tools/run_tests.sh | tools/spec_groups.sh | tools/test_lib.sh) selftest=1 ;; esac
  case $f in tools/run_tests.sh | tools/test_run_tests.sh | tools/test_lib.sh) rtself=1 ;; esac
done

meta=$(cargo metadata --no-deps --format-version 1 -q) || { echo "merge check: cargo metadata failed" >&2; exit 1; }
wsroot=$(jq -r .workspace_root <<<"$meta")
# Step 0a (header): a changed manifest or lock file.
manifest=
for f in "${changed[@]}"; do
  case $f in Cargo.toml | */Cargo.toml | Cargo.lock) manifest=1 ;; esac
done
if [ -n "$manifest" ] && [ -z "$groups_only$list" ]; then
  wsfeat=$(features_of --workspace) || { echo "merge check: cargo tree --workspace failed" >&2; exit 1; }
  bad=
  for p in $(jq -r '.packages[].name' <<<"$meta"); do
    d=$(comm -23 <(features_of -p "$p") <(echo "$wsfeat"))
    [ -z "$d" ] || bad+="  $p:"$'\n'"$(sed 's/^/    /' <<<"$d")"$'\n'
  done
  if [ -n "$bad" ]; then
    echo "merge check: a manifest or Cargo.lock changed, and these packages, built alone, get features the workspace build does not give them (tools/run_tests.sh refuses to build them so):"
    printf %s "$bad"
    echo "merge check: give each the workspace's features, as a dev-dependency"
    echo "merge check: FAILED"
    exit 1
  fi
  echo "merge check: a manifest or Cargo.lock changed: every package, built alone, gets the features the workspace build gives it"
fi
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
# For step 2's narrowing: $fullpkg's directory, the directory of its lib target's root (tests/src)
# and the lib's group (zed_tests). Without a lib and a directory of its own, there is no narrowing.
fulldir= fulllib= fulllibgroup=
if [ -n "$fullpkg" ]; then
  read -r fulldir fulllib fulllibgroup < <(jq -r --arg r "$wsroot/" --arg p "$fullpkg" '.packages[]
    | select(.name == $p) | (.manifest_path | ltrimstr($r) | rtrimstr("Cargo.toml") | rtrimstr("/")) as $d
    | [.targets[] | select(.kind | index("lib"))][0] as $l
    | select($l != null and $d != "")
    | "\($d) \($l.src_path | ltrimstr($r) | sub("/[^/]*$"; "")) \($l.name | gsub("-"; "_"))"' <<<"$meta")
fi

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
# Every path is resolved by one realpath over all of them after the loop (MERGE-selftest-time):
# the loop records each path with its source and a key (empty: includers[path] gets the source;
# a rest: under_rest[rest] gets path|source), in the order the old per-path calls made them, so
# the tables hold the same strings in the same order. A realpath, dirname and basename process
# per path cost about 55 process starts per merge_check call with the test workspace's dozen
# includes, the largest share of tools/test_merge_check.sh's time; the real workspace has about
# 60 includes, so it saves there too. realpath, not a lexical normalizer, keeps the resolution
# physical: a `..` after a symlinked directory goes where the compiler's open() goes.
declare -A includers=() under_rest=()
inc_paths=() inc_keys=() inc_srcs=()
while IFS= read -r hit; do
  src=${hit%%:*}
  lit=${hit#*\"}
  lit=${lit%%\"*}
  # dirname and basename "$src" .rs, without a process each.
  dir=. stem=$src
  [[ $src != */* ]] || dir=${src%/*} stem=${src##*/}
  [ "$stem" = .rs ] || stem=${stem%.rs}
  for at in "$dir/$lit" "$dir/$stem/$lit"; do
    inc_paths+=("$at") inc_keys+=("") inc_srcs+=("$src")
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
  printf -v rest '%s/' "${kept[@]}"
  rest=${rest%/}
  [ -n "$rest" ] || continue
  for b in "$dir" "$dir/$stem"; do
    inc_paths+=("$b") inc_keys+=("$rest") inc_srcs+=("$src")
    # The old calls resolved b first and then b/../rest; with physical resolution that is the
    # same as resolving b/../rest at once.
    up=
    for ((j = 1; j <= m; j++)); do
      up+=../
      inc_paths+=("$b/$up$rest") inc_keys+=("") inc_srcs+=("$src")
    done
  done
done < <(command grep -a -rnoE --include='*.rs' '(#\[path *= *"[^"]+"|include(_str|_bytes)?!\("[^"]+")' \
  $(printf '%s\n' "${pkgdirs[@]}" | cut -d' ' -f1 | command grep -a . | sort -u) | cut -d: -f1,3-)
if [ ${#inc_paths[@]} -gt 0 ]; then
  # xargs splits a list longer than one command line allows; realpath prints one line per path,
  # in order. A count that differs (a path with a newline) stops the check rather than misfile.
  mapfile -t inc_rels < <(printf '%s\0' "${inc_paths[@]}" | xargs -0 realpath -m --relative-to=. --)
  if [ ${#inc_rels[@]} -ne ${#inc_paths[@]} ]; then
    echo "merge check: FAILED: realpath gave ${#inc_rels[@]} paths for ${#inc_paths[@]} include paths" >&2
    exit 1
  fi
  for i in "${!inc_paths[@]}"; do
    if [ -z "${inc_keys[i]}" ]; then
      includers[${inc_rels[i]}]+="${inc_srcs[i]} "
    else
      under_rest[${inc_keys[i]}]+="${inc_rels[i]}|${inc_srcs[i]} "
    fi
  done
fi
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

# Takes the files of the array queue in turn, with the files that name each by an include form,
# and records in the arrays of select_groups, its caller, what each changes: pkgs[<package>],
# direct[<test target>], full[<piece>] or full_all for tests/full, all for a workspace file, and
# crate_srcs.
walk() {
  local f hit td pd d s p
  while [ ${#queue[@]} -gt 0 ]; do
    f=${queue[0]}
    queue=("${queue[@]:1}")
    [ -n "${seen[$f]}" ] && continue
    seen[$f]=1
    case $f in
      Cargo.toml | Cargo.lock | .cargo/* | rust-toolchain*) all=1 ;;
      # The root's clippy configuration applies to every package's lints, and to no test.
      clippy.toml | .clippy.toml) clippy_all=1 ;;
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
}

# Prints the changed packages of pkgs (of select_groups) and every package that depends on one of
# them, by any kind of dependency, on one line; every package when all is set. The package $1, if
# any, is left out, and so is what reaches the changed packages only through it.
closure() {
  jq -r --arg all "$all" --arg seed "${!pkgs[*]}" --arg skip "$1" '
    [.packages[].name] as $members
    | (if $all == "1" then $members else ($seed | split(" ") | map(select(. != ""))) end) as $start
    | [.packages[] | select(.name != $skip)
       | {name, deps: [.dependencies[].name | select(. as $d | $members | index($d))]}] as $g
    | {set: $start, todo: $start}
    | until(.todo == [];
        .todo as $t | .set as $s
        | ([$g[] | select(.name as $n | ($s | index($n) | not)) | select(any(.deps[]; . as $d | $t | index($d))) | .name]) as $new
        | {set: ($s + $new), todo: $new})
    | .set | unique | join(" ")' <<<"$meta"
}

# Attributes that put code or data into every binary that links a crate, used or not: an exported
# or kept symbol, a section of its own (.init_array runs code before main), the global allocator.
linkpat='#!?\[(unsafe\()?(no_mangle|export_name|link_section|used|global_allocator)([^A-Za-z0-9_]|$)|#\[ctor([^A-Za-z0-9_]|$)|init_array'
# Prints those of the packages "$@" whose sources, at HEAD or at $from, hold an attribute of
# linkpat, or that have a build script (which can add libraries and link arguments to every
# binary that links the package). A package's sources are the files in its directory and the
# files outside it that a file in it names by an include form (includers; the inline-module forms
# of under_rest name files under the includer's own directory). O(packages × include forms) for
# the second, against reading each package's include forms anew.
link_symbols() {
  local p pd d t s paths
  for p in "$@"; do
    d=
    for pd in "${pkgdirs[@]}"; do
      [ "${pd#* }" = "$p" ] && { d=${pd%% *}; break; }
    done
    paths=("${d:-.}")
    if [ -n "$d" ]; then
      for t in "${!includers[@]}"; do
        [[ $t == "$d"/* ]] && continue
        for s in ${includers[$t]}; do
          [[ $s == "$d"/* ]] && { paths+=("$t"); break; }
        done
      done
    fi
    if jq -e --arg p "$p" '.packages[] | select(.name == $p) | any(.targets[]; .kind | index("custom-build"))' <<<"$meta" >/dev/null ||
      git grep -q -E "$linkpat" HEAD -- "${paths[@]}" || git grep -q -E "$linkpat" "$from" -- "${paths[@]}"; then
      echo "$p"
    fi
  done
}

# Prints the files among "$2"... whose code names a word of $1 (one per line), each once. Not
# code: a line that is a `//` comment, doc comments included (tools/run_tests.sh runs no doc
# tests; --doc only builds the documentation), and a declaration `mod <name>;`, which names the
# module's file and uses nothing in it. Words in strings and block comments count, which can only
# select more.
rs_naming() {
  local words=$1
  shift
  [ $# -gt 0 ] || return 0
  awk -v words="$words" 'BEGIN { m = split(words, a, "\n"); for (i = 1; i <= m; i++) if (a[i] != "") n[a[i]] = 1 }
    FNR == 1 { done = 0 }
    done { next }
    /^[ \t]*\/\// { next }
    /^[ \t]*(pub(\([^)]*\))?[ \t]+)?mod[ \t]+[A-Za-z_0-9]+[ \t]*;/ { next }
    { line = $0
      while (match(line, /[A-Za-z_][A-Za-z0-9_]*/)) {
        if (substr(line, RSTART, RLENGTH) in n) { print FILENAME; done = 1; break }
        line = substr(line, RSTART + RLENGTH) } }' "$@"
}

# Prints the names by which code outside the file $1 of a lib can reach what it defines without
# naming its module: its macro_rules! macros, and the types of its impl blocks that it does not
# define itself (an impl of a trait for a type defined elsewhere is used through that type).
# Generics are dropped and the last segment of a path kept.
rs_items() {
  awk '/^[ \t]*\/\// { next }
    /^[ \t]*(pub(\([^)]*\))?[ \t]+)?(struct|enum|union|trait|type)[ \t]+[A-Za-z_]/ { l = $0
      sub(/^[ \t]*(pub(\([^)]*\))?[ \t]+)?(struct|enum|union|trait|type)[ \t]+/, "", l); sub(/[^A-Za-z0-9_].*/, "", l); own[l] = 1 }
    { l = $0
      while (match(l, /macro_rules![ \t]*[A-Za-z_][A-Za-z0-9_]*/)) {
        w = substr(l, RSTART, RLENGTH); sub(/.*[! \t]/, "", w); print w; l = substr(l, RSTART + RLENGTH) } }
    hdr != "" || /^[ \t]*(pub(\([^)]*\))?[ \t]+)?(unsafe[ \t]+)?impl[ \t<]/ {
      hdr = hdr " " $0
      if (hdr !~ /[{;]|(^|[ \t])where([ \t]|$)/) next
      h = hdr; hdr = ""
      sub(/[{;].*/, "", h); sub(/(^|[ \t])where([ \t].*|$)/, "", h)
      while (gsub(/<[^<>]*>/, "", h)) {}
      sub(/.*impl[ \t]+/, "", h)
      k = split(h, parts, /[ \t]+for[ \t]+/); t = parts[k]
      gsub(/[^A-Za-z0-9_:]+$/, "", t); sub(/.*[^A-Za-z0-9_]/, "", t)
      if (t != "") imp[t] = 1 }
    END { for (t in imp) if (!(t in own)) print t }' "$1"
}

# The module files above the lib file $1, up to the lib's root directory (not the root file):
# for <lib>/a/b.rs or <lib>/a/b/mod.rs, <lib>/a.rs and <lib>/a/mod.rs.
ancestors() {
  local d
  d=$(dirname "$1")
  [ "$(basename "$1")" = mod.rs ] && d=$(dirname "$d")
  while [ "$d" != "$fulllib" ] && [[ $d == "$fulllib"/* ]]; do
    echo "$d.rs"
    echo "$d/mod.rs"
    d=$(dirname "$d")
  done
}

# Step 2's narrowing for the words "$@" (the crate names by which $fullpkg reaches the changed
# packages). Sets libuse to the files of $fullpkg's lib that use them, users to its other .rs
# files that do, and extra to the files outside the lib that include a file of libuse; sets why
# when the lib's root file uses them. A lib file uses the words when its code names one, names a
# word an earlier such file adds (its module's name, the file's stem or, for mod.rs, its
# directory's; and rs_items), names `super` below such a file, or includes such a file by an
# include form; repeated until no file is added. Each round reads the lib files not yet taken,
# so O(rounds × lib size); rounds are at most the lib's files, and 3 on 2026-11-17.
uses() {
  local -A nset=() aff=()
  local w f s a added libfiles=() supers=() cand=() new=()
  for w in "$@"; do nset[$w]=1; done
  mapfile -t libfiles < <(git ls-files -- "$fulllib/*.rs")
  mapfile -t supers < <(git grep -l -w -F super -- "$fulllib/*.rs")
  libuse= users=() extra=()
  while :; do
    cand=()
    for f in "${libfiles[@]}"; do [ -n "${aff[$f]}" ] || cand+=("$f"); done
    mapfile -t new < <(rs_naming "$(printf '%s\n' "${!nset[@]}")" "${cand[@]}")
    for f in "${supers[@]}"; do
      [ -n "${aff[$f]}" ] && continue
      for a in $(ancestors "$f"); do
        [ -n "${aff[$a]}" ] && { new+=("$f"); break; }
      done
    done
    for f in "${!aff[@]}"; do
      for s in ${includers[$f]} $(inline_includers "$f"); do
        [[ $s == "$fulllib"/* ]] && [ -z "${aff[$s]}" ] && new+=("$s")
      done
    done
    added=
    for f in "${new[@]}"; do
      [ -n "${aff[$f]}" ] && continue
      aff[$f]=1
      added=1
      case $(basename "$f") in
        lib.rs) [ "$(dirname "$f")" = "$fulllib" ] && why="$f, the root of $fullpkg's lib, uses them" ;;
        mod.rs) nset[$(basename "$(dirname "$f")")]=1 ;;
        *) nset[$(basename "$f" .rs)]=1 ;;
      esac
      for w in $(rs_items "$f"); do nset[$w]=1; done
    done
    [ -n "$added" ] || break
  done
  [ -n "$why" ] && return
  libuse=$(printf '%s\n' "${!aff[@]}" | command grep -a . | sort | paste -sd' ')
  for f in "${!aff[@]}"; do
    for s in ${includers[$f]} $(inline_includers "$f"); do
      [[ $s == "$fulllib"/* ]] || extra+=("$s")
    done
  done
  mapfile -t cand < <(git grep -l -w -F -f <(printf '%s\n' "${!nset[@]}") -- "$fulldir/*.rs" ":(exclude)$fulllib")
  mapfile -t users < <(rs_naming "$(printf '%s\n' "${!nset[@]}")" "${cand[@]}")
}

# Sets sel to the groups that the changed files "$@" select, one per line, sorted: each local
# group g, short-g for each, and full-<piece> for each piece of tests/full; and prints how, each
# line headed "merge check$label:". Files are read at HEAD, and the attributes of step 2's
# narrowing at $from too.
select_groups() {
  local -A seen=() pkgs=() direct=() full=()
  local crate_srcs=() all= full_all= clippy_all= queue=("$@") selected groups skip= why= n0= np linked p
  local libuse= users=() extra=()
  walk

  [ ${#crate_srcs[@]} -gt 0 ] && echo "merge check$label: changed crate sources ${crate_srcs[*]}: s_01f_import_graph runs the imports tool over every crate"
  echo "merge check$label: changed packages: ${!pkgs[*]}${all:+ (a workspace file: all)}"
  # Step 2's narrowing (header): $fullpkg is left out of the closure when none of its own files
  # changed, and its groups are chosen by use below.
  [ -n "$fulllib" ] && [ -z "$all" ] && [ -z "${pkgs[$fullpkg]}" ] && skip=$fullpkg
  selected=$(closure "$skip")
  if [ -n "$skip" ]; then
    # The crate names by which $fullpkg's sources can use a selected package: those of its direct
    # dependencies that are selected (a dependency's rename, or its lib target's name).
    n0=$(jq -r --arg p "$fullpkg" --arg sel " $selected " '
      ([.packages[] | {key: .name, value: ([.targets[] | select(any(.kind[]; . == "lib" or . == "rlib"
        or . == "dylib" or . == "cdylib" or . == "proc-macro")) | .name][0] // .name)}] | from_entries) as $lib
      | .packages[] | select(.name == $p) | .dependencies[] | select(.name as $d | $sel | contains(" \($d) "))
      | (.rename // $lib[.name]) | gsub("-"; "_")' <<<"$meta" | sort -u)
    if [ -n "$n0" ]; then
      np=${#pkgs[@]}
      linked=$(link_symbols $selected | paste -sd' ')
      if [ -n "$linked" ]; then
        why="a selected package has a build script, or defines a symbol the linker places in every binary that links it (#[no_mangle], #[export_name], #[link_section], #[used] or #[global_allocator]): $linked"
      else
        uses $n0
        if [ -z "$why" ]; then
          echo "merge check$label: $fullpkg reaches the changed packages through $(paste -sd' ' <<<"$n0"); its lib files that use those names, or the modules, macros and types such files define: ${libuse:-none}"
          echo "merge check$label: its other files that use them: ${#users[@]}, in $(printf '%s\n' "${users[@]}" | command grep -a . | sed 's|/[^/]*$||' | sort -u | paste -sd' ')"
          queue=("${users[@]}" "${extra[@]}")
          walk
          if [ ${#pkgs[@]} -ne "$np" ]; then
            why="a file that uses them belongs to no test target of $fullpkg, or is included by #[path] into another package"
          elif [ -n "$libuse" ]; then
            # The lib's unit tests, and every package that depends on $fullpkg, link the lib.
            direct[$fulllibgroup]=1
            for p in $(jq -r --arg p "$fullpkg" '.packages[] | select(any(.dependencies[]; .name == $p)) | .name' <<<"$meta"); do
              pkgs[$p]=1
            done
            selected=$(closure "$skip")
          fi
        fi
      fi
      if [ -n "$why" ]; then
        echo "merge check$label: $why: $fullpkg is selected whole"
        skip=
        selected=$(closure "")
      fi
    fi
  fi
  echo "merge check$label: with their dependents: $selected"
  # The full battery is one binary of $fullpkg: a change to the package, or one it is selected
  # whole for, reaches every piece.
  if [ -n "$fullpkg" ] && [[ " $selected " == *" $fullpkg "* ]]; then
    full_all=1
    echo "merge check$label: $fullpkg, the package tests/full is built in, is selected: every piece of tests/full"
  fi

  groups=$(jq -r --arg sel " $selected " '.packages[] | select(.name as $n | $sel | contains(" \($n) "))
    | .targets[] | select(.test and ((.["required-features"] // []) == [])
                          and (.kind | index("custom-build") or index("example") or index("bench") | not))
    | .name | gsub("-"; "_")' <<<"$meta")
  [ ${#direct[@]} -gt 0 ] && echo "merge check$label: test targets changed alone: ${!direct[*]}"
  # Step 1a's packages: those selected, and each package that holds a test target of direct;
  # every package for a change to the root's clippy configuration.
  sel_pkgs=$(jq -r --arg sel " $selected " --arg d " ${!direct[*]} " --arg all "$clippy_all" '.packages[]
    | select($all == "1" or (.name as $n | $sel | contains(" \($n) "))
             or any(.targets[]; (.name | gsub("-"; "_")) as $t | $d | contains(" \($t) ")))
    | .name' <<<"$meta" | paste -sd' ')
  [ -z "$clippy_all" ] || echo "merge check$label: the root's clippy configuration changed: clippy runs on every package"
  # The pieces of tests/full selected, those whose folder exists at HEAD.
  local fullsel=$fullpieces
  [ -n "$full_all" ] || fullsel=$(for p in "${!full[@]}"; do [ -d "tests/full/$p" ] && echo "full-$p"; done | sort)
  groups+=$'\n'$(printf '%s\n' "${!direct[@]}")
  [ ${#crate_srcs[@]} -gt 0 ] && groups+=$'\ns_01f_import_graph'
  # A test target built with the feature short-addresses, one tools/run_tests.sh --short-groups
  # names, runs as the piece short-<group> too. Only those: --only '^(short-<group>)$' for any
  # other group selects no piece, which tools/run_tests.sh refuses (TOOL-run-tests-empty-filter).
  groups=$(command grep -a . <<<"$groups" | sort -u)
  [ -n "$groups" ] &&
    groups+=$'\n'$(command grep -a -x -F -f <(tools/run_tests.sh --short-groups) <<<"$groups" | sed 's/^/short-/')
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

label= from=$mb sel_pkgs=
select_groups "${changed[@]}"
clippy_pkgs=$sel_pkgs
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
if [ -z "$sel" ] && [ -z "$selftest$rtself" ] && [ -z "$clippy_pkgs" ]; then
  echo "merge check: no package changed; no tests to run"
  exit 0
fi
snew=$sel
s=$(part_of local "$snew")
echo "merge check: groups:${s:+ $(paste -sd' ' <<<"$s")}"
s=$(part_of full "$snew")
[ -z "$s" ] || echo "merge check: tests/full pieces: $(paste -sd' ' <<<"$s")"
[ -z "$selftest" ] || echo "merge check: a file tools/test_merge_check.sh tests changed: both its parts run"
[ -z "$rtself" ] || echo "merge check: a file tools/test_run_tests.sh tests changed: all its parts run"

# The record (see the header): `<commit>`, then `spec <commit>` when the spec checkout's commit
# is known (tools/spec_groups.sh --commit), then `group <g>` for each group that passed there, then
# `clippy <p>` for each package whose clippy passed there (step 1a), then
# `read <g> <path>` for each path g's pieces named, relative to the root ("." for the root itself,
# "*" for a read of anything, see tools/run_tests.sh --trace), then `end`. torun is
# S_new ∩ (S_D ∪ not S_old); keep is S_old \ S_D. For clippy the same with packages:
# clippy_run is P_new \ clippy_keep and clippy_keep is P_old \ P_D, where P_new is clippy_pkgs,
# P_old the record's packages and P_D the packages step 1a selects for the files of D. Proof that
# skipping a package p of P_old \ P_D is sound: clippy's verdict on p depends only on the files
# compiled into p and into the packages it depends on, each of which selects p (step 2, with the
# dependents), the workspace files (Cargo.toml, Cargo.lock, .cargo/, rust-toolchain*, which select
# every package) and the root's clippy.toml (which selects every package for clippy); no such
# file differs between T_old and H, so clippy gives p the same verdict, under the narrowing's
# assumption for zed-tests. The features clippy builds p with do not depend on which other
# packages the call names, by step 0a. Not covered, as for the tests: the toolchain installed.
torun=$snew keep= clippy_run=$clippy_pkgs clippy_keep=
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
      sd= pd=
      if [ ${#dfiles[@]} -gt 0 ]; then
        label=" (since the record's commit $(git rev-parse --short "$told"))"
        from=$told
        select_groups "${dfiles[@]}"
        sd=$sel pd=$sel_pkgs
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
      # The groups that read the spec checkout (spec:<path> in the record) run again unless it is
      # at the record's spec commit, known on both sides (MERGE-spec-push-check).
      rspec=$(awk '$1 == "spec" { print $2; exit }' "$record")
      if [ -z "$spec_at" ] || [ "$spec_at" != "$rspec" ]; then
        s=$(awk '$1 == "read" && $3 ~ /^spec:/ { print $2 }' "$record" | sort -u)
        echo "merge check: the spec checkout is at ${spec_at:-no known commit (none found, not a git checkout, or uncommitted changes)}, the record's at ${rspec:-no known commit}; the groups that read it are touched:${s:+ $(paste -sd' ' <<<"$s")}"
        sd=$(command grep -a . <<<"$sd"$'\n'"$s" | sort -u)
      fi
      torun=$(comm -12 <(echo "$snew") <(sort -u <(echo "$sd") <(comm -23 <(echo "$snew") <(echo "$sold")) | command grep -a .))
      keep=$(comm -23 <(echo "$sold") <(echo "$sd") | command grep -a .)
      echo "merge check: ${#dfiles[@]} files changed since the record's commit $(git rev-parse --short "$told"); passed there and not touched since: $(paste -sd' ' <<<"$keep")"
      clippy_keep=$(comm -23 <(awk '$1 == "clippy" { print $2 }' "$record" | sort -u) \
        <(tr ' ' '\n' <<<"$pd" | sort -u) | command grep -a .)
      clippy_run=$(comm -23 <(tr ' ' '\n' <<<"$clippy_pkgs" | sort -u) <(echo "$clippy_keep") |
        command grep -a . | paste -sd' ')
    fi
  fi
  s=$(part_of local "$torun")
  echo "merge check: to run:${s:+ $(paste -sd' ' <<<"$s")}"
  s=$(part_of full "$torun")
  [ -z "$s" ] || echo "merge check: tests/full pieces to run: $(paste -sd' ' <<<"$s")"
  echo "merge check: clippy to run:${clippy_run:+ $clippy_run}"
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
  if [ -n "$spec_at" ] && [ "$(tools/spec_groups.sh --commit)" != "$spec_at" ]; then
    echo "merge check: the spec checkout changed during the check; the record is not written"
    return
  fi
  {
    echo "$head"
    [ -z "$spec_at" ] || echo "spec $spec_at"
    command grep -a . <<<"$keep"$'\n'"$torun" | sort -u | sed 's/^/group /'
    command grep -a . <<<"$clippy_keep"$'\n'"$(tr ' ' '\n' <<<"$clippy_pkgs")" | sort -u | sed 's/^/clippy /'
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

# Step 0b: the parts of tools/test_run_tests.sh, started here and waited for after step 0, so the
# two steps run at once. A part that is not run (its chain stopped first) is reported as failed.
# The parts list the tests of the built binaries, and each builds first as run_tests.sh does,
# which does nothing on a built tree; on a worktree whose tests are not built yet every part ran
# into its limit while building (2026-11-20: all six killed at 60 s with empty logs). So the
# build comes first, `run_tests.sh --list` with no --only (the build of the full listing, with
# the short-addresses clone), with no time limit, since it is a build and not a test, and the
# parts start when it has passed. The build runs in the foreground, before step 0 starts its
# timed parts too: run beside them, a workspace build (at load 50 on 2026-11-20) pushed
# tools/test_merge_check.sh select, 15 to 21 s alone, past its 25 s limit.
rtparts=(list select table fresh short copy concurrent trace)
rtpids=()
if [ -n "$rtself" ] && [ -z "$list" ]; then
  rlog=$(git rev-parse --path-format=absolute --git-path merge-check-rt)
  piece_limit
  rtlimit=$((limit > 60 ? limit : 60))
  rt_part() { timeout -k 5 "$rtlimit" tools/test_run_tests.sh "$1" >"$rlog-$1.log" 2>&1; }
  # Emptied first, so a part its chain did not reach shows no line of an earlier check.
  for p in "${rtparts[@]}"; do : >"$rlog-$p.log"; done
  if ! tools/run_tests.sh --logs "$rlog-build" --list >"$rlog-build.log" 2>&1; then
    tail -n 40 "$rlog-build.log"
    echo "merge check: FAILED: the build for tools/test_run_tests.sh (log $rlog-build.log)" >&2
    exit 1
  fi
  # The parts' verdicts are read from their logs.
  (
    (rt_part list && rt_part select && rt_part table) &
    for p in fresh short copy concurrent trace; do rt_part "$p" & done
    wait
  ) &
  rtpids+=($!)
fi
# Waits for step 0b and fails when a part failed: each part's last line is "checks failed: 0"
# exactly when it passed (a part killed by its limit has no such line).
rt_wait() {
  [ ${#rtpids[@]} -gt 0 ] || return 0
  local p bad=
  wait "${rtpids[0]}"
  for p in "${rtparts[@]}"; do
    if [ "$(tail -n 1 "$rlog-$p.log" 2>/dev/null)" != "checks failed: 0" ]; then
      [ ! -f "$rlog-$p.log" ] || cat "$rlog-$p.log"
      echo "merge check: FAILED: tools/test_run_tests.sh $p (limit ${rtlimit}s; log $rlog-$p.log)" >&2
      bad=1
    fi
  done
  [ -z "$bad" ] || exit 1
  echo "merge check: tools/test_run_tests.sh list, select, table, fresh, short, copy, concurrent and trace passed"
}

# Step 0: the toy cases of this script, each part under the limit of a piece of run_tests.sh.
if [ -n "$selftest" ] && [ -z "$list" ]; then
  slog=$(git rev-parse --path-format=absolute --git-path merge-check-self)
  piece_limit
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
  # On a failure here step 0b is still waited for, so no part outlives the check.
  [ "$r1" -eq 0 ] && [ "$r2" -eq 0 ] || { rt_wait; exit 1; }
  echo "merge check: tools/test_merge_check.sh select and record passed"
fi
rt_wait

# Step 1a: clippy on the selected packages, before the tests (see the header), less those whose
# clippy passed at the record's commit with the same inputs.
if [ -n "$clippy_run" ] && [ -z "$list" ]; then
  echo "merge check: clippy -D warnings on: $clippy_run"
  cargo clippy -q $(printf -- '-p %s ' $clippy_run) --all-targets -- -D warnings ||
    { echo "merge check: FAILED: clippy (above)" >&2; exit 1; }
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
  # --skip-other-kind: a test target with benchmarks alone (deep_scaling, zedc_binary) is
  # named, since its package's test targets are, and has no piece to run here.
  tools/run_tests.sh "${full[@]}" --skip-other-kind --only "^($(paste -sd'|' <<<"$run"))\$" "${trace[@]}" $list "$jobs" ||
    { echo "merge check: FAILED: $([ "$kind" = full ] && echo tests/full || echo tests) (above)" >&2; exit 1; }
done
# The groups whose pieces read a file of the spec checkout must be those tools/spec_groups.sh
# names (step 3 above). One pass over the trace's files; spec_groups.sh runs only when a group
# read the spec.
if [ ${#tdirs[@]} -gt 0 ]; then
  spec_read=$(awk '{ dir = FILENAME; sub(/\/groups$/, "", dir); f = $1; gsub("/", "_", f); f = dir "/" f ".reads"
         while ((getline p < f) > 0) if (p ~ /^spec:/) { print $2; break }
         close(f) }' "${tdirs[@]/%//groups}" | sort -u)
  [ -z "$spec_read" ] || tools/spec_groups.sh --check <<<"$spec_read" ||
    { echo "merge check: FAILED: tools/spec_groups.sh (above)" >&2; exit 1; }
fi
[ -z "$record" ] || [ ${#tdirs[@]} -eq 0 ] || { write_record "${tdirs[@]}"; write_reads; }
echo "merge check: passed"
