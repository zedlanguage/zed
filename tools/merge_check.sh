#!/bin/bash
# The checks a branch passes before it is pushed to main (MERGE-import-cycle-check,
# MERGE-dependent-groups, MERGE-push-race). Usage, from a checkout's root, through zrun:
#   /home/luke/Work/wt/zrun tools/merge_check.sh [--base <rev>] [--record <file>] [--reads <dir>] [--list | --groups] [jobs]
# It takes the files the branch changes since its merge base with <rev> (origin/main by default;
# fetch first), both paths of a rename, and
#  0. when tools/merge_check.sh, tools/test_merge_check.sh, tools/run_tests.sh or
#     tools/spec_groups.sh changed: runs the four
#     parts of tools/test_merge_check.sh, select, select2, record and chunks, at once, each under the limit of a
#     piece of tools/run_tests.sh (max(20, 20 × load / cores) s), and fails if one fails
#     (MERGE-tools-self-tests). They test this script on a toy workspace, about 12 s each;
#     tools/run_tests.sh is in the list because this script's cases depend on its --only and
#     --trace, which the toy's stub imitates. Their result is not recorded: they run on every
#     check of such a branch. tools/test_lib.sh, which both test scripts source, is in this list
#     and the next;
#  0b. when tools/run_tests.sh, tools/lib.sh, tools/test_run_tests.sh or tools/test_lib.sh
#     changed: runs every
#     part of tools/test_run_tests.sh, list then select then table then except then benches (all
#     four read the table list publishes, in one log directory), short after list and beside them
#     (list and short both mount the short-addresses clone, and a run waits while another has
#     it), fresh then copy then trace then nobus after that chain (they start cargo, which lets
#     one process at a time hold its package cache), and concurrent and warm beside them (each in
#     a log directory of its own), each part under max(60, the piece limit) s:
#     the header of test_run_tests.sh gives each part 60 s, and list alone took 30 to 57 s at load
#     36 to 76. The parts start after the build of the tests they list, which runs first with no
#     limit, before step 0's timed parts too. Fails if the build or any part fails
#     (TOOL-merge-check-run-tests-self: until 2026-11-20 a change
#     to the test runner landed without its own tests, cc7961f67 tested by hand). Not recorded
#     either;
#  0c. when tools/farm_run.sh or tools/test_farm_run.sh changed: runs tools/test_farm_run.sh (a
#     fake pool and job.sh, about 23 s) under max(60, the piece limit) s, and fails if it fails
#     (FARM-share-load-timeouts). Not recorded;
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
#     Steps 0b, 0, 0c and 1a run, in that order, in tools/merge_check_steps.sh, on one Colab VM
#     through `tools/farm_run.sh --commands` (FARM-merge-check-clippy-selftests-remote), or here
#     with MERGE_CHECK_FARM=local; this script decides which of them run. A change to that script
#     runs step 0, as one to this script does;
#  2. runs, with tools/run_tests.sh --only, every test group of every workspace package that
#     depends on a changed package, directly or through others, and of the changed packages
#     themselves. The packages and their dependencies come from `cargo metadata`; nothing is
#     listed by hand. A file belongs to the package whose directory holds it most deeply, except
#     a file in the directory of a [[test]] target's main file other than the package's root or
#     src (tests/steps/<step>/), which selects that test target alone: no package depends on a
#     [[test]] target, so a change there reaches nothing else. A target's main file is taken with
#     its `.` and `<dir>/..` parts removed: cargo metadata gives the path as the manifest wrote
#     it, crates/zed-native/../../tests/steps/l01_36a_executables/binary.rs for build_binary, a
#     path no changed file has, so until MERGE-target-path-dots a change to such a file selected
#     none of the 14 test targets of zed-native and zed-clif under tests/steps/. A file
#     of the test runner, tools/run_tests.sh, tools/lib.sh (which it and this script source),
#     tools/farm_run.sh (which runs every piece on Colab VMs, step 2's run_farm, and decides which
#     timed-out pieces run again alone, FARM-share-load-timeouts) or
#     this script, selects every local group: every piece runs under tools/run_tests.sh, so a
#     change to it can break any piece, and compilation selects nothing for it
#     (MERGE-runner-selects-all; 324a94ebe, a change to tools/run_tests.sh, broke build_binary,
#     which its check did not select). Not the pieces of tests/full, which need --full. A file
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
#     are; the messages name them apart, as tests/full pieces. Each of the two is listed in one
#     call (--list, which builds) and run in chunks of related pieces of up to 30 s by the
#     times of earlier checks, each chunk a call of its own with jobs 1, `jobs` chunks at once;
#     a failed piece prints as it ends, the result is the sum of the chunks, and the check fails
#     unless the chunks ran exactly the listed pieces (step 2b at the code);
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
selftest= rtself= farmself=
for f in "${changed[@]}"; do
  case $f in tools/merge_check.sh | tools/merge_check_steps.sh | tools/test_merge_check.sh | tools/run_tests.sh | tools/spec_groups.sh | tools/test_lib.sh) selftest=1 ;; esac
  # tools/lib.sh holds `warm`, which `tools/test_run_tests.sh warm` tests (FAIL-warm-step-drops-output).
  case $f in tools/run_tests.sh | tools/lib.sh | tools/test_run_tests.sh | tools/test_lib.sh) rtself=1 ;; esac
  case $f in tools/farm_run.sh | tools/test_farm_run.sh) farmself=1 ;; esac
done

meta=$(cargo metadata --no-deps --format-version 1 -q) || { echo "merge check: cargo metadata failed" >&2; exit 1; }
# Each target's main file with its `.` and `<dir>/..` parts removed (MERGE-target-path-dots):
# cargo gives the path as the manifest wrote it, crates/zed-native/../../tests/steps/... A
# lexical step, which differs from the file system's only when a directory on the path is a
# symbolic link, and the record runs every group when HEAD tracks one.
meta=$(jq 'def norm: reduce (split("/")[]) as $s ([];
    if $s == "." then . elif $s == ".." and length > 1 and .[-1] != ".." then .[:-1] else . + [$s] end)
  | join("/");
  .packages[].targets[].src_path |= norm' <<<"$meta") || { echo "merge check: jq failed on cargo metadata" >&2; exit 1; }
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
# direct[<test target>], full[<piece>] or full_all for tests/full, all for a workspace file,
# runner for a file of the test runner, and crate_srcs.
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
      # The test runner: every piece runs under it (MERGE-runner-selects-all, header step 2).
      tools/run_tests.sh | tools/lib.sh | tools/merge_check.sh | tools/farm_run.sh) runner=1 ;;
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
  local crate_srcs=() all= full_all= clippy_all= runner= queue=("$@") selected groups skip= why= n0= np linked p
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

  # A file of the test runner selects the groups of every package, and no more packages for
  # step 1a's clippy, which reads no shell script.
  local gsel=$selected
  if [ -n "$runner" ]; then
    gsel=$(jq -r '[.packages[].name] | join(" ")' <<<"$meta")
    echo "merge check$label: a file of the test runner changed (tools/run_tests.sh, tools/lib.sh, tools/farm_run.sh or tools/merge_check.sh): every local group"
  fi
  groups=$(jq -r --arg sel " $gsel " '.packages[] | select(.name as $n | $sel | contains(" \($n) "))
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
if [ -z "$sel" ] && [ -z "$selftest$rtself$farmself" ] && [ -z "$clippy_pkgs" ]; then
  echo "merge check: no package changed; no tests to run"
  exit 0
fi
snew=$sel
s=$(part_of local "$snew")
echo "merge check: groups:${s:+ $(paste -sd' ' <<<"$s")}"
s=$(part_of full "$snew")
[ -z "$s" ] || echo "merge check: tests/full pieces: $(paste -sd' ' <<<"$s")"
[ -z "$selftest" ] || echo "merge check: a file tools/test_merge_check.sh tests changed: all its parts run"
[ -z "$rtself" ] || echo "merge check: a file tools/test_run_tests.sh tests changed: all its parts run"
[ -z "$farmself" ] || echo "merge check: a file tools/test_farm_run.sh tests changed: it runs"

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

# farm_dir <name>: a new directory under the git directory for one call of the farm runner.
farm_dir() {
  local o
  o=$(git rev-parse --path-format=absolute --git-path "$1")/$(date -u +%Y%m%dT%H%M%S)-$$
  [[ $o == /?*/"$1"/*-$$ ]] || { echo "merge check: bad farm directory '$o'"; return 1; }
  mkdir -p "$o" || return 1
  echo "$o"
}
# farm_owner: the VMs' owner, merge-check-<branch>, so the pool shows whose check holds them.
farm_owner() {
  local owner
  owner=merge-check-$(git branch --show-current | tr -c 'A-Za-z0-9._\n-' '-' | sed 's#^wt-##')
  [ "$owner" != merge-check- ] || owner=merge-check-$(git rev-parse --short=9 HEAD)
  echo "$owner"
}
# run_steps_farm: the steps in $steps on one VM, as one command of `$farm --commands`, which runs
# it in the checkout's root at the build root of the short-addresses build (test_run_tests.sh's
# list and short parts build that clone), with the logs under the job's out/ (FARM_OUT), which
# come back to the farm's directory; with $doc_vm set, the check of the changed documentation is
# a second command of the same job (doc_vm, below). Prints the commands' lines; fails when one
# failed or did not run to its end.
run_steps_farm() {
  local o spec
  o=$(farm_dir merge-check-steps) || return 1
  spec=$(tools/spec_groups.sh --dir) && [[ $spec == /?* ]] && [ -d "$spec" ] ||
    { echo "merge check: tools/spec_groups.sh --dir gave no spec directory ('$spec')"; return 1; }
  : >"$o/commands" || return 1
  if [ ${#steps[@]} -gt 0 ]; then
    printf 'tools/merge_check_steps.sh --logs "$FARM_OUT/merge-check"%s\n' "$(printf ' %q' "${steps[@]}")" >>"$o/commands" || return 1
    echo "merge check: steps ${steps[*]} on a Colab VM as $(farm_owner) (logs $o)"
  fi
  if [ -n "$doc_vm" ]; then
    echo 'tools/check_changed_docs.sh "$FARM_OUT/doc-changed.log"' >>"$o/commands" || return 1
    echo "merge check: the check of the changed documentation on a Colab VM as $(farm_owner) (logs $o)"
    doc_by="the merge check's job on a Colab VM (logs $o)"
  fi
  "$farm" --owner "$(farm_owner)" --vms 1 --jobs "$jobs" --out "$o/run" --commands "$o/commands" --spec "$spec"
}
# Steps 0b, 0, 0c and 1a, in that order (see the header), in tools/merge_check_steps.sh: run here
# with MERGE_CHECK_FARM=local, else on one Colab VM through `$farm --commands`
# (FARM-merge-check-clippy-selftests-remote; author 2026-11-22: "start all future jobs in the
# cloud via Colab"). Until then they ran here on every check: cargo clippy over the selected
# packages and, when a tool changed, its self-tests, which build the workspace's tests here.
# The VM gets the checkout's files and no git repository, so this script decides which steps run
# and the step script reads only its arguments. Clippy's verdict is the same on the VM: it reads
# the same sources with the same toolchain (rust-toolchain), and the packages whose clippy passed
# at the record's commit are left out of --clippy here, as before. The VM's logs come back under
# the farm's directory, named on a failure.
farm=${MERGE_CHECK_FARM:-$(pwd -P)/tools/farm_run.sh}
[ "$farm" = local ] || [ -x "$farm" ] || { echo "merge check: no farm runner '$farm' (MERGE_CHECK_FARM)" >&2; exit 2; }
steps=()
[ -z "$selftest" ] || steps+=(--self)
[ -z "$rtself" ] || steps+=(--rt)
[ -z "$farmself" ] || steps+=(--farm)
[ -z "$clippy_run" ] || steps+=(--clippy "$clippy_run")
# The check of the changed documentation (tools/check_changed_docs.sh), which runs cargo
# metadata, cargo tree and cargo doc. With a farm runner it runs on the VM of the steps
# (TOOL-doc-check-on-vm; author: no builds on this machine): until then run_farm ran it here
# before the VMs, a local build of every changed package's documentation, twice. The VM's copy
# has no git history, so the changes are found here, by git alone (`--changes` exits before any
# cargo call), and `$farm --commands` sends them with the command (ZED_DOC_CHANGES). It runs when
# tests run, as it did in run_farm and does in run_chunks: doc_vm is set when there are tests to
# run and `--changes` printed a changed file or a lost name, or printed nothing, which it does
# with no origin/main here, and then the check on the VM fails as it would have here. doc_by
# names the run that did the check, for the VM shares of run_farm (ZED_DOC_CHECKED).
doc_vm= doc_by=
if [ "$farm" != local ] && [ -z "$list" ] && [ -n "$torun" ]; then
  doc_changes=$(tools/check_changed_docs.sh --changes) ||
    { echo "merge check: FAILED: tools/check_changed_docs.sh --changes" >&2; exit 1; }
  if [ -z "$doc_changes" ] || awk -F '\t' '$1 == "changed" || $1 == "name" { f = 1 } END { exit !f }' <<<"$doc_changes"; then
    doc_vm=1
  else
    doc_by="the merge check, which found no doc line changed and no linked name lost since origin/main"
  fi
fi
if { [ ${#steps[@]} -gt 0 ] || [ -n "$doc_vm" ]; } && [ -z "$list" ]; then
  if [ "$farm" = local ]; then
    "${BASH_SOURCE[0]%/*}/merge_check_steps.sh" --logs "$(git rev-parse --path-format=absolute --git-path merge-check)" "${steps[@]}" ||
      exit 1
  else
    run_steps_farm || exit 1
  fi
fi

if [ -n "$snew" ] && [ -z "$torun" ]; then
  echo "merge check: passed (every selected group passed at the record's commit, with the same inputs)"
  write_record
  exit 0
fi
# Step 2b, the tests in chunks (MERGE-full-run-split; author: "Split the 129 test pieces into
# separate tests (try to find sensible groupings of related tests, and chunk them up)"). Until
# then each kind was one call of tools/run_tests.sh over every selected group, a run of 2,880
# pieces and 15 to 29 minutes on a change to the runner (spec7, 2026-11-20); tools7 wrapped one
# in `timeout 590`, which killed it with no verdict. Now one call lists the pieces (--list, which
# builds them), they are cut into chunks of related pieces, each chunk is a call of its own with
# jobs 1, and up to `jobs` chunks run at once, so as many pieces run at once as before.
#  - Related: the chunks follow the order of the list, which is the order of the table of
#    tools/run_tests.sh, by test binary and step folder, so a chunk holds whole groups or a
#    run of one group's pieces.
#  - Size: a chunk is closed before the estimate of its pieces' times passes chunk_ms (30 s,
#    half the 60 s a run may take, for the load to vary under). A piece's estimate is its time
#    in the last check that ran it, from <git common dir>/merge-check-times, shared by every
#    worktree; for a piece no check timed yet, the longest time any run of main_watch recorded
#    for it (the summary files under $times_from, /home/luke/Work/wt/main-watch-runs: full runs
#    on main; on 2026-11-20 they timed 2,891 of the 2,896 pieces of a check that selected every
#    local group). The longest, not the newest, since a larger estimate only makes chunks
#    smaller. A piece neither timed is a chunk alone, as is a piece of chunk_ms or more: no
#    guess of an unknown time can bound a chunk of several, and alone it is bounded by the
#    per-piece limit of tools/run_tests.sh. Cost of the seed: one pass over those files, 25
#    summaries of 21,206 lines in 104 ms at load 68 (MERGE-full-run-split, 2026-11-20). Cost of
#    a piece alone: one call's own work (Cost, below). A test binary's pieces of its
#    library tests are named with the build's hash (63 of 2,896, zedc_check-<hash>), which a
#    rebuild changes: they are then timed by neither and each is alone, up to 63 calls, about
#    110 s of work, 27 s of wall time at 4 at once; the next check has their times again.
#  - The 60 s hold for every chunk, the first check's too: a chunk still running at
#    chunk_limit (60 s) is stopped with its pieces and fails the check, with a line naming its
#    pieces and their estimates. Each of its pieces that did not end is written to the times at
#    twice its estimate (run_chunk), so the next check cuts the chunk smaller: a stopped chunk is
#    split, not waited out.
#  - One listing: the list call builds the binaries and writes every selected piece's line
#    (`<name> <directory> <binary> <arguments>`) to the file pieces of its log directory, and
#    each chunk runs its own lines of it with tools/run_tests.sh --pieces, which runs no cargo
#    metadata, build, listing, selection or check of the changed documentation; that check runs
#    once here, after the list. Until then each chunk was a call with --only and --except that
#    did all of these again for its whole groups, so a group cut into c chunks was built and
#    listed c times: 9.6 s on average and up to 30 s a chunk before its first piece, and 17 of
#    56 chunks stopped at 60 s (the second seeded check, 2026-11-20, load 75). A chunk with a
#    short-addresses piece still runs that way, since the piece's binary lay in the list call's
#    clone, unmounted when the list call ended (3 pieces of 2,896, in one or two chunks).
#  - Exactly the same pieces: a --pieces chunk runs the list's lines of its pieces. Any other
#    chunk's call names in --only the terms of the merge check's own
#    selection (its groups) that select any of its pieces, and in --except, one per group, the
#    other pieces those terms select. --except removes a piece by its exact name, and with it
#    a whole group can be cut at any piece: a piece named after its group (a step folder's rest,
#    a library's tests, zed_kernel-<hash>) cannot be selected alone by --only, whose terms take
#    the group whole. Each call's own selection is that of the list call, from the same built
#    binaries, so the union of the chunks is the list. Checked on every run: the pieces in the
#    chunks' summaries must be the listed pieces, each once, or the check fails.
#  - Failures print as they happen, a line per failed piece when its run ends, then each failed
#    chunk's account of its failures once all chunks ended. A chunk without its line `pieces:
#    <n>, failed: <f>` (stopped before its pieces ran, or killed) counts as failed. The result is
#    the sum of the chunks.
# Cost: a --pieces chunk's own work before its first piece is the run's copy of the build (about
# 1,900 hard links, make_run_copy of tools/run_tests.sh) and the linking warm-up when the runtime
# changed: 0.5 s to 21 s, 2.2 s on average, at load 70 to 100 (from the pieces file to the first
# piece in the 35 chunks of the second seeded check that reached their pieces). The copy is made
# once per chunk; a copy shared by all chunks would save most of it (MERGE-chunks-shared-copy).
# The 2,040 s of spec7's pieces make about 70 chunks of 30 s, so about 150 s of such work, 40 s of
# wall time at 4 chunks at once, against the 15 to 29 minutes of the run in one call.
# A smaller chunk_ms costs more such work; a larger one leaves less of the 60 s for the load.
# A chunk that ends early, by a failure or a kill, ends only that chunk.
chunk_ms=30000 chunk_limit=${MERGE_CHECK_CHUNK_LIMIT:-60}
# MERGE_CHECK_TIMES_FROM and MERGE_CHECK_CHUNK_LIMIT exist for tools/test_merge_check.sh, which
# gives its toy runs of main_watch and a limit of a few seconds.
times_from=${MERGE_CHECK_TIMES_FROM:-/home/luke/Work/wt/main-watch-runs}
times_file=$(git rev-parse --path-format=absolute --git-common-dir)/merge-check-times
# The log directory of the run of tools/run_tests.sh whose process was $1: <base>/<UTC time>-<pid>,
# the newest if an older run had the same process number.
run_dir() { ls -d build/test-logs/*-"$1" 2>/dev/null | tail -n 1; }
# run_chunk <k>: runs chunk k of $cdir with jobs 1, writes its log to $cdir/<k>.log and its result
# to $cdir/<k>.result (`<rc> <ms> <log directory>`), and prints each failed piece's line as it ends.
run_chunk() {
  local k=$1 args g names pid rc start
  : >"$cdir/$k.stopped"
  # The chunk's pieces as the list call wrote them, run with --pieces: no cargo metadata, build,
  # listing, selection or check of the changed docs in the chunk's call (One listing, above). With
  # --trace the file groups that select_pieces of tools/run_tests.sh writes is written here, from
  # the list's chosen pieces. A chunk with a short-addresses piece, whose binary lay in the clone of
  # the list call, gone when it ended, selects its pieces again with --only and --except.
  if [ -s "$cdir/$k.lines" ] && [ ! -s "$cdir/$k.short" ]; then
    args=(--pieces "$cdir/$k.lines")
    if [ -n "$tbase" ]; then
      mkdir -p "$tbase/$k" &&
        awk 'NR == FNR { p[$1] = 1; next } $3 in p { print $3, $1, $2 }' "$cdir/$k.pieces" "$cdir/chosen" >"$tbase/$k/groups"
    fi
  else
    args=(--skip-other-kind --only "^($(paste -sd'|' "$cdir/$k.terms"))\$")
    while read -r g names; do args+=(--except "^($names)\$"); done <"$cdir/$k.except"
  fi
  [ -z "$tbase" ] || args+=(--trace "$tbase/$k")
  : >"$cdir/$k.log"
  start=$(date +%s%N)
  # The 60 s a test run may take holds for each chunk: at chunk_limit the chunk is stopped, not
  # waited out. timeout puts the call in a process group of its own and signals the whole group,
  # so the pieces stop with it (checked 2026-11-20: a background grandchild of the timed script
  # was gone after timeout returned 124); rc 124 (or 137 after the KILL 5 s later) marks it.
  timeout -k 5 "$chunk_limit" tools/run_tests.sh $fullarg "${args[@]}" 1 >>"$cdir/$k.log" 2>&1 &
  pid=$!
  # tail checks that $pid lives once per sleep interval, 1 s by default, so each chunk ended up
  # to 1 s late (the toy cases of tools/test_merge_check.sh, a check of several chunks each, took
  # 15 to 18 s longer); at 0.1 s it wakes 10 times a second per running chunk, a cost not seen.
  tail -s 0.1 -n +1 --pid="$pid" -f "$cdir/$k.log" |
    awk -v k="$k" -v n="$nchunks" '$2 ~ /^rc=/ && $2 != "rc=0" { print "merge check: chunk " k " of " n ": failed: " $0; fflush() }'
  wait "$pid"
  rc=$?
  # $pid is timeout's, so the log directory is read from the line `logs: <dir>` that
  # tools/run_tests.sh prints before its first piece.
  echo "$rc $((($(date +%s%N) - start) / 1000000)) $(sed -n 's/^logs: //p' "$cdir/$k.log" | tail -n 1)" >"$cdir/$k.result"
  # Stopped at chunk_limit (rc 124, or 137 after the KILL): a failure that names the chunk's
  # pieces, printed at once. Its pieces that did not end are written to $cdir/<k>.stopped at twice
  # their estimate (at least 1 ms; a piece with none at chunk_ms, alone again), in the form of a
  # summary line, for the times; those that ended have their own times. The chunk took over
  # chunk_limit = 2 × chunk_ms against an estimate of chunk_ms or less, so its pieces took at least
  # twice their estimates together: the doubled estimates of the next check pack fewer of them per
  # chunk, and each further stop doubles them again, so a chunk that keeps passing the limit is cut
  # down to single pieces in at most log2(chunk_ms) checks, each bounded alone by the per-piece
  # limit of tools/run_tests.sh. Until 2026-11-20 each such piece was written at chunk_ms and ran
  # alone at once: the 17 stopped chunks of the second seeded check (2026-11-20) would have made
  # 851 calls of one piece.
  if [ "$rc" = 124 ] || [ "$rc" = 137 ]; then
    awk -v ms="$chunk_ms" 'NR == FNR { if ($2 ~ /^rc=/) done[$1] = 1; next }
      !($1 in done) { e = ($2 ~ /^[0-9]+$/) ? 2 * $2 : ms; if (e < 1) e = 1; print $1, "rc=124", e "ms" }' \
      "$cdir/$k.log" "$cdir/$k.pieces" >"$cdir/$k.stopped"
    echo "merge check: chunk $k of $nchunks: FAILED: over ${chunk_limit} s, stopped; its pieces (estimate in ms; * did not end): $(awk 'NR == FNR { s[$1] = 1; next } { printf "%s%s%s %s", sep, $1, ($1 in s) ? "*" : "", $2; sep = ", " }' "$cdir/$k.stopped" "$cdir/$k.pieces")"
  fi
}
export -f run_chunk
# run_chunks <terms>: lists the pieces that --only '^(<terms>)$' selects (the terms one per line),
# runs them in chunks and fails if a chunk failed or the chunks did not run exactly the listed
# pieces, each once. Uses $fullarg (--full or nothing) and adds each chunk's trace directory to
# tdirs.
run_chunks() {
  local terms=$1 pid rc ldir k n ms dir over sum_p=0 sum_f=0 bad= start
  cdir=$(git rev-parse --path-format=absolute --git-path "merge-check-chunks${fullarg:+-full}")
  tbase=
  [ -z "$record" ] || tbase=$(git rev-parse --path-format=absolute --git-path "merge-check-trace${fullarg:+-full}")
  mkdir -p "$cdir" || return 1
  start=$(date +%s%N)
  # --skip-other-kind: a test target with benchmarks alone (deep_scaling, zedc_binary) is named,
  # since its package's test targets are, and has no piece to run here. The list builds the
  # binaries the chunks run.
  tools/run_tests.sh $fullarg --skip-other-kind --list --only "^($(paste -sd'|' <<<"$terms"))\$" "$jobs" >"$cdir/list.log" 2>&1 &
  pid=$!
  wait "$pid"
  rc=$?
  ldir=$(run_dir "$pid")
  if [ "$rc" -ne 0 ]; then
    cat "$cdir/list.log"
    return 1
  fi
  # The chosen pieces, `<group> <step> <name>` each (select_pieces of tools/run_tests.sh writes
  # them): none when every term names a group of the other kind alone, which the list notes.
  if [ -z "$ldir" ] || [ ! -s "$ldir/chosen" ]; then
    cat "$cdir/list.log"
    return 0
  fi
  cp "$ldir/chosen" "$cdir/chosen" || return 1
  # The check of the changed documentation, which each call of tools/run_tests.sh ran before
  # the chunks and which their --pieces calls leave to the caller (One listing, above).
  if ! tools/check_changed_docs.sh "$cdir/doc-changed.log" >"$cdir/doc-changed.out" 2>&1; then
    cat "$cdir/doc-changed.out"
    echo "merge check: FAILED: the check of the changed documentation (log $cdir/doc-changed.log)"
    return 1
  fi
  # The seed: for each piece, the longest time a summary under $times_from records (see Size in
  # the comment above). find does not follow the symbolic links `latest` there, so each run's
  # summary is read once (cost: Size, above).
  find "$times_from" -name summary -type f -print0 2>/dev/null |
    xargs -0 -r awk '$2 ~ /^rc=/ && $3 ~ /^[0-9]+ms$/ { t = $3 + 0; if (!($1 in m) || t > m[$1]) m[$1] = t }
      END { for (p in m) print p, m[p] }' >"$cdir/seed"
  # The chunks, written as $cdir/<k>.terms (the terms for --only), <k>.except (`<group>
  # <name>|<name>...`, one --except a line) and <k>.pieces, and $cdir/order, the chunks by
  # estimate, longest first, so that the longest do not start last. One pass over the times and
  # the pieces; then each chunk reads the pieces of the terms it names, so a group cut into c
  # chunks is read c times: O(pieces × the most chunks of one group), 543 pieces times 4 for
  # l01_26_type_resolution in spec7's check. Matching every chunk against every piece would be
  # O(pieces × chunks), 2,880 × 70.
  n=$(awk -v cdir="$cdir" -v chunk="$chunk_ms" '
    FILENAME == ARGV[1] { if (NF == 2 && $2 ~ /^[0-9]+$/) ms[$1] = $2; next }
    FILENAME == ARGV[2] { if (NF == 2 && $2 ~ /^[0-9]+$/) sd[$1] = $2; next }
    FILENAME == ARGV[3] { want[$1] = 1; next }
    !($3 in seen) {
      seen[$3] = 1; p = ++np; name[p] = $3; grp[p] = $1
      # The terms that select the piece: run_tests.sh selects it by its group, step or name.
      ts = ""
      if ($1 in want) ts = $1
      if ($2 != $1 && ($2 in want)) ts = ts " " $2
      if ($3 != $1 && $3 != $2 && ($3 in want)) ts = ts " " $3
      if (ts == "") { print "merge check: the listed piece " $3 " is selected by no term" > "/dev/stderr"; exit 1 }
      # A piece timed by neither, or of chunk_ms or more, is a chunk alone (Size, above).
      if ($3 in ms) e = ms[$3]; else if ($3 in sd) e = sd[$3]; else { e = "unknown"; nu++ }
      alone = e == "unknown" || e + 0 >= chunk
      if (k == 0 || full[k] || alone || est[k] + e > chunk) k++
      chunk_of[p] = k; est[k] += (e == "unknown") ? chunk : e; full[k] = alone
      if ($1 ~ /^short-/) short[k] = 1
      nt = split(ts, t, " ")
      for (i = 1; i <= nt; i++) {
        by[t[i]] = by[t[i]] " " p
        if (!((k, t[i]) in has)) { has[k, t[i]] = 1; terms[k] = terms[k] t[i] "\n" }
      }
      pieces[k] = pieces[k] $3 " " e "\n"
    }
    END {
      for (c = 1; c <= k; c++) {
        f = cdir "/" c ".terms"; printf "%s", terms[c] > f; close(f)
        f = cdir "/" c ".pieces"; printf "%s", pieces[c] > f; close(f)
        f = cdir "/" c ".short"; printf "%s", (c in short) ? "1\n" : "" > f; close(f)
        f = cdir "/" c ".lines"; printf "" > f; close(f)
        f = cdir "/" c ".except"; printf "" > f
        nt = split(terms[c], t, "\n"); delete out; delete ex; ng = 0
        for (i = 1; i < nt; i++) {
          m = split(by[t[i]], q, " ")
          for (j = 1; j <= m; j++) {
            p = q[j]
            if (chunk_of[p] == c || (p in out)) continue
            out[p] = 1
            if (!(grp[p] in ex)) { gs[++ng] = grp[p]; ex[grp[p]] = name[p] }
            else ex[grp[p]] = ex[grp[p]] "|" name[p]
          }
        }
        for (i = 1; i <= ng; i++) print gs[i], ex[gs[i]] > f
        close(f)
        print est[c], c > (cdir "/order.unsorted")
      }
      close(cdir "/order.unsorted")
      for (p = 1; p <= np; p++) print name[p], chunk_of[p] > (cdir "/assign")
      close(cdir "/assign")
      print k, nu + 0
    }' <(cat "$times_file" 2>/dev/null) "$cdir/seed" <(printf '%s\n' "$terms") "$cdir/chosen") || return 1
  read -r nchunks nunknown <<<"$n"
  # Each chunk's lines of the list call's file pieces (`<name> <directory> <binary> <arguments>`),
  # for its --pieces call: one pass over the pieces and one over the list, O(pieces). gawk keeps
  # the chunks' files open at once and, past the limit of open files, closes and reopens them to
  # append, so any number of chunks is written correctly.
  awk -v cdir="$cdir" 'FILENAME == ARGV[1] { c[$1] = $2; next }
    ($1 in c) { print > (cdir "/" c[$1] ".lines") }' "$cdir/assign" "$ldir/pieces" || return 1
  sort -k 1,1nr -k 2,2n "$cdir/order.unsorted" | cut -d ' ' -f 2 >"$cdir/order"
  echo "merge check: $(wc -l <"$cdir/chosen") pieces in $nchunks chunks of up to $((chunk_ms / 1000)) s by the times of earlier checks and of main_watch ($nunknown timed by neither, each alone), $jobs at once"
  for k in $(seq 1 "$nchunks"); do : >"$cdir/$k.result"; done
  export cdir tbase fullarg nchunks chunk_limit chunk_ms
  xargs -P "$jobs" -I '{}' bash -c 'run_chunk "$1"' _ '{}' <"$cdir/order"
  # The sum of the chunks and the pieces they ran.
  : >"$cdir/ran"
  : >"$cdir/summaries"
  for k in $(seq 1 "$nchunks"); do
    rc= ms= dir=
    read -r rc ms dir <"$cdir/$k.result"
    n=
    if [ -n "$dir" ]; then
      n=$(command grep -a -o -E '^pieces: [0-9]+, failed: [0-9]+' "$cdir/$k.log" | tail -n 1)
    fi
    over=
    [ ! -s "$cdir/$k.stopped" ] || over=", stopped at ${chunk_limit} s (named above)"
    echo "merge check: chunk $k of $nchunks: ${n:-no result} in $((${ms:-0} / 1000)) s$over"
    if [ -n "$n" ]; then
      [ ! -f "$dir/summary" ] || awk '$2 ~ /^rc=/ { print $1 }' "$dir/summary" >>"$cdir/ran"
      [ ! -f "$dir/summary" ] || echo "$dir/summary" >>"$cdir/summaries"
      n=${n#pieces: } sum_p=$((sum_p + ${n%%,*})) n=${n#*failed: } sum_f=$((sum_f + ${n%%,*}))
    fi
    [ "${rc:-1}" = 0 ] && [ -n "$n" ] || bad="$bad $k"
    # The trace of the chunk's call names the pieces its --except took out too (select_pieces
    # writes it before --except); kept are the chunk's own, so that the record reads no file an
    # earlier check left in this directory for a piece the chunk did not run.
    if [ -n "$tbase" ] && [ -f "$tbase/$k/groups" ]; then
      n=$(awk 'NR == FNR { p[$1] = 1; next } $1 in p' "$cdir/$k.pieces" "$tbase/$k/groups")
      printf '%s' "${n:+$n$'\n'}" >"$tbase/$k/groups"
      tdirs+=("$tbase/$k")
    fi
  done
  # The times for the next check: the old ones, with each piece just run at its new time and each
  # piece of a stopped chunk that did not end at chunk_ms ($cdir/<k>.stopped). Written
  # in place, not moved over the old file (no script here moves a file over another by a path
  # built from variables): a check that reads it during the write sees part of it and takes the
  # times of main_watch for the rest, or runs a piece alone, which only sizes its chunks worse
  # (smaller, or larger but still stopped at chunk_limit); of two checks that write at once
  # one's times are kept, and the next check of those pieces writes them again.
  n=$(awk 'FILENAME == ARGV[1] { if (NF == 2 && $2 ~ /^[0-9]+$/) t[$1] = $2; next }
    $2 ~ /^rc=/ && $3 ~ /^[0-9]+ms$/ { t[$1] = $3 + 0 }
    END { for (p in t) print p, t[p] }' <(cat "$times_file" 2>/dev/null) $(cat "$cdir/summaries") $(seq -f "$cdir/%g.stopped" 1 "$nchunks") | sort)
  [ -z "$n" ] || printf '%s\n' "$n" >"$times_file"
  for k in $bad; do
    echo "---- failed chunk $k of $nchunks (its log: $cdir/$k.log) ----"
    if command grep -a -q -e '^---- failed piece ' "$cdir/$k.log"; then
      sed -n '/^---- failed piece /,$p' "$cdir/$k.log"
    else
      tail -n 40 "$cdir/$k.log"
    fi
  done
  # The chunks must have run the listed pieces, each once: a piece run twice or not at all means
  # the --only and --except of the chunks did not cut the list as computed.
  n=$(sort "$cdir/ran" | uniq -d)
  [ -z "$n" ] || { echo "merge check: run by more than one chunk:"; echo "$n"; bad="$bad set"; }
  if [ -z "$bad" ]; then
    n=$(comm -3 <(awk '{ print $3 }' "$cdir/chosen" | sort -u) <(sort -u "$cdir/ran"))
    [ -z "$n" ] || {
      echo "merge check: the chunks did not run the listed pieces (left: listed, not run; right: run, not listed):"
      echo "$n"
      bad="$bad set"
    }
  fi
  echo "merge check: pieces: $sum_p, failed: $sum_f, in $nchunks chunks, $((($(date +%s%N) - start) / 1000000000)) s"
  [ -z "$bad" ]
}
# Where the pieces run (FARM-merge-check-remote; author 2026-11-22: "start all future jobs in the
# cloud via Colab"). By default on Colab VMs, through tools/farm_run.sh (MERGE_CHECK_FARM names
# another runner); `local` runs them here in chunks (run_chunks above), as before, and is what
# tools/test_merge_check.sh's toy uses ($farm, set above for the steps). The selection above, the
# clippy decision, this script's checks of the trace and the verdict stay here.
# run_farm <terms>: runs the pieces the terms (one a line, each a group) select, of kind $fullarg,
# on Colab VMs; fails if a piece failed or a VM's share was lost. Each term is anchored alone,
# as '^(<terms>)$' anchors them in run_chunks. The VMs' owner is merge-check-<branch>, so the
# pool shows whose check holds them; 4 VMs, the most one owner may hold (FARM.md). The VMs run
# tools/run_tests.sh, whose --list there checks no changed documentation (the VM's copy has no
# origin/main), so that check ran first, in the steps' job on a VM (doc_vm, above). With
# --record each VM's trace comes back as a directory of `groups` and `<piece>.reads` files,
# which join tdirs as run_chunks' chunk directories do. The spec the VMs get is the one the
# tests here would read (tools/spec_groups.sh --dir). The short-* pieces run on VMs too since
# FARM-short-pieces-on-vm-tmpfs, short-zed_kernel too since TEST-short-zed_kernel-split cut it into
# pieces under the limit; a folder of tests/full whose needs no VM has runs nowhere, named on
# farm_run.sh's `farm: not run` line (see the head of tools/farm_run.sh).
run_farm() {
  local terms=$1 o owner spec rc d
  o=$(farm_dir "merge-check-farm${fullarg:+-full}") || return 1
  printf '%s\n' "$terms" >"$o/terms" || return 1
  [ -n "$doc_by" ] || { echo "merge check: the check of the changed documentation did not run (doc_vm)"; return 1; }
  owner=$(farm_owner)
  spec=$(tools/spec_groups.sh --dir) && [[ $spec == /?* ]] && [ -d "$spec" ] ||
    { echo "merge check: tools/spec_groups.sh --dir gave no spec directory ('$spec')"; return 1; }
  local a=(--owner "$owner" --vms 4 --jobs "$jobs" --out "$o/run" --terms "$o/terms" --skip-other-kind --spec "$spec")
  [ -z "$fullarg" ] || a+=("$fullarg")
  [ -z "$record" ] || a+=(--trace "$o/trace")
  echo "merge check: $(wc -l <"$o/terms") groups${fullarg:+ of tests/full} on Colab VMs as $owner (logs $o)"
  # The doc check of the shares, whose copies have no origin/main, is the one the steps' job ran
  # (doc_vm, above; MERGECHECK-doc-check-skipped-without-origin; tools/check_changed_docs.sh).
  ZED_DOC_CHECKED=$doc_by "$farm" "${a[@]}"
  rc=$?
  if [ -n "$record" ] && [ "$rc" = 0 ]; then
    for d in "$o/trace"/*/; do
      [ -f "$d/groups" ] && tdirs+=("${d%/}")
    done
  fi
  [ "$rc" = 0 ]
}
# The local groups run first, then the pieces of tests/full with --full; the record is written
# once both passed. A merge check with --list makes one call of each kind, which lists alone.
tdirs=()
for kind in local full; do
  run=$(part_of "$kind" "$torun")
  [ -n "$run" ] || continue
  fullarg=
  [ "$kind" = full ] && run=$(sed 's/^/full-/' <<<"$run") && fullarg=--full
  what=$([ "$kind" = full ] && echo tests/full || echo tests)
  if [ -n "$list" ]; then
    tools/run_tests.sh $fullarg --skip-other-kind --only "^($(paste -sd'|' <<<"$run"))\$" --list "$jobs" ||
      { echo "merge check: FAILED: $what (above)" >&2; exit 1; }
    continue
  fi
  if [ "$farm" = local ]; then
    run_chunks "$run" || { echo "merge check: FAILED: $what (above)" >&2; exit 1; }
  else
    run_farm "$run" || { echo "merge check: FAILED: $what (above)" >&2; exit 1; }
  fi
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
