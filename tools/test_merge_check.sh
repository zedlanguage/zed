#!/bin/bash
# Tests the selection of tools/merge_check.sh on a workspace of its own in a git repository,
# build/test-merge-check, which it keeps from run to run (it deletes nothing; each run writes every
# file again and commits exactly the files of the list toy_files as the new base, and each case
# commits only the file it changes, so a file an earlier run left behind is in no commit; see the
# comment at toy_files). Run from a checkout's root, through zrun
# (`/home/luke/Work/wt/zrun tools/test_merge_check.sh [select | select2 | record | chunks]`). With an argument it runs
# that part of the cases alone, in a workspace of its own (build/test-merge-check-<part>), so the
# parts can run at once, and with no argument all four do: run so, select, select2, record and
# chunks took 24, 17, 30 and 12 s side by side at load 76 (2026-11-20).
# The workspace is the real one
# in small: crates a, b (depends on a) and c; a package t in tests/ that depends on b, whose lib
# file tests/src/seed.rs crate a also compiles by #[path] (as tests/src/seed.rs is compiled into
# seven crates), with [[test]] targets step_x and step_y in tests/steps/<step>/ and full, which
# needs a feature. tools/run_tests.sh is a stub that prints its arguments and exits with $STUB_RC.
# More files of crates b and c name files of other packages by #[path] in a mod.rs file, inside
# inline modules, and by include! (TEST-merge-check-nested-path). Pieces w and z of tests/full, the
# toy's own tools/test_merge_check.sh (a stub) and a map of run-time reads (--reads) test the
# selection of tests/full, the self-tests and step 2a (MERGE-runtime-inputs,
# MERGE-tools-self-tests). t depends on more crates for the narrowing of step 2
# (MERGE-dep-by-target): tool, named only by step_x; rootuse, named by t's lib root; lnk, which
# exports a symbol; and feat, with a default feature x, for step 0a, and a [[test]] target feat_f
# whose main file its manifest names through `..`, tests/steps/f/feat.rs, as zed-native names
# its test targets under tests/steps/ (MERGE-target-path-dots). t's lib file
# tests/src/helper.rs names b and is used by step_x, the piece w and the lib file
# tests/src/wrap.rs, which step_y uses. The last cases rebase a branch on a main that moves and check what
# --record runs again (MERGE-push-race). Step 1a runs the real cargo clippy on the toy, so its code
# passes clippy -D warnings; b calls a::f, for a case where a change to a makes b warn
# (TOOLS-merge-check-clippy).
# MERGE_CHECK names another script to test, such as an older version, to see these cases fail.
check_script=${MERGE_CHECK:-$(pwd)/tools/merge_check.sh}
spec_groups=$(pwd)/tools/spec_groups.sh
part=$1
case $part in
  '' | select | select2 | record | chunks) ;;
  *) echo "usage: tools/test_merge_check.sh [select | select2 | record | chunks]" >&2; exit 2 ;;
esac
# With no argument the four parts run at once, each as `tools/test_merge_check.sh <part>` in its
# own workspace as step 0 of tools/merge_check.sh runs them; one after another they took 58 to over
# 60 s at load 50 to 77 (2026-11-20), past the 60 s a test run may take. Their output prints part
# by part, and the run passes when all four pass.
if [ -z "$part" ]; then
  parts=(select select2 record chunks) pids=() bad=0
  mkdir -p build
  for p in "${parts[@]}"; do
    "$0" "$p" >"build/test-merge-check-$p.log" 2>&1 &
    pids+=($!)
  done
  for i in "${!parts[@]}"; do
    wait "${pids[$i]}" || bad=$((bad + 1))
    echo "== part ${parts[$i]} (log build/test-merge-check-${parts[$i]}.log)"
    cat "build/test-merge-check-${parts[$i]}.log"
  done
  echo "test_merge_check: $bad of ${#parts[@]} parts failed"
  exit $((bad > 0))
fi
ws=$(pwd)/build/test-merge-check${part:+-$part}
mkdir -p "$ws/crates/a/src" "$ws/crates/b/src/m" "$ws/crates/c/src/m" "$ws/crates/c/data" \
  "$ws/crates/tool/src" "$ws/crates/rootuse/src" "$ws/crates/lnk/src" "$ws/crates/feat/src" "$ws/tests/src" "$ws/tests/steps/x" "$ws/tests/steps/y" "$ws/tests/steps/f" "$ws/tests/full" "$ws/tools" "$ws/docs"
export CARGO_TARGET_DIR=$ws/target
# The toy's spec checkout, a repository of its own (MERGE-spec-push-check); without it the walk of
# tools/spec_groups.sh --dir would find the real one above the checkout.
export ZED_SPEC_DIR=$ws/target/spec
mkdir -p "$ZED_SPEC_DIR"
[ -e "$ZED_SPEC_DIR/.git/HEAD" ] || git -C "$ZED_SPEC_DIR" init -q -b main
git -C "$ZED_SPEC_DIR" config user.name test
git -C "$ZED_SPEC_DIR" config user.email test@localhost
echo "# spec" >"$ZED_SPEC_DIR/DESIGN.md"
git -C "$ZED_SPEC_DIR" add -- DESIGN.md
git -C "$ZED_SPEC_DIR" commit -q --allow-empty -m "spec"
fails=0
. tools/test_lib.sh || exit 2
[ -e "$ws/.git/HEAD" ] || git -C "$ws" init -q -b main
git -C "$ws" config user.name test
git -C "$ws" config user.email test@localhost
pushd "$ws" >/dev/null || exit 1
# Cargo.lock is not tracked: cargo tree (step 0a) writes it.
printf '/target\n/Cargo.lock\n/build\n' >.gitignore
printf '[workspace]\nresolver = "3"\nmembers = ["crates/*", "tests"]\n' >Cargo.toml
pkg() { printf '[package]\nname = "%s"\nversion = "0.0.0"\nedition = "2024"\n%s' "$1" "$2"; }
pkg a '' >crates/a/Cargo.toml
pkg b $'\n[dependencies]\na = { path = "../a" }\n' >crates/b/Cargo.toml
pkg c '' >crates/c/Cargo.toml
pkg tool '' >crates/tool/Cargo.toml
pkg rootuse '' >crates/rootuse/Cargo.toml
pkg lnk '' >crates/lnk/Cargo.toml
pkg feat $'\n[features]\ndefault = ["x"]\nx = []\n\n[[test]]\nname = "feat_f"\npath = "../../tests/steps/f/feat.rs"\n' \
  >crates/feat/Cargo.toml
for c in tool rootuse feat; do echo "//! $c." >"crates/$c/src/lib.rs"; done
printf '//! lnk.\n#[unsafe(no_mangle)]\npub extern "C" fn lnk_f() {}\n' >crates/lnk/src/lib.rs
pkg t $'\n[dependencies]\nb = { path = "../crates/b" }\ntool = { path = "../crates/tool" }
rootuse = { path = "../crates/rootuse" }\nlnk = { path = "../crates/lnk" }
feat = { path = "../crates/feat" }\n\n[features]\nfull = []\nspec = []\n
[[test]]\nname = "step_x"\npath = "steps/x/mod.rs"\n\n[[test]]\nname = "step_y"\npath = "steps/y/mod.rs"\n
[[test]]\nname = "full"\npath = "full/main.rs"\nrequired-features = ["full"]\n' >tests/Cargo.toml
# b calls a::f, so a change to a can make b warn (step 1a, TOOLS-merge-check-clippy).
printf '#[cfg(test)]\n#[path = "../../../tests/src/seed.rs"]\nmod seed;\npub fn f() {}\n' >crates/a/src/lib.rs
printf '//! b.\npub fn g() {\n    a::f()\n}\n' >crates/b/src/lib.rs
echo '//! c.' >crates/c/src/lib.rs
printf '//! t.\npub mod seed;\npub mod helper;\npub mod wrap;\nuse rootuse as _;\n' >tests/src/lib.rs
echo '//! The seed.' >tests/src/seed.rs
printf '//! A step helper.\n// Not code: tool lnk feat.\nuse b as _;\n' >tests/src/helper.rs
# A module imported as `_` is an unused import, which step 1a's clippy refuses.
printf '//! A helper over the helper.\n#![allow(unused_imports)]\nuse crate::helper as _;\n' >tests/src/wrap.rs
# The Rust reference, "The path attribute": in a mod.rs, lib.rs or main.rs file, a #[path] is
# relative to the file's directory, and inside inline modules to that directory followed by the
# inline modules' names; in any other file, inside inline modules, to the directory followed by the
# file's stem and the inline modules' names. include! is relative to the file that holds it.
printf '#[path = "../../../../tests/src/viamod.rs"]\nmod v;\n' >crates/b/src/m/mod.rs
echo 'include!("../../c/data/table.rs");' >crates/b/src/gen.rs
printf 'mod inner {\n    #[path = "../../../../../tests/src/inl.rs"]\n    mod x;\n}\n' >crates/c/src/inl.rs
printf 'mod outer {\n    mod inner {\n        #[path = "../../../../../../tests/src/nest.rs"]\n        mod x;\n    }\n}\n' \
  >crates/c/src/m/mod.rs
for f in viamod inl nest; do echo "//! $f." >"tests/src/$f.rs"; done
echo '// table' >crates/c/data/table.rs
# step_x reads the spec (MERGE-spec-reads-map): its folder holds the feature spec, so the real
# tools/spec_groups.sh, copied into the toy, names it.
printf '//! x.\n#![allow(unused_imports)]\nuse t::helper as _;\nuse tool as _;\n#[cfg(feature = "spec")]\nmod spec {}\n' >tests/steps/x/mod.rs
cat "$spec_groups" >tools/spec_groups.sh
chmod +x tools/spec_groups.sh
printf '//! y.\n#![allow(unused_imports)]\nuse t::wrap as _;\n' >tests/steps/y/mod.rs
echo '//! feat_f.' >tests/steps/f/feat.rs
echo '//! full.' >tests/full/main.rs
mkdir -p tests/full/w tests/full/z
printf '//! w.\nuse t::helper as _;\n' >tests/full/w/mod.rs
echo '//! z.' >tests/full/z/mod.rs
# The toy's own tools/test_merge_check.sh, which merge_check.sh runs when a file it tests changes:
# it prints its part and fails the part named by $STUB_SELF_FAIL, and, when $STUB_BUILD_MARK is
# set, fails if that file does not exist yet (the build of step 0b has not ended).
printf '#!/bin/bash\necho "self $1"\n[ -z "$STUB_BUILD_MARK" ] || [ -e "$STUB_BUILD_MARK" ] || { echo "self $1 ran before the build ended"; exit 1; }\n[ "$1" != "$STUB_SELF_FAIL" ]\n' >tools/test_merge_check.sh
chmod +x tools/test_merge_check.sh
# The toy's own tools/test_run_tests.sh (step 0b, TOOL-merge-check-run-tests-self): it prints its
# part and, as the real one does, "checks failed: <n>" last, 1 for the part named by $STUB_RT_FAIL.
printf '#!/bin/bash\necho "rt $1"\n[ "$1" != "$STUB_RT_FAIL" ] || { echo "checks failed: 1"; exit 1; }\necho "checks failed: 0"\n' >tools/test_run_tests.sh
chmod +x tools/test_run_tests.sh
# The toy's own tools/check_changed_docs.sh, which the chunks of step 2b leave to the merge check
# (tools/run_tests.sh --pieces does not run it): it fails when $STUB_DOCS_FAIL is set.
printf '#!/bin/bash\n[ -z "$STUB_DOCS_FAIL" ] || { echo "a doc link names no item"; exit 1; }\n' >tools/check_changed_docs.sh
chmod +x tools/check_changed_docs.sh
: >tools/test_lib.sh
echo '# Notes' >docs/notes.md
echo '# Plan' >docs/plan.md
mkdir -p data
echo 'notes' >data/notes.txt
# The stub. With --trace <dir>, it writes for each piece its --only selects, before --except,
# `<name> <group> <step>` into <dir>/groups and, as the paths the piece read, the lines `<group>
# <path>` of $STUB_READS into <dir>/<name>.reads. The pieces are those of $STUB_PIECES (lines
# `<group> <step> <name>`) and, for each group of --only that no line of it names, one piece
# p-<group>; a term selects a piece when it is the piece's group, step or name, as in
# tools/run_tests.sh. Each run writes a log directory build/test-logs/<time>-<pid> as the real one
# does: with --list the files chosen and pieces (`<name> <group> /bin/true`, the group in the
# place of the directory) and the names alone; with --pieces <file>, the pieces of that file,
# selecting none and writing no file groups; otherwise, for each piece --except leaves,
# a line `<name> rc=<rc> <ms>ms ...` on standard output and in the file summary, then `pieces: <n>,
# failed: <f>`. A piece fails when it is $STUB_FAIL, runs into a limit of 1 s when it is $STUB_HANG
# (rc 124, as the real per-piece limit reports), sleeps 30 s when it is $STUB_SLOW, and is
# skipped, as if lost, when it is $STUB_DROP. A run prints `logs: <its log directory>` first, as
# the real one does.
# Each call line is appended to $STUB_CALLS too, when it is set: the merge check writes its calls'
# output to log files.
cat >tools/run_tests.sh <<'EOF'
#!/bin/bash
# The groups with a short-addresses piece: $STUB_SHORT, or by default every group of the toy.
if [ "$1" = --short-groups ]; then
  printf '%s\n' ${STUB_SHORT-a b c feat feat_f lnk rootuse s_01f_import_graph step_x step_y t tool}
  exit 0
fi
echo "run_tests $*"
[ -z "$STUB_CALLS" ] || echo "run_tests $*" >>"$STUB_CALLS"
t= o= l= x= p=
while [ $# -gt 0 ]; do
  case $1 in
    --trace) t=$2; shift ;; --only) o=$2; shift ;; --except) x=${x:+$x|}$2; shift ;; --list) l=1 ;;
    --pieces) p=$2; shift ;;
  esac
  shift
done
# A build (--list) that takes a second and then makes the file $STUB_BUILD_MARK, when it is set.
if [ -n "$l" ] && [ -n "$STUB_BUILD_MARK" ]; then
  sleep 1
  : >"$STUB_BUILD_MARK"
fi
[ "${STUB_RC:-0}" = 0 ] || exit "$STUB_RC"
terms=${o#^(}
terms=${terms%)\$}
d=build/test-logs/$(date -u +%Y%m%dT%H%M%S.%NZ)-$$
mkdir -p "$d"
: >"$d/summary"
awk -v terms="$terms" 'BEGIN { n = split(terms, a, "|"); for (i = 1; i <= n; i++) T[a[i]] = 1 }
  FILENAME != "-" { g[$1] = 1; line[++m] = $0; next }
  END {
    for (i = 1; i <= n; i++) if (!(a[i] in g)) line[++m] = a[i] " " a[i] " p-" a[i]
    for (i = 1; i <= m; i++) { split(line[i], f, " ")
      if ((f[1] in T || f[2] in T || f[3] in T) && !seen[f[3]]++) print line[i] }
  }' ${STUB_PIECES:-/dev/null} - </dev/null >"$d/chosen"
# The pieces to run, `<group> <step> <name>` each: with --pieces, those of its file (lines
# `<name> <group> <binary>` as a --list run writes them below, the group standing for the
# directory), else the chosen ones.
if [ -n "$p" ]; then
  awk '{ print $2, $2, $1 }' "$p" >"$d/run"
else
  cp "$d/chosen" "$d/run"
fi
if [ -n "$t" ]; then
  mkdir -p "$t"
  # As tools/run_tests.sh, a --pieces run writes no file groups: it selects nothing.
  [ -n "$p" ] || : >"$t/groups"
  while read -r g s n; do
    [ -n "$p" ] || echo "$n $g $s" >>"$t/groups"
    awk -v g="$g" '$1 == g { print substr($0, length(g) + 2) }' "$STUB_READS" >"$t/$n.reads"
  done <"$d/run"
fi
if [ -n "$l" ]; then
  awk '{ print $3, $1, "/bin/true" }' "$d/chosen" >"$d/pieces"
  awk '{ print $3 }' "$d/chosen"
  exit 0
fi
echo "logs: $d"
np=0 nf=0 dump=
while read -r g s n; do
  [ -z "$x" ] || ! [[ $n =~ $x ]] || continue
  [ "$n" != "$STUB_DROP" ] || continue
  rc=0
  [ "$n" != "$STUB_FAIL" ] || rc=1
  [ "$n" != "$STUB_SLOW" ] || sleep 30
  if [ "$n" = "$STUB_HANG" ]; then
    timeout -k 1 1 sleep 30
    rc=$?
  fi
  echo "$n rc=$rc ${STUB_MS:-5}ms load=0 limit=1s wait=0ms" | tee -a "$d/summary"
  np=$((np + 1))
  [ "$rc" = 0 ] || { nf=$((nf + 1)); dump="$dump---- failed piece $n ----"$'\n'; }
done <"$d/run"
printf '%s' "$dump"
echo "pieces: $np, failed: $nf, load: 0 to 0, cores: 1"
[ "$nf" = 0 ]
EOF
chmod +x tools/run_tests.sh
# The base commit holds exactly the files written above, the list toy_files, staged on an index
# built from nothing (TOOL-merge-selftest-stale-toy). Why: the toy is kept from run to run and the
# script may delete nothing in it (the rm rules forbid a path built from $ws). A run killed in a
# case leaves that case's file behind, untracked or committed on the commit HEAD was left at (the
# select part's last case adds new.txt at the root). The old base, `git add -A` on top of that HEAD,
# took such a file into base, and from then on every run failed the case that adds it ("a file added
# at the root selects the group that stat'ed the root": with new.txt already in base the change is
# no longer an added file at the root); seen by flake1 on 2026-11-20 after merge_check killed the
# select part at its limit.
# Why this is enough: (1) `git read-tree --empty` empties only the index (no ref moves, the working
# tree is untouched), so base's tree is exactly toy_files, whatever HEAD and the index held before;
# (2) each case commits only the file it changes (`git add -- "$1"` in change_on_base, map_after and
# main_moves; `git commit -a` in the record part stages only tracked files), so a left-behind file
# enters no commit; (3) tools/merge_check.sh reads only commits and tracked files (`git diff <base>
# HEAD`, `git ls-files`, `git status --untracked-files=no`), so an untracked file changes none of
# its output; clippy compiles the toy, but the left-behind files are .txt files no crate includes.
# A left-behind file is then reported by name below, and the run goes on; a case that appends to
# one (map_after new.txt) still adds it as a new file, since base does not hold it.
# A file written above but missing from toy_files is not in base: the cases that read it fail, and
# the note below names it on every run.
# Checked by: a run with a new.txt planted at the root failed that case with the old base (rc 1,
# 45 of 46 ok) and passes with this one; the same with data/new.txt in the record part.
toy_files=(
  .gitignore Cargo.toml
  crates/a/Cargo.toml crates/a/src/lib.rs
  crates/b/Cargo.toml crates/b/src/lib.rs crates/b/src/m/mod.rs crates/b/src/gen.rs
  crates/c/Cargo.toml crates/c/src/lib.rs crates/c/src/inl.rs crates/c/src/m/mod.rs crates/c/data/table.rs
  crates/tool/Cargo.toml crates/tool/src/lib.rs crates/rootuse/Cargo.toml crates/rootuse/src/lib.rs
  crates/lnk/Cargo.toml crates/lnk/src/lib.rs crates/feat/Cargo.toml crates/feat/src/lib.rs
  tests/Cargo.toml tests/src/lib.rs tests/src/seed.rs tests/src/helper.rs tests/src/wrap.rs
  tests/src/viamod.rs tests/src/inl.rs tests/src/nest.rs
  tests/steps/x/mod.rs tests/steps/y/mod.rs tests/steps/f/feat.rs tests/full/main.rs tests/full/w/mod.rs tests/full/z/mod.rs
  tools/spec_groups.sh tools/test_merge_check.sh tools/test_run_tests.sh tools/test_lib.sh tools/run_tests.sh
  tools/check_changed_docs.sh
  docs/notes.md docs/plan.md data/notes.txt
)
git read-tree --empty
git add -- "${toy_files[@]}" || exit 1
git commit -q --allow-empty -m base
git tag -f base >/dev/null
mapfile -t stray < <(git ls-files --others --exclude-standard)
# The toy's path relative to the checkout's root: $ws is the path under zrun's fixed mount, which
# outside zrun can name another worktree's toy.
[ ${#stray[@]} -eq 0 ] ||
  printf 'test_merge_check: files in build/test-merge-check%s of this checkout that no commit holds (left by an earlier run, or missing from toy_files); no case reads them, delete them by hand: %s\n' \
    "${part:+-$part}" "${stray[*]}"
# Commits a change to the file $1 on the base (a line ${2:-// changed}).
change_on_base() {
  git checkout -q --detach base
  echo "${2:-// changed}" >>"$1"
  git add -- "$1"
  git commit -q -m "change $1"
}
# Commits a change as change_on_base does and prints the selection's last line. A case that runs
# the full check itself calls change_on_base alone: a --groups run whose output is dropped costs a
# whole merge_check call (MERGE-selftest-time).
groups_after() {
  change_on_base "$@"
  "$check_script" --base base --groups 2>&1 | command grep -a -E '^merge check: (groups|no package)'
}
short() { local g; for g in "$@"; do printf ' %s short-%s' "$g" "$g"; done; }
sorted() { tr ' ' '\n' <<<"$*" | command grep -a . | sort | paste -sd' '; }
# The calls of tools/run_tests.sh that listed or ran pieces since calls last ran (the stub appends
# each call to $STUB_CALLS, as the check writes the calls' output to log files), with --trace and
# its directory taken out; the build of step 0b (--logs) is left out. A check calls the stub for
# each kind once to list the pieces, with its jobs, then once for each chunk, with jobs 1.
export STUB_CALLS=$ws/target/stub-calls
: >"$STUB_CALLS"
# The toy's pieces run here, in chunks (run_chunks), not on Colab VMs (tools/farm_run.sh, which
# tools/test_farm_run.sh tests on a toy of its own).
export MERGE_CHECK_FARM=local
# The runs of main_watch the check reads piece times from (MERGE_CHECK_TIMES_FROM): one toy run
# that times every piece p-<group> of the toy's groups at 5 ms, so that no piece is of unknown
# time (each of which would be a chunk alone) and each kind's pieces make one chunk.
export MERGE_CHECK_TIMES_FROM=$ws/target/stub-main-watch
mkdir -p "$MERGE_CHECK_TIMES_FROM/run/test.logs/1"
for g in a b c feat feat_f lnk rootuse s_01f_import_graph step_x step_y sx t tool w z; do
  for p in "$g" "short-$g" "full-$g" "full-short-$g"; do echo "p-$p rc=0 5ms load=0 limit=1s wait=0ms"; done
done >"$MERGE_CHECK_TIMES_FROM/run/test.logs/1/summary"
calls() { command grep -a -v '^run_tests --logs ' "$STUB_CALLS" | sed 's/ --trace [^ ]*//'; : >"$STUB_CALLS"; }
# The two calls of one kind with one chunk: list, then run, the pieces --only '^($2)$' selects
# ($2 a list of groups joined by |), with jobs $3 for the list (6 by default); $1 is --full or
# empty. The run takes the list's lines with --pieces, or, when a short-addresses group is among
# them, selects again with --only (One listing in tools/merge_check.sh).
two_calls() {
  printf 'run_tests %s--skip-other-kind --list --only ^(%s)$ %s\n' "${1:+$1 }" "$2" "${3:-6}"
  case "|$2" in
  *'|short-'*) printf 'run_tests %s--skip-other-kind --only ^(%s)$ 1\n' "${1:+$1 }" "$2" ;;
  *) printf 'run_tests %s--pieces %s/1.lines 1\n' "${1:+$1 }" \
    "$(git rev-parse --path-format=absolute --git-path "merge-check-chunks${1:+-full}")" ;;
  esac
}

# The part select (not indented, to keep the cases' lines as they were).
if [ "$part" = select ]; then
check "a crate's source selects it, its dependents and s_01f, not the crate beside it" \
  "merge check: groups: $(sorted "$(short a b s_01f_import_graph step_x step_y t)")" \
  "$(groups_after crates/a/src/lib.rs)"
check "a crate no one depends on selects its own unit tests and s_01f" \
  "merge check: groups: $(sorted "$(short c s_01f_import_graph)")" \
  "$(groups_after crates/c/src/lib.rs)"
# TOOL-run-tests-empty-filter: short-<group> only for a group with a short-addresses piece.
check "a selected group gets short-<group> only when tools/run_tests.sh --short-groups names it" \
  "merge check: groups: $(sorted c s_01f_import_graph short-c)" \
  "$(STUB_SHORT=c groups_after crates/c/src/lib.rs)"
check "a file in a step folder selects that step alone" \
  "merge check: groups: $(sorted "$(short step_x)")" \
  "$(groups_after tests/steps/x/mod.rs)"
check "a file another crate includes by #[path] selects that crate and its dependents too" \
  "merge check: groups: $(sorted "$(short a b s_01f_import_graph step_x step_y t)")" \
  "$(groups_after tests/src/seed.rs)"
check "a file a mod.rs names by #[path] selects the crate of the mod.rs and its dependents" \
  "merge check: groups: $(sorted "$(short b s_01f_import_graph step_x step_y t)")" \
  "$(groups_after tests/src/viamod.rs)"
check "a file a #[path] inside an inline module of a non-mod.rs file names selects its crate" \
  "merge check: groups: $(sorted "$(short c s_01f_import_graph step_x step_y t)")" \
  "$(groups_after tests/src/inl.rs)"
check "a file a #[path] inside two inline modules of a mod.rs file names selects its crate" \
  "merge check: groups: $(sorted "$(short c s_01f_import_graph step_x step_y t)")" \
  "$(groups_after tests/src/nest.rs)"
check "a file in a sibling crate's directory that include! names selects the including crate too" \
  "merge check: groups: $(sorted "$(short b c s_01f_import_graph step_x step_y t)")" \
  "$(groups_after crates/c/data/table.rs)"
check "a docs file selects nothing" \
  "merge check: no package changed; no tests to run" \
  "$(groups_after docs/notes.md)"
check "the workspace manifest selects every package" \
  "merge check: groups: $(sorted "$(short a b c feat feat_f lnk rootuse step_x step_y t tool)")" \
  "$(groups_after Cargo.toml '# changed')"
# MERGE-target-path-dots: cargo metadata names feat_f's main file crates/feat/../../tests/steps/f/feat.rs.
check "a file of a test target whose manifest names it through .. selects that target" \
  "merge check: groups: $(sorted "$(short feat_f)")" \
  "$(groups_after tests/steps/f/feat.rs)"
# MERGE-runner-selects-all: every piece runs under the runner, which no crate compiles.
check "a change to tools/run_tests.sh selects every local group" \
  "merge check: groups: $(sorted "$(short a b c feat feat_f lnk rootuse step_x step_y t tool)")" \
  "$(groups_after tools/run_tests.sh '# changed')"
check "a change to tools/lib.sh, which tools/run_tests.sh sources, selects every local group" \
  "merge check: groups: $(sorted "$(short a b c feat feat_f lnk rootuse step_x step_y t tool)")" \
  "$(groups_after tools/lib.sh '# changed')"
# The narrowing of step 2 (MERGE-dep-by-target).
check "a crate the package of tests/full depends on, named by one step alone, selects that step alone" \
  "merge check: groups: $(sorted "$(short s_01f_import_graph step_x tool)")" \
  "$(groups_after crates/tool/src/lib.rs)"
check "a crate named only in comments of the package of tests/full selects none of its targets" \
  "merge check: groups: $(sorted "$(short feat feat_f s_01f_import_graph)")" \
  "$(groups_after crates/feat/src/lib.rs)"
check "a crate the root of that package's lib names selects the package whole" \
  "merge check: groups: $(sorted "$(short rootuse s_01f_import_graph step_x step_y t)")" \
  "$(groups_after crates/rootuse/src/lib.rs)"
check "a crate that exports a symbol selects the package whole" \
  "merge check: groups: $(sorted "$(short lnk s_01f_import_graph step_x step_y t)")" \
  "$(groups_after crates/lnk/src/lib.rs)"
git checkout -q --detach base
printf '//! lnk.\npub fn lnk_f() {}\n' >crates/lnk/src/lib.rs
git commit -q -a -m "lnk: export nothing"
check "a crate that exported a symbol at the base selects the package whole" \
  "merge check: groups: $(sorted "$(short lnk s_01f_import_graph step_x step_y t)")" \
  "$("$check_script" --base base --groups 2>&1 | command grep -a -E '^merge check: groups')"
# Step 0a: tool asks for feat without its default features, which t gives it in the workspace
# build. Cargo's "Blocking waiting for file lock" lines, indented as the report's are, appear
# when another build holds the lock, and are dropped.
git checkout -q --detach base
printf '\n[dependencies]\nfeat = { path = "../feat", default-features = false }\n' >>crates/tool/Cargo.toml
git commit -q -a -m "tool: depend on feat without its defaults"
check "a manifest that gives a package alone other features than the workspace build fails the check" \
  "merge check: a manifest or Cargo.lock changed, and these packages, built alone, get features the workspace build does not give them (tools/run_tests.sh refuses to build them so):
  tool:
    feat v0.0.0 ($ws/crates/feat) []
merge check: FAILED
1" "$("$check_script" --base base 2>&1 | command grep -a -E '^(merge check: (a manifest|FAILED)|  )' |
  command grep -a -v 'Blocking waiting for file lock'; echo "${PIPESTATUS[0]}")"
git checkout -q --detach base
printf '\n[dependencies]\nfeat = { path = "../feat" }\n' >>crates/tool/Cargo.toml
git commit -q -a -m "tool: depend on feat with its defaults"
check "a manifest that gives every package the workspace build's features passes step 0a" \
  "merge check: a manifest or Cargo.lock changed: every package, built alone, gets the features the workspace build gives it
merge check: passed" \
  "$("$check_script" --base base 2>&1 | command grep -a -E '^merge check: (a manifest|passed|FAILED)')"
git checkout -q --detach base
echo "// changed" >>crates/c/src/lib.rs
git commit -q -a -m "change c"
check "a passing run passes the anchored selection to tools/run_tests.sh" \
  "merge check: passed
0
$(two_calls '' "$(sorted "$(short c s_01f_import_graph)" | tr ' ' '|')" 3)" \
  "$(calls >/dev/null; "$check_script" --base base 3 2>&1 | command grep -a -E '^merge check: (passed|FAILED)'; echo "${PIPESTATUS[0]}"; calls)"
check "a failing test run stops the check with exit 1" "merge check: FAILED: tests (above)
1" "$(STUB_RC=1 "$check_script" --base base 2>&1 | command grep -a 'FAILED'; echo "${PIPESTATUS[0]}")"
# Step 1a (TOOLS-merge-check-clippy): clippy -D warnings on the selected packages, before the tests.
clippy_run() {
  # The lint's name, from clippy's line "to override `-D warnings` add `#[allow(<lint>)]`".
  calls >/dev/null
  "$check_script" --base base 2>&1 |
    command grep -a -o -E '^merge check: (clippy|passed|FAILED).*|#\[allow\([a-z_:]+\)\]'
  echo "${PIPESTATUS[0]}"
  calls
}
# The commit "change c", which the case after these returns to.
change_c=$(git rev-parse HEAD)
check "a clean branch passes clippy on its selected packages, then runs its tests" \
  "merge check: clippy -D warnings on: c
merge check: passed
0
$(two_calls '' "$(sorted "$(short c s_01f_import_graph)" | tr ' ' '|')")" "$(clippy_run)"
change_on_base crates/c/src/lib.rs 'pub fn n(v: &Vec<u8>) -> usize { v.len() }'
check "a branch with a clippy warning is refused with exit 1, and its tests do not run" \
  "merge check: clippy -D warnings on: c
#[allow(clippy::ptr_arg)]
merge check: FAILED: clippy (above)
1" "$(clippy_run)"
git checkout -q --detach base
printf '#[cfg(test)]\n#[path = "../../../tests/src/seed.rs"]\nmod seed;\n#[deprecated]\npub fn f() {}\n' >crates/a/src/lib.rs
git commit -q -a -m "a: deprecate f"
check "a change that makes a dependent warn (b calls the now deprecated a::f) is refused" \
  "merge check: clippy -D warnings on: a b t
#[allow(deprecated)]
merge check: FAILED: clippy (above)
1" "$(clippy_run)"
change_on_base tests/steps/x/mod.rs
check "a test target changed alone has clippy run on its package" \
  "merge check: clippy -D warnings on: t" "$(clippy_run | command grep -a 'clippy')"
# Step 2's narrowing leaves t out of the closure when none of its own files changed, and selects
# its test targets by use (TOOLS-clippy-cold-per-worktree). A case built to fail if that dropped a
# test target clippy must see: step_x calls tool::d, which only step_x names, and the branch
# deprecates d.
git checkout -q --detach base
printf '//! tool.\npub fn d() {}\n' >crates/tool/src/lib.rs
printf '\n#[test]\nfn calls_d() {\n    tool::d();\n}\n' >>tests/steps/x/mod.rs
git commit -q -a -m "step_x calls tool::d"
calls_d=$(git rev-parse HEAD)
printf '//! tool.\n#[deprecated]\npub fn d() {}\n' >crates/tool/src/lib.rs
git commit -q -a -m "tool: deprecate d"
check "a change to a crate that only a test target of t names has clippy run on t, which refuses the warning there" \
  "merge check: clippy -D warnings on: tool t
#[allow(deprecated)]
merge check: FAILED: clippy (above)
1" "$("$check_script" --base "$calls_d" 2>&1 |
    command grep -a -o -E '^(run_tests.*|merge check: (clippy|passed|FAILED).*)|#\[allow\([a-z_:]+\)\]'
    echo "${PIPESTATUS[0]}")"
change_on_base clippy.toml '# changed'
check "the root's clippy.toml selects every package for clippy and no test" \
  "merge check: the root's clippy configuration changed: clippy runs on every package
merge check: groups:
merge check: clippy -D warnings on: a b c feat lnk rootuse tool t
merge check: passed
0" "$("$check_script" --base base 2>&1 | command grep -a -E '^merge check: (groups|the root|clippy|passed|FAILED|no package)'
    echo "${PIPESTATUS[0]}")"
git checkout -q --detach "$change_c"
echo "// uncommitted" >>crates/c/src/lib.rs
check "uncommitted changes to tracked files stop the check" "1" \
  "$("$check_script" --base base --groups >/dev/null 2>&1; echo $?)"
printf '//! c.\n// changed\n' >crates/c/src/lib.rs
git checkout -q --detach base
check "a file moved from one package to another selects both" \
  "merge check: groups: $(sorted "$(short a b c s_01f_import_graph step_x step_y t)")" \
  "$(git mv crates/c/src/inl.rs crates/a/src/inl.rs && git commit -q -m move &&
    "$check_script" --base base --groups 2>&1 | command grep -a -E '^merge check: groups')"
# Back to base, which removes the moved file: left in the tree, the next run's new base would not
# hold it, and the check for files no commit holds would stop that run.
git checkout -q --detach base
fi

# Part select2: the second half of the cases of selection, from here, a part of its own since
# with the chunks of step 2b (MERGE-full-run-split) the whole took 37 s at load 58, past the limit
# of 36 s that step 0 gives a part at that load. They use nothing the cases above set.
if [ "$part" = select2 ]; then
# tests/full (MERGE-runtime-inputs): a piece's folder selects that piece alone, run with --full
# under its name full-<piece>; its main.rs selects every piece; neither selects the package t.
# A change that reaches t through its dependencies selects every piece (MERGE-full-by-dependency).
full_run() {
  change_on_base "$1"
  calls >/dev/null
  "$check_script" --base base 2>&1 | command grep -a -E '^merge check: (groups|tests/full|passed)'
  calls
}
check "a file in a piece's folder of tests/full selects that piece alone, run with --full" \
  "merge check: groups:
merge check: tests/full pieces: z
merge check: passed
$(two_calls --full full-z)" "$(full_run tests/full/z/mod.rs)"
check "tests/full/main.rs selects every piece of tests/full" \
  "merge check: groups:
merge check: tests/full pieces: w z
merge check: passed
$(two_calls --full 'full-w|full-z')" "$(full_run tests/full/main.rs)"
all_b=$(sorted "$(short b s_01f_import_graph step_x step_y t)")
check "a crate that a step helper of the package of tests/full names selects every target and piece using the helper, the pieces run with --full after the local groups" \
  "merge check: groups: $all_b
merge check: tests/full pieces: w
merge check: passed
$(two_calls '' "$(tr ' ' '|' <<<"$all_b")")
$(two_calls --full full-w)" "$(full_run crates/b/src/lib.rs)"
check "a crate the package of tests/full does not depend on selects no piece" \
  "merge check: groups: $(sorted "$(short c s_01f_import_graph)")" \
  "$(full_run crates/c/src/lib.rs | command grep -a -E '^merge check: (groups|tests/full)')"
check "a failing run of tests/full stops the check with exit 1" "merge check: FAILED: tests/full (above)
1" "$(change_on_base tests/full/w/mod.rs
    STUB_RC=1 "$check_script" --base base 2>&1 | command grep -a 'FAILED'; echo "${PIPESTATUS[0]}")"
# The self-tests (MERGE-tools-self-tests): a change to tools/run_tests.sh runs all parts of
# tools/test_merge_check.sh; a part that fails refuses the branch.
check "a change to tools/run_tests.sh runs all parts of tools/test_merge_check.sh and every part of tools/test_run_tests.sh" \
  "merge check: a file of the test runner changed (tools/run_tests.sh, tools/lib.sh or tools/merge_check.sh): every local group
merge check: a file tools/test_merge_check.sh tests changed: all its parts run
merge check: a file tools/test_run_tests.sh tests changed: all its parts run
merge check: tools/test_merge_check.sh select, select2, record and chunks passed
merge check: tools/test_run_tests.sh list, select, table, except, benches, fresh, short, copy, concurrent, trace and nobus passed
merge check: passed
0" "$(change_on_base tools/run_tests.sh '# changed'
    "$check_script" --base base 2>&1 | command grep -a -E '^merge check: (a file|tools|passed|FAILED)'
    echo "${PIPESTATUS[0]}")"
check "a failing part of tools/test_merge_check.sh refuses the branch with exit 1" \
  "self select
FAILED: tools/test_merge_check.sh select, rc=1
1" "$(STUB_SELF_FAIL=select "$check_script" --base base 2>&1 |
    command grep -a -o -E '^self select|FAILED: tools/test_merge_check.sh [a-z]+, rc=[0-9]+'
    echo "${PIPESTATUS[0]}")"
# Step 0b (TOOL-merge-check-run-tests-self): each failing part of tools/test_run_tests.sh refuses
# the branch; a failing list also stops select, table, except and benches, which read its table,
# and short, which starts after it, and a failing table stops except and benches, which run after
# it, as a failing except stops benches; those show as
# failed with empty logs, not with the passing logs of the run before.
for p in list table except trace; do
  want="merge check: FAILED: tools/test_run_tests.sh $p"
  [ $p = list ] && want="$want
merge check: FAILED: tools/test_run_tests.sh select
merge check: FAILED: tools/test_run_tests.sh table
merge check: FAILED: tools/test_run_tests.sh except
merge check: FAILED: tools/test_run_tests.sh benches
merge check: FAILED: tools/test_run_tests.sh short"
  [ $p = except ] && want="$want
merge check: FAILED: tools/test_run_tests.sh benches"
  [ $p = table ] && want="$want
merge check: FAILED: tools/test_run_tests.sh except
merge check: FAILED: tools/test_run_tests.sh benches"
  check "a failing part $p of tools/test_run_tests.sh refuses the branch with exit 1" "$want
1" "$(STUB_RT_FAIL=$p "$check_script" --base base 2>&1 |
    command grep -a -o -E '^merge check: FAILED: tools/test_run_tests.sh [a-z]+'
    echo "${PIPESTATUS[0]}")"
done
check "a failing build before the parts of tools/test_run_tests.sh refuses the branch, and no part runs" \
  "merge check: FAILED: the build for tools/test_run_tests.sh
1" "$(STUB_RC=1 "$check_script" --base base 2>&1 |
    command grep -a -o -E '^merge check: FAILED: [a-z ]*tools/test_run_tests.sh( [a-z]+)?'
    echo "${PIPESTATUS[0]}")"
check "a change to tools/test_run_tests.sh alone runs its parts, not tools/test_merge_check.sh" \
  "merge check: a file tools/test_run_tests.sh tests changed: all its parts run
merge check: tools/test_run_tests.sh list, select, table, except, benches, fresh, short, copy, concurrent, trace and nobus passed
merge check: passed
0" "$(change_on_base tools/test_run_tests.sh '# changed'
    "$check_script" --base base 2>&1 | command grep -a -E '^merge check: (a file|tools|passed|FAILED)'
    echo "${PIPESTATUS[0]}")"
# Step 0's parts are timed, so they start only once step 0b's build (which has no limit) has ended.
check "the build for tools/test_run_tests.sh ends before the timed parts of tools/test_merge_check.sh start" \
  "merge check: tools/test_merge_check.sh select, select2, record and chunks passed
merge check: tools/test_run_tests.sh list, select, table, except, benches, fresh, short, copy, concurrent, trace and nobus passed
merge check: passed
0" "$(change_on_base tools/test_lib.sh '# changed'
    STUB_BUILD_MARK=$ws/target/built-$$-$SECONDS "$check_script" --base base 2>&1 |
      command grep -a -E '^merge check: (tools|passed|FAILED)'
    echo "${PIPESTATUS[0]}")"
check "a change to tools/test_lib.sh runs both test scripts" \
  "merge check: a file tools/test_merge_check.sh tests changed: all its parts run
merge check: a file tools/test_run_tests.sh tests changed: all its parts run" \
  "$(change_on_base tools/test_lib.sh '# changed'
    "$check_script" --base base --list 2>&1 | command grep -a -E '^merge check: a file')"
# The map of run-time reads (step 2a): group c read docs/plan.md, step_y listed data, t stat'ed
# the root, the piece z of tests/full read docs/plan.md; gone, no longer a group of the
# workspace, read docs/plan.md too, and so did full-gone, no longer a piece.
map=$ws/target/map
mkdir -p "$map"
printf 'commit 0\ndocs/plan.md\n' >"$map/c.reads"
printf 'commit 0\ndata\n' >"$map/step_y.reads"
printf 'commit 0\n.\n' >"$map/t.reads"
printf 'commit 0\ndocs/plan.md\n' >"$map/gone.reads"
printf 'commit 0\ndocs/plan.md\n' >"$map/full-z.reads"
printf 'commit 0\ndocs/plan.md\n' >"$map/full-gone.reads"
# Commits a change to the file $1 on the base and prints the map's and the selection's lines.
map_after() {
  git checkout -q --detach base
  mkdir -p "$(dirname "$1")"
  echo "${2:-// changed}" >>"$1"
  git add -- "$1"
  git commit -q -m "change $1"
  "$check_script" --base base --reads "$map" --groups 2>&1 |
    command grep -a -E '^merge check: (groups|the map|no package|tests/full)' | sed "s|$map|MAP|"
}
uncovered="merge check: the map has no reads of 8 groups, which only compilation selects: a b feat feat_f lnk rootuse step_x tool
merge check: the map has no reads of 1 tests/full pieces, which only compilation selects: w"
check "a file that a group and a piece of tests/full read at run time selects both, by the map" \
  "merge check: groups that read at run time a path the change can affect (map MAP): c; tests/full pieces: z
$uncovered
merge check: groups: c
merge check: tests/full pieces: z" "$(map_after docs/plan.md)"
check "a file changed in a directory a group listed selects nothing" \
  "merge check: groups that read at run time a path the change can affect (map MAP):
$uncovered
merge check: no package changed; no tests to run" "$(map_after data/notes.txt)"
check "a file added in a new directory under a directory a group listed selects that group, not the root's" \
  "merge check: groups that read at run time a path the change can affect (map MAP): step_y
$uncovered
merge check: groups: step_y" "$(map_after data/sub/new.txt)"
check "a file added at the root selects the group that stat'ed the root" \
  "merge check: groups that read at run time a path the change can affect (map MAP): t
$uncovered
merge check: groups: t" "$(map_after new.txt)"
git checkout -q --detach base
fi

# The part record (not indented either).
if [ "$part" = record ]; then
# The record (MERGE-push-race). The branch changes crate c; main then moves, and the branch is
# rebased on it (a cherry-pick of its commit), as wt/merge-push.sh does after a refused push.
# At run time group c reads docs/plan.md, s_01f_import_graph lists the directory crates and
# short-c the directory data; later short-s_01f_import_graph reads `*`, anything.
mkdir -p "$ws/target"
rec=$ws/target/record
: >"$rec"
export STUB_READS=$ws/target/stub-reads
printf 'c docs/plan.md\ns_01f_import_graph crates\nshort-c data\n' >"$STUB_READS"
echo "// changed" >>crates/c/src/lib.rs
git commit -q -a -m "branch: change c"
git tag -f branch >/dev/null
all_c="$(sorted "$(short c s_01f_import_graph)")"
# Runs the check with the record against the base $1, plus any further arguments, and prints
# what ran, the outcome and the exit code, then the calls of tools/run_tests.sh; with show_clippy
# set, step 1a's lines too.
record_run() {
  calls >/dev/null
  "$check_script" --base "$1" --record "$rec" "${@:2}" 2>&1 |
    command grep -a -E "^merge check: (to run|tests/full pieces to run|${show_clippy:+clippy|}passed|FAILED)"
  echo "${PIPESTATUS[0]}"
  calls
}
# Moves main, the tag upstream (the toy repository's branch main is another ref), on by a change
# to the file $1 and rebases the branch on it.
git tag -f upstream base >/dev/null
main_moves() {
  git checkout -q --detach upstream
  echo "${2:-// changed}" >>"$1"
  git add -- "$1"
  git commit -q -m "main: change $1"
  git tag -f upstream >/dev/null
  git cherry-pick branch >/dev/null
}
check "with no record, every selected group runs, and clippy on every selected package, and the record is written" \
  "merge check: to run: $all_c
merge check: clippy to run: c
merge check: clippy -D warnings on: c
merge check: passed
0
$(two_calls '' "$(tr ' ' '|' <<<"$all_c")")" "$(show_clippy=1 record_run base --reads "$ws/target/map-record")"
check "a passing run writes the map file of each group that ran, from the trace" "commit $(git rev-parse HEAD)
docs/plan.md
commit $(git rev-parse HEAD)
data" "$(cat "$ws/target/map-record/c.reads" "$ws/target/map-record/short-c.reads")"
check "the record names the commit, the spec's commit, the groups and what each read" "$(git rev-parse HEAD)
spec $(git -C "$ZED_SPEC_DIR" rev-parse HEAD)
group c
group s_01f_import_graph
group short-c
group short-s_01f_import_graph
clippy c
read c docs/plan.md
read s_01f_import_graph crates
read short-c data
end" "$(cat "$rec")"
check "the same commit again runs nothing, clippy neither" "merge check: to run:
merge check: clippy to run:
merge check: passed (every selected group passed at the record's commit, with the same inputs)
0" "$(show_clippy=1 record_run base)"
main_moves docs/notes.md
check "main moved by a file no group read: nothing runs" "merge check: to run:
merge check: passed (every selected group passed at the record's commit, with the same inputs)
0" "$(record_run upstream)"
check "the record now names the rebased commit" "$(git rev-parse HEAD)" "$(head -n 1 "$rec")"
main_moves docs/plan.md
check "main moved by a file a group read at run time: that group runs" "merge check: to run: c
merge check: passed
0
$(two_calls '' "c")" "$(record_run upstream)"
check "the group that ran keeps its reads in the new record" "read c docs/plan.md
read s_01f_import_graph crates
read short-c data" "$(command grep -a '^read' "$rec")"
main_moves crates/a/src/lib.rs
check "main moved by a crate the branch's crate does not use: only s_01f, which any crate selects, and no clippy" \
  "merge check: to run: $(sorted "$(short s_01f_import_graph)")
merge check: clippy to run:" \
  "$(show_clippy=1 record_run upstream | command grep -a 'to run')"
passed_at=$(head -n 1 "$rec")
main_moves crates/c/src/inl.rs
check "main changed the branch's crate: clippy runs on it, a failing run exits 1 and keeps the old record" \
  "merge check: to run: $all_c
merge check: clippy to run: c
merge check: clippy -D warnings on: c
merge check: FAILED: tests (above)
1
$passed_at" \
  "$(STUB_RC=1 show_clippy=1 record_run upstream | command grep -a -v '^run_tests'; head -n 1 "$rec")"
echo 'short-s_01f_import_graph *' >>"$STUB_READS"
check "then a passing run runs the same groups and writes the record" "merge check: to run: $all_c
$(git rev-parse HEAD)" \
  "$(record_run upstream | command grep -a 'to run'; head -n 1 "$rec")"
main_moves data/notes.txt
check "a file changed under a directory a group listed: that group does not run; a group that read * does" \
  "merge check: to run: short-s_01f_import_graph" "$(record_run upstream | command grep -a 'to run')"
main_moves data/new.txt
check "a file added under a directory a group listed: that group runs" \
  "merge check: to run: short-c short-s_01f_import_graph" "$(record_run upstream | command grep -a 'to run')"
main_moves tools/run_tests.sh '# changed'
check "a change under tools/ since the record runs every selected group, and clippy on every selected package" \
  "merge check: to run: $all_c
merge check: clippy to run: c" "$(show_clippy=1 record_run upstream | command grep -a 'to run')"
printf '%s\n' "$(head -n 2 "$rec")" >"$rec"
check "a record cut short is ignored" "merge check: to run: $all_c" \
  "$(record_run upstream --groups | command grep -a 'to run')"
# The pieces of tests/full in the record (MERGE-full-by-dependency): a branch that changes crate c
# and the piece z runs the local groups, then z with --full, each with a trace directory of its
# own, and records both; full-z read docs/plan.md.
rec=$ws/target/record-full
: >"$rec"
echo 'full-z docs/plan.md' >>"$STUB_READS"
git checkout -q --detach base
git tag -f upstream base >/dev/null
echo "// changed" >>crates/c/src/lib.rs
echo "// changed" >>tests/full/z/mod.rs
git commit -q -a -m "branch: change c and the piece z"
git tag -f branch >/dev/null
check "local groups and a piece of tests/full run in two calls, the second with --full" \
  "merge check: to run: $all_c
merge check: tests/full pieces to run: z
merge check: passed
0
$(two_calls '' "$(tr ' ' '|' <<<"$all_c")")
$(two_calls --full "full-z")" "$(record_run base --reads "$ws/target/map-full")"
check "the record holds the piece of tests/full and what it read, from the trace of its own call" \
  "group full-z
read c docs/plan.md
read full-z docs/plan.md" "$(command grep -a -E '^(group full-z|read (c|full-z) )' "$rec")"
check "and the map file of the piece is written" "commit $(git rev-parse HEAD)
docs/plan.md" "$(cat "$ws/target/map-full/full-z.reads")"
check "the same commit again runs neither" "merge check: to run:
merge check: passed (every selected group passed at the record's commit, with the same inputs)
0" "$(record_run base)"
main_moves docs/plan.md
check "main moved by a file the piece read at run time: the piece runs again with --full" \
  "merge check: to run: c short-s_01f_import_graph
merge check: tests/full pieces to run: z
merge check: passed
0
$(two_calls '' "c|short-s_01f_import_graph")
$(two_calls --full "full-z")" "$(record_run upstream)"
# A group whose pieces read a file of the spec checkout must be one tools/spec_groups.sh names
# (MERGE-spec-reads-map): in the toy step_x, not short-step_x (the toy has no short_steps).
rec=$ws/target/record-spec
: >"$rec"
git checkout -q --detach base
echo "// changed" >>tests/steps/x/mod.rs
git commit -q -a -m "branch: change the step x"
sx=$(sorted "$(short step_x)")
echo 'step_x spec:DESIGN.md' >>"$STUB_READS"
check "a group that read the spec and that spec_groups.sh names passes" "merge check: to run: $sx
merge check: passed
0
$(two_calls '' "$(tr ' ' '|' <<<"$sx")")" "$(record_run base)"
: >"$rec"
echo 'short-step_x spec:EXAMPLES.md' >>"$STUB_READS"
check "a group that read the spec and that spec_groups.sh does not name fails, and no record is written" \
  "merge check: to run: $sx
merge check: FAILED: tools/spec_groups.sh (above)
1
$(two_calls '' "$(tr ' ' '|' <<<"$sx")")" "$(record_run base; cat "$rec")"
# The spec's commit in the record (MERGE-spec-push-check): a group that read the spec runs again
# when the spec checkout moved since the record or has uncommitted changes, and only then.
command grep -a -v '^short-step_x ' "$STUB_READS" >"$STUB_READS-2"
export STUB_READS=$STUB_READS-2
record_run base >/dev/null
check "the record names the spec's commit" "spec $(git -C "$ZED_SPEC_DIR" rev-parse HEAD)" \
  "$(sed -n 2p "$rec")"
check "the spec unmoved: nothing runs" "merge check: to run:" \
  "$(record_run base | command grep -a 'to run')"
echo "more" >>"$ZED_SPEC_DIR/DESIGN.md"
git -C "$ZED_SPEC_DIR" commit -q -a -m "spec: more"
check "the spec moved: the group that read it runs, the other does not, and the record names the new commit" \
  "merge check: to run: step_x
merge check: passed
0
$(two_calls '' "step_x")
spec $(git -C "$ZED_SPEC_DIR" rev-parse HEAD)" "$(record_run base; sed -n 2p "$rec")"
echo "uncommitted" >>"$ZED_SPEC_DIR/DESIGN.md"
check "the spec has uncommitted changes: the group that read it runs, and the record names no spec commit" \
  "merge check: to run: step_x
group short-step_x" "$(record_run base | command grep -a 'to run'; sed -n 2p "$rec")"
git -C "$ZED_SPEC_DIR" checkout -q DESIGN.md
check "then with the spec clean again, the record's unknown spec commit runs it once more" \
  "merge check: to run: step_x" "$(record_run base | command grep -a 'to run')"
check "and then nothing" "merge check: to run:" "$(record_run base | command grep -a 'to run')"
fi

if [ "$part" = chunks ]; then
# Part chunks: the chunks of step 2b (MERGE-full-run-split), a part of their own since they took
# the record part from 18 to 40 s at load 44, past the limit of 27.5 s that step 0 gives a part at
# that load. Crate c has three pieces, c (named after its group, as a step folder's rest is), c::x
# and c::y, each 20 s by the times of an earlier check, so with chunks of up to 30 s each is a
# chunk, and c::y shares its chunk with the three pieces p-<group>, 5 ms each by the toy's run of
# main_watch. A chunk runs the list call's lines of its pieces with --pieces, so it lists nothing
# (One listing in tools/merge_check.sh); the chunk with the short-addresses group short-c names its
# terms in --only and the other pieces those terms select in --except. The chunks run at once, so
# their calls are compared sorted.
pieces=$ws/target/stub-pieces
cdir=$(git rev-parse --path-format=absolute --git-path merge-check-chunks)
# The toy is kept from run to run: empty the files of an earlier run, which would pass the check of
# the chunks' --pieces files below for a merge check that writes none.
mkdir -p "$cdir" && : >"$cdir/1.lines" && : >"$cdir/2.lines"
printf 'c c c\nc c c::x\nc c c::y\n' >"$pieces"
times=$(git rev-parse --path-format=absolute --git-common-dir)/merge-check-times
slow_times() { printf 'c 20000\nc::x 20000\nc::y 20000\n' >"$times"; }
git checkout -q --detach base
echo "// changed" >>crates/c/src/lib.rs
git commit -q -a -m "branch: change c, for the chunks"
# Runs the check, after $1 (slow_times by default) wrote the times, and prints its lines about
# the chunks and the outcome, without their times in seconds, and its exit code.
chunk_run() {
  ${1:-slow_times}
  calls >/dev/null
  STUB_PIECES=$pieces "$check_script" --base base 2>&1 |
    command grep -a -E '^(merge check: (.*chunks?|pieces|passed|FAILED|run by|the chunks)|c(::[xy])?$)' |
    sed -E 's/ in [0-9]+ s(, stopped)/\1/; s/ in [0-9]+ s$//; s/, in ([0-9]+) chunks, [0-9]+ s$/, in \1 chunks/'
  echo "${PIPESTATUS[0]}"
}
plan="by the times of earlier checks and of main_watch"
check "pieces timed by earlier checks are cut into chunks of up to 30 s, each its own call with jobs 1" \
  "merge check: 6 pieces in 3 chunks of up to 30 s $plan (0 timed by neither, each alone), 6 at once
merge check: chunk 1 of 3: pieces: 1, failed: 0
merge check: chunk 2 of 3: pieces: 1, failed: 0
merge check: chunk 3 of 3: pieces: 4, failed: 0
merge check: pieces: 6, failed: 0, in 3 chunks
merge check: passed
0
run_tests --pieces $cdir/1.lines 1
run_tests --pieces $cdir/2.lines 1
run_tests --skip-other-kind --list --only ^(c|s_01f_import_graph|short-c|short-s_01f_import_graph)\$ 6
run_tests --skip-other-kind --only ^(c|s_01f_import_graph|short-c|short-s_01f_import_graph)\$ --except ^(c|c::x)\$ 1" \
  "$(chunk_run; calls | LC_ALL=C sort)"
check "a chunk's --pieces file is the list's lines of its pieces" "c c /bin/true
c::x c /bin/true" "$(cat "$cdir/1.lines" "$cdir/2.lines")"
check "the check writes each piece's time for the next check's chunks" "c 5
c::x 5
c::y 5
p-s_01f_import_graph 5
p-short-c 5
p-short-s_01f_import_graph 5" "$(cat "$times")"
check "a failing check of the changed docs fails the check before any chunk runs" \
  "merge check: FAILED: the check of the changed documentation (log $cdir/doc-changed.log)
merge check: FAILED: tests (above)
1
run_tests --skip-other-kind --list --only ^(c|s_01f_import_graph|short-c|short-s_01f_import_graph)\$ 6" \
  "$(STUB_DOCS_FAIL=1 chunk_run; calls)"
# The first check, with no times of its own (MERGE-full-run-split, the 60 s hold on the first run
# too): the times of main_watch's runs size the chunks, and c, of 50 s there, is a chunk alone
# while the fast pieces share one, so no chunk is planned past 30 s.
seed50=$ws/target/stub-main-watch-50
mkdir -p "$seed50/run/test.logs/1"
{ cat "$MERGE_CHECK_TIMES_FROM/run/test.logs/1/summary"; printf 'c rc=0 50000ms\nc::x rc=0 100ms\nc::y rc=0 100ms\n'; } \
  >"$seed50/run/test.logs/1/summary"
no_times() { : >"$times"; }
check "with no times of its own, a piece of 50 s by main_watch's runs is a chunk alone and the fast ones share one" \
  "merge check: 6 pieces in 2 chunks of up to 30 s $plan (0 timed by neither, each alone), 6 at once
merge check: chunk 1 of 2: pieces: 1, failed: 0
merge check: chunk 2 of 2: pieces: 5, failed: 0
merge check: pieces: 6, failed: 0, in 2 chunks
merge check: passed
0
run_tests --pieces $cdir/1.lines 1
run_tests --skip-other-kind --list --only ^(c|s_01f_import_graph|short-c|short-s_01f_import_graph)\$ 6
run_tests --skip-other-kind --only ^(c|s_01f_import_graph|short-c|short-s_01f_import_graph)\$ --except ^(c)\$ 1" \
  "$(MERGE_CHECK_TIMES_FROM=$seed50 chunk_run no_times; calls | LC_ALL=C sort)"
# A piece timed by neither is a chunk alone: no guess bounds a chunk of several.
mkdir -p "$ws/target/stub-main-watch-none"
check "with no times anywhere, each piece is a chunk alone" \
  "merge check: 6 pieces in 6 chunks of up to 30 s $plan (6 timed by neither, each alone), 6 at once
merge check: chunk 1 of 6: pieces: 1, failed: 0
merge check: chunk 2 of 6: pieces: 1, failed: 0
merge check: chunk 3 of 6: pieces: 1, failed: 0
merge check: chunk 4 of 6: pieces: 1, failed: 0
merge check: chunk 5 of 6: pieces: 1, failed: 0
merge check: chunk 6 of 6: pieces: 1, failed: 0
merge check: pieces: 6, failed: 0, in 6 chunks
merge check: passed
0" "$(MERGE_CHECK_TIMES_FROM=$ws/target/stub-main-watch-none chunk_run no_times)"
check "a failing piece in one chunk prints as it ends, before the chunks' sums, and fails the check" \
  "merge check: 6 pieces in 3 chunks of up to 30 s $plan (0 timed by neither, each alone), 6 at once
merge check: chunk 2 of 3: failed: c::x rc=1 5ms load=0 limit=1s wait=0ms
merge check: chunk 1 of 3: pieces: 1, failed: 0
merge check: chunk 2 of 3: pieces: 1, failed: 1
merge check: chunk 3 of 3: pieces: 4, failed: 0
merge check: pieces: 6, failed: 1, in 3 chunks
merge check: FAILED: tests (above)
1" "$(STUB_FAIL=c::x chunk_run)"
# The stub stops a hung piece at a limit of 1 s, as tools/run_tests.sh stops one at its limit.
start=$SECONDS
check "a hung piece is stopped at its limit, reported, and fails the check" \
  "merge check: 6 pieces in 3 chunks of up to 30 s $plan (0 timed by neither, each alone), 6 at once
merge check: chunk 3 of 3: failed: c::y rc=124 5ms load=0 limit=1s wait=0ms
merge check: chunk 1 of 3: pieces: 1, failed: 0
merge check: chunk 2 of 3: pieces: 1, failed: 0
merge check: chunk 3 of 3: pieces: 4, failed: 1
merge check: pieces: 6, failed: 1, in 3 chunks
merge check: FAILED: tests (above)
1" "$(STUB_HANG=c::y chunk_run)"
check "and the check ends well before the hung piece would have (30 s)" yes \
  "$([ $((SECONDS - start)) -lt 20 ] && echo yes || echo "no: $((SECONDS - start)) s")"
# A chunk still running at the chunk limit (60 s; 2 s here) is stopped, not waited out: a failure
# printed at once that names its pieces, the pieces that did not end marked *. Each is written
# to the times at twice its estimate, so the next check cuts the chunk smaller.
start=$SECONDS
check "a chunk past the chunk limit is stopped, named with its pieces, and fails the check" \
  "merge check: 6 pieces in 3 chunks of up to 30 s $plan (0 timed by neither, each alone), 6 at once
merge check: chunk 3 of 3: FAILED: over 2 s, stopped; its pieces (estimate in ms; * did not end): c::y* 20000, p-s_01f_import_graph* 5, p-short-c* 5, p-short-s_01f_import_graph* 5
merge check: chunk 1 of 3: pieces: 1, failed: 0
merge check: chunk 2 of 3: pieces: 1, failed: 0
merge check: chunk 3 of 3: no result, stopped at 2 s (named above)
merge check: pieces: 2, failed: 0, in 3 chunks
merge check: FAILED: tests (above)
1" "$(MERGE_CHECK_CHUNK_LIMIT=2 STUB_SLOW=c::y chunk_run)"
check "and the check ends well before the slow piece would have (30 s)" yes \
  "$([ $((SECONDS - start)) -lt 20 ] && echo yes || echo "no: $((SECONDS - start)) s")"
check "and the next check plans c::y, now 40 s, alone, and the rest in chunks under 30 s" \
  "merge check: 6 pieces in 3 chunks of up to 30 s $plan (0 timed by neither, each alone), 6 at once" \
  "$(chunk_run : | command grep -a 'chunks of up to')"
check "a listed piece that no chunk ran fails the check" \
  "merge check: 6 pieces in 3 chunks of up to 30 s $plan (0 timed by neither, each alone), 6 at once
merge check: chunk 1 of 3: pieces: 1, failed: 0
merge check: chunk 2 of 3: pieces: 0, failed: 0
merge check: chunk 3 of 3: pieces: 4, failed: 0
merge check: the chunks did not run the listed pieces (left: listed, not run; right: run, not listed):
c::x
merge check: pieces: 5, failed: 0, in 3 chunks
merge check: FAILED: tests (above)
1" "$(STUB_DROP=c::x chunk_run)"
git checkout -q --detach base
fi
popd >/dev/null || exit 1
echo "test_merge_check: $fails failed"
[ "$fails" -eq 0 ]
