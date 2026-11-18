#!/bin/bash
# Tests the selection of tools/merge_check.sh on a workspace of its own in a git repository,
# build/test-merge-check, which it keeps from run to run (it deletes nothing; each run writes every
# file again and commits it as the new base). Run from a checkout's root, through zrun
# (`/home/luke/Work/wt/zrun tools/test_merge_check.sh [select | record]`). With an argument it runs
# that part of the cases alone, in a workspace of its own (build/test-merge-check-<part>), so the
# two parts can run at once: run so, each took 11 to 12 s at load 74; the whole, 17 s at load 70.
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
# exports a symbol; and feat, with a default feature x, for step 0a. t's lib file
# tests/src/helper.rs names b and is used by step_x, the piece w and the lib file
# tests/src/wrap.rs, which step_y uses. The last cases rebase a branch on a main that moves and check what
# --record runs again (MERGE-push-race).
# MERGE_CHECK names another script to test, such as an older version, to see these cases fail.
check_script=${MERGE_CHECK:-$(pwd)/tools/merge_check.sh}
spec_groups=$(pwd)/tools/spec_groups.sh
part=$1
case $part in
  '' | select | record) ;;
  *) echo "usage: tools/test_merge_check.sh [select | record]" >&2; exit 2 ;;
esac
ws=$(pwd)/build/test-merge-check${part:+-$part}
mkdir -p "$ws/crates/a/src" "$ws/crates/b/src/m" "$ws/crates/c/src/m" "$ws/crates/c/data" \
  "$ws/crates/tool/src" "$ws/crates/rootuse/src" "$ws/crates/lnk/src" "$ws/crates/feat/src" "$ws/tests/src" "$ws/tests/steps/x" "$ws/tests/steps/y" "$ws/tests/full" "$ws/tools" "$ws/docs"
export CARGO_TARGET_DIR=$ws/target
# The toy's spec checkout, a repository of its own (MERGE-spec-push-check); without it the walk of
# tools/spec_groups.sh --dir would find the real one above the checkout.
export ZED_SPEC_DIR=$ws/target/spec
mkdir -p "$ZED_SPEC_DIR"
[ -e "$ZED_SPEC_DIR/.git/HEAD" ] || git -C "$ZED_SPEC_DIR" init -q -b main
git -C "$ZED_SPEC_DIR" config user.name test
git -C "$ZED_SPEC_DIR" config user.email test@localhost
echo "# spec" >"$ZED_SPEC_DIR/DESIGN.md"
git -C "$ZED_SPEC_DIR" add -A
git -C "$ZED_SPEC_DIR" commit -q --allow-empty -m "spec"
fails=0
check() {
  if [ "$2" = "$3" ]; then
    echo "ok: $1"
  else
    echo "FAILED: $1"
    diff <(echo "$2") <(echo "$3")
    fails=$((fails + 1))
  fi
}
[ -e "$ws/.git/HEAD" ] || git -C "$ws" init -q -b main
git -C "$ws" config user.name test
git -C "$ws" config user.email test@localhost
pushd "$ws" >/dev/null || exit 1
# Cargo.lock is not tracked: cargo tree (step 0a) writes it.
printf '/target\n/Cargo.lock\n' >.gitignore
printf '[workspace]\nresolver = "3"\nmembers = ["crates/*", "tests"]\n' >Cargo.toml
pkg() { printf '[package]\nname = "%s"\nversion = "0.0.0"\nedition = "2024"\n%s' "$1" "$2"; }
pkg a '' >crates/a/Cargo.toml
pkg b $'\n[dependencies]\na = { path = "../a" }\n' >crates/b/Cargo.toml
pkg c '' >crates/c/Cargo.toml
pkg tool '' >crates/tool/Cargo.toml
pkg rootuse '' >crates/rootuse/Cargo.toml
pkg lnk '' >crates/lnk/Cargo.toml
pkg feat $'\n[features]\ndefault = ["x"]\nx = []\n' >crates/feat/Cargo.toml
for c in tool rootuse feat; do echo "//! $c." >"crates/$c/src/lib.rs"; done
printf '//! lnk.\n#[unsafe(no_mangle)]\npub extern "C" fn lnk_f() {}\n' >crates/lnk/src/lib.rs
pkg t $'\n[dependencies]\nb = { path = "../crates/b" }\ntool = { path = "../crates/tool" }
rootuse = { path = "../crates/rootuse" }\nlnk = { path = "../crates/lnk" }
feat = { path = "../crates/feat" }\n\n[features]\nfull = []\n
[[test]]\nname = "step_x"\npath = "steps/x/mod.rs"\n\n[[test]]\nname = "step_y"\npath = "steps/y/mod.rs"\n
[[test]]\nname = "full"\npath = "full/main.rs"\nrequired-features = ["full"]\n' >tests/Cargo.toml
printf '#[cfg(test)]\n#[path = "../../../tests/src/seed.rs"]\nmod seed;\n' >crates/a/src/lib.rs
echo '//! b.' >crates/b/src/lib.rs
echo '//! c.' >crates/c/src/lib.rs
printf '//! t.\npub mod seed;\npub mod helper;\npub mod wrap;\nuse rootuse as _;\n' >tests/src/lib.rs
echo '//! The seed.' >tests/src/seed.rs
printf '//! A step helper.\n// Not code: tool lnk feat.\nuse b as _;\n' >tests/src/helper.rs
printf '//! A helper over the helper.\nuse crate::helper as _;\n' >tests/src/wrap.rs
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
printf '//! x.\nuse t::helper as _;\nuse tool as _;\n#[cfg(feature = "spec")]\nmod spec {}\n' >tests/steps/x/mod.rs
cat "$spec_groups" >tools/spec_groups.sh
chmod +x tools/spec_groups.sh
printf '//! y.\nuse t::wrap as _;\n' >tests/steps/y/mod.rs
echo '//! full.' >tests/full/main.rs
mkdir -p tests/full/w tests/full/z
printf '//! w.\nuse t::helper as _;\n' >tests/full/w/mod.rs
echo '//! z.' >tests/full/z/mod.rs
# The toy's own tools/test_merge_check.sh, which merge_check.sh runs when a file it tests changes:
# it prints its part and fails the part named by $STUB_SELF_FAIL.
printf '#!/bin/bash\necho "self $1"\n[ "$1" != "$STUB_SELF_FAIL" ]\n' >tools/test_merge_check.sh
chmod +x tools/test_merge_check.sh
echo '# Notes' >docs/notes.md
echo '# Plan' >docs/plan.md
mkdir -p data
echo 'notes' >data/notes.txt
# With --trace <dir>, the stub writes for each group g of the --only pattern a piece p-g into
# <dir>/groups and, as the paths it read, the lines `g <path>` of $STUB_READS.
cat >tools/run_tests.sh <<'EOF'
#!/bin/bash
echo "run_tests $*"
t= o=
while [ $# -gt 0 ]; do
  case $1 in --trace) t=$2; shift ;; --only) o=$2; shift ;; esac
  shift
done
if [ -n "$t" ]; then
  mkdir -p "$t"
  : >"$t/groups"
  o=${o#^(}
  for g in $(tr '|' ' ' <<<"${o%)\$}"); do
    echo "p-$g $g $g" >>"$t/groups"
    awk -v g="$g" '$1 == g { print substr($0, length(g) + 2) }' "$STUB_READS" >"$t/p-$g.reads"
  done
fi
exit ${STUB_RC:-0}
EOF
chmod +x tools/run_tests.sh
git add -A
git commit -q --allow-empty -m base
git tag -f base >/dev/null
# Commits a change to the file $1 on the base (a line ${2:-// changed}).
change_on_base() {
  git checkout -q --detach base
  echo "${2:-// changed}" >>"$1"
  git add -A
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

# The part select (not indented, to keep the cases' lines as they were).
if [ "$part" != record ]; then
check "a crate's source selects it, its dependents and s_01f, not the crate beside it" \
  "merge check: groups: $(sorted "$(short a b s_01f_import_graph step_x step_y t)")" \
  "$(groups_after crates/a/src/lib.rs)"
check "a crate no one depends on selects its own unit tests and s_01f" \
  "merge check: groups: $(sorted "$(short c s_01f_import_graph)")" \
  "$(groups_after crates/c/src/lib.rs)"
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
  "merge check: groups: $(sorted "$(short a b c feat lnk rootuse step_x step_y t tool)")" \
  "$(groups_after Cargo.toml '# changed')"
# The narrowing of step 2 (MERGE-dep-by-target).
check "a crate the package of tests/full depends on, named by one step alone, selects that step alone" \
  "merge check: groups: $(sorted "$(short s_01f_import_graph step_x tool)")" \
  "$(groups_after crates/tool/src/lib.rs)"
check "a crate named only in comments of the package of tests/full selects none of its targets" \
  "merge check: groups: $(sorted "$(short feat s_01f_import_graph)")" \
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
# build.
git checkout -q --detach base
printf '\n[dependencies]\nfeat = { path = "../feat", default-features = false }\n' >>crates/tool/Cargo.toml
git commit -q -a -m "tool: depend on feat without its defaults"
check "a manifest that gives a package alone other features than the workspace build fails the check" \
  "merge check: a manifest or Cargo.lock changed, and these packages, built alone, get features the workspace build does not give them (tools/run_tests.sh refuses to build them so):
  tool:
    feat v0.0.0 ($ws/crates/feat) []
merge check: FAILED
1" "$("$check_script" --base base 2>&1 | command grep -a -E '^(merge check: (a manifest|FAILED)|  )'; echo "${PIPESTATUS[0]}")"
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
  "run_tests --only ^($(sorted "$(short c s_01f_import_graph)" | tr ' ' '|'))\$ 3
merge check: passed
0" \
  "$("$check_script" --base base 3 2>&1 | command grep -a -E '^(run_tests|merge check: (passed|FAILED))'; echo "${PIPESTATUS[0]}")"
check "a failing test run stops the check with exit 1" "merge check: FAILED: tests (above)
1" "$(STUB_RC=1 "$check_script" --base base 2>&1 | command grep -a 'FAILED'; echo "${PIPESTATUS[0]}")"
echo "// uncommitted" >>crates/c/src/lib.rs
check "uncommitted changes to tracked files stop the check" "1" \
  "$("$check_script" --base base --groups >/dev/null 2>&1; echo $?)"
printf '//! c.\n// changed\n' >crates/c/src/lib.rs
git checkout -q --detach base
check "a file moved from one package to another selects both" \
  "merge check: groups: $(sorted "$(short a b c s_01f_import_graph step_x step_y t)")" \
  "$(git mv crates/c/src/inl.rs crates/a/src/inl.rs && git commit -q -m move &&
    "$check_script" --base base --groups 2>&1 | command grep -a -E '^merge check: groups')"
# tests/full (MERGE-runtime-inputs): a piece's folder selects that piece alone, run with --full
# under its name full-<piece>; its main.rs selects every piece; neither selects the package t.
# A change that reaches t through its dependencies selects every piece (MERGE-full-by-dependency).
full_run() {
  change_on_base "$1"
  "$check_script" --base base 2>&1 | command grep -a -E '^(run_tests|merge check: (groups|tests/full|passed))'
}
check "a file in a piece's folder of tests/full selects that piece alone, run with --full" \
  "merge check: groups:
merge check: tests/full pieces: z
run_tests --full --only ^(full-z)\$ 6
merge check: passed" "$(full_run tests/full/z/mod.rs)"
check "tests/full/main.rs selects every piece of tests/full" \
  "merge check: groups:
merge check: tests/full pieces: w z
run_tests --full --only ^(full-w|full-z)\$ 6
merge check: passed" "$(full_run tests/full/main.rs)"
all_b=$(sorted "$(short b s_01f_import_graph step_x step_y t)")
check "a crate that a step helper of the package of tests/full names selects every target and piece using the helper, the pieces run with --full after the local groups" \
  "merge check: groups: $all_b
merge check: tests/full pieces: w
run_tests --only ^($(tr ' ' '|' <<<"$all_b"))\$ 6
run_tests --full --only ^(full-w)\$ 6
merge check: passed" "$(full_run crates/b/src/lib.rs)"
check "a crate the package of tests/full does not depend on selects no piece" \
  "merge check: groups: $(sorted "$(short c s_01f_import_graph)")" \
  "$(full_run crates/c/src/lib.rs | command grep -a -E '^merge check: (groups|tests/full)')"
check "a failing run of tests/full stops the check with exit 1" "merge check: FAILED: tests/full (above)
1" "$(change_on_base tests/full/w/mod.rs
    STUB_RC=1 "$check_script" --base base 2>&1 | command grep -a 'FAILED'; echo "${PIPESTATUS[0]}")"
# The self-tests (MERGE-tools-self-tests): a change to tools/run_tests.sh runs both parts of
# tools/test_merge_check.sh; a part that fails refuses the branch.
check "a change to tools/run_tests.sh runs both parts of tools/test_merge_check.sh" \
  "merge check: a file tools/test_merge_check.sh tests changed: both its parts run
merge check: tools/test_merge_check.sh select and record passed
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
  git add -A
  git commit -q -m "change $1"
  "$check_script" --base base --reads "$map" --groups 2>&1 |
    command grep -a -E '^merge check: (groups|the map|no package|tests/full)' | sed "s|$map|MAP|"
}
uncovered="merge check: the map has no reads of 7 groups, which only compilation selects: a b feat lnk rootuse step_x tool
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
if [ "$part" != select ]; then
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
# what ran, the outcome and the exit code.
record_run() {
  "$check_script" --base "$1" --record "$rec" "${@:2}" 2>&1 |
    command grep -a -E '^(run_tests|merge check: (to run|tests/full pieces to run|passed|FAILED))' |
    sed 's/ --trace [^ ]*//'
  echo "${PIPESTATUS[0]}"
}
# Moves main, the tag upstream (the toy repository's branch main is another ref), on by a change
# to the file $1 and rebases the branch on it.
git tag -f upstream base >/dev/null
main_moves() {
  git checkout -q --detach upstream
  echo "${2:-// changed}" >>"$1"
  git add -A
  git commit -q -m "main: change $1"
  git tag -f upstream >/dev/null
  git cherry-pick branch >/dev/null
}
check "with no record, every selected group runs, and the record is written" \
  "merge check: to run: $all_c
run_tests --only ^($(tr ' ' '|' <<<"$all_c"))\$ 6
merge check: passed
0" "$(record_run base --reads "$ws/target/map-record")"
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
read c docs/plan.md
read s_01f_import_graph crates
read short-c data
end" "$(cat "$rec")"
check "the same commit again runs nothing" "merge check: to run:
merge check: passed (every selected group passed at the record's commit, with the same inputs)
0" "$(record_run base)"
main_moves docs/notes.md
check "main moved by a file no group read: nothing runs" "merge check: to run:
merge check: passed (every selected group passed at the record's commit, with the same inputs)
0" "$(record_run upstream)"
check "the record now names the rebased commit" "$(git rev-parse HEAD)" "$(head -n 1 "$rec")"
main_moves docs/plan.md
check "main moved by a file a group read at run time: that group runs" "merge check: to run: c
run_tests --only ^(c)\$ 6
merge check: passed
0" "$(record_run upstream)"
check "the group that ran keeps its reads in the new record" "read c docs/plan.md
read s_01f_import_graph crates
read short-c data" "$(command grep -a '^read' "$rec")"
main_moves crates/a/src/lib.rs
check "main moved by a crate the branch's crate does not use: only s_01f, which any crate selects" \
  "merge check: to run: $(sorted "$(short s_01f_import_graph)")" \
  "$(record_run upstream | command grep -a 'to run')"
passed_at=$(head -n 1 "$rec")
main_moves crates/c/src/inl.rs
check "main changed the branch's crate: a failing run exits 1 and keeps the old record" \
  "merge check: to run: $all_c
merge check: FAILED: tests (above)
1
$passed_at" \
  "$(STUB_RC=1 record_run upstream | command grep -a -v '^run_tests'; head -n 1 "$rec")"
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
check "a change under tools/ since the record runs every selected group" "merge check: to run: $all_c" \
  "$(record_run upstream | command grep -a 'to run')"
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
run_tests --only ^($(tr ' ' '|' <<<"$all_c"))\$ 6
run_tests --full --only ^(full-z)\$ 6
merge check: passed
0" "$(record_run base --reads "$ws/target/map-full")"
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
run_tests --only ^(c|short-s_01f_import_graph)\$ 6
run_tests --full --only ^(full-z)\$ 6
merge check: passed
0" "$(record_run upstream)"
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
run_tests --only ^($(tr ' ' '|' <<<"$sx"))\$ 6
merge check: passed
0" "$(record_run base)"
: >"$rec"
echo 'short-step_x spec:EXAMPLES.md' >>"$STUB_READS"
check "a group that read the spec and that spec_groups.sh does not name fails, and no record is written" \
  "merge check: to run: $sx
run_tests --only ^($(tr ' ' '|' <<<"$sx"))\$ 6
merge check: FAILED: tools/spec_groups.sh (above)
1" "$(record_run base; cat "$rec")"
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
run_tests --only ^(step_x)\$ 6
merge check: passed
0
spec $(git -C "$ZED_SPEC_DIR" rev-parse HEAD)" "$(record_run base; sed -n 2p "$rec")"
echo "uncommitted" >>"$ZED_SPEC_DIR/DESIGN.md"
check "the spec has uncommitted changes: the group that read it runs, and the record names no spec commit" \
  "merge check: to run: step_x
group short-step_x" "$(record_run base | command grep -a 'to run'; sed -n 2p "$rec")"
git -C "$ZED_SPEC_DIR" checkout -q DESIGN.md
check "then with the spec clean again, the record's unknown spec commit runs it once more" \
  "merge check: to run: step_x" "$(record_run base | command grep -a 'to run')"
check "and then nothing" "merge check: to run:" "$(record_run base | command grep -a 'to run')"
git checkout -q --detach base
fi
popd >/dev/null || exit 1
echo "test_merge_check: $fails failed"
[ "$fails" -eq 0 ]
