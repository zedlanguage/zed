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
# inline modules, and by include! (TEST-merge-check-nested-path). The last cases rebase a branch
# on a main that moves and check what --record runs again (MERGE-push-race).
# MERGE_CHECK names another script to test, such as an older version, to see these cases fail.
check_script=${MERGE_CHECK:-$(pwd)/tools/merge_check.sh}
part=$1
case $part in
  '' | select | record) ;;
  *) echo "usage: tools/test_merge_check.sh [select | record]" >&2; exit 2 ;;
esac
ws=$(pwd)/build/test-merge-check${part:+-$part}
mkdir -p "$ws/crates/a/src" "$ws/crates/b/src/m" "$ws/crates/c/src/m" "$ws/crates/c/data" \
  "$ws/tests/src" "$ws/tests/steps/x" "$ws/tests/steps/y" "$ws/tests/full" "$ws/tools" "$ws/docs"
export CARGO_TARGET_DIR=$ws/target
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
echo /target >.gitignore
printf '[workspace]\nresolver = "3"\nmembers = ["crates/a", "crates/b", "crates/c", "tests"]\n' >Cargo.toml
pkg() { printf '[package]\nname = "%s"\nversion = "0.0.0"\nedition = "2024"\n%s' "$1" "$2"; }
pkg a '' >crates/a/Cargo.toml
pkg b $'\n[dependencies]\na = { path = "../a" }\n' >crates/b/Cargo.toml
pkg c '' >crates/c/Cargo.toml
pkg t $'\n[dependencies]\nb = { path = "../crates/b" }\n\n[features]\nfull = []\n
[[test]]\nname = "step_x"\npath = "steps/x/mod.rs"\n\n[[test]]\nname = "step_y"\npath = "steps/y/mod.rs"\n
[[test]]\nname = "full"\npath = "full/main.rs"\nrequired-features = ["full"]\n' >tests/Cargo.toml
printf '#[cfg(test)]\n#[path = "../../../tests/src/seed.rs"]\nmod seed;\n' >crates/a/src/lib.rs
echo '//! b.' >crates/b/src/lib.rs
echo '//! c.' >crates/c/src/lib.rs
printf '//! t.\npub mod seed;\n' >tests/src/lib.rs
echo '//! The seed.' >tests/src/seed.rs
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
echo '//! x.' >tests/steps/x/mod.rs
echo '//! y.' >tests/steps/y/mod.rs
echo '//! full.' >tests/full/main.rs
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
# Commits a change to the file $1 on the base (a line ${2:-// changed}) and prints the
# selection's last line.
groups_after() {
  git checkout -q --detach base
  echo "${2:-// changed}" >>"$1"
  git add -A
  git commit -q -m "change $1"
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
  "merge check: groups: $(sorted "$(short a b c step_x step_y t)")" \
  "$(groups_after Cargo.toml '# changed')"
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
    command grep -a -E '^(run_tests|merge check: (to run|passed|FAILED))' | sed 's/ --trace [^ ]*//'
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
0" "$(record_run base)"
check "the record names the commit, the groups and what each read" "$(git rev-parse HEAD)
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
git checkout -q --detach base
fi
popd >/dev/null || exit 1
echo "test_merge_check: $fails failed"
[ "$fails" -eq 0 ]
