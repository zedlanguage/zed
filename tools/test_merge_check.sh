#!/bin/bash
# Tests the selection of tools/merge_check.sh on a workspace of its own in a git repository,
# build/test-merge-check, which it keeps from run to run (it deletes nothing; each run writes every
# file again and commits it as the new base). Run from a checkout's root, through zrun
# (`/home/luke/Work/wt/zrun tools/test_merge_check.sh`); about 2 s. The workspace is the real one
# in small: crates a, b (depends on a) and c; a package t in tests/ that depends on b, whose lib
# file tests/src/seed.rs crate a also compiles by #[path] (as tests/src/seed.rs is compiled into
# seven crates), with [[test]] targets step_x and step_y in tests/steps/<step>/ and full, which
# needs a feature. tools/run_tests.sh is a stub that prints its arguments and exits with $STUB_RC.
check_script=$(pwd)/tools/merge_check.sh
ws=$(pwd)/build/test-merge-check
mkdir -p "$ws/crates/a/src" "$ws/crates/b/src" "$ws/crates/c/src" "$ws/tests/src" \
  "$ws/tests/steps/x" "$ws/tests/steps/y" "$ws/tests/full" "$ws/tools" "$ws/docs"
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
echo '//! x.' >tests/steps/x/mod.rs
echo '//! y.' >tests/steps/y/mod.rs
echo '//! full.' >tests/full/main.rs
echo '# Notes' >docs/notes.md
printf '#!/bin/bash\necho "run_tests $*"\nexit ${STUB_RC:-0}\n' >tools/run_tests.sh
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
popd >/dev/null || exit 1
echo "test_merge_check: $fails failed"
[ "$fails" -eq 0 ]
