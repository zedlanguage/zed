#!/bin/bash
# Tests tools/check_changed_docs.sh on a workspace of two small packages in a git repository of its
# own, build/test-check-changed-docs, which it keeps from run to run (it deletes nothing; each run
# writes every file again and commits it as the new origin/main). Run from a checkout's root, in a
# worktree through zrun (`/home/luke/Work/wt/zrun tools/test_check_changed_docs.sh`); about 10 s.
# Package a has a feature `extra` and a public function `gated` that exists only with it; package
# b depends on a with `extra`, so the workspace build gives a that feature and a build of a alone
# does not, as zed-tests gives zedc-preimage `preimage-ref` (DOC-private-links-3).
check=$(pwd)/tools/check_changed_docs.sh
ws=$(pwd)/build/test-check-changed-docs
mkdir -p "$ws/a/src" "$ws/a/tests" "$ws/b/src" "$ws/.git"
# The checkout's .cargo/config.toml puts the target directory in build/cargo; this workspace keeps
# its own.
export CARGO_TARGET_DIR=$ws/target
fails=0
check() {
  if [ "$2" = "$3" ]; then
    echo "ok: $1"
  else
    echo "FAILED: $1"
    diff <(echo "$2") <(echo "$3") | head -20
    fails=$((fails + 1))
  fi
}
# Runs the check in the workspace: its exit code, then the lines that name a build or a failure.
run() {
  local out rc
  out=$(pushd "$ws" >/dev/null && "$check" "$ws/doc.log" 2>&1)
  rc=$?
  echo "$rc"
  echo "$out" | grep -E '^(Documenting|DOC FAILED|The doc check)' | sed 's/, whose doc comments this branch changes\.$//'
}
lib_a='//! Package a.

/// A public function.
pub fn public_item() {}

/// A private function.
fn private_item() {}

/// A public function that exists only with the feature `extra`.
#[cfg(feature = "extra")]
pub fn gated() {}

/// Uses `private_item`.
pub fn uses() {
    private_item();
}
'
# Writes the base state of every file and makes it origin/main. extra.rs is excluded from git, so
# it is never committed, until a check lifts the exclusion to make it an untracked file.
base() {
  pushd "$ws" >/dev/null || exit 1
  git checkout -q -- . 2>/dev/null
  echo /target >.gitignore
  echo /doc.log >>.gitignore
  echo /a/src/extra.rs >.git/info/exclude
  printf '[workspace]\nresolver = "3"\nmembers = ["a", "b"]\n' >Cargo.toml
  printf '[package]\nname = "a"\nversion = "0.0.0"\nedition = "2024"\n\n[features]\nextra = []\n' >a/Cargo.toml
  printf '[package]\nname = "b"\nversion = "0.0.0"\nedition = "2024"\n\n[dependencies]\na = { path = "../a", features = ["extra"] }\n' >b/Cargo.toml
  echo "$lib_a" >a/src/lib.rs
  printf '//! Package b.\n\n/// Calls a.\npub fn call() {\n    a::gated();\n}\n' >b/src/lib.rs
  printf '//! A test of a.\n\n/// A test.\n#[test]\nfn works() {\n    a::public_item();\n}\n' >a/tests/t.rs
  printf '/// Another public function.\npub fn other() {}\n' >a/src/extra.rs
  git add -A
  git commit -q --allow-empty -m base
  git update-ref refs/remotes/origin/main HEAD
  popd >/dev/null || exit 1
}
[ -e "$ws/.git/HEAD" ] || git -C "$ws" init -q -b main
git -C "$ws" config user.name test
git -C "$ws" config user.email test@localhost
# A run stopped between its checkouts below leaves HEAD detached.
git -C "$ws" symbolic-ref -q HEAD >/dev/null || git -C "$ws" checkout -q main
# Edits file $1 of the workspace with the sed script $2.
edit() { sed -i "$2" "$ws/$1"; }
a_both="Documenting a (alone, with its own default features)
Documenting a (with the workspace build's features extra)"

base
check "no change builds no documentation" "0" "$(run)"

base
edit a/src/lib.rs 's/private_item();/private_item();\n    public_item();/'
check "a change to code alone builds no documentation" "0" "$(run)"

base
edit a/src/lib.rs 's|^/// A public function\.$|/// A public function, beside [`uses`].|'
check "a changed doc line documents its package alone and with the workspace's features" \
  "0
$a_both" "$(run)"

base
edit a/src/lib.rs 's|^/// A public function\.$|/// A public function, beside [`private_item`].|'
check "a public doc linking a private item fails both builds" "1
Documenting a (alone, with its own default features)
DOC FAILED: a (alone, with its own default features).
Documenting a (with the workspace build's features extra)
DOC FAILED: a (with the workspace build's features extra).
DOC FAILED: documentation builds of changed packages that failed: 2, their output in $ws/doc.log." "$(run)"

base
edit a/src/lib.rs 's|^/// A private function\.$|/// A private function, beside [`gated`].|'
check "a link to an item of a feature the package alone lacks fails the build alone" "1
Documenting a (alone, with its own default features)
DOC FAILED: a (alone, with its own default features).
Documenting a (with the workspace build's features extra)
DOC FAILED: documentation builds of changed packages that failed: 1, their output in $ws/doc.log." "$(run)"

base
edit a/src/lib.rs 's|^/// A public function that exists only with the feature `extra`\.$|/// Exists only with `extra`; see [`private_item`].|'
check "a private link in an item of a workspace feature fails the build with that feature" "1
Documenting a (alone, with its own default features)
Documenting a (with the workspace build's features extra)
DOC FAILED: a (with the workspace build's features extra).
DOC FAILED: documentation builds of changed packages that failed: 1, their output in $ws/doc.log." "$(run)"

base
edit a/src/lib.rs 's|^/// A public function\.$|/// A public function, beside [`private_item`].|'
git -C "$ws" commit -q -a -m "a committed doc change"
check "a committed doc change is checked" "1" "$(run | head -1)"

base
edit b/src/lib.rs 's|^/// Calls a\.$|/// Calls [`a::gated`], once [`nothing`] exists.|'
git -C "$ws" commit -q -a -m "on origin/main only"
git -C "$ws" update-ref refs/remotes/origin/main HEAD
git -C "$ws" checkout -q --detach HEAD~1
check "a doc change on origin/main that the branch lacks is not checked" "0" "$(run)"
git -C "$ws" checkout -q main

base
edit a/tests/t.rs 's|^/// A test\.$|/// A test of [`nothing`].|'
check "a doc change in a test file builds no documentation" "0" "$(run)"

base
edit b/src/lib.rs '/^\/\/\/ Calls a\.$/d'
check "a removed doc line documents its package" "0
Documenting b (alone, with its own default features)" "$(run)"

base
git -C "$ws" update-ref -d refs/remotes/origin/main
check "a checkout without origin/main says the check is skipped" "0
The doc check of changed packages is skipped: this checkout has no origin/main to compare with." "$(run)"

base
: >"$ws/.git/info/exclude"
edit a/src/lib.rs 's|^//! Package a\.$|//! Package a.\n\nmod extra;|'
printf '/// Another public function, beside [`nothing`].\npub fn other() {}\n' >"$ws/a/src/extra.rs"
check "a new file git does not track yet is checked" "1" "$(run | head -1)"
base

echo "checks failed: $fails"
[ "$fails" = 0 ]
