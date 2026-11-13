#!/bin/bash
# Checks the documentation of each package of the workspace whose documented sources gain or lose
# a `///` or `//!` line since this checkout left origin/main: committed, staged or not, or in a new
# file git does not track yet. Usage, from a checkout's root (in a worktree through zrun):
#   tools/check_changed_docs.sh [<log file>]
# tools/run_tests.sh runs it before the tests on every run (DOC-check-at-merge), so a branch that
# changes a doc comment is checked by the run its author makes before merging; a branch that
# changes none builds no documentation (author, 2026-11-10: no doc build unless doc comments
# change). It prints each build it makes and exits 1 if any gives a warning, after printing the
# end of rustdoc's output for each failed build; the output of the failed builds is in the log file
# (build/test-logs/doc-changed.log by default).
#
# Each package is documented twice, with --document-private-items and -D warnings (as
# `tools/run_tests.sh --doc` documents the workspace):
#   - alone (`cargo doc -p <package>`), with the package's own default features, as a build of
#     that package by itself gives it;
#   - with the features the workspace build gives the package, when it gives it any.
# One build is not enough: in DOC-private-links-3 the doc of a private item of zedc-preimage linked
# `path_check`, which exists only with the feature `preimage-ref` that zed-tests turns on, so only
# the first build failed; the public `path_check` linked private items, which only the second build
# documents, so only the second failed. `cargo doc --workspace --exclude <the others>` does not give
# the workspace's features (cargo resolves features for the selected packages only; measured on
# that commit), so the second build names them with --features. It gives the package itself the
# workspace's features, and its dependencies those that the package's own features turn on; a
# dependency's feature that only another package of the workspace turns on is not given, which
# matters only for a link to an item of that dependency that exists only with it.
#
# Limit: a change that is not to a doc comment can break a link too (an item renamed, deleted or
# made private while another doc links it). This check does not see that; `tools/run_tests.sh
# --doc`, which documents the whole workspace, does.
#
# Cost: one pass over the diff from origin/main and one lookup per directory level of each changed
# file (an associative array from source directory to package), so linear in the diff; the naive
# search of every target's directory for every file would be (files x targets). The doc builds
# dominate: each documents one package (zedc-preimage, the largest, in about 15 s at load 22).
log=${1:-build/test-logs/doc-changed.log}
mkdir -p "$(dirname "$log")"
if ! base=$(git merge-base HEAD origin/main 2>/dev/null); then
  echo "The doc check of changed packages is skipped: this checkout has no origin/main to compare" \
    "with."
  exit 0
fi
# The files whose diff adds or removes a doc line: the diff of the working tree from the point where
# this branch left origin/main, so the commits of the branch and every change not yet committed.
# A deleted file is named by its old path, so its package is still found.
changed=$(git diff -U0 --no-color --no-ext-diff --src-prefix=a/ --dst-prefix=b/ "$base" -- '*.rs' |
  awk '
    /^--- a\//    { old = substr($0, 7); next }
    /^--- /       { old = ""; next }
    /^\+\+\+ b\// { file = substr($0, 7); next }
    /^\+\+\+ /    { file = old; next }
    /^[-+][ \t]*\/\/[\/!]/ { print file }
  ' | sort -u)
# New files git does not track yet, not ignored, with a doc line.
untracked=$(git ls-files --others --exclude-standard -z -- '*.rs' |
  xargs -0 -r grep -lE '^[ \t]*//[/!]')
changed=$(printf '%s\n%s\n' "$changed" "$untracked" | sed '/^$/d' | sort -u)
[ -n "$changed" ] || exit 0
# The source directory of each target cargo doc documents, a library or a command, and its
# package. A test, bench, example or build script is not documented; a file under its directory
# alone belongs to no documented target (tests/steps/... in zed-tests).
root=$(pwd -P)
declare -A package_of
while read -r package kind dir; do
  case $kind in
    test | bench | example | custom-build) continue ;;
  esac
  dir=${dir#"$root"/}
  [ -n "${package_of[$dir]}" ] || package_of[$dir]=$package
done < <(cargo metadata --no-deps --format-version 1 |
  grep -oE '"name":"[^"]*","version":"[^"]*","id"|"kind":\[[^]]*\],"crate_types":\[[^]]*\],"name":"[^"]*","src_path":"[^"]*"' |
  awk -F '"' '
    /"version"/ { package = $4; next }
    { path = $(NF - 1); sub("/[^/]*$", "", path); print package, $4, path }
  ')
# Each changed file's package: the nearest directory above it that is a target's source directory.
packages=$(while read -r f; do
  d=$(dirname "$f")
  while [ "$d" != . ] && [ "$d" != / ] && [ -z "${package_of[$d]}" ]; do
    d=$(dirname "$d")
  done
  [ -z "${package_of[$d]}" ] || echo "${package_of[$d]}"
done <<<"$changed" | sort -u)
[ -n "$packages" ] || exit 0
# The features the workspace build gives each package, as cargo tree prints them:
# "<package> v<version> (<path>) [<features>]".
workspace_features=$(cargo tree --workspace -f '{p} [{f}]' --prefix none |
  sed 's/ (\*)$//' | sort -u)
# Documents package $1 with the further cargo arguments $3...; $2 says which build it is. A build
# that fails prints the end of rustdoc's output and is counted; the next build still runs, so one
# run names every package and build that fails.
failed=0
: >"$log"
document() {
  local package=$1 which=$2 output
  shift 2
  echo "Documenting $package ($which), whose doc comments this branch changes."
  if ! output=$(RUSTDOCFLAGS='-D warnings' cargo doc --no-deps --document-private-items \
    -p "$package" "$@" 2>&1); then
    echo "$output" >>"$log"
    echo "$output" | tail -40
    echo "DOC FAILED: $package ($which)."
    failed=$((failed + 1))
  fi
}
for p in $packages; do
  document "$p" "alone, with its own default features"
  features=$(echo "$workspace_features" | awk -v p="$p" '$1 == p && $NF ~ /^\[/ { f = $NF; gsub(/[][]/, "", f); print f; exit }')
  [ -z "$features" ] || document "$p" "with the workspace build's features $features" --features "$features"
done
if [ "$failed" != 0 ]; then
  echo "DOC FAILED: documentation builds of changed packages that failed: $failed, their output in $log."
  echo "Every link in a doc comment must name an item that exists in that build, a public item's"
  echo "doc must not link a private one (write the name as code, \`name\`, instead), and an HTML tag"
  echo "must be closed or written as code."
  exit 1
fi
