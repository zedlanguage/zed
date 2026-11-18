#!/bin/bash
# The test groups that read the spec checkout, DESIGN.md, EXAMPLES.md or another file of
# /home/luke/Work/zed (zed_tests::spec finds it: $ZED_SPEC_DIR, else zed/ beside the checkout or
# above it), so that a change to the spec runs every one of them (MERGE-spec-reads-map). Run from
# a checkout's root.
#   tools/spec_groups.sh               prints the groups, one per line, sorted
#   tools/spec_groups.sh --check       reads group names on stdin, those a run of
#                                      tools/run_tests.sh --trace saw read a spec:<path>, and
#                                      exits 1 naming each one the first form does not print
#   tools/spec_groups.sh --run [ARG..] runs them: tools/run_tests.sh --only '^(<groups>)$' ARG..,
#                                      with the caller's ZED_SPEC_DIR (through zrun, as the
#                                      short-addresses pieces need)
#   tools/spec_groups.sh --dir         prints the spec checkout the tests find: $ZED_SPEC_DIR when
#                                      set (a relative one taken from tests/, the directory the
#                                      tests of zed-tests run in), else the first zed/ holding
#                                      DESIGN.md in the checkout's parent or above it; nothing
#                                      when there is none
#   tools/spec_groups.sh --commit      prints the commit of that checkout, or nothing when there is
#                                      none, it is not a git checkout, or its tracked files have
#                                      uncommitted changes (tools/merge_check.sh keeps it in its
#                                      record, MERGE-spec-push-check)
# The groups are read off the code, not kept by hand: a test that reads the spec is compiled only
# with the feature `spec` of zed-tests (tests/src/spec.rs), so its folder, tests/steps/<s> or
# tests/full/<d>, holds `feature = "spec"`. The groups of such a folder are the [[test]] targets
# of tests/Cargo.toml whose path lies in it, short-<s> for a step of the short-addresses build
# (short_steps in tools/run_tests.sh), and full-<d>; and zed_tests, the unit tests of tests/src,
# whose spec locator's tests stat the spec's DESIGN.md (strace's %file calls count as reads). A folder that calls the spec's functions of
# zed_tests (spec::design, spec::root, fences::all...) without that feature stops every form with
# exit 2, naming it, since its group would be missed. tools/merge_check.sh runs --check on the
# groups of each traced run, so a test that reads the spec some other way fails the merge check
# instead of being missed.
# Cost: one grep over tests/steps and tests/full and one pass over tests/Cargo.toml.
mode=list
case $1 in
  --check) mode=check ;;
  --run) mode=run && shift ;;
  --dir) mode=dir ;;
  --commit) mode=commit ;;
  '') ;;
  *)
    echo "usage: tools/spec_groups.sh [--check | --run [run_tests.sh arguments] | --dir | --commit]" >&2
    exit 2
    ;;
esac
[ -f tests/Cargo.toml ] && [ -f tools/run_tests.sh ] ||
  { echo "spec_groups.sh: run from the root of a zed-impl checkout" >&2; exit 2; }

# The rule of zed_tests::spec::locate (tests/src/spec.rs).
spec_dir() {
  local d
  if [ -n "${ZED_SPEC_DIR+set}" ]; then
    d=$ZED_SPEC_DIR
    [[ $d == /* ]] || d=$(pwd)/tests/$d
    realpath -m -s -- "$d"
    return
  fi
  d=$(pwd)
  while [ "$d" != / ]; do
    d=$(dirname "$d")
    [ -f "$d/zed/DESIGN.md" ] && echo "${d%/}/zed" && return
  done
}
case $mode in
  dir) spec_dir; exit 0 ;;
  commit)
    # Only tracked files count, as for the checkout in tools/merge_check.sh: a file added to the
    # spec checkout and not committed is not seen. A directory inside another repository, not
    # the top of its own, has no commit of its own.
    d=$(spec_dir)
    [ -n "$d" ] && [ "$(git -C "$d" rev-parse --show-toplevel 2>&1)" = "$(realpath -e -- "$d" 2>&1)" ] &&
      [ -z "$(git -C "$d" status --porcelain --untracked-files=no 2>&1)" ] &&
      git -C "$d" rev-parse --verify -q HEAD
    exit 0
    ;;
esac

folders() {
  command grep -a -r -l --include='*.rs' "$@" tests/steps tests/full | awk -F/ 'NF > 3 { print $2 "/" $3 }' | sort -u
}
marked=$(folders -E 'feature *= *"spec"')
calls=$(folders -E 'zed_tests::spec\b|(^|[^:a-z_])(spec::(dir|root|design_path|examples_path|design|read)|fences::(design|examples|all|parsed|messages|passage))\(|zed_tests::fences::(design|examples|all|parsed|messages|passage)\b')
unmarked=$(comm -13 <(echo "$marked") <(echo "$calls") | command grep -a .)
if [ -n "$unmarked" ]; then
  echo "spec_groups.sh: these folders call the spec's functions of zed_tests but hold no" \
    "\`#[cfg(feature = \"spec\")]\`, so their groups would not run on a change to the spec:" >&2
  sed 's/^/  tests\//' <<<"$unmarked" >&2
  exit 2
fi
short_steps=$(sed -n 's/^short_steps="\(.*\)"$/\1/p' tools/run_tests.sh)
groups=$(
  awk -v m="$marked" '
    BEGIN { n = split(m, f, "\n"); for (i = 1; i <= n; i++) if (f[i] ~ /^steps\//) dir[f[i]] = 1 }
    /^\[/ { t = ($0 == "[[test]]"); name = ""; next }
    t && /^name *=/ { name = $0; sub(/^[^"]*"/, "", name); sub(/".*/, "", name) }
    t && /^path *=/ { p = $0; sub(/^[^"]*"/, "", p); sub(/".*/, "", p)
      split(p, c, "/"); if ((c[1] "/" c[2]) in dir && name != "") print name }' tests/Cargo.toml
  # The unit tests of tests/src (group zed_tests), which holds zed_tests::spec: locate's tests
  # walk the directories above the build and stat any DESIGN.md beside them, the spec's included.
  echo zed_tests
  for f in $marked; do
    case $f in
      full/*) echo "full-${f#full/}" ;;
      steps/*) [[ " $short_steps " == *" ${f#steps/} "* ]] && echo "short-${f#steps/}" ;;
    esac
  done
)
groups=$(command grep -a . <<<"$groups" | sort -u)
[ -n "$groups" ] || { echo "spec_groups.sh: no folder holds feature = \"spec\"; the search is broken" >&2; exit 2; }

case $mode in
  list) echo "$groups" ;;
  check)
    missed=$(comm -23 <(command grep -a . | sort -u) <(echo "$groups"))
    [ -z "$missed" ] && exit 0
    echo "spec_groups.sh: these groups read the spec but tools/spec_groups.sh does not name them, so" \
      "a change to the spec would not run them; mark the tests that read it" \
      "\`#[cfg(feature = \"spec\")]\` in their folder:" >&2
    sed 's/^/  /' <<<"$missed" >&2
    exit 1
    ;;
  run) exec tools/run_tests.sh --only "^($(paste -sd'|' <<<"$groups"))\$" "$@" ;;
esac
