#!/bin/bash
# Tests the piece selection of tools/run_tests.sh (--list, --only). Run from a checkout's root,
# in a worktree through zrun (`/home/luke/Work/wt/zrun tools/test_run_tests.sh`), since it lists
# the tests of the built binaries. It builds as run_tests.sh does, which does nothing on a built
# tree. The expected pieces of a group are found by the binary each piece runs, not by its name.
# It lists the binaries once, in its own log directory, so a run_tests.sh in the same checkout
# keeps its files, and checks each selection on the saved table (--reuse-table): a listing takes 7
# to 13 s, and one per check ran past 60 s. One check compares a fresh listing with the table.
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
logs=build/test-run-tests
run() {
  tools/run_tests.sh --logs "$logs" "$@"
}
all=$(run --list)
rc=$?
[ "$rc" = 0 ] || { echo "FAILED: --list exit $rc"; exit 1; }
pieces=$(cat "$logs/pieces")
# The names of the pieces whose binary (third field), without its hash, is one of the groups $@.
by_binary() {
  local g
  for g in "$@"; do
    echo "$pieces" | awk -v g="$g" '{ b = $3; sub(".*/", "", b); sub("-[^-]*$", "", b); if (b == g) print $1 }'
  done | sort
}
selected() {
  run --list --reuse-table --only "$1" | sort
}
check "the full list is the names of the pieces file" "$(echo "$pieces" | cut -d ' ' -f 1)" "$all"
step29=$(ls tests/steps | grep '^l01_29_')
check "a step folder is one piece" "$step29" "$(selected '^l01_29_')"
heap=$(by_binary deep_heap)
check "deep_heap is one piece per test, more than one" "yes" "$([ "$(echo "$heap" | wc -l)" -gt 1 ] && echo yes)"
check "deep_heap selects each of its tests" "$heap" "$(selected deep_heap)"
check "a test of deep_heap matches as deep_heap::<test>" "$(echo "$heap" | head -1)" \
  "$(selected "^deep_heap::$(echo "$heap" | head -1)\$")"
check "a union selects both groups" "$(by_binary "$step29" deep_heap)" "$(selected 'l01_29|deep_heap')"
check "deep_values and deep_scaling are split per test too" "$(by_binary deep_values deep_scaling)" \
  "$(selected '^deep_(values|scaling)$')"
check "a step selects the deep binaries in its folder" \
  "$(by_binary l01_22_type_representation deep_types)" "$(selected '^l01_22')"
check "a step selects each test of a deep binary split per test" \
  "$(by_binary l01_36_cranelift deep_heap)" "$(selected '^l01_36_cranelift$')"
check "a test of deep_heap matches as <step>::<test>" "$(echo "$heap" | head -1)" \
  "$(selected "^l01_36_cranelift::$(echo "$heap" | head -1)\$")"
check "m0_09 selects deep_values and deep_scaling" \
  "$(by_binary m0_09_kernel_evaluator deep_values deep_scaling)" "$(selected '^m0_09_')"
live3=$(echo "$all" | grep '^l01_38_presburger::live3::' | sort)
bin38=$(echo "$pieces" | awk '$1 ~ /^l01_38_presburger/ { print $3; exit }')
check "a split module is one piece per test" \
  "$("$bin38" --list --format terse live3:: | sed -n 's/: test$//p' | sed 's/^/l01_38_presburger::/' | sort)" "$live3"
check "a split module selects its tests" "$live3" "$(selected '^l01_38_presburger::live3::')"
check "a split step selects all its pieces" "$(by_binary l01_38_presburger)" "$(selected '^l01_38_presburger')"
check "zedc's unit tests are one piece" "$(by_binary zedc)" "$(selected '^zedc$')"
check "a short-addresses piece is selected by its name" "short-l01_37_oracle" "$(selected '^short-l01_37_oracle$')"
check "a fresh listing selects what the table does" "$(selected '^l01_36_cranelift$')" \
  "$(run --list --only '^l01_36_cranelift$' | sort)"
check "a listing with --only leaves the table of all pieces" "$(echo "$all" | sort)" "$(selected .)"
out=$(run --reuse-table --only '^zedc$')
rc=$?
check "--reuse-table without --list exits 2" "2 --reuse-table needs --list" "$rc $out"
out=$(run --list --reuse-table --only 'no_piece_is_named_this')
rc=$?
check "a pattern matching nothing exits non-zero with a message" "1 NO PIECE MATCHES --only 'no_piece_is_named_this'" \
  "$rc $out"
out=$(run --list --reuse-table --only '(')
rc=$?
check "an invalid pattern exits 2" "2 --only: not a valid extended regular expression: (" "$rc $out"
echo "checks failed: $fails"
[ "$fails" = 0 ]
