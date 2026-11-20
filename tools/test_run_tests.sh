#!/bin/bash
# Tests the piece selection of tools/run_tests.sh (--list, --only, --bench, --each-test), and with
# the argument `trace` the spec reads --trace names. Run from a checkout's root,
# in a worktree through zrun (`/home/luke/Work/wt/zrun tools/test_run_tests.sh`), since it lists
# the tests of the built binaries. It builds as run_tests.sh does, which does nothing on a built
# tree; its first listing selects every piece, so in a checkout with no short-addresses clone
# yet it builds that clone from nothing (85 to 120 s), and then 9 s (2026-11-10). The expected pieces of a group are found by the binary each piece runs, not by its name.
# It lists the binaries once, in its own log directory, so a run_tests.sh in the same checkout
# keeps its files, and checks each selection on the saved table (--reuse-table): a listing takes 7
# to 13 s, and one per check ran past 60 s. One check compares a fresh listing with the table;
# a few list with --only afresh and check the binaries that listing built (build.log).
# The checks are in parts, each run as `tools/test_run_tests.sh <part>` under 60 s: `list`, the
# full listing, which publishes the table (13 s at load 94, 30 to 57 s at load 36 to 76); `select`,
# the selections of steps, modules and tests on the table list published (about 20 of 0.9 to 1.5 s
# each at load 64 to 94: with the full listing in the same part it ran past 60 s at load 47 to 94,
# 2026-11-19); `table`, the selections of --bench and --each-test on that table; `fresh`, the
# listings with --only afresh; `concurrent`, two runs at once on one log directory; and `trace`.
# select and table are run after list, with no build of the tests between them. With no part named
# it runs list, select, table, fresh and concurrent one after another.
# Each part has a log directory of its own, under which every run of run_tests.sh writes a
# directory of its own and points <dir>/latest at it; the parts are run one run at a time, so
# right after a run, latest is that run's.
fails=0
. tools/test_lib.sh || exit 2
part=${1:-all}
case $part in
  all | list | select | table | fresh | concurrent | trace) ;;
  *)
    echo "usage: tools/test_run_tests.sh [list | select | table | fresh | concurrent | trace]"
    exit 2
    ;;
esac
want() { [ "$part" = all ] || [ "$part" = "$1" ]; }
logs=build/test-run-tests
run() {
  tools/run_tests.sh --logs "$logs" "$@"
}
# The log directory of the last run of this part.
last_run() { readlink -f "$logs/latest"; }
# `tools/test_run_tests.sh trace` checks only the spec reads --trace names (MERGE-spec-reads-map),
# in a log directory of its own, as a separate piece: the selection checks take most of 60 s at
# load 80, and these run l01_06 three times and l01_03 once (10 s at load 75, 2026-11-17). l01_06's
# program test reads DESIGN.md and EXAMPLES.md in place, the spec found beside the checkout or
# through ZED_SPEC_DIR, absolute or relative to tests/; the l01_03 lexer tests read no spec file.
if [ "$part" = trace ]; then
  logs=$logs-trace
  spec_reads() {
    command grep -a -h '^spec:' "$1"/*.reads | sort -u | tr '\n' ' '
  }
  spec=$ZED_SPEC_DIR
  d=$(pwd)
  while [ -z "$spec" ] && [ "$d" != / ]; do
    d=$(dirname "$d")
    [ -f "$d/zed/DESIGN.md" ] && spec=${d%/}/zed
  done
  for how in beside absolute relative; do
    case $how in
      beside) env=(env -u ZED_SPEC_DIR) ;;
      absolute) env=(env "ZED_SPEC_DIR=$(realpath "$spec")") ;;
      relative) env=(env "ZED_SPEC_DIR=$(realpath --relative-to=tests "$spec")") ;;
    esac
    "${env[@]}" tools/run_tests.sh --logs "$logs" --only '^l01_06_lexer_tokens$' --trace "$logs/trace-$how" >/dev/null
    check "--trace names the spec's files l01_06 reads, the spec $how" "spec:DESIGN.md spec:EXAMPLES.md " \
      "$(spec_reads "$logs/trace-$how" | command grep -a -o -E 'spec:(DESIGN|EXAMPLES)\.md ' | tr -d '\n')"
  done
  run --only '^l01_03_' --trace "$logs/trace-none" >/dev/null
  check "--trace names no spec file for l01_03" "" "$(spec_reads "$logs/trace-none")"
  echo "checks failed: $fails"
  [ "$fails" = 0 ]
  exit
fi
# The binaries the run in the log directory $1 built, by name without the hash.
built() {
  sed -n 's/^ *Executable .*(.*\/\([^/]*\)-[0-9a-f]*)$/\1/p' "$1/build.log" | sort | tr '\n' ' '
}
# list lists every piece afresh and publishes the table; select and table select from the table
# the last list published.
if want list || want select || want table; then
  if want list; then
    all=$(run --list)
  elif [ -s "$logs/table" ]; then
    all=$(run --list --reuse-table)
  else
    echo "FAILED: no $logs/table: run tools/test_run_tests.sh list first"
    exit 1
  fi
  rc=$?
  [ "$rc" = 0 ] || { echo "FAILED: --list exit $rc"; exit 1; }
  pieces=$(cat "$(last_run)/pieces")
fi
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
if want list; then
check "the full list is the names of the pieces file" "$(echo "$pieces" | cut -d ' ' -f 1)" "$all"
fi
if want select; then
# A step folder outside run_tests.sh's split list is one piece, named by the folder. The step
# must stay off that list: l01_29 served here until TESTS-l01_29-split (69f447307) split it into
# a piece per module and per slow test. l01_03 is 8 small lexer tests (TEST-step-one-piece).
step03=$(ls tests/steps | grep '^l01_03_')
check "a step folder is one piece" "$step03" "$(selected '^l01_03_')"
# l01_29 is two folders, l01_29_diagnostics and l01_29_repairs_and_printing (TESTS-split), each a binary.
step29=$(ls tests/steps | grep '^l01_29_')
heap=$(by_binary deep_heap)
check "deep_heap is one piece per test, more than one" "yes" "$([ "$(echo "$heap" | wc -l)" -gt 1 ] && echo yes)"
check "deep_heap selects each of its tests" "$heap" "$(selected deep_heap)"
check "a test of deep_heap matches as deep_heap::<test>" "$(echo "$heap" | head -1)" \
  "$(selected "^deep_heap::$(echo "$heap" | head -1)\$")"
check "a union selects both groups" "$(by_binary $step29 deep_heap)" "$(selected 'l01_29|deep_heap')"
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
live3=$(echo "$all" | grep '^l01_38_omega_test::live3::' | sort)
bin38=$(echo "$pieces" | awk '$1 ~ /^l01_38_omega_test/ { print $3; exit }')
check "a split module is one piece per test" \
  "$("$bin38" --list --format terse --skip bench:: live3:: | sed -n 's/: test$//p' | sed 's/^/l01_38_omega_test::/' | sort)" "$live3"
check "a split module selects its tests" "$live3" "$(selected '^l01_38_omega_test::live3::')"
check "a split step selects all its pieces" "$(by_binary l01_38_presburger)" "$(selected '^l01_38_presburger')"
check "zedc's unit tests are one piece" "$(by_binary zedc)" "$(selected '^zedc$')"
check "a short-addresses piece is selected by its name" "short-l01_37_oracle" "$(selected '^short-l01_37_oracle$')"
fresh=$(run --list --only '^l01_36_cranelift$' | sort)
fresh_dir=$(last_run)
check "a fresh listing selects what the table does" "$(selected '^l01_36_cranelift$')" "$fresh"
check "a listing with --only builds the binaries of its groups alone" "deep_heap l01_36_cranelift " "$(built "$fresh_dir")"
fi
if want table; then
# Benchmarks (TEST-bench-split): l01_15_kernel_terms holds a module bench beside its correctness
# tests, and l01_03 none. The default run leaves the benchmarks out and runs the rest of the
# step with `--skip bench::`; --bench runs each benchmark as a piece; --each-test runs each
# correctness test of the selection as a piece. The tests of a piece are found by applying its
# arguments to the binary's list, as libtest does; the checks of --each-test compare that with
# libtest's own listing of each piece's command, on pieces with filters, --exact and --skip.
bin15=$(echo "$pieces" | awk '$1 ~ /^l01_15_kernel_terms/ { print $3; exit }')
# What libtest lists for each piece of the pieces file whose name matches $1, prefixed as
# --each-test names the pieces.
listed_by_libtest() {
  echo "$pieces" | awk -v re="$1" '$1 ~ re' | while read -r name _ bin args; do
    # shellcheck disable=SC2086
    "$bin" --list --format terse $args | sed -n "s/: test\$//p" | sed "s/^/${name%%::*}::/"
  done | sort
}
check "the default run runs no benchmark" "0" "$(echo "$all" | grep -c 'bench::')"
check "a step with benchmarks is one correctness piece" "l01_15_kernel_terms" "$(selected '^l01_15_')"
check "its piece skips the benchmarks" "--skip bench::" \
  "$(echo "$pieces" | awk '$1 == "l01_15_kernel_terms" { print $(NF - 1), $NF }')"
check "--bench runs each benchmark of the selection as a piece" \
  "$("$bin15" --list --format terse bench:: | sed -n 's/: test$//p' | sed 's/^/l01_15_kernel_terms::/' | sort)" \
  "$(run --list --reuse-table --bench --only '^l01_15_' | sort)"
check "a benchmark matches as <group>::<test>" "l01_15_kernel_terms::bench::the_printer_scales_with_depth" \
  "$(run --list --reuse-table --bench --only '^l01_15_kernel_terms::bench::the_printer')"
# A library's unit tests are one piece named with the binary's hash, zed_kernel-<hash>; a pattern
# <crate>::<path> runs each of its tests that matches as a piece of its own
# (TOOLS-only-lib-pieces), and a benchmark matches without the hash (TEST-bench-select-one).
check "a library's unit tests match as <crate>::<path>, one piece each" \
  "$(listed_by_libtest '^zed_kernel-' | grep '^zed_kernel-[0-9a-f]*::btree::')" \
  "$(selected '^zed_kernel::btree::')"
check "the unit tests so selected are more than one" "yes" \
  "$([ "$(selected '^zed_kernel::btree::' | wc -l)" -gt 1 ] && echo yes)"
check "a benchmark of a library matches by its name without the hash, alone" \
  "zed_kernel::btree::bench::insertion_lookup_and_difference_scale_as_n_log_n" \
  "$(run --list --reuse-table --bench --only '^zed_kernel::btree::bench::insertion_lookup_and_difference_scale_as_n_log_n$' |
    sed 's/^zed_kernel-[0-9a-f]*::/zed_kernel::/')"
# The short-addresses build keeps 8 bits of each digest, where the zed-kernel benchmarks measure
# ties of digests, not the method (bdd's parity bench asserts 1,024 distinct priority points and
# gets 256), so short-zed_kernel runs the unit tests alone and a --bench run makes no short- piece
# of it (3f857488a, FAIL-bench-main-f215d9c90; TEST-short-benches-full-digest, found by dryS2,
# where 24 of 48 failed bench pieces were short-zed_kernel).
benches_k=$(run --list --reuse-table --bench --only 'zed_kernel')
check "--bench over zed_kernel selects its benchmarks" "yes" \
  "$([ "$(echo "$benches_k" | grep -c '^zed_kernel-[0-9a-f]*::')" -gt 0 ] && echo yes)"
check "--bench over zed_kernel selects no short- piece" "" "$(echo "$benches_k" | grep '^short-')"
out=$(run --list --reuse-table --bench --only '^zed_kernel::btree::bench::no_benchmark_is_named_this$')
rc=$?
check "a benchmark name without the hash that matches nothing exits non-zero" \
  "1 NO PIECE MATCHES --only '^zed_kernel::btree::bench::no_benchmark_is_named_this\$' among the benchmarks" "$rc $out"
# m0_08 is the one step folder with no benchmark (l01_03, used here before, has had some since
# TEST-bench-move-rest, 97a4150e9); pick another if it gains one.
out=$(run --list --reuse-table --bench --only '^m0_08_')
rc=$?
check "--bench on a group without benchmarks stops the run" \
  "1 NO PIECE MATCHES --only '^m0_08_' among the benchmarks" "$rc $out"
check "--each-test runs each correctness test of a step with benchmarks" \
  "$("$bin15" --list --format terse --skip bench:: | sed -n 's/: test$//p' | sed 's/^/l01_15_kernel_terms::/' | sort)" \
  "$(run --list --reuse-table --each-test --only '^l01_15_' | sort)"
check "--each-test runs the tests of a split step's pieces, filtered and --exact" \
  "$(listed_by_libtest '^l01_38_presburger')" "$(run --list --reuse-table --each-test --only '^l01_38_presburger' | sort)"
check "--each-test runs the tests of pieces with --exact and --skip" \
  "$(listed_by_libtest '^(zedc_preimage|zed_kernel)(-|::)')" \
  "$(run --list --reuse-table --each-test --only '^(zedc_preimage|zed_kernel)$' | sort)"
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
# Each term of --only must select a piece (TOOL-run-tests-empty-filter): with
# '^l01_36_cranelift$|m0_03_grammar_tools::' a run passed on l01_36's pieces alone, since the step
# m0_03 is one piece named m0_03_grammar_tools and no piece is named m0_03_grammar_tools::<path>.
out=$(run --list --reuse-table --only '^l01_36_cranelift$|m0_03_grammar_tools::')
rc=$?
check "a term that selects no piece stops the run though another term selects pieces" \
  "1 --only: the term 'm0_03_grammar_tools::' of '^l01_36_cranelift\$|m0_03_grammar_tools::' selects no piece, so the run would pass without running what it names.
No piece is named m0_03_grammar_tools::<path>; '^(m0_03_grammar_tools)\$' selects the pieces of m0_03_grammar_tools." \
  "$rc $out"
check "the term the message gives selects the step" "m0_03_grammar_tools" "$(selected '^(m0_03_grammar_tools)$')"
check "a union whose terms all select pieces selects both" \
  "$(printf '%s\n' m0_03_grammar_tools "$(by_binary l01_36_cranelift deep_heap)" | sort)" \
  "$(selected '^l01_36_cranelift$|^(m0_03_grammar_tools)$')"
out=$(run --list --reuse-table --only 'm0_03_grammar_tools::')
rc=$?
check "the term alone stops the run with the same hint" "1 NO PIECE MATCHES --only 'm0_03_grammar_tools::'
No piece is named m0_03_grammar_tools::<path>; '^(m0_03_grammar_tools)\$' selects the pieces of m0_03_grammar_tools." \
  "$rc $out"
# tools/merge_check.sh writes its groups as one part ^(g1|g2|...)$, which is a term per group.
out=$(run --list --reuse-table --only '^(m0_03_grammar_tools|no_group_is_named_this|zedc)$')
rc=$?
check "a group of a merge check's --only that selects no piece stops the run" \
  "1 --only: the term '^(no_group_is_named_this)\$' of '^(m0_03_grammar_tools|no_group_is_named_this|zedc)\$' selects no piece, so the run would pass without running what it names." \
  "$rc $out"
check "a merge check's --only whose groups all select pieces selects them all" \
  "$(printf '%s\n' m0_03_grammar_tools "$(by_binary zedc)" | sort)" "$(selected '^(m0_03_grammar_tools|zedc)$')"
# Its inside, m0_03_grammar)(_tools|_nothing)(s?, holds a | outside its own parentheses; read as two
# terms, ^(m0_03_grammar)(_tools)$ and ^(_nothing)(s?)$, the second would select nothing.
check "a part ^(...)\$ whose first parenthesis closes before its end is one term" \
  "m0_03_grammar_tools" "$(selected '^(m0_03_grammar)(_tools|_nothing)(s?)$')"
out=$(run --list --reuse-table --bench --only '^l01_15_|^m0_08_')
rc=$?
check "--bench stops a run whose term selects no benchmark" \
  "1 --only: the term '^m0_08_' of '^l01_15_|^m0_08_' selects no piece among the benchmarks, so the run would pass without running what it names." \
  "$rc $out"
# A merge check names every test target of a package, deep_scaling too, whose pieces are all
# benchmarks: --skip-other-kind notes it instead of stopping the run, and excuses nothing else.
out=$(run --list --reuse-table --only '^(deep_scaling|zedc)$')
rc=$?
check "a group with benchmarks alone stops a run without --skip-other-kind" \
  "1 --only: the term '^(deep_scaling)\$' of '^(deep_scaling|zedc)\$' selects no piece, so the run would pass without running what it names." \
  "$rc $out"
out=$(run --list --reuse-table --skip-other-kind --only '^(deep_scaling|zedc)$')
rc=$?
check "--skip-other-kind notes a group with benchmarks alone and runs the others" \
  "0 --skip-other-kind: deep_scaling has benchmarks alone, which a run without --bench does not run
$(by_binary zedc)" \
  "$rc $(command grep -a -- '^--skip-other-kind' <<<"$out")
$(command grep -a -v -- '^--skip-other-kind' <<<"$out" | sort)"
out=$(run --list --reuse-table --skip-other-kind --only '^(deep_scaling)$')
rc=$?
check "--skip-other-kind with groups of benchmarks alone runs nothing and passes" \
  "0 --skip-other-kind: deep_scaling has benchmarks alone, which a run without --bench does not run
--skip-other-kind: nothing to run" "$rc $out"
out=$(run --list --reuse-table --skip-other-kind --only '^(no_group_is_named_this|zedc)$')
rc=$?
check "--skip-other-kind still stops a run whose group has no piece of either kind" \
  "1 --only: the term '^(no_group_is_named_this)\$' of '^(no_group_is_named_this|zedc)\$' selects no piece, so the run would pass without running what it names." \
  "$rc $out"
check "--short-groups names the groups with a short-addresses piece" \
  "l01_37a_short_addresses l01_37_oracle zed_kernel" "$(run --short-groups | paste -sd' ')"
check "each group --short-groups names has its piece short-<group>" \
  "$(run --short-groups | sed 's/^/short-/' | sort)" \
  "$(selected "^($(run --short-groups | sed 's/^/short-/' | paste -sd'|'))\$")"
fi
if want fresh; then
logs=build/test-run-tests-fresh
run --list --only '^zedc$' >/dev/null
check "zedc's unit tests are built from its library and its command" "zedc zedc " "$(built "$(last_run)")"
check "a module is built with its binary alone" "l01_38_omega_test " \
  "$(run --list --only '^l01_38_omega_test::live3::' >/dev/null && built "$(last_run)")"
out=$(run --list --only '^zedc$|live3::')
rc=$?
check "a part naming no binary stops the run" "1 --only: no test binary is selected by the part 'live3::' of '^zedc\$|live3::'.
A test or a module is selected only with its binary's group, as <group>::<path>." "$rc $out"
out=$(run --list --only 'live3::')
rc=$?
check "a fresh listing that selects nothing stops the run" "1 NO PIECE MATCHES --only 'live3::'
A test or a module is selected only with its binary's group, as <group>::<path>." "$rc $out"
out=$(run --list --only '(l01_38::x|y)')
rc=$?
check "a part whose binary cannot be read off stops the run" "2" "$rc"
fi
# Two runs at once on one log directory both run to the end, each in a directory of its own
# (NO-LOCKS-optimistic); until then the second stopped at once, as the run lock was held. Both
# list l01_03, a step folder that is one piece, with a fresh build, so that they overlap: both
# build, both write a table and pieces file, and the table published last is whole. latest is
# one of the two.
if want concurrent; then
logs=build/test-run-tests-concurrent
step03=$(ls tests/steps | grep '^l01_03_')
# Started as commands, not through run, so that $! is the pid each run names its directory by.
tools/run_tests.sh --logs "$logs" --list --only '^l01_03_' >"$logs.a" 2>&1 &
a=$!
tools/run_tests.sh --logs "$logs" --list --only '^l01_03_' >"$logs.b" 2>&1 &
b=$!
wait "$a"
rc_a=$?
wait "$b"
rc_b=$?
check "two runs at once on one log directory both pass" "0 0" "$rc_a $rc_b"
check "both list the piece" "$step03
$step03" "$(cat "$logs.a" "$logs.b")"
check "each has a directory of its own" "2" \
  "$(ls -d "$logs"/*-"$a"* "$logs"/*-"$b"* 2>/dev/null | wc -l)"
check "latest is one of them" "yes" \
  "$(case $(readlink "$logs/latest") in *-"$a" | *-"$b") echo yes ;; esac)"
check "no lock file is left" "" "$(find "$logs" -maxdepth 1 -name '*.lock')"
fi
echo "checks failed: $fails"
[ "$fails" = 0 ]
