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
# 2026-11-19); `table`, the selections of --bench and --each-test on that table; `except`, the
# pieces --except leaves out of a selection on that table; `fresh`, the
# listings with --only afresh; `short`, the short-addresses pieces and their clone; `copy`, a
# piece that starts its binary again after the build is gone; `concurrent`, two runs at once on
# one log directory; and `trace`.
# select, table and except are run after list, with no build of the tests between them. With no part named
# it runs list, select, table, except, fresh, short, copy and concurrent one after another.
# Each part has a log directory of its own, under which every run of run_tests.sh writes a
# directory of its own and points <dir>/latest at it; the parts are run one run at a time, so
# right after a run, latest is that run's.
fails=0
. tools/test_lib.sh || exit 2
part=${1:-all}
case $part in
  all | list | select | table | except | fresh | short | copy | concurrent | trace) ;;
  *)
    echo "usage: tools/test_run_tests.sh [list | select | table | except | fresh | short | copy | concurrent | trace]"
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
# A run prints such a piece with the binary's hash; that name, copied into --only, selects the
# one test, and so does the name with another binary's hash, as after a rebuild
# (TOOL-short-piece-test-filter: such a name selected nothing, so a failing seed test of
# zedc_presburger was run by hand).
hashed=$(listed_by_libtest '^zed_kernel-' | grep '::btree::' | head -1)
check "a library's unit test is selected by the name a run prints, hash and all" "$hashed" \
  "$(selected "^$hashed\$")"
check "and by that name with another hash" "$hashed" \
  "$(selected "^$(echo "$hashed" | sed 's/^zed_kernel-[0-9a-f]*::/zed_kernel-0123456789abcdef::/')\$")"
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
# zedc_types's slow correctness tests run as pieces of their own, and the binary's other tests as
# one piece that skips them (TEST-zedc-types-lib-split: the one piece of 143 tests ran past its
# limit of 33 s at load 52). That piece's `--skip` matches anywhere in a name, so the pieces
# together must still run each correctness test: a skipped name inside another (the index of
# arrows on wider shapes) needs a line of its own in run_tests.sh's alone list.
check "zedc_types's slow tests are pieces of their own" \
  "$(printf 'zedc_types::ty::tests::%s\n' a_generic_arrow_fits_where_some_binding_of_its_variable_fits \
    a_shape_held_as_is_out_of_written_order_gives_no_wrong_verdict bound_shapes_agree_with_trying_every_shape \
    functions_met_through_the_index_are_those_met_pair_by_pair_part_1 \
    functions_met_through_the_index_are_those_met_pair_by_pair_part_2 \
    functions_met_through_the_index_are_those_met_pair_by_pair_part_3 \
    functions_met_through_the_index_are_those_met_pair_by_pair_part_4 pinned_shapes_are_those_of_the_rule_of_one_shape \
    the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows \
    the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows_on_wider_shapes \
    tuples_met_and_subtracted_through_the_index_are_those_of_every_pair \
    tuples_that_hold_a_value_through_the_index_are_those_of_every_tuple | sort)" \
  "$(echo "$pieces" | awk '$1 ~ /^zedc_types::/ { print $1 }' | sort)"
types_bin=$(echo "$pieces" | awk '$1 ~ /^zedc_types-/ { print $3; exit }')
check "zedc_types's pieces together run each of its correctness tests once" \
  "$("$types_bin" --list --format terse --skip bench:: | sed -n 's/: test$//p' | sort)" \
  "$(echo "$pieces" | awk '$1 ~ /^zedc_types(-|::)/' | while read -r _ _ bin args; do
    # shellcheck disable=SC2086
    "$bin" --list --format terse $args | sed -n 's/: test$//p'
  done | sort)"
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
# A second --only adds to the first; it used to replace it, so a run named two groups and ran one.
check "--only given twice selects the union" \
  "$(printf '%s\n' m0_03_grammar_tools "$(by_binary zedc)" | sort)" \
  "$(run --list --reuse-table --only '^(m0_03_grammar_tools)$' --only '^(zedc)$' | sort)"
out=$(run --list --reuse-table --only '^(m0_03_grammar_tools)$' --only 'no_piece_is_named_this')
rc=$?
check "a second --only that selects no piece stops the run" \
  "1 --only: the term 'no_piece_is_named_this' of '^(m0_03_grammar_tools)\$|no_piece_is_named_this' selects no piece, so the run would pass without running what it names." \
  "$rc $out"
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
# --except <ERE> leaves out each selected piece it matches, by the name a run prints or that name
# with the binary's hash taken off (TOOL-main-watch-start-green: main-watch does not start a
# benchmark its known list marks skip, such as rung2 at n = 600, which holds 67 to 71 GB). A part
# of its own: in table these six listings took its run past 60 s (load 36 to 53, 2026-11-20).
if want except; then
[ -s "$logs/table" ] || { echo "FAILED: no $logs/table: run tools/test_run_tests.sh list first"; exit 1; }
benches15=$(run --list --reuse-table --bench --only '^l01_15_' | sort)
check "--except: the benchmark to leave out is among those --only selects" 1 \
  "$(echo "$benches15" | grep -c -x 'l01_15_kernel_terms::bench::the_printer_scales_with_depth')"
check "--except leaves out the benchmark it names, and only it" \
  "$(echo "$benches15" | grep -v -x 'l01_15_kernel_terms::bench::the_printer_scales_with_depth')" \
  "$(run --list --reuse-table --bench --only '^l01_15_' --except '^l01_15_kernel_terms::bench::the_printer_scales_with_depth$' | sort)"
check "--except given twice leaves out both" \
  "$(echo "$benches15" | grep -v -e '::bench::the_printer_scales_with_depth$' -e '::bench::dropping_deep_and_wide_terms_scales$')" \
  "$(run --list --reuse-table --bench --only '^l01_15_' --except '::bench::the_printer_scales_with_depth$' --except '::bench::dropping_deep_and_wide_terms_scales$' | sort)"
benchesk=$(run --list --reuse-table --bench --only 'zed_kernel' | sort)
check "--except: the hashed benchmark to leave out is among those --only selects" 1 \
  "$(echo "$benchesk" | grep -c '^zed_kernel-[0-9a-f]*::btree::bench::insertion_lookup_and_difference_scale_as_n_log_n$')"
check "--except matches a piece named with its binary's hash by the name without it" \
  "$(echo "$benchesk" | grep -v '::btree::bench::insertion_lookup_and_difference_scale_as_n_log_n$')" \
  "$(run --list --reuse-table --bench --only 'zed_kernel' --except '^zed_kernel::btree::bench::insertion_lookup_and_difference_scale_as_n_log_n$' | sort)"
out=$(run --list --reuse-table --bench --only '^l01_15_' --except '(')
rc=$?
check "an invalid --except exits 2" "2 --except: not a valid extended regular expression: (" "$rc $out"
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
# `short`: the short-addresses pieces, in fresh listings, since a --reuse-table run cannot list
# the binaries of an earlier run's clone. A part of its own, as each listing mounts the clone and
# waits while another run of the checkout has it mounted. A warm clone lists in 1.5 s at load 74.
if want short; then
logs=build/test-run-tests-short
# merge_check runs the parts at once, so a run here may find the clone mounted by another part's
# run, or still used by the processes of one that ended (seen next to `list`), wait and say so;
# those lines are left out of the output compared.
others() { grep -v -e '^Waiting for the run that has the short-addresses clone mounted at ' \
  -e '^Waiting for the processes of an ended run that still use the short-addresses clone'; }
# A test inside a short-addresses piece is selected as short-<group>::<path>, one piece each,
# run with --exact in the piece's folder (TOOL-short-piece-test-filter: such a pattern built the
# clone and selected nothing). The piece's binary lies in the listing's clone, unmounted when the
# run ends, so the tests are compared with those of the same module or step in the build without
# short-addresses, which has the same tests there.
plain=$(run --list --only '^zed_kernel::treap_set::' | sed 's/^zed_kernel-[0-9a-f]*::/short-zed_kernel::/' | sort)
check "zed_kernel's treap_set module has more than one test" "yes" \
  "$([ "$(echo "$plain" | wc -l)" -gt 1 ] && echo yes)"
check "a module of short-zed_kernel selects its tests, one piece each" "$plain" \
  "$(run --list --only '^short-zed_kernel::treap_set::' | others | sort)"
check "each runs its one test --exact in crates/zed-kernel" "" "$(awk '{ t = $1; sub(/^short-zed_kernel::/, "", t)
  if (NF != 5 || $2 != "crates/zed-kernel" || $4 != "--exact" || $5 != t) print }' "$(last_run)/pieces")"
bin37=$(run --list --only '^l01_37_oracle$' >/dev/null && awk 'NR == 1 { print $3 }' "$(last_run)/pieces")
t37=$("$bin37" --list --format terse | sed -n 's/: test$//p' | head -1)
check "a test of a short-addresses step is selected as short-<step>::<test>" "short-l01_37_oracle::$t37" \
  "$(run --list --only "^short-l01_37_oracle::$t37\$" | others)"
# A process that still uses the clone when its run ends (TOOL-short-clone-umount-busy: a rustc
# still exiting when a run killed during the clone's build ran its EXIT trap) is played by a
# sleep holding a file of the clone open, started while run a lists. Run a then unmounted its
# clone with "umount: .../short-clone: target is busy." and left the mount; now it ends with no
# message and no mount in the table, and run b, started while the sleep holds the clone, waits
# for it and then lists. Runs are started as commands, so that $! is the pid each run names its
# directory by. Run a's script is stopped from when its clone is seen mounted until the sleep
# has the clone open, so that it cannot reach its EXIT trap, which unmounts the clone, before
# then (its cargo goes on meanwhile): without the stop, a run a on a built tree could end in the
# 0.05 s between two looks at the mount table, and the sleep then held the folder under the
# mount point, so run b had nothing to wait for (seen once at load 93 on 2026-11-20).
tools/run_tests.sh --logs "$logs" --list --only '^short-zed_kernel::treap_set::' >"$logs.a" 2>&1 &
a=$!
mnt=
while [ -z "$mnt" ] && [ -d "/proc/$a" ]; do
  mnt=$(findmnt -rn -t overlay -o TARGET | grep -- "-$a/short-clone\$")
  [ -n "$mnt" ] || sleep 0.05
done
kill -STOP "$a"
# The sleep holds the clone's root directory open, as its standard input; run a goes on once
# the sleep has opened it.
sleep 600 <"$mnt" &
holder=$!
while [ -d "/proc/$holder" ] && [ "$(readlink "/proc/$holder/fd/0")" != "$mnt" ]; do sleep 0.01; done
kill -CONT "$a"
wait "$a"
rc_a=$?
check "the sleep held run a's clone while run a ended" "overlayfs" \
  "$(stat -L -f -c %T "/proc/$holder/fd/0" 2>&1)"
check "a run whose clone is still in use ends with no message" "0 $plain" "$rc_a $(others <"$logs.a" | sort)"
check "and leaves no mount" "" "$(findmnt -rn -t overlay -o TARGET | grep -- "-$a/short-clone\$")"
tools/run_tests.sh --logs "$logs" --list --only '^short-zed_kernel::treap_set::' >"$logs.b" 2>&1 &
b=$!
while [ -d "/proc/$b" ] && ! grep -q '^Waiting for the processes' "$logs.b"; do sleep 0.1; done
kill "$holder"
wait "$b"
rc_b=$?
check "a run started meanwhile waits for that process, then lists" "0 waited
$plain" "$rc_b $(grep -q '^Waiting for the processes of an ended run' "$logs.b" && echo waited)
$(others <"$logs.b" | sort)"
fi
# `copy`: a piece runs the build as it was when its run started (TOOL-run-build-copy): in
# kernel25's --bench run of 2026-11-20, 124 pieces failed with exit 127 when their test binaries
# started themselves again (the run at 8n) while a build in the same checkout had deleted the
# name of libzed_kernel-<hash>.so. The run here is started in a mount namespace of its own, and
# while its piece waits (tests/src/run_copy_tests.rs) the build's deps folder is made to hold
# the piece's test binary alone, in that namespace alone, so no other run of the checkout sees
# it: deps is mounted on a folder of turns/, an empty tmpfs on deps, and the binary from the
# first mount on an empty file in the tmpfs. The piece then starts its binary again. Before the
# copy that new process ended as kernel25's did: exit 127, "error while loading shared
# libraries: lib...-<hash>.so: cannot open shared object file".
if want copy; then
logs=build/test-run-tests-copy
mkdir -p "$logs"
turns=$(mktemp -d "$PWD/$logs/turns.XXXXXX")
ZED_TEST_RUN_COPY_TURNS=$turns unshare --mount tools/run_tests.sh --logs "$logs" \
  --only '^zed_tests::run_copy_tests::a_new_process_of_this_binary_starts_after_the_build_is_gone$' \
  >"$logs.out" 2>&1 &
a=$!
while [ -d "/proc/$a" ] && [ ! -e "$turns/ready" ]; do sleep 0.05; done
left=none
if [ -e "$turns/ready" ]; then
  bin=$(awk 'NR == 1 { print $3 }' "$(last_run)/pieces")
  deps=${bin%/*}
  mkdir "$turns/deps"
  nsenter --target "$a" --mount bash -c 'mount --bind "$1" "$2" && mount -t tmpfs tmpfs "$1" &&
    : >"$3" && mount --bind "$2/${3##*/}" "$3"' _ "$deps" "$turns/deps" "$bin" &&
    left=$(nsenter --target "$a" --mount ls -A "$deps")
fi
: >"$turns/go"
wait "$a"
rc=$?
check "in the run's namespace the build's deps folder holds the test binary alone while the piece waits" \
  "${bin##*/}" "$left"
check "the piece starts its binary again and passes" "0" "$rc"
[ "$rc" = 0 ] || cat "$logs.out"
check "the run deletes its copy of the build" "" "$(ls -d "$(last_run)/cargo" 2>/dev/null)"
check "and leaves no copy to delete" "" "$(ls -d "build/run-copy-dropped/$(basename "$(last_run)")" 2>/dev/null)"
# Runs of one checkout that end at the same time each delete their copy: merge_check runs
# several parts at once. When every run renamed its copy to the one name build/run-copy-dropped,
# a run that found another's copy there kept its own, or deleted the other's under it.
for i in 0 1 2 3; do
  tools/run_tests.sh --logs "$logs/at-once-$i" --only '^l01_06_lexer_tokens$' >"$logs.at-once-$i" 2>&1 &
done
wait
kept=
for i in 0 1 2 3; do
  r=$(readlink -f "$logs/at-once-$i/latest")
  [ -n "$r" ] && [ ! -e "$r/cargo" ] || kept="$kept $i"
  [ ! -e "build/run-copy-dropped/${r##*/}" ] || kept="$kept $i(dropped)"
done
check "four runs that end at once each delete their copy of the build" "" "$kept"
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
