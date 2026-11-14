#!/bin/bash
# Times each correctness test alone. Usage, from a checkout's root, through
# /home/luke/Work/wt/zrun as tools/run_tests.sh is run:
#   tools/time_tests.sh [--only <ERE>] [--full] [jobs]
# It is tools/run_tests.sh --each-test with its own log directory, build/test-times: it builds as
# a run does, lists every correctness test the selection holds (no benchmark, no test whose path
# holds `bench::`), and runs each one alone, `--exact <test>` in a process of its own, with the
# same slots, slice and limit as a run's pieces (20 s, more under load). Then it writes
# build/test-logs/test-times.tsv: a header and a line per test, group, test, ms, rc and load,
# slowest first. The group is the piece's group as --only names it (a crate's test binary without
# its hash); ms is the wall time of the test's process, rc its exit code (124 or 137 past the
# limit) and load the load average when it started. A test that fails keeps its output in
# build/test-times/<group>::<test>.log. The exit code is that of the run.
# Its own log directory lets it run beside a tools/run_tests.sh run of the same checkout, which
# uses build/test-logs (TEST-bench-split, author P169).
tools/run_tests.sh --each-test --logs build/test-times "$@"
rc=$?
if [ ! -s build/test-times/summary ] || [ ! -s build/test-times/pieces ]; then
  exit "$rc"
fi
mkdir -p build/test-logs
{
  printf 'group\ttest\tms\trc\tload\n'
  awk '
    $2 ~ /^rc=/ && $3 ~ /ms$/ && $4 ~ /^load=/ {
      group = $1
      sub(/::.*/, "", group)
      sub(/-[0-9a-f]+$/, "", group)
      test = substr($1, index($1, "::") + 2)
      ms = $3
      sub(/ms$/, "", ms)
      printf "%s\t%s\t%s\t%s\t%s\n", group, test, ms, substr($2, 4), substr($4, 6)
    }' build/test-times/summary | sort -t "$(printf '\t')" -k 3,3nr -k 1,2
} >build/test-logs/test-times.tsv
echo "test times: build/test-logs/test-times.tsv, $(($(wc -l <build/test-logs/test-times.tsv) - 1)) tests"
exit "$rc"
