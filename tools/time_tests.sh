#!/bin/bash
# Times each correctness test alone. Usage, from a checkout's root, through
# /home/luke/Work/wt/zrun as tools/run_tests.sh is run:
#   tools/time_tests.sh [--only <ERE>] [--full] [jobs]
# It is tools/run_tests.sh --each-test with its logs under build/test-times: it builds as a run
# does, lists every correctness test the selection holds (no benchmark, no test whose path holds
# `bench::`), and runs each one alone, `--exact <test>` in a process of its own, with the same
# jobs, slice and limit as a run's pieces (20 s, more under load). Then it writes test-times.tsv
# in the run's log directory, build/test-times/<UTC time>-<pid>, and publishes a copy as
# build/test-logs/test-times.tsv by a rename: a header and a line per test, group, test, ms, rc
# and load, slowest first. The group is the piece's group as --only names it (a crate's test
# binary without its hash); ms is the wall time of the test's process, rc its exit code (124 or
# 137 past the limit) and load the load average when it started. A test that fails keeps its
# output in <the run's log directory>/<group>::<test>.log. The exit code is that of the run.
# The run's log directory is the one tools/run_tests.sh names on its line `logs: <dir>`; until
# NO-LOCKS-optimistic it was build/test-times itself, one run at a time. Runs beside it, of either
# script, share none of its files.
dir= rc=
while IFS= read -r line; do
  if [[ $line =~ ^time_tests-exit=([0-9]+)$ ]]; then
    rc=${BASH_REMATCH[1]}
    continue
  fi
  printf '%s\n' "$line"
  [ -n "$dir" ] || [[ $line != "logs: "* ]] || dir=${line#logs: }
done < <(tools/run_tests.sh --each-test --logs build/test-times "$@"; echo "time_tests-exit=$?")
if [ -z "$dir" ] || [ ! -s "$dir/summary" ] || [ ! -s "$dir/pieces" ]; then
  exit "${rc:-1}"
fi
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
    }' "$dir/summary" | sort -t "$(printf '\t')" -k 3,3nr -k 1,2
} >"$dir/test-times.tsv"
mkdir -p build/test-logs
cp "$dir/test-times.tsv" "build/test-logs/test-times.tsv.$$" &&
  mv -T "build/test-logs/test-times.tsv.$$" build/test-logs/test-times.tsv
echo "test times: build/test-logs/test-times.tsv (from $dir), $(($(wc -l <"$dir/test-times.tsv") - 1)) tests"
exit "${rc:-1}"
