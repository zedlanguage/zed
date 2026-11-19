#!/bin/bash
# Tests tools/bench_limit.sh, the time limit of a benchmark piece (author P214): max(the base
# limit, the milliseconds the benchmark writes to the file ZED_BENCH_LIMIT_FILE names, which
# zed_tests::scaling sets to 10.5 × t1). Run from a checkout's root; about 4 s. The base here is
# 1 s, not 20 s, so the test is short; the scaling side's numbers at 20 s are tested in
# tests/src/scaling_tests.rs (bench_limit_*). It writes only build/test-bench-limit.limit, which
# each run overwrites and none deletes.
limit=$(pwd)/tools/bench_limit.sh
file=$(pwd)/build/test-bench-limit.limit
mkdir -p build
fails=0
. tools/test_lib.sh || exit 2
# Runs a command of 1.5 s that first writes $1 to the limit file, under a base limit of 1 s:
# prints its exit code and whole seconds taken.
run() {
  local start=$SECONDS
  "$limit" 1 "$file" bash -c 'echo '"$1"' >"$ZED_BENCH_LIMIT_FILE"; sleep 1.5'
  echo "$? $((SECONDS - start))"
}
# A 1x of 0.2 s asks for 2100 ms, over the base: the command ends in its own time.
check "a 1x over base / 10.5 raises the limit" "0" "$(run 2100 | cut -d ' ' -f 1)"
# A 1x of 0.05 s asks for 525 ms, under the base: the base holds and the command is stopped.
check "a 1x under base / 10.5 keeps the base" "124" "$(run 525 | cut -d ' ' -f 1)"
check "nothing written keeps the base" "124" \
  "$("$limit" 1 "$file" sleep 1.5; echo $?)"
check "a command's own exit code is kept" "3" "$("$limit" 1 "$file" bash -c 'exit 3'; echo $?)"
# A command that ignores SIGTERM gets SIGKILL 5 s later; not run here (6 s).
[ "$fails" = 0 ] || { echo "$fails FAILED"; exit 1; }
echo "all passed"
