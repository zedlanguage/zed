#!/bin/bash
# Tests tools/bench_limit.sh, the time limits of a benchmark piece's phases (author P214, A160 of
# 2026-11-20): the phase at n has the base limit, and a phase at 8n, which zed_tests::scaling
# starts by writing `<start> <10.5 × t1 ms>` to the file ZED_BENCH_LIMIT_FILE names, has
# max(base, 10.5 × t1), each counted from the phase's own start. Run from a checkout's root;
# about 25 s. The base here is 1 s, not 20 s, so the test is short; the scaling side's numbers at
# 20 s are tested in tests/src/scaling_tests.rs (bench_limit_*). It writes only
# build/test-bench-limit.limit, which each run overwrites and none deletes.
limit=$(pwd)/tools/bench_limit.sh
file=$(pwd)/build/test-bench-limit.limit
mkdir -p build
fails=0
. tools/test_lib.sh || exit 2
# A shell command that writes the phase line `<now - $1 ms> $2` to the limit file.
phase() { echo 'echo "$((${EPOCHREALTIME//[!0-9]/} / 1000 - '"$1"')) '"$2"'" >"$ZED_BENCH_LIMIT_FILE"'; }
# Runs the shell command $1 under a base limit of 1 s and prints its exit code.
run() {
  "$limit" 1 "$file" bash -c "$1"
  echo $?
}
# The phase at n: the base, from the command's start, or from the start of a phase at n written
# later (`<now> 0`, as each run at 8n ends).
check "a phase at n within the base passes" "0" "$(run 'sleep 0.6')"
check "a phase at n past the base is stopped (negative control)" "124" "$(run 'sleep 1.5')"
check "a later phase at n counts from its own start" "0" \
  "$(run "sleep 0.6; $(phase 0 0); sleep 0.6")"
check "a later phase at n past the base is stopped (negative control)" "124" \
  "$(run "sleep 0.3; $(phase 0 0); sleep 1.5")"
# The phase at 8n: max(base, the ms written), from the start written.
# BENCH-limit-counts-setup, scaled down: t1 = 0.4 s asks for 4.2 s. A run at 8n of ratio 10
# (4.0 s) passes; one of ratio 11 (4.4 s) is stopped; and the run of ratio 10 is stopped when
# its phase is counted from the start of the run at n, as before A160 (0.4 + 4.0 s).
check "a phase at 8n of ratio 10 over t1 passes" "0" "$(run "sleep 0.4; $(phase 0 4200); sleep 4.0")"
check "a phase at 8n of ratio 11 over t1 is stopped (negative control)" "124" \
  "$(run "sleep 0.4; $(phase 0 4200); sleep 4.4")"
check "a phase at 8n counted from the start of the run at n is stopped (negative control)" "124" \
  "$(run "sleep 0.4; $(phase 400 4200); sleep 4.0")"
check "a phase at 8n under the base keeps the base (negative control)" "124" \
  "$(run "$(phase 0 525); sleep 1.5")"
check "a phase at 8n counts from its own start" "0" \
  "$(run "sleep 0.8; $(phase 0 1500); sleep 1.2")"
check "a phase at 8n that started earlier is stopped from that start (negative control)" "124" \
  "$(run "sleep 0.8; $(phase 800 1500); sleep 1.2")"
check "a line in another form is ignored" "124" "$(run 'echo 2100 >"$ZED_BENCH_LIMIT_FILE"; sleep 1.5')"
check "a command's own exit code is kept" "3" "$(run 'exit 3')"
"$limit" 1 "$file" bash -c "$(phase 0 2100); sleep 0.3; $(phase 0 0); sleep 0.3"
check "the file holds the largest limit of a phase at the end" "2100" "$(cat "$file")"
# A command that ignores SIGTERM gets SIGKILL 5 s later; not run here (6 s).
[ "$fails" = 0 ] || { echo "$fails FAILED"; exit 1; }
echo "all passed"
