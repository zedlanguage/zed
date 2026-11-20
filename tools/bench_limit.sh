#!/bin/bash
# Runs a benchmark under a time limit for each of its phases (author P214, A160 of 2026-11-20), in
# place of `timeout -k 5 <seconds>`. Usage: tools/bench_limit.sh <seconds> <file> <command>...
# The command runs in phases, each under a limit counted from the phase's own start: the first
# phase starts with the command and has the limit <seconds> (the runner's limit, raised with
# load), and each line `<start> <ms>` written to <file> starts a new phase at <start>
# (milliseconds since 1970) with the limit max(<seconds>, <ms> milliseconds). zed_tests::scaling
# writes these lines through the variable ZED_BENCH_LIMIT_FILE, which this script sets to <file>:
# as each run at 8n starts, `<now> <10.5 × t1>`, t1 the time of the run at n just measured, and as
# it ends, `<now> 0`, so what follows (the next check's inputs and its run at n) has the runner's
# limit again. A line in any other form is ignored. Past the limit of its phase the command gets
# SIGTERM, and SIGKILL 5 s later if it is still running, and the script exits 124, as timeout
# does; otherwise it exits as the command did. Either way it then writes the largest limit any
# phase had, in milliseconds, to <file>, which tools/run_tests.sh prints as the piece's limit. It
# looks at the clock and the file every 0.1 s, so a command may run up to 0.1 s past its limit.
# tools/run_tests.sh --bench runs each benchmark piece so; the correctness pieces keep timeout.
base_ms=$(($1 * 1000)) file=$2
shift 2
: >"$file"
ZED_BENCH_LIMIT_FILE=$file "$@" &
pid=$!
# EPOCHREALTIME is seconds and microseconds, always six digits of them: the digits are microseconds.
phase_start=$((${EPOCHREALTIME//[!0-9]/} / 1000)) phase_ms=0 most=$base_ms
while kill -0 "$pid" 2>/dev/null; do
  line=
  read -r line <"$file"
  if [[ $line =~ ^([0-9]+)\ ([0-9]+)$ ]]; then
    phase_start=${BASH_REMATCH[1]} phase_ms=${BASH_REMATCH[2]}
  fi
  limit=$base_ms
  ((phase_ms <= limit)) || limit=$phase_ms
  ((limit <= most)) || most=$limit
  now=$((${EPOCHREALTIME//[!0-9]/} / 1000))
  if ((now - phase_start >= limit)); then
    echo "bench_limit.sh: stopped: a phase took $((now - phase_start)) ms, past its limit of $limit ms" >&2
    kill -TERM "$pid"
    for _ in $(seq 50); do
      kill -0 "$pid" 2>/dev/null || break
      sleep 0.1
    done
    kill -0 "$pid" 2>/dev/null && kill -KILL "$pid"
    wait "$pid"
    echo "$most" >"$file"
    exit 124
  fi
  sleep 0.1
done
wait "$pid"
rc=$?
echo "$most" >"$file"
exit "$rc"
