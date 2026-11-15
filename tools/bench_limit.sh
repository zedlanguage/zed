#!/bin/bash
# Runs a benchmark under a time limit that the benchmark may raise (author P214), in place of
# `timeout -k 5 <seconds>`. Usage: tools/bench_limit.sh <seconds> <file> <command>...
# The limit is max(<seconds>, the milliseconds last written to <file>): zed_tests::scaling
# writes LIMIT × t1 there (10.5 times the time of the first run at the 1x size, rounded up to a
# millisecond) as soon as that run ends, through the variable ZED_BENCH_LIMIT_FILE, which this
# script sets to <file>. Past the limit the command gets SIGTERM, and SIGKILL 5 s later if it is
# still running, and the script exits 124, as timeout does; otherwise it exits as the command
# did. It looks at the clock and the file every 0.1 s, so a command may run up to 0.1 s past its
# limit. tools/run_tests.sh --bench runs each benchmark piece so; the correctness pieces keep
# timeout.
base_ms=$(($1 * 1000)) file=$2
shift 2
: >"$file"
ZED_BENCH_LIMIT_FILE=$file "$@" &
pid=$!
start=${EPOCHREALTIME//[!0-9]/}
while kill -0 "$pid" 2>/dev/null; do
  raised=
  read -r raised <"$file"
  limit=$base_ms
  if [[ $raised =~ ^[0-9]+$ ]] && ((raised > limit)); then limit=$raised; fi
  now=${EPOCHREALTIME//[!0-9]/}
  if (((now - start) / 1000 >= limit)); then
    kill -TERM "$pid"
    for _ in $(seq 50); do
      kill -0 "$pid" 2>/dev/null || break
      sleep 0.1
    done
    kill -0 "$pid" 2>/dev/null && kill -KILL "$pid"
    wait "$pid"
    exit 124
  fi
  sleep 0.1
done
wait "$pid"
