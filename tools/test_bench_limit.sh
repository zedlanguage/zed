#!/bin/bash
# Tests tools/bench_limit.sh, the time limits of a benchmark piece's phases (author P214, A160 of
# 2026-11-20): the phase at n has the base limit, and a phase at 8n, which zed_tests::scaling
# starts by writing `<start> <10.5 × t1 ms>` to the file ZED_BENCH_LIMIT_FILE names, has
# max(base, 10.5 × t1), each counted from the phase's own start. Run from a checkout's root;
# about 25 s. The base here is 1 s, not 20 s, so the test is short; the scaling side's numbers at
# 20 s are tested in tests/src/scaling_tests.rs (bench_limit_*). It writes only
# build/test-bench-limit.limit, build/test-bench-limit.pid and the fake cargo's files in
# build/test-bench-limit-bin, which each run overwrites and none deletes.
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
# A command stopped at its limit takes the processes it started with it: zed_tests::scaling runs
# each run at 8n in a process of its own, and on 2026-11-20 one of them ran on for 19 minutes,
# holding 67 to 71 GB, after its test binary was stopped (bench_limit.sh signaled only the
# command's pid then). The command here starts `sleep 30` and waits on it; 0.2 s after the stop
# the sleep must be gone. If it is not, the test kills it by its pid, so nothing is left running.
pidfile=$(pwd)/build/test-bench-limit.pid
: >"$pidfile"
"$limit" 1 "$file" bash -c "sleep 30 & echo \$! >'$pidfile'; wait"
stopped=$?
sleep 0.2
child=$(cat "$pidfile")
if [ -n "$child" ] && kill -0 "$child" 2>/dev/null; then
  state=running
  kill -KILL "$child"
else
  state=gone
fi
check "a command stopped at its limit takes the process it started with it" "124 gone" "$stopped $state"
# A cargo test or cargo bench command builds its test binaries outside every limit
# (FARM-bench-line-compile-in-limit): a bench line `tools/bench_limit.sh 20 <file> cargo test ...`
# of b22-kept5's job 33 spent its first phase's 20 s rebuilding the zed-kernel dylib (7.log:
# Compiling zed-kernel, then the stop), so the bench never ran and read as a slow one. A fake
# cargo, first on PATH, stands for it: a first call builds for 1.5 s (a marker file, emptied before each
# case, then says it is built), a call with --no-run then ends, and a run takes 0.3 s; each call's arguments go to a
# file. The base is 1 s, so a build inside the limit is stopped.
bin=$(pwd)/build/test-bench-limit-bin
mkdir -p "$bin"
cat >"$bin/cargo" <<'EOF'
#!/bin/bash
echo "$*" >>"$FAKE_CARGO_DIR/calls"
[ -z "${FAKE_CARGO_FAIL-}" ] || exit 101
[ -s "$FAKE_CARGO_DIR/built" ] || { sleep 1.5; echo built >"$FAKE_CARGO_DIR/built"; }
for a; do [ "$a" = --no-run ] && exit 0; done
sleep 0.3
EOF
chmod +x "$bin/cargo"
# Runs cargo with the arguments under a base limit of 1 s, from a fresh fake build, and prints
# its exit code and then each call's arguments, a line each.
run_cargo() {
  : >"$bin/calls"
  : >"$bin/built"
  PATH=$bin:$PATH FAKE_CARGO_DIR=$bin "$limit" 1 "$file" cargo "$@" 2>/dev/null
  echo $?
  cat "$bin/calls"
}
check "a cargo test command is built before its first phase starts" \
  "0
test -p zed-tests --test l01_38 --no-run
test -p zed-tests --test l01_38 -- bench:: --exact" \
  "$(run_cargo test -p zed-tests --test l01_38 -- bench:: --exact)"
check "a cargo bench command is built so too" "0
bench -p a --no-run
bench -p a" "$(run_cargo bench -p a)"
check "a failed build ends with cargo's exit code and runs nothing" "101
test -p a --no-run" "$(FAKE_CARGO_FAIL=1 run_cargo test -p a)"
check "another command is not built first, so its build is in the limit (negative control)" "124
check -p a" "$(run_cargo check -p a)"
# A command that ignores SIGTERM gets SIGKILL 5 s later; not run here (6 s).
[ "$fails" = 0 ] || { echo "$fails FAILED"; exit 1; }
echo "all passed"
