#!/bin/bash
# Runs every test in pieces, one test binary, step folder or very large test each, each under a
# 60 s limit, and prints a line per piece as it ends. Usage: tools/run_tests.sh [--full] [jobs],
# from a checkout's root. Without --full this is the local suite, which needs only the Rust
# toolchain and runs in CI.
# --full adds tests/full/, the battery that needs emulators, containers, databases and other
# outside tools. It stops before any test if a tool is missing; nothing is skipped.
# A failed piece keeps its output in build/test-logs/<piece>.log. Every piece runs in the
# systemd slice zedtests.slice, whose 112 GB limit holds across all checkouts together. A load
# above the number of cores raises the limit of the pieces that start under it in proportion.
features=
if [ "$1" = --full ]; then
  shift
  features=--features=zed-tests/full
  ZED_TEST_DEPS=${XDG_CACHE_HOME:-$HOME/.cache}/zed-test-deps
  export ZED_TEST_DEPS
  missing=
  for t in $(cat tests/full/*/needs | sort -u); do
    command -v "$t" >/dev/null || missing="$missing $t"
  done
  if [ -n "$missing" ]; then
    echo "MISSING TOOLS:$missing"
    exit 1
  fi
  if [ ! -e "$ZED_TEST_DEPS/done" ]; then
    echo "MISSING $ZED_TEST_DEPS: run tools/fetch_test_deps.sh"
    exit 1
  fi
fi
jobs=${1:-6}
root=$(pwd)
out=$root/build/test-logs
mkdir -p "$out"
if ! cargo test --workspace $features --no-run --message-format=short >"$out/build.log" 2>&1; then
  tail -40 "$out/build.log"
  echo "BUILD FAILED"
  exit 1
fi
bins=$(sed -n "s|^ *Executable .*(\(.*\))$|$root/\1|p" "$out/build.log")
steps=$(echo "$bins" | grep '/steps-')
full=$(echo "$bins" | grep '/full-')
{
  for p in $bins; do
    n=$(basename "$p")
    case $n in
      steps-* | full-*) ;;
      deep_values-* | deep_scaling-*)
        # Tests of many gigabytes at once slow each other through the lock on the address space
        # of their process: 59 s together against 17 s alone at load 50. Each gets a process.
        if tests=$("$p" --list --format terse); then
          for t in $(echo "$tests" | sed -n "s/: test$//p"); do
            echo "$t tests $p --exact $t"
          done
        else
          echo "$n tests $p"
        fi
        ;;
      zedc-*) echo "$n crates/zedc $p" ;;
      zed_kernel-*) echo "$n crates/zed-kernel $p" ;;
      zed_native-*) echo "$n crates/zed-native $p" ;;
      zed_rt-*) echo "$n crates/zed-rt $p" ;;
      zed_cert-*) echo "$n crates/zed-cert $p" ;;
      *) echo "$n tests $p" ;;
    esac
  done
  for d in tests/steps/*/; do
    n=$(basename "$d")
    echo "$n tests $steps $n::"
  done
  if [ -n "$full" ]; then
    for d in tests/full/*/; do
      n=$(basename "$d")
      echo "$n tests $full $n::"
    done
  fi
} >"$out/pieces"
# At most `slots` pieces run at once on this machine, whichever checkout started them. A piece holds
# a lock on one file of $slot_dir until it ends, so a killed run frees its slots, and its 60 s start
# when it has one. Four suites at once took 2:13 with 8 slots and 2:05 without, and the longest
# piece 28 s against 53 s.
slots=8
slot_dir=${XDG_RUNTIME_DIR:-/tmp}/zedtests-slots
mkdir -p "$slot_dir"
# glibc's memcpy and memset use rep movsb and rep stosb on a CPU with erms or fsrm, and the hardware
# counter sees either as one instruction or few, so a quadratic copy would pass a scaling test. A
# setting glibc does not know is ignored; this glibc leaves the stosb threshold alone without erms.
never=0xffffffffffffffff
export GLIBC_TUNABLES=glibc.cpu.hwcaps=-ERMS,-FSRM:glibc.cpu.x86_rep_movsb_threshold=$never:glibc.cpu.x86_rep_stosb_threshold=$never
cores=$(nproc)
export root out slots slot_dir cores
take_slot() {
  while :; do
    for i in $(seq "$slots"); do
      exec 9>"$slot_dir/$i"
      flock -n 9 && return
    done
    sleep 0.1
  done
}
piece() {
  name=$1 dir=$2
  shift 2
  log=$out/$name.log
  take_slot
  read -r load _ </proc/loadavg
  limit=$(awk -v l="$load" -v c="$cores" 'BEGIN { x = 60 * l / c; print (x > 60 ? int(x + 1) : 60) }')
  start=$(date +%s%N)
  (cd "$root/$dir" && CARGO_MANIFEST_DIR=$root/$dir \
    systemd-run --user --scope --quiet --same-dir --slice=zedtests.slice \
    timeout -k 5 "$limit" "$@" >"$log" 2>&1)
  rc=$?
  ms=$((($(date +%s%N) - start) / 1000000))
  echo "$name rc=$rc ${ms}ms load=$load limit=${limit}s $(grep -E '^test result' "$log" | tail -1)"
  [ "$rc" = 0 ] && rm -f "$log"
  [ "$rc" = 0 ]
}
export -f take_slot piece
xargs -P "$jobs" -L 1 bash -c 'piece "$@"' _ <"$out/pieces" | tee "$out/summary"
bad=$(grep -vc 'rc=0 ' "$out/summary")
load=$(awk 'match($0, / load=[0-9.]+/) {
  l = substr($0, RSTART + 6, RLENGTH - 6) + 0
  if (NR == 1 || l < low) low = l
  if (l > high) high = l
} END { print low " to " high }' "$out/summary")
echo "pieces: $(wc -l <"$out/summary"), failed: $bad, load: $load, cores: $cores"
[ "$bad" = 0 ]
