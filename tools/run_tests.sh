#!/bin/bash
# Runs every test in pieces, one test binary, step folder, module or slow test each, each under a
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
# Cargo prints a binary path relative to the checkout only when the target directory is inside it.
bins=$(sed -n -e "s|^ *Executable .*(\(/.*\))$|\1|p" -e "s|^ *Executable .*(\([^/].*\))$|$root/\1|p" "$out/build.log")
full=$(echo "$bins" | grep '/full-')
# The short-addresses build (step L1.37a) keeps 8 bits of every content address and type digest,
# so distinct values collide; its pieces check that every place that compares by address
# confirms equal addresses by contents, and that verdicts and outputs match the full build.
short_steps="l01_37a_short_addresses l01_37_oracle"
if ! CARGO_TARGET_DIR=$root/build/short cargo test -p zed-tests --features short-addresses \
  $(printf -- '--test %s ' $short_steps) --no-run --message-format=short >"$out/build-short.log" 2>&1; then
  tail -40 "$out/build-short.log"
  echo "BUILD FAILED (short-addresses)"
  exit 1
fi
short=$(sed -n -e "s|^ *Executable .*(\(/.*\))$|\1|p" -e "s|^ *Executable .*(\([^/].*\))$|$root/\1|p" \
  "$out/build-short.log")
# The documentation of every crate, private items included, builds with no warning, so a link
# in a doc comment that names no item, or a citation written as a link, fails the run.
if ! RUSTDOCFLAGS='-D warnings' cargo doc --no-deps --document-private-items >"$out/doc.log" 2>&1; then
  tail -40 "$out/doc.log"
  echo "DOC FAILED"
  exit 1
fi
# Each step folder is a test binary of its own, named after the folder (tests/Cargo.toml), and a
# test's name in it is its module path within the folder. A step folder or module named here
# gets a piece for each of its modules and each of its own tests instead of one piece; the rest
# get one piece each. Named because together they ran past
# 60 s at load 100 (l01_25 138 s, l01_38 94 s, l01_36 89 s, l01_16 72 s, l01_08 64 s; l01_23
# 29 to 35 s at load 53, with tests of 36, 32 and 15 s); the modules are those with a test over
# 10 s there, so each of those tests has a process of its own. l01_38 names ran past 60 s at
# load 80 once the orbit tests (11 to 15 s each) joined it, and live3 at load 76 to 95, where
# `slabs_of_million_coefficients_scale` takes 38 s alone (2026-11-05).
# l01_38 shared and stages were added in UTVPI-union verify, where they took 49 and 36 s whole
# at load 77 with the other modules running.
split="
  l01_08_parser l01_16_elaboration l01_16_elaboration::scaling
  l01_23_subtyping l01_23_subtyping::scaling
  l01_25_preimage_catalog l01_25_preimage_catalog::s22
  l01_36_cranelift l01_36_cranelift::scaling l01_36_cranelift::table
  l01_38_presburger l01_38_presburger::oracle l01_38_presburger::omega
  l01_38_presburger::scaling l01_38_presburger::deep
  l01_38_presburger::names l01_38_presburger::live3
  l01_38_presburger::shared l01_38_presburger::stages
"
# The pieces of step folder $1 in the test binary $2, or of its module $3 (a path in the
# binary) when one is given. A module's piece filters by `$3::`, which libtest matches anywhere in
# a name, so it is a piece only when every test matching the filter lies in the module; otherwise
# each of the module's tests is a piece.
step_pieces() {
  local name=$1${3:+::$3} prefix=${3:+$3::} tests
  if ! tests=$("$2" --list --format terse ${prefix:+"$prefix"}); then
    echo "$name tests $2${prefix:+ $prefix}"
    return
  fi
  tests=$(echo "$tests" | sed -n "s/: test$//p")
  case " $(echo $split) " in
    *" $name "*) ;;
    *)
      if [ -z "$prefix" ] || ! echo "$tests" | grep -qv "^$prefix"; then
        echo "$name tests $2${prefix:+ $prefix}"
        return
      fi
      ;;
  esac
  tests=$(echo "$tests" | sed -n "s/^\($prefix[^:]*\)\(.*\)$/\1 \2/p")
  for t in $(echo "$tests" | sed -n 's/ $//p'); do
    echo "$1::$t tests $2 --exact $t"
  done
  for m in $(echo "$tests" | sed -n 's/ ::.*//p' | sort -u); do
    step_pieces "$1" "$2" "$m"
  done
}
{
  for p in $bins; do
    n=$(basename "$p")
    if [ -d "tests/steps/${n%-*}" ]; then
      step_pieces "${n%-*}" "$p"
      continue
    fi
    case $n in
      full-*) ;;
      deep_values-* | deep_scaling-* | deep_heap-*)
        # Tests of many gigabytes at once slow each other through the lock on the address space
        # of their process: 59 s together against 17 s alone at load 50. Each gets a process.
        # deep_heap also compiles functions of up to 20,000 concatenations natively.
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
  for p in $short; do
    echo "short-$(basename "${p%-*}") tests $p"
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
