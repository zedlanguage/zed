#!/bin/bash
# Runs every test in pieces, one test binary or step folder each, each under a 60 s limit, and
# prints a line per piece as it ends. Usage: tools/run_tests.sh [jobs], from a checkout's root.
# A failed piece keeps its output in build/test-logs/<piece>.log. Every piece runs in the
# systemd slice zedtests.slice, whose 112 GB limit holds across all checkouts together.
jobs=${1:-6}
root=$(pwd)
out=$root/build/test-logs
mkdir -p "$out"
if ! cargo test --workspace --no-run --message-format=short >"$out/build.log" 2>&1; then
  tail -40 "$out/build.log"
  echo "BUILD FAILED"
  exit 1
fi
bins=$(sed -n "s|^ *Executable .*(\(.*\))$|$root/\1|p" "$out/build.log")
steps=$(echo "$bins" | grep '/steps-')
{
  for p in $bins; do
    n=$(basename "$p")
    case $n in
      steps-*) ;;
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
} >"$out/pieces"
export root out
piece() {
  name=$1 dir=$2
  shift 2
  log=$out/$name.log
  start=$(date +%s%N)
  (cd "$root/$dir" && CARGO_MANIFEST_DIR=$root/$dir \
    systemd-run --user --scope --quiet --same-dir --slice=zedtests.slice \
    timeout -k 5 60 "$@" >"$log" 2>&1)
  rc=$?
  ms=$((($(date +%s%N) - start) / 1000000))
  echo "$name rc=$rc ${ms}ms $(grep -E '^test result' "$log" | tail -1)"
  [ "$rc" = 0 ] && rm -f "$log"
  [ "$rc" = 0 ]
}
export -f piece
xargs -P "$jobs" -L 1 bash -c 'piece "$@"' _ <"$out/pieces" | tee "$out/summary"
bad=$(grep -vc 'rc=0 ' "$out/summary")
echo "pieces: $(wc -l <"$out/summary"), failed: $bad"
[ "$bad" = 0 ]
