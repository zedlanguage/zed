#!/bin/bash
# Measures one test the same way at any commit, whatever meter that commit's tests/src/scaling.rs
# has (row BENCH-unary-arms-wall-near-limit: the runner and the meter of 23efa911a do not run on
# a Colab VM, and its count came from a hardware counter that VMs lack). It builds the test
# target in the current tree, runs the test alone natively <runs> times, timed, then once under
# DynamoRIO's sample client inscount, which counts every instruction of the process: the input's
# set-up, both sizes and the meter's own work, so it is comparable between two commits only, not
# with the counts a scaling test prints. The tree's own tools are not used, so it can be copied
# into a tree of an older commit and run there (a `!` line of Colab job.sh, from the tree's root).
# Usage: tools/icount/count_test.sh <test target of zed-tests> <test name> <out dir> [runs]
# Prints one line per run, "native <k> rc <rc> wall <s> cpu <s>", then "inscount rc <rc> <n> in
# <p> processes instructions wall <s>".
target=${1-}
name=${2-}
out=${3-}
runs=${4-3}
[ -n "$target" ] && [ -n "$name" ] && [[ $out == /?* ]] && [[ $runs =~ ^[0-9]+$ ]] ||
  { echo "usage: $0 <test target> <test name> <absolute out dir> [runs]" >&2; exit 2; }
mkdir -p "$out" || exit 1
dr=${ZED_DYNAMORIO-/opt/dynamorio}
cargo test -p zed-tests --test "$target" --no-run --message-format=short > "$out/build.log" 2>&1 ||
  { cat "$out/build.log"; exit 4; }
bin=$(command grep -a -o -E "\(([^()]*/deps/$target-[0-9a-f]+)\)" "$out/build.log" | tr -d '()' | tail -n 1)
[ -x "$bin" ] || { echo "no test binary for $target in $out/build.log" >&2; exit 4; }
full=$("$bin" --list 2>/dev/null | sed -n 's/: test$//p' | command grep -a -E "(^|::)$name\$")
[ "$(printf '%s\n' "$full" | command grep -a -c .)" = 1 ] ||
  { echo "the name $name matches no test or several: $full" >&2; exit 2; }
echo "binary $bin test $full commit $(git rev-parse --short HEAD 2>/dev/null || echo unknown)"
# The environment of the benchmarks (tools/run_tests.sh), and no DynamoRIO meter of the tree's
# own, so that each commit's test runs its own way and only this script counts.
export GLIBC_TUNABLES='glibc.cpu.hwcaps=-ERMS,-FSRM:glibc.cpu.x86_rep_movsb_threshold=0xffffffffffffffff:glibc.cpu.x86_rep_stosb_threshold=0xffffffffffffffff'
unset ZED_METER_DRRUN ZED_METER_ICOUNT
for k in $(seq 1 "$runs"); do
  /usr/bin/time -f "%e %U %S" -o "$out/time.$k" "$bin" "$full" --exact --test-threads=1 --nocapture \
    > "$out/native.$k.log" 2>&1
  rc=$?
  read -r wall user sys < "$out/time.$k"
  echo "native $k rc $rc wall $wall cpu $(awk -v u="$user" -v s="$sys" 'BEGIN { print u + s }')"
done
client=$dr/samples/bin64/libinscount.so
[ -f "$client" ] || { echo "no $client: inscount is not run" >&2; exit 3; }
/usr/bin/time -f "%e" -o "$out/time.dr" "$dr/bin64/drrun" -c "$client" -- "$bin" "$full" --exact \
  --test-threads=1 --nocapture > "$out/inscount.log" 2>&1
rc=$?
# DynamoRIO follows the processes the test starts (a scaling test's process for 8n), and the
# client prints a count at each one's exit: the sum is the whole run's.
counts=$(command grep -a -o -E '[0-9]+ instructions executed' "$out/inscount.log" | cut -d' ' -f1)
n=$(printf '%s\n' "$counts" | awk 'NF { s += $1; k++ } END { if (k) print s " in " k " processes"; else print "none" }')
echo "inscount rc $rc $n instructions wall $(cat "$out/time.dr")"
