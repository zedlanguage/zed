#!/bin/bash
# Builds the DynamoRIO client zed_icount (zed_icount.c) into <out dir>/libzed_icount.so.
# Usage: tools/icount/build.sh <DynamoRIO release dir> <out dir>
# The release dir is an unpacked DynamoRIO-Linux-*.tar.gz (job.sh's VM setup puts 11.3.0 at
# /opt/dynamorio). Needs cmake and a C compiler. Runs the client's self-test (selftest.c) under
# it, and prints the path of the client when the test passes.
dr=$1
out=$2
if [ -z "$dr" ] || [ -z "$out" ]; then
  echo "usage: $0 <DynamoRIO release dir> <out dir>" >&2
  exit 2
fi
src=$(dirname "$(readlink -f "$0")")
mkdir -p "$out" || exit 1
cmake -S "$src" -B "$out" -DDynamoRIO_DIR="$dr/cmake" -DCMAKE_BUILD_TYPE=RelWithDebInfo > "$out/cmake.log" 2>&1 ||
  { cat "$out/cmake.log" >&2; exit 1; }
cmake --build "$out" > "$out/build.log" 2>&1 || { cat "$out/build.log" >&2; exit 1; }
# The client's own checks (selftest.c), under the client.
"$dr/bin64/drrun" -c "$out/libzed_icount.so" -- "$out/zed_icount_selftest" > "$out/selftest.log" 2>&1 ||
  { echo "zed_icount's self-test failed:" >&2; cat "$out/selftest.log" >&2; exit 1; }
echo "$out/libzed_icount.so"
