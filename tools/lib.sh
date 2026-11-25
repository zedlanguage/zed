# Functions shared by the tools' shell scripts (tools/run_tests.sh, tools/merge_check.sh), sourced.

# piece_limit [cores]: sets $load to the 1-minute load average and $limit to the time limit of one
# piece of tools/run_tests.sh in whole seconds, max(20, 20 × load / cores) (author P169/P214: 20 s
# per piece, more in proportion when the machine is loaded beyond its cores, so a piece that
# passes in 20 s alone is not killed by other agents' work). cores defaults to nproc; a caller
# that sets many limits passes it, saving a process each time.
piece_limit() {
  local _
  read -r load _ </proc/loadavg
  limit=$(awk -v l="$load" -v c="${1:-$(nproc)}" 'BEGIN { x = 20 * l / c; print (x > 20 ? int(x + 1) : 20) }')
}

# warm <piece name> <step folder> <binary> <arguments...>: runs one piece of tools/run_tests.sh
# before the timed pieces, with no limit, so that the links it makes are kept (run_tests.sh, before
# its slots), in $root/<step folder>, through `capped` and `in_run_copy`, its output in
# $out/warm-$slot.out. Prints "<name> links made before the timed pieces: rc=<rc> <ms>ms" and
# returns 0 exactly when the piece passed. A piece that fails keeps its whole output in
# $out/warm-<name>.log and prints that path and its last 20 lines that name a failure (a panic,
# a failed test, a timeout, an error), or its last 20 lines when none does, each line after
# "<name> warm: ": until 2026-11-24 the output was emptied unread, and five binaries that failed
# here at load 67 left no cause (FAIL-warm-step-drops-output; b22-eqsrest5's patch printed the
# matching lines only). Test: tools/test_run_tests.sh warm.
warm() {
  local name=$1 dir=$2 start rc kept
  shift 2
  start=$(date +%s%N)
  (cd "$root/$dir" && CARGO_MANIFEST_DIR=$root/$dir \
    capped bash -c 'in_run_copy "$@"' in_run_copy "$1" "$@" >"$out/warm-$slot.out" 2>&1)
  rc=$?
  if [ "$rc" != 0 ]; then
    kept=$out/warm-$name.log
    cp "$out/warm-$slot.out" "$kept"
    echo "$name warm: output kept in $kept"
    { command grep -a -E 'panicked|FAILED|failed|timed out|has been running|error|signal' "$kept" ||
      cat "$kept"; } | tail -n 20 | sed "s|^|$name warm: |"
  fi
  : >"$out/warm-$slot.out"
  echo "$name links made before the timed pieces: rc=$rc $((($(date +%s%N) - start) / 1000000))ms"
  [ "$rc" = 0 ]
}

# warm_all <linking file> <jobs> <cores>: runs `warm` on each line of the file (its arguments),
# the first line alone and then the others side by side, at most <jobs> at once, each with
# RUST_TEST_THREADS = <cores> / min(<jobs>, the number of other lines), at least 1. Returns 0
# exactly when every piece passed. `warm`, `capped` and `in_run_copy` must be exported, since
# xargs runs each piece in a new bash. The first piece runs alone so that it makes the prelinked
# runtime (crates/zed-native/src/link.rs, `prelinked`) and the others find it made. The bound on
# the threads: each test runs `zedc build` under `timeout 60`, and a test binary runs as many
# tests at once as there are cores, so on v5e6 (24 cores) the 11 side pieces with no bound
# reached load 379, and 15 tests of 5 pieces failed with exit 124 (FAIL-warm-binaries-rc101-cause,
# 2026-11-25); running the first piece alone did not change that. With the bound, in one run every
# piece passed at load 39 to 49 (most of it from outside the warm step), the longest in 12 s; in
# an earlier run with the same bound, load 20 to 36, 6 tests of 4 pieces still failed with exit
# 124, a cause not yet found. Both xargs take -r: GNU xargs runs its command once on empty input,
# so with a single linking piece the side step ran `warm` once more with no arguments, which ran
# nothing (`in_run_copy`'s `exec` with no command returns 0) and printed a line with an empty piece
# name (until 2026-11-25). Test: tools/test_run_tests.sh warm.
warm_all() {
  local list=$1 jobs=$2 cores=$3 side side_threads first
  side=$(($(wc -l <"$list") - 1))
  side_threads=$((cores / (side < jobs ? (side > 0 ? side : 1) : jobs)))
  [ "$side_threads" -ge 1 ] || side_threads=1
  head -n 1 "$list" | xargs -r --process-slot-var=slot -L 1 bash -c 'warm "$@"' _
  first=$?
  tail -n +2 "$list" |
    RUST_TEST_THREADS=$side_threads xargs -r -P "$jobs" --process-slot-var=slot -L 1 bash -c 'warm "$@"' _ &&
    [ "$first" = 0 ]
}

# features_of <cargo tree options>: each package of the selection as `<package> [<features>]`, one
# a line, sorted: the features a build of that selection gives each package. Comparing it with
# `features_of --workspace` finds a package that a build alone gives other features than the
# workspace build does (its dylib would be built twice, or overwritten).
features_of() { cargo tree "$@" -f '{p} [{f}]' --prefix none | sed 's/ (\*)$//' | sort -u; }
