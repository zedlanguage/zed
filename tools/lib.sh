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

# features_of <cargo tree options>: each package of the selection as `<package> [<features>]`, one
# a line, sorted: the features a build of that selection gives each package. Comparing it with
# `features_of --workspace` finds a package that a build alone gives other features than the
# workspace build does (its dylib would be built twice, or overwritten).
features_of() { cargo tree "$@" -f '{p} [{f}]' --prefix none | sed 's/ (\*)$//' | sort -u; }
