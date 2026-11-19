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

# features_of <cargo tree options>: each package of the selection as `<package> [<features>]`, one
# a line, sorted: the features a build of that selection gives each package. Comparing it with
# `features_of --workspace` finds a package that a build alone gives other features than the
# workspace build does (its dylib would be built twice, or overwritten).
features_of() { cargo tree "$@" -f '{p} [{f}]' --prefix none | sed 's/ (\*)$//' | sort -u; }
