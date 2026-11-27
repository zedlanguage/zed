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

# The tests of each test binary, one per line, listed once (`--list --format terse`, 30 ms for
# l01_38's 644 tests); empty for a binary that cannot be listed. list_binary fills it, in the
# shell that calls it.
declare -A test_list
list_binary() {
  [ -n "${test_list[$1]+x}" ] ||
    test_list[$1]=$("$1" --list --format terse </dev/null 2>/dev/null | sed -n 's/: test$//p')
}
# The tests of a piece's command, one per line: the listed binary $1 run with the arguments
# after it, applied to its list as libtest applies them. A test runs when a filter is part of
# its name (with --exact, its whole name), or when there is no filter, and when no --skip is
# part of it (with --exact, the whole of it). The pieces use no other argument. Listing each
# piece instead would take 30 ms a piece, 50 s for the 1,653 pieces of 2026-11-14.
piece_tests() {
  local bin=$1
  shift
  [ -n "${test_list[$bin]}" ] || return 0
  printf '%s\n' "${test_list[$bin]}" | awk -v args="$*" '
    BEGIN {
      n = split(args, a, " ")
      for (i = 1; i <= n; i++) {
        if (a[i] == "--exact") exact = 1
        else if (a[i] == "--skip") skip[++ns] = a[++i]
        else filter[++nf] = a[i]
      }
    }
    function has(s) { return exact ? $0 == s : index($0, s) > 0 }
    {
      for (i = 1; i <= nf; i++) if (has(filter[i])) break
      if (nf && i > nf) next
      for (i = 1; i <= ns; i++) if (has(skip[i])) next
      print
    }'
}
# Splits the pieces of the table on stdin, `group step name dir binary args`, into correctness
# pieces and benchmarks, and writes each with its kind, test or bench, first. A piece none of
# whose tests has `bench::` in its path is a correctness piece as it is. Otherwise each of its
# benchmarks becomes a piece of its own, <its name before the first ::>::<test> running
# `--exact <test>`, and the rest of it, if any test is left, a correctness piece that skips them:
# by `--skip bench::`, which libtest matches anywhere in a name, or, in a piece that runs with
# --exact, where a skip must be a whole name, by a `--skip` of each. A benchmark two pieces of
# one binary hold becomes one bench piece, at the first.
#
# The work is one awk for the whole table, and one listing of each binary: the shell loop writes
# each binary's listing once, before the first piece that runs it, as a line `\001B <binary>` and
# the binary's own `--list --format terse` output, then each piece as `\001P <piece>`; the awk
# keeps each binary's tests and splits each piece as it comes. Until TOOL-split-benchmarks-forks
# (2026-11-27) each piece of a binary with benchmarks started piece_tests' awk and two to four
# greps, seds and trs, about 3.4 ms a piece: `run_tests.sh --list` took 48 s at load 61 with
# about 2,000 such pieces (nolock1, 2026-11-19). A listing line never starts with \001, so a
# marker cannot be taken for a test, and the `echo` after each listing ends a last line that has
# no newline, so the next marker starts a line of its own.
# Complexity tradeoff: a piece with --exact finds its tests by name in a hash table of its binary's
# tests, O(k log k) for its k names; any other piece scans its binary's T tests, O(T) per piece, as
# piece_tests does and as libtest itself does when it runs the piece (it applies its filters to its
# whole list), so the split costs no more than the runs it plans. A substring index would make
# the scan sublinear, but the filters are a few per piece and T is at most about 2,000, so the
# scan is below a millisecond a piece in awk, against 3.4 ms a piece of forks before.
# Test: tools/test_run_tests.sh warm (each kind of piece, one listing a binary, and as many
# processes for 301 pieces as for 6).
split_benchmarks() {
  local group step name dir bin args
  local -A listed
  while read -r group step name dir bin args; do
    if [ -z "${listed[$bin]}" ]; then
      listed[$bin]=1
      printf '\001B %s\n' "$bin"
      "$bin" --list --format terse </dev/null 2>/dev/null
      echo
    fi
    printf '\001P %s\n' "$group $step $name $dir $bin${args:+ $args}"
  done | awk '
    # The tests of each binary: tests[bin, i] for i = 1 .. count[bin], in the order listed, and
    # at[bin, name] = i.
    # The markers are compared as strings, not as a regular expression with an octal escape, which
    # not every awk reads (Colab'"'"'s default awk is mawk).
    BEGIN { MB = "\001B "; MP = "\001P " }
    substr($0, 1, 3) == MB { cur = substr($0, 4); count[cur] = 0; next }
    substr($0, 1, 3) == MP { split_piece(substr($0, 4)); next }
    /: test$/ && cur != "" {
      name = substr($0, 1, length($0) - 6)
      tests[cur, ++count[cur]] = name
      at[cur, name] = count[cur]
      next
    }
    function has(t, s) { return exact ? t == s : index(t, s) > 0 }
    function split_piece(line,    f, nf_, i, j, k, t, nfil, nskip, filter, skip, m, mt, idx, sel, bin, bench, plain, out, pre) {
      nf_ = split(line, f, " ")
      bin = f[5]
      exact = 0; nfil = 0; nskip = 0
      for (i = 6; i <= nf_; i++) {
        if (f[i] == "--exact") exact = 1
        else if (f[i] == "--skip") skip[++nskip] = f[++i]
        else filter[++nfil] = f[i]
      }
      # The tests the piece runs, in the binary'"'"'s order, as libtest selects them.
      m = 0
      if (exact && nfil) {
        for (i = 1; i <= nfil; i++)
          if ((bin, filter[i]) in at && !((bin, filter[i]) in idx)) idx[bin, filter[i]] = at[bin, filter[i]]
        k = 0
        for (t in idx) mt[++k] = idx[t]
        # Insertion sort of the k indices: k is the number of names the piece gives.
        for (i = 2; i <= k; i++) { t = mt[i]; for (j = i - 1; j >= 1 && mt[j] > t; j--) mt[j + 1] = mt[j]; mt[j + 1] = t }
        for (i = 1; i <= k; i++) {
          t = tests[bin, mt[i]]
          for (j = 1; j <= nskip; j++) if (has(t, skip[j])) break
          if (j > nskip) sel[++m] = t
        }
      } else {
        for (i = 1; i <= count[bin]; i++) {
          t = tests[bin, i]
          for (j = 1; j <= nfil; j++) if (has(t, filter[j])) break
          if (nfil && j > nfil) continue
          for (j = 1; j <= nskip; j++) if (has(t, skip[j])) break
          if (j <= nskip) continue
          sel[++m] = t
        }
      }
      bench = 0; plain = 0
      for (i = 1; i <= m; i++) if (index(sel[i], "bench::")) bench++; else plain++
      if (!bench) { print "test " line; return }
      if (plain) {
        if (exact) {
          out = "test " line
          for (i = 1; i <= m; i++) if (index(sel[i], "bench::")) out = out " --skip " sel[i]
          print out
        } else print "test " line " --skip bench::"
      }
      pre = f[3]
      if ((i = index(pre, "::"))) pre = substr(pre, 1, i - 1)
      for (i = 1; i <= m; i++) {
        t = sel[i]
        if (!index(t, "bench::") || (bin, t) in seen) continue
        seen[bin, t] = 1
        print "bench " f[1] " " f[2] " " pre "::" t " " f[4] " " bin " --exact " t
      }
    }'
}

# features_of <cargo tree options>: each package of the selection as `<package> [<features>]`, one
# a line, sorted: the features a build of that selection gives each package. Comparing it with
# `features_of --workspace` finds a package that a build alone gives other features than the
# workspace build does (its dylib would be built twice, or overwritten).
features_of() { cargo tree "$@" -f '{p} [{f}]' --prefix none | sed 's/ (\*)$//' | sort -u; }
