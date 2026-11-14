#!/bin/bash
# Runs the tests in pieces, one test binary, step folder, module or slow test each, each under a
# limit of 20 s (more under load, below), and prints a line per piece as it ends. Usage, from a
# checkout's root:
#   tools/run_tests.sh [--full] [--bench] [--each-test] [--only <ERE>] [--doc] [--list] [--reuse-table] [--logs <dir>] [jobs]
#   tools/run_tests.sh --short-clone-remove
# A run is of the correctness tests or, with --bench, of the benchmarks alone (TEST-bench-split,
# author P169). A benchmark is a test whose path holds `bench::`: it lies in a module `bench`,
# a file of its own (tests/steps/<step>/bench.rs, or src/.../bench.rs in a crate), and measures
# work at two sizes (zed_tests::scaling). The default run leaves out every piece whose tests are
# all benchmarks and gives a piece that holds some of them `--skip bench::` (with --exact, a
# `--skip` of each by name). --bench runs each benchmark as a piece of its own, named
# <group>::<test>, with the same slots, slice, limit and summary lines; --only selects among them
# as among the correctness pieces. A benchmark runs with --nocapture, since libtest keeps the
# output of a passing test, and its lines that begin `bench ` (zed_tests::scaling) are written to
# <log dir>/bench.log and printed after the summary (TEST-time-pass-condition). --each-test runs
# each selected correctness test as a piece of its own, `--exact <test>` in one process
# (tools/time_tests.sh times the tests this way).
# Without --full this is the local suite, which needs only the Rust toolchain and runs in CI.
# --full adds tests/full/, the battery that needs emulators, containers, databases and other
# outside tools. It stops before any test if a tool is missing; nothing is skipped.
# --only runs only the pieces whose name, or whose group (the step folder, or the test binary's
# name without its hash, e.g. zedc, deep_heap, short-l01_37_oracle), matches the extended regular
# expression; a piece of a binary split per test also matches as <group>::<test>. A test binary
# whose source lies in a step folder under another name (deep_types in l01_22_type_representation)
# has that folder as a second group, so a selection of the step runs it too. A pattern that
# matches no piece stops the run with an error. The short-addresses build is made only when a
# short- piece is selected, in a clone of build/cargo kept in build/short-clone from run to run;
# such a run must go through /home/luke/Work/wt/zrun, and --short-clone-remove deletes the clone
# (through zrun too) and runs nothing. --doc adds the check that the documentation of the whole
# workspace builds, which is off by default; --no-doc is accepted and changes nothing. Every run
# but --list checks the documentation of each package whose `///` or `//!` lines the checkout
# changes since origin/main (tools/check_changed_docs.sh). --list builds what the selection
# needs, prints the names of the selected pieces and runs nothing.
# A run without --only saves the table of all pieces in its log directory; --list --reuse-table
# selects from that table without building or listing the binaries, for tests of the selection.
# The table is as the run that wrote it left it: with --full or not, and stale once the test
# binaries are rebuilt. --logs puts the logs, the table and the piece list in <dir> instead of
# build/test-logs. Two runs in one checkout need different directories: a second run on a
# directory in use stops at once and names the run using it.
# Without --only the build is `cargo test --workspace --no-run`, which does nothing on a tree
# already built that way, so a run after such a build starts the pieces at once. With --only it
# builds only the test binaries of the groups the pattern names, and the libraries under them,
# and runs only binaries this build reported, never one left from an earlier build (author,
# 2026-11-10: rebuild only the test binaries being worked on, whatever an upstream change
# touched). The binaries are chosen before the build, from their groups' names alone, so a test
# or a module is selected only with its binary's group, as <group>::<path>: a part of the pattern
# (an alternative at its top level) that selects no binary stops the run with an error naming it.
# A failed piece keeps its output in build/test-logs/<piece>.log, or in the --logs directory.
# Every piece runs in the systemd slice zedtests.slice, whose 112 GB limit holds across all
# checkouts together. A piece's limit is max(20, 20 × load / cores) s: a load above the number of
# cores raises the limit of the pieces that start under it in proportion. It was 60 s until
# TEST-bench-split (author P169), which puts the measurements at two sizes in benchmarks, run
# apart with --bench, and asks each correctness test to take well under 1 s alone.
args=$*
features= full_suite= only= list= reuse= logs= doc= jobs=6 clone_remove= run_kind=test each_test=
while [ $# -gt 0 ]; do
  case $1 in
    --full) full_suite=1 ;;
    --bench) run_kind=bench ;;
    --each-test) each_test=1 ;;
    --only)
      if [ $# -lt 2 ] || [ -z "$2" ]; then
        echo "--only needs a non-empty extended regular expression"
        exit 2
      fi
      only=$2
      shift
      ;;
    --doc) doc=1 ;;
    --no-doc) ;;
    --list) list=1 doc= ;;
    --reuse-table) reuse=1 ;;
    --short-clone-remove) clone_remove=1 ;;
    --logs)
      if [ $# -lt 2 ] || [ -z "$2" ]; then
        echo "--logs needs a directory"
        exit 2
      fi
      logs=$2
      shift
      ;;
    [1-9]*) jobs=$1 ;;
    *)
      echo "unknown argument: $1 (usage: tools/run_tests.sh [--full] [--bench] [--each-test] [--only <ERE>] [--doc] [--list] [--reuse-table] [--logs <dir>] [--short-clone-remove] [jobs])"
      exit 2
      ;;
  esac
  shift
done
if [ -n "$reuse" ] && [ -z "$list" ]; then
  echo "--reuse-table needs --list"
  exit 2
fi
if [ -n "$only" ]; then
  { [[ x =~ $only ]]; } 2>/dev/null
  if [ $? = 2 ]; then
    echo "--only: not a valid extended regular expression: $only"
    exit 2
  fi
fi
# Whether the piece $2 of group $1 is selected: always without --only.
selected() {
  [ -z "$only" ] || [[ $2 =~ $only || $1 =~ $only ]] || { [[ $2 != "$1"* ]] && [[ $1::$2 =~ $only ]]; }
}
if [ -n "$full_suite" ]; then
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
root=$(pwd)
# The short-addresses build (step L1.37a) keeps 8 bits of every content address and type digest,
# so distinct values collide; its pieces check that every place that compares by address
# confirms equal addresses by contents, and that verdicts and outputs match the full build.
# It builds in a clone of the checkout's build: an overlay mounted at build/short-clone/cargo
# whose one lower layer is build/cargo, read-only, and whose upper layer build/short-clone/upper
# receives what the feature rebuilds (zed-kernel and every crate above it, 16 crates; the 92
# crates from crates.io are reused). Mounting it takes 11 ms; a copy of build/cargo would be
# 94 GB, or 3 GB without the incremental caches, which the feature's crates cannot use. The
# target directory's path changes nothing cargo reuses: the whole workspace built in such a
# clone compiled nothing. The upper layer is kept from run to run, so a run after a change
# rebuilds only what the change touches; the clone is mounted for the run and unmounted when it
# ends, by failure or interrupt too, and is deleted with the checkout, or by
# `tools/run_tests.sh --short-clone-remove` in a checkout that is kept (author, 2026-11-10:
# "delete your clone when you're done"). Measurements (BUILD-short-clone, -j 4) are in its
# STATUS row: before, a target of its own, build/short, took 1.5 GB per checkout, 227 s cold and
# 11 s after a one-line change to zedc; a clone deleted at the end of every run took 180 to
# 237 s on every run.
# The feature's crates are dylibs with no hash in their file names (debug/deps/libzedc.so and
# the like), and their fingerprint directories have the same names in both builds, so the
# clone's copies take the paths of the main build's files, in the upper layer only; a short test binary loads its own copies, the first rpath being $ORIGIN (zrun). Cargo
# sees a change made since the clone's last build by comparing the times of the sources with
# those of the clone's own fingerprints, as in any target directory. That fails only when a
# source gets an older time than the build of it, which seed-build.sh --restack does on purpose
# (it dates every file equal to the central build's commit to 2000): the clone could then call
# fresh a crate built from other contents. So the clone records the build it was made from,
# build/STACK and the inode and birth time of build/upper (a restack makes a new build/upper),
# in build/short-clone/stamp, and a run that finds another one deletes the clone and makes it
# again.
# The clone is mounted in the zrun namespace, so the run must go through zrun, and build/cargo
# must not change while it is mounted (no other zcargo build of this checkout at that time).
# A run killed with SIGKILL leaves it mounted, and the next run unmounts it first. Two runs in
# one checkout take build/short-clone.lock in turn, the second waiting until the first has
# ended; checkouts do not share a clone, as each zrun namespace mounts its own checkout at the
# fixed path.
# The build the clone is made from: build/STACK and build/upper, or build/cargo in a checkout
# without a STACK.
short_clone_stamp() {
  if [ -e "$root/build/STACK" ]; then
    cat "$root/build/STACK"
    stat -c 'upper %i %W' "$root/build/upper"
  else
    stat -c 'cargo %i %W' "$root/build/cargo"
  fi
}
# Unmounts the clone, if it is mounted. The kernel leaves the overlay's inner work directory at
# mode 000, which rm cannot enter; it is opened again, so that deleting the checkout succeeds.
unmount_short_clone() {
  [ -e /home/luke/Work/wt/.build-root/build/short-clone ] || return 0
  for _ in 1 2 3 4 5 6 7 8 9 10; do
    mountpoint -q /home/luke/Work/wt/.build-root/build/short-clone/cargo || break
    umount /home/luke/Work/wt/.build-root/build/short-clone/cargo 2>/dev/null || sleep 1
  done
  if findmnt -rn -o TARGET | grep -qE '^/home/luke/Work/wt/\.build-root/build/short-clone(/|$)'; then
    echo "The short-addresses clone /home/luke/Work/wt/.build-root/build/short-clone/cargo is" \
      "still mounted (in use by a process of this checkout)."
    return 1
  fi
  [ -L /home/luke/Work/wt/.build-root/build/short-clone/work/work ] ||
    [ ! -d /home/luke/Work/wt/.build-root/build/short-clone/work/work ] ||
    chmod u+rwx /home/luke/Work/wt/.build-root/build/short-clone/work/work
}
# Unmounts and deletes the clone, if there is one. Every path is written out: a delete names its
# target in full (the author's rule), and the clone exists only at the fixed path of zrun.
drop_short_clone() {
  [ -e /home/luke/Work/wt/.build-root/build/short-clone ] || return 0
  unmount_short_clone || return 1
  if [ -L /home/luke/Work/wt/.build-root/build/short-clone ] ||
    [ ! -d /home/luke/Work/wt/.build-root/build/short-clone ] ||
    [ "$(realpath -e /home/luke/Work/wt/.build-root/build/short-clone)" != \
      /home/luke/Work/wt/.build-root/build/short-clone ]; then
    echo "The short-addresses clone /home/luke/Work/wt/.build-root/build/short-clone is not a" \
      "directory; it is left in place."
    return 1
  fi
  rm -rf --one-file-system --preserve-root=all /home/luke/Work/wt/.build-root/build/short-clone
}
if [ -n "$clone_remove" ]; then
  if [ "$root" != /home/luke/Work/wt/.build-root ]; then
    echo "The short-addresses clone is mounted in the zrun namespace; run" \
      "/home/luke/Work/wt/zrun tools/run_tests.sh --short-clone-remove from the checkout's root."
    exit 1
  fi
  exec 6>>"$root/build/short-clone.lock"
  if ! flock -n 6; then
    echo "Waiting for the other run of this checkout that uses the short-addresses clone to end."
    flock 6
  fi
  if [ ! -e /home/luke/Work/wt/.build-root/build/short-clone ]; then
    echo "This checkout has no short-addresses clone."
    exit 0
  fi
  drop_short_clone || exit 1
  echo "The short-addresses clone of this checkout is deleted."
  exit 0
fi
out=${logs:-build/test-logs}
[[ $out == /* ]] || out=$root/$out
mkdir -p "$out"
# One run at a time uses a log directory: two runs sharing its piece list and summary report
# pieces of the other run and false failures (rc=127, or a failed count above the failed lines).
# A second run stops at once and names the first. The kernel drops the lock when the run and
# every piece it started have ended, so a killed run leaves none behind. The run holding the lock
# writes its details to run.holder while it holds a short lock on that file, which every run
# takes before trying the lock, so a stopped run reads the details of the run that stopped it.
exec 7>>"$out/run.holder" 8>>"$out/run.lock"
flock 7
if ! flock -n 8; then
  echo "Another tools/run_tests.sh run is using $out: $(cat "$out/run.holder")."
  echo "Wait for it to end, or give this run a directory of its own with --logs <dir>."
  exit 1
fi
echo "process $$, started $(date '+%F %T'), arguments: ${args:-none}" >"$out/run.holder"
exec 7>&-
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
# --exact, where a skip must be a whole name, by a `--skip` of each.
split_benchmarks() {
  local group step name dir bin args tests t skips
  local -A seen
  while read -r group step name dir bin args; do
    list_binary "$bin"
    tests=
    [[ ${test_list[$bin]} != *bench::* ]] || tests=$(piece_tests "$bin" $args)
    if [[ $tests != *bench::* ]]; then
      echo "test $group $step $name $dir $bin${args:+ $args}"
      continue
    fi
    if printf '%s\n' "$tests" | grep -qv 'bench::'; then
      if [[ " $args " == *" --exact "* ]]; then
        skips=$(printf '%s\n' "$tests" | grep 'bench::' | sed 's/^/ --skip /' | tr -d '\n')
        echo "test $group $step $name $dir $bin${args:+ $args}$skips"
      else
        echo "test $group $step $name $dir $bin${args:+ $args} --skip bench::"
      fi
    fi
    for t in $(printf '%s\n' "$tests" | grep 'bench::'); do
      [ -z "${seen[$bin $t]}" ] || continue
      seen[$bin $t]=1
      echo "bench $group $step ${name%%::*}::$t $dir $bin --exact $t"
    done
  done
}
# Writes the pieces of the table $1 of the kind the run is of that --only selects to
# $out/pieces, one per line: its name, directory and command. A line of the table is a piece's
# kind, group and step folder, then those. With --each-test, each selected piece of the run's kind
# becomes a piece per test it runs, <its name before the first ::>::<test> running
# `--exact <test>`.
select_pieces() {
  local k group step name dir bin args first t
  read -r first _ <"$1"
  if [ "$first" != test ] && [ "$first" != bench ]; then
    echo "$1 is a table of pieces of an older tools/run_tests.sh, without the kind of each"
    echo "piece; run tools/run_tests.sh --list without --only to write it again."
    exit 1
  fi
  while read -r k group step name dir bin args; do
    [ "$k" = "$run_kind" ] || continue
    [ "$k" = test ] || args="${args:+$args }--nocapture"
    { selected "$group" "$name" || selected "$step" "$name"; } || continue
    if [ -z "$each_test" ]; then
      echo "$name $dir $bin${args:+ $args}"
      continue
    fi
    list_binary "$bin"
    for t in $(piece_tests "$bin" $args); do
      echo "${name%%::*}::$t $dir $bin --exact $t"
    done
  done <"$1" >"$out/pieces"
  if [ ! -s "$out/pieces" ]; then
    local among=
    [ "$run_kind" = test ] || among=" among the benchmarks"
    if [ -n "$only" ]; then
      echo "NO PIECE MATCHES --only '$only'$among${each_test:+ (or the pieces it selects run no test)}"
    else
      echo "NO PIECE TO RUN$among"
    fi
    exit 1
  fi
}
if [ -n "$reuse" ]; then
  if [ ! -s "$out/table" ]; then
    echo "--reuse-table: no $out/table; run tools/run_tests.sh --list without --only first"
    exit 1
  fi
  select_pieces "$out/table"
  cut -d ' ' -f 1 "$out/pieces"
  exit 0
fi
# A run without --only writes the table of every piece; a run with it, a table of its own.
table=$out/table
[ -z "$only" ] || table=$out/listing
# The step folder of each test binary of tests/Cargo.toml whose source lies in a step folder of
# another name: deep_types, deep_search, deep_heap, deep_values and deep_scaling.
declare -A step_of
while read -r b s; do
  step_of[$b]=$s
done < <(awk '
  /^\[\[test\]\]/ { name = "" }
  /^name = "/ { name = $3; gsub(/"/, "", name) }
  /^path = "steps\// && name != "" { split($3, p, "/"); if (p[2] != name) print name, p[2] }
' tests/Cargo.toml)
# The alternatives at the top level of the extended regular expression $1, one per line: it is
# split at each | outside parentheses, bracket expressions and escapes.
alternatives() {
  local re=$1 n=${#1} i=0 j depth=0 cur= c rest close
  while [ "$i" -lt "$n" ]; do
    c=${re:i:1}
    case $c in
      \\) cur+=${re:i:2} i=$((i + 2)) && continue ;;
      \[)
        # A ] first in a bracket expression, after an optional ^, is a member, and [:class:],
        # [.symbol.] and [=class=] hold a ] of their own.
        j=$((i + 1))
        [ "${re:j:1}" != ^ ] || j=$((j + 1))
        [ "${re:j:1}" != ] ] || j=$((j + 1))
        while [ "$j" -lt "$n" ] && [ "${re:j:1}" != ] ]; do
          case ${re:j:2} in
            '[:' | '[.' | '[=')
              close=${re:j+1:1}]
              rest=${re:j+2}
              rest=${rest%%"$close"*}
              j=$((j + 3 + ${#rest}))
              ;;
          esac
          j=$((j + 1))
        done
        cur+=${re:i:j-i+1} i=$((j + 1))
        continue
        ;;
      \() depth=$((depth + 1)) ;;
      \)) depth=$((depth - 1)) ;;
      \|)
        if [ "$depth" = 0 ]; then
          echo "$cur"
          cur= i=$((i + 1))
          continue
        fi
        ;;
    esac
    cur+=$c i=$((i + 1))
  done
  echo "$cur"
}
# Whether the alternative $1 of --only selects a piece of the test binary of group $2 in step
# folder $3. A piece's name is its group or <group>::<path>, and it matches as <group>::<name> or
# <step>::<name> too (selected above), so an alternative selects one of the binary's pieces when it
# matches the group or the step, or when the text before its first :: matches either at its end.
# The second can hold for a binary none of whose pieces it selects; that binary is built and its
# pieces listed for nothing, which costs time but drops no test.
wants() {
  [[ $2 =~ $1 || $3 =~ $1 ]] && return 0
  [[ $1 == *::* ]] || return 1
  local end="${1%%::*}$"
  [[ $2 =~ $end || $3 =~ $end ]]
}
# Without --only every test binary is built. With it, only the binaries of the groups it selects
# are built, and the libraries under them (author, 2026-11-10: rebuild only the test binaries
# being worked on, whatever an upstream change touched), from the targets of the workspace's
# packages: a step folder's binary or another test of a package with --test, a command's unit
# tests with --bin, and a library's unit tests with -p <package> --lib. The groups are the names
# cargo gives the binaries, the target's name with each - made _. The short-addresses build and
# tests/full are selected below, by their pieces' names, as before; short_steps names the steps of
# the short-addresses build.
short_steps="l01_37a_short_addresses l01_37_oracle"
# The short-addresses pieces build in a clone mounted in the zrun namespace (see below), so a
# run that selects one stops here, before any build, when it does not run through zrun.
short_build=
for s in $short_steps; do
  selected "short-$s" "short-$s" && short_build=1
done
if [ -n "$short_build" ] && [ "$root" != /home/luke/Work/wt/.build-root ]; then
  echo "The short-addresses pieces build in a clone mounted in the zrun namespace; run" \
    "/home/luke/Work/wt/zrun tools/run_tests.sh from the checkout's root."
  exit 1
fi
if [ -z "$only" ]; then
  if ! cargo test --workspace $features --no-run --message-format=short >"$out/build.log" 2>&1; then
    tail -40 "$out/build.log"
    echo "BUILD FAILED"
    exit 1
  fi
else
  mapfile -t alts < <(alternatives "$only")
  for a in "${alts[@]}"; do
    { [[ x =~ ${a%%::*} ]]; } 2>/dev/null
    if [ $? = 2 ]; then
      echo "--only: cannot tell which test binaries '$a' names: the text before its first ::,"
      echo "'${a%%::*}', is not an extended regular expression by itself. Write each binary's"
      echo "pieces as an alternative of its own at the top level, <group>::<path>|<group>::<path>."
      exit 2
    fi
  done
  # The targets of the workspace's packages, from the package name and each target's first kind
  # and name in cargo's metadata, which lists them in this order.
  targets=$(cargo metadata --no-deps --format-version 1 |
    grep -oE '"name":"[^"]*","version":"[^"]*","id"|"kind":\[[^]]*\],"crate_types":\[[^]]*\],"name":"[^"]*"' |
    awk -F '"' '/"version"/ { package = $4; next } { print package, $4, $(NF - 1) }')
  if [ -z "$targets" ]; then
    echo "--only: cargo metadata listed no target of the workspace"
    exit 1
  fi
  tests= libs= unused=
  for a in "${alts[@]}"; do
    any=
    while read -r package kind name; do
      g=${name//-/_}
      case $kind in
        custom-build | example | bench) continue ;;
        test) [ "$g" != full ] || [ -n "$full_suite" ] || continue ;;
      esac
      wants "$a" "$g" "${step_of[$g]:-$g}" || continue
      any=1
      case $kind in
        test)
          # tests/full is one binary, its pieces the folders of tests/full.
          [ "$g" != full ] && tests+="--test $name"$'\n'
          ;;
        bin) tests+="--bin $name"$'\n' ;;
        *) libs+="-p $package"$'\n' ;;
      esac
    done <<<"$targets"
    if [ -n "$full_suite" ]; then
      for d in tests/full/*/; do
        d=$(basename "$d")
        wants "$a" "$d" "$d" && any=1 && tests+="--test full"$'\n'
      done
    fi
    for s in $short_steps; do
      wants "$a" "short-$s" "short-$s" && any=1
    done
    [ -n "$any" ] || unused+=" '$a'"
  done
  # A test or a module is selected only with the group of its binary, since the binaries are
  # chosen from their groups before they are built; a part that selects none stops the run.
  hint="A test or a module is selected only with its binary's group, as <group>::<path>."
  if [ "$unused" = "$(printf " '%s'" "${alts[@]}")" ]; then
    echo "NO PIECE MATCHES --only '$only'"
    echo "$hint"
    exit 1
  fi
  if [ -n "$unused" ]; then
    echo "--only: no test binary is selected by the part$unused of '$only'."
    echo "$hint"
    exit 1
  fi
  tests=$(printf %s "$tests" | sort -u | tr '\n' ' ')
  libs=$(printf %s "$libs" | sort -u | tr '\n' ' ')
  : >"$out/build.log"
  if [ -n "$tests" ] &&
    ! cargo test --workspace $features --no-run --message-format=short $tests >>"$out/build.log" 2>&1; then
    tail -40 "$out/build.log"
    echo "BUILD FAILED"
    exit 1
  fi
  if [ -n "$libs" ]; then
    # Cargo gives a package the features that the packages named on its command line ask for,
    # and the compiler crates are dylibs, whose file names do not change with their features: a
    # build of a package's unit tests with other features than the workspace build overwrites
    # the library every test binary loads, and the next build rebuilds it. The packages ask for
    # the workspace's features (dev-dependencies in crates/zed-native, crates/zed-tools and
    # tests); this stops the build when one does not, before anything is overwritten.
    features_of() { cargo tree "$@" -f '{p} [{f}]' --prefix none | sed 's/ (\*)$//' | sort -u; }
    differ=$(comm -23 <(features_of $libs) <(features_of --workspace))
    if [ -n "$differ" ]; then
      echo "--only: cargo test --no-run $libs--lib would build these packages with features"
      echo "the workspace build does not give them, and overwrite their libraries:"
      echo "$differ"
      echo "Give the package the features of the workspace build, as a dev-dependency."
      exit 1
    fi
    if ! cargo test --no-run --message-format=short $libs --lib >>"$out/build.log" 2>&1; then
      tail -40 "$out/build.log"
      echo "BUILD FAILED"
      exit 1
    fi
  fi
fi
# Cargo prints a binary path relative to the checkout only when the target directory is inside it.
bins=$(sed -n -e "s|^ *Executable .*(\(/.*\))$|\1|p" -e "s|^ *Executable .*(\([^/].*\))$|$root/\1|p" "$out/build.log")
full=$(echo "$bins" | grep '/full-')
short=
if [ -n "$short_build" ]; then
  exec 6>>"$root/build/short-clone.lock"
  if ! flock -n 6; then
    echo "Waiting for the other run of this checkout that uses the short-addresses clone to end."
    flock 6
  fi
  unmount_short_clone || exit 1
  stamp=$(short_clone_stamp)
  if [ -e /home/luke/Work/wt/.build-root/build/short-clone ] &&
    [ "$(cat "$root/build/short-clone/stamp" 2>/dev/null)" != "$stamp" ]; then
    echo "The short-addresses clone was made from another build of this checkout; it is made again."
    drop_short_clone || exit 1
  fi
  trap unmount_short_clone EXIT
  trap 'exit 129' HUP
  trap 'exit 130' INT
  trap 'exit 143' TERM
  mkdir -p "$root/build/short-clone/upper" "$root/build/short-clone/work" "$root/build/short-clone/cargo"
  [ -e "$root/build/short-clone/stamp" ] || printf '%s\n' "$stamp" >"$root/build/short-clone/stamp"
  if ! mount -t overlay overlay -o "lowerdir=$root/build/cargo,upperdir=$root/build/short-clone/upper,workdir=$root/build/short-clone/work,userxattr" \
    "$root/build/short-clone/cargo"; then
    echo "The short-addresses clone of build/cargo could not be mounted."
    exit 1
  fi
  if ! CARGO_TARGET_DIR=$root/build/short-clone/cargo cargo test -p zed-tests --features short-addresses \
    $(printf -- '--test %s ' $short_steps) --no-run --message-format=short >"$out/build-short.log" 2>&1; then
    tail -40 "$out/build-short.log"
    echo "BUILD FAILED (short-addresses)"
    exit 1
  fi
  short=$(sed -n -e "s|^ *Executable .*(\(/.*\))$|\1|p" -e "s|^ *Executable .*(\([^/].*\))$|$root/\1|p" \
    "$out/build-short.log")
fi
# Each step folder is a test binary of its own, named after the folder (tests/Cargo.toml), and a
# test's name in it is its module path within the folder. A step folder or module named here
# gets a piece for each of its modules and each of its own tests instead of one piece; the rest
# get one piece each. The cases below are history, written under the old limit of 60 s; the limit
# is 20 s since TEST-bench-split (author P169). Named because together they ran past
# 60 s at load 100 (l01_25 138 s, l01_38 94 s, l01_36 89 s, l01_16 72 s, l01_08 64 s; l01_23
# 29 to 35 s at load 53, with tests of 36, 32 and 15 s); the modules are those with a test over
# 10 s there, so each of those tests has a process of its own. l01_38 names ran past 60 s at
# load 80 once the orbit tests (11 to 15 s each) joined it, and live3 at load 76 to 95, where
# `slabs_of_million_coefficients_scale` takes 38 s alone (2026-11-05).
# l01_38 shared and stages were added in UTVPI-union verify, where they took 49 and 36 s whole
# at load 77 with the other modules running. l01_39a scaling took 59 s alone at load 62, its
# 29 tests together; the whole step 38 to 47 s at load 23 to 38 (2026-11-07, PA-let-check).
# l01_39 took 49.5 s whole at load 14 once its check of every arm on concrete inputs (25.7 s
# alone) joined its random module (2026-11-07, PA-walk-multi).
# l01_26 ran past 60 s whole at load 24 once deep_ops joined it, its operations on types
# 100,000 deep taking up to 15 s each (2026-11-09, T2-ty). Two of them took 73 s and over 80 s
# alone at load 42 and now run 20,000 deep on a fifth of the stack (2026-11-12, TESTS-l01_29-split).
# l25_08 ran past 60 s whole at load 14 once bare literals made its chain of additions generic;
# its generic chain takes 35 s alone and the int chain 11 s (2026-11-09, LIT-bare).
# l01_39 pendants took 57 s whole at load 20 and ran past 60 s at load 25 once its tests of
# rewritten parts joined it (2026-11-09, PROJECT-canon-gcd).
# l01_39 lazy took 44 to 47 s whole once its check of leaves settled together (20 s alone at
# load 30) joined it; its seed loops of stars and of satellites took 38 and 42 s alone. Each
# loop is a module of parts over its seeds, and each part is a piece (2026-11-09,
# TEST-lazy-split).
# l01_39 if_shortcut holds four random parts of about 14 s each at load 35, which together
# would pass 60 s (2026-11-09, PA-if-shortcut-diff).
# l01_38 one_scope took 28.8 to 43.8 s whole under load, and 52.5 s at load 32; its 58 tests take
# 168 s one by one, the slowest 15 to 37 s alone at load 28 to 46 (2026-11-10, SPLIT-one-scope).
# l01_39 refused took 56 s whole on main and once ran past its limit of 83 s at load 44 to 64;
# its test of many refused tests, 26 to 27 s alone at load 28 to 36, is now three tests, the
# slowest the join check at 20 to 26 s at load 24 to 34 (2026-11-10, SPLIT-reduced-refused).
# l01_39 lazy's joins that drop a star hold three random parts of 13 to 22 s each at load 35
# to 45, which together with the rest of lazy would pass 60 s (2026-11-10,
# SETTLE-class-check-case).
# l01_39 deep_let took 36.8 s whole at load 24 to 35, and 43 s at load 31, nearly all of it in
# `the_arms_of_a_deep_block_scale`; each of its tests is a piece. The parts of lazy's join test
# took 50 to 73 s each alone at load 31 to 58; it has ten parts of 20 seeds, each a piece
# (2026-11-10, SPLIT-l01_39-slow).
# l01_39 linked took 55.4 s whole at load 27 in a full run and 20 to 22 s at load 23 to 28 alone,
# with the same instructions before and after batch 112: its tests take 91 s one by one, the two
# random hole tests 20 and 22 s of it; each is now three parts of 50 trees. exact's test of
# constraints reduced one at a time took 32 s at load 39 and 10.6 to 12.1 s alone at load 24;
# it is now two parts of two names each. Each test of both is a piece
# (2026-11-10, SPLIT-l01_39-rest).
# l01_36_cranelift mul_edges took 32.8 s whole at load 25: its differential of 100,000 integer
# pairs takes 26 to 27 s alone and that of 100,000 float pairs 14 to 16 s at load 22 to 26; each
# test is a piece (2026-11-11, TESTS-L1.36-mul-edges-and-differential). Since TEST-bench-move-l0136
# each draws 4,000 pairs from a new printed seed and takes under 1 s.
# l01_39 families holds four audit parts of 7 to 8 s each, the hop families of 13 s and a
# scaling test of 6 s at load 22 to 24, about 70 s together; each test is a piece
# (2026-11-11, TESTS-lhx-families).
# l01_23 r6_reduction, one test of 384 formulas, took 38 to 77 s alone at load 27 to 41 and ran
# past its limit of 90 s in a full run at load 48; it is four tests of 96 formulas, each a piece
# (2026-11-11, REFUSAL-front-xr after batch merge 128).
# l01_28_staging took 46 to 65 s whole at load 41 and more, 28 s of it the test of four shapes
# 100,000 deep on a small stack and 20 s the test of lets of built values (alone, load 41); those
# are now four tests and two. Each module is a piece, and each test of scaling and dag
# (2026-11-12, TESTS-split-l01_28-staging).
# m0_12_refusal_census reads 120 units of programs.txt, 45 s together at load 41 and 18 s of it
# one unit; each of its tests is a piece (2026-11-12, REFUSAL-census-now).
# l01_29_diagnostics took 38 to 57 s whole at load 46 and more; its modules casts and
# offered_repairs 37 and 32 s each, beside the rest at load 43 to 46. Each module is a piece,
# and each test of casts and offered_repairs; the tests of repairs inside a sum and inside a call
# (59 to 61 s each beside the other pieces at load 52) are each four parts, each a piece, and
# the two tests of a menu's cost in a larger program (36 s each alone at load 46) check programs
# half as large (2026-11-12, TESTS-l01_29-split).
# l01_26a_generic_literals took 42 s whole at load 50; each module (one per test file, so a new
# file is a piece of its own) and each test of mod.rs is a piece. The slowest pieces are scaling
# and lit_branch_ops, 24 to 50 s and 26 to 45 s at load 35 to 51. libtest runs a module's tests on
# parallel threads, so each takes about as long as its slowest test: scaling's test of many calls
# given divisions took 29 to 39 s alone at load 40 to 48. A piece per test of the two modules
# was no faster: in alternate runs at load 39 to 49 the module pieces took 24 and 28 s, the
# piece per test 34 and 32 s at most (2026-11-13, TESTS-l01_26a-split).
split="
  l01_08_parser l01_16_elaboration l01_16_elaboration::scaling
  l01_23_subtyping l01_23_subtyping::scaling l01_23_subtyping::r6_reduction
  l01_25_preimage_catalog l01_25_preimage_catalog::s22
  l01_25_preimage_catalog::exact_oracle
  l01_26_type_resolution l01_26_type_resolution::deep_ops l01_26_type_resolution::op_table
  l01_26a_generic_literals
  l01_28_staging l01_28_staging::scaling l01_28_staging::dag
  l01_29_diagnostics l01_29_diagnostics::casts l01_29_diagnostics::offered_repairs
  l01_29_diagnostics::offered_repairs::every_offered_repair_inside_a_sum_checks_as_written
  l01_29_diagnostics::offered_repairs::every_offered_repair_inside_a_call_checks_as_written
  l01_36_cranelift l01_36_cranelift::scaling l01_36_cranelift::table
  l01_36_cranelift::mul_edges
  l01_38_presburger l01_38_presburger::oracle l01_38_presburger::omega
  l01_38_presburger::scaling l01_38_presburger::deep
  l01_38_presburger::names l01_38_presburger::live3
  l01_38_presburger::shared l01_38_presburger::stages
  l01_38_presburger::one_scope
  l01_39_reduced_product l01_39_reduced_product::random
  l01_39_reduced_product::pendants l01_39_reduced_product::lazy
  l01_39_reduced_product::lazy::a_lazy_scope_settles_each_name_to_the_eager_product
  l01_39_reduced_product::lazy::a_lazy_scope_with_stars_of_two_hubs_settles_each_name_to_the_eager_product
  l01_39_reduced_product::lazy::a_lazy_scope_with_satellites_of_two_hubs_settles_each_name_to_the_eager_product
  l01_39_reduced_product::lazy::leaves_of_one_class_settled_together_get_what_each_gets_alone
  l01_39_reduced_product::lazy::a_join_settles_a_star_it_drops_or_whose_core_gains_a_disjunction
  l01_39_reduced_product::lazy::a_join_settles_the_leaves_whose_core_differs_as_settling_every_name_does
  l01_39_reduced_product::deep_let
  l01_39_reduced_product::if_shortcut
  l01_39_reduced_product::refused
  l01_39_reduced_product::linked
  l01_39_reduced_product::linked::holes_in_a_tree_of_differences_give_the_projection_from_scratch
  l01_39_reduced_product::linked::holes_piled_in_many_names_of_a_tree_give_the_projection_from_scratch
  l01_39_reduced_product::exact
  l01_39_reduced_product::exact::constraints_reduced_one_at_a_time_decide_as_all_at_once
  l01_39_reduced_product::families
  l01_39a_bit_words l01_39a_bit_words::scaling
  l25_08_mutate l25_08_mutate::scaling
  m0_12_refusal_census
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
    g=${n%-*}
    if [ -d "tests/steps/$g" ]; then
      step_pieces "${n%-*}" "$p"
    else
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
        # A crate zedc-* split from zedc; zedc_binary is a test of zed-native, run from tests.
        zedc_*-*)
          c=crates/${n%-*}
          c=${c//_/-}
          if [ -d "$c" ]; then echo "$n $c $p"; else echo "$n tests $p"; fi
          ;;
        zed_kernel-*) echo "$n crates/zed-kernel $p" ;;
        zed_native-*) echo "$n crates/zed-native $p" ;;
        zed_rt-*) echo "$n crates/zed-rt $p" ;;
        zed_cert-*) echo "$n crates/zed-cert $p" ;;
        *) echo "$n tests $p" ;;
      esac
    fi | sed "s|^|$g ${step_of[$g]:-$g} |"
  done
  for p in $short; do
    n=short-$(basename "${p%-*}")
    echo "$n $n $n tests $p"
  done
  if [ -n "$full" ]; then
    for d in tests/full/*/; do
      n=$(basename "$d")
      echo "$n $n $n tests $full $n::"
    done
  fi
} | split_benchmarks >"$table"
select_pieces "$table"
if [ -n "$list" ]; then
  cut -d ' ' -f 1 "$out/pieces"
  exit 0
fi
# With --doc only: the documentation of every crate, private items included, builds with no
# warning, so a link in a doc comment that names no item, or a citation written as a link, fails
# the run. It is off by default so that a run neither spends the time on it nor leaves the
# generated pages in build/cargo/doc; use --doc after any change to a doc comment (/// or //!).
if [ -n "$doc" ] &&
  ! RUSTDOCFLAGS='-D warnings' cargo doc --no-deps --document-private-items >"$out/doc.log" 2>&1; then
  tail -40 "$out/doc.log"
  echo "DOC FAILED"
  exit 1
fi
# On every run, with --doc or not: the documentation of each package whose doc comments this
# checkout changes since origin/main, alone and with the workspace's features. Agents run this
# script before they merge, and seldom passed --doc, so links that broke the doc build reached main
# three times (DOC-private-links, -2, -3); with no doc comment changed it builds nothing.
tools/check_changed_docs.sh "$out/doc-changed.log" || exit 1
# At most `slots` pieces run at once on this machine, whichever checkout started them. A piece holds
# a lock on one file of $slot_dir until it ends, so a killed run frees its slots, and its limit starts
# when it has one. Four suites at once took 2:13 with 8 slots and 2:05 without, and the longest
# piece 28 s against 53 s. The author raised the count from 8 to 12 on 2026-11-11 (BUILD-apply):
# most of a group's wall time was spent waiting for a slot. Waiting pieces queue on a lock of
# $slot_dir/queue (fd 5; fd 8 is the run lock, which pieces inherit and must keep), so only the
# first in the queue polls the slots and they are taken first come, first served; a killed waiter
# frees the queue as a killed piece frees its slot. Six pieces polling without it used 2.9-3.1 s of
# processor time in 5 s.
slots=12
slot_dir=${XDG_RUNTIME_DIR:-/tmp}/zedtests-slots
mkdir -p "$slot_dir"
# glibc's memcpy and memset use rep movsb and rep stosb on a CPU with erms or fsrm, and the hardware
# counter sees either as one instruction or few, so a quadratic copy would pass a scaling test. A
# setting glibc does not know is ignored; this glibc leaves the stosb threshold alone without erms.
# The instructions malloc spends depend on what earlier threads left in the arena a new thread takes
# over, and on the order the hash seed frees blocks in. One check of the same program, on a new
# thread each time in one process, took 30.39 billion instructions or, in some runs, 30.65 billion,
# all of the extra in _int_malloc and unlink_chunk (callgrind); the difference of two such checks
# that l01_29's casts tests take came out 1.5 times its size in 3 of 30 runs. With no per-thread
# cache, the same 30 runs in 15 processes of random seeds repeat to within 0.04%, the first run of
# each process apart (SCALE-casts-spread). The mmap and trim thresholds are left alone: a fixed
# threshold of 128 KiB makes a 64,000-deep l01_26 test 6 times slower, and one of 32 MiB moves the
# sizes at which the memory limits of l01_17 and l01_36 refuse.
never=0xffffffffffffffff
malloc=glibc.malloc.tcache_count=0
export GLIBC_TUNABLES=glibc.cpu.hwcaps=-ERMS,-FSRM:glibc.cpu.x86_rep_movsb_threshold=$never:glibc.cpu.x86_rep_stosb_threshold=$never:$malloc
cores=$(nproc)
export root out slots slot_dir cores run_kind
take_slot() {
  exec 5>"$slot_dir/queue"
  flock 5
  while :; do
    for ((slot = 1; slot <= slots; slot++)); do
      exec 9>"$slot_dir/$slot"
      flock -n 9 && {
        exec 5>&-
        return
      }
    done
    sleep 0.1
  done
}
# A piece writes its output to the file of its slot, which the next piece in that slot overwrites,
# so a passing piece leaves no log and nothing is deleted. A failed piece's output is copied to its
# log; a passing piece empties a log left by an earlier failed run, so every log with contents is
# of a piece that failed in the last run that ran it.
piece() {
  name=$1 dir=$2
  shift 2
  take_slot
  scratch=$out/slot-$slot.out
  log=$out/$name.log
  read -r load _ </proc/loadavg
  limit=$(awk -v l="$load" -v c="$cores" 'BEGIN { x = 20 * l / c; print (x > 20 ? int(x + 1) : 20) }')
  start=$(date +%s%N)
  (cd "$root/$dir" && CARGO_MANIFEST_DIR=$root/$dir \
    systemd-run --user --scope --quiet --same-dir --slice=zedtests.slice \
    timeout -k 5 "$limit" "$@" >"$scratch" 2>&1)
  rc=$?
  ms=$((($(date +%s%N) - start) / 1000000))
  echo "$name rc=$rc ${ms}ms load=$load limit=${limit}s $(grep -E '^test result' "$scratch" | tail -1)"
  # A benchmark prints a few `bench ` lines, far less than the buffer grep writes at once, to a
  # file opened for appending, so the lines of pieces that end together are not mixed.
  [ "$run_kind" = test ] || grep "^bench " "$scratch" >>"$out/bench.log"
  if [ "$rc" = 0 ]; then
    [ ! -s "$log" ] || : >"$log"
  else
    cp "$scratch" "$log"
  fi
  : >"$scratch"
  [ "$rc" = 0 ]
}
export -f take_slot piece
# A test that builds executables (zed_native::link) keeps each one and links it again only when
# an input of its link changed (crates/zed-native/src/link.rs, `kept`). The runtime archive is
# one of those inputs, and Cargo builds it again after any change to zed-native or a crate under
# it, zed-kernel and zedc among them; the next run of such a test then links every executable
# again, about 1.5 s each, most of it GNU ld reading the 207 MB archive: the l01_36a piece took
# 13.4 s instead of 2.6 to 3.0 s at load 44 to 51, and once ran past its limit of 24 s
# (TEST-runtime-build-in-piece). So when the runtime archives beside the test binaries differ
# from those of the last run in $out, the selected pieces of the step folders whose sources call
# the linker run first, with no limit, as part of the build: the links are made there, and the
# pieces run again in the slots, where they find them kept. Their results are not counted; a
# piece that fails there fails again in the slots and is reported there.
warm() {
  name=$1 dir=$2
  shift 2
  take_slot
  start=$(date +%s%N)
  (cd "$root/$dir" && CARGO_MANIFEST_DIR=$root/$dir \
    systemd-run --user --scope --quiet --same-dir --slice=zedtests.slice \
    "$@" >"$out/warm-$slot.out" 2>&1)
  rc=$?
  : >"$out/warm-$slot.out"
  echo "$name links made before the timed pieces: rc=$rc $((($(date +%s%N) - start) / 1000000))ms"
  [ "$rc" = 0 ]
}
export -f warm
deps=$(dirname "$(head -1 "$out/pieces" | cut -d ' ' -f 3)")
runtimes=$(stat -c '%n %s %Y' "$deps"/libzed_native-*.a 2>/dev/null)
if [ "$runtimes" != "$(cat "$out/runtimes" 2>/dev/null)" ]; then
  # A piece calls the linker when the source of its module, read from its name (a step folder,
  # a file or folder in it, or a test in such a file, or in the folder's mod.rs), or the mod.rs
  # of its step folder, which holds the helpers its modules share, names zed_native::link or the
  # helpers of step L1.36a. A piece named <target>-<hash>, a test target of zed-native such as
  # build_binary, calls it when the file its Cargo.toml gives that target does.
  linker='zed_native::link|step_helpers::l01_36a_executables'
  declare -A source
  while read -r t p; do source[$t]=$p; done < <(awk '/^name = / { n = $3 }
    /^path = / { p = $3; gsub(/"/, "", n); gsub(/"/, "", p); f = FILENAME; sub(/[^\/]*$/, "", f)
      print n, f p }' crates/*/Cargo.toml tests/Cargo.toml)
  while read -r name rest; do
    g=tests/steps/${name%%::*}
    if [ ! -d "$g" ]; then
      p=${source[${name%-*}]}
      if [ -n "$p" ] && [[ $p == *.rs ]] && grep -qsE "$linker" "$p"; then
        echo "$name $rest"
      fi
      continue
    fi
    p=tests/steps/${name//:://}
    while [ ! -e "$p.rs" ] && [ ! -d "$p" ] && [[ $p == tests/steps/*/* ]]; do p=${p%/*}; done
    [ ! -e "$p.rs" ] || p=$p.rs
    [ "$p" != "$g" ] || [ "$name" = "${name%%::*}" ] || p=$g/mod.rs
    if grep -rqsE "$linker" "$p" || grep -qsE "$linker" "$g/mod.rs"; then
      echo "$name $rest"
    fi
  done <"$out/pieces" >"$out/linking"
  if [ ! -s "$out/linking" ] ||
    xargs -P "$jobs" -L 1 bash -c 'warm "$@"' _ <"$out/linking"; then
    printf '%s\n' "$runtimes" >"$out/runtimes"
  fi
fi
: >"$out/bench.log"
xargs -P "$jobs" -L 1 bash -c 'piece "$@"' _ <"$out/pieces" | tee "$out/summary"
bad=$(grep -vc 'rc=0 ' "$out/summary")
load=$(awk 'match($0, / load=[0-9.]+/) {
  l = substr($0, RSTART + 6, RLENGTH - 6) + 0
  if (NR == 1 || l < low) low = l
  if (l > high) high = l
} END { print low " to " high }' "$out/summary")
if [ -s "$out/bench.log" ]; then
  echo "bench lines ($out/bench.log):"
  cat "$out/bench.log"
fi
echo "pieces: $(wc -l <"$out/summary"), failed: $bad, load: $load, cores: $cores"
[ "$bad" = 0 ]
