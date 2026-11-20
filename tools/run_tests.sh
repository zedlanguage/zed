#!/bin/bash
# Runs the tests in pieces, one test binary, step folder, module or slow test each, each under a
# limit of 20 s (more under load, below), and prints a line per piece as it ends. Usage, from a
# checkout's root:
#   tools/run_tests.sh [--full] [--bench] [--each-test] [--only <ERE>] [--doc] [--list] [--reuse-table] [--logs <dir>] [--cov <dir>] [--trace <dir>] [jobs]
#   tools/run_tests.sh --short-clone-remove
# A run is of the correctness tests or, with --bench, of the benchmarks alone (TEST-bench-split,
# author P169). A benchmark is a test whose path holds `bench::`: it lies in a module `bench`,
# a file of its own (tests/steps/<step>/bench.rs, or src/.../bench.rs in a crate), and measures
# work at two sizes (zed_tests::scaling). The default run leaves out every piece whose tests are
# all benchmarks and gives a piece that holds some of them `--skip bench::` (with --exact, a
# `--skip` of each by name). --bench runs each benchmark as a piece of its own, named
# <group>::<test>, with the same jobs, slice, limit and summary lines; --only selects among them
# as among the correctness pieces. A benchmark runs with --nocapture, since libtest keeps the
# output of a passing test, and its lines that begin `bench ` (zed_tests::scaling) are written to
# <log dir>/bench.log and printed after the summary (TEST-time-pass-condition). --each-test runs
# each selected correctness test as a piece of its own, `--exact <test>` in one process
# (tools/time_tests.sh times the tests this way).
# Without --full this is the local suite, which needs only the Rust toolchain and runs in CI.
# --full adds tests/full/, the battery that needs emulators, containers, databases and other
# outside tools. It stops before any test if a tool is missing; nothing is skipped. Each folder
# tests/full/<piece>/ is a piece named full-<piece>, which is also its group and step, so that it
# is never confused with the local step folder of the same name (tests/steps/l01_21_test_runner
# and tests/full/l01_21_test_runner): not in --only, in its log, or in the files of --trace.
# --only runs only the pieces whose name, or whose group (the step folder, or the test binary's
# name without its hash, e.g. zedc, deep_heap, short-l01_37_oracle), matches the extended regular
# expression; a piece of a binary split per test also matches as <group>::<test>, and a piece
# named with its binary's hash (a library's unit tests, a benchmark) as <group>[::<path>] with the
# hash taken off. --only given more than once selects the union, its expressions joined by |
# as terms of one expression. A pattern with :: that names tests inside a whole-binary piece (zed_kernel::btree::)
# runs each test it matches as a piece of its own, with --exact. A test binary
# whose source lies in a step folder under another name (deep_types in l01_22_type_representation)
# has that folder as a second group, so a selection of the step runs it too. A pattern that
# matches no piece stops the run with an error, and so does a pattern one of whose terms matches
# none (its alternatives at the top level, a part ^(a|b|...)$ being a term per alternative): the
# run would pass on the other terms' pieces without running what that term names
# (TOOL-run-tests-empty-filter). A term <group>:: where <group> is one piece, such as a step
# folder, gets the term that selects it, ^(<group>)$. --skip-other-kind, which
# tools/merge_check.sh passes, notes and does not run a term that names a group whose pieces are
# all of the other kind (a test target with benchmarks alone, in a run without --bench).
# --short-groups prints the groups that have a short- piece and runs nothing. The
# short-addresses build is made only when a short- piece is selected, in a clone of build/cargo kept in build/short-clone from run to run;
# such a run must go through /home/luke/Work/wt/zrun, and --short-clone-remove deletes the clone
# (through zrun too) and runs nothing. --doc adds the check that the documentation of the whole
# workspace builds, which is off by default; --no-doc is accepted and changes nothing. Every run
# but --list checks the documentation of each package whose `///` or `//!` lines the checkout
# changes since origin/main, or whose doc links an item the checkout renames, deletes, makes
# private or puts behind a cfg (tools/check_changed_docs.sh). --list builds what the selection
# needs, prints the names of the selected pieces and runs nothing.
# Each run writes its logs, table and piece list in a directory of its own,
# build/test-logs/<UTC time>-<pid>, and build/test-logs/latest names the newest; --logs <dir>
# puts these under <dir> instead of build/test-logs. Runs at the same time, with --logs or not,
# share no file. A run without --only also publishes the table of all pieces as <dir>/table;
# --list --reuse-table selects from it without building or listing the binaries, for tests of
# the selection. The table is as the run that published it last left it: with --full or not, and
# stale once the test binaries are rebuilt.
# Without --only the build is `cargo test --workspace --no-run`, which does nothing on a tree
# already built that way, so a run after such a build starts the pieces at once. With --only it
# builds only the test binaries of the groups the pattern names, and the libraries under them,
# and runs only binaries this build reported, never one left from an earlier build (author,
# 2026-11-10: rebuild only the test binaries being worked on, whatever an upstream change
# touched). The binaries are chosen before the build, from their groups' names alone, so a test
# or a module is selected only with its binary's group, as <group>::<path>: a part of the pattern
# (an alternative at its top level) that selects no binary stops the run with an error naming it.
# A failed piece keeps its output in <the run's log directory>/<piece>.log, which the run prints.
# --trace <dir> runs each piece under strace, recording the file system calls of the piece and of
# every process it starts (open, stat, access, exec, readlink, directory listings and the rest of
# strace's %file class), and writes <dir>/<piece>.reads, the paths those calls named, one per
# line, relative to the checkout and sorted, those outside the checkout left out; `.` is the
# checkout's root, and `*` stands for every file, written when a call named the checkout's .git or
# a relative path with no directory strace could name (its cwd is not shown). <dir>/groups lists each piece with its group
# and step folder. tools/merge_check.sh --record uses these to tell which pieces a change since
# a passing check could affect (MERGE-push-race). The overhead, measured 2026-11-16 on the 384
# pieces of l01_26_type_resolution and short-l01_37a_short_addresses at 8 jobs and load 38 to 51:
# the pieces' times summed to 40.4 to 52.1 s traced against 28.5 to 34.6 s plain, about 40 ms more
# a piece (strace stops the piece at each file call, and loading its libraries makes hundreds);
# the wall times, 19 to 39 s traced and 11 to 38 s plain, differed by less than their noise.
# Every piece runs in the systemd slice zedtests.slice, whose 112 GB limit holds across all
# checkouts together. A piece's limit is max(20, 20 × load / cores) s: a load above the number of
# cores raises the limit of the pieces that start under it in proportion. It was 60 s until
# TEST-bench-split (author P169), which puts the measurements at two sizes in benchmarks, run
# apart with --bench, and asks each correctness test to take well under 1 s alone. A benchmark
# piece has a limit for each phase, counted from the phase's own start (author A160,
# 2026-11-20): that limit for each run at n and what comes before it, and the larger of that and
# 10.5 × t1 for each run at 8n, t1 the time of the run at n before it (author P214), which
# zed_tests::scaling writes for tools/bench_limit.sh. Until A160 one limit, max(that, 10.5 × the
# first t1), held the whole piece.
# --cov <dir> is a coverage run (TEST-cov-run-settings): the build goes to build/cov, apart from
# build/cargo, with `-C instrument-coverage` added to RUSTFLAGS, and each piece runs as in any
# other run, with the settings it gives every run (GLIBC_TUNABLES above all, which a test binary
# run directly gives itself by starting again, crate zed-meter-settings), writing its profiles
# to <dir>/<piece>-<pid>.profraw; build scripts and the links made before the timed pieces write
# <dir>/other-<pid>.profraw. Merge them with `llvm-profdata merge -sparse <dir>/*.profraw -o
# <file>` and read them with `llvm-cov report` or `llvm-cov show` and the binaries the run built,
# both the toolchain's own (component llvm-tools, in `$(rustc --print
# sysroot)/lib/rustlib/x86_64-unknown-linux-gnu/bin`): the system's are of an older LLVM, which
# refuses the compiler's raw profiles ("raw profile version mismatch", BUILD-parallel-frontend).
# A coverage run's scaling verdicts are printed but not to be relied on: each pass of a loop adds
# to a counter all threads share, and with tests beside each other the instruction counter read
# up to 5% high (TEST-cov-scaling-noise). The short-addresses pieces are not built for coverage.
args=$*
# The tests that read the spec's DESIGN.md and EXAMPLES.md in place (feature `spec` of the tests
# crate, author P371) are always built: a local run never leaves them out.
features=--features=zed-tests/spec full_suite= only= list= reuse= logs= doc= jobs=6 clone_remove= run_kind=test each_test= cov= trace=
short_groups= skip_other_kind=
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
      # A second --only adds its expression as one more alternative: `only=$2` alone kept the
      # last, so --only m0_03_grammar_tools --only zed_meter_settings ran the meter piece alone
      # and passed (tools4, 2026-11-20). Each term is then checked by check_terms.
      only=${only:+$only|}$2
      shift
      ;;
    --doc) doc=1 ;;
    --no-doc) ;;
    --list) list=1 doc= ;;
    --reuse-table) reuse=1 ;;
    --short-clone-remove) clone_remove=1 ;;
    --short-groups) short_groups=1 ;;
    --skip-other-kind) skip_other_kind=1 ;;
    --logs)
      if [ $# -lt 2 ] || [ -z "$2" ]; then
        echo "--logs needs a directory"
        exit 2
      fi
      logs=$2
      shift
      ;;
    --cov)
      if [ $# -lt 2 ] || [ -z "$2" ]; then
        echo "--cov needs a directory for the profiles"
        exit 2
      fi
      cov=$2
      shift
      ;;
    --trace)
      if [ $# -lt 2 ] || [ -z "$2" ]; then
        echo "--trace needs a directory for the read lists"
        exit 2
      fi
      trace=$2
      shift
      ;;
    [1-9]*) jobs=$1 ;;
    *)
      echo "unknown argument: $1 (usage: tools/run_tests.sh [--full] [--bench] [--each-test] [--only <ERE>] [--skip-other-kind] [--doc] [--list] [--reuse-table] [--logs <dir>] [--cov <dir>] [--trace <dir>] [--short-clone-remove] [--short-groups] [jobs])"
      exit 2
      ;;
  esac
  shift
done
if [ -n "$reuse" ] && [ -z "$list" ]; then
  echo "--reuse-table needs --list"
  exit 2
fi
# short_steps names the steps of the short-addresses build.
short_steps="l01_37a_short_addresses l01_37_oracle"
# short_libs names the packages whose unit tests also run in the short-addresses build, each as
# the piece short-<package with - made _>: the zed-kernel unit tests reach the lines taken only
# when digests tie (the `ByType` buckets, the orders by contents after a tie), which no other
# test reaches (TEST-kernel-units-short-addresses, 2026-11-18).
short_libs="zed-kernel"
if [ -n "$short_groups" ]; then
  printf '%s\n' $short_steps ${short_libs//-/_}
  exit 0
fi
if [ -n "$only" ]; then
  { [[ x =~ $only ]]; } 2>/dev/null
  if [ $? = 2 ]; then
    echo "--only: not a valid extended regular expression: $only"
    exit 2
  fi
fi
# Whether the piece $2 of group $1 is selected: always without --only. A piece of a library's
# unit tests or a benchmark is named after its binary, hash and all (zed_kernel-744b8b7231e6eb90
# or zed_kernel-744b8b7231e6eb90::btree::bench::<test>), so it also matches with the hash taken
# off (zed_kernel::btree::bench::<test>), as its group is (TOOLS-only-lib-pieces,
# TEST-bench-select-one).
selected() {
  [ -z "$only" ] || [[ $2 =~ $only || $1 =~ $only ]] || { [[ $2 != "$1"* ]] && [[ $1::$2 =~ $only ]]; } ||
    { [[ $2 =~ ^$1-[0-9a-f]+(::.*)?$ ]] && [[ $1${BASH_REMATCH[1]} =~ $only ]]; }
}
if [ -n "$full_suite" ]; then
  features=--features=zed-tests/full,zed-tests/spec
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
. "$root/tools/lib.sh" || exit 2
# A coverage run builds apart, so the build/cargo of ordinary runs stays as it is. Without a
# LLVM_PROFILE_FILE an instrumented program writes default_<hash>.profraw in the directory it
# runs in, a step folder or a package's source, so one is set before the build, whose build
# scripts are instrumented too; each piece sets its own (piece, below).
if [ -n "$cov" ]; then
  [[ $cov == /* ]] || cov=$root/$cov
  mkdir -p "$cov" || exit 1
  export CARGO_TARGET_DIR=$root/build/cov
  # zrun's absolute rpaths name build/cargo only; a copy of an executable in another directory
  # (l01_36a a_stripped_zedc_builds) finds this build's dylibs, whose hashed names differ from
  # build/cargo's, only through this one.
  export RUSTFLAGS="${RUSTFLAGS:+$RUSTFLAGS }-C instrument-coverage -C link-arg=-Wl,-rpath,$root/build/cov/debug/deps"
  export LLVM_PROFILE_FILE=$cov/other-%p.profraw
fi
if [ -n "$trace" ]; then
  [[ $trace == /* ]] || trace=$root/$trace
  mkdir -p "$trace" || exit 1
  command -v strace >/dev/null || { echo "--trace needs strace"; exit 2; }
fi
# The short-addresses build (step L1.37a) keeps 8 bits of every content address and type digest,
# so distinct values collide; its pieces check that every place that compares by address
# confirms equal addresses by contents, and that verdicts and outputs match the full build.
# It builds in a clone of the checkout's build: an overlay mounted at <the run's log
# directory>/short-clone whose one lower layer is build/cargo, read-only, and whose upper layer build/short-clone/upper
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
# The feature's crates are dylibs whose file names are the same in both builds
# (debug/deps/libzedc.so and the like, or libzedc-<hash>.so in a worktree with build/LIBHASH,
# where the hash depends on the features and profile only: see zrun), and their fingerprint
# directories have the same names in both builds, so the
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
# Each run mounts it at a directory of its own, <its log directory>/short-clone, with the overlay
# option index=on, under which the kernel refuses a second mount of an upper layer while one is
# mounted ("overlay already mounted or mount point busy"), in this namespace or any other
# (measured 2026-11-19 in a zrun namespace with build/cargo as the lower layer, as here; each run
# checks that it still holds, see mount_short_clone). So two
# runs of one checkout never write the clone at once, with no lock file (NO-LOCKS-optimistic,
# author 2026-11-19: "There should be no locks anywhere"; until then the second run waited on
# build/short-clone.lock): the second finds the mount refused and the first run's mount in the
# namespace's mount table, and tries again every 2 s until that run has ended. Only one mount of
# an upper layer at a time is defined behavior for an overlay, so the wait is the cost of
# sharing the kept clone; a clone of its own would rebuild for 180 to 237 s and leave GBs to
# delete. A run killed with SIGKILL leaves its mount behind, which the next run unmounts once no
# process has the pid named in that mount's directory. Checkouts do not share a clone, as each
# zrun namespace mounts its own checkout at the fixed path.
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
# Prints the directory of each mount of the clone in this namespace, one a line.
short_clone_mounts() {
  findmnt -rn -t overlay -o TARGET,OPTIONS |
    awk '$2 ~ /(^|,)upperdir=\/home\/luke\/Work\/wt\/\.build-root\/build\/short-clone\/upper(,|$)/ { print $1 }'
}
# Unmounts each mount of the clone whose run has ended: one at <dir>/<time>-<pid>/short-clone
# with no process <pid>, or one at build/short-clone/cargo, where a run before NO-LOCKS-optimistic
# mounted it, that no process is using (umount refuses one in use). Prints the directory of each
# mount left, the runs still using the clone. A pid used again by another process since the run
# ended keeps its mount until that process ends; the clone waits that long.
unmount_dead_short_clones() {
  local m pid
  for m in $(short_clone_mounts); do
    if [[ $m =~ -([0-9]+)/short-clone$ ]]; then
      pid=${BASH_REMATCH[1]}
      if [ "$pid" != $$ ] && [ ! -d "/proc/$pid" ] && umount "$m"; then
        continue
      fi
    elif [ "$m" = /home/luke/Work/wt/.build-root/build/short-clone/cargo ] && umount "$m" 2>/dev/null; then
      continue
    fi
    echo "$m"
  done
}
# Opens again the overlay's inner work directory of the clone, which the kernel leaves at mode
# 000 and rm cannot enter, so that deleting the clone or the checkout succeeds.
open_short_clone_work() {
  [ -L /home/luke/Work/wt/.build-root/build/short-clone/work/work ] ||
    [ ! -d /home/luke/Work/wt/.build-root/build/short-clone/work/work ] ||
    chmod u+rwx /home/luke/Work/wt/.build-root/build/short-clone/work/work
}
# Deletes the clone, when no run has it mounted. It is first renamed to
# build/short-clone-dropped, so that a run arriving meanwhile finds no clone and makes a new
# one, and two runs dropping it at once delete it once: one rename succeeds. Every path is
# written out: a delete names its target in full (the author's rule), and the clone exists only
# at the fixed path of zrun. A leftover build/short-clone-dropped, from a run killed while
# deleting it, is deleted first.
drop_short_clone() {
  local d
  if [ -e /home/luke/Work/wt/.build-root/build/short-clone-dropped ]; then
    if [ -L /home/luke/Work/wt/.build-root/build/short-clone-dropped ] ||
      [ "$(realpath -e /home/luke/Work/wt/.build-root/build/short-clone-dropped)" != \
        /home/luke/Work/wt/.build-root/build/short-clone-dropped ]; then
      echo "/home/luke/Work/wt/.build-root/build/short-clone-dropped is not a directory; it is left in place."
      return 1
    fi
    [ -L /home/luke/Work/wt/.build-root/build/short-clone-dropped/work/work ] ||
      [ ! -d /home/luke/Work/wt/.build-root/build/short-clone-dropped/work/work ] ||
      chmod u+rwx /home/luke/Work/wt/.build-root/build/short-clone-dropped/work/work
    rm -rf --one-file-system --preserve-root=all /home/luke/Work/wt/.build-root/build/short-clone-dropped
  fi
  [ -e /home/luke/Work/wt/.build-root/build/short-clone ] || return 0
  d=$(unmount_dead_short_clones)
  if [ -n "$d" ]; then
    echo "The short-addresses clone is mounted by a run still going, at:" $d
    return 1
  fi
  if [ -L /home/luke/Work/wt/.build-root/build/short-clone ] ||
    [ ! -d /home/luke/Work/wt/.build-root/build/short-clone ] ||
    [ "$(realpath -e /home/luke/Work/wt/.build-root/build/short-clone)" != \
      /home/luke/Work/wt/.build-root/build/short-clone ]; then
    echo "The short-addresses clone /home/luke/Work/wt/.build-root/build/short-clone is not a" \
      "directory; it is left in place."
    return 1
  fi
  open_short_clone_work
  # A run that checked for mounts just before another mounted the clone would rename it from
  # under that run's build; both runs would have to find the clone stale within the same few
  # milliseconds, and the build that loses its files fails and is reported, not passed.
  if ! mv -T /home/luke/Work/wt/.build-root/build/short-clone /home/luke/Work/wt/.build-root/build/short-clone-dropped; then
    # Another run renamed it first, and may have made a new one since.
    [ ! -e /home/luke/Work/wt/.build-root/build/short-clone ] && return 0
    [ -n "$stamp" ] && [ "$(cat /home/luke/Work/wt/.build-root/build/short-clone/stamp 2>/dev/null)" = "$stamp" ] && return 0
    echo "The short-addresses clone could not be renamed for deletion."
    return 1
  fi
  rm -rf --one-file-system --preserve-root=all /home/luke/Work/wt/.build-root/build/short-clone-dropped
}
# Mounts the clone at <this run's log directory>/short-clone, made again first when it was made
# from another build of this checkout, and waits while another run has it mounted.
mount_short_clone() {
  local m said= free=
  mkdir -p "$out/short-clone" || return 1
  while :; do
    m=$(unmount_dead_short_clones)
    if [ -z "$m" ] && [ -e /home/luke/Work/wt/.build-root/build/short-clone ] &&
      [ "$(cat /home/luke/Work/wt/.build-root/build/short-clone/stamp 2>/dev/null)" != "$stamp" ]; then
      echo "The short-addresses clone was made from another build of this checkout; it is made again."
      drop_short_clone || return 1
    fi
    mkdir -p /home/luke/Work/wt/.build-root/build/short-clone/upper /home/luke/Work/wt/.build-root/build/short-clone/work || return 1
    if [ ! -e /home/luke/Work/wt/.build-root/build/short-clone/stamp ]; then
      printf '%s\n' "$stamp" >"$out/short-clone.stamp" &&
        mv -T "$out/short-clone.stamp" /home/luke/Work/wt/.build-root/build/short-clone/stamp || return 1
    fi
    if mount -t overlay overlay -o "lowerdir=$root/build/cargo,upperdir=/home/luke/Work/wt/.build-root/build/short-clone/upper,workdir=/home/luke/Work/wt/.build-root/build/short-clone/work,userxattr,index=on" \
      "$out/short-clone" 2>"$out/short-clone.err"; then
      # The refusal of a second mount is what keeps two runs from the clone at once. With
      # userxattr the kernel turns index off (findmnt shows no index), yet it checks index=on
      # first and refuses (Linux 7.3.3, 2026-11-19). A kernel that stops refusing would let two runs
      # write the clone at once, so each run checks: a second mount must fail.
      mkdir -p "$out/short-clone-check"
      if mount -t overlay overlay -o "lowerdir=$root/build/cargo,upperdir=/home/luke/Work/wt/.build-root/build/short-clone/upper,workdir=/home/luke/Work/wt/.build-root/build/short-clone/work,userxattr,index=on" \
        "$out/short-clone-check" 2>/dev/null; then
        umount "$out/short-clone-check"
        umount "$out/short-clone"
        echo "This kernel mounts the short-addresses clone twice with index=on, so two runs could write it at" \
          "once; tools/run_tests.sh needs another way to keep them apart (NO-LOCKS-optimistic)."
        return 1
      fi
      # Another run may have made the clone again between the check above and the mount.
      [ "$(cat /home/luke/Work/wt/.build-root/build/short-clone/stamp)" = "$stamp" ] && return 0
      umount "$out/short-clone"
      continue
    fi
    m=$(unmount_dead_short_clones)
    if [ -z "$m" ]; then
      # The run that had it mounted may have ended since the mount was refused: one more try.
      if [ -n "$free" ]; then
        cat "$out/short-clone.err"
        echo "The short-addresses clone of build/cargo could not be mounted."
        return 1
      fi
      free=1
      continue
    fi
    free=
    [ -n "$said" ] || echo "Waiting for the run that has the short-addresses clone mounted at" $m "to end."
    said=1
    sleep 2
  done
}
if [ -n "$clone_remove" ]; then
  if [ "$root" != /home/luke/Work/wt/.build-root ]; then
    echo "The short-addresses clone is mounted in the zrun namespace; run" \
      "/home/luke/Work/wt/zrun tools/run_tests.sh --short-clone-remove from the checkout's root."
    exit 1
  fi
  if [ ! -e /home/luke/Work/wt/.build-root/build/short-clone ]; then
    echo "This checkout has no short-addresses clone."
    exit 0
  fi
  drop_short_clone || exit 1
  echo "The short-addresses clone of this checkout is deleted."
  exit 0
fi
logbase=${logs:-build/test-logs}
[[ $logbase == /* ]] || logbase=$root/$logbase
# Each run writes into a log directory of its own, <base>/<UTC time>-<pid>, so runs at the same
# time share no file and none waits for another (NO-LOCKS-optimistic, author 2026-11-19: "There
# should be no locks anywhere"). Until then one run held a lock on <base>/run.lock and a second
# run on the same base stopped at once. <base>/latest names the directory of the run that started
# last; it is replaced by a rename, so a reader sees the old or the new link, never none. What a
# later run reads from an earlier one, the table of all pieces and the runtimes the links were
# made for, is published in <base> the same way (publish, below). The run directories are kept:
# TOOL-test-logs-prune deletes old ones.
out=$logbase/$(date -u +%Y%m%dT%H%M%S.%NZ)-$$
mkdir -p "$out" || exit 1
ln -sfn "${out##*/}" "$logbase/latest.$$" && mv -T "$logbase/latest.$$" "$logbase/latest"
echo "process $$, started $(date '+%F %T'), arguments: ${args:-none}" >"$out/run"
# A --list run prints the piece names alone, which its callers read.
[ -n "$list" ] || echo "logs: $out"
# publish <file> <name>: puts a copy of <file> at <base>/<name> by a rename, so a reader of it sees
# one whole version, the last one published.
publish() { cp "$1" "$logbase/$2.$$" && mv -T "$logbase/$2.$$" "$logbase/$2"; }
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
# The alternatives at the top level of the extended regular expression $1, one per line: it is
# split at each | outside parentheses, bracket expressions and escapes. Fails when a ) closes a
# parenthesis that was not opened (terms, below, reads the inside of ^(...)$ with it).
alternatives() {
  local re=$1 n=${#1} i=0 j depth=0 cur= c rest close unopened=
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
      \))
        depth=$((depth - 1))
        [ "$depth" -ge 0 ] || unopened=1
        ;;
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
  [ -z "$unopened" ]
}
# Writes the pieces of the table $1 of the kind the run is of that --only selects to
# $out/pieces, one per line: its name, directory and command. A line of the table is a piece's
# kind, group and step folder, then those. With --each-test, each selected piece of the run's kind
# becomes a piece per test it runs, <its name before the first ::>::<test> running
# `--exact <test>`.
select_pieces() {
  local k group step name dir bin args first t
  # The groups and steps of the table's pieces of the run's kind, for the hints of check_terms,
  # and those of the other kind, for --skip-other-kind.
  local -A groups others
  read -r first _ <"$1"
  if [ "$first" != test ] && [ "$first" != bench ]; then
    echo "$1 is a table of pieces of an older tools/run_tests.sh, without the kind of each"
    echo "piece; run tools/run_tests.sh --list without --only to write it again."
    exit 1
  fi
  [ -z "$trace" ] || : >"$trace/groups"
  # Besides $out/pieces, the loop writes to fd 3 ($out/chosen) the group, step and name each
  # selected piece was selected by (its name before --each-test split it), for check_terms.
  while read -r k group step name dir bin args; do
    [ "$k" = "$run_kind" ] || { others[$group]=1 others[$step]=1 && continue; }
    groups[$group]=1 groups[$step]=1
    [ "$k" = test ] || args="${args:+$args }--nocapture"
    if ! selected "$group" "$name" && ! selected "$step" "$name"; then
      # A piece of a binary named with its hash, not selected as a whole, still gives each of
      # its tests whose <group>::<test> --only matches as a piece of its own, run as with
      # --each-test, so that --only '^zed_kernel::btree::' runs those unit tests of the library
      # (TOOLS-only-lib-pieces). Only a pattern with :: can match such a name, so only then is
      # the binary's list read (once per binary, as above). A benchmark is a piece per test
      # already, so this is for correctness pieces alone.
      [[ $k == test && $only == *::* && $name =~ ^$group-[0-9a-f]+(::|$) ]] || continue
      list_binary "$bin"
      for t in $(piece_tests "$bin" $args); do
        [[ $group::$t =~ $only ]] || continue
        [ -z "$trace" ] || echo "${name%%::*}::$t $group $step" >>"$trace/groups"
        echo "$group $step ${name%%::*}::$t" >&3
        echo "${name%%::*}::$t $dir $bin --exact $t"
      done
      continue
    fi
    if [ -z "$each_test" ]; then
      [ -z "$trace" ] || echo "$name $group $step" >>"$trace/groups"
      echo "$group $step $name" >&3
      echo "$name $dir $bin${args:+ $args}"
      continue
    fi
    list_binary "$bin"
    for t in $(piece_tests "$bin" $args); do
      [ -z "$trace" ] || echo "${name%%::*}::$t $group $step" >>"$trace/groups"
      echo "$group $step $name" >&3
      echo "${name%%::*}::$t $dir $bin --exact $t"
    done
  done <"$1" >"$out/pieces" 3>"$out/chosen"
  local among=
  [ "$run_kind" = test ] || among=" among the benchmarks"
  if [ ! -s "$out/pieces" ]; then
    # Under --skip-other-kind, --only naming groups of the other kind alone is not an error:
    # check_terms stops the run on any other term, or notes each such group.
    if [ -n "$skip_other_kind" ] && [ -n "$only" ]; then
      check_terms
      echo "--skip-other-kind: nothing to run$among"
      exit 0
    fi
    if [ -n "$only" ]; then
      echo "NO PIECE MATCHES --only '$only'$among${each_test:+ (or the pieces it selects run no test)}"
      while IFS= read -r t; do group_hint "$t"; done < <(terms "$only")
    else
      echo "NO PIECE TO RUN$among"
    fi
    exit 1
  fi
  [ -z "$only" ] || check_terms
}
# The terms of --only, one per line: its alternatives at the top level (alternatives, below),
# with a part ^(B1|...|Bn)$ split into ^(B1)$ ... ^(Bn)$, which select the same pieces, since
# each anchor applies to every alternative inside the parentheses. So the one part
# ^(g1|g2|...)$ of tools/merge_check.sh's --only is a term per group.
terms() {
  local a body inner
  while IFS= read -r a; do
    body=${a#'^('}
    body=${body%')$'}
    # alternatives fails when a ) closes more than was opened, as in ^(a)|(b)$ read as a)|(b.
    if [ "^($body)\$" = "$a" ] && inner=$(alternatives "$body"); then
      while IFS= read -r a; do
        echo "^($a)\$"
      done <<<"$inner"
    else
      echo "$a"
    fi
  done < <(alternatives "$1")
}
# A term written <group>:: (with ^, parentheses or a final $ or not) selects only the pieces
# named <group>::<path>; when <group> is a group or step of the run's kind, prints the term that
# selects it, since a step folder that is not split per module or test is one piece named after
# the folder, which <group>:: does not match (TOOL-run-tests-empty-filter). Reads the groups of
# select_pieces.
group_hint() {
  [[ $1 =~ ^\^?\(?([A-Za-z0-9_-]+)\)?::\)?\$?$ ]] || return 0
  local g=${BASH_REMATCH[1]}
  [ -z "${groups[$g]+x}" ] ||
    echo "No piece is named $g::<path>; '^($g)\$' selects the pieces of $g."
}
# Stops the run when a term of --only selects no piece that select_pieces chose: the run would
# otherwise pass on the other terms' pieces without running what that term names
# (TOOL-run-tests-empty-filter: --only '^l01_36_cranelift$|m0_03_grammar_tools::' ran l01_36's
# 142 pieces and passed, though no piece is named m0_03_grammar_tools::<path>). A term matches a
# chosen piece as selected does, on its group, step and name. A term that is one anchored name,
# ^name$ or ^(name)$ (each term of tools/merge_check.sh's --only), is looked up in a hash of the
# strings each chosen piece matches as: O(1) a term after O(pieces) to fill it, where matching
# each term against each piece would be O(terms × pieces), 300 × 3,000 for a merge check. Any
# other term is matched against the chosen pieces until one matches, at most O(pieces) a term,
# the cost the selection itself paid for that term inside --only's regular expression.
check_terms() {
  local t g s n x name saved=$only bad=
  local -A have
  while read -r g s n; do
    have[$n]=1
    for x in "$g" "$s"; do
      have[$x]=1
      [[ $n == "$x"* ]] || have[$x::$n]=1
      [[ $n =~ ^$x-[0-9a-f]+(::.*)?$ ]] && have[$x${BASH_REMATCH[1]}]=1
    done
  done <"$out/chosen"
  name='^\^(\(([A-Za-z0-9_:-]+)\)|([A-Za-z0-9_:-]+))\$$'
  while IFS= read -r t; do
    if [[ $t =~ $name ]]; then
      x=${BASH_REMATCH[2]}${BASH_REMATCH[3]}
      [ -z "${have[$x]+x}" ] || continue
      # --skip-other-kind (tools/merge_check.sh, which names every test target of the packages a
      # change reaches): a group or step whose pieces are all of the other kind, such as a test
      # target holding benchmarks alone, is noted and not run.
      if [ -n "$skip_other_kind" ] && [ -n "${others[$x]+x}" ] && [ -z "${groups[$x]+x}" ]; then
        if [ "$run_kind" = test ]; then
          echo "--skip-other-kind: $x has benchmarks alone, which a run without --bench does not run"
        else
          echo "--skip-other-kind: $x has no benchmark, which a run with --bench runs alone"
        fi
        continue
      fi
    else
      only=$t
      while read -r g s n; do
        selected "$g" "$n" || selected "$s" "$n" || continue
        only=
        break
      done <"$out/chosen"
      [ -n "$only" ] || { only=$saved && continue; }
      only=$saved
    fi
    echo "--only: the term '$t' of '$only' selects no piece$among, so the run would pass without running what it names."
    group_hint "$t"
    bad=1
  done < <(terms "$only")
  [ -z "$bad" ] || exit 1
}
if [ -n "$reuse" ]; then
  if [ ! -s "$logbase/table" ]; then
    echo "--reuse-table: no $logbase/table; run tools/run_tests.sh --list without --only first"
    exit 1
  fi
  select_pieces "$logbase/table"
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
# tests/full are selected below, by their pieces' names, as before (short_steps and short_libs,
# above, name the short-addresses build's steps and packages).
# The short-addresses pieces build in a clone mounted in the zrun namespace (see below), so a
# run that selects one stops here, before any build, when it does not run through zrun. A
# piece is selected by `wants`, as the other binaries are below, so that an alternative naming a
# test in one, ^short-zed_kernel::types::bdd::bench::<test>, builds it; `selected` matches the
# whole name short-zed_kernel only, and such a run built nothing and listed no piece.
short_build=
for s in $short_steps ${short_libs//-/_}; do
  if [ -z "$only" ]; then
    short_build=1
  else
    while read -r a; do
      wants "$a" "short-$s" "short-$s" && short_build=1
    done < <(alternatives "$only")
  fi
done
if [ -n "$short_build" ] && [ -n "$cov" ]; then
  echo "--cov: the short-addresses pieces are not built for coverage; leave them out of --only"
  exit 2
fi
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
        wants "$a" "full-$d" "full-$d" && any=1 && tests+="--test full"$'\n'
      done
    fi
    for s in $short_steps ${short_libs//-/_}; do
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
    # the library every test binary loads, and the next build rebuilds it. (In a worktree with
    # build/LIBHASH each set of features has its own file, see zrun, so such a build overwrites
    # nothing but is still a second build of the package.) The packages ask for
    # the workspace's features (dev-dependencies in crates/zed-native, crates/zed-tools and
    # tests); this stops the build when one does not, before anything is overwritten.
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
  stamp=$(short_clone_stamp)
  trap '! mountpoint -q "$out/short-clone" || umount "$out/short-clone"; open_short_clone_work' EXIT
  trap 'exit 129' HUP
  trap 'exit 130' INT
  trap 'exit 143' TERM
  mount_short_clone || exit 1
  if ! CARGO_TARGET_DIR=$out/short-clone cargo test -p zed-tests --features short-addresses,spec \
    $(printf -- '--test %s ' $short_steps) --no-run --message-format=short >"$out/build-short.log" 2>&1; then
    tail -40 "$out/build-short.log"
    echo "BUILD FAILED (short-addresses)"
    exit 1
  fi
  # The packages of short_libs ask for nothing but short-addresses, which the build above gave
  # zed-kernel already, so this builds only their unit-test binaries.
  if ! CARGO_TARGET_DIR=$out/short-clone cargo test $(printf -- '-p %s ' $short_libs) \
    --features short-addresses --lib --no-run --message-format=short >>"$out/build-short.log" 2>&1; then
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
# l01_38 omega, scaling, names, live3, stages and one_scope moved to l01_38_omega_test, split the
# same way (2026-11-14, TESTS-split).
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
# (2026-11-11, TESTS-lhx-families). lazy, linked and families moved to l01_39_scope_relations,
# split the same way (2026-11-14, TESTS-split).
# l01_39_scope_relations case_wake took 28.4 s whole at load 72 and ran past its limit of 31 s
# at load 49 once FAIL-case-wake-puncture-17583574254131380130 added its seed test; its 16 tests
# take 96 s one after another, the slowest 17.5 s (that seed test) and 13.1 s; each test is a
# piece (2026-11-19, PERF-l139-under9).
# l01_23 r6_reduction, one test of 384 formulas, took 38 to 77 s alone at load 27 to 41 and ran
# past its limit of 90 s in a full run at load 48; it is four tests of 96 formulas, each a piece
# (2026-11-11, REFUSAL-front-xr after batch merge 128). r6_reduction, refusals and the decider's
# modules moved to l01_23_groups_and_refusals, split the same way (2026-11-14, TESTS-split).
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
# half as large (2026-11-12, TESTS-l01_29-split). casts, offered_repairs and the other repair and
# printing modules moved to l01_29_repairs_and_printing, split the same way (2026-11-14, TESTS-split).
# l01_26a_generic_literals took 42 s whole at load 50; each module (one per test file, so a new
# file is a piece of its own) and each test of mod.rs is a piece. The slowest pieces are scaling
# and lit_branch_ops, 24 to 50 s and 26 to 45 s at load 35 to 51. libtest runs a module's tests on
# parallel threads, so each takes about as long as its slowest test: scaling's test of many calls
# given divisions took 29 to 39 s alone at load 40 to 48. A piece per test of the two modules
# was no faster: in alternate runs at load 39 to 49 the module pieces took 24 and 28 s, the
# piece per test 34 and 32 s at most (2026-11-13, TESTS-l01_26a-split).
split="
  l01_08_parser l01_16_elaboration l01_16_elaboration::scaling
  l01_23_groups_and_refusals l01_23_groups_and_refusals::r6_reduction
  l01_23_subtyping l01_23_subtyping::scaling
  l01_25_preimage_catalog l01_25_preimage_catalog::s22
  l01_25_preimage_catalog::exact_oracle
  l01_26_type_resolution l01_26_type_resolution::deep_ops l01_26_type_resolution::op_table
  l01_26a_generic_literals
  l01_28_staging l01_28_staging::scaling l01_28_staging::dag
  l01_29_diagnostics l01_29_repairs_and_printing l01_29_repairs_and_printing::casts
  l01_29_repairs_and_printing::offered_repairs
  l01_29_repairs_and_printing::offered_repairs::every_offered_repair_inside_a_sum_checks_as_written
  l01_29_repairs_and_printing::offered_repairs::every_offered_repair_inside_a_call_checks_as_written
  l01_36_cranelift l01_36_cranelift::scaling l01_36_cranelift::table
  l01_36_cranelift::mul_edges
  l01_38_omega_test l01_38_presburger l01_38_presburger::oracle
  l01_38_presburger::deep l01_38_presburger::shared
  l01_38_omega_test::omega l01_38_omega_test::scaling
  l01_38_omega_test::names l01_38_omega_test::live3
  l01_38_omega_test::stages l01_38_omega_test::one_scope
  l01_39_reduced_product l01_39_scope_relations l01_39_reduced_product::random
  l01_39_reduced_product::pendants l01_39_scope_relations::lazy
  l01_39_scope_relations::case_wake
  l01_39_scope_relations::lazy::a_lazy_scope_settles_each_name_to_the_eager_product
  l01_39_scope_relations::lazy::a_lazy_scope_with_stars_of_two_hubs_settles_each_name_to_the_eager_product
  l01_39_scope_relations::lazy::a_lazy_scope_with_satellites_of_two_hubs_settles_each_name_to_the_eager_product
  l01_39_scope_relations::lazy::leaves_of_one_class_settled_together_get_what_each_gets_alone
  l01_39_scope_relations::lazy::a_join_settles_a_star_it_drops_or_whose_core_gains_a_disjunction
  l01_39_scope_relations::lazy::a_join_settles_the_leaves_whose_core_differs_as_settling_every_name_does
  l01_39_reduced_product::deep_let
  l01_39_reduced_product::if_shortcut
  l01_39_reduced_product::refused
  l01_39_scope_relations::linked
  l01_39_scope_relations::linked::holes_in_a_tree_of_differences_give_the_projection_from_scratch
  l01_39_scope_relations::linked::holes_piled_in_many_names_of_a_tree_give_the_projection_from_scratch
  l01_39_reduced_product::exact
  l01_39_reduced_product::exact::constraints_reduced_one_at_a_time_decide_as_all_at_once
  l01_39_scope_relations::families
  l01_39a_bit_words l01_39a_bit_words::scaling
  l25_08_mutate l25_08_mutate::scaling
  m0_12_refusal_census
"
# Tests of a crate's unit-test binary named here, as <binary name without its hash>::<test>,
# run as a piece of their own (`--exact`), and the binary's other tests as one piece that skips
# them. zedc_preimage took 20.9 s whole at load 53 and 34.6 s at load 97, where its other 76
# tests take 5.7 s at load 89: its seed test of summaries read again takes 11 to 14 s alone at
# load 19 to 60, nearly all of it round 1 (PERF-preimage-seed-7776978274844439420-round1), so a
# piece started at low load ran past its limit of 20 s once the load rose
# (TEST-lib-pieces-near-limit, 2026-11-17).
# zed_kernel ran past its limit of 22 s at load 35 (merge of FAIL-overlaps-order-ddc1ec274,
# 2026-11-18); without benchmarks it took 12.5 to 14.7 s whole at load 39, and 3.9 s without its
# random test of the boolean equation solver, which takes about 10 s alone and is a piece of its own.
# zedc_presburger took 17.96 s without benchmarks at load 27 and 34.8 s at load 76 (88 s of CPU:
# the piece is starved of cores, so its time follows the CPU of all its tests). Its ten tests of
# 2.4 to 5.5 s of CPU each (37 s of the 88) are pieces of their own, each 4.2 to 7.1 s alone at
# load 72 to 91 (LIMIT-two-pin-ratio-11, 2026-11-19).
alone="
  zedc_preimage::preimage::tests::summaries_read_again_give_what_reading_the_term_again_gives_seed_7776978274844439420
  zed_kernel::types::bes::tests::decide_agrees_with_the_game_on_systems_drawn_at_random
  zedc_presburger::presburger::row_sums::tests::the_polygons_of_the_route_are_never_more_than_the_join_spends
  zedc_presburger::presburger::sweep_against_pick_tests::the_unbounded_row_sweep_marks_the_arms_pick_by_finds
  zedc_presburger::presburger::exact::tests::random_formulas_at_seed_10413658062665981385
  zedc_presburger::presburger::exact::tests::random_formulas_at_seed_4164922340731529606
  zedc_presburger::presburger::exact::tests::random_formulas_at_seed_13733945893095969990
  zedc_presburger::presburger::exact::tests::random_formulas_at_seed_3569362060062839708
  zedc_presburger::presburger::exact::tests::random_formulas_project_to_the_values_of_their_points
  zedc_presburger::presburger::row_sums::tests::the_route_and_the_join_agree_on_wide_ranges_with_several_defined_atoms
  zedc_presburger::presburger::exact::tests::read_once_formulas_project_to_the_values_of_their_points
  zedc_presburger::presburger::exact::tests::every_writing_of_a_formula_gets_one_answer
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
          [ -d "$c" ] || c=tests
          skips=
          for t in $alone; do
            [ "${t%%::*}" = "$g" ] || continue
            echo "$t $c $p --exact ${t#*::}"
            skips="$skips --skip ${t#*::}"
          done
          echo "$n $c $p$skips"
          ;;
        zed_kernel-*)
          skips=
          for t in $alone; do
            [ "${t%%::*}" = "$g" ] || continue
            echo "$t crates/zed-kernel $p --exact ${t#*::}"
            skips="$skips --skip ${t#*::}"
          done
          echo "$n crates/zed-kernel $p$skips"
          ;;
        zed_native-*) echo "$n crates/zed-native $p" ;;
        zed_rt-*) echo "$n crates/zed-rt $p" ;;
        zed_cert-*) echo "$n crates/zed-cert $p" ;;
        *) echo "$n tests $p" ;;
      esac
    fi | sed "s|^|$g ${step_of[$g]:-$g} |"
  done
  for p in $short; do
    n=short-$(basename "${p%-*}")
    case $n in
      # The unit tests only: the benchmarks of a library run in the workspace build. Their
      # bounds are proved for digests that do not tie (bdd's parity bench asserts that no two
      # atoms share a priority point, which 1,024 atoms of 8-bit digests cannot meet), and with
      # 256 digests a bucket of ties holds about n/256 entries, so each operation's work grows
      # with n and a ratio of 8n to n measures the 8-bit build, not the method. 22 of them failed
      # here at f215d9c90 and 25 at e4e3ad871, each passing in the workspace build
      # (FAIL-bench-main-f215d9c90).
      # The steps of short_steps have benchmarks written for both builds and keep them.
      short-zed_kernel) echo "$n $n $n crates/zed-kernel $p --skip bench::" ;;
      *) echo "$n $n $n tests $p" ;;
    esac
  done
  if [ -n "$full" ]; then
    for d in tests/full/*/; do
      n=$(basename "$d")
      echo "full-$n full-$n full-$n tests $full $n::"
    done
  fi
} | split_benchmarks >"$table"
[ -n "$only" ] || publish "$table" table || exit 1
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
# checkout changes since origin/main, or whose doc links an item it renames, deletes, makes private
# or puts behind a cfg (DOC-renamed-links), alone and with the workspace's features. Agents run
# this script before they merge, and seldom passed --doc, so links that broke the doc build reached
# main three times (DOC-private-links, -2, -3); with no doc comment and no linked item changed it
# builds nothing.
tools/check_changed_docs.sh "$out/doc-changed.log" || exit 1
# A run runs at most `jobs` pieces at once (xargs -P, below), and each piece's slot is the number
# xargs gives it in $slot (--process-slot-var), 0 to jobs - 1, unique among the pieces of the run
# running at that moment; it names the piece's scratch files in $out. Runs on the same machine do
# not wait for each other (author, 2026-11-19, NO-LOCKS-optimistic: "There should be no locks
# anywhere"). Until 2026-11-19 each piece first took one of 12 machine-wide slots, a `flock` on a
# file of $XDG_RUNTIME_DIR/zedtests-slots, with waiters queued on a flock of its file queue
# (BUILD-apply, BUILD-slots-measure: four suites at once took 2:13 with 8 slots and 2:05 without;
# 12 slots kept the slice peak at 42 GB or less). ZED_TEST_SLOTS set that count and is no longer
# read. Each piece's line gives `wait=`, the time from xargs starting it to its timer starting.
# The C library settings the scaling tests count work under: no rep movsb or rep stosb in memcpy
# and memset (the hardware counter sees either as one instruction or few, so a quadratic copy
# would pass). A measured run allocates from a heap of its own
# (crates/zed-alloc-count/src/meter.rs, TEST-meter-allocator-bias), so malloc keeps its per-thread
# cache. crates/zed-meter-settings/src/lib.rs holds the same text, with the reasons and
# measurements, and a test binary started without it starts itself again with it; this export saves that second start and gives the settings to the programs the
# tests run. Test run_tests_exports_the_settings_of_the_meter checks the two are equal.
export GLIBC_TUNABLES=glibc.cpu.hwcaps=-ERMS,-FSRM:glibc.cpu.x86_rep_movsb_threshold=0xffffffffffffffff:glibc.cpu.x86_rep_stosb_threshold=0xffffffffffffffff
# A benchmark measures one fixed draw of the treap priorities (crates/zed-kernel/src/priority.rs,
# PERF-treap-seeded-priorities), so its counts repeat from run to run and compare between trees:
# under a fresh draw each run the ratios of the s22 chain benchmarks of l01_25_preimage_catalog
# ranged from 8.1 to 10.49 in 4 runs (2026-11-16). A correctness run keeps a fresh draw, so each
# run also checks that the output does not depend on it. ZED_TREAP_SEED, when set, is kept.
[ "$run_kind" = test ] || export ZED_TREAP_SEED=${ZED_TREAP_SEED:-0}
# insta finds the workspace root, under which it reads and writes snapshots, by running `cargo
# metadata` in each test binary; when that fails (a toolchain the pin names but rustup lacks, as on
# 2026-11-17 during the switch to the nightly) it falls back to the tests crate's directory, and
# every snapshot test reports its snapshot as new, under tests/tests/steps/. The root given here
# keeps a toolchain fault out of the snapshot tests and saves one cargo run per test binary.
export INSTA_WORKSPACE_ROOT=$root
cores=$(nproc)
# The spec checkout the tests read (zed_tests::spec::locate, MERGE-spec-reads-map), by the rule
# tools/spec_groups.sh --dir prints. --trace names a read under it spec:<path>, relative to it,
# so the map of run-time reads tells which groups read the spec; strace names a directory by its
# real path, so the real path of the spec checkout is matched too.
spec_dir= spec_real=
if [ -n "$trace" ]; then
  spec_dir=$(tools/spec_groups.sh --dir)
  [ -z "$spec_dir" ] || spec_real=$(realpath -m -- "$spec_dir")
fi
export root out cores run_kind cov trace spec_dir spec_real
# Prints the paths the strace output $1 (strace -f -y -e trace=%file,getdents64) names under the
# checkout, relative to it, and under the spec checkout ($spec_dir above), as spec:<path>
# relative to it, sorted: for a call of the *at family each path after a directory
# strace decoded (`AT_FDCWD</dir>, "path"`, or `3</dir>, ""` for the directory itself), joined to
# it unless absolute; for a directory listing its directory; for any other call (execve, access,
# chdir...) its first path, which must be absolute, as strace does not show the cwd a relative
# one would be resolved against. A relative one of those, and the checkout's .git (a test that
# runs git reads the files through the object store, and its answers change with each commit),
# are printed as `*`: the piece may have read anything. The checkout's root itself is `.`. In the
# spec checkout its root is spec:. and its .git spec:*. Other paths are left out.
# Paths are normalized without following symbolic links, so a/../b is b.
trace_reads() {
  awk -v root="$root" '
    / <\.\.\. [a-z_0-9]+ resumed>/ { next }
    match($0, /^[0-9]+ +([a-z_0-9]+)\(/, m) {
      call = m[1]; rest = substr($0, RSTART + RLENGTH)
      if (call == "getdents64" || call == "getdents") {
        if (match(rest, /^[0-9]+<([^>]*)>/, d)) print d[1]
        next
      }
      if (call ~ /at2?$/ || call == "statx") {
        while (match(rest, /<([^>]*)>, "([^"]*)"/, a)) {
          p = a[2]
          print (p == "" ? a[1] : p ~ /^\// ? p : a[1] "/" p)
          rest = substr(rest, RSTART + RLENGTH)
        }
        next
      }
      # A relative path here is printed as root/.git, which the last step prints as `*`.
      if (match(rest, /^"([^"]*)"/, q) && q[1] != "") print (q[1] ~ /^\// ? q[1] : root "/.git")
    }' "$1" | sort -u | xargs -r -d '\n' realpath -m -s -- |
    awk -v root="$root" -v spec="$spec_dir" -v real="$spec_real" '
      # under(d): the path is the directory d or lies in it; rest(d): the path relative to d.
      function under(d) { return d != "" && index($0 "/", d "/") == 1 }
      function rest(d) { p = substr($0, length(d) + 2); return p == "" ? "." : p }
      under(spec) || under(real) {
        p = under(spec) ? rest(spec) : rest(real)
        print (p ~ /^\.git(\/|$)/ ? "spec:*" : "spec:" p)
        next
      }
      under(root) { p = rest(root); print (p ~ /^\.git(\/|$)/ ? "*" : p) }' | sort -u
}
# A piece writes its output to the file of its slot, which the next piece in that slot overwrites,
# so a passing piece leaves no log and nothing is deleted. A failed piece's output is copied to its
# log; a passing piece empties a log left by an earlier failed run, so every log with contents is
# of a piece that failed in the last run that ran it.
piece() {
  name=$1 dir=$2
  shift 2
  asked=${EPOCHREALTIME//[!0-9]/}
  scratch=$out/slot-$slot.out
  log=$out/$name.log
  piece_limit "$cores"
  start=$(date +%s%N)
  wait=$(((start / 1000 - asked) / 1000))
  # %p: a test may run other programs of the build, each writing a profile of its own.
  [ -z "$cov" ] || export LLVM_PROFILE_FILE=$cov/$name-%p.profraw
  # A benchmark's run at 8n has max(this limit, 10.5 × t1) from its own start, t1 the time of
  # its run at n (author P214, A160), and the rest of it this limit, phase by phase:
  # tools/bench_limit.sh reads the phases from the file zed_tests::scaling writes, and leaves
  # the largest limit of any phase there, printed as the piece's limit. A piece of several
  # phases may so take longer in all than the limit it prints.
  if [ "$run_kind" = test ]; then
    bound=(timeout -k 5 "$limit")
  else
    bound=("$root/tools/bench_limit.sh" "$limit" "$out/slot-$slot.limit")
  fi
  # --trace: strace stops a process only at the calls it traces (--seccomp-bpf), and its output
  # goes to a file of the slot, emptied once read, like $scratch.
  tracer=()
  [ -z "$trace" ] || tracer=(strace -f -qq --seccomp-bpf --kill-on-exit -y -e signal=none
    -e trace=%file,getdents64 -o "$out/slot-$slot.strace")
  (cd "$root/$dir" && CARGO_MANIFEST_DIR=$root/$dir \
    systemd-run --user --scope --quiet --same-dir --slice=zedtests.slice \
    "${bound[@]}" "${tracer[@]}" "$@" >"$scratch" 2>&1)
  rc=$?
  if [ -n "$trace" ]; then
    trace_reads "$out/slot-$slot.strace" >"$trace/${name//\//_}.reads"
    : >"$out/slot-$slot.strace"
  fi
  ms=$((($(date +%s%N) - start) / 1000000))
  if [ "$run_kind" != test ]; then
    raised=
    read -r raised <"$out/slot-$slot.limit"
    [ -z "$raised" ] || [ "$raised" -le $((limit * 1000)) ] || limit=$(((raised + 999) / 1000))
  fi
  echo "$name rc=$rc ${ms}ms load=$load limit=${limit}s wait=${wait}ms $(grep -E '^test result' "$scratch" | tail -1)"
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
# piece_limit comes from tools/lib.sh; a piece runs in a new bash, which has only what is exported.
export -f piece trace_reads piece_limit
# A test that builds executables (zed_native::link) keeps each one and links it again only when
# an input of its link changed (crates/zed-native/src/link.rs, `kept`). The runtime archive is
# one of those inputs, and Cargo builds it again after any change to zed-native or a crate under
# it, zed-kernel and zedc among them; the next run of such a test then links every executable
# again, about 1.5 s each, most of it GNU ld reading the 207 MB archive: the l01_36a piece took
# 13.4 s instead of 2.6 to 3.0 s at load 44 to 51, and once ran past its limit of 24 s
# (TEST-runtime-build-in-piece). So when the runtime archives beside the test binaries differ
# from those named in <base>/runtimes, published by the last run that made the links, the selected pieces of the step folders whose sources call
# the linker run first, with no limit, as part of the build: the links are made there, and the
# pieces run again in the slots, where they find them kept. Their results are not counted; a
# piece that fails there fails again in the slots and is reported there.
warm() {
  name=$1 dir=$2
  shift 2
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
if [ "$runtimes" != "$(cat "$logbase/runtimes" 2>/dev/null)" ]; then
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
    xargs -P "$jobs" --process-slot-var=slot -L 1 bash -c 'warm "$@"' _ <"$out/linking"; then
    printf '%s\n' "$runtimes" >"$out/runtimes"
    publish "$out/runtimes" runtimes
  fi
fi
: >"$out/bench.log"
xargs -P "$jobs" --process-slot-var=slot -L 1 bash -c 'piece "$@"' _ <"$out/pieces" | tee "$out/summary"
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
# The output of each failed piece, printed here so that a copy of this run's output names the
# tests that failed and why: the piece's log goes with the worktree, so a failure seen once under load and passed on every rerun was known only
# as a piece name (FLAKE-l01-39-scaling-unnamed). A benchmark piece, one test run with
# --nocapture, prints its whole log. A correctness piece prints libtest's lines for the tests
# still running past 60 s and its account of the failures, from the line `failures:` to the end
# (each failed test's captured output and panic, then their names); when there is none (a piece
# stopped by its limit or a signal, or a crash), the last 40 lines, as a failed build prints.
# Before those it prints the seed lines of the piece's random tests (`<test>: seed <n>;
# ZED_TEST_SEED=<n> repeats this run`, from zed_tests::seed): they go to standard error past
# libtest's capture, so they stand before `failures:` in the log, and without them a failure
# seen once could not be repeated (TOOL-merge-push-seed-in-dump: the step 3 output of satred1b,
# 2026-11-19T17:22:46Z, named a failed draw of pendants with no seed).
grep -v 'rc=0 ' "$out/summary" | while read -r name _; do
  echo "---- failed piece $name (its output: $out/$name.log) ----"
  if [ "$run_kind" != test ]; then
    cat "$out/$name.log"
  else
    grep -a -E '; ZED_TEST_SEED=[0-9]+ repeats this run$' "$out/$name.log"
    grep -E '^test .* has been running for over' "$out/$name.log"
    if grep -q '^failures:$' "$out/$name.log"; then
      sed -n '/^failures:$/,$p' "$out/$name.log"
    else
      tail -40 "$out/$name.log"
    fi
  fi
done
echo "pieces: $(wc -l <"$out/summary"), failed: $bad, load: $load, cores: $cores"
[ -z "$cov" ] || echo "coverage profiles in $cov; a scaling verdict of this run is not to be relied on"
[ "$bad" = 0 ]
