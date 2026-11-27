#!/bin/bash
# Runs the tests in pieces, one test binary, step folder, module or slow test each, each under a
# limit of 20 s (more under load, below), and prints a line per piece as it ends. Usage, from a
# checkout's root:
#   tools/run_tests.sh [--full] [--bench] [--each-test] [--only <ERE>] [--except <ERE>] [--doc] [--list] [--reuse-table] [--logs <dir>] [--cov <dir>] [--trace <dir>] [jobs]
#   tools/run_tests.sh [--full] [--bench] --pieces <file> [--doc] [--logs <dir>] [--cov <dir>] [--trace <dir>] [jobs]
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
# --except <ERE> does not run a selected piece whose name, or that name with its binary's hash
# taken off, matches; each is noted on standard error, and a second --except adds to the first.
# tools/main_watch.sh passes it for a piece its known list marks skip, one too costly to run while
# it fails (TOOL-main-watch-start-green: rung2 at n = 600 held 67 to 71 GB a run).
# --short-groups prints the groups that have a short- piece and runs nothing. The
# short-addresses build is made only when a short- piece is selected, in a clone of build/cargo kept in build/short-clone from run to run;
# such a run must go through /home/luke/Work/wt/zrun, and --short-clone-remove deletes the clone
# (through zrun too) and runs nothing. --doc adds the check that the documentation of the whole
# workspace builds, which is off by default; --no-doc is accepted and changes nothing. Every run
# but --list and --pieces checks the documentation of each package whose `///` or `//!` lines the checkout
# changes since origin/main, or whose doc links an item the checkout renames, deletes, makes
# private or puts behind a cfg (tools/check_changed_docs.sh). --list builds what the selection
# needs, prints the names of the selected pieces and runs nothing.
# --pieces <file> runs the pieces of <file>, lines `<name> <directory> <binary> <arguments>` as an
# earlier run wrote them to the file pieces of its log directory (a --list run among them), and
# nothing else: no cargo metadata, no build, no listing of the binaries, no selection and no
# check of the changed documentation. tools/merge_check.sh lists once and runs the listed pieces
# in chunks this way; before, each chunk was a run with --only and --except that built, listed
# and selected its whole groups again, so a group cut into c chunks was listed c times, and a
# chunk spent 9.6 s on average and up to 30 s on that before its first piece (56 chunks at load
# 75, MERGE-full-run-split, 2026-11-20). The caller has built the binaries and runs the check of
# the changed documentation. A short-addresses piece is refused: its binary lies in the clone of
# the run that listed it, unmounted when that run ended.
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
features=--features=zed-tests/spec full_suite= only= except= list= reuse= logs= doc= jobs=6 clone_remove= run_kind=test each_test= cov= trace=
short_groups= skip_other_kind= pieces_from=
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
    --except)
      if [ $# -lt 2 ] || [ -z "$2" ]; then
        echo "--except needs a non-empty extended regular expression"
        exit 2
      fi
      except=${except:+$except|}$2
      shift
      ;;
    --doc) doc=1 ;;
    --no-doc) ;;
    --list) list=1 doc= ;;
    --reuse-table) reuse=1 ;;
    --pieces)
      if [ $# -lt 2 ] || [ -z "$2" ]; then
        echo "--pieces needs a file of pieces"
        exit 2
      fi
      pieces_from=$2
      shift
      ;;
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
      echo "unknown argument: $1 (usage: tools/run_tests.sh [--full] [--bench] [--each-test] [--only <ERE>] [--except <ERE>] [--skip-other-kind] [--doc] [--list] [--reuse-table] [--pieces <file>] [--logs <dir>] [--cov <dir>] [--trace <dir>] [--short-clone-remove] [--short-groups] [jobs])"
      exit 2
      ;;
  esac
  shift
done
if [ -n "$reuse" ] && [ -z "$list" ]; then
  echo "--reuse-table needs --list"
  exit 2
fi
if [ -n "$pieces_from" ]; then
  if [ -n "$list$reuse$only$except$each_test" ]; then
    echo "--pieces runs the pieces of its file and selects none: it takes no --list, --reuse-table, --only, --except or --each-test"
    exit 2
  fi
  [[ $pieces_from == /* ]] || pieces_from=$PWD/$pieces_from
  if [ ! -s "$pieces_from" ]; then
    echo "--pieces: $pieces_from names no piece"
    exit 2
  fi
  if awk '$3 ~ /\/short-clone\// { found = 1 } END { exit !found }' "$pieces_from"; then
    echo "--pieces: $pieces_from names a short-addresses piece, whose binary lies in the clone of the run that listed it; select it with --only"
    exit 2
  fi
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
if [ -n "$except" ]; then
  { [[ x =~ $except ]]; } 2>/dev/null
  if [ $? = 2 ]; then
    echo "--except: not a valid extended regular expression: $except"
    exit 2
  fi
fi
if [ -n "$only" ]; then
  { [[ x =~ $only ]]; } 2>/dev/null
  if [ $? = 2 ]; then
    echo "--only: not a valid extended regular expression: $only"
    exit 2
  fi
  # A run prints the pieces of a library's unit tests with the binary's hash,
  # zedc_presburger-78e0977b8abc3f4c::<path>, and the binaries are chosen by group before the
  # build (wants, below), where the hash is not known; such a name copied into --only selected
  # nothing (TOOL-short-piece-test-filter: a seed test of zedc_presburger seen failing in a
  # --full run was run by hand). So a hash of cargo's form, - and 16 hexadecimal digits, after a
  # name and before anything but more of a name, is taken out: the pattern then selects what
  # <group>::<path> does, the hash of today's binary or of an older one. No group, step or test
  # name holds a - followed by 16 hexadecimal digits (groups are cargo's target names with each
  # - made _; the other names are Rust identifiers and step folders, short-<group> and
  # full-<folder>), so nothing else is changed.
  while [[ $only =~ ^(.*[A-Za-z0-9_])-[0-9a-f]{16}([^A-Za-z0-9_-].*)?$ ]]; do
    only=${BASH_REMATCH[1]}${BASH_REMATCH[2]}
  done
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
# A run unmounts its clone lazily (umount -l), and so does a run unmounting the mount of an ended
# run: a process may still use the clone when its run ends (TOOL-short-clone-umount-busy). A run
# whose process group is sent TERM during the short-addresses build (a tool's time limit) sees
# cargo end and runs its EXIT trap while the rustc cargo started is still exiting; a plain umount
# then printed "umount: .../short-clone: target is busy." and left the mount (reproduced
# 2026-11-20 by sending TERM to the group 8 and 15 s into the clone's build, both times; the
# group had no process left 0.5 s later). A lazy unmount takes the mount out of the mount table
# at once, and the kernel ends it when its last user ends; until then the kernel still refuses
# another mount of the upper layer, with EBUSY (measured 2026-11-20, Linux 7.3.3, in a user
# namespace: a mount with index=on refused while a process held a file of a lazily unmounted one
# open, and accepted once it ended). So the clone still has one writer at a time, and a run
# whose mount is refused while no mount of the clone is in sight waits for that last user.
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
# with no process <pid>, lazily, as a process of the ended run may still use it (see above, at
# TOOL-short-clone-umount-busy), or one at build/short-clone/cargo, where a run before
# NO-LOCKS-optimistic mounted it, that no process is using (umount refuses one in use). Prints
# the directory of each mount left, the runs still using the clone. A pid used again by another
# process since the run ended keeps its mount until that process ends; the clone waits that long.
unmount_dead_short_clones() {
  local m pid
  for m in $(short_clone_mounts); do
    if [[ $m =~ -([0-9]+)/short-clone$ ]]; then
      pid=${BASH_REMATCH[1]}
      if [ "$pid" != $$ ] && [ ! -d "/proc/$pid" ] && umount -l "$m"; then
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
  local m said= said_detached= free=
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
      if [ -z "$free" ]; then
        free=1
        continue
      fi
      # Refused twice with no mount of the clone in sight. With EBUSY a mount unmounted lazily
      # by an ended run is still in use by a process of that run, and the kernel ends it when
      # that process ends; any other refusal stops the run. For EBUSY util-linux's mount prints
      # "overlay already mounted on <lowerdir>." here, and "overlay already mounted or mount
      # point busy." for an overlay in a scratch directory (both measured 2026-11-20), so the
      # refusal is read by "already mounted".
      if ! grep -q 'already mounted' "$out/short-clone.err"; then
        cat "$out/short-clone.err"
        echo "The short-addresses clone of build/cargo could not be mounted."
        return 1
      fi
      [ -n "$said_detached" ] ||
        echo "Waiting for the processes of an ended run that still use the short-addresses clone to end."
      said_detached=1
      sleep 2
      continue
    fi
    free=
    [ -n "$said" ] || echo "Waiting for the run that has the short-addresses clone mounted at" $m "to end."
    said=1
    sleep 2
  done
}
# Deletes the run's copy of the build, <log directory>/cargo (make_run_copy, below). The copy is
# first renamed into the folder build/run-copy-dropped, under the name of the run's log
# directory, and then that whole folder is deleted, so the delete names its target in full (the
# author's rule) and needs no lock (NO-LOCKS). Runs of one checkout that end at the same time
# share the folder: each rename is atomic and under a name of its own, and each run's delete
# takes every entry it finds, so the last delete leaves none, a leftover of a run killed while
# deleting included. A run whose rename finds the folder gone (another run's delete took it
# after this run made it) makes it again and renames again; that repeats only while other runs'
# deletes keep ending in between, each of which has made progress. A delete that meets an entry
# renamed in after it read the folder says it could not remove the folder; the delete of the run
# that renamed it in takes it. In this namespace the folders
# of the copy that the pieces mounted the build's folders on are empty, since each piece mounted
# them in a namespace of its own, and --one-file-system keeps rm out of any mount.
drop_run_copy() {
  [ -n "$out" ] && [ -e "$out/cargo" ] || return 0
  while :; do
    if [ -L /home/luke/Work/wt/.build-root/build/run-copy-dropped ]; then
      echo "/home/luke/Work/wt/.build-root/build/run-copy-dropped is a symbolic link; it is left in place."
      return 1
    fi
    mkdir -p /home/luke/Work/wt/.build-root/build/run-copy-dropped &&
      mv -T "$out/cargo" "/home/luke/Work/wt/.build-root/build/run-copy-dropped/${out##*/}" && break
    if [ ! -e "$out/cargo" ] || [ -e /home/luke/Work/wt/.build-root/build/run-copy-dropped ]; then
      echo "The run's copy of the build, $out/cargo, could not be renamed for deletion; it is left with the run's logs."
      return 1
    fi
  done
  rm -rf --one-file-system --preserve-root=all /home/luke/Work/wt/.build-root/build/run-copy-dropped
}
# What a run undoes as it ends, however it ends: it unmounts its short-addresses clone, lazily,
# as a process the run started may still use it (TOOL-short-clone-umount-busy), and deletes its
# copy of the build.
at_exit() {
  ! mountpoint -q "$out/short-clone" || umount -l "$out/short-clone"
  open_short_clone_work
  drop_run_copy
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
# test_list, list_binary, piece_tests and split_benchmarks are in tools/lib.sh, sourced above, so
# that `tools/test_run_tests.sh split` tests split_benchmarks on fake binaries
# (TOOL-split-benchmarks-forks).
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
  local k group step name dir bin args first t stepname
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
    # A piece of a binary whose step folder has another name (deep_heap in l01_36_cranelift) is
    # named <group>::<test>, and matches as <step>::<test> too, without its group.
    stepname=$name
    [ "$group" = "$step" ] || stepname=${name#"$group::"}
    if ! selected "$group" "$name" && ! selected "$step" "$stepname"; then
      # A piece of a binary named with its hash, not selected as a whole, still gives each of
      # its tests whose <group>::<test> --only matches as a piece of its own, run as with
      # --each-test, so that --only '^zed_kernel::btree::' runs those unit tests of the library
      # (TOOLS-only-lib-pieces). Only a pattern with :: can match such a name, so only then is
      # the binary's list read (once per binary, as above). A benchmark is a piece per test
      # already, so this is for correctness pieces alone. A short-addresses piece, named
      # short-<group> after its whole binary (group, step and name the same), is split the same
      # way, so that --only '^short-zed_kernel::treap_set::' runs those tests of the
      # short-addresses build alone (TOOL-short-piece-test-filter: until then such a pattern
      # built the clone and selected nothing). Its binary lies in this run's clone, mounted
      # until the run ends, so a --reuse-table run, whose table names the clone of an earlier
      # run, cannot list its tests and selects none of them. A module piece of a split step,
      # <group>::<module> running `<module>::`, is split the same way when --only holds the text
      # <group>:: itself, so that --only '^l01_26_type_resolution::random::a_wrong_claim_is_caught'
      # runs that one test, as tools/time_tests.sh needs (TOOLS-time-tests-fixes: it printed NO
      # PIECE MATCHES). That text is the condition, and not a pattern that could match such a
      # name, so that only the binaries --only names are listed, not every split step's; a step
      # that is one piece named <group> is not split, so <group>:: alone still selects nothing
      # there and check_terms says how to select the step (TOOL-run-tests-empty-filter). A piece
      # that runs one test `--exact` is that test already, matched or not by selected above;
      # listing each such piece's tests cost an awk a piece, 15 s for the 850 pieces of l01_26 at
      # load 64, where the old selection took 3 s.
      [[ $k == test && $only == *::* &&
        ($name =~ ^$group-[0-9a-f]+(::|$) || ($name == short-* && $name == "$group") ||
        ($name == "$group::"* && $args != --exact* && $only == *"$group::"*)) ]] || continue
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
  # --except: the selected pieces it matches are not run, each noted on standard error. A piece
  # named with its binary's hash (zed_kernel-744b8b7231e6eb90::btree::bench::<test>) matches by
  # that name or by the name without the hash, as for --only. $out/chosen keeps them, so a term of
  # --only that selected only such pieces still counts as selecting (check_terms).
  if [ -n "$except" ]; then
    local line n
    while IFS= read -r line; do
      n=${line%% *}
      if [[ $n =~ $except ]] || { [[ $n =~ ^([A-Za-z0-9_]+)-[0-9a-f]+(::.*)?$ ]] &&
        [[ ${BASH_REMATCH[1]}${BASH_REMATCH[2]} =~ $except ]]; }; then
        echo "--except: not run: $n" >&2
      else
        printf '%s\n' "$line"
      fi
    done <"$out/pieces" >"$out/pieces.kept"
    mv -T "$out/pieces.kept" "$out/pieces"
  fi
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
  local t g s n x m name saved=$only bad=
  local -A have
  while read -r g s n; do
    have[$n]=1
    for x in "$g" "$s"; do
      have[$x]=1
      # As in select_pieces: <group>::<test> matches as <step>::<test> too.
      m=$n
      [ "$x" = "$g" ] || [ "$g" = "$s" ] || m=${n#"$g::"}
      [[ $m == "$x"* ]] || have[$x::$m]=1
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
        m=$n
        [ "$g" = "$s" ] || m=${n#"$g::"}
        selected "$g" "$n" || selected "$s" "$m" || continue
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
# --pieces: the pieces are those of its file, and the run goes straight to them; everything from
# here to the end of this if, cargo metadata, the build, the listing and the selection, is for a
# run that chooses its pieces (the block is not indented, to keep the lines it holds as they were).
if [ -n "$pieces_from" ]; then
  cp "$pieces_from" "$out/pieces" || exit 1
else
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
# pieces listed for nothing, which costs time but drops no test. The text before the first ::
# must match a part of the name that is not empty: an alternative that starts with ::, as
# ::<test>$, matched the empty end of every name, so it built every binary and asked for the
# short-addresses build, which a run outside zrun refuses (FAIL-run-tests-wants-colon-prefix).
# Such an alternative names no binary, and the run stops below with the hint.
wants() {
  [[ $2 =~ $1 || $3 =~ $1 ]] && return 0
  [[ $1 == *::* ]] || return 1
  local end="${1%%::*}$"
  { [[ $2 =~ $end ]] && [ -n "${BASH_REMATCH[0]}" ]; } ||
    { [[ $3 =~ $end ]] && [ -n "${BASH_REMATCH[0]}" ]; }
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
# whole name short-zed_kernel only, and such a run built nothing and listed no piece. The
# piece's tests are then selected one by one in select_pieces (TOOL-short-piece-test-filter).
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
  trap at_exit EXIT
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
# l01_23 group_oracle ran 20.0 to 36 s against its limit of 20 s: twelve order sweeps of 500
# seeds took 6.9 to 8.9 s each alone, every other test under 1.3 s (b22-mem40, 2026-11-22). The
# sweeps are the module cell_order_sweep now, each test a piece (TEST-group-oracle-seed-split).
# l01_28_staging took 46 to 65 s whole at load 41 and more, 28 s of it the test of four shapes
# 100,000 deep on a small stack and 20 s the test of lets of built values (alone, load 41); those
# are now four tests and two. Each module is a piece, and each test of scaling and dag
# (2026-11-12, TESTS-split-l01_28-staging).
# m0_12_refusal_census reads 120 units of programs.txt, 45 s together at load 41 and 18 s of it
# one unit; each of its tests is a piece (2026-11-12, REFUSAL-census-now). Its module seeds was
# one piece of eight tests, 30 s together at load 28 (170 s of CPU), past its limit under load;
# its units are dealt into 20 tests now, each a piece (2026-11-20, FLAKE-m0_12-seeds-load).
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
# l01_39_scope_relations xst ran past its limit of 20 s alone at load 5 once the tests of
# S4-interval-boxes joined it (s4_holed, s4_names, s4_model: 61, 232 and 103 s in a debug build
# at load 2, against 576 s for all of xst). Each module of xst is a piece, and each test of the
# three S4 modules (2026-11-22, S4-interval-boxes).
# l08_02_remaps ran past its limit of 29 s at load 11.5 (30.1 s, b22-misc8's merge check,
# 2026-11-23). Without benchmarks it took 7.1 s whole at 8 threads on l43 at load 0, and its 227
# tests one by one 41.4 s: empty 12.0 s (77 tests), rules 8.0 s (54), recursion 7.7 s (7, of
# which the chain of 8000 maps on a 2 MiB stack is 6.8 s), kernel 5.5 s (39), collisions 4.8 s,
# moves 1.8 s, three_way 0.8 s, kept 0.8 s. Each module is a piece
# (FAIL-l08-02-remaps-piece-past-20s, b22-tests7).
split="
  l01_08_parser l01_16_elaboration l01_16_elaboration::scaling
  l01_23_groups_and_refusals l01_23_groups_and_refusals::r6_reduction
  l01_23_groups_and_refusals::cell_order_sweep
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
  l01_39_scope_relations::xst l01_39_scope_relations::xst::s4_holed
  l01_39_scope_relations::xst::s4_names l01_39_scope_relations::xst::s4_model
  l01_39a_bit_words l01_39a_bit_words::scaling
  l25_08_mutate l25_08_mutate::scaling
  m0_12_refusal_census m0_12_refusal_census::seeds
  l08_02_remaps
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
# The binary's other piece skips each of these with `--skip <test>`, which libtest matches
# anywhere in a name (`--exact` cannot be used there: it would apply to `--skip bench::` too). So
# a test whose name holds one of these is skipped as well and needs a line here of its own: the
# second half of the random test of the boolean equation solver was run by no piece from its
# split (b9fc80f63) until it was added (kernel21, 2026-11-20).
# zedc_preimage's piece took 41.9 s at load 65 against its limit of 38 s: its test of joins of
# random cases (c7fd27fe8, 2026-11-19) took 12.3 s alone at load 41, half the CPU time of the
# binary's 98 other tests together (24 s, each of the others 1.2 s or less). It is four tests of
# 30 histories, 3.0 to 3.9 s each alone at load 52, each a piece (TEST-preimage-unit-piece-load,
# 2026-11-20).
# zedc_types's piece ran past its limit of 33 s at load 52 (merge of
# PROOF-flat-vars-instantiated-clash, 2026-11-20) and took 27.67 s alone at load 58: its 143
# correctness tests take 39.3 s of CPU, 32.3 s of it in the eight below of 1 s or more (9.5,
# 8.0, 4.2, 3.7, 2.7, 2.0, 1.1 and 1.1 s, alone at load 47 to 72), the other 135 together
# 7.1 s. Each of the eight is a piece, and so is the test of the index of arrows on wider
# shapes (0.7 s), whose name holds that of the index of arrows, which the other piece skips
# (TEST-zedc-types-lib-split, 2026-11-20). The slowest, of the index of functions, still took
# 30.1 s at load 64 against 41 s as a piece, so it is split into four parts of 750 cases.
# zedc_presburger's other piece ran past its limit of 23 s at load 37 (rc=124, 23106 ms, the
# merge check of PERF-varfacts-held-shared-dag, 2026-11-21). Each of its 514 tests alone, at load
# 29 to 30 (tools/time_tests.sh, 2026-11-22): the 504 not listed here took 164 s of wall time
# together, 83 s of it in the 29 below: the test of probes in every order 7.5 s, the two tests of
# private quotients 5.2 and 3.9 s, the test of every split of the moduli 2.5 s and the 25 tests of
# every writing at one seed 2.0 to 4.3 s each (65 s together). Each is now a piece, which leaves
# the other piece 81 s of wall time spread over its threads (TEST-presburger-unit-piece-probe-order).
# zed_kernel's piece took 22.4 s at load 13.9 on l43 against its limit of 20 s (seen by kept1,
# checkwalk5 and misc7 on main; FAIL-zed-kernel-unit-piece-past-20s). Each of its 731 tests alone
# there at load 10.6 to 12.2 (tools/time_tests.sh, 2026-11-23): 119.6 s together, 17.8 s of it in
# the two random tests of the boolean equation solver above and 44.5 s in the six below (14.0,
# 7.8, 7.4, 6.0, 4.9 and 4.4 s); the other 723 take 57.3 s together. Each of the six is a piece,
# and no other test's name holds one of their names.
# zed_kernel's piece still came near its limit (FAIL-zed-kernel-piece-near-limit). The piece
# with --report-time on l41 (8 threads, load 5.2 to 5.5, b22-scale1 batch b26, 2026-11-25) took
# 13.2 and 13.3 s of wall time, of which the test of valuations from the top took 10.3 and
# 10.5 s; the next slowest took 2.9 s. That one test bounds the piece's wall time, so it is a
# piece, as it is for short-zed_kernel (short_alone below). No other test's name holds its name.
# zedc_check's piece stopped at its limit alone (rc=124, 20059 ms, on hm1, 8 cores, load 4.0,
# b22-checkrest8, 2026-11-22). Each of its 183 tests alone on hm1 (tools/time_tests.sh, load 1.2
# to 1.6): the 30 below took 133 s together, 1.0 to 7.8 s each (the slowest
# landing6_battery_top), and the other 153 took 6.0 s together. Each of the 30 is now a piece
# (FAIL-four-pieces-over-20s-alone-on-main). b22-tests7 found the same 30 on l43 (12 cores,
# 2026-11-22, FAIL-zedc-check-lib-timeout): whole, the piece took 22.8 s with 12 threads.
# zedc_presburger's other piece took 8.6 s on v5e5 at load 7.5 on main 8a460acb8 and ran past
# its 20 s limit with the nine tests of the factored products solver added (b22-factored2,
# 2026-11-24): its brute-force families, the cone rule and the BMM reduction each test thousands
# of small systems through `satisfiable`, and the wlgrow tests build inputs of 10,000 terms. Each
# is a piece; no other test's name holds one of their names.
# zedc_presburger's other piece still stopped at its limit alone on hm5 (rc=124 at 20 s, load
# 2.7, FAIL-zedc-presburger-lib-piece-20s-hm5). The whole lib without benchmarks on hm2 (8
# cores, b22-small15, 2026-11-24, --report-time): the tests of the other piece took 190.6 s
# together, 16.4 s of it in the test of the step mutants of the plane hull, which ran all 1500
# sequences after the first failure had caught each mutant and now stops there (0.14 s, same
# verdict). The ten below took 4.1 to 7.0 s each, 51 s together; each is a piece, which leaves
# the other piece about 123 s, 15.4 s on 8 cores. No other test's name holds one of their names.
# The whole lib without benchmarks on a v5e VM (8 threads, b22-free2 job prof30, 2026-11-26,
# --report-time, FAIL-s4-model-near-limit): the 565 tests of the other piece took 52.7 s together,
# and the slowest, of random formulas with and without the plain shortcut, 5.8 s, the next 2.0 s.
# That one test set the piece's wall time, so it is a piece; no other test's name holds its name.
alone="
  zedc_types::ty::tests::functions_met_through_the_index_are_those_met_pair_by_pair_part_1
  zedc_types::ty::tests::functions_met_through_the_index_are_those_met_pair_by_pair_part_2
  zedc_types::ty::tests::functions_met_through_the_index_are_those_met_pair_by_pair_part_3
  zedc_types::ty::tests::functions_met_through_the_index_are_those_met_pair_by_pair_part_4
  zedc_types::ty::tests::a_shape_held_as_is_out_of_written_order_gives_no_wrong_verdict
  zedc_types::ty::tests::a_generic_arrow_fits_where_some_binding_of_its_variable_fits
  zedc_types::ty::tests::pinned_shapes_are_those_of_the_rule_of_one_shape
  zedc_types::ty::tests::bound_shapes_agree_with_trying_every_shape
  zedc_types::ty::tests::the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows
  zedc_types::ty::tests::the_index_of_arrows_gives_the_verdict_of_every_set_of_arrows_on_wider_shapes
  zedc_types::ty::tests::tuples_met_and_subtracted_through_the_index_are_those_of_every_pair
  zedc_types::ty::tests::tuples_that_hold_a_value_through_the_index_are_those_of_every_tuple
  zedc_preimage::preimage::tests::summaries_read_again_give_what_reading_the_term_again_gives_seed_7776978274844439420
  zedc_preimage::product::tests::projected_entries_after_joins_of_random_cases_hold_at_the_joins_snapshot_part_1
  zedc_preimage::product::tests::projected_entries_after_joins_of_random_cases_hold_at_the_joins_snapshot_part_2
  zedc_preimage::product::tests::projected_entries_after_joins_of_random_cases_hold_at_the_joins_snapshot_part_3
  zedc_preimage::product::tests::projected_entries_after_joins_of_random_cases_hold_at_the_joins_snapshot_part_4
  zed_kernel::types::bes::tests::decide_agrees_with_the_game_on_systems_drawn_at_random
  zed_kernel::types::bes::tests::decide_agrees_with_the_game_on_systems_drawn_at_random_second_half
  zed_kernel::poly::tests::one_decide_spends_at_most_four_budgets
  zed_kernel::types::bdd::set::tests::tied_sets_and_ids_compare_each_key_a_few_times
  zed_kernel::poly::roots::tests::the_search_is_bounded_on_families_that_defeat_the_cuts
  zed_kernel::eval::binder_tests::reads_lies_between_the_tree_walk_and_the_shared_bound_on_deeply_shared_terms
  zed_kernel::types::bdd::tests::a_chain_joined_at_once_is_the_chain_joined_literal_by_literal
  zed_kernel::types::empty::tests::random_types_agree_with_membership_on_a_finite_set_of_values
  zed_kernel::num::tests::valuations_from_the_top_agree_with_the_tests_on_the_way_up
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
  zedc_presburger::presburger::probe_order::probe_leaves_the_same_parts_in_every_order
  zedc_check::check::r10_tests::landing5_chain_decode_grid
  zedc_check::check::r10_tests::landing6_battery::landing6_battery_held
  zedc_check::check::r10_tests::landing6_battery::landing6_battery_held_holding
  zedc_check::check::r10_tests::landing6_battery::landing6_battery_top
  zedc_check::check::r10_tests::landing6_battery::landing6_battery_top_nested
  zedc_check::check::r10_tests::landing6_battery::landing6_battery_top_shared
  zedc_check::check::r10_tests::landing8_first_seen_decodes_functions_nested_deep_on_a_small_stack
  zedc_check::check::r10_tests::r10_chain2_siblings_wide_skip_set_scale
  zedc_check::check::r10_tests::r10_forward_sweep_of_leaves_depths_and_siblings_agrees_with_e
  zedc_check::check::r10_tests::r10_generalize_runs_against_a_wide_skip_set_scale
  zedc_check::check::r10_tests::r10_m62_op_counts_per_link_f_and_lambda
  zedc_check::check::r10_tests::r10_m66_chains_f_2_to_60
  zedc_check::check::r10_tests::r10_m66_chains_f_61_to_79
  zedc_check::check::r10_tests::r10_m66_chains_f_80_to_92
  zedc_check::check::r10_tests::r10_m66_chains_f_93_to_100
  zedc_check::check::r10_tests::r10_m66_chains_lambda_2_to_36
  zedc_check::check::r10_tests::r10_m66_chains_lambda_37_to_47
  zedc_check::check::r10_tests::r10_m66_chains_lambda_48_to_53
  zedc_check::check::r10_tests::r10_m66_chains_lambda_54_to_58
  zedc_check::check::r10_tests::r10_m66_chains_lambda_59_to_65
  zedc_check::check::r10_tests::r10_m66_chains_lambda_66_to_71
  zedc_check::check::r10_tests::r10_m66_chains_lambda_72_to_76
  zedc_check::check::r10_tests::r10_m66_chains_lambda_77_to_80
  zedc_check::check::r10_tests::r10_m66_chains_lambda_81_to_84
  zedc_check::check::r10_tests::r10_m66_chains_lambda_85_to_87
  zedc_check::check::r10_tests::r10_m66_chains_lambda_88_to_90
  zedc_check::check::r10_tests::r10_m66_chains_lambda_91_to_93
  zedc_check::check::r10_tests::r10_m66_chains_lambda_94_to_96
  zedc_check::check::r10_tests::r10_m66_chains_lambda_97_to_98
  zedc_check::check::r10_tests::r10_m66_chains_lambda_99_to_100
  zedc_presburger::presburger::modular::r4_tests::private_quotients_match_enumeration_and_the_model_path
  zedc_presburger::presburger::modular::r4_tests::private_quotients_match_concrete_models_on_small_systems
  zedc_presburger::presburger::modular::r7_tests::every_split_of_the_moduli_decides_a_regime_as_testing_each_point_does
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_17553006884555075817
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_16338078841102802578
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_5302762248333478882
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_14168001171561652264
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_6791152268047101565
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_17216371871131204067
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_11367085356800913199
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_8124016268280057850
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_3465706508361208641
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_13310776365412627736
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_6248376677308887027
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_6356906811914704334
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_5480617911147767323
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_1018193249963013246
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_11124692055269125873
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_4748931191768879917
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_15275908352311422565
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_9041673993373821060
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_17109464074316566127
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_7570078408948364398
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_13472915549060986335
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_8136853401859909784
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_10746534589920032955
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_17656181055615743818
  zedc_presburger::presburger::exact::tests::every_writing_at_seed_11354000743705775971
  zedc_presburger::presburger::factored::tests::the_pairs_left_keep_the_verdict_on_random_tiny_instances
  zedc_presburger::presburger::factored::tests::the_pairs_left_keep_the_verdict_when_two_rows_conflict_on_a_variable
  zedc_presburger::presburger::factored::tests::the_pairs_left_keep_the_verdict_when_conflicting_rows_share_variables
  zedc_presburger::presburger::factored::tests::the_cone_rule_keeps_the_verdict_on_lists_shared_by_products
  zedc_presburger::presburger::factored::tests::the_residual_of_the_bmm_reduction_is_the_zeros_of_a_f
  zedc_presburger::presburger::factored::tests::the_worklist_of_wlgrow_g_scales
  zedc_presburger::presburger::factored::tests::the_pass1_and_worklist_of_wlgrow_scale
  zedc_presburger::presburger::factored::tests::no_pair_of_the_star_is_listed_and_the_work_scales
  zedc_presburger::presburger::factored::tests::the_cone_rule_is_exact_on_wide_coefficients
  zedc_presburger::presburger::extend::plane::tests::random_rows_give_the_integer_hull
  zedc_presburger::presburger::modular::scaled::tests::the_runs_agree_with_the_residue_sweep
  zedc_presburger::presburger::exact::tests::the_cover_gives_one_answer_in_every_order_of_the_parts
  zedc_presburger::presburger::exact::tests::quick_search_on_rows_of_one_atom_finds_a_point_wherever_one_exists
  zedc_presburger::presburger::exact::tests::the_covers_answer_alike_with_and_without_what_the_symbols_before_learned_part_1
  zedc_presburger::presburger::exact::tests::columns::random_classes_answer_as_with_their_columns_apart
  zedc_presburger::presburger::exact::tests::decomposable_formulas_project_to_the_values_of_their_points
  zedc_presburger::presburger::exact::tests::the_answers_do_not_depend_on_the_order_of_the_symbols_part_3
  zedc_presburger::presburger::exact::tests::the_covers_answer_alike_with_and_without_what_the_symbols_before_learned_part_0
  zedc_presburger::presburger::exact::tests::leaf_choices_over_a_polygon_of_many_true_edges_cost_log_of_them
  zedc_presburger::presburger::exact::tests::random_formulas_project_the_same_with_and_without_the_plain_shortcut
"
# Tests of short-zed_kernel (the zed-kernel unit tests of the short-addresses build) each run as a
# piece of their own, `--exact`, and skipped by the binary's other piece, as for alone above.
# short-zed_kernel as one piece ran past its 20 s limit on l43 (an l4 VM, 12 cores) twice, at load
# 5.4 and 5.5 (FARM-short-pieces-on-vm-tmpfs, 2026-11-22), so it ran on no VM. Each of its 713
# tests alone on v5e3 (24 cores, load 3.6; TEST-short-zed_kernel-split, 2026-11-22): 75.6 s
# together, the whole piece 11.7 s with 8 threads, its time set by its slowest test, 9.8 s. The
# six below took 9.8, 5.5, 5.4, 3.9, 3.8 and 3.5 s (32 s of the 75.6); the other 707 took
# 2.7 s or less each and 43.6 s together, about 5.5 s spread over 8 threads. The rest of the
# piece, then 774 tests, took 32.9 s with 8 threads on hm5 (8 cores, load 6.5 to 9.6) and 12.6 s
# on v5e1 (24 cores, load 11 to 15), set by its slowest test, 9.2 s on v5e1. The 17 after the six
# are those over 1.0 s there in the first of two runs: 9.2, 3.3, 3.2, 2.7, 2.5, 2.4, 2.3, 2.0, 2.0,
# 2.0, 1.5, 1.3, 1.2, 1.2, 1.1, 1.1 and 1.0 s (FAIL-short-zed-kernel-near-limit, 2026-11-25). No name here is part of another test's name
# but the first bes test's, which is the second's (both listed).
short_alone="
  poly::tests::one_decide_spends_at_most_four_budgets
  types::bes::tests::decide_agrees_with_the_game_on_systems_drawn_at_random
  types::bes::tests::decide_agrees_with_the_game_on_systems_drawn_at_random_second_half
  eval::binder_tests::reads_lies_between_the_tree_walk_and_the_shared_bound_on_deeply_shared_terms
  poly::roots::tests::the_search_is_bounded_on_families_that_defeat_the_cuts
  types::bdd::tests::a_chain_joined_at_once_is_the_chain_joined_literal_by_literal
  types::bdd::set::tests::tied_sets_and_ids_compare_each_key_a_few_times
  types::bdd::set::tests::consecutive_numbers_give_a_logarithmic_height
  types::bdd::set::tests::rows_sharing_a_prefix_or_a_suffix_give_a_logarithmic_height
  types::empty::tests::random_types_agree_with_membership_on_a_finite_set_of_values
  types::bdd::set::tests::consecutive_names_give_a_logarithmic_height
  types::bdd::set::tests::a_tied_map_of_rows_of_one_digest_compares_each_row_a_few_times
  num::tests::valuations_from_the_top_agree_with_the_tests_on_the_way_up
  types::bdd::set::tests::structured_digests_give_a_logarithmic_height
  types::empty::tests::overlaps_are_the_same_in_every_order_on_random_cells
  types::bdd::list::tests::blocks_chosen_against_a_fixed_hash_give_a_logarithmic_height
  types::empty::tests::the_check_of_a_list_witness_is_membership_on_chains_with_exits
  types::bdd::tests::connecting_keeps_the_value_of_the_unfolded_expression
  types::bdd::set::tests::colliding_digests_add_at_most_their_number_to_the_height
  types::bdd::set::tests::a_program_can_write_many_rows_of_one_digest
  types::empty::tests::a_list_witness_jumps_a_chain_of_tails_to_the_right_tail
  types::bdd::set::tests::chosen_literals_give_a_logarithmic_height
  types::bdd::tests::lists_agree_with_the_diagrams_apply_built
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
          # Each piece is named <group>::<test>, as a split step's pieces are: split_benchmarks
          # and --each-test name a piece's tests after the name's text before its first ::, and
          # the binaries of a run with --only are chosen by that text. Named <test> alone, a
          # benchmark of deep_heap was listed as bench::bench::<test>, which --only could not
          # select, and a correctness test as <test>::<test> (BENCH-listing-double-prefix).
          if tests=$("$p" --list --format terse); then
            for t in $(echo "$tests" | sed -n "s/: test$//p"); do
              echo "$g::$t tests $p --exact $t"
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
      # Each test of short_alone is a piece of its own, named short-zed_kernel::<test> and run
      # `--exact`, and the other piece skips them (see short_alone).
      short-zed_kernel)
        skips=
        for t in $short_alone; do
          echo "$n $n $n::$t crates/zed-kernel $p --exact $t"
          skips="$skips --skip $t"
        done
        echo "$n $n $n crates/zed-kernel $p --skip bench::$skips"
        ;;
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
# builds nothing. A --pieces run leaves it to its caller, which runs it once for all its runs.
# A run with ZED_DOC_CHECK_SKIP set leaves it out and prints the reason the variable gives:
# tools/test_run_tests.sh sets it, since its runs test the selection and running of pieces, not
# the docs (tools/test_check_changed_docs.sh tests the check, and tools/merge_check.sh runs it).
# Each run of a branch that changes doc lines in zedc-preimage and zedc-presburger made four doc
# builds of 2 to 8 s each, which do not stay fresh from run to run, and took 90 to 98 % of each
# part's time; fresh, copy, trace and nobus ran past their 60 s in merge_check step 0b
# (FAIL-rt-parts-cargo-lock: nobus 40, 69, 100 s alone on an idle l4 VM, 95 s of the 100 with a
# `cargo doc` running, b22-tests10, 2026-11-24).
if [ -n "${ZED_DOC_CHECK_SKIP-}" ]; then
  echo "The doc check of changed packages is skipped: $ZED_DOC_CHECK_SKIP"
elif [ -z "$pieces_from" ]; then
  tools/check_changed_docs.sh "$out/doc-changed.log" || exit 1
fi
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
# A benchmark measures one fixed draw of the treap priorities (crates/zed-collections/src/priority.rs,
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
# Every piece, and every link made before the timed pieces, runs under `capped`: in the systemd
# slice zedtests.slice (above) when a user bus answers, and otherwise with a data limit
# (RLIMIT_DATA, `ulimit -d`) of 112 GiB, the slice's MemoryMax, plus the machine's memory and
# swap once for each core (FARM-run-tests-systemd-run). A Colab VM, a docker container, has no user bus, and
# `systemd-run --user` there fails with "Failed to connect to bus", so every piece failed (found
# by b22-presburger4). tools/farm_run.sh puts a stand-in systemd-run first on PATH on a VM, which
# runs the piece with no limit; the probe below finds that stand-in, so there it is used instead.
# Why memory and swap are added: a native run reserves a stack as large as memory and swap
# together, writable (crates/zed-rt/src/stack.rs, `Stack::new` with no limit of `main`), which
# the data limit counts in full though it is not written; 112 GiB alone refused it on a machine
# with more than that (this one has 192 GiB). Why once for each core: the limit holds for the
# whole process, and a test binary runs its tests on as many threads as there are cores, each
# test with a native run holding its own stack. With memory and swap counted once, a fourth run
# at once passed the limit on a v5e (47 GiB, no swap, a limit of 159 GiB): `zedc` refused to
# start in l01_36_cranelift::hooks with "Cannot allocate memory" (b22-checkrest18, 2026-11-25,
# FAIL-nobus-data-limit-stacks). So each piece may write 112 GiB beyond the stacks of its
# threads. Test: zed_rt::stack::tests::a_stack_for_each_core_is_reserved_at_once, run with no
# user bus by tools/test_run_tests.sh nobus. The address space this reserves, cores times
# memory and swap, is far below the 2^47 bytes a process can address on x86_64. The sum is
# written with printf "%.0f": past 2^31 an awk's `print` may write it in exponent form (mawk
# 1.3.3 does), which `ulimit` refuses.
# Why the data limit and not the address-space limit (`ulimit -v`, `prlimit --as`):
# zed-alloc-count reserves 2^46 bytes of address space with no access before it meters
# (`RESERVED`, crates/zed-alloc-count/src/meter.rs), and zed-native 64 GiB (`FarApart`), which
# the address-space limit counts and so would refuse; the data limit counts only private
# writable mappings (Linux 4.7 and later), which those are not until they are used.
# Tradeoff: the slice caps the memory of every piece of every checkout together; the fallback
# caps each piece alone, so pieces side by side may together use more than the machine has, and
# then the kernel's out-of-memory killer ends one, as it does on a VM alone. A cgroup of the run's
# own would cap them together as the slice does, but needs a writable /sys/fs/cgroup, which a
# docker container and an ordinary user lack. tools/test_run_tests.sh nobus runs a plain and a
# metered piece with no user bus.
user_bus= data_kib=
if systemd-run --user --scope --quiet true 2>/dev/null; then
  user_bus=1
else
  data_kib=$(awk -v cores="$cores" '/^(MemTotal|SwapTotal):/ { s += $2 } END { printf "%.0f\n", cores * s + 112 * 1024 * 1024 }' /proc/meminfo)
  echo "no user bus: each piece runs with a data limit of $data_kib KiB (112 GiB, and memory and swap for each of $cores cores), not in zedtests.slice" >&2
fi
capped() {
  [ -z "$user_bus" ] || exec systemd-run --user --scope --quiet --same-dir --slice=zedtests.slice "$@"
  ulimit -d "$data_kib" && exec "$@"
}
export user_bus data_kib
export -f capped
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
    capped "${bound[@]}" bash -c 'in_run_copy "$@"' in_run_copy "$1" "${tracer[@]}" "$@" >"$scratch" 2>&1)
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
# The pieces run the build as it was when the run made its copy, below (TOOL-run-build-copy,
# tools7, 2026-11-20). A build in this checkout while a run goes on (an agent's next `zcargo
# build` or test run, or merge-push's) links each changed file again, and ld.lld deletes the
# file's name as its link starts and renames the new file in as it ends (strace of ld.lld 21,
# 2026-11-20: unlink of the output, write of <output>.tmp<random>, rename): during the link the
# name is gone, and stays gone when the link fails or is stopped. A process started meanwhile
# from the build failed: in kernel25's --bench run of l01_23 (2026-11-20, logs
# 20261120T191416.628139286Z-3209242) 124 pieces ended with exit 127, "error while loading
# shared libraries: libzed_kernel-1d3f0a86d9cd61e6.so: cannot open shared object file", in the
# run at 8n, a new process of the test binary (tests/src/scaling.rs, run_in_a_new_process),
# while kernel25 built zed-kernel again in the same checkout. After the link ends, a binary
# not linked again loads the new library instead ("symbol lookup error", see zrun), and a new
# process of a test binary linked again is the new build (current_exe names "<path>
# (deleted)"). So the run copies the profile folder of its test binaries (build/cargo/debug,
# or release for --bench) to <log directory>/cargo/<profile> before any piece runs: a hard
# link to each file in the folder and in its deps folder, and an empty folder for each of its
# other folders (build, examples, incremental, .fingerprint). A hard link shares its file, so
# nothing is copied, and keeps the file after the build deletes or replaces the name. Each
# piece then runs in a mount namespace of its own (in_run_copy) in which the copy is mounted on
# the profile folder and the profile's other folders on the copy's empty ones, so every path is
# the one the binaries were built with: current_exe, the rpaths, CARGO_BIN_EXE_zedc, the scratch
# folder found from the test binary's path (tests/src/scratch.rs). The namespace ends with the
# piece's last process, so nothing is unmounted; no lock is taken (NO-LOCKS-optimistic).
# The hard links are made from the files where they lie, the overlay's layers (build/upper over
# the snapshots of build/STACK, or build/cargo in a checkout with no STACK), reached by the
# checkout's own path ($ZRUN_WORKTREE): a link from the overlay mount to another mount fails with
# EXDEV, and the layers, the checkout and the snapshots are on one mount of one file system. A
# name in a higher layer hides it in the lower ones, and a deleted one (a whiteout, a character
# device) is left out; a folder marked opaque (user.overlay.opaque, zrun mounts with userxattr)
# hides the lower layers' folder. The module's metacopy and redirect_dir are off (Fedora's
# default, checked 2026-11-20), so a file in a layer holds its own data and lies at its own path.
# Cost: one find over each layer's two folders and one ln for all the files, about 1,900 links
# for debug. What a piece writes in the profile folder goes into the copy, deleted as the run
# ends (drop_run_copy, above): the prelinked runtime objects (crates/zed-native/src/link.rs,
# `Prelinked`), made beside the runtime library in deps, are found there when the build's deps
# held them as the run started, and made again in each run that needs one that was not.
# A copy is made only under zrun, with the log directory inside the checkout: elsewhere the
# fixed path drop_run_copy deletes by would not be on the copy's file system.
# make_run_copy <profile>: makes <log directory>/cargo/<profile>.
make_run_copy() {
  local profile=$1 base=$ZRUN_WORKTREE copy layers=() l d sub
  copy=$base${out#"$root"}/cargo/$profile
  if [ -e "$root/build/STACK" ]; then
    layers=("$base/build/upper")
    while read -r l; do layers+=("$l"); done <"$root/build/STACK"
  else
    layers=("$base/build/cargo")
  fi
  for sub in "" /deps; do
    mkdir -p "$copy$sub" || return 1
    for l in "${layers[@]}"; do
      d=$l/$profile$sub
      [ -e "$d" ] || [ -L "$d" ] || continue
      # Not a folder: a whiteout, the folder deleted in this layer.
      [ -d "$d" ] && [ ! -L "$d" ] || break
      find "$d" -mindepth 1 -maxdepth 1 -printf '%y\t%f\t%h\n'
      [ "$(getfattr --absolute-names --only-values -n user.overlay.opaque "$l/$profile" 2>/dev/null)" != y ] &&
        [ "$(getfattr --absolute-names --only-values -n user.overlay.opaque "$d" 2>/dev/null)" != y ] || break
    done | awk -F '\t' '!seen[$2]++' >"$out/copy-$profile.list"
    awk -F '\t' '$1 == "f" || $1 == "l" { print $3 "/" $2 }' "$out/copy-$profile.list" |
      xargs -r -d '\n' ln -P -t "$copy$sub" -- || return 1
    [ -n "$sub" ] || awk -F '\t' -v c="$copy" '$1 == "d" && $2 != "deps" { print c "/" $2 }' \
      "$out/copy-$profile.list" | xargs -r -d '\n' mkdir -p -- || return 1
  done
}
# in_run_copy <binary> <command...>: runs the command, in a mount namespace of its own with the
# run's copy of the binary's profile folder mounted on that folder, when the run made one.
in_run_copy() {
  local bin=$1 p
  shift
  p=${bin#"$root"/build/cargo/}
  p=${p%%/*}
  if [[ $bin == "$root"/build/cargo/*/deps/* ]] && [ -d "$out/cargo/$p" ]; then
    exec unshare --mount bash -c 'mount_run_copy "$@"' mount_run_copy "$out/cargo/$p" "$root/build/cargo/$p" "$@"
  fi
  exec "$@"
}
# mount_run_copy <copy> <profile folder> <command...>, in in_run_copy's namespace.
mount_run_copy() {
  local copy=$1 profile=$2 d
  shift 2
  for d in "$copy"/* "$copy"/.[!.]*; do
    [ -d "$d" ] && [ ! -L "$d" ] && [ "${d##*/}" != deps ] || continue
    mount --bind "$profile/${d##*/}" "$d" || exit 126
  done
  mount --rbind "$copy" "$profile" || exit 126
  exec "$@"
}
export -f in_run_copy mount_run_copy
if [ "$root" = /home/luke/Work/wt/.build-root ] && [ -n "$ZRUN_WORKTREE" ] && [[ $out == "$root"/build/* ]]; then
  trap at_exit EXIT
  trap 'exit 129' HUP
  trap 'exit 130' INT
  trap 'exit 143' TERM
  for p in $(awk '{ print $3 }' "$out/pieces" | sed -n "s|^$root/build/cargo/\([^/]*\)/deps/.*|\1|p" | sort -u); do
    if ! make_run_copy "$p"; then
      echo "The run's copy of build/cargo/$p could not be made."
      exit 1
    fi
  done
fi
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
# piece that fails there and passes in the slots keeps its output and prints its cause (`warm`,
# tools/lib.sh, FAIL-warm-step-drops-output).
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
  # The first linking piece runs alone, the others side by side with a bound on their test
  # threads (`warm_all`, tools/lib.sh, FAIL-warm-binaries-rc101-cause).
  if [ ! -s "$out/linking" ] || warm_all "$out/linking" "$jobs" "$cores"; then
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
