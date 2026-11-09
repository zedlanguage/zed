#!/bin/bash
# Runs every test in pieces, one test binary, step folder, module or slow test each, each under a
# 60 s limit, and prints a line per piece as it ends. Usage, from a checkout's root:
#   tools/run_tests.sh [--full] [--only <ERE>] [--no-doc] [--list] [--reuse-table] [--logs <dir>] [jobs]
# Without --full this is the local suite, which needs only the Rust toolchain and runs in CI.
# --full adds tests/full/, the battery that needs emulators, containers, databases and other
# outside tools. It stops before any test if a tool is missing; nothing is skipped.
# --only runs only the pieces whose name, or whose group (the step folder, or the test binary's
# name without its hash, e.g. zedc, deep_heap, short-l01_37_oracle), matches the extended regular
# expression; a piece of a binary split per test also matches as <group>::<test>. A test binary
# whose source lies in a step folder under another name (deep_types in l01_22_type_representation)
# has that folder as a second group, so a selection of the step runs it too. A pattern that
# matches no piece stops the run with an error. The short-addresses build is made only when a
# short- piece is selected. --no-doc skips the check that the documentation builds. --list
# builds what the selection needs, prints the names of the selected pieces and runs nothing.
# A run without --only saves the table of all pieces in its log directory; --list --reuse-table
# selects from that table without building or listing the binaries, for tests of the selection.
# The table is as the run that wrote it left it: with --full or not, and stale once the test
# binaries are rebuilt. --logs puts the logs, the table and the piece list in <dir> instead of
# build/test-logs. Two runs in one checkout need different directories: a second run on a
# directory in use stops at once and names the run using it.
# The build is `cargo test --workspace --no-run`, which does nothing on a tree already built
# that way, so a run after such a build starts the pieces at once.
# A failed piece keeps its output in build/test-logs/<piece>.log, or in the --logs directory.
# Every piece runs in the systemd slice zedtests.slice, whose 112 GB limit holds across all
# checkouts together. A load above the number of cores raises the limit of the pieces that start under it in proportion.
args=$*
features= full_suite= only= list= reuse= logs= doc=1 jobs=6
while [ $# -gt 0 ]; do
  case $1 in
    --full) full_suite=1 ;;
    --only)
      if [ $# -lt 2 ] || [ -z "$2" ]; then
        echo "--only needs a non-empty extended regular expression"
        exit 2
      fi
      only=$2
      shift
      ;;
    --no-doc) doc= ;;
    --list) list=1 doc= ;;
    --reuse-table) reuse=1 ;;
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
      echo "unknown argument: $1 (usage: tools/run_tests.sh [--full] [--only <ERE>] [--no-doc] [--list] [--reuse-table] [--logs <dir>] [jobs])"
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
# Writes the pieces of the table on stdin that --only selects to $out/pieces, one per line: its
# name, directory and command. A line of the table is a piece's group, step folder, then those.
select_pieces() {
  while read -r group step name rest; do
    { selected "$group" "$name" || selected "$step" "$name"; } && echo "$name $rest"
  done >"$out/pieces"
  if [ ! -s "$out/pieces" ]; then
    echo "NO PIECE MATCHES --only '$only'"
    exit 1
  fi
}
if [ -n "$reuse" ]; then
  if [ ! -s "$out/table" ]; then
    echo "--reuse-table: no $out/table; run tools/run_tests.sh --list without --only first"
    exit 1
  fi
  select_pieces <"$out/table"
  cut -d ' ' -f 1 "$out/pieces"
  exit 0
fi
# A run without --only writes the table of every piece; a run with it, a table of its own.
table=$out/table
[ -z "$only" ] || table=$out/listing
if ! cargo test --workspace $features --no-run --message-format=short >"$out/build.log" 2>&1; then
  tail -40 "$out/build.log"
  echo "BUILD FAILED"
  exit 1
fi
# Cargo prints a binary path relative to the checkout only when the target directory is inside it.
bins=$(sed -n -e "s|^ *Executable .*(\(/.*\))$|\1|p" -e "s|^ *Executable .*(\([^/].*\))$|$root/\1|p" "$out/build.log")
full=$(echo "$bins" | grep '/full-')
# The short-addresses build (step L1.37a) keeps 8 bits of every content address and type digest,
# so distinct values collide; its pieces check that every place that compares by address
# confirms equal addresses by contents, and that verdicts and outputs match the full build.
short_steps="l01_37a_short_addresses l01_37_oracle"
short_build=
for s in $short_steps; do
  selected "short-$s" "short-$s" && short_build=1
done
short=
if [ -n "$short_build" ]; then
  if ! CARGO_TARGET_DIR=$root/build/short cargo test -p zed-tests --features short-addresses \
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
# get one piece each. Named because together they ran past
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
# 100,000 deep taking up to 15 s each (2026-11-09, T2-ty).
# l25_08 ran past 60 s whole at load 14 once bare literals made its chain of additions generic;
# its generic chain takes 35 s alone and the int chain 11 s (2026-11-09, LIT-bare).
# l01_39 pendants took 57 s whole at load 20 and ran past 60 s at load 25 once its tests of
# rewritten parts joined it (2026-11-09, PROJECT-canon-gcd).
# l01_39 lazy took 44 to 47 s whole once its check of leaves settled together (20 s alone at
# load 30) joined it; its seed loops of stars and of satellites took 38 and 42 s alone. Each
# loop is a module of parts over its seeds, and each part is a piece (2026-11-09,
# TEST-lazy-split).
split="
  l01_08_parser l01_16_elaboration l01_16_elaboration::scaling
  l01_23_subtyping l01_23_subtyping::scaling
  l01_25_preimage_catalog l01_25_preimage_catalog::s22
  l01_26_type_resolution l01_26_type_resolution::deep_ops
  l01_36_cranelift l01_36_cranelift::scaling l01_36_cranelift::table
  l01_38_presburger l01_38_presburger::oracle l01_38_presburger::omega
  l01_38_presburger::scaling l01_38_presburger::deep
  l01_38_presburger::names l01_38_presburger::live3
  l01_38_presburger::shared l01_38_presburger::stages
  l01_39_reduced_product l01_39_reduced_product::random
  l01_39_reduced_product::pendants l01_39_reduced_product::lazy
  l01_39_reduced_product::lazy::a_lazy_scope_settles_each_name_to_the_eager_product
  l01_39_reduced_product::lazy::a_lazy_scope_with_stars_of_two_hubs_settles_each_name_to_the_eager_product
  l01_39_reduced_product::lazy::a_lazy_scope_with_satellites_of_two_hubs_settles_each_name_to_the_eager_product
  l01_39_reduced_product::lazy::leaves_of_one_class_settled_together_get_what_each_gets_alone
  l01_39a_bit_words l01_39a_bit_words::scaling
  l25_08_mutate l25_08_mutate::scaling
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
        zedc_preimage-*)
          # The random tests split into parts (names ending in a digit) took 4 to 37 s each
          # alone at load 25 to 40, 711 s of processor time together, and the crate ran 75 to
          # 83 s in one process (TEST-split-slow, 2026-11-09); each part gets a process.
          # The or_ifs parts took 28 to 36 s each at load 16 to 40, so that test has sixteen
          # parts, numbered _1 to _16 (TEST-preimage-split, 2026-11-09).
          if tests=$("$p" --list --format terse); then
            parts=$(echo "$tests" | sed -n 's/^\(.*_[0-9][0-9]*\): test$/\1/p')
            echo "$n crates/zedc-preimage $p --exact$(printf ' --skip %s' $parts)"
            for t in $parts; do
              echo "$n::${t##*::} crates/zedc-preimage $p --exact $t"
            done
          else
            echo "$n crates/zedc-preimage $p"
          fi
          ;;
        # A crate zedc-* split from zedc; zedc_binary is a test of zed-native, run from tests.
        zedc_*-*)
          c=crates/${n%-*}
          c=${c//_/-}
          if [ -d "$c" ]; then echo "$n $c $p"; else echo "$n tests $p"; fi
          ;;
        zed_kernel-*)
          # This test took 35 to 39 s alone (46 s at load 26), so the rest of the
          # crate's tests ran past 60 s with it in one process (LIST-xor-finite,
          # 2026-11-07); it gets a process of its own.
          # The exclusive-or scaling test sums 8 random shapes per size and took 38 to 46 s
          # alone, so it gets one too (SCALE-fix-kernel, 2026-11-07). The parity test split
          # out of it takes 25 to 37 s, and gets one as well (SCALE-log-offset, 2026-11-09).
          slow=types::bdd::tests::exclusive_ors_agree_with_their_values
          xors=types::bdd::tests::exclusive_ors_scale
          parity=types::bdd::tests::parity_built_a_literal_at_a_time_scales
          echo "$n crates/zed-kernel $p --skip $slow --skip $xors --skip $parity"
          echo "$n::exclusive_ors crates/zed-kernel $p --exact $slow"
          echo "$n::exclusive_ors_scale crates/zed-kernel $p --exact $xors"
          echo "$n::parity_scale crates/zed-kernel $p --exact $parity"
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
    echo "$n $n $n tests $p"
  done
  if [ -n "$full" ]; then
    for d in tests/full/*/; do
      n=$(basename "$d")
      echo "$n $n $n tests $full $n::"
    done
  fi
} >"$table"
select_pieces <"$table"
if [ -n "$list" ]; then
  cut -d ' ' -f 1 "$out/pieces"
  exit 0
fi
# The documentation of every crate, private items included, builds with no warning, so a link
# in a doc comment that names no item, or a citation written as a link, fails the run.
if [ -n "$doc" ] &&
  ! RUSTDOCFLAGS='-D warnings' cargo doc --no-deps --document-private-items >"$out/doc.log" 2>&1; then
  tail -40 "$out/doc.log"
  echo "DOC FAILED"
  exit 1
fi
# At most `slots` pieces run at once on this machine, whichever checkout started them. A piece holds
# a lock on one file of $slot_dir until it ends, so a killed run frees its slots, and its 60 s start
# when it has one. Four suites at once took 2:13 with 8 slots and 2:05 without, and the longest
# piece 28 s against 53 s.
slots=8
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
export root out slots slot_dir cores
take_slot() {
  while :; do
    for slot in $(seq "$slots"); do
      exec 9>"$slot_dir/$slot"
      flock -n 9 && return
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
  limit=$(awk -v l="$load" -v c="$cores" 'BEGIN { x = 60 * l / c; print (x > 60 ? int(x + 1) : 60) }')
  start=$(date +%s%N)
  (cd "$root/$dir" && CARGO_MANIFEST_DIR=$root/$dir \
    systemd-run --user --scope --quiet --same-dir --slice=zedtests.slice \
    timeout -k 5 "$limit" "$@" >"$scratch" 2>&1)
  rc=$?
  ms=$((($(date +%s%N) - start) / 1000000))
  echo "$name rc=$rc ${ms}ms load=$load limit=${limit}s $(grep -E '^test result' "$scratch" | tail -1)"
  if [ "$rc" = 0 ]; then
    [ ! -s "$log" ] || : >"$log"
  else
    cp "$scratch" "$log"
  fi
  : >"$scratch"
  [ "$rc" = 0 ]
}
export -f take_slot piece
xargs -P "$jobs" -L 1 bash -c 'piece "$@"' _ <"$out/pieces" | tee "$out/summary"
bad=$(grep -vc 'rc=0 ' "$out/summary")
load=$(awk 'match($0, / load=[0-9.]+/) {
  l = substr($0, RSTART + 6, RLENGTH - 6) + 0
  if (NR == 1 || l < low) low = l
  if (l > high) high = l
} END { print low " to " high }' "$out/summary")
echo "pieces: $(wc -l <"$out/summary"), failed: $bad, load: $load, cores: $cores"
[ "$bad" = 0 ]
