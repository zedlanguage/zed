#!/bin/bash
# Runs every test in pieces, one test binary, step folder, module or slow test each, each under a
# 60 s limit, and prints a line per piece as it ends. Usage, from a checkout's root:
#   tools/run_tests.sh [--full] [--only <ERE>] [--doc] [--list] [--reuse-table] [--logs <dir>] [jobs]
# Without --full this is the local suite, which needs only the Rust toolchain and runs in CI.
# --full adds tests/full/, the battery that needs emulators, containers, databases and other
# outside tools. It stops before any test if a tool is missing; nothing is skipped.
# --only runs only the pieces whose name, or whose group (the step folder, or the test binary's
# name without its hash, e.g. zedc, deep_heap, short-l01_37_oracle), matches the extended regular
# expression; a piece of a binary split per test also matches as <group>::<test>. A test binary
# whose source lies in a step folder under another name (deep_types in l01_22_type_representation)
# has that folder as a second group, so a selection of the step runs it too. A pattern that
# matches no piece stops the run with an error. The short-addresses build is made only when a
# short- piece is selected, in a clone of build/cargo that the run deletes at its end; such a
# run must go through /home/luke/Work/wt/zrun. --doc adds the check that the documentation
# builds, which is off by default; --no-doc is accepted and changes nothing. --list builds what
# the selection needs, prints the names of the selected pieces and runs nothing.
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
# checkouts together. A load above the number of cores raises the limit of the pieces that start under it in proportion.
args=$*
features= full_suite= only= list= reuse= logs= doc= jobs=6
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
    --doc) doc=1 ;;
    --no-doc) ;;
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
      echo "unknown argument: $1 (usage: tools/run_tests.sh [--full] [--only <ERE>] [--doc] [--list] [--reuse-table] [--logs <dir>] [jobs])"
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
# The short-addresses build (step L1.37a) keeps 8 bits of every content address and type digest,
# so distinct values collide; its pieces check that every place that compares by address
# confirms equal addresses by contents, and that verdicts and outputs match the full build.
# It builds in a clone of the checkout's build that this run makes and deletes: an overlay mount
# at build/short-clone/cargo whose one lower layer is build/cargo, read-only, with an empty upper
# layer build/short-clone/upper that receives what the feature rebuilds (zed-kernel and every
# crate above it, 16 crates; the 92 crates from crates.io are reused). Mounting it took 11 ms;
# a copy of build/cargo would be 94 GB, or 3 GB without the incremental caches, which the
# feature's crates cannot use. The target directory's path changes nothing cargo reuses: the
# whole workspace built in such a clone compiled nothing. Until 2026-11-10 the build had a
# target directory of its own, build/short, kept from run to run (BUILD-short-clone, -j 4, load
# 27 to 61): build/short took 1.5 GB per checkout and 227 s (735 s of CPU) cold, then 11 s
# after a one-line change to zedc; the clone takes 1.0 GB during the run and none after, and
# 180 to 237 s (500 to 551 s of CPU) on every run, as the feature's crates build from nothing.
# The clone is mounted in the zrun namespace, so the run must go through zrun, and build/cargo
# must not change while it is mounted (no other zcargo build of this checkout at that time).
# The clone is deleted when the run ends, by failure or interrupt too; a run killed with
# SIGKILL leaves it to the next run, which deletes it first. Two runs in one checkout take
# build/short-clone.lock in turn, the second waiting until the first has ended; checkouts do
# not share it, as each zrun namespace mounts its own checkout at the fixed path.
# Unmounts and deletes the clone, if there is one. Every path is written out: a delete names its
# target in full (the author's rule), and the clone exists only at the fixed path of zrun.
drop_short_clone() {
  [ -e /home/luke/Work/wt/.build-root/build/short-clone ] || return 0
  for _ in 1 2 3 4 5 6 7 8 9 10; do
    mountpoint -q /home/luke/Work/wt/.build-root/build/short-clone/cargo || break
    umount /home/luke/Work/wt/.build-root/build/short-clone/cargo 2>/dev/null || sleep 1
  done
  if [ -L /home/luke/Work/wt/.build-root/build/short-clone ] ||
    [ ! -d /home/luke/Work/wt/.build-root/build/short-clone ] ||
    [ "$(realpath -e /home/luke/Work/wt/.build-root/build/short-clone)" != \
      /home/luke/Work/wt/.build-root/build/short-clone ] ||
    findmnt -rn -o TARGET | grep -qE '^/home/luke/Work/wt/\.build-root/build/short-clone(/|$)'; then
    echo "The short-addresses clone /home/luke/Work/wt/.build-root/build/short-clone is still" \
      "mounted, or is not a directory; it is left in place."
    return 1
  fi
  # The kernel leaves the overlay's inner work directory at mode 000, which rm cannot enter.
  [ ! -d /home/luke/Work/wt/.build-root/build/short-clone/work/work ] ||
    chmod u+rwx /home/luke/Work/wt/.build-root/build/short-clone/work/work
  rm -rf --one-file-system --preserve-root=all /home/luke/Work/wt/.build-root/build/short-clone
}
short=
if [ -n "$short_build" ]; then
  exec 6>>"$root/build/short-clone.lock"
  if ! flock -n 6; then
    echo "Waiting for the other run of this checkout that uses the short-addresses clone to end."
    flock 6
  fi
  drop_short_clone || exit 1
  trap drop_short_clone EXIT
  trap 'exit 129' HUP
  trap 'exit 130' INT
  trap 'exit 143' TERM
  mkdir -p "$root/build/short-clone/upper" "$root/build/short-clone/work" "$root/build/short-clone/cargo"
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
split="
  l01_08_parser l01_16_elaboration l01_16_elaboration::scaling
  l01_23_subtyping l01_23_subtyping::scaling
  l01_25_preimage_catalog l01_25_preimage_catalog::s22
  l01_25_preimage_catalog::exact_oracle
  l01_26_type_resolution l01_26_type_resolution::deep_ops
  l01_36_cranelift l01_36_cranelift::scaling l01_36_cranelift::table
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
