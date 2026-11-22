#!/bin/bash
# Tests tools/farm_run.sh with a fake pool.sh and job.sh (FARM_RUN_COLAB_DIR) on a toy checkout
# whose tools/run_tests.sh is a stub. The fake job.sh runs the job's `!` line in a copy of the
# checkout on this machine, with FARM_VM_JOB as the VM's /content/job, so the VM side of
# farm_run.sh (vm_side) runs here as it runs on a VM. The stub lists the pieces p1 to p7, the
# short-addresses piece short-g1 when its copy still has short_steps set (it then checks that it
# runs at the build root FARM_VM_BUILD_ROOT with a tmpfs at build/short-clone, and it refuses
# short-g1 in --pieces, as run_tests.sh does), and with --full the pieces full-a (needs bash, run
# on a VM), full-b (needs qemu-s390x, which no VM has: not run, and named on farm_run.sh's
# `farm: not run` line) and full-c (needs podman: run on a VM after the fake
# tools/fetch_test_deps.sh, which the stub checks); it fails a piece matching
# STUB_FAIL, and a benchmark matching STUB_FLAKY on its first run in a log directory's parent only;
# it stops a piece matching STUB_TIMEOUT by its limit when run beside others (and alone too with
# STUB_TIMEOUT_ALONE), and kills one matching STUB_KILLED early (see the stub).
# Each case checks that every piece runs exactly once, the counts of the last line, the exit code,
# and that every VM acquired is released. Run from a checkout's root:
#   tools/test_farm_run.sh
# The workspace, build/test-farm-run/<UTC time>-<pid>, is kept (this script deletes nothing).
set -u -o pipefail
farm=${FARM_RUN:-$(pwd)/tools/farm_run.sh}
[ -x "$farm" ] || { echo "no $farm"; exit 2; }
ws=$(pwd)/build/test-farm-run/$(date -u +%Y%m%dT%H%M%S)-$$
[[ $ws == /?*/build/test-farm-run/*-$$ ]] || { echo "bad workspace '$ws'"; exit 2; }
toy=$ws/toy colab=$ws/colab
mkdir -p "$toy/tools" "$toy/tests/full/a" "$toy/tests/full/b" "$toy/tests/full/c" "$colab" || exit 2
echo bash >"$toy/tests/full/a/needs"
echo qemu-s390x >"$toy/tests/full/b/needs"
echo podman >"$toy/tests/full/c/needs"
# The fake tools/fetch_test_deps.sh: marks the deps directory of XDG_CACHE_HOME done, or fails
# with STUB_FETCH_FAIL; vm_side runs it when a folder of tests/full that needs podman can run.
cat >"$toy/tools/fetch_test_deps.sh" <<'FETCH'
#!/bin/bash
[ -z "${STUB_FETCH_FAIL:-}" ] || { echo "fetch: failed on purpose"; exit 1; }
[ -n "${XDG_CACHE_HOME:-}" ] || { echo "fetch: no XDG_CACHE_HOME"; exit 2; }
mkdir -p "$XDG_CACHE_HOME/zed-test-deps" && touch "$XDG_CACHE_HOME/zed-test-deps/done" && echo fetched
FETCH
chmod +x "$toy/tools/fetch_test_deps.sh"
export FARM_VM_CACHE=$ws/vm-cache
cat >"$toy/tools/run_tests.sh" <<'STUB'
#!/bin/bash
# Stub of tools/run_tests.sh (tools/test_farm_run.sh).
set -u -o pipefail
short_steps="g1"
short_libs="lib"
logs= list= pieces= only= except= bench= full= trace= jobs=
while [ $# -gt 0 ]; do
  case $1 in
    --short-groups) echo g1; exit 0 ;;
    --logs) logs=$2; shift ;;
    --only) only=$2; shift ;;
    --except) except=$2; shift ;;
    --pieces) pieces=$2; shift ;;
    --trace) trace=$2; shift ;;
    --list) list=1 ;;
    --bench) bench=1 ;;
    --full) full=1 ;;
    --skip-other-kind) ;;
    [0-9]*) jobs=$1 ;;
    *) echo "stub: unknown argument $1"; exit 2 ;;
  esac
  shift
done
if [ -n "$full" ]; then
  for t in $(cat tests/full/*/needs | sort -u); do
    command -v "$t" >/dev/null || { [ "$t" = qemu-s390x ] && [ -n "${STUB_HAS_PODMAN:-}" ]; } || { echo "MISSING TOOLS: $t"; exit 1; }
  done
  [ -e "${XDG_CACHE_HOME:-$HOME/.cache}/zed-test-deps/done" ] || { echo "MISSING deps: run tools/fetch_test_deps.sh"; exit 1; }
fi
[ -n "$logs" ] || { echo "stub: no --logs"; exit 2; }
d=$logs/$(date +%s%N)-$$
mkdir -p "$d" && ln -sfn "$d" "$logs/latest" || exit 2
if [ -z "$pieces" ]; then
  # STUB_BUILD_FAIL: the build fails, as run_tests.sh reports it. STUB_EMPTY_LIST: the list call
  # exits 0 with no piece and no word why. STUB_NOTHING: --skip-other-kind with nothing of the kind.
  if [ -n "${STUB_BUILD_FAIL:-}" ]; then
    echo "error[E0425]: cannot find value \`x\` in this scope"
    echo "BUILD FAILED"
    exit 1
  fi
  if [ -n "${STUB_EMPTY_LIST:-}${STUB_NOTHING:-}" ]; then
    : >"$d/pieces"
    [ -z "${STUB_NOTHING:-}" ] || echo "--skip-other-kind: nothing to run"
    exit 0
  fi
  names="p1 p2 p3 p4 p5 p6 p7"
  [ -z "$short_steps" ] || names+=" short-g1"
  [ -z "$full" ] || names+=" full-a full-b full-c"
  : >"$d/pieces"
  : >"$d/chosen"
  for n in $names; do
    [ -z "$only" ] || [[ $n =~ $only ]] || continue
    [ -z "$except" ] || [[ ! $n =~ $except ]] || continue
    # A short-addresses piece builds only at the build root, here with its clone's upper layer on
    # a tmpfs (FARM-short-pieces-on-vm-tmpfs).
    if [[ $n == short-* ]]; then
      [ "$(pwd)" = "${FARM_VM_BUILD_ROOT:-}" ] || { echo "SHORT BUILD: in $(pwd), not at the build root"; exit 1; }
      [ "$(findmnt -n -o FSTYPE --mountpoint "$(pwd)/build/short-clone")" = tmpfs ] ||
        { echo "SHORT BUILD: no tmpfs at build/short-clone"; exit 1; }
    fi
    echo "$n dir bin-$n" >>"$d/pieces"
    echo "grp-$n step-$n $n" >>"$d/chosen"
  done
  if [ ! -s "$d/pieces" ]; then echo "NO PIECE MATCHES --only '$only'"; exit 1; fi
  if [ -n "$list" ]; then echo "listed $(wc -l <"$d/pieces")"; exit 0; fi
  pieces=$d/pieces
elif grep -q '^short-' "$pieces"; then
  echo "stub: --pieces refuses the short-addresses pieces, whose clone is gone"
  exit 2
fi
f=0 n=0
while read -r name rest; do
  # STUB_SKIP: a piece given but neither run nor reported, which farm_run.sh must not pass.
  [ -z "${STUB_SKIP:-}" ] || [[ ! $name =~ $STUB_SKIP ]] || continue
  n=$((n + 1))
  rc=0 ms=1
  [ -z "${STUB_FAIL:-}" ] || [[ ! $name =~ $STUB_FAIL ]] || rc=1
  # STUB_TIMEOUT: stopped by its limit of 20 s (rc 124 after 21 s, as `timeout` reports it) when
  # run beside others (more than 1 job), and also alone with STUB_TIMEOUT_ALONE=1. STUB_KILLED:
  # killed (rc 137) after 1 ms, well before its limit, as by the kernel's OOM killer.
  if [ -n "${STUB_TIMEOUT:-}" ] && [[ $name =~ $STUB_TIMEOUT ]] && { [ "$jobs" != 1 ] || [ -n "${STUB_TIMEOUT_ALONE:-}" ]; }; then
    rc=124 ms=21000
  fi
  [ -z "${STUB_KILLED:-}" ] || [[ ! $name =~ $STUB_KILLED ]] || rc=137
  if [ -n "$bench" ] && [ -n "${STUB_FLAKY:-}" ] && [[ $name =~ $STUB_FLAKY ]] && [ ! -e "$logs/../flaky-$name" ]; then
    : >"$logs/../flaky-$name"
    rc=1
  fi
  [ -z "$trace" ] || echo "read $name" >"$trace/$name.reads"
  [ "$rc" = 0 ] || f=$((f + 1))
  echo "$name rc=$rc ${ms}ms load=0.5 limit=20s wait=0ms jobs=$jobs"
  # STUB_DUP: a piece reported twice.
  [ -z "${STUB_DUP:-}" ] || [[ ! $name =~ $STUB_DUP ]] || echo "$name rc=$rc ${ms}ms load=0.5 limit=20s wait=0ms jobs=$jobs"
done <"$pieces"
# STUB_LOWER_LOAD: the load file a run beside others leaves high, lowered to 0.1 2 s after it ends.
if [ -n "${STUB_LOWER_LOAD:-}" ] && [ "$jobs" != 1 ]; then
  (sleep 2 && echo '0.10 0.10 0.10 1/100 1' >"$STUB_LOWER_LOAD") >/dev/null 2>&1 &
fi
echo "pieces: $n, failed: $f"
[ "$f" = 0 ]
STUB
chmod +x "$toy/tools/run_tests.sh"
# The fake pool: VM names hm1, hm2...; FAKE_FREE VMs at most held at once (default 4); the first
# FAKE_BUSY acquires of a case are refused (exit 3) as when every VM is taken. Its log has a line
# per acquire, per refused acquire (busy) and per release.
cat >"$colab/pool.sh" <<'POOL'
#!/bin/bash
set -u -o pipefail
d=$(dirname "$0")
case ${1-} in
  acquire)
    [[ ${2-} =~ ^(hm|std|l4|v5e)$ ]] && [ -n "${3-}" ] || { echo "pool: bad acquire $*" >&2; exit 2; }
    if [ "$(command grep -c '^busy' "$d/log" 2>/dev/null)" -lt "${FAKE_BUSY:-0}" ]; then
      echo "busy $2" >>"$d/log"
      exit 3
    fi
    held=$(( $(command grep -c '^acquire' "$d/log" 2>/dev/null) - $(command grep -c '^release' "$d/log" 2>/dev/null) ))
    [ "$held" -lt "${FAKE_FREE:-4}" ] || exit 3
    i=$(( $(command grep -c '^acquire' "$d/log" 2>/dev/null) + 1 ))
    echo "acquire hm$i $3" >>"$d/log"
    echo "hm$i"
    ;;
  release)
    [[ ${2-} =~ ^hm[0-9]+$ ]] || { echo "pool: bad release $*" >&2; exit 2; }
    echo "release $2" >>"$d/log"
    ;;
  *) exit 2 ;;
esac
POOL
# The fake job.sh: the `!` line run in a copy of the checkout, /content/job being <out dir>.
# FAKE_DIE_FIRST=1: the first job of the run dies (exit 5) without running. FAKE_DIE_ALWAYS=1: every
# job dies so, its run.sh having failed to set up the toolchain. FAKE_EMPTY_SHARE=<k>: share k's
# `!` line prints nothing and exits 0, as a share that ran nothing. FAKE_SETUP_FULL_FAIL=1: the
# setup of the full tests' tools fails, as job.sh's run.sh reports it in out/setup-full.log.
cat >"$colab/job.sh" <<'JOB'
#!/bin/bash
set -u -o pipefail
[ $# -ge 4 ] && [ $# -le 5 ] || exit 2
vm=$1 wt=$2 out=$3 tests=$4
[[ $vm =~ ^hm[0-9]+$ ]] && [[ $wt == /?* ]] && [[ $out == /?* ]] && [ -s "$tests" ] || exit 2
d=$(dirname "$0")
if [ "${FAKE_DIE_FIRST:-}" = 1 ] && mkdir "$d/died" 2>/dev/null; then echo "job died on $vm"; exit 5; fi
if [ "${FAKE_DIE_ALWAYS:-}" = 1 ]; then
  echo "job died on $vm"
  echo "run.sh: setup failed: rustup (setup.log)"
  exit 5
fi
mkdir -p "$out/src" "$out/out" || exit 2
( cd "$wt" && git ls-files -z -co --exclude-standard | tar --null -T - -cf - ) | tar xf - -C "$out/src" || exit 2
[ "${FAKE_SETUP_FULL_FAIL:-}" != 1 ] ||
  echo "run.sh: the setup of the full tests' tools failed (setup.log)" >"$out/out/setup-full.log"
line=$(head -1 "$tests")
line=${line//\/content\/job/$out}
if [ -n "${FAKE_EMPTY_SHARE:-}" ] && [[ $line == *"farm_vm.sh $FAKE_EMPTY_SHARE "* ]]; then
  : >"$out/out/1.log"
  rc=0
else
  ( cd "$out/src" && FARM_VM_JOB=$out bash -c "${line#!}" ) >"$out/out/1.log" 2>&1
  rc=$?
fi
printf '%s\t%s\t0\t1\t1\n' "$(head -1 "$tests")" "$rc" >"$out/summary.tsv"
[ "$rc" = 0 ]
JOB
chmod +x "$colab/pool.sh" "$colab/job.sh"
git -C "$toy" init -q && git -C "$toy" add -A && git -C "$toy" -c user.name=t -c user.email=t commit -qm toy || exit 2
export FARM_RUN_COLAB_DIR=$colab
# A stub strace first on PATH: vm_side installs strace for --trace when it has none, and the fake
# VMs, all this machine, would run apt-get at once (one fails on dpkg's lock); the stub
# run_tests.sh never calls it.
mkdir -p "$ws/bin" && printf '#!/bin/sh\nexit 0\n' >"$ws/bin/strace" && chmod +x "$ws/bin/strace" || exit 2
# Likewise gawk, which vm_side installs when missing: the machine's awk stands in for it (the toy
# needs no GNU extension).
command -v gawk >/dev/null || ln -s "$(command -v awk)" "$ws/bin/gawk" || exit 2
export PATH=$ws/bin:$PATH
# The load vm_side reads before it runs timed-out pieces again (FARM_VM_LOADAVG, /proc/loadavg on a
# VM): low, so that no case but load-wait waits, whatever this machine's own load.
echo '0.10 0.10 0.10 1/100 1' >"$ws/loadavg" || exit 2
export FARM_VM_LOADAVG=$ws/loadavg
# The build root vm_side binds each fake VM's checkout at, in a mount namespace of its own, and
# the target directory it binds at its build/cargo (CARGO_TARGET_DIR, /content/target on a VM).
export FARM_VM_BUILD_ROOT=$ws/build-root CARGO_TARGET_DIR=$ws/target
pass=0 fail=0
# case <name> <expected exit> <expected last line> <ERE each piece must match once, or ''> -- <farm_run arguments>
n=0
case_() {
  local name=$1 want_rc=$2 want_last=$3 once=$4
  shift 5
  n=$((n + 1))
  local o=$ws/case-$n-$name
  : >"$colab/log"
  ( cd "$toy" && "$farm" "$@" --out "$o/run" --jobs 2 ) >"$o.out" 2>&1
  local rc=$? bad=
  [ "$rc" = "$want_rc" ] || bad+=" exit $rc, not $want_rc;"
  local last
  last=$(tail -1 "$o.out")
  [ "$last" = "$want_last" ] || bad+=" last line '$last', not '$want_last';"
  if [ -n "$once" ]; then
    local p c
    for p in $once; do
      c=$(command grep -a -c -E "^$p rc=" "$o.out")
      [ "$c" = 1 ] || bad+=" $p reported $c times;"
    done
  fi
  local a r
  a=$(command grep -c '^acquire' "$colab/log")
  r=$(command grep -c '^release' "$colab/log")
  [ "$a" = "$r" ] || bad+=" $a VMs acquired, $r released;"
  if [ -z "$bad" ]; then
    pass=$((pass + 1))
    echo "ok $name"
  else
    fail=$((fail + 1))
    echo "FAIL $name:$bad (output $o.out)"
  fi
}
all="p1 p2 p3 p4 p5 p6 p7 short-g1"
# notrun <case> <names>: the case's output names exactly <names> on its `farm: not run` line (the
# pieces no VM can run, which run nowhere) and reports none of them as run.
notrun() {
  local o=$ws/case-$n-$1.out want=$2 got
  got=$(command grep -a '^farm: not run, ' "$o" | sed 's/^[^:]*: [^:]*: //')
  if [ "$got" != "$want" ] || command grep -a -q -E "^(${want// /|}) rc=" "$o"; then
    fail=$((fail + 1))
    echo "FAIL $1: not-run line '$got', not '$want', or one of them ran"
  fi
}
# has <case> <ERE> <count>: the case's output has exactly <count> lines matching <ERE>. (Until
# FARM-setup-fail-silent it was defined below the cases full, full-no-c and fetch-fail, whose
# `has` checks then ran no check: bash printed "has: command not found" and counted nothing.)
has() {
  local c
  c=$(command grep -a -c -E "$2" "$ws/case-$n-$1.out")
  [ "$c" = "$3" ] || { fail=$((fail + 1)); echo "FAIL $1: $c lines match '$2', not $3 ($ws/case-$n-$1.out)"; }
}
case_ all 0 "pieces: 8, failed: 0" "$all" -- --owner t --vms 3
command grep -q -c 'acquire hm3 t' "$colab/log" || { fail=$((fail + 1)); echo "FAIL all: not 3 VMs of owner t"; }
has all '^farm: not run' 0
# Tests (FARM-short-pieces-on-vm-tmpfs): short-g1 ran on a VM (the stub checked its build root
# and tmpfs), by name in a run of its own, as --pieces refuses it.
has all '^stub: --pieces refuses' 0
STUB_HAS_PODMAN=1 case_ full 0 "pieces: 10, failed: 0" "$all full-a full-c" -- --owner t --vms 2 --full
notrun full "full-b"
# Tests (FARM-local-only-pieces-on-vm): full-c needs podman, so each share fetches the deps first,
# into FARM_VM_CACHE (the stub fails a --full run whose deps are not done).
has full '^farm: tools/fetch_test_deps\.sh ran in [0-9]+ s ' 2
[ -e "$FARM_VM_CACHE/zed-test-deps/done" ] || { fail=$((fail + 1)); echo "FAIL full: nothing fetched into $FARM_VM_CACHE"; }
STUB_HAS_PODMAN=1 case_ full-no-c 0 "pieces: 9, failed: 0" "$all full-a" -- --owner t --vms 2 --full --except '^full-c$'
has full-no-c '^farm: tools/fetch_test_deps' 0
STUB_HAS_PODMAN=1 STUB_FETCH_FAIL=1 case_ fetch-fail 1 "pieces: 0, failed: 0" "" -- --owner t --vms 1 --full
has fetch-fail '^vm_side: tools/fetch_test_deps\.sh failed' 1
has fetch-fail '^farm: FAILED: share 1 of 1 on hm1 ran no piece \(exit 2\): vm_side: tools/fetch_test_deps\.sh failed' 1
STUB_FAIL='^p3$' case_ fail 1 "pieces: 8, failed: 1" "$all" -- --owner t --vms 4
STUB_SKIP='^p3$' case_ skipped 1 "pieces: 7, failed: 0" "p1 p2 p4 p5 p6 p7 short-g1" -- --owner t --vms 2
has skipped '^farm: FAILED: share 1 of 2 on hm[0-9]+ did not run the pieces it was given: not reported: p3$' 1
# Tests (FARM-setup-fail-silent): each way a share can run fewer pieces than it was given, or none,
# fails the run with a line naming the share, its VM and the failing step.
STUB_BUILD_FAIL=1 case_ build-fail 1 "pieces: 0, failed: 0" "" -- --owner t --vms 2
has build-fail '^farm: FAILED: share [12] of 2 on hm[0-9]+ ran no piece \(exit 1\): BUILD FAILED; error\[E0425\]' 2
# The list call exits 0 and lists nothing, without the word of --skip-other-kind.
STUB_EMPTY_LIST=1 case_ empty-list 1 "pieces: 0, failed: 0" "" -- --owner t --vms 1
has empty-list '^farm: FAILED: share 1 of 1 on hm1 ran no piece \(exit 2\): vm_side: the list call exited 0 and listed no piece' 1
# Nothing of the kind with --skip-other-kind: no piece, and no failure.
STUB_NOTHING=1 case_ nothing-to-run 0 "pieces: 0, failed: 0" "" -- --owner t --vms 2 --skip-other-kind
has nothing-to-run '^farm: FAILED' 0
# Share 2 of 3 prints nothing and exits 0: its pieces p2, p5 and short-g1 ran nowhere.
FAKE_EMPTY_SHARE=2 case_ silent-share 1 "pieces: 5, failed: 0" "p1 p3 p4 p6 p7" -- --owner t --vms 3
has silent-share '^farm: FAILED: share 2 of 3 on hm[0-9]+ ran no piece \(exit 0\): no output' 1
# One piece reported twice and another not at all: the counts agree, the names do not.
STUB_DUP='^p3$' STUB_SKIP='^p5$' case_ dup-and-missing 1 "pieces: 8, failed: 0" "" -- --owner t --vms 2
has dup-and-missing '^farm: FAILED: share 1 of 2 on hm[0-9]+ did not run the pieces it was given: not reported: p5; reported more than once: p3$' 1
# Every job dies in its setup: each attempt is named with its VM and the setup's own words.
FAKE_DIE_ALWAYS=1 case_ die-always 129 "pieces: 0, failed: 0" "" -- --owner t --vms 1
has die-always '^farm: share 1 of 1 on hm[0-9]+ did not run to its end \(job\.sh exit 5\): job died on hm[0-9]+; run\.sh: setup failed: rustup \(setup\.log\)' 3
has die-always '^farm: FAILED: share 1 of 1 lost after 3 attempts, on hm1 hm2 hm3; its pieces are not reported$' 1
# The setup of the full tests' tools failed on the VM: the run fails, though its pieces passed.
STUB_HAS_PODMAN=1 FAKE_SETUP_FULL_FAIL=1 case_ setup-full-fail 1 "pieces: 10, failed: 0" "$all full-a full-c" -- --owner t --vms 1 --full
has setup-full-fail "^farm: FAILED: share 1 of 1 on hm1: run\.sh: the setup of the full tests' tools failed" 1
case_ except 0 "pieces: 6, failed: 0" "p1 p2 p4 p5 p7 short-g1" -- --owner t --vms 3 --except '^p3$|^p6$'
printf '%s\n' p2 full-b short-g1 >"$ws/terms"
STUB_HAS_PODMAN=1 case_ terms 0 "pieces: 2, failed: 0" "p2 short-g1" -- --owner t --vms 1 --full --terms "$ws/terms"
notrun terms "full-b"
printf '%s\n' short-g1 >"$ws/terms-short"
case_ terms-short 0 "pieces: 1, failed: 0" "short-g1" -- --owner t --vms 2 --terms "$ws/terms-short"
# Without a term naming one, the VMs' copy of run_tests.sh selects no short-addresses piece.
printf '%s\n' p2 >"$ws/terms-p2"
case_ terms-no-short 0 "pieces: 1, failed: 0" "p2" -- --owner t --vms 1 --terms "$ws/terms-p2"
has terms-no-short '^short-g1 ' 0
printf '%s\n' full-b >"$ws/terms-here"
case_ terms-here-only 0 "pieces: 0, failed: 0" "" -- --owner t --vms 2 --full --terms "$ws/terms-here"
[ "$(command grep -c '^acquire' "$colab/log")" = 0 ] || { fail=$((fail + 1)); echo "FAIL terms-here-only: a VM acquired"; }
notrun terms-here-only full-b
# A short-addresses piece is not run again: failed, or stopped by its limit, its verdict stands,
# and it fails the share even when the share's other stopped piece passes alone.
STUB_FAIL='^short-g1$' case_ short-fail 1 "pieces: 8, failed: 1" "$all" -- --owner t --vms 2
has short-fail '^farm: (first run|each )' 0
STUB_TIMEOUT='^short-g1$' case_ short-timeout 1 "pieces: 8, failed: 1" "$all" -- --owner t --vms 2
has short-timeout '^farm: (first run|each )' 0
STUB_TIMEOUT='^p2$' STUB_FAIL='^short-g1$' case_ short-fail-and-timeout 1 "pieces: 8, failed: 1" "$all" -- --owner t --vms 1
has short-fail-and-timeout '^farm: stopped by its limit under load, passed alone: p2$' 1
has short-fail-and-timeout '^short-g1 rc=1 ' 1
STUB_FLAKY='^p4$' case_ bench-rerun 0 "pieces: 8, failed: 0" "$all" -- --owner t --vms 2 --bench
command grep -q -c '^farm: first run: p4 rc=1' "$ws/case-$n-bench-rerun.out" || { fail=$((fail + 1)); echo "FAIL bench-rerun: no first-run line"; }
STUB_FAIL='^p5$' case_ bench-fail 1 "pieces: 8, failed: 1" "$all" -- --owner t --vms 2 --bench
# Tests (FARM-share-load-timeouts): a piece stopped by its limit under the share's load runs once
# more alone; passing alone it is reported passed, its first line kept with the prefix, and named.
STUB_TIMEOUT='^p4$' case_ timeout-rerun 0 "pieces: 8, failed: 0" "$all" -- --owner t --vms 2
has timeout-rerun '^farm: first run: p4 rc=124 21000ms ' 1
has timeout-rerun '^p4 rc=0 .* jobs=1$' 1
has timeout-rerun '^farm: each test piece stopped by its limit run again once, alone, on the same VM' 1
has timeout-rerun '^farm: stopped by its limit under load, passed alone: p4$' 1
# Stopped by its limit alone too: failed.
STUB_TIMEOUT='^p4$' STUB_TIMEOUT_ALONE=1 case_ timeout-alone-too 1 "pieces: 8, failed: 1" "$all" -- --owner t --vms 2
has timeout-alone-too '^farm: first run: p4 rc=124 ' 1
has timeout-alone-too '^p4 rc=124 .* jobs=1$' 1
has timeout-alone-too '^farm: stopped by its limit under load, passed alone: ' 0
# A failed assertion (rc 1) and a kill well before the limit (rc 137) are not run again.
STUB_FAIL='^p4$' case_ assert-fail 1 "pieces: 8, failed: 1" "$all" -- --owner t --vms 2
has assert-fail '^farm: (first run|each )' 0
STUB_KILLED='^p6$' case_ killed 1 "pieces: 8, failed: 1" "$all" -- --owner t --vms 2
has killed '^farm: (first run|each )' 0
# Both in one share: the timed-out piece passes alone, the failed one stays failed.
STUB_FAIL='^p3$' STUB_TIMEOUT='^p5$' case_ timeout-and-fail 1 "pieces: 8, failed: 1" "$all" -- --owner t --vms 1
has timeout-and-fail '^p3 rc=1 ' 1
has timeout-and-fail '^farm: first run: p3 ' 0
has timeout-and-fail '^p5 rc=0 .* jobs=1$' 1
# Before the run alone vm_side waits for the load to fall to the cores: the stub's share run
# leaves the load at 9999 for 2 s (STUB_LOWER_LOAD), so that the run alone has run_tests.sh's
# limit of 20 s, not one raised by the load the share left behind.
echo '9999.00 9999.00 9999.00 1/100 1' >"$ws/loadavg-high" || exit 2
FARM_VM_LOADAVG=$ws/loadavg-high STUB_LOWER_LOAD=$ws/loadavg-high STUB_TIMEOUT='^p2$' \
  case_ load-wait 0 "pieces: 8, failed: 0" "$all" -- --owner t --vms 1
has load-wait '^farm: waited [1-9][0-9]* s for the load to fall to the [0-9]+ cores \(load 0\.10\)' 1
FAKE_DIE_FIRST=1 case_ died-once 0 "pieces: 8, failed: 0" "$all" -- --owner t --vms 2
ls -d "$ws/case-$n-died-once/run/"vm?-2 >/dev/null 2>&1 || { fail=$((fail + 1)); echo "FAIL died-once: no second attempt"; }
FAKE_FREE=1 case_ one-free 0 "pieces: 8, failed: 0" "$all" -- --owner t --vms 4
# A round in which every shape is refused: one wait of 15 s (the reaper's period, FARM-run-retry-15s),
# then the next round takes both VMs wanted, not only the first.
t0=$(date +%s)
FAKE_BUSY=3 case_ busy-round 0 "pieces: 8, failed: 0" "$all" -- --owner t --vms 2
t1=$(date +%s)
[ "$(command grep -a -c '^farm: no Colab VM free for t; trying again in 15 s ' "$ws/case-$n-busy-round.out")" = 1 ] &&
  [ "$(command grep -c '^busy' "$colab/log")" = 3 ] && [ "$(command grep -c '^acquire' "$colab/log")" = 2 ] &&
  [ $((t1 - t0)) -ge 15 ] && [ $((t1 - t0)) -lt 60 ] ||
  { fail=$((fail + 1)); echo "FAIL busy-round: not one 15 s wait then 2 VMs ($((t1 - t0)) s; $ws/case-$n-busy-round.out)"; }
case_ list 0 "pieces: 0, failed: 0" "" -- --owner t --vms 4 --list
[ "$(command grep -c '^acquire' "$colab/log")" = 1 ] || { fail=$((fail + 1)); echo "FAIL list: not one VM"; }
case_ trace 0 "pieces: 8, failed: 0" "$all" -- --owner t --vms 2 --trace "$ws/trace"
c=$(ls "$ws/trace"/vm*/*.reads 2>/dev/null | wc -l)
[ "$c" = 8 ] && [ -s "$ws/trace/vm1/groups" ] && [ ! -e "$ws/trace/local" ] ||
  { fail=$((fail + 1)); echo "FAIL trace: $c read lists, or a local trace"; }
# Usage errors: exit 2, nothing made, no VM acquired.
for bad in "--owner '' --vms 1" "--owner t --vms 5" "--owner t --vms 0" "--owner 't x' --vms 1" "--owner t --vms 1 --jobs 0" \
  "--owner t --vms 1 --terms /nonexistent" "--owner t --vms 1 --trace rel" "--owner t --vms 1 --zrun /bin/true" \
  "--owner t --vms 1 --except '('" "--owner t --vms 1 --bogus"; do
  : >"$colab/log"
  n=$((n + 1))
  o=$ws/case-$n-usage
  eval "set -- $bad"
  # The bad arguments last, so that a bad --jobs is not overridden by the good one.
  ( cd "$toy" && "$farm" --out "$o" --jobs 2 "$@" ) >"$o.out" 2>&1
  rc=$?
  if [ "$rc" = 2 ] && [ ! -e "$o" ] && [ ! -s "$colab/log" ]; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    echo "FAIL usage '$bad': exit $rc"
  fi
done
mkdir -p "$ws/exists"
( cd "$toy" && "$farm" --owner t --vms 1 --out "$ws/exists" --jobs 2 ) >"$ws/exists.out" 2>&1
if [ $? = 2 ]; then pass=$((pass + 1)); else fail=$((fail + 1)); echo "FAIL usage: an --out that exists"; fi
( cd "$toy" && "$farm" --owner t --vms 1 --out "rel/out" --jobs 2 ) >"$ws/rel.out" 2>&1
if [ $? = 2 ]; then pass=$((pass + 1)); else fail=$((fail + 1)); echo "FAIL usage: a relative --out"; fi
echo "test_farm_run: $pass passed, $fail failed (workspace $ws)"
[ "$fail" = 0 ]
