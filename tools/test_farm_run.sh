#!/bin/bash
# Tests tools/farm_run.sh with a fake pool.sh and job.sh (FARM_RUN_COLAB_DIR) on a toy checkout
# whose tools/run_tests.sh is a stub. The fake job.sh runs the job's `!` line in a copy of the
# checkout on this machine, with FARM_VM_JOB as the VM's /content/job, so the VM side of
# farm_run.sh (vm_side) runs here as it runs on a VM. The stub lists the pieces p1 to p7, the
# short-addresses piece short-g1 when its copy still has short_steps set, and with --full the pieces
# full-a (needs bash, run on a VM) and full-b (needs podman, which no VM has: not run, with
# short-g1, and named on farm_run.sh's `farm: not run` line); it fails a piece matching
# STUB_FAIL, and a benchmark matching STUB_FLAKY on its first run in a log directory's parent only.
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
mkdir -p "$toy/tools" "$toy/tests/full/a" "$toy/tests/full/b" "$colab" || exit 2
echo bash >"$toy/tests/full/a/needs"
echo podman >"$toy/tests/full/b/needs"
cat >"$toy/tools/run_tests.sh" <<'STUB'
#!/bin/bash
# Stub of tools/run_tests.sh (tools/test_farm_run.sh).
set -u -o pipefail
short_steps="g1"
short_libs="lib"
logs= list= pieces= only= except= bench= full= trace=
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
    [0-9]*) ;;
    *) echo "stub: unknown argument $1"; exit 2 ;;
  esac
  shift
done
if [ -n "$full" ]; then
  for t in $(cat tests/full/*/needs | sort -u); do
    command -v "$t" >/dev/null || { [ "$t" = podman ] && [ -n "${STUB_HAS_PODMAN:-}" ]; } || { echo "MISSING TOOLS: $t"; exit 1; }
  done
fi
[ -n "$logs" ] || { echo "stub: no --logs"; exit 2; }
d=$logs/$(date +%s%N)-$$
mkdir -p "$d" && ln -sfn "$d" "$logs/latest" || exit 2
if [ -z "$pieces" ]; then
  names="p1 p2 p3 p4 p5 p6 p7"
  [ -z "$short_steps" ] || names+=" short-g1"
  [ -z "$full" ] || names+=" full-a full-b"
  : >"$d/pieces"
  : >"$d/chosen"
  for n in $names; do
    [ -z "$only" ] || [[ $n =~ $only ]] || continue
    [ -z "$except" ] || [[ ! $n =~ $except ]] || continue
    echo "$n dir bin-$n" >>"$d/pieces"
    echo "grp-$n step-$n $n" >>"$d/chosen"
  done
  if [ ! -s "$d/pieces" ]; then echo "NO PIECE MATCHES --only '$only'"; exit 1; fi
  if [ -n "$list" ]; then echo "listed $(wc -l <"$d/pieces")"; exit 0; fi
  pieces=$d/pieces
fi
f=0 n=0
while read -r name rest; do
  # STUB_SKIP: a piece given but neither run nor reported, which farm_run.sh must not pass.
  [ -z "${STUB_SKIP:-}" ] || [[ ! $name =~ $STUB_SKIP ]] || continue
  n=$((n + 1))
  rc=0
  [ -z "${STUB_FAIL:-}" ] || [[ ! $name =~ $STUB_FAIL ]] || rc=1
  if [ -n "$bench" ] && [ -n "${STUB_FLAKY:-}" ] && [[ $name =~ $STUB_FLAKY ]] && [ ! -e "$logs/../flaky-$name" ]; then
    : >"$logs/../flaky-$name"
    rc=1
  fi
  [ -z "$trace" ] || echo "read $name" >"$trace/$name.reads"
  [ "$rc" = 0 ] || f=$((f + 1))
  echo "$name rc=$rc 1ms"
done <"$pieces"
echo "pieces: $n, failed: $f"
[ "$f" = 0 ]
STUB
chmod +x "$toy/tools/run_tests.sh"
# The fake pool: VM names hm1, hm2...; FAKE_FREE VMs at most held at once (default 4). Its log
# has a line per acquire and per release.
cat >"$colab/pool.sh" <<'POOL'
#!/bin/bash
set -u -o pipefail
d=$(dirname "$0")
case ${1-} in
  acquire)
    [[ ${2-} =~ ^(hm|std|l4|v5e)$ ]] && [ -n "${3-}" ] || { echo "pool: bad acquire $*" >&2; exit 2; }
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
# FAKE_DIE_FIRST=1: the first job of the run dies (exit 5) without running.
cat >"$colab/job.sh" <<'JOB'
#!/bin/bash
set -u -o pipefail
[ $# -ge 4 ] && [ $# -le 5 ] || exit 2
vm=$1 wt=$2 out=$3 tests=$4
[[ $vm =~ ^hm[0-9]+$ ]] && [[ $wt == /?* ]] && [[ $out == /?* ]] && [ -s "$tests" ] || exit 2
d=$(dirname "$0")
if [ "${FAKE_DIE_FIRST:-}" = 1 ] && mkdir "$d/died" 2>/dev/null; then echo "job died on $vm"; exit 5; fi
mkdir -p "$out/src" "$out/out" || exit 2
( cd "$wt" && git ls-files -z -co --exclude-standard | tar --null -T - -cf - ) | tar xf - -C "$out/src" || exit 2
line=$(head -1 "$tests")
line=${line//\/content\/job/$out}
( cd "$out/src" && FARM_VM_JOB=$out bash -c "${line#!}" ) >"$out/out/1.log" 2>&1
rc=$?
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
all="p1 p2 p3 p4 p5 p6 p7"
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
case_ all 0 "pieces: 7, failed: 0" "$all" -- --owner t --vms 3
command grep -q -c 'acquire hm3 t' "$colab/log" || { fail=$((fail + 1)); echo "FAIL all: not 3 VMs of owner t"; }
notrun all short-g1
STUB_HAS_PODMAN=1 case_ full 0 "pieces: 8, failed: 0" "$all full-a" -- --owner t --vms 2 --full
notrun full "short-g1 full-b"
STUB_FAIL='^p3$' case_ fail 1 "pieces: 7, failed: 1" "$all" -- --owner t --vms 4
STUB_SKIP='^p3$' case_ skipped 1 "pieces: 6, failed: 0" "p1 p2 p4 p5 p6 p7" -- --owner t --vms 2
command grep -q -c '^farm: the VMs did not run the listed pieces each once: share 1 ran 3 of its 4 pieces$' \
  "$ws/case-$n-skipped.out" || { fail=$((fail + 1)); echo "FAIL skipped: no line naming share 1's missing piece"; }
case_ except 0 "pieces: 5, failed: 0" "p1 p2 p4 p5 p7" -- --owner t --vms 3 --except '^p3$|^p6$'
printf '%s\n' p2 full-b short-g1 >"$ws/terms"
STUB_HAS_PODMAN=1 case_ terms 0 "pieces: 1, failed: 0" "p2" -- --owner t --vms 1 --full --terms "$ws/terms"
notrun terms "full-b short-g1"
printf '%s\n' short-g1 >"$ws/terms-here"
case_ terms-here-only 0 "pieces: 0, failed: 0" "" -- --owner t --vms 2 --terms "$ws/terms-here"
[ "$(command grep -c '^acquire' "$colab/log")" = 0 ] || { fail=$((fail + 1)); echo "FAIL terms-here-only: a VM acquired"; }
notrun terms-here-only short-g1
STUB_FLAKY='^p4$' case_ bench-rerun 0 "pieces: 7, failed: 0" "$all" -- --owner t --vms 2 --bench
command grep -q -c '^farm: first run: p4 rc=1' "$ws/case-$n-bench-rerun.out" || { fail=$((fail + 1)); echo "FAIL bench-rerun: no first-run line"; }
STUB_FAIL='^p5$' case_ bench-fail 1 "pieces: 7, failed: 1" "$all" -- --owner t --vms 2 --bench
FAKE_DIE_FIRST=1 case_ died-once 0 "pieces: 7, failed: 0" "$all" -- --owner t --vms 2
ls -d "$ws/case-$n-died-once/run/"vm?-2 >/dev/null 2>&1 || { fail=$((fail + 1)); echo "FAIL died-once: no second attempt"; }
FAKE_FREE=1 case_ one-free 0 "pieces: 7, failed: 0" "$all" -- --owner t --vms 4
case_ list 0 "pieces: 0, failed: 0" "" -- --owner t --vms 4 --list
[ "$(command grep -c '^acquire' "$colab/log")" = 1 ] || { fail=$((fail + 1)); echo "FAIL list: not one VM"; }
case_ trace 0 "pieces: 7, failed: 0" "$all" -- --owner t --vms 2 --trace "$ws/trace"
c=$(ls "$ws/trace"/vm*/*.reads 2>/dev/null | wc -l)
[ "$c" = 7 ] && [ -s "$ws/trace/vm1/groups" ] && [ ! -e "$ws/trace/local" ] ||
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
