#!/bin/bash
# Steps 0, 0b, 0c and 1a of tools/merge_check.sh (see its header): the self-tests of the tools and
# clippy, moved here from merge_check.sh (FARM-merge-check-clippy-selftests-remote) so that they can
# run on a Colab VM, which has a copy of the checkout's files but no git repository: merge_check.sh
# decides which steps run and calls this script here (MERGE_CHECK_FARM=local) or on one VM through
# `tools/farm_run.sh --commands`. Usage, from a checkout's root:
#   tools/merge_check_steps.sh --logs <absolute prefix> [--self] [--rt] [--farm] [--clippy '<package>...']
#   --logs    each log is <prefix>-<name>: merge_check.sh passes its git directory's merge-check
#   --self    step 0, the parts of tools/test_merge_check.sh
#   --rt      step 0b, the parts of tools/test_run_tests.sh
#   --farm    step 0c, tools/test_farm_run.sh
#   --clippy  step 1a, cargo clippy -D warnings on these packages
# Exit 0 when every step given passed, 1 when one failed, 2 on a usage error. The lines it prints
# are merge_check.sh's `merge check: ...` lines of these steps.
. "${BASH_SOURCE[0]%/*}/lib.sh" || exit 2
logs= selftest= rtself= farmself= clippy_run=
usage="usage: tools/merge_check_steps.sh --logs <absolute prefix> [--self] [--rt] [--farm] [--clippy '<package>...']"
while [ $# -gt 0 ]; do
  case $1 in
    --logs | --clippy)
      [ $# -ge 2 ] && [ -n "$2" ] || { echo "$usage" >&2; exit 2; }
      if [ "$1" = --logs ]; then logs=$2; else clippy_run=$2; fi
      shift
      ;;
    --self) selftest=1 ;;
    --rt) rtself=1 ;;
    --farm) farmself=1 ;;
    *) echo "$usage" >&2; exit 2 ;;
  esac
  shift
done
[[ $logs == /?* ]] || { echo "$usage" >&2; exit 2; }
[[ $clippy_run =~ ^[A-Za-z0-9_\ -]*$ ]] || { echo "merge check: bad package list '$clippy_run'" >&2; exit 2; }
[ -x tools/run_tests.sh ] || { echo "run from a checkout's root" >&2; exit 2; }
mkdir -p "${logs%/*}" || { echo "merge check: cannot create ${logs%/*}" >&2; exit 2; }

# Step 0b: the parts of tools/test_run_tests.sh, started here and waited for after step 0, so the
# two steps run at once. A part that is not run (its chain stopped first) is reported as failed.
# The parts list the tests of the built binaries, and each builds first as run_tests.sh does,
# which does nothing on a built tree; on a worktree whose tests are not built yet every part ran
# into its limit while building (2026-11-20: all six killed at 60 s with empty logs). So the
# build comes first, `run_tests.sh --list` with no --only (the build of the full listing, with
# the short-addresses clone), with no time limit, since it is a build and not a test, and the
# parts start when it has passed. The build runs in the foreground, before step 0 starts its
# timed parts too: run beside them, a workspace build (at load 50 on 2026-11-20) pushed
# tools/test_merge_check.sh select, 15 to 21 s alone, past its 25 s limit.
rtparts=(list select table except benches fresh short copy concurrent trace nobus warm)
rtpids=()
if [ -n "$rtself" ]; then
  rlog=$logs-rt
  piece_limit
  rtlimit=$((limit > 60 ? limit : 60))
  rt_part() { timeout -k 5 "$rtlimit" tools/test_run_tests.sh "$1" >"$rlog-$1.log" 2>&1; }
  # Emptied first, so a part its chain did not reach shows no line of an earlier check.
  for p in "${rtparts[@]}"; do : >"$rlog-$p.log"; done
  if ! tools/run_tests.sh --logs "$rlog-build" --list >"$rlog-build.log" 2>&1; then
    tail -n 40 "$rlog-build.log"
    echo "merge check: FAILED: the build for tools/test_run_tests.sh (log $rlog-build.log)" >&2
    exit 1
  fi
  # The parts' verdicts are read from their logs.
  # short starts when list has ended: both list fresh with the short-addresses clone, and a run
  # waits while another has it mounted, so beside list short spent list's time (30 to 57 s) out
  # of its own 60 s (killed at 60 s at load 52 on 2026-11-20; 6 to 11 s alone). select and table
  # reuse list's table and mount no clone, as does except after table, so short runs beside them.
  # fresh, copy, trace and nobus each start cargo several times, and cargo lets one process at a
  # time hold its package cache: started at once beside list's chain, they waited on each other
  # and on it ("Blocking waiting for file lock on package cache"), and fresh, copy and trace were
  # killed at 60 s in b22-small15's two checks and b22-tests9's three on 2026-11-24 (hm3 and hm4,
  # load under 2; on 2026-11-23 all passed beside it). One after another on hm3, with nothing
  # beside them, they took 85 (with a rebuild), 23, 45 and 41 s, with no wait on the lock in the
  # last three; in one chain of their own beside list's, fresh, copy and trace were still killed.
  # So they run after list's chain, one after another, each under its own limit as before; the
  # chain goes on past a failed part, so each part's verdict is read. In this order trace and
  # nobus passed but fresh and copy were still killed (hm4, nothing else of the check running):
  # FAIL-rt-parts-cargo-lock is open.
  (
    (
      rt_part list && {
        rt_part short &
        rt_part select && rt_part table && rt_part except && rt_part benches
        wait
      }
      for p in fresh copy trace nobus; do rt_part "$p"; done
    ) &
    for p in concurrent warm; do rt_part "$p" & done
    wait
  ) &
  rtpids+=($!)
fi
# Waits for step 0b and fails when a part failed: each part's last line is "checks failed: 0"
# exactly when it passed (a part killed by its limit has no such line).
rt_wait() {
  [ ${#rtpids[@]} -gt 0 ] || return 0
  local p bad=
  wait "${rtpids[0]}"
  for p in "${rtparts[@]}"; do
    if [ "$(tail -n 1 "$rlog-$p.log" 2>/dev/null)" != "checks failed: 0" ]; then
      [ ! -f "$rlog-$p.log" ] || cat "$rlog-$p.log"
      echo "merge check: FAILED: tools/test_run_tests.sh $p (limit ${rtlimit}s; log $rlog-$p.log)" >&2
      bad=1
    fi
  done
  [ -z "$bad" ] || exit 1
  echo "merge check: tools/test_run_tests.sh list, select, table, except, benches, fresh, short, copy, concurrent, trace, nobus and warm passed"
}

# Step 0: the toy cases of merge_check.sh, each part under the limit of a piece of run_tests.sh.
if [ -n "$selftest" ]; then
  slog=$logs-self
  piece_limit
  sparts=(select select2 record chunks) spids=()
  for part in "${sparts[@]}"; do
    timeout -k 5 "$limit" tools/test_merge_check.sh "$part" >"$slog-$part.log" 2>&1 &
    spids+=($!)
  done
  sbad=
  for part in "${sparts[@]}"; do
    wait "${spids[0]}"
    rc=$?
    spids=("${spids[@]:1}")
    if [ "$rc" -ne 0 ]; then
      cat "$slog-$part.log"
      echo "merge check: FAILED: tools/test_merge_check.sh $part, rc=$rc (limit ${limit}s; log $slog-$part.log)" >&2
      sbad=1
    fi
  done
  # On a failure here step 0b is still waited for, so no part outlives the check.
  [ -z "$sbad" ] || { rt_wait; exit 1; }
  echo "merge check: tools/test_merge_check.sh select, select2, record and chunks passed"
fi
# Step 0c: tools/test_farm_run.sh, the cases of tools/farm_run.sh with a fake pool.sh and job.sh
# (no VM, no build), when either changed. Until FARM-share-load-timeouts a change to farm_run.sh
# ran no test at all. Its limit is max(60, the piece limit): one case waits 15 s by design (the
# pool's retry period) and another 5 s (the load wait); the whole took 22.7 s at load 2 here
# (2026-11-22).
if [ -n "$farmself" ]; then
  flog=$logs-farm-self.log
  piece_limit
  flimit=$((limit > 60 ? limit : 60))
  if ! timeout -k 5 "$flimit" tools/test_farm_run.sh >"$flog" 2>&1; then
    command grep -a -E '^(FAIL|test_farm_run)' "$flog"
    echo "merge check: FAILED: tools/test_farm_run.sh (limit ${flimit}s; log $flog)" >&2
    rt_wait
    exit 1
  fi
  echo "merge check: tools/test_farm_run.sh passed"
fi
rt_wait

# Step 1a: clippy on the selected packages, before the tests (see merge_check.sh's header), less
# those whose clippy passed at the record's commit with the same inputs (merge_check.sh leaves
# them out of --clippy).
if [ -n "$clippy_run" ]; then
  echo "merge check: clippy -D warnings on: $clippy_run"
  cargo clippy -q $(printf -- '-p %s ' $clippy_run) --all-targets -- -D warnings ||
    { echo "merge check: FAILED: clippy (above)" >&2; exit 1; }
fi
exit 0
