#!/bin/bash
# Runs pieces of tools/run_tests.sh of the checkout in the current directory on Colab VMs
# (FARM-main-watch-remote, FARM-merge-check-remote; author, 2026-11-22T10:05Z: "start all future
# jobs in the cloud via Colab"), and prints run_tests.sh's lines for them: each piece's summary
# line `<piece> rc=<n> ...`, BUILD FAILED, the account of each failed piece, and last
# `pieces: <n>, failed: <f>` over all of them. tools/main_watch.sh and tools/merge_check.sh call it.
# Usage, from the checkout's root:
#   tools/farm_run.sh --owner <label> --vms <1-4> --out <new absolute dir> --jobs <n>
#     [--bench] [--full] [--skip-other-kind] [--list] [--terms <file>] [--except <ERE>]
#     [--trace <absolute dir>] [--spec <absolute dir>]
#   --terms <file>  one piece or group name a line, each selected as ^<name>$ (no file: every piece)
#   --except <ERE>  passed to run_tests.sh --except
#   --list          only the build and listing (main_watch's BUILD), on one VM
#   --trace <dir>   run_tests.sh --trace: each VM's read lists land in <dir>/vm<k>, with its
#                   file groups (tools/merge_check.sh --record)
#   --spec <dir>    the spec checkout the VMs get (job.sh's 5th argument; default /home/luke/Work/zed)
# Exit 0 when every piece passed, 1 when a piece or the build failed, 2 on a usage error, 129 when
# a VM's share could not be run after 3 attempts or its run ended past the job's hour: the pieces
# of that share are then not reported, so a caller must not read their absence as passing
# (tools/main_watch.sh treats an exit of 128 or more as a crashed runner).
#
# Design.
#  - The VMs. Up to --vms VMs of owner --owner from /home/luke/Work/wt/colab/pool.sh, shapes hm (8
#    cores, 50 GB), then l4 (12, 52 GB), then v5e (24, 47 GB); std (2 cores, 12 GB) is too small for
#    the suite's pieces. When no VM can be had (pool.sh exits 3 for every shape) it waits 15 s and
#    tries again, without end (FARM.md: never fall back to running here), keeping every VM a round
#    gets, up to the count wanted. 15 s is the period of the pool's reaper, which stops a VM idle
#    for 60 s: with the earlier 2 minutes, VMs freed while main-watch waited were reaped instead of
#    reused (l42 and v5e1, 2026-11-22 11:33Z; author 2026-11-22: "Machines should be claimed and
#    reused by workers when idle"). pool.sh claims under a flock, so two waiting runs never take
#    one VM (FARM-run-retry-15s). Every VM is released, on failure and on a signal too (the trap
#    below).
#  - The shares. With n VMs, VM k runs the pieces at positions k, k + n, k + 2n... of the list that
#    `run_tests.sh --list` makes on it. Every VM builds the same files and lists them in the same
#    order (the table's order, by test binary and step folder), so the shares are disjoint and
#    cover the list; a position, not a name, picks the share, so a library's pieces named with the
#    build's hash (zedc_check-<hash>) need not hash the same on two VMs. A benchmark piece is one
#    whole scaling series (its runs at n and 8n in one process), so a series stays on one VM. The
#    shares are dealt round robin rather than cut into runs, so each VM gets as many of the long
#    groups as the next (l01_26_type_resolution alone is 543 pieces).
#  - On the VM (vm_side, below, sent in the job's tests file as one `!` line) tools/run_tests.sh
#    runs from a copy outside the checkout, so the checkout the tests read stays as packed. The
#    copy's changes, each checked to apply: (1) no short-addresses pieces (short_steps and
#    short_libs empty), since their clone is mounted at the fixed path of zrun, which a VM lacks;
#    (2) with --full, the tools check reads the needs of the folders of tests/full run there only.
#    A `systemd-run` first on PATH runs its command without the scope: a Colab VM is a docker
#    container with no user systemd bus ("Failed to connect to bus", probed 2026-11-22 on std1),
#    and the VM is the job's alone, so the slice's machine-wide memory cap has nothing to share.
#    The list call builds; the share then runs with --pieces, which neither builds nor lists again.
#  - Not run: the short-addresses pieces (tools/run_tests.sh --short-groups, as short-<group>) and
#    the folders of tests/full whose needs file names a tool a VM lacks (podman, systemd-run with a
#    user bus, clang, ld.lld, gdb, qemu: s00_01_tools and s09_release on 2026-11-22; vm_tools below
#    lists what a VM has). No build, test or benchmark runs on this machine (author, 2026-11-22,
#    after main-watch's local bench run at 11:15Z), so these pieces, 5 of about 3,000 (about 27 s
#    of 2,350 s of piece time in main-watch's run of 2026-11-22T09:48Z), go untested, named on a
#    line `farm: not run, ...`, until a VM image has podman and a user systemd and the
#    short-addresses clone can be mounted on a VM (FARM-local-residue). They are neither passed
#    nor failed: they print no summary line.
#  - Benchmarks: a VM has no hardware instruction counter (perf_event_open of instructions gives
#    ENOENT, probed 2026-11-22), so each benchmark counts its instructions in software under
#    DynamoRIO's client zed_icount, which job.sh's VM setup builds and names in ZED_METER_DRRUN and
#    ZED_METER_ICOUNT (BENCH-vm-no-instruction-counter; tests/src/scaling.rs). Where that build
#    failed (the job's out/icount.log says so), they fall back on the task clock, which is
#    noisier. A benchmark that fails is run once more on the same VM at once, alone; that
#    second run's line is the verdict, and the first run's failed line is kept prefixed
#    `farm: first run: `, which no reader of summary lines takes for one.
#  - A share whose job did not run to the end (job.sh exit 2, 4 or 5, or no output) is run again on
#    another VM, up to 3 attempts.
# Cost here: packing the checkout once per VM (tar of the tracked and untracked files, about 2,500
# files, 63 MB) and the polls of job.sh; the build and the pieces run on the VMs.
set -u -o pipefail
die() { echo "farm_run: $*" >&2; exit 2; }
# FARM_RUN_COLAB_DIR: another pool.sh and job.sh, tools/test_farm_run.sh's fakes.
colab_dir=${FARM_RUN_COLAB_DIR:-/home/luke/Work/wt/colab}
[[ $colab_dir == /?* ]] || die "FARM_RUN_COLAB_DIR must be an absolute path, got '$colab_dir'"
# The tools a Colab VM has (probed 2026-11-22 on std1: bash, sh, ip, tc and unshare --user work;
# cargo and rustc come from job.sh's rustup).
vm_tools=" bash sh unshare ip tc cargo rustc "
owner= vms= out= jobs= kind=test full= skip_other= list= terms= except= trace= spec=
while [ $# -gt 0 ]; do
  case $1 in
    --owner | --vms | --out | --jobs | --terms | --except | --trace | --spec)
      [ $# -ge 2 ] && [ -n "$2" ] || die "$1 needs a non-empty value"
      case $1 in
        --owner) owner=$2 ;; --vms) vms=$2 ;; --out) out=$2 ;; --jobs) jobs=$2 ;;
        --terms) terms=$2 ;; --except) except=$2 ;; --trace) trace=$2 ;;
        --spec) spec=$2 ;;
      esac
      shift
      ;;
    --bench) kind=bench ;;
    --full) full=1 ;;
    --skip-other-kind) skip_other=1 ;;
    --list) list=1 ;;
    *) die "unknown argument '$1' (usage: see the head of tools/farm_run.sh)" ;;
  esac
  shift
done
[[ $owner =~ ^[A-Za-z0-9._-]+$ ]] || die "--owner must be a label of [A-Za-z0-9._-], got '$owner'"
[[ $vms =~ ^[1-4]$ ]] || die "--vms must be 1 to 4, got '$vms'"
[[ $jobs =~ ^[1-9][0-9]*$ ]] || die "--jobs must be a positive number, got '$jobs'"
[[ $out == /?* ]] && [ ! -e "$out" ] || die "--out must be an absolute path that does not exist yet, got '$out'"
[ -z "$terms" ] || [ -s "$terms" ] || die "--terms file '$terms' is missing or empty"
[ -z "$trace" ] || [[ $trace == /?* ]] || die "--trace must be an absolute path, got '$trace'"
[ -z "$spec" ] || { [[ $spec == /?* ]] && [ -d "$spec" ]; } || die "--spec must be an absolute path of a directory, got '$spec'"
[ -x tools/run_tests.sh ] || die "run from a checkout's root (no tools/run_tests.sh in $PWD)"
for f in pool.sh job.sh; do [ -x "$colab_dir/$f" ] || die "no $colab_dir/$f"; done
if [ -n "$except" ]; then
  { [[ x =~ $except ]]; } 2>/dev/null
  [ $? != 2 ] || die "--except is not an extended regular expression: $except"
fi
wt=$(pwd -P)
[[ $wt == /?* ]] || die "the checkout's path '$wt' is not absolute"
mkdir -p "$out" || die "cannot create $out"

# The ERE that selects each name of the file $1 alone, ^<name>$|^<name>$ (each its own
# alternative: run_tests.sh reads the text before the first :: of an alternative as a group).
ere_of() { sed 's/[][\.*^$+?(){}|/]/\\&/g; s/.*/^&$/' "$1" | paste -sd'|'; }

# Which pieces run here: short-<group> for each short-addresses group, and full-<folder> for each
# folder of tests/full whose needs a VM lacks.
local_full=() vm_full=()
for d in tests/full/*/; do
  [ -d "$d" ] || continue
  n=$(basename "$d")
  [[ $n =~ ^[A-Za-z0-9_]+$ ]] || die "unexpected folder name tests/full/$n"
  ok=1
  if [ -f "$d/needs" ]; then
    while read -r t; do
      [ -z "$t" ] || [[ $vm_tools == *" $t "* ]] || ok=
    done < <(tr -s ' \t' '\n\n' <"$d/needs")
  fi
  if [ -n "$ok" ]; then vm_full+=("$n"); else local_full+=("$n"); fi
done
short_groups=$(tools/run_tests.sh --short-groups) || die "tools/run_tests.sh --short-groups failed"
# here_name <name>: whether the piece or group <name> runs here.
here_name() {
  local g
  for g in $short_groups; do
    [[ $1 == "short-$g" || $1 == "short-$g::"* ]] && return 0
  done
  for g in "${local_full[@]}"; do
    [[ $1 == "full-$g" || $1 == "full-$g::"* ]] && return 0
  done
  return 1
}
: >"$out/terms.here"
: >"$out/terms.vm"
if [ -n "$terms" ]; then
  while IFS= read -r t; do
    [ -n "$t" ] || continue
    [[ $t != *' '* ]] || die "a term with a space: '$t'"
    if here_name "$t"; then echo "$t" >>"$out/terms.here"; else echo "$t" >>"$out/terms.vm"; fi
  done <"$terms"
elif [ -z "$list" ]; then
  for g in $short_groups; do echo "short-$g" >>"$out/terms.here"; done
  [ -z "$full" ] || for g in "${local_full[@]}"; do echo "full-$g" >>"$out/terms.here"; done
fi
# The VM's --only (empty: every piece) and --except, which also leaves out the pieces run here.
vm_only= vm_except=$except
[ ! -s "$out/terms.vm" ] || vm_only=$(ere_of "$out/terms.vm")
if [ -n "$full" ] && [ ${#local_full[@]} -gt 0 ]; then
  printf 'full-%s\n' "${local_full[@]}" >"$out/full.here"
  vm_except=${vm_except:+$vm_except|}$(ere_of "$out/full.here")
fi
run_vm=1
[ -z "$terms" ] || [ -s "$out/terms.vm" ] || run_vm=

# vm_side <k> <n> <kind> <full 0|1> <skip-other 0|1> <list 0|1> <trace 0|1> <only> <except>
#   <vm full folders, space-separated>: runs on the VM in the checkout's root (job.sh's `!` line);
# see the Design above. Exit as run_tests.sh's run of the share.
vm_side() {
  set -u -o pipefail
  local k=${1-} n=${2-} kind=${3-} full=${4-} skip=${5-} list=${6-} trace=${7-} only=${8-} except=${9-} vmfull=${10-}
  [[ $k =~ ^[1-9][0-9]*$ && $n =~ ^[1-9][0-9]*$ && $k -le $n ]] || { echo "vm_side: bad share '$k/$n'"; return 2; }
  [[ $kind == test || $kind == bench ]] || { echo "vm_side: bad kind '$kind'"; return 2; }
  [[ $full$skip$list$trace =~ ^[01]{4}$ ]] || { echo "vm_side: bad flags"; return 2; }
  [ -x tools/run_tests.sh ] || { echo "vm_side: no tools/run_tests.sh in $PWD"; return 2; }
  # FARM_VM_JOB: the job's directory, /content/job on a VM (job.sh); tools/test_farm_run.sh's own.
  local J=${FARM_VM_JOB:-/content/job} w cores a=() rc d
  [[ $J == /?* ]] || { echo "vm_side: the job directory '$J' is not absolute"; return 2; }
  w=$J/farm-$k
  mkdir -p "$w/bin" "$w/cache/zed-test-deps" || return 2
  cores=$(nproc)
  [[ $cores =~ ^[1-9][0-9]*$ ]] || { echo "vm_side: nproc gave '$cores'"; return 2; }
  printf '%s\n' '#!/bin/bash' '# The scope options of run_tests.sh, then the command, run without a scope.' \
    'while [ $# -gt 0 ] && [ "${1#--}" != "$1" ]; do shift; done' 'exec "$@"' >"$w/bin/systemd-run"
  chmod +x "$w/bin/systemd-run" || return 2
  # tools/run_tests.sh is written for GNU awk (match() with an array, in the parse of --trace's
  # strace output); a Colab VM's awk is mawk, which refused that program and left every .reads file
  # empty (end-to-end run of 2026-11-22). gawk is installed once per VM and put first as awk.
  if ! command -v gawk >/dev/null; then
    apt-get install -y -qq gawk >"$w/gawk-install.log" 2>&1 ||
      { apt-get update -qq && apt-get install -y -qq gawk; } >>"$w/gawk-install.log" 2>&1 ||
      { echo "vm_side: gawk could not be installed"; return 2; }
  fi
  ln -sfn "$(command -v gawk)" "$w/bin/awk" || return 2
  export PATH=$w/bin:$PATH XDG_CACHE_HOME=$w/cache
  : >"$w/cache/zed-test-deps/done"
  : >"$w/needs"
  for d in $vmfull; do [ ! -f "tests/full/$d/needs" ] || cat "tests/full/$d/needs" >>"$w/needs"; done
  sed -e 's/^short_steps=.*/short_steps=""/' -e 's/^short_libs=.*/short_libs=""/' \
    -e "s|cat tests/full/\\*/needs|cat $w/needs|" tools/run_tests.sh >"$w/run_tests.sh" || return 2
  [ "$(grep -c -x -e 'short_steps=""' -e 'short_libs=""' "$w/run_tests.sh")" = 2 ] &&
    grep -q -F "cat $w/needs" "$w/run_tests.sh" ||
    { echo "vm_side: tools/run_tests.sh no longer has the lines farm_run.sh changes in its copy"; return 2; }
  [ "$kind" = test ] || a+=(--bench)
  [ "$full" = 0 ] || a+=(--full)
  local l=("${a[@]}")
  [ "$skip" = 0 ] || l+=(--skip-other-kind)
  [ -z "$only" ] || l+=(--only "$only")
  [ -z "$except" ] || l+=(--except "$except")
  bash "$w/run_tests.sh" --logs "$w/list" "${l[@]}" --list "$cores" >"$w/list.out" 2>&1
  rc=$?
  if [ "$rc" != 0 ] || [ "$list" = 1 ]; then
    cat "$w/list.out"
    return "$rc"
  fi
  # --skip-other-kind with nothing of this kind selected: nothing to run.
  if [ ! -s "$w/list/latest/pieces" ]; then
    cat "$w/list.out"
    return 0
  fi
  awk -v k="$k" -v n="$n" '(NR - 1) % n == k - 1' "$w/list/latest/pieces" >"$w/share"
  # Read by farm_run.sh, which checks that the shares cover the list and each reports its pieces.
  echo "farm: share $k of $n: $(wc -l <"$w/share") of $(wc -l <"$w/list/latest/pieces") pieces"
  [ -s "$w/share" ] || return 0
  if [ "$trace" = 1 ]; then
    # A VM's package lists may be missing or stale: a failed install updates them and tries once more.
    command -v strace >/dev/null || apt-get install -y -qq strace >"$w/strace-install.log" 2>&1 ||
      { apt-get update -qq && apt-get install -y -qq strace; } >>"$w/strace-install.log" 2>&1 ||
      { echo "vm_side: strace could not be installed"; return 2; }
    mkdir -p "$J/out/trace-$k" || return 2
    awk 'NR == FNR { p[$1] = 1; next } $3 in p { print $3, $1, $2 }' "$w/share" "$w/list/latest/chosen" \
      >"$J/out/trace-$k/groups"
    a+=(--trace "$J/out/trace-$k")
  fi
  bash "$w/run_tests.sh" --logs "$w/run" "${a[@]}" --pieces "$w/share" "$cores" >"$w/r1.out" 2>&1
  rc=$?
  if [ "$kind" = bench ] && [ "$rc" = 1 ] &&
    awk '$2 ~ /^rc=[1-9]/ { print $1 }' "$w/r1.out" | sort -u >"$w/failed" && [ -s "$w/failed" ]; then
    awk 'NR == FNR { f[$1] = 1; next } $1 in f' "$w/failed" "$w/share" >"$w/again"
    if [ -s "$w/again" ]; then
      bash "$w/run_tests.sh" --logs "$w/again-run" "${a[@]}" --pieces "$w/again" 1 >"$w/r2.out" 2>&1
      rc=$?
      awk '$2 ~ /^rc=[1-9]/ || /^pieces: / { $0 = "farm: first run: " $0 } { print }' "$w/r1.out"
      echo "farm: each failed benchmark run again once, alone, on the same VM; its verdict:"
      cat "$w/r2.out"
      return "$rc"
    fi
  fi
  cat "$w/r1.out"
  return "$rc"
}
vm_script=$out/vm_side.sh
{
  declare -f vm_side
  echo 'vm_side "$@"'
} >"$vm_script" || die "cannot write $vm_script"
vm_b64=$(base64 -w0 "$vm_script") && [ -n "$vm_b64" ] || die "cannot encode $vm_script"

# The VMs held, released at exit.
held=()
release_all() {
  local v
  for v in "${held[@]}"; do
    [[ $v =~ ^(hm|std|l4|v5e)[0-9]+$ ]] || continue
    "$colab_dir/pool.sh" release "$v" >>"$out/pool.log" 2>&1 || echo "farm_run: release of $v failed (see $out/pool.log)" >&2
  done
  held=()
}
# The running job.sh processes (pids), stopped first at exit, so none polls a released VM.
kids=()
stop_all() {
  local p
  for p in "${kids[@]}"; do [[ $p =~ ^[0-9]+$ ]] && [ "$p" -gt 1 ] && kill "$p" 2>/dev/null; done
  release_all
}
trap stop_all EXIT
trap 'exit 143' TERM
trap 'exit 130' INT
trap 'exit 129' HUP
# acquire <count>: adds up to <count> VMs to held, at least one, waiting 15 s between rounds while
# none can be had (see "The VMs" above).
acquire() {
  local want=$1 got=0 shape v
  while :; do
    for shape in hm l4 v5e; do
      while [ "$got" -lt "$want" ]; do
        v=$("$colab_dir/pool.sh" acquire "$shape" "$owner" 2>>"$out/pool.log") || break
        [[ $v =~ ^(hm|std|l4|v5e)[0-9]+$ ]] || { echo "farm_run: pool.sh gave the VM name '$v'" >&2; break; }
        held+=("$v")
        got=$((got + 1))
      done
    done
    [ "$got" -eq 0 ] || return 0
    echo "farm: no Colab VM free for $owner; trying again in 15 s ($(date -u +%FT%TZ))"
    sleep 15
  done
}

rc_all=0
: >"$out/report"
# The VM shares.
if [ -n "$run_vm" ]; then
  want=$vms
  [ -z "$list" ] || want=1
  acquire "$want"
  n=${#held[@]}
  declare -A tries=() done_k=()
  pending=$(seq 1 "$n")
  while [ -n "$pending" ]; do
    [ ${#held[@]} -gt 0 ] || acquire "$(wc -w <<<"$pending")"
    i=0 started=()
    for k in $pending; do
      [ "$i" -lt ${#held[@]} ] || break
      v=${held[$i]}
      i=$((i + 1))
      tries[$k]=$((${tries[$k]:-0} + 1))
      d=$out/vm$k-${tries[$k]}
      mkdir -p "$d" || die "cannot create $d"
      line=$(printf '!printf %%s %s | base64 -d >/content/job/farm_vm.sh && bash /content/job/farm_vm.sh' "$vm_b64")
      for x in "$k" "$n" "$kind" "${full:-0}" "${skip_other:-0}" "${list:-0}" "$([ -n "$trace" ] && echo 1 || echo 0)" \
        "$vm_only" "$vm_except" "${vm_full[*]}"; do
        line+=" $(printf '%q' "$x")"
      done
      printf '%s\n' "$line" >"$d/tests.txt"
      echo "farm: share $k of $n on $v (attempt ${tries[$k]}; logs $d)"
      "$colab_dir/job.sh" "$v" "$wt" "$d/job" "$d/tests.txt" ${spec:+"$spec"} >"$d/job.out" 2>&1 &
      started+=("$k:$!")
      kids+=("$!")
    done
    for s in "${started[@]}"; do
      k=${s%%:*}
      wait "${s#*:}"
      echo $? >"$out/vm$k-${tries[$k]}/job.rc"
    done
    kids=()
    release_all
    next=
    for s in "${started[@]}"; do
      k=${s%%:*}
      d=$out/vm$k-${tries[$k]}
      jrc=$(cat "$d/job.rc" 2>/dev/null)
      log=$d/job/out/1.log
      lrc=$(awk -F '\t' 'NR == 1 { print $2 }' "$d/job/summary.tsv" 2>/dev/null)
      if [[ ! $jrc =~ ^[01]$ ]] || [ ! -f "$log" ] || [[ ! $lrc =~ ^[0-9]+$ ]]; then
        echo "farm: share $k of $n did not run to its end (job.sh exit ${jrc:-none}; $d/job.out)"
        if [ "${tries[$k]}" -ge 3 ]; then
          echo "farm: share $k of $n lost after 3 attempts; its pieces are not reported"
          rc_all=129
        else
          next+=" $k"
        fi
        continue
      fi
      done_k[$k]=$lrc
    done
    # The shares not started this round for want of VMs, then those to run again.
    for k in $pending; do [[ " ${started[*]%%:*} " == *" $k "* ]] || next+=" $k"; done
    pending=$(tr ' ' '\n' <<<"$next" | sed '/^$/d' | sort -n -u | tr '\n' ' ')
    pending=${pending% }
  done
  for k in $(seq 1 "$n"); do
    [ -n "${done_k[$k]:-}" ] || continue
    d=$out/vm$k-${tries[$k]}
    cat "$d/job/out/1.log" >>"$out/report"
    lrc=${done_k[$k]}
    # job.sh's `!` line runs under `timeout 3600`: 124 is the share stopped past the hour.
    if [ "$lrc" = 124 ] || [ "$lrc" -ge 128 ]; then
      echo "farm: share $k of $n ended with $lrc (past the job's hour or killed); its pieces not reported are unknown" >>"$out/report"
      rc_all=129
    elif [ "$lrc" != 0 ] && [ "$rc_all" = 0 ]; then
      rc_all=1
    fi
    if [ -n "$trace" ] && [ -d "$d/job/out/trace-$k" ]; then
      mkdir -p "$trace" && cp -r "$d/job/out/trace-$k" "$trace/vm$k" || die "cannot copy the trace of share $k"
    fi
  done
  # Every share that listed must report each of its pieces once, and the shares' sizes must add
  # up to the list's: a piece neither reported nor counted would read as passing. (A share whose
  # list call failed prints no share line, and its failure is already counted above.)
  cover=$(awk '
    /^farm: share [0-9]+ of [0-9]+: [0-9]+ of [0-9]+ pieces$/ { k = $3; m[k] = $6; t[k] = $8; next }
    /^farm: / { next }
    $2 ~ /^rc=[0-9]+$/ && k != "" { r[k]++ }
    END {
      for (k in m) {
        if (r[k] + 0 != m[k]) print "share " k " ran " r[k] + 0 " of its " m[k] " pieces"
        s += m[k]; if (tot == "") tot = t[k]; else if (t[k] != tot) print "shares listed " tot " and " t[k] " pieces"
      }
      if (tot != "" && length(m) == '"$n"' && s != tot) print "the shares hold " s " of the " tot " pieces listed"
    }' "$out/report")
  if [ -n "$cover" ]; then
    echo "farm: the VMs did not run the listed pieces each once: $cover" | paste -sd';' >>"$out/report"
    [ "$rc_all" != 0 ] || rc_all=1
  fi
fi
# The pieces no VM can run are not run at all, and named (see "Not run" above).
if [ -s "$out/terms.here" ] && [ -z "$list" ]; then
  echo "farm: not run, no VM has what they need (FARM-local-residue): $(paste -sd' ' "$out/terms.here")" >>"$out/report"
fi
cat "$out/report"
p=$(awk '$2 ~ /^rc=[0-9]+$/' "$out/report" | wc -l)
f=$(awk '$2 ~ /^rc=[0-9]+$/ && $2 != "rc=0"' "$out/report" | wc -l)
echo "pieces: $p, failed: $f"
[ "$f" = 0 ] || [ "$rc_all" != 0 ] || rc_all=1
exit "$rc_all"
