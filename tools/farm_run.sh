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
#   --commands <file>  runs no piece: runs each line of <file> with bash on one VM, in order, in
#                   the build root of the short-addresses pieces, with FARM_OUT a directory that
#                   comes back under --out (tools/merge_check.sh's steps 0b, 0, 0c and 1a,
#                   FARM-merge-check-clippy-selftests-remote); see vm_cmd
# Exit 0 when every piece passed, 1 when a piece or the build failed or a share did not report each
# piece it was given once (a line `farm: FAILED: share <k> of <n> on <VM> ...` names it and the
# failing step: FARM-setup-fail-silent), 2 on a usage error, 129 when
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
#    copy's changes, each checked to apply: (1) when no short-addresses piece is selected, none
#    (short_steps and short_libs empty), so the list call builds no clone; (2) with --full, the
#    tools check reads the needs of the folders of tests/full run there only.
#    A `systemd-run` first on PATH runs its command without the scope: a Colab VM is a docker
#    container with no user systemd bus ("Failed to connect to bus", probed 2026-11-22 on std1),
#    and the VM is the job's alone, so the slice's machine-wide memory cap has nothing to share.
#    The list call builds; the share then runs with --pieces, which neither builds nor lists again.
#  - The short-addresses pieces (tools/run_tests.sh --short-groups, as short-<group>) run on VMs
#    since FARM-short-pieces-on-vm-tmpfs, in a mount namespace with the checkout at zrun's fixed
#    path and a tmpfs for the clone's upper layer (vm_side); short-zed_kernel too since
#    TEST-short-zed_kernel-split cut it into pieces that fit (run_tests.sh's short_alone). Not run:
#    the folders of tests/full whose needs file names a tool a VM lacks (vm_tools below lists what a VM has; s00_01_tools and
#    s09_release run on VMs since FARM-local-only-pieces-on-vm, with the tools job.sh installs,
#    rootless podman and tools/fetch_test_deps.sh, vm_side). No build, test or benchmark runs on
#    this machine (author, 2026-11-22, after main-watch's local bench run at 11:15Z), so these
#    pieces go untested, named on a line `farm: not run, ...` (FARM-local-residue). They are
#    neither passed nor failed: they print no summary line.
#  - Benchmarks: a VM has no hardware instruction counter (perf_event_open of instructions gives
#    ENOENT, probed 2026-11-22), so each benchmark counts its instructions in software under
#    DynamoRIO's client zed_icount, which job.sh's VM setup builds and names in ZED_METER_DRRUN and
#    ZED_METER_ICOUNT (BENCH-vm-no-instruction-counter; tests/src/scaling.rs). Where that build
#    failed (the job's out/icount.log says so), they fall back on the task clock, which is
#    noisier and held to twice the limit; such a run prints `farm: benchmarks measured processor
#    time, not instructions, on <VM> ...` and exits 1 (FARM-icount-fallback-silent). A benchmark that fails is run once more on the same VM at once, alone; that
#    second run's line is the verdict, and the first run's failed line is kept prefixed
#    `farm: first run: `, which no reader of summary lines takes for one.
#  - Tests: a test piece stopped by its limit (not one that failed otherwise) is run once more in
#    the same way, alone, after the load has fallen, and named on a line `farm: stopped by its
#    limit under load, passed alone: ...` when it passed then (FARM-share-load-timeouts; vm_side).
#  - A share whose job did not run to the end (job.sh exit 2, 4, 5, 6 or 7, or no output) is run again on
#    another VM, up to 3 attempts.
# Cost here: packing the checkout once per VM (tar of the tracked and untracked files, about 2,500
# files, 63 MB) and the polls of job.sh; the build and the pieces run on the VMs.
set -u -o pipefail
die() { echo "farm_run: $*" >&2; exit 2; }
# FARM_RUN_COLAB_DIR: another pool.sh and job.sh, tools/test_farm_run.sh's fakes.
colab_dir=${FARM_RUN_COLAB_DIR:-/home/luke/Work/wt/colab}
[[ $colab_dir == /?* ]] || die "FARM_RUN_COLAB_DIR must be an absolute path, got '$colab_dir'"
# The tools a Colab VM has (probed 2026-11-22 on std1: bash, sh, ip, tc and unshare --user work;
# cargo and rustc come from job.sh's rustup; on std2: clang, ld.lld, qemu-aarch64, qemu-riscv64,
# gdb-multiarch and podman from job.sh's setup, podman run rootless and gdb as gdb-multiarch by
# vm_side, and systemd-run is vm_side's stub).
vm_tools=" bash sh unshare ip tc cargo rustc clang ld.lld qemu-aarch64 qemu-riscv64 gdb podman systemd-run "
owner= vms= out= jobs= kind=test full= skip_other= list= terms= except= trace= spec= commands=
while [ $# -gt 0 ]; do
  case $1 in
    --owner | --vms | --out | --jobs | --terms | --except | --trace | --spec | --commands)
      [ $# -ge 2 ] && [ -n "$2" ] || die "$1 needs a non-empty value"
      case $1 in
        --owner) owner=$2 ;; --vms) vms=$2 ;; --out) out=$2 ;; --jobs) jobs=$2 ;;
        --terms) terms=$2 ;; --except) except=$2 ;; --trace) trace=$2 ;;
        --spec) spec=$2 ;; --commands) commands=$2 ;;
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
[ -z "$commands" ] || [ -s "$commands" ] || die "--commands file '$commands' is missing or empty"
[ -z "$commands" ] || [ -z "$terms$list$trace$full$except" ] || die "--commands runs no piece: no --terms, --list, --trace, --full or --except with it"
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

# Which pieces run here (that is, are not run): full-<folder> for each folder of tests/full whose
# needs a VM lacks.
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
# here_name <name>: whether the piece or group <name> runs here (is not run). short-zed_kernel
# was one such until TEST-short-zed_kernel-split (2026-11-22): see run_tests.sh's short_alone.
here_name() {
  local g
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
  [ -z "$full" ] || for g in "${local_full[@]}"; do echo "full-$g" >>"$out/terms.here"; done
fi
# Whether the VMs select short-addresses pieces (vm_side's short): every piece but in --list
# (whose list then leaves them out, as their listing builds the clone), or a term that names one.
vm_short=0
if [ -z "$terms" ]; then
  [ -n "$list" ] || vm_short=1
elif grep -q '^short-' "$out/terms.vm"; then
  vm_short=1
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

# vm_ns <R> <arguments>: runs this script ($0, job.sh's farm_vm.sh) again with <arguments>, in the
# checkout's root bound at R, in a mount namespace of its own with a tmpfs at R/build and the
# target directory at R/build/cargo: the build root of the short-addresses pieces (see vm_side).
vm_ns() {
  local R=$1 tgt=${CARGO_TARGET_DIR:-$PWD/build/cargo} ns=(unshare -m --propagation private)
  shift
  [[ $tgt == /?* ]] || { echo "vm_side: the target directory '$tgt' is not absolute"; return 2; }
  [ "$(id -u)" = 0 ] || ns=(unshare -U -r -m --propagation private)
  mkdir -p "$tgt" "$PWD/build" "$R" ||
    { echo "vm_side: making the mount points for the short-addresses pieces failed"; return 2; }
  # The tmpfs is mounted on R/build, not on R/build/short-clone: run_tests.sh drops a clone made
  # from another build by renaming build/short-clone, and a mount point cannot be renamed
  # ("mv: cannot move ...: Device or resource busy", l43 2026-11-22, a fresh tmpfs having no
  # stamp). tools/test_farm_run.sh's stub renames it.
  "${ns[@]}" bash -c 'mount --bind "$1" "$2" && mount -t tmpfs tmpfs "$2/build" &&
    mkdir "$2/build/cargo" && mount --bind "$3" "$2/build/cargo" ||
    { echo "vm_side: the mounts of the short-addresses build root failed"; exit 2; }
    cd "$2" || { echo "vm_side: cd to $2 failed"; exit 2; }
    shift 4
    CARGO_TARGET_DIR=$PWD/build/cargo exec bash "$0" "$@"' "$0" "$PWD" "$R" "$tgt" _ "$@"
}

# vm_pkg <package> <log dir>: installs the Ubuntu package of that name on the VM when its command
# of the same name is missing, the log in <log dir>/<package>-install.log. A VM's package lists
# may be missing or stale: a failed install updates them and tries once more.
vm_pkg() {
  command -v "$1" >/dev/null && return 0
  apt-get install -y -qq "$1" >"$2/$1-install.log" 2>&1 ||
    { apt-get update -qq && apt-get install -y -qq "$1"; } >>"$2/$1-install.log" 2>&1 ||
    { echo "vm_side: $1 could not be installed"; return 2; }
}

# vm_cmd <command, base64>: runs one command of --commands on the VM with bash, in the build root
# of the short-addresses pieces (vm_ns), with FARM_OUT the job's out/ directory, which job.sh
# brings back, and with the tools a share has (vm_side): gawk first as awk, and strace, which
# tools/test_run_tests.sh trace needs (its three --trace cases found no reads on hm3 without them,
# 2026-11-22). The spec is also linked as /home/luke/Work/zed, beside an ancestor of the build root
# as on this machine, when no such directory is there: tests/src/spec.rs finds the spec beside the
# checkout or an ancestor when ZED_SPEC_DIR is unset, which test_run_tests trace's case "the spec
# beside" checks (it found nothing on std1, the spec being only at ZED_SPEC_DIR, 2026-11-22).
# Exit as the command's.
vm_cmd() {
  set -u -o pipefail
  local R=${FARM_VM_BUILD_ROOT:-/home/luke/Work/wt/.build-root} J=${FARM_VM_JOB:-/content/job} c
  [[ $R == /?* ]] || { echo "vm_side: the build root '$R' is not absolute"; return 2; }
  [[ $J == /?* ]] || { echo "vm_side: the job directory '$J' is not absolute"; return 2; }
  if [ "$PWD" != "$R" ]; then
    vm_ns "$R" cmd "${1-}"
    return
  fi
  c=$(printf %s "${1-}" | base64 -d) && [ -n "$c" ] || { echo "vm_side: the command is not base64"; return 2; }
  mkdir -p "$J/out" "$J/cmd/bin" || { echo "vm_side: mkdir of $J/out or $J/cmd/bin failed"; return 2; }
  vm_pkg gawk "$J/cmd" && vm_pkg strace "$J/cmd" || return 2
  ln -sfn "$(command -v gawk)" "$J/cmd/bin/awk" || { echo "vm_side: linking gawk as awk failed"; return 2; }
  if [ ! -e /home/luke/Work/zed ] && [ -f "${ZED_SPEC_DIR-}/DESIGN.md" ]; then
    ln -s "$ZED_SPEC_DIR" /home/luke/Work/zed || { echo "vm_side: linking the spec as /home/luke/Work/zed failed"; return 2; }
  fi
  PATH=$J/cmd/bin:$PATH FARM_OUT=$J/out bash -c "$c"
}

# vm_side <k> <n> <kind> <full 0|1> <skip-other 0|1> <list 0|1> <trace 0|1> <only> <except>
#   <vm full folders, space-separated> <short 0|1>: runs on the VM in the checkout's root (job.sh's
# `!` line); see the Design above. Exit as run_tests.sh's run of the share.
vm_side() {
  set -u -o pipefail
  local k=${1-} n=${2-} kind=${3-} full=${4-} skip=${5-} list=${6-} trace=${7-} only=${8-} except=${9-} vmfull=${10-} short=${11-}
  [[ $k =~ ^[1-9][0-9]*$ && $n =~ ^[1-9][0-9]*$ && $k -le $n ]] || { echo "vm_side: bad share '$k/$n'"; return 2; }
  [[ $kind == test || $kind == bench ]] || { echo "vm_side: bad kind '$kind'"; return 2; }
  [[ $full$skip$list$trace$short =~ ^[01]{5}$ ]] || { echo "vm_side: bad flags"; return 2; }
  [ -x tools/run_tests.sh ] || { echo "vm_side: no tools/run_tests.sh in $PWD"; return 2; }
  # The short-addresses pieces (FARM-short-pieces-on-vm-tmpfs). run_tests.sh builds them only in
  # the checkout's root at zrun's fixed path, R = /home/luke/Work/wt/.build-root, in an overlay over
  # R/build/cargo whose upper and work directories lie in R/build/short-clone. On a VM that upper
  # directory would be on /content, itself an overlayfs, where the kernel refuses an overlay's upper
  # layer ("wrong fs type, bad option", probed on l42 2026-11-22 by b22-farm1); on a tmpfs it mounts,
  # index=on included. So with short = 1 the share runs in a mount namespace of its own (unshare;
  # as root on a VM, whose docker container has CAP_SYS_ADMIN, CapEff a82c25fb, bit 21; with a user
  # namespace too where not root, as in tools/test_farm_run.sh) in which the checkout is bound at
  # R, a tmpfs at R/build, and the target directory (CARGO_TARGET_DIR, /content/target from job.sh)
  # at R/build/cargo (probed on l43 2026-11-22: the overlay mounts with its upper and work on such a
  # tmpfs, and a second mount of it is refused). The namespace ends with the share, and the tmpfs with
  # it, so each share builds the short-addresses crates once (its list call) and keeps nothing.
  # FARM_VM_BUILD_ROOT: another R, tools/test_farm_run.sh's.
  local R=${FARM_VM_BUILD_ROOT:-/home/luke/Work/wt/.build-root}
  [[ $R == /?* ]] || { echo "vm_side: the build root '$R' is not absolute"; return 2; }
  if [ "$short" = 1 ] && [ "$PWD" != "$R" ]; then
    vm_ns "$R" "$@"
    return
  fi
  # FARM_VM_JOB: the job's directory, /content/job on a VM (job.sh); tools/test_farm_run.sh's own.
  local J=${FARM_VM_JOB:-/content/job} w cores a=() rc d
  [[ $J == /?* ]] || { echo "vm_side: the job directory '$J' is not absolute"; return 2; }
  w=$J/farm-$k
  # Every step that can fail prints a line `vm_side: <step> failed ...`, which farm_run.sh quotes
  # with the share and the VM (FARM-setup-fail-silent).
  mkdir -p "$w/bin" "$w/cache/zed-test-deps" "$J/out" || { echo "vm_side: mkdir of $w failed"; return 2; }
  cores=$(nproc)
  [[ $cores =~ ^[1-9][0-9]*$ ]] || { echo "vm_side: nproc gave '$cores'"; return 2; }
  printf '%s\n' '#!/bin/bash' '# The scope options of run_tests.sh, then the command, run without a scope.' \
    'while [ $# -gt 0 ] && [ "${1#--}" != "$1" ]; do shift; done' 'exec "$@"' >"$w/bin/systemd-run" &&
    chmod +x "$w/bin/systemd-run" || { echo "vm_side: writing the systemd-run stub failed"; return 2; }
  # tools/run_tests.sh is written for GNU awk (match() with an array, in the parse of --trace's
  # strace output); a Colab VM's awk is mawk, which refused that program and left every .reads file
  # empty (end-to-end run of 2026-11-22). gawk is installed once per VM and put first as awk.
  vm_pkg gawk "$w" || return 2
  ln -sfn "$(command -v gawk)" "$w/bin/awk" || { echo "vm_side: linking gawk as awk failed"; return 2; }
  # The folders of tests/full here whose needs name podman (s00_01_tools and s09_release) read
  # what tools/fetch_test_deps.sh fetches and builds: the sysroots, the pinned rustc, alpine and
  # the rustup image. It runs before the share, into a cache kept across the jobs on this VM
  # (FARM_VM_CACHE, /content/farm-cache; a second run checks each file's SHA-256 and builds the
  # image from podman's layer cache). Podman runs as the user zp that job.sh sets up, rootless:
  # as root it cannot run in a Colab VM's docker container (no CAP_NET_ADMIN, a read-only
  # /sys/fs/cgroup; job.sh has the probe), and in its own storage, since CONTAINERS_STORAGE_CONF
  # names root's. gdb is gdb-multiarch: Ubuntu's gdb has no aarch64 or riscv (probed on std2,
  # 2026-11-22; FARM-local-only-pieces-on-vm). Other folders get an empty deps directory, as before.
  # Only when the run can hold such a folder's piece: --only empty or naming full-<folder> (it is
  # made of the names, ere_of), and --except not leaving it out.
  local cache=$w/cache deps= t0
  for d in $vmfull; do
    [ -f "tests/full/$d/needs" ] && tr -s ' \t' '\n\n' <"tests/full/$d/needs" | grep -q -x podman || continue
    { [ -z "$only" ] || [[ $only == *"full-$d"* ]]; } && { [ -z "$except" ] || [[ ! full-$d =~ $except ]]; } && deps=1
  done
  if [ "$full" = 1 ] && [ -n "$deps" ]; then
    printf '%s\n' '#!/bin/bash' '# podman as the user zp, rootless, in its own storage (tools/farm_run.sh vm_side).' \
      'mkdir -p /tmp/zp-run && chown zp: /tmp/zp-run && chmod 700 /tmp/zp-run || exit 125' \
      'exec runuser -u zp -- env -u CONTAINERS_STORAGE_CONF XDG_RUNTIME_DIR=/tmp/zp-run HOME=/home/zp /usr/bin/podman "$@"' \
      >"$w/bin/podman" && chmod +x "$w/bin/podman" || { echo "vm_side: writing the podman wrapper failed"; return 2; }
    [ ! -x /usr/bin/gdb-multiarch ] || ln -sfn /usr/bin/gdb-multiarch "$w/bin/gdb" ||
      { echo "vm_side: linking gdb-multiarch as gdb failed"; return 2; }
    cache=${FARM_VM_CACHE:-/content/farm-cache}
    [[ $cache == /?* ]] || { echo "vm_side: the cache directory '$cache' is not absolute"; return 2; }
    t0=$SECONDS
    if ! PATH=$w/bin:$PATH XDG_CACHE_HOME=$cache bash tools/fetch_test_deps.sh >"$w/fetch.log" 2>&1; then
      echo "vm_side: tools/fetch_test_deps.sh failed; the end of its log:"
      tail -n 20 "$w/fetch.log" | grep -v '@'
      return 2
    fi
    echo "farm: tools/fetch_test_deps.sh ran in $((SECONDS - t0)) s for the folders that need podman"
  else
    : >"$w/cache/zed-test-deps/done"
  fi
  export PATH=$w/bin:$PATH XDG_CACHE_HOME=$cache
  : >"$w/needs"
  for d in $vmfull; do [ ! -f "tests/full/$d/needs" ] || cat "tests/full/$d/needs" >>"$w/needs"; done
  # The copy's short_steps and short_libs are emptied when no short-addresses piece is selected
  # (short = 0), so its list call builds no clone.
  local noshort=(-e 's/^short_steps=.*/short_steps=""/' -e 's/^short_libs=.*/short_libs=""/')
  [ "$short" = 0 ] || noshort=(-e '')
  sed "${noshort[@]}" -e "s|cat tests/full/\\*/needs|cat $w/needs|" tools/run_tests.sh >"$w/run_tests.sh" ||
    { echo "vm_side: writing the copy of tools/run_tests.sh failed"; return 2; }
  { [ "$short" = 1 ] || [ "$(grep -c -x -e 'short_steps=""' -e 'short_libs=""' "$w/run_tests.sh")" = 2 ]; } &&
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
  # An empty list is only right for --skip-other-kind with nothing of this kind selected, which
  # run_tests.sh says in those words; any other empty list ran nothing silently.
  if [ ! -s "$w/list/latest/pieces" ]; then
    cat "$w/list.out"
    if [ "$skip" = 1 ] && grep -q -x -E -e '--skip-other-kind: nothing to run( among the benchmarks)?' "$w/list.out"; then
      : >"$J/out/farm-share"
      echo "farm: share $k of $n: 0 of 0 pieces"
      return 0
    fi
    echo "vm_side: the list call exited 0 and listed no piece"
    return 2
  fi
  awk -v k="$k" -v n="$n" '(NR - 1) % n == k - 1' "$w/list/latest/pieces" >"$w/share" &&
    cut -d ' ' -f 1 "$w/share" >"$J/out/farm-share" ||
    { echo "vm_side: writing the share's list failed"; return 2; }
  # Read by farm_run.sh, which checks that the shares cover the list, and that each reports each
  # piece of $J/out/farm-share (in the job's out.tgz) once.
  echo "farm: share $k of $n: $(wc -l <"$w/share") of $(wc -l <"$w/list/latest/pieces") pieces"
  [ -s "$w/share" ] || return 0
  if [ "$trace" = 1 ]; then
    vm_pkg strace "$w" || return 2
    mkdir -p "$J/out/trace-$k" || { echo "vm_side: mkdir of $J/out/trace-$k failed"; return 2; }
    awk 'NR == FNR { p[$1] = 1; next } $3 in p { print $3, $1, $2 }' "$w/share" "$w/list/latest/chosen" \
      >"$J/out/trace-$k/groups"
    a+=(--trace "$J/out/trace-$k")
  fi
  # A short-addresses piece's binary lies in the clone of the run that listed it, which that run
  # unmounted, so run_tests.sh refuses it in --pieces: the share's short-addresses pieces run by
  # name (--only), in a run that mounts the clone again over this namespace's tmpfs, whose upper
  # layer holds the list call's build of them, so it builds nothing again.
  awk '$1 !~ /^short-/' "$w/share" >"$w/share-main" &&
    awk '$1 ~ /^short-/ { print $1 }' "$w/share" >"$w/share-short" ||
    { echo "vm_side: splitting the share failed"; return 2; }
  : >"$w/r1.out"
  rc=0
  if [ -s "$w/share-main" ]; then
    bash "$w/run_tests.sh" --logs "$w/run" "${a[@]}" --pieces "$w/share-main" "$cores" >"$w/r1.out" 2>&1
    rc=$?
  fi
  if [ -s "$w/share-short" ]; then
    local rs
    bash "$w/run_tests.sh" --logs "$w/run-short" "${a[@]}" \
      --only "$(sed 's/[][\.*^$+?(){}|/]/\\&/g; s/.*/^&$/' "$w/share-short" | paste -sd'|')" "$cores" >>"$w/r1.out" 2>&1
    rs=$?
    [ "$rc" != 0 ] || rc=$rs
  fi
  # The failed pieces run again once, alone: every failed benchmark (see the Design above), and a
  # test piece only when its limit stopped it (FARM-share-load-timeouts), never one that failed an
  # assertion or crashed.
  #
  # How a stopped piece shows. run_tests.sh's piece() runs a test piece under `timeout -k 5 <limit>`
  # and prints `<piece> rc=<rc> <ms>ms load=<load> limit=<limit>s ...`. GNU timeout exits 124 when
  # the limit ran out and its TERM ended the command, and 137 (128 + KILL) when the command outlived
  # the TERM by the 5 s of -k and was killed (coreutils `timeout --help`; checked 2026-11-22 with
  # coreutils 9.10: `timeout -k 1 1 sleep 3` gave 124, the same around a bash that ignores TERM
  # gave 137). 137 is also what a process killed by the kernel's OOM killer gives, so 137 counts
  # as stopped by the limit only when the piece ran at least its limit: a timeout fires only after
  # <limit> s, so a stopped piece has ms >= 1000 x limit, and a kill before that is not the limit's.
  # On a VM systemd-run is the stub above, which execs its command, so the rc is timeout's own.
  #
  # Why alone (FARM-share-load-timeouts). A share runs one piece per core, and the same heavy pieces
  # (lazy points_asked_after_a_disjunction_scale, zedc_check, l01_39 case_wake, l01_23
  # group_oracle, l08_02_remaps) were stopped at loads of 13 to 49 on 12-core VMs in every agent's
  # merge check, and passed alone (main-watch's run of 2026-11-22T11:30Z). The run alone keeps
  # run_tests.sh's own limit, max(20, 20 x load / cores) s, so a piece slow by itself still fails.
  # That limit reads the 1-minute load, which the share leaves high: Linux's load1 is an average
  # damped by e^(-5/60) a 5 s tick (kernel/sched/loadavg.c, EXP_1 = 1884/2048 = 0.9199; from
  # memory of the source, not read today; e^(-5/60) = 0.9200), so with nothing running it falls
  # from L0 to the cores c in 60 ln(L0 / c) s: 84 s from 49 on 12 cores, 149 s from 96 on 8. So
  # the run alone first waits, up to 240 s (enough for L0 up to c e^4 = 54.6 c), until the load is
  # at most the cores, where the limit is the plain 20 s; past 240 s it runs anyway, and its
  # summary line prints the load and the limit it had. tools/test_farm_run.sh's cases
  # timeout-rerun, timeout-alone-too, assert-fail, killed, timeout-and-fail and load-wait check
  # this with a stub of run_tests.sh; they cannot check the real run_tests.sh's lines or a real
  # timeout, which a merge check on VMs exercises.
  # A short-addresses piece is not run again (--pieces refuses it, above): its first verdict stands.
  : >"$w/failed"
  if [ "$rc" = 1 ] && [ "$kind" = bench ]; then
    awk '$2 ~ /^rc=[1-9]/ && $1 !~ /^short-/ { print $1 }' "$w/r1.out" | sort -u >"$w/failed"
  elif [ "$rc" = 1 ]; then
    awk '$2 ~ /^rc=(124|137)$/ && $3 ~ /^[0-9]+ms$/ && $5 ~ /^limit=[0-9]+s$/ && $1 !~ /^short-/ &&
      $3 + 0 >= 1000 * substr($5, 7) { print $1 }' "$w/r1.out" | sort -u >"$w/failed"
  fi
  awk 'NR == FNR { f[$1] = 1; next } $1 in f' "$w/failed" "$w/share-main" >"$w/again"
  if [ -s "$w/again" ]; then
    local lf=${FARM_VM_LOADAVG:-/proc/loadavg} l=0 t=0 alone others
    # The pieces that failed in the first run and are not run again (a test piece that failed
    # otherwise than by its limit, a short-addresses piece): each fails the share.
    others=$(awk 'NR == FNR { f[$1] = 1; next } $2 ~ /^rc=[1-9]/ && !($1 in f)' "$w/failed" "$w/r1.out" | wc -l)
    if [ "$kind" = test ]; then
      while read -r l _ <"$lf" && awk -v l="$l" -v c="$cores" 'BEGIN { exit !(l > c) }' && [ "$t" -lt 240 ]; do
        sleep 5
        t=$((t + 5))
      done
    fi
    bash "$w/run_tests.sh" --logs "$w/again-run" "${a[@]}" --pieces "$w/again" 1 >"$w/r2.out" 2>&1
    rc=$?
    awk 'NR == FNR { f[$1] = 1; next } ($1 in f && $2 ~ /^rc=[1-9]/) || /^pieces: / { $0 = "farm: first run: " $0 } { print }' \
      "$w/failed" "$w/r1.out"
    if [ "$kind" = bench ]; then
      echo "farm: each failed benchmark run again once, alone, on the same VM; its verdict:"
      cat "$w/r2.out"
      [ "$others" = 0 ] || rc=1
      return "$rc"
    fi
    echo "farm: each test piece stopped by its limit run again once, alone, on the same VM; its verdict:"
    echo "farm: waited $t s for the load to fall to the $cores cores (load $l)"
    cat "$w/r2.out"
    alone=$(awk '$2 == "rc=0" { print $1 }' "$w/r2.out" | paste -sd' ')
    [ -z "$alone" ] || echo "farm: stopped by its limit under load, passed alone: $alone"
    # The share fails when a piece failed alone or a piece failed otherwise in the first run.
    [ "$others" = 0 ] || rc=1
    return "$rc"
  fi
  cat "$w/r1.out"
  return "$rc"
}
vm_script=$out/vm_side.sh
{
  declare -f vm_pkg vm_ns vm_cmd vm_side
  # A share's arguments start with its number; a command's with `cmd`.
  echo 'if [ "${1-}" = cmd ]; then shift; vm_cmd "$@"; else vm_side "$@"; fi'
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
# The reports of a share that failed (FARM-setup-fail-silent: a share whose build or setup failed
# printed nothing but `pieces: 0, failed: 0`). Each joins its lines with "; ", drops every line
# with an @ (FARM.md: no account names in kept logs), and repeats no line.
join_lines() { command grep -a -v '@' | awk 'NF && !s[$0]++ { printf "%s%s", (c++ ? "; " : ""), $0 }'; }
# job_why <job.out>: why job.sh stopped, in its own and run.sh's words.
job_why() { command grep -a -E '^(job died on |run\.sh: |job\.sh: |launch failed)' "$1" 2>/dev/null | join_lines; }
# share_why <1.log>: why a share ran no piece: vm_side's own lines, else run_tests.sh's verdict
# and the first compiler error, else the log's last line.
share_why() {
  local s
  s=$(command grep -a '^vm_side: ' "$1" | join_lines)
  [ -n "$s" ] || s=$({ command grep -a -E '^(BUILD FAILED|MISSING |NO PIECE)' "$1"
    command grep -a -m 1 -E '^error(\[|:)' "$1"; } | join_lines)
  [ -n "$s" ] || s=$(command grep -a . "$1" | tail -n 1 | join_lines)
  echo "${s:-no output}"
}
# names <list>: the names of a list one a line, on one line, the first 20 and a count of the rest.
names() { awk 'NF { if (++c <= 20) printf "%s%s", (c > 1 ? " " : ""), $1 } END { if (c > 20) printf " and %d more", c - 20 }' <<<"$1"; }
# share_failed <message>: a line naming a failed share, and the run failed.
share_failed() {
  echo "farm: FAILED: $*" >>"$out/report"
  [ "$rc_all" != 0 ] || rc_all=1
}
# --commands: the file's lines, each a `!` line of one job.sh job on one VM (vm_cmd), run in order;
# a job that did not run to its end (job.sh exit other than 0 or 1, or a line with no exit in
# summary.tsv) is run again on another VM, up to 3 attempts, as a share is. Prints each line's log
# and `farm: command <i> rc=<n>: <line>`; exit 0 when every line passed, 1 when one failed, 129
# when the job could not be run.
if [ -n "$commands" ]; then
  mapfile -t cl < <(command grep -a . "$commands")
  for try in 1 2 3; do
    acquire 1
    v=${held[0]}
    d=$out/commands-$try
    mkdir -p "$d" || die "cannot create $d"
    for c in "${cl[@]}"; do
      printf '!printf %%s %s | base64 -d >/content/job/farm_vm.sh && bash /content/job/farm_vm.sh cmd %s\n' \
        "$vm_b64" "$(printf %s "$c" | base64 -w0)"
    done >"$d/tests.txt"
    echo "farm: ${#cl[@]} commands on $v (attempt $try; logs $d)"
    "$colab_dir/job.sh" "$v" "$wt" "$d/job" "$d/tests.txt" ${spec:+"$spec"} >"$d/job.out" 2>&1 &
    kids=("$!")
    wait "$!"
    jrc=$?
    kids=()
    release_all
    if [[ $jrc =~ ^[01]$ ]] && [ "$(awk -F '\t' '$2 ~ /^[0-9]+$/' "$d/job/summary.tsv" 2>/dev/null | wc -l)" = ${#cl[@]} ]; then
      for i in "${!cl[@]}"; do
        k=$((i + 1))
        r=$(awk -F '\t' -v k="$k" 'NR == k { print $2 }' "$d/job/summary.tsv")
        command grep -a -v '@' "$d/job/out/$k.log" 2>/dev/null
        echo "farm: command $k rc=$r: ${cl[$i]}"
        [ "$r" = 0 ] || rc_all=1
      done
      exit "$rc_all"
    fi
    why=$(job_why "$d/job.out")
    echo "farm: the commands on $v did not run to their end (job.sh exit $jrc)${why:+: $why}; $d/job.out"
  done
  echo "farm: FAILED: the commands could not be run after 3 attempts"
  exit 129
fi
# The VM shares.
if [ -n "$run_vm" ]; then
  want=$vms
  [ -z "$list" ] || want=1
  acquire "$want"
  n=${#held[@]}
  declare -A tries=() done_k=() vm_last=() vms_of=()
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
        "$vm_only" "$vm_except" "${vm_full[*]}" "$vm_short"; do
        line+=" $(printf '%q' "$x")"
      done
      printf '%s\n' "$line" >"$d/tests.txt"
      echo "farm: share $k of $n on $v (attempt ${tries[$k]}; logs $d)"
      vm_last[$k]=$v
      vms_of[$k]+=" $v"
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
        why=$(job_why "$d/job.out")
        echo "farm: share $k of $n on ${vm_last[$k]} did not run to its end (job.sh exit ${jrc:-none})${why:+: $why}; $d/job.out"
        if [ "${tries[$k]}" -ge 3 ]; then
          echo "farm: FAILED: share $k of $n lost after 3 attempts, on${vms_of[$k]}; its pieces are not reported"
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
    # The pieces run against the pieces sent (FARM-setup-fail-silent). A share that printed no
    # share line ran no piece: its list call failed (a failed build or setup, named by share_why)
    # or it ended silently, which before this check passed with `pieces: 0, failed: 0` when the
    # other shares' sizes did not add up to the list's only because one was missing. A share that
    # did list must report each of its pieces once, by name: equal counts can hide a piece run
    # twice and another not at all.
    if [ -z "$list" ]; then
      log=$d/job/out/1.log sent=$d/job/out/farm-share
      if ! command grep -a -q -E '^farm: share [0-9]+ of [0-9]+: [0-9]+ of [0-9]+ pieces$' "$log"; then
        share_failed "share $k of $n on ${vm_last[$k]} ran no piece (exit $lrc): $(share_why "$log"); log $log"
      elif [ ! -f "$sent" ]; then
        share_failed "share $k of $n on ${vm_last[$k]} listed its pieces but sent back no list of them ($sent)"
      else
        ran=$(awk '/^farm: / { next } $2 ~ /^rc=[0-9]+$/ { print $1 }' "$log" | sort)
        miss=$(comm -23 <(sort -u "$sent") <(sort -u <<<"$ran"))
        twice=$(uniq -d <<<"$ran")
        extra=$(comm -13 <(sort -u "$sent") <(sort -u <<<"$ran"))
        why=
        [ -z "$miss" ] || why+="; not reported: $(names "$miss")"
        [ -z "$twice" ] || why+="; reported more than once: $(names "$twice")"
        [ -z "$extra" ] || why+="; reported but not sent: $(names "$extra")"
        [ -z "$why" ] || share_failed "share $k of $n on ${vm_last[$k]} did not run the pieces it was given: ${why#; }"
      fi
      # A failed setup of the full tests' tools (job.sh's run.sh) fails a --full run even when its
      # pieces passed: a piece whose tool is missing may skip, not fail.
      if [ -n "$full" ] && [ -f "$d/job/out/setup-full.log" ]; then
        share_failed "share $k of $n on ${vm_last[$k]}: $(join_lines <"$d/job/out/setup-full.log"); $d/job/setup.log"
      fi
      # Benchmarks measured in processor time fail the run (FARM-icount-fallback-silent). Without
      # zed_icount (its build failed: job.sh's run.sh writes out/icount.log; or the checkout
      # predates tools/icount: no log, but each `bench` line says `work=` where a count says
      # `instr=`, tests/src/scaling_tests.rs), a benchmark falls back on processor time, whose
      # ratio scaling::compare_measured holds to LIMIT x TIME_ALLOWANCE = 21, not 10.5; such a run
      # passed silently (l01_38 twin_chains_of_absolute_values_scale at 11.94, b22-msgtypes4).
      if [ "$kind" = bench ]; then
        why=
        [ ! -f "$d/job/out/icount.log" ] || why=$(join_lines <"$d/job/out/icount.log")
        c=$(awk '$1 == "bench" && / work=/' "$log" | wc -l)
        [ "$c" = 0 ] || why+="${why:+; }$c bench lines say work=, not instr="
        if [ -n "$why" ]; then
          echo "farm: benchmarks measured processor time, not instructions, on ${vm_last[$k]} (share $k of $n): $why" >>"$out/report"
          [ "$rc_all" != 0 ] || rc_all=1
        fi
      fi
    fi
    if [ -n "$trace" ] && [ -d "$d/job/out/trace-$k" ]; then
      mkdir -p "$trace" && cp -r "$d/job/out/trace-$k" "$trace/vm$k" || die "cannot copy the trace of share $k"
    fi
  done
  # The shares' sizes must add up to the list's, and every share must have listed as many pieces:
  # a piece in no share would read as passing. (Each share's own pieces are checked by name above,
  # and a share with no share line is failed there.)
  cover=$(awk '
    /^farm: share [0-9]+ of [0-9]+: [0-9]+ of [0-9]+ pieces$/ { k = $3; m[k] = $6; t[k] = $8; next }
    END {
      for (k in m) {
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
