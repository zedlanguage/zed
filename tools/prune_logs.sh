#!/bin/bash
# Usage: tools/prune_logs.sh [--keep <n>] [--days <d>] [--cited <file>]... <base>...
# Lists, one absolute path a line on stdout, the per-run log directories under each <base> that may
# be deleted, and deletes nothing (TOOL-test-logs-prune). tools/run_tests.sh makes one directory
# per run, <base>/<UTC time>-<pid> (build/test-logs by default; NO-LOCKS-optimistic), and keeps
# them all; /home/luke/Work/wt/main-watch-runs holds the run directories of tools/main_watch.sh,
# <time>-<pid>, and the copies of it that /home/luke/Work/wt/main-watch.sh runs, script.<6 chars>.
# These three kinds of directory are the only ones it looks at (a file, a symbolic link or another
# name is never listed). It keeps, and so does not list:
#  - the one <base>/latest names;
#  - the newest <n> of each base besides that one (default 10), by the time each was last changed;
#  - each changed within the last <d> days (default 7; a fraction is allowed);
#  - each that a live process uses: its working directory, an open file or an argument lies in it;
#  - each whose name a --cited file holds (pass the files that cite logs as evidence:
#    docs/plan_dag.md, /home/luke/Work/wt/ledger.jsonl, running-log.md, spawn-queue.txt).
# On stderr: a line `kept: <path>: in use by pid <p>` or `kept: <path>: cited in <file>` for each
# kept for those two reasons, then for each base `prune_logs: <base>: <m> run directories; keep <k>
# (latest, newest, recent, in use, cited: each counted once, by the first reason in that order);
# list <l>`. Exit 0, or 2 on a usage error, a missing base or a missing --cited file.
# Deleting is left to the caller, by the literal paths this prints: check them with `ls -ld` and
# `realpath -e`, then one `rm -rf --one-file-system --preserve-root=all` naming them (the rm rules
# of the agent brief). A directory that a run starts using after the listing is not protected; the
# newest <n> and the last <d> days cover a run that is still going.
set -euo pipefail
keep=10
days=7
cited=()
bases=()
while [ $# -gt 0 ]; do
  case $1 in
    --keep)
      [[ ${2:-} =~ ^[0-9]+$ ]] || { echo "prune_logs: --keep takes a whole number" >&2; exit 2; }
      keep=$2
      shift 2
      ;;
    --days)
      [[ ${2:-} =~ ^[0-9]+(\.[0-9]+)?$ ]] || { echo "prune_logs: --days takes a number" >&2; exit 2; }
      days=$2
      shift 2
      ;;
    --cited)
      [ -f "${2:-}" ] || { echo "prune_logs: no file ${2:-(none given)} for --cited" >&2; exit 2; }
      cited+=("$(realpath -e "$2")")
      shift 2
      ;;
    -*)
      echo "prune_logs: unknown option $1" >&2
      exit 2
      ;;
    *)
      [ -d "$1" ] || { echo "prune_logs: no directory $1" >&2; exit 2; }
      bases+=("$(realpath -e "$1")")
      shift
      ;;
  esac
done
if [ ${#bases[@]} = 0 ]; then
  echo "usage: tools/prune_logs.sh [--keep <n>] [--days <d>] [--cited <file>]... <base>..." >&2
  exit 2
fi
cutoff=$(($(date +%s) - ${days%.*} * 86400))
[[ $days != *.* ]] || cutoff=$(gawk -v c="$cutoff" -v f="0.${days#*.}" 'BEGIN { printf "%d", c - f * 86400 }')
pats=()
for base in "${bases[@]}"; do pats+=(-e "$base/"); done
# What live processes use, as `<pid> <path>` lines: working directories, open files, and each
# argument of the command lines that name a base. One pass over /proc for all bases (about 0.1 s
# at 900 processes, 2026-11-27); a process that ends meanwhile is skipped. Read by gawk from a
# file descriptor: tens of thousands of lines, too long for one argument.
scan() {
  {
    find /proc/[0-9]*/cwd -maxdepth 0 -printf '%p %l\n'
    find /proc/[0-9]*/fd -mindepth 1 -maxdepth 1 -printf '%p %l\n'
    for f in $(command grep -s -l -a -F "${pats[@]}" /proc/[0-9]*/cmdline || true); do
      { tr '\0' '\n' <"$f"; } 2>/dev/null | sed "s|^|$f |" || true
    done
  } 2>/dev/null | sed -E 's|^/proc/([0-9]+)/[^ ]* |\1 |' || true
}
uses=$(scan)
for base in "${bases[@]}"; do
  # `<mtime> <name>` of each run directory.
  runs=$(find "$base" -mindepth 1 -maxdepth 1 -type d -regextype posix-extended \
    -regex '.*/([0-9]{8}T[0-9]{6}\.[0-9]+Z-[0-9]+|[0-9]{8}-[0-9]{6}-[0-9]+|script\.[A-Za-z0-9]{6})' \
    -printf '%T@ %f\n')
  latest=$(readlink "$base/latest" 2>/dev/null || true)
  # `<file>:<name>` for each run directory's name that a --cited file holds.
  hits=
  if [ ${#cited[@]} -gt 0 ] && [ -n "$runs" ]; then
    hits=$(command grep -a -o -H -F -f <(sed 's/^[^ ]* //' <<<"$runs") "${cited[@]}" || true)
  fi
  # Three inputs: the uses, the hits, the run directories (newest first). Each is read once, and
  # each run directory is looked up in the arrays they fill, so the cost is linear in their sizes.
  LC_ALL=C gawk -v base="$base" -v keep="$keep" -v cutoff="$cutoff" -v latest="${latest##*/}" '
    ARGIND == 1 {
      # The run directory a used path lies in: the component after "<base>/", wherever the path
      # holds it (an argument may be --logs=<path>).
      s = index($0, " "); i = index($0, base "/")
      if (i > s) {
        r = substr($0, i + length(base) + 1); j = index(r, "/")
        n = j ? substr(r, 1, j - 1) : r
        if (!(n in use)) use[n] = substr($0, 1, s - 1)
      }
      next
    }
    ARGIND == 2 {
      # A grep -o -H line is <file>:<name>; a name has no colon, so the last colon ends the file.
      j = match($0, /:[^:]*$/)
      n = substr($0, j + 1)
      if (j && !(n in cite)) cite[n] = substr($0, 1, j - 1)
      next
    }
    $0 != "" {
      t = $1; name = substr($0, index($0, " ") + 1); d = base "/" name
      runs++
      if (name == latest) { k["latest"]++; next }
      if (++ranked <= keep) { k["newest"]++; next }
      if (t + 0 >= cutoff + 0) { k["recent"]++; next }
      if (name in use) { print "kept: " d ": in use by pid " use[name] > "/dev/stderr"; k["in use"]++; next }
      if (name in cite) { print "kept: " d ": cited in " cite[name] > "/dev/stderr"; k["cited"]++; next }
      out[++listed] = d
    }
    END {
      kept = k["latest"] + k["newest"] + k["recent"] + k["in use"] + k["cited"]
      printf "prune_logs: %s: %d run directories; keep %d (latest %d, newest %d, recent %d, in use %d, cited %d); list %d\n", \
        base, runs, kept, k["latest"], k["newest"], k["recent"], k["in use"], k["cited"], listed > "/dev/stderr"
      n = asort(out)
      for (i = 1; i <= n; i++) print out[i]
    }' <(printf '%s\n' "$uses") <(printf '%s\n' "$hits") <(LC_ALL=C sort -r -n <<<"$runs")
done
