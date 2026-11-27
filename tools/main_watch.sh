#!/bin/bash
# Usage:
#   tools/main_watch.sh                 watch origin/main of /home/luke/Work/zed-impl (below)
#   tools/main_watch.sh --start <commit>  first record <commit> as checked (a commit where every
#                                       test and benchmark passes), then watch
# Started by hand, not by a timer; /home/luke/Work/wt/main-watch.sh runs this file from
# /home/luke/Work/zed-impl. Exits only on a usage or setup error (2), which main-watch.sh restarts
# after a delay; a stuck case (below) is recorded and polling goes on.
#
# The author's flow (NO-LOCKS-optimistic, 2026-11-19): merge-push.sh pushes without running tests
# after the rebase, and this watcher finds and fixes what such pushes break:
#  1. Every $MAIN_WATCH_POLL seconds (300) it fetches origin/main and counts the landings since the
#     last checked commit. A landing is one push by merge-push.sh, which appends the pushed commit
#     to /home/luke/Work/wt/landings.log (`<commit> <time> <worktree> <branch>`; the file only
#     grows). A head of main that the file lacks (a push by an older copy of merge-push.sh, or by
#     hand) is appended here as one landing, `<commit> <time> unrecorded -`, so every head this
#     watcher has seen is a landing boundary.
#  2. When at least $MAIN_WATCH_MIN (15) landings are unchecked, it runs every test
#     (tools/run_tests.sh --full) and every benchmark (--bench, a run apart) on main's head, in its
#     own worktree under /home/luke/Work/wt/trees, made and seeded for this run (a per-run copy;
#     two watchers never share one) and removed when the run ends green, after its build is
#     published as the central build (build-publish.sh).
#  3. Each failure is confirmed: the piece is run again alone. One that passes alone is a flake,
#     recorded in main-watch-flakes.log with both summary lines, and not bisected. A confirmed
#     failure that was never seen to pass during this check is run at the last checked commit; if
#     it fails there too it existed before the range, and is filed as FAIL-main-<last checked
#     commit> (below, Stuck) and not bisected: the last
#     checked commit passed everything, so a piece that now fails there means the machine changed
#     or the piece is flaky, which a person must judge.
#  4. Bisect. For a set F of confirmed failures that all passed at commit G (the last checked
#     commit, or a later commit where they were seen to pass): a binary search over the landings
#     in G..head finds the first landing at which some piece of F fails (each landing head was
#     built by merge-push.sh, so each builds); then, when that landing holds more than one commit,
#     `git bisect run` between the landing before it and it finds the first bad commit C (a
#     commit that does not build is skipped, exit 125, unless the build itself is in F). The
#     predicate runs only F's pieces, and a piece counts as failing only when it fails twice in a
#     row (run again alone at once). F1 = the pieces of F that fail at C. C and F1 are recorded;
#     F := F \ F1; repeat until F is empty. So each problem is traced to the first commit that
#     caused it, in turn.
#  5. For each culprit C: a line in main-red.log (`open <C> <time> main-watch <branch> pieces:
#     <pieces>`), a line in running-log.md, and a ledger row FAIL-main-<C's 9-digit hash>, owner
#     main-watch. Then a fixing agent: a fresh worktree from the current origin/main, a brief
#     written from the template main-watch-fix-brief.md (C's message, files and diff, F1 with the
#     failure output, the bisect log), and `claude -p --model opus --dangerously-skip-permissions
#     < brief` run in it, in the foreground. The agent lands its fix through merge-push.sh, which
#     names its worktree in landings.log; that is how the watcher learns the fix's commit. F1 is
#     then run at the fix's commit: passing, the row is done with the fix's commit and main-red.log
#     gets `fixed <C> <time> main-watch by <fix>`. Still failing: another agent, up to 3 attempts.
#  6. After the fixes, it fetches and runs everything again at the new head. New failures go
#     through 3 to 5 again, with the pieces' last passing commits as the bisect's good ends (a
#     failure the fix itself caused is traced to the fix). Only when everything passes does it
#     record the head as checked (main-watch.checked, by write to a temporary file and rename).
#  7. Then it polls again.
# The spec. Many pieces read the spec (DESIGN.md, EXAMPLES.md; tests/src/spec.rs finds it through
# $ZED_SPEC_DIR, else at /home/luke/Work/zed), and a spec change and its zed-impl half land as
# separate pushes, often hours apart. So the watcher keeps its own clone of the spec ($logroot/spec,
# seeded by hardlinks from $MAIN_WATCH_SPEC_SEED, fetched from $MAIN_WATCH_SPEC_URL), exports it as
# ZED_SPEC_DIR, and pins it: each check fetches the spec's origin/main once, S, and every run of the
# check reads S, never the author's working tree, which may be behind origin or hold edits. The
# checked file records S beside the head (`<commit> <time> <spec commit>`); for an older line
# without it, S0 is the spec's last commit on origin/main at or before the line's time. Step 3
# then first asks whether the failure comes from the spec: each confirmed failure is run again at
# the head with S0, the spec the last checked commit C0 was checked with (no build: the head is
# built, and the pieces read the spec when they run). One that passes there was broken by a spec
# commit in S0..S: a binary search over those commits, the head fixed, names the first at which it
# fails twice, and it is filed under the row that commit's subject names (else FAIL-spec-<commit>):
# a QUEUE line in queue mode, a stuck entry otherwise; its zed-impl half is missing, or the spec
# commit is wrong. The rest go on through step 3's run at C0 and the bisect, both with S0, so that
# neither mistakes a spec change for a zed-impl one. Before this (FAIL-main-54b8e6459,
# 2026-11-21) the watcher read /home/luke/Work/zed: spec commits 872897b and 8578919 added
# diagnostics rows hours before their zed-impl halves landed, l01_21_test_runner then failed at
# C0 54b8e6459 too, and was filed as FAIL-main-54b8e6459, a cause no bisect of zed-impl can find.
# Known failures. main-watch-known.txt lists failures a plan row owns, one a line,
# `<kind>:<piece> <row> [skip] [fixed-by <commit>]`: such a piece still runs and is reported with
# its row, but is not bisected or fixed here, and does not keep a head from being checked. A third
# field `skip` keeps the piece from being started at all (tools/run_tests.sh --except), for a piece
# too costly to run while it fails: bench rung2 at n = 600 held 67 to 71 GB a run
# (TOOL-main-watch-start-green). The row's owner never takes the line out: once the fix has landed
# on main it appends `fixed-by <the landed commit>` (MAINWATCH-known-fixed-by, 2026-11-21). The
# line is then in force at every commit that does not contain that commit (known_lines), and
# the watcher itself takes it out at the first check of a head that contains the commit and at
# which the piece passes. Before this, knownf3 took the exp_families line out when its fix
# 0ad3544ed landed; the watcher was then checking 46c1d2b71, which lacks the fix, saw the old
# failure as new, and filed the duplicate row FAIL-main-af9161e5a. A piece that still fails at a
# head containing its fixed-by commit goes back to its row (a QUEUE line, or a stuck entry), and
# its line loses the fixed-by, so it is in force again. Each checked line records the known
# failures its head was checked with (a fourth field), so a failure found at the last checked
# commit that was known there is filed under its row again, not as FAIL-main-<C0>.
# Queue mode. With MAIN_WATCH_QUEUE=<file> (/home/luke/Work/wt/main-watch.sh sets it to
# spawn-queue.txt) step 5 starts no fixing agent: each culprit C becomes one line
# `QUEUE <row> (filed by main-watch <time>: first bad commit <C> ... fails <pieces>; ...)` in that
# file, for the coordinator to send to the row's owner, and its pieces join the known list with
# that row. The row is the plan row C's subject names in its closing parentheses (the project's
# commit convention), else the first row its message names, else FAIL-main-<C>. Once every
# failure is known or queued the head is checked without running everything again (an hour that
# would find nothing new: no fix has landed).
# Processes. Each run of pieces (and the build it starts) runs as a session of its own (setsid);
# when it ends, every process still in that session (a test binary, a fresh child of a benchmark,
# a build process) is logged and killed by pid, so no run holds memory after it ends (author,
# 2026-11-20). A session id names only this run's processes, where the path of a test binary
# (under the shared /home/luke/Work/wt/.build-root) would match other agents' runs too. zrun's
# namespace holder starts a session of its own (setsid -f) and is not touched: it is the
# worktree's, outlives every run, and is stopped when the worktree is removed.
# Stuck: a fixing agent that ends without landing or a fix worktree that cannot be made, pieces
# still failing after 3 attempts, a bisect that names no commit, a named commit at which none of
# the pieces fails twice, or a run of every piece ended by a signal (the runner itself crashed, so
# the pieces it did not report would read as passing). The watcher then writes `stuck <commit>
# <time> main-watch <reason>` to main-red.log (red_open in merge-push.sh reads only open and fixed
# lines) and an entry to main-watch-stuck.md for the author, puts the case's pieces on the known
# list with its row (FAIL-main-<commit>), and polls on (author, 2026-11-21: "main_watch should not
# crash if a test fails or crashes"; it used to exit 3 and stop, which left main unchecked for as
# long as the case stood). A failure that exists at the last checked commit C0 is filed as
# FAIL-main-<C0> the same way; in queue mode it gets a QUEUE line instead of a stuck entry. A
# crashing piece (a signal, an abort, its time limit) is a failing piece, never a watcher error:
# tools/run_tests.sh prints its `rc=` (128 + the signal, 124 for its limit). A failed fetch is
# tried again at the next poll. Only a usage or setup error (no checked commit, a worktree that
# cannot be made or checked out) exits, with 2.
#
# No locks (author, 2026-11-19). Every file it shares is appended to in single lines (O_APPEND,
# each well under PIPE_BUF, so lines of two writers never mix) or replaced by rename. One watcher
# at a time by design: two started at once work in separate worktrees and may record the same
# culprit twice; a ledger or running-log line already present for the same row and state is not
# written again. It never runs git reset, and `git bisect reset` only in its own worktree.
#
# What it costs. A full check is the whole suite plus every benchmark, about 1 hour: on
# origin/main f215d9c90 (2026-11-19) the suite took 1129 s (2752 pieces, load 48 to 86) and the
# benchmarks 2453 s (2982 pieces, load 33 to 126), run one after the other. A bisect over L landings with k commits in the culprit landing
# runs F's pieces about log2(L) + log2(k) times, each with an incremental build of the commit.
#
# For the toy test (tools/test_main_watch.sh) every outside command can be replaced:
# MAIN_WATCH_HOME the directory of the shared files (/home/luke/Work/wt), MAIN_WATCH_REPO the
# repository (/home/luke/Work/zed-impl), MAIN_WATCH_TREES where worktrees go ($home/trees),
# MAIN_WATCH_PREPARE the command run on a new worktree (seed-build.sh), MAIN_WATCH_REMOVE the one
# that removes it (worktree-remove.sh), MAIN_WATCH_PUBLISH the one that publishes its build once
# its head is checked (build-publish.sh), MAIN_WATCH_RUN the command that runs pieces (called in the
# worktree as `<cmd> <log dir> test|bench [piece...]`, printing tools/run_tests.sh's summary lines
# `<piece> rc=<rc> ...` and BUILD FAILED; no piece named means all), MAIN_WATCH_FIXER the fixing
# agent (`<cmd> <brief> <worktree>`), MAIN_WATCH_POLLS the number of polls before it exits
# (unlimited), MAIN_WATCH_FULL the run_tests.sh option for the full battery (--full; empty for the
# local suite alone), MAIN_WATCH_SPEC_SEED the local spec repository its clone is made from
# (/home/luke/Work/zed; only read), MAIN_WATCH_SPEC_URL the spec remote it fetches (that
# repository's origin), MAIN_WATCH_FARM the runner of pieces on Colab VMs (tools/farm_run.sh beside
# this script; `local` runs them here under zrun, as before FARM-main-watch-remote).
home=${MAIN_WATCH_HOME:-/home/luke/Work/wt}
repo=${MAIN_WATCH_REPO:-/home/luke/Work/zed-impl}
trees=${MAIN_WATCH_TREES:-$home/trees}
min=${MAIN_WATCH_MIN:-15}
poll=${MAIN_WATCH_POLL:-300}
polls=${MAIN_WATCH_POLLS:-}
jobs=${MAIN_WATCH_JOBS:-12}
full=${MAIN_WATCH_FULL---full}
zrun=${MAIN_WATCH_ZRUN:-/home/luke/Work/wt/zrun}
prepare=${MAIN_WATCH_PREPARE:-/home/luke/Work/wt/seed-build.sh}
remove=${MAIN_WATCH_REMOVE:-/home/luke/Work/wt/worktree-remove.sh}
publish=${MAIN_WATCH_PUBLISH:-/home/luke/Work/wt/build-publish.sh}
template=${MAIN_WATCH_TEMPLATE:-$home/main-watch-fix-brief.md}
spec_seed=${MAIN_WATCH_SPEC_SEED:-/home/luke/Work/zed}
landings=$home/landings.log
checked_file=$home/main-watch.checked
red=$home/main-red.log
runlog=$home/running-log.md
ledger=$home/ledger.jsonl
stuck_file=$home/main-watch-stuck.md
flakes=$home/main-watch-flakes.log
# Failures a plan row owns, one a line: <kind>:<piece> <row> [skip] [fixed-by <commit>]. Written by
# hand and in queue mode; see Known failures above, and check.
known_file=$home/main-watch-known.txt
queue=${MAIN_WATCH_QUEUE:-}
self=$(realpath -e "$0")
[ -n "$self" ] || { echo "main-watch: cannot resolve the path of $0" >&2; exit 2; }
# The farm runner sits beside this script, so that, like this script (main-watch.sh runs a copy
# of it), it does not change under a run, and every commit of a bisect runs its pieces the same
# way, though older commits lack tools/farm_run.sh. main-watch.sh copies only this script, so the
# first start copies tools/farm_run.sh of $repo beside it.
farm=${MAIN_WATCH_FARM:-${self%/*}/farm_run.sh}
if [ "$farm" != local ] && [ ! -x "$farm" ]; then
  [ "$farm" = "${self%/*}/farm_run.sh" ] && [ -x "$repo/tools/farm_run.sh" ] && cp "$repo/tools/farm_run.sh" "$farm" ||
    { echo "main-watch: no farm runner $farm (MAIN_WATCH_FARM; \`local\` runs the pieces here)" >&2; exit 2; }
fi
export MAIN_WATCH_HOME=$home MAIN_WATCH_REPO=$repo MAIN_WATCH_FULL=$full MAIN_WATCH_JOBS=$jobs MAIN_WATCH_FARM=$farm

ts() { date -u +%FT%TZ; }
say() { echo "main-watch: $*"; }
short() { git -C "$repo" rev-parse --short=9 "$1"; }

# fixed_of <known line>: the commit its `fixed-by <commit>` names (fields after the row), if any.
fixed_of() { awk '{ for (i = 3; i < NF; i++) if ($i == "fixed-by") { print $(i + 1); exit } }' <<<"$1"; }
# known_lines <commit> in|fixed: `in`, the lines of the known list in force at the commit, as
# written: all but comments, blank lines, and lines whose fixed-by commit the commit contains (is
# an ancestor of it, or is it); `fixed`, those last lines alone. Why the first is the right set:
# the fixed-by commit F is the commit its row's owner landed as the fix, so at a commit without F
# the failure is the old one and stays the row's; at a commit
# with F the piece should pass, and if it fails anyway check sends it back to the row (Known
# failures above), so no failure is ever taken from its row unreported. A fixed-by commit that
# does not resolve (a typo, or the sha of a branch commit that merge-push.sh's rebase replaced)
# makes `merge-base --is-ancestor` exit 128, so the line stays in force (known, never dropped), and
# check says so at each check. Cost: one awk and at most one git process per line, O(n) in the
# list's n lines (a few dozen at most); it runs once per check and once per run of every piece.
# Each line is printed with its piece's build hash taken off (unhash), as the names of a run are.
known_lines() {
  local c=$1 want=$2 line f set
  [ -s "$known_file" ] || return 0
  while IFS= read -r line; do
    case $line in '#'* | '') continue ;; esac
    f=$(fixed_of "$line")
    set=in
    [ -n "$f" ] && git -C "$repo" merge-base --is-ancestor "$f" "$c" 2>/dev/null && set=fixed
    [ "$set" != "$want" ] || printf '%s\n' "$line"
  done <"$known_file" | unhash
}

# Runs the pieces "$3"... of kind $2 (test or bench) in the current directory, a worktree, with
# tools/run_tests.sh's own log directory $1. No piece named: all of that kind. The piece BUILD
# alone: only the build (--list builds every test binary first).
run_pieces() {
  if [ -n "${MAIN_WATCH_RUN:-}" ]; then
    "$MAIN_WATCH_RUN" "$@"
    return
  fi
  local logs=$1 kind=$2 p names=()
  shift 2
  for p in "$@"; do [ "$p" = BUILD ] || names+=("$p"); done
  local a=() skip=
  if [ "$kind" = bench ]; then a+=(--bench); elif [ -n "$full" ]; then a+=("$full"); fi
  if [ ${#names[@]} -eq 0 ] && [ $# -eq 0 ]; then
    # A run of every piece leaves out those of this kind the known list marks skip, each as its
    # own anchored alternative, as for --only below; only lines in force at the commit checked out
    # here, so a skipped piece runs at a commit holding its fix and can be seen to pass.
    skip=$(known_lines "$(git rev-parse HEAD)" in | awk -v k="$kind:" '$3 == "skip" && index($1, k) == 1 { print substr($1, length(k) + 1) }' |
      sed 's/[][\.*^$+?(){}|/]/\\&/g; s/.*/^&$/' | paste -sd'|')
    [ -z "$skip" ] || a+=(--except "$skip")
  fi
  if [ "$farm" = local ]; then
    if [ ${#names[@]} -gt 0 ]; then
      # Each name its own alternative, ^<name>$|^<name>$: run_tests.sh reads the text before the
      # first :: of each top-level alternative as the group, which must be an extended regular
      # expression by itself, so ^(a::x|b::y)$ is refused (exit 2, no piece run) and each failure
      # read as a flake (TOOL-main-watch-start-green, 2026-11-20; test_main_watch.sh case zrun).
      a+=(--only "$(printf '%s\n' "${names[@]}" | sed 's/[][\.*^$+?(){}|/]/\\&/g; s/.*/^&$/' | paste -sd'|')")
    elif [ $# -gt 0 ]; then
      a+=(--list)
    fi
    "$zrun" tools/run_tests.sh --logs "$logs" "${a[@]}" "$jobs"
    return
  fi
  # On Colab VMs (FARM-main-watch-remote; author 2026-11-22: "start all future jobs in the cloud
  # via Colab"): tools/farm_run.sh takes the same selection, the names one a line in a file (it
  # anchors each as above), with the log directory as its --out, and prints the same summary
  # lines and BUILD FAILED; see its head for how the pieces are dealt to the VMs, why a
  # benchmark's series stays on one VM and is run again there once when it fails, and which few
  # pieces no VM can run yet (run nowhere, named on a `farm: not run` line; nothing runs on this
  # machine, author 2026-11-22). A run of up to 8 named pieces (fails_twice's runs, each step of a
  # bisect) takes one VM: a VM's start (packing, upload, an incremental build) takes minutes,
  # longer than such pieces; a larger run takes 4, the most one owner may hold (FARM.md). Its
  # exit, 129 when a VM's share could not be run, is 128 or more, which run's callers read as a
  # crashed runner (see Stuck above), never as passing pieces.
  local vms=4
  [ $# -eq 0 ] || [ ${#names[@]} -gt 8 ] || vms=1
  a+=(--owner main-watch --vms "$vms" --jobs "$jobs" --out "$logs")
  [ -z "${ZED_SPEC_DIR:-}" ] || a+=(--spec "$ZED_SPEC_DIR")
  if [ ${#names[@]} -gt 0 ]; then
    printf '%s\n' "${names[@]}" >"$logs.terms" || return 2
    a+=(--terms "$logs.terms")
  elif [ $# -gt 0 ]; then
    a+=(--list)
  fi
  "$farm" "${a[@]}"
}
# --pieces <sid file> <run_pieces arguments>: run_pieces in a process of its own, which run starts
# as a new session; it writes its pid, the session's id, to <sid file> first.
if [ "${1:-}" = --pieces ]; then
  echo $$ >"$2"
  shift 2
  run_pieces "$@"
  exit
fi
# reap <session id> <output file>: kills by pid each process left in the session after its run,
# logging each (its pid, resident memory in KiB, seconds alive and command line) to the output
# file and to the watcher's output. Killed processes leave the list once their parent (init, for
# an orphan) has waited for them; a list not empty after 10 s is reported, not waited on.
reap() {
  local sid=$1 o=$2 left pid line i
  local -A killed=()
  [ -n "$sid" ] || return 0
  for i in $(seq 100); do
    left=$(pgrep -s "$sid")
    [ -n "$left" ] || return 0
    for pid in $left; do
      [ -z "${killed[$pid]:-}" ] || continue
      killed[$pid]=1
      line=$(ps -o pid=,rss=,etimes=,args= -p "$pid")
      [ -n "$line" ] || continue
      kill -KILL "$pid" 2>/dev/null || continue
      echo "left alive after the run, killed by pid: $line" >>"$o"
      say "left alive after the run of $(basename "$o"), killed by pid: $(cut -c1-200 <<<"$line")"
    done
    sleep 0.1
  done
  say "processes of session $sid still listed 10 s after they were killed: $(paste -sd' ' <<<"$left")"
}
# run <kind> [piece...]: runs them in the watcher's worktree (in --predicate mode, where $copy is
# empty, in the current directory, the worktree `git bisect run` was started in), as a session of
# its own whose leftover processes are then killed (reap); prints the file holding the output, a
# new file under $logroot.
run() {
  local kind=$1 o
  shift
  o=$logroot/$(date -u +%H%M%S%N)-$$-$kind
  pushd "${copy:-.}" >/dev/null || exit 2
  setsid -w "$self" --pieces "$o.sid" "$o.logs" "$kind" "$@" >"$o.out" 2>&1
  echo $? >"$o.rc"
  popd >/dev/null || exit 2
  reap "$(cat "$o.sid" 2>/dev/null)" "$o.out" >&2
  echo "$o.out"
}
# unhash: each line on stdin with the build hash of cargo's form (- and 16 hexadecimal digits)
# taken off the first name of its first field, `<kind>:<binary>-<hash>[::<path>]`, so
# test:zed_kernel-647156406bbd16e1::x becomes test:zed_kernel::x; a line without `<kind>:` is
# taken as a bare piece name. A library's unit tests and benchmarks are named after their
# binary, hash and all, and the hash changes with each build of the library: the same piece had
# one name at the head and another at a bisect step or in a known line, so a known failure
# written without the hash, as FAIL-main-escape-tied-true's was, was never matched
# (MAINWATCH-lib-piece-hash, 2026-11-27). Every name the watcher reads from a run goes through
# this, and so does every known line, so the names it compares, stores and passes on are
# without the hash; tools/run_tests.sh --only and --except select a piece by its name with the
# hash taken off (`selected` and the --except loop there), so a name without it runs the same
# piece. No group, step or test name holds a - followed by 16 hexadecimal digits before `::`
# (tools/run_tests.sh, at --only), so nothing else is changed. Test: tools/test_main_watch.sh
# case hash.
unhash() { sed -E 's/^(([a-z]+:)?[A-Za-z0-9_]+)-[0-9a-f]{16}(::| |$)/\1\3/'; }
# The pieces of kind $2 that failed, or passed, in the output $1, as <kind>:<piece>, one a line,
# without the build hash (unhash); a failed build is <kind>:BUILD.
failed_in() {
  command grep -a -o -E '^[^ ]+ rc=[1-9][0-9]* ' "$1" | cut -d' ' -f1 | sed "s/^/$2:/" | unhash
  command grep -a -q 'BUILD FAILED' "$1" && echo "$2:BUILD"
  return 0
}
passed_in() { command grep -a -o -E '^[^ ]+ rc=0 ' "$1" | cut -d' ' -f1 | sed "s/^/$2:/" | unhash; }
# The summary line of piece $2 (<kind>:<piece>, without the hash) in the output $1, where the
# piece's first name may carry its binary's hash.
line_of() {
  local n=${2#*:} rest=
  [[ $n != *::* ]] || rest=::${n#*::}
  command grep -a -m 1 -E "^${n%%::*}(-[0-9a-f]{16})?$rest rc=" "$1"
}
# Items of the list "$1" (one a line) that are in the list "$2".
inter() { [ -n "$1" ] && [ -n "$2" ] && command grep -a -x -F -f <(printf '%s\n' "$2") <<<"$1"; return 0; }
minus() { if [ -z "$2" ]; then printf '%s' "$1"; else command grep -a -v -x -F -f <(printf '%s\n' "$2") <<<"$1"; fi; return 0; }

# fails_twice <items>: runs the items (<kind>:<piece>, one a line) at the current checkout, each
# that fails run again alone; prints those that failed both times, and <kind>:BUILD when the build
# failed (the pieces of that kind then did not run). The outputs of the runs that failed are
# listed in $evidence.
fails_twice() {
  local items=$1 kind names f first p again out=
  for kind in test bench; do
    names=$(sed -n "s/^$kind://p" <<<"$items")
    [ -n "$names" ] || continue
    # shellcheck disable=SC2086
    f=$(run "$kind" $names)
    first=$(inter "$(failed_in "$f" "$kind")" "$items
$kind:BUILD")
    [ -z "$first" ] || echo "$f" >>"$evidence"
    for p in $first; do
      if [ "$p" = "$kind:BUILD" ]; then
        out+="$p"$'\n'
        continue
      fi
      f=$(run "$kind" "${p#*:}")
      again=$(failed_in "$f" "$kind")
      if inter "$again" "$p
$kind:BUILD" | command grep -a -q .; then
        out+="$p"$'\n'
        echo "$f" >>"$evidence"
      fi
    done
  done
  printf '%s' "$out" | sed '/^$/d'
}

# --predicate <file>: the command `git bisect run` calls in the watcher's worktree. Exit 1 when
# some piece listed in <file> fails twice at the commit checked out, 0 when none does, 125 when
# the build fails and the build is not in the list.
if [ "${1:-}" = --predicate ]; then
  items=$(cat "$2")
  logroot=${MAIN_WATCH_LOGROOT:?} evidence=${MAIN_WATCH_EVIDENCE:?}
  bad=$(fails_twice "$items")
  echo "main-watch predicate at $(git rev-parse --short=9 HEAD): ${bad:-none fail}" | tr '\n' ' ' >&2
  echo >&2
  if [ -n "$(inter "$bad" "$(command grep -a -E ':BUILD$' <<<"$bad")")" ] && [ -z "$(inter "$bad" "$items")" ]; then
    exit 125
  fi
  [ -z "$(inter "$bad" "$items")" ]
  exit
fi

start=
if [ "${1:-}" = --start ]; then
  start=$(git -C "$repo" rev-parse -q --verify "${2:-}^{commit}") || { echo "main-watch: --start needs a commit of $repo" >&2; exit 2; }
  shift 2
fi
[ $# -eq 0 ] || { echo "main-watch: usage: main_watch.sh [--start <commit>]" >&2; exit 2; }
git -C "$repo" rev-parse -q --verify origin/main >/dev/null || { echo "main-watch: $repo has no origin/main" >&2; exit 2; }

# A JSON string of $1: backslashes and quotes escaped, control characters as spaces.
json() {
  local s=${1//\\/\\\\}
  s=${s//\"/\\\"}
  printf '"%s"' "$(tr '\000-\037' ' ' <<<"$s" | sed 's/ *$//')"
}
# ledger <id> <state> <commits> <note> [label]: appends a ledger line unless one for the same
# id and state is there already (a second watcher, or a run started again).
ledger() {
  command grep -a -q -F "\"id\":$(json "$1"),\"by\":\"main-watch\",\"state\":$(json "$2")," "$ledger" 2>/dev/null && return 0
  echo "{\"ts\":\"$(ts)\",\"id\":$(json "$1"),\"by\":\"main-watch\",\"state\":$(json "$2"),\"owner\":\"main-watch\",\"commits\":[$(for c in $3; do printf '%s"%s"' "${sep-}" "$c"; sep=,; done)],\"label\":$(json "${5:-$1}"),\"note\":$(json "$4")}" >>"$ledger"
}
runlog() { echo "$(ts) | NO-LOCKS-optimistic:main-watch | $*" >>"$runlog"; }
# The landings in $1..$2 (commits of landings.log, oldest first, ending at $2).
landings_in() {
  [ -f "$landings" ] || return 0
  git -C "$repo" rev-list --reverse "$1..$2" | command grep -a -x -F -f <(cut -d' ' -f1 "$landings")
}
# Fetches; makes sure origin/main's head is in landings.log; prints it.
head_now() {
  local h
  git -C "$repo" fetch -q origin || { echo "main-watch: fetch failed" >&2; return 1; }
  h=$(git -C "$repo" rev-parse origin/main)
  command grep -a -q "^$h " "$landings" 2>/dev/null || echo "$h $(ts) unrecorded -" >>"$landings"
  echo "$h"
}
# The landing line of the landing that contains commit $1 (the first landing at or after it).
landing_of() {
  local l
  for l in $(cut -d' ' -f1 "$landings"); do
    if git -C "$repo" merge-base --is-ancestor "$1" "$l" 2>/dev/null; then
      command grep -a -m 1 "^$l " "$landings"
      return
    fi
  done
}

# known_add <row> <items>: puts each item (<kind>:<piece>) on the known list with the row, unless
# the list has it already.
known_add() {
  local p
  for p in $2; do
    [ -s "$known_file" ] && unhash <"$known_file" | awk -v p="$p" '$1 == p { f = 1 } END { exit !f }' && continue
    echo "$p $1" >>"$known_file"
  done
}
# known_edit <commit> <items> drop|unfix: each line of an item (<kind>:<piece>) whose fixed-by
# commit the commit contains is taken out (drop: the piece passes there, so its fix holds) or
# kept without its fixed-by (unfix: the piece still fails there, so the line is in force again).
# The list is shared and others append to it, so it is replaced by rename, as every shared file
# here that is not only appended to (No locks below): the new text is written to a file of this
# process, the list is read again, and the rename happens only if the list is still the text the
# edit was made from; otherwise the edit is made again from the new text, until the list stands
# still between the read and the check. The loop ends: each pass that does not rename saw a
# change, and changes come from people and agents, a few a day.
#
# The window between that check and the rename (TOOLS-push-tests-cleanup, 2026-11-21). An append
# (`>>`: known_add, fix, a person's echo) made there goes to the file the rename then replaces, and
# was lost. Now the list is read through fd 9, held open on the file it was read from (inode I)
# for the whole pass, with no lock and no extra file. After the rename, I is read again through
# /dev/fd/9 (Linux reopens the inode itself, though it no longer has a name): its text is the
# text read, `old`, followed by whatever was appended to I since. Claim: every line appended to I
# before that second read is in the list after this function. Proof: O_APPEND writes go to the end
# of I, so I's text is old + "\n" + the appended lines (old was read whole, and command
# substitution only strips its final newlines); the second read sees each write completed before
# it; the lines after old are appended (O_APPEND) to the new list, which holds new = the edit of
# old; an append made directly to the new list after the rename is there already. Not covered,
# and why: (a) a writer that opened I before the rename and writes after the second read (the
# gap between its open and its write, inside one `echo >>`): that line is lost; (b) another
# writer's rename between the check (text and inode against fd 9) and ours (the Edit tool replaces a file by rename: its inode
# changed when tried on 2026-11-21) is replaced by ours unseen, since the file it renamed has no
# name and no fd here afterwards; (c) I changed other than by appends (rewritten in place): its
# text cannot be merged line by line safely, so it is written to the running log and the output,
# not lost silently. Closing (a) and (b) needs a lock, which the author's rule of 2026-11-19
# rules out; each window is a few system calls, against a few edits a day. The case
# fixedbyrace of tools/test_main_watch.sh appends a line just before the rename, which the
# version before this one lost.
known_edit() {
  local c=$1 items=$2 how=$3 old new line f whole
  while :; do
    {
      old=$(cat /dev/fd/9) || return 0
      new=$(while IFS= read -r line; do
        f=$(fixed_of "$line")
        if [ -n "$f" ] && [ -n "$(inter "$(unhash <<<"${line%% *}")" "$items")" ] && git -C "$repo" merge-base --is-ancestor "$f" "$c" 2>/dev/null; then
          [ "$how" = drop ] || sed -E 's/ +fixed-by +[^ ]+//g' <<<"$line"
        else
          printf '%s\n' "$line"
        fi
      done <<<"$old")
      [ "$new" != "$old" ] || return 0
      printf '%s\n' "$new" >"$known_file.$$"
      # Same inode as fd 9 too: a file renamed over the list with the same text would pass the
      # text test while fd 9 holds the replaced inode, and the re-read would then miss appends.
      if [ "$(stat -c %i "$known_file")" = "$(stat -L -c %i /dev/fd/9)" ] && [ "$(cat "$known_file")" = "$old" ]; then
        mv -T "$known_file.$$" "$known_file" || {
          say "could not replace $known_file ($how of $(paste -sd' ' <<<"$items"))"
          return 0
        }
        whole=$(cat /dev/fd/9)
        if [ "$whole" != "$old" ]; then
          if [ -z "$old" ]; then
            printf '%s\n' "$whole" >>"$known_file"
          # The prefix test by length and slice, under LC_ALL=C (bytes): linear. The glob form,
          # [[ $whole == "$old"$'\n'* ]] with ${whole#...}, took 1.1 s at 1000 lines and 16.4 s at
          # 4000 (bash 5, 2026-11-21), quadratic or worse; this form took 5.1 ms at 1000 lines,
          # 29 ms at 16000 and 150 ms at 100000 (TOOLS-push-tests-cleanup).
          elif local LC_ALL=C && [ "${whole:0:${#old}+1}" = "$old"$'\n' ]; then
            printf '%s\n' "${whole:${#old}+1}" >>"$known_file"
          else
            runlog "$known_file was changed in place while main-watch replaced it ($how of $(paste -sd' ' <<<"$items")); its text then, which the list may now lack: $(paste -sd'|' <<<"$whole")"
            say "$known_file was changed in place while it was replaced; its text then is in the running log"
          fi
        fi
        return 0
      fi
    } 9<"$known_file" || return 0
  done
}
# known_checked <C0>: the known failures the last checked commit C0 was checked with, one
# `<kind>:<piece> <row>` a line (none: empty), or `?` when that is not recorded. The checked file's
# fourth field holds them (`<kind>:<piece>=<row>,...`, `-` for none; checked_head and --start write
# it); a line written before that field existed lacks it, and then they are read from the
# running log's line `checked <C0>: every test and benchmark passes but the known failures <p>
# (<row>) ... (<n> landings since ...)`, which checked_head has written in that form since
# 2026-11-20 (running-log.md line 14225 holds af9161e5a's, with the exp_families bench).
known_checked() {
  local f l
  f=$(cut -d' ' -f4 "$checked_file")
  if [ -n "$f" ]; then
    [ "$f" = - ] || tr ',' '\n' <<<"$f" | sed 's/=/ /'
    return 0
  fi
  l=$(command grep -a -F "| NO-LOCKS-optimistic:main-watch | checked $(short "$1"): every test and benchmark passes" "$runlog" 2>/dev/null | tail -n 1)
  [ -n "$l" ] || { echo '?'; return 0; }
  sed -n 's/.* but the known failures \(.*\) ([0-9]* landings since [^)]*)$/\1/p' <<<"$l" |
    command grep -a -o -E '[^ ]+ \([^)]*\)' | sed -E 's/ \((.*)\)$/ \1/'
  return 0
}
# known_state <C0's known failures, from known_checked>: the words for the state C0 was checked in.
known_state() {
  case $1 in
    '') echo "which passed every test and benchmark when it was checked" ;;
    '?') echo "which passed every test and benchmark when it was checked, but for known failures that check did not record" ;;
    *) echo "which passed every test and benchmark when it was checked but the known failures $(sed -E 's/^([^ ]+) (.*)$/\1 (\2)/' <<<"$1" | paste -sd' ')" ;;
  esac
}
# stuck <commit or -> <reason> <details> [<row> <items>]: records the case for the author, puts
# the items on the known list with the row, and returns, so polling goes on. A case already
# recorded (the same commit and reason) is not written again.
stuck() {
  local c=$1 why=$2 row=${4:-} items=${5:-}
  known_add "$row" "$items"
  command grep -a "^stuck $c " "$red" 2>/dev/null | command grep -a -q -F -- " main-watch $why" && return 0
  echo "stuck ${c} $(ts) main-watch $why" >>"$red"
  [ "$c" != - ] || c=
  runlog "STUCK: $why${c:+ (commit $c)}${row:+; $(paste -sd' ' <<<"$items") on $known_file with $row}; polling goes on (main-watch-stuck.md)"
  {
    echo
    echo "## $(ts) main-watch stuck: $why"
    echo
    echo "Holds up: ${row:-nothing in main-watch}${row:+, whose pieces $(paste -sd' ' <<<"$items") main-watch now reports as known failures (in $known_file) and does not bisect or fix; once the fix of the row has landed, append \`fixed-by <the landed commit>\` to their lines there, never take them out}. main-watch goes on polling."
    echo
    echo "Commit: ${c:--}. Head checked: $head. The watcher's worktree, left as it was: $copy. Its logs: $logroot."
    echo
    printf '%s\n' "$3"
    echo
    echo "| Case | Holds up | Commit | Reason |"
    echo "|---|---|---|---|"
    echo "| main-watch $(ts) | main-watch polling | ${c:--} | $why |"
  } >>"$stuck_file"
  say "STUCK: $why. Written to $stuck_file and $red; polling goes on."
}

# The watcher's worktree, at $1, made on first use.
copy=
goto() {
  if [ -z "$copy" ]; then
    copy=$trees/main-watch-$(date -u +%Y%m%d-%H%M%S)-$$
    git -C "$repo" worktree add -q --detach "$copy" "$1" && "$prepare" "$copy" >"$logroot/prepare.log" 2>&1 ||
      { echo "main-watch: making the worktree $copy failed ($logroot/prepare.log)" >&2; exit 2; }
  fi
  git -C "$copy" checkout -q --detach "$1" || { echo "main-watch: checking out $1 in $copy failed" >&2; exit 2; }
}

# spec_at <spec commit>: checks the watcher's spec clone ($ZED_SPEC_DIR) out at it.
spec_at() {
  git -C "$spec_dir" checkout -q --detach "$1" || { echo "main-watch: checking out spec $1 in $spec_dir failed" >&2; exit 2; }
}
# spec_now: fetches the spec's origin; prints its origin/main.
spec_now() {
  git -C "$spec_dir" fetch -q origin || { echo "main-watch: spec fetch failed" >&2; return 1; }
  git -C "$spec_dir" rev-parse origin/main
}
# spec_checked: the spec commit the last checked commit was checked with, S0: the third field of
# the checked file, else (a line written before the field existed, or a commit the clone lacks)
# the spec's last commit on origin/main at or before the line's time, else $spec_head (nothing to
# compare with: every failure then goes on as from zed-impl, as before the field existed).
spec_checked() {
  local s t0
  s=$(cut -d' ' -f3 "$checked_file")
  if [ -n "$s" ] && git -C "$spec_dir" cat-file -e "$s^{commit}" 2>/dev/null; then
    echo "$s"
    return
  fi
  t0=$(cut -d' ' -f2 "$checked_file")
  s=$(git -C "$spec_dir" rev-list -1 --first-parent --before="$t0" origin/main)
  echo "${s:-$spec_head}"
}

# spec_bisect <good> <bad> <items>: with the watcher's worktree at the head, prints the first spec
# commit in good..bad (along origin/main's first parents, oldest first) at which some item fails
# twice. The caller knows every item passes at good and fails twice at bad. Invariant of the
# search: the commit at lo (good when lo = -1) was seen to pass and the one at hi (bad at the
# start) to fail twice; each step halves hi - lo, so it ends after about log2(n) steps with
# hi = lo + 1: a spec commit at which some item fails twice whose parent on the list passes. Where
# items fail and pass again along the list, that is a first bad commit, not necessarily the
# earliest one; where good is not an ancestor of bad (the spec's history rewritten), the list is
# bad's commits that good lacks, and the result is still a failing commit after a passing one.
# Each step is only a run of the items: the pieces read the spec when they run, so nothing builds.
spec_bisect() {
  local good=$1 bad=$2 items=$3 ls n lo hi mid f
  mapfile -t ls < <(git -C "$spec_dir" rev-list --reverse --first-parent "$good..$bad")
  n=${#ls[@]}
  lo=-1 hi=$((n - 1))
  echo "spec commits in ${good:0:9}..${bad:0:9}: $n; zed-impl at $(short "$head"); pieces: $(paste -sd' ' <<<"$items")" >>"$bisect_log"
  while [ $((hi - lo)) -gt 1 ]; do
    mid=$(((lo + hi) / 2))
    spec_at "${ls[$mid]}"
    f=$(fails_twice "$items")
    if [ -n "$(inter "$f" "$items")" ]; then
      echo "spec $((mid + 1))/$n ${ls[$mid]:0:9}: bad ($(paste -sd' ' <<<"$f"))" >>"$bisect_log"
      hi=$mid
    else
      echo "spec $((mid + 1))/$n ${ls[$mid]:0:9}: good" >>"$bisect_log"
      lo=$mid
    fi
  done
  echo "first bad spec commit: ${ls[$hi]:0:9}" >>"$bisect_log"
  echo "${ls[$hi]}"
}

# bisect <good> <bad> <items>: prints the first commit in good..bad at which some item fails
# twice. The steps go to $bisect_log.
bisect() {
  local good=$1 bad=$2 items=$3 ls n lo hi mid prev c f
  # S0 throughout, the spec the good end was checked with: a spec commit since then is not a
  # zed-impl culprit (see The spec above).
  spec_at "$s0"
  mapfile -t ls < <(landings_in "$good" "$bad")
  n=${#ls[@]}
  lo=-1 hi=$((n - 1))
  echo "landings in $(short "$good")..$(short "$bad"): $n; pieces: $(paste -sd' ' <<<"$items")" >>"$bisect_log"
  while [ $((hi - lo)) -gt 1 ]; do
    mid=$(((lo + hi) / 2))
    goto "${ls[$mid]}"
    f=$(fails_twice "$items")
    if [ -n "$(inter "$f" "$items")" ]; then
      echo "landing $((mid + 1))/$n $(short "${ls[$mid]}"): bad ($(paste -sd' ' <<<"$f"))" >>"$bisect_log"
      hi=$mid
    else
      echo "landing $((mid + 1))/$n $(short "${ls[$mid]}"): good" >>"$bisect_log"
      lo=$mid
    fi
  done
  if [ "$lo" -ge 0 ]; then prev=${ls[$lo]}; else prev=$good; fi
  c=${ls[$hi]}
  echo "first bad landing: $(short "$c") (after $(short "$prev"))" >>"$bisect_log"
  if [ "$(git -C "$repo" rev-list --count "$prev..$c")" -gt 1 ]; then
    printf '%s\n' "$items" >"$logroot/predicate-items"
    pushd "$copy" >/dev/null || exit 2
    git bisect start "$c" "$prev" >>"$bisect_log" 2>&1
    MAIN_WATCH_LOGROOT=$logroot MAIN_WATCH_EVIDENCE=$logroot/bisect-evidence \
      git bisect run "$self" --predicate "$logroot/predicate-items" >>"$bisect_log" 2>&1
    c=$(git rev-parse refs/bisect/bad)
    git bisect log >>"$bisect_log" 2>&1
    git bisect reset >>"$bisect_log" 2>&1
    popd >/dev/null || exit 2
    echo "first bad commit inside the landing: $(short "$c")" >>"$bisect_log"
  fi
  echo "$c"
}

# fill <NAME> <text>: replaces each {{NAME}} in $t by the text. Both are quoted: bash 5.2 and
# later (patsub_replacement, on by default) would otherwise put the matched {{NAME}} in place of
# each & in the text, and commit messages and diffs hold &.
fill() {
  local p="{{$1}}" r=$2
  t=${t//"$p"/"$r"}
}

# owner_row <commit> [<repository> <prefix>]: the plan row the commit's subject names in its
# closing parentheses ("... (TOOL-main-watch-start-green)"), else the first its message names,
# else <prefix>-<commit> (FAIL-main-<commit>). The repository is zed-impl's unless given.
owner_row() {
  local ids='\b[A-Z][A-Z0-9]*(-[A-Za-z0-9.]+)+\b' r g=${2:-$repo}
  r=$(git -C "$g" log -1 --format=%s "$1" | sed -n 's/.*(\([^()]*\))[[:space:]]*$/\1/p' | command grep -a -o -E "$ids" | awk 'NR == 1')
  [ -n "$r" ] || r=$(git -C "$g" log -1 --format=%B "$1" | command grep -a -o -E "$ids" | awk 'NR == 1')
  echo "${r:-${3:-FAIL-main}-$(git -C "$g" rev-parse --short=9 "$1")}"
}

# spec_culprit <spec commit> <row> <items>: files the items, which the spec commit broke at the
# head, under the row: a QUEUE line and known lines in queue mode, else a stuck entry (which puts
# them on the known list too). No fixing agent: the fix may belong to zed-impl or to the spec.
spec_culprit() {
  local s=$1 row=$2 items=$3 pieces what
  pieces=$(paste -sd' ' <<<"$items")
  what="spec commit ${s:0:9} \"$(git -C "$spec_dir" log -1 --format=%s "$s")\" breaks $pieces at zed-impl $(short "$head"): they pass there with the spec ${s0:0:9} the last checked commit $(short "$c0") was checked with, so zed-impl lacks that spec change's half, or the spec commit is wrong; bisect log $bisect_log, outputs: $(sort -u "$evidence" | paste -sd' ')"
  if [ -z "$queue" ]; then
    stuck - "spec commit ${s:0:9} breaks $pieces" "$what." "$row" "$items"
  else
    known_add "$row" "$items"
    command grep -a -q "^QUEUE .*: spec commit ${s:0:9} " "$queue" 2>/dev/null ||
      echo "QUEUE $row (filed by main-watch $(ts): $what; the row's owner fixes it and, once the fix has landed, appends \`fixed-by <the landed commit>\` to these pieces' lines in $known_file, never taking them out)" >>"$queue"
    runlog "$row: spec commit ${s:0:9} breaks $pieces at $(short "$head"); queued in $queue and put on $known_file"
    say "$row: spec commit ${s:0:9} breaks $pieces; queued"
  fi
}

# fix <commit> <items>: records the culprit, runs fixing agents until its pieces pass, up to 3.
# In queue mode it queues the culprit to its row instead (see Queue mode above).
fix() {
  local c=$1 items=$2 row lnd sub ids attempt name dir base brief before landed fixed t earlier= out
  row=FAIL-main-$(short "$c")
  lnd=$(landing_of "$c")
  sub=$(git -C "$repo" log -1 --format=%s "$c")
  ids=$(git -C "$repo" log -1 --format=%B "$c" | command grep -a -o -E '\b[A-Z][A-Z0-9]*(-[A-Za-z0-9.]+)+\b' | sort -u | paste -sd' ')
  local pieces
  pieces=$(paste -sd' ' <<<"$items")
  local who="branch $(cut -d' ' -f4 <<<"$lnd") from $(cut -d' ' -f3 <<<"$lnd")${ids:+, rows $ids}"
  command grep -a -q "^open $c .* main-watch " "$red" 2>/dev/null ||
    echo "open $c $(ts) main-watch $(cut -d' ' -f4 <<<"$lnd") pieces: $(sed 's/^[a-z]*://' <<<"$items" | paste -sd' ')" >>"$red"
  command grep -a -q "| $row: first bad commit" "$runlog" 2>/dev/null ||
    runlog "$row: first bad commit $(short "$c") \"$sub\" ($who) fails $pieces; bisect log $bisect_log"
  ledger "$row" queued "$c" "first bad commit of $pieces by bisect ($bisect_log); $who; \"$sub\"" "main-watch: $(short "$c") breaks $pieces"
  if [ -n "$queue" ]; then
    local owner
    owner=$(owner_row "$c")
    command grep -a -q "^QUEUE .*first bad commit $(short "$c") " "$queue" 2>/dev/null ||
      echo "QUEUE $owner (filed by main-watch $(ts): first bad commit $(short "$c") \"$sub\" ($who) fails $pieces; bisect log $bisect_log, outputs in $logroot; the row's owner fixes it and, once the fix has landed, appends \`fixed-by <the landed commit>\` to these pieces' lines in $known_file, never taking them out)" >>"$queue"
    # known_add, not a bare append: the list is read once, after the full runs (check), and the
    # bisect that leads here can take hours, so a person, an agent or a second watcher may have
    # listed the piece meanwhile; a bare append then wrote it twice (TOOLS-push-tests-cleanup;
    # the case queuedup of tools/test_main_watch.sh). A piece already listed keeps its line, as
    # for every other caller of known_add, even when that line names another row.
    known_add "$owner" "$items"
    runlog "$row: queued to $owner in $queue: first bad commit $(short "$c") fails $pieces (no fixing agent in queue mode)"
    say "$row: queued to $owner"
    return 0
  fi
  for attempt in 1 2 3; do
    base=$(head_now) || { stuck "$c" "$row: fetch failed before fix attempt $attempt" "" "$row" "$items"; return 0; }
    name=mwfix-$(short "$c")-$attempt-$(date -u +%H%M%S)-$$
    dir=$trees/$name
    git -C "$repo" worktree add -q -b "wt/$name" "$dir" "$base" && "$prepare" "$dir" >"$logroot/prepare-$name.log" 2>&1 ||
      { stuck "$c" "$row: making the fix worktree $dir failed" "See $logroot/prepare-$name.log." "$row" "$items"; return 0; }
    git -C "$repo" show "$c" >"$logroot/$row.diff"
    out=$(for f in $(sort -u "$evidence"); do cat "$f"; done)
    brief=$logroot/brief-$row-$attempt.md
    t=$(cat "$template")
    fill ROW "$row"
    fill ATTEMPT "$attempt"
    fill COMMIT "$c"
    fill LANDING "$who"
    fill PIECES "$pieces"
    fill EARLIER "$earlier"
    fill BASE "$base"
    fill WORKTREE "$dir"
    fill BRANCH "wt/$name"
    fill MESSAGE "$(git -C "$repo" log -1 --format=%B "$c" | sed 's/^/    /')"
    fill STAT "$(git -C "$repo" show --stat --format= "$c" | sed 's/^/    /')"
    fill DIFF "$logroot/$row.diff"
    fill OUTPUT "$(sed 's/^/    /' <<<"$out")"
    fill BISECT "$(sed 's/^/    /' "$bisect_log")"
    printf '%s\n' "$t" >"$brief"
    before=$(wc -l <"$landings")
    ledger "$row" "active-attempt-$attempt" "$c" "fixing agent in $dir, brief $brief"
    say "$row: fix attempt $attempt in $dir (brief $brief)"
    pushd "$dir" >/dev/null || exit 2
    if [ -n "${MAIN_WATCH_FIXER:-}" ]; then
      "$MAIN_WATCH_FIXER" "$brief" "$dir" >"$logroot/fixer-$name.out" 2>&1
    else
      claude -p --model opus --dangerously-skip-permissions <"$brief" >"$logroot/fixer-$name.out" 2>&1
    fi
    popd >/dev/null || exit 2
    landed=$(tail -n +$((before + 1)) "$landings" | awk -v d="$dir" '$3 == d { s = $1 } END { print s }')
    if [ -z "$landed" ]; then
      ledger "$row" blocked "$c" "fix attempt $attempt ended without landing ($logroot/fixer-$name.out); worktree $dir left as it was"
      stuck "$c" "$row: the fixing agent of attempt $attempt ended without landing" "Pieces: $pieces. Brief: $brief. Agent output: $logroot/fixer-$name.out. Its worktree, left as it was: $dir." "$row" "$items"
      return 0
    fi
    head_now >/dev/null
    git -C "$dir" merge-base --is-ancestor HEAD origin/main && "$remove" "$dir" >>"$logroot/remove.log" 2>&1 &&
      git -C "$repo" branch -q -D "wt/$name" >>"$logroot/remove.log" 2>&1
    goto "$landed"
    # The fix is judged with the spec of this check, the one its agent's world has.
    spec_at "$spec_head"
    : >"$evidence"
    fixed=$(fails_twice "$items")
    if [ -z "$(inter "$fixed" "$items")" ]; then
      ledger "$row" done "$c $landed" "fixed by $landed (attempt $attempt): $pieces pass there"
      echo "fixed $c $(ts) main-watch by $landed" >>"$red"
      runlog "$row: fixed by $(short "$landed") (attempt $attempt); $pieces pass there"
      say "$row: fixed by $(short "$landed")"
      for t in $items; do good[$t]=$landed; done
      return 0
    fi
    items=$(inter "$fixed" "$items")
    pieces=$(paste -sd' ' <<<"$items")
    earlier+="Attempt $attempt landed $landed, and these pieces still fail at it: $pieces. Its brief: $brief; its agent's output: $logroot/fixer-$name.out."$'\n'
    runlog "$row: fix attempt $attempt landed $(short "$landed"), but $pieces still fail"
  done
  stuck "$c" "$row: $pieces still fail after 3 fix attempts" "$earlier" "$row" "$items"
}

# checked_head <C0> <known failures>: records $head as checked, publishes the build of the
# watcher's worktree at $head and removes the worktree. The known failures (`<p> (<row>) ...`) go
# in the checked line's fourth field, `<p>=<row>,...` or `-`, for known_checked; the running-log
# line keeps its form, which known_checked reads for older checked lines.
checked_head() {
  local c0=$1 known=$2 kf
  kf=$(command grep -a -o -E '[^ ]+ \([^)]*\)' <<<"$known" | sed -E 's/ \((.*)\)$/=\1/' | paste -sd,)
  echo "$head $(ts) $spec_head ${kf:--}" >"$checked_file.$$" && mv -T "$checked_file.$$" "$checked_file"
  runlog "checked $(short "$head"): every test and benchmark passes${known:+ but the known failures $known}($(landings_in "$c0" "$head" | wc -l) landings since $(short "$c0"))"
  say "checked $(short "$head"): everything passes${known:+ but the known failures $known}"
  # The worktree's build, of a head where everything passes, becomes the central build that
  # seed-build.sh gives each new worktree (TOOLS-clippy-cold-per-worktree). Since the
  # merge batches stopped on 2026-11-19 nothing else publishes it, and a central build 1062
  # commits behind main seeded clippy no better than an empty one (zedc-check after a change
  # to zed-graph: 75 and 106 s, against 87 and 107 s empty and 17 and 24 s seeded from a
  # current build, 2026-11-20). A failed publish leaves the old central build and does not
  # stop the watcher. The worktree may stand at another commit: a bisect leaves it at the
  # culprit, and a failure filed as old leaves it at C0 (in the watcher's first run on
  # 2026-11-21 it published b7f782a7d, the culprit, after checking eaed40fc6). So the head is
  # checked out first, and a worktree where that fails is not published.
  if [ -n "$copy" ] && ! git -C "$copy" checkout -q --detach "$head" >>"$logroot/publish.log" 2>&1; then
    say "checking out $(short "$head") in $copy failed ($logroot/publish.log); the central build is unchanged"
  elif [ -n "$copy" ]; then
    "$publish" "$copy" >>"$logroot/publish.log" 2>&1 ||
      say "publishing the build of $copy failed ($logroot/publish.log); the central build is unchanged"
  fi
  [ -z "$copy" ] || "$remove" "$copy" >>"$logroot/remove.log" 2>&1 || say "could not remove $copy ($logroot/remove.log)"
  copy=
}

# check <C0> <head>: runs everything at the head, bisects and fixes each failure, and repeats at
# the new head until everything passes; then records that head as checked.
check() {
  local c0=$1 f fails items g c f1 all known r
  head=$2
  declare -gA good=()
  while :; do
    # The spec of this pass, S, read by every run until the next pass (globals: fix and
    # checked_head read them).
    spec_head=$(spec_now) || { say "spec fetch failed; checking again at the next poll"; return 0; }
    s0=$(spec_checked)
    say "running every test and benchmark at $(short "$head") ($(landings_in "$c0" "$head" | wc -l) landings since $(short "$c0")), spec ${spec_head:0:9}"
    goto "$head"
    spec_at "$spec_head"
    while read -r p r; do
      runlog "not run: $p ($r) at $(short "$head"), marked skip in $known_file"
    done < <(known_lines "$head" in | awk '$3 == "skip" { print $1, $2 }')
    all=
    fails=
    local crashed=
    for k in test bench; do
      f=$(run "$k")
      fails+=$(failed_in "$f" "$k")$'\n'
      for p in $(passed_in "$f" "$k"); do good[$p]=$head; done
      all+="$f "
      r=$(cat "${f%.out}.rc")
      [ "$r" -lt 128 ] || crashed+="$k (exit $r) "
    done
    # The runner itself ended by a signal (tools/run_tests.sh killed, by the kernel's OOM killer
    # or by hand), or tools/farm_run.sh could not run a VM's share (exit 129): the pieces it did not report would read as passing, so the head is not checked;
    # the next poll runs everything again. (A crashing piece is not this: run_tests.sh reports it
    # with its rc.) The runs of fails_twice are not checked this way: a runner killed there reads
    # as the pieces passing, which at worst calls a failure a flake or moves a bisect step.
    if [ -n "$crashed" ]; then
      stuck - "the run of every ${crashed% } at $(short "$head") ended by a signal or lost a VM's share" "The pieces it did not report would read as passing, so $(short "$head") is not checked; the next poll runs everything again. Outputs: $all"
      return 0
    fi
    fails=$(sed '/^$/d' <<<"$fails")
    # A failure that $known_file gives a plan row ran like every piece and is reported with its
    # row, but is not run again, bisected or fixed here, and does not keep the head from being
    # checked and its build published: its row's owner fixes it (TOOL-main-watch-start-green,
    # 2026-11-20: rows owned bench failures at every commit, so no head could be checked). Only
    # lines in force at the head count (known_lines): a line whose fixed-by commit the head
    # contains does not (MAINWATCH-known-fixed-by). The list is read after the runs, so a line
    # appended during them counts.
    local kin kfixed fb line dropped=
    kin=$(known_lines "$head" in)
    kfixed=$(known_lines "$head" fixed)
    known=
    for p in $fails; do
      r=$(awk -v p="$p" '$1 == p { print $2; exit }' <<<"$kin")
      [ -n "$r" ] || continue
      known+="$p ($r) "
      fails=$(minus "$fails" "$p")
    done
    [ -z "$known" ] || {
      say "known failures at $(short "$head"): $known"
      runlog "known failures at $(short "$head"), each owned by its row ($known_file): $known"
    }
    # A fixed-by commit not in origin/main as this check fetched it is either newer (it landed
    # while an older head was being checked, as 0ad3544ed did during the check of 46c1d2b71) or
    # never comes into a head (a typo, or the sha of a branch commit that merge-push.sh's rebase
    # replaced), and then its line stays in force for good: said at each check, so its row's owner
    # can correct the second kind.
    while IFS= read -r line; do
      fb=$(fixed_of "$line")
      [ -z "$fb" ] || git -C "$repo" merge-base --is-ancestor "$fb" origin/main 2>/dev/null ||
        runlog "the fixed-by commit $fb of the line \"$line\" in $known_file is not in origin/main as fetched for this check, so the line stays in force; if that commit is not the one merge-push.sh printed as landed, its row's owner corrects it"
    done <<<"$kin"
    # A listed piece that passes at the head: with a fixed-by commit the head contains, its fix
    # holds, and its line is taken out here; with none, it is reported, for its row's owner to
    # append fixed-by once the fix has landed.
    for p in $(awk '{ print $1 }' <<<"$kfixed" | sort -u); do
      [ "${good[$p]:-}" != "$head" ] || dropped+="$p"$'\n'
    done
    dropped=$(sed '/^$/d' <<<"$dropped")
    if [ -n "$dropped" ]; then
      known_edit "$head" "$dropped" drop
      runlog "fixed at $(short "$head"): $(paste -sd' ' <<<"$dropped") pass there, which holds the fixed-by commit of each line; their lines are taken out of $known_file"
      say "taken out of $known_file, passing at $(short "$head") with their fixed-by commits: $(paste -sd' ' <<<"$dropped")"
    fi
    for p in $(awk '{ print $1 }' <<<"$kin"); do
      [ "${good[$p]:-}" != "$head" ] || say "$p, listed in $known_file, passes at $(short "$head"); once its row's fix has landed, append fixed-by <the landed commit> to its line"
    done
    # Each failure run again alone; one that passes is a flake.
    items=
    for p in $fails; do
      : >"$evidence"
      if [ -z "$(fails_twice "$p" | sed '/^$/d')" ]; then
        echo "$(ts) $(short "$head") $p full run: $(for f in $all; do line_of "$f" "$p"; done | paste -sd' ') alone: passed" >>"$flakes"
        runlog "flake at $(short "$head"): $p failed in the full run and passed alone ($flakes)"
        say "flake: $p (passed alone)"
      else
        items+="$p"$'\n'
      fi
    done
    items=$(sed '/^$/d' <<<"$items")
    # Confirmed failures whose line names a fixed-by commit the head contains: the fix did not
    # hold. They go back to the line's row, not to a new one (they are its failure, and the row
    # was told), and the line loses its fixed-by, so it is in force again until the owner writes a
    # new one; no spec search or bisect, which would only find the cause the row already owns.
    local back= rb
    for p in $items; do
      rb=$(awk -v p="$p" '$1 == p { print $2; exit }' <<<"$kfixed")
      [ -n "$rb" ] || continue
      back+="$p"$'\n'
      known+="$p ($rb) "
      local what="$p still fails at $(short "$head"), which holds $(awk -v p="$p" '$1 == p { for (i = 3; i < NF; i++) if ($i == "fixed-by") print $(i + 1) }' <<<"$kfixed" | paste -sd' '), the commit its line in $known_file names with fixed-by, so that fix did not hold; the line is in force again without its fixed-by. Outputs: $all"
      if [ -n "$queue" ]; then
        command grep -a -F "$p still fails at $(short "$head"), which holds" "$queue" 2>/dev/null | command grep -a -q "^QUEUE $rb " ||
          echo "QUEUE $rb (filed by main-watch $(ts): $what; the row's owner fixes it and, once the fix has landed, appends \`fixed-by <the landed commit>\` to the line again)" >>"$queue"
        runlog "$rb: $p still fails at $(short "$head"), which holds its fixed-by commit; queued in $queue, its line in force again"
        say "$rb: $p still fails at $(short "$head") with its fixed-by commit; queued"
      else
        stuck - "$p still fails at $(short "$head") with its fixed-by commit" "$what." "$rb" "$p"
      fi
    done
    if [ -n "$back" ]; then
      known_edit "$head" "$back" unfix
      items=$(minus "$items" "$(sed '/^$/d' <<<"$back")")
    fi
    if [ -z "$items" ]; then
      checked_head "$c0" "$known"
      return 0
    fi
    say "confirmed failures at $(short "$head"): $(paste -sd' ' <<<"$items")"
    # Failures from the spec (see The spec above): those that pass at the head with S0 were
    # broken by a spec commit in S0..S. The worktree is at the head still (the runs of
    # fails_twice above check nothing out). Each set goes to its first bad spec commit, as the
    # bisect below does for zed-impl; the rest go on with S0.
    if [ "$spec_head" != "$s0" ]; then
      spec_at "$s0"
      : >"$evidence"
      f=$(inter "$(fails_twice "$items")" "$items")
      local sset sc sf row
      sset=$(minus "$items" "$f")
      while [ -n "$sset" ]; do
        bisect_log=$logroot/bisect-spec-$(date -u +%H%M%S%N).log
        : >"$evidence"
        sc=$(spec_bisect "$s0" "$spec_head" "$sset")
        spec_at "$sc"
        sf=$(inter "$(fails_twice "$sset")" "$sset")
        if [ -z "$sf" ]; then
          stuck - "the search of the spec commits ${s0:0:9}..${spec_head:0:9} for $(paste -sd' ' <<<"$sset") named ${sc:0:9}, at which none fails twice" "Bisect log: $bisect_log." "FAIL-spec-${sc:0:9}" "$sset"
          for p in $sset; do known+="$p (FAIL-spec-${sc:0:9}) "; done
          break
        fi
        row=$(owner_row "$sc" "$spec_dir" FAIL-spec)
        spec_culprit "$sc" "$row" "$sf"
        for p in $sf; do known+="$p ($row) "; done
        sset=$(minus "$sset" "$sf")
      done
      spec_at "$s0"
      items=$f
      if [ -z "$items" ]; then
        checked_head "$c0" "$known"
        return 0
      fi
    fi
    # Failures never seen passing in this check: do they fail at C0 too? (With S0, the spec C0
    # passed with: a failure there means the machine changed or the piece is flaky.)
    local fresh=
    for p in $items; do [ -n "${good[$p]:-}" ] || fresh+="$p"$'\n'; done
    fresh=$(sed '/^$/d' <<<"$fresh")
    if [ -n "$fresh" ]; then
      goto "$c0"
      spec_at "$s0"
      : >"$evidence"
      f=$(inter "$(fails_twice "$fresh")" "$fresh")
      if [ -n "$f" ]; then
        # They existed before the range, so a bisect over it cannot find their cause. One that C0
        # was checked with as a known failure of a row R0 is R0's: its line was taken out before
        # a checked head held its fix (FAIL-main-af9161e5a, 2026-11-21, a duplicate of
        # PRES-growth-exp-families), so it goes back to R0 and onto the list with R0. The rest are
        # filed as FAIL-main-<C0>. All go on the known list, and checking goes on without them.
        local old pieces k0 r0 fnew= what
        old=FAIL-main-$(short "$c0")
        k0=$(known_checked "$c0")
        for p in $f; do
          r0=$([ "$k0" = '?' ] || awk -v p="$p" '$1 == p { print $2; exit }' <<<"$k0")
          if [ -z "$r0" ]; then
            fnew+="$p"$'\n'
            continue
          fi
          known+="$p ($r0) "
          what="$p fails at $(short "$head") and at the last checked commit $(short "$c0"), which was checked with it as a known failure of $r0, so it is $r0's: its line was taken out of $known_file before a checked commit held its fix; it is on the list with $r0 again; outputs: $(sort -u "$evidence" | paste -sd' ')"
          if [ -n "$queue" ]; then
            known_add "$r0" "$p"
            command grep -a -F "$p fails at $(short "$head") and at the last checked commit" "$queue" 2>/dev/null | command grep -a -q "^QUEUE $r0 " ||
              echo "QUEUE $r0 (filed by main-watch $(ts): $what; once the fix has landed, its owner appends \`fixed-by <the landed commit>\` to the line, never taking it out)" >>"$queue"
            runlog "$r0: $p fails at $(short "$c0") too, where it was $r0's known failure; queued in $queue and put on $known_file with $r0"
            say "$r0: $p fails at $(short "$c0") too, where it was known; queued"
          else
            stuck - "$p fails at the last checked commit $(short "$c0") too, where it was a known failure of $r0" "$what." "$r0" "$p"
          fi
        done
        fnew=$(sed '/^$/d' <<<"$fnew")
        pieces=$(paste -sd' ' <<<"$fnew")
        if [ -z "$fnew" ]; then
          :
        elif [ -n "$queue" ]; then
          known_add "$old" "$fnew"
          command grep -a -q "^QUEUE $old " "$queue" 2>/dev/null ||
            echo "QUEUE $old (filed by main-watch $(ts): $pieces fail at the last checked commit $(short "$c0") too, $(known_state "$k0"), so no bisect over $(short "$c0")..$(short "$head") can find their cause; outputs: $(sort -u "$evidence" | paste -sd' '); the row's owner fixes it and, once the fix has landed, appends \`fixed-by <the landed commit>\` to these pieces' lines in $known_file, never taking them out)" >>"$queue"
          runlog "$old: $pieces fail at the last checked commit $(short "$c0") too; queued in $queue and put on $known_file"
          say "$old: $pieces fail at $(short "$c0") too; queued"
        else
          stuck - "$pieces fail at the last checked commit $(short "$c0") too" "These pieces fail at $(short "$c0"), $(known_state "$k0"). Outputs: $(sort -u "$evidence" | paste -sd' ')." "$old" "$fnew"
        fi
        for p in $fnew; do known+="$p ($old) "; done
        items=$(minus "$items" "$f")
        if [ -z "$items" ]; then
          checked_head "$c0" "$known"
          return 0
        fi
      fi
    fi
    # Bisect each group of failures that last passed at the same commit, culprit by culprit.
    for g in $(for p in $items; do echo "${good[$p]:-$c0}"; done | sort -u); do
      local set
      set=$(for p in $items; do [ "${good[$p]:-$c0}" = "$g" ] && echo "$p"; done)
      while [ -n "$set" ]; do
        bisect_log=$logroot/bisect-$(date -u +%H%M%S%N).log
        : >"$evidence"
        c=$(bisect "$g" "$head" "$set")
        # bisect runs in a subshell, so its own failures end only that subshell.
        if [ -z "$c" ]; then
          stuck - "the bisect of $(paste -sd' ' <<<"$set") over $(short "$g")..$(short "$head") named no commit" "Bisect log: $bisect_log." "FAIL-main-$(short "$head")" "$set"
          break
        fi
        goto "$c"
        : >"$evidence"
        f1=$(inter "$(fails_twice "$set")" "$set")
        if [ -z "$f1" ]; then
          stuck "$c" "the bisect named $(short "$c") but none of $(paste -sd' ' <<<"$set") fails there twice" "Bisect log: $bisect_log." "FAIL-main-$(short "$c")" "$set"
          break
        fi
        say "culprit $(short "$c"): $(paste -sd' ' <<<"$f1")"
        fix "$c" "$f1"
        set=$(minus "$set" "$f1")
      done
    done
    # Queue mode: every failure is now queued to its row and on the known list, and no fix has
    # landed, so a run at the head again would find the same; the head is checked with them as
    # known failures.
    if [ -n "$queue" ]; then
      for p in $items; do known+="$p ($(unhash <"$known_file" | awk -v p="$p" '$1 == p { r = $2 } END { print r }')) "; done
      checked_head "$c0" "$known"
      return 0
    fi
    head=$(head_now) || { say "fetch failed after the fixes; checking again at the next poll"; return 0; }
  done
}

mkdir -p "$home" "$trees"
# merge-push.sh names a landing's worktree by its real path; the fix worktree must match it.
trees=$(realpath -e "$trees")
logroot=$home/main-watch-runs/$(date -u +%Y%m%d-%H%M%S)-$$
mkdir -p "$logroot" || exit 2
evidence=$logroot/evidence
: >"$evidence"
# The watcher's own spec clone (see The spec above): a local clone shares the seed's objects by
# hardlinks (the seed is only read), then fetches the seed's own remote, so origin/main is the
# spec's, whatever the seed's working tree holds.
spec_url=${MAIN_WATCH_SPEC_URL:-$(git -C "$spec_seed" remote get-url origin)}
spec_dir=$logroot/spec
git clone -q --no-checkout "$spec_seed" "$spec_dir" && git -C "$spec_dir" remote set-url origin "$spec_url" &&
  git -C "$spec_dir" fetch -q origin || { echo "main-watch: cloning the spec from $spec_seed and fetching $spec_url into $spec_dir failed" >&2; exit 2; }
export ZED_SPEC_DIR=$spec_dir
head= spec_head= s0=
if [ -n "$start" ]; then
  spec_head=$(spec_now) || exit 2
  # The start commit is taken as checked with the known lines in force there (known_checked).
  kf=$(known_lines "$start" in | awk '{ print $1 "=" $2 }' | paste -sd,)
  echo "$start $(ts) $spec_head ${kf:--}" >"$checked_file.$$" && mv -T "$checked_file.$$" "$checked_file"
  say "recorded $(short "$start") as checked"
fi
n=0
while :; do
  n=$((n + 1))
  [ -s "$checked_file" ] || {
    echo "main-watch: no last checked commit ($checked_file) to count and bisect from; start it with --start <commit>, a commit at which every test and benchmark passes" >&2
    exit 2
  }
  if head=$(head_now); then
    c0=$(cut -d' ' -f1 "$checked_file")
    k=$(landings_in "$c0" "$head" | wc -l)
    say "poll $n: $k landings since the last checked commit $(short "$c0"), head $(short "$head")"
    if [ "$k" -ge "$min" ]; then
      check "$c0" "$head"
    fi
  else
    say "poll $n: fetch failed; trying again at the next poll"
  fi
  [ -n "$polls" ] && [ "$n" -ge "$polls" ] && exit 0
  sleep "$poll"
done
