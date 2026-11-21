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
# Known failures. main-watch-known.txt lists failures a plan row owns, one a line,
# `<kind>:<piece> <row>`: such a piece still runs and is reported with its row, but is not
# bisected or fixed here, and does not keep a head from being checked. A third field `skip` keeps
# the piece from being started at all (tools/run_tests.sh --except), for a piece too costly to run
# while it fails: bench rung2 at n = 600 held 67 to 71 GB a run (TOOL-main-watch-start-green).
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
# local suite alone).
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
landings=$home/landings.log
checked_file=$home/main-watch.checked
red=$home/main-red.log
runlog=$home/running-log.md
ledger=$home/ledger.jsonl
stuck_file=$home/main-watch-stuck.md
flakes=$home/main-watch-flakes.log
# Failures a plan row owns, one a line: <kind>:<piece> <row> [skip]. Written by hand and in queue
# mode; see check.
known_file=$home/main-watch-known.txt
queue=${MAIN_WATCH_QUEUE:-}
self=$(realpath -e "$0")
export MAIN_WATCH_HOME=$home MAIN_WATCH_REPO=$repo MAIN_WATCH_FULL=$full MAIN_WATCH_JOBS=$jobs

ts() { date -u +%FT%TZ; }
say() { echo "main-watch: $*"; }
short() { git -C "$repo" rev-parse --short=9 "$1"; }

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
  local a=(--logs "$logs")
  if [ "$kind" = bench ]; then a+=(--bench); elif [ -n "$full" ]; then a+=("$full"); fi
  if [ ${#names[@]} -gt 0 ]; then
    # Each name its own alternative, ^<name>$|^<name>$: run_tests.sh reads the text before the
    # first :: of each top-level alternative as the group, which must be an extended regular
    # expression by itself, so ^(a::x|b::y)$ is refused (exit 2, no piece run) and each failure
    # read as a flake (TOOL-main-watch-start-green, 2026-11-20; test_main_watch.sh case zrun).
    a+=(--only "$(printf '%s\n' "${names[@]}" | sed 's/[][\.*^$+?(){}|/]/\\&/g; s/.*/^&$/' | paste -sd'|')")
  elif [ $# -gt 0 ]; then
    a+=(--list)
  else
    # A run of every piece leaves out those of this kind the known list marks skip, each as its
    # own anchored alternative, as for --only above.
    local skip
    skip=$([ -s "$known_file" ] && awk -v k="$kind:" '$3 == "skip" && index($1, k) == 1 { print substr($1, length(k) + 1) }' "$known_file" |
      sed 's/[][\.*^$+?(){}|/]/\\&/g; s/.*/^&$/' | paste -sd'|')
    [ -z "$skip" ] || a+=(--except "$skip")
  fi
  "$zrun" tools/run_tests.sh "${a[@]}" "$jobs"
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
# The pieces of kind $2 that failed, or passed, in the output $1, as <kind>:<piece>, one a line;
# a failed build is <kind>:BUILD.
failed_in() {
  command grep -a -o -E '^[^ ]+ rc=[1-9][0-9]* ' "$1" | cut -d' ' -f1 | sed "s/^/$2:/"
  command grep -a -q 'BUILD FAILED' "$1" && echo "$2:BUILD"
  return 0
}
passed_in() { command grep -a -o -E '^[^ ]+ rc=0 ' "$1" | cut -d' ' -f1 | sed "s/^/$2:/"; }
# The summary line of piece $2 (<kind>:<piece>) in the output $1.
line_of() { command grep -a -m 1 -E "^${2#*:} rc=" "$1"; }
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
    [ -s "$known_file" ] && awk -v p="$p" '$1 == p { f = 1 } END { exit !f }' "$known_file" && continue
    echo "$p $1" >>"$known_file"
  done
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
    echo "Holds up: ${row:-nothing in main-watch}${row:+, whose pieces $(paste -sd' ' <<<"$items") main-watch now reports as known failures (in $known_file) and does not bisect or fix; take their lines out once the row fixes them}. main-watch goes on polling."
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

# bisect <good> <bad> <items>: prints the first commit in good..bad at which some item fails
# twice. The steps go to $bisect_log.
bisect() {
  local good=$1 bad=$2 items=$3 ls n lo hi mid prev c f
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

# owner_row <commit>: the plan row the commit's subject names in its closing parentheses
# ("... (TOOL-main-watch-start-green)"), else the first its message names, else FAIL-main-<commit>.
owner_row() {
  local ids='\b[A-Z][A-Z0-9]*(-[A-Za-z0-9.]+)+\b' r
  r=$(git -C "$repo" log -1 --format=%s "$1" | sed -n 's/.*(\([^()]*\))[[:space:]]*$/\1/p' | command grep -a -o -E "$ids" | awk 'NR == 1')
  [ -n "$r" ] || r=$(git -C "$repo" log -1 --format=%B "$1" | command grep -a -o -E "$ids" | awk 'NR == 1')
  echo "${r:-FAIL-main-$(short "$1")}"
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
      echo "QUEUE $owner (filed by main-watch $(ts): first bad commit $(short "$c") \"$sub\" ($who) fails $pieces; bisect log $bisect_log, outputs in $logroot; the row's owner fixes it and takes these pieces' lines out of $known_file)" >>"$queue"
    for t in $items; do echo "$t $owner" >>"$known_file"; done
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
# watcher's worktree and removes the worktree.
checked_head() {
  local c0=$1 known=$2
  echo "$head $(ts)" >"$checked_file.$$" && mv -T "$checked_file.$$" "$checked_file"
  runlog "checked $(short "$head"): every test and benchmark passes${known:+ but the known failures $known}($(landings_in "$c0" "$head" | wc -l) landings since $(short "$c0"))"
  say "checked $(short "$head"): everything passes${known:+ but the known failures $known}"
  # The worktree's build, of a head where everything passes, becomes the central build that
  # seed-build.sh gives each new worktree (TOOLS-clippy-cold-per-worktree). Since the
  # merge batches stopped on 2026-11-19 nothing else publishes it, and a central build 1062
  # commits behind main seeded clippy no better than an empty one (zedc-check after a change
  # to zed-graph: 75 and 106 s, against 87 and 107 s empty and 17 and 24 s seeded from a
  # current build, 2026-11-20). A failed publish leaves the old central build and does not
  # stop the watcher.
  [ -z "$copy" ] || "$publish" "$copy" >>"$logroot/publish.log" 2>&1 ||
    say "publishing the build of $copy failed ($logroot/publish.log); the central build is unchanged"
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
    say "running every test and benchmark at $(short "$head") ($(landings_in "$c0" "$head" | wc -l) landings since $(short "$c0"))"
    goto "$head"
    while read -r p r; do
      runlog "not run: $p ($r) at $(short "$head"), marked skip in $known_file"
    done < <([ -s "$known_file" ] && awk '$3 == "skip" { print $1, $2 }' "$known_file")
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
    # or by hand): the pieces it did not report would read as passing, so the head is not checked;
    # the next poll runs everything again. (A crashing piece is not this: run_tests.sh reports it
    # with its rc.) The runs of fails_twice are not checked this way: a runner killed there reads
    # as the pieces passing, which at worst calls a failure a flake or moves a bisect step.
    if [ -n "$crashed" ]; then
      stuck - "the run of every ${crashed% } at $(short "$head") ended by a signal" "The pieces it did not report would read as passing, so $(short "$head") is not checked; the next poll runs everything again. Outputs: $all"
      return 0
    fi
    fails=$(sed '/^$/d' <<<"$fails")
    # A failure that $known_file gives a plan row ran like every piece and is reported with its
    # row, but is not run again, bisected or fixed here, and does not keep the head from being
    # checked and its build published: its row's owner fixes it (TOOL-main-watch-start-green,
    # 2026-11-20: rows owned bench failures at every commit, so no head could be checked). A
    # listed piece that passes is reported, so its line can be taken out.
    known=
    for p in $fails; do
      r=$([ -s "$known_file" ] && awk -v p="$p" '$1 == p { print $2; exit }' "$known_file")
      [ -n "$r" ] || continue
      known+="$p ($r) "
      fails=$(minus "$fails" "$p")
    done
    [ -z "$known" ] || {
      say "known failures at $(short "$head"): $known"
      runlog "known failures at $(short "$head"), each owned by its row ($known_file): $known"
    }
    for p in $([ -s "$known_file" ] && awk '{ print $1 }' "$known_file"); do
      [ "${good[$p]:-}" != "$head" ] || say "$p, listed in $known_file, passes at $(short "$head"); take its line out"
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
    if [ -z "$items" ]; then
      checked_head "$c0" "$known"
      return 0
    fi
    say "confirmed failures at $(short "$head"): $(paste -sd' ' <<<"$items")"
    # Failures never seen passing in this check: do they fail at C0 too?
    local fresh=
    for p in $items; do [ -n "${good[$p]:-}" ] || fresh+="$p"$'\n'; done
    fresh=$(sed '/^$/d' <<<"$fresh")
    if [ -n "$fresh" ]; then
      goto "$c0"
      : >"$evidence"
      f=$(inter "$(fails_twice "$fresh")" "$fresh")
      if [ -n "$f" ]; then
        # They existed before the range, so a bisect over it cannot find their cause: filed as
        # FAIL-main-<C0>, on the known list, and checking goes on without them.
        local old pieces
        old=FAIL-main-$(short "$c0")
        pieces=$(paste -sd' ' <<<"$f")
        if [ -n "$queue" ]; then
          known_add "$old" "$f"
          command grep -a -q "^QUEUE $old " "$queue" 2>/dev/null ||
            echo "QUEUE $old (filed by main-watch $(ts): $pieces fail at the last checked commit $(short "$c0") too, which passed every test and benchmark when it was checked, so no bisect over $(short "$c0")..$(short "$head") can find their cause; outputs: $(sort -u "$evidence" | paste -sd' '); the row's owner fixes it and takes these pieces' lines out of $known_file)" >>"$queue"
          runlog "$old: $pieces fail at the last checked commit $(short "$c0") too; queued in $queue and put on $known_file"
          say "$old: $pieces fail at $(short "$c0") too; queued"
        else
          stuck - "$pieces fail at the last checked commit $(short "$c0") too" "These pieces fail at $(short "$c0"), which passed every test and benchmark when it was checked. Outputs: $(sort -u "$evidence" | paste -sd' ')." "$old" "$f"
        fi
        for p in $f; do known+="$p ($old) "; done
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
      for p in $items; do known+="$p ($(awk -v p="$p" '$1 == p { r = $2 } END { print r }' "$known_file")) "; done
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
head=
if [ -n "$start" ]; then
  echo "$start $(ts)" >"$checked_file.$$" && mv -T "$checked_file.$$" "$checked_file"
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
