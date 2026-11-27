#!/bin/bash
# Tests tools/main_watch.sh on toy repositories: a bare remote, the watcher's clone and a clone the
# landings are made from. The pieces are stubs: the files `tests` and `benches` list them, and a
# piece fails while broken/<piece> exists. t_flaky fails on its first run only (a flake). A stub
# fixer (MAIN_WATCH_FIXER) deletes broken/<piece> for each piece its brief names, commits, pushes
# and appends its landing to landings.log, as merge-push.sh does.
# Usage: tools/test_main_watch.sh [case...]; with no case, all. `controls:<name>` runs the one
# mutant <name> of the case controls, so each can run apart under the 60 s limit of a piece.
# The toy repositories are made under the directory it prints, which is removed at exit unless
# MW_KEEP=1.
pushd "$(dirname "$0")/.." >/dev/null || exit 2
root=$(pwd -P)
popd >/dev/null || exit 2
. "$root/tools/test_lib.sh"
# MW_WATCH: the script under test, for the negative controls (mutants that must fail).
watch=${MW_WATCH:-$root/tools/main_watch.sh}
fails=0
top=$(mktemp -d "${TMPDIR:-/tmp}/test-main-watch.XXXXXX")
# The toy repositories hold thousands of files, and /tmp is a tmpfs with a fixed number of inodes
# (it ran out on 2026-11-21, with leftover test-main-watch.* directories of 5,000 to 13,000 files
# among the largest), so the directory is removed at every exit, failures and signals included
# (timeout sends TERM, after which bash runs no EXIT trap unless the signal is trapped). The rm
# names the literal path mktemp made, fixed when the trap is set; MW_KEEP=1 keeps it for
# inspection.
case $top in "${TMPDIR:-/tmp}"/test-main-watch.??????) ;; *) echo "mktemp gave '$top'"; exit 2 ;; esac
if [ -z "${MW_KEEP:-}" ]; then
  trap "rm -rf --one-file-system --preserve-root=all $(printf %q "$top")" EXIT
  trap 'exit 143' TERM INT HUP
fi
echo "toy repositories under $top${MW_KEEP:+ (kept: MW_KEEP)}"

# Makes the toy repositories and stubs in the new directory $t; the base commit is $c0. With $1
# set, the piece $1 is broken in the base commit already.
setup() {
  mkdir -p "$t/src/broken" "$t/home" "$t/trees" "$t/bin" "$t/state"
  printf '%s\n' t_alpha t_gamma t_flaky t_delta >"$t/src/tests"
  printf '%s\n' b_beta b_eps >"$t/src/benches"
  : >"$t/src/broken/.keep"
  [ -z "${1:-}" ] || echo x >"$t/src/broken/$1"
  git -C "$t/src" init -q -b main
  git -C "$t/src" add -A
  gitc -C "$t/src" commit -q -m base
  git clone -q --bare "$t/src" "$t/remote.git"
  for c in repo dev; do
    git clone -q "$t/remote.git" "$t/$c"
    git -C "$t/$c" config user.name "$c"
    git -C "$t/$c" config user.email "$c@localhost"
  done
  c0=$(git -C "$t/repo" rev-parse HEAD)
  # The spec: a bare remote, and a clone standing in for the author's checkout
  # (/home/luke/Work/zed), exported as ZED_SPEC_DIR as a caller's environment may have it; the
  # watcher must read neither that variable nor that working tree, only its own pinned clone.
  mkdir -p "$t/specsrc/breaks"
  echo "# spec" >"$t/specsrc/DESIGN.md"
  : >"$t/specsrc/breaks/.keep"
  git -C "$t/specsrc" init -q -b main
  git -C "$t/specsrc" add -A
  gitc -C "$t/specsrc" commit -q -m "spec base"
  git clone -q --bare "$t/specsrc" "$t/spec.git"
  git clone -q "$t/spec.git" "$t/speclive"
  export ZED_SPEC_DIR=$t/speclive MAIN_WATCH_SPEC_SEED=$t/spec.git MAIN_WATCH_SPEC_URL=$t/spec.git
  # The runner: run_tests.sh's summary lines; BUILD FAILED while broken/BUILD exists.
  cat >"$t/bin/run" <<'EOF'
#!/bin/bash
logs=$1 kind=$2
shift 2
mkdir -p "$logs"
names=()
# MW_HASH: each piece is a unit test of a library, named toylib-<hash>::<piece> with a new hash
# at each run, as a rebuild of a library gives its binary another hash; it is selected by its
# name without the hash, as tools/run_tests.sh --only selects one.
for n in "$@"; do [ "$n" = BUILD ] || names+=("${n#toylib::}"); done
echo "$(git rev-parse --short=9 HEAD) $kind ${*:-all}" >>"$MW_STATE/runs.log"
# MW_LEAK: each run leaves a process behind, as a test binary or a fresh child can.
if [ -n "${MW_LEAK:-}" ]; then
  sleep 300 </dev/null >/dev/null 2>&1 &
  echo $! >>"$MW_STATE/leaked"
fi
# MW_LIST=<line>: the first run of named pieces (a flake check or a bisect step, both after the
# watcher read the known list) appends the line to the known list, as a person, an agent or a
# second watcher lists a failing piece while the watcher bisects it.
if [ -n "${MW_LIST:-}" ] && [ $# -gt 0 ] && [ ! -e "$MW_STATE/listed" ]; then
  : >"$MW_STATE/listed"
  echo "$MW_LIST" >>"$MAIN_WATCH_HOME/main-watch-known.txt"
fi
[ ! -e broken/BUILD ] || { echo "BUILD FAILED"; exit 1; }
# MW_RUNKILL: the runner itself dies of SIGSEGV on its first run of every test, reporting nothing.
if [ -n "${MW_RUNKILL:-}" ] && [ $# -eq 0 ] && [ "$kind" = test ] && [ ! -e "$MW_STATE/runkilled" ]; then
  : >"$MW_STATE/runkilled"
  kill -SEGV $$
fi
# MW_DIRTY: a run of named pieces at a commit other than the head changes the tracked file work,
# which every landing changes, so the watcher's next checkout of another landing fails.
if [ -n "${MW_DIRTY:-}" ] && [ $# -gt 0 ] && [ -e work ] && [ "$(git rev-parse HEAD)" != "$(git rev-parse origin/main)" ]; then
  echo dirt >>work
fi
[ $# -eq 0 ] || [ ${#names[@]} -gt 0 ] || exit 0
if [ ${#names[@]} -eq 0 ]; then
  if [ "$kind" = test ]; then mapfile -t names <tests; else mapfile -t names <benches; fi
fi
rc=0
for n in "${names[@]}"; do
  echo "$kind $n" >>"$MW_STATE/ran"
  r=0
  [ ! -e "broken/$n" ] || r=1
  # A piece also fails while the spec it reads has breaks/<piece>, as a piece that reads DESIGN.md
  # fails at a spec change whose zed-impl half has not landed.
  [ ! -e "$ZED_SPEC_DIR/breaks/$n" ] || r=1
  # A piece also fails at every commit while $MW_STATE/env-broken/<piece> exists: the machine
  # changed, so it fails at a commit that passed when it was checked.
  [ ! -e "$MW_STATE/env-broken/$n" ] || r=1
  # MW_SEGV=<piece>: that piece, while broken, is killed by SIGSEGV; its rc is 139, as
  # run_tests.sh reports a piece ended by a signal (128 + the signal).
  if [ "$r" = 1 ] && [ "$n" = "${MW_SEGV:-}" ]; then
    bash -c 'kill -SEGV $$' 2>/dev/null
    r=$?
  fi
  # MW_FIRST3=<piece>: that piece fails on its first three runs only (the full run and the two
  # runs of the check for a flake).
  if [ "$n" = "${MW_FIRST3:-}" ]; then
    echo x >>"$MW_STATE/first3"
    [ "$(wc -l <"$MW_STATE/first3")" -gt 3 ] || r=1
  fi
  if [ "$n" = t_flaky ] && [ ! -e "$MW_STATE/flaky-ran" ]; then : >"$MW_STATE/flaky-ran"; r=1; fi
  echo "${MW_HASH:+toylib-$(od -An -N8 -tx1 /dev/urandom | tr -d ' \n')::}$n rc=$r 1ms load=0 limit=20s wait=0ms"
  [ "$r" = 0 ] || rc=1
done
exit "$rc"
EOF
  # The fixer, as a fixing agent: fixes the pieces its brief names, lands, records the landing.
  # MW_FIX=none lands a change that fixes nothing; MW_FIX=fail ends without landing;
  # MW_FIX_BREAK=<piece> breaks that piece in the first fix.
  cat >"$t/bin/fix" <<'EOF'
#!/bin/bash
brief=$1 dir=$2
echo "fixer in $(pwd -P) for $dir" >>"$MW_STATE/fixer.log"
[ "${MW_FIX:-}" != fail ] || exit 1
for p in $(sed -n 's/^Failing pieces: //p' "$brief"); do
  [ "${MW_FIX:-}" = none ] || git rm -q --ignore-unmatch "broken/${p##*:}"
done
if [ -n "${MW_FIX_BREAK:-}" ] && [ ! -e "$MW_STATE/broke" ]; then
  : >"$MW_STATE/broke"
  echo x >"broken/$MW_FIX_BREAK"
  git add -A
fi
echo "fix" >>fixes
git add -A
git commit -q -m "fix: $(sed -n 's/^Failing pieces: //p' "$brief")"
git push -q origin HEAD:main || exit 1
echo "$(git rev-parse HEAD) $(date -u +%FT%TZ) $dir $(git branch --show-current)" >>"$MAIN_WATCH_HOME/landings.log"
EOF
  # zrun for the case zrun: takes tools/run_tests.sh's arguments as main_watch.sh's run_pieces
  # writes them, refuses an --only as run_tests.sh does (exit 2: the text before the first :: of
  # each top-level alternative, split by run_tests.sh's own alternatives(), must be an extended
  # regular expression by itself), and runs the stub runner with each piece named toy::<piece>,
  # as a real piece is named <group>::<path>.
  cat >"$t/bin/zrun" <<'EOF'
#!/bin/bash
shift
logs= kind=test only= list= except=
while [ $# -gt 1 ]; do
  case $1 in
    --logs) logs=$2 && shift ;;
    --bench) kind=bench ;;
    --only) only=$2 && shift ;;
    --except) except=${except:+$except|}$2 && shift ;;
    --list) list=1 ;;
  esac
  shift
done
eval "$(awk '/^alternatives\(\) \{/,/^}/' "$MW_ROOT/tools/run_tests.sh")"
names=()
if [ -n "$only" ]; then
  while read -r a; do
    { [[ x =~ ${a%%::*} ]]; } 2>/dev/null
    if [ $? = 2 ]; then
      echo "--only: cannot tell which test binaries '$a' names"
      echo "$only" >>"$MW_STATE/refused"
      exit 2
    fi
    a=${a#^} a=${a%\$} a=${a//\\/}
    names+=("${a#toy::}")
  done < <(alternatives "$only")
elif [ -n "$list" ]; then
  names=(BUILD)
fi
# --except, as run_tests.sh's: the pieces it matches are not run.
if [ -n "$except" ]; then
  if [ ${#names[@]} -eq 0 ]; then
    if [ "$kind" = test ]; then mapfile -t names <tests; else mapfile -t names <benches; fi
  fi
  kept=()
  for n in "${names[@]}"; do [[ toy::$n =~ $except ]] || kept+=("$n"); done
  names=("${kept[@]}")
  [ ${#names[@]} -gt 0 ] || { echo "NO PIECE TO RUN"; exit 1; }
fi
"$MW_RUN" "$logs" "$kind" "${names[@]}" | sed -E 's/^(t_|b_)/toy::\1/'
exit "${PIPESTATUS[0]}"
EOF
  chmod +x "$t/bin/zrun"
  printf '#!/bin/bash\ntrue\n' >"$t/bin/prepare"
  printf '#!/bin/bash\ngit -C "$1" worktree remove --force "$(realpath -e "$1")"\n' >"$t/bin/remove"
  # The publisher of a checked worktree's build (build-publish.sh): records the worktree's commit.
  printf '#!/bin/bash\ngit -C "$1" rev-parse HEAD >>"$MW_STATE/published"\n' >"$t/bin/publish"
  chmod +x "$t/bin/run" "$t/bin/fix" "$t/bin/prepare" "$t/bin/remove" "$t/bin/publish"
  # The template holds every placeholder; the fixer reads the "Failing pieces:" line.
  printf '%s\n' '# {{ROW}} attempt {{ATTEMPT}}' 'Commit {{COMMIT}} of {{LANDING}}.' \
    'Failing pieces: {{PIECES}}' '{{EARLIER}}' 'Base {{BASE}}, worktree {{WORKTREE}}, branch {{BRANCH}}.' \
    'Message:' '{{MESSAGE}}' 'Files:' '{{STAT}}' 'Diff: {{DIFF}}' 'Output:' '{{OUTPUT}}' 'Bisect:' '{{BISECT}}' \
    >"$t/template"
  export MAIN_WATCH_HOME=$t/home MAIN_WATCH_REPO=$t/repo MAIN_WATCH_TREES=$t/trees \
    MAIN_WATCH_PREPARE=$t/bin/prepare MAIN_WATCH_REMOVE=$t/bin/remove MAIN_WATCH_RUN=$t/bin/run \
    MAIN_WATCH_PUBLISH=$t/bin/publish \
    MAIN_WATCH_FIXER=$t/bin/fix MAIN_WATCH_TEMPLATE=$t/template MAIN_WATCH_POLL=0 MAIN_WATCH_POLLS=2 \
    MAIN_WATCH_FARM=local MW_STATE=$t/state
  unset MW_FIX MW_FIX_BREAK MAIN_WATCH_ZRUN MW_LEAK MAIN_WATCH_QUEUE MAIN_WATCH_MIN MW_SEGV MW_FIRST3 MW_DIRTY MW_RUNKILL MW_LIST MW_HASH
}

# land <n> [<commits>] [<i>:<piece>]: landing n, pushed from the dev clone, of <commits> commits
# (1); commit i breaks the piece.
land() {
  local n=$1 k=${2:-1} brk=${3:-} i msg
  for i in $(seq 1 "$k"); do
    echo "$n.$i" >>"$t/dev/work"
    msg="landing $n commit $i"
    if [ -n "$brk" ] && [ "${brk%%:*}" = "$i" ]; then
      echo x >"$t/dev/broken/${brk#*:}"
      msg="TEST-row-$n: breaks ${brk#*:} (a & b)"
    fi
    git -C "$t/dev" add -A
    git -C "$t/dev" commit -q -m "$msg"
  done
  git -C "$t/dev" push -q origin HEAD:main
  echo "$(git -C "$t/dev" rev-parse HEAD) 2026-11-19T00:00:00Z $t/trees/agent$n wt/agent$n" >>"$t/home/landings.log"
}
# spec_land <i> <message> [<piece>]: spec commit i, pushed from the author's checkout, dated
# 2030-01-0<i> (after any time the watcher writes); it breaks the piece.
spec_land() {
  echo "$2" >>"$t/speclive/DESIGN.md"
  [ -z "${3:-}" ] || echo x >"$t/speclive/breaks/$3"
  git -C "$t/speclive" add -A
  GIT_COMMITTER_DATE="2030-01-0${1}T00:00:00Z" gitc -C "$t/speclive" commit -q -m "$2"
  git -C "$t/speclive" push -q origin HEAD:main
}
# The commit that added broken/$1.
breaker() { git -C "$t/dev" log --diff-filter=A --format=%H -1 -- "broken/$1"; }
# Lands 20 landings: landing 5 breaks t_alpha; landing 12 has 3 commits, the second breaks b_beta.
twenty() {
  local n
  for n in $(seq 1 20); do
    case $n in
      5) land 5 1 1:t_alpha ;;
      12) land 12 3 2:b_beta ;;
      *) land "$n" ;;
    esac
  done
}
# Runs the watcher from c0; its output in $t/out, its exit code in $rc.
watch() {
  timeout 50 "$watch" --start "$c0" >"$t/out" 2>&1
  rc=$?
}
opened() { awk '$1 == "open" { print $2 }' "$t/home/main-red.log" 2>/dev/null; }
fixedby() { awk '$1 == "fixed" { print $2 " " $6 }' "$t/home/main-red.log" 2>/dev/null; }
head_of() { git -C "$t/repo" rev-parse origin/main; }
# The line numbers in the output of the first line matching each pattern, joined; "-" when absent.
order() {
  local p
  for p in "$@"; do
    command grep -a -n -m 1 -E "$p" "$t/out" | cut -d: -f1 | command grep -a . || echo -
  done | paste -sd' '
}
checked() { cut -d' ' -f1 "$t/home/main-watch.checked"; }

run_case() {
  t=$top/$1
  mkdir -p "$t"
  case $1 in
  two)
    # Two culprits found and fixed in turn; the flake is recorded, not bisected; the watcher polls
    # again only after both are fixed and everything passes.
    setup
    twenty
    local a b
    a=$(breaker t_alpha)
    b=$(breaker b_beta)
    watch
    check "two: exit 0" 0 "$rc"
    check "two: the culprits, in order: t_alpha's commit, then b_beta's (inside landing 12)" "$a
$b" "$(opened)"
    check "two: b_beta's culprit is the second of landing 12's three commits" "landing 12 commit 1" \
      "$(git -C "$t/repo" log -1 --format=%s "$b^")"
    check "two: both fixed, each by a fix commit" "$a fix: test:t_alpha
$b fix: bench:b_beta" "$(fixedby | while read -r c f; do echo "$c $(git -C "$t/repo" log -1 --format=%s "$f")"; done)"
    check "two: the flake is recorded" 1 "$(command grep -a -c 'test:t_flaky' "$t/home/main-watch-flakes.log")"
    check "two: the flake is not bisected" 0 "$(command grep -a -c t_flaky "$t/home/main-red.log")"
    local o
    o=($(order '^main-watch: poll 1:' 'fixed by' 'FAIL-main-.*: fixed by' "checked $(git -C "$t/repo" rev-parse --short=9 "$(head_of)")" '^main-watch: poll 2:'))
    check "two: poll 1, both fixes, checked, then poll 2" yes \
      "$([ "${#o[@]}" = 5 ] && [ "${o[0]}" -lt "${o[1]}" ] && [ "$(command grep -a -c ': fixed by' "$t/out")" = 2 ] &&
        [ "$(command grep -a -n ': fixed by' "$t/out" | tail -1 | cut -d: -f1)" -lt "${o[3]}" ] && [ "${o[3]}" -lt "${o[4]}" ] && echo yes)"
    check "two: the head after the fixes is checked" "$(head_of)" "$(checked)"
    check "two: only the checked head's build is published" "$(head_of)" "$(cat "$t/state/published" 2>/dev/null)"
    check "two: two fix landings" 22 "$(wc -l <"$t/home/landings.log")"
    check "two: the ledger rows end done" "FAIL-main-${a:0:9}
FAIL-main-${b:0:9}" "$(command grep -a '"state":"done"' "$t/home/ledger.jsonl" | sed 's/.*"id":"\([^"]*\)".*/\1/')"
    check "two: the running log names the row and agent of the culprit" 1 \
      "$(command grep -a -c "FAIL-main-${a:0:9}: first bad commit .*branch wt/agent5 from .*/agent5, rows TEST-row-5" "$t/home/running-log.md")"
    check "two: the second bisect narrowed inside landing 12 with git bisect" 1 \
      "$(cat "$t/home/main-watch-runs"/*/bisect-*.log | command grep -a -c 'first bad commit inside the landing')"
    check "two: an & in the message reaches the brief" 1 \
      "$(cat "$t/home/main-watch-runs"/*/brief-FAIL-main-"${a:0:9}"-1.md | command grep -a -c -F '(a & b)')"
    check "two: the watcher's and the fixers' worktrees are removed" 1 "$(git -C "$t/repo" worktree list | wc -l)"
    check "two: no bisect is left open" "" "$(git -C "$t/repo" for-each-ref refs/bisect)"
    ;;
  farm)
    # The real run_pieces with a stub tools/farm_run.sh (MAIN_WATCH_FARM; FARM-main-watch-remote):
    # every run goes through it as owner main-watch, with the pinned spec; nothing runs on this
    # machine (the zrun given is never called); a run of every piece takes 4 VMs and a run of a
    # few named pieces 1; the names reach it as a terms file, one a line; the culprits are found as
    # with zrun.
    setup
    unset MAIN_WATCH_RUN
    cat >"$t/bin/farm" <<'EOF'
#!/bin/bash
owner= vms= out= jobs= spec= terms= kind=test list= full=
while [ $# -gt 0 ]; do
  case $1 in
    --owner) owner=$2 && shift ;; --vms) vms=$2 && shift ;; --out) out=$2 && shift ;;
    --jobs) jobs=$2 && shift ;; --spec) spec=$2 && shift ;;
    --terms) terms=$2 && shift ;; --except) shift ;;
    --bench) kind=bench ;; --full) full=1 ;; --list) list=1 ;;
    *) echo "farm stub: unknown argument $1"; exit 2 ;;
  esac
  shift
done
names=()
[ -z "$terms" ] || mapfile -t names <"$terms"
[ -z "$list" ] || names=(BUILD)
echo "$owner $vms $kind ${#names[@]} $([ -n "$jobs" ] && [ -d "$spec" ] && [ "$spec" = "$ZED_SPEC_DIR" ] && [ ! -e "$out" ] && echo ok)" >>"$MW_STATE/farm.log"
"$MW_RUN" "$out" "$kind" "${names[@]}"
EOF
    chmod +x "$t/bin/farm"
    printf '#!/bin/bash\necho "$*" >>"%s"\nexit 0\n' "$t/state/zrun-called" >"$t/bin/zrun-unused"
    chmod +x "$t/bin/zrun-unused"
    export MAIN_WATCH_FARM=$t/bin/farm MAIN_WATCH_ZRUN=$t/bin/zrun-unused MW_RUN=$t/bin/run
    twenty
    local a b
    a=$(breaker t_alpha)
    b=$(breaker b_beta)
    watch
    check "farm: exit 0" 0 "$rc"
    check "farm: the culprits, in order: t_alpha's commit, then b_beta's" "$a
$b" "$(opened)"
    check "farm: every run went through it as main-watch, with jobs and the pinned spec" "" \
      "$(awk '$1 != "main-watch" || $5 != "ok"' "$t/state/farm.log")"
    check "farm: nothing ran here under zrun" "" "$(cat "$t/state/zrun-called" 2>/dev/null)"
    check "farm: the runs of every piece took 4 VMs" "" "$(awk '$4 == 0 && $2 != 4' "$t/state/farm.log")"
    check "farm: the runs of 1 to 8 named pieces took 1 VM" "" "$(awk '$4 >= 1 && $4 <= 8 && $2 != 1' "$t/state/farm.log")"
    check "farm: runs of every piece of both kinds and of named pieces were made" yes \
      "$(awk '$4 == 0 && $3 == "test" { t = 1 } $4 == 0 && $3 == "bench" { b = 1 } $4 > 0 { n = 1 } END { if (t && b && n) print "yes" }' "$t/state/farm.log")"
    ;;
  zrun)
    # The real run_pieces (MAIN_WATCH_ZRUN, not MAIN_WATCH_RUN), with pieces named
    # <group>::<path>: every --only it writes must be one run_tests.sh accepts, or each failure
    # reads as a flake (TOOL-main-watch-start-green, 2026-11-20: run_pieces wrote
    # `^(a::x|b::y)$`, which run_tests.sh refuses, so every failure was logged as a flake).
    setup
    unset MAIN_WATCH_RUN
    export MAIN_WATCH_ZRUN=$t/bin/zrun MW_RUN=$t/bin/run MW_ROOT=$root
    twenty
    local a b
    a=$(breaker t_alpha)
    b=$(breaker b_beta)
    watch
    check "zrun: exit 0" 0 "$rc"
    check "zrun: run_tests.sh refused no --only" "" "$(cat "$t/state/refused" 2>/dev/null)"
    check "zrun: the culprits, in order: t_alpha's commit, then b_beta's" "$a
$b" "$(opened)"
    check "zrun: the flake alone is recorded as a flake" "test:toy::t_flaky" \
      "$(cut -d' ' -f3 "$t/home/main-watch-flakes.log" 2>/dev/null | sort -u)"
    ;;
  fixbreak)
    # The first fix breaks t_gamma; the next round finds the fix commit as the culprit and fixes it.
    setup
    twenty
    export MW_FIX_BREAK=t_gamma
    watch
    check "fixbreak: exit 0" 0 "$rc"
    check "fixbreak: three culprits, the first two as before" "$(breaker t_alpha)
$(breaker b_beta)" "$(opened | sed -n 1,2p)"
    check "fixbreak: the third is the commit that broke t_gamma" \
      "$(git -C "$t/repo" log --diff-filter=A --format=%H -1 origin/main -- broken/t_gamma)" "$(opened | sed -n 3p)"
    check "fixbreak: t_gamma's culprit is the fix of t_alpha" "fix: test:t_alpha" \
      "$(git -C "$t/repo" log -1 --format=%s "$(opened | sed -n 3p)")"
    check "fixbreak: the head after the third fix is checked" "$(head_of)" "$(checked)"
    check "fixbreak: poll 2 after the third fix" yes \
      "$([ "$(command grep -a -n ': fixed by' "$t/out" | sed -n 3p | cut -d: -f1)" -lt "$(order '^main-watch: poll 2:')" ] && echo yes)"
    ;;
  failfix)
    # A fixer that ends without landing: the case is recorded, its pieces join the known list
    # with its row, and the watcher goes on (author, 2026-11-21: "main_watch should not crash if
    # a test fails or crashes"); the head is checked with them as known failures.
    setup
    twenty
    export MW_FIX=fail
    watch
    local a b
    a=$(breaker t_alpha)
    b=$(breaker b_beta)
    check "failfix: exit 0" 0 "$rc"
    check "failfix: a stuck line for t_alpha's culprit" 1 "$(command grep -a -c "^stuck $a .* main-watch " "$t/home/main-red.log")"
    check "failfix: the stuck entry" 1 "$(command grep -a -c "^## .* main-watch stuck: FAIL-main-${a:0:9}: the fixing agent of attempt 1 ended without landing" "$t/home/main-watch-stuck.md")"
    check "failfix: the entry says what it holds up" 1 "$(command grep -a -c "^Holds up: FAIL-main-${a:0:9}, whose pieces test:t_alpha main-watch now reports as known failures" "$t/home/main-watch-stuck.md")"
    check "failfix: both culprits' pieces on the known list with their rows" "test:t_alpha FAIL-main-${a:0:9}
bench:b_beta FAIL-main-${b:0:9}" "$(cat "$t/home/main-watch-known.txt")"
    check "failfix: one fix attempt for each culprit" 2 "$(wc -l <"$t/state/fixer.log")"
    check "failfix: a second poll" yes "$([ "$(order '^main-watch: poll 2:')" != - ] && echo yes)"
    check "failfix: the head is checked" "$(head_of)" "$(checked)"
    check "failfix: the checked head's build is published" "$(head_of)" "$(cat "$t/state/published" 2>/dev/null)"
    ;;
  nofix)
    # Fixers that land but fix nothing: three attempts for each culprit, recorded, then the
    # watcher goes on with the pieces as known failures.
    setup
    twenty
    export MW_FIX=none
    watch
    local a
    a=$(breaker t_alpha)
    check "nofix: exit 0" 0 "$rc"
    check "nofix: three attempts for each of the two culprits" 6 "$(wc -l <"$t/state/fixer.log")"
    check "nofix: stuck after 3 attempts" 1 "$(command grep -a -c "main-watch stuck: FAIL-main-${a:0:9}: test:t_alpha still fail after 3 fix attempts" "$t/home/main-watch-stuck.md")"
    check "nofix: t_alpha on the known list with its row" 1 "$(command grep -a -c -x "test:t_alpha FAIL-main-${a:0:9}" "$t/home/main-watch-known.txt")"
    check "nofix: a second poll" yes "$([ "$(order '^main-watch: poll 2:')" != - ] && echo yes)"
    check "nofix: the head is checked" "$(head_of)" "$(checked)"
    ;;
  segv)
    # A piece killed by SIGSEGV is a failing piece (rc=139), bisected and fixed like any other.
    setup
    export MW_SEGV=t_gamma
    for n in $(seq 1 15); do
      if [ "$n" = 7 ]; then land 7 1 1:t_gamma; else land "$n"; fi
    done
    watch
    check "segv: exit 0" 0 "$rc"
    check "segv: the piece was killed by SIGSEGV" yes "$(cat "$t/home/main-watch-runs"/*/*-test.out | command grep -a -q '^t_gamma rc=139 ' && echo yes)"
    check "segv: the culprit is the commit that broke it" "$(breaker t_gamma)" "$(opened)"
    check "segv: fixed" 1 "$(fixedby | wc -l)"
    check "segv: the head is checked" "$(head_of)" "$(checked)"
    ;;
  runkill)
    # The runner itself dies of SIGSEGV in the run of every test, reporting nothing: the head is
    # not checked from that run (its unreported pieces would read as passing); the case is
    # recorded and the next poll runs everything again and checks the head.
    setup
    export MW_RUNKILL=1
    for n in $(seq 1 15); do land "$n"; done
    watch
    check "runkill: exit 0" 0 "$rc"
    check "runkill: the stuck entry" 1 "$(command grep -a -c "main-watch stuck: the run of every test (exit 139) at $(git -C "$t/repo" rev-parse --short=9 "$(head_of)") ended by a signal" "$t/home/main-watch-stuck.md")"
    check "runkill: every test ran twice, once per poll" 2 "$(command grep -a -c ' test all$' "$t/state/runs.log")"
    check "runkill: the head is checked" "$(head_of)" "$(checked)"
    ;;
  nottwice)
    # A piece that fails its first three runs at the head, then passes everywhere: the bisect
    # names the head, at which it no longer fails twice; recorded, put on the known list, and the
    # watcher goes on.
    setup
    export MW_FIRST3=t_gamma
    for n in $(seq 1 15); do land "$n"; done
    watch
    local h
    h=$(git -C "$t/repo" rev-parse --short=9 "$(head_of)")
    check "nottwice: exit 0" 0 "$rc"
    check "nottwice: the stuck entry" 1 "$(command grep -a -c "main-watch stuck: the bisect named $h but none of test:t_gamma fails there twice" "$t/home/main-watch-stuck.md")"
    check "nottwice: on the known list with the row of the named commit" "test:t_gamma FAIL-main-$h" "$(cat "$t/home/main-watch-known.txt")"
    check "nottwice: no culprit" "" "$(opened)"
    check "nottwice: the head is checked" "$(head_of)" "$(checked)"
    ;;
  nobisect)
    # The bisect's checkout fails (the run left the worktree changed), so the bisect names no
    # commit: recorded, put on the known list, and the head is checked (queue mode).
    setup
    export MW_DIRTY=1 MAIN_WATCH_QUEUE=$t/home/spawn-queue.txt
    for n in $(seq 1 15); do
      if [ "$n" = 8 ]; then land 8 1 1:t_gamma; else land "$n"; fi
    done
    watch
    local h
    h=$(git -C "$t/repo" rev-parse --short=9 "$(head_of)")
    check "nobisect: exit 0" 0 "$rc"
    check "nobisect: the stuck entry" 1 "$(command grep -a -c "main-watch stuck: the bisect of test:t_gamma over ${c0:0:9}..$h named no commit" "$t/home/main-watch-stuck.md")"
    check "nobisect: on the known list with the head's row" "test:t_gamma FAIL-main-$h" "$(cat "$t/home/main-watch-known.txt")"
    check "nobisect: the head is checked" "$(head_of)" "$(checked)"
    check "nobisect: nothing is published from the changed worktree" "" "$(tail -1 "$t/state/published" 2>/dev/null)"
    ;;
  setuperr)
    # Setup errors are the only exits, with 2: no checked commit, and a worktree that cannot be
    # made. Neither is a stuck case.
    setup
    for n in $(seq 1 15); do land "$n"; done
    timeout 50 "$watch" >"$t/out" 2>&1
    check "setuperr: no checked commit: exit 2" 2 "$?"
    export MAIN_WATCH_PREPARE=false
    watch
    check "setuperr: a worktree that cannot be made: exit 2" 2 "$rc"
    check "setuperr: no stuck entry" no "$([ -e "$t/home/main-watch-stuck.md" ] && echo yes || echo no)"
    ;;
  clean)
    # Negative control: nothing broken, so no culprit, and the head is checked.
    setup
    for n in $(seq 1 15); do land "$n"; done
    watch
    check "clean: exit 0" 0 "$rc"
    check "clean: no culprit" "" "$(opened)"
    check "clean: no fixer ran" 0 "$(cat "$t/state/fixer.log" 2>/dev/null | wc -l)"
    check "clean: the head is checked" "$(head_of)" "$(checked)"
    check "clean: the checked head's build is published" "$(head_of)" "$(cat "$t/state/published" 2>/dev/null)"
    check "clean: the flake is recorded" 1 "$(command grep -a -c 'test:t_flaky' "$t/home/main-watch-flakes.log")"
    ;;
  few)
    # Fewer than 15 landings: nothing runs.
    setup
    for n in $(seq 1 14); do land "$n"; done
    watch
    check "few: exit 0" 0 "$rc"
    check "few: no piece ran" 0 "$(cat "$t/state/runs.log" 2>/dev/null | wc -l)"
    check "few: two polls" "14 landings since" "$(command grep -a -m 1 -o '14 landings since' "$t/out")"
    check "few: the checked commit is unchanged" "$c0" "$(checked)"
    ;;
  old)
    # A failure that exists at the last checked commit is not bisected: it is recorded as
    # FAIL-main-<C0>, put on the known list, and the head is checked with it as known.
    setup t_delta
    for n in $(seq 1 15); do land "$n"; done
    watch
    check "old: exit 0" 0 "$rc"
    check "old: no culprit" "" "$(opened)"
    check "old: the stuck entry names the old failure" 1 "$(command grep -a -c "main-watch stuck: test:t_delta fail at the last checked commit" "$t/home/main-watch-stuck.md")"
    check "old: on the known list as FAIL-main-<C0>" "test:t_delta FAIL-main-${c0:0:9}" "$(cat "$t/home/main-watch-known.txt")"
    check "old: no fixer ran" 0 "$(cat "$t/state/fixer.log" 2>/dev/null | wc -l)"
    check "old: the head is checked" "$(head_of)" "$(checked)"
    check "old: the checked head's build is published, not C0's" "$(head_of)" "$(tail -1 "$t/state/published" 2>/dev/null)"
    ;;
  oldqueue)
    # As old, in queue mode: a QUEUE line for FAIL-main-<C0> and a known line, no stuck entry.
    setup t_delta
    export MAIN_WATCH_QUEUE=$t/home/spawn-queue.txt
    for n in $(seq 1 15); do land "$n"; done
    watch
    check "oldqueue: exit 0" 0 "$rc"
    check "oldqueue: the QUEUE line" 1 "$(command grep -a -c "^QUEUE FAIL-main-${c0:0:9} (filed by main-watch .*: test:t_delta fail at the last checked commit" "$t/home/spawn-queue.txt")"
    check "oldqueue: on the known list as FAIL-main-<C0>" "test:t_delta FAIL-main-${c0:0:9}" "$(cat "$t/home/main-watch-known.txt")"
    check "oldqueue: the running log names it" 1 "$(command grep -a -c "FAIL-main-${c0:0:9}: test:t_delta fail at the last checked commit" "$t/home/running-log.md")"
    check "oldqueue: no stuck entry" no "$([ -e "$t/home/main-watch-stuck.md" ] && echo yes || echo no)"
    check "oldqueue: the head is checked" "$(head_of)" "$(checked)"
    check "oldqueue: the checked head's build is published, not C0's" "$(head_of)" "$(tail -1 "$t/state/published" 2>/dev/null)"
    ;;
  spec | specold)
    # A spec commit breaks t_gamma at every zed-impl commit (its zed-impl half has not landed):
    # filed under the row the spec commit names, not as FAIL-main-<C0>, and not bisected over
    # zed-impl (FAIL-main-54b8e6459, 2026-11-21: the watcher read the author's spec checkout, so
    # l01_21_test_runner failed at C0 too and was filed as FAIL-main-54b8e6459). The author's
    # checkout also holds an uncommitted edit that breaks t_alpha, which the watcher must not
    # read. spec: queue mode, C0 recorded by --start, with its spec commit; specold: no queue (a
    # stuck entry), and a checked line written before the spec field existed, `<commit> <time>`,
    # so S0 is the spec at that time.
    setup
    local q=$t/home/spawn-queue.txt s0 s
    [ "$1" != spec ] || export MAIN_WATCH_QUEUE=$q
    s0=$(git -C "$t/spec.git" rev-parse main)
    if [ "$1" = spec ]; then
      for n in 1 2 3; do land "$n"; done
      MAIN_WATCH_POLLS=1 timeout 50 "$watch" --start "$c0" >"$t/out0" 2>&1
      check "spec: the start exits 0" 0 "$?"
      check "spec: the start records C0 with its spec commit" "$c0 $s0" "$(cut -d' ' -f1,3 "$t/home/main-watch.checked")"
    else
      echo "$c0 $(date -u +%FT%TZ)" >"$t/home/main-watch.checked"
      for n in 1 2 3; do land "$n"; done
    fi
    spec_land 1 "spec one (SPEC-row-one)"
    spec_land 2 "DESIGN: a new row (SPEC-row-gamma)" t_gamma
    s=$(git -C "$t/spec.git" rev-parse main)
    spec_land 3 "spec three (SPEC-row-three)"
    echo x >"$t/speclive/breaks/t_alpha"
    for n in $(seq 4 18); do land "$n"; done
    MAIN_WATCH_POLLS=1 timeout 50 "$watch" >"$t/out" 2>&1
    check "$1: exit 0" 0 "$?"
    if [ "$1" = spec ]; then
      check "spec: one QUEUE line, for the row the breaking spec commit names" "QUEUE SPEC-row-gamma ${s:0:9}" \
        "$(sed -E 's/^(QUEUE [^ ]+) .*: spec commit ([0-9a-f]{9}) .*/\1 \2/' "$q" 2>/dev/null)"
    else
      check "specold: one stuck entry, for the breaking spec commit" 1 \
        "$(command grep -a -c "^## .* main-watch stuck: spec commit ${s:0:9} breaks test:t_gamma\$" "$t/home/main-watch-stuck.md")"
      check "specold: it holds up the row the spec commit names" 1 \
        "$(command grep -a -c '^Holds up: SPEC-row-gamma, whose pieces test:t_gamma ' "$t/home/main-watch-stuck.md")"
    fi
    check "$1: on the known list with that row" "test:t_gamma SPEC-row-gamma" "$(cat "$t/home/main-watch-known.txt" 2>/dev/null)"
    check "$1: nothing filed as FAIL-main" 0 \
      "$(cat "$q" "$t/home/main-watch-known.txt" "$t/home/main-red.log" "$t/home/main-watch-stuck.md" 2>/dev/null | command grep -a -c FAIL-main)"
    check "$1: no zed-impl culprit" "" "$(opened)"
    check "$1: t_alpha, broken only in the author's working tree, passed at the head" 1 \
      "$(cat "$t/home/main-watch-runs"/*/*-test.out | command grep -a -c '^t_alpha rc=0 ')"
    check "$1: the head is checked, with the spec's head" "$(head_of) $(git -C "$t/spec.git" rev-parse main)" \
      "$(cut -d' ' -f1,3 "$t/home/main-watch.checked")"
    ;;
  known)
    # As old, but main-watch-known.txt gives the failure's owning row: it still runs and is
    # reported with its row, but is not bisected, fixed or confirmed at C0, and the head is
    # checked and published.
    setup t_delta
    echo "test:t_delta TEST-row-known" >"$t/home/main-watch-known.txt"
    for n in $(seq 1 15); do land "$n"; done
    watch
    check "known: exit 0" 0 "$rc"
    check "known: no culprit" "" "$(opened)"
    check "known: no fixer ran" 0 "$(cat "$t/state/fixer.log" 2>/dev/null | wc -l)"
    check "known: the head is checked" "$(head_of)" "$(checked)"
    check "known: the checked head's build is published" "$(head_of)" "$(cat "$t/state/published" 2>/dev/null)"
    check "known: the failure still ran at the head" 1 \
      "$(command grep -a -c "^$(git -C "$t/repo" rev-parse --short=9 "$(head_of)") test all" "$t/state/runs.log")"
    check "known: the running log names the failure and its row" 1 \
      "$(command grep -a -c 'known failures at .*test:t_delta (TEST-row-known)' "$t/home/running-log.md")"
    ;;
  fixedby | fixedbyfail | fixedbyrace)
    # A known line with `fixed-by F` (MAINWATCH-known-fixed-by). Phase 1, the case of 46c1d2b71
    # (2026-11-21): F is on a side branch only, so the line is in force at the head and the
    # failure is known there: no row is filed and the line is kept. Phase 2: F lands on main.
    # fixedby: F fixes the piece, which passes, and the watcher takes the line out. fixedbyfail: F
    # does not; the piece goes back to the line's row and the line loses its fixed-by.
    # fixedbyrace: as fixedby, but phase 2 runs a copy of the watcher in which a line is appended
    # to the list just before known_edit's rename, as another writer's append may land there
    # (TOOLS-push-tests-cleanup); the line must be on the list afterwards.
    setup t_delta
    local q=$t/home/spawn-queue.txt k=$t/home/main-watch-known.txt fx fb w2=$watch
    local race="test:t_gamma TEST-row-race"
    export MAIN_WATCH_QUEUE=$q
    git clone -q "$t/remote.git" "$t/fx"
    if [ "$1" != fixedbyfail ]; then git -C "$t/fx" rm -q broken/t_delta; else echo x >"$t/fx/other"; fi
    git -C "$t/fx" add -A
    gitc -C "$t/fx" commit -q -m "TEST-row-known: the fix"
    git -C "$t/fx" push -q origin HEAD:side
    fx=$(git -C "$t/fx" rev-parse HEAD)
    fb="test:t_delta TEST-row-known fixed-by ${fx:0:9}"
    printf '%s\n' "# header" "$fb" >"$k"
    for n in $(seq 1 15); do land "$n"; done
    watch
    check "$1: phase 1 exits 0" 0 "$rc"
    check "$1: phase 1 queues nothing" 0 "$(cat "$q" 2>/dev/null | wc -l)"
    check "$1: phase 1 keeps the line" "# header
$fb" "$(cat "$k")"
    check "$1: phase 1 checks the head, with the failure known" "$(head_of) test:t_delta=TEST-row-known" \
      "$(cut -d' ' -f1,4 "$t/home/main-watch.checked")"
    check "$1: phase 1 reports it with its row" 1 \
      "$(command grep -a -c 'known failures at .*test:t_delta (TEST-row-known)' "$t/home/running-log.md")"
    git -C "$t/dev" fetch -q origin side
    gitc -C "$t/dev" merge -q --no-edit origin/side
    land 16
    if [ "$1" = fixedbyrace ]; then
      w2=$t/race.sh
      sed "/^ *mv -T \"\\\$known_file\\.\\\$\\\$\" \"\\\$known_file\"/i\\        echo \"$race\" >>\"\$known_file\"" "$watch" >"$w2"
      chmod +x "$w2"
      check "fixedbyrace: the copy adds one line" 1 "$(diff "$watch" "$w2" | command grep -a -c '^>')"
    fi
    MAIN_WATCH_MIN=1 timeout 50 "$w2" >"$t/out2" 2>&1
    check "$1: phase 2 exits 0" 0 "$?"
    if [ "$1" != fixedbyfail ]; then
      local want="# header"
      [ "$1" = fixedby ] || want+=$'\n'$race
      check "$1: phase 2 takes the line out$([ "$1" = fixedby ] || echo ' and keeps the line appended meanwhile')" "$want" "$(cat "$k")"
      check "$1: phase 2 queues nothing" 0 "$(cat "$q" 2>/dev/null | wc -l)"
      check "$1: phase 2 logs it" 1 "$(command grep -a -c 'fixed at .*: test:t_delta pass there' "$t/home/running-log.md")"
      check "$1: phase 2 checks the head, with no known failure" "$(head_of) -" "$(cut -d' ' -f1,4 "$t/home/main-watch.checked")"
    else
      check "fixedbyfail: phase 2 queues one line, to the line's row" 1 \
        "$(command grep -a -c "^QUEUE TEST-row-known (filed by main-watch .*: test:t_delta still fails at $(git -C "$t/repo" rev-parse --short=9 "$(head_of)"), which holds ${fx:0:9}" "$q")"
      check "fixedbyfail: phase 2 queues nothing else" 1 "$(wc -l <"$q")"
      check "fixedbyfail: the line is in force again" "# header
test:t_delta TEST-row-known" "$(cat "$k")"
      check "fixedbyfail: phase 2 checks the head, with the failure known" "$(head_of) test:t_delta=TEST-row-known" \
        "$(cut -d' ' -f1,4 "$t/home/main-watch.checked")"
    fi
    check "$1: nothing filed as FAIL-main" 0 "$(cat "$q" "$k" "$t/home/main-red.log" 2>/dev/null | command grep -a -c FAIL-main)"
    check "$1: no culprit" "" "$(opened)"
    ;;
  hash | hashold)
    # As known, but each piece is a library's unit test, named with its binary's build hash, which
    # changes at each run (MW_HASH; MAINWATCH-lib-piece-hash). hash: the known line names the
    # piece without the hash, toylib::t_delta; hashold: with the hash of an older build. Either
    # way the failure is the known one: no culprit, and the head is checked. Before unhash, the
    # failure was read as toylib-<hash>::t_delta, matched no known line and was bisected.
    setup t_delta
    export MW_HASH=1
    local kl=test:toylib::t_delta
    [ "$1" = hash ] || kl=test:toylib-0123456789abcdef::t_delta
    echo "$kl TEST-row-known" >"$t/home/main-watch-known.txt"
    for n in $(seq 1 15); do land "$n"; done
    watch
    check "$1: exit 0" 0 "$rc"
    check "$1: the pieces were named with a hash" yes \
      "$(command grep -a -q -E '^toylib-[0-9a-f]{16}::t_delta rc=1 ' "$t"/home/main-watch-runs/*/*-test.out 2>/dev/null && echo yes || echo no)"
    check "$1: no culprit" "" "$(opened)"
    check "$1: no fixer ran" 0 "$(cat "$t/state/fixer.log" 2>/dev/null | wc -l)"
    check "$1: the head is checked, with the failure known by its name without the hash" \
      "$(head_of) test:toylib::t_delta=TEST-row-known" "$(cut -d' ' -f1,4 "$t/home/main-watch.checked")"
    check "$1: the running log names the failure and its row" 1 \
      "$(command grep -a -c 'known failures at .*test:toylib::t_delta (TEST-row-known)' "$t/home/running-log.md")"
    check "$1: nothing filed as FAIL-main" 0 "$(cat "$t/home/main-watch-known.txt" "$t/home/main-red.log" 2>/dev/null | command grep -a -c FAIL-main)"
    ;;
  queuedup)
    # A piece listed by hand while the watcher bisects it (TOOLS-push-tests-cleanup): in queue
    # mode fix puts the culprit's pieces on the known list with known_add, so the list holds the
    # piece once; the bare append it used before wrote a second, identical line.
    setup
    local q=$t/home/spawn-queue.txt n
    for n in $(seq 1 15); do
      if [ "$n" = 5 ]; then land 5 1 1:t_alpha; else land "$n"; fi
    done
    export MAIN_WATCH_QUEUE=$q MW_LIST="test:t_alpha TEST-row-5"
    watch
    check "queuedup: exit 0" 0 "$rc"
    check "queuedup: the line was listed during the runs of named pieces" yes "$([ -e "$t/state/listed" ] && echo yes)"
    check "queuedup: one QUEUE line, to TEST-row-5" 1 "$(command grep -a -c '^QUEUE TEST-row-5 ' "$q")"
    check "queuedup: the known list holds the piece once" "test:t_alpha TEST-row-5" "$(cat "$t/home/main-watch-known.txt")"
    check "queuedup: the head is checked" "$(head_of)" "$(checked)"
    ;;
  oldknown | oldknownlog)
    # FAIL-main-af9161e5a (2026-11-21): C0 was checked with t_delta a known failure of
    # TEST-row-known; then its line was taken out before a checked head held a fix, and the next
    # check found t_delta failing at C0 too. It goes back to TEST-row-known, not to FAIL-main-<C0>.
    # t_gamma fails at C0 too (the machine changed): it is filed as FAIL-main-<C0>, with a message
    # that names C0's known failures. oldknown: C0's checked line records them (fourth field);
    # oldknownlog: a line of the older form, so they are read from the running log.
    setup t_delta
    local q=$t/home/spawn-queue.txt k=$t/home/main-watch-known.txt h1
    export MAIN_WATCH_QUEUE=$q
    printf '%s\n' "# header" "test:t_delta TEST-row-known" >"$k"
    for n in $(seq 1 15); do land "$n"; done
    watch
    h1=$(head_of)
    check "$1: phase 1 exits 0" 0 "$rc"
    check "$1: phase 1 checks the head, with the failure known" "$h1 test:t_delta=TEST-row-known" \
      "$(cut -d' ' -f1,4 "$t/home/main-watch.checked")"
    local c3
    c3=$(cut -d' ' -f1-3 "$t/home/main-watch.checked")
    [ "$1" = oldknown ] || echo "$c3" >"$t/home/main-watch.checked"
    echo "# header" >"$k"
    mkdir -p "$t/state/env-broken"
    : >"$t/state/env-broken/t_gamma"
    land 16
    MAIN_WATCH_MIN=1 timeout 50 "$watch" >"$t/out2" 2>&1
    check "$1: phase 2 exits 0" 0 "$?"
    check "$1: t_delta goes back to its row" 1 \
      "$(command grep -a -c "^QUEUE TEST-row-known (filed by main-watch .*: test:t_delta fails at .* and at the last checked commit ${h1:0:9}, which was checked with it as a known failure of TEST-row-known" "$q")"
    check "$1: t_gamma is filed as FAIL-main-<C0>, naming C0's known failures" 1 \
      "$(command grep -a -c "^QUEUE FAIL-main-${h1:0:9} (filed by main-watch .*: test:t_gamma fail at the last checked commit ${h1:0:9} too, which passed every test and benchmark when it was checked but the known failures test:t_delta (TEST-row-known), so" "$q")"
    check "$1: two QUEUE lines" 2 "$(wc -l <"$q")"
    check "$1: the known list" "test:t_delta TEST-row-known
test:t_gamma FAIL-main-${h1:0:9}" "$(command grep -a -v '^#' "$k" | sort)"
    check "$1: the head is checked" "$(head_of)" "$(checked)"
    check "$1: no culprit" "" "$(opened)"
    ;;
  skip)
    # A known line marked skip: the piece is not started at all (rung2 at n = 600 holds 67 to
    # 71 GB a run), through run_tests.sh's --except; the head is checked without it.
    setup b_eps
    unset MAIN_WATCH_RUN
    export MAIN_WATCH_ZRUN=$t/bin/zrun MW_RUN=$t/bin/run MW_ROOT=$root
    echo "bench:toy::b_eps TEST-row-skip skip" >"$t/home/main-watch-known.txt"
    for n in $(seq 1 15); do land "$n"; done
    watch
    check "skip: exit 0" 0 "$rc"
    check "skip: b_eps never ran" 0 "$(command grep -a -c -x 'bench b_eps' "$t/state/ran")"
    check "skip: the other benchmark ran" 1 "$(command grep -a -c -x 'bench b_beta' "$t/state/ran")"
    check "skip: no culprit" "" "$(opened)"
    check "skip: the head is checked" "$(head_of)" "$(checked)"
    check "skip: the running log names the skipped piece and its row" 1 \
      "$(command grep -a -c 'not run: bench:toy::b_eps (TEST-row-skip)' "$t/home/running-log.md")"
    ;;
  queue)
    # MAIN_WATCH_QUEUE: each culprit goes to its row as a QUEUE line, no fixer runs, and its pieces
    # join the known list with that row; the head is then checked with them as known failures,
    # without a second full run, and a later check does not bisect them again.
    setup
    twenty
    local a b q
    a=$(breaker t_alpha)
    b=$(breaker b_beta)
    q=$t/home/spawn-queue.txt
    echo "QUEUE OTHER-row (filed by someone)" >"$q"
    export MAIN_WATCH_QUEUE=$q
    watch
    check "queue: exit 0" 0 "$rc"
    check "queue: no fixer ran" 0 "$(cat "$t/state/fixer.log" 2>/dev/null | wc -l)"
    check "queue: the earlier line is kept" "QUEUE OTHER-row (filed by someone)" "$(sed -n 1p "$q")"
    check "queue: one QUEUE line per culprit, naming its row and the first bad commit" \
      "QUEUE TEST-row-5 ${a:0:9} test:t_alpha
QUEUE TEST-row-12 ${b:0:9} bench:b_beta" \
      "$(sed -n '2,$p' "$q" | sed -E 's/^(QUEUE [^ ]+) .*first bad commit ([0-9a-f]{9}) .* fails ([^;]*);.*/\1 \2 \3/')"
    check "queue: the pieces join the known list with their rows" "test:t_alpha TEST-row-5
bench:b_beta TEST-row-12" "$(cat "$t/home/main-watch-known.txt")"
    check "queue: the head is checked" "$(head_of)" "$(checked)"
    check "queue: the checked head's build is published, not the culprit's" "$(head_of)" "$(tail -1 "$t/state/published" 2>/dev/null)"
    check "queue: one full run of each kind" "1 1" \
      "$(command grep -a -c ' test all$' "$t/state/runs.log") $(command grep -a -c ' bench all$' "$t/state/runs.log")"
    land 21
    MAIN_WATCH_MIN=1 timeout 50 "$watch" >"$t/out2" 2>&1
    check "queue: the next check exits 0" 0 "$?"
    check "queue: the next check queues nothing again" 3 "$(wc -l <"$q")"
    check "queue: the next check checks the new head" "$(head_of)" "$(checked)"
    ;;
  reap)
    # Every run leaves a process; after each run the watcher kills what its run left, by pid, so
    # nothing of its runs outlives them (author, 2026-11-20: release all RAM after each run).
    setup
    export MW_LEAK=1
    for n in $(seq 1 15); do land "$n"; done
    watch
    local p alive=
    check "reap: exit 0" 0 "$rc"
    check "reap: runs left processes" yes "$([ -s "$t/state/leaked" ] && echo yes)"
    for p in $(cat "$t/state/leaked" 2>/dev/null); do kill -0 "$p" 2>/dev/null && alive+="$p "; done
    check "reap: none of them is alive" "" "$alive"
    check "reap: each kill is logged" "$(wc -l <"$t/state/leaked")" \
      "$(command grep -a -c 'killed by pid' "$t/out")"
    for p in $alive; do kill -KILL "$p"; done
    ;;
  build)
    # A build failure is a piece of its own: bisected and fixed like the others.
    setup
    for n in $(seq 1 16); do
      if [ "$n" = 9 ]; then land 9 2 2:BUILD; else land "$n"; fi
    done
    watch
    check "build: exit 0" 0 "$rc"
    check "build: the culprit is the commit that broke the build" "$(breaker BUILD)" "$(opened)"
    check "build: the head is checked" "$(head_of)" "$(checked)"
    ;;
  controls | controls:*)
    # Negative controls: each mutant of main_watch.sh drops one behavior and must fail the cases
    # that test it.
    local m mutants only=${1#controls}
    only=${only#:}
    mutants=(
      "stuck-exits|s/^\\(  say \"STUCK: .*\\)\$/\\1; exit 3/|failfix"
      "no-park|s/^  known_add \"\\\$row\" \"\\\$items\"\$/  :/|failfix"
      "no-crash-check|s/^      \\[ \"\\\$r\" -lt 128 \\] .*crashed+=.*\$/      :/|runkill"
      "no-flake-rerun|s/if \\[ -z \"\\\$(fails_twice \"\\\$p\"/if false \\&\\& [ -z \"\$(fails_twice \"\$p\"/|two"
      "no-git-bisect|s/rev-list --count \"\\\$prev..\\\$c\")\" -gt 1/rev-list --count \"\$prev..\$c\")\" -gt 999/|two"
      "fixer-not-awaited|s/^      \"\\\$MAIN_WATCH_FIXER\" \"\\\$brief\" \"\\\$dir\" >\\(.*\\) 2>&1\$/      ( sleep 3; \"\$MAIN_WATCH_FIXER\" \"\$brief\" \"\$dir\" ) >\\1 2>\\&1 \\&/|two"
      "no-reap|s/^  reap \"\\\$(cat .*\$/  :/|reap"
      "no-skip|s/(--except \"\\\$skip\")/()/|skip"
      "no-queue|s/^  if \\[ -n \"\\\$queue\" \\]; then\$/  if false; then/|queue"
      "publish-unchecked|s/^  if \\[ -n \"\\\$copy\" \\] .* checkout -q --detach .*; then\$/  if false; then/|queue"
      "no-spec-split|s/^    if \\[ \"\\\$spec_head\" != \"\\\$s0\" \\]; then\$/    if false; then/|spec"
      "unpinned-spec|s/^export ZED_SPEC_DIR=\\\$spec_dir\$/:/|spec"
      "fixed-by-ignored|s/&& set=fixed\$/\\&\\& set=in/|fixedby"
      "fixed-by-always|s#git -C \"\\\$repo\" merge-base --is-ancestor \"\\\$f\" \"\\\$c\" 2>/dev/null && set=fixed\$#set=fixed#|fixedby"
      "no-unfix|s/^      known_edit \"\\\$head\" \"\\\$back\" unfix\$/      :/|fixedbyfail"
      "known-dup|s/^    known_add \"\\\$owner\" \"\\\$items\"\$/    for t in \$items; do echo \"\$t \$owner\" >>\"\$known_file\"; done/|queuedup"
      "no-reread|s/^        whole=\\\$(cat \\/dev\\/fd\\/9)\$/        whole=\$old/|fixedbyrace"
      "no-known-checked|s#^  f=\\\$(cut -d' ' -f4 \"\\\$checked_file\")\$#  echo '?'; return 0#|oldknown"
      "no-log-fallback|s#^  \\[ -n \"\\\$l\" \\] .*\$#  echo '?'; return 0#|oldknownlog"
    )
    for m in "${mutants[@]}"; do
      IFS='|' read -r name expr cases <<<"$m"
      [ -z "$only" ] || [ "$only" = "$name" ] || continue
      sed "$expr" "$watch" >"$t/$name.sh"
      chmod +x "$t/$name.sh"
      check "controls: mutant $name changes one line" 1 "$(diff "$watch" "$t/$name.sh" | command grep -a -c '^>')"
      MW_WATCH=$t/$name.sh TMPDIR=$t "$root/tools/test_main_watch.sh" $cases >"$t/$name.out" 2>&1
      check "controls: mutant $name fails" 1 "$?"
    done
    [ -z "$only" ] || check "controls: a mutant named $only exists" yes "$([ -e "$t/$only.sh" ] && echo yes || echo no)"
    ;;
  *)
    echo "unknown case $1"
    fails=$((fails + 1))
    ;;
  esac
}

all_cases="two farm zrun fixbreak failfix nofix segv runkill nottwice nobisect setuperr clean few old oldqueue spec specold known hash hashold fixedby fixedbyfail fixedbyrace queuedup oldknown oldknownlog skip queue reap build controls"
for c in ${@:-$all_cases}; do run_case "$c"; done
echo "checks failed: $fails"
[ "$fails" = 0 ]
