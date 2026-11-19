#!/bin/bash
# Tests tools/main_watch.sh on toy repositories: a bare remote, the watcher's clone and a clone the
# landings are made from. The pieces are stubs: the files `tests` and `benches` list them, and a
# piece fails while broken/<piece> exists. t_flaky fails on its first run only (a flake). A stub
# fixer (MAIN_WATCH_FIXER) deletes broken/<piece> for each piece its brief names, commits, pushes
# and appends its landing to landings.log, as merge-push.sh does.
# Usage: tools/test_main_watch.sh [case...]; with no case, all. The toy directories are left
# under the directory it prints, for inspection.
pushd "$(dirname "$0")/.." >/dev/null || exit 2
root=$(pwd -P)
popd >/dev/null || exit 2
. "$root/tools/test_lib.sh"
# MW_WATCH: the script under test, for the negative controls (mutants that must fail).
watch=${MW_WATCH:-$root/tools/main_watch.sh}
fails=0
top=$(mktemp -d "${TMPDIR:-/tmp}/test-main-watch.XXXXXX")
echo "toy repositories under $top"

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
  # The runner: run_tests.sh's summary lines; BUILD FAILED while broken/BUILD exists.
  cat >"$t/bin/run" <<'EOF'
#!/bin/bash
logs=$1 kind=$2
shift 2
mkdir -p "$logs"
names=()
for n in "$@"; do [ "$n" = BUILD ] || names+=("$n"); done
echo "$(git rev-parse --short=9 HEAD) $kind ${*:-all}" >>"$MW_STATE/runs.log"
[ ! -e broken/BUILD ] || { echo "BUILD FAILED"; exit 1; }
[ $# -eq 0 ] || [ ${#names[@]} -gt 0 ] || exit 0
if [ ${#names[@]} -eq 0 ]; then
  if [ "$kind" = test ]; then mapfile -t names <tests; else mapfile -t names <benches; fi
fi
rc=0
for n in "${names[@]}"; do
  r=0
  [ ! -e "broken/$n" ] || r=1
  if [ "$n" = t_flaky ] && [ ! -e "$MW_STATE/flaky-ran" ]; then : >"$MW_STATE/flaky-ran"; r=1; fi
  echo "$n rc=$r 1ms load=0 limit=20s wait=0ms"
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
  [ "${MW_FIX:-}" = none ] || git rm -q --ignore-unmatch "broken/${p#*:}"
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
  printf '#!/bin/bash\ntrue\n' >"$t/bin/prepare"
  printf '#!/bin/bash\ngit -C "$1" worktree remove --force "$(realpath -e "$1")"\n' >"$t/bin/remove"
  chmod +x "$t/bin/run" "$t/bin/fix" "$t/bin/prepare" "$t/bin/remove"
  # The template holds every placeholder; the fixer reads the "Failing pieces:" line.
  printf '%s\n' '# {{ROW}} attempt {{ATTEMPT}}' 'Commit {{COMMIT}} of {{LANDING}}.' \
    'Failing pieces: {{PIECES}}' '{{EARLIER}}' 'Base {{BASE}}, worktree {{WORKTREE}}, branch {{BRANCH}}.' \
    'Message:' '{{MESSAGE}}' 'Files:' '{{STAT}}' 'Diff: {{DIFF}}' 'Output:' '{{OUTPUT}}' 'Bisect:' '{{BISECT}}' \
    >"$t/template"
  export MAIN_WATCH_HOME=$t/home MAIN_WATCH_REPO=$t/repo MAIN_WATCH_TREES=$t/trees \
    MAIN_WATCH_PREPARE=$t/bin/prepare MAIN_WATCH_REMOVE=$t/bin/remove MAIN_WATCH_RUN=$t/bin/run \
    MAIN_WATCH_FIXER=$t/bin/fix MAIN_WATCH_TEMPLATE=$t/template MAIN_WATCH_POLL=0 MAIN_WATCH_POLLS=2 \
    MW_STATE=$t/state
  unset MW_FIX MW_FIX_BREAK
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
    # A fixer that ends without landing leaves the watcher stopped, with the stuck entry.
    setup
    twenty
    export MW_FIX=fail
    watch
    local a
    a=$(breaker t_alpha)
    check "failfix: exit 3" 3 "$rc"
    check "failfix: a stuck line for t_alpha's culprit" 1 "$(command grep -a -c "^stuck $a .* main-watch " "$t/home/main-red.log")"
    check "failfix: the stuck entry" 1 "$(command grep -a -c "^## .* main-watch stuck: FAIL-main-${a:0:9}: the fixing agent of attempt 1 ended without landing" "$t/home/main-watch-stuck.md")"
    check "failfix: the entry says what it holds up" 1 "$(command grep -a -c '^Holds up: main-watch has stopped' "$t/home/main-watch-stuck.md")"
    check "failfix: no second poll" - "$(order '^main-watch: poll 2:')"
    check "failfix: the checked commit is unchanged" "$c0" "$(checked)"
    check "failfix: one fix attempt" 1 "$(wc -l <"$t/state/fixer.log")"
    ;;
  nofix)
    # Fixers that land but fix nothing: three attempts, then stuck.
    setup
    twenty
    export MW_FIX=none
    watch
    local a
    a=$(breaker t_alpha)
    check "nofix: exit 3" 3 "$rc"
    check "nofix: three attempts" 3 "$(wc -l <"$t/state/fixer.log")"
    check "nofix: stuck after 3 attempts" 1 "$(command grep -a -c "main-watch stuck: FAIL-main-${a:0:9}: test:t_alpha still fail after 3 fix attempts" "$t/home/main-watch-stuck.md")"
    check "nofix: no second poll" - "$(order '^main-watch: poll 2:')"
    check "nofix: the checked commit is unchanged" "$c0" "$(checked)"
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
    # A failure that exists at the last checked commit is not bisected; the watcher stops.
    setup t_delta
    for n in $(seq 1 15); do land "$n"; done
    watch
    check "old: exit 3" 3 "$rc"
    check "old: no culprit" "" "$(opened)"
    check "old: the stuck entry names the old failure" 1 "$(command grep -a -c "main-watch stuck: test:t_delta fail at the last checked commit" "$t/home/main-watch-stuck.md")"
    check "old: the checked commit is unchanged" "$c0" "$(checked)"
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
  controls)
    # Negative controls: each mutant of main_watch.sh drops one behavior and must fail the cases
    # that test it.
    local m mutants
    mutants=(
      "stuck-continues|s/^  exit 3\$/  return 0/|failfix"
      "no-flake-rerun|s/if \\[ -z \"\\\$(fails_twice \"\\\$p\"/if false \\&\\& [ -z \"\$(fails_twice \"\$p\"/|two"
      "no-git-bisect|s/rev-list --count \"\\\$prev..\\\$c\")\" -gt 1/rev-list --count \"\$prev..\$c\")\" -gt 999/|two"
      "fixer-not-awaited|s/^      \"\\\$MAIN_WATCH_FIXER\" \"\\\$brief\" \"\\\$dir\" >\\(.*\\) 2>&1\$/      ( sleep 3; \"\$MAIN_WATCH_FIXER\" \"\$brief\" \"\$dir\" ) >\\1 2>\\&1 \\&/|two"
    )
    for m in "${mutants[@]}"; do
      IFS='|' read -r name expr cases <<<"$m"
      sed "$expr" "$watch" >"$t/$name.sh"
      chmod +x "$t/$name.sh"
      check "controls: mutant $name changes one line" 1 "$(diff "$watch" "$t/$name.sh" | command grep -a -c '^>')"
      MW_WATCH=$t/$name.sh TMPDIR=$t "$root/tools/test_main_watch.sh" $cases >"$t/$name.out" 2>&1
      check "controls: mutant $name fails" 1 "$?"
    done
    ;;
  *)
    echo "unknown case $1"
    fails=$((fails + 1))
    ;;
  esac
}

all_cases="two fixbreak failfix nofix clean few old build controls"
for c in ${@:-$all_cases}; do run_case "$c"; done
echo "checks failed: $fails"
[ "$fails" = 0 ]
