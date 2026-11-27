#!/bin/bash
# Tests tools/prune_logs.sh (TOOL-test-logs-prune), which lists the per-run log directories that may
# be deleted and deletes nothing. Run from a checkout's root; about 1 s. The fixture is
# build/test-prune-logs, set up again by each run (its names are fixed, its times set by touch), so
# a run leaves nothing new behind and none deletes it.
prune=$(pwd)/tools/prune_logs.sh
t=$(pwd)/build/test-prune-logs
b=$t/base
mkdir -p "$b"
fails=0
. tools/test_lib.sh || exit 2
# dir <name> <days old>: a run directory with one file, its time set <days> back.
dir() {
  mkdir -p "$b/$1"
  echo x >"$b/$1/run"
  touch -d "@$(($(date +%s) - $2 * 86400))" "$b/$1/run" "$b/$1"
}
# The run directories of tools/run_tests.sh (<UTC time>-<pid>), from oldest to newest.
A=20261101T000000.000000001Z-11
B=20261101T000000.000000002Z-12
C=20261101T000000.000000003Z-13
D=20261101T000000.000000004Z-14
E=20261101T000000.000000005Z-15
F=20261101T000000.000000006Z-16
dir $A 10
dir $B 9
dir $C 8
# D's subdirectory is made before its time is set, which making it would change.
mkdir -p "$b/$D/sub"
dir $D 7
dir $E 6
dir $F 0
# A run directory of tools/main_watch.sh, and two script copies of /home/luke/Work/wt/main-watch.sh.
M=20261101-000000-17
dir $M 10
dir script.Ab12Cd 10
dir script.Zz99Yy 10
# What is never listed: a file and a symbolic link with a run directory's name, and a directory
# with another name, all old.
echo x >"$b/20261101T000000.000000009Z-19"
touch -d @0 "$b/20261101T000000.000000009Z-19"
mkdir -p "$t/outside"
ln -sfn "$t/outside" "$b/20261101T000000.000000008Z-18"
dir other 10
# latest names E, as tools/run_tests.sh leaves it.
ln -sfn $E "$b/latest"
# C is cited in a file; D is the working directory of a live process; script.Ab12Cd is named in
# the arguments of one (as main-watch.sh runs <copy>/main_watch.sh).
echo "see $b/$C/run for the log" >"$t/cited.md"
: >"$t/err"
(cd "$b/$D/sub" && exec sleep 20) &
p1=$!
(exec -a "$b/script.Ab12Cd/main_watch.sh" sleep 20) &
p2=$!
# Wait until both have started (their /proc entries show the new directory and name).
for _ in $(seq 100); do
  [ "$(readlink "/proc/$p1/cwd")" = "$b/$D/sub" ] && tr '\0' '\n' <"/proc/$p2/cmdline" | command grep -q -a -F script.Ab12Cd && break
  sleep 0.02
done
before=$(find "$t" | LC_ALL=C sort)

out=$("$prune" --keep 1 --days 3 --cited "$t/cited.md" "$b" 2>"$t/err")
check "the old directories neither newest, recent, latest, in use nor cited are listed, by absolute path" \
  "0
$b/$M
$b/$A
$b/$B
$b/script.Zz99Yy" "$?
$out"
check "the summary counts each kept directory once, by its first reason" \
  "prune_logs: $b: 9 run directories; keep 5 (latest 1, newest 1, recent 0, in use 2, cited 1); list 4" \
  "$(command grep -a '^prune_logs: ' "$t/err")"
check "a directory in use is reported with the pid that uses it" "2" \
  "$(command grep -a -c -E "^kept: $b/($D: in use by pid $p1|script.Ab12Cd: in use by pid $p2)\$" "$t/err")"
check "a cited directory is reported with the file that cites it" "1" \
  "$(command grep -a -c -x -F "kept: $b/$C: cited in $t/cited.md" "$t/err")"
check "nothing is deleted" "$before" "$(find "$t" | LC_ALL=C sort)"

# Recent: with --days 9.5, B (9 days old) is kept and A and the main-watch ones (10 days) are
# listed; C (8 days) is recent, so kept without --cited.
out=$("$prune" --keep 1 --days 9.5 "$b" 2>/dev/null)
check "--days keeps what changed within that many days" "$b/$M
$b/$A
$b/script.Zz99Yy" "$out"

# Without --cited, C is listed.
out=$("$prune" --keep 1 --days 3 "$b" 2>/dev/null)
check "without --cited a cited directory is listed (negative control of --cited)" "$b/$M
$b/$A
$b/$B
$b/$C
$b/script.Zz99Yy" "$out"

# A base named through a symbolic link and a relative path is listed by its real absolute path.
ln -sfn "$b" "$t/link"
out=$(cd "$t" && "$prune" --keep 1 --days 3 --cited cited.md link 2>/dev/null)
check "a base given by a relative path through a link lists real absolute paths" "$b/$M
$b/$A
$b/$B
$b/script.Zz99Yy" "$out"

# The defaults keep the newest 10 of each base: all 9 here.
out=$("$prune" "$b" 2>/dev/null)
check "the defaults (newest 10, 7 days) list nothing here" "0 " "$? $out"

# Two bases: each keeps its own newest.
mkdir -p "$t/base2/$A"
touch -d @0 "$t/base2/$A"
out=$("$prune" --keep 1 --days 3 --cited "$t/cited.md" "$b" "$t/base2" 2>/dev/null)
check "each base keeps its own newest" "$b/$M
$b/$A
$b/$B
$b/script.Zz99Yy" "$out"

kill "$p1" "$p2"
wait "$p1" "$p2" 2>/dev/null
out=$("$prune" --keep 1 --days 3 --cited "$t/cited.md" "$b" 2>/dev/null)
check "once the processes have ended, their directories are listed" "$b/$M
$b/$A
$b/$B
$b/$D
$b/script.Ab12Cd
$b/script.Zz99Yy" "$out"

"$prune" >/dev/null 2>&1
check "no base is a usage error" "2" "$?"
"$prune" "$t/missing" >/dev/null 2>&1
check "a missing base is an error" "2" "$?"
"$prune" --keep x "$b" >/dev/null 2>&1
check "a --keep that is not a number is a usage error" "2" "$?"
"$prune" --cited "$t/missing.md" "$b" >/dev/null 2>&1
check "a missing --cited file is an error" "2" "$?"

[ "$fails" = 0 ] && echo "test_prune_logs: all passed" || echo "test_prune_logs: $fails FAILED"
[ "$fails" = 0 ]
