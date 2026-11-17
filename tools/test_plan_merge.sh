#!/bin/bash
# Tests tools/plan_merge.sh, the merge driver for docs/plan_dag.md, through real `git rebase` and
# `git merge` runs in a git repository of its own, build/test-plan-merge, which it keeps from run
# to run (it deletes nothing: each case writes its files again and moves its branches with
# `git checkout -B`). Run from a checkout's root: `tools/test_plan_merge.sh`; a few seconds.
# The repository holds tools/plan_merge.sh, the .gitattributes line and the config of
# tools/plan_merge.sh's header, so the driver runs as it does in a worktree of zed-impl. The last
# case runs on a copy of this checkout's docs/plan_dag.md.
src=$(pwd)
repo=$src/build/test-plan-merge
mkdir -p "$repo"
fails=0
ok() { echo "ok: $1"; }
bad() {
  echo "FAILED: $1"
  fails=$((fails + 1))
}
g() { git -C "$repo" "$@"; }
[ -d "$repo/.git" ] || g init -q -b main
g config user.name test
g config user.email test@example.invalid
g config merge.conflictstyle diff3
g config merge.plan-needs.name "plan_dag.md: needs cells and counts"
g config merge.plan-needs.driver "tools/plan_merge.sh %O %A %B %L %S %X %Y"
g rebase --abort >/dev/null 2>&1
g merge --abort >/dev/null 2>&1

# A small plan: the count sentence, then the table. $1: L1.41's needs; $2: lines to add after the
# first row; $3: lines to add at the end; $4: the title of T2; $5: the count sentence's numbers.
plan() {
  printf '%s\n' "# Plan DAG" "" "This file lists the remaining work. It has ${5:-4 items, 3 edges and 2 levels (0 to 1)}. More text." "" \
    "## Items by level" "" "| Level | Id | Title | Size | Hard | Needs | Paths |" "|---|---|---|---|---|---|---|" \
    "| 0 | T1 | First | S | no | none | \`a/\` |"
  [ -z "$2" ] || printf '%s\n' "$2"
  printf '%s\n' "| 0 | T2 | ${4:-Second, with a | in its title} | S | no | none | \`b/\` |" \
    "| 0 | T3 | Third | S | no | none | \`c/\` |" \
    "| 1 | L1.41 | End of layer | M | no | $1 | \`tests/\` |"
  [ -z "$3" ] || printf '%s\n' "$3"
  printf '%s\n' "" "## Why each item waits" "" "Notes."
}
# A commit on branch $1 (made from $2) with docs/plan_dag.md read from stdin.
commit() {
  g checkout -q -B "$1" "$2"
  mkdir -p "$repo/docs"
  cat >"$repo/docs/plan_dag.md"
  g add docs/plan_dag.md
  g commit -q -m "$1"
}
needs_of() { command grep -a -E '^\| [0-9]+ \| L1\.41 \|' "$repo/docs/plan_dag.md" | awk -F'|' '{ print $(NF - 2) }' | sed 's/^ *//; s/ *$//'; }
markers() { command grep -a -c -E '^(<<<<<<<|>>>>>>>) ' "$repo/docs/plan_dag.md"; }

# The base commit, on an empty root commit made once: the driver, the attribute and the plan.
g rev-parse -q --verify refs/tags/root >/dev/null || { g commit -q --allow-empty -m root && g tag root; }
g checkout -q -f -B main root
mkdir -p "$repo/tools" "$repo/docs"
cp "$src/tools/plan_merge.sh" "$repo/tools/plan_merge.sh"
echo 'docs/plan_dag.md merge=plan-needs' >"$repo/.gitattributes"
plan "T1, T2, T3" >"$repo/docs/plan_dag.md"
g add tools .gitattributes docs
g commit -q -m base
base=$(g rev-parse HEAD)

# Each case: branch one and branch two from $base; two is rebased on one (as merge-push.sh
# rebases a branch on main). $1 the name, $2 and $3 the plans of one and two.
rebase_case() {
  echo "$2" | commit one "$base"
  echo "$3" | commit two "$base"
  g rebase -q one >"$repo.out" 2>&1
}

# 1. Each side files a row and adds its id to L1.41's needs, and both change the count sentence.
rebase_case "rows added" \
  "$(plan "T1, T2, T3, FAIL-a" "" "| 0 | FAIL-a | A | S | no | none | \`x/\` |" "" "5 items, 4 edges and 2 levels (0 to 1)")" \
  "$(plan "T1, T2, T3, FAIL-b" "| 0 | FAIL-b | B | S | no | none | \`y/\` |" "" "" "5 items, 4 edges and 2 levels (0 to 1)")"
rc=$?
want=$(plan "T1, T2, T3, FAIL-a, FAIL-b" "| 0 | FAIL-b | B | S | no | none | \`y/\` |" "| 0 | FAIL-a | A | S | no | none | \`x/\` |" "" "5 items, 4 edges and 2 levels (0 to 1)")
if [ $rc -eq 0 ] && [ "$(cat "$repo/docs/plan_dag.md")" = "$want" ]; then ok "rebase: both new ids kept in L1.41's needs, count sentence taken from main"; else
  bad "rebase of two added ids (rc $rc): needs '$(needs_of)'"
  g rebase --abort >/dev/null 2>&1
fi
# The same as a merge, in both directions.
for dir in "one two" "two one"; do
  set -- $dir
  g checkout -q -B m "$(g rev-parse "$1")"
  g merge -q --no-edit "$2" >"$repo.out" 2>&1
  rc=$?
  n=$(needs_of)
  if [ $rc -eq 0 ] && { [ "$n" = "T1, T2, T3, FAIL-a, FAIL-b" ] || [ "$n" = "T1, T2, T3, FAIL-b, FAIL-a" ]; }; then ok "merge $2 into $1: both ids"; else
    bad "merge $2 into $1 (rc $rc): needs '$n'"
    g merge --abort >/dev/null 2>&1
  fi
done

# 2. One side removes an id and adds one; the other adds one; base needs none on another row.
rebase_case "removed id" \
  "$(plan "T1, T3, FAIL-a" "" "" "" "4 items, 2 edges and 2 levels (0 to 1)")" \
  "$(plan "T1, T2, T3, FAIL-b, FAIL-c" "" "" "" "4 items, 5 edges and 2 levels (0 to 1)")"
rc=$?
n=$(needs_of)
if [ $rc -eq 0 ] && [ "$n" = "T1, T3, FAIL-a, FAIL-b, FAIL-c" ]; then ok "rebase: an id one side removed stays removed, both sides' additions kept"; else
  bad "rebase with a removed id (rc $rc): needs '$n'"
  g rebase --abort >/dev/null 2>&1
fi
# The same with the sides swapped: theirs (the branch rebased) removes an id, ours adds one.
rebase_case "removed id, theirs" \
  "$(plan "T1, T2, T3, FAIL-a" "" "" "" "4 items, 4 edges and 2 levels (0 to 1)")" \
  "$(plan "T1, T3, FAIL-b" "" "" "" "4 items, 3 edges and 2 levels (0 to 1)")"
rc=$?
n=$(needs_of)
if [ $rc -eq 0 ] && [ "$n" = "T1, T3, FAIL-a, FAIL-b" ]; then ok "rebase: an id the rebased branch removed stays removed"; else
  bad "rebase with an id removed by the rebased branch (rc $rc): needs '$n'"
  g rebase --abort >/dev/null 2>&1
fi
# Both sides empty the cell: none.
rebase_case "emptied" "$(plan "none")" "$(plan "none")"
rc=$?
if [ $rc -eq 0 ] && [ "$(needs_of)" = "none" ]; then ok "rebase: both sides emptied the cell"; else
  bad "rebase of two emptied cells (rc $rc): needs '$(needs_of)'"
  g rebase --abort >/dev/null 2>&1
fi
# One side removes every id, the other adds one: only the added one is left.
rebase_case "one emptied" "$(plan "none")" "$(plan "T1, T2, T3, FAIL-b")"
rc=$?
if [ $rc -eq 0 ] && [ "$(needs_of)" = "FAIL-b" ]; then ok "rebase: one side emptied the cell, the other added an id"; else
  bad "rebase of an emptied cell and an added id (rc $rc): needs '$(needs_of)'"
  g rebase --abort >/dev/null 2>&1
fi

# Negative controls: each must still conflict, with git's markers, as without the driver.
# 3. Both sides change the same row's title differently.
rebase_case "titles" "$(plan "T1, T2, T3" "" "" "Second, as one side says")" "$(plan "T1, T2, T3" "" "" "Second, as the other says")"
rc=$?
m=$(markers)
g rebase --abort >/dev/null 2>&1
if [ $rc -ne 0 ] && [ "$m" = 2 ]; then ok "negative control: two titles of one row still conflict"; else bad "two titles of one row (rc $rc, marker lines $m)"; fi
# 4. Both sides add an id to L1.41, and one side also changes L1.41's title: not the needs cell
# alone.
rebase_case "needs and same-row title" \
  "$(plan "T1, T2, T3, FAIL-a")" \
  "$(plan "T1, T2, T3, FAIL-b" | sed 's/| End of layer |/| End of the layer |/')"
rc=$?
g rebase --abort >/dev/null 2>&1
if [ $rc -ne 0 ]; then ok "negative control: needs on both sides and the same row's title on one still conflict"; else bad "needs plus the same row's title change was merged"; fi
# 5. Both sides change the count sentence's paragraph outside the counts.
rebase_case "paragraph" \
  "$(plan "T1, T2, T3" | sed 's/More text\./More text, one./')" \
  "$(plan "T1, T2, T3" | sed 's/More text\./More text, two./')"
rc=$?
g rebase --abort >/dev/null 2>&1
if [ $rc -ne 0 ]; then ok "negative control: two edits of the count paragraph's prose still conflict"; else bad "two prose edits were merged"; fi
# 6. Without the driver's config, case 1 conflicts: the passes above are the driver's doing.
g config --unset merge.plan-needs.driver
rebase_case "no driver" \
  "$(plan "T1, T2, T3, FAIL-a" "" "| 0 | FAIL-a | A | S | no | none | \`x/\` |" "" "5 items, 4 edges and 2 levels (0 to 1)")" \
  "$(plan "T1, T2, T3, FAIL-b" "| 0 | FAIL-b | B | S | no | none | \`y/\` |" "" "" "5 items, 4 edges and 2 levels (0 to 1)")"
rc=$?
g rebase --abort >/dev/null 2>&1
g config merge.plan-needs.driver "tools/plan_merge.sh %O %A %B %L %S %X %Y"
if [ $rc -ne 0 ]; then ok "negative control: without the driver the same rebase conflicts"; else bad "the rebase without the driver did not conflict"; fi

# 7. The real plan: two branches each add a row at level 0 and its id to L1.41's needs, and each
# recounts the count sentence, as an agent filing a fault does.
if [ -f "$src/docs/plan_dag.md" ]; then
  real=$(cat "$src/docs/plan_dag.md")
  add() { # $1 the id: the plan with a row for it after the first row, and it in L1.41's needs
    awk -v id="$1" '
      /^\| [0-9]+ \| L1\.41 \|/ { n = split($0, c, "|"); c[n - 2] = c[n - 2] ", " id " "; sub(/  $/, " ", c[n - 2]); s = c[1]; for (i = 2; i <= n; i++) s = s "|" c[i]; $0 = s }
      { sub(/It has [0-9]+ items/, "It has " (length(id) * 1000) " items") }
      { print }
      /^\| 0 \| / && !done { print "| 0 | " id " | A test row | S | no | none | `x/` |"; done = 1 }
    ' <<<"$real"
  }
  echo "$real" | commit main "$base"
  base_real=$(g rev-parse HEAD)
  add FAIL-real-a | commit one "$base_real"
  add FAIL-real-bb | commit two "$base_real"
  g rebase -q one >"$repo.out" 2>&1
  rc=$?
  n=$(needs_of)
  if [ $rc -eq 0 ] && [[ $n == *", FAIL-real-a, FAIL-real-bb" ]] && [ "$(markers)" = 0 ]; then ok "the real plan: both ids added to L1.41's needs kept"; else
    bad "the real plan (rc $rc): needs end '${n: -60}'"
    g rebase --abort >/dev/null 2>&1
  fi
  # Negative control: the same rebase without the driver conflicts.
  g config --unset merge.plan-needs.driver
  add FAIL-real-bb | commit two "$base_real"
  g rebase -q one >"$repo.out" 2>&1
  rc=$?
  g rebase --abort >/dev/null 2>&1
  g config merge.plan-needs.driver "tools/plan_merge.sh %O %A %B %L %S %X %Y"
  if [ $rc -ne 0 ]; then ok "negative control: the real plan's rebase conflicts without the driver"; else bad "the real plan's rebase did not conflict without the driver"; fi
fi

echo "failed: $fails"
[ "$fails" -eq 0 ]
