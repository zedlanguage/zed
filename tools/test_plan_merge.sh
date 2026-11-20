#!/bin/bash
# Tests tools/plan_merge.sh, the merge driver for docs/plan_dag.md, through real `git rebase` and
# `git merge` runs in a git repository of its own, build/test-plan-merge, which it keeps from run
# to run (it deletes nothing: each case writes its files again and moves its branches with
# `git checkout -B`). Run from a checkout's root: `tools/test_plan_merge.sh`; a few seconds.
# The repository holds tools/plan_merge.sh, the .gitattributes line and the config of
# tools/plan_merge.sh's header, so the driver runs as it does in a worktree of zed-impl. Cases 7
# and 9 run on a copy of this checkout's docs/plan_dag.md, and case 10 on the plan at commit
# 1d2198af8. Cases 9 and 10 need the built plan and conflicts tools (PLAN_TOOL, CONFLICTS_TOOL).
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

# A small plan: a paragraph, then the table. $1: L1.41's needs; $2: lines to add after the first
# row; $3: lines to add at the end; $4: the title of T2; $5: when given, the numbers of a count
# sentence in the paragraph, as the file held one until TOOL-plan-counts-after-rebase.
plan() {
  printf '%s\n' "# Plan DAG" "" "This file lists the remaining work.${5:+ It has $5.} More text." "" \
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

# 1. Each side files a row and adds its id to L1.41's needs.
rebase_case "rows added" \
  "$(plan "T1, T2, T3, FAIL-a" "" "| 0 | FAIL-a | A | S | no | none | \`x/\` |")" \
  "$(plan "T1, T2, T3, FAIL-b" "| 0 | FAIL-b | B | S | no | none | \`y/\` |")"
rc=$?
want=$(plan "T1, T2, T3, FAIL-a, FAIL-b" "| 0 | FAIL-b | B | S | no | none | \`y/\` |" "| 0 | FAIL-a | A | S | no | none | \`x/\` |")
if [ $rc -eq 0 ] && [ "$(cat "$repo/docs/plan_dag.md")" = "$want" ]; then ok "rebase: both new ids kept in L1.41's needs"; else
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
  "$(plan "T1, T3, FAIL-a")" \
  "$(plan "T1, T2, T3, FAIL-b, FAIL-c")"
rc=$?
n=$(needs_of)
if [ $rc -eq 0 ] && [ "$n" = "T1, T3, FAIL-a, FAIL-b, FAIL-c" ]; then ok "rebase: an id one side removed stays removed, both sides' additions kept"; else
  bad "rebase with a removed id (rc $rc): needs '$n'"
  g rebase --abort >/dev/null 2>&1
fi
# The same with the sides swapped: theirs (the branch rebased) removes an id, ours adds one.
rebase_case "removed id, theirs" \
  "$(plan "T1, T2, T3, FAIL-a")" \
  "$(plan "T1, T3, FAIL-b")"
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
# 5. Both sides change the first paragraph's prose.
rebase_case "paragraph" \
  "$(plan "T1, T2, T3" | sed 's/More text\./More text, one./')" \
  "$(plan "T1, T2, T3" | sed 's/More text\./More text, two./')"
rc=$?
g rebase --abort >/dev/null 2>&1
if [ $rc -ne 0 ]; then ok "negative control: two edits of the first paragraph's prose still conflict"; else bad "two prose edits were merged"; fi
# 6. Without the driver's config, case 1 conflicts: the passes above are the driver's doing.
g config --unset merge.plan-needs.driver
rebase_case "no driver" \
  "$(plan "T1, T2, T3, FAIL-a" "" "| 0 | FAIL-a | A | S | no | none | \`x/\` |")" \
  "$(plan "T1, T2, T3, FAIL-b" "| 0 | FAIL-b | B | S | no | none | \`y/\` |")"
rc=$?
g rebase --abort >/dev/null 2>&1
g config merge.plan-needs.driver "tools/plan_merge.sh %O %A %B %L %S %X %Y"
if [ $rc -ne 0 ]; then ok "negative control: without the driver the same rebase conflicts"; else bad "the rebase without the driver did not conflict"; fi

# 7. The real plan: two branches each add a row at level 0 and its id to L1.41's needs, as an
# agent filing a fault does.
if [ -f "$src/docs/plan_dag.md" ]; then
  real=$(cat "$src/docs/plan_dag.md")
  add() { # $1 the id: the plan with a row for it after the first row, and it in L1.41's needs
    awk -v id="$1" '
      /^\| [0-9]+ \| L1\.41 \|/ { n = split($0, c, "|"); c[n - 2] = c[n - 2] ", " id " "; sub(/  $/, " ", c[n - 2]); s = c[1]; for (i = 2; i <= n; i++) s = s "|" c[i]; $0 = s }
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

# 8. The count sentence and the conflict lists the file held until TOOL-plan-counts-after-rebase
# (2026-11-19): the driver takes both out of all three versions, as plan --fix does. Each side of
# a plan written that way adds a row and writes its own counts and lists, as two branches made
# before that change did with plan --fix; or main has already taken them out, and a branch made
# before still holds them. Either way the rebase stops nowhere and the result holds both rows and
# neither part. $1: the plan's other arguments' needs, $2 and $3 the lines added after the first
# row and at the end, $4 the pair line, $5 the cross line, $6 the count of pairs, $7 the count
# sentence's numbers.
old_plan() {
  plan "$1" "$2" "$3" "" "$7" | awk -v lists="$(old_lists "$4" "$5" "$6")" '$0 == "## Why each item waits" { print lists; print "" } { print }'
}
old_lists() { # $1 the pair line, $2 the cross line, $3 the count
  printf '%s\n' "## File conflicts at the same level" "" "There are $3 pairs." "" "| Level | Items | Shared paths |" "|---|---|---|" \
    "| 0 | T1, T2 | \`a/\` |" "$1" "| 0 | T2, T3 | \`c/\` |" "" "## File conflicts across levels" "" "- \`a/\`: level 0: T1" "$2" "- \`z/\`: level 1: L1.41"
}
row_a="| 0 | FAIL-a | A | S | no | none | \`x/\` |"
row_b="| 0 | FAIL-b | B | S | no | none | \`y/\` |"
old_base=$(old_plan "T1, T2, T3" "" "" "| 0 | T1, T3 | \`a/\` |" "- \`b/\`: level 0: T2" 3 "4 items, 3 edges and 2 levels (0 to 1)")
old_one=$(old_plan "T1, T2, T3, FAIL-a" "" "$row_a" "| 0 | T1, FAIL-a | \`x/\` |" "- \`x/\`: level 0: FAIL-a" 4 "5 items, 4 edges and 2 levels (0 to 1)")
old_two=$(old_plan "T1, T2, T3, FAIL-b" "$row_b" "" "| 0 | T1, FAIL-b | \`y/\` |" "- \`y/\`: level 0: FAIL-b" 5 "5 items, 4 edges and 2 levels (0 to 1)")
new_one=$(plan "T1, T2, T3, FAIL-a" "" "$row_a")
want=$(plan "T1, T2, T3, FAIL-a, FAIL-b" "$row_b" "$row_a")
old_case() { # $1 the plan of one, $2 that of two, both from the base old_base
  echo "$old_base" | commit main "$base"
  obase=$(g rev-parse HEAD)
  echo "$1" | commit one "$obase"
  echo "$2" | commit two "$obase"
  g rebase -q one >"$repo.out" 2>&1
}
old_case "$old_one" "$old_two"
rc=$?
if [ $rc -eq 0 ] && [ "$(cat "$repo/docs/plan_dag.md")" = "$want" ]; then ok "rebase: both sides' count sentences and lists taken out, both rows kept"; else
  bad "both sides' count sentences and lists (rc $rc, marker lines $(markers))"
  g rebase --abort >/dev/null 2>&1
fi
old_case "$new_one" "$old_two"
rc=$?
if [ $rc -eq 0 ] && [ "$(cat "$repo/docs/plan_dag.md")" = "$want" ]; then ok "rebase: a branch still holding the count sentence and lists onto a main without them"; else
  bad "a branch with the old parts onto a main without them (rc $rc, marker lines $(markers))"
  g rebase --abort >/dev/null 2>&1
fi
# Negative control: the same with the stripping turned off in a copy of the driver conflicts, so
# the passes above are its doing.
sed 's/^strip() {$/strip() { cat "$1"; }\nstrip_off() {/' "$src/tools/plan_merge.sh" >"$repo.nostrip.sh"
chmod +x "$repo.nostrip.sh"
cmp -s "$repo.nostrip.sh" "$src/tools/plan_merge.sh" && bad "the mutation of the stripping changed nothing"
g config merge.plan-needs.driver "$repo.nostrip.sh %O %A %B %L %S %X %Y"
old_case "$old_one" "$old_two"
rc=$?
g rebase --abort >/dev/null 2>&1
old_case "$new_one" "$old_two"
rc2=$?
g rebase --abort >/dev/null 2>&1
g config merge.plan-needs.driver "tools/plan_merge.sh %O %A %B %L %S %X %Y"
if [ $rc -ne 0 ] && [ $rc2 -ne 0 ]; then ok "negative control: without the stripping both rebases conflict"; else bad "a rebase merged without the stripping (rc $rc and $rc2)"; fi
# Negative control: the section after the lists is kept, so prose there changed on both sides
# still conflicts.
old_case "$(sed 's/^Notes\.$/Notes, one./' <<<"$old_one")" "$(sed 's/^Notes\.$/Notes, two./' <<<"$old_two")"
rc=$?
m=$(markers)
g rebase --abort >/dev/null 2>&1
if [ $rc -ne 0 ] && [ "$m" = 2 ]; then ok "negative control: prose after the lists, changed on both sides, still conflicts"; else bad "prose after the lists was merged (rc $rc, marker lines $m)"; fi

# 9. The real plan tool ($PLAN_TOOL, a command; by default this checkout's release build of plan
# run through /home/luke/Work/wt/zrun) and the real conflicts tool ($CONFLICTS_TOOL).
plan_tool=${PLAN_TOOL:-/home/luke/Work/wt/zrun build/cargo/release/plan}
conflicts_tool=${CONFLICTS_TOOL:-/home/luke/Work/wt/zrun build/cargo/release/conflicts}
# First: the driver takes out what plan --fix takes out. Merged with itself as base and theirs,
# the old plan of case 8 comes out of the driver as plan --fix writes it. T2's title has its `|`
# written `\|` here, since plan --fix refuses a row with a stray `|`, as it should.
old_nine=${old_one//'with a | in'/'with a \| in'}
new_nine=${new_one//'with a | in'/'with a \| in'}
for f in o a b fix; do printf '%s\n' "$old_nine" >"$repo.$f.md"; done
pushd "$repo" >/dev/null && tools/plan_merge.sh "$repo.o.md" "$repo.a.md" "$repo.b.md"
rc=$?
popd >/dev/null
if ! $plan_tool --fix "$repo.fix.md" >"$repo.fix.out" 2>&1; then
  bad "plan --fix of case 8's plan failed:"
  cat "$repo.fix.out"
  echo "build it with /home/luke/Work/wt/zcargo build --release -p zed-tools --bin plan --bin conflicts, or set PLAN_TOOL and CONFLICTS_TOOL"
elif [ $rc -eq 0 ] && cmp -s "$repo.a.md" "$repo.fix.md" && [ "$(cat "$repo.a.md")" = "$new_nine" ]; then
  ok "the driver takes out the count sentence and the lists as plan --fix does"
else
  bad "the driver (rc $rc) and plan --fix differ: $(diff "$repo.a.md" "$repo.fix.md" | head -c 400)"
fi
# Then the real plan: each side adds a level-0 row whose paths other open level-0 rows touch, and
# its id to L1.41's needs. The rebase stops nowhere and its result passes the plan check as it
# is, with no plan --fix, and the conflicts tool lists both rows.
if [ -f "$src/docs/plan_dag.md" ]; then
  with_row() { # $1 the id: the real plan with its row added (none when empty)
    awk -v id="$1" 'id == "" { print; next }
      /^\| [0-9]+ \| L1\.41 \|/ { n = split($0, c, "|"); c[n - 2] = c[n - 2] ", " id " "; sub(/  $/, " ", c[n - 2]); s = c[1]; for (i = 2; i <= n; i++) s = s "|" c[i]; $0 = s }
      { print }
      /^\| 0 \| / && !done { print "| 0 | " id " | A test row | S | no | none | `DESIGN.md`, `crates/zedc/` |"; done = 1 }
    ' "$src/docs/plan_dag.md"
  }
  with_row "" | commit main "$base"
  rbase=$(g rev-parse HEAD)
  with_row FAIL-gen-a | commit one "$rbase"
  with_row FAIL-gen-b | commit two "$rbase"
  g rebase -q one >"$repo.out" 2>&1
  rc=$?
  m=$(markers)
  if [ $rc -eq 0 ] && [ "$m" = 0 ]; then
    if $plan_tool "$repo/docs/plan_dag.md" >"$repo.fix.out" 2>&1 &&
      $conflicts_tool "$repo/docs/plan_dag.md" >"$repo.lists.out" 2>>"$repo.fix.out" &&
      [ "$(command grep -a -c -E '^\| 0 \| (FAIL-gen-a|FAIL-gen-b) \|' "$repo/docs/plan_dag.md")" = 2 ] &&
      command grep -a -q -E '^\| 0 \| [^|]*(, FAIL-gen-a|FAIL-gen-a, )[^|]* \|' "$repo.lists.out" &&
      command grep -a -q -E '^\| 0 \| [^|]*(, FAIL-gen-b|FAIL-gen-b, )[^|]* \|' "$repo.lists.out"; then
      ok "the real plan: the rebase result passes the plan check with no plan --fix, and the lists name both rows"
    else
      bad "the real plan's rebase result:"
      cat "$repo.fix.out"
    fi
  else
    bad "the real plan with a row on each side (rc $rc, marker lines $m)"
    g rebase --abort >/dev/null 2>&1
  fi
fi

# 10. A branch in flight when TOOL-plan-counts-after-rebase landed: made from the real plan as it
# was before (1d2198af8, the commit that change was made from, with the count sentence and both
# lists), it adds a row and writes the sentence and the lists again as the old plan --fix did.
# Main has taken them out (plan --fix of this checkout) and gained a row of its own. Rebased onto
# main, the branch stops nowhere, and the result has neither the sentence nor the lists, holds
# both rows, and passes the plan check with no plan --fix.
if old_real=$(git -C "$src" show 1d2198af8:docs/plan_dag.md 2>"$repo.out"); then
  row_in() { # $1 the id, $2 the file: the plan with a level-0 row for it, and it in L1.41's needs
    awk -v id="$1" '
      /^\| [0-9]+ \| L1\.41 \|/ { n = split($0, c, "|"); c[n - 2] = c[n - 2] ", " id " "; sub(/  $/, " ", c[n - 2]); s = c[1]; for (i = 2; i <= n; i++) s = s "|" c[i]; $0 = s }
      { print }
      /^\| 0 \| / && !done { print "| 0 | " id " | A test row | S | no | none | `DESIGN.md` |"; done = 1 }
    ' "$2"
  }
  printf '%s\n' "$old_real" >"$repo.old.md"
  cp "$repo.old.md" "$repo.main.md"
  if $plan_tool --fix "$repo.main.md" >"$repo.fix.out" 2>&1; then
    echo "$old_real" | commit main "$base"
    ibase=$(g rev-parse HEAD)
    row_in FAIL-new-b "$repo.main.md" | commit one "$ibase"
    # The branch: its row, then the count sentence one item and one edge up, and its pair and
    # path in the lists, as the old plan --fix wrote them.
    row_in FAIL-old-a "$repo.old.md" | awk '
      !said && match($0, /It has [0-9]+ items, [0-9]+ edges/) {
        split(substr($0, RSTART, RLENGTH), w, " ")
        $0 = substr($0, 1, RSTART - 1) "It has " w[3] + 1 " items, " w[5] + 1 " edges" substr($0, RSTART + RLENGTH); said = 1
      }
      { print }
      $0 == "## File conflicts at the same level" { same = 1 }
      same && $0 == "|---|---|---|" { print "| 0 | FAIL-old-a, SPEC-L3.9-tests | `DESIGN.md` |"; same = 0 }
      $0 == "## File conflicts across levels" { print ""; print "- `DESIGN.md`: level 0: FAIL-old-a"; getline }
    ' | commit two "$ibase"
    g show two:docs/plan_dag.md >"$repo.two.md"
    if [ "$(command grep -a -c -E '^## File conflicts|It has [0-9]+ items|FAIL-old-a' "$repo.two.md")" -lt 6 ]; then
      bad "case 10's branch does not hold the old sentence, both lists and its row and pair: the case tests nothing"
    fi
    g rebase -q one >"$repo.out" 2>&1
    rc=$?
    m=$(markers)
    if [ $rc -eq 0 ] && [ "$m" = 0 ] &&
      ! command grep -a -q -E '^## File conflicts|It has [0-9]+ items, [0-9]+ edges' "$repo/docs/plan_dag.md" &&
      [ "$(command grep -a -c -E '^\| 0 \| (FAIL-old-a|FAIL-new-b) \|' "$repo/docs/plan_dag.md")" = 2 ] &&
      [[ $(needs_of) == *FAIL-new-b*FAIL-old-a* ]] &&
      $plan_tool "$repo/docs/plan_dag.md" >"$repo.fix.out" 2>&1 &&
      $conflicts_tool "$repo/docs/plan_dag.md" >"$repo.lists.out" 2>>"$repo.fix.out" &&
      command grep -a -q -E '^\| 0 \| [^|]*FAIL-old-a[^|]* \|' "$repo.lists.out"; then
      ok "a branch in flight with the old sentence and lists, rebased onto main without them: clean, both dropped, both rows kept"
    else
      bad "the branch in flight with the old sentence and lists (rc $rc, marker lines $m):"
      cat "$repo.fix.out"
      g rebase --abort >/dev/null 2>&1
    fi
    # Negative control: with the stripping turned off (case 8's copy of the driver) it conflicts.
    g config merge.plan-needs.driver "$repo.nostrip.sh %O %A %B %L %S %X %Y"
    commit two "$ibase" <"$repo.two.md"
    g rebase -q one >"$repo.out" 2>&1
    rc=$?
    g rebase --abort >/dev/null 2>&1
    g config merge.plan-needs.driver "tools/plan_merge.sh %O %A %B %L %S %X %Y"
    if [ $rc -ne 0 ]; then ok "negative control: case 10 without the stripping conflicts"; else bad "case 10 merged without the stripping"; fi
  else
    bad "plan --fix of the plan at 1d2198af8 failed:"
    cat "$repo.fix.out"
  fi
else
  bad "no commit 1d2198af8 in $src (a shallow clone?): $(cat "$repo.out")"
fi

echo "failed: $fails"
[ "$fails" -eq 0 ]
