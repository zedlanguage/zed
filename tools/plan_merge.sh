#!/bin/bash
# The git merge driver for docs/plan_dag.md (TOOL-plan-l141-needs-merge). Git runs it, for a file
# that both sides changed, as
#   tools/plan_merge.sh %O %A %B %L %S %X %Y
# (base, ours, theirs, conflict-marker size, and the labels of the three versions) from the top of
# the worktree, and reads the result from %A: exit 0 merged cleanly, exit 1 conflicts remain.
#
# Why: the needs cell of L1.41 is one line of about 22,000 characters to which every agent that
# files a row adds an id, and the count sentence the first paragraph held ("It has N items, ...")
# changed with every row added (44 of the 80 plan commits before 27df7e6f8 changed it, 24 changed
# L1.41); so two branches that each filed a row conflicted on both lines, and the rebase in
# /home/luke/Work/wt/merge-push.sh failed (need-site2 took 6 tries, zip-count 4).
#
# What it does. First the count sentence ("It has N items, E edges and L levels (0 to M).", and one
# space after it) and the two sections "## File conflicts at the same level" and "## File
# conflicts across levels" (up to the next `## ` heading) are taken out of all three versions,
# the same text `plan --fix` takes out (TOOL-plan-counts-after-rebase, 2026-11-19; `sentence` and
# `sections` in crates/zed-tools/src/plan.rs). Both followed from the whole table, so a rebase
# left them stale even where every row merged cleanly, and each landing needed a commit of
# `plan --fix` output; `plan` and `conflicts` now print them instead. Taking them out of the base
# and of both sides also lets a branch made before that change rebase onto a main without them.
# The three versions are written as blobs (`git hash-object -w`) and merged by object id, since
# git merge-file reads a pipe as an empty file; the blobs are loose objects no ref holds, which
# `git gc` prunes.
# Then git's own three-way merge, `git merge-file --diff3`. Then each conflict that
# merge leaves (a hunk: ours, base and theirs, each some lines) is resolved
#  - when every line of all three sides is a row of the plan table and no side holds an id twice
#    (as when both sides append rows at the end of the table, or one appends a row right after
#    a row both changed): by id. Ours' rows in their order, each merged with the base's and
#    theirs' rows of its id by rules 1 and 2 below (a row one side deleted is dropped if the
#    other left it as in the base); then the rows theirs added that ours does not hold, in
#    theirs' order. The plan tool reads rows in any order, so placing theirs' new rows after
#    ours changes nothing it computes. Any other difference (a row deleted on one side and
#    changed on the other, one id added on both sides with different text) leaves the hunk;
#  - otherwise, when its three sides have the same number of lines and every line i is resolved
#    by the first of these rules that applies:
#  1. two of the three sides agree: as git's own merge takes it (both sides equal: that; one side
#     equal to the base: the other side);
#  2. all three are rows of the plan table with the same id that differ only in the level cell
#     (the first) and the needs cell (the second-last; a title may hold a `|`, so the needs cell
#     is counted from the right, as the plan tool reads it): the needs cell is the three-way merge
#     of the two sides' sets of ids, that is, the ids both sides keep, plus the ids either side
#     added, less the ids either side removed (the union when neither side removed one), in ours'
#     order and then the ids only theirs added, in theirs' order; `none` when empty. The level is
#     the side that changed it, or the higher of the two when both did.
# Any other conflict is left as git's merge-file leaves it, markers and all (in the diff3 style
# this machine's git is set to), and the script exits 1. Rule 2 and a row added on each side can
# leave levels that do not match the merged table: the plan check of m0_03 then fails, naming
# them, and `plan --fix` sets them.
# The task named the union of the two sides' ids. A plain union would bring back an id that one
# side removed on purpose; the three-way set merge keeps both sides' intent and equals the union
# whenever neither side removed an id.
#
# Cost: one pass of awk over each version, git merge-file, then one pass of awk over its output,
# each conflicting row's ids put in an associative array per side: O(length of the three files),
# expected.
#
# Left as a conflict, besides any other change to the same line on both sides: a hunk that mixes
# rows with other lines and whose sides differ in line count (say a row appended on both sides
# right next to the table's closing blank line and a prose change after it).
#
# Setup, once (done 2026-11-17 by tools1): the attribute is declared in .gitattributes, and the
# driver is defined in the git config shared by every worktree of the repository:
#   git -C /home/luke/Work/zed-impl config merge.plan-needs.name "plan_dag.md: needs cells and counts"
#   git -C /home/luke/Work/zed-impl config merge.plan-needs.driver "tools/plan_merge.sh %O %A %B %L %S %X %Y"
# A clone without that config merges the file with git's built-in text merge, as before.
# Undo: git -C /home/luke/Work/zed-impl config --remove-section merge.plan-needs
# Test: tools/test_plan_merge.sh.
base=$1 ours=$2 theirs=$3 size=${4:-7}
# The file $1 without the count sentence and the two conflict sections, as `plan --fix` takes them
# out: the sentence only at the first "It has " of the file and only when it is whole; the
# sections only when both headings are there, each a line of its own, the cross-level one after
# the same-level one.
strip() {
  awk '
    { L[++n] = $0 }
    END {
      for (i = 1; i <= n; i++) if (L[i] == "## File conflicts at the same level") { s = i; break }
      for (i = s + 1; s && i <= n; i++) if (L[i] == "## File conflicts across levels") { c = i; break }
      e = n + 1
      for (i = c + 1; c && i <= n; i++) if (index(L[i], "## ") == 1) { e = i; break }
      if (!c) s = 0
      for (i = 1; i <= n; i++) {
        if (!found && (k = index(L[i], "It has "))) {
          found = 1
          r = substr(L[i], k)
          if (match(r, /^It has [0-9]+ items, [0-9]+ edges and [0-9]+ levels \(0 to [0-9]+\)\. ?/))
            L[i] = substr(L[i], 1, k - 1) substr(r, RLENGTH + 1)
        }
        if (!s || i < s || i >= e) print L[i]
      }
    }' "$1"
}
set -o pipefail
blob_o=$(strip "$base" | git hash-object -w --stdin) &&
  blob_a=$(strip "$ours" | git hash-object -w --stdin) &&
  blob_b=$(strip "$theirs" | git hash-object -w --stdin) || {
  echo "plan_merge.sh: could not store the three versions of $ours as blobs" >&2
  exit 2
}
# The merged text, then a last line with the exit codes of git merge-file (the number of
# conflicts, 255 on error) and of awk (the number of conflicts left, at most 1), held in a
# variable so that no temporary file is made.
res=$(
  git merge-file -p --diff3 --marker-size="$size" -L "${6:-ours}" -L "${5:-base}" -L "${7:-theirs}" \
    --object-id "$blob_a" "$blob_o" "$blob_b" |
    awk -v size="$size" '
    function marker(c,   s, i) { s = ""; for (i = 0; i < size; i++) s = s c; return s }
    BEGIN { m_open = marker("<"); m_base = marker("|"); m_sep = marker("="); m_close = marker(">"); left = 0 }
    # The cells of a table row, split at "|": c[2] the level, c[3] the id, c[n-2] the needs and
    # c[n-1] the paths (c[1] and c[n] are empty); the number of cells, or 0 for any other line.
    function cells(l, c,   n) {
      if (l !~ /^\| *[0-9]+ *\| /) return 0
      n = split(l, c, "|")
      return n >= 8 ? n : 0
    }
    function trim(s) { gsub(/^ +| +$/, "", s); return s }
    # The ids of a needs cell into list[1..n], in order, and into set; returns n.
    function ids(cell, list, set,   n, i) {
      cell = trim(cell)
      if (cell == "none") return 0
      n = split(cell, list, ",")
      for (i = 1; i <= n; i++) { list[i] = trim(list[i]); set[list[i]] = 1 }
      return n
    }
    # A row without its level and needs cells, to compare.
    function rest(c, n,   s, i) {
      s = c[3]
      for (i = 4; i <= n; i++) if (i != n - 2) s = s "|" c[i]
      return s
    }
    # The merged row of rows o (base), a (ours) and b (theirs) by rule 2, or "" when they differ
    # outside the level and needs cells.
    function row(o, a, b,   co, ca, cb, no, na, nb, lo, la, lb, lv, i, s, out, sep,
                 io, ia, ib, so, sa, sb, ko, ka, kb) {
      no = cells(o, co); na = cells(a, ca); nb = cells(b, cb)
      if (!no || na != no || nb != no) return ""
      if (rest(co, no) != rest(ca, na) || rest(co, no) != rest(cb, nb)) return ""
      lo = trim(co[2]) + 0; la = trim(ca[2]) + 0; lb = trim(cb[2]) + 0
      lv = la == lo ? lb : lb == lo ? la : (la > lb ? la : lb)
      split("", so); split("", sa); split("", sb)
      ko = ids(co[no - 2], io, so); ka = ids(ca[na - 2], ia, sa); kb = ids(cb[nb - 2], ib, sb)
      out = ""; sep = ""
      # Ours, less the ids theirs removed; then the ids theirs added that ours does not hold.
      for (i = 1; i <= ka; i++)
        if (!((ia[i] in so) && !(ia[i] in sb))) { out = out sep ia[i]; sep = ", " }
      for (i = 1; i <= kb; i++)
        if (!(ib[i] in so) && !(ib[i] in sa)) { out = out sep ib[i]; sep = ", "; sa[ib[i]] = 1 }
      if (out == "") out = "none"
      ca[2] = " " lv " "; ca[na - 2] = " " out " "
      s = ca[1]
      for (i = 2; i <= na; i++) s = s "|" ca[i]
      return s
    }
    # One line from its base o, ours a and theirs b by rules 1 and 2, or "\001".
    function one(o, a, b,   r) {
      if (a == b || b == o) return a
      if (a == o) return b
      r = row(o, a, b)
      return r != "" ? r : "\001"
    }
    # The ids of the lines L[1..n] of one side into id[1..n] and at (id to index); 0 when a line
    # is no row or an id is there twice.
    function keys(L, n, id, at,   i, c, k) {
      for (i = 1; i <= n; i++) {
        if (!(k = cells(L[i], c))) return 0
        id[i] = trim(c[3])
        if (id[i] in at) return 0
        at[id[i]] = i
      }
      return 1
    }
    # By id: a hunk whose lines are all rows, each id at most once per side, merged by id: ours
    # rows in their order, each merged with its base and theirs rows by rules 1 and 2 (a row one
    # side deleted is dropped when the other left it as in the base); then the rows only theirs
    # added. Prints it and returns 1, or prints nothing and returns 0.
    function keyed(   ia, io, ib, aa, ao, ab, i, k, r, out, n) {
      split("", aa); split("", ao); split("", ab)
      if (!keys(A, na, ia, aa) || !keys(O, no, io, ao) || !keys(B, nb, ib, ab)) return 0
      n = 0
      for (i = 1; i <= na; i++) {
        k = ia[i]
        if (k in ao) {
          if (k in ab) { r = one(O[ao[k]], A[i], B[ab[k]]); if (r == "\001") return 0 }
          else if (A[i] == O[ao[k]]) continue
          else return 0
        } else if ((k in ab) && B[ab[k]] != A[i]) return 0
        else r = A[i]
        out[++n] = r
      }
      for (i = 1; i <= nb; i++) {
        k = ib[i]
        if (k in aa) continue
        if (k in ao) { if (B[i] == O[ao[k]]) continue; return 0 }
        out[++n] = B[i]
      }
      for (i = 1; i <= n; i++) print out[i]
      return 1
    }
    function flush(   i, res, ok) {
      if (keyed()) return
      ok = na == no && nb == no
      for (i = 1; ok && i <= no; i++) { res[i] = one(O[i], A[i], B[i]); if (res[i] == "\001") ok = 0 }
      if (ok) { for (i = 1; i <= no; i++) print res[i]; return }
      left = 1
      print head; for (i = 1; i <= na; i++) print A[i]
      print basehead; for (i = 1; i <= no; i++) print O[i]
      print m_sep; for (i = 1; i <= nb; i++) print B[i]
      print tail
    }
    state == 0 && index($0, m_open " ") == 1 { state = 1; head = $0; na = no = nb = 0; next }
    state == 1 && index($0, m_base " ") == 1 { state = 2; basehead = $0; next }
    state == 2 && $0 == m_sep { state = 3; next }
    state == 3 && index($0, m_close " ") == 1 { tail = $0; flush(); state = 0; next }
    state == 1 { A[++na] = $0; next }
    state == 2 { O[++no] = $0; next }
    state == 3 { B[++nb] = $0; next }
    { print }
    END { exit left }
  '
  printf '\n@plan_merge@ %s %s' "${PIPESTATUS[@]}"
)
read -r merged left <<<"${res##*$'\n'@plan_merge@ }"
if [ "$merged" -eq 255 ] || [ -z "$left" ]; then
  echo "plan_merge.sh: git merge-file or awk failed on $ours (codes: $merged $left)" >&2
  exit 2
fi
printf '%s' "${res%$'\n'@plan_merge@ *}" >"$ours"
[ "$left" -eq 0 ]
