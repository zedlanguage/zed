#!/bin/bash
# Checks the documentation of each package of the workspace whose documented sources gain or lose
# a `///` or `//!` line since this checkout left origin/main: committed, staged or not, or in a new
# file git does not track yet; and of each package with a doc line that links the name of an item
# the change renames, deletes, makes less visible or puts behind a cfg (DOC-renamed-links), though
# no doc line changes. Usage, from a checkout's root (in a worktree through zrun):
#   tools/check_changed_docs.sh [<log file>]
# tools/run_tests.sh runs it before the tests on every run (DOC-check-at-merge), so a branch that
# changes a doc comment is checked by the run its author makes before merging; a branch that
# changes none builds no documentation (author, 2026-11-10: no doc build unless doc comments
# change). It prints each build it makes and exits 1 if any gives a warning, after printing the
# end of rustdoc's output for each failed build; the output of the failed builds is in the log file
# (build/test-logs/doc-changed.log by default).
#
# Each package is documented twice, with --document-private-items and -D warnings (as
# `tools/run_tests.sh --doc` documents the workspace):
#   - alone (`cargo doc -p <package>`), with the package's own default features, as a build of
#     that package by itself gives it;
#   - with the features the workspace build gives the package, when it gives it any.
# One build is not enough: in DOC-private-links-3 the doc of a private item of zedc-preimage linked
# `path_check`, which exists only with the feature `preimage-ref` that zed-tests turns on, so only
# the first build failed; the public `path_check` linked private items, which only the second build
# documents, so only the second failed. `cargo doc --workspace --exclude <the others>` does not give
# the workspace's features (cargo resolves features for the selected packages only; measured on
# that commit), so the second build names them with --features. It gives the package itself the
# workspace's features, and its dependencies those that the package's own features turn on; a
# dependency's feature that only another package of the workspace turns on is not given, which
# matters only for a link to an item of that dependency that exists only with it.
#
# A change that is not to a doc comment can break a link too: an item renamed, deleted, made
# private or put behind a feature while a doc links it. Such a change is found by the names the
# diff's removed declarations and added cfg lines lose; what that misses is listed at the
# "Complexity tradeoff" comment below, and `tools/run_tests.sh --doc`, which documents the whole
# workspace, finds it.
#
# Cost: one pass over the diff from origin/main, one `git grep` of the doc lines when the diff loses
# a name, and one lookup per directory level of each file found (an associative array from source
# directory to package); the naive search of every target's directory for every file would be
# (files x targets). The doc builds dominate: each documents one package (zedc-preimage, the
# largest, in about 15 s at load 22).
log=${1:-build/test-logs/doc-changed.log}
mkdir -p "$(dirname "$log")"
if ! base=$(git merge-base HEAD origin/main 2>/dev/null); then
  echo "The doc check of changed packages is skipped: this checkout has no origin/main to compare" \
    "with."
  exit 0
fi
# One pass over the diff of the working tree from the point where this branch left origin/main (the
# commits of the branch and every change not yet committed), with three lines of context so that
# the item under a changed attribute is in the hunk. It prints one tab-separated line per fact:
#   D <file>               a doc line added or removed in <file>;
#   R <file> <vis> <name>  an item, field, variant or `pub use` name declared on a removed line,
#                          with its visibility (`pub`, `pub(crate)`, ..., `private` for a bare item
#                          at column 0, `variant`, or empty);
#   A <file> <vis> <name>  the same on an added line;
#   N <name>               an item under an added `#[cfg]` or `#[cfg_attr]` line, or the module of
#                          an added `#![cfg]` line (a removed cfg line only widens where its item
#                          exists, and a changed one shows as removed and added).
# A deleted file is named by its old path, so its package is still found.
facts=$(git diff -U3 --no-color --no-ext-diff --src-prefix=a/ --dst-prefix=b/ "$base" -- '*.rs' |
  awk '
    # The visibility V and name N of the item, field, variant or the names of the `pub use` that
    # line s declares; returns how many names it put in N[1..].
    function declared(s, m, k, i, w, n) {
      if (match(s, /^[ \t]*(pub(\([^)]*\))?[ \t]+)?((const|async|unsafe|default|extern([ \t]+"[^"]*")?)[ \t]+)*(fn|struct|enum|union|trait|type|const|static|mod|macro_rules!)[ \t]+(mut[ \t]+)?([A-Za-z_][A-Za-z0-9_]*)/, m)) {
        V = m[1]; gsub(/[ \t]/, "", V); N[1] = m[8]
        # A bare item at column 0 is private to its module; an indented one may be a trait item,
        # as visible as its trait, and a macro may be exported.
        if (V == "" && s ~ /^[^ \t]/ && m[6] != "macro_rules!") V = "private"
        return 1
      }
      if (match(s, /^[ \t]*(pub(\([^)]*\))?)[ \t]+use[ \t]/, m)) {
        V = m[1]; n = 0; k = split(substr(s, RLENGTH + 1), w, /[^A-Za-z0-9_]+/)
        for (i = 1; i <= k; i++)
          if (w[i] != "" && w[i] !~ /^(as|crate|self|super|Self|[0-9].*)$/) N[++n] = w[i]
        return n
      }
      if (match(s, /^[ \t]*(pub(\([^)]*\))?)[ \t]+([a-z_][A-Za-z0-9_]*)[ \t]*:([^:]|$)/, m)) {
        V = m[1]; N[1] = m[3]; return 1
      }
      # A variant, as rustfmt writes it: `Name,`, `Name(...),` or `Name {`. A link that names
      # None, Some, Ok or Err alone is to the prelude, so a line of those is an expression.
      if (s !~ /=/ && match(s, /^[ \t]*([A-Z][A-Za-z0-9_]*)[ \t]*(\(.*\)[ \t]*,|\{|,)[ \t]*$/, m) &&
          m[1] !~ /^(None|Some|Ok|Err)$/) {
        V = "variant"; N[1] = m[1]; return 1
      }
      return 0
    }
    /^diff --git / { hunk = 0; next }
    !hunk && /^--- a\//    { old = substr($0, 7); next }
    !hunk && /^--- /       { old = ""; next }
    !hunk && /^\+\+\+ b\// { file = substr($0, 7); next }
    !hunk && /^\+\+\+ /    { file = old; next }
    /^@@/ { hunk = 1; pending = ""; next }
    !hunk { next }
    {
      sign = substr($0, 1, 1); s = substr($0, 2)
      if (sign == "-" || sign == "+") {
        if (s ~ /^[ \t]*\/\/[\/!]/) { print "D\t" file; next }
        if (s ~ /^[ \t]*#!\[cfg/) {
          if (sign == "-") next
          # The module the file is: its name, or its directory'"'"'s for mod.rs.
          k = split(file, w, "/"); name = w[k]; sub(/\.rs$/, "", name)
          if (name == "mod" && k > 1) name = w[k - 1]
          print "N\t" name; next
        }
        if (s ~ /^[ \t]*#\[cfg(_attr)?[ \t]*\(/) { if (sign == "+") pending = 1; next }
        k = declared(s)
        for (i = 1; i <= k; i++) print (sign == "-" ? "R" : "A") "\t" file "\t" V "\t" N[i]
      }
      # The first item after an added cfg line, on an added or unchanged line.
      if (pending && sign != "-" && s !~ /^[ \t]*(#|\/\/)/) {
        k = declared(s)
        for (i = 1; i <= k; i++) print "N\t" N[i]
        pending = ""
      }
    }
  ')
changed=$(awk -F '\t' '$1 == "D" { print $2 }' <<<"$facts" | sort -u)
# The names a link may have lost, each with the file a private one was declared in (and empty for
# the rest): each declared on a removed line and not declared again in the same file with the same
# visibility (a changed signature or body keeps its links), and each under an added cfg line.
names=$(awk -F '\t' '
  $1 == "R" { removed[$2 FS $3 FS $4] = 1 }
  $1 == "A" { added[$2 FS $3 FS $4] = 1 }
  $1 == "N" { lost[$2 FS] = 1 }
  END {
    for (k in removed) if (!(k in added)) {
      split(k, f, FS); lost[f[3] FS (f[2] == "private" ? f[1] : "")] = 1
    }
    for (n in lost) print n
  }' <<<"$facts" | sort)
# The files, tracked or new and not ignored, with a doc line whose link names one of those names:
# a word of a `[...]` span whose text is a path, of the `(...)` target after a span, or of a
# reference definition `[...]: target`. Their packages are documented as if their doc lines had
# changed.
#
# Complexity tradeoff: a renamed, deleted, privatized or cfg-gated item breaks only the docs that
# link it, so only their packages are documented. The naive rule, documenting the package of every
# changed file and every package that depends on it, costs no scan but builds documentation on
# almost every run (two builds of up to about 15 s per package, and zedc-base reaches most of the
# workspace), against the author's rule of no doc build unless docs change (2026-11-10). Used: one
# awk pass over the diff (linear in the diff) and, only when a name was lost, one `git grep` of the
# doc lines that hold a `[` (linear in the sources) and one awk pass over them that looks each word
# of a link up in a hash of the names (linear in those lines plus the names; a private name lost in
# k files is checked against its k scopes). A `git grep -w -F -f` of the names themselves costs
# about (names x sources): 33 s for the 250 names of commit 2016e39f6. Measured on commits of main
# against their parents at load 35 to 40, the whole search before the doc builds: 24 to 43 ms
# before this rule, 32 to 38 ms after it on diffs that lose no name, and 270 to 340 ms on diffs
# that do, from 5 names (444 lines) to 249 names (10902 lines). The match is by word, not by
# resolved path, so it over-approximates: a link to another item of the same name documents a
# package for nothing, which costs time and never misses a break. On the last 150 commits of main
# on 2026-11-14 the rule added 4 package documentations to the 46 the doc lines gave, in 3 commits
# that already built one; most of the extra come from helpers inside `mod tests` blocks, which are
# indented and so kept visible everywhere. It misses: a link whose text is split over two lines; a
# name removed from a `pub use` list written over several lines, other than a capitalized one; an
# item made by a macro; a doc written in another file and pulled in with `include_str!`; a private
# item linked from a module brought in with `#[path]`; and a new item that makes an existing link
# ambiguous. `tools/run_tests.sh --doc`, which documents the whole workspace, finds those.
linking=
if [ -n "$names" ]; then
  linking=$(git grep -I -n -E --untracked '^[[:space:]]*(//[/!]|#!?\[doc).*\[' -- '*.rs' |
    awk -v names="$names" '
      # lost[name] is 1 for a name any file may link; scope[name] lists, for a private one, the
      # file it was declared in and the directory of the modules under it (the files that alone
      # can name it): src/a.rs gives src/a.rs and src/a/, src/a/mod.rs and src/lib.rs their
      # directories.
      BEGIN {
        k = split(names, w, "\n")
        for (i = 1; i <= k; i++) {
          split(w[i], f, "\t")
          if (f[2] == "") { lost[f[1]] = 1; continue }
          d = f[2]
          if (d ~ /(^|\/)(mod|lib|main)\.rs$/) sub(/[^\/]*$/, "", d); else sub(/\.rs$/, "/", d)
          scope[f[1]] = scope[f[1]] " " f[2] " " d
        }
      }
      # Whether file p may link name n.
      function links_lost(n, p, k, i, s) {
        if (n in lost) return 1
        if (!(n in scope)) return 0
        k = split(scope[n], s, " ")
        for (i = 1; i <= k; i++) if (p == s[i] || (s[i] ~ /\/$/ && index(p, s[i]) == 1)) return 1
        return 0
      }
      {
        p = index($0, ":"); path = substr($0, 1, p - 1)
        text = substr($0, p + 1); text = substr(text, index(text, ":") + 1)
        if (text !~ /^[ \t]*(\/\/[\/!]|#!?\[doc)/) next
        links = ""; s = text
        # A span with a `(target)` links its target; one without links its text only when that,
        # without backticks, is a path (`[0, sum]` is no link).
        while (match(s, /\[[^]]*\](\([^)]*\))?/)) {
          span = substr(s, RSTART, RLENGTH); s = substr(s, RSTART + RLENGTH)
          p = index(span, "](")
          if (p) { links = links " " substr(span, p + 2); continue }
          span = substr(span, 2, length(span) - 2); gsub(/`/, "", span)
          if (span ~ /^([a-z]+@)?[A-Za-z_][A-Za-z0-9_]*(::[A-Za-z_][A-Za-z0-9_]*)*(\(\)|!)?$/)
            links = links " " span
        }
        # A reference definition: `[text]: target`, the target one word of no spaces.
        if (match(text, /^[ \t]*\/\/[\/!][ \t]*\[[^]]*\]:[ \t]*[^ \t]+[ \t]*$/))
          links = links " " text
        k = split(links, w, /[^A-Za-z0-9_]+/)
        for (i = 1; i <= k; i++) if (links_lost(w[i], path)) { print path; next }
      }' | sort -u)
fi
# New files git does not track yet, not ignored, with a doc line.
untracked=$(git ls-files --others --exclude-standard -z -- '*.rs' |
  xargs -0 -r grep -lE '^[ \t]*//[/!]')
changed=$(printf '%s\n%s\n%s\n' "$changed" "$untracked" "$linking" | sed '/^$/d' | sort -u)
[ -n "$changed" ] || exit 0
# The source directory of each target cargo doc documents, a library or a command, and its
# package. A test, bench, example or build script is not documented; a file under its directory
# alone belongs to no documented target (tests/steps/... in zed-tests).
root=$(pwd -P)
declare -A package_of
while read -r package kind dir; do
  case $kind in
    test | bench | example | custom-build) continue ;;
  esac
  dir=${dir#"$root"/}
  [ -n "${package_of[$dir]}" ] || package_of[$dir]=$package
done < <(cargo metadata --no-deps --format-version 1 |
  grep -oE '"name":"[^"]*","version":"[^"]*","id"|"kind":\[[^]]*\],"crate_types":\[[^]]*\],"name":"[^"]*","src_path":"[^"]*"' |
  awk -F '"' '
    /"version"/ { package = $4; next }
    { path = $(NF - 1); sub("/[^/]*$", "", path); print package, $4, path }
  ')
# Each changed file's package: the nearest directory above it that is a target's source directory.
packages=$(while read -r f; do
  d=$(dirname "$f")
  while [ "$d" != . ] && [ "$d" != / ] && [ -z "${package_of[$d]}" ]; do
    d=$(dirname "$d")
  done
  [ -z "${package_of[$d]}" ] || echo "${package_of[$d]}"
done <<<"$changed" | sort -u)
[ -n "$packages" ] || exit 0
# The features the workspace build gives each package, as cargo tree prints them:
# "<package> v<version> (<path>) [<features>]".
workspace_features=$(cargo tree --workspace -f '{p} [{f}]' --prefix none |
  sed 's/ (\*)$//' | sort -u)
# Documents package $1 with the further cargo arguments $3...; $2 says which build it is. A build
# that fails prints the end of rustdoc's output and is counted; the next build still runs, so one
# run names every package and build that fails.
failed=0
: >"$log"
document() {
  local package=$1 which=$2 output
  shift 2
  echo "Documenting $package ($which), whose doc comments, or items they link, this branch changes."
  if ! output=$(RUSTDOCFLAGS='-D warnings' cargo doc --no-deps --document-private-items \
    -p "$package" "$@" 2>&1); then
    echo "$output" >>"$log"
    echo "$output" | tail -40
    echo "DOC FAILED: $package ($which)."
    failed=$((failed + 1))
  fi
}
for p in $packages; do
  document "$p" "alone, with its own default features"
  features=$(echo "$workspace_features" | awk -v p="$p" '$1 == p && $NF ~ /^\[/ { f = $NF; gsub(/[][]/, "", f); print f; exit }')
  [ -z "$features" ] || document "$p" "with the workspace build's features $features" --features "$features"
done
if [ "$failed" != 0 ]; then
  echo "DOC FAILED: documentation builds of changed packages that failed: $failed, their output in $log."
  echo "Every link in a doc comment must name an item that exists in that build, a public item's"
  echo "doc must not link a private one (write the name as code, \`name\`, instead), and an HTML tag"
  echo "must be closed or written as code."
  exit 1
fi
