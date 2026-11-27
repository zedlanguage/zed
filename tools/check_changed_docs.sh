#!/bin/bash
# Checks the documentation of each package of the workspace whose documented sources gain or lose
# a `///` or `//!` line since this checkout left origin/main: committed, staged or not, or in a new
# file git does not track yet; and of each package with a doc line that links the name of an item
# the change renames, deletes, makes less visible or puts behind a cfg (DOC-renamed-links), though
# no doc line changes. Usage, from a checkout's root (in a worktree through zrun):
#   tools/check_changed_docs.sh [<log file> | --changes]
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
#
# A copy with no git history, as a Colab VM's (FAIL-merge-check-doc-skipped-on-vm: the job's copy
# is a tar of the tracked and untracked files, with no `.git`), is checked from the changes this
# script finds where the history is: `tools/check_changed_docs.sh --changes` prints them there and
# checks nothing (a line `base <hash>`, a line `changed <file>` for each file whose doc lines
# change, and a line `name <name> <scope file> <file>` for each name a link may have lost, all
# tab-separated; nothing when there is no origin/main), and the check run with ZED_DOC_CHANGES
# naming a file of those lines reads them in place of git's diff and searches the copy's files
# with `git grep --no-index --exclude-standard`, which needs no repository. tools/farm_run.sh
# --commands sends them so with each command.
mode=check
[ "${1-}" != --changes ] || mode=changes
log=build/test-logs/doc-changed.log
[ "$mode" = changes ] || log=${1:-$log}
[ "$mode" = changes ] || mkdir -p "$(dirname "$log")"
if [ -n "${ZED_DOC_CHANGES-}" ]; then
  [ -f "$ZED_DOC_CHANGES" ] && grep -q -P '^base\t' "$ZED_DOC_CHANGES" || {
    echo "check_changed_docs: ZED_DOC_CHANGES '$ZED_DOC_CHANGES' is not a file of changes with a base line"
    exit 2
  }
  # A farm_run.sh run inside a job's command passes the changes on as it got them.
  [ "$mode" = check ] || { cat "$ZED_DOC_CHANGES"; exit; }
  changed=$(awk -F '\t' '$1 == "changed" { print $2 }' "$ZED_DOC_CHANGES" | sort -u)
  names=$(awk -F '\t' '$1 == "name" { print $2 FS $3 FS $4 }' "$ZED_DOC_CHANGES" | sort)
  where=(--no-index --exclude-standard)
else # Up to the `fi` after `--changes` prints them: the changes from git.
if ! base=$(git merge-base HEAD origin/main 2>/dev/null); then
  [ "$mode" = changes ] && exit 0
  # With nothing to compare with, the check cannot run, and an exit 0 read as a pass: the
  # snapshot of a Colab job has no origin/main, and every run_tests.sh of a farm share printed
  # that the check was skipped and passed (MERGECHECK-doc-check-skipped-without-origin). It
  # passes only when ZED_DOC_CHECKED names the run that did the check: tools/farm_run.sh runs it
  # where the history is, or its caller did (tools/merge_check.sh), and gives that to its shares.
  if [ -n "${ZED_DOC_CHECKED-}" ]; then
    echo "The doc check of changed packages is not run again here (no origin/main): it ran in" \
      "$ZED_DOC_CHECKED."
    exit 0
  fi
  echo "DOC CHECK FAILED: this checkout has no origin/main to compare with, so the doc check of" \
    "changed packages cannot run. Run it in a checkout with origin/main, give it the changes" \
    "\`tools/check_changed_docs.sh --changes\` prints there in a file named by ZED_DOC_CHANGES," \
    "or name the run that did the check in ZED_DOC_CHECKED."
  exit 1
fi
where=(--untracked)
# One pass over the diff of the working tree from the point where this branch left origin/main (the
# commits of the branch and every change not yet committed), with three lines of context so that
# the item under a changed attribute is in the hunk. It prints one tab-separated line per fact:
#   D <file>               a doc line added or removed in <file>;
#   R <file> <vis> <name>  an item, field, variant or `pub use` name declared on a removed line,
#                          with its visibility (`pub`, `pub(crate)`, ..., `private` for a bare item
#                          at column 0, `variant`, or empty);
#   A <file> <vis> <name>  the same on an added line;
#   N <name> <file>        an item under an added `#[cfg]` or `#[cfg_attr]` line, or the module of
#                          an added `#![cfg]` line, in <file> (a removed cfg line only widens where
#                          its item exists, and a changed one shows as removed and added).
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
          print "N\t" name "\t" file; next
        }
        if (s ~ /^[ \t]*#\[cfg(_attr)?[ \t]*\(/) { if (sign == "+") pending = 1; next }
        k = declared(s)
        for (i = 1; i <= k; i++) print (sign == "-" ? "R" : "A") "\t" file "\t" V "\t" N[i]
      }
      # The first item after an added cfg line, on an added or unchanged line.
      if (pending && sign != "-" && s !~ /^[ \t]*(#|\/\/)/) {
        k = declared(s)
        for (i = 1; i <= k; i++) print "N\t" N[i] "\t" file
        pending = ""
      }
    }
  ')
changed=$(awk -F '\t' '$1 == "D" { print $2 }' <<<"$facts" | sort -u)
# The names a link may have lost, as lines `<name> <scope file> <file>`: each declared on a removed
# line and not declared again in the same file with the same visibility (a changed signature or
# body keeps its links), and each under an added cfg line; <file> is the file that declared it, and
# <scope file> is that file again for a private name and empty for the rest.
names=$(awk -F '\t' '
  $1 == "R" { removed[$2 FS $3 FS $4] = 1 }
  $1 == "A" { added[$2 FS $3 FS $4] = 1 }
  $1 == "N" { lost[$2 FS FS $3] = 1 }
  END {
    for (k in removed) if (!(k in added)) {
      split(k, f, FS); lost[f[3] FS (f[2] == "private" ? f[1] : "") FS f[1]] = 1
    }
    for (n in lost) print n
  }' <<<"$facts" | sort)
# New files git does not track yet, not ignored, with a doc line.
untracked=$(git ls-files --others --exclude-standard -z -- '*.rs' |
  xargs -0 -r grep -lE '^[ \t]*//[/!]')
changed=$(printf '%s\n%s\n' "$changed" "$untracked" | sed '/^$/d' | sort -u)
if [ "$mode" = changes ]; then
  printf 'base\t%s\n' "$base"
  [ -z "$changed" ] || awk '{ print "changed\t" $0 }' <<<"$changed"
  [ -z "$names" ] || awk '{ print "name\t" $0 }' <<<"$names"
  exit 0
fi
fi # ZED_DOC_CHANGES
# The files, tracked or new and not ignored, with a doc line whose link names one of those names:
# a word of a `[...]` span whose text is a path, of the `(...)` target after a span, or of a
# reference definition `[...]: target`, each as a line `<file> <declaring files>`. Their packages
# are documented as if their doc lines had changed, when they can see a declaring file's package
# (below, at `can_link`).
#
# Complexity tradeoff: a renamed, deleted or privatized item, or one put behind a cfg, breaks only
# the docs that link it, so only their packages are documented. The naive rule, documenting the
# package of every changed file and every package that depends on it, costs no scan but builds
# documentation on almost every run (two builds of up to about 15 s per package, and zedc-base
# reaches most of the workspace), against the author's rule of no doc build unless docs change
# (2026-11-10). Used: one awk pass over the diff (linear in the diff) and, only when a name was
# lost, one `git grep` of the doc lines that hold a `[` (linear in the sources) and one awk pass
# over them that looks each word of a link up in a hash of the names (linear in those lines plus
# the names; a private name lost in k files is checked against its k scopes). A `git grep -w -F -f`
# of the names themselves costs about (names x sources): 33 s for the 250 names a first version
# found in commit 2016e39f6. Measured on commits of main
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
# item linked from a module brought in with `#[path]`, and any item of a file outside a documented
# target's source directory that such a target brings in with `#[path]`; and a new item that makes
# an existing link ambiguous. `tools/run_tests.sh --doc`, which documents the whole workspace, finds those.
linking=
if [ -n "$names" ]; then
  linking=$(git grep -I -n -E "${where[@]}" '^[[:space:]]*(//[/!]|#!?\[doc).*\[' -- '*.rs' |
    awk -v names="$names" '
      # lost[name] is 1 for a name any file may link; scope[name] lists, for a private one, the
      # file it was declared in and the directory of the modules under it (the files that alone
      # can name it): src/a.rs gives src/a.rs and src/a/, src/a/mod.rs and src/lib.rs their
      # directories.
      # lost[name] also lists the files that declared it, each after a space.
      BEGIN {
        k = split(names, w, "\n")
        for (i = 1; i <= k; i++) {
          split(w[i], f, "\t")
          if (f[2] == "") { lost[f[1]] = lost[f[1]] " " f[3]; continue }
          d = f[2]
          if (d ~ /(^|\/)(mod|lib|main)\.rs$/) sub(/[^\/]*$/, "", d); else sub(/\.rs$/, "/", d)
          scope[f[1]] = scope[f[1]] " " f[2] " " d
        }
      }
      # The files that declared the lost names n that file p may link, each after a space, or ""
      # for none. A private name is declared in its scope file, the first of each pair of scope.
      function links_lost(n, p, k, i, s, out) {
        out = (n in lost) ? lost[n] : ""
        if (!(n in scope)) return out
        k = split(scope[n], s, " ")
        for (i = 1; i < k; i += 2)
          if (p == s[i] || (s[i + 1] ~ /\/$/ && index(p, s[i + 1]) == 1)) out = out " " s[i]
        return out
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
        found = ""
        for (i = 1; i <= k; i++) found = found links_lost(w[i], path)
        if (found != "") print path "\t" found
      }' | sort -u)
fi
[ -n "$changed$linking" ] || exit 0
# The source directory of each target cargo doc documents, a library or a command, and its
# package. A test, bench, example or build script is not documented; a file under its directory
# alone belongs to no documented target (tests/steps/... in zed-tests).
root=$(pwd -P)
metadata=$(cargo metadata --no-deps --format-version 1) || exit 1
declare -A package_of
while read -r package kind dir; do
  case $kind in
    test | bench | example | custom-build) continue ;;
  esac
  dir=${dir#"$root"/}
  [ -n "${package_of[$dir]}" ] || package_of[$dir]=$package
done < <(printf '%s\n' "$metadata" |
  grep -oE '"name":"[^"]*","version":"[^"]*","id"|"kind":\[[^]]*\],"crate_types":\[[^]]*\],"name":"[^"]*","src_path":"[^"]*"' |
  awk -F '"' '
    /"version"/ { package = $4; next }
    { path = $(NF - 1); sub("/[^/]*$", "", path); print package, $4, path }
  ')
# Prints the package of file $1, the nearest directory above it that is a target's source directory,
# or nothing when it is in no documented target.
file_package() {
  local d
  d=$(dirname "$1")
  while [ "$d" != . ] && [ "$d" != / ] && [ -z "${package_of[$d]}" ]; do
    d=$(dirname "$d")
  done
  [ -z "${package_of[$d]}" ] || echo "${package_of[$d]}"
}
# The packages that can see the items of each package: the package itself and every package that
# depends on it, directly or not, by normal dependencies, as `cargo tree -i` prints them (a doc
# link resolves to an item of its own crate or of a crate it depends on, perhaps through a
# re-export; the documented targets, libraries and commands, see no dev- or build-dependency).
declare -A seen_by
# Whether a doc of package $1 can link an item that a file of package $2 declares.
can_link() {
  [ -n "${seen_by[$2]+x}" ] ||
    seen_by[$2]=" $(cargo tree -q --workspace -i "$2" -e normal --prefix none -f '{p}' |
      awk '{ print $1 }' | sort -u | tr '\n' ' ')"
  [[ ${seen_by[$2]} == *" $1 "* ]]
}
# The files that link a lost name and whose package can see a package that declared one; a name
# declared in a file of no documented target (a test, a bench) cannot be linked from any.
#
# Complexity tradeoff: matching by word alone documented, for a name lost in a package no other
# depends on, every package whose docs link a word of that name: on wt/tools4-r3 (2026-11-20),
# names such as `check`, `run_with` and `HEAD` removed from zed-tools and from tests of zed-tests
# documented zedc, zedc-check, zedc-elab, zedc-preimage, zedc-syntax and zed-kernel, 179 s from a
# cold doc cache and 54 s warm, though no doc of theirs can link an item of zed-tools; with this
# rule the check takes 4.7 s there and documents zed-tests and zed-tools, whose doc lines the
# branch changes. Used: one `cargo tree -i` per declaring package (0.57 to 0.65 s each at load 68
# to 77; at most one per package of the workspace, done only when a link matches a lost name) and,
# per matching file and declaring file, one walk up the file's directories and one string test.
if [ -n "$linking" ]; then
  linked=$(while IFS=$'\t' read -r f declarers; do
    q=$(file_package "$f")
    [ -n "$q" ] || continue
    for d in $declarers; do
      p=$(file_package "$d")
      if [ -n "$p" ] && can_link "$q" "$p"; then
        echo "$f"
        break
      fi
    done
  done <<<"$linking")
  changed=$(printf '%s\n%s\n' "$changed" "$linked" | sed '/^$/d' | sort -u)
fi
[ -n "$changed" ] || exit 0
packages=$(while read -r f; do file_package "$f"; done <<<"$changed" | sort -u)
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
# The build with the workspace's features goes to a build directory of its own, the cargo build
# directory with -docfeatures appended (PERF-doc-check-every-run). In the same directory as the
# build alone, the builds of a package were never fresh from one call to the next (b22-tests10 on
# l42, 2026-11-24: four builds of 2 to 3 s each on every call, 7 to 8 s each after 36 calls, for
# two packages): the package and its dependencies have other features in each build, and a doc
# page or a dylib has the same file name whatever its features, so each build replaces what the
# other wrote. With two directories each build finds its own output on the next call (measured
# before and after in the Done cell of PERF-doc-check-every-run in docs/plan_dag.md; test:
# tools/test_check_changed_docs.sh, "a second call writes no doc file"). The cost is a second
# copy of the check data of the documented packages' dependencies, built once.
target_dir=${CARGO_TARGET_DIR:-$(printf '%s\n' "$metadata" | grep -oE '"target_directory":"[^"]*"' | cut -d'"' -f4)}
[ -n "$target_dir" ] || { echo "check_changed_docs: cargo metadata names no target_directory"; exit 2; }
for p in $packages; do
  document "$p" "alone, with its own default features"
  features=$(echo "$workspace_features" | awk -v p="$p" '$1 == p && $NF ~ /^\[/ { f = $NF; gsub(/[][]/, "", f); print f; exit }')
  [ -z "$features" ] ||
    CARGO_TARGET_DIR=${target_dir%/}-docfeatures document "$p" "with the workspace build's features $features" --features "$features"
done
if [ "$failed" != 0 ]; then
  echo "DOC FAILED: documentation builds of changed packages that failed: $failed, their output in $log."
  echo "Every link in a doc comment must name an item that exists in that build, a public item's"
  echo "doc must not link a private one (write the name as code, \`name\`, instead), and an HTML tag"
  echo "must be closed or written as code."
  exit 1
fi
