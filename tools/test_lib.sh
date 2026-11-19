# Helpers shared by the shell tests (tools/test_*.sh and /home/luke/Work/wt/test-*.sh), sourced.
# Each test counts its failed checks in $fails and exits non-zero when it is not 0.

# check <what> <expected> <got>: prints "ok: <what>", or "FAILED: <what>" and the whole diff of
# expected against got (never cut: the line that differs may be anywhere), and counts the failure.
check() {
  if [ "$2" = "$3" ]; then
    echo "ok: $1"
  else
    echo "FAILED: $1"
    diff <(echo "$2") <(echo "$3")
    fails=$((fails + 1))
  fi
}

# gitc <git arguments>: git with a fixed author and committer, for toy repositories that have no
# user configured.
gitc() { git -c user.name=t -c user.email=t@localhost "$@"; }

# change <dir> <file> <line> [message]: in the repository <dir>, appends <line> to <file> (made if
# missing) and commits it, with the message "<file>: <line>" unless one is given.
change() {
  echo "$3" >>"$1/$2"
  git -C "$1" add -A
  gitc -C "$1" commit -q -m "${4:-$2: $3}"
}

# landed_by <dir> <file> <line>: change, then pushes it to the main of <dir>'s origin, as another
# agent's landing would.
landed_by() {
  change "$1" "$2" "$3"
  git -C "$1" push -q origin HEAD:main
}

# hook <dir> <script>: installs in the repository <dir> a pre-push hook that runs the executable
# <script> the first time a push starts, if it exists: main moves between the rebase and the push.
hook() {
  printf '#!/bin/bash\nunset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE\nif [ -x %q ] && [ ! -e %q ]; then : >%q; %q; fi\nexit 0\n' \
    "$2" "$2.ran" "$2.ran" "$2" >"$1/.git/hooks/pre-push"
  chmod +x "$1/.git/hooks/pre-push"
}
