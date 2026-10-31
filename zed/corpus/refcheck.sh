#!/bin/sh
# Regenerate nothing: run each ref/NN.dart on NN-*.in and compare with NN-*.out.
# Usage: refcheck.sh [--write]   (--write writes the .out files instead)
# The scripts run in parallel, since most of each one's time is Dart compiling it; the report
# is sorted, so it is the same in every run.
here=$(dirname "$0")
for inp in "$here"/[0-9][0-9]-*.in; do
  base=${inp%.in}
  nn=$(basename "$base" | cut -c1-2)
  if [ "$1" = "--write" ]; then
    { dart "$here/ref/$nn.dart" "$inp" > "$base.out" || echo "$nn ref FAILED"; } &
  else
    { if dart "$here/ref/$nn.dart" "$inp" | cmp -s - "$base.out"; then
        echo "$nn ok"
      else
        echo "$nn DIFFERS"
      fi; } &
  fi
done | sort | awk '{ print } / (DIFFERS|ref FAILED)$/ { bad = 1 } END { exit bad }'
