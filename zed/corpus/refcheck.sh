#!/bin/sh
# Regenerate nothing: run each ref/NN.py on NN-*.in and compare with NN-*.out.
# Usage: refcheck.sh [--write]   (--write writes the .out files instead)
here=$(dirname "$0")
status=0
for inp in "$here"/[0-9][0-9]-*.in; do
  base=${inp%.in}
  nn=$(basename "$base" | cut -c1-2)
  if [ "$1" = "--write" ]; then
    python3 -B "$here/ref/$nn.py" "$inp" > "$base.out" || { echo "$nn ref FAILED"; status=1; }
  elif python3 -B "$here/ref/$nn.py" "$inp" | cmp -s - "$base.out"; then
    echo "$nn ok"
  else
    echo "$nn DIFFERS"; status=1
  fi
done
exit $status
