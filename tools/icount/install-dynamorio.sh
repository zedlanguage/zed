#!/bin/bash
# Installs DynamoRIO 11.3.0 (the release zed_icount.c was written and checked against) at <dir>,
# unless <dir>/bin64/drrun is there already. Usage: tools/icount/install-dynamorio.sh <dir>
# Used by Colab job.sh's VM setup (/home/luke/Work/skills/colab-offload.md) and compare.sh.
# The release is 428,589,887 bytes; the download and unpacking took about 20 s on a Colab VM.
dir=${1-}
[[ $dir == /?* ]] && [ "$dir" != / ] || { echo "usage: $0 <absolute dir>" >&2; exit 2; }
[ -x "$dir/bin64/drrun" ] && exit 0
url=https://github.com/DynamoRIO/dynamorio/releases/download/release_11.3.0-1/DynamoRIO-Linux-11.3.0.tar.gz
tmp=$(mktemp -d) || exit 1
curl -sSfL -o "$tmp/dr.tgz" "$url" || { echo "download of $url failed" >&2; exit 1; }
mkdir -p "$dir" || exit 1
tar xzf "$tmp/dr.tgz" -C "$dir" --strip-components=1 || { echo "unpacking DynamoRIO failed" >&2; exit 1; }
: > "$tmp/dr.tgz"
[ -x "$dir/bin64/drrun" ] || { echo "no $dir/bin64/drrun after unpacking" >&2; exit 1; }
