#!/bin/bash
# Tests `tools/fetch_test_deps.sh --stale` (TOOL-test-deps-stale-pins): on a cache that holds what
# an earlier pin and an earlier package version left beside the current ones, it prints each of
# the old ones by its literal path or podman tag, and none of the current ones, and fetches
# nothing. Run from a checkout's root; under 1 s. The cache is build/test-fetch-test-deps/cache
# (XDG_CACHE_HOME), with stubs of podman (it lists the images below) and curl (it fails, so a
# fetch would show); the run makes its files again each time and deletes nothing.
here=$(pwd)/build/test-fetch-test-deps
fails=0
. tools/test_lib.sh || exit 2
pin=$(sed -n 's/^channel = "\(.*\)"$/\1/p' rust-toolchain.toml)
deps=$here/cache/zed-test-deps
mkdir -p "$here/bin" "$deps/rust" "$deps/rust-nightly-2026-11-10" "$deps/rust-$pin" "$deps/podman" \
  "$deps/dl/2026-11-10" "$deps/dl/${pin#nightly-}" "$deps/dl/libc6-arm64-cross_2.42-1_all.deb.unpacked" \
  "$deps/dl/libc6-arm64-cross_2.43-2ubuntu2cross1_all.deb.unpacked"
: >"$deps/dl/rustup-init"
: >"$deps/dl/libc6-arm64-cross_2.42-1_all.deb"
: >"$deps/dl/libc6-arm64-cross_2.43-2ubuntu2cross1_all.deb"
: >"$deps/podman/storage.conf"
printf '#!/bin/bash\n[ "$CONTAINERS_STORAGE_CONF" = %q ] || exit 9\ncase " $* " in *" images "*) printf "%%s\\n" %q %q %q %q "<none>:<none> 3c3c3c3c3c3c" ;; *) exit 8 ;; esac\n' \
  "$deps/podman/storage.conf" "localhost/zed-test-rustup:$pin 1a1a1a1a1a1a" "localhost/zed-test-rustup:nightly-2026-11-10 2b2b2b2b2b2b" \
  "docker.io/library/alpine:3.20 4d4d4d4d4d4d" "docker.io/library/alpine:3.19 5e5e5e5e5e5e" >"$here/bin/podman"
printf '#!/bin/bash\necho "curl stub: no fetch in this test" >&2\nexit 7\n' >"$here/bin/curl"
chmod +x "$here/bin/podman" "$here/bin/curl"

run() { PATH=$here/bin:$PATH XDG_CACHE_HOME=$here/cache tools/fetch_test_deps.sh "$@" 2>&1; }
got=$(run --stale)
rc=$?
podman="CONTAINERS_STORAGE_CONF=$deps/podman/storage.conf podman rmi"
check "--stale exits 0" 0 "$rc"
check "--stale lists the old pin's and old version's files and images, and only those" \
  "Left by an earlier version or pin, unused by this one (delete by these literal paths once no checkout needs them):
  $deps/rust
  $deps/rust-nightly-2026-11-10
  $deps/dl/2026-11-10
  $deps/dl/libc6-arm64-cross_2.42-1_all.deb
  $deps/dl/libc6-arm64-cross_2.42-1_all.deb.unpacked
  $podman localhost/zed-test-rustup:nightly-2026-11-10
  $podman docker.io/library/alpine:3.19
  $podman 3c3c3c3c3c3c   (an untagged image)" "$got"
# Negative control: a cache of only the current pin's files lists nothing.
mkdir -p "$here/clean/zed-test-deps/rust-$pin" "$here/clean/zed-test-deps/dl/${pin#nightly-}"
: >"$here/clean/zed-test-deps/dl/rustup-init"
check "a cache of only current files lists nothing" "Nothing left by an earlier version or pin." \
  "$(PATH=$here/bin:$PATH XDG_CACHE_HOME=$here/clean tools/fetch_test_deps.sh --stale 2>&1)"
check "an unknown argument is refused" "usage: tools/fetch_test_deps.sh [--stale]
2" "$(run --list; echo $?)"
[ "$fails" = 0 ] || { echo "$fails FAILED"; exit 1; }
echo "all passed"
