#!/bin/bash
# Fetches what the full test battery needs and the distribution does not package, into
# ${XDG_CACHE_HOME:-~/.cache}/zed-test-deps. Needs no root. Every file is checked by its
# SHA-256. Run it again after changing a version here. Ubuntu drops superseded packages
# from its pool, so a 404 means the versions below need updating.
#   aarch64/, riscv64/   target sysroots: glibc, libgcc and libstdc++ (the Fedora aarch64
#                        sysroot package has no libgcc, and Fedora has no riscv64 one)
#   rust/                the official rustc with std for both targets; Fedora's rustc
#                        rejects the official std with E0514, so target builds use this
#   bin/                 <target>-cc, clang with the flags for each sysroot
#   podman/              storage for tests, apart from the user's own Podman config
set -euo pipefail
deps=${XDG_CACHE_HOME:-$HOME/.cache}/zed-test-deps
mkdir -p "$deps/dl" "$deps/bin" "$deps/rust"
ubuntu=http://archive.ubuntu.com/ubuntu/pool/main
rust=https://static.rust-lang.org/dist
image=docker.io/library/alpine:3.20

fetch() { # url sha256
  file=$deps/dl/$(basename "$1")
  [ -e "$file" ] || curl -fsSL -m 300 -o "$file" "$1"
  echo "$2  $file" | sha256sum -c --quiet -
}
deb() { # sysroot-dir path sha256
  fetch "$ubuntu/$2" "$3"
  name=$(basename "$2")
  unpack=$deps/dl/$name.unpacked
  mkdir -p "$unpack" "$deps/$1"
  (pushd "$unpack" >/dev/null && ar x "$deps/dl/$name" && tar xf data.tar.* -C "$deps/$1")
}
component() { # name sha256: a component of the official toolchain
  fetch "$rust/$1.tar.xz" "$2"
  tar xf "$deps/dl/$1.tar.xz" -C "$deps/dl"
}

g=g/gcc-15-cross
c=c/cross-toolchain-base
deb riscv64 $c/libc6-riscv64-cross_2.43-2ubuntu2cross1_all.deb ede35a119f1cdba5b2d4093ea4a64801b137e380c9adc9963b04c7b6fe2ae2c5
deb riscv64 $c/libc6-dev-riscv64-cross_2.43-2ubuntu2cross1_all.deb 134df7386b22367c1b59019c0b44ef97043cdfe14e28de84e43a3840852a0f24
deb riscv64 $c/linux-libc-dev-riscv64-cross_7.3.0-5.5cross2_all.deb 1bf5e00d21d1f1e9d19b70e4bb46dde8182e93a7ff88c23fe8357bd5109e8664
deb riscv64 $g/libgcc-s1-riscv64-cross_15.2.0-4ubuntu4cross1_all.deb 03c7786677ef2e2f515688891d2392a3fa20cf8c66f4e8c2326f9e218912f01a
deb riscv64 $g/libgcc-15-dev-riscv64-cross_15.2.0-4ubuntu4cross1_all.deb bdd893af34789141d3bb112748e495f627dae98daa363086e3ca7b7b7044180b
deb riscv64 $g/libstdc++6-riscv64-cross_15.2.0-4ubuntu4cross1_all.deb 8b5508e53d265dd50e9628bd44e58a27a5f9d3075cd5ec9fba977d3011ef8238
deb riscv64 $g/libstdc++-15-dev-riscv64-cross_15.2.0-4ubuntu4cross1_all.deb 0cedd8fa4c612fef716403d34612f686833c6fcc470a4a24ca4b2e1f9bdb40fa
deb aarch64 $c/libc6-arm64-cross_2.43-2ubuntu2cross1_all.deb 43dc16e207bfc1423088240c8ce7b6387acc48a21057b998d8f7bb95dca20253
deb aarch64 $c/libc6-dev-arm64-cross_2.43-2ubuntu2cross1_all.deb 5057ab46f4bf3f4e2aa9f84745f903c26301c541fcce1704bc511aa4aadf7a1a
deb aarch64 $c/linux-libc-dev-arm64-cross_7.3.0-5.5cross2_all.deb 6c84fc899d3496fd547c35f1ad963c3d87925f1a47d45bf05271ce2e76521491
deb aarch64 $g/libgcc-s1-arm64-cross_15.2.0-4ubuntu4cross1_all.deb b6b66d8f2c4e3ea3898d8d29171df507de0ab8728dcf8b9122e0749c3c1b8481
deb aarch64 $g/libgcc-15-dev-arm64-cross_15.2.0-4ubuntu4cross1_all.deb 5b501c0cb925d99c6033a2f9413a6f27873fac524446d103bd3ad5d60a9aec79
deb aarch64 $g/libstdc++6-arm64-cross_15.2.0-4ubuntu4cross1_all.deb ea227e0bab954ec1fcbd9012e5a3487d2d344ae1aebb91c7a92db98646be2e53
deb aarch64 $g/libstdc++-15-dev-arm64-cross_15.2.0-4ubuntu4cross1_all.deb 9bd8daaadc2eb5e9cf564e88fca5d7259c06fd47ea80d38b8f766ab99e611449

host=x86_64-unknown-linux-gnu
component rustc-1.99.1-$host 2ff05ff9c08a90861e7f6e4065b40a8b87463b4576186fd613871c3e37f2091f
component rust-std-1.99.1-$host 109b074225bf5b9ea3820890876bfdf4ed161adbfaf94b2b4b5984c85ee5d958
component rust-std-1.99.1-aarch64-unknown-linux-gnu e25668477083d6a9ddb87b9beb9c00742225f38233ccb4bfba3afa7a07427f52
component rust-std-1.99.1-riscv64gc-unknown-linux-gnu 0fe2aa8294281e16886a101466160ec460ed99e51c8af11e1c76f88f8bd0de6b
cp -a "$deps/dl/rustc-1.99.1-$host/rustc/." "$deps/rust/"
for t in $host aarch64-unknown-linux-gnu riscv64gc-unknown-linux-gnu; do
  cp -a "$deps/dl/rust-std-1.99.1-$t/rust-std-$t/lib/rustlib/$t" "$deps/rust/lib/rustlib/"
done

for a in aarch64 riscv64; do
  cat >"$deps/bin/$a-cc" <<CC
#!/bin/sh
exec clang --target=$a-linux-gnu -fuse-ld=lld --sysroot=$deps/$a --gcc-toolchain=$deps/$a/usr -idirafter $deps/$a/usr/$a-linux-gnu/include "\$@"
CC
  chmod +x "$deps/bin/$a-cc"
done

mkdir -p "$deps/podman/root"
cat >"$deps/podman/storage.conf" <<CONF
[storage]
driver = "overlay"
runroot = "/run/user/$(id -u)/zed-test-podman"
graphroot = "$deps/podman/root"
CONF
CONTAINERS_STORAGE_CONF=$deps/podman/storage.conf podman --log-level=error pull -q $image
touch "$deps/done"
echo "$deps ready"
