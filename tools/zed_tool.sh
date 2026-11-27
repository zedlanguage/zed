#!/bin/bash
# Usage: tools/zed_tool.sh <bin> [<arg>...]
# Runs a binary of zed-tools (plan, conflicts, catalog, sync, ...) as
#   cargo run -q --release -p zed-tools --bin <bin> -- <arg>...
# but in a build directory of its own: $ZED_TOOL_TARGET_DIR when set, else the cargo build
# directory with -tools appended (/content/target-tools on a VM, where job.sh sets
# CARGO_TARGET_DIR=/content/target; <checkout>/build/target-tools when CARGO_TARGET_DIR is unset).
# The directory is kept, so a second call is a no-op build.
#
# Why (FARM-bang-plan-target-pd, from b22-band4's d34 to d36 on v5e5, 2026-11-26): after the
# workspace build in /content/target, `cargo run -p zed-tools --bin plan` (and conflicts) exited
# 101 with "cannot satisfy dependencies so `std` only shows up once" in zed-kernel, with static
# std (d35, RUSTFLAGS unset) and with job.sh's -C prefer-dynamic retry in /content/target-pd
# (d34) alike; in a fresh directory, CARGO_TARGET_DIR=/content/t-plan, both exited 0 (d36). The
# workspace build gives the dylibs (zedc, zed-kernel, ...) the union of every package's features,
# and `-p zed-tools` the features zed-tools asks for; a dylib's file name does not change with its
# features (crates/zed-tools/Cargo.toml), so the second build replaces some of the dylibs the
# first built and links against a mix. A directory that only this script builds in holds one
# feature set, so nothing mixes. The cost is one release build of zed-tools and its dependencies
# per directory, paid once per VM (measured in the Done cell of FARM-bang-plan-target-pd in
# docs/plan_dag.md).
set -uo pipefail
bin=${1:?usage: tools/zed_tool.sh <bin> [<arg>...]}
shift
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
dir=${ZED_TOOL_TARGET_DIR:-}
if [ -z "$dir" ]; then
  if [ -n "${CARGO_TARGET_DIR:-}" ]; then dir=${CARGO_TARGET_DIR%/}-tools; else dir=$root/build/target-tools; fi
fi
cd "$root" || exit 2
CARGO_TARGET_DIR=$dir exec cargo run -q --release -p zed-tools --bin "$bin" -- "$@"
