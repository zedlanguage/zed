#!/bin/bash
# Fails when a Rust file of the workspace is not as rustfmt writes it: `cargo fmt --all --check`,
# the check .github/workflows/ci.yml runs. CI is off on zed-impl, and from then until
# FMT-main-eval-tag (2026-11-28) nothing ran it, so crates/zed-kernel/src/eval.rs and
# tests/steps/l08_02_remaps/tag.rs reached main unformatted. tools/merge_check.sh runs it on every
# check (step 0d). Usage, from a checkout's root:
#   tools/check_fmt.sh
# First it checks a package of its own, build/check-fmt-control (its two files written on each
# run, never deleted; its own [workspace] keeps it out of the checkout's workspace): its lib.rs as
# rustfmt writes it must pass, and written on one line must fail and be listed. So a check that
# cannot fail, as with no rustfmt installed or no file reached, fails here instead of passing every
# branch. Exit 0 when every file is formatted; 1 when one is not, with the files and the repair
# printed; 2 when the control did not pass and fail as it should.
# Cost: 11.3 s over the workspace (2026-11-28, 2,081 tracked .rs files, rustfmt only, no build),
# and 0.05 s for each run of the control. rustfmt reads each crate from its root, so a file
# no crate reaches is not checked, as in CI. Running rustfmt on every tracked file instead took
# 23.2 s, since a file is formatted again for each module path that reaches it, and found the same
# two files.
ctl=build/check-fmt-control
mkdir -p "$ctl/src" || exit 2
printf '[package]\nname = "check-fmt-control"\nversion = "0.0.0"\nedition = "2024"\n\n[workspace]\n' \
  >"$ctl/Cargo.toml" || exit 2
# control <lib.rs text> <pass | fail>: checks the control package with lib.rs set to the text.
control() {
  local out rc
  printf '%s' "$1" >"$ctl/src/lib.rs" || exit 2
  out=$(cargo fmt --manifest-path "$ctl/Cargo.toml" --check -- -l 2>&1)
  rc=$?
  if [ "$2" = pass ] && [ "$rc" = 0 ] && [ -z "$out" ]; then return 0; fi
  if [ "$2" = fail ] && [ "$rc" = 1 ] && [[ $out == *"$ctl/src/lib.rs"* ]]; then return 0; fi
  printf '%s\n' "$out"
  echo "check_fmt: the control file $ctl/src/lib.rs should $2 \`cargo fmt --check\`, and it gave rc=$rc (output above); this check cannot be trusted until it does" >&2
  exit 2
}
control $'pub fn f() -> i32 {\n    1\n}\n' pass
control $'pub fn f()->i32{1}\n' fail
out=$(cargo fmt --all --check -- -l 2>&1)
rc=$?
[ "$rc" = 0 ] && [ -z "$out" ] && exit 0
printf '%s\n' "$out" | sed "s|^$(pwd -P)/||"
echo "check_fmt: these files are not as rustfmt writes them; run \`cargo fmt --all\` and commit the result" >&2
exit 1
