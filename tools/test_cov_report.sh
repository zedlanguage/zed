#!/bin/bash
# Tests tools/cov_report.sh (TOOLS-coverage-region-report). Run from a checkout's root; about 2 s.
# The fixture is build/test-cov-report, a toy repository set up again by each run (its source
# overwritten and committed again, `git init` on the old .git), with one program built by rustc
# with the flags of a coverage run and run once (its profiles added to those of earlier runs,
# which changes no covered or total count), so a run deletes nothing. The base commit has `half`,
# `main` and `unused`; the change adds a branch to `half`, adds `never`, and calls `never` from
# `main` on a path no run takes. So the regions listed are the branch of `half` not taken, all of
# `never`, and the call in `main`; `unused`, never run and not changed, is not listed (the
# negative control), and neither is a region of a changed function that ran.
report=$(pwd)/tools/cov_report.sh
t=$(pwd)/build/test-cov-report
fails=0
. tools/test_lib.sh || exit 2
mkdir -p "$t/crates/toy/src" "$t/prof" "$t/bins" "$t/empty"
git -C "$t" init -q
src=$t/crates/toy/src/main.rs
cat >"$src" <<'EOF'
fn half(x: i32) -> i32 {
    x / 2
}

fn main() {
    let n = std::env::args().count() as i32;
    println!("{}", half(n));
}

fn unused(x: i32) -> i32 {
    x - 1
}
EOF
git -C "$t" add -A
gitc -C "$t" commit -q --allow-empty -m one
base=$(git -C "$t" rev-parse HEAD)
cat >"$src" <<'EOF'
fn half(x: i32) -> i32 {
    if x > 10 {
        x / 2
    } else {
        x
    }
}

fn never(x: i32) -> i32 {
    x + 1
}

fn main() {
    let n = std::env::args().count() as i32;
    println!("{}", half(n));
    if n > 100 {
        println!("{}", never(n));
    }
}

fn unused(x: i32) -> i32 {
    x - 1
}
EOF
rustc -C instrument-coverage -Z coverage-options=branch -A dead_code -o "$t/bins/toy" "$src" || exit 2
# A file that is no instrumented binary is passed over.
printf '#!/bin/sh\n' >"$t/bins/script"
chmod +x "$t/bins/script"
LLVM_PROFILE_FILE=$t/prof/toy-%p.profraw "$t/bins/toy" >/dev/null || exit 2
pushd "$t" >/dev/null || exit 2
got=$("$report" --base "$base" --bins "$t/bins" "$t/prof" 2>&1)
code=$?
popd >/dev/null || exit 2
check "exit 0" 0 "$code"
short=$(git -C "$t" rev-parse --short "$base")
check "the report" "coverage per crate: regions, branches, lines (covered/total)
  crates/toy  regions 11/20 55%  branches 2/4 50%  lines 10/18 55.5%
changed files against $short: regions, branches, lines
  crates/toy/src/main.rs  regions 11/20 55%  branches 2/4 50%  lines 10/18 55.5%
uncovered regions in changed functions
  crates/toy/src/main.rs:3:9-3:14 (function at line 1)
  crates/toy/src/main.rs:9:1-9:24 (function at line 9)
  crates/toy/src/main.rs:10:5-10:10 (function at line 9)
  crates/toy/src/main.rs:11:1-11:2 (function at line 9)
  crates/toy/src/main.rs:17:9-17:17 (function at line 13)
  crates/toy/src/main.rs:17:24-17:32 (function at line 13)" "$got"
# With no change against the base (the second version committed), only the crates are reported.
git -C "$t" add -A
gitc -C "$t" commit -q -m two
pushd "$t" >/dev/null || exit 2
got=$("$report" --base HEAD --bins "$t/bins" "$t/prof" 2>&1 | tail -2)
popd >/dev/null || exit 2
check "a base with no change" "changed files against $(git -C "$t" rev-parse --short HEAD): regions, branches, lines
  none" "$got"
# No profiles: exit 2 with the reason.
pushd "$t" >/dev/null || exit 2
got=$("$report" --base "$base" --bins "$t/bins" "$t/empty" 2>&1)
code=$?
popd >/dev/null || exit 2
check "no profiles" "2 cov_report: no .profraw files in $t/empty" "$code $got"
[ "$fails" = 0 ] && echo "test_cov_report: all passed" || echo "test_cov_report: $fails FAILED"
