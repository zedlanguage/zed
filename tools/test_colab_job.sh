#!/bin/bash
# Tests of /home/luke/Work/wt/colab/job.sh that need no VM: each runs job.sh with a fake `colab`
# first on PATH, which notes that it was called and answers "Session ... not found.", so a job that
# gets past its checks ends at its first call with exit 5 and never reaches a real VM.
# Usage: tools/test_colab_job.sh [<job.sh>]   (default /home/luke/Work/wt/colab/job.sh; a job runs
# it on a copy of job.sh shipped in the worktree, since job.sh is not in this repository).
# Cases (FARM-job-empty-file-list, b22-kernel9, 2026-11-23):
#   empty-source  a worktree with files but no .git, as a `git archive` snapshot is: job.sh stops
#                 with exit 2 and names the empty file list before any call to colab. Before the
#                 fix it packed an empty source, called colab, and the VM's tests all failed with
#                 rustup's "no default is configured".
#   checkout      a git checkout with a tracked file: job.sh gets past the check and calls colab.
# The temporary directory is left in place (it holds a few small files).
set -u
job=${1:-/home/luke/Work/wt/colab/job.sh}
[ -f "$job" ] || { echo "test_colab_job: no job.sh at '$job'"; exit 2; }
t=$(mktemp -d) || { echo "test_colab_job: mktemp failed"; exit 2; }
[[ $t == /?*/?* ]] || { echo "test_colab_job: bad temporary directory '$t'"; exit 2; }
mkdir -p "$t/bin" "$t/snapshot" "$t/checkout" "$t/spec"
cat > "$t/bin/colab" <<'EOF'
#!/bin/bash
touch "$COLAB_MARK"
echo "[colab] Session 'hm1' not found."
exit 1
EOF
chmod +x "$t/bin/colab"
echo '!true' > "$t/tests.txt"
g() { git -C "$1" -c user.name=test -c user.email=test -c init.defaultBranch=main "${@:2}"; }
echo 'x' > "$t/spec/DESIGN.md"
g "$t/spec" init -q && g "$t/spec" add DESIGN.md && g "$t/spec" commit -q -m spec ||
  { echo "test_colab_job: cannot make the spec checkout"; exit 2; }
echo '[workspace]' > "$t/snapshot/Cargo.toml"
echo '[workspace]' > "$t/checkout/Cargo.toml"
g "$t/checkout" init -q && g "$t/checkout" add Cargo.toml ||
  { echo "test_colab_job: cannot make the checkout"; exit 2; }
pass=0 fail=0
ok() { echo "ok $1"; pass=$((pass + 1)); }
bad() { echo "FAILED $1: $2"; fail=$((fail + 1)); }
# run <case> <worktree>: job.sh's exit code in $rc and its output in $o; the fake colab touches
# $t/called-<case> when it is called.
run() {
  o=$(COLAB_MARK="$t/called-$1" PATH="$t/bin:$PATH" timeout 60 \
    bash "$job" hm1 "$2" "$t/out-$1" "$t/tests.txt" "$t/spec" 2>&1)
  rc=$?
}

run empty-source "$t/snapshot"
if [ -e "$t/called-empty-source" ]; then
  bad empty-source "colab was called (rc $rc): $(tail -2 <<<"$o")"
elif [ $rc -ne 2 ] || ! command grep -a -q 'has no files git lists' <<<"$o"; then
  bad empty-source "rc $rc, want 2 and the empty file list named: $(tail -2 <<<"$o")"
else
  ok empty-source
fi

run checkout "$t/checkout"
if [ -e "$t/called-checkout" ] && [ $rc -eq 5 ]; then
  ok checkout
else
  bad checkout "rc $rc, want 5 after a call to the fake colab: $(tail -2 <<<"$o")"
fi

echo "test_colab_job: $pass passed, $fail failed (temporary directory $t)"
[ $fail -eq 0 ]
