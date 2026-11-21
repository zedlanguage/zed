//! The tools the battery relies on, each doing the job a later step needs: a C and a Rust
//! program built for each target, run under the emulator, and stopped at a breakpoint in the
//! debugger; two containers that reach each other until one is killed; a network namespace
//! whose link delays packets.

use std::env;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

const C_PROGRAM: &str = "#include <stdio.h>\n#include <pthread.h>\n\
static void *work(void *a) { *(int *)a = 42; return 0; }\n\
int main(void) { int r = 0; pthread_t t; pthread_create(&t, 0, work, &r); pthread_join(t, 0); \
printf(\"answer %d\\n\", r); return 0; }\n";
const RUST_PROGRAM: &str = "fn main() { let h = std::thread::spawn(|| (1..=10u64).sum::<u64>()); \
println!(\"sum {}\", h.join().unwrap()); }";
const IMAGE: &str = "docker.io/library/alpine:3.20";

fn deps() -> PathBuf {
    PathBuf::from(env::var("ZED_TEST_DEPS").expect("run through tools/run_tests.sh --full"))
}

fn scratch(name: &str) -> PathBuf {
    zed_tests::step_helpers::scratch_dir(format!("zed-full-{name}"))
}

fn run(program: &str, args: &[&str]) -> Output {
    Command::new(program)
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("{program}: {e}"))
}

fn stdout(program: &str, args: &[&str]) -> String {
    let out = run(program, args);
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "{program} {args:?} failed: {err}");
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// The emulator, waiting for the debugger on a port, and the debugger, run together in a network
/// namespace of their own (FLAKY-full-s00-01-tools-load). On the shared loopback the port was
/// fixed, 41301 or 41302, so two runs of this piece at once (two worktrees' merge checks) took
/// one port: the second emulator failed to bind it and its debugger reached the first's, which
/// reset it ("Connection reset by peer", once in 25 runs at load 129, 2026-11-17). The debugger
/// retries a refused connection until the emulator listens, with no time limit of its own
/// (`connect-timeout unlimited`; the default gave up after 15 s), so how soon the emulator
/// starts does not matter either.
const GDB_SCRIPT: &str = r#"
ip link set lo up
"qemu-$1" -L "$2" -g 1234 "$3" >/dev/null &
gdb -q -batch -ex 'set tcp connect-timeout unlimited' -ex "set sysroot $2" \
  -ex 'target remote 127.0.0.1:1234' -ex 'break work' -ex continue -ex bt -ex kill "$3"
status=$?
wait
exit $status
"#;

fn target_runs_c_and_stops_in_gdb(arch: &str) {
    let dir = scratch(arch);
    let (src, bin) = (dir.join("p.c"), dir.join("p"));
    std::fs::write(&src, C_PROGRAM).unwrap();
    let (src, bin) = (src.to_str().unwrap(), bin.to_str().unwrap());
    let cc = deps().join("bin").join(format!("{arch}-cc"));
    stdout(cc.to_str().unwrap(), &["-g", src, "-o", bin]);
    let libs = deps().join(arch).join(format!("usr/{arch}-linux-gnu"));
    let libs = libs.to_str().unwrap();
    let qemu = format!("qemu-{arch}");
    assert_eq!(stdout(&qemu, &["-L", libs, bin]), "answer 42\n");
    // The emulator of the other target must refuse this binary, or the run above shows nothing.
    let other = if arch == "aarch64" {
        "qemu-riscv64"
    } else {
        "qemu-aarch64"
    };
    assert!(!run(other, &["-L", libs, bin]).status.success());

    let gdb = stdout(
        "unshare",
        &["-Urn", "sh", "-c", GDB_SCRIPT, "sh", arch, libs, bin],
    );
    assert!(
        gdb.contains("Breakpoint 1, work"),
        "no stop at the breakpoint: {gdb}"
    );
}

#[test]
fn aarch64_c_runs_under_qemu_and_gdb() {
    target_runs_c_and_stops_in_gdb("aarch64");
}

#[test]
fn riscv64_c_runs_under_qemu_and_gdb() {
    target_runs_c_and_stops_in_gdb("riscv64");
}

#[test]
fn rust_builds_for_each_target() {
    let dir = scratch("rust");
    let src = dir.join("p.rs");
    std::fs::write(&src, RUST_PROGRAM).unwrap();
    let rustc = deps().join(format!("rust-{}/bin/rustc", crate::s09_release::pinned()));
    for (arch, triple) in [
        ("aarch64", "aarch64-unknown-linux-gnu"),
        ("riscv64", "riscv64gc-unknown-linux-gnu"),
    ] {
        let bin = dir.join(arch);
        let linker = format!(
            "linker={}",
            deps().join("bin").join(format!("{arch}-cc")).display()
        );
        stdout(
            rustc.to_str().unwrap(),
            &[
                "--edition=2021",
                "--target",
                triple,
                "-C",
                &linker,
                src.to_str().unwrap(),
                "-o",
                bin.to_str().unwrap(),
            ],
        );
        let libs = deps().join(arch).join(format!("usr/{arch}-linux-gnu"));
        let out = stdout(
            &format!("qemu-{arch}"),
            &["-L", libs.to_str().unwrap(), bin.to_str().unwrap()],
        );
        assert_eq!(out, "sum 55\n");
    }
}

/// Podman with the battery's own storage, rootless as the user who runs the battery.
///
/// /home/luke/Work/wt/zrun runs every command, these tests included, in a user namespace that
/// maps the user to uid 0 (`unshare --user --map-root-user`). Podman started there sees uid 0,
/// takes the paths of a root install (/run/libpod) and fails ("mkdir /run/libpod: permission
/// denied", measured 2026-11-17), so this test could not pass under zrun. In a user namespace
/// (a /proc/self/uid_map other than the identity map `0 0 4294967295`), podman is started by the
/// user's own systemd manager instead (`systemd-run --user --pipe --wait`), which runs it outside
/// the namespace with stdin, stdout and stderr passed through and its exit status returned.
/// KillMode=process ends the unit when podman exits: without it `--wait` also waits for the
/// container's monitor process (conmon), which `podman run -d` leaves in the unit until the
/// container ends (47 s for `sleep 50`, measured). Outside a user namespace, podman runs directly.
/// systemd-run expands `${name}` in the arguments it passes (not `$name` or `%h`, measured
/// 2026-11-17), so an argument that holds a shell script names its variables as `$name`.
pub(crate) fn podman(args: &[&str]) -> Output {
    let storage = deps().join("podman/storage.conf");
    let identity = std::fs::read_to_string("/proc/self/uid_map")
        .is_ok_and(|m| m.split_whitespace().eq(["0", "0", "4294967295"]));
    let mut command = if identity {
        let mut c = Command::new("podman");
        c.env("CONTAINERS_STORAGE_CONF", &storage);
        c
    } else {
        let mut c = Command::new("systemd-run");
        c.args(["--user", "--pipe", "--wait", "--quiet", "--collect"])
            .args(["-p", "KillMode=process"])
            .arg(format!(
                "--setenv=CONTAINERS_STORAGE_CONF={}",
                storage.display()
            ))
            .arg("podman");
        c
    };
    command
        .arg("--log-level=error")
        .args(args)
        .stdin(Stdio::null())
        .output()
        .unwrap()
}

#[test]
fn containers_reach_each_other_until_one_is_killed() {
    let id = std::process::id();
    let (net, node) = (format!("zed-full-net-{id}"), format!("zed-full-node-{id}"));
    let created = podman(&["network", "create", &net]);
    assert!(
        created.status.success(),
        "podman network create failed: {}",
        String::from_utf8_lossy(&created.stderr)
    );
    let started = podman(&[
        "run",
        "-d",
        "--name",
        &node,
        "--network",
        &net,
        IMAGE,
        "sleep",
        "50",
    ]);
    // Nothing here waits a fixed time (FLAKY-full-s00-01-tools-load). The running node is pinged
    // until it answers: one ping may go unanswered while its ARP request waits for a retry
    // (1 s, seen on a veth at load 60). `podman kill` returns once the node has exited and its
    // network is removed (state `exited` right after it in 10 of 10 runs, podman 5.8.9), so the
    // second ping needs no wait.
    let ping = |script: &str| {
        let args = ["run", "--rm", "--network", &net, IMAGE, "sh", "-c", script];
        podman(&args).status.success()
    };
    let before = ping(&format!("until ping -c 1 -W 1 {node}; do :; done"));
    let killed = podman(&["kill", &node]).status.success();
    let after = ping(&format!("ping -c 1 -W 1 {node}"));
    podman(&["rm", "-f", &node]);
    podman(&["network", "rm", &net]);
    assert!(
        started.status.success(),
        "{}",
        String::from_utf8_lossy(&started.stderr)
    );
    assert!(before, "the running node did not answer");
    assert!(killed);
    assert!(!after, "the killed node still answered");
}

/// Pings a peer namespace over a veth pair, before and after adding a delay to the link, then
/// prints the delay's queue with its counters.
///
/// Nothing here waits a fixed time (FLAKY-full-s00-01-tools-load). The peer prints its pid once
/// it is in its own namespace, where `sleep 0.2` guessed it would be (later, the veth's other end
/// stayed in this namespace and the pings went over loopback, past the delay), and lives until
/// this script's end closes its stdin, where `sleep 20` could end first. The first ping waits for
/// both ends to be up as the kernel reports them (`state UP`), which it sets in the step that
/// enables a link's queue, so that an ARP request is not dropped by a queue not yet enabled.
const NETEM_SCRIPT: &str = r#"
coproc peer_proc { exec unshare -n sh -c 'echo $$; exec cat >/dev/null'; }
read -r peer <&"${peer_proc[0]}"
ip link add va type veth peer name vb netns "$peer"
ip addr add 10.77.0.1/24 dev va
ip link set va up
nsenter -n -t "$peer" sh -c 'ip link set lo up; ip addr add 10.77.0.2/24 dev vb; ip link set vb up'
until ip -o link show dev va | grep -q 'state UP' &&
  nsenter -n -t "$peer" ip -o link show dev vb | grep -q 'state UP'; do sleep 0.01; done
ping -c 1 -W 3 10.77.0.2
tc qdisc add dev va root netem delay 150ms
ping -c 1 -W 3 10.77.0.2
status=$?
tc -s qdisc show dev va
kill "$peer"
exit $status
"#;

/// The delayed ping took at least the delay, which load can only lengthen, and its packet went
/// through the delay's queue. The undelayed ping is not timed: it took 1009 ms once at load 60
/// (2026-11-17; 1 s is the ARP retry time), where the test asked for under 100 ms; a time's upper
/// bound fails under enough load. The queue's counters show instead, with no time in them, that the
/// delay is netem's.
#[test]
fn network_namespace_link_delays_packets() {
    let out = stdout("unshare", &["-Urn", "bash", "-c", NETEM_SCRIPT]);
    let times: Vec<f64> = out
        .split("time=")
        .skip(1)
        .map(|t| t.split(' ').next().unwrap().parse().unwrap())
        .collect();
    assert_eq!(times.len(), 2, "{out}");
    assert!(times[1] >= 150.0, "the delayed link took {} ms", times[1]);
    let netem = out
        .split("qdisc netem ")
        .nth(1)
        .unwrap_or_else(|| panic!("no netem queue on the link: {out}"));
    assert!(netem.contains(" delay 150ms"), "{out}");
    let sent: u64 = netem
        .split(" bytes ")
        .nth(1)
        .and_then(|s| s.split(" pkt").next())
        .and_then(|n| n.parse().ok())
        .unwrap_or_else(|| panic!("no packet count for the netem queue: {out}"));
    assert!(sent >= 1, "no packet went through the delay: {out}");
}
