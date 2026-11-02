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
    let dir = env::temp_dir().join(format!("zed-full-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
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

fn target_runs_c_and_stops_in_gdb(arch: &str, port: &str) {
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

    let mut server = Command::new(&qemu)
        .args(["-L", libs, "-g", port, bin])
        .stdout(Stdio::null())
        .spawn()
        .unwrap();
    let remote = format!("target remote 127.0.0.1:{port}");
    let sysroot = format!("set sysroot {libs}");
    let gdb = stdout(
        "gdb",
        &[
            "-q",
            "-batch",
            "-ex",
            &sysroot,
            "-ex",
            &remote,
            "-ex",
            "break work",
            "-ex",
            "continue",
        ]
        .into_iter()
        .chain(["-ex", "bt", "-ex", "kill", bin])
        .collect::<Vec<_>>(),
    );
    server.wait().unwrap();
    assert!(
        gdb.contains("Breakpoint 1, work"),
        "no stop at the breakpoint: {gdb}"
    );
}

#[test]
fn aarch64_c_runs_under_qemu_and_gdb() {
    target_runs_c_and_stops_in_gdb("aarch64", "41301");
}

#[test]
fn riscv64_c_runs_under_qemu_and_gdb() {
    target_runs_c_and_stops_in_gdb("riscv64", "41302");
}

#[test]
fn rust_builds_for_each_target() {
    let dir = scratch("rust");
    let src = dir.join("p.rs");
    std::fs::write(&src, RUST_PROGRAM).unwrap();
    let rustc = deps().join("rust/bin/rustc");
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

/// Podman with the battery's own storage.
fn podman(args: &[&str]) -> Output {
    Command::new("podman")
        .arg("--log-level=error")
        .args(args)
        .env(
            "CONTAINERS_STORAGE_CONF",
            deps().join("podman/storage.conf"),
        )
        .output()
        .unwrap()
}

#[test]
fn containers_reach_each_other_until_one_is_killed() {
    let id = std::process::id();
    let (net, node) = (format!("zed-full-net-{id}"), format!("zed-full-node-{id}"));
    assert!(podman(&["network", "create", &net]).status.success());
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
    let ping = [
        "run",
        "--rm",
        "--network",
        &net,
        IMAGE,
        "ping",
        "-c",
        "1",
        "-W",
        "1",
        &node,
    ];
    let before = podman(&ping).status.success();
    let killed = podman(&["kill", &node]).status.success();
    let after = podman(&ping).status.success();
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

/// Pings a peer namespace over a veth pair, before and after adding a delay to the link.
const NETEM_SCRIPT: &str = r#"
unshare -n sleep 20 &
peer=$!
sleep 0.2
ip link add va type veth peer name vb netns $peer
ip addr add 10.77.0.1/24 dev va
ip link set va up
nsenter -n -t $peer sh -c 'ip link set lo up; ip addr add 10.77.0.2/24 dev vb; ip link set vb up'
ping -c 1 -W 3 10.77.0.2
tc qdisc add dev va root netem delay 150ms
ping -c 1 -W 3 10.77.0.2
status=$?
kill $peer
exit $status
"#;

#[test]
fn network_namespace_link_delays_packets() {
    let out = stdout("unshare", &["-Urn", "sh", "-c", NETEM_SCRIPT]);
    let times: Vec<f64> = out
        .split("time=")
        .skip(1)
        .map(|t| t.split(' ').next().unwrap().parse().unwrap())
        .collect();
    assert_eq!(times.len(), 2, "{out}");
    assert!(
        times[0] < 100.0,
        "the link without a delay took {} ms",
        times[0]
    );
    assert!(times[1] >= 150.0, "the delayed link took {} ms", times[1]);
}
