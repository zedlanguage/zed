//! The identity of a link at the rule of low complexity (DESIGN.md Part G): the benchmarks of
//! this step, run by `tools/run_tests.sh --bench` and left out of its default run. Each check
//! they make besides the ratio is made at a small size by the correctness test named in its
//! doc.

use std::fs::File;
use std::path::PathBuf;

use zed_native::link::{Inputs, dependencies, sweep};
use zed_tests::scaling::{self, FACTOR};

use super::leftover::{held, left, working};
use super::sources::{hash, till};
use super::{dir, scaling as driver, toolchain};

/// Small instances: `deps::each_file_is_hashed_once` (a file listed twice and by a second
/// path is hashed once) and `deps::lld_s_list_is_read_with_its_escapes`.
#[test]
fn the_files_a_link_read_are_hashed_in_linear_time() {
    // n files of 64 bytes, each listed twice and once by a second path, as a linker lists a
    // library it reads more than once.
    let n = 6_000;
    let d = dir("scaling_inputs");
    let paths: Vec<PathBuf> = (0..FACTOR * n)
        .map(|k| {
            let p = d.join(format!("lib{k}.a"));
            std::fs::write(&p, [k as u8; 64]).unwrap();
            p
        })
        .collect();
    let lists = scaling::inputs(n, |m| {
        let mut list = b"out: \\\n".to_vec();
        for p in &paths[..m] {
            for path in [
                p.clone(),
                p.clone(),
                d.join(".").join(p.file_name().unwrap()),
            ] {
                list.extend_from_slice(b"  ");
                list.extend_from_slice(path.as_os_str().as_encoded_bytes());
                list.extend_from_slice(b" \\\n");
            }
        }
        list.extend_from_slice(b"  ");
        list.extend_from_slice(paths[0].as_os_str().as_encoded_bytes());
        list.push(b'\n');
        list
    });
    scaling::check("the inputs of a link that read n files", n, |m| {
        let inputs = Inputs::of(dependencies(&lists[&m]), &[]).unwrap();
        assert_eq!(inputs.paths.len(), m);
    });
}

/// The sweep reads the output's directory once, and opens and tries to lock each working
/// directory of the output: linear in the directory's entries.
///
/// Small instance: `leftover::a_build_removes_what_stopped_builds_left_and_keeps_a_running_ones`.
#[test]
fn the_sweep_scales() {
    let n = 6_000;
    let made = |m: usize| -> (PathBuf, Vec<File>) {
        let d = dir(&format!("sweep{m}"));
        let out = d.join("sign");
        // m other files, and m working directories of running builds, which stay.
        let locks = (0..m)
            .map(|i| {
                std::fs::write(d.join(format!("note{i}")), b"").unwrap();
                held(&left(&out, 1, u32::try_from(i).unwrap()))
            })
            .collect();
        (out, locks)
    };
    let (small, large) = (made(n), made(FACTOR * n));
    scaling::check("the sweep of a directory of n entries", n, |m| {
        let out = if m == n { &small.0 } else { &large.0 };
        sweep(out);
    });
    assert_eq!(
        working(large.0.parent().unwrap(), &large.0).len(),
        FACTOR * n
    );
}

/// Small instances: `sources::one_tree_in_two_directories_gives_one_hash` and the edits of
/// `sources::an_edit_in_the_crate_or_a_crate_it_depends_on_changes_the_hash`.
#[test]
fn the_hash_of_the_sources_scales() {
    let n = 4_000;
    let trees = scaling::inputs(n, |m| till(&dir(&format!("sources-scaling-{m}")), m));
    assert_eq!(trees.len(), 2, "sizes {n} and {}", FACTOR * n);
    scaling::check(&format!("the sources of a crate of {n} modules"), n, |m| {
        std::hint::black_box(hash(&trees[&m]));
    });
}

/// Only the hash of the object file grows with the program; it allocates nothing. Small
/// instances: the keys of `identity.rs`, equal for equal object files and toolchains and
/// different for an edited object file.
#[test]
fn the_key_of_an_object_file_scales() {
    let n = 64 << 20;
    let tools = zed_native::link::Identity::of(&toolchain()).unwrap();
    let (small, large) = (vec![7u8; n], vec![7u8; FACTOR * n]);
    scaling::check_instructions_only("the key of an object file of n bytes", n, 1, |m| {
        let object = if m == n { &small } else { &large };
        std::hint::black_box(tools.key(object, &[]));
    });
}

/// A build runs the driver the same number of times at every size of program: the count, not
/// the time, is checked. Small instance: `scaling::a_build_runs_the_driver_for_its_reports_and_
/// its_link`.
#[test]
fn a_build_runs_the_driver_the_same_times_at_every_size() {
    let n = 40;
    driver::builds_run_the_driver_the_same_times("scaling", &[n, FACTOR * n]);
}
