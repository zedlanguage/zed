//! How the tools scale with the size of the spec or the program. Each input is built before
//! timing, at n and 8n, and a tool's constant cost of reading the grammars is small beside the
//! work at these sizes. What each benchmark asserts besides its ratio is checked at small sizes
//! by `scaling::each_tool_benchmark_passes_at_small_sizes`.

use zed_tests::scaling::{check, inputs};
use zed_tools::layer;
use zed_tools::spec::Spec;

use crate::scaling::{
    audit_runs, cases_dir, cases_pass, check_passes, checklist, compares_checklist, fences_pass,
    first_pass_accepts, functions, layer_runs, lays_out_fences, many_fences, program_dir,
    progress_plan, reads_each_row, reads_unreadable, rejection_table, renders_progress, ring_runs,
    sync_body, sync_targets, syncs, unreadable,
};
use crate::{Dir, design, fence, spec_dir};

/// A spec for each of the sizes `n` and `8n`, with `body` of the size as its `DESIGN.md` fences.
fn specs(name: &str, n: usize, body: impl Fn(usize) -> String) -> [(usize, Dir); 2] {
    [n, 8 * n].map(|m| (m, spec_dir(&format!("{name}_{m}"), &design(&body(m)), "")))
}

/// Runs `run` at n and 8n on the directory built for the size.
fn scales(what: &str, n: usize, dirs: &[(usize, Dir); 2], run: impl Fn(&Dir) + Sync) {
    check(what, n, |m| {
        let (_, dir) = dirs
            .iter()
            .find(|d| d.0 == m)
            .expect("a size that was built");
        run(dir);
    });
}

#[test]
fn check_scales_with_the_number_of_fences() {
    let dirs = specs("scale_check", 25, many_fences);
    scales("check, by fences", 25, &dirs, check_passes);
}

#[test]
fn check_scales_with_the_length_of_one_fence() {
    let dirs = specs("scale_check_long", 20, |n| fence(&functions(n)));
    scales("check, by the length of a fence", 20, &dirs, check_passes);
}

#[test]
fn fences_scales_with_the_size_of_the_documents() {
    let dirs = specs("scale_fences", 1000, many_fences);
    scales("fences", 1000, &dirs, fences_pass);
}

#[test]
fn fence_layers_scales_with_the_number_of_fences() {
    let dirs = specs("scale_fence_layers", 25, many_fences);
    scales("fence_layers", 25, &dirs, |d| lays_out_fences(d, 25));
}

#[test]
fn rejection_rows_scale_with_the_number_of_rows() {
    let tables: [(usize, String); 2] = [2000, 16000].map(|m| (m, rejection_table(m)));
    check("rejection_rows", 2000, |m| {
        let (_, table) = tables
            .iter()
            .find(|t| t.0 == m)
            .expect("a size that was built");
        reads_each_row(table, m);
    });
}

#[test]
fn cases_scales_with_the_number_of_cases() {
    let dir = spec_dir("scale_cases", &design(""), "");
    let sized = [4000, 32000].map(|m| (m, cases_dir("scale_cases", m)));
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    scales("cases", 4000, &sized, |d| cases_pass(&spec, d));
}

/// A directory holding a program of `m` functions, for `m` in `n` and `8n`.
fn programs(name: &str, n: usize) -> [(usize, Dir); 2] {
    [n, 8 * n].map(|m| (m, program_dir(name, m)))
}

#[test]
fn ring_scales_with_the_length_of_a_file() {
    let spec = spec_dir("scale_ring", &design(""), "");
    let sized = programs("scale_ring_p", 150);
    scales("ring", 150, &sized, |d| ring_runs(&spec, d));
}

#[test]
fn layer_scales_with_the_length_of_a_program() {
    let spec = spec_dir("scale_layer", &design(""), "");
    let sized = programs("scale_layer_p", 2000);
    scales("layer", 2000, &sized, |d| layer_runs(&spec, d));
}

#[test]
fn audit_scales_with_the_length_of_a_program() {
    let spec = spec_dir("scale_audit", &design(""), "");
    let sized = programs("scale_audit_p", 12);
    scales("audit", 12, &sized, |d| audit_runs(&spec, d));
}

/// The audit's comparison of a checklist with what a program needs, at `n` needed alternatives
/// and `n` needed words, all listed, `n` of each listed that are not needed (rules the grammar
/// does not have, words the table does not list), so both directions are measured, and `n`
/// needed words of L1 listed both in the row L1 and in the row L2, so every listed place of an
/// entry is checked against its layer.
#[test]
fn the_checklist_comparison_scales_with_its_entries() {
    let dir = spec_dir("scale_checklist", &design(""), "");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let table = layer::WordTable::read(&spec.design).expect("the table reads");
    let sized = inputs(2000, checklist);
    check("checklist comparison, by entries", 2000, |m| {
        let (needs, list) = &sized[&m];
        compares_checklist(&spec, &table, needs, list, m);
    });
}

/// The audit's reading of Part A at `n` lines it cannot read, each for three reasons, and one
/// line it cannot read for `n` reasons, so every reason of every line is collected.
#[test]
fn the_checklist_reading_scales_with_its_unreadable_lines() {
    let dir = spec_dir("scale_checklist_unread", &design(""), "");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let table = layer::WordTable::read(&spec.design).expect("the table reads");
    let needs = zed_tools::audit::Needs {
        program: "p.zed".into(),
        ..Default::default()
    };
    let sized = inputs(16000, unreadable);
    check("checklist reading, by unreadable lines", 16000, |m| {
        reads_unreadable(&spec, &table, &needs, &sized[&m], m);
    });
}

/// The second pass of the fuzz runs over the rules the first pass missed, a set that shrinks as
/// `n` grows, so its cost at small `n` hides how the first pass grows. This test measures the
/// first pass. It does so at the last ring: a sentence at ring k is parsed once per ring above k,
/// which at low rings is so much work that a quadratic part stays out of sight below some
/// thousands of sentences.
#[test]
fn the_fuzz_first_pass_scales_with_the_number_of_programs() {
    let spec = spec_dir("scale_fuzz", &design(""), "");
    const N: usize = 1000;
    let opened = Spec::open(&spec.root()).expect("the spec reads");
    check("fuzz first pass", N, |m| first_pass_accepts(&opened, m));
}

#[test]
fn progress_scales_with_the_length_of_the_plan() {
    let (n, plans) = (2000, [progress_plan(2000), progress_plan(16000)]);
    check("progress", n, |m| {
        let (plan, done) = &plans[usize::from(m != n)];
        renders_progress(plan, done);
    });
}

/// `sync` lays out each `zed` fence and copies each `text` fence, so its work grows with the
/// number of both; each size writes into a `zed/` of its own directory.
#[test]
fn sync_scales_with_the_number_of_fences() {
    let dirs = specs("scale_sync", 25, sync_body);
    for (_, d) in &dirs {
        sync_targets(d);
    }
    scales("sync", 25, &dirs, syncs);
}
