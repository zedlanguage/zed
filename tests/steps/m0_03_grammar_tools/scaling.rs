//! How the tools scale with the size of the spec or the program. Each input is built before
//! timing, at n and 8n, and a tool's constant cost of reading the grammars is small beside the
//! work at these sizes.

use zed_tests::scaling::{check, inputs};
use zed_tools::spec::Spec;
use zed_tools::{audit, cases, check as check_tool, fences, fuzz, layer, progress, ring, sync};

use super::{Dir, design, fence, spec_dir};

/// `n` functions, each with its own name.
fn functions(n: usize) -> String {
    (0..n)
        .map(|i| format!("f{i}(x: int) -> int = x * {i};\n"))
        .collect()
}

/// `n` fences of one function each.
fn many_fences(n: usize) -> String {
    (0..n)
        .map(|i| fence(&format!("f{i}(x: int) -> int = x * {i};")))
        .collect()
}

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
    scales("check, by fences", 25, &dirs, |d| {
        assert_eq!(check_tool::run(&[d.root()], &mut String::new()), Ok(true));
    });
}

#[test]
fn check_scales_with_the_length_of_one_fence() {
    let dirs = specs("scale_check_long", 20, |n| fence(&functions(n)));
    scales("check, by the length of a fence", 20, &dirs, |d| {
        assert_eq!(check_tool::run(&[d.root()], &mut String::new()), Ok(true));
    });
}

#[test]
fn fences_scales_with_the_size_of_the_documents() {
    let dirs = specs("scale_fences", 1000, many_fences);
    scales("fences", 1000, &dirs, |d| {
        assert_eq!(fences::run(&[d.root()], &mut String::new()), Ok(true));
    });
}

#[test]
fn sync_scales_with_the_number_of_fences() {
    let dirs = specs("scale_sync", 25, many_fences);
    let zed = Dir::new("scale_sync_zed");
    for sub in ["fences", "grammar"] {
        std::fs::create_dir(zed.at(sub)).expect("a copy directory");
    }
    scales("sync", 25, &dirs, |d| {
        let spec = Spec::open(&d.root()).expect("the spec reads");
        assert_eq!(
            sync::sync_into(&spec, &zed.root(), false, &mut String::new()),
            Ok(true)
        );
    });
}

#[test]
fn cases_scales_with_the_number_of_cases() {
    let dir = spec_dir("scale_cases", &design(""), "");
    let line = "Expr ::: a + b * c ::: (a + (b * c))\n";
    let sized = [4000, 32000].map(|m| {
        let d = Dir::new(&format!("scale_cases_{m}"));
        d.write("cases.txt", &line.repeat(m));
        d.write("leftrec.txt", "");
        (m, d)
    });
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    scales("cases", 4000, &sized, |d| {
        assert_eq!(
            cases::run_files(&spec, &d.root(), &mut String::new()),
            Ok(true)
        );
    });
}

/// A directory holding a program of `m` functions, for `m` in `n` and `8n`.
fn programs(name: &str, n: usize) -> [(usize, Dir); 2] {
    [n, 8 * n].map(|m| {
        let d = Dir::new(&format!("{name}_{m}"));
        d.write("p.zed", &format!("// layer L1\n{}", functions(m)));
        (m, d)
    })
}

#[test]
fn ring_scales_with_the_length_of_a_file() {
    let spec = spec_dir("scale_ring", &design(""), "");
    let sized = programs("scale_ring_p", 150);
    scales("ring", 150, &sized, |d| {
        let args = [spec.root(), d.at("p.zed")];
        assert!(ring::run(&args, &mut String::new()).is_ok());
    });
}

#[test]
fn layer_scales_with_the_length_of_a_program() {
    let spec = spec_dir("scale_layer", &design(""), "");
    let sized = programs("scale_layer_p", 2000);
    scales("layer", 2000, &sized, |d| {
        let args = [spec.root(), d.at("p.zed")];
        assert!(layer::run(&args, &mut String::new()).is_ok());
    });
}

#[test]
fn audit_scales_with_the_length_of_a_program() {
    let spec = spec_dir("scale_audit", &design(""), "");
    let sized = programs("scale_audit_p", 12);
    scales("audit", 12, &sized, |d| {
        let args = [spec.root(), d.at("p.zed")];
        assert!(audit::run(&args, &mut String::new()).is_ok());
    });
}

/// The audit's comparison of a checklist with what a program needs, at `n` needed alternatives
/// and `n` needed words, all listed, and `n` of each listed that are not needed (rules the
/// grammar does not have, words the table does not list), so both directions are measured.
#[test]
fn the_checklist_comparison_scales_with_its_entries() {
    let dir = spec_dir("scale_checklist", &design(""), "");
    let spec = Spec::open(&dir.root()).expect("the spec reads");
    let table = layer::WordTable::read(&spec.design).expect("the table reads");
    let sized = inputs(2000, |m| {
        let needs = audit::Needs {
            program: "p.zed".into(),
            alts: (0..m).map(|i| (1, format!("R{i}"), 0)).collect(),
            words: (0..m).map(|i| (format!("w{i}"), 1)).collect(),
        };
        let alts: String = (0..m).map(|i| format!(" `R{i}#0` `S{i}#0`")).collect();
        let words: String = (0..m).map(|i| format!(" `w{i}` `x{i}`")).collect();
        let list = format!(
            "## Part A\n\n| Layer | Alternatives | Words |\n|---|---|---|\n| L1 |{alts} |{words} |\n"
        );
        (needs, list)
    });
    check("checklist comparison, by entries", 2000, |m| {
        let (needs, list) = &sized[&m];
        let mut out = String::new();
        let outcome = audit::compare(&spec, &table, needs, "ZED0.md", list, &mut out);
        assert_eq!(outcome, Ok(false));
        assert!(out.contains(&format!(", {} not needed `", 2 * m)), "{out}");
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
    const LAST_RING: u32 = 22;
    let opened = Spec::open(&spec.root()).expect("the spec reads");
    check("fuzz first pass", N, |m| {
        let accepted = fuzz::first_pass(&opened, LAST_RING.., m, 1, &mut String::new());
        assert!(accepted.expect("the first pass runs") > 0);
    });
}

#[test]
fn progress_scales_with_the_length_of_the_plan() {
    let text = |m: usize| {
        let steps: String = (1..=m).map(|i| format!("L1.{i}. Step {i}.\n")).collect();
        let done: String = (1..=m)
            .map(|i| format!("| L1.{i} | done | x |\n"))
            .collect();
        (
            format!("## (sec:steps) The steps, layer by layer\n\n### L1\n\n{steps}"),
            done,
        )
    };
    let (n, plans) = (2000, [text(2000), text(16000)]);
    check("progress", n, |m| {
        let (plan, done) = &plans[usize::from(m != n)];
        assert!(progress::render(plan, done, None).is_ok());
    });
}
