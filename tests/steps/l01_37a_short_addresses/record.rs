//! The verdicts and outputs of every source enabled at L1, and the verdicts of every fence
//! and corpus program, as snapshots. The snapshots are shared by the full build and the build
//! with `short-addresses`, so each test passing in both shows the two builds agree on that
//! piece.

use std::fmt::Write;

use zed_kernel::{Evaluator, Term, World};
use zed_tests::oracle::{self, ENABLED};
use zedc::elab::Cones;
use zedc::interp;
use zedc::query::Db;
use zedc::run;
use zedc::testing::test;

/// What the full checker gives for the unit `text`: its front verdict with every diagnostic
/// and its steps, the checks of its tables, and the value or error of each binding with no
/// function component.
fn verdict(text: &str) -> String {
    let mut out = String::new();
    let front = Db::new().front(text);
    match &*front {
        Err(ds) => writeln!(out, "  rejected: {ds:#?}"),
        Ok((_, u, warnings)) => {
            writeln!(out, "  warnings: {warnings:#?}").expect("a String takes any write");
            let cones = Cones::new(u);
            for d in u.defs.iter().filter(|d| d.first_order) {
                let t = interp::prelude(cones.close(Term::Var(d.kernel.clone())));
                let v = run::direct(&t, &mut Evaluator::new(World::new()));
                writeln!(out, "  `{}`: {v:?}", d.name).expect("a String takes any write");
            }
            Ok(())
        }
    }
    .expect("a String takes any write");
    writeln!(out, "  checks: {:?}", test(text)).expect("a String takes any write");
    out
}

#[test]
fn every_enabled_fence() {
    let mut out = String::new();
    for f in zed_tests::fences::all()
        .iter()
        .filter(|f| f.layer <= ENABLED && !f.notation)
    {
        writeln!(out, "{}\n{}", f.key, verdict(&f.text)).expect("a String takes any write");
    }
    insta::assert_snapshot!(without_addresses(&out));
}

#[test]
fn every_fence_front_verdict() {
    let mut out = String::new();
    for f in zed_tests::fences::all().iter().filter(|f| !f.notation) {
        let front = Db::new().front(&f.text);
        let v = match &*front {
            Ok((_, _, warnings)) => format!("accepted, warnings {warnings:?}"),
            Err(ds) => format!("rejected: {ds:?}"),
        };
        writeln!(out, "{}: {v}", f.key).expect("a String takes any write");
    }
    insta::assert_snapshot!(without_addresses(&out));
}

#[test]
fn every_rejected_variant() {
    let mut out = String::new();
    for v in zed_tests::fences::variants() {
        writeln!(out, "{}\n{}", v.name, verdict(&v.text)).expect("a String takes any write");
    }
    insta::assert_snapshot!(without_addresses(&out));
}

#[test]
fn every_step_unit() {
    let mut out = String::new();
    for p in oracle::step_units() {
        let text = std::fs::read_to_string(&p).expect("a readable step unit");
        let name = p
            .strip_prefix(zed_tests::steps_dir())
            .expect("a step unit under the steps directory");
        writeln!(out, "{}\n{}", name.display(), verdict(&text)).expect("a String takes any write");
    }
    insta::assert_snapshot!(without_addresses(&out));
}

#[test]
fn every_corpus_program() {
    let corpus = oracle::corpus();
    assert_eq!(corpus.len(), 31);
    let mut out = String::new();
    for (path, layer) in corpus {
        let text = std::fs::read(&path).expect("a readable program");
        let v = match run::load(&text) {
            Ok(_) => "loads".to_string(),
            Err(e) => format!("does not load: {e}"),
        };
        let name = path.file_name().expect("a file name").to_string_lossy();
        writeln!(out, "{name} (L{layer}): {v}").expect("a String takes any write");
    }
    insta::assert_snapshot!(without_addresses(&out));
}

#[test]
fn every_step_program_on_every_corpus_input() {
    let corpus = oracle::corpus();
    let mut out = String::new();
    for p in oracle::step_units() {
        let text = std::fs::read_to_string(&p).expect("a readable step unit");
        if run::load(text.as_bytes()).is_err() {
            continue;
        }
        let name = p
            .strip_prefix(zed_tests::steps_dir())
            .expect("a step unit under the steps directory");
        writeln!(out, "{}", name.display()).expect("a String takes any write");
        for (c, _) in &corpus {
            let input = std::fs::read(c.with_extension("in")).expect("a corpus input");
            let (_, want) = oracle::program(&text, &input, &[]);
            let c = c.file_name().expect("a file name").to_string_lossy();
            writeln!(out, "  {c}: {}", want.expect("a program that loads is run"))
                .expect("a String takes any write");
        }
    }
    insta::assert_snapshot!(without_addresses(&out));
}

#[test]
fn printed_types() {
    // Types whose diagrams test many tuple types and atoms: their printing does not follow
    // the digests, which the two builds order differently. A union of tuple types less
    // another, such as `(| (tuple 0 #a0) (tuple 1 #a1)) - (tuple 1 _)`, printed the negations
    // along its diagram's paths, which follow the digests, so the two builds printed it
    // differently, until both printers showed a diagram from its decision list in its one
    // form (step BDD-atom-order).
    use zed_kernel::Value;
    use zed_kernel::types::Type;
    let lit = |i: i64| Type::lit(&Value::Int(i)).expect("an integer literal type");
    let mut out = String::new();
    for n in [2, 5, 12] {
        let tuples = Type::union_all(
            (0..n).map(|i| Type::tuple(vec![lit(i), Type::atom(&format!("a{i}"))])),
        );
        let atoms = Type::union_all((0..n).map(|i| Type::atom(&format!("b{i}"))));
        let met = &Type::tuple(vec![Type::int(), lit(0)]) & &Type::tuple(vec![lit(n), Type::int()]);
        let less = &tuples - &Type::tuple(vec![lit(n - 1), Type::top()]);
        writeln!(out, "{n}: {tuples}\n  {atoms}\n  {met}\n  {}", !&tuples)
            .expect("a String takes any write");
        for t in [&tuples, &met, &!&tuples, &less] {
            writeln!(out, "  {}", t.surface()).expect("a String takes any write");
        }
        writeln!(out, "  {less}").expect("a String takes any write");
    }
    insta::assert_snapshot!(without_addresses(&out));
}

/// `out` without the address of each diagnostic. The build with `short-addresses` keeps one
/// byte of each address, so the two builds print different addresses for the same diagnostic,
/// and the snapshots they share leave them out: a line `address: #…,` of a pretty-printed
/// diagnostic, `, address: #…` of one printed on a line, and the optional address of a test
/// outcome, `, address: Some(#…)` or `, address: None` (DIAG-addr-rest). One pass over `out`.
fn without_addresses(out: &str) -> String {
    const FIELD: &str = ", address: ";
    let mut kept = String::with_capacity(out.len());
    for line in out.split_inclusive('\n') {
        if line.trim_start().starts_with("address: #") {
            continue;
        }
        let mut rest = line;
        while let Some(i) = rest.find(FIELD) {
            let tail = &rest[i + FIELD.len()..];
            let after = if let Some(t) = tail.strip_prefix("None") {
                t
            } else {
                let (t, some) = match tail.strip_prefix("Some(") {
                    Some(t) => (t, true),
                    None => (tail, false),
                };
                let Some(t) = t.strip_prefix('#') else {
                    // Not an address: keep the text and look after it.
                    kept.push_str(&rest[..i + FIELD.len()]);
                    rest = tail;
                    continue;
                };
                let hex = t.find(|c: char| !c.is_ascii_hexdigit()).unwrap_or(t.len());
                let t = &t[hex..];
                if some {
                    t.strip_prefix(')').unwrap_or(t)
                } else {
                    t
                }
            };
            kept.push_str(&rest[..i]);
            rest = after;
        }
        kept.push_str(rest);
    }
    kept
}
