//! The oracle over every source enabled at L1: the fences, the step units, the corpus
//! programs, and the step programs run on every corpus input.

use zed_tests::oracle::{self, ENABLED, Report, native, program, unit};

#[test]
fn every_enabled_fence_agrees() {
    let mut r = Report::default();
    let ((), runs) = native(|engines| {
        for f in zed_tests::fences::all()
            .iter()
            .filter(|f| f.layer <= ENABLED && !f.notation)
        {
            r.add(&f.at, unit(&f.text, engines));
        }
    });
    // The lambda fence's two bindings run together, once under each engine.
    assert_eq!(runs, 2, "native runs, each leaving no cell live");
    assert_eq!(r.mismatches, Vec::<String>::new());
    assert_eq!(r.not_compared, Vec::<String>::new());
    // The lambda fence's `five` and `seven` under each engine, and the table checks, under
    // each engine, of the fences whose front passes: the lambda fence, and the two `main`s of
    // sec:ports with `MainArgs` (DESIGN sec:ports 1, EXAMPLES section 18 fence 8); a fence the
    // front rejects compares nothing.
    assert_eq!(r.compared, 10);
}

#[test]
fn every_step_unit_agrees() {
    let mut r = Report::default();
    let ((), runs) = native(|engines| {
        for p in oracle::step_units() {
            let text = std::fs::read_to_string(&p).unwrap();
            r.add(&p.display().to_string(), unit(&text, engines));
        }
    });
    // A row of `main` gives its inputs by field of `MainArgs`, and each item of its key is
    // evaluated whether the body reads that field or not: config.zed's three rows evaluate 2
    // items more each than the fields its body reads, 6 runs under each engine.
    assert_eq!(runs, 232, "native runs, each leaving no cell live");
    assert_eq!(r.mismatches, Vec::<String>::new());
    assert_eq!(r.not_compared, Vec::<String>::new());
    assert_eq!(r.compared, 22);
}

#[test]
fn every_enabled_corpus_program_agrees_and_writes_its_output() {
    let corpus = oracle::corpus();
    assert_eq!(corpus.len(), 31);
    let enabled: Vec<_> = corpus.iter().filter(|(_, l)| *l <= ENABLED).collect();
    // The corpus begins at L3; each program joins the oracle when its layer is enabled.
    assert_eq!(enabled.len(), 0);
    let ((), runs) = native(|engines| {
        for (path, _) in enabled {
            let text = std::fs::read_to_string(path).unwrap();
            let input = std::fs::read(path.with_extension("in")).unwrap();
            let out = std::fs::read(path.with_extension("out")).unwrap();
            let (r, want) = program(&text, &input, engines);
            assert_eq!(r.mismatches, Vec::<String>::new(), "{}", path.display());
            assert_eq!(r.not_compared, Vec::<String>::new(), "{}", path.display());
            let out = zed_kernel::Value::str(&String::from_utf8_lossy(&out));
            assert_eq!(want, Some(format!("port `m.stdout` writes {out}")));
        }
    });
    assert_eq!(runs, 0, "native runs, each leaving no cell live");
}

#[test]
fn every_step_program_agrees_on_every_corpus_input() {
    let mut r = Report::default();
    let mut programs = 0;
    let ((), runs) = native(|engines| {
        for p in oracle::step_units() {
            let text = std::fs::read_to_string(&p).unwrap();
            for (c, _) in oracle::corpus() {
                let input = std::fs::read(c.with_extension("in")).unwrap();
                let (rep, want) = program(&text, &input, engines);
                programs += usize::from(want.is_some());
                r.add(&format!("{} on {}", p.display(), c.display()), rep);
            }
        }
    });
    assert_eq!(runs, 248, "native runs, each leaving no cell live");
    assert_eq!(r.mismatches, Vec::<String>::new());
    assert_eq!(r.not_compared, Vec::<String>::new());
    // Four programs on 31 inputs, each under two engines.
    assert_eq!((programs, r.compared), (124, 248));
}
