//! The oracle over every source enabled at L1: the fences, the step units, the corpus
//! programs, and the step programs run on every corpus input.

use zed_tests::oracle::{self, ENABLED, Report, native, program, unit};

#[test]
fn every_enabled_fence_agrees() {
    let mut r = Report::default();
    native(|engines| {
        for f in zed_tests::fences::all()
            .iter()
            .filter(|f| f.layer <= ENABLED && !f.notation)
        {
            r.add(&f.at, unit(&f.text, engines));
        }
    });
    assert_eq!(r.mismatches, Vec::<String>::new());
    // The lambda fence's `five` and `seven` under each engine, and the table checks of the
    // four fences: the three rejected ones compare nothing.
    assert_eq!(r.compared, 6);
}

#[test]
fn every_step_unit_agrees() {
    let mut r = Report::default();
    native(|engines| {
        for p in oracle::step_units() {
            let text = std::fs::read_to_string(&p).unwrap();
            r.add(&p.display().to_string(), unit(&text, engines));
        }
    });
    assert_eq!(r.mismatches, Vec::<String>::new());
    assert_eq!(r.compared, 12);
}

#[test]
fn every_enabled_corpus_program_agrees_and_writes_its_output() {
    let corpus = oracle::corpus();
    assert_eq!(corpus.len(), 31);
    let enabled: Vec<_> = corpus.iter().filter(|(_, l)| *l <= ENABLED).collect();
    // The corpus begins at L3; each program joins the oracle when its layer is enabled.
    assert_eq!(enabled.len(), 0);
    native(|engines| {
        for (path, _) in enabled {
            let text = std::fs::read_to_string(path).unwrap();
            let input = std::fs::read(path.with_extension("in")).unwrap();
            let out = std::fs::read(path.with_extension("out")).unwrap();
            let (r, want) = program(&text, &input, engines);
            assert_eq!(r.mismatches, Vec::<String>::new(), "{}", path.display());
            let out = zed_kernel::Value::str(&String::from_utf8_lossy(&out));
            assert_eq!(want, Some(format!("port `stdout` writes {out}")));
        }
    });
}

#[test]
fn every_step_program_agrees_on_every_corpus_input() {
    let mut r = Report::default();
    let mut runs = 0;
    native(|engines| {
        for p in oracle::step_units() {
            let text = std::fs::read_to_string(&p).unwrap();
            for (c, _) in oracle::corpus() {
                let input = std::fs::read(c.with_extension("in")).unwrap();
                let (rep, want) = program(&text, &input, engines);
                runs += usize::from(want.is_some());
                r.add(&format!("{} on {}", p.display(), c.display()), rep);
            }
        }
    });
    assert_eq!(r.mismatches, Vec::<String>::new());
    // Four programs on 31 inputs, each under two engines.
    assert_eq!((runs, r.compared), (124, 248));
}
