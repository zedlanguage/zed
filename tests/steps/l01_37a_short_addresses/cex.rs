//! Counterexamples replayed as fixed tests: each failing row the checker reports names the
//! result of its call, and the call run alone under the interpreter and both native engines
//! gives that result, in the full build and with `short-addresses`.

use zed_tests::oracle::{self, ENABLED, Report, counterexamples, native};
use zedc::testing::test;

/// A unit whose tables hold two wrong rows among right ones.
const WRONG: &str = "double(positional x) = x * 2
test { 1 -> 2, 3 -> 7, 4 -> 8 }

greet(positional name) = \"hi ${name}\"
test { \"ann\" -> \"hello ann\" }
";

#[test]
fn a_wrong_row_is_replayed_with_the_result_it_names() {
    let failures: Vec<String> = test(WRONG).into_iter().filter_map(|o| o.failure).collect();
    assert_eq!(
        failures,
        [
            "`3 -> 7` of `double`: the result is 6",
            "`\"ann\" -> \"hello ann\"` of `greet`: the result is \"hi ann\"",
        ]
    );
    let ((r, replayed), runs) = native(|engines| counterexamples(WRONG, engines));
    assert_eq!(replayed, 2);
    assert_eq!(runs, 4, "native runs, each leaving no cell live");
    assert_eq!(r.mismatches, Vec::<String>::new());
    // Each row under the interpreter and the two native engines.
    assert_eq!(r.compared, 6);
}

#[test]
fn a_replay_that_disagrees_is_reported() {
    // The replay compares with the failure's text: a row whose call gives another result
    // under some engine is a mismatch. Here the "engine" adds one to every integer result.
    let wrong: &zedc::run::Through<'_> = &|t, e| match zedc::run::direct(t, e)? {
        zed_kernel::Value::Int(i) => Ok(zed_kernel::Value::Int(i + 1)),
        v => Ok(v),
    };
    let (r, replayed) = counterexamples(WRONG, &[("off by one", wrong)]);
    assert_eq!(replayed, 2);
    assert_eq!(
        r.mismatches,
        [
            "the counterexample `3 -> 7` of `double`: the checker names the result is 6, and off by \
          one gives the result is 7"
        ]
    );
}

#[test]
fn every_enabled_source_replays_its_counterexamples() {
    let mut r = Report::default();
    let mut replayed = 0;
    let ((), _) = native(|engines| {
        let mut add = |at: &str, text: &str| {
            let (rep, n) = counterexamples(text, engines);
            replayed += n;
            r.add(at, rep);
        };
        for f in zed_tests::fences::all()
            .iter()
            .filter(|f| f.layer <= ENABLED && !f.notation)
        {
            add(&f.at, &f.text);
        }
        for p in oracle::step_units() {
            add(
                &p.display().to_string(),
                &std::fs::read_to_string(&p).expect("a readable step unit"),
            );
        }
        for (p, _) in oracle::corpus().iter().filter(|(_, l)| *l <= ENABLED) {
            add(
                &p.display().to_string(),
                &std::fs::read_to_string(p).expect("a readable program"),
            );
        }
    });
    assert_eq!(r.mismatches, Vec::<String>::new());
    // Every enabled unit's tables pass, so no row is replayed.
    assert_eq!((replayed, r.compared), (0, 0));
}
