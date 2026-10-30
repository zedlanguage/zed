//! What an edit recomputes, and that the answers stay those of a fresh database.

use zedc::query::{Db, Query};

use super::{PRICING, checks};

/// The counts of the three queries computed so far.
fn counts(db: &Db) -> [usize; 3] {
    [Query::Front, Query::Row, Query::Wave].map(|q| db.computed(q))
}

#[test]
fn asking_again_recomputes_nothing() {
    let mut db = Db::new();
    let first = checks(&mut db, PRICING);
    assert_eq!(
        first,
        ["2:8: ok", "2:19: ok", "5:8: ok", "5:22: ok", "8:8: ok"]
    );
    assert_eq!(counts(&db), [1, 5, 0]);
    assert_eq!(checks(&mut db, PRICING), first);
    assert_eq!(counts(&db), [1, 5, 0]);
}

#[test]
fn a_comment_reruns_the_front_end_and_no_row() {
    let mut db = Db::new();
    checks(&mut db, PRICING);
    let edited = format!("// prices in cents\n{PRICING}");
    let got = checks(&mut db, &edited);
    // The rows' places move with the text; their results are reused.
    assert_eq!(
        got,
        ["3:8: ok", "3:19: ok", "6:8: ok", "6:22: ok", "9:8: ok"]
    );
    assert_eq!(counts(&db), [2, 5, 0]);
}

#[test]
fn an_edit_reruns_the_rows_that_reach_the_changed_definition() {
    let mut db = Db::new();
    checks(&mut db, PRICING);
    // The tax rate goes to 10%: `tax`'s two rows and `total`'s row read `tax`; `discount`'s
    // two rows do not.
    let edited = PRICING.replace("cents * 8 div 100", "cents * 10 div 100");
    let got = checks(&mut db, &edited);
    assert_eq!(
        got,
        [
            "2:8: ok",
            "2:19: ok",
            "5:8: `10000 -> 800` of `tax`: the result is 1000",
            "5:22: `2500 -> 200` of `tax`: the result is 250",
            "8:8: `20000 -> 19440` of `total`: the result is 19800",
        ]
    );
    assert_eq!(counts(&db), [2, 8, 0]);
}

#[test]
fn a_new_row_is_the_only_row_computed() {
    let mut db = Db::new();
    checks(&mut db, PRICING);
    let edited = PRICING.replace("20000 -> 2000 }", "20000 -> 2000, 10000 -> 1000 }");
    let got = checks(&mut db, &edited);
    assert_eq!(got[2], "2:34: ok");
    assert_eq!(counts(&db), [2, 6, 0]);
}

#[test]
fn a_rejected_unit_is_kept_with_its_diagnostics() {
    let mut db = Db::new();
    let bad = "tax(positional cents: int) = cents * \"8\";\n";
    let first = checks(&mut db, bad);
    assert_eq!(first.len(), 1);
    // The outcome carries the diagnostic's derivation, as `zedc test` prints it.
    assert!(
        first[0]
            .starts_with("1:30: `*` does not take (int, \"8\")\n  [1] 1:30: `cents` is int here\n"),
        "{first:?}"
    );
    assert_eq!(checks(&mut db, bad), first);
    assert_eq!(counts(&db), [1, 0, 0]);
}

#[test]
fn a_wave_row_is_reused_until_main_or_what_it_reads_changes() {
    let src = "shout(positional s: String) = upper(s) ++ \"!\";\n\
               whisper(positional s: String) = lower(s);\n\
               main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- shout(stdin[1]);\n}\n\
               test { \"hi\" -> \"HI!\\n\" }\n";
    let mut db = Db::new();
    assert_eq!(checks(&mut db, src), ["6:8: ok"]);
    // `whisper` is not read by `main`: the wave is reused.
    let other = src.replace("lower(s)", "lower(s) ++ \"...\"");
    assert_eq!(checks(&mut db, &other), ["6:8: ok"]);
    assert_eq!(counts(&db), [2, 0, 1]);
    // `shout` is: the wave runs again.
    let read = src.replace("\"!\"", "\"!!\"");
    assert_eq!(
        checks(&mut db, &read),
        ["6:8: `\"hi\" -> \"HI!\\n\"` of `main`: port `stdout` writes \"HI!!\\n\""]
    );
    assert_eq!(counts(&db), [3, 0, 2]);
}

#[test]
fn every_answer_equals_a_fresh_databases() {
    let edits = [
        PRICING.to_string(),
        PRICING.replace("cents div 10", "cents div 5"),
        PRICING
            .replace("cents div 10", "cents div 5")
            .replace("19440", "17280"),
        format!("// v2\n{PRICING}"),
        PRICING.replace("tax(cents - discount(cents))", "tax(cents)"),
        PRICING.to_string(),
    ];
    let mut db = Db::new();
    for text in &edits {
        assert_eq!(
            checks(&mut db, text),
            checks(&mut Db::new(), text),
            "{text}"
        );
    }
    // The last text is the first again: nothing is computed for it.
    let before = counts(&db);
    checks(&mut db, &edits[0]);
    assert_eq!(counts(&db), before);
}
