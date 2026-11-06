//! The report of `zedc --report` (plan item TIME-report): the instructions and bytes of a
//! compilation by stage, unit and definition, counted by the meter of the scaling tests and the
//! counting allocator. A row's work is its own, so the rows sum to the total; a test row that a
//! query takes from its cache counts as cached, at no work.

use zed_tests::scaling::{self, Meter};
use zedc::query::Db;
use zedc::work::{self, Counter, Report, Row, Stage, Work};

use super::{PRICING, checks};

/// The counter of a report: the meter's count as instructions, and the bytes this thread
/// allocates.
fn counter() -> Counter {
    let mut meter = Meter::new();
    Box::new(move || Work {
        instructions: meter.read(),
        bytes: zed_alloc_count::allocated(),
    })
}

/// The test rows of `r` as (definition, instructions, bytes, computed, cached).
fn test_rows(r: &Report) -> Vec<(&str, u64, u64, u64, u64)> {
    r.rows
        .iter()
        .filter(|x| x.stage == Stage::Test)
        .map(|x| {
            let d = x
                .definition
                .as_deref()
                .expect("a test row names its definition");
            (d, x.work.instructions, x.work.bytes, x.computed, x.cached)
        })
        .collect()
}

fn sum(rows: &[Row]) -> Work {
    rows.iter().fold(Work::default(), |s, x| s + x.work)
}

#[test]
fn the_rows_sum_to_the_total_and_name_each_stage_and_definition() {
    let (got, r) = work::with(counter(), || checks(&mut Db::new(), PRICING));
    assert!(got.iter().all(|c| c.ends_with(": ok")), "{got:?}");
    assert_eq!(sum(&r.rows), r.total, "{r}");
    assert!(r.total.instructions > 0 && r.total.bytes > 0, "{r}");
    for stage in [
        Stage::Lex,
        Stage::Parse,
        Stage::Syntax,
        Stage::Resolve,
        Stage::Check,
        Stage::Elaborate,
        Stage::Linear,
    ] {
        let row = r
            .rows
            .iter()
            .find(|x| x.stage == stage && x.definition.is_none());
        let row = row.unwrap_or_else(|| panic!("no row of {stage:?} in\n{r}"));
        assert_eq!((row.computed, row.cached), (1, 0), "{r}");
        assert!(
            row.work.instructions > 0,
            "{stage:?} counts no work in\n{r}"
        );
    }
    let tests: Vec<_> = test_rows(&r).iter().map(|t| (t.0, t.3, t.4)).collect();
    assert_eq!(
        tests,
        [("discount", 2, 0), ("tax", 2, 0), ("total", 1, 0)],
        "{r}"
    );
    // Each line of the text form is a row, after a header and before the total.
    let text = r.to_string();
    assert_eq!(text.lines().count(), r.rows.len() + 2, "{text}");
    let total = text.lines().last().expect("the total line");
    let words: Vec<&str> = total.split_whitespace().collect();
    let expected = [
        "total".to_string(),
        r.total.instructions.to_string(),
        r.total.bytes.to_string(),
    ];
    assert_eq!(words, expected, "{text}");
}

#[test]
fn a_cached_definition_reports_zero() {
    let mut db = Db::new();
    let (_, first) = work::with(counter(), || checks(&mut db, PRICING));
    // `tax` changes; `discount` does not, so its rows come from the cache, and `total`, which
    // calls `tax`, is computed again.
    let edited = PRICING.replace("cents * 8 div 100", "cents * 8 div 100 + 0");
    let (got, second) = work::with(counter(), || checks(&mut db, &edited));
    assert!(got.iter().all(|c| c.ends_with(": ok")), "{got:?}");
    assert_eq!(sum(&second.rows), second.total, "{second}");
    let before = test_rows(&first);
    assert!(
        before.iter().all(|t| t.1 > 0 && t.3 > 0 && t.4 == 0),
        "{first}"
    );
    let after = test_rows(&second);
    assert_eq!(after[0], ("discount", 0, 0, 0, 2), "{second}");
    for (d, instructions, bytes, computed, cached) in &after[1..] {
        assert!(
            *instructions > 0 && *bytes > 0 && *computed > 0 && *cached == 0,
            "{d} was computed again but reports {instructions} instructions in\n{second}"
        );
    }
    // The same text again: the front end and every row come from the cache.
    let (_, third) = work::with(counter(), || checks(&mut db, &edited));
    assert!(third.rows.iter().all(|x| x.stage != Stage::Lex), "{third}");
    let all_cached: Vec<_> = test_rows(&third).iter().map(|t| (t.1, t.2, t.3)).collect();
    assert_eq!(all_cached, [(0, 0, 0); 3], "{third}");
}

/// A unit of a light definition with one row and a heavy one with `rows` rows.
fn light_and_heavy(rows: usize) -> String {
    let table: Vec<String> = (0..rows).map(|i| format!("{i} -> {}", i * 3)).collect();
    format!(
        "light(positional x: int) = x + 1\ntest {{ 1 -> 2 }}\n\n\
         heavy(positional x: int) = x * 3\ntest {{ {} }}\n",
        table.join(", ")
    )
}

#[test]
fn the_work_of_a_definition_is_in_its_own_row() {
    let text = light_and_heavy(200);
    let (got, r) = work::with(counter(), || checks(&mut Db::new(), &text));
    assert_eq!(got.len(), 201, "{got:?}");
    let rows = test_rows(&r);
    let (light, heavy) = (rows[0], rows[1]);
    assert_eq!(
        (light.0, light.3, heavy.0, heavy.3),
        ("light", 1, "heavy", 200),
        "{r}"
    );
    assert!(
        heavy.1 > 50 * light.1,
        "200 rows of `heavy` take {} instructions, 1 row of `light` {}:\n{r}",
        heavy.1,
        light.1
    );
}

/// A unit of `n` definitions, each with a one-row table.
fn definitions(n: usize) -> String {
    (0..n)
        .map(|i| {
            format!(
                "d{i}(positional x: int) = x + {i}\ntest {{ 1 -> {} }}\n\n",
                i + 1
            )
        })
        .collect()
}

/// The recorder alone, with a counter that does no work of its own: n definitions in n / 8
/// units, each marked once computed and once cached, then written as text. The front end's
/// work hides the recorder's in the test below, so this one measures it apart.
#[test]
fn the_recorder_scales_with_its_rows() {
    let n = 2000;
    let names = |m: usize| -> Vec<(String, String)> {
        (0..m)
            .map(|i| (format!("u{}.zed", i / 8), format!("d{i}")))
            .collect()
    };
    let (small, large) = (names(n), names(8 * n));
    scaling::check("the recorder with n rows", n, |m| {
        let marks = if m == n { &small } else { &large };
        let ((), r) = work::with(Box::new(Work::default), || {
            for (u, d) in marks {
                work::unit(u);
                work::stage(Stage::Test, Some(d), || ());
                work::cached(Stage::Test, Some(d));
            }
        });
        assert_eq!(test_rows(&r).len(), m);
        std::hint::black_box(r.to_string());
    });
}

#[test]
fn a_report_scales_with_the_definitions() {
    // The texts are built before any run is counted.
    let n = 40;
    let (small, large) = (definitions(n), definitions(8 * n));
    scaling::check("a reported test of n definitions", n, |m| {
        let text = if m == n { &small } else { &large };
        let (got, r) = work::with(counter(), || checks(&mut Db::new(), text));
        assert!(got.len() == m && got.iter().all(|c| c.ends_with(": ok")));
        assert_eq!(test_rows(&r).len(), m);
        std::hint::black_box(r.to_string());
    });
}
