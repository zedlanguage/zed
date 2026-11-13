//! A repair is offered only when the checker accepts the repaired application, so applying
//! the offered repair makes the program check.

use super::rejected;
use zedc::run::load;

/// The program `src` with the text `at` wrapped in `word(…)`.
fn wrapped(src: &str, at: &str, word: &str) -> String {
    assert_eq!(src.matches(at).count(), 1, "{at}");
    src.replace(at, &format!("{word}({at})"))
}

#[test]
fn the_offered_repair_applied_makes_the_program_check() {
    let cases = [
        (
            "main(m: MainArgs) {
  n = int(m.stdin[0]) else 0;
  m.stdout <- \"count: \" ++ n * 2;
}
",
            "n * 2",
            "String",
        ),
        (
            "price(positional cents: int) = cents * 100;
main(m: MainArgs) {
  m.stdout <- String(price(2.5));
}
",
            "2.5",
            "",
        ),
    ];
    for (src, at, word) in cases {
        let out = rejected(src);
        if word.is_empty() {
            assert!(!out.contains("repair:"), "{out}");
            continue;
        }
        let offered = format!("repair: wrap this in `{word}(…)`; the checker accepts that");
        assert!(out.contains(&offered), "{out}");
        let fixed = wrapped(src, at, word);
        load(fixed.as_bytes()).unwrap_or_else(|e| panic!("{fixed}\n{e}"));
    }
}

#[test]
fn a_conversion_that_can_fail_is_not_offered_where_its_failure_is_not_taken() {
    // `int(m.stdin[0])` is `int | #invalid | …`, and `discount` takes no `#invalid`.
    let src = "discount(price: int, tier) = if tier == #gold { price * 8 } else { price * 10 };
main(m: MainArgs) {
  p = discount(price: m.stdin[0], tier: #gold);
  m.stdout <- String(p);
}
";
    let out = rejected(src);
    assert!(!out.contains("repair: wrap this in `int"), "{out}");
    let tried = wrapped(src, "m.stdin[0]", "int");
    assert!(load(tried.as_bytes()).is_err());
    // `int("12")` always converts, so it is `int` and is offered (item CAST-literal-exact).
    let src = src.replace("m.stdin[0]", "\"12\"");
    let offered = "repair: wrap this in `int(…)`; the checker accepts that";
    assert!(rejected(&src).contains(offered));
    let fixed = wrapped(&src, "\"12\"", "int");
    load(fixed.as_bytes()).unwrap_or_else(|e| panic!("{fixed}\n{e}"));
}
