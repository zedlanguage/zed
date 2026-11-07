//! Item MATHLIB-minfac: every `zed` fence of docs/mathlib-study.md lexes and parses as a unit at
//! the top ring, and each law the `euclid` proof cites outside the prelude is written in one of
//! them. This checks syntax only: `minFac`'s test table needs recursion (step L6.7) and its laws
//! need layer L15, as the page says.

use std::path::PathBuf;

use zed_tests::scaling::{check, inputs};
use zedc::fence::extract;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};

/// The text of this repository's docs/mathlib-study.md.
fn page() -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../docs/mathlib-study.md");
    std::fs::read_to_string(path).expect("docs/mathlib-study.md is readable")
}

/// The fences of `page` that do not lex, or do not parse as a unit at the top ring, each as its
/// line on the page and the error.
fn unparsed(page: &str) -> Vec<String> {
    extract(page)
        .into_iter()
        .filter_map(|f| {
            let at = format!("docs/mathlib-study.md:{}", f.line);
            match lex_fence(&f.text) {
                Err(e) => Some(format!("{at}: does not lex: {e}")),
                Ok(tokens) => parse(&f.text, &tokens, "Unit", TOP)
                    .err()
                    .map(|e| format!("{at}: does not parse: {e}")),
            }
        })
        .collect()
}

/// The laws that the `using` list of `law euclid` on `page` cites, in order.
fn euclid_cites(page: &str) -> Vec<String> {
    let line = page
        .lines()
        .find(|l| l.starts_with("law euclid("))
        .expect("the page states `law euclid`");
    let list = line
        .split_once("using(")
        .and_then(|(_, rest)| rest.split_once(')'))
        .expect("`euclid` has a `using` list")
        .0;
    list.split(',').map(|s| s.trim().to_string()).collect()
}

/// Whether a fence of `page` defines `name`, as a function (`name(` at the start of a line,
/// after any annotations) or as a law (`law name(`).
fn defines(page: &str, name: &str) -> bool {
    let call = format!("{name}(");
    let law = format!("law {name}(");
    extract(page).iter().any(|f| {
        f.text.lines().any(|l| {
            let mut rest = l.trim_start();
            while let Some(after) = rest.strip_prefix('@') {
                rest = skip_annotation(after).trim_start();
            }
            rest.starts_with(&call) || rest.starts_with(&law)
        })
    })
}

/// The text after an annotation's name and its argument list, if it has one, where `text`
/// starts just after the `@`: the parentheses of the list are matched, so an argument may hold
/// spaces and parentheses (`@measure(n - (k + 1))`).
fn skip_annotation(text: &str) -> &str {
    let name = text
        .find(|c: char| !(c.is_alphanumeric() || c == '_'))
        .unwrap_or(text.len());
    let rest = &text[name..];
    if !rest.starts_with('(') {
        return rest;
    }
    let mut depth = 0usize;
    for (i, c) in rest.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return &rest[i + 1..];
                }
            }
            _ => {}
        }
    }
    ""
}

/// The laws the prelude states (DESIGN.md sec:verification, the `using` tactic), which the page
/// does not define.
const PRELUDE: &[&str] = &["anyIntro", "anyElim", "allElim"];

#[test]
fn every_fence_of_the_mathlib_study_parses() {
    let page = page();
    // The sixteen theorems' fifteen fences, section 5's fence, and the fence of `minFac`.
    assert_eq!(extract(&page).len(), 17);
    let bad = unparsed(&page);
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

#[test]
fn a_law_with_a_product_after_a_reduction_does_not_parse() {
    // The first of the study's failures in section 5: the right operand of `><` is a postfix
    // expression, so `* (x + -1)` after `R.add` is a parse error. The second fence is the
    // geometric sum as theorem 15 writes it, with the reduction in parentheses.
    let law = |sum: &str| {
        format!(
            "law geomSum(R: CommRing(T), x: T, n: int[0..]) = {sum} * (x + -1) == \
             pow(M: R, x:, n:) + -1 proof {{ byInduction(n) }}"
        )
    };
    let sum = "(0..<n).map(i -> pow(M: R, x:, n: i)) >< R.add";
    let page = format!(
        "```zed\n{}\n```\n\n```zed\n{}\n```\n",
        law(sum),
        law(&format!("({sum})"))
    );
    let bad = unparsed(&page);
    assert_eq!(bad.len(), 1, "{bad:?}");
    assert!(
        bad[0].starts_with("docs/mathlib-study.md:1: does not parse"),
        "{bad:?}"
    );
}

#[test]
fn every_law_euclid_cites_is_written_on_the_page() {
    let page = page();
    let cites = euclid_cites(&page);
    assert_eq!(cites, ["anyIntro", "minFacPrime", "minFacDvd", "dvdFact"]);
    for name in cites.iter().filter(|c| !PRELUDE.contains(&c.as_str())) {
        assert!(
            defines(&page, name),
            "`{name}` is cited by `euclid` and written nowhere"
        );
    }
    for name in ["minFac", "minFacAux", "minFacLe", "isPrime", "fact", "dvd"] {
        assert!(defines(&page, name), "`{name}` is written nowhere");
    }
}

#[test]
fn a_cited_law_that_is_not_written_is_found() {
    let page = "```zed\nlaw euclid(n: int[0..]) = true proof { using(anyIntro, minFacPrime) }\n\
                @measure(n - (n + 0)) minFacPrime2(n: int[2..]) = n;\n```\n";
    assert_eq!(euclid_cites(page), ["anyIntro", "minFacPrime"]);
    assert!(defines(page, "minFacPrime2"));
    assert!(!defines(page, "minFacPrime"));
}

#[test]
fn parsing_the_fences_of_a_page_scales() {
    let one = "Text.\n\n```zed\nlaw minFacDvd(n: int[2..]) = dvd(minFac(n), n) proof { using(minFacAuxDvd) }\n```\n";
    let last = "```zed\nlaw euclid(n: int[0..]) = true proof { using(anyIntro, dvdFact) }\n```\n";
    let pages = inputs(500, |n| one.repeat(n) + last);
    check(
        "lexing and parsing n fences of a page, and finding names in them",
        500,
        |n| {
            let page = &pages[&n];
            assert!(unparsed(page).is_empty());
            // `euclid` is on the last line and `dvdFact` is defined nowhere, so both searches
            // read the whole page.
            assert_eq!(euclid_cites(page), ["anyIntro", "dvdFact"]);
            assert!(!defines(page, "dvdFact"));
        },
    );
}
