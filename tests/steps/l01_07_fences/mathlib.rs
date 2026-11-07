//! Items MATHLIB-minfac and MATHLIB-euclid-gaps: every `zed` fence of docs/mathlib-study.md lexes
//! and parses as a unit at the top ring, and each law that the proofs of `euclid`, `euclidChain`,
//! `minFacPrime` and `minFacMin` cite outside the prelude is written in one of them. This checks
//! syntax only: `minFac`'s test table needs recursion (step L6.7) and its laws need layer L15, as
//! the page says. Item MATHLIB-allintro-spec: the prelude laws are those step L15.7 of DESIGN.md
//! names and sec:verification states, and DESIGN.md states `allIntro` as the page writes it.

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

/// Whether a fence of `page` defines `name` at its top level, as a function (`name(` at the start
/// of an unindented line, after any annotations) or as a law (`law name(`). An indented line, such
/// as a claim of a `#chain` that starts with a call of `name`, defines nothing.
fn defines(page: &str, name: &str) -> bool {
    let call = format!("{name}(");
    let law = format!("law {name}(");
    extract(page).iter().any(|f| {
        f.text.lines().any(|l| {
            let mut rest = l;
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

/// The text of the law `name` in a fence of `page`: its first line, `law name(` unindented, and
/// the indented lines after it up to and including the first line that starts with `}`.
fn law_text(page: &str, name: &str) -> Option<String> {
    let head = format!("law {name}(");
    extract(page).into_iter().find_map(|f| {
        let mut lines = f.text.lines().skip_while(|l| !l.starts_with(&head));
        let mut text = lines.next()?.to_string();
        for l in lines {
            if !(l.starts_with(' ') || l.starts_with('}')) {
                break;
            }
            text.push('\n');
            text.push_str(l);
            if l.starts_with('}') {
                break;
            }
        }
        Some(text)
    })
}

/// The laws that `text` cites, in order: the rule of each `#use(rule: …)`, then each name in each
/// `using(…)` list.
fn cited(text: &str) -> Vec<&str> {
    let uses = text.match_indices("#use(rule: ").map(|(i, m)| {
        let rest = &text[i + m.len()..];
        let end = rest
            .find(|c: char| !(c.is_alphanumeric() || c == '_'))
            .unwrap_or(rest.len());
        &rest[..end]
    });
    let usings = text.match_indices("using(").flat_map(|(i, m)| {
        let rest = &text[i + m.len()..];
        rest.split_once(')')
            .map_or(rest, |(list, _)| list)
            .split(',')
            .map(str::trim)
    });
    uses.chain(usings).collect()
}

/// The laws the prelude states (DESIGN.md sec:verification, the `using` tactic) and step L15.7
/// builds, in the order step L15.7 names them. The page writes `allIntro` too, with its proof.
const PRELUDE: &[&str] = &["anyIntro", "anyElim", "allElim", "allIntro"];

#[test]
fn every_fence_of_the_mathlib_study_parses() {
    let page = page();
    // The sixteen theorems' fifteen fences, section 5's fence, the fence of `minFac`, and the
    // fence of the divisibility laws, `allIntro` and `euclidChain`.
    assert_eq!(extract(&page).len(), 18);
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
    assert_eq!(
        cites,
        [
            "anyIntro",
            "minFacPrime",
            "minFacDvd",
            "minFacLe",
            "dvdRefl",
            "dvdFact",
            "notDvdSucc"
        ]
    );
    for name in cites.iter().filter(|c| !PRELUDE.contains(&c.as_str())) {
        assert!(
            defines(&page, name),
            "`{name}` is cited by `euclid` and written nowhere"
        );
    }
    for name in [
        "minFac",
        "minFacAux",
        "isPrime",
        "fact",
        "dvd",
        "dvdTrans",
        "dvdMulRight",
        "dvdMulLeftOfDvd",
        "allIntro",
    ] {
        assert!(defines(&page, name), "`{name}` is written nowhere");
    }
}

#[test]
fn every_law_the_proofs_of_euclid_and_minfac_cite_is_written_on_the_page() {
    let page = page();
    for law in ["euclid", "euclidChain", "minFacPrime", "minFacMin"] {
        let text = law_text(&page, law).unwrap_or_else(|| panic!("`{law}` is written nowhere"));
        let cites = cited(&text);
        assert!(!cites.is_empty(), "`{law}` cites no law");
        for name in cites {
            assert!(
                PRELUDE.contains(&name) || defines(&page, name),
                "`{name}` is cited by `{law}` and written nowhere"
            );
        }
    }
    // The chain cites exactly the laws that `euclid`'s `using` list names.
    let chain = law_text(&page, "euclidChain").expect("`euclidChain` is written");
    let mut chain_cites = cited(&chain);
    chain_cites.sort_unstable();
    chain_cites.dedup();
    let mut using = euclid_cites(&page);
    using.sort_unstable();
    assert_eq!(chain_cites, using);
}

#[test]
fn a_cited_law_that_is_not_written_is_found() {
    let page = "```zed\nlaw euclid(n: int[0..]) = true proof { using(anyIntro, minFacPrime) }\n\
                @measure(n - (n + 0)) minFacPrime2(n: int[2..]) = n;\n\
                law chain(n: int[0..]) = true proof {\n  #chain(steps: [\n    \
                #use(rule: minFacDvd, args: [n]),\n  ], claims: [\n    minFacDvd(n),\n  ])\n}\n\
                law after(n: int[0..]) = true proof { using(dvdTrans) }\n```\n";
    assert_eq!(euclid_cites(page), ["anyIntro", "minFacPrime"]);
    assert!(defines(page, "minFacPrime2"));
    assert!(!defines(page, "minFacPrime"));
    // A claim line that starts with a call is indented, so it defines nothing.
    assert!(!defines(page, "minFacDvd"));
    // The law's text ends at its closing brace, before the next law's `using`.
    let chain = law_text(page, "chain").expect("`chain` is on the page");
    assert_eq!(cited(&chain), ["minFacDvd"]);
    assert_eq!(
        cited(&law_text(page, "euclid").unwrap()),
        ["anyIntro", "minFacPrime"]
    );
    assert_eq!(law_text(page, "missing"), None);
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
            let text = law_text(page, "euclid").expect("`euclid` is on the last line");
            assert_eq!(cited(&text), ["anyIntro", "dvdFact"]);
        },
    );
}

/// The names in the first list of laws after `head` in `text`: each backquoted name up to the
/// `;` that ends the list.
fn named_after<'a>(text: &'a str, head: &str) -> Vec<&'a str> {
    let (_, rest) = text
        .split_once(head)
        .unwrap_or_else(|| panic!("`{head}` is in the text"));
    let list = rest.split_once(';').map_or(rest, |(list, _)| list);
    list.split('`').skip(1).step_by(2).collect()
}

#[test]
fn the_prelude_laws_are_those_design_states() {
    let Some(spec) = zed_tests::spec::dir("the prelude laws against DESIGN.md") else {
        return;
    };
    let design = std::fs::read_to_string(spec.join("DESIGN.md")).expect("DESIGN.md is readable");
    // Step L15.7 builds the prelude laws (item MATHLIB-allintro-spec added `allIntro`).
    let step = design
        .lines()
        .find(|l| l.starts_with("L15.7. "))
        .expect("DESIGN.md has step L15.7");
    assert_eq!(named_after(step, "the prelude laws "), PRELUDE);
    let reach = step
        .split_once(" reach proof grade")
        .expect("step L15.7's test names the laws that reach proof grade")
        .0;
    let reach = reach.rsplit_once(';').map_or(reach, |(_, r)| r);
    let reach: Vec<&str> = reach.split('`').skip(1).step_by(2).collect();
    assert_eq!(reach, PRELUDE);
    // sec:verification states each law, `allIntro` as the page writes it, without its proof.
    let states = design
        .lines()
        .find_map(|l| l.split_once("The prelude also states ").map(|(_, r)| r))
        .expect("DESIGN.md states the prelude laws");
    let states = states.split_once(". ").map_or(states, |(s, _)| s);
    for name in PRELUDE {
        assert!(
            states.contains(&format!("`{name}`")) || states.contains(&format!("law {name}(")),
            "DESIGN.md does not state `{name}`"
        );
    }
    let page = page();
    let written = page
        .lines()
        .find(|l| l.starts_with("law allIntro("))
        .and_then(|l| l.split_once(" proof {"))
        .expect("the page writes `allIntro` with a proof")
        .0;
    assert!(
        states.contains(&format!("`{written}`")),
        "DESIGN.md states `allIntro` otherwise than the page: `{written}`"
    );
}
