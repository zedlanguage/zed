//! The `split` tool of plan row ZPARSE-par: one depth scan cuts a program into segments of whole
//! items, each segment is parsed alone, and the items must be those of the whole-file parse. The
//! tests run it on the impl corpus, on damaged copies of each corpus file, on small grammars
//! that show which pairs keep a cut away, and at n and 8n.

use zed_tests::scaling::{check, inputs};
use zed_tools::spec::Spec;
use zed_tools::split::{Parsed, Splitter, compare, run, split_parse, whole_parse, zed_files};
use zed_tools::syntax::lex;
use zedc::parse::{Grammar, Kind};

use super::{design, fence, spec_dir, tool};

/// The real grammars, read from a spec written for the test.
fn real(name: &str) -> Spec {
    let dir = spec_dir(name, &design(""), "");
    Spec::open(&dir.root()).expect("the real grammars")
}

/// The tokens of `text` without `END`, as kind and text.
fn tokens(spec: &Spec, text: &str) -> Option<Vec<(Kind, String)>> {
    let toks = lex(&spec.lexical, text).ok()?;
    let n = toks.0.len() - 1;
    Some(
        toks.0[..n]
            .iter()
            .map(|t| (t.kind, t.text.clone()))
            .collect(),
    )
}

/// `toks` borrowed, as the tool takes them.
fn view(toks: &[(Kind, String)]) -> Vec<(Kind, &str)> {
    toks.iter().map(|(k, t)| (*k, t.as_str())).collect()
}

/// The `.zed` programs of this repository that lex, as tokens.
fn corpus(spec: &Spec) -> Vec<(String, Vec<(Kind, String)>)> {
    let dir = format!("{}/zed", zed_tools::impl_root());
    let files = zed_files(&dir).expect("the zed directory");
    assert!(files.len() > 50, "too few corpus files: {}", files.len());
    files
        .into_iter()
        .filter_map(|f| {
            let text = std::fs::read_to_string(&f).expect("a corpus file");
            tokens(spec, &text).map(|t| (f, t))
        })
        .collect()
}

#[test]
fn split_parse_equals_whole_file_parse_on_the_corpus() {
    let body = format!(
        "{}{}",
        fence("double(x: int) -> int = x * 2;"),
        fence("f(x: int) -> int { x + 1 }\ng(y: int) = f(y);")
    );
    let dir = spec_dir("split_corpus", &design(&body), "");
    let (outcome, out) = tool(run, &[&dir.root()]);
    assert_eq!(outcome, Ok(true), "{out}");
    assert!(out.contains("RESULT: OK"), "{out}");
    assert!(!out.contains("DIFFERS"), "{out}");
    assert!(out.contains("unbalanced 0"), "{out}");
}

#[test]
fn split_parse_equals_whole_file_parse_on_damaged_programs() {
    let spec = real("split_damaged");
    let sp = Splitter::new(&spec.syntactic, "Item").expect("the real grammar splits");
    let mut cases = 0;
    for (file, toks) in corpus(&spec) {
        let n = toks.len();
        if n < 4 {
            continue;
        }
        let mut damaged = Vec::new();
        for at in [n / 4, n / 2, 3 * n / 4] {
            let mut t = toks.clone();
            t.remove(at);
            damaged.push(t);
        }
        let mut t = toks.clone();
        t.insert(n / 3, toks[n / 3].clone());
        damaged.push(t);
        for t in damaged {
            let c = compare(&sp, &spec.syntactic, &view(&t)).expect("rules Unit and Item");
            assert!(c.same && c.sound, "{file}: {c:?}");
            cases += 1;
        }
    }
    assert!(cases > 200, "too few damaged programs: {cases}");
}

/// Cuts at every position at depth 0, which the depth scan alone, without the pairs, would give.
fn every_cut(toks: &[(Kind, &str)]) -> Vec<usize> {
    let mut cuts = vec![0];
    let mut depth = 0usize;
    for (i, &(k, t)) in toks.iter().enumerate() {
        if i > 0 && depth == 0 {
            cuts.push(i);
        }
        if k == Kind::Op {
            match t {
                "(" | "[" | "{" => depth += 1,
                ")" | "]" | "}" => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
    }
    cuts
}

#[test]
fn cuts_that_ignore_the_pairs_give_a_different_parse() {
    // The comparison is what the corpus test rests on: a cut inside an item must show as a
    // difference.
    let spec = real("split_control");
    let mut differs = 0;
    for (_, toks) in corpus(&spec) {
        let t = view(&toks);
        let whole = whole_parse(&spec.syntactic, "Unit", &t).expect("rule Unit");
        let split = split_parse(&spec.syntactic, "Item", &t, &every_cut(&t)).expect("rule Item");
        differs += usize::from(whole != split);
    }
    assert!(differs > 30, "only {differs} programs differ");
}

#[test]
fn the_real_grammar_cuts_between_items_that_end_in_a_semicolon_or_a_block() {
    let spec = real("split_cuts");
    let sp = Splitter::new(&spec.syntactic, "Item").expect("the real grammar splits");
    let text = "a = 1;\nf(x: int) -> int { x + 1 }\nb = f(2);\n";
    let toks = tokens(&spec, text).expect("lexes");
    let t = view(&toks);
    let cuts = sp.cuts(&t).expect("balanced");
    let starts: Vec<&str> = cuts.iter().map(|&c| t[c].1).collect();
    assert_eq!(starts, ["a", "f", "b"]);
    let c = compare(&sp, &spec.syntactic, &t).expect("rules Unit and Item");
    assert!(
        c.same && c.sound && c.parsed && c.missed.is_empty(),
        "{c:?}"
    );
}

#[test]
fn a_word_that_can_follow_a_block_inside_an_item_keeps_the_cut_away() {
    // `xs >< { … } tree` reads `tree` after `}` (ReducePolicy), so an item named `tree` after a
    // block body is not cut from the item before it; the parse is still the same.
    let spec = real("split_tree");
    let sp = Splitter::new(&spec.syntactic, "Item").expect("the real grammar splits");
    let text = "f(x: int) -> int { x + 1 }\ntree = f(2);\n";
    let toks = tokens(&spec, text).expect("lexes");
    let t = view(&toks);
    let c = compare(&sp, &spec.syntactic, &t).expect("rules Unit and Item");
    assert!(c.same && c.sound && c.parsed, "{c:?}");
    assert_eq!(c.segments, 1, "{c:?}");
    assert_eq!(c.missed, [("}".to_string(), "IDENT".to_string(), 13)]);
}

#[test]
fn an_empty_program_and_unbalanced_brackets_give_the_same_parse() {
    let spec = real("split_corners");
    let sp = Splitter::new(&spec.syntactic, "Item").expect("the real grammar splits");
    let c = compare(&sp, &spec.syntactic, &[]).expect("rules Unit and Item");
    assert!(c.same && c.sound && c.parsed && c.segments == 1, "{c:?}");
    for text in [
        "a = (1;\nb = 2;\n",
        "a = 1);\nb = 2;\n",
        "a = 1;\n}\nb = 2;\n",
    ] {
        let toks = tokens(&spec, text).expect("lexes");
        let t = view(&toks);
        assert_eq!(sp.cuts(&t), None, "{text}");
        let c = compare(&sp, &spec.syntactic, &t).expect("rules Unit and Item");
        assert!(
            c.same && !c.balanced && !c.parsed && c.segments == 1,
            "{text}: {c:?}"
        );
    }
    // An error in the second item: the split parse names the same failure as the whole one.
    let toks = tokens(&spec, "a = 1;\nb = = 2;\nc = 3;\n").expect("lexes");
    let t = view(&toks);
    let c = compare(&sp, &spec.syntactic, &t).expect("rules Unit and Item");
    assert!(c.same && !c.parsed, "{c:?}");
    assert!(matches!(
        split_parse(&spec.syntactic, "Item", &t, &sp.cuts(&t).expect("balanced")),
        Ok(Parsed::Failed(6, _))
    ));
}

/// A small grammar over tokens with `Unit = Item* END`.
fn small(item: &str) -> Grammar {
    let text = format!("Unit = Item* END  L1\n{item}");
    Grammar::read_open(&[&text]).expect("a small grammar")
}

const XY: &[(Kind, &str)] = &[(Kind::Ident, "x"), (Kind::Ident, "y"), (Kind::Op, ";")];

#[test]
fn a_lookahead_pairs_the_end_of_an_item_with_the_start_of_the_next() {
    // `x` then `y ;`: two items. With `&'y'` after `x` the item `x` tests the token after its
    // end, so a cut between them would change the parse; the scan does not cut there.
    let g = small("Item = 'x' &'y'  L1\n  | 'y' ';'  L1\n");
    let sp = Splitter::new(&g, "Item").expect("splits");
    assert_eq!(sp.cuts(XY), Some(vec![0]));
    let c = compare(&sp, &g, XY).expect("rules");
    assert!(c.same && c.parsed && c.items == 2, "{c:?}");
    let g = small("Item = 'x'  L1\n  | 'y' ';'  L1\n");
    let sp = Splitter::new(&g, "Item").expect("splits");
    assert_eq!(sp.cuts(XY), Some(vec![0, 1]));
    let c = compare(&sp, &g, XY).expect("rules");
    assert!(c.same && c.parsed && c.missed.is_empty(), "{c:?}");
}

#[test]
fn a_grammar_the_scan_cannot_read_is_reported() {
    for (item, problem) in [
        ("Item = '(' 'x'  L1\n", "bracket"),
        ("Item = 'x' ')' 'y'  L1\n", "bracket"),
        ("Item = ('(' 'x')*  L1\n", "bracket"),
        ("Item = 'x'?  L1\n", "no tokens"),
        ("Item = Missing  L1\n", "undefined"),
        ("Item = '(' 'x' ']'  L1\n", "closes another kind"),
    ] {
        let g = small(item);
        match Splitter::new(&g, "Item") {
            Err(e) => assert!(e.contains(problem), "{item}: {e}"),
            Ok(_) => panic!("{item}: no problem reported"),
        }
    }
}

/// `n` items, half with a block body.
fn items(n: usize) -> String {
    (0..n)
        .map(|i| {
            if i % 2 == 0 {
                format!("v{i} = ({i} + 1) * 2;\n")
            } else {
                format!("f{i}(x: int) -> int {{ x + {i} }}\n")
            }
        })
        .collect()
}

#[test]
fn the_scan_and_the_split_parse_scale_with_the_number_of_items() {
    let spec = real("split_scaling");
    let sp = Splitter::new(&spec.syntactic, "Item").expect("the real grammar splits");
    let toks = inputs(2000, |n| tokens(&spec, &items(n)).expect("lexes"));
    check("split: the depth scan", 2000, |n| {
        let t = view(&toks[&n]);
        assert_eq!(sp.cuts(&t).expect("balanced").len(), n);
    });
    check("split: the split parse", 2000, |n| {
        let t = view(&toks[&n]);
        let cuts = sp.cuts(&t).expect("balanced");
        assert!(matches!(
            split_parse(&spec.syntactic, "Item", &t, &cuts),
            Ok(Parsed::Items(i)) if i.len() == n
        ));
    });
}
