//! The shape of the trees of sec:grammar: a left-associative operator is a left-recursive rule,
//! a `~` alternative leaves no node of its own, and each form is a rule of its own, so a message
//! names the form written.

use std::collections::BTreeSet;
use std::path::PathBuf;

use zed_tests::trees::sx;
use zedc::ast::build;
use zedc::lex::lex;
use zedc::parse::Expr as Peg;
use zedc::parse::{Grammar, TOP, Tree, grammar, parse, parse_unit, parse_with};

/// The bracketing of `text` as `start`.
fn tree(text: &str, start: &str) -> String {
    let tokens = lex(text).unwrap();
    sx(text, &tokens, &parse(text, &tokens, start, TOP).unwrap())
}

/// The syntax tree of the expression `text`.
fn expr(text: &str) -> String {
    let tokens = lex(text).unwrap();
    let parsed = parse(text, &tokens, "Expr", TOP).unwrap();
    build(text, &tokens, &parsed).unwrap().to_string()
}

/// The rule names of the nodes of the parse of `text`, root first.
fn nodes(text: &str, start: &str) -> Vec<&'static str> {
    let tokens = lex(text).unwrap();
    let parsed = parse(text, &tokens, start, TOP).unwrap();
    (0..parsed.nodes.len())
        .rev()
        .map(|n| parsed.name(n))
        .collect()
}

#[test]
fn a_price_after_discount_and_tax_subtracts_from_the_left() {
    assert_eq!(
        tree("price - discount - tax + fee", "Expr"),
        "(((price - discount) - tax) + fee)"
    );
    assert_eq!(
        expr("price - discount - tax + fee"),
        "(+ (- (- price discount) tax) fee)"
    );
}

#[test]
fn a_rate_of_a_rate_divides_from_the_left() {
    assert_eq!(expr("km / hours / 2"), "(/ (/ km hours) 2)");
}

#[test]
fn a_power_of_a_power_stays_right_associative() {
    assert_eq!(tree("2 ^ 3 ^ 2", "Expr"), "(2 ^ (3 ^ 2))");
}

#[test]
fn a_comparison_chain_stays_flat() {
    assert_eq!(tree("0 < x <= 10", "Expr"), "(0 < x <= 10)");
    assert_eq!(tree("a == b == c", "Expr"), "(a == b == c)");
}

#[test]
fn a_call_chain_reads_from_the_left() {
    assert_eq!(
        expr("orders.paid(2024)[0].total"),
        "(. (index (call (. orders paid) 2024) 0) total)"
    );
}

#[test]
fn a_name_leaves_no_node_on_the_rungs_of_the_ladder() {
    assert_eq!(nodes("total", "Expr"), ["Expr", "Name"]);
}

#[test]
fn a_sum_has_one_node_per_operator() {
    let names = nodes("a + b + c", "Expr");
    assert_eq!(names.iter().filter(|n| **n == "Additive").count(), 2);
    assert!(!names.contains(&"Multiplicative"), "{names:?}");
    assert!(!names.contains(&"Primary"), "{names:?}");
}

#[test]
fn a_type_union_prints_flat_and_keeps_its_grouping() {
    assert_eq!(
        tree("Paid | Pending | Failed", "Type"),
        "((Paid | Pending) | Failed)"
    );
    assert_eq!(
        tree("Paid | (Pending | Failed)", "Type"),
        "(Paid | (( (Pending | Failed) )))"
    );
}

#[test]
fn an_alternative_past_its_ring_is_not_tried_through_a_mark() {
    let g = Grammar::read(&["E = ~T L5\n  | 'x' L1\nT = 'y' L5\n"]).unwrap();
    let text = "y";
    let tokens = lex(text).unwrap();
    assert!(parse_with(&g, text, &tokens, "E", 1).is_err());
    assert!(parse_with(&g, text, &tokens, "E", 5).is_ok());
}

#[test]
fn a_marked_alternative_gives_the_node_of_the_rule_it_names() {
    let g = Grammar::read(&["E = &'y' ~T L1\nT = 'y' L1\n"]).unwrap();
    let text = "y";
    let tokens = lex(text).unwrap();
    let parsed = parse_with(&g, text, &tokens, "E", TOP).unwrap();
    assert_eq!(parsed.nodes.len(), 1);
    assert_eq!(parsed.nodes[parsed.root].kids, [] as [usize; 0]);
}

#[test]
fn a_mark_is_refused_outside_the_top_of_its_alternative() {
    for (rule, want) in [
        (
            "E = 'x' (~T) L1\n",
            "a ~ mark must stand at the top of its alternative",
        ),
        ("E = ~T ~T L1\n", "an alternative holds at most one ~ mark"),
        ("E = ~'x' L1\n", "a ~ mark must be on a plain rule name"),
        ("E = ~IDENT L1\n", "a ~ mark must be on a plain rule name"),
        ("E = 'x' ~T L1\n", "beside a ~ mark"),
        ("E = ~T L2\n", "E marks T at L2, above its lowest layer L1"),
    ] {
        let text = format!("{rule}T = 'y' L1\n");
        let err = Grammar::read(&[&text]).unwrap_err().to_string();
        assert!(err.contains(want), "{rule}: {err}");
    }
}

/// `1 + 1 + ... + 2` and `a.b.b...b`, each of `n` operators.
pub(super) fn chains(n: usize) -> [String; 2] {
    ["1 + ".repeat(n) + "2", "a".to_string() + &".b".repeat(n)]
}

/// `text` is lexed, parsed and built.
pub(super) fn builds(text: &str) {
    let tokens = lex(text).unwrap();
    let parsed = parse(text, &tokens, "Expr", TOP).unwrap();
    build(text, &tokens, &parsed).unwrap();
}

/// Each tree of [`chains`] has one nesting per operator; here a few operators build, and a
/// hundred thousand, far more frames than a test thread's 2 MiB stack holds, build in
/// `bench/stack.rs`.
#[test]
fn a_chain_of_a_few_operators_and_members_builds() {
    for n in [1, 2, 9] {
        for text in chains(n) {
            builds(&text);
        }
    }
}

/// `^` is written without spaces (`0..=2^48`), and spaces around it are accepted: each spaced
/// form builds the same tree as the unspaced one.
#[test]
fn spaces_around_a_power_change_nothing() {
    let cases = [
        ("2 ^ 48", "2^48"),
        ("x ^ 2", "x^2"),
        ("(-2) ^ 2", "(-2)^2"),
        ("-x ^ 2", "-x^2"),
        ("2 ^ -1", "2^-1"),
        ("a ^ b ^ c", "a^b^c"),
        ("(a ^ b) ^ c", "(a^b)^c"),
        ("(x + 1r) ^ 2", "(x + 1r)^2"),
        ("x * 2 ^ k", "x * 2^k"),
        ("data.len in 0..=2 ^ 48", "data.len in 0..=2^48"),
    ];
    for (spaced, unspaced) in cases {
        assert_eq!(expr(spaced), expr(unspaced), "{spaced}");
    }
    assert_eq!(expr("-x^2"), "(- (^ x 2))");
    assert_eq!(expr("2^-1"), "(^ 2 (- 1))");
    assert_eq!(expr("a^b^c"), "(^ a (^ b c))");
}

/// The positions in `kids` (the rules of a node's children, in order) that a match of `e` from
/// position `i` can end at, reading a child for each rule `e` names and nothing for a literal,
/// a token kind or a lookahead, whose children the parser drops (`Frame::And`, `Frame::Not`
/// truncate its children to their mark). `stands[r]` holds the rules whose node is a match of
/// `r`: `r`, and through each `~R` alternative of `r` the rules that stand for `R`.
fn ends(e: &Peg, kids: &[usize], i: usize, stands: &[BTreeSet<usize>]) -> BTreeSet<usize> {
    let many = |e: &Peg, from: BTreeSet<usize>| {
        // Every end reached by zero or more matches: each new end is matched from once, and
        // the ends lie in 0..=kids.len(), so this stops.
        let (mut all, mut todo) = (from.clone(), from.into_iter().collect::<Vec<_>>());
        while let Some(j) = todo.pop() {
            for k in ends(e, kids, j, stands) {
                if all.insert(k) {
                    todo.push(k);
                }
            }
        }
        all
    };
    let seq = |es: &[Peg], from: BTreeSet<usize>| {
        es.iter().fold(from, |at, e| {
            at.into_iter()
                .flat_map(|j| ends(e, kids, j, stands))
                .collect()
        })
    };
    match e {
        Peg::Rule(r) => match kids.get(i) {
            Some(k) if stands[*r].contains(k) => BTreeSet::from([i + 1]),
            _ => BTreeSet::new(),
        },
        Peg::Seq(es) => seq(es, BTreeSet::from([i])),
        Peg::Choice(es) => es.iter().flat_map(|e| ends(e, kids, i, stands)).collect(),
        Peg::Star(x) => many(x, BTreeSet::from([i])),
        Peg::Plus(x) => many(x, ends(x, kids, i, stands)),
        Peg::Sep(two) => {
            let [sep, x] = &**two;
            let first = ends(x, kids, i, stands);
            many(&Peg::Seq(vec![sep.clone(), x.clone()]), first)
        }
        Peg::Opt(x) => {
            let mut out = ends(x, kids, i, stands);
            out.insert(i);
            out
        }
        Peg::SetHead(x) | Peg::ClearHead(x) => ends(x, kids, i, stands),
        Peg::And(_) | Peg::Not(_) | Peg::Lit(_) | Peg::Kind(_) | Peg::Head => BTreeSet::from([i]),
        Peg::Class(_) | Peg::Any | Peg::Undefined(_) => {
            unreachable!("the parser's grammar is read by `Grammar::read`")
        }
    }
}

/// The rule each `~R` alternative passes to.
fn passed(e: &Peg) -> Option<usize> {
    match e {
        Peg::Rule(r) => Some(*r),
        Peg::Seq(es) => es.iter().find_map(passed),
        _ => None,
    }
}

/// Every `.zed` unit under `zed/` (the corpus, the prelude and the fences) and in the steps'
/// `zed/` folders, the folders `l01_29_repairs_and_printing::order::units` walks and more.
fn units() -> Vec<(PathBuf, String)> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut dirs = vec![root.join("../zed")];
    for step in std::fs::read_dir(root.join("steps")).unwrap() {
        dirs.push(step.unwrap().path().join("zed"));
    }
    let mut out = Vec::new();
    while let Some(dir) = dirs.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for e in entries {
            let path = e.unwrap().path();
            if path.is_dir() {
                dirs.push(path);
            } else if path.extension().is_some_and(|x| x == "zed") {
                let text = zedc::source::load(&std::fs::read(&path).unwrap()).unwrap();
                out.push((path, text));
            }
        }
    }
    out.sort();
    out
}

/// The premise of the grammar-shape `unreachable!` and `expect` sites of the syntax-tree
/// builder (zedc-syntax `ast/mod.rs`, "Why the shape of a node is known"): every node the
/// parse builds is of an alternative that builds a node, and its children, read by rule, are a
/// match of that alternative's expression, each child a node of the rule the expression names
/// there or of a rule that stands for it through `~` alternatives. Checked on every node
/// reached from the root, and from the roots of the string holes, of every corpus and step
/// unit and of every case of `zed/grammar/cases.txt` that parses; the rules with an alternative
/// that builds a node but no node in any of these are printed, since no node of theirs is
/// checked here.
#[test]
fn every_node_s_children_match_its_alternative() {
    let g = grammar();
    let n = g.rules.len();
    // `stands[r]`: `r` and every rule a chain of `~` alternatives from `r` reaches, found by
    // a search with a visited set from each rule (O(r · a) for a alternatives in all).
    let mut stands = vec![BTreeSet::new(); n];
    for (r, set) in stands.iter_mut().enumerate() {
        let mut todo = vec![r];
        while let Some(q) = todo.pop() {
            if set.insert(q) {
                let alts = g.rules[q].alts.iter().filter(|a| a.pass);
                todo.extend(alts.filter_map(|a| passed(&a.expr)));
            }
        }
    }
    let mut seen = vec![false; n];
    let mut checked = 0usize;
    let mut check = |tree: &Tree, from: &str| {
        let mut trees = vec![tree];
        while let Some(t) = trees.pop() {
            trees.extend(&t.holes);
            let mut stack = vec![t.root];
            while let Some(m) = stack.pop() {
                let node = &t.nodes[m];
                let alt = &g.rules[node.rule].alts[node.alt];
                let name = &g.rules[node.rule].name;
                assert!(!alt.pass, "{from}: a node of a `~` alternative of {name}");
                let kids: Vec<usize> = node.kids.iter().map(|&k| t.nodes[k].rule).collect();
                let names: Vec<&str> = kids.iter().map(|&k| g.rules[k].name.as_str()).collect();
                assert!(
                    ends(&alt.expr, &kids, 0, &stands).contains(&kids.len()),
                    "{from}: a node of {name}, alternative {}, has the children {names:?}",
                    node.alt
                );
                seen[node.rule] = true;
                checked += 1;
                stack.extend(&node.kids);
            }
        }
    };
    for (path, text) in units() {
        // A fence sketch may hold text the lexer refuses (`…`); it builds no tree.
        let Ok(tokens) = lex(&text) else {
            continue;
        };
        check(
            &parse_unit(&text, &tokens, TOP).0,
            &path.display().to_string(),
        );
    }
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let cases = std::fs::read_to_string(root.join("../zed/grammar/cases.txt")).unwrap();
    for line in cases
        .lines()
        .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
    {
        // `Rule[@ring] ::: text ::: tree`, a line break written `⏎`, as `cases.rs` reads it.
        let [start, text, _] = line.split(" ::: ").map(str::trim).collect::<Vec<_>>()[..] else {
            panic!("a case is `Rule ::: text ::: tree`: {line}");
        };
        let (start, ring) = match start.split_once('@') {
            Some((s, r)) => (s, r.parse().unwrap()),
            None => (start, TOP),
        };
        let text = text.replace('⏎', "\n");
        if let Ok(tokens) = lex(&text)
            && let Ok(tree) = parse(&text, &tokens, start, ring)
        {
            check(&tree, line);
        }
    }
    // The rules with a node that neither the units nor the cases build. `AnnotEnd`, `KeyOp`
    // and `JoinExpr` are read only inside `&` and `!`, whose children are dropped, so no node
    // of theirs is ever kept.
    let written = [
        ("Unit", "initial s: int = 0 with carryForward;"),
        (
            "Unit",
            "main(m: MainArgs) { m.stdout <- m.args[0] else #outOfBounds -> \"\"; }\n\
             test with main::args = \"a\", out = 1 { \"\" -> \"a\\n\" }",
        ),
        ("Expr", "a ~max~ b ~min~ c"),
        ("Unit", "x: !int = 1;"),
        ("Unit", "x: 2^3 * 5 = 40;"),
        ("Unit", "x: ? = 1;"),
        ("DocFence", "f: int -> int\nf(1)"),
    ];
    for (start, text) in written {
        let tokens = lex(text).unwrap();
        let tree = parse(text, &tokens, start, TOP).unwrap_or_else(|e| panic!("{text}: {e}"));
        check(&tree, text);
    }
    let unseen: Vec<&str> = (0..n)
        .filter(|&r| !seen[r] && g.rules[r].alts.iter().any(|a| !a.pass))
        .map(|r| g.rules[r].name.as_str())
        .collect();
    eprintln!("{checked} nodes checked; rules with no node checked: {unseen:?}");
    assert!(checked > 0);
}
