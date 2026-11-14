//! The grammar reader refuses each malformed grammar line with a message naming the fault, and
//! the engine runs a grammar over characters (the grammar tools' lexer, read by
//! `Grammar::read_open`): character classes, `ANY`, an undefined name, a token kind, an empty
//! sequence, and a lookahead asked from outside.

use zedc::parse::{Grammar, Input, Kind, Parser};

/// Each line is refused, and the message names the fault.
#[test]
fn each_malformed_grammar_line_is_refused() {
    // (grammar, read over characters too, part of the message)
    let cases: &[(&str, bool, &str)] = &[
        ("E = 'x' ) L1", false, "trailing text"),
        ("E = 'x L1", false, "an unclosed literal"),
        ("E = [a L1", true, "an unclosed class"),
        ("E = 'x' ; L1", false, "is no grammar token"),
        (
            "E = [a] L1",
            false,
            "a character class in a grammar over tokens",
        ),
        ("E = [a--b] L1", true, "holds `--`"),
        ("E = head('x' L1", false, "`head(` is not closed"),
        ("E = nest('x' L1", false, "`nest(` is not closed"),
        ("E = ('x' L1", false, "`(` is not closed"),
        ("E = * L1", false, "unexpected '*'"),
        ("E = 'x' ! L1", false, "an expression is missing"),
        ("E = 'x'", false, "no layer at the end"),
        ("E = 'x' L1x", false, "no layer at the end"),
        (
            "E = 'x' L1\nE = 'y' L1",
            false,
            "the rule E is defined twice",
        ),
        ("E = F L1", false, "the rule F is not defined"),
        ("| 'x' L1", false, "an alternative before any rule"),
        ("E = ~T | 'x' L1\nT = 'y' L1", false, "beside a ~ mark"),
    ];
    for &(text, open, want) in cases {
        let got = if open {
            Grammar::read_open(&[text])
        } else {
            Grammar::read(&[text])
        };
        match got {
            Ok(_) => panic!("{text:?} was read"),
            Err(e) => assert!(e.contains(want), "{text:?}: {e}"),
        }
    }
}

/// What reads: a layer followed by a comment, a mark on an undefined name in an open grammar,
/// and every token kind the grammar names.
#[test]
fn the_edge_forms_of_a_grammar_line_are_read() {
    let g = Grammar::read(&["E = 'x' L1 -- a comment\n"]).unwrap();
    assert_eq!(g.rules[0].alts[0].layer, 1);
    let g = Grammar::read_open(&["E = ~Missing L1\n"]).unwrap();
    assert!(g.rules[0].alts[0].pass);
    for name in [
        "IDENT", "WILD", "INT", "FLOAT", "RAT", "STRING", "ATOM", "ANNOT", "END",
    ] {
        let g = Grammar::read(&[&format!("E = {name} L1\n")]).unwrap();
        match &g.rules[0].alts[0].expr {
            zedc::parse::Expr::Kind(k) => assert_eq!(k.name(), name),
            e => panic!("{name}: {e:?}"),
        }
    }
}

/// The engine over characters: what each item matches, and what a failure expected.
#[test]
fn the_engine_reads_a_grammar_over_characters() {
    let g = Grammar::read_open(&[concat!(
        "Word = [a-z_] [a-z0-9]* L1\n",
        "All = ANY* L1\n",
        "Esc = [\\n\\t] '\\0' L1\n",
        "Dash = [-a] [a-] L1\n",
        "Undef = Missing L1\n",
        "Tok = IDENT L1\n",
        "Empty = () L1\n",
    )])
    .unwrap();
    let run = |rule: &str, text: &str| {
        let chars: Vec<char> = text.chars().collect();
        let mut p = Parser::new(&g, 1, &chars[..]);
        let end = p
            .rule_node(g.rule(rule).unwrap(), 0, false)
            .map(|(end, _)| end);
        let expected: Vec<String> = p.expected().iter().map(|e| format!("{e:?}")).collect();
        (end, p.far, expected)
    };
    assert_eq!(run("Word", "ab9").0, Some(3));
    assert_eq!(run("Word", "_").0, Some(1));
    let (end, far, expected) = run("Word", "9a");
    assert_eq!((end, far), (None, 0));
    assert!(expected.contains(&"Class".to_string()), "{expected:?}");
    let (end, far, expected) = run("All", "xyz");
    assert_eq!((end, far), (Some(3), 3));
    assert!(
        expected.contains(&r#"Name("ANY")"#.to_string()),
        "{expected:?}"
    );
    assert_eq!(run("Esc", "\n\0").0, Some(2));
    assert_eq!(run("Esc", "\t\0").0, Some(2));
    assert_eq!(run("Esc", "n0").0, None);
    assert_eq!(run("Dash", "--").0, Some(2));
    assert_eq!(run("Dash", "aa").0, Some(2));
    assert_eq!(run("Dash", "b-").0, None);
    let (end, _, expected) = run("Undef", "a");
    assert_eq!(end, None);
    assert!(
        expected.contains(&r#"Name("Missing")"#.to_string()),
        "{expected:?}"
    );
    // Characters have no token kinds.
    let (end, _, expected) = run("Tok", "a");
    assert_eq!(end, None);
    assert!(
        expected.contains(&r#"Name("IDENT")"#.to_string()),
        "{expected:?}"
    );
    assert_eq!(run("Empty", "").0, Some(0));
    assert_eq!(run("Empty", "a").0, Some(0));

    // A lookahead asked from outside, which builds nothing.
    let word = &g.rules[g.rule("Word").unwrap()].alts[0].expr;
    let ok: &[char] = &['a', 'b'];
    let bad: &[char] = &['9'];
    assert!(Parser::new(&g, 1, ok).holds(word, 0, false));
    let mut p = Parser::new(&g, 1, bad);
    assert!(!p.holds(word, 0, false));
    assert!(p.nodes.is_empty());
}

/// The inputs' sizes, and that tokens have no characters.
#[test]
fn an_input_of_characters_or_tokens_reports_its_size() {
    let none: &[char] = &[];
    assert!(Input::is_empty(none));
    assert!(!Input::is_empty(&['a'][..]));
    let toks: &[(Kind, &str)] = &[(Kind::Ident, "a")];
    assert!(!Input::is_empty(toks));
    assert_eq!(Input::char_at(toks, 0), None);
    let no_toks: &[(Kind, &str)] = &[];
    assert!(Input::is_empty(no_toks));
}
