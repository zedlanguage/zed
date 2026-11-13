//! A reserved word written where a name stands (DESIGN.md sec:lexical; row "Reserved word
//! written where a name stands" of sec:diagnostics): the parse error is reported at the word,
//! shows the word's line, says what the word begins, and offers the line with another name in
//! the word's place when that line then parses. A name that only begins with a reserved word is
//! an ordinary name.

use zed_tests::scaling;
use zedc::ast::Error;
use zedc::lex::{KEYWORDS, Tok, lex};
use zedc::parse::{RESERVED, TOP, parse};
use zedc::rejection::Row;

/// What `word` begins, written out for the words the position tests use.
fn what(word: &str) -> &'static str {
    match word {
        "without" => "it removes a facet from a value, as `n without units(\"km\")`",
        "law" => {
            "it begins a law, as in `struct Span { lo: int, hi: int, law ordered() = lo <= hi }`"
        }
        "initial" => {
            "it begins the statement `initial x = e;`, which gives `x` its value before step 0 \
             of a loop that updates `x`"
        }
        "if" => "it begins a conditional, as `if x < 0 { -x } else { x }`",
        "for" => "it begins a comprehension, as `for x in xs { x * 2 }`",
        _ => panic!("no message written for {word}"),
    }
}

/// The notes of the message for `word` with the note `repair` last.
fn notes_of(word: &str, what: &str, repair: &str) -> [String; 3] {
    [
        format!("`{word}` is reserved: {what}"),
        format!("rename the other uses of `{word}` as a name too"),
        repair.to_string(),
    ]
}

/// The error the unit `src` is refused with by the parser.
fn refusal(src: &str) -> Error {
    let tokens = lex(src).unwrap();
    Error::of_parse(src, parse(src, &tokens, "Unit", TOP).expect_err(src))
}

/// Checks that `src` is refused at `word`, at byte `at`, with the whole message and notes:
/// the word's line is shown, and `repaired` is offered in its place.
fn reserved(src: &str, word: &str, at: usize, repaired: &str) {
    let start = src[..at].rfind('\n').map_or(0, |i| i + 1);
    let end = src[at..].find('\n').map_or(src.len(), |i| at + i);
    let line = src[start..end].trim();
    refused(
        src,
        word,
        at,
        &format!("Reserved word used as a name: `{line}`. Try `{repaired}` instead."),
        &format!("repair: `{repaired}`"),
    );
}

/// Checks that `src` is refused at `word`, at byte `at`, with `message` and the notes that end
/// in `repair`.
fn refused(src: &str, word: &str, at: usize, message: &str, repair: &str) {
    let e = refusal(src);
    assert_eq!(e.row, Some(Row::ReservedWordAsName), "{src}");
    assert_eq!(e.message, message, "{src}");
    assert_eq!(&src[e.span.start..e.span.end], word, "{src}");
    assert_eq!(e.span.start, at, "{src}");
    let notes: Vec<&str> = e.notes.iter().map(|n| n.text.as_str()).collect();
    assert_eq!(notes, notes_of(word, what(word), repair), "{src}");
    for n in &e.notes {
        assert_eq!(n.span, e.span, "{src}");
    }
}

/// Checks that `src` parses.
fn accepted(src: &str) {
    let tokens = lex(src).unwrap();
    if let Err(e) = parse(src, &tokens, "Unit", TOP) {
        panic!("{src}: {e}");
    }
}

#[test]
fn a_binding() {
    reserved("without = 3;", "without", 0, "rest = 3;");
    reserved("law = 3;", "law", 0, "rule = 3;");
    reserved("initial = 0;", "initial", 0, "start = 0;");
    reserved("local for = 0;", "for", 6, "local each = 0;");
}

#[test]
fn a_parameter() {
    reserved("f(law) = law + 1;", "law", 2, "f(rule) = rule + 1;");
    reserved(
        "f(initial) = initial + 1;",
        "initial",
        2,
        "f(start) = start + 1;",
    );
    reserved(
        "f(positional without: int) = without;",
        "without",
        13,
        "f(positional rest: int) = rest;",
    );
    reserved("g = for -> for + 1;", "for", 4, "g = each -> each + 1;");
}

#[test]
fn a_function_or_method_name() {
    reserved("if(x) = x;", "if", 0, "cond(x) = x;");
    reserved("without(x) = x;", "without", 0, "rest(x) = x;");
    reserved("Point.law = 1;", "law", 6, "Point.rule = 1;");
}

#[test]
fn a_field_after_a_dot() {
    reserved("f(x) = x.if;", "if", 9, "f(x) = x.cond;");
    reserved("y = s.without;", "without", 6, "y = s.rest;");
    reserved("y = for.x;", "for", 4, "y = each.x;");
}

#[test]
fn a_field_of_a_struct_or_interface() {
    reserved("struct S { law: int }", "law", 11, "struct S { rule: int }");
    reserved(
        "struct S { x: int, initial: int }",
        "initial",
        19,
        "struct S { x: int, start: int }",
    );
    reserved(
        "interface I { if: int }",
        "if",
        14,
        "interface I { cond: int }",
    );
}

#[test]
fn a_field_of_a_record_display_or_a_named_argument() {
    reserved("s = { law: 1 };", "law", 6, "s = { rule: 1 };");
    reserved("y = f(without: 1);", "without", 6, "y = f(rest: 1);");
}

#[test]
fn a_type_struct_or_import_name() {
    reserved("type law = int;", "law", 5, "type rule = int;");
    reserved("struct for { x: int }", "for", 7, "struct each { x: int }");
    reserved("f(x: if) = x;", "if", 5, "f(x: cond) = x;");
    reserved("import without;", "without", 7, "import rest;");
}

#[test]
fn a_loop_variable_or_a_statement_of_a_loop() {
    reserved(
        "r = loop for { while for < 3; };",
        "for",
        9,
        "r = loop each { while each < 3; };",
    );
    reserved(
        "r = loop t { while t < 3; initial initial = 0; };",
        "initial",
        34,
        "r = loop t { while t < 3; initial start = 0; };",
    );
}

/// The repair is written into the word's line only, and is the name alone when that line does
/// not then parse; a name the program already uses is not offered.
#[test]
fn the_repair() {
    reserved("x = 1;\ny = x +\n  for * 2;\n", "for", 17, "each * 2;");
    reserved(
        "rule = 1;\nlaw = rule + 1;\n",
        "law",
        10,
        "rule2 = rule + 1;",
    );
    reserved(
        "rule = rule2;\nlaw = rule + 1;\n",
        "law",
        14,
        "rule3 = rule + 1;",
    );
    // `if` both as a name and as a keyword on one line: neither the name everywhere nor at the
    // one site parses, since the second `if` is a name too.
    refused(
        "f(if) = if if > 0 { 1 } else { 0 };",
        "if",
        2,
        "Reserved word used as a name: `f(if) = if if > 0 { 1 } else { 0 };`. Try another \
         name, such as `cond`.",
        "repair: another name, such as `cond`",
    );
    // At the one site only, where the word also stands as a keyword on the line.
    reserved(
        "f(if) = if x > 0 { 1 } else { 0 };",
        "if",
        2,
        "f(cond) = if x > 0 { 1 } else { 0 };",
    );
}

/// The row applies only when a name in the word's place gets the parse past where it stopped;
/// otherwise the parse's own message stands. The word is the one the parse stopped at or the
/// last before it in its statement, so a misused word with another word after it keeps the
/// parse's own message (COMPLEXITY.md, MSG-keyword-as-name).
#[test]
fn other_errors_keep_the_parse_message() {
    for src in [
        "x = a is ;",
        "x = a div ;",
        "x = (a + ;",
        // `_` is no name, and `initial` begins the statement as it should.
        "initial _ = 0;",
        // A name in place of `not` stops at `x`: `not` is no prefix operator, and is not
        // written as a name.
        "y = not x;",
        // `if`, written as a name, stands between the first and the last reserved word before
        // the stop, so it is not tried.
        "y = (a is int) + if(x mod 2, z);",
    ] {
        let e = refusal(src);
        assert_eq!(e.row, Some(Row::SyntaxError), "{src}");
        // The parse's own message: its headline, and what the grammar takes there in a note.
        assert!(
            e.message.starts_with("Syntax error "),
            "{src}: {}",
            e.message
        );
        assert!(e.notes[0].text.starts_with("expected "), "{src}");
        // Then the declaration and each bracket still open where the parse stops, and the
        // repairs that parse (step L1.29d).
        assert!(e.notes[1].text.ends_with(" begins here"), "{src}");
        for n in &e.notes[2..] {
            assert!(
                n.text.contains(" opens here and is still open ") || n.text.starts_with("repair: "),
                "{src}: {}",
                n.text
            );
        }
    }
}

/// Names that only begin with a reserved word are names.
#[test]
fn names_that_begin_with_a_reserved_word_parse() {
    accepted("withouts = 3;\nlawful(x) = withouts + x;\n");
    accepted("initials = 1;\nformat(iffy) = iffy + initials;\nstruct S { lawful: int }\n");
    accepted("y = s.withouts + s.lawful;\n");
    for src in ["withouts = 3;", "lawful(x) = x;", "f(lawful) = lawful;"] {
        let tokens = lex(src).unwrap();
        assert!(
            tokens.iter().all(|t| !matches!(t.tok, Tok::Keyword(_))),
            "{src}"
        );
    }
}

/// The table holds each keyword once, in the order of the lexer's list; each name it offers is
/// a name and no keyword; and every keyword, as a binding, gets the row with its message.
#[test]
fn every_keyword_has_its_message() {
    let words: Vec<&str> = RESERVED.iter().map(|r| r.0).collect();
    assert_eq!(words, KEYWORDS);
    for (word, what, like) in RESERVED {
        let tokens = lex(like).unwrap();
        assert!(
            matches!(&tokens[..], [t] if matches!(t.tok, Tok::Name(_))),
            "{like}"
        );
        let src = format!("{word} = 1;");
        let e = refusal(&src);
        assert_eq!(e.row, Some(Row::ReservedWordAsName), "{src}");
        assert_eq!(
            e.message,
            format!("Reserved word used as a name: `{word} = 1;`. Try `{like} = 1;` instead."),
            "{src}"
        );
        assert_eq!(e.span.start, 0, "{src}");
        let notes: Vec<&str> = e.notes.iter().map(|n| n.text.as_str()).collect();
        assert_eq!(
            notes,
            notes_of(word, what, &format!("repair: `{like} = 1;`")),
            "{src}"
        );
    }
}

/// Each example a message quotes parses: as a unit, as a statement of a loop's body, or as
/// the value of a binding or of a type declaration.
#[test]
fn every_quoted_example_parses() {
    for (word, what, _) in RESERVED {
        for (i, example) in what.split('`').enumerate() {
            if i % 2 == 0 {
                continue;
            }
            let forms = [
                example.to_string(),
                format!("{example};"),
                format!("r = loop t {{ while t < 3; {example} }};"),
                format!("r = loop t {{ while t < 3; x = {example}; }};"),
                format!("y = {example};"),
                format!("type T = {example};"),
            ];
            let parses = forms.iter().any(|src| {
                let tokens = lex(src).unwrap();
                parse(src, &tokens, "Unit", TOP).is_ok()
            });
            assert!(parses, "the example `{example}` of `{word}` does not parse");
        }
    }
}

/// Finding the word takes at most two more parses, each linear: the time is linear in the
/// number of statements before the word, and in the length of its statement.
#[test]
fn finding_the_word_is_linear() {
    let many = scaling::inputs(500, |n| {
        let mut src: String = (0..n).map(|i| format!("a{i} = {i};\n")).collect();
        src += "without = 3;\n";
        src
    });
    scaling::check("n bindings before `without = 3;`", 500, |n| {
        let src = &many[&n];
        let e = refusal(src);
        assert_eq!(e.row, Some(Row::ReservedWordAsName));
    });
    let long = scaling::inputs(500, |n| {
        let terms: Vec<String> = (0..n).map(|i| format!("a{i}")).collect();
        format!("x = {} + y.if;\n", terms.join(" + "))
    });
    scaling::check("a statement of n terms ending in `y.if`", 500, |n| {
        let src = &long[&n];
        let e = refusal(src);
        assert_eq!(e.row, Some(Row::ReservedWordAsName));
    });
}

/// A statement of n reserved words, none of them the cause: each word tried is one more parse,
/// and at most three are tried, so the time stays linear (COMPLEXITY.md, MSG-keyword-as-name).
#[test]
fn many_reserved_words_in_one_statement_are_linear() {
    let long = scaling::inputs(500, |n| {
        format!("x = {} is ;\n", vec!["true"; n].join(" && "))
    });
    scaling::check("a statement of n words `true` ending in `is ;`", 500, |n| {
        let src = &long[&n];
        let e = refusal(src);
        assert_eq!(e.row, Some(Row::SyntaxError));
    });
}
