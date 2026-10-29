use super::render;
use zedc::lex::{ErrorKind, KEYWORDS, OPERATORS, Tok, lex};

#[test]
fn every_keyword_is_a_keyword_and_a_longer_word_is_a_name() {
    for k in KEYWORDS {
        assert_eq!(lex(k).unwrap()[0].tok, Tok::Keyword(k), "{k}");
        for longer in [
            format!("{k}s"),
            format!("{k}_1"),
            format!("{k}2"),
            format!("_{k}"),
        ] {
            assert_eq!(
                lex(&longer).unwrap()[0].tok,
                Tok::Name(longer.clone()),
                "{longer}"
            );
        }
    }
    assert_eq!(KEYWORDS.len(), 36);
    assert_eq!(
        render(&lex("format iffy in_stock types notable asc ascending").unwrap()),
        "format iffy in_stock types notable «asc» ascending"
    );
}

#[test]
fn where_and_sep_are_names_reserved_only_by_position() {
    assert_eq!(
        render(&lex("for x in xs where x > 0").unwrap()),
        "«for» x «in» xs where x > 0₍10₎"
    );
    assert_eq!(lex("sep").unwrap()[0].tok, Tok::Name("sep".into()));
}

#[test]
fn a_prime_does_not_continue_a_keyword() {
    // `if'` is the keyword `if` and a stray `'`, as `KeywordWord !XID_CONTINUE` reads it.
    let e = lex("if'").unwrap_err();
    assert_eq!((e.kind, e.span.start), (ErrorKind::Unexpected('\''), 2));
}

#[test]
fn every_operator_lexes_alone_and_the_longest_wins() {
    for op in OPERATORS {
        assert_eq!(
            lex(op)
                .unwrap()
                .iter()
                .map(|t| t.tok.clone())
                .collect::<Vec<_>>(),
            [Tok::Op(op)],
            "{op}"
        );
    }
    let cases = [
        ("f->?g", "f ->? g"),
        ("0..<n", "0₍10₎ ..< n"),
        ("0..=n", "0₍10₎ ..= n"),
        ("a...", "a ..."),
        ("x**2", "x ** 2₍10₎"),
        ("a++b", "a ++ b"),
        ("p<-m", "p <- m"),
        ("x< -1", "x < - 1₍10₎"),
        ("a><(+)", "a >< ( + )"),
        ("a?.b*.c", "a ?. b *. c"),
        ("m::n", "m :: n"),
        ("a!=b==c<=d>=e", "a != b == c <= d >= e"),
        ("a&&b||!c", "a && b || ! c"),
        (r"\x -> x", r"\ x -> x"),
        ("[1,2];{}", "[ 1₍10₎ , 2₍10₎ ] ; { }"),
        ("a=b:c|d&e?f/g", "a = b : c | d & e ? f / g"),
    ];
    for (src, want) in cases {
        assert_eq!(render(&lex(src).unwrap()), want, "{src}");
    }
}

#[test]
fn atoms_and_annotations() {
    assert_eq!(
        render(&lex("@log @pure #none #inexact #syntaxError(pos: 3) #ok' #if").unwrap()),
        "@log @pure #none #inexact #syntaxError ( pos : 3₍10₎ ) #ok' #if"
    );
}

#[test]
fn golden_lexical_errors() {
    let cases = [
        "# none",
        "x = @",
        "#pаypal",
        "cost = $5",
        "a % b",
        "a ^ b",
        "x ~ y",
        "`cmd`",
        "x''",
    ];
    let out: Vec<String> = cases
        .iter()
        .map(|c| {
            let e = lex(c).unwrap_err();
            format!("{c:<12} [{}..{}] {e}", e.span.start, e.span.end)
        })
        .collect();
    insta::assert_snapshot!(out.join("\n"));
}
