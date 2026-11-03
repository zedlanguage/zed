//! A declared type the checker does not track is shown in its message as the kernel prints it
//! (`zedc::check::declared_text`), not as the syntax tree writes itself, so the text parses
//! back as the same type. No L1 program reaches that message: its type denotes the unknown,
//! and a written type never does (`_` in a type is layer L10, and `&` takes operands), so the
//! text is tested here on the forms an L1 parameter may write.

use zedc::ast::{StmtKind, unit};
use zedc::check::declared_text;
use zedc::check::read::parse_type;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};

/// The printed text of the type written for the one parameter of `f(x: <text>) = 0;`.
fn shown(text: &str) -> Option<String> {
    let src = format!("f(x: {text}) = 0;\n");
    let tokens = lex_fence(&src).unwrap();
    let tree = parse(&src, &tokens, "Unit", TOP).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    let stmts = unit(&src, &tokens, &tree).unwrap();
    let StmtKind::Function(f) = &stmts[0].kind else {
        panic!("{src}: not a function")
    };
    declared_text(f.params[0].ty.as_ref().expect("a declared type"))
}

#[test]
fn a_declared_type_prints_as_text_that_reads_back_as_itself() {
    for text in [
        "int",
        "(int, #a | #b)",
        "(int,)",
        "((int, String) | (bool, f64),)",
        "int & (int | String)",
        "(int) -> String",
        "#a .. #a | #b -> int",
    ] {
        let printed = shown(text).expect("a kernel type");
        // The text is a type a parameter may declare, and it prints as itself.
        assert_eq!(shown(&printed), Some(printed.clone()), "{text}");
        // Read by the checker, it is the type that was written.
        let (back, want) = (parse_type(&printed).unwrap(), parse_type(text).unwrap());
        if let (Some(back), Some(want)) = (back.kernel(), want.kernel()) {
            assert!(
                back.subtype(&want) && want.subtype(&back),
                "{text} prints as {printed}, which reads back as another type"
            );
        }
    }
}

#[test]
fn a_declared_type_holding_a_port_has_no_kernel_text() {
    assert_eq!(shown("Lines"), None);
}
