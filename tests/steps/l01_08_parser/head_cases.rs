//! The cases of the head flag of sec:grammar ("The head flag"), shared by the parser test
//! `heads.rs` and the formatter test `l01_13_formatter::alternatives`.

/// `(text, tree)`, each parsed as `Expr` at the top ring; a tree of `ERROR` means no parse.
pub const HEAD_CASES: &[(&str, &str)] = &[
    // An `else` tail in a head: its block is the body's brace, so it is not read; an operand
    // after `else` is.
    ("if x else { 1 } { 2 } else { 3 }", "ERROR"),
    (
        "if x else 0 { 1 } else { 2 }",
        "(if (x (else 0)) ({ 1 }) else ({ 2 }))",
    ),
    ("match x else { 0 } { _ -> 1 }", "ERROR"),
    (
        "match x else 0 { _ -> 1 }",
        "(match (x (else 0)) { (_ -> 1) })",
    ),
    ("for y in xs else { ys } { y }", "ERROR"),
    (
        "for y in xs else ys { y }",
        "(for (y in (xs (else ys))) ({ y }))",
    ),
    (
        "for y in xs where p else q { y }",
        "(for (y in xs) where (p (else q)) ({ y }))",
    ),
    ("for y in xs where p else { q } { y }", "ERROR"),
    ("if x else #e -> { 0 } { 1 } else { 2 }", "ERROR"),
    (
        "if x else #e -> 0 { 1 } else { 2 }",
        "(if (x (else #e -> 0)) ({ 1 }) else ({ 2 }))",
    ),
    // Brackets clear the flag: the block comes back in parentheses, a call and an array.
    (
        "if (x else { 1 }) { 2 } else { 3 }",
        "(if (( (x (else ({ 1 }))) )) ({ 2 }) else ({ 3 }))",
    ),
    (
        "if ({ y = 1; y }) { 1 } else { 2 }",
        "(if (( ({ (y = 1 ;) y }) )) ({ 1 }) else ({ 2 }))",
    ),
    (
        "if f({ y = 1; y }) { 1 } else { 2 }",
        "(if (f (( ({ (y = 1 ;) y }) ))) ({ 1 }) else ({ 2 }))",
    ),
    (
        "if [{ y = 1; y }] == z { 1 } else { 2 }",
        "(if (([ ({ (y = 1 ;) y }) ]) == z) ({ 1 }) else ({ 2 }))",
    ),
    // A display needs no guard: a brace-led operand in a head that is not a block is a display.
    (
        "if { a } { 1 } else { 2 }",
        "(if ({ a }) ({ 1 }) else ({ 2 }))",
    ),
    // A struct update needs no guard: `with {` continues the operand.
    (
        "if p with { x = 1 } { 1 } else { 2 }",
        "(if (p (with { (x = 1) })) ({ 1 }) else ({ 2 }))",
    ),
    // A construct whose own body is a block may stand in a head: its body clears the flag.
    (
        "if if a { b } else { c } { 1 } else { 2 }",
        "(if (if a ({ b }) else ({ c })) ({ 1 }) else ({ 2 }))",
    ),
    (
        "if if a { b else { c } } else { d } { 1 } else { 2 }",
        "(if (if a ({ (b (else ({ c }))) }) else ({ d })) ({ 1 }) else ({ 2 }))",
    ),
    (
        "if match v { _ -> 1 } == 1 { 1 } else { 2 }",
        "(if ((match v { (_ -> 1) }) == 1) ({ 1 }) else ({ 2 }))",
    ),
    (
        "for y in if a { xs } else { ys } { y }",
        "(for (y in (if a ({ xs }) else ({ ys }))) ({ y }))",
    ),
    (
        "if loop t { until true; } == 0 { 1 } else { 2 }",
        "(if ((loop t ({ (until true ;) })) == 0) ({ 1 }) else ({ 2 }))",
    ),
    // `break` is an `Expr`, not a primary: it is no operand of `||`, and stands in a body.
    ("if c || break { 1 } else { 2 }", "ERROR"),
    (
        "if c { break 1 } else { 2 }",
        "(if c ({ (break 1) }) else ({ 2 }))",
    ),
    // Outside a head an `else` tail takes a block: in an arm body, an arm guard, a block.
    (
        "match v { _ -> x else { 0 } }",
        "(match v { (_ -> (x (else ({ 0 })))) })",
    ),
    (
        "match v { x where x else { false } -> 1 }",
        "(match v { (x where (x (else ({ false }))) -> 1) })",
    ),
    (
        "match v { _ -> { y = 1; y } }",
        "(match v { (_ -> ({ (y = 1 ;) y })) })",
    ),
];
