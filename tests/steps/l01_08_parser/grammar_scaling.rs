//! The forms the left-recursive rules of sec:grammar read, each of length n, whose benchmarks in
//! `bench/grammar_scaling.rs` hold each chain linear in its length and each lookahead over them
//! matched once at its token. Here each parses at small lengths, and a sum is built.

use zedc::ast::build;
use zedc::lex::lex;
use zedc::parse::{TOP, parse};

/// A form of length `n` parsed from `start`; `what` names it for its benchmark.
pub(super) struct Form {
    pub(super) start: &'static str,
    pub(super) what: &'static str,
    pub(super) input: fn(usize) -> String,
}

pub(super) const SUM: Form = Form {
    start: "Expr",
    what: "a sum of n terms",
    input: |n| "a + ".repeat(n) + "b",
};

pub(super) const MEMBER_CHAIN: Form = Form {
    start: "Expr",
    what: "a chain of n members",
    input: |n| "a".to_string() + &".b(1)".repeat(n),
};

pub(super) const TYPE_UNION: Form = Form {
    start: "Type",
    what: "a union of n types",
    input: |n| "A | ".repeat(n) + "B",
};

pub(super) const DOTTED_PATH: Form = Form {
    start: "Path",
    what: "a path of n names",
    input: |n| "a".to_string() + &".b".repeat(n),
};

pub(super) const KEYPATH: Form = Form {
    start: "KeyPath",
    what: "a keypath of n keys",
    input: |n| "a".to_string() + &".b[1]".repeat(n),
};

/// `PlainArg` reads `!(Name ':') Expr` at each argument.
pub(super) const MANY_ARGUMENTS: Form = Form {
    start: "Expr",
    what: "a call of n arguments",
    input: |n| format!("f({}1)", "a + b, ".repeat(n)),
};

/// `Primary` reads `&('{' Item)` before a block, so the statements of a block in a block are
/// read by the lookahead and by the block, once each.
pub(super) const NESTED_BLOCKS: Form = Form {
    start: "Expr",
    what: "n nested blocks",
    input: |n| format!("x -> {}1{}", "{ y = ".repeat(n), "; y }".repeat(n)),
};

pub(super) const MANY_STATEMENTS: Form = Form {
    start: "Expr",
    what: "a block of n statements",
    input: |n| format!("x -> {{ {}x }}", "y = x + 1 * 2; ".repeat(n)),
};

pub(super) const MANY_FUNCTIONS: Form = Form {
    start: "Unit",
    what: "a program of n functions",
    input: |n| "double(x) = x * 2 + 1;\nhalf(y) = y.value / 2 - 1;\n".repeat(n),
};

/// The shape of `l01_16_elaboration::scaling`'s nested functions: function `i` binds `y{i}` and
/// calls function `i + 1`, so the unit nests `n` deep. A position holds an entry for each rule
/// called there, found by a walk of its list of entries (COMPLEXITY.md F86).
pub(super) const NESTED_FUNCTIONS: Form = Form {
    start: "Unit",
    what: "n nested functions",
    input: |n| {
        let mut text = String::new();
        for i in 0..n {
            text += &format!("h{i}(positional x) {{\ny{i} = x + 1;\n");
        }
        text += "x\n";
        for i in (0..n).rev() {
            if i + 1 < n {
                text += &format!("h{}(y{i})\n", i + 1);
            }
            text += "}\n";
        }
        text + "main = h0(1);\n"
    },
};

/// The shape of `l01_26a_generic_literals::scaling`'s calls: a sum of `n` calls, each with a
/// generic literal, the input with the most parser work per byte of those measured for F86.
pub(super) const CALLS_WITH_LITERALS: Form = Form {
    start: "Unit",
    what: "a sum of n calls",
    input: |n| {
        let calls: Vec<String> = (0..n).map(|i| format!("mul(x, {})", i + 1)).collect();
        format!(
            "mul(positional x, positional k) = x * k;\nf(positional x) = {};\n",
            calls.join(" + ")
        )
    },
};

#[test]
fn each_form_parses_at_small_lengths_and_a_sum_is_built() {
    let forms = [
        SUM,
        MEMBER_CHAIN,
        TYPE_UNION,
        DOTTED_PATH,
        KEYPATH,
        MANY_ARGUMENTS,
        NESTED_BLOCKS,
        MANY_STATEMENTS,
        MANY_FUNCTIONS,
        NESTED_FUNCTIONS,
        CALLS_WITH_LITERALS,
    ];
    for form in &forms {
        for n in [1, 2, 9] {
            let text = (form.input)(n);
            let tokens = lex(&text).unwrap();
            if let Err(e) = parse(&text, &tokens, form.start, TOP) {
                panic!("{}, n = {n}: {e}", form.what);
            }
        }
    }
    for n in [1, 2, 9] {
        let text = (SUM.input)(n);
        let tokens = lex(&text).unwrap();
        let tree = parse(&text, &tokens, "Expr", TOP).unwrap();
        build(&text, &tokens, &tree).unwrap();
    }
}
