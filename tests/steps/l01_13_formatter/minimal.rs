//! The formatter writes parentheses in an expression exactly where the grammar needs them to
//! keep its meaning (author P191, PRINT-expr-parens-minimal; SPEC-paren-minimal for DESIGN
//! sec:plan "The formatter is a fixed point"). The grammar has no precedence table: precedence
//! comes from the layering of the rules of DESIGN.md sec:grammar, `Expr12` → `Or` → `And` →
//! `Equality` → `Relation` → `Reduce` → `Range` → `Infix` → `Additive` → `Multiplicative` →
//! `Prefix` → `Power` → `Postfix` → `Primary`, where a `~X` alternative passes through to the
//! next layer, as the type printer's test reads it (tests/steps/l01_29_repairs_and_printing/
//! parens.rs).
//!
//! Two checks. The formatter's levels (`zed_kernel::print::level`, read by `fn level` of
//! crates/zedc-syntax/src/format.rs) are checked against that layering, computed from the
//! grammar the parser reads. And over every pair of an operator form written in each operand
//! position of another, and over the corpus, the round trip (the formatted text builds to the
//! same statements and formats to itself) and minimality (deleting any one pair of grouping
//! parentheses from it either fails to parse or builds other statements). Minimality catches
//! what the layering alone misses: an operand rule of a form one layer tighter than its own,
//! as `Infix INFIX Additive`, and the lookaheads, as `!'{'` before a lambda's body.

use std::collections::HashSet;
use std::path::PathBuf;

use zed_kernel::print::level;
use zedc::format::format;
use zedc::lex::Tok;
use zedc::parse::{Grammar, grammar, marked_rule};
use zed_tests::is_not_yet;
use zed_tests::step_helpers::l01_13_formatter::shape;

use super::build;

/// The rules reachable from rule `r` through `~` alternatives alone, `r` among them: the rules
/// whose text stands where `r` is expected with no parentheses. A visited set bounds the walk.
fn reach(g: &Grammar, r: usize) -> HashSet<usize> {
    let mut seen = HashSet::from([r]);
    let mut work = vec![r];
    while let Some(r) = work.pop() {
        for alt in g.rules[r].alts.iter().filter(|a| a.pass) {
            let m = marked_rule(&alt.expr).expect("a `~` alternative marks a rule");
            if seen.insert(m) {
                work.push(m);
            }
        }
    }
    seen
}

/// Each level of the formatter and the rule of sec:grammar it stands for. `LAMBDA` is `Expr`,
/// whose two alternatives are written out, not passed through with `~`, so it is not in the
/// layering; a lambda is grouped everywhere but at `Expr`, which the pairs below check.
const LEVELS: [(u8, &str); 14] = [
    (level::ELSE, "Expr12"),
    (level::OR, "Or"),
    (level::AND, "And"),
    (level::EQUALITY, "Equality"),
    (level::RELATION, "Relation"),
    (level::REDUCE, "Reduce"),
    (level::RANGE, "Range"),
    (level::INFIX, "Infix"),
    (level::ADDITIVE, "Additive"),
    (level::MULTIPLICATIVE, "Multiplicative"),
    (level::PREFIX, "Prefix"),
    (level::POWER, "Power"),
    (level::POSTFIX, "Postfix"),
    (level::PRIMARY, "Primary"),
];

/// A text written at level `a` stands bare where level `b` is expected exactly when `a >= b`,
/// and the grammar agrees: the rule of `a` is reached from the rule of `b` through `~`
/// alternatives exactly when `a >= b`.
#[test]
fn the_levels_are_the_layering_of_the_grammar() {
    let g = grammar();
    let rule = |name: &str| g.rule(name).unwrap_or_else(|| panic!("no rule `{name}`"));
    let mut wrong = Vec::new();
    for (b, at) in LEVELS {
        let reached = reach(g, rule(at));
        for (a, form) in LEVELS {
            if reached.contains(&rule(form)) != (a >= b) {
                wrong.push(format!("{form} (level {a}) where {at} (level {b}) is expected"));
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// Each operator form with `@` for the operand written in each position in turn; the other
/// operands are names. Every binary operator of sec:grammar, each prefix, `is`, `in`, a range,
/// `else`, a lambda, each suffix, `with`, `><`, an infix call, on each side, and a `for`, at
/// its source (a head) and in its body.
const FORMS: &[&str] = &[
    "for y in @ { y }", "for y in s { @ }",
    "@ || b", "a || @", "@ && b", "a && @", "@ == b", "a == @", "@ != b", "a != @", "@ < b",
    "a < @", "@ <= b", "a <= @", "@ > b", "a > @", "@ >= b", "a >= @", "@ + b", "a + @",
    "@ - b", "a - @", "@ ++ b", "a ++ @", "@ * b", "a * @", "@ / b", "a / @", "@ div b",
    "a div @", "@ mod b", "a mod @", "@ ^ b", "a ^ @", "-@", "!@", "@ is int", "@ in s",
    "a in @", "@..<b", "a..<@", "@ else b", "a else @", "y -> @", "@.c", "@(1)", "@[0]",
    "@*.c", "@ with { c = 1 }", "@ >< max", "@ ~g~ b", "a ~g~ @",
];

/// The pairs of positions of `text` that hold a pair of grouping parentheses: a `(` that does
/// not follow a name, a `)`, a `]` or a `.` (a call's arguments, a parameter list), whose
/// pair holds no `,` at its own depth (a tuple). The tokens of `text` find them, so a
/// parenthesis in a string is not one.
fn grouping(text: &str) -> Vec<(usize, usize)> {
    let (tokens, _) = build(text).expect("the formatter's output builds");
    let mut open: Vec<(usize, bool)> = Vec::new();
    let mut out = Vec::new();
    for (i, t) in tokens.iter().enumerate() {
        match &t.tok {
            Tok::Op("(") => {
                let called = i > 0
                    && matches!(&tokens[i - 1].tok, Tok::Name(_) | Tok::Op(")" | "]" | "."));
                open.push((t.span.start, !called));
            }
            Tok::Op(",") => {
                if let Some(top) = open.last_mut() {
                    top.1 = false;
                }
            }
            Tok::Op(")") => {
                if let Some((start, group)) = open.pop()
                    && group
                {
                    out.push((start, t.span.start));
                }
            }
            _ => {}
        }
    }
    out
}

/// What is wrong with the formatting of `text`, a unit: it does not build back to its
/// statements, does not format to itself, or holds a pair of grouping parentheses whose
/// deletion leaves text that builds to the same statements. Empty when it is right. `name`
/// names `text` in the messages, which show the line of each pair not needed.
fn misformatted(name: &str, text: &str) -> Vec<String> {
    let (tokens, stmts) = match build(text) {
        Ok(b) => b,
        Err(e) => return vec![format!("{name}: does not build: {e}")],
    };
    let out = format(text, &tokens, &stmts);
    let (tokens2, stmts2) = match build(&out) {
        Ok(b) => b,
        Err(e) => return vec![format!("{name}: formats to text that does not build: {e}")],
    };
    let want = shape(&stmts);
    if shape(&stmts2) != want {
        return vec![format!("{name}: formats to text that builds to other statements")];
    }
    if format(&out, &tokens2, &stmts2) != out {
        return vec![format!("{name}: formats to text that does not format to itself")];
    }
    let mut wrong = Vec::new();
    for (a, b) in grouping(&out) {
        let less = format!("{} {} {}", &out[..a], &out[a + 1..b], &out[b + 1..]);
        if build(&less).is_ok_and(|(_, s)| shape(&s) == want) {
            let start = out[..a].rfind('\n').map_or(0, |i| i + 1);
            let end = out[a..].find('\n').map_or(out.len(), |i| a + i);
            wrong.push(format!(
                "{name}: the parentheses at byte {a} of `{}` are not needed",
                &out[start..end]
            ));
        }
    }
    wrong
}

/// The units of the pairs: each form with `@` replaced by each other form, in parentheses,
/// whose names fill its holes.
fn pair_units() -> Vec<String> {
    let mut units = Vec::new();
    for outer in FORMS {
        for inner in FORMS {
            let inner = inner.replace('@', "x");
            let expr = outer.replace('@', &format!("({inner})"));
            units.push(format!("f(a, b, s, x) = {expr};"));
        }
    }
    units
}

/// Over every operator form in every operand position of every other, the formatter keeps
/// each pair the grammar needs and writes no other. A unit a later layer builds is counted, not
/// checked.
#[test]
fn each_operator_pair_is_parenthesized_exactly_where_the_grammar_needs_it() {
    let mut wrong = Vec::new();
    let (mut checked, mut later) = (0, 0);
    for unit in pair_units() {
        match build(&unit) {
            Err(e) if is_not_yet(&e) => later += 1,
            _ => {
                checked += 1;
                wrong.extend(misformatted(&unit, &unit));
            }
        }
    }
    assert!(wrong.is_empty(), "{} wrong:\n{}", wrong.len(), wrong.join("\n"));
    assert_eq!((checked, later), (FORMS.len() * FORMS.len(), 0));
}

/// The join patterns `r3` and `r5` of DESIGN sec:joins (row SPEC-paren-minimal): the group
/// `?(b && ?c)` is a pair of parentheses that carries meaning (sec:lexical). The grammar reads
/// both, and the group is a node of `r3`'s tree that `r5` has not. zedc does not build joins
/// yet (the AST refuses them as not supported); once it does, the formatter must write both
/// as they are, each building to its own statements, which the second branch checks. Their
/// values are not checked here: that needs a run, at the step that builds joins.
#[test]
fn join_patterns_format_unchanged() {
    let r3 = "f(a, b, c, v) = (a, b, c) into (a && ?(b && ?c) -> v);\n";
    let r5 = "f(a, b, c, v) = (a, b, c) into (a && ?b && ?c -> v);\n";
    let nodes = |unit: &str| {
        let tokens = zedc::lex::lex_fence(unit).expect("the pattern lexes");
        let tree = zedc::parse::parse(unit, &tokens, "Unit", zedc::parse::TOP);
        tree.unwrap_or_else(|e| panic!("{unit}: {e}")).nodes.len()
    };
    assert!(nodes(r3) > nodes(r5), "the group is a node of the tree");
    match (build(r3), build(r5)) {
        (Err(e3), Err(e5)) if is_not_yet(&e3) && is_not_yet(&e5) => {}
        (b3, b5) => {
            for unit in [r3, r5] {
                assert_eq!(misformatted(unit, unit), Vec::<String>::new());
                let (tokens, stmts) = build(unit).expect("the pattern builds");
                assert_eq!(format(unit, &tokens, &stmts), unit);
            }
            let (b3, b5) = (b3.unwrap().1, b5.unwrap().1);
            assert_ne!(shape(&b3), shape(&b5), "the group changes the pattern");
        }
    }
}

/// Every corpus program that builds formats with no pair of grouping parentheses the grammar
/// does not need (the corpus test of this step checks the round trip and the fixed point).
#[test]
fn the_corpus_formats_with_no_parentheses_the_grammar_does_not_need() {
    let corpus = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../zed/corpus");
    let mut files: Vec<PathBuf> = std::fs::read_dir(&corpus)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "zed"))
        .collect();
    files.sort();
    let mut wrong = Vec::new();
    let mut checked = 0;
    for path in &files {
        let text = std::fs::read_to_string(path).unwrap();
        if build(&text).is_err() {
            continue;
        }
        checked += 1;
        let name = path.file_name().unwrap().to_string_lossy();
        wrong.extend(misformatted(&name, &text));
    }
    assert!(checked > 0);
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
