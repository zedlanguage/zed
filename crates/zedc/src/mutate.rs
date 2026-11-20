//! Mutation testing (step L25.8): `zedc test --mutate` makes one change at a time to a
//! definition, each modeling an error a person makes at a boundary of the code, and runs the
//! `test { }` tables (step L1.21) against each such mutant.
//!
//! The changes are the set of MUTATION.md section 6 (QUESTIONS A103), heuristics H1 to H11,
//! each derived there from the boundary it probes and the error it models, with the
//! literature it follows (Offutt 1996 for the operators, Kuhn 1999 for the conditions, PIT as
//! Laurent 2016 lists it for the rest):
//! - H1, a comparison by its strictness neighbor (`<` and `<=`, `>` and `>=`, `==` and `!=`);
//! - H2, at `int` with no literal operand, the right operand moved one the other way
//!   (`a < b - 1`, `a <= b + 1`, `a > b + 1`, `a >= b - 1`): with H1, the two points next to
//!   the border, ON and OFF (MUTATION.md 3.1);
//! - H3, not at `int`, a comparison reversed (`<` and `>`, `<=` and `>=`);
//! - H4, an inline `int`, `rat` or decimal literal by one unit of its last written digit down
//!   and up, at the carrier it adopted, in every arm where a generic literal is built once per
//!   carrier (L1.26a); at an `int` comparison not the neighbor that is H1 again;
//! - H5 and H8, a written unary `-` (not on a literal) or `!` removed;
//! - H6, a `-` inserted at the root of an arithmetic expression (not at a binary `-`, not under
//!   a written `-`);
//! - H7, `&&` and `||` swapped, each operand dropped, and `!` inserted before each operand
//!   (not before a written `!`);
//! - H9, an `if` replaced by its `then` branch and by its `else` branch, and its condition
//!   negated (not when it is a written `!`);
//! - H10, `+` and `-` each way, `*` by `/` where `/` is defined (the checker types the product
//!   with no `int`), `/` by `*`, `div` and `mod` each way;
//! - H11, the operands swapped at `-`, `/`, `div`, `mod`, `^` at `int` and string `++`.
//!
//! The literature, as MUTATION.md section 2 quotes it (each checked there against the paper's
//! text; the derivations of MUTATION.md section 3 are checked by the tests of
//! `tests/steps/l25_08_mutate/set.rs`, one or more per heuristic):
//! - \[Offutt96\] A. J. Offutt, A. Lee, G. Rothermel, R. H. Untch, C. Zapf, "An experimental
//!   determination of sufficient mutant operators", ACM TOSEM 5(2), 1996,
//!   doi:10.1145/227607.227610, p. 109: "the five operators ABS, AOR, LCR, ROR, and UOI are
//!   sufficient to achieve almost full mutation coverage"; p. 115: ROR "replaces relational
//!   operators with other relational operators", AOR "replaces each arithmetic operator with
//!   every syntactically legal operator", LCR "replaces each logical connector (AND and OR)",
//!   UOI "inserts unary operators in front of expressions", ABS forces "each arithmetic
//!   expression to take on a zero value, a positive value, and a negative value". The set
//!   takes these five families and keeps of each the replacements that move a boundary.
//! - \[Offutt92\] A. J. Offutt, "Investigations of the software testing coupling effect", ACM
//!   TOSEM 1(1), 1992, doi:10.1145/125489.125473: "by explicitly testing for simple faults, we
//!   are also implicitly testing for more complicated faults". So each mutant changes one
//!   written node.
//! - \[Kuhn99\] D. R. Kuhn, "Fault classes and error detection capability of specification-based
//!   testing", ACM TOSEM 8(4), 1999, doi:10.1145/322993.322996, p. 412: the variable negation,
//!   expression negation and operator reference faults ("x ∧ y replaced by x ∨ y"), and the
//!   missing condition; p. 422: "Tests that detect missing-condition faults will detect variable
//!   negation faults". H7, H8 and H9 model these classes.
//! - \[Laurent16\] T. Laurent, M. Papadakis, M. Kintis, C. Henard, Y. Le Traon, A. Ventresque,
//!   "Assessing and improving the mutation testing practice of PIT", arXiv:1601.02351, 2016,
//!   doi:10.48550/arXiv.1601.02351, Table 1: PIT's "Invert Neg." ("-a ⇝ a", H5, H8), "Inline
//!   Const." ("1 ⇝ 0, a ⇝ a + 1", H4), "Negate Cond." ("== ⇝ !=", H1), "Remove Cond." (H9),
//!   "ABS" ("a ⇝ -a", H6) and "AOD" ("a + b ⇝ a", the operand drops of H7).
//! - H2 has no paper behind it: it is derived in MUTATION.md 3.1 (at `int`, `a < b` is
//!   `b - a >= 1`; H1 differs from it only at `b - a = 0`, H2 only at `b - a = 1`), the ON and
//!   OFF points of the domain testing of White and Cohen 1980 (doi:10.1109/tse.1980.234486,
//!   read only from its abstract; nothing rests on it), and checked by
//!   `set::the_two_points_next_to_a_border_detect_h1_and_h2_and_each_is_needed`.
//!
//! No mutant is made inside a declared constant: the right side of a binding, of a definition
//! without parameters or of a parameter or field default, when it reads no name (author,
//! A103; MUTATION.md 3.7).
//!
//! A mutant is named by its definition's source name, the position of the node in the
//! definition's kernel term, and the replacement, so the name does not change when other
//! declarations move; mutants are taken in that order (definitions by name, nodes in
//! preorder), never in the order of a hash.
//!
//! A mutant is skipped when the optimizer of today, the build stage (`stage::mix`, step
//! L1.28), gives its definition the same term as the original's: the two programs are then
//! the same program. Otherwise it is detected when a row of a table that reaches the
//! definition fails on it, and undetected when every such row passes.
//!
//! Mutants work on the original's elaborated unit: a mutant is the unit with one
//! definition's term replaced, so it costs that definition and the tables that reach it, not
//! a new parse, check or elaboration.

use std::collections::HashMap;
use std::mem;
use std::ops::Range;
use std::sync::Arc;

use zed_kernel::num::{LiteralRounding, TooLarge};
use zed_kernel::provenance::{Position, child, child_mut};
use zed_kernel::{Prim, Rat, Shared, Term, Value};

use crate::ast::{Blocks, Expr, ExprKind, Field, Stmt, StmtKind, expr_kids, stmts_exprs};
use crate::elab::mark::{self, Kind, Mark};
use crate::elab::{self, Cones, Unit};
use crate::lex;
use crate::lex::Span;
use crate::rows;
use crate::run::{self, Through};
use crate::source;
use crate::stage::{self, Remix};

/// What a mutant puts in place of a node, or what the node was.
#[derive(Clone, PartialEq, Debug)]
pub enum Change {
    /// A binary operator.
    Op(Prim),
    /// A numeric constant: its value, and its text when the literal is written as a decimal
    /// (`2.4` for a neighbor of `2.5`); an integer literal is written as its value.
    Num(Value, Option<String>),
    /// A node as it is written, for the report.
    Shown(Shown),
    /// An edit of the node, and the text the mutant writes there, for the report.
    Edit(Edit, Shown),
}

/// An edit of a node that replaces more than its operator or its value (MUTATION.md H2, H5
/// to H9, H11).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Edit {
    /// The right operand `b` of a comparison replaced by `b + 1` (`Prim::Add`) or `b - 1`
    /// (`Prim::Sub`), at `int` (H2).
    Shift(Prim),
    /// The two operands swapped (H11).
    Swap,
    /// The node put under the unary `-` or `!` (H6).
    Wrap(Prim),
    /// The child at this index, a condition or an operand of `&&` or `||`, put under `!` (H7,
    /// H9).
    Negate(u32),
    /// The `if` that `&&` elaborates to made the one of `||` (`true`), or back (`false`):
    /// `if a { b } else { false }` and `if a { true } else { b }` (H7).
    Flip(bool),
    /// The node replaced by its child at this index: a unary operator removed, an operand of
    /// `&&` or `||` dropped, an `if` replaced by a branch (H5, H7, H8, H9).
    Take(u32),
}

/// How the report writes a node or a mutant's replacement: pieces of the source and words
/// between them, rendered only when a mutant is reported ([`describe`]), so that making a
/// mutant costs O(1) whatever the length of the expression it changes.
// Complexity tradeoff: the text built when the mutant is made costs the length of its
// expression, O(n · depth) over the mutants of one nested expression, quadratic for a chain;
// the pieces cost O(1) each, and the text is built for the mutants reported, each in the
// length of the line it writes.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Shown(Vec<Piece>);

/// A piece of a [`Shown`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Piece {
    /// The source in this span, as written.
    Src(Span),
    /// The source in this span, in parentheses unless it is one name or number.
    Grouped(Span),
    /// These words.
    Word(&'static str),
}

impl Shown {
    fn of(pieces: &[Piece]) -> Shown {
        Shown(pieces.to_vec())
    }

    /// The text on one line: its comments dropped ([`uncommented`]) and its runs of white space
    /// each one space. A piece that is one group already, `(a + b)`, takes no parentheses more
    /// (`lex::in_parens`, which counts on the tokens, so a parenthesis in a string or a comment
    /// is not counted).
    fn render(&self, text: &str) -> String {
        let at = |s: Span| uncommented(text.get(s.start..s.end).unwrap_or(""));
        let mut out = String::new();
        for p in &self.0 {
            match *p {
                Piece::Src(s) => out.push_str(&at(s)),
                Piece::Word(w) => out.push_str(w),
                Piece::Grouped(s) => {
                    let t = at(s);
                    let plain =
                        (t.bytes()).all(|b| b.is_ascii_alphanumeric() || b"_'.".contains(&b));
                    match plain || lex::in_parens(&t) {
                        true => out.push_str(&t),
                        false => {
                            out.push('(');
                            out.push_str(&t);
                            out.push(')');
                        }
                    }
                }
            }
        }
        out.split_whitespace().collect::<Vec<_>>().join(" ")
    }
}

/// The program text `t` with each comment, `//` to the end of its line or a nested `/* */`,
/// replaced by one space: the report writes a mutant on one line, where a `//` comment would
/// hide the text after it (`(a) // first\n+ (b)` is written `(a) + (b)`). The comments are
/// found by the lexer (`lex::comments`), so `//` in a string is not one. Text that does not lex
/// is kept as written. O(length of `t`).
fn uncommented(t: &str) -> String {
    if !t.contains("//") && !t.contains("/*") {
        return t.to_string();
    }
    let Ok(tokens) = lex::lex(t) else {
        return t.to_string();
    };
    let mut out = String::with_capacity(t.len());
    let mut from = 0;
    for c in lex::comments(t, &tokens) {
        out.push_str(&t[from..c.start]);
        out.push(' ');
        from = c.end;
    }
    out.push_str(&t[from..]);
    out
}

/// One mutant: the node of a definition it replaces, and the replacement.
#[derive(Clone, Debug)]
pub struct Mutant {
    /// The definition's position in the unit.
    pub def: usize,
    /// The node's position in the definition's term: of an operator, the first in preorder of
    /// its nodes; of a constant, the last, its own value's ([`Self::also`]).
    pub at: Position,
    /// The other nodes of the same written operator or constant, which the mutant replaces too,
    /// each with what replaces it there: one in each arm of an operation on generic literals
    /// built once per carrier, and one in each arm of a generic literal taking its carrier
    /// (L1.26a); none elsewhere. An operator's arms take [`Self::to`]; a constant's arm takes
    /// its neighbor at that arm's carrier, as `2.0` is replaced by `1.0` where `2` is by `1`.
    pub also: Vec<(Position, Change)>,
    /// The node as written.
    pub was: Change,
    /// What replaces it.
    pub to: Change,
    /// Where the operator or constant is in the source.
    pub offset: usize,
}

/// What running the tables against a mutant found.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Verdict {
    /// A row of a table that reaches the definition fails.
    Detected,
    /// Every row that reaches the definition passes, or none reaches it: the reason.
    Undetected(&'static str),
    /// The build stage gives the mutant's definition the original's term.
    Skipped,
    /// No row that ran fails, and a row that reaches the definition was not run because the
    /// form of the mutant's row does not show that it ends.
    NotRun,
}

/// The operators that replace `p` (H1, H10); `quotient` says whether `/` is defined where `p`
/// is `*`. `^` and `++` have none: their errors are in the exponent and in the order
/// (MUTATION.md 3.11). H1 is the strictness part of \[Offutt96\]'s ROR and PIT's "Negate Cond."
/// (\[Laurent16\] Table 1, "== ⇝ !="); H10 is the part of \[Offutt96\]'s AOR that models a slip
/// to the neighboring key, not every legal operator (MUTATION.md 3.11). Tests:
/// `set::h1_h2_a_comparison_at_int_gives_its_neighbor_and_the_moved_bound`,
/// `set::h10_h11_the_arithmetic_operators_and_their_operand_order`.
fn neighbors(p: Prim, quotient: bool) -> &'static [Prim] {
    match p {
        Prim::Lt => &[Prim::Le],
        Prim::Le => &[Prim::Lt],
        Prim::Gt => &[Prim::Ge],
        Prim::Ge => &[Prim::Gt],
        Prim::Eq => &[Prim::Ne],
        Prim::Ne => &[Prim::Eq],
        Prim::Add => &[Prim::Sub],
        Prim::Sub => &[Prim::Add],
        Prim::Mul if quotient => &[Prim::Div],
        Prim::Mul => &[],
        Prim::Div => &[Prim::Mul],
        Prim::IntDiv => &[Prim::Mod],
        Prim::Mod => &[Prim::IntDiv],
        Prim::Pow | Prim::Concat => &[],
        // Cannot happen: the one caller, `operator`, is reached only from the arm of
        // `Mutants::of` that matches a marked `Term::Prim(p, ms)` against an unmarked
        // `Term::Prim(p, us)` with `us.len() == 2`. `mark::mark_of` finds a mark on a `Prim`
        // only when `mark::mutable(p)` holds, or on a `Neg` of a literal, whose unmarked term
        // is the literal itself (`Term::Lit`, the arm after it), never a `Prim`. The arms
        // above name the 14 operators `mutable` admits, each once.
        _ => unreachable!("only the operators `elab::mark::mutable` admits are marked"),
    }
}

/// The comparison `p` reversed (H3), for `<`, `<=`, `>` and `>=`: the rest of \[Offutt96\]'s
/// ROR, made only where H2 is not (MUTATION.md 3.1: at `int` any table that detects H2
/// detects it). Test: `set::h3_a_comparison_not_at_int_is_reversed`.
fn reversed(p: Prim) -> Option<Prim> {
    match p {
        Prim::Lt => Some(Prim::Gt),
        Prim::Gt => Some(Prim::Lt),
        Prim::Le => Some(Prim::Ge),
        Prim::Ge => Some(Prim::Le),
        _ => None,
    }
}

/// The message when the system refuses the memory for a neighbor of a literal.
fn refused(e: TooLarge) -> String {
    format!(
        "Number too large for memory: a neighbor of a literal needs {}",
        e.number()
    )
}

/// The neighbors `n - 1` and `n + 1` of the integer literal `n`, at the carrier it adopted:
/// `int`, `rat`, `f64` or `f32`; an error when the system refuses the memory to build one.
fn beside(n: &Value) -> Result<[Value; 2], String> {
    let exact = |r: &Rat| -> Result<[Rat; 2], String> {
        let one = Rat::int(1.into());
        Ok([r.sub(&one).map_err(refused)?, r.add(&one).map_err(refused)?])
    };
    match n {
        Value::Rat(r) => Ok(exact(r)?.map(Value::rat)),
        Value::Float(x) => Ok([Value::float(x.get() - 1.0), Value::float(x.get() + 1.0)]),
        Value::Float32(x) => Ok([Value::float32(x.get() - 1.0), Value::float32(x.get() + 1.0)]),
        _ => {
            let n = n
                .as_integer()
                .expect("an integer literal is an int, a rat, an f64 or an f32");
            Ok(exact(&n)?.map(Value::integer))
        }
    }
}

/// A decimal literal's text read for its neighbors (H4): the digits of its significand with
/// the point removed, how many of them follow the point, its exponent as written (`e-3`, or
/// empty) and its suffix (`r`, `f32`, …, or empty).
struct Decimal<'t> {
    digits: String,
    frac: usize,
    exp: &'t str,
    suffix: &'t str,
}

/// `t` read as a decimal literal ([`Decimal`]), when it is one: digits with a point, an
/// exponent or a suffix, and not an integer in base 2, 8 or 16. `None` for an integer
/// literal, whose neighbors are its value's ([`beside`]).
fn decimal(t: &str) -> Option<Decimal<'_>> {
    if t.len() > 1 && t.starts_with('0') && t[1..].starts_with(['x', 'X', 'b', 'B', 'o', 'O']) {
        return None;
    }
    let suffix_at = ["bf16", "f16", "f32", "f64", "r"]
        .iter()
        .find(|s| t.ends_with(*s))
        .map_or(t.len(), |s| t.len() - s.len());
    let (body, suffix) = t.split_at(suffix_at);
    let exp_at = body.find(['e', 'E']).unwrap_or(body.len());
    let (significand, exp) = body.split_at(exp_at);
    let (whole, frac) = significand.split_once('.').unwrap_or((significand, ""));
    let digit_run = |s: &str| s.bytes().all(|b| b.is_ascii_digit() || b == b'_');
    let exp_ok = exp.is_empty() || {
        let e = exp[1..].strip_prefix(['+', '-']).unwrap_or(&exp[1..]);
        !e.is_empty() && digit_run(e)
    };
    let decimal = significand.contains('.') || !exp.is_empty() || !suffix.is_empty();
    if !decimal || !digit_run(whole) || !digit_run(frac) || !exp_ok || whole.len() + frac.len() == 0
    {
        return None;
    }
    let frac_digits = frac.bytes().filter(|&b| b != b'_').count();
    let digits: String = (whole.chars().chain(frac.chars()))
        .filter(|&c| c != '_')
        .collect();
    (!digits.is_empty()).then_some(Decimal {
        digits,
        frac: frac_digits,
        exp,
        suffix,
    })
}

/// The text of one unit of the last digit of `d` taken down (`up` false) or up, without the
/// suffix: `2.5` gives `2.4` and `2.6`, `0.0` gives `-0.1`, `1e-3` gives `0e-3`, exactly, on
/// the digits as written.
// Complexity tradeoff: O(digits), one pass of the carry or borrow over the written digits,
// against reading the literal as a rational and back, which costs a multiplication by a power
// of ten and a conversion to text, O(digits log digits) or more.
fn stepped(d: &Decimal<'_>, up: bool) -> String {
    let mut digits: Vec<u8> = d.digits.bytes().collect();
    let negative = !up && digits.iter().all(|&b| b == b'0');
    // `digits` is not empty: `decimal` returns `None` when no digit is written. The loop below
    // stops before `i` passes 0: going up, it stops at the first digit below 9 or inserts a
    // `1` at `i == 0`; going down, `negative` is false, so some digit is not 0, and the borrow
    // stops at the last such digit. Test: `set::h4_a_decimal_literal_moves_by_one_unit_of_its_
    // last_digit`, at `0.0`, `0.1`, `1.9`, `9.9` (the inserted `1`) and `10.0`; it cannot
    // show the loop stops for every digit string, which the argument covers.
    if negative {
        // 0 - 1 = -1, one unit of the last digit below zero.
        *digits.last_mut().expect("a digit") = b'1';
    } else {
        let mut i = digits.len();
        loop {
            i -= 1;
            match (up, digits[i]) {
                (true, b'9') => {
                    digits[i] = b'0';
                    if i == 0 {
                        digits.insert(0, b'1');
                        break;
                    }
                }
                (false, b'0') => digits[i] = b'9',
                (true, _) => {
                    digits[i] += 1;
                    break;
                }
                (false, _) => {
                    digits[i] -= 1;
                    break;
                }
            }
        }
    }
    while digits.len() <= d.frac {
        digits.insert(0, b'0');
    }
    let (whole, frac) = digits.split_at(digits.len() - d.frac);
    let lead = whole
        .iter()
        .take_while(|&&b| b == b'0')
        .count()
        .min(whole.len() - 1);
    let mut out = String::from(if negative { "-" } else { "" });
    out.push_str(std::str::from_utf8(&whole[lead..]).expect("ASCII digits"));
    if d.frac > 0 {
        out.push('.');
        out.push_str(std::str::from_utf8(frac).expect("ASCII digits"));
    }
    out.push_str(d.exp);
    out
}

/// The value of the exact decimal `r` at the carrier of `like`: `f64` and `f32` rounded to
/// nearest, ties to even ([`Rat::to_f64`]), past the largest float its infinity and below the
/// least its zero, of `r`'s sign; `rat` exact. `None` at another carrier.
fn at_carrier(r: &Rat, like: &Value) -> Result<Option<Value>, String> {
    let neg = r.is_negative();
    let rounded = |e: LiteralRounding, inf: f64| match e {
        LiteralRounding::Infinite => Ok(if neg { -inf } else { inf }),
        LiteralRounding::Zero => Ok(if neg { -0.0 } else { 0.0 }),
        LiteralRounding::TooLarge(e) => Err(refused(e)),
    };
    Ok(Some(match like {
        Value::Float(_) => Value::float(r.to_f64().or_else(|e| rounded(e, f64::INFINITY))?),
        Value::Float32(_) => {
            let x = match r.to_f32() {
                Ok(x) => x,
                Err(e) => rounded(e, f64::INFINITY)? as f32,
            };
            Value::float32(x)
        }
        Value::Rat(_) => Value::rat(r.clone()),
        _ => return Ok(None),
    }))
}

/// The neighbors of the literal written `t` whose value in this arm is `v` (H4), each with its
/// text where it is written as a decimal; `drop` names the one left out (`0` the one below,
/// `1` the one above) where it is the H1 mutant of the comparison it is an operand of again
/// (MUTATION.md 3.1). PIT's "Inline Const." adds one to an integer (\[Laurent16\] Table 1,
/// "1 ⇝ 0, a ⇝ a + 1"); here the step is one unit of the last written digit, both ways, the
/// step a person reads off the text (MUTATION.md 3.7). Tests: `set::h4_*`.
fn literal_neighbors(t: &str, v: &Value, drop: Option<usize>) -> Result<Vec<Change>, String> {
    let both: Vec<Change> = match decimal(t) {
        Some(d) => {
            let mut out = Vec::with_capacity(2);
            for (up, near) in [false, true].into_iter().zip(beside(v)?) {
                let text = stepped(&d, up);
                let r = Rat::decimal(&text)
                    .map_err(refused)?
                    .expect("the neighbor's text is a decimal");
                // At a carrier other than `rat`, `f64` and `f32` (none a decimal literal takes
                // today), the neighbor of the value.
                out.push(match at_carrier(&r, v)? {
                    Some(w) => Change::Num(w, Some(format!("{text}{}", d.suffix))),
                    None => Change::Num(near, None),
                });
            }
            out
        }
        None => beside(v)?
            .into_iter()
            .map(|w| Change::Num(w, None))
            .collect(),
    };
    Ok((both.into_iter().enumerate())
        .filter(|(i, _)| Some(*i) != drop)
        .map(|(_, c)| c)
        .collect())
}

/// The constant as written, for the report: its text where it is a decimal, its value
/// otherwise.
fn literal_was(t: &str, v: &Value) -> Change {
    Change::Num(v.clone(), decimal(t).map(|_| t.to_string()))
}

/// The offset of the operator in the text between its operands, `gap`: the start of its first
/// token that is not a parenthesis, so white space and comments, `//` and `/* */` alike, are
/// passed over by the lexer. A scan of the bytes that knew only `//`, as before, put the
/// operator of `a /* x */ + b` at the `/`. O(length of the gap).
fn operator_at(text: &str, gap: Span) -> usize {
    let tokens = text.get(gap.start..gap.end).map(lex::lex);
    let first = tokens
        .and_then(Result::ok)
        .and_then(|ts| (ts.into_iter()).find(|t| !matches!(t.tok, lex::Tok::Op("(" | ")"))));
    first.map_or(gap.start, |t| gap.start + t.span.start)
}

/// The spans of the declared constants of a unit (author, A103; MUTATION.md 3.7), merged
/// where they overlap and sorted: the right side of a binding, of a definition without
/// parameters, and of a parameter or field default, where it reads no name.
struct Declared(Vec<Span>);

impl Declared {
    /// The declared constants of `stmts`.
    // Complexity tradeoff: one walk over the expressions of the unit, with each expression's
    // parent, then one pass in reverse to tell which read a name, O(n), and a sort of the
    // spans, O(k log k); asking each right side separately whether it reads a name costs its
    // size, O(n · depth) where right sides nest (`a = { b = 1; b };`).
    fn of(stmts: &[Stmt]) -> Declared {
        let mut sides: Vec<&Expr> = Vec::new();
        scan(stmts, &mut sides);
        let mut nodes: Vec<(&Expr, usize)> = Vec::new();
        let mut work: Vec<(&Expr, usize)> = Vec::new();
        stmts_exprs(stmts, &mut |e| work.push((e, usize::MAX)));
        while let Some((e, parent)) = work.pop() {
            let i = nodes.len();
            nodes.push((e, parent));
            match &e.kind {
                ExprKind::Block(ss) => scan(ss, &mut sides),
                ExprKind::Lambda { params, .. } => {
                    sides.extend(params.iter().filter_map(|p| p.default.as_ref()));
                }
                _ => {}
            }
            expr_kids(&e.kind, Blocks::Enter, &mut |k| work.push((k, i)));
        }
        // A child is pushed when its parent is visited and visited after it, so its index is
        // larger: in reverse order each node is final before its parent reads it.
        let mut reads = vec![false; nodes.len()];
        for i in (0..nodes.len()).rev() {
            let (e, parent) = nodes[i];
            reads[i] |= matches!(e.kind, ExprKind::Name(_) | ExprKind::This);
            if reads[i] && parent != usize::MAX {
                reads[parent] = true;
            }
        }
        let index: HashMap<*const Expr, usize> = (nodes.iter().enumerate())
            .map(|(i, (e, _))| (*e as *const Expr, i))
            .collect();
        let mut spans: Vec<Span> = (sides.iter())
            .filter(|e| index.get(&(**e as *const Expr)).is_some_and(|&i| !reads[i]))
            .map(|e| e.span)
            .collect();
        spans.sort_by_key(|s| (s.start, s.end));
        let mut merged: Vec<Span> = Vec::with_capacity(spans.len());
        for s in spans {
            match merged.last_mut() {
                Some(last) if s.start <= last.end => last.end = last.end.max(s.end),
                _ => merged.push(s),
            }
        }
        Declared(merged)
    }

    /// Whether `s` lies in a declared constant: O(log k) by binary search.
    fn covers(&self, s: Span) -> bool {
        let before = self.0.partition_point(|d| d.start <= s.start);
        before > 0 && self.0[before - 1].end >= s.end
    }
}

/// Adds to `sides` the right sides in `stmts`, not inside its expressions, that are declared
/// constants where they read no name ([`Declared`]).
fn scan<'a>(stmts: &'a [Stmt], sides: &mut Vec<&'a Expr>) {
    for s in stmts {
        let mut kind = &s.kind;
        loop {
            match kind {
                StmtKind::Local(d) => kind = &d.kind,
                StmtKind::Annotated { decl, .. } => kind = &decl.kind,
                _ => break,
            }
        }
        let defaults = |params: &'a [crate::ast::Param], sides: &mut Vec<&'a Expr>| {
            sides.extend(params.iter().filter_map(|p| p.default.as_ref()));
        };
        match kind {
            StmtKind::Bind { value, .. } => sides.push(value),
            StmtKind::Function(f) => {
                defaults(&f.params, sides);
                if f.params.is_empty() && f.main.is_none() {
                    sides.push(&f.body);
                }
            }
            StmtKind::Method(m) => defaults(&m.function.params, sides),
            StmtKind::Struct(st) => sides.extend(st.fields.iter().filter_map(|f| match f {
                Field::Typed { default, .. } => default.as_ref(),
                _ => None,
            })),
            _ => {}
        }
    }
}

/// The mutants of `unit`, the elaboration of `stmts`, whose text is `text`: definitions by
/// source name, then nodes in preorder, then replacements in the order of MUTATION.md
/// section 6 for each node (`n - 1` before `n + 1`). Finding them elaborates `stmts` once
/// more, with marks ([`elab::elaborate_marked`]), and reads each node of each definition
/// once; no mutant's term is built.
pub fn mutants(text: &str, stmts: &[Stmt], unit: &Unit) -> Result<Vec<Mutant>, String> {
    let res = crate::resolve::resolve(stmts)
        .map_err(|_| "the unit, which compiled, does not resolve again".to_string())?;
    let (marked, marks) = elab::elaborate_marked(stmts, &res)
        .map_err(|_| "the unit, which compiled, does not elaborate again with marks".to_string())?;
    if marked.defs.len() != unit.defs.len() {
        return Err(format!(
            "the marked elaboration has {} definitions and the unit {}",
            marked.defs.len(),
            unit.defs.len()
        ));
    }
    let declared = Declared::of(stmts);
    let mut order: Vec<usize> = (0..unit.defs.len()).collect();
    order.sort_by(|&a, &b| unit.defs[a].name.cmp(&unit.defs[b].name).then(a.cmp(&b)));
    let mut out = Vec::new();
    for def in order {
        let (m, u) = (&marked.defs[def], &unit.defs[def]);
        if m.name != u.name {
            return Err(format!(
                "definition {def} is `{}` in the marked elaboration and `{}` in the unit",
                m.name, u.name
            ));
        }
        let site = Site {
            text,
            def,
            marks: &marks,
            declared: &declared,
        };
        site.walk(&m.term, &u.term, &mut out)?;
    }
    Ok(out)
}

/// What the walk of one definition reads ([`Site::walk`]).
struct Site<'a> {
    text: &'a str,
    def: usize,
    marks: &'a [Mark],
    declared: &'a Declared,
}

/// Whether the marked term `t` is a written `!` (H7, H9: no `!` is inserted before one).
fn written_not(t: &Term) -> bool {
    mark::wrapped(t).is_some_and(|(inner, _)| matches!(inner, Term::Prim(Prim::Not, _)))
}

impl Site<'_> {
    /// Adds the mutants of the definition to `out`, walking its marked term `m` and its term
    /// `u` together in preorder, with an explicit stack. Each entry carries which neighbor of
    /// a literal below it to leave out (MUTATION.md 3.1), set at an `int` comparison for its
    /// literal operand and reversed under a `-`.
    fn walk(&self, m: &Term, u: &Term, out: &mut Vec<Mutant>) -> Result<(), String> {
        let def = self.def;
        // The mutants made at each mark, by its index, so a mark met again adds its node to
        // them; for an operator, also the operator it was.
        let mut first: HashMap<usize, (Range<usize>, Option<Prim>)> = HashMap::new();
        let mut stack = vec![(m, u, Position::root(), None::<usize>)];
        while let Some((m, u, at, drop)) = stack.pop() {
            let differs = |what: &str| {
                Err(format!(
                    "definition {def}'s marked elaboration differs from its elaboration at {at}: {what}"
                ))
            };
            if let Some((inner, k)) = mark::wrapped(m) {
                let Some(mark) = self.marks.get(k) else {
                    return differs("a mark has no entry");
                };
                stack.push((inner, u, at.clone(), None));
                if self.declared.covers(mark.span) {
                    continue;
                }
                if let Some((made, _)) = first.get(&k) {
                    for x in &mut out[made.clone()] {
                        x.also.push((at.clone(), x.to.clone()));
                    }
                    continue;
                }
                let Some((offset, made)) = self.wrapped(mark, inner, u) else {
                    return differs("a marked node has another shape");
                };
                let start = out.len();
                out.extend(made.into_iter().map(|(was, to)| Mutant {
                    def,
                    at: at.clone(),
                    also: Vec::new(),
                    was,
                    to,
                    offset,
                }));
                first.insert(k, (start..out.len(), None));
                continue;
            }
            if let Some(k) = mark::mark_of(m) {
                let Some(mark) = self.marks.get(k) else {
                    return differs("a mark has no entry");
                };
                let skip = self.declared.covers(mark.span);
                match (m, u) {
                    (Term::Prim(p, ms), Term::Prim(q, us)) if p == q && us.len() == 2 => {
                        // At an `int` comparison, the neighbor of a literal operand that is the
                        // strictness neighbor again: `b + 1` and `a - 1` for `<` and `>=`,
                        // `b - 1` and `a + 1` for `<=` and `>` (MUTATION.md 3.1).
                        let duplicate = |i: usize| match (mark.ints, mark.literal[i], p) {
                            (true, true, Prim::Lt | Prim::Ge) => Some(i),
                            (true, true, Prim::Le | Prim::Gt) => Some(1 - i),
                            _ => None,
                        };
                        stack.push((&ms[1], &us[1], at.child(1), duplicate(1)));
                        stack.push((&ms[0], &us[0], at.child(0), duplicate(0)));
                        if skip {
                            continue;
                        }
                        if let Some((made, was)) = first.get(&k) {
                            if *was != Some(*p) {
                                return differs("one mark is on nodes of two kinds");
                            }
                            for x in &mut out[made.clone()] {
                                x.also.push((at.clone(), x.to.clone()));
                            }
                            continue;
                        }
                        let offset = operator_at(self.text, mark.span);
                        let start = out.len();
                        out.extend(self.operator(mark, *p).into_iter().map(|(was, to)| Mutant {
                            def,
                            at: at.clone(),
                            also: Vec::new(),
                            was,
                            to,
                            offset,
                        }));
                        first.insert(k, (start..out.len(), Some(*p)));
                    }
                    (Term::Prim(Prim::Neg, ms), Term::Lit(v)) if matches!(&ms[0], Term::Lit(w) if w == v) =>
                    {
                        if skip {
                            continue;
                        }
                        let t = (self.text.get(mark.span.start..mark.span.end)).unwrap_or("");
                        let was = literal_was(t, v);
                        // One written constant is a node in each arm of a generic literal
                        // taking its carrier (`elab::walk::marked_as`), of that arm's value:
                        // each mutant replaces it in every arm by its neighbor there, and is
                        // named by the last node, the literal's own value, which the source
                        // writes.
                        let to = literal_neighbors(t, v, drop)?;
                        if let Some((made, _)) = first.get(&k) {
                            let made = &mut out[made.clone()];
                            if made.iter().any(|x| !matches!(x.was, Change::Num(..))) {
                                return differs("one mark is on nodes of two kinds");
                            }
                            for (x, to) in made.iter_mut().zip(to) {
                                let at = mem::replace(&mut x.at, at.clone());
                                let to = mem::replace(&mut x.to, to);
                                x.also.push((at, to));
                                x.was = was.clone();
                            }
                            continue;
                        }
                        let start = out.len();
                        out.extend(to.into_iter().map(|to| Mutant {
                            def,
                            at: at.clone(),
                            also: Vec::new(),
                            was: was.clone(),
                            to,
                            offset: mark.span.start,
                        }));
                        first.insert(k, (start..out.len(), None));
                    }
                    _ => return differs("a marked node has another shape"),
                }
                continue;
            }
            if std::mem::discriminant(m) != std::mem::discriminant(u) {
                return differs("the nodes are of different kinds");
            }
            // Under a `-`, a literal's neighbor below moves the operand up.
            let drop = match m {
                Term::Prim(Prim::Neg, _) => drop.map(|d| 1 - d),
                _ => drop,
            };
            let mut kids = Vec::new();
            let mut i = 0;
            while let Some(mc) = child(m, i) {
                let Some(uc) = child(u, i) else {
                    return differs("the marked node has more children");
                };
                kids.push((mc, uc, at.child(i), drop));
                i += 1;
            }
            if child(u, i).is_some() {
                return differs("the marked node has fewer children");
            }
            stack.extend(kids.into_iter().rev());
        }
        Ok(())
    }

    /// The mutants of the marked binary operator `p` (H1 to H3, H6, H10, H11), each as what
    /// it was and what replaces it, in the order of MUTATION.md section 6. H6 is \[Offutt96\]'s
    /// UOI and ABS and PIT's "ABS" (\[Laurent16\], "a ⇝ -a") at the root of an arithmetic
    /// expression only: it lives only where every row gives the expression the value zero, the
    /// gap ABS exists to show, and a negated inner node asks for no row the root does not
    /// (MUTATION.md 3.2); H11, the
    /// operand swap, is in none of these papers and is derived in MUTATION.md 3.9. Tests:
    /// `set::h6_a_minus_is_inserted_at_the_root_of_an_arithmetic_expression`,
    /// `set::h10_h11_the_arithmetic_operators_and_their_operand_order`.
    fn operator(&self, mark: &Mark, p: Prim) -> Vec<(Change, Change)> {
        use Piece::{Grouped, Src, Word};
        let [l, r, whole] = mark.parts;
        let span = |start, end| Span { start, end };
        let shown = Change::Shown(Shown::of(&[Src(whole)]));
        let mut out: Vec<(Change, Change)> = (neighbors(p, mark.quotient).iter())
            .map(|&q| (Change::Op(p), Change::Op(q)))
            .collect();
        if let Some(q) = reversed(p) {
            match mark.ints {
                // H2, where neither operand is a literal, whose neighbors move the bound: the
                // second of the two points next to the border, derived in MUTATION.md 3.1 (module
                // doc, the H2 entry of the literature).
                true if mark.literal == [false; 2] => {
                    let (step, word) = match p {
                        Prim::Lt | Prim::Ge => (Prim::Sub, " - 1"),
                        _ => (Prim::Add, " + 1"),
                    };
                    let to = Shown::of(&[
                        Src(span(whole.start, r.end)),
                        Word(word),
                        Src(span(r.end, whole.end)),
                    ]);
                    out.push((shown.clone(), Change::Edit(Edit::Shift(step), to)));
                }
                true => {}
                false => out.push((Change::Op(p), Change::Op(q))),
            }
        }
        let swapped = match p {
            Prim::Sub | Prim::Div | Prim::IntDiv | Prim::Mod | Prim::Concat => true,
            Prim::Pow => mark.ints,
            _ => false,
        };
        if swapped {
            let to = Shown::of(&[
                Src(span(whole.start, l.start)),
                Grouped(r),
                Src(span(l.end, r.start)),
                Grouped(l),
                Src(span(r.end, whole.end)),
            ]);
            out.push((shown.clone(), Change::Edit(Edit::Swap, to)));
        }
        if mark::arithmetic(p) && !mark.inner && p != Prim::Sub {
            let to = Shown::of(&[Word("-("), Src(whole), Word(")")]);
            out.push((shown, Change::Edit(Edit::Wrap(Prim::Neg), to)));
        }
        out
    }

    /// The offset and the mutants of the node of a wrapped mark (H5, H7 to H9), `inner` its
    /// marked term and `u` its term; `None` where the terms are not of the mark's shape. H7 is
    /// \[Offutt96\]'s LCR with \[Kuhn99\]'s missing condition (PIT's "AOD", \[Laurent16\]) and
    /// variable negation; H5 and H8 are PIT's "Invert Neg." ("-a ⇝ a"); H9 is PIT's "Remove
    /// Cond." with \[Kuhn99\]'s expression negation (MUTATION.md 3.8, 3.10). Tests: `set::h5_*`,
    /// `set::h7_*`, `set::h8_*`, `set::h9_*`.
    fn wrapped(
        &self,
        mark: &Mark,
        inner: &Term,
        u: &Term,
    ) -> Option<(usize, Vec<(Change, Change)>)> {
        use Piece::{Grouped, Src, Word};
        let span = |start, end| Span { start, end };
        // `!` before the part `part`, within `whole`.
        let negated = |part: Span, whole: Span| {
            Shown::of(&[
                Src(span(whole.start, part.start)),
                Word("!"),
                Grouped(part),
                Src(span(part.end, whole.end)),
            ])
        };
        let take = |i, part| Change::Edit(Edit::Take(i), Shown::of(&[Src(part)]));
        match (mark.kind, inner, u) {
            (Kind::Unary, Term::Prim(p, _), Term::Prim(q, _)) if p == q => {
                let [operand, whole, _] = mark.parts;
                let was = Change::Shown(Shown::of(&[Src(whole)]));
                Some((mark.span.start, vec![(was, take(0, operand))]))
            }
            (Kind::Bool { or }, Term::If(c, x, y), Term::If(..)) => {
                let [l, r, whole] = mark.parts;
                let (words, other) = match or {
                    true => (["||", "&&"], y),
                    false => (["&&", "||"], x),
                };
                let was = Change::Shown(Shown::of(&[Src(whole)]));
                let flip = Change::Edit(Edit::Flip(!or), Shown::of(&[Word(words[1])]));
                let right = if or { 2 } else { 1 };
                let mut out = vec![
                    (Change::Shown(Shown::of(&[Word(words[0])])), flip),
                    (was.clone(), take(0, l)),
                    (was.clone(), take(right, r)),
                ];
                if !written_not(c) {
                    let to = Change::Edit(Edit::Negate(0), negated(l, whole));
                    out.push((was.clone(), to));
                }
                if !written_not(other) {
                    out.push((was, Change::Edit(Edit::Negate(right), negated(r, whole))));
                }
                Some((operator_at(self.text, mark.span), out))
            }
            (Kind::If, Term::If(c, _, _), Term::If(..)) => {
                let [cond, then, otherwise] = mark.parts;
                let was = Change::Shown(Shown::of(&[Src(mark.span)]));
                let mut out = vec![
                    (was.clone(), take(1, then)),
                    (was.clone(), take(2, otherwise)),
                ];
                if !written_not(c) {
                    out.push((was, Change::Edit(Edit::Negate(0), negated(cond, mark.span))));
                }
                Some((mark.span.start, out))
            }
            _ => None,
        }
    }
}

/// `term` with each node of `at` replaced as its change says: one copy of `term`, O(its size, the
/// order of the remix that follows), then each node changed in place. The copy shares what
/// `term` holds behind an `Arc` until the path to a node reaches it ([`child_mut`]). `at` holds
/// one node, or one per carrier of an operation on generic literals or of a generic literal
/// ([`Mutant::also`]), each with what replaces it.
pub fn apply<'p>(term: &Term, at: impl IntoIterator<Item = (&'p Position, &'p Change)>) -> Term {
    // Complexity tradeoff (COMPLEXITY.md F58): a rebuild along the path by `with_child`, which
    // copies each inline child list, costs O(size × depth), cubic over the mutants of one
    // chain; one copy of the term and the nodes changed in place through `child_mut` costs
    // O(size + k × depth) for k ≤ 6 nodes, the order of the remix that follows. Precondition:
    // each position lies in `term`.
    let mut out = term.clone();
    for (at, to) in at {
        let mut node = &mut out;
        for i in at.path() {
            node = child_mut(node, i).expect("a mutant's position is in its definition");
        }
        match (node, to) {
            (Term::Prim(p, _), Change::Op(q)) => *p = *q,
            (Term::Lit(v), Change::Num(w, _)) => *v = w.clone(),
            (node, Change::Edit(e, _)) => edit(node, *e),
            _ => unreachable!("a mutant replaces an operator by one, a constant by one"),
        }
    }
    out
}

/// `node` changed by `e` in place, O(1) but for the copy of a shared child it reads.
fn edit(node: &mut Term, e: Edit) {
    let hole = || Term::Lit(Value::Bool(false));
    let under = |p: Prim, t: &mut Term| {
        let inner = mem::replace(t, hole());
        *t = Term::Prim(p, vec![inner]);
    };
    match (e, &mut *node) {
        (Edit::Shift(p), Term::Prim(_, args)) => {
            let b = mem::replace(&mut args[1], hole());
            args[1] = Term::Prim(p, vec![b, Term::Lit(Value::Int(1))]);
        }
        (Edit::Swap, Term::Prim(_, args)) => args.swap(0, 1),
        (Edit::Wrap(p), node) => under(p, node),
        (Edit::Negate(i), node) => {
            under(
                Prim::Not,
                child_mut(node, i).expect("a condition or an operand"),
            );
        }
        (Edit::Flip(or), Term::If(_, a, b)) => {
            let t = |v: bool| Shared::new(Term::Lit(Value::Bool(v)));
            // `if c { x } else { false }` to `if c { true } else { x }`, and back.
            match or {
                true => *b = mem::replace(a, t(true)),
                false => *a = mem::replace(b, t(false)),
            }
        }
        (Edit::Take(i), node) => {
            let kept = child(node, i).expect("a branch or an operand").clone();
            *node = kept;
        }
        _ => unreachable!("an edit of an operator or an `if` of its own shape"),
    }
}

/// The program of the original unit `unit`, elaborated from `stmts`, sharing `unit`: none when
/// the unit has no `main` or `run::program` refuses it, and its `main` rows then do not run.
fn original(stmts: &[Stmt], unit: &Arc<Unit>) -> Option<run::Program> {
    let has_main = stmts
        .iter()
        .any(|s| matches!(&s.bare().kind, StmtKind::Function(f) if f.name == "main"));
    if has_main {
        run::program(stmts, Arc::clone(unit)).ok()
    } else {
        None
    }
}

/// Each mutant of the unit `unit`, elaborated from `stmts`, with its verdict, in the order of
/// [`mutants`]. Each row's closed term is run by `map`. The caller has run the tables against
/// the original, and they pass. The original's program shares `unit`.
pub fn run(
    text: &str,
    stmts: &[Stmt],
    unit: &Arc<Unit>,
    map: &Through<'_>,
) -> Result<Vec<(Mutant, Verdict)>, String> {
    let mutants = mutants(text, stmts, unit)?;
    let cones = Cones::new(unit);
    let program = original(stmts, unit);
    let main = unit.defs.iter().find(|d| d.name == "main");
    // The rows that reach each definition, in written order: an index built once from each
    // row's cone, so a mutant finds its rows by its definition.
    // A row `zedc test` does not run, of a function only branches the build does not take
    // reach (plan row TEST-staged), detects no mutant: it is in no definition's list.
    let untaken = (program.as_ref())
        .map(|p| p.stage().1.untaken)
        .unwrap_or_default();
    let mut rows: Vec<Vec<usize>> = vec![Vec::new(); unit.defs.len()];
    for (j, t) in unit.tests.iter().enumerate() {
        if untaken.contains(&t.kernel) {
            continue;
        }
        let reach = match (t.function.as_str(), main, &program) {
            ("main", Some(main), Some(_)) => {
                let main = Term::Var(main.kernel.clone());
                let mut roots = vec![&main, &t.want];
                roots.extend(&t.args);
                cones.reach(&roots)
            }
            ("main", _, _) => continue,
            _ => cones.reach(&[&t.check]),
        };
        for i in reach {
            rows[i].push(j);
        }
    }
    let (_, mut remix) = Remix::new(unit);
    let mut built: Vec<Option<Term>> = vec![None; unit.defs.len()];
    let mut out = Vec::with_capacity(mutants.len());
    for mutant in mutants {
        let def = mutant.def;
        let original = &unit.defs[def].term;
        if built[def].is_none() {
            built[def] = Some(remix.mix(original));
        }
        let at = std::iter::once((&mutant.at, &mutant.to))
            .chain(mutant.also.iter().map(|(at, to)| (at, to)));
        let term = Shared::new(apply(original, at));
        let verdict = if built[def].as_ref() == Some(&remix.mix(&term)) {
            Verdict::Skipped
        } else if rows[def].is_empty() && untaken.contains(&unit.defs[def].kernel) {
            Verdict::Undetected(
                "the build takes no branch that reaches the definition, so no row that reaches it runs",
            )
        } else if rows[def].is_empty() {
            Verdict::Undetected("no table reaches the definition")
        } else {
            let swap = Some((def, &term));
            let mut verdict = Verdict::Undetected("every row that reaches it passes");
            for &j in &rows[def] {
                let t = &unit.tests[j];
                let closed = match (t.function.as_str(), main) {
                    ("main", Some(main)) => {
                        let main = Term::Var(main.kernel.clone());
                        let mut roots: Vec<Term> = vec![cones.close_with(main, swap)];
                        roots.push(cones.close_with(t.want.clone(), swap));
                        roots.extend(t.args.iter().map(|a| cones.close_with(a.clone(), swap)));
                        roots
                    }
                    _ => vec![cones.close_with(t.check.clone(), swap)],
                };
                // Complexity tradeoff: a row of a mutant runs only when the form of its
                // closed term shows that it ends (`stage::ends`, docs/thresholds.md,
                // replacement 6). What is given up: a row whose form does not show it, though
                // it may end, is not run against the mutant, and a mutant with such a row
                // and no failing row is reported "not run", never detected or undetected.
                // Why: a mutant may not end where the original does (`if x > 0 { w(w) }`
                // with `0` replaced by `-1` never ends), whether it ends is undecidable, and
                // a step count would switch behavior at a size. Trigger: a call through a
                // parameter or a pattern variable in the row's closed term, as in `w(w)` or
                // `twice(f: inc, x)` (L1 has no recursion; `fix` and `gen` would also
                // trigger it). Test:
                // `l25_08_mutate::examples::a_mutant_whose_row_may_not_end_is_not_run`.
                // COMPLEXITY.md row F58. A complete solution cannot exist; a stronger sound
                // one would add a termination proof by decreasing measures (size-change
                // termination, PSPACE-complete in the call graph), as `stage::ends` says.
                // Naive version: every row run, which need not end; used: the form check of
                // `stage::ends`, in time near the number of distinct parts of the term.
                if !closed.iter().all(stage::ends) {
                    verdict = Verdict::NotRun;
                    continue;
                }
                let failed = match (t.function.as_str(), &program) {
                    ("main", Some(p)) => rows::wave(&cones, swap, p, t, map).is_err(),
                    _ => rows::row(&cones, swap, t, map).is_err(),
                };
                if failed {
                    verdict = Verdict::Detected;
                    break;
                }
            }
            verdict
        };
        out.push((mutant, verdict));
    }
    Ok(out)
}

/// The text a report gives for `c`, of the unit whose text is `text`. A wide number's digits
/// are written only after the system gives the memory to build and write them
/// ([`Rat::text_room`]); when it refuses, the report names the number by that memory instead
/// of an abort.
fn reported(text: &str, c: &Change) -> String {
    match c {
        Change::Op(p) => p.written().to_string(),
        Change::Num(_, Some(t)) => t.clone(),
        Change::Num(v @ (Value::Big(r) | Value::Rat(r)), None) => match r.text_room() {
            Ok(()) => v.to_string(),
            Err(e) => format!("an integer of {}", e.amount("")),
        },
        Change::Num(v, None) => v.to_string(),
        Change::Shown(s) | Change::Edit(_, s) => s.render(text),
    }
}

/// The report of a mutant whose verdict is not `Detected`: `line:col: verdict: …`, with
/// `name` the definition's source name.
pub fn describe(text: &str, name: &str, m: &Mutant, v: &Verdict) -> Option<String> {
    let (line, col) = source::line_col(text.as_bytes(), m.offset);
    let (was, to) = (reported(text, &m.was), reported(text, &m.to));
    let what = format!("`{was}` replaced by `{to}` in `{name}` at {}", m.at);
    let says = match v {
        Verdict::Detected => return None,
        Verdict::Undetected(why) => format!("undetected: {what}: {why}"),
        Verdict::Skipped => {
            format!("skipped: {what}: the build stage gives the definition the original's term")
        }
        Verdict::NotRun => format!(
            "not run: {what}: no row that ran fails, and the form of a row that reaches it \
             does not show that it ends"
        ),
    };
    Some(format!("{line}:{col}: {says}"))
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::original;
    use crate::query::Db;

    #[test]
    fn the_original_program_of_a_mutation_run_shares_the_unit_of_the_front_end() {
        let front = Db::new().front("main(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n");
        let Ok((stmts, unit, _)) = &*front else {
            panic!("the unit is accepted")
        };
        let p = original(stmts, unit).expect("`main`'s ports are `Lines`");
        assert!(Arc::ptr_eq(&p.unit, unit));
    }
}
