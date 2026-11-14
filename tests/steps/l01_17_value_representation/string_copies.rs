//! Item K30-rest (COMPLEXITY.md K30): the string words `upper`, `lower` and `trim`, an atom's
//! name and field names, a string's padded display, and a string literal's text copy a joined
//! string only into memory asked first, or not at all. Each used to write the join out with
//! `Text::flat`, or copy the literal's text, with no ask, so where the free memory was short
//! the process aborted. Each refusal is checked in a child under a limit 2 MiB above what it
//! holds, at 4 MiB and 32 MiB; the same work is exact when its memory is given.

use std::fmt::{self, Write as _};

use zed_kernel::term::build::{lit, prim};
use zed_kernel::{KernelError, Prim, Text, Value, eval};

use super::memory_check::{in_child_at, lower_limit_by};

fn in_child(name: &str) -> bool {
    in_child_at(module_path!(), name)
}

/// The limit above what the child holds once its operands are built.
const SHORT: u64 = 2 << 20;

/// The sizes of the refusals, 4 MiB and 32 MiB: each at least twice [`SHORT`], so a copy
/// not asked for first would abort the child. They were 16 MiB and 128 MiB above a limit of
/// 8 MiB, and the copies of the larger took 7 s in `the_copies_of_a_joined_string_are_exact_when_memory_is_given`.
const SIZES: [usize; 2] = [1 << 22, 1 << 25];

fn text(s: &str) -> Text {
    Text::from(s)
}

/// The join of `parts`, left to right.
pub(crate) fn joined(parts: &[&str]) -> Text {
    parts
        .iter()
        .map(|p| text(p))
        .reduce(|a, b| Text::join(&a, &b).expect("a length that fits"))
        .unwrap_or_else(|| text(""))
}

/// `n` copies of `c`, joined from two halves.
pub(crate) fn halves(c: char, n: usize) -> Text {
    let half = text(&c.to_string().repeat(n / 2));
    Text::join(&half, &half).expect("a length that fits")
}

pub(crate) fn word(p: Prim, s: Text) -> Result<Value, KernelError> {
    eval(&prim(p, vec![lit(Value::Str(s))]))
}

/// `#name(..)` with `args` by position, or by the field names `names` when there are any.
pub(crate) fn atom(name: Text, names: Vec<Text>, args: Vec<Value>) -> Result<Value, KernelError> {
    let names = Value::tuple(names.into_iter().map(Value::Str).collect());
    let mut all = vec![lit(Value::Str(name)), lit(names)];
    all.extend(args.into_iter().map(lit));
    eval(&prim(Prim::Atom, all))
}

/// Strings in several blocks, with characters whose case changes their length (`ß`, `İ`), a
/// `Σ` whose lowercase depends on the block after it, and white space of several kinds at
/// either end and across the joins.
fn cases() -> Vec<Vec<&'static str>> {
    vec![
        vec![],
        vec![""],
        vec!["", ""],
        vec!["abc"],
        vec!["straße", " İstanbul"],
        vec!["ΟΔΟΣ", " ΟΔΟΣ"],
        vec!["ΟΔΟ", "Σ", ""],
        vec!["ΟΔΟΣ", "'", "Α"],
        vec!["  ", " \t", "a b", "  ", "\u{3000}"],
        vec![" ", "\n", "\u{3000}"],
        vec!["x", "  ", "y"],
        vec!["\u{2028}é", "ÀÉÎ", " "],
    ]
}

/// `upper`, `lower` and `trim` of a joined string give what they give for the same string in
/// one block, as `str`'s words write it.
#[test]
fn the_string_words_of_a_joined_string_are_those_of_its_text() {
    for parts in cases() {
        let flat: String = parts.concat();
        let s = joined(&parts);
        let want = [
            (Prim::Upper, flat.to_uppercase()),
            (Prim::Lower, flat.to_lowercase()),
            (Prim::Trim, flat.trim().to_string()),
        ];
        for (p, w) in want {
            assert_eq!(word(p, s.clone()), Ok(Value::str(&w)), "{p:?} of {parts:?}");
            assert_eq!(
                word(p, text(&flat)),
                Ok(Value::str(&w)),
                "{p:?} of {flat:?}"
            );
        }
    }
}

/// An atom named by a joined string, or with a joined field name, is the atom named by the same
/// text in one block.
#[test]
fn an_atom_named_by_a_joined_string_is_named_by_its_text() {
    let one = Value::int(1.into());
    let by_parts = atom(joined(&["io", "Error"]), vec![], vec![one.clone()]);
    assert_eq!(by_parts, Ok(Value::atom_with("ioError", vec![one.clone()])));
    let named = atom(
        joined(&["e", "rr"]),
        vec![joined(&["co", "de"]), text("at")],
        vec![one.clone(), one.clone()],
    );
    let want = Value::atom_named(
        "err",
        vec![("code".into(), one.clone()), ("at".into(), one)],
    );
    assert_eq!(named.ok(), want);
}

/// A joined string written with a width, a precision, a fill and an alignment is written as
/// the same text in one `str` is.
#[test]
fn a_joined_string_is_padded_and_cut_as_its_text_is() {
    for parts in cases() {
        let flat: String = parts.concat();
        let s = joined(&parts);
        let n = flat.chars().count();
        for w in [0, 1, n.saturating_sub(1), n, n + 1, n + 4] {
            assert_eq!(
                format!("{s:w$}"),
                format!("{flat:w$}"),
                "{parts:?} width {w}"
            );
            assert_eq!(format!("{s:>w$}"), format!("{flat:>w$}"), "{parts:?} >{w}");
            assert_eq!(
                format!("{s:*^w$}"),
                format!("{flat:*^w$}"),
                "{parts:?} ^{w}"
            );
            assert_eq!(
                format!("{s:-<w$}"),
                format!("{flat:-<w$}"),
                "{parts:?} <{w}"
            );
            for p in [0, 1, 2, n.saturating_sub(1), n, n + 3] {
                assert_eq!(format!("{s:.p$}"), format!("{flat:.p$}"), "{parts:?} .{p}");
                assert_eq!(
                    format!("{s:_^w$.p$}"),
                    format!("{flat:_^w$.p$}"),
                    "{parts:?} ^{w}.{p}"
                );
            }
        }
    }
}

/// The error of `p` on `s` refused, with the bytes it names.
fn copy_refused(p: Prim, s: Text) -> (&'static str, usize) {
    match word(p, s) {
        Err(KernelError::StringCopyTooLarge { op, bytes }) => (op, bytes),
        Ok(v) => panic!("answered a value of type {}", v.kind_type()),
        Err(e) => panic!("another error: {e:?}"),
    }
}

/// `upper` of `n` joined bytes asks for its `n` bytes and their copy first, and is refused.
#[test]
fn upper_of_a_joined_string_is_refused_when_memory_is_short() {
    if !in_child("upper_of_a_joined_string_is_refused_when_memory_is_short") {
        return;
    }
    let all = SIZES.map(|n| (n, halves('a', n)));
    lower_limit_by(SHORT);
    for (n, s) in all {
        assert_eq!(copy_refused(Prim::Upper, s), ("upper", n), "n = {n}");
    }
}

/// `lower` of `n` joined bytes reads them in one piece, asked first, and is refused.
#[test]
fn lower_of_a_joined_string_is_refused_when_memory_is_short() {
    if !in_child("lower_of_a_joined_string_is_refused_when_memory_is_short") {
        return;
    }
    let all = SIZES.map(|n| (n, halves('A', n)));
    lower_limit_by(SHORT);
    for (n, s) in all {
        assert_eq!(copy_refused(Prim::Lower, s), ("lower", n), "n = {n}");
    }
}

/// `trim` of `n` joined bytes between two spaces asks for the `n` bytes kept first, and is
/// refused.
#[test]
fn trim_of_a_joined_string_is_refused_when_memory_is_short() {
    if !in_child("trim_of_a_joined_string_is_refused_when_memory_is_short") {
        return;
    }
    let all = SIZES.map(|n| {
        let a = "a".repeat(n / 2);
        (n, joined(&[" ", &a, &a, " "]))
    });
    lower_limit_by(SHORT);
    for (n, s) in all {
        assert_eq!(copy_refused(Prim::Trim, s), ("trim", n), "n = {n}");
    }
}

/// The error of an atom refused, with the bytes it names.
fn name_refused(r: Result<Value, KernelError>) -> usize {
    match r {
        Err(KernelError::AtomNameTooLarge { bytes }) => bytes,
        Ok(v) => panic!("answered a value of type {}", v.kind_type()),
        Err(e) => panic!("another error: {e:?}"),
    }
}

/// An atom named by `n` joined bytes, or with a field name of `n` joined bytes, asks for the
/// name in one piece first, and is refused.
#[test]
fn an_atom_named_by_a_joined_string_is_refused_when_memory_is_short() {
    if !in_child("an_atom_named_by_a_joined_string_is_refused_when_memory_is_short") {
        return;
    }
    let all = SIZES.map(|n| (n, halves('a', n)));
    let one = Value::int(1.into());
    lower_limit_by(SHORT);
    for (n, s) in all {
        let by_name = atom(s.clone(), vec![], vec![]);
        assert_eq!(name_refused(by_name), n, "the name, n = {n}");
        let by_field = atom(text("err"), vec![s], vec![one.clone()]);
        assert_eq!(name_refused(by_field), n, "a field name, n = {n}");
    }
}

/// With twice their bytes and more given, `upper`, `trim` and an atom's name are exact; `lower`
/// with four times.
#[test]
fn the_copies_of_a_joined_string_are_exact_when_memory_is_given() {
    if !in_child("the_copies_of_a_joined_string_are_exact_when_memory_is_given") {
        return;
    }
    // The smaller size: at 32 MiB the four copies took 2.4 s.
    let n = SIZES[0];
    let (a, big_a) = (halves('a', n), halves('A', n));
    let a_flat = "a".repeat(n / 2);
    let padded = joined(&[" ", &a_flat, &a_flat, " "]);
    lower_limit_by(4 * n as u64 + SHORT);
    let up = word(Prim::Upper, a.clone()).expect("upper is given its memory");
    let Value::Str(up) = up else {
        panic!("upper is a string")
    };
    assert_eq!(
        (up.len(), up.chunks().all(|c| c.bytes().all(|b| b == b'A'))),
        (n, true)
    );
    drop(up);
    let low = word(Prim::Lower, big_a).expect("lower is given its memory");
    let Value::Str(low) = low else {
        panic!("lower is a string")
    };
    assert_eq!(
        (
            low.len(),
            low.chunks().all(|c| c.bytes().all(|b| b == b'a'))
        ),
        (n, true)
    );
    drop(low);
    let trimmed = word(Prim::Trim, padded).expect("trim is given its memory");
    let Value::Str(trimmed) = trimmed else {
        panic!("trim is a string")
    };
    assert_eq!(trimmed.len(), n);
    drop(trimmed);
    let Ok(Value::Atom(x)) = atom(a, vec![], vec![]) else {
        panic!("the atom is given its memory")
    };
    assert_eq!(x.name.len(), n);
}

/// A writer that counts what it is given and keeps none of it.
#[derive(Default)]
pub(crate) struct Count(pub(crate) usize);

impl fmt::Write for Count {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0 += s.len();
        Ok(())
    }
}

/// A joined string of `n` bytes written with a width or a precision, to a writer that keeps
/// nothing, takes no memory: it is written block by block, where it used to be written out in
/// one piece first. (A width or a precision is at most `u16::MAX`, so a width here is less
/// than the string's length, and a precision cuts it to a few characters.)
#[test]
fn a_joined_string_is_padded_with_no_copy_when_memory_is_short() {
    if !in_child("a_joined_string_is_padded_with_no_copy_when_memory_is_short") {
        return;
    }
    let all = SIZES.map(|n| (n, halves('a', n)));
    lower_limit_by(SHORT);
    for (n, s) in all {
        let mut out = Count::default();
        write!(out, "{s:>20}").expect("the writer takes it");
        assert_eq!(out.0, n, "with a width, n = {n}");
        let mut out = Count::default();
        write!(out, "{s:*^20.10}").expect("the writer takes it");
        assert_eq!(out.0, 20, "cut and padded, n = {n}");
    }
}

/// A string literal's text is shared by the token and the syntax tree, not copied: a literal
/// of `n` bytes lexed before the limit is parsed and built into the syntax tree under it.
#[test]
fn the_syntax_tree_shares_a_string_literals_text() {
    if !in_child("the_syntax_tree_shares_a_string_literals_text") {
        return;
    }
    let all = SIZES.map(|n| {
        let text = format!("x = \"{}\";\n", "a".repeat(n));
        let tokens = zedc::lex::lex_fence(&text).expect("the text lexes");
        (n, text, tokens)
    });
    lower_limit_by(SHORT);
    for (n, text, tokens) in &all {
        let tree = zedc::parse::parse(text, tokens, "Unit", zedc::parse::TOP).expect("it parses");
        let stmts = zedc::ast::unit(text, tokens, &tree).expect("it is a unit");
        assert_eq!(stmts.len(), 1, "n = {n}");
    }
}
