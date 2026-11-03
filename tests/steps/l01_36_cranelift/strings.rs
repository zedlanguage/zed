//! Strings are ropes, the kernel's `Text`: a concatenation of two strings links them in a new
//! cell without copying, the length of a string is kept in each piece, in bytes and in
//! characters, so `len` reads it without counting or copying, and the bytes are copied once,
//! when the text is first read; a string handed to the kernel is shared, not copied
//! (COMPLEXITY.md R4, R5).

use zed_kernel::term::build::{let_, lit, prim, var};
use zed_kernel::{Evaluator, Prim, Term, Value, World};

use super::{kernel, native};

#[test]
fn concatenation_links_ropes_and_copies_once_when_read() {
    // ((("ab" ++ "cd") ++ "ef") ++ "gh"), and its length.
    let mut s = lit("ab");
    for part in ["cd", "ef", "gh"] {
        s = prim(Prim::Concat, vec![s, lit(part)]);
    }
    let o = native(&s).unwrap();
    assert_eq!((o.kernel_calls, o.stats.copied), (0, 0));
    let Value::Str(text) = &o.value else {
        panic!("{}", o.value)
    };
    assert!(!text.is_written_out(), "the run never read the text");
    assert_eq!(o.value, kernel(&s).unwrap());
    assert!(text.is_written_out());
    let n = native(&prim(Prim::Len, vec![s.clone()])).unwrap();
    assert_eq!(n.value.to_string(), "8");
    assert_eq!((n.kernel_calls, n.stats.copied), (0, 0));
}

#[test]
fn a_string_two_uses_borrow_is_neither_counted_nor_copied() {
    let t = let_(
        "s",
        prim(Prim::Concat, vec![lit("na"), lit("ïve")]),
        prim(
            Prim::Tuple,
            vec![
                prim(Prim::Len, vec![var("s")]),
                prim(Prim::Upper, vec![var("s")]),
            ],
        ),
    );
    let o = native(&t).unwrap();
    assert_eq!(o.value, kernel(&t).unwrap());
    assert_eq!(o.value.to_string(), "(5, \"NAÏVE\")");
    // Both uses borrow the string, so its count is never written above 1; Upper runs in the
    // kernel, the one kernel call.
    assert_eq!(
        (o.kernel_calls, o.stats.shared, o.stats.increments),
        (1, 0, 0)
    );
}

#[test]
fn a_string_owned_twice_is_shared_not_copied() {
    let t = let_(
        "s",
        prim(Prim::Concat, vec![lit("ab"), lit("c")]),
        prim(Prim::Tuple, vec![var("s"), var("s")]),
    );
    let o = native(&t).unwrap();
    assert_eq!(o.value.to_string(), "(\"abc\", \"abc\")");
    assert_eq!(
        (o.kernel_calls, o.stats.shared, o.stats.increments),
        (0, 1, 1)
    );
}

/// `s` read from input port `x`, then `(len(s), len(s ++ s), len("" ++ s))`.
fn lengths() -> Term {
    let_(
        "s",
        Term::Read("x".into()),
        prim(
            Prim::Tuple,
            vec![
                prim(Prim::Len, vec![var("s")]),
                prim(
                    Prim::Len,
                    vec![prim(Prim::Concat, vec![var("s"), var("s")])],
                ),
                prim(Prim::Len, vec![prim(Prim::Concat, vec![lit(""), var("s")])]),
            ],
        ),
    )
}

/// `t`'s value natively and in the kernel, with input port `x` holding `x`.
fn both_with(t: &Term, x: &str) -> (Value, Value) {
    let mut w = World::new();
    w.inputs.insert("x".into(), Value::str(x));
    let (g, p) = super::planned(t);
    let o = zed_native::run(&g, &p, &mut Evaluator::new(w.clone())).unwrap();
    assert_eq!(o.kernel_calls, 0, "len and ++ run natively");
    (o.value, Evaluator::new(w).run(t).unwrap())
}

/// A name, a word with accents, a CJK place name, an emoji with a modifier, and nothing: the
/// kernel and the native runtime count the same characters, Unicode scalar values.
#[test]
fn len_counts_characters_the_same_natively_and_in_the_kernel() {
    for (x, n) in [
        ("Ada Lovelace", 12),
        ("crème brûlée", 12),
        ("東京都", 3),
        ("👍🏽 ok", 5),
        ("", 0),
    ] {
        let (native, kernel) = both_with(&lengths(), x);
        assert_eq!(native, kernel, "{x:?}");
        assert_eq!(
            native.to_string(),
            format!("({n}, {}, {n})", 2 * n),
            "{x:?}"
        );
    }
}

/// A log line built from 500 fields, each `++`ed onto the line so far, some with characters
/// of two to four bytes, and its length read after every field: the kernel's count and the
/// native count agree at each step and with the characters of the text written out.
#[test]
fn len_after_many_appends_agrees_natively_and_in_the_kernel() {
    let fields = ["id=7", " naïve", " Σ=3", " 🚚", ""];
    let n = 500;
    let mut body = prim(
        Prim::Tuple,
        (1..=n).map(|i| var(&format!("l{i}"))).collect(),
    );
    body = prim(Prim::Tuple, vec![body, var(&format!("s{n}"))]);
    for i in (1..=n).rev() {
        let s = format!("s{i}");
        let field = lit(fields[i % fields.len()]);
        body = let_(
            &s,
            prim(Prim::Concat, vec![var(&format!("s{}", i - 1)), field]),
            let_(&format!("l{i}"), prim(Prim::Len, vec![var(&s)]), body),
        );
    }
    let t = let_("s0", Term::Read("x".into()), body);
    let (native, kernel) = on_big_stack(|| both_with(&t, "log:"));
    assert_eq!(native, kernel);
    let Value::Tuple(parts) = &native else {
        panic!("{native}")
    };
    let (Value::Tuple(lens), Value::Str(line)) = (&parts[0], &parts[1]) else {
        panic!("{native}")
    };
    let want = Value::Int(line.chars().count() as i64);
    assert_eq!(lens.last(), Some(&want));
    assert_eq!(line.char_count(), line.chars().count());
}

/// A string handed to the kernel by a node the runtime does not run natively, here `show`, is
/// the same text, shared: the run copies no bytes for it.
#[test]
fn a_string_handed_to_the_kernel_is_shared_not_copied() {
    let s = prim(Prim::Concat, vec![lit("ab"), lit("cd")]);
    let t = prim(Prim::Show, vec![prim(Prim::Concat, vec![s, lit("ef")])]);
    let o = native(&t).unwrap();
    assert_eq!((o.kernel_calls, o.stats.copied), (1, 0));
    let Value::Str(text) = &o.value else {
        panic!("{}", o.value)
    };
    assert!(!text.is_written_out());
    assert_eq!(o.value, kernel(&t).unwrap());
}

/// `f`'s value, run on a thread whose stack holds the recursive passes over a term hundreds
/// of `let`s deep: lowering, planning and the drop of a graph.
fn on_big_stack<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(1 << 28)
            .spawn_scoped(s, f)
            .unwrap()
            .join()
            .unwrap()
    })
}
