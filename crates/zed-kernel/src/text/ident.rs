//! Names as the grammar reads them (`zed/grammar/lexical.peg`, rules `NameChar` and `Name`;
//! NAME-ascii-only, 2026-11-12), for every crate that finds names in text: the lexer, and the
//! messages and repairs that read a name out of a program's text. A name is ASCII: a letter,
//! or `_` before a name character, then name characters `[A-Za-z0-9_]`, then at most one `'`
//! (`x'`, author decision of 2026-11-12). So `_x`, `x_1`, `__` and `x'` are names, and a bare
//! `_` is the wildcard, not a name.

/// Whether `c` may start a name: the grammar's `[A-Za-z]`. A `_` starts one only before a
/// name character ([`name_end`]).
pub fn is_name_start(c: char) -> bool {
    c.is_ascii_alphabetic()
}

/// Whether `c` may continue a name: the grammar's `NameChar`, `[A-Za-z0-9_]`.
pub fn is_name_continue(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// Whether the byte `c` continues a name. A byte of a character beyond ASCII never does.
fn continues(c: u8) -> bool {
    is_name_continue(char::from(c))
}

/// The end of the name starting at byte `pos` of `text`, if one starts there: its run of name
/// characters and the one `'` after it. A `'` after the first is not part of the name, so
/// `x''` is the name `x'` and a `'`. `pos` need not be on a character boundary, since no byte
/// of a character beyond ASCII starts or continues a name. O(the name's length).
pub fn name_end(text: &str, pos: usize) -> Option<usize> {
    let b = &text.as_bytes()[pos..];
    let first = char::from(*b.first()?);
    let starts = is_name_start(first) || (first == '_' && b.get(1).is_some_and(|&c| continues(c)));
    if !starts {
        return None;
    }
    let run = b.iter().position(|&c| !continues(c)).unwrap_or(b.len());
    Some(pos + run + usize::from(b.get(run) == Some(&b'\'')))
}

/// Whether `text` is one name and nothing else. O(its length).
pub fn is_name(text: &str) -> bool {
    name_end(text, 0) == Some(text.len())
}

/// The names in `text`, in order, each with its byte offset: every maximal run of name
/// characters that [`name_end`] reads as a name, so a number (`12`, `0x1f`), the wildcard `_`
/// and the tail of a run that starts with a digit (`ab` in `12ab`) are not names. Text inside a
/// string literal is read as any other. O(the length of `text`).
pub fn names(text: &str) -> impl Iterator<Item = (usize, &str)> {
    let b = text.as_bytes();
    let mut i = 0;
    std::iter::from_fn(move || {
        while i < b.len() {
            if !continues(b[i]) {
                i += 1;
                continue;
            }
            let start = i;
            match name_end(text, i) {
                Some(end) => {
                    i = end;
                    return Some((start, &text[start..end]));
                }
                None => {
                    while i < b.len() && continues(b[i]) {
                        i += 1;
                    }
                }
            }
        }
        None
    })
}

/// A new name beside the names a program writes: `base` itself when `free` takes it, else
/// [`numbered`] from 2, so `x` taken gives `x2`, the second `x`, then `x3`. DESIGN.md
/// sec:diagnostics names a second binding so: `y2 = y * 2;` (the rebinding row) and
/// `x2 = x - 1;` for `popCount(x - 1)` (the repair of a value outside the ints its use
/// takes). Names that are always numbered, such as the two functions a split makes (`ok1` and
/// `ok2`, DESIGN.md sec:units), call [`numbered`] from 1 instead.
pub fn fresh(base: &str, free: impl Fn(&str) -> bool) -> String {
    if free(base) {
        return base.to_string();
    }
    numbered(base, 2, free).1
}

/// The type names of the prelude at L1; a unit declares no type before L2. A binder may not
/// have one of these names: the resolver refuses it (`zedc_resolve::resolve::TYPES`, which is
/// this list), so a printer choosing a new name for a binder skips them.
pub const PRELUDE_TYPES: &[&str] = &[
    "int",
    "rat",
    "f64",
    "f32",
    "bool",
    "String",
    "Lines",
    "Files",
    "CommandLine",
    "Never",
];

/// The least `k` from `from` up whose name `{base}{k}` `free` takes, and that name. A caller
/// that gives several names of one base passes the `k` after the last one it got, so each
/// suffix is tried once: k names then cost O(k + u) lookups for the u taken names of the form
/// `base` without its final primes, a number, then those primes, not the O(k²) of trying from 1
/// each time.
///
/// A `'` may only end a name, so where `base` ends with primes the number goes before them:
/// `x'` gives `x2'`, not `x'2`, which is no name (Gemini C-2 of round 3 of
/// XR-lazy-and-kernel-batch-1). The names stay distinct for distinct `k`, and none is `base`.
pub fn numbered(base: &str, from: usize, free: impl Fn(&str) -> bool) -> (usize, String) {
    let stem = base.trim_end_matches('\'');
    let primes = &base[stem.len()..];
    (from..)
        .map(|k| (k, format!("{stem}{k}{primes}")))
        .find(|(_, name)| free(name))
        .expect("finitely many names are taken, so some suffix is free")
}

/// The name the program wrote for the binder whose kernel name is `kernel`: the kernel name
/// itself, or the part before the first `@` where elaboration renamed the binder `x@k`
/// (`Elab::new`). A written name holds no `@` ([`is_name`]), and neither does a temporary
/// `$k`, which is kept as it is; a caller that keys on binders rather than naming them maps
/// `$k` further (zedc-zir `canon::binders::unnumbered`). A message names a binder by it
/// (DESIGN.md sec:diagnostics). Linear in the length of the name.
///
/// No kernel name is `$k@j`, a temporary with a binder number after it, which this would cut
/// to `$k` (TEST-written-name-k-at-j). Proof, by the sites that make the two characters (every
/// `format!`, `push` and `write!` of the crates that make names, read on 2026-11-19):
/// - An `@` is put after a name only by elaboration's renaming, `{x}@{k}` (zedc-elab:
///   `Elab::new` in elab/state.rs, the instancing in elab/identities.rs, the binders of a
///   copied body in elab/walk.rs), and `x` there is always a resolver binder's name, which is
///   a lexed name ([`is_name`]: letters, digits, `_` and a final `'`) or one the syntax tree
///   builder or the resolver makes, `<left>` and `<right>` of a section and `this`: none
///   holds a `$`. The checker's `{x}@{id}` and `{x}@p{i}` (zedc-check arms.rs `var`,
///   walk.rs) name its own type facts and never reach a kernel term.
/// - A `$` begins a name only at `Elab::temp`, `${n}` with `n` counted from 1, and at
///   zedc-stage's `CUT_READ`, `$0`; neither name is renamed after it is made, since the
///   renamings above rename resolver binders only, and the later passes name their binders
///   `\0…` (zedc-zir) or add `#…` (zedc-preimage), never `@`. The ZIR readers, text and
///   binary, take a `$` binder only as `$` and digits (zedc-zir zir/text.rs `not_a_binder`).
///
/// A third form holds both characters: the thunk of a default argument, `{f}${p}`, with `f`
/// and `p` the kernel names of the function and its parameter (zedc-elab elab/walk.rs,
/// `Frame::FnDefault`), as `h3$x@4`. It is a definition, not a binder a message names; this
/// gives `h3$x` for it, and `f` for `f@2$x@4`. The test
/// `no_temporary_carries_a_binder_number` (tests/steps/l01_16_elaboration/complete.rs)
/// elaborates programs that make temporaries inside renamed scopes and thunks, and finds no
/// `$k@j`.
pub fn written_name(kernel: &str) -> &str {
    kernel
        .split_once('@')
        .map_or(kernel, |(written, _)| written)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_fresh_name_is_the_base_or_the_second_one() {
        let taken = ["x", "w", "w2", "y2"];
        let free = |n: &str| !taken.contains(&n);
        assert_eq!(fresh("z", free), "z");
        assert_eq!(fresh("x", free), "x2");
        assert_eq!(fresh("w", free), "w3");
        assert_eq!(fresh("y", free), "y");
        assert_eq!(numbered("y", 1, free), (1, "y1".to_string()));
        assert_eq!(numbered("y", 2, free), (3, "y3".to_string()));
    }

    /// A `'` may only end a name ([`name_end`]), so the number goes before it: `x'` gives
    /// `x2'`, never `x'2`, which is the name `x'` and a number (round 3 of
    /// XR-lazy-and-kernel-batch-1, Gemini C-2).
    #[test]
    fn a_numbered_name_puts_the_number_before_a_final_prime() {
        let taken = ["x'", "x2'", "y'"];
        let free = |n: &str| !taken.contains(&n);
        assert_eq!(fresh("z'", free), "z'");
        assert_eq!(fresh("x'", free), "x3'");
        assert_eq!(fresh("y'", free), "y2'");
        assert_eq!(numbered("x'", 1, free), (1, "x1'".to_string()));
        assert_eq!(numbered("x'", 2, free), (3, "x3'".to_string()));
        for (base, from) in [("x'", 2), ("y'", 1), ("_a'", 0), ("x", 2)] {
            let (_, name) = numbered(base, from, free);
            assert!(is_name(&name), "{name}");
        }
    }

    #[test]
    fn a_name_takes_one_prime_and_the_wildcard_is_no_name() {
        assert_eq!(name_end("x' + 1", 0), Some(2));
        assert_eq!(name_end("x''", 0), Some(2));
        assert_eq!(name_end("_", 0), None);
        assert_eq!(name_end("_'", 0), None);
        assert_eq!(name_end("__", 0), Some(2));
        assert_eq!(name_end("1x", 0), None);
        assert_eq!(name_end("é", 0), None);
        assert!(is_name("x_1'") && !is_name("_") && !is_name("x y") && !is_name(""));
    }

    #[test]
    fn a_written_name_drops_the_number_elaboration_gave() {
        assert_eq!(written_name("x"), "x");
        assert_eq!(written_name("x@3"), "x");
        assert_eq!(written_name("x'@12"), "x'");
        assert_eq!(written_name("x@1@2"), "x");
        assert_eq!(written_name("$4"), "$4");
        // The thunk of a default argument (see `written_name`'s comment).
        assert_eq!(written_name("h3$x@4"), "h3$x");
        assert_eq!(written_name("f@2$x@4"), "f");
    }

    #[test]
    fn names_skips_numbers_wildcards_and_text_beyond_ascii() {
        let found: Vec<(usize, &str)> = names("f(x') + 12ab - _ * c_2 >= y").collect();
        assert_eq!(found, [(0, "f"), (2, "x'"), (19, "c_2"), (26, "y")]);
        assert_eq!(names("é x").collect::<Vec<_>>(), [(3, "x")]);
    }

    /// The names of `text` by the grammar read directly (TEST-dry-shared-units): every maximal
    /// run of `[A-Za-z0-9_]` is a name when it starts with a letter, or with `_` and is longer
    /// than one character, and then takes one `'` after it. With `prime` false it never takes
    /// the `'`, the negative control's mistake.
    fn naive_names(text: &str, prime: bool) -> Vec<(usize, String)> {
        let b = text.as_bytes();
        let word = |c: u8| c.is_ascii_alphanumeric() || c == b'_';
        let (mut out, mut i) = (Vec::new(), 0);
        while i < b.len() {
            if !word(b[i]) {
                i += 1;
                continue;
            }
            let start = i;
            while i < b.len() && word(b[i]) {
                i += 1;
            }
            let run = &text[start..i];
            if b[start].is_ascii_alphabetic() || (b[start] == b'_' && run.len() > 1) {
                let mut end = i;
                if prime && b.get(i) == Some(&b'\'') {
                    end += 1;
                }
                out.push((start, text[start..end].to_string()));
            }
        }
        out
    }

    /// Random texts over letters, digits, `_`, `'`, a character beyond ASCII and punctuation,
    /// each with a printed seed (`ZED_TEST_SEED` repeats a run).
    fn random_texts(name: &str) -> Vec<String> {
        let (mut rng, _) = crate::seed::Rng::fresh(name);
        let alphabet = ['a', 'Z', '_', '0', '9', '\'', 'é', ' ', '(', '+'];
        (0..4000)
            .map(|_| {
                let len = rng.below(12);
                (0..len).map(|_| rng.pick(&alphabet)).collect()
            })
            .collect()
    }

    fn found(text: &str) -> Vec<(usize, String)> {
        names(text).map(|(i, n)| (i, n.to_string())).collect()
    }

    #[test]
    fn names_agree_with_the_grammar_read_directly() {
        for text in random_texts("names_agree_with_the_grammar_read_directly") {
            assert_eq!(
                found(&text),
                naive_names(&text, true),
                "the names of {text:?}"
            );
            // Each name found is a name alone, ends where `name_end` puts it, and every name
            // `is_name` takes is found whole.
            for (i, n) in found(&text) {
                assert!(is_name(&n), "{n:?} in {text:?}");
                assert_eq!(name_end(&text, i), Some(i + n.len()));
            }
            assert_eq!(
                is_name(&text),
                found(&text) == [(0, text.clone())],
                "{text:?}"
            );
        }
    }

    /// Negative control: a reading of names that drops the `'` differs from `names` on some
    /// random text, so the property test above can fail.
    #[test]
    fn names_without_the_prime_are_caught() {
        let texts = random_texts("names_without_the_prime_are_caught");
        assert!(texts.iter().any(|t| found(t) != naive_names(t, false)));
    }

    #[test]
    fn a_name_ends_at_the_end_of_the_text_and_never_starts_inside_a_character() {
        assert_eq!(name_end("ab", 2), None);
        assert_eq!(name_end("", 0), None);
        assert_eq!(name_end("x", 0), Some(1));
        assert_eq!(name_end("x'", 0), Some(2));
        assert_eq!(name_end("_1", 0), Some(2));
        // `é` is two bytes; its second byte starts nothing, and a name may start after it.
        assert_eq!(name_end("éx", 1), None);
        assert_eq!(name_end("éx", 2), Some(3));
        assert_eq!(name_end("xé", 0), Some(1));
        assert!(!is_name_start('_') && !is_name_start('1') && !is_name_start('é'));
        assert!(is_name_continue('_') && is_name_continue('9') && !is_name_continue('\''));
        assert!(!is_name_continue('é'));
    }

    /// A position past the end breaks `name_end`'s precondition and the slice refuses it.
    #[test]
    #[should_panic(expected = "out of range")]
    fn a_position_past_the_text_is_refused() {
        name_end("ab", 3);
    }

    #[test]
    fn numbered_names_skip_every_taken_suffix() {
        let taken: std::collections::HashSet<String> = (1..=50)
            .map(|k| format!("t{k}"))
            .chain(["t".to_string()])
            .collect();
        let free = |n: &str| !taken.contains(n);
        assert_eq!(fresh("t", free), "t51");
        assert_eq!(numbered("t", 51, free), (51, "t51".to_string()));
        assert_eq!(numbered("t", 60, free), (60, "t60".to_string()));
        assert_eq!(numbered("u", 0, free), (0, "u0".to_string()));
    }
}
