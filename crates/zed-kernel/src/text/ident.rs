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

/// The least `k` from `from` up whose name `{base}{k}` `free` takes, and that name. A caller
/// that gives several names of one base passes the `k` after the last one it got, so each
/// suffix is tried once: k names then cost O(k + u) lookups for the u taken names of the form
/// `{base}` and a number, not the O(k²) of trying from 1 each time.
pub fn numbered(base: &str, from: usize, free: impl Fn(&str) -> bool) -> (usize, String) {
    (from..)
        .map(|k| (k, format!("{base}{k}")))
        .find(|(_, name)| free(name))
        .expect("finitely many names are taken, so some suffix is free")
}

/// The name the program wrote for the binder whose kernel name is `kernel`: the kernel name
/// itself, or the part before the first `@` where elaboration renamed the binder `x@k`
/// (`Elab::new`). A written name holds no `@` ([`is_name`]), and neither does a temporary
/// `$k`, which is kept as it is; a caller that keys on binders rather than naming them maps
/// `$k` further (zedc-zir `canon::binders::unnumbered`). A message names a binder by it
/// (DESIGN.md sec:diagnostics). Linear in the length of the name.
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
    }

    #[test]
    fn names_skips_numbers_wildcards_and_text_beyond_ascii() {
        let found: Vec<(usize, &str)> = names("f(x') + 12ab - _ * c_2 >= y").collect();
        assert_eq!(found, [(0, "f"), (2, "x'"), (19, "c_2"), (26, "y")]);
        assert_eq!(names("é x").collect::<Vec<_>>(), [(3, "x")]);
    }
}
