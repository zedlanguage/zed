//! The definitions of the types one message writes (step MSG-type-defs-layout): while
//! [`collect`] is on, a printed type writes no definitions of its own. Each part it would
//! define goes into one table for the thread, merged with an equal one already there, and each
//! use writes a reference to it. A message's texts are finished by [`lift`], which names the
//! definitions they reach `T1`, `T2`, … in one numbering, and gives them back to be written once,
//! outside the sentence ([`under`]); [`plain`] finishes one text alone, each definition
//! declared on a line of its own before it ([`declare`]), as `type T1 = …;` and then `T1`.
//!
//! A reference is `\u{FDD5}k\u{FDD6}`, `k` the definition's place in the table: Unicode
//! noncharacters, which no user text in a message holds. The lexer refuses them outside a
//! string, a string value is written with them escaped (`\u{fdd5}`, the `{:?}` form of
//! `Value::Str`), and the source lines quoted under a message are drawn after [`lift`]; test
//! l01_29 `markers`. A text with no part used twice holds none, and is the text it was before
//! the step.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Write as _};

use super::names::{Names, fresh_name};

/// Opens a reference.
const REF: char = '\u{FDD5}';
/// Closes a reference.
const END: char = '\u{FDD6}';
/// A definition whose place is not known yet, written while the printer places the others.
pub(super) const WAIT: &str = "\u{FDD7}";

/// The definitions printed while [`collect`] is on: each body, in which references stand for
/// the definitions it uses, and the place of each body known in full.
#[derive(Default)]
struct Table {
    bodies: Vec<String>,
    index: HashMap<String, usize>,
}

thread_local! {
    static TABLE: RefCell<Option<Table>> = const { RefCell::new(None) };
}

/// While it lives, printed types put their definitions in the thread's table ([`collect`]).
/// Dropped, the table before it is back.
pub struct Collecting {
    before: Option<Table>,
}

impl Drop for Collecting {
    fn drop(&mut self) {
        TABLE.set(self.before.take());
    }
}

/// Starts a table of definitions on this thread, which lasts while the result lives: a
/// checker turns it on for its messages.
pub fn collect() -> Collecting {
    Collecting {
        before: TABLE.replace(Some(Table::default())),
    }
}

/// Whether printed types put their definitions in the table.
pub(super) fn active() -> bool {
    TABLE.with_borrow(Option::is_some)
}

/// The reference to definition `k`.
pub(super) fn reference(k: usize) -> String {
    format!("{REF}{k}{END}")
}

/// The place of a definition with `body`, which is known in full: that of an equal body if
/// there is one. Equal texts mean the same, since each reference stands for one definition.
pub(super) fn add(body: String) -> usize {
    TABLE.with_borrow_mut(|t| {
        let t = t.as_mut().expect("collecting");
        if let Some(&k) = t.index.get(&body) {
            return k;
        }
        let k = t.bodies.len();
        t.index.insert(body.clone(), k);
        t.bodies.push(body);
        k
    })
}

/// A place for a definition whose body uses one not placed yet, as a cycle does; its body
/// comes with [`fill`], and it is merged with none.
pub(super) fn reserve() -> usize {
    TABLE.with_borrow_mut(|t| {
        let t = t.as_mut().expect("collecting");
        t.bodies.push(String::new());
        t.bodies.len() - 1
    })
}

/// Gives the place `k` from [`reserve`] its body.
pub(super) fn fill(k: usize, body: String) {
    TABLE.with_borrow_mut(|t| t.as_mut().expect("collecting").bodies[k] = body);
}

/// The references in `text`, in order.
fn refs(text: &str) -> impl Iterator<Item = usize> + '_ {
    text.split(REF).skip(1).map(|s| {
        let n = s.find(END).expect("a reference is closed");
        s[..n].parse().expect("a reference is a number")
    })
}

/// `text` with each reference written by its name.
fn rename(text: &str, names: &HashMap<usize, String>) -> String {
    let mut parts = text.split(REF);
    let mut out = String::from(parts.next().unwrap_or(""));
    for s in parts {
        let n = s.find(END).expect("a reference is closed");
        let k: usize = s[..n].parse().expect("a reference is a number");
        out.push_str(&names[&k]);
        out.push_str(&s[n + END.len_utf8()..]);
    }
    out
}

/// Names the definitions `texts` reach, directly or through other definitions, `T1`, `T2`, …
/// and writes each reference by its name. Gives the definitions, name and body, each before
/// its uses but where definitions refer to each other in a cycle. Numbers are given in that
/// order, which is found from the texts alone, so equal texts get equal names. A name is
/// skipped if the program binds it, `taken` says so or a text holds it as a word, so a
/// variable `T5` the message writes leaves `T5` to it ([`fresh_name`]). `texts` with no
/// reference are left as they are, and give no definition.
///
/// Time linear in the texts and the bodies reached, with a hash lookup per reference.
pub fn lift(texts: &mut [&mut String], taken: &dyn Fn(&str) -> bool) -> Vec<(String, String)> {
    if !texts.iter().any(|t| t.contains(REF)) {
        return Vec::new();
    }
    let bodies: Vec<(usize, String)> = TABLE.with_borrow(|t| {
        let t = t.as_ref().expect("references are lifted while collecting");
        // Depth-first from the references in reading order; a definition is listed when
        // left, after the definitions its body uses, and each is entered once.
        let mut order = Vec::new();
        let mut seen: HashSet<usize> = HashSet::new();
        for text in texts.iter() {
            for k in refs(text) {
                if !seen.insert(k) {
                    continue;
                }
                let mut stack: Vec<(usize, std::vec::IntoIter<usize>)> =
                    vec![(k, refs(&t.bodies[k]).collect::<Vec<_>>().into_iter())];
                while let Some((at, next)) = stack.last_mut() {
                    let at = *at;
                    match next.find(|j| !seen.contains(j)) {
                        Some(j) => {
                            seen.insert(j);
                            stack.push((j, refs(&t.bodies[j]).collect::<Vec<_>>().into_iter()));
                        }
                        None => {
                            order.push((at, t.bodies[at].clone()));
                            stack.pop();
                        }
                    }
                }
            }
        }
        order
    });
    let words: HashSet<&str> = texts
        .iter()
        .flat_map(|t| t.split(|c: char| !(c.is_alphanumeric() || c == '_')))
        .filter(|w| w.starts_with('T'))
        .collect();
    let mut names: HashMap<usize, String> = HashMap::with_capacity(bodies.len());
    let mut n = 0;
    for (k, _) in &bodies {
        let name: String = fresh_name(Names::Definitions, &mut n, |w| {
            words.contains(w) || taken(w)
        });
        names.insert(*k, name);
    }
    for text in texts.iter_mut() {
        if text.contains(REF) {
            **text = rename(text, &names);
        }
    }
    bodies
        .iter()
        .map(|(k, body)| (names[k].clone(), rename(body, &names)))
        .collect()
}

/// Writes the definition of `name` as a user declares it at the top level, `type T1 = …;`, and
/// ends the line: a type printed alone has its definitions on lines of their own before it
/// (DESIGN sec:diagnostics, "Types in a message").
pub fn declare(out: &mut impl fmt::Write, name: &str, body: &str) -> fmt::Result {
    writeln!(out, "{}", Declaration(name, body))
}

/// The definition of a name, given with its body, as a user declares it at the top level:
/// `type T1 = …;`.
pub struct Declaration<'a>(pub &'a str, pub &'a str);

impl fmt::Display for Declaration<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "type {} = {};", self.0, self.1)
    }
}

/// `text` alone, finished: each of its definitions declared on a line of its own
/// ([`declare`]), then the text, as a type printed outside a message is.
pub fn plain(text: &str) -> String {
    if !text.contains(REF) {
        return text.into();
    }
    let mut root = text.to_string();
    let mut out = String::new();
    for (name, body) in lift(&mut [&mut root], &|_| false) {
        declare(&mut out, &name, &body).expect("a String takes any text");
    }
    out.push_str(&root);
    out
}

/// Writes `defs`, given by [`lift`], after `message`: a line that says what the names stand
/// for, then each definition on a line of its own, as a user declares it. Nothing when `defs`
/// is empty.
pub fn under(message: &mut String, defs: &[(String, String)]) {
    let Some(((last, _), rest)) = defs.split_last() else {
        return;
    };
    let names: Vec<&str> = rest.iter().map(|(n, _)| n.as_str()).collect();
    match names.is_empty() {
        true => write!(
            message,
            "\n  {last} stands for a part written more than once:"
        ),
        false => write!(
            message,
            "\n  {} and {last} stand for parts written more than once:",
            names.join(", ")
        ),
    }
    .expect("a String takes any text");
    for (name, body) in defs {
        write!(message, "\n    {}", Declaration(name, body)).expect("a String takes any text");
    }
}

/// Finishes a message made with [`collect`] on outside a checker: [`lift`] names the
/// definitions it reaches, and [`under`] writes them after it.
pub fn finish(message: &mut String) {
    let defs = lift(&mut [message], &|_| false);
    under(message, &defs);
}

/// Turns [`collect`] on for a printer that writes a message of its own, unless it is on
/// already: then the definitions go to the table of the message around it, which lays them
/// out.
pub fn local() -> Option<Collecting> {
    (!active()).then(collect)
}

/// Whether `text` holds a reference to a definition.
pub fn holds(text: &str) -> bool {
    text.contains(REF)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn definitions_come_before_their_uses_and_a_cycle_keeps_its_own() {
        let _on = collect();
        let inner = add("#a | #b".into());
        let outer = add(format!("({0}, {0})", reference(inner)));
        // `T = #x(U) | #y; U = (T, T)`, a cycle, placed before its bodies are known.
        let (t, u) = (reserve(), reserve());
        fill(t, format!("#x({}) | #y", reference(u)));
        fill(u, format!("({0}, {0})", reference(t)));
        let mut text = format!("{} | {}", reference(outer), reference(t));
        let defs = lift(&mut [&mut text], &|_| false);
        assert_eq!(text, "T2 | T4");
        assert_eq!(
            defs,
            [
                ("T1".to_string(), "#a | #b".to_string()),
                ("T2".to_string(), "(T1, T1)".to_string()),
                ("T3".to_string(), "(T4, T4)".to_string()),
                ("T4".to_string(), "#x(T3) | #y".to_string())
            ]
        );
        // An equal body is merged with the one there; a reserved one never is.
        assert_eq!(add("#a | #b".into()), inner);
    }

    #[test]
    fn collecting_ends_with_its_guard() {
        {
            let _on = collect();
            assert!(active());
        }
        assert!(!active());
    }
}
