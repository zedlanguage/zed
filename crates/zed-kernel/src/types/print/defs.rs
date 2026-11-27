//! The definitions of the types one message writes (step MSG-type-defs-layout): while
//! [`collect`] is on, a printed type writes no definitions of its own. Each part it would
//! define goes into one table for the thread, merged with an equal one already there, and each
//! use writes a reference to it. A message's texts are finished by [`lift`], which names the
//! definitions they reach `Part1`, `Part2`, … in one numbering, and gives them back to be written
//! once, outside the sentence ([`under`]); [`plain`] finishes one text alone, each definition
//! declared on a line of its own before it ([`declare`]), as `type Part1 = …;` and then `Part1`.
//!
//! A reference is `\u{FDD5}k\u{FDD6}`, `k` the definition's place in the table: Unicode
//! noncharacters, which no user text in a message holds. The lexer refuses them outside a
//! string, a string value is written with them escaped (`\u{FDD5}`, as
//! [`crate::text::Text::literal`] writes it), and the source lines quoted under a message are
//! drawn after [`lift`]; test l01_29 `markers`. A text with no part used twice holds none, and is
//! the text it was before the step.
//!
//! A tuple that one type writes once may be written again by another type of the message, or
//! inside another tuple there: a chain `a1 = (a0, 1); a2 = (a1, 2); …` whose steps each print
//! the next. Each such tuple goes into the table too, as a part that may be named
//! (`\u{FDD4}k\u{FDD6}`, `add_soft`), and [`lift`] names it only when one of its uses is
//! inside another part. A tuple holding a part of its own is named when the message writes it
//! twice or more, once inside another part. A tuple holding none is named when its uses inside
//! other parts make naming shorter: written there n times, its declaration `type Tk = …;` and
//! n + 1 names `Tk` are shorter than n copies. It writes every other one in full where it
//! stands (MSG-derive-type-size). So a chain `t1 = (t0, t0); t2 = (t1, t1); …` whose steps
//! print `t6` names each level once, and so does `a1 = (a0, 1); a2 = (a1, 2); …`, while
//! `(1, 2)` written twice is written in full both times. A tuple holding no part, left in full
//! inside n ≥ 2 parts, is at most `(9 + (n + 1) × |Tk|) / (n - 1)` long, a declaration and three
//! names, so the parts grow with the program, not with the paths of the types. A whole type
//! written by several steps and inside no other part is written in full in each, as
//! `` `x` is (int, rat, bool) here `` and `` `x` is declared `(int, rat, bool)` ``: naming it
//! would put a definition into short messages for a type written three or four times. A step
//! whose printed type an earlier step wrote writes `the same type as step k` instead, unless
//! the type is no longer than those words or stands in code ([`same_type_as_step`]), so a
//! chain of n names that each hold the one before with one type of m components,
//! `x1 = x0; x2 = x1; …`, writes the type once (MSG-derive-same-chain).
//!
//! [`lift`] also names the type variables a message's types write by name (UNDERSCORE-print),
//! which a printed type marks with the noncharacters U+FDD9 to U+FDDE ([`VARS`]), so that no name
//! it takes is a word the message writes elsewhere ([`name_vars`]).

use std::any::{Any, TypeId};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Write as _};

use super::names::{Names, fresh_name};
use super::uses::{Seen, Use, Uses};
use crate::text::prose::and_list;

/// Opens a reference.
const REF: char = '\u{FDD5}';
/// Opens a reference to a part that is named only if [`lift`] finds it inside another part
/// ([`add_soft`]).
const SOFT: char = '\u{FDD4}';
/// Opens a reference to a part named from the first step of a message that uses it twice or
/// more, and written in full before ([`add_counted`]).
const COUNT: char = '\u{FDD3}';
/// As [`COUNT`], where the part written in full is parenthesized, as `(1 | 2)[]`.
const WRAP: char = '\u{FDD2}';
/// As [`SOFT`], where the tuple written in full is parenthesized, as the key of
/// `((A, B)) -> V`; written by a name it has no parentheses, `Part1 -> V` (author rule P191).
const SOFT_WRAP: char = '\u{FDDF}';
/// Every mark that opens a reference.
const MARKS: [char; 5] = [REF, SOFT, COUNT, WRAP, SOFT_WRAP];
/// Closes a reference.
const END: char = '\u{FDD6}';
/// Opens the text of one print of types that holds a reference ([`enclose`]), the unit whose
/// uses decide from which step a part is named ([`first_named`]).
const TYPE: char = '\u{FDD0}';
/// Closes what [`TYPE`] opens.
const TYPE_END: char = '\u{FDD1}';
/// Every mark [`spell`] reads, but [`SAME`].
const SPELLED: [char; 7] = [REF, SOFT, COUNT, WRAP, SOFT_WRAP, TYPE, TYPE_END];
/// Opens and closes the number of the step that first wrote the printed type that follows
/// ([`same_type_as_step`]); always followed by a [`TYPE`], so a text that holds it holds one
/// of [`SPELLED`]. Outside U+FDD0..=U+FDDF and [`LOCALS`], and gone once [`lift`] spells the
/// text.
const SAME: char = '\u{FDE7}';
/// A definition whose place is not known yet, written while the printer places the others.
pub(super) const WAIT: &str = "\u{FDD7}";

/// Opens one printed type whose unbounded variables are still to be named (DESIGN
/// sec:diagnostics, "Types in a message"): the names restart in each, so two types printed
/// apart name their variables apart, and equal types are equal texts. Unicode noncharacters,
/// as the references are.
pub const VARS: char = '\u{FDD9}';
/// Closes what [`VARS`] opens.
pub const VARS_END: char = '\u{FDDA}';
/// Opens the members of a union written by name in such a type, separated by [`NEXT`]: each
/// a name, or [`VAR`] and the number of a variable within its type.
pub const UNION: char = '\u{FDDB}';
/// Closes what [`UNION`] opens.
pub const UNION_END: char = '\u{FDDC}';
/// Starts a variable of a union of [`UNION`].
pub const VAR: char = '\u{FDDD}';
/// Separates the members of a union of [`UNION`].
pub const NEXT: char = '\u{FDDE}';
/// Separates, in a mark of [`VAR`], the variable's key from the name a declaration wrote for
/// it: `b3:T` is a variable printed `T` unless another variable of its type took `T` first
/// ([`name_vars`]). No key holds it: a key is a number, or `b` and a number (zedc-types
/// `Scope::mark`).
pub const WRITTEN: char = ':';
/// Opens a mention ([`mention`]): a variable of a type closed before it in the text, written
/// by the name [`name_vars`] gives it there. Noncharacters, as the marks above are: U+FDD0 to
/// U+FDDF are the marks of this module and zedc-check's `DECLARE`, U+FDE0 and U+FDE1 are
/// zedc-check's placeholders (`HIDDEN`), U+FDE2 to U+FDE6 are [`LOCALS`] and U+FDE7 is
/// [`SAME`], so these are the two after them; zedc-check swaps every noncharacter of U+FDD0 to
/// U+FDEF out of the program's texts while a message is laid out (`ProgramTexts`).
pub const MENTION: char = '\u{FDE8}';
/// Closes what [`MENTION`] opens.
pub const MENTION_END: char = '\u{FDE9}';

/// The text of a mention of the variable `key`, written after the type that holds it: `back`
/// is how many types ([`VARS`]) the text closes between the end of that type and the mention,
/// `key` the variable's key as its mark writes it after [`VAR`] (`b3`, `b3:T`, or a number),
/// and `fallback` the name written when that type names no variable of `key` (one printed `_`,
/// or none written). [`name_vars`] writes the name the type gave the variable, so a clause of
/// a message that names a variable of a type it quotes names it as the type prints it
/// (PRINT-headline-note-same-name). Form: `MENTION back NEXT key NEXT fallback MENTION_END`;
/// no key or name holds [`NEXT`].
pub fn mention(back: usize, key: &str, fallback: &str) -> String {
    format!("{MENTION}{back}{NEXT}{key}{NEXT}{fallback}{MENTION_END}")
}

/// The names declarations wrote for the variables marked in `text` up to the next [`VARS`] or
/// [`VARS_END`], the marks after [`WRITTEN`], put in `into`: the names the other variables of
/// that type skip ([`name_vars`]). Linear in the part read.
fn written_in<'t>(text: &'t str, into: &mut HashSet<&'t str>) {
    let end = text.find([VARS, VARS_END]).unwrap_or(text.len());
    for mark in text[..end].split(VAR).skip(1) {
        let key = mark.split([NEXT, UNION_END]).next().unwrap_or_default();
        if let Some((_, w)) = key.split_once(WRITTEN) {
            into.insert(w);
        }
    }
}

/// Opens a tuple a printed type holds in two places or more and writes in full at its first
/// place only (zedc-types `Shared::local`, row PRINT-shared-part-exponential): the tuple's
/// number within its printed type, [`END`], its text, then [`LOCAL_CLOSE`]. Once the type's
/// variables are named, [`lift_holding`] takes that text as the body of a soft part
/// ([`Kind::Local`]) and writes the part's reference in its place ([`take_locals`]). The marks
/// U+FDD0..=U+FDDF are all taken, and U+FDE0 and U+FDE1 are zedc-check's placeholders of the
/// program's own text, so these are the noncharacters after them.
const LOCAL_OPEN: char = '\u{FDE2}';
/// As [`LOCAL_OPEN`], where the tuple stands parenthesized, as [`SOFT_WRAP`] says.
const LOCAL_OPEN_WRAP: char = '\u{FDE3}';
/// Closes what [`LOCAL_OPEN`] opens.
const LOCAL_CLOSE: char = '\u{FDE4}';
/// Writes again a tuple [`LOCAL_OPEN`] opened earlier in the same printed type: its number,
/// then [`END`].
const LOCAL_REF: char = '\u{FDE5}';
/// As [`LOCAL_REF`], where the tuple stands parenthesized.
const LOCAL_REF_WRAP: char = '\u{FDE6}';
/// Every mark of a tuple written once in its printed type.
pub const LOCALS: [char; 5] = [
    LOCAL_OPEN,
    LOCAL_OPEN_WRAP,
    LOCAL_CLOSE,
    LOCAL_REF,
    LOCAL_REF_WRAP,
];

/// Opens in `out` the text of tuple `id` of a printed type (`LOCAL_OPEN`), parenthesized
/// where it stands if `wrap`.
pub fn local_open(out: &mut String, id: usize, wrap: bool) {
    out.push(if wrap { LOCAL_OPEN_WRAP } else { LOCAL_OPEN });
    write!(out, "{id}{END}").expect("a String takes any text");
}

/// Closes in `out` the text [`local_open`] opened last.
pub fn local_close(out: &mut String) {
    out.push(LOCAL_CLOSE);
}

/// Writes in `out` tuple `id` of a printed type again (`LOCAL_REF`), parenthesized where
/// it stands if `wrap`.
pub fn local_ref(out: &mut String, id: usize, wrap: bool) {
    out.push(if wrap { LOCAL_REF_WRAP } else { LOCAL_REF });
    write!(out, "{id}{END}").expect("a String takes any text");
}

/// `text` with each tuple [`local_open`] wrote taken out as the body of a soft part
/// ([`Kind::Local`]) and written by its reference, there and at each [`local_ref`] to it, so
/// that [`lift_holding`] names it or writes it in full by the rule of a soft part, and also
/// names it when it holds a part and is written twice anywhere. The
/// variables in the bodies are named already ([`name_all_vars`]), so a body is the text its
/// printed type writes there. A number is that of a tuple within one printed type, and a
/// later printed type in the same text may use it again, so a reference is to the tuple
/// opened last under its number, which in a printed type is opened before any reference to
/// it.
///
/// Complexity: one pass over `text` with a stack of the bodies open, each character copied
/// once, and one hash of each body by [`place`]; a body holds the tuples inside it by
/// reference, so the bodies are together no longer than `text`.
fn take_locals(text: &mut String) {
    if !text.contains(LOCALS) {
        return;
    }
    let reference = |k: usize, wrap: bool| match wrap {
        true => wrapped(&soft_reference(k)),
        false => soft_reference(k),
    };
    let mut placed: HashMap<usize, usize> = HashMap::new();
    // The bodies open, innermost last, each with its tuple's number and whether it is
    // parenthesized where it stands.
    let mut open: Vec<(String, usize, bool)> = Vec::new();
    let mut out = String::with_capacity(text.len());
    let mut rest = text.as_str();
    while let Some(i) = rest.find(LOCALS) {
        let into = open.last_mut().map_or(&mut out, |(b, ..)| b);
        into.push_str(&rest[..i]);
        let mark = rest[i..].chars().next().expect("a mark was found");
        let after = &rest[i + mark.len_utf8()..];
        if mark == LOCAL_CLOSE {
            let (body, id, wrap) = open.pop().expect("a tuple closed is open");
            let k = place(body, Kind::Local);
            placed.insert(id, k);
            let into = open.last_mut().map_or(&mut out, |(b, ..)| b);
            into.push_str(&reference(k, wrap));
            rest = after;
            continue;
        }
        let n = after.find(END).expect("a tuple's number is closed");
        let id: usize = after[..n].parse().expect("a tuple's number is a number");
        rest = &after[n + END.len_utf8()..];
        match mark {
            LOCAL_OPEN | LOCAL_OPEN_WRAP => open.push((String::new(), id, mark == LOCAL_OPEN_WRAP)),
            _ => {
                let k = placed[&id];
                let into = open.last_mut().map_or(&mut out, |(b, ..)| b);
                into.push_str(&reference(k, mark == LOCAL_REF_WRAP));
            }
        }
    }
    debug_assert!(open.is_empty(), "each tuple opened is closed");
    out.push_str(rest);
    *text = out;
}

/// Names the variables marked in `out` from `from` on ([`VARS`]): in each marked type, each the
/// next of `T`, `U`, `V`, `W`, `T5`, … that the program does not bind and `taken` does not hold
/// ([`fresh_name`]), in the order the variables are first met reading the type, and writes each
/// union's members by name ([`super::order::name_cmp`]). A variable a declaration wrote a name
/// for ([`WRITTEN`]) keeps that name, unless a variable met before it in its type kept it,
/// and no other variable of the type is given it (DESIGN.md sec:diagnostics, "Types in a
/// message": "A type variable that a declaration writes prints by the name it wrote, bounded or
/// not"). Bounded and unbounded variables are named alike, so the names follow their first
/// places whatever bounds them (plan row UNDERSCORE-print-followups). A printer names its text at
/// once outside a message; inside one, [`lift`] names them, and `taken` is every word of the
/// message.
///
/// Why two variables of one type never get one name, step by step. (1) A fresh name is never a
/// name given before in the type: `n` only grows, so [`fresh_name`] gives each name once, and it
/// skips the written names of the type (`written`) and the names given so far (`used`). (2) A
/// written name is given only when no variable before took it (`used`). (3) The key of a mark
/// is one variable's, and `named` gives every place of the key the name it got first.
///
/// A mention ([`mention`]) is written as the name its type gave the variable: each type's
/// `named` is kept when the type closes, and the mention reads the one `back` types before it.
/// So the mention and the type agree whatever the type was given, a written name or a fresh
/// one (PRINT-headline-note-same-name).
///
/// Complexity tradeoff: linear in the text, with a hash lookup per mark, plus a sort of each
/// union's k members, O(k log k); each type is read twice, once for its written names
/// ([`written_in`]). Naming each variable
/// where it is first written, and looking back over the text for a name in use, would be
/// quadratic in a type with many variables (COMPLEXITY.md F169). The names of the closed types
/// are kept for the mentions, memory linear in the marks.
///
/// A text that holds a mention and no type is read too, and each mention in it is written as
/// its fallback, since no type before it was closed: so no caller prints a mention's marks.
pub fn name_vars(out: &mut String, from: usize, taken: &dyn Fn(&str) -> bool) {
    if !out[from..].contains([VARS, MENTION]) {
        return;
    }
    let text = out.split_off(from);
    let mut named: HashMap<&str, String> = HashMap::new();
    let mut closed: Vec<HashMap<&str, String>> = Vec::new();
    let mut written: HashSet<&str> = HashSet::new();
    let mut used: HashSet<String> = HashSet::new();
    let mut n = 0;
    let mut members: Vec<String> = Vec::new();
    let mut rest = text.as_str();
    written_in(rest, &mut written);
    while let Some(i) = rest.find([VARS, VARS_END, UNION, MENTION]) {
        out.push_str(&rest[..i]);
        let c = rest[i..].chars().next().expect("a mark was found");
        let tail = &rest[i + c.len_utf8()..];
        rest = match c {
            VARS | VARS_END => {
                match c {
                    VARS_END => closed.push(std::mem::take(&mut named)),
                    _ => named.clear(),
                }
                written.clear();
                used.clear();
                written_in(tail, &mut written);
                n = 0;
                tail
            }
            MENTION => {
                let end = tail.find(MENTION_END).expect("a mention is closed");
                let mut parts = tail[..end].splitn(3, NEXT);
                let (back, key, fallback) = (parts.next(), parts.next(), parts.next());
                let back: Option<usize> = back.and_then(|b| b.parse().ok());
                let name = back
                    .and_then(|b| closed.len().checked_sub(b + 1))
                    .and_then(|k| closed[k].get(key.unwrap_or_default()));
                out.push_str(name.map_or(fallback.unwrap_or_default(), String::as_str));
                &tail[end + MENTION_END.len_utf8()..]
            }
            _ => {
                let end = tail.find(UNION_END).expect("a union of marks is closed");
                members.clear();
                for m in tail[..end].split(NEXT) {
                    members.push(match m.strip_prefix(VAR) {
                        Some(k) => match named.get(k) {
                            Some(name) => name.clone(),
                            None => {
                                let wrote = k.split_once(WRITTEN).map(|(_, w)| w);
                                let name = match wrote {
                                    Some(w) if !used.contains(w) => w.to_string(),
                                    _ => fresh_name(Names::Variables, &mut n, |c: &str| {
                                        taken(c) || written.contains(c) || used.contains(c)
                                    }),
                                };
                                used.insert(name.clone());
                                named.insert(k, name.clone());
                                name
                            }
                        },
                        None => m.to_string(),
                    });
                }
                // Every member is a name from `String` on, or a recursive type's text `L(args)`
                // (`Ty::write_vars` in zedc-types), which no name holds a `(` of: each is
                // ordered by its name, the text up to a `(` (MSG-union-order-rest,
                // SPEC-union-order-recursive). Two of one name, which no union here holds (a
                // type holds one kernel set, and the union of two recursive types is their
                // unfolding, `Type::zip`), are left in the order of their texts. Inside a
                // message the recursive type's text is still a reference here, as
                // `TYPE COUNT 0 END TYPE_END`, since [`lift_holding`] names the variables
                // before it writes the references; it is ordered by the body it stands for
                // ([`standing`]), and a mark would put it after every name
                // (PRINT-recursive-type-unfolded).
                fn name(m: &str) -> &str {
                    m.find('(').map_or(m, |i| &m[..i])
                }
                let mut keyed: Vec<(String, String)> =
                    members.drain(..).map(|m| (standing(&m), m)).collect();
                keyed.sort_unstable_by(|(a, x), (b, y)| {
                    super::order::name_cmp(name(a), name(b))
                        .then_with(|| super::order::name_cmp(a, b))
                        .then_with(|| x.cmp(y))
                });
                for (j, (_, m)) in keyed.iter().enumerate() {
                    if j > 0 {
                        out.push_str(" | ");
                    }
                    out.push_str(m);
                }
                &tail[end + UNION_END.len_utf8()..]
            }
        };
    }
    out.push_str(rest);
}

/// The text a member `m` of a union of marks is ordered by ([`name_vars`]): `m`, or, when `m`
/// is a reference into the thread's table, opened by [`TYPE`] or not, the body it stands for,
/// followed through each body that is itself such a reference. A body placed uses only
/// definitions placed before it ([`lift`]), so the chain ends; it is cut at the table's
/// length all the same. Outside [`collect`] no text holds a reference, and `m` is returned.
/// Linear in the bodies followed.
fn standing(m: &str) -> String {
    let leading = |s: &str| -> Option<usize> {
        let s = s.strip_prefix(TYPE).unwrap_or(s);
        let after = s.strip_prefix(MARKS)?;
        let n = after.find(END)?;
        after[..n].parse().ok()
    };
    let Some(first) = leading(m) else {
        return m.to_string();
    };
    TABLE.with_borrow(|t| {
        let Some(t) = t.as_ref() else {
            return m.to_string();
        };
        let mut k = first;
        for _ in 0..t.bodies.len() {
            let Some(body) = t.bodies.get(k) else { break };
            match leading(body) {
                Some(j) => k = j,
                None => return body.clone(),
            }
        }
        m.to_string()
    })
}

/// Names the variables marked in `texts` ([`name_vars`]), skipping every word they write. The
/// words hold the names declarations wrote for marked variables ([`WRITTEN`]), so a variable
/// of no written name skips them in every text, as it skips a name written out. A mention
/// ([`mention`]) is no word: it is written as the name its type gives, so a variable that
/// skipped its fallback would print apart from the mention (PRINT-headline-note-same-name).
fn name_all_vars(texts: &mut [&mut String], taken: &dyn Fn(&str) -> bool) {
    if !texts.iter().any(|t| t.contains([VARS, MENTION])) {
        return;
    }
    // The text outside the mentions: each piece after a `MENTION_END`, up to a `MENTION`.
    fn outside(t: &str) -> impl Iterator<Item = &str> {
        (t.split(MENTION_END)).map(|p| p.split_once(MENTION).map_or(p, |(before, _)| before))
    }
    let words: HashSet<String> = texts
        .iter()
        .flat_map(|t| outside(t))
        .flat_map(|t| t.split(|c: char| !(c.is_alphanumeric() || c == '_')))
        .filter(|w| !w.is_empty())
        .map(String::from)
        .collect();
    for text in texts.iter_mut() {
        name_vars(text, 0, &|w| words.contains(w) || taken(w));
    }
}

/// The definitions printed while [`collect`] is on: each body, in which references stand for
/// the definitions it uses, and the place of each body known in full.
#[derive(Default)]
struct Table {
    bodies: Vec<String>,
    index: HashMap<String, usize>,
    /// Whether each definition is named however often it is written: one a printed type
    /// names itself ([`add`], [`reserve`]), not only one [`add_soft`] placed.
    hard: Vec<bool>,
    /// Whether each definition is named by how often the steps of a message use it
    /// ([`add_counted`]), unless it is `hard` too.
    counted: Vec<bool>,
    /// Whether each definition is a tuple that holds its function's variables
    /// ([`take_locals`]).
    local: Vec<bool>,
    /// What the printer keeps of the parts it printed for this table ([`with_kept`]); this
    /// module never reads it.
    kept: Option<Box<dyn Any>>,
    /// What another printer keeps of the parts it printed for this table, by the type it keeps
    /// ([`with_kept_of`]); this module never reads it either.
    kept_of: HashMap<TypeId, Box<dyn Any>>,
}

thread_local! {
    static TABLE: RefCell<Option<Table>> = const { RefCell::new(None) };
    /// The messages lifted since [`record_messages`], while it is on.
    static LIFTED: RefCell<Option<Vec<Lifted>>> = const { RefCell::new(None) };
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
pub fn active() -> bool {
    TABLE.with_borrow(Option::is_some)
}

/// The reference to definition `k`.
pub(super) fn reference(k: usize) -> String {
    format!("{REF}{k}{END}")
}

/// The reference to definition `k` placed by [`add_soft`].
pub fn soft_reference(k: usize) -> String {
    format!("{SOFT}{k}{END}")
}

/// The reference to definition `k` placed by [`add_counted`].
pub(super) fn counted_reference(k: usize) -> String {
    format!("{COUNT}{k}{END}")
}

/// `name`, a reference by `counted_reference` or [`soft_reference`], at a place where the
/// part written in full is parenthesized, as `(1 | 2)[]` or `((A, B)) -> V`; written by a name
/// it is not.
pub fn wrapped(name: &str) -> String {
    match name.strip_prefix(SOFT) {
        Some(rest) => format!("{SOFT_WRAP}{rest}"),
        None => name.replacen(COUNT, &WRAP.to_string(), 1),
    }
}

/// Whether `name`, written for a node, is a reference by [`soft_reference`]: a text the
/// message may write in full where it stands, so it binds as the text does.
pub(super) fn is_soft(name: &str) -> bool {
    name.starts_with(SOFT)
}

/// Marks the texts of one print, `roots`, written in this order into one text of a message, as
/// one type ([`TYPE`]) if one holds a reference: [`first_named`] counts the uses of a part in
/// it, as a type printed alone does, and not those of the other types its step writes.
pub(super) fn enclose(roots: &mut [String]) {
    if !roots.iter().any(|r| r.contains(MARKS)) {
        return;
    }
    roots[0].insert(0, TYPE);
    roots[roots.len() - 1].push(TYPE_END);
}

/// Marks, in each of the steps of a message, `steps` in reading order, a printed type that an
/// earlier step wrote, so that `spell` writes it as `the same type as step k`, `k` the
/// number, from 1, of the first step that wrote it (DESIGN sec:diagnostics, "Types in a
/// message"; MSG-derive-same-chain). Run on the steps before [`lift`]. A printed type is a
/// text `enclose` marked, one that holds a reference: a tuple, a union or another part this
/// module defines. Equal types are equal texts here, since a part is placed once and its
/// references are its place, and the variables of each printed type are marked apart from any
/// other's ([`VARS`]), so the comparison is of the texts. A type with no part, as `int` or
/// `1`, holds no mark and is written where it stands; a type the message writes once is not
/// changed; nor is one that, spelled, is no longer than the words, as `String | #outOfBounds`
/// or a part named in that step, `Part4`; nor is a type inside code, after an odd number of
/// backquotes, as the result of `` `bool -> (Part2, 0)` ``, which must read back as a type.
///
/// The type is marked, not replaced: `SAME`, `k`, `SAME`, then the type as it was. So the
/// parts are counted, and named, as if each step wrote the type, and `spell` decides by the
/// type as that step spells it whether it is shorter than the words, with the spelling cut off
/// at the words' length.
///
/// So a chain `x1 = x0; …; xn = x(n-1)` of names of one type of m components writes that type
/// once, and each later step `the same type as step k`, where it wrote it at each step shown.
/// The derivation shows a bounded number of lines (`additional lines not shown` in zedc-check),
/// so the text was linear in m before too; it is shorter by about the number of steps shown:
/// 39921 bytes before and 8985 after for 800 names of a tuple of 800 components (the bench
/// `rejecting_a_chain_of_n_names_of_one_type_of_n_components_writes_a_text_linear_in_n`).
///
/// Time and space linear in the steps' length: each printed type is read once and hashed
/// once, and kept once as a key, the first time it is written.
pub fn same_type_as_step(steps: &mut [String]) {
    let mut first: HashMap<String, usize> = HashMap::new();
    for (j, step) in steps.iter_mut().enumerate() {
        if !step.contains(TYPE) {
            continue;
        }
        let mut out = String::with_capacity(step.len());
        // Where the outermost printed type now open starts in `step`, and the depth.
        let (mut open, mut depth, mut copied) = (0usize, 0usize, 0usize);
        for (i, m) in step.match_indices([TYPE, TYPE_END]) {
            if m.starts_with(TYPE) {
                if depth == 0 {
                    open = i;
                }
                depth += 1;
                continue;
            }
            depth = depth
                .checked_sub(1)
                .expect("a type is opened before it is closed");
            if depth > 0 {
                continue;
            }
            let end = i + TYPE_END.len_utf8();
            let ty = &step[open..end];
            out.push_str(&step[copied..open]);
            match first.get(ty) {
                // The backquotes before `open` are counted from the step's start, so each
                // step is read once more at most: linear still.
                Some(&k) if k != j && step[..open].matches('`').count() % 2 == 0 => {
                    write!(out, "{SAME}{}{SAME}", k + 1).expect("a String takes any text")
                }
                Some(_) => {}
                None => {
                    first.insert(ty.to_string(), j);
                }
            }
            out.push_str(ty);
            copied = end;
        }
        out.push_str(&step[copied..]);
        *step = out;
    }
}

/// The end in `text`, which opens with [`TYPE`], of that printed type, after its
/// [`TYPE_END`].
fn type_end(text: &str) -> usize {
    let mut depth = 0usize;
    for (i, m) in text.match_indices([TYPE, TYPE_END]) {
        match m.starts_with(TYPE) {
            true => depth += 1,
            false => depth -= 1,
        }
        if depth == 0 {
            return i + TYPE_END.len_utf8();
        }
    }
    unreachable!("a type is closed after it is opened")
}

/// Whether `name`, written for a node, is a reference by [`counted_reference`].
pub(super) fn is_counted(name: &str) -> bool {
    name.starts_with([COUNT, WRAP])
}

/// How [`lift`] decides whether a definition is named.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    /// Named however often it is written.
    Hard,
    /// A tuple, named by its uses inside other parts ([`add_soft`]).
    Soft,
    /// Named from the first step that uses it twice or more ([`add_counted`]).
    Counted,
    /// A tuple that holds its function's variables, named as a soft one and also when it
    /// holds a part and is written twice anywhere ([`take_locals`]).
    Local,
}

/// The place of a definition with `body`, which is known in full: that of an equal body if
/// there is one. Equal texts mean the same, since each reference stands for one definition.
pub(super) fn add(body: String) -> usize {
    place(body, Kind::Hard)
}

/// As `add`, for a part that [`lift`] names only if one of its uses is inside another part,
/// by the rule [`lift`] gives; it is written in full wherever else it stands.
pub fn add_soft(body: String) -> usize {
    place(body, Kind::Soft)
}

/// As [`add`], for a part that [`lift`] names in each step of a message from the first that
/// uses it twice or more, and writes in full before: a union or an intersection, and any other
/// part but a tuple and a recursive type (MSG-derive-print-union-names).
pub(super) fn add_counted(body: String) -> usize {
    place(body, Kind::Counted)
}

fn place(body: String, kind: Kind) -> usize {
    TABLE.with_borrow_mut(|t| {
        let t = t.as_mut().expect("collecting");
        // A body that is one reference, as that of a union of one tuple, is the part it
        // refers to: defining it again would print `type Part2 = Part1;`.
        let k = match only_reference(&body).or_else(|| t.index.get(&body).copied()) {
            Some(k) => k,
            None => {
                let k = t.bodies.len();
                t.index.insert(body.clone(), k);
                t.bodies.push(body);
                t.hard.push(false);
                t.counted.push(false);
                t.local.push(false);
                k
            }
        };
        t.hard[k] |= kind == Kind::Hard;
        t.counted[k] |= kind == Kind::Counted;
        t.local[k] |= kind == Kind::Local;
        k
    })
}

/// The definition `text` refers to, if it is one reference and nothing else. A reference
/// that parenthesizes the part written in full is not that part's text alone.
pub(super) fn only_reference(text: &str) -> Option<usize> {
    let rest = text.strip_prefix([REF, SOFT, COUNT])?.strip_suffix(END)?;
    rest.parse().ok()
}

/// A place for a definition whose body uses one not placed yet, as a cycle does; its body
/// comes with [`fill`], and it is merged with none.
pub(super) fn reserve() -> usize {
    TABLE.with_borrow_mut(|t| {
        let t = t.as_mut().expect("collecting");
        t.bodies.push(String::new());
        t.hard.push(true);
        t.counted.push(false);
        t.local.push(false);
        t.bodies.len() - 1
    })
}

/// Gives the place `k` from [`reserve`] its body.
pub(super) fn fill(k: usize, body: String) {
    TABLE.with_borrow_mut(|t| t.as_mut().expect("collecting").bodies[k] = body);
}

/// Runs `f` on what the printer keeps of the parts it printed while [`collect`] is on (step
/// MSG-derive-print-per-message), which lives and ends with the table; `None` when no table is
/// on.
pub(super) fn with_kept<R>(f: impl FnOnce(&mut Option<Box<dyn Any>>) -> R) -> Option<R> {
    TABLE.with_borrow_mut(|t| t.as_mut().map(|t| f(&mut t.kept)))
}

/// As `with_kept`, for a printer outside this module, which keeps a `T`: runs `f` on it,
/// made empty the first time; `None` when no table is on. It ends with the table, and
/// [`forget_printed`] empties it.
pub fn with_kept_of<T: Default + Any, R>(f: impl FnOnce(&mut T) -> R) -> Option<R> {
    TABLE.with_borrow_mut(|t| {
        t.as_mut().map(|t| {
            let kept = t
                .kept_of
                .entry(TypeId::of::<T>())
                .or_insert_with(|| Box::new(T::default()));
            f(kept.downcast_mut::<T>().expect("kept by its type"))
        })
    })
}

/// Forgets the printed parts kept for reuse: a checker calls it when the spellings of its
/// program's literals change, since a part kept spells them as they were.
pub fn forget_printed() {
    TABLE.with_borrow_mut(|t| {
        if let Some(t) = t.as_mut() {
            t.kept = None;
            t.kept_of.clear();
        }
    });
}

/// The references in `text`, in order, each with the mark that opens it.
fn marked_refs(text: &str) -> impl Iterator<Item = (char, usize)> + '_ {
    text.match_indices(MARKS).map(|(i, m)| {
        let rest = &text[i + m.len()..];
        let n = rest.find(END).expect("a reference is closed");
        let mark = m.chars().next().expect("a mark");
        (mark, rest[..n].parse().expect("a reference is a number"))
    })
}

/// The references in `text` by the print of types they stand in ([`enclose`]): those of each
/// outermost [`TYPE`] in order, then, if any, those outside every one.
fn refs_by_type(text: &str) -> Vec<Vec<usize>> {
    let (mut types, mut open, mut outside) = (Vec::new(), Vec::new(), Vec::new());
    let mut depth = 0usize;
    for (i, m) in text.match_indices(SPELLED) {
        match m.chars().next().expect("a mark") {
            TYPE => depth += 1,
            TYPE_END => {
                depth = depth
                    .checked_sub(1)
                    .expect("a type is opened before it is closed");
                if depth == 0 {
                    types.push(std::mem::take(&mut open));
                }
            }
            _ => {
                let rest = &text[i + m.len()..];
                let n = rest.find(END).expect("a reference is closed");
                let k: usize = rest[..n].parse().expect("a reference is a number");
                match depth {
                    0 => outside.push(k),
                    _ => open.push(k),
                }
            }
        }
    }
    if !outside.is_empty() {
        types.push(outside);
    }
    types
}

/// The references in `text`, in order.
fn refs(text: &str) -> impl Iterator<Item = usize> + '_ {
    marked_refs(text).map(|(_, k)| k)
}

/// The length of `text` in characters, its references left out.
fn bare_len(text: &str) -> usize {
    let marks: usize = marked_refs(text)
        .map(|(_, k)| 2 + k.checked_ilog10().map_or(1, |d| d as usize + 1))
        .sum();
    text.chars().count() - marks
}

/// How [`spell`] writes each reference.
struct Spelling<'a> {
    /// The name of each definition named in some step.
    names: HashMap<usize, String>,
    /// The step from which each definition named by count is named ([`first_named`]).
    from: HashMap<usize, usize>,
    /// The body of each definition that some step writes in full.
    full: HashMap<usize, &'a str>,
}

/// Writes `text`, held by step `step` of a message, to `out`: each reference to a definition
/// named in that step by its name, and each other by its body, written so in turn, with a stack
/// of its own; one by [`WRAP`] or [`SOFT_WRAP`] written in full is parenthesized. The definitions
/// under a message are written as by a step after the last, `usize::MAX`. Whether it wrote a name.
///
/// Complexity tradeoff: a part written in full is written straight into `out`, in time linear
/// in what is written. Spelling each part to a string of its own first, and that string into
/// the part around it, would copy a chain of n parts nested one in the next O(n²) times.
fn spell(text: &str, s: &Spelling, step: usize, out: &mut String) -> bool {
    spell_within(text, s, step, out, usize::MAX).expect("no bound to pass")
}

/// [`spell`] with at most `cap` characters written to `out`: `None`, with `out` holding at most
/// `cap` characters, as soon as the text would write more, so the time is
/// linear in `cap`, not in the text. `usize::MAX` writes the whole text.
fn spell_within(
    text: &str,
    s: &Spelling,
    step: usize,
    out: &mut String,
    cap: usize,
) -> Option<bool> {
    let mut holds = false;
    // Characters still allowed; counted only under a bound.
    let mut room = cap;
    let mut push = |out: &mut String, piece: &str| -> Option<()> {
        if room != usize::MAX {
            let n = piece.chars().take(room + 1).count();
            if n > room {
                return None;
            }
            room -= n;
        }
        out.push_str(piece);
        Some(())
    };
    let mut stack: Vec<&str> = vec![text];
    while let Some(t) = stack.pop() {
        let Some(i) = t.find(|c| SPELLED.contains(&c) || c == SAME) else {
            push(out, t)?;
            continue;
        };
        push(out, &t[..i])?;
        let mark = t[i..].chars().next().expect("a mark was found");
        let rest = &t[i + mark.len_utf8()..];
        if mark == SAME {
            // A printed type an earlier step wrote: the words that name that step, unless the
            // type as this step spells it is no longer than they are, as `int | #a` or a part
            // named here, `Part4`. Spelling the type is cut off at the words' length, so it
            // costs O(length of the words) whichever is written, and the type is skipped when
            // the words are.
            let n = rest.find(SAME).expect("a step number is closed");
            let ty = &rest[n + SAME.len_utf8()..];
            let end = type_end(ty);
            let words = format!("the same type as step {}", &rest[..n]);
            let mut short = String::new();
            match spell_within(&ty[..end], s, step, &mut short, words.chars().count()) {
                Some(named) => {
                    push(out, &short)?;
                    holds |= named;
                }
                None => push(out, &words)?,
            }
            stack.push(&ty[end..]);
            continue;
        }
        if mark == TYPE || mark == TYPE_END {
            stack.push(rest);
            continue;
        }
        let n = rest.find(END).expect("a reference is closed");
        let k: usize = rest[..n].parse().expect("a reference is a number");
        stack.push(&rest[n + END.len_utf8()..]);
        let named_here = s.from.get(&k).is_none_or(|&j| j <= step);
        match s.names.get(&k).filter(|_| named_here) {
            Some(name) => {
                push(out, name)?;
                holds = true;
            }
            None if mark == WRAP || mark == SOFT_WRAP => {
                push(out, "(")?;
                stack.push(")");
                stack.push(s.full[&k]);
            }
            None => stack.push(s.full[&k]),
        }
    }
    Some(holds)
}

/// Whether definition `k` is named by count ([`add_counted`]).
fn by_count(t: &Table, k: usize) -> bool {
    t.counted[k] && !t.hard[k]
}

/// The number of definition `k` in a map of [`Uses`]; a text's number counts down from the
/// top, past every definition's.
fn key(k: usize) -> u32 {
    u32::try_from(k)
        .ok()
        .filter(|&k| k < 1 << 31)
        .expect("fewer definitions than 2^31")
}

/// `u` with the uses that the text or body numbered `id` makes by its references `at`, sorted:
/// one of each definition named by count that it refers to once, and many of one it refers to
/// twice or more.
fn with_refs(t: &Table, mut u: Uses, at: &[usize], id: u32) -> Uses {
    for run in at.chunk_by(|a, b| a == b) {
        if by_count(t, run[0]) {
            let used = match run.len() {
                1 => Use::One { from: id },
                _ => Use::Many,
            };
            u = u.with(key(run[0]), used);
        }
    }
    u
}

/// The uses that the body of definition `root`, with the bodies it reaches, makes of the
/// definitions named by count, kept in `memo` for each body met, which is entered once: a
/// depth-first walk with a stack of its own, a body's map made when it is left. A reference
/// back to a body on the walk's path, which a cycle makes, adds no uses: every cycle passes
/// through a definition named however often it is written, and the body first entered on the
/// cycle has every use the cycle makes.
fn body_uses<'m>(t: &Table, root: usize, memo: &'m mut HashMap<usize, Uses>) -> &'m Uses {
    if !memo.contains_key(&root) {
        let enter = |k: usize| {
            let mut at: Vec<usize> = refs(&t.bodies[k]).collect();
            at.sort_unstable();
            (k, at, 0)
        };
        let mut open: HashSet<usize> = HashSet::from([root]);
        let mut stack: Vec<(usize, Vec<usize>, usize)> = vec![enter(root)];
        while let Some(top) = stack.last_mut() {
            if let Some(&c) = top.1.get(top.2) {
                top.2 += 1;
                if !memo.contains_key(&c) && open.insert(c) {
                    stack.push(enter(c));
                }
                continue;
            }
            let (k, at, _) = stack.pop().expect("the top was found");
            let mut u = Uses::default();
            for c in at.chunk_by(|a, b| a == b) {
                if let Some(m) = memo.get(&c[0]) {
                    u = u.union(m);
                }
            }
            memo.insert(k, with_refs(t, u, &at, key(k)));
        }
    }
    &memo[&root]
}

/// The step from which each definition named by count that `texts` reach is named, by the
/// order of `texts`: the first that writes a printed type ([`enclose`]) which, with the bodies
/// it reaches, uses it twice or more. A use is a reference in the type or in one of those
/// bodies, each body counted once, as a type printed alone counts the uses of its parts
/// ([`super::Printer`]); two types of one step that each use a part once do not name it, so
/// `` `v : #off | #on` `` beside `` `#off | #on` `` writes the union in full.
///
/// Complexity tradeoff (MSG-derive-print-union-names): naive, the bodies each text reaches
/// walked anew for each text, O(n) per step and O(n²) for a derivation of n steps that each
/// print the next of a chain. Used: one map of [`Uses`] per body, made once from those of the
/// bodies it refers to, and one per text from those of its references; a persistent trie
/// (Okasaki and Gill, 1998, cited in full in [`super::uses`]) shares the map of a part with
/// every map made from it, so each map costs O(32) per reference made in its own body or text,
/// plus a merge of O(32 k) for maps
/// sharing no subtree and k keys, and the definitions used twice or more are found walking each
/// trie node once over all the texts ([`Uses::each_new_many`]). This is option (1) of
/// COMPLEXITY.md row K110, which the author chose (2026-11-13).
///
/// A part placed only by [`add_soft`] that no body reached refers to is never named by
/// [`lift_holding`] (it is inside no other part), so it is written in full at each of its
/// references: a printed type that refers to it twice or more writes each part named by count
/// that its body refers to twice or more, and that part is named from that step. So `(Part1 ->
/// 1, Part1 -> 1)` names `type Part1 = int | String;` when the function is placed. A part
/// named by count inside such a body is written once, in its declaration, as it is used twice
/// itself, so the parts its own body uses are counted as before. A soft part that a body refers
/// to is counted as before too, its body once, though the length rule may still write it in
/// full at each place (not handled: whether it is named depends on the names this function
/// gives).
// Complexity tradeoff (FAIL-nested-display-headline-type-growth): naive, each such part's body
// walked with the bodies it reaches as a tree, as the text would be written with no part named,
// O(2^d) for parts held twice at each of d levels. Used: only the references in its own body
// are read, once per printed type that writes it twice or more, a cost no greater than the
// text that type writes in full; plus one walk of the bodies the texts reach, each entered
// once, O(n) in their references, to find those a body refers to.
fn first_named(t: &Table, texts: &[&mut String]) -> HashMap<usize, usize> {
    let mut memo: HashMap<usize, Uses> = HashMap::new();
    let mut seen = Seen::default();
    let mut from: HashMap<usize, usize> = HashMap::new();
    // The definitions some body reached from the texts refers to; each body is entered once.
    let mut in_body: HashSet<usize> = HashSet::new();
    let mut entered: HashSet<usize> = HashSet::new();
    let mut stack: Vec<usize> = texts.iter().flat_map(|text| refs(text)).collect();
    while let Some(k) = stack.pop() {
        if entered.insert(k) {
            for j in refs(&t.bodies[k]) {
                in_body.insert(j);
                stack.push(j);
            }
        }
    }
    let written_whole = |k: usize| !t.hard[k] && !t.counted[k] && !in_body.contains(&k);
    // Each printed type's number, counting down from the top past every definition's.
    let mut id = u32::MAX;
    for (j, text) in texts.iter().enumerate() {
        for mut at in refs_by_type(text) {
            at.sort_unstable();
            let mut u = Uses::default();
            for c in at.chunk_by(|a, b| a == b) {
                if c.len() >= 2 && written_whole(c[0]) {
                    for k in refs(&t.bodies[c[0]]).filter(|&k| by_count(t, k)) {
                        from.entry(k).or_insert(j);
                    }
                }
                u = u.union(body_uses(t, c[0], &mut memo));
            }
            assert!(id >= 1 << 31, "fewer printed types than 2^31");
            let u = with_refs(t, u, &at, id);
            id -= 1;
            u.each_new_many(&mut seen, &mut |k| {
                from.entry(k as usize).or_insert(j);
            });
        }
    }
    from
}

/// Names the definitions `texts` reach, directly or through other definitions, `Part1`, `Part2`, …
/// and writes each reference to a named one by its name. Gives the definitions, name and body,
/// each before its uses but where definitions refer to each other in a cycle. Numbers are given
/// in that order, which is found from the texts alone, so equal texts get equal names. A name is
/// skipped if the program binds it, `taken` says so or a text holds it as a word, so a
/// definition `Part5` the message writes leaves `Part5` to it ([`fresh_name`]). First the unbounded
/// variables the texts mark are named, skipping every word of the texts ([`name_vars`]). `texts`
/// with no mark or reference are left as they are, and give no definition.
///
/// The texts are the steps of a message in reading order. A part placed by `add_counted`, a
/// union or an intersection, is named in each text from the first that writes a printed type
/// which, with the bodies it reaches, uses it twice or more (`first_named`), and in the
/// definitions; before that text, and in a message where no printed type uses it twice, it is
/// written in full. So a step that uses a union once spells it, and once a step names it,
/// that step and every later one write it by name.
///
/// A part placed by `add_soft` is counted where it is written: n times in all, counting each
/// reference in a text and each in a body reached, each body once, and n_b of them in bodies.
/// One whose body holds a part named somewhere is named when n_b ≥ 1 and n ≥ 2: so a part held
/// at each level of a nesting, or by each link of a chain whose steps print each link, is
/// written once. One whose body holds none, of length L with the parts in it written in full,
/// is named when `n_b × L` is more than `type Tk = …;` and n_b + 1 names `Tk`; left in full at
/// n_b ≥ 2 it is at most `((n_b + 1) × |Tk| + 9) / (n_b - 1)`, about three names, long.
/// Otherwise each reference to a part is its body, written in full. A body placed so uses only
/// definitions placed before it, or ones a printed type names itself, so writing one in full
/// ends.
///
/// Time linear in the texts and the bodies reached, and in the parts written in full, with a
/// hash lookup per reference, and the merges of `first_named`.
pub fn lift(texts: &mut [&mut String], taken: &dyn Fn(&str) -> bool) -> Vec<(String, String)> {
    lift_holding(texts, false, taken).0
}

/// As [`lift`], and also whether each text names a definition once lifted. With `headline`,
/// the first text is a message's sentence, which writes each tuple it writes whole in full,
/// its parts named as anywhere else: `(Part1, Part1)`, not a `Part2` the reader would have to look
/// up below (DESIGN sec:diagnostics, "Types in a message"). That adds one body per tuple the
/// sentence writes. The parts are counted as if the sentence wrote those tuples by reference,
/// so a part written once inside a tuple that both the sentence and a step write is not
/// thereby written twice.
pub fn lift_holding(
    texts: &mut [&mut String],
    headline: bool,
    taken: &dyn Fn(&str) -> bool,
) -> (Vec<(String, String)>, Vec<bool>) {
    // The step from which each part named by count is named, found before the sentence's
    // tuples are opened below, so that a tuple it writes twice counts its parts once.
    let from = match texts.iter().any(|t| t.contains(MARKS)) {
        true => TABLE.with_borrow(|t| {
            first_named(
                t.as_ref().expect("references are lifted while collecting"),
                texts,
            )
        }),
        false => HashMap::new(),
    };
    // The tuples the sentence writes whole, once per place; each is counted below as a use
    // of itself, as if not opened.
    let mut opened: Vec<usize> = Vec::new();
    if let Some(first) = texts
        .first_mut()
        .filter(|t| headline && t.contains([SOFT, SOFT_WRAP]))
    {
        **first = TABLE.with_borrow(|t| {
            let t = t.as_ref().expect("references are lifted while collecting");
            let mut out = String::with_capacity(first.len());
            let mut rest = first.as_str();
            while let Some(i) = rest.find([SOFT, SOFT_WRAP]) {
                out.push_str(&rest[..i]);
                let mark = rest[i..].chars().next().expect("a mark was found");
                let after = &rest[i + mark.len_utf8()..];
                let n = after.find(END).expect("a reference is closed");
                let k: usize = after[..n].parse().expect("a reference is a number");
                match mark == SOFT_WRAP {
                    true => out.extend(["(", &t.bodies[k], ")"]),
                    false => out.push_str(&t.bodies[k]),
                }
                opened.push(k);
                rest = &after[n + END.len_utf8()..];
            }
            out.push_str(rest);
            out
        });
    }
    name_all_vars(texts, taken);
    for text in texts.iter_mut() {
        take_locals(text);
    }
    let raw: Option<Vec<String>> = LIFTED
        .with_borrow(Option::is_some)
        .then(|| texts.iter().map(|t| t.to_string()).collect());
    if !texts.iter().any(|t| t.contains(SPELLED)) {
        return (Vec::new(), vec![false; texts.len()]);
    }
    // Each definition reached, in the order of the depth-first walk below, with its body and
    // whether it is named.
    let reached: Vec<(usize, String, bool)> = TABLE.with_borrow(|t| {
        let t = t.as_ref().expect("references are lifted while collecting");
        // Depth-first from the references in reading order; a definition is listed when
        // left, after the definitions its body uses, and each is entered once.
        let mut order = Vec::new();
        let mut seen: HashSet<usize> = HashSet::new();
        // How often each definition is written, in the texts and in the bodies reached, and
        // how often in those bodies.
        let mut uses: HashMap<usize, (usize, usize)> = HashMap::new();
        // The sentence's opened tuples, after its references, are walked as if written
        // there; the references their bodies put in the sentence were counted with those
        // bodies, so they are taken off the sentence's count.
        let roots = texts.iter().flat_map(|text| refs(text));
        for k in roots.chain(opened.iter().copied()) {
            uses.entry(k).or_default().0 += 1;
            if !seen.insert(k) {
                continue;
            }
            let mut stack: Vec<(usize, std::vec::IntoIter<usize>)> =
                vec![(k, refs(&t.bodies[k]).collect::<Vec<_>>().into_iter())];
            for &j in stack[0].1.as_slice() {
                let u = uses.entry(j).or_default();
                *u = (u.0 + 1, u.1 + 1);
            }
            while let Some((at, next)) = stack.last_mut() {
                let at = *at;
                match next.find(|j| !seen.contains(j)) {
                    Some(j) => {
                        seen.insert(j);
                        let inner: Vec<usize> = refs(&t.bodies[j]).collect();
                        for &i in &inner {
                            let u = uses.entry(i).or_default();
                            *u = (u.0 + 1, u.1 + 1);
                        }
                        stack.push((j, inner.into_iter()));
                    }
                    None => {
                        order.push(at);
                        stack.pop();
                    }
                }
            }
        }
        for &k in &opened {
            for j in refs(&t.bodies[k]) {
                uses.get_mut(&j).expect("counted in the sentence").0 -= 1;
            }
        }
        // The longest name a definition can take, as long as `T` and the number of
        // definitions reached; a name skipped for one the program binds is longer, which
        // makes naming no shorter than this counts it.
        let name = 1 + order.len().to_string().len();
        // For each definition left, whether its body holds a part named somewhere, through
        // the parts named by count it writes in full, and else its length with those
        // written in full. A definition is left after those its body refers to, but on a
        // cycle, whose parts are named.
        let mut bare: HashMap<usize, (bool, usize)> = HashMap::with_capacity(order.len());
        // For each definition left, whether it is named and its length with every part it
        // holds that is not named written in full. A tuple that holds its function's
        // variables is judged by these ([`Kind::Local`]): the text, read back, holds each
        // part not named as a copy at each place, so reading it back must give the same
        // judgment, and these two are the same for a part and for its copies.
        let mut whole: HashMap<usize, (bool, usize)> = HashMap::with_capacity(order.len());
        order
            .into_iter()
            .map(|k| {
                let body = &t.bodies[k];
                let (mut part, mut len) = (false, bare_len(body));
                let (mut named_part, mut whole_len) = (false, len);
                for (mark, j) in marked_refs(body) {
                    match bare.get(&j) {
                        Some(&(p, l)) if by_count(t, j) && !from.contains_key(&j) => {
                            part |= p;
                            len += l + if mark == WRAP { 2 } else { 0 };
                        }
                        _ => part = true,
                    }
                    match whole.get(&j) {
                        Some(&(false, l)) => {
                            let wrap = matches!(mark, WRAP | SOFT_WRAP);
                            whole_len = whole_len.saturating_add(l + if wrap { 2 } else { 0 });
                        }
                        // Named, or on a cycle, whose parts are named.
                        _ => named_part = true,
                    }
                }
                bare.insert(k, (part, len));
                let (part, len) = match t.local[k] {
                    true => (named_part, whole_len),
                    false => (part, len),
                };
                let (n, inside) = uses[&k];
                // A tuple with a part of its own is named when it is written twice, once
                // inside another part, so that a part held at each level of a nesting is
                // written once. A tuple that holds its function's variables and a part named
                // is named when written twice anywhere: written in full twice in the text, it
                // would read back as two tuples, which print again as other text (row
                // PRINT-shared-part-exponential). A tuple with none is named when its
                // declaration `type Tk = …;` and a name at each of its uses in bodies are
                // shorter than a copy at each.
                let named = t.hard[k]
                    || match (by_count(t, k), part) {
                        (true, _) => from.contains_key(&k),
                        (false, true) => (inside > 0 || t.local[k]) && n >= 2,
                        (false, false) => {
                            inside.saturating_mul(len)
                                > len + "type  = ;".len() + (inside + 1) * name
                        }
                    };
                whole.insert(k, (named, whole_len));
                (k, body.clone(), named)
            })
            .collect()
    });
    let words: HashSet<&str> = texts
        .iter()
        .map(|t| t.as_str())
        .chain(reached.iter().map(|(_, b, _)| b.as_str()))
        .flat_map(|t| t.split(|c: char| !(c.is_alphanumeric() || c == '_')))
        // Only a word a definition could be named, `Part{k}`, can clash ([`Names::Definitions`]).
        .filter(|w| w.starts_with("Part"))
        .collect();
    let mut names: HashMap<usize, String> = HashMap::with_capacity(reached.len());
    let mut n = 0;
    for (k, _, named) in &reached {
        if *named {
            let name: String = fresh_name(Names::Definitions, &mut n, |w| {
                words.contains(w) || taken(w)
            });
            names.insert(*k, name);
        }
    }
    // The body of each part some step writes in full where it stands: one not named, and one
    // named by count, which the steps before it is named write in full.
    let full: HashMap<usize, &str> = (reached.iter())
        .filter(|(k, _, named)| !named || from.contains_key(k))
        .map(|(k, b, _)| (*k, b.as_str()))
        .collect();
    let spelling = Spelling { names, from, full };
    let holding: Vec<bool> = texts
        .iter_mut()
        .enumerate()
        .map(|(step, text)| {
            if !text.contains(SPELLED) {
                return false;
            }
            let mut out = String::with_capacity(text.len());
            let holds = spell(text, &spelling, step, &mut out);
            **text = out;
            holds
        })
        .collect();
    let defs = (reached.iter())
        .filter(|(_, _, named)| *named)
        .map(|(k, body, _)| {
            let mut out = String::with_capacity(body.len());
            spell(body, &spelling, usize::MAX, &mut out);
            (spelling.names[k].clone(), out)
        })
        .collect();
    if let Some(raw) = raw {
        let Spelling { names, from, full } = spelling;
        let full = full.into_iter().map(|(k, b)| (k, b.to_string())).collect();
        let lifted = Lifted {
            raw,
            defs: Vec::clone(&defs),
            names,
            from,
            full,
        };
        LIFTED.with_borrow_mut(|l| l.as_mut().map(|l| l.push(lifted)));
    }
    (defs, holding)
}

/// A message [`lift_holding`] wrote while [`record_messages`] was on, kept for the test that
/// parses each type a step writes back with the message's declarations in scope (step L1.29,
/// MSG-derive-print-union-names): its texts before the references were written, its
/// definitions, and how each reference is written.
pub struct Lifted {
    raw: Vec<String>,
    /// The definitions, each name with its body, as the message declares them.
    pub defs: Vec<(String, String)>,
    names: HashMap<usize, String>,
    from: HashMap<usize, usize>,
    full: HashMap<usize, String>,
}

impl Lifted {
    /// `text`, a type's text printed while the message collected definitions, as each step
    /// whose text holds it writes it: none if no step holds it, as a type with variables the
    /// message renamed.
    pub fn spelled(&self, text: &str) -> Vec<String> {
        let spelling = Spelling {
            names: self.names.clone(),
            from: self.from.clone(),
            full: (self.full.iter()).map(|(&k, b)| (k, b.as_str())).collect(),
        };
        (self.raw.iter().enumerate())
            .filter(|(_, t)| t.contains(text))
            .map(|(step, _)| {
                let mut out = String::new();
                spell(text, &spelling, step, &mut out);
                out
            })
            .collect()
    }
}

/// Starts keeping each message [`lift_holding`] writes on this thread, dropping those kept.
pub fn record_messages() {
    LIFTED.set(Some(Vec::new()));
}

/// Whether [`record_messages`] is on for this thread: then each call of [`lift_holding`] is
/// kept, so a caller that would reuse a result instead of calling it again calls it.
pub fn recording_messages() -> bool {
    LIFTED.with_borrow(Option::is_some)
}

/// The messages kept since [`record_messages`], in the order written; keeping stops.
pub fn take_messages() -> Vec<Lifted> {
    LIFTED.take().unwrap_or_default()
}

/// Whether `text`, printed while a message collects definitions, holds a reference to one.
pub fn holds_reference(text: &str) -> bool {
    text.contains(MARKS) || text.contains(LOCALS)
}

/// Writes the definition of `name` as a user declares it at the top level, `type Part1 = …;`, and
/// ends the line: a type printed alone has its definitions on lines of their own before it
/// (DESIGN sec:diagnostics, "Types in a message").
pub fn declare(out: &mut impl fmt::Write, name: &str, body: &str) -> fmt::Result {
    writeln!(out, "{}", Declaration(name, body))
}

/// The definition of a name, given with its body, as a user declares it at the top level:
/// `type Part1 = …;`.
pub struct Declaration<'a>(pub &'a str, pub &'a str);

impl fmt::Display for Declaration<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "type {} = {};", self.0, self.1)
    }
}

/// `text` alone, finished: each of its definitions declared on a line of its own
/// ([`declare`]), then the text, as a type printed outside a message is.
pub fn plain(text: &str) -> String {
    if !text.contains([
        REF,
        SOFT,
        COUNT,
        WRAP,
        SOFT_WRAP,
        TYPE,
        VARS,
        LOCAL_OPEN,
        LOCAL_OPEN_WRAP,
    ]) {
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
    let names: Vec<&str> = defs.iter().map(|(n, _)| n.as_str()).collect();
    match names.len() {
        0 => return,
        1 => write!(
            message,
            "\n  {} stands for a part written more than once:",
            names[0]
        ),
        _ => write!(
            message,
            "\n  {} stand for parts written more than once:",
            and_list(&names)
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

#[cfg(test)]
mod tests {
    use super::*;

    /// A union of the marks `keys` alone, as zedc-types writes a variable printed by a mark.
    fn marks(keys: &[&str]) -> String {
        let mut out = String::from(UNION);
        for (i, k) in keys.iter().enumerate() {
            if i > 0 {
                out.push(NEXT);
            }
            out.push(VAR);
            out.push_str(k);
        }
        out.push(UNION_END);
        out
    }

    /// UNDERSCORE-print-followups: a variable a declaration wrote a name for keeps it, though
    /// one of no written name stands before it; a second of that written name in the type gets
    /// a fresh one; every place of one variable gets one name; and each type names its own
    /// variables from `T` on.
    #[test]
    fn a_written_name_is_kept_and_the_others_skip_it_in_order_of_first_place() {
        let (a, b1, b2) = (marks(&["0"]), marks(&["b1:T"]), marks(&["b2:T"]));
        let mut text = format!("{VARS}({a}, {b1}, {b2}, {a}){VARS_END}");
        text.push_str(&format!("{VARS}({a}){VARS_END}"));
        name_vars(&mut text, 0, &|_| false);
        assert_eq!(text, "(U, T, V, U)(T)");
        // A word of the message is skipped by a fresh name, never by a written one.
        let mut text = format!("{VARS}({a}, {b1}){VARS_END}");
        name_vars(&mut text, 0, &|w| w == "T" || w == "U");
        assert_eq!(text, "(V, T)");
        // In one union the members are written by name, the written one among them.
        let mut text = format!("{VARS}{}{VARS_END}", marks(&["0", "b1:A"]));
        name_vars(&mut text, 0, &|_| false);
        assert_eq!(text, "A | T");
    }

    /// PRINT-headline-note-same-name: a mention names its variable as the type it refers back
    /// to names it. Red before: the mention marks were left in the text, and a clause that
    /// wrote the checker's name `T` as a plain word made the type skip `T` and print `U`.
    #[test]
    fn a_mention_names_its_variable_as_its_type_does() {
        let b0 = marks(&["b0"]);
        // The type names `b0` apart from the words of the message, and the mention follows.
        let mut text = format!(
            "{VARS}({b0}, {b0}){VARS_END} with {}",
            mention(0, "b0", "T")
        );
        name_vars(&mut text, 0, &|w| w == "T");
        assert_eq!(text, "(U, U) with U");
        // A mention is no word of the message: the type keeps `T`.
        let mut text = format!(
            "{VARS}({b0}, {b0}){VARS_END} with {}",
            mention(0, "b0", "T")
        );
        name_all_vars(&mut [&mut text], &|_| false);
        assert_eq!(text, "(T, T) with T");
        // A type between the one referred to and the mention: `back` 1 reads past it.
        let (a, b) = (marks(&["0"]), marks(&["1"]));
        let mut text = format!(
            "{VARS}({a}, {b}, {b}){VARS_END} at {VARS}({a}, {a}){VARS_END}: {} and {}",
            mention(1, "1", "X"),
            mention(0, "0", "X")
        );
        name_vars(&mut text, 0, &|_| false);
        assert_eq!(text, "(T, U, U) at (T, T): U and T");
        // A key the type never named, and a `back` past the first type, write the fallback.
        let mut text = format!(
            "{VARS}({b0}){VARS_END}: {} {}",
            mention(0, "b9", "X"),
            mention(1, "b0", "Y")
        );
        name_vars(&mut text, 0, &|_| false);
        assert_eq!(text, "(T): X Y");
    }

    /// A text that holds a mention and no type writes the mention's fallback, so no caller
    /// prints a mention's marks. zedc-types writes a mention only after the mark it names
    /// (`arrow_text_naming`), so no caller makes such a text today; this keeps one from
    /// printing marks if one ever does. Red before: the text was left as it was.
    #[test]
    fn a_mention_with_no_type_before_it_writes_its_fallback() {
        let mut text = format!("with {}", mention(0, "0", "A"));
        name_vars(&mut text, 0, &|_| false);
        assert_eq!(text, "with A");
        let mut text = format!("with {}", mention(0, "0", "A"));
        name_all_vars(&mut [&mut text], &|_| false);
        assert_eq!(text, "with A");
    }

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
        assert_eq!(text, "Part2 | Part4");
        assert_eq!(
            defs,
            [
                ("Part1".to_string(), "#a | #b".to_string()),
                ("Part2".to_string(), "(Part1, Part1)".to_string()),
                ("Part3".to_string(), "(Part4, Part4)".to_string()),
                ("Part4".to_string(), "#x(Part3) | #y".to_string())
            ]
        );
        // An equal body is merged with the one there; a reserved one never is.
        assert_eq!(add("#a | #b".into()), inner);
    }

    #[test]
    fn a_tuple_is_named_when_written_twice_once_inside_another_or_when_naming_it_is_shorter() {
        let _on = collect();
        // `d0 = (1, 1); d1 = (d0, d0); d2 = (d1, d1);` with a note on `d2`; a tuple of seven
        // components inside `p` and `q`, and one of five inside `r` and `s`; `(int, int)`
        // written whole in two notes and inside no other part; and `a0 = (0, 0);
        // a1 = (a0, 1); a2 = (a1, 2);` with a note on `a1` and one on `a2`. Thirteen parts
        // are reached, so a name is 3 long, and `type Tk = ;` is 9.
        let d0 = add_soft("(1, 1)".into());
        let d1 = add_soft(format!("({0}, {0})", soft_reference(d0)));
        let d2 = add_soft(format!("({0}, {0})", soft_reference(d1)));
        let x7 = add_soft("(0, 1, 2, 3, 4, 5, 6)".into());
        let p = add_soft(format!("({}, 5)", soft_reference(x7)));
        let q = add_soft(format!("({}, 6)", soft_reference(x7)));
        let x5 = add_soft("(0, 1, 2, 3, 4)".into());
        let r = add_soft(format!("({}, 5)", soft_reference(x5)));
        let s = add_soft(format!("({}, 6)", soft_reference(x5)));
        let y = add_soft("(int, int)".into());
        let a0 = add_soft("(0, 0)".into());
        let a1 = add_soft(format!("({}, 1)", soft_reference(a0)));
        let a2 = add_soft(format!("({}, 2)", soft_reference(a1)));
        let mut t: Vec<String> = [d2, p, q, r, s, y, y, a1, a2].map(soft_reference).into();
        let (defs, holding) =
            lift_holding(&mut t.iter_mut().collect::<Vec<_>>(), false, &|_| false);
        // `d1`, with parts, is written twice in `d2`, and `a1` in `a2` and a note: named.
        // `d2`, `p`, `q`, `r`, `s` and `a2` are inside no other part, and `y` too. Of the
        // tuples with no part, `x7` is named, 2 × 21 > 21 + 9 + 3 × 3; `x5` is not,
        // 2 × 15 ≤ 15 + 9 + 3 × 3; `d0`, 2 × 6, and `a0`, 1 × 6, are not.
        let expected = [
            "(Part1, Part1)",
            "(Part2, 5)",
            "(Part2, 6)",
            "((0, 1, 2, 3, 4), 5)",
            "((0, 1, 2, 3, 4), 6)",
            "(int, int)",
            "(int, int)",
            "Part3",
            "(Part3, 2)",
        ];
        assert_eq!(t, expected);
        let defs: Vec<(&str, &str)> = defs.iter().map(|(a, b)| (a.as_str(), b.as_str())).collect();
        assert_eq!(
            defs,
            [
                ("Part1", "((1, 1), (1, 1))"),
                ("Part2", "(0, 1, 2, 3, 4, 5, 6)"),
                ("Part3", "((0, 0), 1)")
            ]
        );
        assert_eq!(
            holding,
            [true, true, true, false, false, false, false, true, true]
        );
        // A part a printed type names itself stays named, whichever way it was placed first.
        assert_eq!(add("(1, 1)".into()), d0);
        let mut t = format!("({0}, {0})", soft_reference(d0));
        assert_eq!(
            lift(&mut [&mut t], &|_| false),
            [("Part1".to_string(), "(1, 1)".to_string())]
        );
        assert_eq!(t, "(Part1, Part1)");
    }

    #[test]
    fn a_message_sentence_writes_its_tuples_whole_at_the_top_level() {
        let _on = collect();
        let d0 = add_soft("(1, 1)".into());
        let d1 = add_soft(format!("({0}, {0})", soft_reference(d0)));
        let d2 = add_soft(format!("({0}, {0})", soft_reference(d1)));
        // The sentence and a note both write `d2`.
        let (mut s, mut n) = (
            format!("`+` does not take ({}, 1)", soft_reference(d2)),
            soft_reference(d2),
        );
        let (defs, _) = lift_holding(&mut [&mut s, &mut n], true, &|_| false);
        assert_eq!(s, "`+` does not take ((Part1, Part1), 1)");
        assert_eq!(n, "(Part1, Part1)");
        assert_eq!(
            defs,
            [("Part1".to_string(), "((1, 1), (1, 1))".to_string())]
        );
        // A pair written once in `o`, which the sentence and a note both write: the sentence
        // writing `o` whole does not make the pair written twice inside another part.
        let u = add("#a | #b".into());
        let pair = add_soft(format!("({0}, {0})", reference(u)));
        let o = add_soft(format!("({}, 0)", soft_reference(pair)));
        let (mut s, mut n) = (
            format!("`g` does not take {}", soft_reference(o)),
            soft_reference(o),
        );
        let (defs, _) = lift_holding(&mut [&mut s, &mut n], true, &|_| false);
        assert_eq!(s, "`g` does not take ((Part1, Part1), 0)");
        assert_eq!(n, "((Part1, Part1), 0)");
        assert_eq!(defs, [("Part1".to_string(), "#a | #b".to_string())]);
    }

    #[test]
    fn a_counted_part_is_written_until_a_step_uses_it_twice_and_named_in_every_step_after() {
        let _on = collect();
        let u = add_counted("#a | #b".into());
        let r = counted_reference(u);
        // A printed type, as a print writes it into a message.
        let ty = |text: String| {
            let mut roots = [text];
            enclose(&mut roots);
            let [text] = roots;
            text
        };
        // Steps in reading order: once, once where it is parenthesized, twice, once, once
        // parenthesized.
        let mut t: Vec<String> = vec![
            ty(r.clone()),
            ty(format!("{}[]", wrapped(&r))),
            format!("`f` is `{}`", ty(format!("({r}) -> ({r}, 0)"))),
            ty(r.clone()),
            ty(format!("{}[]", wrapped(&r))),
        ];
        let (defs, _) = lift_holding(&mut t.iter_mut().collect::<Vec<_>>(), false, &|_| false);
        assert_eq!(
            t,
            [
                "#a | #b",
                "(#a | #b)[]",
                "`f` is `(Part1) -> (Part1, 0)`",
                "Part1",
                "Part1[]"
            ]
        );
        assert_eq!(defs, [("Part1".to_string(), "#a | #b".to_string())]);
        // Used once by each type, it is never named, though a step writes two such types.
        let mut t: Vec<String> = vec![
            format!("`v : {}` is not `{}`", ty(r.clone()), ty(r.clone())),
            ty(format!("({r}, 0)")),
        ];
        let (defs, _) = lift_holding(&mut t.iter_mut().collect::<Vec<_>>(), false, &|_| false);
        assert_eq!(t, ["`v : #a | #b` is not `#a | #b`", "(#a | #b, 0)"]);
        assert!(defs.is_empty());
    }

    /// A sentence's tuple at a place where its text is parenthesized, `T[]`, is written whole in
    /// parentheses.
    #[test]
    fn a_sentence_writes_a_wrapped_tuple_whole_in_parentheses() {
        let _on = collect();
        let d0 = add_soft("(1, 1)".into());
        let mut s = format!("`f` does not take {}[]", wrapped(&soft_reference(d0)));
        let (defs, _) = lift_holding(&mut [&mut s], true, &|_| false);
        assert_eq!(s, "`f` does not take ((1, 1))[]");
        assert!(defs.is_empty());
    }

    /// A step whose printed type an earlier step wrote writes `the same type as step k`, `k`
    /// the first that wrote it; a type written once, a different one, and a step's text
    /// around the type are kept (MSG-derive-same-chain).
    #[test]
    fn a_type_an_earlier_step_wrote_is_the_same_type_as_that_step() {
        let _on = collect();
        let a = soft_reference(add_soft("(0, 1, 2, 3, 4, 5, 6, 7, 8, 9)".into()));
        // Shorter, spelled, than the words that would replace it.
        let b = soft_reference(add_soft("(3, 4)".into()));
        let u = soft_reference(add_soft("String | #outOfBounds".into()));
        let h = reference(add("int | #x".into()));
        let ty = |text: String| {
            let mut roots = [text];
            enclose(&mut roots);
            let [text] = roots;
            text
        };
        let mut steps = vec![
            "`x` is int here".to_string(),
            format!("`x2` is {} here", ty(a.clone())),
            format!("`y` is {}", ty(b.clone())),
            format!("`x1` is {} here", ty(a.clone())),
            // A type holding the first inside another is a different type.
            format!("`z` is {}", ty(format!("({a}, {})", ty(a.clone())))),
            format!("`w` is {} and {}", ty(b.clone()), ty(a.clone())),
            format!("`v` is {}", ty(u.clone())),
            format!("`v2` is {}", ty(u.clone())),
            // Inside code a type must read back, so it is kept.
            format!("`f` is `int -> {}`", ty(a.clone())),
            // A part named in the message is one word, shorter than the words.
            format!("`p` is {}", ty(h.clone())),
            format!("`q` is {}", ty(h.clone())),
        ];
        same_type_as_step(&mut steps);
        let mut texts: Vec<&mut String> = steps.iter_mut().collect();
        lift(&mut texts, &|_| false);
        assert_eq!(
            steps,
            [
                "`x` is int here",
                "`x2` is (0, 1, 2, 3, 4, 5, 6, 7, 8, 9) here",
                "`y` is (3, 4)",
                "`x1` is the same type as step 2 here",
                "`z` is ((0, 1, 2, 3, 4, 5, 6, 7, 8, 9), (0, 1, 2, 3, 4, 5, 6, 7, 8, 9))",
                "`w` is (3, 4) and the same type as step 2",
                "`v` is String | #outOfBounds",
                "`v2` is String | #outOfBounds",
                "`f` is `int -> (0, 1, 2, 3, 4, 5, 6, 7, 8, 9)`",
                "`p` is Part1",
                "`q` is Part1",
            ]
        );
    }

    /// A type as long as `the same type as step 1`, 23 characters, is kept; one character more
    /// and the words are written.
    #[test]
    fn a_type_as_long_as_the_words_is_kept_and_one_longer_is_replaced() {
        let _on = collect();
        let even = soft_reference(add_soft("#abcdefghij | #klmnopqr".into()));
        let over = soft_reference(add_soft("#abcdefghij | #klmnopqrs".into()));
        assert_eq!(
            "#abcdefghij | #klmnopqr".len(),
            "the same type as step 1".len()
        );
        let ty = |text: String| {
            let mut roots = [text];
            enclose(&mut roots);
            let [text] = roots;
            text
        };
        let mut steps = vec![
            format!("{} and {}", ty(even.clone()), ty(over.clone())),
            format!("{} and {}", ty(even.clone()), ty(over.clone())),
        ];
        same_type_as_step(&mut steps);
        let mut texts: Vec<&mut String> = steps.iter_mut().collect();
        lift(&mut texts, &|_| false);
        assert_eq!(
            steps,
            [
                "#abcdefghij | #klmnopqr and #abcdefghij | #klmnopqrs",
                "#abcdefghij | #klmnopqr and the same type as step 1",
            ]
        );
    }

    /// A printed type inside another is counted with the outermost: a counted part used once
    /// in each is used twice by one type, and named.
    #[test]
    fn a_type_printed_inside_another_counts_with_the_outermost() {
        let _on = collect();
        let r = counted_reference(add_counted("#a | #b".into()));
        let ty = |text: String| {
            let mut roots = [text];
            enclose(&mut roots);
            let [text] = roots;
            text
        };
        let mut t = ty(format!("({r}, {})", ty(r.clone())));
        let defs = lift(&mut [&mut t], &|_| false);
        assert_eq!(t, "(Part1, Part1)");
        assert_eq!(defs, [("Part1".to_string(), "#a | #b".to_string())]);
    }

    /// Forgetting the printed parts empties what a printer keeps, and does nothing when no
    /// table is on.
    #[test]
    fn forgetting_the_printed_parts_empties_what_is_kept() {
        forget_printed();
        assert!(!active());
        assert_eq!(with_kept_of(|n: &mut u32| *n), None);
        let _on = collect();
        assert_eq!(with_kept_of(|n: &mut u32| std::mem::replace(n, 7)), Some(0));
        assert_eq!(with_kept_of(|n: &mut u32| *n), Some(7));
        forget_printed();
        assert_eq!(with_kept_of(|n: &mut u32| *n), Some(0));
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
