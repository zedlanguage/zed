//! The names a printed type makes up: its type variables, `T`, `U`, `V`, `W`, `T5`, …, and the
//! definitions a message lifts out of it, `T1`, `T2`, … ([`crate::types::defs`]). Every place that
//! makes up such a name picks it with [`fresh_name`], so all of them follow one rule: a made-up
//! name is the next of its sequence that the program does not bind ([`ProgramNames`]) and that
//! the caller's `taken` does not hold, such as a name the message already writes. The two
//! sequences share the names from `T5` on, so a message that writes a variable `T5` defines
//! its parts as `T1` to `T4`, `T6`, …: the definitions skip the words of the message.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// Which sequence a made-up name comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Names {
    /// A signature's own type variables: `T`, `U`, `V`, `W`, `T5`, `T6`, ….
    Variables,
    /// The definitions of a printed type: `T1`, `T2`, ….
    Definitions,
}

/// The letters the variables are named first.
const LETTERS: [&str; 4] = ["T", "U", "V", "W"];

impl Names {
    /// The `n`th name of the sequence, counted from 0: `T` or `T1` first. From `n = 4` on both
    /// sequences give `T{n + 1}`.
    pub fn nth<S: From<&'static str> + From<String>>(self, n: usize) -> S {
        match (self, n) {
            (Names::Variables, 0..4) => LETTERS[n].into(),
            _ => format!("T{}", n + 1).into(),
        }
    }
}

/// The names a program binds that a sequence could give: for each, the letter's place, or the
/// number `k - 1` of a name `T{k}` (`k` at least 1, written without a leading zero).
enum Place {
    Letter(usize),
    Numbered(usize),
}

fn place(name: &str) -> Option<Place> {
    if let Some(i) = LETTERS.iter().position(|&l| l == name) {
        return Some(Place::Letter(i));
    }
    let digits = name.strip_prefix('T')?;
    if digits.starts_with('0') || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let k: usize = digits.parse().ok()?;
    Some(Place::Numbered(k - 1))
}

/// The names of [`Names`] a program binds, as [`ProgramNames`] holds them.
#[derive(Default)]
struct Held {
    /// Whether the program binds each of `T`, `U`, `V`, `W`.
    letters: [bool; 4],
    /// For each `n` such that the program binds `T{n + 1}`, the first `m > n` such that it
    /// binds none of `T{n + 1}` to `T{m}`: a run of bound names is stepped over at once.
    ends: HashMap<usize, usize>,
}

thread_local! {
    /// The names of the program being checked on this thread ([`ProgramNames`]).
    static HELD: RefCell<Rc<Held>> = RefCell::default();
}

/// The names a program binds, which no made-up name takes while it is held: a type a message
/// prints is read in the program's scope, where `T` already names the program's own `T`
/// (DESIGN.md sec:diagnostics, "Types in a message"). Dropping it puts back the names held
/// before, so a check started inside another, as of an operator alone, leaves them as it found
/// them.
pub struct ProgramNames(Rc<Held>);

impl ProgramNames {
    /// Holds `names`, the names the program binds, on this thread until it is dropped. Only
    /// those a [`Names`] sequence gives matter, so the table is as large as they are. `O(k)`
    /// for `k` names.
    pub fn hold<'n>(names: impl IntoIterator<Item = &'n str>) -> ProgramNames {
        let mut held = Held::default();
        let mut numbered = HashSet::new();
        for p in names.into_iter().filter_map(place) {
            match p {
                Place::Letter(i) => held.letters[i] = true,
                Place::Numbered(n) => {
                    numbered.insert(n);
                }
            }
        }
        // Each run of consecutive numbers is walked once, from its first.
        held.ends.reserve(numbered.len());
        for &n in &numbered {
            if n > 0 && numbered.contains(&(n - 1)) {
                continue;
            }
            let mut end = n + 1;
            while numbered.contains(&end) {
                end += 1;
            }
            held.ends.extend((n..end).map(|k| (k, end)));
        }
        ProgramNames(HELD.replace(Rc::new(held)))
    }
}

impl Drop for ProgramNames {
    fn drop(&mut self) {
        HELD.set(std::mem::take(&mut self.0));
    }
}

/// The next name of `names` from the `n`th on that the program being checked does not bind
/// ([`ProgramNames`]) and `taken` does not hold, with `n` moved past it. Every place that makes
/// up a name for a printed type picks it here. A run of names the program binds is stepped
/// over at once, so a pick costs `O(1)` beside the names `taken` holds, however many names the
/// program binds.
pub fn fresh_name<S>(names: Names, n: &mut usize, taken: impl Fn(&str) -> bool) -> S
where
    S: From<&'static str> + From<String> + std::ops::Deref<Target = str>,
{
    HELD.with_borrow(|held| {
        loop {
            match (names, *n) {
                (Names::Variables, 0..4) if held.letters[*n] => {
                    *n += 1;
                    continue;
                }
                (Names::Variables, 0..4) => {}
                _ => {
                    if let Some(&end) = held.ends.get(n) {
                        *n = end;
                    }
                }
            }
            let name: S = names.nth(*n);
            *n += 1;
            if !taken(&name) {
                break name;
            }
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn picks(names: Names, k: usize, taken: impl Fn(&str) -> bool) -> Vec<String> {
        let mut n = 0;
        (0..k).map(|_| fresh_name(names, &mut n, &taken)).collect()
    }

    #[test]
    fn with_nothing_held_the_sequences_are_as_before() {
        assert_eq!(
            picks(Names::Variables, 6, |_| false),
            ["T", "U", "V", "W", "T5", "T6"]
        );
        assert_eq!(picks(Names::Definitions, 3, |_| false), ["T1", "T2", "T3"]);
    }

    #[test]
    fn the_program_names_are_skipped_in_both_sequences() {
        let _names = ProgramNames::hold(["T", "V", "T2", "T3", "T5", "T05", "T0", "x"]);
        assert_eq!(
            picks(Names::Variables, 4, |_| false),
            ["U", "W", "T6", "T7"]
        );
        assert_eq!(
            picks(Names::Definitions, 4, |_| false),
            ["T1", "T4", "T6", "T7"]
        );
        // A name the caller holds is skipped too: a variable `T6` the message writes.
        assert_eq!(
            picks(Names::Definitions, 3, |w| w == "T6"),
            ["T1", "T4", "T7"]
        );
    }

    #[test]
    fn a_hold_inside_another_gives_the_outer_names_back() {
        let _outer = ProgramNames::hold(["T1"]);
        {
            let _inner = ProgramNames::hold(["T2"]);
            assert_eq!(picks(Names::Definitions, 2, |_| false), ["T1", "T3"]);
        }
        assert_eq!(picks(Names::Definitions, 2, |_| false), ["T2", "T3"]);
    }
}
