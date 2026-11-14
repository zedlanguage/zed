//! Why the solver refuses a question ([`Refusal`]), how a refusal is written for the program's
//! author, and the shape of [`project_each`](super::project_each)'s result ([`Each`]).
//!
//! These are kept in a file below both `presburger.rs` and `row_sums.rs`, which both name them,
//! since a name of `presburger.rs` from `row_sums.rs` would put the two files in an import
//! cycle, which Zed forbids between files (DESIGN.md sec:units; ZED_PORT_GAPS.md gap 10). The
//! parent re-exports every public name, so `presburger::Refusal` and the rest are unchanged.

use std::collections::HashSet;
use std::fmt;
use std::sync::Arc;

use zedc_lattice::interval::IntervalSet;

/// Why a question lies outside the fragment the solver decides. Each is reported in its own
/// words (sec:diagnostics), and each but [`Refusal::Work`] is a property of the system's
/// shape, never of its size or of the names of its variables; narrowing keeps the written
/// constraint, which is sound.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Refusal {
    /// Every elimination of a variable would enlarge the system, which has four variables or
    /// more and is not of the form `±x ± y + k >= 0`; no row is below zero over the box its
    /// bounds give its variables, and each of the five points of that box that `box_point`
    /// tries misses some row. A system with three variables left is decided by `live3`.
    Growth,
    /// The integer points could lie only in a splinter whose own dark eliminations leave as many
    /// live variables as the one it came from, four or more: splitting it again need not end.
    Shadows,
    /// The search through the disjunctions found no point and removed no disjunct.
    Disjuncts,
    /// The next step would choose among variables, or equalities, that no structure of the
    /// rows tells apart and that share a row, so the choice would fall to their names; the
    /// stages that need no choice decided nothing.
    Tie(Arc<Tie>),
    /// The formula has disjunctions left after every disjunct with no point is removed, and
    /// atoms that no structure tells apart, so the search through the disjunctions would go in
    /// an order chosen by name; the one choice of disjuncts that the structure fixes, when
    /// there is one, has no point with the rest. The rows of the [`Tie`] are the disjunctions left.
    Unordered(Arc<Tie>),
    /// The values of the variables asked were to be found by adding up, row by row, the values
    /// their alternatives allow (module `row_sums`), and that work passed its measured limit,
    /// `row_sums::JOIN_LIMIT` (about 250 ms). The one refusal by size: the author refuses a
    /// question that provably blows up, by a measured limit (P196, as A99 does), rather than
    /// answer with the solver's coarser set (P197; PRES-switchover-not-race).
    Work,
}

/// The variables of a [`Refusal::Tie`], and the rows they share, written over the variables
/// left at that step: a variable the solver made up for an equality or a splinter is `t1`,
/// `t2` and so on, and a variable standing for several whose columns are multiples of one
/// column is written as their sum.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Tie {
    /// The variables, as written.
    pub vars: Vec<String>,
    /// The rows they share, each `... >= 0` or `... == 0`.
    pub rows: Vec<String>,
}

/// The sentence that closes a refusal of a question whose answer nothing stands in for: how
/// far the search got ([`Refusal::closed_by`] closes the others).
const STOPPED: &str = "The checker stopped there, with no values found and none ruled out";

/// The opening of a refusal met while removing variables.
const REMOVING: &str = "to find whole numbers that meet these conditions, the checker removes \
                        one variable at a time, putting in place of the conditions on it \
                        conditions on the variables left";

/// The opening of a refusal met while choosing among alternatives.
const ALTERNATIVES: &str = "the conditions hold alternatives, where one of several cases is \
                            enough (from `||`, from `!=`, which holds when either side is the \
                            larger, or from a negated `&&`), and the checker looks for a \
                            choice of one case from each alternative that can hold with the rest";

/// `xs`, each in backquotes, joined by commas.
fn quoted(xs: &[String]) -> String {
    xs.iter()
        .map(|x| format!("`{x}`"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// "the condition `a`" or "the conditions `a`, `b`".
fn conditions(rows: &[String]) -> String {
    let s = if rows.len() == 1 { "" } else { "s" };
    format!("the condition{s} {}", quoted(rows))
}

/// Conditions whose question was refused, as the program wrote them: what the repairs of
/// [`Refusal::repairs`] rewrite. The checker's front end has the program's text and gives a
/// function's; a scope of the reduced product, built from kernel terms with no text, gives its
/// conditions as printed.
pub struct Written<'a> {
    /// What the conditions belong to, as the repairs name it: `` `ok` ``, `the test`.
    pub what: &'a str,
    /// What comes before the conditions: `ok(x, y) = ` for a function, empty for a test.
    pub head: &'a str,
    /// What comes after them: `;` for a function, ` }` for one that ends its block with them,
    /// empty for a test.
    pub tail: &'a str,
    /// The function the split repair divides; `None` for a test.
    pub split: Option<Split<'a>>,
    /// The operands of the conditions' outermost `&&`, in order, as written.
    pub conjuncts: &'a [&'a str],
    /// The variables of the conditions a program can fix, in written order.
    pub names: &'a [&'a str],
}

/// A function whose conditions the split repair divides between two new functions.
pub struct Split<'a> {
    /// Its name.
    pub name: &'a str,
    /// What follows its name in [`Written::head`]: `(x, y) = ` for `ok(x, y) = `.
    pub rest: &'a str,
    /// The names of the two new functions, which the program does not use:
    /// [`free_names`] of the name.
    pub into: [&'a str; 2],
}

/// The two names the split repair of function `f` gives its new functions: `{f}1` and `{f}2`,
/// or, where `taken` holds either, `f` with the two least numbers from 1 up that `taken` does
/// not hold, so a program that already has `ok1` gets `ok2` and `ok3`. `taken` holds every
/// name the program writes, so a new top-level function shadows none of its names and none of
/// its local names hides one at a call. The names of units that import the program are not
/// counted: an importer reaches the program's names only by writing them, in a qualified use
/// or a selective import, so its own `ok1` and a new `pricing.ok1` stay two names (DESIGN.md
/// sec:units, sec:diagnostics), and the repair depends on the unit's text alone, the same
/// whether it is checked alone or in a build. Each candidate is one lookup in `taken`, and at most
/// two more are tried than `taken` holds names of the form `f` and a number.
pub fn free_names(f: &str, taken: &HashSet<&str>) -> [String; 2] {
    let mut k = 0usize;
    let mut next = || loop {
        k += 1;
        let candidate = format!("{f}{k}");
        if !taken.contains(candidate.as_str()) {
            return candidate;
        }
    };
    [next(), next()]
}

/// The words of `text` that name variables, each once, in the order they first occur: a word
/// not followed by `(`, which calls a function, and not an operator or literal word. O(the
/// length of `text`).
pub fn names_in(text: &str) -> Vec<&str> {
    const WORDS: [&str; 10] = [
        "mod", "div", "true", "false", "not", "in", "is", "as", "else", "with",
    ];
    let b = text.as_bytes();
    let ident = |c: u8| c.is_ascii_alphanumeric() || c == b'_';
    let mut out: Vec<&str> = Vec::new();
    let mut seen: HashSet<&str> = HashSet::new();
    let mut i = 0;
    while i < b.len() {
        if ident(b[i]) && (i == 0 || !ident(b[i - 1])) {
            let start = i;
            while i < b.len() && ident(b[i]) {
                i += 1;
            }
            let w = &text[start..i];
            let call = text[i..].trim_start().starts_with('(');
            if !b[start].is_ascii_digit() && !call && !WORDS.contains(&w) && seen.insert(w) {
                out.push(w);
            }
        } else {
            i += 1;
        }
    }
    out
}

impl Refusal {
    /// The repairs of this refusal, each `repair: ` and the program's conditions `w` rewritten,
    /// checkable first: a value stated for one variable, an order stated between two variables
    /// the refusal found alike, and the conditions split between two functions. Each ended the
    /// refusal of its kind in `l01_38_presburger::checker`; a repair the data does not support
    /// (an order with fewer than two alike variables the program wrote, a split of one
    /// condition) is left out. A law with a proof would end each too, from step L15 on, and is
    /// not offered before it.
    pub fn repairs(&self, w: &Written<'_>) -> Vec<String> {
        let what = w.what;
        let body = w.conjuncts.join(" && ");
        let names: HashSet<&str> = w.names.iter().copied().collect();
        let tied: Vec<&str> = match self {
            Refusal::Tie(t) | Refusal::Unordered(t) => t
                .vars
                .iter()
                .map(String::as_str)
                .filter(|v| names.contains(v))
                .collect(),
            _ => Vec::new(),
        };
        let mut out = Vec::new();
        if let Some(v) = tied.first().or(w.names.first()) {
            out.push(format!(
                "repair: if `{v}` is meant to take only one value in {what}, state that value, and \
                 the checker removes `{v}` from the question: `{}{v} == 0 && {body}{}`, with the \
                 value in place of `0`",
                w.head, w.tail
            ));
        }
        if let [a, b, ..] = tied[..] {
            out.push(format!(
                "repair: if `{a} <= {b}` is meant to hold in {what}, state it, and the checker \
                 can tell `{a}` and `{b}` apart: `{}{a} <= {b} && {body}{}`",
                w.head, w.tail
            ));
        }
        if let (Some(split), true) = (&w.split, w.conjuncts.len() >= 2) {
            // Alike variables go to separate functions, which ends their tie; with none, the
            // conditions are halved.
            let (first, second): (Vec<&str>, Vec<&str>) = match tied[..] {
                [a, b, ..] => w.conjuncts.iter().partition(|c| {
                    let n = names_in(c);
                    n.contains(&a) && !n.contains(&b)
                }),
                _ => {
                    let (x, y) = w.conjuncts.split_at(w.conjuncts.len().div_ceil(2));
                    (x.to_vec(), y.to_vec())
                }
            };
            if !first.is_empty() && !second.is_empty() {
                // The head is the name and `rest`, so the new names replace the name's token
                // and nothing else the head writes.
                let (f, rest, [a, b]) = (split.name, split.rest, split.into);
                out.push(format!(
                    "repair: split the conditions between two functions, `{a}` and `{b}`, \
                     and where `{f}` is called, call `{a}(…) && {b}(…)` with the same \
                     arguments; each asks a smaller question, and a function whose body joins \
                     them asks the joined question again: `{a}{rest}{}{}` and `{b}{rest}{}{}`",
                    first.join(" && "),
                    w.tail,
                    second.join(" && "),
                    w.tail
                ));
            }
        }
        out
    }
}

impl Refusal {
    /// This refusal's reason, what the checker was working out and why it stopped, closed by
    /// the sentence `last`, which says what the checker kept: for a refused projection, the
    /// bounds it kept (DESIGN step L1.38), where [`Refusal`]'s own closing sentence, that it
    /// found no values and ruled none out, would be false.
    pub fn closed_by<'a>(&'a self, last: &'a str) -> impl fmt::Display + 'a {
        Closed { why: self, last }
    }
}

impl Refusal {
    /// This refusal's reason as a program with the variables `names` reads it, where `moduli`
    /// are the divisors of the remainders and quotients its conditions take. With one
    /// variable, the variables the shadows reason counts are the checker's own, one for each
    /// remainder and quotient, and the reason names the moduli they come from (I4.11); every
    /// other reason is [`Refusal`]'s own. O(the moduli's text).
    pub fn said(&self, names: &[&str], moduli: &[&str]) -> String {
        match (self, names, moduli.split_last()) {
            (Refusal::Shadows, [x], Some((last, rest))) => {
                let by = if rest.is_empty() {
                    last.to_string()
                } else {
                    format!("{} and {last}", rest.join(", "))
                };
                format!(
                    "{REMOVING}. The program has one variable, `{x}`, and the conditions read it \
                     through its remainders and quotients by {by}; the checker gives each \
                     remainder and quotient a variable of its own. Where the values a variable \
                     can take have gaps, it splits the conditions into cases, one for each gap. \
                     Here the only values could lie in a case that would have to be split again \
                     with as many of the checker's variables left as before, so the splitting \
                     need not end. {STOPPED}"
                )
            }
            _ => self.to_string(),
        }
    }
}

/// A refusal's reason and the sentence that closes it ([`Refusal::closed_by`]).
struct Closed<'a> {
    why: &'a Refusal,
    last: &'a str,
}

impl fmt::Display for Refusal {
    /// The reason, closed by the sentence that the checker found no values and ruled none out.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.closed_by(STOPPED).fmt(f)
    }
}

impl fmt::Display for Closed<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.why {
            Refusal::Growth => write!(
                f,
                "{REMOVING}. Here four variables or more are left, and removing any one of \
                 them would leave more conditions than there are now, so the work could grow \
                 without end."
            ),
            Refusal::Shadows => write!(
                f,
                "{REMOVING}. Where the values a variable can take have gaps, it splits the \
                 conditions into cases, one for each gap. Here the only values could lie in a \
                 case that would have to be split again with as many variables left as before, \
                 so the splitting need not end."
            ),
            Refusal::Disjuncts => write!(
                f,
                "{ALTERNATIVES}; no choice it tried has values that meet every condition, \
                 and it could rule out none of the cases."
            ),
            Refusal::Tie(t) => write!(
                f,
                "{REMOVING}. Its next step must choose among the variables {}, which occur \
                 alike in the conditions (with the same coefficients, in conditions that are \
                 alike) and share {}, so only their names could order them, and the checker \
                 never lets a name change an answer.",
                quoted(&t.vars),
                conditions(&t.rows)
            ),
            Refusal::Work => write!(
                f,
                "{ALTERNATIVES}. To find every value each variable can take, it adds up the \
                 values the cases allow, one condition at a time. Here the sums take so many \
                 different values that this would take longer than the checker allows (about \
                 a quarter of a second)."
            ),
            Refusal::Unordered(t) => write!(
                f,
                "{ALTERNATIVES}. After every case that cannot hold is removed, {} {} left, \
                 and the variables {} occur alike in them (with the same coefficients, in \
                 conditions that are alike), so only their names could order the search, and \
                 the checker never lets a name change an answer; the one choice the conditions \
                 alone fix, if there is one, has no values that meet the rest.",
                if t.rows.len() == 1 {
                    format!("the alternative {}", quoted(&t.rows))
                } else {
                    format!("the alternatives {}", quoted(&t.rows))
                },
                if t.rows.len() == 1 { "is" } else { "are" },
                quoted(&t.vars)
            ),
        }?;
        write!(f, " {}", self.last)
    }
}

/// The projections of [`super::project_each`], one for each symbol, and the causes for which a
/// disjunction was left out of them.
pub type Each = (Vec<Result<IntervalSet, Refusal>>, Vec<Refusal>);
