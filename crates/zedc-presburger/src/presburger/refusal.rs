//! Why the solver refuses a question ([`Refusal`]), how a refusal is written for the program's
//! author, and the shape of the results of [`project_each`](super::project_each) ([`Each`])
//! and [`project`](super::project) ([`One`]).
//!
//! These are kept in a file below both `presburger.rs` and `row_sums.rs`, which both name them,
//! since a name of `presburger.rs` from `row_sums.rs` would put the two files in an import
//! cycle, which Zed forbids between files (DESIGN.md sec:units; ZED_PORT_GAPS.md gap 10). The
//! parent re-exports every public name, so `presburger::Refusal` and the rest are unchanged.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::Arc;

use zed_kernel::text::ident;
use zed_kernel::text::prose::{and_list, plural};
use zedc_lattice::interval::{End, IntervalSet, Num};
use zedc_lattice::lattice::{Congruence, Lattice};

/// Why a question lies outside the fragment the solver decides. Each is reported in its own
/// words (sec:diagnostics), and each but [`Refusal::Work`] and [`Refusal::Questions`] is a
/// property of the system's shape, never of its size or of the names of its variables;
/// narrowing keeps the written constraint, which is sound.
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
    /// `row_sums::JOIN_LIMIT`, a count of work units (measured once as about 250 ms, so the
    /// count, not the time, decides on every machine). The one refusal by size: the author
    /// refuses a question that provably blows up, by a measured limit (P196, as A99 does),
    /// rather than answer with the solver's coarser set (P197; PRES-switchover-not-race).
    Work,
    /// The values of a variable were to be found exactly by asking, one range of values at a
    /// time, whether some point of the formula lies there (module `exact`), and that work,
    /// the solver's work for each question included, passed its measured limit,
    /// `meter::EXACT_LIMIT`, a count of work units (measured once as about 250 ms). A refusal
    /// by size, as [`Refusal::Work`] is (PRES-pugh-work-budget). The message says "more work
    /// than the checker allows" and names no time, since load never changes the verdict.
    Questions,
    /// The values of a variable have gaps that repeat without end (`x == 2 * y` with `y`
    /// unbounded gives the even numbers), which a set of ranges cannot hold (module `exact`).
    Repeats,
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
    let s = plural(&rows.len());
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
    let free = |n: &str| !taken.contains(n);
    let (k, first) = ident::numbered(f, 1, free);
    [first, ident::numbered(f, k + 1, free).1]
}

/// The words of `text` that name variables, each once, in the order they first occur: a name
/// as the grammar reads it, prime included (`x'`, [`ident::names`]), not followed by `(`,
/// which calls a function, and not an operator or literal word. O(the length of `text`).
pub fn names_in(text: &str) -> Vec<&str> {
    const WORDS: [&str; 10] = [
        "mod", "div", "true", "false", "not", "in", "is", "as", "else", "with",
    ];
    let mut out: Vec<&str> = Vec::new();
    let mut seen: HashSet<&str> = HashSet::new();
    for (at, w) in ident::names(text) {
        let call = text[at + w.len()..].trim_start().starts_with('(');
        if !call && !WORDS.contains(&w) && seen.insert(w) {
            out.push(w);
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
        match (self, names, moduli) {
            (Refusal::Shadows, [x], [_, ..]) => {
                let by = and_list(moduli);
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
                 different values that this would take more work than the checker allows."
            ),
            Refusal::Questions => write!(
                f,
                "to find exactly which values each variable can take, the checker asks, one \
                 range of values at a time, whether some values there meet every condition. \
                 Here those questions would take more work than the checker allows."
            ),
            Refusal::Repeats => write!(
                f,
                "to find exactly which values each variable can take, the checker writes them \
                 as ranges. Here the values have gaps that repeat without end, as the even \
                 numbers do, which no list of ranges can hold."
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

/// The projection of [`super::project`] onto one symbol, and the causes for which a
/// disjunction was left out of it.
pub type One = (IntervalSet, Vec<Refusal>);

/// A set of integers written as ranges met with one congruence class: the values of `ranges`
/// that lie in `class`. The set the exact projection gives where its values are every second
/// (or every `m`-th) value of some ranges, as the odd values of `-b..=b`, which ranges alone
/// hold only as one range for each value (PRES-interval-strided-piece).
///
/// Kept in one form for each set ([`Classed::new`]), so that two equal sets compare equal:
/// the class is the least one holding the set (its modulus the gcd of the differences of its
/// members; every integer where that is 1 or the set has one member or none), and the ranges
/// are its maximal runs of members one modulus apart, each from its least member to its
/// greatest. Proof that this is a function of the set alone: the gcd of the differences of a
/// set's members and the residue of any member modulo it depend on the members only, and so
/// do the maximal runs. A class other than every integer is kept only with finite ranges: a
/// set with an infinite range holds two consecutive integers, so its gcd is 1.
// Complexity tradeoff: naive version, every value of the class within the ranges listed as a
// range of its own (`exact::block_set` before PRES-interval-strided-piece), O(v) pieces for v
// values, for every set built and every set read; used: the ranges and the class, O(p) for p
// ranges (one in the benchmarks of `l01_39_scope_relations::xst::s4::bench`), with the values
// listed only where a reader asks for the plain set ([`Classed::met`]), O(v) there, or a join
// meets two different classes ([`Classed::join`]). Design B of the plan row, scored against a
// strided piece inside `IntervalSet` (no one form for equality, every reader of its pieces
// expanding it again).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Classed {
    /// The ranges, each from a member of the set to a member.
    pub ranges: IntervalSet,
    /// The class; every integer (modulus 1) for a set of ranges alone.
    pub class: Congruence,
}

impl Classed {
    /// The set `set`, in the form of [`Classed`]: O(p) for p ranges.
    pub fn plain(set: IntervalSet) -> Classed {
        Classed::new(set, Congruence::top())
    }

    /// The values of `ranges` in `class`, in the one form of [`Classed`]. `class` other than
    /// every integer must come with finite ranges (or none). O(p log p) for p ranges.
    pub fn new(ranges: IntervalSet, class: Congruence) -> Classed {
        let empty = || Classed {
            ranges: IntervalSet::empty(),
            class: Congruence::top(),
        };
        let (m, r) = match class {
            Congruence::Bottom => return empty(),
            Congruence::Class { modulus, residue } => (modulus, residue),
        };
        if m.is_zero() {
            // One value, `r`.
            return if ranges.contains_end(&End::Fin(r.clone())) {
                Classed::plain_unchecked(IntervalSet::point(r))
            } else {
                empty()
            };
        }
        // Each range's ends moved in to the nearest members of the class (as
        // `revision::reduce_congruence`), so every end is a member.
        let reduced: Vec<(End, End)> = if m == Num::ONE {
            ranges.into_pieces()
        } else {
            (ranges.pieces())
                .filter_map(|(lo, hi)| {
                    let (End::Fin(lo), End::Fin(hi)) = (lo, hi) else {
                        unreachable!("a class other than every integer comes with finite ranges")
                    };
                    let lo = lo + &(&r - lo).rem_euclid(&m);
                    let hi = hi - &(hi - &r).rem_euclid(&m);
                    (lo <= hi).then_some((End::Fin(lo), End::Fin(hi)))
                })
                .collect()
        };
        // The gcd `g` of the differences of the members from the least one, `a0`: every member
        // is `a0 + (lo_i - a0) + k m` for a range `[lo_i, hi_i]`, so `g` is the gcd of the
        // `lo_i - a0` and, where a range holds two members, of `m`.
        let Some((End::Fin(a0), _)) = reduced.first().cloned() else {
            return match reduced.first() {
                None => empty(),
                // An infinite range holds two consecutive integers: every integer.
                Some(_) => Classed::plain_unchecked(IntervalSet::from_pieces(reduced)),
            };
        };
        let mut g = Num::ZERO;
        for (lo, hi) in &reduced {
            let (End::Fin(lo), End::Fin(hi)) = (lo, hi) else {
                // An infinite end: two consecutive integers, so `m` is 1 and `g` would be 1.
                return Classed::plain_unchecked(IntervalSet::from_pieces(reduced));
            };
            if hi > lo {
                g = g.gcd(&m);
            }
            g = g.gcd(&(lo - &a0));
        }
        if g.is_zero() || g == Num::ONE {
            // One member, or every integer: the ranges alone.
            return Classed::plain_unchecked(IntervalSet::from_pieces(reduced));
        }
        // Every member lies in `a0 mod g`; the maximal runs of members `g` apart. With `g`
        // above `m` every range holds one member, so the runs join single values; with `g`
        // equal to `m`, ranges whose ends are `m` apart.
        let mut runs: Vec<(Num, Num)> = Vec::new();
        for (lo, hi) in reduced {
            let (End::Fin(lo), End::Fin(hi)) = (lo, hi) else {
                unreachable!("every range is finite here, shown above")
            };
            match runs.last_mut() {
                Some((_, end)) if (&lo - &*end) == g => *end = hi,
                _ => runs.push((lo, hi)),
            }
        }
        let class = Congruence::new(g.clone(), a0);
        Classed {
            ranges: IntervalSet::from_pieces(
                (runs.into_iter())
                    .map(|(lo, hi)| (End::Fin(lo), End::Fin(hi)))
                    .collect(),
            ),
            class,
        }
    }

    /// `set` with every integer as its class, `set` known to be in the one form already.
    fn plain_unchecked(set: IntervalSet) -> Classed {
        Classed {
            ranges: set,
            class: Congruence::top(),
        }
    }

    /// Whether the set has no value.
    pub fn is_empty(&self) -> bool {
        self.ranges.is_empty()
    }

    /// The modulus of the class and its residue, where it is not every integer.
    pub fn strided(&self) -> Option<(&Num, &Num)> {
        match &self.class {
            Congruence::Class { modulus, residue } if *modulus > Num::ONE => {
                Some((modulus, residue))
            }
            _ => None,
        }
    }

    /// The set as ranges alone, each value of a class other than every integer listed as a
    /// range of its own: the set [`super::project_each`] gave before the class was kept.
    /// O(v) for v values.
    pub fn met(&self) -> IntervalSet {
        let Some((m, _)) = self.strided() else {
            return self.ranges.clone();
        };
        let mut pieces = Vec::new();
        for (lo, hi) in self.ranges.pieces() {
            let (End::Fin(lo), End::Fin(hi)) = (lo, hi) else {
                unreachable!("a class other than every integer comes with finite ranges")
            };
            let mut v = lo.clone();
            while &v <= hi {
                pieces.push((End::Fin(v.clone()), End::Fin(v.clone())));
                v = &v + m;
            }
        }
        IntervalSet::from_pieces(pieces)
    }

    /// The union. With one class, the union of the ranges in it; else the two sets listed
    /// ([`Classed::met`]) and joined.
    // Complexity tradeoff: the union of two different classes is in general no one class
    // within ranges (the odd values and the multiples of 4), so it is listed, O(v) for v
    // values, as every union was before PRES-interval-strided-piece; one class costs O(p).
    pub fn join(&self, other: &Classed) -> Classed {
        if self.is_empty() {
            return other.clone();
        }
        if other.is_empty() {
            return self.clone();
        }
        if self.class == other.class {
            return Classed::new(self.ranges.join(&other.ranges), self.class.clone());
        }
        Classed::plain(self.met().join(&other.met()))
    }

    /// The union of `sets`, as [`Classed::join`] of each in turn gives it, with the ranges of
    /// each class gathered and made one set at once.
    // Complexity tradeoff: naive version, `set = set.join(&p)` for each of k sets; a join of
    // one class is `Classed::new` over the whole union, O(p) for p ranges so far, so k sets of
    // one range each cost O(k^2) (the union of a disjunction of k blocks, `exact::blocks_set`,
    // before PRES-cover-moduli-two-disjunctions). Used: the ranges of each class listed, then
    // sorted and merged once (`IntervalSet::from_pieces`, O(P log P) for P ranges in all, O(P)
    // bytes) and `Classed::new` once per class, O(P log P) in all; the sets of different classes
    // are then joined as before, listed, O(c·v) for c classes and v values, the cost
    // `Classed::join` already has for two classes. The groups are kept in the order their
    // class first came, so the answer does not hang on a hash order.
    pub fn join_all(sets: impl IntoIterator<Item = Classed>) -> Classed {
        let mut at: HashMap<Congruence, usize> = HashMap::new();
        let mut groups: Vec<(Congruence, Vec<(End, End)>)> = Vec::new();
        for c in sets {
            if c.is_empty() {
                continue;
            }
            let i = *at.entry(c.class.clone()).or_insert_with(|| {
                groups.push((c.class.clone(), Vec::new()));
                groups.len() - 1
            });
            groups[i].1.extend(c.ranges.into_pieces());
        }
        groups
            .into_iter()
            .map(|(class, pieces)| Classed::new(IntervalSet::from_pieces(pieces), class))
            .fold(Classed::plain(IntervalSet::empty()), |set, c| set.join(&c))
    }

    /// The intersection: the ranges met, in the meet of the classes (by the Chinese remainder
    /// theorem, `Congruence::meet`), exact, as `(A ∩ C) ∩ (B ∩ D) = (A ∩ B) ∩ (C ∩ D)`.
    pub fn meet(&self, other: &Classed) -> Classed {
        Classed::new(
            self.ranges.meet(&other.ranges),
            self.class.meet(&other.class),
        )
    }

    /// The hull: every end of the ranges is a member.
    pub fn hull(&self) -> IntervalSet {
        self.ranges.hull()
    }

    /// The number of values, `u64::MAX` for a set with no end or past `u64`. O(p) for p
    /// ranges.
    pub fn count(&self) -> u64 {
        let m = self.strided().map_or(Num::ONE, |(m, _)| m.clone());
        let mut n: u64 = 0;
        for (lo, hi) in self.ranges.pieces() {
            let (End::Fin(lo), End::Fin(hi)) = (lo, hi) else {
                return u64::MAX;
            };
            // `lo` and `hi` are members, so the range holds `(hi - lo) / m + 1` of them.
            let k = (&(hi - lo).div_floor(&m) + &Num::ONE).to_i128();
            let k = k.and_then(|k| u64::try_from(k).ok()).unwrap_or(u64::MAX);
            n = n.saturating_add(k);
        }
        n
    }

    /// The number of ranges of the plain set ([`Classed::met`]), counted, not listed: each
    /// value with a class other than every integer is a range of its own (no two members are
    /// next to each other), else the ranges, maximal in the one form. O(p) for p ranges.
    pub fn listed_len(&self) -> u64 {
        if self.strided().is_some() {
            self.count()
        } else {
            self.ranges.len() as u64
        }
    }

    /// The values of `self` not in `other`, exact. With `A = R ∩ C` and `B = S ∩ D`,
    /// `A \ B = ((R \ S) ∩ C) ∪ ((R ∩ S) ∩ (C \ D))`; `C \ D` is `C` where the classes do not
    /// meet, nothing where `C` lies in `D`, and the one class of `C` left where `D` takes one
    /// of the two classes modulo `lcm(m, k)` into which it cuts `C` (as the even values left
    /// of every integer once the odd ones are taken). Where `C \ D` is more classes than one,
    /// the sets are listed ([`Classed::met`]) and their difference taken.
    // Complexity tradeoff: naive version, both sets listed and subtracted, O(v) for v values,
    // as `projection::Held::push` did before PRES-interval-strided-piece; used: the ranges and
    // the classes, O(p log p) for p ranges, in the cases above, which are the ones the exact
    // projection of a stride makes (a range with the odd values taken, then the even ones),
    // and the listed difference in every other, O(v) as before.
    pub fn minus(&self, other: &Classed) -> Classed {
        if self.is_empty() || other.is_empty() {
            return self.clone();
        }
        let met = self.class.meet(&other.class);
        // `C \ D`, where it is one class or none (`Bottom`).
        let rest = if met == Congruence::Bottom {
            Some(self.class.clone())
        } else if met == self.class {
            Some(Congruence::Bottom)
        } else {
            match (&self.class, &met) {
                (
                    Congruence::Class {
                        modulus: m,
                        residue: a,
                    },
                    Congruence::Class { modulus: l, .. },
                ) if !m.is_zero() && *l == m * &Num::from(2) => {
                    // `C` is two classes modulo `l`; `D` holds the one `met`, so `C \ D` is
                    // the other, `a + m` or `a` modulo `l`, whichever is not `met`.
                    let shifted = Congruence::new(l.clone(), a + m);
                    Some(if shifted == met {
                        Congruence::new(l.clone(), a.clone())
                    } else {
                        shifted
                    })
                }
                _ => None,
            }
        };
        let Some(rest) = rest else {
            return Classed::plain(self.met().minus(&other.met()));
        };
        // Complexity tradeoff: naive version, always run `minus` and `meet` over all p pieces,
        // O(p) allocations when `self.ranges` and `other.ranges` share the same `Arc<Node>`
        // (common in `Held::push` when the projected stride covers the full finite goal); used:
        // O(1) equality check (`Arc::ptr_eq` inside `IntervalSet::eq`) skips both tree walks.
        if self.ranges == other.ranges {
            return if rest == Congruence::Bottom {
                Classed::plain(IntervalSet::empty())
            } else {
                Classed::new(self.ranges.clone(), rest)
            };
        }
        let outside = Classed::new(self.ranges.minus(&other.ranges), self.class.clone());
        if rest == Congruence::Bottom {
            return outside;
        }
        let inside = self.ranges.meet(&other.ranges);
        // `rest` other than every integer needs finite ranges: `other`'s class is not every
        // integer (else `C` would lie in it), so `other`'s ranges, and their meet, are finite.
        outside.join(&Classed::new(inside, rest))
    }
}

/// [`Each`] with each set [`Classed`]: the answer of [`super::project_each_classed`].
#[derive(Clone, PartialEq, Debug)]
pub struct EachClassed {
    /// Each symbol's set, or its refusal.
    pub sets: Vec<Result<Classed, Refusal>>,
    /// The causes for which a disjunction was left out of them.
    pub causes: Vec<Refusal>,
}

impl EachClassed {
    /// The sets of `each`, with every integer as each one's class.
    pub fn plain(each: Each) -> EachClassed {
        let (sets, causes) = each;
        EachClassed {
            sets: (sets.into_iter()).map(|r| r.map(Classed::plain)).collect(),
            causes,
        }
    }

    /// The sets as ranges alone ([`Classed::met`]): what [`super::project_each`] gave before
    /// the class was kept, for every caller that reads ranges alone.
    pub fn met(&self) -> Each {
        let sets = (self.sets.iter())
            .map(|r| r.as_ref().map(Classed::met).map_err(Clone::clone))
            .collect();
        (sets, self.causes.clone())
    }
}

#[cfg(test)]
mod tests {
    /// A name ends after its one `'` (D3 of REPORT-dryA3): the scan this replaced stopped
    /// before it, so a repair could name `x` where the program wrote `x'`.
    #[test]
    fn names_in_keeps_a_prime_and_skips_calls_words_and_numbers() {
        assert_eq!(
            super::names_in("x' + f(x) - 2y >= x mod 3 && _ < y'"),
            ["x'", "x", "y'"]
        );
    }
}
