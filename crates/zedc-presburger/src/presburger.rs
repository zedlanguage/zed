//! The linear-relation domain (DESIGN.md sec:domains, "linear-integer relations among in-scope
//! keys and cardinalities (Presburger)", and sec:verification, rung 2; step L1.38).
//!
//! A relation is a quantifier-free formula over linear constraints with integer coefficients,
//! `t >= 0` and `t == 0`, joined by `&&`, `||` and `!`. A constraint's term is a sum of atoms,
//! each times a coefficient, plus a constant. An atom is a symbol, the product of two symbols,
//! or an auxiliary variable that names a quotient or a remainder by a constant; the formula
//! that defines an auxiliary variable is kept apart from the body, since it fixes the variable
//! for each value of the symbols, so that negating the body never negates a definition.
//!
//! Satisfiability is decided by the Omega test \[Omega\] on the fragment it settles in a number
//! of steps polynomial in the rows, though not in the bit length of the coefficients, with no
//! budget (docs/thresholds.md, replacement 4), in one loop over a
//! system that holds each set of coefficients once and knows each variable's rows and bound
//! counts, so that a step touches only the rows of the variable it removes. Arithmetic is
//! exact, over unbounded integers. Equalities are solved, with Pugh's symmetric remainder
//! where no coefficient is a unit; two opposite rows that meet become an equality, and so,
//! once, do the rows of a cycle of differences (`Omega::cycles`); a variable
//! bounded on one side only is dropped with its rows. Otherwise the variable whose elimination
//! adds the fewest rows, of those the one that writes the fewest terms, is eliminated, exact
//! eliminations first, and only while the system holds no more terms than it was given: each
//! step removes a variable and the terms never pass the input's count. An elimination is
//! exact when every lower or every upper coefficient of the variable is a unit.
//!
//! Before the parts are split, variables whose columns are multiples of one column are merged
//! into one variable (`quotient`), a unimodular change of variables that keeps every
//! integer point. Two cases are then decided exactly whatever the eliminations would do. Rows
//! over two variables or fewer are decided by counting the integer points under each piece of
//! their upper and lower envelopes ([`zedc_solvers::twovar`]). Rows `±x ± y + k >= 0` are decided by
//! the parity test on the zero-weight cycles of their tight constraint graph
//! ([`zedc_solvers::utvpi`]); once they are shown to have a point, exact eliminations that add terms
//! are allowed, since each keeps that form, and they are taken only when a model is wanted.
//!
//! When every elimination left would add terms, the box test decides what it can, in one pass
//! over the terms and with no linear program: each variable's bounds are tightened once by
//! every row from the bounds its bound rows give (`bounds`); the rows are empty when one of
//! them is below zero at every point of that box, have a point when one of five points of the
//! box holds every row (the point nearest zero, the lower and upper corners, and the two
//! midpoints, `box_point`), are decided completely by [`zedc_solvers::live3`] when three variables are
//! live, and are refused otherwise. At the first inexact elimination
//! the real shadow is tested once (`relaxed_empty`): real-shadow eliminations are taken
//! while each adds no terms, and the box test ends it; empty, it shows the problem empty. From
//! there on the dark shadow is solved, whose points are points of the problem. When it has
//! none, the splinters of each dark elimination are searched [Omega, sec. 2.3]: for each lower
//! row `a·x + l >= 0` of the eliminated `x` and `m` its largest upper coefficient, the problem
//! with `a·x + l == k` for a fresh variable `0 <= k <= (a·m - a - m) / m`. The problem has a
//! point exactly when the dark shadow or a splinter has one. A splinter whose own dark shadow
//! has no point is split again when each of its dark eliminations leaves fewer live variables
//! than the one it came from, and is refused otherwise: that, and a system every elimination of
//! which would add terms and which the box test does not decide, are the refusals ([`Refusal`]),
//! each a property of the system's shape. A
//! satisfiable problem yields a model, built only when one is wanted: each eliminated variable
//! takes the value nearest zero that its bounds allow under the values of the variables
//! eliminated after it.
//!
//! A formula with disjunctions is not split into all its conjunctions. Its top-level
//! constraints are the base; a disjunct whose own top-level constraints meet the base nowhere
//! is removed, and a disjunction with one disjunct left adds it to the base, with its own
//! disjunctions read in the same round, until nothing is removed: each round but the last
//! removes a disjunct, so the rounds are at most the disjuncts. No
//! disjunct left is no point. A point is then sought by taking, for each disjunction in turn,
//! the first disjunct that meets the base with the disjuncts already taken, disjuncts and
//! disjunctions being sorted first, so that the order they are written in changes nothing. Where none does,
//! each disjunct whose addition to the base empties it by the rule above is removed, until
//! none is, and the search runs again; where it fails again, the question is refused. A
//! projection is the meet, over the disjunctions, of the union over each one's disjuncts of
//! the projection of the base with that disjunct; with two disjunctions or more left, each
//! finite bound is then moved inward by halving the step, only where the formula with the
//! value past it is shown empty. Each loop removes a disjunct or halves a step, so each ends.
//!
//! Entailment from premises to a goal is the unsatisfiability of the premises with the negated
//! goal. A product of two symbols is an atom of its own, so the test still decides linear
//! facts; before it, for each product the formulas mention, the premises on its factors are
//! multiplied in pairs, once: a premise on a symbol is a top-level linear inequality of the
//! premises that mentions it, or a bound on the symbol that the linear premises imply.
//!
//! A refused question leaves the relation unused, which is sound: the written constraint is
//! kept, and [`Entailment::Refused`] carries the cause. No compiler path calls [`entails`] yet,
//! and a refusal met in narrowing is kept in `product::Scope::refusals`, which
//! `product::Scope::warnings` reports as one warning each, with the constraint it was asked of.
//! Every integer, written or derived, is unbounded.

use std::cell::{Cell, OnceCell};
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::mem;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};

use imbl::{OrdMap, OrdSet};

use zed_kernel::refine::Refine;
use zed_kernel::value::fresh_id;
use zedc_int::int::Int;
use zedc_lattice::interval::{End, IntervalSet, Num};
use zedc_solvers::linear::{Q, Term};
use zedc_solvers::{live3, twovar, utvpi};

mod deep;
pub mod extend;
mod forced;
mod formula;
mod values;

use forced::{Facts, Forced};
pub use formula::{Atom, Con, Factor, Formula, Id, Lin, Model, Rel, Shared};

/// Why a question lies outside the fragment the solver decides. Each is reported in its own
/// words (sec:diagnostics), and each is a property of the system's shape, never of its size
/// or of the names of its variables; narrowing keeps the written constraint, which is sound.
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
/// its local names hides one at a call. Each candidate is one lookup in `taken`, and at most
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

impl Formula {
    /// `true`.
    pub fn top() -> Formula {
        Formula::And(Shared::new(Vec::new()))
    }

    /// `false`.
    pub fn bottom() -> Formula {
        Formula::Or(Shared::new(Vec::new()))
    }

    /// The conjunction, flattened, `true` dropped and `false` absorbing.
    pub fn and(fs: Vec<Formula>) -> Formula {
        Formula::and_keeping(fs, |_| false)
    }

    /// [`Formula::and`], with each conjunction at an index of `fs` where `keep` holds kept
    /// whole, as one conjunct, and not flattened into this one. The translator keeps the
    /// formula of a name used as an operand of `&&` (`preimage::Tx::chain`), and the
    /// maps of a formula keep a conjunction that was kept in the node they rebuild
    /// (`Formula::rebuild`), so whether a part is kept follows the program and never how
    /// many handles hold it. A kept conjunction is read as flattened by compare, hash
    /// and show (`deep::Flat`), and, each kept part at its first place alone, by
    /// `Formula::conjuncts`, by `Conjuncts::and` and by `Parts::of`.
    // Complexity tradeoff: a kept conjunction is not merged into this one, so the tightening
    // below (one constraint per left-hand side) does not reach the constraints inside it, and a
    // constraint written both inside it and beside it is kept twice. No point is given up and
    // no answer changes; the printed relation lists the named part's constraints as written.
    // Merging would copy the named part's k constraints into each of the d places that use it,
    // O(d k), quadratic in the size of the program when k is about d. Trigger: a name of a
    // conjunction used as an operand of `&&`. Test
    // `l01_39_reduced_product::named_test::arms_of_a_wide_named_conjunction_at_each_tier_take_time_near_linear_in_the_depth`,
    // COMPLEXITY.md S31b. A complete merge needs the conjunction as a persistent map from each
    // left-hand side to its constraint, shared with the named part and extended at each place.
    pub fn and_keeping(fs: Vec<Formula>, keep: impl Fn(usize) -> bool) -> Formula {
        #[cfg(feature = "two-at-a-time")]
        if TWO_AT_A_TIME.get() {
            return before::and_keeping_before(fs, keep);
        }
        let mut j = Joining::new(true);
        for (i, f) in fs.into_iter().enumerate() {
            j.operand(f, keep(i));
        }
        j.finish()
    }

    /// The disjunction, flattened, `false` dropped and `true` absorbing, and `true` when two
    /// disjuncts are complements (`Formula::complementary`).
    pub fn or(fs: Vec<Formula>) -> Formula {
        Formula::or_keeping(fs, |_| false)
    }

    /// [`Formula::or`], with each disjunction at an index of `fs` where `keep` holds kept
    /// whole, as one disjunct, as [`Formula::and_keeping`] keeps a conjunction: the formula of
    /// a name used as an operand of `||`, and a disjunction kept in the node a map rebuilds.
    // Complexity tradeoff: a kept disjunction is not merged into this one, so `complementary`
    // does not find a constraint inside it beside its complement outside it, and the disjunction
    // stays one, which holds at the same points: no answer changes, but each later test splits
    // into its cases. Merging would copy the named part's k disjuncts into each of the d places
    // that use it, O(d k). Trigger: a name of a disjunction used as an operand of `||`. Test
    // `l01_39_reduced_product::named_test::arms_of_a_wide_named_disjunction_at_each_tier_take_time_near_linear_in_the_depth`,
    // COMPLEXITY.md S31b. A complete check needs each kept part's constraints indexed in its
    // node, so that the lookup across it costs O(1) per disjunct.
    pub fn or_keeping(fs: Vec<Formula>, keep: impl Fn(usize) -> bool) -> Formula {
        #[cfg(feature = "two-at-a-time")]
        if TWO_AT_A_TIME.get() {
            return before::or_keeping_before(fs, keep);
        }
        let mut j = Joining::new(false);
        for (i, f) in fs.into_iter().enumerate() {
            j.operand(f, keep(i));
        }
        j.finish()
    }

    /// Whether two of `fs` are each other's complements, so that their disjunction is `true`:
    /// a constraint `c` and `!c`, or `t >= 0` and `s >= 0` with `t + s` a constant of at least
    /// `-1`, since at an integer point `t <= -1` makes `s >= 0`. Each disjunct that is a
    /// constraint or the negation of one is looked up once by its content, so the check costs
    /// the size of the constraints in `fs` and never the depth of a compound disjunct.
    // Complexity tradeoff: a compound `g || !g`, with `g` a conjunction or disjunction, is not
    // found and stays a disjunction. That is sound, since the disjunction holds at every point,
    // but each later test splits into its cases, as before this check (COMPLEXITY.md S20).
    // Looking `g` up by its content hashes it through its whole depth on every `Formula::or`,
    // and `map_cons`, `nnf` and `forget` call `or` once per `Or` node, so a nested or/and
    // formula would cost its size times its depth (62 times the work for 8 times the depth,
    // measured at d = 500 to 4000). The trigger is a disjunct that is not a constraint. Tests
    // in `l01_39_reduced_product::linked`: `a_disjunction_of_a_constraint_and_its_complement_is_true`
    // and `a_nested_or_and_formula_is_built_and_mapped_in_time_near_its_size`. A complete check
    // needs a hash of each formula kept in its node when it is built, so that the lookup costs
    // O(1) per disjunct.
    fn complementary(fs: &[Formula]) -> bool {
        if fs.len() < 2 {
            return false;
        }
        let mut ge: HashMap<&BTreeMap<Atom, Int>, &Int> = HashMap::new();
        let mut whole: std::collections::HashSet<&Con> = std::collections::HashSet::new();
        for f in fs {
            let Formula::Con(c) = f else { continue };
            whole.insert(c);
            if c.rel == Rel::Ge {
                // Of two disjuncts on one term, the weaker, the larger constant, decides.
                let k = ge.entry(&c.lin.terms).or_insert(&c.lin.constant);
                if c.lin.constant > **k {
                    *k = &c.lin.constant;
                }
            }
        }
        fs.iter().any(|f| match f {
            Formula::Not(g) => matches!(&**g, Formula::Con(c) if whole.contains(c)),
            Formula::Con(c) if c.rel == Rel::Ge => {
                let neg: BTreeMap<Atom, Int> =
                    c.lin.terms.iter().map(|(a, k)| (a.clone(), -k)).collect();
                ge.get(&neg)
                    .is_some_and(|k| &c.lin.constant + *k >= Int::from(-1i64))
            }
            _ => false,
        })
    }

    /// The disjunction of `a` and `b` with the conjuncts they share taken out of it, so that
    /// joining two narrowings of one relation does not copy the relation into each disjunct.
    /// Each constraint of the rest of each side is replaced by `rest` of it. When the rest of
    /// one side is one constraint `c`, a conjunct `d` of the other with `c || d` true
    /// (`complements`) is dropped, since `c || (d && r)` is `(c || d) && (c || r)`, that is
    /// `c || r`: the two cases of `!(x >= n && x >= m)`, `x < n` and `x >= n && x < m`, join
    /// to `x < n || x < m`, which bounds `x` on one side alone
    /// ([`crate::conjuncts::Conjuncts::star`]).
    pub fn either(a: &Formula, b: &Formula, rest: &dyn Fn(&Con) -> Formula) -> Formula {
        fn parts(f: &Formula) -> &[Formula] {
            match f {
                Formula::And(gs) => gs,
                g => std::slice::from_ref(g),
            }
        }
        let (pa, pb) = (parts(a), parts(b));
        let in_b: std::collections::HashSet<&Formula> = pb.iter().collect();
        let shared: std::collections::HashSet<&Formula> =
            pa.iter().filter(|g| in_b.contains(g)).collect();
        let oa: Vec<&Formula> = pa.iter().filter(|g| !shared.contains(g)).collect();
        let ob: Vec<&Formula> = pb.iter().filter(|g| !shared.contains(g)).collect();
        let (ca, cb) = (
            (oa.len() == 1).then(|| oa[0]),
            (ob.len() == 1).then(|| ob[0]),
        );
        let left = |o: &[&Formula], other: Option<&Formula>| {
            Formula::and(
                o.iter()
                    .filter(|g| other.is_none_or(|c| !complements(c, g)))
                    .map(|g| g.map_cons(rest))
                    .collect(),
            )
        };
        let (la, lb) = (left(&oa, cb), left(&ob, ca));
        let mut out: Vec<Formula> = pa.iter().filter(|g| shared.contains(g)).cloned().collect();
        out.push(Formula::or(vec![la, lb]));
        Formula::and(out)
    }

    /// The formula with every constraint that mentions `sym`, alone or in a product,
    /// replaced by `true` where it occurs under an even number of negations and by `false`
    /// where under an odd number: a formula implied by `self` that says nothing of `sym`.
    pub fn forget(&self, sym: &Arc<str>) -> Formula {
        // The context is whether the part is under an even number of negations.
        self.fold(
            true,
            |g, pos| pos != matches!(g, Formula::Not(_)),
            |g, pos, parts| match g {
                Formula::Con(c) => {
                    let mentions = c.lin.terms.keys().any(|a| match a {
                        Atom::Sym(n) => n == sym,
                        Atom::Product(x, y) => x.is(sym) || y.is(sym),
                        Atom::Aux(_) => false,
                    });
                    match (mentions, pos) {
                        (false, _) => g.clone(),
                        (true, true) => Formula::top(),
                        (true, false) => Formula::bottom(),
                    }
                }
                Formula::Not(_) | Formula::And(_) | Formula::Or(_) => g.rebuild(parts),
            },
        )
    }

    /// The formula with each constraint `c` replaced by `f(c)`.
    pub fn map_cons(&self, f: &dyn Fn(&Con) -> Formula) -> Formula {
        self.fold(
            (),
            |_, ()| (),
            |g, (), parts| match g {
                Formula::Con(c) => f(c),
                Formula::Not(_) | Formula::And(_) | Formula::Or(_) => g.rebuild(parts),
            },
        )
    }

    /// The node `self` with `parts` in place of its parts, through [`Formula::negate`],
    /// [`Formula::and_keeping`] or [`Formula::or_keeping`]; a constraint has no parts and is
    /// copied. A part in the place of a conjunction kept in a conjunction, or of a disjunction
    /// kept in a disjunction ([`Formula::kept`]), is kept whole.
    fn rebuild(&self, mut parts: Vec<Formula>) -> Formula {
        match self {
            Formula::Con(c) => Formula::Con(c.clone()),
            Formula::Not(_) => Formula::negate(parts.pop().expect("one part")),
            Formula::And(_) => Formula::and_keeping(parts, |i| self.kept(i)),
            Formula::Or(_) => Formula::or_keeping(parts, |i| self.kept(i)),
        }
    }

    /// Whether the part at `i` of `self` is a conjunction kept whole in a conjunction, or a
    /// disjunction kept whole in a disjunction.
    fn kept(&self, i: usize) -> bool {
        match self {
            Formula::And(gs) => matches!(gs[i], Formula::And(_)),
            Formula::Or(gs) => matches!(gs[i], Formula::Or(_)),
            Formula::Con(_) | Formula::Not(_) => false,
        }
    }

    /// The negation, with double negations and constants removed.
    pub fn negate(f: Formula) -> Formula {
        match f {
            Formula::Not(_) => f.into_negated().expect("a negation"),
            Formula::And(ref gs) if gs.is_empty() => Formula::bottom(),
            Formula::Or(ref gs) if gs.is_empty() => Formula::top(),
            g => Formula::Not(Shared::new(g)),
        }
    }

    /// Each constraint, in order, the constraints of a part held in more than one place listed
    /// at its first place alone (`Formula::walk`), so the list is at most the number of
    /// distinct parts and not the size of the formula written out. A caller that needs each
    /// place, for a count or a position, cannot use it. Its callers in the compiler read it as
    /// a set (`atoms`) or as a conjunction (`unbounded`), which a repeated constraint does not
    /// change; `conjuncts::Conjuncts::cons` passes it on, conjunct by conjunct.
    pub fn cons(&self) -> Vec<&Con> {
        let mut out = Vec::new();
        self.walk(&mut |c| out.push(c));
        out
    }

    /// Each atom, in order.
    pub fn atoms(&self) -> BTreeSet<Atom> {
        self.cons()
            .into_iter()
            .flat_map(|c| c.lin.terms.keys().cloned())
            .collect()
    }

    /// Whether the formula holds at `values`; an absent atom is zero, and a product atom is
    /// read as the product of its factors' values.
    /// Each product is read where it is met, so a disjunct that is decided by its first part is
    /// not walked through.
    pub fn holds(&self, values: &Model) -> bool {
        self.holds_as(values)
    }

    /// The top-level conjuncts, with a conjunction kept among them ([`Formula::and_keeping`])
    /// read as flattened into it; a conjunction kept at more than one place is read at its first.
    fn conjuncts(&self) -> Vec<&Formula> {
        let mut out = Vec::new();
        let mut seen = std::collections::HashSet::new();
        let mut stack = vec![self];
        while let Some(g) = stack.pop() {
            match g {
                Formula::And(gs) => {
                    if seen.insert(Id::any(g)) {
                        stack.extend(gs.iter().rev());
                    }
                }
                g => out.push(g),
            }
        }
        out
    }
}

/// Whether `f || g` holds at every integer point, by their forms: a constraint and its
/// negation, or `t >= 0` and `s >= 0` with `t + s` a constant of at least `-1`, as
/// [`Formula::complementary`] finds among many. In time near the constraints' size.
fn complements(f: &Formula, g: &Formula) -> bool {
    match (f, g) {
        (Formula::Con(c), Formula::Not(n)) | (Formula::Not(n), Formula::Con(c)) => {
            matches!(&**n, Formula::Con(d) if d == c)
        }
        (Formula::Con(c), Formula::Con(d)) if c.rel == Rel::Ge && d.rel == Rel::Ge => {
            c.lin.terms.len() == d.lin.terms.len()
                && c.lin
                    .terms
                    .iter()
                    .all(|(a, k)| d.lin.terms.get(a).is_some_and(|j| j == &-k))
                && &c.lin.constant + &d.lin.constant >= Int::from(-1i64)
        }
        _ => false,
    }
}

/// A conjunction or a disjunction made one operand at a time: [`Formula::and_keeping`] and
/// [`Formula::or_keeping`] give it their operands, and the translator gives it each operand of
/// a chain of `&&` or of `||` (`preimage::Tx::chain`), so that a chain of k operands costs
/// O(k log k), and not the O(k²) that making the conjunction of each prefix in turn costs,
/// which copied and tightened the prefix again at each operand (ST-formula-k2).
pub struct Joining {
    /// A conjunction, or a disjunction.
    and: bool,
    /// The parts so far.
    out: Vec<Formula>,
    /// Of a conjunction, the place in `out` of the constraint on each term and comparison.
    at: BTreeMap<(BTreeMap<Atom, Int>, Rel), usize>,
    /// Whether an operand decided the whole: `false` met in a conjunction, two constraints on
    /// one term that cannot both hold, or `true` met in a disjunction.
    decided: bool,
    /// How many parts were added, a constraint merged into an earlier one counted too.
    added: usize,
}

/// Where a [`Joining`] was, from [`Joining::mark`].
#[derive(Clone, Copy)]
pub struct Mark {
    /// The count of parts added, a constraint merged into an earlier one counted too.
    added: usize,
    /// The length of `out`.
    len: usize,
}

impl Joining {
    /// An empty conjunction when `and`, otherwise an empty disjunction.
    pub fn new(and: bool) -> Joining {
        Joining {
            and,
            out: Vec::new(),
            at: BTreeMap::new(),
            decided: false,
            added: 0,
        }
    }

    /// Adds the operand `f`. A part of the joining's own kind is kept whole where `kept`, and
    /// otherwise its parts are added; the empty one of that kind is dropped, and the empty
    /// one of the other kind decides the whole.
    pub fn operand(&mut self, f: Formula, kept: bool) {
        if self.decided {
            return;
        }
        let (own, empty) = match &f {
            Formula::And(gs) => (self.and, gs.is_empty()),
            Formula::Or(gs) => (!self.and, gs.is_empty()),
            Formula::Con(_) | Formula::Not(_) => (false, false),
        };
        match (own, empty) {
            (true, true) => {}
            (false, true) => self.decided = true,
            (true, false) if !kept => {
                for g in f.into_parts().expect("a conjunction or a disjunction") {
                    self.part(g);
                }
            }
            _ => self.part(f),
        }
    }

    /// Adds `g` as a part. Of two constraints in a conjunction on one term and comparison,
    /// the tighter alone, in the place of the first.
    fn part(&mut self, g: Formula) {
        if self.decided {
            return;
        }
        self.added += 1;
        let Formula::Con(c) = &g else {
            self.out.push(g);
            return;
        };
        if !self.and {
            self.out.push(g);
            return;
        }
        let key = (c.lin.terms.clone(), c.rel);
        match self.at.get(&key) {
            Some(&i) => {
                let Formula::Con(old) = &self.out[i] else {
                    unreachable!("a constraint")
                };
                if c.rel == Rel::Ge && c.lin.constant < old.lin.constant {
                    self.out[i] = g;
                } else if c.rel == Rel::Eq && c.lin.constant != old.lin.constant {
                    self.decided = true;
                }
            }
            None => {
                self.at.insert(key, self.out.len());
                self.out.push(g);
            }
        }
    }

    /// Where the joining is now, to pass to [`Joining::close`].
    pub fn mark(&self) -> Mark {
        Mark {
            added: self.added,
            len: self.out.len(),
        }
    }

    /// Ends an inner operand of the chain, one that is itself a `&&` in a chain of `&&` (or a
    /// `||` in one of `||`), whose operands are those added since `mark`. Made apart, such an
    /// operand is the formula `finish` gives, which is its one part where it has one, and
    /// the chain around it adds that part as an operand that is not kept: its parts when it
    /// is of the joining's kind, nothing when it is the empty one of that kind, and the whole
    /// decided when it is the empty one of the other. This does the same, so that the chain
    /// gives the formula of its operands joined two at a time as written.
    pub fn close(&mut self, mark: Mark) {
        // One part added since `mark` and one more in `out`: the operand made apart is that
        // part alone, the last of `out`. A constraint merged into an earlier one is counted in
        // `added` alone, and the operand made apart holds it as a part of its own.
        if self.decided || self.added - mark.added != 1 || self.out.len() - mark.len != 1 {
            return;
        }
        let unwraps = match self.out.last() {
            Some(Formula::And(gs)) => self.and || gs.is_empty(),
            Some(Formula::Or(gs)) => !self.and || gs.is_empty(),
            _ => false,
        };
        if !unwraps {
            return;
        }
        let last = self.out.pop().expect("the last part");
        self.added -= 1;
        self.operand(last, false);
    }

    /// The conjunction or disjunction: its one part where it has one, and `true` for a
    /// disjunction of two complementary parts (`Formula::complementary`).
    pub fn finish(mut self) -> Formula {
        if self.decided {
            return if self.and {
                Formula::bottom()
            } else {
                Formula::top()
            };
        }
        if !self.and && Formula::complementary(&self.out) {
            return Formula::top();
        }
        if self.out.len() == 1 {
            self.out.pop().expect("one")
        } else if self.and {
            Formula::And(Shared::new(self.out))
        } else {
            Formula::Or(Shared::new(self.out))
        }
    }
}

/// A relation: a body, and the definitions of its auxiliary variables, each of which fixes
/// one auxiliary variable for every value of the others.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Relation {
    /// The body.
    pub body: Formula,
    /// The definitions, each an auxiliary variable and the formula that fixes it.
    pub defs: Vec<(u32, String, Formula)>,
}

impl Relation {
    /// The relation `body`, with no auxiliary variable.
    pub fn of(body: Formula) -> Relation {
        Relation {
            body,
            defs: Vec::new(),
        }
    }

    /// The definitions, as one formula.
    pub fn defined(&self) -> Formula {
        Formula::and(self.defs.iter().map(|(_, _, f)| f.clone()).collect())
    }
}

impl fmt::Display for Relation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body)?;
        for (i, (n, what, _)) in self.defs.iter().enumerate() {
            write!(f, "{} q{n} = {what}", if i == 0 { " where" } else { "," })?;
        }
        Ok(())
    }
}

/// The formula of `facts` with each fixed atom replaced by its value, each constraint left with no
/// atom replaced by `true` or `false`, and each conjunction and disjunction rebuilt by
/// [`Formula::and_keeping`] and [`Formula::or_keeping`], which drop `true` and `false`
/// and keep the tighter of two rows of one left-hand side; and beside it the equation
/// `a == v` of each fixed atom `a`, so that every atom of the formula is still in it, and
/// two atoms the formula tells apart (`x == 2` beside a product `x * y`) are told apart
/// there too, as the solver's check that no name orders its search needs
/// ([`Renamed`]). `None` when no atom is fixed, so the formula goes to the solver
/// as written. O(n + k log k) for `n` the size of the formula with each shared part
/// counted once ([`Formula::map_cons`] folds each shared part once) and `k` the atoms
/// fixed, whose equations are sorted, so that their order is the same in every order of
/// the propagation.
fn reduced(facts: &Facts) -> Option<Formula> {
    if facts.known.is_empty() {
        return None;
    }
    let replaced = facts.formula.map_cons(&|c| {
        if !c.lin.terms.keys().any(|a| facts.known.contains_key(a)) {
            return Formula::Con(c.clone());
        }
        let mut lin = Lin {
            terms: BTreeMap::new(),
            constant: c.lin.constant.clone(),
        };
        for (a, k) in &c.lin.terms {
            match facts.known.get(a) {
                Some(v) => lin.constant = &lin.constant + &(k * v),
                None => {
                    lin.terms.insert(a.clone(), k.clone());
                }
            }
        }
        if !lin.terms.is_empty() {
            return Formula::Con(Con { lin, rel: c.rel });
        }
        let holds = match c.rel {
            Rel::Eq => lin.constant.is_zero(),
            Rel::Ge => !lin.constant.is_negative(),
        };
        if holds {
            Formula::top()
        } else {
            Formula::bottom()
        }
    });
    let mut fixed: Vec<(&Atom, &Int)> = facts.known.iter().map(|(a, v)| (*a, v)).collect();
    fixed.sort_unstable();
    let equations = (fixed.into_iter())
        .map(|(a, v)| Formula::Con(Con::eq(&Lin::atom(a.clone()), &Lin::constant(v.clone()))));
    Some(Formula::and(
        std::iter::once(replaced).chain(equations).collect(),
    ))
}

/// Whether `f` holds somewhere, and where. A formula whose forced equations fix its atoms one
/// after another, as the preimage of a chain of `if` at a point gives, is answered by
/// propagation alone in time linear in its size (module `forced`, PRES-small-cost), with every
/// atom of the formula in its point; any other goes to the solver. The solver's point may leave
/// atoms of `f` out, and each atom left out is zero there, as [`Formula::holds`] reads it: an
/// atom of a disjunction that `absorb` removed where zero lies between its bounds (`repair`), an
/// atom of a disjunct the search did not take, and an atom of a disjunct it took because its rows
/// hold with that atom read as zero (`pick`). A caller that needs a value for every atom gives
/// those left out zero (`l01_38_presburger::model_keys`). A product is read as an atom of its
/// own, as everywhere in the solver, so its value in the point need not be the product of its
/// factors' values: the point satisfies `f` with each product read as a variable of its own
/// (PRES-product-parity), and [`Formula::holds`], which reads a product through its factors, may
/// reject it (PRES-model-products).
/// The solver is given `f` with each atom propagation fixed replaced by its value; a formula it
/// refuses so is asked again as written (PRES-small-point).
pub fn satisfiable(f: &Formula) -> Result<Option<Model>, Refusal> {
    match forced::forced(f, true) {
        Forced::Empty => Ok(None),
        Forced::Point(m) => Ok(Some(m)),
        Forced::Holds => unreachable!("a point is asked for"),
        Forced::Undecided(facts) => match reduced(&facts) {
            None => or_old(|| satisfiable_named(f)),
            // Complexity tradeoff: as at `decide`, a refusal with the facts asks again as
            // written.
            Some(g) => match or_old(|| satisfiable_named(&g)) {
                Ok(m) => Ok(m.map(|mut m| {
                    facts.fill(&mut m);
                    m
                })),
                Err(_) => or_old(|| satisfiable_named(f)),
            },
        },
    }
}

/// [`satisfiable`] on one path ([`or_old`]).
fn satisfiable_named(f: &Formula) -> Result<Option<Model>, Refusal> {
    match Renamed::of(f) {
        Naming::Kept => satisfiable_inner(f),
        Naming::Renamed(r) => {
            let found = satisfiable_inner(&r.f).map_err(|e| r.back_refusal(e))?;
            Ok(found.map(|m| m.into_iter().map(|(a, v)| (r.back(&a), v)).collect()))
        }
        Naming::Tied(vars, color) => match settle_tied(f, &color, true)? {
            Settled::Empty => Ok(None),
            Settled::Point(m) => Ok(Some(m)),
            Settled::Left(p) => Err(unordered(vars, &p)),
        },
    }
}

/// [`satisfiable`] of a formula whose names no longer matter ([`Renamed`]): searched as
/// [`decide_inner`] searches it, with the rows the disjunctions imply asked first and the
/// atoms that [`absorb`] projected away given values. The implied rows hold at every point of
/// the formula, so a point with them is a point of the formula; they keep [`pick`] from taking
/// a disjunct that leaves the disjunctions after it no point within their hulls, which on a
/// path of steps each up or down took two steps down that the rest could not balance
/// (`l01_38_presburger::model::a_disjunction_of_unit_rows_is_decided_and_placed`).
// Complexity tradeoff: as in [`decide_inner`], a formula refused with the implied rows is
// asked twice, so it costs up to twice what it cost before; the first ask stops at the
// refusal. No answer is given up: one refused with the rows is asked as before without them.
// Naive version: one ask without the implied rows; used: the ask with them first, and without
// them only on a refusal, at most two asks of one size. COMPLEXITY.md row S44.
fn satisfiable_inner(f: &Formula) -> Result<Option<Model>, Refusal> {
    let (p, gone) = absorbed(f, &[]);
    let implied = if old_path() {
        Vec::new()
    } else {
        disjunction_hulls(&p.ors, &mut DeepHulls::default())
    };
    let ask = |mut p: Parts, rows: Vec<Con>| -> Result<Option<Model>, Refusal> {
        p.cons.extend(rows);
        match settle(p, true)? {
            None => Ok(None),
            Some(p) => found(p),
        }
    };
    let m = if implied.is_empty() {
        ask(p, implied)?
    } else {
        ask(p, implied).or_else(|_| ask(absorbed(f, &[]).0, Vec::new()))?
    };
    Ok(m.map(|mut m| {
        repair(&mut m, &gone);
        m
    }))
}

/// Whether `f` holds somewhere. A conjunction is decided without building a point; a point is
/// built only to search the disjunctions that propagation leaves.
/// A formula that propagation over its forced parts decides (module `forced`), or the rounds at
/// its bounds show true at a point, is answered without the solver; any other goes to the solver
/// with each atom propagation fixed replaced by its value, and as written if the solver refuses
/// that.
pub fn decide(f: &Formula) -> Result<bool, Refusal> {
    // The formula with each shared part taken out of the disjunctions that hold it in every
    // disjunct ([`factored`]) holds at the same points, so its answer is the answer; the
    // formula as written is asked where it is refused, so a refusal names the formula as
    // written.
    if let Some(g) = factored(f)
        && let Ok(b) = decide_written(&g)
    {
        return Ok(b);
    }
    decide_written(f)
}

/// [`decide`] of `f` as it is written, with no part taken out of its disjunctions.
fn decide_written(f: &Formula) -> Result<bool, Refusal> {
    match forced::forced(f, false) {
        Forced::Empty => Ok(false),
        Forced::Point(_) | Forced::Holds => Ok(true),
        Forced::Undecided(facts) => match reduced(&facts) {
            None => or_old(|| decide_named(f)),
            // Complexity tradeoff: a formula the solver refuses with the facts is asked again
            // as written, so it costs up to twice what it cost before, and no answer given as
            // written becomes a refusal; a refusal then names the rows as written. Naive
            // version: the formula as written alone, which leaves the solver to find again
            // what propagation proved; used: the facts first, at most two asks of one size.
            // Measured over the undecided formulas of the forced_against_solver census, the
            // solver's work with the facts, a second ask included, is 0.64 of that as written
            // on chains of definitions, 0.76 on bounded inputs, 0.93 on ladders; one formula
            // in 50 of the chains is refused with the facts, where the replaced rows told two
            // factors of a product apart. Leaving such factors as written gave no refusals but
            // 0.83, since fewer formulas kept any fact. COMPLEXITY.md row PRES-small-point.
            Some(g) => or_old(|| decide_named(&g)).or_else(|_| or_old(|| decide_named(f))),
        },
    }
}

/// [`decide`] on one path ([`or_old`]).
fn decide_named(f: &Formula) -> Result<bool, Refusal> {
    match Renamed::of(f) {
        Naming::Kept => unit_rows_have_a_point(f).map_or_else(|| decide_inner(f), Ok),
        Naming::Renamed(r) => decide_inner(&r.f).map_err(|e| r.back_refusal(e)),
        Naming::Tied(vars, color) => match settle_tied(f, &color, false)? {
            Settled::Empty => Ok(false),
            Settled::Point(_) => Ok(true),
            Settled::Left(p) => Err(unordered(vars, &p)),
        },
    }
}

/// Whether `f`, a conjunction with no disjunction or negation, has an integer point, when each
/// of its constraints has at most two terms, each with coefficient 1 or -1 and over a symbol or
/// an auxiliary variable; `None` for any other formula. Such rows are decided exactly by
/// [`utvpi::integer_empty`], the search that [`Omega::run`] makes on them at the end of
/// [`decide_inner`]'s path, so the answer is the same; the path's front end ([`nnf`], [`take`],
/// [`canonical`], [`quotient`]) is skipped, which on such rows cost 3 to 5 times the search
/// itself and grew by a factor of `log m` from its ordered maps keyed by [`Atom`] (COMPLEXITY.md
/// S44, DECIDE-front-cost). An equality is its two rows `t >= 0` and `-t >= 0`; a row of no
/// term is decided by its constant. One pass over the constraints, each atom numbered through
/// a hash map: O(m) for `m` terms, plus the search.
fn unit_rows_have_a_point(f: &Formula) -> Option<bool> {
    let cons = f.cons();
    let unit = |(a, k): (&Atom, &Int)| k.is_unit() && !matches!(a, Atom::Product(..));
    if !(cons.iter()).all(|c| c.lin.terms.len() <= 2 && c.lin.terms.iter().all(unit)) {
        return None;
    }
    let mut ids: HashMap<&Atom, usize> = HashMap::new();
    let mut rows: Vec<(Vec<Term>, Int)> = Vec::with_capacity(cons.len());
    for c in &cons {
        let k = &c.lin.constant;
        if c.lin.terms.is_empty() {
            if k.is_negative() || (c.rel == Rel::Eq && !k.is_zero()) {
                return Some(false);
            }
            continue;
        }
        let terms: Vec<Term> = (c.lin.terms.iter())
            .map(|(a, coef)| {
                let next = ids.len();
                (*ids.entry(a).or_insert(next), coef.clone())
            })
            .collect();
        if c.rel == Rel::Eq {
            let neg = terms.iter().map(|(j, coef)| (*j, -coef)).collect();
            rows.push((neg, -k));
        }
        rows.push((terms, k.clone()));
    }
    let rows: Vec<(&[Term], &Int)> = rows.iter().map(|(t, k)| (&t[..], k)).collect();
    Some(!utvpi::integer_empty(ids.len(), &rows))
}

/// For each disjunction, the bounds on a linear form that every disjunct puts on it, joined:
/// when each disjunct bounds `l` from below, the disjunction implies the least of those
/// bounds, and likewise above. A disjunct's bounds are its deep hull ([`DeepHulls`]): those of its
/// own rows on `l` alone, met with those its own disjunctions imply, at every level of the
/// nest, so that `z >= 1` at the bottom of a nest of disjunctions is implied at its top. A
/// disjunct whose deep hull shows it has no point is left out of the join, and a disjunction
/// left with none gives the row `0 >= 1`. A form is read up to its sign and constant
/// (`s <= 1` and `s >= 3` are both rows on `s`), so the rows returned have the points of the
/// disjunctions and more, and the formula with them has its own points. On `k` disjunctions
/// such as `s == 2 || s == 3` along a chain, the rows `2 <= s <= 3` show by one solve of the
/// base that a bound on the chain's end past what they allow leaves no point, where [`probe`]
/// tests each disjunct by a propagation of the whole formula (COMPLEXITY.md DISJ-incremental).
/// `deep` keeps the hulls of the disjunctions found, so that a caller asking again joins each
/// once; the hull of each disjunct is kept on it ([`Parts`]), so that it is found once in its
/// life, however many questions read the formulas that hold it.
fn disjunction_hulls(ors: &[Vec<Rc<Parts>>], deep: &mut DeepHulls) -> Vec<Con> {
    let mut rows = Vec::new();
    for ds in ors {
        if ds.is_empty() {
            continue;
        }
        let Some(join) = deep.join(ds) else {
            rows.push(Con::ge(&Lin::constant(0), &Lin::constant(1)));
            continue;
        };
        for (terms, (lo, hi)) in join.iter() {
            let form = Lin {
                terms: terms.iter().cloned().collect(),
                constant: Int::ZERO,
            };
            if let Some(l) = lo {
                rows.push(Con::ge(&form, &Lin::constant(l.clone())));
            }
            if let Some(h) = hi {
                rows.push(Con::ge(&Lin::constant(h.clone()), &form));
            }
        }
    }
    rows
}

/// The bounds that each linear form has at every point of a part, each form read up to its
/// sign and constant as [`values::form_bounds`] reads a row. A persistent map, so that a hull
/// that is another with a few forms changed shares the rest.
type HullMap = OrdMap<values::Form, values::Bounds>;

/// A hull of [`DeepHulls`], under an id that no other hull of one call has, with the hull it
/// was made from, if any: its id, its map, and the forms changed from it, so that hulls made
/// from one hull are joined or met at those forms alone.
#[derive(Clone)]
struct Rooted {
    id: u64,
    map: HullMap,
    from: Option<Rc<(u64, HullMap, Vec<values::Form>)>>,
}

/// A part read by [`DeepHulls`]: its base, the meet of the hulls of its disjunctions (`None`
/// when one of them has no point), and the bounds of its own rows; its hull is the two met.
struct Read {
    base: Option<Rooted>,
    own: values::FormBounds,
}

impl Read {
    /// Whether the part has points as far as its hull shows: a base, and no form whose bounds
    /// cross once its own are met with the base's.
    fn live(&self) -> bool {
        let Some(b) = &self.base else { return false };
        (self.own.iter()).all(|(t, o)| met(b.map.get(t), o).is_some())
    }

    /// The bounds of the form `t` in the part's hull; the part is live.
    fn at(&self, t: &values::Form) -> Option<values::Bounds> {
        let b = self.base.as_ref().expect("a live part").map.get(t);
        match self.own.get(t) {
            Some(o) => met(b, o),
            None => b.cloned(),
        }
    }
}

/// The deep hulls of parts ([`disjunction_hulls`]): of a part, the bounds its own rows put on
/// each form ([`values::form_bounds`]) met with those of its base, the meet of the hulls of
/// its disjunctions; of a disjunction, the join of the deep hulls of its disjuncts that have
/// points. Every bound is implied by the part, so the rows they give hold at each of its
/// points; a part with no hull has none. The hulls depend only on the rows of the parts, not
/// on which parts are shared: a part held in two places has the same hull in both, and the
/// formula written out with a copy at each place has the same hulls.
// Complexity tradeoff: the naive version finds the hulls of each part from the formula
// written out, one per path through the nest, `2^k` for `k` levels of a disjunction held by
// both disjuncts of the one above (PRES-nest-empty, the family of `nest_empty`); with a
// plain map for each part, built from those below it, O(n·d) for `n` rows and depth `d`,
// and a join form by form over the smallest hull, O(n²) on a chain of two disjunctions each
// held by both at the level above; and with the hulls kept for one call, O(n) again for
// each question on a formula that holds the nest, O(n²) where `project_parts` asks one at
// each level (`l01_39_reduced_product::deep_condition`, the bound that moves at each
// level). Used: each part is read once in its life, its hull kept on it, on an explicit
// stack, so a question on a formula of parts read before reads only its top; a hull is
// never built in full; a disjunction's hull is the join of its disjuncts' bases with the
// forms of their own rows joined again, made from that join; the join of bases is kept by
// their ids, and bases that are one hull, or that are made from one hull, are joined at
// the forms changed from it alone; a part's base likewise. So a disjunction costs
// O(r log n) for the `r` forms of its disjuncts' own rows and of those of the level below,
// O(n log n) in all on both chains whatever their depth (`l01_38_presburger::nest_empty`,
// COMPLEXITY.md PRES-nest-empty). What is given up: the hull kept on each disjunct for its
// life, and maps from ids to the hulls of disjunctions for one call. Bases made from
// different hulls are joined over the smallest, O(s log n) for its `s` forms, and met by
// adding the smaller to the largest: a formula whose disjunctions each join hulls with no
// common origin and many forms still costs O(n·s).
#[derive(Default)]
struct DeepHulls {
    /// The hull of each disjunction, by the ids of its disjuncts; `None` when none has points.
    ors: HashMap<Vec<u64>, Option<Rooted>>,
    /// The base of each part, by the ids of the hulls of its disjunctions, sorted.
    meets: HashMap<Vec<u64>, Option<Rooted>>,
    /// The join of the bases of the live disjuncts of a disjunction, by their ids, sorted.
    joins: HashMap<Vec<u64>, Rooted>,
}

impl DeepHulls {
    /// The hull of the disjunction `ds`, reading each part below it that is not yet read,
    /// each before the parts that hold it, on an explicit stack (a nest can be deeper than a
    /// thread's stack allows).
    fn join(&mut self, ds: &[Rc<Parts>]) -> Option<HullMap> {
        let mut stack: Vec<&Parts> = ds.iter().map(|d| &**d).collect();
        while let Some(&p) = stack.last() {
            if p.hull.get().is_some() {
                stack.pop();
                continue;
            }
            let open = stack.len();
            let below = p.ors.iter().flatten().map(|d| &**d);
            stack.extend(below.filter(|d| d.hull.get().is_none()));
            if stack.len() > open {
                continue;
            }
            stack.pop();
            let base = self.base(&p.ors);
            let own = values::form_bounds(&p.cons);
            let _ = p.hull.set(Read { base, own });
        }
        self.disjunction(ds).map(|h| h.map)
    }

    /// The meet of the hulls of the disjunctions `ors`, whose disjuncts are all read; the
    /// empty hull, id 0, when there are none.
    fn base(&mut self, ors: &[Vec<Rc<Parts>>]) -> Option<Rooted> {
        let mut hulls: Vec<Rooted> = (ors.iter())
            .map(|ds| self.disjunction(ds))
            .collect::<Option<_>>()?;
        hulls.sort_unstable_by_key(|h| h.id);
        hulls.dedup_by_key(|h| h.id);
        if hulls.len() <= 1 {
            return Some(hulls.pop().unwrap_or_else(|| Rooted {
                id: 0,
                map: OrdMap::new(),
                from: None,
            }));
        }
        let ids: Vec<u64> = hulls.iter().map(|h| h.id).collect();
        if let Some(m) = self.meets.get(&ids) {
            return m.clone();
        }
        let map = match one_origin(&hulls) {
            Some((map, forms)) => forms.into_iter().try_fold(map, |mut map, t| {
                let mut b: values::Bounds = (None, None);
                for h in &hulls {
                    if let Some(hb) = h.map.get(&t) {
                        b = met(Some(&b), hb)?;
                    }
                }
                match b {
                    (None, None) => map.remove(&t),
                    b => map.insert(t, b),
                };
                Some(map)
            }),
            None => {
                let largest = (0..hulls.len()).max_by_key(|&i| hulls[i].map.len());
                let mut map = hulls.swap_remove(largest.expect("two hulls")).map;
                let others = hulls.iter().flat_map(|h| h.map.iter());
                let crossed = others.into_iter().any(|(t, b)| match met(map.get(t), b) {
                    Some(m) => {
                        map.insert(t.clone(), m);
                        false
                    }
                    None => true,
                });
                (!crossed).then_some(map)
            }
        };
        let out = map.map(|map| Rooted {
            id: fresh_id(),
            map,
            from: None,
        });
        self.meets.insert(ids, out.clone());
        out
    }

    /// The join of the hulls of the disjuncts of `ds` that have points, all read: the join of
    /// their bases ([`join_bases`]) with the forms of their own rows joined again.
    fn disjunction(&mut self, ds: &[Rc<Parts>]) -> Option<Rooted> {
        let key: Vec<u64> = ds.iter().map(|d| d.id()).collect();
        if let Some(h) = self.ors.get(&key) {
            return h.clone();
        }
        let live: Vec<&Read> = (ds.iter())
            .map(|d| d.hull.get().expect("a part read"))
            .filter(|r| r.live())
            .collect();
        let out = (!live.is_empty()).then(|| {
            let bases: Vec<&Rooted> = live
                .iter()
                .map(|r| r.base.as_ref().expect("live"))
                .collect();
            let join = join_bases(&mut self.joins, &bases);
            let forms: BTreeSet<&values::Form> = live.iter().flat_map(|r| r.own.keys()).collect();
            let mut map = join.map.clone();
            for &t in &forms {
                match joined(live.iter().map(|r| r.at(t))) {
                    Some(b) => map.insert(t.clone(), b),
                    None => map.remove(t),
                };
            }
            let forms = forms.into_iter().cloned().collect();
            Rooted {
                id: fresh_id(),
                map,
                from: Some(Rc::new((join.id, join.map, forms))),
            }
        });
        self.ors.insert(key, out.clone());
        out
    }
}

/// The join of the hulls `bases`, kept in `joins` by their ids: one hull is itself; hulls
/// made from one hull ([`one_origin`]) are it with the forms changed from it joined; others
/// are joined form by form over the smallest.
fn join_bases(joins: &mut HashMap<Vec<u64>, Rooted>, bases: &[&Rooted]) -> Rooted {
    let mut bases: Vec<&Rooted> = bases.to_vec();
    bases.sort_unstable_by_key(|h| h.id);
    bases.dedup_by_key(|h| h.id);
    if let [one] = bases[..] {
        return one.clone();
    }
    let ids: Vec<u64> = bases.iter().map(|h| h.id).collect();
    if let Some(j) = joins.get(&ids) {
        return j.clone();
    }
    let at = |t: &values::Form| joined(bases.iter().map(|h| h.map.get(t).cloned()));
    let owned: Vec<Rooted> = bases.iter().map(|h| (*h).clone()).collect();
    let map = match one_origin(&owned) {
        Some((mut map, forms)) => {
            for t in forms {
                match at(&t) {
                    Some(b) => map.insert(t, b),
                    None => map.remove(&t),
                };
            }
            map
        }
        None => {
            let smallest = bases.iter().min_by_key(|h| h.map.len()).expect("two hulls");
            (smallest.map.keys())
                .filter_map(|t| Some((t.clone(), at(t)?)))
                .collect()
        }
    };
    let out = Rooted {
        id: fresh_id(),
        map,
        from: None,
    };
    joins.insert(ids, out.clone());
    out
}

/// When every hull of `hulls` was made from one hull, that hull's map and the forms changed
/// from it in any of them; outside those forms each of `hulls` is that hull.
fn one_origin(hulls: &[Rooted]) -> Option<(HullMap, BTreeSet<values::Form>)> {
    let first = hulls.first()?.from.as_ref()?;
    let mut forms = BTreeSet::new();
    for h in hulls {
        let from = h.from.as_ref()?;
        if from.0 != first.0 {
            return None;
        }
        forms.extend(from.2.iter().cloned());
    }
    Some((first.1.clone(), forms))
}

/// The join of the bounds `bs` of one form, one from each disjunct: the least of the lower
/// bounds and the greatest of the upper ones, a side left open where any disjunct leaves it
/// open; `None` when both sides are open, or a disjunct does not bound the form.
fn joined(mut bs: impl Iterator<Item = Option<values::Bounds>>) -> Option<values::Bounds> {
    let (mut lo, mut hi) = bs.next()??;
    for b in bs {
        let (l, h) = b?;
        lo = lo.zip(l).map(|(a, b)| a.min(b));
        hi = hi.zip(h).map(|(a, b)| a.max(b));
        if lo.is_none() && hi.is_none() {
            return None;
        }
    }
    (lo.is_some() || hi.is_some()).then_some((lo, hi))
}

/// The bounds `a` met with `b`: the greater lower bound and the lesser upper one; `None`
/// when they cross.
fn met(a: Option<&values::Bounds>, b: &values::Bounds) -> Option<values::Bounds> {
    let (lo, hi) = match a {
        None => b.clone(),
        Some((l, u)) => (
            [l, &b.0].into_iter().flatten().max().cloned(),
            [u, &b.1].into_iter().flatten().min().cloned(),
        ),
    };
    match (&lo, &hi) {
        (Some(l), Some(u)) if l > u => None,
        _ => Some((lo, hi)),
    }
}

/// Removes from `ors` each disjunct that has no point with `rows` and the rows that the
/// disjunctions imply ([`disjunction_hulls`]), until none is removed, and gives the number of
/// passes; `None` when a disjunction is left with no disjunct or the rows show there is no
/// point. `rows` and the disjunctions are the parts of a formula, so the implied rows hold at
/// each of its points, and a disjunct removed has none: the formula's points are as they were.
/// A pass asks each disjunct of the rows projected onto its own atoms ([`by_halves`],
/// [`shadow`], exact over the integers), and a disjunction that loses a disjunct adds its
/// narrower implied rows to the projections of the disjunctions after it in the pass, once
/// all its disjuncts are asked. The disjunctions are taken in the order of their structure
/// ([`by_structure`]), forward and backward in turn, until a pass removes nothing. The result
/// does not depend on the order of the disjunctions or of their disjuncts: a disjunct is
/// removed only when it is
/// empty with rows that the disjuncts still there imply, fewer disjuncts imply narrower rows,
/// so a disjunct removed in one order is removed in any, and the last pass, which removes
/// nothing, asks every disjunct of the same rows (the greatest set of disjuncts closed under
/// this test). The one exception is a disjunct whose question the solver refuses (`solve`
/// gives `Err`, a [`Refusal`] such as one for growth): it is kept, and since a refusal depends
/// on the rows asked with, not only on whether they have a point, the same disjunct asked with
/// narrower rows in another order could be answered and removed. Running to a fixed point does
/// not remove this, because the refused test is not monotone in the rows. Both results are
/// sound; the one with the disjunct kept can have a wider hull. In the tests this happens only
/// in `by_halves_against_old::answers_are_those_of_the_old_path`, 61 refused questions in 781
/// calls, and the disjuncts kept were the same in both orders in every call. Two
/// disjunctions on one stage of a chain, `x[i + 1] - x[i]` in {3, 7} and
/// `x[i + 1] - x[i] + y[i]` in {6, 9} with `1 <= y[i] <= 2`, lose 3 (the sum's rows allow 4 to
/// 8 for the step) and then 6 (the step is 7), and then imply the stage exactly: rows that
/// [`project_parts`] reads for its hulls and [`tighten_each`] for a point at each end, so that no
/// question is asked whose answer is no point (COMPLEXITY.md DISJ-incremental).
// Complexity tradeoff: a pass costs one projection by halves, O((m + k) log k) for `m` terms
// and `k` disjuncts asked where the projections of the ranges of the order stay small, as on
// a chain in its own order. Each disjunct is asked of the rows projected onto its own atoms;
// projected onto the atoms of its whole disjunction, as before item PROJECT-canon-rounds,
// the rows each disjunct was asked with were as large as that union, so a disjunction of `k`
// cases each reading its own stage of a chain cost `k` questions of O(k) rows, O(k²) (70
// times the time at `8k`, `exclusive_cases`); now 10 times. The answers are the same: a
// disjunct has a point with the rows exactly when it has one with their projection onto any
// set of atoms that holds its own, and a disjunction is changed only after all its disjuncts
// are asked, as it was. A question the solver refuses (a [`Refusal`]) keeps its disjunct
// as before; since a refusal depends on the rows asked, a question refused with one set of
// rows could be answered with the other, which changed no answer of the steps that use this
// solver (each projection compared before and after this change). The projections by halves
// are onto the atoms of ranges of disjuncts rather than of disjunctions, the same atoms in
// all. Removals that each need the one before run in one pass while they follow the order
// of the pass. On a chain (each part sharing atoms with the one before and
// the one after only) the structural order runs from one end to the other, so such removals
// cost O(1) passes, whatever the names or the order given (4 or fewer on the chain of
// `jointly_empty_order`, in six orders at 16 and 128 stages). What is given up: time only,
// where the removals turn back in the structural order: each turn costs a pass, O(k) passes
// at most since each pass but the last removes a disjunct, so O(k (m + k) log k) in all. A hub
// with `r` arms whose removals run out along each arm and back through the hub turns twice per
// arm: 9, 17 and 31 passes at 4, 8 and 32 arms (25 ms, 108 ms and 977 ms). Why: the test of a
// disjunct reads the whole projection, and a removal reaches every disjunction linked to it
// by rows, not only those sharing an atom with it (the next arm shares none), so asking again
// only the disjunctions that share an atom misses removals, and asking every linked one is a
// pass. A method with a bound would keep the projections as a tree of halves, remake one path
// after a removal and ask again only the disjunctions whose projection changed; on the hub
// that is still `r` projections changed per arm. Trigger: removals that pass back and forth
// through shared atoms. Tests: `jointly_empty_order` (both families, in several orders) and
// `l01_38_presburger::disj_groups` (the chains at `n` and `8n`). Also not done here: a
// disjunct empty only with a choice of disjuncts in other disjunctions (case reasoning, a
// search that backtracks over the disjuncts) is kept; see the comment on the questions in
// [`project_parts`].
fn drop_jointly_empty(rows: &[Con], ors: &mut [Vec<Rc<Parts>>]) -> Option<usize> {
    let mut order = by_structure(rows, ors);
    let mut passes = 0;
    let mut deep = DeepHulls::default();
    loop {
        let implied = disjunction_hulls(ors, &mut deep);
        if implied.is_empty() {
            return Some(passes);
        }
        passes += 1;
        // The atoms of the constraints of each disjunct asked, by disjunction in the order of
        // this pass, with its place: each disjunct is asked of the rows projected onto its own
        // atoms, which have a point with it exactly when the rows do (the projection is exact
        // over the integers).
        let mut keep: Vec<BTreeSet<Atom>> = Vec::new();
        let mut place: Vec<(usize, usize)> = Vec::new();
        for &j in &order {
            for (t, d) in ors[j]
                .iter()
                .enumerate()
                .filter(|(_, d)| !d.cons.is_empty())
            {
                keep.push(
                    d.cons
                        .iter()
                        .flat_map(|c| c.lin.terms.keys().cloned())
                        .collect(),
                );
                place.push((j, t));
            }
        }
        let mut all = rows.to_vec();
        all.extend(implied);
        let mut removed = false;
        // The disjuncts of the disjunction being asked found with no point.
        let mut empty: Vec<usize> = Vec::new();
        // `Err` when a projection or a disjunction is left with no point.
        let ran: Result<(), ()> = by_halves(all, &keep, |i, k| {
            let k = k.ok_or(())?;
            let (j, t) = place[i];
            let cs: Vec<&Con> = k.iter().chain(ors[j][t].cons.iter()).collect();
            if matches!(solve(&cs, false), Ok(None)) {
                empty.push(t);
            }
            // The disjunction is changed after its last disjunct is asked, so that its
            // narrower rows reach the disjunctions after it in the pass only.
            if place.get(i + 1).is_some_and(|&(next, _)| next == j) || empty.is_empty() {
                return Ok(Vec::new());
            }
            // `empty` is in increasing order, so one walk removes its disjuncts.
            let ds = &mut ors[j];
            let (mut t, mut next) = (0, empty.iter().peekable());
            ds.retain(|_| {
                t += 1;
                next.next_if_eq(&&(t - 1)).is_none()
            });
            empty.clear();
            if ds.is_empty() {
                return Err(());
            }
            removed = true;
            Ok(disjunction_hulls(std::slice::from_ref(ds), &mut deep))
        });
        if ran.is_err() {
            return None;
        }
        if !removed {
            return Some(passes);
        }
        order.reverse();
    }
}

/// The places in `ors` of the disjunctions with a disjunct that has constraints of its own, in
/// breadth-first order over the parts, two parts (a row of `rows` or a disjunction) being
/// neighbors when they share an atom, from a part that a first breadth-first search from the
/// first disjunction of its group reaches last (the start that Cuthill and McKee's order takes,
/// "Reducing the bandwidth of sparse symmetric matrices", ACM '69, 157-172). Each group of
/// parts linked by shared atoms comes whole. On a chain, where each part shares atoms with the
/// one before and the one after only, the order runs from one end to the other, whatever the
/// names of the atoms or the order of `ors`. O(t) hash operations for `t` terms.
fn by_structure<'a>(rows: &'a [Con], ors: &'a [Vec<Rc<Parts>>]) -> Vec<usize> {
    let asked: Vec<usize> = (0..ors.len())
        .filter(|&j| ors[j].iter().any(|d| !d.cons.is_empty()))
        .collect();
    let mut atoms: Vec<Vec<&Atom>> = rows.iter().map(|c| c.lin.terms.keys().collect()).collect();
    for &j in &asked {
        let cons = ors[j].iter().flat_map(|d| d.cons.iter());
        let mut xs: Vec<&Atom> = cons.flat_map(|c| c.lin.terms.keys()).collect();
        xs.sort_unstable();
        xs.dedup();
        atoms.push(xs);
    }
    let mut by_atom: HashMap<&Atom, Vec<usize>> = HashMap::new();
    for (u, xs) in atoms.iter().enumerate() {
        for &a in xs {
            by_atom.entry(a).or_default().push(u);
        }
    }
    // The parts in breadth-first order from `start`, over the parts not yet `seen`, with the
    // atoms whose parts are already queued in `done`.
    let breadth_first = |start: usize, seen: &mut [bool], done: &mut HashSet<&'a Atom>| {
        seen[start] = true;
        let mut out = vec![start];
        let mut head = 0;
        while let Some(&u) = out.get(head) {
            for &a in &atoms[u] {
                if done.insert(a) {
                    for &v in &by_atom[a] {
                        if !seen[v] {
                            seen[v] = true;
                            out.push(v);
                        }
                    }
                }
            }
            head += 1;
        }
        out
    };
    // Each search covers a group of linked parts, so each part is reached once by each.
    let (mut seen_first, mut done_first) = (vec![false; atoms.len()], HashSet::new());
    let (mut seen, mut done) = (vec![false; atoms.len()], HashSet::new());
    let mut order = Vec::with_capacity(asked.len());
    for start in rows.len()..atoms.len() {
        if seen[start] {
            continue;
        }
        let first = breadth_first(start, &mut seen_first, &mut done_first);
        let far = *first.last().expect("the start");
        let group = breadth_first(far, &mut seen, &mut done);
        order.extend(
            (group.into_iter()).filter_map(|u| u.checked_sub(rows.len()).map(|k| asked[k])),
        );
    }
    order
}

/// Whether the projections by halves ([`by_halves`] in [`settle`], [`pick`] and
/// [`project_parts`]) and the rows the disjunctions imply ([`disjunction_hulls`]) are left
/// out, as before DISJ-diff-fast and DISJ-incremental: while a question that the solver
/// refused on the new path is asked again ([`or_old`]), and in the tests that compare the
/// two.
fn old_path() -> bool {
    OLD_PATH.with(Cell::get)
}

thread_local! {
    static OLD_PATH: Cell<bool> = const { Cell::new(false) };
    static REVERSED: Cell<bool> = const { Cell::new(false) };
}

/// `f` run with the disjunctions of every `project_parts` call, and the disjuncts of each,
/// read in the reverse of their order, so that a test can check that the answer does not
/// depend on that order (item PROJECT-canon-precision).
pub fn with_parts_reversed<T>(f: impl FnOnce() -> T) -> T {
    let was = REVERSED.with(|r| r.replace(true));
    let out = f();
    REVERSED.with(|r| r.set(was));
    out
}

/// `f` written one way whatever way an equal formula was written (items PROJECT-each-canon and
/// PROJECT-canon-gcd): each constraint divided by the greatest common divisor of its
/// coefficients ([`Con::reduced`]: `2t == 0` as `t == 0`, `2t == 1` as `false`, `2t + 1 >= 0`
/// as `t >= 0`); each equation `t == 0` with the sign of `t` whose first coefficient is
/// positive, or, with `both`, held with both signs ([`equation`]); and in each conjunction,
/// `t >= 0` beside `-t >= 0`, after the division, as `t == 0`, so that an equation written
/// with either sign, with a common factor, twice with opposite signs, or as two inequalities
/// is one constraint, and [`Formula::and`] holds it once. Each later step reads the signs of
/// the rows (the colors of [`stable_colors`] and the order of [`canonical`] among them), and
/// a question that one writing answered another refused with [`Refusal::Growth`]. In time
/// O(n log n) in the size of `f`; a node that is written so already is kept, with its id.
///
/// Neither writing answers every question the other does: the solver refuses some systems with
/// one sign of an equation and answers them with the other, and [`project_each`] asks with the
/// second writing only where the first is refused.
fn signed(f: &Formula, both: bool) -> Formula {
    // Each node's writing, or `None` where it is written so already: an unchanged node is kept
    // as it is, with its id, so that what later steps keep by id still finds it.
    let changed = f.fold(
        false,
        |g, negated| negated != matches!(g, Formula::Not(_)),
        |g, negated, parts: Vec<Option<Formula>>| match g {
            Formula::Con(c) => match c.reduced() {
                Some(r) => Some(match &r {
                    Formula::Con(e) if e.rel == Rel::Eq => equation(e, negated, both).unwrap_or(r),
                    _ => r,
                }),
                None if c.rel == Rel::Eq => equation(c, negated, both),
                None => None,
            },
            Formula::And(gs) => {
                // Each `t >= 0` whose `-t >= 0` is a part too, both as reduced, as the
                // equation, in its place, so that the parts keep their places
                // ([`Formula::rebuild`]).
                let rows: Vec<&Formula> = (gs.iter().zip(&parts))
                    .map(|(k, p)| p.as_ref().unwrap_or(k))
                    .collect();
                let paired = opposite_rows(&rows);
                if paired.is_empty() && parts.iter().all(Option::is_none) {
                    return None;
                }
                let kids = (rows.iter().enumerate())
                    .map(|(i, k)| match k {
                        Formula::Con(c) if paired.contains(&i) => {
                            let eq = Con {
                                lin: c.lin.clone(),
                                rel: Rel::Eq,
                            };
                            equation(&eq, negated, both).unwrap_or(Formula::Con(eq))
                        }
                        k => (*k).clone(),
                    })
                    .collect();
                Some(g.rebuild(kids))
            }
            Formula::Not(_) | Formula::Or(_) => {
                if parts.iter().all(Option::is_none) {
                    return None;
                }
                let kids = (g.kids().iter().zip(parts))
                    .map(|(k, p)| p.unwrap_or_else(|| k.clone()))
                    .collect();
                Some(g.rebuild(kids))
            }
        },
    );
    changed.unwrap_or_else(|| f.clone())
}

/// The places of the rows `t >= 0` among `gs` whose opposite `-t >= 0` is among them too, found
/// by a hash that `t` and `-t` share, so that no row is copied.
fn opposite_rows(gs: &[&Formula]) -> BTreeSet<usize> {
    use std::hash::{Hash, Hasher};
    let mut by: HashMap<u64, Vec<usize>> = HashMap::new();
    for (i, g) in gs.iter().enumerate() {
        let Formula::Con(c) = g else { continue };
        let Some((_, first)) = c.lin.terms.first_key_value() else {
            continue;
        };
        if c.rel != Rel::Ge {
            continue;
        }
        let flip = first.is_negative();
        let mut h = std::hash::DefaultHasher::new();
        for (a, k) in &c.lin.terms {
            a.hash(&mut h);
            if flip { -k } else { k.clone() }.hash(&mut h);
        }
        if flip {
            -&c.lin.constant
        } else {
            c.lin.constant.clone()
        }
        .hash(&mut h);
        by.entry(h.finish()).or_default().push(i);
    }
    let lin = |i: usize| match &gs[i] {
        Formula::Con(c) => &c.lin,
        _ => unreachable!("a row"),
    };
    let mut out = BTreeSet::new();
    // Complexity tradeoff: the rows of one hash are compared pairwise. Why: they are `t` and
    // `-t` for one `t`, two at most, since `Formula::and` holds equal rows once, unless two rows
    // share a 64-bit hash by chance. Trigger: such a collision; the size plays no part. Test:
    // `l01_39_reduced_product::pendants::rewritten_parts_give_one_answer_first_half`.
    // Naive version: every pair of rows compared, O(n²) for n rows; used: rows grouped by hash,
    // O(n) expected, pairs compared only within a group of one hash.
    for rows in by.values().filter(|rows| rows.len() > 1) {
        for (n, &i) in rows.iter().enumerate() {
            for &j in &rows[n + 1..] {
                if opposite_lins(lin(i), lin(j)) {
                    out.extend([i, j]);
                }
            }
        }
    }
    out
}

/// Whether `b` is `-a`.
fn opposite_lins(a: &Lin, b: &Lin) -> bool {
    a.constant == -&b.constant
        && a.terms.len() == b.terms.len()
        && (a.terms.iter().zip(&b.terms)).all(|((x, k), (y, m))| x == y && *k == -m)
}

/// The equation `c`, `t == 0`, with the sign of `t` whose first coefficient, in the order of
/// the names, is positive (of a row with no names, whose constant is not negative), which no
/// writing of the equation changes, or `None` when that is `c` as written. With `both`, and not
/// under a negation (`negated`), `t == 0 && -t == 0`; under a negation, where
/// `!(t == 0)` reads as `t - 1 >= 0 || -t - 1 >= 0` whichever sign `t` has, the one sign.
fn equation(c: &Con, negated: bool, both: bool) -> Option<Formula> {
    let eq = |lin: Lin| Formula::Con(Con { lin, rel: Rel::Eq });
    if both && !negated {
        return Some(Formula::and(vec![eq(c.lin.clone()), eq(c.lin.times(-1))]));
    }
    let lead = c.lin.terms.values().next().unwrap_or(&c.lin.constant);
    lead.is_negative().then(|| eq(c.lin.times(-1)))
}

/// `run`, and when the solver refuses it, `run` again on the path before DISJ-diff-fast and
/// DISJ-incremental ([`old_path`]), so that no question answered there is refused now. The
/// new path changes which disjuncts a search reads and with which rows, and a different
/// system may meet a refusal of the solver ([`Refusal::Growth`] on rows of three atoms or
/// more) that the old one did not.
// Complexity tradeoff: a question the new path refuses costs that refusal and the old path's
// work, which is O(n²) solves of its groups on a chain of `n` disjunctions (COMPLEXITY.md
// DECIDE-disj-chain). Why: which systems the solver refuses depends on their shape, which the
// projections change, so no check before the question tells which path it answers. Trigger:
// rows of three atoms or more whose projection the solver refuses. Test:
// `store::presburger::by_halves_against_old::answers_are_those_of_the_old_path`.
fn or_old<T>(run: impl Fn() -> Result<T, Refusal>) -> Result<T, Refusal> {
    match run() {
        Err(_) if !old_path() => {
            OLD_PATH.with(|o| o.set(true));
            let again = run();
            OLD_PATH.with(|o| o.set(false));
            again
        }
        r => r,
    }
}

/// [`decide`] of a formula whose names no longer matter ([`Renamed`]): the disjunctions that
/// [`absorb`] shows to remove no point removed, the rest settled for a search ([`settle`] with
/// `search`) and searched ([`found`]).
///
/// The rows the disjunctions imply ([`disjunction_hulls`]) are asked first with the base: they
/// change no answer, and show at once that the formula is empty with a bound past what its
/// disjuncts allow. When the solver refuses the formula with them (a row of three terms or
/// more joining a group may make an elimination enlarge it), it is asked as before, without
/// them, so no answer given without them becomes a refusal.
// Complexity tradeoff: a formula refused with the implied rows is asked twice, so it costs
// up to twice what it cost before; the first ask stops at the refusal.
// Naive version: one ask without the implied rows; used: the ask with them first, and without
// them only on a refusal, at most two asks of one size.
fn decide_inner(f: &Formula) -> Result<bool, Refusal> {
    decide_kept(f, None)
}

/// [`decide_inner`], which with `kept` adds to it a point of `f` where the search finds one.
/// Both search as [`has_point`] does, with [`probe_to`] stopped at the first point of the
/// parts it finds, which answers `true`, so the answer with `kept` is the answer without it.
/// A point is kept only once `f` is shown to hold at it, with the atoms that [`absorb`]
/// projected away given values ([`repair`]); a point of the parts at which `f` does not hold
/// so still answers `true` (S22-shapes-linear and PREIMAGE-slow-rounds, one first-point path).
fn decide_kept(f: &Formula, mut kept: Option<&mut Vec<Model>>) -> Result<bool, Refusal> {
    let (p, gone) = absorbed(f, &[]);
    let implied = if old_path() {
        Vec::new()
    } else {
        disjunction_hulls(&p.ors, &mut DeepHulls::default())
    };
    let point_of_f = |mut m: Model| {
        repair(&mut m, &gone);
        f.holds(&m).then_some(m)
    };
    let mut ask = |mut p: Parts, rows: Vec<Con>| -> Result<bool, Refusal> {
        p.cons.extend(rows);
        let p = match settle(p, true)? {
            None => return Ok(false),
            Some(p) if p.ors.is_empty() => return Ok(true),
            Some(p) => p,
        };
        let Some(kept) = kept.as_deref_mut() else {
            return has_point(p);
        };
        if let Ok(m) = pick(&p, true) {
            kept.extend(point_of_f(m));
            return Ok(true);
        }
        let mut first = Vec::new();
        let Some(q) = probe_to(p, &mut first, true)? else {
            return Ok(false);
        };
        match first.pop() {
            // The probe ran to its end, as [`found`]'s does.
            None => pick(&q, true).map(|m| {
                kept.extend(point_of_f(m));
                true
            }),
            // A point of the parts, so `f` has one ([`has_point`]); it is kept only where `f`
            // holds at it once the atoms [`absorb`] projected away are given values.
            Some(m) => {
                kept.extend(point_of_f(m));
                Ok(true)
            }
        }
    };
    if implied.is_empty() {
        return ask(p, implied);
    }
    match ask(p, implied) {
        Err(_) => ask(absorbed(f, &[]).0, Vec::new()),
        r => r,
    }
}

/// The new name of `a` under the renaming `to` of [`Renamed`]; an atom not in it keeps its own,
/// and a product its factors renamed.
fn rename(to: &HashMap<Atom, Arc<str>>, a: &Atom) -> Atom {
    let factor =
        |f: &Factor| (to.get(&f.atom())).map_or_else(|| f.clone(), |s| Factor::Sym(s.clone()));
    match a {
        Atom::Product(x, y) => Atom::product_of(factor(x), factor(y)),
        Atom::Sym(_) | Atom::Aux(_) => to
            .get(a)
            .map_or_else(|| a.clone(), |s| Atom::Sym(s.clone())),
    }
}

/// A formula with disjunctions, its atoms renamed by the structure of its constraints, so that
/// the search through its disjunctions ([`pick`], [`probe`], [`project_parts`]) reads one
/// formula under every naming of its variables. That search takes, in each disjunction, the
/// first disjunct that serves, in an order and at points that the names decide: [`nnf`] sorts
/// the disjuncts, comparing atoms by name, and the points come from [`solve`], whose model
/// breaks ties by place. The coloring of [`stable_colors`] over every constraint of the
/// formula, read as one system, depends on the structure alone; when it gives each atom its
/// own color, the atom of color rank `k` is renamed `#k`, which no written name is, with `k`
/// written with leading zeros to one width so that the names sort as the ranks do. A renaming
/// of the variables carries their colors with them, so every naming gives the one formula,
/// and every answer and refusal of it is renamed back. A product keeps its factors, renamed:
/// the coloring is given, for each product, a row joining it to its two factors, so that a factor
/// that occurs only in products has a color too.
///
/// Complexity tradeoff: when two atoms share a color ([`Naming::Tied`]), no renaming is
/// fixed by the structure, so the formula is not searched: [`decide`] and [`satisfiable`]
/// settle it by [`settle_as_sets`], whose result no order of its parts changes, answer it
/// when no two disjunctions left are linked ([`alone`]), test what is otherwise left with the
/// disjuncts their colors choose ([`settle_tied`], [`by_color`]), and refuse
/// with [`Refusal::Unordered`] when that finds no point; [`project_each`] projects it by
/// [`project_parts`] with `sets`, which asks only such questions and keeps every disjunction.
/// What is given up: a formula with such atoms whose point or whose emptiness only the search
/// shows (`true` or `false` becomes the refusal; [`settle_tied`]'s tradeoff), and in a
/// projection, the narrowing that showing a disjunct empty by a search would give. Why:
/// telling such atoms apart is canonical labeling
/// of the formula's graph, which individualization and refinement (McKay and Piperno's nauty
/// and Traces) do in time exponential in the worst case, while color refinement alone gives
/// one color to atoms that no automorphism exchanges (regular graphs, the Frucht graph);
/// searching as written made the answer depend on the names (5 of 1,000 systems of the test
/// below). Trigger: a formula with a disjunction, after negations are pushed in, two of whose
/// atoms the coloring does not tell apart. Tests:
/// `l01_38_presburger::names::disjunctions_whose_atoms_share_a_color` and
/// `l01_38_presburger::names::a_formula_whose_atoms_share_a_color_is_settled_or_refused`.
/// COMPLEXITY.md row NAME-ties-or. A complete solution would rename by a canonical labeling,
/// or search the disjunctions completely (DPLL(T)); each is exponential in the worst case.
struct Renamed {
    /// The formula renamed.
    f: Formula,
    /// The atom renamed `#k`, at `k`.
    from: Vec<Atom>,
    /// The new name of each atom renamed.
    to: HashMap<Atom, Arc<str>>,
}

/// How the names of a formula's atoms reach its answer ([`Renamed::of`]).
enum Naming {
    /// They do not: the formula has no disjunction, and [`solve`] decides it by structure
    /// alone.
    Kept,
    /// The formula renamed by the colors of its atoms.
    Renamed(Renamed),
    /// Two atoms or more share a color: the atoms of the least such color, by name, and the
    /// color of each atom, which no renaming changes.
    Tied(Vec<Atom>, HashMap<Atom, usize>),
}

impl Renamed {
    /// How the names of `f`'s atoms are kept from its answer: not at all when it has no
    /// disjunction, by renaming when each atom has its own color, and otherwise by settling
    /// it without a search ([`Naming::Tied`]).
    fn of(f: &Formula) -> Naming {
        if !f.chooses() {
            return Naming::Kept;
        }
        let mut cons = f.cons();
        let mut atoms: BTreeSet<Atom> = BTreeSet::new();
        for c in &cons {
            atoms.extend(c.lin.terms.keys().cloned());
        }
        let joins: Vec<Con> = (atoms.iter())
            .filter_map(|a| match a {
                Atom::Product(x, y) => {
                    let factors = Lin::atom(x.atom()).plus(&Lin::atom(y.atom()));
                    Some(Con::eq(
                        &Lin::atom(a.clone()).plus(&factors),
                        &Lin::default(),
                    ))
                }
                Atom::Sym(_) | Atom::Aux(_) => None,
            })
            .collect();
        for c in &joins {
            atoms.extend(c.lin.terms.keys().cloned());
        }
        cons.extend(joins.iter());
        let atoms: Vec<Atom> = atoms.into_iter().collect();
        let color = stable_colors(&atoms, &cons);
        let mut plain: Vec<usize> = (0..atoms.len())
            .filter(|&i| !matches!(atoms[i], Atom::Product(..)))
            .collect();
        plain.sort_unstable_by_key(|&i| color[i]);
        if let Some(w) = plain.windows(2).find(|w| color[w[0]] == color[w[1]]) {
            let tied = color[w[0]];
            let mut vars: Vec<Atom> = (plain.iter())
                .filter(|&&i| color[i] == tied)
                .map(|&i| atoms[i].clone())
                .collect();
            vars.sort_unstable();
            return Naming::Tied(vars, atoms.into_iter().zip(color).collect());
        }
        let from: Vec<Atom> = plain.iter().map(|&i| atoms[i].clone()).collect();
        // The rank is written with leading zeros to one width, so that names compare as their
        // ranks do: unpadded, `#10` sorts before `#2`, and [`nnf`] would hand the disjuncts of
        // a chain to [`pick`] out of rank order, where its first choices can fail and [`probe`]
        // runs (`l01_25_preimage_catalog::s22::chain_cross_live_scales`: 34.9 times the bytes
        // from 32 to 256 unpadded, against a limit of 24).
        let width = from.len().saturating_sub(1).to_string().len();
        let to: HashMap<Atom, Arc<str>> = (from.iter().enumerate())
            .map(|(k, a)| (a.clone(), Arc::from(format!("#{k:0width$}"))))
            .collect();
        let f = f.map_cons(&|c| {
            let terms = c.lin.terms.iter().map(|(a, k)| (rename(&to, a), k.clone()));
            Formula::Con(Con {
                lin: Lin {
                    terms: terms.collect(),
                    constant: c.lin.constant.clone(),
                },
                rel: c.rel,
            })
        });
        Naming::Renamed(Renamed { f, from, to })
    }

    /// The new name of `a`; an atom not in the formula keeps its own.
    fn there(&self, a: &Atom) -> Atom {
        rename(&self.to, a)
    }

    /// The atom that `a`, a new name or one kept, stands for.
    fn back(&self, a: &Atom) -> Atom {
        let of = |s: &Arc<str>| {
            let k = s.strip_prefix('#').and_then(|k| k.parse::<usize>().ok());
            k.map(|k| &self.from[k])
        };
        match a {
            Atom::Sym(s) => of(s).map_or_else(|| a.clone(), Atom::clone),
            Atom::Product(x, y) => {
                let factor = |f: &Factor| match f {
                    Factor::Sym(s) => of(s).and_then(Factor::of).unwrap_or_else(|| f.clone()),
                    Factor::Aux(_) => f.clone(),
                };
                Atom::product_of(factor(x), factor(y))
            }
            Atom::Aux(_) => a.clone(),
        }
    }

    /// `text`, written over the new names, with each written as the atom it stands for.
    fn back_text(&self, text: &str) -> String {
        let mut out = String::with_capacity(text.len());
        let mut rest = text;
        while let Some(at) = rest.find('#') {
            out.push_str(&rest[..at]);
            let digits = rest[at + 1..]
                .bytes()
                .take_while(u8::is_ascii_digit)
                .count();
            match rest[at + 1..at + 1 + digits].parse::<usize>() {
                Ok(k) if k < self.from.len() => out.push_str(&self.from[k].to_string()),
                _ => out.push_str(&rest[at..at + 1 + digits]),
            }
            rest = &rest[at + 1 + digits..];
        }
        out.push_str(rest);
        out
    }

    /// The refusal `e` of the renamed formula, written over the atoms as given.
    fn back_refusal(&self, e: Refusal) -> Refusal {
        match e {
            Refusal::Tie(t) => Refusal::Tie(Arc::new(Tie {
                vars: t.vars.iter().map(|v| self.back_text(v)).collect(),
                rows: t.rows.iter().map(|v| self.back_text(v)).collect(),
            })),
            Refusal::Unordered(t) => Refusal::Unordered(Arc::new(Tie {
                vars: t.vars.iter().map(|v| self.back_text(v)).collect(),
                rows: t.rows.iter().map(|v| self.back_text(v)).collect(),
            })),
            Refusal::Growth | Refusal::Shadows | Refusal::Disjuncts => e,
        }
    }
}

/// The refusal of a formula whose atoms `vars` share a color ([`Naming::Tied`]) and whose
/// settled parts `p` keep disjunctions: the atoms, and the disjunctions left that mention one
/// of them, or every disjunction left when none does. A disjunct is written as its own
/// constraints, with `&& ...` for the disjunctions within it.
fn unordered(vars: Vec<Atom>, p: &Parts) -> Refusal {
    let mentions = |ds: &[Rc<Parts>]| {
        ds.iter()
            .any(|d| vars.iter().any(|v| d.atoms().contains(v)))
    };
    let write = |ds: &[Rc<Parts>]| {
        let each = ds.iter().map(|d| {
            let mut cs: Vec<String> = d.cons.iter().map(Con::to_string).collect();
            if !d.ors.is_empty() {
                cs.push("...".to_owned());
            }
            match cs.len() {
                1 => cs.pop().expect("one"),
                _ => format!("({})", cs.join(" && ")),
            }
        });
        each.collect::<Vec<_>>().join(" || ")
    };
    let near: Vec<String> = (p.ors.iter())
        .filter(|ds| mentions(ds))
        .map(|ds| write(ds))
        .collect();
    let mut rows = if near.is_empty() {
        p.ors.iter().map(|ds| write(ds)).collect()
    } else {
        near
    };
    rows.sort_unstable();
    Refusal::Unordered(Arc::new(Tie {
        vars: vars.iter().map(Atom::to_string).collect(),
        rows,
    }))
}

/// The parts `p` settled as [`settle`] settles them, with each test of a disjunct made
/// against a base that no order of the parts can change, for a formula whose atoms share a
/// color ([`Naming::Tied`]), whose parts [`nnf`] sorts by name.
///
/// [`settle`] reads the disjunctions one at a time, and a disjunction left with one disjunct
/// joins the base at once, so a later disjunct is tested against more rows than an earlier
/// one; [`solve`] may refuse a system and decide a smaller one empty, so that order could
/// change which disjuncts are removed. Here the disjunctions are read in stages: each stage
/// tests every disjunction it holds against the base as the stage began, and only then adds
/// the disjuncts left alone to the base and makes their disjunctions the next stage, as
/// [`settle`] reads them in the same round. Each test then has the same rows whatever the
/// order, [`solve`] answers by the rows and not their order or names, and the base after each
/// stage is the same set of rows ([`Linked::meet`] keeps the least constant for a term and
/// comparison whatever the order), so by induction on the stages and rounds every naming
/// gives the same rounds, the same disjuncts removed and the same answer. A disjunct whose
/// constraints hold at the point found for the base is kept untested, as [`settle`] keeps it,
/// only while that point holds every row added to the base since: it is then a point of the
/// base and the disjunct, so the test would keep it too, and the point, which may depend on
/// the names, changes no result. The cost is that of [`settle`] with the points of later
/// stages unused, at most one test of each disjunct for each round.
///
/// While the point holds, a disjunct is tested first against the base projected onto the
/// atoms of its disjunction ([`stage_kernels`]), as [`settle`] and [`project_parts`] test
/// theirs, and against the base rows linked to it only when the solver refuses that. The
/// projection has a point with the disjunct exactly when the base has one, so where both
/// tests answer they answer alike, and the answer is a fact of the rows, not of their order.
/// On a chain of `n` stages with a disjunction at each, every test read the whole chain
/// before, `n` solves of `n` rows (COMPLEXITY.md PROJECT-dead2-quadratic).
///
/// A disjunct is kept when its test finds a point or is refused, so a disjunct kept is not
/// shown to have a point: [`AsSets::proven`] says which were. The last round adds nothing to
/// the base (a round that adds rows is not the last), so each disjunct left was tested in it
/// against the base as returned, and the marks of that round hold for the parts returned.
// Complexity tradeoff: naive version, each disjunct the base's point missed is solved with
// every base row linked to its atoms, a whole union-find group: on a chain of n stages, n
// solves of n rows, O(n²) (40.6 times the instructions from 16 to 128 stages). Used: while the
// point holds, a disjunct is tested first against the base projected by halves onto its own
// atoms (`stage_kernels`, `by_halves`), O((m + k) log k) for k disjunctions on a chain or
// tree of m rows (11.0 times). Tradeoffs: a projection the solver refuses sends the question
// to the whole group, O(n) that disjunct, as before; the hulls are unchanged. Tests
// `l01_38_presburger::omega::project_each_on_a_chained_pipeline_scales` and
// `omega::pipeline_stage_hulls_match_the_code_before`; COMPLEXITY.md row
// PROJECT-dead2-quadratic.
fn settle_as_sets(mut p: Parts) -> Result<Option<AsSets>, Refusal> {
    let mut base = Linked::reduced(std::mem::take(&mut p.cons));
    loop {
        let Some(model) = solve(&base.cons, !p.ors.is_empty())? else {
            return Ok(None);
        };
        let mut proven: Vec<Vec<bool>> = Vec::new();
        if p.ors.is_empty() {
            p.cons = base.cons;
            return Ok(Some(AsSets { p, proven }));
        }
        let mut changed = false;
        // Whether `model` is a point of the base as it now stands.
        let mut at_model = true;
        let mut stage = std::mem::take(&mut p.ors);
        while !stage.is_empty() {
            let mut alone: Vec<Rc<Parts>> = Vec::new();
            let kernels = stage_kernels(&base, &stage, at_model.then_some(&model));
            for (ds, kernel) in stage.into_iter().zip(kernels) {
                let n = ds.len();
                // Each disjunct not shown empty, and whether it is shown to have a point.
                let (mut live, shown): (Vec<Rc<Parts>>, Vec<bool>) = (ds.into_iter())
                    .filter_map(|d| {
                        if at_model && d.cons.iter().all(|c| c.holds_linear(&model)) {
                            return Some((d, true));
                        }
                        // Asked of the base projected onto the disjunction's atoms, which has
                        // a point with the disjunct exactly when the base has one; when the
                        // solver refuses that, of the base's groups, as before.
                        if let Some(k) = &kernel {
                            let mut cs = k.around(&d.cons);
                            cs.extend(d.cons.iter());
                            match solve(&cs, false) {
                                Ok(None) => return None,
                                Ok(Some(_)) => return Some((d, true)),
                                Err(_) => {}
                            }
                        }
                        let mut cs = base.around(&d.cons);
                        cs.extend(d.cons.iter());
                        match solve(&cs, false) {
                            Ok(None) => None,
                            Ok(Some(_)) => Some((d, true)),
                            Err(_) => Some((d, false)),
                        }
                    })
                    .unzip();
                changed |= live.len() < n;
                match live.len() {
                    0 => return Ok(None),
                    // The others are shown empty, so the formula's points are those of the
                    // base with this one, which the next round solves.
                    1 => alone.push(live.pop().expect("one")),
                    _ => {
                        p.ors.push(live);
                        proven.push(shown);
                    }
                }
            }
            // Rows added to the base are solved again in the next round.
            changed |= !alone.is_empty();
            stage = Vec::new();
            for d in &alone {
                at_model &= d.cons.iter().all(|c| c.holds_linear(&model));
                d.cons.iter().for_each(|c| {
                    base.meet(c.clone());
                });
                stage.extend(d.ors.iter().cloned());
            }
        }
        if !changed {
            p.cons = base.cons;
            return Ok(Some(AsSets { p, proven }));
        }
    }
}

/// For each disjunction of `stage`, the rows of `base` projected ([`by_halves`]) onto the atoms
/// of its disjuncts' own constraints, when `model`, a point of the base, is given and a
/// disjunct does not hold there, so that one is asked; otherwise `None` for each. The stage
/// adds no rows to the base while it is tested, so every projection is of the base as the
/// stage began. On a chain or a tree of `m` rows, `k` disjunctions cost O((m + k) log k)
/// instead of a solve of the whole linked group for each disjunct.
fn stage_kernels(
    base: &Linked,
    stage: &[Vec<Rc<Parts>>],
    model: Option<&Model>,
) -> Vec<Option<Linked>> {
    let mut kernels: Vec<Option<Linked>> = stage.iter().map(|_| None).collect();
    let asks = model.is_some_and(|m| {
        (stage.iter().flatten()).any(|d| !d.cons.iter().all(|c| c.holds_linear(m)))
    });
    if !asks || old_path() {
        return kernels;
    }
    let keep: Vec<BTreeSet<Atom>> = (stage.iter())
        .map(|ds| {
            (ds.iter())
                .flat_map(|d| d.cons.iter().flat_map(|c| c.lin.terms.keys().cloned()))
                .collect()
        })
        .collect();
    let rows: Vec<Con> = (base.around_atoms(keep.iter().flatten()).into_iter())
        .cloned()
        .collect();
    let filled: Result<(), ()> = by_halves(rows, &keep, |i, k| {
        kernels[i] = k.map(Linked::of);
        Ok(Vec::new())
    });
    filled.expect("no leaf fails");
    kernels
}

/// The parts that [`settle_as_sets`] leaves, and for each disjunction left, in the order of
/// `p.ors`, whether each of its disjuncts is shown to have a point with the base: [`solve`]
/// found one with the base rows linked to it, or its constraints hold at a point of the base.
/// A disjunct kept because [`solve`] refused it is not.
struct AsSets {
    p: Parts,
    proven: Vec<Vec<bool>>,
}

/// What [`settle_tied`] leaves of a formula whose atoms share a color.
enum Settled {
    /// No point.
    Empty,
    /// A point, or an empty model when none was asked for.
    Point(Model),
    /// The parts, with disjunctions that settling leaves and no disjunct taken by color.
    Left(Parts),
}

/// `f`, whose atoms share a color ([`Naming::Tied`]) and have the colors `color`, settled
/// ([`settle_as_sets`]) and then, when disjunctions are left, answered when no two of them are
/// linked ([`alone`]), or else tested with the disjuncts that their colors choose
/// ([`by_color`]): a point of the base with those disjuncts is a point of `f`. With `want`,
/// the point is built.
///
/// Complexity tradeoff: a formula with linked disjunctions left after settling is answered
/// only when each disjunction has one least disjunct by [`by_color`]'s key and the base with
/// those disjuncts has a point; otherwise it is `Left`, which [`decide`] and [`satisfiable`]
/// refuse with [`Refusal::Unordered`]. What is given up: such a formula whose only points lie
/// under other choices, or two of whose disjuncts tie on the key, and every such formula with no
/// point (`false` becomes the refusal; [`settle_as_sets`] still shows no point when a
/// disjunction loses every disjunct against the base, and the rows the disjunctions imply
/// show it when the base has no point beside them). Why: a search that tries the
/// disjuncts in turn needs an order among those of equal key, and that order would come from
/// the names; testing every disjunct with every other disjunction instead, as the probe that
/// this replaced did, cost the disjuncts times a settling for each round, cubic on a star of
/// tied leaves with a disjunction each (8 to 64 leaves: 22 ms to 10.8 s). Here the test is one
/// [`solve`] after the settling, and the links are read once. Trigger: a formula with two
/// linked disjunctions left after settling, two of whose atoms the coloring does not tell
/// apart. Tests:
/// `l01_38_presburger::names::a_formula_whose_atoms_share_a_color_is_settled_or_refused`,
/// `l01_38_presburger::names::decide_on_tied_disjunctions_scales` and
/// `l01_38_presburger::names::decide_on_separate_tied_disjunctions_scales`. COMPLEXITY.md row
/// NAME-ties-or. A complete solution would search the disjunctions completely (DPLL(T)),
/// exponential in the disjunctions in the worst case, or tell the atoms apart by a canonical
/// labeling, exponential in the worst case too.
fn settle_tied(f: &Formula, color: &HashMap<Atom, usize>, want: bool) -> Result<Settled, Refusal> {
    let (p, gone) = absorbed(f, &[]);
    // The rows the disjunctions imply ([`disjunction_hulls`]) hold at every point of `f` and
    // depend on its rows alone, not on the names, so a base with no point beside them shows
    // `f` empty at once: a nest every path of which is empty (PRES-nest-empty). They serve
    // that test alone: settled with them in the base, the random guarded chains of
    // `l01_25_preimage_catalog::s22` made fewer boxes exact (49 against 53), so a base with a
    // point beside them is settled as before.
    if !old_path() && !p.ors.is_empty() {
        let implied = disjunction_hulls(&p.ors, &mut DeepHulls::default());
        if !implied.is_empty() {
            let rows: Vec<&Con> = p.cons.iter().chain(implied.iter()).collect();
            if let Ok(None) = solve(&rows, false) {
                return Ok(Settled::Empty);
            }
        }
    }
    let Some(AsSets { p, proven }) = settle_as_sets(p)? else {
        return Ok(Settled::Empty);
    };
    // Settling solved the base, and showed a point of the base with each disjunct that
    // `alone` takes (it takes only those [`AsSets::proven`] marks), so a point need not be
    // found again unless it is wanted.
    let lone = alone(&p, &proven);
    if !want && (p.ors.is_empty() || lone.is_some()) {
        return Ok(Settled::Point(Model::new()));
    }
    let Some(cons) = lone.or_else(|| by_color(&p, color)) else {
        return Ok(Settled::Left(p));
    };
    Ok(match solve(&cons, want)? {
        Some(mut m) => {
            if want {
                repair(&mut m, &gone);
            }
            Settled::Point(m)
        }
        None => Settled::Left(p),
    })
}

/// The constraints of the settled parts `p` with one disjunct of each disjunction, when no
/// two disjunctions are linked, through rows of the base or through each other's disjuncts,
/// and each has a disjunct with no disjunction of its own that `proven` marks; otherwise
/// `None`. Settling left disjuncts that it did not show empty, and `proven`
/// ([`AsSets::proven`]) marks those shown to have a point with the base: each was tested
/// against the rows linked to it, or holds at a point of the base as it now stands
/// ([`settle_as_sets`]). A disjunct that [`solve`] refused is not marked and never taken,
/// even when it comes first: taking it would read a refusal as a point. The rows a disjunct
/// is linked to are linked to no other disjunction, so the points of separate groups
/// combine into one point of the base with every disjunct taken. Whether `p` has such a
/// point is then fixed by the links, which no renaming changes; the disjunct taken in each
/// disjunction is the first marked one with no disjunction of its own, which the names
/// order, so only the point found by [`satisfiable`] may change with them. The groups are
/// found by union and find over the atoms with path halving, linking each row and each
/// disjunction's atoms.
fn alone<'a>(p: &'a Parts, proven: &[Vec<bool>]) -> Option<Vec<&'a Con>> {
    fn find(parent: &mut [usize], mut i: usize) -> usize {
        while parent[i] != i {
            parent[i] = parent[parent[i]];
            i = parent[i];
        }
        i
    }
    let mut ids: HashMap<&'a Atom, usize> = HashMap::new();
    let mut parent: Vec<usize> = Vec::new();
    // Links the atoms given into one group, and gives the group's root, or `None` when no
    // atom is given.
    let mut link = |atoms: &mut dyn Iterator<Item = &'a Atom>| -> Option<usize> {
        let mut root: Option<usize> = None;
        for a in atoms {
            let next = parent.len();
            let i = *ids.entry(a).or_insert(next);
            if i == next {
                parent.push(i);
            }
            let r = find(&mut parent, i);
            match root {
                None => root = Some(r),
                Some(q) if q != r => parent[r] = q,
                Some(_) => {}
            }
        }
        root
    };
    p.cons.iter().for_each(|c| {
        link(&mut c.lin.terms.keys());
    });
    let roots: Vec<Option<usize>> = (p.ors.iter())
        .map(|ds| link(&mut ds.iter().flat_map(|d| d.atoms().iter())))
        .collect();
    let mut seen = vec![false; parent.len()];
    for r in roots.into_iter().flatten() {
        let r = find(&mut parent, r);
        if std::mem::replace(&mut seen[r], true) {
            return None;
        }
    }
    let mut cons: Vec<&Con> = p.cons.iter().collect();
    for (ds, shown) in p.ors.iter().zip(proven) {
        let (d, _) = (ds.iter().zip(shown)).find(|&(d, &s)| s && d.ors.is_empty())?;
        cons.extend(d.cons.iter());
    }
    Some(cons)
}

/// The key of a constraint that no renaming of its atoms changes, given their colors: its
/// comparison, its constant, and the color and coefficient of each term, sorted. An atom with
/// no color, which the formula colored has not, reads as the greatest color.
fn color_key<'a>(
    c: &'a Con,
    color: &HashMap<Atom, usize>,
) -> (Rel, &'a Int, Vec<(usize, &'a Int)>) {
    let mut terms: Vec<(usize, &Int)> = (c.lin.terms.iter())
        .map(|(a, k)| (color.get(a).copied().unwrap_or(usize::MAX), k))
        .collect();
    terms.sort_unstable();
    (c.rel, &c.lin.constant, terms)
}

/// The constraints of the settled parts `p` with, in each disjunction, and in each disjunction
/// of a disjunct taken, the disjunct whose constraints have the least sorted list of
/// [`color_key`]s, or `None` when two disjuncts of a disjunction share the least list. Each
/// choice reads one disjunction and the colors, which a renaming carries with the atoms, so
/// every naming takes the same disjuncts, renamed; the constraints are a set to [`solve`],
/// which answers by the rows and not their order or names. The nest is read on an explicit
/// stack, and each disjunct's key costs its constraints' terms times their logarithm.
fn by_color<'a>(p: &'a Parts, color: &HashMap<Atom, usize>) -> Option<Vec<&'a Con>> {
    let mut cons: Vec<&Con> = p.cons.iter().collect();
    let mut stack: Vec<&[Rc<Parts>]> = p.ors.iter().map(Vec::as_slice).collect();
    while let Some(ds) = stack.pop() {
        let key = |d: &'a Parts| {
            let mut k: Vec<_> = d.cons.iter().map(|c| color_key(c, color)).collect();
            k.sort_unstable();
            k
        };
        let mut least: Option<(_, &Parts)> = None;
        let mut tied = false;
        for d in ds {
            let k = key(d);
            match &least {
                Some((l, _)) if k > *l => {}
                Some((l, _)) if k == *l => tied = true,
                _ => {
                    least = Some((k, d));
                    tied = false;
                }
            }
        }
        let (_, d) = least?;
        if tied {
            return None;
        }
        cons.extend(d.cons.iter());
        stack.extend(d.ors.iter().map(Vec::as_slice));
    }
    Some(cons)
}

/// A point of the propagated parts `p`, or `None` when the search removes every disjunct of
/// a disjunction. Where the [`pick`] after the probe fails, or the probe refuses, after the
/// probe has found a point, that point is the answer (the first one found), not the refusal,
/// so that [`satisfiable`] answers wherever [`decide`] does ([`has_point`]).
fn found(p: Parts) -> Result<Option<Model>, Refusal> {
    if let Ok(m) = pick(&p, true) {
        return Ok(Some(m));
    }
    let mut points = Vec::new();
    let refused = match probe_to(p, &mut points, false) {
        Ok(None) => return Ok(None),
        Ok(Some(p)) => match pick(&p, true) {
            Ok(m) => return Ok(Some(m)),
            Err(why) => why,
        },
        Err(why) => why,
    };
    points
        .into_iter()
        .next()
        .map_or(Err(refused), |m| Ok(Some(m)))
}

/// Whether the propagated parts `p` have a point: [`found`], but the probe stops at the first
/// point it finds ([`probe_to`]), which is a point of `p`, where [`found`] probes every
/// disjunct and then asks [`pick`] for a point again. On a membership in a set of `h` pieces
/// next to disjunctions that the first [`pick`] reads the wrong way, each piece needs a point
/// of its own, so a probe to the end found `h` points, each at the cost of the whole formula,
/// `O(h^2)`, to answer a question its first point answers (S22-shapes-linear: shape 0 of
/// `counted_shapes(spread_remainder_chain(k))` over `x` with `64 k` holes).
///
/// The answer is `found(p)?.is_some()`: the probe is the same up to its first point, a probe
/// that finds none runs to the end as before, and [`found`] answers with that point where its
/// own search after it refuses.
// Complexity tradeoff: naive version, `found` probing every disjunct to the end, O(h²) here
// (21.5 s at k = 32). Used: the probe stops at its first point, linear in the pieces (6.75
// times the instructions in the scaling test below). Tradeoffs: a probe that finds no point
// still runs to the end; `satisfiable` still probes to the end, so its model is main's. Tests
// `l01_25_preimage_catalog::s22::the_box_of_a_chain_over_many_holes_is_tested_in_linear_work`
// and `l01_38_presburger::model::satisfiable_agrees_with_decide_on_disjunctions_of_unit_rows`;
// COMPLEXITY.md row S22-shapes-linear.
fn has_point(p: Parts) -> Result<bool, Refusal> {
    if pick(&p, true).is_ok() {
        return Ok(true);
    }
    let mut points = Vec::new();
    match probe_to(p, &mut points, true)? {
        None => Ok(false),
        Some(_) if !points.is_empty() => Ok(true),
        Some(p) => pick(&p, true).map(|_| true),
    }
}

/// `c` with each atom outside `free` replaced by its value in `model`.
fn specialize_con(c: &Con, free: &BTreeSet<Atom>, model: &Model) -> Con {
    let mut terms = BTreeMap::new();
    let mut k = c.lin.constant.clone();
    for (a, coef) in &c.lin.terms {
        if free.contains(a) {
            terms.insert(a.clone(), coef.clone());
        } else if let Some(val) = model.get(a) {
            k = &k + &(coef * val);
        }
    }
    Con {
        lin: Lin { terms, constant: k },
        rel: c.rel,
    }
}
/// The atoms of `extra` that no constraint of two or more atoms taken so far reads, re-solved
/// with every other atom held at `model`: with `extra` specialized there and those atoms'
/// bounds. A point found is a point of the constraints taken with `extra`, since none of
/// them reads a re-solved atom but through its bounds. O(`extra` log n): on `k` disjunctions
/// each of whose disjuncts brings atoms of its own beside one read by all (a remainder by a
/// term `x mod (n + i)` for each `i`, PRES-mod-conjuncts), [`local_repair`] costs the `k`
/// constraints that read the shared atom for each disjunct, O(k²) in all.
fn own_repair(near: &Near, model: &Model, extra: &[Con]) -> Option<Model> {
    own_repair_in(&[near], &|_| false, model, extra)
}

/// [`own_repair`] with the constraints taken indexed in several parts, `nears`, and the atoms
/// for which `fixed` holds kept at `model` too.
fn own_repair_in(
    nears: &[&Near],
    fixed: &dyn Fn(&Atom) -> bool,
    model: &Model,
    extra: &[Con],
) -> Option<Model> {
    let own: BTreeSet<Atom> = (extra.iter())
        .flat_map(|c| c.lin.terms.keys())
        .filter(|a| !fixed(a) && nears.iter().all(|n| !n.by_atom.contains_key(*a)))
        .cloned()
        .collect();
    if own.is_empty() {
        return None;
    }
    let mut local = Vec::with_capacity(extra.len());
    for c in extra {
        match c.lin.terms.keys().any(|a| own.contains(a)) {
            true => local.push(specialize_con(c, &own, model)),
            false if c.holds_linear(model) => {}
            false => return None,
        }
    }
    for a in &own {
        nears.iter().for_each(|n| n.bounds(a, &mut local));
    }
    let mut m = solve(&local, true).ok()??;
    for a in own {
        m.entry(a).or_insert(Int::ZERO);
    }
    Some(m)
}

/// The variables of `extra` re-solved with their neighbors fixed at `model`: with `extra`, the
/// constraints taken so far that link a variable of `extra` to others, specialized at `model`,
/// and each variable's bounds.
fn local_repair(acc: &[Con], near: &Near, model: &Model, extra: &[Con]) -> Option<Model> {
    let seed: BTreeSet<Atom> = extra
        .iter()
        .flat_map(|c| c.lin.terms.keys().cloned())
        .collect();
    if seed.is_empty() {
        return None;
    }
    let mut ids = BTreeSet::new();
    let mut local: Vec<Con> = extra.to_vec();
    for a in &seed {
        if let Some(v) = near.by_atom.get(a) {
            ids.extend(v.iter().copied());
        }
        near.bounds(a, &mut local);
    }
    for id in ids {
        local.push(specialize_con(&acc[id], &seed, model));
    }
    let mut m = solve(&local, true).ok()??;
    for a in seed {
        m.entry(a).or_insert(Int::ZERO);
    }
    Some(m)
}

/// Whether `extra` is shown to meet the constraints taken so far nowhere by a part of them:
/// `extra`, the bounds of its atoms, and the constraints taken so far whose atoms are all
/// atoms of `extra`. When these have no point, neither has the whole; `false` shows nothing.
/// The cost is that of [`local_repair`]'s constraints, not of the groups `extra` touches.
fn local_refute(acc: &[Con], near: &Near, extra: &[Con]) -> bool {
    let seed: BTreeSet<&Atom> = extra.iter().flat_map(|c| c.lin.terms.keys()).collect();
    let mut ids = BTreeSet::new();
    let mut bounds = Vec::new();
    for a in &seed {
        if let Some(v) = near.by_atom.get(*a) {
            let within = |i: &usize| acc[*i].lin.terms.keys().all(|b| seed.contains(b));
            ids.extend(v.iter().copied().filter(within));
        }
        near.bounds(a, &mut bounds);
    }
    let local: Vec<&Con> = (extra.iter())
        .chain(&bounds)
        .chain(ids.into_iter().map(|i| &acc[i]))
        .collect();
    matches!(solve(&local, false), Ok(None))
}

thread_local! {
    /// The parts [`Parts::witness`] has tested on this thread since [`parts_tested`] was last
    /// called.
    static TESTED: Cell<u64> = const { Cell::new(0) };
}

/// The number of parts (a disjunct and its own constraints) that the search for a point has
/// tested against its values on this thread since the last call, which resets it. A test reads
/// it to count that work directly.
pub fn parts_tested() -> u64 {
    TESTED.replace(0)
}

/// A stamp no search has used before ([`Parts::witness`]); zero is never one.
fn fresh_stamp() -> u64 {
    static NEXT: AtomicU64 = AtomicU64::new(1);
    NEXT.fetch_add(1, AtomicOrdering::Relaxed)
}

/// A point of `p`, taking for each disjunction in turn the first disjunct that meets the
/// constraints taken so far, or a refusal when none does. Unless `deep`, the disjunctions
/// within a disjunct are not read: the model is then a point of the parts with each disjunct
/// cut to its own constraints, which have more points than the parts.
///
/// Complexity tradeoff: the choice of a disjunct is never undone, so a formula whose point
/// needs an earlier disjunction decided another way gets `Refusal::Disjuncts` ("not decided")
/// here; `probe` then removes the disjuncts it shows empty, and what is still refused stays
/// refused. Why: finding a point of a conjunction of disjunctions of linear rows is
/// NP-complete (graph 3-coloring is such a formula: one disjunction of three colors per
/// node, one row per edge), so a search that backtracks is exponential in the disjunctions.
/// Trigger: two or more disjunctions whose disjuncts conflict through shared variables,
/// whatever the size. Tests: `l01_38_presburger::omega::each_cause_of_a_refusal_has_its_own_message`
/// (four tasks in three slots), `l01_38_presburger::omega::a_disjunct_refused_by_the_solver_is_reported_by_its_own_cause`.
/// COMPLEXITY.md rows S16 and S18. A complete solution would backtrack over the disjuncts
/// (DPLL(T) with learned conflicts), exponential in the worst case.
///
/// The disjunctions are first read with [`by_halves`] (`fast`), each disjunct that no point
/// answers asked of the constraints taken projected onto its disjunction's atoms; a disjunct
/// taken so leaves the model a point of the constraints taken before it only, so until the
/// model is found again, by one solve of the constraints taken, the disjuncts are asked of
/// the projection alone. When that reading is refused, the disjunctions are read again as
/// before, each disjunct asked of the groups of the constraints taken (not `fast`), so no
/// formula is refused that was not before. Either reading gives a point of `p`, but not
/// always the same one.
// Complexity tradeoff: a failed fast reading is followed by the reading of before, which
// asks each disjunct that no point answers of its whole group: on `n` disjunctions over one
// group of `n` rows whose point needs an earlier choice undone, O(n²), as before this plan
// item (DISJ-incremental). No answer is given up.
fn pick(p: &Parts, deep: bool) -> Result<Model, Refusal> {
    pick_taking(p, deep).map(|(m, _)| m)
}

/// [`pick`], with the disjuncts it took: each holds at the point, those below a disjunct taken
/// included when `deep`. A disjunct holding at the point that the search did not take is not
/// among them.
fn pick_taking(p: &Parts, deep: bool) -> Result<(Model, Vec<&Parts>), Refusal> {
    if old_path() {
        return pick_by(p, deep, false);
    }
    pick_by(p, deep, true).or_else(|_| pick_by(p, deep, false))
}

/// [`pick_taking`], reading the disjunctions by halves when `fast`.
fn pick_by(p: &Parts, deep: bool, fast: bool) -> Result<(Model, Vec<&Parts>), Refusal> {
    // The disjuncts taken, each with its constraints among those taken, which the model is a
    // point of at the end.
    let mut took: Vec<&Parts> = Vec::new();
    let mut model = solve(&p.cons, true)?.ok_or(Refusal::Disjuncts)?;
    let mut acc = Linked::default();
    let mut near = Near::default();
    take(&p.cons, &mut acc, &mut near);
    // The disjunctions left, in the order they are read (the last first); only the disjuncts
    // taken are entered.
    let batch: Vec<&[Rc<Parts>]> = p.ors.iter().rev().map(Vec::as_slice).collect();
    // The disjuncts that hold at the model, found by [`Parts::witness`].
    let mut held: Vec<&Parts> = Vec::new();
    // A new stamp each time the model changes, under which a part found not to hold at the
    // model is not read again ([`Parts::witness`]).
    let mut stamp = fresh_stamp();
    // Whether a disjunction may be asked of the solver: one with no disjunct holding at the
    // model, which only a taken disjunct changes.
    let asks = fast
        && !batch.iter().all(|ds| {
            ds.iter()
                .any(|d| d.cons.iter().all(|c| c.holds_linear(&model)))
        });
    // Whether the model is a point of the constraints taken: not after a disjunct is taken on
    // the projection's word, until it is found again.
    let mut valid = true;
    let keep: Vec<BTreeSet<Atom>> = if asks {
        (batch.iter())
            .map(|ds| {
                (ds.iter())
                    .flat_map(|d| d.cons.iter().flat_map(|c| c.lin.terms.keys().cloned()))
                    .collect()
            })
            .collect()
    } else {
        Vec::new()
    };
    let rows: Vec<Con> = (acc.around_atoms(keep.iter().flatten()).into_iter())
        .cloned()
        .collect();
    // Reads the disjunction at `i` and the disjunctions below the disjuncts it takes, given the
    // constraints taken projected onto its atoms (`None`: not known), and returns the
    // constraints it takes. The model is a point of the constraints taken throughout.
    let mut one = |i: usize, kernel: Option<Vec<Con>>| -> Result<Vec<Con>, Refusal> {
        let mut added: Vec<Con> = Vec::new();
        // The disjunctions below, read before the next of `batch`, as a queue of all of them
        // would read them; the projection is of the atoms of the first alone.
        let mut queue: Vec<&[Rc<Parts>]> = vec![batch[i]];
        let mut kernel = kernel.map(Linked::of);
        'next: while let Some(ds) = queue.pop() {
            let kernel = kernel.take();
            if !valid && kernel.is_none() {
                model = solve(&acc.cons, true)?.ok_or(Refusal::Disjuncts)?;
                stamp = fresh_stamp();
                valid = true;
            }
            // A disjunct that holds at the model is taken with the disjunct that holds first in
            // each disjunction below it, which reading those disjunctions one by one would
            // take, the model being unchanged; so the nest below is read once, not again at
            // each level.
            for d in ds.iter().filter(|_| valid) {
                held.clear();
                let holds = if deep {
                    d.witness(&model, stamp, &mut held)
                } else {
                    held.push(d);
                    d.cons.iter().all(|c| c.holds_linear(&model))
                };
                if holds {
                    for h in &held {
                        take(&h.cons, &mut acc, &mut near);
                        added.extend(h.cons.iter().cloned());
                    }
                    took.extend(held.iter().copied());
                    continue 'next;
                }
            }
            let mut taken: Option<(&Parts, Model)> = None;
            let mut why = Refusal::Disjuncts;
            for d in ds.iter().filter(|_| valid) {
                // A disjunct whose constraints hold at the model, though the disjunctions below
                // it may not, is taken with the model unchanged, so that the parts found not to
                // hold below it are not read again.
                if d.cons.iter().all(|c| c.holds_linear(&model)) {
                    taken = Some((d, Model::new()));
                    break;
                }
                if let Some(m) = local_repair(&acc.cons, &near, &model, &d.cons) {
                    taken = Some((d, m));
                    break;
                }
            }
            for d in ds {
                if taken.is_some() {
                    break;
                }
                // Asked of the constraints taken projected onto the disjunction's atoms, which
                // have a point with the disjunct exactly when the constraints taken do, and
                // which give one there; the model takes the projection's point on the
                // disjunct's group, whose atoms are kept. When the solver refuses that, of the
                // groups of the constraints taken, as before.
                if let Some(k) = &kernel {
                    let mut cs = k.around(&d.cons);
                    cs.extend(d.cons.iter());
                    match solve(&cs, false) {
                        Ok(None) => continue,
                        Ok(Some(_)) => {
                            taken = Some((d, Model::new()));
                            valid = false;
                            break;
                        }
                        Err(_) => {}
                    }
                }
                if !valid {
                    model = solve(&acc.cons, true)?.ok_or(Refusal::Disjuncts)?;
                    stamp = fresh_stamp();
                    valid = true;
                }
                let mut cs = acc.around(&d.cons);
                cs.extend(d.cons.iter());
                match solve(&cs, true) {
                    Ok(Some(m)) => {
                        taken = Some((d, m));
                        break;
                    }
                    Ok(None) => {}
                    Err(r) => why = r,
                }
            }
            let Some((d, m)) = taken else {
                return Err(why);
            };
            // A change of any value drops every mark, not only the marks of the parts that
            // mention it, yet no part is read again below each level: a part is marked by the
            // first walk that reaches it and fails, at the disjunction `D` popped then. The
            // disjunctions popped after `D` and before the one that holds the part are those of
            // the disjuncts taken on the way down, read last to first as that walk read them;
            // each was found to hold by that walk, and each disjunct on the way has its
            // constraints holding, so it is taken with the model unchanged. A disjunct taken
            // earlier in its disjunction leaves the part unread. So the model is the same when
            // the part is reached again, and its mark holds. Test `l01_39_reduced_product::deep_condition::the_search_for_a_point_tests_each_part_of_a_deep_test_a_bounded_number_of_times`
            // counts the parts tested ([`parts_tested`]) (COMPLEXITY S31).
            if m.iter().any(|(a, v)| model.get(a) != Some(v)) {
                stamp = fresh_stamp();
            }
            model.extend(m);
            take(&d.cons, &mut acc, &mut near);
            took.push(d);
            added.extend(d.cons.iter().cloned());
            if deep {
                queue.extend(d.ors.iter().map(Vec::as_slice));
            }
        }
        Ok(added)
    };
    if asks {
        by_halves(rows, &keep, &mut one)?;
    } else {
        (0..batch.len()).try_for_each(|i| one(i, None).map(drop))?;
    }
    if !valid {
        model = solve(&acc.cons, true)?.ok_or(Refusal::Disjuncts)?;
    }
    Ok((model, took))
}

/// Adds the constraints of a disjunct taken, a bound taken again kept once ([`Linked::meet`]).
/// A bound on one atom that [`Linked::meet`] puts in the place of a weaker one still tightens
/// that atom's bounds in `near`; a constraint of more atoms put in place keeps its atoms, so
/// its entries in `near` stand.
fn take(cons: &[Con], acc: &mut Linked, near: &mut Near) {
    for c in cons {
        let i = acc.cons.len();
        if acc.meet(c.clone()) || c.lin.terms.len() == 1 {
            near.add(i, c);
        }
    }
}

/// The constraints taken so far by [`pick`] or [`settle`], indexed for [`local_repair`]: each constraint of
/// two or more atoms under each of its atoms, and the constraints of one atom as that atom's
/// bounds. A repair then costs the constraints that link its atoms to others and two bounds
/// for each atom, not every constraint an atom has had alone: on a chain of `k` guards
/// `i >= j` on one input, listing them made the repair of each of the `k` levels cost `k`.
#[derive(Default)]
struct Near {
    by_atom: BTreeMap<Atom, Vec<usize>>,
    /// The least and the greatest value of an atom; a least above the greatest leaves none.
    one: BTreeMap<Atom, (Option<Int>, Option<Int>)>,
}

impl Near {
    /// Adds the constraint `c`, numbered `i` among those taken.
    fn add(&mut self, i: usize, c: &Con) {
        let Some((a, lo, hi)) = one_bound(c) else {
            for a in c.lin.terms.keys() {
                self.by_atom.entry(a.clone()).or_default().push(i);
            }
            return;
        };
        self.tighten(a, lo, hi);
    }

    /// Moves the least value of `a` up to `lo` and its greatest down to `hi`, where they are
    /// given and tighter.
    fn tighten(&mut self, a: &Atom, lo: Option<Int>, hi: Option<Int>) {
        narrow_to(&mut self.one, a, lo, hi);
    }

    /// Whether some constraint of one atom in `cons` leaves that atom no value within its
    /// bounds here.
    fn refutes(&self, cons: &[Con]) -> bool {
        cons.iter().filter_map(one_bound).any(|(a, lo, hi)| {
            let (l, h) = self
                .one
                .get(a)
                .map_or((None, None), |(l, h)| (l.as_ref(), h.as_ref()));
            let lo = [l, lo.as_ref()].into_iter().flatten().max();
            let hi = [h, hi.as_ref()].into_iter().flatten().min();
            matches!((lo, hi), (Some(lo), Some(hi)) if lo > hi)
        })
    }

    /// Pushes the bounds of `a` onto `out` as constraints.
    fn bounds(&self, a: &Atom, out: &mut Vec<Con>) {
        let Some((lo, hi)) = self.one.get(a) else {
            return;
        };
        let x = Lin::atom(a.clone());
        if let Some(lo) = lo {
            out.push(Con::ge(&x, &Lin::constant(lo.clone())));
        }
        if let Some(hi) = hi {
            out.push(Con::ge(&Lin::constant(hi.clone()), &x));
        }
    }
}

/// The atom of a constraint of one atom, with the least and the greatest value it allows that
/// atom; a least above the greatest allows none.
fn one_bound(c: &Con) -> Option<(&Atom, Option<Int>, Option<Int>)> {
    let mut terms = c.lin.terms.iter();
    let (Some((a, coef)), None) = (terms.next(), terms.next()) else {
        return None;
    };
    // `coef·a + k` compared with zero.
    let k = &c.lin.constant;
    let m = coef.abs();
    let (lo, hi) = match c.rel {
        // `a >= -k / coef`, rounded up.
        Rel::Ge if coef.is_positive() => (Some(-&k.div_floor(&m)), None),
        // `a <= k / |coef|`, rounded down.
        Rel::Ge => (None, Some(k.div_floor(&m))),
        Rel::Eq if k.mod_floor(&m).is_zero() => {
            let v = -&k.div_floor(&m);
            let v = if coef.is_positive() { v } else { -&v };
            (Some(v.clone()), Some(v))
        }
        // No integer `a` has `coef·a == -k`.
        Rel::Eq => (Some(Int::ONE), Some(Int::ZERO)),
    };
    Some((a, lo, hi))
}

/// Constraints grouped by the variables they share, so that a question about a few variables
/// solves only the constraints it can meet: variables that share no constraint do not interact,
/// and the rest are known to have a point.
#[derive(Default)]
struct Linked {
    cons: Vec<Con>,
    ids: BTreeMap<Atom, usize>,
    parent: Vec<usize>,
    /// At each root, its constraints.
    held: Vec<Vec<usize>>,
    /// For the constraints added by [`Linked::meet`], the index of each term's constraint,
    /// keyed by the term without its constant and by the comparison.
    by_terms: HashMap<(BTreeMap<Atom, Int>, Rel), usize>,
}

impl Linked {
    fn of(cons: Vec<Con>) -> Linked {
        let mut l = Linked::default();
        cons.into_iter().for_each(|c| l.add(c));
        l
    }

    /// [`Linked::of`] with each constraint added by [`Linked::meet`].
    fn reduced(cons: Vec<Con>) -> Linked {
        let mut l = Linked::default();
        cons.into_iter().for_each(|c| {
            l.meet(c);
        });
        l
    }

    /// Adds a constraint unless one with the same term and comparison already implies it: of
    /// `t + a >= 0` and `t + b >= 0` only the one with the smaller constant is kept, in the
    /// place of the other, and an equality is not added twice. A bound written again at each
    /// level of a nest then adds nothing to the group of its atoms.
    /// Whether it is added at the end of `cons`; a constraint put in the place of another has
    /// the same atoms.
    fn meet(&mut self, c: Con) -> bool {
        let key = (c.lin.terms.clone(), c.rel);
        match self.by_terms.get(&key) {
            Some(&i) => {
                let old = &self.cons[i].lin.constant;
                match c.rel {
                    Rel::Ge if c.lin.constant < *old => self.cons[i] = c,
                    Rel::Ge => {}
                    Rel::Eq if c.lin.constant == *old => {}
                    Rel::Eq => {
                        self.add(c);
                        return true;
                    }
                }
                false
            }
            None => {
                self.by_terms.insert(key, self.cons.len());
                self.add(c);
                true
            }
        }
    }

    fn id(&mut self, a: &Atom) -> usize {
        if let Some(i) = self.ids.get(a) {
            return *i;
        }
        let i = self.parent.len();
        self.ids.insert(a.clone(), i);
        self.parent.push(i);
        self.held.push(Vec::new());
        i
    }

    fn root(&self, mut i: usize) -> usize {
        while self.parent[i] != i {
            i = self.parent[i];
        }
        i
    }

    /// Adds a constraint; the smaller group joins the larger, so a root is found in `log` steps.
    fn add(&mut self, c: Con) {
        let n = self.cons.len();
        let ids: Vec<usize> = c.lin.terms.keys().map(|a| self.id(a)).collect();
        self.cons.push(c);
        let Some(first) = ids.first() else {
            return;
        };
        let mut r = self.root(*first);
        for i in &ids[1..] {
            let o = self.root(*i);
            if o != r {
                let (big, small) = if self.held[r].len() < self.held[o].len() {
                    (o, r)
                } else {
                    (r, o)
                };
                let moved = std::mem::take(&mut self.held[small]);
                self.held[big].extend(moved);
                self.parent[small] = big;
                r = big;
            }
        }
        self.held[r].push(n);
    }

    /// The constraints in the groups of the atoms of `cs`, in no particular order.
    fn around(&self, cs: &[Con]) -> Vec<&Con> {
        self.around_atoms(cs.iter().flat_map(|c| c.lin.terms.keys()))
    }

    /// The constraints in the groups of `atoms`, in no particular order.
    fn around_atoms<'a>(&self, atoms: impl Iterator<Item = &'a Atom>) -> Vec<&Con> {
        (self.around_places(atoms).into_iter())
            .map(|i| &self.cons[i])
            .collect()
    }

    /// The places in `cons` of the constraints in the groups of `atoms`, in no particular order.
    fn around_places<'a>(&self, atoms: impl Iterator<Item = &'a Atom>) -> Vec<usize> {
        let roots: BTreeSet<usize> = atoms
            .filter_map(|a| self.ids.get(a).map(|i| self.root(*i)))
            .collect();
        (roots.into_iter())
            .flat_map(|r| self.held[r].iter().copied())
            .collect()
    }
}

/// The rows of `rows` in the groups of `atoms` ([`Linked::around_atoms`]), in their order.
fn linked_to<'a>(rows: Vec<Con>, atoms: impl Iterator<Item = &'a Atom>) -> Vec<Con> {
    let linked = Linked::of(rows);
    let mut at = linked.around_places(atoms);
    at.sort_unstable();
    let mut rows: Vec<Option<Con>> = linked.cons.into_iter().map(Some).collect();
    at.into_iter()
        .map(|i| rows[i].take().expect("each place once"))
        .collect()
}

/// A row `a·x + rest >= 0` read as a bound on `x`: `a` above zero for a lower bound, below for an
/// upper one.
struct Side1 {
    a: Int,
    rest: Lin,
    /// The row it comes from, so that the two sides of one equality are not combined.
    row: usize,
}

impl Side1 {
    /// The bounds the row `c`, numbered `row`, puts on `x`, which it holds, pushed on `lows` and
    /// `highs`: one, or both for an equality.
    fn push(c: &Con, x: &Atom, row: usize, lows: &mut Vec<Side1>, highs: &mut Vec<Side1>) {
        let a = c.lin.terms.get(x).expect("a row of the atom").clone();
        let mut rest = c.lin.clone();
        rest.terms.remove(x);
        let neg = || Lin {
            terms: rest.terms.iter().map(|(b, k)| (b.clone(), -k)).collect(),
            constant: -&rest.constant,
        };
        match (c.rel, a.is_positive()) {
            (Rel::Eq, true) => {
                highs.push(Side1 {
                    a: -&a,
                    rest: neg(),
                    row,
                });
                lows.push(Side1 { a, rest, row });
            }
            (Rel::Eq, false) => {
                lows.push(Side1 {
                    a: -&a,
                    rest: neg(),
                    row,
                });
                highs.push(Side1 { a, rest, row });
            }
            (Rel::Ge, true) => lows.push(Side1 { a, rest, row }),
            (Rel::Ge, false) => highs.push(Side1 { a, rest, row }),
        }
    }

    /// The real shadow of the lower bound `self`, `a·x + r >= 0`, and the upper bound `hi`,
    /// `-b·x + s >= 0`: `b·r + a·s`, which is at least 0 where they have a real `x` between them.
    fn combine(&self, hi: &Side1) -> Lin {
        let b = -&hi.a;
        let mut lin = Lin {
            terms: BTreeMap::new(),
            constant: &(&b * &self.rest.constant) + &(&self.a * &hi.rest.constant),
        };
        for (t, k) in &self.rest.terms {
            lin.terms.insert(t.clone(), &b * k);
        }
        for (t, k) in &hi.rest.terms {
            let v = &self.a * k;
            let sum = match lin.terms.remove(t) {
                Some(w) => &w + &v,
                None => v,
            };
            if !sum.is_zero() {
                lin.terms.insert(t.clone(), sum);
            }
        }
        lin
    }

    /// Whether the real shadow of the pair has the integer points of its dark shadow, `b·r +
    /// a·s >= (a - 1)·(b - 1)` (Pugh, "The Omega test", 1992), so that the pair has an integer
    /// `x` between its bounds wherever its real shadow holds. With `g` the greatest common
    /// divisor of the terms of `b·r + a·s` and `c` its constant, the form takes the values `g·t
    /// + c`, so the two rows hold for the same `t` when `c` and `c - (a - 1)·(b - 1)` round down
    /// to one multiple of `g`; without terms, when the constant is below 0 or at least
    /// `(a - 1)·(b - 1)`. `lin` is [`Side1::combine`] of the pair. O(the terms of the pair).
    fn dark_is_real(&self, hi: &Side1, lin: &Lin) -> bool {
        let gap = &(&self.a - &Int::ONE) * &(&(-&hi.a) - &Int::ONE);
        if lin.terms.is_empty() {
            return lin.constant.is_negative() || lin.constant >= gap;
        }
        let g = lin.terms.values().fold(Int::ZERO, |g, k| g.gcd(k));
        lin.constant.div_floor(&g) == (&lin.constant - &gap).div_floor(&g)
    }
}

/// The rows of `rows`, a system with an integer point when `None` is not returned, with atoms
/// that `keep` does not hold eliminated wherever the elimination is exact and adds no terms:
/// the integer points of the result, read on the atoms it keeps, are those of `rows`, so the
/// result with any rows over kept atoms has a point exactly when `rows` with them has one.
/// An atom `x` is eliminated by Fourier-Motzkin, each lower bound `a·x + r >= 0` combined with
/// each upper bound `-b·x + s >= 0` into `b·r + a·s >= 0`, an equality giving both; this is exact
/// over the integers when every lower bound or every upper bound has coefficient 1 (Pugh, "The
/// Omega test", 1992, the exact shadow). It is done only when the `L·U` rows made have no more
/// terms in all than the `L + U` rows taken out, judged in O(1) from counts kept for each atom,
/// so the system never grows and the whole elimination costs O(m log m) for m terms, an atom
/// being looked at again only when a row of it changes. Where the counts do not show it but
/// at most `L + U` rows can be made once the pairs of two bounds of one term (which make no
/// row) are left out, the rows are made, and the elimination is done when they, one kept for
/// each linear form, are no more rows and terms than those taken out: so `y` with `1 <= y <=
/// 2`, `y <= d` and `4 <= d + y <= 5` goes, leaving `2 <= d <= 4`. This is tried for an atom
/// with two bounds or more on each side, which then has `(L - 1)(U - 1) <= 2`: at most five
/// rows read and six made. An atom with an equality in which its
/// coefficient is 1 or -1 is eliminated by substituting that equality (the one of fewest terms)
/// into its other rows, which is exact over the integers, when the terms this adds are at most
/// those of its equalities and twice their number; and of two `>=` rows on one linear form only
/// the tighter is kept, so a substitution or a combination that writes a row again adds
/// nothing. `None` when a combination or a substitution leaves a false row without atoms, or an
/// equality whose terms' greatest common divisor does not divide its constant: `rows` has no
/// point. With `dark`, an atom is eliminated too where each pair of its bounds has the integer
/// points of its real shadow in its dark shadow (as `2·q <= x <= 2·q + 1`, the bounds of `q = x
/// div 2`, leave no gap) and the rows its elimination makes are no more than those it takes
/// out; without it, as the solver's own projections ([`by_halves`]) always did.
// Complexity tradeoff: an atom whose elimination would add terms is kept, so the result is
// small only where the graph of the rows is: on chains, trees and other graphs whose atoms
// have few lower or few upper bounds it keeps little beyond `keep`, and on a graph with a core
// of atoms each of three or more lower and three or more upper bounds (a dense graph, a grid)
// it keeps that core whole. A complete projection there grows the rows quadratically or worse
// (Fourier-Motzkin is doubly exponential in general), so no smaller exact result is known;
// the callers then solve the kept core with each question, as they did the whole group.
pub(super) fn shadow(rows: &[Con], keep: &dyn Fn(&Atom) -> bool, dark: bool) -> Option<Vec<Con>> {
    shadow_logged(rows, keep, dark, false, None)
}

/// The conjunction `rows` with every atom outside `keep` eliminated, exactly over the integers
/// (Fourier–Motzkin with the dark shadow, `shadow`): rows over the atoms of `keep` alone that
/// hold at a point exactly where `rows` hold at some values of the other atoms there, the
/// single row `-1 >= 0` where `rows` hold nowhere. `None` when an atom outside `keep` cannot be
/// eliminated so.
pub fn eliminated(rows: &[Con], keep: &dyn Fn(&Atom) -> bool) -> Option<Vec<Con>> {
    match shadow(rows, keep, true) {
        None => Some(vec![Con::ge(&Lin::constant(0), &Lin::constant(1))]),
        Some(out) => (out.iter())
            .all(|c| c.lin.terms.keys().all(keep))
            .then_some(out),
    }
}

/// An atom eliminated by [`shadow`] and its rows when it was: a point of the rows left gives
/// the atom a value by them, the atoms eliminated after it having theirs ([`point_of`]).
type Eliminated = (Atom, Vec<Con>);

/// [`shadow`] with every atom outside `keep` eliminated that can be exactly (by an equality
/// where its coefficient is 1 or -1, by bounds of which one side has coefficients 1 or -1, or by
/// dark shadows equal to the real ones), however many rows that makes: for small systems whose
/// projection is known to stay small, the pieces of a summary of definitions
/// (`extend::Summaries::make`), where the size rules of [`shadow`] would leave an atom that
/// the next elimination needs gone.
// Complexity tradeoff: naive version, [`shadow`], which leaves an atom whose elimination
// makes more rows than it takes out, so that a projection never grows: a summary piece with
// such an atom is not made, and its chain of definitions is decided whole at each question,
// O(n²) over n links. Used: the elimination done anyway, Fourier-Motzkin on the piece, O(l·u)
// rows for an atom of l lower and u upper bounds, so a piece of r rows may grow to O(r²) at
// each atom; a piece of a summary holds the rows of one case of one definition and of one
// piece below, a few rows each, and is measured by the `separate_*_scale` tests
// (l01_38_presburger::one_scope), COMPLEXITY.md row LOAD-chain-sep-rest.
pub(super) fn shadow_whole(rows: &[Con], keep: &dyn Fn(&Atom) -> bool) -> Option<Vec<Con>> {
    shadow_logged(rows, keep, true, true, None)
}

/// [`shadow`], each elimination written to `log` in turn when there is one; with `grow`, as
/// [`shadow_whole`].
fn shadow_logged(
    rows: &[Con],
    keep: &dyn Fn(&Atom) -> bool,
    dark: bool,
    grow: bool,
    mut log: Option<&mut Vec<Eliminated>>,
) -> Option<Vec<Con>> {
    #[derive(Default)]
    struct Deg {
        lo: usize,
        hi: usize,
        lo_terms: usize,
        hi_terms: usize,
        lo_wide: usize,
        hi_wide: usize,
        // Its bounds of one term, `±x + k >= 0`: at most one on each side, the tighter of two
        // being kept, so a pair of them combines into a row without atoms.
        lo_unary: usize,
        hi_unary: usize,
        // The equalities of the atom, and those where its coefficient is 1 or -1 with their
        // terms in all.
        eqs: usize,
        unit_eqs: usize,
        unit_eq_terms: usize,
        rows: Vec<usize>,
        gone: bool,
        queued: bool,
    }
    let mut live: Vec<Option<Con>> = Vec::with_capacity(rows.len());
    let mut deg: HashMap<Atom, Deg> = HashMap::new();
    let mut queue: std::collections::VecDeque<Atom> = std::collections::VecDeque::new();
    // Adds (`by` 1) or takes out (`by` -1) the counts of row `i` at each of its atoms, queuing
    // those that may now be eliminated.
    let count = |deg: &mut HashMap<Atom, Deg>,
                 queue: &mut std::collections::VecDeque<Atom>,
                 c: &Con,
                 i: usize,
                 add: bool| {
        let n = c.lin.terms.len();
        for (a, k) in &c.lin.terms {
            let d = deg.entry(a.clone()).or_default();
            let wide = usize::from(!k.is_unit());
            let sides = if c.rel == Rel::Eq {
                [true, true]
            } else {
                [k.is_positive(), !k.is_positive()]
            };
            for (lower, on) in [(true, sides[0]), (false, sides[1])] {
                if !on {
                    continue;
                }
                let (cnt, terms, w, one) = if lower {
                    (&mut d.lo, &mut d.lo_terms, &mut d.lo_wide, &mut d.lo_unary)
                } else {
                    (&mut d.hi, &mut d.hi_terms, &mut d.hi_wide, &mut d.hi_unary)
                };
                let unary = usize::from(n == 1 && c.rel == Rel::Ge);
                if add {
                    *cnt += 1;
                    *terms += n;
                    *w += wide;
                    *one += unary;
                } else {
                    *cnt -= 1;
                    *terms -= n;
                    *w -= wide;
                    *one -= unary;
                }
            }
            if c.rel == Rel::Eq {
                let unit = usize::from(k.is_unit());
                if add {
                    d.eqs += 1;
                    d.unit_eqs += unit;
                    d.unit_eq_terms += unit * n;
                } else {
                    d.eqs -= 1;
                    d.unit_eqs -= unit;
                    d.unit_eq_terms -= unit * n;
                }
            }
            if add {
                d.rows.push(i);
            }
            if !d.gone && !d.queued && !keep(a) {
                d.queued = true;
                queue.push_back(a.clone());
            }
        }
    };
    // A combined row with its terms divided by their common divisor and its constant rounded
    // down; `None` for a row without atoms, which is false when its constant is below zero.
    let tidy = |lin: Lin, rel: Rel| -> Result<Option<Con>, ()> {
        if lin.terms.is_empty() {
            let holds = match rel {
                Rel::Eq => lin.constant.is_zero(),
                Rel::Ge => !lin.constant.is_negative(),
            };
            return if holds { Ok(None) } else { Err(()) };
        }
        let g = lin.terms.values().fold(Int::ZERO, |g, k| g.gcd(k));
        if rel == Rel::Eq && !lin.constant.mod_floor(&g).is_zero() {
            return Err(());
        }
        let lin = if g.is_unit() {
            lin
        } else {
            Lin {
                terms: lin
                    .terms
                    .iter()
                    .map(|(a, k)| (a.clone(), k.div_floor(&g)))
                    .collect(),
                constant: lin.constant.div_floor(&g),
            }
        };
        Ok(Some(Con { lin, rel }))
    };
    // Of two inequalities on one form only the tighter is kept, so that a bound made again
    // (by two eliminations, or by an equality put in two rows) does not count against the
    // elimination of its atoms; `same` gives the place of the row kept for each form.
    let mut same: HashMap<BTreeMap<Atom, Int>, usize> = HashMap::new();
    macro_rules! put {
        ($c:expr) => {{
            let c: Con = $c;
            let i = live.len();
            let mut fresh = true;
            if c.rel == Rel::Ge {
                match same.get(&c.lin.terms).copied() {
                    Some(j) if live[j].is_some() => {
                        let old = &live[j].as_ref().expect("a live row").lin.constant;
                        if c.lin.constant >= *old {
                            fresh = false;
                        } else {
                            let o = live[j].take().expect("a live row");
                            count(&mut deg, &mut queue, &o, j, false);
                            same.insert(c.lin.terms.clone(), i);
                        }
                    }
                    _ => {
                        same.insert(c.lin.terms.clone(), i);
                    }
                }
            }
            if fresh {
                count(&mut deg, &mut queue, &c, i, true);
                live.push(Some(c));
            }
        }};
    }
    for c in rows {
        put!(c.clone());
    }
    while let Some(x) = queue.pop_front() {
        let d = deg.get_mut(&x).expect("a queued atom");
        d.queued = false;
        let (l, u) = (d.lo, d.hi);
        let exact = d.lo_wide == 0 || d.hi_wide == 0;
        let small = l * u <= l + u
            && l * d.hi_terms + u * d.lo_terms <= d.lo_terms + d.hi_terms + 2 * l * u;
        // A pair of bounds of one term makes a row without atoms, so at most `l·u - 1` rows
        // are made when the atom has both. Where that is no more than the rows taken out but
        // the count of terms above is, the rows are made and counted (`trial`): terms of the
        // two sides may cancel (`y >= 4 - d` with `y <= 5 - d`), and a row made twice is kept
        // once, which no count from the sides foresees. With two bounds or more on each side,
        // `(l - 1)(u - 1) <= 2`, so a trial reads at most five rows of the atom and makes at
        // most six.
        let made = l * u - d.lo_unary * d.hi_unary;
        let trial = !small && l >= 2 && u >= 2 && made <= l + u;
        let (out_rows, out_terms) = (l + u, d.lo_terms + d.hi_terms);
        // An equality where the atom's coefficient is 1 or -1 gives its value, which is put
        // in each other row of the atom, exactly: `r` rows and an equality of `e` terms make
        // `r` rows of at most `r·(e - 2)` more terms than they had, done when that is no more
        // than the `e` terms of the equality taken out. Judged with the mean size of such
        // equalities, which the one used is no larger than.
        let others = (l + u).saturating_sub(d.eqs + 1);
        let by_eq = d.unit_eqs > 0
            && (grow || others * d.unit_eq_terms <= d.unit_eq_terms + 2 * others * d.unit_eqs);
        // With `dark`, an atom is eliminated too when each pair of its bounds has, in its real
        // shadow, the integer points of its dark shadow ([`Side1::dark_is_real`], always so
        // for a coefficient 1 or -1): the dark shadow of the whole then has the points of the
        // real one, and the projection, between them, is exact (Pugh 1992). An equality whose
        // coefficient is not 1 or -1 is left, since its two sides alone ask that the
        // coefficient divide the rest. Whether the result is small is judged by the rows the
        // elimination makes, after cancelling (as `x div 2` of `x div 2` cancels its input),
        // and not by the bound of `small`: no more rows, of no more terms in all, than it
        // takes out. The rows are made only where `l·u <= l + u` (one side has one or two
        // bounds), so the trial costs O(the terms of the atom's rows), as the elimination does.
        let fits =
            dark && (grow || l * u <= l + u) && !by_eq && !d.gone && d.eqs == d.unit_eqs && {
                let (mut lows, mut highs) = (Vec::new(), Vec::new());
                let (mut old_rows, mut old_terms) = (0, 0);
                for &i in &d.rows {
                    if let Some(c) = &live[i] {
                        old_rows += 1;
                        old_terms += c.lin.terms.len();
                        Side1::push(c, &x, i, &mut lows, &mut highs);
                    }
                }
                let (mut new_rows, mut new_terms) = (0, 0);
                let all = (lows.iter()).all(|lo| {
                    (highs.iter()).filter(|hi| lo.row != hi.row).all(|hi| {
                        let lin = lo.combine(hi);
                        let real = lo.dark_is_real(hi, &lin);
                        if let Ok(Some(c)) = tidy(lin, Rel::Ge) {
                            new_rows += 1;
                            new_terms += c.lin.terms.len();
                        }
                        real
                    })
                });
                all && (grow || (new_rows <= old_rows && new_terms <= old_terms))
            };
        if d.gone || !(by_eq || (exact && (small || trial || grow)) || fits) {
            continue;
        }
        d.gone = true;
        let mut ids = mem::take(&mut d.rows);
        ids.sort_unstable();
        ids.dedup();
        if by_eq {
            let mut taken: Vec<Con> = (ids.iter())
                .filter_map(|&i| live[i].take().map(|c| (i, c)))
                .map(|(i, c)| {
                    count(&mut deg, &mut queue, &c, i, false);
                    c
                })
                .collect();
            if let Some(log) = log.as_deref_mut() {
                log.push((x.clone(), taken.clone()));
            }
            let at = (taken.iter().enumerate())
                .filter(|(_, c)| c.rel == Rel::Eq && c.lin.terms[&x].is_unit())
                .min_by_key(|(_, c)| c.lin.terms.len())
                .map(|(j, _)| j)
                .expect("a unit equality of the atom");
            let e = taken.swap_remove(at);
            // `x = -(e - x)` when its coefficient in `e` is 1; `e` is turned so that it is.
            let e = if e.lin.terms[&x].is_positive() {
                e.lin
            } else {
                e.lin.times(-1)
            };
            for c in taken {
                let a = c.lin.terms[&x].clone();
                let lin = c.lin.minus(&e.times(a));
                match tidy(lin, c.rel) {
                    Err(()) => return None,
                    Ok(None) => {}
                    Ok(Some(c)) => put!(c),
                }
            }
            continue;
        }
        let (mut lows, mut highs): (Vec<Side1>, Vec<Side1>) = (Vec::new(), Vec::new());
        for &i in &ids {
            let Some(c) = &live[i] else { continue };
            Side1::push(c, &x, i, &mut lows, &mut highs);
        }
        // The rows made, each tidied; a row without atoms that is false shows that `rows` has
        // no point, whether the elimination is then done or not.
        let mut made: Vec<Con> = Vec::with_capacity(lows.len() * highs.len());
        for lo in &lows {
            for hi in &highs {
                if lo.row == hi.row {
                    continue;
                }
                // `lo.a·x + r >= 0` and `hi.a·x + s >= 0` with `hi.a` below zero.
                match tidy(lo.combine(hi), Rel::Ge) {
                    Err(()) => return None,
                    Ok(None) => {}
                    Ok(Some(c)) => made.push(c),
                }
            }
        }
        if !small {
            // Of the rows on one form the tighter (least constant) is the one kept.
            made.sort_unstable_by(|a, b| {
                (a.lin.terms.cmp(&b.lin.terms)).then_with(|| a.lin.constant.cmp(&b.lin.constant))
            });
            made.dedup_by(|later, first| later.lin.terms == first.lin.terms);
            let terms: usize = made.iter().map(|c| c.lin.terms.len()).sum();
            if !grow && (made.len() > out_rows || terms > out_terms) {
                let d = deg.get_mut(&x).expect("a queued atom");
                d.gone = false;
                d.rows = ids;
                continue;
            }
        }
        let mut taken = Vec::with_capacity(ids.len());
        for &i in &ids {
            if let Some(c) = live[i].take() {
                count(&mut deg, &mut queue, &c, i, false);
                taken.push(c);
            }
        }
        if let Some(log) = log.as_deref_mut() {
            log.push((x.clone(), taken));
        }
        for c in made {
            put!(c);
        }
    }
    Some(live.into_iter().flatten().collect())
}

/// Runs `leaf` on each item `0..keep.len()` in order, giving it the rows of the system `rows`
/// and of every row an earlier `leaf` returned, projected by [`shadow`] onto the atoms of the
/// item, `keep[i]`, and cut to the groups of those atoms ([`linked_to`]); `None` when the
/// projection found no point, which a system with a point never gives. The projections are
/// made by halves: the system projected onto the atoms of a range of items is projected onto
/// those of its first half, whose items run, and then, with the rows they returned, onto those
/// of its second half. On a system whose projections stay small (see [`shadow`]) the work is
/// O((m + k) log k) for m terms and k items, where asking each item of the whole system is
/// O(m k). `rows` must have an integer point, and keep one with the rows returned, for a
/// projection to be used by the leaves.
fn by_halves<E>(
    rows: Vec<Con>,
    keep: &[BTreeSet<Atom>],
    mut leaf: impl FnMut(usize, Option<Vec<Con>>) -> Result<Vec<Con>, E>,
) -> Result<(), E> {
    let n = keep.len();
    if n == 0 {
        return Ok(());
    }
    let project = |rows: Vec<Con>, l: usize, r: usize| -> Option<Vec<Con>> {
        let atoms: HashSet<&Atom> = keep[l..r].iter().flatten().collect();
        let near = linked_to(rows, atoms.iter().copied());
        let s = shadow(&near, &|a| atoms.contains(a), false)?;
        Some(linked_to(s, atoms.iter().copied()))
    };
    // The ranges still to run after the one running, each with its system (`None`: unknown),
    // to which the rows returned meanwhile are added; innermost last.
    let mut open: Vec<(usize, usize, Option<Vec<Con>>)> = Vec::new();
    let mut cur = Some((0, n, Some(rows)));
    loop {
        if let Some((l, r, rows)) = cur.take() {
            let k = rows.and_then(|rows| project(rows, l, r));
            if r - l == 1 {
                let added = leaf(l, k)?;
                if !added.is_empty() {
                    for (_, _, rows) in &mut open {
                        if let Some(rows) = rows {
                            rows.extend(added.iter().cloned());
                        }
                    }
                }
            } else {
                let m = l + (r - l) / 2;
                cur = Some((l, m, k.clone()));
                open.push((m, r, k));
                continue;
            }
        }
        match open.pop() {
            Some(next) => cur = Some(next),
            None => return Ok(()),
        }
    }
}

/// `p` with each disjunct removed whose addition, propagated, leaves no point, until none is
/// removed, or `None` when `p` has no point. Each round but the last removes a disjunct, and
/// each tests every disjunct by one propagation, so the work is polynomial in the disjuncts.
///
/// A disjunct that holds at a point of the formula is kept without its test: removing a
/// disjunct that meets the rest nowhere leaves the formula's points as they were, so a point
/// found once is a point of every later state, and propagation, which removes a disjunct only
/// on a proof that it has no point with the rest, never removes one that holds there. The
/// points are found by [`pick`] on the parts of a test,
/// trying first the disjuncts that no point found so far holds: on a chain of `k` guards
/// `i >= j` on one input, two points (at the least and the greatest `i` the chain allows)
/// keep every disjunct but the `O(1)` that propagation removes, where testing each of the
/// `2k` disjuncts by a propagation of all `2k` disjunctions cost `k^2` (ledger LIN-probe).
///
/// A disjunct that a propagation removes is also read for its bounds of one atom by
/// [`learn`], which finds the bounds the formula implies, and each later disjunct that breaks
/// one of them is removed without a test: on `k` guards beyond the inputs, where the formula
/// implies `i > c` and the `c` disjuncts `i <= j - 1` with `j <= c + 1` have no point, one
/// search over their bounds removes them all (ledger LIN-probe-refute). Such a disjunct has no
/// point, so the formula's points are as before; it may be one that propagation alone would
/// have kept, so the result can have fewer disjuncts than one propagation per disjunct
/// leaves.
///
/// Before a point is sought, a disjunct is tested by [`refuted_by_links`] with only the
/// disjunctions it shares a private atom with, and one it removes is not read by [`learn`]:
/// on a chain of `k` guarded remainders (`n + i == 0 || x mod (n + i) >= 0`) each disjunct of
/// the negated goal has no point with its own remainder's definition, and a test of all the
/// parts per disjunct cost `130` times the work at `8k` (ledger PRES-guarded-chain). The
/// disjunctions are tested in the order of [`private_links`], cheapest linked test first, so
/// that a definition is tested after the goal's disjuncts that its cases refute are gone.
///
/// Each disjunct in `kept` is kept untested, as if a point held it: neither removed nor
/// searched for ([`probe_kept`]).
fn probe(p: Parts, kept: &HashSet<*const Parts>) -> Result<Option<Parts>, Refusal> {
    probe_kept(p, &mut Vec::new(), false, kept)
}

/// The parts of [`project_parts`] with two disjunctions or more, with each disjunct that has no
/// point removed ([`probe`]) from each disjunction whose atoms' values [`forest_domains`] does
/// not find exactly; `None` when they have no point. Also returned: the values
/// [`forest_domains`] finds before the probe with, for each disjunction, whether its component
/// was handled so (on the new path), and whether the probe ran. A disjunction handled is not
/// tested by the probe: its atoms' values are exact whatever disjuncts without a point it
/// keeps, so it is kept untested. Nor is a set of values of one atom ([`one_atom_set`]), as a
/// domain with holes is written. With every disjunction kept so, the probe is not run.
///
/// Which disjunctions are kept depends only on their own form, never on their place, so the
/// parts the probe leaves, and the hulls read from them, are the same in every order of the
/// parts (the s22 reverse-order tests: 0 boxes of 4000 change; with the probe run only where
/// the greedy search failed, 17 changed).
///
/// Complexity tradeoff: testing each piece of a set of values of one atom costs one search of
/// the whole formula per piece that the rounds by halves cannot refute together, O(h·n) for a
/// domain of `h` pieces over a formula of size `n` (holes of `x` on difference chains, 128 to
/// 1024 pieces: 12.55 times the work for 8 times the pieces, limit 12.57; 66 to 1015 rounds
/// for 128 to 2048). Keeping the set untested asks nothing of it (6 to 69 rounds; 7.4 times
/// with the set left out of each search, [`search_by_halves`]),
/// at the price of a piece with no point that the set keeps: it can widen a hull or leave it
/// inexact, the same in every order. Measured against the probe of every piece over the
/// preimage tests: 5 exact marks fewer in 82500 cases (exact_oracle) and 2 boxes counted as
/// made exact more (s22, the transfer before less exact); against the probe only after a
/// failed search, which main ran, every changed box is narrower or as exact but two, and each
/// of those two is main's own answer with the parts reversed.
///
/// Kept out of [`project_parts`], which recurses once per level of a nest, so that its frame
/// does not grow by this code's locals (`nest_empty` at depth 512 runs on the test thread's
/// stack).
#[inline(never)]
#[allow(clippy::type_complexity)]
fn probe_unhandled(
    p: &mut Parts,
) -> Result<Option<(Option<Box<(HashMap<Atom, IntervalSet>, Vec<bool>)>>, bool)>, Refusal> {
    let mut kept: HashSet<*const Parts> = HashSet::new();
    let mut early = None;
    if !old_path() {
        let Some(m) = solve(&p.cons, true)? else {
            return Ok(None);
        };
        let (doms, handled) = forest_domains(&Linked::of(p.cons.clone()), &p.ors, &m);
        kept = (p.ors.iter().zip(&handled))
            .filter(|(o, h)| **h || one_atom_set(o))
            .flat_map(|(o, _)| o.iter().map(Rc::as_ptr))
            .collect();
        early = Some(Box::new((doms, handled)));
    }
    if early.is_some()
        && p.ors
            .iter()
            .flatten()
            .all(|d| kept.contains(&Rc::as_ptr(d)))
    {
        return Ok(Some((early, false)));
    }
    Ok(probe(std::mem::take(p), &kept)?.map(|q| {
        *p = q;
        (early, true)
    }))
}

/// Whether each disjunct of `o` is bounds on one atom, the same atom for all, with no
/// disjunction inside: a set of values of that atom, as a domain with holes is written.
fn one_atom_set(o: &[Rc<Parts>]) -> bool {
    let mut atom = None;
    o.iter().all(|d| {
        d.ors.is_empty()
            && d.cons
                .iter()
                .all(|c| one_bound(c).is_some_and(|(a, _, _)| *atom.get_or_insert(a) == a))
    })
}

/// A set of values of one atom ([`one_atom_set`]) as its atom, `None` when no disjunct bounds
/// one, and its pieces, sorted by their lower ends and merged, `None` an open end.
struct OneAtomSet {
    atom: Option<Atom>,
    pieces: Vec<(Option<Int>, Option<Int>)>,
}

impl OneAtomSet {
    /// The set that the disjunction `o`, for which [`one_atom_set`] holds, writes:
    /// `O(h log h)` for `h` disjuncts.
    fn of(o: &[Rc<Parts>]) -> OneAtomSet {
        let mut atom = None;
        let mut pieces: Vec<(Option<Int>, Option<Int>)> = Vec::with_capacity(o.len());
        for d in o {
            let (mut lo, mut hi): (Option<Int>, Option<Int>) = (None, None);
            for (a, l, h) in d.cons.iter().filter_map(one_bound) {
                atom.get_or_insert_with(|| a.clone());
                if let Some(l) = l {
                    lo = Some(lo.map_or(l.clone(), |x| x.max(l)));
                }
                if let Some(h) = h {
                    hi = Some(hi.map_or(h.clone(), |x| x.min(h)));
                }
            }
            if let (Some(l), Some(h)) = (&lo, &hi)
                && l > h
            {
                continue;
            }
            pieces.push((lo, hi));
        }
        // `None` as a lower end is below every value.
        pieces.sort_by(|a, b| match (&a.0, &b.0) {
            (None, None) => Ordering::Equal,
            (None, _) => Ordering::Less,
            (_, None) => Ordering::Greater,
            (Some(x), Some(y)) => x.cmp(y),
        });
        let mut merged: Vec<(Option<Int>, Option<Int>)> = Vec::with_capacity(pieces.len());
        for (lo, hi) in pieces {
            if let Some((_, last)) = merged.last_mut() {
                // The piece meets or touches the last one: its lower end is at most one past it.
                let joins = match (&*last, &lo) {
                    (None, _) | (_, None) => true,
                    (Some(l), Some(x)) => *x <= l + &Int::from(1),
                };
                if joins {
                    *last = match (last.take(), hi) {
                        (Some(l), Some(h)) => Some(l.max(h)),
                        _ => None,
                    };
                    continue;
                }
            }
            merged.push((lo, hi));
        }
        OneAtomSet {
            atom,
            pieces: merged,
        }
    }

    /// Whether `m` lies in the set, by binary search on the pieces: `O(log h)`.
    fn holds(&self, m: &Model) -> bool {
        let Some(a) = &self.atom else {
            return !self.pieces.is_empty();
        };
        let Some(v) = m.get(a) else {
            return false;
        };
        // The pieces whose lower end is at most `v` come first.
        let at = self
            .pieces
            .partition_point(|(lo, _)| lo.as_ref().is_none_or(|l| l <= v));
        at > 0 && self.pieces[at - 1].1.as_ref().is_none_or(|h| v <= h)
    }
}

/// The values [`forest_domains`] finds in [`project_parts`] for the parts after the probe, and
/// for each disjunction whether it was handled so. Without a probe the parts are those
/// [`forest_domains`] read before it ([`probe_unhandled`]), so `early`, its answer then, is
/// taken as it is. After one, the values found before the probe are still those of the
/// formula, and are met where the pass over the probed parts finds none. Not inlined, so that
/// [`project_parts`], which recurses once per level of a nest, keeps its frame.
#[inline(never)]
#[allow(clippy::type_complexity)]
fn tree_domains(
    early: Option<Box<(HashMap<Atom, IntervalSet>, Vec<bool>)>>,
    probed: bool,
    linked: &Linked,
    ors: &[Vec<Rc<Parts>>],
    model: &Model,
) -> (HashMap<Atom, IntervalSet>, Vec<bool>) {
    match early {
        Some(e) if !probed => *e,
        _ if !old_path() && !ors.is_empty() => {
            let (mut doms, handled) = forest_domains(linked, ors, model);
            for (a, d) in early.map(|e| e.0).unwrap_or_default() {
                doms.entry(a).or_insert(d);
            }
            (doms, handled)
        }
        _ => (HashMap::new(), vec![false; ors.len()]),
    }
}

/// [`probe`], which pushes each point it finds onto `points`, so that its caller has them
/// also when it refuses, and, when `stop` is set, stops at the first point and returns the
/// parts with the disjunction then tested whole, which have the points of `p`. Each point
/// holds a disjunct of the disjunction under test and every other part ([`point_with`]), so
/// it is a point of `p`. Until that point it does what [`probe`] does, so without one it
/// gives what [`probe`] gives.
fn probe_to(p: Parts, points: &mut Vec<Model>, stop: bool) -> Result<Option<Parts>, Refusal> {
    probe_kept(p, points, stop, &HashSet::new())
}

/// [`probe_to`], with each disjunct in `kept` kept untested, as if a point held it: neither
/// removed nor searched for. [`project_parts`] passes the disjuncts of the disjunctions whose
/// atoms' values [`forest_domains`] finds exactly, whose hulls no disjunct left without a
/// point widens.
fn probe_kept(
    mut p: Parts,
    points: &mut Vec<Model>,
    stop: bool,
    kept: &HashSet<*const Parts>,
) -> Result<Option<Parts>, Refusal> {
    // The bounds on single atoms that the formula implies, found by [`learn`]. The formula
    // only gains constraints or stays equal from round to round, so they hold to the end.
    let mut implied = Near::default();
    loop {
        let mut changed = false;
        // For each disjunct of each disjunction, whether a point found so far holds it or it
        // is kept untested.
        let mut held: Vec<Vec<bool>> = p
            .ors
            .iter()
            .map(|o| {
                o.iter()
                    .map(|d| kept.contains(&Rc::as_ptr(d)) || points.iter().any(|m| d.holds(m)))
                    .collect()
            })
            .collect();
        let (order, links) = private_links(&p);
        // The bounds of single atoms that the top-level constraints write, read by
        // [`refuted_by_links`].
        let mut base = Near::default();
        take(&p.cons, &mut Linked::default(), &mut base);
        // For each disjunct, whether the search with it forced found no point ([`search_by_halves`]).
        let mut single_failed: Vec<Vec<bool>> =
            p.ors.iter().map(|o| vec![false; o.len()]).collect();
        let (order, links) = if stop {
            (order, links)
        } else {
            // The tests that ask no search remove their disjuncts first, so that the
            // batched searches below do not force a disjunct with no point.
            for &i in &order {
                let ds = std::mem::take(&mut p.ors[i]);
                let hs = std::mem::take(&mut held[i]);
                let n = ds.len();
                let mut keep = Vec::with_capacity(n);
                let mut keep_held = Vec::with_capacity(n);
                for (at, (d, h)) in ds.into_iter().zip(hs).enumerate() {
                    if !h
                        && (implied.refutes(&d.cons)
                            || refuted_by_links(&p, &links[i][at], &base, &d))
                    {
                        continue;
                    }
                    keep.push(d);
                    keep_held.push(h);
                }
                changed |= keep.len() < n;
                if keep.is_empty() {
                    return Ok(None);
                }
                p.ors[i] = keep;
                held[i] = keep_held;
            }
            single_failed = search_by_halves(&p, &mut held, points, &implied);
            private_links(&p)
        };
        for i in order {
            let ds = std::mem::take(&mut p.ors[i]);
            let flags = std::mem::take(&mut held[i]);
            // The points found while this disjunction is tested, which its flags do not count.
            let since = points.len();
            let n = ds.len();
            let mut live = Vec::with_capacity(n);
            let mut live_held = Vec::with_capacity(n);
            for (at, (d, h)) in ds.iter().zip(flags).enumerate() {
                let d = d.clone();
                if h || points[since..].iter().any(|m| d.holds(m)) {
                    live.push(d);
                    live_held.push(true);
                    continue;
                }
                if implied.refutes(&d.cons) {
                    continue;
                }
                if refuted_by_links(&p, &links[i][at], &base, &d) {
                    continue;
                }
                // A disjunct whose forced search already failed in [`search_by_halves`] is not searched
                // forward again; the propagation and the backward search below still test it.
                let mut point = if single_failed[i][at] {
                    None
                } else {
                    point_with(&p, &held, &d, &implied, false)
                };
                if point.is_none() {
                    // Complexity tradeoff: a disjunct that no point holds, no implied bound and
                    // no linked test ([`refuted_by_links`]) removes is still tested by one
                    // propagation of all the parts, so `r` such
                    // disjuncts cost `r` propagations of the whole formula, and failed-literal
                    // probing is polynomial, not `O(n log n)`, when `r` grows with `n` and the
                    // disjuncts share no bound of one atom that [`learn`] finds. Why: `settle`
                    // does not report which disjuncts its proof covers, and an undoable
                    // (trail-based) propagation does not help, since on a chain each refutation's
                    // own propagation runs through the whole chain. Each refuted disjunct also
                    // costs [`learn`]: for each bound of one atom it writes, an exponential and a
                    // binary search over the `m` bounds the other disjuncts write on that atom, up
                    // to about `2 log2 m + 1` tests, each one [`bounds_refute`] (one propagation
                    // of bounds, `O(n log n)`) and, when that does not refute, one `settle`. The
                    // search usually ends on a bound that has a point, and that test always costs
                    // a `settle`. So when no learned bound removes a later disjunct, `r` refuted
                    // disjuncts cost up to `O(r log m)` settles, not `r` (verifier's counters:
                    // `guards_beyond_the_inputs_scale` 5 calls of `learn` and 16 settles in them,
                    // cross 2 and 2). Trigger: disjuncts without a point whose proofs
                    // differ by more than a bound of one atom. Tests:
                    // `l01_25_preimage_catalog::s22::chains_on_two_inputs_keep_their_boxes`
                    // reaches it (cross at `k = 51`); `chain_cross_above_its_width_scales` (cross
                    // at 12 and 96, COMPLEXITY.md S22: 40.0 times the bytes with one propagation
                    // per disjunct, 10.1 times now) and
                    // `l01_38_presburger::probe::guards_beyond_the_inputs_scale` measure it. A
                    // complete solution is a `settle` that returns, with each refutation, the
                    // constraints its proof used (a conflict explanation), so that one propagation
                    // removes every disjunct those constraints exclude. The linked test is that
                    // explanation for the case where it is one disjunction reached through a
                    // private atom; it costs at most one more `settle` of a part of the formula
                    // before the one of the whole, so the worst case stays `O(n)` per disjunct.
                    // Tests: `l01_38_presburger::ladder::a_chain_of_guarded_remainders_scales`
                    // (COMPLEXITY.md PRES-guarded-chain).
                    let mut q = Parts {
                        cons: p.cons.clone(),
                        ors: p.ors.iter().filter(|o| !o.is_empty()).cloned().collect(),
                        atoms: OnceCell::new(),
                        hull: OnceCell::new(),
                        failed: Cell::new(0),
                        id: Cell::new(0),
                    };
                    q.put(&d);
                    if matches!(settle(q, false), Ok(None)) {
                        // The disjunction without `d`, which the formula is equal to without it.
                        let rest: Vec<Rc<Parts>> =
                            live.iter().chain(&ds[at + 1..]).cloned().collect();
                        learn(&p, rest, &d, &mut implied);
                        continue;
                    }
                    // A disjunct the propagation leaves is searched again with the
                    // disjunctions read in the other order: [`pick`] reads the last first, and
                    // on a chain of definitions written first to last (each stage of
                    // `n1 = if n0 < 2 {..} else {..}`, `n2 = ..`) a stage chosen first fixes
                    // a value that a stage read later defines otherwise, so the search is
                    // refused on every disjunct and each of them costs a propagation of the
                    // whole formula. Read from the first, each stage is chosen after the stages
                    // that define its inputs, and the point found holds many disjuncts, which
                    // are then kept unasked. Only a disjunct the propagation leaves pays the
                    // second search, so none is added for a disjunct removed (item
                    // PREIMAGE-slow-rounds). The disjuncts removed are those without a point,
                    // as before; a point only spares a question.
                    point = point_with(&p, &held, &d, &implied, true);
                }
                let Some(m) = point else {
                    live.push(d);
                    live_held.push(false);
                    continue;
                };
                if stop {
                    points.push(m);
                    p.ors[i] = ds;
                    return Ok(Some(p));
                }
                for (o, hs) in p.ors.iter().zip(held.iter_mut()) {
                    for (e, h) in o.iter().zip(hs.iter_mut()) {
                        *h = *h || e.holds(&m);
                    }
                }
                points.push(m);
                live.push(d);
                live_held.push(true);
            }
            changed |= live.len() < n;
            if live.is_empty() {
                return Ok(None);
            }
            p.ors[i] = live;
            held[i] = live_held;
        }
        if !changed {
            return Ok(Some(p));
        }
        match settle(p, false)? {
            None => return Ok(None),
            Some(q) => p = q,
        }
    }
}

/// After [`probe`] has found that the disjunct `d` of its parts `p` has no point, tests each
/// bound of one atom in `d` alone: when the formula with `x <= h` has no point, it implies
/// `x >= h + 1`, which removes without a propagation every disjunct that bounds `x` by `h` or
/// less. Of the upper bounds on `x` that the disjuncts write, sorted, the greatest for which
/// the formula has no point is found by an exponential and then a binary search, so that `r`
/// disjuncts removed this way cost `O(log r)` propagations, not `r`; lower bounds likewise.
/// The formula with a weaker bound has more points, so the bounds without a point are those
/// up to one. `rest` is `d`'s disjunction without `d`, whose place in `p` is empty while it
/// is tested. Each bound is first tested by [`bounds_refute`], which costs `O(n log n)`, and
/// then by [`settle`]; a bound is recorded in `implied` only when one of them has shown that
/// the formula has no point with its negation, so each removal it makes is proved.
fn learn(p: &Parts, rest: Vec<Rc<Parts>>, d: &Parts, implied: &mut Near) {
    if rest.is_empty() {
        return;
    }
    let mut ors: Vec<Vec<Rc<Parts>>> = (p.ors.iter()).filter(|o| !o.is_empty()).cloned().collect();
    ors.push(rest);
    let f = Parts {
        cons: p.cons.clone(),
        ors,
        atoms: OnceCell::new(),
        hull: OnceCell::new(),
        failed: Cell::new(0),
        id: Cell::new(0),
    };
    for (x, lo, hi) in d.cons.iter().filter_map(one_bound) {
        // `upper`: the bound is `x <= v`; otherwise `x >= v`. An equality is a bound both
        // ways, and its refutation implies neither.
        let (v, upper) = match (lo, hi) {
            (None, Some(h)) => (h, true),
            (Some(l), None) => (l, false),
            _ => continue,
        };
        let con = |v: &Int| {
            let (x, v) = (Lin::atom(x.clone()), Lin::constant(v.clone()));
            if upper {
                Con::ge(&v, &x)
            } else {
                Con::ge(&x, &v)
            }
        };
        if implied.refutes(&[con(&v)]) {
            continue;
        }
        // The bounds on `x` of the same side that are no stronger than `v`, weakest last.
        let weaker = |w: &Int| if upper { *w >= v } else { *w <= v };
        let mut ws: Vec<Int> = (f.ors.iter().flatten())
            .flat_map(|e| e.cons.iter().filter_map(one_bound))
            .filter_map(|(y, l, h)| (y == x).then_some(if upper { h } else { l }).flatten())
            .filter(weaker)
            .chain([v.clone()])
            .collect();
        ws.sort_unstable();
        ws.dedup();
        if !upper {
            ws.reverse();
        }
        let none = |w: &Int| {
            let c = con(w);
            if bounds_refute(&f, x, &c) {
                return true;
            }
            let mut q = f.clone();
            q.cons.push(c);
            // Complexity tradeoff: on a chain of definitions, a bound at the i-th stage
            // reaches the end of the chain in about i rounds of `settle`, each a pass over the
            // whole formula, so the bounds of a chain of k stages cost O(k^2) passes, cubic in
            // k in all (`a_staged_chain_under_false_is_read_in_time_near_its_length` in
            // zedc-preimage, ignored; 22.4 times the bytes from 4 to 32 stages). Propagating
            // the bound along the chain's definitions in one pass is item
            // PRES-settle-chain-rounds; every bound recorded stays proved.
            matches!(settle(q, false), Ok(None))
        };
        if !none(&ws[0]) {
            continue;
        }
        // `ws[good]` has no point; `ws[bad]`, when `bad < ws.len()`, has one.
        let (mut good, mut step) = (0, 1);
        let mut bad = loop {
            let at = good + step;
            if at >= ws.len() {
                break ws.len();
            }
            if !none(&ws[at]) {
                break at;
            }
            good = at;
            step *= 2;
        };
        while bad - good > 1 {
            let mid = good + (bad - good) / 2;
            if none(&ws[mid]) {
                good = mid;
            } else {
                bad = mid;
            }
        }
        let w = &ws[good];
        if upper {
            implied.tighten(x, Some(w + &Int::ONE), None);
        } else {
            implied.tighten(x, None, Some(w - &Int::ONE));
        }
    }
}

/// For the disjunctions of `p`, the order in which [`probe`] tests them and, for each disjunct
/// of each, its linked disjunctions: those that share with the disjunct's own disjunction an
/// atom that the disjunct mentions and that no third disjunction mentions (a private atom).
/// On a chain of guarded remainders, the remainder `r` of `x mod (n + i)` is written by the
/// definition's disjunction and read by one disjunct of the negated goal, so that disjunct's
/// link is the definition, and the definition with it has no point.
///
/// The order is by the cost of the linked test: a disjunction comes before another when the
/// greatest, over its disjuncts, of the atoms its linked disjunctions mention is smaller, ties
/// by position. A disjunction whose disjuncts are removed by small linked tests is thus tested
/// first, and the disjuncts it loses are gone when the others are tested. The order reads
/// only the formula's structure, not the atoms' names. Each atom of each disjunct is read once
/// with a hash map, so the whole costs `O(n log n)` for parts of `n` atoms, the sort included.
fn private_links(p: &Parts) -> (Vec<usize>, Vec<Vec<Vec<usize>>>) {
    // The disjunctions that mention each atom, in increasing position, each once.
    let mut readers: HashMap<&Atom, Vec<usize>> = HashMap::new();
    // The atoms each disjunction mentions, counted once per disjunct.
    let mut size = Vec::with_capacity(p.ors.len());
    for (j, o) in p.ors.iter().enumerate() {
        let mut s = 0;
        for d in o {
            s += d.atoms().len();
            for a in d.atoms() {
                let r = readers.entry(a).or_default();
                if r.last() != Some(&j) {
                    r.push(j);
                }
            }
        }
        size.push(s);
    }
    let mut key = Vec::with_capacity(p.ors.len());
    let links: Vec<Vec<Vec<usize>>> = (p.ors.iter().enumerate())
        .map(|(i, o)| {
            let ls: Vec<Vec<usize>> = o
                .iter()
                .map(|d| {
                    let mut l: Vec<usize> = (d.atoms().iter())
                        .filter_map(|a| match readers[a].as_slice() {
                            [x, y] if *x == i => Some(*y),
                            [x, y] if *y == i => Some(*x),
                            _ => None,
                        })
                        .collect();
                    l.sort_unstable();
                    l.dedup();
                    l
                })
                .collect();
            let cost = |l: &Vec<usize>| l.iter().map(|&j| size[j]).sum::<usize>();
            key.push(ls.iter().map(cost).max().unwrap_or(0));
            ls
        })
        .collect();
    let mut order: Vec<usize> = (0..p.ors.len()).collect();
    order.sort_by_key(|&i| (key[i], i));
    (order, links)
}

/// Whether the disjunct `d` has no point with the disjunctions of `p` at the positions
/// `links` (from [`private_links`]) and the bounds that `base` holds for `d`'s atoms. These
/// are a part of `p`'s constraints, so an answer `true` proves that `d` has no point with
/// `p`. The test costs one [`settle`] of `d` and its linked disjunctions, which on a chain of
/// guarded remainders is one definition, not the whole chain.
fn refuted_by_links(p: &Parts, links: &[usize], base: &Near, d: &Parts) -> bool {
    if links.is_empty() {
        return false;
    }
    let mut q = Parts {
        cons: Vec::new(),
        ors: (links.iter())
            .map(|&j| p.ors[j].clone())
            .filter(|o| !o.is_empty())
            .collect(),
        atoms: OnceCell::new(),
        hull: OnceCell::new(),
        failed: Cell::new(0),
        id: Cell::new(0),
    };
    for a in d.atoms() {
        base.bounds(a, &mut q.cons);
    }
    q.put(d);
    matches!(settle(q, false), Ok(None))
}

/// The least and the greatest value of each atom, as [`Near::one`] keeps them; an atom absent
/// is unbounded.
type AtomBounds = BTreeMap<Atom, (Option<Int>, Option<Int>)>;

/// A part of a formula that [`bounds_refute`] reads: a constraint, or a disjunction.
enum Unit<'a> {
    Con(&'a Con),
    Or(&'a [Rc<Parts>]),
}

impl<'a> Unit<'a> {
    /// The atoms of the part but `x`, each once.
    fn atoms(&self, x: &Atom) -> Vec<&'a Atom> {
        let cons: Vec<&'a Con> = match self {
            Unit::Con(c) => vec![c],
            Unit::Or(ds) => ds.iter().flat_map(|d| &d.cons).collect(),
        };
        let mut atoms: Vec<&'a Atom> = (cons.into_iter())
            .flat_map(|c| c.lin.terms.keys())
            .filter(|a| *a != x)
            .collect();
        atoms.sort_unstable();
        atoms.dedup();
        atoms
    }
}

/// Whether the bounds of the atoms, propagated, show that the parts `f` with the bound `extra`
/// on the atom `x` have no point. A constraint moves the bounds of each of its atoms by the
/// bounds of the others. A disjunction moves each atom that all its disjuncts mention to the
/// join of the bounds each disjunct leaves it, a disjunct's own constraints being propagated
/// twice from the bounds so far, and a disjunct left with an atom that has no value being
/// dropped; the disjunctions below a disjunct are not read, which leaves it more points, so
/// every answer `true` is a proof. The parts are read once in breadth-first order from the
/// constraints, two parts being neighbors when they share an atom other than `x`, and once in
/// the reverse order: on a chain of definitions the first reading carries the bounds from
/// each end to the middle and the second carries them on to the other end. `x` is left out
/// of the neighbors because the guards on it reach every part of a chain of guards, so that
/// every part would be one step from the constraints. The order is that of the parts'
/// structure, not of the atoms' names. Each reading costs each constraint once, `O(n log n)`
/// for parts of `n` terms with the map from atoms to parts.
///
/// Complexity tradeoff: the propagation is not repeated until no bound moves, so a proof that
/// needs bounds carried along a chain more than twice is not found here; [`learn`] then asks
/// [`settle`], and a disjunct no bound refutes is tested by its own propagation in [`probe`],
/// as before. Why: propagating bounds until none moves can move a bound by one per round on a
/// cycle of constraints with no point (`x >= y + 1`, `y >= x`), so the rounds grow with the
/// bounds' magnitude, not with the parts. Trigger: a proof that needs a bound carried back
/// along a chain after it was carried there. Tests:
/// `l01_25_preimage_catalog::s22::chain_cross_above_its_width_scales` (cross at 12 and 96,
/// COMPLEXITY.md S22) and `l01_38_presburger::probe::guards_beyond_the_inputs_scale` (guards
/// on symbols whose names do not sort in the chain's order). A complete solution is the exact
/// projection of the formula onto `x`, which with disjunctions is exponential in them.
fn bounds_refute(f: &Parts, x: &Atom, extra: &Con) -> bool {
    let units: Vec<Unit<'_>> = (f.cons.iter().map(Unit::Con))
        .chain(f.ors.iter().map(|ds| Unit::Or(ds)))
        .collect();
    let atoms: Vec<Vec<&Atom>> = units.iter().map(|u| u.atoms(x)).collect();
    let mut by_atom: BTreeMap<&Atom, Vec<usize>> = BTreeMap::new();
    for (u, xs) in atoms.iter().enumerate() {
        for a in xs {
            by_atom.entry(a).or_default().push(u);
        }
    }
    // Breadth first from the first part of each set of connected parts.
    let mut seen = vec![false; units.len()];
    let mut order: Vec<usize> = Vec::with_capacity(units.len());
    let mut done: BTreeSet<&Atom> = BTreeSet::new();
    let mut head = 0;
    for start in 0..units.len() {
        if seen[start] {
            continue;
        }
        seen[start] = true;
        order.push(start);
        while head < order.len() {
            for a in &atoms[order[head]] {
                if done.insert(a) {
                    for &v in &by_atom[a] {
                        if !seen[v] {
                            seen[v] = true;
                            order.push(v);
                        }
                    }
                }
            }
            head += 1;
        }
    }
    let mut b = AtomBounds::new();
    let first = narrow(extra, &mut b);
    let mut read = |u: usize| match &units[u] {
        Unit::Con(c) => narrow(c, &mut b),
        Unit::Or(ds) => narrow_or(ds, &mut b),
    };
    !(first && order.iter().rev().all(|&u| read(u)) && order.iter().all(|&u| read(u)))
}

/// Moves the bounds in `b` of the atoms of the disjunction `ds` to the join of those its
/// disjuncts leave ([`bounds_refute`]); `false` when every disjunct is left without a point.
fn narrow_or(ds: &[Rc<Parts>], b: &mut AtomBounds) -> bool {
    let mut join: Option<AtomBounds> = None;
    for d in ds {
        let mut own: AtomBounds = (d.cons.iter().flat_map(|c| c.lin.terms.keys()))
            .map(|a| (a.clone(), b.get(a).cloned().unwrap_or_default()))
            .collect();
        let holds = (0..2).all(|_| d.cons.iter().all(|c| narrow(c, &mut own)));
        if !holds {
            continue;
        }
        join = Some(match join {
            None => own,
            // An atom one disjunct does not mention keeps its bounds there, so the join keeps
            // only the atoms both mention.
            Some(j) => (j.into_iter())
                .filter_map(|(a, (l, h))| {
                    let (ol, oh) = own.get(&a)?;
                    let lo = l.zip(ol.as_ref()).map(|(l, o)| l.min(o.clone()));
                    let hi = h.zip(oh.as_ref()).map(|(h, o)| h.max(o.clone()));
                    Some((a, (lo, hi)))
                })
                .collect(),
        });
    }
    let Some(join) = join else {
        return false;
    };
    join.into_iter()
        .all(|(a, (lo, hi))| narrow_to(b, &a, lo, hi))
}

/// Moves the bounds in `b` of the atoms of `c` by the bounds of its other atoms; `false` when
/// an atom is left with no value, or `c` has no atom and does not hold.
fn narrow(c: &Con, b: &mut AtomBounds) -> bool {
    match c.rel {
        Rel::Ge => narrow_ge(&c.lin, true, b),
        Rel::Eq => narrow_ge(&c.lin, true, b) && narrow_ge(&c.lin, false, b),
    }
}

/// [`narrow`] for `lin >= 0`, or for `-lin >= 0` unless `sign`.
fn narrow_ge(lin: &Lin, sign: bool, b: &mut AtomBounds) -> bool {
    let signed = |k: &Int| if sign { k.clone() } else { -k };
    // The greatest value of each term `coef·x`, `None` when `x` is unbounded that way.
    let most: Vec<Option<Int>> = (lin.terms.iter())
        .map(|(a, coef)| {
            let coef = signed(coef);
            let (lo, hi) = b.get(a)?;
            if coef.is_positive() {
                hi.as_ref().map(|h| &coef * h)
            } else {
                lo.as_ref().map(|l| &coef * l)
            }
        })
        .collect();
    let unbounded = most.iter().filter(|m| m.is_none()).count();
    let sum = (most.iter().flatten()).fold(signed(&lin.constant), |s, m| &s + m);
    if lin.terms.is_empty() {
        return !sum.is_negative();
    }
    for ((a, coef), m) in lin.terms.iter().zip(&most) {
        let coef = &signed(coef);
        // The greatest value of the other terms and the constant, when it is bounded.
        let rest = match (m, unbounded) {
            (Some(m), 0) => &sum - m,
            (None, 1) => sum.clone(),
            _ => continue,
        };
        // `coef·x >= -rest`.
        let r = -&rest;
        let ok = if coef.is_positive() {
            // `x >= ceil(r / coef)`.
            narrow_to(b, a, Some(-&(-&r).div_floor(coef)), None)
        } else {
            // `x <= floor(r / coef)`, `coef` below zero.
            narrow_to(b, a, None, Some((-&r).div_floor(&-coef)))
        };
        if !ok {
            return false;
        }
    }
    true
}

/// Moves the bounds in `b` of `a` in to `lo` and `hi` where they are given and tighter;
/// `false` when `a` is left with no value.
fn narrow_to(b: &mut AtomBounds, a: &Atom, lo: Option<Int>, hi: Option<Int>) -> bool {
    let (l, h) = b.entry(a.clone()).or_default();
    if let Some(lo) = lo
        && l.as_ref().is_none_or(|l| lo > *l)
    {
        *l = Some(lo);
    }
    if let Some(hi) = hi
        && h.as_ref().is_none_or(|h| hi < *h)
    {
        *h = Some(hi);
    }
    !matches!((&*l, &*h), (Some(l), Some(h)) if l > h)
}

/// A point of the formula of [`probe`]'s parts `p` where the disjunct `d` holds, `d` being a
/// disjunct of the disjunction that `p` lacks while it is tested, or `None` when [`pick`]
/// finds none. In each other disjunction `pick` tries first the disjuncts that `held` marks as
/// held by no point, so that the point holds as many of them as its search reaches. The point
/// is one of every part: [`pick`] takes a disjunct of each disjunction, below `d` and below
/// each disjunct taken too, and gives a point of the constraints it took, so it is not
/// checked again (a check cost a test of every disjunct per point; item
/// PROJECT-canon-precision).
/// The bounds in `implied`, which the formula implies, are added to the parts, so that the
/// search does not choose a value of an atom that no point has.
/// With `backward`, [`pick`] reads the disjunctions from the first, not from the last.
fn point_with(
    p: &Parts,
    held: &[Vec<bool>],
    d: &Parts,
    implied: &Near,
    backward: bool,
) -> Option<Model> {
    let others = || p.ors.iter().zip(held).filter(|(o, _)| !o.is_empty());
    let mut cons = p.cons.clone();
    implied
        .one
        .keys()
        .for_each(|a| implied.bounds(a, &mut cons));
    let mut q = Parts {
        cons,
        ors: others()
            .map(|(o, hs)| {
                let new = o.iter().zip(hs).filter(|(_, h)| !**h);
                let old = o.iter().zip(hs).filter(|(_, h)| **h);
                new.chain(old).map(|(e, _)| e.clone()).collect()
            })
            .collect(),
        atoms: OnceCell::new(),
        hull: OnceCell::new(),
        failed: Cell::new(0),
        id: Cell::new(0),
    };
    q.put(d);
    if backward {
        q.ors.reverse();
    }
    pick(&q, true).ok()
}

/// Points for [`probe_to`] found by searches that force many disjuncts at once: first all the
/// disjuncts of `p` that `held` marks as held by no point, each disjunction with its forced
/// disjuncts all taken; when [`pick`] finds no point, each half of the forced disjuncts in
/// turn, down to one. Each point is pushed onto `points`, and every disjunct it holds is
/// marked in `held`: those forced and those [`pick`] took (each disjunction not forced is
/// read with its unmarked disjuncts first, so that the point holds as many of them as the
/// search reaches). Returns, for each disjunct, whether its search alone was made and found
/// no point; [`probe_to`] does not search forward for such a disjunct again but still tests
/// it by a propagation, so the disjuncts it removes are those it removed before, the ones with
/// no point. The points are those of `p`: [`pick`] gives a point of every part it is asked of
/// (each disjunction has a disjunct taken, and the model is a point of the constraints taken),
/// and the parts asked are `p` with some disjuncts forced and the bounds that `p` implies.
///
/// Complexity tradeoff: one search per disjunct, as [`probe_to`] made before (item
/// PROJECT-canon-precision, method (b)), costs `r` searches of the whole formula for `r`
/// disjuncts no earlier point holds, `O(r n log n)`, which grew with `n` on the difference
/// chain (39.4 times the bytes at `8n`, limit 13.2), the three-atom chain (16.6 times) and the
/// wide named disjunction (25.8 times), measured after batch 101. Here a set of `s` forced disjuncts that has a point costs one
/// search, and one without costs two more, of its halves, so that `f` disjuncts with no point
/// cost `O(f log r)` searches and the others `O(f log r + 1)` together: on those chains, where
/// the disjuncts that no greedy point holds all have a point together, one search does all.
/// The disjuncts are forced in rounds: one whose bounds of one atom exclude those of a
/// disjunct forced before it in the round waits for the next. Taken a round each, a
/// disjunction of `m` cases that exclude each other, each with a point, cost `m` rounds of one
/// search each, `O(m n log n)`: 20.1 times the bytes at `8n` (limit 14.1) on a chain whose
/// cases each read one stage (`exclusive_cases`). Here the first search of a round that finds
/// a point also settles the disjuncts left waiting ([`hold_waiting`]): each is marked held
/// when the point, with the atoms that only that disjunct's disjunction reads moved
/// ([`own_repair_in`]), satisfies it, which costs `O(d log n)` for a disjunct of `d`
/// constraints, so the `m` cases cost one search and `O(m log n)` repairs, 10.0 times the
/// bytes at `8n`. What is given up: a case whose point needs an atom moved that another
/// disjunction or the rest of the formula reads is not repaired and still waits for a round of
/// its own, as before; such cases cost what they cost before. Forced all in one round (method
/// (c)), such cases share no point, so their halves cost a search each down to one case: the
/// chain of guarded remainders took 77.7
/// times the bytes at `8n` (limit 15.4); in rounds 8.8 times. On the remainder chains `m` stops at the classes of the modulus (spread and
/// sliced chains, sizes 8 to 64: 6.8 and 7.5 times the work, limit 17.6; 32 to 256: 7.5 and
/// 11.1 times). A set of values of one atom, which would cost a round per piece, is not
/// tested here ([`one_atom_set`] in [`probe_unhandled`]).
/// When most disjuncts have no point (`f` near `r`), the halving adds up to `2r` searches to
/// the propagation each of them costs anyway, a constant factor. The held marks come from
/// the disjuncts [`pick`] took, read once each, not from a test of every disjunct at each
/// point (`O(n)` per point). Tests: the scaling tests of
/// `l01_38_presburger::disj_groups`, `l01_39_reduced_product::named_test` and
/// `l01_39_reduced_product::deep_condition`, and `ladder::a_chain_of_guarded_remainders_scales`
/// (COMPLEXITY.md PROJECT-canon-precision).
fn search_by_halves(
    p: &Parts,
    held: &mut [Vec<bool>],
    points: &mut Vec<Model>,
    implied: &Near,
) -> Vec<Vec<bool>> {
    let mut cons = p.cons.clone();
    implied
        .one
        .keys()
        .for_each(|a| implied.bounds(a, &mut cons));
    // Complexity tradeoff: a set of values of one atom that is kept untested ([`one_atom_set`]
    // in [`probe_unhandled`]), every disjunct of it held, was read by each search, so `r`
    // searches over a set of `h` pieces cost `O(r h)` more: on a chain of `k` cases of one
    // remainder over `x` with `64k` holes, `k` searches, one per case, `O(k^2)` (16 times the
    // pieces at 8 times the holes from 512, the limit failed). Each such set is read here once,
    // as its pieces sorted and merged (`O(h log h)`); a search leaves it out, and the point is
    // looked up in it by binary search (`O(log h)`). Only when the point lies outside the set is
    // the search made again with the set, as before, so the points are those of `p`.
    let sets: Vec<Option<OneAtomSet>> = (p.ors.iter().zip(held.iter()))
        .map(|(o, hs)| {
            (!o.is_empty() && hs.iter().all(|h| *h) && one_atom_set(o)).then(|| OneAtomSet::of(o))
        })
        .collect();
    // The atoms of those sets, which a repair below keeps at the point's values.
    let set_atoms: BTreeSet<&Atom> = (p.ors.iter().zip(&sets))
        .filter(|(_, s)| s.is_some())
        .flat_map(|(o, _)| o.iter().flat_map(|d| &d.cons))
        .flat_map(|c| c.lin.terms.keys())
        .collect();
    // The constraints that every search takes, indexed for the repairs below.
    let mut base = Near::default();
    cons.iter().for_each(|c| base.add(0, c));
    // One search with the disjuncts in `forced` (by disjunction) all taken, and without the
    // sets above when `bare`; a point, the disjuncts [`pick`] took, and, when `note`, the
    // constraints of those disjuncts indexed.
    let ask = |held: &[Vec<bool>], forced: &[Vec<usize>], bare: bool, note: bool| {
        let mut q = Parts {
            cons: cons.clone(),
            ors: Vec::new(),
            atoms: OnceCell::new(),
            hull: OnceCell::new(),
            failed: Cell::new(0),
            id: Cell::new(0),
        };
        for (((o, hs), fs), set) in p.ors.iter().zip(held).zip(forced).zip(&sets) {
            if o.is_empty() || (bare && set.is_some()) {
                continue;
            }
            if !fs.is_empty() {
                fs.iter().for_each(|&at| q.put(&o[at]));
                continue;
            }
            let new = o.iter().zip(hs).filter(|(_, h)| !**h);
            let old = o.iter().zip(hs).filter(|(_, h)| **h);
            q.ors.push(new.chain(old).map(|(e, _)| e.clone()).collect());
        }
        let (m, took) = pick_taking(&q, true).ok()?;
        let mut near = Near::default();
        if note {
            (took.iter().flat_map(|t| &t.cons)).for_each(|c| near.add(0, c));
        }
        let took: HashSet<*const Parts> = took.into_iter().map(|t| t as *const Parts).collect();
        Some((m, took, near))
    };
    // One search with the disjuncts in `forced` all taken; on a point, marks the disjuncts it
    // holds, and those of `waiting` it holds once repaired ([`hold_waiting`]), and keeps it.
    // Without a point when the sets are left out, there is none with them.
    let mut search =
        |held: &mut [Vec<bool>], forced: &[Vec<usize>], waiting: &mut [Vec<usize>]| -> bool {
            let note =
                (forced.iter().zip(waiting.iter())).any(|(f, w)| !f.is_empty() && !w.is_empty());
            let Some((m, took, near)) = ask(held, forced, true, note) else {
                return false;
            };
            let inside = sets.iter().flatten().all(|s| s.holds(&m));
            let Some((m, took, near)) = (if inside {
                Some((m, took, near))
            } else {
                ask(held, forced, false, note)
            }) else {
                return false;
            };
            for (((o, hs), fs), set) in p.ors.iter().zip(held.iter_mut()).zip(forced).zip(&sets) {
                if set.is_some() {
                    continue;
                }
                for (e, h) in o.iter().zip(hs.iter_mut()) {
                    *h = *h || took.contains(&Rc::as_ptr(e));
                }
                fs.iter().for_each(|&at| hs[at] = true);
            }
            if note {
                hold_waiting(p, forced, waiting, held, &m, (&base, near), &set_atoms);
            }
            points.push(m);
            true
        };
    let mut failed: Vec<Vec<bool>> = p.ors.iter().map(|o| vec![false; o.len()]).collect();
    // The disjuncts not yet forced in a search, in the order of the parts.
    let mut left: Vec<(usize, usize)> = (p.ors.iter().enumerate())
        .flat_map(|(i, o)| (0..o.len()).map(move |at| (i, at)))
        .collect();
    while !left.is_empty() {
        // One round: each disjunct no point holds is forced, but one whose bound of one atom
        // the bounds of one atom of those forced before it in the round exclude, which waits
        // for the next round: `y == 0` and `y == 10` of one disjunction are never forced
        // together, a search that fails, and whose failure the solver proves at a cost that
        // grows faster than the parts on a chain. The first search of the round that finds a
        // point marks those that wait which that point, repaired, holds ([`hold_waiting`]),
        // so that they need no round of their own.
        let mut near = Near::default();
        let (mut round, mut later) = (Vec::new(), Vec::new());
        // The disjuncts that wait, by disjunction.
        let mut waiting: Vec<Vec<usize>> = vec![Vec::new(); p.ors.len()];
        for (i, at) in left {
            if held[i][at] {
                continue;
            }
            let d = &p.ors[i][at];
            if !round.is_empty() && near.refutes(&d.cons) {
                later.push((i, at));
                waiting[i].push(at);
                continue;
            }
            for (a, lo, hi) in d.cons.iter().filter_map(one_bound) {
                near.tighten(a, lo, hi);
            }
            round.push((i, at));
        }
        left = later;
        by_halves_of(round, held, &mut failed, &mut waiting, &mut search);
    }
    failed
}

/// After a search of [`search_by_halves`] has found the point `model`, marks in `held` each
/// disjunct listed in `waiting` (by disjunction, each list emptied, so that it is tried once a
/// round) that holds at a point found from `model` by moving only atoms of its own: those
/// that no other constraint the search took reads, but bounds of one atom. Only a disjunct of
/// a disjunction with disjuncts forced in the search, and with no disjunction below it, is
/// tried. The constraints the search took are those every search takes (`parts.0`), the
/// disjuncts [`pick`] took (`parts.1`, to which the forced disjuncts of the disjunctions not
/// tried are added here), and the forced disjuncts of those tried; the atoms of the forced
/// disjuncts of a disjunction tried are its own for its waiting disjuncts when no other
/// disjunction tried reads them, and the atoms of the sets left out of the search
/// (`set_atoms`) are never own. Then the point repaired ([`own_repair_in`]) holds the
/// disjunct, every part the search took but the forced disjuncts of its own disjunction, and
/// so every disjunction: it is a point of the parts, which is all a mark claims.
fn hold_waiting(
    p: &Parts,
    forced: &[Vec<usize>],
    waiting: &mut [Vec<usize>],
    held: &mut [Vec<bool>],
    model: &Model,
    parts: (&Near, Near),
    set_atoms: &BTreeSet<&Atom>,
) {
    let (base, mut took) = parts;
    let tried: Vec<bool> = (forced.iter().zip(waiting.iter()))
        .map(|(f, w)| !f.is_empty() && !w.is_empty())
        .collect();
    let forced_cons = |i: usize| forced[i].iter().flat_map(move |&at| &p.ors[i][at].cons);
    for i in (0..forced.len()).filter(|&i| !tried[i]) {
        forced_cons(i).for_each(|c| took.add(0, c));
    }
    // For each disjunction tried, the atoms of its forced disjuncts; for each atom, the
    // number of those disjunctions that read it.
    let mine: Vec<(usize, BTreeSet<&Atom>)> = (0..forced.len())
        .filter(|&i| tried[i])
        .map(|i| (i, forced_cons(i).flat_map(|c| c.lin.terms.keys()).collect()))
        .collect();
    let mut readers: BTreeMap<&Atom, usize> = BTreeMap::new();
    for a in mine.iter().flat_map(|(_, s)| s) {
        *readers.entry(a).or_default() += 1;
    }
    for (i, mine) in &mine {
        let fixed = |a: &Atom| {
            set_atoms.contains(a)
                || readers
                    .get(a)
                    .is_some_and(|&k| k > usize::from(mine.contains(a)))
        };
        for at in mem::take(&mut waiting[*i]) {
            let d = &p.ors[*i][at];
            if held[*i][at] || !d.ors.is_empty() {
                continue;
            }
            held[*i][at] = d.cons.iter().all(|c| c.holds_linear(model))
                || own_repair_in(&[base, &took], &fixed, model, &d.cons).is_some();
        }
    }
}

/// [`search_by_halves`]'s searches of one round: all the disjuncts of `round` forced, and on
/// a failure each half in turn, down to one, which is then marked in `failed`. `waiting` is
/// handed to each search.
fn by_halves_of(
    round: Vec<(usize, usize)>,
    held: &mut [Vec<bool>],
    failed: &mut [Vec<bool>],
    waiting: &mut [Vec<usize>],
    search: &mut impl FnMut(&mut [Vec<bool>], &[Vec<usize>], &mut [Vec<usize>]) -> bool,
) {
    let width = failed.len();
    let mut stack = vec![round];
    while let Some(s) = stack.pop() {
        let s: Vec<(usize, usize)> = s.into_iter().filter(|&(i, at)| !held[i][at]).collect();
        if s.is_empty() {
            continue;
        }
        let mut forced: Vec<Vec<usize>> = vec![Vec::new(); width];
        s.iter().for_each(|&(i, at)| forced[i].push(at));
        if search(held, &forced, waiting) {
            continue;
        }
        if let [(i, at)] = s[..] {
            failed[i][at] = true;
        } else {
            let mid = s.len() / 2;
            stack.push(s[mid..].to_vec());
            stack.push(s[..mid].to_vec());
        }
    }
}

/// A formula in negation normal form as its top-level constraints and its top-level
/// disjunctions, each a list of disjuncts, each disjunct the parts of it. A disjunct is shared,
/// not copied, when it is handed to a search or a level below, so that a disjunction nested
/// `d` deep is copied at no level above it.
#[derive(Default)]
struct Parts {
    cons: Vec<Con>,
    ors: Vec<Vec<Rc<Parts>>>,
    /// The atoms of the parts' disjunctions (their base, with its id and origin), and the
    /// atoms of the parts, found the first time they are asked for ([`Parts::atoms`]).
    /// They are asked only of a disjunct, which is not changed once it is made.
    atoms: OnceCell<(AtomSet, OrdSet<Atom>)>,
    /// The deep hull of the parts ([`DeepHulls`]), found the first time a disjunction holding
    /// them is joined, and kept for the parts' life, so that a later question on a formula
    /// that holds them reads them at no cost. Asked only of a disjunct, as the atoms are.
    hull: OnceCell<Read>,
    /// The stamp of the last search ([`Parts::witness`]) that found the parts not to hold at its
    /// values, so that the search does not read them again while its values are unchanged.
    failed: Cell<u64>,
    /// The id of a disjunct, drawn the first time it is asked for ([`Parts::id`]), 0 until
    /// then. Like the atoms it is asked only of a disjunct, which is not changed once made.
    id: Cell<u64>,
}

impl Clone for Parts {
    /// A copy, which may be changed, so it takes its own id when one is asked of it.
    fn clone(&self) -> Parts {
        Parts {
            cons: self.cons.clone(),
            ors: self.ors.clone(),
            atoms: self.atoms.clone(),
            hull: OnceCell::new(),
            failed: self.failed.clone(),
            id: Cell::new(0),
        }
    }
}

/// Drops the disjuncts nested below on an explicit stack, not by recursion on their depth
/// (COMPLEXITY.md S27). A disjunct still shared elsewhere is left to its other holders.
impl Drop for Parts {
    fn drop(&mut self) {
        if self.ors.is_empty() {
            return;
        }
        let mut stack: Vec<Rc<Parts>> = self.ors.drain(..).flatten().collect();
        while let Some(d) = stack.pop() {
            if let Ok(mut p) = Rc::try_unwrap(d) {
                stack.extend(p.ors.drain(..).flatten());
            }
        }
    }
}

impl Parts {
    /// The parts of a formula in negation normal form. The disjuncts nested below are made on
    /// an explicit stack, each before the disjunct that holds it, so that a nest of any depth
    /// is read without recursion (COMPLEXITY.md S27). A disjunction that the formula holds as a
    /// conjunct in more than one place, and a disjunct held in more than one place, are made
    /// once and shared, as [`Rc`]s, at each place (COMPLEXITY.md S31).
    // Complexity tradeoff: a part reached twice in the formula is made once, but the skip of
    // one already conjoined above reaches only the places below the place that conjoined it.
    // A shared conjunction or disjunction used as a conjunct at places on separate branches
    // (disjuncts beside each other, not nested) is read at each: a conjunction's k constraints
    // are added to the base of each place, and a disjunction's list of k disjuncts is copied
    // into each (`ds.clone()`), where `settle`, `pick` and `witness` read it again. No answer is
    // given up. Trigger: a `let`-bound conjunction or disjunction of k parts used at each of d
    // disjuncts of one disjunction costs O(d k) here: with k = d named credit limits in each of
    // d tiers side by side, `product::arms` allocates 208.8 MB at d = 30 and 10.59 GB at 240,
    // 50.7 times (ST-formula-wide repair 4). [`project_each`] and [`decide`] now take a part
    // common to every disjunct out of the disjunction first ([`factored`], ST-formula-sibling)
    // when it is linked to no atom of the rest of the disjuncts, so this shape reaches here
    // with the part once. A linked part is not taken out, since `project_parts` hulls each
    // disjunction of a part apart from the rest: `rule && (x <= 0 || y <= 0)` projects `x` to
    // `[..]` where `(rule && x <= 0) || (rule && y <= 0)` gives `[..=0, 5..]`; it still costs
    // O(d k) here, as do a part not common to every disjunct and [`satisfiable`], since taking
    // the part out may change the model it returns. Test of the side-by-side shape:
    // `l01_39_reduced_product::named_test::arms_of_named_limits_in_side_by_side_tiers_take_time_near_linear_in_the_depth`.
    // The nested shapes are near linear (`Formula::and` and `Formula::or` keep a named part
    // whole): tests in `l01_39_reduced_product::named_test`
    // `arms_of_a_wide_named_conjunction_at_each_tier_take_time_near_linear_in_the_depth`,
    // `..._wide_named_disjunction_at_each_tier_...`, `..._wide_named_disjunction_required_at_each_tier_...`
    // and `arms_of_a_chain_of_named_{conjunctions,disjunctions}_take_time_near_linear_in_its_length`,
    // COMPLEXITY.md S31b. A complete solution holds a shared conjunction as a shared chunk of
    // the base and a shared disjunction as one shared list (`Rc<[Rc<Parts>]>`), and lets
    // `settle`, `pick` and `witness` read a chunk or a disjunction they have already met once
    // per model; reading a repeated disjunction once can change which disjuncts `pick` takes,
    // so the models it returns must then be checked against the present ones.
    fn of(f: Formula) -> Parts {
        /// The shared parts known to hold (`yes`) and known not to hold (`no`) where a part is
        /// made: those conjoined on the way down, and the shared disjuncts beside a disjunct.
        #[derive(Clone, Default)]
        struct Assumed {
            yes: imbl::HashSet<Id>,
            no: imbl::HashSet<Id>,
        }
        /// A disjunction being entered: its key when shared, its disjuncts left and those
        /// made, and what is assumed where a disjunct held by it alone is made.
        type Entering = (
            Option<Id>,
            std::vec::IntoIter<Formula>,
            Vec<Rc<Parts>>,
            Assumed,
        );
        /// A part being made: its disjunctions not yet entered, last first, the disjunction
        /// being entered, the part's own key when shared, and what is assumed where it is.
        struct Frame {
            p: Parts,
            todo: Vec<Formula>,
            arms: Option<Entering>,
            id: Option<Id>,
            at: Assumed,
        }
        fn open(
            f: Formula,
            id: Option<Id>,
            mut at: Assumed,
            twice: &std::collections::HashSet<Id>,
        ) -> Frame {
            let mut p = Parts::default();
            let mut todo = Vec::new();
            let mut stack = vec![f];
            while let Some(mut g) = stack.pop() {
                // A shared part already conjoined above holds here; one known not to hold
                // makes the part false.
                if let Some(k) = Id::among(&g, twice) {
                    if at.yes.contains(&k) {
                        continue;
                    }
                    if at.no.contains(&k) {
                        let mut p = Parts::default();
                        p.ors.push(Vec::new());
                        return Frame {
                            p,
                            todo: Vec::new(),
                            arms: None,
                            id,
                            at,
                        };
                    }
                    at.yes.insert(k);
                }
                match &mut g {
                    Formula::Con(c) => p.cons.push(Con::take(c)),
                    // Reversed, so the conjuncts are added in order.
                    Formula::And(_) => {
                        stack.extend(g.into_parts().expect("a conjunction").into_iter().rev())
                    }
                    Formula::Or(_) => todo.push(g),
                    Formula::Not(_) => unreachable!("a formula in negation normal form"),
                }
            }
            todo.reverse();
            Frame {
                p,
                todo,
                arms: None,
                id,
                at,
            }
        }
        // The parts that the formula reaches through more than one parent: only these are made
        // once and assumed by key, so the parts made follow the formula's own sharing, never the
        // handles that hold its parts outside it.
        let twice = Id::reached_twice(&f);
        // The disjunctions and the disjuncts already made that are held in more than one place,
        // each made with nothing assumed, so that it serves at every place.
        let mut ors: HashMap<Id, Vec<Rc<Parts>>> = HashMap::new();
        let mut arms: HashMap<Id, Rc<Parts>> = HashMap::new();
        let mut stack = vec![open(f, None, Assumed::default(), &twice)];
        let mut made: Option<Rc<Parts>> = None;
        while let Some(top) = stack.last_mut() {
            if let (Some(q), Some((_, _, done, _))) = (made.take(), &mut top.arms) {
                // A false disjunct is left out.
                if !q.ors.iter().any(Vec::is_empty) {
                    done.push(q);
                }
            }
            if let Some((_, left, done, at)) = &mut top.arms {
                if let Some(g) = left.next() {
                    match Id::among(&g, &twice) {
                        Some(id) => match arms.get(&id) {
                            Some(q) => {
                                if !q.ors.iter().any(Vec::is_empty) {
                                    done.push(Rc::clone(q))
                                }
                            }
                            None => stack.push(open(g, Some(id), Assumed::default(), &twice)),
                        },
                        None => {
                            let at = at.clone();
                            stack.push(open(g, None, at, &twice))
                        }
                    }
                    continue;
                }
                let (id, _, done, _) = top.arms.take().expect("the disjunction entered");
                if let Some(id) = id {
                    ors.insert(id, done.clone());
                }
                top.p.ors.push(done);
            }
            if let Some(g) = top.todo.pop() {
                let id = Id::among(&g, &twice);
                if let Some(ds) = id.as_ref().and_then(|id| ors.get(id)) {
                    top.p.ors.push(ds.clone());
                    continue;
                }
                // A shared disjunction is made with nothing assumed. Each of its disjuncts
                // held by it alone is made with its shared disjuncts assumed not to hold, since
                // it serves only where they do not; a shared disjunct known to hold makes the
                // disjunction hold, and one known not to hold, or met twice, is left out.
                let mut at = match id {
                    Some(_) => Assumed::default(),
                    None => top.at.clone(),
                };
                let mut keep = Vec::new();
                let mut holds = false;
                for d in g.into_parts().expect("a disjunction") {
                    if let Some(k) = Id::among(&d, &twice) {
                        if at.yes.contains(&k) {
                            holds = true;
                            break;
                        }
                        if at.no.insert(k).is_some() {
                            continue;
                        }
                    }
                    keep.push(d);
                }
                if !holds {
                    top.arms = Some((id, keep.into_iter(), Vec::new(), at));
                }
                continue;
            }
            let Frame { p, id, .. } = stack.pop().expect("the top frame");
            if stack.is_empty() {
                return p;
            }
            let q = Rc::new(p);
            if let Some(id) = id {
                arms.insert(id, Rc::clone(&q));
            }
            made = Some(q);
        }
        unreachable!("the root returns")
    }

    /// Adds the parts of the disjunct `d`, sharing its disjunctions.
    fn put(&mut self, d: &Parts) {
        self.cons.extend(d.cons.iter().cloned());
        self.ors.extend(d.ors.iter().cloned());
    }

    /// Whether the parts hold at `values`, read as the solver reads them: each atom, a product
    /// included, a variable of its own ([`Con::holds_linear`]), not as [`Formula::holds`] reads a
    /// product, through its factors (PRES-product-parity).
    fn holds(&self, values: &Model) -> bool {
        self.witness(values, fresh_stamp(), &mut Vec::new())
    }

    /// Whether the parts hold at `values` (read as [`Parts::holds`] reads them), and if so, in
    /// `out`, the parts and, below them, the first disjunct of each disjunction that holds there, each before
    /// the disjuncts taken below it and the disjunctions read last to first, the order in
    /// which [`pick`] reads them. A disjunction is read until a disjunct holds, and each part
    /// is entered at most once, so the cost is at most the size of the parts. A part found not
    /// to hold is marked with `stamp`, and a part so marked is not entered again: a caller
    /// passes a new stamp whenever `values` change.
    fn witness<'a>(&'a self, values: &Model, stamp: u64, out: &mut Vec<&'a Parts>) -> bool {
        let fails = |p: &Parts| {
            let no = p.failed.get() == stamp || {
                TESTED.set(TESTED.get() + 1);
                !p.cons.iter().all(|c| c.holds_linear(values))
            };
            if no {
                p.failed.set(stamp);
            }
            no
        };
        /// A part entered: the disjunctions not yet shown to hold are `p.ors[..left]`, the
        /// last of them read at its disjunct `at`, and `mark` is the length of `out` before
        /// that disjunct was entered.
        struct Frame<'a> {
            p: &'a Parts,
            left: usize,
            at: usize,
            mark: usize,
        }
        let start = out.len();
        if fails(self) {
            return false;
        }
        out.push(self);
        // An explicit stack, since a nest can be deeper than a thread's stack allows.
        let mut stack = vec![Frame {
            p: self,
            left: self.ors.len(),
            at: 0,
            mark: out.len(),
        }];
        while let Some(top) = stack.last_mut() {
            if top.left == 0 {
                // Every disjunction of the part holds: the part holds, and the disjunct of the
                // part above it that it is holds.
                stack.pop();
                if let Some(up) = stack.last_mut() {
                    up.left -= 1;
                    up.at = 0;
                    up.mark = out.len();
                }
                continue;
            }
            let ds = &top.p.ors[top.left - 1];
            let Some(d) = ds.get(top.at) else {
                // No disjunct holds: the part fails, and the part above tries its next one.
                top.p.failed.set(stamp);
                stack.pop();
                let Some(up) = stack.last_mut() else {
                    out.truncate(start);
                    return false;
                };
                out.truncate(up.mark);
                up.at += 1;
                continue;
            };
            if !fails(d) {
                out.push(d);
                stack.push(Frame {
                    p: d,
                    left: d.ors.len(),
                    at: 0,
                    mark: out.len(),
                });
            } else {
                top.at += 1;
            }
        }
        true
    }

    /// The id of the parts, drawn the first time it is asked for: no other parts have it, so
    /// a memo keyed by it ([`BelowKey`]) knows a disjunct shared by several disjunctions,
    /// and ids are never reused, so the memo needs not hold the disjunct.
    fn id(&self) -> u64 {
        if self.id.get() == 0 {
            self.id.set(fresh_id());
        }
        self.id.get()
    }

    /// The atoms of the parts. Each disjunct's set is found once, from its disjuncts' sets,
    /// with the set of the atoms of its disjunctions alone (its base) kept beside it, under an
    /// id ([`AtomSet`]). The union of a disjunction's sets is the union of its disjuncts' bases
    /// ([`union_sets`]) with their own atoms added ([`union_of`]); the base of a part is the
    /// union of its disjunctions' sets. Each union is found once per call for each list of
    /// ids it is made from, so that two disjunctions whose disjuncts have the same bases and
    /// atoms of their own share one set and one id, as do the parts that hold them.
    // Complexity tradeoff: the naive version adds every atom of each disjunct's set to the
    // largest: on a tree an atom is then added only to a set at least twice the size of the
    // one it came from, O(n log² n) for a nest of `n` constraints; but where the disjuncts at
    // each level hold the same disjunctions of the level below (PRES-nest-empty), the sets
    // are equal or differ in a few atoms and are not shared, and each level adds all of one
    // to the other, O(n² log n). Used: unions kept by the ids of the sets they are made from,
    // and each set made by adding atoms to one set records it as its origin, so that sets of
    // one origin are united by adding the atoms each added to it, O(r log n) for `r` such
    // atoms: O(n log n) on the nest, on a chain of two disjunctions each held by one disjunct
    // of both at the level above, and on two disjunctions each held by both disjuncts of both
    // at the level above, with atoms of their own that the other lacks
    // (`l01_38_presburger::nest_empty`, COMPLEXITY.md PRES-nest-empty). What is given up:
    // maps from ids to sets for one call, and the cost of the naive union for sets of no
    // common origin (made from different disjunctions with different atoms), O(s log n) for
    // the atoms `s` of the smaller sets, O(n log² n) on a tree. A complete solution keeps the
    // sets as trees whose equal parts are one node, so that a union costs the parts that
    // differ.
    fn atoms(&self) -> &OrdSet<Atom> {
        // The unions found, each with its id, by the ids they are made from.
        let mut memo = Unions::default();
        // An explicit stack, since a nest can be deeper than a thread's stack allows; a
        // disjunct shared by two disjunctions is found once, its set marking it as visited.
        let mut stack: Vec<&Parts> = vec![self];
        while let Some(&p) = stack.last() {
            if p.atoms.get().is_some() {
                stack.pop();
                continue;
            }
            let open = stack.len();
            let below = p.ors.iter().flatten().map(|d| &**d);
            stack.extend(below.filter(|d| d.atoms.get().is_none()));
            if stack.len() > open {
                continue;
            }
            stack.pop();
            let sets: Vec<AtomSet> = (p.ors.iter()).map(|ds| union_of(ds, &mut memo)).collect();
            let base = union_sets(sets, &mut memo.sets);
            let mut set = base.set.clone();
            set.extend(p.cons.iter().flat_map(|c| c.lin.terms.keys().cloned()));
            let _ = p.atoms.set((base, set));
        }
        &self.atoms.get().expect("the set just found").1
    }
}

/// A set of atoms of [`Parts::atoms`], under an id that no other set has (0 for the empty set
/// that is the base of a part with no disjunctions), with the set it was made from by adding
/// atoms, if any: its id, its atoms, and the atoms added, so that sets made from one set are
/// united by adding those alone.
#[derive(Clone)]
struct AtomSet {
    id: u64,
    set: OrdSet<Atom>,
    from: Option<Rc<Origin>>,
}

/// The set an [`AtomSet`] was made from: its id and atoms, and the atoms added to it.
type Origin = (u64, OrdSet<Atom>, Vec<Atom>);

/// The unions found by [`Parts::atoms`] in one call: of sets, by their sorted ids; of a set and
/// atoms added to it, by its id and the sorted atoms.
#[derive(Default)]
struct Unions {
    sets: HashMap<Vec<u64>, AtomSet>,
    added: HashMap<(u64, Vec<Atom>), AtomSet>,
}

/// The union of the atoms of the disjuncts `ds`, whose sets are found ([`Parts::atoms`]): the
/// union of their bases ([`union_sets`]) with the atoms of their own rows added, made from
/// that union, kept in `memo` by its id and those atoms.
fn union_of(ds: &[Rc<Parts>], memo: &mut Unions) -> AtomSet {
    let bases = (ds.iter()).map(|d| d.atoms.get().expect("a set found below").0.clone());
    let base = union_sets(bases.collect(), &mut memo.sets);
    let own = ds.iter().flat_map(|d| d.cons.iter());
    let own: BTreeSet<Atom> = own.flat_map(|c| c.lin.terms.keys().cloned()).collect();
    let own: Vec<Atom> = own.into_iter().filter(|a| !base.set.contains(a)).collect();
    if own.is_empty() {
        return base;
    }
    (memo.added.entry((base.id, own)))
        .or_insert_with_key(|(_, own)| {
            let mut set = base.set.clone();
            set.extend(own.iter().cloned());
            AtomSet {
                id: fresh_id(),
                set,
                from: Some(Rc::new((base.id, base.set.clone(), own.clone()))),
            }
        })
        .clone()
}

/// The union of `sets`, kept in `memo` by their ids: one set is itself; sets made from one set
/// are it with the atoms each added; others start as the largest, shared, with the atoms of
/// the others added.
fn union_sets(mut sets: Vec<AtomSet>, memo: &mut HashMap<Vec<u64>, AtomSet>) -> AtomSet {
    sets.sort_unstable_by_key(|s| s.id);
    sets.dedup_by_key(|s| s.id);
    if sets.len() <= 1 {
        return sets.pop().unwrap_or_else(|| AtomSet {
            id: 0,
            set: OrdSet::new(),
            from: None,
        });
    }
    let ids: Vec<u64> = sets.iter().map(|s| s.id).collect();
    if let Some(u) = memo.get(&ids) {
        return u.clone();
    }
    let origin = sets[0].from.as_ref().map(|f| f.0);
    let one_origin =
        origin.is_some() && sets.iter().all(|s| s.from.as_ref().map(|f| f.0) == origin);
    let set = if one_origin {
        let mut set = sets[0].from.as_ref().expect("an origin").1.clone();
        set.extend(
            sets.iter()
                .flat_map(|s| s.from.as_ref().expect("an origin").2.iter().cloned()),
        );
        set
    } else {
        let largest = (0..sets.len())
            .max_by_key(|&i| sets[i].set.len())
            .expect("two sets");
        let mut set = sets.swap_remove(largest).set;
        set.extend(sets.iter().flat_map(|s| s.set.iter().cloned()));
        set
    };
    let u = AtomSet {
        id: fresh_id(),
        set,
        from: None,
    };
    memo.insert(ids, u.clone());
    u
}

/// `f`, negated when `!sign`, with each negation pushed to the constraints: not `t >= 0` is
/// `-t - 1 >= 0`, and not `t == 0` is `t >= 1 || -t >= 1`. The parts of each conjunction and
/// disjunction are sorted, so that the search through them, which takes the first that serves,
/// does not depend on the order they are written in. The sort compares names, so its order
/// reaches an answer only through the names [`Renamed`] gives by color, or not at all: a
/// formula whose atoms share a color is settled, tested and projected by questions whose
/// answers no order of the parts changes ([`settle_as_sets`], [`alone`], [`by_color`],
/// [`project_parts`] with `sets`), and refused when a search would be needed.
fn nnf(f: &Formula, sign: bool) -> Formula {
    f.fold(
        sign,
        |g, s| s != matches!(g, Formula::Not(_)),
        |g, sign, mut parts| {
            let mut out = match (g, sign) {
                (Formula::Not(_), _) => parts.pop().expect("one part"),
                (Formula::And(_), true) | (Formula::Or(_), false) => {
                    Formula::and_keeping(parts, |i| g.kept(i))
                }
                (Formula::And(_), false) | (Formula::Or(_), true) => {
                    Formula::or_keeping(parts, |i| g.kept(i))
                }
                (Formula::Con(c), true) => Formula::Con(c.clone()),
                (Formula::Con(c), false) => {
                    let one = Lin::constant(1);
                    let neg = Formula::Con(Con::ge(&Lin::default(), &c.lin.plus(&one)));
                    if c.rel == Rel::Ge {
                        neg
                    } else {
                        Formula::or(vec![Formula::Con(Con::ge(&c.lin, &one)), neg])
                    }
                }
            };
            // A node held elsewhere is a part passed through whole, already sorted.
            if let Formula::And(gs) | Formula::Or(gs) = &mut out
                && let Some(gs) = Shared::change(gs)
            {
                gs.sort();
            }
            out
        },
    )
}

/// The parts of `f` ([`Parts::of`] its [`nnf`]) with each disjunction removed that [`absorb`]
/// shows to change no answer read over `keep` alone, and the rows over the atoms projected
/// away with it, which [`repair`] reads to give them values.
fn absorbed(f: &Formula, keep: &[Atom]) -> (Parts, Vec<(Atom, Vec<Con>)>) {
    let mut p = Parts::of(nnf(f, true));
    let gone = absorb(&mut p, keep);
    (p, gone)
}

/// The rows over one atom on one side, read by [`absorb`]: each row `x + r >= 0` (a lower
/// bound) or `-x + r >= 0` (an upper bound) by its rest `r`, written as its terms and its
/// constant.
#[derive(Default)]
enum Side<'a> {
    /// No row.
    #[default]
    Empty,
    /// Every row has these terms; the least constant among them.
    Shared(Vec<(&'a Atom, &'a Int)>, &'a Int),
    /// Two rows differ in their terms.
    Mixed,
}

impl<'a> Side<'a> {
    /// Adds the row whose rest has the terms `terms` and the constant `k`.
    fn add(&mut self, terms: Vec<(&'a Atom, &'a Int)>, k: &'a Int) {
        match self {
            Side::Empty => *self = Side::Shared(terms, k),
            Side::Shared(t, least) if *t == terms => *least = (*least).min(k),
            Side::Shared(..) => *self = Side::Mixed,
            Side::Mixed => {}
        }
    }

    /// Whether every lower bound of `self` and upper bound of `upper` sum to a constant at
    /// least zero: their terms cancel, and the least constants sum to zero or more.
    fn fits(&self, upper: &Side<'_>) -> bool {
        match (self, upper) {
            (Side::Empty, _) | (_, Side::Empty) => true,
            (Side::Shared(l, kl), Side::Shared(u, ku)) => {
                l.len() == u.len()
                    && l.iter().zip(u).all(|((a, k), (b, j))| a == b && **k == -*j)
                    && !(*kl + *ku).is_negative()
            }
            _ => false,
        }
    }
}

/// The row `c` read as a bound on `x` ([`Side`]): whether it is a lower bound, and the terms of
/// its rest; `None` when it is an equality or the coefficient of `x` is not 1 or -1.
fn unit_bound<'a>(c: &'a Con, x: &Atom) -> Option<(bool, Vec<(&'a Atom, &'a Int)>)> {
    let k = c.lin.terms.get(x)?;
    let lower = *k == Int::ONE;
    if c.rel != Rel::Ge || !(lower || *k == -&Int::ONE) {
        return None;
    }
    let rest = c.lin.terms.iter().filter(|(a, _)| *a != x).collect();
    Some((lower, rest))
}

/// Removes from `p` each top-level disjunction `D` one of whose disjuncts `d` shows that `D`
/// removes no point once the atoms private to `d` are projected away, and gives, for each
/// such atom, the rows over it (the base's and `d`'s), from which [`repair`] gives it a value.
///
/// An atom of `d` is private when it is a symbol or an auxiliary variable, not a product nor a
/// factor of one, not in `keep`, and in no other top-level disjunction at any depth. `d` serves
/// when it has no disjunction of its own and each of its constraints is an inequality with one
/// private atom, of coefficient 1 or -1; each base row over that atom must be such an
/// inequality too, with no other atom held by a disjunction alone. Writing each row over a
/// private atom `x` as `x + l >= 0` or `u - x >= 0`, `d` serves when `l + u` is a constant at
/// least zero for each pair of a lower and an upper bound of which one or both are `d`'s.
///
/// Why this is exact: with each coefficient of `x` 1 or -1, an integer `x` lies between its
/// bounds at a point of the other atoms exactly when each lower bound is at most each upper
/// bound there (Fourier-Motzkin elimination of `x` is exact over the integers). The pairs with
/// a row of `d` hold everywhere, so the base `R` gives the rest: `∃x (R ∧ d) ≡ ∃x R`. Each row
/// has one private atom, so they are eliminated one by one, and since `R ∧ d` implies `R ∧ D`,
/// which implies `R`, `∃P (R ∧ D) ≡ ∃P R` over the private atoms `P`. No other part reads
/// `P`, so `D` is removed for every question over the other atoms: whether a point exists,
/// and the projections onto `keep`. A disjunction removed this way holds the private atoms
/// of its own disjuncts only, so the removals do not depend on each other or on the order in
/// which they are made. Which disjunctions are removed depends on the structure alone, not on
/// the names or the order of the parts, so [`settle_as_sets`] may run after it; only the
/// disjunct whose rows [`repair`] reads is the first by that order.
///
/// The cost is linear in the size of the parts, times a logarithm: the atoms of each disjunct
/// are found once ([`Parts::atoms`]), each base row is read once, and each disjunct's rows
/// once, compared with the base's bounds as two summaries per atom ([`Side`]).
///
/// Complexity tradeoff: only disjunctions shown removable by one disjunct over private atoms
/// with unit coefficients are removed here; the rest are settled and searched ([`settle`],
/// [`settle_as_sets`], [`pick`]), whose test of a disjunct that the base's point misses solves
/// it with every base row linked to it. What is given up: a formula with many disjunctions
/// linked through one group of base rows, none of them shown removable by this rule (their
/// atoms shared, or with coefficients other than 1 or -1, or bounds that do not cancel), still
/// costs a solve of the group for each such disjunct: quadratic in the formula. A base row over
/// two atoms each held by a single disjunction marks both, though when it bounds the atom only
/// on the side `d` leaves unpaired it would not stop the removal: telling those apart would
/// read the row once for each such atom in it. Why: removing a disjunction requires showing
/// that it changes no projection, which in general is the projection itself; the unit case is
/// the one where elimination is exact and reads only the bounds of one atom. Trigger: a star
/// whose leaves each choose between two bounds (`l01_38_presburger::names::star_with_choices`)
/// is covered; the same with each choice over two leaves is not. Tests:
/// `l01_38_presburger::names::decide_on_tied_disjunctions_scales`,
/// `satisfiable_on_tied_disjunctions_scales` and `project_each_on_tied_disjunctions_scales`.
/// COMPLEXITY.md row DECIDE-disj-chain. A complete solution would be a projection that shares
/// work between the disjuncts of one group (an incremental solver that keeps the eliminated
/// group and adds one disjunct at a time).
fn absorb(p: &mut Parts, keep: &[Atom]) -> Vec<(Atom, Vec<Con>)> {
    if p.ors.is_empty() {
        return Vec::new();
    }
    let (removed, gone) = {
        // The top-level disjunction that holds each atom of a disjunction, or `None` when two
        // or more do.
        let mut owner: HashMap<&Atom, Option<usize>> = HashMap::new();
        for (j, ds) in p.ors.iter().enumerate() {
            for a in ds.iter().flat_map(|d| d.atoms()) {
                let o = owner.entry(a).or_insert(Some(j));
                if *o != Some(j) {
                    *o = None;
                }
            }
        }
        let kept: HashSet<&Atom> = keep.iter().collect();
        let mut factors: HashSet<Atom> = HashSet::new();
        for a in (p.cons.iter().flat_map(|c| c.lin.terms.keys())).chain(owner.keys().copied()) {
            if let Atom::Product(x, y) = a {
                factors.insert(x.atom());
                factors.insert(y.atom());
            }
        }
        // The disjunction that alone holds `a`, when `a` may be private to one of its disjuncts.
        let held_by = |a: &Atom| match (a, owner.get(a)) {
            (Atom::Product(..), _) => None,
            (_, Some(Some(j))) if !kept.contains(a) && !factors.contains(a) => Some(*j),
            _ => None,
        };
        // The base's bounds on each such atom, its rows, and whether a row over it is not a
        // unit inequality with no other such atom.
        #[derive(Default)]
        struct Bounds<'a> {
            lower: Side<'a>,
            upper: Side<'a>,
            rows: Vec<&'a Con>,
            bad: bool,
        }
        let mut base: HashMap<&Atom, Bounds<'_>> = HashMap::new();
        for c in &p.cons {
            let mut own = c.lin.terms.keys().filter(|a| held_by(a).is_some());
            let Some(x) = own.next() else {
                continue;
            };
            if own.next().is_some() {
                for a in c.lin.terms.keys().filter(|a| held_by(a).is_some()) {
                    base.entry(a).or_default().bad = true;
                }
                continue;
            }
            let b = base.entry(x).or_default();
            b.rows.push(c);
            match unit_bound(c, x) {
                Some((true, rest)) => b.lower.add(rest, &c.lin.constant),
                Some((false, rest)) => b.upper.add(rest, &c.lin.constant),
                None => b.bad = true,
            }
        }
        let none = Bounds::default();
        // The rows of each private atom of `d`, a disjunct of disjunction `j`, when `d` shows
        // that `j` removes no point.
        let serves = |j: usize, d: &Parts| -> Option<Vec<(Atom, Vec<Con>)>> {
            if !d.ors.is_empty() {
                return None;
            }
            let mut own: BTreeMap<&Atom, (Side<'_>, Side<'_>, Vec<&Con>)> = BTreeMap::new();
            for c in &d.cons {
                let mut xs = (c.lin.terms.keys()).filter(|a| held_by(a) == Some(j));
                let (Some(x), None) = (xs.next(), xs.next()) else {
                    return None;
                };
                let (lower, rest) = unit_bound(c, x)?;
                let (dl, du, rows) = own.entry(x).or_default();
                (if lower { dl } else { du }).add(rest, &c.lin.constant);
                rows.push(c);
            }
            let mut out = Vec::new();
            for (x, (dl, du, rows)) in own {
                let b = base.get(x).unwrap_or(&none);
                if b.bad || !(b.lower.fits(&du) && dl.fits(&du) && dl.fits(&b.upper)) {
                    return None;
                }
                let all = b.rows.iter().chain(&rows).map(|&c| c.clone());
                out.push((x.clone(), all.collect()));
            }
            Some(out)
        };
        let mut removed = vec![false; p.ors.len()];
        let mut gone = Vec::new();
        for (j, ds) in p.ors.iter().enumerate() {
            if let Some(rows) = ds.iter().find_map(|d| serves(j, d)) {
                removed[j] = true;
                gone.extend(rows);
            }
        }
        (removed, gone)
    };
    let mut j = 0;
    p.ors.retain(|_| {
        j += 1;
        !removed[j - 1]
    });
    gone
}

/// Gives each atom that [`absorb`] projected away a value between its bounds at `m` over the
/// rows kept for it: its value in `m` when that lies between them, so that a point that already
/// holds is not moved, and otherwise the nearer bound. When `m` is a point of the parts left,
/// the bounds meet ([`absorb`]), and no row left or kept for another such atom reads this one,
/// so `m` becomes a point of the parts with each disjunction removed. The cost is that of
/// reading the rows once.
fn repair(m: &mut Model, gone: &[(Atom, Vec<Con>)]) {
    for (x, rows) in gone {
        let at = m.get(x).cloned().unwrap_or(Int::ZERO);
        let (mut lo, mut hi): (Option<Int>, Option<Int>) = (None, None);
        for c in rows {
            // `c` is `k·x + r >= 0`, `k` 1 or -1: `x >= -r` or `x <= r`.
            let k = &c.lin.terms[x];
            let r = &c.lin.eval_linear(m) - &(k * &at);
            if k.is_negative() {
                hi = Some(match hi {
                    Some(h) => h.min(r),
                    None => r,
                });
            } else {
                let r = -&r;
                lo = Some(match lo {
                    Some(l) => l.max(r),
                    None => r,
                });
            }
        }
        debug_assert!(lo.as_ref().zip(hi.as_ref()).is_none_or(|(l, h)| l <= h));
        let v = match (lo, hi) {
            (Some(l), _) if at < l => l,
            (_, Some(h)) if at > h => h,
            _ => continue,
        };
        m.insert(x.clone(), v);
    }
}

/// The parts' base and disjunctions once no disjunct can be removed, or `None` when they have
/// no point. A disjunct is removed when its top-level constraints meet the base nowhere; a
/// disjunction left with one disjunct adds it to the base. Each round but the last removes a
/// disjunct, so there are at most as many rounds as disjuncts, each a test of every disjunct.
///
/// A disjunct is kept when its constraints hold at a point of the base or when its own atoms
/// re-solved with the base's other atoms held at that point have a point ([`local_repair`]);
/// it is removed when its constraints with its atoms' bounds and the base's constraints over
/// its atoms alone have none ([`local_refute`]); only when all of these fail are the base
/// groups it touches solved with it. Each answer is exact. The base grows within a round as
/// disjunctions left with one disjunct join it, and on a nest those groups are one chain as
/// long as the nest: solving it for each disjunct cost the disjuncts times the chain (chain
/// family `cross_live` at `k = 256`: 1022 solves of 261 constraints in one call). The local
/// tests cost the constraints that link the disjunct's atoms to others and their bounds, so
/// the point is kept a point of the base as it grows, repaired the same way when a disjunct
/// that joins it does not hold there (COMPLEXITY S22, tests
/// `l01_25_preimage_catalog::s22::chain_cross_live_scales` and
/// `chain_cross_within_its_width_scales`).
///
/// With `search`, for a caller that only searches the parts for a point ([`decide`],
/// [`satisfiable`]), a disjunct that the local tests neither keep nor remove is kept untested
/// when another disjunct of its disjunction holds at the point: the search takes that one
/// while the point stands ([`pick`]), and when the point moves it tests each disjunct anyway,
/// so a disjunct kept so is at worst one the search tries and fails, after which [`probe`]
/// tests each disjunct without `search`. Without `search` (a projection, or a test of
/// emptiness in [`probe`]) every disjunct is answered, since a disjunct kept there widens a
/// hull or hides that the parts have no point.
///
/// Without `search`, or when no disjunct of a disjunction holds at the point, a disjunct that
/// the local tests do not answer is asked of the base projected onto the atoms of its
/// disjunction ([`by_halves`], [`shadow`]), with the disjuncts of a round taken by halves, so
/// that on a chain or a tree of `n` rows `n` such disjuncts cost O(n log n), not `n` solves of
/// the group (COMPLEXITY.md DECIDE-disj-chain, DISJ-incremental; tests in
/// `l01_38_presburger::disj_groups`). A disjunct the solver refuses with the projection is
/// solved with every base row linked to it, as before.
///
/// Complexity tradeoff: where [`shadow`] keeps a core of the group whole (a dense graph, a
/// grid: atoms with three or more lower and three or more upper bounds), each disjunct is
/// asked of that core, so `n` disjuncts over a core of `c` rows cost `n` solves of `c` rows,
/// up to quadratic as before. What is given up: no answer, only time on such groups. Why: an
/// exact projection of such a core grows it (Fourier-Motzkin), and testing each disjunct
/// against one solved core needs an incremental solver, which [`solve`] is not. Trigger: `n`
/// disjunctions over a group whose rows form such a core. A complete solution would settle
/// against one solved group, adding and retracting each disjunct.
fn settle(mut p: Parts, search: bool) -> Result<Option<Parts>, Refusal> {
    // The base, with a bound written again (at each level of a nest, say) kept once
    // ([`Linked::meet`]), so that the groups a disjunct is tested with do not grow with the
    // depth, and indexed for [`local_repair`].
    let mut base = Linked::default();
    let mut near = Near::default();
    take(&std::mem::take(&mut p.cons), &mut base, &mut near);
    loop {
        // A point of the base serves only to keep, unasked, the disjuncts that meet the base,
        // so none is built when no disjunction is left.
        let Some(model) = solve(&base.cons, !p.ors.is_empty())? else {
            return Ok(None);
        };
        if p.ors.is_empty() {
            p.cons = base.cons;
            return Ok(Some(p));
        }
        // A point of the base as it is now, or `None` once the solver refuses to find one, after
        // which each disjunct is solved with its groups.
        let mut point = Some(model);
        let mut changed = false;
        // The disjunctions to test, with those of a disjunct added to the base appended, so
        // that a chain of disjunctions each left with one disjunct is read in one round, not
        // one level of it per round; the disjunct's constraints join the base at once.
        let mut todo = std::mem::take(&mut p.ors);
        let mut next = 0;
        while next < todo.len() {
            let end = todo.len();
            // Whether a disjunct of these disjunctions may be asked of the solver: one that does
            // not hold at the point, in a disjunction that the point does not serve.
            let asks = !old_path()
                && point.as_ref().is_some_and(|pt| {
                    todo[next..end].iter().any(|ds| {
                        let holds = |d: &Rc<Parts>| d.cons.iter().all(|c| c.holds_linear(pt));
                        !(search && ds.iter().any(holds)) && !ds.iter().all(holds)
                    })
                });
            // The atoms of each disjunction's own constraints, onto which [`by_halves`]
            // projects the base for its questions.
            let keep: Vec<BTreeSet<Atom>> = if asks {
                (todo[next..end].iter())
                    .map(|ds| {
                        (ds.iter())
                            .flat_map(|d| d.cons.iter().flat_map(|c| c.lin.terms.keys().cloned()))
                            .collect()
                    })
                    .collect()
            } else {
                Vec::new()
            };
            let rows: Vec<Con> = (base.around_atoms(keep.iter().flatten()).into_iter())
                .cloned()
                .collect();
            // Tests the disjunction at `i`, given the base projected onto its atoms (`None`:
            // not known), and returns the constraints it adds to the base.
            let mut one = |i: usize, kernel: Option<Vec<Con>>| -> Result<Vec<Con>, ()> {
                let ds = std::mem::take(&mut todo[i]);
                let n = ds.len();
                // With `search`, whether a disjunct of this disjunction holds at the point.
                let served = search
                    && (point.as_ref()).is_some_and(|pt| {
                        ds.iter().any(|d| d.cons.iter().all(|c| c.holds_linear(pt)))
                    });
                // The projection is of a base with a point; one is known while `point` is.
                let kernel = kernel.filter(|_| point.is_some()).map(Linked::of);
                let mut live: Vec<Rc<Parts>> = ds
                    .into_iter()
                    .filter(|d| {
                        // The question below is of the disjunct's own constraints, so the point
                        // answers it when they hold there, whatever holds below them; reading
                        // only them keeps a nest from being read once for each level above it.
                        // The repairs only keep a disjunct, which `served` keeps anyway unless
                        // a refutation below removes it, and a disjunct a repair keeps has a
                        // point with the base, which no refutation then shows empty: so with
                        // `served` they decide nothing and are not run (item
                        // PRES-each-settle-share).
                        if let Some(pt) = &point
                            && (d.cons.iter().all(|c| c.holds_linear(pt))
                                || (!served && own_repair(&near, pt, &d.cons).is_some()))
                        {
                            return true;
                        }
                        // A bound of the disjunct that the base's bounds leave no value, and only
                        // then the repair and the refutation that read the constraints linking
                        // its atoms to others, each exact, so the order changes no answer.
                        if near.refutes(&d.cons) {
                            return false;
                        }
                        if !served
                            && let Some(pt) = &point
                            && local_repair(&base.cons, &near, pt, &d.cons).is_some()
                        {
                            return true;
                        }
                        if local_refute(&base.cons, &near, &d.cons) {
                            return false;
                        }
                        if served {
                            return true;
                        }
                        // Asked of the base projected onto the disjunction's atoms, which has a
                        // point with the disjunct exactly when the base has one; when the
                        // solver refuses that, of the base's groups, as before.
                        if let Some(k) = &kernel {
                            let mut cs = k.around(&d.cons);
                            cs.extend(d.cons.iter());
                            match solve(&cs, false) {
                                Ok(None) => return false,
                                Ok(Some(_)) => return true,
                                Err(_) => {}
                            }
                        }
                        let mut cs = base.around(&d.cons);
                        cs.extend(d.cons.iter());
                        !matches!(solve(&cs, false), Ok(None))
                    })
                    .collect();
                changed |= live.len() < n;
                match live.len() {
                    0 => Err(()),
                    1 => {
                        let d = live.pop().expect("one");
                        // The disjunct joins the base, so a disjunction tested before it in
                        // this round is tested again with its rows: without that round the
                        // result would depend on whether the disjunction came before or after
                        // the ones its rows narrow, that is on the order of the parts (item
                        // PROJECT-canon-precision).
                        changed = true;
                        let repaired = match &point {
                            Some(pt) if d.cons.iter().all(|c| c.holds_linear(pt)) => None,
                            Some(pt) => Some(
                                own_repair(&near, pt, &d.cons)
                                    .or_else(|| local_repair(&base.cons, &near, pt, &d.cons)),
                            ),
                            None => None,
                        };
                        take(&d.cons, &mut base, &mut near);
                        match (repaired, &mut point) {
                            (Some(Some(m)), Some(pt)) => pt.extend(m),
                            // No point of the base near the old one: one of the whole base, or
                            // none, in which case the formula has none either.
                            (Some(None), _) => match solve(&base.cons, true) {
                                Ok(Some(m)) => point = Some(m),
                                Ok(None) => return Err(()),
                                Err(_) => point = None,
                            },
                            _ => {}
                        }
                        todo.extend(d.ors.iter().cloned());
                        Ok(d.cons.clone())
                    }
                    _ => {
                        p.ors.push(live);
                        Ok(Vec::new())
                    }
                }
            };
            let done = if asks {
                by_halves(rows, &keep, |i, k| one(next + i, k))
            } else {
                (next..end).try_for_each(|i| one(i, None).map(drop))
            };
            if done.is_err() {
                return Ok(None);
            }
            next = end;
        }
        if !changed {
            p.cons = base.cons;
            return Ok(Some(p));
        }
    }
}

/// Whether a conjunction of constraints holds somewhere, and, when `want`, where; without
/// `want` a point is answered by an empty model, and none is built.
///
/// No step of the solver chooses by the names of the variables or by the order of the rows:
/// each choice goes by what the structure of the rows gives (the colors of [`canonical`], the
/// fill of an elimination, the coefficients), and where that leaves two candidates that share
/// a row, the solver refuses with [`Refusal::Tie`] instead of choosing; candidates that share
/// no row are taken together, which no order can change. So the answer, refusals included, is
/// the same under every naming of the variables and every order of the constraints.
fn solve<C: std::borrow::Borrow<Con>>(cons: &[C], want: bool) -> Result<Option<Model>, Refusal> {
    let cons: Vec<&Con> = cons.iter().map(|c| c.borrow()).collect();
    let atoms: Vec<Atom> = cons
        .iter()
        .flat_map(|c| c.lin.terms.keys().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let Canonical {
        atoms,
        rows,
        keys,
        row_keys,
    } = canonical(atoms, &cons);
    let index: BTreeMap<&Atom, usize> = atoms.iter().enumerate().map(|(i, a)| (a, i)).collect();
    // In the order of `canonical`, so that neither the order of the constraints nor the names of
    // the variables decide the order of the work, except among variables that refinement cannot
    // tell apart, where no choice is made by that order.
    let sorted: Vec<&Con> = rows.into_iter().map(|r| cons[r]).collect();
    // Each equality `x - y == d` ties `x` to `y`: every row is written over one variable of
    // each tied class, the others being offsets from it, so no row is rewritten for them.
    let mut ties = Ties::new(atoms.len());
    for c in &sorted {
        if c.rel != Rel::Eq || c.lin.terms.len() != 2 {
            continue;
        }
        let mut terms = c.lin.terms.iter();
        let (x, a) = terms.next().expect("two terms");
        let (y, b) = terms.next().expect("two terms");
        if !a.is_unit() || *b != -a {
            continue;
        }
        // `a·x - a·y + k == 0`, so `x - y == -k·a`.
        if !ties.equate(index[x], index[y], -&(&c.lin.constant * a)) {
            return Ok(None);
        }
    }
    let at = ties.representatives(&keys);
    let mut base: Vec<(Row, Rel)> = Vec::with_capacity(sorted.len());
    for c in sorted {
        let mut sum: BTreeMap<usize, Int> = BTreeMap::new();
        let mut k = c.lin.constant.clone();
        for (a, coef) in &c.lin.terms {
            let (r, d) = &at[index[a]];
            k = &k + &(coef * d);
            let at = sum.entry(*r).or_insert(Int::ZERO);
            *at = &*at + coef;
        }
        let a = sum.into_iter().filter(|(_, c)| !c.is_zero()).collect();
        base.push((Row { a, k }, c.rel));
    }
    let name = |i: usize| atoms[i].to_string();
    let Some(vals) = quotient(atoms.len(), base, &keys, &row_keys, want, &name)? else {
        return Ok(None);
    };
    if !want {
        return Ok(Some(Model::new()));
    }
    let mut model: Model = atoms.iter().cloned().zip(vals).collect();
    for (i, a) in atoms.iter().enumerate() {
        let (r, d) = &at[i];
        if *r != i {
            let v = &model[&atoms[*r]] + d;
            model.insert(a.clone(), v);
        }
    }
    Ok(Some(model))
}

/// A choice among candidates that share a row and that nothing but their names or places
/// tells apart, as variables by place and rows: the cause of a [`Refusal::Tie`] before its
/// variables are named.
struct Tied {
    vars: Vec<usize>,
    rows: Vec<(Row, Rel)>,
}

impl Tied {
    /// The refusal, with the variables by place below `vars` named by `name` and those made
    /// up after them `t1`, `t2` and so on.
    fn written(&self, vars: usize, name: &dyn Fn(usize) -> String) -> Refusal {
        let label = |j: usize| {
            if j < vars {
                name(j)
            } else {
                format!("t{}", j - vars + 1)
            }
        };
        Refusal::Tie(Arc::new(Tie {
            vars: self.vars.iter().map(|&j| label(j)).collect(),
            rows: self
                .rows
                .iter()
                .map(|(r, rel)| {
                    let rel = if *rel == Rel::Eq { "==" } else { ">=" };
                    format!(
                        "{} {rel} 0",
                        sum_of(r.a.iter().map(|(j, c)| (label(*j), c)), &r.k)
                    )
                })
                .collect(),
        }))
    }
}

/// `Σ c·x + k`, written as [`Lin`] writes a term.
fn sum_of<'a>(terms: impl Iterator<Item = (String, &'a Int)>, k: &Int) -> String {
    let mut out = String::new();
    for (x, c) in terms {
        let m = c.abs();
        match (out.is_empty(), c.is_negative()) {
            (true, true) => out.push('-'),
            (true, false) => {}
            (false, true) => out.push_str(" - "),
            (false, false) => out.push_str(" + "),
        }
        if m == Int::ONE {
            out.push_str(&x);
        } else {
            out.push_str(&format!("{m} * {x}"));
        }
    }
    if out.is_empty() {
        out = k.to_string();
    } else if k.is_positive() {
        out.push_str(&format!(" + {k}"));
    } else if k.is_negative() {
        out.push_str(&format!(" - {}", k.abs()));
    }
    out
}

/// Variables whose columns are multiples of one column, merged into one variable: the
/// greatest common divisor of their multiples, and for each, by place, the Bézout factors
/// `(j, s, t)` of the step that took it in, `s` on the divisor before and `t` on its own
/// multiple.
struct Merged {
    gcd: Int,
    links: Vec<(usize, Int, Int)>,
}

/// `(g, s, t)` with `g` the greatest common divisor of `a` and `b` and `s·a + t·b == g`, for
/// `a` not below zero, by the extended Euclidean algorithm.
fn bezout(a: &Int, b: &Int) -> (Int, Int, Int) {
    let (mut r, mut next) = (a.clone(), b.abs());
    let (mut s, mut ns) = (Int::ONE, Int::ZERO);
    let (mut t, mut nt) = (Int::ZERO, Int::ONE);
    while !next.is_zero() {
        let q = r.div_floor(&next);
        let rem = &r - &(&q * &next);
        r = std::mem::replace(&mut next, rem);
        let ns2 = &s - &(&q * &ns);
        s = std::mem::replace(&mut ns, ns2);
        let nt2 = &t - &(&q * &nt);
        t = std::mem::replace(&mut nt, nt2);
    }
    if b.is_negative() {
        t = -&t;
    }
    (r, s, t)
}

/// [`parts`] on `base` with the variables whose columns are multiples of one primitive column
/// merged. Where `x[j]` and `x[l]` enter every row as `c·p` and `d·p`, the rows see only
/// `c·x[j] + d·x[l]`, whose values over the integers are the multiples of `gcd(c, d)`; so
/// one variable `y` with column `gcd(c, d)·p` has a point exactly when they have one, and a
/// point of `y` lifts by the Bézout factors `s·c + t·d == gcd(c, d)` to `x[j] = s·y`,
/// `x[l] = t·y`. The substitution is unimodular on each group, so no integer point is lost or
/// added. A primitive column has coprime entries and its first entry above zero; columns are
/// grouped by sorting them, O(T log T) comparisons for T terms, and the factors grow by
/// O(log² C) bits for coefficients of C. With no two columns grouped, `base` goes on as it is.
///
/// The first entry of a column is first in the order of the rows, which names can decide, so
/// the sign of `y`, which the later steps can see, is set otherwise: `p` is turned so that the
/// members of least color (`keys`) enter with multiples above zero; where those members enter
/// with both signs, so that the sorted pairs of row color (`row_keys`) and entry are the
/// lesser of `p` and `-p`; and where `p` and `-p` give the same pairs, the group is not
/// merged. `y` takes the least color of its members.
fn quotient(
    vars: usize,
    base: Vec<(Row, Rel)>,
    keys: &[usize],
    row_keys: &[usize],
    want: bool,
    name: &dyn Fn(usize) -> String,
) -> Result<Option<Vec<Int>>, Refusal> {
    // Each column, as its signed content and its primitive part, by row.
    let mut cols: Vec<Vec<(usize, &Int)>> = vec![Vec::new(); vars];
    for (i, (r, _)) in base.iter().enumerate() {
        for (j, c) in r.a.iter() {
            cols[*j].push((i, c));
        }
    }
    let split: Vec<Option<(Int, Vec<Term>)>> = cols
        .iter()
        .map(|col| {
            let &(_, first) = col.first()?;
            let g = col.iter().fold(Int::ZERO, |g, (_, c)| g.gcd(c));
            let prim = col
                .iter()
                .map(|(i, c)| {
                    let q = c.div_floor(&g);
                    (*i, if first.is_negative() { -&q } else { q })
                })
                .collect();
            Some((if first.is_negative() { -&g } else { g }, prim))
        })
        .collect();
    drop(cols);
    // The groups in the order of their first variable, each with that variable.
    let mut group: BTreeMap<&[Term], usize> = BTreeMap::new();
    let mut groups: Vec<(usize, Merged)> = Vec::new();
    for (j, (content, prim)) in split
        .iter()
        .enumerate()
        .filter_map(|(j, s)| Some((j, s.as_ref()?)))
    {
        let id = *group.entry(prim).or_insert_with(|| {
            groups.push((
                j,
                Merged {
                    gcd: Int::ZERO,
                    links: Vec::new(),
                },
            ));
            groups.len() - 1
        });
        let m = &mut groups[id].1;
        let (g, s, t) = bezout(&m.gcd, content);
        m.gcd = g;
        m.links.push((j, s, t));
    }
    if groups.iter().all(|(_, m)| m.links.len() == 1) {
        return parts(vars, base, keys, want, name);
    }
    // The sign of each group's variable (true where it is `-p`), and its color. A group whose
    // sign nothing but names would choose is not merged: each member stays a variable of its
    // own, with its own column and color, which keeps the points as they are; whether a group
    // is merged depends on its columns and colors only, so no naming changes it.
    let content = |j: usize| &split[j].as_ref().expect("a column").0;
    let mut turned: Vec<(bool, usize)> = Vec::with_capacity(groups.len());
    let mut kept: Vec<(usize, Merged)> = Vec::with_capacity(groups.len());
    for (first, m) in groups {
        let (_, prim) = split[first].as_ref().expect("a group's first column");
        let least = m
            .links
            .iter()
            .map(|(j, _, _)| keys[*j])
            .min()
            .expect("a group has a member");
        let signs: BTreeSet<bool> = m
            .links
            .iter()
            .filter(|(j, _, _)| keys[*j] == least)
            .map(|(j, _, _)| content(*j).is_negative())
            .collect();
        let flip = match signs.len() {
            1 => Some(signs.contains(&true)),
            _ => {
                let pairs = |sign: &Int| {
                    let mut v: Vec<(usize, Int)> =
                        prim.iter().map(|(i, p)| (row_keys[*i], p * sign)).collect();
                    v.sort();
                    v
                };
                match pairs(&Int::ONE).cmp(&pairs(&-&Int::ONE)) {
                    Ordering::Less => Some(false),
                    Ordering::Greater => Some(true),
                    Ordering::Equal => None,
                }
            }
        };
        match flip {
            Some(flip) => {
                turned.push((flip, least));
                kept.push((first, m));
            }
            None => {
                for (j, _, _) in m.links {
                    turned.push((false, keys[j]));
                    let gcd = content(j).clone();
                    let links = vec![(j, Int::ZERO, Int::ONE)];
                    kept.push((j, Merged { gcd, links }));
                }
            }
        }
    }
    let groups = kept;
    let mut rows: Vec<Vec<Term>> = vec![Vec::new(); base.len()];
    for (id, (first, m)) in groups.iter().enumerate() {
        let (_, prim) = split[*first].as_ref().expect("a group's first column");
        let g = if turned[id].0 { -&m.gcd } else { m.gcd.clone() };
        for (i, p) in prim {
            rows[*i].push((id, p * &g));
        }
    }
    let reduced = base
        .into_iter()
        .zip(rows)
        .map(|((r, rel), a)| {
            (
                Row {
                    a: a.into(),
                    k: r.k,
                },
                rel,
            )
        })
        .collect();
    let group_keys: Vec<usize> = turned.iter().map(|t| t.1).collect();
    // A group's variable is the sum of its members, each times its multiple over the divisor.
    let group_name = |id: usize| {
        let (m, flip) = (&groups[id].1, turned[id].0);
        let terms: Vec<(String, Int)> = m
            .links
            .iter()
            .map(|(j, _, _)| {
                let c = content(*j).div_floor(&m.gcd);
                (name(*j), if flip { -&c } else { c })
            })
            .collect();
        sum_of(terms.iter().map(|(x, c)| (x.clone(), c)), &Int::ZERO)
    };
    let Some(y) = parts(groups.len(), reduced, &group_keys, want, &group_name)? else {
        return Ok(None);
    };
    if !want {
        return Ok(Some(Vec::new()));
    }
    let mut x = vec![Int::ZERO; vars];
    for (((_, m), value), (flip, _)) in groups.iter().zip(y).zip(&turned) {
        let mut carry = if *flip { -&value } else { value };
        for (j, s, t) in m.links.iter().rev() {
            x[*j] = t * &carry;
            carry = s * &carry;
        }
    }
    Ok(Some(x))
}

/// A part of a system: its variables, and its rows.
type Part = (Vec<usize>, Vec<(Row, Rel)>);

/// [`search`] on each part of `base` that shares no variable with the others: the rows hold
/// at a point exactly when each part's rows do at its own variables. So the answer is empty
/// when one part is empty, whatever the others give; otherwise the least of the parts'
/// refusals; otherwise the parts' points together, a variable in no row taking 0. A part of
/// two variables is decided exactly, however many such parts there are. Each part's
/// variables keep their colors, `keys`.
fn parts(
    vars: usize,
    base: Vec<(Row, Rel)>,
    keys: &[usize],
    want: bool,
    name: &dyn Fn(usize) -> String,
) -> Result<Option<Vec<Int>>, Refusal> {
    // The parts, by union-find over the variables each row mentions.
    let mut parent: Vec<usize> = (0..vars).collect();
    fn find(parent: &mut [usize], mut i: usize) -> usize {
        while parent[i] != i {
            parent[i] = parent[parent[i]];
            i = parent[i];
        }
        i
    }
    for (r, _) in &base {
        if let Some(&(first, _)) = r.a.first() {
            let a = find(&mut parent, first);
            for &(j, _) in &r.a[1..] {
                let b = find(&mut parent, j);
                parent[b] = a;
            }
        }
    }
    // Each part's rows, in the order of `base`, and its variables renumbered from 0 in
    // increasing order; the parts in the order of their least variable.
    let mut of_root: BTreeMap<usize, Part> = BTreeMap::new();
    for v in 0..vars {
        let root = find(&mut parent, v);
        of_root.entry(root).or_default().0.push(v);
    }
    for (r, rel) in base {
        let Some(&(first, _)) = r.a.first() else {
            // A row with no variable holds or fails alone.
            let holds = match rel {
                Rel::Ge => !r.k.is_negative(),
                Rel::Eq => r.k.is_zero(),
            };
            if !holds {
                return Ok(None);
            }
            continue;
        };
        let root = find(&mut parent, first);
        of_root
            .get_mut(&root)
            .expect("a part per root")
            .1
            .push((r, rel));
    }
    let mut vals = vec![Int::ZERO; vars];
    let mut refused: Option<Refusal> = None;
    let mut points = Vec::new();
    for (vs, rows) in of_root.into_values() {
        if rows.is_empty() {
            continue;
        }
        let local: BTreeMap<usize, usize> = vs.iter().enumerate().map(|(i, &v)| (v, i)).collect();
        let rows: Vec<(Row, Rel)> = rows
            .into_iter()
            .map(|(r, rel)| {
                // The renumbering keeps the order, so the row stays sorted.
                let a = r.a.iter().map(|(j, c)| (local[j], c.clone())).collect();
                (Row { a, k: r.k }, rel)
            })
            .collect();
        let part_keys: Vec<usize> = vs.iter().map(|&v| keys[v]).collect();
        let part_name = |i: usize| name(vs[i]);
        match search(vs.len(), &rows, &part_keys, want, &part_name) {
            Ok(None) => return Ok(None),
            Ok(Some(p)) => points.push((vs, p)),
            Err(r) => refused = Some(least(refused, r)),
        }
    }
    if let Some(r) = refused {
        return Err(r);
    }
    for (vs, p) in points {
        for (v, x) in vs.into_iter().zip(p) {
            vals[v] = x;
        }
    }
    Ok(Some(vals))
}

/// The lesser of a refusal and the one held, if any.
fn least(held: Option<Refusal>, r: Refusal) -> Refusal {
    match held {
        Some(q) if q <= r => q,
        _ => r,
    }
}

/// The Omega test on `base` over `vars` variables of colors `keys`, with the splinters of its
/// dark eliminations: by Pugh's lemma [Omega, sec. 2.3] the problem has an integer point
/// exactly when its dark shadow has one or one of the splinters of a dark elimination has one.
/// The splinters are searched only when the dark shadows have no point. Pugh's lemma holds for
/// either side of an elimination (for the upper bounds, it is the lemma for `-x`), so the
/// splinters taken are those of the side with fewer bounds, and of both sides when they have as
/// many, since which side is the lower one can turn on the sign `quotient` gave a merged
/// variable. A splinter whose own dark shadows have no point is split in turn
/// ([`splinters`]) when each of its dark eliminations leaves fewer variables than the one it
/// came from; otherwise it is refused with [`Refusal::Shadows`]. The splinters are searched a
/// batch of dark eliminations at a time, in the order of the batches, and every splinter of a
/// batch is searched, so the answer does not depend on the order of the variables within a
/// batch: a point of a splinter is the answer; otherwise the first batch with a dark
/// elimination none of whose sides has only empty splinters gives the least refusal met in
/// that batch; otherwise the problem is empty. A refused dark shadow is the answer likewise:
/// the splinters hold only the points it misses, so they could turn the refusal into a point
/// but never into an empty answer.
fn search(
    vars: usize,
    base: &[(Row, Rel)],
    keys: &[usize],
    want: bool,
    name: &dyn Fn(usize) -> String,
) -> Result<Option<Vec<Int>>, Refusal> {
    let mut top = Omega::new(keys, base, want);
    match top.run() {
        Leaf::Point(v) => return Ok(Some(v)),
        Leaf::Empty => {}
        Leaf::Refused(r) => return Err(r),
        Leaf::Tied(t) => return Err(t.written(vars, name)),
    }
    splinters(&top, base, vars, name)
}

/// The splinters of the dark eliminations of `top`, a run of the Omega test on `base` that
/// ended empty, searched as [`search`] describes. A splinter holds the rows of `base` with one
/// bound of the eliminated variable fixed within its gap by a fresh variable; when its own run
/// ends empty after dark shadows, those are split in turn, so a point that lies in a splinter
/// of a splinter is found.
///
/// Complexity tradeoff: a splinter whose dark eliminations are not all at fewer live variables
/// than the one it came from is not split again; the question gets `Refusal::Shadows` ("not
/// decided") even when a point lies there. Why: a splinter with a gap of more than one value
/// adds the fresh variable for the one it eliminates, so splitting it again keeps the count of
/// variables and need not end (on the example in `omega.rs` it ran 41 levels deep, the rows
/// growing from 8 to 992); with fewer live variables at each level the depth is at most the
/// live variables less three, where `live3` decides the rest. Within that depth the search
/// is a tree: each level multiplies the runs by the bounds of one side, so the cost is
/// exponential in the depth of the nesting, as in Pugh's Omega test (integer feasibility is
/// NP-complete). No child system repeats within one search (0 of 10806 measured over chained
/// rows with coefficient 2 on one side, the form that nests), so no visited set is kept.
/// Trigger for the refusal: a dark elimination inside a splinter at as many live variables as
/// the one it splits, which needs a gap of more than one value (a bound coefficient other than
/// ±1 or 2). Tests: `l01_38_presburger::omega::each_cause_of_a_refusal_has_its_own_message`,
/// `l01_38_presburger::checker::a_question_whose_point_lies_past_one_splinter_is_rejected`,
/// `l01_38_presburger::scaling::pughs_example_in_a_chain_scales`,
/// `l01_38_presburger::scaling::splinters_of_splinters_scale`. COMPLEXITY.md row S18. A
/// complete solution would enumerate the gap of each such splinter by value, as Pugh's Omega
/// test does, at a cost exponential in the coefficients as well as the depth.
///
/// Complexity tradeoff: the search ends at the first batch of dark eliminations with a refusal,
/// and the splinters of later batches, which could hold a point, are not searched; the
/// question gets the refusal. Why: searching every splinter costs a run of the Omega test for
/// each, which along a chain of dark eliminations is quadratic in the variables; ending at the
/// first refusal keeps it linear when that refusal comes early. The batches are given by the
/// structure, and so is their order, so ending after a whole batch keeps the answer the same
/// under every naming, which ending inside one would not. Trigger: a dark elimination whose
/// splinters are refused, before one whose splinters hold a point. Tests:
/// `l01_38_presburger::scaling::pughs_example_in_a_chain_scales`,
/// `l01_38_presburger::names::the_splinters_are_searched_a_batch_at_a_time`. COMPLEXITY.md row
/// NAME-ties.
fn splinters(
    top: &Omega,
    base: &[(Row, Rel)],
    vars: usize,
    name: &dyn Fn(usize) -> String,
) -> Result<Option<Vec<Int>>, Refusal> {
    for (live, batch) in &top.gray {
        let mut refused: Option<Refusal> = None;
        for &(at, n) in batch {
            let Step::Chosen(j, rows) = &top.steps[at] else {
                unreachable!("a dark elimination is a chosen step")
            };
            let (lowers, uppers): (Vec<&Row>, Vec<&Row>) =
                rows.iter().partition(|r| r.at(*j).is_positive());
            // The splinters of the side with fewer rows, each bound measured against the
            // largest coefficient of the other side; both sides when they have as many rows.
            let sides: Vec<(&[&Row], &[&Row])> = match uppers.len().cmp(&lowers.len()) {
                Ordering::Less => vec![(&uppers, &lowers)],
                Ordering::Greater => vec![(&lowers, &uppers)],
                Ordering::Equal => vec![(&lowers, &uppers), (&uppers, &lowers)],
            };
            let mut covered = false;
            let mut why: Option<Refusal> = None;
            for (side, other) in sides {
                let m = other
                    .iter()
                    .map(|r| r.at(*j).abs())
                    .max()
                    .expect("an inexact elimination has both bounds");
                let mut open: Option<Refusal> = None;
                for bound in side {
                    let Some((rows, keys)) = top.splinter(base, at, n, bound, *j, &m) else {
                        continue;
                    };
                    let mut child = Omega::new(&keys, &rows, top.want);
                    let mut leaf = child.run();
                    if matches!(leaf, Leaf::Empty) && !child.gray.is_empty() {
                        // Run again with each gray shadow over three variables decided by
                        // `live3`, which leaves gray shadows only where four variables or more
                        // are left.
                        child = Omega::new(&keys, &rows, top.want);
                        child.exact3 = true;
                        leaf = child.run();
                    }
                    let split = match leaf {
                        Leaf::Point(v) => return Ok(Some(v)),
                        Leaf::Empty if child.gray.is_empty() => continue,
                        Leaf::Empty if child.gray.iter().all(|(l, _)| l < live) => {
                            splinters(&child, &rows, vars, name)
                        }
                        Leaf::Empty => Err(Refusal::Shadows),
                        Leaf::Refused(r) => Err(r),
                        Leaf::Tied(t) => Err(t.written(vars, name)),
                    };
                    match split {
                        Ok(Some(v)) => return Ok(Some(v)),
                        Ok(None) => {}
                        Err(r) => open = Some(least(open, r)),
                    }
                }
                match open {
                    None => covered = true,
                    Some(r) => why = Some(least(why, r)),
                }
            }
            if !covered && let Some(r) = why {
                refused = Some(least(refused, r));
            }
        }
        if let Some(r) = refused {
            return Err(r);
        }
    }
    Ok(None)
}

/// The equalities `x - y == d` as a forest with union by rank, so that each root is found in
/// a number of steps logarithmic in the variables: each variable is its parent plus its offset.
struct Ties {
    parent: Vec<usize>,
    rank: Vec<usize>,
    offset: Vec<Int>,
}

impl Ties {
    fn new(n: usize) -> Ties {
        Ties {
            parent: (0..n).collect(),
            rank: vec![0; n],
            offset: vec![Int::ZERO; n],
        }
    }

    /// The root of `x[i]` and `d` with `x[i] == root + d`.
    fn root(&self, mut i: usize) -> (usize, Int) {
        let mut d = Int::ZERO;
        while self.parent[i] != i {
            d = &d + &self.offset[i];
            i = self.parent[i];
        }
        (i, d)
    }

    /// Adds `x[x] - x[y] == d`; false when the ties already make it something else. Which of
    /// two roots of equal rank goes under the other follows the order of the arguments, so it
    /// is not used beyond this forest: [`Ties::representatives`] chooses the variable that
    /// stands for each class.
    fn equate(&mut self, x: usize, y: usize, d: Int) -> bool {
        let (x, dx) = self.root(x);
        let (y, dy) = self.root(y);
        // `x - y == d - dx + dy` between the roots.
        let delta = &(&d - &dx) + &dy;
        if x == y {
            return delta.is_zero();
        }
        if self.rank[x] < self.rank[y] {
            self.parent[x] = y;
            self.offset[x] = delta;
        } else {
            self.parent[y] = x;
            self.offset[y] = -&delta;
            if self.rank[x] == self.rank[y] {
                self.rank[x] += 1;
            }
        }
        true
    }

    /// For each variable, the member of its class that stands for the class, and `d` with the
    /// variable equal to that member plus `d`: the member of least color (`keys`), then of least
    /// offset, then of least place. Colors, and the differences between the offsets of a
    /// class, depend on the rows alone, not on the order in which [`Ties::equate`] joined the
    /// class: that order, and the order of the arguments of each `equate`, choose only which
    /// member is the root, and moving the root from `r` to `s` subtracts the one constant
    /// `x[s] - x[r]` from the offset of every member of the class, which keeps both the order
    /// of the candidates `(color, offset, place)` and each difference `d - e` below. Two
    /// members of one color and one offset are equal at every point and alike in the rows, so
    /// taking one or the other only renames the variable that stands for the class. Test
    /// `tests::the_representatives_of_joined_equalities_do_not_depend_on_their_order`.
    /// O(n log n) for n variables.
    fn representatives(&self, keys: &[usize]) -> Vec<(usize, Int)> {
        let roots: Vec<(usize, Int)> = (0..self.parent.len()).map(|i| self.root(i)).collect();
        let mut best: Vec<Option<(usize, &Int, usize)>> = vec![None; roots.len()];
        for (i, (r, d)) in roots.iter().enumerate() {
            let candidate = (keys[i], d, i);
            if best[*r].is_none_or(|b| candidate < b) {
                best[*r] = Some(candidate);
            }
        }
        roots
            .iter()
            .map(|(r, d)| {
                let (_, e, rep) = best[*r].expect("each root has a member");
                (rep, d - e)
            })
            .collect()
    }
}

/// `atoms`, in name order, put in the order the solver takes them; the places in `cons` of the
/// rows in the order it takes them; and the color of each atom of that order in the coarsest
/// stable coloring of the system ([`stable_colors`]). Both orders are breadth first over the
/// rows, so that variables that share a row stand near each other, and so do rows that share a
/// variable:
/// from the variable of least color not yet placed, each placed variable's rows not yet taken
/// are taken in the order of their colors, and each row's variables not yet placed in the
/// order of theirs. Rows with no variable come last, by color. Names, and the order of
/// `cons`, break ties between equal colors only; when every variable's color is distinct, two
/// rows of one color are equal, so the orders depend on the structure alone. O(n + m + t log t)
/// for n variables, m rows and t terms, with the sorts of each row's terms and each variable's
/// rows. The colors of the rows, in the order taken, come with them.
fn canonical(atoms: Vec<Atom>, cons: &[&Con]) -> Canonical {
    let n = atoms.len();
    let color = stable_colors(&atoms, cons);
    let by_color = |v: &usize| (color[*v], *v);
    let mut rows_of: Vec<Vec<usize>> = vec![Vec::new(); n];
    let vars_of: Vec<Vec<usize>> = cons
        .iter()
        .enumerate()
        .map(|(r, c)| {
            let mut xs: Vec<usize> = c
                .lin
                .terms
                .keys()
                .map(|a| atoms.binary_search(a).expect("an atom of the system"))
                .collect();
            for &x in &xs {
                rows_of[x].push(n + r);
            }
            xs.sort_by_key(by_color);
            xs
        })
        .collect();
    for rs in &mut rows_of {
        rs.sort_by_key(by_color);
    }
    let mut seeds: Vec<usize> = (0..n).collect();
    seeds.sort_by_key(by_color);
    let mut placed = vec![false; n];
    let mut taken = vec![false; cons.len()];
    let mut order: Vec<usize> = Vec::with_capacity(n);
    let mut rows: Vec<usize> = Vec::with_capacity(cons.len());
    for s in seeds {
        if placed[s] {
            continue;
        }
        placed[s] = true;
        order.push(s);
        let mut head = order.len() - 1;
        while head < order.len() {
            for &r in &rows_of[order[head]] {
                if taken[r - n] {
                    continue;
                }
                taken[r - n] = true;
                rows.push(r - n);
                for &x in &vars_of[r - n] {
                    if !placed[x] {
                        placed[x] = true;
                        order.push(x);
                    }
                }
            }
            head += 1;
        }
    }
    let mut bare: Vec<usize> = (0..cons.len()).filter(|&r| !taken[r]).collect();
    bare.sort_by_key(|&r| (color[n + r], r));
    rows.extend(bare);
    let keys = order.iter().map(|&x| color[x]).collect();
    let row_keys = rows.iter().map(|&r| color[n + r]).collect();
    let mut atoms: Vec<Option<Atom>> = atoms.into_iter().map(Some).collect();
    let order = order
        .into_iter()
        .map(|x| atoms[x].take().expect("each variable placed once"))
        .collect();
    Canonical {
        atoms: order,
        rows,
        keys,
        row_keys,
    }
}

/// What [`canonical`] gives: the atoms in the order taken, the places of the rows in the order
/// taken, and the color of each atom and of each row in those orders.
struct Canonical {
    atoms: Vec<Atom>,
    rows: Vec<usize>,
    keys: Vec<usize>,
    row_keys: Vec<usize>,
}

/// The variables of the conjunction `cons` in the order the solver takes them, and their
/// colors, by which it orders them: two variables have one color exactly when the structure
/// of the rows does not tell them apart, and the numbers depend on that structure only, not on
/// the names.
pub fn colors(cons: &[Con]) -> (Vec<Atom>, BTreeMap<Atom, u64>) {
    let cons: Vec<&Con> = cons.iter().collect();
    let atoms: Vec<Atom> = cons
        .iter()
        .flat_map(|c| c.lin.terms.keys().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let Canonical {
        atoms: order,
        keys: colors,
        ..
    } = canonical(atoms, &cons);
    let colors = order
        .iter()
        .zip(colors)
        .map(|(a, k)| (a.clone(), k as u64))
        .collect();
    (order, colors)
}

/// The color of each of `atoms` (sorted, each in some row of `cons`), then of each row of
/// `cons`, in the coarsest stable coloring of the system's graph. The graph has a vertex for
/// each variable, each row and each term of a row, a term joined to its row and to its
/// variable. A row starts colored by its relation and constant, a term by its coefficient, and
/// every variable alike. A coloring is
/// stable when any two vertices of one color have, for every color, as many neighbors of that
/// color. So two variables keep one color exactly when no number of rounds of comparing the
/// multisets of (row color, coefficient) of their rows tells them apart: refinement runs until
/// the partition is stable, with no count of rounds.
///
/// The method is the canonical color refinement of Berkholz, Bonsma and Grohe, "Tight lower and
/// upper bounds for the complexity of canonical colour refinement" (Theory Comput. Syst. 60,
/// 2017; arXiv:1509.08251), section 3, with edge colors by the subdivision of their
/// edge-colored theorem, which is the term vertex here. A popped color class R refines every
/// class by the number of neighbors in R each of its vertices has. After a split, the largest
/// new class is not pushed unless the old one was waiting (Hopcroft's rule, "process the smaller
/// half"), so a vertex is in O(log N) refining classes in all. The coarsest stable coloring is
/// Cardon and Crochemore's "coarsest regular congruence", an equivalence in which any two equal
/// vertices have the same number of successors by each type of arc in each class ("Partitioning
/// a graph in O(|A| log2 |V|)", Theoret. Comput. Sci. 19, 1982, 85-98), and Paige and Tarjan's
/// coarsest size-stable refinement, which they compute by queueing every new block but the
/// largest, in O(m log n) time because a vertex lies in at most log2 n + 1 of the blocks taken
/// from the queue ("Three partition refinement algorithms", SIAM J. Comput. 16(6), 1987,
/// 973-989, end of section 3). New colors are numbered in the increasing order of
/// (old color, number of neighbors), never by a hash, so equal colors mean equal structure and
/// the numbers depend on the structure alone, not on the names or the order of the rows.
/// O((n + m + t) log(n + m + t)) for n variables, m rows and t terms, with the sorts of the
/// starting colors.
// Complexity tradeoff: naive version, rounds of hashed color refinement until no class
// splits, O(n²) on a pipeline of n stages, which needs about n/2 rounds (125 → 1000 stages:
// 78.5 times the instructions); a fixed count of rounds instead stops before the colors are
// stable, and a hash may merge colors (coefficients 2 and -3). Used: Berkholz, Bonsma and
// Grohe's canonical refinement with Hopcroft's rule, O((n + m + t) log(n + m + t)), colors
// numbered by sorting. Tradeoffs: the graph of variables, rows and terms is built in memory,
// O(n + m + t); a coloring is a stable partition, not a canonical labeling, so symmetric
// variables stay in one class. Tests in `tests/steps/l01_38_presburger/canonical.rs`;
// COMPLEXITY.md row S32.
fn stable_colors(atoms: &[Atom], cons: &[&Con]) -> Vec<usize> {
    let (n, m) = (atoms.len(), cons.len());
    let mut terms: Vec<(usize, usize, &Int)> = Vec::new();
    for (r, c) in cons.iter().enumerate() {
        for (a, k) in &c.lin.terms {
            let x = atoms.binary_search(a).expect("an atom of the system");
            terms.push((r, x, k));
        }
    }
    let size = n + m + terms.len();
    // Vertices: the variables, then the rows, then the terms.
    let mut color = vec![0; size];
    let mut next = usize::from(n > 0);
    let mut rows: Vec<usize> = (0..m).collect();
    let row = |r: usize| (cons[r].rel, &cons[r].lin.constant);
    rows.sort_by(|&p, &q| row(p).cmp(&row(q)));
    for (i, &r) in rows.iter().enumerate() {
        if i > 0 && row(rows[i - 1]) != row(r) {
            next += 1;
        }
        color[n + r] = next;
    }
    next += usize::from(m > 0);
    let mut by_coef: Vec<usize> = (0..terms.len()).collect();
    by_coef.sort_by(|&p, &q| terms[p].2.cmp(terms[q].2));
    for (i, &e) in by_coef.iter().enumerate() {
        if i > 0 && terms[by_coef[i - 1]].2 != terms[e].2 {
            next += 1;
        }
        color[n + m + e] = next;
    }
    next += usize::from(!terms.is_empty());
    // The neighbors of vertex v are `adj[start[v]..start[v + 1]]`.
    let mut start = vec![0; size + 1];
    for (e, &(r, x, _)) in terms.iter().enumerate() {
        start[x + 1] += 1;
        start[n + r + 1] += 1;
        start[n + m + e + 1] = 2;
    }
    for v in 0..size {
        start[v + 1] += start[v];
    }
    let mut adj = vec![0; start[size]];
    let mut cursor = start[..size].to_vec();
    let mut link = |a: usize, b: usize| {
        adj[cursor[a]] = b;
        cursor[a] += 1;
    };
    for (e, &(r, x, _)) in terms.iter().enumerate() {
        let e = n + m + e;
        link(x, e);
        link(e, x);
        link(n + r, e);
        link(e, n + r);
    }
    let degree = (0..size)
        .map(|v| start[v + 1] - start[v])
        .max()
        .unwrap_or(0);
    let mut refine = Refine::new(color, next, degree);
    refine.run(&start, &adj);
    refine.color.truncate(n + m);
    refine.color
}

/// The coefficients of a row, nonzero, in variable order. Rows are shared, not copied, among
/// the system, its index and the steps.
type Coefs = Rc<[Term]>;

/// A splinter (`Omega::splinter`): its rows, each `>= 0` or `== 0`, and the colors of its
/// variables.
type Splinter = (Vec<(Row, Rel)>, Vec<usize>);

/// `Σ a[i]·x[i] + k`, compared with zero by `>=`, or by `==` among the equalities.
#[derive(Clone)]
struct Row {
    a: Coefs,
    k: Int,
}

/// What normalizing a row gives.
enum Norm {
    True,
    False,
    Row(Row),
}

/// `f·x + g·y`, without the variable `skip`.
fn merge(x: &[Term], f: &Int, y: &[Term], g: &Int, skip: usize) -> Coefs {
    let mut out = Vec::with_capacity(x.len() + y.len());
    let (mut xs, mut ys) = (x.iter().peekable(), y.iter().peekable());
    loop {
        let order = match (xs.peek(), ys.peek()) {
            (Some(p), Some(q)) => p.0.cmp(&q.0),
            (Some(_), None) => Ordering::Less,
            (None, Some(_)) => Ordering::Greater,
            (None, None) => break,
        };
        let (v, c) = match order {
            Ordering::Less => {
                let (v, c) = xs.next().expect("peeked");
                (*v, c * f)
            }
            Ordering::Greater => {
                let (v, d) = ys.next().expect("peeked");
                (*v, d * g)
            }
            Ordering::Equal => {
                let (v, c) = xs.next().expect("peeked");
                let (_, d) = ys.next().expect("peeked");
                (*v, &(c * f) + &(d * g))
            }
        };
        if v != skip && !c.is_zero() {
            out.push((v, c));
        }
    }
    out.into()
}

/// The coefficients of the opposite row.
fn opposite(a: &[Term]) -> Vec<Term> {
    a.iter().map(|(i, c)| (*i, -c)).collect()
}

/// Whether every real point `(x, y)` of the box `b` = [x least, x greatest, y least, y
/// greatest] with `p·(x, y) + pk >= 0` has `q·(x, y) + qk >= 0`, for rows `p` and `q` over
/// the same two variables. That part of the box is a polygon, and `q` is least over it at a
/// corner: a corner of the box that `p` keeps, or where the line of `p` crosses a side of the
/// box, at `(x / d, y / d)` with `d > 0`. An empty part gives `true`, and then the system has
/// no point.
fn implies_in_box(b: &[Int; 4], p: &[Term], pk: &Int, q: &[Term], qk: &Int) -> bool {
    let (pi, pj, qi, qj) = (&p[0].1, &p[1].1, &q[0].1, &q[1].1);
    // `d` times `q` at `(x / d, y / d)`.
    let q_at = |x: &Int, y: &Int, d: &Int| &(&(qi * x) + &(qj * y)) + &(qk * d);
    for x in [&b[0], &b[1]] {
        for y in [&b[2], &b[3]] {
            let kept = !(&(&(pi * x) + &(pj * y)) + pk).is_negative();
            if kept && q_at(x, y, &Int::ONE).is_negative() {
                return false;
            }
        }
    }
    // The line of `p` on the sides `x = X`, at `y = -(pi·X + pk) / pj`, and on the sides
    // `y = Y`, at `x = -(pj·Y + pk) / pi`; the coefficients of a row are not zero.
    let cut = |c: &Int, at: &Int, over: &Int| {
        let (num, d) = (-&(&(c * at) + pk), over.clone());
        if d.is_negative() {
            (-&num, -&d)
        } else {
            (num, d)
        }
    };
    for x in [&b[0], &b[1]] {
        let (y, d) = cut(pi, x, pj);
        if y >= &b[2] * &d && y <= &b[3] * &d && q_at(&(x * &d), &y, &d).is_negative() {
            return false;
        }
    }
    for y in [&b[2], &b[3]] {
        let (x, d) = cut(pj, y, pi);
        if x >= &b[0] * &d && x <= &b[1] * &d && q_at(&x, &(y * &d), &d).is_negative() {
            return false;
        }
    }
    true
}

impl Row {
    /// The coefficient at `x[j]`, which the row holds.
    fn at(&self, j: usize) -> &Int {
        let i = self.a.binary_search_by_key(&j, |t| t.0);
        &self.a[i.expect("the row holds the variable")].1
    }

    fn eval(&self, m: &[Int]) -> Int {
        self.a
            .iter()
            .fold(self.k.clone(), |v, (i, c)| &v + &(c * &m[*i]))
    }

    /// The row divided by the gcd of its coefficients, an inequality's constant rounded down.
    fn normal(self, eq: bool) -> Norm {
        let mut g = Int::ZERO;
        for (_, c) in self.a.iter() {
            g = g.gcd(c);
            if g.is_unit() {
                return Norm::Row(self);
            }
        }
        if g.is_zero() {
            let holds = if eq {
                self.k.is_zero()
            } else {
                !self.k.is_negative()
            };
            return if holds { Norm::True } else { Norm::False };
        }
        if eq && !self.k.mod_floor(&g).is_zero() {
            return Norm::False;
        }
        Norm::Row(Row {
            a: self.a.iter().map(|(i, c)| (*i, c.div_floor(&g))).collect(),
            k: self.k.div_floor(&g),
        })
    }

    /// The row, which holds `x[j]`, with `x[j]` replaced by `def`.
    fn subst(&self, j: usize, def: &Row) -> Row {
        let c = self.at(j);
        Row {
            a: merge(&self.a, &Int::ONE, &def.a, c, j),
            k: &self.k + &(c * &def.k),
        }
    }
}

/// The symmetric remainder of `a` by `m`, of either sign, odd in `a`: at exactly half of `m`
/// it takes the sign opposite to `a`, so that `mod_hat(-a, m) == -mod_hat(a, m)` and an
/// equality solved with its sign turned gives the same definition.
fn mod_hat(a: &Int, m: &Int) -> Int {
    let m = m.abs();
    let r = a.mod_floor(&m);
    match (&r + &r).cmp(&m) {
        Ordering::Less => r,
        Ordering::Greater => &r - &m,
        Ordering::Equal if a.is_negative() => r,
        Ordering::Equal => &r - &m,
    }
}

/// How a variable occurs in the inequalities: as a lower or an upper bound, and how often with
/// a coefficient that is not a unit.
#[derive(Default)]
struct Sides {
    lo: usize,
    hi: usize,
    lo_wide: usize,
    hi_wide: usize,
    /// The terms of its rows on each side.
    lo_terms: usize,
    hi_terms: usize,
    /// Its rows of one term, at most one on each side: a row of one term is normalized to a
    /// unit coefficient, and two with the same coefficient are held as one.
    lo_unary: usize,
    hi_unary: usize,
}

impl Sides {
    /// Whether no elimination of the variable is exact.
    fn inexact(&self) -> bool {
        self.lo_wide > 0 && self.hi_wide > 0
    }

    /// The terms its elimination writes less the terms it removes, the variable's own terms
    /// in the new rows not counted.
    fn fill(&self) -> isize {
        let written = self.lo * self.hi_terms + self.hi * self.lo_terms;
        written as isize
            - 2 * (self.lo * self.hi) as isize
            - (self.lo_terms + self.hi_terms) as isize
    }

    /// Whether every row but its bounds pulls the variable to one bound it has.
    fn fixable(&self) -> bool {
        self.lo > 0
            && self.hi > 0
            && ((self.lo == self.lo_unary && self.lo_unary > 0)
                || (self.hi == self.hi_unary && self.hi_unary > 0))
    }

    /// Where the variable `x[j]`, of color `key`, stands among those to eliminate.
    fn rank(&self, key: usize, j: usize) -> Rank {
        (self.fill(), key, j)
    }
}

/// The fill of a variable's elimination, its color, and the variable. The step takes the
/// least fill and color; the place only orders variables that tie in both, among which no
/// choice is made by it (see [`System::least`]).
type Rank = (isize, usize, usize);

/// A row of a [`System`]: its constant, and its place in the system's list.
struct Held {
    k: Int,
    id: usize,
}

/// A variable of a [`System`]: its rows, by place, how it occurs in them, and its color.
#[derive(Default)]
struct Var {
    rows: BTreeSet<usize>,
    sides: Sides,
    key: usize,
    /// Its entry in [`System::shrinking`], when it has one.
    shrink: Option<isize>,
}

/// A system of inequalities, kept normalized as rows are added and removed: each set of
/// coefficients is held once, with its least constant, and each variable knows its rows and
/// how it occurs in them, so that a step touches only the rows of the variable it eliminates.
struct System {
    rows: BTreeMap<Coefs, Held>,
    /// The coefficients of each row ever added, by place, while it is held.
    ids: Vec<Option<Coefs>>,
    vars: Vec<Var>,
    /// The variables whose elimination is exact, by rank.
    exact: BTreeSet<Rank>,
    /// The variables whose elimination is inexact, likewise.
    inexact: BTreeSet<Rank>,
    /// The variables whose elimination is exact and adds no terms as [`System::shrink`]
    /// counts them, by that count, as of the last [`System::refresh`].
    shrinking: BTreeSet<Rank>,
    /// The variables whose rows changed since the last [`System::refresh`].
    dirty: BTreeSet<usize>,
    /// Variables whose rows' variables [`System::refresh`] marks first ([`System::touch`]).
    near: BTreeSet<usize>,
    /// The number of rows held of each length.
    lengths: BTreeMap<usize, usize>,
    /// The places of the held rows of two terms, by their two variables, the lesser first.
    pairs: HashMap<(usize, usize), BTreeSet<usize>>,
    /// The place of the opposite of each held row whose opposite is held, both ways.
    opposites: BTreeMap<usize, usize>,
    /// The variables bounded on one side only.
    one_sided: BTreeSet<usize>,
    /// The variables [`Sides::fixable`] holds of.
    fixable: BTreeSet<usize>,
    /// The lesser coefficients of two opposite rows whose constants sum to zero; a pair may
    /// since have changed, and is checked when taken.
    meets: BTreeSet<Coefs>,
    /// The lesser coefficients of the equalities kept as pairs of opposite rows, which are
    /// not met again.
    loose: BTreeSet<Coefs>,
    /// Whether a row is false, or two opposite rows meet nowhere.
    empty: bool,
    /// The variables some row holds.
    live: usize,
    /// The rows not of the form `±x ± y + k >= 0` or `±x + k >= 0`.
    wide_rows: usize,
}

impl System {
    /// An empty system over variables of the colors `keys`.
    fn new(keys: impl Iterator<Item = usize>) -> System {
        System {
            rows: BTreeMap::new(),
            ids: Vec::new(),
            vars: keys
                .map(|key| Var {
                    key,
                    ..Var::default()
                })
                .collect(),
            exact: BTreeSet::new(),
            inexact: BTreeSet::new(),
            shrinking: BTreeSet::new(),
            dirty: BTreeSet::new(),
            near: BTreeSet::new(),
            lengths: BTreeMap::new(),
            pairs: HashMap::new(),
            opposites: BTreeMap::new(),
            one_sided: BTreeSet::new(),
            fixable: BTreeSet::new(),
            meets: BTreeSet::new(),
            loose: BTreeSet::new(),
            empty: false,
            live: 0,
            wide_rows: 0,
        }
    }

    fn add(&mut self, r: Row) {
        let r = match r.normal(false) {
            Norm::False => {
                self.empty = true;
                return;
            }
            Norm::True => return,
            Norm::Row(r) => r,
        };
        if r.a.len() == 2 && !self.rows.contains_key(&r.a) {
            let Some(weaker) = self.dominated(&r) else {
                return;
            };
            for id in weaker {
                self.remove(id);
            }
        }
        let id = if let Some(old) = self.rows.get_mut(&r.a) {
            if old.k <= r.k {
                return;
            }
            old.k = r.k.clone();
            old.id
        } else {
            let id = self.ids.len();
            self.ids.push(Some(r.a.clone()));
            self.count(&r.a, id, true);
            *self.lengths.entry(r.a.len()).or_insert(0) += 1;
            if let [(i, _), (j, _)] = &r.a[..] {
                self.pairs.entry((*i, *j)).or_default().insert(id);
            }
            self.touch(&r.a);
            let k = r.k.clone();
            self.rows.insert(r.a.clone(), Held { k, id });
            id
        };
        let opp = opposite(&r.a);
        if let Some((key, o)) = self.rows.get_key_value(opp.as_slice()) {
            self.opposites.insert(id, o.id);
            self.opposites.insert(o.id, id);
            let s = &r.k + &o.k;
            if s.is_negative() {
                self.empty = true;
            } else if s.is_zero() {
                let lesser = if r.a < *key { r.a } else { key.clone() };
                if !self.loose.contains(&lesser) {
                    self.meets.insert(lesser);
                }
            }
        }
    }

    /// Counts the row `a` at place `id` in, or out when `!add`, at each of its variables.
    fn count(&mut self, a: &Coefs, id: usize, add: bool) {
        if a.len() > 2 || a.iter().any(|(_, c)| !c.is_unit()) {
            if add {
                self.wide_rows += 1;
            } else {
                self.wide_rows -= 1;
            }
        }
        for (i, c) in a.iter() {
            self.dirty.insert(*i);
            let v = &mut self.vars[*i];
            let set = if v.sides.inexact() {
                &mut self.inexact
            } else {
                &mut self.exact
            };
            let key = v.key;
            set.remove(&v.sides.rank(key, *i));
            self.one_sided.remove(i);
            self.fixable.remove(i);
            let s = &mut v.sides;
            let was = s.lo + s.hi > 0;
            let (side, wide, terms, unary) = if c.is_positive() {
                (&mut s.lo, &mut s.lo_wide, &mut s.lo_terms, &mut s.lo_unary)
            } else {
                (&mut s.hi, &mut s.hi_wide, &mut s.hi_terms, &mut s.hi_unary)
            };
            if add {
                *side += 1;
                *wide += usize::from(!c.is_unit());
                *terms += a.len();
                *unary += usize::from(a.len() == 1);
                v.rows.insert(id);
            } else {
                *side -= 1;
                *wide -= usize::from(!c.is_unit());
                *terms -= a.len();
                *unary -= usize::from(a.len() == 1);
                v.rows.remove(&id);
            }
            match (was, s.lo + s.hi > 0) {
                (false, true) => self.live += 1,
                (true, false) => self.live -= 1,
                _ => {}
            }
            if s.lo + s.hi == 0 {
                continue;
            }
            let set = if s.inexact() {
                &mut self.inexact
            } else {
                &mut self.exact
            };
            set.insert(s.rank(key, *i));
            if s.lo == 0 || s.hi == 0 {
                self.one_sided.insert(*i);
            }
            if s.fixable() {
                self.fixable.insert(*i);
            }
        }
    }

    /// Marks for [`System::refresh`] the variables whose [`System::shrink`] the row `a`, just
    /// added or removed, can change besides its own: whether a row written is held already. A
    /// row the elimination of `x[j]` writes holds only variables of the rows of `x[j]`, so
    /// `x[j]` shares a row with each variable of `a`, and with the one of fewest rows in
    /// particular. That variable is kept, and [`System::refresh`] marks the variables of its
    /// rows as they are held then: `x[j]` still shares one of them with it, or that row was
    /// removed and [`System::count`] marked `x[j]`. Marking here, at a cost of the terms of
    /// those rows, made every row added beside a sum of n bounded terms cost O(n)
    /// (`omega::eliminating_the_terms_of_a_long_row_costs_the_row_each_time` took 26.7 times
    /// the instructions from 128 to 1,024), though most systems never reach the stage that
    /// reads the marks. Which of several such variables is taken marks other variables but
    /// changes no count.
    fn touch(&mut self, a: &Coefs) {
        if let Some(v) = a
            .iter()
            .map(|(i, _)| *i)
            .min_by_key(|i| (self.vars[*i].rows.len(), *i))
        {
            self.near.insert(v);
        }
    }

    /// For a row `r` of two terms not held yet: `None` when a held row over the same two
    /// variables implies it within their bounds and is not implied by it, else the places of
    /// the held rows over those variables that `r` implies so and that do not imply `r`.
    ///
    /// Dropping such a row keeps every point, integer or not: the stronger row and the
    /// bounds stay. A row is dropped when a row ever added over its pair implies it strictly,
    /// and implying strictly is transitive, so the rows kept are the same in whatever order
    /// they are added while the bounds stand. Rows with a held opposite, which may be an
    /// equality, are left alone. Without this, eliminating a convex chain
    /// (`q1_local::growth_of_a_convex_valley`) carried rows `k·x - (k - 1)·y >= -N` for every
    /// k so far, all through the corner (N, N) of the box and each implied by the next, from
    /// one variable to the next: O(n) rows per step, 38.1 times the bytes for 8 times the
    /// size.
    ///
    /// The rows over the pair are found in [`System::pairs`], O(1) expected.
    ///
    /// Complexity tradeoff: the new row is compared with each of the p rows kept over its
    /// pair, O(p) for each row of two terms added. Why: which rows imply which depends on the
    /// bounds, so the rows of a pair are not kept in an order that a search could use. Trigger:
    /// a pair with many rows of which none implies another strictly within the bounds, each a
    /// side of the polygon they cut from the box. Measured (Q1-LOCAL, 2026-11-08): the largest p
    /// was 10 (a tree of blocks of five, n = 256), 7 or less from n = 512 to 2,048 with no
    /// growth in n, 3 in the convex valley, 5 in the oracle's family; the comparisons were 4%
    /// of the rows added or less. A complete solution would keep only the sides of the
    /// polygon that the rows of the pair together cut from the box, in order of the angle of
    /// their normals as dynamic half-plane intersection does, and find the sides a new row
    /// meets by binary search, O(log p).
    fn dominated(&self, r: &Row) -> Option<Vec<usize>> {
        let mut weaker = Vec::new();
        let [(i, _), (j, _)] = &r.a[..] else {
            return Some(weaker);
        };
        if self.rows.contains_key(opposite(&r.a).as_slice()) {
            return Some(weaker);
        }
        let bounds = [
            self.bound(*i, false),
            self.bound(*i, true),
            self.bound(*j, false),
            self.bound(*j, true),
        ];
        let [Some(ilo), Some(ihi), Some(jlo), Some(jhi)] = bounds else {
            return Some(weaker);
        };
        let b = [ilo, ihi, jlo, jhi];
        let Some(ids) = self.pairs.get(&(*i, *j)) else {
            return Some(weaker);
        };
        for id in ids {
            let a = self.ids[*id].as_ref().expect("a row held");
            if self.opposites.contains_key(id) {
                continue;
            }
            let k = &self.rows[a].k;
            let stronger = implies_in_box(&b, a, k, &r.a, &r.k);
            let implied = implies_in_box(&b, &r.a, &r.k, a, k);
            if stronger && !implied {
                return None;
            }
            if implied && !stronger {
                weaker.push(*id);
            }
        }
        Some(weaker)
    }

    /// Removes the held row at place `id`, and returns it.
    fn remove(&mut self, id: usize) -> Row {
        let a = self.ids[id].take().expect("a row held");
        let k = self.rows.remove(&a).expect("a row held").k;
        self.count(&a, id, false);
        if let [(i, _), (j, _)] = &a[..]
            && let Some(ids) = self.pairs.get_mut(&(*i, *j))
        {
            ids.remove(&id);
            if ids.is_empty() {
                self.pairs.remove(&(*i, *j));
            }
        }
        if let Some(o) = self.opposites.remove(&id) {
            self.opposites.remove(&o);
        }
        if let Some(n) = self.lengths.get_mut(&a.len()) {
            *n -= 1;
            if *n == 0 {
                self.lengths.remove(&a.len());
            }
        }
        self.touch(&a);
        Row { a, k }
    }

    /// Removes the rows that hold `x[j]`, and returns them.
    fn take(&mut self, j: usize) -> Vec<Row> {
        let ids = std::mem::take(&mut self.vars[j].rows);
        ids.into_iter().map(|id| self.remove(id)).collect()
    }

    /// The rows of opposite pairs that meet in an equality, one of each pair, all removed. Two
    /// pairs share no row, since a row has one opposite, so taking them all at once leaves the
    /// same system in whatever order they are taken.
    fn meetings(&mut self) -> Vec<Row> {
        let mut out = Vec::new();
        for a in std::mem::take(&mut self.meets) {
            let opp = opposite(&a);
            if let (Some(r), Some(o)) = (self.rows.get(&a), self.rows.get(opp.as_slice()))
                && (&r.k + &o.k).is_zero()
            {
                let (r, o) = (r.id, o.id);
                self.remove(o);
                out.push(self.remove(r));
            }
        }
        out
    }

    /// The variables of least fill and color among the ranks of `sets`, with that fill: all
    /// of them when no two share a row, and otherwise the tie, with the rows they share.
    ///
    /// Variables that share no row are eliminated together, and the order among them does
    /// not change the result: eliminating `x[i]` removes the rows of `x[i]` and adds rows over
    /// their other variables, none of which is `x[j]`, since no row holds both, so the rows of
    /// `x[j]`, and with them its elimination, are the same before and after; and adding a row
    /// keeps the least constant of each set of coefficients, which no order changes.
    fn least(&self, sets: &[&BTreeSet<Rank>]) -> Option<(isize, Result<Vec<usize>, Tied>)> {
        let &(fill, key, _) = sets.iter().filter_map(|s| s.first()).min()?;
        let js: Vec<usize> = sets
            .iter()
            .flat_map(|s| s.range((fill, key, 0)..=(fill, key, usize::MAX)))
            .map(|r| r.2)
            .collect();
        let mut seen: BTreeMap<usize, usize> = BTreeMap::new();
        for j in &js {
            for id in &self.vars[*j].rows {
                *seen.entry(*id).or_insert(0) += 1;
            }
        }
        let shared: Vec<(Row, Rel)> = seen
            .into_iter()
            .filter(|(_, n)| *n > 1)
            .map(|(id, _)| {
                let a = self.ids[id].clone().expect("a row held");
                let k = self.rows[&a].k.clone();
                (Row { a, k }, Rel::Ge)
            })
            .collect();
        if shared.is_empty() {
            Some((fill, Ok(js)))
        } else {
            Some((
                fill,
                Err(Tied {
                    vars: js,
                    rows: shared,
                }),
            ))
        }
    }

    /// The value of the bound row of `x[j]` on the side `upper`, if it has one.
    fn bound(&self, j: usize, upper: bool) -> Option<Int> {
        let c = if upper { -&Int::ONE } else { Int::ONE };
        let held = self.rows.get([(j, c)].as_slice())?;
        Some(if upper { held.k.clone() } else { -&held.k })
    }

    /// The terms the real shadow of `x[j]` writes less the terms it removes, the rows written
    /// counted as [`System::add`] keeps them: a row of no term (two opposite rows, or rows
    /// whose other terms cancel), a row held already, and a row written twice add nothing.
    /// `None` once the terms written exceed those removed.
    ///
    /// Complexity tradeoff: the pairs of lower and upper rows are combined until the terms
    /// written exceed those removed, so a count costs O((r + z) t log n) for the r terms of the
    /// variable's rows, z pairs that write nothing new, and rows of t terms; the z pairs are
    /// not bounded by r, and a variable is counted again each time one of its rows changes
    /// (from [`System::refresh`]). Two opposite rows, and a bound with another row, are counted
    /// without writing a row, so a long row that many variables share, as the sum of
    /// `q1_local::growth_of_offsets_laid_end_to_end`, is not written once per variable (written
    /// so, that test took 28.5 times the bytes for 8 times the size). Why: knowing exactly
    /// whether an elimination adds terms needs the rows it writes, and the count that
    /// `Sides::fill` keeps per row cannot see cancellation or rows held already. Trigger: a variable of d rows whose d^2 / 4 pairs
    /// mostly write rows held already or constants, its rows changed by many steps before the
    /// counts are needed; the size of the system plays no part. Rows of a bounded number of
    /// variables each, as in `q1_local::sliding_windows_of_four_are_decided`, give z = O(1)
    /// per count and O(1) counts per step. A complete solution would keep, per pair of rows,
    /// whether it writes a new row, renewed as rows come and go. Given up besides: the bound
    /// from the lengths of the rows (`apart`) and the count of a bound with another row take
    /// two pairs that write one row as two rows, so such a variable can be left out, and a
    /// system decided only through it is refused (`Refusal::Growth`); no answer is wrong,
    /// since every elimination taken is exact. COMPLEXITY.md row Q1-LOCAL.
    fn shrink(&self, j: usize) -> Option<isize> {
        // Constants do not change the terms of a row written, so the rows are taken at 0.
        let with: Vec<(usize, Row)> = self.vars[j]
            .rows
            .iter()
            .map(|id| {
                let a = self.ids[*id].clone().expect("a row held");
                (*id, Row { a, k: Int::ZERO })
            })
            .collect();
        let removed: usize = with.iter().map(|(_, r)| r.a.len()).sum();
        let (lowers, uppers): (Vec<_>, Vec<_>) =
            with.iter().partition(|(_, r)| r.at(j).is_positive());
        // A pair of rows of s and t terms writes a row of at least g = |s - t| terms: `x[j]`
        // leaves both, and at most the other terms of the shorter cancel. Such a row is held
        // already only if a held row without `x[j]` has g terms or more, so the pairs with g
        // above the longest of those, `beyond`, write at least g terms each, unless two of
        // them write one row. Their sum, from the sorted lengths, shows a long row's
        // elimination growing without writing a row of it.
        let mut own: BTreeMap<usize, usize> = BTreeMap::new();
        for (_, r) in &with {
            *own.entry(r.a.len()).or_insert(0) += 1;
        }
        // Whether a row of `t` terms without `x[j]` is held.
        let elsewhere = |t: usize| {
            self.lengths
                .get(&t)
                .is_some_and(|n| own.get(&t).is_none_or(|m| n > m))
        };
        let beyond = self
            .lengths
            .iter()
            .rev()
            .find(|(t, n)| own.get(t).is_none_or(|m| *n > m))
            .map_or(0, |(t, _)| *t);
        let length = |side: &[&(usize, Row)]| side.iter().map(|(_, r)| r.a.len()).collect();
        if apart(length(&lowers), length(&uppers), beyond) > removed {
            return None;
        }
        let mut new: BTreeSet<Coefs> = BTreeSet::new();
        let mut written = 0;
        for (l, lo) in &lowers {
            for (h, hi) in &uppers {
                // Two opposite rows write a constant, and a bound `x[j] >= c` or `x[j] <= c`
                // with a row of t terms writes that row without `x[j]`: t - 1 terms, new when
                // no held row has t - 1 terms. Both are known without writing the row, which
                // keeps a long row shared by many variables from being written for each.
                // Such a row is not compared with the rows written, so two of them equal
                // count twice; that can only leave the variable out.
                if self.opposites.get(l) == Some(h) {
                    continue;
                }
                let other = match (lo.a.len(), hi.a.len()) {
                    (1, t) | (t, 1) => Some(t - 1).filter(|t| !elsewhere(*t)),
                    _ => None,
                };
                let t = match other {
                    Some(t) => t,
                    None => match combine(lo, hi, j, false).normal(false) {
                        Norm::Row(r) if !self.rows.contains_key(&r.a) => {
                            let t = r.a.len();
                            if !new.insert(r.a) {
                                continue;
                            }
                            t
                        }
                        _ => continue,
                    },
                };
                written += t;
                if written > removed {
                    return None;
                }
            }
        }
        Some(written as isize - removed as isize)
    }

    /// Renews [`System::shrinking`] for the variables whose rows changed since it was last
    /// renewed: those of exact elimination bounded on both sides whose [`System::shrink`] is
    /// zero or less. The rows of the variables [`System::touch`] kept are each read once,
    /// however many of those variables hold them: until Q1-LOCAL a row of n terms shared by n
    /// such variables was read n times in one call, O(n^2)
    /// (`q1_local::growth_of_offsets_laid_end_to_end`).
    fn refresh(&mut self) {
        let mut seen: HashSet<usize> = HashSet::new();
        for v in std::mem::take(&mut self.near) {
            for id in &self.vars[v].rows {
                if !seen.insert(*id) {
                    continue;
                }
                for (i, _) in self.ids[*id].as_ref().expect("a row held").iter() {
                    self.dirty.insert(*i);
                }
            }
        }
        for j in std::mem::take(&mut self.dirty) {
            let v = &self.vars[j];
            if let Some(f) = v.shrink {
                self.shrinking.remove(&(f, v.key, j));
            }
            let s = &v.sides;
            let f = if s.lo > 0 && s.hi > 0 && !s.inexact() {
                self.shrink(j).filter(|f| *f <= 0)
            } else {
                None
            };
            if let Some(f) = f {
                self.shrinking.insert((f, v.key, j));
            }
            self.vars[j].shrink = f;
        }
    }

    /// Eliminates `x[j]` by its real shadow, or its dark one when `dark`; returns its rows.
    fn eliminate(&mut self, j: usize, dark: bool) -> Vec<Row> {
        let with = self.take(j);
        let (lowers, uppers): (Vec<&Row>, Vec<&Row>) =
            with.iter().partition(|r| r.at(j).is_positive());
        for lo in &lowers {
            for hi in &uppers {
                self.add(combine(lo, hi, j, dark));
            }
        }
        with
    }
}

/// The sum of `|s - t|` over the lengths `s` of `lowers` and `t` of `uppers` that differ by
/// more than `beyond`, from the sorted lengths with prefix sums: O(d log d) for d rows.
fn apart(lowers: Vec<usize>, mut hi: Vec<usize>, beyond: usize) -> usize {
    hi.sort_unstable();
    let mut below = vec![0; hi.len() + 1];
    for (i, t) in hi.iter().enumerate() {
        below[i + 1] = below[i] + t;
    }
    let total = below[hi.len()];
    lowers
        .into_iter()
        .map(|s| {
            // The uppers shorter than `s - beyond`, and those longer than `s + beyond`.
            let m = hi.partition_point(|t| t + beyond < s);
            let p = hi.partition_point(|t| *t <= s + beyond);
            (m * s - below[m]) + (total - below[p] - (hi.len() - p) * s)
        })
        .sum()
}

/// Whether the inequalities have no rational point once each row is normalized, which keeps
/// every integer point: real shadows while an elimination adds no terms, and the box test of
/// [`box_empty`] on what is left. The shadows are taken as [`System::least`] gives them: all
/// the variables of least fill and color together, and where two of those share a row, none,
/// the box test then deciding, so no step turns on the names of the variables.
fn relaxed_empty(gs: &System) -> bool {
    let mut sys = System::new(gs.vars.iter().map(|v| v.key));
    for (a, r) in &gs.rows {
        sys.add(Row {
            a: a.clone(),
            k: r.k.clone(),
        });
    }
    while !sys.empty {
        let Some((fill, js)) = sys.least(&[&sys.exact, &sys.inexact]) else {
            return false;
        };
        let (true, Ok(js)) = (fill <= 0, js) else {
            return box_empty(&sys);
        };
        for j in js {
            sys.eliminate(j, false);
        }
    }
    true
}

/// The lower and the upper bound of each variable, where it has one.
type Bounds = (Vec<Option<Int>>, Vec<Option<Int>>);

/// The bounds of each variable: those of its bound rows, each then tightened once by every
/// wide row `Σ a[i]·x[i] + k >= 0` from those bounds, all rows at the same time, so the
/// result does not depend on the order of the rows. With each other term at its largest value
/// in the box, the row leaves `a[i]·x[i] >= -rest`, a bound every integer point keeps; `rest`
/// is known when at most `x[i]` itself lacks the bound the row needs. `None` when some
/// variable is left with no value, which shows the rows empty. One pass over the terms.
fn bounds(sys: &System) -> Option<Bounds> {
    let n = sys.vars.len();
    let lo: Vec<Option<Int>> = (0..n).map(|j| sys.bound(j, false)).collect();
    let hi: Vec<Option<Int>> = (0..n).map(|j| sys.bound(j, true)).collect();
    let wide = sys.rows.iter().filter(|(a, _)| a.len() > 1);
    tightened(lo, hi, wide.map(|(a, held)| (&**a, &held.k)))
}

/// The bounds `lo`, `hi` of each variable, each tightened once by every wide row
/// `Σ a[i]·x[i] + k >= 0` of `wide` from those bounds, all rows at the same time ([`bounds`]); `None` when
/// some variable is left with no value. One pass over the terms.
fn tightened<'r>(
    lo: Vec<Option<Int>>,
    hi: Vec<Option<Int>>,
    wide: impl Iterator<Item = (&'r [Term], &'r Int)>,
) -> Option<Bounds> {
    let n = lo.len();
    let (mut tlo, mut thi) = (lo.clone(), hi.clone());
    for (a, k) in wide {
        // The largest value of `c·x[i]` in the box.
        let top = |i: usize, c: &Int| {
            if c.is_positive() { &hi[i] } else { &lo[i] }
                .as_ref()
                .map(|b| c * b)
        };
        let mut sum = k.clone();
        let mut open: Vec<usize> = Vec::new();
        for (i, c) in a.iter() {
            match top(*i, c) {
                Some(m) => sum = &sum + &m,
                None => open.push(*i),
            }
        }
        for (i, c) in a.iter() {
            let rest = match (open.as_slice(), top(*i, c)) {
                ([], Some(m)) => &sum - &m,
                ([o], None) if o == i => sum.clone(),
                _ => continue,
            };
            if c.is_positive() {
                let b = -&rest.div_floor(c);
                if tlo[*i].as_ref().is_none_or(|l| *l < b) {
                    tlo[*i] = Some(b);
                }
            } else {
                let b = rest.div_floor(&-c);
                if thi[*i].as_ref().is_none_or(|h| b < *h) {
                    thi[*i] = Some(b);
                }
            }
        }
    }
    let empty = (0..n).any(|j| matches!((&tlo[j], &thi[j]), (Some(l), Some(h)) if h < l));
    (!empty).then_some((tlo, thi))
}

/// Whether the wide rows `Σ a[i]·x[i] + k >= 0` have no rational point in the box `lo`, `hi`,
/// by one of two tests on each row ([`row_box_empty`]): the row is below zero at every point of
/// the box, or it bounds a variable on one side by a rational past the bound another row gives
/// it on the other. Each variable keeps the greatest lower and the least upper bound the rows
/// have given it so far, so a pair of crossing bounds is found when the later of its two rows
/// is read, whatever the order of the rows. One pass over the terms. Every point of the rows
/// lies in the box, so either test shows them empty.
fn box_empty_in(sys: &System, lo: &[Option<Int>], hi: &[Option<Int>]) -> bool {
    // The box's own bounds have no place here: a row that bounds a variable past one of them
    // is below zero at every point of the box, which the first test finds.
    let mut least: Vec<Option<Q>> = vec![None; lo.len()];
    let mut most: Vec<Option<Q>> = vec![None; hi.len()];
    sys.rows
        .iter()
        .filter(|(a, _)| a.len() > 1)
        .any(|(a, held)| row_box_empty(a, &held.k, lo, hi, &mut least, &mut most))
}

/// Whether the row `Σ a[i]·x[i] + k >= 0` shows the rows empty in the box `lo`, `hi`, given the
/// greatest lower bounds `least` and the least upper bounds `most` that the rows read before it
/// gave each variable, which it then updates with its own. Its largest value in the box, `k`
/// plus each `a[i]` times the upper bound of `x[i]` when `a[i]` is above zero and the lower one
/// when below, is negative; or, with each other term at its largest value `rest`, the row
/// leaves `a[i]·x[i] >= -rest`, a rational bound on `x[i]` that crosses the other side's bound.
/// `rest` is known when at most `x[i]` itself lacks the bound the row needs. No bound is
/// rounded, so what is shown empty has no rational point in the box. Two passes over the
/// row's terms.
fn row_box_empty(
    a: &[Term],
    k: &Int,
    lo: &[Option<Int>],
    hi: &[Option<Int>],
    least: &mut [Option<Q>],
    most: &mut [Option<Q>],
) -> bool {
    // The largest value of `c·x[i]` in the box.
    let top = |i: usize, c: &Int| {
        if c.is_positive() { &hi[i] } else { &lo[i] }
            .as_ref()
            .map(|b| c * b)
    };
    let mut sum = k.clone();
    let mut open: Option<usize> = None;
    for (i, c) in a {
        match top(*i, c) {
            Some(m) => sum = &sum + &m,
            None if open.is_none() => open = Some(*i),
            // Two variables lack the bound the row needs: it bounds none of them.
            None => return false,
        }
    }
    if open.is_none() && sum.is_negative() {
        return true;
    }
    for (i, c) in a {
        let rest = match (open, top(*i, c)) {
            (None, Some(m)) => &sum - &m,
            (Some(o), None) if o == *i => sum.clone(),
            _ => continue,
        };
        if c.is_positive() {
            // `c·x[i] >= -rest`: a lower bound.
            let b = Q::new(-&rest, c.clone());
            if most[*i].as_ref().is_some_and(|h| *h < b) {
                return true;
            }
            if least[*i].as_ref().is_none_or(|l| *l < b) {
                least[*i] = Some(b);
            }
        } else {
            // `-c·x[i] <= rest`: an upper bound.
            let b = Q::new(rest, -c);
            if least[*i].as_ref().is_some_and(|l| b < *l) {
                return true;
            }
            if most[*i].as_ref().is_none_or(|h| b < *h) {
                most[*i] = Some(b);
            }
        }
    }
    false
}

/// Whether the rows are empty by [`bounds`] or by [`box_empty_in`] in the box it gives.
fn box_empty(sys: &System) -> bool {
    bounds(sys).is_none_or(|(lo, hi)| box_empty_in(sys, &lo, &hi))
}

/// The value of one variable in one candidate point of the box stage, from its two bounds, or
/// none where a bound it reads is missing.
type Coordinate = fn(&Option<Int>, &Option<Int>) -> Option<Int>;

/// The five candidate points of the box stage, one coordinate at a time: the value nearest
/// zero ([`nearest_zero`], which also stands in wherever a bound is missing), the lower bound,
/// the upper bound, and the midpoint of the bounds rounded down and rounded up.
const CANDIDATES: [Coordinate; 5] = [
    |_, _| None,
    |lo, _| lo.clone(),
    |_, hi| hi.clone(),
    |lo, hi| Some((lo.as_ref()? + hi.as_ref()?).div_floor(&Int::from(2))),
    |lo, hi| Some((&(lo.as_ref()? + hi.as_ref()?) + &Int::ONE).div_floor(&Int::from(2))),
];

/// The value nearest zero between the bounds `lo` and `hi`.
fn nearest_zero(lo: &Option<Int>, hi: &Option<Int>) -> Int {
    match (lo, hi) {
        (Some(l), _) if l.is_positive() => l.clone(),
        (_, Some(h)) if h.is_negative() => h.clone(),
        _ => Int::ZERO,
    }
}

/// The first of five points of the box `lo`, `hi` that holds every row: the point nearest
/// zero, the lower corner, the upper corner, and the two midpoints, rounded down and rounded
/// up ([`CANDIDATES`]), each taken variable by variable. Each costs one pass over the terms of
/// the rows. They depend on the rows and the box alone, not on the names of the variables or
/// the order of the rows.
fn box_point(sys: &System, lo: &[Option<Int>], hi: &[Option<Int>]) -> Option<Vec<Int>> {
    CANDIDATES.iter().find_map(|at| {
        let v: Vec<Int> = lo
            .iter()
            .zip(hi)
            .map(|(l, h)| at(l, h).unwrap_or_else(|| nearest_zero(l, h)))
            .collect();
        let holds = sys.rows.iter().all(|(a, held)| {
            !a.iter()
                .fold(held.k.clone(), |s, (i, c)| &s + &(c * &v[*i]))
                .is_negative()
        });
        holds.then_some(v)
    })
}

/// The shadow row of the lower bound `a·x + l >= 0` and the upper bound `-b·x + u >= 0` on
/// `x = x[j]`: the real shadow `a·u + b·l >= 0`, or the dark one
/// `a·u + b·l >= (a - 1)(b - 1)` when `dark`.
fn combine(lo: &Row, hi: &Row, j: usize, dark: bool) -> Row {
    let (a, b) = (lo.at(j), &-hi.at(j));
    let k = &(&hi.k * a) + &(&lo.k * b);
    Row {
        a: merge(&hi.a, a, &lo.a, b, j),
        k: if dark {
            &k - &(&(a - &Int::ONE) * &(b - &Int::ONE))
        } else {
            k
        },
    }
}
/// An equality as its structure gives it: the colors of its variables with their
/// coefficients, sorted, and its constant, taken for the row or its negation, whichever is
/// less, so that neither the names of the variables nor the sign the row was written with
/// changes it.
type Shape = (Vec<(usize, Int)>, Int);

/// The order in which equalities are solved: first those written by the latest batch of steps,
/// so that the work stays with the equalities the last step changed, as a stack of equalities
/// does; then the fewest variables; then the number of equalities that hold the variable the
/// step would define (its degree, the least over a tie), so that a step writes its definition
/// into as few other equalities as it can; then the [`Shape`]. Each part is given by the
/// structure and by the steps before, none by a name. Along a chain of equalities this goes
/// from one equality to the next and keeps each as short as it was; an order that jumps
/// fills the rows in, and their coefficients grow.
type EqKey = (std::cmp::Reverse<u64>, usize, usize, Shape);

/// The [`Shape`] of the row `r` over the variables of `sys`.
fn shape(r: &Row, sys: &System) -> Shape {
    let side = |f: &Int| -> Shape {
        let mut a: Vec<(usize, Int)> = r.a.iter().map(|(i, c)| (sys.vars[*i].key, c * f)).collect();
        a.sort_unstable();
        (a, &r.k * f)
    };
    side(&Int::ONE).min(side(&-&Int::ONE))
}

/// The variables a step on the equality `e` would choose to define, as `Omega::equality`
/// chooses: those with a unit coefficient when there are any, otherwise those of least
/// coefficient; of these those that no other equality holds, when there are any (`others`
/// gives the number of other equalities that hold a variable); and of these those of least
/// color. More than one is a tie.
///
/// A variable no other equality holds is defined without writing into any equality: its
/// definition is substituted only into the equalities that hold it, and there are none. So
/// along a chain of equalities each with a variable of its own, as `o[i+1] == o[i] + l[i]`
/// with each `l[i]` in one equality, or `x[i+1] == x[i] + c`, whose end variables are each in
/// one equality and leave the next end so, every equality keeps its length, and a step costs
/// O(t log n) for its t terms. Until Q1-LOCAL the choice went by color alone: on `o[i+1] ==
/// o[i] + l[i]` a variable of two equalities was chosen, each step added a term to the next
/// equality, and n pieces cost O(n^2) (23.4 times the instructions and 32.4 times the bytes
/// from 64 to 512 pieces). Whether another equality holds a variable is structure, not a
/// name, so the choice is the same under every naming of the variables.
fn pivots(e: &Row, sys: &System, others: impl Fn(usize) -> usize) -> Vec<usize> {
    let units = e.a.iter().any(|(_, c)| c.is_unit());
    let pool: Vec<(Int, bool, usize, usize)> =
        e.a.iter()
            .filter(|(_, c)| !units || c.is_unit())
            .map(|(i, c)| (c.abs(), others(*i) > 0, sys.vars[*i].key, *i))
            .collect();
    let (m, shared, k, _) = pool.iter().min().expect("a row has a variable").clone();
    pool.into_iter()
        .filter(|(c, sh, kk, _)| *c == m && *sh == shared && *kk == k)
        .map(|p| p.3)
        .collect()
}

/// The row or its negation, whichever is less, as its coefficients and its constant: two
/// equalities with the same one are the same equality.
fn unsigned(r: &Row) -> (Vec<Term>, Int) {
    let neg = opposite(&r.a);
    if *r.a <= *neg {
        (r.a.to_vec(), r.k.clone())
    } else {
        (neg, -&r.k)
    }
}

/// An equality held: its row, its key, and the variables a step on it would define.
struct Kept {
    row: Row,
    key: EqKey,
    pivots: Vec<usize>,
}

/// The equalities, by slot, a slot emptied when its row holds everywhere or another slot
/// holds the same equality, with the slots of each variable, the slots whose step would define
/// each variable, and the slots in use in the order of their [`EqKey`]s.
struct Equalities {
    rows: Vec<Option<Kept>>,
    of: Vec<BTreeSet<usize>>,
    pivot_of: Vec<BTreeSet<usize>>,
    order: BTreeSet<(EqKey, usize)>,
    /// The slot of each equality held, by [`unsigned`].
    held: BTreeMap<(Vec<Term>, Int), usize>,
    /// The number of batches of steps begun so far: an equality written by a later one is solved
    /// first.
    now: u64,
}

/// The equalities to solve next, by slot: those of least [`EqKey`] when no two share a variable,
/// otherwise the same slots with the tie.
type EqStep = Result<Vec<usize>, (Vec<usize>, Tied)>;

impl Equalities {
    fn new(vars: usize) -> Equalities {
        Equalities {
            rows: Vec::new(),
            of: vec![BTreeSet::new(); vars],
            pivot_of: vec![BTreeSet::new(); vars],
            order: BTreeSet::new(),
            held: BTreeMap::new(),
            now: 0,
        }
    }

    /// Room for a fresh variable.
    fn grow(&mut self) {
        self.of.push(BTreeSet::new());
        self.pivot_of.push(BTreeSet::new());
    }

    /// The row in slot `s`, which is in use.
    fn row(&self, s: usize) -> &Row {
        &self.rows[s].as_ref().expect("a slot in use").row
    }

    /// The slots of the equalities of least key, all of them when no two share a variable or
    /// when each has one variable to define, with a unit coefficient, that no other of them
    /// holds; otherwise the tie, with the variables they share and the equalities. Equalities
    /// taken so are solved together, and the order among them does not change the result:
    /// solving one defines one of its variables (its pivot) by the others, or by the others
    /// and a fresh one, and writes the definition only into the rows that hold the pivot. In
    /// the first case no other of them holds any of its variables. In the second, no other of
    /// them holds its pivot, so each other is solved the same before and after, and no
    /// definition holds another's pivot, since a definition holds only variables of its own
    /// equality, so each row ends with every pivot replaced by its definition, whatever the
    /// order. Every substitution of one batch is stamped alike (`Equalities::step`), so the
    /// order does not reach the [`EqKey`]s either.
    fn least(&self) -> Option<EqStep> {
        let (key, _) = self.order.first()?;
        let slots: Vec<usize> = self
            .order
            .range((key.clone(), 0)..=(key.clone(), usize::MAX))
            .map(|(_, s)| *s)
            .collect();
        let mut seen: BTreeMap<usize, usize> = BTreeMap::new();
        for s in &slots {
            for (i, _) in self.row(*s).a.iter() {
                *seen.entry(*i).or_insert(0) += 1;
            }
        }
        let vars: Vec<usize> = seen
            .into_iter()
            .filter(|(_, n)| *n > 1)
            .map(|(i, _)| i)
            .collect();
        let apart = |s: &usize| {
            let held = self.rows[*s].as_ref().expect("a slot in use");
            let [p] = held.pivots[..] else {
                return false;
            };
            held.row.at(p).is_unit() && vars.binary_search(&p).is_err()
        };
        if vars.is_empty() || slots.iter().all(apart) {
            return Some(Ok(slots));
        }
        let rows = slots
            .iter()
            .map(|s| (self.row(*s).clone(), Rel::Eq))
            .collect();
        Some(Err((slots, Tied { vars, rows })))
    }

    fn push(&mut self, r: Row, sys: &mut System) {
        self.rows.push(None);
        self.put(self.rows.len() - 1, r, sys);
    }

    /// The degree of a step that would define one of `pivots`.
    fn degree(&self, pivots: &[usize]) -> usize {
        pivots
            .iter()
            .map(|p| self.of[*p].len())
            .min()
            .expect("a pivot")
    }

    fn put(&mut self, s: usize, r: Row, sys: &mut System) {
        match r.normal(true) {
            Norm::False => sys.empty = true,
            Norm::True => {}
            Norm::Row(r) => {
                let same = unsigned(&r);
                if self.held.contains_key(&same) {
                    return;
                }
                self.held.insert(same, s);
                for (i, _) in r.a.iter() {
                    self.of[*i].insert(s);
                }
                let pivots = pivots(&r, sys, |i| self.of[i].len() - 1);
                for p in &pivots {
                    self.pivot_of[*p].insert(s);
                }
                let key = (
                    std::cmp::Reverse(self.now),
                    r.a.len(),
                    self.degree(&pivots),
                    shape(&r, sys),
                );
                self.order.insert((key.clone(), s));
                let vars: Vec<usize> = r.a.iter().map(|(i, _)| *i).collect();
                self.rows[s] = Some(Kept {
                    row: r,
                    key,
                    pivots,
                });
                self.rekey(&vars, s);
                // A variable now in two equalities was, until now, in the other one alone.
                for i in &vars {
                    if self.of[*i].len() == 2 {
                        let t = *self.of[*i].iter().find(|t| **t != s).expect("another slot");
                        self.repivot(t, sys);
                    }
                }
            }
        }
    }

    /// Empties the slot `s`, and returns its row.
    fn clear(&mut self, s: usize, sys: &System) -> Row {
        let Kept { row, key, pivots } = self.rows[s].take().expect("a slot in use");
        self.order.remove(&(key, s));
        self.held.remove(&unsigned(&row));
        for p in &pivots {
            self.pivot_of[*p].remove(&s);
        }
        let vars: Vec<usize> = row.a.iter().map(|(i, _)| *i).collect();
        for i in &vars {
            self.of[*i].remove(&s);
        }
        self.rekey(&vars, s);
        // A variable now in one equality was, until now, in another as well.
        for i in &vars {
            if self.of[*i].len() == 1 {
                let t = *self.of[*i].first().expect("a slot");
                self.repivot(t, sys);
            }
        }
        row
    }

    /// Chooses again the variables a step on slot `t` would define. The choice ([`pivots`])
    /// changes only when one of its variables comes to be held by another equality or ceases
    /// to be, and that variable is then held by at most two equalities, so a change to an
    /// equality renews at most one other slot for each of its variables.
    fn repivot(&mut self, t: usize, sys: &System) {
        let row = &self.rows[t].as_ref().expect("a slot in use").row;
        let new = pivots(row, sys, |i| self.of[i].len() - 1);
        let degree = self.degree(&new);
        let held = self.rows[t].as_mut().expect("a slot in use");
        if held.pivots == new {
            return;
        }
        for p in &held.pivots {
            self.pivot_of[*p].remove(&t);
        }
        for p in &new {
            self.pivot_of[*p].insert(t);
        }
        self.order.remove(&(held.key.clone(), t));
        held.key.2 = degree;
        self.order.insert((held.key.clone(), t));
        held.pivots = new;
    }

    /// Renews the degree in the key of each slot but `s` whose step would define one of
    /// `vars`, whose counts of equalities have changed. Each slot has its own pivots, so a
    /// change to the equalities of a variable renews only the slots that would define it.
    fn rekey(&mut self, vars: &[usize], s: usize) {
        let slots: BTreeSet<usize> = vars
            .iter()
            .flat_map(|v| self.pivot_of[*v].iter().copied())
            .filter(|t| *t != s)
            .collect();
        for t in slots {
            let degree = self.degree(&self.rows[t].as_ref().expect("a slot in use").pivots);
            let held = self.rows[t].as_mut().expect("a slot in use");
            if held.key.2 != degree {
                self.order.remove(&(held.key.clone(), t));
                held.key.2 = degree;
                self.order.insert((held.key.clone(), t));
            }
        }
    }

    /// Starts a batch of steps: the equalities their substitutions write are stamped after
    /// those of every batch before, and alike within the batch.
    fn step(&mut self) {
        self.now += 1;
    }

    /// Replaces `x[j]` by `def` in each equality that holds it. `of[j]` stays exact while the
    /// equalities are rewritten one by one (`clear` takes each from it), since the choice of
    /// pivots of an equality not yet rewritten counts the others that hold `x[j]`.
    fn subst(&mut self, j: usize, def: &Row, sys: &mut System) {
        let slots: Vec<usize> = self.of[j].iter().copied().collect();
        for s in slots {
            let r = self.clear(s, sys);
            self.put(s, r.subst(j, def), sys);
        }
    }
}

/// A step the model is built back through, last step first.
enum Step {
    /// `x[j]` defined by an equality.
    Defined(usize, Row),
    /// `x[j]` chosen within the rows that held it.
    Chosen(usize, Vec<Row>),
}

/// What one run of the Omega test finds.
enum Leaf {
    /// A point, the values by variable; empty when no model was wanted.
    Point(Vec<Int>),
    /// No point; where a dark shadow was taken on the way, no point in the dark shadow.
    Empty,
    /// The system is outside the fragment decided.
    Refused(Refusal),
    /// The next step would choose among candidates that only their names tell apart.
    Tied(Tied),
}

/// The Omega test. Each step solves an equality, turns two opposite rows that meet into one,
/// drops a variable bounded on one side only, fixes a variable at a bound, or eliminates a
/// variable, until no row is left; the model is then built back through the steps.
struct Omega {
    sys: System,
    es: Equalities,
    steps: Vec<Step>,
    /// The definitions not yet written into the inequalities: each inequality is rewritten once
    /// for all of them, however many of its variables they define.
    pending: Vec<(usize, Row)>,
    /// Whether a model is wanted.
    want: bool,
    /// Whether the real shadow was tested, at the first inexact elimination.
    tested: bool,
    /// The dark eliminations kept for the search of their splinters, by batch, the batches in
    /// the order taken: the live variables when the batch was taken, and for each elimination
    /// the place of its step and the number of variables then. A batch is the variables
    /// [`System::least`] gave together, which share no row and which nothing but their names
    /// tells apart.
    gray: Vec<(usize, Vec<(usize, usize)>)>,
    /// Whether a gray shadow with three variables left is decided by `live3` in place of a
    /// dark shadow with a gap: set when a splinter is run again after its first run left one.
    exact3: bool,
    /// The first tie among equalities, which were then kept as pairs of opposite rows.
    loose_tie: Option<Tied>,
    /// The equalities whose coefficients a step has reduced but not yet to a unit: each is
    /// taken again until it is solved, as the Omega test does, since taking another between
    /// its steps can undo their reduction. They share no variable, as the batch they came
    /// from shares none and a step brings in only its own variables and a fresh one.
    working: Vec<usize>,
    /// Whether the cycles of the rows have been searched for the equalities they imply
    /// ([`Omega::cycles`]).
    cycled: bool,
}

impl Omega {
    /// The test on the rows `base`, each `>= 0` or `== 0`, over variables of the colors `keys`.
    fn new(keys: &[usize], base: &[(Row, Rel)], want: bool) -> Omega {
        let mut sys = System::new(keys.iter().copied());
        let mut es = Equalities::new(keys.len());
        for (r, rel) in base {
            match rel {
                Rel::Eq => es.push(r.clone(), &mut sys),
                Rel::Ge => sys.add(r.clone()),
            }
        }
        Omega {
            sys,
            es,
            steps: Vec::new(),
            pending: Vec::new(),
            want,
            tested: false,
            gray: Vec::new(),
            exact3: false,
            loose_tie: None,
            working: Vec::new(),
            cycled: false,
        }
    }

    // Complexity tradeoff: naive version, Pugh's Omega test recursing into both the real and
    // the dark shadow at each inexact elimination, O(2^V) problems per leaf for V variables
    // (15 variables took 1.03 s). Used: one loop with no recursion into the shadows, exact
    // eliminations first, eliminating only while the rows hold no more terms than the input;
    // at the first inexact elimination the real shadow is tested once (`relaxed_empty`), then
    // the dark shadow is solved, and `search` tries the splinters of one side one level deep.
    // Steps are polynomial in the rows (2 ms at 15 variables). Tradeoffs: two refusals, each
    // a property of the system's shape: `Refusal::Shadows` when a splinter leaves a gray
    // shadow of its own, `Refusal::Growth` when every elimination left would add terms and
    // the box test decides nothing; the cases still above n log n are row S18. Tests in
    // `l01_38_presburger::scaling` (`a_long_chain_with_a_point_scales` and the other chain
    // tests); COMPLEXITY.md row S5.
    fn run(&mut self) -> Leaf {
        // The values of the variables left when the loop ends, zero where none is given.
        let mut start: Vec<Int> = Vec::new();
        loop {
            if self.sys.empty {
                return Leaf::Empty;
            }
            // No step below chooses by the names of the variables: each takes what the
            // structure gives first (by color, through `System::least` and
            // `Equalities::least`), all such candidates together when no two share a row, and
            // none when two do, which ends the eliminations at `tie`. Equalities tied so are
            // kept as pairs of opposite rows, which the stages below decide by the same rule.
            let working = std::mem::take(&mut self.working);
            let slots: Vec<usize> = working
                .into_iter()
                .filter(|s| self.es.rows[*s].is_some())
                .collect();
            let next = if slots.is_empty() {
                self.es.least()
            } else {
                Some(Ok(slots))
            };
            self.es.step();
            match next {
                Some(Ok(slots)) => {
                    for s in slots {
                        if let Err(t) = self.equality(s) {
                            self.loosen(&[s], t);
                        }
                    }
                    continue;
                }
                Some(Err((slots, t))) => {
                    if !self.differences(&slots) {
                        self.loosen(&slots, t);
                    }
                    continue;
                }
                None => {}
            }
            if !self.pending.is_empty() {
                self.flush();
                continue;
            }
            let meets = self.sys.meetings();
            if !meets.is_empty() {
                for r in meets {
                    self.es.push(r, &mut self.sys);
                }
                continue;
            }
            // Before the first step that is not an equality, the equalities that cycles of the
            // rows imply are solved like those of the input.
            if !self.cycled {
                self.cycled = true;
                if self.cycles() {
                    continue;
                }
            }
            if self.sys.rows.is_empty() {
                break;
            }
            // Dropping a variable bounded on one side only removes its rows, which leaves every
            // other such variable bounded on one side or not at all, so the variables dropped
            // in the end, and the rows left, are the same in whatever order they are taken.
            if let Some(&j) = self.sys.one_sided.first() {
                let rows = self.sys.take(j);
                self.steps.push(Step::Chosen(j, rows));
                continue;
            }
            if !self.sys.fixable.is_empty() {
                self.fix();
                continue;
            }
            let mut tie: Option<Tied> = None;
            match self.sys.least(&[&self.sys.exact]) {
                Some((fill, _)) if fill > 0 => {}
                Some((_, Ok(js))) => {
                    for j in js {
                        let rows = self.sys.eliminate(j, false);
                        self.steps.push(Step::Chosen(j, rows));
                    }
                    continue;
                }
                Some((_, Err(t))) => tie = Some(t),
                None => {}
            }
            if self.sys.live <= 2 {
                let Some((x, v)) = self.pair() else {
                    return Leaf::Empty;
                };
                if !self.want {
                    return Leaf::Point(Vec::new());
                }
                for (j, v) in x.into_iter().zip(v) {
                    self.sys.take(j);
                    let a = Vec::new().into();
                    self.steps.push(Step::Defined(j, Row { a, k: v }));
                }
                continue;
            }
            if self.sys.wide_rows == 0 {
                // Every elimination is exact, and each adds terms or is tied. The rows are
                // decided, and their point placed, from a potential of their constraint graph
                // (`utvpi::integer_point`): the search `utvpi::integer_empty` makes, then one
                // linear pass, with no elimination. Until UTVPI-model
                // the point was placed by eliminating every variable with fill allowed, which
                // grew the rows (COMPLEXITY.md S38).
                let rows: Vec<(&[Term], &Int)> =
                    self.sys.rows.iter().map(|(a, h)| (&**a, &h.k)).collect();
                let n = self.sys.vars.len();
                if !self.want {
                    return if utvpi::integer_empty(n, &rows) {
                        Leaf::Empty
                    } else {
                        Leaf::Point(Vec::new())
                    };
                }
                let Some(v) = utvpi::integer_point(n, &rows) else {
                    return Leaf::Empty;
                };
                start = v;
                break;
            }
            if tie.is_none() {
                match self.sys.least(&[&self.sys.inexact]) {
                    Some((fill, Ok(js))) if fill <= 0 => {
                        // An empty real shadow, which keeps every integer point, shows the
                        // problem empty; from here on the dark shadow is solved, whose points
                        // are points of the problem, and the splinters of each dark elimination
                        // hold the points it misses.
                        if !self.tested {
                            self.tested = true;
                            if relaxed_empty(&self.sys) {
                                return Leaf::Empty;
                            }
                        }
                        if self.exact3 && self.sys.live == 3 {
                            // A gray shadow inside a splinter, which would leave the question
                            // refused, is decided completely when three variables are left.
                            match self.three() {
                                Some(leaf) => return leaf,
                                None => continue,
                            }
                        }
                        let live = self.sys.live;
                        let mut batch = Vec::with_capacity(js.len());
                        for j in js {
                            batch.push((self.steps.len(), self.sys.vars.len()));
                            let rows = self.sys.eliminate(j, true);
                            self.steps.push(Step::Chosen(j, rows));
                        }
                        self.gray.push((live, batch));
                        continue;
                    }
                    Some((fill, Err(t))) if fill <= 0 => tie = Some(t),
                    _ => {}
                }
            }
            // `Sides::fill` counts every term a pair of rows writes, so an exact elimination
            // can add nothing and still be counted as growing: two opposite rows `l <= a·x <=
            // u` combine to a constant, a lower and an upper row that share other variables
            // with opposite signs cancel them, and a row written may be held already. The
            // variables whose exact elimination adds no terms when so counted are taken next,
            // as `System::least` gives them; when two of least count share a row, none is taken
            // here and the stages below go on, so no name decides.
            if tie.is_none() {
                self.sys.refresh();
                if let Some((_, Ok(js))) = self.sys.least(&[&self.sys.shrinking]) {
                    for j in js {
                        let rows = self.sys.eliminate(j, false);
                        self.steps.push(Step::Chosen(j, rows));
                    }
                    continue;
                }
            }
            // Every elimination left adds terms. Three live variables, with a unit side or
            // not, are decided by `live3` below, after the box. Until HULL3-subsumed a
            // variable with a unit coefficient in every row on one side was first projected
            // out here by the pairs of bounds `hull3::shadow` chose (XT3 B4). That stage was
            // removed on these measurements of `decide` (instructions; load 47 to 57,
            // 2026-11-05). Rows of `stages::three_rows` with
            // coefficients up to a million, summed over 3 seeds, at 64 / 512 / 4,096 rows:
            // 261M / 3,705M / 38,929M with the stage, 203M / 501M / 1,369M without it. The
            // lens of `live3::tangents` over (5000, 5000), at 64 / 256 / 1,024 pairs of
            // planes: 355M / 2,198M / 11,712M with the stage, 941M / 4,092M / 7,163M without
            // it, and in time 66 ms / 1.61 s against about 210 ms / 2.4 s. The stage was at
            // worst 28 times the work of `live3` alone and grew 10 to 14 times per factor 8,
            // while `live3` alone was at worst 2.7 times the work (3.5 times the time) of the
            // stage. With coefficients up to 5, or a pair of rows with no point, the stage
            // never ran.
            //
            // An empty real shadow shows the problem empty whatever was tied.
            if tie.is_some() && !self.tested {
                self.tested = true;
                if relaxed_empty(&self.sys) {
                    return Leaf::Empty;
                }
            }
            // The rows are empty when the box of their bounds shows it, and have a point when
            // one of the five points of the box that `box_point` tries holds them; otherwise
            // three variables left are decided by `live3`, and four or
            // more are refused.
            //
            // Complexity tradeoff: a system over four variables or more that the box neither
            // empties nor satisfies, once
            // no elimination is left that keeps the rows from growing, is given up: it gets
            // `Refusal::Growth` ("not decided", rejected at the function by `run.rs`
            // `linear_questions`), though it may have a point or none. Only five points of the
            // box are tried (nearest zero, lower corner, upper corner, the two midpoints), so a
            // system whose points all lie elsewhere in the box is refused. The box is shown empty
            // only by one pass over the rows (`row_box_empty`): a row below zero over the box, or
            // two rows that bound a variable past each other with the other terms at their
            // largest; a system with no rational point that no such pair shows (the rows of
            // `stages::CROSSING` raised by 1 to 7) is refused, since the resolvents that would
            // find more (cross-review XR3 Q1) were not adopted. Why: an
            // elimination that adds terms multiplies lower by upper bounds, so the rows can grow
            // doubly exponentially in the variables eliminated (Fourier–Motzkin), and the dark
            // and gray shadows of the full Omega test add an exponential search on top; trying
            // every point of the box is exponential in the variables, and the integer points of
            // sparse rows of three variables over 0 and 1 hold 3-SAT. Trigger: four or more live
            // variables, rows not all `±x ± y + k >= 0`, every inexact elimination adding terms
            // as `Sides::fill` counts them, and every exact one adding terms even counted by the
            // rows it writes (`System::shrink`); the size of the system plays no part. Measured
            // in `l01_38_presburger::q1_local` (Q1-LOCAL, 2026-11-08): weighted sliding
            // windows, a band of four, blocks of five chained or as a tree, sums over grid
            // squares and sparse random rows, each with a point, are refused at every size.
            // (Three live variables are decided completely, by `live3` below.) Tests:
            // `l01_38_presburger::omega::each_cause_of_a_refusal_has_its_own_message`,
            // `l01_38_presburger::checker::a_satisfiable_question_with_no_elimination_that_keeps_the_rows_is_refused`,
            // `l01_38_presburger::scaling::the_shifted_sparse_family_scales`,
            // `l01_38_presburger::stages::rows_the_one_pass_test_does_not_show_empty_stay_refused`,
            // `l01_38_presburger::scaling::the_box_stage_with_a_hub_in_one_row_per_block_scales`.
            // COMPLEXITY.md rows S18, Q1-ROWBOX, Q1-LOCAL and Kept "Fourier–Motzkin pairs". A
            // complete solution would run the growing eliminations of the full Omega test (or another
            // complete Presburger procedure) and accept their exponential worst case, or find a
            // structural class of growing systems over four variables or more decidable in
            // O(n log n).
            let Some((lo, hi)) = bounds(&self.sys) else {
                return Leaf::Empty;
            };
            if box_empty_in(&self.sys, &lo, &hi) {
                return Leaf::Empty;
            }
            if let Some(v) = box_point(&self.sys, &lo, &hi) {
                start = v;
                break;
            }
            if self.sys.live <= 3 {
                // `live3` decides three variables completely, so the order of tied ones
                // cannot change its answer.
                match self.three() {
                    Some(leaf) => return leaf,
                    None => continue,
                }
            }
            // Complexity tradeoff: when the next elimination would choose among variables
            // (or equalities, or the variables of an equality) that share a row and that
            // refinement of the rows cannot tell apart, and neither the stages above nor the
            // box decide the rows, the question gets `Refusal::Tie` ("not decided"), though
            // it may have a point or none. Why: which of them goes first changes the rows
            // that follow and so whether a later stage decides them, and nothing but their
            // names would choose; refusing keeps every answer, refusals included, the same
            // under every naming of the variables, while trying every order is exponential
            // in the tied variables and telling them apart for good (canonical labeling of
            // the rows) has no known polynomial algorithm. Trigger: two variables of one
            // color, both of least fill, sharing a row, in a system no other stage decides;
            // the size of the system plays no part. Tests:
            // `l01_38_presburger::names::a_tie_that_shares_a_row_is_refused`,
            // `l01_38_presburger::names::every_naming_gives_one_answer_on_the_regular_family_of_five_103`.
            // COMPLEXITY.md row NAME-ties. A complete solution would search every order of
            // the tied candidates, or decide the rows by a complete method (plan item
            // HULL3-GEN; three live variables are decided by `live3` above).
            return match tie.or_else(|| self.loose_tie.take()) {
                Some(t) => Leaf::Tied(t),
                None => Leaf::Refused(Refusal::Growth),
            };
        }
        if !self.want {
            return Leaf::Point(Vec::new());
        }
        let mut vals = start;
        vals.resize(self.sys.vars.len(), Int::ZERO);
        for step in self.steps.iter().rev() {
            let (j, v) = match step {
                Step::Defined(j, def) => (*j, def.eval(&vals)),
                Step::Chosen(j, rows) => (*j, choose(rows, *j, &vals)),
            };
            vals[j] = v;
        }
        Leaf::Point(vals)
    }

    /// Decides the rows, which hold three variables, by Lenstra's method in dimension three
    /// (`live3`), with no refusal: the answer when it is settled here (empty, or a point
    /// that is not wanted), or `None` once the three variables are defined by a point.
    fn three(&mut self) -> Option<Leaf> {
        let Some((x, v)) = self.triple() else {
            return Some(Leaf::Empty);
        };
        if !self.want {
            return Some(Leaf::Point(Vec::new()));
        }
        for (j, v) in x.into_iter().zip(v) {
            self.sys.take(j);
            let a = Vec::new().into();
            self.steps.push(Step::Defined(j, Row { a, k: v }));
        }
        None
    }

    /// The three live variables and an integer point of the rows over them, or `None` when
    /// the rows have none.
    fn triple(&self) -> Option<([usize; 3], [Int; 3])> {
        let vs: BTreeSet<usize> = self
            .sys
            .rows
            .keys()
            .flat_map(|a| a.iter().map(|(i, _)| *i))
            .collect();
        let vs: [usize; 3] = Vec::from_iter(vs)
            .try_into()
            .unwrap_or_else(|_| unreachable!("three live variables"));
        let rows: Vec<(&[Term], &Int)> = self.sys.rows.iter().map(|(a, h)| (&**a, &h.k)).collect();
        let x = live3::decide(&rows, &vs)?;
        Some((vs, x))
    }

    /// Decides the rows, which hold two variables or fewer: their variables and a point of
    /// them, or `None` when they have no integer point.
    fn pair(&self) -> Option<(Vec<usize>, Vec<Int>)> {
        let mut vs: Vec<usize> = Vec::new();
        for a in self.sys.rows.keys() {
            for (i, _) in a.iter() {
                if !vs.contains(i) {
                    vs.push(*i);
                }
            }
        }
        vs.sort_unstable();
        let rows: Vec<(&[Term], &Int)> = self.sys.rows.iter().map(|(a, h)| (&**a, &h.k)).collect();
        let (x, y) = twovar::point(&rows, vs[0], vs.get(1).copied(), self.want)?;
        Some((vs, vec![x, y]))
    }

    /// The splinter of the dark elimination whose step is at `at`, the system then having
    /// `vars` variables, for its bound `r >= 0` on `x = x[j]` with coefficient `±a` there, and
    /// `m` the largest coefficient of `x`, in magnitude, among the bounds of the other side:
    /// the problem with `r == k` for a fresh `0 <= k <= (a·m - a - m) / m` [Omega, sec. 2.3;
    /// for an upper bound, the same of `-x`], as its rows and the colors of its variables, or
    /// `None` when that range is empty.
    /// It is built from the given rows and the definitions made before the step, so nothing of
    /// this run's state is copied: its points are points of the problem, and it holds the
    /// points of the splinter of the system at the step, each of which extends to one.
    fn splinter(
        &self,
        base: &[(Row, Rel)],
        at: usize,
        vars: usize,
        bound: &Row,
        j: usize,
        m: &Int,
    ) -> Option<Splinter> {
        let a = &bound.at(j).abs();
        let top = (&(&(a * m) - a) - m).div_floor(m);
        if top.is_negative() {
            return None;
        }
        let k = vars;
        let mut rows: Vec<(Row, Rel)> = base.to_vec();
        for step in &self.steps[..at] {
            if let Step::Defined(v, def) = step {
                let a = merge(
                    &def.a,
                    &Int::ONE,
                    &[(*v, Int::ONE)],
                    &-&Int::ONE,
                    usize::MAX,
                );
                rows.push((
                    Row {
                        a,
                        k: def.k.clone(),
                    },
                    Rel::Eq,
                ));
            }
        }
        let a = merge(
            &bound.a,
            &Int::ONE,
            &[(k, Int::ONE)],
            &-&Int::ONE,
            usize::MAX,
        );
        rows.push((
            Row {
                a,
                k: bound.k.clone(),
            },
            Rel::Eq,
        ));
        rows.push((
            Row {
                a: vec![(k, Int::ONE)].into(),
                k: Int::ZERO,
            },
            Rel::Ge,
        ));
        rows.push((
            Row {
                a: vec![(k, -&Int::ONE)].into(),
                k: top,
            },
            Rel::Ge,
        ));
        // The fresh `k` has a color of its own, above every color of the rows.
        let keys: Vec<usize> = self.sys.vars[..vars]
            .iter()
            .map(|v| v.key)
            .chain([usize::MAX])
            .collect();
        Some((rows, keys))
    }

    /// Solves the equality in slot `s`: by the unit coefficient of least color where it has
    /// one, or else by one unimodular step on the variable `y` of least coefficient `b` and of
    /// least color among those: with `q[i]` the nearest integer to `a[i] / b` at each other
    /// `x[i]` and `q` that of `k / b`, `y = t - Σ q[i]·x[i] - q` for a fresh `t` of the color of
    /// `y`. The map is onto the integers, and leaves the symmetric remainder of each `a[i]` by
    /// `b`, so the least coefficient at least halves and every other falls below it in one
    /// step, however large it was. When two variables tie for the choice, the tie, with the
    /// equality, and the equality is left in its slot.
    fn equality(&mut self, s: usize) -> Result<(), Tied> {
        let e = self.es.clear(s, &self.sys);
        let key = |i: usize| self.sys.vars[i].key;
        let units = e.a.iter().any(|(_, c)| c.is_unit());
        // The slot is out of the equalities, so each count is of the others.
        let tied = pivots(&e, &self.sys, |i| self.es.of[i].len());
        // `x - y == d` between two variables of one color, as `Ties` does in `solve`: the
        // greater is defined by the lesser, which is a choice by the values, not the names; when
        // `d` is zero the two are equal at every point, so defining either leaves the same rows
        // with one name for the other.
        let difference = tied.len() == 2 && e.a.len() == 2 && e.a[0].1 == -&e.a[1].1;
        if difference {
            // `c·x0 - c·x1 + k == 0`, so `x0 - x1 == -k·c`.
            let d = -&(&e.k * &e.a[0].1);
            let y = if d.is_negative() { e.a[1].0 } else { e.a[0].0 };
            self.define(y, &e);
            return Ok(());
        }
        if tied.len() > 1 {
            let rows = vec![(e.clone(), Rel::Eq)];
            self.es.put(s, e, &mut self.sys);
            return Err(Tied { vars: tied, rows });
        }
        let y = tied[0];
        if units {
            self.define(y, &e);
            return Ok(());
        }
        let b = &e.at(y).clone();
        let t = self.fresh(key(y));
        let mut a: Vec<Term> =
            e.a.iter()
                .filter(|(i, _)| *i != y)
                .map(|(i, c)| (*i, -&(c - &mod_hat(c, b)).div_floor(b)))
                .filter(|(_, q)| !q.is_zero())
                .collect();
        a.push((t, Int::ONE));
        // The constant is reduced with the rest, so that values do not grow past what the
        // solutions need.
        let def = Row {
            a: a.into(),
            k: -&(&e.k - &mod_hat(&e.k, b)).div_floor(b),
        };
        self.es.put(s, e, &mut self.sys);
        self.es.subst(y, &def, &mut self.sys);
        self.working.push(s);
        self.steps.push(Step::Defined(y, def.clone()));
        self.pending.push((y, def));
        Ok(())
    }

    /// Solves the equalities in `slots` together when each is `x - y == d`, and says whether
    /// it did. Each class of variables they join is written over one member, the member of least
    /// color, then of least value, then of least place, as [`Ties::representatives`] chooses,
    /// so the order of the equalities plays no part; two members of one color and one value
    /// are equal at every point, so taking either leaves the same rows with one name for the
    /// other. O(e log e) for e equalities.
    fn differences(&mut self, slots: &[usize]) -> bool {
        let is_difference =
            |r: &Row| r.a.len() == 2 && r.a[0].1.is_unit() && r.a[0].1 == -&r.a[1].1;
        if !slots.iter().all(|s| {
            self.es.rows[*s]
                .as_ref()
                .is_some_and(|h| is_difference(&h.row))
        }) {
            return false;
        }
        let rows: Vec<Row> = slots.iter().map(|s| self.es.clear(*s, &self.sys)).collect();
        let vars: Vec<usize> = rows
            .iter()
            .flat_map(|r| r.a.iter().map(|(i, _)| *i))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let local = |i: usize| vars.binary_search(&i).expect("a variable of the rows");
        let mut ties = Ties::new(vars.len());
        for r in &rows {
            // `c·x - c·y + k == 0`, so `x - y == -k·c`.
            let d = -&(&r.k * &r.a[0].1);
            if !ties.equate(local(r.a[0].0), local(r.a[1].0), d) {
                self.sys.empty = true;
                return true;
            }
        }
        let keys: Vec<usize> = vars.iter().map(|&i| self.sys.vars[i].key).collect();
        for (l, (rep, d)) in ties.representatives(&keys).into_iter().enumerate() {
            if rep != l {
                // `x - rep - d == 0`.
                let e = Row {
                    a: merge(
                        &[(vars[l], Int::ONE)],
                        &Int::ONE,
                        &[(vars[rep], -&Int::ONE)],
                        &Int::ONE,
                        usize::MAX,
                    ),
                    k: -&d,
                };
                self.define(vars[l], &e);
            }
        }
        true
    }

    /// Turns into equalities the rows that a cycle of rows forces to hold with `==`, and says
    /// whether it found any, or found the rows empty. A row `x - y + k >= 0` with `k <= 0`
    /// says `x >= y + w` with `w = -k >= 0`: an edge `y → x` of weight `w` in a graph over
    /// the variables and a node for zero, which the rows `x + k >= 0` (`x >= w`, an edge from
    /// zero) and `-x + k >= 0` (`0 >= x + w`, an edge to zero) join. Every edge within a
    /// strongly connected component lies on a cycle, along which the variables only rise,
    /// each by at least its edge's weight, and come back to where they began; so an edge
    /// of weight above zero there leaves no point, and every other holds with `==`. The
    /// variables of a cycle of rows `x - y >= 0` are thus all equal, and so are two rows
    /// `x - y >= 0` and `y - x >= 0`. The edges are chosen by the rows alone, so no name plays
    /// a part. O(m log m + n) for m rows over n variables, by Tarjan's algorithm
    /// ([`utvpi::components`]).
    ///
    /// Complexity tradeoff: two kinds of implied equality are not found here. A cycle whose
    /// weights have both signs and sum to zero (`x - y + 1 >= 0`, `y - z - 1 >= 0`,
    /// `z - x >= 0`) needs a potential of the whole graph, a shortest-path search with
    /// negative weights; and a cycle that only forms after the definitions this search starts,
    /// or after an elimination, would need the search again after every step, O(m) each, so
    /// O(m·n) over a run. The search runs once, before the first step that is not an
    /// equality. A system that has only such cycles goes on to the stages below as before, and
    /// may be refused with `Refusal::Growth` though its cycles decide it. Trigger: a zero-sum
    /// cycle of difference rows with a weight below zero on it, or one closed by a step; the
    /// size of the system plays no part. Tests:
    /// `l01_38_presburger::omega::a_cycle_of_rows_makes_its_variables_equal` and
    /// `l01_38_presburger::scaling::a_cycle_of_rows_scales`. COMPLEXITY.md row
    /// OMEGA-cycle-growth. A complete solution would find a potential with
    /// [`utvpi::integer_empty`]'s search, take the zero-weight cycles among its tight edges,
    /// and keep the components up to date as steps add rows (incremental strongly connected
    /// components).
    fn cycles(&mut self) -> bool {
        // The node of `x[j]` is `j + 1`, and zero is node 0.
        let mut out: Vec<Vec<usize>> = vec![Vec::new(); self.sys.vars.len() + 1];
        let mut edges: Vec<(usize, usize, usize, bool)> = Vec::new();
        for (a, held) in &self.sys.rows {
            if held.k.is_positive() || a.iter().any(|(_, c)| !c.is_unit()) {
                continue;
            }
            let node = |(i, _): &Term| i + 1;
            let (from, to) = match &a[..] {
                [t] if t.1.is_positive() => (0, node(t)),
                [t] => (node(t), 0),
                [s, t] if s.1 == -&t.1 && s.1.is_positive() => (node(t), node(s)),
                [s, t] if s.1 == -&t.1 => (node(s), node(t)),
                _ => continue,
            };
            out[from].push(to);
            edges.push((from, to, held.id, held.k.is_zero()));
        }
        let comp = utvpi::components(&out, |v| *v);
        let mut tight: Vec<usize> = Vec::new();
        for (from, to, id, zero) in edges {
            if comp[from] != comp[to] {
                continue;
            }
            if !zero {
                self.sys.empty = true;
                return true;
            }
            tight.push(id);
        }
        let found = !tight.is_empty();
        for id in tight {
            let r = self.sys.remove(id);
            self.es.push(r, &mut self.sys);
        }
        found
    }

    /// Keeps the equalities in `slots`, which tie as `t` says, as pairs of opposite rows. Each
    /// slot is cleared, and no equality takes its place: equalities are formed only from the
    /// input and from rows that meet ([`System::meetings`]), and rows whose coefficients are
    /// kept in `loose` are not formed again, so the loop ends. An equality whose rows were
    /// kept before adds them again, which changes nothing, and the loop goes on to the stages
    /// below as after any tie kept so; the stages after the eliminations decide what they can
    /// and the first tie is kept for the refusal. Each pair holds the points of its equality,
    /// so the rows mean what they did, and the set of slots is chosen by structure, so no
    /// order among them plays a part. O(e log m) for e equalities over m rows.
    fn loosen(&mut self, slots: &[usize], t: Tied) {
        self.loose_tie.get_or_insert(t);
        for &s in slots {
            if self.es.rows[s].is_none() {
                continue;
            }
            let r = self.es.clear(s, &self.sys);
            let opp: Coefs = opposite(&r.a).into();
            let lesser = if r.a < opp { r.a.clone() } else { opp.clone() };
            self.sys.loose.insert(lesser);
            let k = -&r.k;
            self.sys.add(r);
            self.sys.add(Row { a: opp, k });
        }
    }

    /// A fresh variable of the color `key`.
    fn fresh(&mut self, key: usize) -> usize {
        self.sys.vars.push(Var {
            key,
            ..Var::default()
        });
        self.es.grow();
        self.sys.vars.len() - 1
    }

    /// Replaces `x[j]` everywhere by what the equality `e`, whose coefficient there is a unit,
    /// makes it.
    fn define(&mut self, j: usize, e: &Row) {
        // `aj·x + rest == 0`, so `x = -aj·rest`.
        let f = -e.at(j);
        let def = Row {
            a: merge(&e.a, &f, &[], &Int::ZERO, j),
            k: &e.k * &f,
        };
        self.es.subst(j, &def, &mut self.sys);
        self.steps.push(Step::Defined(j, def.clone()));
        self.pending.push((j, def));
    }

    /// Fixes each variable every row but its bounds pulls to one bound, at that bound: a point
    /// with the variable elsewhere between its bounds stays a point when it moves there, so
    /// this keeps every answer, and it holds of several variables at once.
    fn fix(&mut self) {
        for j in std::mem::take(&mut self.sys.fixable) {
            let (lo, hi) = (self.sys.bound(j, false), self.sys.bound(j, true));
            let s = &self.sys.vars[j].sides;
            let v = match (s.lo == s.lo_unary, s.hi == s.hi_unary, lo, hi) {
                // Only bounds: the value nearest zero.
                (true, true, Some(l), Some(h)) => l.max(Int::ZERO).min(h),
                (true, _, Some(l), _) => l,
                (_, _, _, Some(h)) => h,
                _ => unreachable!("a fixable variable has the bound"),
            };
            let def = Row {
                a: Vec::new().into(),
                k: v,
            };
            self.steps.push(Step::Defined(j, def.clone()));
            self.pending.push((j, def));
        }
    }

    /// Writes the pending definitions into the inequalities, each row once. A definition holds
    /// only variables defined after it, or none, so each is resolved from the last back.
    fn flush(&mut self) {
        let defs = std::mem::take(&mut self.pending);
        let at: HashMap<usize, usize> =
            defs.iter().enumerate().map(|(p, (j, _))| (*j, p)).collect();
        let mut rows = Vec::new();
        for (j, _) in &defs {
            rows.extend(self.sys.take(*j));
        }
        for r in rows {
            let r = resolve(&r, &defs, &at);
            self.sys.add(r);
        }
    }
}

/// `r` with each variable that `defs` defines replaced by its definition, and the variables
/// of that definition defined in turn, until no defined variable is left; `at` gives the place
/// in `defs` of each variable defined. A definition holds only variables defined after it, so
/// the defined variables are taken in the order of their places: when one is taken, every
/// variable whose definition holds it has been replaced, and its coefficient is final. A
/// coefficient that sums to zero ends that path, so `o[n] - o[n-5]` along a chain of
/// definitions `o[i+1] = o[i] + l[i]` takes five definitions, not n.
///
/// Until Q1-LOCAL each definition was first resolved in full, from the last back, and each row
/// then took the resolved forms of its variables: along a chain of n definitions the resolved
/// forms have 1, 2, ..., n terms, O(n^2) however few rows held the chain
/// (`q1_local::growth_of_offsets_laid_end_to_end`: 4.0 times the terms per doubling).
///
/// Complexity tradeoff: a row costs O(w log w) for the w definitions it reaches with a
/// nonzero coefficient, which can exceed the terms it ends with when they cancel late: m rows
/// that each reach the whole of a chain of n definitions and cancel most of it cost O(m n).
/// Why: the coefficients are known only once the definitions are expanded, and no sum of a
/// chain is kept to subtract. Trigger: many rows that each hold a variable at the end of a
/// long chain of definitions and also terms that cancel the chain; the size of the system
/// alone plays no part. Rows that end as long as the definitions they reach cost what writing
/// them costs. A complete solution would keep the definitions of a chain as prefix sums, so
/// that a difference of two of them is read in O(log n).
fn resolve(r: &Row, defs: &[(usize, Row)], at: &HashMap<usize, usize>) -> Row {
    let mut sum: BTreeMap<usize, Int> = BTreeMap::new();
    let mut open: BTreeMap<usize, Int> = BTreeMap::new();
    let mut k = r.k.clone();
    let mut put = |v: usize, c: Int, open: &mut BTreeMap<usize, Int>| {
        let into = match at.get(&v) {
            Some(p) => open.entry(*p),
            None => sum.entry(v),
        };
        let held = into.or_insert(Int::ZERO);
        *held = &*held + &c;
    };
    for (v, c) in r.a.iter() {
        put(*v, c.clone(), &mut open);
    }
    while let Some((p, c)) = open.pop_first() {
        if c.is_zero() {
            continue;
        }
        let d = &defs[p].1;
        k = &k + &(&c * &d.k);
        for (w, e) in d.a.iter() {
            put(*w, &c * e, &mut open);
        }
    }
    Row {
        a: sum.into_iter().filter(|(_, c)| !c.is_zero()).collect(),
        k,
    }
}

/// The value nearest zero for `x[j]` that the rows allow at the values `m` of the variables
/// chosen after it, `m[j]` being zero still.
fn choose(rows: &[Row], j: usize, m: &[Int]) -> Int {
    let (mut lo, mut hi) = (None::<Int>, None::<Int>);
    for r in rows {
        let c = r.at(j);
        let rest = r.eval(m);
        // `c·x + rest >= 0`.
        if c.is_positive() {
            let b = -&rest.div_floor(c);
            lo = Some(lo.map_or(b.clone(), |l| l.max(b)));
        } else {
            let b = rest.div_floor(&-c);
            hi = Some(hi.map_or(b.clone(), |h| h.min(b)));
        }
    }
    match (lo, hi) {
        (Some(l), _) if l.is_positive() => l,
        (_, Some(h)) if h.is_negative() => h,
        _ => Int::ZERO,
    }
}

/// The values of a symbol over the formula's points, as a union of intervals (see the module
/// note): exact when one disjunction is left, a set holding them otherwise. A bound past `i64`
/// is read as no bound.
///
/// Complexity tradeoff: with two or more disjunctions the answer is the meet of each
/// disjunction's union of projections, with its two ends moved in by `tighten`; the gaps
/// that only a combination of disjuncts shows are given up, so the set can hold values no
/// point takes. Why: the exact projection is the union over every combination of one disjunct
/// per disjunction, which is exponential in the disjunctions. Trigger: more than one
/// disjunction left after propagation. Test:
/// `l01_38_presburger::random::random_tests_agree_with_the_interpreter` (every projection
/// holds every value; one of 60 is wider than the hull). COMPLEXITY.md rows S7 and S16. A
/// complete solution would project each combination of disjuncts, or a decision diagram over
/// the disjuncts, at a cost exponential in the worst case.
pub fn project(f: &Formula, sym: &Atom) -> Result<IntervalSet, Refusal> {
    project_each(f, std::slice::from_ref(sym))?.0.remove(0)
}

/// The projections of [`project_each`], one for each symbol, and the causes for which a
/// disjunction was left out of them.
pub type Each = (Vec<Result<IntervalSet, Refusal>>, Vec<Refusal>);

/// [`project`] onto each of `syms`, removing disjuncts once: one result for each symbol, so
/// that a symbol whose hull is refused leaves the others projected. With them, the causes for
/// which a disjunction was left out, which leaves each hull wider but sound.
///
/// Whatever way an equal formula is written, the answer is the same: `f` is asked written one
/// way (`signed`), and where that is refused, with each equation held with both signs.
// Complexity tradeoff: a question refused in the first writing costs a second question of the
// same size. Why: the solver chooses its order of elimination by the signs of the rows, so
// which systems it refuses depends on them, and no check before the question tells which
// writing it answers; asking both every time would double every question. Trigger: a question
// the solver refuses with each equation in the sign of [`equation`]. Test:
// `l01_39_reduced_product::pendants::refused_parts_projected_exactly_by_pendants_fourth_quarter_rest`.
// COMPLEXITY.md row PROJECT-each-canon.
pub fn project_each(f: &Formula, syms: &[Atom]) -> Result<Each, Refusal> {
    // The formula with each shared part taken out of the disjunctions that hold it in every
    // disjunct ([`factored`]) is asked first, and the formula as written where that leaves
    // anything refused, so no refusal or cause appears that the formula as written does not
    // give.
    if let Some(g) = factored(f) {
        let r = project_each_written(&g, syms);
        if matches!(&r, Ok(each) if !refused(each)) {
            return r;
        }
    }
    project_each_written(f, syms)
}

/// [`project_each`] of `f` as it is written, with no part taken out of its disjunctions.
fn project_each_written(f: &Formula, syms: &[Atom]) -> Result<Each, Refusal> {
    let first = project_each_signed(&signed(f, false), syms);
    if matches!(&first, Ok(each) if !refused(each)) {
        return first;
    }
    // The second writing where the first is refused; where both
    // refuse something, the meet of the two (each sound, so the meet is), with the causes the
    // first gives.
    match (first, project_each_signed(&signed(f, true), syms)) {
        (_, Ok(other)) if !refused(&other) => Ok(other),
        (Ok((mut each, skipped)), Ok((others, _))) => {
            meet_each(&mut each, others);
            Ok((each, skipped))
        }
        (Ok(each), Err(_)) => Ok(each),
        (Err(_), Ok(other)) => Ok(other),
        (Err(e), Err(_)) => Err(e),
    }
}

/// Each of `each` met with the same symbol's projection in `others`, both sound: a refused
/// symbol takes the other, every other the meet of the two.
fn meet_each(each: &mut [Result<IntervalSet, Refusal>], others: Vec<Result<IntervalSet, Refusal>>) {
    for (s, o) in each.iter_mut().zip(others) {
        match (&*s, o) {
            (Ok(n), Ok(o)) => *s = Ok(n.meet(&o)),
            (Err(_), o) => *s = o,
            (Ok(_), Err(_)) => {}
        }
    }
}

/// Whether `each` refuses a symbol or leaves a disjunction out.
fn refused(each: &Each) -> bool {
    !each.1.is_empty() || each.0.iter().any(Result::is_err)
}

thread_local! {
    /// Whether [`factored`] takes no part out, so that [`project_each`] and [`decide`] ask
    /// every formula as it is written: for the tests that compare the two (ST-formula-sibling).
    pub static UNFACTORED: Cell<bool> = const { Cell::new(false) };
}

/// `f` with each shared part `u` that every disjunct of a disjunction holds as a conjunct
/// taken out of the disjunction, `(u && r1) || (u && r2)` as `u && (r1 || r2)`, which holds at
/// the same points; `None` when no part is taken out. Only the disjunctions reached from the
/// root through conjunctions and negations are read, and a part is taken out only when no
/// atom of it is linked, through the constraints of `f` (an atom of a product linked with its
/// factors), to an atom of the rest of a disjunct. The part then forms a group of its own in
/// the projection, read once, and not again with each disjunct: the projection of the result
/// is that of the formula as written or within it, never wider (of 20000 random formulas, 53
/// within it, where reading the part with each disjunct lost a bound, and none wider).
/// [`project_each`] and [`decide`] still ask the formula as written where the result leaves
/// anything refused, so no refusal or cause appears that the formula as written does not
/// give. A formula with an auxiliary variable, linked through definitions that are not among
/// its constraints, is left as it is.
// Complexity tradeoff: naive version, the formula as written: each of d disjuncts holds the
// shared part's k constraints, and the projection reads them in each disjunct (`Parts::of`,
// `project_parts`), O(d k) time and memory, quadratic in the program when k is about d (k
// named limits at each of d side-by-side tiers: 55.9 times the instructions and 46.6 times the
// bytes from d = 30 to 240). Used: one walk with a visited set to link the atoms, one look at
// each disjunct's parts by key, and the shared part read once, O(n log n) for a formula of n
// distinct parts; the check reads each disjunction on the spine once, as the projection that
// follows does. A part linked to the rest of a disjunct is not taken out, since there the
// projection of the result can differ from that of the formula as written (a coarser set, as
// `[..=0,5..]` to `[..]`), and such a disjunction still costs O(d k). Trigger: a disjunction
// every disjunct of which holds one shared part over atoms of its own. Tests:
// `l01_39_reduced_product::named_test::arms_of_named_limits_in_side_by_side_tiers_take_time_near_linear_in_the_depth`,
// `l01_38_presburger::shared::taking_a_shared_part_out_of_a_disjunction_loses_no_precision`.
// COMPLEXITY.md S31b.
fn factored(f: &Formula) -> Option<Formula> {
    if matches!(f, Formula::Con(_)) || UNFACTORED.with(Cell::get) {
        return None;
    }
    let links = AtomLinks::of(f)?;
    // Each compound part on the spine, its key mapped to the part rewritten, or `None` when
    // unchanged; each part is entered once, after its parts on the spine.
    let mut done: HashMap<Id, Option<Formula>> = HashMap::new();
    let mut seen: HashSet<Id> = HashSet::new();
    let mut stack: Vec<(&Formula, bool)> = vec![(f, false)];
    while let Some((g, leave)) = stack.pop() {
        let id = Id::any(g);
        if leave {
            let new = |k: &Formula| match k {
                Formula::Con(_) => None,
                _ => done[&Id::any(k)].clone(),
            };
            let out = (g.kids().iter().any(|k| new(k).is_some())).then(|| {
                g.rebuild(
                    (g.kids().iter())
                        .map(|k| new(k).unwrap_or_else(|| k.clone()))
                        .collect(),
                )
            });
            done.insert(id, out);
            continue;
        }
        if !seen.insert(id) {
            continue;
        }
        match g {
            Formula::Con(_) => unreachable!("a constraint is not pushed"),
            Formula::Or(_) => {
                done.insert(id, factored_or(g, &links));
            }
            Formula::Not(_) | Formula::And(_) => {
                stack.push((g, true));
                let compound = g.kids().iter().filter(|k| !matches!(k, Formula::Con(_)));
                stack.extend(compound.map(|k| (k, false)));
            }
        }
    }
    done.remove(&Id::any(f)).flatten()
}

/// The disjunction `g` with the compound parts every disjunct holds as conjuncts taken out
/// ([`factored`]), or `None` when there are none or one is linked to the rest of a disjunct.
fn factored_or(g: &Formula, links: &AtomLinks) -> Option<Formula> {
    let ds = g.kids();
    if ds.len() < 2 {
        return None;
    }
    fn parts(d: &Formula) -> Option<impl Iterator<Item = &Formula>> {
        match d {
            Formula::And(ps) => Some(ps.iter().filter(|p| !matches!(p, Formula::Con(_)))),
            _ => None,
        }
    }
    let mut common: Vec<&Formula> = Vec::new();
    let mut ids: HashSet<Id> = HashSet::new();
    for p in parts(&ds[0])? {
        if ids.insert(Id::any(p)) {
            common.push(p);
        }
    }
    for d in &ds[1..] {
        let here: HashSet<Id> = parts(d)?.map(Id::any).collect();
        common.retain(|p| here.contains(&Id::any(p)));
        if common.is_empty() {
            return None;
        }
    }
    let ids: HashSet<Id> = common.iter().map(|p| Id::any(p)).collect();
    let rests: Vec<Formula> = (ds.iter())
        .map(|d| {
            let rest: Vec<&Formula> = (d.kids().iter())
                .filter(|p| matches!(p, Formula::Con(_)) || !ids.contains(&Id::any(p)))
                .collect();
            let keep: Vec<bool> = rest.iter().map(|p| matches!(p, Formula::And(_))).collect();
            Formula::and_keeping(rest.into_iter().cloned().collect(), |i| keep[i])
        })
        .collect();
    let rest = Formula::or(rests);
    let mut groups: HashSet<usize> = HashSet::new();
    for p in &common {
        p.walk(&mut |c| groups.extend(c.lin.terms.keys().map(|a| links.group(a))));
    }
    let mut linked = false;
    rest.walk(&mut |c| linked |= c.lin.terms.keys().any(|a| groups.contains(&links.group(a))));
    if linked {
        return None;
    }
    let mut out: Vec<Formula> = common.into_iter().cloned().collect();
    let keep: Vec<bool> = out.iter().map(|p| matches!(p, Formula::And(_))).collect();
    out.push(rest);
    Some(Formula::and_keeping(out, |i| {
        keep.get(i).copied().unwrap_or(false)
    }))
}

/// The atoms of a formula grouped by the constraints that link them ([`factored`]), an atom
/// of a product linked with its factors; a group is found in near-constant time.
struct AtomLinks {
    ids: HashMap<Atom, usize>,
    parent: Vec<usize>,
    /// At each root, the number of atoms in its group.
    size: Vec<usize>,
}

impl AtomLinks {
    /// The groups of the atoms of `f`'s constraints, or `None` when `f` has an auxiliary
    /// variable.
    fn of(f: &Formula) -> Option<AtomLinks> {
        let mut l = AtomLinks {
            ids: HashMap::new(),
            parent: Vec::new(),
            size: Vec::new(),
        };
        let mut aux = false;
        f.walk(&mut |c| {
            let mut first: Option<usize> = None;
            for a in c.lin.terms.keys() {
                let mut join = |l: &mut AtomLinks, b: &Atom| {
                    let i = l.id(b);
                    match first {
                        Some(r) => l.union(r, i),
                        None => first = Some(i),
                    }
                };
                match a {
                    Atom::Aux(_) => aux = true,
                    Atom::Product(x, y) => {
                        aux |= matches!(x, Factor::Aux(_)) || matches!(y, Factor::Aux(_));
                        join(&mut l, &x.atom());
                        join(&mut l, &y.atom());
                    }
                    Atom::Sym(_) => {}
                }
                join(&mut l, a);
            }
        });
        (!aux).then_some(l)
    }

    fn id(&mut self, a: &Atom) -> usize {
        if let Some(&i) = self.ids.get(a) {
            return i;
        }
        let i = self.parent.len();
        self.ids.insert(a.clone(), i);
        self.parent.push(i);
        self.size.push(1);
        i
    }

    /// The root of `i`, with the path to it halved.
    fn root_mut(&mut self, mut i: usize) -> usize {
        while self.parent[i] != i {
            self.parent[i] = self.parent[self.parent[i]];
            i = self.parent[i];
        }
        i
    }

    /// Joins the groups of `a` and `b`, the smaller into the larger, so a root is found in
    /// `log` steps.
    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.root_mut(a), self.root_mut(b));
        if ra != rb {
            let (big, small) = if self.size[ra] < self.size[rb] {
                (rb, ra)
            } else {
                (ra, rb)
            };
            self.parent[small] = big;
            self.size[big] += self.size[small];
        }
    }

    /// The group of the atom `a`, which is one of the atoms the groups were made of.
    fn group(&self, a: &Atom) -> usize {
        let mut i = self.ids[a];
        while self.parent[i] != i {
            i = self.parent[i];
        }
        i
    }
}

/// [`project_each`] of `f` written one way ([`signed`]).
fn project_each_signed(f: &Formula, syms: &[Atom]) -> Result<Each, Refusal> {
    // Where the new path refuses a symbol or leaves a disjunction out, the old path is asked
    // too ([`or_old`]): a refused symbol takes the old hull, every other the meet of the two
    // (each sound, so the meet is), and the causes given are the old path's, so that no
    // refusal or cause appears where the old path had none.
    let new = or_old(|| project_each_named(f, syms));
    match new {
        Ok(mut each) if refused(&each) && !old_path() => {
            OLD_PATH.with(|o| o.set(true));
            let old = project_each_named(f, syms);
            OLD_PATH.with(|o| o.set(false));
            if let Ok((olds, skipped)) = old {
                meet_each(&mut each.0, olds);
                each.1 = skipped;
            }
            Ok(each)
        }
        r => r,
    }
}

/// [`project_each`] on one path ([`or_old`]).
fn project_each_named(f: &Formula, syms: &[Atom]) -> Result<Each, Refusal> {
    let r = match Renamed::of(f) {
        Naming::Kept => return project_each_inner(f, syms),
        Naming::Renamed(r) => r,
        // Projected with each disjunction kept, by questions that no order of the parts
        // changes ([`project_parts`] with `sets`).
        Naming::Tied(..) => {
            return match settle_as_sets(absorbed(f, syms).0)? {
                None => Ok(no_points(syms)),
                // A projection may keep a disjunct not shown to have a point.
                Some(AsSets { p, .. }) => {
                    project_parts(p, syms, Some(f), true, &mut HashMap::new())
                }
            };
        }
    };
    let there: Vec<Atom> = syms.iter().map(|s| r.there(s)).collect();
    let (each, skipped) = project_each_inner(&r.f, &there).map_err(|e| r.back_refusal(e))?;
    Ok((
        each.into_iter()
            .map(|s| s.map_err(|e| r.back_refusal(e)))
            .collect(),
        skipped.into_iter().map(|e| r.back_refusal(e)).collect(),
    ))
}

/// [`project_each`] of a formula whose names no longer matter ([`Renamed`]).
fn project_each_inner(f: &Formula, syms: &[Atom]) -> Result<Each, Refusal> {
    match settle(absorbed(f, syms).0, false)? {
        Some(p) => project_parts(p, syms, Some(f), false, &mut HashMap::new()),
        None => Ok(no_points(syms)),
    }
}

/// [`project_each`] with a set for every symbol, for a caller that narrows by the
/// projection: where the solver refuses the question or the projection onto a symbol, the
/// symbol keeps the bounds the box stage gives the rows of the formula ([`row_box`]), which
/// hold every value it takes at a point of the formula.
#[derive(Clone, PartialEq, Debug)]
pub struct Boxed {
    /// Each symbol's set: its projection, or where it was refused, the box stage's bounds
    /// and the cause.
    pub each: Vec<(IntervalSet, Option<Refusal>)>,
    /// The causes for which a disjunction was left out of the projections.
    pub skipped: Vec<Refusal>,
    /// The cause for which the whole question was refused, when it was; every symbol then
    /// keeps the box stage's bounds.
    pub whole: Option<Refusal>,
}

impl Boxed {
    /// The first cause for which a set is wider than the projection: of the whole question,
    /// then of the first refused symbol, then of the first disjunction left out.
    pub fn cause(&self) -> Option<Refusal> {
        (self.whole.clone())
            .or_else(|| self.each.iter().find_map(|(_, r)| r.clone()))
            .or_else(|| self.skipped.first().cloned())
    }
}

/// [`project_each`], each refused symbol, or every symbol when the whole question is refused,
/// given the bounds of [`row_box`] in place of its projection ([`Boxed`]).
///
/// Complexity tradeoff: a projection the solver refuses (`Refusal::Growth` and the other
/// causes of [`Refusal`], see `Omega::run`) keeps only the box stage's bounds: each row with
/// one term bounds its atom, and each wider row tightens each of its atoms once from the
/// bounds of the others, so the set can be wider than the projection (seed 17 case 272 of
/// `l01_39_reduced_product::pendants::WRITTEN`: `z1` in [-7, 13] where the projection is
/// [-7, 6]). Why: the exact projection of rows the solver refuses is an integer program over
/// four variables or more, and propagating the bounds to their fixed point can take a number
/// of rounds that grows with the constants, not the rows. Trigger: a question or a symbol the
/// solver refuses. Tests: `l01_39_reduced_product::pendants::parts_once_answered_by_how_they_were_written_give_one_answer`,
/// `l01_39_reduced_product::pendants::refused_projections_keep_the_box_of_their_rows`,
/// `l01_38_presburger::omega::the_box_of_refused_rows_scales`. COMPLEXITY.md row
/// PROJECT-growth-box. A complete solution would decide the integer program (see
/// `Omega::run`).
pub fn project_each_boxed(f: &Formula, syms: &[Atom]) -> Boxed {
    let (each, skipped, whole) = match project_each(f, syms) {
        Ok((each, skipped)) => (each, skipped, None),
        Err(e) => (
            syms.iter().map(|_| Err(e.clone())).collect(),
            Vec::new(),
            Some(e),
        ),
    };
    let mut boxed: Option<Vec<IntervalSet>> = None;
    let each = (each.into_iter().enumerate())
        .map(|(k, r)| match r {
            Ok(s) => (s, None),
            Err(e) => {
                let b = boxed.get_or_insert_with(|| row_box(f, syms));
                (b[k].clone(), Some(e))
            }
        })
        .collect();
    Boxed {
        each,
        skipped,
        whole,
    }
}

/// The bounds the box stage of the Omega test (`tightened`) gives each of `syms` over the
/// rows of `f`'s conjunction: each row with one term bounds its atom, as does each
/// disjunction every disjunct of which bounds the atom (by their hull), and each wider row
/// then tightens each of its atoms once from the bounds of the others, all rows at the same
/// time. Other disjunctions and negations are not read, so each set holds every value the
/// symbol takes at a point of `f`; every set is empty when the bounds show that `f` has no
/// point. Each row is divided by the gcd of its coefficients and an equation is read as its
/// two rows, so no order, sign, factor or repetition of the rows, and no name, changes the
/// answer. O(T log T) for the T terms of `f`.
pub fn row_box(f: &Formula, syms: &[Atom]) -> Vec<IntervalSet> {
    let empty = || syms.iter().map(|_| IntervalSet::empty()).collect();
    let mut index: HashMap<&Atom, usize> = HashMap::new();
    let mut lo: Vec<Option<Int>> = Vec::new();
    let mut hi: Vec<Option<Int>> = Vec::new();
    let mut wide: Vec<Row> = Vec::new();
    let mut ors: Vec<&[Formula]> = Vec::new();
    // Raises the lower bound `b` to `v`, or with `upper` lowers the upper bound `b` to `v`.
    fn raise(b: &mut Option<Int>, v: Int, upper: bool) {
        if b.as_ref().is_none_or(|o| (v < *o) == upper) {
            *b = Some(v);
        }
    }
    let mut stack: Vec<&Formula> = vec![f];
    while let Some(g) = stack.pop() {
        match g {
            Formula::And(cs) => stack.extend(cs.iter()),
            Formula::Or(ds) if ds.is_empty() => return empty(),
            Formula::Or(ds) => ors.push(&ds[..]),
            Formula::Not(_) => {}
            Formula::Con(c) => {
                let mut a: Vec<Term> = (c.lin.terms.iter())
                    .map(|(x, v)| {
                        let n = index.len();
                        let j = *index.entry(x).or_insert(n);
                        if j == n {
                            lo.push(None);
                            hi.push(None);
                        }
                        (j, v.clone())
                    })
                    .collect();
                a.sort_unstable_by_key(|(j, _)| *j);
                let row = Row {
                    a: a.into(),
                    k: c.lin.constant.clone(),
                };
                let eq = c.rel == Rel::Eq;
                let rows = match row.normal(eq) {
                    Norm::False => return empty(),
                    Norm::True => continue,
                    Norm::Row(r) if eq => {
                        let back = Row {
                            a: opposite(&r.a).into(),
                            k: -&r.k,
                        };
                        vec![r, back]
                    }
                    Norm::Row(r) => vec![r],
                };
                for r in rows {
                    match &r.a[..] {
                        // `x + k >= 0` or `-x + k >= 0`, the coefficient one after the
                        // division by the gcd.
                        [(j, c)] if c.is_positive() => raise(&mut lo[*j], -&r.k, false),
                        [(j, _)] => raise(&mut hi[*j], r.k, true),
                        _ => wide.push(r),
                    }
                }
            }
        }
    }
    // A disjunction bounds the atoms that every disjunct with a point bounds by its rows of
    // one term, by the hull of those bounds.
    for ds in ors {
        let mut hull: Option<OneTerm<'_>> = None;
        for d in ds {
            let Some(own) = one_term_bounds(d) else {
                continue;
            };
            hull = Some(match hull {
                None => own,
                Some(h) => (h.into_iter())
                    .filter_map(|(x, (l, u))| {
                        let (l2, u2) = own.get(x)?;
                        let l = l.zip(l2.clone()).map(|(p, q)| p.min(q));
                        let u = u.zip(u2.clone()).map(|(p, q)| p.max(q));
                        (l.is_some() || u.is_some()).then_some((x, (l, u)))
                    })
                    .collect(),
            });
        }
        let Some(hull) = hull else {
            return empty();
        };
        for (x, (l, u)) in hull {
            let n = index.len();
            let j = *index.entry(x).or_insert(n);
            if j == n {
                lo.push(None);
                hi.push(None);
            }
            if let Some(l) = l {
                raise(&mut lo[j], l, false);
            }
            if let Some(u) = u {
                raise(&mut hi[j], u, true);
            }
        }
    }
    let Some((lo, hi)) = tightened(lo, hi, wide.iter().map(|r| (&*r.a, &r.k))) else {
        return empty();
    };
    let end = |v: &Option<Int>, inf: End| v.as_ref().map_or(inf, |v| End::Fin(Num::from(v)));
    syms.iter()
        .map(|s| match index.get(s) {
            Some(&j) => IntervalSet::range(end(&lo[j], End::NegInf), end(&hi[j], End::PosInf)),
            None => IntervalSet::top(),
        })
        .collect()
}

/// The bounds that one-term rows give each atom, lower and upper.
type OneTerm<'a> = HashMap<&'a Atom, (Option<Int>, Option<Int>)>;

/// The bounds that the rows of one term of the conjunction `d` give each of their atoms,
/// `None` when one of them, or a lower bound above an upper one, shows `d` has no point. A
/// disjunction within `d` is not read.
fn one_term_bounds(d: &Formula) -> Option<OneTerm<'_>> {
    let mut out: HashMap<&Atom, (Option<Int>, Option<Int>)> = HashMap::new();
    let mut stack = vec![d];
    while let Some(g) = stack.pop() {
        match g {
            Formula::And(cs) => stack.extend(cs.iter()),
            Formula::Or(ds) if ds.is_empty() => return None,
            Formula::Con(c) if c.lin.terms.len() == 1 => {
                let (x, a) = c.lin.terms.iter().next().expect("one term");
                let (l, u) = int_bounds([(a.clone(), c.lin.constant.clone(), c.rel)])?;
                let e = out.entry(x).or_insert((None, None));
                if let Some(l) = l
                    && e.0.as_ref().is_none_or(|o| *o < l)
                {
                    e.0 = Some(l);
                }
                if let Some(u) = u
                    && e.1.as_ref().is_none_or(|o| u < *o)
                {
                    e.1 = Some(u);
                }
            }
            _ => {}
        }
    }
    let crossed = out
        .values()
        .any(|b| matches!(b, (Some(l), Some(u)) if u < l));
    (!crossed).then_some(out)
}

/// [`project_each`]'s answer for a formula with no point.
fn no_points(syms: &[Atom]) -> Each {
    (
        syms.iter().map(|_| Ok(IntervalSet::empty())).collect(),
        Vec::new(),
    )
}

/// [`project_each`] of the settled parts `p` of a formula, which is `whole` when it is given.
/// A disjunct is projected from the parts of it, shared, not copied, and the base groups it
/// touches, found from its atoms, which are found once ([`Parts::atoms`]), or from the base's
/// atoms when they are fewer, so that a nest of disjunctions `d` deep costs each disjunct once,
/// not once for each level above it. A disjunct is asked only for the symbols that every
/// disjunct with a point beside it touches, and a hull is tightened at the top over the whole
/// formula and below it over the level with each disjunct's disjunctions cut to their
/// disjuncts' own constraints and its projections added ([`summarize`]), so that no level
/// reads the whole nest below it either.
///
/// With `sets`, for parts whose atoms share a color ([`Naming::Tied`]), each question is one
/// whose answer no order of the parts changes: no search ([`pick`], [`probe`]) removes
/// disjuncts first (the removal by values, [`values::drop_outside_values`], depends on no
/// order); each disjunct of a disjunction is settled by [`settle_as_sets`] before any is
/// asked for a symbol; those shown to have no point are not asked, and each of the others
/// is asked for the symbols that all of them touch, even after one is refused; and a hull is
/// tightened by [`decide`], which renames or settles the formula as its colors allow. The
/// projection is then a function of the parts as sets: for each disjunction, the union of its
/// disjuncts' projections, met over the disjunctions. The settling of each disjunct is the
/// cost added to that of the projection, one test of each disjunct below it for each round of
/// the settling.
fn project_parts(
    mut p: Parts,
    syms: &[Atom],
    whole: Option<&Formula>,
    sets: bool,
    memo: &mut Below,
) -> Result<Each, Refusal> {
    let none = || no_points(syms);
    let mut skipped: Vec<Refusal> = Vec::new();
    if REVERSED.with(Cell::get) {
        p.ors.reverse();
        p.ors.iter_mut().for_each(|ds| ds.reverse());
    }
    // Each disjunct whose own rows put a form outside the values that the base and the
    // disjunctions leave it is removed first, with or without `sets`, on either path
    // ([`values::drop_outside_values`]): `y == 1` of `y == 1 || z >= 0` where `y` is 0 or 2,
    // which the rows the disjunctions imply keep (they allow `0 <= y <= 2`), so that `z` is
    // projected with its lower bound (item PROJECT-hull-credit-lower). It asks the solver
    // nothing, so it refuses nothing.
    if !p.ors.is_empty() && !values::drop_outside_values(&p.cons, &mut p.ors, |d| d.cons.as_slice())
    {
        return Ok(none());
    }
    // With two disjunctions or more, each disjunct that has no point with the base and the
    // rows the other disjunctions imply is removed first ([`drop_jointly_empty`]), before the
    // greedy search ([`pick`]) reads the disjuncts in their order: a disjunct removed so can
    // no longer be taken first and fail the search, which [`probe`] would then answer by a
    // question per disjunct. So which disjunct of `x == 3 || x == 7` comes first, which the
    // sign the equations are written with decides, no longer decides the cost (item
    // PROJECT-each-canon). With `sets`, no other disjunct is removed here.
    if !sets && p.ors.len() > 1 && !old_path() && drop_jointly_empty(&p.cons, &mut p.ors).is_none()
    {
        return Ok(none());
    }
    // Whether [`probe`] changed the parts after that removal. It runs whether or not a
    // greedy search finds a point: when it ran only on a failed search, a disjunct with no
    // point stayed whenever the search found a point first, and widened the hulls by an
    // amount that the order of the parts decided (item PROJECT-canon-precision: the s22
    // reverse-order tests counted 17 boxes of 4000 changing when the parts were reversed;
    // now none change).
    let mut probed = false;
    let mut early = None;
    if !sets && p.ors.len() > 1 {
        let Some(r) = probe_unhandled(&mut p)? else {
            return Ok(none());
        };
        (early, probed) = r;
    }
    let Some(model) = solve(&p.cons, true)? else {
        return Ok(none());
    };
    // The base's constraints in groups linked by shared atoms ([`Linked`]). The base has a
    // point, so its groups are independent: a symbol's hull over the base is its hull over its
    // own group, and a disjunct is projected with the groups its atoms touch, onto the symbols
    // in them, the others keeping the base's hull. A projection then costs the groups each
    // disjunct touches, not the whole base for each disjunct and each symbol.
    // With two disjunctions or more, a hull with a finite end, the only end a tightening moves,
    // is tightened: at the top over the whole formula, below it over [`summarize`].
    let mut ors = std::mem::take(&mut p.ors);
    let n_ors = ors.len();
    let linked = Linked::of(std::mem::take(&mut p.cons));
    // With two disjunctions or more, each disjunct that has no point with the base and the
    // rows the other disjunctions imply is removed again ([`drop_jointly_empty`]), after the
    // search, which [`probe`] may have changed the parts by, so that the implied rows read
    // below for the hulls and for a point at each end are those of the disjuncts left. With
    // `sets`, the parts are projected as they are. Without a probe, the parts are those the
    // removal above left, which removes nothing more from them: its last pass asked every
    // disjunct of these rows and removed none (`linked.cons` is `p.cons`, in its order), so
    // it is not run again (item PRES-each-settle-share). A second run could differ only on a
    // question the solver refused in that pass and answers in the other order (see
    // [`drop_jointly_empty`]); run beside the first in every test of the solver and the
    // preimage steps, it removed nothing.
    if !sets
        && probed
        && n_ors > 1
        && !old_path()
        && drop_jointly_empty(&linked.cons, &mut ors).is_none()
    {
        return Ok(none());
    }
    let bases: HashMap<usize, Formula> = (0..linked.held.len())
        .filter(|r| !linked.held[*r].is_empty())
        .map(|r| {
            let cs = linked.held[r]
                .iter()
                .map(|i| Formula::Con(linked.cons[*i].clone()));
            (r, Formula::and(cs.collect()))
        })
        .collect();
    // The group of an atom: a symbol no constraint mentions is a group of its own, numbered
    // past the linked atoms.
    let index: HashMap<&Atom, usize> = syms.iter().enumerate().map(|(k, s)| (s, k)).collect();
    let group = |a: &Atom| match linked.ids.get(a) {
        Some(i) => Some(linked.root(*i)),
        None => index.get(a).map(|k| linked.parent.len() + k),
    };
    let mut syms_of: HashMap<usize, Vec<usize>> = HashMap::new();
    for (k, s) in syms.iter().enumerate() {
        let g = group(s).expect("a symbol's group");
        syms_of.entry(g).or_default().push(k);
    }
    // The symbols no base constraint mentions.
    let free: Vec<&Atom> = index
        .keys()
        .copied()
        .filter(|s| !linked.ids.contains_key(*s))
        .collect();
    let top = Formula::top();
    let base_of = |r: usize| bases.get(&r).unwrap_or(&top);
    // A group of difference constraints and bounds gives the hulls of all its atoms in one
    // pass ([`difference_hulls`]); any other group, each hull by its own questions.
    let mut differences: HashMap<usize, Option<HashMap<Atom, IntervalSet>>> = HashMap::new();
    let mut out: Vec<Result<IntervalSet, Refusal>> = Vec::with_capacity(syms.len());
    for s in syms {
        let g = group(s).expect("a symbol's group");
        let found = match linked.held.get(g) {
            Some(held) if !held.is_empty() => differences
                .entry(g)
                .or_insert_with(|| {
                    let cs: Vec<&Con> = held.iter().map(|i| &linked.cons[*i]).collect();
                    difference_hulls(&cs, &model)
                })
                .as_ref()
                .and_then(|h| h.get(s).cloned()),
            _ => None,
        };
        out.push(match found {
            Some(h) => Ok(h),
            None => hull_from(base_of(g), s, &model),
        });
    }
    // Complexity tradeoff: the naive way, still taken below for every disjunction not handled
    // here, asks each disjunction about every symbol of its group: `L(s) ∩ ⋂_j U_j(s)` costs
    // Θ(n) disjunctions for each of `n` symbols, Θ(n²) on a chain of `n` holes. Here each
    // component of difference rows, bounds and disjunctions over one or two tie classes that
    // is a forest once its tie classes are contracted gets every atom's exact values by two
    // passes of arc revision ([`forest_domains`]), O(n log n) plus the size of the answer,
    // and its disjunctions are then asked about no symbol. The tradeoffs: the answer is exact
    // where main's may be a hull, so it can be narrower (sound), and its size is that of the
    // answer (`x[k+1] - x[k]` in {0, 10} gives `x[n]` n + 1 intervals); a component with a
    // cycle, two disjunctions on one edge, a disjunction over three classes or more, or a
    // row that is not a difference row keeps the naive way.
    let (tree_doms, tree_handled) = tree_domains(early, probed, &linked, &ors, &model);
    for (k, s) in syms.iter().enumerate() {
        if let (Some(d), Ok(o)) = (tree_doms.get(s), &mut out[k]) {
            *o = o.meet(d);
        }
    }
    // For each disjunction, its disjuncts with a point and their projections, each sorted by
    // symbol; read only to tighten a hull, so kept only with two disjunctions or more.
    let mut seen: Vec<Option<Vec<Projected>>> = Vec::new();
    // The groups a disjunct touches, found from its atoms or from the base's, whichever are
    // fewer, so that a level does not read every atom below it.
    let roots_of = |atoms: &OrdSet<Atom>| -> Vec<usize> {
        let mut roots: Vec<usize> = if atoms.len() <= linked.ids.len() {
            (atoms.iter())
                .filter_map(|a| linked.ids.get(a).map(|i| linked.root(*i)))
                .collect()
        } else {
            (linked.ids.iter())
                .filter(|(a, _)| atoms.contains(*a))
                .map(|(_, i)| linked.root(*i))
                .collect()
        };
        roots.sort_unstable();
        roots.dedup();
        roots
    };
    // The symbols a disjunct with `atoms` and base groups `roots` touches, in order.
    let touched = |atoms: &OrdSet<Atom>, roots: &[usize]| -> Vec<usize> {
        let named: Vec<&Atom> = if atoms.len() <= free.len() {
            (atoms.iter())
                .filter(|a| index.contains_key(a) && !linked.ids.contains_key(*a))
                .collect()
        } else {
            free.iter()
                .copied()
                .filter(|s| atoms.contains(*s))
                .collect()
        };
        let groups = roots
            .iter()
            .copied()
            .chain(named.into_iter().filter_map(group));
        let mut ks: Vec<usize> = groups
            .flat_map(|r| syms_of.get(&r).into_iter().flatten().copied())
            .collect();
        ks.sort_unstable();
        ks.dedup();
        ks
    };
    // The disjunct's parts with the base groups it touches, its constraints sorted as
    // [`nnf`] sorts them and its disjunctions shared.
    // The base is given as its groups `roots`, or as rows `kernel` with the same points on
    // the disjunct's atoms and its symbols.
    let parts_of = |d: &Parts, roots: &[usize], kernel: Option<&[Con]>| -> Parts {
        let mut fs: Vec<Formula> = match kernel {
            Some(k) => k.iter().cloned().map(Formula::Con).collect(),
            None => roots.iter().map(|r| base_of(*r).clone()).collect(),
        };
        fs.extend(d.cons.iter().cloned().map(Formula::Con));
        let mut q = Parts::of(Formula::and(fs));
        q.cons.sort();
        q.ors.extend(d.ors.iter().cloned());
        q
    };
    // For each disjunct, the base projected ([`by_halves`]) onto the atoms of the disjunct and
    // of the nest below it that the base has, and onto the symbols in the groups it touches:
    // the disjunct with it has the points on those that it has with the base, so each is
    // projected with rows about its own size where the base is a chain or a tree, not with
    // its groups whole. The base has a point.
    let mut kernels: Vec<Vec<Option<Vec<Con>>>> =
        ors.iter().map(|ds| vec![None; ds.len()]).collect();
    {
        let mut keep: Vec<BTreeSet<Atom>> = Vec::new();
        let mut place: Vec<(usize, usize)> = Vec::new();
        for (j, ds) in ors.iter().enumerate() {
            for (t, d) in ds.iter().enumerate() {
                let atoms = d.atoms();
                let roots = roots_of(atoms);
                let mut set: BTreeSet<Atom> = if atoms.len() <= linked.ids.len() {
                    (atoms.iter())
                        .filter(|a| linked.ids.contains_key(*a))
                        .cloned()
                        .collect()
                } else {
                    (linked.ids.keys())
                        .filter(|a| atoms.contains(*a))
                        .cloned()
                        .collect()
                };
                if !tree_handled[j] {
                    set.extend(touched(atoms, &roots).into_iter().map(|k| syms[k].clone()));
                }
                keep.push(set);
                place.push((j, t));
            }
        }
        let rows = linked.cons.clone();
        // The least and the first past the greatest product atom, to ask whether a disjunct
        // has one in O(log n).
        let products = (
            Atom::product_of(Factor::Sym(Arc::from("")), Factor::Sym(Arc::from(""))),
            Atom::Aux(0),
        );
        let filled: Result<(), ()> = by_halves(rows, &keep, |i, k| {
            let (j, t) = place[i];
            // The projection keeps an atom of neither the disjunct nor the symbols where it
            // cannot eliminate it exactly (`2 h == x + 15`, `h` a witness of `x` odd); its
            // constants then differ by the path the disjunct is read on, and are moved to one
            // form ([`shift_free`]) so that the memo below knows the disjunct again.
            let atoms = ors[j][t].atoms();
            let plain = atoms
                .range(products.0.clone()..products.1.clone())
                .next()
                .is_none();
            kernels[j][t] = k.filter(|_| !old_path()).map(|k| {
                if plain {
                    shift_free(k, |a| !atoms.contains(a) && !index.contains_key(a))
                } else {
                    k
                }
            });
            Ok(Vec::new())
        });
        filled.expect("no leaf fails");
    }
    for (j, ds) in ors.iter().enumerate() {
        // For each symbol, the join of its projections over the satisfiable disjuncts that
        // touch it (`None` once one is refused), and how many touch it; a satisfiable disjunct
        // that does not touch it gives the base's hull, which leaves it as it is.
        let mut acc: HashMap<usize, (Option<IntervalSet>, usize)> = HashMap::new();
        let (mut sat, mut refused) = (0usize, false);
        let mut found_here = Vec::new();
        // A symbol changes only when every disjunct with a point touches it, so the disjuncts
        // are read smallest first, and each is asked only for the symbols that every disjunct
        // with a point before it touched (`None`: all of them). A deep disjunct beside a small
        // one is then asked for the few symbols the small one names, not for every symbol of
        // the nest below it. With `sets`, each disjunct is settled first, and each
        // that may have a point is asked for the symbols that all such disjuncts touch, which
        // no order changes; the others are not asked.
        let mut order: Vec<(usize, &Rc<Parts>)> = ds.iter().enumerate().collect();
        order.sort_by_key(|(_, d)| d.atoms().len());
        let mut wanted: Option<Vec<usize>> = None;
        // With `sets`, each disjunct's settling, and whether it was of the base's groups.
        let mut pre: Vec<Option<Presettled>> = Vec::new();
        if sets {
            for &(t, d) in &order {
                let roots = roots_of(d.atoms());
                // A projection may keep a disjunct not shown to have a point; one refused with
                // the projected base is asked again with the base's groups.
                let kernel = kernels[j][t].as_deref();
                let mut s = settle_as_sets(parts_of(d, &roots, kernel)).map(|s| s.map(|s| s.p));
                let groups = kernel.is_none() || s.is_err();
                if s.is_err() && kernel.is_some() {
                    s = settle_as_sets(parts_of(d, &roots, None)).map(|s| s.map(|s| s.p));
                }
                // Only a settling that leaves no point shows that a disjunct has none; a
                // search for one would choose by name.
                let maybe = !matches!(s, Ok(None));
                if maybe {
                    let ks = if tree_handled[j] {
                        Vec::new()
                    } else {
                        touched(d.atoms(), &roots)
                    };
                    wanted = Some(match wanted {
                        None => ks,
                        Some(ws) => ws
                            .into_iter()
                            .filter(|k| ks.binary_search(k).is_ok())
                            .collect(),
                    });
                }
                pre.push(maybe.then_some((s, groups)));
            }
        }
        for (at, (t, d)) in order.into_iter().enumerate() {
            let pre_d = match pre.get_mut(at) {
                Some(s) => match s.take() {
                    Some(s) => Some(s),
                    None => continue,
                },
                None => None,
            };
            let atoms = d.atoms();
            let roots = roots_of(atoms);
            let ks: Vec<usize> = match &wanted {
                Some(ws) => ws
                    .iter()
                    .copied()
                    .filter(|&k| match linked.ids.get(&syms[k]) {
                        Some(i) => roots.binary_search(&linked.root(*i)).is_ok(),
                        None => atoms.contains(&syms[k]),
                    })
                    .collect(),
                None if tree_handled[j] => Vec::new(),
                None => touched(atoms, &roots),
            };
            let sub: Vec<Atom> = ks.iter().map(|&k| syms[k].clone()).collect();
            // A disjunct asked for no symbol is only asked whether it has a point, as
            // [`decide`] asks it; with `sets` it was asked above.
            // A disjunct met before, with the same base and asked for the same symbols, is
            // read once: its answer depends on these alone. The base is the one projected for
            // this disjunct, its free atoms moved to one form ([`shift_free`]), or, where there
            // is none or the solver refuses the disjunct with it, the base's groups; each
            // answer is kept under a key of its own, so that the answer read for a disjunct
            // does not depend on which path to it was read first.
            let kernel = kernels[j][t].take();
            let (mut pre_d, pre_groups) = match pre_d {
                Some((s, g)) => (Some(s), g),
                None => (None, false),
            };
            let answer = |settled: Result<Option<Parts>, Refusal>, memo: &mut Below| {
                settled.and_then(|q| match q {
                    None => Ok((no_points(&sub), false)),
                    Some(q) if ks.is_empty() => {
                        // A point of the disjunct with each disjunct below cut to its own
                        // constraints keeps it, as a level below the top is tightened
                        // ([`summarize`]); the search below it runs only when there is none.
                        // Only whether a point exists is asked, so the probe stops at its
                        // first point ([`probe_to`]); up to that point it is [`probe`], so a
                        // refusal stays a refusal (kept as a point, as before) and no point is
                        // `Ok(None)` exactly where [`probe`] gives it. Not [`has_point`]: its
                        // [`pick`] before and after the probe repeats the one above and decides
                        // nothing here (PRES-probe-first).
                        let point = sets
                            || q.ors.is_empty()
                            || pick(&q, false).is_ok()
                            || !matches!(probe_to(q, &mut Vec::new(), true), Ok(None));
                        Ok(((Vec::new(), Vec::new()), point))
                    }
                    Some(q) => project_parts(q, &sub, None, sets, memo).map(|e| {
                        let point = e.0.iter().any(|r| !matches!(r, Ok(s) if s.is_empty()));
                        (e, point)
                    }),
                })
            };
            let mut found = None;
            if let Some(k) = kernel
                && !pre_groups
            {
                let key: BelowKey = (d.id(), false, k, sub.clone());
                let r = if let Some(r) = memo.get(&key) {
                    r.clone()
                } else {
                    let settled = match pre_d.take() {
                        Some(s) => s,
                        None => settle(parts_of(d, &roots, Some(&key.2)), false),
                    };
                    let r = answer(settled, memo);
                    memo.insert(key, r.clone());
                    r
                };
                // A settling with the projected base is no settling of the base's groups.
                pre_d = None;
                if r.is_ok() {
                    found = Some(r);
                }
            }
            let found_rs = match found {
                Some(r) => r,
                None => {
                    let rows = (roots.iter())
                        .flat_map(|r| linked.held[*r].iter().map(|i| linked.cons[*i].clone()));
                    let key: BelowKey = (d.id(), true, rows.collect(), sub.clone());
                    if let Some(r) = memo.get(&key) {
                        r.clone()
                    } else {
                        let settled = match pre_d {
                            Some(s) => s,
                            None if sets => {
                                settle_as_sets(parts_of(d, &roots, None)).map(|s| s.map(|s| s.p))
                            }
                            None => settle(parts_of(d, &roots, None), false),
                        };
                        let r = answer(settled, memo);
                        memo.insert(key, r.clone());
                        r
                    }
                }
            };
            let (rs, has_point) = match found_rs {
                Ok(((rs, more), point)) => {
                    skipped.extend(more);
                    (rs, point)
                }
                Err(r) => {
                    skipped.push(r);
                    refused = true;
                    // With `sets` every disjunct is asked, so the causes reported are those
                    // of all of them, not of those before the first refused.
                    if sets {
                        continue;
                    }
                    break;
                }
            };
            if !has_point {
                continue;
            }
            sat += 1;
            let mut kept = Vec::new();
            for (j, &k) in ks.iter().enumerate() {
                if let Err(r) = &rs[j] {
                    skipped.push(r.clone());
                }
                let e = acc.entry(k).or_insert((Some(IntervalSet::empty()), 0));
                e.0 =
                    e.0.take()
                        .and_then(|u| rs[j].as_ref().ok().map(|h| u.join(h)));
                e.1 += 1;
                if n_ors > 1
                    && let Ok(h) = &rs[j]
                {
                    kept.push((k, h.clone()));
                }
            }
            if n_ors > 1 {
                found_here.push((&**d, kept));
            }
            if !sets {
                wanted = Some(ks);
            }
        }
        if n_ors > 1 {
            seen.push((!refused).then_some(found_here));
        }
        if refused {
            continue;
        }
        if sat == 0 {
            return Ok(none());
        }
        for (k, (u, touched)) in acc {
            if touched == sat
                && let Some(u) = u
                && let Ok(o) = &mut out[k]
            {
                *o = o.meet(&u);
            }
        }
    }
    // Complexity tradeoff: each bound is tightened by about `2 log2 w` questions of the formula
    // (of the symbol's group alone, where its groups have points), `w` the hull's width, unless a
    // point of the formula at the end shows it (see [`tighten_each`]). First each disjunct that
    // the base and the rows the disjunctions imply show empty is removed ([`drop_jointly_empty`]), and the hull is met with the bounds that the
    // base and the rows the disjunctions left imply ([`disjunction_hulls`]) give, below; where
    // those rows are exact (each disjunction alone, or a few on one stage once their empty
    // disjuncts are gone, decide what its forms may be) the point at each end is found and no
    // question is asked, so a chain of `n` three-atom stages costs O(n log n)
    // (`x[i + 1] - x[i] - y[i] >= 0`, `1 <= y[i] <= 2`, `x[i + 1] - x[i] + y[i] == 4 || == 5`:
    // 0.16 s at 128 stages, where it was 41.6 s; with `x[i + 1] - x[i]` in {3, 7} and
    // `x[i + 1] - x[i] + y[i]` in {6, 9}, which force 7 where the rows allow 4: 0.08, 0.16 and
    // 2.0 s at 64, 128 and 1024 stages, where it was 7.7 s at 64, plan item DISJ-dpll). What is
    // given up: no answer, only time, where disjunctions leave out the end of a hull only by
    // case reasoning, a disjunct empty with each choice of disjuncts elsewhere but not with
    // their hulls (`x` in {0, 2} with `y` in {0, 2} and `x + y` in {1, 3}): the bound of the
    // rows has no point, the bisection asks empty questions, the solver may refuse each with
    // the implied rows (its count of an elimination does not make [`shadow`]'s trial) and
    // [`probe`] tests each disjunct by a propagation of the whole formula, O(n²) solves or more
    // for each question. Why: finding a point of a conjunction of disjunctions of linear rows
    // is NP-complete, and a search that backtracks over the disjuncts (DPLL(T)) is exponential
    // in the worst case. Trigger: disjunctions that only by cases leave out the end of a hull
    // that their rows allow. Tests: `l01_38_presburger::disj_groups` (the hulls of small chains
    // against their points counted one by one, and the two chains above at `n` and `8n`);
    // COMPLEXITY.md row DISJ-incremental.
    // A hull with one finite end is tightened at that end too, searched toward the value of
    // the symbol at a point of the formula (item PRES-pendants-wider: `z0 <= 25` of seed 14
    // case 271 of `l01_39_reduced_product::pendants`, left at 27 before), and an infinite end
    // that a disjunct's own projection bounds is tried at that bound ([`Hull::tighten`]).
    let finite = |o: &Result<IntervalSet, Refusal>| matches!(o, Ok(s) if s.bounds().is_some_and(|(l, h)| matches!(l, End::Fin(_)) || matches!(h, End::Fin(_))));
    // Before the questions, each hull to be tightened is met with the symbol's hull over the
    // base and the rows the disjunctions imply ([`disjunction_hulls`]), all symbols at once by
    // [`by_halves`]: the rows hold at every point of the parts, so the bounds are sound, and
    // where the disjunctions act on the symbol only through the forms they bound (each
    // disjunct one stage of a chain), they are its exact bounds, so no question of the
    // bisection below is empty. An empty question costs the most: the solver may refuse the
    // formula with the implied rows (rows of three atoms whose eliminations it counts as
    // growing), and [`probe`] then tests each disjunct by a propagation of the whole formula.
    // A bound is read from the rows of the projection with the symbol alone, so a projection
    // that keeps other atoms (a core, see [`shadow`]) gives what it gives and the questions
    // the rest. Rows with no point show the parts have none. A hull with an infinite end is met
    // too: in `b + c >= z` with `b` in {0, 2} and `c` in {0, 2} (each a disjunction, as a box
    // with a hole is, [`member`]), each disjunction's union, with the other's atom free, leaves
    // `z` unbounded, and their meet does too, where the rows `0 <= b <= 2` and `0 <= c <= 2`
    // the two imply give `z <= 4` (seed 17 case 121 of `l01_39_reduced_product::pendants`,
    // item PRES-pendants-wider).
    // The rows the disjuncts left imply, read below for the hulls and by [`tighten_each`] for a
    // point at each end.
    let implied = if !sets && n_ors > 1 && !old_path() && out.iter().any(Result::is_ok) {
        disjunction_hulls(&ors, &mut DeepHulls::default())
    } else {
        Vec::new()
    };
    if !implied.is_empty() {
        let ks: Vec<usize> = (0..syms.len()).filter(|&k| out[k].is_ok()).collect();
        let keep: Vec<BTreeSet<Atom>> = (ks.iter())
            .map(|&k| BTreeSet::from([syms[k].clone()]))
            .collect();
        let mut rows = linked.cons.clone();
        rows.extend(implied.iter().cloned());
        let mut empty = false;
        let ran: Result<(), ()> = by_halves(rows, &keep, |i, k| {
            match k {
                None => empty = true,
                Some(rows) => {
                    if let Ok(o) = &mut out[ks[i]] {
                        *o = o.meet(&bounds_alone(&syms[ks[i]], &rows));
                    }
                }
            }
            Ok(Vec::new())
        });
        ran.expect("no leaf fails");
        if empty {
            return Ok(none());
        }
    }
    // For each symbol, the least finite lower end and the greatest finite upper end that a
    // disjunct's own projection gives it, candidates for an end the hull leaves open
    // ([`Hull::tighten`]), read in one pass over the projections kept.
    let mut open: HashMap<usize, (Option<Int>, Option<Int>)> = HashMap::new();
    for (_, kept) in seen.iter().flatten().flatten() {
        for (k, h) in kept {
            let Some((l, u)) = h.bounds() else { continue };
            let e = open.entry(*k).or_default();
            if let End::Fin(v) = l {
                let v = Int::from(v);
                if e.0.as_ref().is_none_or(|w| &v < w) {
                    e.0 = Some(v);
                }
            }
            if let End::Fin(v) = u {
                let v = Int::from(v);
                if e.1.as_ref().is_none_or(|w| &v > w) {
                    e.1 = Some(v);
                }
            }
        }
    }
    // The hulls to tighten: those with a finite end, and those an `open` candidate may give
    // one.
    let ks: Vec<usize> = (0..syms.len())
        .filter(|&k| {
            finite(&out[k])
                || (out[k].is_ok() && open.get(&k).is_some_and(|e| e.0.is_some() || e.1.is_some()))
        })
        .collect();
    if n_ors > 1 && !ks.is_empty() {
        let summary;
        let f = match whole {
            Some(f) => f,
            None => {
                summary = summarize(&linked.cons, &seen, syms);
                &summary
            }
        };
        let ask: Ask = if sets {
            |f, _| decide(f)
        } else {
            |f, kept| decide_kept(f, Some(kept))
        };
        tighten_each(f, syms, &ks, &open, &mut out, &implied, ask);
    }
    skipped.sort_unstable();
    skipped.dedup();
    Ok((out, skipped))
}

/// A disjunct of [`project_parts`] below the top, by its id ([`Parts::id`]), with whether it is
/// read with the base's groups (`true`) or with the base projected for it, the constraints of
/// that base, and the symbols it is asked for.
type BelowKey = (u64, bool, Vec<Con>, Vec<Atom>);

/// The answers of [`project_parts`] for the disjuncts below the top already read. A disjunct
/// shared by several disjunctions (a named disjunction used as a disjunct at each of several
/// places, COMPLEXITY.md S31b) is then projected once for each base and set of symbols, not
/// once for each path to it, which is exponential in the depth when the shared disjunctions
/// nest.
type Below = HashMap<BelowKey, Result<(Each, bool), Refusal>>;

/// A disjunct of [`project_parts`] settled before it is read (with `sets`), with whether it was
/// settled with the base's groups.
type Presettled = (Result<Option<Parts>, Refusal>, bool);

/// `rows`, sorted, with each atom `a` that `free` allows (a symbol or an auxiliary variable,
/// not a factor of a product among the rows) replaced by `a - q` for the integer `q` that
/// brings the constant of one row over `a` into the range from 0 up to that row's coefficient
/// of `a`: `2 a == x + 15` becomes `2 a == x - 1` (`q` = -8), and every other row over `a`
/// moves by `q` times its own coefficient of `a`. The row is the one with the least
/// coefficient of `a` in size, then by comparison, then by terms, then by constant, a choice
/// that moving any atom does not change: rows that compare equal up to the constant have the
/// same coefficients, so they move together and keep their order.
///
/// The answer of [`project_parts`] for a disjunct read with `rows` is unchanged when `free`
/// holds of no atom of the disjunct or of the symbols: `a ↦ a - q` maps the integer points
/// of the rows with the disjunct one to one onto those of the rows moved with it, and changes
/// no atom that the disjunct or the symbols read, so the points have the same values on the
/// symbols and the same have a point. A product's factor is left as it is, since moving it
/// would change the product. The solver is then asked about the moved rows, the same set.
///
/// Complexity tradeoff: [`project_parts`] keyed its memo by the base rows as projected,
/// which keep, where the projection cannot eliminate an atom exactly, the same core with a
/// constant that depends on the path the disjunct is read on (`2 h == x[i] + c` with `c` one
/// of the `2^i` partial sums of a nest of shared disjunctions `x[i] == x[i - 1]` or
/// `x[i] == x[i - 1] + 2^i`, `x[k]` odd): the memo never knew the disjunct again, so the
/// projection read all `2^k` paths, O(2^k) (0.72G to 11.50G instructions at k = 10 to 14).
/// With the free atoms moved, each level has one key and the nest costs O(k). This costs
/// O(r log r) for a projected base of `r` terms, no more than the projection that made it.
/// What is given up: only the constant of each free atom is moved, one atom at a time, so
/// two projected bases that differ by a move of free atoms are made equal where each row
/// holds one free atom; where a row holds two or more, or the bases differ by more than a
/// move (`a ↦ a + x`, `a ↦ -a`), they can stay apart, and a nest with such links still reads
/// each path: O(2^k). A disjunct with a product atom is not moved at all (finding whether a
/// product reads a free atom costs the disjunct's atoms at each level, O(k^2) in a nest).
/// Why: the form that makes every equal projection equal is the projection's own normal
/// form, the Hermite normal form of the free atoms' columns, a change of the projection,
/// not of its key. Tests: `l01_38_presburger::shared::a_linked_nest_projects_in_time_linear_in_its_depth`
/// (the nest at k and 8k, and its answers against the ways counted one by one), `twin_linked_nests_project_in_time_linear_in_their_depth`; COMPLEXITY.md row
/// PRES-below-key.
fn shift_free(mut rows: Vec<Con>, free: impl Fn(&Atom) -> bool) -> Vec<Con> {
    let mut factors: HashSet<Atom> = HashSet::new();
    let mut at: BTreeMap<Atom, Vec<usize>> = BTreeMap::new();
    for (i, c) in rows.iter().enumerate() {
        for a in c.lin.terms.keys() {
            match a {
                Atom::Product(x, y) => {
                    factors.insert(x.atom());
                    factors.insert(y.atom());
                }
                _ if free(a) => at.entry(a.clone()).or_default().push(i),
                _ => {}
            }
        }
    }
    for (a, is) in at {
        if factors.contains(&a) {
            continue;
        }
        let q = {
            let coef = |i: usize| &rows[i].lin.terms[&a];
            let pick = (is.iter().copied())
                .min_by(|&i, &j| {
                    (coef(i).abs().cmp(&coef(j).abs()))
                        .then_with(|| rows[i].rel.cmp(&rows[j].rel))
                        .then_with(|| rows[i].lin.terms.cmp(&rows[j].lin.terms))
                        .then_with(|| rows[i].lin.constant.cmp(&rows[j].lin.constant))
                })
                .expect("a free atom's row");
            rows[pick].lin.constant.div_floor(coef(pick))
        };
        if q.is_zero() {
            continue;
        }
        for i in is {
            let by = &rows[i].lin.terms[&a] * &q;
            let lin = &mut rows[i].lin;
            lin.constant = &lin.constant - &by;
        }
    }
    rows.sort_unstable();
    rows
}

/// A disjunct with a point and its projections, each with the index of its symbol, sorted.
type Projected<'a> = (&'a Parts, Vec<(usize, IntervalSet)>);

/// A level of [`project_parts`] below the top, with more points than it has, for tightening
/// its hulls: the base `cons` and, for each disjunction (`None` where a disjunct was refused),
/// the disjunction of its disjuncts with a point, each a disjunct's own constraints and, when
/// it has disjunctions, its projections onto the symbols it was asked for and each of its
/// disjunctions with every disjunct cut to its own constraints. Each part's constraints are
/// read here at its own level and at the level above it, so the summaries of a nest cost its
/// size twice, however deep it is.
// Complexity tradeoff: below the top, a hull is tightened over this formula, not over the
// level's own, so a bound that only a choice two disjunctions or more inside a disjunct, jointly
// with the rest of the level, pushes inward is left where the projections put it: a sound
// hull, wider than the level's. Test
// `l01_39_reduced_product::deep_condition::a_choice_two_levels_inside_a_branch_is_read_by_its_projections_only`
// asserts the wider hull `[3..=4, 10..=10, 100..=200]` where the level's own is
// `[3..=4, 100..=200]`; a choice one disjunction inside is read exactly
// (`a_choice_one_level_inside_a_branch_is_read_with_the_rest_of_the_branch`). The level's own
// formula holds the whole nest below it, and tightening over it at each level costs the nest
// once for each level above: measured on this code, `arms_of_a_capped_test_take_time_near_linear_in_its_depth`
// then takes 51.1 times the work from d = 30 to 240 (limit 24), O(d²) (COMPLEXITY S31). It is
// triggered by two disjunctions or more at a level below the top, one of them with a disjunct
// whose disjunctions have disjunctions of their own. A complete answer would need each level's
// formula decided incrementally from the level below's; in general the exact bound decides
// whether a nest of disjunctions of linear constraints has a point, which is NP-complete.
fn summarize(cons: &[Con], seen: &[Option<Vec<Projected>>], syms: &[Atom]) -> Formula {
    let own = |p: &Parts| -> Vec<Formula> { p.cons.iter().cloned().map(Formula::Con).collect() };
    let mut fs: Vec<Formula> = cons.iter().cloned().map(Formula::Con).collect();
    for ds in seen.iter().flatten() {
        let each = ds.iter().map(|(d, rs)| {
            let mut gs = own(d);
            if !d.ors.is_empty() {
                gs.extend(rs.iter().map(|(k, h)| member(&syms[*k], h)));
                let cut = d
                    .ors
                    .iter()
                    .map(|es| Formula::or(es.iter().map(|e| Formula::and(own(e))).collect()));
                gs.extend(cut);
            }
            Formula::and(gs)
        });
        fs.push(Formula::or(each.collect()));
    }
    Formula::and(fs)
}

/// A question of [`tighten_each`]: whether a formula has a point, [`decide_kept`] adding to
/// the list a point of the formula it finds, or [`decide`], which adds none.
type Ask = fn(&Formula, &mut Vec<Model>) -> Result<bool, Refusal>;

/// Each hull of `out` at the places `ks` (the projection of `f` onto the symbol of `syms` at
/// its place) with each finite bound raised or lowered by bisection to the nearest value at
/// which `f` with the symbol past it is shown to have no point ([`Hull::tighten`]), and each
/// infinite end with a candidate in `open` made finite where `f` past the candidate is shown
/// to have no point. A bound moves only on such a proof, so a refused question leaves it
/// sound. Each question is asked of `ask`. `hint` holds rows that the parts `f` stands for
/// imply, read with `f`'s own to find a point at each end.
///
/// The conjuncts of `f` are first put in groups linked by shared atoms
/// ([`linked_conjuncts`]). When there are two groups or more and each is shown to have a
/// point, each symbol is asked of its own group alone: `f` with a constraint on the symbol has
/// a point exactly when the symbol's group with it has one, the other groups having points.
/// When one group is shown to have none, `f` has none, and every such hull is empty. When the
/// solver refuses to say whether a group has a point, every symbol is asked of `f`, as when
/// there is one group.
///
/// Within a group the least and greatest value of each symbol over the points of the group
/// found so far are kept ([`Hull`]): a question whose constraint holds at one of them has a
/// point, so it is not asked (it would be answered `true` or refused, and either leaves the
/// bound where the point does), and a point with the symbol at an end of its hull shows that
/// end is its bound. The bounds of each hull are added to the rows, as `f` implies them.
/// Before the questions, a point of the group's rows with every atom at its least value, and
/// one with every atom at its greatest, are read ([`point_of`]); where the group holds at
/// them, they show every end that the rows alone decide, at once.
// Complexity tradeoff: each symbol was asked of the whole formula, its rows read again for each
// symbol and a point of them searched for at each end, O(N) per symbol for a formula of size N,
// so projecting the k symbols of a family cost O(k N), quadratic in the family (all states of a
// pipeline of 16 and 128 stages, `l01_38_presburger::omega::dead2`: 56.1 times the bytes
// unchained, 61.6 chained, item TIGHTEN-each-whole). Now the groups cost O(N log N) to find, the
// rows of each group are read once, with each hull's bounds added to them so that the point
// with every atom least (or greatest) puts each symbol at its hull's end where the group allows
// it, and an end shown by a point found before costs O(1); one that no point shows costs a
// point search of its group ([`point_of`]: a [`shadow`] of its rows and a solve), and the
// questions of its bisection, each a question of the group. What is given up: no answer, only
// time, on a group in which the ends of the symbols need points of their own, not the least or
// greatest of every atom at once (`k` symbols each 0 or 1 whose sum is at most 1: each upper
// end needs the point with that symbol 1 and the others 0): one point search of the whole
// group per symbol, at least O(k m) for `m` rows, measured 2.9, 16 and 118 ms at k = 16, 32
// and 64 (the code before: 6.2, 37 and 244 ms; the projection of each disjunct onto every
// symbol before it, item PROJECT-each-chain-all, takes 71, 425 and 2830 ms there). Why: the
// points at the ends are as many as the symbols, and each is searched for in the group's rows
// from the start; a point that differs from one found before in one atom could be checked by
// reading only the rows and disjunctions on that atom, with each row's value kept and changed
// by the atom's coefficient, but [`point_of`] and [`Formula::holds`] read the whole group.
// Trigger: one group whose symbols' ends are reached at different points. Tests:
// `l01_38_presburger::omega::every_state_and_credit_of_a_pipeline_scale` (unchained; the
// chained pipeline's tightening is O(n log n) too, but its projection of each disjunct onto
// every symbol of the chain is not, item PROJECT-each-chain-all),
// `l01_38_presburger::omega::independent_stages_scale` (ends shown only by questions);
// COMPLEXITY.md row TIGHTEN-each-whole.
// A hull with one finite end (item PRES-pendants-wider): the naive search walks from the end
// one value at a time, `w` questions with `w` the distance from the end to the nearest value at
// a point. Here the end is bisected toward the value of the symbol at a point found (the least
// or greatest kept in [`Hull`]), about `log2 w` questions of the group; where the solver shows
// the group has a point but gives none ([`decide`] with `sets`), steps of 1, 2, 4, ... away
// from the end first find a value at or past a point, so about `2 log2 w` questions in all. The
// cost: a step may overshoot by up to `w`, and each question is a whole `decide` of the group.
// An infinite end is first given a candidate, the farthest finite end that a disjunct's own
// projection gives the symbol (`open`, read by [`project_parts`] in one pass over the
// projections kept), and one question, the group with the symbol past the candidate, makes it
// a finite end to search from where it has no point (`z1 <= 6` of seed 11 case 226 of
// `l01_39_reduced_product::pendants`, where `z1 >= 7` leaves three disjuncts that hold together
// at no point). What is given up: an end that cases bound at a value no disjunct gives
// (`z <= x + y` with `x <= 0` and `y <= 0` each by cases) stays open, a sound hull wider than
// the exact one, as does an end whose question the solver refuses. Finding whether such an end
// is finite at all asks whether the formula has points with the symbol past every bound, a
// question with one more quantifier, and no search by values ends where it is not (item
// PRES-cases-end). Tests
// `l01_38_presburger::disj_groups::a_finite_end_whose_other_is_infinite_is_tightened_by_cases`,
// `a_finite_end_is_tightened_where_the_solver_gives_no_point`,
// `an_end_only_case_reasoning_bounds_is_read_from_a_disjunct`,
// `an_end_that_cases_bound_at_a_value_no_disjunct_gives_is_left_open` and
// `the_middle_of_a_chain_whose_lower_end_only_cases_give_is_projected_in_n_log_n` (`n` and
// `8n`); COMPLEXITY.md row PRES-pendants-wider.
fn tighten_each(
    f: &Formula,
    syms: &[Atom],
    ks: &[usize],
    open: &HashMap<usize, (Option<Int>, Option<Int>)>,
    out: &mut [Result<IntervalSet, Refusal>],
    hint: &[Con],
    ask: Ask,
) {
    // Each hull holds the symbol at every point of `f`, so its finite bounds are rows `f`
    // implies.
    let mut rows = hint.to_vec();
    for &k in ks {
        if let Ok(s) = &out[k]
            && let Some((lo, hi)) = s.bounds()
        {
            let x = Lin::atom(syms[k].clone());
            if let End::Fin(lo) = lo {
                rows.push(Con::ge(&x, &Lin::constant(Int::from(lo))));
            }
            if let End::Fin(hi) = hi {
                rows.push(Con::ge(&Lin::constant(Int::from(hi)), &x));
            }
        }
    }
    let hint = &rows[..];
    let groups = linked_conjuncts(f, hint, syms, ks);
    if groups.len() > 1 {
        let mut ends: Vec<Hull> = (groups.into_iter())
            .map(|(cs, rows, ks)| {
                let g = Formula::and(cs.into_iter().cloned().collect());
                Hull::new(g, rows.into_iter().cloned(), syms, ks, ask)
            })
            .collect();
        let mut refused = false;
        for e in &mut ends {
            match e.has_point() {
                Ok(true) => {}
                // A group with no point: `f` has none.
                Ok(false) => {
                    for &k in ks {
                        out[k] = Ok(IntervalSet::empty());
                    }
                    return;
                }
                Err(_) => refused = true,
            }
        }
        if !refused {
            for e in &mut ends {
                e.tighten_all(out, open);
            }
            return;
        }
    }
    let mut e = Hull::new(f.clone(), hint.iter().cloned(), syms, ks.to_vec(), ask);
    e.seed();
    e.tighten_all(out, open);
}

/// The top-level conjuncts of `f` ([`Formula::conjuncts`]) in groups linked by shared atoms, a
/// product linked to its factors, each with the rows of `hint` on its atoms (a row with no atom
/// is left out: the rows only help find points) and the symbols of `ks` (indices into `syms`)
/// in it. A symbol in no conjunct and no row is a group of its own. The groups come in the
/// order of their first conjunct, row or symbol. A part that two conjuncts hold is walked
/// once, and links them, so the cost is O(N log N) for `f` of N distinct parts.
fn linked_conjuncts<'f>(
    f: &'f Formula,
    hint: &'f [Con],
    syms: &[Atom],
    ks: &[usize],
) -> Vec<(Vec<&'f Formula>, Vec<&'f Con>, Vec<usize>)> {
    /// A union-find over the conjuncts, numbered first, and the atoms.
    struct Sets {
        parent: Vec<usize>,
        ids: HashMap<Atom, usize>,
    }
    impl Sets {
        fn find(&mut self, mut i: usize) -> usize {
            while self.parent[i] != i {
                self.parent[i] = self.parent[self.parent[i]];
                i = self.parent[i];
            }
            i
        }
        fn union(&mut self, a: usize, b: usize) {
            let (a, b) = (self.find(a), self.find(b));
            self.parent[a.max(b)] = a.min(b);
        }
        /// The element of atom `a`, a product's linked to its factors'.
        fn atom(&mut self, a: &Atom) -> usize {
            if let Some(&e) = self.ids.get(a) {
                return e;
            }
            let e = self.parent.len();
            self.parent.push(e);
            self.ids.insert(a.clone(), e);
            if let Atom::Product(x, y) = a {
                for g in [x.atom(), y.atom()] {
                    let h = self.atom(&g);
                    self.union(e, h);
                }
            }
            e
        }
    }
    let cs = f.conjuncts();
    let mut sets = Sets {
        parent: (0..cs.len()).collect(),
        ids: HashMap::new(),
    };
    // The conjunct that first reached each part shared by more than one holder.
    let mut reached: HashMap<Id, usize> = HashMap::new();
    for (j, c) in cs.iter().enumerate() {
        let mut stack = vec![*c];
        while let Some(g) = stack.pop() {
            if let Formula::Con(con) = g {
                for a in con.lin.terms.keys() {
                    let e = sets.atom(a);
                    sets.union(j, e);
                }
                continue;
            }
            if let Some(id) = Id::of(g) {
                match reached.entry(id) {
                    std::collections::hash_map::Entry::Occupied(o) => {
                        let first = *o.get();
                        sets.union(j, first);
                        continue;
                    }
                    std::collections::hash_map::Entry::Vacant(v) => {
                        v.insert(j);
                    }
                }
            }
            stack.extend(g.kids());
        }
    }
    let rows: Vec<(usize, &Con)> = (hint.iter())
        .filter_map(|r| {
            let mut atoms = r.lin.terms.keys();
            let first = sets.atom(atoms.next()?);
            for a in atoms {
                let e = sets.atom(a);
                sets.union(first, e);
            }
            Some((first, r))
        })
        .collect();
    let at: Vec<usize> = ks.iter().map(|&k| sets.atom(&syms[k])).collect();
    let mut group: HashMap<usize, usize> = HashMap::new();
    let mut out: Vec<(Vec<&Formula>, Vec<&Con>, Vec<usize>)> = Vec::new();
    let mut place = |sets: &mut Sets, e: usize| {
        let r = sets.find(e);
        *group.entry(r).or_insert_with(|| {
            out.push((Vec::new(), Vec::new(), Vec::new()));
            out.len() - 1
        })
    };
    let cs_at: Vec<usize> = (0..cs.len()).map(|j| place(&mut sets, j)).collect();
    let rows_at: Vec<usize> = rows.iter().map(|(e, _)| place(&mut sets, *e)).collect();
    let ks_at: Vec<usize> = at.iter().map(|&e| place(&mut sets, e)).collect();
    for (c, g) in cs.into_iter().zip(cs_at) {
        out[g].0.push(c);
    }
    for ((_, r), g) in rows.into_iter().zip(rows_at) {
        out[g].1.push(r);
    }
    for (&k, g) in ks.iter().zip(ks_at) {
        out[g].2.push(k);
    }
    out
}

/// A formula whose hulls [`tighten_each`] tightens, with the rows read to find its points and,
/// for each symbol it tightens, the least and greatest value of the symbol over the points of
/// the formula found so far.
struct Hull {
    f: Formula,
    /// The rows of `f`'s parts ([`absorbed`]), the rows its disjunctions imply
    /// ([`disjunction_hulls`]) and the rows given as a hint.
    rows: Vec<Con>,
    /// The symbols tightened, as indices into `syms`, each with its linear form.
    ks: Vec<(usize, Lin)>,
    /// For each of `ks`, the least and greatest value over the points found.
    seen: Vec<Option<(Int, Int)>>,
    /// The points that `ask` found and that are not yet read into `seen`.
    found: Vec<Model>,
    /// Whether `ask` showed that `f` has a point; it may give none ([`decide`]).
    has: bool,
    ask: Ask,
}

impl Hull {
    fn new(
        f: Formula,
        hint: impl Iterator<Item = Con>,
        syms: &[Atom],
        ks: Vec<usize>,
        ask: Ask,
    ) -> Hull {
        let mut parts = absorbed(&f, &[]).0;
        let mut rows = mem::take(&mut parts.cons);
        rows.extend(disjunction_hulls(&parts.ors, &mut DeepHulls::default()));
        rows.extend(hint);
        let ks: Vec<(usize, Lin)> = (ks.into_iter())
            .map(|k| (k, Lin::atom(syms[k].clone())))
            .collect();
        Hull {
            f,
            rows,
            seen: vec![None; ks.len()],
            ks,
            found: Vec::new(),
            has: false,
            ask,
        }
    }

    /// Reads the point `m` of `f` into `seen`; an atom absent from it is zero, a product the
    /// product of its factors' values, as [`Formula::holds`] reads them.
    fn read(&mut self, m: &Model) {
        for ((_, x), s) in self.ks.iter().zip(&mut self.seen) {
            let v = x.eval(m);
            *s = Some(match s.take() {
                None => (v.clone(), v),
                Some((lo, hi)) => (lo.min(v.clone()), hi.max(v)),
            });
        }
    }

    /// Reads the points `ask` found.
    fn read_found(&mut self) {
        for m in mem::take(&mut self.found) {
            self.read(&m);
        }
    }

    /// Reads a point of the rows with every atom at its least value, and one with every atom
    /// at its greatest, where `f` holds at them; whether one did.
    fn seed(&mut self) -> bool {
        let mut held = false;
        for greatest in [false, true] {
            if let Some(m) = point_of(&self.rows, greatest)
                && self.f.holds(&m)
            {
                self.read(&m);
                held = true;
            }
        }
        held
    }

    /// Whether `f` has a point: shown by [`Hull::seed`], or else asked.
    fn has_point(&mut self) -> Result<bool, Refusal> {
        if self.seed() {
            return Ok(true);
        }
        let r = (self.ask)(&self.f, &mut self.found);
        self.read_found();
        self.has = matches!(r, Ok(true));
        r
    }

    /// The constraint that symbol `i` is at most `v` (`below`) or at least `v`.
    fn side(&self, i: usize, below: bool, v: &Int) -> Con {
        let (x, v) = (&self.ks[i].1, Lin::constant(v.clone()));
        if below {
            Con::ge(&v, x)
        } else {
            Con::ge(x, &v)
        }
    }

    /// Whether a point found has symbol `i` at most `v` (`below`) or at least `v`.
    fn known(&self, i: usize, below: bool, v: &Int) -> bool {
        match &self.seen[i] {
            Some((lo, hi)) => {
                if below {
                    lo <= v
                } else {
                    hi >= v
                }
            }
            None => false,
        }
    }

    /// The answer of `ask` to `f` with symbol `i` at most `v` (`below`) or at least `v`.
    fn asked(&mut self, i: usize, below: bool, v: &Int) -> Result<bool, Refusal> {
        let con = self.side(i, below, v);
        let r = (self.ask)(
            &Formula::and(vec![self.f.clone(), Formula::Con(con)]),
            &mut self.found,
        );
        self.read_found();
        r
    }

    /// Whether `f` with symbol `i` at most `v` (`below`) or at least `v` is shown to have no
    /// point.
    fn none(&mut self, i: usize, below: bool, v: &Int) -> bool {
        !self.known(i, below, v) && matches!(self.asked(i, below, v), Ok(false))
    }

    /// Whether a point of `f` with symbol `i` at `v` is found: among those found, or as a point
    /// of the rows with the symbol at `v` and every other atom at its least value (`below`) or
    /// its greatest, where `f` holds.
    fn at_end(&mut self, i: usize, below: bool, v: &Int) -> bool {
        if self.known(i, below, v) {
            return true;
        }
        self.rows
            .push(Con::eq(&self.ks[i].1, &Lin::constant(v.clone())));
        let m = point_of(&self.rows, !below);
        self.rows.pop();
        match m {
            Some(m) if self.f.holds(&m) => {
                self.read(&m);
                true
            }
            _ => false,
        }
    }

    /// The hull `set` of symbol `i`, each finite bound tightened. A point of `f` where the
    /// symbol is at an end of `set` shows that end is its bound: each question of that side
    /// has a point, so none is asked, and the bound is the one the questions give. Where the
    /// rows read are exact (each disjunct one stage of a chain) and give the bounds of `set`,
    /// the points are found, and no question is asked that the solver would refuse with the
    /// implied rows and send to a [`probe`] of every disjunct. Where no such point is found,
    /// the question of the end itself, the symbol at most `lo` (or at least `hi`), is asked
    /// first: a point of it shows the end is the bound, as the search below would find, since
    /// every question of that side then has a point. One question where the end is the bound,
    /// in place of about `log2 w` that all have a point (item PRES-project-each-cost); one more
    /// where it is not. A refusal or `false` leaves the search as it was.
    ///
    /// Where the other end is infinite, the search runs toward the value of the symbol at a
    /// point of `f`, and the infinite end stays (item PRES-pendants-wider). An infinite end
    /// with a candidate in `open` (lower, upper), a value past which no point is expected,
    /// becomes that value where `f` with the symbol past it is shown to have no point, and is
    /// then searched as a finite end; a point or a refusal leaves it open.
    fn tighten(
        &mut self,
        i: usize,
        set: IntervalSet,
        open: &(Option<Int>, Option<Int>),
    ) -> IntervalSet {
        let fin = |e: &End| match e {
            End::Fin(v) => Some(Int::from(v)),
            _ => None,
        };
        let Some((lo, hi)) = set.bounds().map(|(l, h)| (fin(l), fin(h))) else {
            return set;
        };
        let (one, two) = (Int::ONE, Int::from(2));
        // An end the rows leave open that a disjunct's own projection bounds (`z <= 0` of
        // `z <= 0 || a >= 5` with `z <= 0 || a <= 3`): one question, `f` with the symbol past
        // the candidate, and where it has no point the candidate is a finite end to search
        // from.
        let hi = match (hi, &open.1) {
            (None, Some(u))
                if lo.as_ref().is_none_or(|l| l <= u) && self.none(i, false, &(u + &one)) =>
            {
                Some(u.clone())
            }
            (hi, _) => hi,
        };
        let lo = match (lo, &open.0) {
            (None, Some(l))
                if hi.as_ref().is_none_or(|h| l <= h) && self.none(i, true, &(l - &one)) =>
            {
                Some(l.clone())
            }
            (lo, _) => lo,
        };
        if lo.is_none() && hi.is_none() {
            return set;
        }
        // With one end infinite, the value of the symbol at a point of `f` bounds the search of
        // the finite end from the other side: a point found so far ([`Hull::seed`], the
        // questions before), else the one `ask` finds for `f` itself. `f` with no point leaves
        // no value, and a refusal leaves `set` as it is. Where `ask` shows that `f` has a point
        // but gives none ([`decide`] with `sets`), the search first steps away from the finite
        // end by 1, 2, 4, ... to a value with no proof that `f` has no point up to it; `f` has
        // a point, so the steps end, after about `log2 w` questions with `w` the distance from
        // the end to the nearest value of the symbol at a point.
        if (lo.is_none() || hi.is_none()) && self.seen[i].is_none() && !self.has {
            match (self.ask)(&self.f, &mut self.found) {
                Ok(true) => self.has = true,
                Ok(false) => return IntervalSet::empty(),
                Err(_) => return set,
            }
            self.read_found();
        }
        // The least `v` from `lo` with no proof that `f` has no point where the symbol is at
        // most `v`, and the greatest down to it with none where it is at least `v`.
        let new_lo = match lo {
            None => None,
            Some(lo)
                if self.at_end(i, true, &lo) || matches!(self.asked(i, true, &lo), Ok(true)) =>
            {
                Some(lo)
            }
            Some(lo) => {
                let top = hi
                    .clone()
                    .or_else(|| self.seen[i].as_ref().map(|s| s.0.clone()));
                let (mut a, mut b) = match top {
                    Some(top) => (lo, top),
                    None => {
                        let (mut a, mut step) = (lo, one.clone());
                        loop {
                            let v = &a + &step;
                            if !self.none(i, true, &v) {
                                break (a, v);
                            }
                            a = &v + &one;
                            step = &step * &two;
                        }
                    }
                };
                while a < b {
                    let mid = &a + &(&b - &a).div_floor(&two);
                    if self.none(i, true, &mid) {
                        a = &mid + &one
                    } else {
                        b = mid
                    }
                }
                if self.none(i, true, &a) {
                    return IntervalSet::empty();
                }
                Some(a)
            }
        };
        let new_hi = match hi {
            None => None,
            Some(hi)
                if self.at_end(i, false, &hi) || matches!(self.asked(i, false, &hi), Ok(true)) =>
            {
                Some(hi)
            }
            Some(hi) => {
                let bottom =
                    (new_lo.clone()).or_else(|| self.seen[i].as_ref().map(|s| s.1.clone()));
                let (mut a, mut b) = match bottom {
                    Some(bottom) => (bottom, hi),
                    None => {
                        let (mut b, mut step) = (hi, one.clone());
                        loop {
                            let v = &b - &step;
                            if !self.none(i, false, &v) {
                                break (v, b);
                            }
                            b = &v - &one;
                            step = &step * &two;
                        }
                    }
                };
                while a < b {
                    let mid = &b - &(&b - &a).div_floor(&two);
                    if self.none(i, false, &mid) {
                        b = &mid - &one
                    } else {
                        a = mid
                    }
                }
                Some(a)
            }
        };
        let end = |v: Option<Int>, inf: End| v.map_or(inf, |v| End::Fin(Num::from(&v)));
        set.meet(&IntervalSet::range(
            end(new_lo, End::NegInf),
            end(new_hi, End::PosInf),
        ))
    }

    /// Tightens the hull in `out` of each symbol of `ks`, with the candidates `open` gives
    /// for its infinite ends.
    fn tighten_all(
        &mut self,
        out: &mut [Result<IntervalSet, Refusal>],
        open: &HashMap<usize, (Option<Int>, Option<Int>)>,
    ) {
        let no = (None, None);
        for i in 0..self.ks.len() {
            let k = self.ks[i].0;
            if let Ok(s) = &out[k] {
                let s = s.clone();
                out[k] = Ok(self.tighten(i, s, open.get(&k).unwrap_or(&no)));
            }
        }
    }
}

/// The values of `sym` that the rows of `rows` with `sym` alone allow, with the bounds that
/// the rows give each other by [`propagate`] added: where the rows keep other atoms (a core,
/// [`shadow`]), `2·a + z + 15 >= 0` with `a <= 7` gives `z >= -29` (seed 15 case 331 of
/// `l01_39_reduced_product::pendants`, item PRES-pendants-wider). Each bound holds at every
/// point of `rows`, so the set holds every value of `sym` over `rows`. The cost is linear in
/// the rows' terms ([`propagate`]).
fn bounds_alone(sym: &Atom, rows: &[Con]) -> IntervalSet {
    let mut added = Vec::new();
    if rows.iter().any(|c| c.lin.terms.len() > 1) {
        propagate(
            &rows.iter().collect::<Vec<_>>(),
            &HashMap::new(),
            &mut added,
        );
    }
    let alone = (rows.iter().chain(&added))
        .filter(|c| c.lin.terms.len() == 1)
        .filter_map(|c| Some((c.lin.terms.get(sym)?.clone(), c.lin.constant.clone(), c.rel)));
    let Some((lo, hi)) = int_bounds(alone) else {
        return IntervalSet::empty();
    };
    let end = |v: Option<Int>, inf: End| v.map_or(inf, |v| End::Fin(Num::from(&v)));
    IntervalSet::range(end(lo, End::NegInf), end(hi, End::PosInf))
}

/// The least and greatest integers `x` (`None`: unbounded) with `a·x + k >= 0`, or `== 0` by
/// its relation, for each `(a, k, rel)` of `rows`, `a` not zero; `None` when there is none.
fn int_bounds(
    rows: impl IntoIterator<Item = (Int, Int, Rel)>,
) -> Option<(Option<Int>, Option<Int>)> {
    let (mut lo, mut hi): (Option<Int>, Option<Int>) = (None, None);
    let mut raise = |v: Int| lo = Some(lo.take().map_or(v.clone(), |l| l.max(v)));
    let mut lower = |v: Int| hi = Some(hi.take().map_or(v.clone(), |h| h.min(v)));
    for (a, k, rel) in rows {
        // `x >= -k / a` rounded up when `a` is above zero, `x <= k / -a` rounded down when
        // below; an equality is both.
        match rel {
            Rel::Ge if a.is_positive() => raise(-&k.div_floor(&a)),
            Rel::Ge => lower(k.div_floor(&-&a)),
            Rel::Eq => {
                if !k.mod_floor(&a).is_zero() {
                    return None;
                }
                let v = -&k.div_floor(&a);
                raise(v.clone());
                lower(v);
            }
        }
    }
    if let (Some(l), Some(h)) = (&lo, &hi)
        && l > h
    {
        return None;
    }
    Some((lo, hi))
}

/// An integer point of `rows`, or `None` when none is found so: [`shadow`] eliminates every
/// atom it can, [`solve`] finds a point of the rows left, and each atom eliminated, the last
/// first, takes the least value (or the greatest, with no least) that its rows allow at the
/// values of the atoms eliminated after it and of those left; with `greatest`, the greatest
/// value (or the least, with no greatest). Each elimination is exact over
/// the integers, so such a value exists; `None` comes when the rows have no point or the
/// solver refuses the rows left. Each atom of a row, a product too, is read as its own value,
/// as the solver reads it. The cost is that of [`shadow`] and of one solve of the rows left.
fn point_of(rows: &[Con], greatest: bool) -> Option<Model> {
    let mut log = Vec::new();
    let left = shadow_logged(rows, &|_| false, false, false, Some(&mut log))?;
    let mut model = solve(&left, true).ok()??;
    for (x, rows) in log.into_iter().rev() {
        let at = rows.iter().map(|c| {
            let mut k = c.lin.constant.clone();
            for (b, v) in c.lin.terms.iter().filter(|(b, _)| **b != x) {
                k = &k + &(v * model.get(b).unwrap_or(&Int::ZERO));
            }
            (c.lin.terms[&x].clone(), k, c.rel)
        });
        let v = match int_bounds(at)? {
            (_, Some(hi)) if greatest => hi,
            (Some(lo), _) => lo,
            (None, Some(hi)) => hi,
            (None, None) => Int::ZERO,
        };
        model.insert(x, v);
    }
    Some(model)
}

/// The least and greatest values of a symbol over a formula, given a point `m` of it: the two
/// sides [`hull_side`] finds.
fn hull_from(c: &Formula, sym: &Atom, m: &Model) -> Result<IntervalSet, Refusal> {
    let end = |dir: i64, inf: End| -> Result<End, Refusal> {
        Ok(hull_side(c, sym, m, dir)?.map_or(inf, |v| End::Fin(Num::from(&v))))
    };
    Ok(IntervalSet::range(
        end(-1, End::NegInf)?,
        end(1, End::PosInf)?,
    ))
}

thread_local! {
    /// The sides [`hull_side`] has found on this thread since [`hull_sides_asked`] was last
    /// called.
    static SIDES: Cell<u64> = const { Cell::new(0) };
}

/// The number of sides of hulls (the least or the greatest value of one atom over a formula)
/// that the solver has been asked for on this thread since the last call, which resets it. A
/// test reads it to show that the bounds of the factors of products were found without the
/// solver.
pub fn hull_sides_asked() -> u64 {
    SIDES.replace(0)
}

/// The greatest value (`dir` 1) or the least (`dir` -1) of a symbol over a formula, given a
/// point `m` of it; `None` when there is none. A bound is found by the monotone question "is
/// there a point with the symbol at least `v`" (or at most). Where `c`'s constraints with the
/// symbol alone bound that side ([`alone_end`]), the bound lies between the point's value and
/// that end, and it is searched from both, [`side_within`]: no question of an unbounded side
/// is asked, and a bound at the end, or a few steps inside it, is found by a few questions
/// whatever the point's distance. Otherwise a side with no bound is found by one question,
/// [`unbounded`], and a bound by a search outward from the point's value with steps that
/// double, then by bisection, so it takes O(log d) questions for a bound at distance d, each
/// on integers of O(log d) bits. Every bound is exact at any magnitude.
fn hull_side(c: &Formula, sym: &Atom, m: &Model, dir: i64) -> Result<Option<Int>, Refusal> {
    SIDES.set(SIDES.get() + 1);
    let x = Lin::atom(sym.clone());
    // Whether some point has the symbol at `v` or beyond it, going `dir`: false far enough
    // that way, since the side is bounded, and true at the point's value.
    let holds = |v: &Int| -> Result<bool, Refusal> {
        let beyond = if dir > 0 {
            Con::ge(&x, &Lin::constant(v.clone()))
        } else {
            Con::ge(&Lin::constant(v.clone()), &x)
        };
        decide_inner(&Formula::and(vec![c.clone(), Formula::Con(beyond)]))
    };
    // The search from both ends answers what the search below answers, the one bound, where
    // its questions are answered; where one is refused, the search below is run as before
    // (item PRES-project-each-cost: a disjunct `1024 * q <= x`, `1024 * q >= x - 1023`,
    // `x == 2 * e`, `x` in a gap's bounds, read about 20 questions for each side, and now 3).
    if let Some(end) = alone_end(c, sym, dir)
        && let Some(at) = m.get(sym)
        && (if dir > 0 { *at <= end } else { *at >= end })
        && let Ok(side) = side_within(&holds, at.clone(), end, dir)
    {
        return Ok(Some(side));
    }
    if unbounded(c, sym, dir)? {
        return Ok(None);
    }
    let at = m.get(sym).cloned().unwrap_or(Int::ZERO);
    let step_dir = Int::from(dir);
    let (mut good, mut step) = (at, Int::ONE);
    let bad = loop {
        let next = &good + &(&step_dir * &step);
        if !holds(&next)? {
            break next;
        }
        good = next;
        step = &step + &step;
    };
    let (mut good, mut bad) = (good, bad);
    let two = Int::from(2);
    while (&bad - &good).abs() > Int::ONE {
        let mid = &good + &(&bad - &good).div_floor(&two);
        if holds(&mid)? { good = mid } else { bad = mid }
    }
    Ok(Some(good))
}

/// The last value `v` going `dir` from `good`, where `holds(good)`, with `holds(v)`, given that
/// `holds` is false past `end` and monotone (true up to the side, false past it). The questions
/// alternate between one inward from the false end, at `end` first, and one outward from the
/// true end, each side's step doubling while its answers move that end; a question that would
/// pass the other end bisects instead. A side `e` inside `end` and `d` past the point is then
/// found by O(log min(d, e)) questions plus a bisection of the last step's width, at most about
/// twice the questions of the search outward alone. The first refusal is returned.
fn side_within(
    holds: &impl Fn(&Int) -> Result<bool, Refusal>,
    good: Int,
    end: Int,
    dir: i64,
) -> Result<Int, Refusal> {
    let way = Int::from(dir);
    let two = Int::from(2);
    let (mut good, mut bad) = (good, &end + &way);
    let (mut outward, mut inward) = (Int::ONE, Int::ONE);
    let mut from_end = true;
    while (&bad - &good).abs() > Int::ONE {
        let v = if from_end {
            &bad - &(&way * &inward)
        } else {
            &good + &(&way * &outward)
        };
        let between = if dir > 0 {
            v > good && v < bad
        } else {
            v < good && v > bad
        };
        let v = if between {
            v
        } else {
            &good + &(&bad - &good).div_floor(&two)
        };
        if holds(&v)? {
            good = v;
            if !from_end {
                outward = &outward + &outward;
            }
        } else {
            bad = v;
            if from_end {
                inward = &inward + &inward;
            }
        }
        from_end = !from_end;
    }
    Ok(good)
}

/// The greatest value (`dir` 1) or the least (`dir` -1) of `sym` that the constraints of `c`
/// with `sym` alone allow, `c` read as a conjunction: a constraint of it, or one directly
/// inside it. `None` when they give none that way, or have no point. Every point of `c` holds
/// them, so the side of `sym` over `c` is no further out. One pass over `c`'s parts.
fn alone_end(c: &Formula, sym: &Atom, dir: i64) -> Option<Int> {
    let cons: Vec<&Con> = match c {
        Formula::Con(k) => vec![k],
        Formula::And(fs) => (fs.iter())
            .filter_map(|f| match f {
                Formula::Con(k) => Some(k),
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    };
    let alone = (cons.into_iter())
        .filter(|k| k.lin.terms.len() == 1)
        .filter_map(|k| Some((k.lin.terms.get(sym)?.clone(), k.lin.constant.clone(), k.rel)));
    let (lo, hi) = int_bounds(alone)?;
    if dir > 0 { hi } else { lo }
}

/// The hull of every atom of `cons`, constraints with a point `m`, when each is a difference
/// constraint (`x - y + k >= 0`, `x - y + k == 0`) or a bound (`±x + k >= 0`, `x + k == 0`);
/// `None` when one is not. Such rows are totally unimodular, so the integer points of the
/// constraints with an atom fixed at any value between its least and greatest are found by the
/// same constraints, and those two values are shortest paths: with a node `z` standing for 0,
/// `y <= x + k` is an edge `x → y` of weight `k`, a bound is an edge to or from `z`, and an
/// atom's greatest value is its distance from `z`, its least the negated distance to `z`
/// (Shostak, "Deciding linear inequalities by computing loop residues", J. ACM 28, 1981).
/// The point gives a potential under which no edge has a negative reduced weight, so each
/// side is one Dijkstra search: O(m log n) for m constraints over n atoms, against
/// [`hull_from`]'s O(log d) questions of the whole group for each atom. The bounds are those
/// [`hull_from`] finds, exact at any magnitude.
fn difference_hulls(cons: &[&Con], m: &Model) -> Option<HashMap<Atom, IntervalSet>> {
    let end = |e: Option<Int>, inf: End| e.map_or(inf, |v| End::Fin(Num::from(&v)));
    Some(
        difference_ends(cons, m)?
            .into_iter()
            .map(|(a, (lo, hi))| {
                (
                    a,
                    IntervalSet::range(end(lo, End::NegInf), end(hi, End::PosInf)),
                )
            })
            .collect(),
    )
}

/// The least and greatest value of each atom, `None` where there is none.
type Ends = (Option<Int>, Option<Int>);

/// [`difference_hulls`] with each hull as its two ends.
fn difference_ends(cons: &[&Con], m: &Model) -> Option<HashMap<Atom, Ends>> {
    Some(Differences::of(cons, m)?.ends())
}

/// Difference constraints and bounds with a point, as the graph of [`difference_hulls`]: node 0
/// is `z`, standing for 0, and the atoms follow in order of first use; `y <= x + k` is the edge
/// `x → y` of weight `k`, held in `out` at `x` and in `back` at `y`; `p` is the point's value at
/// each node, 0 at `z`.
struct Differences<'a> {
    atoms: Vec<&'a Atom>,
    node: HashMap<&'a Atom, usize>,
    out: Vec<Vec<(usize, Int)>>,
    back: Vec<Vec<(usize, Int)>>,
    p: Vec<Int>,
}

/// Which way a search of [`Differences`] goes: `Up` along the edges, so that a node `v` at
/// distance `d` from a source `s` has `v <= s + d`, or `Down` against them, so that
/// `v >= s - d`.
#[derive(Clone, Copy)]
enum Along {
    Up,
    Down,
}

impl<'a> Differences<'a> {
    /// The graph of `cons`, constraints with the point `m`; `None` when one is not a difference
    /// constraint or a bound, or `m` gives no value to one of their atoms.
    fn of(cons: &[&'a Con], m: &Model) -> Option<Differences<'a>> {
        let mut node: HashMap<&Atom, usize> = HashMap::new();
        let mut atoms: Vec<&Atom> = Vec::new();
        let mut out: Vec<Vec<(usize, Int)>> = vec![Vec::new()];
        for c in cons {
            let mut ends: Vec<(usize, bool)> = Vec::with_capacity(2);
            for (a, k) in &c.lin.terms {
                if !k.is_unit() {
                    return None;
                }
                let i = *node.entry(a).or_insert_with(|| {
                    atoms.push(a);
                    out.push(Vec::new());
                    atoms.len()
                });
                ends.push((i, k.is_positive()));
            }
            // The term as `x - y + k` with `x` or `y` possibly `z`: the edge `x → y` of
            // weight `k`.
            let (x, y) = match ends[..] {
                [(i, true)] => (i, 0),
                [(i, false)] => (0, i),
                [(i, true), (j, false)] => (i, j),
                [(i, false), (j, true)] => (j, i),
                _ => return None,
            };
            out[x].push((y, c.lin.constant.clone()));
            if c.rel == Rel::Eq {
                out[y].push((x, -&c.lin.constant));
            }
        }
        let mut p: Vec<Int> = Vec::with_capacity(out.len());
        p.push(Int::ZERO);
        for a in &atoms {
            p.push(m.get(*a)?.clone());
        }
        let mut back: Vec<Vec<(usize, Int)>> = vec![Vec::new(); out.len()];
        for (u, es) in out.iter().enumerate() {
            for (v, w) in es {
                // The point meets every row, so no reduced weight is negative.
                if (w + &p[u]) < p[*v] {
                    return None;
                }
                back[*v].push((u, w.clone()));
            }
        }
        Some(Differences {
            atoms,
            node,
            out,
            back,
            p,
        })
    }

    /// The distance of each node from the nearest of `sources` going `along`, with that
    /// source, or `None` where no source reaches or two are nearest. Each edge `u → v` of
    /// weight `w` is taken at its reduced weight `w + sign·(p(u) - p(v))` (`sign` 1 up, -1
    /// down), which the point keeps from being negative, so the search is Dijkstra's from all
    /// the sources at once. Nearest is by reduced distance, which is the slack at the point of
    /// the bound the path gives. A source is its own nearest, through the empty path. A node
    /// that two sources reach at its least reduced distance has no nearest, and nor has a node
    /// whose shortest paths pass through one: choosing among them could only go by their places
    /// in `sources`, that is by name, and the checker never lets a name change an answer
    /// (C2-chain-general; `l01_38_presburger::ladder::the_bounds_found_do_not_depend_on_names`).
    /// Each node is expanded at most twice at its least distance, once with one nearest source
    /// and once with none, so the cost is O(m log n) for m edges over n nodes, and the result
    /// does not depend on the order of the edges. Unless `through_z`, the search does not enter
    /// `z`, so a path is a chain of difference constraints alone and not of a bound on one end
    /// joined to a bound on the other.
    fn search(
        &self,
        along: Along,
        sources: &[usize],
        through_z: bool,
    ) -> Vec<Option<(Int, usize)>> {
        let (edges, sign) = match along {
            Along::Up => (&self.out, Int::ONE),
            Along::Down => (&self.back, Int::from(-1)),
        };
        let p = &self.p;
        // Each node's least reduced distance, with its one nearest source, or `None` for two
        // or more; and how far it has been expanded: 0 not yet, 1 with one source, 2 with none.
        let mut label: Vec<Option<(Int, Option<usize>)>> = vec![None; edges.len()];
        let mut expanded = vec![0u8; edges.len()];
        let mut heap = std::collections::BinaryHeap::new();
        for &s in sources {
            label[s] = Some((Int::ZERO, Some(s)));
            heap.push(std::cmp::Reverse((Int::ZERO, s)));
        }
        while let Some(std::cmp::Reverse((d, u))) = heap.pop() {
            let Some((du, from)) = label[u].clone() else {
                continue;
            };
            let stage = if from.is_some() { 1 } else { 2 };
            if d > du || expanded[u] >= stage {
                continue;
            }
            expanded[u] = stage;
            for (v, w) in &edges[u] {
                if (*v == 0 && !through_z)
                    || label[*v].as_ref().is_some_and(|(_, s)| *s == Some(*v))
                {
                    continue;
                }
                let nd = &d + &(w + &(&sign * &(&p[u] - &p[*v])));
                let next = match &label[*v] {
                    Some((old, _)) if nd > *old => continue,
                    Some((old, s)) if nd == *old => {
                        if s.is_none() || *s == from {
                            continue;
                        }
                        None
                    }
                    _ => from,
                };
                label[*v] = Some((nd.clone(), next));
                heap.push(std::cmp::Reverse((nd, *v)));
            }
        }
        // Back from reduced distances: `d(v) = d'(v) - sign·(p(s) - p(v))` for the source `s`.
        label
            .into_iter()
            .enumerate()
            .map(|(v, l)| {
                let (d, s) = l?;
                let s = s?;
                Some((&d - &(&sign * &(&p[s] - &p[v])), s))
            })
            .collect()
    }

    /// The least and greatest value of each atom: the negated distance to `z` and the distance
    /// from it.
    fn ends(&self) -> HashMap<Atom, Ends> {
        let up = self.search(Along::Up, &[0], true);
        let down = self.search(Along::Down, &[0], true);
        self.atoms
            .iter()
            .enumerate()
            .map(|(k, a)| {
                (
                    (*a).clone(),
                    (
                        down[k + 1].as_ref().map(|(d, _)| -d),
                        up[k + 1].as_ref().map(|(d, _)| d.clone()),
                    ),
                )
            })
            .collect()
    }
}

/// Whether `c` is a difference constraint or a bound, a row [`difference_ends`] takes.
fn is_difference(c: &Con) -> bool {
    let mut ks = c.lin.terms.values();
    match (ks.next(), ks.next(), ks.next()) {
        (Some(k), None, None) => k.is_unit(),
        (Some(j), Some(k), None) => {
            j.is_unit() && k.is_unit() && j.is_positive() != k.is_positive()
        }
        _ => false,
    }
}

/// The exact domain of each atom of a component whose base rows are difference rows and
/// bounds and whose disjunctions name atoms of one or two tie classes each (atoms whose
/// differences the base fixes), with difference rows and bounds in every disjunct, when the
/// component, with its tie classes contracted, is a forest. Two passes of arc revision over a forest
/// give each atom the values it takes at some point (Freuder 1982). Also, for each
/// disjunction, whether its component was handled so.
fn forest_domains(
    linked: &Linked,
    ors: &[Vec<Rc<Parts>>],
    model: &Model,
) -> (HashMap<Atom, IntervalSet>, Vec<bool>) {
    let mut handled = vec![false; ors.len()];
    let mut doms: HashMap<Atom, IntervalSet> = HashMap::new();
    let n_base = linked.parent.len();
    let mut free: Vec<&Atom> = Vec::new();
    let mut free_id: HashMap<&Atom, usize> = HashMap::new();
    let mut units_of: Vec<Vec<usize>> = Vec::with_capacity(ors.len());
    for ds in ors {
        let atoms: BTreeSet<&Atom> = ds.iter().flat_map(|d| d.atoms().iter()).collect();
        let us: Vec<usize> = atoms
            .iter()
            .map(|a| match linked.ids.get(*a) {
                Some(i) => linked.root(*i),
                None => {
                    let k = *free_id.entry(*a).or_insert_with(|| {
                        free.push(*a);
                        free.len() - 1
                    });
                    n_base + k
                }
            })
            .collect();
        units_of.push(us);
    }
    let n_units = n_base + free.len();
    let mut uf: Vec<usize> = (0..n_units).collect();
    fn find(uf: &mut [usize], mut i: usize) -> usize {
        while uf[i] != i {
            uf[i] = uf[uf[i]];
            i = uf[i];
        }
        i
    }
    for us in &units_of {
        for u in us.iter().skip(1) {
            let (a, b) = (find(&mut uf, us[0]), find(&mut uf, *u));
            if a != b {
                uf[a.max(b)] = a.min(b);
            }
        }
    }
    // Each component, by its least unit.
    let mut comps: BTreeMap<usize, ForestComponent> = BTreeMap::new();
    for (j, ds) in ors.iter().enumerate() {
        let Some(&u0) = units_of[j].first() else {
            continue;
        };
        let c = find(&mut uf, u0);
        let e = comps.entry(c).or_insert_with(|| ForestComponent {
            groups: BTreeSet::new(),
            free: Vec::new(),
            ors: Vec::new(),
            simple: true,
        });
        e.simple &= ds
            .iter()
            .all(|d| d.ors.is_empty() && d.cons.iter().all(is_difference));
        e.ors.push(j);
        for &u in &units_of[j] {
            if u < n_base {
                e.groups.insert(u);
            }
        }
    }
    for (k, a) in free.iter().enumerate() {
        let c = find(&mut uf, n_base + k);
        if let Some(e) = comps.get_mut(&c) {
            e.free.push(*a);
        }
    }
    for ForestComponent {
        groups,
        free: free_atoms,
        ors: js,
        simple,
    } in comps.values()
    {
        if !*simple {
            continue;
        }
        let cons: Vec<&Con> = groups
            .iter()
            .flat_map(|r| linked.held[*r].iter().map(|i| &linked.cons[*i]))
            .collect();
        if !cons.iter().all(|c| is_difference(c)) {
            continue;
        }
        let g = if cons.is_empty() {
            Differences {
                atoms: Vec::new(),
                node: HashMap::new(),
                out: vec![Vec::new()],
                back: vec![Vec::new()],
                p: vec![Int::ZERO],
            }
        } else {
            match Differences::of(&cons, model) {
                Some(g) => g,
                None => continue,
            }
        };
        if let Some(d) = forest_component_domains(&g, free_atoms, js, ors) {
            doms.extend(d);
            for &j in js {
                handled[j] = true;
            }
        }
    }
    (doms, handled)
}

/// One component for [`forest_domains`]: its groups of base rows, its atoms in no group, its
/// disjunctions, and whether every disjunct holds only difference rows and bounds.
struct ForestComponent<'a> {
    groups: BTreeSet<usize>,
    free: Vec<&'a Atom>,
    ors: Vec<usize>,
    simple: bool,
}

/// `set` with each piece moved by `[lo, hi]` (`None`: unbounded): `{x + t : x in set, lo <= t
/// <= hi}`.
fn shifted(set: &IntervalSet, lo: &Option<Int>, hi: &Option<Int>) -> IntervalSet {
    if let (Some(l), Some(h)) = (lo, hi)
        && l > h
    {
        return IntervalSet::empty();
    }
    let add = |e: &End, k: &Option<Int>| match (e, k) {
        (End::Fin(x), Some(k)) => End::Fin(x + &Num::from(k)),
        (End::Fin(_), None) => End::NegInf,
        (e, _) => e.clone(),
    };
    IntervalSet::from_pieces(
        set.pieces()
            .map(|(a, b)| {
                let lo_end = add(a, lo);
                let hi_end = match (b, hi) {
                    (End::Fin(x), Some(k)) => End::Fin(x + &Num::from(k)),
                    (End::Fin(_), None) => End::PosInf,
                    (e, _) => e.clone(),
                };
                (lo_end, hi_end)
            })
            .collect(),
    )
}

/// The meet (`meet`) or the join of `sets`, taken in pairs level by level, so that `k` sets
/// of `P` intervals in all cost O(P log k), where one after another they cost O(P k): the
/// `n` holes of one atom, each a disjunction, are met into one set.
fn fold_in_pairs(mut sets: Vec<IntervalSet>, meet: bool) -> IntervalSet {
    if sets.is_empty() {
        return if meet {
            IntervalSet::top()
        } else {
            IntervalSet::empty()
        };
    }
    while sets.len() > 1 {
        let mut next = Vec::with_capacity(sets.len().div_ceil(2));
        let mut it = sets.into_iter();
        while let Some(a) = it.next() {
            next.push(match it.next() {
                Some(b) if meet => a.meet(&b),
                Some(b) => a.join(&b),
                None => a,
            });
        }
        sets = next;
    }
    sets.pop().expect("one set")
}

fn lower_to(a: &mut Option<Int>, v: Int) {
    if a.as_ref().is_none_or(|x| v < *x) {
        *a = Some(v);
    }
}

fn raise_to(a: &mut Option<Int>, v: Int) {
    if a.as_ref().is_none_or(|x| v > *x) {
        *a = Some(v);
    }
}

/// One disjunct on an edge or a class: the values of the first class (`ia`), of the second
/// (`ib`), and the bounds of `second - first`.
struct ForestPart {
    ia: IntervalSet,
    ib: IntervalSet,
    lo: Option<Int>,
    hi: Option<Int>,
}

/// An edge between classes `a < b`: bounds of `rep(b) - rep(a)`, and the disjunction on it.
struct ForestEdge {
    a: usize,
    b: usize,
    lo: Option<Int>,
    hi: Option<Int>,
    parts: Option<Vec<ForestPart>>,
}

fn forest_component_domains(
    g: &Differences,
    free_atoms: &[&Atom],
    js: &[usize],
    ors: &[Vec<Rc<Parts>>],
) -> Option<HashMap<Atom, IntervalSet>> {
    // Nodes: 0 is z, 1..=atoms the graph's atoms, then the free atoms.
    let n0 = g.out.len();
    let n = n0 + free_atoms.len();
    let mut node: HashMap<&Atom, usize> = g.node.iter().map(|(a, v)| (*a, *v)).collect();
    for (k, a) in free_atoms.iter().enumerate() {
        node.insert(*a, n0 + k);
    }
    let p = |v: usize| -> Int { if v < n0 { g.p[v].clone() } else { Int::ZERO } };
    // Tie classes: strongly connected components of the edges of reduced weight 0 between
    // atoms (Kosaraju, explicit stacks).
    let mut tout: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut tin: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (u, es) in g.out.iter().enumerate().skip(1) {
        for (v, w) in es {
            if *v != 0 && (w + &(&g.p[u] - &g.p[*v])).is_zero() {
                tout[u].push(*v);
                tin[*v].push(u);
            }
        }
    }
    let mut seen = vec![false; n];
    let mut post: Vec<usize> = Vec::with_capacity(n);
    for s in 1..n {
        if seen[s] {
            continue;
        }
        seen[s] = true;
        let mut st = vec![(s, 0usize)];
        while let Some((u, i)) = st.pop() {
            if i < tout[u].len() {
                st.push((u, i + 1));
                let v = tout[u][i];
                if !seen[v] {
                    seen[v] = true;
                    st.push((v, 0));
                }
            } else {
                post.push(u);
            }
        }
    }
    let mut class = vec![usize::MAX; n];
    let mut reps: Vec<usize> = Vec::new();
    for &s in post.iter().rev() {
        if class[s] != usize::MAX {
            continue;
        }
        let c = reps.len();
        reps.push(s);
        class[s] = c;
        let mut st = vec![s];
        while let Some(u) = st.pop() {
            for &v in &tin[u] {
                if class[v] == usize::MAX {
                    class[v] = c;
                    st.push(v);
                }
            }
        }
    }
    let off: Vec<Int> = (0..n)
        .map(|v| {
            if v == 0 {
                Int::ZERO
            } else {
                &p(v) - &p(reps[class[v]])
            }
        })
        .collect();
    let nc = reps.len();
    let mut dom: Vec<IntervalSet> = vec![IntervalSet::top(); nc];
    let fin = |k: Int| End::Fin(Num::from(&k));
    let mut edges: Vec<ForestEdge> = Vec::new();
    let mut key: HashMap<(usize, usize), usize> = HashMap::new();
    let mut cuf: Vec<usize> = (0..nc).collect();
    fn find(uf: &mut [usize], mut i: usize) -> usize {
        while uf[i] != i {
            uf[i] = uf[uf[i]];
            i = uf[i];
        }
        i
    }
    // The edge between classes `x` and `y`, made when new; `None` when it closes a cycle.
    let mut edge = |x: usize,
                    y: usize,
                    edges: &mut Vec<ForestEdge>,
                    key: &mut HashMap<(usize, usize), usize>|
     -> Option<usize> {
        let k = (x.min(y), x.max(y));
        if let Some(e) = key.get(&k) {
            return Some(*e);
        }
        let (a, b) = (find(&mut cuf, x), find(&mut cuf, y));
        if a == b {
            return None;
        }
        cuf[a.max(b)] = a.min(b);
        edges.push(ForestEdge {
            a: k.0,
            b: k.1,
            lo: None,
            hi: None,
            parts: None,
        });
        key.insert(k, edges.len() - 1);
        Some(edges.len() - 1)
    };
    // `v <= u + k` between atoms, as a bound on `rep(b) - rep(a)` of `(lo, hi)`.
    let le = |u: usize, v: usize, k: &Int, a: usize, lo: &mut Option<Int>, hi: &mut Option<Int>| {
        // rep(cv) - rep(cu) <= k + off(u) - off(v)
        let kk = &(k + &off[u]) - &off[v];
        if class[u] == a {
            lower_to(hi, kk);
        } else {
            raise_to(lo, -&kk);
        }
    };
    for u in 0..n0 {
        for (v, w) in &g.out[u] {
            let v = *v;
            match (u, v) {
                (0, v) => {
                    let c = class[v];
                    dom[c] = dom[c].meet(&IntervalSet::range(End::NegInf, fin(w - &off[v])));
                }
                (u, 0) => {
                    let c = class[u];
                    dom[c] = dom[c].meet(&IntervalSet::range(fin(&(-w) - &off[u]), End::PosInf));
                }
                (u, v) if class[u] == class[v] => {}
                (u, v) => {
                    let e = edge(class[u], class[v], &mut edges, &mut key)?;
                    let a = edges[e].a;
                    let (mut lo, mut hi) = (edges[e].lo.take(), edges[e].hi.take());
                    le(u, v, w, a, &mut lo, &mut hi);
                    edges[e].lo = lo;
                    edges[e].hi = hi;
                }
            }
        }
    }
    // The disjunctions; those over one class are met into its set at the end, all at once.
    let mut unary: Vec<Vec<IntervalSet>> = vec![Vec::new(); nc];
    for &j in js {
        let mut cls: Vec<usize> = Vec::new();
        for d in &ors[j] {
            for a in d.atoms().iter() {
                cls.push(class[*node.get(a)?]);
            }
        }
        cls.sort_unstable();
        cls.dedup();
        let (ca, cb) = match cls[..] {
            [c] => (c, None),
            [x, y] => (x, Some(y)),
            _ => return None,
        };
        let mut parts: Vec<ForestPart> = Vec::new();
        'd: for d in &ors[j] {
            let mut part = ForestPart {
                ia: IntervalSet::top(),
                ib: IntervalSet::top(),
                lo: None,
                hi: None,
            };
            for c in &d.cons {
                let ts: Vec<(usize, bool)> = c
                    .lin
                    .terms
                    .iter()
                    .map(|(a, k)| node.get(a).map(|v| (*v, k.is_positive())))
                    .collect::<Option<_>>()?;
                // Each row as edges `x → y` of weight `k` (`y <= x + k`), `x` or `y` 0 for z.
                let (x, y) = match ts[..] {
                    [(i, true)] => (i, 0),
                    [(i, false)] => (0, i),
                    [(i, true), (j2, false)] => (i, j2),
                    [(i, false), (j2, true)] => (j2, i),
                    _ => return None,
                };
                let k = c.lin.constant.clone();
                let mut rows = vec![(x, y, k.clone())];
                if c.rel == Rel::Eq {
                    rows.push((y, x, -&k));
                }
                for (x, y, k) in rows {
                    match (x, y) {
                        (0, v) => {
                            let s = IntervalSet::range(End::NegInf, fin(&k - &off[v]));
                            if class[v] == ca {
                                part.ia = part.ia.meet(&s)
                            } else {
                                part.ib = part.ib.meet(&s)
                            }
                        }
                        (u, 0) => {
                            let s = IntervalSet::range(fin(&(-&k) - &off[u]), End::PosInf);
                            if class[u] == ca {
                                part.ia = part.ia.meet(&s)
                            } else {
                                part.ib = part.ib.meet(&s)
                            }
                        }
                        (u, v) if class[u] == class[v] => {
                            // A fixed difference: holds or empties the disjunct.
                            if &off[v] - &off[u] > k {
                                continue 'd;
                            }
                        }
                        (u, v) => le(u, v, &k, ca, &mut part.lo, &mut part.hi),
                    }
                }
            }
            if part.ia.is_empty() || part.ib.is_empty() {
                continue;
            }
            parts.push(part);
        }
        match cb {
            None => {
                unary[ca].push(fold_in_pairs(
                    parts.iter().map(|pt| pt.ia.clone()).collect(),
                    false,
                ));
            }
            Some(cb) => {
                let e = edge(ca, cb, &mut edges, &mut key)?;
                if edges[e].parts.is_some() {
                    return None;
                }
                edges[e].parts = Some(parts);
            }
        }
    }
    for (d, us) in dom.iter_mut().zip(unary) {
        if !us.is_empty() {
            *d = d.meet(&fold_in_pairs(us, true));
        }
    }
    // Two passes of arc revision over each tree.
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); nc];
    for (i, e) in edges.iter().enumerate() {
        adj[e.a].push(i);
        adj[e.b].push(i);
    }
    let revise = |e: &ForestEdge, x: usize, dx: &IntervalSet| -> IntervalSet {
        // The values of the other end `y` that some value of `x` in `dx` supports.
        let fwd = x == e.a;
        let orient = |lo: &Option<Int>, hi: &Option<Int>| -> (Option<Int>, Option<Int>) {
            if fwd {
                (lo.clone(), hi.clone())
            } else {
                (hi.as_ref().map(|h| -h), lo.as_ref().map(|l| -l))
            }
        };
        match &e.parts {
            None => {
                let (lo, hi) = orient(&e.lo, &e.hi);
                shifted(dx, &lo, &hi)
            }
            Some(parts) => {
                let mut s: Vec<IntervalSet> = Vec::with_capacity(parts.len());
                for pt in parts {
                    let (mut lo, mut hi) = (e.lo.clone(), e.hi.clone());
                    if let Some(l) = &pt.lo {
                        raise_to(&mut lo, l.clone())
                    }
                    if let Some(h) = &pt.hi {
                        lower_to(&mut hi, h.clone())
                    }
                    let (lo, hi) = orient(&lo, &hi);
                    let (ix, iy) = if fwd {
                        (&pt.ia, &pt.ib)
                    } else {
                        (&pt.ib, &pt.ia)
                    };
                    s.push(shifted(&dx.meet(ix), &lo, &hi).meet(iy));
                }
                fold_in_pairs(s, false)
            }
        }
    };
    // Each tree in BFS order from its least class: (node, parent, edge).
    let mut visited = vec![false; nc];
    let mut orders: Vec<Vec<(usize, usize, usize)>> = Vec::new();
    for root in 0..nc {
        if visited[root] {
            continue;
        }
        visited[root] = true;
        let mut order: Vec<(usize, usize, usize)> = Vec::new();
        let mut q = std::collections::VecDeque::from([root]);
        while let Some(u) = q.pop_front() {
            for &ei in &adj[u] {
                let e = &edges[ei];
                let v = if e.a == u { e.b } else { e.a };
                if !visited[v] {
                    visited[v] = true;
                    order.push((v, u, ei));
                    q.push_back(v);
                }
            }
        }
        orders.push(order);
    }
    let hull = |s: &IntervalSet| match s.bounds() {
        Some((l, h)) => IntervalSet::range(l.clone(), h.clone()),
        None => IntervalSet::empty(),
    };
    // First the two passes on the hulls alone, each set one interval, so that the exact
    // passes below start from sets no wider than the bounds the whole tree gives: a set built
    // leaves to root then holds only values inside them (`x[k+1] - x[k]` in {0, 10} with both
    // ends 0 keeps `{0}` at every step, not `k + 1` intervals).
    let mut hdom: Vec<IntervalSet> = dom.iter().map(hull).collect();
    for order in &orders {
        for &(v, u, ei) in order.iter().rev() {
            let s = hull(&revise(&edges[ei], v, &hdom[v]));
            hdom[u] = hdom[u].meet(&s);
        }
        for &(v, u, ei) in order {
            let s = hull(&revise(&edges[ei], u, &hdom[u]));
            hdom[v] = hdom[v].meet(&s);
        }
    }
    for (d, h) in dom.iter_mut().zip(&hdom) {
        *d = d.meet(h);
    }
    for order in &orders {
        for &(v, u, ei) in order.iter().rev() {
            let s = revise(&edges[ei], v, &dom[v]);
            dom[u] = dom[u].meet(&s);
        }
        for &(v, u, ei) in order {
            let s = revise(&edges[ei], u, &dom[u]);
            dom[v] = dom[v].meet(&s);
        }
    }
    if dom.iter().any(IntervalSet::is_empty) {
        return None;
    }
    Some(
        (1..n)
            .map(|v| {
                let c = &off[v];
                let k = Some(c.clone());
                (
                    (if v < n0 {
                        g.atoms[v - 1]
                    } else {
                        free_atoms[v - n0]
                    })
                    .clone(),
                    shifted(&dom[class[v]], &k, &k),
                )
            })
            .collect(),
    )
}

/// The bounds that the row `lin >= 0` gives each of its atoms from the bounds `b` of the
/// others, pushed onto `out` as rows `x - lo >= 0` and `hi - x >= 0`: with `M` the greatest
/// value of the other terms and the constant, `k·x >= -M`, so `x >= ⌈-M/k⌉` for `k > 0` and
/// `x <= ⌊M/-k⌋` for `k < 0`. An atom for which `b` gives nothing is unbounded. The sum is taken once, so
/// the cost is linear in the row's terms.
fn row_bounds<'a>(lin: &Lin, b: impl Fn(&Atom) -> Option<&'a Ends>, out: &mut Vec<Con>) {
    let most = |a: &Atom, k: &Int| -> Option<Int> {
        let (lo, hi) = b(a)?;
        if k.is_positive() {
            hi.as_ref()
        } else {
            lo.as_ref()
        }
        .map(|v| k * v)
    };
    let tops: Vec<Option<Int>> = lin.terms.iter().map(|(a, k)| most(a, k)).collect();
    let open = tops.iter().filter(|t| t.is_none()).count();
    if open > 1 {
        return;
    }
    let sum = tops
        .iter()
        .flatten()
        .fold(lin.constant.clone(), |s, t| &s + t);
    for ((a, k), top) in lin.terms.iter().zip(&tops) {
        let rest = match top {
            Some(t) if open == 0 => &sum - t,
            Some(_) => continue,
            None => sum.clone(),
        };
        let x = Lin::atom(a.clone());
        out.push(Con {
            lin: if k.is_positive() {
                x.minus(&Lin::constant(-&rest.div_floor(k)))
            } else {
                Lin::constant(rest.div_floor(&-k)).minus(&x)
            },
            rel: Rel::Ge,
        });
    }
}

/// `g` as one constraint: itself, or for the negation of `t >= 0` the constraint
/// `-t - 1 >= 0`, as [`nnf`] writes it. The negation of an equality is a disjunction and is not
/// one constraint.
fn as_row(g: &Formula) -> Option<std::borrow::Cow<'_, Con>> {
    use std::borrow::Cow;
    match g {
        Formula::Con(c) => Some(Cow::Borrowed(c)),
        Formula::Not(h) => match &**h {
            Formula::Con(c) if c.rel == Rel::Ge => Some(Cow::Owned(Con::ge(
                &Lin::default(),
                &c.lin.plus(&Lin::constant(1)),
            ))),
            _ => None,
        },
        _ => None,
    }
}

/// The bounds of the atoms of the constraints among the top-level conjuncts of `f` ([`as_row`]),
/// from the bounds `b` that hold wherever `f` does: each constraint's bounds ([`row_bounds`])
/// from `b`, then again from `b` met with those, the tightest of each side of each atom kept.
/// `None` when a lower bound passes an upper one, so that `f` has no point. The cost is linear
/// in the conjuncts' terms.
fn conjunct_bounds(f: &Formula, b: &HashMap<Atom, Ends>) -> Option<HashMap<Atom, Ends>> {
    let cons: Vec<_> = f.conjuncts().into_iter().filter_map(as_row).collect();
    let mut own: HashMap<Atom, Ends> = HashMap::new();
    for _pass in 0..2 {
        let mut rows = Vec::new();
        for c in &cons {
            let bound = |a: &Atom| own.get(a).or_else(|| b.get(a));
            row_bounds(&c.lin, bound, &mut rows);
            if c.rel == Rel::Eq {
                row_bounds(&c.lin.times(-1), bound, &mut rows);
            }
        }
        for r in &rows {
            meet_bound(&mut own, r, b);
        }
    }
    let empty = own
        .values()
        .any(|e| matches!(e, (Some(lo), Some(hi)) if lo > hi));
    (!empty).then_some(own)
}

/// Meets the bounds in `own` with the bound row `r` ([`one_bound`]); an atom not yet in `own`
/// starts from its bounds in `b`.
fn meet_bound(own: &mut HashMap<Atom, Ends>, r: &Con, b: &HashMap<Atom, Ends>) {
    let (a, lo, hi) = one_bound(r).expect("a bound has one atom");
    let (l, h) = own
        .entry(a.clone())
        .or_insert_with(|| b.get(a).cloned().unwrap_or_default());
    if let Some(lo) = lo
        && l.as_ref().is_none_or(|l| lo > *l)
    {
        *l = Some(lo);
    }
    if let Some(hi) = hi
        && h.as_ref().is_none_or(|h| hi < *h)
    {
        *h = Some(hi);
    }
}

/// The bounds that the disjunction of `ds` gives its atoms from the bounds `b`: a side of an
/// atom that every disjunct with a point bounds ([`conjunct_bounds`]), at the widest of those
/// bounds. A disjunct shared by several disjunctions is read once, by its key in `seen`.
fn disjunction_bounds(
    ds: &[Formula],
    b: &HashMap<Atom, Ends>,
    seen: &mut HashMap<Id, Option<HashMap<Atom, Ends>>>,
    out: &mut Vec<Con>,
) {
    let mut acc: Option<HashMap<Atom, Ends>> = None;
    for d in ds {
        let own = match d {
            Formula::Con(_) => conjunct_bounds(d, b),
            _ => seen
                .entry(Id::any(d))
                .or_insert_with(|| conjunct_bounds(d, b))
                .clone(),
        };
        let Some(own) = own else { continue };
        acc = Some(match acc {
            None => own,
            Some(acc) => acc
                .into_iter()
                .filter_map(|(a, (lo, hi))| {
                    let (l, h) = own.get(&a)?;
                    let lo = lo.zip(l.clone()).map(|(x, y)| x.min(y));
                    let hi = hi.zip(h.clone()).map(|(x, y)| x.max(y));
                    (lo.is_some() || hi.is_some()).then_some((a, (lo, hi)))
                })
                .collect(),
        });
    }
    for (a, (lo, hi)) in acc.into_iter().flatten() {
        let x = Lin::atom(a);
        if let Some(l) = lo {
            out.push(Con::ge(&x, &Lin::constant(l)));
        }
        if let Some(h) = hi {
            out.push(Con::ge(&Lin::constant(h), &x));
        }
    }
}

/// The bounds that the rows `other` give the atoms at the nodes `sources` of `g` through
/// paths of difference rows, by one level of elimination, pushed onto `out` as bound rows. In a
/// row `Σ k·a + c >= 0`, each atom `a` that a path ties to a source `s` (`a <= s + d` where
/// `k > 0`, `a >= s - d` where `k < 0`, so `k·a <= k·s + |k|·d`) is replaced by that bound, and
/// each other atom by its own greatest `k·a` from `b`; the row then gives `K·s + C >= 0`, a
/// bound on `s` when `K` is not zero, rounded inward. For example `w1 <= v` and `w2 <= v` turn
/// `w1 + w2 >= 10` into `2·v - 10 >= 0`, so `v >= 5`. Each bound holds wherever the rows do,
/// since each replacement only raises the row's left side. Each atom is tied to its nearest
/// source alone, and to none where two are nearest, so that no name chooses
/// ([`Differences::search`], two searches from all the sources at once, not through `z`);
/// such an atom counts with its own bound from `b`. A row is read once, a sum kept for each source among its atoms', so the
/// cost is O(m log n) for m rows over n atoms. An equality is read as two rows.
fn eliminate(
    g: &Differences,
    b: &HashMap<Atom, Ends>,
    sources: &[usize],
    other: &[&Con],
    out: &mut Vec<Con>,
) {
    if sources.is_empty() || other.is_empty() {
        return;
    }
    let up = g.search(Along::Up, sources, false);
    let down = g.search(Along::Down, sources, false);
    /// For one source: the sum of the coefficients replaced by it, the sum of the constants
    /// its paths add, the sum of those atoms' own greatest terms from `b`, and how many of
    /// them have none.
    struct Tied {
        k: Int,
        path: Int,
        own: Int,
        open: usize,
    }
    let mut row = |lin: &Lin| {
        // The constant and the greatest terms from `b`, and the number of atoms with none.
        let mut fixed = lin.constant.clone();
        let mut open = 0usize;
        let mut by: BTreeMap<usize, Tied> = BTreeMap::new();
        for (a, k) in &lin.terms {
            let own = (b.get(a))
                .and_then(|(lo, hi)| {
                    if k.is_positive() {
                        hi.as_ref()
                    } else {
                        lo.as_ref()
                    }
                })
                .map(|v| k * v);
            match &own {
                Some(v) => fixed = &fixed + v,
                None => open += 1,
            }
            let ends = if k.is_positive() { &up } else { &down };
            let Some((d, s)) = g.node.get(a).and_then(|&i| ends[i].as_ref()) else {
                continue;
            };
            let t = by.entry(*s).or_insert_with(|| Tied {
                k: Int::ZERO,
                path: Int::ZERO,
                own: Int::ZERO,
                open: 0,
            });
            t.k = &t.k + k;
            t.path = &t.path + &(&k.abs() * d);
            match own {
                Some(v) => t.own = &t.own + &v,
                None => t.open += 1,
            }
        }
        for (s, t) in by {
            if open > t.open || t.k.is_zero() {
                continue;
            }
            let c = &(&fixed - &t.own) + &t.path;
            let x = Lin::atom(g.atoms[s - 1].clone());
            out.push(Con {
                lin: if t.k.is_positive() {
                    x.minus(&Lin::constant(-&c.div_floor(&t.k)))
                } else {
                    Lin::constant(c.div_floor(&-&t.k)).minus(&x)
                },
                rel: Rel::Ge,
            });
        }
    };
    for c in other {
        row(&c.lin);
        if c.rel == Rel::Eq {
            row(&c.lin.times(-1));
        }
    }
}

/// For each atom of `f`, whether it has a positive and whether a negative coefficient in a
/// constraint `t >= 0` of `f` in negation normal form ([`nnf`]: under an odd number of
/// negations `t >= 0` is `-t - 1 >= 0`), an equality, or its negation, counting as both. An
/// atom with no negative one keeps every constraint that holds holding as it rises, so from any
/// point of `f` it rises without bound over the points of `f`, the others fixed; one with no
/// positive one likewise falls without bound. One fold over the distinct parts of `f` with the
/// parity of the negations above them, so the cost is linear in its size.
fn signs(f: &Formula) -> HashMap<Atom, (bool, bool)> {
    let mut out: HashMap<Atom, (bool, bool)> = HashMap::new();
    f.fold(
        true,
        |g, pos| pos != matches!(g, Formula::Not(_)),
        |g, pos, _: Vec<()>| {
            if let Formula::Con(c) = g {
                for (a, k) in &c.lin.terms {
                    let (p, n) = out.entry(a.clone()).or_default();
                    if c.rel == Rel::Eq {
                        (*p, *n) = (true, true);
                    } else if k.is_positive() == pos {
                        *p = true;
                    } else {
                        *n = true;
                    }
                }
            }
        },
    );
    out
}

/// The bounds that the rows `other` give their atoms from the bounds `b` and from each other,
/// pushed onto `out` as bound rows. A row `Σ k·a + c >= 0` gives `a` a lower bound where
/// `k > 0` and an upper one where `k < 0`, from the sides of the other atoms that bound their
/// terms from above, as [`row_bounds`] reads it. A side is final once each row that bounds it
/// has been read for it, and a row is read for an atom once the sides it needs of the other
/// atoms are final, so a bound found through one row reaches the rows that need it: from
/// `b + 2·c <= 3` with `c >= 0`, `b <= 3`, and then from `a + b >= 10`, `a >= 7`. The sides
/// are taken in that order (Kahn's), so each final side is what reading the rows again and
/// again until nothing changes gives it, and the result does not depend on the order of the
/// rows. A side that depends on itself through the rows is never final, and a row that needs
/// it is read for nothing else. A row is read at most twice, once when one of the sides it
/// needs is not final and once when none is, each time in one pass over its terms, so the
/// cost is linear in the rows' terms. An equality is read as two rows.
fn propagate(other: &[&Con], b: &HashMap<Atom, Ends>, out: &mut Vec<Con>) {
    // A side is `2·i` for the lower one of the `i`th atom and `2·i + 1` for the upper. Each
    // row `>= 0` holds, for each term, the side it gives, the side it needs and its
    // coefficient, and the row's constant.
    let mut index: HashMap<&Atom, usize> = HashMap::new();
    let mut atoms: Vec<&Atom> = Vec::new();
    /// A row: for each term the side it gives, the side it needs and its coefficient; and the
    /// constant.
    type Row = (Vec<(usize, usize, Int)>, Int);
    let mut rows: Vec<Row> = Vec::new();
    for c in other {
        let signs: &[i64] = if c.rel == Rel::Eq { &[1, -1] } else { &[1] };
        for &sign in signs {
            let sign = Int::from(sign);
            let terms = (c.lin.terms.iter())
                .map(|(a, k)| {
                    let i = *index.entry(a).or_insert_with(|| {
                        atoms.push(a);
                        atoms.len() - 1
                    });
                    let k = &sign * k;
                    let up = usize::from(k.is_positive());
                    (2 * i + 1 - up, 2 * i + up, k)
                })
                .collect();
            rows.push((terms, &sign * &c.lin.constant));
        }
    }
    let mut at: Vec<Option<Int>> = Vec::with_capacity(2 * atoms.len());
    for a in &atoms {
        let (lo, hi) = b.get(*a).cloned().unwrap_or_default();
        at.push(lo);
        at.push(hi);
    }
    let start = at.clone();
    // How many terms still give each side, whether it is final, the rows whose terms need it,
    // and how many of each row's terms need a side not final.
    let mut left = vec![0usize; at.len()];
    let mut needed_by: Vec<Vec<usize>> = vec![Vec::new(); at.len()];
    for (i, (terms, _)) in rows.iter().enumerate() {
        for (gives, needs, _) in terms {
            left[*gives] += 1;
            needed_by[*needs].push(i);
        }
    }
    let mut fin: Vec<bool> = left.iter().map(|&n| n == 0).collect();
    let mut pending: Vec<usize> = (rows.iter())
        .map(|(terms, _)| terms.iter().filter(|(_, n, _)| !fin[*n]).count())
        .collect();
    // Row `i` read for its one term whose needed side is not final, or with none, for each
    // term but the one that needs `skip`, read before: the sides given and their bounds.
    let read = |i: usize, at: &[Option<Int>], fin: &[bool], skip: Option<usize>| {
        let (terms, constant) = &rows[i];
        // The greatest value of each term whose needed side is final; `None` if unbounded.
        let tops: Vec<Option<Int>> = (terms.iter())
            .map(|(_, n, k)| at[*n].as_ref().filter(|_| fin[*n]).map(|v| k * v))
            .collect();
        let lone = terms.iter().filter(|(_, n, _)| !fin[*n]).count();
        let wide = tops.iter().filter(|t| t.is_none()).count() - lone;
        let sum = (tops.iter().flatten()).fold(constant.clone(), |s, t| &s + t);
        let mut given: Vec<(usize, Option<Int>)> = Vec::new();
        for ((g, n, k), top) in terms.iter().zip(&tops) {
            if (lone == 1) == fin[*n] || skip == Some(*n) {
                continue;
            }
            // With `M` the greatest value of the other terms and the constant, `k·a >= -M`.
            let rest = match top {
                Some(t) if wide == 0 => Some(&sum - t),
                None if wide + lone == 1 => Some(sum.clone()),
                _ => None,
            };
            let v = rest.map(|rest| {
                if k.is_positive() {
                    -&rest.div_floor(k)
                } else {
                    rest.div_floor(&-k)
                }
            });
            given.push((*g, v));
        }
        given
    };
    /// The sides as they are found: the bound of each, read by the rows; the bound given to
    /// each side after it was let go, which no row reads; how many terms still give each;
    /// whether each is queued to be final, or was let go; the queue; and the sides with a
    /// bound that are not queued.
    struct Found {
        at: Vec<Option<Int>>,
        late: Vec<Option<Int>>,
        left: Vec<usize>,
        queued: Vec<bool>,
        gone: Vec<bool>,
        ready: Vec<usize>,
        valued: Vec<usize>,
    }
    /// The tighter of the bounds `old` and `v` of side `s`.
    fn meet(s: usize, old: &mut Option<Int>, v: Int) {
        if old
            .as_ref()
            .is_none_or(|o| if s.is_multiple_of(2) { v > *o } else { v < *o })
        {
            *old = Some(v);
        }
    }
    impl Found {
        /// Meets each side given with its bound, and counts the term as read for it.
        fn give(&mut self, given: Vec<(usize, Option<Int>)>) {
            for (s, v) in given {
                if let Some(v) = v {
                    if self.gone[s] {
                        meet(s, &mut self.late[s], v);
                    } else {
                        if self.at[s].is_none() && !self.queued[s] {
                            self.valued.push(s);
                        }
                        meet(s, &mut self.at[s], v);
                    }
                }
                self.left[s] -= 1;
                if self.left[s] == 0 && !mem::replace(&mut self.queued[s], true) {
                    self.ready.push(s);
                }
            }
        }
    }
    let n = at.len();
    let valued = (0..n).filter(|&s| !fin[s] && at[s].is_some()).collect();
    let mut found = Found {
        at,
        late: vec![None; n],
        left,
        queued: fin.clone(),
        gone: vec![false; n],
        ready: Vec::new(),
        valued,
    };
    for (i, _) in pending.iter().enumerate().filter(|(_, p)| **p <= 1) {
        found.give(read(i, &found.at, &fin, None));
    }
    loop {
        while let Some(s) = found.ready.pop() {
            fin[s] = true;
            for &i in &needed_by[s] {
                pending[i] -= 1;
                if pending[i] <= 1 {
                    let skip = (pending[i] == 0).then_some(s);
                    found.give(read(i, &found.at, &fin, skip));
                }
            }
        }
        // What is left waits on sides that depend on themselves through the rows. Each side
        // with a bound is let go at once with the bound it has, and the rows read on from
        // there; a bound it is given later is kept, but no row reads it, so what each row
        // reads is fixed by the rows alone and not by the order they are taken in.
        let go: Vec<usize> = mem::take(&mut found.valued)
            .into_iter()
            .filter(|&s| !found.queued[s])
            .collect();
        if go.is_empty() {
            break;
        }
        for s in go {
            found.queued[s] = true;
            found.gone[s] = true;
            found.ready.push(s);
        }
    }
    for (s, (v, late)) in found.at.into_iter().zip(found.late).enumerate() {
        let mut v = v;
        if let Some(l) = late {
            meet(s, &mut v, l);
        }
        let Some(v) = v.filter(|v| start[s].as_ref() != Some(v)) else {
            continue;
        };
        let x = Lin::atom(atoms[s / 2].clone());
        out.push(Con {
            lin: if s.is_multiple_of(2) {
                x.minus(&Lin::constant(v))
            } else {
                Lin::constant(v).minus(&x)
            },
            rel: Rel::Ge,
        });
    }
}

/// For each atom of a row of `cons` that is not a difference constraint or a bound, or of a
/// disjunction of `ors`, the formula of its cluster: the atoms that such rows and disjunctions
/// join, by union-find over the atoms of each, with those rows and disjunctions, the
/// difference constraints of `cons` on atoms of the cluster alone, and the bounds `ends` of
/// each atom of the cluster. Each holds wherever `cons`, `ors` and `ends` do, so the hull of
/// an atom over its cluster contains its hull over them, and it is wider where a path of
/// difference constraints through other atoms ties two atoms of the cluster more closely than
/// their bounds do. Each row and disjunction is read once, so the cost is linear in their size,
/// with a factor log n for the ordered map of the n atoms, which keeps the order of each
/// cluster's rows independent of the hash seed.
fn clusters(
    cons: &[Con],
    ors: &[&Formula],
    ends: &HashMap<Atom, Ends>,
) -> HashMap<Atom, Rc<Formula>> {
    fn find(parent: &mut [usize], mut i: usize) -> usize {
        while parent[i] != i {
            parent[i] = parent[parent[i]];
            i = parent[i];
        }
        i
    }
    let mut ids: BTreeMap<Atom, usize> = BTreeMap::new();
    let mut parent: Vec<usize> = Vec::new();
    let mut join = |atoms: Vec<Atom>, parent: &mut Vec<usize>| -> Option<usize> {
        let mut root = None;
        for a in atoms {
            let i = *ids.entry(a).or_insert_with(|| {
                parent.push(parent.len());
                parent.len() - 1
            });
            let r = find(parent, i);
            match root {
                None => root = Some(r),
                Some(q) => parent[r] = q,
            }
        }
        root
    };
    let mut joining: Vec<(usize, Formula)> = Vec::new();
    for c in cons.iter().filter(|c| !is_difference(c)) {
        if let Some(r) = join(c.lin.terms.keys().cloned().collect(), &mut parent) {
            joining.push((r, Formula::Con(c.clone())));
        }
    }
    for g in ors {
        if let Some(r) = join(g.atoms().into_iter().collect(), &mut parent) {
            joining.push((r, (*g).clone()));
        }
    }
    let mut parts: HashMap<usize, Vec<Formula>> = HashMap::new();
    for (r, f) in joining {
        let root = find(&mut parent, r);
        parts.entry(root).or_default().push(f);
    }
    for c in cons.iter().filter(|c| is_difference(c)) {
        let mut roots = c.lin.terms.keys().map(|a| ids.get(a).copied());
        let Some(Some(first)) = roots.next() else {
            continue;
        };
        let root = find(&mut parent, first);
        if roots.all(|i| i.is_some_and(|i| find(&mut parent, i) == root)) {
            parts.entry(root).or_default().push(Formula::Con(c.clone()));
        }
    }
    for (a, &i) in &ids {
        let root = find(&mut parent, i);
        let (lo, hi) = ends.get(a).cloned().unwrap_or_default();
        let x = Lin::atom(a.clone());
        let part = parts.entry(root).or_default();
        if let Some(lo) = lo {
            part.push(Formula::Con(Con::ge(&x, &Lin::constant(lo))));
        }
        if let Some(hi) = hi {
            part.push(Formula::Con(Con::ge(&Lin::constant(hi), &x)));
        }
    }
    let formulas: HashMap<usize, Rc<Formula>> = (parts.into_iter())
        .map(|(root, fs)| (root, Rc::new(Formula::and(fs))))
        .collect();
    (ids.into_iter())
        .map(|(a, i)| {
            let root = find(&mut parent, i);
            (a, Rc::clone(&formulas[&root]))
        })
        .collect()
}

/// What [`part_bounds`] finds of a part: bounds of its atoms, whether they are its hulls
/// because every row is a difference constraint or a bound, and, where they are not, the
/// cluster of each atom of a general row or a disjunction ([`clusters`]).
struct PartBounds {
    ends: HashMap<Atom, Ends>,
    hulls: bool,
    local: HashMap<Atom, Rc<Formula>>,
}

/// Bounds of the atoms of `part`, a part of the premises with the point `m`, whose atoms
/// `factors` are factors of products. First, every atom that is not a factor and is in no
/// disjunction is eliminated from the top-level rows where that is exact over the integers and
/// adds no terms ([`shadow`]), so a chain of general rows through such atoms becomes rows on
/// the atoms kept, with the same integer points on them: from `a + b >= 10`, `b + 2·c <= 3`
/// and `c >= 0`, with `b` and `c` not kept, `a >= 7`. Then come the hulls of the difference
/// constraints and bounds left ([`difference_ends`]), and those hulls again with the bounds
/// found from the first hulls added as rows: those each other row gives its atoms alone
/// ([`row_bounds`]) and through the bounds the other rows give ([`propagate`]), those it gives
/// the factors through paths of difference rows ([`eliminate`]), and those each top-level
/// disjunction gives from its disjuncts' top-level constraints ([`disjunction_bounds`]). Each
/// bound holds at every point of the part, since each row added does. Where the bounds are not
/// all hulls, the cluster of each atom of a general row or a disjunction is kept too
/// ([`clusters`]), for [`products`] to ask the solver over. The cost is the elimination,
/// which adds no terms, four shortest-path passes, and passes linear in the other rows and in
/// each disjunction's disjuncts, O(m log n) for m rows over n atoms. Where every row is a
/// difference constraint or a bound the bounds are the hulls [`hull_from`] finds.
///
/// Complexity tradeoff: with any other row a bound may be wider than the hull, or missing:
/// one that needs two general rows at once on atoms that are both kept (from
/// `a + b >= 10` and `a - 2·b >= 1` with `b` in a disjunction, `a >= 7`), a side that depends
/// on itself through the rows (let go with the bound it has, [`propagate`]), a path to a
/// factor other than the nearest one or to one of two nearest, or a row nested two levels
/// deep, in a disjunction within a disjunct, or under the negation of an equality or of a
/// conjunction or disjunction.
/// Why: the hull of one atom of a general integer system is an integer program, and integer
/// programming is NP-hard, so no method finds every hull in O(m log n) unless P = NP; each
/// side by [`hull_from`] costs O(part). These bounds are a first try: where the goal is then
/// not proved, [`products`] asks the solver for each side of a factor not known to be the
/// hull's, and its own tradeoff comment says what that costs. Test:
/// `l01_38_presburger::ladder::a_bound_that_needs_two_general_rows_is_found_by_the_solver`.
/// COMPLEXITY.md row C2.
fn part_bounds(part: &Formula, m: &Model, factors: &[&Atom]) -> PartBounds {
    // The rows, and every atom that is a factor or in a disjunction.
    let (mut cons, mut ors, mut whole) = (Vec::new(), Vec::new(), true);
    let mut joined: Vec<&Formula> = Vec::new();
    let mut keep: HashSet<Atom> = factors.iter().map(|a| (*a).clone()).collect();
    for g in part.conjuncts() {
        match g {
            Formula::Or(ds) => {
                ors.push(ds);
                joined.push(g);
                keep.extend(g.atoms());
            }
            _ => match as_row(g) {
                Some(c) => cons.push(c.into_owned()),
                None => whole = false,
            },
        }
    }
    // The rows with every other atom eliminated where that is exact and adds no terms
    // ([`shadow`]): their integer points on the atoms kept are those of the rows, so the
    // hulls of the factors are the same, and a chain of general rows through atoms that are
    // not factors becomes rows on the factors alone, often difference constraints.
    let Some(cons) = shadow(&cons, &|a| keep.contains(a), true) else {
        return PartBounds {
            ends: HashMap::new(),
            hulls: false,
            local: HashMap::new(),
        };
    };
    let (mut rows, other): (Vec<&Con>, Vec<&Con>) = cons.iter().partition(|c| is_difference(c));
    let hulls = whole && other.is_empty() && ors.is_empty();
    let Some(g) = Differences::of(&rows, m) else {
        return PartBounds {
            ends: HashMap::new(),
            hulls: false,
            local: HashMap::new(),
        };
    };
    let first = g.ends();
    let mut added = Vec::new();
    for c in &other {
        row_bounds(&c.lin, |a| first.get(a), &mut added);
        if c.rel == Rel::Eq {
            row_bounds(&c.lin.times(-1), |a| first.get(a), &mut added);
        }
    }
    propagate(&other, &first, &mut added);
    let sources: Vec<usize> = factors
        .iter()
        .filter_map(|a| g.node.get(a).copied())
        .collect();
    eliminate(&g, &first, &sources, &other, &mut added);
    let mut seen = HashMap::new();
    for ds in ors {
        disjunction_bounds(ds, &first, &mut seen, &mut added);
    }
    if added.is_empty() {
        let local = if hulls {
            HashMap::new()
        } else {
            clusters(&cons, &joined, &first)
        };
        return PartBounds {
            ends: first,
            hulls,
            local,
        };
    }
    // The point `m` may leave out an atom that no difference row names, and the shortest
    // paths need its value at each atom of their rows; such an atom is in no other difference
    // row, so its bounds are those added alone.
    let (known, loose): (Vec<&Con>, Vec<&Con>) =
        (added.iter()).partition(|r| r.lin.terms.keys().all(|a| m.get(a).is_some()));
    rows.extend(known);
    let mut ends = difference_ends(&rows, m).unwrap_or(first);
    for r in loose {
        meet_bound(&mut ends, r, &HashMap::new());
    }
    let local = if hulls {
        HashMap::new()
    } else {
        clusters(&cons, &joined, &ends)
    };
    PartBounds { ends, hulls, local }
}

/// Whether `sym` takes arbitrarily large values (`dir` 1) or arbitrarily small ones (`dir`
/// -1) over the integer points of `c`, which has one. In negation normal form `c` is an
/// and-or tree of constraints, so its integer points are the union, over its terms in
/// disjunctive form, of the integer points of each term's polyhedron `P`. When `P` has an
/// integer point, the hull of its integer points has the recession cone of `P` (Meyer 1974),
/// so `sym` is unbounded over them exactly when some ray `r` with `A·r >= 0` and `E·r == 0`
/// for `P`'s rows `A·z + a >= 0` and `E·z + e == 0` has `dir · r_sym > 0`, and then one with
/// `dir · r_sym >= 1` in integers, the cone being rational. The question is one formula: each
/// constraint is replaced by itself and its row without the constant over a copy of the atoms
/// (fresh auxiliary variables), which keeps the tree, so its terms are the pairs of a term's
/// polyhedron and its cone. With no disjunction the point is known, and the cone alone is
/// asked. Its size is twice that of `c`.
fn unbounded(c: &Formula, sym: &Atom, dir: i64) -> Result<bool, Refusal> {
    let f = nnf(c, true);
    let atoms = f.atoms();
    let first = atoms
        .iter()
        .filter_map(|a| match a {
            Atom::Aux(n) => Some(n + 1),
            _ => None,
        })
        .max()
        .unwrap_or(0);
    let ray: BTreeMap<&Atom, Atom> = atoms
        .iter()
        .zip(first..)
        .map(|(a, n)| (a, Atom::Aux(n)))
        .collect();
    let cone = |con: &Con| Con {
        lin: Lin {
            terms: con
                .lin
                .terms
                .iter()
                .map(|(a, k)| (ray[a].clone(), k.clone()))
                .collect(),
            constant: Int::ZERO,
        },
        rel: con.rel,
    };
    // A shared conjunction is entered once.
    let has_or = |g: &Formula| -> bool {
        let mut seen = std::collections::HashSet::new();
        let mut stack = vec![g];
        while let Some(g) = stack.pop() {
            match g {
                Formula::Or(_) => return true,
                Formula::And(gs) if Id::of(g).is_none_or(|id| seen.insert(id)) => {
                    stack.extend(gs.iter())
                }
                _ => {}
            }
        }
        false
    };
    // A symbol no constraint mentions takes every value.
    let Some(r) = ray.get(sym) else {
        return Ok(true);
    };
    let r = Lin::atom(r.clone());
    let away = Formula::Con(Con::ge(&r.times(dir), &Lin::constant(1)));
    let body = if has_or(&f) {
        // Each constraint `k` replaced by `k && cone(k)`.
        f.map_cons(&|k| Formula::and(vec![Formula::Con(k.clone()), Formula::Con(cone(k))]))
    } else {
        Formula::and(f.cons().iter().map(|con| Formula::Con(cone(con))).collect())
    };
    decide(&Formula::and(vec![body, away]))
}

/// The set `s` of a symbol as a formula: the disjunction of its pieces.
pub fn member(sym: &Atom, s: &IntervalSet) -> Formula {
    within(&Lin::atom(sym.clone()), s)
}

/// The values of the term `l` in the set `s`, as a formula.
pub fn within(l: &Lin, s: &IntervalSet) -> Formula {
    let mut pieces = Vec::new();
    for (lo, hi) in s.pieces() {
        let mut both = Vec::new();
        if let End::Fin(v) = lo {
            both.push(Formula::Con(Con::ge(l, &Lin::constant(v))));
        }
        if let End::Fin(v) = hi {
            both.push(Formula::Con(Con::ge(&Lin::constant(v), l)));
        }
        pieces.push(Formula::and(both));
    }
    Formula::or(pieces)
}

/// What rung 2 concludes about an entailment.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Entailment {
    /// The premises entail the goal; the certificate is the premise set, the products of the
    /// factor premises included.
    Proved(Vec<Formula>),
    /// The goal fails at these values of the symbols, where the premises hold.
    Refuted(Model),
    /// The premises with the products, read linearly, hold at these values with the goal
    /// failing, but the values of the product atoms are not the products of the symbols'.
    NotProved(Model),
    /// The question lies outside the fragment decided in polynomial time.
    Refused(Refusal),
}

impl fmt::Display for Entailment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let model = |m: &Model, f: &mut fmt::Formatter<'_>| {
            let parts: Vec<String> = m.iter().map(|(a, v)| format!("{a} = {v}")).collect();
            write!(f, "{}", parts.join(", "))
        };
        match self {
            Entailment::Proved(ps) => {
                let parts: Vec<String> = ps.iter().map(|p| p.to_string()).collect();
                write!(f, "proved from {}", parts.join(" && "))
            }
            Entailment::Refuted(m) => {
                write!(f, "refuted: countermodel ")?;
                model(m, f)
            }
            Entailment::NotProved(m) => {
                write!(f, "not proved: the linear reading fails at ")?;
                model(m, f)
            }
            Entailment::Refused(r) => write!(f, "refused: {r}"),
        }
    }
}

/// Whether `premises` entail `goal` (rung 2). The two come from one call of
/// `preimage::relations`, so that their auxiliary variables are numbered apart: the definitions
/// of both are conjoined, and `q0` of one is otherwise `q0` of the other, which proves goals
/// that do not follow (`x mod 2 == 1` to `x mod 4 <= 1`). Panics when the numbers overlap.
pub fn entails(premises: &Relation, goal: &Relation) -> Entailment {
    // The numbers of a relation's definitions ascend from its first to its last
    // (`preimage::relations` numbers them in one sequence), so the two ends tell whether the
    // two relations share one.
    let ends = |r: &Relation| (r.defs.first()).zip(r.defs.last()).map(|(a, b)| (a.0, b.0));
    if let (Some((p0, p1)), Some((g0, g1))) = (ends(premises), ends(goal)) {
        assert!(
            p1 < g0 || g1 < p0,
            "the auxiliary variables of premises and goal must be numbered apart: \
             translate both in one call of `preimage::relations`"
        );
    }
    entails_inner(premises, goal).unwrap_or_else(Entailment::Refused)
}

fn entails_inner(premises: &Relation, goal: &Relation) -> Result<Entailment, Refusal> {
    let (ps, loose) = products(premises, goal, Tier::Cheap)?;
    let first = linear_reading(premises, goal, ps)?;
    if !loose || !matches!(first, Entailment::NotProved(_)) {
        return Ok(first);
    }
    // The bounds of some factor may be wider than its hull, so the products are taken again
    // from the hulls the solver finds for those sides, first over each factor's cluster and
    // then, if the goal is still not proved, over its whole part. Each bound found holds
    // wherever the premises do and lies within the one before, so each such product implies
    // the one from the wider bound with the linear premises, whatever one try proves the next
    // proves too, and the last verdict is the one the hulls give. Where the solver refuses,
    // the verdict before stands.
    // Complexity tradeoff: each try costs one solver question for each open side, over the
    // cluster O(sides × cluster) and over the part O(sides × part); see [`Tier`] for why and
    // when. COMPLEXITY.md row C2.
    let (ps, loose) = match products(premises, goal, Tier::Local) {
        Ok(found) => found,
        Err(_) => return Ok(first),
    };
    let second = linear_reading(premises, goal, ps).unwrap_or(first);
    if !loose || !matches!(second, Entailment::NotProved(_)) {
        return Ok(second);
    }
    Ok(products(premises, goal, Tier::Whole)
        .and_then(|(ps, _)| linear_reading(premises, goal, ps))
        .unwrap_or(second))
}

/// Whether `premises` with the products `extra` ([`products`]) entail `goal` when each
/// product is read as its own atom: proved, or a point of the premises where the goal fails,
/// which is a countermodel when it is one with each product read as a product.
fn linear_reading(
    premises: &Relation,
    goal: &Relation,
    extra: Vec<Formula>,
) -> Result<Entailment, Refusal> {
    let defs = Formula::and(vec![premises.defined(), goal.defined()]);
    let mut ps = vec![premises.body.clone()];
    ps.extend(extra);
    let premise = Formula::and(ps.clone());
    let f = Formula::and(vec![
        defs.clone(),
        premise,
        Formula::negate(goal.body.clone()),
    ]);
    let Some(m) = satisfiable(&f)? else {
        return Ok(Entailment::Proved(ps));
    };
    // A countermodel of the linear reading is a countermodel when the premises hold and the
    // goal fails with each product read as a product.
    let real = Formula::and(vec![
        defs,
        premises.body.clone(),
        Formula::negate(goal.body.clone()),
    ]);
    let syms: Model = m
        .iter()
        .filter(|(a, _)| !matches!(a, Atom::Product(..)))
        .map(|(a, v)| (a.clone(), v.clone()))
        .collect();
    if real.holds(&syms) {
        let shown = syms
            .into_iter()
            .filter(|(a, _)| matches!(a, Atom::Sym(_)))
            .collect();
        return Ok(Entailment::Refuted(shown));
    }
    Ok(Entailment::NotProved(m))
}

/// Which bounds [`products`] takes of a factor: those [`part_bounds`] finds (`Cheap`), or
/// those with each side not known to be the hull's replaced by the hull the solver finds
/// ([`hull_side`]) over the factor's cluster ([`clusters`], `Local`) or over its whole part
/// (`Whole`). A side found over the cluster lies between the hull over the part and the
/// bound of `Cheap`, since the cluster holds wherever the part does and holds that bound.
///
/// Complexity tradeoff: `Local` costs one solver question of the cluster for each open side
/// and O(log d) more for a bound at distance d, so O(sides × cluster), linear over a chain
/// of links that each hold their own general rows, and O(n²) at worst when one cluster holds
/// n open factors; `Whole` costs O(sides × part), O(n²) on a part with n open factors. Why:
/// the hull of one atom of a general integer system is an integer program, NP-hard, and the
/// bounds [`part_bounds`] finds in O(m log n) are not always the hulls; no way is known to
/// share the work of one side's question with another's. Trigger: [`entails_inner`] takes
/// `Local` only when the goal is not proved from the `Cheap` bounds and one of them is not
/// known to be the hull's, and `Whole` only when the goal is still not proved, which needs a
/// path of difference constraints through atoms outside a cluster that ties two of its atoms
/// more closely than their bounds do. Test:
/// `l01_38_presburger::ladder::products_whose_factors_keep_open_sides_scale` (`Local`, linear
/// in the links). Measured quadratic case: one cluster of k links joined by a sum of their
/// atoms, 32 sides in 52 ms at k = 8 and 234 sides in 3.86 s at k = 64; plan row
/// C2-local-tier. COMPLEXITY.md row C2.
#[derive(Clone, Copy)]
enum Tier {
    Cheap,
    Local,
    Whole,
}

/// For each product the formulas mention, the products in pairs of the premises on its two
/// factors, each `>= 0`, and whether a bound used is not known to be the factor's hull. The
/// bounds of each factor are those [`part_bounds`] finds, with each side not known to be the
/// hull's found by the solver as `tier` says ([`Tier`]). A side is known to be the hull's
/// when every row of the part is a difference constraint or a bound, when the part's point
/// meets the bound, or, with no bound, when the factor has no coefficient of the sign that
/// could stop it going that way ([`signs`]).
///
/// Complexity tradeoff: a product of two variables is an opaque atom, bounded only by these
/// products of pairs of linear premises; a goal that needs any other nonlinear reasoning is
/// `Entailment::NotProved`. Why: entailment over integer polynomials is undecidable
/// (Hilbert's tenth problem), and over the reals it costs time doubly exponential in the
/// variables (cylindrical algebraic decomposition). Trigger: a product atom in the premises
/// or the goal. Test:
/// `l01_38_presburger::entailment::a_product_is_bounded_only_through_the_premises_on_its_factors`.
/// COMPLEXITY.md row C2. No complete solution exists for integers; a stronger sound one would
/// add higher-degree products of premises (Positivstellensatz certificates), at a cost
/// polynomial of growing degree.
fn products(
    premises: &Relation,
    goal: &Relation,
    tier: Tier,
) -> Result<(Vec<Formula>, bool), Refusal> {
    let mut wanted = BTreeSet::new();
    for f in [&premises.body, &goal.body] {
        for a in f.atoms() {
            if let Atom::Product(x, y) = a {
                wanted.insert((x, y));
            }
        }
    }
    if wanted.is_empty() {
        return Ok((Vec::new(), false));
    }
    // The top-level linear inequalities, an equality read as two; and the other top-level
    // conjuncts that mention no product, a disjunction or a negation, which bound the factors
    // too ([`disjunction_bounds`]).
    let mut linear = Vec::new();
    let mut joined = Vec::new();
    for g in premises.body.conjuncts() {
        match g {
            Formula::Con(c) => {
                if c.lin.is_linear() {
                    linear.push(c.lin.clone());
                    if c.rel == Rel::Eq {
                        linear.push(c.lin.times(-1));
                    }
                }
            }
            _ => {
                if g.atoms().iter().all(|a| !matches!(a, Atom::Product(..))) {
                    joined.push(g.clone());
                }
            }
        }
    }
    // The rows of the premises, their definitions, the linear inequalities and the other
    // conjuncts above, in parts that share no atom, by union-find over the atoms each row
    // mentions; and the linear rows on each atom. A factor's bounds are its hull over its own
    // part: the other parts constrain other atoms, so where the premises have a point the hull
    // is the hull over all of them, and where they have none they entail any goal. Taking the
    // hull over all the premises for each factor cost O(factors × premises) (LADDER-study,
    // `l01_38_presburger::ladder::products_of_premises_in_pairs_scale`).
    let rows: Vec<Formula> = premises
        .defs
        .iter()
        .map(|(_, _, f)| f.clone())
        .chain(linear.iter().map(|l| {
            Formula::Con(Con {
                lin: l.clone(),
                rel: Rel::Ge,
            })
        }))
        .chain(joined)
        .collect();
    fn find(parent: &mut [usize], mut i: usize) -> usize {
        while parent[i] != i {
            parent[i] = parent[parent[i]];
            i = parent[i];
        }
        i
    }
    let mut ids: BTreeMap<Atom, usize> = BTreeMap::new();
    let mut parent: Vec<usize> = Vec::new();
    let mut firsts: Vec<Option<usize>> = Vec::with_capacity(rows.len());
    // A row with no atom holds or fails alone; where one fails the premises have no point.
    let mut consistent = true;
    for r in &rows {
        let atoms: Vec<usize> = r
            .atoms()
            .into_iter()
            .map(|a| {
                *ids.entry(a).or_insert_with(|| {
                    parent.push(parent.len());
                    parent.len() - 1
                })
            })
            .collect();
        if let Some((&a, rest)) = atoms.split_first() {
            for &b in rest {
                let (ra, rb) = (find(&mut parent, a), find(&mut parent, b));
                parent[rb] = ra;
            }
        } else if !r.holds(&Model::new()) {
            consistent = false;
        }
        firsts.push(atoms.first().copied());
    }
    let mut part_rows: BTreeMap<usize, Vec<Formula>> = BTreeMap::new();
    for (r, first) in rows.into_iter().zip(firsts) {
        if let Some(a) = first {
            let root = find(&mut parent, a);
            part_rows.entry(root).or_default().push(r);
        }
    }
    let parts: BTreeMap<usize, Formula> = part_rows
        .into_iter()
        .map(|(root, rs)| (root, Formula::and(rs)))
        .collect();
    let mut on_atom: BTreeMap<&Atom, Vec<usize>> = BTreeMap::new();
    for (i, l) in linear.iter().enumerate() {
        for a in l.terms.keys() {
            on_atom.entry(a).or_default().push(i);
        }
    }
    let factors: BTreeSet<Factor> = wanted
        .iter()
        .flat_map(|(x, y)| [x.clone(), y.clone()])
        .collect();
    // The factors of each part, in order.
    let mut part_factors: BTreeMap<usize, Vec<Atom>> = BTreeMap::new();
    for s in &factors {
        let atom = s.atom();
        if let Some(&id) = ids.get(&atom)
            && consistent
        {
            part_factors
                .entry(find(&mut parent, id))
                .or_default()
                .push(atom);
        }
    }
    // What each part gives its factors: `None` when it has no point, and otherwise its point,
    // the bounds of all its atoms ([`part_bounds`], O(m log n) for m rows over n atoms), and,
    // where those are not all hulls, the signs of its atoms ([`signs`], linear in the part).
    // Asking [`hull_from`] for each factor cost O(factors × part) on one part (C2-chain,
    // `l01_38_presburger::ladder::products_whose_factors_one_chain_connects_scale`, and
    // C2-chain-general, `products_along_a_chain_with_a_general_row_scale`).
    type Signs = HashMap<Atom, (bool, bool)>;
    let mut given: HashMap<usize, Option<(Model, PartBounds, Option<Signs>)>> = HashMap::new();
    for (root, atoms) in &part_factors {
        let part = &parts[root];
        let found = satisfiable_inner(part)?.map(|m| {
            let refs: Vec<&Atom> = atoms.iter().collect();
            let b = part_bounds(part, &m, &refs);
            let signs = (!b.hulls).then(|| signs(part));
            (m, b, signs)
        });
        given.insert(*root, found);
    }
    let mut loose = false;
    let mut on: BTreeMap<Factor, Vec<Lin>> = BTreeMap::new();
    for s in factors {
        let atom = s.atom();
        let mut set: Vec<Lin> = on_atom.get(&atom).map_or_else(Vec::new, |is| {
            is.iter().map(|&i| linear[i].clone()).collect()
        });
        let x = Lin::atom(atom.clone());
        let root = match ids.get(&atom) {
            Some(&id) if consistent => Some(find(&mut parent, id)),
            _ => None,
        };
        if let Some(root) = root
            && let Some((m, b, signs)) = &given[&root]
        {
            let (lo, hi) = b.ends.get(&atom).cloned().unwrap_or_default();
            // Whether the side going `dir` is the hull's: see the doc comment above.
            let known = |end: &Option<Int>, dir: i64| {
                b.hulls
                    || match end {
                        Some(v) => m.get(&atom) == Some(v),
                        None => signs
                            .as_ref()
                            .and_then(|s| s.get(&atom))
                            .is_some_and(|&(pos, neg)| if dir > 0 { !neg } else { !pos }),
                    }
            };
            let mut side = |end: Option<Int>, dir: i64| -> Result<Option<Int>, Refusal> {
                if known(&end, dir) {
                    return Ok(end);
                }
                match (tier, b.local.get(&atom)) {
                    (Tier::Whole, _) => hull_side(&parts[&root], &atom, m, dir),
                    (Tier::Local, Some(c)) => {
                        loose = true;
                        Ok(hull_side(c, &atom, m, dir).unwrap_or(end))
                    }
                    _ => {
                        loose = true;
                        Ok(end)
                    }
                }
            };
            if let Some(l) = side(lo, -1)? {
                set.push(x.minus(&Lin::constant(l)));
            }
            if let Some(h) = side(hi, 1)? {
                set.push(Lin::constant(h).minus(&x));
            }
        }
        set.sort();
        set.dedup();
        on.insert(s, set);
    }
    let mut out = BTreeSet::new();
    for (x, y) in &wanted {
        for a in &on[x] {
            for b in &on[y] {
                if let Some(p) = a.product(b) {
                    out.insert(Con {
                        lin: p,
                        rel: Rel::Ge,
                    });
                }
            }
        }
    }
    Ok((out.into_iter().map(Formula::Con).collect(), loose))
}

#[cfg(feature = "two-at-a-time")]
thread_local! {
    /// Whether [`Formula::and_keeping`] and [`Formula::or_keeping`] join as they did before
    /// [`Joining`], and the translator joins a chain of `&&` or `||` two at a time
    /// (`preimage::Tx::two_at_a_time`): for the tests that compare the two (ST-formula-k2). Only with
    /// the feature `two-at-a-time`, which the crate that holds `preimage` turns on for its tests.
    pub static TWO_AT_A_TIME: Cell<bool> = const { Cell::new(false) };
}

/// The joins as they were before [`Joining`], which [`TWO_AT_A_TIME`] selects and the tests compare
/// against.
#[cfg(any(test, feature = "two-at-a-time"))]
mod before {
    use super::*;

    /// `Formula::and_keeping` as it was before `Joining`, to compare against.
    pub(super) fn and_keeping_before(fs: Vec<Formula>, keep: impl Fn(usize) -> bool) -> Formula {
        let mut flat = Vec::new();
        for (i, f) in fs.into_iter().enumerate() {
            match f {
                Formula::And(ref gs) if gs.is_empty() => {}
                Formula::And(_) if keep(i) => flat.push(f),
                Formula::And(_) => flat.extend(f.into_parts().expect("a conjunction")),
                Formula::Or(ref gs) if gs.is_empty() => return Formula::bottom(),
                g => flat.push(g),
            }
        }
        // Of two constraints on one term, the tighter alone, in the place of the first.
        let mut out: Vec<Formula> = Vec::new();
        let mut at: BTreeMap<(BTreeMap<Atom, Int>, Rel), usize> = BTreeMap::new();
        for g in flat {
            let Formula::Con(c) = &g else {
                out.push(g);
                continue;
            };
            let key = (c.lin.terms.clone(), c.rel);
            match at.get(&key) {
                Some(&i) => {
                    let Formula::Con(old) = &out[i] else {
                        unreachable!("a constraint")
                    };
                    if c.rel == Rel::Ge && c.lin.constant < old.lin.constant {
                        out[i] = g;
                    } else if c.rel == Rel::Eq && c.lin.constant != old.lin.constant {
                        return Formula::bottom();
                    }
                }
                None => {
                    at.insert(key, out.len());
                    out.push(g);
                }
            }
        }
        if out.len() == 1 {
            out.pop().expect("one")
        } else {
            Formula::And(Shared::new(out))
        }
    }

    /// `Formula::or_keeping` as it was before `Joining`, to compare against.
    pub(super) fn or_keeping_before(fs: Vec<Formula>, keep: impl Fn(usize) -> bool) -> Formula {
        let mut out = Vec::new();
        for (i, f) in fs.into_iter().enumerate() {
            match f {
                Formula::Or(ref gs) if gs.is_empty() => {}
                Formula::Or(_) if keep(i) => out.push(f),
                Formula::Or(_) => out.extend(f.into_parts().expect("a disjunction")),
                Formula::And(ref gs) if gs.is_empty() => return Formula::top(),
                g => out.push(g),
            }
        }
        if Formula::complementary(&out) {
            return Formula::top();
        }
        if out.len() == 1 {
            out.pop().expect("one")
        } else {
            Formula::Or(Shared::new(out))
        }
    }
}

#[cfg(test)]
pub(super) mod tests {
    use super::before::{and_keeping_before, or_keeping_before};
    use super::*;

    fn sym(s: &str) -> Atom {
        Atom::Sym(s.into())
    }

    fn lin(terms: &[(&str, i128)], k: i128) -> Lin {
        let mut l = Lin::constant(k);
        for (s, c) in terms {
            l = l.plus(&Lin::atom(sym(s)).times(*c));
        }
        l
    }

    fn ge(terms: &[(&str, i128)], k: i128) -> Formula {
        Formula::Con(Con {
            lin: lin(terms, k),
            rel: Rel::Ge,
        })
    }

    #[test]
    fn a_relation_prints_with_the_first_atom_on_the_left() {
        assert_eq!(ge(&[("a", -1), ("b", -1)], 49).to_string(), "a + b <= 49");
        assert_eq!(ge(&[("i", -1), ("n", 1)], -2).to_string(), "i <= n - 2");
        assert_eq!(ge(&[("x", 2)], -3).to_string(), "2 * x >= 3");
    }

    #[test]
    fn integer_points_are_decided_where_the_real_shadow_has_points() {
        // 2x = 2y + 1 has real points and no integer point.
        let f = Formula::Con(Con {
            lin: lin(&[("x", 2), ("y", -2)], -1),
            rel: Rel::Eq,
        });
        assert_eq!(satisfiable(&f), Ok(None));
        // 3 <= 2x <= 3 has none either. 27 <= 11x + 13y <= 45, -10 <= 7x - 9y <= 4 has none
        // (Pugh's example): its dark shadow is empty and its real shadow is not, and the
        // splinters, or the exact test on two variables, settle it.
        assert_eq!(
            satisfiable(&Formula::and(vec![
                ge(&[("x", 2)], -3),
                ge(&[("x", -2)], 3)
            ])),
            Ok(None)
        );
        let pugh = Formula::and(vec![
            ge(&[("x", 11), ("y", 13)], -27),
            ge(&[("x", -11), ("y", -13)], 45),
            ge(&[("x", 7), ("y", -9)], 10),
            ge(&[("x", -7), ("y", 9)], 4),
        ]);
        assert_eq!(satisfiable(&pugh), Ok(None));
        // Shifted to hold the point (2, 1), the dark shadow finds a point.
        let shifted = Formula::and(vec![
            ge(&[("x", 11), ("y", 13)], -27),
            ge(&[("x", -11), ("y", -13)], 45),
            ge(&[("x", 7), ("y", -9)], -5),
            ge(&[("x", -7), ("y", 9)], 5),
        ]);
        let m = satisfiable(&shifted).unwrap().unwrap();
        assert!(shifted.holds(&m), "{m:?}");
    }

    fn row(a: &[(usize, i128)], k: i128) -> Row {
        Row {
            a: a.iter().map(|(j, c)| (*j, Int::from(*c))).collect(),
            k: Int::from(k),
        }
    }

    #[test]
    fn columns_of_opposite_signs_merge_and_lift_by_bezout() {
        // `2x - 3y == 1` sees `x` and `y` only through `2x - 3y`, which takes every integer:
        // one variable with column 1, and its point lifted to `x` and `y`.
        let r = row(&[(0, 2), (1, -3)], -1);
        let point = quotient(2, vec![(r.clone(), Rel::Eq)], &[0, 1], &[0], true, &|i| {
            format!("x{i}")
        })
        .expect("decided")
        .expect("a point");
        assert_eq!(r.eval(&point), Int::ZERO);
    }

    #[test]
    fn merged_columns_take_only_the_multiples_of_their_divisor() {
        // `2x + 4y` is even, so `2x + 4y == 1` has no point, though it has rational ones.
        let r = row(&[(0, 2), (1, 4)], -1);
        assert_eq!(
            quotient(2, vec![(r, Rel::Eq)], &[0, 1], &[0], true, &|i| format!(
                "x{i}"
            )),
            Ok(None)
        );
    }

    #[test]
    fn bezout_factors_give_the_divisor() {
        for (a, b) in [
            (0, 5),
            (0, -5),
            (12, 18),
            (12, -18),
            (7, 1),
            (1, -7),
            (6, 35),
        ] {
            let (g, s, t) = bezout(&Int::from(a), &Int::from(b));
            let want = Int::from(a).gcd(&Int::from(b));
            assert_eq!(g, want, "{a} {b}");
            assert_eq!(
                &(&s * &Int::from(a)) + &(&t * &Int::from(b)),
                want,
                "{a} {b}"
            );
        }
    }

    /// Whether the rows `Σ a[i]·x[i] + k >= 0` over `n` variables, with the box `lo`, `hi` as
    /// rows, have no rational point: Fourier–Motzkin over every variable, exact over `Int`.
    fn rationally_empty(
        n: usize,
        rows: &[(Vec<Int>, Int)],
        lo: &[Option<Int>],
        hi: &[Option<Int>],
    ) -> bool {
        let unit = |j: usize, c: i128| -> Vec<Int> {
            (0..n)
                .map(|i| Int::from(if i == j { c } else { 0 }))
                .collect()
        };
        let mut cur: Vec<(Vec<Int>, Int)> = rows.to_vec();
        for j in 0..n {
            if let Some(l) = &lo[j] {
                cur.push((unit(j, 1), -l));
            }
            if let Some(h) = &hi[j] {
                cur.push((unit(j, -1), h.clone()));
            }
        }
        for j in 0..n {
            let (mut pos, mut neg, mut rest) = (Vec::new(), Vec::new(), Vec::new());
            for r in cur {
                if r.0[j].is_positive() {
                    pos.push(r);
                } else if r.0[j].is_negative() {
                    neg.push(r);
                } else {
                    rest.push(r);
                }
            }
            for (pa, pk) in &pos {
                for (qa, qk) in &neg {
                    let (a, b) = (&pa[j], &-&qa[j]);
                    let c: Vec<Int> = (0..n).map(|i| &(b * &pa[i]) + &(a * &qa[i])).collect();
                    let k = &(b * pk) + &(a * qk);
                    let g = c.iter().fold(k.abs(), |g, x| g.gcd(x));
                    if g.is_zero() {
                        rest.push((c, k));
                    } else {
                        rest.push((c.iter().map(|x| x.div_floor(&g)).collect(), k.div_floor(&g)));
                    }
                }
            }
            rest.sort();
            rest.dedup();
            cur = rest;
        }
        cur.iter().any(|(_, k)| k.is_negative())
    }

    /// The rows of `sys` over `n` variables, each as its coefficients by place and its constant.
    fn dense(sys: &System, n: usize) -> Vec<(Vec<Int>, Int)> {
        sys.rows
            .iter()
            .map(|(a, held)| {
                let mut c = vec![Int::ZERO; n];
                for (i, x) in a.iter() {
                    c[*i] = x.clone();
                }
                (c, held.k.clone())
            })
            .collect()
    }

    /// The old box test: some wide row below zero at every point of the box.
    fn a_row_below_zero(sys: &System, lo: &[Option<Int>], hi: &[Option<Int>]) -> bool {
        sys.rows
            .iter()
            .filter(|(a, _)| a.len() > 1)
            .any(|(a, held)| {
                let mut s = held.k.clone();
                for (i, c) in a.iter() {
                    match if c.is_positive() { &hi[*i] } else { &lo[*i] } {
                        Some(b) => s = &s + &(c * b),
                        None => return false,
                    }
                }
                s.is_negative()
            })
    }

    /// A system of the rows `Σ c·x + k >= 0` over variables by place, renamed by `perm`, with
    /// each variable in `[-half, half]`.
    fn boxed_system(rows: &[(Vec<i128>, i128)], perm: &[usize], half: i128) -> System {
        let n = perm.len();
        let mut sys = System::new(0..n);
        for (c, k) in rows {
            let t: Vec<(usize, i128)> = (0..n)
                .filter(|&i| c[i] != 0)
                .map(|i| (perm[i], c[i]))
                .collect();
            let mut t = t;
            t.sort();
            sys.add(row(&t, *k));
        }
        for j in 0..n {
            sys.add(row(&[(j, 1)], half));
            sys.add(row(&[(j, -1)], half));
        }
        sys
    }

    /// A small random generator for the tests below (xorshift).
    struct Draw(u64);

    impl Draw {
        fn int(&mut self, lo: i128, hi: i128) -> i128 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            lo + (self.0 % (hi - lo + 1) as u64) as i128
        }
    }

    /// Every permutation of `0..4`.
    fn perms4() -> Vec<Vec<usize>> {
        let mut out = Vec::new();
        for a in 0..4 {
            for b in 0..4 {
                for c in 0..4 {
                    for d in 0..4 {
                        let p = vec![a, b, c, d];
                        let mut s = p.clone();
                        s.sort();
                        s.dedup();
                        if s.len() == 4 {
                            out.push(p);
                        }
                    }
                }
            }
        }
        out
    }

    #[test]
    fn the_row_test_of_the_box_shows_empty_only_what_has_no_rational_point() {
        // 3000 systems of 2 to 5 rows over four variables in [-4, 4], coefficients up to 7
        // and constants up to 20 (the oracle's 0x38_0a family). Wherever the box test says
        // empty, Fourier–Motzkin finds no rational point in the box it was given; the answer
        // is the same under all 24 namings of the variables, which reorder the rows; and some
        // systems are shown empty only by two rows whose bounds on a variable cross.
        let mut g = Draw(0x38_0a_0b);
        let all = perms4();
        let (mut empty, mut crossed) = (0, 0);
        for _ in 0..3000 {
            let rows: Vec<(Vec<i128>, i128)> = (0..g.int(2, 5))
                .map(|_| ((0..4).map(|_| g.int(-7, 7)).collect(), g.int(-20, 20)))
                .collect();
            let mut answers = Vec::new();
            for p in &all {
                let sys = boxed_system(&rows, p, 4);
                if sys.empty {
                    answers.push(None);
                    continue;
                }
                let Some((lo, hi)) = bounds(&sys) else {
                    answers.push(None);
                    continue;
                };
                let e = box_empty_in(&sys, &lo, &hi);
                if p == &all[0] {
                    if e {
                        assert!(rationally_empty(4, &dense(&sys, 4), &lo, &hi), "{rows:?}");
                    }
                    empty += usize::from(e);
                    crossed += usize::from(e && !a_row_below_zero(&sys, &lo, &hi));
                }
                answers.push(Some(e));
            }
            assert!(answers.windows(2).all(|w| w[0] == w[1]), "{rows:?}");
        }
        assert!(empty > crossed && crossed > 0, "{empty} {crossed}");
    }

    #[test]
    fn the_row_test_of_the_box_keeps_every_system_with_an_integer_point() {
        // 3000 systems of 2 to 6 rows over four variables in [-4, 4], each row holding at a
        // random point of the box with slack 0 to 2: the box test never says empty.
        let mut g = Draw(0x38_0c_0d);
        for _ in 0..3000 {
            let p: Vec<i128> = (0..4).map(|_| g.int(-4, 4)).collect();
            let rows: Vec<(Vec<i128>, i128)> = (0..g.int(2, 6))
                .map(|_| {
                    let c: Vec<i128> = (0..4).map(|_| g.int(-7, 7)).collect();
                    let at: i128 = c.iter().zip(&p).map(|(c, x)| c * x).sum();
                    (c, g.int(0, 2) - at)
                })
                .collect();
            let sys = boxed_system(&rows, &[0, 1, 2, 3], 4);
            let (lo, hi) = bounds(&sys).expect("a box holding the point");
            assert!(!box_empty_in(&sys, &lo, &hi), "{rows:?} at {p:?}");
        }
    }

    /// The box test on the rows `Σ a·x + k >= 0` over `n` variables and the box `lo`, `hi`.
    fn box_test(
        n: usize,
        rows: &[(&[(usize, i128)], Int)],
        lo: &[Option<i128>],
        hi: &[Option<i128>],
    ) -> bool {
        let mut sys = System::new(0..n);
        for (a, k) in rows {
            sys.add(Row {
                a: a.iter().map(|(j, c)| (*j, Int::from(*c))).collect(),
                k: k.clone(),
            });
        }
        let lo: Vec<Option<Int>> = lo.iter().map(|b| b.map(Int::from)).collect();
        let hi: Vec<Option<Int>> = hi.iter().map(|b| b.map(Int::from)).collect();
        box_empty_in(&sys, &lo, &hi)
    }

    #[test]
    fn a_row_with_no_variables_is_below_zero_when_its_constant_is() {
        let (lo, hi) = ([Some(0)], [Some(1)]);
        let (mut least, mut most) = (vec![None], vec![None]);
        let to = |b: &[Option<i128>]| -> Vec<Option<Int>> {
            b.iter().map(|b| b.map(Int::from)).collect()
        };
        let (lo, hi) = (to(&lo), to(&hi));
        assert!(row_box_empty(
            &[],
            &Int::from(-1),
            &lo,
            &hi,
            &mut least,
            &mut most
        ));
        assert!(!row_box_empty(
            &[],
            &Int::ZERO,
            &lo,
            &hi,
            &mut least,
            &mut most
        ));
    }

    #[test]
    fn a_variable_with_no_bound_on_the_side_a_row_needs_is_bounded_by_that_row() {
        // x0 has no bound and x1 is in [0, 1]. `2·x0 - x1 - 3 >= 0` needs the upper bound of
        // x0, so it bounds x0 alone: x0 >= 3/2. `-2·x0 - x1 + k >= 0` gives x0 <= k/2, below
        // 3/2 for k = 2 (empty) and not for k = 4 (the point (2, 0)).
        let (lo, hi) = ([None, Some(0)], [None, Some(1)]);
        let a: &[(usize, i128)] = &[(0, 2), (1, -1)];
        let b: &[(usize, i128)] = &[(0, -2), (1, -1)];
        for (k, empty) in [(2, true), (3, false), (4, false)] {
            let rows = [(a, Int::from(-3)), (b, Int::from(k))];
            assert_eq!(box_test(2, &rows, &lo, &hi), empty, "k = {k}");
        }
        // With x2 unbounded too, `x0 + x2 - 100 >= 0` lacks two bounds and bounds neither.
        let c: &[(usize, i128)] = &[(0, 1), (2, 1)];
        let rows = [(a, Int::from(-3)), (c, Int::from(-100))];
        assert!(!box_test(
            3,
            &rows,
            &[None, Some(0), None],
            &[None, Some(1), None]
        ));
    }

    #[test]
    fn bounds_at_the_edge_of_i128_cross_exactly() {
        // `P·x0 + x1 - (P - 1) >= 0` and `-P·x0 + x1 + R >= 0` with P = i128::MAX, x0 in
        // [-1, 1] and x1 in [0, 1]: x0 >= (P - 2)/P and x0 <= (R + 1)/P. Each row's largest
        // value in the box passes i128 and is positive; the bounds cross for R = P - 10 and
        // meet at one point for R = P - 3.
        let p = i128::MAX;
        let (lo, hi) = ([Some(-1), Some(0)], [Some(1), Some(1)]);
        let a: &[(usize, i128)] = &[(0, p), (1, 1)];
        let b: &[(usize, i128)] = &[(0, -p), (1, 1)];
        for (r, empty) in [(p - 10, true), (p - 3, false), (p, false)] {
            let rows = [(a, -&Int::from(p - 1)), (b, Int::from(r))];
            assert_eq!(box_test(2, &rows, &lo, &hi), empty, "R = P - {}", p - r);
        }
    }

    /// A chain of `&&` or `||` as the translator reads it: a leaf is an operand's formula
    /// and whether it is a name's (kept whole), and an inner node joins two chains.
    enum Chain {
        Leaf(Formula, bool),
        Join(Box<Chain>, Box<Chain>),
    }

    /// A pseudo-random number generator (xorshift64), so the cases are the same on each run.
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: u64) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0 % n
        }
    }

    /// A small random formula over `x` and `y`: a constraint `>= 0` or `== 0` on a term
    /// with a small constant, `true`, `false`, a negation, or a conjunction or disjunction
    /// of one to three of these built directly, so one with a single part occurs too.
    fn small(rng: &mut Rng, depth: u32) -> Formula {
        let con = |rng: &mut Rng| {
            let terms: &[(&str, i128)] = match rng.below(3) {
                0 => &[("x", 1)],
                1 => &[("y", -1)],
                _ => &[("x", 1), ("y", 1)],
            };
            let rel = if rng.below(4) == 0 { Rel::Eq } else { Rel::Ge };
            Formula::Con(Con {
                lin: lin(terms, rng.below(3) as i128 - 1),
                rel,
            })
        };
        match rng.below(if depth == 0 { 4 } else { 8 }) {
            0 | 1 => con(rng),
            2 => Formula::top(),
            3 => Formula::bottom(),
            4 => Formula::negate(con(rng)),
            k => {
                let parts = (0..=rng.below(3)).map(|_| small(rng, depth - 1)).collect();
                if k % 2 == 0 {
                    Formula::And(Shared::new(parts))
                } else {
                    Formula::Or(Shared::new(parts))
                }
            }
        }
    }

    fn chain(rng: &mut Rng, depth: u32) -> Chain {
        if depth == 0 || rng.below(3) == 0 {
            Chain::Leaf(small(rng, 2), rng.below(2) == 0)
        } else {
            Chain::Join(
                Box::new(chain(rng, depth - 1)),
                Box::new(chain(rng, depth - 1)),
            )
        }
    }

    /// The chain joined two at a time, as the translator joined it before `Joining`: an
    /// inner node is no name, so its formula is not kept.
    fn two_at_a_time(c: &Chain, and: bool) -> (Formula, bool) {
        match c {
            Chain::Leaf(f, kept) => (f.clone(), *kept),
            Chain::Join(a, b) => {
                let ((fa, ka), (fb, kb)) = (two_at_a_time(a, and), two_at_a_time(b, and));
                let keep = |i: usize| [ka, kb][i];
                let f = if and {
                    and_keeping_before(vec![fa, fb], keep)
                } else {
                    or_keeping_before(vec![fa, fb], keep)
                };
                (f, false)
            }
        }
    }

    /// The chain in one `Joining`, read as `preimage::Tx::chain` reads it.
    fn in_one(c: &Chain, and: bool) -> Formula {
        fn add(c: &Chain, j: &mut Joining) {
            match c {
                Chain::Leaf(f, kept) => j.operand(f.clone(), *kept),
                Chain::Join(a, b) => {
                    let mark = j.mark();
                    add(a, j);
                    add(b, j);
                    j.close(mark);
                }
            }
        }
        let Chain::Join(a, b) = c else {
            unreachable!("a chain of two operands")
        };
        let mut j = Joining::new(and);
        add(a, &mut j);
        add(b, &mut j);
        j.finish()
    }

    /// The formula's tree as built, each node and its parts, with kept parts shown as such:
    /// compare, hash and show read a kept part as flattened, and this must not.
    fn built(f: &Formula) -> String {
        match f {
            Formula::Con(c) => format!("({c})"),
            Formula::Not(g) => format!("!{}", built(g)),
            Formula::And(gs) => format!(
                "and[{}]",
                gs.iter().map(built).collect::<Vec<_>>().join(", ")
            ),
            Formula::Or(gs) => format!(
                "or[{}]",
                gs.iter().map(built).collect::<Vec<_>>().join(", ")
            ),
        }
    }

    #[test]
    fn a_chain_joined_in_one_pass_is_built_as_joined_two_at_a_time() {
        let mut rng = Rng(0x2545_f491_4f6c_dd1d);
        let mut kinds = std::collections::BTreeSet::new();
        for round in 0..20_000 {
            // A chain is a `&&` or `||` of two operands, never one operand alone.
            let c = Chain::Join(Box::new(chain(&mut rng, 4)), Box::new(chain(&mut rng, 4)));
            for and in [true, false] {
                let (old, _) = two_at_a_time(&c, and);
                let new = in_one(&c, and);
                assert_eq!(built(&new), built(&old), "round {round}, and = {and}");
                kinds.insert(built(&old).chars().take(3).collect::<String>());
            }
        }
        // `true`, `false`, constraints, negations, conjunctions and disjunctions all occur.
        assert!(kinds.len() >= 5, "{kinds:?}");
    }

    /// The hulls of a system of difference constraints and bounds found by one shortest-path
    /// pass are those found by asking the solver of each atom ([`hull_from`]), on random
    /// systems of up to 8 rows over 5 names, some without a bound on a side; a row with a
    /// coefficient of 2 or three atoms is not taken.
    #[test]
    fn difference_hulls_are_those_the_solver_finds() {
        let names = ["a", "b", "c", "d", "e"];
        let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
        let mut compared = 0;
        for _ in 0..1500 {
            let rows = 1 + rng.below(8) as usize;
            let cons: Vec<Con> = (0..rows)
                .map(|_| {
                    let x = names[rng.below(5) as usize];
                    let k = rng.below(13) as i128 - 6;
                    let terms: Vec<(&str, i128)> = match rng.below(4) {
                        0 => vec![(x, 1)],
                        1 => vec![(x, -1)],
                        _ => {
                            let y = names[rng.below(5) as usize];
                            if x == y {
                                vec![(x, 1)]
                            } else {
                                vec![(x, 1), (y, -1)]
                            }
                        }
                    };
                    let rel = if rng.below(5) == 0 { Rel::Eq } else { Rel::Ge };
                    Con {
                        lin: lin(&terms, k),
                        rel,
                    }
                })
                .collect();
            let Ok(Some(model)) = solve(&cons, true) else {
                continue;
            };
            let refs: Vec<&Con> = cons.iter().collect();
            let hulls = difference_hulls(&refs, &model).expect("difference rows");
            let whole = Formula::and(cons.iter().cloned().map(Formula::Con).collect());
            for (a, h) in &hulls {
                assert_eq!(
                    Ok(h.clone()),
                    hull_from(&whole, a, &model),
                    "{whole} onto {a}"
                );
                compared += 1;
            }
        }
        assert!(compared > 1000, "{compared}");
        let two = [Con {
            lin: lin(&[("a", 2), ("b", -1)], 0),
            rel: Rel::Ge,
        }];
        let three = [Con {
            lin: lin(&[("a", 1), ("b", -1), ("c", 1)], 0),
            rel: Rel::Ge,
        }];
        let m: Model = [
            (sym("a"), Int::ZERO),
            (sym("b"), Int::ZERO),
            (sym("c"), Int::ZERO),
        ]
        .into_iter()
        .collect();
        assert!(difference_hulls(&[&two[0]], &m).is_none());
        assert!(difference_hulls(&[&three[0]], &m).is_none());
    }

    /// The bounds [`part_bounds`] gives each atom of a part contain the hull the solver finds
    /// ([`hull_from`]), on random parts of up to 6 rows over 4 names with coefficients from -3
    /// to 3 and up to three atoms a row, some with a disjunction of two conjunctions of such
    /// rows, with a random set of the names as factors; and they are the hull itself for many
    /// atoms, so the comparison is not empty. Each side that [`products`] takes as known to be
    /// the hull is the hull: every side where the bounds are hulls, a side the point meets, and
    /// a missing side that [`signs`] shows to be open.
    #[test]
    fn part_bounds_contain_the_hulls_the_solver_finds() {
        let names = ["a", "b", "c", "d"];
        let mut rng = Rng(0x2545_f491_4f6c_dd1d);
        let row = |rng: &mut Rng| {
            let terms: Vec<(&str, i128)> = (0..1 + rng.below(3))
                .map(|_| {
                    let k = 1 + rng.below(3) as i128;
                    let k = if rng.below(2) == 0 { k } else { -k };
                    (names[rng.below(4) as usize], k)
                })
                .collect();
            let rel = if rng.below(5) == 0 { Rel::Eq } else { Rel::Ge };
            Formula::Con(Con {
                lin: lin(&terms, rng.below(13) as i128 - 6),
                rel,
            })
        };
        let (mut compared, mut same, mut known) = (0, 0, 0);
        for _ in 0..1500 {
            let mut parts: Vec<Formula> = (0..1 + rng.below(6)).map(|_| row(&mut rng)).collect();
            if rng.below(3) == 0 {
                let side = |rng: &mut Rng| {
                    let n = 1 + rng.below(2);
                    Formula::and((0..n).map(|_| row(rng)).collect())
                };
                let (l, r) = (side(&mut rng), side(&mut rng));
                parts.push(Formula::or(vec![l, r]));
            }
            let whole = Formula::and(parts);
            let Ok(Some(model)) = satisfiable_inner(&whole) else {
                continue;
            };
            let factors: Vec<Atom> = (whole.atoms().into_iter())
                .filter(|_| rng.below(2) == 0)
                .collect();
            let bounds = part_bounds(&whole, &model, &factors.iter().collect::<Vec<_>>());
            let signs = signs(&whole);
            for a in whole.atoms() {
                let Ok(hull) = hull_from(&whole, &a, &model) else {
                    continue;
                };
                let end =
                    |e: &Option<Int>, inf: End| e.as_ref().map_or(inf, |v| End::Fin(Num::from(v)));
                let (lo, hi) = bounds.ends.get(&a).cloned().unwrap_or_default();
                let found = IntervalSet::range(end(&lo, End::NegInf), end(&hi, End::PosInf));
                assert!(
                    hull.is_subset(&found),
                    "{whole} onto {a}: {hull} in {found}"
                );
                compared += 1;
                same += usize::from(hull.hull() == found);
                let (h_lo, h_hi) = hull.bounds().expect("the part has a point");
                let (pos, neg) = signs[&a];
                let sides = [
                    (&lo, End::NegInf, h_lo, !pos),
                    (&hi, End::PosInf, h_hi, !neg),
                ];
                for (e, inf, h, open) in sides {
                    let sure = (bounds.hulls && factors.contains(&a))
                        || match e {
                            Some(v) => model.get(&a) == Some(v),
                            None => open,
                        };
                    if sure {
                        known += 1;
                        assert_eq!(&end(e, inf), h, "{whole} onto {a}: {e:?} for {hull}");
                    }
                }
            }
        }
        assert!(
            compared > 1000 && same > compared / 4 && known > compared / 2,
            "{same} and {known} of {compared}"
        );
    }

    /// Calls `f` with each order of `0..n`, by Heap's method.
    fn each_order(n: usize, f: &mut impl FnMut(&[usize])) {
        let mut p: Vec<usize> = (0..n).collect();
        let mut c = vec![0; n];
        f(&p);
        let mut i = 1;
        while i < n {
            if c[i] < i {
                if i % 2 == 0 {
                    p.swap(0, i);
                } else {
                    p.swap(c[i], i);
                }
                f(&p);
                c[i] += 1;
                i = 1;
            } else {
                c[i] = 0;
                i += 1;
            }
        }
    }

    /// Variables with a value each, joined by equalities `x[a] - x[b] == value[a] - value[b]`
    /// along `edges`, and the color of each.
    struct Classes {
        value: Vec<i64>,
        keys: Vec<usize>,
        edges: Vec<(usize, usize)>,
    }

    impl Classes {
        /// The representatives of the forest that joins `edges` in `order`, edge `e` written
        /// `equate(b, a, -d)` in place of `equate(a, b, d)` when bit `e` of `flip` is set; the
        /// root of each variable; and the greatest rank of a root.
        fn joined(&self, order: &[usize], flip: &[bool]) -> (Vec<(usize, Int)>, Vec<usize>, usize) {
            let mut ties = Ties::new(self.value.len());
            for &e in order {
                let (a, b) = self.edges[e];
                let (x, y) = if flip[e] { (b, a) } else { (a, b) };
                assert!(ties.equate(x, y, Int::from(self.value[x] - self.value[y])));
            }
            let roots = (0..self.value.len()).map(|i| ties.root(i).0).collect();
            let rank = ties.rank.iter().copied().max().unwrap_or(0);
            (ties.representatives(&self.keys), roots, rank)
        }

        /// What `representatives` must give, from the values: in each class the member of
        /// least color, then value, then place, and each variable's value less that member's.
        fn expected(&self) -> Vec<(usize, Int)> {
            let n = self.value.len();
            let mut class: Vec<usize> = (0..n).collect();
            fn top(class: &mut [usize], mut i: usize) -> usize {
                while class[i] != i {
                    i = class[i];
                }
                i
            }
            for &(a, b) in &self.edges {
                let (ra, rb) = (top(&mut class, a), top(&mut class, b));
                class[ra.max(rb)] = ra.min(rb);
            }
            let class: Vec<usize> = (0..n).map(|i| top(&mut class, i)).collect();
            (0..n)
                .map(|i| {
                    let rep = (0..n)
                        .filter(|&j| class[j] == class[i])
                        .min_by_key(|&j| (self.keys[j], self.value[j], j))
                        .expect("a class has a member");
                    (rep, Int::from(self.value[i] - self.value[rep]))
                })
                .collect()
        }
    }

    #[test]
    fn the_representatives_of_joined_equalities_do_not_depend_on_their_order() {
        // Three classes: {0, 2, 4, 6, 7} by five equalities, one of them implied by the
        // others, with 2 and 4 of one color and one value, so their places choose; {1, 3, 8},
        // all of one color; and {5} alone. Every order of the seven equalities, each written
        // either way round, gives one vector, though the roots differ (union by rank orients
        // a join of roots of equal rank by the order of the arguments).
        let small = Classes {
            value: vec![5, 0, 3, -4, 3, 0, 7, 3, 6],
            keys: vec![1, 2, 0, 2, 0, 0, 0, 1, 2],
            edges: vec![(0, 2), (4, 6), (7, 0), (6, 2), (4, 7), (1, 3), (8, 1)],
        };
        let want = small.expected();
        assert_eq!(want[0].0, 2, "{want:?}");
        assert_eq!(want[1].0, 3, "{want:?}");
        let mut roots = BTreeSet::new();
        each_order(small.edges.len(), &mut |order| {
            for bits in 0..1u32 << small.edges.len() {
                let flip: Vec<bool> = (0..small.edges.len()).map(|e| bits >> e & 1 == 1).collect();
                let (got, r, _) = small.joined(order, &flip);
                assert_eq!(got, want, "order {order:?}, flipped {flip:?}");
                roots.insert(r);
            }
        });
        assert!(roots.len() > 1, "the roots never differ: {roots:?}");
        // Classes of 16, 8 (one color), 2 and 1 joined by random trees with three implied
        // equalities each, in 400 random orders and orientations: roots of rank 2 and more
        // are joined, so equal ranks occur above the leaves.
        let mut rng = Rng(0x38_0e1e);
        let sizes = [16, 8, 2, 1];
        let n: usize = sizes.iter().sum();
        let mut place: Vec<usize> = (0..n).collect();
        for i in (1..n).rev() {
            place.swap(i, rng.below(i as u64 + 1) as usize);
        }
        let mut value = vec![0; n];
        let mut keys = vec![0; n];
        let mut edges = Vec::new();
        let mut start = 0;
        for (c, &size) in sizes.iter().enumerate() {
            let members = &place[start..start + size];
            for (k, &m) in members.iter().enumerate() {
                value[m] = rng.below(5) as i64 - 2;
                keys[m] = if c == 1 { 7 } else { rng.below(3) as usize };
                if k > 0 {
                    edges.push((m, members[rng.below(k as u64) as usize]));
                }
            }
            if size > 2 {
                for _ in 0..3 {
                    let a = members[rng.below(size as u64) as usize];
                    let b = members[rng.below(size as u64) as usize];
                    edges.push((a, b));
                }
            }
            start += size;
        }
        let large = Classes { value, keys, edges };
        let want = large.expected();
        let mut roots = BTreeSet::new();
        let mut rank = 0;
        let m = large.edges.len();
        for _ in 0..400 {
            let mut order: Vec<usize> = (0..m).collect();
            for i in (1..m).rev() {
                order.swap(i, rng.below(i as u64 + 1) as usize);
            }
            let flip: Vec<bool> = (0..m).map(|_| rng.below(2) == 1).collect();
            let (got, r, k) = large.joined(&order, &flip);
            assert_eq!(got, want, "order {order:?}, flipped {flip:?}");
            roots.insert(r);
            rank = rank.max(k);
        }
        assert!(roots.len() > 1, "the roots never differ");
        assert!(
            rank >= 2,
            "no join of two roots of rank 1: greatest rank {rank}"
        );
    }
}

#[cfg(test)]
mod difference_rows {
    use super::*;

    /// A pseudo-random number generator (xorshift64), so the cases are the same on each run.
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: u64) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0 % n
        }
    }

    fn x(i: usize) -> Lin {
        Lin::atom(Atom::Sym(format!("x{i}").into()))
    }

    /// `x[i] - x[j] + k >= 0`, or `== 0`; with `j == i`, the bound `x[i] + k >= 0`, and with
    /// `sum`, `x[i] + x[j] + k >= 0`.
    fn row(i: usize, j: usize, k: i128, eq: bool, sum: bool) -> Con {
        let mut l = x(i).plus(&Lin::constant(k));
        if j != i {
            l = l.plus(&x(j).times(if sum { 1 } else { -1 }));
        }
        Con {
            lin: l,
            rel: if eq { Rel::Eq } else { Rel::Ge },
        }
    }

    /// Whether the rows `x[i] - x[j] + k >= 0` (`x[j] <= x[i] + k`, an edge `i → j` of weight
    /// `k`; the bounds are edges from and to a node for zero) have no point: a cycle of
    /// negative weight, by Bellman-Ford. Over the integers as over the reals, since the
    /// weights are integers.
    fn negative_cycle(n: usize, edges: &[(usize, usize, i128)]) -> bool {
        let mut d = vec![0i128; n + 1];
        for _ in 0..=n + 1 {
            let mut moved = false;
            for &(a, b, w) in edges {
                if d[a] + w < d[b] {
                    d[b] = d[a] + w;
                    moved = true;
                }
            }
            if !moved {
                return false;
            }
        }
        true
    }

    /// The premise of the fast path for groups of difference rows (DISJ-diff-fast, question
    /// A44): `solve` never refuses a system whose rows are all `±x ± y + k >= 0`, `± x + k >=
    /// 0` or such equalities, with or without a model wanted, and its answer is that of
    /// Bellman-Ford on the rows `x - y + k`. Shapes chosen to tie: cycles and cliques whose
    /// rows are all alike, stars of alike leaves, chains, and random graphs.
    #[test]
    fn solve_never_refuses_rows_of_two_unit_terms() {
        let mut rng = Rng(0xd1ff_0a44);
        let (mut empty, mut point) = (0, 0);
        for case in 0..6000 {
            let n = 2 + rng.below(24) as usize;
            let sum_ok = case % 3 == 2;
            let k = |rng: &mut Rng, alike: bool| {
                if alike { 0 } else { rng.below(9) as i128 - 4 }
            };
            let alike = rng.below(3) == 0;
            let mut pairs: Vec<(usize, usize)> = Vec::new();
            match rng.below(5) {
                0 => pairs.extend((0..n).map(|i| (i, (i + 1) % n))),
                1 => {
                    for i in 0..n.min(9) {
                        for j in 0..n.min(9) {
                            if i != j {
                                pairs.push((i, j));
                            }
                        }
                    }
                }
                2 => pairs.extend((1..n).flat_map(|i| [(0, i), (i, 0)])),
                3 => pairs.extend((0..n - 1).map(|i| (i + 1, i))),
                _ => {
                    for _ in 0..rng.below(3 * n as u64) + 1 {
                        let i = rng.below(n as u64) as usize;
                        let j = rng.below(n as u64) as usize;
                        pairs.push((i, j));
                    }
                }
            }
            let mut cons = Vec::new();
            let mut edges = Vec::new();
            let mut sums = false;
            for (i, j) in pairs {
                let c = k(&mut rng, alike);
                let eq = rng.below(6) == 0;
                let sum = sum_ok && i != j && rng.below(3) == 0;
                sums |= sum;
                cons.push(row(i, j, c, eq, sum));
                if i != j && !sum {
                    edges.push((i + 1, j + 1, c));
                    if eq {
                        edges.push((j + 1, i + 1, -c));
                    }
                }
                if i == j {
                    // `x[i] + c >= 0`: `0 <= x[i] + c`, an edge `i → zero` of weight `c`.
                    edges.push((i + 1, 0, c));
                    if eq {
                        edges.push((0, i + 1, -c));
                    }
                }
            }
            for _ in 0..rng.below(4) {
                let i = rng.below(n as u64) as usize;
                let c = rng.below(21) as i128 - 10;
                cons.push(Con {
                    lin: x(i).times(-1).plus(&Lin::constant(c)),
                    rel: Rel::Ge,
                });
                edges.push((0, i + 1, c));
            }
            let quick = solve(&cons, false);
            let full = solve(&cons, true);
            let (Ok(quick), Ok(full)) = (&quick, &full) else {
                panic!("refused: {quick:?} {full:?} on {cons:?}");
            };
            assert_eq!(quick.is_some(), full.is_some(), "{cons:?}");
            if let Some(m) = full {
                point += 1;
                assert!(cons.iter().all(|c| c.holds(m)), "{cons:?} at {m:?}");
            } else {
                empty += 1;
            }
            if !sums {
                assert_eq!(negative_cycle(n, &edges), full.is_none(), "{cons:?}");
            }
        }
        assert!(
            empty > 1000 && point > 1000,
            "{empty} empty, {point} with a point"
        );
    }
}

#[cfg(test)]
mod by_halves_against_old {
    use super::*;

    /// A pseudo-random number generator (xorshift64), so the cases are the same on each run.
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: u64) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0 % n
        }
    }

    fn v(i: usize) -> Lin {
        Lin::atom(Atom::Sym(format!("v{i}").into()))
    }

    fn ge(l: Lin) -> Formula {
        Formula::Con(Con::ge(&l, &Lin::default()))
    }

    fn eq(l: Lin) -> Formula {
        Formula::Con(Con::eq(&l, &Lin::default()))
    }

    /// A group of `n` atoms in `0..=20` linked by edges of a chain, a tree or a sparse random
    /// graph, each a difference row `v[b] - v[a] + k >= 0` or, with `general`, a row of three
    /// atoms `v[b] - v[a] - v[c] + k >= 0`, with disjunctions on the forms of some edges, each
    /// two or three disjuncts of a bound or an equality, so that some hold at the least point,
    /// some at none and some are empty.
    fn group(rng: &mut Rng, general: bool) -> (Formula, Vec<Atom>) {
        let n = 3 + rng.below(10) as usize;
        let mut edges: Vec<(usize, usize)> = match rng.below(3) {
            0 => (0..n - 1).map(|i| (i, i + 1)).collect(),
            1 => (1..n).map(|i| (rng.below(i as u64) as usize, i)).collect(),
            _ => (0..n + n / 2)
                .map(|_| (rng.below(n as u64) as usize, rng.below(n as u64) as usize))
                .filter(|(a, b)| a != b)
                .collect(),
        };
        edges.sort_unstable();
        edges.dedup();
        let form = |rng: &mut Rng, (a, b): (usize, usize)| {
            let l = v(b).minus(&v(a));
            if general {
                let c = rng.below(n as u64) as usize;
                if c != a && c != b {
                    return l.minus(&v(c));
                }
            }
            l
        };
        let mut fs: Vec<Formula> = Vec::new();
        for i in 0..n {
            fs.push(ge(v(i)));
            fs.push(ge(Lin::constant(20).minus(&v(i))));
        }
        for &e in &edges {
            let k = rng.below(5) as i128 - 2;
            fs.push(ge(form(rng, e).plus(&Lin::constant(k))));
        }
        for _ in 0..1 + rng.below(4) {
            let Some(&e) = edges.get(rng.below(edges.len().max(1) as u64) as usize) else {
                break;
            };
            let f = form(rng, e);
            let ds = (0..2 + rng.below(2))
                .map(|_| {
                    let c = Lin::constant(rng.below(13) as i128 - 4);
                    match rng.below(3) {
                        0 => ge(c.minus(&f)),
                        1 => ge(f.minus(&c)),
                        _ => eq(f.minus(&c)),
                    }
                })
                .collect();
            fs.push(Formula::or(ds));
        }
        let syms = (0..n).map(|i| Atom::Sym(format!("v{i}").into())).collect();
        (Formula::and(fs), syms)
    }

    fn old<T>(run: impl FnOnce() -> T) -> T {
        OLD_PATH.with(|o| o.set(true));
        let out = run();
        OLD_PATH.with(|o| o.set(false));
        out
    }

    /// The projections by halves (DISJ-diff-fast, DISJ-incremental) give the answers of the
    /// path before them: [`decide`] the same answer, [`satisfiable`] a point exactly when the
    /// old one does, and a point of the formula; [`project_each`] and [`project`] a hull within
    /// the old one, equal to it on every symbol whose old hull was found without a refused
    /// question, and never a refusal where the old path answered. Batch ([`project_each`]) and
    /// single ([`project`]) projections agree on the new path.
    #[test]
    fn answers_are_those_of_the_old_path() {
        let mut rng = Rng(0x0d15_6a1f);
        let (mut cases, mut narrower) = (0, 0);
        for case in 0..600 {
            let general = case % 2 == 1;
            let (f, syms) = group(&mut rng, general);
            let (d_new, d_old) = (decide(&f), old(|| decide(&f)));
            match (&d_new, &d_old) {
                (Ok(a), Ok(b)) => assert_eq!(a, b, "decide, case {case}: {f}"),
                (Err(_), Ok(_)) => panic!("decide refused, case {case}: {f}"),
                _ => {}
            }
            let (s_new, s_old) = (satisfiable(&f), old(|| satisfiable(&f)));
            match (&s_new, &s_old) {
                (Ok(a), Ok(b)) => {
                    assert_eq!(a.is_some(), b.is_some(), "satisfiable, case {case}: {f}");
                    if let Some(m) = a {
                        assert!(f.holds(m), "a point that does not hold, case {case}: {f}");
                    }
                }
                (Err(_), Ok(_)) => panic!("satisfiable refused, case {case}: {f}"),
                _ => {}
            }
            let (e_new, e_old) = (project_each(&f, &syms), old(|| project_each(&f, &syms)));
            match (&e_new, &e_old) {
                (Ok((a, causes)), Ok((b, skipped))) => {
                    assert!(
                        causes.iter().all(|r| skipped.contains(r)),
                        "a disjunction left out for {causes:?}, before for {skipped:?}, case {case}: {f}"
                    );
                    for ((x, y), sym) in a.iter().zip(b).zip(&syms) {
                        match (x, y) {
                            (Ok(x), Ok(y)) => {
                                assert!(
                                    x.is_subset(y),
                                    "{sym} {x:?} not in {y:?}, case {case}: {f}"
                                );
                                if x != y {
                                    narrower += 1;
                                    // A narrower hull is sound when every value it drops has
                                    // no point: `decide` on the old path says so for each.
                                    for val in (0..=20i128).filter(|&val| {
                                        y.contains(val as i64) && !x.contains(val as i64)
                                    }) {
                                        let g = Formula::and(vec![
                                            f.clone(),
                                            eq(Lin::atom(sym.clone()).minus(&Lin::constant(val))),
                                        ]);
                                        assert_eq!(
                                            old(|| decide(&g)).ok(),
                                            Some(false),
                                            "{sym} {x:?} drops {val}, which has a point, case {case}: {f}"
                                        );
                                    }
                                }
                                let one = project(&f, sym);
                                assert_eq!(
                                    one.as_ref().ok(),
                                    Some(x),
                                    "batch and single, {sym}, case {case}: {f}"
                                );
                            }
                            (Err(_), Ok(_)) => panic!("{sym} refused, case {case}: {f}"),
                            _ => {}
                        }
                    }
                }
                (Err(_), Ok(_)) => panic!("project_each refused, case {case}: {f}"),
                _ => {}
            }
            cases += 1;
        }
        assert_eq!(cases, 600);
        eprintln!("hulls narrower than the old path's: {narrower}");
    }

    /// `n` stages, each `y[k]` in `{0, -2}` with `y[k] == -1 or z[k] >= 0` and `z[k] <= 5`,
    /// with `chain`, `y[k+1] - y[k] >= -2` linking each stage to the next (item
    /// PROJECT-dead2-quadratic). The disjunct `y[k] == -1` has no point, but only beside the
    /// other disjunction of its stage, so each test of a disjunct reads the stage's rows.
    fn dead2(n: usize, chain: bool) -> (Formula, Vec<Atom>) {
        let a = |s: &str, k: usize| Atom::Sym(format!("{s}{k}").into());
        let (y, z) = (|k| Lin::atom(a("y", k)), |k| Lin::atom(a("z", k)));
        let k = Lin::constant;
        let mut fs = Vec::new();
        for i in 0..n {
            if chain && i + 1 < n {
                fs.push(ge(y(i + 1).minus(&y(i)).plus(&k(2))));
            }
            fs.push(Formula::or(vec![eq(y(i)), eq(y(i).plus(&k(2)))]));
            fs.push(Formula::or(vec![eq(y(i).plus(&k(1))), ge(z(i))]));
            fs.push(ge(k(5).minus(&z(i))));
        }
        let syms = (0..n).flat_map(|i| [a("y", i), a("z", i)]).collect();
        (Formula::and(fs), syms)
    }

    /// The stages' disjunctions tested against the base projected onto their atoms
    /// ([`stage_kernels`]) give the hulls of the old path, which tested each against the
    /// base's whole group, on every symbol: `y` in `{-2, 0}`, `z` in `[0..=5]`, whose lower
    /// bound the removal by values ([`values::drop_outside_values`]) finds on both paths.
    #[test]
    fn dead2_hulls_are_those_of_the_old_path() {
        for chain in [false, true] {
            for n in [1, 2, 3, 8, 17] {
                let (f, syms) = dead2(n, chain);
                let new = project_each(&f, &syms).expect("answered");
                let old = old(|| project_each(&f, &syms)).expect("answered");
                assert_eq!(new.0, old.0, "n = {n}, chain = {chain}");
                assert_eq!((new.1.len(), old.1.len()), (0, 0));
                for (h, s) in new.0.iter().zip(&syms) {
                    let h = h.as_ref().expect("not refused").to_string();
                    let want = if s.to_string().starts_with('y') {
                        "[-2..=-2, 0..=0]"
                    } else {
                        "[0..=5]"
                    };
                    assert_eq!(h, want, "{s}, n = {n}, chain = {chain}");
                }
            }
        }
    }
}

#[cfg(test)]
mod dark_shadow {
    use super::*;

    /// A pseudo-random number generator (xorshift64), so the cases are the same on each run.
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: u64) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0 % n
        }
    }

    fn a(s: &str) -> Atom {
        Atom::Sym(s.into())
    }

    /// Whether the rows hold at `y` and `z` for some `r` in `-4..=4` (every row bounds `r`
    /// there), counted, not solved.
    fn points(rows: &[Con], y: i128, z: i128) -> bool {
        (-4..=4).any(|r| {
            let m: Model = [(a("y"), y), (a("z"), z), (a("r"), r)]
                .into_iter()
                .map(|(k, v)| (k, Int::from(v)))
                .collect();
            rows.iter().all(|c| c.holds(&m))
        })
    }

    /// `shadow` with dark shadows projects out `r` exactly or keeps it: on small systems over
    /// `y`, `z` and `r`, with coefficients of `r` from -4 to 4, the integer points of the result
    /// on `y` and `z` are those of the system. Bounds such as `4·r <= y <= 4·r + 1`, whose real
    /// shadow has points (`y = 2`) the system has not, are the case the dark shadow keeps.
    #[test]
    fn projections_with_dark_shadows_keep_the_integer_points() {
        let mut rng = Rng(0x5eed_da4c);
        let (mut cases, mut gone) = (0, 0);
        for _ in 0..400 {
            let mut rows = vec![
                Con::ge(&Lin::atom(a("r")), &Lin::constant(-4)),
                Con::ge(&Lin::constant(4), &Lin::atom(a("r"))),
            ];
            for _ in 0..2 + rng.below(3) {
                let k = |rng: &mut Rng, n: u64| rng.below(2 * n + 1) as i128 - n as i128;
                let lin = Lin::atom(a("r"))
                    .times(k(&mut rng, 4))
                    .plus(&Lin::atom(a("y")).times(k(&mut rng, 2)))
                    .plus(&Lin::atom(a("z")).times(k(&mut rng, 1)))
                    .plus(&Lin::constant(k(&mut rng, 6)));
                rows.push(Con::ge(&lin, &Lin::default()));
            }
            let keep = |x: &Atom| *x != a("r");
            let Some(out) = shadow(&rows, &keep, true) else {
                let none = (-12..=12).all(|y| (-12..=12).all(|z| !points(&rows, y, z)));
                assert!(none, "{rows:?}: no point found, but it has one");
                continue;
            };
            cases += 1;
            gone += usize::from(out.iter().all(|c| !c.lin.terms.contains_key(&a("r"))));
            for y in -12..=12 {
                for z in -12..=12 {
                    assert_eq!(
                        points(&rows, y, z),
                        points(&out, y, z),
                        "{rows:?} projected to {out:?} at y = {y}, z = {z}"
                    );
                }
            }
        }
        assert!(
            cases >= 300 && gone >= 100,
            "{cases} cases, {gone} projected"
        );
    }

    /// The bounds `4·r <= y <= 4·r + 1` of `r` from 0 to 1 have `y` in {0, 1, 4, 5}: their real
    /// shadow `0 <= y <= 5` is not their projection, so `r` is kept.
    #[test]
    fn bounds_with_a_gap_are_kept() {
        let y = || Lin::atom(a("y"));
        let r4 = || Lin::atom(a("r")).times(4);
        let rows = vec![
            Con::ge(&Lin::atom(a("r")), &Lin::default()),
            Con::ge(&Lin::constant(1), &Lin::atom(a("r"))),
            Con::ge(&y(), &r4()),
            Con::ge(&r4().plus(&Lin::constant(1)), &y()),
        ];
        let out = shadow(&rows, &|x| *x != a("r"), true).expect("a point");
        assert!(points(&out, 4, 0) && !points(&out, 2, 0), "{out:?}");
    }
}

#[cfg(test)]
mod jointly_empty_order {
    use super::*;

    fn x(i: usize) -> Lin {
        Lin::atom(Atom::Sym(format!("x{i:05}").into()))
    }

    fn any_of(l: &Lin, vs: &[i128]) -> Vec<Rc<Parts>> {
        (vs.iter())
            .map(|v| {
                let mut p = Parts::default();
                p.cons = vec![Con::eq(l, &Lin::constant(*v))];
                Rc::new(p)
            })
            .collect()
    }

    /// The values each disjunction keeps, by the constant of its first disjunct's row.
    fn kept(ors: &[Vec<Rc<Parts>>]) -> Vec<Vec<String>> {
        let row = |d: &Rc<Parts>| d.cons.iter().map(|c| format!("{c:?}")).collect::<String>();
        ors.iter().map(|ds| ds.iter().map(row).collect()).collect()
    }

    /// The orders of `0..n` (`n` a power of two) that the stages of a chain are given in.
    fn orders(n: usize) -> Vec<(&'static str, Vec<usize>)> {
        let bits = n.trailing_zeros();
        let mut random: Vec<usize> = (0..n).collect();
        let mut s = 0x9e37_79b9_7f4a_7c15_u64;
        for i in (1..n).rev() {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            random.swap(i, (s % (i as u64 + 1)) as usize);
        }
        vec![
            ("in order", (0..n).collect()),
            ("reversed", (0..n).rev().collect()),
            (
                "bit reversal",
                (0..n)
                    .map(|i| i.reverse_bits() >> (usize::BITS - bits))
                    .collect(),
            ),
            ("odd forward, even backward", {
                let odd = (0..n).filter(|i| i % 2 == 1);
                odd.chain((0..n).filter(|i| i % 2 == 0).rev()).collect()
            }),
            (
                "from both ends",
                (0..n)
                    .map(|i| if i % 2 == 0 { i / 2 } else { n - 1 - i / 2 })
                    .collect(),
            ),
            ("random", random),
        ]
    }

    /// `x[0] == 0` with, at each stage `i`, `x[i + 1] - x[i]` in {0, 10} and `x[i + 1]` in
    /// {0, 15}, the two disjunctions of stage `i` placed at `at[i]`: each value 15 and each step
    /// 10 has no point once the stage before is 0, so the removals run along the chain, and the
    /// order of the disjunctions is that of `at`, not of the chain. Before the disjunctions were
    /// put in the order of their structure ([`by_structure`]) the passes were 4 in the chain's
    /// order and 17 and 129 (`n + 1`) at 16 and 128 stages by bit reversal, 16.4 s at 128.
    #[test]
    fn a_chain_of_removals_takes_the_same_passes_in_any_order() {
        for n in [16, 128] {
            let mut first: Option<Vec<Vec<String>>> = None;
            for (name, at) in orders(n) {
                let mut slots: Vec<Vec<Vec<Rc<Parts>>>> = vec![Vec::new(); n];
                for i in 0..n {
                    slots[at[i]].push(any_of(&x(i + 1).minus(&x(i)), &[0, 10]));
                    slots[at[i]].push(any_of(&x(i + 1), &[0, 15]));
                }
                let mut ors: Vec<Vec<Rc<Parts>>> = slots.into_iter().flatten().collect();
                let rows = vec![Con::eq(&x(0), &Lin::default())];
                let passes = drop_jointly_empty(&rows, &mut ors).expect("a point");
                assert!(passes <= 4, "{name}, {n} stages: {passes} passes");
                assert!(ors.iter().all(|ds| ds.len() == 1), "{name}, {n} stages");
                let mut k = kept(&ors);
                k.sort();
                assert_eq!(
                    first.get_or_insert_with(|| k.clone()),
                    &k,
                    "{name}, {n} stages"
                );
            }
        }
    }

    fn a(i: usize, k: usize) -> Lin {
        Lin::atom(Atom::Sym(format!("a{i:03}_{k:02}").into()))
    }

    /// A hub `h` in `[0, r]` and `r` arms, each the chain above from `a[i][0]` to `a[i][4]`,
    /// with `(r - i + 1) a[i][0] <= 15 h` (the value 15 at the start of arm `i` needs
    /// `h > r - i`) and `h <= r - i - 1 + a[i][4]` (the end of arm `i` at 0 moves the hub to
    /// `r - i - 1`). Arm `i + 1` shares no atom with arm `i`: its removals follow arm `i`'s
    /// through the rows on `h` alone. The removals run out along each arm and back through the
    /// hub, so the passes grow with `r` (9, 17 and 31 at 4, 8 and 32 arms); every order still
    /// reaches the same disjuncts, every 15 and every 10 removed.
    #[test]
    fn removals_through_a_hub_keep_the_same_disjuncts_in_both_orders() {
        let h = Lin::atom(Atom::Sym("h".into()));
        let c = |v: i128| Lin::constant(v);
        let r = 8;
        let mut rows = vec![Con::ge(&h, &c(0)), Con::ge(&c(r as i128), &h)];
        let mut ors: Vec<Vec<Rc<Parts>>> = Vec::new();
        for i in 0..r {
            let ri = (r - i) as i128;
            rows.push(Con::ge(&h.times(15), &a(i, 0).times(ri + 1)));
            rows.push(Con::ge(&a(i, 4).plus(&c(ri - 1)), &h));
            ors.push(any_of(&a(i, 0), &[0, 15]));
            for k in 0..4 {
                ors.push(any_of(&a(i, k + 1).minus(&a(i, k)), &[0, 10]));
                ors.push(any_of(&a(i, k + 1), &[0, 15]));
            }
        }
        let mut back: Vec<Vec<Rc<Parts>>> = ors.iter().rev().cloned().collect();
        assert!(drop_jointly_empty(&rows, &mut ors).is_some());
        assert!(drop_jointly_empty(&rows, &mut back).is_some());
        assert!(ors.iter().all(|ds| ds.len() == 1));
        back.reverse();
        assert_eq!(kept(&ors), kept(&back));
    }
}

// Propagation over forced parts (module `forced`, PRES-small-cost) against the whole solver.
#[cfg(test)]
mod forced_against_solver {
    use std::collections::BTreeSet;
    use std::sync::Arc;

    use super::forced::{Forced, forced};
    use super::*;

    fn sym(x: &str) -> Lin {
        Lin::atom(Atom::Sym(Arc::from(x)))
    }

    fn q(i: u32) -> Lin {
        Lin::atom(Atom::Aux(i))
    }

    fn k(v: i64) -> Lin {
        Lin::constant(v)
    }

    fn ge(a: &Lin, b: &Lin) -> Formula {
        Formula::Con(Con::ge(a, b))
    }

    fn eq(a: &Lin, b: &Lin) -> Formula {
        Formula::Con(Con::eq(a, b))
    }

    /// What the whole solver says of `f`: the point it finds, or `None` when it finds none, and
    /// whether `f` holds somewhere; `None` when it refuses.
    fn slow(f: &Formula) -> Option<(Option<Model>, bool)> {
        let m = or_old(|| satisfiable_named(f)).ok()?;
        let d = or_old(|| decide_named(f)).ok()?;
        Some((m, d))
    }

    /// Whether `p` is a point of `f`, as the solver reads `f`; `None` when it refuses.
    fn is_point(f: &Formula, p: &Model) -> Option<bool> {
        let at = (p.iter()).map(|(a, v)| eq(&Lin::atom(a.clone()), &Lin::constant(v.clone())));
        let fixed = Formula::and(std::iter::once(f.clone()).chain(at).collect());
        slow(&fixed).map(|(_, d)| d)
    }

    /// Whether `f` holds at `p`, which gives each atom of `f` a value, each atom read as a
    /// variable of its own, a product included, as the solver reads it. Each shared part is
    /// evaluated once (`seen`, by its id).
    fn holds_at(f: &Formula, p: &Model, seen: &mut HashMap<formula::Id, bool>) -> bool {
        let id = formula::Id::of(f);
        if let Some(v) = id.and_then(|id| seen.get(&id)) {
            return *v;
        }
        let v = match f {
            Formula::Con(c) => {
                let mut v = c.lin.constant.clone();
                for (a, k) in &c.lin.terms {
                    v = &v + &(k * &p[a]);
                }
                if c.rel == Rel::Eq {
                    v.is_zero()
                } else {
                    !v.is_negative()
                }
            }
            Formula::Not(g) => !holds_at(g, p, seen),
            Formula::And(gs) => gs.iter().all(|g| holds_at(g, p, seen)),
            Formula::Or(gs) => gs.iter().any(|g| holds_at(g, p, seen)),
        };
        if let Some(id) = id {
            seen.insert(id, v);
        }
        v
    }

    /// Checks [`forced`] of `f` against the whole solver, with and without its point; gives
    /// which answer it gave (0 empty, 1 point, 3 undecided, 4 refused by the solver, 5 empty
    /// where the solver gives a point that is none, 6 a point at the bounds other than the
    /// solver's, 7 a point at the bounds where the solver refuses; 2, a formula that holds with
    /// some atom free, is answered with its point since PRES-small-point and counted as 1 or
    /// 6; 8 refused by the solver as written, answered with the facts). A point at the bounds
    /// ([`forced`]'s trial when propagation leaves `f` undecided) is checked by evaluating `f`
    /// at it. An undecided formula goes to the solver with the atoms propagation fixed replaced
    /// by their values ([`forced::Facts`]): [`satisfiable`] and [`decide`] then give the answers
    /// the solver gives on `f` as written, or an answer where it refuses `f`, and each point is
    /// checked by evaluation.
    fn agrees(f: &Formula) -> usize {
        let Some((m, d)) = slow(f) else {
            if let Forced::Point(p) = forced(f, true) {
                assert_eq!(p.keys().cloned().collect::<BTreeSet<_>>(), f.atoms(), "{f}");
                assert!(
                    holds_at(f, &p, &mut HashMap::new()),
                    "{p:?} is no point of {f}"
                );
                assert!(matches!(forced(f, false), Forced::Holds), "{f}");
                eprintln!("refused by the solver, a point at the bounds {p:?}: {f}");
                return 7;
            }
            // The solver may answer with the atoms propagation fixed replaced by their values
            // what it refuses as written: the answer is checked, the point by evaluation.
            match (decide(f), satisfiable(f)) {
                (Err(_), Err(_)) => {
                    eprintln!("refused: {f}");
                    return 4;
                }
                (Ok(d), Ok(m)) => {
                    assert_eq!(
                        m.is_some(),
                        d,
                        "satisfiable and decide of {f}, with the facts"
                    );
                    if let Some(mut p) = m {
                        for a in f.atoms() {
                            p.entry(a).or_insert(Int::ZERO);
                        }
                        assert!(
                            holds_at(f, &p, &mut HashMap::new()),
                            "{p:?} is no point of {f}"
                        );
                    }
                    eprintln!("refused as written, answered with the facts: {f}");
                    return 8;
                }
                (d, m) => panic!("{f}: with the facts decide {d:?}, satisfiable {m:?}"),
            }
        };
        assert_eq!(m.is_some(), d, "satisfiable and decide of {f}");
        let class = match forced(f, true) {
            Forced::Empty => match &m {
                // The solver's answer is wrong when the point it gives is none of `f`, as it was
                // with `x` and the product `x * y` both fixed beside a row of parity over a value
                // a disjunction defines until PRES-product-parity ([`bounds_agree_with_the_solver`]):
                // counted apart.
                Some(s) if is_point(f, s) != Some(true) => {
                    eprintln!(
                        "the solver's point of {f} is none of it ({:?}): {s:?}",
                        is_point(f, s)
                    );
                    assert!(matches!(forced(f, false), Forced::Empty), "{f}");
                    return 5;
                }
                _ => {
                    assert_eq!(m, None, "{f} has a point, but propagation found none");
                    0
                }
            },
            Forced::Point(p) => {
                // A point propagation forces is the solver's, which may leave out some atoms;
                // a point at the bounds, or one with an atom the formula does not read, may be
                // another.
                let s = m.expect("a point");
                assert_eq!(p.keys().cloned().collect::<BTreeSet<_>>(), f.atoms(), "{f}");
                assert!(
                    holds_at(f, &p, &mut HashMap::new()),
                    "{p:?} is no point of {f}"
                );
                if s.iter().all(|(a, v)| p.get(a) == Some(v)) {
                    1
                } else {
                    6
                }
            }
            Forced::Holds => panic!("{f}: a point asked for, none built"),
            Forced::Undecided(_) => {
                assert_eq!(
                    decide(f).ok(),
                    Some(d),
                    "{f}: decided otherwise with the facts"
                );
                let fast =
                    satisfiable(f).unwrap_or_else(|r| panic!("{f}: refused with the facts: {r}"));
                assert_eq!(fast.is_some(), d, "{f}: placed otherwise with the facts");
                if let Some(p) = &fast {
                    assert_eq!(is_point(f, p), Some(true), "{p:?} is no point of {f}");
                }
                3
            }
        };
        match (forced(f, false), class) {
            (Forced::Point(_), _) => panic!("a point built for {f}, though not asked"),
            (Forced::Empty, 0) | (Forced::Holds, 1 | 6) | (Forced::Undecided(_), 3) => class,
            (got, _) => panic!(
                "{f}: with the point {class}, without it {}",
                match got {
                    Forced::Empty => "empty",
                    Forced::Holds => "holds",
                    _ => "undecided",
                }
            ),
        }
    }

    /// A pseudo-random number generator (xorshift64), so the cases are the same on each run.
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: u64) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0 % n
        }

        fn small(&mut self) -> i64 {
            self.below(7) as i64 - 3
        }
    }

    /// A formula of the shape the preimage of a chain of `if` at a point gives: definitions
    /// `(g && c * q_i == e1) || (!g && q_i == e2)`, each guard `g` over the inputs or an earlier
    /// definition and held in both disjuncts (a shared part), with the inputs fixed or left
    /// free, sometimes fixed twice to different values, and terms with the product `x * y`.
    /// With `bounded`, the inputs are bounded by rows instead ([`input_bounds`]).
    fn chain(rng: &mut Rng, bounded: bool) -> Formula {
        let p = Lin::atom(Atom::product(&Arc::from("x"), &Arc::from("y")));
        let mut fs = Vec::new();
        let defs = 1 + rng.below(4) as u32;
        for i in 0..defs {
            let over = |rng: &mut Rng| match rng.below(4) {
                0 => sym("x"),
                1 => sym("y"),
                2 if i > 0 => q(rng.below(u64::from(i)) as u32),
                _ => p.clone(),
            };
            let g = ge(&over(rng), &k(rng.small()));
            let c = 1 + rng.below(2) as i64;
            let e1 = over(rng).plus(&k(rng.small()));
            let e2 = k(rng.small());
            fs.push(Formula::or(vec![
                Formula::and(vec![g.clone(), eq(&q(i).times(c), &e1)]),
                Formula::and(vec![Formula::negate(g), eq(&q(i), &e2)]),
            ]));
        }
        if bounded {
            input_bounds(rng, &p, &mut fs);
            return Formula::and(fs);
        }
        for x in ["x", "y"] {
            match rng.below(5) {
                0 => {}
                1 => fs.push(eq(&sym(x).times(2), &k(rng.small()))),
                _ => fs.push(eq(&sym(x), &k(rng.small()))),
            }
        }
        if rng.below(6) == 0 {
            fs.push(eq(&sym("x"), &k(rng.small())));
        }
        Formula::and(fs)
    }

    /// Rows bounding the inputs `x` and `y` and the product `p`, pushed to `fs`: for each input,
    /// none, one row on either side, an equation, or two rows `cx >= v && v + d·c >= cx` with
    /// `d` of -1, 0 or 1, whose bounds cross, meet or leave two values; the coefficient `c` is
    /// 1, 2 or 3, so a bound may need rounding. Then `p` fixed by two rows, or one row over `p`,
    /// over both inputs, or over their difference.
    fn input_bounds(rng: &mut Rng, p: &Lin, fs: &mut Vec<Formula>) {
        for x in ["x", "y"] {
            let c = 1 + rng.below(3) as i64;
            let cx = sym(x).times(c);
            let lo = rng.small();
            match rng.below(8) {
                0 => {}
                1 => fs.push(ge(&cx, &k(lo))),
                2 => fs.push(ge(&k(lo), &cx)),
                3 => fs.push(eq(&sym(x), &k(lo))),
                _ => {
                    let hi = lo + c * (rng.below(3) as i64 - 1);
                    fs.push(ge(&cx, &k(lo)));
                    fs.push(ge(&k(hi), &cx));
                }
            }
        }
        let v = rng.small();
        match rng.below(8) {
            0 => fs.push(ge(p, &k(v))),
            1 => fs.push(ge(&sym("x").plus(&sym("y")), &k(v))),
            2 => fs.push(ge(&k(v), &sym("x").minus(&sym("y")))),
            3 => {}
            _ => {
                fs.push(ge(p, &k(v)));
                fs.push(ge(&k(v), p));
            }
        }
    }

    #[test]
    fn propagation_agrees_with_the_solver_on_chains_of_definitions() {
        let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
        let mut seen = [0usize; 9];
        for _ in 0..3000 {
            seen[agrees(&chain(&mut rng, false))] += 1;
        }
        // Each answer occurs often enough to be tested; class 2 no longer occurs, since a
        // formula true before the trial now gives its point (class 1).
        assert!([0, 1, 3].iter().all(|&c| seen[c] >= 50), "answers {seen:?}");
    }

    #[test]
    fn propagation_agrees_with_the_solver_on_bounded_inputs() {
        let mut rng = Rng(0x2545_f491_4f6c_dd1d);
        let mut seen = [0usize; 9];
        for _ in 0..3000 {
            seen[agrees(&chain(&mut rng, true))] += 1;
        }
        eprintln!("answers {seen:?}");
        // Each answer that bounds give occurs often enough to be tested; a formula that holds
        // with a variable free is rare here (the inputs are mostly bounded), and the chains of
        // the test above give it often. A point at the bounds other than the solver's (6) is
        // common (PRES-small-point).
        assert!(
            [0, 1, 3, 6].iter().all(|&i| seen[i] >= 50),
            "answers {seen:?}"
        );
    }

    #[test]
    fn corner_cases_agree_with_the_solver() {
        let p = Lin::atom(Atom::product(&Arc::from("x"), &Arc::from("y")));
        let g = ge(&sym("x"), &k(1));
        let cases = [
            // true and false.
            (Formula::top(), 1),
            (Formula::bottom(), 0),
            // A non-integer value: `2 q0 == 3`.
            (
                Formula::and(vec![eq(&q(0).times(2), &k(3)), eq(&sym("x"), &k(1))]),
                0,
            ),
            (
                Formula::and(vec![eq(&q(0).times(2), &sym("x")), eq(&sym("x"), &k(3))]),
                0,
            ),
            // A product is an atom of its own: an equation fixes it, not its factors.
            (Formula::and(vec![eq(&p, &k(6)), eq(&sym("x"), &k(2))]), 1),
            // and its factors' values do not give it one: the solver reads it as free. Its bound
            // does, at which propagation tries it (PRES-small-point).
            (
                Formula::and(vec![
                    ge(&p, &k(6)),
                    eq(&sym("x"), &k(2)),
                    eq(&sym("y"), &k(3)),
                ]),
                1,
            ),
            // A row with two unknowns, the product and `z`, bounds neither.
            (
                Formula::and(vec![
                    ge(&p.plus(&sym("z")), &k(6)),
                    eq(&sym("x"), &k(2)),
                    eq(&sym("y"), &k(3)),
                ]),
                3,
            ),
            // A shared guard, read in both disjuncts.
            (
                Formula::and(vec![
                    Formula::or(vec![
                        Formula::and(vec![g.clone(), eq(&sym("x"), &q(0))]),
                        Formula::and(vec![Formula::negate(g.clone()), eq(&q(0), &k(1))]),
                    ]),
                    eq(&sym("x"), &k(0)),
                ]),
                1,
            ),
            // A negation is not forced into its operand: `!(x >= 1 && y == 2)` fixes nothing.
            (
                Formula::and(vec![
                    Formula::negate(Formula::and(vec![g.clone(), eq(&sym("y"), &k(2))])),
                    eq(&sym("x"), &k(3)),
                ]),
                3,
            ),
            // True at the values given, with `z` free: its point, `z` zero, which the solver gives
            // too (PRES-small-point; before, the solver was asked for the point).
            (
                Formula::and(vec![
                    eq(&sym("x"), &k(1)),
                    Formula::or(vec![g.clone(), eq(&sym("z"), &k(5))]),
                ]),
                1,
            ),
            // Two values for one variable.
            (
                Formula::and(vec![eq(&sym("x"), &k(1)), eq(&sym("x").times(2), &k(4))]),
                0,
            ),
            // A disjunction with two live operands fixes nothing.
            (
                Formula::and(vec![
                    Formula::or(vec![eq(&sym("x"), &k(1)), eq(&sym("x"), &k(2))]),
                    ge(&sym("y"), &k(0)),
                ]),
                3,
            ),
        ];
        for (f, want) in cases {
            assert_eq!(agrees(&f), want, "{f}");
        }
    }

    #[test]
    fn bounds_agree_with_the_solver() {
        let p = Lin::atom(Atom::product(&Arc::from("x"), &Arc::from("y")));
        let x = sym("x");
        let y = eq(&sym("y"), &k(0));
        let and = |fs: Vec<Formula>| Formula::and(fs.into_iter().chain([y.clone()]).collect());
        let cases = [
            // Bounds that meet fix `x`; that cross leave no point.
            (and(vec![ge(&x, &k(6)), ge(&k(6), &x)]), 1),
            (and(vec![ge(&x, &k(7)), ge(&k(6), &x)]), 0),
            // `2x >= 5` is `x >= 3`, and `2x <= 5` is `x <= 2`; with a negative constant,
            // `2x >= -5` is `x >= -2` and `2x <= -5` is `x <= -3`.
            (and(vec![ge(&x.times(2), &k(5)), ge(&k(3), &x)]), 1),
            (and(vec![ge(&x.times(2), &k(5)), ge(&k(2), &x)]), 0),
            (and(vec![ge(&k(5), &x.times(2)), ge(&x, &k(2))]), 1),
            (and(vec![ge(&x.times(2), &k(-5)), ge(&k(-2), &x)]), 1),
            (and(vec![ge(&x.times(2), &k(-5)), ge(&k(-3), &x)]), 0),
            (and(vec![ge(&k(-5), &x.times(2)), ge(&x, &k(-3))]), 1),
            (and(vec![ge(&k(-5), &x.times(2)), ge(&x, &k(-2))]), 0),
            // A row over a known and an unknown variable: `x + y >= 4` with `y == 0`.
            (and(vec![ge(&x.plus(&sym("y")), &k(4)), ge(&k(4), &x)]), 1),
            // A bound on one side only, or two that leave two values, fix nothing; the formula
            // holds with `x` at its (lower) bound, which propagation then tries
            // (PRES-small-point).
            (and(vec![ge(&x, &k(6))]), 1),
            (and(vec![ge(&x, &k(6)), ge(&k(7), &x)]), 1),
            // Rows not forced bound nothing: in `(x >= 6 || x == 0) && 6 >= x`, `x >= 6` is not
            // forced, so `x` has the one bound 6, where the formula holds.
            (
                and(vec![
                    Formula::or(vec![ge(&x, &k(6)), eq(&x, &k(0))]),
                    ge(&k(6), &x),
                ]),
                1,
            ),
            // At the bounds `x >= 7` is false, which forces `z == 1`: the point `x == 6, z == 1`,
            // not the solver's.
            (
                and(vec![
                    ge(&x, &k(6)),
                    ge(&k(7), &x),
                    Formula::or(vec![ge(&x, &k(7)), eq(&sym("z"), &k(1))]),
                ]),
                6,
            ),
            // At the bounds the formula is false, though it has a point (`x == 7`): no answer,
            // and the solver decides.
            (
                and(vec![
                    ge(&x, &k(6)),
                    ge(&k(7), &x),
                    Formula::or(vec![eq(&x, &k(7)), eq(&x, &k(8))]),
                ]),
                3,
            ),
            // `z` is bounded only after the first round: `x == 6` makes `x >= 7` false, which
            // forces `z >= 1`, and the second round sets `z == 1`, where the formula holds.
            (
                and(vec![
                    ge(&x, &k(6)),
                    ge(&k(7), &x),
                    Formula::or(vec![ge(&x, &k(7)), ge(&sym("z"), &k(1))]),
                ]),
                1,
            ),
            // The same, and then the second round sets `z == 1`, which makes `z >= 2` false and
            // forces `w >= 1`, while `z + w <= 1` gives `w <= 0`: a contradiction in the second
            // round, though the formula has a point (`x == 7, z == 0, w == 1`), which the solver
            // finds. `w` is never bounded alone, so no round sets it.
            (
                and(vec![
                    ge(&x, &k(6)),
                    ge(&k(7), &x),
                    Formula::or(vec![ge(&x, &k(7)), ge(&sym("z"), &k(1))]),
                    Formula::or(vec![ge(&sym("z"), &k(2)), ge(&sym("w"), &k(1))]),
                    ge(&k(1), &sym("z").plus(&sym("w"))),
                ]),
                3,
            ),
            // At the bounds `x == 6` contradicts `q0 == x + 1` and `q0 <= 6`; the formula has no
            // point, which the solver finds.
            (
                and(vec![
                    ge(&x, &k(6)),
                    eq(&q(0), &x.plus(&k(1))),
                    ge(&k(6), &q(0)),
                ]),
                3,
            ),
            // `x == 0 && x * y == 3` takes the first disjunct, so `q0 == 2`, which is not odd:
            // no point. The solver gave one that is none, `q0 == 1` from the second disjunct,
            // until its search read the product as a variable of its own (PRES-product-parity).
            (
                Formula::and(vec![
                    Formula::or(vec![
                        Formula::and(vec![ge(&p, &k(3)), eq(&x, &q(0).minus(&k(2)))]),
                        Formula::and(vec![Formula::negate(ge(&p, &k(3))), eq(&q(0), &k(1))]),
                    ]),
                    eq(&x, &k(0)),
                    eq(&p, &k(3)),
                    eq(&q(0), &q(3).times(2).plus(&k(1))),
                ]),
                0,
            ),
        ];
        for (f, want) in cases {
            assert_eq!(agrees(&f), want, "{f}");
        }
        // The two cases above with `z` bounded after the first round are decided in the second.
        let later = || {
            vec![
                ge(&x, &k(6)),
                ge(&k(7), &x),
                Formula::or(vec![ge(&x, &k(7)), ge(&sym("z"), &k(1))]),
            ]
        };
        assert_eq!(forced::rounds(&and(later())), Some((Some(true), 2)));
        let mut fs = later();
        fs.push(Formula::or(vec![
            ge(&sym("z"), &k(2)),
            ge(&sym("w"), &k(1)),
        ]));
        fs.push(ge(&k(1), &sym("z").plus(&sym("w"))));
        assert_eq!(forced::rounds(&and(fs)), Some((Some(false), 2)));
    }

    /// `f` with each atom renamed by `name` and the operands of each conjunction and
    /// disjunction in an order drawn from `rng` (a shared part is rewritten at each place).
    fn rewritten(f: &Formula, name: &dyn Fn(&Atom) -> Atom, rng: &mut Rng) -> Formula {
        fn each(gs: &[Formula], name: &dyn Fn(&Atom) -> Atom, rng: &mut Rng) -> Vec<Formula> {
            let mut gs: Vec<Formula> = gs.iter().map(|g| rewritten(g, name, rng)).collect();
            for i in (1..gs.len()).rev() {
                gs.swap(i, rng.below(i as u64 + 1) as usize);
            }
            gs
        }
        match f {
            Formula::Con(c) => {
                let lin = (c.lin.terms.iter())
                    .fold(Lin::constant(c.lin.constant.clone()), |l, (a, k)| {
                        l.plus(&Lin::atom(name(a)).times(k.clone()))
                    });
                Formula::Con(match c.rel {
                    Rel::Eq => Con::eq(&lin, &k(0)),
                    Rel::Ge => Con::ge(&lin, &k(0)),
                })
            }
            Formula::Not(g) => Formula::negate(rewritten(g, name, rng)),
            Formula::And(gs) => Formula::and(each(gs, name, rng)),
            Formula::Or(gs) => Formula::or(each(gs, name, rng)),
        }
    }

    /// What [`forced`] gave, each atom of its point, or of what it proved for the solver,
    /// named by `name`.
    fn shown(f: Forced, name: &dyn Fn(&Atom) -> Atom) -> String {
        let named = |p: Model| p.into_iter().map(|(a, v)| (name(&a), v)).collect::<Model>();
        match f {
            Forced::Empty => "empty".into(),
            Forced::Holds => "holds".into(),
            Forced::Point(p) => format!("{:?}", named(p)),
            Forced::Undecided(facts) => format!("undecided, {:?}", named(facts.fixed())),
        }
    }

    /// `x` and `y` swapped, and each auxiliary variable `qi` named `q(9 - i)`, which reverses
    /// their order.
    fn swapped(a: &Atom) -> Atom {
        match a {
            Atom::Sym(s) => Atom::Sym(Arc::from(if &**s == "x" { "y" } else { "x" })),
            Atom::Aux(i) => Atom::Aux(9 - i),
            // `x * y`, which the swap keeps.
            Atom::Product(..) => a.clone(),
        }
    }

    /// Checks that `f` and three rewritings of it ([`rewritten`] by [`swapped`], each
    /// conjunction and disjunction in an order drawn from `order`) are answered alike:
    /// propagation and its rounds at the bounds give the same answer, the same point renamed,
    /// and the same atoms fixed for the solver renamed; [`decide`] and [`satisfiable`], the
    /// solver given those atoms, give the same answer or the same kind of refusal (a refusal
    /// names the variables it ties, renamed here). Gives what `f` gave without its point.
    fn alike_rewritten(f: &Formula, order: &mut Rng) -> String {
        let same = |a: &Atom| a.clone();
        let want = [
            shown(forced(f, false), &swapped),
            shown(forced(f, true), &swapped),
        ];
        let kind = |r: Refusal| std::mem::discriminant(&r);
        for _ in 0..3 {
            let g = rewritten(f, &swapped, order);
            let got = [
                shown(forced(&g, false), &same),
                shown(forced(&g, true), &same),
            ];
            assert_eq!(got, want, "{f}\n  rewritten {g}");
            assert_eq!(
                decide(&g).map_err(kind),
                decide(f).map_err(kind),
                "{f}\n  rewritten {g}"
            );
            assert_eq!(
                satisfiable(&g).map(|m| m.is_some()).map_err(kind),
                satisfiable(f).map(|m| m.is_some()).map_err(kind),
                "{f}\n  rewritten {g}"
            );
        }
        want[0].clone()
    }

    #[test]
    fn the_point_at_the_bounds_does_not_depend_on_names_or_order() {
        // Propagation, and the point it tries at the bounds when it leaves the formula
        // undecided, give the same answer, and the same point renamed.
        let mut rng = Rng(0x6a09_e667_f3bc_c909);
        let mut order = Rng(0xbb67_ae85_84ca_a73b);
        let mut at_bounds = 0;
        for case in 0..4000 {
            let f = chain(&mut rng, case % 2 == 0);
            if alike_rewritten(&f, &mut order) == "holds" && matches!(agrees(&f), 6 | 7) {
                at_bounds += 1;
            }
        }
        // The trial at the bounds answers often enough to be tested.
        assert!(at_bounds >= 50, "{at_bounds} answered at the bounds alone");
    }

    /// A ladder that the rounds at the bounds climb one step a round: `x` bounded, then each
    /// `qi` bounded by a disjunction `prev >= t || qi >= prev + d` (or `qi <= prev + d`), whose
    /// first operand is decided only once `prev`, the step before, has its value; some steps
    /// also bound `qi` on the other side from the start, which a later round may contradict;
    /// and at the end, sometimes, a disjunction over the last step and `y`.
    fn ladder(rng: &mut Rng) -> Formula {
        let x = sym("x");
        let lo = rng.small();
        let mut fs = vec![ge(&x, &k(lo))];
        if rng.below(2) == 0 {
            fs.push(ge(&k(lo + rng.below(3) as i64), &x));
        }
        let (mut prev, mut at) = (x, lo);
        for i in 0..1 + rng.below(8) as u32 {
            // `prev >= t` false at `prev`'s value `at`, mostly, so the second operand is forced.
            let t = at + rng.below(4) as i64;
            let d = rng.small();
            let step = if rng.below(3) == 0 {
                ge(&prev.plus(&k(d)), &q(i))
            } else {
                ge(&q(i), &prev.plus(&k(d)))
            };
            fs.push(Formula::or(vec![ge(&prev, &k(t)), step]));
            if rng.below(4) == 0 {
                fs.push(ge(&k(at + d + rng.small()), &q(i)));
            }
            (prev, at) = (q(i), at + d);
        }
        if rng.below(2) == 0 {
            let m = at + rng.small();
            fs.push(Formula::or(vec![
                ge(&k(m), &prev),
                eq(&sym("y"), &k(rng.small())),
            ]));
        }
        Formula::and(fs)
    }

    #[test]
    fn rounds_at_the_bounds_do_not_depend_on_names_or_order() {
        // Ladders that need several rounds, some ending in a contradiction in a later round:
        // each is answered alike whatever the names and order, and agrees with the solver.
        let mut rng = Rng(0x3c6e_f372_fe94_f82b);
        let mut order = Rng(0xa54f_f53a_5f1d_36f1);
        let (mut several, mut later_empty, mut three) = (0, 0, 0);
        for _ in 0..3000 {
            let f = ladder(&mut rng);
            alike_rewritten(&f, &mut order);
            agrees(&f);
            match forced::rounds(&f) {
                Some((Some(true), r)) if r >= 2 => several += 1,
                Some((Some(false), r)) if r >= 2 => later_empty += 1,
                _ => {}
            }
            if forced::rounds(&f).is_some_and(|(_, r)| r >= 3) {
                three += 1;
            }
        }
        assert!(
            several >= 50 && later_empty >= 50 && three >= 50,
            "{several} decided in round 2 or later, {later_empty} contradicted there, {three} \
             with three rounds or more"
        );
    }

    #[test]
    fn the_state_never_loosens() {
        // After each event of the propagation and of the rounds at the bounds, the state knows
        // at least what it knew before (`forced::trace::below`), on the census chains and the
        // ladders. A check of the proof at `Trial::holds`, which does not rest on it.
        // Complexity tradeoff: each state is copied whole after each event, O(e·n) for `e`
        // events and `n` parts and variables, so quadratic in the size of one formula. The
        // formulas here have at most a few dozen parts and do not grow. A record of each
        // change alone would cost O(e), but it would be taken inside the methods of module
        // `state` that the test checks from outside.
        let mut rng = Rng(0x510e_527f_ade6_82d1);
        let mut events = 0;
        for case in 0..3000 {
            let f = match case % 3 {
                0 => chain(&mut rng, false),
                1 => chain(&mut rng, true),
                _ => ladder(&mut rng),
            };
            let states = forced::trace::states(&f);
            events += states.len();
            for w in states.windows(2) {
                assert!(
                    forced::trace::below(&w[1], &w[0]),
                    "{f}: loosened from {:?} to {:?}",
                    w[0],
                    w[1]
                );
            }
        }
        assert!(events >= 10_000, "{events} events");
    }
}

#[cfg(test)]
// The tests of `Formula`'s kept hashes (deep.rs). They are here, not in deep.rs, because they
// build formulas with `Atom` and `nnf` from this file, which deep.rs may not import.
mod formula_hashes {
    use super::formula::Sig;
    use super::*;

    /// `x + c >= 0`.
    fn con(c: i64) -> Formula {
        let x = Lin::atom(Atom::Sym("x".into()));
        Formula::Con(Con::ge(&x.plus(&Lin::constant(c)), &Lin::default()))
    }

    fn and(fs: Vec<Formula>) -> Formula {
        Formula::And(Shared::new(fs))
    }

    fn or(fs: Vec<Formula>) -> Formula {
        Formula::Or(Shared::new(fs))
    }

    #[test]
    fn formulas_whose_hashes_collide_are_compared() {
        // One hash kept by hand for three conjunctions before any is hashed: two equal, one
        // not. Equal hashes decide nothing, so `cmp` still tells them apart.
        let sig = Sig {
            rank: 2,
            n: 7,
            seq: 7,
            pow: 7,
        };
        let (a, b, c) = (
            and(vec![con(0), con(1)]),
            and(vec![con(0), con(2)]),
            and(vec![con(0), con(1)]),
        );
        for f in [&a, &b, &c] {
            let Formula::And(gs) = f else { unreachable!() };
            assert!(Shared::keep_sig(gs, sig));
        }
        assert_eq!(a.sig(), b.sig());
        assert_ne!(a, b);
        assert_ne!(b, a);
        assert_eq!(a, c);
        assert_eq!(a.cmp(&b), b.cmp(&a).reverse());
        assert_ne!(a.cmp(&b), Ordering::Equal);
        // A hash found by the walk: unequal to the one kept by hand, and to the hash of `a`.
        // (`b == d` would be false, since the hash kept for `b` is not its own; `cmp`, which
        // reads no hash, still finds them equal.)
        let d = and(vec![con(0), con(2)]);
        assert_ne!(a.sig(), d.sig());
        assert_ne!(a, d);
        assert_eq!(b.cmp(&d), Ordering::Equal);
    }

    #[test]
    fn runs_in_other_orders_are_unequal_until_sorted_and_then_hash_alike() {
        // `x >= 0 && (x >= -1 || x >= -2)` and the same with each run in the other order:
        // unequal as written, since `Ord` reads parts in order, and equal with equal hashes
        // once `nnf` sorts each run.
        let a = and(vec![con(0), or(vec![con(1), con(2)])]);
        let b = and(vec![or(vec![con(2), con(1)]), con(0)]);
        assert_ne!(a, b);
        let (a, b) = (nnf(&a, true), nnf(&b, true));
        assert_eq!(a, b);
        assert_eq!(a.sig(), b.sig());
        assert_eq!(a.cmp(&b), Ordering::Equal);
    }

    #[test]
    fn a_hash_is_found_again_after_its_parts_change() {
        let mut f = and(vec![con(0), con(1)]);
        let before = f.sig();
        let Formula::And(gs) = &mut f else {
            unreachable!()
        };
        Shared::change(gs).expect("one holder").push(con(2));
        let fresh = and(vec![con(0), con(1), con(2)]);
        assert_ne!(f.sig(), before);
        assert_eq!(f.sig(), fresh.sig());
        assert_eq!(f, fresh);
    }

    #[test]
    fn parts_held_by_a_conjunction_and_a_disjunction_hash_as_each() {
        // One list of parts under two variants: one keeps its hash with the parts, the other's
        // is found in the call (`spill`), and both match the same formulas built apart.
        let gs = Shared::new(vec![con(0), con(1)]);
        let (a, o) = (Formula::And(gs.clone()), Formula::Or(gs));
        let top = and(vec![a.clone(), o.clone(), a.clone()]);
        let apart = |fs: [i64; 2]| fs.map(con).to_vec();
        let top_apart = and(vec![
            and(apart([0, 1])),
            or(apart([0, 1])),
            and(apart([0, 1])),
        ]);
        assert_eq!(top.sig(), top_apart.sig());
        assert_eq!(a.sig(), and(apart([0, 1])).sig());
        assert_eq!(o.sig(), or(apart([0, 1])).sig());
        assert_ne!(a, o);
        assert_eq!(top, top_apart);
    }
}
