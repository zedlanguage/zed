use super::super::meter::{SOLVER_STEP, TWO_PIN_READINGS};
use super::super::{SOLVER, Shared, member, project_each_exact};
use super::*;

mod bench;
mod columns;
mod push_down;

/// A pseudo-random number generator (xorshift64), seeded by [`crate::seed::seed`]: a new
/// seed on each run, printed, which `ZED_TEST_SEED` repeats.
struct Rng(u64);

impl Rng {
    fn below(&mut self, n: u64) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0 % n
    }

    fn int(&mut self, lo: i64, hi: i64) -> i64 {
        lo + self.below((hi - lo + 1) as u64) as i64
    }
}

/// Signing must simplify a raw duplicate node even when neither of its rows changes.
/// Previously one sign kept two rows and the other rebuilt the node as a single row.
#[test]
fn raw_repeated_equations_have_one_cover_input_in_both_signs() {
    use super::super::{Signs, canonical_parts, cover_input, signed};
    let chosen = signed(&eq(&[("x", 1), ("y", -2)], 0), Signs::Chosen);
    let flipped = match &chosen {
        Formula::Con(c) => Formula::Con(Con {
            lin: c.lin.times(-1),
            rel: Rel::Eq,
        }),
        _ => unreachable!(),
    };
    for conjunction in [false, true] {
        let raw = |c: &Formula| {
            let kids = super::super::Shared::new(vec![c.clone(), c.clone()]);
            if conjunction {
                Formula::And(kids)
            } else {
                Formula::Or(kids)
            }
        };
        let (f, g) = (raw(&chosen), raw(&flipped));
        // Keep the old expressions in the diagnostic: the negative control checks
        // actual nesting, which Formula's flattened comparison deliberately ignores.
        println!(
            "old cover inputs: {:?} / {:?}",
            canonical_parts(&signed(&f, Signs::Chosen)),
            canonical_parts(&signed(&g, Signs::Chosen))
        );
        let (left, right) = (cover_input(&f), cover_input(&g));
        assert_eq!(format!("{left:?}"), format!("{right:?}"));
        // The conjunction constructor removes duplicate rows; the disjunction
        // constructor retains them, and `canonical_parts` keeps a repeated part once
        // (`a || a` is `a`), equally for both equation signs.
        assert_eq!(constraints(&left), 1);
    }
}

/// Refused ordering is an explicit error, never a provisional color assignment.
#[test]
fn a_spent_ordering_returns_before_color_refinement() {
    let row = Con::ge(&lin(&[("x", 1)], 0), &Lin::constant(0));
    let mut work = Work {
        used: 0,
        limit: 0,
        solver: SOLVER,
    };
    let mut rejected = false;
    let got = work.metered(|| {
        rejected = super::super::canonical(vec![a("x")], &[&row]).is_err();
    });
    assert!(rejected);
    assert_eq!(got, Err(Refusal::Questions));
}

/// Three rows are admitted, but substituting y into the two bounds is additional work.
/// Stopping that shadow must refuse, never turn a stopped proof into an empty set.
#[test]
fn a_small_shadow_charges_its_generated_rows() {
    let rows: Vec<_> = [
        eq(&[("x", 1), ("y", -1)], 0),
        ge(&[("y", 1)], 0),
        ge(&[("y", -1)], 10),
    ]
    .into_iter()
    .map(|f| match &f {
        Formula::Con(c) => c.clone(),
        _ => unreachable!(),
    })
    .collect();
    let mut work = Work {
        used: 0,
        limit: rows.len() as u64 * SOLVER_UNIT,
        solver: SOLVER,
    };
    assert_eq!(
        projected(&rows, &a("x"), &mut work),
        Err(Refusal::Questions)
    );
    let mut work = Work {
        used: 0,
        limit: EXACT_LIMIT,
        solver: SOLVER,
    };
    assert_eq!(
        projected(&rows, &a("x"), &mut work),
        Ok(Some(IntervalSet::of(0, 10)))
    );
}

/// The questions of `rays` charge the solver's work on them, not only their fixed reads
/// (PRES-rays-unmetered): `x >= y >= 0` has one ray, up from 0, and the charge is more than
/// the reads; with a limit of the reads alone, `rays` is refused, where before this row it
/// answered with the solver's work uncounted.
#[test]
fn the_questions_of_rays_charge_the_solvers_work() {
    let rows: Vec<Con> = [
        ge(&[("x", 3), ("y", -2)], 0),
        ge(&[("y", 5), ("z", -7)], 1),
        ge(&[("z", 1)], 0),
        ge(&[("x", 2), ("z", -3)], 0),
    ]
    .into_iter()
    .map(|f| match &f {
        Formula::Con(c) => c.clone(),
        _ => unreachable!(),
    })
    .collect();
    let size = 1;
    let mut work = Work {
        used: 0,
        limit: EXACT_LIMIT,
        solver: SOLVER,
    };
    let got = projection::rays(&rows, &a("x"), size, &mut work).unwrap();
    assert_eq!(got.len(), 1, "{got:?}");
    assert_eq!((&got[0].lo, &got[0].hi), (&Some(Int::from(0)), &None));
    // The rows' terms with their constants; two sign questions, then one question for each
    // residue modulo the ray's step.
    let terms: u64 = rows.iter().map(|k| k.lin.terms.len() as u64 + 1).sum();
    let g = got[0].step.to_i128().unwrap() as u64;
    let reads = SOLVER_UNIT * (2 * (size + terms) + g * (size + terms + 2));
    assert!(work.used > reads, "used {} reads {reads}", work.used);
    let mut work = Work {
        used: 0,
        limit: reads,
        solver: SOLVER,
    };
    assert_eq!(
        projection::rays(&rows, &a("x"), size, &mut work),
        Err(Refusal::Questions)
    );
}

/// An insertion after refusal must not update the row index or contradiction flag.
/// Only the enclosing metered caller may interpret the incomplete solver state.
#[test]
fn a_spent_insertion_leaves_the_system_alone() {
    let mut sys = super::super::System::new([0].into_iter());
    let mut work = Work {
        used: 0,
        limit: 0,
        solver: SOLVER,
    };
    assert!(matches!(
        work.metered(|| sys.add(super::super::Row {
            a: vec![(0, Int::ONE)].into(),
            k: Int::ZERO,
        })),
        Err(Refusal::Questions)
    ));
    assert!(sys.rows.is_empty());
    assert!(sys.ids.is_empty());
    assert!(!sys.empty);
}

fn a(s: &str) -> Atom {
    Atom::Sym(s.into())
}

fn lin(terms: &[(&str, i64)], k: i64) -> Lin {
    Lin {
        terms: (terms.iter())
            .filter(|(_, c)| *c != 0)
            .map(|(s, c)| (a(s), Int::from(*c)))
            .collect(),
        constant: Int::from(k),
    }
}

fn ge(terms: &[(&str, i64)], k: i64) -> Formula {
    Formula::Con(Con::ge(&lin(terms, k), &Lin::constant(0)))
}

fn eq(terms: &[(&str, i64)], k: i64) -> Formula {
    Formula::Con(Con::eq(&lin(terms, k), &Lin::constant(0)))
}

const NAMES: [&str; 3] = ["x", "y", "z"];
const B: i64 = 4;

/// `f` with each of x, y and z in `-B..=B`.
fn boxed(f: Formula) -> Formula {
    let mut all: Vec<Formula> = (NAMES.iter())
        .map(|n| member(&a(n), &IntervalSet::of(-B, B)))
        .collect();
    all.push(f);
    Formula::and(all)
}

/// The values of `sym` at the points of `f` in the box, by trying every point.
fn brute(f: &Formula, sym: &str) -> IntervalSet {
    let at = NAMES.iter().position(|n| *n == sym).unwrap();
    let mut set = IntervalSet::empty();
    let r = -B..=B;
    for x in r.clone() {
        for y in r.clone() {
            for z in r.clone() {
                let p = [x, y, z];
                let m: Model = (NAMES.iter().zip(p))
                    .map(|(n, v)| (a(n), Int::from(v)))
                    .collect();
                if f.holds(&m) {
                    set = set.join(&IntervalSet::single(p[at]));
                }
            }
        }
    }
    set
}

/// A random constraint over one to three of x, y and z, coefficients from -3 to 3.
fn constraint(rng: &mut Rng) -> Formula {
    let terms: Vec<(&str, i64)> = NAMES.iter().map(|n| (*n, rng.int(-3, 3))).collect();
    let terms: Vec<(&str, i64)> = if terms.iter().all(|t| t.1 == 0) {
        vec![("x", 1)]
    } else {
        terms
    };
    let k = rng.int(-4, 4);
    if rng.below(3) == 0 {
        eq(&terms, k)
    } else {
        ge(&terms, k)
    }
}

fn formula(rng: &mut Rng, depth: u32) -> Formula {
    if depth == 0 || rng.below(4) == 0 {
        return constraint(rng);
    }
    let n = 2 + rng.below(2) as usize;
    let parts: Vec<Formula> = (0..n).map(|_| formula(rng, depth - 1)).collect();
    match rng.below(5) {
        0 => Formula::negate(Formula::and(parts)),
        1 | 2 => Formula::and(parts),
        _ => Formula::or(parts),
    }
}

/// The projections of random formulas over x, y and z in a box, with strides
/// (coefficients from -3 to 3, equations) and nested disjunctions and negations, are the
/// sets of values that trying each of the 729 points gives: never wider, never narrower.
/// The solver alone (`EXACT_OFF`) gives wider sets on some of them; a refusal is counted
/// and printed with its cause.
#[test]
fn random_formulas_project_to_the_values_of_their_points() {
    random_formulas_at(crate::seed::seed(
        "random_formulas_project_to_the_values_of_their_points",
    ));
}

/// [`random_formulas_project_to_the_values_of_their_points`] at seed 10413658062665981385,
/// which refused 4 answers, past the 3 allowed (FAIL-exact-refusals-10413658062665981385).
#[test]
fn random_formulas_at_seed_10413658062665981385() {
    random_formulas_at(10413658062665981385);
}

/// [`random_formulas_project_to_the_values_of_their_points`] at seed 3569362060062839708,
/// which refused 4 answers, past the 3 allowed (FAIL-exact-refusals-3569362060062839708).
#[test]
fn random_formulas_at_seed_3569362060062839708() {
    random_formulas_at(3569362060062839708);
}

/// [`random_formulas_project_to_the_values_of_their_points`] at seed 13733945893095969990,
/// which refused 4 answers, past the 3 allowed (PRES-presbench1-red).
#[test]
fn random_formulas_at_seed_13733945893095969990() {
    random_formulas_at(13733945893095969990);
}

/// [`random_formulas_project_to_the_values_of_their_points`] at seed 4164922340731529606,
/// which refused 5 answers, past the 3 allowed (FAIL-exact-refusals-4164922340).
#[test]
fn random_formulas_at_seed_4164922340731529606() {
    random_formulas_at(4164922340731529606);
}

/// A disjunct that the local repair showed to have no point with the constraints taken
/// ([`super::super::Repair::Empty`]) is passed over without the solve of its whole group, also
/// where the projection passed over one such disjunct before it (PRES-presbench1-red). Round 63
/// of seed 13733945893095969990 runs out of work inside a reading where the repair showed
/// disjuncts 0, 1 and 2 empty and the projection passed over 0; the cursor over the empty
/// disjuncts stayed on 0, so 1 and 2 were solved in full.
#[test]
fn disjuncts_shown_empty_are_never_solved_in_full() {
    let mut rng = Rng(13733945893095969990 | 1);
    let f = (0..=63)
        .map(|_| boxed(formula(&mut rng, 3)))
        .last()
        .unwrap();
    let syms: Vec<Atom> = NAMES.iter().map(|n| a(n)).collect();
    super::super::PICK_TRACE.with(|t| *t.borrow_mut() = Some(Vec::new()));
    let _ = project_each_exact(&f, &syms);
    let trace = super::super::PICK_TRACE
        .with(|t| t.borrow_mut().take())
        .unwrap_or_default();
    let (mut empty, mut emptied, mut solved) = (Vec::new(), 0, Vec::new());
    for (step, at, _) in &trace {
        match *step {
            "disjunction" => empty.clear(),
            "empty" => {
                empty.push(*at);
                emptied += 1;
            }
            "full" if empty.contains(at) => solved.push(*at),
            _ => {}
        }
    }
    assert!(emptied > 0, "no disjunct shown empty: {f}");
    assert_eq!(solved, Vec::<usize>::new());
}

fn random_formulas_at(seed: u64) {
    let mut rng = Rng(seed | 1);
    let syms: Vec<Atom> = NAMES.iter().map(|n| a(n)).collect();
    let (mut wrong, mut refused, mut wider_before) = (Vec::new(), Vec::new(), 0);
    for round in 0..300 {
        let f = boxed(formula(&mut rng, 3));
        let each = project_each_exact(&f, &syms);
        EXACT_OFF.set(true);
        let before = project_each_exact(&f, &syms);
        EXACT_OFF.set(false);
        for (k, n) in NAMES.iter().enumerate() {
            let want = brute(&f, n);
            if let Ok((b, _)) = &before
                && let Ok(b) = &b[k]
                && b != &want
            {
                wider_before += 1;
            }
            match each.as_ref().map(|e| &e.0[k]) {
                Ok(Ok(got)) if got == &want => {}
                Ok(Ok(got)) => wrong.push(format!("round {round} {n}: {got} not {want}: {f}")),
                Ok(Err(e)) | Err(e) => refused.push(format!("round {round} {n}: {e:?}: {f}")),
            }
        }
    }
    println!("seed {seed}: {wider_before} wider before, refused {refused:#?}");
    assert!(wrong.is_empty(), "seed {seed}: {wrong:#?}");
    assert!(refused.len() <= 3, "seed {seed}: {refused:#?}");
}

/// Conjunctions of random rows over one or two of x, y and z, so that their atoms often fall
/// into groups that share no atom, some groups with no point, project to the sets that trying
/// each point gives. `read_once` projects each group onto its own atoms alone
/// (PRES-cover-bench-disjoint-reduced) and empties every set where some group has no point.
#[test]
fn conjunctions_of_separate_groups_project_to_the_values_of_their_points() {
    let seed =
        crate::seed::seed("conjunctions_of_separate_groups_project_to_the_values_of_their_points");
    let mut rng = Rng(seed | 1);
    let syms: Vec<Atom> = NAMES.iter().map(|n| a(n)).collect();
    let (mut wrong, mut refused, mut rounds, mut empty) = (Vec::new(), Vec::new(), 0, 0);
    for round in 0..400 {
        let rows: Vec<Formula> = (0..2 + rng.below(4))
            .map(|_| {
                let i = rng.below(3) as usize;
                let j = rng.below(3) as usize;
                let mut terms = vec![(
                    NAMES[i],
                    rng.int(1, 3) * if rng.below(2) == 0 { 1 } else { -1 },
                )];
                if j != i && rng.below(2) == 0 {
                    terms.push((NAMES[j], rng.int(-3, 3)));
                }
                let k = rng.int(-6, 6);
                if rng.below(4) == 0 {
                    eq(&terms, k)
                } else {
                    ge(&terms, k)
                }
            })
            .collect();
        let f = boxed(Formula::and(rows));
        let wants: Vec<IntervalSet> = NAMES.iter().map(|n| brute(&f, n)).collect();
        empty += wants[0].is_empty() as usize;
        rounds += 1;
        match project_each_exact(&f, &syms) {
            Ok((got, _)) => {
                for (k, n) in NAMES.iter().enumerate() {
                    match &got[k] {
                        Ok(g) if g == &wants[k] => {}
                        Ok(g) => {
                            wrong.push(format!("round {round} {n}: {g} not {}: {f}", wants[k]))
                        }
                        Err(e) => refused.push(format!("round {round} {n}: {e:?}")),
                    }
                }
            }
            Err(e) => refused.push(format!("round {round}: {e:?}")),
        }
    }
    println!("seed {seed}: {rounds} conjunctions, {empty} with no point");
    assert!(
        empty > 0 && empty < rounds,
        "seed {seed}: both kinds must occur"
    );
    assert!(wrong.is_empty(), "seed {seed}: {wrong:#?}");
    assert!(refused.is_empty(), "seed {seed}: {refused:#?}");
}

/// The answers and refusals of a call do not depend on the order of its symbols, nor on a
/// symbol named twice: random formulas as above, at limits from a few questions' work to
/// the full one, each symbol answered alike for `[x, y, z]`, `[z, y, x]` and `[y, x, z, y]`.
/// Before the symbols were taken in one order (`exact_each`), a symbol covered after
/// another read the points that one's questions found, so its work, and a refusal past the
/// limit, depended on the order of the call.
#[test]
fn the_answers_do_not_depend_on_the_order_of_the_symbols() {
    let seed = crate::seed::seed("the_answers_do_not_depend_on_the_order_of_the_symbols");
    let mut rng = Rng(seed | 1);
    let orders: [&[&str]; 3] = [&["x", "y", "z"], &["z", "y", "x"], &["y", "x", "z", "y"]];
    let mut differ = Vec::new();
    for round in 0..120 {
        let f = boxed(formula(&mut rng, 3));
        for limit in [3_000, 10_000, 30_000, 100_000, EXACT_LIMIT] {
            EXACT_LIMIT_SET.set(Some(limit));
            let answers: Vec<_> = (orders.iter())
                .map(|o| {
                    let syms: Vec<Atom> = o.iter().map(|n| a(n)).collect();
                    let got = project_each_exact(&f, &syms);
                    let mut by: Vec<(&str, String)> = (o.iter().copied())
                        .zip(match &got {
                            Ok((each, _)) => each.iter().map(|r| format!("{r:?}")).collect(),
                            Err(e) => vec![format!("{e:?}"); o.len()],
                        })
                        .collect();
                    by.sort();
                    by.dedup();
                    (by, got.map(|g| g.1).unwrap_or_default())
                })
                .collect();
            EXACT_LIMIT_SET.set(None);
            if answers.iter().any(|a| a != &answers[0]) {
                differ.push(format!("round {round} limit {limit}: {answers:?}: {f}"));
            }
        }
    }
    assert!(differ.is_empty(), "seed {seed}: {differ:#?}");
}

/// The covers of a part's symbols give the same answers and refusals with what the symbols
/// before them learned (`PartCache`) as without it: random formulas as above, at limits from a
/// few questions' work to the full one, for `[x, y, z, w]` (`w` read by no constraint). Where
/// the call is refused as a whole, every symbol is refused for that cause without the cache.
/// None asks more questions or runs more fast work (`FAST_WORK`) with the cache, and some call
/// is refused as a whole. What the cache saves is measured on the formulas it is for
/// (`disjoint::bench::the_join_of_arms_on_many_disjoint_refused_groups_reduced_scales` in
/// `l01_39_scope_relations`): random formulas over four symbols seldom reach the steps it keeps.
#[test]
fn the_covers_answer_alike_with_and_without_what_the_symbols_before_learned() {
    let seed = crate::seed::seed(
        "the_covers_answer_alike_with_and_without_what_the_symbols_before_learned",
    );
    let mut rng = Rng(seed | 1);
    let syms: Vec<Atom> = ["x", "y", "z", "w"].iter().map(|n| a(n)).collect();
    let (mut differ, mut whole) = (Vec::new(), 0);
    let run = |f: &Formula, off: bool| {
        PART_CACHE_OFF.set(off);
        let (q, d) = (EXACT_QUESTIONS.get(), FAST_WORK.get());
        let got = project_each_exact(f, &syms);
        PART_CACHE_OFF.set(false);
        (got, EXACT_QUESTIONS.get() - q, FAST_WORK.get() - d)
    };
    for round in 0..120 {
        let f = boxed(formula(&mut rng, 3));
        for limit in [3_000, 10_000, 30_000, 100_000, EXACT_LIMIT] {
            EXACT_LIMIT_SET.set(Some(limit));
            let (on, q_on, d_on) = run(&f, false);
            let (off, q_off, d_off) = run(&f, true);
            EXACT_LIMIT_SET.set(None);
            let say = |what: String| format!("round {round} limit {limit}: {what}: {f}");
            match (&on, &off) {
                (Ok((a, _)), Ok((b, _))) if a != b => {
                    differ.push(say(format!("{a:?} with, {b:?} without")))
                }
                (Err(e), Ok((b, _))) => {
                    whole += 1;
                    if b.iter().any(|r| r.as_ref().err() != Some(e)) {
                        differ.push(say(format!("refused {e:?} with, {b:?} without")));
                    }
                }
                (Ok(_), Err(_)) | (Err(_), Err(_)) if format!("{on:?}") != format!("{off:?}") => {
                    differ.push(say(format!("{on:?} with, {off:?} without")))
                }
                _ => {}
            }
            if q_on > q_off || d_on > d_off {
                differ.push(say(format!(
                    "{q_on} questions, {d_on} fast work with; {q_off}, {d_off} without"
                )));
            }
        }
    }
    assert!(differ.is_empty(), "seed {seed}: {differ:#?}");
    assert!(whole > 0, "seed {seed}: no call was refused as a whole");
}

/// `(x == 1 && y == 0 || x == 3 && y == 1) && (x == 1 && y == 1 || x == 3 && y == 0)`, which
/// has no point, though the solver's meet of the unions of hulls keeps x in {1, 3}.
fn apart() -> Formula {
    let d = |p: i64, q: i64, r: i64, s: i64| {
        Formula::or(vec![
            Formula::and(vec![eq(&[("x", 1)], -p), eq(&[("y", 1)], -q)]),
            Formula::and(vec![eq(&[("x", 1)], -r), eq(&[("y", 1)], -s)]),
        ])
    };
    Formula::and(vec![d(1, 0, 3, 1), d(1, 1, 3, 0)])
}

/// `f` with x, y and z renamed u, v and w.
fn renamed(f: &Formula) -> Formula {
    let to = |s: &Atom| match s {
        Atom::Sym(n) if &**n == "x" => a("u"),
        Atom::Sym(n) if &**n == "y" => a("v"),
        Atom::Sym(n) if &**n == "z" => a("w"),
        _ => s.clone(),
    };
    let each = |gs: &[Formula]| gs.iter().map(renamed).collect::<Vec<_>>();
    match f {
        Formula::Con(c) => Formula::Con(Con {
            lin: Lin {
                terms: c
                    .lin
                    .terms
                    .iter()
                    .map(|(s, k)| (to(s), k.clone()))
                    .collect(),
                constant: c.lin.constant.clone(),
            },
            rel: c.rel,
        }),
        Formula::Not(g) => Formula::Not(Shared::new(renamed(g))),
        Formula::And(gs) => Formula::And(Shared::new(each(gs))),
        Formula::Or(gs) => Formula::Or(Shared::new(each(gs))),
    }
}

/// The answers for a part that `split` cuts from the formula, where [`direct`] answers it
/// (PRES-cover-refusals-moduli, the comment at `cover`): random `f = p ∧ q`, `p` over x, y and
/// z and `q` over u, v and w, each in a box, on fixed seeds; on every other round `q` is
/// [`apart`], which has no point. `direct` reads `p` alone, so its answer for x is the
/// projection of `p`, which has values with no point of `f` where `q` has none, and may lie
/// outside the solver's set `h` there, which then need not hold it; `exact_each` makes every
/// answer empty where a part has no point (`has_points`).
///
/// First, as the solver gives `h`: each answer must equal the values the points of `f` give
/// (every point of `p` and of `q` tried), lie within `h`, and equal the answer of the cover
/// with `direct` off (`DIRECT_OFF`) wherever both answer. The solver alone finds that `f` has
/// no point wherever `q` has none (none of 388 empty random formulas of depth 4 had a value
/// in its sets, 2026-11-18), so `exact_each` returns at its first step there, and the case
/// above is not reached by this path. Second, so that it is: where `q` has no point,
/// `exact_each` is given sets that miss that, `{0}` for x, y and z and the box for u, v and w
/// (sound, as `f` has no value at all), and must answer every symbol empty, with `direct` on
/// and off; the rounds where the projection of `p` onto x leaves `{0}`, so that `direct`'s
/// answer is not within `h`, are counted and must occur.
#[test]
fn a_part_split_off_gets_the_same_answer_with_and_without_direct() {
    let names = ["x", "y", "z", "u", "v", "w"];
    let syms: Vec<Atom> = names.iter().map(|n| a(n)).collect();
    let (mut wrong, mut refused, mut outside) = (Vec::new(), 0, 0);
    for seed in [1u64, 126, 4_242, 99_991] {
        let mut rng = Rng(seed);
        for round in 0..20 {
            let p = boxed(formula(&mut rng, 3));
            let q = boxed(if round % 2 == 0 {
                apart()
            } else {
                formula(&mut rng, 3)
            });
            let f = Formula::and(vec![p.clone(), renamed(&q)]);
            let q_empty = brute(&q, "x").is_empty();
            let both = !q_empty && !brute(&p, "x").is_empty();
            let at = |r: &Result<Each, Refusal>, k: usize| match r {
                Ok((e, _)) => e[k].clone().ok(),
                Err(_) => None,
            };
            let each = project_each_exact(&f, &syms);
            DIRECT_OFF.set(true);
            let off = project_each_exact(&f, &syms);
            DIRECT_OFF.set(false);
            EXACT_OFF.set(true);
            let solver = project_each_exact(&f, &syms);
            EXACT_OFF.set(false);
            for (k, n) in names.iter().enumerate() {
                let want = match (both, k < 3) {
                    (false, _) => IntervalSet::empty(),
                    (true, true) => brute(&p, n),
                    (true, false) => brute(&q, NAMES[k - 3]),
                };
                let Some(got) = at(&each, k) else {
                    refused += 1;
                    continue;
                };
                let say = |what: String| format!("seed {seed} round {round} {n}: {what}: {f}");
                if got != want {
                    wrong.push(say(format!("{got} not {want}")));
                }
                if let Some(o) = at(&off, k)
                    && o != got
                {
                    wrong.push(say(format!("{got}, with direct off {o}")));
                }
                if let Some(h) = at(&solver, k)
                    && got.meet(&h) != got
                {
                    wrong.push(say(format!("{got} outside {h}")));
                }
            }
            if !q_empty {
                continue;
            }
            if brute(&p, "x").minus(&IntervalSet::single(0)) != IntervalSet::empty() {
                outside += 1;
            }
            let given: Vec<Result<IntervalSet, Refusal>> = (0..6)
                .map(|k| {
                    Ok(if k < 3 {
                        IntervalSet::single(0)
                    } else {
                        IntervalSet::of(-B, B)
                    })
                })
                .collect();
            let g = super::super::canonical_parts(&f);
            for off in [false, true] {
                DIRECT_OFF.set(off);
                let (got, _) = exact_each(&g, &syms, (given.clone(), vec![]), SOLVER).met();
                DIRECT_OFF.set(false);
                for (k, r) in got.iter().enumerate() {
                    if let Ok(set) = r
                        && !set.is_empty()
                    {
                        let n = names[k];
                        wrong.push(format!(
                            "seed {seed} round {round} {n}, h missing the emptiness, direct off {off}: {set} not empty: {f}"
                        ));
                    }
                }
            }
        }
    }
    println!("{outside} rounds where direct's answer for x leaves h, {refused} refused");
    assert!(wrong.is_empty(), "{wrong:#?}");
    assert!(outside > 0, "no round where the projection of p leaves h");
    assert!(refused <= 12, "{refused} refused");
}

/// A value that each disjunction allows through a different disjunct, where no one
/// combination of them does: `(x == 1 && y == 0 || x == 3 && y == 1) && (x == 1 && y == 1 ||
/// x == 3 && y == 0)` has no point, while the solver's meet of the unions of hulls keeps
/// x in {1, 3}.
#[test]
fn values_two_disjunctions_allow_only_apart_are_left_out() {
    let f = boxed(apart());
    let each = project_each_exact(&f, &[a("x"), a("y")]).unwrap();
    assert_eq!(each.0[0], Ok(IntervalSet::empty()), "{f}");
    assert_eq!(each.0[1], Ok(IntervalSet::empty()), "{f}");
}

/// The fast certificate includes disjunctions and holed domains, but excludes
/// a cyclic constraint graph and a non-unit stride. Compare every projected
/// value with exhaustive points, without using the cover as the oracle.
#[test]
fn certified_forests_match_enumerated_points_without_questions() {
    let mut rng = Rng(0x1380);
    for _ in 0..40 {
        let edge = |x, y, vs: [i64; 2]| {
            Formula::or(vs.into_iter().map(|v| eq(&[(x, 1), (y, -1)], -v)).collect())
        };
        let f = boxed(Formula::and(vec![
            edge("x", "y", [rng.int(-3, 3), rng.int(-3, 3)]),
            edge("y", "z", [rng.int(-3, 3), rng.int(-3, 3)]),
            Formula::or(vec![ge(&[("x", -1)], -2), ge(&[("x", 1)], 0)]),
        ]));
        EXACT_QUESTIONS.set(0);
        let each = super::super::certified_domains(&f, &[a("x"), a("y"), a("z")])
            .expect("a forest is certified");
        for (got, s) in each.0.iter().zip(NAMES) {
            assert_eq!(got, &Ok(brute(&f, s)), "{s}: {f}");
        }
        assert!(each.1.is_empty());
        assert_eq!(EXACT_QUESTIONS.get(), 0);
        assert_eq!(
            project_each_exact(&f, &[a("x"), a("y"), a("z")]).unwrap(),
            each
        );
        assert_eq!(EXACT_QUESTIONS.get(), 0);
    }
    assert!(super::super::certified_domains(&evens(4), &[a("x")]).is_none());
    let edge = |x, y| Formula::or(vec![eq(&[(x, 1), (y, -1)], 0), eq(&[(x, 1), (y, -1)], -2)]);
    let cycle = boxed(Formula::and(vec![
        edge("x", "y"),
        edge("y", "z"),
        edge("z", "x"),
    ]));
    assert!(super::super::certified_domains(&cycle, &[a("x")]).is_none());
}

/// Canonicalization must equalize the work, including the refusal boundary,
/// and must intern duplicate raw subtrees regardless of their input sharing.
#[test]
fn reordered_covers_spend_identical_work() {
    let f = evens(8);
    let Formula::And(parts) = &f else {
        panic!("a conjunction");
    };
    let h = IntervalSet::of(0, 16);
    for limit in [1_000, EXACT_LIMIT] {
        let mut expected = None;
        for reverse in [false, true] {
            let mut kids = parts.to_vec();
            if reverse {
                kids.reverse();
            }
            for child_reverse in [false, true] {
                let kids = kids
                    .iter()
                    .map(|p| match p {
                        Formula::Or(gs) if child_reverse => Formula::Or(super::super::Shared::new(
                            gs.iter().rev().cloned().collect(),
                        )),
                        _ => p.clone(),
                    })
                    .collect();
                let g = Formula::And(super::super::Shared::new(kids));
                EXACT_WORK.set(0);
                EXACT_QUESTIONS.set(0);
                EXACT_LIMIT_SET.set(Some(limit));
                let g = super::super::canonical_parts(&g);
                let got = exact_each(&g, &[a("x")], (vec![Ok(h.clone())], vec![]), SOLVER);
                EXACT_LIMIT_SET.set(None);
                let got = (got, EXACT_WORK.get(), EXACT_QUESTIONS.get());
                if let Some(want) = &expected {
                    assert_eq!(&got, want);
                } else {
                    expected = Some(got);
                }
            }
        }
    }
    // Two equal parts under two parents are one node. (Under one parent a repeated part
    // is kept once, so `p || q` itself is `p`.)
    let p = Formula::Or(super::super::Shared::new(vec![
        ge(&[("x", 1)], 0),
        ge(&[("y", 1)], 0),
    ]));
    let q = Formula::Or(super::super::Shared::new(p.kids().to_vec()));
    let under = |part: Formula, z: i64| {
        Formula::And(super::super::Shared::new(vec![part, ge(&[("z", 1)], z)]))
    };
    let f = Formula::Or(super::super::Shared::new(vec![
        under(p.clone(), 0),
        under(q.clone(), 1),
    ]));
    let g = super::super::canonical_parts(&f);
    let inner = |k: &Formula| {
        let parts: Vec<_> = k
            .kids()
            .iter()
            .filter(|c| !matches!(c, Formula::Con(_)))
            .cloned()
            .collect();
        assert_eq!(parts.len(), 1, "{k:?}");
        Id::any(&parts[0])
    };
    assert_eq!(g.kids().len(), 2, "{g:?}");
    assert_eq!(inner(&g.kids()[0]), inner(&g.kids()[1]));
    let pq =
        super::super::canonical_parts(&Formula::Or(super::super::Shared::new(vec![p.clone(), q])));
    assert_eq!(pq, super::super::canonical_parts(&p));
}

/// A disjunct with a stride keeps its holes: `x != 1 || x + 2 * y == 0` (the shape of the
/// zedc_preimage test of FAIL-or-if-projection-not-exact) gives `x` every value but 1, and
/// `(y >= 1 || y <= -1) && x == 3 * y + 1` the values of `3 * y + 1` in the box.
#[test]
fn a_disjunct_with_a_stride_keeps_its_holes() {
    let f = boxed(Formula::or(vec![
        ge(&[("x", 1)], -2),
        ge(&[("x", -1)], 0),
        eq(&[("x", 1), ("y", 2)], 0),
    ]));
    let x = project(&f, "x");
    assert_eq!(x, brute(&f, "x"), "{f}");
    assert!(!x.contains(1), "{x}");
    let f = boxed(Formula::and(vec![
        Formula::or(vec![ge(&[("y", 1)], -1), ge(&[("y", -1)], -1)]),
        eq(&[("x", 1), ("y", -3)], -1),
    ]));
    assert_eq!(
        project(&f, "x"),
        IntervalSet::from_pieces(vec![(End::of(-2), End::of(-2)), (End::of(4), End::of(4)),])
    );
}

fn project(f: &Formula, s: &str) -> IntervalSet {
    project_each_exact(f, &[a(s)]).unwrap().0.remove(0).unwrap()
}

/// A formula whose cover takes one question for each even value of x in `0..=2k`, the
/// stride of `x == 2 * y` kept apart from the box by a disjunction.
fn evens(k: i64) -> Formula {
    Formula::and(vec![
        Formula::or(vec![
            eq(&[("x", 1), ("y", -2)], 0),
            eq(&[("x", 1), ("z", -2)], 0),
        ]),
        member(&a("x"), &IntervalSet::of(0, 2 * k)),
        member(&a("z"), &IntervalSet::of(0, 2 * k)),
    ])
}

/// A conjunction held by both sides of a conjunction, 18 levels deep: a DAG of 19 parts whose
/// tree has 2^18 paths. Its conjuncts are the two constraints, each read once, and `split`
/// parts them. Read once for each path (before Sol's fix in round 2 of PRES-pugh-xr) they were
/// 2^19, and 2^22 at 22 levels took 42 s and 8 GB.
#[test]
fn splitting_a_shared_conjunction_reads_it_once() {
    let mut f = Formula::And(Shared::new(vec![ge(&[("x", 1)], 0), ge(&[("y", 1)], 0)]));
    for _ in 0..18 {
        f = Formula::And(Shared::new(vec![f.clone(), f]));
    }
    assert_eq!(f.conjuncts().len(), 2);
    let parts = split(&f);
    assert_eq!(parts.len(), 2);
    assert!(parts.iter().all(|p| p.size == 1));
}

/// [`evens`] with a second disjunction on `z`, `z <= 2k or y <= -1`, which holds wherever
/// `evens` does, so that `direct` declines it: two disjunctions tied through `z` in one group
/// (since PRES-cover-refusals-moduli `direct` answers `evens` itself, one disjunction with the
/// bound on `z`).
fn evens_tied(k: i64) -> Formula {
    Formula::and(vec![
        evens(k),
        Formula::or(vec![ge(&[("z", -1)], 2 * k), ge(&[("y", -1)], -1)]),
    ])
}

/// The work limit on both sides: allowed exactly the work the cover of [`evens_tied`] takes,
/// the solver's work for its questions included and that of its fast path left out (`tried`:
/// `direct` reads the rows and fails, two disjunctions grouped through `z`), it answers with the exact set (the even values); allowed one unit
/// less, it refuses ([`Refusal::Questions`]) and never answers with the solver's set, which
/// has values with no point (PRES-pugh-work-budget). The work is counted, so a second run
/// uses the same. Before `tried` had an allowance of its own, the failed fast path was
/// charged to the limit, and the cover was refused at the limit its loop needs.
#[test]
fn the_work_limit_is_met_alike_on_both_sides() {
    let f = evens_tied(20);
    let want =
        IntervalSet::from_pieces((0..=20).map(|v| (End::of(2 * v), End::of(2 * v))).collect());
    EXACT_WORK.set(0);
    FAST_WORK.set(0);
    assert_eq!(project(&f, "x"), want);
    let fast = FAST_WORK.replace(0);
    let used = EXACT_WORK.replace(0) - fast;
    assert!(used > 0);
    assert!(fast > 0, "the fast path read nothing");
    EXACT_LIMIT_SET.set(Some(used));
    assert_eq!(project(&f, "x"), want);
    assert_eq!(
        EXACT_WORK.replace(0) - FAST_WORK.replace(0),
        used,
        "the work is not the same on a second run"
    );
    EXACT_LIMIT_SET.set(Some(used - 1));
    let r = project_each_exact(&f, &[a("x")]).unwrap();
    EXACT_LIMIT_SET.set(None);
    assert_eq!(r.0, vec![Err(Refusal::Questions)]);
    assert!(r.1.is_empty(), "{:?}", r.1);
    EXACT_OFF.set(true);
    let solver = project(&f, "x");
    EXACT_OFF.set(false);
    assert!(solver.meet(&want) == want && solver != want, "{solver}");
}

/// An unbounded set with holes, the even values of `x == 2 * y || x == 2 * z` with no
/// bound, is not a finite union of ranges, so no answer is exact: the cover's tail
/// question proves the holes, and the piece holding them is kept whole, every value,
/// with [`Refusal::Repeats`] as the cause of the wider answer.
#[test]
fn an_unbounded_set_with_holes_is_kept_whole_with_its_cause() {
    let f = Formula::or(vec![
        eq(&[("x", 1), ("y", -2)], 0),
        eq(&[("x", 1), ("z", -2)], 0),
    ]);
    EXACT_LIMIT_SET.set(Some(10_000));
    let (mut each, causes) = project_each_exact(&f, &[a("x")]).unwrap();
    EXACT_LIMIT_SET.set(None);
    assert_eq!(
        each.remove(0),
        Ok(IntervalSet::range(End::NegInf, End::PosInf))
    );
    assert_eq!(causes, vec![Refusal::Repeats]);
}

/// Exhaust the orders of two strided rays and a finite exception, including the
/// orders inside each conjunction. The oracle enumerates witnesses in a box large
/// enough for every tested x; it does not ask the solver. P246 and
/// PRES-cover-tail-writing: the answer is read from the exact set `E` alone, the ray below
/// past the last value where `E` and its period differ whole and `E` above it exact, the
/// same for the solver's `h`, for another sound `h`, for every order, and for every place
/// the cells stop and the kept tail starts.
#[test]
fn holed_tails_agree_in_every_order_and_with_enumerated_points() {
    // Sound for every formula here (each has `x <= 4`), and wider than the solver's.
    let wide = IntervalSet::range(End::NegInf, End::of(4));
    let orders = [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ];
    let mut checked = 0;
    for step in [3, 4, 5] {
        for offset in [1, 7] {
            let mut expected = None;
            for order in orders {
                for mask in 0..8 {
                    let ray = |name: &str, residue: i64, reverse: bool| {
                        let mut rows = vec![
                            eq(&[("x", 1), (name, -step)], -residue),
                            ge(&[("x", -1)], -offset),
                        ];
                        if reverse {
                            rows.reverse();
                        }
                        Formula::And(super::super::Shared::new(rows))
                    };
                    let arms = [
                        ray("y", 0, mask & 1 != 0),
                        ray("z", 1, mask & 2 != 0),
                        eq(&[("x", 1)], -3),
                    ];
                    let disj = Formula::Or(super::super::Shared::new(
                        order.iter().map(|i| arms[*i].clone()).collect(),
                    ));
                    let mut top = vec![disj, ge(&[("x", -1)], 4)];
                    if mask & 4 != 0 {
                        top.reverse();
                    }
                    let f = Formula::And(super::super::Shared::new(top));
                    // The whole path, and `exact_each` given another sound `h` directly,
                    // so the test exercises the cover even if a future solver fast path
                    // recognizes this family: one answer.
                    let got = project_each_exact(&f, &[a("x")]).expect("answered");
                    let given = exact_each(
                        &super::super::canonical_parts(&f),
                        &[a("x")],
                        (vec![Ok(wide.clone())], vec![]),
                        SOLVER,
                    )
                    .met();
                    assert_eq!(got, given, "{f}");
                    let set = got.0[0].as_ref().expect("this small tail must answer");
                    assert_eq!(got.1, vec![Refusal::Repeats], "{f}");
                    if let Some(want) = &expected {
                        assert_eq!(&got, want, "{f}");
                    } else {
                        expected = Some(got.clone());
                    }
                    // `E` from enumerated points in [-12, 12]; below it `E` is its period,
                    // the residues 0 and 1 (each ray reaches past -12 with no other bound).
                    let period = |x: i64| matches!(x.rem_euclid(step), 0 | 1);
                    let listed: Vec<bool> = (-12..=12)
                        .map(|x| {
                            (-20..=20).any(|v| {
                                let m = [
                                    (a("x"), Int::from(x)),
                                    (a("y"), Int::from(v)),
                                    (a("z"), Int::from(v)),
                                ]
                                .into_iter()
                                .collect();
                                f.holds(&m)
                            })
                        })
                        .collect();
                    let e = |x: i64| {
                        if x < -12 {
                            period(x)
                        } else {
                            x <= 12 && listed[(x + 12) as usize]
                        }
                    };
                    // The rule: `d` the least value where `E` and its period differ (one
                    // above 4 at the latest), `l` the greatest value of `E` below it, then
                    // `(-inf, l]` and `E` above `l`.
                    let d = (-12..=12)
                        .find(|&x| e(x) != period(x))
                        .expect("a difference");
                    let l = (-12..d).rev().find(|&x| e(x)).expect("a value below");
                    let points = |from: i64| {
                        IntervalSet::from_pieces(
                            (from..=12)
                                .filter(|&x| e(x))
                                .map(|x| (End::of(x), End::of(x)))
                                .collect(),
                        )
                    };
                    let want = IntervalSet::range(End::NegInf, End::of(l)).join(&points(l + 1));
                    assert_eq!(set, &want, "{f}");
                    for x in -12..=12 {
                        assert!(!e(x) || set.contains(x), "lost point {x}: {f}");
                    }
                    // ended reads `E` alone: the same wherever the cells stopped and the
                    // kept tail starts (below `d`, where `E` is the tail's residues).
                    for cut in [d - 1, d - 4, d - 25] {
                        let kept = vec![Kept {
                            lo: End::NegInf,
                            hi: End::of(cut),
                            step: Int::from(step),
                            have: (0..step).map(period).collect(),
                        }];
                        let mut work = Work {
                            used: 0,
                            limit: u64::MAX,
                            solver: SOLVER,
                        };
                        assert_eq!(
                            ended(points(cut + 1), kept, &mut work),
                            Ok((want.clone(), true)),
                            "cut {cut}: {f}"
                        );
                    }
                    checked += 1;
                }
            }
        }
    }
    assert_eq!(checked, 288);
}

/// The conjunction of a pendants part that ran forever (l01_39 `pendants`, rows 5 to 9):
/// `w == 2·a - b` with `a <= -14`, so `w` unbounded below. The elimination that never
/// grows its rows leaves atoms of it, so each cell was one line and each question found
/// one more value; with every exact step done (`eliminated_whole`) one cell covers it.
#[test]
fn an_unbounded_conjunction_needs_one_cell() {
    let f = Formula::and(vec![
        ge(&[("a", -1)], -14),
        ge(&[("b", 1)], -1),
        ge(&[("b", -1)], 8),
        ge(&[("z2", -1)], -9),
        ge(&[("z3", -1)], 2),
        ge(&[("a", -2), ("b", -1), ("c", -1), ("z2", 1)], -7),
        ge(&[("a", -1), ("b", -2), ("z2", 1)], -2),
        eq(&[("a", -1), ("c", -1), ("z3", 1)], -5),
        ge(&[("a", 1), ("b", 1), ("c", 1), ("z2", -1)], 6),
        ge(&[("z2", -1), ("z3", 1)], -11),
        eq(&[("w", -1), ("a", 2), ("b", -1)], 0),
        ge(&[("w", -1)], -29),
    ]);
    EXACT_QUESTIONS.set(0);
    // Every `w <= -31`, and -29: -30 needs `a == -14`, `b == 2`, so `z2 >= -8`, past `z2 <= -9`.
    let want = IntervalSet::from_pieces(vec![
        (End::NegInf, End::of(-31)),
        (End::of(-29), End::of(-29)),
    ]);
    assert_eq!(project(&f, "w"), want);
    assert!(
        EXACT_QUESTIONS.get() <= 2,
        "{} questions",
        EXACT_QUESTIONS.get()
    );
}
/// The part of l01_39 `pendants` (case 272 of seed 17) whose `b` the solver answers
/// `[-4, 15]`. Every `b` in `-4..=15` has a point (all points of the box with `c` in
/// `-3..=8` listed, PRES-pugh-findings; 15: `a == 2, c == -3, z2 == 6, z1 == -7`) and 16
/// has none (`a + b + 2·c == z2 + 5` with `z2 <= 6`, `a >= 2` gives `c <= -4`, and
/// `a + 2·c >= -4` gives `c >= -3`), so `[-4, 15]` is the exact set. But the cover's
/// question of the piece `-4..=0` (or `-4..=-2`, by the in-cell method) is refused by the
/// solver (`Refusal::Growth`), so `b` is refused for that cause: a piece not confirmed is
/// never kept as the solver's set had it (PRES-pugh-work-budget; the caller reports it and
/// keeps the box of the rows).
#[test]
fn the_pendants_part_of_row_3_refuses_b_for_its_refused_question() {
    let mem = |s: &str, l: Option<i64>, u: Option<i64>| {
        let e = |v: Option<i64>, inf| v.map(End::of).unwrap_or(inf);
        member(
            &a(s),
            &IntervalSet::from_pieces(vec![(e(l, End::NegInf), e(u, End::PosInf))]),
        )
    };
    let f = Formula::and(vec![
        mem("a", Some(2), Some(3)),
        mem("b", Some(-4), None),
        mem("c", None, Some(8)),
        mem("z0", Some(-6), Some(-4)),
        mem("z1", Some(-7), Some(13)),
        mem("z2", Some(-10), Some(6)),
        ge(&[("a", 1), ("c", 2)], 4),
        Formula::or(vec![ge(&[("a", 2), ("b", 1)], -7), ge(&[("z2", -1)], 8)]),
        ge(&[("a", 1), ("b", 2), ("c", 1), ("z1", 1)], -4),
        ge(&[("a", 1), ("b", -1), ("z1", -1)], 6),
        Formula::or(vec![ge(&[("b", 1), ("c", -1)], 11), ge(&[("z2", -1)], 4)]),
        ge(&[("a", 1), ("b", 1), ("c", 1), ("z1", -1)], -2),
        ge(&[("a", -1), ("z1", -1), ("b", 1), ("c", 1)], 9),
        ge(&[("a", 1), ("c", 1), ("z0", -1)], 12),
        eq(&[("a", 1), ("b", 1), ("c", 2), ("z2", -1)], -5),
    ]);
    let b = project_each_exact(&f, &[a("b")]).unwrap().0.remove(0);
    assert_eq!(b, Err(Refusal::Growth), "{b:?}");
    // By model-based projection the cells hold the disjuncts that hold their points, and no
    // question is refused: the exact set (2026-11-18, PRES-cover-refusals-where-exact).
    METHOD.set(Some(Method::Liaproj));
    let b = project_each_exact(&f, &[a("b")]).unwrap().0.remove(0);
    METHOD.set(None);
    let want = IntervalSet::from_pieces(vec![(End::of(-4), End::of(15))]);
    assert_eq!(b, Ok(want), "{b:?}");
}

/// The questions of the cover on a stride, as the remainder reading writes one (`y == 2·q
/// + r` with `r == 0`), and on remainders kept in a range (`x == 1024·q + r` with `r` in
/// `0..=36`), each in a box: the even values of `y` (but -4 and -2, which a case leaves out) from one point, along the direction that
/// keeps the equation (`directions`); a run of 37 values of `x` from each point, with `q`
/// fixed (`strides_fixed`).
#[test]
fn strides_and_remainders_are_covered_a_few_points_each() {
    let f = Formula::and(vec![
        eq(&[("y", 1), ("q", -2), ("r", -1)], 0),
        eq(&[("r", 1)], 0),
        member(&a("y"), &IntervalSet::of(-1000, 1000)),
        Formula::or(vec![ge(&[("y", 1)], 0), ge(&[("y", -1)], -5)]),
    ]);
    let evens = (-500..=500).filter(|v| !(-2..=-1).contains(v));
    let want = IntervalSet::from_pieces(evens.map(|v| (End::of(2 * v), End::of(2 * v))).collect());
    EXACT_QUESTIONS.set(0);
    assert_eq!(project(&f, "y"), want);
    assert!(
        EXACT_QUESTIONS.get() <= 4,
        "{} questions",
        EXACT_QUESTIONS.get()
    );
    let f = Formula::and(vec![
        eq(&[("x", 1), ("q", -1024), ("r", -1)], 0),
        member(&a("r"), &IntervalSet::of(0, 1023)),
        member(&a("x"), &IntervalSet::of(-10240, 10239)),
        Formula::or(vec![ge(&[("r", -1)], 36), ge(&[("r", 1)], -2000)]),
    ]);
    let want = IntervalSet::from_pieces(
        (-10..10)
            .map(|q| (End::of(1024 * q), End::of(1024 * q + 36)))
            .collect(),
    );
    EXACT_QUESTIONS.set(0);
    assert_eq!(project(&f, "x"), want);
    assert!(
        EXACT_QUESTIONS.get() <= 2 * 20 + 2,
        "{} questions",
        EXACT_QUESTIONS.get()
    );
}

/// `f` with the parts of every conjunction and disjunction in a random order.
fn shuffled(f: &Formula, rng: &mut Rng) -> Formula {
    let mut turned = |gs: &[Formula]| {
        let mut gs: Vec<Formula> = gs.iter().map(|g| shuffled(g, rng)).collect();
        for i in (1..gs.len()).rev() {
            gs.swap(i, rng.below(i as u64 + 1) as usize);
        }
        gs
    };
    match f {
        Formula::Con(_) => f.clone(),
        Formula::Not(g) => Formula::Not(Shared::new(turned(std::slice::from_ref(&**g)).remove(0))),
        Formula::And(gs) => Formula::And(Shared::new(turned(gs))),
        Formula::Or(gs) => Formula::Or(Shared::new(turned(gs))),
    }
}

/// The window of `x` read by [`holed`], and the box of `y` and `z`.
const W: i64 = 30;
const BY: i64 = 2;

/// A random formula over `x`, unbounded, and `y` and `z`, each in `-BY..=BY`, whose
/// projection onto `x` has holes without end: besides constraints over x, y and z, its
/// leaves include strides `x == m * k + r` (m from 2 to 4), each with a `k` of its own that
/// no other leaf reads. With the strides listed as `(k, m, r)`.
fn holed(rng: &mut Rng) -> (Formula, Vec<(String, i64, i64)>) {
    fn leaf(rng: &mut Rng, strides: &mut Vec<(String, i64, i64)>) -> Formula {
        if rng.below(3) == 0 {
            let (m, k) = (rng.int(2, 4), format!("k{}", strides.len()));
            let r = rng.int(0, m - 1);
            strides.push((k.clone(), m, r));
            return eq(&[("x", 1), (k.as_str(), -m)], -r);
        }
        let terms = [
            ("x", rng.int(-2, 2)),
            ("y", rng.int(-2, 2)),
            ("z", rng.int(-2, 2)),
        ];
        let terms: Vec<_> = if terms.iter().all(|t| t.1 == 0) {
            vec![("y", 1)]
        } else {
            terms.to_vec()
        };
        if rng.below(4) == 0 {
            eq(&terms, rng.int(-3, 3))
        } else {
            ge(&terms, rng.int(-6, 6))
        }
    }
    fn node(rng: &mut Rng, d: u32, strides: &mut Vec<(String, i64, i64)>) -> Formula {
        if d == 0 || rng.below(4) == 0 {
            return leaf(rng, strides);
        }
        let parts: Vec<Formula> = (0..2 + rng.below(2))
            .map(|_| node(rng, d - 1, strides))
            .collect();
        match rng.below(5) {
            0 => Formula::negate(Formula::and(parts)),
            1 | 2 => Formula::and(parts),
            _ => Formula::or(parts),
        }
    }
    let mut strides = Vec::new();
    let g = node(rng, 3, &mut strides);
    let f = Formula::and(vec![
        member(&a("y"), &IntervalSet::of(-BY, BY)),
        member(&a("z"), &IntervalSet::of(-BY, BY)),
        g,
    ]);
    (f, strides)
}

/// The values of `x` in `-W..=W` with a point of `f`, from [`holed`]: `y` and `z` over
/// their box, and each `k` at `(x - r) / m` where that is whole, and one more, so that its
/// stride holds or fails as a point may choose; `k` read by one leaf alone, every point is
/// reached.
///
/// Only the strides that can hold at `x` (`m` divides `x - r`) are given both values of
/// their `k`: at any other `x` the stride `x == m * k + r` fails at `k = (x - r) / m`
/// rounded down and at one more alike, and its `k` is read by no other leaf, so the two
/// values give `f` the same truth and one of them suffices. Exact, and it takes
/// `2^(strides that can hold at x)` points per `(x, y, z)` in place of `2^(strides)`: with
/// every stride enumerated, seed 10847150771481521372 took 21 to 38 s, past the 20 s limit
/// of a piece (FAIL-cover-every-order-seed-time).
fn holed_values(f: &Formula, strides: &[(String, i64, i64)]) -> IntervalSet {
    let mut set = IntervalSet::empty();
    for x in -W..=W {
        let can_hold: Vec<usize> = (0..strides.len())
            .filter(|&i| (x - strides[i].2).rem_euclid(strides[i].1) == 0)
            .collect();
        'x: for y in -BY..=BY {
            for z in -BY..=BY {
                for pick in 0..1u32 << can_hold.len() {
                    let mut m: Model = [
                        (a("x"), Int::from(x)),
                        (a("y"), Int::from(y)),
                        (a("z"), Int::from(z)),
                    ]
                    .into_iter()
                    .collect();
                    for (k, step, r) in strides {
                        m.insert(a(k), Int::from((x - r).div_euclid(*step)));
                    }
                    for (bit, &i) in can_hold.iter().enumerate() {
                        let (k, step, r) = &strides[i];
                        let base = (x - r).div_euclid(*step);
                        m.insert(a(k), Int::from(base + i64::from(pick >> bit & 1)));
                    }
                    if f.holds(&m) {
                        set = set.join(&IntervalSet::single(x));
                        break 'x;
                    }
                }
            }
        }
    }
    set
}

/// R1 cross-review Q2(c): the weakest claim of the cover was that its answer, and `ended`'s
/// pieces kept whole, are the same in every order of a formula's parts. Formulas with holes
/// without end in `x` ([`holed`]) are projected in their order and in random orders of the
/// parts of every node; each answer, its cause and each refusal must be the same in every
/// order, and the answer must hold exactly the values of `x` in `-W..=W` that points
/// enumerated there give, or more where the cause is [`Refusal::Repeats`] (a piece of `h`
/// kept whole), never fewer. `canonical_parts` must also give one formula for every order. Each
/// formula is projected at the work limit and again at `LOW`, so that many covers end
/// near their limit, where a refusal decided by the order of the work would show.
#[test]
fn the_cover_gives_one_answer_in_every_order_of_the_parts() {
    const LOW: u64 = 150_000;
    let seed = crate::seed::seed("the_cover_gives_one_answer_in_every_order_of_the_parts");
    let mut rng = Rng(seed | 1);
    let syms = vec![a("x")];
    let window = IntervalSet::of(-W, W);
    let (mut differ, mut wrong, mut narrow) = (Vec::new(), Vec::new(), Vec::new());
    let (mut repeats, mut refused, mut forms) = (0, [0, 0], 0);
    for round in 0..40 {
        let (f, strides) = holed(&mut rng);
        let want = holed_values(&f, &strides);
        let one = super::super::canonical_parts(&f);
        let orders: Vec<Formula> = (0..6).map(|_| shuffled(&f, &mut rng)).collect();
        for g in &orders {
            forms += 1;
            if super::super::canonical_parts(g) != one
                || format!("{:?}", super::super::canonical_parts(g)) != format!("{one:?}")
            {
                differ.push(format!(
                    "round {round}: canonical form differs: {f} and {g}"
                ));
            }
        }
        for (l, limit) in [None, Some(LOW)].into_iter().enumerate() {
            EXACT_LIMIT_SET.set(limit);
            let first = project_each_exact(&f, &syms);
            for g in &orders {
                let other = project_each_exact(g, &syms);
                if other != first {
                    differ.push(format!(
                        "round {round} limit {limit:?}: {first:?} and {other:?}: {f} and {g}"
                    ));
                }
            }
            EXACT_LIMIT_SET.set(None);
            match &first {
                Ok((sets, causes)) => match &sets[0] {
                    Ok(got) => {
                        let seen = got.meet(&window);
                        let kept = causes.contains(&Refusal::Repeats);
                        repeats += usize::from(kept);
                        if !want.minus(&seen).is_empty() {
                            narrow.push(format!("round {round}: {seen} misses {want}: {f}"));
                        } else if seen != want && !kept {
                            wrong.push(format!("round {round}: {seen} not {want}: {f}"));
                        }
                    }
                    Err(_) => refused[l] += 1,
                },
                Err(_) => refused[l] += 1,
            }
        }
    }
    println!(
        "seed {seed}: {forms} orders, {repeats} answers kept with Repeats, refused {} at the limit and {} at {LOW}",
        refused[0], refused[1]
    );
    assert!(differ.is_empty(), "seed {seed}: {differ:#?}");
    assert!(narrow.is_empty(), "seed {seed}: {narrow:#?}");
    assert!(wrong.is_empty(), "seed {seed}: {wrong:#?}");
}

/// PRES-pugh-xr round 3, question B: `direct` runs under the full A99 work limit `L` on its
/// own meter (`tried`), so a structural projection needing between `L / 4` and `L` units
/// answers in zero solver questions, and a depleted `fast == 0` allowance walks nothing.
#[test]
fn fast_path_uses_the_full_work_limit_and_zero_allowance_walks_nothing() {
    let arms: Vec<Formula> = (0..=30).map(|k| eq(&[("x", 1)], -2 * k)).collect();
    // `y - 2 * x == 0` skips `certified_domains` (`-2` is not unit), while `direct`
    // eliminates `y` by Pugh's unit-coefficient shadow with zero solver questions.
    let f = Formula::and(vec![eq(&[("y", 1), ("x", -2)], 0), Formula::or(arms)]);
    let want =
        IntervalSet::from_pieces((0..=30).map(|k| (End::of(2 * k), End::of(2 * k))).collect());

    EXACT_QUESTIONS.set(0);
    EXACT_WORK.set(0);
    FAST_WORK.set(0);
    assert_eq!(project(&f, "x"), want);
    assert_eq!(EXACT_QUESTIONS.replace(0), 0);
    let fast_needed = FAST_WORK.replace(0);
    assert_eq!(EXACT_WORK.replace(0), fast_needed);
    assert!(fast_needed > 4);

    // At limit == `fast_needed`, the old `limit / 4` allowance aborted `direct` a quarter of
    // the way through; with `fast = work.limit`, `direct` finishes with zero solver questions
    // and total work <= L.
    EXACT_LIMIT_SET.set(Some(fast_needed));
    EXACT_QUESTIONS.set(0);
    EXACT_WORK.set(0);
    FAST_WORK.set(0);
    let got = project_each_exact(&f, &[a("x")]).unwrap().0;
    EXACT_LIMIT_SET.set(None);
    assert_eq!(got, vec![Ok(want)]);
    assert_eq!(EXACT_QUESTIONS.replace(0), 0);
    assert_eq!(FAST_WORK.replace(0), fast_needed);
    assert_eq!(EXACT_WORK.replace(0), fast_needed);

    // Once `fast` reaches 0 in `has_points`, `tried` must not walk `holders` or charge reads.
    let mut zero = 0;
    EXACT_WORK.set(0);
    FAST_WORK.set(0);
    let skipped = tried(&mut zero, SOLVER, |w| {
        direct(&f, &a("x"), &IntervalSet::top(), w)
    });
    assert!(skipped.is_none());
    assert_eq!(FAST_WORK.replace(0), 0);
    assert_eq!(EXACT_WORK.replace(0), 0);
}

/// PRES-pugh-xr round 3, question D(1): `eliminated_counted` charges the `p * q` bound pairs
/// formed under `one_other()` in both `projected` and `cell`, and when the meter runs out
/// mid-shadow `Work::metered` returns `Err(Refusal::Questions)` rather than reading a
/// truncated shadow as empty.
#[test]
fn counted_elimination_charges_pairs_and_refuses_when_spent() {
    let s = a("x");
    let p = 30i64;
    let mut rows: Vec<Con> = vec![
        Con::ge(&lin(&[("x", 1)], 0), &Lin::constant(0)),
        Con::ge(&lin(&[("x", -1)], 10), &Lin::constant(0)),
    ];
    for i in 1..=p {
        rows.push(Con::ge(&lin(&[("y", 1), ("x", -i)], 0), &Lin::constant(0)));
        rows.push(Con::ge(
            &lin(&[("y", -1), ("x", i)], 1000),
            &Lin::constant(0),
        ));
    }
    let read_only = (rows.len() as u64) * SOLVER_UNIT;
    let pair_work = ((p * p) as u64) * SOLVER_STEP;

    let mut full = Work {
        used: 0,
        limit: u64::MAX,
        solver: SOLVER,
    };
    let got = projected(&rows, &s, &mut full).unwrap();
    assert_eq!(got, Some(IntervalSet::of(0, 10)));
    assert!(
        full.used >= read_only + pair_work,
        "expected at least {} units (reads {} + pairs {}), got {}",
        read_only + pair_work,
        read_only,
        pair_work,
        full.used
    );

    // One unit below the full cost, the shadow truncates mid-elimination and `projected`
    // refuses with `Questions` (never `Ok(Some(empty))`).
    let mut tight = Work {
        used: 0,
        limit: full.used - 1,
        solver: SOLVER,
    };
    assert_eq!(projected(&rows, &s, &mut tight), Err(Refusal::Questions));

    // The same holds in `cell`'s quick path on a satisfiable point `(x = 0, y = 0)`.
    let f_conj = Formula::And(Shared::new(
        rows.iter().cloned().map(Formula::Con).collect(),
    ));
    let m: Model = [(a("x"), Int::from(0)), (a("y"), Int::from(0))]
        .into_iter()
        .collect();
    let factors = HashSet::new();
    let within = IntervalSet::of(0, 10);
    let mut cell_full = Work {
        used: 0,
        limit: u64::MAX,
        solver: SOLVER,
    };
    let (c_set, _, _) = cell(&f_conj, &m, &s, &factors, &within, &mut cell_full).unwrap();
    assert_eq!(c_set, IntervalSet::of(0, 10));
    assert!(cell_full.used >= read_only + pair_work);

    let mut cell_tight = Work {
        used: 0,
        limit: cell_full.used - 1,
        solver: SOLVER,
    };
    assert_eq!(
        cell(&f_conj, &m, &s, &factors, &within, &mut cell_tight).err(),
        Some(Refusal::Questions)
    );
}

/// PRES-pugh-xr round 3, question D(2): when `canonical` or `System::add` passes the meter's
/// limit inside `solve`, `solve` stops at once instead of running color refinement, component
/// search, `System::add` and `relaxed_empty` across the remaining rows and components.
#[test]
fn spent_canonical_and_system_add_stop_without_unbounded_tail_charges() {
    let mut cons: Vec<Con> = Vec::new();
    for i in 0..80 {
        let x = format!("u{i}");
        let y = format!("v{i}");
        cons.push(Con::ge(&lin(&[(&x, 1), (&y, 1)], 0), &Lin::constant(0)));
        cons.push(Con::ge(&lin(&[(&x, 1), (&y, -1)], 0), &Lin::constant(0)));
        cons.push(Con::ge(&lin(&[(&x, -1)], 10), &Lin::constant(0)));
        cons.push(Con::ge(&lin(&[(&y, -1)], 10), &Lin::constant(0)));
    }
    // `solve` charges `cons.len() + terms` = `320 + 480 = 800` solver steps on entry, and
    // `canonical` charges `n + cons.len() + terms` = `160 + 320 + 480 = 960` solver steps.
    let entry_charge = (320 + 480) * SOLVER_STEP;
    let canon_charge = (160 + 320 + 480) * SOLVER_STEP;

    // Failing in `canonical` must stop before any `System::add` runs.
    let mut w_canon = Work {
        used: 0,
        limit: entry_charge + SOLVER_STEP,
        solver: SOLVER,
    };
    let r_canon = w_canon.metered(|| super::super::solve(&cons, true));
    assert_eq!(r_canon, Err(Refusal::Questions));
    assert_eq!(
        w_canon.used,
        entry_charge + canon_charge,
        "solve continued charging after canonical spent the meter"
    );

    // Failing in the first component's `System::add` must stop without charging the other 79
    // components (`320` rows would add `> 320 * SOLVER_STEP` more units if ignored).
    let step_limit = entry_charge + canon_charge + 4 * SOLVER_STEP;
    let mut w_add = Work {
        used: 0,
        limit: step_limit,
        solver: SOLVER,
    };
    let r_add = w_add.metered(|| super::super::solve(&cons, true));
    assert_eq!(r_add, Err(Refusal::Questions));
    assert!(
        w_add.used <= step_limit + 4 * SOLVER_STEP,
        "System::add kept running across remaining rows/components: used={} vs limit={}",
        w_add.used,
        step_limit
    );
}

/// PRES-cover-sign-through-h (seat Gemini, PRES-pugh-xr round 3): the cover's input
/// (`cover_input`) is the same for two writings of one formula, but the solver's hull `h`
/// (`factored` before `signed`) and `certified_domains` (`is_difference` before rows are
/// reduced by their gcd) read the formula as written, so flipping one equation's sign or
/// scaling one inequality by 2 can widen `h` or skip `certified_domains` and turn an answer
/// into [`Refusal::Questions`] at a limit the other writing meets.
#[test]
fn one_meaning_written_with_another_sign_or_scale_gets_one_answer() {
    let u_pos = Formula::And(Shared::new(vec![
        ge(&[("b", 1)], -1),
        Formula::Or(Shared::new(vec![
            eq(&[("b", 2), ("a", -1)], 0),
            ge(&[("b", 1)], -1),
        ])),
    ]));
    let u_neg = Formula::And(Shared::new(vec![
        ge(&[("b", 1)], -1),
        Formula::Or(Shared::new(vec![
            eq(&[("b", -2), ("a", 1)], 0),
            ge(&[("b", 1)], -1),
        ])),
    ]));
    let build = |last_u: Formula| {
        // `c0 <= c1 || c1 <= c2 || ... || c7 <= c0` holds on all integers: its negation is
        // the strict 8-cycle `c0 > c1 > ... > c7 > c0`, which has no unary bounds and every
        // proper subset satisfiable. When all eight arms share `u_pos`, `factored` pulls
        // `u_pos` out leaving one 2-arm disjunction whose cycle arm `solve` empties; when the
        // eighth arm flips `2*b - a == 0` to `-2*b + a == 0`, `factored` misses before
        // `signed` runs, leaving eight disjunctions whose solver hull on `b` stays unbounded
        // above.
        let names = ["c0", "c1", "c2", "c3", "c4", "c5", "c6", "c7"];
        let mut ds: Vec<Formula> = (0..7)
            .map(|i| {
                Formula::And(Shared::new(vec![
                    u_pos.clone(),
                    ge(&[(names[i + 1], 1), (names[i], -1)], 0),
                ]))
            })
            .collect();
        ds.push(Formula::And(Shared::new(vec![
            last_u,
            ge(&[(names[0], 1), (names[7], -1)], 0),
        ])));
        let tiers = Formula::Not(Shared::new(Formula::Or(Shared::new(ds))));
        Formula::And(Shared::new(vec![
            ge(&[("b", 1)], 5),
            eq(&[("a", 1), ("b", -1)], -1),
            Formula::Or(Shared::new(vec![ge(&[("a", -1)], 0), ge(&[("a", 1)], -5)])),
            tiers,
        ]))
    };
    let f_same = build(u_pos.clone());
    let f_flip = build(u_neg);
    assert_eq!(
        super::super::cover_input(&f_same),
        super::super::cover_input(&f_flip)
    );

    EXACT_OFF.set(true);
    let h_same = project(&f_same, "b");
    let h_flip = project(&f_flip, "b");
    EXACT_OFF.set(false);
    let exact_b = IntervalSet::of(-5, -1);
    println!("solver sets for b: same={h_same}, flip={h_flip}");

    EXACT_QUESTIONS.set(0);
    EXACT_WORK.set(0);
    FAST_WORK.set(0);
    assert_eq!(project(&f_same, "b"), exact_b);
    let q_same = EXACT_QUESTIONS.replace(0);
    let loop_same = EXACT_WORK.replace(0) - FAST_WORK.replace(0);

    EXACT_QUESTIONS.set(0);
    EXACT_WORK.set(0);
    FAST_WORK.set(0);
    assert_eq!(project(&f_flip, "b"), exact_b);
    let q_flip = EXACT_QUESTIONS.replace(0);
    let loop_flip = EXACT_WORK.replace(0) - FAST_WORK.replace(0);
    println!("questions and loop work: same=({q_same}, {loop_same}), flip=({q_flip}, {loop_flip})");

    for limit in [loop_same, loop_flip] {
        EXACT_LIMIT_SET.set(Some(limit));
        let same = project_each_exact(&f_same, &[a("b")]).unwrap().0;
        let flip = project_each_exact(&f_flip, &[a("b")]).unwrap().0;
        EXACT_LIMIT_SET.set(None);
        assert_eq!(
            same, flip,
            "one equation written with the other sign, limit {limit}"
        );
    }

    // Case A-2: `x >= 0` scaled to `2 * x >= 0` keeps the same cover input.
    let g = |k: i64| {
        Formula::And(Shared::new(vec![
            ge(&[("x", k)], 0),
            ge(&[("x", -1)], 10),
            Formula::Or(Shared::new(vec![
                eq(&[("x", 1), ("y", -1)], 0),
                eq(&[("x", 1), ("y", -1)], -2),
            ])),
        ]))
    };
    assert_eq!(
        super::super::cover_input(&g(1)),
        super::super::cover_input(&g(2))
    );
    for limit in [Some(1), Some(10), None] {
        EXACT_LIMIT_SET.set(limit);
        let unit = project_each_exact(&g(1), &[a("x")]).unwrap().0;
        let scaled = project_each_exact(&g(2), &[a("x")]).unwrap().0;
        EXACT_LIMIT_SET.set(None);
        assert_eq!(
            scaled, unit,
            "2x >= 0 and x >= 0 are one row, limit {limit:?}"
        );
    }
    assert_eq!(
        project_each_exact(&g(1), &[a("x")]).unwrap().0,
        vec![Ok(IntervalSet::of(0, 10))]
    );
}

/// `f` with every equation in the other sign.
fn flipped(f: &Formula) -> Formula {
    f.map_cons(&|c| {
        Formula::Con(match c.rel {
            Rel::Eq => Con {
                lin: c.lin.times(-1),
                rel: Rel::Eq,
            },
            Rel::Ge => c.clone(),
        })
    })
}

/// `f` with every row times `k`, more than zero, as written, not divided by the gcd.
fn scaled(f: &Formula, k: i64) -> Formula {
    f.map_cons(&|c| {
        Formula::Con(Con {
            lin: c.lin.times(k),
            rel: c.rel,
        })
    })
}

/// PRES-cover-sign-through-h and PRES-cover-tail-writing: the answer depends on the formula
/// alone. Random formulas, boxed ([`boxed`]) and with holes without end in `x`
/// ([`holed`]), are projected as written and in writings that `cover_input` makes one:
/// every equation in the other sign, every row times 2 or 3, the parts in random orders, the
/// formula repeated as a conjunct of itself, and all of these at once. Each must give the
/// same answer, cause and refusal, at the full limit and at a low one. Writings that are other
/// inputs, a part shared by every disjunct taken out by hand and the formula with no part
/// taken out (`UNFACTORED`), must give the same answer and cause wherever both answer. Every
/// answer must be exact (boxed: the values of the 729 points; holed: the values in `-W..=W`,
/// or more only with [`Refusal::Repeats`]).
#[test]
fn every_writing_of_a_formula_gets_one_answer() {
    use super::super::UNFACTORED;
    const LOW: u64 = 150_000;
    let seed = crate::seed::seed("every_writing_of_a_formula_gets_one_answer");
    let mut rng = Rng(seed | 1);
    let window = IntervalSet::of(-W, W);
    let (mut differ, mut wrong) = (Vec::new(), Vec::new());
    let (mut forms, mut answered, mut repeats, mut refused) = (0, 0, 0, 0);
    for round in 0..24 {
        // A part `c` shared by both disjuncts, as written, `c && (d || e)`, and taken out by
        // hand, `(c && d) || (c && e)`.
        let (f, syms, want, strides) = if round % 2 == 0 {
            let parts: Vec<Formula> = (0..3).map(|_| formula(&mut rng, 2)).collect();
            let f = boxed(Formula::and(vec![
                parts[0].clone(),
                Formula::or(vec![parts[1].clone(), parts[2].clone()]),
            ]));
            let syms: Vec<Atom> = NAMES.iter().map(|n| a(n)).collect();
            let want: Vec<IntervalSet> = NAMES.iter().map(|n| brute(&f, n)).collect();
            (f, syms, Some(want), Vec::new())
        } else {
            let (f, strides) = holed(&mut rng);
            (f, vec![a("x")], None, strides)
        };
        let spread = match &f {
            Formula::And(gs) => {
                let gs: Vec<Formula> = gs.to_vec();
                let (ors, rest): (Vec<Formula>, Vec<Formula>) =
                    gs.into_iter().partition(|g| matches!(g, Formula::Or(_)));
                match ors.split_first() {
                    Some((Formula::Or(ds), others)) => {
                        let mut shared = rest;
                        shared.extend(others.iter().cloned());
                        Some(Formula::Or(Shared::new(
                            (ds.iter())
                                .map(|d| {
                                    let mut c = shared.clone();
                                    c.push(d.clone());
                                    Formula::And(Shared::new(c))
                                })
                                .collect(),
                        )))
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        let k = rng.int(2, 3);
        let same: Vec<Formula> = vec![
            flipped(&f),
            scaled(&f, k),
            shuffled(&f, &mut rng),
            Formula::And(Shared::new(vec![f.clone(), f.clone()])),
            shuffled(&scaled(&flipped(&f), k), &mut rng),
        ];
        for limit in [None, Some(LOW)] {
            EXACT_LIMIT_SET.set(limit);
            let first = project_each_exact(&f, &syms);
            for g in &same {
                forms += 1;
                let other = project_each_exact(g, &syms);
                if other != first {
                    differ.push(format!(
                        "round {round} limit {limit:?}: {first:?} and {other:?}: {f} and {g}"
                    ));
                }
            }
            let mut others = Vec::new();
            if let Some(g) = &spread {
                others.push((format!("{g}"), project_each_exact(g, &syms)));
            }
            UNFACTORED.with(|u| u.set(true));
            others.push(("unfactored".into(), project_each_exact(&f, &syms)));
            UNFACTORED.with(|u| u.set(false));
            EXACT_LIMIT_SET.set(None);
            for (name, other) in &others {
                forms += 1;
                if let (Ok((a, ca)), Ok((b, cb))) = (&first, other) {
                    for (s, (x, y)) in a.iter().zip(b).enumerate() {
                        if let (Ok(x), Ok(y)) = (x, y)
                            && (x != y
                                || ca.contains(&Refusal::Repeats) != cb.contains(&Refusal::Repeats))
                        {
                            differ.push(format!(
                                    "round {round} limit {limit:?} symbol {s}: {x} {ca:?} and {y} {cb:?}: {f} and {name}"
                                ));
                        }
                    }
                }
            }
            let Ok((sets, causes)) = &first else {
                refused += 1;
                continue;
            };
            for (s, got) in sets.iter().enumerate() {
                let Ok(got) = got else {
                    refused += 1;
                    continue;
                };
                answered += 1;
                let kept = causes.contains(&Refusal::Repeats);
                repeats += usize::from(kept);
                match &want {
                    Some(want) if got != &want[s] => {
                        wrong.push(format!(
                            "round {round} symbol {s}: {got} not {}: {f}",
                            want[s]
                        ));
                    }
                    Some(_) => {}
                    None => {
                        let points = holed_values(&f, &strides);
                        let seen = got.meet(&window);
                        if !points.minus(&seen).is_empty() || (seen != points && !kept) {
                            wrong.push(format!("round {round}: {seen} not {points}: {f}"));
                        }
                    }
                }
            }
        }
    }
    println!(
        "seed {seed}: {forms} writings, {answered} answers, {repeats} with Repeats, {refused} refused"
    );
    assert!(differ.is_empty(), "seed {seed}: {differ:#?}");
    assert!(wrong.is_empty(), "seed {seed}: {wrong:#?}");
}

/// The even integers, written as one equation, as two disjuncts, with a bound split in two
/// and with a residue question's worth of strides, get one set and one cause: every
/// integer, as no finite union of ranges is the even integers, with [`Refusal::Repeats`]
/// wherever that is so, whichever step answers.
#[test]
fn the_even_integers_get_one_answer_in_every_writing() {
    let writings = [
        eq(&[("x", 1), ("y", -2)], 0),
        Formula::or(vec![
            eq(&[("x", 1), ("y", -2)], 0),
            eq(&[("x", 1), ("z", -2)], 0),
        ]),
        Formula::or(vec![
            Formula::and(vec![eq(&[("x", 1), ("y", -2)], 0), ge(&[("x", 1)], 0)]),
            Formula::and(vec![eq(&[("x", 1), ("y", -2)], 0), ge(&[("x", -1)], -1)]),
        ]),
        Formula::or(vec![
            eq(&[("x", 1), ("y", -4)], 0),
            eq(&[("x", 1), ("z", -4)], -2),
        ]),
    ];
    let got: Vec<_> = (writings.iter())
        .map(|f| (format!("{f}"), project_each_exact(f, &[a("x")])))
        .collect();
    for (f, g) in &got {
        assert_eq!(
            g,
            &Ok((vec![Ok(IntervalSet::top())], vec![Refusal::Repeats])),
            "{f}: all {got:#?}"
        );
    }
}

/// The repaired unit of l01_29 `refused_warning::a_unit_with_no_refusal_prints_no_warning`:
/// `w == 0` and four rows in x, y and z.
fn repaired_unit() -> Formula {
    Formula::and(vec![
        eq(&[("w", 1)], 0),
        ge(&[("x", 4), ("w", -12), ("y", -10), ("z", -12)], 11),
        ge(&[("w", 4), ("x", 10), ("y", -10), ("z", -11)], -28),
        ge(&[("w", 11), ("x", 4), ("y", -1), ("z", 12)], -28),
        ge(&[("w", -8), ("x", -5), ("y", 12), ("z", -1)], 31),
    ])
}

/// Every name of the repaired unit has its exact answer, the same by the default in-cell
/// method as by recession rays (`Method::Rays`): `w` is {0} and `x` is [4, +inf). Measured
/// 2026-11-18: the default (`Method::Pugh`) refused `w` and `x` (`Questions`) at the full
/// 3.1M units of work with no question asked, since its cell projected the implicant with
/// every splinter of the dark shadow, though for `w` the line through the point alone,
/// `w == 0`, covers every value. Rays answered `w` in 20k units and `x` in 482k units with 20
/// questions. Fixed by the line first in `cell` (`w`: 13k units) and by the goal of
/// `projection::pugh`, which stops once the values the cell still needs are held (`x`: 180k
/// units, no question, against 4.8M with every splinter; `y` 20k, `z` 20k; row
/// PRES-cover-refusals-where-exact).
#[test]
fn every_name_of_the_repaired_unit_has_its_exact_answer() {
    let f = repaired_unit();
    let exact = |s: &str| {
        let got = project_each_exact(&f, &[a(s)]);
        match got {
            Ok((v, _)) => v.into_iter().next().expect("one set"),
            Err(r) => Err(r),
        }
    };
    for s in ["w", "x", "y", "z"] {
        METHOD.set(Some(Method::Rays));
        let rays = exact(s);
        METHOD.set(None);
        let got = exact(s);
        assert!(got.is_ok(), "{s}: {got:?}");
        assert_eq!(got, rays, "{s}");
    }
    assert_eq!(
        exact("w"),
        Ok(IntervalSet::from_pieces(vec![(End::of(0), End::of(0))]))
    );
    assert_eq!(exact("x"), Ok(IntervalSet::range(End::of(4), End::PosInf)));
}

/// [`reduced`] of `f` keeping `x`, with the limit `limit`.
fn reduce_keeping_x(f: &Formula, limit: u64) -> Result<Option<Formula>, Refusal> {
    let x = a("x");
    let mut work = Work {
        used: 0,
        limit,
        solver: SOLVER,
    };
    reduced(f, &|b| *b == x, &mut work)
}

/// Whether `f` and `g` have a point at the same values of `x` in `-12..=12`, by the solver.
fn same_on_x(f: &Formula, g: &Formula) {
    for v in -12..=12 {
        let at = |h: &Formula| {
            let q = Formula::and(vec![h.clone(), eq(&[("x", 1)], -v)]);
            (SOLVER.satisfiable)(&q).unwrap().is_some()
        };
        assert_eq!(at(f), at(g), "x = {v}: {f:?} and {g:?}");
    }
}

/// A conjunction of rows is left to [`direct`]: `reduced` gives `None`.
#[test]
fn reduced_leaves_a_conjunction_of_rows_alone() {
    let f = Formula::and(vec![
        ge(&[("x", 1)], 0),
        ge(&[("x", -1)], 10),
        eq(&[("y", 1), ("x", -1)], -1),
    ]);
    assert_eq!(reduce_keeping_x(&f, EXACT_LIMIT), Ok(None));
}

/// `0 <= x <= 3`, `y == x + 1`, `z >= x or y <= -3`: `z` is read by the first disjunct
/// alone and has no upper bound, so the disjunction holds at every value of the rest and goes
/// (the rule of module `absorbing`); `y` is then read by no disjunction and is eliminated.
/// What is left reads `x` alone, with the same values of `x`.
#[test]
fn reduced_removes_a_disjunction_its_private_atom_satisfies_and_eliminates_the_rest() {
    let f = Formula::and(vec![
        ge(&[("x", 1)], 0),
        ge(&[("x", -1)], 3),
        eq(&[("y", 1), ("x", -1)], -1),
        Formula::or(vec![ge(&[("z", 1), ("x", -1)], 0), ge(&[("y", -1)], -3)]),
    ]);
    let g = reduce_keeping_x(&f, EXACT_LIMIT)
        .unwrap()
        .expect("a smaller formula");
    assert_eq!(g.atoms(), [a("x")].into_iter().collect(), "{g:?}");
    same_on_x(&f, &g);
}

/// `0 <= x <= 9`, `y == 2x`, `x <= 2 or x >= 7`: the disjunction reads the kept `x`, which is
/// never private, so it stays; `y` goes.
#[test]
fn reduced_keeps_a_disjunction_over_a_kept_atom() {
    let f = Formula::and(vec![
        ge(&[("x", 1)], 0),
        ge(&[("x", -1)], 9),
        eq(&[("y", 1), ("x", -2)], 0),
        Formula::or(vec![ge(&[("x", -1)], 2), ge(&[("x", 1)], -7)]),
    ]);
    let g = reduce_keeping_x(&f, EXACT_LIMIT)
        .unwrap()
        .expect("a smaller formula");
    assert_eq!(g.atoms(), [a("x")].into_iter().collect(), "{g:?}");
    assert!(
        g.conjuncts().iter().any(|h| matches!(h, Formula::Or(_))),
        "{g:?}"
    );
    same_on_x(&f, &g);
}

/// `0 <= x <= 5`, `y == x + 2`, `z == y + 1`, `y <= 3 or y >= 6`: the disjunction reads `y`,
/// which the rows also read, so it stays and `y` is kept for it; `z`, read by the rows alone,
/// goes.
#[test]
fn reduced_keeps_the_atoms_a_remaining_disjunction_reads() {
    let f = Formula::and(vec![
        ge(&[("x", 1)], 0),
        ge(&[("x", -1)], 5),
        eq(&[("y", 1), ("x", -1)], -2),
        eq(&[("z", 1), ("y", -1)], -1),
        Formula::or(vec![ge(&[("y", -1)], 3), ge(&[("y", 1)], -6)]),
    ]);
    let g = reduce_keeping_x(&f, EXACT_LIMIT)
        .unwrap()
        .expect("a smaller formula");
    assert_eq!(g.atoms(), [a("x"), a("y")].into_iter().collect(), "{g:?}");
    same_on_x(&f, &g);
}

/// The elimination is metered: with no work left it is refused, never a smaller formula from
/// a stopped elimination.
#[test]
fn reduced_is_refused_past_the_limit() {
    let f = Formula::and(vec![
        ge(&[("x", 1)], 0),
        ge(&[("x", -1)], 5),
        eq(&[("y", 1), ("x", -1)], -2),
        eq(&[("z", 1), ("y", -1)], -1),
        Formula::or(vec![ge(&[("y", -1)], 3), ge(&[("y", 1)], -6)]),
    ]);
    assert_eq!(reduce_keeping_x(&f, 0), Err(Refusal::Questions));
}

fn read_once_answers(f: &Formula) -> Option<(bool, HashMap<Atom, IntervalSet>)> {
    let mut work = Work {
        used: 0,
        limit: EXACT_LIMIT,
        solver: SOLVER,
    };
    read_once(f, &mut work).expect("within the limit")
}

/// A random formula read once over blocks, or nearly: x, y and z each have a block of one to
/// three rows over that name alone, and the three blocks are joined by a random tree of
/// conjunctions, disjunctions and negations (a negated block parts into several, so some
/// formulas are not read once, and `read_once` must then decline). Each row's solutions reach
/// within 5 of 0, so a value in `-B..=B` with a point has one with every name in the box of
/// `brute_wide`.
fn read_once_formula(rng: &mut Rng) -> Formula {
    let mut blocks: Vec<Formula> = (NAMES.iter())
        .map(|n| {
            let rows: Vec<Formula> = (0..1 + rng.below(3))
                .map(|_| {
                    let c = [1, -1, 2, -2, 3][rng.below(5) as usize];
                    let k = rng.int(-4, 4);
                    if rng.below(4) == 0 {
                        eq(&[(n, c)], k)
                    } else {
                        ge(&[(n, c)], k)
                    }
                })
                .collect();
            Formula::and(rows)
        })
        .collect();
    while blocks.len() > 1 {
        let i = rng.below(blocks.len() as u64) as usize;
        let g = blocks.swap_remove(i);
        let j = rng.below(blocks.len() as u64) as usize;
        let h = blocks.swap_remove(j);
        let mut joined = if rng.below(2) == 0 {
            Formula::and(vec![g, h])
        } else {
            Formula::or(vec![g, h])
        };
        if rng.below(4) == 0 {
            joined = Formula::negate(joined);
        }
        blocks.push(joined);
    }
    blocks.remove(0)
}

/// The values of `sym` in `-B..=B` at the points of `f` with every name in `-W..=W`.
fn brute_wide(f: &Formula, sym: &str) -> IntervalSet {
    const W: i64 = 7;
    let at = NAMES.iter().position(|n| *n == sym).unwrap();
    let mut set = IntervalSet::empty();
    for x in -W..=W {
        for y in -W..=W {
            for z in -W..=W {
                let p = [x, y, z];
                let m: Model = (NAMES.iter().zip(p))
                    .map(|(n, v)| (a(n), Int::from(v)))
                    .collect();
                if p[at].abs() <= B && f.holds(&m) {
                    set = set.join(&IntervalSet::single(p[at]));
                }
            }
        }
    }
    set
}

/// `read_once` answers each name of a formula read once with the values that trying the points
/// gives, read in the box, and whether there is a point; it declines the others. Negative
/// control: with `esc[c] = esc[i]` at a disjunction (no other part with a point lets the
/// symbol take every value), this test fails.
#[test]
fn read_once_formulas_project_to_the_values_of_their_points() {
    let seed = crate::seed::seed("read_once_formulas_project_to_the_values_of_their_points");
    let mut rng = Rng(seed | 1);
    let (mut answered, mut wrong) = (0, Vec::new());
    for round in 0..400 {
        let f = read_once_formula(&mut rng);
        let Some((has, sets)) = read_once_answers(&f) else {
            continue;
        };
        answered += 1;
        let mut any = false;
        for n in NAMES {
            let want = brute_wide(&f, n);
            any |= !want.is_empty();
            let got = sets
                .get(&a(n))
                .cloned()
                .unwrap_or_else(|| match has {
                    true => IntervalSet::range(End::NegInf, End::PosInf),
                    false => IntervalSet::empty(),
                })
                .meet(&IntervalSet::of(-B, B));
            if got != want {
                wrong.push(format!("round {round} {n}: {got} not {want}: {f}"));
            }
        }
        if has != any {
            wrong.push(format!("round {round}: has {has} not {any}: {f}"));
        }
    }
    println!("seed {seed}: {answered} of 400 answered");
    assert!(wrong.is_empty(), "seed {seed}: {wrong:#?}");
    assert!(answered >= 100, "seed {seed}: only {answered} answered");
}

/// The else arm of a chain of accounts, `x0 <= -1 and not (x0 >= 0 or (y0 >= 0 and x1 >= 1))`:
/// the rows on `x0` meet in one block once the conjunctions are taken in, so `read_once`
/// answers every name, `x0 <= -1` and `y0`, `x1` free
/// (`deep_condition::bench::arms_of_a_chain_of_accounts_take_time_near_linear_in_its_depth`).
#[test]
fn the_else_arm_of_a_chain_of_accounts_is_read_once() {
    let inner = Formula::and(vec![ge(&[("y0", 1)], 0), ge(&[("x1", 1)], -1)]);
    let f = Formula::and(vec![
        ge(&[("x0", -1)], -1),
        Formula::negate(Formula::or(vec![ge(&[("x0", 1)], 0), inner])),
    ]);
    let (has, sets) = read_once_answers(&f).expect("read once");
    assert!(has);
    assert_eq!(sets[&a("x0")], IntervalSet::range(End::NegInf, End::of(-1)));
    for n in ["y0", "x1"] {
        assert_eq!(
            sets[&a(n)],
            IntervalSet::range(End::NegInf, End::PosInf),
            "{n}"
        );
    }
}

/// `(x == 0 and y == 0) or (x == 0 and z == 0)` reads `x` in two blocks, the two parts of a
/// disjunction: `read_once` answers `x` in {0}, the union of the blocks' projections, and `y`,
/// `z` free, as each has an arm with a point that does not read it (Sol, rounds 1 and 2 of
/// XR-cover-hybrid).
#[test]
fn an_atom_in_both_arms_of_a_disjunction_is_answered() {
    let f = Formula::or(vec![
        Formula::and(vec![eq(&[("x", 1)], 0), eq(&[("y", 1)], 0)]),
        Formula::and(vec![eq(&[("x", 1)], 0), eq(&[("z", 1)], 0)]),
    ]);
    let (has, sets) = read_once_answers(&f).expect("decomposable");
    assert!(has);
    assert_eq!(sets[&a("x")], IntervalSet::single(0));
    for n in ["y", "z"] {
        assert_eq!(
            sets[&a(n)],
            IntervalSet::range(End::NegInf, End::PosInf),
            "{n}"
        );
        assert_eq!(project(&f, n), sets[&a(n)], "{n}");
    }
}

/// `(x >= 0 or y >= 0) and x + z <= 5` has two non-unary parts of a conjunction reading `x`:
/// `read_once` declines, while unary `x <= 5` above `x >= 0 or y >= 0` is answered by the
/// cumulative ancestor box as `(-inf, 5]`.
#[test]
fn an_atom_in_two_parts_of_a_conjunction_is_declined() {
    let boxed = Formula::and(vec![
        Formula::or(vec![ge(&[("x", 1)], 0), ge(&[("y", 1)], 0)]),
        ge(&[("x", -1)], 5),
    ]);
    let (has, sets) = read_once_answers(&boxed).expect("unary ancestor box answered");
    assert!(has);
    assert_eq!(sets[&a("x")], IntervalSet::range(End::NegInf, End::of(5)));
    assert_eq!(sets[&a("y")], IntervalSet::top());

    let f = Formula::and(vec![
        Formula::or(vec![ge(&[("x", 1)], 0), ge(&[("y", 1)], 0)]),
        ge(&[("x", -1), ("z", -1)], 5),
    ]);
    assert!(read_once_answers(&f).is_none());
}

/// The shape of `wide_pairs` with a box: `-5 <= z_j <= 5` and either `z_j + z_(j+1) >= 0` for
/// every `j` or `z_j - z_(j+1) >= 0` for every `j`, the box in each arm. Each arm is one block, a
/// path of rows over two atoms (`forest`), and each atom is read by both arms: every `z_j` takes
/// `-5..=5`, and in the arm with `+`, `z_0 + z_1 >= 0` with `z_1 <= 5` gives `z_0 >= -5`.
#[test]
fn the_arms_of_wide_pairs_are_paths_read_at_once() {
    let names = ["x", "y", "z"];
    let arm = |s: i64| {
        let mut rows: Vec<Formula> = names
            .iter()
            .flat_map(|n| [ge(&[(n, 1)], 5), ge(&[(n, -1)], 5)])
            .collect();
        rows.extend(names.windows(2).map(|w| ge(&[(w[0], 1), (w[1], s)], 0)));
        Formula::and(rows)
    };
    let f = Formula::or(vec![arm(1), arm(-1)]);
    let (has, sets) = read_once_answers(&f).expect("decomposable");
    assert!(has);
    for n in names {
        assert_eq!(sets[&a(n)], IntervalSet::of(-5, 5), "{n}");
    }
    // One arm alone, `+` with `z <= -3`: `y >= 3`, so `x >= -5` meets `x + y >= 0` anywhere in
    // the box, and `y <= 5`.
    let mut rows = vec![ge(&[("z", -1)], -3)];
    rows.extend(
        names
            .iter()
            .flat_map(|n| [ge(&[(n, 1)], 5), ge(&[(n, -1)], 5)]),
    );
    rows.extend(names.windows(2).map(|w| ge(&[(w[0], 1), (w[1], 1)], 0)));
    let g = Formula::and(rows);
    let (has, sets) = read_once_answers(&g).expect("one block");
    assert!(has);
    assert_eq!(sets[&a("x")], IntervalSet::of(-5, 5));
    assert_eq!(sets[&a("y")], IntervalSet::of(3, 5));
    assert_eq!(sets[&a("z")], IntervalSet::of(-5, -3));
}

/// A random decomposable formula over x, y and z: a disjunction of two such formulas over the
/// same names, a conjunction of two over names parted in two, or a block of one to three rows
/// over one or two of its names, each name of the block held in `-W..=W` by rows of its own.
/// Each name a block reads is in the box there, so a value of a name with a point has one with
/// every name in the box (the names no chosen block reads at 0).
fn decomposable_formula(rng: &mut Rng, names: &[&str], depth: u32) -> Formula {
    const W: i64 = B;
    let pick = rng.below(4);
    if depth > 0 && pick == 0 {
        return Formula::or(vec![
            decomposable_formula(rng, names, depth - 1),
            decomposable_formula(rng, names, depth - 1),
        ]);
    }
    if depth > 0 && pick == 1 && names.len() > 1 {
        let cut = 1 + rng.below(names.len() as u64 - 1) as usize;
        return Formula::and(vec![
            decomposable_formula(rng, &names[..cut], depth - 1),
            decomposable_formula(rng, &names[cut..], depth - 1),
        ]);
    }
    let read: Vec<&str> = if names.len() > 1 && rng.below(2) == 0 {
        let i = rng.below(names.len() as u64) as usize;
        let j = (i + 1 + rng.below(names.len() as u64 - 1) as usize) % names.len();
        vec![names[i], names[j]]
    } else {
        vec![names[rng.below(names.len() as u64) as usize]]
    };
    let mut rows: Vec<Formula> = (read.iter())
        .flat_map(|n| [ge(&[(n, 1)], W), ge(&[(n, -1)], W)])
        .collect();
    for _ in 0..1 + rng.below(3) {
        let c = |rng: &mut Rng| [1, -1, 2, -2, 3][rng.below(5) as usize];
        let k = rng.int(-4, 4);
        let terms: Vec<(&str, i64)> = if read.len() == 2 && rng.below(2) == 0 {
            vec![(read[0], c(rng)), (read[1], c(rng))]
        } else {
            vec![(read[rng.below(read.len() as u64) as usize], c(rng))]
        };
        rows.push(if rng.below(5) == 0 {
            eq(&terms, k)
        } else {
            ge(&terms, k)
        });
    }
    Formula::and(rows)
}

/// `read_once` answers each name of a random decomposable formula with the values that trying
/// the points in the box gives, and whether there is a point; blocks with two rows over the same
/// two names, or an equation over two, take the elimination of each name instead of `forest`.
/// Negative controls: with the parting disjunctions not checked (`escaped |= ctx[x] && live[x] > reading`
/// removed), or with `forest`'s message from a parent leaving out its own rows, this test fails.
#[test]
fn decomposable_formulas_project_to_the_values_of_their_points() {
    let seed = crate::seed::seed("decomposable_formulas_project_to_the_values_of_their_points");
    let mut rng = Rng(seed | 1);
    let (mut answered, mut wrong, mut declined) = (0, Vec::new(), Vec::new());
    for round in 0..300 {
        let f = decomposable_formula(&mut rng, &NAMES, 3);
        let Some((has, sets)) = read_once_answers(&f) else {
            declined.push(format!("round {round}: {f}"));
            continue;
        };
        answered += 1;
        let mut any = false;
        for n in NAMES {
            let want = brute_wide(&f, n);
            any |= !want.is_empty();
            let got = sets
                .get(&a(n))
                .cloned()
                .unwrap_or_else(|| match has {
                    true => IntervalSet::range(End::NegInf, End::PosInf),
                    false => IntervalSet::empty(),
                })
                .meet(&IntervalSet::of(-B, B));
            if got != want {
                wrong.push(format!("round {round} {n}: {got} not {want}: {f}"));
            }
        }
        if has != any {
            wrong.push(format!("round {round}: has {has} not {any}: {f}"));
        }
    }
    println!("seed {seed}: {answered} of 300 answered, declined: {declined:#?}");
    assert!(wrong.is_empty(), "seed {seed}: {wrong:#?}");
    assert!(answered >= 200, "seed {seed}: only {answered} answered");
}

/// PRES-cover-refusals-moduli, [`super::cut_at_shared`]: the emptiness question of
/// `has_points` (`direct` on a symbol that occurs nowhere) on the shape the l01_25 moduli cases
/// declined, rows `x == 5 z + y`, `0 <= y <= 4` tying `x` to its remainder `y`, a disjunction
/// over `x` alone and one over `x` and `y`, in the box, random on fixed seeds. Every case is
/// answered, none declined (before the cut each was, its two disjunctions tied by `x`), and the
/// answer is empty exactly where trying every point finds none.
#[test]
fn two_disjunctions_tied_by_one_atom_get_their_emptiness_answered() {
    let none = Atom::Sym("#none".into());
    let (mut wrong, mut declined, mut empty) = (Vec::new(), 0, 0);
    for seed in [1u64, 126, 4_242, 99_991] {
        let mut rng = Rng(seed);
        for round in 0..50 {
            let over_x = |rng: &mut Rng| {
                let c = if rng.below(2) == 0 { 1 } else { -1 };
                ge(&[("x", c)], rng.int(-4, 4))
            };
            let over_xy = |rng: &mut Rng| {
                let b = Formula::and(vec![
                    ge(
                        &[("x", rng.int(-3, 3)), ("y", rng.int(-3, 3))],
                        rng.int(-4, 4),
                    ),
                    eq(&[("y", 1)], -rng.int(0, 4)),
                ]);
                Formula::and(vec![b, over_x(rng)])
            };
            let n = 2 + rng.below(2) as usize;
            let xs = Formula::or(
                (0..n)
                    .map(|_| Formula::and(vec![over_x(&mut rng), over_x(&mut rng)]))
                    .collect(),
            );
            let xys = Formula::or((0..n).map(|_| over_xy(&mut rng)).collect());
            let f = boxed(Formula::and(vec![
                eq(&[("x", 1), ("z", -5), ("y", -1)], 0),
                ge(&[("y", 1)], 0),
                ge(&[("y", -1)], 4),
                xs,
                xys,
            ]));
            let has = !brute(&f, "x").is_empty();
            empty += usize::from(!has);
            let mut fast = u64::MAX;
            let got = tried(&mut fast, SOLVER, |w| {
                direct(&f, &none, &IntervalSet::top(), w)
            });
            match got {
                None => declined += 1,
                Some(set) if set.is_empty() == has => wrong.push(format!(
                    "seed {seed} round {round}: {set:?}, points {has}: {f}"
                )),
                Some(_) => {}
            }
        }
    }
    println!("{empty} of 200 empty, {declined} declined");
    assert!(wrong.is_empty(), "{wrong:#?}");
    assert_eq!(declined, 0);
    assert!(empty > 0 && empty < 200, "{empty} of 200 empty");
}

/// `x == 2a + b` with `b == 1` and x in `-bound..=bound`, the odd values of the range.
fn odd_x(bound: i64) -> Formula {
    Formula::and(vec![
        eq(&[("x", 1), ("a", -2), ("b", -1)], 0),
        ge(&[("b", 1)], 0),
        ge(&[("b", -1)], 1),
        eq(&[("b", 1)], -1),
        ge(&[("x", 1)], bound),
        ge(&[("x", -1)], bound),
    ])
}

/// [`block_set`] with `list` (as [`cut_at_shared`] reads it) answers a stride as its range met
/// with its class, a few pieces whatever the bound, not one piece per value
/// (PRES-interval-strided-piece): the odd values of `-bound..=bound` are the range from the
/// first odd value to the last, met with 1 mod 2. [`direct`] declines the stride
/// (PRES-direct-stride-answer-downstream: its answer, one disjunct per value in the preimage
/// stage's check, made `l01_25` `bench::s22::remainder_chains_in_the_linear_stage_scale` run
/// past 60 s), and the public answer is still the odd values.
#[test]
fn a_stride_is_answered_as_its_range_and_class() {
    let mut pieces = Vec::new();
    for bound in [101, 808] {
        let f = odd_x(bound);
        let Formula::And(rows) = &f else {
            panic!("odd_x is a conjunction")
        };
        let rows: Vec<Con> = rows
            .iter()
            .map(|r| match r {
                Formula::Con(c) => c.clone(),
                other => panic!("odd_x holds rows only: {other:?}"),
            })
            .collect();
        let mut work = Work {
            used: 0,
            limit: super::super::meter::EXACT_LIMIT,
            solver: SOLVER,
        };
        let got = block_set(&rows, &a("x"), &IntervalSet::top(), true, &mut work)
            .unwrap()
            .expect("with `list`, the stride is answered");
        assert_eq!(
            got.class,
            Congruence::new(Num::from(2), Num::from(1)),
            "{got:?}"
        );
        let odd = if bound % 2 == 1 { bound } else { bound - 1 };
        assert_eq!(got.ranges, IntervalSet::of(-odd, odd), "{got:?}");
        assert_eq!(got.met(), brute_odd(bound));
        pieces.push(got.ranges.len());
        let mut work = Work {
            used: 0,
            limit: super::super::meter::EXACT_LIMIT,
            solver: SOLVER,
        };
        let declined = direct(&f, &a("x"), &IntervalSet::top(), &mut work).unwrap();
        assert_eq!(declined, None, "direct declines the stride");
        assert_eq!(project(&f, "x"), brute_odd(bound));
    }
    assert_eq!(pieces, vec![1, 1]);
}

fn brute_odd(bound: i64) -> IntervalSet {
    IntervalSet::from_pieces(
        (-bound..=bound)
            .filter(|v| v.rem_euclid(2) == 1)
            .map(|v| (End::of(v), End::of(v)))
            .collect(),
    )
}

/// [`Classed::minus`], [`Classed::count`] and [`Classed::listed_len`] agree with the listed
/// sets ([`Classed::met`]) on every set of up to two ranges in `-6..=6` with a modulus up to
/// 4, taken from every other such set: the difference, exact, in each case the projection's
/// `Held::push` meets (a class less another, a range less a class) and the listed fallback.
#[test]
fn classed_differences_and_counts_agree_with_the_listed_sets() {
    let mut sets = Vec::new();
    let ranges = [
        IntervalSet::empty(),
        IntervalSet::of(-6, 6),
        IntervalSet::of(-3, 2),
        IntervalSet::from_pieces(vec![(End::of(-6), End::of(-2)), (End::of(1), End::of(5))]),
        IntervalSet::of(4, 4),
    ];
    for r in &ranges {
        for m in 1..=4i64 {
            for a in 0..m {
                sets.push(Classed::new(
                    r.clone(),
                    Congruence::new(Num::from(m), Num::from(a)),
                ));
            }
        }
    }
    for x in &sets {
        let listed = x.met();
        let values: Vec<i64> = (-7..=7).filter(|v| listed.contains(*v)).collect();
        assert_eq!(x.count(), values.len() as u64, "{x:?}");
        assert_eq!(x.listed_len(), listed.len() as u64, "{x:?}");
        for y in &sets {
            let got = x.minus(y);
            assert_eq!(got.met(), listed.minus(&y.met()), "{x:?} minus {y:?}");
            // In the one form: the class found again from the listed values.
            assert_eq!(got, Classed::plain(got.met()), "{got:?}");
        }
    }
}

/// A named formula and the values each of its atoms takes.
type Case<'a> = (&'a str, Formula, Vec<(&'a str, IntervalSet)>);

/// The counterexamples to pushing a conjunction's unary rows down into its parts (Gemini, round 2
/// of XR-cover-hybrid: CE1, CE1b, CE2, CE3) and three fixtures of Sol's from the same round, each
/// with the values every atom takes. The exact projection gives them, and `read_once`, when it
/// answers, gives the same; a push-down that escapes past an ancestor's box answers every value.
#[test]
fn pushed_down_boxes_do_not_escape_their_ancestors() {
    let all = IntervalSet::range(End::NegInf, End::PosInf);
    let none = IntervalSet::empty();
    let box5 = || Formula::and(vec![ge(&[("s", 1)], 5), ge(&[("s", -1)], 5)]);
    let s_or_y = || Formula::or(vec![ge(&[("s", 1)], 0), ge(&[("y", 1)], 0)]);
    let ce1 = Formula::and(vec![box5(), s_or_y()]);
    let ce1b = Formula::or(vec![
        Formula::and(vec![box5(), s_or_y()]),
        eq(&[("s", 1)], -10),
    ]);
    let ce2 = Formula::and(vec![
        ge(&[("s", 1)], 5),
        ge(&[("s", -1)], 2),
        Formula::or(vec![
            Formula::and(vec![ge(&[("s", 1)], -4), ge(&[("s", -1)], 6), s_or_y()]),
            Formula::and(vec![eq(&[("z", 1)], -1), eq(&[("z", 1)], -2)]),
        ]),
    ]);
    let ce3 = Formula::and(vec![
        box5(),
        eq(&[("s", 1), ("w", -2)], 0),
        Formula::or(vec![eq(&[("s", 1)], -1), eq(&[("s", 1)], -2)]),
    ]);
    let sol1 = Formula::and(vec![
        Formula::or(vec![eq(&[("s", 1)], 0), eq(&[("t", 1)], 0)]),
        Formula::and(vec![eq(&[("u", 1)], 0), eq(&[("u", 1)], -1)]),
    ]);
    let sol2 = Formula::and(vec![
        eq(&[("s", 1)], 0),
        Formula::or(vec![
            eq(&[("t", 1)], 0),
            Formula::and(vec![
                ge(&[("s", 1)], -1),
                Formula::or(vec![eq(&[("s", 1)], -2), eq(&[("u", 1)], 0)]),
            ]),
        ]),
    ]);
    let sol3 = Formula::or(vec![
        Formula::and(vec![eq(&[("s", 1)], 0), eq(&[("t", 1)], 0)]),
        Formula::and(vec![eq(&[("s", 1)], -2), eq(&[("u", 1)], 0)]),
    ]);
    let five = IntervalSet::of(-5, 5);
    let cases: Vec<Case> = vec![
        ("CE1", ce1, vec![("s", five.clone()), ("y", all.clone())]),
        (
            "CE1b",
            ce1b,
            vec![
                (
                    "s",
                    IntervalSet::from_pieces(vec![
                        (End::of(-5), End::of(5)),
                        (End::of(10), End::of(10)),
                    ]),
                ),
                ("y", all.clone()),
            ],
        ),
        (
            "CE2",
            ce2,
            vec![
                ("s", none.clone()),
                ("y", none.clone()),
                ("z", none.clone()),
            ],
        ),
        (
            "CE3",
            ce3,
            vec![("s", IntervalSet::single(2)), ("w", IntervalSet::single(1))],
        ),
        (
            "sol1",
            sol1,
            vec![
                ("s", none.clone()),
                ("t", none.clone()),
                ("u", none.clone()),
            ],
        ),
        (
            "sol2",
            sol2,
            vec![
                ("s", IntervalSet::single(0)),
                ("t", IntervalSet::single(0)),
                ("u", all.clone()),
            ],
        ),
        (
            "sol3",
            sol3,
            vec![
                (
                    "s",
                    IntervalSet::from_pieces(vec![
                        (End::of(0), End::of(0)),
                        (End::of(2), End::of(2)),
                    ]),
                ),
                ("t", all.clone()),
                ("u", all.clone()),
            ],
        ),
    ];
    for (name, f, want) in cases {
        let once = read_once_answers(&f);
        for (n, set) in want {
            assert_eq!(project(&f, n), set, "{name} {n}");
            if let Some((has, sets)) = &once {
                let got = if *has {
                    sets[&a(n)].clone()
                } else {
                    none.clone()
                };
                assert_eq!(got, set, "{name} {n} read_once");
            }
        }
    }
}

/// The work of one call asking every atom of a conjunction of n separate groups grows with n,
/// not n^2 (PRES-cover-bench-disjoint-reduced, PRES-cover-bench-many-calls): each group is a
/// cycle `x_i >= y_i >= z_i >= x_i - 1` in `0..=9`, which `forest` declines, so before each
/// atom's projection eliminated the rows of all n groups. Counted in [`EXACT_WORK`], so the
/// load of the machine plays no part; the answers are checked as well. Run at a limit of
/// 100,000, which one reading of the part passes from 16 groups on, each symbol's cover well
/// within it: before, the reading had the limit once for the whole part, so it declined and
/// each symbol was covered over the whole part again (`exact_each`, the allowance of `once`), as
/// `disjoint::bench` did past 213 groups at the limit of 3,100,000.
#[test]
fn the_work_of_one_call_on_separate_groups_grows_linearly() {
    let work = |n: usize| {
        let mut rows = Vec::new();
        let mut syms = Vec::new();
        for i in 0..n {
            let (x, y, z) = (format!("x{i}"), format!("y{i}"), format!("z{i}"));
            rows.push(ge(&[(x.as_str(), 1), (y.as_str(), -1)], 0));
            rows.push(ge(&[(y.as_str(), 1), (z.as_str(), -1)], 0));
            rows.push(ge(&[(z.as_str(), 1), (x.as_str(), -1)], 1));
            for s in [&x, &y, &z] {
                rows.push(ge(&[(s.as_str(), 1)], 0));
                rows.push(ge(&[(s.as_str(), -1)], 9));
                syms.push(a(s));
            }
        }
        // Two arms, the second with each atom also at most 4, so the groups meet in one
        // part (`split` keeps them together) and each arm is one conjunction of n groups.
        let narrow: Vec<Formula> = (syms.iter())
            .map(|s| member(s, &IntervalSet::of(0, 4)))
            .chain(rows.iter().cloned())
            .collect();
        let f = Formula::or(vec![Formula::and(rows), Formula::and(narrow)]);
        EXACT_WORK.set(0);
        let (got, _) = project_each_exact(&f, &syms).unwrap();
        for g in got {
            assert_eq!(g.unwrap(), IntervalSet::of(0, 9));
        }
        EXACT_WORK.replace(0)
    };
    EXACT_LIMIT_SET.set(Some(100_000));
    let (small, large) = (work(16), work(128));
    EXACT_LIMIT_SET.set(None);
    println!("work at 16 groups: {small}, at 128: {large}");
    assert!(
        large <= 9 * small,
        "work {small} at 16 groups, {large} at 128"
    );
}

/// The reading and the fast paths of one call never spend more than the fast paths of its
/// symbols' covers could, k times the limit for k symbols asked of a part, where `read_once`
/// gives up late (PRES-cover-bench-disjoint-reduced, the condition on zed-impl 90cac8417): the
/// formula of `the_work_of_one_call_on_separate_groups_grows_linearly` at 16 groups, 48
/// symbols, under a limit so low that the reading passes its allowance of 48 limits. Each
/// symbol's fast path (`direct`) then has only what the reading left of that symbol's limit,
/// here nothing, so the fast work of the call less `reduced`'s (one limit for the call, outside
/// the symbols', as `has_points`'s is) is the reading's. Each loop keeps a limit of its own.
/// Before, each fast path started again with a whole limit: 101,700 units against 48,900.
#[test]
fn a_reading_that_gives_up_late_leaves_the_covers_only_what_is_left() {
    const LIMIT: u64 = 1_000;
    let n = 16;
    let mut rows = Vec::new();
    let mut syms = Vec::new();
    for i in 0..n {
        let (x, y, z) = (format!("x{i}"), format!("y{i}"), format!("z{i}"));
        rows.push(ge(&[(x.as_str(), 1), (y.as_str(), -1)], 0));
        rows.push(ge(&[(y.as_str(), 1), (z.as_str(), -1)], 0));
        rows.push(ge(&[(z.as_str(), 1), (x.as_str(), -1)], 1));
        for s in [&x, &y, &z] {
            rows.push(ge(&[(s.as_str(), 1)], 0));
            rows.push(ge(&[(s.as_str(), -1)], 9));
            syms.push(a(s));
        }
    }
    let narrow: Vec<Formula> = (syms.iter())
        .map(|s| member(s, &IntervalSet::of(0, 4)))
        .chain(rows.iter().cloned())
        .collect();
    let f = Formula::or(vec![Formula::and(rows), Formula::and(narrow)]);
    let k = syms.len() as u64;
    let allowed = k * LIMIT;
    // The reading alone, with the allowance `exact_each` gives it: it declines past it.
    EXACT_WORK.set(0);
    let read = tried(&mut { allowed }, SOLVER, |w| read_once(&f, w));
    let pass = EXACT_WORK.replace(0);
    assert!(read.is_none(), "the reading answered within {allowed}");
    // `reduced`, run once for the call with an allowance of one limit.
    let kept: HashSet<&Atom> = syms.iter().collect();
    tried(&mut { LIMIT }, SOLVER, |w| {
        reduced(&f, &|s| kept.contains(s), w)
    });
    let reduce = EXACT_WORK.replace(0);
    // The certificates' preparation of the part, which declines (48 atoms, no definition), then
    // the reading on what it leaves of the allowance, as `exact_each` runs them.
    let mut left = allowed;
    let prepared = tried(&mut left, SOLVER, |w| guarded::prepare(&f, w)).is_some();
    let prep = allowed - left;
    EXACT_WORK.set(0);
    let read_left = tried(&mut left, SOLVER, |w| read_once(&f, w));
    let read_after = EXACT_WORK.replace(0);
    assert!(
        !prepared && prep > 0 && read_left.is_none() && left == 0,
        "prepared {prepared} with {prep}; the reading on the rest answered or left {left}"
    );
    EXACT_LIMIT_SET.set(Some(LIMIT));
    FAST_WORK.set(0);
    let found = (vec![Ok(IntervalSet::of(0, 9)); syms.len()], vec![]);
    let got = exact_each(&f, &syms, found, SOLVER);
    EXACT_LIMIT_SET.set(None);
    let total = EXACT_WORK.replace(0);
    let fast = FAST_WORK.replace(0) - reduce;
    let loops = total - reduce - fast;
    println!(
        "k = {k}, k * limit = {allowed}; reading alone {pass}, reduced {reduce}; in the call: \
         fast paths less reduced {fast}, loops {loops}, all {total}"
    );
    // Late: the reading passed its whole allowance, by its one stopping charge.
    assert!(
        pass > allowed,
        "the reading stopped at {pass}, before {allowed}"
    );
    // The fast paths of the covers (`direct`) have nothing left after it, so the fast work of
    // the symbols is the certificates' preparation, which runs first on the same allowance
    // (`exact_each`), and the reading on the rest: k limits and the one charge that passed
    // them, here the reading's, larger on the smaller rest (it stops within a bulk charge).
    assert_eq!(
        fast,
        prep + read_after,
        "the fast work passes the preparation's {prep} and the reading's {read_after} \
         (k * limit = {allowed})"
    );
    // Each loop has a limit of its own, as with no reading: at most two meters a symbol (over
    // the reduced formula, then the part), each passing its limit by one stopping charge.
    for g in got.sets {
        assert!(
            matches!(g, Err(Refusal::Questions)) || g == Ok(Classed::plain(IntervalSet::of(0, 9))),
            "{g:?}"
        );
    }
}

/// The counter of `l01_38_omega_test::repair::guards`, written with this module's helpers and
/// names chosen by `name` (for `i`, `m` and `t(j)`): `t(0) == m`, and `t(j)` is `t(j-1)` where
/// `i >= j`, else `t(j-1) + 1`, for `j` in `1..=k`; `i` in `[-w, w]`, `m` in `[-w, w]` where
/// `bounded`; `t(k) >= 0` where `meet`, else `t(k) <= -1`.
fn guards_named(
    k: i64,
    w: i64,
    meet: bool,
    bounded: bool,
    name: &dyn Fn(&str, i64) -> String,
) -> Formula {
    let (i, m) = (name("i", 0), name("m", 0));
    let t = |j: i64| name("t", j);
    let mut fs = vec![
        ge(&[(i.as_str(), 1)], w),
        ge(&[(i.as_str(), -1)], w),
        eq(&[(t(0).as_str(), 1), (m.as_str(), -1)], 0),
    ];
    if bounded {
        fs.push(ge(&[(m.as_str(), 1)], w));
        fs.push(ge(&[(m.as_str(), -1)], w));
    }
    for j in 1..=k {
        let (tj, tp) = (t(j), t(j - 1));
        fs.push(Formula::or(vec![
            Formula::and(vec![
                ge(&[(i.as_str(), 1)], -j),
                eq(&[(tj.as_str(), 1), (tp.as_str(), -1)], 0),
            ]),
            Formula::and(vec![
                ge(&[(i.as_str(), -1)], j - 1),
                eq(&[(tj.as_str(), 1), (tp.as_str(), -1)], -1),
            ]),
        ]));
    }
    let tk = t(k);
    fs.push(if meet {
        ge(&[(tk.as_str(), 1)], 0)
    } else {
        ge(&[(tk.as_str(), -1)], -1)
    });
    Formula::and(fs)
}

fn guards_f(k: i64, w: i64, meet: bool, bounded: bool) -> Formula {
    guards_named(k, w, meet, bounded, &|s, j| {
        if s == "t" {
            format!("t{j}")
        } else {
            s.to_string()
        }
    })
}

/// The values of `i` of [`guards_named`], by trying every `i` and `m` (with `m` from
/// `-(k + 1)` to `k + 1` where it is unbounded, wide enough: `t(k)` is `m` plus 0 to `k`, so
/// `m == -(k + 1)` gives `t(k) <= -1` and `m == 0` gives `t(k) >= 0`).
fn guards_brute(k: i64, w: i64, meet: bool, bounded: bool) -> IntervalSet {
    let r = if bounded { w } else { k + 1 };
    let mut set = IntervalSet::empty();
    for i in -w..=w {
        if (-r..=r).any(|m| {
            let t = m + (1..=k).filter(|&j| i < j).count() as i64;
            (t >= 0) == meet
        }) {
            set = set.join(&IntervalSet::single(i));
        }
    }
    set
}

/// The projection of [`guards_f`] onto `i` with the forward certificate and without it, with
/// the questions each asks: (answer, questions).
#[expect(
    clippy::type_complexity,
    reason = "two runs of one projection, compared in place"
)]
fn guards_both(
    f: &Formula,
) -> (
    (Result<IntervalSet, Refusal>, u64),
    (Result<IntervalSet, Refusal>, u64),
) {
    let run = |off: bool| {
        GUARDED_OFF.set(off);
        EXACT_QUESTIONS.set(0);
        let got = project_each_exact(f, &[a("i")]).unwrap().0.remove(0);
        GUARDED_OFF.set(false);
        (got, EXACT_QUESTIONS.replace(0))
    };
    (run(false), run(true))
}

/// PRES-cover-bench-guards-beyond: the counter below zero, at the benchmark's sizes `k = 16`
/// and `k = 128` on inputs `3k/4` wide, projects onto `i` as `k/4 + 1 ..= 3k/4` with no
/// question: the forward certificate pins `m` and reads every `t(j)` from it. Without it the
/// cover asks one question for each value of `i`, and at `k = 128` passes the work limit (the
/// red case of the row).
#[test]
fn guards_beyond_the_inputs_are_certified_without_questions() {
    for k in [16, 128] {
        let w = 3 * k / 4;
        let f = guards_f(k, w, false, true);
        let want = IntervalSet::of(k / 4 + 1, w);
        let ((got, asked), (old, old_asked)) = guards_both(&f);
        assert_eq!(got, Ok(want.clone()), "k {k}");
        assert_eq!(asked, 0, "k {k}: {asked} questions");
        assert!(
            old_asked > 0,
            "k {k}: the certificate's case was not reached"
        );
        if k == 16 {
            assert_eq!(old, Ok(want), "k {k}, without the certificate");
        } else {
            assert_eq!(
                old,
                Err(Refusal::Questions),
                "k {k}, without the certificate"
            );
        }
    }
}

/// The counter on both sides, small sizes, bounded and unbounded `m`: with the certificate
/// the answer is the values of `i` found by trying every point, as without it.
#[test]
fn guards_on_both_sides_agree_with_their_points() {
    for k in 1..=9 {
        for w in 0..=4 {
            for meet in [false, true] {
                for bounded in [false, true] {
                    let f = guards_f(k, w, meet, bounded);
                    let want = guards_brute(k, w, meet, bounded);
                    let ((got, _), (old, _)) = guards_both(&f);
                    let at = format!("k {k} w {w} meet {meet} bounded {bounded}");
                    assert_eq!(got, Ok(want.clone()), "{at}");
                    assert_eq!(old, Ok(want), "{at}, without the certificate");
                }
            }
        }
    }
}

/// The certificate does not depend on the names or the order of the parts: the counter with
/// its atoms renamed (so that another atom of the chain is the least, and the pin) and its
/// conjuncts shuffled is certified alike, with no question.
#[test]
fn guards_renamed_and_shuffled_are_certified_alike() {
    let mut rng = Rng(crate::seed::seed(
        "guards_renamed_and_shuffled_are_certified_alike",
    ));
    type Name<'a> = &'a dyn Fn(&str, i64) -> String;
    let names: [Name; 3] = [
        &|s, j| {
            if s == "t" {
                format!("a{j}")
            } else {
                s.to_string()
            }
        },
        &|s, j| match s {
            "t" => format!("z{}", 99 - j),
            "m" => "zz".to_string(),
            _ => "i".to_string(),
        },
        &|s, j| match s {
            "t" => format!("t{j}"),
            "m" => "b".to_string(),
            _ => "i".to_string(),
        },
    ];
    for name in names {
        let f = shuffled(&guards_named(16, 12, false, true, name), &mut rng);
        let ((got, asked), _) = guards_both(&f);
        assert_eq!(got, Ok(IntervalSet::of(5, 12)));
        assert_eq!(asked, 0);
    }
}

/// A certificate that declines late leaves the reading and the fast paths only what is left of
/// the symbol's limit (`exact_each`): the counter at k = 16 given the set `[4, 12]`, one value
/// wider than its projection, so the certificate reads the whole chain and declines at the
/// piece. With the limit between the certificate's work and that plus the reading's, the fast
/// work of the call (less `reduced`'s, outside the symbol's limit) is the certificate's and the
/// reading's on what it left, within the limit but for the reading's one stopping charge.
/// Negative control: the certificate's work and the fast work with it off pass that, so the
/// reading had the whole limit there and would pass the limit had nothing been taken.
#[test]
fn a_certificate_that_declines_late_leaves_the_rest_only_what_is_left() {
    late_decline(|spent, read| spent + read / 2);
}

/// As above, with the certificate taking more than 90% of the limit (the limit is its work
/// times 20/19): the reading and the fast paths get only the last 5%, so the fast work of the
/// call after the certificate is exactly the reading's when run alone on that remainder (which
/// passes the remainder only by the reading's one stopping charge: 100 units on 51). Negative
/// control: with the certificate off, the reading takes more than ten times that.
#[test]
fn a_certificate_that_declines_after_most_of_the_limit_leaves_only_the_remainder() {
    let (limit, spent, read_left, fast_on, fast_off) = late_decline(|spent, _| spent + spent / 19);
    assert!(
        spent * 10 > limit * 9,
        "the certificate took {spent} of {limit}"
    );
    assert_eq!(
        fast_on - spent,
        read_left,
        "after the certificate, the rest is not the reading's on the remainder {}",
        limit - spent
    );
    assert!(
        fast_off > 10 * read_left,
        "control: the reading alone took {fast_off}, not more than ten times {read_left}"
    );
}

/// The shared body: the limit is `limit_of(certificate's work, reading's work)`; returns the
/// limit, the certificate's work, the reading's on what is left, and the fast work on and off.
fn late_decline(limit_of: fn(u64, u64) -> u64) -> (u64, u64, u64, u64, u64) {
    let f = guards_f(16, 12, false, true);
    let h = IntervalSet::of(4, 12);
    assert_eq!(project(&f, "i"), IntervalSet::of(5, 12));
    type Run<'a> = &'a dyn Fn(&mut Work) -> Result<bool, Refusal>;
    let alone = |run: Run, allowance: u64| {
        EXACT_WORK.set(0);
        let mut left = allowance;
        let answered = tried(&mut left, SOLVER, |w| Ok(run(w)?.then_some(())));
        (answered.is_some(), EXACT_WORK.replace(0))
    };
    let certificate = |w: &mut Work| Ok(guarded::forward(&f, &a("i"), &h, w)?.is_some());
    let reading = |w: &mut Work| Ok(read_once(&f, w)?.is_some());
    let (certified, spent) = alone(&certificate, u64::MAX);
    assert!(
        !certified,
        "the certificate answered a set wider than the projection"
    );
    let (_, read) = alone(&reading, u64::MAX);
    assert!(spent > 0 && read > 0, "certificate {spent}, reading {read}");
    let limit = limit_of(spent, read);
    let (read_answered, read_left) = alone(&reading, limit - spent);
    assert!(
        !read_answered,
        "the reading answered within {}",
        limit - spent
    );
    let i = a("i");
    let kept: HashSet<&Atom> = [&i].into_iter().collect();
    EXACT_WORK.set(0);
    tried(&mut { limit }, SOLVER, |w| {
        reduced(&f, &|s| kept.contains(s), w)
    });
    let reduce = EXACT_WORK.replace(0);
    let run = |off: bool| {
        EXACT_LIMIT_SET.set(Some(limit));
        GUARDED_OFF.set(off);
        EXACT_WORK.set(0);
        FAST_WORK.set(0);
        let got = exact_each(&f, &[a("i")], (vec![Ok(h.clone())], vec![]), SOLVER);
        GUARDED_OFF.set(false);
        EXACT_LIMIT_SET.set(None);
        EXACT_WORK.set(0);
        (got.sets, FAST_WORK.replace(0) - reduce)
    };
    let (on, fast_on) = run(false);
    let (off, fast_off) = run(true);
    println!(
        "limit {limit}: certificate {spent}, reading alone {read}, reading on what is left \
         {read_left}, reduced {reduce}; fast work on {fast_on}, off {fast_off}"
    );
    assert_eq!(on, off);
    assert!(
        fast_on <= spent + read_left,
        "the fast work {fast_on} passes the certificate's {spent} and the reading's {read_left}"
    );
    assert!(
        spent + fast_off > fast_on && spent + fast_off > limit,
        "control: {spent} + {fast_off} is within the limit {limit}"
    );
    (limit, spent, read_left, fast_on, fast_off)
}

fn certify(f: &Formula, s: &str, h: &IntervalSet) -> Option<IntervalSet> {
    let mut work = Work {
        used: 0,
        limit: u64::MAX,
        solver: SOLVER,
    };
    guarded::forward(f, &a(s), h, &mut work).unwrap()
}

/// Where the set given is wider than the projection, the certificate declines, never
/// answering with a value that has no point: the counter's set widened by one value below; a
/// hole (`x != 0`) under a set that holds it; and given the set without the hole, it answers.
#[test]
fn a_set_wider_than_the_projection_is_never_certified() {
    let f = guards_f(16, 12, false, true);
    assert_eq!(
        certify(&f, "i", &IntervalSet::of(5, 12)),
        Some(IntervalSet::of(5, 12))
    );
    assert_eq!(certify(&f, "i", &IntervalSet::of(4, 12)), None);
    let holed = Formula::and(vec![
        Formula::Not(Shared::new(eq(&[("x", 1)], 0))),
        ge(&[("x", 1)], 2),
        ge(&[("x", -1)], 2),
    ]);
    assert_eq!(certify(&holed, "x", &IntervalSet::of(-2, 2)), None);
    let apart = IntervalSet::of(-2, -1).join(&IntervalSet::of(1, 2));
    assert_eq!(certify(&holed, "x", &apart), Some(apart));
}

/// The cases the certificate must decline, each with its set exact or wider: a guard reading
/// the only free atom; a choice across the cut of its guard whose two equations give the pin
/// other slopes (taken on one side of the cut, it answers); two guards that are not
/// complements (`x >= 1`, `x <= -1`: `x == 0` takes neither); and a diamond, the head defined
/// twice, whose second definition holds at no point.
#[test]
fn guards_on_the_pin_unequal_slopes_gaps_and_diamonds_decline() {
    let box_x = |f: Formula| Formula::and(vec![f, ge(&[("x", 1)], 2), ge(&[("x", -1)], 2)]);
    let on_pin = box_x(Formula::or(vec![
        Formula::and(vec![ge(&[("y", 1)], 0), eq(&[("z", 1)], -1)]),
        Formula::and(vec![ge(&[("y", -1)], -1), eq(&[("z", 1)], -2)]),
    ]));
    assert_eq!(certify(&on_pin, "x", &IntervalSet::of(-2, 2)), None);
    let slopes = box_x(Formula::and(vec![
        Formula::or(vec![
            Formula::and(vec![ge(&[("x", 1)], 0), eq(&[("z", 1), ("y", -1)], 0)]),
            Formula::and(vec![ge(&[("x", -1)], -1), eq(&[("z", 1), ("y", -2)], 0)]),
        ]),
        ge(&[("y", 1)], 0),
    ]));
    assert_eq!(certify(&slopes, "x", &IntervalSet::of(-2, 2)), None);
    assert_eq!(
        certify(&slopes, "x", &IntervalSet::of(0, 2)),
        Some(IntervalSet::of(0, 2))
    );
    let gap = box_x(Formula::or(vec![
        Formula::and(vec![ge(&[("x", 1)], -1), eq(&[("z", 1)], 0)]),
        Formula::and(vec![ge(&[("x", -1)], -1), eq(&[("z", 1)], -1)]),
    ]));
    assert_eq!(certify(&gap, "x", &IntervalSet::of(-2, 2)), None);
    assert_eq!(
        project(&gap, "x"),
        IntervalSet::of(-2, -1).join(&IntervalSet::of(1, 2))
    );
    // `b == x + 1`, `c == x + 1`, `d == b` and `d == c + 1`: no point at all.
    let diamond = |shift: i64| {
        box_x(Formula::and(vec![
            eq(&[("b", 1), ("x", -1)], -1),
            eq(&[("c", 1), ("x", -1)], -1),
            eq(&[("d", 1), ("b", -1)], 0),
            eq(&[("d", 1), ("c", -1)], -shift),
        ]))
    };
    assert_eq!(certify(&diamond(1), "x", &IntervalSet::of(-2, 2)), None);
    assert_eq!(certify(&diamond(1), "x", &IntervalSet::single(0)), None);
    assert_eq!(project(&diamond(1), "x"), IntervalSet::empty());
    // The same diamond with `d == c`: every value has a point; the certificate answers at
    // each single value, where the intervals are exact.
    assert_eq!(
        certify(&diamond(0), "x", &IntervalSet::single(1)),
        Some(IntervalSet::single(1))
    );
    assert_eq!(project(&diamond(0), "x"), IntervalSet::of(-2, 2));
}

/// The certificate's work limit on both sides: at every limit, either the certificate answers
/// with no work of the loop and no question, or it stops (or declines) and the loop runs as it
/// does with the certificate off, with the same loop work, questions and answer; both happen
/// over the limits tried. A formula the certificate declines (the evens with one disjunction)
/// gives the same answer and the same loop work with the certificate on and off.
#[test]
fn the_certificate_meets_the_work_limit_alike_on_both_sides() {
    let f = guards_f(16, 12, false, true);
    let want = IntervalSet::of(5, 12);
    EXACT_WORK.set(0);
    FAST_WORK.set(0);
    EXACT_QUESTIONS.set(0);
    assert_eq!(project(&f, "i"), want);
    let needed = FAST_WORK.replace(0);
    assert_eq!(EXACT_WORK.replace(0), needed);
    assert_eq!(EXACT_QUESTIONS.replace(0), 0);
    let run = |limit: u64, off: bool| {
        EXACT_LIMIT_SET.set(Some(limit));
        GUARDED_OFF.set(off);
        EXACT_WORK.set(0);
        FAST_WORK.set(0);
        EXACT_QUESTIONS.set(0);
        let got = project_each_exact(&f, &[a("i")]).unwrap().0;
        GUARDED_OFF.set(false);
        EXACT_LIMIT_SET.set(None);
        let fast = FAST_WORK.replace(0);
        (
            got,
            EXACT_WORK.replace(0) - fast,
            EXACT_QUESTIONS.replace(0),
        )
    };
    let (mut answered, mut stopped) = (false, false);
    for limit in (0..16).map(|j| needed >> j) {
        let on = run(limit, false);
        if on == (vec![Ok(want.clone())], 0, 0) {
            answered = true;
        } else {
            assert_eq!(on, run(limit, true), "limit {limit}");
            stopped = true;
        }
    }
    assert!(answered && stopped, "answered {answered} stopped {stopped}");
    let g = evens(20);
    let loop_run = |off: bool| {
        GUARDED_OFF.set(off);
        EXACT_WORK.set(0);
        FAST_WORK.set(0);
        let got = project(&g, "x");
        GUARDED_OFF.set(false);
        (got, EXACT_WORK.replace(0) - FAST_WORK.replace(0))
    };
    assert_eq!(loop_run(false), loop_run(true));
}

/// `unary_arms` of `l01_39_scope_relations::families`: `k` names all at least 1 or all at most
/// -1, then `z0 + z(k-1) >= 5 || x <= 0`. The two tests share `z0` and `z(k-1)`, so `read_once`
/// declines the part (a conjunction with two parts reading one atom).
fn unary_arms(k: usize) -> (Formula, Vec<Atom>) {
    let z = |i: usize| format!("z{i}");
    let up = Formula::and((0..k).map(|i| ge(&[(&z(i), 1)], -1)).collect());
    let down = Formula::and((0..k).map(|i| ge(&[(&z(i), -1)], -1)).collect());
    let last = z(k - 1);
    let test = Formula::or(vec![ge(&[("z0", 1), (&last, 1)], -5), ge(&[("x", -1)], 0)]);
    let f = Formula::and(vec![Formula::or(vec![up, down]), test]);
    let mut syms: Vec<Atom> = (0..k).map(|i| a(&z(i))).collect();
    syms.push(a("x"));
    (f, syms)
}

/// Each point's implicant answers every symbol it reads, and every symbol it does not, for all
/// the symbols of a part at once: a part `read_once` declines is not covered symbol by symbol,
/// each cover reading the whole part, O(k) symbols times O(k) rows (PRES-cover-bench-unary-arms).
#[test]
fn a_declined_part_is_covered_for_all_its_symbols_at_once() {
    let not_zero = IntervalSet::range(End::NegInf, fin(&Int::from(-1)))
        .join(&IntervalSet::range(fin(&Int::from(1)), End::PosInf));
    let mut used = Vec::new();
    for k in [64, 512] {
        let (f, syms) = unary_arms(k);
        EXACT_WORK.set(0);
        let got = project_each_exact(&f, &syms).unwrap().0;
        used.push(EXACT_WORK.replace(0));
        for (s, g) in syms.iter().zip(&got) {
            let want = if *s == a("x") {
                IntervalSet::top()
            } else {
                not_zero.clone()
            };
            assert_eq!(g.as_ref().unwrap(), &want, "{s:?} at k = {k}");
        }
    }
    let ratio = used[1] as f64 / used[0].max(1) as f64;
    assert!(ratio < 10.5, "work {used:?}, {ratio:.2} times at 8 times k");
}

/// Two atoms with equal coefficients in every sum are twins only where no other row reads
/// one of them: `a mod 3 == 0`, written `a == 3·q`, gives `a` a column `b` and `c` lack, so
/// `a` is not given every value, while `b` and `c`, twins, are.
#[test]
fn an_atom_read_by_a_remainder_is_no_twin() {
    let f = Formula::and(vec![
        ge(&[("a", 1), ("b", 1), ("c", 1)], 0),
        ge(&[("a", -1), ("b", -1), ("c", -1)], 10),
        eq(&[("a", 1), ("q", -3)], 0),
    ]);
    let top = IntervalSet::top();
    let names = [a("a"), a("b"), a("c")];
    let want: BTreeMap<&Atom, IntervalSet> = names.iter().map(|s| (s, top.clone())).collect();
    let mut points = Vec::new();
    let mut out = HashMap::new();
    let mut work = Work {
        used: 0,
        limit: EXACT_LIMIT,
        solver: SOLVER,
    };
    shared_cells(&f, constraints(&f), want, &mut points, &mut out, &mut work).unwrap();
    assert_eq!(out.get(&a("b")), Some(&top));
    assert_eq!(out.get(&a("c")), Some(&top));
    assert_ne!(out.get(&a("a")), Some(&top), "{out:?}");
}

/// One linear form over boxed atoms projects exactly onto each atom: `z0 + z1 + z2 >= 12` (and
/// the weaker `>= 3`) with each in `-5..=5` leaves each at least 2, as the other two give at
/// most 10; `w`, read by no sum, keeps its box.
#[test]
fn a_sum_of_boxed_atoms_projects_exactly_onto_each() {
    let con = |f: Formula| match &f {
        Formula::Con(c) => c.clone(),
        _ => unreachable!(),
    };
    let mut rows = Vec::new();
    for z in ["z0", "z1", "z2", "w"] {
        rows.push(con(ge(&[(z, 1)], 5)));
        rows.push(con(ge(&[(z, -1)], 5)));
    }
    rows.push(con(ge(&[("z0", 1), ("z1", 1), ("z2", 1)], -12)));
    rows.push(con(ge(&[("z0", 1), ("z1", 1), ("z2", 1)], -3)));
    let mut work = Work {
        used: 0,
        limit: EXACT_LIMIT,
        solver: SOLVER,
    };
    let got = star(&rows, &mut work).unwrap().unwrap();
    for z in ["z0", "z1", "z2"] {
        assert_eq!(got[&a(z)], IntervalSet::of(2, 5), "{z}");
    }
    assert_eq!(got[&a("w")], IntervalSet::of(-5, 5));
    // Two different forms are not this shape.
    rows.push(con(ge(&[("z0", 1), ("w", 1)], 0)));
    assert!(star(&rows, &mut work).unwrap().is_none());
}

/// The rows of `star`'s tests, each a constraint.
fn star_rows(fs: Vec<Formula>) -> Vec<Con> {
    (fs.into_iter())
        .map(|f| match &f {
            Formula::Con(c) => c.clone(),
            _ => unreachable!(),
        })
        .collect()
}

fn star_of(fs: Vec<Formula>) -> Option<HashMap<Atom, IntervalSet>> {
    let mut work = Work {
        used: 0,
        limit: EXACT_LIMIT,
        solver: SOLVER,
    };
    star(&star_rows(fs), &mut work).unwrap()
}

/// `-2·z0 - z1 >= 4` with each in `-5..=5`: `-z1` is at most 5, so `-2·z0 >= -1`, `z0 <= 1/2`,
/// rounded down to 0 (a negative coefficient bounds from above, and the bound rounds toward
/// lower values); `-2·z0` is at most 10, so `z1 <= 6`, and `z1` keeps its box.
#[test]
fn a_star_with_a_negative_coefficient_bounds_from_above() {
    let got = star_of(vec![
        ge(&[("z0", 1)], 5),
        ge(&[("z0", -1)], 5),
        ge(&[("z1", 1)], 5),
        ge(&[("z1", -1)], 5),
        ge(&[("z0", -2), ("z1", -1)], -4),
    ])
    .unwrap();
    assert_eq!(got[&a("z0")], IntervalSet::of(-5, 0));
    assert_eq!(got[&a("z1")], IntervalSet::of(-5, 5));
}

/// A coefficient written as zero is no term (`lin` and every `Lin` keep none), so `z1` there
/// is read by its box alone: `3·z0 + 0·z1 >= 7` leaves `z0 >= 3`.
#[test]
fn a_star_with_a_zero_coefficient_reads_that_atom_by_its_box() {
    let got = star_of(vec![
        ge(&[("z0", 1)], 5),
        ge(&[("z0", -1)], 5),
        ge(&[("z1", 1)], 5),
        ge(&[("z1", -1)], 5),
        ge(&[("z0", 3), ("z1", 0), ("z2", 1)], -7),
        ge(&[("z2", 1)], 0),
        ge(&[("z2", -1)], 0),
    ])
    .unwrap();
    assert_eq!(got[&a("z0")], IntervalSet::of(3, 5));
    assert_eq!(got[&a("z1")], IntervalSet::of(-5, 5));
}

/// `3·z1 + z2 >= 7` with `z2` in `0..=2`: `3·z1 >= 5`, so `z1 >= 2` (5/3 rounded up), and
/// with `z1` in `0..=2`, `z2 >= 1`.
#[test]
fn a_star_with_a_coefficient_of_three_rounds_up() {
    let got = star_of(vec![
        ge(&[("z1", 1)], 0),
        ge(&[("z1", -1)], 2),
        ge(&[("z2", 1)], 0),
        ge(&[("z2", -1)], 2),
        ge(&[("z1", 3), ("z2", 1)], -7),
    ])
    .unwrap();
    assert_eq!(got[&a("z1")], IntervalSet::of(2, 2));
    assert_eq!(got[&a("z2")], IntervalSet::of(1, 2));
}

/// One empty box (`z1 >= 3` and `z1 <= 1`): no point, so every projection is empty.
#[test]
fn a_star_with_an_empty_box_projects_to_nothing() {
    let got = star_of(vec![
        ge(&[("z0", 1)], 5),
        ge(&[("z1", 1)], -3),
        ge(&[("z1", -1)], 1),
        ge(&[("z0", 1), ("z1", 1)], 0),
    ])
    .unwrap();
    assert_eq!(got[&a("z0")], IntervalSet::empty());
    assert_eq!(got[&a("z1")], IntervalSet::empty());
}

/// `z0 + z1 >= 11` with each in `0..=5`: never met, so every projection is empty.
#[test]
fn a_star_whose_form_cannot_be_met_projects_to_nothing() {
    let got = star_of(vec![
        ge(&[("z0", 1)], 0),
        ge(&[("z0", -1)], 5),
        ge(&[("z1", 1)], 0),
        ge(&[("z1", -1)], 5),
        ge(&[("z0", 1), ("z1", 1)], -11),
    ])
    .unwrap();
    assert_eq!(got[&a("z0")], IntervalSet::empty());
    assert_eq!(got[&a("z1")], IntervalSet::empty());
}

/// `(sum >= 5k - 2 || z0 <= -1)` with each of the `k` names `z_i` in `-5..=5`, as two blocks
/// read once: in the first each `z_i` is at least 3 (the other `k - 1` give at most `5k - 5`),
/// so `z0` is `-5..=-1` or `3..=5` and every other name keeps its box.
fn boxed_sum_arms(k: usize) -> Formula {
    let names: Vec<String> = (0..k).map(|i| format!("z{i}")).collect();
    let boxes = || -> Vec<Formula> {
        (names.iter())
            .flat_map(|n| [ge(&[(n.as_str(), 1)], 5), ge(&[(n.as_str(), -1)], 5)])
            .collect()
    };
    let sum: Vec<(&str, i64)> = names.iter().map(|n| (n.as_str(), 1)).collect();
    let mut first = boxes();
    first.push(ge(&sum, -(5 * k as i64 - 2)));
    let mut second = boxes();
    second.push(ge(&[("z0", -1)], -1));
    Formula::or(vec![Formula::and(first), Formula::and(second)])
}

/// A block whose rows are a sum of `k` boxed names is read in work linear in `k`
/// ([`star`]), where each name's own elimination over the block was work near `k^2` in all
/// (`wide` of `l01_39_scope_relations::families`).
#[test]
fn a_block_of_a_boxed_sum_is_read_once_in_linear_work() {
    let mut used = Vec::new();
    for k in [64, 512] {
        let f = boxed_sum_arms(k);
        let mut work = Work {
            used: 0,
            limit: EXACT_LIMIT,
            solver: SOLVER,
        };
        let (_, sets) = read_once(&f, &mut work)
            .expect("within the limit")
            .expect("a reading");
        used.push(work.used);
        let z0 = IntervalSet::of(-5, -1).join(&IntervalSet::of(3, 5));
        assert_eq!(sets[&a("z0")], z0);
        assert_eq!(sets[&a("z1")], IntervalSet::of(-5, 5));
    }
    let ratio = used[1] as f64 / used[0] as f64;
    assert!(ratio < 10.5, "work {used:?}, {ratio:.2} times");
}

/// One part of the counter of [`guards_f`] at k = 16, asked for `i`, `m` and every `t(j)`,
/// where the forward certificate answers one symbol and the reading declines (`exact_each`).
/// The shared step reads each left symbol's cell at the newest point before its question
/// ([`shared_cells`]), as the symbol's own cover would read it at its first point, so it asks
/// no question that cover would not. The work with the step is then at most the work without
/// it plus what the step reads beyond that one cell a symbol: `c = k·(size + 2·PIECE)`, for
/// the k symbols asked and `size` the constraints of `f` (at least the part's). Before the cell
/// read, the step asked 9 questions here, 3,141,230 units against 899,024 without it; with it,
/// no question, 607,274 units. The answers are the same, and both sides stay within `4·k·L`
/// for limit L.
#[test]
fn a_part_certified_in_part_shares_only_what_direct_declined() {
    let f = guards_f(16, 12, false, true);
    let mut names = vec!["i".to_string(), "m".to_string()];
    names.extend((1..=16).map(|j| format!("t{j}")));
    let syms: Vec<Atom> = names.iter().map(|s| a(s)).collect();
    let run = |off: bool| {
        SHARED_OFF.set(off);
        EXACT_WORK.set(0);
        let got = project_each_exact(&f, &syms).unwrap().0;
        SHARED_OFF.set(false);
        (got, EXACT_WORK.replace(0))
    };
    let (on, work_on) = run(false);
    let (off, work_off) = run(true);
    assert_eq!(on, off);
    let c = syms.len() as u64 * (constraints(&f) + 2 * PIECE);
    assert!(
        work_on <= work_off + c,
        "work on {work_on}, off {work_off}, c {c}"
    );
    let bound = 4 * syms.len() as u64 * EXACT_LIMIT;
    assert!(
        work_on <= bound && work_off <= bound,
        "{work_on}, {work_off}, bound {bound}"
    );
}

/// Where the cell at the newest point leaves a gap, [`shared_cells`] still asks its question:
/// on `(0 <= x <= 2 ∧ y = 0) ∨ (3 <= x <= 7 ∧ y = 1)` the first point is in one disjunct, its
/// cell of `x` holds one of the two ranges, and the other is found by a question. The sets
/// asked are the hulls of the answers, since the step asks one question a symbol and leaves
/// a symbol with more gaps to its own cover. The sets shown are those of the symbols run
/// alone (`SHARED_OFF`).
#[test]
fn a_cell_with_a_gap_still_asks_its_question() {
    let arm = |lo: i64, hi: i64, v: i64| {
        Formula::and(vec![
            ge(&[("x", 1)], -lo),
            ge(&[("x", -1)], hi),
            eq(&[("y", 1)], -v),
        ])
    };
    let f = Formula::or(vec![arm(0, 2, 0), arm(3, 7, 1)]);
    let (ax, ay) = (a("x"), a("y"));
    let want: BTreeMap<&Atom, IntervalSet> =
        [(&ax, IntervalSet::of(0, 7)), (&ay, IntervalSet::of(0, 1))]
            .into_iter()
            .collect();
    let mut work = Work {
        used: 0,
        limit: EXACT_LIMIT,
        solver: SOLVER,
    };
    let (mut points, mut out) = (Vec::new(), HashMap::new());
    EXACT_QUESTIONS.set(0);
    shared_cells(&f, constraints(&f), want, &mut points, &mut out, &mut work).unwrap();
    let asked = EXACT_QUESTIONS.replace(0);
    assert!(asked >= 1, "{asked} questions: the gap was not asked about");
    SHARED_OFF.set(true);
    let alone = project_each_exact(&f, &[ax.clone(), ay.clone()]).unwrap().0;
    SHARED_OFF.set(false);
    let x_set = IntervalSet::of(0, 7);
    assert_eq!(out.get(&ax), Some(&x_set));
    assert_eq!(out.get(&ay), Some(&IntervalSet::of(0, 1)));
    assert_eq!(
        format!("{:?}", alone[0]),
        format!("{:?}", Ok::<_, Refusal>(x_set))
    );
}

/// The family `wide_pairs` of l01_39 at `k` names: one disjunction of two arms, each the
/// conjunction of `z(j) + z(j+1) >= 0` (`-` in the other arm) over the adjacent pairs of `z0`
/// to `z(k-1)`. It has no definition, so the forward certificate declines for every name.
fn wide_pairs(k: usize) -> Formula {
    let z: Vec<String> = (0..k).map(|j| format!("z{j}")).collect();
    let arm = |c: i64| {
        Formula::And(Shared::new(
            (0..k - 1)
                .map(|j| ge(&[(&z[j], 1), (&z[j + 1], c)], 0))
                .collect(),
        ))
    };
    Formula::Or(Shared::new(vec![arm(1), arm(-1)]))
}

/// The certificates of a part's k names read the part once, not once a name: on `wide_pairs`
/// at 128 names, the work they add to the fast work is one piece for each of its constraints
/// read (so the meter sees what they read), and not 128 times that. Before, each name's
/// certificate read the whole part, k times the formula in all (O(k²) here), and charged one
/// piece for the disjunction, not one for each constraint read in it: 32.7 times the
/// instructions at 8n on `wide_pairs_scale` (PRES-groupA-forward-per-part).
#[test]
fn the_certificates_of_a_part_read_it_once_not_once_a_name() {
    let k = 128;
    let f = wide_pairs(k);
    let syms: Vec<Atom> = (0..k).map(|j| a(&format!("z{j}"))).collect();
    let run = |off: bool| {
        GUARDED_OFF.set(off);
        EXACT_WORK.set(0);
        FAST_WORK.set(0);
        let found = ((0..k).map(|_| Ok(IntervalSet::top())).collect(), vec![]);
        let got = exact_each(&f, &syms, found, SOLVER);
        GUARDED_OFF.set(false);
        EXACT_WORK.set(0);
        (got.sets, FAST_WORK.replace(0))
    };
    let (on, fast_on) = run(false);
    let (off, fast_off) = run(true);
    assert_eq!(on, off);
    let read = PIECE * 2 * (k as u64 - 1);
    let added = fast_on.saturating_sub(fast_off);
    assert!(
        (read..=2 * read).contains(&added),
        "the certificates added {added} units of work for {read} units of constraints read"
    );
}

/// `s` asked of `f` by `exact_each`, given the solver's set `h`, with the forward certificate
/// on and off: the two answers must agree.
fn on_off(f: &Formula, h: &IntervalSet) -> String {
    let run = |off: bool| {
        GUARDED_OFF.set(off);
        let got = exact_each(f, &[a("s")], (vec![Ok(h.clone())], vec![]), SOLVER);
        GUARDED_OFF.set(false);
        EXACT_WORK.set(0);
        FAST_WORK.set(0);
        format!("{:?}", got.sets)
    };
    let (on, off) = (run(false), run(true));
    assert_eq!(on, off, "the certificate changed the answer");
    on
}

/// The count of `guarded::prepare` (decline where the atoms number more than the definitions
/// plus 2) at its edge. `s == x + y`, `0 <= s <= 9`, `0 <= x <= 3`: three atoms, one
/// definition, exactly the definitions plus 2. The reading learns `s`, pins `x`, then takes the
/// equation for `y`, so the certificate answers `[0, 9]`. A count that declined one atom
/// earlier (at the definitions plus 1) would decline here, and this test would fail.
#[test]
fn a_part_with_exactly_two_atoms_more_than_its_definitions_is_certified() {
    let f = Formula::And(Shared::new(vec![
        eq(&[("x", 1), ("y", 1), ("s", -1)], 0),
        ge(&[("s", 1)], 0),
        ge(&[("s", -1)], 9),
        ge(&[("x", 1)], 0),
        ge(&[("x", -1)], 3),
    ]));
    let h = IntervalSet::of(0, 9);
    assert_eq!(certify(&f, "s", &h), Some(h.clone()));
    on_off(&f, &h);
}

/// A definition that reaches two new atoms: `s == x + y + z` has three unknowns once `s` is
/// known; a reading can pin one, and with no other definition the second stop declines. The
/// atoms (4) are the definitions (1) plus 3, so `prepare` declines before any reading, the same
/// answer the reading gives. Given a second definition `z == x`, which supplies one of the two,
/// the atoms (4) are the definitions (2) plus 2: the reading pins `x`, takes `z`, then `y`, and
/// the certificate answers, so the count does not decline it early. Both agree with the cover
/// alone.
#[test]
fn a_definition_that_reaches_two_new_atoms_declines_unless_another_supplies_one() {
    let bounds = || {
        vec![
            eq(&[("x", 1), ("y", 1), ("z", 1), ("s", -1)], 0),
            ge(&[("s", 1)], 0),
            ge(&[("s", -1)], 9),
            ge(&[("x", 1)], 0),
            ge(&[("x", -1)], 3),
        ]
    };
    let h = IntervalSet::of(0, 9);
    let alone = Formula::And(Shared::new(bounds()));
    let mut work = Work {
        used: 0,
        limit: u64::MAX,
        solver: SOLVER,
    };
    assert!(guarded::prepare(&alone, &mut work).unwrap().is_none());
    assert_eq!(certify(&alone, "s", &h), None);
    on_off(&alone, &h);
    let mut parts = bounds();
    parts.push(eq(&[("z", 1), ("x", -1)], 0));
    let supplied = Formula::And(Shared::new(parts));
    assert_eq!(certify(&supplied, "s", &h), Some(h.clone()));
    on_off(&supplied, &h);
}

/// The work of the forward certificates of the one part `family(k)` (`guarded::prepare`, then
/// `certificates` for every name, asked with the set given) at k = 64 and 512; at k = 8 the
/// answers of `exact_each` agree with the cover alone. Returns the two counts.
fn fast_work_of(family: impl Fn(usize) -> (Formula, Vec<Atom>, Vec<IntervalSet>)) -> Vec<u64> {
    let answers = |off: bool| {
        let (f, syms, sets) = family(8);
        GUARDED_OFF.set(off);
        let got = exact_each(
            &f,
            &syms,
            (sets.into_iter().map(Ok).collect(), vec![]),
            SOLVER,
        );
        GUARDED_OFF.set(false);
        EXACT_WORK.set(0);
        FAST_WORK.set(0);
        format!("{:?}", got.sets)
    };
    assert_eq!(
        answers(false),
        answers(true),
        "the certificates against the cover alone"
    );
    let work = |k: usize| {
        let (f, syms, sets) = family(k);
        let mine: Vec<(&Atom, &IntervalSet)> = syms.iter().zip(&sets).collect();
        let mut left = u64::MAX;
        FAST_WORK.set(0);
        if let Some(prep) = tried(&mut left, SOLVER, |w| guarded::prepare(&f, w)) {
            certificates(&prep, &mine, &mut left, SOLVER);
        }
        FAST_WORK.replace(0)
    };
    [64, 512].into_iter().map(work).collect()
}

/// Names tied through equations of three atoms: `c(j+1) == c(j) + d`, `0 <= d <= 1`,
/// `0 <= c0 <= 9`, every name asked with its exact set (`c(j) = c0 + j·d`). One reading for
/// the part, not one a name (PRES-groupA-forward-per-name-order, part 2).
#[test]
fn names_tied_through_three_atoms_are_read_once_for_the_part() {
    let used = fast_work_of(|k| {
        let c = |j: usize| format!("c{j}");
        let mut rows: Vec<Formula> = (0..k)
            .map(|j| eq(&[(&c(j + 1), 1), (&c(j), -1), ("d", -1)], 0))
            .collect();
        rows.extend([ge(&[("d", 1)], 0), ge(&[("d", -1)], 1)]);
        rows.extend([ge(&[("c0", 1)], 0), ge(&[("c0", -1)], 9)]);
        let mut syms: Vec<Atom> = (0..=k).map(|j| a(&c(j))).collect();
        syms.push(a("d"));
        let mut sets: Vec<IntervalSet> = (0..=k as i64)
            .map(|j| IntervalSet::of(0, 9).join(&IntervalSet::of(j, j + 9)))
            .collect();
        sets.push(IntervalSet::of(0, 1));
        (Formula::And(Shared::new(rows)), syms, sets)
    });
    let ratio = used[1] as f64 / used[0].max(1) as f64;
    assert!(ratio < 10.5, "work {used:?}, {ratio:.2} times at 8 times k");
}

/// A class whose certificate declines: `z(j) == x + j`, `0 <= x <= 9`, `x >= 5 || x <= 3`,
/// every name asked with a set holding a value with no point (`x = 4`), so every certificate
/// declines. The class is tried once, not once a name (PRES-groupA-forward-per-name-order,
/// part 2).
#[test]
fn a_class_whose_certificate_declines_is_tried_once() {
    let used = fast_work_of(|k| {
        let z = |j: usize| format!("z{j}");
        let mut rows: Vec<Formula> = (0..k)
            .map(|j| eq(&[(&z(j), 1), ("x", -1)], -(j as i64)))
            .collect();
        rows.extend([ge(&[("x", 1)], 0), ge(&[("x", -1)], 9)]);
        rows.push(Formula::or(vec![ge(&[("x", 1)], -5), ge(&[("x", -1)], 3)]));
        let syms: Vec<Atom> = (0..k).map(|j| a(&z(j))).collect();
        let sets = (0..k as i64).map(|j| IntervalSet::of(j, j + 9)).collect();
        (Formula::And(Shared::new(rows)), syms, sets)
    });
    let ratio = used[1] as f64 / used[0].max(1) as f64;
    assert!(ratio < 10.5, "work {used:?}, {ratio:.2} times at 8 times k");
}

/// The whole work of `exact_each` (certificates, the reading of the part and the cover) on
/// `family(k)` at k = 64 and 512, every name asked with the set given; the answers at k = 8
/// agree with the cover alone.
fn exact_work_of(family: impl Fn(usize) -> (Formula, Vec<Atom>, Vec<IntervalSet>)) -> Vec<u64> {
    let run = |k: usize, off: bool| {
        let (f, syms, sets) = family(k);
        GUARDED_OFF.set(off);
        EXACT_WORK.set(0);
        FAST_WORK.set(0);
        let got = exact_each(
            &f,
            &syms,
            (sets.into_iter().map(Ok).collect(), vec![]),
            SOLVER,
        );
        GUARDED_OFF.set(false);
        FAST_WORK.set(0);
        (format!("{:?}", got.sets), EXACT_WORK.replace(0))
    };
    assert_eq!(
        run(8, false).0,
        run(8, true).0,
        "the certificates against the cover alone"
    );
    [64, 512].into_iter().map(|k| run(k, false).1).collect()
}

/// `y(j) == a·p + b·q + j` with `0 <= p, q <= 9`, every name asked with the hull of its values.
fn two_free_atoms(a_: i64, b: i64) -> impl Fn(usize) -> (Formula, Vec<Atom>, Vec<IntervalSet>) {
    move |k| {
        let y = |j: usize| format!("y{j}");
        let mut rows: Vec<Formula> = (0..k)
            .map(|j| eq(&[(&y(j), 1), ("p", -a_), ("q", -b)], -(j as i64)))
            .collect();
        rows.extend([ge(&[("p", 1)], 0), ge(&[("p", -1)], 9)]);
        rows.extend([ge(&[("q", 1)], 0), ge(&[("q", -1)], 9)]);
        let syms: Vec<Atom> = (0..k).map(|j| a(&y(j))).collect();
        let top = 9 * (a_ + b);
        let sets = (0..k as i64).map(|j| IntervalSet::of(j, j + top)).collect();
        (Formula::And(Shared::new(rows)), syms, sets)
    }
}

/// Names whose coefficients on the free atoms are not 1 or -1, `y(j) == 2·p + 3·q + j`: the
/// part is read once, not once a name (PRES-groupA-forward-per-name-order, part 2b).
#[test]
fn names_with_coefficients_past_one_are_read_once_for_the_part() {
    let used = exact_work_of(two_free_atoms(2, 3));
    let ratio = used[1] as f64 / used[0].max(1) as f64;
    assert!(ratio < 10.5, "work {used:?}, {ratio:.2} times at 8 times k");
}

/// As above with a common factor, `y(j) == 2·p + 4·q + j`: whatever answers these names, the
/// part costs no work a name of its size (PRES-groupA-forward-per-name-order, part 2b).
#[test]
fn names_with_a_common_factor_are_read_once_for_the_part() {
    let used = exact_work_of(two_free_atoms(2, 4));
    let ratio = used[1] as f64 / used[0].max(1) as f64;
    assert!(ratio < 10.5, "work {used:?}, {ratio:.2} times at 8 times k");
}

/// As `names_with_coefficients_past_one_are_read_once_for_the_part` with one more half-plane
/// a name, `p + j·q <= 9 + 9·j` (none cuts the box): the residuals grow with k, and each name
/// must not read them all (PRES-two-pin-edges).
#[test]
fn names_over_a_polygon_of_many_sides_read_its_edges_once() {
    let used = exact_work_of(|k| {
        let (f, syms, sets) = two_free_atoms(2, 3)(k);
        let Formula::And(rows) = &f else {
            unreachable!()
        };
        let mut rows: Vec<Formula> = rows.iter().cloned().collect();
        rows.extend((0..k as i64).map(|j| ge(&[("p", -1), ("q", -j)], 9 + 9 * j)));
        (Formula::And(Shared::new(rows)), syms, sets)
    });
    let ratio = used[1] as f64 / used[0].max(1) as f64;
    assert!(ratio < 10.5, "work {used:?}, {ratio:.2} times at 8 times k");
}

/// As above with every row a true edge, the tangents `q >= 2·j·p - j²` to `q = p²` under
/// `q <= k²`: the edges grow with k, and each name still costs no work of their number
/// (PRES-two-pin-edges).
#[test]
fn names_over_a_polygon_of_many_true_edges_cost_log_of_them() {
    let used = exact_work_of(|k| {
        let y = |j: usize| format!("y{j}");
        let kk = k as i64;
        let mut rows: Vec<Formula> = (0..k)
            .map(|j| eq(&[(&y(j), 1), ("p", -2), ("q", -3)], -(j as i64)))
            .collect();
        rows.extend((0..=kk).map(|j| ge(&[("q", 1), ("p", -2 * j)], j * j)));
        rows.extend([ge(&[("q", -1)], kk * kk), ge(&[("p", 1)], kk)]);
        let syms: Vec<Atom> = (0..k).map(|j| a(&y(j))).collect();
        let sets = (0..k)
            .map(|_| IntervalSet::from_pieces(vec![(End::NegInf, End::PosInf)]))
            .collect();
        (Formula::And(Shared::new(rows)), syms, sets)
    });
    // The part is O(k log k) (the sort of its k + 3 edges) and each name O(log k) (binary
    // searches over them, each charged one piece a halving: `u64::BITS - leading_zeros + 1`,
    // 8 at 67 edges and 11 at 515). So the predicted ratio is 8 · 11/8 = 11, which by P300
    // meets the scaling rule for a proved n log n; anything past it is more than n log n.
    let ratio = used[1] as f64 / used[0].max(1) as f64;
    assert!(
        ratio <= 11.0,
        "work {used:?}, {ratio:.2} times at 8 times k"
    );
}

/// The same polygon with names in many directions, `y(j) == g·(j + 1)·p + g·(2·j + 1)·q`,
/// `g = 2` in every third: each set is exactly the values at the polygon's integer points,
/// counted one by one (the cover alone refuses most of these names), through the binary
/// searches along every direction (PRES-two-pin-edges).
#[test]
fn names_in_many_directions_over_many_edges_are_exact() {
    let k = 8i64;
    let y = |j: i64| format!("y{j}");
    let g = |j: i64| if j % 3 == 0 { 2 } else { 1 };
    let mut rows: Vec<Formula> = (0..k)
        .map(|j| {
            eq(
                &[
                    (&y(j), 1),
                    ("p", -g(j) * (j + 1)),
                    ("q", -g(j) * (2 * j + 1)),
                ],
                0,
            )
        })
        .collect();
    rows.extend((0..=k).map(|i| ge(&[("q", 1), ("p", -2 * i)], i * i)));
    rows.extend([ge(&[("q", -1)], k * k), ge(&[("p", 1)], k)]);
    let syms: Vec<Atom> = (0..k).map(|j| a(&y(j))).collect();
    let sets = (0..k)
        .map(|_| Ok(IntervalSet::from_pieces(vec![(End::NegInf, End::PosInf)])))
        .collect();
    let f = Formula::And(Shared::new(rows));
    let got = exact_each(&f, &syms, (sets, vec![]), SOLVER);
    for j in 0..k {
        let mut want = std::collections::BTreeSet::new();
        for p in -k..=k {
            for q in 0..=k * k {
                if (0..=k).all(|i| q - 2 * i * p + i * i >= 0) {
                    want.insert(g(j) * (j + 1) * p + g(j) * (2 * j + 1) * q);
                }
            }
        }
        let Ok(set) = &got.sets[j as usize] else {
            panic!("y{j} refused: {:?}", got.sets[j as usize]);
        };
        for v in -2000..=2000i64 {
            let has = set.ranges.contains(v) && set.class.contains(&Num::from(v));
            assert_eq!(has, want.contains(&v), "y{j} at {v}: {set:?}");
        }
    }
}

/// `y(j) == 2·p + 3·q + j` with only `p, q >= 0`: the polygon is unbounded, and each name's
/// set, `j` and every value from `j + 2` up, is read once for the part (PRES-two-pin-edges).
#[test]
fn names_over_an_unbounded_polygon_are_read_once_for_the_part() {
    let used = exact_work_of(|k| {
        let y = |j: usize| format!("y{j}");
        let mut rows: Vec<Formula> = (0..k)
            .map(|j| eq(&[(&y(j), 1), ("p", -2), ("q", -3)], -(j as i64)))
            .collect();
        rows.extend([ge(&[("p", 1)], 0), ge(&[("q", 1)], 0)]);
        let syms: Vec<Atom> = (0..k).map(|j| a(&y(j))).collect();
        let sets = (0..k as i64)
            .map(|j| IntervalSet::from_pieces(vec![(End::of(j), End::PosInf)]))
            .collect();
        (Formula::And(Shared::new(rows)), syms, sets)
    });
    let ratio = used[1] as f64 / used[0].max(1) as f64;
    assert!(ratio < 10.5, "work {used:?}, {ratio:.2} times at 8 times k");
}

/// The tangents `q >= 2·j·p - j²` to `q = p²` for `j` from 0 to k and `p >= -k`, with no
/// upper side: the polygon is open, its edges grow with k, and names `y(j) == 2·p + 3·q + j`
/// over it cost no work of their number (PRES-two-pin-prune, part a).
fn open_tangents(k: usize) -> (Formula, Vec<Atom>, Vec<IntervalSet>) {
    let y = |j: usize| format!("y{j}");
    let kk = k as i64;
    let mut rows: Vec<Formula> = (0..k)
        .map(|j| eq(&[(&y(j), 1), ("p", -2), ("q", -3)], -(j as i64)))
        .collect();
    rows.extend((0..=kk).map(|j| ge(&[("q", 1), ("p", -2 * j)], j * j)));
    rows.push(ge(&[("p", 1)], kk));
    let syms: Vec<Atom> = (0..k).map(|j| a(&y(j))).collect();
    let sets = (0..k)
        .map(|_| IntervalSet::from_pieces(vec![(End::NegInf, End::PosInf)]))
        .collect();
    (Formula::And(Shared::new(rows)), syms, sets)
}

/// Names over an open polygon of many true edges (`open_tangents`): before PRES-two-pin-prune
/// each name read every half-plane, O(h²) a name (Fourier-Motzkin and Pugh's dark shadow).
#[test]
fn names_over_an_open_polygon_of_many_true_edges_cost_log_of_them() {
    let used = exact_work_of(open_tangents);
    // As `names_over_a_polygon_of_many_true_edges_cost_log_of_them`: O(k log k) a part and
    // O(log k) a name, predicted 8 · 11/8 = 11 times at 8 times k (P300).
    let ratio = used[1] as f64 / used[0].max(1) as f64;
    assert!(
        ratio <= 11.0,
        "work {used:?}, {ratio:.2} times at 8 times k"
    );
}

/// Every set over an open region is exactly the values at its integer points, counted one by
/// one in a box large enough for the window checked, and is answered by the two-pin reading
/// with no question of the cover: the open tangents in many directions, a half-strip, a wedge,
/// a strip and a half-plane, each with redundant half-planes beside its edges, and names that
/// fall, rise or stay along the open side (PRES-two-pin-prune, part a).
#[test]
fn names_over_open_regions_are_exact() {
    // Each region: its name and its half-planes `(A, B, C)`, `A·p + B·q + C >= 0`.
    type Halves = Vec<(i64, i64, i64)>;
    let tangents: Halves = (0..=6)
        .map(|j| (-2 * j, 1, j * j))
        .chain([(1, 0, 6)])
        .collect();
    let regions: Vec<(&str, Halves)> = vec![
        ("tangents", tangents),
        // `p >= 0`, `0 <= q <= 3`, and looser copies.
        (
            "half-strip",
            vec![(1, 0, 0), (0, 1, 0), (0, -1, 3), (0, -1, 5), (1, 0, 4)],
        ),
        // `q >= p`, `q >= -2·p`, and `q >= -p - 3` (no edge).
        ("wedge", vec![(-1, 1, 0), (2, 1, 0), (1, 1, 3)]),
        // `0 <= p + q <= 2`, and a looser copy.
        ("strip", vec![(1, 1, 0), (-1, -1, 2), (1, 1, 1)]),
        // `p + 2·q >= 3`, and a looser copy.
        ("half-plane", vec![(1, 2, -3), (2, 4, -1)]),
    ];
    // The names `α·p + β·q`, none with a common factor (an open class declines, as before)
    // and none crossing the strip in a stretch shorter than 1 (`3·p - 2·q` there is three
    // classes modulo 5, which no one class holds).
    let dirs: [(i64, i64); 8] = [
        (1, 0),
        (0, 1),
        (2, 3),
        (-1, 0),
        (1, -1),
        (3, 1),
        (-2, -3),
        (1, 1),
    ];
    // Every value of the window has a point in the box where it has one at all (`-p == -40`
    // over the tangents needs `q >= 444`).
    let (pbox, qbox, window) = (120i64, 600i64, 40i64);
    for (region, halves) in &regions {
        let y = |j: usize| format!("y{j}");
        let mut rows: Vec<Formula> = dirs
            .iter()
            .enumerate()
            .map(|(j, &(al, be))| eq(&[(&y(j), 1), ("p", -al), ("q", -be)], 0))
            .collect();
        rows.extend(
            halves
                .iter()
                .map(|&(a_, b, c)| ge(&[("p", a_), ("q", b)], c)),
        );
        let f = Formula::And(Shared::new(rows));
        let syms: Vec<Atom> = (0..dirs.len()).map(|j| a(&y(j))).collect();
        let sets = dirs
            .iter()
            .map(|_| Ok(IntervalSet::from_pieces(vec![(End::NegInf, End::PosInf)])))
            .collect();
        EXACT_WORK.set(0);
        FAST_WORK.set(0);
        let got = exact_each(&f, &syms, (sets, vec![]), SOLVER);
        let covered = EXACT_WORK.replace(0) - FAST_WORK.replace(0);
        let mut want = vec![std::collections::BTreeSet::new(); dirs.len()];
        for p in -pbox..=pbox {
            for q in -qbox..=qbox {
                if halves.iter().all(|&(a_, b, c)| a_ * p + b * q + c >= 0) {
                    for (j, &(al, be)) in dirs.iter().enumerate() {
                        want[j].insert(al * p + be * q);
                    }
                }
            }
        }
        for (j, want) in want.iter().enumerate() {
            let Ok(set) = &got.sets[j] else {
                panic!("{region}: y{j} refused: {:?}", got.sets[j]);
            };
            for v in -window..=window {
                let has = set.ranges.contains(v) && set.class.contains(&Num::from(v));
                assert_eq!(has, want.contains(&v), "{region}: y{j} at {v}: {set:?}");
            }
        }
        assert_eq!(covered, 0, "{region}: a name was covered");
    }
}

/// `y(j) == 2·p + 3·q + j` with `0 <= p, q <= 9` and one choice, `z == max(p, q)` (`z == p`
/// where `p - q >= 0`, `z == q` where `q - p - 1 >= 0`), under `z <= 7`: the choice splits the
/// polygon in two, and the part is still read once, not once a name (PRES-two-pin-choices).
#[test]
fn names_beside_a_choice_are_read_once_for_the_part() {
    let used = exact_work_of(|k| {
        let (f, syms, _) = two_free_atoms(2, 3)(k);
        let Formula::And(rows) = &f else {
            unreachable!()
        };
        let mut rows: Vec<Formula> = rows.iter().cloned().collect();
        rows.push(Formula::or(vec![
            Formula::And(Shared::new(vec![
                eq(&[("z", 1), ("p", -1)], 0),
                ge(&[("p", 1), ("q", -1)], 0),
            ])),
            Formula::And(Shared::new(vec![
                eq(&[("z", 1), ("q", -1)], 0),
                ge(&[("q", 1), ("p", -1)], -1),
            ])),
        ]));
        rows.push(ge(&[("z", -1)], 7));
        let sets = (0..k as i64).map(|j| IntervalSet::of(j, j + 35)).collect();
        (Formula::And(Shared::new(rows)), syms, sets)
    });
    let ratio = used[1] as f64 / used[0].max(1) as f64;
    assert!(ratio < 10.5, "work {used:?}, {ratio:.2} times at 8 times k");
}

/// `0 <= p, q <= 9` and a choice for each name, `y(j) == p + 2·q + j` where `p - q - m >= 0`,
/// else `y(j) == 2·p + q + j`, with `m = j mod 7`: each choice is read by nothing else (a
/// leaf), so the part is one cell and each name two queries on it, not a reading of its own
/// (PRES-two-pin-choices). (Arms of steps 2 and 3, as `2·p` and `3·q`, would decline: no one
/// class holds the union.)
#[test]
fn names_each_with_a_choice_of_its_own_are_read_once_for_the_part() {
    let used = exact_work_of(|k| {
        let y = |j: usize| format!("y{j}");
        let mut rows: Vec<Formula> = (0..k)
            .map(|j| {
                let (yj, m) = (y(j), (j % 7) as i64);
                Formula::or(vec![
                    Formula::And(Shared::new(vec![
                        eq(&[(&yj, 1), ("p", -1), ("q", -2)], -(j as i64)),
                        ge(&[("p", 1), ("q", -1)], -m),
                    ])),
                    Formula::And(Shared::new(vec![
                        eq(&[(&yj, 1), ("p", -2), ("q", -1)], -(j as i64)),
                        ge(&[("q", 1), ("p", -1)], m - 1),
                    ])),
                ])
            })
            .collect();
        rows.extend([ge(&[("p", 1)], 0), ge(&[("p", -1)], 9)]);
        rows.extend([ge(&[("q", 1)], 0), ge(&[("q", -1)], 9)]);
        let syms: Vec<Atom> = (0..k).map(|j| a(&y(j))).collect();
        let sets = (0..k as i64).map(|j| IntervalSet::of(j, j + 27)).collect();
        (Formula::And(Shared::new(rows)), syms, sets)
    });
    let ratio = used[1] as f64 / used[0].max(1) as f64;
    assert!(ratio < 10.5, "work {used:?}, {ratio:.2} times at 8 times k");
}

/// `0 <= p, q <= 9`, a shared choice `z == max(p, q)` under `2 <= z <= 7`, and names over it:
/// a common factor 2 in both cells (`y0`, `y1`), `z` itself in a sum (`y2`, `2·p - q` and `p`
/// on the two cells; `z + 3·q` would be `p + 3·q` and `4·q`, two steps, which no one class
/// holds, so it would decline like `y5`), leaf choices with
/// even arms (`y3`), constant arms (`y4`), arms of residues 0 and 1 (`y5`, which declines to
/// the cover), and an arm whose guard is false on the whole part (`y6`). Each set is exactly
/// the values at the integer points counted one by one, and every name but `y5` is answered
/// with no question of the cover (PRES-two-pin-choices).
#[test]
fn names_over_a_choice_are_exact() {
    let choice = |y: &str, guard: &[(&str, i64)], c: i64, arms: [(&[(&str, i64)], i64); 2]| {
        let neg: Vec<(&str, i64)> = guard.iter().map(|&(s, k)| (s, -k)).collect();
        let arm = |(terms, d): (&[(&str, i64)], i64)| {
            let mut t = vec![(y, 1)];
            t.extend(terms.iter().map(|&(s, k)| (s, -k)));
            eq(&t, -d)
        };
        Formula::or(vec![
            Formula::And(Shared::new(vec![arm(arms[0]), ge(guard, c)])),
            Formula::And(Shared::new(vec![arm(arms[1]), ge(&neg, -c - 1)])),
        ])
    };
    let rows = vec![
        ge(&[("p", 1)], 0),
        ge(&[("p", -1)], 9),
        ge(&[("q", 1)], 0),
        ge(&[("q", -1)], 9),
        choice(
            "z",
            &[("p", 1), ("q", -1)],
            0,
            [(&[("p", 1)], 0), (&[("q", 1)], 0)],
        ),
        ge(&[("z", -1)], 7),
        ge(&[("z", 1)], -2),
        eq(&[("y0", 1), ("p", -2), ("q", -2)], 0),
        eq(&[("y1", 1), ("z", -2)], -1),
        eq(&[("y2", 1), ("z", -1), ("p", -1), ("q", 1)], 0),
        choice("y3", &[("p", 1)], -4, [(&[("q", 2)], 0), (&[("p", 2)], 0)]),
        choice("y4", &[("q", 1), ("p", -1)], 0, [(&[], 5), (&[], 9)]),
        choice("y5", &[("p", 1)], -5, [(&[("q", 2)], 0), (&[("q", 2)], 1)]),
        choice(
            "y6",
            &[("p", 1), ("q", 1)],
            -20,
            [(&[("q", 1)], 0), (&[("p", 1)], 30)],
        ),
    ];
    let f = Formula::And(Shared::new(rows));
    let value = |name: &str, p: i64, q: i64| {
        let z = p.max(q);
        match name {
            "y0" => 2 * p + 2 * q,
            "y1" => 2 * z + 1,
            "y2" => z + p - q,
            "y3" => {
                if p >= 4 {
                    2 * q
                } else {
                    2 * p
                }
            }
            "y4" => {
                if q >= p {
                    5
                } else {
                    9
                }
            }
            "y5" => {
                if p >= 5 {
                    2 * q
                } else {
                    2 * q + 1
                }
            }
            _ => {
                if p + q >= 20 {
                    q
                } else {
                    p + 30
                }
            }
        }
    };
    let names = ["y0", "y1", "y2", "y3", "y4", "y5", "y6"];
    let run = |names: &[&str]| {
        let syms: Vec<Atom> = names.iter().map(|s| a(s)).collect();
        let sets = names
            .iter()
            .map(|_| Ok(IntervalSet::from_pieces(vec![(End::NegInf, End::PosInf)])))
            .collect();
        EXACT_WORK.set(0);
        FAST_WORK.set(0);
        let got = exact_each(&f, &syms, (sets, vec![]), SOLVER);
        let covered = EXACT_WORK.replace(0) - FAST_WORK.replace(0);
        (got, covered)
    };
    let (got, _) = run(&names);
    for (j, name) in names.iter().enumerate() {
        let mut want = std::collections::BTreeSet::new();
        for p in 0..=9 {
            for q in 0..=9 {
                if (2..=7).contains(&p.max(q)) {
                    want.insert(value(name, p, q));
                }
            }
        }
        let Ok(set) = &got.sets[j] else {
            panic!("{name} refused: {:?}", got.sets[j]);
        };
        for v in -100..=100i64 {
            let has = set.ranges.contains(v) && set.class.contains(&Num::from(v));
            assert_eq!(has, want.contains(&v), "{name} at {v}: {set:?}");
        }
    }
    let (_, covered) = run(&["y0", "y1", "y2", "y3", "y4", "y6"]);
    assert_eq!(covered, 0, "a name was covered");
}

/// `0 <= p, q <= 9`, three shared choices `z(i) == q + 1` where `p - i >= 0`, else
/// `z(i) == q - 1`, for `i` from 1 to 3, each read by `z(i) >= -100`, and names
/// `y(j) == 2·p + 3·q + j` for `j < 8`. Of the 8 cells of the three guards only 4 have
/// points (`p <= 0`, `p == 1`, `p == 2`, `p >= 3`); at a choice whose one arm would make the
/// cell empty, the reading takes the other arm and goes on, so no empty cell is read and the
/// search reads 7 times (2·4 - 1, a binary tree with the 4 cells as leaves), not 15 (every
/// cell of the 8), and each set is exact (PRES-two-pin-prune, part b).
#[test]
fn empty_cells_are_pruned_before_they_are_read() {
    let y = |j: usize| format!("y{j}");
    let z = |i: i64| format!("z{i}");
    let mut rows: Vec<Formula> = (0..8)
        .map(|j| eq(&[(&y(j), 1), ("p", -2), ("q", -3)], -(j as i64)))
        .collect();
    for i in 1..=3 {
        let zi = z(i);
        rows.push(Formula::or(vec![
            Formula::And(Shared::new(vec![
                eq(&[(&zi, 1), ("q", -1)], -1),
                ge(&[("p", 1)], -i),
            ])),
            Formula::And(Shared::new(vec![
                eq(&[(&zi, 1), ("q", -1)], 1),
                ge(&[("p", -1)], i - 1),
            ])),
        ]));
        rows.push(ge(&[(&zi, 1)], 100));
    }
    rows.extend([ge(&[("p", 1)], 0), ge(&[("p", -1)], 9)]);
    rows.extend([ge(&[("q", 1)], 0), ge(&[("q", -1)], 9)]);
    let f = Formula::And(Shared::new(rows));
    let syms: Vec<Atom> = (0..8).map(|j| a(&y(j))).collect();
    let sets = (0..8)
        .map(|_| Ok(IntervalSet::from_pieces(vec![(End::NegInf, End::PosInf)])))
        .collect();
    EXACT_WORK.set(0);
    FAST_WORK.set(0);
    TWO_PIN_READINGS.set(0);
    let got = exact_each(&f, &syms, (sets, vec![]), SOLVER);
    let readings = TWO_PIN_READINGS.replace(0);
    let covered = EXACT_WORK.replace(0) - FAST_WORK.replace(0);
    let mut want = std::collections::BTreeSet::new();
    for p in 0..=9 {
        for q in 0..=9 {
            want.insert(2 * p + 3 * q);
        }
    }
    for j in 0..8i64 {
        let Ok(set) = &got.sets[j as usize] else {
            panic!("y{j} refused: {:?}", got.sets[j as usize]);
        };
        for v in -10..=60i64 {
            let has = set.ranges.contains(v) && set.class.contains(&Num::from(v));
            assert_eq!(has, want.contains(&(v - j)), "y{j} at {v}: {set:?}");
        }
    }
    assert_eq!(covered, 0, "a name was covered");
    assert_eq!(readings, 7, "the readings of the part");
}

/// The search stop of the two-pin reading where the pass before it counts nothing: a choice
/// `a + b == p` where `p >= 0`, else `a + b == -p`, with `b >= 0`. Its possible heads are `a`,
/// read by nothing else (so the choice could be a leaf, and the pass does not count it), and
/// `b`; but the reading makes `p` its first pin and `a` its second, so `b` is the head, read by
/// `b >= 0`, and the choice splits the part. With one name two cells would cost more than the
/// per-name path, and the search stops at that branch after one reading; with two it reads the
/// part and both cells (PRES-two-pin-prune).
#[test]
fn a_choice_shared_only_through_the_head_the_reading_gives_it_stops_the_search() {
    let f = Formula::And(Shared::new(vec![
        Formula::or(vec![
            Formula::And(Shared::new(vec![
                eq(&[("a", 1), ("b", 1), ("p", -1)], 0),
                ge(&[("p", 1)], 0),
            ])),
            Formula::And(Shared::new(vec![
                eq(&[("a", 1), ("b", 1), ("p", 1)], 0),
                ge(&[("p", -1)], -1),
            ])),
        ]),
        ge(&[("b", 1)], 0),
    ]));
    for (names, read, readings) in [(1, false, 1), (2, true, 3)] {
        let mut work = Work {
            used: 0,
            limit: u64::MAX,
            solver: SOLVER,
        };
        let prep = guarded::prepare(&f, &mut work).unwrap().unwrap();
        TWO_PIN_READINGS.set(0);
        let got = prep.two_pins(names, &mut work).unwrap();
        assert_eq!(got.is_some(), read, "with {names} names");
        assert_eq!(TWO_PIN_READINGS.replace(0), readings, "with {names} names");
    }
}

/// A leaf choice for each name over a polygon of many true edges: `y(j) == p + 2·q + j` where
/// `q - 4·p - m >= 0`, else `y(j) == 2·p + q + j`, `m = j mod 7`, over the tangents of
/// `names_over_a_polygon_of_many_true_edges_cost_log_of_them`. Each arm's query is over the
/// polygon cut by its guard, which is clipped in O(log V) rather than its edges found again in
/// O(V log V) (PRES-two-pin-prune, part c).
fn leaf_choices_over_tangents(k: usize, open: bool) -> (Formula, Vec<Atom>, Vec<IntervalSet>) {
    let y = |j: usize| format!("y{j}");
    let kk = k as i64;
    let mut rows: Vec<Formula> = (0..k)
        .map(|j| {
            let (yj, m) = (y(j), (j % 7) as i64);
            Formula::or(vec![
                Formula::And(Shared::new(vec![
                    eq(&[(&yj, 1), ("p", -1), ("q", -2)], -(j as i64)),
                    ge(&[("q", 1), ("p", -4)], -m),
                ])),
                Formula::And(Shared::new(vec![
                    eq(&[(&yj, 1), ("p", -2), ("q", -1)], -(j as i64)),
                    ge(&[("q", -1), ("p", 4)], m - 1),
                ])),
            ])
        })
        .collect();
    rows.extend((0..=kk).map(|j| ge(&[("q", 1), ("p", -2 * j)], j * j)));
    rows.push(ge(&[("p", 1)], kk));
    if !open {
        rows.push(ge(&[("q", -1)], kk * kk));
    }
    let syms: Vec<Atom> = (0..k).map(|j| a(&y(j))).collect();
    let sets = (0..k)
        .map(|_| IntervalSet::from_pieces(vec![(End::NegInf, End::PosInf)]))
        .collect();
    (Formula::And(Shared::new(rows)), syms, sets)
}

/// Leaf choices over many true edges (`leaf_choices_over_tangents`): before
/// PRES-two-pin-prune each query found the cut polygon's edges again, O(V log V) a name.
#[test]
fn leaf_choices_over_a_polygon_of_many_true_edges_cost_log_of_them() {
    for open in [false, true] {
        let used = exact_work_of(|k| leaf_choices_over_tangents(k, open));
        // O(k log k) a part and O(log k) a name: 11 times at 8 times k, as above (P300).
        let ratio = used[1] as f64 / used[0].max(1) as f64;
        assert!(
            ratio <= 11.0,
            "open {open}: work {used:?}, {ratio:.2} times at 8 times k"
        );
    }
}

/// Each name: the guard `(A, B, C)` and the arms `(α, β)`, `y == α·p + β·q`.
type Leaf = ((i64, i64, i64), [(i64, i64); 2]);

/// The sets of the names `y(j)`, each a leaf choice of `leaves[j]`, over the tangents of
/// `leaf_choices_over_tangents` at k = 6 (closed under `q <= 36`, or open), checked against the
/// values at the integer points counted one by one; returns the work the cover spent.
fn leaf_choices_checked(leaves: &[Leaf], open: bool) -> u64 {
    let k = 6i64;
    {
        let y = |j: usize| format!("y{j}");
        let mut rows: Vec<Formula> = leaves
            .iter()
            .enumerate()
            .map(|(j, &((ga, gb, gc), [(a0, b0), (a1, b1)]))| {
                let yj = y(j);
                Formula::or(vec![
                    Formula::And(Shared::new(vec![
                        eq(&[(&yj, 1), ("p", -a0), ("q", -b0)], 0),
                        ge(&[("p", ga), ("q", gb)], gc),
                    ])),
                    Formula::And(Shared::new(vec![
                        eq(&[(&yj, 1), ("p", -a1), ("q", -b1)], 0),
                        ge(&[("p", -ga), ("q", -gb)], -gc - 1),
                    ])),
                ])
            })
            .collect();
        rows.extend((0..=k).map(|j| ge(&[("q", 1), ("p", -2 * j)], j * j)));
        rows.push(ge(&[("p", 1)], k));
        if !open {
            rows.push(ge(&[("q", -1)], k * k));
        }
        let f = Formula::And(Shared::new(rows));
        let syms: Vec<Atom> = (0..leaves.len()).map(|j| a(&y(j))).collect();
        let sets = leaves
            .iter()
            .map(|_| Ok(IntervalSet::from_pieces(vec![(End::NegInf, End::PosInf)])))
            .collect();
        EXACT_WORK.set(0);
        FAST_WORK.set(0);
        let got = exact_each(&f, &syms, (sets, vec![]), SOLVER);
        let covered = EXACT_WORK.replace(0) - FAST_WORK.replace(0);
        let mut want = vec![std::collections::BTreeSet::new(); leaves.len()];
        for p in -k..=120 {
            for q in 0..=600 {
                let inside = (0..=k).all(|j| q - 2 * j * p + j * j >= 0) && (open || q <= k * k);
                if !inside {
                    continue;
                }
                for (j, &((ga, gb, gc), [(a0, b0), (a1, b1)])) in leaves.iter().enumerate() {
                    want[j].insert(if ga * p + gb * q + gc >= 0 {
                        a0 * p + b0 * q
                    } else {
                        a1 * p + b1 * q
                    });
                }
            }
        }
        for (j, want) in want.iter().enumerate() {
            let Ok(set) = &got.sets[j] else {
                panic!("open {open}: y{j} refused: {:?}", got.sets[j]);
            };
            for v in -40..=40i64 {
                let has = set.ranges.contains(v) && set.class.contains(&Num::from(v));
                assert_eq!(has, want.contains(&v), "open {open}: y{j} at {v}: {set:?}");
            }
        }
        covered
    }
}

/// Leaf choices whose guards cut the tangents (closed under `q <= 36` and open) across, touch
/// them at a corner (`-p - q - 6 >= 0`, only `(-6, 0)`) or along an edge (`-p - 6 >= 0`, in the
/// open case the ray `p == -6`, `q >= 0`), miss them (`-p - 100 >= 0`) or hold on all of them
/// (`q + 1000 >= 0`): each set is exactly the values at the integer points, counted one by one,
/// with no question of the cover (PRES-two-pin-prune, part c). On the ray `p == -6` an arm
/// `y == p + 2·q` takes the even values from -6 on, infinitely many and periodic, which no runs
/// of `u` give: there the reading declines (the module note of `two_pins`), and the cover
/// answers the name exactly.
#[test]
fn leaf_choices_over_many_edges_are_exact() {
    let leaves: [Leaf; 6] = [
        ((-4, 1, -1), [(1, 2), (2, 1)]),
        ((-1, -1, -6), [(1, 2), (2, 1)]),
        ((-1, 0, -6), [(0, 1), (1, 2)]),
        ((-1, 0, -100), [(1, 2), (2, 1)]),
        ((0, 1, 1000), [(1, 2), (2, 1)]),
        ((1, 0, -3), [(0, 1), (1, 0)]),
    ];
    for open in [false, true] {
        let covered = leaf_choices_checked(&leaves, open);
        assert_eq!(covered, 0, "open {open}: a name was covered");
    }
    let periodic: [Leaf; 1] = [((-1, 0, -6), [(1, 2), (0, 1)])];
    assert_eq!(leaf_choices_checked(&periodic, false), 0, "closed: covered");
    assert!(
        leaf_choices_checked(&periodic, true) > 0,
        "open: the periodic values on the ray were answered by the reading"
    );
}

/// The two-pin reading on a polygon with slanted sides, where the dark shadow is narrower
/// than the real one and values between them are tried one by one, and on names with a common
/// factor and with none: each set agrees with the cover alone (`guarded::two_pins`).
#[test]
fn the_two_pin_reading_agrees_with_the_cover_on_slanted_sides() {
    let f = Formula::And(Shared::new(vec![
        eq(&[("y", 1), ("p", -3), ("q", -5)], 0),
        eq(&[("z", 1), ("p", -4), ("q", 6)], -1),
        eq(&[("v", 1), ("p", -7), ("q", -2)], 0),
        ge(&[("p", 1)], 0),
        ge(&[("q", 1)], 0),
        ge(&[("p", -2), ("q", -3)], 40),
        ge(&[("p", -1), ("q", 1)], 7),
        Formula::Not(Shared::new(ge(&[("p", 1), ("q", -3)], 0))),
    ]));
    let syms: Vec<Atom> = ["y", "z", "v", "p", "q"].iter().map(|s| a(s)).collect();
    let run = |off: bool| {
        GUARDED_OFF.set(off);
        let got = exact_each(
            &f,
            &syms,
            (vec![Ok(IntervalSet::of(-1000, 1000)); syms.len()], vec![]),
            SOLVER,
        );
        GUARDED_OFF.set(false);
        format!("{:?}", got.sets)
    };
    assert_eq!(run(false), run(true));
}

/// Names tied with both signs and nonzero shifts (`b = 5 - a`, `c = a - 3`, `d = -c - 2`,
/// with `e` in a second class over `e + f - s == 0`): each set moved from the first name of
/// its class certified agrees with the cover alone, name by name, with every name asked.
#[test]
fn names_tied_with_both_signs_are_moved_exactly() {
    let f = Formula::And(Shared::new(vec![
        eq(&[("b", 1), ("a", 1)], -5),
        eq(&[("c", 1), ("a", -1)], 3),
        eq(&[("d", 1), ("c", 1)], 2),
        eq(&[("e", 1), ("f", -1)], 0),
        ge(&[("a", 1)], 0),
        ge(&[("a", -1)], 9),
        ge(&[("f", 1)], 2),
        ge(&[("f", -1)], 4),
    ]));
    let names = ["a", "b", "c", "d", "e", "f"];
    let want = [(0, 9), (-4, 5), (-3, 6), (-8, 1), (-2, 4), (-2, 4)];
    let syms: Vec<Atom> = names.iter().map(|s| a(s)).collect();
    let run = |off: bool| {
        GUARDED_OFF.set(off);
        let each = want
            .iter()
            .map(|&(l, h)| Ok(IntervalSet::of(l, h)))
            .collect();
        let got = exact_each(&f, &syms, (each, vec![]), SOLVER);
        GUARDED_OFF.set(false);
        EXACT_WORK.set(0);
        FAST_WORK.set(0);
        got.sets
            .into_iter()
            .map(|g| g.unwrap().ranges)
            .collect::<Vec<_>>()
    };
    let on = run(false);
    assert_eq!(on, run(true));
    for ((s, got), &(l, h)) in names.iter().zip(&on).zip(&want) {
        assert_eq!(got, &IntervalSet::of(l, h), "{s}");
    }
    // Two pieces, one without end: `b = 5 - a` reverses them and moves each end.
    let mut work = Work {
        used: 0,
        limit: u64::MAX,
        solver: SOLVER,
    };
    let prep = guarded::prepare(&f, &mut work).unwrap().unwrap();
    let set = IntervalSet::from_pieces(vec![(End::NegInf, End::of(0)), (End::of(3), End::of(4))]);
    let moved = IntervalSet::from_pieces(vec![(End::of(1), End::of(2)), (End::of(5), End::PosInf)]);
    assert_eq!(prep.carried(&a("b"), &a("a"), &set), Some(moved));
    assert_eq!(prep.carried(&a("e"), &a("a"), &set), None);
}

/// The chain `c(j+1) == c(j) + 1` for `j < k`, with `0 <= c0 <= 9`, every name asked with its
/// exact set `j..=j+9`: each answered by the certificate, the part read for the names together,
/// not once a name, O(k) in all and not O(k²) (PRES-groupA-forward-per-name-order).
#[test]
fn the_names_of_a_chain_of_unit_equations_are_certified_together() {
    let mut used = Vec::new();
    for k in [64, 512] {
        let c = |j: usize| format!("c{j}");
        let mut rows: Vec<Formula> = (0..k)
            .map(|j| eq(&[(&c(j + 1), 1), (&c(j), -1)], -1))
            .collect();
        rows.push(ge(&[("c0", 1)], 0));
        rows.push(ge(&[("c0", -1)], 9));
        let f = Formula::And(Shared::new(rows));
        let syms: Vec<Atom> = (0..=k).map(|j| a(&c(j))).collect();
        let want: Vec<IntervalSet> = (0..=k)
            .map(|j| IntervalSet::of(j as i64, j as i64 + 9))
            .collect();
        let each = want.iter().cloned().map(Ok).collect();
        EXACT_WORK.set(0);
        FAST_WORK.set(0);
        let got = exact_each(&f, &syms, (each, vec![]), SOLVER);
        let fast = FAST_WORK.replace(0);
        used.push(fast);
        assert_eq!(
            EXACT_WORK.replace(0) - fast,
            0,
            "a name was covered at k = {k}"
        );
        assert_eq!(got.sets.len(), want.len());
        for (g, w) in got.sets.iter().zip(&want) {
            assert_eq!(&g.as_ref().unwrap().ranges, w, "at k = {k}");
        }
    }
    let ratio = used[1] as f64 / used[0].max(1) as f64;
    assert!(ratio < 10.5, "work {used:?}, {ratio:.2} times at 8 times k");
}
