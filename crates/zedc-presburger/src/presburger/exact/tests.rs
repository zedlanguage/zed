use super::super::meter::SOLVER_STEP;
use super::super::{SOLVER, Shared, member, project_each_exact};
use super::*;

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
    let seed = crate::seed::seed("random_formulas_project_to_the_values_of_their_points");
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
                Ok(Err(e)) | Err(e) => refused.push(format!("round {round} {n}: {e:?}")),
            }
        }
    }
    println!("seed {seed}: {wider_before} wider before, refused {refused:#?}");
    assert!(wrong.is_empty(), "seed {seed}: {wrong:#?}");
    assert!(refused.len() <= 3, "seed {seed}: {refused:#?}");
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

/// A value that each disjunction allows through a different disjunct, where no one
/// combination of them does: `(x == 1 && y == 0 || x == 3 && y == 1) && (x == 1 && y == 1 ||
/// x == 3 && y == 0)` has no point, while the solver's meet of the unions of hulls keeps
/// x in {1, 3}.
#[test]
fn values_two_disjunctions_allow_only_apart_are_left_out() {
    let d = |p: i64, q: i64, r: i64, s: i64| {
        Formula::or(vec![
            Formula::and(vec![eq(&[("x", 1)], -p), eq(&[("y", 1)], -q)]),
            Formula::and(vec![eq(&[("x", 1)], -r), eq(&[("y", 1)], -s)]),
        ])
    };
    let f = boxed(Formula::and(vec![d(1, 0, 3, 1), d(1, 1, 3, 0)]));
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

/// The work limit on both sides: allowed exactly the work the cover of [`evens`] takes, the
/// solver's work for its questions included and that of its fast path left out (`tried`:
/// `direct` reads the rows of `evens` and fails, a projected disjunction grouped with the
/// bound on `z`), it answers with the exact set (the even values); allowed one unit
/// less, it refuses ([`Refusal::Questions`]) and never answers with the solver's set, which
/// has values with no point (PRES-pugh-work-budget). The work is counted, so a second run
/// uses the same. Before `tried` had an allowance of its own, the failed fast path was
/// charged to the limit, and the cover was refused at the limit its loop needs.
#[test]
fn the_work_limit_is_met_alike_on_both_sides() {
    let f = evens(20);
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
                    );
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
    let skipped = tried(&mut zero, SOLVER, |w| direct(&f, &a("x"), w));
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
