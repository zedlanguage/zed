//! Plan item PERF-ref-memo-quadratic: the reference transfer (`zedc::store::preimage_ref`)
//! without its quadratic memo. Two kinds of test:
//!
//! - the answers: every call of main's answer dump (2cb726965, 182,747 calls) whose answer the
//!   new transfer changed is kept here with main's answer (`ref_memo_changed.txt`), as are calls
//!   22, 45 and 86 of the audit of that dump (`ref_memo_pinned.txt`); each new answer must lie
//!   inside main's box, keep main's exactness and relation, and agree with the interpreter at
//!   the points near every end of the input, of main's box and of the new one, and in
//!   [-60, 60]. The other 182,327 calls give main's answer unchanged; the dump is 126 MB, so
//!   that replay was run once, outside the tests (COMPLEXITY.md C56);
//! - the scaling, in `bench::ref_memo`: each of the 48 families of the item's benchmark at n
//!   and 8n, held to the plan's limit (`scaling::LIMIT`) in instructions and bytes, with no
//!   wider limit for any family; each answer grows at most 8 times (`output_grid` demands four
//!   values, 4n pieces).
//!   The work of writing out a larger answer is held at one n by
//!   `output_grid_work_grows_with_its_answer`, and `nested_moduli_eq_4096` with its costly
//!   constants next to the root at every n is ignored with its plan row,
//!   REF-nested-moduli-state.

use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

use num_bigint::BigInt;
use zed_kernel::{Prim, Shared, Term, Value, eval};
use zed_tests::instances::Rng;
use zed_tests::step_helpers::l01_38_presburger::solver_alone;
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::preimage_ref::{Demand, Domains, Listed, Preimage, preimage, preimage_listed};

use super::s22::{bits, chain, i_in, int, over, prim, var};

// ---- Main's answers ----

const CHANGED: &str = include_str!("ref_memo_changed.txt");
const PINNED: &str = include_str!("ref_memo_pinned.txt");

/// A call of the dump and main's answer to it.
struct Call {
    term: Term,
    inputs: Domains,
    listed: Listed,
    demand: Demand,
    main: Domains,
    main_exact: bool,
    main_relation: bool,
}

/// A set written `lo..hi,lo..hi`, an empty end an infinity.
fn set(s: &str) -> IntervalSet {
    let end = |e: &str, inf: End| {
        if e.is_empty() {
            inf
        } else {
            End::Fin(Num::from(e.parse::<BigInt>().expect("an integer end")))
        }
    };
    let pieces = s
        .split(',')
        .filter(|p| !p.is_empty())
        .map(|p| {
            let (lo, hi) = p.split_once("..").expect("a piece lo..hi");
            (end(lo, End::NegInf), end(hi, End::PosInf))
        })
        .collect();
    IntervalSet::from_pieces(pieces)
}

/// Domains written `x=set;y=set`.
fn domains(s: &str) -> Domains {
    s.split(';')
        .map(|d| {
            let (name, s) = d.split_once('=').expect("a domain name=set");
            (Arc::from(name), set(s))
        })
        .collect()
}

fn primitive(s: &str) -> Prim {
    match s {
        "Add" => Prim::Add,
        "Sub" => Prim::Sub,
        "Mul" => Prim::Mul,
        "IntDiv" => Prim::IntDiv,
        "Mod" => Prim::Mod,
        "Pow" => Prim::Pow,
        "Neg" => Prim::Neg,
        "Abs" => Prim::Abs,
        "Min" => Prim::Min,
        "Max" => Prim::Max,
        "Eq" => Prim::Eq,
        "Ne" => Prim::Ne,
        "Le" => Prim::Le,
        "Lt" => Prim::Lt,
        "Ge" => Prim::Ge,
        "Gt" => Prim::Gt,
        "And" => Prim::And,
        "Or" => Prim::Or,
        "Not" => Prim::Not,
        _ => panic!("no primitive {s}"),
    }
}

/// The term of a call, written as the dump writes it: its nodes in the order a depth-first
/// walk first meets them, `#k=Kind(args)`, a child written `tN`, `N` the number of the node
/// that walk gave it. Each node is built once, after its children (`built` is the visited set).
fn term(dag: &str) -> Term {
    struct Node<'a> {
        kind: &'a str,
        args: Vec<&'a str>,
        children: Vec<usize>,
    }
    let mut stack = vec![0];
    let mut nodes = HashMap::new();
    for def in dag.split(';').filter(|s| !s.is_empty()) {
        let raw = loop {
            let u = stack.pop().expect("a node for each definition");
            if !nodes.contains_key(&u) {
                break u;
            }
        };
        let (_, rhs) = def.split_once('=').expect("#k=Kind(args)");
        let (kind, args) = rhs.split_once('(').expect("Kind(args)");
        let args: Vec<&str> = args.strip_suffix(')').unwrap().split(',').collect();
        let first_child = match kind {
            "P" | "Let" => 1,
            "Lam" => args.len() - 1,
            "App" | "If" => 0,
            _ => args.len(),
        };
        let children: Vec<usize> = args[first_child..]
            .iter()
            .map(|a| a.strip_prefix('t').unwrap().parse().unwrap())
            .collect();
        stack.extend(children.iter().rev());
        nodes.insert(
            raw,
            Node {
                kind,
                args,
                children,
            },
        );
    }
    let mut built: HashMap<usize, Shared> = HashMap::new();
    let mut work = vec![(0, false)];
    while let Some((u, ready)) = work.pop() {
        if built.contains_key(&u) {
            continue;
        }
        let n = &nodes[&u];
        if !ready {
            work.push((u, true));
            work.extend(n.children.iter().map(|&c| (c, false)));
            continue;
        }
        let child = |i: usize| built[&n.children[i]].clone();
        let all = |from: usize| -> Vec<Term> {
            (from..n.children.len())
                .map(|i| (*child(i)).clone())
                .collect()
        };
        let t = match n.kind {
            "I" | "L" => {
                let v = Num::from(n.args[0].parse::<BigInt>().unwrap());
                Term::Lit(Value::from(&v))
            }
            "B" => Term::Lit(Value::Bool(n.args[0].parse().unwrap())),
            "V" => Term::Var(n.args[0].into()),
            "P" => Term::Prim(primitive(n.args[0]), all(0)),
            "Lam" => {
                let params = n.args[..n.args.len() - 1].iter();
                Term::Lam(params.map(|&p| p.into()).collect(), child(0))
            }
            "Let" => Term::Let(n.args[0].into(), child(0), child(1)),
            "If" => Term::If(child(0), child(1), child(2)),
            "App" => Term::App(child(0), all(1)),
            kind => panic!("no node kind {kind}"),
        };
        built.insert(u, Shared::new(t));
    }
    (*built[&0]).clone()
}

/// A line `dag inputs listed demand => domains marks`, tab-separated.
fn call(line: &str) -> Call {
    let f: Vec<&str> = line.split('\t').collect();
    let [dag, inputs, listed, demand, "=>", main, marks] = f[..] else {
        panic!("a line of seven fields: {line}");
    };
    Call {
        term: term(dag),
        inputs: domains(inputs),
        listed: listed
            .split(',')
            .filter(|n| *n != "-")
            .map(Arc::from)
            .collect(),
        demand: match demand {
            "true" | "false" => Demand::Bool(demand == "true"),
            _ => Demand::Ints(set(demand)),
        },
        main: domains(main),
        main_exact: marks.starts_with("exact"),
        main_relation: marks.ends_with(" rel"),
    }
}

/// Whether the name `x` occurs in `t`.
fn reads(t: &Term, x: &str) -> bool {
    match t {
        Term::Var(n) => &**n == x,
        Term::Lam(_, b) => reads(b, x),
        Term::Let(_, v, b) => reads(v, x) || reads(b, x),
        Term::If(g, a, b) => reads(g, x) || reads(a, x) || reads(b, x),
        Term::App(f, args) => reads(f, x) || args.iter().any(|a| reads(a, x)),
        Term::Prim(_, args) => args.iter().any(|a| reads(a, x)),
        _ => false,
    }
}

/// Whether `t` meets `d` with the inputs `names` at `point`; a failure does not.
fn meets(t: &Term, names: &[Arc<str>], point: &[Num], d: &Demand) -> bool {
    let bound = names.iter().zip(point).rev().fold(t.clone(), |t, (n, v)| {
        let v = Shared::new(Term::Lit(Value::from(v)));
        Term::Let(n.clone(), v, Shared::new(t))
    });
    eval(&bound).is_ok_and(|v| d.holds(&v))
}

/// The points at which the interpreter checks an answer: on each axis the values in
/// [-60, 60], the values within 2 of every end of the input, of main's box and of the new
/// box, and the ends of `i64`, those in the input; one value on an axis `t` does not read.
fn points(c: &Call, new: &Domains) -> Vec<Vec<Num>> {
    let mut all = vec![vec![]];
    for (name, input) in &c.inputs {
        let mut at: BTreeSet<Num> = (-60..=60).map(Num::from).collect();
        at.extend([i64::MIN, i64::MAX].map(Num::from));
        for s in [Some(input), c.main.get(name), new.get(name)]
            .into_iter()
            .flatten()
        {
            for (lo, hi) in s.pieces() {
                for v in [lo, hi].iter().filter_map(|e| match e {
                    End::Fin(v) => Some(v.clone()),
                    _ => None,
                }) {
                    at.extend((-2..=2).map(|k| &v + &Num::from(k)));
                }
            }
        }
        let mut axis: Vec<Num> = at
            .into_iter()
            .filter(|v| input.contains_end(&End::Fin(v.clone())))
            .collect();
        if !reads(&c.term, name) {
            axis.truncate(1);
        }
        all = all
            .into_iter()
            .flat_map(|p| {
                axis.iter().map(move |v| {
                    let mut q = p.clone();
                    q.push(v.clone());
                    q
                })
            })
            .collect();
    }
    all
}

/// How a new answer differs from main's.
#[derive(Debug, Default, PartialEq)]
struct Kept {
    same: usize,
    narrower: usize,
    made_exact: usize,
}

/// Checks the new answer to `line` against main's: inside main's box (or empty), exact where
/// main's was, with a relation or exact where main's had one, and sound and (when exact)
/// exact at [`points`] when `at_points`. Counts it in `kept`.
///
/// Main's answers are those of the solver alone, so they are compared with the solver alone
/// ([`solver_alone`]). The exact cover refuses a set it cannot confirm exact in place of
/// keeping the solver's wider set (PRES-pugh-work-budget), and the transfer then keeps the box
/// of the stage before, which can be wider than main's, with no relation (a call of part 2
/// keeps `i` in `-13..-6`, where main kept `-12..-5`; a call of each of parts 0, 1 and 3
/// loses main's relation; one call of `PINNED` is made exact): its answer is checked to be
/// sound and (when exact) exact at the points, and, when exact, inside main's box.
fn check_line(line: &str, kept: &mut Kept, at_points: bool) {
    let c = call(line);
    let covered: Preimage = preimage_listed(&c.term, &c.inputs, &c.listed, &c.demand);
    let p: Preimage = solver_alone(|| preimage_listed(&c.term, &c.inputs, &c.listed, &c.demand));
    let empty = p.domains.values().any(IntervalSet::is_empty);
    let inside = |n: &Arc<str>, s: &IntervalSet| c.main.get(n).is_none_or(|m| s.is_subset(m));
    assert!(
        empty || p.domains.iter().all(|(n, s)| inside(n, s)),
        "{line}\nthe new box is not inside main's: {:?}",
        p.domains
    );
    assert!(!c.main_exact || p.exact, "{line}\nmain's exactness lost");
    assert!(
        !c.main_relation || p.exact || p.relation.is_some(),
        "{line}\nmain's relation lost"
    );
    // An exact answer lies inside every sound one, so inside main's.
    let cover_empty = covered.domains.values().any(IntervalSet::is_empty);
    assert!(
        !covered.exact || cover_empty || covered.domains.iter().all(|(n, s)| inside(n, s)),
        "{line}\nthe cover's exact box is not inside main's: {:?}",
        covered.domains
    );
    let names: Vec<Arc<str>> = c.inputs.keys().cloned().collect();
    for (how, p) in [("new", &p), ("cover's", &covered)] {
        let at = if at_points {
            points(&c, &p.domains)
        } else {
            Vec::new()
        };
        for pt in at {
            let meets = meets(&c.term, &names, &pt, &c.demand);
            let hit = names.iter().zip(&pt).all(|(n, v)| {
                p.domains
                    .get(n)
                    .is_none_or(|s| s.contains_end(&End::Fin(v.clone())))
            });
            assert!(
                !meets || hit,
                "{line}\nthe point {pt:?} meets the demand outside the {how} box"
            );
            assert!(
                !p.exact || !hit || meets,
                "{line}\nthe point {pt:?} of the {how} box, marked exact, fails the demand"
            );
        }
    }
    if p.exact && !c.main_exact {
        kept.made_exact += 1;
    } else if p.domains != c.main {
        kept.narrower += 1;
    } else {
        kept.same += 1;
    }
}

fn lines(fixture: &str) -> impl Iterator<Item = &str> {
    fixture.lines().filter(|l| !l.starts_with("# "))
}

/// The 226 distinct calls of main's dump (420 with repeats) whose answer the new transfer
/// changes: each kept or made finer. 91 are made exact, 107 narrower and still inexact (90
/// and 108 until FAIL-project-each-coarser-seed, whose join of a disjunction left with one
/// disjunct makes one more call exact, all its inputs checked at its points; 85 and 113 until
/// FAIL-presburger-propagation-seed, whose merge of atoms defined alike lets
/// `decide` answer 5 tied questions it refused; all 226 calls checked at their points); 28
/// keep main's domains and exactness and differ in a stop, a listing, a relation or a
/// refusal, which the replay compares and this file does not keep. Every call is answered
/// and compared with main's box; the interpreter runs at the [`points`] of 5 calls of each part
/// drawn from a new seed each run. The calls are checked in four parts, the lines whose index
/// is `part` mod 4, each part with its own counts (`want`), which sum to those above. Until
/// TEST-bench-move-l0125 (author P169: a correctness test runs well under 1 s, a random one
/// takes fewer cases and a new seed each run) one test ran at the points of every call, 4.6 s;
/// one test of all the calls at the points of 20 took 1.7 s alone.
fn changed_answers_kept_or_made_finer(part: usize, want: Kept) {
    let test =
        format!("ref_memo::the_changed_answers_of_main_s_dump_are_kept_or_made_finer_{part}");
    let mut rng = Rng::new(super::run_seed(&test));
    let ours: Vec<usize> = (0..lines(CHANGED).count())
        .filter(|i| i % 4 == part)
        .collect();
    let at: BTreeSet<usize> = (0..5).map(|_| rng.pick(&ours)).collect();
    let mut kept = Kept::default();
    for (i, l) in lines(CHANGED).enumerate().filter(|(i, _)| i % 4 == part) {
        check_line(l, &mut kept, at.contains(&i));
    }
    assert_eq!(kept, want, "part {part}");
}

#[test]
fn the_changed_answers_of_main_s_dump_are_kept_or_made_finer_0() {
    changed_answers_kept_or_made_finer(
        0,
        Kept {
            same: 5,
            narrower: 27,
            made_exact: 25,
        },
    );
}

#[test]
fn the_changed_answers_of_main_s_dump_are_kept_or_made_finer_1() {
    changed_answers_kept_or_made_finer(
        1,
        Kept {
            same: 6,
            narrower: 30,
            made_exact: 21,
        },
    );
}

#[test]
fn the_changed_answers_of_main_s_dump_are_kept_or_made_finer_2() {
    changed_answers_kept_or_made_finer(
        2,
        Kept {
            same: 11,
            narrower: 23,
            made_exact: 22,
        },
    );
}

#[test]
fn the_changed_answers_of_main_s_dump_are_kept_or_made_finer_3() {
    changed_answers_kept_or_made_finer(
        3,
        Kept {
            same: 6,
            narrower: 27,
            made_exact: 23,
        },
    );
}

/// Calls 22, 45 and 86 of the audit of main's dump, whose answers the candidates of rounds 1
/// and 2 made coarser at first: main's answer or a finer one. Call 45 is
/// `(if (x < 3) { x * 5 } else { x * y }) div 3` over x in [10, 21], y in (-inf, 18], demand
/// (-inf, -7]: main answers y in (-inf, 0], not exact (the exact answer is y <= -1).
#[test]
fn calls_22_45_and_86_keep_main_s_answer_or_a_finer_one() {
    let kept = {
        let mut kept = Kept::default();
        lines(PINNED).for_each(|l| check_line(l, &mut kept, true));
        kept
    };
    assert_eq!(
        kept,
        Kept {
            same: 3,
            narrower: 0,
            made_exact: 0
        }
    );
}

// ---- Scaling ----

fn ne0(t: Term) -> Term {
    prim(Prim::Ne, t, int(0))
}

fn sub_c(c: i64, t: Term) -> Term {
    prim(Prim::Sub, int(c), t)
}

fn abs(t: Term) -> Term {
    Term::Prim(Prim::Abs, vec![t])
}

fn g_mod7(j: i64) -> Term {
    prim(Prim::Le, var("i"), int(j % 7 - 3))
}

fn g_lej(j: i64) -> Term {
    prim(Prim::Le, var("i"), int(j))
}

fn g_eqj(j: i64) -> Term {
    prim(Prim::Eq, var("i"), int(j))
}

/// `i` in `[-1_000_000, 1_000_000]`.
fn mega() -> Domains {
    i_in(-1_000_000, 1_000_000)
}

/// `i` and `m` in `[-1000, 1000]`.
fn i_and_m() -> Domains {
    over(&[
        ("i", IntervalSet::of(-1000, 1000)),
        ("m", IntervalSet::of(-1000, 1000)),
    ])
}

/// `(-inf, -3] ∪ [3, inf)`.
fn gap() -> Demand {
    Demand::Ints(IntervalSet::from_pieces(vec![
        (End::NegInf, End::of(-3)),
        (End::of(3), End::PosInf),
    ]))
}

/// The chain of `n` links over `i` with guards `i <= j` and else arms `op(j, t)`.
fn steps(n: usize, op: impl Fn(i64, Term) -> Term) -> Term {
    chain(n, var("i"), g_lej, op)
}

/// The chain `f(t, a(j), j mod 5)` of `n` calls of the named function `f(x, j, c) = if i <= j
/// { x } else { c - x }`.
fn named(n: usize, a: impl Fn(i64) -> i64) -> Term {
    let body = Term::If(
        Shared::new(prim(Prim::Le, var("i"), var("j"))),
        Shared::new(var("x")),
        Shared::new(prim(Prim::Sub, var("c"), var("x"))),
    );
    let lam = Term::Lam(vec!["x".into(), "j".into(), "c".into()], Shared::new(body));
    let t = (1..=n as i64).fold(var("i"), |t, j| {
        Term::App(Shared::new(var("f")), vec![t, int(a(j)), int(j % 5)])
    });
    Term::Let("f".into(), Shared::new(lam), Shared::new(t))
}

/// Remainders by `moduli[j mod len]` under the guards `guard`.
fn moduli(n: usize, guard: fn(i64) -> Term, ms: &'static [i64]) -> Term {
    moduli_from(n, guard, ms, 0)
}

/// [`moduli`] with link `j` taking the constants `(j + d) mod 5` and `ms[(j + d) mod len]`.
fn moduli_from(n: usize, guard: fn(i64) -> Term, ms: &'static [i64], d: i64) -> Term {
    chain(n, var("i"), guard, move |j, t| {
        let k = j + d;
        sub_c(k % 5, prim(Prim::Mod, t, int(ms[k as usize % ms.len()])))
    })
}

/// Four random chains of reflections `c - (t + s)` under random comparisons of `i`.
fn random_chains(n: usize) -> Vec<(Term, Domains, Demand)> {
    let mut rng = Rng::new(0x5eed_c4a1_u64);
    (0..4)
        .map(|k| {
            let (lo, hi, base) = if k % 2 == 0 {
                (10_000, 10_040, 10_020)
            } else {
                (10_000, 12_000, 10_000)
            };
            let mut t = var("i");
            for j in 1..=n as i64 {
                let cut = match k {
                    0 | 2 => base + rng.int(-4, 4),
                    1 => base + j + rng.int(-3, 3),
                    _ => base + rng.int(0, 1000),
                };
                let p = [Prim::Le, Prim::Ge, Prim::Lt, Prim::Gt, Prim::Eq, Prim::Ne][rng.below(6)];
                let (c, s) = (rng.int(-4, 4), rng.int(-1, 1));
                let shared = Shared::new(t);
                let inner = if s == 0 {
                    (*shared).clone()
                } else {
                    prim(Prim::Add, (*shared).clone(), int(s))
                };
                let refl = Shared::new(sub_c(c, inner));
                let (a, b) = if rng.below(2) == 0 {
                    (shared, refl)
                } else {
                    (refl, shared)
                };
                t = Term::If(Shared::new(prim(p, var("i"), int(cut))), a, b);
            }
            (ne0(t), i_in(lo, hi), Demand::Bool(true))
        })
        .collect()
}

/// The cases of the family `name` at size `n`: the families of the item's benchmark (run 3's
/// `prm_bench`, and the two of cross-review round 3), each a chain of `n` links.
pub(super) fn family(name: &str, n: usize) -> Vec<(Term, Domains, Demand)> {
    let ni = n as i64;
    let yes = Demand::Bool(true);
    let jmod5 = || chain(n, var("i"), g_mod7, |j, t| sub_c(j % 5, t));
    let one = |t: Term, ds: Domains| vec![(ne0(t), ds, Demand::Bool(true))];
    match name {
        "jmod5_narrow" => one(jmod5(), i_in(-20, 20)),
        "jmod5_wide" => one(jmod5(), i_in(-1000, 1000)),
        "jmod5_mega" => one(jmod5(), mega()),
        "jmod5_top" => one(jmod5(), over(&[("i", IntervalSet::top())])),
        "jmod5_ne100" => vec![(prim(Prim::Ne, jmod5(), int(100)), i_in(-1000, 1000), yes)],
        "const_base_wide" => one(
            chain(n, int(5), g_lej, |j, t| sub_c(j % 5, t)),
            i_in(-1000, 1000),
        ),
        "lambda_chain" => {
            let x: Arc<str> = "x".into();
            let t = (1..=ni).fold(var("i"), |acc, j| {
                let body = Term::If(
                    Shared::new(g_mod7(j)),
                    Shared::new(Term::Var(x.clone())),
                    Shared::new(sub_c(j % 5, Term::Var(x.clone()))),
                );
                let lam = Term::Lam(vec![x.clone()], Shared::new(body));
                Term::App(Shared::new(lam), vec![acc])
            });
            one(t, i_in(-1000, 1000))
        }
        "guarded_holes_narrow" | "guarded_holes_wide" => {
            let t = chain(n, var("i"), g_mod7, |j, t| sub_c(3 * j + 1, t));
            let w = if name.ends_with("narrow") { 20 } else { 10_000 };
            one(t, i_in(-w, w))
        }
        "const2_narrow" | "const2_wide" => {
            let t = chain(n, var("i"), g_mod7, |_, t| sub_c(2, t));
            let w = if name.ends_with("narrow") { 20 } else { 1000 };
            one(t, i_in(-w, w))
        }
        "i_le_j_narrow" | "i_le_j_wide" => {
            let w = if name.ends_with("narrow") { 20 } else { 1000 };
            one(steps(n, |j, t| sub_c(j % 5, t)), i_in(-w, w))
        }
        "pow2_wide" => one(steps(n, |j, t| sub_c(1 << ((j - 1) % 40), t)), mega()),
        "pow2_small" => one(steps(n, |j, t| sub_c(1 << (j - 1), t)), mega()),
        "let_chain" => {
            let t = (1..=ni).fold(var("i"), |acc, j| {
                let name: Arc<str> = format!("u{j}").into();
                let u = Term::Var(name.clone());
                let body = Term::If(
                    Shared::new(g_lej(j)),
                    Shared::new(u.clone()),
                    Shared::new(sub_c(j % 5, u)),
                );
                Term::Let(name, Shared::new(acc), Shared::new(body))
            });
            one(t, i_in(-1000, 1000))
        }
        "div_base_i_le_j" => {
            let base = prim(Prim::IntDiv, var("i"), int(3));
            one(
                chain(n, base, g_lej, |j, t| sub_c(j % 5, t)),
                i_in(-1000, 1000),
            )
        }
        "cross_2in" => {
            let t = chain(n, var("m"), g_lej, |j, t| sub_c(j % 5, t));
            let ds = over(&[
                ("i", IntervalSet::of(-100, 100)),
                ("m", IntervalSet::of(500, 600)),
            ]);
            one(t, ds)
        }
        "indep_const2" | "indep_small" => {
            let c = if name == "indep_small" { 2 } else { -10 };
            let bit = |j: i64| prim(Prim::Ge, var(&format!("b{j}")), int(1));
            one(chain(n, var("z"), bit, |_, t| sub_c(c, t)), bits(n, 1, 25))
        }
        "ne_guard_wide" => one(
            chain(n, var("i"), g_eqj, |j, t| sub_c(3 * j + 1, t)),
            i_in(-1000, 1000),
        ),
        "interleaved_wide" => {
            let half = ni / 2;
            let cut = move |j| {
                let c = if j <= half { 2 * j - 1 } else { 2 * (j - half) };
                prim(Prim::Le, var("i"), int(c))
            };
            one(
                chain(n, var("i"), cut, |j, t| sub_c(j % 5, t)),
                i_in(-1000, 1000),
            )
        }
        "random_chains" => random_chains(n),
        "pathological_abs" => {
            let g = |j| prim(Prim::Le, var("i"), int(2 * j));
            let t = chain(n, var("i"), g, |j, t| sub_c(j % 5 + 2, abs(t)));
            one(t, i_in(-1000, 1000))
        }
        "normal_add_base" | "normal_mul_base" => {
            let op = if name == "normal_add_base" {
                Prim::Add
            } else {
                Prim::Mul
            };
            let base = prim(op, var("i"), var("m"));
            one(chain(n, base, g_lej, |j, t| sub_c(j % 5, t)), i_and_m())
        }
        "normal_named" => one(named(n, |j| j), i_in(-1000, 1000)),
        "normal_named_modguard" => one(named(n, |j| j % 7 - 3), i_in(-1000, 1000)),
        "normal_min_gap" => {
            let t = steps(n, |j, t| sub_c(j % 5 + 4, prim(Prim::Min, t, int(20))));
            vec![(t, mega(), gap())]
        }
        "normal_mul_chain" | "normal_div_chain" | "normal_mod_chain" => {
            let (op, c) = match name {
                "normal_mul_chain" => (Prim::Mul, 2),
                "normal_div_chain" => (Prim::IntDiv, 2),
                _ => (Prim::Mod, 7),
            };
            one(steps(n, |j, t| sub_c(j % 5, prim(op, t, int(c)))), mega())
        }
        "normal_rel_guard" => {
            let g = |j| prim(Prim::Le, var("i"), prim(Prim::Add, var("m"), int(j)));
            one(chain(n, var("i"), g, |j, t| sub_c(j % 5, t)), i_and_m())
        }
        "normal_round_trip" | "normal_round_down" => {
            let (inner, outer) = if name == "normal_round_trip" {
                (Prim::Mul, Prim::IntDiv)
            } else {
                (Prim::IntDiv, Prim::Mul)
            };
            let t = steps(n, |j, t| {
                sub_c(6 * j + 2, prim(outer, prim(inner, t, int(2)), int(2)))
            });
            one(t, mega())
        }
        "normal_named_reflection" => {
            let lam = Term::Lam(
                vec!["c".into(), "x".into()],
                Shared::new(prim(Prim::Sub, var("c"), var("x"))),
            );
            let t = steps(n, |j, t| {
                Term::App(Shared::new(var("f")), vec![int(6 * j + 2), t])
            });
            let t = Term::Let("f".into(), Shared::new(lam), Shared::new(t));
            one(t, i_in(-1000, 1000))
        }
        "normal_mixed_moduli" => one(moduli(n, g_lej, &[3, 5, 7]), mega()),
        "normal_incompatible_moduli" => one(moduli(n, g_lej, &[64, 7, 2]), mega()),
        "nested_moduli_eq" => one(moduli(n, g_eqj, &[7, 64]), mega()),
        "nested_moduli_mod7" => one(moduli(n, g_mod7, &[7, 64]), mega()),
        "nested_moduli_946_eq" => one(moduli(n, g_eqj, &[9, 4, 6]), mega()),
        "nested_moduli_eq_4096" => one(moduli(n, g_eqj, &[7, 4096]), mega()),
        "normal_holey_guards" => {
            let g = |j| prim(Prim::Le, var("i"), int(4 * j));
            let t = chain(n, var("i"), g, |j, t| sub_c(j % 5, t));
            let ps = (0..ni).map(|j| (End::of(4 * j), End::of(4 * j))).collect();
            one(t, over(&[("i", IntervalSet::from_pieces(ps))]))
        }
        "output_grid" => vec![output_grid(n, 4)],
        "pathological_2var" => {
            let g = |j: i64| {
                let (v, at) = if j % 2 == 0 {
                    ("i", 2000 + j)
                } else {
                    ("m", j)
                };
                prim(Prim::Le, var(v), int(at))
            };
            let ds = over(&[
                ("i", IntervalSet::of(2000, 4000)),
                ("m", IntervalSet::of(-1000, 1000)),
            ]);
            one(chain(n, var("i"), g, |j, t| sub_c(j % 5, t)), ds)
        }
        // PROOF-preimage-ref-chain-cost: the shapes `Tx::back_doubt` names as kept on the old
        // memo. A guard `i + i <= j`, which `difference_guard` does not read (coefficient 2).
        "coef2_guard" => {
            let g = |j| prim(Prim::Le, prim(Prim::Add, var("i"), var("i")), int(j));
            one(
                chain(n, var("i"), g, |j, t| sub_c(j % 5, t)),
                i_in(-1000, 1000),
            )
        }
        // Guards on `i` and `m` in turn, both over `[-1000, 1000]`: the guards of two links
        // join to two coordinates.
        "alternating_2var" => {
            let g = |j: i64| prim(Prim::Le, var(if j % 2 == 0 { "i" } else { "m" }), int(j));
            one(chain(n, var("i"), g, |j, t| sub_c(j % 5, t)), i_and_m())
        }
        // `alternating_2var` on the base `m` (the Opus seat's `alt2var_m`,
        // PERF-ref-memo-multi-input round 3): the base input is not the one the first guard reads.
        "alt2var_m" => {
            let g = |j: i64| prim(Prim::Le, var(if j % 2 == 0 { "i" } else { "m" }), int(j));
            one(chain(n, var("m"), g, |j, t| sub_c(j % 5, t)), i_and_m())
        }
        // An independent bit per guard with centers that vary, so no common center.
        "indep_varying" => {
            let bit = |j: i64| prim(Prim::Ge, var(&format!("b{j}")), int(1));
            one(
                chain(n, var("z"), bit, |j, t| sub_c(j % 5, t)),
                bits(n, 1, 25),
            )
        }
        // Nested remainders by 7 and 64 under the guards of `alternating_2var`.
        "alternating_moduli" => {
            let g = |j: i64| prim(Prim::Le, var(if j % 2 == 0 { "i" } else { "m" }), int(j));
            let ms = [7, 64];
            let t = chain(n, var("i"), g, move |j, t| {
                sub_c(j % 5, prim(Prim::Mod, t, int(ms[j as usize % 2])))
            });
            one(t, i_and_m())
        }
        // Scalar inverses that do not map pieces one to one: `t * 3`, and `t / -2`.
        "normal_mul3_chain" => one(
            steps(n, |j, t| sub_c(j % 5, prim(Prim::Mul, t, int(3)))),
            mega(),
        ),
        "normal_div_neg2_chain" => one(
            steps(n, |j, t| sub_c(j % 5, prim(Prim::IntDiv, t, int(-2)))),
            mega(),
        ),
        _ => panic!("no family {name}"),
    }
}

/// `t0 = i; tj = if i <= j n { t(j-1) } else { t(j-1) - n }` over `i` in `[1, n^2]`, the demand
/// the first `k` odd values of `[1, n]` (`k <= n / 2`). An `i` in the block `(b-1) n < i <= b n`
/// meets the `b - 1` guards `j < b` false, so the chain gives `i - (b-1) n`, its place in the
/// block, and each demanded value `v` gives the one point `v + (b-1) n` in each of the `n`
/// blocks. The points are odd places, so no two are adjacent, within a block or across one: the
/// answer is exactly `k n` pieces.
pub(super) fn output_grid(n: usize, k: usize) -> (Term, Domains, Demand) {
    assert!(
        2 * k <= n,
        "output_grid: {k} odd values do not fit in [1, {n}]"
    );
    let ni = n as i64;
    let g = |j| prim(Prim::Le, var("i"), int(j * ni));
    let t = chain(n, var("i"), g, |_, t| prim(Prim::Sub, t, int(ni)));
    let odd = (1..=ni).filter(|i| i % 2 == 1).take(k);
    let wanted = odd.map(|i| (End::of(i), End::of(i))).collect();
    (
        t,
        i_in(1, ni * ni),
        Demand::Ints(IntervalSet::from_pieces(wanted)),
    )
}

/// The pieces of every domain of the answer to `case`.
pub(super) fn answer_pieces(case: &(Term, Domains, Demand)) -> usize {
    let (t, ds, d) = case;
    preimage(t, ds, d)
        .domains
        .values()
        .map(IntervalSet::len)
        .sum()
}

/// The answer of [`output_grid`] has exactly `k n` pieces, as its comment derives.
#[test]
fn output_grid_answers_have_k_n_pieces() {
    for (n, k) in [(8, 1), (8, 4), (16, 8), (64, 4), (64, 32), (512, 4)] {
        let pieces = answer_pieces(&output_grid(n, k));
        assert_eq!(pieces, k * n, "output_grid at n = {n}, k = {k}");
    }
}

/// The families that `bench::ref_memo` times, each named once.
pub(super) const FAMILIES: [&str; 50] = [
    "alt2var_m",
    "alternating_2var",
    "coef2_guard",
    "const2_narrow",
    "const2_wide",
    "const_base_wide",
    "cross_2in",
    "div_base_i_le_j",
    "guarded_holes_narrow",
    "guarded_holes_wide",
    "i_le_j_narrow",
    "i_le_j_wide",
    "indep_const2",
    "indep_small",
    "indep_varying",
    "interleaved_wide",
    "jmod5_mega",
    "jmod5_narrow",
    "jmod5_ne100",
    "jmod5_top",
    "jmod5_wide",
    "lambda_chain",
    "let_chain",
    "ne_guard_wide",
    "nested_moduli_946_eq",
    "nested_moduli_eq",
    "nested_moduli_eq_4096",
    "nested_moduli_mod7",
    "normal_add_base",
    "normal_div_chain",
    "normal_div_neg2_chain",
    "normal_holey_guards",
    "normal_incompatible_moduli",
    "normal_min_gap",
    "normal_mixed_moduli",
    "normal_mod_chain",
    "normal_mul_base",
    "normal_mul_chain",
    "normal_mul3_chain",
    "normal_named",
    "normal_named_modguard",
    "normal_named_reflection",
    "normal_rel_guard",
    "normal_round_down",
    "normal_round_trip",
    "output_grid",
    "pathological_2var",
    "pathological_abs",
    "pow2_small",
    "pow2_wide",
];

/// Families of terms that read two or more inputs, on the memo of `Tx::back_doubt`, that
/// `bench::ref_memo` does not time: their work grows faster than n (row
/// PERF-ref-memo-multi-input; T(8n)/T(n) 12.1 at 4 and 101 at 8 for `alternating_moduli`).
/// Their answers are checked here with the timed families. `alternating_2var` (25.2 at 64 on
/// the memo) and `alt2var_m` are timed since `Tx::affine_threshold_pair` answers them in
/// O(n log n), and `indep_varying` (183 at 24 on the memo) since `Tx::independent_affine`
/// answers it in O(n).
const UNTIMED_FAMILIES: [&str; 1] = ["alternating_moduli"];

/// Every family `bench::ref_memo` times, at 1 to 4 links (`output_grid` at 8), and the
/// [`UNTIMED_FAMILIES`]: the reference preimage holds every
/// point of `[-12, 12]` on each input (within its domain) that meets the demand, and, where
/// it is marked exact, every point of it there meets the demand, by the interpreter. The
/// benchmarks time these families at 2 to 1280 links and check only their work.
#[test]
fn every_family_the_benchmarks_time_is_answered_soundly_at_small_sizes() {
    for name in FAMILIES
        .iter()
        .chain(&["random_chains"])
        .chain(&UNTIMED_FAMILIES)
    {
        // `output_grid` demands four odd values, so it needs 8 links.
        let sizes = if *name == "output_grid" { 8..=8 } else { 1..=4 };
        for n in sizes {
            for (t, ds, d) in family(name, n) {
                let p = preimage(&t, &ds, &d);
                let names: Vec<Arc<str>> = ds.keys().cloned().collect();
                let mut all: Vec<Vec<Num>> = vec![vec![]];
                for name in &names {
                    let axis: Vec<Num> = (-12..=12)
                        .map(Num::from)
                        .filter(|v| ds[name].contains_end(&End::Fin(v.clone())))
                        .collect();
                    all = all
                        .into_iter()
                        .flat_map(|q| {
                            axis.iter().map(move |v| {
                                let mut q = q.clone();
                                q.push(v.clone());
                                q
                            })
                        })
                        .collect();
                }
                for pt in &all {
                    let hit = names.iter().zip(pt).all(|(x, v)| {
                        p.domains
                            .get(x)
                            .is_none_or(|s| s.contains_end(&End::Fin(v.clone())))
                    });
                    let meets = meets(&t, &names, pt, &d);
                    assert!(
                        !meets || hit,
                        "{name} at {n}: {pt:?} meets {d:?} outside {p:?}"
                    );
                    assert!(
                        !p.exact || !hit || meets,
                        "{name} at {n}: {pt:?} in exact {p:?}"
                    );
                }
            }
        }
    }
}

/// FAIL-ref-memo-stale-entries: a relation translated partway through a run (here by
/// `independent_reflections`, after `difference_guard` has translated the guard's difference
/// and given up) must not reuse translation entries numbered by another translation. On main
/// 22fd64d3a the relation held at (0, 0) and (1, 1), where the term is 0 (found by the Gemini
/// seat of the PERF-ref-memo-multi-input cross-review, round 3). Every point of the box is
/// checked: where the relation holds, the term meets the demand.
#[test]
fn a_relation_built_partway_through_a_run_holds_only_where_its_term_does() {
    let t = ne0(Term::If(
        Shared::new(prim(Prim::Le, prim(Prim::Mod, var("i"), int(2)), int(0))),
        Shared::new(var("m")),
        Shared::new(sub_c(1, var("m"))),
    ));
    let ds = over(&[("i", IntervalSet::of(0, 1)), ("m", IntervalSet::of(0, 1))]);
    let d = Demand::Bool(true);
    let p = preimage(&t, &ds, &d);
    let rel = p
        .relation
        .as_ref()
        .expect("a relation, the box being inexact");
    assert!(!p.exact, "{p:?}");
    let names: Vec<Arc<str>> = ds.keys().cloned().collect();
    for i in 0..=1 {
        for m in 0..=1 {
            let value = |x: &str| if x == "i" { i } else { m };
            let pt: Vec<Num> = names.iter().map(|x| Num::from(value(x))).collect();
            let holds = relation_holds(rel, &names, &pt);
            let in_box = names.iter().all(|x| {
                p.domains
                    .get(x)
                    .is_none_or(|s| s.contains_end(&End::Fin(Num::from(value(x)))))
            });
            let meets = meets(&t, &names, &pt, &d);
            assert!(
                !meets || holds,
                "({i}, {m}) meets but the relation fails: {rel:?}"
            );
            assert!(
                meets || !in_box || !holds,
                "({i}, {m}) fails, lies in the box and the relation holds: {rel:?}"
            );
        }
    }
}

/// Whether `rel` (its body and its definitions) holds at the point `pt` of the inputs `names`,
/// by the Presburger solver.
fn relation_holds(rel: &zedc::store::presburger::Relation, names: &[Arc<str>], pt: &[Num]) -> bool {
    use zedc::store::presburger::{self, Atom, Formula};
    let mut parts = vec![rel.body.clone(), rel.defined()];
    for (x, v) in names.iter().zip(pt) {
        parts.push(presburger::member(
            &Atom::Sym(x.clone()),
            &IntervalSet::from_pieces(vec![(End::Fin(v.clone()), End::Fin(v.clone()))]),
        ));
    }
    presburger::satisfiable(&Formula::and(parts))
        .expect("decided")
        .is_some()
}

/// The set of the integers `vs`.
fn set_of(vs: impl IntoIterator<Item = i64>) -> IntervalSet {
    vs.into_iter()
        .fold(IntervalSet::empty(), |s, v| s.join(&IntervalSet::of(v, v)))
}

/// `Tx::affine_threshold_pair` (PERF-ref-memo-multi-input, Theorem 1 at `threshold_box`):
/// on random two-input threshold chains (guards `<=`, `<`, `>`, `>=` with the literal on either
/// side, cuts monotone on each input, arms `t`, `-t`, `t + c`, `t - c`, `c + t`, `c - t` of one
/// inner value, either input the base, `!=` or `==` demanded false) over boxes of 1 to 5 values
/// on each side, the answer is the exact projections of the points that meet the demand, it is
/// exact iff their product holds no failing point, and an attached relation holds exactly where
/// the term meets the demand. Every point of the box is evaluated by the interpreter.
/// Negative control: with the y projection's test removed (every y cell kept, the Opus seat's
/// mutant `late = true`), this test failed at case 297 of seed 0x7e5e_0001, the `m`
/// projection 0..=4 where the interpreter gives 0..=3 (run once, 2026-11-21).
#[test]
fn threshold_chains_match_the_interpreter_on_every_point() {
    let mut rng = Rng::new(0x7e5e_0001_u64);
    let names: Vec<Arc<str>> = vec!["i".into(), "m".into()];
    for case in 0..400 {
        let n = rng.int(0, 7) as usize;
        let lo = [rng.int(-4, 4), rng.int(-4, 4)];
        let hi = [lo[0] + rng.int(0, 4), lo[1] + rng.int(0, 4)];
        let base = rng.below(2);
        // The input of each link, then monotone cuts for each input.
        let axes: Vec<usize> = (0..n).map(|_| rng.below(2)).collect();
        let mut cuts: [Vec<i64>; 2] = [vec![], vec![]];
        for (a, cs) in cuts.iter_mut().enumerate() {
            let k = axes.iter().filter(|&&x| x == a).count();
            *cs = (0..k).map(|_| rng.int(-6, 6)).collect();
            cs.sort_unstable();
            if rng.coin() {
                cs.reverse();
            }
        }
        let mut next = [0, 0];
        let arm = |rng: &mut Rng, t: &Shared| -> Shared {
            let c = rng.int(-3, 3);
            let inner = || (**t).clone();
            match rng.below(6) {
                0 => t.clone(),
                1 => Shared::new(Term::Prim(Prim::Neg, vec![inner()])),
                2 => Shared::new(prim(Prim::Add, inner(), int(c))),
                3 => Shared::new(prim(Prim::Sub, inner(), int(c))),
                4 => Shared::new(prim(Prim::Add, int(c), inner())),
                _ => Shared::new(prim(Prim::Sub, int(c), inner())),
            }
        };
        let mut t = var(&names[base]);
        for &a in &axes {
            let cut = cuts[a][next[a]];
            next[a] += 1;
            let cmp = [Prim::Le, Prim::Lt, Prim::Gt, Prim::Ge][rng.below(4)];
            let guard = if rng.coin() {
                prim(cmp, var(&names[a]), int(cut))
            } else {
                let mirrored = match cmp {
                    Prim::Le => Prim::Ge,
                    Prim::Lt => Prim::Gt,
                    Prim::Gt => Prim::Lt,
                    _ => Prim::Le,
                };
                prim(mirrored, int(cut), var(&names[a]))
            };
            let inner = Shared::new(t);
            let (yes, no) = (arm(&mut rng, &inner), arm(&mut rng, &inner));
            t = Term::If(Shared::new(guard), yes, no);
        }
        let target = rng.int(-6, 6);
        let (t, d) = if rng.coin() {
            (prim(Prim::Ne, t, int(target)), Demand::Bool(true))
        } else {
            (prim(Prim::Eq, int(target), t), Demand::Bool(false))
        };
        let ds = over(&[
            ("i", IntervalSet::of(lo[0], hi[0])),
            ("m", IntervalSet::of(lo[1], hi[1])),
        ]);
        let p = preimage(&t, &ds, &d);
        let box_points = || (lo[0]..=hi[0]).flat_map(move |i| (lo[1]..=hi[1]).map(move |m| [i, m]));
        let pass = |pt: [i64; 2]| meets(&t, &names, &pt.map(Num::from), &d);
        let px = set_of(box_points().filter(|&pt| pass(pt)).map(|pt| pt[0]));
        let py = set_of(box_points().filter(|&pt| pass(pt)).map(|pt| pt[1]));
        let want = |x: &str, proj: &IntervalSet| {
            let got = p.domains.get(x).unwrap_or(&ds[x]);
            if proj.is_empty() {
                // An empty answer may name either input empty.
                return;
            }
            assert_eq!(got, proj, "case {case}, {x}: {t:?} on {ds:?}, {p:?}");
        };
        if px.is_empty() {
            assert!(
                p.domains.values().any(IntervalSet::is_empty),
                "case {case}: no point meets, {t:?} on {ds:?}, {p:?}"
            );
            continue;
        }
        want("i", &px);
        want("m", &py);
        let exact = box_points()
            .filter(|pt| px.contains_end(&End::of(pt[0])) && py.contains_end(&End::of(pt[1])))
            .all(pass);
        assert_eq!(
            p.exact, exact,
            "case {case}, exactness: {t:?} on {ds:?}, {p:?}"
        );
        if let Some(rel) = &p.relation {
            for pt in box_points() {
                assert_eq!(
                    relation_holds(rel, &names, &pt.map(Num::from)),
                    pass(pt),
                    "case {case}, relation at {pt:?}: {t:?}, {rel:?}"
                );
            }
        } else {
            assert!(p.exact, "case {case}: inexact with no relation, {p:?}");
        }
    }
}

/// `alternating_2var` with base `m` (the Opus seat's `alt2var_m`) at 18 to 21 links, where
/// the 3-slice cover of the round-3 combination declined: the whole box, not exact, and the
/// relation of `threshold_relation` (one definition a link), so `Tx::affine_threshold_pair`
/// answered. The point (-1000, 0) fails by the interpreter.
#[test]
fn alt2var_m_at_18_to_21_links_is_answered_by_the_threshold_stage() {
    let names: Vec<Arc<str>> = vec!["i".into(), "m".into()];
    for n in 18..=21 {
        for (t, ds, d) in family("alt2var_m", n) {
            let p = preimage(&t, &ds, &d);
            assert!(!p.exact, "alt2var_m at {n}: {p:?}");
            assert_eq!(p.domains, ds, "alt2var_m at {n}");
            let rel = p.relation.as_ref().expect("a relation");
            assert_eq!(rel.defs.len(), n, "alt2var_m at {n}: {rel:?}");
            let fail = [Num::from(-1000), Num::from(0)];
            assert!(!meets(&t, &names, &fail, &d), "alt2var_m at {n}");
            assert!(!relation_holds(rel, &names, &fail), "alt2var_m at {n}");
        }
    }
}

/// `alt2var_m` at one link, `if m <= 1 { m } else { 1 - m } != 0`: it fails only at m = 0
/// (1 - m is 0 at m = 1, which takes the first arm), so the answer is the box with m = 0
/// removed, and it is exact.
#[test]
fn alt2var_m_at_one_link_removes_m_zero_exactly() {
    for (t, ds, d) in family("alt2var_m", 1) {
        let p = preimage(&t, &ds, &d);
        assert!(p.exact, "{p:?}");
        assert!(p.relation.is_none(), "{p:?}");
        assert_eq!(p.domains.get("i").unwrap_or(&ds["i"]), &ds["i"]);
        let want = IntervalSet::from_pieces(vec![
            (End::of(-1000), End::of(-1)),
            (End::of(1), End::of(1000)),
        ]);
        assert_eq!(p.domains["m"], want, "{p:?}");
    }
}

/// Listed inputs take the threshold stage too (`preimage_in`): `enumerate` takes only a box
/// with at most one input of several members, where the product of the projections is the set
/// of passing points, so the stage, exact by Theorem 1 at `threshold_box`, must answer it
/// exactly and with no relation. On `alternating_2var` and `alt2var_m` at 1 to 4 links, over
/// listed boxes with holes (`i` in {-3, -1, 0, 2, 5} and each `m` in -2..=2, then each `i` in
/// -3..=3 and `m` in {-2, 0, 1, 3}), listed and unlisted calls both give the projections of
/// the points that meet the demand, exact, with no relation.
#[test]
fn listed_threshold_chains_are_answered_exactly() {
    let names: Vec<Arc<str>> = vec!["i".into(), "m".into()];
    let mut boxes: Vec<(Vec<i64>, Vec<i64>)> = Vec::new();
    for m in -2..=2 {
        boxes.push((vec![-3, -1, 0, 2, 5], vec![m]));
    }
    for i in -3..=3 {
        boxes.push((vec![i], vec![-2, 0, 1, 3]));
    }
    let listed: Listed = names.iter().cloned().collect();
    for name in ["alternating_2var", "alt2var_m"] {
        for n in 1..=4 {
            for (t, _, d) in family(name, n) {
                for (is, ms) in &boxes {
                    let ds = over(&[
                        ("i", set_of(is.iter().copied())),
                        ("m", set_of(ms.iter().copied())),
                    ]);
                    let pass: Vec<[i64; 2]> = (is.iter())
                        .flat_map(|&i| ms.iter().map(move |&m| [i, m]))
                        .filter(|pt| meets(&t, &names, &pt.map(Num::from), &d))
                        .collect();
                    let px = set_of(pass.iter().map(|pt| pt[0]));
                    let py = set_of(pass.iter().map(|pt| pt[1]));
                    for p in [preimage_listed(&t, &ds, &listed, &d), preimage(&t, &ds, &d)] {
                        let at = format!("{name} n={n} i={is:?} m={ms:?}: {p:?}");
                        assert!(p.exact && p.relation.is_none(), "{at}");
                        assert_eq!(p.domains.get("i").unwrap_or(&ds["i"]), &px, "{at}");
                        assert_eq!(p.domains.get("m").unwrap_or(&ds["m"]), &py, "{at}");
                    }
                }
            }
        }
    }
}

/// Every point of a box given as one list of values per input, in the order of `names`.
fn grid(names: &[Arc<str>], values: &HashMap<Arc<str>, Vec<i64>>) -> Vec<Vec<i64>> {
    names.iter().fold(vec![vec![]], |all, x| {
        all.into_iter()
            .flat_map(|q| {
                values[x].iter().map(move |&v| {
                    let mut q = q.clone();
                    q.push(v);
                    q
                })
            })
            .collect()
    })
}

/// `Tx::independent_affine` (PERF-ref-memo-multi-input part (b)): on random chains whose
/// guards read distinct inputs `b1..bn` (comparisons `<=`, `<`, `>`, `>=` with the literal on
/// either side), with arms `t`, `-t`, `t + c`, `t - c`, `c + t`, `c - t` of one inner value,
/// the base `z` (with holes in its domain at times) or a constant, and a demand whose
/// complement is a point, a ray or an interval, over boxes of 1 to 3 values per guard input
/// and 1 to 5 for `z`: the answer is the exact projections of the points that meet the demand,
/// it is exact iff their product holds no failing point, and an attached relation holds
/// exactly where the term meets the demand. Every point of the box is evaluated by the
/// interpreter. Negative control: with every allowed arm marked surviving, case 11 failed on
/// the projection of `b3` (run once, 2026-11-21).
#[test]
fn independent_chains_match_the_interpreter_on_every_point() {
    let mut rng = Rng::new(0x1d5e_0002_u64);
    for case in 0..400 {
        let n = rng.int(1, 5) as usize;
        let mut values: HashMap<Arc<str>, Vec<i64>> = HashMap::new();
        let zlo = rng.int(-4, 4);
        let mut zs: Vec<i64> = (zlo..=zlo + rng.int(0, 4))
            .filter(|_| rng.below(4) != 0)
            .collect();
        if zs.is_empty() {
            zs.push(zlo);
        }
        values.insert("z".into(), zs);
        let arm = |rng: &mut Rng, t: &Shared| -> Shared {
            let c = rng.int(-3, 3);
            let inner = || (**t).clone();
            match rng.below(6) {
                0 => t.clone(),
                1 => Shared::new(Term::Prim(Prim::Neg, vec![inner()])),
                2 => Shared::new(prim(Prim::Add, inner(), int(c))),
                3 => Shared::new(prim(Prim::Sub, inner(), int(c))),
                4 => Shared::new(prim(Prim::Add, int(c), inner())),
                _ => Shared::new(prim(Prim::Sub, int(c), inner())),
            }
        };
        let mut t = if rng.below(5) == 0 {
            int(rng.int(-3, 3))
        } else {
            var("z")
        };
        for j in 1..=n {
            let b = format!("b{j}");
            let lo = rng.int(-2, 1);
            values.insert(b.as_str().into(), (lo..=lo + rng.int(0, 2)).collect());
            let cut = rng.int(-2, 3);
            let cmp = [Prim::Le, Prim::Lt, Prim::Gt, Prim::Ge][rng.below(4)];
            let guard = if rng.coin() {
                prim(cmp, var(&b), int(cut))
            } else {
                let mirrored = match cmp {
                    Prim::Le => Prim::Ge,
                    Prim::Lt => Prim::Gt,
                    Prim::Gt => Prim::Lt,
                    _ => Prim::Le,
                };
                prim(mirrored, int(cut), var(&b))
            };
            let inner = Shared::new(t);
            let (yes, no) = (arm(&mut rng, &inner), arm(&mut rng, &inner));
            t = Term::If(Shared::new(guard), yes, no);
        }
        let target = rng.int(-6, 6);
        let (t, d) = match rng.below(4) {
            0 => (prim(Prim::Ne, t, int(target)), Demand::Bool(true)),
            1 => (prim(Prim::Eq, int(target), t), Demand::Bool(false)),
            2 => {
                let cmp = [Prim::Le, Prim::Lt, Prim::Gt, Prim::Ge][rng.below(4)];
                (prim(cmp, t, int(target)), Demand::Bool(rng.coin()))
            }
            _ => {
                let hole = IntervalSet::of(target, target + rng.int(0, 3));
                (t, Demand::Ints(IntervalSet::top().minus(&hole)))
            }
        };
        let ds: Domains = values
            .iter()
            .map(|(x, vs)| (x.clone(), set_of(vs.iter().copied())))
            .collect();
        let names: Vec<Arc<str>> = ds.keys().cloned().collect();
        let p = preimage(&t, &ds, &d);
        let pts = grid(&names, &values);
        let pass = |pt: &[i64]| {
            let pt: Vec<Num> = pt.iter().map(|&v| Num::from(v)).collect();
            meets(&t, &names, &pt, &d)
        };
        let passing: Vec<&Vec<i64>> = pts.iter().filter(|pt| pass(pt)).collect();
        if passing.is_empty() {
            assert!(
                p.domains.values().any(IntervalSet::is_empty),
                "case {case}: no point meets, {t:?} on {ds:?}, {p:?}"
            );
            continue;
        }
        let projs: Vec<IntervalSet> = (0..names.len())
            .map(|k| set_of(passing.iter().map(|pt| pt[k])))
            .collect();
        for (x, proj) in names.iter().zip(&projs) {
            let got = p.domains.get(x).unwrap_or(&ds[x]);
            assert_eq!(got, proj, "case {case}, {x}: {t:?} on {ds:?}, {p:?}");
        }
        let exact = pts
            .iter()
            .filter(|pt| {
                pt.iter()
                    .zip(&projs)
                    .all(|(&v, s)| s.contains_end(&End::of(v)))
            })
            .all(|pt| pass(pt));
        assert_eq!(
            p.exact, exact,
            "case {case}, exactness: {t:?} on {ds:?}, {p:?}"
        );
        if let Some(rel) = &p.relation {
            for pt in &pts {
                let at: Vec<Num> = pt.iter().map(|&v| Num::from(v)).collect();
                assert_eq!(
                    relation_holds(rel, &names, &at),
                    pass(pt),
                    "case {case}, relation at {pt:?}: {t:?}, {rel:?}"
                );
            }
        } else {
            assert!(p.exact, "case {case}: inexact with no relation, {p:?}");
        }
    }
}

/// The subset-sum chains of the coNP-hardness proof at `Tx::independent_affine`: `z` fixed to
/// 0, guards `b_j <= 0` over `0..=1`, arms `t + a_j` and `t`, the demand `t != s`. Every arm
/// survives (n >= 2), so the answer is the whole box, and it is exact iff no subset of the
/// `a_j` sums to `s`, by the interpreter at every point. The sets leave gaps among their sums
/// (`{3, 5}` gives 0, 3, 5, 8), where the progressions of Check 2 are not exact and must not
/// claim a failing point; `s` is taken in the gaps, on the sums, and outside them.
/// Negative control: with `ApNum::join` marking every join exact, the random test
/// `independent_chains_match_the_interpreter_on_every_point` still passed, and this one failed
/// (run once, 2026-11-21).
#[test]
fn subset_sum_chains_are_exact_iff_no_subset_reaches_the_demand() {
    let sets: [&[i64]; 5] = [&[3, 5], &[2, 4, 6], &[4, 6], &[-3, 5, 7], &[3, 5, 11, 13]];
    for a in sets {
        let n = a.len();
        let t = a.iter().enumerate().fold(var("z"), |t, (j, &aj)| {
            let inner = Shared::new(t);
            Term::If(
                Shared::new(prim(Prim::Le, var(&format!("b{}", j + 1)), int(0))),
                Shared::new(prim(Prim::Add, (*inner).clone(), int(aj))),
                inner,
            )
        });
        let mut ds = bits(n, 0, 0);
        ds.insert("z".into(), IntervalSet::of(0, 0));
        let sums: BTreeSet<i64> = (0..1u32 << n)
            .map(|m| (0..n).filter(|j| m >> j & 1 == 1).map(|j| a[j]).sum())
            .collect();
        for s in -4..=33 {
            let term = prim(Prim::Ne, t.clone(), int(s));
            let d = Demand::Bool(true);
            let p = preimage(&term, &ds, &d);
            let at = format!("a={a:?} s={s}: {p:?}");
            for (x, whole) in &ds {
                assert_eq!(p.domains.get(x).unwrap_or(whole), whole, "{at}");
            }
            assert_eq!(p.exact, !sums.contains(&s), "{at}");
        }
    }
}

/// Listed inputs take the independent stage too (`preimage_in`): on a box `enumerate` takes,
/// every input but one has one value, and the stage must answer it with the exact projections,
/// exact, with no relation. On `indep_varying` at 1 to 4 links: `z` listed with holes
/// ({1, 2, 3, 5, 8, 13}) under every choice of the bits, and each `z` in 1..=5 with one bit
/// listed as {-1, 1} (a hole at 0) and the others fixed; listed and unlisted calls agree.
#[test]
fn listed_independent_chains_are_answered_exactly() {
    for n in 1..=4usize {
        for (t, _, d) in family("indep_varying", n) {
            let mut boxes: Vec<HashMap<Arc<str>, Vec<i64>>> = Vec::new();
            for mask in 0..1u32 << n {
                let mut b: HashMap<Arc<str>, Vec<i64>> = HashMap::new();
                b.insert("z".into(), vec![1, 2, 3, 5, 8, 13]);
                for j in 1..=n {
                    b.insert(format!("b{j}").into(), vec![i64::from(mask >> (j - 1) & 1)]);
                }
                boxes.push(b);
            }
            for z in 1..=5 {
                for k in 1..=n {
                    let mut b: HashMap<Arc<str>, Vec<i64>> = HashMap::new();
                    b.insert("z".into(), vec![z]);
                    for j in 1..=n {
                        let vs = if j == k {
                            vec![-1, 1]
                        } else {
                            vec![(j as i64 + z) % 2]
                        };
                        b.insert(format!("b{j}").into(), vs);
                    }
                    boxes.push(b);
                }
            }
            for values in &boxes {
                let ds: Domains = values
                    .iter()
                    .map(|(x, vs)| (x.clone(), set_of(vs.iter().copied())))
                    .collect();
                let names: Vec<Arc<str>> = ds.keys().cloned().collect();
                let listed: Listed = names.iter().cloned().collect();
                let passing: Vec<Vec<i64>> = grid(&names, values)
                    .into_iter()
                    .filter(|pt| {
                        let pt: Vec<Num> = pt.iter().map(|&v| Num::from(v)).collect();
                        meets(&t, &names, &pt, &d)
                    })
                    .collect();
                for p in [preimage_listed(&t, &ds, &listed, &d), preimage(&t, &ds, &d)] {
                    let at = format!("indep_varying n={n} {values:?}: {p:?}");
                    assert!(p.exact && p.relation.is_none(), "{at}");
                    if passing.is_empty() {
                        assert!(p.domains.values().any(IntervalSet::is_empty), "{at}");
                        continue;
                    }
                    for (k, x) in names.iter().enumerate() {
                        let proj = set_of(passing.iter().map(|pt| pt[k]));
                        assert_eq!(p.domains.get(x).unwrap_or(&ds[x]), &proj, "{at}");
                    }
                }
            }
        }
    }
}

/// PROOF-round-down-piece-bound: on `normal_round_down` the forward image of a node has at most
/// 3 pieces (3 only at the `Round`) and every label the walk builds has one piece, the two
/// bounds the proof at `Tx::inverse_states` derives for every n. Every n to 128, on the default
/// stack (author P178); `bench::ref_memo::normal_round_down_keeps_its_pieces_at_large_sizes`
/// reads the same at 1024 to 8192.
#[test]
fn the_round_down_chain_keeps_three_pieces_and_one_piece_labels() {
    for n in 1..=128 {
        assert_eq!(round_down_most(n), [3, 1], "normal_round_down at {n}");
    }
}

/// COMPLEXITY.md K138 (C): the tree of B_j, the largest `If` tree of `normal_min_gap`, has at
/// most 15 nodes at every n, as the proof at `Tx::inverse_states` derives (its excluded values
/// lie in one of five runs of 15 integers). 15 is reached, from n = 11 on.
pub(super) const MIN_GAP_B_NODES: u64 = 15;

/// K138 (C) at every n to 128; `bench::ref_memo::normal_min_gap_keeps_its_b_nodes_at_1024`
/// reads the benchmark's size. The bound is reached, so one fewer fails this test.
#[test]
fn the_min_gap_chain_keeps_b_to_fifteen_nodes() {
    let mut most = 0;
    for n in 1..=128 {
        let m = min_gap_if_tree_nodes(n);
        assert!(m <= MIN_GAP_B_NODES, "normal_min_gap at {n}: {m} nodes");
        most = most.max(m);
    }
    assert_eq!(most, MIN_GAP_B_NODES, "the bound is reached");
}

/// The most nodes of the tree of an `If` node at its step in the preimage of `normal_min_gap`
/// at `n` links ([`zedc::store::preimage::counts::if_tree_nodes`]), read on the calling thread.
pub(super) fn min_gap_if_tree_nodes(n: usize) -> u64 {
    use zedc::store::preimage::counts::{count_if_tree_nodes, if_tree_nodes};
    let mut most = 0;
    for (t, ds, d) in family("normal_min_gap", n) {
        count_if_tree_nodes();
        preimage(&t, &ds, &d);
        most = most.max(if_tree_nodes().expect("recording on this thread"));
    }
    most
}

/// The most pieces of a forward image and of a label in the preimage of `normal_round_down` at
/// `n` links ([`zedc::store::preimage::counts::inverse_most`]), read on the calling thread.
pub(super) fn round_down_most(n: usize) -> [u64; 2] {
    use zedc::store::preimage::counts::inverse_most;
    let mut most = [0, 0];
    for (t, ds, d) in family("normal_round_down", n) {
        inverse_most();
        preimage(&t, &ds, &d);
        let m = inverse_most();
        most = [most[0].max(m[0]), most[1].max(m[1])];
    }
    most
}
