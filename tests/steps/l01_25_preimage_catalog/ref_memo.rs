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
//! - the scaling: each of the 48 families of the item's benchmark at n and 8n, held to the
//!   plan's limit (`scaling::LIMIT`) in instructions and bytes, with no wider limit for any
//!   family; each answer grows at most 8 times (`output_grid` demands four values, 4n pieces).
//!   The work of writing out a larger answer is held at one n by
//!   `output_grid_work_grows_with_its_answer`, and `nested_moduli_eq_4096` with its costly
//!   constants next to the root at every n is ignored with its plan row,
//!   REF-nested-moduli-state.

use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

use num_bigint::BigInt;
use zed_kernel::{Prim, Shared, Term, Value, eval};
use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::preimage_ref::{Demand, Domains, Listed, Preimage, preimage, preimage_listed};

use super::s22::{bits, chain, i_in, int, on_big_stack, over, prim, var};

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
/// exact at [`points`]. Counts it in `kept`.
fn check_line(line: &str, kept: &mut Kept) {
    let c = call(line);
    let p: Preimage = preimage_listed(&c.term, &c.inputs, &c.listed, &c.demand);
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
    let names: Vec<Arc<str>> = c.inputs.keys().cloned().collect();
    for pt in points(&c, &p.domains) {
        let hit = names.iter().zip(&pt).all(|(n, v)| {
            p.domains
                .get(n)
                .is_none_or(|s| s.contains_end(&End::Fin(v.clone())))
        });
        let meets = meets(&c.term, &names, &pt, &c.demand);
        assert!(
            !meets || hit,
            "{line}\nthe point {pt:?} meets the demand outside the new box"
        );
        assert!(
            !p.exact || !hit || meets,
            "{line}\nthe point {pt:?} of the new box, marked exact, fails the demand"
        );
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
/// changes: each kept or made finer. 85 are made exact, 113 narrower and still inexact; 28
/// keep main's domains and exactness and differ in a stop, a listing, a relation or a
/// refusal, which the replay compares and this file does not keep.
#[test]
fn the_changed_answers_of_main_s_dump_are_kept_or_made_finer() {
    let kept = on_big_stack(|| {
        let mut kept = Kept::default();
        lines(CHANGED).for_each(|l| check_line(l, &mut kept));
        kept
    });
    assert_eq!(
        kept,
        Kept {
            same: 28,
            narrower: 113,
            made_exact: 85
        }
    );
}

/// Calls 22, 45 and 86 of the audit of main's dump, whose answers the candidates of rounds 1
/// and 2 made coarser at first: main's answer or a finer one. Call 45 is
/// `(if (x < 3) { x * 5 } else { x * y }) div 3` over x in [10, 21], y in (-inf, 18], demand
/// (-inf, -7]: main answers y in (-inf, 0], not exact (the exact answer is y <= -1).
#[test]
fn calls_22_45_and_86_keep_main_s_answer_or_a_finer_one() {
    let kept = on_big_stack(|| {
        let mut kept = Kept::default();
        lines(PINNED).for_each(|l| check_line(l, &mut kept));
        kept
    });
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
fn family(name: &str, n: usize) -> Vec<(Term, Domains, Demand)> {
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
        "normal_abs_gap" => {
            let g = |j| prim(Prim::Le, var("i"), int(1000 * j));
            let t = chain(n, var("i"), g, |j, t| sub_c(j % 5 + 4, abs(t)));
            vec![(t, mega(), gap())]
        }
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
        "nested_moduli_eq_4096_at_6" => {
            // The links next to the root take the constants they take at n = 6 mod 10, the
            // class whose answer has about 760 pieces, at every n.
            let d = (6 - n as i64).rem_euclid(10);
            one(moduli_from(n, g_eqj, &[7, 4096], d), mega())
        }
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
        _ => panic!("no family {name}"),
    }
}

/// `t0 = i; tj = if i <= j n { t(j-1) } else { t(j-1) - n }` over `i` in `[1, n^2]`, the demand
/// the first `k` odd values of `[1, n]` (`k <= n / 2`). An `i` in the block `(b-1) n < i <= b n`
/// meets the `b - 1` guards `j < b` false, so the chain gives `i - (b-1) n`, its place in the
/// block, and each demanded value `v` gives the one point `v + (b-1) n` in each of the `n`
/// blocks. The points are odd places, so no two are adjacent, within a block or across one: the
/// answer is exactly `k n` pieces.
fn output_grid(n: usize, k: usize) -> (Term, Domains, Demand) {
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
fn answer_pieces(case: &(Term, Domains, Demand)) -> usize {
    let (t, ds, d) = case;
    preimage(t, ds, d)
        .domains
        .values()
        .map(IntervalSet::len)
        .sum()
}

/// [`scaling::compare`] on the reference preimage of the family `name` at `n` and `8n` links: a
/// pass of order n, held to [`scaling::LIMIT`] with the note from [`scaling::PREFERRED`]. Every
/// family's answer grows at most 8 times from `n` to `8n`; the work of writing out a larger
/// answer is held by [`output_grid_work_grows_with_its_answer`], at one `n`.
fn scales(name: &str, n: usize) {
    on_big_stack(|| {
        let large_n = n * scaling::FACTOR;
        let (small, large) = (family(name, n), family(name, large_n));
        let run = |cases: &[(Term, Domains, Demand)]| {
            for (t, ds, d) in cases {
                std::hint::black_box(preimage(t, ds, d));
            }
        };
        let what = format!("the reference preimage of the family {name}, sizes {n} and {large_n}");
        scaling::compare(&what, 1, || run(&small), || run(&large));
    });
}

/// One test a family, each at the first size the item's scorer used, except where a note says.
macro_rules! scaling_tests {
    ($($test:ident: $name:literal at $n:literal;)*) => {
        $(
            #[test]
            fn $test() {
                scales($name, $n);
            }
        )*
    };
}

scaling_tests! {
    const2_narrow_scales: "const2_narrow" at 64;
    const2_wide_scales: "const2_wide" at 64;
    const_base_wide_scales: "const_base_wide" at 64;
    cross_2in_scales: "cross_2in" at 16;
    div_base_i_le_j_scales: "div_base_i_le_j" at 64;
    guarded_holes_narrow_scales: "guarded_holes_narrow" at 256;
    guarded_holes_wide_scales: "guarded_holes_wide" at 64;
    i_le_j_narrow_scales: "i_le_j_narrow" at 64;
    i_le_j_wide_scales: "i_le_j_wide" at 64;
    indep_const2_scales: "indep_const2" at 64;
    indep_small_scales: "indep_small" at 6;
    interleaved_wide_scales: "interleaved_wide" at 64;
    jmod5_mega_scales: "jmod5_mega" at 64;
    jmod5_narrow_scales: "jmod5_narrow" at 64;
    jmod5_ne100_scales: "jmod5_ne100" at 64;
    jmod5_top_scales: "jmod5_top" at 64;
    jmod5_wide_scales: "jmod5_wide" at 64;
    lambda_chain_scales: "lambda_chain" at 64;
    let_chain_scales: "let_chain" at 64;
    ne_guard_wide_scales: "ne_guard_wide" at 64;
    nested_moduli_946_eq_scales: "nested_moduli_946_eq" at 2;
    nested_moduli_eq_scales: "nested_moduli_eq" at 2;
    // At n = 0 mod 10, so both sizes put the same constants next to the root (they repeat every
    // 10 links); at 32 and 256 the answer went from 5 pieces to 772, a different question.
    nested_moduli_eq_4096_scales: "nested_moduli_eq_4096" at 160;
    nested_moduli_eq_long_scales: "nested_moduli_eq" at 128;
    nested_moduli_mod7_scales: "nested_moduli_mod7" at 2;
    normal_abs_gap_scales: "normal_abs_gap" at 16;
    normal_add_base_scales: "normal_add_base" at 16;
    normal_div_chain_scales: "normal_div_chain" at 16;
    normal_holey_guards_scales: "normal_holey_guards" at 16;
    normal_incompatible_moduli_16_scales: "normal_incompatible_moduli" at 16;
    normal_incompatible_moduli_scales: "normal_incompatible_moduli" at 4;
    normal_min_gap_scales: "normal_min_gap" at 16;
    normal_mixed_moduli_scales: "normal_mixed_moduli" at 16;
    normal_mod_chain_scales: "normal_mod_chain" at 16;
    normal_mul_base_scales: "normal_mul_base" at 16;
    normal_mul_chain_scales: "normal_mul_chain" at 16;
    normal_named_scales: "normal_named" at 16;
    normal_named_modguard_scales: "normal_named_modguard" at 16;
    normal_named_reflection_scales: "normal_named_reflection" at 16;
    normal_rel_guard_scales: "normal_rel_guard" at 16;
    normal_round_down_scales: "normal_round_down" at 16;
    normal_round_trip_scales: "normal_round_trip" at 16;
    // Four values demanded: 4n pieces. At 8 the answer-free work was 84% of the run.
    output_grid_scales: "output_grid" at 64;
    pathological_2var_scales: "pathological_2var" at 16;
    pathological_abs_scales: "pathological_abs" at 16;
    pow2_small_scales: "pow2_small" at 8;
    pow2_wide_scales: "pow2_wide" at 64;
    random_chains_scales: "random_chains" at 64;
}

/// The answer of [`output_grid`] has exactly `k n` pieces, as its comment derives.
#[test]
fn output_grid_answers_have_k_n_pieces() {
    for (n, k) in [(8, 1), (8, 4), (16, 8), (64, 4), (64, 32), (512, 4)] {
        let pieces = on_big_stack(|| answer_pieces(&output_grid(n, k)));
        assert_eq!(pieces, k * n, "output_grid at n = {n}, k = {k}");
    }
}

/// The work of writing out an answer 8 times larger, the term unchanged: [`output_grid`] at 1024
/// links with 64 and 512 values demanded, `64 n` and `512 n` pieces by the hand count, held to
/// [`scaling::LIMIT`] as a pass of order n in the pieces. An earlier test held `output_grid`'s
/// work at `n` and `8n` with all `n / 2` odd values demanded to the limit times the growth of
/// the answer counted from the code under test (64 times): work quadratic in `n` passed it, and
/// an answer split into more pieces raised its own limit.
#[test]
fn output_grid_work_grows_with_its_answer() {
    on_big_stack(|| {
        let n = 1024;
        let (small, large) = (output_grid(n, 64), output_grid(n, 512));
        let run = |(t, ds, d): &(Term, Domains, Demand)| {
            std::hint::black_box(preimage(t, ds, d));
        };
        scaling::compare(
            "the reference preimage of output_grid at 1024 links, 64 and 512 values demanded",
            1,
            || run(&small),
            || run(&large),
        );
        assert_eq!(answer_pieces(&small), 64 * n);
        assert_eq!(answer_pieces(&large), 512 * n);
    });
}

/// [`scales`] on `nested_moduli_eq_4096` with the constants of n = 6 mod 10 next to the root at
/// every n, an answer of about 760 pieces at both sizes.
#[test]
#[ignore = "REF-nested-moduli-state: the reference preimage's remainder chain costs about 150M instructions a link, 21.4 times the instructions and 20.5 times the bytes at 16 and 128 links, 11.5 and 12.1 at 64 and 512, over the limit; open"]
fn nested_moduli_eq_4096_at_6_scales() {
    scales("nested_moduli_eq_4096_at_6", 16);
}
