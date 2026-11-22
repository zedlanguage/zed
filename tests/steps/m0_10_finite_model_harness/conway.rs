//! Plan row TRACE-conway: the four Conway identities for the lattice `fix`, run on the
//! reference evaluator.
//!
//! DESIGN.md sec:categories says `fix` is the trace, since on a cartesian category a trace is
//! the same thing as a Conway fixed-point operator (Hasegawa; Hyland; [BentonHyland]
//! Theorem 2.9, which the bibliography entry cites), and leaves open whether the seeded least
//! fixed point over a carrier with failure atoms satisfies the identities. The operator read
//! here, as the row says: for a step `f` with the seed `a` as parameter, `f†(a)` is
//! `fix_lattice(a, s, ⊔)`, the least fixed point of `x ↦ a ⊔ x ⊔ s(x)`, which for monotone `s`
//! is the least fixed point of `f(a, x) = a ⊔ s(x)` (a prefixed point of either is a `y` with
//! `a ≤ y` and `s(y) ≤ y`, and on a complete lattice the least fixed point of a monotone map is
//! its least prefixed point (Knaster–Tarski)). The identities, as Benton and Hyland state them
//! (Definitions 2.6 and 2.7) for `f: A × X → X` and `f†: A → X`:
//!
//! - fixed point: `f†(a) = f(a, f†(a))`;
//! - naturality in the parameter: `(f ∘ (h × id))† = f† ∘ h`;
//! - dinaturality: for `f: A × X → Y` and `g: A × Y → X`,
//!   `(g ∘ ⟨π₁, f⟩)†(a) = g(a, (f ∘ ⟨π₁, g⟩)†(a))`;
//! - diagonal: `(f ∘ (id × Δ))† = (f†)†`, that is `μx. f(a, x, x) = μx. μy. f(a, x, y)`.
//!
//! The carrier is the powerset of `{0, 1, 2}` written as the integers `0..8` under `bitOr`
//! (and of `{0, 1}`, `0..4`, for the exhaustive runs), so that it is a lattice that is not a
//! chain: on a chain every monotone map preserves binary joins, and the slid-seed form below
//! could not fail. A step is a table `x ↦ t[x]` looked up by `get`; T-Fix admits it when it is
//! monotone (the step is not in join-update form, so monotonicity is the evidence T-Fix asks
//! for, DESIGN.md sec:kernel), and the carrier is finite, so the ascending chain condition
//! holds. A carrier with a loose failure atom is the same lattice with the seed allowed to be
//! the atom `#fail`: a step whose output can be a loose atom is a static error at the step
//! (DESIGN.md sec:kernel, the step must be total on the carrier with no passing out), so an
//! atom can reach a `fix` T-Fix admits only through its seed.
//!
//! Why the atom changes nothing, beyond the finite runs: put `#fail` above every member of
//! the lattice `L`. Then `L ∪ {#fail}` is again a complete lattice, `x ⊔ #fail = #fail` is its
//! join (the evaluator's `bitOr` passes the atom out), and a step that passes the atom out,
//! `s(#fail) = #fail`, stays monotone, since `s(x) ≤ #fail = s(#fail)` for every `x`. On a complete
//! lattice, with `μ` the least fixed point of a monotone map, the four identities hold:
//! fixed point by definition; naturality because both sides are `μx. f(h(b), x)`;
//! dinaturality (the rolling rule): `g(μ(f∘g))` is a fixed point of `g∘f`, so
//! `μ(g∘f) ≤ g(μ(f∘g))`, and `f(μ(g∘f))` is a fixed point of `f∘g`, so
//! `μ(f∘g) ≤ f(μ(g∘f))` and `g(μ(f∘g)) ≤ g(f(μ(g∘f))) = μ(g∘f)`; diagonal: with
//! `d = μx. f(x, x)` and `k(x) = μy. f(x, y)`, `f(d, d) = d` gives `k(d) ≤ d`, so `μk ≤ d`, and
//! `m = μk` has `m = k(m) = f(m, k(m)) = f(m, m)`, so `d ≤ m`. The parameter `a` is carried
//! through each step unchanged. So the seeded `fix` over the carrier with the atom is a
//! Conway operator too. The runs below check this on the
//! evaluator, and that the evaluator's iteration `x := x ⊔ s(x)` from the seed reaches that
//! least fixed point. Results (2026-11-22): all four identities hold on every instance, with
//! and without the atom; the slid-seed form holds for a slid map that preserves binary joins
//! and fails for one that does not.

use zed_kernel::term::build::{let_, lit, prim, var};
use zed_kernel::{Prim, Term, Value, eval};
use zed_tests::check::{holds, refuted};
use zed_tests::instances::{Rng, seq_value};
use zed_tests::kernel::{atom, fix_lattice, fresh, func, get};

/// A seed: a member of the lattice, or the loose failure atom.
#[derive(Clone, Copy, Debug)]
enum Seed {
    Set(u8),
    Fail,
}

fn seed(a: Seed) -> Term {
    match a {
        Seed::Set(m) => lit(Value::Int(m as i64)),
        Seed::Fail => atom("fail"),
    }
}

fn join(a: Term, b: Term) -> Term {
    prim(Prim::BitOr, vec![a, b])
}

/// The step `x ↦ t[x]`.
fn table(t: &[u8]) -> Term {
    let t: Vec<i64> = t.iter().map(|&v| v as i64).collect();
    lit(seq_value(&t))
}

fn apply(t: &[u8], x: Term) -> Term {
    get(table(t), x)
}

fn step(t: &[u8]) -> Term {
    let t = t.to_vec();
    func(move |[x]| apply(&t, x))
}

/// `f†(a)`: `fix_lattice(a, s, bitOr)`.
fn dagger(a: Term, s: Term) -> Term {
    fix_lattice(a, s, Term::PrimFn(Prim::BitOr))
}

/// Whether `t`, a map on the powerset of `bits` elements, is monotone.
fn monotone(t: &[u8]) -> bool {
    (0..t.len()).all(|x| (0..t.len()).all(|y| x & y != x || t[x] & t[y] == t[x]))
}

/// Whether `t` preserves binary joins.
fn preserves_joins(t: &[u8]) -> bool {
    (0..t.len()).all(|x| (0..t.len()).all(|y| t[x | y] == t[x] | t[y]))
}

/// Every monotone map on the powerset of `{0, 1}`: 36 of the 256 maps on `0..4`.
fn monotone_maps_2() -> Vec<[u8; 4]> {
    let all = (0..256u32).map(|c| std::array::from_fn(|i| ((c >> (2 * i)) & 3) as u8));
    all.filter(|t: &[u8; 4]| monotone(t)).collect()
}

/// A random monotone map on the powerset of `{0, 1, 2}`: the join of up to four rules "when
/// `x` holds `m`, give `c`", which is monotone, and every monotone map is such a join (one
/// rule per argument).
fn random_monotone_3(rng: &mut Rng) -> [u8; 8] {
    let rules: Vec<(usize, u8)> = (0..1 + rng.below(4))
        .map(|_| (rng.below(8), rng.below(8) as u8))
        .collect();
    std::array::from_fn(|x| {
        rules
            .iter()
            .filter(|&&(m, _)| x & m == m)
            .fold(0, |acc, &(_, c)| acc | c)
    })
}

/// The seeds of the exhaustive runs: every member of the powerset of `{0, 1}`, and the atom.
fn seeds_2() -> Vec<Seed> {
    (0..4).map(Seed::Set).chain([Seed::Fail]).collect()
}

fn seeds_3() -> Vec<Seed> {
    (0..8).map(Seed::Set).chain([Seed::Fail]).collect()
}

// The fixed point identity.

/// `f†(a)` and `f(a, f†(a)) = a ⊔ s(f†(a))`.
fn fixed_point_sides(&(t, a): &([u8; 4], Seed)) -> (Term, Term) {
    let r = fresh("r");
    (
        dagger(seed(a), step(&t)),
        let_(
            &r,
            dagger(seed(a), step(&t)),
            join(seed(a), apply(&t, var(&r))),
        ),
    )
}

#[test]
fn conway_fixed_point_holds_for_every_monotone_step_and_seed() {
    let cases: Vec<_> = monotone_maps_2()
        .into_iter()
        .flat_map(|t| seeds_2().into_iter().map(move |a| (t, a)))
        .collect();
    assert_eq!(holds(cases, fixed_point_sides), 36 * 5);
}

#[test]
fn conway_the_literal_step_with_its_seed_is_not_a_fixed_point() {
    // Negative control: read as `f = s` with the seed outside the operator, `fix` is not a
    // fixed point of the step, since the seed is kept and the step need not give it back.
    let cases: Vec<_> = monotone_maps_2()
        .into_iter()
        .flat_map(|t| (0..4).map(move |a| (t, Seed::Set(a))))
        .collect();
    let (_, l, r) = refuted(cases, |&(t, a)| {
        let r = fresh("r");
        (
            dagger(seed(a), step(&t)),
            let_(&r, dagger(seed(a), step(&t)), apply(&t, var(&r))),
        )
    });
    assert_eq!((l, r), (Ok(Value::Int(1)), Ok(Value::Int(0))));
}

// Naturality in the parameter.

/// A two-argument step `(p, x) ↦ t[p][x]`, monotone in `x` for each `p`, with the parameter
/// `p` reached through `h`: `f†` at `h(q)` computed outside the step, and `(f ∘ (h × id))†`
/// computing `h(q)` inside it.
fn naturality_sides(&(t, h, q, a): &([[u8; 4]; 4], [u8; 4], u8, Seed)) -> (Term, Term) {
    let p = fresh("p");
    let table2 = |p: Term, x: Term| get(get(two_level(&t), p), x);
    let hq = || apply(&h, lit(Value::Int(q as i64)));
    (
        let_(&p, hq(), dagger(seed(a), func(|[x]| table2(var(&p), x)))),
        dagger(seed(a), func(|[x]| table2(hq(), x))),
    )
}

/// The table `p -> x -> t[p][x]`.
fn two_level(t: &[[u8; 4]; 4]) -> Term {
    let rows: Vec<Value> = t
        .iter()
        .map(|r| seq_value(&r.iter().map(|&v| v as i64).collect::<Vec<_>>()))
        .collect();
    lit(seq_value(&rows))
}

#[test]
fn conway_naturality_in_the_parameter_holds() {
    let maps = monotone_maps_2();
    let mut rng = Rng::new(61);
    let mut cases = Vec::new();
    for _ in 0..64 {
        let t: [[u8; 4]; 4] = std::array::from_fn(|_| maps[rng.below(maps.len())]);
        let h: [u8; 4] = std::array::from_fn(|_| rng.below(4) as u8);
        for q in 0..4 {
            for a in seeds_2() {
                cases.push((t, h, q, a));
            }
        }
    }
    assert_eq!(holds(cases, naturality_sides), 64 * 4 * 5);
}

// Dinaturality.

/// With `f(a, x) = s₁(x)` and `g(a, y) = a ⊔ s₂(y)`, so that the seed enters at `g`:
/// `(g ∘ ⟨π₁, f⟩)†(a)` is `fix(a, s₂ ∘ s₁)`, and `g(a, (f ∘ ⟨π₁, g⟩)†(a))` is
/// `a ⊔ s₂(fix(⊥, y ↦ s₁(a ⊔ s₂(y))))`.
fn dinaturality_sides(&(f, g, a): &([u8; 4], [u8; 4], Seed)) -> (Term, Term) {
    let r = fresh("r");
    let inner = dagger(
        lit(Value::Int(0)),
        func(|[y]| apply(&f, join(seed(a), apply(&g, y)))),
    );
    (
        dagger(seed(a), func(|[x]| apply(&g, apply(&f, x)))),
        let_(&r, inner, join(seed(a), apply(&g, var(&r)))),
    )
}

#[test]
fn conway_dinaturality_holds_for_every_pair_of_monotone_steps() {
    let maps = monotone_maps_2();
    let cases: Vec<_> = maps
        .iter()
        .flat_map(|&f| maps.iter().map(move |&g| (f, g)))
        .flat_map(|(f, g)| seeds_2().into_iter().map(move |a| (f, g, a)))
        .collect();
    assert_eq!(holds(cases, dinaturality_sides), 36 * 36 * 5);
}

/// The slid-seed form, the seed moved through the slid map as `gen`'s loop rotation moves its
/// boundary: `fix(g(y₀), g ∘ f)` and `g(fix(y₀, f ∘ g))`.
fn slid_seed_sides(&(f, g, y0): &([u8; 8], [u8; 8], Seed)) -> (Term, Term) {
    (
        dagger(apply(&g, seed(y0)), func(|[x]| apply(&g, apply(&f, x)))),
        apply(&g, dagger(seed(y0), func(|[y]| apply(&f, apply(&g, y))))),
    )
}

#[test]
fn conway_slid_seed_form_holds_when_the_slid_map_preserves_joins() {
    // Proof, for monotone `f` and a `g` that preserves binary joins, with
    // `L = μy. y₀ ⊔ f(g(y))` and `R = μx. g(y₀) ⊔ g(f(x))`:
    // (1) `g(L) = g(y₀ ⊔ f(g(L))) = g(y₀) ⊔ g(f(g(L)))`, so `g(L)` is a fixed point of
    //     `x ↦ g(y₀) ⊔ g(f(x))`, and `R ≤ g(L)`.
    // (2) With `M = y₀ ⊔ f(R)`: `y₀ ⊔ f(g(M)) = y₀ ⊔ f(g(y₀) ⊔ g(f(R))) = y₀ ⊔ f(R) = M`, by
    //     join preservation and then `R = g(y₀) ⊔ g(f(R))`; so `M` is a fixed point of
    //     `y ↦ y₀ ⊔ f(g(y))`, `L ≤ M`, and by monotonicity
    //     `g(L) ≤ g(M) = g(y₀) ⊔ g(f(R)) = R`.
    // Both steps use join preservation of `g` only at binary joins, and `f` only monotone.
    // The atom seed is outside the lattice: `g(#fail)` and every join with it is `#fail`.
    let mut rng = Rng::new(62);
    let mut cases = Vec::new();
    while cases.len() < 9 * 400 {
        let f = random_monotone_3(&mut rng);
        let g = random_monotone_3(&mut rng);
        if preserves_joins(&g) {
            cases.extend(seeds_3().into_iter().map(|y0| (f, g, y0)));
        }
    }
    assert_eq!(holds(cases, slid_seed_sides), 9 * 400);
}

#[test]
fn conway_slid_seed_form_fails_when_the_slid_map_does_not_preserve_joins() {
    // `y₀ = {0}`, `f` constantly `{1}`, and `g` giving `{0, 1}` on `{0, 1}` and above, `∅`
    // elsewhere: `L = {0, 1}`, so `g(L) = {0, 1}`, while `R` starts at `g({0}) = ∅` and
    // `g(f(∅)) = g({1}) = ∅`, so `R = ∅`.
    let f = [2u8; 8];
    let g: [u8; 8] = std::array::from_fn(|x| if x & 3 == 3 { 3 } else { 0 });
    assert!(monotone(&g) && !preserves_joins(&g));
    let (_, l, r) = refuted(vec![(f, g, Seed::Set(1))], slid_seed_sides);
    assert_eq!((l, r), (Ok(Value::Int(0)), Ok(Value::Int(3))));
}

// The diagonal.

/// A random two-argument monotone step on the powerset of `{0, 1, 2}`: a monotone map on
/// the six bits of `(x, y)`, as in `random_monotone_3`.
fn random_monotone_pair(rng: &mut Rng) -> [[u8; 8]; 8] {
    let rules: Vec<(usize, u8)> = (0..1 + rng.below(5))
        .map(|_| (rng.below(64), rng.below(8) as u8))
        .collect();
    std::array::from_fn(|x| {
        std::array::from_fn(|y| {
            let z = x | y << 3;
            rules
                .iter()
                .filter(|&&(m, _)| z & m == m)
                .fold(0, |acc, &(_, c)| acc | c)
        })
    })
}

/// `μx. a ⊔ t[x][x]` and `μx. μy. a ⊔ t[x][y]`, the inner `fix` seeded with `a` too.
fn diagonal_sides(&(t, a): &([[u8; 8]; 8], Seed)) -> (Term, Term) {
    let rows: Vec<Value> = t
        .iter()
        .map(|r| seq_value(&r.iter().map(|&v| v as i64).collect::<Vec<_>>()))
        .collect();
    let t2 = lit(seq_value(&rows));
    let cell = |x: Term, y: Term| get(get(t2.clone(), x), y);
    let x = fresh("x");
    (
        dagger(
            seed(a),
            func(|[x]| {
                let v = fresh("v");
                let_(&v, x, cell(var(&v), var(&v)))
            }),
        ),
        dagger(
            seed(a),
            func(|[x2]| let_(&x, x2, dagger(seed(a), func(|[y]| cell(var(&x), y))))),
        ),
    )
}

#[test]
fn conway_diagonal_holds_for_monotone_two_argument_steps() {
    let mut rng = Rng::new(63);
    let cases: Vec<_> = (0..300)
        .map(|_| random_monotone_pair(&mut rng))
        .flat_map(|t| seeds_3().into_iter().map(move |a| (t, a)))
        .collect();
    assert_eq!(holds(cases, diagonal_sides), 300 * 9);
}

#[test]
fn conway_the_atom_seed_passes_out_of_every_step() {
    // What the atom cases rest on: a `fix` seeded with `#fail` gives `#fail`, as the join and
    // the lookup pass it out (DESIGN.md sec:failure).
    for t in monotone_maps_2() {
        assert_eq!(
            eval(&dagger(seed(Seed::Fail), step(&t))),
            Ok(Value::atom("fail"))
        );
    }
}
