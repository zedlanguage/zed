//! The shapes on which deciding whether a trivial model exists is NP-complete, and what the
//! report does there.
//!
//! Equations alone encode 3-SAT. A field `p` of two arguments with the law `p(x, x) == x` is a
//! projection, so it is one bit: true when it returns `x`, its first argument. A clause
//! `a || b || !c` is the law `p_a(x, p_b(x, p_c(y, x))) == x`: the left side reaches `x` exactly
//! when some literal of the clause is true, and otherwise ends at `y`. So the trivial models of
//! the theory are the satisfying assignments of the formula. A second family needs no equation:
//! fields of no arguments with the laws `a != b || b != c`, one per triple, are the 2-colourings
//! of a 3-uniform hypergraph, which is NP-complete to decide (Lovász 1973).

use zed_tests::instances::Rng;

use super::brute::describe;
use super::trivial::{End, Mode, Theory, render, report};

/// A clause as its literals, each a variable and whether it is negated.
type Clause = Vec<(usize, bool)>;

/// The theory of a CNF over `n` variables: one projection field per variable, one law per
/// clause.
pub fn sat_theory(n: usize, clauses: &[Clause]) -> Theory {
    let mut t = Theory::new("Sat");
    for i in 0..n {
        t.field(&format!("p{i}"), 2);
    }
    for i in 0..n {
        t.law(&format!("proj{i}"), "x y", &format!("p{i}(x, x) == x"));
    }
    for (k, clause) in clauses.iter().enumerate() {
        let mut term = "y".to_string();
        for &(v, negated) in clause.iter().rev() {
            term = if negated {
                format!("p{v}({term}, x)")
            } else {
                format!("p{v}(x, {term})")
            };
        }
        t.law(&format!("clause{k}"), "x y", &format!("{term} == x"));
    }
    t
}

/// `m` random clauses over `n` variables, three distinct variables each.
pub fn random_cnf(rng: &mut Rng, n: usize, m: usize) -> Vec<Clause> {
    (0..m)
        .map(|_| {
            let a = rng.below(n);
            let mut b = rng.below(n);
            while b == a {
                b = rng.below(n);
            }
            let mut c = rng.below(n);
            while c == a || c == b {
                c = rng.below(n);
            }
            vec![
                (a, rng.below(2) == 1),
                (b, rng.below(2) == 1),
                (c, rng.below(2) == 1),
            ]
        })
        .collect()
}

/// The number of assignments that satisfy `clauses`, by trying all `2^n`.
fn count_sat(n: usize, clauses: &[Clause]) -> u64 {
    (0..1u64 << n)
        .filter(|bits| {
            clauses
                .iter()
                .all(|cl| cl.iter().any(|&(v, neg)| ((bits >> v) & 1 == 1) != neg))
        })
        .count() as u64
}

/// The number of models the exhaustive report lists: the product of its groups' counts.
fn model_count(t: &Theory) -> (u64, u64) {
    let r = report(t, Mode::Exhaustive);
    assert!(r.free.is_empty());
    let count = r.groups.iter().map(|g| g.models.len() as u64).product();
    let dead = r.groups.iter().map(|g| g.dead_ends).sum();
    (count, dead)
}

#[test]
fn clause_laws_have_one_model_per_satisfying_assignment() {
    let mut rng = Rng::new(0x5a7_c1a5e);
    let mut with_dead_ends = 0;
    for _ in 0..300 {
        let n = 4 + rng.below(9);
        let m = rng.below(5 * n);
        let cnf = random_cnf(&mut rng, n, m);
        let t = sat_theory(n, &cnf);
        let (count, dead) = model_count(&t);
        assert_eq!(count, count_sat(n, &cnf), "{}", describe(&t));
        with_dead_ends += usize::from(dead > 0);
    }
    eprintln!("random 3-CNF theories with a dead end: {with_dead_ends} of 300");
    assert!(with_dead_ends > 0);
}

/// The Fano plane: seven points and seven lines of three, which no 2-colouring leaves
/// without a line of one colour.
fn fano() -> Theory {
    let mut t = Theory::new("Fano");
    for i in 1..=7 {
        t.field(&format!("c{i}"), 0);
    }
    let lines = [
        [1, 2, 3],
        [1, 4, 5],
        [1, 6, 7],
        [2, 4, 6],
        [2, 5, 7],
        [3, 4, 7],
        [3, 5, 6],
    ];
    for (k, [a, b, c]) in lines.into_iter().enumerate() {
        t.law(
            &format!("line{}", k + 1),
            "",
            &format!("c{a} != c{b} || c{b} != c{c}"),
        );
    }
    t
}

#[test]
fn nae_fano_has_no_model() {
    let t = fano();
    let full = report(&t, Mode::Exhaustive);
    assert_eq!(full.groups.len(), 1);
    let g = &full.groups[0];
    assert!(g.models.is_empty());
    assert!(g.dead_ends > 0);
    eprintln!("Fano: {} choices, {} dead ends", g.nodes, g.dead_ends);
    let short = report(&t, Mode::Default);
    let text = render(&t, &short);
    eprint!("{text}");
    assert!(matches!(short.groups[0].end, End::Stopped(_)), "{text}");
    assert_eq!(
        text,
        "\
trivial models of Fano
  on one value, #a: law line1 (c1 != c2 || c2 != c3) does not hold, since on one value every two values are equal.
  on two values, #a | #b:
    c1, c2, c3, c4, c5, c6, c7, linked by laws line1, line2, line3, line4, line5, line6, line7: not decided.
      The report stopped at a choice that leads to no model, so this list may be incomplete:
        with c1: #a, c2: #a, c4: #a
        c3 cannot be #a, by law line1: c1 != c2 || c2 != c3
        c5 cannot be #a, by law line2: c1 != c4 || c4 != c5
        c6 cannot be #a, by law line4: c2 != c4 || c4 != c6
        so law line7: c3 != c5 || c5 != c6 does not hold
      Whether laws like these have a model can take time exponential in the number of fields to decide, so the report does not search on by itself. To list every trivial model, at the cost of that search, write `@exhaustive` before the interface:
        @exhaustive interface Fano(T) { ... }
"
    );
}

/// The pigeonhole formula: `h + 1` pigeons each in one of `h` holes, no two in one hole. It is
/// unsatisfiable, and every resolution refutation of it has 2^Ω(h) clauses (Haken 1985).
fn pigeonhole(h: usize) -> (usize, Vec<Clause>) {
    let var = |p: usize, j: usize| p * h + j;
    let mut clauses: Vec<Clause> = (0..=h)
        .map(|p| (0..h).map(|j| (var(p, j), false)).collect())
        .collect();
    for j in 0..h {
        for p in 0..=h {
            for q in p + 1..=h {
                clauses.push(vec![(var(p, j), true), (var(q, j), true)]);
            }
        }
    }
    ((h + 1) * h, clauses)
}

/// The search on the pigeonhole theories: no model, and dead ends that grow faster than any
/// exponential in the holes. The search's dead ends with the laws they used form a tree-like
/// resolution refutation, so no order of the fields avoids an exponential count here.
#[test]
fn dead_ends_grow_exponentially_on_pigeonholes() {
    let mut dead = Vec::new();
    for h in 1..=6 {
        let (n, cnf) = pigeonhole(h);
        let (count, d) = model_count(&sat_theory(n, &cnf));
        assert_eq!(count, 0);
        eprintln!("pigeonhole, {h} holes, {n} fields: {d} dead ends");
        dead.push(d as f64);
    }
    // Each hole more multiplies the dead ends by more than the one before it did.
    for w in dead[1..].windows(3) {
        assert!(w[2] / w[1] > w[1] / w[0], "dead ends {dead:?}");
    }
}

/// The dead ends of the exhaustive search on random 3-CNF with 5 clauses per variable, most of
/// them unsatisfiable: a measurement for the report, since random 3-CNF of fixed density needs
/// resolution refutations of size 2^Ω(n) (Chvátal and Szemerédi 1988) but the constant is small
/// enough that the growth looks polynomial below about 100 variables.
#[test]
fn dead_ends_on_random_3_cnf() {
    let mut means = Vec::new();
    for n in [10, 20, 40, 80] {
        let mut rng = Rng::new(0xdead_0000 + n as u64);
        let runs = 8;
        let mut total = 0;
        for _ in 0..runs {
            let cnf = random_cnf(&mut rng, n, 5 * n);
            total += model_count(&sat_theory(n, &cnf)).1;
        }
        let mean = total as f64 / runs as f64;
        eprintln!("n = {n}: mean dead ends {mean}");
        means.push(mean);
    }
    for w in means.windows(2) {
        assert!(w[1] > w[0], "dead ends {means:?}");
    }
}
