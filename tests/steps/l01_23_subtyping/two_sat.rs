//! Tuple parts that are 2-CNFs over two-valued components (item T6-2sat): the type
//! `(bit, ..., bit) & ∩ (C1 | C2)`, each `Ci` a tuple type that fixes one component to `0` or
//! `1` and holds `top` elsewhere, is decided by an implication graph and its strongly connected
//! components, and a satisfiable one is shown inhabited by the tuple the solution gives.

use zed_kernel::Value;
use zed_kernel::types::{Type, Verdict};
use zed_tests::instances::Rng;
use zed_tests::scaling;

fn lit(i: i64) -> Type {
    Type::lit(&Value::Int(i)).expect("an integer literal")
}

/// A clause: each literal a variable and whether it is taken.
type Clause = Vec<(usize, bool)>;

/// The tuples of `vars` bits, one per variable, in which every clause holds: each literal is
/// the tuple type with that bit fixed and `top` elsewhere.
fn cnf_type(vars: usize, clauses: &[Clause]) -> Type {
    let bit = &lit(0) | &lit(1);
    let cylinder = |v: usize, b: bool| {
        let mut c = vec![Type::top(); vars];
        c[v] = lit(i64::from(b));
        Type::tuple(c)
    };
    let mut t = Type::tuple(vec![bit; vars]);
    for c in clauses {
        let u = (c.iter()).fold(Type::empty(), |u, &(v, b)| &u | &cylinder(v, b));
        t = &t & &u;
    }
    t
}

/// The clauses of shape `name` on `n` variables. `r2`: `n` random clauses of two literals.
/// `chain`: `x0`, `!xi | x(i+1)` and `!x(n-1)`, unsatisfiable only through the whole chain.
/// `chainsat`: the chain without its last clause. `xoreven`: `xi != x(i+1 mod n)`, satisfiable
/// for even `n`. `xorcycle`: the same on the first `n` or `n - 1` variables, whichever is odd,
/// so it is unsatisfiable at every `n`.
fn shape(name: &str, n: usize, seed: u64) -> Vec<Clause> {
    let mut g = Rng::new(seed * 2 + 1);
    match name {
        "r2" => (0..n)
            .map(|_| (0..2).map(|_| (g.below(n), g.below(2) == 0)).collect())
            .collect(),
        "chain" | "chainsat" => {
            let mut c: Vec<Clause> = (0..n - 1)
                .map(|i| vec![(i, false), (i + 1, true)])
                .collect();
            c.push(vec![(0, true)]);
            if name == "chain" {
                c.push(vec![(n - 1, false)]);
            }
            c
        }
        "xorcycle" | "xoreven" => {
            let k = if name == "xoreven" { n } else { n - 1 + n % 2 };
            (0..k)
                .flat_map(|i| {
                    let j = (i + 1) % k;
                    [vec![(i, true), (j, true)], vec![(i, false), (j, false)]]
                })
                .collect()
        }
        _ => unreachable!("no shape {name}"),
    }
}

/// Whether the values `x` hold every clause.
fn holds(x: &[bool], clauses: &[Clause]) -> bool {
    (clauses.iter()).all(|c| c.iter().any(|&(v, b)| x[v] == b))
}

/// Whether some value holds the clauses, by enumeration of all `2^vars`.
fn by_enumeration(vars: usize, clauses: &[Clause]) -> bool {
    (0u64..1 << vars).any(|m| {
        let x: Vec<bool> = (0..vars).map(|v| m >> v & 1 == 1).collect();
        holds(&x, clauses)
    })
}

/// Whether some value holds the clauses of at most two literals, by Even, Itai and Shamir's
/// method: set an unset variable, propagate the clauses left with one literal, and on a
/// contradiction undo and set it the other way; a contradiction both ways means none. A
/// reference written apart from the kernel's, for sizes enumeration cannot reach.
fn by_propagation(vars: usize, clauses: &[Clause]) -> bool {
    let mut x: Vec<Option<bool>> = vec![None; vars];
    // Sets `v` to `b` and propagates; the variables set, or `None` on a contradiction.
    let set = |x: &mut Vec<Option<bool>>, v: usize, b: bool| -> Option<Vec<usize>> {
        let (mut todo, mut done) = (vec![(v, b)], Vec::new());
        while let Some((v, b)) = todo.pop() {
            match x[v] {
                Some(c) if c == b => continue,
                Some(_) => {
                    for &u in &done {
                        x[u] = None;
                    }
                    return None;
                }
                None => {}
            }
            x[v] = Some(b);
            done.push(v);
            for c in clauses {
                if c.iter().any(|&(u, s)| x[u] == Some(s)) {
                    continue;
                }
                let open: Vec<_> = c.iter().filter(|&&(u, _)| x[u].is_none()).collect();
                match open[..] {
                    [] => {
                        for &u in &done {
                            x[u] = None;
                        }
                        return None;
                    }
                    [&(u, s)] => todo.push((u, s)),
                    _ => {}
                }
            }
        }
        Some(done)
    };
    for v in 0..vars {
        if x[v].is_none() && set(&mut x, v, true).is_none() && set(&mut x, v, false).is_none() {
            return false;
        }
    }
    true
}

/// Runs `f` on a 2 MiB stack, the default of a test thread: the search walks deep types, on
/// a stack of its own on the heap. It ran on 256 MiB, which it never needed (TY-sub-stack).
fn deep(f: impl FnOnce() + Send) {
    zed_tests::deep::on_small_stack(f);
}

/// Random clause sets of one and two literals on up to 10 variables, decided as enumeration
/// decides them by both `verdict` and `is_empty`, cold; the inhabited ones with a value built
/// and checked against the type (`Verdict::Inhabited`).
#[test]
fn random_two_cnf_parts_are_decided_as_enumeration_decides_them() {
    deep(|| {
        let mut g = Rng::new(23);
        let (mut empty, mut inhabited) = (0, 0);
        for vars in 1..=10 {
            for _ in 0..24 {
                let m = 1 + g.below(3 * vars);
                let clauses: Vec<Clause> = (0..m)
                    .map(|_| {
                        let width = 1 + g.below(2);
                        (0..width)
                            .map(|_| (g.below(vars), g.below(2) == 0))
                            .collect()
                    })
                    .collect();
                let sat = by_enumeration(vars, &clauses);
                assert_eq!(by_propagation(vars, &clauses), sat, "{clauses:?}");
                let t = cnf_type(vars, &clauses);
                Type::forget_emptiness();
                let expected = if sat {
                    Verdict::Inhabited
                } else {
                    Verdict::Empty
                };
                assert_eq!(t.verdict(), expected, "{vars} variables, {clauses:?}");
                Type::forget_emptiness();
                assert_eq!(t.is_empty(), !sat, "{vars} variables, {clauses:?}");
                if sat {
                    inhabited += 1;
                } else {
                    empty += 1;
                }
            }
        }
        // Both answers are met.
        assert!(
            empty >= 20 && inhabited >= 20,
            "{empty} empty, {inhabited} inhabited"
        );
    });
}

/// The measurement of report Q1Q7 (2-SAT refused 1 of 6 at n = 12, 3 of 6 at 16, 6 of 6 at
/// 48): no refusal on random clause sets at those sizes. Each verdict equals the reference's
/// answer, enumeration at 12 and 16, propagation at 48, and both answers are met.
#[test]
fn random_two_cnf_parts_at_the_reported_sizes_are_never_refused() {
    deep(|| {
        let mut answers = [0usize; 2];
        for n in [12, 16, 48] {
            for seed in 1..=6 {
                let clauses = shape("r2", n, seed);
                let sat = by_propagation(n, &clauses);
                if n <= 16 {
                    assert_eq!(by_enumeration(n, &clauses), sat);
                }
                Type::forget_emptiness();
                let v = cnf_type(n, &clauses).verdict();
                let expected = if sat {
                    Verdict::Inhabited
                } else {
                    Verdict::Empty
                };
                assert_eq!(v, expected, "r2 n = {n}, seed {seed}");
                answers[usize::from(sat)] += 1;
            }
        }
        assert!(answers[0] > 0 && answers[1] > 0, "{answers:?}");
    });
}

/// The chain, the chain left open, and the parity cycle of odd and even length are decided:
/// the chain and the odd cycle are empty, the others inhabited.
#[test]
fn chains_and_parity_cycles_are_decided() {
    deep(|| {
        for (name, n, sat) in [
            ("chain", 40, false),
            ("chainsat", 40, true),
            ("xorcycle", 41, false),
            ("xoreven", 40, true),
        ] {
            let clauses = shape(name, n, 0);
            assert_eq!(by_propagation(n, &clauses), sat, "{name} {n}");
            Type::forget_emptiness();
            let expected = if sat {
                Verdict::Inhabited
            } else {
                Verdict::Empty
            };
            assert_eq!(cnf_type(n, &clauses).verdict(), expected, "{name} {n}");
        }
    });
}

/// Corner cases: no clause (the box alone), one unit clause, a unit clause and its complement,
/// and a clause of one literal written twice.
#[test]
fn an_empty_clause_set_and_unit_clauses_are_decided() {
    deep(|| {
        let cases: [(usize, Vec<Clause>, Verdict); 5] = [
            (3, vec![], Verdict::Inhabited),
            (1, vec![vec![(0, true)]], Verdict::Inhabited),
            (3, vec![vec![(1, false)]], Verdict::Inhabited),
            (3, vec![vec![(1, false)], vec![(1, true)]], Verdict::Empty),
            (
                2,
                vec![vec![(0, true), (0, true)], vec![(0, false), (1, true)]],
                Verdict::Inhabited,
            ),
        ];
        for (vars, clauses, expected) in cases {
            Type::forget_emptiness();
            assert_eq!(cnf_type(vars, &clauses).verdict(), expected, "{clauses:?}");
        }
    });
}

/// Pigeonhole with 3 holes: each of 4 pigeons in some hole is a clause of 3 literals, so the
/// part is no 2-CNF and is left to the search, as before; it is unsatisfiable, and the answer
/// is never `Inhabited`. The search decides it at this size; the point of the test is that the
/// 2-CNF reading does not take a clause of three literals.
#[test]
fn pigeonhole_is_left_to_the_search() {
    deep(|| {
        let holes = 3;
        let vars = (holes + 1) * holes;
        let mut clauses: Vec<Clause> = (0..=holes)
            .map(|p| (0..holes).map(|h| (p * holes + h, true)).collect())
            .collect();
        for h in 0..holes {
            for p in 0..=holes {
                for q in 0..p {
                    clauses.push(vec![(p * holes + h, false), (q * holes + h, false)]);
                }
            }
        }
        assert!(!by_enumeration(vars, &clauses));
        Type::forget_emptiness();
        let v = cnf_type(vars, &clauses).verdict();
        assert_ne!(v, Verdict::Inhabited);
    });
}

/// The shape `name` on `m` variables as a type, the verdict the reference gives it, and the
/// type's size, counted as clauses times components.
fn instance(name: &str, m: usize) -> (Type, Verdict, usize) {
    let clauses = shape(name, m, 0);
    let expected = if by_propagation(m, &clauses) {
        Verdict::Inhabited
    } else {
        Verdict::Empty
    };
    (cnf_type(m, &clauses), expected, clauses.len() * m)
}

/// Decides an instance built before the run, cold.
fn decide(name: &str, m: usize, (t, expected, _): &(Type, Verdict, usize)) {
    Type::forget_emptiness();
    assert_eq!(t.verdict(), *expected, "{name} {m}");
}

/// The variable counts of [`scales`]. The input's size is that of the type: about one clause
/// per variable, each a union of tuple types of one component per variable, so of order
/// `vars^2`, and 45 and 128 variables give it 8 times over.
const VARS: (usize, usize) = (45, 128);

/// The cost of deciding a shape at the variable counts `VARS`, the types built before the runs,
/// under the limit of 13 times ([`scaling::limit`]); the sizes of the types are 7.9 to 8.2 times
/// apart.
fn scales(name: &str) {
    let ((a, b), small, large) = (VARS, instance(name, VARS.0), instance(name, VARS.1));
    let ratio = large.2 as f64 / small.2 as f64;
    assert!((7.9..8.2).contains(&ratio), "{name}: size ratio {ratio}");
    scaling::compare(
        &format!(
            "2-CNF {name}: {a} and {b} variables, sizes {} and {}, {ratio:.2} times",
            small.2, large.2
        ),
        1,
        || decide(name, a, &small),
        || decide(name, b, &large),
    );
}

/// Small instance of the four benchmarks of [`scales`] (TEST-bench-move-l0123, author P170):
/// the chain, the open chain and the parity cycle at every small number of variables, odd and
/// even, decided as enumeration decides them. At an even count the parity cycle is on all but
/// the last variable, which no clause reads; `chains_and_parity_cycles_are_decided` runs it
/// only at an odd count.
#[test]
fn chains_and_parity_cycles_of_every_small_size_are_decided() {
    deep(|| {
        for name in ["chain", "chainsat", "xorcycle"] {
            for n in 1..=12 {
                let sat = by_enumeration(n, &shape(name, n, 0));
                let made = instance(name, n);
                assert_eq!(made.1 == Verdict::Inhabited, sat, "{name} {n}");
                decide(name, n, &made);
            }
        }
    });
}

mod bench;
