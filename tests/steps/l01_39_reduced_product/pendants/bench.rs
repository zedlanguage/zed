//! Benchmarks of `pendants` (ST-eqs-rest-exact): the projection by pendants of a part of `k`
//! pendants on one form `a + b` of two hubs, each family one of the shapes the route admits
//! since ST-eqs-rest-exact (R1_CLAUDE Finding B2 and T1, R1_CODEX D and B): coefficients other
//! than one (B), holes in the pendants' names (C), two disjunctions among the hubs (D). Each
//! times one `assume` of the conjunction of the `k` pendants at `k` and `8k`, in a scope whose
//! hubs and holes were assumed before the timing, and counts the systems the solver is asked
//! about ([`solved_in`]), which on the route is one question about the form, whatever `k`.
//! What each family answers is checked at a small size in `pendants.rs`
//! (`the_benchmark_families_are_exact_at_a_small_size`).
//!
//! The negative control of each is the same input on the base of ST-eqs-rest-exact (3d28e21c5),
//! where the route refuses each of these parts and the whole part is projected instead: its
//! counts and ratios are in the report of the row.

use super::*;
use zed_tests::scaling;

/// The hubs of every family: `a`, `b` in `[0, 100000]`, `a + b <= 150000`, `a < 3 || b > 7`,
/// and with `two` also `a > 11 || b < 5`; the names `z0` .. `z{k-1}`, each unbounded.
pub(super) fn hubs(k: usize, two: bool) -> Scope {
    let p = Premises::new();
    let mut names: Vec<Arc<str>> = vec!["a".into(), "b".into()];
    names.extend((0..k).map(|i| Arc::from(format!("z{i}"))));
    let mut s = ints(&names);
    for n in ["a", "b"] {
        s = s
            .assume(&prim(Prim::Ge, vec![var(n), lit(0)]), true, &p)
            .assume(&prim(Prim::Le, vec![var(n), lit(100_000)]), true, &p);
    }
    let sum = prim(Prim::Add, vec![var("a"), var("b")]);
    let or = |x: Term, y: Term| prim(Prim::Or, vec![x, y]);
    s = s
        .assume(&prim(Prim::Le, vec![sum, lit(150_000)]), true, &p)
        .assume(
            &or(
                prim(Prim::Lt, vec![var("a"), lit(3)]),
                prim(Prim::Gt, vec![var("b"), lit(7)]),
            ),
            true,
            &p,
        );
    if two {
        s = s.assume(&extra_disjunction(1), true, &p);
    }
    s
}

/// The `d`-th disjunction among the hubs after the first (`a < 3 || b > 7`), from 1: `a > 11
/// || b < 5`, then `a > 20 || b < 30`, then `a < 40 || b > 50`, each with points on both
/// arms, so the hub question has `2^(d + 1)` conjunctions at most.
pub(super) fn extra_disjunction(d: usize) -> Term {
    let or = |x: Term, y: Term| prim(Prim::Or, vec![x, y]);
    match d {
        1 => or(
            prim(Prim::Gt, vec![var("a"), lit(11)]),
            prim(Prim::Lt, vec![var("b"), lit(5)]),
        ),
        2 => or(
            prim(Prim::Gt, vec![var("a"), lit(20)]),
            prim(Prim::Lt, vec![var("b"), lit(30)]),
        ),
        _ => or(
            prim(Prim::Lt, vec![var("a"), lit(40)]),
            prim(Prim::Gt, vec![var("b"), lit(50)]),
        ),
    }
}

/// `z{i}`.
fn z(i: usize) -> Term {
    var(&format!("z{i}"))
}

/// `a + b - c * z{i} == c * j`.
fn pendant(i: usize, c: i64, j: i64) -> Term {
    let sum = prim(Prim::Add, vec![var("a"), var("b")]);
    let cz = if c == 1 {
        z(i)
    } else {
        prim(Prim::Mul, vec![lit(c), z(i)])
    };
    prim(Prim::Eq, vec![prim(Prim::Sub, vec![sum, cz]), lit(c * j)])
}

/// The conjunction of `terms`, nested to the right.
pub(super) fn all(terms: Vec<Term>) -> Term {
    (terms.into_iter().rev())
        .reduce(|r, t| prim(Prim::And, vec![t, r]))
        .expect("a term")
}

/// A family's input at `k`: the scope with its hubs (and holes) and the conjunction timed.
pub(super) type Family = (Scope, Term);

/// B: `a + b - 2 * z{i} == 2 * i`, so `a + b` even, one class modulo 2 (Codex's B: offsets
/// `2 * i`, since offsets `i` ask two parities and empty the part at `k = 2`).
pub(super) fn b_even(k: usize) -> Family {
    (
        hubs(k, false),
        all((0..k).map(|i| pendant(i, 2, i as i64)).collect()),
    )
}

/// B with coefficients 2 and 3 alternating, `a + b - c * z{i} == c * i`: classes 0 modulo 2
/// and 0 modulo 3, met by the Chinese remainder theorem in one class modulo 6 (R1_CLAUDE B2).
pub(super) fn b_mixed(k: usize) -> Family {
    let c = |i: usize| if i % 2 == 0 { 2 } else { 3 };
    (
        hubs(k, false),
        all((0..k).map(|i| pendant(i, c(i), i as i64)).collect()),
    )
}

/// C spaced: `z{i} != 3` assumed before, then `a + b - z{i} == 2 * i`, so the form misses
/// `3 + 2i` for each `i`, `k` holes apart from one another (R1_CLAUDE T1, 4.).
pub(super) fn c_spaced(k: usize) -> Family {
    let p = Premises::new();
    let mut s = hubs(k, false);
    for i in 0..k {
        s = s.assume(&prim(Prim::Ne, vec![z(i), lit(3)]), true, &p);
    }
    (
        s,
        all((0..k).map(|i| pendant(i, 1, 2 * i as i64)).collect()),
    )
}

/// D: two disjunctions among the hubs and `a + b - z{i} == i` (the fixture of R1_CODEX D).
pub(super) fn d_two(k: usize) -> Family {
    (
        hubs(k, true),
        all((0..k).map(|i| pendant(i, 1, i as i64)).collect()),
    )
}

/// The systems the solver is asked about while `run` runs, on this thread
/// (`presburger::systems_solved`, which resets its count when read).
fn solved_in(run: impl FnOnce()) -> u64 {
    presburger::systems_solved();
    run();
    presburger::systems_solved()
}

/// Times `family` at `n` and `8n` ([`scaling::check_inputs`]) and holds the count of systems
/// solved at the two sizes to [`scaling::hold_linear`].
fn family_scales(what: &str, n: usize, family: fn(usize) -> Family) {
    let p = Premises::new();
    let count = |k: usize| {
        let (s, t) = family(k);
        solved_in(|| {
            s.assume(&t, true, &p);
        })
    };
    scaling::hold_linear(
        &format!("{what}: systems solved at {n} and {}", 8 * n),
        "systems",
        count(n),
        count(8 * n),
    );
    scaling::check_inputs(what, n, family, |(s, t)| {
        s.assume(t, true, &Premises::new());
    });
}

// Complexity tradeoff: the cost the benchmarks below hold, for one call of
// `Scope::project_by_pendants` on a part of `k` pendants of `f` forms on `h` hubs, with `d`
// disjunctions among the hubs (each a conjunct `Or`, or a hub with a hole) and `P` pieces in all
// of the forms' allowed sets: O(k) to find the pendants and meet their allowed sets, O(f) rows
// added, one question to the exact cover of size O(h + f + P), whose work is exponential in `d`
// at worst (each disjunction splits the question; Presburger projection is NP-hard already
// with `d = 0`), and O(k) to read each pendant's name back from its form's answer, plus the
// output, whose pieces are those of `W` for each name. Here `f = 1`, `h = 2`, `d` = 1 to 3 and
// `P` = 1 for B and D, while C-spaced has `P = k + 1` pieces, so its output is `k (k + 1)`
// pieces, Theta(k^2), until each name's set is held as an affine image of `W`
// (ST-eqs-rest-cost); at k = 16 and 128 the rest of the work still hides it (7.4 times the
// work for 8 times k, first run on a v5e VM, 2026-11-23).
// The one question of B is flat in `k` but large: 0.57 s and 1.09 GB at k = 16 for B even
// (base: 9 ms, but 26.6 times the bytes at 8 times k). Its cost is in zedc-presburger's exact
// module, not here: the class row `w == M * t + r` under a disjunction among the hubs makes it
// list strided parts value by value where they meet plain ranges (`projection::ranges`,
// `Classed::join` of two classes), O(v) for the v values of the hubs' boxes, each value charged
// to the work meter, so a box too wide is refused there and the whole part projected instead.
// Measured (2026-11-23, a, b in [0, R]): 4 ms at R = 10^3, 26 ms at 10^4, 270 ms at 10^5;
// 0 ms with no disjunction or no class row. Fixing it means keeping strided parts unlisted in
// the exact projection, a row of its own.

#[test]
fn a_part_of_pendants_with_coefficient_two_is_projected_in_linear_time() {
    family_scales("k pendants a + b - 2 zi == 2i, one assume", 16, b_even);
}

#[test]
fn a_part_of_pendants_with_coefficients_two_and_three_is_projected_in_linear_time() {
    family_scales(
        "k pendants a + b - c zi == c i, c = 2, 3, one assume",
        16,
        b_mixed,
    );
}

#[test]
fn a_part_of_pendants_under_two_disjunctions_is_projected_in_linear_time() {
    family_scales(
        "k pendants a + b - zi == i under two disjunctions, one assume",
        16,
        d_two,
    );
}

#[test]
fn a_part_of_pendants_with_spaced_holes_is_projected_in_linear_time() {
    family_scales(
        "k pendants a + b - zi == 2i, zi != 3, one assume",
        16,
        c_spaced,
    );
}

/// `a + b - z{i} == i` under `d` disjunctions among the hubs (`a < 3 || b > 7` and the first
/// `d - 1` of [`extra_disjunction`]).
fn e_under(d: usize, k: usize) -> Family {
    let p = Premises::new();
    let mut s = hubs(k, false);
    for e in 1..d {
        s = s.assume(&extra_disjunction(e), true, &p);
    }
    (s, all((0..k).map(|i| pendant(i, 1, i as i64)).collect()))
}

/// `d` as a parameter apart from `k`: for each of `d` = 1, 2 and 3 disjunctions among the hubs,
/// `k` pendants at `k` and `8k`, each held to the limit on its own. The work at fixed `k` grows
/// with `d` (printed: 192, 670 and 688 systems at `k = 64`, a first run), which the cost comment
/// above bounds by an exponential in `d` and no ratio here holds; what is held is that for
/// each `d` the work stays linear in `k`.
#[test]
fn a_part_of_pendants_is_projected_in_linear_time_for_one_two_and_three_disjunctions() {
    let fs: [fn(usize) -> Family; 3] = [|k| e_under(1, k), |k| e_under(2, k), |k| e_under(3, k)];
    for (d, f) in (1..=3).zip(fs) {
        family_scales(
            &format!("k pendants a + b - zi == i under d = {d} disjunctions, one assume"),
            16,
            f,
        );
    }
}
