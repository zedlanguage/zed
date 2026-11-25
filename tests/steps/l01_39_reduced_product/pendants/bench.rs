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

/// One disjunction of `k` disjuncts over the names `x0` .. `x{m-1}`, each in `[0, 100]` and
/// linked in one group by `x{i} + x{i+1} <= 150` (PERF-pendants-dnf-hull-sides): disjunct `j`
/// is `x0 + x{m-1} >= j && x0 <= x{m-1} + j`, which leaves every name its whole box, so once
/// one disjunct is read no name needs asking of the others.
fn one_wide_disjunction(m: usize, k: usize) -> (Scope, Formula, Vec<Atom>) {
    let last = m - 1;
    let mut text: Vec<String> = (0..last)
        .map(|i| format!("x{i} + x{} <= 150", i + 1))
        .collect();
    let arms: Vec<String> = (0..k)
        .map(|j| format!("x0 + x{last} >= {j} && x0 <= x{last} + {j}"))
        .collect();
    text.push(format!("({})", arms.join(" || ")));
    let items = parse(&text.join(" && "));
    let bs = (0..m)
        .map(|i| (format!("x{i}"), vec![(Some(0), Some(100))]))
        .collect();
    (scope(&bs), formula(&items), item_names(&items))
}

/// The hull sides asked by one `project_each_boxed` of [`one_wide_disjunction`] with `k`
/// names and `k` disjuncts, at `k` and `8k`, held linear, and the time of one with six names
/// and `k` disjuncts. Each disjunct asked for every name of its group was `2 k^2` sides with
/// `k` names, Theta(k^2) (128 and 8192 on main, 64 times); a name is now asked only of the
/// disjuncts read before the union of their hulls holds the name's hull
/// (`Level::start_disjunct`), so the first disjunct is asked for each name and the rest for
/// none. Every name keeps its box, none refused. The time is held with the names fixed: with
/// `k` names each disjunct is also settled with its base group of `k` rows, Theta(k^2) work
/// apart from the sides (39.2 times the instructions at 8k, first run), row
/// PERF-disjunct-base-group-each.
#[test]
fn hull_sides_of_a_disjunction_grow_linearly_in_its_disjuncts() {
    let sides = |k: usize| {
        let (s, f, syms) = one_wide_disjunction(k, k);
        presburger::hull_sides_asked();
        let got = boxed_names(&s, &f, &syms);
        let sides = presburger::hull_sides_asked();
        let whole = IntervalSet::range(End::Fin(Num::from(0)), End::Fin(Num::from(100)));
        for (n, (set, refused)) in &got {
            assert!(set == &whole && !refused, "k = {k}: {n} {set:?} {refused}");
        }
        sides
    };
    scaling::hold_linear(
        "one disjunction of k disjuncts over k linked names: hull sides at 8 and 64",
        "hull sides",
        sides(8),
        sides(64),
    );
    scaling::check_inputs(
        "one disjunction of k disjuncts over 6 linked names, project_each_boxed",
        8,
        |k| one_wide_disjunction(6, k),
        |(s, f, syms)| {
            boxed_names(s, f, syms);
        },
    );
}

/// A family's input for `k` additions: the scope with its hubs (and holes), and the `k`
/// pendants, each assumed alone, one after another (ST-eqs-rest-cost).
type Additions = (Scope, Vec<Term>);

/// The pendants of `family`'s conjunction, apart.
fn apart(family: Family) -> Additions {
    fn split(t: &Term, out: &mut Vec<Term>) {
        match t {
            Term::Prim(Prim::And, v) if v.len() == 2 => {
                split(&v[0], out);
                split(&v[1], out);
            }
            t => out.push(t.clone()),
        }
    }
    let (s, t) = family;
    let mut out = Vec::new();
    split(&t, &mut out);
    (s, out)
}

/// The `k` additions of `ts` to `s`, one `assume` each.
fn add_each(s: &Scope, ts: &[Term]) -> Scope {
    let p = Premises::new();
    ts.iter().fold(s.clone(), |s, t| s.assume(t, true, &p))
}

/// Times `k` additions of `family`'s pendants, one `assume` each, at `n` and `8n`
/// ([`scaling::check_inputs`]), and holds the systems solved at the two sizes to
/// [`scaling::hold_linear`]: each addition asks one question of the form at most, so `k`
/// additions ask O(k).
fn additions_scale(what: &str, n: usize, family: fn(usize) -> Family) {
    let count = |k: usize| {
        let (s, ts) = apart(family(k));
        solved_in(|| {
            add_each(&s, &ts);
        })
    };
    scaling::hold_linear(
        &format!("{what}: systems solved at {n} and {}", 8 * n),
        "systems",
        count(n),
        count(8 * n),
    );
    scaling::check_inputs(
        what,
        n,
        |k| apart(family(k)),
        |(s, ts)| {
            add_each(s, ts);
        },
    );
}

/// E: `a + b - z{i} == i` under the one disjunction `a < 3 || b > 7`, the route of unit
/// coefficients with no hole and no class.
fn e_one(k: usize) -> Family {
    e_under(1, k)
}

#[test]
fn k_additions_of_unit_pendants_take_linear_time() {
    additions_scale("k additions a + b - zi == i, one assume each", 16, e_one);
}

#[test]
fn k_additions_of_pendants_with_coefficient_two_take_linear_time() {
    additions_scale(
        "k additions a + b - 2 zi == 2i, one assume each",
        16,
        b_even,
    );
}

#[test]
fn k_additions_of_pendants_with_spaced_holes_take_linear_time() {
    additions_scale(
        "k additions a + b - zi == 2i, zi != 3, one assume each",
        16,
        c_spaced,
    );
}

#[test]
fn k_additions_of_pendants_under_two_disjunctions_take_linear_time() {
    additions_scale(
        "k additions a + b - zi == i under two disjunctions, one assume each",
        16,
        d_two,
    );
}

/// TEMPORARY probes (remove before landing): one run of `k` additions of each family, for a
/// callgrind profile at k = 16 and 64.
#[test]
fn probe_additions() {
    let k: usize = std::env::var("PROBE_K").map_or(16, |v| v.parse().expect("a count"));
    let family: fn(usize) -> Family = match std::env::var("PROBE_F").as_deref() {
        Ok("b") => b_even,
        Ok("c") => c_spaced,
        _ => e_one,
    };
    let (s, ts) = apart(family(k));
    std::hint::black_box(add_each(&s, &ts));
}
