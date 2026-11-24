//! Questions over shared conjunctions, decided from the answers of the conjunction each extends
//! (`presburger::extend`, LOAD-chain-share): each answer is the one `decide` gives the whole,
//! and a chain of n extensions is decided in time of its links.

use zedc::store::presburger::extend::{Answers, Extending, counts};
use zedc::store::presburger::{Atom, Con, Formula, Lin, decide};

pub(super) fn sym(name: &str) -> Lin {
    Lin::atom(Atom::Sym(name.into()))
}

/// `a >= b`.
pub(super) fn ge(a: Lin, b: Lin) -> Formula {
    Formula::Con(Con::ge(&a, &b))
}

/// `part && rest`, with `part` kept whole, as the translator joins a call's relation.
pub(super) fn extend(part: &Formula, rest: Vec<Formula>) -> Formula {
    let mut fs = vec![part.clone()];
    fs.extend(rest);
    Formula::and_keeping(fs, |i| i == 0)
}

/// The answers `decide` gives `f` and its negation.
pub(super) fn decided(f: &Formula) -> Answers {
    Answers {
        holds: decide(f),
        fails: decide(&Formula::negate(f.clone())),
    }
}

/// `x + k * y <= c`.
pub(super) fn sum(k: i64, c: i64) -> Formula {
    ge(Lin::constant(c), sym("x").plus(&sym("y").times(k)))
}

#[test]
fn each_answer_is_the_one_the_whole_has() {
    let (x, y) = (sym("x"), sym("y"));
    // A conjunction of two, so that it is kept whole and not one constraint.
    let base = Formula::and(vec![
        ge(x.clone(), y.clone()),
        ge(y.clone(), Lin::constant(0)),
    ]);
    // Holding everywhere: x >= 0 or x <= -1 with y in either of two halves, not seen as `true`
    // when it is built.
    let halves = |v: &Lin| {
        Formula::or(vec![
            ge(v.clone(), Lin::constant(0)),
            ge(Lin::constant(-1), v.clone()),
        ])
    };
    let everywhere = Formula::and(vec![halves(&x), halves(&y)]);
    let empty = Formula::and(vec![
        ge(x.clone(), Lin::constant(5)),
        ge(Lin::constant(4), x.clone()),
    ]);
    let cases = [
        // The point of the part serves.
        extend(&base, vec![ge(Lin::constant(100), x.clone())]),
        // The point of the part does not serve: decided whole.
        extend(
            &base,
            vec![
                ge(x.clone(), Lin::constant(50)),
                ge(y.clone(), Lin::constant(7)),
            ],
        ),
        // Nowhere, by the new parts alone.
        extend(&base, vec![ge(Lin::constant(-1), y.clone())]),
        // Nowhere, since the part holds nowhere.
        extend(&empty, vec![ge(x.clone(), Lin::constant(0))]),
        // The part holds everywhere: the negation is that of the new parts.
        extend(&everywhere, vec![ge(x.clone(), Lin::constant(3))]),
        extend(&everywhere, vec![]),
        // A part of a part.
        extend(&extend(&base, vec![sum(2, 40)]), vec![sum(3, 60)]),
        // No kept part, and not a conjunction.
        Formula::and(vec![ge(x.clone(), y.clone()), ge(y.clone(), x.clone())]),
        ge(x.clone(), Lin::constant(1)),
        Formula::or(vec![base.clone(), empty.clone()]),
    ];
    let mut e = Extending::new();
    for f in &cases {
        assert_eq!(e.answers(f), decided(f), "{f}");
        // Asked again, from what is remembered.
        assert_eq!(e.answers(f), decided(f), "{f} again");
    }
    // Each in a new memory, so that no answer depends on what was asked before.
    for f in &cases {
        assert_eq!(Extending::new().answers(f), decided(f), "{f} alone");
    }
}

/// The links `f{i} = f{i-1} && x + i * y >= 1000 i` over `x >= y + 1, y >= 0`, `1..=n`.
pub(super) fn a_moving_chain(n: usize) -> Vec<Formula> {
    let mut f = Formula::and(vec![
        ge(sym("x"), sym("y").plus(&Lin::constant(1))),
        ge(sym("y"), Lin::constant(0)),
    ]);
    let mut out = Vec::with_capacity(n);
    for i in 1..=n as i64 {
        let row = ge(sym("x").plus(&sym("y").times(i)), Lin::constant(1000 * i));
        f = extend(&f, vec![row]);
        out.push(f.clone());
    }
    out
}

/// The links `f{i} = f{i-1} && y >= 2 i x - i²` over `y >= 0`, `1..=n`: each row is the
/// tangent of `y = x²` at `x = i`, so each bounds the region, and every row is kept. META1 A1
/// writes this chain `i x + y >= i²`, but those rows meet in a region bounded by the first and
/// the last alone: for a fixed `x`, `i² - i x` is convex in `i`, so its largest value over
/// `1..=n` is at `i = 1` or `i = n`. The tangents keep the intent, every row a bound.
pub(super) fn a_tangent_chain(n: usize) -> Vec<Formula> {
    let mut f = Formula::and(vec![
        ge(sym("y"), Lin::constant(0)),
        ge(Lin::constant(1_000_000), sym("x")),
    ]);
    let mut out = Vec::with_capacity(n);
    for i in 1..=n as i64 {
        let row = ge(sym("y").plus(&Lin::constant(i * i)), sym("x").times(2 * i));
        f = extend(&f, vec![row]);
        out.push(f.clone());
    }
    out
}

#[test]
fn a_chain_whose_points_move_keeps_few_rows() {
    // The point found for f{i-1} is below the new row, so no point extends, and each f{i} was
    // decided whole, 56.9 times slower at 400 links than at 50 (LOAD-chain-move). Each is now
    // decided from the integer hull of its rows (design B, META3 H2), the part's hull with one
    // row added, at most 4 sides at every link (design D11), and each answer is still the one
    // the whole has. The base rows are `x >= y + 1, y >= 0`.
    let mut e = Extending::new();
    for (i, f) in a_moving_chain(40).iter().enumerate() {
        counts::take();
        let got = e.answers(f);
        let c = counts::take();
        assert_eq!(got, decided(f), "{f}");
        assert_eq!(
            c[counts::PLANE],
            1,
            "link {}: decided from its region",
            i + 1
        );
        assert!(
            c[counts::PLANE_ROWS] <= 4,
            "link {}: {} sides",
            i + 1,
            c[counts::PLANE_ROWS]
        );
        assert_eq!(c[counts::HULL_UPDATES], 1, "link {}: one row added", i + 1);
        // The base, not in the list, is decided in link 1's call and seeds the hull once.
        let fresh = u64::from(i == 0);
        assert_eq!(
            c[counts::PLANE_FRESH],
            fresh,
            "link {}: no hull rebuilt",
            i + 1
        );
        assert_eq!(c[counts::WHOLE], 0, "link {}: nothing decided whole", i + 1);
    }
}

#[test]
fn a_tangent_chain_keeps_every_row() {
    // Every row of the tangent chain bounds its region, so the integer hull at link n has
    // n + 3 sides: `y >= 0`, `y >= x`, the n - 1 chords `y >= (2k + 1) x - k (k + 1)`, the
    // last tangent and `x <= 1000000` (design D11). Each link adds its one row to the part's
    // hull and asks nothing of the solver (META3 H2).
    let mut e = Extending::new();
    for (i, f) in a_tangent_chain(30).iter().enumerate() {
        counts::take();
        let got = e.answers(f);
        let c = counts::take();
        assert_eq!(got, decided(f), "{f}");
        assert_eq!(c[counts::HULL_UPDATES], 1, "link {}: one row added", i + 1);
        assert_eq!(c[counts::PLANE], 1, "link {}: decided from its hull", i + 1);
        assert_eq!(c[counts::PLANE_ROWS], i as u64 + 4, "link {}", i + 1);
        assert_eq!(c[counts::WHOLE], 0, "link {}: nothing decided whole", i + 1);
    }
}

#[test]
fn a_translated_quadrant_keeps_its_rays() {
    // META3 H1, Codex B1: the quadrant `x >= 0, y >= 0` cut by `x >= 5` keeps one vertex,
    // (5, 0), and two rays, so it is not a Point; a hull read as the Point (5, 0) answers the
    // next links (`y >= 1`, the point (5, 1)) empty. Each link is answered from the hull
    // (`counts::PLANE`) and each answer is the one the whole has, both polarities.
    let (x, y, k) = (sym("x"), sym("y"), Lin::constant);
    let quadrant = Formula::and(vec![ge(x.clone(), k(0)), ge(y.clone(), k(0))]);
    let moved = extend(&quadrant, vec![ge(x.clone(), k(5))]);
    let links = [
        extend(&moved, vec![ge(y.clone(), k(1))]),
        extend(&moved, vec![ge(k(5), x.clone())]),
        extend(
            &extend(&moved, vec![ge(k(5), x.clone())]),
            vec![ge(k(3), y.clone())],
        ),
        extend(&moved, vec![ge(k(4), x.clone())]),
        extend(&moved, vec![ge(k(4), x.clone().plus(&y.clone()))]),
    ];
    let mut e = Extending::new();
    assert_eq!(e.answers(&moved), decided(&moved), "{moved}");
    for f in &links {
        counts::take();
        let got = e.answers(f);
        let c = counts::take();
        assert_eq!(got, decided(f), "{f}");
        assert!(c[counts::PLANE] >= 1, "{f}: decided from its hull");
        assert_eq!(c[counts::WHOLE], 0, "{f}: nothing decided whole");
    }
}

#[test]
fn each_region_over_two_symbols_is_decided_as_its_rows() {
    // LOAD-chain-move, META1 A1/A2 corner cases: each answer is the one `decide` gives the
    // whole, at every link, where the region is decided from its kept rows and where it
    // is not (a row `==`, an `Aux`, a region with no interior).
    let (x, y, k) = (sym("x"), sym("y"), Lin::constant);
    let b = |lo: i64, hi: i64| {
        Formula::and(vec![
            ge(x.clone(), k(lo)),
            ge(k(hi), x.clone()),
            ge(y.clone(), k(lo)),
            ge(k(hi), y.clone()),
        ])
    };
    let lin = |a: i64, c: i64| x.times(a).plus(&y.times(c));
    let q = Lin::atom(Atom::Aux(0));
    let eq = |a: Lin, c: Lin| Formula::Con(Con::eq(&a, &c));
    let quadrant = Formula::and(vec![ge(x.clone(), k(0)), ge(y.clone(), k(0))]);
    let chains: Vec<(&str, Formula, Vec<Vec<Formula>>)> = vec![
        // The triangle (0,0), (2,0), (0,2): three lattice lines meet it (META1 error 4).
        (
            "triangle",
            quadrant.clone(),
            vec![vec![ge(k(2), lin(1, 1))], vec![ge(lin(1, 1), k(1))]],
        ),
        // 2x + 2y >= 1 on [0,3]²: no integer point on the row (META1 error 3).
        (
            "2x+2y",
            b(0, 3),
            vec![vec![ge(lin(2, 2), k(1))], vec![ge(k(1), lin(2, 2))]],
        ),
        // 3x + 5y >= 7 on [0,2]².
        (
            "3x+5y",
            b(0, 2),
            vec![vec![ge(lin(3, 5), k(7))], vec![ge(k(8), lin(3, 5))]],
        ),
        // A cut that empties the region, one that keeps every row, one that keeps one.
        ("empties", b(0, 3), vec![vec![ge(x.clone(), k(10))]]),
        ("keeps all", b(0, 3), vec![vec![ge(lin(1, 1), k(1))]]),
        (
            "keeps one",
            quadrant.clone(),
            vec![vec![ge(x.clone(), k(5))], vec![ge(x.clone(), k(7))]],
        ),
        // An unbounded region.
        (
            "unbounded",
            Formula::and(vec![ge(x.clone(), y.clone()), ge(y.clone(), k(-4))]),
            vec![vec![ge(y.clone(), k(3))], vec![ge(lin(1, -2), k(-50))]],
        ),
        // A row `==`, and a row over an `Aux` such as `x mod 3`'s quotient: decided whole.
        (
            "eq",
            b(0, 9),
            vec![vec![eq(x.clone(), y.times(2))], vec![ge(x.clone(), k(3))]],
        ),
        (
            "aux",
            b(0, 9),
            vec![vec![ge(x.clone(), q.times(3))], vec![ge(x.clone(), k(3))]],
        ),
        // A row of no atom, false, and a third atom.
        ("constant", b(0, 9), vec![vec![ge(k(0), k(1))]]),
        ("third", b(0, 9), vec![vec![ge(sym("z"), x.clone())]]),
    ];
    for (name, base, links) in chains {
        let mut e = Extending::new();
        let mut f = base;
        assert_eq!(e.answers(&f), decided(&f), "{name}: {f}");
        for rows in links {
            f = extend(&f, rows);
            assert_eq!(e.answers(&f), decided(&f), "{name}: {f}");
        }
    }
    // One conjunction extended by two callers, each with its own region.
    let mut e = Extending::new();
    let f1 = extend(&quadrant, vec![ge(x.clone(), k(5))]);
    let f2 = extend(&quadrant, vec![ge(k(-1), y.clone())]);
    let f3 = extend(&f1, vec![ge(k(4), x.clone())]);
    for f in [&quadrant, &f1, &f2, &f3, &f1] {
        assert_eq!(e.answers(f), decided(f), "{f}");
    }
}

#[test]
fn the_step_controls_of_the_integer_hull_are_answered_as_their_rows() {
    // LOAD-chain-move-tangent, META1 D12 and D13 of XR-load-call-node: the controls of the steps
    // of design B (/home/luke/Work/wt/design-b22-load5.md), each link's answer checked against
    // `decide` of the whole. They pass on design A, which decides each link from its rows over
    // Z; design B must keep them passing, and each names the step whose mutant it catches.
    let (x, y, k) = (sym("x"), sym("y"), Lin::constant);
    let and = Formula::and;
    let box_ = |x0: i64, x1: i64, y0: i64, y1: i64| {
        and(vec![
            ge(x.clone(), k(x0)),
            ge(k(x1), x.clone()),
            ge(y.clone(), k(y0)),
            ge(k(y1), y.clone()),
        ])
    };
    let lin = |a: i64, c: i64| x.times(a).plus(&y.times(c));
    let quadrant = and(vec![ge(x.clone(), k(0)), ge(y.clone(), k(0))]);
    // `l` times 10^40, past i128.
    let wide = |l: &Lin| {
        l.times(1_000_000_000_000_000_000i64)
            .times(1_000_000_000_000_000_000i64)
            .times(10_000)
    };
    let chains: Vec<(&str, Formula, Vec<Vec<Formula>>)> = vec![
        // Step 1 (D12): `1 <= 2x - 2y <= 1` has rational points and no integer point; the
        // tightening alone finds it.
        (
            "step 1: 2x - 2y = 1",
            box_(0, 9, 0, 9),
            vec![vec![ge(lin(2, -2), k(1))], vec![ge(k(1), lin(2, -2))]],
        ),
        // Step 1 (D1): a negative constant, 2x + 4y - 3 >= 0 is x + 2y >= floor(3/2) + 1 = 2
        // and not x + 2y >= 1 as truncation gives, so beside x + 2y <= 1 it is empty.
        (
            "step 1: floor of a negative constant",
            box_(-5, 5, -5, 5),
            vec![vec![ge(lin(2, 4), k(3))], vec![ge(k(1), lin(1, 2))]],
        ),
        // Constant rows (D1, D13): true, zero, false.
        (
            "constant rows",
            box_(0, 3, 0, 3),
            vec![
                vec![ge(k(1), k(0))],
                vec![ge(k(0), k(0))],
                vec![ge(k(0), k(1))],
            ],
        ),
        // Step 5 (D12), Gemini: 2x - y <= 1, 2x + y >= 1, y <= 0 meet in (1/2, 0) alone.
        (
            "step 5: Gemini",
            and(vec![ge(k(1), lin(2, -1)), ge(lin(2, 1), k(1))]),
            vec![vec![ge(k(0), y.clone())]],
        ),
        // Step 5 (D12), Claude: 3x + 2y <= -4, 3y >= x - 1, y <= 3x + 4.
        (
            "step 5: Claude",
            and(vec![ge(k(-4), lin(3, 2)), ge(lin(-1, 3), k(-1))]),
            vec![vec![ge(lin(3, -1), k(-4))]],
        ),
        // The corner repair (D12), Codex: the triangle (0,0), (0,1), (2,0) cut by x >= 1 is the
        // segment [(1,0), (2,0)] (a Line), then 3y >= x leaves it empty (META2 G10, Gemini
        // Q6.1). Without the repair the hull keeps (1, 1/2), where 3y >= x holds, and answers
        // that it holds (prototype proto-r3/hull.rs, mutant NoCuts; the last link before,
        // y >= 1, is empty over Q as well, so it could not tell).
        (
            "corner repair",
            and(vec![
                ge(x.clone(), k(0)),
                ge(y.clone(), k(0)),
                ge(k(2), lin(1, 2)),
            ]),
            vec![vec![ge(x.clone(), k(1))], vec![ge(lin(-1, 3), k(0))]],
        ),
        // Case 1 with C redundant (D13): [0,1]×[0,2] and 3x + y <= 2.
        (
            "case 1, C redundant",
            box_(0, 1, 0, 2),
            vec![vec![ge(k(2), lin(3, 1))], vec![ge(x.clone(), k(1))]],
        ),
        // Case 2 with C' redundant (D13): 0 <= y <= 1 and 3x - y <= 1, then 2x >= 1, which has
        // rational points (x in [1/2, 2/3] at y = 1) and no integer point.
        (
            "case 2, C' redundant",
            and(vec![ge(y.clone(), k(0)), ge(k(1), y.clone())]),
            vec![vec![ge(k(1), lin(3, -1))], vec![ge(lin(2, 0), k(1))]],
        ),
        // Codex's case-2 triangle (D5): (-2,0), (-2,1), (1,2) cut by x <= 0, whose section on
        // x = 0 holds y in [4/3, 5/3] and no integer: case 1 there gives a fractional vertex.
        // The hull is then (-2,0), (-2,1), (-1,1), and x + y >= 1 leaves it empty (META2 G10,
        // Gemini Q6.1); a hull that skipped step 5 keeps (-1/2, 3/2), where x + y = 1, and
        // answers that it holds (prototype proto-r3/hull.rs, mutant NoCuts). The link before,
        // x >= 0, is empty over Q on that hull as well, so it could not tell.
        (
            "case 2 triangle",
            and(vec![
                ge(x.clone(), k(-2)),
                ge(lin(-2, 3), k(4)),
                ge(lin(1, -3), k(-5)),
            ]),
            vec![vec![ge(k(0), x.clone())], vec![ge(lin(1, 1), k(1))]],
        ),
        // Unbounded (D3): every vertex cut off and not empty; no vertex cut off and not implied.
        (
            "quadrant, x >= 5",
            quadrant.clone(),
            vec![vec![ge(x.clone(), k(5))]],
        ),
        (
            "quadrant, x <= 5",
            quadrant.clone(),
            vec![vec![ge(k(5), x.clone())]],
        ),
        // Ties (D2): rows through a vertex, min f = c (implied, twice), then max f = c (the
        // point (0,0)).
        (
            "ties",
            box_(0, 3, 0, 3),
            vec![
                vec![ge(lin(1, 1), k(0))],
                vec![ge(k(6), lin(1, 1))],
                vec![ge(k(0), lin(1, 1))],
            ],
        ),
        // Ties (Gemini N1): a row through two vertices with min f < c < max f elsewhere, and a
        // quadrant cut to its ray x = 0.
        (
            "ties: x + y >= 1 on the unit square",
            box_(0, 1, 0, 1),
            vec![vec![ge(lin(1, 1), k(1))]],
        ),
        (
            "quadrant, x <= 0",
            quadrant.clone(),
            vec![vec![ge(k(0), x.clone())]],
        ),
        // The states of D4: a half-plane, a strip, a ray, a segment, a point, empty.
        (
            "states",
            and(vec![ge(lin(1, 2), k(0)), ge(lin(1, 2), k(-5))]),
            vec![
                vec![ge(k(3), lin(1, 2))],
                vec![ge(lin(1, 2), k(3))],
                vec![ge(x.clone(), k(1))],
                vec![ge(k(7), x.clone())],
                vec![ge(k(1), x.clone())],
                vec![ge(y.clone(), k(2))],
            ],
        ),
        // A long continued fraction (D13): consecutive Fibonacci coefficients.
        (
            "Fibonacci",
            box_(-1000, 1000, -1000, 1000),
            vec![
                vec![ge(lin(89, 144), k(1000))],
                vec![ge(k(1003), lin(89, 144))],
                vec![ge(lin(-55, 89), k(1))],
                vec![ge(k(2), lin(-55, 89))],
            ],
        ),
        // Coefficients past i128 (D13): 10^40 x + (10^40 + 1) y in [1, 10^40].
        (
            "past i128",
            box_(-9, 9, -9, 9),
            vec![
                vec![ge(wide(&lin(1, 1)).plus(&y), k(1))],
                vec![ge(wide(&k(1)), wide(&lin(1, 1)).plus(&y))],
            ],
        ),
    ];
    for (name, base, links) in chains {
        let mut e = Extending::new();
        let mut f = base;
        assert_eq!(e.answers(&f), decided(&f), "{name}: {f}");
        for rows in links {
            f = extend(&f, rows);
            assert_eq!(e.answers(&f), decided(&f), "{name}: {f}");
        }
    }
    // Persistence (D13, META2 G10): three callers extend one region, the base never asked
    // itself, so no answer of it is remembered. Each extension holds and they are pairwise
    // disjoint, so a hull the first one cut in place (x <= 2) would make the next two (3 <= x
    // <= 4, x >= 5) answer empty; each is compared with the whole decided, and at least two
    // of them must be decided from the region (`counts::PLANE`), so that the hull is the one
    // read. Then the first again and the base.
    let base = extend(&box_(0, 6, 0, 6), vec![ge(k(9), lin(1, 1))]);
    let mut e = Extending::new();
    let left = extend(&base, vec![ge(k(2), x.clone())]);
    let mid = extend(&base, vec![ge(x.clone(), k(3)), ge(k(4), x.clone())]);
    let right = extend(&base, vec![ge(x.clone(), k(5))]);
    counts::take();
    for f in [&left, &mid, &right] {
        let got = e.answers(f);
        assert_eq!(got, decided(f), "{f}");
        assert_eq!(got.holds, Ok(true), "each caller's region holds: {f}");
    }
    let c = counts::take();
    assert!(
        c[counts::PLANE] >= 2,
        "{} of the three callers decided from the region",
        c[counts::PLANE]
    );
    for f in [&left, &base] {
        assert_eq!(e.answers(f), decided(f), "{f}");
    }
}

/// A chain of `n` calls as the scope reads it (LOAD-extend-refuses): `x{i} == x{i+1} + k`, the
/// argument of call i bound to its callee's atom, written from the last link back so that the
/// bindings resolve through long paths; `b{i} == i`, a binding's own variable; and at each link
/// the callee's `x{i} mod 3`, a division over the callee's atom, with a disjunction over its
/// remainder. With `k` 0 every division divides the same term.
pub(super) fn bound_chain(n: usize, k: i64) -> Formula {
    let x = |i: usize| sym(&format!("x{i}"));
    let eq = |a: Lin, b: Lin| Formula::Con(Con::eq(&a, &b));
    let mut fs = Vec::new();
    for i in (0..n).rev() {
        fs.push(eq(x(i), x(i + 1).plus(&Lin::constant(k))));
        fs.push(eq(sym(&format!("b{i}")), Lin::constant(i as i64)));
    }
    for i in 0..=n {
        let (q, r) = (sym(&format!("q{i}")), sym(&format!("r{i}")));
        fs.push(eq(x(i), q.times(3).plus(&r)));
        fs.push(ge(r.clone(), Lin::constant(0)));
        fs.push(ge(Lin::constant(2), r.clone()));
        fs.push(Formula::or(vec![
            eq(r.clone(), Lin::constant(1)),
            ge(x(i), Lin::constant(10 * i as i64)),
        ]));
    }
    Formula::and(fs)
}

#[test]
fn bindings_put_in_place_leave_one_atom_and_one_division() {
    // LOAD-extend-refuses: a whole question the solver refuses is asked again with its
    // bindings in place. Over a chain they leave one of the x atoms and no binding variable,
    // the divisions of one term merge into one, and the formula with them in place has the
    // answer of the formula.
    use zedc::store::presburger::extend::with_bindings_in_place;
    for k in [0, 2] {
        let f = bound_chain(6, k);
        let g = with_bindings_in_place(&f).expect("bindings");
        let atoms = g.atoms();
        let xs = atoms
            .iter()
            .filter(|a| format!("{a:?}").contains("\"x"))
            .count();
        let bs = atoms
            .iter()
            .filter(|a| format!("{a:?}").contains("\"b"))
            .count();
        let rs = atoms
            .iter()
            .filter(|a| format!("{a:?}").contains("\"r"))
            .count();
        assert_eq!((xs, bs), (1, 0), "{g}");
        // With k 0 each x is the same term, so the seven divisions are one; with k 2 the terms
        // differ by 2, so none merge.
        assert_eq!(rs, if k == 0 { 1 } else { 7 }, "{g}");
        assert_eq!(decide(&g), decide(&f), "{f}");
    }
}

/// A kept part whose face holds a clause over a quotient that clause alone reads, and a
/// constraint beside the part over that quotient (SOUND-extend-face-local-atoms). The part is
/// `q(x) = (x mod 2 != 1 || x mod 4 == 1) && x >= 2 && x <= 9` over the pairs `x == 2 * q0 +
/// q1` and `x == 4 * q2 + q3`, whose face keeps the clause `x == 4 * q2 + 1 || x == 2 * q0`;
/// the whole is `q && x >= 9 && q0 <= 2`, which holds nowhere: `x` is 9 and `9 div 2` is 4.
/// The face's `q0` is bound inside its clause (the clause holds by its first disjunct at
/// `x = 9`, whatever `q0` is), so it is not read beside the face, and the answer is the one
/// the whole has with its definitions. Before the fix the face counted `q0` as one of its
/// atoms, and the point `x = 9, q0 = 0` of the faces answered `true`.
#[test]
fn an_atom_a_face_clause_alone_reads_is_not_read_beside_it() {
    let x = sym("x");
    let q = |n: u32| Lin::atom(Atom::Aux(n));
    let k = Lin::constant;
    let eq = |a: Lin, b: Lin| Formula::Con(Con::eq(&a, &b));
    let pair = |m: i64, n: u32| {
        Formula::and(vec![
            eq(x.clone(), q(n).times(m).plus(&q(n + 1))),
            ge(q(n + 1), k(0)),
            ge(k(m - 1), q(n + 1)),
        ])
    };
    let defs = [pair(2, 0), pair(4, 2)];
    let def = |n: u32| defs[n as usize / 2].clone();
    let part = Formula::and(vec![
        Formula::or(vec![Formula::negate(eq(q(1), k(1))), eq(q(3), k(1))]),
        ge(x.clone(), k(2)),
        ge(k(9), x.clone()),
    ]);
    let whole = extend(&part, vec![ge(x.clone(), k(9)), ge(k(2), q(0))]);
    // Only the part is a call, and its caller reads `x`.
    let iface = |g: &Formula| matches!(g, Formula::And(_)).then(|| vec![Atom::Sym("x".into())]);
    let with_defs = |f: Formula| Formula::and(vec![defs[0].clone(), defs[1].clone(), f]);
    let want = Answers {
        holds: decide(&with_defs(whole.clone())),
        fails: decide(&with_defs(Formula::negate(whole.clone()))),
    };
    assert_eq!(
        (want.holds.clone(), want.fails.clone()),
        (Ok(false), Ok(true))
    );
    let mut e = Extending::new();
    // The part asked first, as a unit asks its callee before its caller, and the whole after.
    e.defined_with(&part, &def, &iface);
    assert_eq!(e.defined_with(&whole, &def, &iface), want, "{whole}");
    // The control: `x div 4 <= 2` beside the part, which holds at `x = 9`, so the fix does not
    // turn a true answer false.
    let control = extend(&part, vec![ge(x.clone(), k(9)), ge(k(2), q(2))]);
    let want = Answers {
        holds: decide(&with_defs(control.clone())),
        fails: decide(&with_defs(Formula::negate(control.clone()))),
    };
    assert_eq!(want.holds, Ok(true));
    assert_eq!(e.defined_with(&control, &def, &iface), want, "{control}");
}

/// The pair `x == m * q{n} + q{n+1}`, `0 <= q{n+1} <= m - 1`.
fn division_pair(m: i64, n: u32) -> Formula {
    let q = |n: u32| Lin::atom(Atom::Aux(n));
    Formula::and(vec![
        Formula::Con(Con::eq(&sym("x"), &q(n).times(m).plus(&q(n + 1)))),
        ge(q(n + 1), Lin::constant(0)),
        ge(Lin::constant(m - 1), q(n + 1)),
    ])
}

/// Asks each of `links` in turn of one `Extending`, the caller reading `x` of each kept part,
/// and checks each answer against the one `decide` gives the link with `defs`; returns those
/// answers.
fn links_answer_as_the_whole(defs: &[Formula], links: &[Formula]) -> Vec<Answers> {
    let def = |n: u32| defs[n as usize / 2].clone();
    let iface = |g: &Formula| matches!(g, Formula::And(_)).then(|| vec![Atom::Sym("x".into())]);
    let with_defs = |f: Formula| Formula::and(defs.iter().cloned().chain([f]).collect());
    let mut e = Extending::new();
    let mut out = Vec::new();
    for f in links {
        let want = Answers {
            holds: decide(&with_defs(f.clone())),
            fails: decide(&with_defs(Formula::negate(f.clone()))),
        };
        assert_eq!(e.defined_with(f, &def, &iface), want, "{f}");
        out.push(want);
    }
    out
}

/// XR-sound-extend-face-local-atoms round 1, L1: a quotient two disjunctions of one disjunct
/// share is kept inside that disjunct (`split`), while the other disjunct holds whatever its
/// value is. Over `x == 3 * q0 + q1`: `D1 = x >= 0 && (q1 == 0 || x <= -1) && (q1 == 1 || x >=
/// 51)`, `D2 = q0 >= 0 && q1 == 2`, the part `(D1 || D2) && 2 <= x <= 9`, which holds at
/// x in {2, 5, 8} by `D2` alone, and the whole `part && q1 == 0`, which holds nowhere. With
/// `D1` and `D2` in both orders.
#[test]
fn a_quotient_kept_inside_one_disjunct_is_not_read_beside_the_face() {
    let (x, q, k) = (sym("x"), |n: u32| Lin::atom(Atom::Aux(n)), Lin::constant);
    let eq = |a: Lin, b: Lin| Formula::Con(Con::eq(&a, &b));
    let d1 = Formula::and(vec![
        ge(x.clone(), k(0)),
        Formula::or(vec![eq(q(1), k(0)), ge(k(-1), x.clone())]),
        Formula::or(vec![eq(q(1), k(1)), ge(x.clone(), k(51))]),
    ]);
    let d2 = Formula::and(vec![ge(q(0), k(0)), eq(q(1), k(2))]);
    for ds in [vec![d1.clone(), d2.clone()], vec![d2, d1]] {
        let part = Formula::and(vec![
            Formula::or(ds),
            ge(x.clone(), k(2)),
            ge(k(9), x.clone()),
        ]);
        let whole = extend(&part, vec![eq(q(1), k(0))]);
        let got = links_answer_as_the_whole(&[division_pair(3, 0)], &[part, whole]);
        assert_eq!(
            (got[1].holds.clone(), got[1].fails.clone()),
            (Ok(false), Ok(true))
        );
    }
}

/// XR-sound-extend-face-local-atoms round 1, L2: the point a link stores, found through its
/// part's face, may give the quotient the face's clause alone reads a value its definition does
/// not give at that point, and the next link reads that point. Over `x == 2 * q0 + q1` and `x ==
/// 4 * q2 + q3`, `q = (q1 != 1 || q3 == 1) && 2 <= x <= 9`, `p1 = q && x >= 9` (x = 9),
/// `p2 = p1 && q0 <= 2`, which holds nowhere since `9 div 2` is 4; and the mirror, `q` over
/// `9 <= x <= 17`, `p1 = q && x <= 9`, so that either end the solver picks is met.
#[test]
fn a_point_stored_through_a_face_is_not_read_at_a_quotient_the_face_projects_out() {
    let (x, q, k) = (sym("x"), |n: u32| Lin::atom(Atom::Aux(n)), Lin::constant);
    let eq = |a: Lin, b: Lin| Formula::Con(Con::eq(&a, &b));
    let defs = [division_pair(2, 0), division_pair(4, 2)];
    for (lo, hi, link) in [(2, 9, ge(x.clone(), k(9))), (9, 17, ge(k(9), x.clone()))] {
        let part = Formula::and(vec![
            Formula::or(vec![Formula::negate(eq(q(1), k(1))), eq(q(3), k(1))]),
            ge(x.clone(), k(lo)),
            ge(k(hi), x.clone()),
        ]);
        let p1 = extend(&part, vec![link]);
        let p2 = extend(&p1, vec![ge(k(2), q(0))]);
        let got = links_answer_as_the_whole(&defs, &[part, p1, p2]);
        assert_eq!(
            (got[2].holds.clone(), got[2].fails.clone()),
            (Ok(false), Ok(true))
        );
    }
}
