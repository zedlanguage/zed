//! The projection of a part by its pendants (`Scope::project_by_pendants`, item ST-eqs-cubic)
//! checked against an exact computation by brute force, on the parts the projection of the
//! whole part refused (Growth, Tie) in 3000 random programs, against the projection of the
//! whole part on random parts where neither refuses, and on a program where the answer
//! changed.

use std::collections::{BTreeMap, HashSet};
use std::sync::Arc;

use zed_kernel::Prim;
use zed_kernel::Term;
use zed_kernel::term::build::{lit, prim, var};
use zed_tests::instances::Rng;
use zedc::store::cell::Premises;
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::presburger::{self, Atom, Con, Formula, Lin, Shared};
use zedc::store::product::Scope;

use super::ints;

/// `Σ coefficient · name + constant`, with `>= 0`, or `== 0` when `eq`.
#[derive(Clone, Debug, PartialEq)]
struct Cmp {
    terms: BTreeMap<String, i64>,
    constant: i64,
    eq: bool,
}

/// A top-level conjunct of a part: a constraint, or a disjunction of conjunctions of them.
#[derive(Clone, Debug)]
enum Item {
    Con(Cmp),
    Or(Vec<Vec<Cmp>>),
    /// `!(t == 0)`, the formula's negation of the equation, `t - 1 >= 0 || -t - 1 >= 0`.
    Ne(Cmp),
}

/// `text`, terms such as `2 * a`, `b`, `6` joined by ` + ` and ` - `, as a sum.
fn sum(text: &str) -> (BTreeMap<String, i64>, i64) {
    let toks: Vec<&str> = text.split(' ').collect();
    let mut terms = BTreeMap::new();
    let mut constant = 0;
    let mut sign = 1;
    let mut i = 0;
    while i < toks.len() {
        match toks[i] {
            "+" => sign = 1,
            "-" => sign = -1,
            t => {
                match t.parse::<i64>() {
                    Ok(v) if toks.get(i + 1) == Some(&"*") => {
                        *terms.entry(toks[i + 2].to_string()).or_insert(0) += sign * v;
                        i += 2;
                    }
                    Ok(v) => constant += sign * v,
                    Err(_) => {
                        let (s, n) = t.strip_prefix('-').map_or((1, t), |n| (-1, n));
                        *terms.entry(n.to_string()).or_insert(0) += sign * s;
                    }
                }
                sign = 1;
            }
        }
        i += 1;
    }
    (terms, constant)
}

/// `left - right`, as a sum.
fn minus(left: &str, right: &str) -> (BTreeMap<String, i64>, i64) {
    let (mut t, c) = sum(left);
    let (u, d) = sum(right);
    for (n, k) in u {
        *t.entry(n).or_insert(0) -= k;
    }
    t.retain(|_, k| *k != 0);
    (t, c - d)
}

/// A comparison `l <= r`, `l >= r` or `l == r`, or its negation when `negated`, as a
/// disjunction of constraints.
fn compare(text: &str, negated: bool) -> Vec<Cmp> {
    let (op, at) = [" <= ", " >= ", " == "]
        .iter()
        .find_map(|op| text.find(op).map(|i| (*op, i)))
        .expect("a comparison");
    let (l, r) = (&text[..at], &text[at + op.len()..]);
    let ((terms, constant), eq) = match op {
        " >= " => (minus(l, r), false),
        " <= " => (minus(r, l), false),
        _ => (minus(l, r), true),
    };
    let neg = |terms: &BTreeMap<String, i64>| terms.iter().map(|(n, k)| (n.clone(), -k)).collect();
    match (negated, eq) {
        (false, eq) => vec![Cmp {
            terms,
            constant,
            eq,
        }],
        // !(t >= 0): -t - 1 >= 0.
        (true, false) => vec![Cmp {
            terms: neg(&terms),
            constant: -constant - 1,
            eq: false,
        }],
        // !(t == 0): t - 1 >= 0 or -t - 1 >= 0.
        (true, true) => vec![
            Cmp {
                terms: terms.clone(),
                constant: constant - 1,
                eq: false,
            },
            Cmp {
                terms: neg(&terms),
                constant: -constant - 1,
                eq: false,
            },
        ],
    }
}

/// The top-level conjuncts of a part as written: ` && ` between them, each a comparison,
/// `!(comparison)`, or `(c || c && c || ...)`.
fn parse(text: &str) -> Vec<Item> {
    let mut parts = Vec::new();
    let mut depth = 0;
    let mut start = 0;
    for (i, ch) in text.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            _ if depth == 0 && text[i..].starts_with(" && ") => {
                parts.push(&text[start..i]);
                start = i + 4;
            }
            _ => {}
        }
    }
    parts.push(&text[start..]);
    parts
        .into_iter()
        .map(|p| {
            if let Some(inner) = p.strip_prefix("!(") {
                let c = compare(
                    inner.strip_suffix(')').expect("a closing parenthesis"),
                    true,
                );
                if c.len() == 1 {
                    Item::Con(c[0].clone())
                } else {
                    Item::Ne(
                        compare(
                            inner.strip_suffix(')').expect("a closing parenthesis"),
                            false,
                        )
                        .remove(0),
                    )
                }
            } else if let Some(inner) = p.strip_prefix('(') {
                let inner = inner.strip_suffix(')').expect("a closing parenthesis");
                Item::Or(
                    inner
                        .split(" || ")
                        .map(|arm| {
                            arm.split(" && ")
                                .map(|c| compare(c, false).remove(0))
                                .collect()
                        })
                        .collect(),
                )
            } else {
                Item::Con(compare(p, false).remove(0))
            }
        })
        .collect()
}

fn con(c: &Cmp) -> Formula {
    let mut l = Lin::constant(c.constant);
    for (n, k) in &c.terms {
        l = l.plus(&Lin::atom(Atom::Sym(n.as_str().into())).times(*k));
    }
    let zero = Lin::constant(0);
    Formula::Con(if c.eq {
        Con::eq(&l, &zero)
    } else {
        Con::ge(&l, &zero)
    })
}

/// The part as a formula. An equation written twice is held twice in the scope, the second
/// time with the opposite sign (a formula holds one copy of a constraint), so here too.
fn formula(items: &[Item]) -> Formula {
    let mut seen = Vec::new();
    let mut parts = Vec::new();
    for i in items {
        parts.push(match i {
            Item::Con(c) if c.eq && seen.contains(c) => {
                let terms = c.terms.iter().map(|(n, k)| (n.clone(), -k)).collect();
                con(&Cmp {
                    terms,
                    constant: -c.constant,
                    eq: true,
                })
            }
            Item::Con(c) => {
                seen.push(c.clone());
                con(c)
            }
            Item::Ne(c) => Formula::Not(Shared::new(con(c))),
            Item::Or(arms) => Formula::or(
                arms.iter()
                    .map(|a| Formula::and(a.iter().map(con).collect()))
                    .collect(),
            ),
        });
    }
    Formula::and(parts)
}

/// `x` as written in the table, `[lo,hi lo,hi]`, `-inf` and `inf` for no bound.
fn show(x: &IntervalSet) -> String {
    let end = |e: &End| match e {
        End::NegInf => "-inf".to_string(),
        End::PosInf => "inf".to_string(),
        End::Fin(v) => format!("{v}"),
    };
    let ps: Vec<String> = x
        .pieces()
        .map(|(l, h)| format!("{},{}", end(l), end(h)))
        .collect();
    format!("[{}]", ps.join(" "))
}

/// `a=[1,5] z1=[-inf,8 10,inf]` as each name and the text within its brackets.
fn bracketed(text: &str) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    let mut rest = text;
    while let Some(open) = rest.find("=[") {
        let close = open + rest[open..].find(']').expect("a closing bracket");
        out.insert(
            rest[..open].trim().to_string(),
            rest[open + 2..close].to_string(),
        );
        rest = &rest[close + 1..];
    }
    out
}

/// One piece of a box: its bounds, `None` for none.
type Piece = (Option<i64>, Option<i64>);

/// The boxes as written, each name's pieces.
fn boxes(text: &str) -> BTreeMap<String, Vec<Piece>> {
    let end = |s: &str| match s {
        "-inf" | "inf" => None,
        v => Some(v.parse::<i64>().expect("a bound")),
    };
    bracketed(text)
        .into_iter()
        .map(|(n, inner)| {
            let pieces = inner
                .split(' ')
                .filter(|p| !p.is_empty())
                .map(|p| {
                    let (l, h) = p.split_once(',').expect("a piece");
                    (end(l), end(h))
                })
                .collect();
            (n, pieces)
        })
        .collect()
}

/// A scope whose names hold `boxes` exactly.
fn scope(boxes: &BTreeMap<String, Vec<Piece>>) -> Scope {
    let p = Premises::new();
    let names: Vec<Arc<str>> = boxes.keys().map(|n| Arc::from(n.as_str())).collect();
    let mut s = ints(&names);
    for (n, pieces) in boxes {
        if let Some(lo) = pieces[0].0 {
            s = s.assume(&prim(Prim::Ge, vec![var(n), lit(lo)]), true, &p);
        }
        if let Some(hi) = pieces[pieces.len() - 1].1 {
            s = s.assume(&prim(Prim::Le, vec![var(n), lit(hi)]), true, &p);
        }
        for w in pieces.windows(2) {
            for v in w[0].1.expect("a gap") + 1..w[1].0.expect("a gap") {
                s = s.assume(&prim(Prim::Ne, vec![var(n), lit(v)]), true, &p);
            }
        }
    }
    for (n, pieces) in boxes {
        let f = |e: &Option<i64>, inf: &str| e.map_or(inf.to_string(), |v| v.to_string());
        let want: Vec<String> = pieces
            .iter()
            .map(|(l, h)| format!("{},{}", f(l, "-inf"), f(h, "inf")))
            .collect();
        assert_eq!(
            show(s.get(n).ints()),
            format!("[{}]", want.join(" ")),
            "the box of {n}"
        );
    }
    s
}

/// What [`points`] finds within one range of the hubs: the hull of each name and the exact set
/// of its values (for a `z` its hull again unless asked for), or `None` where there is no point.
type Found = Option<BTreeMap<String, (IntervalSet, IntervalSet)>>;

/// Over the integer points of `cons` within `boxes` (one piece each), what [`Found`] holds,
/// with the hubs (the names other than `z1`, `z2`, ...) enumerated within their boxes and
/// `-near..=near`, then within `-far..=far` (`near <= far`). Each `z` is mentioned with
/// coefficient one or minus one, at most two to a constraint and then with opposite signs,
/// so for the hubs' values the `z` constraints are integer difference constraints, which
/// shortest paths from a source solve exactly: each `z` takes every integer from minus its
/// distance to the source to its distance from it. An unbounded end is `End::NegInf` or
/// `End::PosInf`.
///
/// One pass over the wider range serves both, a point counted for the narrower one where
/// each hub lies within it, and each `z` keeps the least and greatest end it took, its exact
/// set of values only with `exact`. Two passes, and a set of the ranges of each `z` added to
/// at every point, took 15 s over the 24 rows of [`REFUSED`] (TEST-bench-move-l0139). It is
/// still `O(far^hubs · z^3)`, as a brute force is.
fn points(
    cons: &[Cmp],
    boxes: &BTreeMap<String, Piece>,
    (near, far): (i64, i64),
    exact: bool,
) -> [Found; 2] {
    const INF: i64 = i64::MAX / 4;
    let hubs: Vec<&String> = boxes.keys().filter(|n| !n.starts_with('z')).collect();
    let zs: Vec<&String> = boxes.keys().filter(|n| n.starts_with('z')).collect();
    let src = zs.len();
    let size = zs.len() + 1;
    let coefficients = |c: &Cmp| -> Vec<i64> {
        hubs.iter()
            .map(|h| *c.terms.get(*h).unwrap_or(&0))
            .collect()
    };
    // The constraints on the hubs alone: their coefficients, constant, whether an equation.
    let on_hubs: Vec<(Vec<i64>, i64, bool)> = cons
        .iter()
        .filter(|c| !c.terms.keys().any(|n| n.starts_with('z')))
        .map(|c| (coefficients(c), c.constant, c.eq))
        .collect();
    // The others: hub coefficients, the `z` of sign one and of sign minus one (the source
    // where there is none), constant, whether an equation.
    let on_zs: Vec<(Vec<i64>, usize, usize, i64, bool)> = cons
        .iter()
        .filter(|c| c.terms.keys().any(|n| n.starts_with('z')))
        .map(|c| {
            let z: Vec<(usize, i64)> = c
                .terms
                .iter()
                .filter_map(|(n, k)| zs.iter().position(|z| *z == n).map(|i| (i, *k)))
                .collect();
            assert!(
                z.iter().all(|(_, k)| k.abs() == 1)
                    && (z.len() < 2 || (z.len() == 2 && z[0].1 == -z[1].1)),
                "a difference constraint over the z: {c:?}"
            );
            let at = |s| z.iter().find(|(_, k)| *k == s).map_or(src, |(i, _)| *i);
            (coefficients(c), at(1), at(-1), c.constant, c.eq)
        })
        .collect();
    let ranges: Vec<(i64, i64)> = hubs
        .iter()
        .map(|h| {
            let (lo, hi) = boxes[*h];
            (
                lo.map_or(-far, |l| l.max(-far)),
                hi.map_or(far, |h| h.min(far)),
            )
        })
        .collect();
    let total: i64 = ranges.iter().map(|(l, h)| (h - l + 1).max(0)).product();
    let fin = |x: i64, inf: End| {
        if x.abs() >= INF {
            inf
        } else {
            End::Fin(Num::from(x))
        }
    };
    // Each hub value taken, by its place in the hub's range, for each range; and the
    // distinct ranges each `z` takes, for each range, joined once at the end: joining sets
    // at each of the up to 151^3 points took 35 s on one row (TEST-split-slow).
    let mut hub_seen: [Vec<Vec<bool>>; 2] = std::array::from_fn(|_| {
        ranges
            .iter()
            .map(|(l, h)| vec![false; (h - l + 1).max(0) as usize])
            .collect()
    });
    let mut z_hull: [Vec<Option<(i64, i64)>>; 2] = [vec![None; zs.len()], vec![None; zs.len()]];
    let mut z_seen: [Vec<HashSet<(i64, i64)>>; 2] =
        std::array::from_fn(|_| vec![HashSet::new(); zs.len()]);
    let mut v = vec![0i64; hubs.len()];
    let mut d = vec![vec![INF; size]; size];
    let at_hubs =
        |hub: &[i64], c: i64, v: &[i64]| c + hub.iter().zip(v).map(|(k, x)| k * x).sum::<i64>();
    for at in 0..total {
        let mut idx = at;
        for (i, (l, h)) in ranges.iter().enumerate() {
            v[i] = l + idx % (h - l + 1);
            idx /= h - l + 1;
        }
        let holds = |(hub, c, eq): &(Vec<i64>, i64, bool)| {
            let c0 = at_hubs(hub, *c, &v);
            if *eq { c0 == 0 } else { c0 >= 0 }
        };
        if !on_hubs.iter().all(holds) {
            continue;
        }
        for (i, row) in d.iter_mut().enumerate() {
            row.fill(INF);
            row[i] = 0;
        }
        let mut edge = |from: usize, to: usize, w: i64| d[from][to] = d[from][to].min(w);
        for (hub, plus, minus, c, eq) in &on_zs {
            // `plus - minus + c0 >= 0` is `minus - plus <= c0`: an edge from `plus` to
            // `minus` of weight `c0`, and for an equation one back of weight `-c0`.
            let c0 = at_hubs(hub, *c, &v);
            edge(*plus, *minus, c0);
            if *eq {
                edge(*minus, *plus, -c0);
            }
        }
        for (i, z) in zs.iter().enumerate() {
            let (l, h) = boxes[*z];
            if let Some(l) = l {
                edge(i, src, -l);
            }
            if let Some(h) = h {
                edge(src, i, h);
            }
        }
        for k in 0..size {
            for i in 0..size {
                for j in 0..size {
                    if d[i][k] < INF && d[k][j] < INF && d[i][k] + d[k][j] < d[i][j] {
                        d[i][j] = d[i][k] + d[k][j];
                    }
                }
            }
        }
        if (0..size).any(|i| d[i][i] < 0) {
            continue;
        }
        let in_near = v.iter().all(|x| x.abs() <= near);
        for which in [0, 1].into_iter().filter(|&w| w == 1 || in_near) {
            for (i, (l, _)) in ranges.iter().enumerate() {
                hub_seen[which][i][(v[i] - l) as usize] = true;
            }
            for (i, h) in z_hull[which].iter_mut().enumerate() {
                let (lo, hi) = (-d[i][src], d[src][i]);
                *h = Some(h.map_or((lo, hi), |(l, u)| (l.min(lo), u.max(hi))));
                if exact {
                    z_seen[which][i].insert((lo, hi));
                }
            }
        }
    }
    // The union of the ranges, and its hull, which is the hull of the hulls taken one at a
    // time.
    let found = |which: usize| -> Found {
        let mut seen: Vec<Vec<(i64, i64)>> = (hub_seen[which].iter().zip(&ranges))
            .map(|(taken, (l, _))| {
                let at = taken.iter().enumerate().filter(|(_, t)| **t);
                at.map(|(j, _)| (l + j as i64, l + j as i64)).collect()
            })
            .collect();
        seen.extend(z_seen[which].iter().zip(&z_hull[which]).map(|(s, h)| {
            let mut s: Vec<(i64, i64)> = if exact {
                s.iter().copied().collect()
            } else {
                h.iter().copied().collect()
            };
            s.sort_unstable();
            s
        }));
        if seen.iter().all(Vec::is_empty) {
            return None;
        }
        let out = seen.iter().map(|s| {
            let exact = s.iter().fold(IntervalSet::empty(), |e, (l, h)| {
                e.join(&IntervalSet::range(
                    fin(*l, End::NegInf),
                    fin(*h, End::PosInf),
                ))
            });
            (exact.hull(), exact)
        });
        Some(
            hubs.iter()
                .chain(zs.iter())
                .map(|n| (*n).clone())
                .zip(out)
                .collect(),
        )
    };
    [found(0), found(1)]
}

/// `x`, found with the hubs enumerated within a range, with each outer end opened where it
/// differs from that of `y`, found within a wider one: an end that moves with the range is
/// no end.
fn widened(x: &IntervalSet, y: &IntervalSet) -> IntervalSet {
    let (Some(first), Some(last)) = (x.first(), x.last()) else {
        return x.clone();
    };
    let same = |e: &End, f: Option<&End>| f == Some(e);
    let lo = if same(&first.0, y.first().map(|p| &p.0)) {
        first.0.clone()
    } else {
        End::NegInf
    };
    let hi = if same(&last.1, y.last().map(|p| &p.1)) {
        last.1.clone()
    } else {
        End::PosInf
    };
    x.join(&IntervalSet::range(lo, first.1.clone()))
        .join(&IntervalSet::range(last.0.clone(), hi))
}

/// The ranges `(near, far)` [`brute`] enumerates the hubs within on random parts.
const WIDE: (i64, i64) = (50, 75);

/// The ranges [`brute`] enumerates the hubs within on the rows of [`REFUSED`]. The widest
/// reach a row needs is that of row 18, whose `z4 <= -4` holds at `a = -22`, `b = -3`,
/// `c = 45` alone: `a + 2 * b + c <= 17` (from `z3 <= 9`), `a <= 3 * b - 13` and `b <= -3` give
/// `z4 = 2 * a + b + c - 2 <= a - b + 15 <= 2 * b + 2 <= -4`. Within -30..=30 or -40..=40 the
/// brute force reads that end as none. With [`WIDE`] the brute force took 12 s over the 24
/// rows, with these and only the hulls kept 4 s (TEST-bench-move-l0139).
const NARROW: (i64, i64) = (46, 56);

/// The exact projection of the part onto each name by brute force: in each disjunct (a
/// choice of an arm of each disjunction and of a piece of each box), the hull of the name's
/// values and the set of them, and over the disjuncts the union of each. The hubs are
/// enumerated within `-near..=near` and `-far..=far`, `reach` ([`WIDE`] or [`NARROW`]): an
/// outer end that differs between the two is no end, so every finite end of a name must be
/// reached with each hub within `-near..=near`. The set of a `z` is its hull unless `exact`.
fn brute(
    items: &[Item],
    bs: &BTreeMap<String, Vec<Piece>>,
    reach: (i64, i64),
    exact: bool,
) -> BTreeMap<String, (String, String)> {
    let mut terms: Vec<(Vec<Cmp>, BTreeMap<String, Piece>)> = vec![(Vec::new(), BTreeMap::new())];
    for i in items {
        let arms = match i {
            Item::Con(c) => vec![vec![c.clone()]],
            Item::Or(arms) => arms.clone(),
            Item::Ne(c) => compare_ne(c),
        };
        terms = terms
            .into_iter()
            .flat_map(|(cs, b)| {
                arms.iter().map(move |a| {
                    let mut cs = cs.clone();
                    cs.extend(a.iter().cloned());
                    (cs, b.clone())
                })
            })
            .collect();
    }
    for (n, pieces) in bs {
        terms = terms
            .into_iter()
            .flat_map(|(cs, b)| {
                pieces.iter().map(move |p| {
                    let mut b = b.clone();
                    b.insert(n.clone(), *p);
                    (cs.clone(), b)
                })
            })
            .collect();
    }
    let mut out: BTreeMap<String, (IntervalSet, IntervalSet)> = bs
        .keys()
        .map(|n| (n.clone(), (IntervalSet::empty(), IntervalSet::empty())))
        .collect();
    for (cs, b) in &terms {
        let [near, far] = points(cs, b, reach, exact);
        let Some(near) = near else {
            assert!(
                far.is_none(),
                "a point only with the wider hubs: {cs:?} {b:?}"
            );
            continue;
        };
        let far = far.expect("the wider enumeration holds the narrower");
        for (n, (hull, exact)) in near {
            let o = out.get_mut(&n).expect("a name");
            // Within the name's box in this disjunct, which a far end may reach only with
            // hubs beyond either range.
            let (l, h) = b[&n];
            let end = |e: Option<i64>, inf: End| e.map_or(inf, |v| End::Fin(Num::from(v)));
            let within = IntervalSet::range(end(l, End::NegInf), end(h, End::PosInf));
            o.0 = o.0.join(&widened(&hull, &far[&n].0).meet(&within));
            o.1 = o.1.join(&widened(&exact, &far[&n].1).meet(&within));
        }
    }
    out.into_iter()
        .map(|(n, (h, e))| (n, (show(&h), show(&e))))
        .collect()
}

/// The projection by pendants of the part, each name met with its box, or `None` where the
/// route is not taken.
fn hung(s: &Scope, f: &Formula) -> Option<BTreeMap<String, String>> {
    let out = s.project_by_pendants(f)?;
    Some(
        out.into_iter()
            .map(|(n, x)| (n.to_string(), show(&s.get(&n).ints().meet(&x))))
            .collect(),
    )
}

/// Each part the projection of the whole part refused in 3000 random programs
/// (`probe_diff`, seeds 1 to 10 of 300 cases each), the boxes of its names then, and its
/// projection by pendants, each name met with its box.
const REFUSED: &[(&str, &str, &str)] = &[
    (
        "(a <= 3 || b >= 3) && a + b <= 11 && a + c <= b - 3 && a + b + z2 >= c - 1 && a + b + c >= z1 - 2 && a + b == z3 + 10 && a + b >= z3 - 8 && b <= c + z1 + 6",
        "a=[1,5] b=[6,10] c=[-2,4] z1=[-1,17] z2=[-14,13] z3=[0,1]",
        "a=[1,5] b=[6,10] c=[-2,4] z1=[-1,17] z3=[0,1] z2=[-14,13]",
    ),
    (
        "(a >= 1 || z3 <= -1) && a + b <= 11 && a + c <= b - 3 && a + b + z2 >= c - 1 && a + b + c >= z1 - 2 && a + b == z3 + 10 && a + b >= z3 - 8 && b <= c + z1 + 6",
        "a=[1,5] b=[6,10] c=[-2,4] z1=[-1,17] z2=[-14,13] z3=[0,1]",
        "a=[1,5] b=[6,10] c=[-2,4] z1=[-1,17] z3=[0,1] z2=[-14,13]",
    ),
    (
        "a + b <= 11 && a + b + c == z0 - 1 && a + b + c == z2 + 8 && a + z1 >= c - 3 && 2 * a + 2 * c >= b + 1 && 2 * a + c >= z1 - 11 && b + 2 * c <= z3 + 4 && z0 >= z1 + 7",
        "a=[22,inf] b=[-inf,-11] c=[4,inf] z0=[16,inf] z1=[9,inf] z2=[7,inf] z3=[-inf,-7]",
        "a=[22,inf] b=[-inf,-11] c=[4,inf] z0=[16,inf] z1=[9,inf] z2=[7,inf] z3=[-inf,-7]",
    ),
    (
        "a + b <= 11 && a + c <= b - 3 && a + b + z2 >= c - 1 && a + b + c >= z1 - 2 && a + b == z3 + 10 && a + b >= z3 - 8 && b <= c + z1 + 6",
        "a=[1,5] b=[6,10] c=[-2,4] z1=[-1,17] z2=[-14,13] z3=[0,1]",
        "a=[1,5] b=[6,10] c=[-2,4] z1=[-1,17] z3=[0,1] z2=[-14,13]",
    ),
    (
        "(a >= 3 || b <= 5) && a + b <= 11 && a + b + c == z0 - 1 && a + b + c == z2 + 8 && a + z1 >= c - 3 && 2 * a + 2 * c >= b + 1 && 2 * a + c >= z1 - 11 && b + 2 * c <= z3 + 4 && z0 >= z1 + 7",
        "a=[-4,inf] b=[-inf,8] c=[-inf,inf] z0=[16,inf] z1=[9,inf] z2=[7,inf] z3=[-inf,-7]",
        "a=[22,inf] b=[-inf,-11] c=[4,inf] z0=[16,inf] z1=[9,inf] z2=[7,inf] z3=[-inf,-7]",
    ),
    (
        "2 * a + b + c <= z2 - 7 && 2 * a <= b + z1 - 3 && a + 2 * b <= z2 - 2 && a + b + c >= z2 - 6 && a + c == z3 - 5 && z2 <= z3 - 11",
        "a=[-inf,-14] b=[1,8] c=[-inf,inf] z1=[-9,inf] z2=[-inf,-9] z3=[-inf,2]",
        "a=[-inf,-14] b=[1,8] c=[10,inf] z2=[-inf,-9] z3=[-inf,2] z1=[-9,inf]",
    ),
    (
        "2 * a + b + c <= z2 - 7 && 2 * a <= b + z1 - 3 && a + b + c >= z2 - 6 && a + c == z3 - 5 && z2 <= z3 - 11",
        "a=[-inf,-1] b=[1,8] c=[-inf,inf] z1=[-9,inf] z2=[-inf,-9] z3=[-inf,2]",
        "a=[-inf,-14] b=[1,8] c=[-inf,inf] z2=[-inf,-9] z3=[-inf,2] z1=[-9,inf]",
    ),
    (
        "!(2 * b + c == z4 - 6) && a <= b + z3 - 8 && a + z1 == 2 * b + c + 1 && a + z1 == 2 * b + c + 1 && a + b >= z2 - 9 && a + b >= z4 - 9 && a + b >= z5 - 11 && 2 * b + 2 * c <= z5 && 2 * b <= c + z1 - 1 && z1 >= z3 + 4",
        "a=[-5,2] b=[-3,11] c=[-2,1] z1=[-6,7] z2=[10,22] z3=[-8,19] z4=[-inf,22] z5=[10,24]",
        "a=[] b=[] c=[] z1=[] z3=[] z4=[] z5=[] z2=[]",
    ),
    (
        "a + 2 * b + 2 * c <= z1 - 2 && a + 2 * b <= z4 + 4 && a >= b + z4 && a + 2 * b + c == z0 + 6 && a + 2 * b + c >= z4 - 4",
        "a=[-inf,inf] b=[-inf,1] c=[-6,inf] z0=[-inf,-2] z1=[-4,2] z4=[-inf,8]",
        "a=[-inf,inf] b=[-inf,1] c=[-6,inf] z4=[-inf,8] z1=[-4,2] z0=[-inf,-2]",
    ),
    (
        "a + 2 * b + c <= -6 && a + b + c <= z3 - 8 && a + 2 * b >= z6 - 10 && 2 * a + c == z2 + 5 && 2 * b + c == z1 + 3 && z1 >= z3 - 1",
        "a=[-inf,inf] b=[-inf,inf] c=[-inf,inf] z1=[-inf,3] z2=[-inf,-19] z3=[-inf,4] z6=[-inf,13]",
        "a=[-inf,inf] b=[-inf,inf] c=[-inf,inf] z1=[-inf,3] z3=[-inf,4] z6=[-inf,13] z2=[-inf,-19]",
    ),
    (
        "a + 2 * b + c <= -6 && a + b + c <= z3 - 8 && a + 2 * b >= z6 - 10 && a >= c + z4 - 5 && 2 * a + c == z2 + 5 && 2 * b + c == z1 + 3 && z1 >= z3 - 1",
        "a=[-inf,inf] b=[-inf,inf] c=[-inf,inf] z1=[-inf,3] z2=[-inf,-19] z3=[-inf,4] z4=[-inf,12] z6=[-inf,13]",
        "a=[-inf,inf] b=[-inf,inf] c=[-inf,inf] z1=[-inf,3] z3=[-inf,4] z6=[-inf,13] z4=[-inf,12] z2=[-inf,-19]",
    ),
    (
        "a + 2 * b + c <= z5 - 12 && a + z1 == b + c + 5 && a + 2 * c <= z4 - 10 && a + z1 == b + c + 5 && a + b + c >= z5 + 5 && a + 2 * b == c + z2 - 6",
        "a=[-inf,inf] b=[-inf,-17] c=[-inf,2] z1=[-inf,8 10,inf] z2=[-inf,5] z4=[-inf,16] z5=[-inf,-7]",
        "a=[-inf,inf] b=[-inf,-17] c=[-inf,2] z1=[-inf,8 10,inf] z5=[-inf,-7] z4=[-inf,16] z2=[-inf,5]",
    ),
    (
        "a + c <= z0 - 2 && a + b >= z0 - 4 && a + z2 >= c + 3 && 2 * a + b + c == z1 + 4",
        "a=[1,8] b=[-8,4] c=[-inf,6] z0=[0,3 5,8 10,16] z1=[-inf,22] z2=[-inf,inf]",
        "a=[1,8] b=[-8,4] c=[-inf,6] z0=[0,3 5,8 10,16] z2=[-inf,inf] z1=[-inf,22]",
    ),
    (
        "a + c <= z0 - 2 && a + b >= z0 - 4 && a + z2 >= c + 3 && 2 * a + b + c == z1 + 4",
        "a=[-2,8] b=[-8,4] c=[-inf,6] z0=[0,3 5,8 10,16] z1=[-inf,22] z2=[-inf,inf]",
        "a=[-2,8] b=[-8,4] c=[-inf,6] z0=[0,3 5,8 10,16] z2=[-inf,inf] z1=[-inf,22]",
    ),
    (
        "(b >= 0 || z3 <= 4) && 2 * a + 2 * b <= c + 11 && 2 * a + b + c <= 4 && a + b + c <= z3 - 3 && a + c >= b + z4 - 10 && a + b >= z3 - 3 && a + 2 * b >= z2 - 6 && a + c == z0 + 1",
        "a=[-4,inf] b=[-inf,0] c=[-inf,0] z0=[-5,inf] z2=[-inf,9] z3=[-inf,6] z4=[-inf,inf]",
        "a=[-4,inf] b=[-inf,0] c=[-inf,0] z3=[-inf,6] z4=[-inf,inf] z2=[-inf,9] z0=[-5,inf]",
    ),
    (
        "(b >= 6 || z0 <= -2) && a + 2 * b + 2 * c <= z1 - 2 && a + 2 * b <= z4 + 4 && a >= b + z4 && a + 2 * b + c == z0 + 6 && a + 2 * b + c >= z4 - 4",
        "a=[-inf,inf] b=[-inf,1] c=[-6,inf] z0=[-inf,-2] z1=[-4,2] z4=[-inf,8]",
        "a=[-inf,inf] b=[-inf,1] c=[-6,inf] z0=[-inf,-2] z4=[-inf,8] z1=[-4,2]",
    ),
    (
        "!(b + c == z1 + 12) && a + 2 * b + 2 * c <= z1 + 3 && a + 2 * b + c <= z2 + 5 && a + b <= z5 - 11 && a + z5 >= b + 11 && a + b + c >= z3 - 10 && 2 * a + 2 * b + 2 * c >= z0 - 3 && b == c + z4",
        "a=[2,10] b=[-7,1] c=[-20,inf] z0=[-inf,inf] z1=[-47,inf] z2=[-29,inf] z3=[-7,inf] z4=[-inf,21] z5=[6,14]",
        "a=[2,10] b=[-7,1] c=[-20,inf] z1=[-47,inf] z5=[6,14] z2=[-29,inf] z3=[-7,inf] z0=[-inf,inf] z4=[-inf,21]",
    ),
    (
        "!(b == c + z1 + 7) && 2 * a + c <= b + z3 - 5 && a + b + c <= z2 - 5 && a + z4 <= b + 2 * c + 12 && 2 * a + c >= b + z1 + 5 && 2 * a + b + c == z4 + 2",
        "a=[-inf,5] b=[-inf,4] c=[-inf,inf] z1=[-inf,-1] z2=[-inf,inf] z3=[-inf,9] z4=[-inf,16]",
        "a=[-inf,4] b=[-inf,4] c=[-inf,inf] z1=[-inf,-1] z4=[-inf,10] z3=[-inf,9] z2=[-inf,inf]",
    ),
    (
        "!(b == c + z1 + 7) && 2 * a + c <= b + z3 - 5 && a + b + c <= z2 - 5 && a + z4 <= b + 2 * c + 12 && a + 2 * b + c == z3 + 8 && 2 * a + c >= b + z1 + 5 && 2 * a + b + c == z4 + 2",
        "a=[-inf,0] b=[-inf,-3] c=[-inf,inf] z1=[-inf,-1] z2=[-inf,inf] z3=[-inf,9] z4=[-inf,10]",
        "a=[-inf,-22] b=[-inf,-3] c=[-inf,inf] z1=[-inf,-1] z3=[-inf,9] z4=[-inf,-4] z2=[-inf,inf]",
    ),
    (
        "(a >= 6 || b <= -1) && a + b + z1 == c - 7 && 2 * b + c == z0 + 7",
        "a=[-inf,inf] b=[-inf,inf] c=[-inf,inf] z0=[-8,inf] z1=[18,inf]",
        "a=[-inf,inf] b=[-inf,inf] c=[1,inf] z1=[18,inf] z0=[-8,inf]",
    ),
    (
        "(a >= 6 || b <= -1) && a + b + z1 == c - 7 && 2 * b + c == z0 + 7",
        "a=[-inf,inf] b=[-inf,inf] c=[-inf,inf] z0=[-inf,-9] z1=[18,inf]",
        "a=[-inf,inf] b=[-inf,-1] c=[-inf,inf] z1=[18,inf] z0=[-inf,-9]",
    ),
    (
        "(a >= 6 || b <= -1) && a + b + z1 == c - 7 && 2 * b + c == z0 + 7",
        "a=[-inf,inf] b=[-inf,inf] c=[-inf,inf] z0=[-inf,inf] z1=[18,inf]",
        "a=[-inf,inf] b=[-inf,inf] c=[-inf,inf] z1=[18,inf] z0=[-inf,inf]",
    ),
    (
        "!(2 * a + b + c == z1 + 9) && a + b + 2 * c <= z0 - 12 && a + c + z2 == b - 6",
        "a=[-inf,inf] b=[-inf,inf] c=[-inf,inf] z0=[-inf,inf] z1=[-inf,inf] z2=[-inf,inf]",
        "a=[-inf,inf] b=[-inf,inf] c=[-inf,inf] z1=[-inf,inf] z0=[-inf,inf] z2=[-inf,inf]",
    ),
    (
        "a + b + 2 * c == z1 - 1 && a + b + 2 * c == z2 - 2",
        "a=[-8,inf] b=[-inf,1 3,inf] c=[-inf,inf] z1=[-inf,inf] z2=[-inf,inf]",
        "a=[-8,inf] b=[-inf,1 3,inf] c=[-inf,inf] z1=[-inf,inf] z2=[-inf,inf]",
    ),
];

/// Each of `rows` projected by pendants as the table says, which is the union over the
/// disjuncts of the hulls the brute force finds (its exact sets of values shown on a mismatch).
fn check(rows: &[(&str, &str, &str)]) {
    let mut wrong = Vec::new();
    for (part, bx, want) in rows {
        let items = parse(part);
        let bs = boxes(bx);
        let s = scope(&bs);
        let got = hung(&s, &formula(&items));
        let want: BTreeMap<String, String> = bracketed(want)
            .into_iter()
            .map(|(n, x)| (n, format!("[{x}]")))
            .collect();
        let hulls: BTreeMap<String, String> = brute(&items, &bs, NARROW, false)
            .into_iter()
            .map(|(n, (h, _))| (n, h))
            .collect();
        if hulls != want || got.as_ref() != Some(&want) {
            let sets: BTreeMap<String, String> = brute(&items, &bs, NARROW, true)
                .into_iter()
                .map(|(n, (_, e))| (n, e))
                .collect();
            wrong.push(format!(
                "{part}\n  boxes {bx}\n  hulls {hulls:?}\n  sets  {sets:?}\n  hung  {got:?}\n  want  {want:?}"
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "{} of {} wrong:\n{}",
        wrong.len(),
        rows.len(),
        wrong.join("\n")
    );
}

/// `!(t == 0)` as its two arms, `t - 1 >= 0` and `-t - 1 >= 0`.
fn compare_ne(c: &Cmp) -> Vec<Vec<Cmp>> {
    let neg = c.terms.iter().map(|(n, k)| (n.clone(), -k)).collect();
    vec![
        vec![Cmp {
            terms: c.terms.clone(),
            constant: c.constant - 1,
            eq: false,
        }],
        vec![Cmp {
            terms: neg,
            constant: -c.constant - 1,
            eq: false,
        }],
    ]
}

// The rows of [`REFUSED`] in groups that each take under 0.5 s alone, row 22 about 0.6 s.

#[test]
fn refused_parts_projected_exactly_by_pendants_rows_0_to_4() {
    check(&REFUSED[..5]);
}

#[test]
fn refused_parts_projected_exactly_by_pendants_rows_5_to_9() {
    check(&REFUSED[5..10]);
}

#[test]
fn refused_parts_projected_exactly_by_pendants_row_10() {
    check(&REFUSED[10..11]);
}

#[test]
fn refused_parts_projected_exactly_by_pendants_rows_11_to_16() {
    check(&REFUSED[11..17]);
}

#[test]
fn refused_parts_projected_exactly_by_pendants_rows_17_and_18() {
    check(&REFUSED[17..19]);
}

#[test]
fn refused_parts_projected_exactly_by_pendants_rows_19_and_20() {
    check(&REFUSED[19..21]);
}

#[test]
fn refused_parts_projected_exactly_by_pendants_rows_21_and_23() {
    check(&REFUSED[21..22]);
    check(&REFUSED[23..]);
}

#[test]
fn refused_parts_projected_exactly_by_pendants_row_22() {
    check(&REFUSED[22..23]);
}

/// A random sum of two or three of the hubs, coefficients from -1, 1 and 2.
fn hub_terms(r: &mut Rng) -> BTreeMap<String, i64> {
    let mut hs = vec!["a", "b", "c"];
    (0..2 + r.below(2))
        .map(|_| {
            let h = hs.remove(r.below(hs.len()));
            (h.to_string(), [1, 1, -1, 2][r.below(4)])
        })
        .collect()
}

/// A random part over hubs `a`, `b`, `c` and `z0`..`z{nz-1}`: pendants of the `z` on sums
/// of hubs, constraints on the hubs, differences of two `z`, and up to two disjunctions.
fn random_part(r: &mut Rng, nz: usize) -> Vec<Item> {
    let mut items = Vec::new();
    for _ in 0..3 + r.below(8) {
        let z = format!("z{}", r.below(nz));
        let c = r.int(-8, 12);
        let mut terms = hub_terms(r);
        items.push(match r.below(9) {
            0..=3 => {
                terms.insert(z, [1, -1][r.below(2)]);
                Item::Con(Cmp {
                    terms,
                    constant: c,
                    eq: r.below(3) == 0,
                })
            }
            4 | 5 => Item::Con(Cmp {
                terms,
                constant: c,
                eq: false,
            }),
            6 => {
                let w = format!("z{}", r.below(nz));
                if w == z {
                    continue;
                }
                Item::Con(Cmp {
                    terms: BTreeMap::from([(z, 1), (w, -1)]),
                    constant: c,
                    eq: false,
                })
            }
            7 => {
                terms.insert(z, -1);
                Item::Ne(Cmp {
                    terms,
                    constant: c,
                    eq: true,
                })
            }
            _ => Item::Or(vec![
                vec![Cmp {
                    terms,
                    constant: c,
                    eq: false,
                }],
                vec![Cmp {
                    terms: BTreeMap::from([(z, -1)]),
                    constant: r.int(-2, 8),
                    eq: false,
                }],
            ]),
        });
    }
    items
}

/// Random boxes for the hubs and the `z`, some unbounded and some of a hub with a hole.
fn random_boxes(r: &mut Rng, nz: usize) -> BTreeMap<String, Vec<Piece>> {
    let names = ["a", "b", "c"]
        .map(String::from)
        .into_iter()
        .chain((0..nz).map(|i| format!("z{i}")));
    names
        .map(|n| {
            let lo = (r.below(3) != 0).then(|| r.int(-10, 4));
            let hi = (r.below(3) != 0).then(|| lo.unwrap_or(-10) + r.int(0, 20));
            let pieces = match (lo, hi) {
                (Some(l), Some(h)) if !n.starts_with('z') && h - l >= 4 && r.below(6) == 0 => {
                    let m = l + 1 + r.below((h - l - 2) as usize) as i64;
                    vec![(Some(l), Some(m)), (Some(m + 2), Some(h))]
                }
                p => vec![p],
            };
            (n, pieces)
        })
        .collect()
}

/// The projection of the whole part framed by its boxes, met with each box, or `None` where
/// it refuses a question.
fn whole(s: &Scope, f: &Formula) -> Option<BTreeMap<String, String>> {
    let syms: Vec<Atom> = f
        .atoms()
        .into_iter()
        .filter(|a| matches!(a, Atom::Sym(_)))
        .collect();
    let mut parts: Vec<Formula> = syms
        .iter()
        .map(|a| match a {
            Atom::Sym(n) => presburger::member(a, s.get(n).ints()),
            _ => unreachable!("a name"),
        })
        .collect();
    parts.push(f.clone());
    let (each, skipped) = presburger::project_each(&Formula::and(parts), &syms).ok()?;
    if !skipped.is_empty() {
        return None;
    }
    syms.iter()
        .zip(each)
        .map(|(a, x)| {
            let Atom::Sym(n) = a else {
                unreachable!("a name")
            };
            Some((n.to_string(), show(&s.get(n).ints().meet(&x.ok()?))))
        })
        .collect()
}

/// On random parts from a new seed each run, the projection by pendants, where it is taken,
/// and that of the whole part, where neither refuses, are the same; parts are drawn until
/// [`PENDANT_COMPARED`] are compared. Seed 0x7e4d at 400 parts took 1.6 s.
#[test]
fn the_projection_by_pendants_is_that_of_the_whole_part_where_neither_refuses() {
    let (r, seed) = Rng::fresh("the projection by pendants");
    pendants_against_whole(r, seed);
}

/// The parts [`pendants_against_whole`] compares in a run. Over 956 seeds (FAIL-pendants-route-
/// quarter-seed) 30.8% of the parts are compared, 4.9 parts in 120 the standard deviation,
/// so a fixed 120 parts compared fewer than a quarter (30) on 58 seeds, and 400 parts fewer
/// than a quarter (100) on 4: the floor of a quarter lies 2.5 standard deviations under the
/// mean at either size. Reaching 40 took 130 parts on average and 193 at most.
const PENDANT_COMPARED: usize = 40;

/// The parts [`pendants_against_whole`] may draw before it has compared [`PENDANT_COMPARED`]:
/// 240, where 74 are compared on average, 55 at least over the 956 seeds, and 40 lies 4.9
/// standard deviations under the mean. It fails when the route is taken on fewer than one
/// part in six, half the rate measured.
const PENDANT_PARTS_MAX: usize = 240;

/// Random parts drawn from `r` until [`PENDANT_COMPARED`] are compared: the projection by
/// pendants, where it is taken, and that of the whole part, where neither refuses, are the
/// same on each, and the count is met within [`PENDANT_PARTS_MAX`] parts.
fn pendants_against_whole(mut r: Rng, seed: u64) {
    let (mut same, mut taken, mut cases) = (0, 0, 0);
    let mut wrong = Vec::new();
    while same + wrong.len() < PENDANT_COMPARED && cases < PENDANT_PARTS_MAX {
        let nz = 2 + r.below(5);
        let items = random_part(&mut r, nz);
        let bs = random_boxes(&mut r, nz);
        let s = scope(&bs);
        let f = formula(&items);
        cases += 1;
        let Some(got) = hung(&s, &f) else { continue };
        taken += 1;
        let Some(want) = whole(&s, &f) else { continue };
        if got == want {
            same += 1;
        } else {
            wrong.push(format!(
                "{f}\n  boxes {bs:?}\n  hung  {got:?}\n  whole {want:?}"
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "seed {seed}: {} differ:\n{}",
        wrong.len(),
        wrong.join("\n")
    );
    eprintln!("{cases} parts, the route taken on {taken}, the same as the whole on {same}");
    assert!(
        same >= PENDANT_COMPARED,
        "seed {seed}: {same} compared of {cases}: too few to show anything"
    );
}

/// Case 32 of the random programs of seed 2 (`probe_diff`): two of its parts were refused
/// by the projection of the whole part (Growth) and are projected by their pendants (rows
/// of [`REFUSED`], each checked by brute force), which narrows the scope it ends with.
#[test]
fn a_program_whose_refused_parts_are_projected_by_pendants_ends_narrower() {
    let program: Vec<(Term, bool, bool)> = vec![
        (prim(Prim::Ge, vec![var("z1"), lit(9)]), true, false),
        (
            prim(
                Prim::Le,
                vec![
                    prim(
                        Prim::Add,
                        vec![
                            prim(
                                Prim::Add,
                                vec![
                                    prim(Prim::Mul, vec![lit(2), var("c")]),
                                    prim(Prim::Mul, vec![lit(-1), var("b")]),
                                ],
                            ),
                            prim(Prim::Mul, vec![lit(2), var("a")]),
                        ],
                    ),
                    lit(0),
                ],
            ),
            false,
            false,
        ),
        (
            prim(
                Prim::Ge,
                vec![prim(Prim::Sub, vec![var("z2"), var("z0")]), lit(8)],
            ),
            true,
            true,
        ),
        (
            prim(
                Prim::Ge,
                vec![
                    var("z1"),
                    prim(
                        Prim::Add,
                        vec![
                            prim(
                                Prim::Add,
                                vec![prim(Prim::Mul, vec![lit(-1), var("a")]), var("c")],
                            ),
                            lit(-3),
                        ],
                    ),
                ],
            ),
            true,
            false,
        ),
        (
            prim(
                Prim::Or,
                vec![
                    prim(Prim::Lt, vec![var("b"), lit(6)]),
                    prim(Prim::Gt, vec![var("a"), lit(2)]),
                ],
            ),
            true,
            false,
        ),
        (
            prim(
                Prim::Le,
                vec![prim(Prim::Add, vec![var("a"), var("b")]), lit(11)],
            ),
            true,
            false,
        ),
        (
            prim(
                Prim::Ge,
                vec![
                    var("z1"),
                    prim(
                        Prim::Add,
                        vec![
                            prim(
                                Prim::Add,
                                vec![
                                    prim(
                                        Prim::Add,
                                        vec![prim(Prim::Mul, vec![lit(2), var("a")]), var("b")],
                                    ),
                                    prim(Prim::Mul, vec![lit(-1), var("c")]),
                                ],
                            ),
                            lit(3),
                        ],
                    ),
                ],
            ),
            true,
            true,
        ),
        (
            prim(
                Prim::Ge,
                vec![
                    var("z2"),
                    prim(
                        Prim::Add,
                        vec![prim(Prim::Add, vec![var("c"), var("b")]), lit(-6)],
                    ),
                ],
            ),
            true,
            true,
        ),
        (
            prim(
                Prim::Or,
                vec![
                    prim(Prim::Lt, vec![var("z2"), lit(8)]),
                    prim(Prim::Gt, vec![var("c"), lit(-2)]),
                ],
            ),
            true,
            true,
        ),
        (
            prim(
                Prim::Ge,
                vec![
                    var("z1"),
                    prim(
                        Prim::Add,
                        vec![
                            prim(
                                Prim::Add,
                                vec![prim(Prim::Mul, vec![lit(2), var("a")]), var("c")],
                            ),
                            lit(12),
                        ],
                    ),
                ],
            ),
            false,
            false,
        ),
        (
            prim(
                Prim::Eq,
                vec![
                    prim(
                        Prim::Sub,
                        vec![
                            prim(
                                Prim::Add,
                                vec![prim(Prim::Add, vec![var("a"), var("b")]), var("c")],
                            ),
                            var("z2"),
                        ],
                    ),
                    lit(8),
                ],
            ),
            true,
            false,
        ),
        (prim(Prim::Le, vec![var("b"), lit(10)]), true, true),
        (
            prim(
                Prim::Ge,
                vec![prim(Prim::Sub, vec![var("z0"), var("z1")]), lit(7)],
            ),
            true,
            false,
        ),
        (
            prim(
                Prim::Eq,
                vec![
                    prim(
                        Prim::Sub,
                        vec![
                            prim(
                                Prim::Add,
                                vec![prim(Prim::Add, vec![var("a"), var("c")]), var("b")],
                            ),
                            var("z0"),
                        ],
                    ),
                    lit(-1),
                ],
            ),
            true,
            false,
        ),
        (
            prim(
                Prim::Ge,
                vec![
                    var("z3"),
                    prim(
                        Prim::Add,
                        vec![
                            prim(
                                Prim::Add,
                                vec![prim(Prim::Mul, vec![lit(2), var("c")]), var("b")],
                            ),
                            lit(-4),
                        ],
                    ),
                ],
            ),
            true,
            false,
        ),
        (prim(Prim::Le, vec![var("z0"), lit(11)]), false, false),
        (prim(Prim::Ge, vec![var("z3"), lit(-6)]), false, false),
        (prim(Prim::Ne, vec![var("b"), lit(-1)]), true, false),
    ];
    let p = Premises::new();
    let names: Vec<Arc<str>> = ["a", "b", "c", "z0", "z1", "z2", "z3"]
        .map(Arc::from)
        .to_vec();
    let mut s = ints(&names);
    // Each test is assumed to hold, or not, or both outcomes are joined.
    for (t, holds, joined) in &program {
        s = if *joined {
            let mut j = s.assume(t, true, &p).join(&s.assume(t, false, &p));
            j.reduce();
            j
        } else {
            s.assume(t, *holds, &p)
        };
    }
    let want = [
        "a:",
        "  ints [22..]",
        "  type int",
        "b:",
        "  ints [..=-11]",
        "  type (\\ int -1)",
        "c:",
        "  ints [4..]",
        "  type int",
        "z0:",
        "  ints [16..]",
        "  type int",
        "z1:",
        "  ints [9..]",
        "  type int",
        "z2:",
        "  ints [7..]",
        "  type int",
        "z3:",
        "  ints [..=-7]",
        "  type int",
        "relation a + b <= 11 && a + b + c == z0 - 1 && a + b + c == z2 + 8 && a + z1 >= c - 3 && 2 * a + 2 * c >= b + 1 && 2 * a + c >= z1 - 11 && b + 2 * c <= z3 + 4 && z0 >= z1 + 7 && (a >= 3 || b <= 5) && (c >= -1 || z2 <= 7 || (c <= -2 && z2 >= 8 && !(c >= -1 || z2 <= 7)))",
    ];
    assert_eq!(format!("{s}").trim_end(), want.join("\n"));
}

/// `c` with each coefficient and its constant negated: for an equation, the same equation.
fn negated(c: &Cmp) -> Cmp {
    Cmp {
        terms: c.terms.iter().map(|(n, k)| (n.clone(), -k)).collect(),
        constant: -c.constant,
        eq: c.eq,
    }
}

/// The projections of `f` framed by the boxes of `s`, each met with its box, a refused one
/// the bounds the box stage gives ([`presburger::project_each_boxed`]) with the refusal, and
/// the causes for which a disjunction was left out, or the refusal of the whole with the
/// bounds kept.
fn each_answer(s: &Scope, f: &Formula, syms: &[Atom]) -> String {
    let mut parts: Vec<Formula> = syms
        .iter()
        .map(|a| match a {
            Atom::Sym(n) => presburger::member(a, s.get(n).ints()),
            _ => unreachable!("a name"),
        })
        .collect();
    parts.push(f.clone());
    let got = presburger::project_each_boxed(&Formula::and(parts), syms);
    let shown: Vec<String> = syms
        .iter()
        .zip(got.each)
        .map(|(a, (x, e))| {
            let Atom::Sym(n) = a else {
                unreachable!("a name")
            };
            let x = show(&s.get(n).ints().meet(&x));
            match e {
                None => format!("{n}={x}"),
                Some(e) => format!("{n}={x} refused: {e:?}"),
            }
        })
        .collect();
    match got.whole {
        Some(e) => format!("refused: {e:?}, kept {}", shown.join(" ")),
        None => format!("{} left out: {:?}", shown.join(" "), got.skipped),
    }
}

/// `items` written another way with the same points: each equation negated or not, and held
/// once or twice, the second time negated; each inequality held once or twice; with `split`,
/// some equations `t == 0` written as `t >= 0 && -t >= 0`; and the items, the arms of each
/// disjunction and the constraints of each arm in a random order.
fn rewritten(r: &mut Rng, items: &[Item], split: bool) -> Formula {
    let mut parts = Vec::new();
    for i in items {
        match i {
            Item::Con(c) if c.eq => {
                let c = if r.below(2) == 0 {
                    c.clone()
                } else {
                    negated(c)
                };
                if split && r.below(2) == 0 {
                    let ge = Cmp { eq: false, ..c };
                    parts.push(con(&negated(&ge)));
                    parts.push(con(&ge));
                } else {
                    if r.below(2) == 0 {
                        parts.push(con(&negated(&c)));
                    }
                    parts.push(con(&c));
                }
            }
            Item::Con(c) => {
                for _ in 0..1 + r.below(2) {
                    parts.push(con(c));
                }
            }
            Item::Ne(c) => {
                let c = if r.below(2) == 0 {
                    c.clone()
                } else {
                    negated(c)
                };
                parts.push(Formula::Not(Shared::new(con(&c))));
            }
            Item::Or(arms) => {
                let mut arms: Vec<Formula> = arms
                    .iter()
                    .map(|a| {
                        let mut cs: Vec<Formula> = a.iter().map(con).collect();
                        shuffle(r, &mut cs);
                        Formula::and(cs)
                    })
                    .collect();
                shuffle(r, &mut arms);
                parts.push(Formula::or(arms));
            }
        }
    }
    shuffle(r, &mut parts);
    Formula::and(parts)
}

/// `xs` in a random order.
fn shuffle<T>(r: &mut Rng, xs: &mut [T]) {
    for i in (1..xs.len()).rev() {
        xs.swap(i, r.below(i + 1));
    }
}

/// `c` with each coefficient and its constant multiplied by `m`, and for an inequality `j` of
/// `0..m` added to its constant: `m·t + j >= 0` has the integer points of `t >= 0`, since
/// `m·t >= -j > -m` gives `t > -1`.
fn times(c: &Cmp, m: i64, j: i64) -> Cmp {
    Cmp {
        terms: c.terms.iter().map(|(n, k)| (n.clone(), m * k)).collect(),
        constant: m * c.constant + if c.eq { 0 } else { j },
        eq: c.eq,
    }
}

/// `items` written another way with the same points: each constraint, in the disjunctions
/// and under `!` too, multiplied by 1, 2 or 3 and, if an inequality, with a constant below
/// that factor added (`2 * a >= 2 * b - 1` for `a >= b`); each equation negated or not and
/// held once or twice, the second time negated; and the items, the arms of each disjunction
/// and the constraints of each arm in a random order.
fn scaled(r: &mut Rng, items: &[Item]) -> Formula {
    let one = |r: &mut Rng, c: &Cmp| {
        let m = 1 + r.int(0, 2);
        let j = r.int(0, m - 1);
        times(c, m, j)
    };
    let mut parts = Vec::new();
    for i in items {
        match i {
            Item::Con(c) => {
                let c = one(r, c);
                let c = if c.eq && r.below(2) == 0 {
                    negated(&c)
                } else {
                    c
                };
                if c.eq && r.below(2) == 0 {
                    parts.push(con(&negated(&one(r, &c))));
                }
                parts.push(con(&c));
            }
            Item::Ne(c) => {
                let c = one(r, c);
                parts.push(Formula::Not(Shared::new(con(&c))));
            }
            Item::Or(arms) => {
                let mut arms: Vec<Formula> = arms
                    .iter()
                    .map(|a| {
                        let mut cs: Vec<Formula> = a.iter().map(|c| con(&one(r, c))).collect();
                        shuffle(r, &mut cs);
                        Formula::and(cs)
                    })
                    .collect();
                shuffle(r, &mut arms);
                parts.push(Formula::or(arms));
            }
        }
    }
    shuffle(r, &mut parts);
    Formula::and(parts)
}

/// The names `items` mention, in order: those of a formula that is `false` as written too.
fn item_names(items: &[Item]) -> Vec<Atom> {
    let mut names = std::collections::BTreeSet::new();
    let mut add = |c: &Cmp| names.extend(c.terms.keys().cloned());
    for i in items {
        match i {
            Item::Con(c) | Item::Ne(c) => add(c),
            Item::Or(arms) => arms.iter().flatten().for_each(&mut add),
        }
    }
    names
        .into_iter()
        .map(|n| Atom::Sym(n.as_str().into()))
        .collect()
}

/// `items` written four ways with the same points: as they are; each equation and each
/// excluded equation negated; each equation held twice, the second time negated; and each
/// equation `t == 0` split into `t >= 0 && -t >= 0`.
fn four_ways(items: &[Item]) -> [(&'static str, Formula); 4] {
    let mut negated_all = Vec::new();
    let mut twice = Vec::new();
    let mut split = Vec::new();
    for i in items {
        let as_is = formula(std::slice::from_ref(i));
        match i {
            Item::Con(c) if c.eq => {
                let ge = Cmp {
                    eq: false,
                    ..c.clone()
                };
                negated_all.push(con(&negated(c)));
                twice.extend([con(c), con(&negated(c))]);
                split.extend([con(&ge), con(&negated(&ge))]);
            }
            Item::Ne(c) => {
                negated_all.push(Formula::Not(Shared::new(con(&negated(c)))));
                twice.push(as_is.clone());
                split.push(as_is);
            }
            _ => {
                negated_all.push(as_is.clone());
                twice.push(as_is.clone());
                split.push(as_is);
            }
        }
    }
    [
        ("as written", formula(items)),
        ("negated", Formula::and(negated_all)),
        ("held twice", Formula::and(twice)),
        ("split", Formula::and(split)),
    ]
}

/// The projections of `part` within `bx`, both of the whole part and by pendants, for each
/// of the four ways of writing it, each that differs from the first shown.
fn written_four_ways(part: &str, bx: &str) -> (String, Option<BTreeMap<String, String>>) {
    let items = parse(part);
    let s = scope(&boxes(bx));
    let syms = item_names(&items);
    let [(_, base), rest @ ..] = four_ways(&items);
    let want = (each_answer(&s, &base, &syms), hung(&s, &base));
    for (how, g) in rest {
        let got = (each_answer(&s, &g, &syms), hung(&s, &g));
        assert_eq!(got, want, "{part}\n  {how}: {g}\n  boxes {bx}");
    }
    want
}

/// The part of seed 7 case 264 (item PROJECT-each-canon), whose equation `a + z1 == 2 * b +
/// c + 1` was refused held once and answered held twice with opposite signs: held once, held
/// twice, and held once negated, it is empty every way, by pendants and as a whole.
#[test]
fn an_equation_held_once_twice_or_negated_gives_one_answer() {
    let (twice, bx, _) = REFUSED[7];
    let eq = "a + z1 == 2 * b + c + 1 && ";
    assert!(twice.contains(&format!("{eq}{eq}")));
    let once = twice.replacen(eq, "", 1);
    let opposite = twice.replacen(eq, "2 * b + c + 1 == a + z1 && ", 1);
    let empty: BTreeMap<String, String> = bracketed("a=[] b=[] c=[] z1=[] z2=[] z3=[] z4=[] z5=[]")
        .into_iter()
        .map(|(n, x)| (n, format!("[{x}]")))
        .collect();
    let want = "a=[] b=[] c=[] z1=[] z2=[] z3=[] z4=[] z5=[] left out: []";
    for text in [twice, &once, &opposite] {
        let (each, by_pendants) = written_four_ways(text, bx);
        assert_eq!(each, want, "{text}");
        assert_eq!(by_pendants.as_ref(), Some(&empty), "{text}");
    }
}

/// Parts on which the projection of the whole part answered differently as written, negated,
/// held twice or split (seeds 12, 13, 16 and 17 of 400 random parts, before item
/// PROJECT-each-canon), each with its boxes and the one answer of all four ways. The fourth's
/// `c` was refused before item PRES-project-each-cost, with the box stage's bounds `[-3,6]`;
/// its ends are exact: `c >= -3` from `a + 2 * c >= -4` and `a <= 3`, reached at
/// `a=2 b=5 c=-3 z1=0 z2=-4`; `c <= 6` from `a + b + 2 * c == z2 + 5`, `z2 <= 6`, `a >= 2`
/// and `b >= -4`, reached at `a=3 b=-4 c=6 z1=3 z2=6`. The fifth left out a `Tie` on `c` and
/// `z0` before item PERF-l139-family, with the same boxes: the question that the solver refused
/// is not asked since each side is first asked at its real bound.
const WRITTEN: &[(&str, &str, &str)] = &[
    (
        "a + b >= -2 && b + z2 <= 2 * c + 6 && !(a + 2 * b == z0 - 1) && !(a + z3 == 2 * c) && 2 * a + 2 * c >= b - 2 && 2 * a + 2 * b + c + z0 >= 5 && a + c >= -2 && b + c + z0 >= 3 && a + b + c + z3 == 0",
        "a=[-1,16] b=[-inf,inf] c=[-10,inf] z0=[-10,inf] z1=[-1,8] z2=[-6,14] z3=[-5,15]",
        "a=[-1,16] b=[-18,4] c=[-10,7] z0=[-3,inf] z2=[-6,14] z3=[-5,12] left out: []",
    ),
    (
        "!(b + 2 * c == z1 + 8) && 2 * a + c + z1 == b - 3 && (a + c >= -2 || z0 <= -2) && 2 * b >= c + 4 && a + b >= c + z0 + 2 && a + b + z0 >= 7 && z0 <= z1 - 4 && !(b + c == z0 - 1)",
        "a=[0,17] b=[-inf,7] c=[-inf,-10] z0=[-4,inf] z1=[2,19]",
        "a=[2,17] b=[-8,7] c=[-64,-10] z0=[-4,-2] z1=[2,19] left out: []",
    ),
    (
        "a >= b + z2 - 1 && !(2 * a + 2 * c == b + z2 - 9) && z0 <= z2 - 4 && a <= 2 * b + 2 * c + 2 && 2 * a + z0 == b + c - 8",
        "a=[-2,18] b=[-inf,6] c=[-inf,9] z0=[-8,inf] z1=[-inf,7] z2=[-3,6]",
        "a=[-2,7] b=[-11,6] c=[-4,9] z0=[-8,0] z2=[-3,6] left out: []",
    ),
    (
        "a + 2 * c >= -4 && (2 * a + b >= 7 || z2 <= 8) && a + 2 * b + c + z1 >= 4 && a >= b + z1 - 6 && (b >= c - 11 || z2 <= 4) && a + b + c >= z1 + 2 && a + z1 <= b + c + 9 && a + c >= z0 - 12 && a + b + 2 * c == z2 + 5",
        "a=[2,3] b=[-4,inf] c=[-inf,8] z0=[-6,-4] z1=[-7,13] z2=[-10,6]",
        "a=[2,3] b=[-4,16] refused: Growth c=[-3,6] z0=[-6,-4] z1=[-7,13] refused: Growth z2=[-10,6] refused: Growth left out: [Growth]",
    ),
    (
        "(2 * a >= b + 2 || z0 <= 4) && !(a + b + z0 == 2 * c - 8) && (2 * a + b + 2 * c >= -9 || z1 <= 6) && 2 * a + b == c + z0 - 1",
        "a=[-9,inf] b=[4,12] c=[-8,3 5,11] z0=[-inf,8] z1=[4,18] z2=[-inf,0]",
        "a=[-9,7] b=[4,12] c=[-8,3 5,11] z0=[-24,8] z1=[4,18] left out: []",
    ),
];

/// Checks that each of `rows` of [`WRITTEN`] has one projection of the whole part, the one
/// the table gives, and one by pendants, however its equations are written.
fn written_rows(rows: &[(&str, &str, &str)]) {
    let wrong: Vec<String> = rows
        .iter()
        .filter_map(|(part, bx, want)| {
            let (each, _) = written_four_ways(part, bx);
            (each != *want).then(|| format!("{part}\n  boxes {bx}\n  want {want}\n  got  {each}"))
        })
        .collect();
    assert!(
        wrong.is_empty(),
        "{} of {} wrong:\n{}",
        wrong.len(),
        rows.len(),
        wrong.join("\n")
    );
}

/// The rows of [`WRITTEN`] but row 3, which takes as long as the rest
/// ([`parts_once_answered_by_how_they_were_written_give_one_answer_row_3`]).
#[test]
fn parts_once_answered_by_how_they_were_written_give_one_answer() {
    written_rows(&WRITTEN[..3]);
    written_rows(&WRITTEN[4..]);
}

/// Row 3 of [`WRITTEN`], case 272 of seed 17.
#[test]
fn parts_once_answered_by_how_they_were_written_give_one_answer_row_3() {
    written_rows(&WRITTEN[3..4]);
}

/// Each of `syms`, the names of `f` within the boxes of `s`: its set from
/// [`presburger::project_each_boxed`] met with its box, and whether it was refused, by the
/// question as a whole or alone.
fn boxed_names(s: &Scope, f: &Formula, syms: &[Atom]) -> BTreeMap<String, (IntervalSet, bool)> {
    let mut parts: Vec<Formula> = syms
        .iter()
        .map(|a| match a {
            Atom::Sym(n) => presburger::member(a, s.get(n).ints()),
            _ => unreachable!("a name"),
        })
        .collect();
    parts.push(f.clone());
    let got = presburger::project_each_boxed(&Formula::and(parts), syms);
    syms.iter()
        .zip(got.each)
        .map(|(a, (x, e))| {
            let Atom::Sym(n) = a else {
                unreachable!("a name")
            };
            (n.to_string(), (s.get(n).ints().meet(&x), e.is_some()))
        })
        .collect()
}

/// `items` and `bs` with each name `n` written `to[n]`.
fn renamed(
    items: &[Item],
    bs: &BTreeMap<String, Vec<Piece>>,
    to: &BTreeMap<String, String>,
) -> (Vec<Item>, BTreeMap<String, Vec<Piece>>) {
    let cmp = |c: &Cmp| Cmp {
        terms: c.terms.iter().map(|(n, k)| (to[n].clone(), *k)).collect(),
        ..c.clone()
    };
    let items = items
        .iter()
        .map(|i| match i {
            Item::Con(c) => Item::Con(cmp(c)),
            Item::Ne(c) => Item::Ne(cmp(c)),
            Item::Or(arms) => Item::Or(arms.iter().map(|a| a.iter().map(cmp).collect()).collect()),
        })
        .collect();
    let bs = bs.iter().map(|(n, p)| (to[n].clone(), p.clone())).collect();
    (items, bs)
}

/// The names of `bs` in order, each written `v{i}` with `i` counting down from the last, so
/// renaming reverses the order of the names.
fn reversing(bs: &BTreeMap<String, Vec<Piece>>) -> BTreeMap<String, String> {
    let n = bs.len();
    bs.keys()
        .enumerate()
        .map(|(i, k)| (k.clone(), format!("v{}", n - 1 - i)))
        .collect()
}

/// The sets of [`boxed_names`] for `items` within `bs` as written and with the names reversed
/// ([`reversing`]), each name of the second read back as the first; `Err` with both where they
/// differ.
#[allow(clippy::type_complexity)]
fn boxed_as_named(
    items: &[Item],
    bs: &BTreeMap<String, Vec<Piece>>,
    f: &Formula,
) -> Result<BTreeMap<String, (IntervalSet, bool)>, String> {
    let s = scope(bs);
    let want = boxed_names(&s, f, &item_names(items));
    let to = reversing(bs);
    let (items2, bs2) = renamed(items, bs, &to);
    let back: BTreeMap<&String, &String> = to.iter().map(|(k, v)| (v, k)).collect();
    let got: BTreeMap<String, (IntervalSet, bool)> =
        boxed_names(&scope(&bs2), &formula(&items2), &item_names(&items2))
            .into_iter()
            .map(|(n, x)| (back[&n].clone(), x))
            .collect();
    if got == want {
        Ok(want)
    } else {
        Err(format!("as written {want:?}\n  renamed {got:?}"))
    }
}

/// `[l,h l,h]` as printed by [`show`], as a set.
fn shown_set(text: &str) -> IntervalSet {
    let end = |s: &str, inf: End| match s {
        "-inf" | "inf" => inf,
        v => End::Fin(Num::from(v.parse::<i64>().expect("a bound"))),
    };
    let inner = (text.strip_prefix('[').and_then(|t| t.strip_suffix(']'))).expect("brackets");
    inner
        .split(' ')
        .filter(|p| !p.is_empty())
        .fold(IntervalSet::empty(), |acc, p| {
            let (l, h) = p.split_once(',').expect("a piece");
            acc.join(&IntervalSet::range(
                end(l, End::NegInf),
                end(h, End::PosInf),
            ))
        })
}

/// The answer of [`boxed_names`] for case 272 of seed 17, each name's set and `!` where it
/// was refused.
const ROW_BOXES: &str = "a=[2,3] b=[-4,16]! c=[-3,6] z0=[-6,-4] z1=[-7,13]! z2=[-10,6]!";

/// [`boxed_names`] of `g`, case 272 of seed 17 written another way, as [`ROW_BOXES`] shows it.
fn row_boxes(g: &Formula) -> String {
    let (items, bs) = (parse(WRITTEN[3].0), boxes(WRITTEN[3].1));
    shown_boxes(&boxed_names(&scope(&bs), g, &item_names(&items)))
}

/// Each name's set and `!` where it was refused, as [`ROW_BOXES`] shows them.
fn shown_boxes(got: &BTreeMap<String, (IntervalSet, bool)>) -> String {
    let shown: Vec<String> = got
        .iter()
        .map(|(n, (x, refused))| format!("{n}={}{}", show(x), if *refused { "!" } else { "" }))
        .collect();
    shown.join(" ")
}

/// Case 272 of seed 17 (`WRITTEN`), which the solver refuses with four live variables or more
/// (`Refusal::Growth`), within its boxes: `b`, `z1` and `z2` keep the bounds of the box stage
/// over its rows, `b` narrower than its box, and each holds the exact hull that brute force
/// finds; `c`, refused until item PRES-project-each-cost with the box stage's `[-3,6]`, is now
/// answered, with that exact hull. The answer is the same with the names reversed; for other
/// writings see [`refused_projections_keep_the_box_of_their_rows_in_each_writing`],
/// [`refused_projections_keep_the_box_of_their_rows_in_rewritten_writings`] and
/// [`refused_projections_keep_the_box_of_their_rows_in_scaled_writings`] (one test took 2 s).
#[test]
fn refused_projections_keep_the_box_of_their_rows() {
    let (part, bx, _) = WRITTEN[3];
    let items = parse(part);
    let bs = boxes(bx);
    let want = boxed_as_named(&items, &bs, &formula(&items)).expect("one answer");
    assert_eq!(shown_boxes(&want), ROW_BOXES);
    let exact = brute(&items, &bs, WIDE, false);
    assert_eq!(
        exact
            .iter()
            .map(|(n, (h, _))| format!("{n}={h}"))
            .collect::<Vec<_>>()
            .join(" "),
        "a=[2,3] b=[-4,15] c=[-3,6] z0=[-6,-4] z1=[-7,6] z2=[-6,6]"
    );
    for (n, (h, _)) in &exact {
        let h = shown_set(h);
        assert_eq!(want[n].0.meet(&h), h, "the box of {n} holds the exact hull");
    }
}

/// [`refused_projections_keep_the_box_of_their_rows`] in each writing of [`four_ways`].
#[test]
fn refused_projections_keep_the_box_of_their_rows_in_each_writing() {
    for (how, g) in four_ways(&parse(WRITTEN[3].0)) {
        assert_eq!(row_boxes(&g), ROW_BOXES, "{how}: {g}");
    }
}

/// [`refused_projections_keep_the_box_of_their_rows`] in four random writings by [`rewritten`],
/// two of them with rows split.
#[test]
fn refused_projections_keep_the_box_of_their_rows_in_rewritten_writings() {
    let items = parse(WRITTEN[3].0);
    let mut r = Rng::new(0x272);
    let writings = [false, true, false, true].map(|split| rewritten(&mut r, &items, split));
    for g in writings {
        assert_eq!(row_boxes(&g), ROW_BOXES, "{g}");
    }
}

/// [`refused_projections_keep_the_box_of_their_rows`] in two random writings by [`scaled`].
#[test]
fn refused_projections_keep_the_box_of_their_rows_in_scaled_writings() {
    let items = parse(WRITTEN[3].0);
    let mut rs = Rng::new(0x5ca1e);
    for g in (0..2).map(|_| scaled(&mut rs, &items)) {
        assert_eq!(row_boxes(&g), ROW_BOXES, "{g}");
    }
}

/// Counts of the parts with a refused name, of the refused names, and of those narrower than
/// their box.
type RefusedCount = (usize, usize, usize);

/// Checks the names of `items` within `bs` that the solver refuses, where it refuses one: each
/// keeps a set that holds its exact hull (`hulls`, asked only then), the same with the names
/// reversed ([`boxed_as_named`]), in each writing of [`four_ways`], and in other orders of the
/// parts and of the names: reversed, two random orders drawn from `order`, and a random
/// writing of [`rewritten`], so that a box whose answer depends on the order of the rows is
/// caught. Adds to `count`, and describes each mismatch, under `label`, in `wrong`.
fn check_refused(
    label: &str,
    order: &mut Rng,
    items: &[Item],
    bs: &BTreeMap<String, Vec<Piece>>,
    hulls: impl FnOnce() -> BTreeMap<String, IntervalSet>,
    count: &mut RefusedCount,
    wrong: &mut Vec<String>,
) {
    let s = scope(bs);
    let syms = item_names(items);
    let f = formula(items);
    let got = boxed_names(&s, &f, &syms);
    if !got.values().any(|(_, refused)| *refused) {
        return;
    }
    count.0 += 1;
    if let Err(e) = boxed_as_named(items, bs, &f) {
        wrong.push(format!("{label}: {f}\n  {e}"));
    }
    for (how, g) in four_ways(items).into_iter().skip(1) {
        let other = boxed_names(&s, &g, &syms);
        if other != got {
            wrong.push(format!(
                "{label}: {f}\n  {how}: {g}\n  {got:?}\n  {other:?}"
            ));
        }
    }
    let mut reordered = vec![(
        "reversed",
        items.iter().rev().cloned().collect::<Vec<_>>(),
        syms.iter().rev().cloned().collect::<Vec<_>>(),
    )];
    for _ in 0..2 {
        let (mut is, mut ss) = (items.to_vec(), syms.clone());
        shuffle(order, &mut is);
        shuffle(order, &mut ss);
        reordered.push(("shuffled", is, ss));
    }
    let mut writings: Vec<(&str, Formula, Vec<Atom>)> = (reordered.into_iter())
        .map(|(how, is, ss)| (how, formula(&is), ss))
        .collect();
    writings.push(("rewritten", rewritten(order, items, false), syms.clone()));
    for (how, g, ss) in writings {
        let other = boxed_names(&s, &g, &ss);
        if other != got {
            wrong.push(format!(
                "{label}: {f}\n  {how}: {g}\n  {got:?}\n  {other:?}"
            ));
        }
    }
    let hulls = hulls();
    for (n, (x, refused)) in &got {
        if !*refused {
            continue;
        }
        count.1 += 1;
        if x != s.get(n).ints() {
            count.2 += 1;
        }
        let h = &hulls[n];
        if x.meet(h) != *h {
            wrong.push(format!(
                "{label}: {f}\n  boxes {bs:?}\n  {n} = {} misses {}",
                show(x),
                show(h)
            ));
        }
    }
}

/// Each name's hull from [`brute`].
fn brute_hulls(items: &[Item], bs: &BTreeMap<String, Vec<Piece>>) -> BTreeMap<String, IntervalSet> {
    brute(items, bs, WIDE, false)
        .into_iter()
        .map(|(n, (h, _))| (n, shown_set(&h)))
        .collect()
}

/// [`check_refused`] on `cases` random parts drawn from `seed`, with `double` each part two
/// random parts over the same names joined (more rows, so more refusals), the hulls by brute
/// force. Each case draws its orders from a sequence of its own, so a case of a seed checks
/// the same orders whichever cases before it are checked.
fn refused_names_in(seed: u64, cases: usize, double: bool) -> RefusedCount {
    let mut count = (0, 0, 0);
    let mut wrong = Vec::new();
    let mut r = Rng::new(seed);
    for case in 0..cases {
        let (items, bs) = next_case(&mut r, double);
        let mut order = Rng::new(0x0de5 ^ seed ^ ((case as u64) << 32));
        let label = format!("seed {seed} case {case}");
        let hulls = || brute_hulls(&items, &bs);
        check_refused(
            &label, &mut order, &items, &bs, hulls, &mut count, &mut wrong,
        );
    }
    assert!(
        wrong.is_empty(),
        "seed {seed}: {} wrong:\n{}",
        wrong.len(),
        wrong.join("\n")
    );
    count
}

/// Random parts, each within random boxes, checked by [`refused_names_in`] from a new seed
/// each run. Seeds 11 to 18 at 400 parts each (item PROJECT-each-canon) took 9 to 13 s;
/// two of their parts are refused (seeds 16 and 17), and one is kept as
/// [`a_refused_part_keeps_a_sound_box`]. Item PRES-small-point answers one name refused
/// before, `c` of seed 13 case 264,
/// `(a + b + 2 * c >= 2 || z0 <= 6) && a + c >= -9 && a + b + z1 == c - 6` within
/// `b >= -6`, `-1 <= z0 <= 8`, `z1 >= -4`, with the hull brute force finds, `c >= -6`. Items
/// PERF-l139-family and PRES-project-each-cost answer the last names refused with the hulls
/// brute force finds.
#[test]
fn refused_projections_of_random_parts_keep_sound_boxes() {
    let (_, seed) = Rng::fresh("refused projections of random parts");
    let count = refused_names_in(seed, 100, false);
    eprintln!("{count:?} (parts refused, names refused, names narrower than the box)");
}

/// As [`refused_projections_of_random_parts_keep_sound_boxes`], with each part two random
/// parts joined. Seeds 11 and 12 at 400 parts each counted (7, 30, 14) and took 15 s, most of
/// it in a few refused parts of up to 3 s each; one of them is kept as
/// [`a_refused_joined_part_keeps_a_sound_box`].
#[test]
fn refused_projections_of_joined_random_parts_keep_sound_boxes() {
    let (_, seed) = Rng::fresh("refused projections of joined random parts");
    let count = refused_names_in(seed, 25, true);
    eprintln!("{count:?} (parts refused, names refused, names narrower than the box)");
}

/// The next random part of `r` and its boxes, as [`refused_names_in`] draws them.
fn next_case(r: &mut Rng, double: bool) -> (Vec<Item>, BTreeMap<String, Vec<Piece>>) {
    let nz = 2 + r.below(5);
    let mut items = random_part(r, nz);
    if double {
        items.extend(random_part(r, nz));
    }
    let bs = random_boxes(r, nz);
    (items, bs)
}

/// The part `case` of `seed` and its boxes, drawn as [`refused_names_in`] draws them.
fn random_case(seed: u64, case: usize, double: bool) -> (Vec<Item>, BTreeMap<String, Vec<Piece>>) {
    let mut r = Rng::new(seed);
    for _ in 0..case {
        next_case(&mut r, double);
    }
    next_case(&mut r, double)
}

/// [`check_refused`] on part `case` of `seed`: `want` counts its refused names and those
/// narrower than their box.
fn check_refused_case(seed: u64, case: usize, double: bool, want: RefusedCount) {
    let (items, bs) = random_case(seed, case, double);
    let mut order = Rng::new(0x0de5 ^ seed ^ ((case as u64) << 32));
    let (mut count, mut wrong) = ((0, 0, 0), Vec::new());
    let hulls = || brute_hulls(&items, &bs);
    check_refused("", &mut order, &items, &bs, hulls, &mut count, &mut wrong);
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    assert_eq!(count, want, "seed {seed} case {case}");
}

/// Case 102 of seed 16: of its 7 names refused, 6 are narrower than their box, each holding
/// the hull brute force finds, `a=[2,5] b=[17,23] c=[7,8] z0=[-80,inf] z1=[-15,-9]
/// z2=[35,51] z3=[-69,1]`.
#[test]
fn a_refused_part_keeps_a_sound_box() {
    check_refused_case(16, 102, false, (1, 7, 6));
}

/// Case 296 of seed 12, each part two joined: of its 6 names refused, 2 are narrower than
/// their box, each holding the hull brute force finds, `a=[12,16] b=[-5,-4] c=[4,6]
/// z0=[-25,-20] z1=[-1,8] z2=[4,6]`.
#[test]
fn a_refused_joined_part_keeps_a_sound_box() {
    check_refused_case(12, 296, true, (1, 6, 2));
}

/// Names of random parts of seeds 11 to 18, not refused, whose hulls were wider than brute
/// force finds (item PRES-pendants-wider), each now that hull: `a` and `z2` by the rows that
/// the rows of a projection give each other (`2·a + z2 + 15 >= 0` with `a <= 7`), `z0` of
/// seed 17 and `z3` by the rows the disjunctions imply with an end the hull left infinite,
/// `z0` of seed 14 by a search of a finite end whose other end is infinite, and `z1` by a
/// candidate end a disjunct gives (`z1 <= 6`, where `z1 >= 7` leaves three disjuncts that
/// hold together at no point).
#[test]
fn hulls_once_wider_than_brute_force_are_its_hulls() {
    for (seed, case, name, want) in [
        (16, 8, "a", "[3,inf]"),
        (15, 331, "z2", "[-29,inf]"),
        (17, 121, "z0", "[-21,-4]"),
        (16, 214, "z3", "[-7,29]"),
        (14, 271, "z0", "[-inf,25]"),
        (11, 226, "z1", "[-3,6]"),
    ] {
        let (items, bs) = random_case(seed, case, false);
        let got = boxed_names(&scope(&bs), &formula(&items), &item_names(&items));
        let (x, refused) = &got[name];
        assert!(!refused, "seed {seed} case {case} {name}");
        assert_eq!(show(x), want, "seed {seed} case {case} {name}");
        assert_eq!(
            brute_hulls(&items, &bs)[name],
            *x,
            "seed {seed} case {case} {name}"
        );
    }
}

/// A random part, its boxes, and six other writings of it with the same points: four by
/// [`rewritten`] (its equations negated or held twice with opposite signs, its inequalities
/// held twice, some equations split into two inequalities, with `split`) and two by
/// [`scaled`] (each constraint with a common factor), each with its items, arms and
/// constraints in a random order.
struct Rewrites {
    case: usize,
    items: Vec<Item>,
    bs: BTreeMap<String, Vec<Piece>>,
    rewrites: Vec<Formula>,
}

/// `cases` random parts drawn from `seed` and their rewrites ([`Rewrites`]). The scaled
/// writings draw from a sequence of their own (`seed` ^ 0x5ca1e), so the parts and their other
/// writings are those of `seed` alone.
fn random_rewrites(seed: u64, cases: usize) -> Vec<Rewrites> {
    let mut r = Rng::new(seed);
    let mut rs = Rng::new(seed ^ 0x5ca1e);
    (0..cases)
        .map(|case| {
            let nz = 2 + r.below(5);
            let items = random_part(&mut r, nz);
            let bs = random_boxes(&mut r, nz);
            let mut rewrites: Vec<Formula> = [false, false, true, true]
                .into_iter()
                .map(|split| rewritten(&mut r, &items, split))
                .collect();
            rewrites.extend((0..2).map(|_| scaled(&mut rs, &items)));
            Rewrites {
                case,
                items,
                bs,
                rewrites,
            }
        })
        .collect()
}

/// Random parts, each also written six other ways ([`random_rewrites`]), from a new seed each
/// run: the projection of the whole part is the same as for the part as written, and so is
/// the projection by pendants wherever both writings take it. `Scope::project_by_pendants`
/// takes its route by the structure of the part alone, so one writing may take it and another
/// not: a part folded to `false`, or `x == y` written as `x <= y && x >= y`, or a sum scaled
/// (2076 seeds of 10 parts: 163 rewrites, 15 of them with a point, where each route taken gave
/// the boxes of the whole). Seed 0xca17 at 300 parts took 14 s; 10 parts take about 0.5 s.
#[test]
fn rewritten_parts_give_one_answer() {
    let (_, seed) = Rng::fresh("rewritten parts give one answer");
    let mut wrong = Vec::new();
    let mut n = 0;
    for Rewrites {
        case,
        items,
        bs,
        rewrites,
    } in random_rewrites(seed, 10)
    {
        let s = scope(&bs);
        let syms = item_names(&items);
        let f = formula(&items);
        let want = (each_answer(&s, &f, &syms), hung(&s, &f));
        for g in rewrites {
            n += 1;
            let got = (each_answer(&s, &g, &syms), hung(&s, &g));
            let both_hung = want.1.is_some() && got.1.is_some();
            if got.0 != want.0 || (both_hung && got.1 != want.1) {
                wrong.push(format!(
                    "case {case}\n  {f}\n  {g}\n  boxes {bs:?}\n  want {want:?}\n  got  {got:?}"
                ));
            }
        }
    }
    assert!(
        wrong.is_empty(),
        "seed {seed}: {} of {n} rewrites differ:\n{}",
        wrong.len(),
        wrong.join("\n")
    );
}

/// Whether `f` within the boxes of `s` has a point, as `presburger::decide` and
/// `presburger::satisfiable` answer, refusals included.
fn decided(s: &Scope, f: &Formula, syms: &[Atom]) -> String {
    let mut parts: Vec<Formula> = syms
        .iter()
        .map(|a| match a {
            Atom::Sym(n) => presburger::member(a, s.get(n).ints()),
            _ => unreachable!("a name"),
        })
        .collect();
    parts.push(f.clone());
    let f = Formula::and(parts);
    format!(
        "decide {:?}, satisfiable {:?}",
        presburger::decide(&f),
        presburger::satisfiable(&f).map(|m| m.is_some())
    )
}

/// The parts of [`rewritten_parts_give_one_answer`], each written seven ways, with duplicate,
/// negated, split and scaled rows and in other orders, from a new seed each run: `decide` and
/// `satisfiable` give each the same answer, refusals included (item PROJECT-canon-decide).
/// Seed 0xca17 at 300 parts took 1.7 s; 60 parts take about 0.4 s.
#[test]
fn rewritten_parts_are_decided_alike() {
    let (_, seed) = Rng::fresh("rewritten parts are decided alike");
    let mut wrong = Vec::new();
    let mut n = 0;
    for Rewrites {
        case,
        items,
        bs,
        rewrites,
    } in random_rewrites(seed, 60)
    {
        let s = scope(&bs);
        let syms = item_names(&items);
        let f = formula(&items);
        let want = decided(&s, &f, &syms);
        for g in rewrites {
            n += 1;
            let got = decided(&s, &g, &syms);
            if got != want {
                wrong.push(format!(
                    "case {case}\n  {f}\n  {g}\n  boxes {bs:?}\n  want {want}\n  got  {got}"
                ));
            }
        }
    }
    assert!(
        wrong.is_empty(),
        "seed {seed}: {} of {n} rewrites differ:\n{}",
        wrong.len(),
        wrong.join("\n")
    );
}

/// Case 14 of seed 0xca17 with its equation written with a common factor,
/// `2 * b + 2 * c + 2 * z4 == -16` for `b + c + z4 == -8`, and an inequality with one and
/// a constant below it added, `2 * z0 >= 2 * z3 + 5` for `z0 >= z3 + 3`: both projections
/// give the answer of the rows divided by it, where the projection by pendants, which reads
/// a pendant's coefficient, declined before (item PROJECT-canon-gcd). And an equation whose
/// constant the factor does not divide, `2 * b == 2 * c + 1`, leaves no point.
#[test]
fn rows_with_a_common_factor_give_the_answer_of_the_rows_divided_by_it() {
    let part = "!(b + z1 == c + 7) && 2 * b + c + z0 >= -10 && b + c + z4 == -8 && z0 >= z3 + 3";
    let bx = "b=[0,7] c=[-inf,-6] z0=[-6,7] z1=[-5,-3] z3=[-inf,inf] z4=[-10,inf]";
    let want = "b=[0,7] c=[-31,-6] z0=[-6,7] z1=[-5,-3] z3=[-inf,4] z4=[-9,16] left out: []";
    let factored = part
        .replace("b + c + z4 == -8", "2 * b + 2 * c + 2 * z4 == -16")
        .replace("z0 >= z3 + 3", "2 * z0 >= 2 * z3 + 5");
    assert_ne!(factored, part);
    let by_pendants: BTreeMap<String, String> = bracketed(want)
        .into_iter()
        .map(|(n, x)| (n, format!("[{x}]")))
        .collect();
    for text in [part, &factored] {
        let (each, hung) = written_four_ways(text, bx);
        assert_eq!(each, want, "{text}");
        assert_eq!(hung.as_ref(), Some(&by_pendants), "{text}");
    }
    let odd = format!("{part} && 2 * b == 2 * c + 1");
    let (each, _) = written_four_ways(&odd, bx);
    assert_eq!(
        each, "b=[] c=[] z0=[] z1=[] z3=[] z4=[] left out: []",
        "{odd}"
    );
}

// FAIL-product-refused-box-renamed, found by TEST-complete-preimage (author P189) in an
// instrumented run of l01_39_reduced_product. Append this test to
// tests/steps/l01_39_reduced_product/pendants.rs (it uses `refused_names_in` there). Case 11 of
// seed 6277671696228035587 is the part
//   2 * a + b + z2 >= 5 && a + 2 * b + c >= z1 - 12 && a + b + c + z1 >= 4
//   && 2 * a + b + c == z2 - 4 && 2 * b + c >= -5 && a + b == c + z0 - 5
//   && a + z1 >= c - 10 && a + 2 * b + 2 * c >= -5 && 2 * b + 2 * c + z2 >= 1
// within its random boxes. As written, the solver refuses `z2` and keeps the box [6..=10];
// with the names renamed it projects `z2` to [6..=7], not refused. The other names agree
// (a = -3, b = 5, c in [3..=4], z0 in [3..=4], z1 in [1..=13]). The answer depends on the
// names, so batch and single-file checking can disagree. Expected: one box for `z2` however
// the names are spelled; [6..=7] holds the hull, since 2a + b + c == z2 - 4 with a = -3,
// b = 5 and c in [3..=4] gives z2 in [6..=7].

/// Case 11 of seed 6277671696228035587 gives one box for each name however the names are
/// spelled (cases 0 to 10 of the seed pass).
#[test]
fn a_refused_box_does_not_depend_on_the_names_seed_6277671696228035587() {
    refused_names_in(6277671696228035587, 12, false);
}

/// Case 10 of seed 15900465239627589939, parts within two boxes each, gives one box for each
/// name however the names are spelled: written so, the solver refused all seven names, and
/// with the names reversed it projected each, because each equation was signed by its first
/// coefficient in name order. The sign is now chosen by the structure of the part.
#[test]
fn a_refused_box_does_not_depend_on_the_names_seed_15900465239627589939() {
    refused_names_in(15900465239627589939, 11, true);
}

/// Seed 8203920530908347152 of [`rewritten_parts_give_one_answer`]
/// (FAIL-pendants-rewrite-empty-seed): case 5, a part with no point whose rows
/// `a + b >= 2 * c + z2 + 10`, `a + b <= 2 * c + z2 + 10` and `a + b == 2 * c + z2 - 3`
/// `Formula::and` folds to `false` as written. By pendants the part as written gave the empty
/// map, naming none of its names, and three of its rewrites a map of each name empty; a part
/// folded to `false` no longer takes the route.
#[test]
fn rewritten_parts_of_seed_8203920530908347152_give_one_answer() {
    let seed = 8203920530908347152u64;
    let mut wrong = Vec::new();
    for Rewrites {
        case,
        items,
        bs,
        rewrites,
    } in random_rewrites(seed, 10)
    {
        let s = scope(&bs);
        let syms = item_names(&items);
        let f = formula(&items);
        let want = (each_answer(&s, &f, &syms), hung(&s, &f));
        for g in rewrites {
            let got = (each_answer(&s, &g, &syms), hung(&s, &g));
            let both_hung = want.1.is_some() && got.1.is_some();
            if got.0 != want.0 || (both_hung && got.1 != want.1) {
                wrong.push(format!(
                    "case {case}\n  {g}\n  want {want:?}\n  got  {got:?}"
                ));
            }
        }
    }
    assert!(wrong.is_empty(), "seed {seed}:\n{}", wrong.join("\n"));
}

/// A part `Formula::and` folds to `false` (one sum equal to 1 and to 2) names no name, so
/// the route by pendants is not taken on it: an empty map would leave out the names its
/// other writings empty.
#[test]
fn a_part_folded_to_false_does_not_take_the_route() {
    let s = scope(&boxes("a=[-5,5] b=[-5,5] c=[-5,5]"));
    let f = formula(&parse("a + b == c + 1 && a + b == c + 2 && a >= b"));
    assert_eq!(f, Formula::bottom(), "{f}");
    assert_eq!(hung(&s, &f), None);
}

/// Part 23 of seed 1541603418123298951 of the projection by pendants against that of the
/// whole part (FAIL-pendants-rewrite-empty-seed): its one pendant `b <= c + z2 - 5`, `z2`
/// unbounded above, takes the shortcut of an unbounded unit sum, and the rows left have no
/// point (`a + c + z0` is 3 and 6). By pendants it named only `b`, `c` and `z2` empty, the names
/// of the pendant; each name of the part is empty, as in the projection of the whole part.
#[test]
fn an_empty_part_by_the_unbounded_shortcut_empties_each_of_its_names() {
    let part = "b <= c + z2 - 5 && 3 == a + c + z0 && a + c == z0 + 4 && a + c + z0 == 6 \
        && 2 * a + 2 * b + z0 >= -9 && (2 * b >= c - 6 || z0 <= 6) && a >= b - 6 \
        && 2 * a + c + z0 >= 0";
    let s = scope(&boxes(
        "a=[-10,-8] b=[-7,-7] c=[3,inf] z0=[-inf,0] z1=[-inf,-10] z2=[-inf,inf] z3=[1,inf]",
    ));
    let f = formula(&parse(part));
    let empty: BTreeMap<String, String> = ["a", "b", "c", "z0", "z2"]
        .into_iter()
        .map(|n| (n.to_string(), "[]".to_string()))
        .collect();
    assert_eq!(hung(&s, &f), Some(empty.clone()), "{f}");
    assert_eq!(whole(&s, &f), Some(empty), "{f}");
}

/// Parts that take the shortcut of an unbounded unit sum, `z2` unbounded above in the pendant
/// `b <= c + z2 - 5`, and whose rows left have a point: the names the shortcut answers are
/// those of the projection of the whole part, with at least one not empty.
#[test]
fn a_part_with_a_point_by_the_unbounded_shortcut_is_projected_as_the_whole() {
    for (bx, part) in [
        (
            "b=[-7,-7] c=[3,inf] z2=[-inf,inf]",
            "b <= c + z2 - 5 && (2 * b >= c - 6 || c >= 10)",
        ),
        (
            "b=[-7,inf] c=[3,inf] z2=[-inf,inf]",
            "b <= c + z2 - 5 && b + c >= 0 && (c <= 20 || c >= 30)",
        ),
        (
            "b=[0,9] c=[-inf,4] z2=[0,inf]",
            "b <= c + z2 - 5 && (b >= c + 3 || c <= -2)",
        ),
    ] {
        let s = scope(&boxes(bx));
        let f = formula(&parse(part));
        let got = hung(&s, &f).expect("taken");
        assert!(got.values().any(|d| d != "[]"), "{part}: {got:?}");
        assert_eq!(Some(got), whole(&s, &f), "{part}");
    }
}

/// The seeds on which a fixed 120 parts compared fewer than a quarter of them
/// (FAIL-pendants-route-quarter-seed), no part differing: 4023886734010713935 compared 28,
/// 11312057540586612196 compared 26 and 6901888717729865865 compared 24. Drawn until
/// [`PENDANT_COMPARED`] are compared, each reaches the count.
#[test]
fn the_seeds_that_compared_too_few_parts_reach_the_count() {
    for seed in [
        4023886734010713935,
        11312057540586612196,
        6901888717729865865,
    ] {
        pendants_against_whole(Rng::new(seed), seed);
    }
}
