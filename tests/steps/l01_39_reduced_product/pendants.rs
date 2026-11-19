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
use zed_tests::step_helpers::l01_38_presburger::solver_alone;
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

/// What [`points`] finds within the range of the hubs: the hull of each name and the exact
/// set of its values taken there (for a `z` its hull again unless asked for), or `None` where
/// there is no point.
type Found = Option<BTreeMap<String, (IntervalSet, IntervalSet)>>;

/// Over the integer points of `cons` within `boxes` (one piece each), what [`Found`] holds,
/// with the hubs (the names other than `z1`, `z2`, ...) enumerated within their boxes and
/// `-far..=far`. Each `z` is mentioned with coefficient one or minus one, at most two to a
/// constraint and then with opposite signs, so for the hubs' values the `z` constraints are
/// integer difference constraints, which shortest paths from a source solve exactly: each
/// `z` takes every integer from minus its distance to the source to its distance from it. An
/// unbounded end is `End::NegInf` or `End::PosInf`. Every value found is taken; a finite end
/// found may lie short of the name's end, which [`brute`] decides.
///
/// Each `z` keeps the least and greatest end it took, its exact set of values only with
/// `exact`. Two passes, and a set of the ranges of each `z` added to at every point, took 15 s
/// over the 24 rows of [`REFUSED`] (TEST-bench-move-l0139). It is still `O(far^hubs · z^3)`,
/// as a brute force is.
fn points(cons: &[Cmp], boxes: &BTreeMap<String, Piece>, far: i64, exact: bool) -> Found {
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
    // Each hub within its box, `-far..=far`, and the floor and ceiling of its greatest and
    // least value at the rational points of `cons` ([`lp_max`]): a hub value outside those
    // has no integer point, so it would fail the hubs' rows or close a negative cycle below,
    // and leaving it out changes nothing found.
    //
    // Complexity tradeoff: the hubs' ranges as `-far..=far` within their boxes alone visit up
    // to 151^3 hub points per disjunct, each with an `O(z^3)` closure; two [`lp_max`] per hub
    // (a few pivots each) first cut the ranges to what the rows allow. Measured on seeds 214
    // and 509 of the joined parts (PERF-pendants-joined-slow-seeds; see COMPLEXITY.md).
    let rows = lp_rows(cons, boxes);
    let unit = |m: &str, s: i64| -> Vec<i64> {
        boxes.keys().map(|x| if x == m { s } else { 0 }).collect()
    };
    let at_most = |m: &str, s: i64, bound: i64| match lp_max(&rows, &unit(m, s)) {
        Lp::Max(g) => g.to_i64().map_or(bound, |g| g.min(bound)),
        Lp::Empty => -far - 1,
        Lp::Unbounded => bound,
    };
    let ranges: Vec<(i64, i64)> = hubs
        .iter()
        .map(|h| {
            let (lo, hi) = boxes[*h];
            let (lo, hi) = (
                lo.map_or(-far, |l| l.max(-far)),
                hi.map_or(far, |h| h.min(far)),
            );
            (-at_most(h, -1, -lo), at_most(h, 1, hi))
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
    let mut hub_seen: Vec<Vec<bool>> = ranges
        .iter()
        .map(|(l, h)| vec![false; (h - l + 1).max(0) as usize])
        .collect();
    let mut z_hull: Vec<Option<(i64, i64)>> = vec![None; zs.len()];
    let mut z_seen: Vec<HashSet<(i64, i64)>> = vec![HashSet::new(); zs.len()];
    let mut v = vec![0i64; hubs.len()];
    // The distances, row `i` at `d[i * size..]`, and the edges of the boxes of the `z`, the
    // same at every point: found once here, not by name at each point, which with the
    // distances as a vector of rows took a third of the time of seed 509 of the joined parts
    // (PERF-pendants-joined-slow-seeds).
    let mut d = vec![INF; size * size];
    let z_edges: Vec<(usize, usize, i64)> = (zs.iter().enumerate())
        .flat_map(|(i, z)| {
            let (l, h) = boxes[*z];
            [l.map(|l| (i, src, -l)), h.map(|h| (src, i, h))]
        })
        .flatten()
        .collect();
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
        d.fill(INF);
        for i in 0..size {
            d[i * size + i] = 0;
        }
        let mut edge = |from: usize, to: usize, w: i64| {
            let e = &mut d[from * size + to];
            *e = (*e).min(w);
        };
        for (hub, plus, minus, c, eq) in &on_zs {
            // `plus - minus + c0 >= 0` is `minus - plus <= c0`: an edge from `plus` to
            // `minus` of weight `c0`, and for an equation one back of weight `-c0`.
            let c0 = at_hubs(hub, *c, &v);
            edge(*plus, *minus, c0);
            if *eq {
                edge(*minus, *plus, -c0);
            }
        }
        for &(from, to, w) in &z_edges {
            edge(from, to, w);
        }
        // Floyd and Warshall's closure, a row `i` with no path to `k` skipped whole.
        for k in 0..size {
            for i in 0..size {
                let ik = d[i * size + k];
                if ik >= INF {
                    continue;
                }
                for j in 0..size {
                    let kj = d[k * size + j];
                    if kj < INF && ik + kj < d[i * size + j] {
                        d[i * size + j] = ik + kj;
                    }
                }
            }
        }
        if (0..size).any(|i| d[i * size + i] < 0) {
            continue;
        }
        for (i, (l, _)) in ranges.iter().enumerate() {
            hub_seen[i][(v[i] - l) as usize] = true;
        }
        for (i, h) in z_hull.iter_mut().enumerate() {
            let (lo, hi) = (-d[i * size + src], d[src * size + i]);
            *h = Some(h.map_or((lo, hi), |(l, u)| (l.min(lo), u.max(hi))));
            if exact {
                z_seen[i].insert((lo, hi));
            }
        }
    }
    // The union of the ranges, and its hull, which is the hull of the hulls taken one at a
    // time.
    let mut seen: Vec<Vec<(i64, i64)>> = (hub_seen.iter().zip(&ranges))
        .map(|(taken, (l, _))| {
            let at = taken.iter().enumerate().filter(|(_, t)| **t);
            at.map(|(j, _)| (l + j as i64, l + j as i64)).collect()
        })
        .collect();
    seen.extend(z_seen.iter().zip(&z_hull).map(|(s, h)| {
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
}

/// The rational points of `cons` within `boxes` as rows `(a, b)`, each `a · x <= b`, over the
/// names of `boxes` in order.
fn lp_rows(cons: &[Cmp], boxes: &BTreeMap<String, Piece>) -> Vec<(Vec<i64>, i64)> {
    let names: Vec<&String> = boxes.keys().collect();
    let k = names.len();
    let col = |m: &str| {
        names
            .iter()
            .position(|x| *x == m)
            .expect("a name with a box")
    };
    let mut rows = Vec::new();
    for c in cons {
        let mut a = vec![0i64; k];
        for (m, x) in &c.terms {
            a[col(m)] = *x;
        }
        // `a · x + constant >= 0` is `-a · x <= constant`; an equation is also
        // `a · x <= -constant`.
        rows.push((a.iter().map(|x| -x).collect(), c.constant));
        if c.eq {
            rows.push((a, -c.constant));
        }
    }
    for (i, (lo, hi)) in boxes.values().enumerate() {
        let unit = |s: i64| (0..k).map(|j| if j == i { s } else { 0 }).collect();
        if let Some(h) = hi {
            rows.push((unit(1), *h));
        }
        if let Some(l) = lo {
            rows.push((unit(-1), -l));
        }
    }
    rows
}

/// What [`lp_max`] finds of the greatest value of an objective over the rational points of
/// some rows: none, as there is no point; none, as it grows without bound; or the floor of it.
#[derive(Debug)]
enum Lp {
    Empty,
    Unbounded,
    Max(Num),
}

/// The greatest value of `objective · x` over the rational `x` with `a · x <= b` for each row
/// `(a, b)`, by the simplex method, in two phases where some `b` is negative: the auxiliary
/// problem of Chvátal (1983, ch. 3) adds `x0 >= 0` to every row as `a · x - x0 <= b`, pivots it
/// in at the row of least `b`, which makes every right side at least 0, and minimizes it; there
/// is a point where its least value is 0. Each `x` is free, the difference of two columns
/// `u - v`.
///
/// The tableau is kept in integers by integer pivoting (Edmonds 1967; Bareiss 1968; as in
/// lrs, Avis 2000): each entry over the common denominator `den`, the last pivot, and the new
/// entry `(t[p][q] · t[i][j] - t[i][q] · t[p][j]) / den`, which divides exactly since every
/// entry is a minor of the starting tableau. After the one pivot on a negative entry (`x0`
/// entering) every entry and `den` are negated, which leaves each value the same, so `den` is
/// positive and the signs of the entries are those of the values. Bland's rule (the least
/// column of negative reduced cost enters; ties of the ratio test go to the least basic
/// column) ends each phase (Bland 1977). `x0` is column 0, so on a tie it leaves first: its
/// value falls to 0 only on a pivot where its row ties for the least ratio, so phase one,
/// which stops when `x0` leaves, ends with `x0` out of the basis wherever there is a point, and
/// phase two never lets it in. In `Num`, whole numbers of any size, nothing overflows.
///
/// Complexity tradeoff: a brute force over the rational points has no end; the simplex
/// method takes at most C(cols, rows) pivots of `O(rows · cols)` each, in practice a few
/// pivots on the at most 3 + 6 names and some 40 rows of a random part. Fourier-Motzkin
/// elimination of the other names would be shorter to write but can square the rows at each
/// of up to 8 eliminations.
fn lp_max(rows: &[(Vec<i64>, i64)], objective: &[i64]) -> Lp {
    /// Pivots on `t[p][q]`, `p` a constraint row (from 2).
    fn pivot(t: &mut [Vec<Num>], den: &mut Num, basis: &mut [usize], p: usize, q: usize) {
        let pv = t[p][q].clone();
        let (top, rest) = t.split_at_mut(p);
        let (row_p, bottom) = rest.split_first_mut().expect("the pivot row");
        for row in top.iter_mut().chain(bottom.iter_mut()) {
            let f = row[q].clone();
            for (x, y) in row.iter_mut().zip(row_p.iter()) {
                *x = (&(&pv * &*x) - &(&f * y)).div_floor(den);
            }
        }
        *den = pv;
        basis[p - 2] = q;
        if den.signum() < 0 {
            for x in t.iter_mut().flatten() {
                *x = -&*x;
            }
            *den = -&*den;
        }
    }
    /// Runs the simplex method on objective row `obj` over columns `cols`, until no column
    /// enters (`true`), no row bounds the entering column (`false`), or `stop` holds (`true`).
    fn run(
        t: &mut [Vec<Num>],
        den: &mut Num,
        basis: &mut [usize],
        obj: usize,
        cols: std::ops::Range<usize>,
        stop: impl Fn(&[usize]) -> bool,
    ) -> bool {
        let rhs = t[0].len() - 1;
        while !stop(basis) {
            let Some(q) = cols.clone().find(|&j| t[obj][j].signum() < 0) else {
                return true;
            };
            // The ratio test: the least `t[i][rhs] / t[i][q]` over `t[i][q] > 0`, compared by
            // cross products (both positive).
            let mut best: Option<usize> = None;
            for i in 2..t.len() {
                if t[i][q].signum() <= 0 {
                    continue;
                }
                best = Some(best.map_or(i, |b| {
                    let (x, y) = (&t[i][rhs] * &t[b][q], &t[b][rhs] * &t[i][q]);
                    if x < y || (x == y && basis[i - 2] < basis[b - 2]) {
                        i
                    } else {
                        b
                    }
                }));
            }
            let Some(p) = best else {
                return false;
            };
            pivot(t, den, basis, p, q);
        }
        true
    }
    let k = objective.len();
    let m = rows.len();
    // Columns: `x0`, `u` (k), `v` (k), one slack per row, the right side. Row 0 is the
    // objective of phase two, `z - objective · (u - v) = 0`; row 1 that of phase one,
    // `w + x0 = 0`, `w = -x0` maximized; then a row `a · (u - v) - x0 + slack = b` for each row.
    let width = 2 * k + m + 2;
    let rhs = width - 1;
    let num = Num::from;
    let mut t: Vec<Vec<Num>> = vec![vec![num(0); width]; m + 2];
    for (j, c) in objective.iter().enumerate() {
        t[0][1 + j] = num(-c);
        t[0][1 + k + j] = num(*c);
    }
    t[1][0] = num(1);
    for (i, (a, b)) in rows.iter().enumerate() {
        let r = &mut t[i + 2];
        r[0] = num(-1);
        for (j, x) in a.iter().enumerate() {
            r[1 + j] = num(*x);
            r[1 + k + j] = num(-x);
        }
        r[1 + 2 * k + i] = num(1);
        r[rhs] = num(*b);
    }
    let mut basis: Vec<usize> = (0..m).map(|i| 1 + 2 * k + i).collect();
    let mut den = num(1);
    // `min_by_key` gives the first of the least.
    if let Some(p) = (2..m + 2)
        .filter(|&i| t[i][rhs].signum() < 0)
        .min_by_key(|&i| t[i][rhs].clone())
    {
        pivot(&mut t, &mut den, &mut basis, p, 0);
        let out = |b: &[usize]| !b.contains(&0);
        assert!(
            run(&mut t, &mut den, &mut basis, 1, 0..rhs, out),
            "phase one is bounded by 0"
        );
        if !out(&basis) {
            // Optimal with `x0` in the basis, so at a value above 0 (see above).
            assert!(t[1][rhs].signum() < 0, "x0 leaves when it reaches 0");
            return Lp::Empty;
        }
    }
    if !run(&mut t, &mut den, &mut basis, 0, 1..rhs, |_| false) {
        return Lp::Unbounded;
    }
    Lp::Max(t[0][rhs].div_floor(&den))
}

/// A row of [`omega`]: coefficients and constant.
type Row = (Vec<Num>, Num);

/// Whether some integer `x` has `a · x <= b` for each row `(a, b)` ([`omega`]).
fn has_point(rows: &[(Vec<i64>, i64)]) -> bool {
    let row = |(a, b): &(Vec<i64>, i64)| (a.iter().map(|x| Num::from(*x)).collect(), Num::from(*b));
    omega(rows.iter().map(row).collect(), Vec::new())
}

/// Whether some integer `x` has `a · x <= b` for each row `(a, b)` of `le` and `a · x == b` for
/// each of `eq`, by the Omega test (Pugh, "A practical algorithm for exact array dependence
/// analysis", CACM 35(8), 1992), exact for any rows, with no bound on `x`.
///
/// An equation is divided by the gcd of its coefficients (no integer point where that does not
/// divide its constant), then its coefficients are brought to one of `±1` by Euclid's algorithm
/// on columns: `x_i = x_i' - q · x_j'` is a change of variables with an integer inverse, so it
/// maps the integer points one to one, and it turns the coefficient `c_j` of every row into
/// `c_j - q · c_i`. With the one coefficient left `±1`, the equation fixes `x_i`, which is put
/// into every row. An inequality is divided by the gcd of its coefficients, its constant
/// rounded down (the same integer points); of two with the same coefficients the lesser
/// constant is kept, and two of opposite coefficients whose constants add to 0 are an
/// equation. A variable bounded on one side only is dropped with its rows: for any integer
/// values of the others, an integer value of it far enough out meets them all. Otherwise a
/// variable is eliminated by Fourier and Motzkin's real shadow, the combinations
/// `l · upper + u · lower`, which has the same integer points as the projection where each
/// lower bound or each upper bound has coefficient 1; else there are integer points if the dark
/// shadow (each constant less `(l - 1)(u - 1)`) has one, none if the real shadow has none, and
/// otherwise exactly where one of the splinters has one: the equations `l · x_j = L + i` for
/// each lower bound `L <= l · x_j` and `0 <= i <= (l · m - l - m) / m`, `m` the greatest
/// coefficient of an upper bound (Pugh's theorem). Each step leaves out a variable, or adds an
/// equation that then does, so the recursion ends.
///
/// Complexity tradeoff: exponential in the variables in the worst case (each elimination can
/// multiply the rows, each splinter adds a branch), against enumeration within the proven bound
/// `(n + 1) · Δ` on some integer point (Schrijver, Theory of Linear and Integer Programming,
/// cor. 17.1b; `Δ` the greatest subdeterminant), which for the 3 hubs and up to 6 `z` and 40
/// rows of a random part is millions of values per hub. The rows are deduplicated after each
/// step. A test oracle on at most 9 variables.
fn omega(le: Vec<Row>, mut eq: Vec<Row>) -> bool {
    let (zero, one) = (Num::from(0), Num::from(1));
    let gcd = |a: &[Num]| a.iter().fold(Num::from(0), |g, x| g.gcd(x));
    let mut le = le;
    while let Some((mut a, b)) = eq.pop() {
        let g = gcd(&a);
        if g.is_zero() {
            if !b.is_zero() {
                return false;
            }
            continue;
        }
        if !b.mod_floor(&g).is_zero() {
            return false;
        }
        for x in &mut a {
            *x = x.div_floor(&g);
        }
        let b = b.div_floor(&g);
        let i = loop {
            let nz: Vec<usize> = (0..a.len()).filter(|&j| !a[j].is_zero()).collect();
            let i = *nz
                .iter()
                .min_by_key(|&&j| a[j].abs())
                .expect("a coefficient, as gcd 1");
            if nz.len() == 1 {
                break i;
            }
            for &j in nz.iter().filter(|&&j| j != i) {
                let q = a[j].div_floor(&a[i]);
                let shift = |r: &mut Vec<Num>| r[j] = &r[j] - &(&q * &r[i]);
                shift(&mut a);
                for (r, _) in le.iter_mut().chain(eq.iter_mut()) {
                    shift(r);
                }
            }
        };
        assert!(
            a[i].abs() == one,
            "Euclid's algorithm keeps the gcd 1: {a:?}"
        );
        let v = &b * &a[i];
        for (r, c) in le.iter_mut().chain(eq.iter_mut()) {
            *c = &*c - &(&r[i] * &v);
            r[i] = zero.clone();
        }
    }
    let mut rows: BTreeMap<Vec<Num>, Num> = BTreeMap::new();
    for (a, b) in le {
        let g = gcd(&a);
        if g.is_zero() {
            if b.signum() < 0 {
                return false;
            }
            continue;
        }
        let a: Vec<Num> = a.iter().map(|x| x.div_floor(&g)).collect();
        let b = b.div_floor(&g);
        let c = rows.entry(a).or_insert_with(|| b.clone());
        if b < *c {
            *c = b;
        }
    }
    let mut eqs = Vec::new();
    for (a, b) in &rows {
        let na: Vec<Num> = a.iter().map(|x| -x).collect();
        if let Some(c) = rows.get(&na) {
            let s = b + c;
            if s.signum() < 0 {
                return false;
            }
            if s.is_zero() && *a > na {
                eqs.push((a.clone(), b.clone()));
            }
        }
    }
    let rows: Vec<Row> = rows.into_iter().collect();
    if !eqs.is_empty() {
        return omega(rows, eqs);
    }
    // The variable to eliminate: exact first, then the fewest combinations.
    let k = rows.first().map_or(0, |r| r.0.len());
    let mut best: Option<(bool, usize, usize)> = None;
    for j in 0..k {
        let (mut lo, mut up, mut lo_unit, mut up_unit) = (0, 0, true, true);
        for (a, _) in &rows {
            match a[j].signum() {
                1 => (up, up_unit) = (up + 1, up_unit && a[j] == one),
                -1 => (lo, lo_unit) = (lo + 1, lo_unit && a[j] == -&one),
                _ => {}
            }
        }
        if lo + up == 0 {
            continue;
        }
        if lo == 0 || up == 0 {
            return omega(
                rows.into_iter().filter(|(a, _)| a[j].is_zero()).collect(),
                eq,
            );
        }
        let key = (!(lo_unit || up_unit), lo * up, j);
        if best.is_none_or(|b| key < b) {
            best = Some(key);
        }
    }
    // No variable left: each row is `0 <= b` with `b >= 0`, checked above.
    let Some((inexact, _, j)) = best else {
        return true;
    };
    let side = |s: i8| -> Vec<&Row> { rows.iter().filter(|(a, _)| a[j].signum() == s).collect() };
    let (lower, upper) = (side(-1), side(1));
    let shadow = |dark: bool| -> Vec<Row> {
        let mut out: Vec<Row> = rows
            .iter()
            .filter(|(a, _)| a[j].is_zero())
            .cloned()
            .collect();
        for (ua, ub) in &upper {
            for (la, lb) in &lower {
                let (u, l) = (&ua[j], -&la[j]);
                let a = ua
                    .iter()
                    .zip(la)
                    .map(|(x, y)| &(&l * x) + &(u * y))
                    .collect();
                let mut b = &(&l * ub) + &(u * lb);
                if dark {
                    b = &b - &(&(&l - &one) * &(u - &one));
                }
                out.push((a, b));
            }
        }
        out
    };
    if !inexact {
        return omega(shadow(false), Vec::new());
    }
    if !omega(shadow(false), Vec::new()) {
        return false;
    }
    if omega(shadow(true), Vec::new()) {
        return true;
    }
    let m = upper
        .iter()
        .map(|(a, _)| a[j].clone())
        .max()
        .expect("an upper bound");
    for (la, lb) in &lower {
        let l = -&la[j];
        let top = (&(&(&l * &m) - &l) - &m).div_floor(&m);
        let mut i = zero.clone();
        while i <= top {
            if omega(rows.clone(), vec![(la.clone(), lb - &i)]) {
                return true;
            }
            i = &i + &one;
        }
    }
    false
}

/// The rows `a · x <= b` with `l <= u · x <= h` added.
fn with_range(rows: &[(Vec<i64>, i64)], u: &[i64], l: i64, h: i64) -> Vec<(Vec<i64>, i64)> {
    let mut out = rows.to_vec();
    out.push((u.iter().map(|x| -x).collect(), -l));
    out.push((u.to_vec(), h));
    out
}

/// The values of `u · x` in `l..=h` at the integer points `x` of `rows`, as ranges in order,
/// by halving the range and asking [`has_point`] of each half.
///
/// Complexity tradeoff: `O(pieces · log(h - l))` questions where the values taken form a few
/// pieces, `O(h - l)` where every value is a piece of its own; asking value by value is always
/// `O(h - l)`. A test oracle over ranges of a few hundred values at most.
fn taken_within(rows: &[(Vec<i64>, i64)], u: &[i64], l: i64, h: i64) -> Vec<(i64, i64)> {
    if l > h || !has_point(&with_range(rows, u, l, h)) {
        return Vec::new();
    }
    if l == h {
        return vec![(l, l)];
    }
    let m = l + (h - l) / 2;
    let mut out = taken_within(rows, u, l, m);
    for (a, b) in taken_within(rows, u, m + 1, h) {
        match out.last_mut() {
            Some((_, e)) if *e + 1 == a => *e = b,
            _ => out.push((a, b)),
        }
    }
    out
}

/// The least value of `u · x` at least `from` at the integer points `x` of `rows`, or `None`
/// where there is none: a range doubled from `from` until [`has_point`] finds a point in it,
/// which it does once it reaches that least value, then halved down to it.
fn least_taken_from(rows: &[(Vec<i64>, i64)], u: &[i64], from: i64) -> Option<i64> {
    let mut above = rows.to_vec();
    above.push((u.iter().map(|x| -x).collect(), -from));
    if !has_point(&above) {
        return None;
    }
    let mut span: i64 = 1;
    while !has_point(&with_range(rows, u, from, from + span - 1)) {
        span = span.checked_mul(2).expect("a value within i64");
    }
    let (mut lo, mut hi) = (from, from + span - 1);
    while lo < hi {
        let m = lo + (hi - lo) / 2;
        if has_point(&with_range(rows, u, from, m)) {
            hi = m;
        } else {
            lo = m + 1;
        }
    }
    Some(lo)
}

/// The values of `u · x` above `q` at the integer points `x` of `rows`, where the rational
/// values grow without bound and every value in `p..=q` is taken (`p` `None` for no lower end),
/// as ranges in order with the last one open (`None`), or `None` where they are not a finite
/// union of ranges.
///
/// Let `t0` be the least `t >= 1` with an integer point `y` of the recession cone
/// (`a · y <= 0` for each row) with `u · y = t`: one exists, since a rational ray with
/// `u · y > 0` times a common denominator is one, and [`has_point`] decides each `t`. For a
/// value `w` taken at an integer point `x`, `x + k · y` is an integer point for each whole `k`
/// (`a · (x + k · y) <= b`), so `w + k · t0` is taken. So in each class of residues mod `t0`,
/// the values above `q` taken are those from the least one, `m_r`, on: those of `p..=q` itself
/// where it meets the class, else the least found by [`least_taken_from`] with
/// `u · x = r + t0 · k` for a new integer `k`, or none in the class. Where every class has
/// values, `w > q` is taken exactly where `w >= m_r` of its class, and every `w` from the
/// greatest `m_r` on is; where a class has none, the values are infinitely many with
/// infinitely many gaps, which a finite union of ranges cannot hold.
fn taken_beyond(
    rows: &[(Vec<i64>, i64)],
    u: &[i64],
    p: Option<i64>,
    q: i64,
) -> Option<Vec<(i64, Option<i64>)>> {
    let cone: Vec<(Vec<i64>, i64)> = rows.iter().map(|(a, _)| (a.clone(), 0)).collect();
    let t0 = (1..)
        .find(|&t| has_point(&with_range(&cone, u, t, t)))
        .expect("a step of the cone, as the values grow without bound");
    let covered = |r: i64| p.is_none_or(|p| q - p + 1 >= t0 || (r - p).rem_euclid(t0) <= q - p);
    let mut least: Vec<i64> = Vec::new();
    for r in (0..t0).filter(|&r| !covered(r)) {
        let class: Vec<(Vec<i64>, i64)> = rows
            .iter()
            .map(|(a, b)| (a.iter().copied().chain([0]).collect(), *b))
            .chain([
                (u.iter().copied().chain([-t0]).collect(), r),
                (u.iter().map(|x| -x).chain([t0]).collect(), -r),
            ])
            .collect();
        let ue: Vec<i64> = u.iter().copied().chain([0]).collect();
        least.push(least_taken_from(&class, &ue, q + 1)?);
    }
    let top = least.iter().copied().max().unwrap_or(q + 1);
    let mut out: Vec<(i64, Option<i64>)> = Vec::new();
    for w in q + 1..top {
        let r = w.rem_euclid(t0);
        let m = (0..t0).filter(|&s| !covered(s)).position(|s| s == r);
        if m.is_none_or(|m| w >= least[m]) {
            match out.last_mut() {
                Some((_, Some(e))) if *e + 1 == w => *e = w,
                _ => out.push((w, Some(w))),
            }
        }
    }
    match out.last_mut() {
        Some((_, e)) if *e == Some(top - 1) => *e = None,
        _ => out.push((top, None)),
    }
    Some(out)
}

/// `Ok` where each hub lies within `-far..=far` at every rational point of `rows` (over the
/// names of `boxes`, from [`lp_rows`]), or there is none: then [`points`], which visits every
/// integer point with the hubs in that range, visited every integer point of `rows`, so a value
/// it did not find there has no point. Otherwise a description of a hub that reaches beyond.
fn hubs_within(
    rows: &[(Vec<i64>, i64)],
    boxes: &BTreeMap<String, Piece>,
    far: i64,
) -> Result<(), String> {
    let unit = |m: &str, s: i64| -> Vec<i64> {
        boxes.keys().map(|x| if x == m { s } else { 0 }).collect()
    };
    for h in boxes.keys().filter(|h| !h.starts_with('z')) {
        for s in [1, -1] {
            match lp_max(rows, &unit(h, s)) {
                Lp::Empty => return Ok(()),
                Lp::Max(g) if g <= Num::from(far) => {}
                other => return Err(format!("{s} * {h} reaches {other:?}, beyond {far}")),
            }
        }
    }
    Ok(())
}

/// The values of `n` in one disjunct (`cons` within `boxes`), from `hull` and `set`, those
/// [`points`] found with the hubs within `-far..=far` (empty where it found no point; [`brute`]
/// asks this only of a disjunct with an integer point). Where every hub lies in that range at
/// every rational point of the disjunct ([`hubs_within`]), what `points` found is exact.
/// Otherwise the values are decided by integer feasibility ([`has_point`]), exact for any
/// rows, so `far` sets only how much `points` finds at once, never the answer: a value is
/// found first where `points` found none ([`least_taken_from`]); each hole between pieces is
/// decided ([`taken_within`]); at an end that is not the end of the name's box, the values
/// past it up to the floor of the greatest rational value ([`lp_max`]) are decided the same
/// way, and where the rational values grow without bound, those beyond are decided by
/// [`taken_beyond`].
///
/// This replaces a rule that proved values past an end or in a hole taken only by a step of
/// the recession cone found within the window and that panicked where neither a step nor
/// [`hubs_within`] decided them (FAIL-pendants-oracle-undecided: seed 12883791572206885593,
/// whose hole `-117..=-117` of `z2` lay where `-a` is unbounded beyond 75).
///
/// Returns the hull, `lower` and `upper`: `lower` holds only values proved taken and `upper`
/// every value taken, so the exact set lies between them. They are equal but where an end's
/// values grow without bound with a residue class mod the cone's least step never taken
/// ([`taken_beyond`]: infinitely many gaps, which [`IntervalSet`] cannot hold); there `upper`
/// holds every value beyond, and a check that reads these sets says it cannot decide.
fn decided_ends(
    (hull, set): (IntervalSet, IntervalSet),
    n: &str,
    cons: &[Cmp],
    boxes: &BTreeMap<String, Piece>,
    far: i64,
) -> (IntervalSet, IntervalSet, IntervalSet) {
    let rows = lp_rows(cons, boxes);
    if hubs_within(&rows, boxes, far).is_ok() {
        return (hull, set.clone(), set);
    }
    let unit = |s: i64| -> Vec<i64> { boxes.keys().map(|x| if x == n { s } else { 0 }).collect() };
    // A value taken where `points` found none, which [`brute`] asks only of a disjunct with an
    // integer point: the least from 0 up, else the greatest below 0.
    let mut taken = if set.is_empty() {
        let v = least_taken_from(&rows, &unit(1), 0)
            .or_else(|| least_taken_from(&rows, &unit(-1), 1).map(|v| -v))
            .expect("a value, as the disjunct has an integer point");
        IntervalSet::single(v)
    } else {
        set
    };
    // Each hole between two pieces found, `[b + 1, a - 1]` between `[.., b]` and `[a, ..]`.
    let holes: Vec<(i64, i64)> = (taken.pieces().zip(taken.pieces().skip(1)))
        .map(|(p, q)| {
            let (End::Fin(b), End::Fin(a)) = (&p.1, &q.0) else {
                panic!("pieces with a hole between them have finite ends: {taken:?}");
            };
            (
                b.to_i64().expect("a value") + 1,
                a.to_i64().expect("a value") - 1,
            )
        })
        .collect();
    for (b, a) in holes {
        for (l, h) in taken_within(&rows, &unit(1), b, a) {
            taken = taken.join(&IntervalSet::of(l, h));
        }
    }
    let (lo, hi) = boxes[n];
    // Each end, in the values of `sign · n`: the piece at it is `p..=q`, `q` the end found.
    // `back` turns a range of those values, `None` for no end, into one of `n`.
    let mut upper = taken.clone();
    for (sign, bound) in [(1, hi), (-1, lo)] {
        let piece = if sign == 1 {
            taken.last()
        } else {
            taken.first()
        };
        let (near, end) = piece
            .map(|(a, b)| if sign == 1 { (a, b) } else { (b, a) })
            .expect("a value");
        // An end found unbounded: every value beyond it is taken.
        let End::Fin(e) = end else { continue };
        let e = e.to_i64().expect("an end found within the boxes");
        if bound == Some(e) {
            continue;
        }
        let (p, q) = (near.to_i64().map(|v| sign * v), sign * e);
        let back = |l: i64, h: Option<i64>| match sign {
            1 => IntervalSet::range(End::of(l), h.map_or(End::PosInf, End::of)),
            _ => IntervalSet::range(h.map_or(End::NegInf, |h| End::of(-h)), End::of(-l)),
        };
        let more: Vec<IntervalSet> = match lp_max(&rows, &unit(sign)) {
            Lp::Max(f) => {
                let f = f.to_i64().expect("a value");
                (taken_within(&rows, &unit(sign), q + 1, f).into_iter())
                    .map(|(l, h)| back(l, Some(h)))
                    .collect()
            }
            Lp::Unbounded => match taken_beyond(&rows, &unit(sign), p, q) {
                Some(rs) => rs.into_iter().map(|(l, h)| back(l, h)).collect(),
                None => {
                    upper = upper.join(&back(q, None));
                    Vec::new()
                }
            },
            Lp::Empty => unreachable!("{n} takes {e} in {cons:?} {boxes:?}"),
        };
        for m in more {
            taken = taken.join(&m);
            upper = upper.join(&m);
        }
    }
    (upper.hull(), taken, upper)
}

/// The range `-far..=far` [`brute`] enumerates the hubs within on random parts.
const WIDE: i64 = 75;

/// The range [`brute`] enumerates the hubs within on the rows of [`REFUSED`]. The widest
/// reach a row needs is that of row 18, whose `z4 <= -4` holds at `a = -22`, `b = -3`,
/// `c = 45` alone: `a + 2 * b + c <= 17` (from `z3 <= 9`), `a <= 3 * b - 13` and `b <= -3` give
/// `z4 = 2 * a + b + c - 2 <= a - b + 15 <= 2 * b + 2 <= -4`. With [`WIDE`] the brute force took
/// 12 s over the 24 rows, with this and only the hulls kept 4 s (TEST-bench-move-l0139).
const NARROW: i64 = 56;

/// The exact projection of the part onto each name by brute force: in each disjunct (a
/// choice of an arm of each disjunction and of a piece of each box), the hull of the name's
/// values and the set of them, and over the disjuncts the union of each. The hubs are
/// enumerated within `-far..=far`, `far` [`WIDE`] or [`NARROW`], and each end found is decided
/// by [`decided_ends`]. The set is given by two bounds, `lower`, values proved taken, and
/// `upper`, which holds every value taken; the set is exact where they are equal. The sets of a
/// `z` are its hull unless `exact`, and then only the hull is meant to be read.
fn brute(
    items: &[Item],
    bs: &BTreeMap<String, Vec<Piece>>,
    far: i64,
    exact: bool,
) -> BTreeMap<String, Bruted> {
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
    let mut out: BTreeMap<String, (IntervalSet, IntervalSet, IntervalSet)> = bs
        .keys()
        .map(|n| {
            let e = IntervalSet::empty();
            (n.clone(), (e.clone(), e.clone(), e))
        })
        .collect();
    for (cs, b) in &terms {
        let found = match points(cs, b, far, exact) {
            Some(found) => found,
            // No integer point with the hubs within `-far..=far`: none at all, or every name
            // is decided from no value found.
            None if !has_point(&lp_rows(cs, b)) => continue,
            None => {
                let e = IntervalSet::empty();
                b.keys()
                    .map(|n| (n.clone(), (e.clone(), e.clone())))
                    .collect()
            }
        };
        for (n, x) in found {
            let o = out.get_mut(&n).expect("a name");
            let (hull, lower, upper) = decided_ends(x, &n, cs, b, far);
            o.0 = o.0.join(&hull);
            o.1 = o.1.join(&lower);
            o.2 = o.2.join(&upper);
        }
    }
    out.into_iter()
        .map(|(n, (h, l, u))| (n, (show(&h), show(&l), show(&u))))
        .collect()
}

/// What [`brute`] gives each name, shown: its hull, the values proved taken, and a set that
/// holds every value taken.
type Bruted = (String, String, String);

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

/// What [`hung`] leaves each name the part mentions: its answer, or for a name it does not
/// answer, the box, which `Scope::project_part` leaves as it is. The route through
/// `Scope::unbounded_unit` answers the names of the pendant and its form alone; it is taken
/// only where each conjunct on any other name holds at every point of the boxes, so the box
/// of each other name is its projection
/// ([`seed_16705573548664468879_part_16_by_pendants_leaves_the_other_names_their_boxes`]).
fn kept(s: &Scope, f: &Formula) -> Option<BTreeMap<String, String>> {
    let mut out = hung(s, f)?;
    for a in f.atoms() {
        if let Atom::Sym(n) = a {
            out.entry(n.to_string())
                .or_insert_with(|| show(s.get(&n).ints()));
        }
    }
    Some(out)
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
/// disjuncts of the hulls the brute force finds (its exact sets of values shown on a mismatch),
/// with the solver alone ([`solver_alone`]); with the exact cover, the projection by pendants
/// gives the same answer or none, where a question of the cover is refused (row 16).
fn check(rows: &[(&str, &str, &str)]) {
    let mut wrong = Vec::new();
    for (part, bx, want) in rows {
        let items = parse(part);
        let bs = boxes(bx);
        let s = scope(&bs);
        let covered = hung(&s, &formula(&items));
        let got = solver_alone(|| hung(&scope(&bs), &formula(&items)));
        let want: BTreeMap<String, String> = bracketed(want)
            .into_iter()
            .map(|(n, x)| (n, format!("[{x}]")))
            .collect();
        let hulls: BTreeMap<String, String> = brute(&items, &bs, NARROW, false)
            .into_iter()
            .map(|(n, (h, _, _))| (n, h))
            .collect();
        let cover_wrong = covered.as_ref().is_some_and(|c| *c != want);
        if hulls != want || got.as_ref() != Some(&want) || cover_wrong {
            let sets: BTreeMap<String, String> = brute(&items, &bs, NARROW, true)
                .into_iter()
                .map(|(n, (_, l, u))| (n, if l == u { u } else { format!("{l} to {u}") }))
                .collect();
            wrong.push(format!(
                "{part}\n  boxes {bx}\n  hulls {hulls:?}\n  sets  {sets:?}\n  hung  {got:?}\n  cover {covered:?}\n  want  {want:?}"
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
/// and that of the whole part, where neither refuses, are each sound, over the same names
/// ([`pendants_against_whole`]); [`PENDANT_PARTS`] parts are drawn.
/// Each must be the exact set (author P197), so the test fails on any name where the two
/// differ, naming the precision of each answer ([`compared`]), and prints the counts.
/// Seed 0x7e4d at 400 parts took 1.6 s.
#[test]
fn the_projections_by_pendants_and_of_the_whole_part_are_sound() {
    let (r, seed) = Rng::fresh("the projection by pendants");
    pendants_against_whole(r, seed);
}

/// Whether the answer for one name is the exact set of its values, a sound set wider than
/// it, or the set brute force found to hold every value without proving it exact
/// ([`decided_ends`]), so sound and perhaps wider. A wider answer is wrong (author P197) and is
/// counted, not yet failed, until PRES-switchover-not-race.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Precision {
    Exact,
    Wider,
    Sound,
}

/// How `answer` for `name` stands to the set of its values, which brute force bounds by
/// `lower`, values proved taken, and `upper`, which holds every value taken ([`brute`]):
/// - it misses a value of `lower`: an error, unsound;
/// - it holds `upper` and more: wider, since each value outside `upper` is taken nowhere;
/// - it is `upper` and `upper` is `lower`: exact;
/// - it is `upper` and `upper` is not proved exact: sound only, not called exact;
/// - else (it holds `lower` and misses some of `upper`): an error, as brute force cannot
///   decide whether it is sound.
fn precision(
    name: &str,
    answer: &IntervalSet,
    lower: &IntervalSet,
    upper: &IntervalSet,
) -> Result<Precision, String> {
    if lower.meet(answer) != *lower {
        Err(format!(
            "{name}: {} misses values of {} (unsound)",
            show(answer),
            show(lower)
        ))
    } else if upper.meet(answer) != *upper {
        Err(format!(
            "{name}: {} holds {}, the values proved taken, and misses some of {}, which holds \
             every value but is not proved exact (not decided)",
            show(answer),
            show(lower),
            show(upper)
        ))
    } else if answer != upper {
        Ok(Precision::Wider)
    } else if lower == upper {
        Ok(Precision::Exact)
    } else {
        Ok(Precision::Sound)
    }
}

/// Two answers for the part `items` within `bs`, the projection by pendants (`route`) and
/// that of the whole part, checked against brute force: both over the same names and each
/// name of each sound ([`precision`]). On success, each name where they differ with the
/// precision of each.
fn compared(
    items: &[Item],
    bs: &BTreeMap<String, Vec<Piece>>,
    route: &BTreeMap<String, String>,
    whole: &BTreeMap<String, String>,
) -> Result<Vec<(String, Precision, Precision)>, String> {
    if route.keys().ne(whole.keys()) {
        return Err(format!(
            "the answers are over different names: {:?} and {:?}",
            route.keys().collect::<Vec<_>>(),
            whole.keys().collect::<Vec<_>>()
        ));
    }
    let truth = brute(items, bs, WIDE, true);
    let mut differ = Vec::new();
    let mut faults = Vec::new();
    for (n, r) in route {
        let (lower, upper) = (shown_set(&truth[n].1), shown_set(&truth[n].2));
        let judge = |x: &str| precision(n, &shown_set(x), &lower, &upper);
        match (judge(r), judge(&whole[n])) {
            (Ok(p), Ok(q)) if *r != whole[n] => differ.push((n.clone(), p, q)),
            (Ok(_), Ok(_)) => {}
            (p, q) => {
                faults.extend(p.err().map(|e| format!("by pendants {e}")));
                faults.extend(q.err().map(|e| format!("whole {e}")));
            }
        }
    }
    if faults.is_empty() {
        Ok(differ)
    } else {
        Err(faults.join("; "))
    }
}

/// The parts [`pendants_against_whole`] draws: 130, the mean that reaching 40 compared took
/// over 956 seeds (FAIL-pendants-route-quarter-seed), where 30.8% of the parts are compared.
/// No count of compared parts is required of them (PROOF-test-coverage-constructive): when
/// none is compared, the part [`built_compared_part`] is compared in their place.
const PENDANT_PARTS: usize = 130;

/// A part built so that the projection by pendants is taken and that of the whole part
/// answers (the first part of
/// [`a_part_with_a_point_by_the_unbounded_shortcut_is_projected_as_the_whole`]): its items
/// and boxes.
fn built_compared_part() -> (Vec<Item>, BTreeMap<String, Vec<Piece>>) {
    (
        parse("b <= c + z2 - 5 && (2 * b >= c - 6 || c >= 10)"),
        boxes("b=[-7,-7] c=[3,inf] z2=[-inf,inf]"),
    )
}

/// Compares the projection by pendants of one part with that of the whole part: `None` where
/// the route is not taken, `Some(None)` where it is and the whole part refuses, else
/// `Some(Some(fault))`, `fault` empty where the two agree. They must be the same, since each
/// is the exact set (PRES-switchover-not-race); where they differ, [`compared`] (brute force)
/// names the wrong one in the fault, and the names that differ are counted in `kinds` by the
/// precision of each answer.
fn compare_part(
    items: &[Item],
    bs: &BTreeMap<String, Vec<Piece>>,
    kinds: &mut BTreeMap<(Precision, Precision), usize>,
) -> Option<Option<String>> {
    let s = scope(bs);
    let f = formula(items);
    let got = kept(&s, &f)?;
    let Some(want) = whole(&s, &f) else {
        return Some(None);
    };
    if got == want {
        return Some(Some(String::new()));
    }
    let e = match compared(items, bs, &got, &want) {
        Ok(differ) => {
            for (_, p, q) in &differ {
                *kinds.entry((*p, *q)).or_default() += 1;
            }
            format!("{differ:?}")
        }
        Err(e) => e,
    };
    Some(Some(format!(
        "{f}\n  boxes {bs:?}\n  hung  {got:?}\n  whole {want:?}\n  {e}"
    )))
}

/// [`PENDANT_PARTS`] random parts drawn from `r`, each checked by [`compare_part`]; when none
/// was compared, [`built_compared_part`] is, so the comparison is never skipped. Prints the
/// count of names that differ by the precision of each answer, which is empty when the test
/// passes.
fn pendants_against_whole(mut r: Rng, seed: u64) {
    let (mut same, mut taken, mut compared_on) = (0, 0, 0);
    let mut kinds: BTreeMap<(Precision, Precision), usize> = BTreeMap::new();
    let mut wrong = Vec::new();
    for part in 1..=PENDANT_PARTS {
        let (items, bs) = next_case(&mut r, false);
        let Some(answer) = compare_part(&items, &bs, &mut kinds) else {
            continue;
        };
        taken += 1;
        let Some(fault) = answer else { continue };
        compared_on += 1;
        if fault.is_empty() {
            same += 1;
        } else {
            wrong.push(format!("part {part}: {fault}"));
        }
    }
    eprintln!(
        "{PENDANT_PARTS} parts, the route taken on {taken}, compared on {compared_on}, the \
         same on {same}; names that differ (by pendants, whole): {kinds:?}"
    );
    if compared_on == 0 {
        let (items, bs) = built_compared_part();
        match compare_part(&items, &bs, &mut kinds) {
            Some(Some(fault)) if fault.is_empty() => {}
            Some(Some(fault)) => wrong.push(format!("the built part: {fault}")),
            other => panic!("the built part is not compared: {other:?}"),
        }
        eprintln!("no part compared; the built part compared in their place");
    }
    assert!(
        wrong.is_empty(),
        "seed {seed}: {} wrong:\n{}",
        wrong.len(),
        wrong.join("\n")
    );
}

/// The part built for [`pendants_against_whole`] takes the route by pendants, the whole part
/// answers, and the two agree.
#[test]
fn the_part_built_to_be_compared_is_compared_and_agrees() {
    let (items, bs) = built_compared_part();
    let mut kinds = BTreeMap::new();
    assert_eq!(
        compare_part(&items, &bs, &mut kinds),
        Some(Some(String::new()))
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
/// is not asked since each side is first asked at its real bound. The fourth's `b` was refused
/// with `[-4,16]` before item FAIL-batch-single-hull-seed, which asks it of the projection of
/// the rows onto it; its exact hull is `[-4,15]` (brute force,
/// [`refused_projections_keep_the_box_of_their_rows`]).
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
        "a=[2,3] b=[-4,15] c=[-3,6] z0=[-6,-4] z1=[-7,13] refused: Growth z2=[-10,6] refused: Growth left out: [Growth]",
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
    // With the solver alone: under the exact cover, which names of this row are refused
    // depends on how it is written (row GROUP-order-verdicts), and each set it keeps holds
    // the exact hull ([`refused_projections_keep_the_box_of_their_rows_in_each_writing`]).
    solver_alone(|| written_rows(&WRITTEN[3..4]));
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
    let want = boxed_names(&scope(bs), f, &item_names(items));
    renamed_alike(items, bs, want)
}

/// `Ok(want)` where [`boxed_names`] of `items` within `bs` with the names reversed
/// ([`reversing`]), each name read back, is `want`, the answer as written; `Err` with both where
/// they differ. [`refused_alike`] passes the answer it has already, which asking again would
/// only repeat (PERF-pendants-joined-slow-seeds).
#[allow(clippy::type_complexity)]
fn renamed_alike(
    items: &[Item],
    bs: &BTreeMap<String, Vec<Piece>>,
    want: BTreeMap<String, (IntervalSet, bool)>,
) -> Result<BTreeMap<String, (IntervalSet, bool)>, String> {
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
const ROW_BOXES: &str = "a=[2,3] b=[-4,15] c=[-3,6] z0=[-6,-4] z1=[-7,13]! z2=[-10,6]!";

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
/// (`Refusal::Growth`), within its boxes: `z1` and `z2` keep the bounds of the box stage over
/// its rows, each holding the exact hull that brute force finds; `c`, refused until item
/// PRES-project-each-cost with the box stage's `[-3,6]`, and `b`, refused until item
/// FAIL-batch-single-hull-seed with `[-4,16]`, are now answered, each with its exact hull.
/// The answer is the same with the names reversed; for other
/// writings see [`refused_projections_keep_the_box_of_their_rows_in_each_writing`],
/// [`refused_projections_keep_the_box_of_their_rows_in_rewritten_writings`] and
/// [`refused_projections_keep_the_box_of_their_rows_in_scaled_writings`] (one test took 2 s).
///
/// These tests pin the solver alone ([`solver_alone`]). Under the exact cover the names
/// refused, and so the sets kept, depend on how the case is written (as written `a`, `b`, `z1`
/// and `z2`, `b` keeping `[-4,16]`; with the names reversed `z0`, `z1` and `z2`; row
/// GROUP-order-verdicts); [`cover_keeps_the_exact_hulls`] checks that every set it keeps in
/// each writing holds the exact hull.
#[test]
fn refused_projections_keep_the_box_of_their_rows() {
    let (part, bx, _) = WRITTEN[3];
    let items = parse(part);
    let bs = boxes(bx);
    let want = solver_alone(|| boxed_as_named(&items, &bs, &formula(&items))).expect("one answer");
    assert_eq!(shown_boxes(&want), ROW_BOXES);
    let exact = row_hulls();
    assert_eq!(
        exact
            .iter()
            .map(|(n, h)| format!("{n}={}", show(h)))
            .collect::<Vec<_>>()
            .join(" "),
        "a=[2,3] b=[-4,15] c=[-3,6] z0=[-6,-4] z1=[-7,6] z2=[-6,6]"
    );
    for (n, h) in &exact {
        assert_eq!(&want[n].0.meet(h), h, "the box of {n} holds the exact hull");
    }
    cover_keeps_the_exact_hulls(&formula(&items));
    let to = reversing(&bs);
    let (items2, bs2) = renamed(&items, &bs, &to);
    let back: BTreeMap<&String, &String> = to.iter().map(|(k, v)| (v, k)).collect();
    let got = boxed_names(&scope(&bs2), &formula(&items2), &item_names(&items2));
    for (n, (x, _)) in got {
        let h = &exact[back[&n]];
        assert_eq!(
            &x.meet(h),
            h,
            "renamed, the set of {n} holds the exact hull"
        );
    }
}

/// The exact hull of each name of case 272 of seed 17 within its boxes, by brute force.
fn row_hulls() -> BTreeMap<String, IntervalSet> {
    let (part, bx, _) = WRITTEN[3];
    brute(&parse(part), &boxes(bx), WIDE, false)
        .into_iter()
        .map(|(n, (h, _, _))| (n, shown_set(&h)))
        .collect()
}

/// Under the exact cover, each set [`boxed_names`] keeps for `g`, case 272 of seed 17 written
/// another way, holds the exact hull of [`row_hulls`].
fn cover_keeps_the_exact_hulls(g: &Formula) {
    let exact = row_hulls();
    let (items, bs) = (parse(WRITTEN[3].0), boxes(WRITTEN[3].1));
    for (n, (x, _)) in boxed_names(&scope(&bs), g, &item_names(&items)) {
        let h = &exact[&n];
        assert_eq!(&x.meet(h), h, "{g}: the set of {n} holds the exact hull");
    }
}

/// [`refused_projections_keep_the_box_of_their_rows`] in each writing of [`four_ways`].
#[test]
fn refused_projections_keep_the_box_of_their_rows_in_each_writing() {
    for (how, g) in four_ways(&parse(WRITTEN[3].0)) {
        assert_eq!(solver_alone(|| row_boxes(&g)), ROW_BOXES, "{how}: {g}");
        cover_keeps_the_exact_hulls(&g);
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
        assert_eq!(solver_alone(|| row_boxes(&g)), ROW_BOXES, "{g}");
        cover_keeps_the_exact_hulls(&g);
    }
}

/// [`refused_projections_keep_the_box_of_their_rows`] in two random writings by [`scaled`].
#[test]
fn refused_projections_keep_the_box_of_their_rows_in_scaled_writings() {
    let items = parse(WRITTEN[3].0);
    let mut rs = Rng::new(0x5ca1e);
    for g in (0..2).map(|_| scaled(&mut rs, &items)) {
        assert_eq!(solver_alone(|| row_boxes(&g)), ROW_BOXES, "{g}");
        cover_keeps_the_exact_hulls(&g);
    }
}

/// Counts of the parts with a refused name, of the refused names, and of those narrower than
/// their box.
type RefusedCount = (usize, usize, usize);

/// Checks the names of `items` within `bs` that the solver refuses, where it refuses one: each
/// keeps a set that holds its exact hull (`hulls`, asked only then). In every case, refused or
/// not ([`refused_alike`]), the sets and refusals are the same with the names reversed
/// ([`boxed_as_named`]), in each writing of [`four_ways`], and in other orders of the parts
/// and of the names: reversed, two random orders drawn from `order`, and a random writing of
/// [`rewritten`], so that a box whose answer depends on the order of the rows is caught. Adds
/// to `count`, and describes each mismatch, under `label`, in `wrong`.
///
/// These checks are made with the solver alone ([`solver_alone`]). Under the exact cover the
/// names refused depend on how the part is written (row GROUP-order-verdicts: seed
/// 17956898709070133281 case 9 of the joined parts refuses `z1` as written and answers it
/// with the names reversed), so there each set kept, refused or not, is checked only to hold
/// its exact set of values, where some name is refused. The cover is not checked against the
/// hull: its answers are exact, so where a name's values have a hole its answer has the hole
/// too (seed 576410681482475148 case 77 answers `z1 = [-6,-1 1,1]`, the set brute force finds
/// within the hull `[-6,1]`).
fn check_refused(
    label: &str,
    order: &mut Rng,
    items: &[Item],
    bs: &BTreeMap<String, Vec<Piece>>,
    hulls: impl FnOnce() -> BTreeMap<String, (IntervalSet, IntervalSet, IntervalSet)>,
    count: &mut RefusedCount,
    wrong: &mut Vec<String>,
) {
    let f = formula(items);
    let covered = boxed_names(&scope(bs), &f, &item_names(items));
    let cover_refused = covered.values().any(|(_, refused)| *refused);
    let alone = solver_alone(|| refused_alike(label, order, items, bs, count, wrong));
    if alone.is_none() && !cover_refused {
        return;
    }
    let hulls = hulls();
    if cover_refused {
        for (n, (x, _)) in &covered {
            // A set that misses a value proved taken is unsound; one that holds those but
            // misses some of a set brute force found to hold every value, not proved exact,
            // is not decided, and fails too rather than pass unchecked ([`decided_ends`]).
            let (_, lower, upper) = &hulls[n];
            if x.meet(lower) != *lower {
                wrong.push(format!(
                    "{label}: {f}\n  boxes {bs:?}\n  under the cover {n} = {} misses {}",
                    show(x),
                    show(lower)
                ));
            } else if x.meet(upper) != *upper {
                wrong.push(format!(
                    "{label}: {f}\n  boxes {bs:?}\n  under the cover {n} = {} holds {}, the \
                     values proved taken, but not all of {}: brute force cannot decide whether \
                     it is sound",
                    show(x),
                    show(lower),
                    show(upper)
                ));
            }
        }
    }
    let Some((s, got)) = alone else { return };
    for (n, (x, refused)) in &got {
        if !*refused {
            continue;
        }
        count.1 += 1;
        if x != s.get(n).ints() {
            count.2 += 1;
        }
        let h = &hulls[n].0;
        if x.meet(h) != *h {
            wrong.push(format!(
                "{label}: {f}\n  boxes {bs:?}\n  {n} = {} misses {}",
                show(x),
                show(h)
            ));
        }
    }
}

/// The checks of [`check_refused`] that do not read the hulls: the same sets and refusals in
/// each writing and order, in every case, so that a writing that refuses a name, or answers it
/// otherwise, where the plain writing answers is caught too (TEST-refused-alike-plain-answered).
/// Returns the scope and the sets, or `None` where no name is refused.
///
/// Complexity tradeoff: comparing only where a name is refused cost one [`boxed_names`] per
/// answered case; comparing in every case costs about 9 (the writing as given, 1 with the names
/// reversed in [`renamed_alike`], 3 other writings, 4 other orders; until
/// PERF-pendants-joined-slow-seeds `boxed_as_named` asked the writing as given a second time).
/// Measured at seeds 11 to 18 (instructions, so load does not
/// enter): 5.3 times the work of each random test, 1.8 times where refused parts and their
/// hulls already took most of it; at most 38.9 G instructions (seed 17, 100 parts), about
/// 6.5 s. A fault put in to mark a name refused in the reversed writing of answered parts
/// failed all 100 cases of a seed; before this change it could not fail.
#[allow(clippy::type_complexity)]
fn refused_alike(
    label: &str,
    order: &mut Rng,
    items: &[Item],
    bs: &BTreeMap<String, Vec<Piece>>,
    count: &mut RefusedCount,
    wrong: &mut Vec<String>,
) -> Option<(Scope, BTreeMap<String, (IntervalSet, bool)>)> {
    let s = scope(bs);
    let syms = item_names(items);
    let f = formula(items);
    let got = boxed_names(&s, &f, &syms);
    let refused = got.values().any(|(_, refused)| *refused);
    if refused {
        count.0 += 1;
    }
    if let Err(e) = renamed_alike(items, bs, got.clone()) {
        wrong.push(format!("{label}: {f}\n  {e}"));
    }
    let ways = four_ways(items).into_iter().skip(1);
    wrong.extend(writings_that_differ(label, &f, &got, &s, &syms, ways));
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
    refused.then_some((s, got))
}

/// For each writing of `ways` whose sets and refusals in `s` differ from `got`, those of `f`,
/// a line that shows both.
fn writings_that_differ<'a>(
    label: &str,
    f: &Formula,
    got: &BTreeMap<String, (IntervalSet, bool)>,
    s: &Scope,
    syms: &[Atom],
    ways: impl IntoIterator<Item = (&'a str, Formula)>,
) -> Vec<String> {
    let mut wrong = Vec::new();
    for (how, g) in ways {
        let other = boxed_names(s, &g, syms);
        if &other != got {
            wrong.push(format!(
                "{label}: {f}\n  {how}: {g}\n  {got:?}\n  {other:?}"
            ));
        }
    }
    wrong
}

/// Each name's hull from [`brute`].
fn brute_hulls(items: &[Item], bs: &BTreeMap<String, Vec<Piece>>) -> BTreeMap<String, IntervalSet> {
    brute(items, bs, WIDE, false)
        .into_iter()
        .map(|(n, (h, _, _))| (n, shown_set(&h)))
        .collect()
}

/// Each name's hull, the values proved taken and a set that holds every value taken, from
/// [`brute`].
fn brute_sets(
    items: &[Item],
    bs: &BTreeMap<String, Vec<Piece>>,
) -> BTreeMap<String, (IntervalSet, IntervalSet, IntervalSet)> {
    brute(items, bs, WIDE, true)
        .into_iter()
        .map(|(n, (h, l, u))| (n, (shown_set(&h), shown_set(&l), shown_set(&u))))
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
        let hulls = || brute_sets(&items, &bs);
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

/// The oracle decides each end and hole of seed 12883791572206885593 of the joined random
/// parts, whose hole `-117..=-117` of `z2` lies where `-a` is unbounded beyond [`WIDE`]
/// (FAIL-pendants-oracle-undecided).
#[test]
fn the_oracle_decides_every_end_and_hole_of_seed_12883791572206885593() {
    refused_names_in(12883791572206885593, 25, true);
}

/// The oracle decides each end and hole of seed 9829204742287041310 of the joined random parts,
/// whose end 30 of `a` has `c` up to 83 past it, beyond [`WIDE`]
/// (FAIL-pendants-oracle-undecided).
#[test]
fn the_oracle_decides_every_end_and_hole_of_seed_9829204742287041310() {
    refused_names_in(9829204742287041310, 25, true);
}

/// The oracle reads the end 57 of `a` in case 8 of seed 490 of the joined random parts
/// (`a <= 2 * c + 11`, `c <= 23`) as the end, though `a` passes the enumerated range there
/// (FAIL-pendants-brute-window-seed).
#[test]
fn the_oracle_decides_the_end_57_of_seed_490() {
    refused_names_in(490, 25, true);
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
    let hulls = || brute_sets(&items, &bs);
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

/// Case 23 of seed 977, each part two joined (FAIL-pendants-split-writing-seed): beside the
/// equation `2 * a + b == c + z1 + 8` the part has `2 * a + b >= c + z1 - 2`, which the
/// equation implies. Written with each equation split into two rows, the implied row has the
/// terms of one of them and is merged into it; written with the equation as one row, it was
/// kept beside it, changed the order in which the solver took the variables, and the solver
/// refused every name for growth where the split writing gave every name empty. The solver
/// now leaves out a row its equation implies. Every writing gives every name empty, none
/// refused.
#[test]
fn an_equation_beside_a_row_it_implies_is_answered_as_when_split() {
    let (items, bs) = random_case(977, 23, true);
    let s = scope(&bs);
    let syms = item_names(&items);
    for (how, g) in four_ways(&items) {
        let got = boxed_names(&s, &g, &syms);
        assert!(
            got.values()
                .all(|(set, refused)| set.is_empty() && !refused),
            "{how}: {g}\n  {got:?}"
        );
    }
}

/// The comparison of writings in [`refused_alike`] still finds a writing whose answer differs:
/// the part of seed 977, case 23, which gives every name empty, against a planted writing
/// `true`, which does not. The bug of FAIL-pendants-split-writing-seed, an answer that
/// depends on the writing, is fixed, so no true writing of the part is left to plant.
#[test]
fn a_planted_writing_with_another_answer_is_found() {
    let (items, bs) = random_case(977, 23, true);
    let s = scope(&bs);
    let syms = item_names(&items);
    let [_, _, _, (_, split)] = four_ways(&items);
    let got = boxed_names(&s, &split, &syms);
    let wrong = writings_that_differ(
        "planted",
        &split,
        &got,
        &s,
        &syms,
        [("planted", Formula::top())],
    );
    assert_eq!(wrong.len(), 1, "{wrong:?}");
}

/// Case 15 of seed 894, each part two joined (FAIL-pendants-oracle-seed-894):
/// `z0 >= z3 + 8` with `z0 <= 21` gives `z3 <= 13`, the cover's answer `[-1,13]`. Brute force
/// found `z3 = 13` with the hubs within one range and not within the other, and so opened the
/// end to the box's `19`, and failed the sound cover; [`decided_ends`] keeps it. The set, which
/// [`check_refused`] holds the cover to, is the hull, so a cover that misses any of `-1..=13`
/// still fails.
#[test]
fn an_end_that_moves_between_ranges_of_the_hubs_is_decided_not_opened() {
    let (items, bs) = random_case(894, 15, true);
    let z3 = &brute_sets(&items, &bs)["z3"];
    let want = shown_set("[-1,13]");
    assert_eq!((&z3.0, &z3.1, &z3.2), (&want, &want, &want));
    check_refused_case(894, 15, true, (1, 1, 1));
}

/// Case 77 of seed 576410681482475148: the solver alone refuses no name; the cover refuses
/// some name, and answers `z1` with the set brute force finds, `[-6,-1 1,1]`, which has a
/// hole at 0 within the hull `[-6,1]`; a check of the cover against the hull failed it.
#[test]
fn a_part_whose_name_has_a_hole_keeps_its_exact_set_under_the_cover() {
    check_refused_case(576410681482475148, 77, false, (0, 0, 0));
}

/// Case 2 of seed 12220907512220935064, each part two joined: the names the solver refuses
/// (`z2`, `z4` and `z5`, each `Refusal::Growth`) and their boxes are the same in every order of
/// the wanted names, which is also the order of their box rows (item
/// FAIL-refused-boxes-order-seed: the projection of a group's rows onto its names
/// together, `projected_hulls`, eliminated by the names' order, and in some orders the solver
/// answered `z4` or `z5`, in others refused it).
#[test]
fn refused_boxes_do_not_depend_on_the_order_of_the_symbols() {
    let seed = 12220907512220935064;
    let (items, bs) = random_case(seed, 2, true);
    let s = scope(&bs);
    let syms = item_names(&items);
    let f = formula(&items);
    let want = boxed_names(&s, &f, &syms);
    let refused: Vec<&str> = (want.iter())
        .filter(|(_, (_, e))| *e)
        .map(|(n, _)| n.as_str())
        .collect();
    assert_eq!(refused, ["z2", "z4", "z5"]);
    let mut order = Rng::new(0x0de5 ^ seed ^ (2 << 32));
    let mut orders: Vec<Vec<Atom>> = (0..syms.len())
        .map(|k| (syms[k..].iter()).chain(&syms[..k]).cloned().collect())
        .collect();
    orders.push(syms.iter().rev().cloned().collect());
    for _ in 0..8 {
        let mut ss = syms.clone();
        shuffle(&mut order, &mut ss);
        orders.push(ss);
    }
    for ss in &orders {
        assert_eq!(boxed_names(&s, &f, ss), want, "names in the order {ss:?}");
    }
}

/// [`check_refused`] on case 2 of seed 12220907512220935064 (item
/// FAIL-refused-boxes-order-seed): its refused names in every order of the parts and names.
#[test]
fn a_refused_part_keeps_its_refusals_in_every_order() {
    check_refused_case(12220907512220935064, 2, true, (1, 3, 0));
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

/// Seed 5401893596085442912 of [`rewritten_parts_give_one_answer`], kept (row
/// PRES-cover-order-rewrites): its case 4 refused `z0` with `Questions` as written, and three
/// rewrites (another order, a repeated conjunct, an equation as two inequalities) answered
/// `z0 = [-13, -5]`. The formula reached the cover with `!(a + z1 == b + 2c - 4)` in the sign it
/// was written in, and the cover's work depends on the sign of each row; the projection now
/// writes each equation in one sign before the cover (`project_each_asked`).
#[test]
fn the_rewrites_of_seed_5401893596085442912_give_one_answer() {
    let seed = 5401893596085442912;
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
                    "case {case}\n  {f}\n  {g}\n  want {want:?}\n  got  {got:?}"
                ));
            }
        }
    }
    assert!(
        wrong.is_empty(),
        "{} rewrites differ:\n{}",
        wrong.len(),
        wrong.join("\n")
    );
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

/// Seed 8087861239740142386 of [`rewritten_parts_are_decided_alike`]
/// (FAIL-pendants-rewrite-growth-seed): case 43, with `2 * a + b + 2 * c + z0 == 3` and no
/// point, was found empty by `decide` on each writing, but `satisfiable` refused it by growth as
/// written and found it empty once the equation was written as two rows. `satisfiable` now
/// removes the disjuncts the bounds show have no point before it settles, as `decide` does
/// (`l01_38_omega_test::decide_sat::an_equation_written_as_one_row_or_two_is_decided_by_both`).
#[test]
fn rewritten_parts_of_seed_8087861239740142386_are_decided_alike() {
    let seed = 8087861239740142386u64;
    let mut wrong = Vec::new();
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
            let got = decided(&s, &g, &syms);
            if got != want {
                wrong.push(format!(
                    "case {case}\n  {f}\n  {g}\n  want {want}\n  got  {got}"
                ));
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
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
/// 11312057540586612196 compared 26 and 6901888717729865865 compared 24. Each of their
/// [`PENDANT_PARTS`] parts compared agrees.
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

/// A random part, its boxes, its formula, its projection by pendants and that of the whole.
type Answers = (
    Vec<Item>,
    BTreeMap<String, Vec<Piece>>,
    Formula,
    BTreeMap<String, String>,
    BTreeMap<String, String>,
);

/// Part `part` (from 1) of `seed` as [`pendants_against_whole`] draws them, its formula,
/// and its projection by pendants and that of the whole part, which must both answer.
fn answers(seed: u64, part: usize) -> Answers {
    let (items, bs) = random_case(seed, part - 1, false);
    let s = scope(&bs);
    let f = formula(&items);
    let route = kept(&s, &f).expect("the route taken");
    let all = whole(&s, &f).expect("the whole projection answers");
    (items, bs, f, route, all)
}

/// Three random parts whose projection by pendants lost a parity or a hole while the new name
/// of each pendant form took every value (FAIL-pendants-route-parity): with the name bounded
/// by the range of its form over the boxes (`Scope::form_hull`), each is projected as the
/// whole part is, and both are sound.
#[test]
fn the_route_by_pendants_keeps_parities_and_holes() {
    for (seed, part) in [
        (12317615902327464975u64, 352),
        (11157326757344143999, 200),
        (11291320176478098157, 117),
    ] {
        let (items, bs, f, route, all) = answers(seed, part);
        assert_eq!(route, all, "seed {seed} part {part}: {f}");
        assert_eq!(
            compared(&items, &bs, &route, &all),
            Ok(Vec::new()),
            "seed {seed} part {part}: {f}"
        );
    }
}

/// A part where `2 * b + 2 * c + z3 == 7` makes `z3` odd (FAIL-whole-projection-parity): the
/// projection by pendants and that of the whole part both give the exact set `{1, 3, 5}`.
/// The whole part's projection was the hull `[1, 5]` while the solver could answer first in
/// the race of `row_sums` (QUESTIONS A105, overruled by the author, P196/P197); since
/// PRES-switchover-not-race the join answers it within its limit.
#[test]
fn seed_12035647242373093243_part_52_is_exact_both_ways() {
    let (items, bs, f, route, all) = answers(12035647242373093243, 52);
    assert_eq!(route["z3"], "[1,1 3,3 5,5]", "{f}");
    assert_eq!(all["z3"], "[1,1 3,3 5,5]", "{f}");
    assert_eq!(route, all, "{f}");
    assert_eq!(compared(&items, &bs, &route, &all), Ok(Vec::new()), "{f}");
}

/// Negative controls of [`compared`] on part 52 of seed 12035647242373093243, where
/// `2 * b + 2 * c + z3 == 7` makes `z3` odd: with `z3` of the projection by pendants
/// replaced, a set that misses the value 3 is caught as unsound, and a set that holds 7 is
/// sound but counted wider, not exact; answers over different names are caught.
#[test]
fn the_comparison_of_projections_catches_unsound_answers_and_counts_wider_ones() {
    let (items, bs, _, route, all) = answers(12035647242373093243, 52);
    let with = |z3: &str| {
        let mut m = route.clone();
        m.insert("z3".to_string(), z3.to_string());
        m
    };
    let got = compared(&items, &bs, &with("[1,1 5,5]"), &all);
    assert!(
        got.as_ref().is_err_and(|e| e.contains("(unsound)")),
        "want unsound, got {got:?}"
    );
    let got = compared(&items, &bs, &with("[1,7]"), &with("[1,1 3,3 5,5]"));
    assert_eq!(
        got,
        Ok(vec![("z3".to_string(), Precision::Wider, Precision::Exact)])
    );
    let mut fewer = route.clone();
    fewer.remove("z3");
    let got = compared(&items, &bs, &fewer, &all);
    assert!(
        got.as_ref().is_err_and(|e| e.contains("different names")),
        "want different names, got {got:?}"
    );
}

/// The sets [`brute`] gives each name of a part, `upper` as an answer [`compared`] takes,
/// with `lower` and `upper` for the assertions.
#[allow(clippy::type_complexity)]
fn brute_answer(
    items: &[Item],
    bs: &BTreeMap<String, Vec<Piece>>,
) -> (BTreeMap<String, String>, BTreeMap<String, (String, String)>) {
    let truth = brute(items, bs, WIDE, true);
    let answer = (truth.iter())
        .map(|(n, (_, _, u))| (n.clone(), u.clone()))
        .collect();
    let bounds = (truth.into_iter())
        .map(|(n, (_, l, u))| (n, (l, u)))
        .collect();
    (answer, bounds)
}

/// How [`compared`] judges `x` for `name` against the sets brute force finds for the rest of
/// the part: each other name is given that set both ways.
fn judged(
    items: &[Item],
    bs: &BTreeMap<String, Vec<Piece>>,
    name: &str,
    x: &str,
) -> Result<Vec<(String, Precision, Precision)>, String> {
    let (truth, _) = brute_answer(items, bs);
    let mut answer = truth.clone();
    answer.insert(name.to_string(), x.to_string());
    compared(items, bs, &answer, &truth)
}

/// Negative controls of the brute-force check (TEST-pendants-brute-force-catches-unsound) on
/// case 15 of seed 894, each part two joined, where `z3` takes every value of `[-1,13]` and its
/// upper end `13` is decided by the simplex's maximum and its lower end `-1` likewise
/// ([`an_end_that_moves_between_ranges_of_the_hubs_is_decided_not_opened`]): an end one too
/// narrow at either side, a hole that is not a hole, and the empty set are each caught as
/// unsound by [`compared`] and by [`precision`]; the set itself is exact.
#[test]
fn the_brute_force_check_rejects_a_narrow_end_a_false_hole_and_the_empty_set() {
    let (items, bs) = random_case(894, 15, true);
    let (_, bounds) = brute_answer(&items, &bs);
    assert_eq!(bounds["z3"], ("[-1,13]".to_string(), "[-1,13]".to_string()));
    let exact = shown_set("[-1,13]");
    for x in ["[-1,12]", "[0,13]", "[-1,5 7,13]", "[-1,-1 1,13]", "[]"] {
        let got = judged(&items, &bs, "z3", x);
        assert!(
            got.as_ref().is_err_and(|e| e.contains("(unsound)")),
            "z3 = {x}: want unsound, got {got:?}"
        );
        let got = precision("z3", &shown_set(x), &exact, &exact);
        assert!(got.is_err(), "z3 = {x}: want unsound, got {got:?}");
    }
    let got = judged(&items, &bs, "z3", "[-1,13]");
    assert_eq!(got, Ok(Vec::new()));
    let got = judged(&items, &bs, "z3", "[-2,13]");
    assert_eq!(
        got,
        Ok(vec![("z3".to_string(), Precision::Wider, Precision::Exact)])
    );
}

/// A periodic name given its hull, bounded: in part 52 of seed 12035647242373093243,
/// `2 * b + 2 * c + z3 == 7` makes `z3` odd, `{1, 3, 5}`, and its hull `[1,5]` is judged wider,
/// not exact; the exact set is exact.
#[test]
fn the_brute_force_check_counts_the_hull_of_a_bounded_periodic_name_wider() {
    let (items, bs, _, route, all) = answers(12035647242373093243, 52);
    let mut hull = route.clone();
    hull.insert("z3".to_string(), "[1,5]".to_string());
    assert_eq!(
        compared(&items, &bs, &hull, &all),
        Ok(vec![("z3".to_string(), Precision::Wider, Precision::Exact)])
    );
    let (_, bounds) = brute_answer(&items, &bs);
    let odd = "[1,1 3,3 5,5]".to_string();
    assert_eq!(bounds["z3"], (odd.clone(), odd));
}

/// A name unbounded on one side whose values beyond the range brute force enumerates keep a
/// period or a gap: `z0 == 2 * a + 1` takes the odd values from 1 on (or, within
/// `z0 <= 0`, from -1 down), and `100 * b <= a <= 100 * b + 1` with `b >= 0` takes
/// `0, 1, 100, 101, ...`. Brute force opens the end, and the set it opens holds every value
/// but is wider than the exact set, which no finite union of ranges is. Before the check
/// read the values proved taken, an answer equal to that opened set was judged exact; now it
/// is judged sound only, the hull is wider, a set that misses a value found is unsound, and
/// a set that holds the values found but stops at the range enumerated is not decided.
#[test]
fn the_brute_force_check_does_not_call_an_opened_periodic_or_gapped_set_exact() {
    // The odd values from 1 to 151, found with `a` in `0..=75`.
    let odd: Vec<String> = (0..=75).map(|k| format!("{0},{0}", 2 * k + 1)).collect();
    let found = format!("[{}]", odd.join(" "));
    let opened = format!("[{} 151,inf]", odd[..75].join(" "));
    let missing = format!("[{} 151,inf]", odd[1..75].join(" "));
    let items = parse("z0 == 2 * a + 1");
    let bs = boxes("a=[-inf,inf] z0=[0,inf]");
    let got = judged(&items, &bs, "z0", &opened);
    assert_eq!(got, Ok(Vec::new()), "the opened set is sound");
    let (_, bounds) = brute_answer(&items, &bs);
    let (lower, upper) = (shown_set(&bounds["z0"].0), shown_set(&bounds["z0"].1));
    let got = precision("z0", &shown_set(&opened), &lower, &upper);
    assert_eq!(
        got,
        Ok(Precision::Sound),
        "the opened set is not called exact"
    );
    assert_eq!(bounds["z0"], (found.clone(), opened.clone()));
    for (x, want) in [
        (opened.as_str(), Ok(Precision::Sound)),
        ("[1,inf]", Ok(Precision::Wider)),
        ("[0,inf]", Ok(Precision::Wider)),
    ] {
        let got = judged(&items, &bs, "z0", x).map(|d| d.first().map(|(_, p, _)| *p));
        let want = want.map(|p| (p != Precision::Sound).then_some(p));
        assert_eq!(got, want, "z0 = {x}");
        let got = precision("z0", &shown_set(x), &shown_set(&found), &shown_set(&opened));
        assert_eq!(got, want.map(|p| p.unwrap_or(Precision::Sound)), "z0 = {x}");
    }
    for (x, says) in [
        (missing.as_str(), "(unsound)"),
        ("[]", "(unsound)"),
        (found.as_str(), "(not decided)"),
        ("[1,149]", "(unsound)"),
    ] {
        let got = judged(&items, &bs, "z0", x);
        assert!(
            got.as_ref().is_err_and(|e| e.contains(says)),
            "z0 = {x}: want {says}, got {got:?}"
        );
    }
    // The lower end alike.
    let bs = boxes("a=[-inf,inf] z0=[-inf,0]");
    let (_, bounds) = brute_answer(&items, &bs);
    let (lower, upper) = (shown_set(&bounds["z0"].0), shown_set(&bounds["z0"].1));
    assert_eq!(
        upper.meet(&shown_set("[-inf,-148]")),
        shown_set("[-inf,-149]")
    );
    assert_eq!(lower.first(), Some(&(End::of(-149), End::of(-149))));
    assert_eq!(
        precision("z0", &upper, &lower, &upper),
        Ok(Precision::Sound)
    );
    // A gap: `a` takes `0, 1` within the range and `100, 101, ...` beyond it, the classes 2
    // to 99 mod the cone's least step 100 never, so it is not proved; `b` takes every value
    // from 0 on (`a = 100 * b`), only 0 within the range, and the cone's step 1 proves the rest.
    let items = parse("100 * b <= a && a <= 100 * b + 1");
    let bs = boxes("a=[-inf,inf] b=[0,inf]");
    let (truth, bounds) = brute_answer(&items, &bs);
    assert_eq!(bounds["a"], ("[0,1]".to_string(), "[0,inf]".to_string()));
    assert_eq!(bounds["b"], ("[0,inf]".to_string(), "[0,inf]".to_string()));
    assert_eq!(
        compared(&items, &bs, &truth, &truth),
        Ok(Vec::new()),
        "the opened sets are sound"
    );
    let (l, u) = &bounds["a"];
    let got = precision("a", &shown_set(u), &shown_set(l), &shown_set(u));
    assert_eq!(got, Ok(Precision::Sound), "a");
    let (l, u) = &bounds["b"];
    let got = precision("b", &shown_set(u), &shown_set(l), &shown_set(u));
    assert_eq!(got, Ok(Precision::Exact), "b");
}

/// An opened end that a step of the recession cone proves ([`decided_ends`]) keeps an exact
/// set: `z0 == a + 1` (step 1) takes every value from 0 on, and `z0 == 2 * a + b` with
/// `a >= 0` and `b` in `0..=1` (step 2 only, within a last piece found of 152 values) takes
/// every value from 0 on; on the lower side `z0 == a - 1` within `z0 <= 0` takes every value
/// from 0 down. Each such set is judged exact, and one value fewer unsound.
#[test]
fn an_opened_end_proved_by_a_step_of_the_cone_is_exact() {
    for (part, bx, name, want, fewer) in [
        (
            "z0 == a + 1",
            "a=[-inf,inf] z0=[0,inf]",
            "z0",
            "[0,inf]",
            "[0,1 3,inf]",
        ),
        (
            "z0 == 2 * a + b",
            "a=[0,inf] b=[0,1] z0=[-inf,inf]",
            "z0",
            "[0,inf]",
            "[0,1 3,inf]",
        ),
        (
            "z0 == a - 1",
            "a=[-inf,inf] z0=[-inf,0]",
            "z0",
            "[-inf,0]",
            "[-inf,-1]",
        ),
        (
            "z0 == 2 * a + b",
            "a=[0,inf] b=[0,1] z0=[-inf,inf]",
            "a",
            "[0,inf]",
            "[1,inf]",
        ),
    ] {
        let (items, bs) = (parse(part), boxes(bx));
        let (_, bounds) = brute_answer(&items, &bs);
        assert_eq!(
            bounds[name],
            (want.to_string(), want.to_string()),
            "{part} {name}"
        );
        let x = shown_set(want);
        assert_eq!(precision(name, &x, &x, &x), Ok(Precision::Exact), "{part}");
        let got = judged(&items, &bs, name, fewer);
        assert!(
            got.as_ref().is_err_and(|e| e.contains("(unsound)")),
            "{part}: {name} = {fewer}: want unsound, got {got:?}"
        );
    }
}

/// Plan row TEST-pendants-step-proof-complete: opened ends that are exact where the values
/// found within the range have holes near their end that only a hub beyond the range fills,
/// so the rows alone do not decide them ([`decided_ends`]). `z0 == 2 * a + 3 * b` with `a`
/// and `b` from 0 takes 0 and every value from 2 on, steps 2 and 3 combined; within the range
/// it misses 374, which needs `a = 76` or `b = 76`. With `b` in `0..=1` it takes the same, step
/// 2 alone from 0 and from 3; within the range it misses 152. The lower side alike. Each hole
/// is filled by a step of the cone from a value found, the end is then proved, the set is
/// judged exact, and the set without the filled value unsound. The brute force panicked on
/// each such hole before ("cannot decide the hole").
#[test]
fn a_hole_filled_by_a_step_of_the_cone_is_taken() {
    for (part, bx, want, fewer) in [
        (
            "z0 == 2 * a + 3 * b",
            "a=[0,inf] b=[0,inf] z0=[-inf,inf]",
            "[0,0 2,inf]",
            "[0,0 2,373 375,inf]",
        ),
        (
            "z0 == 2 * a + 3 * b",
            "a=[0,inf] b=[0,1] z0=[-inf,inf]",
            "[0,0 2,inf]",
            "[0,0 2,151 153,inf]",
        ),
        (
            "z0 + 2 * a + 3 * b == 0",
            "a=[0,inf] b=[0,inf] z0=[-inf,inf]",
            "[-inf,-2 0,0]",
            "[-inf,-375 -373,-2 0,0]",
        ),
    ] {
        let (items, bs) = (parse(part), boxes(bx));
        let (_, bounds) = brute_answer(&items, &bs);
        assert_eq!(
            bounds["z0"],
            (want.to_string(), want.to_string()),
            "{part} {bx}"
        );
        let x = shown_set(want);
        assert_eq!(precision("z0", &x, &x, &x), Ok(Precision::Exact), "{part}");
        let got = judged(&items, &bs, "z0", fewer);
        assert!(
            got.as_ref().is_err_and(|e| e.contains("(unsound)")),
            "{part} {bx}: z0 = {fewer}: want unsound, got {got:?}"
        );
    }
}

/// `z0 <= z5 + 5 && !(2 * a + b + c == z5 + 6) && b <= c + z2 - 8`, where the first two hold
/// at every point of the boxes (`z0` in `[-4,-3]`, `z5 == -2`, `a <= -3`, `b <= 1`, `c` in
/// `[2,4]`): the projection by pendants (`Scope::unbounded_unit`) answers `b`, `c` and `z2`
/// alone, and leaves `a`, `z0` and `z5` their boxes, which are the projection of the whole
/// part.
#[test]
fn seed_16705573548664468879_part_16_by_pendants_leaves_the_other_names_their_boxes() {
    let (items, bs) = random_case(16705573548664468879, 15, false);
    let s = scope(&bs);
    let f = formula(&items);
    let answered: Vec<String> = hung(&s, &f).expect("the route taken").into_keys().collect();
    assert_eq!(answered, ["b", "c", "z2"], "{f}");
    let (items, bs, f, route, all) = answers(16705573548664468879, 16);
    assert_eq!(route, all, "{f}");
    assert_eq!(compared(&items, &bs, &route, &all), Ok(Vec::new()), "{f}");
}

/// On the seeds of FAIL-pendants-route-parity and FAIL-whole-projection-parity, the
/// projection by pendants and that of the whole part each give, for every name, the exact
/// set of its values that brute force finds (author P197: a projection is the exact set on
/// every path; PRES-switchover-not-race).
#[test]
fn projections_by_pendants_and_of_the_whole_part_are_exact_on_the_parity_seeds() {
    let mut wrong = Vec::new();
    for (seed, part) in [
        (12317615902327464975u64, 352),
        (11157326757344143999, 200),
        (11291320176478098157, 117),
        (12035647242373093243, 52),
        (16705573548664468879, 16),
    ] {
        let (items, bs, f, route, all) = answers(seed, part);
        let truth = brute(&items, &bs, WIDE, true);
        for (side, answer) in [("by pendants", &route), ("whole", &all)] {
            for (n, x) in answer {
                let (lower, upper) = (shown_set(&truth[n].1), shown_set(&truth[n].2));
                if lower != upper {
                    wrong.push(format!(
                        "seed {seed} part {part}: brute force has not proved the set of {n} \
                         exact, {} to {}; {f}",
                        show(&lower),
                        show(&upper)
                    ));
                } else if shown_set(x) != upper {
                    wrong.push(format!(
                        "seed {seed} part {part} {side}: {n} is {x}, not the exact set {}; {f}",
                        show(&upper)
                    ));
                }
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// Seeds of the rewritten parts whose writings were decided differently (FAIL-rewrite-growth-both,
/// found in a run of 960 seeds of `rewritten_parts_are_decided_alike`): `decide` and
/// `satisfiable` both refused for growth on some writings of a part and answered on others, as
///   seed 12542484037655067360 case 20: Ok(true) as written, Err(Growth) on a rewrite;
///   seed 2180316115169132109 case 27: Ok(false) as written, Err(Growth) on three rewrites;
///   seed 9035190647815979720 case 19: Err(Growth) as written, Ok(true) on a rewrite;
/// and the rows a `Tie` or `Unordered` refusal names followed the order the rows were written in
/// (seed 14004696678485946570 case 56, seed 17840270323861607379 case 12). The solver's
/// elimination order reads the scale and sign of each row; both questions now write the formula
/// one way first (`signed` in crates/zedc-presburger/src/presburger.rs).
#[test]
fn rewritten_parts_of_five_seeds_are_decided_alike() {
    let mut wrong = Vec::new();
    for seed in [
        12542484037655067360u64,
        2180316115169132109,
        9035190647815979720,
        14004696678485946570,
        17840270323861607379,
    ] {
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
                let got = decided(&s, &g, &syms);
                if got != want {
                    wrong.push(format!(
                        "seed {seed} case {case}\n  {f}\n  {g}\n  want {want}\n  got  {got}"
                    ));
                }
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// Case 39 of seed 15306138842172969565 is decided alike on every rewrite
/// (FAIL-pendants-growth-scaled-seed). The part is
///   2 * a == b + c + z0 - 2 && a + z0 >= b - 1 && z2 >= z5 - 7 && 2 * a + b + z5 >= 4
///   && 2 * a + b + c >= z5 + 3 && a + z2 >= b + c - 5 && 2 * a + c + z5 >= -11
///   && z0 <= z1 + 10 && 2 * a + c + z1 == b - 12
/// with boxes a >= 0, z0 >= -3, z1 >= 3, z2 in -2..=11, z3 >= 3, z4 in 3..=21, z5 in 0..=13.
/// As written, `decide` and `satisfiable` gave Ok(true); on one rewrite of 360 (rows times 2
/// and 3, the first equation written twice, rows reordered) both refused with Err(Growth), from
/// f0467a735, the first commit at which this seed draws this case, on. The cause is that of
/// FAIL-rewrite-growth-both, and so is the fix.
#[test]
fn rewritten_parts_of_seed_15306138842172969565_are_decided_alike() {
    let seed = 15306138842172969565u64;
    let mut wrong = Vec::new();
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
            let got = decided(&s, &g, &syms);
            if got != want {
                wrong.push(format!(
                    "seed {seed} case {case}\n  {f}\n  {g}\n  want {want}\n  got  {got}"
                ));
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// Case 39 of seed 15306138842172969565, with one change of writing at a time: its second
/// equation times 3, its inequalities each times a factor, its first equation held twice (the
/// second time times 2), and its rows in another order. Each gives the answer of the case as
/// written, a point. Before `decide` and `satisfiable` wrote each formula one way (each row
/// divided by the common factor of its coefficients, each equation with one sign), the rows
/// times a factor got other colors in the solver's elimination order, and both questions were
/// refused for growth (FAIL-rewrite-growth-both).
#[test]
fn each_change_of_writing_of_case_39_keeps_its_answer() {
    let s = scope(&boxes(
        "a=[0,inf] b=[-inf,inf] c=[-inf,inf] z0=[-3,inf] z1=[3,inf] z2=[-2,11] z5=[0,13]",
    ));
    let written = "2 * a == b + c + z0 - 2 && a + z0 >= b - 1 && z2 >= z5 - 7 && \
                   2 * a + b + z5 >= 4 && 2 * a + b + c >= z5 + 3 && a + z2 >= b + c - 5 && \
                   2 * a + c + z5 >= -11 && z0 <= z1 + 10 && 2 * a + c + z1 == b - 12";
    let changed = [
        // The second equation times 3.
        "2 * a == b + c + z0 - 2 && a + z0 >= b - 1 && z2 >= z5 - 7 && 2 * a + b + z5 >= 4 && \
         2 * a + b + c >= z5 + 3 && a + z2 >= b + c - 5 && 2 * a + c + z5 >= -11 && \
         z0 <= z1 + 10 && 6 * a + 3 * c + 3 * z1 == 3 * b - 36",
        // Each inequality times 2 or 3, its constant moved toward zero by less than the factor.
        "2 * a == b + c + z0 - 2 && 3 * a + 3 * z0 >= 3 * b - 4 && 2 * z2 >= 2 * z5 - 14 && \
         4 * a + 2 * b + 2 * z5 >= 8 && 4 * a + 2 * b + 2 * c >= 2 * z5 + 6 && \
         2 * a + 2 * z2 >= 2 * b + 2 * c - 10 && 6 * a + 3 * c + 3 * z5 >= -34 && \
         3 * z0 <= 3 * z1 + 32 && 2 * a + c + z1 == b - 12",
        // The first equation held twice.
        "2 * a == b + c + z0 - 2 && 4 * a == 2 * b + 2 * c + 2 * z0 - 4 && a + z0 >= b - 1 && \
         z2 >= z5 - 7 && 2 * a + b + z5 >= 4 && 2 * a + b + c >= z5 + 3 && \
         a + z2 >= b + c - 5 && 2 * a + c + z5 >= -11 && z0 <= z1 + 10 && \
         2 * a + c + z1 == b - 12",
        // The rows in another order.
        "2 * a + c + z5 >= -11 && 2 * a + c + z1 == b - 12 && 2 * a == b + c + z0 - 2 && \
         a + z2 >= b + c - 5 && a + z0 >= b - 1 && 2 * a + b + c >= z5 + 3 && z2 >= z5 - 7 && \
         z0 <= z1 + 10 && 2 * a + b + z5 >= 4",
    ];
    let items = parse(written);
    let syms = item_names(&items);
    let want = decided(&s, &formula(&items), &syms);
    assert_eq!(want, "decide Ok(true), satisfiable Ok(true)");
    for text in changed {
        let items = parse(text);
        assert_eq!(item_names(&items), syms, "{text}: the names");
        assert_eq!(decided(&s, &formula(&items), &syms), want, "{text}");
    }
}

/// Seeds of `rewritten_parts_are_decided_alike` found after the fix of FAIL-rewrite-growth-both
/// by other agents, each failing the same on main before it: one part decided Ok(true) as
/// written and Err(Growth) by both `decide` and `satisfiable` on one rewrite.
///   seed 11479163432696490265 case 48 (found by the agent of FAIL-pendants-route-parity on
///   e8310066c): the rewrite holds the equation `2 * a + c == b + z0 - 4` twice and writes
///   `a + c == z1 - 11` as two inequalities;
///   seed 6219709144489400023 case 44: the rewrite holds `a + z3 == 2 * b + c` twice and writes
///   `2 * a + z0 == c - 2` as two inequalities.
/// The cause and the fix are those of FAIL-rewrite-growth-both (checked red with the fix taken
/// out).
#[test]
fn rewritten_parts_of_seeds_found_later_are_decided_alike() {
    let mut wrong = Vec::new();
    for seed in [11479163432696490265u64, 6219709144489400023] {
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
                let got = decided(&s, &g, &syms);
                if got != want {
                    wrong.push(format!(
                        "seed {seed} case {case}\n  {f}\n  {g}\n  want {want}\n  got  {got}"
                    ));
                }
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// Seed 8090022510343574640 of the test of pendants against the whole part: the whole part
/// keeps the parity of `z0` that `2 * b + 2 * c + z0 == 3` forces (FAIL-whole-projection-parity-seed).
#[test]
fn the_whole_part_keeps_the_parity_an_equality_forces_at_seed_8090022510343574640() {
    let seed = 8_090_022_510_343_574_640;
    pendants_against_whole(Rng::new(seed), seed);
}

/// Seed 11342540463404683610: `2 * a + 2 * b + z2 == -12`, z2 even.
#[test]
fn the_whole_part_keeps_the_parity_an_equality_forces_at_seed_11342540463404683610() {
    let seed = 11_342_540_463_404_683_610;
    pendants_against_whole(Rng::new(seed), seed);
}

/// Case 9 of seed 7683774971210369151, each part two joined: with `a + b + 2 * c == z1 + 5`
/// beside `a + b + 2 * c >= z1 - 8`, a row it implies, the solver alone refused every name, and
/// with the equation split it gave the exact sets `a=[3,4] b=[-1,-1] c=[0,1] z0=[2,2]
/// z1=[-3,0]`: the solver dropped the row (FAIL-pendants-split-writing-seed) but the search
/// above it did not. The writing of the formula now drops it (FAIL-pendants-sound-7683774971).
#[test]
fn an_equation_beside_a_row_it_implies_is_projected_as_when_split() {
    refused_names_in(7683774971210369151, 10, true);
}
