//! The elimination of unit equalities from a system of integer rows: each equality with a
//! coefficient `±1`, or with one term only, is solved for that atom, and the atom is substituted
//! out of every other row. This is the Gauss–Jordan step on the unit pivots, which keeps every
//! row integer; an equality whose pivots are all non-units is left as it is. Moved from
//! zedc-presburger `two_var_domains` (its one caller; DRY-affine-crate-2026-11-26, batch 4),
//! where the bound on the size of the numbers it makes stays, with that function's cost proof.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::hash::Hash;

use zed_graph::{Order, Worklist};
use zedc_int::int::Int;

/// A row `Σ t_x·x + k`, as its terms and constant; an equality means `== 0`, an inequality
/// `>= 0`.
pub type Row<K> = (BTreeMap<K, Int>, Int);

/// What [`eliminate_units`] found.
#[derive(Debug, PartialEq, Eq)]
pub enum Eliminated<K> {
    /// The rows have no integer point: an equality became a nonzero constant, or a single-atom
    /// equality `a·x + k == 0` has `a ∤ k`.
    Empty,
    /// The atoms solved for, in order, each with the row it equals: terms over the atoms present
    /// when it was solved, and a constant (no terms for a single-atom equality).
    Solved(Vec<(K, Row<K>)>),
}

/// Solves the equalities `eq` for their unit atoms (and single-atom equalities for their atom),
/// never for `keep`, and substitutes each solved atom out of the other rows of `eq` and of the
/// inequalities `ge`, in place. A used equality is left as the empty row `0`. `charge` is called
/// with the terms of each substitution into a row (plus one) before it is made; its error is
/// returned at once, with the rows part rewritten.
///
/// Which equality is used, and how, depends on its own terms alone: a single-atom `a·x + k`
/// with `x != keep` gives `x = -k / a` (no point unless `a | k`), else the first term
/// `±1·x` with `x != keep` gives `x = ∓(Σ_(y != x) t_y·y + k)` (`1 / a = a` for `a = ±1`).
///
/// Complexity tradeoff (XR-l139-neon-r4, found by AUDIT-kept-rows, b22-research3): the naive
/// version made passes over every equality until one changed nothing, each substitution reading
/// every row: `O(e·r)` rows read for `e` equalities and `r` rows even when each atom is in two
/// rows, quadratic on the chain `x_i == x_(i+1) + 1` of zedc-presburger's
/// `two_var_tests::bench::a_chain_of_unit_equalities_scales`. Used: the rows holding each atom
/// (`holds`), so a substitution reads only the rows that hold its atom, and a work list of
/// equalities, which takes an equality again only after a substitution changed it. As an
/// equality's use depends on its own terms alone, an equality left unchanged since it was last
/// read is still unused, and the list stops at the fixed point the passes stopped at. A
/// substitution costs `O(t log a)` for each row holding its atom (`t` terms in its equality,
/// `a` atoms), so the chain costs `O(e log e)`; the general bound is the cost proof at
/// zedc-presburger's `two_var_domains`.
pub fn eliminate_units<K: Ord + Clone + Hash, E>(
    eq: &mut [Row<K>],
    ge: &mut [Row<K>],
    keep: Option<&K>,
    mut charge: impl FnMut(u64) -> Result<(), E>,
) -> Result<Eliminated<K>, E> {
    let ne = eq.len();
    let mut holds: HashMap<K, BTreeSet<usize>> = HashMap::new();
    for (j, row) in eq.iter().chain(ge.iter()).enumerate() {
        for x in row.0.keys() {
            holds.entry(x.clone()).or_default().insert(j);
        }
    }
    let mut work = Worklist::all(ne, Order::Fifo);
    let mut pivots: Vec<(K, Row<K>)> = Vec::new();
    while let Some(i) = work.pop() {
        if eq[i].0.is_empty() {
            if !eq[i].1.is_zero() {
                return Ok(Eliminated::Empty);
            }
            continue;
        }
        let single = eq[i].0.len() == 1;
        let free = |x: &K| keep != Some(x);
        let pick = if single {
            let (x, a) = eq[i].0.iter().next().expect("one term");
            free(x).then(|| (x.clone(), a.clone()))
        } else {
            (eq[i].0.iter())
                .find(|(x, a)| free(x) && a.abs() == Int::ONE)
                .map(|(x, a)| (x.clone(), a.clone()))
        };
        let Some((x, a)) = pick else {
            continue;
        };
        let val = if single {
            let k = &eq[i].1;
            if !k.mod_floor(&a).is_zero() {
                return Ok(Eliminated::Empty);
            }
            Some(-&k.div_floor(&a))
        } else {
            None
        };
        let (t, k) = std::mem::take(&mut eq[i]);
        pivots.push(match &val {
            Some(v) => (x.clone(), (BTreeMap::new(), v.clone())),
            None => (
                x.clone(),
                (
                    (t.iter().filter(|(y, _)| **y != x))
                        .map(|(y, v)| (y.clone(), -&(&a * v)))
                        .collect(),
                    -&(&a * &k),
                ),
            ),
        });
        for y in t.keys() {
            if let Some(set) = holds.get_mut(y) {
                set.remove(&i);
            }
        }
        let holders = holds.remove(&x).unwrap_or_default();
        for j in holders {
            let row = if j < ne { &mut eq[j] } else { &mut ge[j - ne] };
            let Some(m) = row.0.remove(&x) else {
                continue;
            };
            if let Some(val) = &val {
                row.1 = &row.1 + &(&m * val);
            } else {
                charge(t.len() as u64 + 1)?;
                let f = -&(&m * &a);
                for (y, v) in t.iter().filter(|(y, _)| **y != x) {
                    let s = &row.0.remove(y).unwrap_or(Int::ZERO) + &(&f * v);
                    let set = holds.entry(y.clone()).or_default();
                    if s.is_zero() {
                        set.remove(&j);
                    } else {
                        row.0.insert(y.clone(), s);
                        set.insert(j);
                    }
                }
                row.1 = &row.1 + &(&f * &k);
            }
            if j < ne {
                work.push(j);
            }
        }
    }
    Ok(Eliminated::Solved(pivots))
}
