//! Which products of pairs of factor rows [`super::products`] forms (plan row C2-pairs-exact).
//!
//! Each product `p ⊗ q >= 0` of two linear rows `p >= 0`, `q >= 0` is read linearly, each
//! product atom `w * z` its own integer atom. An atom the formulas do not mention (no premise,
//! goal or definition holds it) is held only by product rows. When one product row is the only
//! live one holding such an atom with a nonzero coefficient, that row is dropped: whatever
//! point satisfies the other rows, the atom can be given a value of the sign of its coefficient
//! and large enough that the row holds too, since nothing else reads it. Dropped rows are
//! justified in the reverse of the order they go, each by the atom it alone held when it went,
//! so the verdict of the linear reading is the one all the products give, over the integers.
//! The rule is monotone (a row that can go can still go once others have gone), so the rows
//! left do not depend on the order of the tests or on names.
//!
//! The coefficient of `w * z` in `p ⊗ q` is `p_w q_z + p_z q_w`, and `p_w q_w` for `w * w`. A
//! pair is tested from its factor rows without expanding the product: for each `w` of the
//! shorter row `q`, the `z` of the longer row `p` that do not give a free atom `w * z` are
//! collected, and the pair goes when they are fewer than the variables of `p`.

use std::collections::{HashMap, HashSet, VecDeque};

use zedc_int::int::Int;

use super::formula::{Factor, Lin};

/// Whether each of `pairs`, the unordered pairs of indices into `rows`, is kept: the pairs left
/// when every pair whose product alone holds an atom with no entry in `partners` (the factors
/// each factor is multiplied by in a product the formulas mention) is dropped, to a fixpoint.
///
/// Complexity tradeoff: the naive method expands every product, Σ |p| × |q| terms over the
/// pairs, Θ(k²) for one row of k factors paired with a row on each of them, such as one sum
/// `b0 + ... + b{k-1}` beside the products `b{i} * c{i}` (33.5 times the instructions at 8
/// times the links, C2-pairs-long-row), and then counts the holders of each atom again after
/// each round of drops, O(rounds × Σ |p| × |q|). Here no product is expanded. The test of a
/// pair `{p, q}`, `|q| <= |p|`, tries each `w` of `q`, those on the fewest pairs first, and
/// stops at the first that frees an atom; for one `w` it costs O(|q| × log) for the atoms that
/// cancel inside `p ⊗ q`, O(min(|p|, partners of w) × log) for those mentioned, and for each
/// live pair `{r, s}` with `r` holding `w`, O(log) when `s` is `p` and `p` does not hold `w`
/// (then `r ⊗ p` holds every `w * z`), and otherwise O(min(|s|, |p|) × log) for the variables
/// `s` and `p` share. After its first test a pair is tested again only when a pair that held
/// one of its atoms at its last test is dropped, so each drop costs a test of the pairs that
/// share an atom with it, and each pair is tested at most once more than the number of its
/// blockers that go. On the family the sum is only ever `p`, each `w` is on a constant number
/// of pairs, and the whole costs O(k log k). In general it is not O(n log n): many long rows
/// that share variables cost O(|s| × |p|) for each pair read, and no bound better than the
/// products themselves is known for that case. Tests:
/// `tests::the_pairs_kept_are_those_left_by_expanding_every_product` (against the naive
/// method) and `l01_38_presburger::ladder::products_whose_factors_one_sum_on_the_factors_joins_scale`.
pub(super) fn kept(
    rows: &[&Lin],
    pairs: &[(usize, usize)],
    partners: &HashMap<Factor, Vec<Factor>>,
) -> Vec<bool> {
    let index = Index::new(rows, pairs, partners);
    let n = pairs.len();
    let mut live = vec![true; n];
    let mut queued = vec![true; n];
    let mut queue: VecDeque<usize> = (0..n).collect();
    // The pairs that each pair blocked at their last test, to test again when it goes.
    let mut watch: Vec<Vec<usize>> = vec![Vec::new(); n];
    while let Some(e) = queue.pop_front() {
        queued[e] = false;
        if live[e] && index.frees(e, &live, &mut watch) {
            live[e] = false;
            for f in std::mem::take(&mut watch[e]) {
                if live[f] && !queued[f] {
                    queued[f] = true;
                    queue.push_back(f);
                }
            }
        }
    }
    live
}

/// The factor rows and pairs of [`kept`], with each factor numbered.
struct Index<'a> {
    /// Each row's variables, by number, ascending, with their coefficients.
    vars: Vec<Vec<(usize, &'a Int)>>,
    pairs: &'a [(usize, usize)],
    /// The rows holding each variable.
    holding: Vec<Vec<usize>>,
    /// Each row's partners in a pair, with the pair.
    opp: Vec<Vec<(usize, usize)>>,
    /// The number of pairs on the rows holding each variable: the order in which the variables
    /// of a row are tried.
    weight: Vec<usize>,
    /// The variables each variable is multiplied by in a product the formulas mention,
    /// ascending.
    mentioned: Vec<Vec<usize>>,
}

impl<'a> Index<'a> {
    fn new(
        rows: &[&'a Lin],
        pairs: &'a [(usize, usize)],
        partners: &HashMap<Factor, Vec<Factor>>,
    ) -> Index<'a> {
        let mut number: HashMap<Factor, usize> = HashMap::new();
        let mut holding: Vec<Vec<usize>> = Vec::new();
        let vars: Vec<Vec<(usize, &Int)>> = rows
            .iter()
            .enumerate()
            .map(|(r, row)| {
                let mut vs: Vec<(usize, &Int)> = row
                    .terms
                    .iter()
                    .filter_map(|(a, c)| {
                        let f = Factor::of(a)?;
                        let next = number.len();
                        let v = *number.entry(f).or_insert(next);
                        if v == holding.len() {
                            holding.push(Vec::new());
                        }
                        holding[v].push(r);
                        Some((v, c))
                    })
                    .collect();
                vs.sort_unstable_by_key(|&(v, _)| v);
                vs
            })
            .collect();
        let mut opp: Vec<Vec<(usize, usize)>> = vec![Vec::new(); rows.len()];
        for (e, &(p, q)) in pairs.iter().enumerate() {
            opp[p].push((q, e));
            if p != q {
                opp[q].push((p, e));
            }
        }
        let weight = holding
            .iter()
            .map(|rs| rs.iter().map(|&r| opp[r].len()).sum())
            .collect();
        let mut mentioned: Vec<Vec<usize>> = vec![Vec::new(); holding.len()];
        for (u, ps) in partners {
            if let Some(&u) = number.get(u) {
                mentioned[u] = ps.iter().filter_map(|p| number.get(p).copied()).collect();
                mentioned[u].sort_unstable();
            }
        }
        Index {
            vars,
            pairs,
            holding,
            opp,
            weight,
            mentioned,
        }
    }

    /// The coefficient of `w` in row `r`, zero when it has none.
    fn coef(&self, r: usize, w: usize) -> Option<&'a Int> {
        let vs = &self.vars[r];
        vs.binary_search_by_key(&w, |&(v, _)| v)
            .ok()
            .map(|i| vs[i].1)
    }

    /// Whether the coefficient of `w * z` in `r ⊗ s` is not zero.
    fn holds(&self, r: usize, s: usize, w: usize, z: usize) -> bool {
        let times = |a: usize, b: usize| match (self.coef(r, a), self.coef(s, b)) {
            (Some(x), Some(y)) => x * y,
            _ => Int::ZERO,
        };
        if w == z {
            !times(w, w).is_zero()
        } else {
            !(&times(w, z) + &times(z, w)).is_zero()
        }
    }

    /// The variables of `p` that `s` holds too, through the shorter of the two.
    fn shared(&self, s: usize, p: usize) -> Vec<usize> {
        let (short, long) = if self.vars[s].len() <= self.vars[p].len() {
            (s, p)
        } else {
            (p, s)
        };
        (self.vars[short].iter())
            .map(|&(v, _)| v)
            .filter(|&v| self.coef(long, v).is_some())
            .collect()
    }

    /// Whether the live pair `e` alone holds an atom `w * z` that the formulas do not mention,
    /// against the live pairs `live`; when it does not, `e` is entered in `watch` under each
    /// pair found to hold one of its atoms.
    fn frees(&self, e: usize, live: &[bool], watch: &mut [Vec<usize>]) -> bool {
        let (a, b) = self.pairs[e];
        let (q, p) = if self.vars[a].len() <= self.vars[b].len() {
            (a, b)
        } else {
            (b, a)
        };
        let width = self.vars[p].len();
        let mut ws: Vec<usize> = self.vars[q].iter().map(|&(w, _)| w).collect();
        ws.sort_by_key(|&w| (self.weight[w], w));
        'w: for w in ws {
            // The `z` of `p` for which `w * z` is not free.
            let mut not: HashSet<usize> = HashSet::new();
            let ms = &self.mentioned[w];
            if ms.len() <= width {
                not.extend(ms.iter().filter(|&&z| self.coef(p, z).is_some()));
            } else {
                not.extend(self.vars[p].iter().map(|&(z, _)| z));
                not.retain(|z| ms.binary_search(z).is_ok());
            }
            // Only for `z` held by `q` too can the coefficient in `e` be zero.
            not.extend(
                (self.vars[q].iter())
                    .map(|&(z, _)| z)
                    .filter(|&z| self.coef(p, z).is_some() && !self.holds(p, q, w, z)),
            );
            let p_holds_w = self.coef(p, w).is_some();
            for &r in &self.holding[w] {
                for &(s, f) in &self.opp[r] {
                    if f == e || !live[f] {
                        continue;
                    }
                    if s == p && !p_holds_w {
                        // `r ⊗ p` holds `w * z` with the coefficient `r_w p_z` for every `z`.
                        watch[f].push(e);
                        continue 'w;
                    }
                    for z in self.shared(s, p) {
                        if !not.contains(&z) && self.holds(r, s, w, z) {
                            not.insert(z);
                            watch[f].push(e);
                            if not.len() == width {
                                continue 'w;
                            }
                        }
                    }
                }
            }
            if not.len() < width {
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::super::formula::{Atom, Factor, Lin};
    use super::kept;

    /// The pairs kept, found by expanding every product: each round drops every live pair
    /// that alone holds an atom with no entry in `partners`, until a round drops none.
    fn expanded(
        rows: &[&Lin],
        pairs: &[(usize, usize)],
        partners: &HashMap<Factor, Vec<Factor>>,
    ) -> Vec<bool> {
        let free = |a: &Atom| match a {
            Atom::Product(u, v) => !partners.get(u).is_some_and(|ps| ps.contains(v)),
            _ => false,
        };
        let products: Vec<Lin> = (pairs.iter())
            .map(|&(a, b)| rows[a].product(rows[b]).expect("linear rows"))
            .collect();
        let atoms: Vec<Vec<&Atom>> = (products.iter())
            .map(|p| {
                (p.terms.iter())
                    .filter(|&(a, c)| !c.is_zero() && free(a))
                    .map(|(a, _)| a)
                    .collect()
            })
            .collect();
        let mut live = vec![true; pairs.len()];
        loop {
            let mut holders: HashMap<&Atom, usize> = HashMap::new();
            for (e, held) in atoms.iter().enumerate() {
                if live[e] {
                    for &a in held {
                        *holders.entry(a).or_default() += 1;
                    }
                }
            }
            let drop: Vec<usize> = (0..pairs.len())
                .filter(|&e| live[e] && atoms[e].iter().any(|&a| holders[a] == 1))
                .collect();
            if drop.is_empty() {
                return live;
            }
            for e in drop {
                live[e] = false;
            }
        }
    }

    /// The row `constant + Σ c × name`.
    fn row(constant: i64, terms: &[(i64, &str)]) -> Lin {
        let mut l = Lin::constant(constant);
        for &(c, name) in terms {
            l.plus_assign(&Lin::atom(Atom::Sym(name.into())).times(c));
        }
        l
    }

    /// The partners of the products `u * v` of `products`, both ways.
    fn partners_of(products: &[(&str, &str)]) -> HashMap<Factor, Vec<Factor>> {
        let mut partners: HashMap<Factor, Vec<Factor>> = HashMap::new();
        for &(u, v) in products {
            let (u, v) = (Factor::Sym(u.into()), Factor::Sym(v.into()));
            partners.entry(u.clone()).or_default().push(v.clone());
            partners.entry(v).or_default().push(u);
        }
        for ps in partners.values_mut() {
            ps.sort();
            ps.dedup();
        }
        partners
    }

    #[test]
    fn an_atom_held_by_two_products_of_different_pairs_keeps_both() {
        // `c * d` is in `(1 - a - d) * (1 + a - b + c)` and in `(-a - b - d) * (-c)`, the
        // products for `a * b` and for `b * c`; every other atom of the two is mentioned or
        // cancels against a third product, so all four are kept, as the proof of
        // `l01_38_presburger::ladder::a_product_atom_cancels_through_the_products_of_another_pair`
        // needs.
        let rows = [
            row(1, &[(-1, "a"), (-1, "d")]),
            row(1, &[(1, "a"), (-1, "b"), (1, "c")]),
            row(0, &[(1, "b"), (-1, "a")]),
            row(0, &[(-1, "a"), (-1, "b"), (-1, "d")]),
            row(0, &[(-1, "c")]),
        ];
        let rows: Vec<&Lin> = rows.iter().collect();
        let pairs = [(0, 1), (2, 3), (3, 4), (4, 4)];
        let partners = partners_of(&[("a", "b"), ("b", "b"), ("b", "c"), ("c", "c")]);
        assert_eq!(kept(&rows, &pairs, &partners), [true; 4]);
        assert_eq!(expanded(&rows, &pairs, &partners), [true; 4]);
        // Without the product of `-a - b - d` and `-c`, `(1 - a - d) * (1 + a - b + c)` alone
        // holds `c * d`, and then `(b - a) * (-a - b - d)` alone holds `a * d`.
        assert_eq!(
            kept(&rows, &[(0, 1), (2, 3), (4, 4)], &partners),
            [false, false, true]
        );
    }

    #[test]
    fn an_atom_whose_coefficient_is_zero_frees_nothing() {
        // `(x + y) * (x - y)` is `x * x - y * y`: `x * y` cancels inside it, so with both
        // squares mentioned it is kept; with `y * y` not mentioned it goes.
        let rows = [
            row(0, &[(1, "x"), (1, "y")]),
            row(0, &[(1, "x"), (-1, "y")]),
        ];
        let rows: Vec<&Lin> = rows.iter().collect();
        let both = partners_of(&[("x", "x"), ("y", "y")]);
        assert_eq!(kept(&rows, &[(0, 1)], &both), [true]);
        let one = partners_of(&[("x", "x")]);
        assert_eq!(kept(&rows, &[(0, 1)], &one), [false]);
    }

    #[test]
    fn the_pairs_kept_are_those_left_by_expanding_every_product() {
        // Random rows over a few symbols, random pairs and random mentioned products, the
        // pairs given in a random order: `kept` agrees with `expanded`, so its answer does not
        // depend on the order of the pairs.
        let mut s = 0x2545_f491_4f6c_dd1d_u64;
        let mut next = move |n: u64| {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s % n
        };
        let names = ["a", "b", "c", "d", "e", "f"];
        let mut dropped = 0;
        for case in 0..4000 {
            let nv = 3 + next(4) as usize;
            let rows: Vec<Lin> = (0..2 + next(5))
                .map(|_| {
                    let terms: Vec<(i64, &str)> = (0..1 + next(4))
                        .map(|_| {
                            (
                                [-2, -1, 1, 1, 2][next(5) as usize],
                                names[next(nv as u64) as usize],
                            )
                        })
                        .collect();
                    row(next(5) as i64 - 2, &terms)
                })
                .filter(|r| !r.terms.is_empty())
                .collect();
            let n = rows.len();
            if n == 0 {
                continue;
            }
            let mut pairs: Vec<(usize, usize)> = Vec::new();
            for a in 0..n {
                for b in a..n {
                    if next(3) != 0 {
                        pairs.push((a, b));
                    }
                }
            }
            for i in (1..pairs.len()).rev() {
                pairs.swap(i, next(i as u64 + 1) as usize);
            }
            let products: Vec<(&str, &str)> = (0..next(5))
                .map(|_| {
                    (
                        names[next(nv as u64) as usize],
                        names[next(nv as u64) as usize],
                    )
                })
                .collect();
            let partners = partners_of(&products);
            let rows: Vec<&Lin> = rows.iter().collect();
            let want = expanded(&rows, &pairs, &partners);
            assert_eq!(
                kept(&rows, &pairs, &partners),
                want,
                "case {case}: rows {rows:?}, pairs {pairs:?}, products {products:?}"
            );
            dropped += want.iter().filter(|&&k| !k).count();
        }
        assert!(dropped > 0, "no case dropped a pair");
    }
}
