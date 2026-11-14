//! The order in which the solver takes the variables (item CANON-stable): `colors` refines the
//! variables until the partition is stable, with no count of rounds that depends on the size,
//! and the colors depend on the structure of the rows only, not on the names. The solver takes
//! the variables breadth first over the rows, and the colors along that order do not depend on
//! the names either, except among variables of one color, where the names break the tie.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use zed_tests::instances::Rng;
use zedc::store::presburger::{self, Atom, Con, Lin, Rel};

fn var(name: &str) -> Atom {
    Atom::Sym(Arc::from(name))
}

/// `Σ k·x + c >= 0`, or `== 0` when `eq`, over the named variables.
fn row(terms: &[(&str, i128)], c: i128, eq: bool) -> Con {
    Con {
        lin: Lin {
            terms: terms.iter().map(|(a, k)| (var(a), (*k).into())).collect(),
            constant: c.into(),
        },
        rel: if eq { Rel::Eq } else { Rel::Ge },
    }
}

/// The colors of the variables of `cons`.
pub(super) fn colors(cons: &[Con]) -> BTreeMap<Atom, u64> {
    presburger::colors(cons).1
}

/// The variables of `cons` in the order the solver takes them.
fn order(cons: &[Con]) -> Vec<Atom> {
    presburger::colors(cons).0
}

fn names(n: usize, prefix: &str) -> Vec<String> {
    (0..n).map(|i| format!("{prefix}{i}")).collect()
}

/// A pipeline of `n` stages, `stage[i] + 2·stage[i+1] >= 1`: each stage is told apart from the
/// others by its distance from the two ends, which takes about n/2 rounds of comparison to see.
pub(super) fn pipeline(n: usize) -> Vec<Con> {
    let s = names(n, "stage");
    (0..n - 1)
        .map(|i| row(&[(&s[i], 1), (&s[i + 1], 2)], -1, false))
        .collect()
}

/// A ring of `n` buffers, `buf[i] + buf[i+1] <= 8` around the ring: every buffer is like every
/// other.
fn ring(n: usize) -> Vec<Con> {
    let b = names(n, "buf");
    (0..n)
        .map(|i| row(&[(&b[i], -1), (&b[(i + 1) % n], -1)], 8, false))
        .collect()
}

/// `rows` rows over `n` variables, each of two or three terms with coefficients in -3..=3,
/// constants in -4..=4, an equality one time in four.
pub(super) fn random(rng: &mut Rng, n: usize, rows: usize, prefix: &str) -> Vec<Con> {
    let v = names(n, prefix);
    (0..rows)
        .map(|_| {
            let mut t: BTreeMap<&str, i128> = BTreeMap::new();
            for _ in 0..2 + rng.below(2) {
                let k = rng.int(-3, 3) as i128;
                if k != 0 {
                    t.insert(&v[rng.below(n)], k);
                }
            }
            let t: Vec<(&str, i128)> = t.into_iter().collect();
            row(&t, rng.int(-4, 4) as i128, rng.below(4) == 0)
        })
        .collect()
}

fn distinct(c: &BTreeMap<Atom, u64>) -> usize {
    c.values().collect::<BTreeSet<_>>().len()
}

/// All k! permutations of 0..k, the j-th by the factorial digits of j.
fn permutations(k: usize) -> Vec<Vec<usize>> {
    let count: usize = (1..=k).product();
    let perms: Vec<Vec<usize>> = (0..count)
        .map(|mut j: usize| {
            let mut left: Vec<usize> = (0..k).collect();
            let mut p = Vec::new();
            for f in (1..=k).rev() {
                let fact: usize = (1..f).product();
                p.push(left.remove(j / fact));
                j %= fact;
            }
            p
        })
        .collect();
    assert_eq!(perms.iter().collect::<BTreeSet<_>>().len(), count);
    perms
}

/// `sys` with `base[i]` renamed to `base[p[i]]`, and its rows reversed.
fn renamed(sys: &[Con], base: &[String], p: &[usize]) -> (Vec<Con>, impl Fn(&Atom) -> Atom) {
    let rename = move |a: &Atom| match a {
        Atom::Sym(s) => {
            let i = base
                .iter()
                .position(|b| **b == **s)
                .expect("a named variable");
            var(&base[p[i]])
        }
        other => other.clone(),
    };
    let mut out: Vec<Con> = sys
        .iter()
        .map(|c| Con {
            lin: Lin {
                terms: c
                    .lin
                    .terms
                    .iter()
                    .map(|(a, k)| (rename(a), k.clone()))
                    .collect(),
                constant: c.lin.constant.clone(),
            },
            rel: c.rel,
        })
        .collect();
    out.reverse();
    (out, rename)
}

/// The colors of `sys` follow its variables under every renaming of `base` (with the rows
/// reversed too), and the colors along the solver's order stay the same.
fn same_colors_under_every_naming(sys: &[Con], base: &[String], perms: &[Vec<usize>]) {
    let first = colors(sys);
    let first_order: Vec<u64> = order(sys).iter().map(|a| first[a]).collect();
    for p in perms {
        let (other, rename) = renamed(sys, base, p);
        let got = colors(&other);
        let got_order: Vec<u64> = order(&other).iter().map(|a| got[a]).collect();
        assert_eq!(
            got_order, first_order,
            "{sys:?} renamed by {p:?}: the order"
        );
        for (a, k) in &first {
            assert_eq!(got[&rename(a)], *k, "{sys:?} renamed by {p:?}");
        }
    }
}

#[test]
fn every_stage_of_a_long_pipeline_gets_its_own_color() {
    // Control: the old count of rounds, log n + 1, gave 17 colors at 64 and 23 at 512.
    for n in [8, 64, 512] {
        let c = colors(&pipeline(n));
        assert_eq!(c.len(), n);
        assert_eq!(distinct(&c), n, "pipeline of {n} stages");
        // The solver takes the stages along the pipeline, from one end.
        let s: Vec<Atom> = names(n, "stage").iter().map(|x| var(x)).collect();
        let o = order(&pipeline(n));
        assert!(
            o == s || o.iter().rev().eq(&s),
            "pipeline of {n} stages: {o:?}"
        );
    }
}

#[test]
fn every_buffer_of_a_ring_keeps_one_color() {
    for n in [3, 64, 512] {
        let c = colors(&ring(n));
        assert_eq!(c.len(), n);
        assert_eq!(distinct(&c), 1, "ring of {n} buffers");
    }
    // A budget shared by k counts, each count at least 0: the counts are alike.
    let k = names(20, "count");
    let mut rows: Vec<Con> = k.iter().map(|x| row(&[(x, 1)], 0, false)).collect();
    let sum: Vec<(&str, i128)> = k.iter().map(|x| (x.as_str(), -1)).collect();
    rows.push(row(&sum, 49, false));
    assert_eq!(distinct(&colors(&rows)), 1);
}

#[test]
fn colors_do_not_depend_on_the_names_or_the_order_of_the_rows() {
    // Each system of five variables, under all 120 namings: a variable's color follows it, and
    // the colors along the order the solver takes the variables stay the same.
    let mut rng = Rng::new(0xCA_0001);
    let base = names(5, "x");
    let perms = permutations(5);
    let mut ties = 0;
    for _ in 0..40 {
        let rows = 2 + rng.below(5);
        let sys = random(&mut rng, 5, rows, "x");
        ties += usize::from(distinct(&colors(&sys)) < 5);
        same_colors_under_every_naming(&sys, &base, &perms);
    }
    // The renamings must reach systems where some variables share a color.
    assert!(ties > 0, "no system with a tie");
}

#[test]
fn coefficients_one_and_minus_two_are_told_apart() {
    // Codex's six-variable system from cross-review round 3: each row is `a·x + k >= 0`, with
    // every variable in -3..=3. A hash of the coefficients that sent 1 and -2 to one key gave
    // some of these variables one color; refinement by the coefficients themselves gives each
    // its own, under all 720 namings.
    let x = names(6, "x");
    let rows: [([i128; 6], i128); 6] = [
        ([0, -2, 1, 1, 0, 0], 0),
        ([-2, 1, 0, -2, 0, 0], 0),
        ([0, 0, -2, 0, -2, -2], -1),
        ([1, -2, 0, 0, 1, 0], -1),
        ([-2, 0, 0, -2, 0, 1], -1),
        ([0, 0, -2, 0, -2, -2], 0),
    ];
    let mut sys: Vec<Con> = rows
        .iter()
        .map(|(a, k)| {
            let t: Vec<(&str, i128)> = x
                .iter()
                .zip(a)
                .filter(|(_, k)| **k != 0)
                .map(|(v, k)| (v.as_str(), *k))
                .collect();
            row(&t, *k, false)
        })
        .collect();
    for v in &x {
        sys.push(row(&[(v, 1)], 3, false));
        sys.push(row(&[(v, -1)], 3, false));
    }
    assert_eq!(distinct(&colors(&sys)), 6);
    same_colors_under_every_naming(&sys, &x, &permutations(6));
    // The smallest case: one row with coefficients 1 and -2.
    assert_eq!(
        distinct(&colors(&[row(&[("a", 1), ("b", -2)], 0, false)])),
        2
    );
}

/// The partition of the variables that rounds of plain refinement reach when run until the
/// number of classes stops rising: a row's signature is its relation, constant and multiset of
/// (coefficient, variable class); a variable's is its class and multiset of (row class,
/// coefficient). Classes are numbered by sorting the signatures. Each variable maps to the least
/// variable of its class.
fn plain_refinement(cons: &[Con]) -> BTreeMap<Atom, Atom> {
    let vars: Vec<Atom> = cons
        .iter()
        .flat_map(|c| c.lin.terms.keys().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let mut class: BTreeMap<Atom, usize> = vars.iter().map(|a| (a.clone(), 0)).collect();
    let mut count = 1;
    loop {
        let row_sigs: Vec<_> = cons
            .iter()
            .map(|c| {
                let mut t: Vec<_> = c
                    .lin
                    .terms
                    .iter()
                    .map(|(a, k)| (k.clone(), class[a]))
                    .collect();
                t.sort();
                (c.rel, c.lin.constant.clone(), t)
            })
            .collect();
        let sorted: BTreeSet<_> = row_sigs.iter().collect();
        let row_class: Vec<usize> = row_sigs
            .iter()
            .map(|s| sorted.iter().position(|t| *t == s).expect("a signature"))
            .collect();
        let mut var_sigs: BTreeMap<&Atom, (usize, Vec<(usize, _)>)> =
            vars.iter().map(|a| (a, (class[a], Vec::new()))).collect();
        for (c, r) in cons.iter().zip(&row_class) {
            for (a, k) in &c.lin.terms {
                var_sigs
                    .get_mut(a)
                    .expect("a variable")
                    .1
                    .push((*r, k.clone()));
            }
        }
        for s in var_sigs.values_mut() {
            s.1.sort();
        }
        let sorted: BTreeSet<_> = var_sigs.values().collect();
        let next: BTreeMap<Atom, usize> = var_sigs
            .iter()
            .map(|(a, s)| {
                (
                    (*a).clone(),
                    sorted.iter().position(|t| *t == s).expect("a signature"),
                )
            })
            .collect();
        let rising = sorted.len() > count;
        count = sorted.len();
        class = next;
        if !rising {
            break;
        }
    }
    let mut first: BTreeMap<usize, Atom> = BTreeMap::new();
    for (a, c) in &class {
        first.entry(*c).or_insert_with(|| a.clone());
    }
    class
        .iter()
        .map(|(a, c)| (a.clone(), first[c].clone()))
        .collect()
}

#[test]
fn the_partition_is_the_one_plain_refinement_reaches() {
    let mut rng = Rng::new(0xCA_0003);
    for i in 0..300 {
        let n = 2 + rng.below(12);
        let rows = 1 + rng.below(2 * n);
        let sys = random(&mut rng, n, rows, "y");
        let c = colors(&sys);
        let mut first: BTreeMap<u64, Atom> = BTreeMap::new();
        for (a, k) in &c {
            first.entry(*k).or_insert_with(|| a.clone());
        }
        let got: BTreeMap<Atom, Atom> = c
            .iter()
            .map(|(a, k)| (a.clone(), first[k].clone()))
            .collect();
        assert_eq!(got, plain_refinement(&sys), "system {i}: {sys:?}");
    }
    let sys = pipeline(40);
    assert_eq!(distinct(&colors(&sys)), 40);
}

#[test]
fn corner_cases() {
    // No rows, and rows with no variables.
    assert!(colors(&[]).is_empty());
    assert!(colors(&[row(&[], 3, false), row(&[], 0, true)]).is_empty());
    // One variable.
    let one = colors(&[row(&[("n", 1)], 0, false)]);
    assert_eq!(one.len(), 1);
    // Duplicate rows: as many copies of every row change no color class.
    let sys = pipeline(30);
    let twice: Vec<Con> = sys.iter().chain(sys.iter()).cloned().collect();
    assert_eq!(distinct(&colors(&twice)), 30);
    // Two variables alike in a row written twice stay alike.
    let pair = row(&[("lo", 1), ("hi", 1)], -2, false);
    let c = colors(&[pair.clone(), pair]);
    assert_eq!(distinct(&c), 1);
    // The coefficient and the relation tell variables apart.
    let c = colors(&[row(&[("a", 1), ("b", 2)], 0, false)]);
    assert_eq!(distinct(&c), 2);
    let c = colors(&[row(&[("a", 1)], 0, true), row(&[("b", 1)], 0, false)]);
    assert_eq!(distinct(&c), 2);
}
