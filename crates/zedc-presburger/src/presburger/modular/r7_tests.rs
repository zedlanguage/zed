//! Round-7 tests of the one-variable modular solver (PERF-negated-chain-xr).

use super::*;
use crate::scaling;

/// `x mod 3 == 2`, `0 <= x <= 10000`, and `n` atoms fixed one after another: `a_n == 1` and
/// `2 a_i == 2 a_(i+1)`, the rows written so that each pass of the constant propagation of
/// step 1 can fix only one more atom.
fn fixed_chain(n: usize) -> Formula {
    let atoms: Vec<_> = (0..=n)
        .map(|i| Atom::Sym(format!("f{i:06}").into()))
        .collect();
    let mut parts = Vec::new();
    for pair in atoms.windows(2) {
        parts.push(Formula::Con(Con::eq(
            &Lin::atom(pair[0].clone()).times(2),
            &Lin::atom(pair[1].clone()).times(2),
        )));
    }
    parts.push(Formula::Con(Con::eq(
        &Lin::atom(atoms[n].clone()),
        &Lin::constant(1),
    )));
    let x = Lin::atom(Atom::Sym("x".into()));
    let q = Lin::atom(Atom::Aux(0));
    let r = Lin::atom(Atom::Aux(1));
    parts.extend([
        Formula::Con(Con::eq(&x, &q.times(3).plus(&r))),
        Formula::Con(Con::ge(&r, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(2), &r)),
        Formula::Con(Con::eq(&r, &Lin::constant(2))),
        Formula::Con(Con::ge(&x, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(10000), &x)),
    ]);
    Formula::And(crate::presburger::Shared::new(parts))
}

#[test]
// A hand-run probe, not a test (PERF-negated-chain-unsolved: prints the work at four sizes, against
// no limit): built only with `--cfg zed_probes`; see [workspace.lints.rust] in the top Cargo.toml.
#[cfg(zed_probes)]
fn pncx_fixed_chain_axis() {
    let mut meter = scaling::Meter::new();
    for n in [64, 128, 256, 512] {
        let f = fixed_chain(n);
        let work = meter.work(|| {
            std::hint::black_box(solve_modular(&f, false));
        });
        println!(
            "FIXED_CHAIN n={n} answer={:?} work={} bytes={}",
            solve_modular(&f, false).map(|a| a.is_some()),
            work.units,
            work.bytes
        );
    }
}

#[test]
fn pncx_fixed_chain_scale() {
    let inputs = scaling::inputs(64, fixed_chain);
    scaling::check_order("atoms fixed one after another", 64, 1, |n| {
        assert!(matches!(solve_modular(&inputs[&n], false), Some(Some(_))));
    });
}

/// `2 p` for the first `n` odd primes `p`, as `r4_tests::shared_moduli`.
#[cfg(zed_probes)]
fn twice_primes(n: usize) -> Vec<Int> {
    let mut ms = Vec::new();
    let mut p = 3i64;
    while ms.len() < n {
        if (3..)
            .step_by(2)
            .take_while(|d| d * d <= p)
            .all(|d| p % d != 0)
        {
            ms.push(Int::from(2 * p));
        }
        p += 2;
    }
    ms
}

#[test]
// A hand-run probe, not a test (PERF-negated-chain-unsolved: prints the work at four sizes, against
// no limit): built only with `--cfg zed_probes`; see [workspace.lints.rust] in the top Cargo.toml.
#[cfg(zed_probes)]
fn pncx_common_factor_parts_axis() {
    let mut meter = scaling::Meter::new();
    for n in [512, 1024, 2048, 4096] {
        let ms = twice_primes(n);
        let bits: u64 = ms
            .iter()
            .map(|m| 64 - (m.to_string().parse::<u64>().unwrap_or(0)).leading_zeros() as u64)
            .sum();
        let mut g = Int::ZERO;
        let w_gcd = meter.work(|| {
            g = ms[0].clone();
            for m in &ms[1..] {
                g = g.gcd_recursive(m);
            }
        });
        let qs: Vec<Int> = ms.iter().map(|m| m.div_floor_wide(&g)).collect();
        let mut tree = Vec::new();
        let w_tree = meter.work(|| tree = product_tree(qs.clone()));
        let mut cof = Vec::new();
        let w_rem = meter.work(|| cof = cofactors_mod_leaves(&tree));
        let top = tree.len() - 2;
        let (v0, v1) = (tree[top][0].clone(), tree[top][1].clone());
        let root = tree[top + 1][0].clone();
        let mut sq = Int::ZERO;
        let w_mul = meter.work(|| sq = &v0 * &v0);
        let w_mul2 = meter.work(|| {
            std::hint::black_box(&v0 * &v1);
        });
        let w_div = meter.work(|| {
            std::hint::black_box(root.mod_floor_wide(&sq));
        });
        let w_div2 = meter.work(|| {
            std::hint::black_box(root.div_floor_wide(&v0));
        });
        println!(
            "TOP n={n} mul_sq={} mul={} rem_root_by_sq={} quot_root_by_v0={}",
            w_mul.units, w_mul2.units, w_div.units, w_div2.units
        );
        let w_check = meter.work(|| {
            std::hint::black_box(
                qs.iter()
                    .zip(&cof)
                    .all(|(q, c)| q.gcd_recursive(c) == Int::ONE),
            );
        });
        let w_all = meter.work(|| {
            std::hint::black_box(coprime_factorization(&ms.iter().cloned().collect()));
        });
        println!(
            "COMMON n={n} bits={bits} gcd={} tree={} rem={} check={} all={}",
            w_gcd.units, w_tree.units, w_rem.units, w_check.units, w_all.units
        );
    }
}

#[test]
// A hand-run probe, not a test (PERF-negated-chain-unsolved: prints the work at six widths, against
// no limit): built only with `--cfg zed_probes`; see [workspace.lints.rust] in the top Cargo.toml.
#[cfg(zed_probes)]
fn pncx_multiply_bytes_axis() {
    // Bytes and work of one product of two numbers of `w` words, at the widths of the
    // Fibonacci scale test (44 to 355 words) and of the common-factor tree (up to 970 words).
    let mut meter = scaling::Meter::new();
    for w in [44usize, 88, 177, 355, 710, 1420] {
        let mut a = Int::ONE;
        for _ in 0..w * 64 {
            a = &a + &a;
        }
        let a = &a - &Int::from(12345);
        let b = &a - &Int::from(999);
        let work = meter.work(|| {
            std::hint::black_box(&a * &b);
        });
        println!("MUL words={w} work={} bytes={}", work.units, work.bytes);
    }
}

/// `(x mod 6) mod 2 == 1 && 0 <= x <= 20`: `x = 6 q + r`, `r = 2 p + s`, the rows of the two
/// divisions in the order given by `inner_first`, and in the coordinates of `names`.
fn nested_remainder(inner_first: bool, names: [&str; 5]) -> Formula {
    let [x, q, r, p, s] = names.map(|n| Lin::atom(Atom::Sym(n.into())));
    let outer = vec![
        Formula::Con(Con::eq(&x, &q.times(6).plus(&r))),
        Formula::Con(Con::ge(&r, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(5), &r)),
    ];
    let inner = vec![
        Formula::Con(Con::eq(&r, &p.times(2).plus(&s))),
        Formula::Con(Con::ge(&s, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(1), &s)),
    ];
    let (a, b) = if inner_first {
        (inner, outer)
    } else {
        (outer, inner)
    };
    let mut parts = a;
    parts.extend(b);
    parts.extend([
        Formula::Con(Con::eq(&s, &Lin::constant(1))),
        Formula::Con(Con::ge(&x, &Lin::constant(0))),
        Formula::Con(Con::ge(&Lin::constant(20), &x)),
    ]);
    Formula::and(parts)
}

#[test]
fn nested_remainder_answers_do_not_depend_on_row_order() {
    // R7-CLAUDE-2: step 3 kept the first row that defines a remainder and skipped a later row
    // whose `x_root` an earlier row had defined. Each writing has the point x = 1.
    let mut got = Vec::new();
    for names in [
        ["x", "q", "r", "p", "s"],
        ["x", "a", "b", "c", "d"],
        ["z", "y", "w", "v", "u"],
    ] {
        for inner_first in [false, true] {
            let f = nested_remainder(inner_first, names);
            let answer = solve_modular(&f, true).map(|m| m.map(|m| f.holds(&m)));
            got.push((names[0], inner_first, answer));
        }
    }
    println!("NESTED {got:?}");
    assert!(got.iter().all(|g| g.2 == got[0].2), "{got:?}");
}
