//! The benchmarks of `pncx_probe.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use zed_kernel::Term;
use zed_tests::step_helpers::l01_16_elaboration::elab;
use zed_tests::step_helpers::l01_38_presburger::pncx::*;
use zedc::store::preimage::Scoped;
use zedc::store::presburger::extend::Extending;

#[test]
fn pncx_distinct_moduli_scale() {
    use zedc::store::presburger::satisfiable;
    let inputs = zed_tests::scaling::inputs(4800, |n| pncx_formula("moduli", n));
    zed_tests::scaling::check_order("one-variable distinct moduli", 4800, 1, |n| {
        let ans = satisfiable(&inputs[&n]);
        assert!(ans.is_ok());
        let _ = std::hint::black_box(ans);
    });
}

#[test]
fn pncx_easy_pairs_scale() {
    use zedc::store::presburger::satisfiable;
    let inputs = zed_tests::scaling::inputs(2, |n| pncx_formula("pairs", n));
    zed_tests::scaling::check_order("separate remainder pairs", 2, 1, |n| {
        let ans = satisfiable(&inputs[&n]);
        assert!(matches!(ans, Ok(Some(_))));
        let _ = std::hint::black_box(ans);
    });
}

#[test]
fn pncx_sat_crt_construction_scale() {
    let inputs = zed_tests::scaling::inputs(3200, |n| {
        let mut ps = Vec::new();
        let mut p = 2i64;
        while ps.len() < n {
            if (2..).take_while(|d| d * d <= p).all(|d| p % d != 0) {
                ps.push(p);
            }
            p += 1;
        }
        let cl = [(n - 3, true), (n - 2, false), (n - 1, true)];
        (ps, cl)
    });
    zed_tests::scaling::check_order("construct SAT image residues by CRT", 3200, 1, |n| {
        let (ps, cl) = &inputs[&n];
        let residues: Vec<_> = (0..n).map(|_| pncx_sat_residue(ps, cl)).collect();
        std::hint::black_box(residues);
    });
}

/// Two consecutive Fibonacci moduli, the slowest case of the Euclidean extended gcd: the whole
/// question costs at most 10 times the kernel's gcd of the same two moduli, at F(80001) (55,540
/// bits) and F(750001) (520,682 bits). Measured 5.8 and 6.5 times with the half gcd; 190 times
/// at F(80001) with the Euclidean `bezout` (R6-CLAUDE-7). A scaling test cannot hold it: the
/// kernel's gcd alone on these numbers grows 17.5 times in instructions and 13.9 times in bytes
/// from F(750001) to F(6000001), above the limit of 13. Ignored for its time,
/// about 3 seconds.
#[test]
fn pncx_fibonacci_crt_scale() {
    use zedc::store::int::Num;
    use zedc::store::presburger::satisfiable;
    let mut meter = zed_tests::scaling::Meter::new();
    for n in [80_000, 750_000] {
        let f = pncx_crt_bits(n);
        let ms: Vec<num_bigint::BigUint> = f
            .cons()
            .iter()
            .flat_map(|c| c.lin.terms.values())
            .map(|k| Num::from(k).built().expect("written").magnitude().clone())
            .filter(|m| m.bits() > 64)
            .collect();
        let mut ans = None;
        let question = meter.work(|| ans = Some(satisfiable(&f)));
        let model = ans.expect("run").expect("answer").expect("a point");
        assert!(f.holds(&model));
        let mut g = None;
        let gcd = meter.work(|| g = Some(zed_kernel::num::gcd_uint(&ms[0], &ms[1])));
        assert!(g.expect("run") == num_bigint::BigUint::from(1u32));
        let ratio = question.units as f64 / gcd.units as f64;
        println!(
            "FIBCRT {n} question {} gcd {} ratio {ratio:.2}",
            question.units, gcd.units
        );
        assert!(
            ratio <= 10.0,
            "F({}): the question is {ratio:.2} gcds",
            n + 1
        );
    }
}

#[test]
fn pncx_disj_scale() {
    pncx_front_scale("disj", 1200);
}

#[test]
fn pncx_pairs_scale() {
    pncx_front_scale("pairs", 512);
}

#[test]
fn pncx_wide_divisor_translation_scale() {
    use zedc::store::int::Int;
    let inputs = zed_tests::scaling::inputs(42000, |n| {
        let mut m = Int::ONE;
        for _ in 0..n {
            m = &m + &m;
        }
        let src = format!("f(x: int) = x mod {} == 1;", &m + &Int::ONE);
        let unit = elab(&src).unwrap();
        let scope = lets(&unit);
        (unit, scope)
    });
    zed_tests::scaling::check_order("translate written wide divisors", 42000, 1, |n| {
        let (unit, scope) = &inputs[&n];
        let mut scoped = Scoped::new(scope);
        let Term::Lam(ps, body) = &*unit.defs[0].term else {
            panic!("one function")
        };
        let r = scoped
            .relation(body, ps, ps, true)
            .expect("wide divisor retains its question");
        let got = Extending::new().defined(&r, &|i| scoped.def(i));
        assert_eq!(got.holds, Ok(true));
        assert_eq!(got.fails, Ok(true));
    });
}
