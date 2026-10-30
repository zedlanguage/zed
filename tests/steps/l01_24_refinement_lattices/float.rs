//! Float classes, against the floats they hold.

use zedc::store::float::{FloatClass, Kind, Width};
use zedc::store::lattice::Lattice;

/// Floats of every kind and of each narrowest width.
const SAMPLES: [f64; 14] = [
    0.0,
    -0.0,
    1.5,
    -65504.0,
    65505.0,
    5.960464477539063e-8,  // 2^-24, the least f16 subnormal
    2.9802322387695312e-8, // 2^-25, an f32 and not an f16
    1e10,
    0.1,
    f64::MAX,
    f64::MIN_POSITIVE,
    f64::INFINITY,
    f64::NEG_INFINITY,
    f64::NAN,
];

/// Every class: each set of kinds at each width.
fn classes() -> Vec<FloatClass> {
    let kinds = [Kind::NegInf, Kind::Finite, Kind::PosInf, Kind::NaN];
    let mut out = Vec::new();
    for mask in 0..16u8 {
        let ks: Vec<Kind> = (0..4)
            .filter(|i| mask & (1 << i) != 0)
            .map(|i| kinds[i])
            .collect();
        for w in [Width::F16, Width::F32, Width::F64] {
            out.push(FloatClass::new(&ks, w));
        }
    }
    out
}

#[test]
fn each_float_has_its_narrowest_width() {
    let want = [
        Width::F16,
        Width::F16,
        Width::F16,
        Width::F16,
        Width::F32,
        Width::F16,
        Width::F32,
        Width::F32,
        Width::F64,
        Width::F64,
        Width::F64,
        Width::F16,
        Width::F16,
        Width::F16,
    ];
    for (x, w) in SAMPLES.iter().zip(want) {
        assert_eq!(Width::of(*x), w, "{x}");
    }
    // Each value is in its own class and in no narrower width's.
    for x in SAMPLES {
        let c = FloatClass::of(x);
        assert!(c.contains(x), "{x} is not in {c}");
        if Width::of(x) != Width::F16 {
            assert!(
                !FloatClass::width(Width::F16).contains(x),
                "{x} is not an f16"
            );
        }
    }
}

#[test]
fn meet_is_exact_and_join_holds_both_sides() {
    let all = classes();
    for a in &all {
        for b in &all {
            let (m, j) = (a.meet(b), a.join(b));
            assert_eq!(j, b.join(a));
            assert_eq!(a.widen(&j), j);
            assert_eq!(
                a.leq(b),
                all_in(a, b) || *a == FloatClass::bottom(),
                "{a} ⊑ {b}"
            );
            for x in SAMPLES {
                assert_eq!(
                    m.contains(x),
                    a.contains(x) && b.contains(x),
                    "{x}: {a} ⊓ {b} = {m}"
                );
                if a.contains(x) || b.contains(x) {
                    assert!(j.contains(x), "{x}: {a} ⊔ {b} = {j}");
                }
            }
        }
    }
}

/// Whether every sample in `a` is in `b`, and `a`'s width is within `b`'s.
fn all_in(a: &FloatClass, b: &FloatClass) -> bool {
    SAMPLES.iter().all(|&x| !a.contains(x) || b.contains(x)) && a.join(b) == *b
}

#[test]
fn the_facets_a_key_needs_read_off_the_class() {
    let finite = FloatClass::new(&[Kind::Finite], Width::F64);
    let no_nan = FloatClass::new(&[Kind::Finite, Kind::PosInf], Width::F32);
    assert!(finite.is_finite() && finite.excludes_nan());
    assert!(!no_nan.is_finite() && no_nan.excludes_nan());
    assert!(!FloatClass::top().excludes_nan());
    assert_eq!(no_nan.to_string(), "f32{finite, inf}");
    assert_eq!(FloatClass::of(f64::NAN).to_string(), "f16{nan}");
    assert_eq!(FloatClass::bottom().to_string(), "{}");
}
