//! Integer and order edges (plan row TESTS-L1.17-wide-edges): `i64::MIN` under `div -1`,
//! `mod -1`, `* -1`, `-` and `abs`, with results that narrow back to one machine word; the
//! zeros, NaN and the subnormals under the language's comparisons, `min` and `max`, and the
//! natural order; and `sum` of the empty tuple. Every expected value is taken from DESIGN.md,
//! whose sentence each test quotes. The group has no native comparison, so these run in the
//! kernel evaluator only. The float literals are plain decimals, each an `f64` by the rule of
//! LIT-plain; step L1.26b gives `0.0` the format f16 and adds the suffix `f64`, which these
//! literals then need to stay one format. NaN and the infinities are written as quotients, since
//! the casts `f64(#NaN)` and `f64(#inf)` of DESIGN come with plan row NAN-cast-atoms.

use zed_kernel::Value;

use zed_tests::step_helpers::l01_16_elaboration::{elab, errors, value, with_prelude};
use zed_tests::step_helpers::l01_26_type_resolution::info;

/// The values of the definitions `names` of `src`.
fn values(src: &str, names: &[&str]) -> Vec<Value> {
    let u = elab(src).unwrap();
    names
        .iter()
        .map(|n| zed_kernel::eval(&with_prelude(u.get(n).unwrap())).unwrap())
        .collect()
}

const MIN: &str = "lo = -9223372036854775808;\n";

// DESIGN.md L1.17: "an integer is one machine word while it fits and a big integer beyond,
// so arithmetic widens instead of failing". DESIGN.md sec:domains: "`div`/`mod` on integers
// are **Euclidean**: `a = b·(a div b) + (a mod b)` with `0 ≤ a mod b < |b|`".
#[test]
fn the_smallest_word_widens_under_negation_and_narrows_back() {
    let src = format!(
        "{MIN}q = lo div -1;\nr = lo mod -1;\np = lo * -1;\nn = -lo;\na = abs(lo);\n\
         qBack = q - 1;\npBack = p * -1;\nnBack = -n;\naBack = -a;\nwhole = q * -1 + r;\n"
    );
    let wide = "9223372036854775808";
    let cases = [
        ("q", wide),
        ("r", "0"),
        ("p", wide),
        ("n", wide),
        ("a", wide),
        ("qBack", "9223372036854775807"),
        ("pBack", "-9223372036854775808"),
        ("nBack", "-9223372036854775808"),
        ("aBack", "-9223372036854775808"),
        ("whole", "-9223372036854775808"),
    ];
    for (name, want) in cases {
        assert_eq!(value(&src, name), want, "{name}");
    }
    // Past a word the value is a big integer, and back inside it is one word again.
    let names: Vec<&str> = cases.iter().map(|c| c.0).collect();
    for (name, v) in names.iter().zip(values(&src, &names)) {
        let fits = !matches!(*name, "q" | "p" | "n" | "a");
        assert_eq!(matches!(v, Value::Int(_)), fits, "{name} is {v:?}");
        assert_eq!(matches!(v, Value::Big(_)), !fits, "{name} is {v:?}");
    }
    // Arithmetic widens instead of failing, so no result's type holds a failure atom.
    let i = info(&src).0;
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    for name in names {
        let t = i.tops[name].to_string();
        assert!(!t.contains('#'), "{name}: {t}");
    }
}

// The same rule at the other divisors near -1, and the identity on each: the remainder is
// at least 0 and below |b|.
#[test]
fn the_smallest_word_divides_euclidean_by_small_negative_divisors() {
    let src = format!(
        "{MIN}q2 = lo div -2;\nr2 = lo mod -2;\no = lo + 1;\nq3 = o div -2;\nr3 = o mod -2;\n\
         q4 = o div -1;\nr4 = o mod -1;\nq5 = lo div 1;\nr5 = lo mod 1;\n\
         back2 = q2 * -2 + r2 == lo;\nback3 = q3 * -2 + r3 == o;\n"
    );
    let cases = [
        ("q2", "4611686018427387904"),
        ("r2", "0"),
        ("q3", "4611686018427387904"),
        ("r3", "1"),
        ("q4", "9223372036854775807"),
        ("r4", "0"),
        ("q5", "-9223372036854775808"),
        ("r5", "0"),
        ("back2", "true"),
        ("back3", "true"),
    ];
    for (name, want) in cases {
        assert_eq!(value(&src, name), want, "{name}");
    }
    let vs = values(&src, &["q2", "q3", "q4", "q5"]);
    assert!(vs.iter().all(|v| matches!(v, Value::Int(_))), "{vs:?}");
}

// DESIGN.md sec:failure: "`x div y : int | #divByZero`"; the
// smallest word is no exception.
#[test]
fn the_smallest_word_divided_by_zero_is_div_by_zero() {
    let src =
        format!("{MIN}whole(positional v: int) = v;\nq = lo div whole(0);\nr = lo mod whole(0);\n");
    for name in ["q", "r"] {
        assert_eq!(value(&src, name), "#divByZero", "{name}");
        let t = info(&src).0.tops[name].to_string();
        assert!(t.contains("#divByZero"), "{name}: {t}");
    }
}

// DESIGN.md sec:type_resolution: "The orders follow IEEE as well: `-0.0 < 0.0` is false and
// `-0.0 <= 0.0` is true, and a tuple compares component by component in that order, so
// `(-0.0, 1) < (0.0, 0)` is false." DESIGN.md L1.17: "`<`, `<=`, `>`, `>=` are IEEE 754 on
// two floats".
#[test]
fn the_two_zeros_compare_equal_under_ieee() {
    let src = "z = 0.0f64;\nm = -0.0f64;\nlt = m < z;\nle = m <= z;\ngt = z > m;\nge = z >= m;\n\
               eq = m == z;\nne = m != z;\nt = (m, 1) < (z, 0);\ntz = (m, 1) == (z, 1);\n\
               zs = String(z);\nms = String(m);\n";
    let cases = [
        ("lt", "false"),
        ("le", "true"),
        ("gt", "false"),
        ("ge", "true"),
        ("eq", "true"),
        ("ne", "false"),
        ("t", "false"),
        ("tz", "true"),
        // DESIGN.md sec:reduction: "the zeros print as `0.0` and `-0.0`".
        ("zs", "\"0.0\""),
        ("ms", "\"-0.0\""),
    ];
    for (name, want) in cases {
        assert_eq!(value(src, name), want, "{name}");
    }
}

// DESIGN.md sec:reduction: "NaN canonicalized to the quiet NaN with cleared sign and zero
// payload", and NaN prints `nan`; every IEEE comparison with NaN is false but `!=`.
#[test]
fn nan_is_unordered_and_its_negation_is_the_canonical_nan() {
    let src = "nan = 0.0f64 / 0.0f64;\nneg = -nan;\nsq = (0.0f64 - 1.0f64) * nan;\none = 1.0f64;\n\
               a = neg < one;\nb = neg > one;\nc = neg <= neg;\nd = neg == neg;\ne = neg != neg;\n\
               f = nan >= -1.0f64 / 0.0f64;\nshown = String(neg);\n";
    let cases = [
        ("neg", "nan"),
        ("a", "false"),
        ("b", "false"),
        ("c", "false"),
        ("d", "false"),
        ("e", "true"),
        ("f", "false"),
        ("shown", "\"nan\""),
    ];
    for (name, want) in cases {
        assert_eq!(value(src, name), want, "{name}");
    }
    // The quotient, its negation and its product with -1 are the one canonical value.
    let vs = values(src, &["nan", "neg", "sq"]);
    assert_eq!(vs[0], vs[1]);
    assert_eq!(vs[0], vs[2]);
    let Value::Float(f) = &vs[1] else {
        panic!("{:?}", vs[1])
    };
    assert!(f.get().is_nan() && f.get().is_sign_positive());
}

// The subnormals are ordinary floats under IEEE: the smallest lies strictly between the
// zeros and the largest subnormal, which lies below the smallest normal.
#[test]
fn subnormals_order_between_zero_and_the_normals() {
    let src = "z = 0.0f64;\nm = -0.0f64;\ntiny = 5.0e-324f64;\nnegTiny = -5.0e-324f64;\n\
               topSub = 2.225073858507201e-308f64;\nnormal = 2.2250738585072014e-308f64;\n\
               a = tiny > z;\nb = negTiny < m;\nc = tiny < topSub;\nd = topSub < normal;\n\
               e = negTiny < z;\nf = tiny / 2.0f64 == z;\n";
    for name in ["a", "b", "c", "d", "e", "f"] {
        assert_eq!(value(src, name), "true", "{name}");
    }
    assert_eq!(value(src, "tiny"), "5.0e-324");
    assert_eq!(value(src, "negTiny"), "-5.0e-324");
}

// DESIGN.md sec:reduction item 5: "`min` and `max` ... are the IEEE 754-2019 `minimum` and
// `maximum`: NaN where either operand is NaN, in either order, and `-0.0` below `0.0`, so
// `min(-0.0, 0.0)` is `-0.0`"; and "`min((2.0, 1), (f64(#NaN), 0))` and
// `max((2.0, 1), (f64(#NaN), 0))` are both `(f64(#NaN), 0)`, and `min((0.0, 1), (-0.0, 1))` is
// `(-0.0, 1)` in either order".
#[test]
fn min_and_max_put_the_negative_zero_below_and_nan_absorbs() {
    let src = "z = 0.0f64;\nm = -0.0f64;\nnan = 0.0f64 / 0.0f64;\n\
               a = min(m, z);\nb = min(z, m);\nc = max(m, z);\nd = max(z, m);\n\
               e = min(nan, 1.0f64);\nf = max(1.0f64, nan);\ng = min(5.0e-324f64, m);\n\
               h = min((2.0f64, 1), (nan, 0));\ni = max((2.0f64, 1), (nan, 0));\n\
               j = min((z, 1), (m, 1));\nk = min((m, 1), (z, 1));\n";
    let cases = [
        ("a", "-0.0"),
        ("b", "-0.0"),
        ("c", "0.0"),
        ("d", "0.0"),
        ("e", "nan"),
        ("f", "nan"),
        ("g", "-0.0"),
        ("h", "(nan, 0)"),
        ("i", "(nan, 0)"),
        ("j", "(-0.0, 1)"),
        ("k", "(-0.0, 1)"),
    ];
    for (name, want) in cases {
        assert_eq!(value(src, name), want, "{name}");
    }
}

// DESIGN.md L1.17: "`<`, `<=`, `>`, `>=` ... compare only two numbers of one kind ...,
// anything else being a type error". The `int` zero is the name `i`, since a literal without a
// suffix takes the carrier of the other side where it is exact (L1.26a).
#[test]
fn zeros_of_two_kinds_do_not_compare() {
    for src in [
        "i = 0;\nx = i < 0r;\n",
        "x = 0r <= 0.0f64;\n",
        "i = 0;\nx = i > -0.0f64;\n",
        "i = 0;\nx = (i, 1) < (0r, 1);\n",
    ] {
        assert!(!errors(src).is_empty(), "{src}");
    }
}

/// The edge numbers of the natural-order tests, their names, and their printed forms in
/// the natural order, with the two float zeros last so that a caller can check them apart.
const ORDER_SRC: &str = "i = 0;\nr = 0r;\nz = 0.0f64;\nm = -0.0f64;\ntiny = 5.0e-324f64;\n\
                         negTiny = -5.0e-324f64;\ntopSub = 2.225073858507201e-308f64;\n\
                         normal = 2.2250738585072014e-308f64;\nnan = 0.0f64 / 0.0f64;\nneg = -nan;\n\
                         inf = 1.0f64 / 0.0f64;\nninf = -1.0f64 / 0.0f64;\nnegOne = -1;\n";
const ORDER_NAMES: [&str; 13] = [
    "nan", "tiny", "z", "r", "neg", "ninf", "i", "normal", "m", "inf", "negTiny", "topSub",
    "negOne",
];

// DESIGN.md L1.17: "orders numbers by exact value across `int`, `rat` and the float formats
// (a float as the dyadic rational it is, the infinities at the ends, the NaN last), an equal
// value ordered `int`, then `rat`, then float".
#[test]
fn the_natural_order_places_zeros_subnormals_and_nan() {
    let mut vs = values(ORDER_SRC, &ORDER_NAMES);
    vs.sort();
    let shown: Vec<String> = vs.iter().map(|v| v.to_string()).collect();
    // The two float zeros are one value, so their order between themselves is the subject of
    // the next test; here they are only checked to be adjacent at the right place.
    let mut zeros = [shown[5].clone(), shown[6].clone()];
    zeros.sort();
    assert_eq!(zeros, ["-0.0", "0.0"], "{shown:?}");
    let rest: Vec<&str> = shown
        .iter()
        .enumerate()
        .filter(|&(k, _)| k != 5 && k != 6)
        .map(|(_, s)| s.as_str())
        .collect();
    assert_eq!(
        rest,
        [
            "-inf",
            "-1",
            "-5.0e-324",
            "0",
            "0r",
            "5.0e-324",
            "2.225073858507201e-308",
            "2.2250738585072014e-308",
            "inf",
            "nan",
            "nan"
        ]
    );
    // The NaN of `-nan` is the canonical NaN, equal to the other.
    assert_eq!(vs[11], vs[12]);
}

// DESIGN.md L1.18: "`sum` of a tuple ... is `0` for the empty tuple"; DESIGN.md L1.22:
// the empty tuple is "the result of a block that exports nothing".
#[test]
fn the_sum_of_the_empty_tuple_is_zero() {
    let src = "nothing() {\n}\ne = nothing();\ns = sum(e);\nt = sum(nothing()) + 1;\n\
               u = sum((-9223372036854775808, -1)) + 1;\n";
    assert_eq!(value(src, "e"), "()");
    assert_eq!(value(src, "s"), "0");
    assert_eq!(value(src, "t"), "1");
    assert_eq!(value(src, "u"), "-9223372036854775808");
    let vs = values(src, &["s", "u"]);
    assert_eq!(vs[0], Value::Int(0));
    assert!(matches!(vs[1], Value::Int(_)), "{:?}", vs[1]);
}
