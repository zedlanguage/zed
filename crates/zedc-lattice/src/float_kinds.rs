//! What a float may be (FLOAT-class-zir): the NaN, an infinity of either sign, a zero of
//! either sign, the one, or another finite value, with the kinds each primitive gives from its
//! operands' kinds. It is finer than [`super::float::FloatClass`], whose one finite kind cannot
//! say that a value is not 0 or not 1, which is what float `^` needs: IEEE 754 `pow` gives a
//! number for a NaN operand only as `pow(NaN, 0)` and `pow(1, NaN)`. The native back end
//! (zed-native `tables.rs`, `Tables::visit`, and `codegen.rs`, fn `pow`) finds the kinds of each
//! ZIR edge from the graph's structure, each constant's own kind and each operation's result
//! from its operands', so it needs no fact the stripped form drops (`zedc::zir::strip`).
//!
//! The rules are those of IEEE Std 754-2019 (doi:10.1109/IEEESTD.2019.8766229): section 7.2
//! lists the operations that give the NaN for operands that are not NaN ("invalid operation"):
//! (b) `0 × ∞`; (d) `∞ - ∞` by addition or subtraction; (e) `0 / 0` and `∞ / ∞`; (g)
//! `pow(x, y)` of a finite `x < 0` and a finite non-integer `y` (section 9.2.1); and section
//! 6.2 that an operation of a NaN operand gives the NaN, which Zed's `^` holds for every
//! operand (DESIGN.md sec:domains, NaN rule 5; zed-kernel `eval.rs`, fn `prim_on`, at
//! `Prim::Pow`). Section 7.4: a finite result rounds to an infinity only when its magnitude is
//! at least `MAX + ulp(MAX) / 2`, so a sum with a zero or with one of `±1` never overflows, and
//! neither does a product with a zero or with one of `±1`. So the kind one, there for `pow`,
//! also bounds overflow.
//! Floats combine only with floats of their format (`prim_on`'s float arms), so the kinds are
//! those of whichever float format the value has, and a value that is no float has none.
//!
//! How this was checked: the 6.2, 7.2 and 9.2.1 passages are those the kernel quotes from the
//! 2019 text, read 2026-11-20 (zed-kernel `eval.rs`, fn `prim_on`, at `Prim::Sqrt` and
//! `Prim::Pow`). The list letters of 7.2 and the 7.3 and 7.4 rules are written from memory,
//! not checked against the text (2026-11-22). Every rule is checked against the kernel, which
//! runs Rust's IEEE operations, by test
//! `l01_36_cranelift::pow_nan::float_kinds_hold_every_result_the_kernel_gives`: each primitive
//! on every pair of 16 sample operands (both zeros, `±1`, `±2`, `±0.5`, 3, `±MAX`, the
//! smallest normal and subnormal, both infinities, the NaN), and the rules' monotonicity over
//! every set of kinds. It catches a rule that leaves out a kind some sample pair gives; it
//! cannot catch one that only an operand pair outside the samples reaches.
//!
//! Complexity: O(1) per primitive. The back end makes one pass over each region's nodes,
//! within the O(n) of building its tables. Tradeoff: a node's operands defined after it (no
//! such graph is lowered today) and every output of a node that is no primitive (`apply`, `if`,
//! a fold) count as any float, so the analysis stays one forward pass; the checker's classes of
//! a function's parameters are not in the graph (lowering types every edge `_`), so a parameter
//! is any float until row ZIR-checker-facts writes those types on the edges, which this reads.

use zed_kernel::{Prim, Value};

/// A set of the kinds a float may be, one bit each.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Kinds(u8);

impl Kinds {
    /// The NaN.
    pub const NAN: Kinds = Kinds(1);
    /// Plus infinity.
    pub const PINF: Kinds = Kinds(2);
    /// Minus infinity.
    pub const NINF: Kinds = Kinds(4);
    /// Plus or minus zero.
    pub const ZERO: Kinds = Kinds(8);
    /// The one, `1.0`.
    pub const ONE: Kinds = Kinds(16);
    /// A finite value that is no zero and not `1.0`.
    pub const OTHER: Kinds = Kinds(32);
    /// No kind: a value that is no float.
    pub const NONE: Kinds = Kinds(0);
    /// Every kind: a float about which nothing is known.
    pub const ALL: Kinds = Kinds(63);
    /// Each kind alone.
    pub const EACH: [Kinds; 6] = [
        Kinds::NAN,
        Kinds::PINF,
        Kinds::NINF,
        Kinds::ZERO,
        Kinds::ONE,
        Kinds::OTHER,
    ];
    const INF: Kinds = Kinds(6);
    const FINITE: Kinds = Kinds(56);
    const NONZERO: Kinds = Kinds(54);
    const NUMBER: Kinds = Kinds(62);

    /// The kind of the value `v`: none for a value that is no float.
    pub fn of(v: &Value) -> Kinds {
        let x = match v {
            Value::Float(x) => x.get(),
            Value::Float32(x) => f64::from(x.get()),
            _ => return Kinds::NONE,
        };
        if x.is_nan() {
            Kinds::NAN
        } else if x == f64::INFINITY {
            Kinds::PINF
        } else if x == f64::NEG_INFINITY {
            Kinds::NINF
        } else if x == 0.0 {
            Kinds::ZERO
        } else if x == 1.0 {
            Kinds::ONE
        } else {
            Kinds::OTHER
        }
    }

    /// Whether some kind is in both.
    pub fn meets(self, k: Kinds) -> bool {
        self.0 & k.0 != 0
    }

    /// Both sets' kinds.
    pub fn or(self, k: Kinds) -> Kinds {
        Kinds(self.0 | k.0)
    }

    /// The kinds in both sets.
    pub fn and(self, k: Kinds) -> Kinds {
        Kinds(self.0 & k.0)
    }

    /// The kinds of `self` not in `k`.
    pub fn minus(self, k: Kinds) -> Kinds {
        Kinds(self.0 & !k.0)
    }

    /// The kinds the negation of a float of these kinds may be: `-1` is another value, and the
    /// negation of another value may be the one.
    fn neg(self) -> Kinds {
        let mut r = Kinds(self.0 & (Kinds::NAN.0 | Kinds::ZERO.0));
        r = r.when(self.meets(Kinds::PINF), Kinds::NINF);
        r = r.when(self.meets(Kinds::NINF), Kinds::PINF);
        r = r.when(self.meets(Kinds::ONE), Kinds::OTHER);
        r.when(self.meets(Kinds::OTHER), Kinds::OTHER.or(Kinds::ONE))
    }

    /// `self` with `k` added when `c`.
    fn when(self, c: bool, k: Kinds) -> Kinds {
        if c { self.or(k) } else { self }
    }

    /// The kinds a sum of floats of kinds `a` and `b` may be (section 7.2 (d), 7.4).
    fn sum(a: Kinds, b: Kinds) -> Kinds {
        if a == Kinds::NONE || b == Kinds::NONE {
            return Kinds::NONE;
        }
        let nan = a.meets(Kinds::NAN)
            || b.meets(Kinds::NAN)
            || (a.meets(Kinds::PINF) && b.meets(Kinds::NINF))
            || (a.meets(Kinds::NINF) && b.meets(Kinds::PINF));
        // Two other values may overflow; a zero or one of `±1` may not (7.4).
        let over = a.meets(Kinds::OTHER) && b.meets(Kinds::OTHER);
        let finite = a.meets(Kinds::FINITE) && b.meets(Kinds::FINITE);
        Kinds::NONE
            .when(nan, Kinds::NAN)
            .when(
                a.meets(Kinds::PINF) || b.meets(Kinds::PINF) || over,
                Kinds::PINF,
            )
            .when(
                a.meets(Kinds::NINF) || b.meets(Kinds::NINF) || over,
                Kinds::NINF,
            )
            .when(finite, Kinds::FINITE)
    }

    /// The kinds a product of floats of kinds `a` and `b` may be (section 7.2 (b), 7.4).
    fn product(a: Kinds, b: Kinds) -> Kinds {
        if a == Kinds::NONE || b == Kinds::NONE {
            return Kinds::NONE;
        }
        let nan = a.meets(Kinds::NAN)
            || b.meets(Kinds::NAN)
            || (a.meets(Kinds::INF) && b.meets(Kinds::ZERO))
            || (a.meets(Kinds::ZERO) && b.meets(Kinds::INF));
        let inf = (a.meets(Kinds::INF) && b.meets(Kinds::NONZERO))
            || (b.meets(Kinds::INF) && a.meets(Kinds::NONZERO))
            || (a.meets(Kinds::OTHER) && b.meets(Kinds::OTHER));
        let finite = a.meets(Kinds::FINITE) && b.meets(Kinds::FINITE);
        Kinds::NONE
            .when(nan, Kinds::NAN)
            .when(inf, Kinds::INF)
            .when(finite, Kinds::FINITE)
    }

    /// The kinds a quotient of floats of kinds `a` and `b` may be (section 7.2 (e), 7.3, 7.4).
    fn quotient(a: Kinds, b: Kinds) -> Kinds {
        if a == Kinds::NONE || b == Kinds::NONE {
            return Kinds::NONE;
        }
        let nan = a.meets(Kinds::NAN)
            || b.meets(Kinds::NAN)
            || (a.meets(Kinds::ZERO) && b.meets(Kinds::ZERO))
            || (a.meets(Kinds::INF) && b.meets(Kinds::INF));
        // A division by zero (7.3), an infinity divided, or a quotient that overflows.
        let inf = (a.meets(Kinds::NONZERO) && b.meets(Kinds::ZERO))
            || (a.meets(Kinds::INF) && b.meets(Kinds::FINITE))
            || (a.meets(Kinds::NONZERO) && b.meets(Kinds::OTHER));
        let finite = a.meets(Kinds::FINITE) && b.meets(Kinds::NUMBER);
        Kinds::NONE
            .when(nan, Kinds::NAN)
            .when(inf, Kinds::INF)
            .when(finite, Kinds::FINITE)
    }

    /// The kinds `p` may give for operands of kinds `ins`: every kind for an operation these
    /// rules do not cover.
    pub fn transfer(p: Prim, ins: &[Kinds]) -> Kinds {
        match (p, ins) {
            (Prim::Add, &[a, b]) => Kinds::sum(a, b),
            (Prim::Sub, &[a, b]) => Kinds::sum(a, b.neg()),
            (Prim::Mul, &[a, b]) => Kinds::product(a, b),
            (Prim::Div, &[a, b]) => Kinds::quotient(a, b),
            (Prim::Neg, &[a]) => a.neg(),
            (Prim::Abs, &[a]) => {
                let n = a.neg();
                a.or(n)
                    .minus(Kinds::NINF)
                    .when(a.meets(Kinds::INF), Kinds::PINF)
            }
            // The result is one of the two (`ieee_min_max`), the NaN when either is.
            (Prim::Min | Prim::Max, &[a, b]) if a != Kinds::NONE && b != Kinds::NONE => a.or(b),
            (Prim::Min | Prim::Max, &[_, _]) => Kinds::NONE,
            // NaN in, NaN out; otherwise the NaN only for a finite negative base and a finite
            // non-integer exponent, both other values (9.2.1). An exponent that is no float is
            // an integer (`f32 ^ int`, `prim_on`), which never gives the NaN of a number.
            (Prim::Pow, &[a, b]) => {
                if a == Kinds::NONE {
                    return Kinds::NONE;
                }
                let nan = a.meets(Kinds::NAN)
                    || b.meets(Kinds::NAN)
                    || (a.meets(Kinds::OTHER) && b.meets(Kinds::OTHER));
                Kinds::NUMBER.when(nan, Kinds::NAN)
            }
            // A number that is no float rounds to a finite value or an infinity; a float keeps
            // its NaN (`zed_kernel::words`, the casts).
            (Prim::CastF64 | Prim::CastF32, &[a]) => {
                Kinds::NUMBER.when(a.meets(Kinds::NAN), Kinds::NAN)
            }
            _ => Kinds::ALL,
        }
    }
}
