//! Kernel terms: Tier 0, a strict lambda calculus with data, and Tier 1, the seven
//! generators over families (DESIGN.md sec:kernel).
//!
//! Every surface form elaborates to a [`Term`]. Names are plain strings: the front end has
//! resolved scopes before a term is built, so a term never needs renaming.

use std::collections::BTreeMap;
use std::fmt;
use std::ops::Deref;
use std::sync::{Arc, OnceLock};

use crate::deep;

pub mod walk;
use crate::types::Type;
use crate::value::Value;
use crate::value::{Id, fresh_id};

/// A primitive operation. Applied to a failure atom, every primitive but `Tuple`, `Atom`,
/// `Eq` and `Ne` returns its leftmost atom argument without computing (sec:failure): a loose
/// atom selects no arrow. `Tuple` and `Atom` store atoms as data, and `==` and `!=` compare
/// them, having an arrow at every type (step L1.17).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Prim {
    /// `a + b` over two ints or two floats.
    Add,
    /// `a - b`.
    Sub,
    /// `a * b`.
    Mul,
    /// Float division `a / b`.
    Div,
    /// Euclidean `a div b` over ints; `#divByZero` when `b` is 0 (sec:failure).
    IntDiv,
    /// Euclidean `a mod b` over ints, never negative; `#divByZero` when `b` is 0.
    Mod,
    /// `-a`.
    Neg,
    /// `a == b`: structural, but two floats compare as IEEE 754 does ([`Value::surface_eq`]).
    Eq,
    /// `a != b`.
    Ne,
    /// `a < b` in the total order of values, two floats compared as IEEE 754 does (IEEE Std
    /// 754-2019, doi:10.1109/IEEESTD.2019.8766229, section 5.11; the full comment is in
    /// `value.rs`, `Value::surface_cmp`).
    Lt,
    /// `a <= b`.
    Le,
    /// `a > b`.
    Gt,
    /// `a >= b`.
    Ge,
    /// `a && b` over bools.
    And,
    /// `a || b` over bools.
    Or,
    /// `!a`.
    Not,
    /// The smaller of two values.
    Min,
    /// The larger of two values.
    Max,
    /// `f[k]`: the entry of family `f` at top-level key `k`, or `#notFound`.
    Get,
    /// The number of top-level entries of a family.
    Count,
    /// The union of two families. A keypath both write must carry equal values, else it is
    /// a collision; on set families this is set union, the join of a reachability `fix`.
    Union,
    /// Builds a keypath value from its key arguments.
    Path,
    /// `p[i]`: key `i` of keypath `p`, counting from 0, or `#notFound`.
    PathKey,
    /// The number of keys of a keypath.
    PathLen,
    /// Builds a tuple from its arguments.
    Tuple,
    /// `t[i]`: component `i` of a tuple, counting from 0.
    TupleGet,
    /// `a ++ b`, two strings joined. It is not `Add`, so no law of `+` (commutativity) is
    /// ever read as one of `++`.
    Concat,
    /// `a ^ b`: an int to a non-negative int power, or a float to a float power.
    Pow,
    /// Builds an atom: `atom("err", (), 1)` is `#err(1)` and `atom("err", ("code",), 3)` is
    /// `#err(code: 3)`. The first argument is the name, the second the field names of a
    /// struct payload, empty for a tuple payload, and the rest the payload's values.
    Atom,
    /// `String(x)`: a string as itself, any other value as it prints (step L1.18).
    Show,
    /// `int(x)`, the checked cast: the `int` equal to `x`, or `#invalid` of a string that is
    /// not one or a float that is not finite; the checker proves a number whole (step L1.18).
    CastInt,
    /// `rat(x)`, the checked cast.
    CastRat,
    /// `f64(x)`, the checked cast; from a string it reads what `String` prints.
    CastF64,
    /// `f32(x)`, the checked cast; from a string it reads what `String` prints.
    CastF32,
    /// `abs(x)` of a number.
    Abs,
    /// `len(s)`, the number of Unicode scalars of a string.
    Len,
    /// `lower(s)`, Unicode lowercase.
    Lower,
    /// `upper(s)`, Unicode uppercase.
    Upper,
    /// `trim(s)`, without leading and trailing Unicode white space.
    Trim,
    /// `sum(t)`, the `+` of a tuple's components, `0` for the empty tuple.
    Sum,
    /// `bitAnd(a, b)`: the binary digits of two non-negative ints, and-ed (step L1.39a).
    BitAnd,
    /// `bitOr(a, b)`, or-ed.
    BitOr,
    /// `bitXor(a, b)`, exclusive-or-ed.
    BitXor,
    /// `bitNot(x, width: w)`: `2^w - 1 - x`, for `x` in `0 ..< 2^w`.
    BitNot,
    /// `shl(x, k)`: `x * 2^k`, for any int `x` and `k >= 0`.
    Shl,
    /// `shr(x, k)`: `x div 2^k`, Euclidean, for any int `x` and `k >= 0`.
    Shr,
    /// `popCount(x)`: the number of one digits of `x >= 0`.
    PopCount,
    /// `leadingZeros(x, width: w)`: `w` minus the number of binary digits of `x`.
    LeadingZeros,
    /// `trailingZeros(x, width: w)`: the zero digits below the lowest one digit; `w` for 0.
    TrailingZeros,
    /// `rotl(x, k, width: w)`: the `w` low digits of `x` rotated `k` places toward the high.
    Rotl,
    /// `rotr(x, k, width: w)`: rotated toward the low digits.
    Rotr,
    /// `f64Bits(x)`: the IEEE 754 binary64 encoding of a float, an int in `0 ..< 2^64` (IEEE
    /// Std 754-2019, doi:10.1109/IEEESTD.2019.8766229, section 3.4; the full comment is in
    /// `value.rs`, at the canonical NaN's bits).
    F64Bits,
    /// `codePoint(s)`: the Unicode scalar value of a string of one scalar, an int in
    /// `0 ..= 1114111`; `#notScalar` for any other string (step L1.39c).
    CodePoint,
    /// `scalar(n)`: the string of the one scalar `n`; `#notScalar` for a surrogate or an `n`
    /// outside `0 ..= 1114111`.
    Scalar,
    /// `utf8(s)`: the family of the UTF-8 bytes of `s`, keyed by byte offset from 0.
    Utf8,
    /// `fromUtf8(b)`: the string the bytes of `b`, in key order, encode; `#badUtf8` when they
    /// are not well-formed UTF-8.
    FromUtf8,
    /// `mulHi(a, b, width: w)`: `shr(a * b, w)`, for `a` and `b` in `0 ..< 2^w`, the high half of
    /// the product (step L1.39f, DESIGN.md sec:linalg, machine operations).
    MulHi,
    /// `bitReverse(x, width: w)`: the `w` low digits of `x` in reverse order.
    BitReverse,
    /// `byteSwap(x, width: w)`, `w` a multiple of 8: the `w / 8` low bytes of `x` in reverse order.
    ByteSwap,
    /// `pdep(x, mask)`: the low digits of `x` deposited at the one digits of `mask`, lowest first.
    Pdep,
    /// `pext(x, mask)`: the digits of `x` at the one digits of `mask`, gathered into the low
    /// digits.
    Pext,
    /// `funnelShl(hi, lo, k, width: w)`: the high `w` digits of the `2w` digits `hi * 2^w + lo`
    /// shifted `k` places toward the high, for `k` in `0 ..< w`.
    FunnelShl,
    /// `funnelShr(hi, lo, k, width: w)`: the low `w` digits of `hi * 2^w + lo` shifted `k` places
    /// toward the low.
    FunnelShr,
    /// `v[k]` at a read the checker proved is of a family whose keys are one integer interval,
    /// every key present: the entry at `k`, or `#outOfBounds` (DESIGN.md sec:type_language, the
    /// `m[k]` row); on a tuple, `TupleGet`.
    At,
    /// `sqrt(x)` of an `f64` or an `f32`: the square root correctly rounded to the operand's
    /// format, as IEEE 754 `squareRoot` gives it: `sqrt(-0.0)` is `-0.0`, and a negative or NaN
    /// operand gives NaN (DESIGN.md sec:linalg, machine operations). Citation for this and
    /// `Fma`: IEEE Std 754-2019, doi:10.1109/IEEESTD.2019.8766229, section 5.4.1; the full
    /// comment is in `eval.rs`, fn `prim_on`, at `Prim::Sqrt`.
    Sqrt,
    /// `fma(a, b, c)` of three `f64` or three `f32`: the exact `a * b + c` rounded once to the
    /// operands' format, IEEE 754 `fusedMultiplyAdd` (DESIGN.md step L1.18a).
    Fma,
    /// `floatMod(x, m)` of two `f64` or two `f32`, `m` finite and greater than `0.0`: the float
    /// of `[0.0, m)` nearest the exact residue `x − m·⌊x/m⌋`, ties to even; NaN for an
    /// infinite or NaN `x` (DESIGN.md sec:domains; QUESTIONS A174). The proof is at
    /// `num::float_mod::float_mod`.
    FloatMod,
    /// `{k0 -> v0, k1 -> v1, …}`: the family of the entries its arguments give in pairs, key
    /// then value, the map and array displays of step L3.2. A value that is a family is a level
    /// beneath its key; two entries with one key are a collision.
    Entries,
    /// `k in f`: whether the family `f` holds the top-level key `k` (step L3.2).
    Has,
    /// `range(a, b)`: the set of the integers `a`, `a + 1`, …, `b - 1`, each key mapping to
    /// itself, empty when `b <= a`; `a ..< b` is `range(a, b)` and `a ..= b` is
    /// `range(a, b + 1)` (DESIGN.md sec:grammar, rule Range, and step L3.2).
    Range,
    /// `firstEntry(f)`: the entry of the least top-level key of the family `f`, as the tuple
    /// `(k, v)`, or the empty tuple `()` when `f` has no entries. The four entry steps walk a
    /// level in key order for the folds, quantifiers and scans of plan row FP-ops-run; the end
    /// is `()`, not an atom, since a key may itself be an atom held as data.
    FirstEntry,
    /// `lastEntry(f)`: the entry of the greatest top-level key, `(k, v)`, or `()`.
    LastEntry,
    /// `entryAfter(f, e)`: the entry of the least top-level key of `f` above `e[0]`, the key of
    /// the entry tuple `e`, as `(k, v)`, or `()` when there is none. `e[0]` need not be held.
    EntryAfter,
    /// `entryBefore(f, e)`: the entry of the greatest top-level key below `e[0]`, or `()`.
    EntryBefore,
    /// `f.first`: the leaf at the least keypath of `f`, descending through each level in key
    /// order while the entry is a family, or `#none` when a level on the way is empty
    /// (DESIGN.md sec:corner_cases, "`first`/`last` are lexicographic").
    First,
    /// `f.last`: the leaf at the greatest keypath of `f`, or `#none`.
    Last,
    /// `split(s, sep)`: the pieces of the string `s` between the occurrences of `sep`, each
    /// kept, empty ones included, as a family keyed from 0 in order (DESIGN.md step L3.2). An
    /// empty `sep` gives each character of `s` as a piece, and `[""]` for an empty `s`.
    Split,
    /// `lines(s)`: the lines of the string `s`, each ended by `\n`, `\r\n` or a lone `\r`, with
    /// no empty line after a line end at the end of `s`, as a family keyed from 0 in order
    /// (DESIGN.md step L3.2, sec:codecs).
    Lines,
    /// `concat(pieces, sep: s)`: the strings of the family `pieces`, in key order, with `s`
    /// between each two; `""` for no pieces (DESIGN.md step L3.2).
    Join,
    /// `rangeFrom(a)`: the set of the integers `a`, `a + 1`, …, with no upper end, each key
    /// mapping to itself; `a ..` is `rangeFrom(a)` (DESIGN.md sec:grammar, rule Range). It is
    /// read by a key, by `in` and by `first`, and never walked (plan row RANGE-open).
    RangeFrom,
    /// `a ++ b` on two lists (DESIGN.md step L5.2): `a`'s entries, then `b`'s with each key `k`
    /// moved to `a.count + k`. Both lists are shared in the result, not copied
    /// (`Family::concat`, plan row PERF-list-concat-shared). `++` on strings is `Concat`.
    ListConcat,
    /// `place(table, f)` or `place(table, f, fill)`: the closure `f` with its parameter list
    /// (DESIGN.md sec:values_morphisms, "The function called places the arguments"). `table`
    /// is a literal: the tuple `(p, names, places, defaulted)` of the number of parameters,
    /// their names sorted, the place of each sorted name, and for each parameter in order
    /// whether it has a default. `fill` is given when one has: a lambda of the parameters and
    /// then one flag for each defaulted parameter, true where the call leaves it out, which
    /// computes each such default in order in the declaration's scope and calls `f`. A
    /// positional call of the result is a call of `f`; [`Prim::CallNamed`] reads the list.
    /// Elaboration makes one only in a unit with a call through a value whose functions
    /// place its arguments differently (plan row CALL-callee-places), and as the result of a
    /// curried call through a value that its function places (plan row CALL-curried-placed).
    Place,
    /// `callNamed(shape, f, args…)`: the call of the function value `f` with its arguments as
    /// written, the positional ones first, then the named ones in the order written. `shape`
    /// is a literal: the tuple `(k, names, at)` of the number of positional arguments, the
    /// names of the named ones sorted, and for each sorted name the index of its argument
    /// among the named ones. `f`'s list from [`Prim::Place`] places them, and its `fill`
    /// fills the parameters left out. `shape` may be `(k, names, at, opt)`, the call then
    /// `callNamed(shape, f, args…, flags…)`: for each sorted name, `opt` holds the index of
    /// its flag among `flags`, or -1, and a name whose flag is true is left out, as if the
    /// call did not write it. The fill of a curried call's result passes these, so that `f`
    /// fills each parameter the result's own call leaves out (plan row CALL-curried-placed).
    CallNamed,
    /// `round(x)`: the whole number nearest `x`, a tie to the even one, as an `int`, for an
    /// `int`, `rat`, `f64` or `f32` `x`; a NaN gives `#NaN` and an infinity `#overflow`
    /// (DESIGN.md sec:facets, "Rounding to a whole number"; plan row CAST-round-whole). The
    /// five below are the same but for the rule ([`crate::num::Rounding`]).
    Round,
    /// `round(x, ties: #away)`: the whole number nearest `x`, a tie away from zero.
    RoundTiesAway,
    /// `floor(x)`: rounded toward −∞.
    Floor,
    /// `ceil(x)`: rounded toward +∞.
    Ceil,
    /// `trunc(x)`: rounded toward zero.
    Trunc,
    /// `awayFromZero(x)`: rounded away from zero.
    AwayFromZero,
}

impl Prim {
    /// The number of arguments the primitive takes, or `None` when it takes any number.
    pub fn arity(self) -> Option<usize> {
        use Prim::*;
        match self {
            Neg | Not | Count | PathLen | Show | CastInt | CastRat | CastF64 | CastF32 | Abs
            | Len | Lower | Upper | Trim | Sum | PopCount | F64Bits | CodePoint | Scalar | Utf8
            | FromUtf8 | Sqrt | FirstEntry | LastEntry | First | Last | Lines | RangeFrom
            | Round | RoundTiesAway | Floor | Ceil | Trunc | AwayFromZero => Some(1),
            Rotl | Rotr | MulHi | Fma => Some(3),
            FunnelShl | FunnelShr => Some(4),
            Path | Tuple | Atom | Entries | Place | CallNamed => None,
            _ => Some(2),
        }
    }

    /// The fixed number of the primitive, by which the canonical serialization writes it.
    /// Each number is assigned here and never changes, so that renaming a variant, reordering
    /// the enum, or adding a primitive leaves every other primitive's number, and with it every
    /// canonical address, as it was; a new primitive takes the next unused number. The numbers
    /// are the positions of the ZIR binary form's list, `zedc::zir::text::PRIMS`.
    pub fn code(self) -> u64 {
        use Prim::*;
        match self {
            Add => 0,
            Sub => 1,
            Mul => 2,
            Div => 3,
            IntDiv => 4,
            Mod => 5,
            Neg => 6,
            Eq => 7,
            Ne => 8,
            Lt => 9,
            Le => 10,
            Gt => 11,
            Ge => 12,
            And => 13,
            Or => 14,
            Not => 15,
            Min => 16,
            Max => 17,
            Get => 18,
            Count => 19,
            Union => 20,
            Path => 21,
            PathKey => 22,
            PathLen => 23,
            Tuple => 24,
            TupleGet => 25,
            Concat => 26,
            Pow => 27,
            Atom => 28,
            Show => 29,
            CastInt => 30,
            CastRat => 31,
            CastF64 => 32,
            Abs => 33,
            Len => 34,
            Lower => 35,
            Upper => 36,
            Trim => 37,
            Sum => 38,
            BitAnd => 39,
            BitOr => 40,
            BitXor => 41,
            BitNot => 42,
            Shl => 43,
            Shr => 44,
            PopCount => 45,
            LeadingZeros => 46,
            TrailingZeros => 47,
            Rotl => 48,
            Rotr => 49,
            F64Bits => 50,
            CodePoint => 51,
            Scalar => 52,
            Utf8 => 53,
            FromUtf8 => 54,
            MulHi => 55,
            BitReverse => 56,
            ByteSwap => 57,
            Pdep => 58,
            Pext => 59,
            FunnelShl => 60,
            FunnelShr => 61,
            At => 62,
            CastF32 => 63,
            Sqrt => 64,
            Fma => 65,
            Entries => 66,
            Has => 67,
            Range => 68,
            FirstEntry => 69,
            LastEntry => 70,
            EntryAfter => 71,
            EntryBefore => 72,
            First => 73,
            Last => 74,
            Split => 75,
            Lines => 76,
            Join => 77,
            RangeFrom => 78,
            ListConcat => 79,
            Place => 80,
            CallNamed => 81,
            Round => 82,
            RoundTiesAway => 83,
            Floor => 84,
            Ceil => 85,
            Trunc => 86,
            AwayFromZero => 87,
            FloatMod => 88,
        }
    }

    /// The arrows of a primitive over scalar carriers, the one table both the evaluator and
    /// the checker read (KERNEL-prim-arrow-table): for each tuple of operand carriers the
    /// primitive takes, the carrier of its result and the atoms a checked program may see it
    /// give. `None` for a primitive whose operands are not all scalars (a family, a tuple, a
    /// key path, a function, any value at all) or whose arrows the checker builds by another
    /// rule (the bit words, step L1.39a). The checker's `op_sig` and `word_sig` are built from
    /// this table, in its order, which is the order a class tries the carriers; the test
    /// `prim_arrow_table` checks that [`mod@crate::eval`] takes each tuple of scalars exactly
    /// when an arrow here does, and gives that arrow's carrier or an atom.
    ///
    /// The atoms are those the checker types, not every atom the evaluator may give: `int(x)`
    /// of a float gives `#invalid` when `x` is not whole, but the checker accepts the cast
    /// only where it proves `x` whole (step L1.18), so the arrow lists no atom.
    pub fn arrows(self) -> Option<&'static [ScalarArrow]> {
        use Prim::*;
        use ScalarType::{Bool as B, F32, F64, Int as I, Rat as R, Str as S};
        const fn a(
            params: &'static [ScalarType],
            result: ScalarType,
            atoms: &'static [&'static str],
        ) -> ScalarArrow {
            ScalarArrow {
                params,
                result,
                atoms,
                refused: None,
            }
        }
        // A tuple the checker refuses by design, for the reason `why`.
        const fn r(
            params: &'static [ScalarType],
            result: ScalarType,
            why: &'static str,
        ) -> ScalarArrow {
            ScalarArrow {
                params,
                result,
                atoms: &[],
                refused: Some(why),
            }
        }
        // A list of arrows as a constant, so the slice it returns is `'static`.
        macro_rules! list {
            ($($arrow:expr),* $(,)?) => {{
                const LIST: &[ScalarArrow] = &[$($arrow),*];
                LIST
            }};
        }
        const DIV0: &[&str] = &["divByZero"];
        const NAN: &[&str] = &["NaN", "overflow"];
        const INVALID: &[&str] = &["invalid"];
        const NOT_SCALAR: &[&str] = &["notScalar"];
        const ARITH: &[ScalarArrow] = &[
            a(&[I, I], I, &[]),
            a(&[F64, F64], F64, &[]),
            a(&[R, R], R, &[]),
            a(&[F32, F32], F32, &[]),
        ];
        const ORDER: &[ScalarArrow] = &[
            a(&[I, I], B, &[]),
            a(&[F64, F64], B, &[]),
            a(&[R, R], B, &[]),
            a(&[F32, F32], B, &[]),
            a(&[S, S], B, &[]),
            a(&[B, B], B, &[]),
        ];
        // `==` and `!=` of two carriers: the evaluator compares any two values, and the checker
        // refuses two whose types share no value, numbers of two carriers included (`n == y`
        // with `n: int` and `y: f64`); the repair is a cast (DESIGN.md sec:diagnostics, the
        // rows "Two numeric values with no common carrier" and "Two values compared by `==` or
        // `!=` whose types share no value"; `Ck::equal` in zedc-check).
        const APART: &str = "two carriers share no value; the repair is a cast";
        const EQUAL: &[ScalarArrow] = &[
            a(&[I, I], B, &[]),
            a(&[F64, F64], B, &[]),
            a(&[R, R], B, &[]),
            a(&[F32, F32], B, &[]),
            a(&[S, S], B, &[]),
            a(&[B, B], B, &[]),
            r(&[I, R], B, APART),
            r(&[I, F32], B, APART),
            r(&[I, F64], B, APART),
            r(&[I, S], B, APART),
            r(&[I, B], B, APART),
            r(&[R, I], B, APART),
            r(&[R, F32], B, APART),
            r(&[R, F64], B, APART),
            r(&[R, S], B, APART),
            r(&[R, B], B, APART),
            r(&[F32, I], B, APART),
            r(&[F32, R], B, APART),
            r(&[F32, F64], B, APART),
            r(&[F32, S], B, APART),
            r(&[F32, B], B, APART),
            r(&[F64, I], B, APART),
            r(&[F64, R], B, APART),
            r(&[F64, F32], B, APART),
            r(&[F64, S], B, APART),
            r(&[F64, B], B, APART),
            r(&[S, I], B, APART),
            r(&[S, R], B, APART),
            r(&[S, F32], B, APART),
            r(&[S, F64], B, APART),
            r(&[S, B], B, APART),
            r(&[B, I], B, APART),
            r(&[B, R], B, APART),
            r(&[B, F32], B, APART),
            r(&[B, F64], B, APART),
            r(&[B, S], B, APART),
        ];
        // `min` and `max` of two strings or two bools: the evaluator orders any two values of
        // one kind (DESIGN.md sec:order), and the checker's `min` and `max` take numbers only.
        // DESIGN.md says neither that they take strings and bools nor that they refuse them;
        // until it does, the checker keeps refusing them.
        const NUMBERS_ONLY: &str = "the checker's `min` and `max` take numbers only";
        const MIN_MAX: &[ScalarArrow] = &[
            a(&[I, I], I, &[]),
            a(&[F64, F64], F64, &[]),
            a(&[R, R], R, &[]),
            a(&[F32, F32], F32, &[]),
            r(&[S, S], S, NUMBERS_ONLY),
            r(&[B, B], B, NUMBERS_ONLY),
        ];
        const NUMBER: &[ScalarArrow] = &[
            a(&[I], I, &[]),
            a(&[F64], F64, &[]),
            a(&[R], R, &[]),
            a(&[F32], F32, &[]),
        ];
        // The rounding words give an `int` (DESIGN.md sec:facets, "Rounding to a whole
        // number"); no whole number stands for the NaN or an infinity, which give `#NaN` and
        // `#overflow` (author, P361).
        const ROUND: &[ScalarArrow] = &[
            a(&[I], I, &[]),
            a(&[R], I, &[]),
            a(&[F64], I, NAN),
            a(&[F32], I, NAN),
        ];
        Some(match self {
            Add | Sub | Mul => ARITH,
            Div => list![
                a(&[F64, F64], F64, &[]),
                a(&[F32, F32], F32, &[]),
                a(&[R, R], R, DIV0),
            ],
            // The kernel's `mod` is total on the ints, `#divByZero` at 0 (zed-kernel eval.rs,
            // `int_binary`); a Zed program reaches it only with `m` in `int[1..]`, which the
            // checker proves, and so drops the atom (DESIGN.md sec:domains; QUESTIONS A174).
            IntDiv | Mod => list![a(&[I, I], I, DIV0)],
            // A `rat` takes an integer exponent of either sign, exactly; `0r` to a negative
            // power is `#divByZero`. `f32 ^ int` is the one arrow between two carriers
            // (DESIGN.md L1.18).
            Pow => list![
                a(&[I, I], I, &[]),
                a(&[F64, F64], F64, &[]),
                a(&[F32, F32], F32, &[]),
                a(&[R, I], R, DIV0),
                a(&[F32, I], F32, &[]),
            ],
            Concat => list![a(&[S, S], S, &[])],
            Eq | Ne => EQUAL,
            Lt | Le | Gt | Ge => ORDER,
            And | Or => list![a(&[B, B], B, &[])],
            Not => list![a(&[B], B, &[])],
            Neg | Abs => NUMBER,
            Min | Max => MIN_MAX,
            CastInt => list![
                a(&[I], I, &[]),
                a(&[F64], I, &[]),
                a(&[F32], I, &[]),
                a(&[R], I, &[]),
                a(&[S], I, INVALID),
            ],
            // No `rat` stands for the NaN or an infinity (DESIGN.md sec:corner_cases, "Casts
            // are domain proofs"; author P361).
            CastRat => list![
                a(&[I], R, &[]),
                a(&[F64], R, NAN),
                a(&[F32], R, NAN),
                a(&[R], R, &[]),
                a(&[S], R, INVALID),
            ],
            // A cast to a float format is the float nearest the value, and the infinity of its
            // sign beyond the largest finite one (step L1.18), so it gives no atom.
            CastF64 => list![
                a(&[I], F64, &[]),
                a(&[F64], F64, &[]),
                a(&[R], F64, &[]),
                a(&[S], F64, INVALID),
                a(&[F32], F64, &[]),
            ],
            CastF32 => list![
                a(&[I], F32, &[]),
                a(&[F64], F32, &[]),
                a(&[R], F32, &[]),
                a(&[S], F32, INVALID),
                a(&[F32], F32, &[]),
            ],
            Round | RoundTiesAway | Floor | Ceil | Trunc | AwayFromZero => ROUND,
            // The float formats alone: an `int` or `rat` operand is cast first, `sqrt(f64(n))`,
            // so no call rounds where the text does not say so (row FLOAT-sqrt).
            Sqrt => list![a(&[F64], F64, &[]), a(&[F32], F32, &[])],
            Fma => list![a(&[F64, F64, F64], F64, &[]), a(&[F32, F32, F32], F32, &[])],
            // The float formats alone, as for `sqrt`; no atom, since the checker proves the
            // modulus finite and greater than `0.0` (DESIGN.md sec:domains, "`floatMod`").
            FloatMod => list![a(&[F64, F64], F64, &[]), a(&[F32, F32], F32, &[])],
            Len => list![a(&[S], I, &[])],
            CodePoint => list![a(&[S], I, NOT_SCALAR)],
            Scalar => list![a(&[I], S, NOT_SCALAR)],
            Lower | Upper | Trim => list![a(&[S], S, &[])],
            Get | Count | Union | Path | PathKey | PathLen | Tuple | TupleGet | Atom | Show
            | Sum | BitAnd | BitOr | BitXor | BitNot | Shl | Shr | PopCount | LeadingZeros
            | TrailingZeros | Rotl | Rotr | F64Bits | Utf8 | FromUtf8 | MulHi | BitReverse
            | ByteSwap | Pdep | Pext | FunnelShl | FunnelShr | At | Entries | Has | Range
            | FirstEntry | LastEntry | EntryAfter | EntryBefore | First | Last | Split | Lines
            | Join | RangeFrom | ListConcat | Place | CallNamed => return None,
        })
    }
}

/// A scalar carrier, as [`Prim::arrows`] names the operands and results of a primitive.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ScalarType {
    /// `bool`.
    Bool,
    /// `int`.
    Int,
    /// `rat`.
    Rat,
    /// `f32`.
    F32,
    /// `f64`.
    F64,
    /// `String`.
    Str,
}

/// One arrow of [`Prim::arrows`]: the operand carriers, the result's carrier, and the atoms a
/// checked program may see the primitive give beside it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ScalarArrow {
    /// The operands' carriers, in order.
    pub params: &'static [ScalarType],
    /// The result's carrier.
    pub result: ScalarType,
    /// The atoms, by name, the result may be instead.
    pub atoms: &'static [&'static str],
    /// `Some(why)` for a tuple the evaluator takes and the checker refuses by design, so no
    /// checked program reaches it; the checker builds no arrow from it.
    pub refused: Option<&'static str>,
}

/// A pattern of a `match` arm.
pub enum Pattern {
    /// `_`, matching anything.
    Wild,
    /// A name, matching anything and binding it.
    Bind(Arc<str>),
    /// A literal, matching an equal value.
    Lit(Value),
    /// `#name(p, …)`, matching an atom of that name whose tuple payload matches.
    Atom(Arc<str>, Vec<Pattern>),
    /// `#name(f: p, …)`, matching an atom of that name with a struct payload that has each
    /// field named, its value matching; the payload may have other fields.
    Fields(Arc<str>, Vec<(Arc<str>, Pattern)>),
    /// `(p, …)`, matching a tuple of that length.
    Tuple(Vec<Pattern>),
    /// `#_`, any atom, its payload included: the arm `else` and `?.` write for the atom
    /// members of a value until its type enumerates them (DESIGN.md, step L1.16).
    AnyAtom,
    /// `x is T` as a pattern: a value of the type `T`, which is decidable (step L1.22).
    Is(Type),
}

/// Where a `gen` loop tests its guard (sec:generations).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum GuardPos {
    /// `while c { … }`: the guard reads the last committed frame before each step, so a
    /// guard that ends the loop commits nothing.
    Before,
    /// `{ … } while c`: the guard reads the frame just committed, so a guard that ends the
    /// loop does so after its frame is committed.
    After,
}

/// The evidence a `reindex` carries that its key map is injective (T-Reindex). The reference
/// evaluator checks the collision rule on every run whatever the witness, so the witness only
/// records which discharge the checker used.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Witness {
    /// Proved by the Presburger or residue reasoning of (sec:grouping).
    Residue,
    /// Taken from a named entry of the injectivity catalog.
    Catalog(Arc<str>),
}

/// How strongly a tracked property is established (DESIGN.md sec:property_tracking), in the
/// order of that section: `Axiom > CheckedExhaustive | Proved > Bounded > Obligated > Assumed`,
/// the two in the middle incomparable. A property derived by the derivation rules has the meet
/// of its premises' grades, and that meet is what a record holds; the rule and the premises are
/// the property tracker's to keep.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Grade {
    /// A built-in's law, such as `+` on exact numerics being associative.
    Axiom,
    /// Checked over the whole of a small finite domain at compile time.
    CheckedExhaustive,
    /// A certificate the independent checker accepted.
    Proved,
    /// Checked up to a bound (rung 6 of the discharge ladder).
    Bounded,
    /// Emitted as a generated property test bound to the definition.
    Obligated,
    /// Waived by `@assume`.
    Assumed,
}

impl Grade {
    /// Whether the grade is proof grade, the grades that may change a type.
    pub fn is_proof_grade(self) -> bool {
        matches!(
            self,
            Grade::Axiom | Grade::CheckedExhaustive | Grade::Proved
        )
    }
}

/// The evidence record `ev` of a `fold` or a `fix`: each tracked property established, with
/// its grade. A property absent is unknown. `fold` reads the Boom row (`associative`,
/// `commutative`, `idempotent`), `fix` reads `monotone`, `inflationary` and the ACC fact.
pub type Evidence = BTreeMap<Arc<str>, Grade>;

/// The evidence of a `fix` (T-Fix): which instance of the least-fixed-point rule it is.
#[derive(Clone, PartialEq, Debug)]
pub enum FixKind {
    /// A lattice ascent: `x := join(x, step(x))` from the bottom `init` until nothing
    /// changes. The join is a binary function term, such as `Prim::Union` on sets.
    Lattice {
        /// The join of the lattice.
        join: Shared,
    },
    /// General recursion, the definedness instance: a partial family over the domain `init`,
    /// which starts undefined everywhere. Each round evaluates the body at every undefined
    /// key, and an entry whose body reads only defined entries becomes defined.
    Definedness,
}

/// A subterm, shared: a copy is a reference count. It carries the id it was given when it was
/// built: copies share it, no other subterm has it, and a subterm changed in place
/// ([`Shared::make_mut`]) takes a new one. So a walk that meets a shared subterm again knows it
/// by its id (memo keys are ids or structure, never addresses), the way [`crate::Items`] and
/// [`crate::Family`] are known by theirs. The id does not change what the term means: equality,
/// `Debug` and every evaluation read the term alone.
#[derive(Clone)]
pub struct Shared(Arc<Held>);

#[derive(Clone)]
struct Held {
    id: Id,
    term: Term,
    /// The names the term reads, as the evaluator finds them for a lambda body
    /// (`eval/made.rs`'s `reads`), found once for the life of the subterm rather than
    /// once per run: a function a test calls is made once per row, each row a run of its own.
    /// It is a function of `term` alone, so a copy may keep it, and [`Shared::make_mut`],
    /// which changes `term`, clears it.
    reads: ReadsMemo,
}

/// The memo in [`Held`]'s `reads`, a type of its own so that clippy's notes name it: clippy's
/// `mutable_key_type` refuses every map or set keyed by a type that holds a [`Shared`], and
/// clippy.toml lists each such key type whose order is shown not to read the memo, now only
/// zedc-preimage's `Address`. It takes no part in any equality, order or hash. `Shared`'s
/// equality reads the id and the term; no `Hash` or `Ord` is implemented for `Shared` or
/// `Term`; the memo is private to this crate and read only through [`Shared::reads_memo`],
/// whose only callers are in `eval/made.rs` (tests
/// `eval::tests::the_names_a_body_reads_take_no_part_in_equality` and zedc-preimage's
/// `address::tests::a_run_of_the_canonical_term_does_not_change_the_address`).
// Complexity tradeoff: naive version, the memo kept outside the node, in a table keyed by the
// node's id, so that the node holds no cell: one hash lookup per made function where the memo
// in the node costs one pointer read, and a table that outlives the nodes it names, with no
// point at which an entry can be freed. Used: the memo in the node, O(1) to read, freed with
// the node, and named in clippy.toml with the proof above. Nothing is given up.
#[derive(Clone, Default)]
struct ReadsMemo(OnceLock<Arc<[Arc<str>]>>);

impl Shared {
    /// `t`, shared, with a new id.
    pub fn new(t: Term) -> Shared {
        Shared(Arc::new(Held {
            id: fresh_id(),
            term: t,
            reads: ReadsMemo::default(),
        }))
    }

    /// The memo of the names the term reads (see [`Held`]'s `reads`).
    pub(crate) fn reads_memo(&self) -> &OnceLock<Arc<[Arc<str>]>> {
        &self.0.reads.0
    }

    /// The id of the subterm: copies share it, and no other subterm has it. Ids are only
    /// compared; no result may depend on their values.
    pub fn id(&self) -> u64 {
        self.0.id
    }

    /// The term, to change in place: copied first when another holder shares it. Either way it
    /// takes a new id, since what the old id named is no longer this term.
    pub fn make_mut(this: &mut Shared) -> &mut Term {
        let held = Arc::make_mut(&mut this.0);
        held.id = fresh_id();
        held.reads = ReadsMemo::default();
        &mut held.term
    }

    /// The term, moved out when `this` is its only holder, else copied.
    pub fn unwrap_or_clone(this: Shared) -> Term {
        Arc::unwrap_or_clone(this.0).term
    }

    /// The number of holders of the subterm.
    pub fn strong_count(this: &Shared) -> usize {
        Arc::strong_count(&this.0)
    }

    /// The term, when `this` is its only holder (only to free it).
    fn get_mut(this: &mut Shared) -> Option<&mut Term> {
        Arc::get_mut(&mut this.0).map(|h| &mut h.term)
    }
}

impl Deref for Shared {
    type Target = Term;

    fn deref(&self) -> &Term {
        &self.0.term
    }
}

impl AsRef<Term> for Shared {
    fn as_ref(&self) -> &Term {
        &self.0.term
    }
}

impl From<Term> for Shared {
    fn from(t: Term) -> Shared {
        Shared::new(t)
    }
}

impl PartialEq for Shared {
    fn eq(&self, other: &Shared) -> bool {
        self.0.id == other.0.id || self.0.term == other.0.term
    }
}

impl fmt::Debug for Shared {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0.term, f)
    }
}

impl fmt::Display for Shared {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0.term, f)
    }
}

/// A kernel term.
pub enum Term {
    /// A literal value.
    Lit(Value),
    /// A variable.
    Var(Arc<str>),
    /// `(x, …) -> body`.
    Lam(Vec<Arc<str>>, Shared),
    /// `f(a, …)`, call by value, arguments evaluated left to right.
    App(Shared, Vec<Term>),
    /// A primitive applied to its arguments.
    Prim(Prim, Vec<Term>),
    /// A primitive as a function value, such as `(+)` passed to `fold`.
    PrimFn(Prim),
    /// `x = e; body`.
    Let(Arc<str>, Shared, Shared),
    /// `if c { a } else { b }`. A failure atom as the condition is the result.
    If(Shared, Shared, Shared),
    /// `match e { p -> t, … }`, first matching arm wins.
    Match(Shared, Vec<(Pattern, Term)>),
    /// `fam(D, i -> e)`: the family over the top-level keys of `D` whose entry at `i` is `e`.
    Fam {
        /// The domain, a family whose top-level keys are used.
        domain: Shared,
        /// The key variable.
        var: Arc<str>,
        /// The entry at each key.
        body: Shared,
    },
    /// `reindex(F, kf, vf)`: each leaf `(p, v)` of `F` moves to keypath `kf(p, v)` with value
    /// `vf(p, v)`. Two leaves landing on one keypath is a collision.
    Reindex {
        /// The family to rekey.
        family: Shared,
        /// `(path, value) -> path`.
        kf: Shared,
        /// `(path, value) -> value`.
        vf: Shared,
        /// The injectivity evidence.
        witness: Witness,
    },
    /// `discard(F, sel)`: walks `F` top down calling `sel(path, entry)` at each entry. `true`
    /// keeps the entry and descends into it, `false` drops it with its subtree, and
    /// `#boundary` keeps only the key, as a set leaf.
    Discard {
        /// The family to filter.
        family: Shared,
        /// `(path, entry) -> bool | #boundary`.
        sel: Shared,
    },
    /// `fold(F, op, ev)`: collapses the innermost level of `F` with the binary `op`.
    Fold {
        /// The family to fold.
        family: Shared,
        /// The binary operator.
        op: Shared,
        /// The identity, which is the result of folding an empty level; without one an
        /// empty level folds to `#empty`.
        identity: Option<Shared>,
        /// The number of key levels of `family`, at least 1, which its type gives. A family
        /// with no leaves does not show its depth, and folds to the empty family when the
        /// depth is above 1.
        depth: usize,
        /// The evidence for `op`, which the reduction checker reads (T-Fold).
        ev: Evidence,
    },
    /// `fix(F0, step, ev)`: the least fixed point of `step` above `F0`.
    Fix {
        /// The bottom for a lattice ascent, the domain for the definedness instance.
        init: Shared,
        /// For a lattice, a function from one iterate to the next. For definedness, the
        /// body of the entry at key `key`, which reads the partial family as `this`.
        step: Shared,
        /// The name the definedness body uses for the family being defined.
        this: Arc<str>,
        /// The name of the key variable in the definedness body.
        key: Arc<str>,
        /// Which instance of the rule.
        kind: FixKind,
        /// The evidence for `step`, which T-Fix reads.
        ev: Evidence,
    },
    /// `gen(init, step, guard)`: a loop over generations. The result is the family from
    /// generation number (0 for `init`) to committed frame; a guard result that is not a bool
    /// ends the loop and is stored as the entry after the last frame.
    Gen {
        /// Generation 0.
        init: Shared,
        /// `frame -> frame`: reads generation `t - 1`, returns generation `t`.
        step: Shared,
        /// `frame -> bool | atom`, `true` meaning go on.
        guard: Shared,
        /// Where the guard is tested.
        pos: GuardPos,
    },
    /// Reads the whole value of an input port.
    Read(Arc<str>),
    /// `p <- v`: pushes a value to an output port, giving its acknowledgment (T-Port).
    Push(Arc<str>, Shared),
}

/// Shorthands for building terms in tests and in the front end's elaboration.
pub mod build {
    use super::*;

    /// A variable.
    pub fn var(name: &str) -> Term {
        Term::Var(name.into())
    }

    /// A literal.
    pub fn lit(v: impl Into<Value>) -> Term {
        Term::Lit(v.into())
    }

    /// A lambda.
    pub fn lam(params: &[&str], body: Term) -> Term {
        Term::Lam(
            params.iter().map(|p| Arc::from(*p)).collect(),
            Shared::new(body),
        )
    }

    /// An application.
    pub fn app(f: Term, args: Vec<Term>) -> Term {
        Term::App(Shared::new(f), args)
    }

    /// A primitive applied to arguments.
    pub fn prim(p: Prim, args: Vec<Term>) -> Term {
        Term::Prim(p, args)
    }

    /// `x = e; body`.
    pub fn let_(name: &str, e: Term, body: Term) -> Term {
        Term::Let(name.into(), Shared::new(e), Shared::new(body))
    }

    /// `if c { a } else { b }`.
    pub fn if_(c: Term, a: Term, b: Term) -> Term {
        Term::If(Shared::new(c), Shared::new(a), Shared::new(b))
    }

    /// The term that makes the family `f` again in O(1), for a range kept as its ends:
    /// `range(lo, last + 1)` (`lo ..< last + 1`, whose high end is `2^63` past `i64` for
    /// `..= i64::MAX`) or `rangeFrom(lo)`; `None` for a family kept as its entries. The build
    /// writes it where it would write the family as a literal, since a literal is written entry
    /// by entry, O(n) for a range of n entries, and never ends for `a ..` (plan row RANGE-open).
    /// A range with an end past `i64` is kept as its ends too (RANGE-lazy-wide), so it is made
    /// again the same way, O(digits); `span`, which gives only 64-bit ends, would leave it to
    /// the literal, written entry by entry.
    /// It is written here, not in module `value`, so that `value` names nothing of `term`.
    pub fn made_by(f: &crate::Family) -> Option<Term> {
        if let Some((lo, last)) = f.ends() {
            let high = Value::int(crate::value::built_integer(&last) + 1);
            return Some(prim(Prim::Range, vec![lit(lo), lit(high)]));
        }
        f.open_lo()
            .map(|lo| prim(Prim::RangeFrom, vec![lit(Value::clone(lo))]))
    }
}

/// A part of a term or pattern whose owner is being dropped (module `deep`): a term nested deep
/// is freed in a loop, on any stack.
#[expect(dead_code, reason = "a part is held only to be dropped")]
enum Freed {
    Term(Term),
    Shared(Shared),
    Terms(Vec<Term>),
    Arms(Vec<(Pattern, Term)>),
    Patterns(Vec<Pattern>),
    Fields(Vec<(Arc<str>, Pattern)>),
}

thread_local! {
    /// The parts of terms and patterns waiting to be dropped.
    static FREED: deep::Queue<Freed> = const { deep::Queue::new() };
    /// What a shared subterm still held elsewhere leaves in its place when it is queued.
    static HOLE: Shared = Shared::new(Term::PrimFn(Prim::Tuple));
}

fn free(part: Freed) {
    deep::free_in(&FREED, part);
}

/// Queues the term `t` holds, when `t` is its last owner, and otherwise `t` itself: a subterm
/// that one term holds in several places, as a DAG does, or that another thread lets go of at
/// the same moment, is freed by the queue when its last holder there lets go, not by this
/// term's own drop recursing into it.
fn free_shared(t: &mut Shared) {
    if let Some(t) = Shared::get_mut(t) {
        free(Freed::Term(std::mem::replace(t, Term::PrimFn(Prim::Tuple))));
    } else if let Ok(hole) = HOLE.try_with(Shared::clone) {
        free(Freed::Shared(std::mem::replace(t, hole)));
    }
}

fn free_terms(ts: &mut Vec<Term>) {
    if !ts.is_empty() {
        free(Freed::Terms(std::mem::take(ts)));
    }
}

impl Term {
    /// The name of this node while it is alive, for its source site ([`crate::sites::key`]):
    /// the address one past the end of its own parts, or `None` when it has none. O(1).
    pub(crate) fn site_key(&self) -> Option<usize> {
        match self {
            Term::App(_, args) | Term::Prim(_, args) if !args.is_empty() => Some(parts_end(args)),
            Term::Match(_, arms) if !arms.is_empty() => Some(parts_end(arms)),
            _ => None,
        }
    }
}

/// The address one past the last element of `xs`.
pub(crate) fn parts_end<T>(xs: &[T]) -> usize {
    xs.as_ptr_range().end as usize
}

/// A term's parts are freed in a loop, not by recursion.
impl Drop for Term {
    fn drop(&mut self) {
        if crate::site_table::recording()
            && let Some(k) = self.site_key()
        {
            crate::site_table::forget(k);
        }
        match self {
            Term::Lit(_) | Term::Var(_) | Term::PrimFn(_) | Term::Read(_) => {}
            Term::Lam(_, b) | Term::Push(_, b) => free_shared(b),
            Term::App(f, args) => {
                free_shared(f);
                free_terms(args);
            }
            Term::Prim(_, args) => free_terms(args),
            Term::Let(_, a, b) | Term::Discard { family: a, sel: b } => {
                free_shared(a);
                free_shared(b);
            }
            Term::Fam { domain, body, .. } => {
                free_shared(domain);
                free_shared(body);
            }
            Term::If(a, b, c)
            | Term::Reindex {
                family: a,
                kf: b,
                vf: c,
                ..
            }
            | Term::Gen {
                init: a,
                step: b,
                guard: c,
                ..
            } => {
                free_shared(a);
                free_shared(b);
                free_shared(c);
            }
            Term::Match(e, arms) => {
                free_shared(e);
                if !arms.is_empty() {
                    free(Freed::Arms(std::mem::take(arms)));
                }
            }
            Term::Fold {
                family,
                op,
                identity,
                ..
            } => {
                free_shared(family);
                free_shared(op);
                if let Some(i) = identity {
                    free_shared(i);
                }
            }
            Term::Fix {
                init, step, kind, ..
            } => {
                free_shared(init);
                free_shared(step);
                match kind {
                    FixKind::Lattice { join } => free_shared(join),
                    FixKind::Definedness => {}
                }
            }
        }
    }
}

/// A pattern's parts are freed in a loop, as a term's are.
impl Drop for Pattern {
    fn drop(&mut self) {
        match self {
            Pattern::Wild
            | Pattern::Bind(_)
            | Pattern::Lit(_)
            | Pattern::AnyAtom
            | Pattern::Is(_) => {}
            Pattern::Atom(_, ps) | Pattern::Tuple(ps) => {
                if !ps.is_empty() {
                    free(Freed::Patterns(std::mem::take(ps)));
                }
            }
            Pattern::Fields(_, fs) => {
                if !fs.is_empty() {
                    free(Freed::Fields(std::mem::take(fs)));
                }
            }
        }
    }
}
