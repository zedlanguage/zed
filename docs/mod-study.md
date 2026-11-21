# Study: integer `mod`, the float remainder `floatMod`, and a positive modulus

Checked 2026-11-21. This study answers QUESTIONS A174 as the author decided it (2026-11-21, verbatim):
"A174: do A, but also add `floatMod(x, m)` which gives the floating point residue in `[0..<m]` after
dividing by `m`. Different languages do float mod differently, so survey them and figure out the right
one to implement for `floatMod`. Also survey for both int and float mod what the rounding standard is
for negative `x`. And make sure `m > 0` both `mod` and `floatMod`."

DESIGN.md carries the short form at the definitions (sec:domains, "`div` and `mod`" and "`floatMod`, the
remainder of a float"); this file holds the full tables, quotes, probe outputs and check counts. Plan
rows: FLOAT-mod, FLOAT-floatMod, MOD-positive-modulus, MSG-float-mod-type-error.

## Decisions

1. `mod` takes ints alone; `x mod 360.0` with a float operand is a type error whose repair is
   `floatMod(x, 360.0)`, with the exact `rat(x) - 360r * rat(floor(rat(x) / 360r))` as a note.
2. `x mod m` takes only `m` in `int[1..]`. A modulus proved at most 0 (`x mod 0`, `x mod -3`) is a
   compile error with no test offered; a modulus not proved in `int[1..]` is refused by the rule of
   sec:diagnostics, "The repair of a value outside the ints its use takes", with the test
   `if m > 0 { x mod m } else { … }`. So `mod` has no `#divByZero`.
3. `div` keeps its domain (any nonzero divisor, Euclidean quotient). The law
   `x == m * (x div m) + x mod m` speaks of `div` only where `mod` is defined, at `m >= 1`, so it does
   not force a change to `div`.
4. `floatMod(x, m)`, for a finite `m > 0.0` (proved, as for `mod`), is the float of `[0.0, m)` nearest
   the exact residue `ρ = x − m·⌊x/m⌋`, ties to even. It is computed with round-to-nearest only
   (QUESTIONS A173): `f = fmod(x, m)` (exact); if `f >= 0`, `f + 0.0` (so `-0.0` gives `0.0`); else
   `s = RN(f + m)`, and `s` if `s < m`, `nextDown(m)` if `s == m`. An infinite `x` gives NaN carrying
   `nan()` (`#NaN` under `@fpstrict`); a NaN `x` gives NaN.

## Integer conclusion (survey 1 below)

Survey 1 has 51 integer remainder operations in 35 languages and standards (Scheme R6RS and R7RS counted
apart). 26 truncate (C, C++, Java `%`, C#, JavaScript BigInt, Go, Rust `%`, Swift, Kotlin `rem`, Scala,
Ruby `remainder`, PHP, Haskell `rem`, OCaml, Erlang, Elixir `rem`, Ada `rem`, Fortran `MOD`, Dart
`remainder`, Julia `rem`, Zig `@rem`, Smalltalk `rem:`, SQL, PostgreSQL, MySQL, SQLite); 17 floor (Java
`floorMod`, Kotlin `mod`, Python, Ruby `%`, Perl, Lua, R, Haskell `mod`, Elixir `Integer.mod`, Common
Lisp `mod`, Ada `mod`, Fortran `MODULO`, Julia `mod`, Zig `@mod`, Smalltalk `\\`, Mathematica, Excel);
3 are Euclidean (Rust `rem_euclid`, Scheme R6RS `mod`, Dart `%`); and 5 offer several rules or another
one (Common Lisp `truncate`/`ceiling`/`round`, R6RS `div0`/`mod0`, R7RS `floor/` and `truncate/`, Julia
`div(x, y, r)` with a rounding mode, Zig `a % b`, positive operands only). With `m >= 1` the floored and the Euclidean
definitions are the same function: each gives the one `r` with `0 <= r <= m - 1` and `x - r` a multiple
of `m`; they differ only at a negative modulus, which Zed's `mod` does not take. Literature: Boute, "The
Euclidean definition of the functions div and mod", ACM TOPLAS 14(2):127–144, 1992,
doi:10.1145/128861.128862, p. 127: "Its distinguishing feature is that 0 ≤ D mod d < |d| irrespective of
the signs of D and d"; Leijen, "Division and Modulus for Computer Scientists", 2001,
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/divmodnote-letter.pdf; Knuth, *The
Art of Computer Programming*, vol. 1, §1.2.4, and Graham, Knuth and Patashnik, *Concrete Mathematics*,
§3.4, eq. (3.21), "x mod y = x − y⌊x/y⌋, for y ≠ 0" (quoted from Furia, arXiv:1406.5453, §2; neither
book was read). Only Zig restricts the sign of the modulus of an operator: `a % b` with signed operands
requires them "comptime-known and positive", and Zig 0.11.0–0.14.0 documented `@rem`/`@mod` with
"denominator > 0".

## Float candidates and scores

`f = fmod(x, m)`, exact (C11 F.10.7.1: "the returned value is exact and is independent of the current
rounding direction mode"). RN is round to nearest, ties to even; RD is round toward minus infinity.

| candidate | definition | used by |
|---|---|---|
| a | `RN(x − RN(m·floor(RN(x/m))))` | the textbook formula written in floats (C, Rust, Python "formula" rows) |
| b | `f < 0 ? RN(f + m) : f` | Python `%`, Rust `rem_euclid`, Lua `%`, Dart `%`, Ruby `%`, NumPy `mod`, Haskell `mod'` (in effect) |
| c | `RN(ρ)` with a result of `m` sent to `+0.0` | none found; nearest on the circle |
| d | `RD(ρ)` | none found; needs directed rounding |
| e | `f < 0 ? (s = RN(f + m); s == m ? nextDown(m) : s) : f + 0.0` | chosen |
| g | `fmod(RN(f + m), m)` | the JavaScript idiom `((x % m) + m) % m`, Zig `@mod` on floats (from memory) |

Exhaustive check over every pair of a finite `x` and a finite `m > 0` (`fmcheck`, Rust, exact residue by
integer arithmetic on the significands; scratch only, not in the repository): f16 2,015,299,584 pairs,
bf16 2,130,673,920 pairs. Sampled: f32 160,000,000 pairs (8 seeds), f64 16,000,000 pairs (8 seeds),
subnormals included. `u` is the spacing of the format just below `m`.

| candidate | f16 exhaustive | bf16 exhaustive | f32 sampled | score 0–10 | reasoning |
|---|---|---|---|---|---|
| e | 0 out of `[0, m)`, 0 `-0.0`, 0 monotonicity breaks, max error 0.99999999814 u; error above u/2 only on 200,227,841 pairs where `ρ` rounds to `m` and the clamp gives `nextDown(m)` | 0 out of range, 0 `-0.0`, 0 breaks, max error below 1 u | 0 out of range, 0 `-0.0`, max error below 1 u | 9 | always in `[0, m)` as the author asked, the nearest float there to `ρ`, monotone, never `-0.0`, round-to-nearest only (A173); one comparison more than (b); not 10 because the clamp gives an error up to 1 u where (b) gives at most u/2 by leaving the range |
| c | 0 out of range; 200,242,688 pairs give `0.0` where `ρ` is just below `m` (error up to `m`, but 0 is congruent to `m`); 29,183 monotonicity breaks | 497,730,880 such pairs; 32,319 breaks | 44,371,754 such pairs | 8 | in range and nearest on the circle, natural for angles, but it jumps from just below `m` to `0` inside one period, so `floatMod` would not be monotone in `x` |
| d | 0 out of range; 295,477,248 pairs with error above u/2, max below 1 u | max below 1 u | max below 1 u | 7 | in range and monotone, but needs a directed rounding mode, which A173 rules out of the definition, and it is not nearest on 295 million f16 pairs |
| b | 200,242,688 pairs return `m` (out of range); 2,340,669 return `-0.0`; max error u/2 | 497,730,880 return `m`; 14,893,292 `-0.0` | 44,371,754 return `m`; 1,331,980 `-0.0` | 3 | correctly rounded, but returns `m`, outside `[0..<m]`, which the author's answer excludes; Rust's own documentation calls this "violating the mathematical definition" |
| a | 466,207,580 out of range, 239,207,857 infinite, 180,333,542 equal to `m`, 20,909,291 breaks, max error 34,792 u | 846,809,441 out of range, 264,297,147 infinite | 51,053,430 out of range, 5,007,826 infinite | 2 | the quotient and product round, so the result can be infinite, negative or far from `ρ` (`1e17 % 3.0`) |
| g | 290,414,154 pairs with error above u/2, 2,096,128 NaN, 44,030 breaks, max error 2048 u | 32,640 NaN, 48,510 breaks | 637 NaN | 2 | the sum `f + m` rounds before the second `fmod`, so a small positive `x` can give `0.0` (`x = 2^-24`, `m = 1.0` in f16) and `f + m` can overflow to infinity and give NaN |

The best candidate scores 9, so no QUESTIONS entry was opened (the brief opens one only when none does).

## Proof that (e) is the float of `[0.0, m)` nearest `ρ` (round-to-nearest only)

1. `f = fmod(x, m)` is exact, `f ≡ x (mod m)` and `|f| < m` (C11 7.12.10.1 and F.10.7.1).
2. If `f >= 0`, then `ρ = f`, a float in `[0, m)`; `f + 0.0` is `f` with `-0.0` mapped to `0.0`.
3. If `f < 0`, then `ρ = f + m`, a real in `(0, m)`, and `s = RN(ρ)` is the float nearest `ρ` among all
   floats, ties to even, with `0 <= s <= m` since `0` and `m` are floats and RN is monotone.
4. If `s < m`, `s` lies in `[0, m)` and is nearest `ρ` among all floats, so it is nearest among those in
   `[0, m)`; its error is at most u/2.
5. If `s == m`, then `ρ >= (nextDown(m) + m)/2 > nextDown(m)`, so `nextDown(m)` is the float of
   `[0, m)` nearest `ρ` (the only nearer float, `m`, is excluded); its error is in `[u/2, u)`.
6. On one period `x ∈ [k·m, (k+1)·m)` the residue is `x − k·m`, nondecreasing in `x`, and "nearest float
   in `[0, m)`" is a nondecreasing map, so `floatMod` is nondecreasing on each period.

The exhaustive f16/bf16 counts above check steps 1–6 on every pair.

## Special values (every format)

| `x` | `m` finite, `m > 0` | result |
|---|---|---|
| `0.0` or `-0.0` | any | `0.0` |
| finite, a multiple of `m` | any | `0.0` |
| finite | the least subnormal | `0.0` (every finite float is a multiple of it) |
| `+inf` or `-inf` | any | NaN carrying `nan()`, `#NaN` under `@fpstrict` |
| NaN | any | NaN |

A modulus of `0.0`, `-0.0`, a negative one, an infinity or NaN is never reached: it is refused at compile
time (no test offered where proved out of range; otherwise the test
`if m > 0.0 && m.isFinite { floatMod(x, m) } else { … }`). The f16 special-value output of `fmcheck`
is in the last section.


Survey tables, read against each document on 2026-11-21 and run where a toolchain was on hand.

Markers used in the tables:
- **doc**: stated in the cited document, fetched today (quote below).
- **run**: observed today on this machine (versions: Python 3.14.10, Node 22.22.2, Ruby 4.0.9, Perl 5.42.3, Go 1.26.10, rustc 1.102.0-nightly 2026-11-17, Java 26.0.2, Dart 3.13.7, GHC 9.10.3, SQLite 3.51.2, gcc/glibc).
- **src**: read in the implementation source, fetched today.
- **mem**: from memory, not checked.
- **inf**: inferred from the documented definition, not stated in the document.

Notation: x = dividend, m (or y, n, b) = modulus/divisor. "T" = truncated quotient (toward zero), "F" = floored (toward minus infinity), "E" = Euclidean (remainder always >= 0), "R" = rounded to nearest, ties to even.

## Survey 1: integer mod/div with negative operands

| language | operation | quotient rounding | sign/range of remainder | modulus 0 | negative modulus | source URL |
|---|---|---|---|---|---|---|
| C99/C11 | `/`, `%` | T (doc: "fractional part discarded", footnote "truncation toward zero") | sign of x (inf from identity (a/b)*b + a%b == a) | UB (doc 6.5.5p5) | allowed; result sign of x | https://port70.net/~nsz/c/c11/n1570.html#6.5.5 |
| C++ (draft) | `/`, `%` | T (doc, footnote "truncation towards zero") | sign of x (inf) | UB (doc [expr.mul]/4) | allowed | https://eel.is/c++draft/expr.mul |
| Java | `/`, `%` | T (doc "Integer division rounds toward 0") | sign of x; abs < abs(m) (doc) | `ArithmeticException` (doc; run: "/ by zero") | allowed; `5%(-3)==2` (doc) | https://docs.oracle.com/javase/specs/jls/se21/html/jls-15.html#jls-15.17.3 |
| Java | `Math.floorMod`, `floorDiv` | F | sign of m or zero; -abs(y) < r < abs(y) (doc) | `ArithmeticException` (doc; run) | allowed; `floorMod(7,-3)==-2` (run) | https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/lang/Math.html |
| C# | `/`, `%` | T (doc "rounded toward zero") | sign of x (doc) | `System.DivideByZeroException` (doc) | allowed | https://learn.microsoft.com/en-us/dotnet/csharp/language-reference/language-specification/expressions (12.13.4) |
| JavaScript BigInt | `/`, `%` | T (doc BigInt::divide uses truncate) | sign of x (doc note) | `RangeError` (doc; run: "RangeError: Division by zero") | allowed; `7n % -3n == 1n` (run) | https://tc39.es/ecma262/#sec-numeric-types-bigint-remainder |
| Go | `/`, `%` | T (doc "truncated division") | sign of x, abs(r) < abs(y) (doc table) | constant divisor: compile error; run time: panic (doc; run: "runtime error: integer divide by zero") | allowed; `5 % -3 == 2` (doc) | https://go.dev/ref/spec#Arithmetic_operators |
| Rust | `/`, `%` | T (doc) | sign of x (doc) | panic (doc; run: "attempt to calculate the remainder with a divisor of zero") | allowed | https://doc.rust-lang.org/reference/expressions/operator-expr.html |
| Rust | `i64::rem_euclid`, `div_euclid` | E (q rounds toward -inf if rhs > 0, toward +inf if rhs < 0) | 0 <= r < abs(rhs) (doc) | panic; also panics for MIN, -1 (doc) | allowed; `7.rem_euclid(-4)==3` (doc) | https://doc.rust-lang.org/std/primitive.i64.html#method.rem_euclid |
| Swift | `/`, `%` | T | sign of lhs, magnitude < rhs.magnitude (doc) | precondition: "rhs must not be zero" (doc); runtime trap (mem) | sign of m ignored: "a % b and a % -b always give the same answer" (doc) | https://raw.githubusercontent.com/swiftlang/swift/main/stdlib/public/core/Integers.swift ; https://raw.githubusercontent.com/swiftlang/swift-book/main/TSPL.docc/LanguageGuide/BasicOperators.md |
| Kotlin | `rem` / `%` | T | zero or sign of dividend, abs < abs(divisor) (doc) | `ArithmeticException` (mem, JVM) | allowed | https://kotlinlang.org/api/core/kotlin-stdlib/kotlin/-int/rem.html |
| Kotlin | `mod` (since 1.5) | F | zero or sign of divisor, abs < abs(divisor) (doc) | `ArithmeticException` (mem) | allowed | https://kotlinlang.org/api/core/kotlin-stdlib/kotlin/mod.html |
| Scala | `/`, `%` on Int | T (same as Java; spec defers to "the given arithmetic operation" of the type) | sign of x (mem, JVM) | `ArithmeticException` (mem) | allowed | https://www.scala-lang.org/api/current/scala/Int.html ; https://scala-lang.org/files/archive/spec/2.13/12-the-scala-standard-library.html |
| Python | `//`, `%`, `divmod` | F (doc "floor") | sign of m or zero; abs < abs(m) (doc) | `ZeroDivisionError` (doc; run) | allowed; `7 % -3 == -2` (run) | https://docs.python.org/3/reference/expressions.html#binary-arithmetic-operations |
| Ruby | `Integer#%`/`modulo`, `/`, `divmod` | F (doc: n-r*(n/r).floor) | sign of m (doc examples `10 % -3 == -2`) | `ZeroDivisionError: divided by 0` (run) | allowed | https://docs.ruby-lang.org/en/master/Integer.html |
| Ruby | `Integer#remainder` | T | sign of x (doc examples `-11.remainder(4) == -3`) | `ZeroDivisionError` (mem) | allowed | https://docs.ruby-lang.org/en/master/Integer.html#method-i-remainder |
| Perl | `%` | F for integers (doc) | m > 0: result in [0, m); m < 0: result <= 0 (doc) | dies "Illegal modulus zero" (run) | allowed (doc); under `use integer`: C semantics, -7%3 == -1 (run) | https://perldoc.perl.org/perlop#Multiplicative-Operators |
| PHP | `%`, `intdiv` | T | sign of dividend (doc) | `%`: `DivisionByZeroError` "Modulo by zero" (mem); `intdiv`: `DivisionByZeroError` (doc); `intdiv(PHP_INT_MIN,-1)`: `ArithmeticError` (doc) | allowed; `5 % -3 == 2` (doc) | https://www.php.net/manual/en/language.operators.arithmetic.php ; https://www.php.net/manual/en/function.intdiv.php |
| Lua 5.4 | `//`, `%` | F (doc) | sign of m (inf from floor) | integers: error "attempt to perform 'n%%0'" (src lvm.c) | allowed | https://www.lua.org/manual/5.4/manual.html#3.4.1 |
| R | `%/%`, `%%` | F (doc) | sign(r) == sign(y) (doc) | `NA_integer_` for integers, `NaN` for doubles (doc) | allowed (`x %% -3` example, doc) | https://stat.ethz.ch/R-manual/R-devel/library/base/html/Arithmetic.html |
| Haskell | `quot`/`rem` | T (doc) | sign of x (inf) | report: laws stated only "if y is non-zero"; GHC throws `divide by zero` (run) | allowed | https://www.haskell.org/onlinereport/haskell2010/haskellch6.html#x13-1360006.4.2 |
| Haskell | `div`/`mod` | F (doc) | sign of y (inf; run `7 `mod` (-3) == -2`) | GHC `divide by zero` (run) | allowed | same |
| OCaml | `/`, `mod`, `Int.div`, `Int.rem` | T (doc) | "x mod y is negative only if x < 0"; abs <= abs(y)-1 (doc) | `Division_by_zero` (doc) | allowed | https://ocaml.org/manual/5.2/api/Stdlib.html ; https://ocaml.org/manual/5.2/api/Int.html |
| Erlang | `div`, `rem` | T (mem) | sign of x (mem) | `badarith` error (mem) | allowed | https://www.erlang.org/doc/system/expressions.html (doc gives no sign rule) |
| Elixir | `div/2`, `rem/2` | T (doc) | sign of dividend (doc) | `ArithmeticError` (doc) | allowed; `rem(6,-4)==2` (doc) | https://hexdocs.pm/elixir/Kernel.html#rem/2 |
| Elixir | `Integer.floor_div/2`, `Integer.mod/2` | F (doc) | sign of divisor (doc) | `ArithmeticError` (doc) | allowed; `Integer.mod(6,-4)==-2` (doc) | https://hexdocs.pm/elixir/Integer.html#mod/2 |
| Common Lisp | `floor`/`mod` | F (doc) | zero or sign of divisor (doc Notes) | CLHS lists "Exceptional Situations: None"; implementations signal `division-by-zero` (mem) | allowed; `(mod 13 -4) => -3` (doc) | https://www.lispworks.com/documentation/HyperSpec/Body/f_mod_r.htm ; https://www.lispworks.com/documentation/HyperSpec/Body/f_floorc.htm |
| Common Lisp | `truncate`/`rem`; also `ceiling`, `round` (ties even) | T / C / R (doc) | rem: sign of number (doc examples) | as above | allowed | same |
| Scheme R6RS | `div`/`mod` | E (doc examples: `(mod -123 -10) = 7`) | 0 <= mod < abs(x2) (doc examples; formula is an image on the page) | "&assertion" exception (doc) | allowed | https://www.r6rs.org/final/html/r6rs/r6rs-Z-H-14.html#node_sec_11.7.3.1 |
| Scheme R6RS | `div0`/`mod0` | R-like: mod0 "lies within a half-open interval centered on zero" (doc); -abs(x2/2) <= mod0 < abs(x2/2) (mem) | centered | &assertion (doc) | allowed | same |
| Scheme R7RS | `floor/`, `floor-quotient`, `floor-remainder`; `truncate/`, ... | F and T (doc) | floor: sign of n2; truncate: sign of n1 (doc examples) | "It is an error if n2 is zero" (doc) | allowed; `(floor/ 5 -2) => -3 -1` (doc) | https://small.r7rs.org/attachment/r7rs.pdf (6.2.6) |
| Ada | `/`, `rem` | T (doc identity (-A)/B = -(A/B) = A/(-B)) | rem has sign of A (doc) | `Constraint_Error` (doc) | allowed | https://www.adaic.org/resources/add_content/standards/22rm/html/RM-4-5-5.html |
| Ada | `mod` | F | zero or sign of B, abs < abs(B) (doc) | `Constraint_Error` (doc) | allowed | same |
| Fortran | `MOD(A,P)` | T: A - INT(A/P)*P (doc) | sign of A, magnitude < abs(P) (doc) | P "shall be ... not equal to zero" (doc); standard: processor dependent (mem) | allowed | https://gcc.gnu.org/onlinedocs/gfortran/MOD.html |
| Fortran | `MODULO(A,P)` | F | sign of P (doc); gfortran text for integers says "R is between 0 (inclusive) and P (exclusive)" | P "shall not be zero" (doc) | allowed | https://gcc.gnu.org/onlinedocs/gfortran/MODULO.html |
| Dart | `num.%` (inherited by `int`) | E | "always positive" (doc), i.e. 0 <= r < abs(b) | `IntegerDivisionByZeroException` (run); `~/` doc: "other must not be zero" | allowed; `5 % -3 == 2`, `-5 % -3 == 1` (doc) | https://api.dart.dev/stable/dart-core/num/operator_modulo.html |
| Dart | `remainder`, `~/` | T (doc) | sign of dividend (doc) | as above (mem for remainder) | allowed | https://api.dart.dev/stable/dart-core/num/remainder.html ; https://api.dart.dev/stable/dart-core/num/operator_truncate_divide.html |
| Julia | `div`/`÷`, `rem`/`%` | T (doc examples `-5 ÷ 3 == -1`) | sign of x (doc) | `DivideError` (mem) | allowed | https://docs.julialang.org/en/v1/base/math/ |
| Julia | `fld`, `mod` | F (doc) | sign of y (doc) | `DivideError` (mem) | allowed | same |
| Julia | `div(x,y,r)`, `rem(x,y,r)` with RoundingMode | any of T, F, C (RoundUp), R (RoundNearest) (doc) | per mode (doc) | | allowed | same |
| Zig | `@rem`, `@divTrunc` | T (doc) | sign of numerator (`@rem(-5,3) == -2`, doc) | "Caller guarantees denominator != 0", else safety-checked illegal behavior "Remainder Division by Zero" (doc, master and 0.15.1); 0.11.0-0.14.0 said "denominator > 0" | master: allowed; 0.11-0.14 docs: forbidden | https://ziglang.org/documentation/master/ |
| Zig | `@mod`, `@divFloor` | F (doc) | sign of denominator (inf) | same as `@rem` | same as `@rem`; `std.math.mod` returns `error.NegativeDenominator` (src) | same; https://raw.githubusercontent.com/ziglang/zig/master/lib/std/math.zig |
| Zig | `a % b` | | | "Can cause Division by Zero for integers" | "Signed or floating-point operands must be comptime-known and positive. In other cases, use @rem or @mod instead." (doc) | same |
| Smalltalk (Pharo 13) | `//`, `\\` | F (src comment) | sign of aNumber (src comment) | `ZeroDivide` (src Integer>>//) | allowed; `9 \\ -4 = -3` | https://raw.githubusercontent.com/pharo-project/pharo/Pharo13/src/Kernel/Number.class.st |
| Smalltalk (Pharo 13) | `quo:`, `rem:` | T (src) | sign of self (src) | `ZeroDivide` (mem) | allowed | same |
| Mathematica | `Mod[m,n]`, `Quotient` | F (Quotient is floor; mem) | "same sign as the modulus" (doc); 0..n-1 for positive integers (doc) | `Indeterminate` with message `Mod::indet` (mem) | allowed | https://reference.wolfram.com/language/ref/Mod.html |
| Excel | `MOD(n,d)` | F: n - d*INT(n/d) (doc) | "same sign as divisor" (doc) | `#DIV/0!` (doc) | allowed; `MOD(3,-2) = -1` (doc) | https://support.microsoft.com/en-us/office/mod-function-9b6cd169-b6ee-406a-a97b-edf2a9dc24f3 |
| SQL standard | `MOD(N,M)` | T (mem) | sign of N (mem) | exception "data exception - division by zero" (mem) | allowed | ISO/IEC 9075-2 is not public; mem |
| PostgreSQL | `%`, `mod(y,x)`, `div(y,x)` | T: `/` and `div` "truncates towards zero" (doc) | sign of dividend (mem) | error "division by zero" (mem) | allowed | https://www.postgresql.org/docs/current/functions-math.html |
| MySQL 8.4 | `MOD(N,M)`, `%`, `MOD` operator | T (mem) | sign of N (mem; doc gives no negative example) | `MOD(N,0)` returns NULL (doc) | allowed | https://dev.mysql.com/doc/refman/8.4/en/mathematical-functions.html (curl got 403; read through WebFetch) |
| SQLite | `%`, `/` | T: "Integer divide yields an integer result, truncated toward zero" (doc) | sign of dividend (run: -7%3 = -1) | NULL (run: `7%0` gives empty/NULL) | allowed; `7%-3 = 1` (run) | https://www.sqlite.org/lang_expr.html |

## Survey 2: floating-point mod

"can return m": whether a finite result can equal abs(m) (or m) because the exact result is rounded.

| language | operation | definition | sign/range | modulus 0 | negative modulus | can return m | exact | source URL |
|---|---|---|---|---|---|---|---|---|
| C | `fmod` | x - n*y, n integer, result sign of x, magnitude < abs(y) (doc 7.12.10.1) | sign of x, abs < abs(y) | implementation-defined: domain error or 0 (7.12.10.1); Annex F: NaN + invalid | allowed; sign ignored | no | yes, Annex F: "the returned value is exact and is independent of the current rounding direction mode" (doc F.10.7.1) | https://port70.net/~nsz/c/c11/n1570.html#7.12.10.1 |
| C | `remainder` | IEC 60559 REM: n = integer nearest x/y, ties even (doc footnote 239) | abs <= abs(y)/2 (inf); zero has sign of x | implementation-defined: domain error or 0 (7.12.10.2); Annex F defers to IEC 60559 (NaN) | allowed | no | yes (doc F.10.7.2) | https://port70.net/~nsz/c/c11/n1570.html#7.12.10.2 |
| C | `remquo` | same remainder; stores sign of x/y and at least 3 low bits of quotient (doc 7.12.10.3) | as remainder | as remainder | allowed | no | yes (doc F.10.7.3) | same |
| IEEE 754-2019 | `remainder` (5.3.1) | r = x - y*n, n integer nearest x/y, ties even (quoted via C11 footnote 239, which quotes IEC 60559) | abs(r) <= abs(y)/2 | invalid operation, NaN (mem) | allowed | no | yes: "the remainder is always exact" (mem, 754 text) | standard not public; text via C11 footnote 239 |
| Python | `%` on float | F: same sign as second operand (doc) | sign of m; abs < abs(m) "mathematically" but not numerically (doc) | `ZeroDivisionError` (run) | allowed | yes: `-1e-100 % 1e100 == 1e100` (doc, run) | no (doc: "may not be exactly computable") | https://docs.python.org/3/reference/expressions.html (footnote 1) |
| Python | `math.fmod` | C fmod (doc) | sign of x | `ValueError: math domain error` (run) | allowed | no | yes (doc: intent is "exactly ... equal to x - n*y") | https://docs.python.org/3/library/math.html#math.fmod |
| Python | `math.remainder` | IEEE 754 remainder (doc) | abs(r) <= 0.5*abs(y) (doc) | `ValueError` (doc) | allowed | no | yes (doc) | https://docs.python.org/3/library/math.html#math.remainder |
| NumPy | `remainder` / `mod` | Python `%` semantics, complement of `floor_divide` (doc) | sign of x2 (doc) | integers: returns 0 (doc); floats: NaN (mem) | allowed | yes (mem: implementation is fmod then `+= b`) | no (mem) | https://numpy.org/doc/stable/reference/generated/numpy.remainder.html |
| NumPy | `fmod` | C fmod (doc) | sign of x1 (doc) | NaN (mem) | allowed | no | yes (inf from C fmod) | https://numpy.org/doc/stable/reference/generated/numpy.fmod.html |
| Julia | `mod(x,y)` / `rem(x,y,RoundDown)` | x - y*fld(x,y) without intermediate rounding, then rounded (doc) | sign of y, magnitude < abs(y) "with some exceptions" (doc) | NaN (mem) | allowed | yes: "if the exact result is very close to y, then it may be rounded to y"; `mod(-eps(), 3) == 3.0` (doc). Note: the `rem(x,y,RoundDown)` text on the same page claims the interval [0, y), which contradicts this | no: "The result may not be exact if x and y have different signs" (doc) | https://docs.julialang.org/en/v1/base/math/#Base.mod |
| Julia | `rem` / `%` | T (doc) | sign of x | NaN (mem) | allowed | no | yes: "This value is always exact" (doc) | same |
| Julia | `rem(x,y,RoundNearest)` | IEEE remainder | [-abs(y)/2, abs(y)/2] (doc) | NaN (mem) | allowed | no | yes (doc) | same |
| Julia | `mod2pi(x)` | modulus after division by the exact real 2pi (doc) | [0, 2pi) (doc) | n/a | n/a | the doc warns `mod2pi(2π)` is not 0 | rounded result of exact-2pi reduction (doc) | https://docs.julialang.org/en/v1/base/math/#Base.Math.mod2pi |
| Rust | `f64 % f64` | doc: "same sign as the dividend and is computed as: x - (x / y).trunc() * y" | sign of x | NaN (run) | allowed | no | yes in practice (fmod/LLVM frem): `1e17 % 3.0 == 1` while the doc formula evaluated in f64 gives 0 (run). The doc formula describes the math, not the f64 evaluation | https://doc.rust-lang.org/std/primitive.f64.html (impl Rem) |
| Rust | `f64::rem_euclid` | least nonnegative remainder (doc) | 0.0 <= r < abs(rhs) "in most cases" (doc) | NaN (mem) | allowed (sign ignored) | yes: "it can result in r == rhs.abs()" (doc); `(-f64::EPSILON).rem_euclid(3.0) == 3.0` (run) | no; doc: "guaranteed to be the rounded infinite-precision result" (that is, correctly rounded, not exact) | https://doc.rust-lang.org/std/primitive.f64.html#method.rem_euclid |
| Go | `math.Mod` | floating-point remainder of x/y (doc) | "magnitude ... less than y and its sign agrees with that of x" (doc) | NaN (doc) | allowed | no | yes (inf: fmod semantics; doc does not say) | https://pkg.go.dev/math#Mod |
| Go | `math.Remainder` | IEEE 754 remainder (doc) | abs <= abs(y)/2 (inf) | NaN (doc) | allowed | no | yes (inf) | https://pkg.go.dev/math#Remainder |
| Java | `%` on double | T, "analogous to" fmod (doc) | sign of dividend (doc) | NaN, never throws (doc) | allowed | no | yes: "Overflow, underflow, or loss of precision cannot occur" (doc) | https://docs.oracle.com/javase/specs/jls/se21/html/jls-15.html#jls-15.17.3 |
| Java | `Math.IEEEremainder` | IEEE 754 remainder (doc) | zero has sign of first argument | NaN (doc) | allowed | no | yes (inf) | https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/lang/Math.html#IEEEremainder(double,double) |
| JavaScript | `%` on Number | T; "not the same as the 'remainder' operation defined by IEEE 754-2019" (doc) | sign of dividend (-0 kept) | NaN (doc step 4) | allowed | no | yes (inf: exact real remainder then 𝔽(), and the exact value is representable) | https://tc39.es/ecma262/#sec-numeric-types-number-remainder |
| C# | `%` on double | x - n*y, n largest integer <= x/y on absolute values (doc) | sign of x (doc) | NaN (doc table) | allowed | no | not stated; inf yes | https://learn.microsoft.com/en-us/dotnet/csharp/language-reference/language-specification/expressions (12.13.4) |
| C# | `Math.IEEERemainder` | x - y*Q, Q = x/y rounded to nearest, ties even (doc) | +0 or -0 by sign of x when zero (doc) | NaN (mem) | allowed | no | yes (inf) | https://learn.microsoft.com/en-us/dotnet/api/system.math.ieeeremainder |
| Swift | `truncatingRemainder(dividingBy:)` | T (doc) | sign of self, strictly smaller in magnitude than other (doc) | NaN (mem) | allowed | no | yes: "always exact" (doc) | https://developer.apple.com/documentation/swift/double/truncatingremainder(dividingby:) |
| Swift | `remainder(dividingBy:)` | IEEE 754 remainder (doc) | closed range -abs(other/2)...abs(other/2) (doc) | NaN (mem) | allowed | no | yes: "always exact" (doc) | https://developer.apple.com/documentation/swift/double/remainder(dividingby:) |
| Kotlin | `Double.rem` / `%` | T (doc) | zero or sign of dividend, abs < abs(divisor) (doc) | NaN (mem) | allowed | no | yes (inf, JVM `%`) | https://kotlinlang.org/api/core/kotlin-stdlib/kotlin/-double/rem.html |
| Kotlin | `Double.mod` | F (doc) | zero or sign of divisor; "the absolute value of the result can be less than or equal to the absolute value of the divisor" (doc) | NaN (mem) | allowed | yes (doc) | no: "If the result cannot be represented exactly, it is rounded" (doc) | https://kotlinlang.org/api/core/kotlin-stdlib/kotlin/mod.html |
| Dart | `double.%` | E extended to doubles (doc) | doc: 0 <= r < abs(b), "always positive" | NaN (run) | allowed; `-7.5 % -2 == 0.5` (run) | yes: `-1e-100 % 1e100 == 1e100` (run), contradicting the doc's 0 <= r < abs(b) | no (inf from run) | https://api.dart.dev/stable/dart-core/double/operator_modulo.html |
| Dart | `double.remainder` | T (doc) | sign of dividend (doc) | NaN (mem) | allowed | no | not stated | https://api.dart.dev/stable/dart-core/double/remainder.html |
| Haskell | `Data.Fixed.mod'` | n - fromInteger (floor (toRational n / toRational d)) * d (src) | sign of d (inf) | `divide by zero` / Ratio exception (mem) | allowed; `mod' 7.5 (-2) == -0.5` (run) | yes: `mod' (-1e-100) 1e100 == 1e100` (run) | no: the multiply and subtract round (src) | https://hackage.haskell.org/package/base/docs/Data-Fixed.html ; src https://hackage.haskell.org/package/base/docs/src/Data.Fixed.html |
| Fortran | `MOD` on REAL | A - INT(A/P)*P (doc) | sign of A, magnitude < abs(P) (doc) | P shall not be zero (doc) | allowed | no (mem: gfortran uses fmod) | gfortran: yes (mem, fmod); the doc formula read literally would round | https://gcc.gnu.org/onlinedocs/gfortran/MOD.html |
| Fortran | `MODULO` on REAL | A - FLOOR(A/P)*P (doc) | sign of P, magnitude < abs(P) (doc) | P shall not be zero (doc) | allowed | yes in practice (mem: fmod then add P) despite the doc's "magnitude less than" | no (mem) | https://gcc.gnu.org/onlinedocs/gfortran/MODULO.html |
| Lua 5.4 | `%` on floats | F (doc); implemented as `m = fmod(a,b); if (m*b < 0) m += b` (src llimits.h) | sign of b | NaN (inf: IEEE rules, doc says "machine's rules") | allowed | yes (src: `-1e-100 % 1e100` adds b and rounds to b) | no when the adjustment fires (src) | https://www.lua.org/manual/5.4/manual.html#3.4.1 ; https://raw.githubusercontent.com/lua/lua/v5.4/llimits.h |
| Lua 5.4 | `math.fmod` | T (doc) | sign of x | integers: error; floats: NaN (mem) | allowed | no | yes (inf, C fmod) | https://www.lua.org/manual/5.4/manual.html#pdf-math.fmod |
| R | `%%` on doubles | F (doc) | sign(r) == sign(y) (doc) | NaN (doc) | allowed | not stated (mem: unknown) | no: "subject to catastrophic loss of accuracy"; "subject to representation error" (doc) | https://stat.ethz.ch/R-manual/R-devel/library/base/html/Arithmetic.html |
| MATLAB | `mod(a,m)` | a - m.*floor(a./m) (doc) | zero or sign of divisor (doc) | `mod(a,0)` returns a (doc) | allowed | not stated | no; "attempts to compensate for floating-point round-off effects to produce exact integer results when possible" (doc). The tolerance rule (if a./m is within roundoff of an integer, that integer is used) is from older documentation and is not on the current page (mem) | https://www.mathworks.com/help/matlab/ref/double.mod.html (curl 403; read through WebFetch) |
| MATLAB | `rem(a,b)` | a - b.*fix(a./b) (doc) | zero or sign of dividend (doc) | `rem(a,0)` is NaN (doc) | allowed | no | "When possible, rem attempts to produce exact integer results by compensating for floating-point round-off effects" (doc) | https://www.mathworks.com/help/matlab/ref/double.rem.html |
| Mathematica | `Mod` on reals | m - n Quotient[m,n] (doc) | sign of modulus (doc) | Indeterminate (mem) | allowed | not stated | machine reals: rounding; doc "Possible Issues": some computations need higher internal precision (doc) | https://reference.wolfram.com/language/ref/Mod.html |
| Common Lisp | `mod`, `rem` on floats | remainder of `floor` / `truncate` (doc); `(mod -13.4 1) => 0.6` (doc) | mod: sign of divisor (doc Notes) | unspecified (doc "None"); mem: division-by-zero | allowed | not specified (inf yes in implementations that compute number - q*divisor) | not specified | https://www.lispworks.com/documentation/HyperSpec/Body/f_mod_r.htm |
| Zig | `@mod` on floats | floored modulus (doc, no float-specific text) | sign of denominator (inf) | "Caller guarantees denominator != 0" (doc) | allowed (master) | mem: lowered as rem(rem(a,b)+b, b), so a rounding to b becomes 0; not checked | no (mem) | https://ziglang.org/documentation/master/#mod |
| Zig | `@rem` on floats | truncated (doc) | sign of numerator | as above | allowed | no | yes (mem, fmod) | https://ziglang.org/documentation/master/#rem |
| PHP | `fmod` | num1 = i*num2 + r, r sign of num1, magnitude < abs(num2) (doc) | sign of num1 | NAN (doc) | allowed | no | yes (inf, C fmod) | https://www.php.net/manual/en/function.fmod.php |
| Ruby | `Float#%` | f - r*(f/r).floor (doc) | sign of r (doc examples) | `ZeroDivisionError: divided by 0` (run, Ruby 4.0.9) | allowed | yes: `-1e-100 % 1e100 == 1.0e+100` (run) | no (inf) | https://docs.ruby-lang.org/en/master/Float.html |
| OCaml | `mod_float` (also `Float.rem`) | a - n*b, n = a/b rounded toward zero (doc) | sign of a (inf) | NaN (mem) | allowed | no | yes (mem, C fmod) | https://ocaml.org/manual/5.2/api/Stdlib.html |
| SQLite | `mod(X,Y)` (math functions) | "similar to the '%' operator, except that it works for non-integer arguments" (doc) | sign of X (run: `mod(-7.5,2) = -1.5`) | NULL (run) | allowed | no (inf, fmod) | inf yes | https://www.sqlite.org/lang_mathfunc.html |

## Quotes

Each entry: URL, verbatim quote, date checked. All dated 2026-11-21 unless marked "from memory, not checked".

### C99 6.5.5 (n1256)
https://port70.net/~nsz/c/c99/n1256.html#6.5.5 , checked 2026-11-21
> 6 When integers are divided, the result of the / operator is the algebraic quotient with any fractional part discarded.⁹⁰⁾ If the quotient a/b is representable, the expression (a/b)*b + a%b shall equal a.
> 90) This is often called ''truncation toward zero''.

### C11 6.5.5 (n1570)
https://port70.net/~nsz/c/c11/n1570.html#6.5.5 , checked 2026-11-21
> 5 The result of the / operator is the quotient from the division of the first operand by the second; the result of the % operator is the remainder. In both operations, if the value of the second operand is zero, the behavior is undefined.
> 6 When integers are divided, the result of the / operator is the algebraic quotient with any fractional part discarded.¹⁰⁵⁾ If the quotient a/b is representable, the expression (a/b)*b + a%b shall equal a; otherwise, the behavior of both a/b and a%b is undefined.
> 105) This is often called ''truncation toward zero''.

### C++ [expr.mul]
https://eel.is/c++draft/expr.mul , checked 2026-11-21
> If the second operand of / or % is zero, the behavior is undefined ([ub:expr.mul.div.by.zero]). For integral operands, the / operator yields the algebraic quotient with any fractional part discarded;⁵⁷ if the quotient a/b is representable in the type of the result, (a/b)*b + a%b is equal to a; otherwise, the behavior of both a/b and a%b is undefined.
> 57) This is often called truncation towards zero.

### C11 7.12.10.1 fmod
https://port70.net/~nsz/c/c11/n1570.html#7.12.10.1 , checked 2026-11-21
> 3 The fmod functions return the value x - ny, for some integer n such that, if y is nonzero, the result has the same sign as x and magnitude less than the magnitude of y. If y is zero, whether a domain error occurs or the fmod functions return zero is implementation- defined.

Annex F.10.7.1 (same URL, #F.10.7.1):
> - fmod(x, y) returns a NaN and raises the ''invalid'' floating-point exception for x infinite or y zero (and neither is a NaN).
> - fmod(x, (+-)(inf)) returns x for x not infinite.
> 2 When subnormal results are supported, the returned value is exact and is independent of the current rounding direction mode.

### C11 7.12.10.2 remainder, and the IEC 60559 text it quotes (IEEE 754 remainder)
https://port70.net/~nsz/c/c11/n1570.html#7.12.10.2 , checked 2026-11-21
> 2 The remainder functions compute the remainder x REM y required by IEC 60559.²³⁹⁾
> 3 The remainder functions return x REM y. If y is zero, whether a domain error occurs or the functions return zero is implementation defined.
> 239) ''When y != 0, the remainder r = x REM y is defined regardless of the rounding mode by the mathematical relation r = x - ny, where n is the integer nearest the exact value of x/y; whenever | n - x/y | = 1/2, then n is even. If r = 0, its sign shall be that of x.'' This definition is applicable for all implementations.

F.10.7.2: "The remainder functions are fully specified as a basic arithmetic operation in IEC 60559." and "When subnormal results are supported, the returned value is exact and is independent of the current rounding direction mode."

### IEEE 754-2019 5.3.1 remainder
Standard text is not publicly available; the C11 footnote 239 above quotes the IEC 60559 (IEEE 754-1985) wording. The 2019 wording, from memory, not checked: "When y ≠ 0, the remainder r = remainder(x, y) is defined for finite x and y regardless of the rounding-direction attribute by the mathematical relation r = x − y × n, where n is the integer nearest the exact number x/y; whenever |n − x/y| = 1/2, then n is even. Thus, the remainder is always exact. If r = 0, its sign shall be that of x. remainder(x, ∞) is x for finite x."

### C11 7.12.10.3 remquo
https://port70.net/~nsz/c/c11/n1570.html#7.12.10.3 , checked 2026-11-21
> 2 The remquo functions compute the same remainder as the remainder functions. In the object pointed to by quo they store a value whose sign is the sign of x/y and whose magnitude is congruent modulo 2^(n) to the magnitude of the integral quotient of x/y, where n is an implementation-defined integer greater than or equal to 3.

### Java JLS 15.17.2 and 15.17.3
https://docs.oracle.com/javase/specs/jls/se21/html/jls-15.html#jls-15.17.3 , checked 2026-11-21
> Integer division rounds toward 0. [...] if the value of the divisor in an integer division is 0, then an ArithmeticException is thrown.
> It follows from this rule that the result of the remainder operation can be negative only if the dividend is negative, and can be positive only if the dividend is positive. Moreover, the magnitude of the result is always less than the magnitude of the divisor.
> The result of a floating-point remainder operation as computed by the % operator is not the same as that computed by the remainder operation in IEEE 754, due to the choice of rounding policy in the Java programming language (§15.4). [...] this may be compared with the C library function fmod.
> - If the dividend is an infinity, or the divisor is a zero, or both, the result is NaN.
> Evaluation of a floating-point remainder operator % never throws a run-time exception, even if the right-hand operand is zero. Overflow, underflow, or loss of precision cannot occur.

### Java Math.floorMod, Math.IEEEremainder
https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/lang/Math.html , checked 2026-11-21
> The floor modulus is r = x - (floorDiv(x, y) * y), has the same sign as the divisor y or is zero, and is in the range of -abs(y) < r < +abs(y).
> [IEEEremainder] Computes the remainder operation on two arguments as prescribed by the IEEE 754 standard. The remainder value is mathematically equal to f1 - f2 × n, where n is the mathematical integer closest to the exact mathematical value of the quotient f1/f2, and if two mathematical integers are equally close to f1/f2, then n is the integer that is even.

### C# 12.13.4 Remainder operator
https://learn.microsoft.com/en-us/dotnet/csharp/language-reference/language-specification/expressions , checked 2026-11-21
> The result of x % y is the value produced by x – (x / y) * y. If y is zero, a System.DivideByZeroException is thrown.
> z is the result of x % y and is computed as x – n * y, where n is the largest possible integer that is less than or equal to x / y. This method of computing the remainder is analogous to that used for integer operands, but differs from the IEC 60559 definition (in which n is the integer closest to x / y).

https://learn.microsoft.com/en-us/dotnet/csharp/language-reference/operators/arithmetic-operators :
> For the operands of integer types, the result of the / operator is of an integer type and equals the quotient of the two operands rounded toward zero
> The sign of the non-zero remainder matches the sign of the left-hand operand

### C# Math.IEEERemainder
https://learn.microsoft.com/en-us/dotnet/api/system.math.ieeeremainder , checked 2026-11-21
> A number equal to x - (y Q), where Q is the quotient of x / y rounded to the nearest integer (if x / y falls halfway between two integers, the even integer is returned).
> If x - (y Q) is zero, the value +0 is returned if x is positive, or -0 if x is negative.

### ECMA-262 BigInt::remainder and Number::remainder
https://tc39.es/ecma262/#sec-numeric-types-bigint-remainder , checked 2026-11-21
> 1. If denominator = 0ℤ, throw a RangeError exception. [...] 4. Let truncatedQuotient be ℤ(truncate(quotient)). 5. Return numerator - (denominator × truncatedQuotient).
> Note: The sign of the result is the sign of the dividend.

https://tc39.es/ecma262/#sec-numeric-types-number-remainder
> 4. If denominator is either +0𝔽 or -0𝔽, return NaN.
> Note 2: The result of a floating-point remainder operation as computed by the % operator is not the same as the “remainder” operation defined by IEEE 754-2019. The IEEE 754-2019 “remainder” operation computes the remainder from a rounding division, not a truncating division, and so its behaviour is not analogous to that of the usual integer remainder operator. Instead the ECMAScript language defines % on floating-point operations to behave in a manner analogous to that of the Java integer remainder operator; this may be compared with the C library function fmod.

### Go spec, Arithmetic operators
https://go.dev/ref/spec#Arithmetic_operators , checked 2026-11-21
> For two integer values x and y, the integer quotient q = x / y and remainder r = x % y satisfy the following relationships: x = q*y + r and |r| < |y| with x / y truncated towards zero ("truncated division").
> If the divisor is a constant, it must not be zero. If the divisor is zero at run time, a run-time panic occurs.

### Go math.Mod, math.Remainder
https://pkg.go.dev/math#Mod , checked 2026-11-21
> Mod returns the floating-point remainder of x/y. The magnitude of the result is less than y and its sign agrees with that of x. Special cases are: [...] Mod(x, 0) = NaN
> Remainder returns the IEEE 754 floating-point remainder of x/y. [...] Remainder(x, 0) = NaN

### Rust reference, arithmetic operators
https://doc.rust-lang.org/reference/expressions/operator-expr.html , checked 2026-11-21
> * Integer division rounds towards zero.
> ** Rust uses a remainder defined with truncating division. Given remainder = dividend % divisor, the remainder will have the same sign as the dividend.
> † For integer types, division by zero panics.

### Rust i64::rem_euclid, div_euclid
https://doc.rust-lang.org/std/primitive.i64.html#method.rem_euclid , checked 2026-11-21
> Calculates the least nonnegative remainder of self when divided by rhs. This is done as if by the Euclidean division algorithm – given r = self.rem_euclid(rhs), the result satisfies self = rhs * self.div_euclid(rhs) + r and 0 <= r < abs(rhs).
> This function will panic if rhs is zero or if self is Self::MIN and rhs is -1.
> [div_euclid] If rhs > 0, this is equal to rounding towards -infinity; if rhs < 0, this is equal to rounding towards +infinity.

### Rust f64::rem_euclid
https://doc.rust-lang.org/std/primitive.f64.html#method.rem_euclid , checked 2026-11-21
> Calculates the least nonnegative remainder of self when divided by rhs.
> In particular, the return value r satisfies 0.0 <= r < rhs.abs() in most cases. However, due to a floating point round-off error it can result in r == rhs.abs(), violating the mathematical definition, if self is much smaller than rhs.abs() in magnitude and self < 0.0. This result is not an element of the function’s codomain, but it is the closest floating point number in the real numbers and thus fulfills the property self == self.div_euclid(rhs) * rhs + self.rem_euclid(rhs) approximately.
> §Precision: The result of this operation is guaranteed to be the rounded infinite-precision result.
> `// limitation due to round-off error` / `assert!((-f64::EPSILON).rem_euclid(3.0) != 0.0);`

### Rust f64 `%` (impl Rem for f64)
https://doc.rust-lang.org/std/primitive.f64.html , checked 2026-11-21
> The remainder from the division of two floats. The remainder has the same sign as the dividend and is computed as: x - (x / y).trunc() * y.

### Swift BinaryInteger `%` (stdlib source doc comment)
https://raw.githubusercontent.com/swiftlang/swift/main/stdlib/public/core/Integers.swift , checked 2026-11-21
> The result of the remainder operator (`%`) has the same sign as `lhs` and has a magnitude less than `rhs.magnitude`.
> - rhs: The value to divide `lhs` by. `rhs` must not be zero.

### Swift book, Remainder Operator
https://raw.githubusercontent.com/swiftlang/swift-book/main/TSPL.docc/LanguageGuide/BasicOperators.md , checked 2026-11-21
> The sign of `b` is ignored for negative values of `b`. This means that `a % b` and `a % -b` always give the same answer.

### Swift Double.truncatingRemainder / remainder
https://developer.apple.com/documentation/swift/double/truncatingremainder(dividingby:) (JSON at https://developer.apple.com/tutorials/data/documentation/swift/double/truncatingremainder(dividingby:).json), checked 2026-11-21
> If this value and other are both finite numbers, the truncating remainder has the same sign as this value and is strictly smaller in magnitude than other. The truncatingRemainder(dividingBy:) method is always exact.

https://developer.apple.com/documentation/swift/double/remainder(dividingby:)
> For two finite values x and y, the remainder r of dividing x by y satisfies x == y * q + r, where q is the integer nearest to x / y. If x / y is exactly halfway between two integers, q is chosen to be even. [...] If this value and other are finite numbers, the remainder is in the closed range -abs(other / 2)...abs(other / 2). The remainder(dividingBy:) method is always exact. This method implements the remainder operation defined by the IEEE 754 specification.

### Kotlin rem and mod
https://kotlinlang.org/api/core/kotlin-stdlib/kotlin/-int/rem.html , checked 2026-11-21
> Calculates the remainder of truncating division of this value (dividend) by the other value (divisor). The result is either zero or has the same sign as the dividend and has the absolute value less than the absolute value of the divisor.

https://kotlinlang.org/api/core/kotlin-stdlib/kotlin/mod.html , checked 2026-11-21
> Calculates the remainder of flooring division of this value (dividend) by the other value (divisor). The result is either zero or has the same sign as the divisor and has the absolute value less than the absolute value of the divisor.
> [Double/Float overloads add:] If the result cannot be represented exactly, it is rounded to the nearest representable number. In this case the absolute value of the result can be less than or equal to the absolute value of the divisor.

### Scala
https://scala-lang.org/files/archive/spec/2.13/12-the-scala-standard-library.html , checked 2026-11-21
> Arithmetic methods addition (+), subtraction (-), multiplication (*), division (/), and remainder (%), which each exist in 7 overloaded alternatives. [...] The operation is evaluated by converting the receiver and its argument to their operation type and performing the given arithmetic operation of that type.
https://www.scala-lang.org/api/current/scala/Int.html : "Returns the remainder of the division of this value by x." (no sign rule stated; JVM semantics, from memory, not checked).

### Python `%` and footnote
https://docs.python.org/3/reference/expressions.html#binary-arithmetic-operations , checked 2026-11-21
> The % (modulo) operator yields the remainder from the division of the first argument by the second. The numeric arguments are first converted to a common type. A zero right argument raises the ZeroDivisionError exception. [...] The modulo operator always yields a result with the same sign as its second operand (or zero); the absolute value of the result is strictly smaller than the absolute value of the second operand [1].
> [1] While abs(x%y) < abs(y) is true mathematically, for floats it may not be true numerically due to roundoff. For example, and assuming a platform on which a Python float is an IEEE 754 double-precision number, in order that -1e-100 % 1e100 have the same sign as 1e100, the computed result is -1e-100 + 1e100, which is numerically exactly equal to 1e100. The function math.fmod() returns a result whose sign matches the sign of the first argument instead, and so returns -1e-100 in this case. Which approach is more appropriate depends on the application.

### Python math.fmod, math.remainder
https://docs.python.org/3/library/math.html , checked 2026-11-21
> [fmod] The intent of the C standard is that fmod(x, y) be exactly (mathematically; to infinite precision) equal to x - n*y for some integer n such that the result has the same sign as x and magnitude less than abs(y). Python’s x % y returns a result with the sign of y instead, and may not be exactly computable for float arguments. [...] For this reason, function fmod() is generally preferred when working with floats, while Python’s x % y is preferred when working with integers.
> [remainder] The remainder r = remainder(x, y) thus always satisfies abs(r) <= 0.5 * abs(y). [...] remainder(x, 0) and remainder(math.inf, x) raise ValueError for any non-NaN x. [...] On platforms using IEEE 754 binary floating point, the result of this operation is always exactly representable: no rounding error is introduced.

### Ruby Integer#%, Float#%
https://docs.ruby-lang.org/en/master/Integer.html , checked 2026-11-21
> Returns self modulo other as a real numeric (Integer, Float, or Rational). For integer n and real number r, these expressions are equivalent: n % r / n-r*(n/r).floor / n.divmod(r)[1]
> [remainder examples] -11.remainder(4) # => -3

https://docs.ruby-lang.org/en/master/Float.html
> Returns self modulo other as a Float. For float f and real number r, these expressions are equivalent: f % r / f-r*(f/r).floor / f.divmod(r)[1]

### Perl perlop, Multiplicative Operators
https://perldoc.perl.org/perlop#Multiplicative-Operators , checked 2026-11-21
> Given integer operands $m and $n: If $n is positive, then $m % $n is $m minus the largest multiple of $n less than or equal to $m. If $n is negative, then $m % $n is $m minus the smallest multiple of $n that is not less than $m (that is, the result will be less than or equal to zero). If the operands $m and $n are floating point values and the absolute value of $n (that is abs($n)) is less than (UV_MAX + 1), only the integer portion of $m and $n will be used in the operation [...] Note that when use integer is in scope, "%" gives you direct access to the modulo operator as implemented by your C compiler.

### PHP
https://www.php.net/manual/en/language.operators.arithmetic.php , checked 2026-11-21
> Operands of modulo are converted to int before processing. For floating-point modulo, see fmod(). The result of the modulo operator % has the same sign as the dividend — that is, the result of $a % $b will have the same sign as $a.
https://www.php.net/manual/en/function.intdiv.php
> If num2 is 0, a DivisionByZeroError exception is thrown. If the num1 is PHP_INT_MIN and the num2 is -1, then an ArithmeticError exception is thrown.
https://www.php.net/manual/en/function.fmod.php
> The remainder (r) is defined as: num1 = i * num2 + r, for some integer i. If num2 is non-zero, r has the same sign as num1 and a magnitude less than the magnitude of num2. [...] NAN (float) if the second argument is 0.

### Lua 5.4 manual 3.4.1
https://www.lua.org/manual/5.4/manual.html#3.4.1 , checked 2026-11-21
> Floor division (//) is a division that rounds the quotient towards minus infinity, resulting in the floor of the division of its operands.
> Modulo is defined as the remainder of a division that rounds the quotient towards minus infinity (floor division).
> [math.fmod] Returns the remainder of the division of x by y that rounds the quotient towards zero. (integer/float)

Lua source (float `%`), https://raw.githubusercontent.com/lua/lua/v5.4/llimits.h , checked 2026-11-21:
> `{ (void)L; (m) = l_mathop(fmod)(a,b); if (((m) > 0) ? (b) < 0 : ((m) < 0 && (b) > 0)) (m) += (b); }`
Integer `%` by zero, https://raw.githubusercontent.com/lua/lua/v5.4/lvm.c : `luaG_runerror(L, "attempt to perform 'n%%0'");`

### R Arithmetic
https://stat.ethz.ch/R-manual/R-devel/library/base/html/Arithmetic.html , checked 2026-11-21
> %% indicates x mod y (“x modulo y”), i.e., computes the ‘remainder’ r <- x %% y, and %/% indicates integer division, where R uses “floored” integer division, i.e., q <- x %/% y := floor(x/y), [...] and hence sign(r) == sign(y). It is guaranteed that (up to rounding error) x == (x %% y) + y * (x %/% y) unless y == 0 where the result of %% is NA_integer_ or NaN (depending on the typeof of the arguments)
> For double arguments, %% can be subject to catastrophic loss of accuracy if x is much larger than y, and a warning is given if this is detected.
> %% and x %/% y can be used for non-integer y, e.g. 1 %/% 0.2, but the results are subject to representation error and so may be platform-dependent.

### Haskell 2010 report 6.4.2
https://www.haskell.org/onlinereport/haskell2010/haskellch6.html , checked 2026-11-21
> The quot, rem, div, and mod class methods satisfy these laws if y is non-zero: (x ‘quot‘ y)⋆y + (x ‘rem‘ y) == x; (x ‘div‘ y)⋆y + (x ‘mod‘ y) == x. ‘quot‘ is integer division truncated toward zero, while the result of ‘div‘ is truncated toward negative infinity.

### Haskell Data.Fixed mod'
https://hackage.haskell.org/package/base/docs/Data-Fixed.html , checked 2026-11-21
> mod' :: Real a => a -> a -> a — Generalisation of mod to any instance of Real
Source (https://hackage.haskell.org/package/base/docs/src/Data.Fixed.html): `mod' n d = n - (fromInteger f) * d where f = div' n d`, `div' n d = floor (toRational n / toRational d)`.

### OCaml Stdlib
https://ocaml.org/manual/5.2/api/Stdlib.html , checked 2026-11-21
> Integer division. Integer division rounds the real quotient of its arguments towards zero. [...] Raises Division_by_zero if the second argument is 0.
> Integer remainder. If y is not zero, the result of x mod y satisfies the following properties: x = (x / y) * y + x mod y and abs(x mod y) <= abs(y) - 1. If y = 0, x mod y raises Division_by_zero. Note that x mod y is negative only if x < 0.
> mod_float a b returns the remainder of a with respect to b. The returned value is a -. n *. b, where n is the quotient a /. b rounded towards zero to an integer.

### Erlang
https://www.erlang.org/doc/system/expressions.html , checked 2026-11-21
> div — Integer division — Integer; rem — Integer remainder of X/Y — Integer
(No sign rule or zero behavior stated on the page; truncation, sign of dividend, and `badarith` are from memory, not checked.)

### Elixir
https://hexdocs.pm/elixir/Kernel.html#rem/2 , checked 2026-11-21
> rem/2 uses truncated division, which means that the result will always have the sign of the dividend. Raises an ArithmeticError exception if one of the arguments is not an integer, or when the divisor is 0.
https://hexdocs.pm/elixir/Integer.html#mod/2
> This function performs a floored division, which means that the result will always have the sign of the divisor. Raises an ArithmeticError exception if one of the arguments is not an integer, or when the divisor is 0.

### Common Lisp HyperSpec
https://www.lispworks.com/documentation/HyperSpec/Body/f_mod_r.htm , checked 2026-11-21
> mod performs the operation floor on number and divisor and returns the remainder of the floor operation. rem performs the operation truncate on number and divisor and returns the remainder of the truncate operation. [...] Exceptional Situations: None. [...] Notes: The result of mod is either zero or a real with the same sign as divisor.
https://www.lispworks.com/documentation/HyperSpec/Body/f_floorc.htm
> floor and ffloor produce a quotient that has been truncated toward negative infinity [...] round and fround produce a quotient that has been rounded to the nearest mathematical integer; if the mathematical quotient is exactly halfway between two integers, [...] then the quotient has been rounded to the even (divisible by two) integer.

### Scheme R6RS 11.7.3.1 and 11.7.4.3
https://www.r6rs.org/final/html/r6rs/r6rs-Z-H-14.html , checked 2026-11-21
> div, mod, div₀, and mod₀ each accept two real numbers x₁ and x₂ as operands, where x₂ must be nonzero. div returns an integer, and mod returns a real.
> div₀ and mod₀ are like div and mod, except the result of mod₀ lies within a half-open interval centered on zero.
> In each case, x₁ must be neither infinite nor a NaN, and x₂ must be nonzero; otherwise, an exception with condition type &assertion is raised.
(The defining formulas are images on the page. From memory, not checked: x₁ = n_d·x₂ + x_m with 0 ≤ x_m < |x₂| for div/mod, and −|x₂/2| ≤ x_m < |x₂/2| for div0/mod0. The page's examples confirm (mod −123 −10) = 7.)

### Scheme R7RS 6.2.6
https://small.r7rs.org/attachment/r7rs.pdf , checked 2026-11-21
> These procedures implement number-theoretic (integer) division. It is an error if n2 is zero. [...] floor nq = ⌊n1/n2⌋; truncate nq = truncate(n1/n2)
> (floor/ 5 -2) =⇒ -3 -1 ; (truncate/ -5 2) =⇒ -2 -1

### Ada RM 4.5.5
https://www.adaic.org/resources/add_content/standards/22rm/html/RM-4-5-5.html , checked 2026-11-21 (ada-auth.org timed out)
> Signed integer division and remainder are defined by the relation: A = (A/B)*B + (A rem B) where (A rem B) has the sign of A and an absolute value less than the absolute value of B. Signed integer division satisfies the identity: (-A)/B = -(A/B) = A/(-B)
> The signed integer modulus operator is defined such that the result of A mod B is either zero, or has the sign of B and an absolute value less than the absolute value of B; in addition, for some signed integer value N, this result satisfies the relation: A = B*N + (A mod B)
> The exception Constraint_Error is raised by integer division, rem, and mod if the right operand is zero.

### Fortran (gfortran)
https://gcc.gnu.org/onlinedocs/gfortran/MOD.html , checked 2026-11-21
> P Shall be a scalar of the same type and kind as A and not equal to zero. [...] The return value is the result of A - (INT(A/P) * P). [...] The returned value has the same sign as A and a magnitude less than the magnitude of P.
https://gcc.gnu.org/onlinedocs/gfortran/MODULO.html
> If A and P are of type INTEGER or UNSIGNED: MODULO(A,P) has the value R such that A=Q*P+R, where Q is an integer and R is between 0 (inclusive) and P (exclusive). If A and P are of type REAL: MODULO(A,P) has the value of A - FLOOR (A / P) * P. The returned value has the same sign as P and a magnitude less than the magnitude of P.

### Dart num `%`, remainder, `~/`
https://api.dart.dev/stable/dart-core/num/operator_modulo.html , checked 2026-11-21 (the `int/operator_modulo.html` page is 404; `int` inherits `%` from `num`, per https://api.dart.dev/dart-core/int-class.html)
> Euclidean modulo of this number by other. Returns the remainder of the Euclidean division. The Euclidean division of two integers a and b yields two integers q and r such that a == b * q + r and 0 <= r < b.abs(). The Euclidean division is only defined for integers, but can be easily extended to work with doubles. In that case, q is still an integer, but r may have a non-integer value that still satisfies 0 <= r < |b|. The sign of the returned value r is always positive.
> print(5 % -3); // 2 / print(-5 % -3); // 1
(The phrase "the result is always non-negative" given in the brief does not appear on today's page; the page says "always positive".)
https://api.dart.dev/stable/dart-core/num/remainder.html
> The result r of this operation satisfies: this == (this ~/ other) * other + r. As a consequence, the remainder r has the same sign as the dividend this.
https://api.dart.dev/stable/dart-core/num/operator_truncate_divide.html
> Truncating division is division where a fractional result is converted to an integer by rounding towards zero. If both operands are ints, then other must not be zero.

### Julia
https://docs.julialang.org/en/v1/base/math/ , checked 2026-11-21
> [mod] The reduction of x modulo y, or equivalently, the remainder of x after floored division by y, i.e. x - y*fld(x,y) if computed without intermediate rounding. The result will have the same sign as y if isfinite(y), and magnitude less than abs(y) (with some exceptions, see note below). Note: When used with floating point values, the exact result may not be representable by the type, and so rounding error may occur. In particular, if the exact result is very close to y, then it may be rounded to y.
> julia> mod(-eps(), 3) / 3.0
> [rem] Remainder from Euclidean division, returning a value of the same sign as x, and smaller in magnitude than y. This value is always exact.
> [rem(x,y,r)] if r == RoundDown, then the result is in the interval [0, y) if y is positive, or (y, 0] otherwise. The result may not be exact if x and y have different signs, and abs(x) < abs(y).
> [mod2pi] Modulus after division by 2π, returning in the range [0,2π). This function computes a floating point representation of the modulus after division by numerically exact 2π, and is therefore not exactly the same as mod(x,2π)

### Zig language reference
https://ziglang.org/documentation/master/#mod , checked 2026-11-21
> @mod(numerator: T, denominator: T) T — Modulus division. For unsigned integers this is the same as numerator % denominator. Caller guarantees denominator != 0, otherwise the operation will result in a Remainder Division by Zero when runtime safety checks are enabled. - @mod(-5, 3) == 1 - (@divFloor(a, b) * b) + @mod(a, b) == a
> @rem [...] Caller guarantees denominator != 0 [...] - @rem(-5, 3) == -2
> @divFloor — Floored division. Rounds toward negative infinity. [...] Caller guarantees denominator != 0 and !(@typeInfo(T) == .int and T.is_signed and numerator == std.math.minInt(T) and denominator == -1).
> [a % b] Signed or floating-point operands must be comptime-known and positive. In other cases, use @rem or @mod instead.
Older versions, https://ziglang.org/documentation/0.14.0/ (same text in 0.11.0 and 0.13.0), checked 2026-11-21:
> Caller guarantees denominator > 0, otherwise the operation will result in a Remainder Division by Zero when runtime safety checks are enabled.
0.15.1 and master say "denominator != 0".
std.math.mod, https://raw.githubusercontent.com/ziglang/zig/master/lib/std/math.zig :
> /// Returns numerator modulo denominator, or an error if denominator is zero or negative. Negative numerators never result in negative return values.

### Smalltalk (Pharo 13 source comments)
https://raw.githubusercontent.com/pharo-project/pharo/Pharo13/src/Kernel/Number.class.st , checked 2026-11-21
> [//] Integer quotient defined by division with truncation toward negative infinity. \\ answers the remainder from this division.
> [\\] modulo. Remainder defined in terms of //. Answer a Number with the same sign as aNumber. "9 \\ -4 >>> -3"
> [quo:] Integer quotient defined by division with truncation toward zero.
> [rem:] Remainder defined in terms of quo:. Answer a Number with the same sign as self.
(ANSI Smalltalk not fetched.)

### Mathematica Mod
https://reference.wolfram.com/language/ref/Mod.html , checked 2026-11-21
> Mod[m,n] gives the remainder of m divided by n. Mod[m,n] is equivalent to m-n Quotient[m,n]. For positive integers m and n, Mod[m,n] is an integer between 0 and n-1.
> The results have the same sign as the modulus
`Mod[m,0]` gives `Indeterminate`: from memory, not checked.

### Excel MOD
https://support.microsoft.com/en-us/office/mod-function-9b6cd169-b6ee-406a-a97b-edf2a9dc24f3 , checked 2026-11-21
> Returns the remainder after number is divided by divisor. The result has the same sign as divisor. [...] If divisor is 0, MOD returns the #DIV/0! error value. The MOD function can be expressed in terms of the INT function: MOD(n, d) = n - d*INT(n/d)

### SQL standard MOD
From memory, not checked (ISO/IEC 9075-2 is not public): MOD(N, M) returns R with the sign of N and abs(R) < abs(M) such that N = M*K + R for an integer K; M = 0 raises "data exception — division by zero".

### PostgreSQL
https://www.postgresql.org/docs/current/functions-math.html , checked 2026-11-21
> Division (for integral types, division truncates the result towards zero)
> numeric_type % numeric_type → numeric_type — Modulo (remainder); available for smallint, integer, bigint, and numeric
> div ( y numeric, x numeric ) → numeric — Integer quotient of y/x (truncates towards zero)
(Sign of `%` and the "division by zero" error: from memory, not checked; no server available locally.)

### MySQL 8.4
https://dev.mysql.com/doc/refman/8.4/en/mathematical-functions.html (via WebFetch; curl got HTTP 403), checked 2026-11-21
> MOD(N,M), N % M, N MOD M — Modulo operation. Returns the remainder of N divided by M. Returns NULL if M or N is NULL. [...] MOD() also works on values that have a fractional part and returns the exact remainder after division: mysql> SELECT MOD(34.5,3); -> 1.5. MOD(N,0) returns NULL.

### SQLite
https://www.sqlite.org/lang_expr.html , checked 2026-11-21
> The % operator casts both of its operands to type INTEGER and then computes the remainder after dividing the left integer by the right integer. [...] Integer divide yields an integer result, truncated toward zero.
https://www.sqlite.org/lang_mathfunc.html
> mod(X,Y) Return the remainder after dividing X by Y. This is similar to the '%' operator, except that it works for non-integer arguments.

### NumPy
https://numpy.org/doc/stable/reference/generated/numpy.remainder.html , checked 2026-11-21
> Computes the remainder complementary to the floor_divide function. It is equivalent to the Python modulus operator x1 % x2 and has the same sign as the divisor x2. The MATLAB function equivalent to np.remainder is mod. [...] Returns 0 when x2 is 0 and both x1 and x2 are (arrays of) integers. mod is an alias of remainder.
https://numpy.org/doc/stable/reference/generated/numpy.fmod.html
> This is the NumPy implementation of the C library function fmod, the remainder has the same sign as the dividend x1. It is equivalent to the Matlab(TM) rem function and should not be confused with the Python modulus operator x1 % x2.

### MATLAB mod and rem
https://www.mathworks.com/help/matlab/ref/double.mod.html (via WebFetch; curl got HTTP 403), checked 2026-11-21
> This function is often called the modulo operation, which can be expressed as b = a - m.*floor(a./m).
> The mod function produces a result that is either zero or has the same sign as the divisor.
> The mod function follows the convention that mod(a,0) returns a.
> Note that mod attempts to compensate for floating-point round-off effects to produce exact integer results when possible.
The current page contains no tolerance rule (checked for "roundoff", "tolerance", "eps", "within"). The rule "if a./m is within round-off error of an integer, then that integer is used as the quotient" is from older MATLAB documentation: from memory, not checked.
https://www.mathworks.com/help/matlab/ref/double.rem.html
> r = a - b.*fix(a./b). The rem function produces a result that is either zero or has the same sign as the dividend. The rem function follows the convention that rem(a,0) is NaN. When possible, rem attempts to produce exact integer results by compensating for floating-point round-off effects.

## Local runs (2026-11-21)

- Python: `-7%3, 7%-3, -7//3` = `2 -2 -3`; `-1e-100 % 1e100` = `1e+100` (equals 1e100: True); `math.fmod(-1e-100,1e100)` = `-1e-100`; `1%0`, `1.0%0.0` raise `ZeroDivisionError division by zero`; `math.fmod(1,0)`, `math.remainder(1,0)` raise `ValueError math domain error`.
- Node: `-7%3, 7%-3` = `-1 1`; `-7n%3n, 7n%-3n` = `-1n 1n`; `5%0` = `NaN`; `1n%0n` throws `RangeError: Division by zero`.
- Ruby 4.0.9: `[-7%3, 7%-3, -7.remainder(3), -7/3, (-1e-100)%1e100, (-7.0).remainder(3)]` = `[2, -2, -1, -3, 1.0e+100, -1.0]`; `1.0%0.0`, `1%0`, `1.0.divmod(0.0)`, `1.0.modulo(0)` all raise `ZeroDivisionError: divided by 0`.
- Perl: `-7%3, 7%-3, -7.5%3, 7.5%-3` = `2 -2 2 -2`; `1 % 0` dies `Illegal modulus zero`; under `use integer`, `-7%3` = `-1`.
- SQLite 3.51.2: `-7%3, 7%-3, 7%0, 7.5%2, mod(-7.5,2), mod(7,0), -7/3` = `-1|1||1.0|-1.5||-2`.
- C (gcc, glibc): `-7%3, 7%-3` = `-1 1`; `fmod(-7.5,2)=-1.5`, `fmod(7.5,-2)=1.5`, `remainder(5,2)=1`, `remainder(7,2)=-1`, `fmod(1,0)=-nan`; `fmod(-1e-100,1e100)` = `-0x1.bff2ee48e053p-333` (that is, -1e-100 unchanged).
- Go 1.26: `-7%3, 7%-3, -7/3` = `-1 1 -2`; `math.Mod(-7.5,2)=-1.5`, `math.Mod(1,0)=NaN`, `Remainder(5,2)=1`, `Remainder(7,2)=-1`; `1%z` panics `runtime error: integer divide by zero`.
- Rust: `-7%3, 7%-3, (-7).rem_euclid(3), 7.rem_euclid(-3), (-7).div_euclid(-3)` = `-1 1 2 1 3`; `(-f64::EPSILON).rem_euclid(3.0)` = `3`; `(-1e-100).rem_euclid(1e100) == 1e100` true; `-7.5 % 2.0` = `-1.5`; `1.0 % 0.0` = `NaN`; `1 % 0` panics "attempt to calculate the remainder with a divisor of zero". `1e17 % 3.0` = `1` while `x - (x/y).trunc()*y` evaluated in f64 = `0`.
- Java 26: `-7%3, 7%-3, floorMod(-7,3), floorMod(7,-3), -7.5%2, 1.0%0.0, IEEEremainder(5,2), IEEEremainder(7,2)` = `-1 1 2 -2 -1.5 NaN 1.0 -1.0`; `1%0` and `floorMod(1,0)` throw `java.lang.ArithmeticException: / by zero`.
- Dart 3.13.7: `-7%3, 7%-3, (-7).remainder(3), -7~/3` = `2 1 -1 -2`; `(-1e-100)%1e100` = `1e+100` (== 1e100 true); `1.0%0.0` = `NaN`; `(-7.5)%-2` = `0.5`; `1%0` throws `IntegerDivisionByZeroException`.
- GHC 9.10.3: `(-7) mod 3, 7 mod (-3), (-7) rem 3, (-7) div 3, (-7) quot 3` = `(2,-2,-1,-3,-2)`; `mod' (-1e-100) 1e100` = `1.0e100` (== 1e100 True); `mod' 7.5 (-2)` = `-0.5`; `1 mod 0` throws `divide by zero`.

## Exhaustive and sampled check counts (fmcheck)

Lines `C` are counts, `M` maxima in units of u, `E` the first examples (bit patterns of x, m and the result).
Counter names: `out_of_range` a result outside `[0, m)`; `equals_m` a result equal to `m`; `neg_zero` a result `-0.0`;
`err_gt_half_u`, `err_ge_u` the error against the exact residue; `circ_*` the same error measured around the circle of
length `m`; `mono_violation` a result smaller than that at the next smaller `x` in one period; `not_exact` a result
other than `ρ` where `ρ` is a float; `infinite`, `nan` such results.

### f16

```
C a.circ_gt_half_u 574186672
C a.equals_m 180333542
C a.err_eq_half_u 15218176
C a.err_ge_u 620852853
C a.err_gt_half_u 620852853
C a.infinite 239207857
C a.mono_violation 20909291
C a.not_exact 600939125
C a.out_of_range 466207580
C add_inexact 440911360
C b.equals_m 200242688
C b.err_eq_half_u 15218176
C b.neg_zero 2340669
C b.out_of_range 200242688
C c.err_eq_half_u 15203329
C c.err_ge_u 200242688
C c.err_gt_half_u 200242688
C c.mono_violation 29183
C d.circ_gt_half_u 295477248
C d.err_eq_half_u 15218176
C d.err_gt_half_u 295477248
C e.circ_gt_half_u 200227841
C e.err_eq_half_u 15218176
C e.err_gt_half_u 200227841
C g.circ_gt_half_u 90171466
C g.err_eq_half_u 45086210
C g.err_ge_u 283544906
C g.err_gt_half_u 290414154
C g.mono_violation 44030
C g.nan 2096128
C g.not_exact 538354507
C pairs 2015299584
C rho_not_representable 440911360
C sterbenz_violation 0
M a.max_circ_over_u 1.023e3
M a.max_err_over_u 3.4792e4
M b.max_circ_over_u 5e-1
M b.max_err_over_u 5e-1
M c.max_circ_over_u 5e-1
M c.max_err_over_u 2.0479999999962747e3
M d.max_circ_over_u 9.999999981373549e-1
M d.max_err_over_u 9.999999981373549e-1
M e.max_circ_over_u 9.999999981373549e-1
M e.max_err_over_u 9.999999981373549e-1
M g.max_circ_over_u 1e0
M g.max_err_over_u 2.0479999999962747e3
E a.err_ge_u x=0xe710 m=0x2711 r=0x0
E a.err_ge_u x=0xe70f m=0x2711 r=0x0
E a.err_ge_u x=0xe70e m=0x2711 r=0x0
E a.mono_violation x=0xcffc m=0x2711 r=0x0 prev_x=0xcffd prev_r=0x2400
E a.mono_violation x=0xcff9 m=0x2711 r=0xa400 prev_x=0xcffa prev_r=0x0
E a.mono_violation x=0xcff5 m=0x2711 r=0x0 prev_x=0xcff6 prev_r=0x2400
E a.not_exact x=0xe710 m=0x2711 r=0x0
E a.not_exact x=0xe70f m=0x2711 r=0x0
E a.not_exact x=0xe70e m=0x2711 r=0x0
E a.out_of_range x=0xfbff m=0x2711 r=0x7c00
E a.out_of_range x=0xfbfe m=0x2711 r=0x7c00
E a.out_of_range x=0xfbfd m=0x2711 r=0x7c00
E b.out_of_range x=0x807f m=0x2711 r=0x2711
E b.out_of_range x=0x807e m=0x2711 r=0x2711
E b.out_of_range x=0x807d m=0x2711 r=0x2711
E c.err_ge_u x=0x807f m=0x2711 r=0x0
E c.err_ge_u x=0x807e m=0x2711 r=0x0
E c.err_ge_u x=0x807d m=0x2711 r=0x0
E c.mono_violation x=0x807f m=0x2711 r=0x0 prev_x=0x8080 prev_r=0x2710
E c.mono_violation x=0x8080 m=0x2712 r=0x0 prev_x=0x8081 prev_r=0x2711
E c.mono_violation x=0x807f m=0x2713 r=0x0 prev_x=0x8080 prev_r=0x2712
E g.err_ge_u x=0x807f m=0x2711 r=0x0
E g.err_ge_u x=0x807e m=0x2711 r=0x0
E g.err_ge_u x=0x807d m=0x2711 r=0x0
E g.mono_violation x=0x807f m=0x2711 r=0x0 prev_x=0x8080 prev_r=0x2710
E g.mono_violation x=0x8080 m=0x2712 r=0x0 prev_x=0x8081 prev_r=0x2711
E g.mono_violation x=0x2711 m=0x2712 r=0x0 prev_x=0x2710 prev_r=0x2710
E g.nan x=0x77ff m=0x7800 r=0x7e00
E g.nan x=0x77fd m=0x7801 r=0x7e00
E g.nan x=0x77fe m=0x7801 r=0x7e00
E g.not_exact x=0x1 m=0x2711 r=0x0
E g.not_exact x=0x2 m=0x2711 r=0x0
E g.not_exact x=0x3 m=0x2711 r=0x0
```

### bf16

```
C a.circ_gt_half_u 673047802
C a.equals_m 377788298
C a.err_eq_half_u 2088640
C a.err_ge_u 877771798
C a.err_gt_half_u 877771798
C a.infinite 264297147
C a.mono_violation 3261442
C a.not_exact 757824662
C a.out_of_range 846809441
C add_inexact 524345536
C b.equals_m 497730880
C b.err_eq_half_u 2088640
C b.neg_zero 14893292
C b.out_of_range 497730880
C c.err_eq_half_u 2072449
C c.err_ge_u 497730880
C c.err_gt_half_u 497730880
C c.mono_violation 32319
C d.circ_gt_half_u 507014176
C d.err_eq_half_u 2088640
C d.err_gt_half_u 507014176
C e.circ_gt_half_u 497714689
C e.err_eq_half_u 2088640
C e.err_gt_half_u 497714689
C g.circ_gt_half_u 82627885
C g.err_eq_half_u 6209218
C g.err_ge_u 579286989
C g.err_gt_half_u 580358765
C g.mono_violation 48510
C g.nan 32640
C g.not_exact 607941646
C pairs 2130673920
C rho_not_representable 524345536
C sterbenz_violation 0
M a.max_circ_over_u 1.27e2
M a.max_err_over_u 1.7014118346046923e38
M b.max_circ_over_u 5e-1
M b.max_err_over_u 5e-1
M c.max_circ_over_u 5e-1
M c.max_err_over_u 2.56e2
M d.max_circ_over_u 1e0
M d.max_err_over_u 1e0
M e.max_circ_over_u 1e0
M e.max_err_over_u 1e0
M g.max_circ_over_u 1e0
M g.max_err_over_u 2.56e2
E a.err_ge_u x=0xe710 m=0x2711 r=0x0
E a.err_ge_u x=0xe70f m=0x2711 r=0x0
E a.err_ge_u x=0xe70e m=0x2711 r=0x0
E a.mono_violation x=0xaa7e m=0x2711 r=0x0 prev_x=0xaa7f prev_r=0x2680
E a.mono_violation x=0xaa7c m=0x2711 r=0xa680 prev_x=0xaa7d prev_r=0x2680
E a.mono_violation x=0xaa77 m=0x2711 r=0x0 prev_x=0xaa78 prev_r=0x2680
E a.not_exact x=0xe710 m=0x2711 r=0x0
E a.not_exact x=0xe70f m=0x2711 r=0x0
E a.not_exact x=0xe70e m=0x2711 r=0x0
E a.out_of_range x=0xff7f m=0x2711 r=0x7f80
E a.out_of_range x=0xff7e m=0x2711 r=0x7f80
E a.out_of_range x=0xff7d m=0x2711 r=0x7f80
E b.out_of_range x=0xa2ff m=0x2711 r=0x2711
E b.out_of_range x=0xa2fe m=0x2711 r=0x2711
E b.out_of_range x=0xa2fd m=0x2711 r=0x2711
E c.err_ge_u x=0xa2ff m=0x2711 r=0x0
E c.err_ge_u x=0xa2fe m=0x2711 r=0x0
E c.err_ge_u x=0xa2fd m=0x2711 r=0x0
E c.mono_violation x=0xa2ff m=0x2711 r=0x0 prev_x=0xa300 prev_r=0x2710
E c.mono_violation x=0xa300 m=0x2712 r=0x0 prev_x=0xa301 prev_r=0x2711
E c.mono_violation x=0xa2ff m=0x2713 r=0x0 prev_x=0xa300 prev_r=0x2712
E g.err_ge_u x=0xa2ff m=0x2711 r=0x0
E g.err_ge_u x=0xa2fe m=0x2711 r=0x0
E g.err_ge_u x=0xa2fd m=0x2711 r=0x0
E g.mono_violation x=0xa2ff m=0x2711 r=0x0 prev_x=0xa300 prev_r=0x2710
E g.mono_violation x=0xa300 m=0x2712 r=0x0 prev_x=0xa301 prev_r=0x2711
E g.mono_violation x=0x2711 m=0x2712 r=0x0 prev_x=0x2710 prev_r=0x2710
E g.nan x=0x7eff m=0x7f00 r=0x7fc0
E g.nan x=0x7efd m=0x7f01 r=0x7fc0
E g.nan x=0x7efe m=0x7f01 r=0x7fc0
E g.not_exact x=0x1 m=0x2711 r=0x0
E g.not_exact x=0x2 m=0x2711 r=0x0
E g.not_exact x=0x3 m=0x2711 r=0x0
```

### f32

```
C a.circ_gt_half_u 51023157
C a.equals_m 38636725
C a.err_eq_half_u 1050623
C a.err_ge_u 58432036
C a.err_gt_half_u 58432036
C a.infinite 5007826
C a.not_exact 52696575
C a.out_of_range 51053430
C add_inexact 85066824
C b.equals_m 44371754
C b.err_eq_half_u 1050623
C b.neg_zero 1331980
C b.out_of_range 44371754
C c.err_eq_half_u 1028737
C c.err_ge_u 44371754
C c.err_gt_half_u 44371754
C d.circ_gt_half_u 62906051
C d.err_eq_half_u 1050623
C d.err_gt_half_u 62906051
C e.circ_gt_half_u 44349868
C e.err_eq_half_u 1050623
C e.err_gt_half_u 44349868
C g.circ_gt_half_u 4010430
C g.err_eq_half_u 1106336
C g.err_ge_u 48363166
C g.err_gt_half_u 48382184
C g.nan 637
C g.not_exact 13970961
C pairs 160000000
C rho_not_representable 85066824
C sterbenz_violation 0
M a.max_circ_over_u 8.386748e6
M a.max_err_over_u 1.7014118346046923e38
M b.max_circ_over_u 5e-1
M b.max_err_over_u 5e-1
M c.max_circ_over_u 5e-1
M c.max_err_over_u 1.6777216e7
M d.max_circ_over_u 1e0
M d.max_err_over_u 1e0
M e.max_circ_over_u 1e0
M e.max_err_over_u 1e0
M g.max_circ_over_u 1e0
M g.max_err_over_u 1.6777216e7
E a.err_ge_u x=0xc00573ae m=0x3b71dde4 r=0x0
E a.err_ge_u x=0x18fb47b2 m=0x4d4a3f5 r=0x0
E a.err_ge_u x=0xbe47cc44 m=0x3a50c4b9 r=0x32800000
E a.not_exact x=0xc00573ae m=0x3b71dde4 r=0x0
E a.not_exact x=0x18fb47b2 m=0x4d4a3f5 r=0x0
E a.not_exact x=0xbe47cc44 m=0x3a50c4b9 r=0x32800000
E a.out_of_range x=0x52d29cbe m=0x1db43ff r=0xff800000
E a.out_of_range x=0xc5f67daa m=0x643b59f7 r=0x643b59f7
E a.out_of_range x=0xbc55970b m=0x7510e2e3 r=0x7510e2e3
E b.out_of_range x=0xc5f67daa m=0x643b59f7 r=0x643b59f7
E b.out_of_range x=0xbc55970b m=0x7510e2e3 r=0x7510e2e3
E b.out_of_range x=0xdf8dfe4d m=0x6cfd70c9 r=0x6cfd70c9
E c.err_ge_u x=0xc5f67daa m=0x643b59f7 r=0x0
E c.err_ge_u x=0xbc55970b m=0x7510e2e3 r=0x0
E c.err_ge_u x=0xdf8dfe4d m=0x6cfd70c9 r=0x0
E g.err_ge_u x=0x52d29cbe m=0x1db43ff r=0xd592d4
E g.err_ge_u x=0x18fb47b2 m=0x4d4a3f5 r=0x4cb24ff
E g.err_ge_u x=0xc5f67daa m=0x643b59f7 r=0x0
E g.nan x=0x7ef75938 m=0x7f0f844b r=0x7fc00000
E g.nan x=0x7f293bc7 m=0x7f293bca r=0x7fc00000
E g.nan x=0x7dc8b6e1 m=0x7f674cb4 r=0x7fc00000
E g.not_exact x=0x52d29cbe m=0x1db43ff r=0xd592d4
E g.not_exact x=0x18fb47b2 m=0x4d4a3f5 r=0x4cb24ff
E g.not_exact x=0x309dbeaf m=0x5cad510e r=0x0
```

### f64

```
C a.circ_gt_half_u 5188918
C a.equals_m 4100819
C a.err_eq_half_u 34479
C a.err_ge_u 6225790
C a.err_gt_half_u 6225790
C a.infinite 501011
C a.not_exact 5383306
C a.out_of_range 5638702
C add_inexact 8795145
C b.equals_m 4943263
C b.err_eq_half_u 34479
C b.neg_zero 73060
C b.out_of_range 4943263
C c.err_eq_half_u 34344
C c.err_ge_u 4943263
C c.err_gt_half_u 4943263
C d.circ_gt_half_u 6800250
C d.err_eq_half_u 34479
C d.err_gt_half_u 6800250
C e.circ_gt_half_u 4943128
C e.err_eq_half_u 34479
C e.err_gt_half_u 4943128
C g.circ_gt_half_u 402776
C g.err_eq_half_u 35354
C g.err_ge_u 5345806
C g.err_gt_half_u 5346039
C g.nan 4
C g.not_exact 1402530
C pairs 16000000
C rho_not_representable 8795145
C sterbenz_violation 0
M a.max_circ_over_u 4.501821583966632e15
M a.max_err_over_u 8.98846567431158e307
M b.max_circ_over_u 5e-1
M b.max_err_over_u 5e-1
M c.max_circ_over_u 5e-1
M c.max_err_over_u 9.007198744198695e15
M d.max_circ_over_u 1e0
M d.max_err_over_u 1e0
M e.max_circ_over_u 1e0
M e.max_err_over_u 1e0
M g.max_circ_over_u 1e0
M g.max_err_over_u 9.007198744198695e15
E a.err_ge_u x=0xe370f06ec624b4a7 m=0x62d8d9c20d69ede3 r=0x0
E a.err_ge_u x=0x86bb387fa35734f6 m=0x7a28f7828bdbbb51 r=0x86bb387fa35734f6
E a.err_ge_u x=0xb8b566dd72c55f94 m=0x381c2b41bde388f9 r=0x381c2b41bde37c00
E a.not_exact x=0xe370f06ec624b4a7 m=0x62d8d9c20d69ede3 r=0x0
E a.not_exact x=0xb8b566dd72c55f94 m=0x381c2b41bde388f9 r=0x381c2b41bde37c00
E a.not_exact x=0x39bb14db49b80c9b m=0x39212918e5354247 r=0x3688000000000000
E a.out_of_range x=0x86bb387fa35734f6 m=0x7a28f7828bdbbb51 r=0x86bb387fa35734f6
E a.out_of_range x=0x85cb1e5aac897ac6 m=0x324870bed739d667 r=0x324870bed739d667
E a.out_of_range x=0x82357680186740b1 m=0x39c3246ff3b93b3b r=0x39c3246ff3b93b3b
E b.out_of_range x=0x86bb387fa35734f6 m=0x7a28f7828bdbbb51 r=0x7a28f7828bdbbb51
E b.out_of_range x=0x85cb1e5aac897ac6 m=0x324870bed739d667 r=0x324870bed739d667
E b.out_of_range x=0x82357680186740b1 m=0x39c3246ff3b93b3b r=0x39c3246ff3b93b3b
E c.err_ge_u x=0x86bb387fa35734f6 m=0x7a28f7828bdbbb51 r=0x0
E c.err_ge_u x=0x85cb1e5aac897ac6 m=0x324870bed739d667 r=0x0
E c.err_ge_u x=0x82357680186740b1 m=0x39c3246ff3b93b3b r=0x0
E g.err_ge_u x=0x86bb387fa35734f6 m=0x7a28f7828bdbbb51 r=0x0
E g.err_ge_u x=0x85cb1e5aac897ac6 m=0x324870bed739d667 r=0x0
E g.err_ge_u x=0x82357680186740b1 m=0x39c3246ff3b93b3b r=0x0
E g.nan x=0x7fefb1c35891d200 m=0x7fefb1c35891d202 r=0x7ff8000000000000
E g.nan x=0x7fefb1c35891d200 m=0x7fefb1c35891d202 r=0x7ff8000000000000
E g.nan x=0x7fd8405afc5c19aa m=0x7fe5e4bf87abf157 r=0x7ff8000000000000
E g.not_exact x=0x76a43a3d48f8b32e m=0x7b19eb08dbaaa828 r=0x0
E g.not_exact x=0x4b8a2f0e55671ddf m=0x4afd350c15a4a969 r=0x4afd350c15a4a827
E g.not_exact x=0x1630092079d88f65 m=0x73bb9c30a41cce67 r=0x0
```

## Special values (fmcheck special; columns a b c d e g)

```
format f16: candidates ["a", "b", "c", "d", "e", "g"]; '?' marks a value outside [0, m)
x=0.0          m=5.960464477539063e-8 0.0  0.0  0.0  0.0  0.0  0.0
x=-0.0         m=5.960464477539063e-8 0.0  -0.0  0.0  0.0  0.0  0.0
x=5.960464477539063e-8 m=5.960464477539063e-8 0.0  0.0  0.0  0.0  0.0  0.0
x=-5.960464477539063e-8 m=5.960464477539063e-8 0.0  -0.0  0.0  0.0  0.0  0.0
x=1.0          m=5.960464477539063e-8 -inf?  0.0  0.0  0.0  0.0  0.0
x=-1.0         m=5.960464477539063e-8 inf?  -0.0  0.0  0.0  0.0  0.0
x=65504.0      m=5.960464477539063e-8 -inf?  0.0  0.0  0.0  0.0  0.0
x=-65504.0     m=5.960464477539063e-8 inf?  -0.0  0.0  0.0  0.0  0.0
x=inf          m=5.960464477539063e-8 NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=5.960464477539063e-8 NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=5.960464477539063e-8 NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=1.0          0.0  0.0  0.0  0.0  0.0  0.0
x=-0.0         m=1.0          0.0  -0.0  0.0  0.0  0.0  0.0
x=5.960464477539063e-8 m=1.0          5.960464477539063e-8  5.960464477539063e-8  5.960464477539063e-8  5.960464477539063e-8  5.960464477539063e-8  0.0
x=-5.960464477539063e-8 m=1.0          1.0?  1.0?  0.0  0.99951171875  0.99951171875  0.0
x=1.0          m=1.0          0.0  0.0  0.0  0.0  0.0  0.0
x=-1.0         m=1.0          0.0  -0.0  0.0  0.0  0.0  0.0
x=65504.0      m=1.0          0.0  0.0  0.0  0.0  0.0  0.0
x=-65504.0     m=1.0          0.0  -0.0  0.0  0.0  0.0  0.0
x=inf          m=1.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=1.0          NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=1.0          NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=65504.0      0.0  0.0  0.0  0.0  0.0  0.0
x=-0.0         m=65504.0      0.0  -0.0  0.0  0.0  0.0  0.0
x=5.960464477539063e-8 m=65504.0      5.960464477539063e-8  5.960464477539063e-8  5.960464477539063e-8  5.960464477539063e-8  5.960464477539063e-8  0.0
x=-5.960464477539063e-8 m=65504.0      -5.960464477539063e-8?  65504.0?  0.0  65472.0  65472.0  0.0
x=1.0          m=65504.0      1.0  1.0  1.0  1.0  1.0  0.0
x=-1.0         m=65504.0      65504.0?  65504.0?  0.0  65472.0  65472.0  0.0
x=65504.0      m=65504.0      0.0  0.0  0.0  0.0  0.0  0.0
x=-65504.0     m=65504.0      0.0  -0.0  0.0  0.0  0.0  0.0
x=inf          m=65504.0      NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=65504.0      NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=65504.0      NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=inf          NaN  0.0  0.0  0.0  0.0  NaN
x=-0.0         m=inf          NaN  -0.0  0.0  -0.0  0.0  NaN
x=5.960464477539063e-8 m=inf          NaN  5.960464477539063e-8  5.960464477539063e-8  5.960464477539063e-8  5.960464477539063e-8  NaN
x=-5.960464477539063e-8 m=inf          NaN  inf?  0.0  inf?  65504.0  NaN
x=1.0          m=inf          NaN  1.0  1.0  1.0  1.0  NaN
x=-1.0         m=inf          NaN  inf?  0.0  inf?  65504.0  NaN
x=65504.0      m=inf          NaN  65504.0  65504.0  65504.0  65504.0  NaN
x=-65504.0     m=inf          NaN  inf?  0.0  inf?  65504.0  NaN
x=inf          m=inf          NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=inf          NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=inf          NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-0.0         m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=5.960464477539063e-8 m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-5.960464477539063e-8 m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=1.0          m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-1.0         m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=65504.0      m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-65504.0     m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=inf          m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-0.0         m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=5.960464477539063e-8 m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-5.960464477539063e-8 m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=1.0          m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-1.0         m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=65504.0      m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-65504.0     m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=inf          m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=-1.0         0.0?  0.0?  0.0?  0.0?  0.0?  -0.0?
x=-0.0         m=-1.0         0.0?  -0.0?  0.0?  -0.0?  0.0?  -0.0?
x=5.960464477539063e-8 m=-1.0         -0.9999999403953552?  5.960464477539063e-8?  5.960464477539063e-8?  5.960464477539063e-8?  5.960464477539063e-8?  -0.9999999403953552?
x=-5.960464477539063e-8 m=-1.0         -5.960464477539063e-8?  -1.0000000596046448?  -1.0000000596046448?  -1.0000000596046448?  -1.0000000596046448?  -5.960464477539063e-8?
x=1.0          m=-1.0         0.0?  0.0?  0.0?  0.0?  0.0?  -0.0?
x=-1.0         m=-1.0         0.0?  -0.0?  0.0?  -0.0?  0.0?  -0.0?
x=65504.0      m=-1.0         0.0?  0.0?  0.0?  0.0?  0.0?  -0.0?
x=-65504.0     m=-1.0         0.0?  -0.0?  0.0?  -0.0?  0.0?  -0.0?
x=inf          m=-1.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=-1.0         NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=-1.0         NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-0.0         m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=5.960464477539063e-8 m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-5.960464477539063e-8 m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=1.0          m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-1.0         m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=65504.0      m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-65504.0     m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=inf          m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
format bf16: candidates ["a", "b", "c", "d", "e", "g"]; '?' marks a value outside [0, m)
x=0.0          m=9.183549615799121e-41 0.0  0.0  0.0  0.0  0.0  0.0
x=-0.0         m=9.183549615799121e-41 0.0  -0.0  0.0  0.0  0.0  0.0
x=9.183549615799121e-41 m=9.183549615799121e-41 0.0  0.0  0.0  0.0  0.0  0.0
x=-9.183549615799121e-41 m=9.183549615799121e-41 0.0  -0.0  0.0  0.0  0.0  0.0
x=1.0          m=9.183549615799121e-41 -inf?  0.0  0.0  0.0  0.0  0.0
x=-1.0         m=9.183549615799121e-41 inf?  -0.0  0.0  0.0  0.0  0.0
x=3.3895313892515355e38 m=9.183549615799121e-41 -inf?  0.0  0.0  0.0  0.0  0.0
x=-3.3895313892515355e38 m=9.183549615799121e-41 inf?  -0.0  0.0  0.0  0.0  0.0
x=inf          m=9.183549615799121e-41 NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=9.183549615799121e-41 NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=9.183549615799121e-41 NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=1.0          0.0  0.0  0.0  0.0  0.0  0.0
x=-0.0         m=1.0          0.0  -0.0  0.0  0.0  0.0  0.0
x=9.183549615799121e-41 m=1.0          9.183549615799121e-41  9.183549615799121e-41  9.183549615799121e-41  9.183549615799121e-41  9.183549615799121e-41  0.0
x=-9.183549615799121e-41 m=1.0          1.0?  1.0?  0.0  0.99609375  0.99609375  0.0
x=1.0          m=1.0          0.0  0.0  0.0  0.0  0.0  0.0
x=-1.0         m=1.0          0.0  -0.0  0.0  0.0  0.0  0.0
x=3.3895313892515355e38 m=1.0          0.0  0.0  0.0  0.0  0.0  0.0
x=-3.3895313892515355e38 m=1.0          0.0  -0.0  0.0  0.0  0.0  0.0
x=inf          m=1.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=1.0          NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=1.0          NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=3.3895313892515355e38 0.0  0.0  0.0  0.0  0.0  0.0
x=-0.0         m=3.3895313892515355e38 0.0  -0.0  0.0  0.0  0.0  0.0
x=9.183549615799121e-41 m=3.3895313892515355e38 9.183549615799121e-41  9.183549615799121e-41  9.183549615799121e-41  9.183549615799121e-41  9.183549615799121e-41  0.0
x=-9.183549615799121e-41 m=3.3895313892515355e38 -9.183549615799121e-41?  3.3895313892515355e38?  0.0  3.3762391092936863e38  3.3762391092936863e38  0.0
x=1.0          m=3.3895313892515355e38 1.0  1.0  1.0  1.0  1.0  0.0
x=-1.0         m=3.3895313892515355e38 3.3895313892515355e38?  3.3895313892515355e38?  0.0  3.3762391092936863e38  3.3762391092936863e38  0.0
x=3.3895313892515355e38 m=3.3895313892515355e38 0.0  0.0  0.0  0.0  0.0  0.0
x=-3.3895313892515355e38 m=3.3895313892515355e38 0.0  -0.0  0.0  0.0  0.0  0.0
x=inf          m=3.3895313892515355e38 NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=3.3895313892515355e38 NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=3.3895313892515355e38 NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=inf          NaN  0.0  0.0  0.0  0.0  NaN
x=-0.0         m=inf          NaN  -0.0  0.0  -0.0  0.0  NaN
x=9.183549615799121e-41 m=inf          NaN  9.183549615799121e-41  9.183549615799121e-41  9.183549615799121e-41  9.183549615799121e-41  NaN
x=-9.183549615799121e-41 m=inf          NaN  inf?  0.0  inf?  3.3895313892515355e38  NaN
x=1.0          m=inf          NaN  1.0  1.0  1.0  1.0  NaN
x=-1.0         m=inf          NaN  inf?  0.0  inf?  3.3895313892515355e38  NaN
x=3.3895313892515355e38 m=inf          NaN  3.3895313892515355e38  3.3895313892515355e38  3.3895313892515355e38  3.3895313892515355e38  NaN
x=-3.3895313892515355e38 m=inf          NaN  inf?  0.0  inf?  3.3895313892515355e38  NaN
x=inf          m=inf          NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=inf          NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=inf          NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-0.0         m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=9.183549615799121e-41 m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-9.183549615799121e-41 m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=1.0          m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-1.0         m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=3.3895313892515355e38 m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-3.3895313892515355e38 m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=inf          m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-0.0         m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=9.183549615799121e-41 m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-9.183549615799121e-41 m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=1.0          m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-1.0         m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=3.3895313892515355e38 m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-3.3895313892515355e38 m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=inf          m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=-1.0         0.0?  0.0?  0.0?  0.0?  0.0?  -0.0?
x=-0.0         m=-1.0         0.0?  -0.0?  0.0?  -0.0?  0.0?  -0.0?
x=9.183549615799121e-41 m=-1.0         -1.0?  9.183549615799121e-41?  9.183549615799121e-41?  9.183549615799121e-41?  9.183549615799121e-41?  -0.0?
x=-9.183549615799121e-41 m=-1.0         -9.183549615799121e-41?  -1.0?  0.0?  -1.0?  NaN  -0.0?
x=1.0          m=-1.0         0.0?  0.0?  0.0?  0.0?  0.0?  -0.0?
x=-1.0         m=-1.0         0.0?  -0.0?  0.0?  -0.0?  0.0?  -0.0?
x=3.3895313892515355e38 m=-1.0         0.0?  0.0?  0.0?  0.0?  0.0?  -0.0?
x=-3.3895313892515355e38 m=-1.0         0.0?  -0.0?  0.0?  -0.0?  0.0?  -0.0?
x=inf          m=-1.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=-1.0         NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=-1.0         NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-0.0         m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=9.183549615799121e-41 m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-9.183549615799121e-41 m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=1.0          m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-1.0         m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=3.3895313892515355e38 m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-3.3895313892515355e38 m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=inf          m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
format f32: candidates ["a", "b", "c", "d", "e", "g"]; '?' marks a value outside [0, m)
x=0.0          m=1.401298464324817e-45 0.0  0.0  0.0  0.0  0.0  0.0
x=-0.0         m=1.401298464324817e-45 0.0  -0.0  0.0  0.0  0.0  0.0
x=1.401298464324817e-45 m=1.401298464324817e-45 0.0  0.0  0.0  0.0  0.0  0.0
x=-1.401298464324817e-45 m=1.401298464324817e-45 0.0  -0.0  0.0  0.0  0.0  0.0
x=1.0          m=1.401298464324817e-45 -inf?  0.0  0.0  0.0  0.0  0.0
x=-1.0         m=1.401298464324817e-45 inf?  -0.0  0.0  0.0  0.0  0.0
x=3.4028234663852886e38 m=1.401298464324817e-45 -inf?  0.0  0.0  0.0  0.0  0.0
x=-3.4028234663852886e38 m=1.401298464324817e-45 inf?  -0.0  0.0  0.0  0.0  0.0
x=inf          m=1.401298464324817e-45 NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=1.401298464324817e-45 NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=1.401298464324817e-45 NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=1.0          0.0  0.0  0.0  0.0  0.0  0.0
x=-0.0         m=1.0          0.0  -0.0  0.0  0.0  0.0  0.0
x=1.401298464324817e-45 m=1.0          1.401298464324817e-45  1.401298464324817e-45  1.401298464324817e-45  1.401298464324817e-45  1.401298464324817e-45  0.0
x=-1.401298464324817e-45 m=1.0          1.0?  1.0?  0.0  0.9999999403953552  0.9999999403953552  0.0
x=1.0          m=1.0          0.0  0.0  0.0  0.0  0.0  0.0
x=-1.0         m=1.0          0.0  -0.0  0.0  0.0  0.0  0.0
x=3.4028234663852886e38 m=1.0          0.0  0.0  0.0  0.0  0.0  0.0
x=-3.4028234663852886e38 m=1.0          0.0  -0.0  0.0  0.0  0.0  0.0
x=inf          m=1.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=1.0          NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=1.0          NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=3.4028234663852886e38 0.0  0.0  0.0  0.0  0.0  0.0
x=-0.0         m=3.4028234663852886e38 0.0  -0.0  0.0  0.0  0.0  0.0
x=1.401298464324817e-45 m=3.4028234663852886e38 1.401298464324817e-45  1.401298464324817e-45  1.401298464324817e-45  1.401298464324817e-45  1.401298464324817e-45  0.0
x=-1.401298464324817e-45 m=3.4028234663852886e38 -1.401298464324817e-45?  3.4028234663852886e38?  0.0  3.4028232635611926e38  3.4028232635611926e38  0.0
x=1.0          m=3.4028234663852886e38 1.0  1.0  1.0  1.0  1.0  0.0
x=-1.0         m=3.4028234663852886e38 3.4028234663852886e38?  3.4028234663852886e38?  0.0  3.4028232635611926e38  3.4028232635611926e38  0.0
x=3.4028234663852886e38 m=3.4028234663852886e38 0.0  0.0  0.0  0.0  0.0  0.0
x=-3.4028234663852886e38 m=3.4028234663852886e38 0.0  -0.0  0.0  0.0  0.0  0.0
x=inf          m=3.4028234663852886e38 NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=3.4028234663852886e38 NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=3.4028234663852886e38 NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=inf          NaN  0.0  0.0  0.0  0.0  NaN
x=-0.0         m=inf          NaN  -0.0  0.0  -0.0  0.0  NaN
x=1.401298464324817e-45 m=inf          NaN  1.401298464324817e-45  1.401298464324817e-45  1.401298464324817e-45  1.401298464324817e-45  NaN
x=-1.401298464324817e-45 m=inf          NaN  inf?  0.0  inf?  3.4028234663852886e38  NaN
x=1.0          m=inf          NaN  1.0  1.0  1.0  1.0  NaN
x=-1.0         m=inf          NaN  inf?  0.0  inf?  3.4028234663852886e38  NaN
x=3.4028234663852886e38 m=inf          NaN  3.4028234663852886e38  3.4028234663852886e38  3.4028234663852886e38  3.4028234663852886e38  NaN
x=-3.4028234663852886e38 m=inf          NaN  inf?  0.0  inf?  3.4028234663852886e38  NaN
x=inf          m=inf          NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=inf          NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=inf          NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-0.0         m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=1.401298464324817e-45 m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-1.401298464324817e-45 m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=1.0          m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-1.0         m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=3.4028234663852886e38 m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-3.4028234663852886e38 m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=inf          m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-0.0         m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=1.401298464324817e-45 m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-1.401298464324817e-45 m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=1.0          m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-1.0         m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=3.4028234663852886e38 m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-3.4028234663852886e38 m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=inf          m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=-1.0         0.0?  0.0?  0.0?  0.0?  0.0?  -0.0?
x=-0.0         m=-1.0         0.0?  -0.0?  0.0?  -0.0?  0.0?  -0.0?
x=1.401298464324817e-45 m=-1.0         -1.0?  1.401298464324817e-45?  1.401298464324817e-45?  1.401298464324817e-45?  1.401298464324817e-45?  -0.0?
x=-1.401298464324817e-45 m=-1.0         -1.401298464324817e-45?  -1.0?  0.0?  -1.0?  NaN  -0.0?
x=1.0          m=-1.0         0.0?  0.0?  0.0?  0.0?  0.0?  -0.0?
x=-1.0         m=-1.0         0.0?  -0.0?  0.0?  -0.0?  0.0?  -0.0?
x=3.4028234663852886e38 m=-1.0         0.0?  0.0?  0.0?  0.0?  0.0?  -0.0?
x=-3.4028234663852886e38 m=-1.0         0.0?  -0.0?  0.0?  -0.0?  0.0?  -0.0?
x=inf          m=-1.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=-1.0         NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=-1.0         NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-0.0         m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=1.401298464324817e-45 m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-1.401298464324817e-45 m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=1.0          m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-1.0         m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=3.4028234663852886e38 m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-3.4028234663852886e38 m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=inf          m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
format f64: candidates ["a", "b", "c", "d", "e", "g"]; '?' marks a value outside [0, m)
x=0.0          m=5e-324       0.0  0.0  0.0  0.0  0.0  0.0
x=-0.0         m=5e-324       0.0  -0.0  0.0  0.0  0.0  0.0
x=5e-324       m=5e-324       0.0  0.0  0.0  0.0  0.0  0.0
x=-5e-324      m=5e-324       0.0  -0.0  0.0  0.0  0.0  0.0
x=1.0          m=5e-324       -inf?  0.0  0.0  0.0  0.0  0.0
x=-1.0         m=5e-324       inf?  -0.0  0.0  0.0  0.0  0.0
x=1.7976931348623157e308 m=5e-324       -inf?  0.0  0.0  0.0  0.0  0.0
x=-1.7976931348623157e308 m=5e-324       inf?  -0.0  0.0  0.0  0.0  0.0
x=inf          m=5e-324       NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=5e-324       NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=5e-324       NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=1.0          0.0  0.0  0.0  0.0  0.0  0.0
x=-0.0         m=1.0          0.0  -0.0  0.0  0.0  0.0  0.0
x=5e-324       m=1.0          5e-324  5e-324  5e-324  5e-324  5e-324  0.0
x=-5e-324      m=1.0          1.0?  1.0?  0.0  0.9999999999999999  0.9999999999999999  0.0
x=1.0          m=1.0          0.0  0.0  0.0  0.0  0.0  0.0
x=-1.0         m=1.0          0.0  -0.0  0.0  0.0  0.0  0.0
x=1.7976931348623157e308 m=1.0          0.0  0.0  0.0  0.0  0.0  0.0
x=-1.7976931348623157e308 m=1.0          0.0  -0.0  0.0  0.0  0.0  0.0
x=inf          m=1.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=1.0          NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=1.0          NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=1.7976931348623157e308 0.0  0.0  0.0  0.0  0.0  0.0
x=-0.0         m=1.7976931348623157e308 0.0  -0.0  0.0  0.0  0.0  0.0
x=5e-324       m=1.7976931348623157e308 5e-324  5e-324  5e-324  5e-324  5e-324  0.0
x=-5e-324      m=1.7976931348623157e308 -5e-324?  1.7976931348623157e308?  0.0  1.7976931348623155e308  1.7976931348623155e308  0.0
x=1.0          m=1.7976931348623157e308 1.0  1.0  1.0  1.0  1.0  0.0
x=-1.0         m=1.7976931348623157e308 1.7976931348623157e308?  1.7976931348623157e308?  0.0  1.7976931348623155e308  1.7976931348623155e308  0.0
x=1.7976931348623157e308 m=1.7976931348623157e308 0.0  0.0  0.0  0.0  0.0  0.0
x=-1.7976931348623157e308 m=1.7976931348623157e308 0.0  -0.0  0.0  0.0  0.0  0.0
x=inf          m=1.7976931348623157e308 NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=1.7976931348623157e308 NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=1.7976931348623157e308 NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=inf          NaN  0.0  0.0  0.0  0.0  NaN
x=-0.0         m=inf          NaN  -0.0  0.0  -0.0  0.0  NaN
x=5e-324       m=inf          NaN  5e-324  5e-324  5e-324  5e-324  NaN
x=-5e-324      m=inf          NaN  inf?  0.0  inf?  1.7976931348623157e308  NaN
x=1.0          m=inf          NaN  1.0  1.0  1.0  1.0  NaN
x=-1.0         m=inf          NaN  inf?  0.0  inf?  1.7976931348623157e308  NaN
x=1.7976931348623157e308 m=inf          NaN  1.7976931348623157e308  1.7976931348623157e308  1.7976931348623157e308  1.7976931348623157e308  NaN
x=-1.7976931348623157e308 m=inf          NaN  inf?  0.0  inf?  1.7976931348623157e308  NaN
x=inf          m=inf          NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=inf          NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=inf          NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-0.0         m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=5e-324       m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-5e-324      m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=1.0          m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-1.0         m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=1.7976931348623157e308 m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-1.7976931348623157e308 m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=inf          m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=0.0          NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-0.0         m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=5e-324       m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-5e-324      m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=1.0          m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-1.0         m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=1.7976931348623157e308 m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-1.7976931348623157e308 m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=inf          m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=-0.0         NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=-1.0         0.0?  0.0?  0.0?  0.0?  0.0?  -0.0?
x=-0.0         m=-1.0         0.0?  -0.0?  0.0?  -0.0?  0.0?  -0.0?
x=5e-324       m=-1.0         -1.0?  5e-324?  5e-324?  5e-324?  5e-324?  -0.0?
x=-5e-324      m=-1.0         -5e-324?  -1.0?  0.0?  -1.0?  NaN  -0.0?
x=1.0          m=-1.0         0.0?  0.0?  0.0?  0.0?  0.0?  -0.0?
x=-1.0         m=-1.0         0.0?  -0.0?  0.0?  -0.0?  0.0?  -0.0?
x=1.7976931348623157e308 m=-1.0         0.0?  0.0?  0.0?  0.0?  0.0?  -0.0?
x=-1.7976931348623157e308 m=-1.0         0.0?  -0.0?  0.0?  -0.0?  0.0?  -0.0?
x=inf          m=-1.0         NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=-1.0         NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=-1.0         NaN  NaN  NaN  NaN  NaN  NaN
x=0.0          m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-0.0         m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=5e-324       m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-5e-324      m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=1.0          m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-1.0         m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=1.7976931348623157e308 m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-1.7976931348623157e308 m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=inf          m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=-inf         m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
x=NaN          m=NaN          NaN  NaN  NaN  NaN  NaN  NaN
```

## Probe outputs (each language run on this machine, bit-exact)

```
MOD / REMAINDER PROBES, measured 2026-11-21 on Linux x86_64 (Fedora 44, glibc 2.43).

TOOLCHAIN VERSIONS
gcc (GCC) 16.2.1 20261029 (Red Hat 16.2.1-3)
g++ (GCC) 16.2.1 20261029 (Red Hat 16.2.1-3)
clang version 22.1.8 (Fedora 22.1.8-4.fc44)
rustc 1.102.0-nightly (59cbdee2e 2026-11-17)
go version go1.26.10-X:nodwarf5 linux/amd64
v22.22.2
java version "26.0.2" 2026-07-21
javac 26.0.2
Python 3.14.10
numpy 2.5.3
ruby 4.0.9 (2026-10-23 revision 3e93b23afc) +PRISM [x86_64-linux]
LuaJIT 2.1.1767980792 -- Copyright (C) 2005-2026 Mike Pall. https://luajit.org/
The Glorious Glasgow Haskell Compilation System, version 9.10.3
perl v5.42.3
Dart SDK version: 3.13.7 (stable) (Thu Oct 22 14:28:57 2026 -0700) on "linux_x64"
bc 1.08.2
tcl 9.0.2
GNU Awk 5.3.2, API 4.0, PMA Avon 8-g1, (GNU MPFR 4.2.2, GNU MP 6.3.0)
This is LuaTeX, Version 1.24.0 (TeX Live 2026)
texlua _VERSION: Lua 5.3 (printed by lua53_probe.lua)
ldd (GNU libc) 2.43


LEGEND
  Cells are the shortest round-trip decimal of the f64 result, recomputed from the 64-bit pattern the
  program printed (Python repr). The bit patterns themselves are in each <lang>_probe.out / c_float_*.out.
  gawk has no bit cast: its cells come from %.17g. "-nan" = NaN with sign bit set; "nan" = sign clear.
  *m  result equals m exactly.
  !   result lies outside [0, m) for m > 0 (NaN results are not marked).
  w   a warning was printed (NumPy RuntimeWarning, Perl warning); text in the .out file.
  E<n> an exception / panic / signal; texts listed under ERRORS.
  -   operation not run for this case.
  "formula" is x - m*floor(x/m) written in that language in f64.
  Quotient-only ops (div_euclid, div', ~/, remquo's quo) are omitted from the float table; see .out files.
  Input NaN (case 14): C, Rust, Python, Java, JS, Ruby pass NaN with sign clear (7ff8000000000000); Go 7ff8000000000001;
  LuaJIT, Lua5.3, Perl, Haskell (0/0 or inf-inf) and Dart (double.nan) have the sign bit set (fff8000000000000); Tcl rejects NaN.
  C row is gcc -O0. clang -O2 output is byte-identical to it; gcc -O2 differs ONLY in remainder() NaN sign for cases 12, 19, 21 (-nan instead of nan).
  Rust rows are rustc -O; an unoptimized (debug) build printed byte-identical output.
  C/C++ int rows: gcc -O0, gcc -O2, clang -O2, g++ -O2 and clang++ -O2 (same source compiled as C++) printed identical output.

FLOAT TABLE, part 1 (cases 0-10)
operation                        [0] -90,360  [1] -1e-20,360  [2] 5.5,2  [3] -0.5,2  [4] -0.0,360  [5] 360,360  [6] 1e300,3  [7] -1e300,3  [8] 5e-324,1  [9] -5e-324,1  [10] 1,5e-324
-------------------------------  -----------  --------------  ---------  ----------  ------------  -----------  -----------  ------------  ------------  -------------  -------------
C fmod                           -90.0!       -1e-20!         1.5        -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0
C remainder                      -90.0!       -1e-20!         -0.5!      -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0
C remquo                         -90.0!       -1e-20!         -0.5!      -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0
C fmod_then_plus_m_if_neg        270.0        360.0*m         1.5        1.5         -0.0          0.0          0.0          -0.0          5e-324        1.0*m          0.0
C formula                        270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          -inf!
Rust f64.%                       -90.0!       -1e-20!         1.5        -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0
Rust f64.rem_euclid              270.0        360.0*m         1.5        1.5         -0.0          0.0          0.0          -0.0          5e-324        1.0*m          0.0
Rust formula                     270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          -inf!
Python py.%                      270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          0.0
Python py.math.fmod              -90.0!       -1e-20!         1.5        -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0
Python py.math.remainder         -90.0!       -1e-20!         -0.5!      -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0
Python py.divmod                 270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          0.0
Python py.formula                270.0        360.0*m         1.5        1.5         -0.0          0.0          0.0          0.0           5e-324        1.0*m          E6
Python py.formula_floatfloor     270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          -inf!
Python np.mod                    270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          0.0
Python np.fmod                   -90.0!       -1e-20!         1.5        -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0
Python np.remainder              270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          0.0
Python np.divmod                 270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          0.0w
Python np.formula                270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          -inf!w
Python np.mod_array              270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          0.0
Go math.Mod                      -90.0!       -1e-20!         1.5        -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0
Go math.Remainder                -90.0!       -1e-20!         -0.5!      -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0
Go formula                       270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          -inf!
Java %                           -90.0!       -1e-20!         1.5        -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0
Java Math.IEEEremainder          -90.0!       -1e-20!         -0.5!      -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0
Java StrictMath.IEEEremainder    -90.0!       -1e-20!         -0.5!      -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0
Java formula                     270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          -inf!
Java StrictMath.formula          270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          -inf!
JS %                             -90.0!       -1e-20!         1.5        -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0
JS formula                       270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          -inf!
JS ((x%m)+m)%m                   270.0        0.0             1.5        1.5         0.0           0.0          0.0          0.0           0.0           0.0            0.0
Ruby %                           270.0        360.0*m         1.5        1.5         -0.0          0.0          0.0          -0.0          5e-324        1.0*m          0.0
Ruby modulo                      270.0        360.0*m         1.5        1.5         -0.0          0.0          0.0          -0.0          5e-324        1.0*m          0.0
Ruby remainder                   -90.0!       0.0             1.5        -0.5!       -0.0          0.0          0.0          -0.0          5e-324        0.0            0.0
Ruby divmod                      270.0        360.0*m         1.5        1.5         -0.0          0.0          0.0          -0.0          5e-324        1.0*m          E14
Ruby formula                     270.0        360.0*m         1.5        1.5         -0.0          0.0          0.0          0.0           5e-324        1.0*m          E14
Ruby formula_float_floor         270.0        360.0*m         1.5        1.5         -0.0          0.0          0.0          0.0           5e-324        1.0*m          E14
LuaJIT %                         270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          -inf!
LuaJIT math.fmod                 -90.0!       -1e-20!         1.5        -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0
LuaJIT formula                   270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          -inf!
Lua5.3 %                         270.0        360.0*m         1.5        1.5         -0.0          0.0          0.0          -0.0          5e-324        1.0*m          0.0
Lua5.3 math.fmod                 -90.0!       -1e-20!         1.5        -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0
Lua5.3 formula                   270.0        360.0*m         1.5        1.5         -0.0          0.0          0.0          0.0           5e-324        1.0*m          -inf!
Perl %                           270.0        0.0             1.0        0.0         0.0           0.0          0.0          0.0           0.0           0.0            E21
Perl POSIX::fmod                 -90.0!       -1e-20!         1.5        -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0
Perl POSIX::remainder            -90.0!       -1e-20!         -0.5!      -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0
Perl formula                     270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          -inf!
Haskell Data.Fixed.mod'          270.0        360.0*m         1.5        1.5         -0.0          0.0          0.0          0.0           5e-324        1.0*m          -inf!
Haskell formula(floor::Integer)  270.0        360.0*m         1.5        1.5         -0.0          0.0          0.0          0.0           5e-324        1.0*m          -inf!
Haskell formula(floor::Int)      270.0        360.0*m         1.5        1.5         -0.0          0.0          1e+300!      -1e+300!      5e-324        1.0*m          1.0!
Dart %                           270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          0.0
Dart remainder                   -90.0!       -1e-20!         1.5        -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0
Dart formula                     270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          -inf!
Dart formula(floor() to int)     270.0        360.0*m         1.5        1.5         -0.0          0.0          1e+300!      -1e+300!      5e-324        1.0*m          E26
Tcl fmod                         -90.0!       -1e-20!         1.5        -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0
Tcl %                            E28          E29             E30        E31         E32           E33          E34          E35           E36           E37            E38
Tcl formula                      270.0        360.0*m         1.5        1.5         0.0           0.0          0.0          0.0           5e-324        1.0*m          -inf!
gawk %                           -90.0!       -1e-20!         1.5        -0.5!       -0.0          0.0          0.0          -0.0          5e-324        -5e-324!       0.0

FLOAT TABLE, part 2 (cases 11-21)
operation                        [11] 0.75,1.5e-323  [12] inf,360  [13] -inf,360  [14] nan,360  [15] -1,inf  [16] 1,inf  [17] -90,-360  [18] 90,-360  [19] 5,0  [20] -5,0  [21] 0,0
-------------------------------  ------------------  ------------  -------------  ------------  -----------  ----------  -------------  ------------  --------  ---------  --------
C fmod                           0.0                 -nan          -nan           nan           -1.0!        1.0         -90.0          90.0          -nan      -nan       -nan
C remainder                      0.0                 nan           -nan           nan           -1.0!        1.0         -90.0          90.0          nan       -nan       nan
C remquo                         0.0                 -nan          -nan           nan           -1.0!        1.0         -90.0          90.0          -nan      -nan       -nan
C fmod_then_plus_m_if_neg        0.0                 -nan          -nan           nan           inf*m        1.0         -450.0         90.0          -nan      -nan       -nan
C formula                        -inf!               -nan          -nan           nan           -nan         -nan        -90.0          -270.0        -nan      -nan       -nan
Rust f64.%                       0.0                 -nan          -nan           nan           -1.0!        1.0         -90.0          90.0          -nan      -nan       -nan
Rust f64.rem_euclid              0.0                 -nan          -nan           nan           inf*m        1.0         270.0          90.0          -nan      -nan       -nan
Rust formula                     -inf!               -nan          -nan           nan           -nan         -nan        -90.0          -270.0        -nan      -nan       -nan
Python py.%                      0.0                 -nan          -nan           nan           inf*m        1.0         -90.0          -270.0        E9        E9         E9
Python py.math.fmod              0.0                 E7            E7             nan           -1.0!        1.0         -90.0          90.0          E7        E7         E7
Python py.math.remainder         0.0                 E7            E7             nan           -1.0!        1.0         -90.0          90.0          E7        E7         E7
Python py.divmod                 0.0                 -nan          -nan           nan           inf*m        1.0         -90.0          -270.0        E9        E9         E9
Python py.formula                E6                  E6            E6             E8            -nan         -nan        -90.0          -270.0        E9        E9         E9
Python py.formula_floatfloor     -inf!               -nan          -nan           nan           -nan         -nan        -90.0          -270.0        E9        E9         E9
Python np.mod                    0.0                 -nanw         -nanw          nan           inf*m        1.0         -90.0          -270.0        -nanw     -nanw      -nanw
Python np.fmod                   0.0                 -nanw         -nanw          nan           -1.0!        1.0         -90.0          90.0          -nanw     -nanw      -nanw
Python np.remainder              0.0                 -nanw         -nanw          nan           inf*m        1.0         -90.0          -270.0        -nanw     -nanw      -nanw
Python np.divmod                 0.0w                -nanw         -nanw          nan           inf*m        1.0         -90.0          -270.0        -nanw     -nanw      -nanw
Python np.formula                -inf!w              -nanw         -nanw          nan           -nanw        -nanw       -90.0          -270.0        -nanw     -nanw      -nanw
Python np.mod_array              0.0                 -nanw         -nanw          nan           inf*m        1.0         -90.0          -270.0        -nanw     -nanw      -nanw
Go math.Mod                      0.0                 nan           nan            nan           -1.0!        1.0         -90.0          90.0          nan       nan        nan
Go math.Remainder                0.0                 nan           nan            nan           -1.0!        1.0         -90.0          90.0          nan       nan        nan
Go formula                       -inf!               -nan          -nan           nan           -nan         -nan        -90.0          -270.0        -nan      -nan       -nan
Java %                           0.0                 -nan          -nan           nan           -1.0!        1.0         -90.0          90.0          -nan      -nan       -nan
Java Math.IEEEremainder          0.0                 -nan          -nan           nan           -1.0!        1.0         -90.0          90.0          -nan      -nan       -nan
Java StrictMath.IEEEremainder    0.0                 -nan          -nan           nan           -1.0!        1.0         -90.0          90.0          -nan      -nan       -nan
Java formula                     -inf!               -nan          -nan           nan           -nan         -nan        -90.0          -270.0        -nan      -nan       -nan
Java StrictMath.formula          -inf!               -nan          -nan           nan           -nan         -nan        -90.0          -270.0        -nan      -nan       -nan
JS %                             0.0                 -nan          -nan           nan           -1.0!        1.0         -90.0          90.0          -nan      -nan       -nan
JS formula                       -inf!               -nan          -nan           nan           -nan         -nan        -90.0          -270.0        -nan      -nan       -nan
JS ((x%m)+m)%m                   0.0                 -nan          -nan           nan           -nan         -nan        -90.0          -270.0        -nan      -nan       -nan
Ruby %                           0.0                 -nan          -nan           nan           inf*m        1.0         -90.0          -270.0        E17       E17        E17
Ruby modulo                      0.0                 -nan          -nan           nan           inf*m        1.0         -90.0          -270.0        E17       E17        E17
Ruby remainder                   0.0                 -nan          -nan           nan           -1.0!        1.0         -90.0          90.0          E17       E17        E17
Ruby divmod                      E14                 E14           E15            E16           inf*m        1.0         -90.0          -270.0        E17       E17        E17
Ruby formula                     E14                 E14           E15            E16           -nan         -nan        -90.0          -270.0        E14       E15        E16
Ruby formula_float_floor         E14                 E14           E15            E16           -nan         -nan        -90.0          -270.0        E14       E15        E16
LuaJIT %                         -inf!               -nan          -nan           -nan          -nan         -nan        -90.0          -270.0        -nan      -nan       -nan
LuaJIT math.fmod                 0.0                 -nan          -nan           -nan          -1.0!        1.0         -90.0          90.0          -nan      -nan       -nan
LuaJIT formula                   -inf!               -nan          -nan           -nan          -nan         -nan        -90.0          -270.0        -nan      -nan       -nan
Lua5.3 %                         0.0                 -nan          -nan           -nan          inf*m        1.0         -90.0          -270.0        -nan      -nan       -nan
Lua5.3 math.fmod                 0.0                 -nan          -nan           -nan          -1.0!        1.0         -90.0          90.0          -nan      -nan       -nan
Lua5.3 formula                   -inf!               -nan          -nan           -nan          -nan         -nan        -90.0          -270.0        -nan      -nan       -nan
Perl %                           E21                 -nan          -nan           -nan          inf*m        1.0         -90.0          -270.0        E21       E21        E21
Perl POSIX::fmod                 0.0                 -nan          -nan           -nan          -1.0!        1.0         -90.0          90.0          -nan      -nan       -nan
Perl POSIX::remainder            0.0                 -nan          -nan           -nan          -1.0!        1.0         -90.0          90.0          -nan      -nan       -nan
Perl formula                     -inf!               -nan          -nan           -nan          -nan         -nan        -90.0          -270.0        E22       E22        E22
Haskell Data.Fixed.mod'          -inf!               -nan          -nan           -nan          inf*m        -nan        -90.0          -270.0        E23       E23        E23
Haskell formula(floor::Integer)  -inf!               -nan          -nan           -nan          -nan         -nan        -90.0          -270.0        -nan      -nan       -nan
Haskell formula(floor::Int)      0.75!               inf!          -inf!          -nan          -nan         -nan        -90.0          -270.0        5.0       -5.0       0.0
Dart %                           0.0                 -nan          -nan           -nan          inf*m        1.0         270.0          90.0          -nan      -nan       -nan
Dart remainder                   0.0                 -nan          -nan           -nan          -1.0!        1.0         -90.0          90.0          -nan      -nan       -nan
Dart formula                     -inf!               -nan          -nan           -nan          -nan         -nan        -90.0          -270.0        -nan      -nan       -nan
Dart formula(floor() to int)     E26                 E26           E26            E26           -nan         -nan        -90.0          -270.0        E26       E26        E26
Tcl fmod                         0.0                 E40           E40            E43           -1.0!        1.0         -90.0          90.0          E40       E40        E40
Tcl %                            E39                 E41           E42            E44           E46          E38         E28            E47           E48       E49        E50
Tcl formula                      -inf!               E40           E40            E45           E40          E40         -90.0          -270.0        E40       E40        E40
gawk %                           0.0                 nan           nan            nan           -1.0!        1.0         -90.0          90.0          -         -          -

F32 TABLE (cells are the language's own shortest f32 decimal; bits in .out)
operation                       [0] -1e-20f,360f  [1] -90f,360f  [2] -1e-7f,1f
------------------------------  ----------------  -------------  -------------
C f32.fmodf                     -1e-20!           -9e+01!        -1e-07!
C f32.remainderf                -1e-20!           -9e+01!        -1e-07!
C f32.fmodf_then_plus_m_if_neg  3.6e+02*m         2.7e+02        0.9999999
C f32.formula                   3.6e+02*m         2.7e+02        0.9999999
Rust f32.%                      -1e-20!           -90.0!         -1e-7!
Rust f32.rem_euclid             360.0*m           270.0          0.9999999
Rust f32.formula                360.0*m           270.0          0.9999999

INT TABLE (MIN = INT64_MIN = -9223372036854775808; Perl int./ is float division; Tcl, Python, Ruby, BigInt, Haskell Integer, bc are arbitrary precision)
operation                    [0] 7,3           [1] -7,3           [2] 7,-3           [3] -7,-3         [4] 0,3      [5] 7,0       [6] -7,0      [7] MIN,-1
---------------------------  ----------------  -----------------  -----------------  ----------------  -----------  ------------  ------------  -------------------------------
C/C++ /                      2                 -2                 -2                 2                 0            E1            E1            E1
C/C++ %                      1                 -1                 1                  -1                0            E1            E1            E1
Rust i64./                   2                 -2                 -2                 2                 0            E2            E2            E4
Rust i64.%                   1                 -1                 1                  -1                0            E3            E3            E5
Rust i64.div_euclid          2                 -3                 -2                 3                 0            E2            E2            E4
Rust i64.rem_euclid          1                 2                  1                  2                 0            E3            E3            E5
Python int.py.%              1                 2                  -2                 -1                0            E9            E9            0
Python int.py.//             2                 -3                 -3                 2                 0            E9            E9            9223372036854775808
Python int.py.divmod         (2, 1)            (-3, 2)            (-3, -2)           (2, -1)           (0, 0)       E9            E9            (9223372036854775808, 0)
Python int.np.int64.%        np.int64(1)       np.int64(2)        np.int64(-2)       np.int64(-1)      np.int64(0)  np.int64(0)w  np.int64(0)w  np.int64(0)
Python int.np.int64.//       np.int64(2)       np.int64(-3)       np.int64(-3)       np.int64(2)       np.int64(0)  np.int64(0)w  np.int64(0)w  np.int64(-9223372036854775808)w
Python int.np.int64.fmod     np.int64(1)       np.int64(-1)       np.int64(1)        np.int64(-1)      np.int64(0)  np.int64(0)w  np.int64(0)w  np.int64(0)
Python int.np.int64array.%   np.int64(1)       np.int64(2)        np.int64(-2)       np.int64(-1)      np.int64(0)  np.int64(0)w  np.int64(0)w  np.int64(0)
Python int.np.int64array.//  np.int64(2)       np.int64(-3)       np.int64(-3)       np.int64(2)       np.int64(0)  np.int64(0)w  np.int64(0)w  np.int64(-9223372036854775808)w
Go int64./                   2                 -2                 -2                 2                 0            E10           E10           -9223372036854775808
Go int64.%                   1                 -1                 1                  -1                0            E10           E10           0
Java long./                  2                 -2                 -2                 2                 0            E11           E11           -9223372036854775808
Java long.%                  1                 -1                 1                  -1                0            E11           E11           0
Java Math.floorDiv           2                 -3                 -3                 2                 0            E11           E11           -9223372036854775808
Java Math.floorMod           1                 2                  -2                 -1                0            E11           E11           0
Java Math.divideExact        2                 -2                 -2                 2                 0            E11           E11           E12
Java Math.ceilDiv            3                 -2                 -2                 3                 0            E11           E11           -9223372036854775808
Java Math.ceilMod            -2                -1                 1                  2                 0            E11           E11           0
JS BigInt.%                  1                 -1                 1                  -1                0            E13           E13           0
JS BigInt./                  2                 -2                 -2                 2                 0            E13           E13           9223372036854775808
JS Number.%                  1                 -1                 1                  -1                0            NaN           NaN           -0
JS Math.trunc(Number./)      2                 -2                 -2                 2                 0            Infinity      -Infinity     9223372036854776000
JS int32 via x/m bitor 0     2                 -2                 -2                 2                 0            0             0             0
Ruby int.%                   1                 2                  -2                 -1                0            E17           E17           0
Ruby int./                   2                 -3                 -3                 2                 0            E17           E17           9223372036854775808
Ruby int.modulo              1                 2                  -2                 -1                0            E17           E17           0
Ruby int.remainder           1                 -1                 1                  -1                0            E17           E17           0
Ruby int.divmod              [2, 1]            [-3, 2]            [-3, -2]           [2, -1]           [0, 0]       E17           E17           [9223372036854775808, 0]
LuaJIT int.%                 1                 2                  -2                 -1                0            nan           nan           -
LuaJIT int.math.fmod         1                 -1                 1                  -1                0            nan           nan           -
LuaJIT int.math.floor(x/m)   2                 -3                 -3                 2                 0            inf           -inf          -
Lua5.3 int.%                 1                 2                  -2                 -1                0            E18           E18           0
Lua5.3 int.//                2                 -3                 -3                 2                 0            E19           E19           -9223372036854775808
Lua5.3 int.math.fmod         1                 -1                 1                  -1                0            E20           E20           0
Perl int.%                   1                 2                  -2                 -1                0            E21           E21           0
Perl int./                   2.33333333333333  -2.33333333333333  -2.33333333333333  2.33333333333333  0            E22           E22           9223372036854775808
Perl int.int(x/m)            2                 -2                 -2                 2                 0            E22           E22           9223372036854775808
Perl int.use_integer.%       1                 -1                 1                  -1                0            E21           E21           0
Perl int.use_integer./       2                 -2                 -2                 2                 0            E22           E22           -9223372036854775808
Haskell Int64.mod            1                 2                  -2                 -1                0            E24           E24           0
Haskell Int64.rem            1                 -1                 1                  -1                0            E24           E24           0
Haskell Int64.div            2                 -3                 -3                 2                 0            E24           E24           E25
Haskell Int64.quot           2                 -2                 -2                 2                 0            E24           E24           E25
Haskell Int64.divMod         (2,1)             (-3,2)             (-3,-2)            (2,-1)            (0,0)        E24           E24           E25
Haskell Int64.quotRem        (2,1)             (-2,-1)            (-2,1)             (2,-1)            (0,0)        E24           E24           E25
Haskell Integer.mod          1                 2                  -2                 -1                0            E24           E24           0
Haskell Integer.div          2                 -3                 -3                 2                 0            E24           E24           9223372036854775808
Dart int.%                   1                 2                  1                  2                 0            E27           E27           0
Dart int.~/                  2                 -2                 -2                 2                 0            E27           E27           -9223372036854775808
Dart int.remainder           1                 -1                 1                  -1                0            E27           E27           0
Tcl int.%                    1                 2                  -2                 -1                0            E51           E51           0
Tcl int./                    2                 -3                 -3                 2                 0            E51           E51           9223372036854775808
gawk int.%                   1                 -1                 1                  -1                0            -             -             -0
gawk int.int(x/m)            2                 -2                 -2                 2                 0            -             -             9.2233720368547758e+18
bc(scale=0) %                1                 -1                 1                  -1                0            E52           E54           0
bc(scale=0) /                2                 -2                 -2                 2                 0            E53           E55           9223372036854775808

BC AT scale=20 (not in the table): -7 % 3 -> -.00000000000000000001 ; 5.5 % 2 -> 0 ; -90 % 360 -> 0

ERRORS
  E1: killed by signal 8 (Floating point exception)
  E2: panic: attempt to divide by zero
  E3: panic: attempt to calculate the remainder with a divisor of zero
  E4: panic: attempt to divide with overflow
  E5: panic: attempt to calculate the remainder with overflow
  E6: OverflowError: cannot convert float infinity to integer
  E7: ValueError: math domain error
  E8: ValueError: cannot convert float NaN to integer
  E9: ZeroDivisionError: division by zero
  E10: panic: runtime error: integer divide by zero
  E11: java.lang.ArithmeticException: / by zero
  E12: java.lang.ArithmeticException: long overflow
  E13: RangeError: Division by zero
  E14: FloatDomainError: Infinity
  E15: FloatDomainError: -Infinity
  E16: FloatDomainError: NaN
  E17: ZeroDivisionError: divided by 0
  E18: attempt to perform 'n%0'
  E19: attempt to divide by zero
  E20: bad argument #2 to 'fmod' (zero)
  E21: Illegal modulus zero at <file> line N.
  E22: Illegal division by zero at <file> line N.
  E23: Ratio has zero denominator
  E24: divide by zero
  E25: arithmetic overflow
  E26: UnsupportedError: Unsupported operation: Infinity or NaN toInt
  E27: IntegerDivisionByZeroException: IntegerDivisionByZeroException
  E28: cannot use floating-point value "-90.0" as left operand of "%" | errorcode: ARITH DOMAIN {floating-point value}
  E29: cannot use floating-point value "-1e-20" as left operand of "%" | errorcode: ARITH DOMAIN {floating-point value}
  E30: cannot use floating-point value "5.5" as left operand of "%" | errorcode: ARITH DOMAIN {floating-point value}
  E31: cannot use floating-point value "-0.5" as left operand of "%" | errorcode: ARITH DOMAIN {floating-point value}
  E32: cannot use floating-point value "-0.0" as left operand of "%" | errorcode: ARITH DOMAIN {floating-point value}
  E33: cannot use floating-point value "360.0" as left operand of "%" | errorcode: ARITH DOMAIN {floating-point value}
  E34: cannot use floating-point value "1e300" as left operand of "%" | errorcode: ARITH DOMAIN {floating-point value}
  E35: cannot use floating-point value "-1e300" as left operand of "%" | errorcode: ARITH DOMAIN {floating-point value}
  E36: cannot use floating-point value "4.9406564584124654e-324" as left operand of "%" | errorcode: ARITH DOMAIN {floating-point value}
  E37: cannot use floating-point value "-4.9406564584124654e-324" as left operand of "%" | errorcode: ARITH DOMAIN {floating-point value}
  E38: cannot use floating-point value "1.0" as left operand of "%" | errorcode: ARITH DOMAIN {floating-point value}
  E39: cannot use floating-point value "0.75" as left operand of "%" | errorcode: ARITH DOMAIN {floating-point value}
  E40: domain error: argument not in valid range | errorcode: ARITH DOMAIN {domain error: argument not in valid range}
  E41: cannot use floating-point value "Inf" as left operand of "%" | errorcode: ARITH DOMAIN {floating-point value}
  E42: cannot use floating-point value "-Inf" as left operand of "%" | errorcode: ARITH DOMAIN {floating-point value}
  E43: floating point value is Not a Number | errorcode: TCL VALUE DOUBLE NAN
  E44: cannot use non-numeric floating-point value "NaN" as left operand of "%" | errorcode: ARITH DOMAIN {non-numeric floating-point value}
  E45: cannot use non-numeric floating-point value "NaN" as left operand of "/" | errorcode: ARITH DOMAIN {non-numeric floating-point value}
  E46: cannot use floating-point value "-1.0" as left operand of "%" | errorcode: ARITH DOMAIN {floating-point value}
  E47: cannot use floating-point value "90.0" as left operand of "%" | errorcode: ARITH DOMAIN {floating-point value}
  E48: cannot use floating-point value "5.0" as left operand of "%" | errorcode: ARITH DOMAIN {floating-point value}
  E49: cannot use floating-point value "-5.0" as left operand of "%" | errorcode: ARITH DOMAIN {floating-point value}
  E50: cannot use floating-point value "0.0" as left operand of "%" | errorcode: ARITH DOMAIN {floating-point value}
  E51: divide by zero | errorcode: ARITH DIVZERO {divide by zero}
  E52: Runtime error (func=(main), adr=5): Modulo by zero
  E53: Runtime error (func=(main), adr=5): Divide by zero
  E54: Runtime error (func=(main), adr=6): Modulo by zero
  E55: Runtime error (func=(main), adr=6): Divide by zero

FLOAT RESULTS EQUAL TO m OR OUTSIDE [0, m), FOR FINITE x AND FINITE m > 0
  C fmod                                   case [0] (-90,360) -> -90.0 !
  C fmod                                   case [1] (-1e-20,360) -> -1e-20 !
  C fmod                                   case [3] (-0.5,2) -> -0.5 !
  C fmod                                   case [9] (-5e-324,1) -> -5e-324 !
  C remainder                              case [0] (-90,360) -> -90.0 !
  C remainder                              case [1] (-1e-20,360) -> -1e-20 !
  C remainder                              case [2] (5.5,2) -> -0.5 !
  C remainder                              case [3] (-0.5,2) -> -0.5 !
  C remainder                              case [9] (-5e-324,1) -> -5e-324 !
  C remquo                                 case [0] (-90,360) -> -90.0 !
  C remquo                                 case [1] (-1e-20,360) -> -1e-20 !
  C remquo                                 case [2] (5.5,2) -> -0.5 !
  C remquo                                 case [3] (-0.5,2) -> -0.5 !
  C remquo                                 case [9] (-5e-324,1) -> -5e-324 !
  C fmod_then_plus_m_if_neg                case [1] (-1e-20,360) -> 360.0 *m
  C fmod_then_plus_m_if_neg                case [9] (-5e-324,1) -> 1.0 *m
  C formula                                case [1] (-1e-20,360) -> 360.0 *m
  C formula                                case [9] (-5e-324,1) -> 1.0 *m
  C formula                                case [10] (1,5e-324) -> -inf !
  C formula                                case [11] (0.75,1.5e-323) -> -inf !
  Rust f64.%                               case [0] (-90,360) -> -90.0 !
  Rust f64.%                               case [1] (-1e-20,360) -> -1e-20 !
  Rust f64.%                               case [3] (-0.5,2) -> -0.5 !
  Rust f64.%                               case [9] (-5e-324,1) -> -5e-324 !
  Rust f64.rem_euclid                      case [1] (-1e-20,360) -> 360.0 *m
  Rust f64.rem_euclid                      case [9] (-5e-324,1) -> 1.0 *m
  Rust formula                             case [1] (-1e-20,360) -> 360.0 *m
  Rust formula                             case [9] (-5e-324,1) -> 1.0 *m
  Rust formula                             case [10] (1,5e-324) -> -inf !
  Rust formula                             case [11] (0.75,1.5e-323) -> -inf !
  Python py.%                              case [1] (-1e-20,360) -> 360.0 *m
  Python py.%                              case [9] (-5e-324,1) -> 1.0 *m
  Python py.math.fmod                      case [0] (-90,360) -> -90.0 !
  Python py.math.fmod                      case [1] (-1e-20,360) -> -1e-20 !
  Python py.math.fmod                      case [3] (-0.5,2) -> -0.5 !
  Python py.math.fmod                      case [9] (-5e-324,1) -> -5e-324 !
  Python py.math.remainder                 case [0] (-90,360) -> -90.0 !
  Python py.math.remainder                 case [1] (-1e-20,360) -> -1e-20 !
  Python py.math.remainder                 case [2] (5.5,2) -> -0.5 !
  Python py.math.remainder                 case [3] (-0.5,2) -> -0.5 !
  Python py.math.remainder                 case [9] (-5e-324,1) -> -5e-324 !
  Python py.divmod                         case [1] (-1e-20,360) -> 360.0 *m
  Python py.divmod                         case [9] (-5e-324,1) -> 1.0 *m
  Python py.formula                        case [1] (-1e-20,360) -> 360.0 *m
  Python py.formula                        case [9] (-5e-324,1) -> 1.0 *m
  Python py.formula_floatfloor             case [1] (-1e-20,360) -> 360.0 *m
  Python py.formula_floatfloor             case [9] (-5e-324,1) -> 1.0 *m
  Python py.formula_floatfloor             case [10] (1,5e-324) -> -inf !
  Python py.formula_floatfloor             case [11] (0.75,1.5e-323) -> -inf !
  Python np.mod                            case [1] (-1e-20,360) -> 360.0 *m
  Python np.mod                            case [9] (-5e-324,1) -> 1.0 *m
  Python np.fmod                           case [0] (-90,360) -> -90.0 !
  Python np.fmod                           case [1] (-1e-20,360) -> -1e-20 !
  Python np.fmod                           case [3] (-0.5,2) -> -0.5 !
  Python np.fmod                           case [9] (-5e-324,1) -> -5e-324 !
  Python np.remainder                      case [1] (-1e-20,360) -> 360.0 *m
  Python np.remainder                      case [9] (-5e-324,1) -> 1.0 *m
  Python np.divmod                         case [1] (-1e-20,360) -> 360.0 *m
  Python np.divmod                         case [9] (-5e-324,1) -> 1.0 *m
  Python np.formula                        case [1] (-1e-20,360) -> 360.0 *m
  Python np.formula                        case [9] (-5e-324,1) -> 1.0 *m
  Python np.formula                        case [10] (1,5e-324) -> -inf !
  Python np.formula                        case [11] (0.75,1.5e-323) -> -inf !
  Python np.mod_array                      case [1] (-1e-20,360) -> 360.0 *m
  Python np.mod_array                      case [9] (-5e-324,1) -> 1.0 *m
  Go math.Mod                              case [0] (-90,360) -> -90.0 !
  Go math.Mod                              case [1] (-1e-20,360) -> -1e-20 !
  Go math.Mod                              case [3] (-0.5,2) -> -0.5 !
  Go math.Mod                              case [9] (-5e-324,1) -> -5e-324 !
  Go math.Remainder                        case [0] (-90,360) -> -90.0 !
  Go math.Remainder                        case [1] (-1e-20,360) -> -1e-20 !
  Go math.Remainder                        case [2] (5.5,2) -> -0.5 !
  Go math.Remainder                        case [3] (-0.5,2) -> -0.5 !
  Go math.Remainder                        case [9] (-5e-324,1) -> -5e-324 !
  Go formula                               case [1] (-1e-20,360) -> 360.0 *m
  Go formula                               case [9] (-5e-324,1) -> 1.0 *m
  Go formula                               case [10] (1,5e-324) -> -inf !
  Go formula                               case [11] (0.75,1.5e-323) -> -inf !
  Java %                                   case [0] (-90,360) -> -90.0 !
  Java %                                   case [1] (-1e-20,360) -> -1e-20 !
  Java %                                   case [3] (-0.5,2) -> -0.5 !
  Java %                                   case [9] (-5e-324,1) -> -5e-324 !
  Java Math.IEEEremainder                  case [0] (-90,360) -> -90.0 !
  Java Math.IEEEremainder                  case [1] (-1e-20,360) -> -1e-20 !
  Java Math.IEEEremainder                  case [2] (5.5,2) -> -0.5 !
  Java Math.IEEEremainder                  case [3] (-0.5,2) -> -0.5 !
  Java Math.IEEEremainder                  case [9] (-5e-324,1) -> -5e-324 !
  Java StrictMath.IEEEremainder            case [0] (-90,360) -> -90.0 !
  Java StrictMath.IEEEremainder            case [1] (-1e-20,360) -> -1e-20 !
  Java StrictMath.IEEEremainder            case [2] (5.5,2) -> -0.5 !
  Java StrictMath.IEEEremainder            case [3] (-0.5,2) -> -0.5 !
  Java StrictMath.IEEEremainder            case [9] (-5e-324,1) -> -5e-324 !
  Java formula                             case [1] (-1e-20,360) -> 360.0 *m
  Java formula                             case [9] (-5e-324,1) -> 1.0 *m
  Java formula                             case [10] (1,5e-324) -> -inf !
  Java formula                             case [11] (0.75,1.5e-323) -> -inf !
  Java StrictMath.formula                  case [1] (-1e-20,360) -> 360.0 *m
  Java StrictMath.formula                  case [9] (-5e-324,1) -> 1.0 *m
  Java StrictMath.formula                  case [10] (1,5e-324) -> -inf !
  Java StrictMath.formula                  case [11] (0.75,1.5e-323) -> -inf !
  JS %                                     case [0] (-90,360) -> -90.0 !
  JS %                                     case [1] (-1e-20,360) -> -1e-20 !
  JS %                                     case [3] (-0.5,2) -> -0.5 !
  JS %                                     case [9] (-5e-324,1) -> -5e-324 !
  JS formula                               case [1] (-1e-20,360) -> 360.0 *m
  JS formula                               case [9] (-5e-324,1) -> 1.0 *m
  JS formula                               case [10] (1,5e-324) -> -inf !
  JS formula                               case [11] (0.75,1.5e-323) -> -inf !
  Ruby %                                   case [1] (-1e-20,360) -> 360.0 *m
  Ruby %                                   case [9] (-5e-324,1) -> 1.0 *m
  Ruby modulo                              case [1] (-1e-20,360) -> 360.0 *m
  Ruby modulo                              case [9] (-5e-324,1) -> 1.0 *m
  Ruby remainder                           case [0] (-90,360) -> -90.0 !
  Ruby remainder                           case [3] (-0.5,2) -> -0.5 !
  Ruby divmod                              case [1] (-1e-20,360) -> 360.0 *m
  Ruby divmod                              case [9] (-5e-324,1) -> 1.0 *m
  Ruby formula                             case [1] (-1e-20,360) -> 360.0 *m
  Ruby formula                             case [9] (-5e-324,1) -> 1.0 *m
  Ruby formula_float_floor                 case [1] (-1e-20,360) -> 360.0 *m
  Ruby formula_float_floor                 case [9] (-5e-324,1) -> 1.0 *m
  LuaJIT %                                 case [1] (-1e-20,360) -> 360.0 *m
  LuaJIT %                                 case [9] (-5e-324,1) -> 1.0 *m
  LuaJIT %                                 case [10] (1,5e-324) -> -inf !
  LuaJIT %                                 case [11] (0.75,1.5e-323) -> -inf !
  LuaJIT math.fmod                         case [0] (-90,360) -> -90.0 !
  LuaJIT math.fmod                         case [1] (-1e-20,360) -> -1e-20 !
  LuaJIT math.fmod                         case [3] (-0.5,2) -> -0.5 !
  LuaJIT math.fmod                         case [9] (-5e-324,1) -> -5e-324 !
  LuaJIT formula                           case [1] (-1e-20,360) -> 360.0 *m
  LuaJIT formula                           case [9] (-5e-324,1) -> 1.0 *m
  LuaJIT formula                           case [10] (1,5e-324) -> -inf !
  LuaJIT formula                           case [11] (0.75,1.5e-323) -> -inf !
  Lua5.3 %                                 case [1] (-1e-20,360) -> 360.0 *m
  Lua5.3 %                                 case [9] (-5e-324,1) -> 1.0 *m
  Lua5.3 math.fmod                         case [0] (-90,360) -> -90.0 !
  Lua5.3 math.fmod                         case [1] (-1e-20,360) -> -1e-20 !
  Lua5.3 math.fmod                         case [3] (-0.5,2) -> -0.5 !
  Lua5.3 math.fmod                         case [9] (-5e-324,1) -> -5e-324 !
  Lua5.3 formula                           case [1] (-1e-20,360) -> 360.0 *m
  Lua5.3 formula                           case [9] (-5e-324,1) -> 1.0 *m
  Lua5.3 formula                           case [10] (1,5e-324) -> -inf !
  Lua5.3 formula                           case [11] (0.75,1.5e-323) -> -inf !
  Perl POSIX::fmod                         case [0] (-90,360) -> -90.0 !
  Perl POSIX::fmod                         case [1] (-1e-20,360) -> -1e-20 !
  Perl POSIX::fmod                         case [3] (-0.5,2) -> -0.5 !
  Perl POSIX::fmod                         case [9] (-5e-324,1) -> -5e-324 !
  Perl POSIX::remainder                    case [0] (-90,360) -> -90.0 !
  Perl POSIX::remainder                    case [1] (-1e-20,360) -> -1e-20 !
  Perl POSIX::remainder                    case [2] (5.5,2) -> -0.5 !
  Perl POSIX::remainder                    case [3] (-0.5,2) -> -0.5 !
  Perl POSIX::remainder                    case [9] (-5e-324,1) -> -5e-324 !
  Perl formula                             case [1] (-1e-20,360) -> 360.0 *m
  Perl formula                             case [9] (-5e-324,1) -> 1.0 *m
  Perl formula                             case [10] (1,5e-324) -> -inf !
  Perl formula                             case [11] (0.75,1.5e-323) -> -inf !
  Haskell Data.Fixed.mod'                  case [1] (-1e-20,360) -> 360.0 *m
  Haskell Data.Fixed.mod'                  case [9] (-5e-324,1) -> 1.0 *m
  Haskell Data.Fixed.mod'                  case [10] (1,5e-324) -> -inf !
  Haskell Data.Fixed.mod'                  case [11] (0.75,1.5e-323) -> -inf !
  Haskell formula(floor::Integer)          case [1] (-1e-20,360) -> 360.0 *m
  Haskell formula(floor::Integer)          case [9] (-5e-324,1) -> 1.0 *m
  Haskell formula(floor::Integer)          case [10] (1,5e-324) -> -inf !
  Haskell formula(floor::Integer)          case [11] (0.75,1.5e-323) -> -inf !
  Haskell formula(floor::Int)              case [1] (-1e-20,360) -> 360.0 *m
  Haskell formula(floor::Int)              case [6] (1e300,3) -> 1e+300 !
  Haskell formula(floor::Int)              case [7] (-1e300,3) -> -1e+300 !
  Haskell formula(floor::Int)              case [9] (-5e-324,1) -> 1.0 *m
  Haskell formula(floor::Int)              case [10] (1,5e-324) -> 1.0 !
  Haskell formula(floor::Int)              case [11] (0.75,1.5e-323) -> 0.75 !
  Dart %                                   case [1] (-1e-20,360) -> 360.0 *m
  Dart %                                   case [9] (-5e-324,1) -> 1.0 *m
  Dart remainder                           case [0] (-90,360) -> -90.0 !
  Dart remainder                           case [1] (-1e-20,360) -> -1e-20 !
  Dart remainder                           case [3] (-0.5,2) -> -0.5 !
  Dart remainder                           case [9] (-5e-324,1) -> -5e-324 !
  Dart formula                             case [1] (-1e-20,360) -> 360.0 *m
  Dart formula                             case [9] (-5e-324,1) -> 1.0 *m
  Dart formula                             case [10] (1,5e-324) -> -inf !
  Dart formula                             case [11] (0.75,1.5e-323) -> -inf !
  Dart formula(floor() to int)             case [1] (-1e-20,360) -> 360.0 *m
  Dart formula(floor() to int)             case [6] (1e300,3) -> 1e+300 !
  Dart formula(floor() to int)             case [7] (-1e300,3) -> -1e+300 !
  Dart formula(floor() to int)             case [9] (-5e-324,1) -> 1.0 *m
  Tcl fmod                                 case [0] (-90,360) -> -90.0 !
  Tcl fmod                                 case [1] (-1e-20,360) -> -1e-20 !
  Tcl fmod                                 case [3] (-0.5,2) -> -0.5 !
  Tcl fmod                                 case [9] (-5e-324,1) -> -5e-324 !
  Tcl formula                              case [1] (-1e-20,360) -> 360.0 *m
  Tcl formula                              case [9] (-5e-324,1) -> 1.0 *m
  Tcl formula                              case [10] (1,5e-324) -> -inf !
  Tcl formula                              case [11] (0.75,1.5e-323) -> -inf !
  gawk %                                   case [0] (-90,360) -> -90.0 !
  gawk %                                   case [1] (-1e-20,360) -> -1e-20 !
  gawk %                                   case [3] (-0.5,2) -> -0.5 !
  gawk %                                   case [9] (-5e-324,1) -> -5e-324 !
  C f32.fmodf                              f32 case [0] (-1e-20f,360f) -> -1e-20!
  C f32.fmodf                              f32 case [1] (-90f,360f) -> -9e+01!
  C f32.fmodf                              f32 case [2] (-1e-7f,1f) -> -1e-07!
  C f32.remainderf                         f32 case [0] (-1e-20f,360f) -> -1e-20!
  C f32.remainderf                         f32 case [1] (-90f,360f) -> -9e+01!
  C f32.remainderf                         f32 case [2] (-1e-7f,1f) -> -1e-07!
  C f32.fmodf_then_plus_m_if_neg           f32 case [0] (-1e-20f,360f) -> 3.6e+02*m
  C f32.formula                            f32 case [0] (-1e-20f,360f) -> 3.6e+02*m
  Rust f32.%                               f32 case [0] (-1e-20f,360f) -> -1e-20!
  Rust f32.%                               f32 case [1] (-90f,360f) -> -90.0!
  Rust f32.%                               f32 case [2] (-1e-7f,1f) -> -1e-7!
  Rust f32.rem_euclid                      f32 case [0] (-1e-20f,360f) -> 360.0*m
  Rust f32.formula                         f32 case [0] (-1e-20f,360f) -> 360.0*m

SAME, FOR FINITE x AND m = +inf
  C fmod                                   case [15] (-1,inf) -> -1.0 !
  C remainder                              case [15] (-1,inf) -> -1.0 !
  C remquo                                 case [15] (-1,inf) -> -1.0 !
  C fmod_then_plus_m_if_neg                case [15] (-1,inf) -> inf *m
  Rust f64.%                               case [15] (-1,inf) -> -1.0 !
  Rust f64.rem_euclid                      case [15] (-1,inf) -> inf *m
  Python py.%                              case [15] (-1,inf) -> inf *m
  Python py.math.fmod                      case [15] (-1,inf) -> -1.0 !
  Python py.math.remainder                 case [15] (-1,inf) -> -1.0 !
  Python py.divmod                         case [15] (-1,inf) -> inf *m
  Python np.mod                            case [15] (-1,inf) -> inf *m
  Python np.fmod                           case [15] (-1,inf) -> -1.0 !
  Python np.remainder                      case [15] (-1,inf) -> inf *m
  Python np.divmod                         case [15] (-1,inf) -> inf *m
  Python np.mod_array                      case [15] (-1,inf) -> inf *m
  Go math.Mod                              case [15] (-1,inf) -> -1.0 !
  Go math.Remainder                        case [15] (-1,inf) -> -1.0 !
  Java %                                   case [15] (-1,inf) -> -1.0 !
  Java Math.IEEEremainder                  case [15] (-1,inf) -> -1.0 !
  Java StrictMath.IEEEremainder            case [15] (-1,inf) -> -1.0 !
  JS %                                     case [15] (-1,inf) -> -1.0 !
  Ruby %                                   case [15] (-1,inf) -> inf *m
  Ruby modulo                              case [15] (-1,inf) -> inf *m
  Ruby remainder                           case [15] (-1,inf) -> -1.0 !
  Ruby divmod                              case [15] (-1,inf) -> inf *m
  LuaJIT math.fmod                         case [15] (-1,inf) -> -1.0 !
  Lua5.3 %                                 case [15] (-1,inf) -> inf *m
  Lua5.3 math.fmod                         case [15] (-1,inf) -> -1.0 !
  Perl %                                   case [15] (-1,inf) -> inf *m
  Perl POSIX::fmod                         case [15] (-1,inf) -> -1.0 !
  Perl POSIX::remainder                    case [15] (-1,inf) -> -1.0 !
  Haskell Data.Fixed.mod'                  case [15] (-1,inf) -> inf *m
  Dart %                                   case [15] (-1,inf) -> inf *m
  Dart remainder                           case [15] (-1,inf) -> -1.0 !
  Tcl fmod                                 case [15] (-1,inf) -> -1.0 !
  gawk %                                   case [15] (-1,inf) -> -1.0 !

EXTRA MEASUREMENTS (perl_extra.pl/.out, ruby_extra.rb/.out)
1e300 % 3                    0
1e300 % 7                    1
-1e300 % 7                   6
18446744073709551615 % 7     1
-1 % inf                     Inf
5.5 % 1e20                   5.5
-5.5 % 1e20                  1e+20
-5.5 % 1e20 == 1e20          true
x=-1.0e-20 y=360.0  remainder=0.0  x-y*(x/y).truncate=-1.0e-20  x%y=360.0  owner=Numeric
x=-5.0e-324 y=1.0  remainder=0.0  x-y*(x/y).truncate=-5.0e-324  x%y=1.0  owner=Numeric
x=-90.0 y=360.0  remainder=-90.0  x-y*(x/y).truncate=-90.0  x%y=270.0  owner=Numeric
x=-1.0 y=Infinity  remainder=-1.0  x-y*(x/y).truncate=NaN  x%y=Infinity  owner=Numeric
```
