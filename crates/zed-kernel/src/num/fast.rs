//! Subquadratic arithmetic on wide integers: multiplication by number-theoretic transforms,
//! division by a Newton reciprocal, the binary recursive gcd of Stehlé and Zimmermann, and
//! decimal printing by halves. num-bigint 0.4.8's multiplication is Toom-3, about `n^1.46`; its
//! division above 64 words is Burnikel and Ziegler's recursion over that multiplication, and
//! its decimal printing is by halves over that division, both about `n^1.46` too; its gcd is
//! Stein's, O(n^2) (COMPLEXITY.md K30 and K41).
//!
//! `M(n)` below is the cost of a product of two `n`-bit numbers, O(n log n) here. Division
//! costs O(M(n)), and gcd and printing O(M(n) log n). Below a leaf size each operation hands
//! its operands to num-bigint, which is faster there; the value computed does not depend on
//! the leaf sizes.
//!
//! # The methods
//!
//! A number is a list of 64-bit words, the coefficients of a polynomial in `2^64`. The design
//! makes the product O(n log n) and builds division, gcd and printing from a bounded number of
//! products at each level of a recursion that halves the width.
//!
//! **Multiplication** ([`mul`], [`transform_mul`]). The product of two numbers is the
//! convolution of their word lists followed by carrying, O(n^2) done directly. A transform
//! turns the convolution into pointwise products: evaluate both polynomials at the `n`-th
//! roots of unity ([`Field::forward`], an FFT), multiply the values pairwise, interpolate back
//! ([`Field::inverse`]), O(n log n). The arithmetic is modulo a prime `p = c 2^50 + 1`, so roots
//! of unity of every order up to `2^50` exist and the values are exact; a coefficient of the
//! convolution can reach `n 2^128`, more than one 62-bit prime holds, so the convolution is
//! done modulo three primes ([`FIELDS`], product above `2^185`) and each coefficient rebuilt by
//! the Chinese remainder theorem in Garner's form, then the carries propagated, in one pass.
//! Products modulo `p` use Montgomery's form and Shoup's precomputed quotients for the
//! twiddle factors. The length is padded to a power of two, so the time rises in steps:
//! doubling the padded length doubles the time, and sizes between two powers cost the same. A
//! square needs one forward transform fewer. A factor with few nonzero words (as `2^s + 1`,
//! which the exact numbers keep) is multiplied by schoolbook over those words
//! ([`sparse_mul`]). Above [`MUL_LEAF`] words in the narrower factor, [`mul`] takes whichever of
//! three computed costs is lowest: rows over nonzero words, the transforms ([`transform_plan`])
//! and num-bigint's product ([`TOOM_COST`]); at or below it, num-bigint's.
//!
//! **Division** ([`div_rem`], [`Level`], [`approx_reciprocal`]). To divide by `d` of `n` bits
//! a quotient of `k <= n` bits, take the top `k` bits `t` of `d` and an approximate reciprocal
//! `X`, `t X < 2^2k <= t (X + 2)`, from Newton's iteration (Brent and Zimmermann, Modern
//! Computer Arithmetic, Algorithm 3.5): from a reciprocal of [`RECIP_LEAF`] bits by
//! num-bigint's division, each step goes from `h = ceil((p + 3) / 2)` bits to `p` with two
//! cyclic products of `p / 2` bits that share one factor's transforms ([`newton`]), so the
//! whole costs about 5/3 of a product of `k` bits. With `X` taken to `w = 64 ceil(k / 64)`
//! bits, the estimate `q0 = xh + floor(xh (X - 2^w) / 2^w)`, `xh` the dividend's bits above
//! the divisor's, is a product of `k` bits, at most four below the quotient (two above it when
//! `k < n`), and the remainder `x - q0 d`, in `(-2d, 5d)`, is a cyclic product of `d`'s width
//! modulo `2^(64 m) - 1` read back by its low word ([`unfold`]); at most four steps of `d`
//! correct both. A quotient wider than the divisor is found in blocks
//! of the divisor's width ([`div_rem_blocks`]) by one [`Divisor`], whose reciprocal and both
//! factors' transforms are built once: about one product of the divisor's width a block. A
//! divisor with few nonzero words is divided by long division over those words
//! ([`sparse_div_rem`]), chosen by computed cost as for products.
//!
//! **Gcd** ([`gcd`], [`half`], [`step`], [`half_leaf`]). Euclid's algorithm takes O(n) steps of
//! O(n) each. The half gcd avoids touching the full numbers at each step. It uses the binary
//! step: with `a` odd and `b = 2^j b'`, `b'` odd, choose `q`, `|q| < 2^j`, with `a + q b'`
//! divisible by `2^(j+1)` ([`inverse_mod_pow2`] gives `q`), and replace the pair by
//! `(b', (a + q b') / 2^j)`. This keeps the gcd's odd part ([`gcd`] divides each number by its
//! own power of two first and multiplies the result by the smaller power at the end), and is
//! the 2 by 2 integer matrix `[[0, 2^j], [2^j, q]]` over `2^2j` ([`Mat`]).
//! Because the steps work from the low end, the steps whose halvings total at most `k` depend
//! only on `a` and `b` modulo `2^(2k+1)`: no carry from the high bits reaches them, which is
//! why the binary form is used rather than the classical half gcd, which works from the high
//! end and must correct for carries. So [`half`] finds the matrix of the first half of the
//! steps from residues of half the width, applies it to the whole pair (a few products), takes
//! one step, and recurses on the second half: `T(n) = 2 T(n/2) + O(M(n))`, O(M(n) log n). The
//! recursion's leaf ([`half_leaf`], at or below [`HALF_LEAF`]) runs on 128-bit integers, which
//! the residues and matrix entries provably never exceed. [`gcd`] repeats one half gcd and one
//! step until the second number is zero, and hands what is left to num-bigint's Stein gcd at
//! or below [`GCD_LEAF`]. Reference: Stehlé and Zimmermann (2004) and Möller (2008), cited
//! in full under "Sources" below.
//!
//! **Printing** ([`to_decimal`], [`to_decimal_split`]). The powers `10^(L 2^i)`, `L` being
//! [`PRINT_LEAF`], are built once by squaring. `x` is written as `high 10^(L 2^i) + low` by one
//! division by the largest power at most `x`, and each half is printed by the next power down,
//! the low half padded with zeros to its fixed width. The largest power's reciprocal is found
//! by Newton's iteration to only the precision that division and the level below need; each
//! power below is a [`Level`] whose reciprocal is derived from the one above by one product and
//! one cyclic product ([`derive()`]), and whose reciprocal and power are transformed once for
//! all its divisions. A division at a level takes one product for the quotient and one cyclic
//! product of half its length for the remainder, which lies in `[0, 4d)` and so is found modulo
//! `2^(64 m) - 1`. Each level divides numbers of `n` bits in total, O(M(n)), over
//! `log2(n / L)` levels: O(M(n) log n). Parts below powers of [`PRINT_HANDOFF`] words, and
//! numbers of fewer than [`PRINT_WHOLE`] words, are printed by num-bigint.
//!
//! **Where the constants lose** (measured 2026-11-06 and, for products, 2026-11-07;
//! COMPLEXITY.md section "Crossovers"). A transform product costs three convolutions and the
//! recombination, so num-bigint's product is faster up to about 1024 words a factor, and
//! again just above each power of two of the transform's points, up to about 6144 words, where
//! the padding nearly doubles the transform's time. Division of `2w` by `w` words costs about
//! 4.1 squarings of `w` words from 16,384 to 131,072 words (KERNEL-div-newton, 2026-11-09; it
//! was 7.4 to 12.4 before), and takes 1.3 to 2.5 times num-bigint's Burnikel and Ziegler
//! division's time from 96 to 4096 words, the same at 8192 and 0.76, 0.59 and 0.46 times at
//! 16,384, 32,768 and 65,536 (load 15 to 17); printing, by the levels above, is slower than
//! num-bigint's below [`PRINT_WHOLE`] words, where its fixed costs (the powers, the levels'
//! transforms, one Newton reciprocal) outweigh num-bigint's `n^1.5` (COMPLEXITY.md K81).
//! The gcd gains from about 300 words, since num-bigint's is quadratic. Past [`DIV_LEAF`],
//! num-bigint's division is taken by a computed cost, [`DIV_COST`], as [`TOOM_COST`] is for
//! products (CROSSOVER-bench, 2026-11-12). Open for the port: a cheaper first reciprocal or
//! cached powers, which would lower the split's fixed costs and with them [`PRINT_WHOLE`].
//!
//! # Sources
//!
//! Each was checked on 2026-11-20: DOIs against Crossref, quotes against the text named.
//!
//! - D. Stehlé, P. Zimmermann, "A binary recursive gcd algorithm", Algorithmic Number Theory
//!   (ANTS 2004), Lecture Notes in Computer Science, Springer, pp. 411-425,
//!   doi:10.1007/978-3-540-24847-7_31. Lemma 1 (GB division): for `ν2(a) < ν2(b)` there is
//!   one `(q, r)` with `r = a + q b / 2^(ν2(b) - ν2(a))`, `|q| < 2^(ν2(b) - ν2(a))` and
//!   `ν2(r) > ν2(b)`; this is [`step`]. Lemma 7: if `a' = a mod 2^(2k+1)` and
//!   `b' = b mod 2^(2k+1)`, then up to the first remainder of valuation above `k` the GB
//!   quotients of the two pairs are equal; this is why [`half`] works on residues. Theorem 4:
//!   Fast-GB-gcd takes `O(M(n) log n)`. Departures: the pair is kept with its powers of two
//!   divided out, as in Möller's form below, and the leaf runs on 128-bit integers.
//! - N. Möller, "On Schönhage's algorithm and subquadratic integer gcd computation", Math.
//!   Comp. 77(261):589-607, 2008 (Crossref dates it 2007, online first),
//!   doi:10.1090/S0025-5718-07-02017-0. Section 4, p. 596, restates Stehlé and Zimmermann's
//!   algorithm as `hgcd-b`, whose step 7, `(A; B) <- (α, β) + 2^(ℓ1 - 2 j1) M (A'; B')`,
//!   lifts the residues' pair by the matrix applied to the high parts; [`half`]'s `lift` is
//!   that step. p. 595: "The use of quotients in the symmetric interval −2^k < q < 2^k is
//!   essential; if one tries to use positive quotients 0 < q < 2^(k+1), the algorithm no
//!   longer terminates."
//! - R. P. Brent, P. Zimmermann, Modern Computer Arithmetic, Cambridge University Press,
//!   2010, doi:10.1017/CBO9780511921698. Read in the authors' version 0.5.1 (November 26,
//!   2024), arXiv:1004.4710, whose numbering may differ from the printed book; checked again
//!   on 2026-11-20 (FIX-history-uses-attributions) against the text of the arXiv PDF: the
//!   quotes below are verbatim, Algorithm 3.5 and Lemma 3.4.2 are in §3.4.1 (p. 112), and
//!   Algorithms 1.25 FastIntegerInput and 1.26 FastIntegerOutput in §1.7.2 (pp. 42-43). This
//!   file's reciprocal and radix conversions are from this book, not from Brent's "An improved
//!   Monte Carlo factorization algorithm" (BIT 20, 1980), which an older sweep named for them.
//!   Algorithm 3.5 ApproximateReciprocal (§3.4.1) takes a reciprocal of the top `h` words and
//!   refines it by one Newton step; Lemma 3.4.2: "If β is a power of two satisfying β ≥ 8, and
//!   β^n/2 ≤ A < β^n, then the output X ... satisfies: AX < β^2n < A(X + 2)". Departure:
//!   [`approx_reciprocal`] works in bits (β = 2, outside the lemma's `β ≥ 8`) and starts each
//!   step from `h = ceil((p + 3) / 2)` bits, and it promises only `t (X + 2) > 2^2k`. The
//!   lemma's proof does not cover that case; [`newton`] proves one step in bits and
//!   [`approx_reciprocal`] the whole by induction over its sizes, at every width
//!   (PROOF-kernel-proofdoc3a-gaps (e)). The test `approximate_reciprocals_keep_their_bounds`
//!   checks the bound for every `t` of 5 to 13 bits and for edge and random `t` at 15 widths up
//!   to 30,001 bits. Algorithm 1.26
//!   FastIntegerOutput (§1.7.2) prints `A` as `Output(Q) || 0^(k - len(r)) || r` with
//!   `(Q, R) = DivRem(A, B^k)`, and "has complexity O(M(n) log n)"; [`to_decimal`] is that
//!   recursion, with the powers `10^(L 2^i)` fixed in advance and their reciprocals shared.
//!   Algorithm 1.25 FastIntegerInput (§1.7.2) joins the digit values in pairs, `ℓ ← [ℓ0 +
//!   bℓ1, ℓ2 + bℓ3, ...]`, then `(b, k) ← (b^2, ⌈k/2⌉)`, until one is left, and "has
//!   complexity O(M(n) log n)"; [`read_digits_by`] is that loop, over leaves of `leaf` digits
//!   rather than single digits.
//! - C. Burnikel, J. Ziegler, "Fast Recursive Division", research report MPI-I-98-1-022,
//!   Max-Planck-Institut für Informatik, October 1998,
//!   <https://pure.mpg.de/rest/items/item_1819444_4/component/file_2599480/content>: "Its
//!   running time is 2K(n) + O(n log n) for division of a 2n-digit number by an n-digit number
//!   where K(n) is the Karatsuba multiplication time." Not used here; it is num-bigint's
//!   division, against which this file is measured.
//! - A. Schönhage, "Schnelle Berechnung von Kettenbruchentwicklungen", Acta Inform.
//!   1(2):139-144, 1971, doi:10.1007/BF00289520. Its summary: a method of Knuth for the gcd
//!   and continued fraction "is modified in such a way that only O(n(lg n)^2(lglg n))
//!   elementary steps are used for u,v<2^n". Modern Computer Arithmetic §1.9 (Notes and
//!   References): "The first subquadratic gcd algorithm was published by Knuth ... The correct
//!   complexity O(n log^2 n log log n) was given by Schönhage". Cited for the gcd only; it is
//!   not a radix-conversion paper.
//! - D. J. Bernstein, "Scaled remainder trees", draft, 2004,
//!   <https://cr.yp.to/arith/scaledmod-20040820.pdf>. Abstract: U mod p1, U mod p2, ... can
//!   be computed "in time n(lg n)^(2+o(1))"; the paper's algorithm has a smaller o(1). Cited
//!   for radix conversion in O(M(n) log n): Modern Computer Arithmetic, Exercise 1.35, makes
//!   integer output as fast as input with "D. Bernstein's scaled remainder tree \[21\] and the
//!   middle product". This file does not use the scaled tree; it divides by Newton reciprocals.
//! - D. E. Knuth, The Art of Computer Programming, vol. 2, 3rd ed., Addison-Wesley, 1997,
//!   §4.3.1, Algorithm D (long division), no DOI. Read 2026-11-20 in a scanned copy of the
//!   3rd edition from LibGen, kept out of the repository and used only to check this entry:
//!   Algorithm D ("Division of nonnegative integers") begins on p. 272, beside Theorem B on
//!   the same page, which bounds the trial quotient digit, estimated from the leading digits,
//!   between the true digit and the true digit plus 2 once the divisor's leading digit is at
//!   least half the base; step D1 ("Normalize") scales both operands so that this holds.
//!   `sparse_div_rem` keeps the
//!   digit-at-a-time window of the algorithm but skips the divisor's zero words, a departure
//!   that the book does not describe.
//! - J. W. Cooley, J. W. Tukey, "An algorithm for the machine calculation of complex Fourier
//!   series", Math. Comp. 19(90):297-301, 1965, doi:10.1090/S0025-5718-1965-0178586-1
//!   (read: the radix-2 case, equations (14)-(20), and (22)): "The algorithm with r = 2 is
//!   derived by expressing the indices in the form" of their binary digits; each step (20)
//!   involves "only the two storage locations" whose indices differ in one bit, and the
//!   result comes out "in such an order that the index of an X must have its binary bits
//!   put in reverse order" (22). So a transform of `2^k` points is `k`
//!   stages of butterflies `(x + r y, x - r y)`, O(n log n) in all, in bit-reversed order.
//!   [`Field::forward`] does this over the integers modulo a prime in place of the complex
//!   numbers.
//! - P. L. Montgomery, "Modular multiplication without trial division", Math. Comp.
//!   44(170):519-521, 1985, doi:10.1090/S0025-5718-1985-0777282-X (read 2026-11-20, PDF,
//!   Sci-Hub, verification only; the AMS copy is behind a browser check). Section 1, p. 519:
//!   with `R R^-1 - N N' = 1`, "function REDC(T): m ← (T mod R) N' mod R; t ← (T + mN)/R; if
//!   t ≥ N then return t - N else return t", for `0 ≤ T < RN`, since then "0 ≤ t < 2N". Here
//!   `R = 2^64` and `N' = -N^-1 mod R`. [`Field::mul`] is REDC of `a b` with `neg_inv` as
//!   `N'`, ending with that subtraction; it departs by taking `a, b < 2p`, so `T < 4p^2`, which
//!   is below `RN = 2^64 p` because `4p < 2^64`, and the paper's bound still holds.
//! - D. Harvey, "Faster arithmetic for number-theoretic transforms", J. Symbolic Comput.
//!   60:113-119, 2014, doi:10.1016/j.jsc.2013.09.002 (Crossref and the text checked). Its
//!   Algorithm 3, the modified Shoup butterfly, takes `X, Y` in `[0, 2p)` and returns
//!   `X + Y` and `W (X - Y)` mod `p` in `[0, 2p)`, so "each element has two possible
//!   representations", saving reductions; its twiddle products use a precomputed quotient
//!   `W' = ⌊W β / p⌋` ([`Field::shoup`]), a method the paper says "is attributed to Shoup in
//!   Färnqvist (2005), but does not seem to have been published". Its Algorithm 4, the
//!   inverse butterfly, holds values in `[0, 4p)`. [`Field::forward`] takes values below `4p`
//!   and returns them below `2p`.
//! - H. L. Garner, "The residue number system", IRE Trans. Electronic Computers
//!   EC-8(2):140-147, 1959, doi:10.1109/TEC.1959.5219515 (read 2026-11-20, PDF, LibGen,
//!   verification only). P. 145, eqs. (28)-(36): the residue code is converted "to a
//!   nonconsistently based polynomial number representation by means of residue arithmetic",
//!   `S = a_t + m_t {d_t + m_(t-1) [d_(t-1) + ...]}` (35), each digit found from the ones
//!   before with "the multiplicative inverse of m_t with respect to base m_i" (29)-(30). In
//!   this file's terms: a number known by its residues modulo `p0, p1, p2` is
//!   `v0 + v1 p0 + v2 p0 p1`,
//!   each `v_i < p_i` found from the ones before by one product with a fixed inverse; this is
//!   [`garner`], with its constants in [`Garner`].
//! - J. Stein, "Computational problems associated with Racah algebra", J. Comput. Phys.
//!   1(3):397-405, 1967, doi:10.1016/0021-9991(67)90047-2 (Crossref and the text checked). Its
//!   gcd rests on "if a and b are odd integers and a > b, then GCD (a, b) = GCD(b, (a - b)/2)",
//!   with the difference shifted right until odd. [`stein_odd`] departs by taking up to 30 such
//!   halvings at a time from the low 128 bits as a 2 by 2 matrix, the 2-adic analog of
//!   Lehmer's method below, and applying it to the full words in one pass.
//! - D. H. Lehmer, "Euclid's algorithm for large numbers", Amer. Math. Monthly 45(4):227-233,
//!   1938, doi:10.1080/00029890.1938.11990797 (read 2026-11-20, PDF, LibGen, verification
//!   only). Pp. 228-229: "if (x0, x1) are replaced by approximate values (y0, y1), then the
//!   first few partial quotients of x0/x1 and y0/y1 will be the same"; from them a 2 by 2
//!   matrix of small numbers A, B is built, and "Thus far the calculation has involved only
//!   small numbers"; then (9)-(10) apply it to the large x0, x1 at once.
//!   Möller (above), §1.1, describes it: "Lehmer's algorithm computes the initial part of the
//!   quotient sequence using single or double precision arithmetic on the most significant
//!   words of the input, and applies several quotients at once to the multi-precision
//!   numbers." [`stein_odd`] uses that idea at the low end.
//! - A. L. Toom, "The complexity of a scheme of functional elements realizing the
//!   multiplication of integers", Soviet Math. Dokl. 3:714-716, 1963, and S. A. Cook, "On the
//!   minimum computation time of functions", PhD thesis, Harvard University, 1966. Neither has
//!   a DOI. Toom's Russian original, Dokl. Akad. Nauk SSSR 150(3):496-498, 1963, read
//!   2026-11-20, PDF, Math-Net.Ru (paper 27978); section 2, pp. 496-497 (translated here): the
//!   `n` bits of `N` are cut into `r + 1` parts `a_0..a_r` of `q` bits, `P(x) = Σ a_i x^i`, so
//!   `N = P(2^q)`; part I computes `P(i)` for every integer `-r <= i <= r`, part II squares
//!   these `2r + 1` values, part III, "knowing the values of the polynomial P^2(x) of degree
//!   2r at 2r + 1 points, computes its coefficients by the known formulas", part IV evaluates
//!   at `2^q`. Toom squares (a product follows from squares) and lets `r` grow with `n`, for
//!   a size below `n c^sqrt(log n)`. Cook's thesis, chapter III, "Positive results", section
//!   16, "The Toom algorithm for multiplication", pp. 51-53, read 2026-11-20 in the scans D. J.
//!   Bernstein keeps at <http://cr.yp.to/bib/1966/cook.html> (cook/01.jpg to 03.jpg; the pages
//!   carry no numbers, which are MCA's, below). Cook multiplies two numbers instead of
//!   squaring, "Toom's method (slightly modified)": "divide the expansions of m and n into
//!   r + 1 segments of q digits each", `P(x) = Σ α_k x^k` and `Q(x) = Σ β_k x^k` with
//!   `M = P(b^q)`, `N = Q(b^q)`; then "(16.4) m_k = P(k), n_k = Q(k), k = 0,1,...,2r", the
//!   products `m_k n_k` "by applying the general method all over again", and "(16.5) γ0 + γ1
//!   k + γ2 k^2 + ... + γ_2r k^2r = m_k n_k" is solved for the coefficients. Like Toom, Cook
//!   lets `r` grow, `r = 2^[sqrt(log q)]`, for `T(n) ≤ n 2^(5 sqrt(log n))` Turing machine
//!   steps. The cost at a fixed number of parts is stated in R. P. Brent and P. Zimmermann,
//!   "Modern Computer Arithmetic", version 0.5.1, arXiv:1004.4710, section 1.3.3, "Toom-Cook
//!   multiplication", p. 8 (read 2026-11-20, arXiv PDF): "Toom-Cook r-way reduces one n-word
//!   product to 2r − 1 products of about n/r words, thus costs O(n^ν) with ν = log(2r −
//!   1)/ log r", and "The case r = 3 is known as Toom-Cook 3-way"; its `r` counts parts, one
//!   more than Toom's and Cook's. So Toom-3 is three parts, five products of a third the size,
//!   `T(n) = 5 T(n/3) + O(n)`, which by the master theorem is `O(n^log3(5))`, `log3(5) =
//!   1.46497`. MCA's reference \[76\] gives the cr.yp.to URL and its notes put Toom-Cook in
//!   the thesis at "\[76, pp. 51–77\]". Departures: num-bigint's Toom-3 evaluates at 0, 1, -1,
//!   -2 and infinity (num-bigint 0.4.8 `src/biguint/multiplication.rs`, line 325, "w(t) at
//!   t = 0, 1, -1, -2 and inf", with an interpolation that "is given by Bodrato", line 380;
//!   read 2026-11-20), not at Cook's 0..2r, and stops its recursion at a fixed size; neither
//!   changes the exponent, which counts only the five products of a third the size. The
//!   search before the scans were found (2026-11-20, 16:41-16:56 UTC): OpenAlex, Unpaywall,
//!   CORE and dblp know only Cook and Aanderaa's 1969 paper (doi:10.2307/1995359); Harvard's
//!   catalog (record 990038153110203941) holds the thesis on paper and microfilm only; archive.org,
//!   LibGen, Google Scholar and Anna's Archive gave nothing. None of this code runs Toom's
//!   method; it is num-bigint's product, modeled by [`TOOM_COST`] and [`TOOM_POWER`], whose
//!   exponent the instruction counts there check (6.48 to 7.19 units per `l s^0.465` over 512
//!   to 24,576 words); a wrong exponent would show as a drift of that ratio with size, a
//!   wrong constant would not show except as a crossover moved from its measured place.
//!
//! Tests: `tests::products_agree_with_num_bigint` and
//! `tests::factor_products_agree_with_num_bigint` check the transform, REDC, the lazy reduction
//! and Garner's step together by comparing whole products with num-bigint's;
//! `tests::gcds_agree_with_num_bigint` checks [`gcd`], whose leaf is [`stein_odd`]. None checks
//! a bound on a residue between stages directly: a value that overflowed would show only as a
//! wrong product.
//!
//! **At the port to Zed.** The results must stay those of num-bigint's operations, which the
//! unit tests compare at every leaf setting. What depends on measurement and is to be measured
//! again on the Zed code: the leaves [`MUL_LEAF`], [`DIV_LEAF`], [`RECIP_LEAF`], [`GCD_LEAF`],
//! [`PRINT_HANDOFF`], [`PRINT_WHOLE`] and the cost constants [`TOOM_COST`], [`DIV_COST`],
//! [`TRANSFORM_COST`], [`WRAP_COST`], [`SPARSE_WORD`], [`SPARSE_RUN`], [`SPARSE_STEP`],
//! [`CACHED_COST`];
//! the benchmark `crossover all` (crate zed-benches) measures each against its crossover.
//! [`HALF_LEAF`] and [`PRINT_LEAF`] are derived, not measured. The Rust constructs that need
//! a Zed form are listed in ZED_PORT_GAPS.md, sections "Entries from NUM-subquad", "Entries from
//! BIGINT-fast-mul" and "Entries from NUM-print-fast".
//!
//! Each leaf is a crossover between two methods whose results are identical, set from timings
//! rather than solved from the two methods' cost formulas. The author accepted this for now
//! (2026-11-06) because nothing observable changes at a crossover, on the condition that each
//! is commented with the timings it rests on. The timings move with the load and the code: at
//! load 45 to 75 on 2026-11-05 multiplication and the gcd crossed at about 1024 and 512 words,
//! at load 1 on 2026-11-06 at about 4096 and 300. They are to be measured again when this file
//! is rewritten in Zed for self-hosting, by the procedure in COMPLEXITY.md section
//! "Crossovers", which also lists the curves on both sides of each leaf and what is not yet
//! understood about them. Where one method is never slower than the other, it is used alone,
//! with no crossover.

use std::borrow::Cow;
use std::rc::{Rc, Weak};

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};
use zed_numtheory::inverse_mod_2_64;

use super::TooLarge;
use crate::machine_int::BitLen;

/// The 64-bit words at or below which the narrower factor goes to num-bigint's
/// multiplication, the other methods' costs not computed. Measured on 2026-11-07 at load 34
/// to 41 (BIGINT-fast-mul), the transform took 1.74 times num-bigint's time at 256 by 256
/// words, 1.30 at 512 by 512, 1.16 at 256 by 65536 and 1.07 at 512 by 65536, slower at every
/// shape measured with the narrower at 512 words or fewer; above, [`TOOM_COST`] decides. It
/// was 1024 from 2026-11-05 (load 68), when the transform's constant was higher (COMPLEXITY.md,
/// "Crossovers"). Measured again on 2026-11-12 (RADIX-depth) in instructions, in the test
/// build, after the transform's constant fell to 7: at 512 by 512 words the transform takes
/// 1.24 million against num-bigint's 1.02, at 1024 by 1024 2.68 against 2.76, so the
/// instruction counts cross between, and 512 stood. Measured again on 2026-11-12
/// (CROSSOVER-bench, `crossover mul 32`, load 41 to 48) at 256 to 2048 by 32 times the
/// words, the shape where the transform gains soonest: num-bigint does less work up to 455
/// words (1.012 times the transform's instructions) and the transform from 460 (0.988), so
/// 459. Measured again on 2026-11-22 (RADIX-balanced-mul-regress), after [`WRAP_COST`] made
/// the transforms cheaper at these widths: `mul 4` crosses at 390 words and `mul 32` at 417
/// (num-bigint 1.005 times the transform's instructions at 413 by 13,216 words, 0.992 at
/// 417), and at 459 the transform was 1.038 times cheaper at 431 by 1724 words, so 400. The
/// product does not depend on it; the unit tests use a smaller leaf, so that they reach the
/// transforms at small sizes.
#[cfg(not(test))]
const MUL_LEAF: usize = 400;
#[cfg(test)]
const MUL_LEAF: usize = 48;

/// num-bigint 0.4.8's cost of a product of `s` by `l >= s` words, per `l s^0.465`, in the
/// units of [`TRANSFORM_COST`]. Its multiplication is Toom-3 above 256 words, `s^log3(5)` =
/// `s^1.465` for balanced factors, and cuts the longer factor in halves while it has twice
/// the other's words (`biguint/multiplication.rs` lines 102 to 166), so `l / s` such products.
/// It was 10.4 from times measured on 2026-11-07 (BIGINT-fast-mul). Measured again on
/// 2026-11-12 (RADIX-depth) in instructions, in the test build, over balanced factors of 512
/// to 24,576 words: 6.48 to 7.19 units per `l s^0.465`, 6.8 on average. With it and
/// [`TRANSFORM_COST`] the two methods' instruction counts cross where they are measured to:
/// num-bigint's product is taken at 768 by 768 words (1.80 million instructions against the
/// transform's 2.53) and the transform at 1024 by 1024 (2.68 against 2.76) and from 2048
/// (5.54 against 8.12). Between, the two are near: the transform is taken at 1280 by 1280
/// (3.99 against 3.92) and 1536 by 1536 (5.42 against 5.17), where the wrapped plan of
/// [`points`] is estimated within 1% of num-bigint's product. Fitted again on 2026-11-12
/// (CROSSOVER-bench) over `crossover mul 1`, `mul 4` and `mul 32` together, which alone ask
/// for 5.92 to 6.22, 5.64 to 5.69 and above 5.94: from 5.71 to 5.87 the most work any of them
/// does is the least, 1.047 times the less of the two methods', so 5.8; 6.8 did up to 1.17
/// times. Fitted again on 2026-11-22 (RADIX-balanced-mul-regress) with [`WRAP_COST`] 10 and
/// [`MUL_LEAF`] 400: `mul 1` asks for 6.34 to 7.81, `mul 4` for 6.80 or more and `mul 32` for
/// 6.33 to 6.42 alone, and at 7.0 each of the three takes the method of its measured
/// crossover at every size (exit status 0); at 5.8, `mul 4` took num-bigint's product at 431
/// to 512 by 4 times the words, up to 1.038 times the transform's work. The product does not
/// depend on it; the unit tests never take num-bigint's product above [`MUL_LEAF`], so that
/// they reach the transforms.
#[cfg(not(test))]
const TOOM_COST: f64 = 7.0;
#[cfg(test)]
const TOOM_COST: f64 = f64::INFINITY;

/// `log3(5) - 1`, the exponent of the narrower factor in [`TOOM_COST`]: Toom-3 makes five
/// products of a third the size, `T(n) = 5 T(n/3) + O(n) = O(n^log3(5))`, `log3(5) =
/// 1.46497` (R. P. Brent and P. Zimmermann, "Modern Computer Arithmetic", v0.5.1,
/// arXiv:1004.4710, section 1.3.3, p. 8, "O(n^ν) with ν = log(2r − 1)/ log r", `r = 3`
/// parts; with Toom 1963 and Cook's 1966 thesis, pp. 51-53, quoted with the sources in the
/// module doc, "Sources", all read 2026-11-20). The 0.465 is that value rounded, checked by
/// the measured units per `l s^0.465` above, which stay within 6.48 to 7.19 from 512 to
/// 24,576 words.
const TOOM_POWER: f64 = 0.465;

/// The bits at or below which the divisor goes to num-bigint's division, which then costs at
/// most this many bits times the dividend's, and at or below which a quotient by a wider
/// divisor goes to [`div_rem_short_quotient`], O(n) (plan row KERNEL-bz-short-quotient; before
/// it such a quotient went to num-bigint too); above both, [`DIV_COST`] decides.
/// The result does not depend on it. Not measured when it was set. On 2026-11-06 at load 1,
/// the Newton division then used took 1.13 times num-bigint's time at `w` = 64, 1.00 at 96,
/// 2.03 at 1024, 3.84 at 2048 and 2.60 at 8192 words, for `2w` by `w`. The division by
/// [`Level`] (KERNEL-div-newton) took, on 2026-11-09 at load 15 to 17, 1.31 times at 96, 2.54
/// at 1024, 1.88 at 2048, 1.36 at 4096, 1.02 at 8192, 0.76 at 16,384 and 0.46 at 65,536.
/// Measured in instructions on 2026-11-12 (CROSSOVER-bench, `crossover div-leaf`), num-bigint
/// does less work from 16 words up to 3192 words for `2w` by `w`, 919 for a quotient of a
/// quarter of the divisor's words, 899 for one of four times them, 417 for one of sixteen times
/// them and 242 for one of 256 times them, so the leaf on the narrower of the two alone cannot
/// sit at every crossover;
/// [`DIV_COST`] sets them, and this leaf only spares the cost computation on small divisions.
/// Measured again on 2026-11-23 (see [`DIV_COST`]): 3090, 861, 1480, 417 and 366 words; with
/// the reciprocal's cost on its [`Level`]'s points, 1779, 807, 1480, 417 and 366.
const DIV_LEAF: u64 = 64 * 64;

/// The cost of num-bigint's division past [`DIV_LEAF`], per unit of [`num_bigint_div_cost`], in
/// the units of [`TRANSFORM_COST`]. Fitted on 2026-11-12 (CROSSOVER-bench) over `crossover
/// div-leaf` for `2w` by `w` and for quotients of a quarter, four, sixteen and 256 times the
/// divisor's words together, which alone ask for 10.6 to 11.9, 10.4 to 10.5, 9.06 to 9.22,
/// 9.0 to 10.0 and 7.7 to 8.2: from 9.06 to 9.22 the most work any of them does is the least,
/// 1.089 times the less of the two methods', so 9.1. The work past the leaf depends on it
/// too, since a [`Divisor`] asks [`num_bigint_divides`] for its blocks, so it was fitted again
/// at 9.1, where the fit holds. With [`DIV_LEAF`] alone num-bigint's division did up to 3.4
/// times the work of the other methods. The quotient does not depend on it; infinite in the
/// unit tests, so that the other methods are reached past the leaf.
///
/// A scaling test whose two sizes fall on either side of this switch may read more than the
/// reciprocal's own growth without a fault of the order: where the switch sits at the
/// measured crossover, the work at `n` is the less of the two methods', `min(L(n), R(n))`
/// for num-bigint's `L` and the reciprocal's `R`, and at 8n past it is `R(8n)`, so the ratio
/// is `R(8n) / min(L(n), R(n)) >= R(8n) / R(n)`, larger only because the small size took the
/// faster method. That holds only where the switch is at the crossover, and the excess is the
/// switch's alone only where `R(8n) <= L(8n)`, so that the large size took the faster method
/// too: else part of it is the switch's error at 8n. Measured again in
/// instructions on 2026-11-23 (`crossover div-leaf`, under DynamoRIO's `zed_icount` on a Colab
/// VM, run h5-req30 on commit 25e53c9b5), num-bigint does less work up to 3090 words for `2w`
/// by `w`, 861 for a quotient of a quarter of the divisor's words, 1898 for twice, 1480 for
/// four times, 417 for sixteen times and 366 for 256 times them. Alone they ask for 11.73 to
/// 11.84, 11.41 to 11.47, 9.07 to 9.22, 9.04 to 9.19, 8.99 to 9.12 and 9.06 to 9.21. At 9.1
/// the four shapes of a quotient wider than the divisor sit at their crossovers, but the
/// build takes num-bigint for `2w` by `w` at 2048, 2896 and 5793 words (the reciprocal at
/// 4096 and from 8192), up to 1.329 times the less work, and for a quarter at 1448 words,
/// 1.123 times. Over the six together the least worst is 1.142, from 9.95 to 10.80. One
/// constant cannot fit both groups, so the shape terms of [`num_bigint_div_units`] were what
/// was off: refit as [`DIV_NARROW`] and [`DIV_SAME`] (plan row
/// PERF-div-narrow-quotient-factor, cross-review XR-ROOTS-REF round 2, D8), and the
/// reciprocal's cost of a quotient at most as wide as the divisor put on the points of its
/// [`Level`] ([`newton_cost`]), whose doubling past a power of two [`transform_cost`] did not
/// show. Measured with both on 2026-11-23 (`crossover div-leaf`, zed_icount, v5e3): the
/// crossovers are 1779 words for `2w - 1` by `w` (`1 1`, where num-bigint does less work
/// again from 2049 to 2773 words, the reciprocal's points having doubled, and the reciprocal
/// from 2803), 807 for a quarter, 1898, 1480, 417 and 366 for two, four, sixteen and 256
/// times; at 9.1 the build takes the method that does less work at every size of the six,
/// except 1760 words of `1 1` (1.0025 times the less) and 2803 to 2834 words of `1 1` (up
/// to 1.0228 times), and at 2048, 2049, 2896, 4096 and 5793 words with a quotient of 1 word
/// less, 1 more and 2 more than the divisor. Before, at 2049 words of `1 1` it took the
/// reciprocal at 1.527 times num-bigint's work. Where this matters:
/// `l01_39_reduced_product::roots::bench`, whose quotients are of both shapes (`TRANSFORM_BITS`
/// there), read 12.974 times the instructions at 8n from 131,072 to 1,048,576 bits with the
/// old search (h5-req23) and 11.197 after the Newton step at doubling precision (h5-req26),
/// with the quotients 8.40 times and the rest 4.55 times from 131,072 to 524,288 bits
/// (Callgrind, h5-req26), since both shapes were below their crossovers at n and past them at
/// 8n.
#[cfg(not(test))]
const DIV_COST: f64 = DIV_COST_FIT;
#[cfg(test)]
const DIV_COST: f64 = f64::INFINITY;

/// [`DIV_COST`] as fitted and built, which the unit tests of the switch read, since their
/// [`DIV_COST`] is infinite.
const DIV_COST_FIT: f64 = 9.1;

/// The exponent of num-bigint's division of `2w` by `w` words in `w`, measured: its work in
/// instructions grows 2.88, 2.90, 2.83 and 2.79 times for each doubling of `w` from 1024 to
/// 16,384 words (2026-11-12), `2^1.52 = 2.87`.
const DIV_POWER: f64 = 1.52;

/// The cost of each word of the divisor beyond the quotient's width in num-bigint's division of
/// a narrow quotient, per `q^(DIV_POWER - 1)` for a quotient of `q` words, over that of a
/// quotient word beyond the divisor's width per `n^(DIV_POWER - 1)`: measured, 0.45 for a
/// quotient of a quarter of the divisor at 512 to 4096 words (2026-11-12). Refit to 0.427 with
/// [`DIV_SAME`] (plan row PERF-div-narrow-quotient-factor, cross-review XR-ROOTS-REF round 2,
/// D8): the quarter's crossover of 2026-11-23, 861 words of quotient, asked for 11.41 to
/// 11.47 at the old form, 1.2538 to 1.2604 times 9.1 (middle 1.2571). Its units are `q^0.52
/// (q + DIV_NARROW 3q)`, so with the factor `DIV_SAME (1 + 3 DIV_NARROW) = 1.2571 (1 + 3
/// 0.45)`, `DIV_NARROW = 0.4271`. Kept with [`DIV_SAME`] 1.44: the quarter's crossover
/// is then 807 words, and at 9.1 the build takes the method that does less work at every size.
const DIV_NARROW: f64 = 0.427;

/// The factor on [`num_bigint_div_units`] for a quotient of at most one word more than the
/// divisor (`qw <= bw + 1`), where [`div_rem`] counts a quotient's words as `words(a) -
/// words(b) + 1`: a `2w` by `w` dividend of `2w` words has a quotient of `w + 1`, one of `2w
/// - 1` (`crossover div-leaf 1 1`) one of `w`. First 1.295, fitted to the crossover of `1 1`
/// of 2026-11-23 against [`newton_cost`] on [`transform_cost`]. Refit to 1.44 with
/// [`newton_cost`] on the points of its [`Level`] (plan row PERF-div-narrow-quotient-factor,
/// cross-review XR-ROOTS-REF round 2, D8), over 66 measured divisions of a quotient of at
/// most `bw + 1` words (`crossover div-leaf 1 1` and `1 4`, and `1 1` with 1 word less and 1
/// and 2 more at 2048, 2049, 2896, 4096 and 5793 words; zed_icount, 2026-11-23): from 1.4231
/// to 1.4571 times 9.1 the most work any of them does is the least, 1.030 times the less of
/// the two methods' (at a quotient of 2049 by 2048 words); 1.44 is near the middle. Measured
/// at 1.44 (see [`DIV_COST`]), the most is 1.0228, at 2834 words of `1 1`. The four
/// shapes of a quotient of two or more times the divisor keep the factor 1, where 9.1 alone
/// fits them. The step the factor makes at `qw = bw + 2` is the fit's: there num-bigint does
/// less work at all five sizes, and the build takes it. The cost only chooses a method, never
/// the quotient.
const DIV_SAME: f64 = 1.44;

/// The bits at or below which a reciprocal is found by num-bigint's division. It was 32 words,
/// not measured. Measured on 2026-11-12 (CROSSOVER-bench, `crossover recip`, load 41 to 48):
/// one division does less work up to 413 words (1.003 times a Newton step's instructions; 0.55
/// times at 32 words) and a Newton step from 417 (0.998), so 416 words. The reciprocal does
/// not depend on it; the unit tests use the least that Newton's step allows, 4 (a step to `p`
/// bits starts from `ceil((p + 3) / 2)`, fewer only for `p >= 5`), so that every step is
/// reached on small numbers.
#[cfg(not(test))]
const RECIP_LEAF: u64 = 64 * 416;
#[cfg(test)]
const RECIP_LEAF: u64 = 4;

/// The bits at or below which the gcd of what is left goes to num-bigint's gcd: near the
/// crossover measured on 2026-11-05, 2.2 ms against 1.7 ms at 256 words and 12 ms against
/// 30 ms at 1024 (load 75). Measured again on 2026-11-06 at load 1, the half gcd takes 1.20
/// times num-bigint's time at 256 words, 0.76 at 384, 0.78 at 512 and 0.50 at 1024, so the
/// curves cross near 300 words (COMPLEXITY.md, "Crossovers"). Measured in instructions on
/// 2026-11-12 (CROSSOVER-bench, `crossover gcd-leaf`): Stein's gcd does less work up to 297
/// words (1.002 times the half gcd's) and the half gcd from 300 (0.987), so 299 words, where
/// it was 512. Measured again on 2026-11-15 on the C library's heap, which `crossover` now
/// counts on (PERF-crossover-heap): Stein's gcd does less work up to 307 words (1.002) and the
/// half gcd from 311 (0.985; at 304 it did 1.011 times Stein's, against a spread of 1.0026), so
/// 310 words. The gcd does not depend on it;
/// the unit tests use a smaller leaf.
#[cfg(not(test))]
const GCD_LEAF: u64 = 64 * 310;
#[cfg(test)]
const GCD_LEAF: u64 = 64 * 16;

/// The valuation budget, in bits, at or below which [`half_low`] lifts the pair found from the
/// residues rather than applying the matrix to the whole numbers: matrix entries of at most
/// [`MUL_LEAF`] words (see [`half_low`]). The pair does not depend on it.
const LIFT_BITS: u64 = 64 * MUL_LEAF as u64;

/// The valuation budget at or below which the half gcd runs its steps on 128-bit integers:
/// residues of `2k + 1 <= 121` bits stay below `2^120`, and so do the matrix entries.
const HALF_LEAF: u64 = 60;

/// The digits of the narrowest power of ten [`to_decimal`] divides by, `10^597`: the most
/// digits whose power fits in 31 words (`597 log2(10) < 1984 = 31 * 64 < 598 log2(10)`), so
/// that `10^(L 2^i)` has at most `31 * 2^i` words and its cyclic product (see [`Level`]) is
/// on `32 * 2^i` points, a power of two with little padding. Derived, not measured.
const PRINT_LEAF: usize = 597;

/// The widest power of ten, in words, by which [`to_decimal`] hands a part to num-bigint rather
/// than split it further, so that the leaves are parts below `10^9552`. The setting has one
/// effect for each power's words, 31, 62, 124, 248, 496 and so on; the benchmark `crossover
/// print-handoff` (crate zed-benches) prints numbers of 160,000, 320,000 and 1,280,000 digits
/// with each, and 248 does the least work at all three: 159.4, 365.1 and 1784.8 million
/// instructions, against 162.0, 372.4 and 1820.1 million at 496 and 172.5, 389.8 and 1877.8
/// million splitting down to `10^597`; its bytes are 1.13 times the latter's and 0.91 times those
/// at 496 (2026-11-12, load 42 to 51; COMPLEXITY.md K81). The digits do not depend on it.
#[cfg(not(test))]
pub const PRINT_HANDOFF: usize = 248;
/// One in the unit tests, below every power's words, so that their small numbers reach the
/// transforms.
#[cfg(test)]
pub const PRINT_HANDOFF: usize = 1;

/// The fewest words of a number that [`to_decimal`] splits ([`to_decimal_split`]); a narrower
/// one is printed whole by num-bigint. The benchmark `crossover print-whole` (crate zed-benches)
/// times both on random numbers of 256 to 65,536 words. Below 496 words both run num-bigint.
/// From there the split divides: at 512 words once, by `10^9552` of 496 words, which costs
/// 0.977 times num-bigint's instructions; from 609 to 7803 words more, 1.57 times at 861
/// words and 1.005 at 7803; from 7845 words fewer at every size measured, 0.998 times there,
/// 0.87 at 8192 words, 0.70 at 16,384 and 0.43 at 65,536 (2026-11-12, load 36 to 51;
/// COMPLEXITY.md K81). It allocates fewer bytes from 2048 words on. The digits do not depend
/// on it.
#[cfg(not(test))]
pub const PRINT_WHOLE: usize = 7845;
/// One in the unit tests, so that every number reaches the split.
#[cfg(test)]
pub const PRINT_WHOLE: usize = 1;

/// The most bits of a number that the split writes as one leaf without building the powers,
/// for parts handed to num-bigint below powers of more than `handoff` words:
/// `floor(3.32 L) 2^i`, for `i` the least with `31 * 2^i > handoff` (31,712 bits, 496 words,
/// with [`PRINT_HANDOFF`] at 248; 1982 bits in the unit tests). The split divides a number
/// only by a power `10^(L 2^j)` of more than `handoff` words, and that power has at most
/// `31 * 2^j` words (see [`PRINT_LEAF`]), so `j >= i`; a number of at most these bits is below
/// `2^(3.32 L 2^i) < 10^(L 2^i)`, as `log2(10) > 3.32`, and is not split. Derived, not
/// measured, so the same leaves are printed with or without it: it only spares a leaf the
/// powers, built and then not divided by.
const fn leaf_bits(handoff: usize) -> u64 {
    let mut i = 0;
    while 31 << i <= handoff {
        i += 1;
    }
    (PRINT_LEAF as u64 * 332 / 100) << i
}

/// The cost of a transform product on `n` points, per `n log2(n)`, in units of one word
/// product of [`sparse_mul`]. Only which of two equal results is computed depends on it. It was
/// 12 from times measured on 2026-11-07 (BIGINT-fast-mul). Measured again on 2026-11-12
/// (RADIX-depth) in instructions, after the butterflies' reductions by a sign test, in the
/// test build: a word product of `sparse_mul` takes 16.42 instructions, and a balanced product
/// of `m` by `m` words on `n = 2m` points 7.37, 7.25, 6.86, 6.83, 6.54 and 6.53 units per
/// `n log2(n)` at `m` = 512, 1024, 2048, 4096, 8192 and 16,384: 7. Fitted on 2026-11-12
/// (CROSSOVER-bench, `crossover mul-rows`): rows and transforms cross at 199 nonzero words,
/// which 7.07 to 7.14 puts at the crossover, so 7.1.
const TRANSFORM_COST: f64 = 7.1;

/// The cost of a wrapped plan of [`points`] per point, besides its transforms and the top
/// words' product, in the units of [`TRANSFORM_COST`]: the subtraction of the top product
/// from the wrapped coefficients modulo each prime and the extra residues and carries, linear
/// in the points. Without it the wrap was taken where it costs more (RADIX-balanced-mul-regress):
/// on 2026-11-22, `crossover wrap 4096` measured the wrapped plan 1.3% to 1.4% dearer at 1411
/// to 1539 words, which it took up to 1678, and `wrap 8192` 2.5% to 5% dearer at 3110 to 3144
/// words, which it took up to 3213. Fitted by `crossover wrap 4096` and `wrap 8192` both: 4
/// still takes the wrap at 1539 words (1.27% dearer), 16 drops it at 2822 words (4.6% dearer),
/// and 8 to 12 put both at the crossover, so 10 (each value a rebuild: the constant is in
/// [`transform_cost`] too, at each depth). The fit the benchmark reports moves only the top
/// level's value, the depths below kept at 10: 14.2 to 16.3 for `wrap 4096` and up to 3.8 for
/// `wrap 8192`, so a model with one cost per point at every depth cannot match the top level
/// of both alone; at 10 both take the cheaper plan at every size off their crossover.
const WRAP_COST: f64 = 10.0;

/// The cost of a word of a step of [`sparse_div_rem`], and of a step besides its words (the
/// quotient word's estimate is a 128-bit division), in the units of [`TRANSFORM_COST`]:
/// measured on 2026-11-05, 2.3 ns a word, and set at 2. Fitted on 2026-11-12 (CROSSOVER-bench,
/// `crossover div-rows`) with [`SPARSE_STEP`] at 20: long division and the reciprocal cross at
/// 240 words, which 1.68 to 1.72 puts at the crossover, so 1.7. Kept at 1.7 when
/// [`SPARSE_STEP`] was fitted (2026-11-22, below): `div-rows` alone then puts it at 1.32 to
/// 1.34, but that pair does 1.33 times the less work on the sparse divisors. Refitted with
/// [`SPARSE_RUN`] (DIV-crossover-model, 2026-11-23): the dense divisors of `crossover div-rows`
/// (one run) cross at 374 to 378 words, where [`newton_cost`] is 598 a quotient word, so
/// `SPARSE_STEP + 378 SPARSE_WORD + SPARSE_RUN = 598` with the step at 45: 1.46. The timings
/// agree: 3.2 ns a word of a dense divisor of 1024 words, 8.5 ns a nonzero word of a sparse one.
const SPARSE_WORD: f64 = 1.46;
/// The cost of a run of consecutive nonzero words of the divisor in a step of
/// [`sparse_div_rem`], besides its words, in the units of [`TRANSFORM_COST`]: where a run
/// ends, the carry is subtracted by `sub_at` and the next word read from a scattered index, so
/// a divisor whose nonzero words lie apart costs more per word than a dense one (8.5 ns
/// against 3.2 ns on 2026-11-23). Without this term no pair ([`SPARSE_WORD`], [`SPARSE_STEP`])
/// met both kinds (MEASURE-sparse-step-fit). Fitted (DIV-crossover-model, 2026-11-23, std
/// Colab VM, processor time) from the crossovers of `crossover div-sparse 1024` at 126 nonzero
/// words (a run each), [`newton_cost`] 487 a quotient word, and `div-sparse 1024 16` at 40,
/// 185.5 a quotient word: `SPARSE_WORD + SPARSE_RUN = (487 - 185.5) / (126 - 40) = 3.51`, so
/// 3.51 - 1.46 = 2.05, and `SPARSE_STEP = 185.5 - 40 × 3.51 = 45`. The model then puts the
/// crossover of `div-sparse 2048` at 139 nonzero words (measured 126 to 128, where the two
/// methods' times differ by 0.5%) and of `div-sparse 256` at 100 (measured between 64 and
/// 128). Over the quotient's words the reciprocal measured 112, 128 and 135 times a sparse word
/// at 256, 1024 and 2048 words, and [`newton_cost`] gives 396, 487 and 532 units: one ratio,
/// 3.5 to 3.9, so `newton_cost` needs no change.
const SPARSE_RUN: f64 = 2.05;
/// The cost of a step of [`sparse_div_rem`] besides its words, in the units of
/// [`TRANSFORM_COST`] ([`SPARSE_WORD`]). It was 20 from the 2026-11-05 timings (NUM-subquad).
/// Fitted on 2026-11-22 (MEASURE-sparse-step-fit) by `crossover div-sparse w`, `2w - 1` by `w`
/// words of which 2 to `w` are nonzero, and `crossover div-rows step`, the dense divisors of
/// `div-rows`, with [`SPARSE_WORD`] at 1.7. Long division and the reciprocal cross near 200
/// nonzero words at every width (217 of 256, 193 of 1024, 201 of 2048, 242 dense), while
/// [`newton_cost`] over the quotient's words grows with the width, so each width alone fits a
/// different value (29 at 256, 160 at 1024, 192 at 2048, 7 to 14 dense) and no one value meets
/// all: 20 did 1.33 times the less work at 1024 words, between 189 and 362 nonzero; 98 to 106
/// do at most 1.11 times it on all four (1.110 at 1024, 1.069 at 2048, 1.067 at 256, 1.036
/// dense), so 100. Over (word, step) pairs, (1.3, 100) and (1.1, 170) also left 1.33. With at
/// most 64 nonzero words long division is taken and does the less work at every measured width
/// (2 to 8 nonzero words do 0.07 to 0.12 of the reciprocal's work at 256 words). Only choices
/// between methods with the same quotient and remainder read it, through [`sparse_div_cost`]:
/// long division or the reciprocal in [`div_rem_past_leaf`], num-bigint or
/// [`div_rem_past_leaf`] in [`num_bigint_divides`], and the blocks or not in
/// [`rem_takes_blocks`]; so a wrong value costs time and never an answer. `crossover div-leaf`
/// and `rem-leaf` gave the same counts with 20 and with 100. Refitted to 45 with
/// [`SPARSE_RUN`] (DIV-crossover-model, 2026-11-23, see there): the per-word cost that grew
/// with the width was the runs' cost, which a step constant could only average. The timings
/// agree: 73 to 100 ns a step besides its words, against 8.5 ns a sparse word.
const SPARSE_STEP: f64 = 45.0;

/// The number of 64-bit words of `x`.
fn words(x: &BigUint) -> usize {
    x.iter_u64_digits().len()
}

// ------------------------------------------------------------------------------------------
// Multiplication

/// A prime `c * 2^50 + 1` below `2^62`, for transforms of up to `2^50` points, with what
/// Montgomery multiplication modulo it needs.
struct Field {
    p: u64,
    /// `-p^-1 mod 2^64`.
    neg_inv: u64,
    /// `2^128 mod p`.
    r2: u64,
    /// A generator of the multiplicative group.
    root: u64,
}

impl Field {
    const fn new(p: u64, root: u64) -> Field {
        // Newton's iteration doubles the correct low bits of `p^-1`: 1, 2, 4, ..., 64.
        let mut inv = 1u64;
        let mut i = 0;
        while i < 6 {
            inv = inv.wrapping_mul(2u64.wrapping_sub(p.wrapping_mul(inv)));
            i += 1;
        }
        let r = (1u128 << 64) % p as u128;
        Field {
            p,
            neg_inv: inv.wrapping_neg(),
            r2: (r * r % p as u128) as u64,
            root,
        }
    }

    /// `a * b / 2^64 mod p`, reduced, for `a, b < 2p` (Montgomery): `a b + m p < 2^128` and its
    /// quotient by `2^64` is below `2p`, since `4p < 2^64`.
    #[inline]
    fn mul(&self, a: u64, b: u64) -> u64 {
        let t = u128::from(a) * u128::from(b);
        let m = (t as u64).wrapping_mul(self.neg_inv);
        let u = ((t + u128::from(m) * u128::from(self.p)) >> 64) as u64;
        below(u, self.p)
    }

    /// `x mod p` for any 64-bit `x`, without a division: with `q = floor(x / 2^62) <= 3`,
    /// `x - q p = (x mod 2^62) + q (2^62 - p)` lies in `[0, 2p)`, since each prime is above
    /// `2^62 - 2^57` (`2^62 + 3 * 2^57 < 2p`), and one subtraction finishes it.
    #[inline]
    fn reduce(&self, x: u64) -> u64 {
        let r = x - (x >> 62) * self.p;
        below(r, self.p)
    }

    #[inline]
    fn add(&self, a: u64, b: u64) -> u64 {
        let s = a + b;
        below(s, self.p)
    }

    #[inline]
    fn sub(&self, a: u64, b: u64) -> u64 {
        // `a - b` lies in `(-p, p)` for `a, b < p`; `a + p - b` in `(0, 2p)` is below `2^64`.
        below(a.wrapping_add(self.p).wrapping_sub(b), self.p)
    }

    /// `x * 2^64 mod p`, the Montgomery form of `x < p`.
    fn to_mont(&self, x: u64) -> u64 {
        self.mul(x, self.r2)
    }

    /// `x^e`, both in Montgomery form.
    fn pow(&self, mut x: u64, mut e: u64) -> u64 {
        let mut r = self.to_mont(1);
        while e > 0 {
            if e & 1 == 1 {
                r = self.mul(r, x);
            }
            x = self.mul(x, x);
            e >>= 1;
        }
        r
    }

    /// The roots of the stages of a transform on `n` points, a power of two, in bit-reversed
    /// order: entry `k < n/2` is `w^brv(k)`, `w` a primitive `n`-th root and `brv` the reversal
    /// of `log2(n) - 1` bits, each with its Shoup quotient (see [`Field::shoup`]). For
    /// `k < 2^s` that is `w_(2^(s+1))^brv_s(k)`, the root of block `k` of the stage with `2^s`
    /// blocks ([`Field::forward`]), so every stage reads a prefix of the table, one root a
    /// block, and the table of a larger power of two serves a smaller one. Built by doubling:
    /// `brv(2^s + i) = brv(i) + n/2^(s+2)`, so entries `2^s .. 2^(s+1)` are entries
    /// `0 .. 2^s` times `w_(2^(s+2))`. `n/2` pairs, as before, so a product's memory is
    /// unchanged.
    fn twiddles(&self, n: usize) -> Vec<(u64, u64)> {
        // `w_(2^t)` for `t` from 2 to `log2(n)`, in Montgomery form, by squaring down from a
        // primitive `n`-th root, the generator to the power `(p - 1) / n`.
        let mut step = Vec::with_capacity(n.trailing_zeros() as usize);
        let mut w = self.pow(self.to_mont(self.root), (self.p - 1) / n as u64);
        for _ in 2..=n.trailing_zeros() {
            step.push(w);
            w = self.mul(w, w);
        }
        // `mul(t, w)` of `t` in plain form and `w` in Montgomery form is `t w` in plain form.
        // The Shoup quotient `s = floor(t 2^64 / p)` is found without a division: with
        // `r = t 2^64 mod p` (`to_mont(t)`), `s p = t 2^64 - r` is exact, so
        // `s = -r p^-1 mod 2^64 = r neg_inv`, and `s < 2^64` since `t < p`.
        let mut tw = Vec::with_capacity(n / 2);
        tw.push((1, 0));
        // `step` holds `w_n, w_(n/2), ..., w_4`; doubling from 1 entry uses `w_4` first.
        for &r in step.iter().rev() {
            let have = tw.len();
            for i in 0..have {
                let t = self.mul(tw[i].0, r);
                tw.push((t, 0));
            }
        }
        for (t, s) in &mut tw {
            *s = self.to_mont(*t).wrapping_mul(self.neg_inv);
        }
        tw
    }

    /// `x w mod p`, in `[0, 2p)`, for any `x` and `w < p` with `s = floor(w 2^64 / p)`
    /// (Shoup): the quotient `x s / 2^64` is at most one below `x w / p`.
    #[inline]
    fn shoup(&self, x: u64, (w, s): (u64, u64)) -> u64 {
        let q = ((u128::from(x) * u128::from(s)) >> 64) as u64;
        x.wrapping_mul(w).wrapping_sub(q.wrapping_mul(self.p))
    }

    /// The transform of `a`, in place, `a.len()` a power of two: the evaluations at the
    /// powers of a primitive `a.len()`-th root, in bit-reversed order, by Cooley and Tukey's
    /// butterflies `(x + r y, x - r y)`, one root `r` a block ([`Field::twiddles`]), with `tw`
    /// from [`Field::twiddles`] of `a.len()` points or of any larger power of two. The entries
    /// from `filled` up are zero. Values below `4p` go in, and values below `2p` come out, the
    /// same residues (Harvey's lazy reduction: between stages every value is below
    /// `4p < 2^64`).
    ///
    /// A stage whose blocks' upper halves are all zero, as the first is for a factor padded to
    /// the points of a product, makes each block's upper half a copy of its lower half, so the
    /// leading stages of half `filled` or more are done at once by copying the first block.
    /// The other stages are done two at a time ([`Field::forward_pair`]), which loads and stores
    /// each value once for both, and an odd one left over at the end alone.
    fn forward(&self, a: &mut [u64], filled: usize, tw: &[(u64, u64)]) {
        let p2 = 2 * self.p;
        let n = a.len();
        debug_assert!(2 * tw.len() >= n, "a table of at least the points");
        debug_assert!(
            a[filled.min(n)..].iter().all(|&x| x == 0),
            "zeros from `filled` up"
        );
        let mut len = n / 2;
        while len > 0 && len >= filled {
            len /= 2;
        }
        let size = (2 * len).max(1);
        if size < n {
            let (first, rest) = a.split_at_mut(size);
            for block in rest.chunks_exact_mut(size) {
                block.copy_from_slice(first);
            }
        }
        let mut blocks = n / size;
        while len >= 2 {
            // Block `k` of the first stage of the two has root `tw[k]`; its two halves are
            // blocks `2k` and `2k + 1` of the second, with roots `tw[2k]` and `tw[2k + 1]`.
            // Index loops, not `zip`: the test build has no inlining across codegen units, so
            // `Zip::new` there is a call per block. With it, the larger run of
            // `reading_a_rat_of_two_wide_parts_scales` took 8349 M instructions; without, 7571 M
            // (that test is deferred to plan row RADIX-nlog2-10_5 in
            // wt/scratch/deferred-tests/RADIX-nlog2-10_5.rs).
            let first = &tw[..blocks];
            let second = tw[..2 * blocks].as_chunks::<2>().0;
            for k in 0..blocks {
                let block = &mut a[2 * len * k..2 * len * (k + 1)];
                let (wa, [wb, wc]) = (first[k], second[k]);
                match len == 2 {
                    true => self.forward_pair::<true>(block, wa, wb, wc),
                    false => self.forward_pair::<false>(block, wa, wb, wc),
                }
            }
            len /= 4;
            blocks *= 4;
        }
        if len == 1 {
            for (pair, &w) in a.as_chunks_mut::<2>().0.iter_mut().zip(&tw[..blocks]) {
                // As in [`Field::butterfly`], then each output brought below `2p` by one
                // subtraction.
                let (s, d) = self.butterfly(pair[0], pair[1], w);
                pair[0] = below(s, p2);
                pair[1] = below(d, p2);
            }
        }
    }

    /// Cooley and Tukey's butterfly `(x + w y, x - w y)` for `x, y < 4p`, each output below
    /// `4p`: `u = x mod 2p < 2p` and Shoup's `t = w y < 2p`, so `u + t < 4p` and `u + 2p - t`
    /// lies in `(0, 4p)`; `4p < 2^64`, so nothing wraps.
    #[inline]
    fn butterfly(&self, x: u64, y: u64, w: (u64, u64)) -> (u64, u64) {
        let p2 = 2 * self.p;
        let u = below(x, p2);
        let t = self.shoup(y, w);
        (u.wrapping_add(t), u.wrapping_add(p2).wrapping_sub(t))
    }

    /// Two stages of [`Field::forward`] on one block of the first, of `2 len` values, `len`
    /// at least 2: the first's butterflies of root `wa` across its halves, then the second's
    /// of roots `wb` and `wc` across each half's halves. With `LAST`, each output is brought
    /// below `2p`.
    #[inline]
    fn forward_pair<const LAST: bool>(
        &self,
        block: &mut [u64],
        wa: (u64, u64),
        wb: (u64, u64),
        wc: (u64, u64),
    ) {
        let p2 = 2 * self.p;
        let half = block.len() / 4;
        let (lo, hi) = block.split_at_mut(2 * half);
        let (q0, q1) = lo.split_at_mut(half);
        let (q2, q3) = hi.split_at_mut(half);
        let q3 = &mut q3[..half];
        // An index loop, not `zip`, as in [`Field::forward`].
        for i in 0..half {
            let (a0, a2) = self.butterfly(q0[i], q2[i], wa);
            let (a1, a3) = self.butterfly(q1[i], q3[i], wa);
            let (b0, b1) = self.butterfly(a0, a1, wb);
            let (b2, b3) = self.butterfly(a2, a3, wc);
            match LAST {
                // Each below `4p`, so one subtraction brings it below `2p`.
                true => {
                    q0[i] = below(b0, p2);
                    q1[i] = below(b1, p2);
                    q2[i] = below(b2, p2);
                    q3[i] = below(b3, p2);
                }
                false => (q0[i], q1[i], q2[i], q3[i]) = (b0, b1, b2, b3),
            }
        }
    }

    /// The inverse of [`Field::forward`] times `a.len()`, from bit-reversed order to natural
    /// order, by Gentleman and Sande's butterflies `(x + y, (x - y) / r)`, with `tw` as for
    /// [`Field::forward`]. The stage with `2^s` blocks undoes the forward stage with as many:
    /// block 0 has root 1, and for block `k` in `[2^t, 2^(t+1))`, `t < s`, `1/r` is
    /// `-tw[3 2^t - 1 - k]`. (With `r = w^b`, `w` of order `2^(s+1)`, `b = 2^(s-1-t) (2m + 1)`
    /// for `m = brv_t(k - 2^t)`, `1/r = w^(2^(s+1) - b) = -w^(2^s - b)`, and `2^s - b` is
    /// `2^(s-1-t) (2 (2^t - 1 - m) + 1)`, the exponent of entry `3 2^t - 1 - k`, since bit
    /// reversal commutes with complementing the bits.) So the blocks of group `t` read the
    /// table's entries `2^t .. 2^(t+1)` from the top down, and the sign goes into the
    /// difference: `(y - x) r'` for `r' = tw[3 2^t - 1 - k]`. The stages are done two at a
    /// time ([`Field::inverse_pair`]), an odd one left over at the end alone. Values below
    /// `2p` go in, and values below `p` come out.
    fn inverse(&self, a: &mut [u64], tw: &[(u64, u64)]) {
        let p = self.p;
        let n = a.len();
        debug_assert!(2 * tw.len() >= n, "a table of at least the points");
        let mut len = 1;
        while 4 * len <= n {
            let size = 4 * len;
            // Block 0: roots 1 and `1/tw[1]` in the first stage, 1 in the second.
            match size == n {
                true => self.inverse_pair::<true>(&mut a[..size], None, tw[1], None),
                false => self.inverse_pair::<false>(&mut a[..size], None, tw[1], None),
            }
            // Block `k` of group `t` (`2^t <= k < 2^(t+1)`): halves `2k` and `2k + 1` of
            // group `t + 1` read entries `3 2^(t+1) - 1 - 2k` and the one below it, a pair
            // of the table's entries `2^(t+1) .. 2^(t+2)` from the top down. Index loops, not
            // `zip`, as in [`Field::forward`].
            let mut group = 1;
            while group < n / size {
                let halves = tw[2 * group..4 * group].as_chunks::<2>().0;
                let whole = &tw[group..2 * group];
                for j in 0..group {
                    let k = group + j;
                    let [wb, wa] = halves[group - 1 - j];
                    let wc = whole[group - 1 - j];
                    let block = &mut a[size * k..size * (k + 1)];
                    self.inverse_pair::<false>(block, Some(wa), wb, Some(wc));
                }
                group *= 2;
            }
            len *= 4;
        }
        if len < n {
            // The last stage, one block of root 1, each output brought below `p`.
            let (lo, hi) = a.split_at_mut(len);
            for (x, y) in lo.iter_mut().zip(hi.iter_mut()) {
                let (s, d) = self.inverse_one(*x, *y);
                *x = below(s, p);
                *y = below(d, p);
            }
        } else if n == 1 && a[0] >= p {
            a[0] -= p;
        }
    }

    /// Gentleman and Sande's butterfly of root 1, `(x + y, x - y)`, for `x, y < 2p`: `x + y <
    /// 4p` and `x + 2p - y` in `(0, 4p)`, each brought below `2p` by one subtraction; `4p <
    /// 2^64`, so nothing wraps.
    #[inline]
    fn inverse_one(&self, x: u64, y: u64) -> (u64, u64) {
        let p2 = 2 * self.p;
        let (s, d) = (x.wrapping_add(y), x.wrapping_add(p2).wrapping_sub(y));
        (below(s, p2), below(d, p2))
    }

    /// Gentleman and Sande's butterfly `(x + y, (x - y) / r)` with `-1/r = w`, for `x, y <
    /// 2p`: `x + y < 4p`, brought below `2p` by one subtraction, and `(y + 2p - x) w`, Shoup's
    /// product of a value in `(0, 4p)`, below `2p`; `4p < 2^64`, so nothing wraps.
    #[inline]
    fn inverse_root(&self, x: u64, y: u64, w: (u64, u64)) -> (u64, u64) {
        let p2 = 2 * self.p;
        let s = x.wrapping_add(y);
        (
            below(s, p2),
            self.shoup(y.wrapping_add(p2).wrapping_sub(x), w),
        )
    }

    /// Two stages of [`Field::inverse`] on one block of the second, of `4 len` values: the
    /// first's butterflies across each half's halves, the lower half's with `-1/r = wa` (root
    /// 1 for `None`) and the upper's with `wb`, then the second's across the halves, with `wc`
    /// (root 1 for `None`). With `LAST`, each output is brought below `p`.
    #[inline]
    fn inverse_pair<const LAST: bool>(
        &self,
        block: &mut [u64],
        wa: Option<(u64, u64)>,
        wb: (u64, u64),
        wc: Option<(u64, u64)>,
    ) {
        let p = self.p;
        let half = block.len() / 4;
        let (lo, hi) = block.split_at_mut(2 * half);
        let (q0, q1) = lo.split_at_mut(half);
        let (q2, q3) = hi.split_at_mut(half);
        let q3 = &mut q3[..half];
        let pair = |x: u64, y: u64, w: Option<(u64, u64)>| match w {
            Some(w) => self.inverse_root(x, y, w),
            None => self.inverse_one(x, y),
        };
        // An index loop, not `zip`, as in [`Field::forward`].
        for i in 0..half {
            let (a0, a1) = pair(q0[i], q1[i], wa);
            let (a2, a3) = self.inverse_root(q2[i], q3[i], wb);
            let (b0, b2) = pair(a0, a2, wc);
            let (b1, b3) = pair(a1, a3, wc);
            match LAST {
                // Each below `2p`, so one subtraction brings it below `p`.
                true => {
                    q0[i] = below(b0, p);
                    q1[i] = below(b1, p);
                    q2[i] = below(b2, p);
                    q3[i] = below(b3, p);
                }
                false => (q0[i], q1[i], q2[i], q3[i]) = (b0, b1, b2, b3),
            }
        }
    }

    /// The coefficients of the product of the words of `a` from `sa` up and those of `b` from
    /// `sb` up (`b` is `None` for a square of `a`'s), `la + lb - 1` of them, each below `p`,
    /// with room for one more. `tw` as for [`Field::forward`], of at least the points used,
    /// and `fb` a buffer as for [`Field::convolve`].
    ///
    /// With `n` the power of two of points at or above the coefficients, `N = n / 2` and `r`
    /// the coefficients above `N`, the product is taken on `n` points, or, when the costs of
    /// [`transform_cost`] say it is cheaper, on `N`: the cyclic product modulo `x^N - 1` holds
    /// `c_t + c_(N+t)` at `t < r`, and the top `r` coefficients `c_(N+t)` are those of the
    /// product of the top `min(la, r)` and `min(lb, r)` words alone (a word `a_i` reaches
    /// `c_(N+t)` only with some `b_j`, `j <= lb - 1`, so `i >= N - lb + 1 = la - r`, and the
    /// same for `b`), found by this function on at most `2 r - 1` coefficients and subtracted.
    /// So no product pays for up to twice its points, as one just above a power of two did.
    fn linear(
        &self,
        a: &BigUint,
        sa: usize,
        b: Option<(&BigUint, usize)>,
        tw: &[(u64, u64)],
        fb: &mut Vec<u64>,
    ) -> Vec<u64> {
        let la = words(a) - sa;
        let lb = b.map_or(la, |(b, sb)| words(b) - sb);
        self.linear_on(a, sa, b, points(la, lb), tw, fb)
    }

    /// [`Field::linear`] on the points `n` and wrapped or not as `(n, wrap)` says, whatever
    /// [`points`] would choose; the top product, when wrapped, as [`points`] chooses. With
    /// `wrap`, `n` is half the power of two at or above the coefficients and each factor has
    /// at most `n` words; without, `n` is at or above the coefficients.
    fn linear_on(
        &self,
        a: &BigUint,
        sa: usize,
        b: Option<(&BigUint, usize)>,
        (n, wrap): (usize, bool),
        tw: &[(u64, u64)],
        fb: &mut Vec<u64>,
    ) -> Vec<u64> {
        let la = words(a) - sa;
        let lb = b.map_or(la, |(b, sb)| words(b) - sb);
        let coeffs = la + lb - 1;
        if !wrap {
            let mut v = self.convolve(a, sa, b, n, coeffs + 1, tw, fb);
            v.truncate(coeffs);
            return v;
        }
        let mut v = self.convolve(a, sa, b, n, coeffs + 1, tw, fb);
        let r = coeffs - n;
        let (ra, rb) = (la.min(r), lb.min(r));
        let top = b.map(|(b, sb)| (b, sb + lb - rb));
        let d = self.linear(a, sa + la - ra, top, tw, fb);
        // `d_k` is the coefficient at `la - ra + lb - rb + k = N + t` for
        // `k = t + ra + rb - 1 - r`, and `ra + rb >= r + 1` since both are at least 1 and one is
        // `r`.
        let high = &d[ra + rb - 1 - r..];
        debug_assert_eq!(high.len(), r, "the top `r` coefficients");
        for (x, &h) in v.iter_mut().zip(high) {
            *x = self.sub(*x, h);
        }
        // Within the capacity `coeffs + 1` asked of `convolve`.
        v.extend_from_slice(high);
        v
    }

    /// The cyclic convolution modulo `p` of the words of `a` from `sa` up and those of `b`
    /// from `sb` up (`b` is `None` for a square of `a`'s) on `n` points, each coefficient
    /// reduced below `p`, in a vector of capacity at least `room`; each has at most `n` words. `tw`
    /// as for [`Field::forward`]; `b`'s
    /// transform is written into `fb`, so that one buffer serves the three primes.
    #[allow(clippy::too_many_arguments)]
    fn convolve(
        &self,
        a: &BigUint,
        sa: usize,
        b: Option<(&BigUint, usize)>,
        n: usize,
        room: usize,
        tw: &[(u64, u64)],
        fb: &mut Vec<u64>,
    ) -> Vec<u64> {
        let load = |x: &BigUint, s: usize, v: &mut Vec<u64>| {
            v.clear();
            v.extend(x.iter_u64_digits().skip(s).map(|d| self.reduce(d)));
            let filled = v.len();
            debug_assert!(filled <= n, "at most `n` words");
            v.resize(n, 0);
            self.forward(v, filled, tw);
        };
        let mut fa = Vec::with_capacity(room.max(n));
        load(a, sa, &mut fa);
        // The pointwise product is `a b / 2^64`; the inverse multiplies by `n`; the scale
        // `2^128 / n`, in Montgomery form, undoes both.
        let n_inv = self.p - (self.p - 1) / n as u64;
        let scale = self.to_mont(self.to_mont(n_inv));
        match b {
            Some((b, sb)) => {
                load(b, sb, fb);
                for (x, y) in fa.iter_mut().zip(fb.iter()) {
                    *x = self.mul(self.mul(*x, *y), scale);
                }
            }
            None => {
                for x in fa.iter_mut() {
                    *x = self.mul(self.mul(*x, *x), scale);
                }
            }
        }
        self.inverse(&mut fa, tw);
        fa
    }

    /// The transform of the words `x` on `n >= x.len()` points, a power of two, each value
    /// multiplied by `2^64 / n` modulo `p` and below `p`: a factor transformed once for
    /// [`Field::cyclic`], which then needs one product a point, with `tw` as for
    /// [`Field::forward`].
    fn spectrum(&self, x: &[u64], n: usize, tw: &[(u64, u64)]) -> Vec<u64> {
        let mut v = Vec::with_capacity(n);
        v.extend(x.iter().map(|&d| self.reduce(d)));
        v.resize(n, 0);
        self.forward(&mut v, x.len(), tw);
        // As in [`Field::convolve`]: `2^128 / n` in Montgomery form, so that the pointwise
        // product `x s / 2^64` is `x y / n`, and the inverse's factor `n` cancels.
        let n_inv = self.p - (self.p - 1) / n as u64;
        let scale = self.to_mont(self.to_mont(n_inv));
        for y in &mut v {
            *y = self.mul(*y, scale);
        }
        v
    }

    /// The transform of the words of `x` on `n` points, a power of two, each value below `2p`,
    /// written into `v`, with `tw` as for [`Field::forward`]. Word `i` goes to point `i mod n`,
    /// added to those before it there: the transform of `x(z) mod (z^n - 1)`, which is `x`'s
    /// itself when `n` is at or above its words.
    fn transform_into(&self, x: &BigUint, n: usize, tw: &[(u64, u64)], v: &mut Vec<u64>) {
        v.clear();
        let mut digits = x.iter_u64_digits();
        v.extend(digits.by_ref().take(n).map(|d| self.reduce(d)));
        let filled = v.len();
        v.resize(n, 0);
        for (i, d) in digits.enumerate() {
            v[i % n] = self.add(v[i % n], self.reduce(d));
        }
        self.forward(v, filled, tw);
    }

    /// `x 2^128 / n` in Montgomery form for each `x` of `v`, each below `p`: as
    /// [`Field::spectrum`] scales a transform, so that the pointwise products are those of
    /// the cyclic product.
    fn scale(&self, v: &mut [u64], n: usize) {
        let n_inv = self.p - (self.p - 1) / n as u64;
        let scale = self.to_mont(self.to_mont(n_inv));
        for y in v {
            *y = self.mul(*y, scale);
        }
    }

    /// The cyclic convolution modulo `p` of the words `x` and the number whose
    /// [`Field::spectrum`] is `s`, on `s.len() >= x.len()` points, each coefficient below `p`.
    fn cyclic(&self, x: &[u64], s: &[u64], tw: &[(u64, u64)]) -> Vec<u64> {
        // Two words more than the points, for the carry [`Factor::mul`] appends.
        let mut v = Vec::with_capacity(s.len() + 2);
        v.extend(x.iter().map(|&d| self.reduce(d)));
        v.resize(s.len(), 0);
        self.forward(&mut v, x.len(), tw);
        for (a, b) in v.iter_mut().zip(s) {
            *a = self.mul(*a, *b);
        }
        self.inverse(&mut v, tw);
        v
    }
}

/// The constants of Garner's form of the Chinese remainder theorem over [`FIELDS`], computed
/// once at compile time (each product computed them before, by exponentiations whose u128
/// remainders took a fifth of a 64-word product's time).
struct Garner {
    /// `p0^-1 mod p1`, in Montgomery form modulo `p1`.
    inv01: u64,
    /// `(p0 p1)^-1 mod p2`, in Montgomery form modulo `p2`.
    inv012: u64,
    /// `p0 mod p2`, in Montgomery form modulo `p2`.
    p0_in_2: u64,
    /// `p0 p1`.
    p01: u128,
}

/// `x 2^64 mod p`, the Montgomery form, at compile time.
const fn mont_of(x: u64, p: u64) -> u64 {
    (((x as u128) << 64) % p as u128) as u64
}

const GARNER: Garner = {
    let [p0, p1, p2] = [FIELDS[0].p, FIELDS[1].p, FIELDS[2].p];
    let p01 = p0 as u128 * p1 as u128;
    Garner {
        inv01: mont_of(inv_mod(p0 % p1, p1), p1),
        inv012: mont_of(inv_mod((p01 % p2 as u128) as u64, p2), p2),
        p0_in_2: mont_of(p0 % p2, p2),
        p01,
    }
};

/// `x mod m` for `x < 2m`, `m < 2^63`, `x < 2^64`: `x - m` read as signed is negative exactly
/// when `x < m` (it is then at least `2^64 - m > 2^63`, and otherwise below `m < 2^63`), and a
/// test of the sign compiles to a subtraction and a conditional move, two instructions fewer
/// than a comparison with `m`.
#[inline]
fn below(x: u64, m: u64) -> u64 {
    let d = x.wrapping_sub(m);
    if (d as i64) < 0 { x } else { d }
}

/// Three primes `c * 2^50 + 1` with a generator each; their product exceeds `2^185`, above
/// every coefficient of a product of `2^50` words, `2^50 * 2^128`.
const FIELDS: [Field; 3] = [
    Field::new(4_601_552_919_265_804_289, 3),
    Field::new(4_546_383_823_830_515_713, 10),
    Field::new(4_522_739_925_786_820_609, 37),
];

/// The cost of a product by transforms whose coefficients number `coeffs`, in units of one
/// word product of [`sparse_mul`], as [`Field::linear`] takes it: `TRANSFORM_COST n log2(n)`
/// for `n` points, the constant measured (see [`TRANSFORM_COST`]), on the power of two of
/// points at or above the coefficients, or on half as many plus [`WRAP_COST`] per point and
/// the cost of the top coefficients' product when that is less (see [`points`]).
fn transform_cost(coeffs: usize) -> f64 {
    let (n, wrap) = points(coeffs.div_ceil(2), coeffs / 2 + 1);
    let top = match wrap {
        true => WRAP_COST * n as f64 + transform_cost(2 * (coeffs - n) - 1),
        false => 0.0,
    };
    TRANSFORM_COST * points_cost(n) as f64 + top
}

/// `n log2(n)`, at least `n`, the steps of a transform on `n` points.
fn points_cost(n: usize) -> u128 {
    let n = n as u128;
    n * u128::from(n.trailing_zeros().max(1))
}

/// The points of a product of `la` and `lb` words by [`Field::linear`], and whether it wraps
/// its top coefficients around: `n`, the power of two at or above the `la + lb - 1`
/// coefficients, or `n / 2` when that plus the product of the top words (the `r = la + lb -
/// 1 - n / 2` coefficients above `n / 2` need at most `min(la, r) + min(lb, r) - 1`) and
/// [`WRAP_COST`] per point costs less by [`transform_cost`]. The choice is the cheaper of two
/// computed costs, with no size constant. Both factors must fit in `n / 2` words to wrap: a
/// wider one would have to be folded by coefficients, and [`spectra`] folds by words.
fn points(la: usize, lb: usize) -> (usize, bool) {
    let n = (la + lb - 1).next_power_of_two();
    match wrap_flip(la, lb) {
        Some(flip) if WRAP_COST < flip => (n / 2, true),
        _ => (n, false),
    }
}

/// The value of [`WRAP_COST`] below which [`points`] wraps a product of `la` and `lb` words,
/// `None` where it cannot wrap. The wrap costs `TRANSFORM_COST points_cost(n / 2) + WRAP_COST
/// n / 2 + T` against `TRANSFORM_COST points_cost(n)`, `T` the top words' [`transform_cost`]
/// (which holds [`WRAP_COST`] as built at the depths below), so it is the cheaper exactly when
/// `WRAP_COST < (TRANSFORM_COST (points_cost(n) - points_cost(n / 2)) - T) / (n / 2)`.
fn wrap_flip(la: usize, lb: usize) -> Option<f64> {
    let coeffs = la + lb - 1;
    let n = coeffs.next_power_of_two();
    if coeffs <= 2 || n == coeffs || la.max(lb) > n / 2 {
        return None;
    }
    let r = coeffs - n / 2;
    let top = la.min(r) + lb.min(r) - 1;
    let saved = TRANSFORM_COST * (points_cost(n) - points_cost(n / 2)) as f64;
    Some((saved - transform_cost(top)) / (n / 2) as f64)
}

/// The cheapest way to multiply a factor of `short` words by one of `long >= short` words by
/// transforms, and its cost: the longer cut into pieces of the returned length, each
/// multiplied by the shorter on the next power of two of points above their coefficients.
/// The pieces tried are those whose coefficients just fit a power of two of points, one for
/// each power from the shorter's width to the whole product's, so no more points are wasted
/// to rounding up than in the product whole, and an unbalanced product costs
/// O((long / short) M(short)).
fn transform_plan(short: usize, long: usize) -> (f64, usize) {
    let mut best = (transform_cost(short + long - 1), long);
    let mut points = short.next_power_of_two();
    while points < short + long - 1 {
        let piece = points + 1 - short;
        let cost = long.div_ceil(piece) as f64 * transform_cost(points);
        if cost < best.0 {
            best = (cost, piece);
        }
        points *= 2;
    }
    best
}

/// The nonzero 64-bit words of `x`.
fn nonzero_words(x: &BigUint) -> usize {
    x.iter_u64_digits().filter(|&d| d != 0).count()
}

/// The nonzero 64-bit words of `x` and the runs of consecutive ones they form, the shape
/// [`sparse_div_cost`] reads. O(words(x)), as [`nonzero_words`].
fn nonzero_runs(x: &BigUint) -> (usize, usize) {
    let (mut nonzero, mut runs, mut last) = (0, 0, false);
    for d in x.iter_u64_digits() {
        let here = d != 0;
        nonzero += usize::from(here);
        runs += usize::from(here && !last);
        last = here;
    }
    (nonzero, runs)
}

/// `a * b`. When the narrower factor has at most `MUL_LEAF` (400) words, by num-bigint's
/// multiplication; above that, by whichever of three methods has the least computed cost:
/// num-bigint's (Toom-3, about `n^1.465`), rows over the nonzero words of one factor, or
/// transforms modulo three primes joined by the Chinese remainder theorem, O(n log n). Every
/// method gives the same product; only the time depends on the choice.
pub fn mul(a: &BigUint, b: &BigUint) -> BigUint {
    let method = mul_method(a, b);
    #[cfg(feature = "method-counts")]
    method_counts::note(
        "mul",
        a,
        b,
        match method {
            MulBy::NumBigint => "num-bigint",
            MulBy::Rows => "rows",
            MulBy::Pieces(_) => "transform",
        },
    );
    match method {
        MulBy::NumBigint => a * b,
        MulBy::Rows => sparse_mul(a, b),
        MulBy::Pieces(piece) => pieces_mul(a, b, piece),
    }
}

/// How [`mul`] multiplies two factors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MulBy {
    /// num-bigint's product.
    NumBigint,
    /// Rows over the nonzero words of one factor ([`sparse_mul`]).
    Rows,
    /// Transforms, the longer factor cut into pieces of this many words ([`pieces_mul`]).
    Pieces(usize),
}

/// The method [`mul`] takes for `a * b`.
fn mul_method(a: &BigUint, b: &BigUint) -> MulBy {
    let (la, lb) = (words(a), words(b));
    let (short, long) = (la.min(lb), la.max(lb));
    // Complexity tradeoff: two timed crossovers of algorithms with identical results, nothing
    // given up. A product whose narrower factor has at most `MUL_LEAF` words, and one above it
    // where `toom_cost` is the least of the three computed costs, is num-bigint's Toom-3, about
    // `n^1.465`, in place of the O(n log n) transforms, because num-bigint was measured faster
    // there (the timings, dates and loads are in the doc comments of `MUL_LEAF` and
    // `TOOM_COST`). Every method gives the same product (tests
    // `l01_17_value_representation::subquadratic::products_agree_with_num_bigint_across_the_crossovers`
    // and `tests::products_agree_with_num_bigint`, with the leaf and `TOOM_COST` set so the
    // transforms are reached at small sizes); the growth above the leaf is tested by
    // `a_dense_product_scales` (COMPLEXITY.md K82 and section "Crossovers", BIGINT-fast-mul).
    // A complete solution solves the crossings from the methods' cost formulas rather than
    // from timings; both constants are to be measured again at the Zed port (ZED_PORT_GAPS.md,
    // "Entries from BIGINT-fast-mul").
    if short <= MUL_LEAF {
        return MulBy::NumBigint;
    }
    // Complexity tradeoff: rows over the nonzero words cost `nonzero(a) words(b)` word
    // products, below the transforms' O(n log n) when a factor has few nonzero words, as a
    // kept power `2^s + 1` has; the cheaper of the two computed costs is taken, from the
    // operands' counts and the measured `TRANSFORM_COST`, with no size constant, and both give
    // the same product. A dense factor costs O(n) more for the count. Tested by
    // `a_sparse_product_scales` and `products_agree_with_num_bigint` (COMPLEXITY.md K30).
    let rows =
        (nonzero_words(a) as u128 * lb as u128).min(nonzero_words(b) as u128 * la as u128) as f64;
    let (cost, piece) = transform_plan(short, long);
    // The second crossover of the tradeoff above (`TOOM_COST`): num-bigint's product where its
    // computed cost is the least, which follows the transform's steps at each power of two of
    // its points.
    if toom_cost(short, long) <= rows.min(cost) {
        return MulBy::NumBigint;
    }
    if rows <= cost {
        return MulBy::Rows;
    }
    MulBy::Pieces(piece)
}

/// A factor `x` that multiplies many numbers of at most `other` words, with its spectra on
/// the points of such a product (see [`Field::spectrum`]) when that costs less than [`mul`]:
/// each product then transforms only the other factor and the result, two of the three
/// transforms of [`transform_mul`].
pub(crate) struct Factor {
    x: BigUint,
    other: usize,
    spectra: Option<([Vec<u64>; 3], Rc<Roots>)>,
}

impl Factor {
    /// `x`, for `uses` products with numbers of at most `other` words.
    pub(crate) fn new(x: BigUint, other: usize, uses: usize) -> Factor {
        let (points, _) = self::points(words(&x), other);
        // Complexity tradeoff: the spectra cost one of a product's three transforms, once, and
        // each product by them then costs `cached_cost` (the other two, measured as
        // `CACHED_COST`), so they are kept when the computed costs, in the units of
        // `TRANSFORM_COST`, say `uses` products by them cost less than by `mul`'s cheapest
        // method for dense factors; else `mul` alone, with no memory held. Both give the same
        // products. The one transform is costed as a whole product less the two
        // (`TRANSFORM_COST - CACHED_COST` per `n log2(n)`). It was a third of a product's cost
        // (`transform_cost / 3`), which disagrees with the measured constants: the two kept
        // transforms measure 4.2 of the 7.1 (`crossover cached`, `crossover mul-rows`,
        // CROSSOVER-bench, 2026-11-12), so the one left is 2.9, not 2.37. One use does the
        // three transforms of one product either way, a tie the rounding of the costs could
        // break either way, so it never keeps them. Kept, they hold three words a point, about
        // six of `x`'s words for each, for as long as the factor lives (COMPLEXITY.md C31,
        // RADIX-depth).
        let spectra = (uses > 1
            && uses as f64
                * (cached_total(points, words(&x), other) - dense_cost(words(&x), other))
                + (TRANSFORM_COST - CACHED_COST) * (points_cost(points) as f64)
                < 0.0)
            .then(|| {
                let tw = roots(points);
                (spectra(&x.to_u64_digits(), points, &tw), tw)
            });
        Factor { x, other, spectra }
    }

    /// `y * x`, for `y` of at most `other` words, by the spectra when they are kept and cost
    /// less than [`mul`] for `y`'s width; the product is the same.
    pub(crate) fn mul(&self, y: &BigUint) -> BigUint {
        let wy = words(y);
        match &self.spectra {
            Some((s, tw)) if self.takes_spectra(s[0].len(), wy) => self.spectra_mul(y, s, tw),
            _ => mul(y, &self.x),
        }
    }

    /// Whether a product by `y` of `wy` words takes spectra on `points` points: when `y` fits
    /// them and they cost less than [`mul`].
    fn takes_spectra(&self, points: usize, wy: usize) -> bool {
        let wx = words(&self.x);
        wy <= self.other && cached_total(points, wx, wy) < dense_cost(wy, wx)
    }

    /// `y * x` by the kept spectra `s` on the roots `tw`, for `y` of at most `other` words.
    fn spectra_mul(&self, y: &BigUint, s: &[Vec<u64>; 3], tw: &Roots) -> BigUint {
        let wy = words(y);
        // The cyclic product on the points, less the top coefficients above them, which
        // wrapped around, as in [`Field::linear`]; then the carry out of its top word
        // as in `transform_mul`.
        let wx = words(&self.x);
        let coeffs = wx + wy - 1;
        let n = s[0].len();
        let yw = y.to_u64_digits();
        let mut fb = Vec::new();
        let [mut r0, r1, r2] = [0, 1, 2].map(|k| {
            let mut v = FIELDS[k].cyclic(&yw, &s[k], &tw[k]);
            if coeffs > n {
                let r = coeffs - n;
                let (rx, ry) = (wx.min(r), wy.min(r));
                let top = Some((y, wy - ry));
                let d = FIELDS[k].linear(&self.x, wx - rx, top, &tw[k], &mut fb);
                let high = &d[rx + ry - 1 - r..];
                for (x, &h) in v.iter_mut().zip(high) {
                    *x = FIELDS[k].sub(*x, h);
                }
                v.extend_from_slice(high);
            }
            v
        });
        let carry = garner(&mut r0, &r1, &r2);
        drop((r1, r2));
        let mut out = r0;
        out.extend([carry as u64, (carry >> 64) as u64]);
        trim(&mut out);
        from_words(out)
    }

    /// The factor itself.
    pub(crate) fn value(&self) -> &BigUint {
        &self.x
    }
}

/// The cost of a product by a [`Factor`]'s spectra on `n` points, per `n log2(n)`, in the
/// units of [`TRANSFORM_COST`]: two of the three transforms of a product, so about two thirds
/// of it. It was 11 from cycles measured on 2026-11-12 (load 50). Measured again the same day
/// (RADIX-depth) in instructions, in the test build: 4.89, 4.82, 4.57, 4.54, 4.35, 4.35 and
/// 4.15 units per `n log2(n)` at 1024 to 65,536 points: 5. Fitted on 2026-11-12 (CROSSOVER-bench,
/// `crossover cached`): the products by spectra and by plain transforms cross at 602 words,
/// which 4.17 to 4.22 puts at the crossover, so 4.2. Only which of two equal products is
/// computed depends on it; the unit tests use the same value.
#[cfg(not(test))]
const CACHED_COST: f64 = 4.2;
#[cfg(test)]
const CACHED_COST: f64 = 4.2;

/// The cost of a product of `wx` and `wy` words by spectra on `points` points: the cached
/// product, plus, when the coefficients pass the points, the product of the top words that
/// wrapped (see [`Field::linear`]).
fn cached_total(points: usize, wx: usize, wy: usize) -> f64 {
    let coeffs = wx + wy - 1;
    let top = match coeffs > points {
        true => {
            let r = coeffs - points;
            transform_cost(wx.min(r) + wy.min(r) - 1)
        }
        false => 0.0,
    };
    cached_cost(points) + top
}

/// The cost of a product by a [`Factor`]'s spectra on `points` points, in the units of
/// [`TRANSFORM_COST`]: [`CACHED_COST`] `n log2(n)` for `n` points.
fn cached_cost(points: usize) -> f64 {
    let n = points.next_power_of_two() as u128;
    CACHED_COST * (n * u128::from(n.trailing_zeros().max(1))) as f64
}

/// The cost [`mul`] computes for its cheapest method on dense factors of `a` and `b` words,
/// in the units of [`TRANSFORM_COST`]: zero at or below [`MUL_LEAF`], where num-bigint's
/// product is taken with no cost computed, so that no other method is taken there.
fn dense_cost(a: usize, b: usize) -> f64 {
    let (short, long) = (a.min(b), a.max(b));
    match short <= MUL_LEAF {
        true => 0.0,
        false => toom_cost(short, long).min(transform_plan(short, long).0),
    }
}

/// The cost [`mul`] is estimated to take on dense factors of `a` and `b` 64-bit words, in the
/// units of [`TRANSFORM_COST`] (one word product): num-bigint's product at or below
/// [`MUL_LEAF`], `a b` word products or [`toom_cost`], whichever is less; above it the less of
/// [`toom_cost`] and the transforms' [`transform_plan`], as [`mul_method`] chooses. Rows over
/// nonzero words are not counted, so a factor with many zero words costs less than this.
/// Infinite when the product's words do not fit in a `usize` with room to round up.
pub(crate) fn mul_cost(a: usize, b: usize) -> f64 {
    // Complexity tradeoff: `O(log)` in the sizes, as `transform_plan`; counting the rows over
    // nonzero words would read the factors, `O(L)`. It would not mend `crossover poly-wide 8`
    // (POLY-mul-cost-gaps, 2026-11-22): there the dense product took up to 1.50 times the
    // sparse one's time where it was estimated cheaper, and fewer counted words only lower its
    // estimate. A packed integer with terms of both signs has about half its words nonzero
    // (`poly::pack` writes `pos - neg`, so a borrow fills the gap after each term of the other
    // sign), and rows over them cost more than `toom_cost`. The error is `toom_cost` below
    // `MUL_LEAF`, fitted from 512 words: at 372 words num-bigint's Toom-3 took about 1.6 times
    // the time per estimated unit of the 23-word long multiplications it was weighed against.
    let (short, long) = (a.min(b).max(1), a.max(b).max(1));
    if long > usize::MAX / 4 {
        return f64::INFINITY;
    }
    let toom = toom_cost(short, long);
    match short <= MUL_LEAF {
        true => (short as f64 * long as f64).min(toom),
        false => toom.min(transform_plan(short, long).0),
    }
}

/// Whether [`mul`] squares a number of `n` 64-bit words, every one nonzero, by transforms whole
/// ([`transform_mul`]), as [`mul_method`] chooses for `a * a`: such a square takes one forward
/// transform fewer than a product of two numbers, which [`mul_cost`] does not count. num-bigint's
/// product and the rows over nonzero words square no faster than they multiply. `O(log n)`, as
/// [`transform_plan`].
pub(crate) fn squares_by_transform(n: usize) -> bool {
    // Past `usize::MAX / 4` words the product's length does not fit, as in [`mul_cost`].
    if n <= MUL_LEAF || n > usize::MAX / 4 {
        return false;
    }
    let (cost, piece) = transform_plan(n, n);
    toom_cost(n, n) > cost && n as f64 * n as f64 > cost && piece >= n
}

/// num-bigint's cost of a product of `short <= long` words, `TOOM_COST long short^0.465`, in
/// the units of [`TRANSFORM_COST`].
fn toom_cost(short: usize, long: usize) -> f64 {
    TOOM_COST * long as f64 * (short as f64).powf(TOOM_POWER)
}

/// `a * b` by transforms, the longer factor cut into pieces of `piece` words (whole when it
/// has no more), as [`transform_plan`] chose.
fn pieces_mul(a: &BigUint, b: &BigUint, piece: usize) -> BigUint {
    let (la, lb) = (words(a), words(b));
    let (short, long) = match la <= lb {
        true => (a, b),
        false => (b, a),
    };
    if piece >= words(long) {
        return transform_mul(a, b);
    }
    // Complexity tradeoff: a product is cut into pieces when that costs less by
    // `transform_plan`, which also bounds its memory by that of the pieces' transforms; a
    // square so cut loses its single transform, which the plan does not count, so it may cost
    // up to a third more than whole. Tested by `products_agree_with_num_bigint`
    // (COMPLEXITY.md K30).
    let mut out = vec![0u64; la + lb];
    let mut digits = long.iter_u64_digits();
    let mut at = 0;
    while digits.len() > 0 {
        let part = from_words(digits.by_ref().take(piece).collect());
        let p = transform_mul(short, &part);
        drop(part);
        let mut slots = out[at..].iter_mut();
        let mut carry = false;
        for d in p.iter_u64_digits() {
            // Unreachable: `p = short * part` has at most `words(short) + words(part)` words,
            // and `out[at..]` has `la + lb - at` of them, with `words(part) <= la - at`.
            let slot = slots.next().expect("the product fits in its words");
            let (v, c1) = slot.overflowing_add(d);
            let (v, c2) = v.overflowing_add(u64::from(carry));
            *slot = v;
            carry = c1 || c2;
        }
        for slot in slots {
            if !carry {
                break;
            }
            (*slot, carry) = slot.overflowing_add(1);
        }
        at += piece;
    }
    from_words(out)
}

/// `a * b` by transforms modulo three primes joined by the Chinese remainder theorem.
fn transform_mul(a: &BigUint, b: &BigUint) -> BigUint {
    let plan = points(words(a), words(b));
    transform_mul_on(a, b, plan, plan.0)
}

/// [`transform_mul`] on the points and plan `plan`, as [`Field::linear_on`] takes them, with
/// the roots of `table >= plan.0` points. [`transform_mul`] passes the points of the plan
/// [`points`] chose. When it wraps on `N = plan.0` points, every product inside (the top
/// words', at each depth) is on at most `N` points. Proof: [`points`] wraps only when
/// `C(N) + WRAP_COST N + T < C(2N)`, with `C(m) = TRANSFORM_COST points_cost(m)` and `T` the
/// top product's [`transform_cost`], so only when `T < C(2N)`. The top product has at most
/// `2N - 1` coefficients, so its
/// power of two of points is at most `2N`; were it `2N` unwrapped, `T` would be `C(2N)` and
/// the wrap would not be chosen; wrapped, it is on at most `N`. The same holds at each depth
/// below, whose `N` is at most this one. A wrap [`points`] did not choose
/// (`crossover::mul_on_points`) may put the top product on `2N` points.
fn transform_mul_on(a: &BigUint, b: &BigUint, plan: (usize, bool), table: usize) -> BigUint {
    // The product has `la + lb - 1` coefficients and `la + lb` words: the top word is the
    // last carry, pushed into the room [`Field::linear`] leaves.
    let n = plan.0;
    assert!(n <= 1 << 50, "a product of at most 2^50 words");
    let square = std::ptr::eq(a, b) || a == b;
    let other = (!square).then_some((b, 0));
    let tw = roots(table);
    // `b`'s transform for each prime in turn, in one buffer; the peak, during the last
    // transform, is four vectors of `n` words (two residues, `a`'s transform and `b`'s), and
    // the roots, kept by [`roots`] for later products.
    let mut fb = Vec::with_capacity(if square { 0 } else { n });
    let [mut r0, r1, r2] =
        [0, 1, 2].map(|k| FIELDS[k].linear_on(a, 0, other, plan, &tw[k], &mut fb));
    drop(fb);
    let carry = garner(&mut r0, &r1, &r2);
    debug_assert!(
        carry >> 64 == 0,
        "the product fits in the words of both factors"
    );
    drop((r1, r2));
    r0.push(carry as u64);
    from_words(r0)
}

/// The coefficients whose residues modulo the primes of [`FIELDS`] are `r0`, `r1` and `r2`,
/// each below its prime, joined by Garner's form of the Chinese remainder theorem and carried:
/// they are written over `r0` as words, and the carry out of the top is returned. `r1` and
/// `r2` have at least as many entries as `r0`.
fn garner(r0: &mut [u64], r1: &[u64], r2: &[u64]) -> u128 {
    let [f0, f1, f2] = &FIELDS;
    // Garner's form: c = v0 + v1 p0 + v2 p0 p1, each `v_i < p_i`, with the constants of
    // [`GARNER`].
    let Garner {
        inv01,
        inv012,
        p0_in_2,
        p01,
    } = GARNER;
    let (p01_lo, p01_hi) = (p01 as u64, (p01 >> 64) as u64);
    // Coefficient `i` is read before word `i` is written.
    let mut carry = 0u128;
    for i in 0..r0.len() {
        let v0 = r0[i];
        let v1 = f1.mul(f1.sub(r1[i], f1.reduce(v0)), inv01);
        let low = f2.add(f2.reduce(v0), f2.mul(v1, p0_in_2));
        let v2 = f2.mul(f2.sub(r2[i], low), inv012);
        // c = s + v2 p01_lo + v2 p01_hi 2^64, with s = v0 + v1 p0 < 2^125.
        let s = u128::from(v0) + u128::from(v1) * u128::from(f0.p);
        let s = s + u128::from(v2) * u128::from(p01_lo);
        let hi = (s >> 64) + u128::from(v2) * u128::from(p01_hi);
        let t = u128::from(s as u64) + (carry & u128::from(u64::MAX));
        r0[i] = t as u64;
        carry = hi + (carry >> 64) + (t >> 64);
    }
    carry
}

/// [`garner`] for coefficients that may be negative, each of absolute value below `P / 2`,
/// `P = p0 p1 p2`: the residue `v2 = c / (p0 p1)` of a coefficient `c` in `[0, P)` is taken
/// as `v2 - p2` when it is above `p2 / 2`, which gives `c - P`, the negative coefficient. With
/// `s = v0 + v1 p0 < p0 p1 < 2^125` and `|v2| < 2^62`, `s + v2 p01_lo` lies within `2^127`
/// and `v2 p01_hi` within `2^122`, and the carry stays within `2^123`. The words written over
/// `r0` and the carry returned are the sum's two's complement.
fn garner_signed(r0: &mut [u64], r1: &[u64], r2: &[u64]) -> i128 {
    let [f0, f1, f2] = &FIELDS;
    let Garner {
        inv01,
        inv012,
        p0_in_2,
        p01,
    } = GARNER;
    let (p01_lo, p01_hi) = (i128::from(p01 as u64), i128::from((p01 >> 64) as u64));
    let mut carry = 0i128;
    for i in 0..r0.len() {
        let v0 = r0[i];
        let v1 = f1.mul(f1.sub(r1[i], f1.reduce(v0)), inv01);
        let low = f2.add(f2.reduce(v0), f2.mul(v1, p0_in_2));
        let v2 = f2.mul(f2.sub(r2[i], low), inv012);
        let v2 = match v2 > f2.p / 2 {
            true => i128::from(v2) - i128::from(f2.p),
            false => i128::from(v2),
        };
        let s = u128::from(v0) + u128::from(v1) * u128::from(f0.p);
        let x = s as i128 + v2 * p01_lo;
        let t = u128::from(x as u64) + u128::from(carry as u64);
        r0[i] = t as u64;
        carry = (x >> 64) + v2 * p01_hi + (carry >> 64) + (t >> 64) as i128;
    }
    carry
}

/// The number whose two's complement is the words `w`, lowest first, followed by those of
/// `carry`.
fn signed_from_words(mut w: Vec<u64>, carry: i128) -> BigInt {
    w.extend([carry as u64, (carry >> 64) as u64]);
    if carry >= 0 {
        trim(&mut w);
        return BigInt::from_biguint(Sign::Plus, from_words(w));
    }
    // The magnitude is the two's complement: the words inverted, plus one.
    let mut one = true;
    for d in &mut w {
        (*d, one) = (!*d).overflowing_add(u64::from(one));
    }
    trim(&mut w);
    BigInt::from_biguint(Sign::Minus, from_words(w))
}

/// The number whose 64-bit words, lowest first, are `w`.
///
/// num-bigint takes only 32-bit digits, which it copies into its own vector, so the halves
/// go through a vector made and dropped here. A buffer kept for the thread would save that
/// allocation but stay live, as wide as the widest number made, after the operation ended,
/// counted against the memory limit (test
/// `a_wide_number_modulo_a_wide_one_answers_when_its_peak_is_given`).
fn from_words(w: Vec<u64>) -> BigUint {
    let halves: Vec<u32> = w
        .iter()
        .flat_map(|d| [*d as u32, (*d >> 32) as u32])
        .collect();
    drop(w);
    BigUint::new(halves)
}

/// `a * b` by schoolbook rows, one for each nonzero word of the factor with fewer, across
/// the other's words: O(nonzero(a) words(b)).
fn sparse_mul(a: &BigUint, b: &BigUint) -> BigUint {
    let (la, lb) = (words(a), words(b));
    let (rows, across) = match nonzero_words(a) * lb <= nonzero_words(b) * la {
        true => (a, b),
        false => (b, a),
    };
    let mut out = vec![0u64; la + lb];
    for (i, x) in rows.iter_u64_digits().enumerate().filter(|&(_, x)| x != 0) {
        let mut carry = 0u128;
        for (slot, y) in out[i..].iter_mut().zip(across.iter_u64_digits()) {
            let t = u128::from(x) * u128::from(y) + u128::from(*slot) + carry;
            *slot = t as u64;
            carry = t >> 64;
        }
        // The row's sum is below `2^(64 (i + words(across) + 1))`, so the carry stops in the
        // product.
        for slot in &mut out[i + words(across)..] {
            if carry == 0 {
                break;
            }
            let t = u128::from(*slot) + carry;
            *slot = t as u64;
            carry = t >> 64;
        }
    }
    from_words(out)
}

/// `x^-1 mod p` for a prime `p` and `x` not a multiple of it, by Fermat: `x^(p - 2)`.
const fn inv_mod(x: u64, p: u64) -> u64 {
    zed_numtheory::pow_mod(x, p - 2, p)
}

/// `a * b` of signed numbers, by [`mul`].
pub fn mul_int(a: &BigInt, b: &BigInt) -> BigInt {
    BigInt::from_biguint(a.sign() * b.sign(), mul(a.magnitude(), b.magnitude()))
}

/// `v0 * p1 + v1 * p0` over nonnegative integers. When both products are past [`MUL_LEAF`] and
/// transforming the four operands and taking one inverse transform costs less by [`TRANSFORM_COST`]
/// than two separate products, the sum is formed in the transform domain (five transforms in place
/// of six, one Garner pass, and no separate big-integer addition; D. J. Bernstein, "Fast
/// multiplication and its applications", in *Algorithmic Number Theory*, MSRI Publications 44,
/// Cambridge University Press, 2008, pp. 325-384,
/// <https://cr.yp.to/lineartime/multapps-20080515.pdf>, §11.7 p. 347 "FFT addition", checked
/// 2026-11-20 against the author's PDF; no DOI); otherwise
/// [`mul`] is called twice. Both give the same sum. Test:
/// `num::fast::tests::mul_add_pair_agrees_with_separate_products`.
pub(super) fn mul_add_pair(v0: &BigUint, p1: &BigUint, v1: &BigUint, p0: &BigUint) -> BigUint {
    if v0.is_zero() || p1.is_zero() {
        return mul(v1, p0);
    }
    if v1.is_zero() || p0.is_zero() {
        return mul(v0, p1);
    }
    let (w0, w1, w2, w3) = (words(v0), words(p1), words(v1), words(p0));
    if w0.min(w1) <= MUL_LEAF || w2.min(w3) <= MUL_LEAF {
        return mul(v0, p1) + mul(v1, p0);
    }
    let widest = (w0 + w1 - 1).max(w2 + w3 - 1);
    let n = widest.next_power_of_two();
    let separate = dense_cost(w0, w1) + dense_cost(w2, w3);
    // Four forward transforms and one inverse: 5/3 of one three-transform product.
    let shared = 5.0 * TRANSFORM_COST * points_cost(n) as f64 / 3.0;
    if n > (1 << 50) || shared >= separate {
        return mul(v0, p1) + mul(v1, p0);
    }
    let tw = roots(n);
    let mut fa = Vec::with_capacity(n);
    let mut fb = Vec::with_capacity(n);
    let mut fc = Vec::with_capacity(n);
    let mut fd = Vec::with_capacity(n);
    let [mut r0, r1, r2] = [0, 1, 2].map(|k| {
        let field = &FIELDS[k];
        field.transform_into(v0, n, &tw[k], &mut fa);
        field.transform_into(p1, n, &tw[k], &mut fb);
        field.transform_into(v1, n, &tw[k], &mut fc);
        field.transform_into(p0, n, &tw[k], &mut fd);
        let n_inv = field.p - (field.p - 1) / n as u64;
        let scale = field.to_mont(field.to_mont(n_inv));
        let mut acc = Vec::with_capacity(n + 2);
        for i in 0..n {
            let t0 = field.mul(fa[i], fb[i]);
            let t1 = field.mul(fc[i], fd[i]);
            acc.push(field.mul(field.add(t0, t1), scale));
        }
        field.inverse(&mut acc, &tw[k]);
        acc
    });
    drop((fa, fb, fc, fd));
    // Each product's coefficients are at most min(w_a, w_b) * 2^128 <= (n / 2) * 2^128, so their
    // sum is at most n * 2^128 <= 2^178 < p0 p1 p2 (> 2^185), exact under Garner's CRT.
    let carry = garner(&mut r0, &r1, &r2);
    drop((r1, r2));
    r0.extend([carry as u64, (carry >> 64) as u64]);
    trim(&mut r0);
    from_words(r0)
}

/// Keeps the thread-local NTT root table alive for the lifetime of the returned guard so a tree
/// traversal builds the table once.
pub(super) fn hold_roots() -> HoldRoots {
    HoldRoots::open()
}

/// An initial root value `S` in `[0, 2^f)` for a scaled remainder tree (D. J. Bernstein, "Scaled
/// remainder trees", 2004, Section 2), satisfying `|S / 2^f - u / p| < 1.5 / 2^f` for `0 <= u < p`
/// and `p >= 2`, `f >= bits(p) + 4`.
///
/// Below or at [`RECIP_LEAF`] bits, exact floor division `floor(u * 2^f / p)` has error
/// `< 1 / 2^f`.
/// Above [`RECIP_LEAF`], [`approx_reciprocal`] on `p' = p * 2^(k - n)` (`n = bits(p)`, `k = f + 2`)
/// gives `X` with `p' X < 2^(2k) <= p' (X + 2)`, so `0 < 2^(f + n + 2) / p - X <= 2`; then
/// `S = floor(u X / 2^(n + 2))` satisfies `0 <= S < 2^f` (as `u < p` implies `u X < 2^(f + n + 2)`)
/// and `0 <= u * 2^f / p - S < 2 u / 2^(n + 2) + 1 < 2 p / 2^(n + 2) + 1 < 1.5`.
pub(super) fn scaled_root(u: &BigUint, p: &BigUint, f: u64) -> BigUint {
    if u.is_zero() {
        return BigUint::zero();
    }
    debug_assert!(u < p && p.bits() >= 2 && f >= p.bits() + 4);
    if f <= 64 && u.bits() + f <= 128 && p.bits() <= 64 {
        let uv = u.iter_u64_digits().next().unwrap_or(0);
        let pv = p.iter_u64_digits().next().unwrap_or(1);
        return BigUint::from(((u128::from(uv) << f) / u128::from(pv)) as u64);
    }
    if f <= RECIP_LEAF {
        return (u << f) / p;
    }
    let n = p.bits();
    let k = f + 2;
    let p_shifted = p << (k - n);
    let m = cyclic_points(k);
    let tw = roots(m);
    let x = approx_reciprocal(&p_shifted, k, &tw, RECIP_LEAF);
    drop(p_shifted);
    mul(u, &x) >> (n + 2)
}

/// Precision `f` (in bits) and whether to step to children by Theorem 2.2 (cyclic NTT modulo
/// `2^(64 m) - 1` with the parent's spectrum shared across both children) rather than Theorem 2.1
/// (`mul` modulo `2^f`) for a scaled-remainder-tree node `v = a * b`, `a, b >= 2`, needing
/// `2^f >= 2^(bits(v) + guard)` and `f <= cap`.
///
/// Both methods satisfy Bernstein (2004) Theorems 2.1/2.2; the choice compares the existing cost
/// model's `(TRANSFORM_COST + CACHED_COST) * m log2(m)` (one shared forward transform plus two
/// cached cyclic products on `m` points) against `mul_cost(fw, words(a)) + mul_cost(fw, words(b))`.
pub(super) fn scaled_node_precision(
    v: &BigUint,
    a: &BigUint,
    b: &BigUint,
    guard: u64,
    cap: u64,
) -> (u64, bool) {
    let tight = v.bits() + guard;
    let fw = usize::try_from(tight.div_ceil(64)).expect("words fit in memory");
    let m = fw.next_power_of_two();
    let ntt_bits = 64u64.saturating_mul(m as u64);
    let wa = words(a);
    let wb = words(b);
    let can_ntt = m <= (1 << 50) && ntt_bits <= cap && wa.min(wb) > 0;
    if can_ntt {
        let ntt_cost = (TRANSFORM_COST + CACHED_COST) * points_cost(m) as f64;
        let mul_both = mul_cost(fw, wa) + mul_cost(fw, wb);
        if ntt_cost < mul_both {
            return (ntt_bits, true);
        }
    }
    (tight, false)
}

/// Rounded bit-window extraction: given `y` (whose low `f` bits are `Y = y mod 2^f`), returns
/// `R = round(Y / 2^(f - e)) mod 2^e` in `[0, 2^e)`, where `round` rounds half up (distance at
/// most `1/2` from `Y / 2^(f - e)`), for `e <= f`.
fn rounded_window_big(y: &BigUint, f: u64, e: u64) -> BigUint {
    if e == 0 {
        return BigUint::zero();
    }
    debug_assert!(e <= f);
    let shift = f - e;
    let round_up = shift > 0 && y.bit(shift - 1);
    let skip = (shift / 32) as usize;
    let bit_off = (shift % 32) as u32;
    let n32 = usize::try_from(e.div_ceil(32)).expect("words fit in memory");
    let mut digits = y.iter_u32_digits().skip(skip);
    let mut out = Vec::with_capacity(n32);
    if bit_off == 0 {
        out.extend(digits.take(n32));
    } else if let Some(mut lo) = digits.next() {
        for _ in 0..n32 {
            let hi = digits.next().unwrap_or(0);
            out.push((lo >> bit_off) | (hi << (32 - bit_off)));
            lo = hi;
        }
    }
    let rem_bits = (e % 32) as u32;
    if rem_bits != 0 && out.len() == n32 {
        out[n32 - 1] &= (1u32 << rem_bits) - 1;
    }
    if round_up {
        let mut carry = true;
        for d in &mut out {
            (*d, carry) = d.overflowing_add(1);
            if !carry {
                break;
            }
        }
        if carry {
            if out.len() < n32 {
                out.push(1);
            } else {
                out.clear();
            }
        }
        if rem_bits != 0 && out.len() == n32 && (out[n32 - 1] >> rem_bits) != 0 {
            out.clear();
        }
    }
    BigUint::new(out)
}

/// Same as [`rounded_window_big`] for `Y` held as 64-bit words `y` (in `[0, 2^f - 1]`).
fn rounded_window_words(y: &[u64], f: u64, e: u64) -> BigUint {
    if e == 0 {
        return BigUint::zero();
    }
    debug_assert!(e <= f);
    let shift = f - e;
    let round_up = if shift > 0 {
        let b = shift - 1;
        let idx = (b / 64) as usize;
        idx < y.len() && ((y[idx] >> (b % 64)) & 1) != 0
    } else {
        false
    };
    let mut out = shr_words(y, shift);
    let nwords = usize::try_from(e.div_ceil(64)).expect("words fit in memory");
    if out.len() > nwords {
        out.truncate(nwords);
    }
    let rem_bits = (e % 64) as u32;
    if rem_bits != 0 && out.len() == nwords {
        out[nwords - 1] &= (1u64 << rem_bits) - 1;
    }
    if round_up {
        increment(&mut out);
        if rem_bits == 0 {
            if out.len() > nwords {
                out.clear();
            }
        } else if out.len() == nwords && (out[nwords - 1] >> rem_bits) != 0 {
            out.clear();
        }
    }
    trim(&mut out);
    from_words(out)
}

/// One parent-to-two-children step of Bernstein's scaled remainder tree (D. J. Bernstein, "Scaled
/// remainder trees", draft 2004-08-20, <https://cr.yp.to/arith/scaledmod-20040820.pdf>, Theorems
/// 2.1 and 2.2, pp. 4-5; no DOI; checked 2026-11-20 against the extracted text of the author's
/// PDF): given `sv` in `[0, 2^f)` representing `(u / (a b)) mod 1` to `f` bits (`2^f >= 8 l a b`
/// for an `l`-level tree), returns `(sa, sb)` representing `(u / a) mod 1` to `ea <= f` bits
/// (`2^ea >= 8 l a`) and `(u / b) mod 1` to `eb <= f` bits (`2^eb >= 8 l b`).
///
/// Error-bound proof (Bernstein 2004, Theorem 2.2, p. 4, for child `P = a`, sibling `Q = b >= 2`):
/// let `Y` in `[0, 2^f - 1]` satisfy `Y == Q * sv (mod 2^f - 1)` (cyclic NTT via `cyclic_product`
/// and `add_around` on `m = f / 64` words with `sv`'s spectrum shared across both children), `Z`
/// be within `1/2` of `Y / 2^(f - e)`, and `R = Z mod 2^e`. Modulo `Z`:
///
/// - `|R / 2^e - Y / 2^f| <= 1 / 2^(e + 1) <= 1 / (16 l P)`;
/// - `|Y / 2^f - Y / (2^f - 1)| = Y / (2^f (2^f - 1)) <= 1 / 2^f <= 1 / (8 l P Q) <= 1 / (16 l P)`
///   (as `Q >= 2`);
/// - `Y / (2^f - 1) == Q * sv / (2^f - 1) (mod Z)`;
/// - `|Q * sv / (2^f - 1) - Q * sv / 2^f| = Q * sv / (2^f (2^f - 1)) <= Q / 2^f <= 1 / (8 l P)`.
///
/// Summing gives `dist(R / 2^e - Q * sv / 2^f, Z) <= (1/16 + 1/16 + 1/8) / (l P) = 1 / (4 l P)`.
/// For Theorem 2.1 (`!use_ntt`, `Y = (Q * sv) mod 2^f`), only the rounding term `1 / 2^(e + 1)
/// <= 1 / (16 l P) < 1 / (4 l P)` appears. Thus if parent error `< (l + i) / (4 l P Q)`, then
/// multiplying by `Q` gives `< (l + i) / (4 l P)` and adding `1 / (4 l P)` gives
/// `< (l + i + 1) / (4 l P)`.
///
/// Tests: `num::fast::tests::scaled_root_and_children_preserve_precision`,
/// `num::trees::tests::the_remainders_agree_with_one_division_a_leaf`,
/// `num::trees::tests::the_scaled_remainders_and_cofactors_agree_past_ntt_width`.
pub(super) fn scaled_children(
    sv: &BigUint,
    f: u64,
    use_ntt: bool,
    a: &BigUint,
    ea: u64,
    b: &BigUint,
    eb: u64,
) -> (BigUint, BigUint) {
    if sv.is_zero() {
        return (BigUint::zero(), BigUint::zero());
    }
    if use_ntt {
        debug_assert!(f.is_multiple_of(64));
        let m = (f / 64) as usize;
        debug_assert!(m.is_power_of_two());
        let tw = roots(m);
        let sv_w = sv.to_u64_digits();
        let sv_s = spectra(&sv_w, m, &tw);
        drop(sv_w);
        let step = |q: &BigUint, e: u64| {
            let qw = q.to_u64_digits();
            let (mut y, carry) = cyclic_product(&folded(&qw, m), &sv_s, &tw);
            add_around(&mut y, carry);
            rounded_window_words(&y, f, e)
        };
        return (step(b, ea), step(a, eb));
    }
    if !use_ntt && f <= 64 && a.bits() <= 64 && b.bits() <= 64 {
        let sv_u = sv.iter_u64_digits().next().unwrap_or(0);
        let au = a.iter_u64_digits().next().unwrap_or(0);
        let bu = b.iter_u64_digits().next().unwrap_or(0);
        let mask_f = u128::MAX >> (128 - f);
        let step_u64 = |q: u64, e: u64| -> BigUint {
            if e == 0 {
                return BigUint::zero();
            }
            let y = (u128::from(sv_u) * u128::from(q)) & mask_f;
            let shift = f - e;
            let round = u128::from(shift > 0 && ((y >> (shift - 1)) & 1) != 0);
            let mask_e = u128::MAX >> (128 - e);
            BigUint::from((((y >> shift) + round) & mask_e) as u64)
        };
        return (step_u64(bu, ea), step_u64(au, eb));
    }
    let sa = rounded_window_big(&mul(sv, b), f, ea);
    let sb = rounded_window_big(&mul(sv, a), f, eb);
    (sa, sb)
}

/// Leaf recovery for a scaled remainder tree: `round(m * s / 2^e)` (half up), wrapping `m` to
/// `0`, for `m >= 2` and `e >= 1`. Evaluates in `u128` registers when `m` and `s` fit in 64 bits.
pub(super) fn scaled_leaf_rem(m: &BigUint, s: &BigUint, e: u64) -> BigUint {
    if m.bits() < 2 || s.is_zero() {
        return BigUint::zero();
    }
    debug_assert!(e >= 1);
    if e <= 64 && m.bits() <= 64 && s.bits() <= 64 {
        let mv = m.iter_u64_digits().next().unwrap_or(0);
        let sv = s.iter_u64_digits().next().unwrap_or(0);
        let prod = u128::from(mv) * u128::from(sv);
        let round = (prod >> (e - 1)) & 1;
        let r = (prod >> e) + round;
        let r = if r == u128::from(mv) { 0 } else { r as u64 };
        return BigUint::from(r);
    }
    let r = rounded_div_pow2(&mul(m, s), e);
    if r == *m { BigUint::zero() } else { r }
}

/// `round(x / 2^e)` (half up) for nonnegative `x` and `e >= 1`.
fn rounded_div_pow2(x: &BigUint, e: u64) -> BigUint {
    debug_assert!(e >= 1);
    let round_up = x.bit(e - 1);
    let mut q = x >> e;
    if round_up {
        q += 1u32;
    }
    q
}

/// `b^e`, by squaring with [`mul`].
pub fn pow(b: &BigUint, mut e: u64) -> BigUint {
    let mut b = Cow::Borrowed(b);
    let mut r = BigUint::one();
    while e > 0 {
        if e & 1 == 1 {
            r = mul(&r, &b);
        }
        e >>= 1;
        if e > 0 {
            b = Cow::Owned(mul(&b, &b));
        }
    }
    r
}

// ------------------------------------------------------------------------------------------
// Division

/// `(a / b, a mod b)` for `b` not zero. A narrow divisor goes to num-bigint, a narrow quotient
/// by a wider divisor to [`div_rem_short_quotient`], and a quotient wider than the divisor
/// goes block by block ([`div_rem_blocks`]). Otherwise the
/// quotient, of `k` bits, is estimated from the reciprocal of the divisor's top `k` bits, at
/// most a few off, and the remainder, found by a cyclic product ([`Level::div_rem`]), corrects
/// it. O(M(n)): about four squarings of the quotient's width (4.0 at 4096 to 65,536 words,
/// 2026-11-09), and the same for `2w` by `w` words through [`div_rem_blocks`].
pub(crate) fn div_rem(a: &BigUint, b: &BigUint) -> (BigUint, BigUint) {
    assert!(!b.is_zero(), "a division by zero");
    if a < b {
        return (BigUint::zero(), a.clone());
    }
    let (m, n) = (a.bits(), b.bits());
    // The quotient has at most `k` bits.
    let k = m - n + 1;
    // Complexity tradeoff: a timed crossover with identical results, nothing given up. A
    // divisor of at most `DIV_LEAF` bits goes to num-bigint's division, Knuth's algorithm D,
    // which costs at most `DIV_LEAF` bits times the dividend's, O(n), and was measured faster
    // there. A quotient of at most `DIV_LEAF` bits by a wider divisor goes to
    // [`div_rem_short_quotient`], O(n): num-bigint 0.4.8 does not take algorithm D there but
    // Burnikel and Ziegler's division, by the counts of words alone (a dividend over 128 words
    // and a divisor over 64, `div_rem_core`, src/biguint/division.rs:343-346, read 2026-11-22),
    // whose recursion copies the divisor's halves at each level (:274-287), so its bytes grew
    // 10.7 times at 8n on `bench::a_short_quotient_of_a_wide_number_scales` (4,096 to 32,768
    // words, a quotient of 33 words; plan row KERNEL-bz-short-quotient). Past the leaf,
    // num-bigint's division is still taken where its computed cost
    // (`num_bigint_div_cost`, fitted to its measured work) is at most the cheaper of the other
    // two methods' (`past_leaf_cost`), as `mul` takes num-bigint's product by `TOOM_COST`.
    // num-bigint 0.4.8 divides by Knuth's algorithm D (The Art of Computer Programming, vol. 2,
    // 4.3.1) up to 64 words and above by Burnikel and Ziegler's recursive division (both cited
    // in full in the module's "Sources"), whose cost is that of its products, Toom-3,
    // O(n^1.465); its work was measured to grow 2.79 to 2.90 times per doubling of `2w` by
    // `w` (2026-11-12), so `DIV_POWER` 1.52, against about four squarings, O(n log n) each,
    // by the reciprocal. The plan row asked for one threshold at the measured crossover; the
    // curves cross at 3192 words for `2w` by `w`, 919 for a quotient of a quarter of the
    // divisor's words, 899 for four times, 417 for sixteen times and 242 for 256 times them
    // (2026-11-12, `crossover div-leaf`), so no one leaf sits at every crossover, and
    // `DIV_LEAF` alone at 64 words did up to 3.38 times the least work. With `DIV_COST`
    // fitted over the five shapes together the worst is 1.089 (COMPLEXITY.md, "Crossovers").
    // Both sides are tested by
    // `tests::quotients_agree_with_num_bigint` and
    // `tests::wide_quotients_agree_with_num_bigint`; the growth above it by
    // `dividing_a_wide_number_scales` (COMPLEXITY.md K30, "Crossovers"; ZED_PORT_GAPS.md,
    // "Entries from KERNEL-div-newton").
    if n > DIV_LEAF && k <= DIV_LEAF {
        #[cfg(feature = "method-counts")]
        method_counts::note("div", a, b, "short quotient");
        return div_rem_short_quotient(a, b);
    }
    if n.min(k) <= DIV_LEAF || num_bigint_divides(words(a) - words(b) + 1, b) {
        #[cfg(feature = "method-counts")]
        method_counts::note(
            "div",
            a,
            b,
            ["num-bigint", "leaf"][usize::from(n.min(k) <= DIV_LEAF)],
        );
        return a.div_rem(b);
    }
    #[cfg(feature = "method-counts")]
    {
        let qw = words(a) - words(b) + 1;
        let sparse = sparse_div_cost(qw, b) <= newton_cost(qw, words(b));
        method_counts::note("div", a, b, ["reciprocal", "sparse"][usize::from(sparse)]);
    }
    div_rem_past_leaf(a, b)
}

/// The calls of [`div_rem`] and [`mul`] by method and by the operands' words, under the
/// feature `method-counts` only, for the table of each level's backend at
/// `l01_39_reduced_product::roots::bench` (plan row DECISION-roots-bench-regime, cross-review
/// XR-ROOTS-REF round 2, D7). A feature and not `cfg(test)`: the benches are integration
/// tests, built against the library without `cfg(test)`, whose constants (`DIV_COST`
/// infinite) would pick other methods.
#[cfg(feature = "method-counts")]
pub mod method_counts {
    use num_bigint::BigUint;
    use std::cell::RefCell;
    use std::collections::BTreeMap;

    /// `(operation, method, words of the quotient or of the shorter factor, words of the
    /// divisor or of the longer factor)` to calls.
    pub type Counts = BTreeMap<(&'static str, &'static str, usize, usize), u64>;

    thread_local! {
        static COUNTS: RefCell<Counts> = const { RefCell::new(BTreeMap::new()) };
    }

    /// Counts one call of `op` on `a` and `b` by `method`.
    pub(super) fn note(op: &'static str, a: &BigUint, b: &BigUint, method: &'static str) {
        let (aw, bw) = (super::words(a), super::words(b));
        let key = match op {
            "div" => (op, method, aw - bw + 1, bw),
            _ => (op, method, aw.min(bw), aw.max(bw)),
        };
        COUNTS.with(|c| *c.borrow_mut().entry(key).or_insert(0) += 1);
    }

    /// The counts since the last call, which empties them.
    pub fn take() -> Counts {
        COUNTS.with(|c| std::mem::take(&mut *c.borrow_mut()))
    }
}

/// [`div_rem`] of a quotient of at most `DIV_LEAF` bits by a divisor of more: the quotient
/// from the top bits alone, then one product to correct it. With `k = bits(a) - bits(b) + 1`,
/// `t = max(0, bits(b) - k - 64)`, `a' = floor(a / 2^t)`, `b' = floor(b / 2^t)` and `q' =
/// floor(a' / b')`, the quotient `q = floor(a / b)` is `q'` or `q' - 1`.
///
/// Proof. Where `t = 0`, `q' = q`. Else `b'` has `k + 64` bits, `b' >= 2^(k + 63)`, and `q <
/// 2^k` gives `a < 2^k b < 2^k (b' + 1) 2^t`, so `a' < 2^k (b' + 1)`. Below: `a >= a' 2^t`
/// and `b < (b' + 1) 2^t`, so `a / b > a' / (b' + 1) = a' / b' - a' / (b' (b' + 1)) > a' / b' -
/// 2^k / b' >= a' / b' - 2^-63 > q' - 1`, and `q >= q' - 1`. Above: `a < (a' + 1) 2^t` and
/// `b >= b' 2^t`, so `a / b < (a' + 1) / b' <= q' + 1`, as `a' <= q' b' + b' - 1`, and `q <=
/// q'`. So `q' b > a` exactly where `q = q' - 1`.
///
/// Complexity tradeoff: num-bigint's division (Burnikel and Ziegler's past 64 words of
/// divisor, see [`div_rem`]) copies the divisor at each level of its recursion. Here the
/// division is of numbers of at most `2 DIV_LEAF + 65` bits, a constant, and the rest is one
/// product of at most `DIV_LEAF` bits by `n`, `O(n)` word products, and a subtraction: O(n)
/// work and bytes for `n` bits. The same leading-digit estimate as Knuth's algorithm D (The
/// Art of Computer Programming, vol. 2, 4.3.1), taken with 64 guard bits so that one
/// correction is enough. Tested by `tests::a_short_quotient_is_corrected_once` and
/// `tests::quotients_agree_with_num_bigint`; scaling by
/// `bench::a_short_quotient_of_a_wide_number_scales`.
fn div_rem_short_quotient(a: &BigUint, b: &BigUint) -> (BigUint, BigUint) {
    let k = a.bits() - b.bits() + 1;
    let t = b.bits().saturating_sub(k + 64);
    let q = (a >> t).div_rem(&(b >> t)).0;
    let p = mul(&q, b);
    match p > *a {
        true => (q - 1u32, a + b - p),
        false => (q, a - p),
    }
}

/// Whether num-bigint's division of a quotient of `qw` words by `b`, past [`DIV_LEAF`], costs at
/// most [`past_leaf_cost`].
fn num_bigint_divides(qw: usize, b: &BigUint) -> bool {
    let bw = words(b);
    num_bigint_div_cost(qw, bw) <= past_leaf_cost(qw, b)
}

/// The cost of [`div_rem_past_leaf`] for a quotient of `qw` words by the divisor `b`: the
/// cheaper of long division over the nonzero words and the division by a reciprocal.
fn past_leaf_cost(qw: usize, b: &BigUint) -> f64 {
    sparse_div_cost(qw, b).min(newton_cost(qw, words(b)))
}

/// [`div_rem`] above [`DIV_LEAF`], for `a >= b`: the cheaper of long division over the
/// divisor's nonzero words and the division by a reciprocal.
fn div_rem_past_leaf(a: &BigUint, b: &BigUint) -> (BigUint, BigUint) {
    // Complexity tradeoff: long division over the divisor's nonzero words costs
    // `nonzero(b)` word products for each quotient word, below the reciprocal's O(M(n)) when
    // the divisor has few nonzero words, as a kept power `2^s + 1` has; the cheaper of the two
    // computed costs is taken, with no size constant, and both give the same result. Tested
    // by `a_sparse_division_scales` and `quotients_agree_with_num_bigint` (COMPLEXITY.md K30).
    let (aw, bw) = (words(a), words(b));
    if sparse_div_cost(aw - bw + 1, b) <= newton_cost(aw - bw + 1, bw) {
        return sparse_div_rem(a, b);
    }
    div_rem_by_reciprocal(a, b)
}

/// [`div_rem`] by a reciprocal, for `a >= b`: block by block ([`div_rem_blocks`]) when the
/// quotient is wider than the divisor, else by one [`Level`].
fn div_rem_by_reciprocal(a: &BigUint, b: &BigUint) -> (BigUint, BigUint) {
    let (m, n) = (a.bits(), b.bits());
    let k = m - n + 1;
    if k > n {
        return div_rem_blocks(a, b);
    }
    let (linear, cyclic) = level_points(n, k);
    let tw = roots(linear.max(cyclic));
    let level = Level::new(b.to_u64_digits(), n, k, &tw);
    let (q, r) = level.div_rem(&a.to_u64_digits(), &tw);
    (from_words(q), from_words(r))
}

/// `a mod b` for `b` not zero, as [`div_rem`] finds it. A quotient wider than `b` is not built:
/// [`Divisor::rem`] reads `a` block by block and keeps only the remainder. Panics with "a
/// division by zero" for `b` zero, as [`div_rem`] does.
pub(crate) fn rem(a: &BigUint, b: &BigUint) -> BigUint {
    // A zero `b` has 0 bits, so it went to num-bigint's `%` below, which panics with "attempt
    // to divide by zero": the same refusal as `div_rem`'s, worded differently
    // (TEST-dry-shared-units, `units::refused`). One message for both, checked first.
    assert!(!b.is_zero(), "a division by zero");
    // Complexity tradeoff: a divisor of at most `DIV_LEAF` bits goes to num-bigint's long
    // division, O(DIV_LEAF m) for `m` bits, linear, as every step of a `Divisor` would send it
    // there anyway; the blocks of a `Divisor` would then each be one division of
    // `2 len` words with its own buffers, which for a one-word prime cost 5.8 times the
    // instructions of `bench::pncx_probe::pncx_pairs_scale` at 2880 (DRY-numeric-shared,
    // 2026-11-19). Identical results; tested by `quotients_agree_with_num_bigint`.
    if b.bits() <= DIV_LEAF {
        return a % b;
    }
    if rem_takes_blocks(a, b) {
        return Divisor::new(Cow::Borrowed(b), a.bits()).rem(a);
    }
    div_rem(a, b).1
}

/// Whether [`rem`] reads `a` in blocks through one [`Divisor`]: exactly where [`div_rem`]
/// would take [`div_rem_blocks`], a quotient wider than the divisor `b`, which is past
/// [`DIV_LEAF`], with num-bigint's computed cost and that of long division over `b`'s nonzero
/// words both above the reciprocal's. The rule of `div_rem`, not `DIV_LEAF` alone
/// (DRY-numeric-shared-rest): `crossover rem-leaf q`, a dividend of `(q + 1) w` words by `w`,
/// measured num-bigint's `%` cheaper up to 1878, 889, 413 and 227 words of divisor for `q` =
/// 2, 4, 16 and 256, near the division's crossovers (`div-leaf`: 899 for 4, 417 for 16, 235
/// for 256). The blocks taken from 91 words, as `DIV_LEAF` alone took them, did up to 1.208,
/// 1.168, 1.066 and 1.017 times the cheaper method's work; by `DIV_COST` as built, 1.000,
/// 1.000, 1.005 and 1.080 (at 128 words, where the blocks dip below num-bigint once), at
/// the cost of num-bigint's peak memory, up to 4 times the blocks', below the crossover
/// (2026-11-20). Both sides are measured by `rem-leaf`.
fn rem_takes_blocks(a: &BigUint, b: &BigUint) -> bool {
    let (m, n) = (a.bits(), b.bits());
    if n <= DIV_LEAF || m.saturating_sub(n) < n {
        return false;
    }
    let (qw, bw) = (words(a) - words(b) + 1, words(b));
    let blocks = newton_cost(qw, bw);
    blocks < num_bigint_div_cost(qw, bw) && blocks < sparse_div_cost(qw, b)
}

/// [`div_rem`] of a quotient wider than the divisor `b`: `a` is read from the top in blocks of
/// as many words as `b` has, each step dividing the remainder so far joined to the next block,
/// below `b 2^(64 len)`, by `b` through one [`Divisor`], and the quotient's blocks are written
/// into place. O((m / n) M(n)) for `m` bits by `n`, and the memory of a step is O(n).
fn div_rem_blocks(a: &BigUint, b: &BigUint) -> (BigUint, BigUint) {
    Divisor::new(Cow::Borrowed(b), a.bits()).div_rem(a)
}

/// The cost of [`sparse_div_rem`] of a quotient of `qw` words by the divisor `b`, by its
/// nonzero words and their runs ([`nonzero_runs`]): [`SPARSE_WORD`] a nonzero word,
/// [`SPARSE_RUN`] a run and [`SPARSE_STEP`] a step (where each comes from). O(words(b)).
fn sparse_div_cost(qw: usize, b: &BigUint) -> f64 {
    let (nonzero, runs) = nonzero_runs(b);
    (qw as f64 + 1.0) * (SPARSE_WORD * nonzero as f64 + SPARSE_RUN * runs as f64 + SPARSE_STEP)
}

/// The cost of [`div_rem`] by a reciprocal of a quotient of `qw` words by a divisor of `bw`,
/// in products: [`approx_reciprocal`] costs about 5/3 of a product of the quotient's width,
/// the estimate one, and the remainder a cyclic product of the divisor's width, which is one
/// product's transforms on half the points. A quotient wider than the divisor
/// ([`div_rem_blocks`]) builds that once, about three products of the divisor's width, and
/// then costs about one product for each block, its two factors' transforms kept. A quotient of
/// `qw` words has a dividend of `aw = qw + bw - 1`, which [`Divisor::blocks`] reads as a first
/// block of at most `bw` words, by long division in O(bw), then
/// `(aw - bw) / bw = (qw - 1) / bw` blocks, rounded up. Not `qw / bw` rounded up, one block
/// more where `qw` is 1 more than a multiple of `bw`: `crossover rem-leaf`, a dividend of
/// `(q + 1) bw` words, then took num-bigint's
/// division up to 2048 words of divisor for `q = 2` where the blocks did 0.632 times its work
/// from 1898 words (DRY-numeric-shared-rest, 2026-11-20).
///
/// A quotient at most as wide as the divisor costs its products on the points of its
/// [`Level`] ([`level_points`]): the power of two at or above `2 qw` words for the estimate
/// and at or above about `bw` for the remainder, which never wrap their top coefficients as
/// [`transform_cost`] may. With [`transform_cost`] the cost of `2049` by `2049` words read
/// about that of `2048` by `2048`, and the build took the reciprocal there at 1.527 times
/// num-bigint's work (29,147,467 against 19,087,323 instructions; `crossover div-leaf 1 1 0
/// 2048,2049,2896,4096,5793`, zed_icount, 2026-11-23, plan row
/// PERF-div-narrow-quotient-factor, cross-review XR-ROOTS-REF round 2, D8): the reciprocal's
/// work steps up by 1.77 from 2048 to 2049 words, the Level's points doubling. The wider
/// quotients' branch keeps [`transform_cost`], to which their four shapes fit at 9.1.
fn newton_cost(qw: usize, bw: usize) -> f64 {
    let level = |coeffs: usize| TRANSFORM_COST * points_cost(coeffs.next_power_of_two()) as f64;
    match qw > bw {
        true => ((qw - 1).div_ceil(bw) as f64 + 3.0) * transform_cost(2 * bw),
        false => 8.0 * level(2 * qw) / 3.0 + level(bw),
    }
}

/// num-bigint's cost of a division of a quotient of `qw` words by a divisor of `bw`, in the
/// units of [`TRANSFORM_COST`]: `DIV_COST s^DIV_POWER` for the narrower `s` of the two, and
/// for each word of the wider beyond it `DIV_COST s^(DIV_POWER - 1)`, times [`DIV_NARROW`]
/// when the divisor is the wider. A quotient wider than the divisor so costs as `qw / bw`
/// divisions of `2 bw` by `bw` words would. That is a fit to num-bigint's measured work, not
/// its method: num-bigint 0.4.8, for a dividend over 128 words and a divisor over 64
/// (`div_rem_core`, src/biguint/division.rs:343-346, read 2026-11-23), divides by Burnikel
/// and Ziegler's recursion at one power-of-two level, `L = 2^floor(log2 aw)` words for a
/// dividend of `aw`, doubled where the divisor has more than `L` (:328-331): the dividend as
/// two digits of `L` words over the divisor as one, each digit halved down to 64 words. Its
/// work so steps where `aw` crosses a power of two, which this form does not model.
fn num_bigint_div_cost(qw: usize, bw: usize) -> f64 {
    DIV_COST * num_bigint_div_units(qw, bw)
}

/// [`num_bigint_div_cost`] over [`DIV_COST`].
fn num_bigint_div_units(qw: usize, bw: usize) -> f64 {
    let (q, b) = (qw as f64, bw as f64);
    let s = q.min(b);
    let wider = match qw > bw {
        true => q - b,
        false => DIV_NARROW * (b - q),
    };
    let same = match qw <= bw + 1 {
        true => DIV_SAME,
        false => 1.0,
    };
    same * s.powf(DIV_POWER - 1.0) * (s + wider)
}

/// `(a / b, a mod b)` by long division (Knuth's algorithm D) over the nonzero words of `b`,
/// which has at least two words: `a` is read from the top, a word at a time, into a window
/// of `words(b) + 1` words holding the remainder so far, and each step subtracts a quotient
/// word times `b`, touching only the words where `b` is nonzero and those a borrow passes.
/// A borrow passes a zero word and leaves it all ones, which stops the next borrow, so the
/// borrows cost O(words(a)) in all and the division O(words(a) + quotient words times
/// nonzero(b)). Its memory is that of `b` and the quotient, whatever the size of `a`.
fn sparse_div_rem(a: &BigUint, b: &BigUint) -> (BigUint, BigUint) {
    if a < b {
        return (BigUint::zero(), a.clone());
    }
    let (q, r) = sparse_div_rem_words(a.iter_u64_digits(), b);
    (from_words(q), from_words(r))
}

/// [`sparse_div_rem`] of the words `a`, lowest first, at least `words(b) - 1` of them, as
/// words with no zero on top.
fn sparse_div_rem_words(
    a: impl DoubleEndedIterator<Item = u64> + ExactSizeIterator,
    b: &BigUint,
) -> (Vec<u64>, Vec<u64>) {
    let la = a.len();
    // Normalized: the top word of `b 2^sh` has its top bit set, so a quotient word estimated
    // from the window's top two words and the divisor's top word is at most two above.
    // Unreachable: both callers pass a nonzero `b`: `sparse_div_rem` one of at least two
    // words, and `Divisor::step` the divisor `Divisor::new` asserts is not zero.
    let sh = b
        .iter_u64_digits()
        .next_back()
        .expect("b is not zero")
        .leading_zeros();
    let bs = (b << sh).to_u64_digits();
    let lb = bs.len();
    debug_assert!(lb >= 2);
    let nonzero: Vec<usize> = (0..lb).filter(|&k| bs[k] != 0).collect();
    let (b1, b2) = (u128::from(bs[lb - 1]), u128::from(bs[lb - 2]));
    // The words of `a 2^sh`, highest first, one more than `a` has.
    let mut prev = 0u64;
    debug_assert!(la + 1 >= lb, "a has at least words(b) - 1 words");
    let mut shifted = a.rev().chain(std::iter::once(0)).map(|d| {
        let w = (((u128::from(prev) << 64) | u128::from(d)) >> (64 - sh)) as u64;
        prev = d;
        w
    });
    // The remainder so far, `lb` words, lowest first, lies in `buf[start..start + lb]`; a step
    // writes the next word below it and leaves the top word zero, so the remainder moves down
    // a word, and when it reaches the bottom it is copied to the top, once every `lb + 2`
    // steps. It starts as the top `lb - 1` words of `a 2^sh`, below `b 2^sh`, and a zero.
    let mut buf = vec![0u64; 2 * lb + 2];
    let mut start = lb + 2;
    for (i, w) in shifted.by_ref().take(lb - 1).enumerate() {
        buf[start + lb - 2 - i] = w;
    }
    let mut quotient: Vec<u64> = Vec::with_capacity(la + 2 - lb);
    for w in shifted {
        if start == 0 {
            buf.copy_within(0..lb, lb + 2);
            start = lb + 2;
        }
        start -= 1;
        buf[start] = w;
        let win = &mut buf[start..=start + lb];
        let top = (u128::from(win[lb]) << 64) | u128::from(win[lb - 1]);
        let (mut q, mut r) = (top / b1, top % b1);
        while q >> 64 != 0 || (r >> 64 == 0 && q * b2 > (r << 64 | u128::from(win[lb - 2]))) {
            q -= 1;
            r += b1;
        }
        let q = q as u64;
        // `q b 2^sh` is subtracted word by word with the carry kept while the divisor's
        // nonzero words follow each other, and carried up by `sub_at` where they do not.
        let (mut carry, mut at, mut below) = (0u64, 0usize, false);
        for &k in &nonzero {
            if k != at && carry != 0 {
                below |= sub_at(win, at, carry);
                carry = 0;
            }
            // At most `(2^64 - 1)^2 + 2^64 - 1`, so the carry stays a word.
            let t = u128::from(q) * u128::from(bs[k]) + u128::from(carry);
            let (v, borrow) = win[k].overflowing_sub(t as u64);
            win[k] = v;
            carry = (t >> 64) as u64 + u64::from(borrow);
            at = k + 1;
        }
        if carry != 0 {
            below |= sub_at(win, at, carry);
        }
        let q = match below {
            // The window went below zero by less than `b 2^sh`: one addition makes it right.
            true => {
                let (mut carry, mut at) = (false, 0usize);
                for &k in &nonzero {
                    if k != at && carry {
                        add_at(win, at, 1);
                        carry = false;
                    }
                    let (v, c1) = win[k].overflowing_add(bs[k]);
                    let (v, c2) = v.overflowing_add(u64::from(carry));
                    win[k] = v;
                    carry = c1 || c2;
                    at = k + 1;
                }
                if carry {
                    add_at(win, at, 1);
                }
                q - 1
            }
            false => q,
        };
        debug_assert_eq!(win[lb], 0, "the remainder is below the divisor");
        quotient.push(q);
    }
    quotient.reverse();
    trim(&mut quotient);
    buf.truncate(start + lb);
    buf.drain(..start);
    (quotient, shr_words(&buf, u64::from(sh)))
}

/// Subtracts `x` from `w` at word `i`, the borrow carried up; whether it passes the top.
fn sub_at(w: &mut [u64], mut i: usize, x: u64) -> bool {
    let (v, mut borrow) = w[i].overflowing_sub(x);
    w[i] = v;
    while borrow {
        i += 1;
        if i == w.len() {
            return true;
        }
        (w[i], borrow) = w[i].overflowing_sub(1);
    }
    false
}

/// Adds `x` to `w` at word `i`, the carry carried up and dropped past the top.
fn add_at(w: &mut [u64], mut i: usize, x: u64) {
    if i == w.len() {
        return;
    }
    let (v, mut carry) = w[i].overflowing_add(x);
    w[i] = v;
    while carry {
        i += 1;
        if i == w.len() {
            return;
        }
        (w[i], carry) = w[i].overflowing_add(1);
    }
}

/// The quotient and remainder from an estimate `q` of `a / b` a few off, given `q b`.
fn settle(a: &BigUint, b: &BigUint, mut q: BigUint, mut qb: BigUint) -> (BigUint, BigUint) {
    while qb > *a {
        qb -= b;
        q -= 1u32;
    }
    let mut r = a - &qb;
    drop(qb);
    while r >= *b {
        r -= b;
        q += 1u32;
    }
    (q, r)
}

/// `2^2k / x`, floored, for `x` of exactly `k` bits: [`approx_reciprocal`], one below or
/// exact, made exact by the sign of `2^2k - x y - x`, found by one cyclic product. O(M(k)).
fn reciprocal(x: &BigUint, k: u64) -> BigUint {
    reciprocal_from(x, k, RECIP_LEAF)
}

/// [`reciprocal`] with Newton's steps from `leaf` bits in place of [`RECIP_LEAF`].
fn reciprocal_from(x: &BigUint, k: u64, leaf: u64) -> BigUint {
    let m = cyclic_points(k);
    let tw = roots(m);
    let mut y = approx_reciprocal(x, k, &tw, leaf);
    // `e = 2^2k - x y` lies in `(0, 2x)`, below `2^(64 m + 61)`; the floor is `y + 1` when
    // `e >= x`.
    let (xw, yw) = (x.to_u64_digits(), y.to_u64_digits());
    let (mut xy, carry) = cyclic_product(&folded(&xw, m), &spectra(&yw, m, &tw), &tw);
    add_around(&mut xy, carry);
    let e = sub_around(power_around(2 * k, m), &xy);
    let low = low_power(2 * k).wrapping_sub(first(&xw).wrapping_mul(first(&yw)));
    let (negative, e) = unfold(e, m, low);
    // `e in (0, 2x)` is proved at `approx_reciprocal` (`x y < 2^2k < x (y + 2)`), and checked
    // here in every build, so that a wrong reciprocal stops the run, never a quotient read from
    // it. The sign is one bit; `e - x < x` costs one subtraction of k bits beside the O(M(k))
    // of the call, and only when `e >= x`.
    assert!(
        !negative && e.iter().any(|&w| w != 0),
        "the estimate is below the reciprocal"
    );
    if cmp_words(&e, &xw).is_ge() {
        assert!(
            from_words(e) - x < *x,
            "the estimate is within 2 of the reciprocal"
        );
        y += 1u32;
    }
    y
}

/// `X` with `a X < 2^2p <= a (X + 2)`, for `a` of exactly `p` bits, so that
/// `2^p <= X < 2^(p + 1)`, by Newton's iteration on the top bits of `a`, each precision `p`
/// from `h = ceil((p + 3) / 2)` ([`newton`]), from num-bigint's division at or below
/// `leaf` bits ([`RECIP_LEAF`] except in a benchmark). Each precision costs five transforms on
/// the points of a product of `p / 2` bits by `p / 2`, so the whole about 5/3 of a product of
/// `p` bits by `p`. `tw` as for
/// [`Field::forward`], of at least [`cyclic_points`]`(p)` points. Brent and Zimmermann, Modern
/// Computer Arithmetic (2010), Algorithm 3.5, in bits rather than words; the module's
/// "Sources" gives the lemma, why it does not cover bits, and the test that checks the bound.
///
/// Proof of the bound at every width, in bits (the lemma's `β >= 8` not needed), by induction
/// over the list `sizes`, `p = s_0 > s_1 > ... > s_j`, `s_(i+1) = ceil((s_i + 3) / 2)`, built
/// while `s_i > leaf`. It ends: for `s > 3`, `ceil((s + 3) / 2) < s`, and every caller's
/// `leaf` is at least 4 (`RECIP_LEAF` is 4 or 64·416; the benchmark hook takes `leaf.max(4)`),
/// so the loop steps only from a size `s > leaf >= 4`, whose successor is smaller. Base, at
/// `h = s_j`: `x =
/// floor((2^2h - 1) / a_h)` for `a_h = a >> (p - h)`, the top `h` bits, so `a_h x <= 2^2h - 1 <
/// 2^2h` and `a_h (x + 1) > 2^2h - 1`, so `a_h (x + 1) >= 2^2h`: the step's premise
/// `a_h x < 2^2h <= a_h (x + 2)` holds, and so does the bound when `p <= leaf` and no step
/// runs. Step, from `h = s_(i+1)` to `q = s_i`: the top `h` bits of `top = a >> (p - q)` are
/// `a >> (p - h)`, of exactly `h` bits as `top` has `q`; `h = ceil((q + 3) / 2)` gives `2h >=
/// q + 3`, so `l = q - h <= h - 3`: [`newton`]'s premise `l + 3 <= h` holds, and its proof
/// gives `0 < 2^2q / top - X < 2`, that is `top X < 2^2q < top (X + 2)`. The last step has
/// `q = p` and
/// `top = a`. So the output has `a X < 2^2p < a (X + 2)`, which is what `reciprocal_from` needs.
/// Tested by `tests::approximate_reciprocals_keep_their_bounds` at 5 to 13 bits in full and at
/// 15 widths up to 30,001 bits.
fn approx_reciprocal(a: &BigUint, p: u64, tw: &Roots, leaf: u64) -> BigUint {
    debug_assert_eq!(a.bits(), p);
    let mut sizes = vec![p];
    // Complexity tradeoff: the precisions at or below `RECIP_LEAF` bits start from one
    // division by num-bigint, O(RECIP_LEAF^2) once, in place of further Newton steps whose
    // transforms cost more at that width; the reciprocal's bounds do not depend on it, which
    // `tests::approximate_reciprocals_keep_their_bounds` checks with the leaf at 4 bits.
    while let Some(&s) = sizes.last().filter(|&&s| s > leaf) {
        sizes.push((s + 3).div_ceil(2));
    }
    // Unreachable: `sizes` starts as `[p]` and only grows.
    let mut h = sizes.pop().expect("p is listed");
    // `a_h X < 2^2h <= a_h (X + 1)` for `a_h` the top `h` bits.
    let mut x = ((BigUint::one() << (2 * h)) - 1u32) / (a >> (p - h));
    while let Some(q) = sizes.pop() {
        let top = match q == p {
            true => Cow::Borrowed(a),
            false => Cow::Owned(a >> (p - q)),
        };
        x = newton(&top, q, x, h, tw);
        h = q;
    }
    x
}

/// One step of [`approx_reciprocal`]: from `xh` for the top `h` bits `a_h` of `a`, which has
/// `p` bits, `a_h xh < 2^2h <= a_h (xh + 2)`, the same for `a`, with `l = p - h <= h - 3`.
///
/// `T = a xh` lies in `(2^(p + h) - 2a, 2^(p + h) + 2^(p + 1))`: `a_h xh <= a / 2^l xh` and
/// `xh < 2^(h + 1)` bound it above, and `a_h (xh + 2) >= 2^2h` with `a_h 2^l <= a` below. So
/// `R = T - 2^(p + h)` is found modulo `M = 2^(64 m) - 1` by a cyclic product and [`unfold`],
/// and taking `a` from it for each one taken from `xh` (at most four times) leaves
/// `t = 2^(p + h) - a xh` in `(0, 2a)`. Then `2^2p / a = xh 2^l / (1 - d)` with
/// `d = t / 2^(p + h)`, `= xh 2^l + xh t / 2^2h + Q`, `Q = (2^2p / a) d^2`, and the step returns
/// `X = xh 2^l + floor(xh floor(t / 2^l) / 2^(2h - l))`. What it leaves out is positive, as
/// `Q > 0`, so `a X < 2^2p`, and below 2: the floor less than 1, the low bits of `t` less than
/// `2^(h + 1) 2^l / 2^2h <= 1/4`, and `Q < 4a / 2^2h < 2^(p + 2 - 2h) <= 1/2`.
///
/// Both products are cyclic on `m` points and share `xh`'s transforms: five transforms per
/// prime, `m` the least power of two with `64 m >= p - 55`, so that `|R| < 2^(p + 1)` and
/// `xh floor(t / 2^l) < 2^(2h + 2)` are both below `2^(64 m + 61)`.
fn newton(a: &BigUint, p: u64, xh: BigUint, h: u64, tw: &Roots) -> BigUint {
    let l = p - h;
    debug_assert!(l + 3 <= h);
    let m = cyclic_points(p);
    let xw = xh.to_u64_digits();
    let xs = spectra(&xw, m, tw);
    let aw = a.to_u64_digits();
    let (mut t, carry) = cyclic_product(&folded(&aw, m), &xs, tw);
    add_around(&mut t, carry);
    let r = sub_around(t, &power_around(p + h, m));
    let low = first(&aw)
        .wrapping_mul(first(&xw))
        .wrapping_sub(low_power(p + h));
    drop(aw);
    let (negative, r) = unfold(r, m, low);
    let mut r = from_words(r);
    // `t = 2^(p + h) - a xh`, `xh` lowered by `taken`.
    let mut taken = 0u32;
    let t = match negative {
        true => r,
        false => loop {
            taken += 1;
            if r < *a {
                break a - &r;
            }
            r -= a;
        },
    };
    debug_assert!(taken <= 4, "R is below 2^(p + 1) and a at least 2^(p - 1)");
    let tm = t >> l;
    let tmw = tm.to_u64_digits();
    // `xh tm`, `tm = floor(t / 2^l)`, for the `xh` before it was lowered, whose transforms are
    // kept, then `taken tm` taken off.
    let (mut u, carry) = cyclic_product(&folded(&tmw, m), &xs, tw);
    add_around(&mut u, carry);
    let (negative, u) = unfold(u, m, first(&tmw).wrapping_mul(first(&xw)));
    debug_assert!(!negative, "a product of positive numbers");
    drop((xs, xw, tmw));
    let u = from_words(u) - &tm * taken;
    ((xh - taken) << l) + (u >> (2 * h - l))
}

/// `floor(a / m)` for `m` not zero, by [`div_rem`] on the magnitudes: O(M(n)) past the
/// measured crossover, num-bigint's division below it. A quotient of operands of opposite
/// signs with a remainder rounds down, one below the negated quotient of the magnitudes.
pub(crate) fn div_floor(a: &BigInt, m: &BigInt) -> BigInt {
    let (q, r) = div_rem(a.magnitude(), m.magnitude());
    if a.is_negative() == m.is_negative() {
        BigInt::from(q)
    } else if r.is_zero() {
        -BigInt::from(q)
    } else {
        -BigInt::from(q + 1u32)
    }
}

/// `a - m floor(a / m)` for `m` not zero, the remainder of [`div_floor`], which has the sign
/// of `m`, by [`rem`] on the magnitudes (no quotient built when it would be wider than `m`).
pub(crate) fn mod_floor(a: &BigInt, m: &BigInt) -> BigInt {
    let r = rem(a.magnitude(), m.magnitude());
    let r = match a.is_negative() != m.is_negative() && !r.is_zero() {
        true => m.magnitude() - r,
        false => r,
    };
    BigInt::from_biguint(m.sign(), r)
}

/// The Euclidean quotient `floor`-like `a div m`, the remainder in `[0, |m|)`, `m` not zero.
pub(crate) fn div_euclid(a: &BigInt, m: &BigInt) -> BigInt {
    let (q, r) = div_rem(a.magnitude(), m.magnitude());
    let q = match (a.is_negative(), r.is_zero()) {
        (true, false) => q + 1u32,
        _ => q,
    };
    let sign = match a.is_negative() == m.is_negative() {
        true => Sign::Plus,
        false => Sign::Minus,
    };
    BigInt::from_biguint(sign, q)
}

// ------------------------------------------------------------------------------------------
// Greatest common divisor

/// A 2x2 matrix `[[m00, m01], [m10, m11]]` of the binary gcd's steps.
struct Mat([BigInt; 4]);

impl Mat {
    fn identity() -> Mat {
        Mat([BigInt::one(), BigInt::zero(), BigInt::zero(), BigInt::one()])
    }

    /// `self * other`.
    fn times(&self, other: &Mat) -> Mat {
        let [a, b, c, d] = &self.0;
        let [e, f, g, h] = &other.0;
        // Unreachable: `matrix_product` returns `2 c` entries for `c = r.len() / 2`, four here.
        let [w, x, y, z] = matrix_product([a, b, c, d], &[e, f, g, h], None)
            .try_into()
            .expect("a 2x2 product");
        Mat([w, x, y, z])
    }

    /// `self * (a, b) / 2^2j`, exact.
    fn apply(&self, a: &BigInt, b: &BigInt, j: u64) -> (BigInt, BigInt) {
        let [m00, m01, m10, m11] = &self.0;
        // Unreachable: `matrix_product` returns `2 c` entries for `c = r.len() / 2`, two here.
        let [c, d] = matrix_product([m00, m01, m10, m11], &[a, b], Some(2 * j))
            .try_into()
            .expect("a 2x1 product");
        (c, d)
    }
}

/// `l r` for the 2x2 matrix `l` and the 2 x `c` matrix `r`, both by rows (`r` has `2 c`
/// entries), its `2 c` entries by rows.
///
/// Each entry is a sum of two products, and each factor is in two products. By transforms,
/// on points enough for the widest product, each nonzero factor is transformed once and each
/// sum is formed among the transforms and transformed back once: `4 + 2 c` transforms forward
/// and `2 c` back, where the products one by one take three each, `12 c`. That is 8 in place
/// of 12 for `c = 1` ([`Mat::apply`]) and 12 in place of 24 for `c = 2` ([`Mat::times`]). It is
/// taken when its cost, `TRANSFORM_COST / 3` [`points_cost`] a transform (a third of a
/// product's), is less than the sum of the costs [`mul`] computes for the products, and every
/// product is above `MUL_LEAF`, where `mul` takes num-bigint's with no cost computed; else the
/// products are taken one by one by [`mul_int`]. Both give the same entries.
///
/// With `shift` `Some(s)`, each entry, known to be a multiple of `2^s`, is divided by it, and
/// the points are planned for the quotient, not the product: the transforms give the entry
/// modulo `2^(64 n) - 1`, enough to find a quotient of fewer than `64 n - 2` bits (see
/// [`unrotate`]). [`Mat::apply`] after `j` steps has entries below `2^(2 j)` and the shift
/// `2 j`, so for numbers of `b` bits the quotients have about `b` bits where the products have
/// `b + 2 j`: in [`half`], with `b` about `2 k` and `2 j` about `k`, the points are planned for
/// about `2 k` bits in place of `3 k`.
fn matrix_product(l: [&BigInt; 4], r: &[&BigInt], shift: Option<u64>) -> Vec<BigInt> {
    let c = r.len() / 2;
    let width = |x: &BigInt| x.magnitude().iter_u64_digits().len();
    let terms = || {
        (0..2 * c).flat_map(move |out| {
            let (i, j) = (out / c, out % c);
            [(l[2 * i], r[j]), (l[2 * i + 1], r[c + j])]
        })
    };
    let one_by_one = || -> Vec<BigInt> {
        (0..2 * c)
            .map(|out| {
                let (i, j) = (out / c, out % c);
                let e = mul_int(l[2 * i], r[j]) + mul_int(l[2 * i + 1], r[c + j]);
                // No shift by 0: num-bigint's shift, even by 0, shrinks the sum's digits to
                // fit, a reallocation and copy when it has spare capacity (1-2 % of bezout's
                // instructions at every width).
                match shift {
                    Some(s) => e >> s,
                    None => e,
                }
            })
            .collect()
    };
    let nonzero = || terms().filter(|(x, y)| !x.is_zero() && !y.is_zero());
    // A product at or below `MUL_LEAF` decides for the products one by one before any cost is
    // computed: the common case inside the half gcd's recursion.
    if nonzero().any(|(x, y)| width(x).min(width(y)) <= MUL_LEAF) {
        return one_by_one();
    }
    let (mut separate, mut widest) = (0.0, 0);
    for (x, y) in nonzero() {
        let (wx, wy) = (width(x), width(y));
        separate += dense_cost(wx, wy);
        widest = widest.max(wx + wy - 1);
    }
    let factors = l.iter().chain(r).filter(|x| !x.is_zero()).count();
    let n = match shift {
        None => widest.next_power_of_two(),
        // Each entry `e = 2^s q`, `|q| < 2^(bl + br + 1 - s)` for factors below `2^bl` and
        // `2^br`; with `64 n >= bl + br + 3 - s` its residue modulo `2^(64 n) - 1` gives `q`
        // (see [`unrotate`]). A factor of more than `n` words is folded into `n` (see
        // [`Field::transform_into`]); with `n` at least a quarter of the widest, each point
        // holds at most four words, and each coefficient, a sum of at most `2 n` products of
        // two points, is below `2 n 16 2^128 <= 2^183` for `n <= 2^50`: within `P / 2`, as
        // [`garner_signed`] needs.
        Some(s) => {
            let bits = |x: &[&BigInt]| x.iter().map(|x| x.bits()).max().unwrap_or(0);
            let q = (bits(&l) + bits(r) + 3).saturating_sub(s).div_ceil(64) as usize;
            let wide = l.iter().chain(r).map(|x| width(x)).max().unwrap_or(0);
            q.max(wide.div_ceil(4)).next_power_of_two()
        }
    };
    let shared = (factors + 2 * c) as f64 * TRANSFORM_COST * points_cost(n) as f64 / 3.0;
    if widest == 0 || shared >= separate {
        return one_by_one();
    }
    #[cfg(test)]
    SHARED_PRODUCTS.with(|v| {
        let folded = l.iter().chain(r).any(|x| width(x) > n);
        let (shared, folds) = v.get();
        v.set((shared + 1, folds + u32::from(folded)));
    });
    let tw = roots(n);
    // For each prime, the left factors' transforms, scaled, the right factors' transforms, in
    // buffers kept for the three primes, and each entry's sum of pointwise products, signed,
    // transformed back, with room for the two words of the carry.
    let mut residues: Vec<[Vec<u64>; 3]> = (0..2 * c).map(|_| Default::default()).collect();
    let mut ls: Vec<Vec<u64>> = (0..4).map(|_| Vec::with_capacity(n)).collect();
    let mut rs: Vec<Vec<u64>> = (0..2 * c).map(|_| Vec::with_capacity(n)).collect();
    for (k, field) in FIELDS.iter().enumerate() {
        for (x, v) in l.iter().zip(&mut ls).filter(|(x, _)| !x.is_zero()) {
            field.transform_into(x.magnitude(), n, &tw[k], v);
            field.scale(v, n);
        }
        for (y, v) in r.iter().zip(&mut rs).filter(|(y, _)| !y.is_zero()) {
            field.transform_into(y.magnitude(), n, &tw[k], v);
        }
        for (out, slot) in residues.iter_mut().enumerate() {
            let (i, j) = (out / c, out % c);
            let mut acc = Vec::with_capacity(n + 2);
            acc.resize(n, 0);
            for (t, (x, y)) in [(2 * i, j), (2 * i + 1, c + j)].into_iter().enumerate() {
                let (lx, ry) = (l[2 * i + t], r[y]);
                if lx.is_zero() || ry.is_zero() {
                    continue;
                }
                let plus = lx.is_negative() == ry.is_negative();
                for ((a, &u), &v) in acc.iter_mut().zip(&ls[x]).zip(&rs[y]) {
                    let p = field.mul(u, v);
                    *a = match plus {
                        true => field.add(*a, p),
                        false => field.sub(*a, p),
                    };
                }
            }
            field.inverse(&mut acc, &tw[k]);
            slot[k] = acc;
        }
    }
    residues
        .into_iter()
        .map(|[mut r0, r1, r2]| {
            let carry = garner_signed(&mut r0, &r1, &r2);
            drop((r1, r2));
            match shift {
                None => signed_from_words(r0, carry),
                Some(s) => unrotate(r0, carry, s),
            }
        })
        .collect()
}

#[cfg(test)]
thread_local! {
    /// The products [`matrix_product`] took by shared transforms, and how many of them folded
    /// a factor.
    static SHARED_PRODUCTS: std::cell::Cell<(u32, u32)> = const { std::cell::Cell::new((0, 0)) };
}

/// `q` from the words `w` (two's complement, `n` of them) and the signed `carry` of
/// `v = w + carry 2^(64 n)`, where `v = 2^s q mod M`, `M = 2^(64 n) - 1`, and `|q| < 2^(64 n - 2)`.
/// As `2^(64 n)` is 1 modulo `M`, `v` is `w + carry` there, and `2^s` turns the words round by
/// `s` bits, so turning them back by `s` bits gives `q mod M`, read as negative when its top
/// bit is set: `q - M`, whose magnitude is the complement of the words.
fn unrotate(mut w: Vec<u64>, carry: i128, s: u64) -> BigInt {
    let n = w.len();
    match carry >= 0 {
        true => add_around(&mut w, carry as u128),
        false => {
            let c = carry.unsigned_abs();
            // `w - c + 2^(64 n) >= 1` when it borrows, `c < 2^123` being below `2^(64 n)`;
            // `n` is above `MUL_LEAF`, so at least the two words of `c`.
            if sub_words(&mut w, &[c as u64, (c >> 64) as u64]) {
                sub_at(&mut w, 0, 1);
            }
        }
    }
    let (words, bits) = ((s / 64) as usize % n, (s % 64) as u32);
    w.rotate_left(words);
    if bits != 0 {
        let low = w[0] << (64 - bits);
        for i in 0..n - 1 {
            w[i] = (w[i] >> bits) | (w[i + 1] << (64 - bits));
        }
        w[n - 1] = (w[n - 1] >> bits) | low;
    }
    let sign = match w[n - 1] >> 63 {
        0 => Sign::Plus,
        _ => {
            w.iter_mut().for_each(|d| *d = !*d);
            Sign::Minus
        }
    };
    trim(&mut w);
    BigInt::from_biguint(sign, from_words(w))
}

/// `x` modulo `2^w`, centered: in `[-2^(w-1), 2^(w-1))`.
fn cmod(x: &BigInt, w: u64) -> BigInt {
    let one = BigInt::one();
    let r = x & ((&one << w) - &one);
    match r.bit(w - 1) {
        true => r - (one << w),
        false => r,
    }
}

/// `x` modulo `2^128`, from the two's complement of a negative `x`.
fn low128(x: &BigInt) -> u128 {
    let mut d = x.iter_u64_digits();
    let lo = u128::from(d.next().unwrap_or(0)) | (u128::from(d.next().unwrap_or(0)) << 64);
    match x.is_negative() {
        true => lo.wrapping_neg(),
        false => lo,
    }
}

/// The 2-adic valuation of `x`; `None` for 0.
fn nu(x: &BigInt) -> Option<u64> {
    x.trailing_zeros()
}

/// `x^-1 mod 2^w` for an odd `x`, by Newton's iteration `y (2 - x y)`, which doubles the
/// correct bits. With `y` right to `h` bits, `x y = 1 + 2^h e` modulo `2^bits`, `bits <= 2 h`,
/// and `y (2 - x y) = y - 2^h y e`: only `e` and `y e` modulo `2^(bits - h)` are needed.
/// Complexity tradeoff: the plain step takes two products of `bits x h` bits; this one takes
/// one of `bits x h` and one of `h x (bits - h)`, about a quarter less, O(M(w)) either way.
/// Test inverses_modulo_powers_of_two.
fn inverse_mod_pow2(x: &BigUint, w: u64) -> BigUint {
    // Unreachable: every caller passes an odd `x` (`step`'s `b1`, `a` after its `bit(0)`
    // test, the odd part `o`, an odd modulus), and an odd number has a low word.
    let low = x.iter_u64_digits().next().expect("x is odd");
    let mut y = BigUint::from(inverse_mod_2_64(low));
    let mut h = 64;
    while h < w {
        let bits = (2 * h).min(w);
        let high = (BigUint::one() << (bits - h)) - 1u32;
        let e = (mul(&(x & ((BigUint::one() << bits) - 1u32)), &y) >> h) & &high;
        // `-y e` modulo `2^(bits - h)`, placed above the `h` bits of `y`.
        let ye = mul(&y, &e) & &high;
        y += (((&high + 1u32) - ye) & &high) << h;
        h = bits;
    }
    let mask = (BigUint::one() << w) - 1u32;
    y & mask
}

/// One binary division step of `(a, b)` with `a` odd and `b` of valuation `j`: with
/// `b' = b / 2^j` and `q = -a / b' mod 2^(j+1)` centered, `|q| < 2^j`, the pair becomes
/// `(b', (a + q b') / 2^j)`, which is `[[0, 2^j], [2^j, q]] (a, b) / 2^2j`. The new second
/// number is even, and the odd part of the gcd is kept.
fn step(a: &BigInt, b: &BigInt, j: u64) -> (BigInt, BigInt, BigInt) {
    let b1 = b >> j;
    let w = j + 1;
    let q = match w < 128 {
        // In 128-bit registers: `b1^-1 mod 2^128` by one more Newton step from 64 bits.
        true => {
            let y = low128(&b1);
            let inv = u128::from(inverse_mod_2_64(y as u64));
            let inv = inv.wrapping_mul(2u128.wrapping_sub(y.wrapping_mul(inv)));
            let t = low128(a).wrapping_neg().wrapping_mul(inv) & ((1u128 << w) - 1);
            match t >> j {
                0 => BigInt::from(t),
                _ => -BigInt::from((1u128 << w) - t),
            }
        }
        false => {
            // The residues modulo `2^w`, not negative (`&` reads a negative number in two's
            // complement).
            let mask = (BigInt::one() << w) - 1;
            let inv = BigInt::from(inverse_mod_pow2((&b1 & &mask).magnitude(), w));
            cmod(&-mul_int(&(a & &mask), &inv), w)
        }
    };
    let r = (a + mul_int(&q, &b1)) >> j;
    (q, b1, r)
}

/// What a caller of [`half`] takes from it: the product `R` of the steps, the pair they reach,
/// or both.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Want {
    Matrix,
    Pair,
    Both,
}

/// [`half`]'s result: the number of halvings `j`, and `R` and the pair `R (a, b) / 2^2j` as
/// asked for by its [`Want`].
struct Half {
    j: u64,
    r: Option<Mat>,
    pair: Option<(BigInt, BigInt)>,
}

impl Half {
    /// `(j, R, x, y)` of a result asked for with [`Want::Both`].
    fn both(self) -> (u64, Mat, BigInt, BigInt) {
        // Unreachable: `half` sets `pair` when asked for it (`want != Matrix`) and `r` when
        // asked for the matrix (`want != Pair`), and `both` is called only after `Want::Both`.
        let (x, y) = self.pair.expect("asked for the pair");
        (self.j, self.r.expect("asked for the matrix"), x, y)
    }
}

/// The steps of the binary gcd of `(a, b)`, `a` odd and `b` even or 0, whose valuations sum
/// to at most `k`, as many as fit: their number of halvings `j`, their product `R`, and the
/// pair they reach, `R (a, b) / 2^2j`. The steps depend only on `a` and `b` modulo
/// `2^(2k+1)`, so the first half is found from those residues of half the width
/// ([`half_low`]), and the rest from the pair it reaches (Stehlé and Zimmermann, "A binary
/// recursive gcd algorithm", ANTS 2004, Lemma 7; cited in full in the module's "Sources").
/// O(M(k) log k).
///
/// Complexity tradeoff: `R` is `r2 (q r1)`, a product of two matrices of about `k / 2` bits,
/// and the pair is `r2 (a3, b3) / 2^2j2` from the pair `(a3, b3)` that `r2` was found from,
/// a product of a matrix by a pair. A caller that needs one of them only ([`gcd_using`] the
/// pair, the second half inside the recursion the matrix) is spared the other product. Before
/// [`gcd_using`] asked for the pair only, it formed `R` and applied it to the whole numbers;
/// without the product of the matrices a gcd of 4,153 words takes 7.1 % fewer instructions,
/// one of 33,220 words 6.5 % fewer (2026-11-12). Test half_pairs_match_the_matrix.
fn half(a: BigInt, b: BigInt, k: u64, want: Want, lift: u64) -> Half {
    let (matrix, pair) = (want != Want::Pair, want != Want::Matrix);
    let done = |j, r: Mat, x, y| Half {
        j,
        r: matrix.then_some(r),
        pair: pair.then_some((x, y)),
    };
    match nu(&b) {
        Some(v) if v <= k => {}
        _ => return done(0, Mat::identity(), a, b),
    }
    if k <= HALF_LEAF {
        let (j, r) = half_leaf(&a, &b, k);
        let (x, y) = match pair {
            true => r.apply(&a, &b, j),
            false => (a, b),
        };
        return done(j, r, x, y);
    }
    let k1 = k / 2;
    let (j1, r1, a2, b2) = half_low(a, b, k1, lift);
    let j0 = match nu(&b2) {
        Some(v) if j1 + v <= k => v,
        _ => return done(j1, r1, a2, b2),
    };
    let (q, a3, b3) = step(&a2, &b2, j0);
    drop((a2, b2));
    let k2 = k - j1 - j0;
    let (j2, r2, last) = match pair {
        true => {
            let (j2, r2, a4, b4) = half_low(a3, b3, k2, lift);
            (j2, r2, Some((a4, b4)))
        }
        false => {
            let w = 2 * k2 + 1;
            let h = half(cmod(&a3, w), cmod(&b3, w), k2, Want::Matrix, lift);
            // Unreachable: `half` sets `r` when asked for `Want::Matrix`.
            (h.j, h.r.expect("asked for the matrix"), None)
        }
    };
    let j = j1 + j0 + j2;
    if !matrix {
        return Half {
            j,
            r: None,
            pair: last,
        };
    }
    // The step's matrix [[0, 2^j0], [2^j0, q]] times r1.
    let [m00, m01, m10, m11] = &r1.0;
    let qr1 = Mat([
        m10 << j0,
        m11 << j0,
        (m00 << j0) + mul_int(&q, m10),
        (m01 << j0) + mul_int(&q, m11),
    ]);
    drop(r1);
    Half {
        j,
        r: Some(r2.times(&qr1)),
        pair: last,
    }
}

/// [`half`] of `(a, b)` with budget `k`, found from their residues modulo `2^w`, `w = 2k + 1`,
/// centered: its matrix `R` and the pair `R (a, b) / 2^2j`. With
/// `(a, b) = (a_l, b_l) + 2^w (a_h, b_h)`, that pair is
/// `R (a_l, b_l) / 2^2j + 2^(w - 2j) R (a_h, b_h)`, as `2j < w`.
///
/// Complexity tradeoff: applying `R` (entries of about `k` bits) to the whole numbers
/// ([`Mat::apply`]) takes products by all `bits(a)` bits; lifting the residues' pair takes
/// them by the high parts only, `bits(a) - w` bits, but needs that pair, one more product of
/// a matrix by a pair inside the recursion. When the products are num-bigint's (entries of
/// at most `MUL_LEAF` words, where [`matrix_product`] takes them one by one), whose cost grows
/// with the product of the widths, the lift is cheaper (Möller's `hgcd-b`, step 7, "On
/// Schönhage's algorithm and subquadratic integer gcd computation", Math. Comp. 2008, §4;
/// cited in full in the module's "Sources"): [`bezout`] of
/// Fibonacci pairs takes 8 % fewer instructions at 356 words and 11 % fewer at 711. Above,
/// the transforms of [`Mat::apply`] are planned for the quotient, about `bits(a) - k` bits,
/// the same size as the lift's products, so the lift only adds the residues' pair: a gcd of
/// 33,220 words took 7 % more when every level lifted. So the lift is taken for entries of
/// at most `MUL_LEAF` words, `k` at most [`LIFT_BITS`] bits. Measured on 2026-11-12, a gcd of two
/// random odd numbers of 4,153 and of 33,220 words took 515.9 and 6,270.1 million
/// instructions; with the limit at half, 537.0 and 6,443.6, and at double, 521.9 and 6,344.5.
/// The same pair either way. Tests half_pairs_match_the_matrix and
/// pncx_fast_bezout_matches_euclid; reading_a_rat_of_two_wide_parts_scales is deferred to plan
/// row RADIX-nlog2-10_5 in wt/scratch/deferred-tests/RADIX-nlog2-10_5.rs.
fn half_low(a: BigInt, b: BigInt, k: u64, lift: u64) -> (u64, Mat, BigInt, BigInt) {
    // At the leaf the matrix has at most two words, and applying it to the whole numbers is
    // linear in their width, as a lift is.
    if k <= HALF_LEAF {
        return half(a, b, k, Want::Both, lift).both();
    }
    let w = 2 * k + 1;
    let (al, bl) = (cmod(&a, w), cmod(&b, w));
    if k > lift {
        let h = half(al, bl, k, Want::Matrix, lift);
        // Unreachable: `half` sets `r` when asked for `Want::Matrix`.
        let r = h.r.expect("asked for the matrix");
        let (x, y) = r.apply(&a, &b, h.j);
        return (h.j, r, x, y);
    }
    // `x >> w` rounds down, to `(x - r) / 2^w` for the residue `r` in `[0, 2^w)`; a negative
    // centered residue is `r - 2^w`, one more `2^w` in the high part.
    let ah = (a >> w) + BigInt::from(al.is_negative());
    let bh = (b >> w) + BigInt::from(bl.is_negative());
    let (j, r, x, y) = half(al, bl, k, Want::Both, lift).both();
    let [m00, m01, m10, m11] = &r.0;
    // Unreachable: `matrix_product` returns `2 c` entries for `c = r.len() / 2`, two here.
    let [c, d] = matrix_product([m00, m01, m10, m11], &[&ah, &bh], None)
        .try_into()
        .expect("a 2x1 product");
    let s = w - 2 * j;
    (j, r, x + (c << s), y + (d << s))
}

/// [`half`] on 128-bit integers, for `k <= HALF_LEAF`: the residues modulo `2^(2k+1)` stay
/// below `2^120` in size through the steps, since a step's new second number is at most the
/// sum of the two over `2^j`, and the matrix entries below `2^(2 j)`, since a step multiplies
/// their size by less than `2^(j+1)`.
fn half_leaf(a: &BigInt, b: &BigInt, k: u64) -> (u64, Mat) {
    let w = 2 * k + 1;
    let low = |x: &BigInt| -> i128 {
        let r = low128(x) & ((1u128 << w) - 1);
        match r >> (w - 1) {
            1 => r as i128 - (1i128 << w),
            _ => r as i128,
        }
    };
    let (mut x, mut y) = (low(a), low(b));
    let [mut m00, mut m01, mut m10, mut m11] = [1i128, 0, 0, 1];
    let mut j = 0u64;
    while y != 0 {
        let v = u64::from(y.trailing_zeros());
        if j + v > k {
            break;
        }
        let y1 = y >> v;
        // `q = -x / y1 mod 2^(v+1)`, centered.
        let inv = inverse_mod_2_64(y1 as u64);
        let t = (x as u64).wrapping_neg().wrapping_mul(inv) & ((1u64 << (v + 1)) - 1);
        let q = match t > 1 << v {
            true => i128::from(t) - (1i128 << (v + 1)),
            false => i128::from(t),
        };
        (x, y) = (y1, (x + q * y1) >> v);
        (m00, m01, m10, m11) = (
            m10 << v,
            m11 << v,
            (m00 << v) + q * m10,
            (m01 << v) + q * m11,
        );
        j += v;
    }
    (j, Mat([m00, m01, m10, m11].map(BigInt::from)))
}

#[cfg(test)]
thread_local! {
    static STEIN_ACCEPTED_SHIFT: std::cell::Cell<u32> = const {std::cell::Cell::new(0)};
    static STEIN_REJECTED_SHIFT: std::cell::Cell<u32> = const {std::cell::Cell::new(0)};
}
/// 2-adic Lehmer binary gcd on the positive odd parts `a >> za` and `b >> zb`: each outer pass
/// advances up to 30 halving steps in 128-bit registers from the low 128 bits (`[[m00, m01],
/// [m10, m11]]` with `|m_ij| < 2^62`, determinant `+-2^(2j)`) and applies the resulting signed
/// `i64` matrix to two reusable `u64` word buffers in one pass, dropping to 128-bit and 64-bit
/// Stein registers once both operands fit in two words, with no per-pass heap allocations.
fn stein_odd(a: &BigUint, za: u64, b: &BigUint, zb: u64) -> BigUint {
    fn odd_words(x: &BigUint, z: u64) -> Vec<u64> {
        let w = (z / 64) as usize;
        let sh = (z % 64) as u32;
        let mut v: Vec<u64> = x.iter_u64_digits().skip(w).collect();
        if sh != 0 && !v.is_empty() {
            for i in 0..v.len() - 1 {
                v[i] = (v[i] >> sh) | (v[i + 1] << (64 - sh));
            }
            if let Some(last) = v.last_mut() {
                *last >>= sh;
            }
        }
        while v.last() == Some(&0) {
            v.pop();
        }
        v
    }
    fn cmp_words(u: &[u64], v: &[u64]) -> std::cmp::Ordering {
        u.len().cmp(&v.len()).then_with(|| {
            for i in (0..u.len()).rev() {
                if u[i] != v[i] {
                    return u[i].cmp(&v[i]);
                }
            }
            std::cmp::Ordering::Equal
        })
    }
    fn shr_odd_in_place(u: &mut Vec<u64>) {
        while u.last() == Some(&0) {
            u.pop();
        }
        let Some(w) = u.iter().position(|&x| x != 0) else {
            u.clear();
            return;
        };
        let sh = u[w].trailing_zeros();
        let len = u.len() - w;
        if sh == 0 {
            if w != 0 {
                u.copy_within(w.., 0);
                u.truncate(len);
            }
        } else {
            for j in 0..len - 1 {
                u[j] = (u[j + w] >> sh) | (u[j + w + 1] << (64 - sh));
            }
            u[len - 1] = u[len - 1 + w] >> sh;
            u.truncate(len);
            while u.last() == Some(&0) {
                u.pop();
            }
        }
    }
    fn sub_shr_odd(u: &mut Vec<u64>, v: &[u64]) {
        let mut borrow = 0u64;
        for (ui, &vi) in u.iter_mut().zip(v) {
            let (d1, b1) = ui.overflowing_sub(vi);
            let (d2, b2) = d1.overflowing_sub(borrow);
            *ui = d2;
            borrow = u64::from(b1 | b2);
        }
        let mut i = v.len();
        while borrow != 0 {
            let (d, b) = u[i].overflowing_sub(1);
            u[i] = d;
            borrow = u64::from(b);
            i += 1;
        }
        shr_odd_in_place(u);
    }
    fn lin_shr_odd(out: &mut Vec<u64>, m0: i64, m1: i64, u: &[u64], v: &[u64]) {
        out.clear();
        let len = u.len().max(v.len());
        let (c0, c1) = (i128::from(m0), i128::from(m1));
        let mut carry = 0i128;
        for i in 0..len {
            let ui = i128::from(u.get(i).copied().unwrap_or(0));
            let vi = i128::from(v.get(i).copied().unwrap_or(0));
            let acc = carry + c0 * ui + c1 * vi;
            out.push(acc as u64);
            carry = acc >> 64;
        }
        if carry > 0 {
            out.push(carry as u64);
        } else if carry < 0 {
            out.push(carry as u64);
            let mut borrow = 0u64;
            for w in out.iter_mut() {
                let (d1, b1) = 0u64.overflowing_sub(*w);
                let (d2, b2) = d1.overflowing_sub(borrow);
                *w = d2;
                borrow = u64::from(b1 | b2);
            }
        }
        shr_odd_in_place(out);
    }
    let mut u = odd_words(a, za);
    let mut v = odd_words(b, zb);
    let mut c_buf: Vec<u64> = Vec::new();
    let mut d_buf: Vec<u64> = Vec::new();
    loop {
        if u.len() <= 2 && v.len() <= 2 {
            let mut uu = v128_from(&u);
            let mut vv = v128_from(&v);
            loop {
                if uu <= u128::from(u64::MAX) && vv <= u128::from(u64::MAX) {
                    let (mut a64, mut b64) = (uu as u64, vv as u64);
                    while a64 != b64 {
                        if a64 < b64 {
                            (a64, b64) = (b64, a64);
                        }
                        a64 -= b64;
                        a64 >>= a64.trailing_zeros();
                    }
                    return BigUint::from(a64);
                }
                if uu == vv {
                    return BigUint::from(uu);
                }
                if uu < vv {
                    (uu, vv) = (vv, uu);
                }
                uu -= vv;
                uu >>= uu.trailing_zeros();
            }
        }
        match cmp_words(&u, &v) {
            std::cmp::Ordering::Equal => return from_words(u),
            std::cmp::Ordering::Less => std::mem::swap(&mut u, &mut v),
            std::cmp::Ordering::Greater => {}
        }
        let mut x = v128_from(&u);
        let mut y = v128_from(&v).wrapping_sub(x);
        let [mut m00, mut m01, mut m10, mut m11] = [1i64, 0, -1, 1];
        let mut j = 0u32;
        while y != 0 {
            let tz = y.trailing_zeros();
            if j + tz > 30 {
                #[cfg(test)]
                STEIN_REJECTED_SHIFT.with(|v| v.set(v.get().max(j + tz)));
                break;
            }
            let y1 = y >> tz;
            let y1_64 = y1 as u64;
            let mut inv = 1u64;
            for _ in 0..6 {
                inv = inv.wrapping_mul(2u64.wrapping_sub(y1_64.wrapping_mul(inv)));
            }
            let mask = (1u64 << (tz + 1)) - 1;
            let t = (x as u64).wrapping_neg().wrapping_mul(inv) & mask;
            let q = if t > (1u64 << tz) {
                (t as i64) - (1i64 << (tz + 1))
            } else {
                t as i64
            };
            let q128 = (q as i128) as u128;
            (x, y) = (y1, x.wrapping_add(q128.wrapping_mul(y1)) >> tz);
            (m00, m01, m10, m11) = (
                m10 << tz,
                m11 << tz,
                (m00 << tz) + q * m10,
                (m01 << tz) + q * m11,
            );
            j += tz;
            #[cfg(test)]
            STEIN_ACCEPTED_SHIFT.with(|v| v.set(v.get().max(j)));
        }
        if j == 0 {
            sub_shr_odd(&mut u, &v);
        } else {
            lin_shr_odd(&mut c_buf, m00, m01, &u, &v);
            lin_shr_odd(&mut d_buf, m10, m11, &u, &v);
            if d_buf.is_empty() {
                return from_words(c_buf);
            }
            std::mem::swap(&mut u, &mut c_buf);
            std::mem::swap(&mut v, &mut d_buf);
        }
    }
}

fn v128_from(v: &[u64]) -> u128 {
    u128::from(v[0]) | (v.get(1).copied().map_or(0, u128::from) << 64)
}

/// The greatest common divisor of `a` and `b`. The powers of 2 are taken out first; the odd
/// parts then go through the binary gcd, half of what is left at a time by [`half`], whose
/// steps keep the odd part of the gcd. O(M(n) log n).
pub(crate) fn gcd(a: &BigUint, b: &BigUint) -> BigUint {
    gcd_using(a, b, GCD_LEAF, LIFT_BITS)
}

fn gcd_using(a: &BigUint, b: &BigUint, leaf: u64, lift: u64) -> BigUint {
    let (Some(za), Some(zb)) = (a.trailing_zeros(), b.trailing_zeros()) else {
        return a | b;
    };
    let z = za.min(zb);
    if (a.bits() - za).max(b.bits() - zb) <= leaf {
        return stein_odd(a, za, b, zb) << z;
    }
    let mut x = BigInt::from(a >> za);
    let mut y = BigInt::from(b >> zb) - &x;
    let _hold = HoldRoots::open();
    // Complexity tradeoff: the half gcd costs O(M(n) log n) = O(n log^2 n), a log factor above
    // a product, accepted because no faster gcd is known: the subquadratic gcds (Schönhage 1971;
    // the binary recursive gcd of Stehlé and Zimmermann, ANTS 2004, used here; Möller 2008;
    // all in the module's "Sources") all take O(M(n) log n) (author decision A47, 2026-11-09;
    // COMPLEXITY.md C31). The scaling test holds it to the limit of work of order n log^2 n.
    // Below `GCD_LEAF`, `stein_odd` runs 2-adic Lehmer passes (up to 30 halvings per pass in
    // 128-bit registers, applied in one pass over two reusable word buffers) and drops to
    // 128-bit and 64-bit Stein registers once both operands fit in two words, avoiding
    // num-bigint's per-step shift allocations while keeping O(n^2) bounded to the leaf width
    // with a 30x smaller pass count.
    // Measured on 2026-11-06: 1.8 s at 32768 words, 11.0 s at 131072; Stein's gcd is faster
    // below about 300 words at load 1 (2026-11-06), 512 to 1024 at load 45 to 75 (2026-11-05);
    // see `GCD_LEAF`. Test `a_gcd_of_wide_numbers_scales`, deferred to plan row
    // RADIX-nlog2-10_5 in wt/scratch/deferred-tests/RADIX-nlog2-10_5.rs.
    while !y.is_zero() {
        let n = x.bits().max(y.bits());
        if n <= leaf {
            let (xm, ym) = (x.magnitude(), y.magnitude());
            // Unreachable: `y` is not zero by the loop's test, and `x` stays odd (the binary
            // gcd's invariant: it starts as `a >> za` and each step makes it `b / 2^j`), so
            // each has a lowest set bit.
            let zx = xm.trailing_zeros().expect("x is odd");
            let zy = ym.trailing_zeros().expect("y is not zero");
            return (stein_odd(xm, zx, ym, zy) << zx.min(zy)) << z;
        }
        // Unreachable: `half` sets `pair` when asked for `Want::Pair`.
        (x, y) = half(x, y, n / 2, Want::Pair, lift)
            .pair
            .expect("asked for the pair");
        if let Some(v) = nu(&y) {
            let (_, a1, b1) = step(&x, &y, v);
            (x, y) = (a1, b1);
        }
    }
    x.magnitude() << z
}

/// `a^-1 mod m` for `m` above zero, or `None` when `a` and `m` have a common factor. The odd
/// part `o` of `m` by [`inverse_mod_odd`], the power `2^e` by [`inverse_mod_pow2`], joined by
/// the Chinese remainder theorem: `x = x1 + o ((x2 - x1) o^-1 mod 2^e)`, below `o 2^e = m`.
/// O(M(n) log n). Panics with "a modulus above 0" for `m` zero.
pub(crate) fn inverse_mod(a: &BigUint, m: &BigUint) -> Option<BigUint> {
    // `m = 0` had `trailing_zeros` give `None`, so the answer was `None` for every `a`: wrong
    // for `a = 1`, which is its own inverse in the integers (the ring modulo 0), and silent.
    // No caller passes it (the one in zedc-presburger, `modular::inverse_mod`, reduces `a` by
    // `m` first, which already panics on zero), so the precondition the doc states is now
    // checked (TEST-dry-shared-units, `units::refused::an_inverse_mod_zero`).
    assert!(!m.is_zero(), "a modulus above 0");
    // Unreachable: `m` is not zero, so it has a lowest set bit.
    let e = m.trailing_zeros().expect("a modulus above 0 has a set bit");
    let o = m >> e;
    let x1 = match o.is_one() {
        true => BigUint::zero(),
        false => inverse_mod_odd(&rem(a, &o), &o)?,
    };
    if e == 0 {
        return Some(x1);
    }
    if !a.bit(0) {
        return None;
    }
    let mask = (BigUint::one() << e) - 1u32;
    let x2 = inverse_mod_pow2(a, e);
    let d = (x2 + &mask + 1u32 - (&x1 & &mask)) & &mask;
    let t = mul(&d, &inverse_mod_pow2(&o, e)) & &mask;
    Some(x1 + mul(&o, &t))
}

/// `a^-1 mod b` for `b` odd and above 1 and `a` below `b`, or `None` when they have a common
/// factor. The binary gcd of `(b, y0)`, `y0` being `a` or `a - b`, whichever is even, is run
/// as in [`gcd`] but down to `y = 0`, with no leaf of [`GCD_LEAF`] (the leaf of [`half`] is
/// [`half_leaf`]), and the second column `(c0, c1)` of the product `T` of its steps is kept:
/// each pair it reaches is `T (b, y0) / 2^e`, so modulo `b` it is `(c0, c1) y0 / 2^e`. At the
/// end `x = ±g`; with `g = 1`, `x c0 2^-e` is the inverse of `y0`, which is `a` modulo `b`.
/// `2^-e mod b` is `(1 + b s) / 2^e` with `s = -b^-1 mod 2^e`. O(M(n) log n), as [`gcd`].
fn inverse_mod_odd(a: &BigUint, b: &BigUint) -> Option<BigUint> {
    let bi = BigInt::from(b.clone());
    let mut x = bi.clone();
    let mut y = BigInt::from(a.clone());
    if a.bit(0) {
        y -= &bi;
    }
    let (mut c0, mut c1) = (BigInt::zero(), BigInt::one());
    let mut e = 0u64;
    while !y.is_zero() {
        let n = x.bits().max(y.bits());
        let (j, r, x1, y1) = half(x, y, n / 2, Want::Both, LIFT_BITS).both();
        (x, y) = (x1, y1);
        if j > 0 {
            let [m00, m01, m10, m11] = &r.0;
            (c0, c1) = (
                mul_int(m00, &c0) + mul_int(m01, &c1),
                mul_int(m10, &c0) + mul_int(m11, &c1),
            );
            e += 2 * j;
        }
        drop(r);
        if let Some(v) = nu(&y) {
            let (q, a1, b1) = step(&x, &y, v);
            (x, y) = (a1, b1);
            (c0, c1) = (&c1 << v, (&c0 << v) + mul_int(&q, &c1));
            e += 2 * v;
        }
    }
    if !x.magnitude().is_one() {
        return None;
    }
    let num = c0 * x;
    let r = rem(num.magnitude(), b);
    let r = match num.is_negative() && !r.is_zero() {
        true => b - r,
        false => r,
    };
    let two_inv = match e {
        0 => BigUint::one(),
        _ => {
            let s = (BigUint::one() << e) - inverse_mod_pow2(b, e);
            (BigUint::one() + mul(b, &s)) >> e
        }
    };
    Some(rem(&mul(&r, &two_inv), b))
}

/// Extended binary half-GCD on nonnegative inputs. The half-GCD's matrix
/// acts on the pair over a power of two. Only its coefficient of the second
/// input is accumulated; an exact division recovers the other coefficient.
// Complexity tradeoff: extended Euclid uses O(n^2) bit operations, while
// separately computing the gcd and an inverse repeats the half-GCD. This
// computes both in one O(M(n) log n) pass. Total: the halving count cannot overflow (proof at
// `bezout_with`, step 6). Tests: pncx_fast_bezout_matches_euclid and
// bezout_coefficients_with_unequal_widths; pncx_fibonacci_scale is deferred to plan row
// PERF-negated-chain-unsolved in wt/scratch/deferred-tests/PERF-negated-chain-unsolved.rs.
pub(super) fn bezout(a: &BigUint, b: &BigUint) -> (BigUint, BigInt, BigInt) {
    bezout_with(a, b, LIFT_BITS)
}

/// [`bezout`] with the lift of [`half_low`] up to `lift` bits in place of [`LIFT_BITS`].
fn bezout_with(a: &BigUint, b: &BigUint, lift: u64) -> (BigUint, BigInt, BigInt) {
    let (Some(za), Some(zb)) = (a.trailing_zeros(), b.trailing_zeros()) else {
        return (
            a | b,
            BigInt::from(!a.is_zero()),
            BigInt::from(!b.is_zero()),
        );
    };
    let common = za.min(zb);
    let (a, b) = (a >> common, b >> common);
    let swapped = !a.bit(0);
    let (u, v) = if swapped { (&b, &a) } else { (&a, &b) };
    let mut x = BigInt::from(u.clone());
    let mut y = BigInt::from(v.clone());
    if v.bit(0) {
        y -= &x;
    }
    let (mut bx, mut by) = (BigInt::zero(), BigInt::one());
    // Bound on `halvings`, every step. N = max(a.bits(), b.bits()).
    // 1. The pair is the GB remainder sequence of Stehlé and Zimmermann (ANTS 2004, sec. 2.3,
    //    doi:10.1007/978-3-540-24847-7_31), normalized: r_0 = x, r_1 = y (ν2(r_0) = 0 <
    //    ν2(r_1)), r_{i+1} = r_{i-1} + q_i r_i / 2^{n_i}, n_i = ν2(r_i) - ν2(r_{i-1}) >= 1,
    //    q_i the GB quotient of Lemma 1, |q_i| < 2^{n_i}. After i steps (x, y) = (r_i,
    //    r_{i+1}) / 2^{ν2(r_i)}, by induction: from the pair after i - 1 steps, `y` has
    //    valuation n_i, and `step` with j = n_i gives (r_i / 2^{ν2(r_i)}, (r_{i-1} + q_i r_i /
    //    2^{n_i}) / 2^{ν2(r_i)}); `half` takes the same steps, its `j` their n_i summed.
    // 2. So `halvings` = n_1 + ... + n_i = ν2(r_i), and when y = 0 it is ν2(r_t), r_t the
    //    last nonzero term; every partial sum is at most that.
    // 3. |r_{i+1}| <= |r_{i-1}| + |r_i|, so |r_i| <= F_{i+1} M <= φ^i M, M = max(|r_0|,
    //    |r_1|) < 2^N (r_0 = u, |r_1| <= max(u, v), both at most max(a, b)), F Fibonacci
    //    with F_1 = F_2 = 1, φ the golden ratio (F_{i+1} <= φ^i by induction).
    // 4. t <= ν2(r_t) = ν since each n_i >= 1, and 2^ν <= |r_t| since 2^ν divides r_t != 0.
    // 5. 2^ν <= φ^t M <= φ^ν M, so (2/φ)^ν <= M < 2^N; (2/φ)^4 = 16/φ^4 > 2 (φ^4 = 3φ + 2
    //    < 7), so ν >= 4N would give (2/φ)^ν > 2^N: ν < 4N.
    // (The paper's Theorem 3 gives about 1.555 N, for j >= 9, proved there in sketch only;
    // 4N is enough here.)
    // 6. `halvings` and `shift = 2 halvings` fit in u128 on every target, so the sums below
    //    cannot overflow (PROOF-bezout-halvings-address-width). A `BigUint` holds its value in
    //    a `Vec` of 64-bit digits, and its `bits()` is `data.len() * 64 - zeros` (num-bigint
    //    0.4.8 src/biguint.rs `bits`, read 2026-11-21). Rust allocates no block larger than
    //    isize::MAX bytes: std::alloc::Layout, "`size`, when rounded up to the nearest
    //    multiple of `align`, must not overflow `isize` (i.e., the rounded value must be less
    //    than or equal to `isize::MAX`)" (https://doc.rust-lang.org/std/alloc/struct.Layout.html,
    //    read 2026-11-21, std 1.100.0). So `data.len() <= isize::MAX / 8 < 2^60` and N < 2^66
    //    on any target whose `isize` has at most 64 bits; by steps 2 and 5 every partial sum of
    //    `halvings` is below 4N < 2^68, and `shift` below 2^69 < 2^128. (num-bigint's own
    //    `bits()` would wrap in u64 for N >= 2^64, a limit of that library this code does not
    //    reach past: `j` and `m` are its u64 counts, and only their sums here need more room.)
    //    The earlier u64 count needed N < 2^61, true of the x86_64 and aarch64 address spaces
    //    but not proved for every 64-bit target, and answered None past it.
    //    Test: pncx_fast_bezout_matches_euclid checks the answers; no test can hold an input
    //    of 2^61 bits, so the bound itself rests on this proof alone.
    let mut halvings = 0u128;
    while !y.is_zero() {
        let n = x.bits().max(y.bits());
        let (j, r, x1, y1) = half(x, y, (n / 2).max(1), Want::Both, lift).both();
        (x, y) = (x1, y1);
        if j > 0 {
            let [m00, m01, m10, m11] = &r.0;
            (bx, by) = (
                mul_int(m00, &bx) + mul_int(m01, &by),
                mul_int(m10, &bx) + mul_int(m11, &by),
            );
            halvings += u128::from(j);
        }
        drop(r);
        if let Some(j) = y.trailing_zeros() {
            let (q, a1, b1) = step(&x, &y, j);
            (bx, by) = (&by << j, (&bx << j) + mul_int(&q, &by));
            (x, y) = (a1, b1);
            halvings += u128::from(j);
        }
    }
    let g = x.magnitude();
    let modulus = div_rem(u, g).0;
    let m = modulus.bits();
    let (v_coefficient, inverse) = if modulus.is_one() {
        (BigUint::zero(), BigUint::one())
    } else {
        let coefficient = if x.is_negative() { -bx } else { bx };
        let c = rem(coefficient.magnitude(), &modulus);
        let mut c = if coefficient.is_negative() && !c.is_zero() {
            &modulus - c
        } else {
            c
        };
        // Divide c by 2^shift modulo the odd modulus without another gcd, in chunks of at
        // most `m` bits, `m` the modulus's width: c + k modulus is divisible by 2^s, with
        // 0 < k < 2^s, k = -c modulus^-1 mod 2^s, when c is not 0 mod 2^s. Each chunk keeps
        // c below 2 modulus, so one subtraction ends below the modulus.
        // Complexity tradeoff: one chunk of all `shift` bits needs modulus^-1 to `shift` bits,
        // O(M(shift)) even for a small modulus; chunks of `m` bits reuse one inverse of `m`
        // bits and cost O((shift / m + 1) M(m)), no more. Test pncx_fast_bezout_matches_euclid.
        let mut shift = 2 * halvings;
        let inverse = inverse_mod_pow2(&modulus, m);
        while shift > 0 {
            // At most `m`, a u64, so the conversion back is exact.
            let s = shift.min(u128::from(m)) as u64;
            let mask = (BigUint::one() << s) - 1u32;
            let low = &c & &mask;
            if !low.is_zero() {
                let k = (&mask + 1u32) - (mul(&low, &inverse) & &mask);
                c = (c + mul(&k, &modulus)) >> s;
            } else {
                c >>= s;
            }
            shift -= u128::from(s);
        }
        if c >= modulus {
            c -= &modulus;
        }
        debug_assert!(c < modulus);
        (c, inverse)
    };
    // The other coefficient is (g - t v) / u = (1 - t V) / U for U = u / g and V = v / g,
    // an exact quotient q of A = |1 - t V| by the odd U of `m` bits. Its low `m` bits are
    // A U^-1 mod 2^m, from the inverse above; its high bits are floor((A >> m) / U), since
    // A = U (q_high 2^m + q_low) with q_low U < 2^m U.
    // Complexity tradeoff: dividing g - t v by u, about 2n bits by n, costs a general
    // division, O(M(n)) with a large constant (about an eighth of the call at 356 words);
    // the low bits cost one product of m bits, and the high part divides only the bits of A
    // above m, under the width of V, so nothing for balanced inputs. Test
    // bezout_coefficients_with_unequal_widths.
    let second = BigInt::from(v_coefficient);
    let reduced_v = match g.is_one() {
        true => Cow::Borrowed(v),
        false => Cow::Owned(div_rem(v, g).0),
    };
    let numerator = BigInt::one() - BigInt::from(mul(second.magnitude(), &reduced_v));
    let a_mag = numerator.magnitude();
    let mask = (BigUint::one() << m) - 1u32;
    let low = mul(&(a_mag & &mask), &inverse) & mask;
    let high = div_rem(&(a_mag >> m), &modulus).0;
    let first = BigInt::from_biguint(numerator.sign(), (high << m) + low);
    let (s, t) = if swapped {
        (second, first)
    } else {
        (first, second)
    };
    (g << common, s, t)
}

// ------------------------------------------------------------------------------------------
// Decimal printing

/// A divisor used many times, with how it is divided by, chosen as [`div_rem`] chooses for the
/// widest dividend it is made for: num-bigint's division when it has at most [`DIV_LEAF`] bits
/// or costs least, long division over its nonzero words when that costs less than the
/// reciprocal, else a [`Level`]: its reciprocal and itself transformed once, with the roots for
/// every product.
pub(crate) struct Divisor<'a> {
    d: Cow<'a, BigUint>,
    /// The words of `d`.
    len: usize,
    by: By,
}

enum By {
    Leaf,
    Sparse,
    Reciprocal(Box<Level>, Rc<Roots>),
}

/// How a [`Divisor`] of `d` for dividends of at most `a_bits` bits divides.
enum Way {
    /// num-bigint's division, for at most [`DIV_LEAF`] bits or where it costs least.
    Leaf,
    /// Long division over the nonzero words, where it costs less than the reciprocal.
    Sparse,
    /// A [`Level`] on this many points.
    Reciprocal(usize),
}

/// The way a [`Divisor`] of `d` for dividends of at most `a_bits` bits divides.
fn divisor_way(d: &BigUint, a_bits: u64) -> Way {
    let (n, len) = (d.bits(), words(d));
    // Complexity tradeoff: the choice `div_rem` makes for the whole quotient, of at least
    // `len` words, by the same computed costs and with no size constant, so that a quotient
    // `div_rem` costed by the reciprocal is divided by it. It was the choice for one division
    // of `2 len` words by `d`, which charges the making of the reciprocal to one step, with no
    // num-bigint past `DIV_LEAF`: a quotient of 256 times the divisor's words then went by long
    // division from 91 to 235 words, 1.9 to 2.6 times num-bigint's work, where `div_rem` had
    // costed the reciprocal (CROSSOVER-bench, `crossover div-leaf 256 1`, 2026-11-12;
    // COMPLEXITY.md K30).
    // The quotient's words as `div_rem` counts them, `words(a) - words(d) + 1`; the `+ 1` was
    // missing, so the costs here read a dividend one word narrower than `div_rem`'s
    // (DRY-numeric-shared-rest, 2026-11-20).
    let qw = ((a_bits.div_ceil(64) as usize).saturating_sub(len) + 1).max(len);
    if n <= DIV_LEAF || num_bigint_divides(qw, d) {
        return Way::Leaf;
    }
    if sparse_div_cost(qw, d) <= newton_cost(qw, len) {
        return Way::Sparse;
    }
    let (linear, cyclic) = level_points(n, n);
    Way::Reciprocal(linear.max(cyclic))
}

/// The points of the transforms a [`Divisor`] of `d` for dividends of at most `a_bits` bits
/// keeps, the most of its [`level_points`], or `None` when it divides without them (see
/// [`Way`]). Its memory is a multiple of these points (`num::Rat::rem_euclid` and
/// `num::Rat::div_euclid` ask for it).
pub(crate) fn reciprocal_points(d: &BigUint, a_bits: u64) -> Option<usize> {
    match divisor_way(d, a_bits) {
        Way::Reciprocal(points) => Some(points),
        Way::Leaf | Way::Sparse => None,
    }
}

impl<'a> Divisor<'a> {
    /// `d`, for dividends of at most `a_bits` bits.
    pub(crate) fn new(d: Cow<'a, BigUint>, a_bits: u64) -> Divisor<'a> {
        assert!(!d.is_zero(), "a division by zero");
        let way = divisor_way(&d, a_bits);
        Divisor::with_way(d, way)
    }

    /// `d`, not zero, dividing the way `way` says.
    fn with_way(d: Cow<'a, BigUint>, way: Way) -> Divisor<'a> {
        let by = match way {
            Way::Leaf => By::Leaf,
            Way::Sparse => By::Sparse,
            Way::Reciprocal(points) => {
                let tw = roots(points);
                let n = d.bits();
                By::Reciprocal(Box::new(Level::new(d.to_u64_digits(), n, n, &tw)), tw)
            }
        };
        Divisor {
            len: words(&d),
            d,
            by,
        }
    }

    /// `(a / d, a mod d)`, by [`Divisor::blocks`].
    pub(crate) fn div_rem(&self, a: &BigUint) -> (BigUint, BigUint) {
        let mut quotient = vec![0u64; words(a)];
        let r = self.blocks(a, |at, q| quotient[at..at + q.len()].copy_from_slice(q));
        (from_words(quotient), from_words(r))
    }

    /// `a mod d`, by [`Divisor::blocks`], its memory that of `d` whatever the size of `a`.
    pub(crate) fn rem(&self, a: &BigUint) -> BigUint {
        from_words(self.blocks(a, |_, _| {}))
    }

    /// The words of `a mod d`, `a` read from the top in blocks of as many words as `d` has:
    /// each step divides the remainder so far joined to the next block, below `d 2^(64 len)`,
    /// by `d` ([`Divisor::step`]), and gives the words of its quotient to `put` with the place
    /// of their lowest word in `a / d`. The words of each step are built in one buffer, so a
    /// step copies nothing of `a` but its block. O((m / n) M(n)) for `m` bits by `n`.
    fn blocks(&self, a: &BigUint, mut put: impl FnMut(usize, &[u64])) -> Vec<u64> {
        let len = self.len;
        let mut digits = a.iter_u64_digits();
        let mut left = digits.len();
        let take = match left % len {
            0 => len.min(left),
            k => k,
        };
        // The first block has at most `len` words, so its quotient is below `2^64` and long
        // division ([`sparse_div_rem_words`], Knuth's algorithm D over `d`'s nonzero words)
        // finds it in one step of O(n) word products, where the reciprocal would cost a
        // product; every later step has a quotient as wide as `d`. Fewer than `len - 1` words
        // are below `d`, the quotient 0, as in `Divisor::step`.
        //
        // Complexity tradeoff (PERF-div-bytes-2p17): this block went to num-bigint's division,
        // taken here for long division. num-bigint 0.4.8 divides by Burnikel and Ziegler's
        // recursive division once the dividend has more than 128 words and the divisor more
        // than 64 (`div_rem_core`, `BURNIKEL_ZIEGLER_THRESHOLD`), whatever the quotient's
        // width, so a one-word quotient cost its full recursion: Toom-3 products, O(n^1.465),
        // and 368 to 496 bytes allocated a word of `d` at 2^16, 2^19 and 2^20 words, against 32
        // at 2^17, where the seed's block fell below `d` and num-bigint returned at once
        // (b22-kernelb5, the bytes of each phase of one division, 2026-11-22). That made
        // `dividing_a_wide_number_scales` allocate 11.9 times the bytes from 2^17 to 2^20
        // words. Long division costs O(n) time and about 6n words of memory (the shifted
        // divisor, its nonzero places, the window and the remainder), with the same quotient
        // and remainder; tested by
        // `tests::wide_quotients_agree_with_num_bigint` and
        // `tests::a_divisors_first_block_divides_in_linear_bytes`. A divisor of one word
        // (long division needs two) divides its one-word block by num-bigint's O(1) word
        // division (`tests::the_cost_of_the_blocks_counts_the_blocks_read` at `bw` 1).
        let mut x: Vec<u64> = digits.by_ref().rev().take(take).collect();
        x.reverse();
        left -= take;
        let (q, mut r) = if x.len() + 1 < len {
            (Vec::new(), x)
        } else if len < 2 {
            let (q, r) = from_words(x).div_rem(&*self.d);
            (q.to_u64_digits(), r.to_u64_digits())
        } else {
            sparse_div_rem_words(x.into_iter(), &self.d)
        };
        put(left, &q);
        let mut x: Vec<u64> = Vec::with_capacity(2 * len);
        while left > 0 {
            // `x = r 2^(64 len) + block`, the block's words read from the top.
            x.clear();
            x.resize(len, 0);
            for (slot, w) in x.iter_mut().rev().zip(digits.by_ref().rev()) {
                *slot = w;
            }
            x.extend_from_slice(&r);
            trim(&mut x);
            left -= len;
            let (q, rest) = self.step(&x);
            put(left, &q);
            r = rest;
        }
        r
    }

    /// `(x / d, x mod d)` as words with no zero on top, for the words `x`, with no zero on
    /// top, below `d 2^(64 len)`: num-bigint's division, long division over `d`'s nonzero
    /// words ([`sparse_div_rem`]), or a [`Level`] ([`Level::div_rem`]), O(M(n)), about one
    /// product's transforms of `d`'s width.
    fn step(&self, x: &[u64]) -> (Vec<u64>, Vec<u64>) {
        match &self.by {
            By::Leaf => {
                let (q, r) = from_words(x.to_vec()).div_rem(&*self.d);
                (q.to_u64_digits(), r.to_u64_digits())
            }
            // Long division needs at least `len - 1` words; fewer are below `d`.
            By::Sparse => match x.len() + 1 < self.len {
                true => (Vec::new(), x.to_vec()),
                false => sparse_div_rem_words(x.iter().copied(), &self.d),
            },
            By::Reciprocal(level, tw) => {
                debug_assert!(
                    x.len() <= level.d.len() + level.yw,
                    "x is below d 2^(64 len)"
                );
                level.div_rem(x, tw)
            }
        }
    }
}

/// One table of roots for each prime of [`FIELDS`] (see [`Field::twiddles`]).
type Roots = [Vec<(u64, u64)>; 3];

/// The roots [`roots`] built last on a thread, and the scopes that keep them.
struct Kept {
    /// The table, while something holds it: a product while it runs, a [`Factor`] or a
    /// printer's level that keeps spectra, or `held`. A table serves every smaller power of
    /// two (see [`Field::twiddles`]), so while it is held it is not built again. Only a weak
    /// reference is kept for the thread: a table of three words a point of the widest
    /// transform, held for the thread's life, would stay counted against the memory limit
    /// after the operation that built it ended (and failed
    /// `a_wide_number_modulo_a_wide_one_answers_when_its_peak_is_given`).
    table: Weak<Roots>,
    /// The table, held while `holds` is above zero.
    held: Option<Rc<Roots>>,
    /// How many [`HoldRoots`] scopes are open on the thread.
    holds: u32,
}

thread_local! {
    static ROOTS: std::cell::RefCell<Kept> = const {
        std::cell::RefCell::new(Kept { table: Weak::new(), held: None, holds: 0 })
    };
}

/// While it lives, [`roots`] keeps the table it built last, so that products run one after
/// another, as the gcd's matrix products are, share one table instead of each building its
/// own. Opened for one operation and dropped at its end, which frees the table once nothing
/// else holds it. Measured, `reading_a_rat_of_two_wide_parts_scales` at 640,000 digits:
/// 7,620 M instructions without it, 7,558 M with it (that test is deferred to plan row
/// RADIX-nlog2-10_5 in wt/scratch/deferred-tests/RADIX-nlog2-10_5.rs).
pub(super) struct HoldRoots;

impl HoldRoots {
    fn open() -> HoldRoots {
        ROOTS.with(|kept| kept.borrow_mut().holds += 1);
        HoldRoots
    }
}

impl Drop for HoldRoots {
    fn drop(&mut self) {
        ROOTS.with(|kept| {
            let mut kept = kept.borrow_mut();
            kept.holds -= 1;
            if kept.holds == 0 {
                kept.held = None;
            }
        });
    }
}

/// The roots of [`FIELDS`] for transforms of up to `n` points, a power of two: those of two
/// points for `n = 1`, whose transform is itself but whose table [`Field::forward`] checks.
/// The table [`ROOTS`] refers to when it is still held and wide enough, else a new one,
/// which an open [`HoldRoots`] keeps.
fn roots(n: usize) -> Rc<Roots> {
    ROOTS.with(|kept| {
        let mut kept = kept.borrow_mut();
        match kept.table.upgrade() {
            Some(tw) if 2 * tw[0].len() >= n => tw,
            _ => {
                let tw = Rc::new(roots_of(n));
                kept.table = Rc::downgrade(&tw);
                if kept.holds > 0 {
                    kept.held = Some(Rc::clone(&tw));
                }
                tw
            }
        }
    })
}

/// The roots of [`FIELDS`] for transforms of exactly `n.max(2)` points, built.
fn roots_of(n: usize) -> Roots {
    FIELDS.each_ref().map(|f| f.twiddles(n.max(2)))
}

/// The [`Field::spectrum`] of the words `x` for each prime of [`FIELDS`], on `n` points, `x`
/// folded modulo `2^(64 n) - 1` when it has more words.
fn spectra(x: &[u64], n: usize, tw: &Roots) -> [Vec<u64>; 3] {
    let x = folded(x, n);
    [0, 1, 2].map(|k| FIELDS[k].spectrum(&x, n, &tw[k]))
}

/// `x` folded modulo `2^(64 m) - 1` ([`fold_words`]) when it has more than `m` words, else
/// itself.
fn folded(x: &[u64], m: usize) -> Cow<'_, [u64]> {
    match x.len() > m {
        true => Cow::Owned(fold_words(x, m)),
        false => Cow::Borrowed(x),
    }
}

/// The points of the cyclic products modulo `M = 2^(64 m) - 1` that find a number `v`,
/// `|v| < 2^(bits + 6)`, from its residue modulo `M` and its low word ([`unfold`]): the least
/// power of two `m` with `64 m >= bits - 55`, so that `|v|` is below `2^(64 m + 61)`. The
/// widest use is [`newton`]'s `xh tm < 2^(2h + 2) <= 2^(p + 6)`.
fn cyclic_points(bits: u64) -> usize {
    let words = bits.saturating_sub(55).div_ceil(64).max(1);
    // Unreachable: a number of `bits` bits in memory has fewer words than a `usize` counts.
    usize::try_from(words)
        .expect("a number whose words fit in memory")
        .next_power_of_two()
}

/// The points of the two products of a [`Level`] for a divisor of `bits` bits whose top `k`
/// bits give the reciprocal: the estimate's, on the `2 yw` words of a product of two numbers of
/// `yw` words, `k` bits' words, and the remainder's ([`cyclic_points`]); the reciprocal's own
/// need no more than the first.
fn level_points(bits: u64, k: u64) -> (usize, usize) {
    // Unreachable: a reciprocal of `k` bits in memory has fewer words than a `usize` counts.
    let yw = usize::try_from(k.div_ceil(64)).expect("a number whose words fit in memory");
    ((2 * yw).next_power_of_two(), cyclic_points(bits))
}

/// `2^e mod (2^(64 m) - 1)`, as `m` words: one bit.
fn power_around(e: u64, m: usize) -> Vec<u64> {
    let mut power = vec![0u64; m];
    let at = e % (64 * m as u64);
    power[(at / 64) as usize] = 1 << (at % 64);
    power
}

/// `2^e mod 2^64`.
fn low_power(e: u64) -> u64 {
    match e < 64 {
        true => 1 << e,
        false => 0,
    }
}

/// The lowest word of `x`, zero for no words.
fn first(x: &[u64]) -> u64 {
    x.first().copied().unwrap_or(0)
}

/// The number `v`, as whether it is below zero and the words of `|v|`, from `r`, `v` modulo
/// `M = 2^(64 m) - 1` in at most `m` words (`M` itself allowed), and `low`, `v` modulo `2^64`,
/// for `|v| < 2^(64 m + 61)`. With `v = r + j M`, `M = -1` modulo `2^64` gives
/// `j = r - low` modulo `2^64`, and `|j| <= |v| / M + 1 < 2^62`, so `j` is that residue read
/// as signed. O(m).
fn unfold(mut r: Vec<u64>, m: usize, low: u64) -> (bool, Vec<u64>) {
    let j = first(&r).wrapping_sub(low) as i64;
    let k = j.unsigned_abs();
    r.resize(m + 1, 0);
    let negative = j < 0;
    if negative {
        // `|v| = k M - r`, computed modulo `2^(64 (m + 1))`, which holds it: `-r`, then
        // `k 2^(64 m) - k` added.
        for v in r.iter_mut() {
            *v = !*v;
        }
        add_at(&mut r, 0, 1);
    }
    // `v = r + k 2^(64 m) - k`, or `|v|` as above; the borrow past the top, if any, cancels
    // the carry into the top word, both modulo `2^(64 (m + 1))`.
    r[m] = r[m].wrapping_add(k);
    sub_at(&mut r, 0, k);
    trim(&mut r);
    (negative && !r.is_empty(), r)
}

/// The remainder `x - q d`, as whether it is below zero and the words of its magnitude, from
/// its residue modulo `M = 2^(64 m) - 1`, where `q d` is a cyclic product with `d`'s spectra
/// `dc` on `m` points, and its low word ([`unfold`]), for `|x - q d| < 2^(64 m + 61)`.
fn remainder(x: &[u64], d: &[u64], dc: &[Vec<u64>; 3], q: &[u64], tw: &Roots) -> (bool, Vec<u64>) {
    let m = dc[0].len();
    let (mut qd, carry) = cyclic_product(&folded(q, m), dc, tw);
    add_around(&mut qd, carry);
    let r = sub_around(fold_words(x, m), &qd);
    let low = first(x).wrapping_sub(first(q).wrapping_mul(first(d)));
    unfold(r, m, low)
}

/// The decimal digits of `x`, as num-bigint writes them: by num-bigint whole below
/// [`PRINT_WHOLE`] words, in O(n^1.5), and by halves ([`to_decimal_split`]) from there, in
/// O(M(n) log n) = O(n log^2 n).
pub fn to_decimal(x: &BigUint) -> String {
    // Complexity tradeoff: the naive method, num-bigint's printing of the whole number, costs
    // O(n^1.5) (Toom-3 products under Burnikel and Ziegler's division, about 2.85 times per
    // doubling of the words); the split costs O(M(n) log n) = O(n log^2 n), but its fixed
    // costs (the powers, the levels' transforms, one Newton reciprocal) make it slower below
    // `PRINT_WHOLE` words. The crossover is set by the benchmark `crossover print-whole`
    // (crate zed-benches; COMPLEXITY.md K81) and set again on each target platform. The two
    // methods print the same digits.
    if words(x) < PRINT_WHOLE {
        return x.to_string();
    }
    to_decimal_split(x)
}

/// The decimal digits of `x` by halves, at any size: `x = high * 10^(L 2^i) + low`, `L` being
/// 597, each half written alone and the low half padded with zeros to its width. The widest
/// power, which divides once, is divided by a reciprocal of only the quotient's precision; the
/// next power down has one Newton reciprocal, and each power below it has its reciprocal
/// derived from the one above by one product and one cyclic product, transformed once and
/// reused by every division at its level. O(M(n) log n), the recursion `log2(n / L)` deep; the
/// leaves, below powers of at most [`PRINT_HANDOFF`] words, are written by num-bigint. The text
/// is num-bigint's. [`to_decimal`] uses it from [`PRINT_WHOLE`] words; the tests and the
/// benchmark call it to force the split below there.
///
/// Proof of the bound, `x` of `n` words, `h` = [`PRINT_HANDOFF`]: the recursion has `L =
/// log2(n / h)` levels, and level `i` from the top divides `2^i` parts of about `n / 2^i` words
/// by one power, each a bounded number of products and one cyclic product of about `n / 2^(i+1)`
/// words (the module's section on division), so `O(2^i M(n / 2^i)) = O(n log(n / 2^i))` the
/// level, `M` the transform product, `O(n log n)` for every length up to `2^50` points ([`mul`]
/// takes the least of three computed costs, one of them that product). The powers, built by
/// squaring, cost `sum M(n / 2^i) = O(M(n))`; the one Newton reciprocal `O(M(n))`; each derived
/// reciprocal one product and one cyclic product at its level. The `O(n / h)` leaves cost
/// `O(h^1.5)` each, `O(n)` for the fixed `h`. Summed, `T(n) = a n (L^2 / 2 + (log2 h + 1/2) L) +
/// O(n) = O(n log^2 n)`, the `M(n) log n` of COMPLEXITY.md C31 (author decision A47). At `8n`
/// words `L` grows by 3, so the leading term predicts `8 f(L + 3) / f(L)`, `f` the bracket: 11.88
/// at 131,072 words and 11.68 at 196,608 (`8 (ln 8n / ln n)^2`, counted from one word, gives 11.07
/// and 10.96); the linear part lowers the ratio. Benchmarks `writing_a_wide_end_scales`,
/// `writing_a_long_decimal_end_scales` and `printing_a_wide_number_scales` read under these
/// (author decision P300, BENCH-over-nlogn-prediction, 2026-11-20).
pub fn to_decimal_split(x: &BigUint) -> String {
    to_decimal_split_at(x, PRINT_HANDOFF)
}

/// [`to_decimal_split`] with parts below powers of at most `handoff` words handed to
/// num-bigint, in place of [`PRINT_HANDOFF`]: for the benchmark that sets it. The text does not
/// depend on `handoff`.
pub fn to_decimal_split_at(x: &BigUint, handoff: usize) -> String {
    // Complexity tradeoff: a number of at most `leaf_bits(handoff)` bits is a single leaf and
    // builds no power, O(1) against building powers it would not divide by.
    if x.bits() <= leaf_bits(handoff) {
        return x.to_string();
    }
    let mut powers = vec![BigUint::from(10u32).pow(PRINT_LEAF as u32)];
    loop {
        // Unreachable: `powers` starts with one power and the loop only pushes.
        let last = powers.last().expect("the first power is built");
        // `last^2 > x` once its bits exceed `x`'s.
        if 2 * last.bits() - 1 > x.bits() {
            break;
        }
        let next = mul(last, last);
        if next > *x {
            break;
        }
        powers.push(next);
    }
    // Each power listed is at most `x`, except perhaps the first, and the last squared is
    // above it, so `high` and `low` below are each under the next power down squared.
    // Unreachable: the loop above only pushes onto the one power `powers` starts with.
    let top = powers.pop().expect("the first power is listed");
    // Complexity tradeoff: a number whose split would divide by a power of ten of at most
    // `handoff` words is printed by num-bigint, whose printing is faster there; the two
    // print the same digits. The crossover `PRINT_HANDOFF` is set by the benchmark `crossover
    // print-handoff` (crate zed-benches; COMPLEXITY.md K81) and set again on each target.
    if top > *x || words(&top) <= handoff {
        return x.to_string();
    }
    // Complexity tradeoff: the digits are written by halves, each level of the recursion
    // dividing by one power of ten, so the cost is O(M(n) log n) = O(n log^2 n), a log factor
    // above a product, accepted because no faster radix conversion is known: the subquadratic
    // method (Brent and Zimmermann, Modern Computer Arithmetic, 2010, section 1.7.2; the
    // scaled remainder tree of Bernstein, 2004; both in the module's "Sources") takes
    // O(M(n) log n) (author decision A47, 2026-11-09; COMPLEXITY.md C31), against
    // num-bigint's O(n^2). Tested by `printing_a_wide_number_scales` and
    // `writing_a_wide_end_scales` (COMPLEXITY.md K30, K81).
    let n = top.bits();
    // The quotient has at most `k` bits, and the reciprocal of `top` is taken to `p = k`
    // bits, only what it needs: the levels below do not derive theirs from it (see
    // [`Printer::new`]).
    let k = x.bits() - n + 1;
    let p = k;
    // `r = 2^2p / t`, floored, for `t` the top `p` bits of `top` (or `top 2^(p - n)`), lies in
    // `[R, R + 4]`, `R = 2^(p + n) / top` floored: `t <= top / 2^(n - p) < t + 1`, and
    // `2^2p / t - 2^2p / (t + 1) < 2^2p / t^2 <= 4`.
    let r = match p <= n {
        true => reciprocal(&(&top >> (n - p)), p),
        false => reciprocal(&(&top << (p - n)), p),
    };
    // With `a = x / 2^(n - 1)`, floored, `a r / 2^(p + 1)` is within 3 of `x / top`: the
    // error of `r` adds less than `4 x / 2^(p + n) <= 2`, as `x < 2^(n + k - 1)` and `p >= k`,
    // and the floors take off at most 2.
    let a = x >> (n - 1);
    let estimate = mul(&a, &r) >> (p + 1);
    drop(a);
    let product = mul(&estimate, &top);
    let (high, low) = settle(x, &top, estimate, product);
    drop(top);
    let printer = Printer::new(powers, handoff);
    // `log10(2) < 1234 / 4096`.
    // Unreachable: `x` is in memory, below `2^51` bits with 48-bit addresses, so its digit
    // count is far below what a `usize` counts.
    let digits = usize::try_from(x.bits() * 1234 / 4096 + 2).expect("a text that fits in memory");
    let mut out = String::with_capacity(digits);
    let level = printer.levels.len() + printer.first;
    // `high` is not zero, the power being at most `x`.
    printer.write(high.to_u64_digits(), level, false, &mut out);
    drop(high);
    printer.write(low.to_u64_digits(), level, true, &mut out);
    out
}

/// The levels of [`to_decimal`] below its widest power: `levels[j]` divides by
/// `10^(L 2^(first + j))`, and a number below `10^(L 2^first)` is a leaf, printed by
/// num-bigint. `tw` holds one table of roots for each prime of [`FIELDS`], of as many points
/// as the widest product needs, which serves every narrower one (see [`Field::forward`]).
struct Printer {
    first: usize,
    levels: Vec<Level>,
    tw: [Vec<(u64, u64)>; 3],
}

/// A divisor `d`, of `n` bits, divided by many times, with what each division needs
/// transformed once (per prime of [`FIELDS`], [`Field::spectrum`]): `y`, the spectra of
/// `X' = X - 2^w` on enough points for its product with a number of `yw` words, `X` the
/// reciprocal of `t`, the top `k <= n` bits of `d`, shifted to `w = 64 yw` bits, with
/// `T X <= 2^2w <= T (X + 2)`, `T = t 2^(w - k)` (the floor, or [`approx_reciprocal`]); and `dc`,
/// the spectra of `d` on `m` points, `64 m >= n - 55` ([`cyclic_points`]), or more.
struct Level {
    d: Vec<u64>,
    bits: u64,
    yw: usize,
    y: [Vec<u64>; 3],
    dc: [Vec<u64>; 3],
}

impl Level {
    /// The level of `d`, as words, of `bits` bits, its reciprocal from its top `k` bits, with
    /// the points of [`level_points`] and `tw` as for [`Field::forward`] of at least that many.
    fn new(d: Vec<u64>, bits: u64, k: u64, tw: &Roots) -> Level {
        let (linear, cyclic) = level_points(bits, k);
        let w = k.next_multiple_of(64);
        let t = from_words(shr_words(&d, bits - k)) << (w - k);
        let x = approx_reciprocal(&t, w, tw, RECIP_LEAF);
        drop(t);
        // `2^w <= X < 2^(w + 1)`: the top word is 1.
        let mut low = x.to_u64_digits();
        drop(x);
        let top = low.pop();
        debug_assert_eq!(top, Some(1), "the reciprocal has w + 1 bits");
        trim(&mut low);
        Level {
            y: spectra(&low, linear, tw),
            dc: spectra(&d, cyclic, tw),
            // Unreachable: `w / 64` is the word count of a reciprocal held in memory.
            yw: usize::try_from(w / 64).expect("a number whose words fit in memory"),
            d,
            bits,
        }
    }

    /// `(x / d, x mod d)` as words, for `x < 2^(n + w)` when `k = n`, and `x < 2^(n + k - 1)`
    /// when `k < n`. With `xh = x / 2^n`, floored, below `2^w`, the estimate
    /// `q0 = xh X / 2^w`, floored, is `xh + xh X' / 2^w`, a product of `yw` words by `yw`, and
    /// lies in `[q - 4, q]` for `k = n`: `xh X / 2^w > xh 2^k / t - 2`, `x / d < (xh + 1) 2^k /
    /// t`, `2^k / t <= 2`, and the floor takes off less than 1 more. For `k < n` the top bits
    /// `t` of `d` make the estimate up to 2 above as well (`x / d < 2^k`, so `(x / d) / t < 2`),
    /// `[q - 4, q + 2]`. So the remainder `x - q0 d` lies in `[-2d, 5d)`, below
    /// `2^(64 m + 61)` in size, and is found by a cyclic product on `d`'s `m` points
    /// ([`remainder`]); at most four steps of one `d` correct it. O(M(n)).
    fn div_rem(&self, x: &[u64], tw: &Roots) -> (Vec<u64>, Vec<u64>) {
        // A high half often is below the power: its quotient is zero, with no transform.
        if cmp_words(x, &self.d).is_lt() {
            return (Vec::new(), x.to_vec());
        }
        let xh = shr_words(x, self.bits);
        debug_assert!(xh.len() <= self.yw, "x / 2^n is below 2^w");
        let (yx, carry) = cyclic_product(&xh, &self.y, tw);
        debug_assert_eq!(carry, 0, "the product fits in its points");
        let mut q = xh;
        add_words(&mut q, yx.get(self.yw..).unwrap_or(&[]));
        drop(yx);
        trim(&mut q);
        let (mut negative, mut r) = remainder(x, &self.d, &self.dc, &q, tw);
        let mut steps = 0;
        while negative {
            // `-r + d`: below zero while `r > d`.
            negative = cmp_words(&r, &self.d).is_gt();
            r = match negative {
                true => {
                    sub_words(&mut r, &self.d);
                    r
                }
                // `d - r` as `-(r - d)` modulo `2^(64 len(d))`, in place.
                false => {
                    r.resize(self.d.len(), 0);
                    sub_words(&mut r, &self.d);
                    for v in r.iter_mut() {
                        *v = !*v;
                    }
                    add_at(&mut r, 0, 1);
                    r
                }
            };
            trim(&mut r);
            let borrow = sub_at(&mut q, 0, 1);
            debug_assert!(!borrow, "the estimate is above the quotient");
            trim(&mut q);
            steps += 1;
        }
        while cmp_words(&r, &self.d).is_ge() {
            let borrow = sub_words(&mut r, &self.d);
            debug_assert!(!borrow, "r is at least d");
            trim(&mut r);
            increment(&mut q);
            steps += 1;
        }
        debug_assert!(steps <= 4, "the estimate is at most four off");
        (q, r)
    }
}

/// The coefficients of the product, cyclic on `s[k].len()` points, of the words `x` and the
/// number whose spectra (see [`Field::spectrum`]) are `s`, joined and carried into words,
/// with the carry out of the top; `tw` as for [`Field::forward`].
fn cyclic_product(x: &[u64], s: &[Vec<u64>; 3], tw: &[Vec<(u64, u64)>; 3]) -> (Vec<u64>, u128) {
    let [f0, f1, f2] = &FIELDS;
    let mut r0 = f0.cyclic(x, &s[0], &tw[0]);
    let r1 = f1.cyclic(x, &s[1], &tw[1]);
    let r2 = f2.cyclic(x, &s[2], &tw[2]);
    let carry = garner(&mut r0, &r1, &r2);
    (r0, carry)
}

/// `(a - b) mod M`, `M = 2^(64 m) - 1`, for `a` and `b` of `m` words each below or at `M`,
/// as words with no zero on top, `M` itself read as `0`.
fn sub_around(mut a: Vec<u64>, b: &[u64]) -> Vec<u64> {
    if sub_words(&mut a, b) {
        // `a - b + 2^(64 m) >= 1`, so taking one off borrows nothing past the top.
        sub_at(&mut a, 0, 1);
    }
    if a.iter().all(|&v| v == u64::MAX) {
        a.fill(0);
    }
    trim(&mut a);
    a
}

/// `floor(2^(w + n) / d)` for `d` of `n` bits, `w` the bits of its words, from `ya`, which is
/// `Y = floor(2^ea / d^2)` with `ea >= w + 2n`, or up to 4 above it with `ea >= w + 2n + 3`;
/// `d` also given as words `dw` and as the spectra `dc` of its cyclic product (see
/// [`Level`]). As `1/d = d / d^2`, with `R = floor(2^(w + 2n) / d^2) = Y / 2^(ea - w - 2n)`
/// (floors compose), `r = ya / 2^(ea - w - 2n)` is `R` or `R + 1`, and `R d` lies in
/// `(2^(w + 2n) / d - d, 2^(w + 2n) / d]`, so `t = r d / 2^n`, floored, is the quotient,
/// one below or one above, since `d < 2^n`; which is told by the remainder
/// `2^(w + n) - t d`, in `[-d, 2d)` and so found modulo `2^(64 m) - 1` by a cyclic product. One
/// product of `n` bits and one cyclic one, against several of Newton's iteration. O(M(n)).
fn derive(
    d: &BigUint,
    dw: &[u64],
    dc: &[Vec<u64>; 3],
    tw: &[Vec<(u64, u64)>; 3],
    ya: &BigUint,
    ea: u64,
) -> BigUint {
    let n = d.bits();
    let w = n.next_multiple_of(64);
    // Unreachable: the one caller, `Printer::new`, passes the `e` of the level above, at
    // least `w + 2n + 3` there (each `d` is at least the first power, of 31 words).
    let shift = ea
        .checked_sub(w + 2 * n)
        .expect("the reciprocal above is at least as precise");
    let mut t = mul(&(ya >> shift), d) >> n;
    let m = dc[0].len();
    let (mut td, carry) = cyclic_product(&fold_words(&t.to_u64_digits(), m), dc, tw);
    add_around(&mut td, carry);
    // `2^(w + n) mod M` is one bit.
    let mut power = vec![0u64; m];
    let at = (w + n) % (64 * m as u64);
    power[(at / 64) as usize] = 1 << (at % 64);
    // The remainder lies in `[-d, 2d)`, `M > 4d`: `[d, 2d)` for `t` one below, and a
    // negative one reads as `M - d` or above, past `2d`.
    let mut rem = sub_around(power, &td);
    if cmp_words(&rem, dw).is_ge() {
        let past = sub_words(&mut rem, dw);
        debug_assert!(!past, "the remainder is at least d");
        trim(&mut rem);
        match cmp_words(&rem, dw).is_lt() {
            true => t += 1u32,
            false => t -= 1u32,
        }
    }
    t
}

impl Printer {
    /// The levels of the powers `10^(L 2^i)` listed, each the square of the one before,
    /// those of at most `handoff` words left to leaves. The widest level's reciprocal
    /// is [`approx_reciprocal`]'s `X`, at most one below the floor, which [`Level::div_rem`]
    /// allows; each level below derives its own from the one above ([`derive()`]), given `X + 1`
    /// for the widest, at most one above the floor.
    fn new(powers: Vec<BigUint>, handoff: usize) -> Printer {
        let first = powers
            .iter()
            .position(|p| words(p) > handoff)
            .unwrap_or(powers.len());
        let powers = powers.get(first..).unwrap_or(&[]);
        // The points of each level's products: `xh y'` for `xh` and `y' < 2^w` of at most `W`
        // words each (`y' = 2^w` only for `d` a power of two), and the least power of two `m`
        // at least `W` with `4d < 2^(64 m) - 1`.
        let points = |d: &BigUint| {
            let len = words(d);
            let mut cyclic = len.next_power_of_two();
            if d.bits() + 2 > 64 * cyclic as u64 {
                cyclic *= 2;
            }
            ((2 * len - 1).next_power_of_two(), cyclic)
        };
        let most = powers
            .last()
            .map(|d| {
                let (linear, cyclic) = points(d);
                linear.max(cyclic)
            })
            .unwrap_or(1);
        let tw = FIELDS.each_ref().map(|f| f.twiddles(most));
        let spectra = |x: &[u64], n: usize| [0, 1, 2].map(|k| FIELDS[k].spectrum(x, n, &tw[k]));
        let mut levels = Vec::with_capacity(powers.len());
        // The reciprocal `floor(2^e / d)` of the level above, or one above it, and `e`.
        let mut above: Option<(BigUint, u64)> = None;
        for d in powers.iter().rev() {
            let (linear, cyclic) = points(d);
            let bits = d.bits();
            let w = bits.next_multiple_of(64);
            let dw = d.to_u64_digits();
            let dc = spectra(&dw, cyclic);
            // `y = 2^2w / (d 2^s)` = `2^(w + n) / d`, floored, or one below for the widest.
            // `d` is at least the first power, of 31 words, so the `e` above it is at least
            // `w + 2n + 3`, as [`derive()`] needs for a reciprocal one above the floor.
            let y = match &above {
                Some((ya, ea)) => {
                    debug_assert!(*ea >= w + 2 * bits + 3, "the level above is precise enough");
                    derive(d, &dw, &dc, &tw, ya, *ea)
                }
                None => approx_reciprocal(&(d << (w - bits)), w, &tw, RECIP_LEAF),
            };
            // `X + 1` for the widest: `X` is at most one below the floor.
            let over = u32::from(above.is_none());
            let low = (&y - (BigUint::one() << w)).to_u64_digits();
            levels.push(Level {
                y: spectra(&low, linear),
                dc,
                yw: dw.len(),
                d: dw,
                bits,
            });
            above = Some((y + over, w + bits));
        }
        levels.reverse();
        Printer { first, levels, tw }
    }

    /// Writes `x < 10^(L 2^level)` to `out`, padded to `L 2^level` digits when `pad`.
    fn write(&self, x: Vec<u64>, level: usize, pad: bool, out: &mut String) {
        if level <= self.first {
            let s = from_words(x).to_string();
            if pad {
                out.extend(std::iter::repeat_n('0', (PRINT_LEAF << level) - s.len()));
            }
            out.push_str(&s);
            return;
        }
        let (high, low) = self.levels[level - 1 - self.first].div_rem(&x, &self.tw);
        drop(x);
        if !pad && high.is_empty() {
            return self.write(low, level - 1, false, out);
        }
        self.write(high, level - 1, pad, out);
        self.write(low, level - 1, true, out);
    }
}

/// `x / 2^n`, floored, as words with no zero on top.
fn shr_words(x: &[u64], n: u64) -> Vec<u64> {
    let (skip, bits) = ((n / 64) as usize, (n % 64) as u32);
    let src = x.get(skip..).unwrap_or(&[]);
    let mut out: Vec<u64> = match bits {
        0 => src.to_vec(),
        _ => src
            .iter()
            .zip(src.iter().skip(1).map(Some).chain([None]))
            .map(|(lo, hi)| (lo >> bits) | hi.map_or(0, |h| h << (64 - bits)))
            .collect(),
    };
    trim(&mut out);
    out
}

/// Drops the zero words on top of `x`.
fn trim(x: &mut Vec<u64>) {
    while x.last() == Some(&0) {
        x.pop();
    }
}

/// `a += b`, `a` growing as needed.
fn add_words(a: &mut Vec<u64>, b: &[u64]) {
    if a.len() < b.len() {
        a.resize(b.len(), 0);
    }
    let mut carry = false;
    for (x, y) in a.iter_mut().zip(b) {
        let (s, c1) = x.overflowing_add(*y);
        let (s, c2) = s.overflowing_add(u64::from(carry));
        *x = s;
        carry = c1 || c2;
    }
    if carry && carry_at(a, b.len()) {
        a.push(1);
    }
}

/// Adds one to `a` at word `i`, the carry carried up; whether it passes the top.
fn carry_at(a: &mut [u64], mut i: usize) -> bool {
    loop {
        if i == a.len() {
            return true;
        }
        let (v, carry) = a[i].overflowing_add(1);
        a[i] = v;
        if !carry {
            return false;
        }
        i += 1;
    }
}

/// `x + 1`, `x` growing as needed.
fn increment(x: &mut Vec<u64>) {
    if carry_at(x, 0) {
        x.push(1);
    }
}

/// `a -= b` for `a.len() >= b.len()`, modulo `2^(64 a.len())`; whether it borrowed past the
/// top, that is whether `a` was below `b`.
fn sub_words(a: &mut [u64], b: &[u64]) -> bool {
    let mut borrow = false;
    for (x, y) in a.iter_mut().zip(b) {
        let (s, b1) = x.overflowing_sub(*y);
        let (s, b2) = s.overflowing_sub(u64::from(borrow));
        *x = s;
        borrow = b1 || b2;
    }
    borrow && (b.len() == a.len() || sub_at(a, b.len(), 1))
}

/// The order of two numbers given as words with no zero on top.
fn cmp_words(a: &[u64], b: &[u64]) -> std::cmp::Ordering {
    a.len()
        .cmp(&b.len())
        .then_with(|| a.iter().rev().cmp(b.iter().rev()))
}

/// `x mod (2^(64 m) - 1)` in `m` words, perhaps `2^(64 m) - 1` itself: the sum of `x`'s
/// pieces of `m` words, `2^(64 m)` being 1.
fn fold_words(x: &[u64], m: usize) -> Vec<u64> {
    let mut out = vec![0u64; m];
    for piece in x.chunks(m) {
        let mut carry = false;
        for (o, v) in out.iter_mut().zip(piece) {
            let (s, c1) = o.overflowing_add(*v);
            let (s, c2) = s.overflowing_add(u64::from(carry));
            *o = s;
            carry = c1 || c2;
        }
        if carry && carry_at(&mut out, piece.len()) {
            add_around(&mut out, 1);
        }
    }
    out
}

/// `x += c 2^0 mod (2^(64 x.len()) - 1)`: what passes the top is added again at the bottom.
fn add_around(x: &mut [u64], mut c: u128) {
    while c != 0 {
        for v in x.iter_mut() {
            if c == 0 {
                return;
            }
            let t = u128::from(*v) + (c & u128::from(u64::MAX));
            *v = t as u64;
            c = (c >> 64) + (t >> 64);
        }
    }
}

/// `prod p^e`, built. A power of 2 is a shift, done last, so `2^e` costs its `e` bits and
/// not the squarings of a multiplication. [`TooLarge`] when an exponent is 2^64 or more: the
/// power has at least that many bits, more than any memory holds, and it names a lower bound
/// on the bits of the whole product as its size, and `sum e * ceil(log2 p)`, an upper bound,
/// as the memory asked for. Every other build asks
/// the system for its memory before calling this.
///
/// Complexity tradeoff (NUM-no-panic-built): the exponents are read once before the build,
/// O(terms) word operations, to refuse an exponent of 2^64 or more as an error; before, such
/// an exponent stopped zedc at an `expect`, when a message printed the digits of `2^2^100`.
pub(super) fn built(pows: &[(u64, BigUint)]) -> Result<BigInt, TooLarge> {
    let small: Option<Vec<(u64, u64)>> = (pows.iter())
        .map(|(p, e)| e.to_u64().map(|e| (*p, e)))
        .collect();
    let Some(small) = small else {
        let bits: BigUint = (pows.iter()).map(|(p, e)| e * p.ceil_log2()).sum();
        // The size named is a lower bound on the product's bits (`super::room::least_bits`), the
        // memory asked the upper bound (row CONST-least-refusal-size).
        let one = BigInt::one();
        return Err(TooLarge {
            size: super::room::least_bits(&one, pows.iter().map(|(p, e)| (*p, e))),
            ask: bits,
        });
    };
    let mut out = BigUint::one();
    let mut twos = 0;
    for (p, e) in small {
        match (p, e) {
            (_, 0) => {}
            (2, _) => twos = e,
            _ => out = mul(&out, &pow(&BigUint::from(p), e)),
        }
    }
    out <<= twos;
    Ok(BigInt::from(out))
}

/// The digits `read_decimal` reads whole, with no split. The value read does not depend on it.
//
// Complexity tradeoff: a timed crossover of two algorithms with identical results, nothing
// given up. A text of at most `LEAF_DIGITS` digits is read whole (`digit_text::read_whole`),
// O(n^2), one word of 19 digits at a time (num-bigint's `parse` until SWAR-read-literals); a
// longer one is split by halves (`read_digits_by`), O(n log^2 n). Both
// give the same number for every text (test `num::tests::the_leaf_does_not_change_the_value`,
// leaf 1 against `LEAF_DIGITS` and against num-bigint; COMPLEXITY.md K41). Measured on
// 2026-11-07 (item KERNEL-leaf-digits, not committed): `read_digits` with each leaf on random
// texts, the test build (opt-level 2), the fewest instructions of 2 to 20 runs, load5 28 to 36:
//
//   digits      leaf 32     64     128     256     512    1024    2048
//   700          64,526  50,065  43,054  38,847  36,664  30,667  30,667
//   1,000        94,516  73,183  62,109  56,689  52,879  47,480  47,480
//   1,500       150,409 120,772 103,724  95,565  91,004  90,112  81,143
//   3,000       351,391 291,238 258,980 242,832 233,841 232,414 236,825
//   6,000       879,929 759,963 694,248 663,420 645,131 642,638 657,250
//   10^4 (M)      1.906   1.705   1.597   1.544   1.514   1.511   1.536
//   10^5 (M)     66.877  64.892  63.801  63.276  62.979  62.959  63.215
//   10^6 (M)     1,314.2 1,294.4 1,283.4 1,278.2 1,275.3 1,275.1 1,277.6
//
// 1024 has the fewest at every size but 700 and 1,000 (tied with 2048, which reads them
// whole) and 1,500 (2048, 10% fewer); from 3,000 digits 2048 costs 0.2% to 2.3% more, as the
// O(n^2) leaves grow. Processor time agreed within its noise at this load (10^6: 153 to 157
// ms for leaves 128 to 2048). The peak heap is the same at 512 and 1024, 23.6 bits per digit
// on 2^16 to 2^22 nines, within the 48 that `read_decimal` asks for. Measured again with the
// leaf read eight digits a step (EXP-swar-digits, 2026-11-12, leaves 128 to 4096 at 3,000 to
// 10^6 digits): 1024 and 2048 are again the fewest, within 1% of each other, so a cheaper leaf
// does not move the crossover. Measured again by `crossover leaf-digits` with the meter's own
// heap (TEST-meter-allocator-bias, 2026-11-15; leaves 128 to 16384 at 700 to 10^6 digits): the
// per-size counts are as above (2048 costs 0.1% to 0.9% more from 3,000 digits, 20% less at
// 1,500), and summed over the sizes as `crossover` sums them 2048 does 1.0274 times less work
// than 1024, outside the spread of repeated runs, now 1.0000 (it was 1.0340, which held 1024).
// On the C library's heap with its per-thread cache the same benchmark gives 1.0296 against a
// spread of 1.0106, so both heaps put the leaf at 2048. To be measured again at the Zed port,
// where both sides of the crossover change.
pub(super) const LEAF_DIGITS: usize = 2048;

/// [`super::read_digits`] with texts of at most `leaf` digits read whole; `leaf` is at least 1.
///
/// It is here, beside the products it is built from, and not in `num`, which reads through it:
/// the module `crossover` below also names it, and a name of `num` from this file would put the
/// two files in an import cycle, which Zed forbids between files (DESIGN.md sec:units).
pub(super) fn read_digits_by(digits: &str, leaf: usize) -> BigUint {
    // Complexity tradeoff: reading by halves costs one widest product per level, `log2(n /
    // leaf)` levels, O(M(n) log n) = O(n log^2 n), a log factor above a product, accepted
    // because no faster radix conversion is known: the subquadratic method (Brent and
    // Zimmermann, Modern Computer Arithmetic, 2010, section 1.7.2, Algorithm 1.25
    // FastIntegerInput; Bernstein, "Scaled remainder trees", 2004; both in the module's
    // "Sources") takes O(M(n) log n) (author decision A47, 2026-11-09;
    // COMPLEXITY.md C31), against num-bigint's O(n^2). The scaling tests of reading hold it to
    // the limit of work of order n log^2 n.
    //
    // The levels are joined one at a time from the leaves up, not by a recursion from the top,
    // so that each level's power `10^(leaf 2^j)` multiplies every pair of the level by spectra
    // transformed once (`fast::Factor`), two transforms a product in place of three, and the
    // spectra of one level only are held at a time. A recursion from the top visits every
    // level along each path, so it would hold all levels' spectra at once, about six words for
    // each word of the powers, over the 48 bits a digit that `read_decimal` asks for. Measured
    // on 2026-11-12 (RADIX-depth) on `int(s)` of 160,000 and 1,280,000 digits, the reading by
    // a recursion with `fast::mul` took 121.4 and 1,827.9 million instructions, and level by
    // level with `fast::Factor` 121.5 and 1,756.4 (the spectra are kept from 1701 words, only
    // at the larger size). The number is the same: every split of the text gives its value.
    assert!(
        !digits.is_empty(),
        "a nonempty text of ASCII decimal digits"
    );
    let text = digits.as_bytes();
    // A text of one leaf, which is every literal of up to `leaf` digits, is read with no vector
    // of parts and no power of ten: building `10^leaf` alone cost about 9,500 instructions
    // (EXP-swar-digits, 2026-11-12), 70% to 84% of reading a literal of 1 to 25 digits.
    if text.len() <= leaf {
        return super::digit_text::read_whole(text);
    }
    let mut parts: Vec<BigUint> = (0..text.len().div_ceil(leaf))
        .map(|i| {
            let end = text.len() - i * leaf;
            super::digit_text::read_whole(&text[end.saturating_sub(leaf)..end])
        })
        .collect();
    // `parts[i]` is below `power`, `10^(leaf 2^j)` at level `j`, and is the `i`-th group of
    // `leaf 2^j` digits from the low end; the top one may have fewer.
    let mut power = BigUint::from(10u32).pow(leaf as u32);
    while parts.len() > 1 {
        // Each high part is below the power, so it has at most the power's words.
        let other = power.iter_u64_digits().len();
        let factor = Factor::new(power, other, parts.len() / 2);
        let mut joined = Vec::with_capacity(parts.len().div_ceil(2));
        let mut each = parts.into_iter();
        while let Some(low) = each.next() {
            joined.push(match each.next() {
                Some(high) => factor.mul(&high) + low,
                None => low,
            });
        }
        parts = joined;
        power = match parts.len() > 1 {
            true => mul(factor.value(), factor.value()),
            false => BigUint::zero(),
        };
    }
    // Unreachable: `read_digits_by` asserts a nonempty text, so `parts` starts nonempty and
    // each round leaves `ceil(len / 2) >= 1` parts.
    parts.pop().expect("a nonempty text has a part")
}

/// The methods on either side of each size threshold of `num`, one by one, for the
/// crossover benchmarks (crate zed-benches, binary `crossover`; DESIGN.md sec:plan, A96),
/// which time both methods on both sides of a threshold and check that they give the same
/// output. Not for other use: each function forces one method whatever the size.
#[doc(hidden)]
pub mod crossover {
    use num_bigint::{BigInt, BigUint};

    use super::MulBy;

    /// `super::MUL_LEAF` as built, in words.
    pub const MUL_LEAF: usize = super::MUL_LEAF;
    /// `super::DIV_LEAF` as built, in bits.
    pub const DIV_LEAF: u64 = super::DIV_LEAF;
    /// `super::RECIP_LEAF` as built, in bits.
    pub const RECIP_LEAF: u64 = super::RECIP_LEAF;
    /// `super::GCD_LEAF` as built, in bits.
    pub const GCD_LEAF: u64 = super::GCD_LEAF;
    /// `super::LIFT_BITS` as built, in bits.
    pub const LIFT_BITS: u64 = super::LIFT_BITS;
    /// The digits [`crate::num::read_digits`] reads whole, as built.
    pub const LEAF_DIGITS: usize = super::LEAF_DIGITS;
    /// `super::DIV_COST` as built.
    pub const DIV_COST: f64 = super::DIV_COST;
    /// `super::TOOM_COST` as built.
    pub const TOOM_COST: f64 = super::TOOM_COST;
    /// `super::TRANSFORM_COST` as built.
    pub const TRANSFORM_COST: f64 = super::TRANSFORM_COST;
    /// `super::SPARSE_WORD` as built.
    pub const SPARSE_WORD: f64 = super::SPARSE_WORD;
    /// `super::SPARSE_STEP` as built.
    pub const SPARSE_STEP: f64 = super::SPARSE_STEP;
    /// `super::SPARSE_RUN` as built.
    pub const SPARSE_RUN: f64 = super::SPARSE_RUN;
    /// `super::CACHED_COST` as built.
    pub const CACHED_COST: f64 = super::CACHED_COST;

    /// The method [`super::mul`] takes for `a * b`: "num-bigint", "rows" or "transforms".
    pub fn mul_method(a: &BigUint, b: &BigUint) -> &'static str {
        match super::mul_method(a, b) {
            MulBy::NumBigint => "num-bigint",
            MulBy::Rows => "rows",
            MulBy::Pieces(_) => "transforms",
        }
    }

    /// `a * b` by transforms, in the pieces `super::transform_plan` chooses, whatever the
    /// sizes; both factors nonzero.
    pub fn mul_by_transforms(a: &BigUint, b: &BigUint) -> BigUint {
        let (la, lb) = (super::words(a), super::words(b));
        let (_, piece) = super::transform_plan(la.min(lb), la.max(lb));
        super::pieces_mul(a, b, piece)
    }

    /// `a * b` by transforms whole (`super::transform_mul`), on half the power of two of
    /// points at or above its coefficients with the top coefficients' product subtracted
    /// (`wrap`), or on all of them, whatever `super::points` chooses for the whole product;
    /// both factors nonzero and, with `wrap`, each of at most half the points' words.
    pub fn mul_on_points(a: &BigUint, b: &BigUint, wrap: bool) -> BigUint {
        let n = (super::words(a) + super::words(b) - 1).next_power_of_two();
        super::transform_mul_on(a, b, (if wrap { n / 2 } else { n }, wrap), n)
    }

    /// Whether `super::points` wraps `a * b` onto half the points ([`mul_on_points`]).
    pub fn wraps(a: &BigUint, b: &BigUint) -> bool {
        super::points(super::words(a), super::words(b)).1
    }

    /// `super::WRAP_COST` as built.
    pub const WRAP_COST: f64 = super::WRAP_COST;

    /// The value of `super::WRAP_COST` below which `super::points` wraps `a * b`, `None` where
    /// it cannot wrap (`super::wrap_flip`).
    pub fn wrap_flip(a: &BigUint, b: &BigUint) -> Option<f64> {
        super::wrap_flip(super::words(a), super::words(b))
    }

    /// `a * b` by rows over the nonzero words of one factor (`super::sparse_mul`).
    pub fn mul_by_rows(a: &BigUint, b: &BigUint) -> BigUint {
        super::sparse_mul(a, b)
    }

    /// `(a / b, a mod b)` past `super::DIV_LEAF`, whatever the sizes: the cheaper of long
    /// division over the nonzero words of `b` and the division by a reciprocal; `a >= b > 0`.
    pub fn div_rem_past_leaf(a: &BigUint, b: &BigUint) -> (BigUint, BigUint) {
        super::div_rem_past_leaf(a, b)
    }

    /// `a mod b` by the blocks of one `super::Divisor`, as `super::rem` takes it where
    /// `super::div_rem` would take its blocks, here whatever the sizes; `b > 0`.
    pub fn rem_by_blocks(a: &BigUint, b: &BigUint) -> BigUint {
        super::Divisor::new(std::borrow::Cow::Borrowed(b), a.bits()).rem(a)
    }

    /// Whether `super::rem` takes the blocks of a `super::Divisor` for `a mod b`, not
    /// num-bigint's `%` (nor `super::div_rem`); `b > 0`.
    pub fn rem_takes_blocks(a: &BigUint, b: &BigUint) -> bool {
        super::rem_takes_blocks(a, b)
    }

    /// `(a / b, a mod b)` by long division over the nonzero words of `b`, which has at least
    /// two words; `a >= b`.
    pub fn div_rem_sparse(a: &BigUint, b: &BigUint) -> (BigUint, BigUint) {
        super::sparse_div_rem(a, b)
    }

    /// `(a / b, a mod b)` by a reciprocal; `a >= b > 0`.
    pub fn div_rem_by_reciprocal(a: &BigUint, b: &BigUint) -> (BigUint, BigUint) {
        super::div_rem_by_reciprocal(a, b)
    }

    /// `(a / b, a mod b)` by a reciprocal at every block, where [`div_rem_by_reciprocal`]'s
    /// blocks divide the way `super::divisor_way` chooses, which may be long division over the
    /// nonzero words; `a >= b > 0`, `b` past `super::DIV_LEAF`.
    pub fn div_rem_by_levels(a: &BigUint, b: &BigUint) -> (BigUint, BigUint) {
        let n = b.bits();
        let (linear, cyclic) = super::level_points(n, n);
        let way = super::Way::Reciprocal(linear.max(cyclic));
        super::Divisor::with_way(std::borrow::Cow::Borrowed(b), way).div_rem(a)
    }

    /// Whether [`div_rem_past_leaf`] takes long division over the nonzero words of `b` for
    /// `a / b`, rather than the reciprocal; `a >= b > 0`.
    pub fn div_by_rows(a: &BigUint, b: &BigUint) -> bool {
        let (aw, bw) = (super::words(a), super::words(b));
        super::sparse_div_cost(aw - bw + 1, b) <= super::newton_cost(aw - bw + 1, bw)
    }

    /// Whether `super::div_rem` takes num-bigint's division for `a / b`; `a >= b > 0`.
    pub fn div_by_num_bigint(a: &BigUint, b: &BigUint) -> bool {
        div_flip(a, b).is_none_or(|flip| super::DIV_COST <= flip)
    }

    /// The value of `super::DIV_COST` at which `super::div_rem` changes method for `a / b`:
    /// num-bigint's division at or below it. `None` at or below `super::DIV_LEAF`, where it
    /// does not decide; `a >= b > 0`.
    pub fn div_flip(a: &BigUint, b: &BigUint) -> Option<f64> {
        let (m, n) = (a.bits(), b.bits());
        if n.min(m - n + 1) <= super::DIV_LEAF {
            return None;
        }
        let (aw, bw) = (super::words(a), super::words(b));
        let qw = aw - bw + 1;
        let past = super::past_leaf_cost(qw, b);
        Some(past / super::num_bigint_div_units(qw, bw))
    }

    /// The value of `super::TOOM_COST` at which [`super::mul`] changes method for `a * b`:
    /// num-bigint's product at or below it, else the cheaper of rows and transforms. `None` at
    /// or below `super::MUL_LEAF`, where it does not decide.
    pub fn toom_flip(a: &BigUint, b: &BigUint) -> Option<f64> {
        let (la, lb) = (super::words(a), super::words(b));
        let (short, long) = (la.min(lb), la.max(lb));
        if short <= super::MUL_LEAF {
            return None;
        }
        let rows = (super::nonzero_words(a) as u128 * lb as u128)
            .min(super::nonzero_words(b) as u128 * la as u128);
        let (cost, _) = super::transform_plan(short, long);
        let per = super::toom_cost(short, long) / super::TOOM_COST;
        Some((rows as f64).min(cost) / per)
    }

    /// The value of `super::TRANSFORM_COST` at which [`super::mul`] changes from transforms
    /// to rows for `a * b`: rows at or above it. `None` at or below `super::MUL_LEAF`.
    pub fn transform_flip(a: &BigUint, b: &BigUint) -> Option<f64> {
        let (la, lb) = (super::words(a), super::words(b));
        let (short, long) = (la.min(lb), la.max(lb));
        if short <= super::MUL_LEAF {
            return None;
        }
        let rows = (super::nonzero_words(a) as u128 * lb as u128)
            .min(super::nonzero_words(b) as u128 * la as u128);
        let (cost, _) = super::transform_plan(short, long);
        Some(rows as f64 * super::TRANSFORM_COST / cost)
    }

    /// The value of `super::SPARSE_WORD` at which [`div_rem_past_leaf`] changes method for
    /// `a / b`: long division at or below it, the reciprocal above; `a >= b > 0`.
    pub fn sparse_flip(a: &BigUint, b: &BigUint) -> Option<f64> {
        let (aw, bw) = (super::words(a), super::words(b));
        let q = (aw - bw + 1) as f64;
        let newton = super::newton_cost(aw - bw + 1, bw);
        let (k, runs) = super::nonzero_runs(b);
        let rest = super::SPARSE_STEP + super::SPARSE_RUN * runs as f64;
        Some((newton / (q + 1.0) - rest) / k as f64)
    }

    /// The value of `super::SPARSE_STEP` at which [`div_rem_past_leaf`] changes method for
    /// `a / b`, with `super::SPARSE_WORD` and `super::SPARSE_RUN` as built: long division at
    /// or below it, the reciprocal above; `a >= b > 0`. From `sparse_div_cost(q, b) <=
    /// newton_cost`, that is `(q + 1) (SPARSE_WORD k + SPARSE_RUN r + SPARSE_STEP) <= newton`
    /// for `k` nonzero words in `r` runs, solved for `SPARSE_STEP`.
    pub fn step_flip(a: &BigUint, b: &BigUint) -> Option<f64> {
        let (aw, bw) = (super::words(a), super::words(b));
        let q = (aw - bw + 1) as f64;
        let newton = super::newton_cost(aw - bw + 1, bw);
        let (k, runs) = super::nonzero_runs(b);
        Some(newton / (q + 1.0) - super::SPARSE_WORD * k as f64 - super::SPARSE_RUN * runs as f64)
    }

    /// A factor whose spectra are kept for products with numbers of at most `other` words
    /// whatever the costs, where `super::Factor` keeps them only when they cost less.
    pub struct Kept(super::Factor);

    impl Kept {
        /// `x` with its spectra on the points of a product with `other` words.
        pub fn new(x: BigUint, other: usize) -> Kept {
            let (points, _) = super::points(super::words(&x), other);
            let tw = super::roots(points);
            let spectra = super::spectra(&x.to_u64_digits(), points, &tw);
            Kept(super::Factor {
                x,
                other,
                spectra: Some((spectra, tw)),
            })
        }

        /// `x`.
        pub fn value(&self) -> &BigUint {
            self.0.value()
        }

        /// `y * x` by the spectra, `y` of at most `other` words.
        pub fn mul(&self, y: &BigUint) -> BigUint {
            // Unreachable: `Kept::new`, the only constructor, sets the spectra.
            let (s, tw) = self.0.spectra.as_ref().expect("kept spectra");
            self.0.spectra_mul(y, s, tw)
        }

        /// `y * x` as [`super::Factor::mul`] takes it with these spectra kept: by them when
        /// they cost less than [`super::mul`], else by [`super::mul`].
        pub fn factor_mul(&self, y: &BigUint) -> BigUint {
            self.0.mul(y)
        }

        /// Whether [`super::Factor::mul`] takes the spectra for `y`.
        pub fn by_spectra(&self, y: &BigUint) -> bool {
            // Unreachable: `Kept::new`, the only constructor, sets the spectra.
            let (s, _) = self.0.spectra.as_ref().expect("kept spectra");
            self.0.takes_spectra(s[0].len(), super::words(y))
        }

        /// The value of [`super::CACHED_COST`] at which [`super::Factor::mul`] changes method
        /// for `y`: the spectra below it, [`super::mul`] at or above. `None` where it does not
        /// decide: `y` wider than the spectra allow, or [`super::mul`] taking num-bigint's
        /// product at or below [`super::MUL_LEAF`].
        pub fn cached_flip(&self, y: &BigUint) -> Option<f64> {
            // Unreachable: `Kept::new`, the only constructor, sets the spectra.
            let (s, _) = self.0.spectra.as_ref().expect("kept spectra");
            let (points, wx, wy) = (s[0].len(), super::words(&self.0.x), super::words(y));
            let dense = super::dense_cost(wy, wx);
            if wy > self.0.other || dense == 0.0 {
                return None;
            }
            let cached = super::cached_cost(points);
            let top = super::cached_total(points, wx, wy) - cached;
            Some((dense - top) * super::CACHED_COST / cached)
        }
    }

    /// `2^2k / x`, floored, for `x` of exactly `k` bits, Newton's steps starting from
    /// num-bigint's division at or below `leaf` bits (at least 4).
    pub fn reciprocal(x: &BigUint, leaf: u64) -> BigUint {
        super::reciprocal_from(x, x.bits(), leaf.max(4))
    }

    /// The gcd of `a` and `b` by `super::gcd` with the leaf of `leaf` bits and the lift of
    /// `lift` bits.
    pub fn gcd(a: &BigUint, b: &BigUint, leaf: u64, lift: u64) -> BigUint {
        super::gcd_using(a, b, leaf, lift)
    }

    /// The value of a nonempty text of ASCII decimal digits, as [`crate::num::read_digits`]
    /// reads it but with texts of at most `leaf` digits read whole; `leaf` at least 1.
    pub fn read_digits(digits: &str, leaf: usize) -> BigUint {
        super::read_digits_by(digits, leaf)
    }

    /// `super::bezout` with the lift of `lift` bits.
    pub fn bezout(a: &BigUint, b: &BigUint, lift: u64) -> (BigUint, BigInt, BigInt) {
        super::bezout_with(a, b, lift)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bezout_coefficients_with_unequal_widths() {
        for (wa, wb) in [
            (1, 45),
            (45, 1),
            (2, 356),
            (356, 2),
            (45, 356),
            (356, 45),
            (45, 45),
        ] {
            let a = random(wa as u64, wa) | BigUint::one();
            let b = random(wb as u64 + 1, wb) | BigUint::one();
            for factor in [BigUint::one(), random(93, 5) | BigUint::one()] {
                for shift in [0, 1, 77] {
                    let a = (&a * &factor) << shift;
                    let b = &b * &factor;
                    for (a, b) in [(&a, &b), (&b, &a)] {
                        let (g, s, t) = bezout(a, b);
                        assert_eq!(g, a.gcd(b));
                        assert_eq!(
                            &s * BigInt::from(a.clone()) + &t * BigInt::from(b.clone()),
                            BigInt::from(g.clone())
                        );
                        // The identity and the canonical coefficient uniquely determine the answer.
                        let (odd, coefficient) = if a.trailing_zeros() <= b.trailing_zeros() {
                            (a, &t)
                        } else {
                            (b, &s)
                        };
                        assert!(!coefficient.is_negative());
                        assert!(coefficient.magnitude() < &(odd / &g));
                    }
                }
            }
        }
    }

    /// `words` random 64-bit words from `seed`, each 32-bit digit the low half of one draw.
    fn random(seed: u64, words: usize) -> BigUint {
        let mut rng = crate::seed::Rng::new(seed);
        let digits: Vec<u32> = (0..2 * words).map(|_| rng.next_u64() as u32).collect();
        BigUint::new(digits)
    }

    /// Edge forms of `words` words: all ones, a power of two, one above a power of two, and
    /// random.
    fn forms(words: usize, seed: u64) -> Vec<BigUint> {
        let bits = 64 * words as u64;
        let one = BigUint::one();
        vec![
            (&one << bits) - 1u32,
            &one << (bits - 1),
            (&one << (bits - 1)) + 1u32,
            random(seed, words),
        ]
    }

    #[test]
    fn the_primes_are_primes_with_a_root_of_order_2_to_the_50() {
        for f in &FIELDS {
            assert!(zed_numtheory::is_prime(f.p));
            assert_eq!((f.p - 1) % (1 << 50), 0);
            // A quadratic nonresidue: root^((p-1)/2) = -1, so root^((p-1)/2^50) has order 2^50.
            let r = f.pow(f.to_mont(f.root), (f.p - 1) / 2);
            assert_eq!(f.mul(r, 1), f.p - 1);
            assert!(f.p < 1 << 62);
        }
    }

    /// A [`Factor`] keeps its spectra for two or more products above [`MUL_LEAF`] (here 48
    /// words, with num-bigint's Toom-3 never chosen) and none for one, and its products equal
    /// num-bigint's for every width of the other factor up to `other`, edge forms included,
    /// whose all-ones words give the widest carry out of the top; at points just filled
    /// (`words(x) + other - 1` a power of two) and just past one.
    #[test]
    fn factor_products_agree_with_num_bigint() {
        for (wx, other) in [
            (49, 49),
            (64, 65),
            (65, 64),
            (100, 60),
            (200, 57),
            (300, 300),
        ] {
            for x in forms(wx, wx as u64) {
                assert!(
                    Factor::new(x.clone(), other, 1).spectra.is_none(),
                    "{wx}, one use"
                );
                let factor = Factor::new(x.clone(), other, 2);
                assert!(factor.spectra.is_some(), "{wx} by {other} words, two uses");
                for wy in [1, 2, 48, 49, other - 1, other] {
                    for y in forms(wy, 11 + wy as u64) {
                        assert_eq!(factor.mul(&y), &x * &y, "{wx} by {wy} of {other} words");
                    }
                }
                assert!(factor.mul(&BigUint::zero()).is_zero());
            }
        }
    }

    #[test]
    fn products_agree_with_num_bigint() {
        let sizes = [1, 47, 48, 49, 50, 64, 100, 129, 300, 1000, 1500];
        for (i, &la) in sizes.iter().enumerate() {
            for &lb in &sizes[i..] {
                for (x, y) in forms(la, la as u64)
                    .iter()
                    .zip(forms(lb, 7 + lb as u64).iter())
                {
                    assert_eq!(mul(x, y), x * y, "{la} by {lb} words");
                    assert_eq!(mul(y, x), x * y, "{lb} by {la} words");
                }
            }
            for x in forms(la, 3) {
                assert_eq!(mul(&x, &x), &x * &x, "square of {la} words");
            }
        }
        assert!(mul(&BigUint::zero(), &random(1, 100)).is_zero());
        let neg = -BigInt::from(random(2, 80));
        let pos = BigInt::from(random(3, 90));
        assert_eq!(mul_int(&neg, &pos), &neg * &pos);
        assert_eq!(mul_int(&neg, &neg), &neg * &neg);
    }

    /// Numbers of `words` words whose words are each 0, 1, `2^63`, `2^64 - 2` or `2^64 - 1`,
    /// the top one not zero: the cases where a quotient word's estimate is corrected.
    fn edgy(seed: u64, words: usize) -> BigUint {
        let pick = [0u64, 1, 1 << 63, u64::MAX - 1, u64::MAX];
        let mut w: Vec<u64> = random(seed, words)
            .iter_u64_digits()
            .map(|d| pick[(d % 5) as usize])
            .collect();
        w.resize(words, 0);
        w[words - 1] |= 1;
        from_words(w)
    }

    /// 200 nonzero words of a divisor of 1024, by a quotient of 1024 words: in one run long
    /// division is cheaper, spread one apart the reciprocal is, as `crossover div-sparse 1024`
    /// measured (DIV-crossover-model: 181 spread words took 0.68 times long division's time by
    /// the reciprocal; dense words cost 3.2 ns each against 8.5 ns spread). Until SPARSE_RUN
    /// both took long division.
    #[test]
    fn runs_of_nonzero_words_decide_long_division_or_the_reciprocal() {
        let (w, k) = (1024usize, 200usize);
        let divisor = |at: &dyn Fn(usize) -> usize| {
            let mut words = vec![0u64; w];
            for i in 0..k {
                words[at(i)] = (0x9e37_79b9_7f4a_7c15 ^ i as u64) | 1;
            }
            words[w - 1] |= 1 << 63;
            from_words(words)
        };
        let run = divisor(&|i| w - k + i);
        let spread = divisor(&|i| i * (w - 1) / (k - 1));
        assert_eq!(nonzero_runs(&run), (k, 1));
        assert_eq!(nonzero_runs(&spread), (k, k));
        assert_eq!(nonzero_runs(&BigUint::from(0b1011u32)), (1, 1));
        assert_eq!(nonzero_runs(&((BigUint::one() << 128u32) + 1u32)), (2, 2));
        let reciprocal = newton_cost(w, w);
        assert!(sparse_div_cost(w, &run) < reciprocal, "one run");
        assert!(sparse_div_cost(w, &spread) > reciprocal, "spread");
    }

    #[test]
    fn rows_and_long_division_over_nonzero_words_agree_with_num_bigint() {
        for &la in &[1usize, 2, 3, 5, 64, 200] {
            for &lb in &[2usize, 3, 4, 65, 130] {
                for seed in 0..20 {
                    let (x, y) = (edgy(seed, la), edgy(seed + 100, lb));
                    assert_eq!(sparse_mul(&x, &y), &x * &y, "{la} by {lb} words");
                    assert_eq!(sparse_div_rem(&x, &y), x.div_rem(&y), "{la} by {lb} words");
                    let z = &x * &y + (&y - 1u32);
                    assert_eq!(sparse_div_rem(&z, &y), (x.clone(), &y - 1u32));
                }
                for (x, y) in forms(la.max(2), 17 + la as u64)
                    .iter()
                    .zip(forms(lb, 19 + lb as u64).iter())
                {
                    assert_eq!(sparse_mul(x, y), x * y, "{la} by {lb} words");
                    let z = x * y + (y - 1u32);
                    assert_eq!(sparse_div_rem(&z, y), (x.clone(), y - 1u32));
                }
            }
        }
        // A sparse divisor reused, as a kept power's remainder uses one.
        let d = (BigUint::one() << 20_000u32) + 1u32;
        let div = Divisor::new(Cow::Borrowed(&d), 2 * d.bits());
        assert!(matches!(div.by, By::Sparse));
        let x = (random(3, 600) % &d) << (64 * 313) | random(4, 313);
        assert_eq!(div.div_rem(&x), x.div_rem(&d));
    }

    /// [`newton_cost`] charges a quotient of `qw` words, wider than the divisor's `bw`, the
    /// blocks [`Divisor::blocks`] reads after its first: `(qw - 1) / bw` rounded up, which is
    /// `qw / bw` rounded up less one where `qw` is 1 more than a multiple of `bw`.
    #[test]
    fn the_cost_of_the_blocks_counts_the_blocks_read() {
        for bw in 1..=5usize {
            let d = (BigUint::one() << (64 * bw - 1)) + 1u32;
            let div = Divisor::new(Cow::Borrowed(&d), 64 * 8 * bw as u64);
            for qw in bw + 1..=6 * bw + 1 {
                let a = (BigUint::one() << (64 * (qw + bw - 1) - 1)) + 3u32;
                let mut steps = 0usize;
                div.blocks(&a, |_, _| steps += 1);
                let blocks = (qw - 1).div_ceil(bw);
                assert_eq!(steps, blocks + 1, "bw {bw} qw {qw}");
                let cost = (blocks as f64 + 3.0) * transform_cost(2 * bw);
                assert_eq!(newton_cost(qw, bw), cost, "bw {bw} qw {qw}");
            }
        }
    }

    #[test]
    fn quotients_agree_with_num_bigint() {
        let sizes = [1, 60, 64, 65, 70, 100, 200, 400, 777];
        for &la in &sizes {
            for &lb in &sizes {
                for (x, y) in forms(la, 11 + la as u64)
                    .iter()
                    .zip(forms(lb, 13 + lb as u64).iter())
                {
                    assert_eq!(div_rem(x, y), x.div_rem(y), "{la} by {lb} words");
                    assert_eq!(rem(x, y), x % y, "{la} by {lb} words, remainder only");
                    let z = x * y + (y - 1u32);
                    assert_eq!(div_rem(&z, y), (x.clone(), y - 1u32), "{la} by {lb} words");
                    let z = x * y;
                    assert_eq!(div_rem(&z, y), (x.clone(), BigUint::zero()));
                }
            }
        }
        // The reciprocal of every precision near a power of two.
        for k in [2049u64, 4096, 4097, 8191, 8192, 8193, 30001] {
            for x in [
                (BigUint::one() << k) - 1u32,
                BigUint::one() << (k - 1),
                random(k, 470) >> (470 * 64 - k) | (BigUint::one() << (k - 1)),
            ] {
                assert_eq!(
                    reciprocal(&x, k),
                    (BigUint::one() << (2 * k)) / &x,
                    "{k} bits"
                );
            }
        }
        // A divisor reused, of bits not a multiple of 64, and dividends up to `d 2^(64 len)`.
        for (bits, seed) in [(4097u64, 41u64), (6000, 43), (8191, 47), (64 * 100, 53)] {
            let d = random(seed, 130) >> (130 * 64 - bits) | (BigUint::one() << (bits - 1));
            let div = Divisor::new(Cow::Borrowed(&d), 2 * d.bits());
            let len = bits.div_ceil(64);
            let top = (&d << (64 * len)) - 1u32;
            for x in [
                top.clone(),
                &top >> 1u32,
                random(seed + 1, 2 * len as usize) % &top,
                d.clone(),
                &d - 1u32,
            ] {
                assert_eq!(div.div_rem(&x), x.div_rem(&d), "{bits} bits");
            }
        }
        let a = -BigInt::from(random(5, 300));
        let m = BigInt::from(random(6, 120));
        for (a, m) in [(&a, &m), (&-&a, &m), (&a, &-&m), (&-&a, &-&m)] {
            assert_eq!(div_euclid(a, m), num_traits::Euclid::div_euclid(a, m));
        }
        // Floor division and its remainder on every sign, exact and inexact, a dividend of 0
        // and one below the divisor, past the leaf (the tests' `DIV_COST` is infinite).
        let exact = &m * BigInt::from(random(7, 180));
        let zero = BigInt::zero();
        for (a, m) in [(&a, &m), (&exact, &m), (&zero, &m), (&m, &a)] {
            for (a, m) in [(a, m), (&-a, m), (a, &-m), (&-a, &-m)] {
                let want = (Integer::div_floor(a, m), Integer::mod_floor(a, m));
                assert_eq!((div_floor(a, m), mod_floor(a, m)), want, "{a} by {m}");
            }
        }
    }

    /// Plan row KERNEL-bz-short-quotient: [`div_rem_short_quotient`]'s estimate from the top
    /// bits is one too high where the divisor's dropped bits are all ones, and one correction
    /// gives num-bigint's quotient. `b = b' 2^t + 2^t - 1` and `a = q0 b' 2^t`, with `b'` of
    /// `j + 64` bits and `q0` of `j`, so that `a' b'` is under `2^(j + bits(b') - 1)` and the
    /// function's shift is this `t`: `a' / b' = q0` exactly, and `a < q0 b`, so the quotient is
    /// `q0 - 1`. Each case has `b` of more than [`DIV_LEAF`] bits and a quotient of at most
    /// `DIV_LEAF`, the sizes [`div_rem`] sends to the function, which is also called directly.
    /// Then `q0 b + b - 1`, with quotient `q0`, which needs no correction. Negative
    /// control: the correction taken out (`(q, a - p)` alone) panics on the first case.
    #[test]
    fn a_short_quotient_is_corrected_once() {
        let one = BigUint::one();
        for (j, t, seed) in [
            (2u64, 4100u64, 61u64),
            (64, 4000, 67),
            (1000, 7000, 71),
            (4096, 64, 73),
        ] {
            let h = j + 64;
            // Each factor is under 1.25 times its top bit, so the product is under 2^(j + h - 1).
            let low = |bits: u64, seed| {
                bits.checked_sub(3).map_or(BigUint::zero(), |b| {
                    random(seed, h.div_ceil(64) as usize) % (&one << b)
                })
            };
            let q0 = (&one << (j - 1)) + low(j, seed);
            let top = (&one << (h - 1)) + low(h, seed + 1);
            let b = (&top << t) + (&one << t) - 1u32;
            let a = (&q0 * &top) << t;
            assert_eq!(
                b.bits() - (a.bits() - b.bits() + 1) - 64,
                t,
                "{j} bits: the shift"
            );
            assert!(
                a.bits() - b.bits() < DIV_LEAF && b.bits() > DIV_LEAF,
                "{j} bits: div_rem takes div_rem_short_quotient"
            );
            assert_eq!(
                (&a >> t) / (&b >> t),
                q0,
                "{j} bits: the estimate is one too high"
            );
            assert_eq!(
                div_rem_short_quotient(&a, &b),
                (&q0 - 1u32, &a + &b - &q0 * &b),
                "{j} bits, by the function itself"
            );
            assert_eq!(
                div_rem(&a, &b),
                (&q0 - 1u32, &a + &b - &q0 * &b),
                "{j} bits"
            );
            assert_eq!(div_rem(&a, &b), a.div_rem(&b), "{j} bits");
            let c = &q0 * &b + &b - 1u32;
            assert_eq!(
                div_rem(&c, &b),
                (q0.clone(), &b - 1u32),
                "{j} bits, no correction"
            );
        }
    }

    /// [`approx_reciprocal`] keeps `a X < 2^2p <= a (X + 2)` for every `a` of 5 to 13 bits,
    /// where the tests' leaf lets Newton's step start, and for edge and random `a` at
    /// precisions next to a word, the production leaf and powers of two.
    #[test]
    fn approximate_reciprocals_keep_their_bounds() {
        let one = BigUint::one();
        let check = |a: &BigUint, p: u64| {
            let tw = roots(cyclic_points(p));
            let x = approx_reciprocal(a, p, &tw, RECIP_LEAF);
            let power = &one << (2 * p);
            assert!(a * &x < power, "{p} bits, a = {a}: a X is not below 2^2p");
            assert!(
                a * (&x + 2u32) >= power,
                "{p} bits, a = {a}: a (X + 2) is below 2^2p"
            );
        };
        for p in 5..=13u64 {
            for a in (1u64 << (p - 1))..(1u64 << p) {
                check(&BigUint::from(a), p);
            }
        }
        for p in [
            63u64, 64, 65, 127, 128, 129, 2047, 2048, 2049, 4096, 4097, 8191, 8192, 8193, 30001,
        ] {
            let w = p.div_ceil(64) as usize;
            let top = &one << (p - 1);
            for a in [
                (&one << p) - 1u32,
                (&one << p) - 2u32,
                top.clone(),
                &top + 1u32,
                random(p, w) >> (64 * w as u64 - p) | &top,
                edgy(p, w) >> (64 * w as u64 - p) | &top,
            ] {
                check(&a, p);
            }
        }
    }

    /// [`unfold`] recovers every value from its residue modulo `2^(64 m) - 1` and its low word,
    /// below zero and above, at the ends of its range.
    #[test]
    fn values_unfold_from_their_residues() {
        let one = BigInt::one();
        for m in [1usize, 2, 4] {
            let modulus: BigInt = (&one << (64 * m)) - 1;
            let limit: BigInt = &one << (64 * m + 61);
            let mut values = vec![BigInt::zero(), one.clone(), &modulus - 1, modulus.clone()];
            values.extend([1u64, 3, 64].map(|s| BigInt::from(random(s, m + 1)) % &limit));
            values.extend([&limit - 1, &modulus + 1, &modulus * 7 + 5]);
            for v in values.clone() {
                values.push(-v);
            }
            for v in values {
                let r = v.mod_floor(&modulus).magnitude().to_u64_digits();
                let low = v.mod_floor(&(&one << 64)).to_u64().expect("below 2^64");
                let (negative, words) = unfold(r, m, low);
                let back = BigInt::from_biguint(Sign::Plus, from_words(words));
                assert_eq!(if negative { -back } else { back }, v, "{m} words");
            }
        }
    }

    /// [`Level::div_rem`], the division of [`div_rem`] and [`Divisor`] past their leaves, for
    /// every divisor of 1 to 6 bits, every precision `k` of its reciprocal and every dividend
    /// below `2^(n + k - 1)`, or below `2^2n` and at the top of its range `2^(n + 64)` for
    /// `k = n`.
    #[test]
    fn levels_divide_like_num_bigint_exhaustively() {
        for n in 1..=6u64 {
            for d in (1u64 << (n - 1))..(1u64 << n) {
                let big = BigUint::from(d);
                for k in 1..=n {
                    let (linear, cyclic) = level_points(n, k);
                    let tw = roots(linear.max(cyclic));
                    let level = Level::new(vec![d], n, k, &tw);
                    let mut xs: Vec<BigUint> = match k == n {
                        true => (0..1u64 << (2 * n)).map(BigUint::from).collect(),
                        false => (0..1u64 << (n + k - 1)).map(BigUint::from).collect(),
                    };
                    if k == n {
                        let top = BigUint::one() << (n + 64);
                        xs.extend([&top - 1u32, (&big << 64u32) - 1u32, &top >> 1u32]);
                        xs.extend((0..8).map(|s| random(s, 2) % &top));
                    }
                    for x in xs {
                        let (q, r) = level.div_rem(&x.to_u64_digits(), &tw);
                        assert_eq!(
                            (from_words(q), from_words(r)),
                            x.div_rem(&big),
                            "{x} by {d}, k = {k}"
                        );
                    }
                }
            }
        }
    }

    /// [`div_rem`] and [`Divisor`] next to the powers of two of their transforms' points, for
    /// random, edge and long-carry operands, with quotients as wide as the divisor and
    /// narrower.
    /// The switch of [`DIV_COST_FIT`] takes the method that did less work in instructions for a
    /// quotient of as many words as the divisor (`crossover div-leaf 1 1 0
    /// 2048,2049,2896,4096,5793`, zed_icount, 2026-11-23; plan row
    /// PERF-div-narrow-quotient-factor): the reciprocal at 2048 words (0.881 times num-bigint's
    /// work), num-bigint at 2049 (the reciprocal 1.527 times, its points doubling) and at 1024
    /// (1.183 times), the reciprocal at 2896, 4096 and 5793 (0.955, 0.635 and 0.705 times).
    /// With [`newton_cost`] on [`transform_cost`] and [`DIV_SAME`] 1.295 the build took the
    /// reciprocal at 2049 and num-bigint at 2896.
    #[test]
    fn the_division_switch_takes_the_cheaper_method_at_a_square_quotient() {
        for (w, by_num_bigint) in [
            (1024, true),
            (2048, false),
            (2049, true),
            (2896, false),
            (4096, false),
            (5793, false),
        ] {
            let top = |n: usize| BigUint::one() << (64 * n - 1);
            let (a, b) = (
                random(w as u64, 2 * w - 1) | top(2 * w - 1),
                random(!(w as u64), w) | top(w),
            );
            let qw = words(&a) - words(&b) + 1;
            assert_eq!(qw, w);
            let flip = past_leaf_cost(qw, &b) / num_bigint_div_units(qw, w);
            assert_eq!(
                DIV_COST_FIT <= flip,
                by_num_bigint,
                "{w} words: flip {flip}"
            );
        }
    }

    #[test]
    fn wide_quotients_agree_with_num_bigint() {
        let base = crate::seed::seed("wide_quotients_agree_with_num_bigint");
        for (la, lb) in [
            (130, 65),
            (1023, 512),
            (2048, 1024),
            (2049, 1025),
            (2047, 1024),
            (1500, 1100),
            (3000, 2000),
            (4100, 2050),
        ] {
            let seed = base ^ la as u64;
            let pairs = [
                (random(seed, la), random(seed.wrapping_add(50), lb)),
                (edgy(seed, la), edgy(seed.wrapping_add(50), lb)),
            ];
            for (x, y) in pairs.iter().chain(
                forms(la, seed.wrapping_add(9))
                    .iter()
                    .zip(forms(lb, seed.wrapping_add(10)).iter())
                    .map(|(x, y)| (x.clone(), y.clone()))
                    .collect::<Vec<_>>()
                    .iter(),
            ) {
                assert_eq!(div_rem(x, y), x.div_rem(y), "{la} by {lb} words");
                assert_eq!(rem(x, y), x % y, "{la} by {lb} words, remainder only");
                let q = x >> (64 * (la - lb) as u64);
                let z = &q * y + (y - 1u32);
                assert_eq!(div_rem(&z, y), (q.clone(), y - 1u32), "{la} by {lb} words");
                let div = Divisor::new(Cow::Borrowed(y), 2 * y.bits());
                let top = (y << (64 * lb as u64)) - 1u32;
                for v in [&top, &(x % &top), &(&q * y)] {
                    assert_eq!(div.div_rem(v), v.div_rem(y), "{la} by {lb} words, reused");
                }
            }
        }
    }

    /// The first block [`Divisor::blocks`] reads, of as many words as `d`, divides by long
    /// division in O(n) bytes whether it is below `d` or not (PERF-div-bytes-2p17): a block at
    /// or above `d` allocates at most a word more for each word of `d` than one below it. It
    /// went to num-bigint, whose recursive division (past 64 words of divisor) allocated
    /// about 46 words for each word of `d` where the block was not below `d`, and returned at
    /// once where it was, so the bytes of `dividing_a_wide_number_scales` depended on the
    /// seed's top words.
    #[test]
    fn a_divisors_first_block_divides_in_linear_bytes() {
        let len = 1024;
        let top_word = (BigUint::one() << (64 * len)) - (BigUint::one() << (64 * (len - 1)));
        let d = random(4, len) | (BigUint::one() << (64 * len - 1));
        // Dividends of `len` words, so `blocks` reads the first block only.
        let above = &random(5, len) | &top_word;
        let below = &d >> 1u32;
        assert!(above > d && below < d && words(&below) == len);
        let div = Divisor::new(Cow::Borrowed(&d), 64 * len as u64);
        let bytes = |a: &BigUint| {
            let start = zed_alloc_count::allocated();
            let (q, r) = div.div_rem(a);
            let used = zed_alloc_count::allocated() - start;
            assert_eq!((q, r), a.div_rem(&d), "{} words by {len}", words(a));
            used
        };
        let (b_below, b_above) = (bytes(&below), bytes(&above));
        assert!(
            b_above <= b_below + 8 * len as u64,
            "a first block above d allocated {b_above} bytes, below it {b_below}, at {len} words"
        );
    }

    /// [`matrix_product`] equals num-bigint's products, by shared transforms (above
    /// `MUL_LEAF`, here 48 words) and one by one: 2x2 by 2x2 and 2x2 by 2x1, signed, with zero
    /// entries, edge words and unbalanced widths, and with a shift, from entries made
    /// divisible by `2^s` and from the half gcd's own matrices, which divide factors wider
    /// than the result, so that factors are folded.
    #[test]
    fn matrix_products_agree_with_num_bigint() {
        SHARED_PRODUCTS.with(|v| v.set((0, 0)));
        let plain = |l: &[BigInt; 4], r: &[BigInt]| -> Vec<BigInt> {
            let c = r.len() / 2;
            (0..2 * c)
                .map(|out| {
                    let (i, j) = (out / c, out % c);
                    &l[2 * i] * &r[j] + &l[2 * i + 1] * &r[c + j]
                })
                .collect()
        };
        let pick = |s: u64, w: usize| -> BigInt {
            let x = match s % 3 {
                0 => random(s, w),
                1 => edgy(s, w),
                _ => forms(w, s)[(s / 3 % 4) as usize].clone(),
            };
            match (s >> 2) & 1 {
                1 => -BigInt::from(x),
                _ => BigInt::from(x),
            }
        };
        for &(wl, wr) in &[
            (49usize, 49usize),
            (64, 64),
            (60, 200),
            (200, 60),
            (50, 700),
            (300, 301),
        ] {
            for seed in 0..6u64 {
                let mut l: [BigInt; 4] = std::array::from_fn(|i| pick(seed * 8 + i as u64, wl));
                let mut r: [BigInt; 4] = std::array::from_fn(|i| pick(seed * 8 + 4 + i as u64, wr));
                if seed == 5 {
                    (l[1], r[2]) = (BigInt::zero(), BigInt::zero());
                }
                let (lr, rr) = (l.each_ref(), r.each_ref());
                assert_eq!(
                    matrix_product(lr, &rr, None),
                    plain(&l, &r),
                    "{wl} by {wr} words"
                );
                for s in [0u64, 1, 63, 64, 1000, 64 * wl as u64 + 5] {
                    let ls = l.each_ref().map(|x| x << s);
                    let got = matrix_product(ls.each_ref(), &[&r[0], &r[1]], Some(s));
                    assert_eq!(got, plain(&l, &r[..2]), "{wl} by {wr} words, shift {s}");
                }
            }
        }
        // The half gcd's matrices, applied to the whole of numbers wider than their residues.
        for (words, seed) in [(120usize, 1u64), (400, 2), (700, 3)] {
            let a = BigInt::from(random(seed, words) | BigUint::one());
            let b = BigInt::from(random(seed + 10, words) << 1u32);
            for k in [64 * words as u64 / 4, 64 * words as u64 / 2] {
                let h = half(a.clone(), b.clone(), k, Want::Matrix, LIFT_BITS);
                let (j, m) = (h.j, h.r.expect("asked for the matrix"));
                let [m00, m01, m10, m11] = &m.0;
                let want = (
                    (m00 * &a + m01 * &b) >> (2 * j),
                    (m10 * &a + m11 * &b) >> (2 * j),
                );
                assert_eq!(m.apply(&a, &b, j), want, "{words} words, k = {k}");
            }
        }
        let (shared, folded) = SHARED_PRODUCTS.with(|v| v.get());
        assert!(shared > 0 && folded > 0, "{shared} shared, {folded} folded");
    }

    /// [`half`] for each [`Want`]: the same halvings, the same matrix, and the pair that matrix
    /// gives, at widths on both sides of the lift's limit in [`half_low`] (`64 MUL_LEAF` bits,
    /// 3,072 in the tests), with budgets from 1 to above the width, for both signs and second
    /// numbers of every valuation class.
    #[test]
    fn half_pairs_match_the_matrix() {
        let base = crate::seed::seed("half_pairs_match_the_matrix");
        for words in [1usize, 2, 3, 5, 8, 17, 40, 120] {
            let bits = 64 * words as u64;
            for (i, x) in forms(words, base ^ words as u64).into_iter().enumerate() {
                let a = x | BigUint::one();
                let y = random(base.rotate_left(29).wrapping_add(i as u64), words);
                for b in [
                    BigUint::zero(),
                    &y | BigUint::one(),
                    &y << 1u32,
                    (&y >> 1u32) << (bits / 3 + 1),
                    forms(words, 7)[i].clone() << 2u32,
                ] {
                    for (sa, sb) in [(1i32, 1i32), (-1, 1), (1, -1), (-1, -1)] {
                        let a = BigInt::from(a.clone()) * sa;
                        let b = BigInt::from(b.clone()) * sb;
                        for k in [1, HALF_LEAF, HALF_LEAF + 1, bits / 4, bits / 2, bits + 64] {
                            let at = format!("{words} words, form {i}, signs {sa} {sb}, k = {k}");
                            let (j, m, x, y) =
                                half(a.clone(), b.clone(), k, Want::Both, LIFT_BITS).both();
                            assert!(j <= k, "{at}: {j} halvings");
                            let [m00, m01, m10, m11] = &m.0;
                            let (p, q) = (m00 * &a + m01 * &b, m10 * &a + m11 * &b);
                            let low = (BigInt::one() << (2 * j)) - 1;
                            assert!((&p & &low).is_zero() && (&q & &low).is_zero(), "{at}");
                            let pair = (p >> (2 * j), q >> (2 * j));
                            assert_eq!((&x, &y), (&pair.0, &pair.1), "{at}");
                            let h = half(a.clone(), b.clone(), k, Want::Matrix, LIFT_BITS);
                            assert_eq!((h.j, h.r.map(|r| r.0), h.pair), (j, Some(m.0), None));
                            let h = half(a.clone(), b.clone(), k, Want::Pair, LIFT_BITS);
                            assert_eq!((h.j, h.r.is_none(), h.pair), (j, true, Some(pair)));
                        }
                    }
                }
            }
        }
    }

    /// [`inverse_mod_pow2`] at widths around the Newton steps' doublings and their ends.
    #[test]
    fn inverses_modulo_powers_of_two() {
        for w in [
            1u64, 2, 63, 64, 65, 127, 128, 129, 200, 1000, 4096, 4097, 20_000,
        ] {
            let mask = (BigUint::one() << w) - 1u32;
            for x in [
                BigUint::one(),
                mask.clone(),
                random(w, 1 + w as usize / 64) | BigUint::one(),
                (random(w + 1, 2 + w as usize / 32) << 3u32) | BigUint::one(),
            ] {
                let y = inverse_mod_pow2(&x, w);
                assert!(y <= mask, "width {w}");
                assert!(((&x * &y) & &mask).is_one(), "width {w}");
            }
        }
    }

    #[test]
    fn gcds_agree_with_num_bigint() {
        let base = crate::seed::seed("gcds_agree_with_num_bigint");
        let sizes = [1, 2, 16, 17, 40, 100, 300];
        for &la in &sizes {
            for &lb in &sizes {
                for (x, y) in forms(la, base ^ la as u64)
                    .iter()
                    .zip(forms(lb, base.rotate_left(17) ^ lb as u64).iter())
                {
                    assert_eq!(gcd(x, y), x.gcd(y), "{la} and {lb} words");
                    let g = random(base.rotate_left(31), 1 + lb / 3);
                    let (gx, gy) = (x * &g, y * &g);
                    assert_eq!(
                        gcd(&gx, &gy),
                        gx.gcd(&gy),
                        "{la} and {lb} words times a common factor"
                    );
                    let (sx, sy) = (&gx << 77u32, &gy << 300u32);
                    assert_eq!(gcd(&sx, &sy), sx.gcd(&sy), "with powers of two");
                }
            }
        }
        let x = random(base.rotate_left(47), 500);
        assert_eq!(gcd(&x, &BigUint::zero()), x);
        assert_eq!(gcd(&BigUint::zero(), &x), x);
        assert_eq!(gcd(&x, &x), x);
        // Fibonacci neighbours: the longest Euclidean remainder sequence.
        let (mut f, mut g) = (BigUint::one(), BigUint::one());
        for _ in 0..40_000 {
            (f, g) = (g.clone(), f + g);
        }
        assert!(gcd(&f, &g).is_one());
        assert_eq!(gcd(&(&f * 6u32), &(&g * 4u32)), BigUint::from(2u32));
    }

    #[test]
    fn inverses_agree_with_their_definition() {
        // `a x == 1 mod m` when `gcd(a, m) == 1`, and `None` otherwise; moduli odd, even and
        // powers of two, across the leaf width under test (`GCD_LEAF`).
        let check = |a: &BigUint, m: &BigUint, what: &str| match inverse_mod(a, m) {
            Some(x) => {
                assert!(&x < m, "{what}: below the modulus");
                assert!((a * &x % m).is_one() || m.is_one(), "{what}: an inverse");
            }
            None => assert!(!a.gcd(m).is_one(), "{what}: None only for a common factor"),
        };
        let sizes = [1, 2, 16, 17, 40, 100, 300];
        for &la in &sizes {
            for &lb in &sizes {
                for (x, y) in forms(la, 41 + la as u64)
                    .iter()
                    .zip(forms(lb, 43 + lb as u64).iter())
                {
                    check(x, y, &format!("{la} mod {lb} words"));
                    check(
                        x,
                        &(y | BigUint::one()),
                        &format!("{la} mod {lb} words, odd"),
                    );
                    check(
                        &(x | BigUint::one()),
                        &(y << 5u32),
                        &format!("{la} mod {lb}, even"),
                    );
                    let g = random(47, 1 + lb / 3) | BigUint::one();
                    check(
                        &(x * &g),
                        &(y * &g),
                        &format!("{la} and {lb}, common factor"),
                    );
                }
            }
        }
        let m = BigUint::one() << 700u32;
        check(&random(53, 20), &m, "a power of two");
        check(
            &(random(53, 20) | BigUint::one()),
            &m,
            "a power of two, odd",
        );
        check(&BigUint::from(5u32), &BigUint::one(), "modulo 1");
        // Fibonacci neighbours: the longest Euclidean remainder sequence.
        let (mut f, mut g) = (BigUint::one(), BigUint::one());
        for _ in 0..20_000 {
            (f, g) = (g.clone(), f + g);
        }
        check(&f, &g, "Fibonacci neighbours");
        check(&g, &f, "Fibonacci neighbours, swapped");
        check(&(&f << 3u32), &g, "Fibonacci, times 8");
    }

    /// The split's text does not depend on where it hands parts to num-bigint: every handoff
    /// from none (0) to past every power's words, at the powers' widths `31 * 2^i` and next to
    /// them, where the leaves change.
    #[test]
    fn decimals_do_not_depend_on_the_handoff() {
        for handoff in [0, 30, 31, 32, 62, 124, 496, 992, 4000] {
            for words in [1, 31, 32, 61, 62, 63, 500, 1000, 1984, 3000] {
                for x in forms(words, 7 + words as u64) {
                    assert_eq!(
                        to_decimal_split_at(&x, handoff),
                        x.to_string(),
                        "{words} words, handoff {handoff}"
                    );
                }
            }
        }
    }

    #[test]
    fn decimals_agree_with_num_bigint() {
        for words in [1, 50, 100, 106, 107, 200, 213, 500, 1000, 3000] {
            for x in forms(words, 31 + words as u64) {
                assert_eq!(to_decimal(&x), x.to_string(), "{words} words");
            }
        }
        // Zeros in the middle and at the end of a half.
        let ten = BigUint::from(10u32);
        for e in [1024u32, 1025, 2048, 4096, 5000] {
            let x = ten.pow(e);
            assert_eq!(to_decimal(&x), x.to_string());
            let y = &x + 1u32;
            assert_eq!(to_decimal(&y), y.to_string());
            let z = &x - 1u32;
            assert_eq!(to_decimal(&z), z.to_string());
            let w = &x * &x + &x;
            assert_eq!(to_decimal(&w), w.to_string());
        }
        assert_eq!(to_decimal(&BigUint::zero()), "0");
        // Each size at and next to a power's words `31 * 2^i`, where the levels change, and
        // the powers `10^(L 2^i)` and their neighbors, where a half is zero or all nines.
        for i in 0..7 {
            for words in [31 << i, (31 << i) - 1, (31 << i) + 1, 62 << i] {
                for seed in 0..3 {
                    let x = random(seed * 1000 + words as u64, words);
                    assert_eq!(to_decimal(&x), x.to_string(), "{words} words");
                }
            }
            let p = ten.pow((PRINT_LEAF as u32) << i);
            for x in [
                &p - 1u32,
                p.clone(),
                &p + 1u32,
                &p * &p - 1u32,
                &p * &p + &p - 1u32,
            ] {
                assert_eq!(
                    to_decimal(&x),
                    x.to_string(),
                    "10^({PRINT_LEAF} 2^{i}) nearby"
                );
            }
        }
    }

    /// [`derive()`] from the reciprocal of `d^2` and from it plus 1 to 4 (with 3 more bits),
    /// against the reciprocal of `d` by num-bigint's division, for powers of ten and random `d`.
    #[test]
    fn derived_reciprocals_agree_with_division() {
        let ten = BigUint::from(10u32);
        let one = BigUint::one();
        let mut ds: Vec<BigUint> = (0..5).map(|i| ten.pow((PRINT_LEAF as u32) << i)).collect();
        ds.extend([3, 31, 32, 100, 500].map(|w| random(w as u64, w) | &one));
        for d in &ds {
            let n = d.bits();
            let w = n.next_multiple_of(64);
            let dw = d.to_u64_digits();
            let mut m = dw.len().next_power_of_two();
            if n + 2 > 64 * m as u64 {
                m *= 2;
            }
            let tw = FIELDS.each_ref().map(|f| f.twiddles(m));
            let dc = [0, 1, 2].map(|k| FIELDS[k].spectrum(&dw, m, &tw[k]));
            let want = (&one << (w + n)) / d;
            let square = d * d;
            let ea = w + 2 * n;
            let exact = (&one << ea) / &square;
            assert_eq!(
                derive(d, &dw, &dc, &tw, &exact, ea),
                want,
                "{n} bits, exact"
            );
            let above = (&one << (ea + 3)) / &square;
            for e in 0..=4u32 {
                let ya = &above + e;
                assert_eq!(
                    derive(d, &dw, &dc, &tw, &ya, ea + 3),
                    want,
                    "{n} bits, +{e}"
                );
            }
        }
    }
    #[test]
    fn r5_binary_leaf_random_and_adversarial_pairs() {
        use num_integer::Integer;
        let mut checked = 0;
        let base = crate::seed::seed("r5_binary_leaf_random_and_adversarial_pairs");
        for words in [3, 4, 5, 16, 31, 64, 127, 256, 511] {
            for seed in (0..3).map(|i| base.wrapping_add(i)) {
                let x = random(seed, words) | BigUint::one();
                let y = random(seed.wrapping_add(999), words) | BigUint::one();
                for (a, b) in [
                    (x.clone(), y),
                    (x.clone(), x.clone()),
                    (x.clone(), &x + 2u32),
                    (x.clone(), &x - 2u32),
                    (x.clone(), &x + (BigUint::one() << 20u32)),
                    (x.clone(), &x + (BigUint::one() << 30u32)),
                    (x.clone(), &x + (BigUint::one() << 31u32)),
                    (x.clone(), &x << 129u32),
                    (&x * 35u32, (&x + 2u32) * 35u32),
                    ((BigUint::one() << (64 * words)) - 1u32, x.clone()),
                ] {
                    let want = a.gcd(&b);
                    assert_eq!(gcd(&a, &b), want, "words={words}, seed={seed}");
                    assert_eq!(gcd(&b, &a), want, "reversed words={words}, seed={seed}");
                    checked += 2;
                }
            }
        }
        eprintln!("R5 gcd independent comparisons={checked}");
    }
    #[test]
    fn binary_leaf_exercises_both_sides_of_the_register_shift_bound() {
        use num_integer::Integer;
        let x = (BigUint::one() << 256usize) + 1u32;
        for shift in [30usize, 31] {
            STEIN_ACCEPTED_SHIFT.with(|v| v.set(0));
            STEIN_REJECTED_SHIFT.with(|v| v.set(0));
            let y = &x + (BigUint::one() << shift);
            assert_eq!(stein_odd(&x, 0, &y, 0), x.gcd(&y));
            let accepted = STEIN_ACCEPTED_SHIFT.with(|v| v.get());
            let rejected = STEIN_REJECTED_SHIFT.with(|v| v.get());
            assert!(accepted <= 30);
            if shift == 30 {
                assert_eq!(accepted, 30);
            } else {
                assert!(rejected >= 31);
            }
            eprintln!("gcd boundary shift={shift}, accepted={accepted}, rejected={rejected}");
        }
    }

    /// Plain extended Euclid on nonnegative numbers: `(g, s, t)` with `s a + t b = g`.
    fn euclid(a: &BigUint, b: &BigUint) -> (BigUint, BigInt, BigInt) {
        let (mut r0, mut r1) = (BigInt::from(a.clone()), BigInt::from(b.clone()));
        let (mut s0, mut s1) = (BigInt::one(), BigInt::zero());
        let (mut t0, mut t1) = (BigInt::zero(), BigInt::one());
        while !r1.is_zero() {
            let q = &r0 / &r1;
            let r2 = &r0 - &q * &r1;
            let s2 = &s0 - &q * &s1;
            let t2 = &t0 - &q * &t1;
            r0 = std::mem::replace(&mut r1, r2);
            s0 = std::mem::replace(&mut s1, s2);
            t0 = std::mem::replace(&mut t1, t2);
        }
        (r0.into_parts().1, s0, t0)
    }

    /// [`step`] with `b = 2^j b'` for `j` on both sides of 127, where `q` is found in 128-bit
    /// registers below and from `b'^-1 mod 2^(j+1)` of `j + 1` bits from there on: `q` is
    /// centered, `|q| < 2^j`, `a + q b'` is a multiple of `2^(j+1)`, and the new second number
    /// is `(a + q b') / 2^j`; for odd `a` of either sign and of fewer or more bits than
    /// `2^(j+1)`.
    #[test]
    fn a_step_of_127_halvings_or_more_meets_its_definition() {
        for j in [126u64, 127, 128, 191, 200, 1000] {
            let words = j as usize / 64 + 2;
            for seed in 1..=4 {
                let b1 = BigInt::from(random(seed, words) | BigUint::one());
                let b = &b1 << j;
                let narrow = BigInt::from(random(seed + 50, 1) | BigUint::one());
                let wide = BigInt::from(random(seed + 90, 2 * words) | BigUint::one());
                for a in [
                    BigInt::one(),
                    -BigInt::one(),
                    narrow.clone(),
                    -narrow,
                    wide.clone(),
                    -wide,
                ] {
                    let (q, b1_out, r) = step(&a, &b, j);
                    assert_eq!(b1_out, b1, "j={j}, seed={seed}");
                    assert!(q.magnitude() < &(BigUint::one() << j), "j={j}, seed={seed}");
                    let sum = &a + mul_int(&q, &b1);
                    assert!(
                        sum.trailing_zeros().is_none_or(|z| z > j),
                        "j={j}, seed={seed}: a + q b' is not a multiple of 2^(j+1)"
                    );
                    assert_eq!(r << j, sum, "j={j}, seed={seed}");
                }
            }
        }
    }

    /// [`bezout`] of an odd number and `2^j` times an odd number, `j` from 126 to 4097, in
    /// both orders and with a common power of two, and with odd parts of 1 to 40 words, all
    /// ones among them: a valuation of 127 or more reaches the step whose `q` is found from
    /// an inverse of `j + 1` bits. The gcd is that of plain extended Euclid, and the
    /// coefficients satisfy `s a + t b = g`.
    #[test]
    fn bezout_of_a_number_with_127_or_more_factors_of_two_matches_euclid() {
        let all_ones = |words: usize| (BigUint::one() << (64 * words)) - 1u32;
        for j in [126u64, 127, 128, 129, 200, 255, 256, 1000, 4097] {
            for seed in 1..=3 {
                for (wa, wb) in [(1, 1), (1, 4), (4, 1), (40, 3), (3, 40)] {
                    let odd_a = random(seed, wa) | BigUint::one();
                    let odd_b = random(seed + 30, wb) | BigUint::one();
                    let wide = &odd_b << j;
                    let shared = &odd_a * 3u32 * 5u32 * 7u32;
                    for (a, b) in [
                        (odd_a.clone(), wide.clone()),
                        (wide.clone(), odd_a.clone()),
                        (&odd_a << 5u32, &wide << 5u32),
                        (all_ones(wa), wide.clone()),
                        (shared.clone(), &odd_a << j),
                        (&odd_a << j, shared),
                    ] {
                        let at = format!("j={j}, seed={seed}, words=({wa}, {wb})");
                        let (g, s, t) = bezout(&a, &b);
                        let (want, es, et) = euclid(&a, &b);
                        let (ia, ib) = (BigInt::from(a), BigInt::from(b));
                        let want_int = BigInt::from(want.clone());
                        assert_eq!(&es * &ia + &et * &ib, want_int, "Euclid, {at}");
                        assert_eq!(g, want, "{at}");
                        assert_eq!(mul_int(&s, &ia) + mul_int(&t, &ib), want_int, "{at}");
                    }
                }
            }
        }
    }

    /// [`mul_add_pair`] equals `v0 * p1 + v1 * p0` across zero, below-leaf, above-leaf NTT, and
    /// unequal-width operands (including all-ones edge forms with maximum carries).
    #[test]
    fn mul_add_pair_agrees_with_separate_products() {
        let base = crate::seed::seed("mul_add_pair_agrees_with_separate_products");
        let zero = BigUint::zero();
        let x = random(base, 60);
        assert_eq!(mul_add_pair(&zero, &x, &x, &x), &x * &x);
        assert_eq!(mul_add_pair(&x, &x, &zero, &x), &x * &x);
        for &(w0, w1, w2, w3) in &[
            (1usize, 1usize, 1usize, 1usize),
            (48, 48, 48, 48),
            (49, 49, 49, 49),
            (64, 64, 64, 64),
            (65, 65, 65, 65),
            (100, 120, 90, 130),
            (300, 300, 300, 300),
        ] {
            for (i, (((v0, p1), v1), p0)) in forms(w0, base ^ w0 as u64)
                .into_iter()
                .zip(forms(w1, base.wrapping_add(1) ^ w1 as u64))
                .zip(forms(w2, base.wrapping_add(2) ^ w2 as u64))
                .zip(forms(w3, base.wrapping_add(3) ^ w3 as u64))
                .enumerate()
            {
                let got = mul_add_pair(&v0, &p1, &v1, &p0);
                let want = &v0 * &p1 + &v1 * &p0;
                assert_eq!(got, want, "widths ({w0},{w1},{w2},{w3}) form {i}");
            }
        }
    }

    /// [`scaled_root`] and [`scaled_children`] satisfy Bernstein (2004) Theorems 2.1 and 2.2 on
    /// both the Theorem 2.1 (`mul`) and Theorem 2.2 (shared-spectrum cyclic NTT) paths.
    #[test]
    fn scaled_root_and_children_preserve_precision() {
        let base = crate::seed::seed("scaled_root_and_children_preserve_precision");
        for &(wa, wb) in &[(1usize, 1usize), (2, 3), (60, 60), (130, 130)] {
            let a = random(base ^ wa as u64, wa) | BigUint::from(3u32);
            let b = random(base.wrapping_add(17) ^ wb as u64, wb) | BigUint::from(5u32);
            let v = &a * &b;
            let u = random(base.wrapping_add(31), wa + wb) % &v;
            let guard = 8u64;
            let (f_auto, auto_ntt) = scaled_node_precision(&v, &a, &b, guard, u64::MAX);
            let ea = a.bits() + guard;
            let eb = b.bits() + guard;
            let mut configs = vec![(v.bits() + guard, false)];
            let m = usize::try_from((v.bits() + guard).div_ceil(64))
                .expect("words")
                .next_power_of_two();
            configs.push((64 * m as u64, true));
            if auto_ntt {
                configs.push((f_auto, true));
            }
            for (f, use_ntt) in configs {
                let sv = scaled_root(&u, &v, f);
                assert!(sv.bits() <= f, "sv fits in {f} bits");
                // `|sv / 2^f - u / v| < 1.5 / 2^f` <=> `|2 * (u * 2^f - v * sv)| < 3 * v`.
                let lhs = (&u << f) * 2u32;
                let rhs = (&v * &sv) * 2u32;
                let diff = if lhs >= rhs { lhs - rhs } else { rhs - lhs };
                assert!(diff < &v * 3u32, "root bound failed for ({wa},{wb}) f={f}");
                let (sa, sb) = scaled_children(&sv, f, use_ntt, &a, ea, &b, eb);
                for (child, s_child, e) in [(&a, &sa, ea), (&b, &sb, eb)] {
                    let got = scaled_leaf_rem(child, s_child, e);
                    assert_eq!(
                        got,
                        &u % child,
                        "child remainder mismatch ({wa},{wb}) use_ntt={use_ntt}"
                    );
                }
            }
        }
    }
}
