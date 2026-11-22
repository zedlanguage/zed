# One exact method for finite and periodic integer sets (SETS-study)

Plan row SETS-study, 2026-11-22, by b22-research3. It answers QUESTIONS Q11's options C and D
and the author's request (2026-11-07) for "a cleaner solution that can subsume all of this".
Sources: the round 1 cross-review in /home/luke/Work/wt/xsets (STUDY0 to STUDY2, META1, the
prototypes alg.js and meta1/*.js), DESIGN at zed 0bb4fbd, and zed-impl at 5a0513dd6.

## 1. Where each option of Q11 stands

| Option | State | Record |
|---|---|---|
| A, enumerate only sets the source lists | Done | row LIST-size |
| B, `@exact` at an overload overlap | Open, after L15.8 | row LIST-exact-overlap |
| C, residue sets | Decided by QUESTIONS A82 (2026-11-11) and written in DESIGN sec:constraints, "Residue sets" | rows MOD-pre-width, MOD-residue, MOD-residue-fragment, CONG-transfer; A83 (cost in bit operations) in TESTS-floor-sum-digits |
| D, ranges in the type's scalar part | Split in two below: D1 is a fault against DESIGN as written, D2 waits for a program that needs it | D1: row KERNEL-int-ranges (new) |

## 2. The method

STUDY2's method is the one DESIGN now states. A set of integers is kept as a description, not a
list of members:

- pieces `{x : lo <= x <= hi, x ≡ r (mod k)}`;
- guards, the facts of the enclosing arms, decided by the Presburger solver (step L1.39);
- residue sets `{x : p(x) mod m ∈ R}`, one set per prime-power factor of a literal `m` below
  2^128, never multiplied out (Chinese remainder theorem), with `R` a union of intervals;
- opaque conjuncts, read only at points.

A description is always exact. A question about it (empty, least, greatest, inside an interval)
is answered exactly or refused with the menu `@exact`, a listed set or a proof. DESIGN's τ rule
fixes the refusal: when τ, the number of prime-power factors that admit more than one class, is at
most 1, the floor sums of step L1.25 answer exactly in O(|S| log m); when τ >= 2 the question is
refused. The τ rule reads the constants of the text, not a width, so it is not a threshold.

This subsumes A and C and gives `@exact` (B) one meaning: the written request for the cost that
follows the number of points. No candidate found in rounds 1 or this study does better at every
width without such a refusal, since the questions are NP-hard (section 4).

## 3. Option D, measured against the code

What the code does (read at zed-impl 5a0513dd6):

- A written range never enters a kernel type. `x: int[0..<100]` has kernel type `int`; the range
  sits in `WrittenRange` (crates/zedc-types/src/ty.rs, `pub low: Option<Value>`,
  `pub high: Option<Value>`), in the checker's `param_ints` (crates/zedc-check/src/check/mod.rs),
  and in the interval domain of the reduced product (`Product::of_type_within`,
  crates/zedc-preimage/src/product.rs).
- The kernel's integer part is `Lits { cofinite: bool, values: TreapSet<Value> }`
  (crates/zed-kernel/src/types.rs), a list of members. product.rs copies an interval into the type
  only when the type already lists literals or the interval has one member, and says why at
  `reduce_domains_now`: "A complete solution would let the type language hold integer ranges, so
  that the interval enters the type without listing."
- Narrowing by a comparison stays in per-scope stores. `f(x: int[0..<100]) = if x < 10 { x } else
  { 0 }` gets the result hull `int[0..=99]`, since `hull_into` reads the text and both arms.

What DESIGN says: step L1.22, "The scalar part is exact: per base type a finite or cofinite set of
literals", and sec:type_language normalizes `int[0..=10] \ int[4..=6]` to "one `#scalar` whose
interval is the union `int[0..<4] | int[7..=10]`". Both describe a set of members, so they agree on
meaning; L1.22 does not say how the set is held, and a list of members cannot hold
`int[0..<2**64]` at a cost that follows the text. So:

- **D1, conformance.** DESIGN already makes integer ranges types (written parameter types, set
  arithmetic, `::shape`). The kernel must hold `int`'s literal set as a finite union of intervals,
  each held by its two ends, so that a range costs its text and set operations cost O(i log i) in
  the number i of intervals. This is a fault in the kernel's representation, not a new choice.
  Filed as KERNEL-int-ranges, a need of L1.41-join-zed-kernel-correct. DESIGN L1.22 gets one
  clause saying so (zed, this row).
- **D2, narrowing into types.** Whether a comparison's narrowing stays in the type after the arm
  (so the hull above would be `int[0..=9]`) changes printed types, which are syntax. Q11 offered it
  as a later row "when a real program needs it" and the author did not choose it. It is not filed;
  it becomes one small change once D1 holds ranges in types.

## 4. Literature (allpapers, this study)

Four papers added to zed verification/bib.md, each quoted from its text:

- Bjørner, Blass, Gurevich and Musuvathi 2008, "Modular difference logic is hard",
  arXiv:0811.0987: "The problem becomes NP complete if we restrict attention to the residues for a
  fixed modulus N." Supports refusing τ >= 2 questions instead of searching.
- Arias, Borja and Rubio 2018, "Counting integers representable as images of polynomials modulo
  n", arXiv:1812.11599: recurrences for the number of values a polynomial takes modulo p^n, and
  (text line 22) "the associated sizes \alpha(n) define a multiplicative function. Then, for
  determining \alpha(n) for all n, it suffices to determine \alpha(p^n)". Supports one set per
  prime power.
- Pitchanathan et al. 2024, "Strided difference bound matrices", arXiv:2405.11244: "SDBM
  satisfiability problem turns out to be NP-hard", with an O(n m D_lcm) algorithm. Its cost
  follows the value of the lcm of the strides, which the cost rule refuses; it is not adopted.
- Pertseva et al. 2025, "Integer reasoning modulo different constants in SMT", arXiv:2505.14998:
  "a new refutation procedure for multi-modular systems",
  sound and incomplete. Supports the refusal with a menu over a search with no bound.

Round 1 had already quoted Manders and Adleman, Stockmeyer and Meyer, Granger 1989 and 1991, BLQ,
CKS, Harvey and van der Hoeven, Bryant, Haase 2020 and Pitchanathan et al. The semantic search
(242 papers) and the keyword search found no method that decides these questions at every width
without a refusal or a cost that follows a constant's value.

## 5. STUDY2's open items

| Item | State |
|---|---|
| 2, polynomial image in an interval | Partial-period containment is coNP-hard; refused by the τ rule. MOD-residue-fragment |
| 3, is τ structural | Decided: DESIGN's τ rule (A82) |
| 4 and 10, symbolic modulus | DESIGN's "Residue sets" takes `m` as a positive literal, so a test with a term `m` is not narrowed by that rule (read from the text; no test checks it yet). Not filed: no program in the tests needs more |
| 5, description size, min and max | Not proved. MOD-pre-width's scaling test at n and 8n measures the size of the description it keeps; a growth there is a fault under that row |
| 6, operator table | CONG-transfer (`+ - *` and `^` by a constant) and MOD-pre-width (`mod c`) |
| 7, prior art | Section 4 |
| 8, against zed-impl | MOD-pre-width, MOD-residue; KERNEL-int-ranges for the type |
| 9, bit cost | A83: bit operations; TESTS-floor-sum-digits |

## 6. Candidates

| Candidate | Result | Score | Reason |
|---|---|---|---|
| Descriptions with the τ rule (DESIGN now) plus D1's interval-union literal sets | DESIGN text and code read; round 1 prototypes pass their tests | 9 | Exact at every width; one refusal rule read off the constants; D1 removes the one place a range is lost |
| The same without D1 | code read | 7 | Written ranges stay in three side stores; a type cannot hold `int[0..<2**64]` |
| D2 as well | not built | 6 | Better hulls, but changes printed types with no program asking for it |
| Strided difference bound matrices | quoted | 3 | Cost follows the lcm's value |
| Automata over binary digits, BDDs, SMT | round 1 | 2 to 3 | Cost follows a value, or no bound |

## 7. Rows this study adds

- KERNEL-int-ranges, a need of L1.41-join-zed-kernel-correct.
- XSETS-unified-tests (already filed) now needs only this row; round 1's scripts are ported there.
