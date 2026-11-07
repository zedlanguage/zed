# Mathlib study: data for the L33.3 benchmark

This file keeps the data of the 2026-11-03 proofs study (ledger item PROOFS) that step L33.3 relies on: the sixteen Mathlib theorems stated in Zed, the helper definitions, the pinned Mathlib and Lean commits, the Lean line counts, and the study's section A rejections. The study's files are in `/home/luke/Work/wt/proofs`, which is not a git repository; item MATHLIB-seed copies these pieces here so that they are kept. Every piece below is copied verbatim from the file named in its header, except the section "`minFac` and its laws". In the copied text, `D:n` means line n of the zed spec's DESIGN.md at commit 8456c46 (`REPORT.md` line 4), and "section 5" means the section "Helper definitions and other code" below.

`minFac` and the laws `minFacPrime`, `minFacDvd` and `dvdFact`, cited by the `euclid` proof (theorem 11), are written in the section "`minFac` and its laws" below (item MATHLIB-minfac, 2026-11-07). That section is new text, not a copy from the study. zed-impl can only parse it today: a test lexes and parses every `zed` fence of this file (`l01_07_fences::mathlib`). Running `minFac`'s test table needs recursion (step L6.7) and, with its parameter types, layer L10, and checking its laws needs laws and proofs (layer L15, step L22.5 and step L33.3).

## The two commits

Source: `/home/luke/Work/wt/proofs/REPORT.md` line 14.

- **Lean sources:** Mathlib commit 296b5b4ac142878b519837d1ba8024ef92961e92 and Lean 4 core commit 713757e804cc152db7a8019aeb59bef57e7a6706 (src/Init only). Lines were counted by /home/luke/Work/wt/proofs/scripts/count_lean.sh into /home/luke/Work/wt/proofs/lean_counts.txt. S is statement lines; P is proof lines (after `:=` or `by`, not counting blank lines or attributes). [C]

## The sixteen theorems

Source: `/home/luke/Work/wt/proofs/REPORT.md` lines 97 to 216 (section B.2). These are the parse-fixed forms: the first drafts are in `/home/luke/Work/wt/proofs/snippets.zed.md`, and REPORT.md section 5 (copied in the next section) states what was fixed.

- Lean S/P counts are from lean_counts.txt [C].
- The Zed statements all parse [C].
- Every claim about which rung proves a law is [I]; the L22.10 tests would confirm them once the rungs exist.
- The helper definitions (`choose`, `fact`, `gcd`, `dvd`, `isPrime`, `rev`, `Group`) are in section 5 and parse [C].

**1. Binomial theorem** (`Commute.add_pow` 2/29, `add_pow` 2/1)
- Proof: `byInduction(n)`. The step peels the last term off the range sum, applies Pascal's rule for `choose`, and leaves the rest to the `CommRing` normalizer at rung 3.
- Missing: a prelude law for splitting a `><` over a range at its end (whether the Boom obligations already give this is [I]), and Pascal's law for `choose`.
```zed
law binomial(R: CommRing(T), x: T, y: T, n: int[0..]) = pow(M: R, x: x + y, n:) == (0..=n).map(m -> pow(M: R, x:, n: m) * pow(M: R, x: y, n: n - m) * ofNat(R, choose(n, m))) >< R.add proof { byInduction(n) }
```

**2. Sum of a row of binomial coefficients** (`Nat.sum_range_choose` 1/2)
- Proof: cite #1 at x = y = 1, then rung 3. Nothing missing.
```zed
law rowSum(n: int[0..]) = (0..=n).map(m -> choose(n, m)).sum == 2 ** n proof { #use(rule: binomial, args: [intRing, 1, 1, n]) }
```

**3. Gauss sum** (`Finset.sum_range_id_mul_two` 1/7)
- Proof: `byInduction(n)`. Nothing missing.
- 5 of Lean's 7 lines handle truncated subtraction (`add_tsub_cancel_of_le`, `Nat.le_sub_one_of_lt`). In Zed, `int[0..]` is a range of `int`, not a separate type with its own `-`, so these lemmas do not arise.
```zed
law gauss(n: int[0..]) = (0..<n).sum * 2 == n * (n - 1) proof { byInduction(n) }
```

**4. `sub_sq`, `add_sq`** (1/1 each)
- Proof: none; the `CommRing` normalizer at rung 3 (D:1194).
- Binary `-` is rejected at `CommRing` by design (D:1156, L22.3 test), so the statement uses `+ -`. The fix belongs in the library, not the operator rule: a `Ring` theory with a `sub` field and `law subDef(a, b) = sub(a, b) == add(a, neg(b))`.
```zed
law subSq(R: CommRing(T), a: T, b: T) = (a + -b) * (a + -b) == a * a + -(2 * a * b) + b * b;
```

**5. `mul_inv_rev`** (1/1, plus 1/2 in `Group`)
- Proof: none if a `Group` normalizer exists (free word reduction, registered with `@decides`). Without it, the 3-link chain in section 5.
- Missing: the `Group` normalizer.
```zed
law mulInvRev(G: Group(T), a: T, b: T) = G.inv(a * b) == G.inv(b) * G.inv(a);
```

**6. `max_le_iff`** (1/1)
- Proof: none, if rung 5 splits `if` and rung 2 then decides each case. Today D:992 names only union-typed binders and `match`.
- Missing: rung 5 splitting `if`, which is a `match` on `bool`.
```zed
law maxLe(a: int, b: int, c: int) = (max(a, b) <= c) == (a <= c && b <= c);
```

**7. `sq_nonneg`** (2/9)
- Rungs 1–3 cannot prove it: interval arithmetic on `a * a` gives no sign, and nonlinear predicates are kept as written (D:603). Splitting on `a >= 0` gives two arms, each a product of two factors with the same sign, which rung 2 handles.
- Missing: `#cases` on a bool expression. Today `#cases` takes only a binder (D:1007).
```zed
law sqNonneg(a: int) = a * a >= 0 proof { byCases(a >= 0) }
```

**8. Triangle inequality** (`abs_add_le`, generated by `to_additive` from `mabs_mul_le`, 1/4)
- Proof: none, if rung 5 splits the `if` inside each `abs` and rung 2 decides the cases. Same caveat as #6.
- One law covers it; no multiplicative copy is needed.
```zed
law absAdd(a: int, b: int) = abs(a + b) <= abs(a) + abs(b);
```

**9. `Nat.gcd_comm`** (1/3)
- Proof today: the 5-step `#chain` in section 5. With the proposed tactic: one line.
- Missing: the `using` tactic, or at least filling in `#chain` claims automatically.
```zed
law gcdComm(a: int[0..], b: int[0..]) = gcd(a, b) == gcd(b, a) proof { using(dvdAntisymm, dvdGcd, gcdDvd) }
```

**10. `Coprime.dvd_of_dvd_mul_left/right`** (1/1, 1/2)
- Proof: `using` over `gcdMulLeft`, `gcdDvd`, `dvdGcd`.
```zed
law coprimeDvd(k: int[0..], m: int[0..], n: int[0..]) = (gcd(k, m) == 1 && dvd(k, m * n)).implies(dvd(k, n)) proof { using(gcdMulLeft, gcdDvd, dvdGcd) }
```

**11. Infinitely many primes** (`Nat.exists_infinite_primes` 1/9, with `minFac_prime` 1/2)
- Stated with a bounded `any`, because D:1032 allows no existential over an infinite domain. The bound `n! + 1` is the witness's own bound, so this is the same theorem.
- Witness: `minFac(fact(n) + 1)`.
- Missing: the prelude laws `anyIntro`/`anyElim`, and `using`.
```zed
law euclid(n: int[0..]) = (n..=fact(n) + 1).any(p -> isPrime(p)) proof { using(anyIntro, minFacPrime, minFacDvd, dvdFact) }
```

**12. `Nat.Prime.two_le`** (1/3)
- Proof: none. `isPrime` unfolds to `p >= 2 && …`, and rung 2 takes the first conjunct.
```zed
law primeTwoLe(p: int[0..]) = isPrime(p).implies(p >= 2);
```

**13. Size of the powerset** (`Finset.card_powerset`, `Multiset.card_powerset`, 1/1 each)
- Proof: induction on the set.
- Missing: induction over a collection. `#induction` schemes cover only `int[lo..]` and recursive unions (D:991, D:2262).
```zed
law cardPowerset(s: Set(T)) = s.powerset.count == 2 ** s.count proof { byCollectionInduction(s) }
```

**14. `List.reverse_reverse` (1/1 plus a 1/3 helper) and `List.length_append` (1/3)**
- `lenAppend`: none; lengths are linear integer terms, decided at rung 2.
- `revRev`: needs equality of two morphisms (functions from keys to values) turned into equality at each key; then rung 2 decides the index arithmetic.
- Missing: that per-key equality step. D:986–998 do not state it.
```zed
law revRev(xs: [T]) = rev(rev(xs)) == xs;
law lenAppend(xs: [T], ys: [T]) = (xs ++ ys).len == xs.len + ys.len;
```

**15. Geometric sum** (`geom_sum_mul` 1/3, `geom_sum_eq` 1/2)
- Proof: `byInduction(n)`, with the normalizer in the step.
- The field version needs a `Field` theory whose `inv` is defined only for nonzero values.
```zed
law geomSum(R: CommRing(T), x: T, n: int[0..]) = ((0..<n).map(i -> pow(M: R, x:, n: i)) >< R.add) * (x + -1) == pow(M: R, x:, n:) + -1 proof { byInduction(n) }
```

**16. Squeeze theorem; 1/n → 0** (`tendsto_of_tendsto_of_tendsto_of_le_of_le` 3/2; `tendsto_one_div_atTop_nhds_zero_nat` 3/1)
- Stated only in modulus form: the inner "there exists N" becomes a function field of a model (D:1206).
- `squeeze` is a theory morphism whose modulus is the `max` of the two given moduli.
- 1/n → 0 is a `Limit` model with modulus `ceil(1/e) + 1`, proved through `oneOverN` [I].
- This is a different statement from Lean's (which uses filters and topology) and covers only sequences over `rat`.
- The code is in section 5.

Totals [I]: if the rungs work as specified, 7 rows need no proof text (#4, #5 with a Group normalizer, #6, #8, #12, and both laws of #14). 8 rows need one line. Analysis is in reach only with explicit moduli. Lean needs at least one proof line for every row.

## Helper definitions and other code

Source: `/home/luke/Work/wt/proofs/REPORT.md` lines 361 to 433 (section 5, "Zed snippets as checked"). The code block holds the helper definitions (`Group`, `choose`, `fact`, `gcd`, `dvd`, `isPrime`, `rev`), the code of theorem 16 (`Limit`, `Squeeze`, `squeeze`, `oneOverN`) and the chain proofs of theorems 9 and 5 (`gcdCommChain`, `mulInvRevChain`).

All fences parse [C]: `RESULT: OK` for each fence, and `parsed 152 failed 0` for the whole copy. The first attempt failed in three places, and each shows something about the grammar:
- **`(…) >< R.add * (x - 1)` fails.** The right operand of `><` is a postfix expression (`ReduceTail`, D:3269), so a `*` after it is a parse error. The reduction has to be in parentheses.
- **A lambda inside a record display fails.** Display entries are `Name ':' Expr12` (D:3339), and a lambda is not an `Expr12`, so `modulus: (e -> …)` needs parentheses.
  - This also breaks the prose example at D:1239, `{ f: x -> 2 * x + 1 }`. As code, `m = { f: x -> 2 * x + 1 };` fails with `FAIL near '*'` [C].
  - Because it is prose, no test catches it.
  - Fix: write `{ f: (x -> 2 * x + 1) }` there, or let display entries take a lambda.
- **`law sameLim() = …` fails.** A law needs at least one parameter.

Statements with binary `-` at a `CommRing` binder parse, but the operator rule (D:1156) would reject them. The versions above use `+ -` instead.

```zed
interface Group(T) {
  import Monoid(T),
  inv: (T) -> T,
  law mulInv(a: T) = mul(a, inv(a)) == one,
  law invMul(a: T) = mul(inv(a), a) == one,
}

choose(positional n: int[0..], positional k: int[0..]) -> int[0..] =
  if k == 0 { 1 } else if n == 0 { 0 } else { choose(n - 1, k - 1) + choose(n - 1, k) };
fact(positional n: int[0..]) -> int[1..] = if n == 0 { 1 } else { n * fact(n - 1) };
gcd(positional a: int[0..], positional b: int[0..]) -> int[0..] = if b == 0 { a } else { gcd(b, a mod b) };
dvd(positional d: int[0..], positional n: int[0..]) = if d == 0 { n == 0 } else { n mod d == 0 };
isPrime(positional p: int[0..]) = p >= 2 && (2..<p).all(d -> p mod d != 0);
rev(positional xs: [T]) = (0..<xs.len).map(i -> xs[xs.len - 1 - i]);

interface Limit {
  seq: (int[0..]) -> rat,
  lim: rat,
  modulus: (rat) -> int[0..],
  law conv(e: rat where e > 0, n: int[0..]) = (n >= modulus(e)).implies(abs(seq(n) - lim) < e),
}

interface Squeeze {
  low: Limit,
  high: Limit,
  f: (int[0..]) -> rat,
  law between(n: int[0..]) = low.lim == high.lim && low.seq(n) <= f(n) && f(n) <= high.seq(n),
}

squeeze(S: Squeeze) -> Limit = { seq: S.f, lim: S.low.lim, modulus: (e -> max(S.low.modulus(e), S.high.modulus(e))) };

law oneOverN(e: rat where e > 0, n: int[1..]) = (n * e > 1).implies(1 / n < e);

law gcdCommChain(a: int[0..], b: int[0..]) = gcd(a, b) == gcd(b, a) proof {
  #chain(steps: [
    #use(rule: gcdDvd, args: [a, b]),
    #use(rule: gcdDvd, args: [b, a]),
    #use(rule: dvdGcd, args: [b, a, gcd(a, b)]),
    #use(rule: dvdGcd, args: [a, b, gcd(b, a)]),
    #use(rule: dvdAntisymm, args: [gcd(a, b), gcd(b, a)]),
  ], claims: [
    dvd(gcd(a, b), a) && dvd(gcd(a, b), b),
    dvd(gcd(b, a), b) && dvd(gcd(b, a), a),
    dvd(gcd(a, b), gcd(b, a)),
    dvd(gcd(b, a), gcd(a, b)),
    gcd(a, b) == gcd(b, a),
  ])
}

law mulInvRevChain(G: Group(T), a: T, b: T) = G.inv(a * b) == G.inv(b) * G.inv(a)
proof {
  G.inv(a * b)
    == G.inv(a * b) * (a * b * (G.inv(b) * G.inv(a)))
    == G.inv(a * b) * (a * b) * (G.inv(b) * G.inv(a))
    == G.inv(b) * G.inv(a)
}
```

- `gcdCommChain` is 14 lines; `using` plus automatic claims makes it 1. Its helper laws need `byStrongInduction`.
- `isPrime` is the slow textbook test. It serves as the specification, and the library would prove it equal to a faster test.

## `minFac` and its laws

Written for item MATHLIB-minfac on 2026-11-07; this section is not copied from the study. The Mathlib source is the pinned commit 296b5b4ac142878b519837d1ba8024ef92961e92, read from GitHub (`raw.githubusercontent.com/leanprover-community/mathlib4/<commit>/<path>`), since the study's local clones are deleted (`REPORT.md` line 441). Only the two files that lean_counts.txt cites were read: `Mathlib/Data/Nat/Prime/Defs.lean` (written `Defs` below) and `Mathlib/Data/Nat/Prime/Infinite.lean` (written `Infinite`). Their line numbers agree with lean_counts.txt: `Nat.minFac_prime` at `Defs`:286-288, `Nat.Prime.two_le` at `Defs`:72-75, `Nat.exists_infinite_primes` at `Infinite`:36-45. `D:n` in this section means line n of DESIGN.md at zed spec commit d3c2da0.

```zed
@measure(n - k) minFacAux(positional n: int[2..], positional k: int[3..]) -> int[2..] =
  if n < k * k { n } else if n mod k == 0 { k } else { minFacAux(n, k + 2) };
minFac(positional n: int[2..]) -> int[2..] = if n mod 2 == 0 { 2 } else { minFacAux(n, 3) }
test { 2 -> 2, 3 -> 3, 4 -> 2, 9 -> 3, 15 -> 3, 25 -> 5, 91 -> 7, 97 -> 97, 121 -> 11, 7917 -> 3, 7919 -> 7919 }

law minFacAuxDvd(n: int[2..], k: int[3..]) = dvd(minFacAux(n, k), n);
law minFacAuxLe(n: int[2..], k: int[3..], m: int[2..]) = (k mod 2 == 1 && (2..<k).all(j -> n mod j != 0) && dvd(m, n)).implies(minFacAux(n, k) <= m);

law minFacDvd(n: int[2..]) = dvd(minFac(n), n) proof { using(minFacAuxDvd) }
law minFacLe(n: int[2..], m: int[2..]) = dvd(m, n).implies(minFac(n) <= m) proof { using(minFacAuxLe) }
law minFacPrime(n: int[2..]) = isPrime(minFac(n)) proof { using(minFacDvd, minFacLe, dvdTrans) }
law dvdFact(m: int[1..], n: int[0..]) = (m <= n).implies(dvd(m, fact(n))) proof { byInduction(n) }
```

**Definitions.** `minFacAux` and `minFac` follow `Nat.minFacAux` (`Defs`:207-215) and `Nat.minFac` (`Defs`:217-220) line for line: test 2 first, then the odd numbers from 3, and stop at n itself once `k * k` passes n. A call costs O(√n) steps.
- **Domain.** Mathlib's `minFac` is total on ℕ: `minFac 0 = 2` (`Defs`:222-224) and `minFac 1 = 1` (`Defs`:226-228). These are junk values; the docstring at `Defs`:217 calls it "the smallest prime factor of `n ≠ 1`", and its OEIS attribute (`Defs`:218) calls `n = 0` a junk value. Zed's `minFac` takes `n: int[2..]` instead, the domain restriction that sec:failure calls the fully checked special case of totality (D:515). A call at 0 or 1 is then not a value: the checker rejects a call whose argument it cannot place in `int[2..]` [I: the argument-fit rule of sec:type_resolution, not checked against an implementation, since parameter types are built from layer L10]. The result type `int[2..]` states `Nat.minFac_prime`'s `2 ≤ p` part once, in the signature.
- **Laws.** Because of the domain, `minFacPrime` needs no premise `n ≠ 1`, and Mathlib's laws at 0 (`minFac_dvd` at `n = 0`, `2 ∣ 0`) have no Zed counterpart. Every law here has binders `int[2..]`, which is the set where Mathlib's laws carry information.
- **Termination.** Mathlib uses `termination_by k => sqrt n + 2 - k` (`Defs`:214). No entry of the closed catalog of descent evidence (D:966) fits, since `k` rises, and D:1270 lets a law that demands `minFacAux` reach proof grade only with evidence, so the definition carries `@measure(n - k)` (step L17.1). It falls by 2 at each call, a linear obligation. That it stays at least 0 at the call needs `k <= n` from `!(n < k * k)` and `k >= 3`, which is nonlinear; whether interval revision settles it is [I] (a nonlinear predicate is kept as written and read by interval revision, D:660 and D:716). If it does not, the guard `n < k || n < k * k` makes the bound linear and returns the same values.

**Laws and their Mathlib sources.**
- `minFacDvd` is `Nat.minFac_dvd` (`Defs`:283-284). The even branch is `n mod 2 == 0`, which is `dvd(2, n)` unfolded; the odd branch cites `minFacAuxDvd` at `(n, 3)`.
- `minFacLe` is `Nat.minFac_le_of_dvd` (`Defs`:296-299). `minFacPrime` needs it, and `euclid` needs it at `m = n` for its witness's upper end (below). The odd branch cites `minFacAuxLe` at `(n, 3, m)`, whose premise `(2..<3).all(j -> n mod j != 0)` is the branch's `n mod 2 != 0`.
- `minFacAuxDvd` and `minFacAuxLe` together are the private `minFacAux_has_prop` (`Defs`:239-268). Its premise `k = 2 * i + 3` becomes `k mod 2 == 1`, which the step uses to skip the even `k + 1`. Its premise "every divisor m ≥ 2 of n is at least k" becomes `(2..<k).all(j -> n mod j != 0)`, in the form of `isPrime`. Both laws are proved by induction read off `minFacAux`'s recursion (rung 4, step L6.12) under the termination evidence above, so they have no `proof` clause. In the case `n < k * k` of `minFacAuxLe`, a divisor m with `m < n` would give the divisor `n div m`, also at least k, so `n >= k * k`; Mathlib proves this case through `prime_def_le_sqrt`. That step is nonlinear [I].
- `minFacPrime` is `Nat.minFac_prime` (`Defs`:286-288), 1 statement line and 2 proof lines in lean_counts.txt. Mathlib's proof: `prime_def_lt'` with `minFac_has_prop` and `Nat.dvd_trans`. In Zed: `isPrime(p)` unfolds to `p >= 2 && (2..<p).all(d -> p mod d != 0)`; the first conjunct is the result type; for the second, a d in `2..<p` with `p mod d == 0` divides n by `dvdTrans`, so `minFacLe` gives `p <= d`, against `d < p`.
- `dvdFact` is `Nat.dvd_factorial`, used at `Infinite`:41 (`dvd_factorial (minFac_pos _) h`, so its premises are `0 < m` and `m ≤ n`, hence `m: int[1..]`). It is defined in `Mathlib/Data/Nat/Factorial/Basic.lean` (imported at `Infinite`:11), which this item did not read because the study does not cite it; its line numbers and line counts are not recorded here.
- **`dvdFact`'s proof is `byInduction(n)`, not `using`.** `using` only instantiates cited laws at subterms of the goal and hypotheses (D:1122), so it cannot supply the claim at `n - 1`. The step unfolds `fact(n)` to `n * fact(n - 1)`: at `m == n` it needs `dvd(n, n * x)`, and at `m <= n - 1` the claim at `n - 1` and `dvd(m, x).implies(dvd(m, n * x))`. With `dvd` defined through `mod`, both are nonlinear, so the induction step needs these two divisibility laws [I].

**Still missing.**
- The helper laws `dvdTrans` (Lean's `Nat.dvd_trans`) and the two divisibility laws of `dvdFact`'s step are cited but not written, like `gcdDvd`, `dvdGcd` and `dvdAntisymm` in theorems 9 and 10.
- `minFacPrime` proves a `.all` over `2..<p`. The prelude states `allElim` but no introduction rule for `.all` (D:1122). Whether rung 5 or a `#cases` covers this is [I].
- Theorem 11's list `using(anyIntro, minFacPrime, minFacDvd, dvdFact)` is not enough as copied. `Infinite`:42-43 also use `Nat.dvd_add_iff_right` and `Prime.not_dvd_one`: a p ≥ 2 that divides `fact(n)` cannot divide `fact(n) + 1`. `anyIntro` also needs `p <= fact(n) + 1`, which is `minFacLe` at `m = n`. The fix is to add `minFacLe` and a law such as `law notDvdSucc(d: int[2..], x: int[0..]) = !(dvd(d, x) && dvd(d, x + 1))` to theorem 11's list. The list above is left as the study wrote it.

**What checks this.** zed-impl parses every `zed` fence of this file at the top ring (test `l01_07_fences::mathlib`), so the code above is checked for syntax only. Nothing runs or checks its meaning yet. `zedc test` refuses the unit for three reasons: parameter types are built from layer L10, recursion arrives at layer L6 (steps L6.4 and L6.7), and `law` is built from layer L15. Measured on 2026-11-07 with the types removed, `minFac`'s table still did not run, because of the recursion. The first step that can run `minFac`'s test table with the types removed is L6.7; with them it also needs layer L10. The laws are checked from L15.2 (laws enter the obligation record), with `using` at L15.7, `byInduction` on `int[lo..]` at L22.5, `@measure` at L17.1, and the theorems at proof grade at L33.3, whose test proves `isPrime` equal to a `minFac`-based test.

## Lean line counts (lean_counts.txt)

Source: `/home/luke/Work/wt/proofs/lean_counts.txt`, written by `/home/luke/Work/wt/proofs/scripts/count_lean.sh` at the two commits above. S is statement lines; P is proof lines (after `:=` or `by`, not counting blank lines or attributes) (`REPORT.md` line 14). Paths are relative to the Mathlib and Lean 4 checkouts.

```text
Commute.add_pow                          S=2  P=29  mathlib4/Mathlib/Data/Nat/Choose/Sum.lean:34-64
add_pow                                  S=2  P=1   mathlib4/Mathlib/Data/Nat/Choose/Sum.lean:76-78
Nat.sum_range_choose                     S=1  P=2   mathlib4/Mathlib/Data/Nat/Choose/Sum.lean:94-96
Finset.sum_range_id_mul_two              S=1  P=7   mathlib4/Mathlib/Algebra/BigOperators/Intervals.lean:175-182
sub_sq                                   S=1  P=1   mathlib4/Mathlib/Algebra/Ring/Commute.lean:203-204
add_sq                                   S=1  P=1   mathlib4/Mathlib/Algebra/Ring/Defs.lean:258-259
mul_inv_rev                              S=1  P=1   mathlib4/Mathlib/Algebra/Group/DivInvMonoid.lean:327-328
Group.toDivisionMonoid.mul_inv_rev       S=1  P=2   mathlib4/Mathlib/Algebra/Group/Defs.lean:95-97
max_le_iff                               S=1  P=1   mathlib4/Mathlib/Order/Defs/LinearOrder.lean:146-147
sq_nonneg                                S=2  P=9   mathlib4/Mathlib/Algebra/Order/Ring/Unbundled/Basic.lean:608-618
mabs_mul_le(abs_add_le)                  S=1  P=4   mathlib4/Mathlib/Algebra/Order/Group/Unbundled/Abs.lean:123-127
Nat.gcd_comm                             S=1  P=3   lean4/src/Init/Data/Nat/Gcd.lean:109-112
Nat.Coprime.dvd_of_dvd_mul_left          S=1  P=1   lean4/src/Init/Data/Nat/Coprime.lean:42-43
Nat.Coprime.dvd_of_dvd_mul_right         S=1  P=2   lean4/src/Init/Data/Nat/Coprime.lean:38-40
Nat.exists_infinite_primes               S=1  P=9   mathlib4/Mathlib/Data/Nat/Prime/Infinite.lean:36-45
Nat.minFac_prime                         S=1  P=2   mathlib4/Mathlib/Data/Nat/Prime/Defs.lean:286-288
Nat.Prime.two_le                         S=1  P=3   mathlib4/Mathlib/Data/Nat/Prime/Defs.lean:72-75
Finset.card_powerset                     S=1  P=1   mathlib4/Mathlib/Data/Finset/Powerset.lean:102-103
Multiset.card_powerset                   S=1  P=1   mathlib4/Mathlib/Data/Multiset/Powerset.lean:114-115
List.reverse_reverse                     S=1  P=1   lean4/src/Init/Data/List/Lemmas.lean:2484-2485
List.reverseAux_reverseAux_nil           S=1  P=3   lean4/src/Init/Data/List/Lemmas.lean:2478-2481
List.length_append                       S=1  P=3   lean4/src/Init/Data/List/Basic.lean:622-625
geom_sum_eq                              S=1  P=2   mathlib4/Mathlib/Algebra/Field/GeomSum.lean:43-45
geom_sum_mul                             S=1  P=3   mathlib4/Mathlib/Algebra/Ring/GeomSum.lean:233-236
tendsto_of_tendsto_of_tendsto_of_le_of_le S=3  P=2   mathlib4/Mathlib/Topology/Order/Basic.lean:231-235
tendsto_of_tendsto_of_tendsto_of_le_of_le' S=3  P=1   mathlib4/Mathlib/Topology/Order/Basic.lean:220-223
tendsto_one_div_atTop_nhds_zero_nat      S=3  P=1   mathlib4/Mathlib/Analysis/SpecificLimits/Basic.lean:57-60
tendsto_inv_atTop_nhds_zero_nat          S=3  P=2   mathlib4/Mathlib/Analysis/SpecificLimits/Basic.lean:45-49
```

## Section A rejections

Source: `/home/luke/Work/wt/proofs/REPORT.md` line 26 (settled by the earlier study, `/home/luke/Work/wt/osprey/REPORT.md`), lines 30 to 32 (section A introduction) and lines 66 to 69 (A6), as `wt/review-audit/pass2/result.json` line 3043 asks.

From the list of points settled by the earlier study:

  - the rejection of importing Lean proofs

As of its 2026-10-30 checkpoint, Osprey's proof work is a kernel written in Osprey that re-checks proof terms exported from Lean. Its own proof-writing surface is "exercise scale". Spec 0049 now makes `.lean` files the only proof source and deletes Osprey's two home-made proof formats ([PROOF-SOURCE-DELETED]). [C, txt/page_spec_0049-dependenttypesandproofs.txt lines 143–153 and 171–173]

So most of what Osprey has is Lean's, reached by importing Lean proofs, which Zed has rejected. What is left are a few ideas about trust, version identity and how the user sees a proof.

**A6. Proofs written as English sentences**
- Osprey: docs/proof-workbench/ (`Assume h : p ∧ q. By cases on h …`).
- Zed now: the kernel rules at D:1239.
- Proposal: reject. Osprey deleted this format itself ([PROOF-SOURCE-DELETED]), and Zed's derivation chains already read as mathematics.
