# Mathlib study: data for the L33.3 benchmark

This file keeps the data of the 2026-11-03 proofs study (ledger item PROOFS) that step L33.3 relies on: the sixteen Mathlib theorems stated in Zed, the helper definitions, the pinned Mathlib and Lean commits, the Lean line counts, and the study's section A rejections. The study's files are in `/home/luke/Work/wt/proofs`, which is not a git repository; item MATHLIB-seed copies these pieces here so that they are kept. Every piece below is copied verbatim from the file named in its header, except the sections "`minFac` and its laws" and "Divisibility laws, `.all` introduction and the `euclid` chain", and the `using` list of theorem 11, which item MATHLIB-euclid-gaps extended (the study wrote `using(anyIntro, minFacPrime, minFacDvd, dvdFact)`). In the copied text, `D:n` means line n of the zed spec's DESIGN.md at commit 8456c46 (`REPORT.md` line 4), and "section 5" means the section "Helper definitions and other code" below.

`minFac` and the laws `minFacPrime`, `minFacDvd` and `dvdFact`, cited by the `euclid` proof (theorem 11), are written in the section "`minFac` and its laws" below (item MATHLIB-minfac, 2026-11-07). That section is new text, not a copy from the study. The divisibility laws they rest on (`dvdRefl`, `dvdTrans`, `dvdMulRight`, `dvdMulLeftOfDvd`, `notDvdSucc`), an introduction rule for `.all` (`allIntro`) and the proof of theorem 11 written out as a `#chain` (`euclidChain`) are in the section "Divisibility laws, `.all` introduction and the `euclid` chain" (item MATHLIB-euclid-gaps, 2026-11-07), also new text. zed-impl can only parse these sections today: a test lexes and parses every `zed` fence of this file (`l01_07_fences::mathlib`). Running `minFac`'s test table needs recursion (step L6.7) and, with its parameter types, layer L10, and checking its laws needs laws and proofs (layer L15, step L22.5 and step L33.3).

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
law euclid(n: int[0..]) = (n..=fact(n) + 1).any(p -> isPrime(p)) proof { using(anyIntro, minFacPrime, minFacDvd, minFacLe, dvdRefl, dvdFact, notDvdSucc) }
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
law minFacMin(n: int[2..], d: int[2..<minFac(n)]) = minFac(n) mod d != 0 proof {
  #cases(on: dvd(d, minFac(n)), arms: b -> match b {
    true -> #chain(steps: [
      #use(rule: minFacDvd, args: [n]),
      #use(rule: dvdTrans, args: [d, minFac(n), n]),
      #use(rule: minFacLe, args: [n, d]),
      #domain,
    ], claims: [
      dvd(minFac(n), n),
      dvd(d, n),
      minFac(n) <= d,
      minFac(n) mod d != 0,
    ]),
    false -> #domain,
  })
}
law minFacPrime(n: int[2..]) = isPrime(minFac(n)) proof {
  #chain(steps: [
    #use(rule: allIntro, args: [(2..<minFac(n)), (d -> minFac(n) mod d != 0)]),
    #domain,
  ], claims: [
    (2..<minFac(n)).all(d -> minFac(n) mod d != 0),
    isPrime(minFac(n)),
  ])
}
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
- `minFacPrime` is `Nat.minFac_prime` (`Defs`:286-288), 1 statement line and 2 proof lines in lean_counts.txt. Mathlib's proof: `prime_def_lt'` with `minFac_has_prop` and `Nat.dvd_trans`. In Zed: `isPrime(p)` unfolds to `p >= 2 && (2..<p).all(d -> p mod d != 0)`; the first conjunct is the result type; for the second, a d in `2..<p` with `p mod d == 0` divides n by `dvdTrans`, so `minFacLe` gives `p <= d`, against `d < p`. That argument is about one d at a time, and it is the law `minFacMin`; the proof of `minFacPrime` turns it into the `.all` by `allIntro` (next section), then closes `isPrime(minFac(n))` at rung 2 from the result type and the `.all` it has as a claim [I]. MATHLIB-minfac wrote this proof as `using(minFacDvd, minFacLe, dvdTrans)`. That cannot work: `using` chains forward from hypotheses (D:1122), and nothing it can add has the form `(2..<p).all(…)`. The written proof is 8 lines against Lean's 2, because Lean's `prime_def_lt'` already states primality as a property of each smaller number, which `isPrime`'s `.all` does not.
- `minFacMin` has no Mathlib counterpart of its own: it is the step inside `Nat.minFac_prime`'s proof (`Defs`:286-288) that applies `minFac_le_of_dvd` to a divisor of `minFac n` through `Nat.dvd_trans`. Its binder `d: int[2..<minFac(n)]` has a range bound by the earlier binder, as in step L22.5's test `law impossible(n: int[0..], k: int[0..<n]) = false` (D:2638). The proof splits on `dvd(d, minFac(n))` with `#cases` on a `bool` expression (D:1122), written as step L15.5's test writes it (D:2508). In the arm `true` the chain reaches `minFac(n) <= d`, which with the binder's `d < minFac(n)` leaves no case, so `#domain` closes the goal. In the arm `false`, `dvd(d, minFac(n))` unfolds at `d >= 2` to `minFac(n) mod d == 0`, whose negation is the goal.
- `dvdFact` is `Nat.dvd_factorial`, used at `Infinite`:42 (`dvd_factorial (minFac_pos _) h`, so its premises are `0 < m` and `m ≤ n`, hence `m: int[1..]`). It is defined in `Mathlib/Data/Nat/Factorial/Basic.lean` (imported at `Infinite`:11), which MATHLIB-minfac did not read because the study does not cite it. MATHLIB-euclid-gaps read it at the pinned commit: `Nat.dvd_factorial` is at lines 82-83, proved by `Nat.dvd_mul_right` and `factorial_dvd_factorial` (lines 77-80, an induction on `m ≤ n` whose step is `Nat.dvd_trans` with `Nat.dvd_mul_left`). lean_counts.txt has no row for it.
- **`dvdFact`'s proof is `byInduction(n)`, not `using`.** `using` only instantiates cited laws at subterms of the goal and hypotheses (D:1122), so it cannot supply the claim at `n - 1`. The step unfolds `fact(n)` to `n * fact(n - 1)`: at `m == n` it needs `dvd(n, n * x)`, and at `m <= n - 1` the claim at `n - 1` and `dvd(m, x).implies(dvd(m, n * x))`. With `dvd` defined through `mod`, both are nonlinear, so the induction step needs these two divisibility laws [I]. They are `dvdMulRight` at `(n, fact(n - 1))` and `dvdMulLeftOfDvd` at `(m, fact(n - 1), n)`, written in the next section, the same two laws Mathlib's proof uses. Whether `byInduction(n)` finds them in its step without a citation is [I]: rung 3 uses every proved law in scope (D:1096), but `dvdMulLeftOfDvd` is an implication, which a rewrite does not apply. If it does not, the step is written as a `#chain` with a `#use` of each.

**Still missing.** The gaps that MATHLIB-minfac listed here (`dvdTrans`, the two laws of `dvdFact`'s step, an introduction rule for `.all`, and the two laws theorem 11's `using` list lacked) are written in the next section. What remains is that their proofs, and those of `dvdFact`, `minFacAuxDvd` and `minFacAuxLe`, are only claimed [I], as the next section states law by law.

**What checks this.** zed-impl parses every `zed` fence of this file at the top ring (test `l01_07_fences::mathlib`), so the code above is checked for syntax only. Nothing runs or checks its meaning yet. `zedc test` refuses the unit for three reasons: parameter types are built from layer L10, recursion arrives at layer L6 (steps L6.4 and L6.7), and `law` is built from layer L15. Measured on 2026-11-07 with the types removed, `minFac`'s table still did not run, because of the recursion. The first step that can run `minFac`'s test table with the types removed is L6.7; with them it also needs layer L10. The laws are checked from L15.2 (laws enter the obligation record), with `using` at L15.7, `byInduction` on `int[lo..]` at L22.5, `@measure` at L17.1, and the theorems at proof grade at L33.3, whose test proves `isPrime` equal to a `minFac`-based test.

## Divisibility laws, `.all` introduction and the `euclid` chain

Written for item MATHLIB-euclid-gaps on 2026-11-07; this section is not copied from the study. The Lean sources were read at the two pinned commits from GitHub, as in the previous section: `Dvd` is Lean 4 core's `src/Init/Data/Nat/Dvd.lean`, and `Defs` and `Infinite` are the two Mathlib files of the previous section. `D:n` means line n of DESIGN.md at zed spec commit d3c2da0, as in the previous section.

```zed
law dvdRefl(a: int[0..]) = dvd(a, a);
law dvdTrans(a: int[0..], b: int[0..], c: int[0..]) = (dvd(a, b) && dvd(b, c)).implies(dvd(a, c));
law dvdMulRight(a: int[0..], b: int[0..]) = dvd(a, a * b);
law dvdMulLeftOfDvd(a: int[0..], b: int[0..], c: int[0..]) = dvd(a, b).implies(dvd(a, c * b));
law notDvdSucc(d: int[2..], x: int[0..]) = dvd(d, x).implies(!dvd(d, x + 1));

law allIntro(m: K -> V, p: (V) -> bool where m.map(p) == m.map(v -> true)) = m.all(p) proof { byCollectionInduction(m) }

law euclidChain(n: int[0..]) = (n..=fact(n) + 1).any(p -> isPrime(p)) proof {
  #chain(steps: [
    #use(rule: minFacPrime, args: [fact(n) + 1]),
    #use(rule: minFacDvd, args: [fact(n) + 1]),
    #use(rule: dvdRefl, args: [fact(n) + 1]),
    #use(rule: minFacLe, args: [fact(n) + 1, fact(n) + 1]),
    #cases(on: minFac(fact(n) + 1) <= n, arms: b -> match b {
      true -> #chain(steps: [
        #use(rule: dvdFact, args: [minFac(fact(n) + 1), n]),
        #use(rule: notDvdSucc, args: [minFac(fact(n) + 1), fact(n)]),
        #domain,
      ], claims: [
        dvd(minFac(fact(n) + 1), fact(n)),
        !dvd(minFac(fact(n) + 1), fact(n) + 1),
        n <= minFac(fact(n) + 1),
      ]),
      false -> #domain,
    }),
    #domain,
    #use(rule: anyIntro, args: [minFac(fact(n) + 1), (n..=fact(n) + 1), (p -> isPrime(p))]),
  ], claims: [
    isPrime(minFac(fact(n) + 1)),
    dvd(minFac(fact(n) + 1), fact(n) + 1),
    dvd(fact(n) + 1, fact(n) + 1),
    minFac(fact(n) + 1) <= fact(n) + 1,
    n <= minFac(fact(n) + 1),
    minFac(fact(n) + 1) in (n..=fact(n) + 1)::domain,
    (n..=fact(n) + 1).any(p -> isPrime(p)),
  ])
}
```

**The divisibility laws.** Each states a Lean core law over `int[0..]`, with `dvd` as section 5 defines it (`d == 0` divides only 0; otherwise `n mod d == 0`). None has a `proof` clause. With `dvd` defined through `mod`, rung 2 writes `x mod a` as a remainder `r` with `x == a * q + r`, where `a * q` is a product atom (D:1093), and from such atoms it does not derive `r == 0` in any of these laws, so each needs a written proof [I]. They are in the same state as `gcdDvd`, `dvdGcd` and `dvdAntisymm`, which theorems 9 and 10 cite and nobody has written.
- `dvdRefl` is `Nat.dvd_refl` (`Dvd`:19). `euclidChain` uses it at `fact(n) + 1`: it is the premise of `minFacLe` at `m = n = fact(n) + 1`, which gives the witness's upper end `minFac(fact(n) + 1) <= fact(n) + 1`.
- `dvdTrans` is `Nat.dvd_trans` (`Dvd`:26-29). `minFacMin` uses it at `(d, minFac(n), n)`, so `minFacPrime`, and through it `euclidChain`, rest on it.
- `dvdMulRight` is `Nat.dvd_mul_right` (`Dvd`:24), and `dvdMulLeftOfDvd` is `Nat.dvd_mul_left_of_dvd` (`Dvd`:31-32), with Lean's order of the factors in `c * b`. They are the two laws of `dvdFact`'s induction step (previous section), and Mathlib's proof of `Nat.dvd_factorial` uses the same two. `euclidChain` uses them only through `dvdFact`.
- `notDvdSucc` replaces Mathlib's two steps at `Infinite`:43-44: `Nat.dvd_add_iff_right` (`Dvd`:52-53) gives `p ∣ 1` from `p ∣ n !` and `p ∣ n ! + 1`, and `Nat.Prime.not_dvd_one` (`Defs`:191-192) refutes it. A d that divides both x and `x + 1` divides 1, so `d <= 1`; the law needs only `d >= 2`, not that d is prime. It is an implication, not the conjunction `!(dvd(d, x) && dvd(d, x + 1))` that MATHLIB-minfac proposed, so that a `#use` and `using` can apply it forward from the hypothesis `dvd(d, x)`. `euclidChain` uses it at `(minFac(fact(n) + 1), fact(n))` in the case `minFac(fact(n) + 1) <= n`.

**`allIntro`, an introduction rule for `.all`.** The prelude states `anyIntro`, `anyElim` and `allElim` (D:1122), each an implication whose premise a proof supplies as a hypothesis. An introduction rule for `.all` needs its premise at every key of `m`, and no constructor of `Proof` introduces a new binder for a key (D:1110-1119). The ladder does: rung 5 turns an equation between two collections into `f::domain == g::domain` and `f[k] == g[k]` at a new binder `k` in `f::domain` (D:1098). So `allIntro` puts its premise in the `where` clause of its binder `p`, as the collection equation `m.map(p) == m.map(v -> true)`: a `#use` adds, for each argument, the obligation that it lies in its binder's domain, `where` clause included (D:1352), and the ladder, not the proof, discharges that obligation. Rung 5 splits it into `p(m[k]) == true` at a new binder `k` in `m::domain`; the two domains are equal because `.map` keeps the keys [I].
- **In `minFacPrime`**, `m` is the range `2..<minFac(n)`, a self-map whose values are its keys (D:3062), so each half of the split is `minFac(n) mod k != 0` with `k` in `2..<minFac(n)`, which is `minFacMin` at `(n, k)`. Rung 3 uses every proved law in scope (D:1096); that it uses a law whose statement is a `bool` expression, not an equation, as a rewrite to `true`, with the binder's range read from the hypotheses, is [I], since D:1096 does not say how such a law is used.
- **Its own proof** is by `byCollectionInduction(m)` (D:1122): at the empty collection `.all` is `true` (D:2123), and adding one entry adds one conjunct to `m.all(p)` and one key to each side of the premise [I].
- **It is not in the prelude.** D:1122 states only the three laws above, and step L15.7 builds them. Adding `allIntro` to the prelude is a spec change, which this item does not make; until then it is a library law that L33.3 writes.
- `m: K -> V` takes a range because a range is a map (D:3062) [I: that a range value fills a binder of a map type].

**`euclidChain`, the proof of theorem 11 written out.** It proves `euclid`'s statement by the kernel's rules alone, as `gcdCommChain` does for theorem 9. With N = `fact(n) + 1` and p = `minFac(N)`:
1. `minFacPrime` and `minFacDvd` at N give `isPrime(p)` and `dvd(p, N)`. N fills `n: int[2..]` because `fact`'s result type is `int[1..]`, an obligation rung 2 discharges.
2. `dvdRefl` and `minFacLe` at `(N, N)` give `p <= N`, the upper end.
3. `#cases` on `p <= n` gives the lower end. In the arm `true`, `dvdFact` at `(p, n)` gives `dvd(p, fact(n))` (p fills `m: int[1..]` because `minFac`'s result type is `int[2..]`), `notDvdSucc` at `(p, fact(n))` gives `!dvd(p, fact(n) + 1)`, against step 1's `dvd(p, N)`, and `#domain` closes the goal with no case left. In the arm `false`, `n < p` gives `n <= p`. This is Mathlib's `le_of_not_ge` at `Infinite`:41.
4. `#domain` turns `n <= p` and `p <= N` into `p in (n..=N)::domain`, a range's domain being the range itself (D:3062) [I: that rung 2 reads that membership as the two bounds].
5. `anyIntro` at `(p, n..=N, (p -> isPrime(p)))` gives the goal. Its premise `k in m::domain && p(m[k])` is the conjunction of the claims of steps 4 and 1 once `m[k]` on a range is `k` and the function is applied [I: that canonical equality, D:1352, includes both]. D:1122 gives `anyIntro`'s statement but not its binders, so the chain assumes the binder order in which the statement first names them: `k`, `m`, `p`.
- The proof takes 29 lines after the statement line; Lean's takes 9 (lean_counts.txt).

**Theorem 11's one-line proof.** The `using` list of theorem 11 now names every law `euclidChain` cites. `using` as D:1122 defines it still does not find the proof, for two reasons. (1) It instantiates the cited laws' binders only with subterms of the goal and of the hypotheses it starts with. The witness `minFac(fact(n) + 1)` is neither, so `anyIntro`, `dvdFact` and `notDvdSucc` are never instantiated at it. (2) The lower end needs the case split of step 3, and forward chaining makes no case split. So L33.3 proves theorem 11 by `euclidChain`, or changes `using`. Two changes would do. For (1), `using` could take written terms, for example `using(anyIntro, …, at: [minFac(fact(n) + 1)])`, added to the subterms it instantiates with; the set stays fixed and finite, so the termination argument of D:1122 still holds. For (2), the laws could be stated in the direction forward chaining needs: `notDvdSucc` as `dvd(d, x + 1).implies(!dvd(d, x))` and the contrapositive of `dvdFact`, `(!dvd(m, fact(n))).implies(n < m)`, give `n < p` from `dvd(p, N)` with no case split. Both are spec or library decisions for L15.7 and L33.3, not made here.

**What checks this.** As for the previous section: test `l01_07_fences::mathlib` parses every fence of this file, and it also checks that each law cited by a `#use` or `using` in `euclid`, `euclidChain`, `minFacPrime` and `minFacMin` is a prelude law or is written in a fence of this file. Nothing checks the laws' meaning before layer L15.

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
