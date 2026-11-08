# LADDER-study: rung tests and ladder boundaries

Study by agent LADDER-study, 2026-11-07, at commit fbc34544 (rebased on a0c81bb8). Committed by the orchestrator, because the agent could not write report files. Tests: `tests/steps/l01_38_presburger/ladder.rs`.

Key to plan IDs:

| Plan ID | What it covers |
|---|---|
| L3.8 | obligation record, grades, rungs 1, 2, 5 and 7 |
| L3.9 | rung 3, the e-graph |
| L3.20 | rung 6, bounded model checking |
| L6.12 | rung 4, induction, and termination evidence |
| L6.12a | rung 2 at recursive calls |
| L6.12b | rung 2 at a decided match arm |
| FOLD-unique | equality with a fold by its universal property |
| ARM-split | rung 5 for an undecided arm |
| MOD-residue | the falling-factorial test |
| POLY-nf | the polynomial normal form |
| L15.5 | rung 8, zed-cert |
| L16.1 | `@assume` |
| LAW-shape | the index instance over a type variable |

## Summary

- **Only rung 2 exists in code.** It is the Presburger `entails` over the `relations` translation, and no ladder driver calls it. Rungs 1 and 3 to 9 do not exist. The grades exist only as the enum `zed_kernel::Grade` (names, printing, serialization); no code produces a grade.
- **14 new tests** cover rung 2 at its boundaries with rungs 1, 3, 5, 6 and 7, a refutation ending the ladder, determinism under reordering and renaming, and scaling at n and 8n.
- **One code fix.** `presburger::products` took the hull of each factor over the whole premise set, O(factors × premises); the new scaling test failed at 63.3 times the bytes for 8 times the size. Premise rows are now split into parts that share no atom (union-find), and each factor takes the hull over its own part. The test passes at 8.7 times the instructions and 8.0 times the bytes.
- **D9, a soundness defect.** Rung 2 can prove false facts, and give wrong refutations, at a divisor that may be zero. Follow-up RUNG2-definedness, with two failing tests (section E).
- **Both known spec defects are confirmed.** Defect (i) is stronger than stated: `@assume` can never license anything (D1).

## A. Per rung

| Rung | Code | Tests that exist | Missing tests, and what they wait for |
|---|---|---|---|
| 1 Evaluation | None. Partial pieces: the interpreter, `zedc-stage`, `Type::finite` (C22). `Grade::CheckedExhaustive` is only a name (`zed-kernel/src/term.rs:306`, `print.rs:195`, `zedc-zir/src/canon/serial.rs:296`). | `l01_15_kernel_terms::evidence` checks the proof-grade split only | Enumeration, witness, grade, mixed binders. Waits for L3.8 and LAW-shape. |
| 2 Domain reasoning | `zedc-presburger/src/presburger.rs`: `entails` :7594, `entails_inner` :7609, `products` :7657, `hull` :7300. `zedc-preimage/src/preimage.rs`: `relations` :957, `div_mod_by_term` :1689, `Tx::enter` :3630. Production callers: `product.rs` `relation_of` :2163 (filters to int names), `front.rs` `linear_questions` :190 (reports refusals only). | `l01_38_presburger`: `entailment`, `mod_symbol`, `omega`, `random`, `controls`, `ladder` | Full normal form (POLY-nf), MOD-residue, L6.12a and b, the termination premise (L6.12), the carrier (D6), definedness (D9) |
| 3 E-graph | None (`crates/zedc/src/egraph/` does not exist) | none | L3.9 |
| 4 Induction | None | none | L6.12, FOLD-unique |
| 5 Case split | None. Rung 2 settles the disjunctions of `min`, `max`, `abs` and `if` itself, which is not the rung-5 algorithm. | the rung-2 halves in `ladder` | Joins, parts, stop rule, merging equal halves: L3.8, ARM-split |
| 6 Bounded | None (grade name only) | none | L3.20 |
| 7 Property tests | None | none | L3.8 |
| 8 Certificate | `zed-cert/src/lib.rs` is a 5-line stub | none | L15.5 |
| 9 `@assume` | None (`Assume` in `zedc-check/src/check/arms.rs` is an unrelated narrowing node) | none | L16.1 |

## B. Corner cases

Classes: P = only just proves; F = only just fails and passes on; R = must refute; U = a wrong verdict would be unsound; D = determinism. Rung-2 cases written `p ⊢ g` call rung 2 on premise `p` and goal `g`.

**Rung 1 | rung 2.**

| ID | Class | Program | Expected | Status |
|---|---|---|---|---|
| B12-1 | P, F | `law andComm(a: bool, b: bool) = (a && b) == (b && a);` | CheckedExhaustive at rung 1; rung 2 takes nothing | Rung-2 side tested; rung 1 waits L3.8 |
| B12-2 | R | `law orAbsorb(a: bool, b: bool) = (a \|\| b) == a;` | Refuted at rung 1, witness a = false, b = true | L3.8 |
| B12-3 | P, D | `law sq(k: 0 \| 1 \| 2) = k * k <= 2 * k;` | CheckedExhaustive at rung 1; rung 2 also proves it from `0 <= k <= 2`, so only the order of rungs picks between two incomparable grades | Rung-2 side tested; rung 1 waits L3.8 |
| B12-4 | P | `law mixed(a: bool, x: int) = (if a { x } else { x + 1 }) >= x;` | Proved: enumerate `a`, rung 2 on each residual | L3.8, D2 |
| B12-5 | R | the same with `x - 1` | Refuted at a = false | L3.8 |
| B12-6 | P, U | `law swapTwice(p: (T, T)) = swap(swap(p)) == p;` | CheckedExhaustive on the index instance; not over a float type with NaN | LAW-shape |
| B12-7 | F | `law eqSym(p: (T, T)) = (p.0 == p.1) == (p.1 == p.0);` | Not reduced; Obligated at `T := int` | LAW-shape, L3.8 |

**Rung 2 | rung 3.**

| ID | Class | Program | Expected | Status |
|---|---|---|---|---|
| B23-1 | P | `(x + 1) * (x + 1) == x * x + 2 * x + 1` | Proved(#domain) at rung 2 | Tested |
| B23-2 | P | `x * 0 == 0` | Proved at rung 2 | Tested |
| B23-3 | U | `law addAssoc(a: f64, b: f64, c: f64) = (a + b) + c == a + (b + c);` | Not proved; today `relations` reads `+` at f64 as int (D6) | L3.8; latent |
| B23-4 | F | `x * y * z >= 0` (false) | Rung 2 takes nothing; rung 7 refutes | Rung-2 side tested |
| B23-5 | P | four-way `++` associativity | Proved at rung 3 from the `++` axiom | L3.9 |
| B23-6 | F, U | `l2` needs the unproved law `l1` | Not proved at rung 3 | L3.9 |
| B23-7 | R | `l1` and `l2` need each other | Cycle reported, naming both | L3.9 |
| B23-8 | U | `f(g(x)) == x` with `f(g(x)) == g(f(x))` | The law failing weak acyclicity is left out of rung 3 | L3.9 |

**Rung 3 | rung 4** (`add` recurses on its first argument).

| ID | Class | Program | Expected | Status |
|---|---|---|---|---|
| B34-1 | P | `add(#zero, n) == n` | Proved at rung 2 | L6.12a |
| B34-2 | F, P | `add(n, #zero) == n` | Proved at rung 4 | L6.12 |
| B34-3 | R | `add(n, #zero) == #succ(n)` | Refuted at n = #zero (D10) | L6.12, L3.8 |
| B34-4 | P | `size(mirror(t)) == size(t)` | Proved at rung 4 by law 21 | FOLD-unique |
| B34-5 | F | `add(m, n) == add(n, m)` | Obligated (nested induction) | L6.12, L3.8 |

**Rung 4 | rung 5.**

| ID | Class | Program | Expected | Status |
|---|---|---|---|---|
| B45-1 | P | `count(#cons(h, #nil)) <= 1` | Proved at rung 5 by a split on `h == 0` | L6.12a, L6.12b |
| B45-2 | F | `(a != 0).implies(count(#cons(a, #cons(h, #nil))) <= 2)` | Obligated | L6.12b, ARM-split |
| B45-3 | P | `size(t) >= 0` | Proved at rung 4 | L6.12 |

**Rung 5 | rung 6.**

| ID | Class | Program | Expected | Status |
|---|---|---|---|---|
| B56-1 | P | triangle inequality with `if` absolute values | DESIGN says Proved at rung 5 with halves closed at rung 2; each half is refused today by the name-tie rule (D3) | Halves tested; split waits L3.8 |
| B56-2 | P | `(if a > 0 {1} else {0}) + (if b > 0 {1} else {0}) <= 2` | Raw form refused (tie); joined form Proved, so the join is rung 5's | Tested |
| B56-3 | P | `(a <= c && b <= c).implies(max(a, b) <= c)` | Rung 2 proves it alone (D13) | Tested |
| B56-4 | F, P | `x * y * z <= 27`, x, y, z in `int[0..=3]` | Bounded at rung 6 though the check covers the whole domain (D11) | L3.20 |
| B56-5 | D | two halves with equal residuals | Merged; result independent of condition order | L3.8 |
| B56-6 | P | `(lo <= hi).implies(clamp(x, lo, hi) in lo..=hi)` | Proved at rung 2 in min/max form; the if-chain form is refused and needs rung 5 (D5) | Tested |

**Rung 6 | rung 7.**

| ID | Class | Program | Expected | Status |
|---|---|---|---|---|
| B67-1 | P | B56-4 | Bounded kept over Obligated | L3.20 |
| B67-2 | F | the cube with nonnegative premises, no written bound | Rung 6 does not run; Obligated | L3.8 |
| B67-3 | F, R, U | `(y >= 0 && w <= 0).implies(y * w >= 0)` (false) | Rung 2 says not proved, never a fake refutation; rung 7 refutes at y = 1, w = -1 | Rung-2 side tested |
| B67-4 | F, U | `a * a >= 0` | Open with no premise, never refuted; Proved with `a >= 0` | Tested |
| B67-5 | F | `(x * (x + 1)) mod 2 == 0` | Not refuted today; the spec wants Proved, after MOD-residue | "Not refuted" tested |

**Rung 7 | rung 8.**

| ID | Class | Program | Expected | Status |
|---|---|---|---|---|
| B78-1 | P | B67-2 with a pinned Proof | Obligated at rung 7, then Proved(certificate) at rung 8, kept | L15.5 |
| B78-2 | P | B45-2 with `#cases` on `h == 0` | Proved(certificate) | L15.5 |
| B78-3 | D | the same law renamed or compiled again | The same sampled cases | L3.8 |

**Rung 8 | rung 9.**

| ID | Class | Program | Expected | Status |
|---|---|---|---|---|
| B89-1 | U | `@assume(associative)` on f64 `+` | The license is lost today (D1) | L16.1 |
| B89-2 | P | `@assume(associative)` on `max` at int | Redundant; reporting unspecified (D12) | L16.1 |
| B89-3 | R | `@assume(commutative)` on `a - b` | Refuted at rung 2 and rejected | L16.1 |
| B89-4 | U | `@assume` with an invalid pinned proof | Rejected at rung 8 | L15.5, L16.1 |

**Non-adjacent interactions.**

| ID | Interaction | Status |
|---|---|---|
| N1 | Refutations end the ladder, each checked with the interpreter | Tested; D9 adds two wrong refutations (U2, U3), held for RUNG2-definedness |
| N2 | A pinned Proof always reaches rung 8; an invalid one is rejected even where rung 2 proved the law | L15.5 |
| N3 | The highest grade is kept: Bounded over Obligated | L3.20 |
| N4 | Termination premise: `spin(n) * 0 == 0` must not be Proved | L6.12; the same defect for `mod` is testable now and fails (D9, U1) |
| N5 | Rung 5 sends halves to rung 6 | L3.20, L3.8 |
| N6 | Rung 3 uses only proved laws; cycles reported | L3.9 |
| N7 | Contradictory premises close a part | Tested |
| N8 | Same verdict under reordering and renaming | Tested |
| N9 | Scaling at n and 8n | Tested |

| Boundary | Cases | Testable now | Written |
|---|---|---|---|
| 1\|2 | 7 | 2 | 2 |
| 2\|3 | 8 | 3 | 3 |
| 3\|4 | 5 | 0 | 0 |
| 4\|5 | 3 | 0 | 0 |
| 5\|6 | 6 | 4 | 4 |
| 6\|7 | 5 | 3 | 3 |
| 7\|8 | 3 | 0 | 0 |
| 8\|9 | 4 | 0 | 0 |
| Non-adjacent | 9 | 4 + D9 | 4 + 2 held back |
| **Total** | **50** | **16** | **16** (14 test functions) |

## C. Spec defects, each with a proposed sentence

- **D1 (defect i, stronger than stated).** Rung 7 runs on every obligation rungs 1 to 6 do not prove, and Obligated sits above Assumed, so an `@assume` always ends at Obligated, which licenses nothing. Proposed: "An `@assume` is not a rung that competes with the others: the obligation keeps the highest grade rungs 1–8 reached, and a written waiver is recorded beside that grade as `Assumed(site)`, so that the obligation licenses the union of what its grade and the waiver license; `Bounded` or `Obligated` with a waiver license static regroupings as written trust, and a refutation at any rung ends the ladder whatever is waived." Take `Assumed` out of the grade chain into a note.
- **D2 (defect ii).** Rung 1 with mixed listed and unlisted binders. Proposed: "When some binders have listed domains and others do not, the listed binders are enumerated and at each binding the body is partially evaluated; each residual goes to rung 2 with the binding as a premise, a refutation there is a refutation with the binding and rung 2's witness, and the obligation is `Proved(#domain)` when every residual is; `CheckedExhaustive` is reached only when every binder's domain is listed."
- **D3.** Rung 5's triangle example conflicts with the name-tie refusal (XR3 fix B): each half is refused by rung 2. Options: (a) change the example and add "A half that rung 2 refuses, a name tie included, is open, and the part goes on as a stopped one."; (b) break name ties by binder position.
- **D4.** A binding where an operation fails. Proposed: "A binding at which an operation of the obligation fails, so that its body gives no `true`, refutes it, the witness printing the failure as the body's value; rung 2 reports such a point only where its translation reads the failing operation exactly."
- **D5.** The clamp example is false without `lo <= hi`: "`(lo <= hi).implies(clamp(x, lo, hi) in lo..=hi)`, with `clamp` as `max(lo, min(x, hi))`, is exact `min`/`max` transfer".
- **D6.** Rung 2 reads f64 arithmetic as int (`relations` turns `(a+b)+c == a+(b+c)` at f64 into `0 == 0`; latent, callers filter to int). Proposed: "Rung 2 reads `+`, `-`, `*`, `div`, `mod` and comparisons as integer arithmetic only where their operands' type is `int` or a refinement of it; at any other carrier the term is an atom."
- **D7.** `Grade` has no order and no meet in code, though its doc comment cites a meet. Code gap for L3.8.
- **D8.** The ladder text does not say a rung-2 refusal continues the ladder. Proposed: "A question the Presburger layer refuses (sec:domains) is open, as one it does not prove is."
- **D9 (soundness, code and spec).** The polynomial normal form cancels `mod` and `div` by a divisor that may be zero. Confirmed with the interpreter:

| Case | Kind | Rung 2 today | Interpreter |
|---|---|---|---|
| U1 | wrong proof | `(x mod n) * 0 == 0` and `x mod n - x mod n == 0` Proved from `true` and from `n >= 0` | both `false` at x = 3, n = 0 |
| U2 | wrong refutation | `n >= 0 && x mod n == 0 ⊢ n >= 1` refuted at n = 0 | the premise is false there |
| U3 | wrong refutation | `n == 0 ⊢ x mod n == (x + 1) mod n` refuted at n = 0 | the goal is true there (both sides the same atom) |

  Cause: `div_mod_by_term` leaves quotient and remainder as free integers at n == 0, which over-approximates a premise but not a goal or a witness. Proposed: "An operation that may fail, such as `div` or `mod` by a divisor the premises do not show nonzero, is removed from a residual only with the premise that it does not fail, as a call is removed only with the termination premise; and a point at which such an operation fails is a witness only where the body's value there is what the interpreter gives."
- **D10.** Rung 4: "A base case or step with no binder left that evaluates to `false` is a refutation with that member as witness."
- **D11.** Rung 6 on the whole domain: "When the instance rung 6 runs is the whole domain of every binder, its success is `CheckedExhaustive(domain)`."
- **D12.** "A waiver on an obligation that rungs 1–8 bring to proof grade is reported as unneeded." Also state that a refutation at rungs 1 to 7 rejects the claim at build time.
- **D13.** "where rung 2's own disjunctions (`min`, `max`, `abs`) settle the part, no split is made."

## D. Negative controls (each applied once, reverted, checked with `cmp`)

| Control | Mutation | Failing tests |
|---|---|---|
| NC1 | the old `products` | scaling, 63.3 times the bytes |
| NC2 | refute without checking the countermodel | 4 |
| NC3 | never refute | 6 |
| NC4 | no pair products | 3 |
| NC5 | refusal reported as "not proved" | 4 |
| NC6 | verdict depends on conjunct order | 3 |
| NC7 | premises' auxiliary definitions dropped | 2 |
| NC8 | every call treated as recursive | 2 |
| NC9 | a term outside the fragment read as `true` | 1 |

## E. Failing tests held for RUNG2-definedness

```rust
#[test]
fn a_residual_that_drops_a_failing_operation_is_not_proved() {
    for goal in ["ok(x, n) = (x mod n) * 0 == 0;", "ok(x, n) = x mod n - x mod n == 0;"] {
        for premise in ["ok(x, n) = true;", "ok(x, n) = n >= 0;"] {
            let e = rung2(premise, goal);
            assert!(!matches!(e, Entailment::Proved(_)), "{premise} to {goal}: {e}");
        }
    }
}

#[test]
fn a_point_where_an_operation_fails_is_a_witness_only_where_the_interpreter_agrees() {
    for (p, g) in [
        ("ok(x, n) = n >= 0 && x mod n == 0;", "ok(x, n) = n >= 1;"),
        ("ok(x, n) = n == 0;", "ok(x, n) = x mod n == (x + 1) mod n;"),
    ] {
        if let Entailment::Refuted(_) = rung2(p, g) { refuted_at(p, g); }
    }
}
```

Follow-ups (ledger, queued, feeding L3.8): RUNG2-definedness (D9), RUNG2-carrier (D6), C2-chain (`products` still O(factors × part) when one chain of premises connects all factors; no test yet), LADDER-tie-rung5 (D3).

## Claims most likely to be wrong

- U3: a wrong refutation only because the interpreter gives `true` for `#divByZero == #divByZero`. If the loose atom bubbles out of `==` (bubbling decision, 2026-11-07), the refutation is correct. U1 and U2 hold either way.
- B12-3's "rung 2 also proves it" was tested with `0 <= k <= 2` written as a premise; whether the driver passes a listed domain to rung 2 that way is L3.8's choice.
