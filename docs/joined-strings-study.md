# Study: exact equality of joined strings for staging (item STAGE-joined-eq, part 2)

Author's answer to QUESTIONS A7 (2026-11-07): every call at a joined string is staged as
written, whatever its length (part 1, merged with this study), and a study looks for an exact
comparison of two compressed strings in O(n log N), n the nodes and N the length, so that calls
at joins could again be keyed by their answers. The answer must be exact, never probabilistic.

Result: a method exists in the literature that meets the bound on every length a `Text` can
hold, and it is exact. It is not built in this item: it is a hard algorithm of size L whose
correctness rests on locality constants that are easy to get wrong, and the standing rule sends
such an algorithm to cross-review before it is built. Follow-up item: STAGE-joined-eq-build.

Confirmed below means read in this repository at the place named; inferred means derived from
the cited papers as remembered, not rechecked against their text in this item.

## 1. What staging needs, which is more than equality

Confirmed (`crates/zedc-stage/src/stage.rs`): staging compares strings in three ordered maps
keyed by `Value`, whose order on strings is `Text::cmp`, byte order read block by block:

- `Stub::table: Mutex<BTreeMap<Value, Said>>`, a function's answer at each argument tuple;
- the run log, `(Probe, Answer)` pairs whose `Probe::Call` holds the argument tuple and whose
  `Answer::Gives` holds the answer, recorded per part and compared when a part is looked up;
- `Mixer::literals: BTreeMap<Value, usize>`, a number for each literal term (`Mixer::number`).

So a pairwise test "are these two strings equal" is not enough: each new key must be found among
all keys of the map. What is needed is one of:

1. a canonical name per string, the same number for equal strings and different numbers for
   different ones, shared by every string of one staging run; the maps are then keyed by a
   `Value` whose strings are replaced by their names (order by name, not by bytes; no result
   reads the maps' order, inferred from the code read, to be confirmed when built); or
2. an exact byte order of two compressed strings in polylogarithmic time, so the maps keep
   their present keys.

Method B below gives both: the name, and the order by a descent of two parse trees.

## 2. The input

Confirmed (`crates/zed-kernel/src/text.rs`): a `Text` is a persistent finger tree of blocks;
nodes are shared, so a text doubled k times is O(k) nodes and 2^k times as long. Read as a
grammar it is a straight-line program (SLP) whose rules have up to nine parts (a deep tree's
four, its middle, four) and whose terminals are blocks. A block a join writes holds at most 128
bytes; a literal's block may be any length. Lengths are `usize`, so N < 2^64. The tree's shape
depends on the order of the joins, so two equal texts are in general different trees: comparing
shapes, or hash-consing the nodes, does not decide equality.

## 3. The methods

| Method | Exact | Time for a text of n nodes, length N | Names shared by all strings of a run | Score | Why |
|---|---|---|---|---|---|
| B: signature encoding, deterministic coin tossing (Mehlhorn, Sundar and Uhrig 1997; Alstrup, Brodal and Rauhe 2000; Nishimoto, I, Inenaga, Bannai and Takeda 2016) | yes | O(n log N log* N) dictionary steps; log* N ≤ 5 for every N < 2^64, so O(n log N) on every text that exists | yes | 8 | the one method that is exact, worst case and online; also gives byte order |
| C: recompression with a fixed partition per level (the restricted recompression of Kempa and Kociumaka; Jeż's pair and block compression with the partition read from a fixed function of the letter) | yes | O(n log N) expected, no worst-case bound for a fixed partition function | yes | 6 | simpler (each choice reads one neighbor), answers exact; only the time is a bound in expectation |
| A: Jeż's recompression, partition chosen from the input's pair counts (Jeż, "Faster fully compressed pattern matching by recompression", TALG 2015) | yes | O(n log N) worst case for the strings given together | no: the names depend on the set of strings | 4 | meets the bound for one comparison, but the keys of a map arrive one by one, and naming each new key with all earlier ones again costs O(total) per key, quadratic over a run |
| D: Karp-Rabin fingerprints, or any fixed hash | no | O(n) | yes | 1 | two different strings can share a fingerprint; no proof that they cannot exists, since there are more strings than fingerprints (A7 option D) |
| E: hash-consing the finger tree | no | O(n) | yes | 0 | equal texts have different trees (section 2), so equal strings get different names |
| F: Plandowski's and Lifshits's equality and pattern tests | yes | polynomial, O(n^3) for Lifshits | no | 1 | far above the bound |

### Method B in detail

Each level ℓ turns a sequence of symbols (level 0: the bytes) into a shorter one, by a rule that
reads the sequence alone, and names each piece through one dictionary per staging run. The
dictionary maps a key (level, the piece's symbols) to the next free number, and compares keys
exactly, so names are injective: two strings have one name exactly when they are equal, by
induction on the levels, since the dictionary can be read backward. Exactness needs only that
the rule be a function of the sequence; the time bound needs the rule to be local and to
shrink.

1. Runs: each maximal run `a^k`, k ≥ 2, becomes one symbol named (ℓ, run, a, k). After this no
   two neighbors are equal.
2. Deterministic coin tossing (Cole and Vishkin): each position's label starts as its symbol;
   one round replaces a label by 2p + (bit p of the label), p the lowest bit in which it
   differs from its left neighbor's label. After log* σ + O(1) rounds (σ < 2^32 the alphabet,
   so 5 or 6 rounds) the labels are in 0..5, and neighbors still differ; three passes bring
   them to 0..2. A block starts at each local maximum of the labels, so every block has 2 to 4
   symbols, except at the two ends.
3. Each block becomes one symbol named (ℓ, block, its symbols).

Each level at least halves the sequence, so a string has at most log2 N + 1 levels, and its
name is the one symbol of its last level. A position's block depends only on the r = log* σ +
O(1) symbols to its left and two to its right.

Naming a join without reading it: the level-ℓ sequence of `x ++ y` agrees with that of `x`
except in its last D symbols and with that of `y` except in its first D, for a constant D of the
order of r (the cited papers prove it). So a text is summarized, for each level, by its first
and last W symbols, W a constant somewhat larger than D + r, held as run-length lists because a
run may be any length; a text with at most 2W symbols at a level keeps that level whole. The
summary of `x ++ y` is made level by level from the summaries of `x` and `y`: at each level
the window where `x`'s end meets `y`'s start is parsed again, O(W) dictionary steps per level.
A `Text` node is named by joining its parts' summaries in order (up to eight joins for a deep
tree), with one memo entry per distinct node, kept while the staging run holds the texts (the
node's address names it for identity only, never for order, which the author allows). A text
of n distinct nodes so takes O(n log N W) dictionary steps; each block is parsed once, in its
length.

Order: two named strings are ordered by descending their parse trees from the top: at each
level, the first symbol where the two differ is expanded one level down; O(log N W) steps. So
the stub tables could also keep byte order.

Memory: O(W log L) symbols per distinct node of length L. Most nodes of a finger tree are short
(a block of at most 128 bytes has about 8 levels), so this is O(n) words times a modest
constant for typical trees and O(n log N) in the worst case; a summary can be freed once every
parent of its node has been named.

### What building B needs

- `zed-kernel`: a `Names` dictionary and the summaries, with the join of summaries; tests that
  compare names against byte equality on every pair of a corpus of random small joins and of
  doubled strings (exhaustively over short strings on a two-letter alphabet, where coin tossing
  meets all its cases), and that check the levels shrink as stated.
- `zedc-stage`: the three maps above keyed by names, or by order through the descent; `compared`
  then accepts strings of every kind again, and the test
  `l01_28_staging::dag::calls_at_joins_of_100_and_200_bytes_stage_alike` changes to: the part is
  mixed once at both lengths.
- The tests the plan row asks for: n and 8n nodes within 24x, and a doubled join of 2^40 bytes
  named in time near its 40 levels, with a negative control (comparison by bytes) run once.

## 4. Why it is not built in this item

- Size: A7 itself rated option B size L, and the plan row is M for both parts.
- Risk: B's correctness does not depend on the constants (any deterministic rule gives exact
  names), but its time bound and the join of summaries do. A window W one symbol too small
  gives a summary that is wrong near a boundary, and then two equal strings get different names:
  staging would mix a part twice, which is no error in value but is an error in the method, and
  tests on short strings may not reach it. This is the kind of algorithm the standing rule sends
  to cross-review (Opus 5.5, gpt-6.1-sol and gemini) before it is built.
- Part 1 already removes the size switch the no-thresholds rule forbids; method B only brings
  back sharing that part 1 gave up for joins, a gain in staging time, not in value.

## 5. Questions for the cross-review

1. Is method C's expected bound acceptable under the rule that answers be exact (they are; only
   the time is in expectation), given that it is perhaps half the code of B?
2. For B, the exact D and W for the run step followed by six rounds of coin tossing on 32-bit
   names, with a proof, or the constants from Nishimoto et al. checked against their text.
3. Whether keying the three maps by names (order by name) changes any result, or whether the
   byte order by descent is needed.

## References

- K. Mehlhorn, R. Sundar, C. Uhrig. "Maintaining dynamic sequences under equality tests in
  polylogarithmic time." Algorithmica 17(2), 1997.
- S. Alstrup, G. S. Brodal, T. Rauhe. "Pattern matching in dynamic texts." SODA 2000.
- T. Nishimoto, T. I, S. Inenaga, H. Bannai, M. Takeda. "Fully dynamic data structure for LCE
  queries in compressed space." MFCS 2016.
- A. Jeż. "Faster fully compressed pattern matching by recompression." ACM Transactions on
  Algorithms 11(3), 2015.
- D. Kempa, T. Kociumaka. "Resolution of the Burrows-Wheeler transform conjecture." FOCS 2020
  (restricted recompression).
- R. Cole, U. Vishkin. "Deterministic coin tossing with applications to optimal parallel list
  ranking." Information and Control 70(1), 1986.
- Y. Lifshits. "Processing compressed texts: a tractability border." CPM 2007.

These are cited from memory and were not reread for this study; the constants in section 3 are
inferred from them and are question 2 for the cross-review.
