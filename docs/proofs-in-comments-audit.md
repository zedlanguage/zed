# Proofs in code comments: audit (DOC-proofs-in-comments-audit)

Author, STANDING, 2026-11-20: "also you must add proofs and reasoning in the code comments too".
The audit was split by crate over three agents; each table lists source, claim, code site and
status, with counts per crate at its top:

- [proofdoc1a](proofs-audit/proofdoc1a.md): zed-kernel, zed-numtheory, zed-collections,
  zed-graph, zed-native, zed-rt, zed-alloc-count, zed-clif, zed-tools, zedc-zir, tools/.
  44 rows, 8 sites edited. One argument was wrong: zed-rt `on_fault` said `mprotect` is
  async-signal-safe, which POSIX does not say; corrected and marked Not proved, row
  FAIL-rt-fault-mprotect-signal-safety.
- [proofdoc1b](proofs-audit/proofdoc1b.md): zedc-check, zedc-base, zedc-elab (zedc-syntax and
  zedc-lattice in one row). zedc-check 28 found, 13 already there, 14 added; zedc-base 5, 2,
  3; zedc-elab 2, 0, 2. No wrong argument.
- [proofdoc1](proofs-audit/proofdoc1.md): zedc-types, zedc-presburger, zedc-preimage,
  zedc-solvers, zedc-int, and first the memos dryC1 named in c4937d86c. zedc-types 20 found,
  16 already there, 4 added, 1 Not proved; zedc-presburger 9, 3, 6, 1; zedc-preimage 9, 8;
  zedc-solvers 1, 1; zedc-int 1, 1. Every memo dryC1 named is safe; `RunMark` holds by a
  convention of its callers, row TYPES-run-marks-move-safe.

The second pass, row DOC-proofs-in-comments-audit-rest, swept what the first left:

- [proofdoc2](proofs-audit/proofdoc2.md): the rest of proofdoc1a's crates, the ledger and
  running log for them, the agent reports under /home/luke/Work/wt (no code claim in them), and
  the two rows the first pass filed (FAIL-rt-fault-mprotect-signal-safety, cf4648fff;
  TYPES-run-marks-move-safe, ea2e24555). zed-kernel 25 found, 20 already there, 1 added, 2 Not
  proved (rows named at the sites); zedc-zir 3, 1, 2, 0, 1 corrected; zed-rt 1, corrected;
  zedc-types 1, added, corrected; zed-alloc-count 1, 1; zed-clif 1, 1. One fault fixed with a
  test: zedc-zir `Domain::normal` kept a class built from its fields as written, so `4 mod 9`
  and `1 mod 4` had two normal forms.
- [proofdoc2a](proofs-audit/proofdoc2a.md): zedc-resolve, zedc-stage, zedc, zedc-syntax,
  zedc-lattice, zed-cert, zed-meter-settings, and two leftovers of proofdoc1b. 98 claims found,
  9 already there, 87 added, 1 Not proved (row PROOF-meter-no-thread-before-main), 2
  corrected. One fault fixed with a test: a `main` in a block inside a string's hole made the
  syntax-tree builder panic.
- [proofdoc2b](proofs-audit/proofdoc2b.md): zedc-check, zedc-types, zedc-presburger,
  zedc-preimage, zedc-base, zedc-elab, zedc-solvers, zedc-int, from the commits ranked highest.
  32 found, 15 already there, 14 added, 1 Not proved (row PROOF-never-bind-order-fit-needs), 4
  corrected. One fault fixed with a test: a map or set display with a key of many values was
  typed as a guaranteed read (`{ n -> 10 }[n + 1]` gave `#notFound` at run time), row
  FAIL-display-computed-key-sure; and the pair count of PROOF-star-pairs was false.

Not swept: the commits each table of the second pass lists as not read (proofdoc2: 156;
proofdoc2b: 28 at score 4 or more and all 382 entries below), proofdoc2a's high-ranked commits
whose code moved to zedc-check, zedc-elab and zedc-types, and the sites proofdoc2a names as not
traced. They are row DOC-proofs-in-comments-audit-rest-2.

The third pass, row DOC-proofs-in-comments-audit-rest-2, reads those:

- [proofdoc3](proofs-audit/proofdoc3.md): one table, a section per helper (proofdoc3a:
  zed-kernel read only, the lower crates, the front-end crates, zedc-preimage, 80870e234 and
  the untraced sites; proofdoc3b: zedc-check, zedc-elab, zedc-base and the moved commits;
  proofdoc3c: zedc-types, zedc-presburger, zedc-solvers, zedc-int).

| Section | Entries read | Claims found | Already there | Added or completed | Marked unproved | False |
|---|---|---|---|---|---|---|
| proofdoc3a | 173 of 345 | zed-kernel 71 (reported only), zedc-preimage 35, 28 in the other crates | 69 | 19 | 11 | 2 faults fixed with a test red first (zedc-preimage spans.rs priority tie, zedc-syntax recover.rs kept declaration); 2 false zed-kernel comments reported (row FIX-poly-limit-comments) |
| proofdoc3b | 90 of 365 | zedc-check 89 in 75 entries | 67 | 10 | 0 | 1: `fold_dir_end`'s round bound (row FAIL-fold-rotating-tuple-rounds) |
| proofdoc3c | 12 in full, 361 through four filters | 31 | 8 | 24 | 2 sub-cases (`find_tied_point`, `root_approx`) | 0 |

The rows filed for what this pass left open are listed in docs/plan_dag.md under row
DOC-proofs-in-comments-audit-rest-2. The entries not read, and the 361 read only through
filters, are row DOC-proofs-in-comments-audit-rest-3.
