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

Not swept: the agent reports under /home/luke/Work/wt (all three), the running log and ledger
(proofdoc1a and proofdoc1b), the commits each agent ranked below its cut, and the crates
zedc-resolve, zedc-stage, zedc, zedc-syntax, zedc-lattice (one row only), zed-cert and
zed-meter-settings. The audit is a first pass, not a complete one; the rest is row
DOC-proofs-in-comments-audit-rest.
