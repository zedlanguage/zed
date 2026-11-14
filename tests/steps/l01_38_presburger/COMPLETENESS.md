# Completeness: the linear-relation domain (L1.38)

Row TEST-complete-presburger (author P189). The code under test is the linear-relation domain,
crate `crates/zedc-presburger` (module `presburger` and its submodules, re-exported as
`zedc::store::presburger`): the formula constructors and printing, `satisfiable`, `decide`,
`project`, `project_each`, `project_each_boxed`, `row_box`, `entails` and rung 2, the refusals
and their repairs, `eliminated` and `colors`, and the translation of a function's terms into a
relation (`zedc::store::preimage::relations`) as the checker reads it. Expected results are from
DESIGN.md step L1.38 and its paragraph "Where this document does not say", and sec:constraints;
where DESIGN is silent (the printed form of a row, the box of `row_box`), from the doc comment
of the function, which is cited at the test.

llvm-cov of this group's tests and the crate's unit tests (benchmarks skipped), as a floor,
regions (lines) before → after: COVERAGE.

Tests in `completeness.rs` unless a file is named.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
CASES
