# Completeness: zedc-stage unit tests

Row TEST-complete-crates (author P189). The crate has no unit tests: `src/` holds no `#[test]`
and no `#[cfg(test)]` module, so no code is exercised by unit tests of its own and there are no
cases to list here. Its code (`src/defs.rs`, a unit's definitions and tests, and `src/stage.rs`,
the cones of definitions and their evaluation at build time, DESIGN.md sec:staging) is reached
through `zedc::stage` and tested by:

- `tests/steps/l01_28_staging`, with its own case list (`COMPLETENESS.md` in the group);
- `tests/steps/l01_21_test_runner` (the tests of a unit);
- `tests/steps/l01_39_reduced_product` and `tests/steps/l25_08_mutate`.
