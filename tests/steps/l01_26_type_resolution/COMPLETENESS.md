# Completeness: type resolution (L1.26)

Row TEST-complete-literals (author P189). The code under test is the checker,
`crates/zedc-check/src/check/` (`walk.rs`, `mod.rs`, `widen.rs`, `read.rs`, `arms.rs`), and the
types of `crates/zedc-types/src/ty.rs`: resolution rules 1, 3 and 4 of DESIGN.md
"Resolution", the bounds clause, narrowing by `is`, the fit of a function argument to its
slot, and the literal rules L1.26a and L1.26b. Expected results are from DESIGN.md step L1.26,
sec:type_resolution, sec:type_language, sec:failure and sec:order. This pass looked for the
literal cases; the new tests of literals stand beside the L1.26a tests, in
`../l01_26a_generic_literals/positions.rs` and `features.rs`, whose COMPLETENESS.md lists
them, and none was added here. llvm-cov, as a floor, over both groups' tests (regions):
`check/walk.rs` 82.99% before, 83.59% after; `check/mod.rs` 86.20% before, 86.47% after;
`check/widen.rs` 81.64% before and after; `check/read.rs` 81.28% before and after;
`check/arms.rs` 39.26% before and after; `ty.rs` 85.67% before, 85.69% after. The counts move
by up to 0.3% from run to run with the order of the test threads.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| A declared function's signature from its body; the error at the use that leaves a parameter no carrier | `signatures.rs` | |
| Bounds clause `t for X in t1 \| … \| tn`: scope, resolution, one carrier per call | `bounds.rs` | |
| A bare literal at an operand of `==`, a union parameter with one numeric member, a tuple component at any depth | `literals.rs`, `adoption.rs` | Each syntactic position and feature of a literal: `../l01_26a_generic_literals/COMPLETENESS.md` |
| `is` narrowing through `not`, `&&`, `\|\|`; chains | `narrowing.rs`, `is_chains.rs` | |
| Narrowing an undeclared parameter at each call; atoms its uses handle | `given.rs`, `handled.rs` | |
| A function argument fitting its slot: names, order, defaults, lambdas | `fits.rs`; `../l01_26a_generic_literals/positions.rs` `a_lambda_in_a_slot_of_a_declared_function_type_gives_its_literal_that_slots_carrier`; `../l01_26a_generic_literals/features.rs` `a_lambda_needs_a_parameter_for_each_argument_passed_by_position` | |
| Calls through a value; named and positional calls | `calls.rs`, `named_calls.rs` | |
| The type table of every operator | `op_table.rs` | The slow `div_mod` case is not split (row brief) |
| Divisors that hold no zero; operations that always fail | `divisors.rs`, `always_fails.rs` | |
| `f64(n)` exact for a bounded `int` | `exact_casts.rs` | |
| `==` with no common value; ordered tuples | `no_common_value.rs`, `ordered_tuples.rs` | |
| Lookups: tuple keys, `#outOfBounds`, partial maps | `tuple_keys.rs`, `out_of_bounds.rs`, `partial_maps.rs` | |
| `Never`: as a type, as an operand | `never.rs`, `never_operands.rs` | |
| Functions held in tuples; shared tuples; payload variables | `held_functions.rs`, `shared_tuples.rs`, `payload_variables.rs` | |
| Cycles of definitions | `cycles.rs` | |
| Doc comments | `docs.rs` | |
| Soundness: accepted programs never meet a kernel type error | `soundness.rs`, `random.rs` | |
| Deep nesting on the default stack | `deep_ops.rs`, `deep_scaling.rs`, `deep_types.rs` | Thousands deep are benchmarks (P178), `bench/` |
| Scaling of classes and atoms | `scaling.rs`, `atom_scaling.rs`, `curried_classes.rs` | Larger sizes are benchmarks (P178), `bench/` |
| `match` arms (`check/arms.rs`, 39% of regions) | | `match` is built at L2.4; at L1 no program reaches it |
| Struct, type, method, local, `import`, `initial`, `while`, `until` statements | | Rejected by name resolution at this layer (`crates/zedc-check/src/check/walk.rs`, the statement match at line 1607) |
| Units and facets | | Units exist only in the parser at this layer |
| Uncovered functions in `walk.rs` that are not literal code: `power_too_large`, `product_too_large`, `build_too_large`, `main_limits`, `main_limit_fix`, `width_error`, `bit_domains`, `floors_at`, `min_max_tuples`, `read_image`, `fit_needs` | | Values past the address space (A100), bit domains, `min`/`max` of tuples and functions with needs; outside the rules of this group and not measured by this pass |
