# M0.11 completeness: prelude axioms, unit addresses and limits

Code under test: the axiom table `zedc::axioms` (crates/zedc-base/src/axioms.rs) and its prelude
copy `zed/prelude/axioms.zed`; `zedc::canon::unit_address` and `zed/prelude/unit.zed`; the
limit `zed_kernel::eval::MIN_NESTED_CALLS` and `zed/prelude/limits.zed`; all against DESIGN.md step M0.11.
Lines of axioms.rs reached (llvm-cov, without the `bench` module): 61% before (7 of 18 missed),
83% after (3 missed: the `const fn ax`, which runs only at compile time). `unit_address` is
reached in full (mod.rs of the canonicalizer, 100%, see m0_07's table).

| Case | Covering test, or the reason none is needed |
|---|---|
| The table holds every law DESIGN names, at each operator and carrier, and no other, and no law twice | `cases::the_table_holds_exactly_the_laws_design_names` |
| `-` at `f64`, `/`, `div`, `mod` and `clamp` carry no law; `min`, `max` no identity at `int`; an operator at a carrier it has no arrow at has none; an unknown operator has none | `cases::operators_with_no_law_by_axiom_have_none` |
| Constants compare as the kernel's values: a float by its bits (NaN equal to itself, `-0.0` not `0.0`), int, bool, string, and two carriers never equal | `cases::constants_compare_as_the_kernels_values_do` |
| Each axiom holds on the M0.10 harness instances | `axioms::every_axiom_holds_on_the_harness_instances` |
| A false claim of each kind of law is refuted by the same check | `axioms::a_false_claim_of_each_kind_is_refuted` |
| The prelude copy is the Rust table | `axioms::the_prelude_copy_is_the_rust_table` |
| Order-chain compositions at `int`, `f64`, strings; weak links never prove a strict law; `!=` never transitive | `axioms::the_compositions_an_order_chain_needs_are_axioms` |
| Float instances hold NaN, both zeros, both infinities | `axioms::the_float_instances_hold_the_ieee_corner_values` |
| Strings compare by code point | `axioms::strings_compare_by_code_point` |
| `==` and `!=` at every carrier, `f64` only symmetric (and `==` transitive) | `axioms::equality_has_its_laws_at_every_carrier` |
| Bit words on every value of 1 to 8 binary digits and about 2^63, 2^64; `shl(1, 64)` is 2^64; `shr` rounds toward negative infinity | `axioms::the_bit_word_axioms_hold_at_every_width_to_8`, `axioms::false_shift_axioms_are_refuted_where_they_fail` |
| `min`/`max` at `f64` are IEEE `minimum`/`maximum`: signed zeros, NaN zero, infinite identities; `minsd` does not have the laws | `axioms::min_and_max_at_f64_have_the_ieee_laws_and_minsd_has_not` |
| The two zeros compare equal, stay two values, find one key | `signed_zero::*` |
| Comparisons at `bool` | None: DESIGN M0.11 names the comparison laws at `int`, `f64` and the string types only, and the table has no arrow of `<`, `<=`, `>`, `>=` at `bool`; the kernel evaluates them on booleans (eval.rs, natural order `false` before `true`), so if the language gives them an arrow at `bool`, DESIGN must list their laws there |
| `++` at each string type | The kernel has one string carrier (`String`); the other string types' arrows come with their layers, as M0.11 says |
| Unit address: pinned value, local names and export order do not change it, a changed local helper changes it through its export, the arrows of an overloaded name all hashed | `units::*`; and `m0_07 cases::a_unit_address_hashes_its_exports_sorted_by_name_then_address` |
| Limit: the prelude's `minNestedCalls` is 20 000, equal to `MIN_NESTED_CALLS` | `cases::the_prelude_limit_of_nested_calls_is_the_rust_one` |
| Chains of 20 000 nested calls, one more, and fifty times as many run | `bench::limits::twenty_thousand_nested_calls_are_accepted` (an unusual size, P178); small chains in `limits::a_few_nested_calls_and_a_short_doubled_string_are_accepted` |
| No minimum of steps or of memory (DESIGN: "there is no minimum of steps or of memory") | `fail_limits_steps_memory::the_limits_unit_names_only_the_minimum_of_nested_calls` (the unit declares `minNestedCalls` alone); `limits::with_no_fuel_no_count_of_steps_stops_the_evaluation` (small sizes), `tests/full` `ten_million_and_one_steps_run_with_no_fuel` (one step past the old minimum of ten million), `bench::limits::a_value_of_almost_a_gibibyte_is_accepted` (no memory limit stops a value of 2^30 - 1 bytes) |
| Fuel, an evaluator setting and not a limit, counted exactly | `limits::the_step_past_the_fuel_is_refused` |
| Linear work of the harness | `bench::the_harness_is_linear_in_the_tuples_it_checks`; small widths in `scaling::the_harness_checks_each_triple_of_a_narrow_word_once` |
