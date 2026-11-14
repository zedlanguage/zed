# Completeness: zedc-int unit tests

Row TEST-complete-crates (author P189). The code these unit tests exercise is `Int`, the
solver's unbounded integer (`src/int.rs` lines 1-450), and the helpers of `least_root` and
`strip` (`expand_pow` to `strip`, lines 734-1278): roots, the residue filter, the remainder
tree, word arithmetic and the coprime base. Expected results are the integers' own arithmetic
(DESIGN.md sec:domains, "exact, over unbounded integers"), computed with num-bigint or written
out. Tests named without a file are in `src/int/completeness.rs`; `tests::` names the older
tests in `src/int.rs`.

`Num` and its kept forms (`Kept`, `Core`, `Atom`, `Approx`, `Memo`, lines 450-733 and
1279-3094) are not exercised by these unit tests: they are the interval ends of step L1.24 and
are tested in `tests/steps/l01_24_refinement_lattices` (`ends.rs`, `past_i64.rs`, `num_text.rs`,
`kept_serial.rs`), which is that step's row.

llvm-cov lines (unit tests of the crate, benchmarks none):

| Lines | Before | After |
|---|---|---|
| `Int`, 1-450 | 142/234 (60.7%) | 234/234 (100%) |
| helpers, 734-1278 | 304/353 (86.1%) | 352/353 (99.7%) |

The one line left is `remainders`' `return Vec::new()`: the levels start with one level and the
loop only adds levels, so `levels.pop()` is never `None` (an empty list of moduli reaches the
end with an empty top level instead, tested).

| Case | Test, or reason none is needed |
|---|---|
| `Int::from` i32, i64, usize, i128 at each type's ends; `Default`; `ZERO`, `ONE` | `every_constructor_gives_one_form_per_value` |
| `Int::from(BigInt)` inside i128 equals the machine value and hashes alike | `every_constructor_gives_one_form_per_value` |
| `Int::from(BigInt)` past i128, each sign: `to_i128` is `None`, text is the decimal | `every_constructor_gives_one_form_per_value` |
| A wide result that comes back into i128 has the machine form (equal, same hash) | `every_constructor_gives_one_form_per_value` |
| `is_negative`, `is_positive`, `is_zero`, `is_odd`, `is_unit` on 0, ±1, ±2, -3, i128 ends, wide even and odd of each sign | `sign_parity_and_unit_tests_on_both_forms` |
| Negation: 0, ±small, i128::MAX, i128::MIN to 2^127 (wide), 2^127 back to i128::MIN (machine form), wide each sign | `abs_and_negation_cross_the_end_of_i128_both_ways`, `tests::values_past_i128_keep_their_order_and_come_back_small` |
| `abs` on each of those | `abs_and_negation_cross_the_end_of_i128_both_ways` |
| `+`, `-`, `*` on every pair of ends (0, units, i64 and i128 ends and one past, 2^200, 3^100, both signs): no overflow, overflow to wide, wide back to machine, both wide; products of 64-bit operands, of 128-bit operands that fit and that overflow | `sums_differences_and_products_agree_with_num_bigint_on_every_path` |
| Order: machine against machine, wide against wide, wide negative or positive against machine either side; sorting mixed forms | `sums_differences_and_products_agree_with_num_bigint_on_every_path`, `order_puts_each_wide_value_outside_every_machine_value` |
| `&` small by small, every sign | `tests::bit_and_reads_each_sign_as_twos_complement_at_every_size` |
| `&` wide by wide, wide by small, -1 and nonnegative masks | `tests::bit_and_reads_each_sign_as_twos_complement_at_every_size` |
| `&` with 0 either side, with itself, with its negation, -1 with a negative wide value, a mask bringing the result back into i128 | `bitwise_and_of_zero_and_of_minus_one_with_wide_values` |
| `Display`, machine and wide, each sign | `decimal_text_of_wide_values_of_both_signs` |
| `gcd`: 0 with 0; 64-bit and 128-bit machine paths; i128::MIN with itself (2^127, wide); 0 against wide either side; ±1 against wide; machine power of 2 against wide (fewer and more twos than the wide value); machine odd part of one word (sharing a factor or not); machine odd part past a word; wide by wide; every sign, both orders | `the_gcd_on_every_path_is_the_nonnegative_gcd`, `tests::the_big_gcd_agrees_with_num_bigint`, `tests::division_rounds_down_and_the_gcd_is_never_negative` |
| `gcd_recursive`: the same cases, machine pair and wide | `the_gcd_on_every_path_is_the_nonnegative_gcd` |
| `extended_gcd`: machine path and wide path, every pair of ends with zero, every sign: `g` is the gcd and `s·a + t·b = g` | `the_extended_gcd_gives_bezout_coefficients_for_every_sign` |
| `div_floor`, `mod_floor`: 64-bit, 128-bit and wide paths, every sign, `MIN / -1`, `MIN mod -1`, at and across the i64 and i128 ends | `tests::floor_division_agrees_on_every_path_for_every_sign`, `tests::division_rounds_down_and_the_gcd_is_never_negative` |
| `div_floor_wide`, `mod_floor_wide`: machine divisor (falls to `div_floor`) and wide divisor, every sign, dividend 0, below the divisor, exact and inexact | `wide_floor_division_agrees_with_floor_division_for_every_sign` |
| Exact multiples of a wide divisor have remainder 0 for every sign | `wide_floor_division_agrees_with_floor_division_for_every_sign` |
| Division by zero | None needed: the divisor is "nonzero" by contract (doc of `div_floor`, `div_floor_wide`); the callers divide by coefficients they checked |
| `least_root` on 2..50,000 against trial | `tests::least_roots_agree_with_trial_and_with_powers_of_large_bases` |
| `least_root` on powers of wide bases (odd, even, with odd parts) to prime and composite exponents and their neighbors; a power of 2 alone | `tests::least_roots_agree_with_trial_and_with_powers_of_large_bases` |
| `least_root` on 2 and 3 (below the loop bound), 4, 8, 9, 12, 36, 72, 6^6 (square then cube root), 10^9, 2^15, 5^15 (cube then 5th root) | `least_roots_of_the_smallest_bases_and_of_mixed_powers` |
| `odd_primes_below` for every bound 0..300 | `the_odd_prime_sieve_agrees_with_trial_division` |
| `OddPart::root`: power of 2 not a multiple of the index; odd part 1; one-word root found; one-word candidate refused by its bits or by the test primes; wide root found; wide non-power refused | `a_root_by_odd_part_rejects_each_way_a_candidate_fails` |
| `OddPart::filter`: the wide indices and their least primes | `tests::each_index_wider_than_a_word_has_its_least_prime` |
| `OddPart::passes`: a power passes each of its indices, wide ones included; an index past the wide list with no small prime passes (the filter is necessary only, the root refuses); a residue 0 at every prime passes; a non-cube fails | `the_residue_filter_passes_powers_and_ignores_indices_it_holds_no_prime_for` |
| `remainders`: 0 to 9 moduli (every tree shape), a value below the product | `tests::a_remainder_tree_gives_each_remainder` |
| `remainders`: one modulus, u64::MAX, moduli 1, value 0 | `a_remainder_tree_of_one_modulus_and_of_moduli_past_the_value` |
| `pow_mod`: modulus 1, exponent 0, base 0, base equal to and past the modulus, the largest prime below 2^64 | `word_arithmetic_helpers_on_their_ends` |
| `pow_word`, `inverse_mod_word`, `pow_mod_pow2` at their ends | `word_arithmetic_helpers_on_their_ends` |
| `odd_root_mod_word`, `odd_root_mod_pow2` one word and wide | `tests::a_root_in_one_word_is_the_root_by_big_numbers` |
| `expand_pow`: exponent 0, base 0, base 1, base 2, wide results | `expand_pow_writes_out_each_power` |
| `strip` by a power of 2: fewer zeros than the factor has, zeros not a multiple of its exponent, rest 1 | `tests::stripping_a_power_of_2_agrees_with_dividing_once_per_factor`, `stripping_a_power_of_2_by_a_power_of_2` |
| `strip` by other factors: odd, even, composite, a power, wider than a word, multiplicities around powers of 2, past the kernel's division leaf | `tests::stripping_any_factor_agrees_with_dividing_once_per_factor` |
| `strip` by a factor that does not divide; by a factor equal to the rest | `stripping_a_power_of_2_by_a_power_of_2` |
| `coprime_base`: empty, only ones, one prime, a composite alone, 4 and 8, 6 2 3, coprime already, equal inputs, 12 and 18, 2^20·3 and 2, 10 15 6, wide inputs sharing a wide factor | `a_coprime_base_of_each_shape_of_input` |
| `exponents_over`: no powers, one, shared factors, exponent 0, an exponent past a word; two equal products have equal exponents | `exponents_over_a_coprime_base_rebuild_each_product` |
| Interaction with language features (units, unions, ports, staging and the rest) | None needed: `Int` is the solver's arithmetic, below the language; its language-level uses are tested in the step groups that reach it (L1.24, L1.38) |
