# Completeness: zed-kernel

Crate zed-kernel's own unit tests: the exact arithmetic of `num` (division, products, gcd,
Bezout coefficients, reciprocals and digit reading in `num/fast.rs`, each on both sides of its
crossover; `Rat` with kept prime powers in `num.rs`) and the L1 prelude words on scalars in
`words.rs` (casts, `String`, `abs`, `len`, `lower`, `upper`, `trim`, `codePoint`, `scalar`,
`utf8`, `fromUtf8`). Plan row TEST-complete-kernel (author P188, P189). The new tests are in
`src/completeness/` (`fast.rs`, `rat.rs`, `words.rs`); expected results come from DESIGN.md
L1.17, L1.18 and L1.39c, and for the arithmetic from num-bigint's schoolbook results.

Line coverage of the crate's unit tests (llvm-cov, `cargo test -p zed-kernel --lib`, benchmarks
skipped), before and after: whole crate 65.30% to 66.61%; `num.rs` 82.9% to 94.1%;
`num/fast.rs` 94.3% to 98.5%; `num/float_text.rs` 95.4% to 98.2%; `words.rs` 27.3% to 89.8%.

| Case | Covering test | Or reason none is needed |
|---|---|---|
| Division handed to num-bigint at a divisor of 4096 bits, past the leaf at 4097; the same for the quotient's bits | `fast.rs::division_on_both_sides_of_the_leaf` | |
| Past the leaf: the sparse method (rows) at few nonzero divisor words, the reciprocal at full density, exactly one change between, and `div_by_rows` agreeing with `sparse_flip` | `fast.rs::past_the_leaf_both_methods_and_the_flip_between_them` | |
| Past the leaf, every path (`div_rem_uint`, `rem_uint`, `div_rem_past_leaf`, `div_rem_by_reciprocal`, `div_rem_sparse`) equal to num-bigint, an exact multiple and the largest remainder among them | `fast.rs::past_the_leaf_both_methods_and_the_flip_between_them`, `fast.rs::edge_forms_past_the_leaf` | |
| Divisor forms all ones, `2^(b-1)`, `2^(b-1)+1`, random | `fast.rs::edge_forms_past_the_leaf` | |
| Small divisions: dividend below the divisor, equal, one word | `fast.rs::small_divisions` | |
| Division by zero | `fast.rs::a_zero_divisor_panics` | |
| Products on both sides of the leaf (48 and 49 words), unequal lengths, rows and transforms each taken, sparse times dense by rows | `fast.rs::products_on_both_sides_of_the_leaf` | |
| Products against a kept spectrum (cached transform) on both sides of its flip | `fast.rs::kept_spectra_products` | |
| Reciprocals of 1 to 3000 bits at each leaf, including powers of two and one past | `fast.rs::reciprocals` | |
| gcd: iterative, recursive and the crossover hook at each leaf and lift, a zero operand | `fast.rs::gcds` | |
| Reading digits at each leaf | `fast.rs::digits_read_at_each_leaf` | |
| Bezout coefficients at both lifts, all four sign pairs, a zero operand | `fast.rs::bezout_coefficients` | |
| Euclidean `div` and `mod` at each pair of signs, `i64::MIN` by `-1` and by 7 (`-1 div 4, -1 mod 4` is `-1, 3`) | `rat.rs::euclidean_division_at_each_pair_of_signs` | |
| Euclidean division of kept powers (`2^100`, `1e1000`) by each sign and by a power; an exact division keeps the powers | `rat.rs::euclidean_division_of_kept_powers` | |
| Powers: 0, 1, -1 at huge even and odd exponents stay small; `0^-1` is none (`#divByZero`); negative exponents; a huge exponent kept | `rat.rs::powers_by_an_integer` | |
| Nearest `f64` and `f32`: infinite past the largest finite, the tie at the top, `MAX`, least subnormal, zero below half of it, ties to even, round to 1.0 | `rat.rs::nearest_floats` | |
| `neg`, `try_neg`, `abs` | `rat.rs::negation` | |
| Parity of plain and kept values, odd and even decimals | `rat.rs::parity` | |
| Borrowed and built numerator and denominator of kept values | `rat.rs::built_parts` | |
| Literal text of zero, integers, decimals, a huge exponent, ratios | `rat.rs::literal_texts` | |
| `int(s)`: leading zeros, `-0`, the `i64` ends and one past, a long digit string; `#invalid` for empty, `-`, `+5`, spaces, a point, an exponent, digits of another script, full-width digits | `words.rs::int_of_a_string` | |
| `rat(s)`: `3r`, `-1r/3r`, without the `r`s, decimals; `#invalid` for a zero denominator, mixed `r`, a negative denominator, `.5`, `5.`, `+1r`, empty, an exponent, another script | `words.rs::rat_of_a_string` | |
| `f64(s)`, `f32(s)`: signed zero, `inf`, `-inf`, `nan`, underflow to a signed zero, the least subnormal, `#overflow`, `#invalid` forms, `f32` rounded once from the digits | `words.rs::floats_of_a_string` | |
| Casts between number kinds: exact, `#inexact`, `#overflow`, `#invalid` for an infinity or NaN at an exact kind, `f64` of `f32` exact, a big integer `rat` to `int` | `words.rs::casts_between_number_kinds` | |
| `f64(-0.0)` and `f32(-0.0f64)` keep the sign of zero | `completeness::words::casts_between_number_kinds` | Fixed by row FAIL-values-cast-negzero: a finite `f64` is narrowed as a float, not through its rational, which has no sign of zero. Neighbors there: `0.0`, the least `f32` subnormal, `±1e-46` (`#inexact`), the largest `f32` and the next `f64` past it at each sign (`#overflow`). |
| A cast of a bool, tuple, atom or family; each other word at a kind it does not take | `words.rs::words_at_kinds_they_do_not_take` | |
| `abs` at each kind and sign, `i64::MIN` widening, `-0.0`, `-inf`, NaN, `f32` | `words.rs::abs_at_each_kind` | |
| `len` in code points; full case mappings (`straße`, `ﬁ`, final sigma, dotted `İ`); `trim` with Unicode white space, all space, empty, zero-width space kept | `words.rs::string_words` | |
| `codePoint` of one scalar, `#notScalar` for empty, two, a combining sequence; `scalar` at 0, `0xD7FF`, `0xE000`, `0x10FFFF`, `#notScalar` for surrogates, past `0x10FFFF`, negative, big | `words.rs::code_points_and_scalars` | |
| `utf8` of empty, two and four byte forms; `fromUtf8` round trip at each width, key order, empty; `#badUtf8` for overlong, surrogate, past `0x10FFFF`, truncated, stray continuation, `0xFF`, 256, -1, a big value | `words.rs::utf8_both_ways` | |
| `String(x)` of strings, floats (`0.1`, `1.0e300`, `inf`, `nan`, `-0.0`, `f32`), big integers, rats, named and payload atoms, sets, bools, a tuple with an `f32` member | `words.rs::string_of_each_kind` | |
| `len` of a string past `i64::MAX` code points | | Unreachable in a test: needs more than 2^63 characters. |
| A refused allocation in `num.rs`, `words.rs` and `num/room.rs` (`TooLarge`, `Watch`, the order and equality fallbacks to normal forms) | | Needs the system to refuse memory; tested where refusals are measured (COMPLEXITY.md K30 and the benchmark modules), not in small tests (P178). |
| `const fn` bodies in `num/fast.rs` (`Field::new`, `mont_of`, `inv_mod`) | | Evaluated at compile time, so llvm-cov reports them as not run. |
| `bits.rs` (bit words, machine operations) | | Covered by l01_39a_bit_words and l01_39f_int_machine_ops (TEST-complete-reduced). |
| `types/**`, `frames`, `value.rs` printing and keys | | Covered by l01_22_type_representation, l01_23_subtyping and crate zedc-types (TEST-complete-types). |
| `eval.rs`, `term.rs`, `term/walk.rs`, `print.rs`, `print/dag.rs` | | Reached through l01_15_kernel_terms to l01_18_scalar_interpreter and m0_09 to m0_11 (TEST-complete-names, TEST-complete-values, TEST-complete-m0). |
| `provenance.rs` | | Covered by l01_20_provenance (TEST-complete-diagnostics) and l01_24_refinement_lattices (TEST-complete-lattices). |
| `poly.rs`, `poly/roots.rs` | | Covered by l01_39_reduced_product (TEST-complete-reduced) and its own unit tests (96 to 98%). |
| `sites.rs`, `site_table.rs`, `address.rs`, `limits.rs`, `text.rs` | | Used by zedc, zedc-stage, zed-native and l01_37a_short_addresses; covered by TEST-complete-crates and TEST-complete-native. |
| Large sizes and scaling | the `bench` modules | Benchmarks (P178). |
