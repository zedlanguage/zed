# s07b_clif_shim: completeness (step S.7b)

Row CLIF-shim. The code under test is `crates/zed-clif/src/lib.rs`, the Cranelift shim: its C
functions, each called from Rust through an `extern "C"` block with opaque handles, as a C caller
calls them. Those tests are the target `s07b_clif_shim_calls` of the package `zed-clif`
(`calls.rs`), since the step tests' package `zed-tests` forbids `unsafe`; `mod.rs` is this
folder's `zed-tests` target and checks the Cranelift version. Expected results are from DESIGN
step S.7b (the shim's interface) and the row's list of cases.

| Case | Covering test, or reason none is needed |
|---|---|
| A call and a symbol: one relocation each, named as in the text, inside the code | `calls.rs` `a_call_and_a_symbol_give_one_relocation_each_named_as_in_the_text` |
| Malformed text: an error naming the line, not a panic | `malformed_text_gives_an_error_naming_the_line` |
| A function that fails the verifier, with the verifier setting on and off | `a_function_that_fails_the_verifier_gives_an_error_naming_it` |
| The same text twice, by two handles and by one: the same bytes | `the_same_text_gives_the_same_bytes` |
| An empty text, blank lines, a comment only: no functions | `an_empty_text_gives_an_image_with_no_functions` |
| A function with no blocks (Cranelift 0.137.1 panics on it) | `a_function_with_no_blocks_gives_an_error` |
| A panic inside Cranelift (i128 arguments on x86-64): an error, and the shim works after | `a_panic_in_cranelift_gives_an_error_and_the_shim_still_works`; negative control run once, not committed: with `catch_unwind` bypassed the process aborts (SIGABRT, "panic in a function that cannot unwind") |
| An unknown target: not a triple, an empty name, an architecture Cranelift lacks | `an_unknown_target_gives_an_error` |
| An unknown flag, with and without a value; a bad value; a value missing | `an_unknown_flag_or_a_bad_value_gives_an_error` |
| Shared and instruction-set flags, white space of any kind between them | `shared_and_instruction_set_flags_are_accepted` |
| The host target | `the_host_target_compiles` |
| A released target handle, not used again, while its image is read; null to each release | `a_released_handle_is_not_needed_by_its_image` |
| A null target, a null error out-parameter, a null pointer with a length, null symbols with a count, text not UTF-8; each reader on a null image and error | `null_and_bad_arguments_give_errors_or_empty_answers` |
| Each reader past the last function and relocation, and with a null `out` | `read_image`, called by every test that generates |
| A `test`, `set`, `target` (supported or not) or `feature` line before the functions | `a_text_with_a_test_set_target_or_feature_line_gives_an_error` |
| `u0:i` past the symbols, in namespace 1, with no symbols; a test-case name; a call Cranelift adds on its own (`ceilf`) | `names_resolve_by_the_symbols_and_out_of_range_names_give_errors` |
| Jump tables and pool constants are bytes of the code, aligned, with no relocation | `constants_and_jump_tables_are_inside_the_code` |
| A well-known symbol (`ElfGlobalOffsetTable`, `CoffTlsIndex`) as a relocation target | None: no x86-64 text found that gives one; its name is Cranelift's Display of its own enum, the path the relocation kind takes, which every test reads |
| A relocation to a place inside the function (`RelocTarget::Label`) | None: no text found that gives one (the jump table and pool constant of `constants_and_jump_tables_are_inside_the_code` are resolved inside the code); not proved that Cranelift never gives one, so the shim reports one as an error naming its offset |
| A panic in a release or a reader | None reached: they read the shim's own vectors and free its own boxes; each still runs under `catch_unwind` |
| Scaling in the number of functions | `generation_scales_with_the_number_of_functions` (n = 40, 8n = 320) |
| The Cranelift version: pinned, equal to zed-native's, the only one in Cargo.lock | `mod.rs` `the_shim_pins_the_cranelift_version_of_zed_native_and_the_lock_has_no_other`, with its readers checked by `the_requirements_and_the_lock_are_read_as_written` |
