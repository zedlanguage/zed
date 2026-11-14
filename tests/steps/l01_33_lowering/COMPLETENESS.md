# l01_33_lowering: completeness of the correctness tests

DESIGN L1.33: kernel term → ZIR lowering, ports' state edges, CSE by content address, and the
inverse `raise` kept for the tests. Code under test: crates/zedc-zir/src/zir/lower.rs.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| **One node per kernel operation** | | |
| Every corpus row, waves included, lowered, validated, canonicalized, read back from text and binary, raised, and still passing | corpus.rs `every_row_passes_through_zir` | |
| `fam` reading a computed capture; `reindex` then `fold`; a float fold keeping identity and tree; `discard` | forms.rs (4 tests) | |
| `fix` lattice and definedness; a `match` inside a fixpoint; `gen` with the guard before and after | forms.rs (4 tests) | |
| Nested patterns bind in preorder (tuple, positional atom, wildcard) | forms.rs `nested_patterns_bind_in_preorder` | |
| A fields pattern, matched and not matched, and in the arm of a function that pushes | reach.rs `a_fields_pattern_lowers_and_raises_to_the_same_value` | |
| A primitive of fixed arity as a value stays the primitive | forms.rs `a_primitive_passed_as_a_value_stays_the_primitive` | |
| A primitive of any arity (`(..)`) as a value is refused | reach.rs `a_variadic_primitive_as_a_value_is_refused` | |
| An unbound name; an unknown primitive; a name bound inside a function is not the function of that name outside | errors.rs (2 tests) | |
| Captures taken on demand, once per region, at every depth | scaling.rs `a_name_read_at_every_depth_*` (2 tests) | |
| **Ports** | | |
| Two pushes thread one state edge; root is a port region with the states in order of use | ports.rs `two_pushes_thread_one_state_edge` | |
| An arm that does not touch a port passes its state through; each arm passes the ports it does not touch | ports.rs (2 tests) | |
| A `let`-bound function that pushes: called once is inlined, called twice is one `lambda` and two `apply` | ports.rs (2 tests) | |
| The same with a function that reads and pushes (two states), and one that only reads | reach.rs `a_function_that_reads_and_pushes_called_twice_threads_both_states`, `a_function_that_only_reads_called_twice_is_one_lambda` | |
| A port function whose body holds a `fam` with a `fold`, or a definedness `fix`: they stay pure inside the lambda | reach.rs `a_port_function_whose_body_holds_a_family_a_fold_or_a_fixpoint_keeps_them_pure` | |
| Ports kept by place, not by address | ports.rs `ports_are_kept_by_place_not_address` | |
| A function that uses one port, used as a value: refused | errors.rs `a_function_that_pushes_is_only_called` | |
| A function that uses two ports, used as a value: refused, naming both ports | reach.rs `a_function_using_two_ports_used_as_a_value_names_both` | |
| A push in a fold's operator; in a lambda passed as an argument: refused as a function not bound by `let` | errors.rs `a_port_inside_a_fold_is_refused`, reach.rs `a_push_in_a_family_or_in_a_lambda_passed_as_an_argument_is_refused` | |
| A push in `gen`, a push or a read in a definedness `fix`: refused as inside a loop | reach.rs `a_push_in_a_generation_or_a_fixpoint_is_refused_as_inside_a_loop` | |
| A push or a read in a family's body: refused | reach.rs (refusal and port only) | FAIL-zir-lower-port-in-family-message: the wording says a function not bound by `let`, not a family |
| A port inside a recursive function (`rec` region) | none | The lowering makes no `rec` region: kernel recursion is a `fix`, and `let` is not recursive (an unbound self-reference is the unbound-name error) |
| **CSE** | | |
| A repeated product is one node; `let` names (hints) do not separate equal nodes; equal lambdas are one node | cse.rs (3 tests) | |
| Equal nodes in different regions stay apart | cse.rs `nodes_in_different_regions_stay_apart` | |
| Equal reads and equal pushes are never merged | reach.rs `equal_reads_and_equal_pushes_are_never_merged` | |
| Facet order on edges | none | L1.33: edges carry `_` and hints only, so the lowering writes no facets; facet order is l01_32's |
| Equal lambdas of a wide constant under a memory limit | asks.rs (4 tests) | |
| **Raise** | | |
| Every lowered term raises to the same value and pushes | `same`/`round_trip` in ports.rs, reach.rs, scaling.rs, corpus.rs | |
| A root with the wrong number of results for its states | errors.rs `raise_wants_one_value_and_a_state_per_port` | |
| `rec` and `wave` have no kernel term | reach.rs `raise_refuses_the_ops_the_lowering_does_not_make` | `derived` is refused by the same branch of `node` |
| `raise_node`, `raise_with` (per-node raising for native hooks) | none here | Used by crates/zed-native/src/hooks.rs, tested by l01_36_cranelift |
| `lower_sited` (source sites per node) | none here | Tested by l01_36a_executables sites.rs |
| **Size** | bench.rs, scaling.rs | Unusual sizes are benchmarks (P178); scaling.rs keeps small-size checks of each benchmark input |
