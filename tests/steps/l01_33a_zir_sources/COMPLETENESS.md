# Completeness: l01_33a_zir_sources

Step L1.33a (DESIGN.md), the map between ZIR nodes and source nodes: each node of a graph
lowered with sites has every parse tree node it was lowered from, named by its declaration
and its path there, and the reverse map gives each parse tree node's graph nodes.

| Case | Covering test | Or reason none is needed |
|---|---|---|
| Two equal sums lowered to one node: the node has both, the reverse map of each gives it, its constant too | `sources.rs::the_addition_of_two_equal_sums_has_both_sums` | |
| A blank line, or a declaration `main` does not reach, above `f`: no entry changes | `sources.rs::text_above_a_declaration_changes_no_entry` | |
| The run-time sites table is the first lowered site, among the node's sources; sources sorted, each once; one entry a pair | `sources.rs::the_sites_table_gives_each_node_the_site_it_gave_before` | |
| A read placed outside a family body shares one node for two reads, which has both sites | `sources.rs::a_read_placed_outside_a_family_has_the_source_of_each_read` | |
| A statement among a block's statements, paths through a block | `sources.rs::each_line_of_a_chain_has_one_sum_with_both_copies` | |
| The corpus and the step units (no corpus program loads before L3): every span is a source node's; a node has a source exactly when it has a site | `corpus.rs::every_node_of_a_corpus_program_with_a_site_has_a_source` | |
| Scaling | `bench.rs::building_the_map_scales` | |
| Two top-level declarations of one name (`nth`) | | Built by counting in `SourceMap::new`; no corpus program or test here declares a name twice. |
