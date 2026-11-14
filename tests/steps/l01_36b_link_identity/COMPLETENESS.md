# l01_36b_link_identity: completeness (step L1.36b)

The code under test is the cache of links in `crates/zed-native/src/link.rs` (`Identity`, the
key of a link, the GNU build ID that records it, `Record` and the files a link read, `kept`,
the working directory and `sweep`) and the hash of the runtime library's sources in
`crates/zed-native/src/sources.rs`. Each row is a case; the second column names the test that
covers it, or says why no test is needed.

| Case | Covering test, or reason none is needed |
|---|---|
| **What the key names** | |
| the object file, by its bytes | `identity::the_object_file_is_named_by_its_bytes`, `cache::an_edited_program_links_again` |
| the runtime library, by its bytes, not its path | `identity::the_runtime_library_is_named_by_its_bytes_not_its_path` |
| the linker, by the driver's `--version` and `-Wl,--version` reports | `identity::the_linker_is_named_by_its_drivers_reports`, `cache::another_release_of_the_driver_or_the_linker_links_again` |
| the files the link read and the environment | `identity::the_key_names_the_files_read_and_the_environment` |
| the same toolchain on other paths | `cache::the_same_toolchain_on_other_paths_keeps_the_executable` |
| one program at two outputs | `cache::one_program_built_at_two_outputs_records_one_key` |
| a driver that gives no version; a missing runtime library | `identity::a_driver_that_gives_no_version_is_refused`, `identity::a_missing_runtime_library_is_named` |
| **When the output is kept** | |
| a file of the user's at the output | `cache::a_file_of_the_users_at_the_output_is_replaced` |
| the executable edited or stripped | `deps::an_edited_executable_links_again`, `deps::a_stripped_executable_links_again` |
| the executable without its record | `deps::an_executable_without_its_record_links_again` |
| a library the link read changed; another library path | `deps::a_changed_library_the_link_read_links_again`, `deps::another_library_path_links_again` |
| a file the record names that is gone | `deps::a_record_naming_a_file_that_is_gone_links_again` |
| a record that names no files | `deps::a_record_naming_no_files_reads_back` |
| another input format | `deps::another_input_format_links_again` |
| an output of any name | `deps::an_output_may_take_any_name` |
| **The list of files the linker read** | |
| GNU ld's and lld's forms, escapes for `#`, space and `\` | `deps::the_list_of_either_linker_is_read`, `deps::lld_s_list_is_read_with_its_escapes` |
| `$` written `$$` | `deps::a_dollar_sign_in_a_listed_path_is_read` |
| each file hashed once | `deps::each_file_is_hashed_once` |
| a linker that lists no files, a listed file that cannot be read, a linker that writes no build ID | `deps::a_linker_that_lists_no_files_is_refused`, `deps::a_listed_file_that_cannot_be_read_is_refused`, `deps::a_linker_that_writes_no_build_id_is_refused` |
| **Working directories** | |
| a file at the old object file's name | `leftover::a_file_at_the_old_object_files_name_blocks_no_build` |
| what stopped builds left removed; a running build's kept; another output's kept | `leftover::a_build_removes_what_stopped_builds_left_and_keeps_a_running_ones` |
| names not of the form `<out>.zed-build.<digits>.<digits>`, and a file of that form | `leftover::the_sweep_removes_only_what_has_the_form_of_a_working_directory` |
| builds to one output at once | `leftover::builds_to_one_output_at_once_all_succeed` |
| **The runtime library's sources** | |
| the sources named by the library | `sources::the_runtime_library_names_the_sources_it_was_built_from` |
| an edit in the crate or a dependency; an edit outside both | `sources::an_edit_in_the_crate_or_a_crate_it_depends_on_changes_the_hash`, `sources::an_edit_outside_the_crate_and_its_dependencies_leaves_the_hash` |
| one tree in two directories | `sources::one_tree_in_two_directories_gives_one_hash` |
| each way a manifest names a dependency: inline table, dotted key, table of its own, with and without a version, build dependencies (also per target), dev-dependencies (not followed), a path through `.`, registry versions, commented lines, workspace dependencies listed and not listed, another table | `sources::each_way_a_manifest_names_a_dependency_is_read` |
| a directory reached again through a symbolic link | `sources::a_directory_reached_again_through_a_symbolic_link_is_read_once` |
| `include_str!` with a path built by a macro, an escape, a literal that never ends, beside a real include | `sources::an_include_the_scan_does_not_follow_leaves_those_after_it` |
| a missing source directory; a crate outside every workspace | `sources::a_missing_source_directory_is_named`, `sources::a_crate_outside_every_workspace_is_named` |
| a directory or file that cannot be read during the walk | none: the tests run as root in a user namespace (`zrun` runs `unshare --user --map-root-user`), which reads a mode-000 directory, so no test here can make one unreadable; the message is the one of `a_missing_source_directory_is_named`, from the same `map_err` form `{path}: {error}` |
| **The driver's runs** | `scaling::a_build_runs_the_driver_for_its_reports_and_its_link` |
| **Scaling** | in `bench.rs` (`--bench`); not correctness tests (P178) |
