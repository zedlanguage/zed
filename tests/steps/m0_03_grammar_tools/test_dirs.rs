//! The test directories of the M0.3 helpers (TEST-m0_03-flake). Two tests that used one name
//! deleted each other's files when they ran at once, which failed one or both only now and
//! then; a name is now given once in a test binary, and a second use fails at once.

use std::panic;

use zed_tests::step_helpers::m0_03_grammar_tools::Dir;

#[test]
fn a_test_directory_name_is_given_once_and_lies_under_the_binary_name() {
    let dir = Dir::new("given_once");
    assert!(
        dir.root()
            .ends_with("/build/tool_tests/m0_03_grammar_tools/given_once"),
        "{}",
        dir.root()
    );
    let again = panic::catch_unwind(|| Dir::new("given_once"));
    let Err(why) = again else {
        panic!("a second use of the name was taken");
    };
    assert_eq!(
        why.downcast_ref::<String>().map(String::as_str),
        Some("two tests use the test directory given_once")
    );
    // The first directory is still there.
    assert!(std::path::Path::new(&dir.root()).is_dir());
}
