//! The keys: a content hash of the parts, with the parts' boundaries in it.

use zedc::query::key;

#[test]
fn equal_parts_give_equal_keys_and_one_byte_changes_the_key() {
    let a = key("front", &[b"x = 1;\n"]);
    assert_eq!(a, key("front", &[b"x = 1;\n"]));
    assert_ne!(a, key("front", &[b"x = 2;\n"]));
    assert_ne!(a, key("row", &[b"x = 1;\n"]));
    // Names of one length differ in their bytes, not only in their length prefix.
    assert_ne!(key("row", &[b"x"]), key("run", &[b"x"]));
}

#[test]
fn the_parts_boundaries_are_hashed() {
    assert_ne!(key("row", &[b"ab", b"c"]), key("row", &[b"a", b"bc"]));
    assert_ne!(key("row", &[b"ab"]), key("row", &[b"ab", b""]));
}
