//! Keying the fences of a document is linear in its sections: the benchmark of `keys.rs`, whose
//! test keys a generated document of a few sections.

use zed_tests::scaling::{check, inputs};

use crate::keys::{keys, sections_of};

#[test]
fn keying_scales_with_the_document() {
    let texts = inputs(2000, sections_of);
    check("fence keys, by sections", 2000, |n| {
        assert_eq!(keys(&texts[&n]).len(), 2 * n);
    });
}
