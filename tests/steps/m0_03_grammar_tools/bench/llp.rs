//! The LL(1)-pair checker's time on a grammar of n nested rules, linear in n; the cores it
//! counts are checked at small sizes by `llp::the_checker_reads_nested_rules_at_small_sizes`.

use zed_tests::scaling::{check, inputs};

use crate::llp::{nesting, pair_table_has_the_cores};

#[test]
fn the_checker_scales_with_the_grammar() {
    let grammars = inputs(200, nesting);
    check("llp: the pair table of n nested rules", 200, |n| {
        pair_table_has_the_cores(&grammars[&n], n);
    });
}
