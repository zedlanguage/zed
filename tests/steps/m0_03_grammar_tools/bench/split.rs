//! The depth scan and the split parse, each linear in the number of items; the items each
//! finds are checked at small sizes by
//! `split::the_scan_and_the_split_parse_find_each_item_at_small_sizes`.

use zed_tests::scaling::{check, inputs};
use zed_tools::split::Splitter;

use crate::split::{cuts_between_items, items, real, split_parses_items, tokens, view};

#[test]
fn the_scan_and_the_split_parse_scale_with_the_number_of_items() {
    let spec = real("split_scaling");
    let sp = Splitter::new(&spec.syntactic, "Item").expect("the real grammar splits");
    let toks = inputs(2000, |n| tokens(&spec, &items(n)).expect("lexes"));
    check("split: the depth scan", 2000, |n| {
        cuts_between_items(&sp, &view(&toks[&n]), n);
    });
    check("split: the split parse", 2000, |n| {
        split_parses_items(&spec, &sp, &view(&toks[&n]), n);
    });
}
