//! The notes on `n` refused pushes of a value holding a written and an unwritten parameter,
//! at `n` and `8n` (`fresh_names.rs`, plan row MSG-push-note-mixed-written-unwritten).

use zed_tests::scaling;

use crate::fresh_names::{mixed_pushes, notes_of_mixed_pushes_print_both};

#[test]
fn notes_on_many_mixed_pushes_scale() {
    // Each refused push reads the call's bind of its unwritten parameter and keeps its written
    // one: one lookup per class variable of the pushed value, O(log b) in the call's b binds,
    // and one rebuild of the value, so the n refusals cost O(n log n) at most. A search of
    // the call's binds by scan, or of all the program's classes, per refusal would be n².
    let n = 200;
    let inputs = scaling::inputs(n, mixed_pushes);
    scaling::check_order(
        "the notes on n refused pushes of a value with a written and an unwritten parameter",
        n,
        1,
        |size| notes_of_mixed_pushes_print_both(&inputs[&size], size),
    );
}
