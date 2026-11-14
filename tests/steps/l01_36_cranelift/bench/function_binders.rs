//! A function scrutinee bound by a name, `match f { h -> h(z) }`, is one word or edge whatever
//! the function captured: O(1) per match. The small instances are in `function_binders.rs`.

use zed_kernel::World;
use zed_kernel::term::build::{app, var};

use super::scaling::check_run;
use crate::function_binders::{bind, calls, match1};

/// `n` matches of a function bound by a name and called: O(1) each, so the run is O(n).
#[test]
fn binders_of_a_function_scale() {
    check_run(
        "n matches of a function by a name",
        1_800,
        |n| {
            calls(
                n,
                match1(var("f"), bind("h"), app(var("h"), vec![var("z")])),
            )
        },
        |_| World::new(),
    );
}
