//! `zedc run` on `n` rejections under `n` refused questions, at `n` and `8n`
//! (`refused_in_rejection.rs`).

use zed_tests::scaling;

use crate::refused_in_rejection::{many_groups, rejections_under_refused_tests};
use crate::refused_warning::unit;

/// Each rejection names the one question on its names: finding them is within n log n, where
/// reading every question of the scope for each rejection would be n².
#[test]
fn many_rejections_under_many_refused_tests_scale() {
    let n = 20;
    let files = scaling::inputs(n, |m| {
        unit("rejection", &format!("groups{m}.zed"), &many_groups(m))
    });
    scaling::check(
        "zedc run on n rejections under n refused questions",
        n,
        |m| rejections_under_refused_tests(&files[&m], m),
    );
}
