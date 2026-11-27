//! `zedc run` on `n` rejections under `n` refused questions, at `n` and `8n`
//! (`refused_in_rejection.rs`).

use zed_tests::scaling;

use crate::refused_in_rejection::{many_groups, rejections_under_refused_tests};
use crate::refused_warning::unit;

/// Each rejection names the one question on its names: finding them is within n log n, where
/// reading every question of the scope for each rejection would be n². At 777, the size from
/// which n log n stays under the limit (DESIGN sec:plan; SCALE-small-n-rest), with each unit
/// written only in the process that runs its size (`scaling::check_inputs`).
#[test]
fn many_rejections_under_many_refused_tests_scale() {
    scaling::check_inputs(
        "zedc run on n rejections under n refused questions",
        777,
        |m| {
            (
                unit("rejection", &format!("groups{m}.zed"), &many_groups(m)),
                m,
            )
        },
        |(file, m)| rejections_under_refused_tests(file, *m),
    );
}
