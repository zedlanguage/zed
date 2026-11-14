//! A chain of `n` units with syntax errors, loaded at `n` and `8n` (`package_recovery.rs`).

use zed_tests::scaling;
use zedc::query::Db;
use zedc::unit::load;

use crate::package_recovery::a_broken_chain;

#[test]
fn reporting_the_errors_of_a_chain_of_broken_units_scales() {
    let n = 200;
    let pkgs = scaling::inputs(n, a_broken_chain);
    scaling::check_order("a chain of units with syntax errors", n, 1, |k| {
        std::hint::black_box(load(&mut Db::new(), &pkgs[&k], &["main"]));
    });
}
