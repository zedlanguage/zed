use zed_tests::scaling;
use zedc::resolve::topo::topo_around_cycles;

use super::super::cycles::{cycles_beside_a_chain, deps_around_cycles};
use super::super::scaling::resolved;

/// `n` cycles of two functions each, and a chain of `n` functions, each calling the one before
/// and a function of a cycle: the checker's pass at `n` and `8n`. Its own work hides that of
/// the order, which `the_order_around_many_cycles_scales` times alone.
#[test]
fn many_cycles_beside_many_functions_scale() {
    let units = resolved(200, cycles_beside_a_chain);
    scaling::check_order("n cycles beside a chain of n functions", 200, 1, |n| {
        let info = units[&n].check();
        assert_eq!(info.errors.len(), n);
        assert_eq!(info.sigs.len(), n + 1);
    });
}

/// The order alone, around `n` cycles of two items each, with a chain of `n` items each
/// depending on the one before and on an item of a cycle; `check_order` sees what the checker's
/// pass above hides.
#[test]
fn the_order_around_many_cycles_scales() {
    let made = scaling::inputs(20_000, deps_around_cycles);
    scaling::check_order("the order around n cycles", 20_000, 1, |n| {
        let deps = &made[&n];
        let (order, cycles) = topo_around_cycles(deps, deps.len());
        assert_eq!((order.len(), cycles.len()), (n, n));
    });
}
