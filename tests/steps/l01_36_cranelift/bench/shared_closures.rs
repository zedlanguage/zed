//! A closure the kernel is handed is one term however many closures share it, so a rule of
//! `d` layers each holding the layer below twice is handed over in time linear in `d`, by the
//! counting machine and by native code (COMPLEXITY.md R9). The small instances are in
//! `shared_closures.rs`.

use zed_kernel::{Evaluator, Value, World};
use zed_tests::scaling;
use zedc::zir::memory;

use crate::planned;
use crate::shared_closures::doubled;

/// The depth of the counting machine's scaling test, and 8 times it.
const D_MACHINE: usize = 10_000;

/// The depth of native code's scaling test, and 8 times it.
const D_NATIVE: usize = 1_500;

#[test]
fn the_machine_hands_the_kernel_a_layered_rule_in_time_linear_in_its_layers() {
    // Planning and the machine's passes recurse on the rule's layers.
    scaling::on_a_thread(1 << 30, || {
        let programs = [D_MACHINE, scaling::FACTOR * D_MACHINE].map(|d| (d, planned(&doubled(d))));
        scaling::check(
            "memory::run of a fold by d layers of a rule held twice",
            D_MACHINE,
            |d| {
                let (_, (g, p)) = programs.iter().find(|(m, _)| *m == d).unwrap();
                let (v, _) = memory::run(g.graph(), p, &mut Evaluator::new(World::new())).unwrap();
                assert_eq!(v, Value::Int(3));
            },
        );
    });
}

#[test]
fn native_code_hands_the_kernel_a_layered_rule_in_time_linear_in_its_layers() {
    let programs = [D_NATIVE, scaling::FACTOR * D_NATIVE].map(|d| (d, planned(&doubled(d))));
    scaling::check(
        "native run of a fold by d layers of a rule held twice",
        D_NATIVE,
        |d| {
            let (_, (g, p)) = programs.iter().find(|(m, _)| *m == d).unwrap();
            let o = zed_native::run(g, p, &mut Evaluator::new(World::new())).unwrap();
            assert_eq!(o.value, Value::Int(3));
        },
    );
}
