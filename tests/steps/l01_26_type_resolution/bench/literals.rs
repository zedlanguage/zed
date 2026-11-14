use zed_tests::scaling;

use super::super::literals::{deep, deep_operands, menus, shapes, wide, wide_tuple};

#[test]
fn adopting_at_a_union_of_many_tuple_shapes_scales() {
    checks_linearly(
        "adopting the literals of tuples at n tuple shapes",
        2048,
        shapes,
        |_| 8,
    );
}

/// Checks the programs `text(n)` and `text(8n)`, lexed, parsed and resolved before timing,
/// and checks the checker's work is linear; each check adopts `adopts(n)` literals.
fn checks_linearly(what: &str, n: usize, text: fn(usize) -> String, adopts: fn(usize) -> usize) {
    use zed_tests::deep::statements;
    let units: Vec<_> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let stmts = statements(&text(m));
            let res = zedc::resolve::resolve(&stmts).unwrap();
            (m, stmts, res)
        })
        .collect();
    scaling::check_order(what, n, 1, |m| {
        let (_, stmts, res) = units.iter().find(|(k, _, _)| *k == m).unwrap();
        let info = zedc::check::walk::check(stmts, res);
        assert!(info.errors.is_empty(), "{:?}", info.errors);
        assert_eq!(info.adopt.len(), adopts(m));
    });
}

#[test]
fn adopting_the_literals_of_a_wide_tuple_scales() {
    checks_linearly(
        "adopting the literals of tuples of width n",
        2048,
        wide,
        |m| 3 * m,
    );
}

#[test]
fn adopting_the_literals_of_a_deep_tuple_scales() {
    // The parser, the checker and the type printer recurse on the nesting, within a 2 MiB
    // stack at 1,024 deep (it ran on 512 MiB, TY-sub-stack).
    zed_tests::deep::on_small_stack(|| {
        checks_linearly(
            "adopting the literals of tuples nested n deep",
            128,
            deep,
            |m| 2 * (m + 1),
        );
    });
}

#[test]
fn pairing_the_sides_of_a_deep_comparison_scales() {
    // The check of the whole program in `adopting_the_literals_of_a_deep_tuple_scales` spends
    // about 357,000 instructions a level, most of them outside `==`, and that hides a `sides`
    // that walks each level's whole type for variables, O(d^2) with no allocation: the test
    // passed such a `sides` at 9.1 times the instructions from depth 128 to 1,024. Here the
    // operands are built before the timing, and only their pairing by `==` is timed. The
    // pairing itself spends about 106,000 instructions a level, most in `class_of_ty` of each
    // literal's carrier, so the O(d^2) walk reaches the limit only from depth 2,048: that
    // `sides` takes 37.3 times the instructions from 2,048 to 16,384 here, and this one 8.0.
    let ops: Vec<_> = [2048, scaling::FACTOR * 2048]
        .into_iter()
        .map(|d| (d, deep_operands(d)))
        .collect();
    scaling::check_order(
        "pairing the sides of == of tuples nested n deep",
        2048,
        1,
        |d| {
            let (_, o) = ops.iter().find(|(k, _)| *k == d).unwrap();
            assert_eq!(o.adoptions(), d + 1);
        },
    );
}

#[test]
fn the_component_repairs_of_a_wide_tuple_scale() {
    // One repair per component, each read once in each shape.
    let n = 8192;
    let units: Vec<_> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let stmts = zed_tests::deep::statements(&wide_tuple(m));
            let res = zedc::resolve::resolve(&stmts).unwrap();
            (m, stmts, res)
        })
        .collect();
    scaling::check_order(
        "the repairs of a tuple of n components compared with a literal",
        n,
        1,
        |m| {
            let (_, stmts, res) = units.iter().find(|(k, _, _)| *k == m).unwrap();
            let info = zedc::check::walk::check(stmts, res);
            assert_eq!(info.errors.len(), 1);
            assert!(
                info.errors[0]
                    .message
                    .contains(&format!("`x[{}] == 1`", m - 1))
            );
        },
    );
}

#[test]
fn rejecting_literals_with_their_menus_scales() {
    // A copy of every earlier error at each menu takes 45.2 times the bytes from 256 to 2,048
    // here, and fails; a scan of every earlier error's text at each menu does not, since the
    // checker's own work at each rejected literal is far larger than the scan up to n = 8,192.
    use zed_tests::deep::statements;
    let n = 1024;
    let units: Vec<_> = [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let stmts = statements(&menus(m));
            let res = zedc::resolve::resolve(&stmts).unwrap();
            (m, stmts, res)
        })
        .collect();
    scaling::check_order(
        "rejecting n decimals at a parameter and n compared with a class",
        n,
        1,
        |m| {
            let (_, stmts, res) = units.iter().find(|(k, _, _)| *k == m).unwrap();
            let info = zedc::check::walk::check(stmts, res);
            assert_eq!(info.errors.len(), 2 * m);
        },
    );
}
