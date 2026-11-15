//! The ZIR address of a string held in parts costs its bytes (ZIR-string-tree-address), and the
//! lowering merges two nodes over equal strings held in different trees at the cost of their
//! distinct nodes, not their bytes (ZIR-string-cse-tree): the benchmarks of `string_trees.rs`,
//! whose tests give one string in three trees one address and one node.

use zed_kernel::term::Prim;
use zed_kernel::term::build::{lam, lit, prim, var};
use zed_kernel::text::Text;
use zed_kernel::value::Value;
use zed_tests::scaling::{check_order, inputs};
use zedc::zir::Region;
use zedc::zir::canon::address;

/// A graph whose one constant is `n` bytes held as blocks of 300 bytes joined from the left,
/// each block distinct, so the address writes the string as one block of `n` bytes.
fn joined(n: usize) -> Region {
    let mut t = Text::from("");
    for i in 0..n / 300 {
        t = Text::join(&t, &Text::from(format!("{i:0>300}"))).expect("under 2^64 bytes");
    }
    zedc::zir::lower::lower(&lit(Value::Str(t))).expect("lowered")
}

#[test]
fn a_string_held_in_parts_is_addressed_in_time_linear_in_its_bytes() {
    let n = 300 << 9;
    let graphs = inputs(n, joined);
    check_order("the ZIR address of a joined string", n, 1, |k| {
        address(&graphs[&k]).expect("memory for the address");
    });
}

/// `n` distinct blocks of 200 bytes, joined from the left (`left`) or from the right, and the
/// result doubled 40 times: about `2^48 n` bytes in O(n) nodes, as
/// `l01_31_zir::bench::shared_strings` builds it. The two trees share no node.
fn doubled(n: usize, left: bool) -> Text {
    let block = |i: usize| Text::from(format!("{i:0>200}"));
    let mut t = Text::from("");
    for i in 0..n {
        t = if left {
            Text::join(&t, &block(i))
        } else {
            Text::join(&block(n - 1 - i), &t)
        }
        .expect("under 2^64 bytes");
    }
    (0..40).fold(t, |t, _| Text::join(&t, &t).expect("under 2^64 bytes"))
}

/// `x -> (x ++ s1, x ++ s2)` with `s1` and `s2` one text of about `2^48 n` bytes held in the two
/// trees of [`doubled`]: the lowering merges the two `++` nodes, and the strings are told equal
/// by their distinct nodes (`zir::canon::Strings`), so the work is linear in `n`. A byte
/// comparison of the two would read about 2^56 bytes at the smaller size.
#[test]
fn equal_strings_in_doubled_trees_are_merged_in_linear_time() {
    let n = 64;
    let terms = inputs(n, |k| {
        let s = |left| lit(Value::Str(doubled(k, left)));
        lam(
            &["x"],
            prim(
                Prim::Tuple,
                vec![
                    prim(Prim::Concat, vec![var("x"), s(true)]),
                    prim(Prim::Concat, vec![var("x"), s(false)]),
                ],
            ),
        )
    });
    check_order("merging two equal doubled strings", n, 1, |k| {
        let g = zedc::zir::lower::lower(&terms[&k]).expect("lowered");
        let body = &g.nodes[0].regions[0];
        let concats = body
            .nodes
            .iter()
            .filter(|n| matches!(n.op, zedc::zir::Op::Prim(Prim::Concat)))
            .count();
        assert_eq!(concats, 1, "the two `++` nodes are one");
    });
}
