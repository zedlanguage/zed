//! Each pass over a deep graph, and over the deep values, patterns and types inside it, is
//! linear in its depth: the benchmarks of `scaling.rs`, whose tests make each pass at small
//! sizes and whose deep tests make it on a 2 MiB stack.

use zed_tests::deep::on_small_stack;
use zed_tests::scaling::check_order;
use zedc::zir::validate::validate;
use zedc::zir::{Op, Region, Src, binary, text};

use crate::scaling::{
    deep_type_text, family_graph, generated_binders, holding, nested_ifs, wide_family,
};

#[test]
fn checking_a_deep_graph_is_linear_in_its_depth() {
    on_small_stack(|| {
        let (small, large) = (nested_ifs(12_500), nested_ifs(100_000));
        let twins = (nested_ifs(12_500), nested_ifs(100_000));
        check_order("checking nested `if` regions", 12_500, 1, |k| {
            validate(if k == 12_500 { &small } else { &large }).unwrap();
        });
        check_order("comparing nested `if` regions", 12_500, 1, |k| {
            let (g, h) = if k == 12_500 {
                (&small, &twins.0)
            } else {
                (&large, &twins.1)
            };
            assert!(g == h);
        });
    });
}

#[test]
fn writing_and_reading_a_deep_graph_in_binary_is_linear_in_its_depth() {
    on_small_stack(|| {
        let (small, large) = (nested_ifs(12_500), nested_ifs(100_000));
        check_order("writing nested `if` regions in binary", 12_500, 1, |k| {
            binary::encode(if k == 12_500 { &small } else { &large })
                .expect("memory for the bytes");
        });
        let (small, large) = (
            binary::encode(&small).expect("memory for the bytes"),
            binary::encode(&large).expect("memory for the bytes"),
        );
        check_order("reading nested `if` regions in binary", 12_500, 1, |k| {
            binary::decode(if k == 12_500 { &small } else { &large }).unwrap();
        });
    });
}

#[test]
fn writing_and_reading_a_deep_graph_as_text_is_linear_in_the_text() {
    on_small_stack(|| {
        let (small, large) = (nested_ifs(250), nested_ifs(2_000));
        // Power 2: the text grows as the square of the depth.
        check_order("writing nested `if` regions as text", 250, 2, |k| {
            text::print(if k == 250 { &small } else { &large });
        });
        let (small, large) = (text::print(&small), text::print(&large));
        check_order("reading nested `if` regions as text", 250, 2, |k| {
            text::parse(if k == 250 { &small } else { &large }).unwrap();
        });
    });
}

#[test]
fn writing_and_reading_deep_values_patterns_and_types_is_linear_in_their_depth() {
    on_small_stack(|| {
        let (small, large) = (holding(12_500, 1_000), holding(100_000, 8_000));
        let pick = |k: usize| if k == 12_500 { &small } else { &large };
        check_order(
            "writing deep values and patterns in binary",
            12_500,
            1,
            |k| {
                binary::encode(pick(k)).expect("memory for the bytes");
            },
        );
        let (bs, bl) = (
            binary::encode(&small).expect("memory for the bytes"),
            binary::encode(&large).expect("memory for the bytes"),
        );
        check_order(
            "reading deep values and patterns in binary",
            12_500,
            1,
            |k| {
                binary::decode(if k == 12_500 { &bs } else { &bl }).unwrap();
            },
        );
        let text_of = |g: &Region| {
            let Src::Const(v) = &g.nodes[0].inputs[0] else {
                unreachable!("a constant")
            };
            v.to_string()
        };
        let (vs, vl) = (text_of(&small), text_of(&large));
        check_order("reading a deep value as text", 12_500, 1, |k| {
            text::parse_value(if k == 12_500 { &vs } else { &vl }).unwrap();
        });
        let pattern_of = |g: &Region| {
            let Op::Match(ps) = &g.nodes[0].op else {
                unreachable!("a match")
            };
            text::pattern(&ps[0])
        };
        check_order("writing a deep pattern as text", 1_000, 1, |k| {
            pattern_of(if k == 1_000 { &small } else { &large });
        });
        let (ps, pl) = (pattern_of(&small), pattern_of(&large));
        check_order("reading a deep pattern as text", 1_000, 1, |k| {
            text::parse_pattern(if k == 1_000 { &ps } else { &pl }).unwrap();
        });
        let (ts, tl) = (deep_type_text(250), deep_type_text(2_000));
        check_order("reading a deep type as text", 250, 1, |k| {
            text::parse_type(if k == 250 { &ts } else { &tl }).unwrap();
        });
    });
}

#[test]
fn writing_and_reading_generated_binders_is_linear_in_their_number() {
    let (small, large) = (generated_binders(12_500), generated_binders(100_000));
    let pick = |k: usize| if k == 12_500 { &small } else { &large };
    check_order("writing generated binders as text", 12_500, 1, |k| {
        text::pattern(pick(k));
    });
    let (ts, tl) = (text::pattern(&small), text::pattern(&large));
    check_order("reading generated binders as text", 12_500, 1, |k| {
        text::parse_pattern(if k == 12_500 { &ts } else { &tl }).unwrap();
    });
}

#[test]
fn printing_a_deep_graph_for_debugging_is_linear_in_its_depth() {
    on_small_stack(|| {
        let (small, large) = (nested_ifs(12_500), nested_ifs(100_000));
        check_order(
            "printing nested `if` regions for debugging",
            12_500,
            1,
            |k| {
                let _ = format!("{:?}", if k == 12_500 { &small } else { &large });
            },
        );
    });
}

#[test]
fn reading_a_wide_family_and_refusing_a_repeated_key_is_n_log_n_in_its_entries() {
    let (n, large) = (2_000, 16_000);
    let pick = |k: usize, a, b| if k == n { a } else { b };
    let (ok_small, ok_large) = (wide_family(n, false), wide_family(large, false));
    let (bad_small, bad_large) = (wide_family(n, true), wide_family(large, true));
    check_order("reading a family of n entries as text", n, 1, |k| {
        text::parse_value(pick(k, &ok_small, &ok_large)).unwrap();
    });
    check_order(
        "refusing a family of n entries that repeats a key",
        n,
        1,
        |k| {
            text::parse_value(pick(k, &bad_small, &bad_large)).unwrap_err();
        },
    );
    let (bin_small, bin_large) = (family_graph(&ok_small), family_graph(&ok_large));
    check_order("reading a family of n entries in binary", n, 1, |k| {
        binary::decode(if k == n { &bin_small } else { &bin_large }).unwrap();
    });
}
