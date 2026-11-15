//! Level names through remaps and reductions, named slicing, empty levels and misses in source
//! form (DESIGN.md sec:level_names, sec:remap_law; steps L8.2b, L8.2c, EMPTY-level-swap).

use crate::source::{prints, rejected, same, with_sales};

// ---- Names through remaps and reductions (sec:level_names) ----

#[test]
fn sales_names() {
    // "`sales::names` is `("region", "day", "sku", "quantitySold")`".
    prints(
        &with_sales("n = sales::names;\n"),
        "n",
        "(\"region\", \"day\", \"sku\", \"quantitySold\")",
    );
}

#[test]
fn a_permutation_carries_the_names() {
    // "Names through remaps": a by-name permutation moves each name with its level.
    prints(
        &with_sales("x = sales into (sku -> region -> day -> quantitySold);\nn = x::names;\n"),
        "n",
        "(\"sku\", \"region\", \"day\", \"quantitySold\")",
    );
}

#[test]
fn reduce_with_plus_names_the_leaf_sum() {
    // `totals = sales into (region -> day -> sku >< (+) -> quantitySold);` "totals is
    // { "east" -> [5], "west" -> [4, 2] }; totals::names is ("region", "day",
    // "sum_quantitySold")".
    let src = with_sales(
        "totals = sales into (region -> day -> sku >< (+) -> quantitySold);\n\
         want = { \"east\" -> [5], \"west\" -> [4, 2] };\nn = totals::names;\n",
    );
    same(&src, "totals", "want");
    prints(&src, "n", "(\"region\", \"day\", \"sum_quantitySold\")");
}

#[test]
fn reduce_with_concatenation_names_the_leaf_concat() {
    // `joined = labels into (sku -> pos >< (++) -> label);` "joined is { "A12" -> "redsmall" };
    // joined::names is ("sku", "concat_label")".
    let src = "labels: Utf8String ->? [Utf8String] with names(\"sku\", \"pos\", \"label\") = { \"A12\" -> [\"red\", \"small\"] };\n\
               joined = labels into (sku -> pos >< (++) -> label);\n\
               want = { \"A12\" -> \"redsmall\" };\nn = joined::names;\n";
    same(src, "joined", "want");
    prints(src, "n", "(\"sku\", \"concat_label\")");
}

#[test]
fn reduce_with_a_named_function_takes_its_name() {
    // `floof(...) = a + b; f = sales into (region -> day -> sku >< floof -> quantitySold);`
    // "f is { "east" -> [5], "west" -> [4, 2] }; f::names is ("region", "day",
    // "floof_quantitySold")".
    let src = with_sales(
        "floof(positional a: int, positional b: int) -> int = a + b;\n\
         f = sales into (region -> day -> sku >< floof -> quantitySold);\n\
         want = { \"east\" -> [5], \"west\" -> [4, 2] };\nn = f::names;\n",
    );
    same(&src, "f", "want");
    prints(&src, "n", "(\"region\", \"day\", \"floof_quantitySold\")");
}

#[test]
fn reduce_with_a_lambda_names_the_leaf_reduce() {
    // `g = sales into (region -> day -> sku >< ((a, b) -> a + b) -> quantitySold);`
    // "g::names is ("region", "day", "reduce_quantitySold")".
    let src = with_sales(
        "g = sales into (region -> day -> sku >< ((a, b) -> a + b) -> quantitySold);\n\
         want = { \"east\" -> [5], \"west\" -> [4, 2] };\nn = g::names;\n",
    );
    same(&src, "g", "want");
    prints(&src, "n", "(\"region\", \"day\", \"reduce_quantitySold\")");
}

#[test]
fn two_reductions_derive_names_from_the_inside_out() {
    // "`sales into (region -> day >< (+) -> sku >< (+) -> quantitySold)` names its leaf
    // `sum_sum_quantitySold`". The values: east 5, west 3 + 1 + 2 = 6.
    let src = with_sales(
        "x = sales into (region -> day >< (+) -> sku >< (+) -> quantitySold);\n\
         want = { \"east\" -> 5, \"west\" -> 6 };\nn = x::names;\n",
    );
    same(&src, "x", "want");
    prints(&src, "n", "(\"region\", \"sum_sum_quantitySold\")");
}

#[test]
fn reduce_at_the_outermost_level() {
    // sec:remap_law: `><` may stand at any level; folding every level of `sales` sums all
    // its values, 5 + 3 + 1 + 2 = 11.
    let src =
        with_sales("x = sales into (region >< (+) -> day >< (+) -> sku >< (+) -> quantitySold);\n");
    prints(&src, "x", "11");
}

#[test]
fn the_join_lines_example() {
    // "Joins by name": `lines = (sales, prices) into (region -> day -> sku -> (line:
    // (quantitySold, price)));` with its value and `lines::names is ("region", "day",
    // "sku", "line")`.
    let src = with_sales(
        "prices: (sku: Utf8String) ->? f64 with names(\"sku\", \"price\") = { \"A12\" -> 2.5, \"B7\" -> 4.0 };\n\
         lines = (sales, prices) into (region -> day -> sku -> (line: (quantitySold, price)));\n\
         want = { \"east\" -> [{ \"B7\" -> (5, 4.0) }], \"west\" -> [{ \"A12\" -> (3, 2.5), \"B7\" -> (1, 4.0) }, { \"A12\" -> (2, 2.5) }] };\n\
         n = lines::names;\n",
    );
    same(&src, "lines", "want");
    prints(&src, "n", "(\"region\", \"day\", \"sku\", \"line\")");
}

// ---- Named slicing (sec:level_names, "Named slicing"; step L8.2c) ----

#[test]
fn slice_at_an_inner_named_level() {
    // `a12 = sales[sku: "A12"];` "a12 is { "east" -> [#notFound], "west" -> [3, 2] }; a12::names
    // is ("region", "day", "quantitySold")".
    let src = with_sales(
        "a12 = sales[sku: \"A12\"];\nwant = { \"east\" -> [#notFound], \"west\" -> [3, 2] };\nn = a12::names;\n",
    );
    same(&src, "a12", "want");
    prints(&src, "n", "(\"region\", \"day\", \"quantitySold\")");
}

#[test]
fn slice_at_the_outermost_level_is_a_lookup() {
    // "at the outermost level `sales[region: "west"]` is `sales["west"]`".
    let src = with_sales("x = sales[region: \"west\"];\ny = sales[\"west\"];\n");
    same(&src, "x", "y");
}

#[test]
fn slice_a_list_level_misses_with_out_of_bounds() {
    // "`sales[day: 1]` is `{ "east" -> #outOfBounds, "west" -> { "A12" -> 2 } }`".
    let src = with_sales(
        "x = sales[day: 1];\nwant = { \"east\" -> #outOfBounds, \"west\" -> { \"A12\" -> 2 } };\n",
    );
    same(&src, "x", "want");
}

#[test]
fn slice_at_day_zero() {
    // sec:diagnostics, the worked example's fixes: "x = sales[day: 0]; x is { "east" -> { "B7"
    // -> 5 }, "west" -> { "A12" -> 3, "B7" -> 1 } }".
    let src = with_sales(
        "x = sales[day: 0];\nwant = { \"east\" -> { \"B7\" -> 5 }, \"west\" -> { \"A12\" -> 3, \"B7\" -> 1 } };\n",
    );
    same(&src, "x", "want");
}

#[test]
fn slice_misses_at_every_place() {
    // The same fixes: "x = sales[sku: "Monday"]; x is { "east" -> [#notFound], "west" ->
    // [#notFound, #notFound] }" and "x = sales[region: "Monday"]; x is #notFound".
    let src = with_sales(
        "x = sales[sku: \"Monday\"];\nwant = { \"east\" -> [#notFound], \"west\" -> [#notFound, #notFound] };\n\
         y = sales[region: \"Monday\"];\n",
    );
    same(&src, "x", "want");
    prints(&src, "y", "#notFound");
}

#[test]
fn slice_by_two_names_in_any_order() {
    // "`sales[sku: "A12", region: "west"]` is `[3, 2]`".
    let src = with_sales("x = sales[sku: \"A12\", region: \"west\"];\nwant = [3, 2];\n");
    same(&src, "x", "want");
}

#[test]
fn slice_by_a_name_the_type_lacks() {
    // "A name that is not a level of the value's static type is an error that lists the levels
    // and their names."
    let src = with_sales("x = sales[store: \"A12\"];\n");
    rejected(&src, &["store", "region", "day", "sku"]);
}

#[test]
fn slice_naming_one_level_twice() {
    // Step L8.2c: "one level named twice, rejected with the levels listed".
    let src = with_sales("x = sales[sku: \"A12\", sku: \"B7\"];\n");
    rejected(&src, &["sku"]);
}

#[test]
fn slice_a_list_level_with_a_string_key() {
    // sec:diagnostics, "A worked example naming a level": the headline and the first fix.
    let src = with_sales("x = sales[day: \"Monday\"];\n");
    rejected(
        &src,
        &[
            "A list level has no string key: `sales[day: \"Monday\" : Utf8String]`. Try `sales[day: 0]` instead.",
            "x = sales[day: 0];",
        ],
    );
}

// ---- Empty levels (sec:remap_law; step EMPTY-level-swap) ----

#[test]
fn an_empty_inner_level_keeps_its_key_under_a_computed_outer_level() {
    // sec:remap_law: "`{"a" -> {}} as (k -> j -> v) into (k.upper -> j -> v)` is `{"A" ->
    // {}}`".
    let src = "m: Utf8String ->? (int ->? int) = { \"a\" -> {} };\n\
               x = m as (k -> j -> v) into (k.upper -> j -> v);\n";
    prints(src, "x", "{\"A\" -> {}}");
}

#[test]
fn a_transpose_drops_an_empty_inner_level() {
    // sec:remap_law: "`{"a" -> {}}` transposed is `{}`".
    let src = "m: Utf8String ->? (int ->? int) = { \"a\" -> {} };\n\
               x = m as (k -> j -> v) into (j -> k -> v);\n";
    prints(src, "x", "{}");
}

#[test]
fn a_rank_over_the_outer_level_ranks_an_empty_entry() {
    // sec:remap_law: "a rank or sort over the outer level ranks `"a"` like any other entry".
    let src = "m: Utf8String ->? (int ->? int) = { \"a\" -> {}, \"b\" -> { 1 -> 2 } };\n\
               x = m as (k -> j -> v) into (asc k -> k -> j -> v);\n\
               want: int ->? (Utf8String ->? (int ->? int)) = { 0 -> { \"a\" -> {} }, 1 -> { \"b\" -> { 1 -> 2 } } };\n";
    same(src, "x", "want");
}
