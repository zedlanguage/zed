//! How the reference programs scale with their input. Each input is built before timing, at n
//! and 8n. Most are linear up to a sort or a tree lookup; the ones that are not name why at their
//! test: the power is what the problem forces, such as a full table in the output or a pair read
//! once, not the algorithm of the corpus program.

use std::fmt::Write;
use std::fs;

use zed_tests::scaling::check_order;

/// A line per `i` in `0..n`.
fn lines(n: usize, line: impl Fn(usize) -> String) -> String {
    (0..n).fold(String::new(), |mut s, i| {
        writeln!(s, "{}", line(i)).expect("writing to a String");
        s
    })
}

/// Checks reference `number` at n and 8n on the input `input` builds for each size.
fn scales(what: &str, number: &str, n: usize, power: u32, input: impl Fn(usize) -> String) {
    let name = what.replace(' ', "_");
    let path = |m: usize| format!("{}/build/ref_{name}_{m}.in", zed_tools::impl_root());
    for m in [n, 8 * n] {
        fs::write(path(m), input(m)).expect("writing an input");
    }
    check_order(what, n, power, |m| {
        let (_, result) = zed_corpus_ref::run(number, &path(m));
        assert_eq!(result, Ok(()), "{what}");
    });
    for m in [n, 8 * n] {
        fs::remove_file(path(m)).expect("removing an input");
    }
}

#[test]
fn word_count_over_many_words() {
    scales("word count", "01", 4000, 1, |n| {
        lines(n, |i| format!("the w{i} Cat"))
    });
}

/// One word as long as the input: a line of the output per length up to it.
#[test]
fn histogram_with_one_long_word_among_short_ones() {
    scales("histogram", "02", 20000, 1, |n| {
        format!("{} {}\n", "x".repeat(n), "a bb ".repeat(n / 5))
    });
}

/// The table of an edit distance has a cell per pair of characters.
#[test]
fn edit_distance_is_quadratic_in_the_word_length() {
    scales("edit distance", "03", 300, 2, |n| {
        format!("{} {}\n", "ab".repeat(n / 2), "ba".repeat(n / 2))
    });
}

#[test]
fn running_variance_of_a_long_series() {
    scales("running variance", "04", 3000, 1, |n| {
        lines(n, |i| format!("{}.5e{}", i % 97, i as i64 % 40 - 20))
    });
}

#[test]
fn max_prefix_sum_of_a_long_series() {
    scales("max prefix sum", "05", 8000, 1, |n| {
        lines(n, |i| format!("{}", (i as i64 * 7919) % 2001 - 1000))
    });
}

/// A k by k product has k³ terms.
#[test]
fn matrix_multiply_is_cubic_in_the_side() {
    scales("matrix multiply", "06", 12, 3, |k| {
        let cells: Vec<String> = (0..k).map(|j| format!("{}.5", j % 7)).collect();
        let row = cells.join(" ") + "\n";
        format!("{k} {k} {k}\n{}", row.repeat(2 * k))
    });
}

#[test]
fn json_parser_on_deep_nesting() {
    scales("json depth", "07", 20000, 1, |n| {
        format!("{}1{}\n", "[".repeat(n), "]".repeat(n))
    });
}

#[test]
fn json_parser_on_deep_objects() {
    scales("json object depth", "07", 20000, 1, |n| {
        format!("{}1{}\n", "{\"a\": ".repeat(n), "}".repeat(n))
    });
}

#[test]
fn json_parser_on_a_wide_list() {
    scales("json width", "07", 20000, 1, |n| {
        format!("[{}true]\n", "\"a b\" , ".repeat(n))
    });
}

#[test]
fn json_parser_on_a_failure_at_the_end_of_a_deep_list() {
    scales("json failure", "07", 20000, 1, |n| {
        format!("{}1,\n", "[".repeat(n))
    });
}

#[test]
fn percent_decoding_of_a_long_line() {
    scales("percent decoding", "08", 10000, 1, |n| {
        format!("{}\n", "caf%C3%A9%20".repeat(n / 12))
    });
}

#[test]
fn canonical_equality_over_many_lines() {
    scales("canonical equality", "09", 5000, 1, |n| {
        lines(n, |i| format!("New-York {i} | new york {i}"))
    });
}

#[test]
fn regex_matcher_over_many_lines() {
    scales("regex lines", "10", 3000, 1, |n| {
        lines(n, |i| format!("{:02}:{:02}", i % 30, i % 70))
    });
}

#[test]
fn regex_matcher_on_a_long_line() {
    scales("regex length", "10", 3000, 1, |n| {
        format!("{}\n", "2".repeat(n))
    });
}

#[test]
fn csv_split_of_a_long_line() {
    scales("csv", "11", 20000, 1, |n| {
        format!("{}\n", "\"x,y\",z,".repeat(n / 8))
    });
}

/// The corpus program fills a CYK table; the reference prints the same answer from one pass.
#[test]
fn balanced_brackets_of_a_long_line() {
    scales("balanced brackets", "12", 20000, 1, |n| {
        format!("{}\n", "()".repeat(n / 2))
    });
}

#[test]
fn balanced_brackets_of_a_deep_line() {
    scales("deep brackets", "12", 20000, 1, |n| {
        format!("{}{}\n", "(".repeat(n / 2), ")".repeat(n / 2))
    });
}

/// The node count comes from the largest id on an edge, so the input is sized by it.
#[test]
fn union_find_over_a_long_chain() {
    scales("union find", "13", 4000, 1, |n| {
        lines(n, |i| format!("{} {}", i, i + 1)) + &lines(n, |i| format!("? 0 {i}"))
    });
}

/// Any pair of points may decide a merge, so all n(n-1)/2 distances are read. The nearest cluster
/// is kept by key, so the merges cost no more than that.
#[test]
fn clustering_is_quadratic_in_the_number_of_points() {
    scales("clustering", "14", 200, 2, |n| {
        format!("1\n{}", lines(n, |i| format!("{} {}", i * i, i % 3)))
    });
}

/// Every edit prints every cell, so the output is quadratic.
#[test]
fn spreadsheet_prints_every_cell_after_every_edit() {
    scales("spreadsheet", "15", 200, 2, |n| {
        lines(n, |i| match i {
            0 => "c0 = 1".to_string(),
            _ => format!("c{i} = c{}+1", i - 1),
        })
    });
}

/// A formula is read once, so n edits of a cell it does not name cost nothing for its n terms.
#[test]
fn spreadsheet_edits_of_a_cell_beside_one_long_formula() {
    scales("spreadsheet long formula", "15", 4000, 1, |n| {
        let edits = lines(n, |i| format!("b = {i}"));
        format!("a = {}\n{edits}", vec!["1"; n].join("+"))
    });
}

/// A formula keeps each name once with its multiplicity, so its n terms are one dependency edge.
#[test]
fn spreadsheet_edits_of_the_cell_a_long_formula_repeats() {
    scales("spreadsheet repeated term", "15", 4000, 1, |n| {
        let edits = lines(n, |i| format!("b = {i}"));
        format!("a = {}\n{edits}", vec!["b"; n].join("+"))
    });
}

/// All n cells depend on the edited one, so each edit costs one visit per dependency edge, and it
/// changes every value on the line it prints. n edits must print n² values, so no method does
/// better than this power.
#[test]
fn spreadsheet_edits_of_a_cell_that_every_cell_depends_on() {
    scales("spreadsheet all depend", "15", 200, 2, |n| {
        let cells = lines(n, |i| format!("c{i} = s+1"));
        format!("{cells}{}", lines(n, |i| format!("s = {i}")))
    });
}

#[test]
fn game_tick_with_many_players() {
    scales("game players", "16", 10000, 1, |n| {
        lines(n, |i| format!("0 p{i} 3"))
    });
}

#[test]
fn game_tick_over_many_ticks() {
    scales("game ticks", "16", 10000, 1, |n| {
        lines(n, |i| format!("{i} ann 1"))
    });
}

#[test]
fn sensor_pipeline_over_many_readings() {
    scales("sensor pipeline", "17", 10000, 1, |n| {
        lines(n, |i| format!("{i} temp {}", i % 30))
    });
}

#[test]
fn windowed_word_frequency_over_many_lines() {
    scales("word frequency", "18", 10000, 1, |n| {
        lines(n, |i| format!("{i} w{} Hello", i % 1000))
    });
}

#[test]
fn bank_ledger_over_many_transactions() {
    scales("bank ledger", "19", 5000, 1, |n| {
        lines(n, |i| format!("open a{i}")) + &lines(n, |i| format!("dep a{i} {i}"))
    });
}

#[test]
fn taint_escaping_of_many_lines() {
    scales("taint", "20", 10000, 1, |n| {
        lines(n, |_| "<b>fish & chips</b>".to_string())
    });
}

#[test]
fn stats_over_many_rows() {
    scales("stats", "21", 5000, 1, |n| {
        lines(n, |i| format!("{}.5 {}", i % 100, i % 7))
    });
}

#[test]
fn top_k_over_many_scores() {
    scales("top k", "22", 10000, 1, |n| {
        lines(n, |i| format!("p{i} {}", (i * 7919) % 1009))
    });
}

#[test]
fn join_zoo_over_many_keys() {
    scales("join zoo", "23", 5000, 1, |n| {
        lines(n, |i| format!("O {i} {i}")) + &lines(n, |i| format!("P {} 1", 2 * i))
    });
}

#[test]
fn weighted_pick_over_many_queries() {
    scales("weighted pick", "24", 5000, 1, |n| {
        let weights: Vec<String> = (0..n).map(|i| (i % 5).to_string()).collect();
        weights.join(" ") + "\n" + &lines(n, |i| i.to_string())
    });
}

#[test]
fn autocorrelation_of_a_long_series() {
    scales("autocorrelation", "25", 8000, 1, |n| {
        let xs: Vec<String> = (0..n).map(|i| (i % 19).to_string()).collect();
        xs.join(" ") + "\n"
    });
}

/// The number of steps is a value in the input, not a length; this is the length.
#[test]
fn heat_stencil_over_a_long_row() {
    scales("heat stencil", "26", 5000, 1, |n| {
        let cells: Vec<String> = (0..n).map(|i| (i % 400).to_string()).collect();
        format!("3\n{}\n", cells.join(" "))
    });
}

#[test]
fn parent_chain_of_one_long_chain() {
    scales("parent chain", "27", 10000, 1, |n| {
        format!("n0 -\n{}", lines(n, |i| format!("n{} n{i}", i + 1)))
    });
}

#[test]
fn precedence_climbing_of_a_long_expression() {
    scales("precedence climbing", "28", 10000, 1, |n| {
        format!("{}1\n", "2 ^ 3 + ".repeat(n / 8))
    });
}

#[test]
fn late_dedup_over_many_readings() {
    scales("late dedup", "29", 10000, 1, |n| {
        lines(n, |i| format!("k{} {i} {i}", i % 100))
    });
}

#[test]
fn client_server_over_many_requests() {
    scales("client server", "30", 5000, 1, |n| {
        lines(n, |i| format!("buy item{} {}", i % 50, i % 9))
    });
}

#[test]
fn typechecker_over_a_long_chain_of_declarations() {
    scales("typechecker chain", "31", 5000, 1, |n| {
        lines(n, |i| match i {
            0 => "d0 = 1".to_string(),
            _ => format!("d{i} = d{} 1 +", i - 1),
        })
    });
}

/// Declared last to first, the order that takes the most rounds from all-unknown.
#[test]
fn typechecker_over_a_chain_declared_backward() {
    scales("typechecker backward", "31", 5000, 1, |n| {
        lines(n, |i| match n - 1 - i {
            0 => "d0 = 1".to_string(),
            k => format!("d{k} = d{} 1 +", k - 1),
        })
    });
}

#[test]
fn typechecker_on_one_long_expression() {
    scales("typechecker length", "31", 20000, 1, |n| {
        format!("x = 1{}\n", " 1 +".repeat(n / 4))
    });
}

#[test]
fn typechecker_on_a_long_cycle() {
    scales("typechecker cycle", "31", 5000, 1, |n| {
        lines(n, |i| format!("d{i} = d{} 1 +", (i + 1) % n))
    });
}
