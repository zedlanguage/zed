//! How the reference programs scale with their input. Each input is built before timing, at n
//! and 8n. Most are linear up to a sort or a tree lookup; the ones that are not name why at their
//! test: the power is what the problem forces, such as a full table in the output, not the
//! algorithm of the corpus program.

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

#[test]
fn union_find_over_a_long_chain() {
    scales("union find", "13", 4000, 1, |n| {
        lines(n, |i| format!("{} {}", i, i + 1)) + &lines(n, |i| format!("? 0 {i}"))
    });
}

/// Memory and time follow the edges and queries, not the node numbers, which here are about
/// 10^13 times the input's length.
#[test]
fn union_find_over_few_edges_among_huge_node_numbers() {
    const STEP: usize = 10_000_000_000_000;
    scales("union find huge numbers", "13", 4000, 1, |n| {
        lines(n, |i| format!("{} {}", i * STEP, (i + 1) * STEP))
            + &lines(n, |i| format!("? 0 {}", i * STEP))
    });
}

/// Checks reference 14 at n and 8n on `input`, after its output at n is checked to be that of
/// the O(n²) form. The merges follow a Delaunay triangulation: O(n log n).
fn clustering_scales(what: &str, n: usize, input: impl Fn(usize) -> String) {
    let small = input(n);
    let differs = super::clustering_differs_from_oracle(&small);
    assert!(differs.is_none(), "{what}: the O(n²) form differs at {n}");
    scales(what, "14", n, 1, input);
}

/// The side of the smallest square grid of at least `n` points.
fn side(n: usize) -> usize {
    (1..).find(|w| w * w >= n).expect("a side")
}

/// Nearly collinear points far apart.
#[test]
fn clustering_of_points_near_a_line() {
    clustering_scales("clustering near a line", 1000, |n| {
        format!("1\n{}", lines(n, |i| format!("{} {}", i * i, i % 3)))
    });
}

/// A grid: every side of every square at one distance, so the label rule orders whole levels.
#[test]
fn clustering_of_a_grid() {
    clustering_scales("clustering grid", 1000, |n| {
        let w = side(n);
        format!(
            "{}\n{}",
            n / 2,
            lines(n, |i| format!("{} {}", i % w, i / w))
        )
    });
}

/// The grid turned by the angle whose cosine is 3/5 and scaled by 5: (3a + 4b, -4a + 3b).
#[test]
fn clustering_of_a_rotated_grid() {
    clustering_scales("clustering rotated grid", 1000, |n| {
        let w = side(n);
        let point = |i: usize| {
            let (a, b) = ((i % w) as i64, (i / w) as i64);
            format!("{} {}", 3 * a + 4 * b, -4 * a + 3 * b)
        };
        format!("{}\n{}", n / 2, lines(n, point))
    });
}

/// splitmix64 of `i`, cut to 30 bits.
fn hash(i: usize) -> u64 {
    let mut z = (i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    (z ^ (z >> 31)) >> 34
}

/// Points in random places: each coordinate a hash of its position in the input.
#[test]
fn clustering_of_random_points() {
    clustering_scales("clustering random", 1000, |n| {
        format!(
            "1\n{}",
            lines(n, |i| format!("{} {}", hash(2 * i + 1), hash(2 * i + 2)))
        )
    });
}

/// Point i is (i mod 3, i mod 2), which fixes i mod 6: six distinct points, each about n/6 times
/// in turn, so all but six points equal an earlier one. Three clusters: the merges join every
/// set of equal points at distance 0, then stop after three of the seven pairs at distance 1.
#[test]
fn clustering_of_many_equal_points() {
    clustering_scales("clustering equal points", 1000, |n| {
        format!("3\n{}", lines(n, |i| format!("{} {}", i % 3, i % 2)))
    });
}

/// Points all on one line, in an order far from sorted: the triangulation is their path.
#[test]
fn clustering_of_points_on_one_line() {
    clustering_scales("clustering on a line", 1000, |n| {
        let point = |i: usize| {
            let x = i * 7919 % n;
            format!("{x} {}", 2 * x)
        };
        format!("1\n{}", lines(n, point))
    });
}

/// Points all on one circle, where every in-circle test of four of them is 0: the first n of the
/// 8192 lattice points of x² + y² = 5 · 13 · 17 · 29 · 37 · 41 · 53 · 61 · 73 · 89 · 97, each a
/// product of one of a ± bi per prime p = a² + b², times a unit.
#[test]
fn clustering_of_points_on_one_circle() {
    let primes = [
        (1, 2),
        (2, 3),
        (1, 4),
        (2, 5),
        (1, 6),
        (4, 5),
        (2, 7),
        (5, 6),
        (3, 8),
        (5, 8),
        (4, 9),
    ];
    let mut zs: Vec<(i64, i64)> = vec![(1, 0)];
    for (a, b) in primes {
        zs = zs
            .iter()
            .flat_map(|&(x, y)| {
                [
                    (x * a - y * b, x * b + y * a),
                    (x * a + y * b, y * a - x * b),
                ]
            })
            .collect();
    }
    let circle: Vec<(i64, i64)> = zs
        .into_iter()
        .flat_map(|(x, y)| [(x, y), (-y, x), (-x, -y), (y, -x)])
        .collect();
    clustering_scales("clustering circle", 1000, |n| {
        let (x, y): (Vec<i64>, Vec<i64>) = circle[..n].iter().copied().unzip();
        format!("1\n{}", lines(n, |i| format!("{} {}", x[i], y[i])))
    });
}

/// Two parabolas facing apart, x = ±(10000 + t²) and y = 5000t: every point is on the hull of its
/// half, so each merge of the triangulation walks long hull chains.
#[test]
fn clustering_of_two_parabolas_facing_apart() {
    clustering_scales("clustering two parabolas", 1000, |n| {
        format!(
            "1\n{}",
            lines(n, |i| {
                let t = (i / 2) as i64 - n as i64 / 4;
                let x = 10_000 + t * t;
                let x = if i % 2 == 0 { -x } else { x };
                format!("{x} {}", 5_000 * t)
            })
        )
    });
}

/// Points (i, i²) and (i, -i²) in turn: two parabolas facing apart, interleaved in the input.
#[test]
fn clustering_of_points_on_two_parabolas_by_turns() {
    clustering_scales("clustering parabolas by turns", 1000, |n| {
        let point = |i: usize| {
            let y = (i * i) as i64;
            format!("{i} {}", if i % 2 == 1 { y } else { -y })
        };
        format!("1\n{}", lines(n, point))
    });
}

/// A coordinate of `chunks` blocks of nine decimal digits, block j the hash of `(seed, j)`: the
/// first blocks do not depend on `chunks`, so with more blocks the points scale up by a power of
/// 10 and move by less than one unit of the shorter ones.
fn wide(seed: usize, chunks: usize) -> String {
    (0..chunks).fold(String::new(), |mut s, j| {
        let block = hash(seed * 64 + j);
        if j == 0 {
            write!(s, "{}", block % 900_000_000 + 100_000_000)
        } else {
            write!(s, "{:09}", block % 1_000_000_000)
        }
        .expect("writing to a String");
        s
    })
}

/// `n` random points whose coordinates have `chunks` blocks of nine digits.
fn wide_random_points(n: usize, chunks: usize) -> String {
    let point = |i: usize| format!("{} {}", wide(2 * i + 1, chunks), wide(2 * i + 2, chunks));
    format!("1\n{}", lines(n, point))
}

/// Random points with coordinates of 72 digits (240 bits): every product and sum in the
/// predicates is several 64-bit words long, and the in-circle determinant up to 4b + 8 = 968 bits
/// (COMPLEXITY F39). At a fixed coordinate size the bound O(L + n log n · M(b)) is O(n log n).
#[test]
fn clustering_of_random_points_with_wide_coordinates() {
    clustering_scales("clustering random wide", 1000, |n| wide_random_points(n, 8));
}

/// The same 1000 random points with coordinates of 36 and of 288 digits (120 and 957 bits, an
/// in-circle determinant of up to 488 and 3836 bits), held to the limit of power 1. At these
/// sizes the cost per number is mostly fixed, so this does not show the cost of num-bigint's
/// products, which larger coordinates reach (COMPLEXITY F39, item BIGINT-fast-mul).
#[test]
fn clustering_of_random_points_at_eight_times_the_coordinate_size() {
    let differs = super::clustering_differs_from_oracle(&wide_random_points(1000, 4));
    assert!(differs.is_none(), "the O(n²) form differs at 36 digits");
    scales("clustering coordinate blocks", "14", 4, 1, |chunks| {
        wide_random_points(1000, chunks)
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
