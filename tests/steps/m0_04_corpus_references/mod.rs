//! Step M0.4: the reference programs of the corpus. Each `.out` file is what the reference
//! program of its number prints on the `.in` file of the same name. The references compute the
//! outputs without the compiler, so the corpus tests the compiler rather than repeating it.

mod int_reading;
mod lattice_circles;
mod p14_oracle;
mod scaling;

use std::fs;

use zed_corpus_ref::zedrt;

/// The corpus directory.
fn corpus() -> String {
    format!("{}/zed/corpus", zed_tools::impl_root())
}

/// The base names of the corpus's `.in` files, sorted.
fn inputs() -> Vec<String> {
    let mut names: Vec<String> = fs::read_dir(corpus())
        .expect("the corpus is readable")
        .map(|e| e.expect("a directory entry").file_name())
        .map(|n| n.into_string().expect("a UTF-8 file name"))
        .filter_map(|n| n.strip_suffix(".in").map(str::to_string))
        .collect();
    names.sort();
    names
}

#[test]
fn every_output_is_what_its_reference_program_prints() {
    let names = inputs();
    assert_eq!(names.len(), 31, "{names:?}");
    for base in &names {
        let (out, result) = zed_corpus_ref::run(&base[..2], &format!("{}/{base}.in", corpus()));
        assert_eq!(result, Ok(()), "{base}");
        let want = fs::read_to_string(format!("{}/{base}.out", corpus())).expect("an output");
        assert!(out == want, "{base}: the reference and the .out differ");
    }
}

#[test]
fn a_number_with_no_program_is_an_error() {
    for number in ["00", "32", "xy"] {
        let (out, result) = zed_corpus_ref::run(number, "/dev/null");
        assert_eq!(out, "");
        assert_eq!(result, Err(format!("no reference program {number}")));
    }
}

#[test]
fn a_missing_input_is_an_error() {
    let (out, result) = zed_corpus_ref::run("01", "/no/such/input");
    assert_eq!(out, "");
    assert!(result.expect_err("no input").contains("/no/such/input"));
}

#[test]
fn an_input_that_is_not_utf8_is_an_error_and_prints_nothing() {
    let path = format!("{}/build/not_utf8.in", zed_tools::impl_root());
    fs::write(&path, b"caf\xe9\n").expect("writing a test input");
    let (out, result) = zed_corpus_ref::run("01", &path);
    fs::remove_file(&path).expect("removing a test input");
    assert_eq!(out, "");
    assert!(result.is_err());
}

#[test]
fn floats_print_as_the_compiler_prints_them() {
    let cases = [
        (1.0, "1.0"),
        (0.1, "0.1"),
        (-0.0, "-0.0"),
        (1e21, "1.0e21"),
        (1e20, "100000000000000000000.0"),
        (1.5e-7, "1.5e-7"),
        (1e-6, "0.000001"),
        (123.456, "123.456"),
        (2.5e-5, "0.000025"),
        // The value is exactly 1666666666666669.25: .2 and .3 both read back and are equally near,
        // and the larger magnitude is printed.
        (6666666666666677.0 / 4.0, "1666666666666669.3"),
        (-6666666666666677.0 / 4.0, "-1666666666666669.3"),
    ];
    for (x, want) in cases {
        assert_eq!(zedrt::fmt_float(x), want);
    }
    assert_eq!(zedrt::fmt_float(f64::INFINITY), "inf");
    assert_eq!(zedrt::fmt_float(f64::NAN), "nan");
}

#[test]
fn the_references_do_not_depend_on_the_compiler() {
    let manifest = fs::read_to_string(format!("{}/ref/Cargo.toml", corpus())).expect("a manifest");
    for crate_name in ["zedc", "zed-kernel", "zed-native", "zed-rt", "zed-tools"] {
        assert!(
            !manifest.contains(crate_name),
            "the references use {crate_name}"
        );
    }
}

/// The output of reference `number` on `input`, which `name` keeps apart from other tests.
fn on_text(number: &str, name: &str, input: &str) -> (String, Result<(), String>) {
    let path = format!("{}/build/ref_{name}.in", zed_tools::impl_root());
    fs::write(&path, input).expect("writing a test input");
    let result = zed_corpus_ref::run(number, &path);
    fs::remove_file(&path).expect("removing a test input");
    result
}

#[test]
fn a_json_document_may_nest_as_deeply_as_its_line_is_long() {
    let depth = 2_000_000;
    let nested = format!("{}1{}\n", "[".repeat(depth), "]".repeat(depth));
    assert_eq!(on_text("07", "json_deep", &nested), (nested, Ok(())));
}

#[test]
fn a_json_failure_deep_in_a_list_reports_the_farthest_position() {
    let cases = [
        ("[[[1,]]]\n", "error at 5\n"),
        ("[1 2]\n", "error at 3\n"),
        ("{\"a\" 1}\n", "error at 5\n"),
        ("[ ] x\n", "error at 3\n"),
        ("[1.x]\n", "error at 3\n"),
        ("[]\n", "[]\n"),
        ("[ { } , [ ] ]\n", "[{},[]]\n"),
    ];
    for (input, want) in cases {
        let (out, result) = on_text("07", "json_failure", input);
        assert_eq!((out.as_str(), result), (want, Ok(())), "{input}");
    }
}

#[test]
fn a_spreadsheet_cell_may_depend_on_a_chain_as_long_as_the_sheet() {
    // Every edit prints every cell, so this is as long as a chain can be and stay a small test.
    let n = 3000;
    let mut input: String = (1..n)
        .rev()
        .map(|i| format!("c{i} = c{}+1\n", i - 1))
        .collect();
    input.push_str("c0 = 1\n");
    let (out, result) = on_text("15", "sheet_chain", &input);
    assert_eq!(result, Ok(()));
    let last = out.lines().last().expect("a line per edit");
    assert!(last.contains(&format!(" c{}={n}", n - 1)), "{last}");
}

#[test]
fn a_spreadsheet_cell_that_depends_on_itself_is_an_error() {
    let (_, result) = on_text("15", "sheet_cycle", "a = b+1\nb = a+1\n");
    assert_eq!(result, Err("the cell a depends on itself".to_string()));
}

#[test]
fn a_type_may_depend_on_a_chain_as_long_as_the_program() {
    let n = 200_000;
    let mut input: String = (1..n)
        .rev()
        .map(|i| format!("d{i} = d{} 1 +\n", i - 1))
        .collect();
    input.push_str("d0 = 1\n");
    let (out, result) = on_text("31", "type_chain", &input);
    assert_eq!(result, Ok(()));
    assert_eq!(out.lines().count(), n);
    assert!(out.lines().all(|l| l.ends_with(": int")));
}

#[test]
fn a_type_error_spreads_through_a_cycle_and_past_it() {
    let input = "a = b 1 true + +\nb = a 1 +\nc = b\nd = e\ne = d\n";
    let (out, result) = on_text("31", "type_cycle", input);
    assert_eq!(result, Ok(()));
    let want = "a : error\nb : error\nc : error\nd : unknown\ne : unknown\n\
                line 4: d is cyclic\nline 5: e is cyclic\n";
    assert_eq!(out, want);
}

#[test]
fn a_parent_chain_stops_at_the_first_node_it_has_seen() {
    let (out, result) = on_text("27", "chain_cycle", "a -\nb a\nc d\nd c\n");
    assert_eq!(out, "a a 0\nb a 1\n");
    assert_eq!(result, Err("the chain of c has a cycle".to_string()));
    let (out, result) = on_text("27", "chain_self", "x x\n");
    assert_eq!(out, "");
    assert_eq!(result, Err("the chain of x has a cycle".to_string()));
}

#[test]
fn a_parent_outside_the_children_is_a_root() {
    let (out, result) = on_text("27", "chain_root", "b a\nc b\n");
    assert_eq!((out.as_str(), result), ("b a 1\nc a 2\n", Ok(())));
}

#[test]
fn a_running_sum_stays_exact_where_doubles_alone_would_lose_it() {
    // 1e308 + 1e308 overflows a double, and fsum says so at that line, after the lines before it.
    let (out, result) = on_text("04", "sum_overflow", "1e308\n1e308\n");
    assert_eq!(result, Err("intermediate overflow in fsum".to_string()));
    assert_eq!(out.lines().count(), 1);
    // A value lost beside a large one by plain addition survives when the large one cancels.
    let (out, result) = on_text("04", "sum_exact", "1e100\n1\n-1e100\n");
    assert_eq!(result, Ok(()));
    let third = out.lines().nth(2).expect("three lines");
    assert!(third.starts_with("-1.0e100 0.333"), "{third}");
    // inf and -inf together are an error, at the line that brings the second.
    let (out, result) = on_text("04", "sum_inf", "inf\n-inf\n");
    assert_eq!(result, Err("-inf + inf in fsum".to_string()));
    assert_eq!(out.lines().count(), 1);
}

#[test]
fn a_histogram_counts_each_length_up_to_the_longest() {
    let (out, result) = on_text("02", "histogram", "a ccc a\n");
    assert_eq!((out.as_str(), result), ("1 2 2\n2 0 0\n3 1 1\n", Ok(())));
    let (out, result) = on_text("02", "histogram_none", "");
    assert_eq!((out.as_str(), result), ("", Ok(())));
}

#[test]
fn a_matrix_header_of_huge_sizes_reserves_nothing() {
    for header in ["1 1 100000000000000", "1 100000000000000 1"] {
        let input = format!("{header}\n1\n1\n");
        let (out, result) = on_text("06", "matrix_huge", &input);
        assert_eq!(out, "", "{header}");
        assert!(
            result.is_err_and(|e| e.contains("out of range")),
            "{header}"
        );
    }
}

/// Whether `s`, of brackets alone, is balanced and not empty, by the definition.
fn is_balanced(s: &[u8]) -> bool {
    let mut depth = 0i32;
    for &c in s {
        depth += if c == b'(' { 1 } else { -1 };
        if depth < 0 {
            return false;
        }
    }
    depth == 0 && !s.is_empty()
}

#[test]
fn balanced_brackets_agree_with_the_definition_on_every_short_line() {
    let line = |bits: u32, len: u32| -> String {
        let bit = |i: u32| if bits >> i & 1 == 0 { '(' } else { ')' };
        (0..len).map(bit).collect()
    };
    let all: Vec<String> = (1..=10)
        .flat_map(|len| (0..1u32 << len).map(move |bits| line(bits, len)))
        .collect();
    let (out, result) = on_text("12", "brackets_all", &(all.join("\n") + "\n"));
    assert_eq!(result, Ok(()));
    let want: Vec<String> = all
        .iter()
        .map(|l| {
            let b = l.as_bytes();
            let count = (0..b.len())
                .flat_map(|i| (i + 1..=b.len()).map(move |j| (i, j)))
                .filter(|&(i, j)| is_balanced(&b[i..j]))
                .count();
            let verdict = if is_balanced(b) {
                "balanced"
            } else {
                "unbalanced"
            };
            format!("{verdict} {count} {l}\n")
        })
        .collect();
    assert_eq!(out, want.concat());
}

#[test]
fn balanced_brackets_of_a_line_with_other_characters() {
    let (out, result) = on_text("12", "brackets_other", "(a)()\n\n");
    assert_eq!(
        (out.as_str(), result),
        ("unbalanced 1 (a)()\nunbalanced 0 \n", Ok(()))
    );
}

#[test]
fn a_two_node_edge_with_a_huge_number_counts_the_nodes_between() {
    let (out, result) = on_text("13", "uf_huge", "10000000000000 1\n");
    assert_eq!(result, Ok(()));
    assert_eq!(out, "components 10000000000000\n");
}

#[test]
fn node_numbers_may_be_larger_than_any_machine_word() {
    let big = "1000000000000000000000000000000";
    let input = format!("{big} 1\n? {big} 1\n? {big} 0\n");
    let (out, result) = on_text("13", "uf_word", &input);
    assert_eq!(result, Ok(()));
    let want = format!("{big} 1 yes\n{big} 0 no\ncomponents {big}\n");
    assert_eq!(out, want);
}

/// Between and above the numbers on the edges, a node is alone without being stored.
#[test]
fn nodes_on_no_edge_are_alone_among_huge_numbers() {
    let input = "10000000000000 1\n\
                 ? 5 6\n? 5 5\n? 5 1\n\
                 ? 20000000000000 20000000000000\n? 20000000000000 1\n";
    let (out, result) = on_text("13", "uf_alone", input);
    assert_eq!(result, Ok(()));
    let want = "5 6 no\n5 5 yes\n5 1 no\n\
                20000000000000 20000000000000 yes\n20000000000000 1 no\n\
                components 10000000000000\n";
    assert_eq!(out, want);
}

/// The node count is 10^13 + 1, so -1 is the largest node, -10^13 is node 1 and -(10^13 + 1) is
/// node 0.
#[test]
fn a_negative_node_counts_from_the_end_of_a_huge_range() {
    let input = "10000000000000 1\n\
                 ? -1 1\n? -10000000000000 1\n? -10000000000001 0\n? -2 1\n";
    let (out, result) = on_text("13", "uf_negative", input);
    assert_eq!(result, Ok(()));
    let want = "-1 1 yes\n-10000000000000 1 yes\n-10000000000001 0 yes\n-2 1 no\n\
                components 10000000000000\n";
    assert_eq!(out, want);
}

#[test]
fn a_negative_node_below_the_range_is_an_error() {
    let input = "10000000000000 1\n? 1 1\n? -10000000000002 1\n";
    let (out, result) = on_text("13", "uf_below", input);
    assert_eq!(out, "1 1 yes\n");
    assert_eq!(result, Err("node -10000000000002 is out of range".into()));
    let (out, result) = on_text("13", "uf_edge", "-5 1\n? 0 0\n");
    assert_eq!(out, "");
    assert_eq!(result, Err("node -5 is out of range".into()));
}

#[test]
fn a_negative_node_on_an_edge_names_the_same_node_as_its_positive() {
    let (out, result) = on_text("13", "uf_same", "-1 3\n? 3 3\n");
    assert_eq!(result, Ok(()));
    assert_eq!(out, "3 3 yes\ncomponents 4\n");
}

#[test]
fn no_edges_mean_no_nodes_in_range() {
    let (out, result) = on_text("13", "uf_empty", "? 2 2\n? 2 3\n");
    assert_eq!(result, Ok(()));
    assert_eq!(out, "2 2 yes\n2 3 no\ncomponents 0\n");
    let (out, result) = on_text("13", "uf_empty_negative", "? -1 2\n");
    assert_eq!(out, "");
    assert_eq!(result, Err("node -1 is out of range".into()));
}

/// A table of a label per node, relabeled at each edge, on small graphs of a fixed random sequence.
#[test]
fn union_find_agrees_with_a_table_of_labels_on_small_graphs() {
    let mut state: u64 = 0x2545_f491_4f6c_dd1d;
    let mut next = |below: u64| {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (state >> 33) % below
    };
    for round in 0..500 {
        let span = 1 + next(12);
        let lines = (0..1 + next(8)).map(|_| {
            let (a, b) = (next(span) as i64, next(span) as i64);
            (a, b)
        });
        let edges: Vec<(i64, i64)> = lines.collect();
        let count = 1 + edges.iter().map(|e| e.0.max(e.1)).max().expect("an edge");
        let mut label: Vec<i64> = (0..count).collect();
        // A loop on the largest node fixes the count, whatever form the other edges take.
        let mut input = format!("{0} {0}\n", count - 1);
        for &(a, b) in &edges {
            // Half of the edges name a node by its negative form.
            let shown = if next(2) == 0 { a } else { a - count };
            input += &format!("{shown} {b}\n");
            let (from, to) = (label[a as usize], label[b as usize]);
            label
                .iter_mut()
                .filter(|l| **l == from)
                .for_each(|l| *l = to);
        }
        let mut want = String::new();
        for _ in 0..4 {
            let (a, b) = (next(span + 2) as i64, next(span + 2) as i64);
            input += &format!("? {a} {b}\n");
            let same = a == b || a < count && b < count && label[a as usize] == label[b as usize];
            want += &format!("{a} {b} {}\n", if same { "yes" } else { "no" });
        }
        let mut roots = label.clone();
        roots.sort_unstable();
        roots.dedup();
        want += &format!("components {}\n", roots.len());
        let (out, result) = on_text("13", "uf_table", &input);
        assert_eq!(result, Ok(()), "round {round}: {input}");
        assert_eq!(out, want, "round {round}: {input}");
    }
}

#[test]
fn clustering_breaks_ties_by_label() {
    let input = "2\n0 0\n1 0\n0 1\n1 1\n";
    let (out, result) = on_text("14", "cluster_ties", input);
    assert_eq!(result, Ok(()));
    assert_eq!(out, "0: 0 1 2\n3: 3\n");
}

/// All three pairs of neighbors are at distance 1. Merging 3 into 0 makes the pair of points 3
/// and 2 one of clusters 0 and 2, which then comes before the pair of 1 and 2: the key reads the
/// labels the clusters have now.
#[test]
fn clustering_ties_use_current_cluster_labels() {
    let (out, result) = on_text("14", "cluster_current_labels", "2\n0 0\n3 0\n2 0\n1 0\n");
    assert_eq!((out.as_str(), result), ("0: 0 2 3\n1: 1\n", Ok(())));
}

/// Points 3 and 4 are equal and join first, and 0 takes them at distance 1. At distance 2 the
/// pairs of that cluster with point 2 and of point 1 with point 2 tie, and the cluster goes by
/// its least point 0, so it takes 2 before 1 can. Labeled by the root of its union-find tree,
/// point 3, it would come after 1.
#[test]
fn clustering_start_order_uses_least_label() {
    let input = "2\n0 1\n2 2\n2 0\n0 0\n0 0\n";
    let (out, result) = on_text("14", "cluster_start_order", input);
    assert_eq!((out.as_str(), result), ("0: 0 2 3 4\n1: 1\n", Ok(())));
}

/// What each count of points and clusters gives: a merge reads both coordinates of every point
/// first, and a merge past one cluster is an error.
#[test]
fn clustering_errors_by_the_count_of_points_and_clusters() {
    let none = "min() of no pairs";
    let cases: [(&str, &str, Result<(), &str>); 12] = [
        ("0\n", "", Ok(())),
        ("3\n", "", Ok(())),
        ("-1\n", "", Err(none)),
        ("1\n7\n", "0: 0\n", Ok(())),
        ("0\n7\n", "", Err(none)),
        ("-5\n7 1\n", "", Err(none)),
        ("2\n7\n8\n", "0: 0\n1: 1\n", Ok(())),
        ("1\n0 0\n7\n", "", Err("index 1 out of range 0..1")),
        ("1\n0\n7 1\n", "", Err("index 1 out of range 0..1")),
        ("0\n0 0\n1 1\n", "", Err(none)),
        ("0\n0 0\n1\n", "", Err("index 1 out of range 0..1")),
        ("1\n0 0\n1 1\n", "0: 0 1\n", Ok(())),
    ];
    for (input, want_out, want) in cases {
        let (out, result) = cluster_text(input);
        assert_eq!(
            (out.as_str(), result),
            (want_out, want.map_err(str::to_string)),
            "{input:?}"
        );
    }
}

/// The lines of `text` as the references read a file of it.
fn input_lines(text: &str) -> Vec<String> {
    if text.is_empty() {
        return Vec::new();
    }
    let body = text.strip_suffix('\n').unwrap_or(text);
    body.split('\n').map(String::from).collect()
}

/// Reference 14's output and result on `text`, read as a file of it.
fn cluster_text(text: &str) -> (String, Result<(), String>) {
    let run = zed_corpus_ref::program("14").expect("reference 14");
    let mut out = String::new();
    let result = run(&input_lines(text), &mut out);
    (out, result)
}

/// The input `text` if reference 14 and its O(n²) form give it different outputs or results.
fn clustering_differs_from_oracle(text: &str) -> Option<String> {
    let mut out = String::new();
    let result = p14_oracle::run(&input_lines(text), &mut out);
    (cluster_text(text) != (out, result)).then(|| text.to_string())
}

/// Counts the inputs on which reference 14 and its O(n²) form differ, and shows the first.
fn count_differences(inputs: impl Iterator<Item = String>) -> (usize, usize, Option<String>) {
    let (mut seen, mut differ, mut first) = (0, 0, None);
    for text in inputs {
        seen += 1;
        if let Some(text) = clustering_differs_from_oracle(&text) {
            differ += 1;
            first.get_or_insert(text);
        }
    }
    (seen, differ, first)
}

/// Every sequence of up to 5 points of the 3 by 3 grid, points repeated or not, and every count
/// of clusters from -1 to n + 1. A sequence is a set in one order, and every order of every set
/// is here, so this also checks that reordering the input lines renames the clusters as the
/// O(n²) form does.
#[test]
fn clustering_agrees_with_its_quadratic_form_on_every_small_grid_input() {
    let grid: Vec<String> = (0..9).map(|c| format!("{} {}\n", c % 3, c / 3)).collect();
    let mut inputs = Vec::new();
    let mut points = vec![String::new()];
    for n in 0..=5 {
        for body in &points {
            for k in -1..=n + 1 {
                inputs.push(format!("{k}\n{body}"));
            }
        }
        points = points
            .iter()
            .flat_map(|body| grid.iter().map(move |p| format!("{body}{p}")))
            .collect();
    }
    let (seen, differ, first) = count_differences(inputs.into_iter());
    assert_eq!(seen, 523_137);
    assert_eq!((differ, first), (0, None), "of {seen} inputs");
}

/// splitmix64: the `i`th number of the sequence that starts at `seed`.
fn splitmix(seed: u64, i: u64) -> u64 {
    let mut z = seed.wrapping_add(i.wrapping_mul(0x9E37_79B9_7F4A_7C15));
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Random sets of up to 40 points: coordinates from ranges of 3, 10 and 1000 values, which give
/// equal points and equal distances often, and from 2^40 values times 10^20, which needs more
/// than 64 bits; a count of clusters from -1 to n + 1 at random.
#[test]
fn clustering_agrees_with_its_quadratic_form_on_random_inputs() {
    let mut inputs = Vec::new();
    for case in 0..6000u64 {
        let draw = |i: u64| splitmix(case, i);
        let n = draw(0) % 41;
        let (range, scale) = [
            (3, ""),
            (10, ""),
            (1000, ""),
            (1 << 40, "00000000000000000000"),
        ][(draw(1) % 4) as usize];
        let coordinate = |i: u64| {
            let c = (draw(i) % range) as i64 - (range / 2) as i64;
            if c == 0 {
                "0".to_string()
            } else {
                format!("{c}{scale}")
            }
        };
        let body: String = (0..n)
            .map(|i| format!("{} {}\n", coordinate(2 + 2 * i), coordinate(3 + 2 * i)))
            .collect();
        let k = (draw(100) % (n + 3)) as i64 - 1;
        inputs.push(format!("{k}\n{body}"));
    }
    let (seen, differ, first) = count_differences(inputs.into_iter());
    assert_eq!((differ, first), (0, None), "of {seen} inputs");
}

/// Malformed and unusual inputs give what the O(n²) form gives, errors with its messages.
#[test]
fn clustering_agrees_with_its_quadratic_form_on_malformed_inputs() {
    let inputs = [
        "",
        "2",
        "two\n0 0\n",
        "1.5\n0 0\n",
        "1\n0 0\n1\n",
        "1\n0 0\n1 x\n",
        "1\n0 0\nx 1\n",
        "1\n0 0\n1.5 2\n",
        "1\n0  0\n1 1\n",
        "1\n0 0\n\n",
        "1\n0 0 9\n1 1\n",
        "2\n0 0\n1\n",
        "3\n0 0\n1\n",
        "1\n0\n1\n2\n",
        "-1000000000000000000000000\n0 0\n1 1\n",
    ];
    let (seen, differ, first) = count_differences(inputs.into_iter().map(String::from));
    assert_eq!((seen, differ, first), (inputs.len(), 0, None));
}

#[test]
fn clustering_with_as_many_clusters_as_points_merges_nothing() {
    let (out, result) = on_text("14", "cluster_none", "5\n0 0\n9 9\n");
    assert_eq!((out.as_str(), result), ("0: 0\n1: 1\n", Ok(())));
}

#[test]
fn clustering_to_a_hugely_negative_count_stops_at_one_cluster() {
    let input = "-1000000000000000000000000\n0 0\n1 1\n";
    let (_, result) = on_text("14", "cluster_huge", input);
    assert!(
        result.is_err(),
        "merging past one cluster has no closest pair"
    );
}

#[test]
fn a_spreadsheet_formula_counts_a_repeated_term_each_time() {
    let input = "a = b+b+1\nb = 2\nb = -3\n";
    let (out, result) = on_text("15", "sheet_repeat", input);
    assert_eq!(
        (out.as_str(), result),
        ("a=1\na=5 b=2\na=-5 b=-3\n", Ok(()))
    );
}

#[test]
fn a_spreadsheet_edit_drops_the_dependencies_of_the_old_formula() {
    let input = "a = b\nb = 1\na = 2\nb = 3\n";
    let (out, result) = on_text("15", "sheet_drop", input);
    assert_eq!(
        (out.as_str(), result),
        ("a=0\na=1 b=1\na=2 b=1\na=2 b=3\n", Ok(()))
    );
}

#[test]
fn a_spreadsheet_change_reaches_a_diamond_of_cells_once_per_path() {
    let input = "d = b+c\nb = a\nc = a\na = 5\n";
    let (out, result) = on_text("15", "sheet_diamond", input);
    assert_eq!(result, Ok(()));
    assert_eq!(out.lines().last(), Some("a=5 b=5 c=5 d=10"));
}

#[test]
fn a_spreadsheet_cycle_made_by_a_late_edit_is_an_error() {
    let (_, result) = on_text("15", "sheet_late", "a = b\nb = c\nc = 1\nc = a\n");
    assert!(result.is_err_and(|e| e.ends_with("depends on itself")));
}

#[test]
fn a_heat_stencil_prints_the_first_three_rows_and_the_last() {
    let (out, result) = on_text("26", "heat_rows", "5\n0 8 0\n");
    assert_eq!(result, Ok(()));
    let times: Vec<&str> = out.lines().filter_map(|l| l.split(':').next()).collect();
    assert_eq!(times, ["t=0", "t=1", "t=2", "t=5"]);
}
