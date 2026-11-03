//! Step M0.4: the reference programs of the corpus. Each `.out` file is what the reference
//! program of its number prints on the `.in` file of the same name. The references compute the
//! outputs without the compiler, so the corpus tests the compiler rather than repeating it.

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
fn clustering_breaks_ties_by_label() {
    let input = "2\n0 0\n1 0\n0 1\n1 1\n";
    let (out, result) = on_text("14", "cluster_ties", input);
    assert_eq!(result, Ok(()));
    assert_eq!(out, "0: 0 1 2\n3: 3\n");
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
