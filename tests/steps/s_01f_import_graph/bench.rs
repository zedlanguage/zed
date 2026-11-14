//! The benchmarks of the import-graph tool, run by `tools/run_tests.sh --bench` and left out
//! of its default run (TEST-bench-move-rest). They hold the comparison with the known list
//! linear in its length; the tool linear in the files of one cycle, in methods written apart
//! and called on untyped or typed values, and in many untyped calls of one name, open or
//! hidden; and untyped calls with no triangle at `n^1.5 log n` in the input (COMPLEXITY.md
//! F103). What each asserts besides its ratio is checked at small sizes by a test of `mod.rs`.

use zed_tests::scaling::{check, check_order};

use crate::{
    half_new_half_stale, hidden_methods_import_nothing, known_list, many_calls,
    many_calls_import_their_methods, many_hidden, method_ring, no_call_imports_without_a_triangle,
    no_triangle, one_cycle_of_methods, one_ring_of, ring, untyped_ring,
};

#[test]
fn comparing_with_the_known_list_scales_with_its_length() {
    // Inputs are built before timing: n files in cycles and a list of n entries, half of them
    // the files, half stale, so both directions are searched in full.
    let n = 20_000;
    let sizes = [n, 8 * n];
    let inputs: Vec<(Vec<String>, Vec<String>)> = sizes.iter().map(|&m| known_list(m)).collect();
    let lists: Vec<Vec<&str>> = inputs
        .iter()
        .map(|(_, k)| k.iter().map(String::as_str).collect())
        .collect();
    check("against_known, by files and entries", n, |m| {
        let at = sizes
            .iter()
            .position(|&s| s == m)
            .expect("a size that was built");
        half_new_half_stale(&lists[at], &inputs[at].0, m);
    });
}

#[test]
fn the_tool_scales_with_the_number_of_files() {
    // Inputs are built before timing. The ring is one long component, so Tarjan's explicit
    // stack is as deep as the crate is large, and the report names all n files twice.
    let n = 400;
    let inputs = [ring(n), ring(8 * n)];
    check("imports, by files in one cycle", n, |m| {
        let files = inputs
            .iter()
            .find(|f| f.len() == m + 1)
            .expect("a size that was built");
        one_ring_of(files, m);
    });
}

#[test]
fn untyped_calls_scale_with_the_number_of_files() {
    // Every type has a method `go`, so each untyped call meets n type files; joined from the
    // calling file's two imports of type files, it costs two lookups, and the imports are 2n.
    let n = 200;
    let inputs = [untyped_ring(n), untyped_ring(8 * n)];
    check(
        "imports, by untyped calls of methods written apart",
        n,
        |m| {
            let files = inputs
                .iter()
                .find(|f| f.len() == 2 * m + 1)
                .expect("a size that was built");
            one_cycle_of_methods(files, m, m);
        },
    );
}

#[test]
fn typing_the_calls_scales_with_the_number_of_files() {
    // Every type has a method of the same name, so a call whose receiver went untyped would
    // import all n files with it, n^2 imports in all; typed, each call is one hash lookup.
    let n = 200;
    let inputs = [method_ring(n), method_ring(8 * n)];
    check("imports, by methods written apart in one cycle", n, |m| {
        let files = inputs
            .iter()
            .find(|f| f.len() == 2 * m + 1)
            .expect("a size that was built");
        one_cycle_of_methods(files, m, 0);
    });
}

#[test]
fn many_calls_of_a_name_cost_no_more_than_their_methods() {
    // k calls of `go` in one file meet k methods of `go` through `t.rs`. Taken once for the pair
    // of file and name, they cost O(k log k), not one walk over the k methods per call (k^2),
    // whether the methods are open to the calls or not.
    let n = 200;
    let inputs = [many_calls(n, true), many_calls(8 * n, true)];
    check("imports, by many untyped calls of one name", n, |m| {
        let files = inputs
            .iter()
            .find(|f| f.len() == m + 3)
            .expect("a size that was built");
        many_calls_import_their_methods(files, m);
    });
    // Each hidden method costs the k^2 walk one check of a range, cheap beside reading its
    // lines, so the walk shows in the ratio only from k = 600 on (14.1 times at 600 and 4800).
    let n = 600;
    let inputs = [many_hidden(n), many_hidden(8 * n)];
    check("imports, by many untyped calls of hidden methods", n, |m| {
        hidden_methods_import_nothing(&inputs[usize::from(m != n)]);
    });
}

#[test]
fn untyped_calls_without_a_triangle_scale_at_the_proven_bound() {
    // The join of the pairs of caller and name with the type files costs p √p for p pairs,
    // imports and type files, and no method is near-linear unless triangles can be found in
    // near-linear time (COMPLEXITY.md F103). At `s` and `8s` the input grows 64 times and the
    // work by at most 8^3 = 512, held to n^3 log n in `s`, that is n^1.5 log n in the input.
    let s = 24;
    let inputs = [no_triangle(s), no_triangle(8 * s)];
    check_order("imports, by untyped calls with no triangle", s, 3, |m| {
        let files = inputs
            .iter()
            .find(|f| f.len() == 3 * m + 2)
            .expect("a size that was built");
        no_call_imports_without_a_triangle(files, m);
    });
}
