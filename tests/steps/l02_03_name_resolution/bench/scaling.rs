//! Loading and resolving a package is linear in its units, its imports and its names, and
//! ordering an import graph and reporting its cycles is linear in its units and imports: the
//! benchmarks of `scaling.rs`, whose tests load each package and order each graph at small
//! sizes, with the checks of each input these benchmarks made at n and 8n.

use std::collections::HashMap;
use std::sync::Mutex;

use zed_tests::scaling;
use zedc::query::Db;
use zedc::unit::{Memory, load, order};

use crate::scaling::{
    Graph, chain, chain_back, chain_of_cycles, complete, cycles_of_two, dense, fan, graph,
    imports_back, ladder, later_forms, long_cycle, memory, names, nested_fors, own_main, pairs,
    pairs_of_units, placeholders, ring,
};

/// Checks that loading the package `make(k)` from `main` is linear in `k`, from `k` = `n`.
fn linear(what: &str, n: usize, make: impl Fn(usize) -> Vec<(String, String)>) {
    let pkgs: HashMap<usize, Memory> = [n, 8 * n]
        .into_iter()
        .map(|k| (k, memory(make(k))))
        .collect();
    scaling::check_order(what, n, 1, |k| {
        std::hint::black_box(load(&mut Db::new(), &pkgs[&k], &["main"]));
    });
}

#[test]
fn many_units_each_importing_two_load_in_linear_time() {
    linear("a ladder of units", 200, ladder);
}

#[test]
fn a_long_chain_of_imports_loads_in_linear_time() {
    linear("a chain of units", 200, chain);
}

#[test]
fn a_unit_importing_many_units_loads_in_linear_time() {
    linear("a fan of imports", 200, fan);
}

#[test]
fn an_import_of_many_names_loads_in_linear_time() {
    linear("an import of many names", 500, names);
}

#[test]
fn a_lambda_of_many_tuple_parameters_resolves_in_linear_time() {
    linear("a lambda of many tuple parameters", 2000, pairs);
}

#[test]
fn many_functions_of_later_forms_resolve_in_linear_time() {
    linear("many functions of later forms", 500, later_forms);
}

#[test]
fn fors_nested_deep_resolve_in_linear_time() {
    linear("fors nested deep", 500, nested_fors);
}

#[test]
fn a_long_cycle_is_named_whole_in_linear_time() {
    linear("a cycle of units", 200, long_cycle);
}

#[test]
fn a_chain_with_one_import_back_is_named_in_linear_time() {
    linear("a chain with one import back", 200, chain_back);
}

#[test]
fn many_imports_back_into_a_long_cycle_are_named_once_in_linear_time() {
    linear("many imports back into a cycle", 200, imports_back);
}

#[test]
fn many_disjoint_cycles_are_each_named_in_linear_time() {
    linear("many cycles of two", 200, cycles_of_two);
}

#[test]
fn many_roots_load_in_linear_time() {
    // Each unit is looked up among those read when it is added (`unit::add`); a linear scan
    // there in place of `Package::index` makes this 47.2 times the work at 1,000 and 8,000
    // units (measured), while the other tests here pass with it: a unit of the fan costs
    // 540,000 instructions to read, parse and resolve, against the scan's 32 per unit compared.
    let pkgs: HashMap<usize, (Memory, Vec<String>)> = [1000, 8000]
        .into_iter()
        .map(|k| (k, placeholders(k)))
        .collect();
    scaling::check_order("many roots", 1000, 1, |k| {
        let (fs, roots) = &pkgs[&k];
        let roots: Vec<&str> = roots.iter().map(String::as_str).collect();
        std::hint::black_box(load(&mut Db::new(), fs, &roots));
    });
}

/// Orders the import graph `g` again, its earlier order and reports cleared.
fn reorder(g: &Mutex<Graph>) {
    let (pkg, edges) = &mut *g.lock().unwrap();
    pkg.order.clear();
    pkg.problems.clear();
    std::hint::black_box(order(pkg, edges, None));
}

/// Checks that ordering the import graph `make(k)` and reporting its cycles is linear in its
/// units and imports, from `k` = `n`, with no file read.
fn ordered(what: &str, n: usize, make: impl Fn(usize) -> Vec<Vec<usize>>) {
    let graphs: HashMap<usize, Mutex<Graph>> = [n, 8 * n]
        .into_iter()
        .map(|k| (k, Mutex::new(graph(&make(k)))))
        .collect();
    scaling::check_order(what, n, 1, |k| reorder(&graphs[&k]));
}

#[test]
fn many_disjoint_cycles_are_ordered_and_reported_in_linear_time_with_no_file_read() {
    // Clearing or allocating the search's arrays, of the size of the package, for each
    // component makes this quadratic and fails here (measured, COMPLEXITY.md F84); the loading
    // tests above passed under the allocation, since loading a unit costs far more.
    ordered("many cycles of two, ordered", 4000, pairs_of_units);
}

#[test]
fn one_long_cycle_is_ordered_and_reported_in_linear_time_with_no_file_read() {
    ordered("one cycle, ordered", 2000, ring);
}

#[test]
fn a_dense_component_is_searched_once_in_linear_time_with_no_file_read() {
    // A search from each unit would take `k` times as long.
    ordered("a dense component, ordered", 500, dense);
}

#[test]
fn a_chain_of_cycles_is_ordered_in_linear_time_with_no_file_read() {
    ordered("a chain of cycles, ordered", 4000, chain_of_cycles);
}

#[test]
fn a_complete_component_is_searched_once_in_time_linear_in_its_imports() {
    // The sizes 40 and 113 give 1,560 and 12,656 imports, 8.1 times as many, held to the limit
    // for 8 times.
    let graphs: HashMap<usize, Mutex<Graph>> = [40, 113]
        .into_iter()
        .map(|k| (k, Mutex::new(graph(&complete(k)))))
        .collect();
    scaling::compare(
        "a complete component, ordered: 40 and 113 units, 1,560 and 12,656 imports, 8.1 times",
        1,
        || reorder(&graphs[&40]),
        || reorder(&graphs[&113]),
    );
}

#[test]
fn reads_of_main_files_in_a_unit_with_its_own_main_are_rejected_in_linear_time() {
    let pkgs: HashMap<usize, Memory> = scaling::inputs(200, |k| memory(own_main(k)));
    scaling::check(
        "an imported unit with its own main and many reads of main::files",
        200,
        |k| {
            std::hint::black_box(load(&mut Db::new(), &pkgs[&k], &["main"]));
        },
    );
}
