//! Row TEST-range-keys-mutual-recursion: a remap that reads a parameter declared a partial map
//! with a range on its key (RANGE-keys), in functions that call each other or themselves, and
//! in a lambda or a function inside the body. The checker records that a remap reads the
//! parameter while it checks the body, and turns the record into the parameter's need when
//! the function's check ends (`floors_into`); these tests show no remap is read after that.
//! Recursion is rejected until step L6 and the body of a function in a cycle is not checked,
//! so no remap there is read at all: only the recursion is reported.

use crate::source::{all_errors, rejected, same};

/// `f` and `g` call each other, and each remaps its `m` by `k mod 5`, whose witness reads the
/// range on the key.
const MUTUAL: &str = "f(positional m: int[5..<10] ->? int, n: int) = if n > 0 { g(m, n: n - 1) } else { m as (k -> v) into (k mod 5 -> v) };\n\
                      g(positional m: int[5..<10] ->? int, n: int) = if n > 0 { f(m, n: n - 1) } else { m as (k -> v) into (k mod 5 -> v) };\n";

/// The errors of `src`: each reports the recursion, and none a key or a remap.
fn only_recursion(src: &str, head: &str) {
    let es = all_errors(src);
    assert!(
        es.iter().any(|e| e.contains(head)),
        "{src}\nmissing {head:?} in:\n{}",
        es.join("\n")
    );
    for e in &es {
        assert!(
            !e.contains("keys in") && !e.contains("family") && !e.contains("remap"),
            "{src}\nan error of a key or a remap:\n{}",
            es.join("\n")
        );
    }
}

#[test]
fn functions_that_call_each_other_and_remap_their_ranged_maps_report_only_the_recursion() {
    only_recursion(
        MUTUAL,
        "`f`, `g` are defined in terms of each other, which is recursion",
    );
    // A call of them, with keys outside the range, adds no error of the keys: the functions
    // of a cycle have no signature to check it against.
    only_recursion(
        &format!("{MUTUAL}x = f({{ 3 -> 1, 8 -> 2 }}, n: 2);\n"),
        "which is recursion",
    );
}

#[test]
fn a_function_that_calls_itself_and_remaps_its_ranged_map_reports_only_the_recursion() {
    let src = "f(positional m: int[5..<10] ->? int, n: int) = if n > 0 { f(m, n: n - 1) } else { m as (k -> v) into (k mod 5 -> v) };\n";
    only_recursion(src, "is defined in terms of itself, which is recursion");
}

#[test]
fn a_cycle_where_only_one_function_remaps_reports_only_the_recursion() {
    let src = "f(positional m: int[5..<10] ->? int, n: int) = if n > 0 { g(m, n: n - 1) } else { m as (k -> v) into (k mod 5 -> v) };\n\
               g(positional m: int[5..<10] ->? int, n: int) = if n > 0 { f(m, n: n - 1) } else { m };\n";
    only_recursion(src, "which is recursion");
}

#[test]
fn a_function_outside_the_cycle_still_checks_the_keys_its_remap_reads() {
    // `h` calls into the cycle but is not in it: its own remap is checked, and its calls are
    // checked against the range on its key.
    let src = format!(
        "{MUTUAL}h(positional m: int[5..<10] ->? int) = m as (k -> v) into (k mod 5 -> v);\n\
         x = h({{ 7 -> 1 }});\nwant = {{ 2 -> 1 }};\ny = h({{ 3 -> 1, 8 -> 2 }});\n"
    );
    rejected(
        &src,
        &[
            "which is recursion",
            "`h` takes `m` as a family, which a remap reads, with keys in int[5..=9]: `{ 3 -> 1, 8 -> 2 }` may not be one",
        ],
    );
}

/// The need a call of `f` fails where a remap reads `m`: the message says `m` is taken as a
/// family, which only a remap read before the end of `f`'s check records.
const FAMILY: &str = "`f` takes `m` as a family, which a remap reads, with keys in int[5..=9]: `{ 3 -> 1, 8 -> 2 }` may not be one";

#[test]
fn a_lambda_in_the_body_remaps_the_ranged_map_and_its_calls_are_checked() {
    let f = "f(positional m: int[5..<10] ->? int) = { h = (n: int) -> m as (k -> v) into (k mod 5 -> v); h(0) };\n";
    same(
        &format!("{f}x = f({{ 7 -> 1 }});\nwant = {{ 2 -> 1 }};\n"),
        "x",
        "want",
    );
    rejected(&format!("{f}x = f({{ 3 -> 1, 8 -> 2 }});\n"), &[FAMILY]);
}

#[test]
fn a_function_in_the_body_remaps_the_ranged_map_and_its_calls_are_checked() {
    let f = "f(positional m: int[5..<10] ->? int) = { h(n: int) = m as (k -> v) into (k mod 5 -> v); h(n: 0) };\n";
    same(
        &format!("{f}x = f({{ 7 -> 1 }});\nwant = {{ 2 -> 1 }};\n"),
        "x",
        "want",
    );
    rejected(&format!("{f}x = f({{ 3 -> 1, 8 -> 2 }});\n"), &[FAMILY]);
}

/// Landing review of LAND-map-chain-neon, B6: link `h{i}` calls `h{i-1}` and maps its result by
/// `f`, written last link first, so each link's forward holds the next as its callee and
/// finishing them went 8,000 calls deep. The recursion aborted with a stack overflow on an
/// 8 MiB stack; the explicit stack in `r10_finish_fwd_callee` checks it on 2 MiB.
#[test]
fn a_chain_of_8000_maps_written_in_reverse_order_checks_on_a_2_mib_stack() {
    let n = 8000;
    let mut src = String::new();
    for i in (1..n).rev() {
        src.push_str(&format!(
            "h{i}(positional f, positional m) = h{}(f, m).map(f);\n",
            i - 1
        ));
    }
    src.push_str("h0(positional f, positional m) = m.map(f);\n");
    src.push_str(&format!(
        "a = h{}(x -> x + 1, {{\"k\" -> 0}})[\"k\"];\n",
        n - 1
    ));
    std::thread::scope(|scope| {
        let thread = std::thread::Builder::new().stack_size(2 << 20);
        let run = || {
            assert_eq!(
                zed_tests::step_helpers::l01_16_elaboration::value(&src, "a"),
                n.to_string()
            )
        };
        thread.spawn_scoped(scope, run).unwrap().join().unwrap();
    });
}
