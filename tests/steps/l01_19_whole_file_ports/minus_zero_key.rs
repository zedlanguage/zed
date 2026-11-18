//! A `-0.0` read from the input and held in a family finds the entry of the family with `0.0`
//! (plan row PERF-value-key-sites-bench). DESIGN.md sec:type_resolution, "Equality and order
//! corner rules": key formation turns `-0.0` into `0.0`, so the two zeros are one key, at any
//! depth of the key. Before the fix the key of a family kept its `-0.0` (`Value::is_key` passed
//! over families), so `t[[z, 1.0]]` missed and printed `-1`. The zero comes from standard input,
//! so no evaluation before the run can fold it.

use zed_tests::step_helpers::l01_19_whole_file_ports::run;

const SRC: &str = "main(m: MainArgs) {
    s = m.stdin[0] else \"0\";
    z = f64(s) else 1.0;
    t = {[0.0, 1.0] -> 7};
    u = {(0.0, 1.0) -> 7};
    v = {z -> 7};
    m.stdout <- \"${[z, 1.0] == [0.0, 1.0]} ${t[[z, 1.0]] else -1} ${u[(z, 1.0)] else -1} ${v[0.0] else -1}\";
}
";

/// The list key, the tuple key and the scalar key each find their entry, for `-0` and, as a
/// control, `0`.
#[test]
fn a_list_holding_minus_zero_finds_the_entry_of_the_list_holding_zero() {
    for input in ["-0\n", "0\n"] {
        let out = run("minus_zero_key", SRC, input, &[]);
        assert_eq!(
            (out.status, out.stdout.as_str()),
            (0, "true 7 7 7\n"),
            "stdin {input:?}\n{}",
            out.stderr
        );
    }
}
