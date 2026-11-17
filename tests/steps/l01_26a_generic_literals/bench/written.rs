use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::type_errors;

use super::super::written::long;

// The ratio is 9.29 in instructions (2,654M at n = 1,500,000, 24,663M at 8n; 8.65 in bytes,
// 2026-11-17, plan row PERF-quoting-bench-ratio), over the goal of 9 and under the limit. The
// literal's value is read once per check (`read_literal`, `Value::int_text`, `read_decimal`) and
// never printed; the rest is linear: lexing the `_` out (`without_separators`) and scanning the
// message text. The part above n log n is that one decimal-to-binary conversion of 1.5M digits,
// O(n log^2 n) (`num::fast::read_digits_by`, COMPLEXITY.md K41), about 40% of the cycles of
// both sizes under perf; no
// faster conversion is known, and plan row RADIX-nlog2-10_5 owns it. For comparison, n log n
// alone predicts 8 ln(8n)/ln n = 9.17 at this n, and n log^2 n 10.51.
#[test]
fn quoting_a_literal_of_n_digits_with_underscores_scales() {
    let n = 1_500_000;
    let srcs = scaling::inputs(n, long);
    scaling::check("quoting a literal of n digits with `_`", n, |m| {
        type_errors(&srcs[&m]);
    });
}
