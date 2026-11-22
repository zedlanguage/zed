//! Completeness cases for step M0.4 (TEST-complete-m0, author P189): the shared helpers of the
//! references at each kind of value, and each reference's branches for input it does not read
//! as data. Expected values follow DESIGN.md (sec:reduction for the float sum and printing, step
//! L1.18 for `lower`) and the header comment of each reference. The case list is
//! `COMPLETENESS.md`.

use super::on_text;
use zed_corpus_ref::zedrt::{TreeSum, fsum, lower, parse_float};

/// DESIGN sec:reduction item 1's canonical tree over `xs`, transcribed from its recursive
/// definition: one value is itself; a power-of-two count reduces its two halves and adds the left
/// result to the right; any other count `n`, with `p` the largest power of two dividing it,
/// reduces the first `n - p` and the last `p` and adds the left to the right.
fn tree(xs: &[f64]) -> f64 {
    let n = xs.len();
    if n == 1 {
        return xs[0];
    }
    let p = 1 << n.trailing_zeros();
    let split = if p == n { n / 2 } else { n - p };
    tree(&xs[..split]) + tree(&xs[split..])
}

#[test]
fn a_float_sum_is_ieee_addition_on_the_canonical_tree_at_every_kind_of_value() {
    let bits = |xs: &[f64]| fsum(xs.iter().copied()).to_bits();
    // No value is the identity of IEEE addition, -0.0 (sec:reduction, "Identity as data"); one
    // value is itself, so a lone -0.0 keeps its sign, as IEEE's -0.0 + -0.0 does; x + -x is +0.0.
    // IEEE Std 754-2019, doi:10.1109/IEEESTD.2019.8766229, section 6.3; the full comment is in
    // zedc-check `check/walk.rs`, at the identity of a float `+` fold. The other IEEE mentions
    // in this file and in `mod.rs` rest on the same citation and on section 5.4.1 (zed-kernel
    // `eval.rs`, fn `prim_on`, at `Prim::Sqrt`).
    assert_eq!(bits(&[]), (-0.0f64).to_bits());
    assert_eq!(bits(&[-0.0]), (-0.0f64).to_bits());
    assert_eq!(bits(&[-0.0, -0.0]), (-0.0f64).to_bits());
    assert_eq!(bits(&[1.0, -1.0]), 0);
    // n = 3 is (e0 + e1) + e2: 0.1 + 0.2 + 0.3 is 0.6000000000000001, where the exact sum
    // rounded once would be 0.6, and 1 is lost beside 1e16 before -1e16 cancels it.
    assert_eq!(fsum([0.1, 0.2, 0.3]), 0.6000000000000001);
    assert_eq!(fsum([1.0, 1e16, -1e16]), 0.0);
    // n = 4 is (e0 + e1) + (e2 + e3): the last two ones add to 2 before they meet 1e16, where a
    // left-to-right sum loses each 1 (1e16 + 1 is a tie, kept at the even 1e16).
    assert_eq!(fsum([1e16, 1.0, 1.0, 1.0]), 10000000000000002.0);
    assert_eq!(((1e16 + 1.0) + 1.0) + 1.0, 1e16);
    // n = 6 is ((e0 + e1) + (e2 + e3)) + (e4 + e5), DESIGN's own example: 1e16 + 2 + 2.
    assert_eq!(fsum([1e16, 1.0, 1.0, 1.0, 1.0, 1.0]), 10000000000000004.0);
    // Overflow is IEEE's: an infinity, even where the exact sum is finite.
    assert_eq!(fsum([f64::MAX, f64::MAX, -f64::MAX]), f64::INFINITY);
    assert_eq!(fsum([f64::MAX, f64::MAX]), f64::INFINITY);
    assert_eq!(fsum([-f64::MAX, -f64::MAX]), f64::NEG_INFINITY);
    // Subnormal terms and results: 2 * 2^-1074, and the largest subnormal.
    assert_eq!(bits(&[5e-324, 5e-324]), 2);
    assert_eq!(bits(&[f64::MIN_POSITIVE, -5e-324]), 0x000F_FFFF_FFFF_FFFF);
    // Ties to even: 2^53 - 1 + 0.5 rounds up into the next binade, 2^53 - 2 + 0.5 down.
    let two53 = 2f64.powi(53);
    assert_eq!(fsum([two53 - 1.0, 0.5]), two53);
    assert_eq!(fsum([two53 - 2.0, 0.5]), two53 - 2.0);
    // The special values: NaN in, NaN out (item 5); inf + -inf is NaN, not an error, as a float
    // `+` without `@fpwarn` gives IEEE's own values (the unlifted-carrier rule, item 1).
    assert!(fsum([f64::NAN, 1.0]).is_nan());
    assert!(fsum([1.0, f64::NAN, f64::INFINITY]).is_nan());
    assert_eq!(fsum([f64::INFINITY, 1.0]), f64::INFINITY);
    assert_eq!(fsum([f64::NEG_INFINITY, 1.0]), f64::NEG_INFINITY);
    assert!(fsum([f64::INFINITY, f64::NEG_INFINITY]).is_nan());
}

#[test]
fn every_scan_entry_and_fold_is_the_canonical_tree_over_its_prefix() {
    // Values of magnitudes from 2^-60 to 2^70 and both signs, so that the grouping changes the
    // rounding (a left-to-right sum fails this test first at entry 31); the prefix lengths 1 to
    // 300 reach every stack of up to eight blocks.
    let xs: Vec<f64> = (0..300)
        .map(|i: i32| {
            let x = f64::from((i * 7919) % 1009 + 1) * 2f64.powi((i * 37) % 121 - 60);
            if i % 3 == 0 { -x } else { x }
        })
        .collect();
    let mut scan = TreeSum::default();
    for (i, &x) in xs.iter().enumerate() {
        let want = tree(&xs[..=i]).to_bits();
        assert_eq!(scan.add(x).to_bits(), want, "scan entry {i}");
        assert_eq!(scan.value().to_bits(), want, "value after entry {i}");
        assert_eq!(
            fsum(xs[..=i].iter().copied()).to_bits(),
            want,
            "fold of {}",
            i + 1
        );
    }
}

#[test]
fn a_float_text_reads_as_design_says_where_the_reference_agrees() {
    // DESIGN step L1.18: an optional `-`, then `inf`, `nan`, or digits with an optional fraction
    // and exponent, correctly rounded; a zero after `-` is -0.0, and a value at most half the
    // smallest subnormal is a zero of its sign.
    let read = |s: &str| parse_float(s).map(f64::to_bits);
    assert_eq!(parse_float("1.5"), Ok(1.5));
    assert_eq!(parse_float("2.5e-3"), Ok(0.0025));
    assert_eq!(parse_float("1e3"), Ok(1000.0));
    // The exponent is written as `String` writes it, `e` and a sign only as `-`; the compiler
    // reads it so (l01_18 `completeness.rs`, `1E5` and `1e+5` are `#invalid`).
    for s in ["1E3", "1e+3"] {
        assert_eq!(parse_float(s), Err(format!("invalid float: {s}")), "{s:?}");
    }
    assert_eq!(read("-0"), Ok((-0.0f64).to_bits()));
    assert_eq!(read("1e-400"), Ok(0));
    assert_eq!(read("-1e-400"), Ok((-0.0f64).to_bits()));
    assert_eq!(parse_float("inf"), Ok(f64::INFINITY));
    assert_eq!(parse_float("-inf"), Ok(f64::NEG_INFINITY));
    assert!(parse_float("nan").is_ok_and(f64::is_nan));
    for s in [
        "", ".", "-", "e5", ".e5", "1e", "1e+", "1e5.", "1.2.3", "abc", "0x10", "_1", "1_", "1__0",
        "1_.5", "1._5",
    ] {
        assert_eq!(parse_float(s), Err(format!("invalid float: {s}")), "{s:?}");
    }
}

#[test]
fn lower_takes_the_full_mapping_with_the_final_sigma() {
    // DESIGN step L1.18: `lower` is Unicode's full case mapping, which maps U+0130 to two code
    // points and capital sigma to the final form only after a cased letter and before none,
    // case-ignorable characters (here the apostrophe) skipped.
    for (s, want) in [
        ("İ", "i\u{307}"),
        ("ΟΔΟΣ", "οδος"),
        ("Σ", "σ"),
        ("ΣΑ", "σα"),
        ("ΑΣ'", "ας'"),
        ("Α'Σ", "α'ς"),
        ("ΑΣ'Β", "ασ'β"),
        ("ΑΣ Β", "ας β"),
    ] {
        assert_eq!(lower(s), want, "{s}");
    }
}

/// The output and result of reference `number` on `input`, compared with the expected ones.
fn check(number: &str, name: &str, input: &str, out: &str, result: Result<(), &str>) {
    assert_eq!(
        on_text(number, name, input),
        (out.to_string(), result.map_err(str::to_string)),
        "{number} on {input:?}"
    );
}

#[test]
fn a_line_with_the_wrong_number_of_fields_is_an_error() {
    check(
        "16",
        "case_tick",
        "1 a\n",
        "",
        Err("not \"tick player dx\": 1 a"),
    );
    check(
        "23",
        "case_join",
        "o 1\n",
        "",
        Err("not \"side id amount\": o 1"),
    );
    check(
        "27",
        "case_chain",
        "a\n",
        "",
        Err("not \"child parent\": a"),
    );
    check(
        "29",
        "case_dedup",
        "a 1\n",
        "",
        Err("not \"id time value\": a 1"),
    );
}

#[test]
fn an_unreadable_number_or_a_missing_field_takes_the_programs_else_default() {
    // 04-running-variance.zed:8 reads `f64(l) else 0.0`: "abc" is 0.0, so after it the mean
    // and variance are 0.0, and after 2.0 they are 1.0 and 4/2 - 1 = 1.0.
    check(
        "04",
        "else_float",
        "abc\n2\n",
        "0.0 0.0 0.0\n2.0 1.0 1.0\n",
        Ok(()),
    );
    // 06-matrix-multiply.zed:12 reads each cell as `f64(t) else 0.0`: A = [[0.0]] and
    // B = [[3.0]] give 0.0.
    check("06", "else_cell", "1 1 1\nx\n3\n", "0.0\n", Ok(()));
    // Line 13 reads the header fields as `int(t) else 0` and lines 14-16 a missing one as
    // `hdr[i] else 0`. With "1 1" p is 0, and A, lines 1..<2 of one line, is empty.
    check("06", "else_head_short", "1 1\n", "", Ok(()));
    // With "x 1 1" n is 0, so A is empty.
    check("06", "else_head_text", "x 1 1\n2\n3\n", "", Ok(()));
    // Line 19 reads a cell of B past its row as `r[k] else 0.0`: p = 3 over a B of width 1.
    check(
        "06",
        "else_column",
        "1 1 3\n2\n5\n",
        "10.0 0.0 0.0\n",
        Ok(()),
    );
}

#[test]
fn a_matrix_row_range_before_the_first_row_is_empty() {
    // n = -5: A is `rows.slice(1..<-4)`, the lines whose rank lies in 1..<-4, and no rank does
    // (DESIGN counts no rank from the end).
    check("06", "case_rows", "-5 1 1\n2\n3\n", "", Ok(()));
}

#[test]
fn a_slice_leaves_out_the_rank_at_its_upper_end() {
    // B is `rows.slice(1 + n..<1 + n + inner)` = `rows.slice(2..<3)`: `..<` is half-open
    // (DESIGN sec:grammar, Range) and `.slice(r)` keeps the entries whose rank lies in `r`
    // (sec:kernel, the `.slice` row), so B is the line "3" alone, and the line "5" at rank 3 is
    // left out. Were rank 3 kept, A's cell 7 would meet it: 2 * 3 + 7 * 5 = 41.
    check("06", "slice_end", "1 1 1\n2 7\n3\n5\n", "6.0\n", Ok(()));
}

#[test]
fn a_short_matrix_row_or_too_few_rows_read_as_zeros() {
    // 06-matrix-multiply.zed:19 sums over the lines of B present, reading A's cell as
    // `row[c - 1 - n] else 0.0` and B's as `r[k] else 0.0`, with no `zip` and so no claim that
    // the two have one keyspace (row FAIL-corpus-06-zip-keys). A row of A shorter than inner:
    // A = [[1.0]] over B = [[2.0], [3.0]] is 1.0 * 2.0 + 0.0 * 3.0.
    check("06", "zip_short", "1 2 1\n1\n2\n3\n", "2.0\n", Ok(()));
    // Fewer lines of B than inner: B is the one line 2, so only A's column 0 is read.
    check("06", "few_b_rows", "1 3 1\n1 1 1\n2\n", "2.0\n", Ok(()));
    // A's columns from inner on are not read: 2.0 * 3.0, the 7 left out.
    check("06", "long_a_row", "1 1 1\n2 7\n3\n", "6.0\n", Ok(()));
    // inner = 0: each of the p cells is the empty sum, -0.0, the identity of IEEE addition
    // (sec:reduction, "Identity as data").
    check("06", "no_b_rows", "1 0 2\n5\n", "-0.0 -0.0\n", Ok(()));
    // Two rows of A, one short, over a 2 × 2 B: [1, 2] · B = [1 + 6, 2 + 8] and [4] · B = [4, 8].
    check(
        "06",
        "ragged",
        "2 2 2\n1 2\n4\n1 2\n3 4\n",
        "7.0 10.0\n4.0 8.0\n",
        Ok(()),
    );
}

#[test]
fn percent_decoding_drops_a_surrogate_a_value_past_u10ffff_an_overlong_form_and_a_bad_lead() {
    // "Malformed UTF-8 is dropped, not repaired" (08-utf8-percent.zed's header), and the line
    // goes on. %ED%A0%80 is U+D800 and %F7%BF%BF%BF is 0x1FFFFF: neither is a character.
    check("08", "case_surrogate", "a%ED%A0%80b\n", "ab\n", Ok(()));
    check("08", "case_past", "ok\n%F7%BF%BF%BF!\n", "ok\n!\n", Ok(()));
    // %F4%90%80%80 is 0x110000, the first value past U+10FFFF.
    check("08", "case_first_past", "x%F4%90%80%80y\n", "xy\n", Ok(()));
    // Overlong forms: U+0000 in two bytes, U+07FF in three, U+FFFF in four, and C1 BF (U+007F).
    check(
        "08",
        "case_overlong",
        "a%C0%80b%E0%9F%BFc%F0%8F%BF%BFd%C1%BFe\n",
        "abcde\n",
        Ok(()),
    );
    // The shortest form of each length stays: U+0080, U+0800 and U+10000.
    check(
        "08",
        "case_shortest",
        "%C2%80%E0%A0%80%F0%90%80%80\n",
        "\u{80}\u{800}\u{10000}\n",
        Ok(()),
    );
    // A byte from F8 up starts no sequence; its three bytes after are stray continuations.
    check("08", "case_bad_lead", "%F9%90%80%80z\n", "z\n", Ok(()));
}

#[test]
fn a_spreadsheet_cycle_is_named_after_a_walk_past_closed_and_shared_cells() {
    // The walk in name order: a closes, b reads c before c's own turn and a closed, c is passed
    // over as visited, and d reaches itself through e.
    let input = "a = 1\nb = c+a\nc = 2\nd = e\ne = d\n";
    let out = "a=1\na=1 b=1\na=1 b=3 c=2\na=1 b=3 c=2 d=0\n";
    check(
        "15",
        "case_walk",
        input,
        out,
        Err("the cell d depends on itself"),
    );
}

#[test]
fn a_word_frequency_line_whose_first_piece_is_not_an_int_is_skipped() {
    let plain = on_text("18", "case_plain", "1 a b\n7 a\n");
    assert_eq!(plain.1, Ok(()));
    let skipped = on_text("18", "case_skip", "x a\n1 a b\n\nnine a\n7 a\n");
    assert_eq!(skipped, plain);
}

#[test]
fn a_failed_balance_stays_failed_and_an_unknown_kind_is_ignored() {
    let input = "open a\nwd a 5\nwd a 1\ndep a 9\nnote a\nopen b\ndep b 3\nnote zz 1\n";
    let out = "a: insufficient at tx 1, short 5\nb: 3\ntotal 3 over 1 accounts, 1 failed\n";
    check("19", "case_ledger", input, out, Ok(()));
}

#[test]
fn stats_of_no_line_divide_by_zero() {
    check("21", "case_stats", "", "", Err("float division by zero"));
}

#[test]
fn a_buy_request_with_no_quantity_fails_at_the_farthest_position() {
    // "buy apple": the get alternative fails at 0 and the buy alternative at 9, where a quantity
    // was expected; with "x" there it fails at 10, past the space.
    check(
        "30",
        "case_buy",
        "buy apple\nbuy apple x\nbuy apple 2\n",
        "bad request at 9\nbad request at 10\napple=6\n",
        Ok(()),
    );
}

#[test]
fn a_missing_account_operand_or_heat_step_is_an_error() {
    check("19", "case_account", "dep a 5\n", "", Err("no account a"));
    check("28", "case_operands", "1 +\n", "", Err("too few operands"));
    // One step: the rows of steps 0 and 1 print, and there is no step 2.
    check(
        "26",
        "case_steps",
        "1\n0 8 0\n",
        "t=0: 0 8 0\nt=1: 0 4 0\n",
        Err("no step 2"),
    );
}
