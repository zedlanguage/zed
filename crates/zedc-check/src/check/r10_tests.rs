//! Round 10 verification suite for the unified fixed-D design (`M66`, `M31`, `M62`, `M63`)
//! and Point 2 (`M56(c)`).

use std::collections::{BTreeSet, HashSet};

use crate::check::Info;
use crate::check::probe::{
    PendingMode, R10Config, R10Stats, StoreMode, last_r10_stats, set_next_config,
};
use crate::check::walk::check_text;
use zedc_types::ty::{NeedKind, Sig, fits_sig, fwd_decode_count, reset_fwd_decode_count};

fn run_with_cfg(text: &str, cfg: R10Config) -> (Info, R10Stats) {
    let tokens = zedc_syntax::lex::lex(text).expect("the unit lexes");
    let (tree, parse_errs) = zedc_syntax::parse::parse_unit(text, &tokens, zedc_syntax::parse::TOP);
    assert!(
        parse_errs.is_empty(),
        "parse errors: {parse_errs:?}\n{text}"
    );
    let unit = zedc_syntax::ast::unit(text, &tokens, &tree).expect("the unit builds");
    let res = zedc_resolve::resolve::resolve(&unit).expect("the unit resolves");
    set_next_config(cfg);
    let info = check_text(&unit, &res, Some(text));
    let stats = last_r10_stats();
    (info, stats)
}

fn chain_src(n: usize, form: &str, with_main: bool) -> String {
    let by = match form {
        "f" => "f",
        "lambda" => "x -> f(x)",
        other => panic!("unexpected form: {other}"),
    };
    let mut s = format!("h0(positional f, positional m) = m.map({by});\n");
    for i in 1..n {
        s.push_str(&format!(
            "h{i}(positional f, positional m) = h{}(f, m).map({by});\n",
            i - 1
        ));
    }
    if with_main {
        s.push_str(&format!(
            "main(m: MainArgs) {{\n  a = h{}(x -> x + 1, {{\"k\" -> 0}})[\"k\"];\n  m.stdout <- [\"${{a}}\"];\n}}\n",
            n - 1
        ));
    }
    s
}

/// Collects all `own` variables of `sig`, including those inside any `NeedKind::Fwd` after
/// decoding, so we can compare `sig.own` against flat E directly.
fn decoded_own_vars(sig: &Sig) -> BTreeSet<std::sync::Arc<str>> {
    let mut own = sig.own.clone();
    for n in &sig.needs {
        if let NeedKind::Fwd(fwd) = &n.kind {
            if let Some(ref fin) = fwd.finish_naming {
                for &(start_n, count) in &fin.runs {
                    let mut n_idx = start_n;
                    for _ in 0..count {
                        let nm = zedc_types::ty::fresh_name_with_held(
                            zedc_types::ty::Names::Variables,
                            &mut n_idx,
                            &fin.held,
                            |s| fin.skip.contains(s),
                        );
                        own.insert(nm);
                    }
                }
            } else if let Some(lo) = fwd.base_class {
                let exit_offs: HashSet<usize> = fwd.exits.iter().map(|(o, _)| *o).collect();
                for off in 0..fwd.need_count {
                    if !exit_offs.contains(&off) {
                        own.insert(format!("${}", lo + off).into());
                    }
                }
            }
        }
    }
    own
}

fn sig_eq_full(label: &str, e: &Sig, d: &Sig) -> Result<(), String> {
    if format!("{e}") != format!("{d}") {
        return Err(format!("{label}: Display mismatch\n  E: {e}\n  D: {d}"));
    }
    if e.digest() != d.digest() {
        return Err(format!(
            "{label}: Sig::digest mismatch (E={} D={})\n  E: {e}\n  D: {d}",
            e.digest(),
            d.digest()
        ));
    }
    if e != d {
        return Err(format!(
            "{label}: Same::sig (PartialEq) returned false\n  E: {e}\n  D: {d}"
        ));
    }
    if !fits_sig(e, d) || !fits_sig(d, e) {
        return Err(format!("{label}: fits_sig mismatch\n  E: {e}\n  D: {d}"));
    }
    let e_needs = e.decoded_needs_cow();
    let d_needs = d.decoded_needs_cow();
    if e_needs.as_ref() != d_needs.as_ref() {
        return Err(format!(
            "{label}: decoded sig.needs mismatch (len E={} vs D={})\n  E: {:?}\n  D: {:?}",
            e_needs.len(),
            d_needs.len(),
            e_needs.as_ref(),
            d_needs.as_ref()
        ));
    }
    let e_own = decoded_own_vars(e);
    let d_own = decoded_own_vars(d);
    if e_own != d_own {
        return Err(format!(
            "{label}: decoded sig.own mismatch\n  E: {e_own:?}\n  D: {d_own:?}"
        ));
    }
    if e.named != d.named {
        return Err(format!(
            "{label}: sig.named mismatch (E={} D={})",
            e.named, d.named
        ));
    }
    if e.bounds != d.bounds {
        return Err(format!(
            "{label}: sig.bounds mismatch (E={:?} D={:?})",
            e.bounds, d.bounds
        ));
    }
    Ok(())
}

fn info_eq_full(label: &str, e: &Info, d: &Info) -> Result<(), String> {
    if e.errors != d.errors {
        return Err(format!(
            "{label}: errors mismatch\n  E: {:?}\n  D: {:?}",
            e.errors, d.errors
        ));
    }
    if e.warnings != d.warnings {
        return Err(format!(
            "{label}: warnings mismatch\n  E: {:?}\n  D: {:?}",
            e.warnings, d.warnings
        ));
    }
    if e.sigs.len() != d.sigs.len() {
        return Err(format!(
            "{label}: sigs len mismatch (E={} D={})",
            e.sigs.len(),
            d.sigs.len()
        ));
    }
    for (id, e_sig) in &e.sigs {
        let Some(d_sig) = d.sigs.get(id) else {
            return Err(format!("{label}: missing sig for binder {id}"));
        };
        sig_eq_full(&format!("{label}:sigs[{id}]"), e_sig, d_sig)?;
    }
    if e.calls.len() != d.calls.len() {
        return Err(format!(
            "{label}: calls len mismatch (E={} D={})",
            e.calls.len(),
            d.calls.len()
        ));
    }
    for (sp, e_sig) in &e.calls {
        let Some(d_sig) = d.calls.get(sp) else {
            return Err(format!("{label}: missing call sig at {sp:?}"));
        };
        sig_eq_full(&format!("{label}:calls[{sp:?}]"), e_sig, d_sig)?;
    }
    if e.tops != d.tops {
        return Err(format!("{label}: tops mismatch"));
    }
    if e.adopt != d.adopt {
        return Err(format!("{label}: adopt mismatch"));
    }
    if e.placed != d.placed {
        return Err(format!("{label}: placed mismatch"));
    }
    if e.fits != d.fits {
        return Err(format!("{label}: fits mismatch"));
    }
    if e.passes != d.passes {
        return Err(format!("{label}: passes mismatch"));
    }
    if e.quotients != d.quotients {
        return Err(format!("{label}: quotients mismatch"));
    }
    if e.follows != d.follows {
        return Err(format!("{label}: follows mismatch"));
    }
    if e.witness != d.witness {
        return Err(format!("{label}: witness mismatch"));
    }
    if e.dense != d.dense {
        return Err(format!("{label}: dense mismatch"));
    }
    if e.brackets != d.brackets {
        return Err(format!("{label}: brackets mismatch"));
    }
    if e.reduce != d.reduce {
        return Err(format!("{label}: reduce mismatch"));
    }
    if e.reducers != d.reducers {
        return Err(format!("{label}: reducers mismatch"));
    }
    if e.family_sums != d.family_sums {
        return Err(format!("{label}: family_sums mismatch"));
    }
    if e.list_concats != d.list_concats {
        return Err(format!("{label}: list_concats mismatch"));
    }
    if e.generic_sums != d.generic_sums {
        return Err(format!("{label}: generic_sums mismatch"));
    }
    if e.split_folds != d.split_folds {
        return Err(format!("{label}: split_folds mismatch"));
    }
    if e.fold_calls != d.fold_calls {
        return Err(format!("{label}: fold_calls mismatch"));
    }
    if e.split_needs != d.split_needs {
        return Err(format!(
            "{label}: split_needs mismatch\n  E: {:?}\n  D: {:?}",
            e.split_needs, d.split_needs
        ));
    }
    if e.fold_reads != d.fold_reads {
        return Err(format!("{label}: fold_reads mismatch"));
    }
    if e.escaping_calls != d.escaping_calls {
        return Err(format!("{label}: escaping_calls mismatch"));
    }
    if e.remaps != d.remaps {
        return Err(format!("{label}: remaps mismatch"));
    }
    if e.reported_literals != d.reported_literals {
        return Err(format!("{label}: reported_literals mismatch"));
    }
    if e.blocking != d.blocking {
        return Err(format!("{label}: blocking mismatch"));
    }
    if e.limits != d.limits {
        return Err(format!("{label}: limits mismatch"));
    }
    Ok(())
}

fn assert_info_eq(label: &str, e: &Info, d: &Info) {
    if let Err(msg) = info_eq_full(label, e, d) {
        panic!("{msg}");
    }
}

/// Deliverable (a) + M66: On chains without `main` (n = 35, both forms), D performs ZERO
/// `FwdNeed` decodes, stores O(1) needs per link (1 `Fwd` + link's direct needs), and matches E
/// across every `Info` field, decoded `sig.needs`, decoded `sig.own`, `Same::sig`, `Sig::digest`,
/// `fits_sig`, and `Display`.
#[test]
fn r10_m66_zero_decode_and_readers_chain() {
    for (form, expected_compact_len) in [("f", 2usize), ("lambda", 4usize)] {
        let src = chain_src(35, form, false);
        let (e_info, _) = run_with_cfg(&src, R10Config::eager());
        reset_fwd_decode_count();
        let (d_info, d_stats) = run_with_cfg(&src, R10Config::default());
        let decodes_during_check = fwd_decode_count();
        assert_eq!(
            decodes_during_check, 0,
            "M66 violation on {form} chain without main: expected 0 decodes, got {decodes_during_check}"
        );
        assert_eq!(
            d_stats.admitted, 34,
            "{form}: expected 34 admitted forwards"
        );
        assert_eq!(
            d_stats.kept_at_generalize, 34,
            "{form}: expected 34 kept forwards"
        );
        assert_eq!(
            d_stats.m56c_bound_vars, 0,
            "{form}: m56c_bound_vars must be 0"
        );
        let last_sig = d_info.sigs.values().last().expect("h34 sig");
        assert_eq!(
            last_sig.needs.len(),
            expected_compact_len,
            "{form}: h34 compact sig.needs.len() should be {expected_compact_len}"
        );
        assert!(
            last_sig
                .needs
                .iter()
                .any(|n| matches!(n.kind, NeedKind::Fwd(_))),
            "{form}: h34 must contain NeedKind::Fwd"
        );
        assert_info_eq(&format!("chain_{form}_35_nomain"), &e_info, &d_info);
    }
}

/// Deliverable (a): `D = E` on chains of the given form for every `n` in `lo..=hi`, with exactly
/// 1 decode (at `main`). The chains to 100 are split into ranges so each test stays under the
/// 20 s limit: E (the eager checker) costs about n^2.5 per chain, measured 7.8 s for lambda
/// 2..=50, 34.5 s for 51..=80 and 57.5 s for 81..=100 at load 40 to 48 (neon-retry, 2026-11-18);
/// each range below is cut for about 8 s at that load.
fn d_equals_e_on_chains(form: &str, lo: usize, hi: usize) {
    for n in lo..=hi {
        let src = chain_src(n, form, true);
        let (e_info, _) = run_with_cfg(&src, R10Config::eager());
        assert!(
            e_info.errors.is_empty(),
            "{form} n={n} E errors: {:?}",
            e_info.errors
        );
        reset_fwd_decode_count();
        let (d_info, d_stats) = run_with_cfg(&src, R10Config::default());
        let decodes = fwd_decode_count();
        assert_eq!(
            decodes, 1,
            "{form} n={n}: expected exactly 1 decode (at main), got {decodes}"
        );
        assert_eq!(d_stats.admitted, n - 1, "{form} n={n}: admitted");
        assert_eq!(d_stats.kept_at_generalize, n - 1, "{form} n={n}: kept");
        assert_eq!(d_stats.m56c_bound_vars, 0, "{form} n={n}: m56c_bound_vars");
        assert_info_eq(&format!("{form}_n{n}"), &e_info, &d_info);
    }
}

#[test]
fn r10_m66_chains_f_2_to_79() {
    d_equals_e_on_chains("f", 2, 79);
}

#[test]
fn r10_m66_chains_f_80_to_92() {
    d_equals_e_on_chains("f", 80, 92);
}

#[test]
fn r10_m66_chains_f_93_to_100() {
    d_equals_e_on_chains("f", 93, 100);
}

/// Includes `lambda n=2`, where round 9's D differed from E.
#[test]
fn r10_m66_chains_lambda_2_to_36() {
    d_equals_e_on_chains("lambda", 2, 36);
}

#[test]
fn r10_m66_chains_lambda_37_to_47() {
    d_equals_e_on_chains("lambda", 37, 47);
}

#[test]
fn r10_m66_chains_lambda_48_to_53() {
    d_equals_e_on_chains("lambda", 48, 53);
}

#[test]
fn r10_m66_chains_lambda_54_to_58() {
    d_equals_e_on_chains("lambda", 54, 58);
}

#[test]
fn r10_m66_chains_lambda_59_to_65() {
    d_equals_e_on_chains("lambda", 59, 65);
}

#[test]
fn r10_m66_chains_lambda_66_to_71() {
    d_equals_e_on_chains("lambda", 66, 71);
}

#[test]
fn r10_m66_chains_lambda_72_to_76() {
    d_equals_e_on_chains("lambda", 72, 76);
}

#[test]
fn r10_m66_chains_lambda_77_to_80() {
    d_equals_e_on_chains("lambda", 77, 80);
}

#[test]
fn r10_m66_chains_lambda_81_to_84() {
    d_equals_e_on_chains("lambda", 81, 84);
}

#[test]
fn r10_m66_chains_lambda_85_to_87() {
    d_equals_e_on_chains("lambda", 85, 87);
}

#[test]
fn r10_m66_chains_lambda_88_to_90() {
    d_equals_e_on_chains("lambda", 88, 90);
}

#[test]
fn r10_m66_chains_lambda_91_to_93() {
    d_equals_e_on_chains("lambda", 91, 93);
}

#[test]
fn r10_m66_chains_lambda_94_to_96() {
    d_equals_e_on_chains("lambda", 94, 96);
}

#[test]
fn r10_m66_chains_lambda_97_to_98() {
    d_equals_e_on_chains("lambda", 97, 98);
}

#[test]
fn r10_m66_chains_lambda_99_to_100() {
    d_equals_e_on_chains("lambda", 99, 100);
}

/// M66 reader coverage: `instantiated`, direct `Narrow` beside `Fwd`, higher-order `Info.calls`,
/// `sig_text` with `Into` beside `Fwd`, error-path `CallPath` notes (outermost-first), and `T6`
/// exit-variable displacement (`V -> W`).
#[test]
fn r10_m66_instantiated_printer_calls_callpath() {
    // 1. Direct Narrow need beside Fwd (Claude R9 M66_PRINT)
    let narrow_beside_fwd = "\
h0(positional f, positional m) = m.map(f);\n\
h1(positional f, positional m, positional x) = {\n\
  r = h0(f, m);\n\
  y = if x is int { x + 1 } else { 0 };\n\
  (r, y)\n\
};\n";
    let (e, _) = run_with_cfg(narrow_beside_fwd, R10Config::eager());
    let (d, st) = run_with_cfg(narrow_beside_fwd, R10Config::default());
    assert!(
        st.kept_at_generalize >= 1,
        "narrow_beside_fwd should keep Fwd"
    );
    let h1_sig = d.sigs.values().last().expect("h1 sig");
    assert!(
        h1_sig
            .needs
            .iter()
            .any(|n| matches!(n.kind, NeedKind::Fwd(_)))
            && h1_sig
                .needs
                .iter()
                .any(|n| matches!(n.kind, NeedKind::Narrow(_))),
        "h1 must hold both Fwd and direct Narrow side by side"
    );
    assert_info_eq("narrow_beside_fwd", &e, &d);

    // 2. Bad call triggering `instantiated` + `CallPath` outermost-first notes on a 6-link chain
    let mut bad_chain = chain_src(6, "f", false);
    bad_chain.push_str("bad = h5(x -> x + 1, 42);\n");
    let (e, _) = run_with_cfg(&bad_chain, R10Config::eager());
    let (d, st) = run_with_cfg(&bad_chain, R10Config::default());
    assert!(!e.errors.is_empty(), "bad_chain must produce a type error");
    assert_eq!(st.kept_at_generalize, 5, "bad_chain keeps h1..h5");
    assert!(
        e.errors[0].notes.len() >= 6,
        "expected full call-chain notes, got {}",
        e.errors[0].notes.len()
    );
    assert_info_eq("bad_chain_callpath_notes", &e, &d);

    // 3. Higher-order Info.calls (Codex R9 CASE=2) + Into beside Fwd in sig_text
    let higher_order = "\
h0(positional f, positional m) = m.map(f);\n\
h1(positional f, positional m) = h0(f, m).map(f);\n\
apply2(positional g, positional f, positional m) = g(f, m);\n\
res = apply2(h1, x -> x + 1, {\"k\" -> 0});\n\
take_int(positional x: int) = x + 1;\n\
h_into(positional f, positional m, positional z) = (h0(f, m), take_int(z));\n\
bad_into = h_into(1);\n";
    let (e, _) = run_with_cfg(higher_order, R10Config::eager());
    let (d, st) = run_with_cfg(higher_order, R10Config::default());
    assert!(st.kept_at_generalize >= 2, "higher_order keeps forwards");
    assert!(!e.errors.is_empty(), "bad_into triggers sig_text");
    assert_info_eq("higher_order_and_sig_text", &e, &d);

    // 4. T6 exit-variable displacement (Codex R8/R9): T6 held in parameter type of h10 shifts
    //    internal names across the FwdNeed and displaces the exit variable, verifying M62 bulk
    //    jump (`fresh_variable_span_stats` skipping `T6`) + M65 `Sig::digest` agree with E.
    let mut t6_chain = chain_src(10, "f", false);
    t6_chain.push_str(
        "h10(positional f, positional m, positional t: (T6, T6)) = (h9(f, m).map(f), t);\n",
    );
    let (e, _) = run_with_cfg(&t6_chain, R10Config::eager());
    let (d, st) = run_with_cfg(&t6_chain, R10Config::default());
    assert_eq!(
        st.kept_at_generalize, 10,
        "t6_chain must keep all 10 forwards including h10 holding T6"
    );
    assert_info_eq("t6_exit_displacement", &e, &d);
}

/// M66 negative controls:
/// (A) Skipping `clear_map_lambda` on decode (`keep_map_lambda_on_decode: true`) breaks `D = E`
///     on `lambda n = 2` (reproducing Round 9's exact failure).
/// (B) Decoding forwards in `generalize` (`decode_in_generalize: true`) makes
///     `generalize_needs_walked` grow quadratically instead of linearly.
#[test]
fn r10_m66_neg_keep_map_lambda_and_decode_generalize() {
    // Control A: decode without clearing Map.lambda (`clear_map_lambda = false`) breaks D=E on
    // `lambda n = 2` (exact reproduction of Round 9's failure), whereas `clear_map_lambda = true`
    // matches E identically.
    let src_l2 = chain_src(2, "lambda", false);
    let (e_l2, _) = run_with_cfg(&src_l2, R10Config::eager());
    let (d_l2, _) = run_with_cfg(&src_l2, R10Config::default());
    assert_info_eq("m66_lambda_n2_fixed", &e_l2, &d_l2);
    let e_h1 = e_l2.sigs.values().last().expect("E h1");
    let d_h1 = d_l2.sigs.values().last().expect("D h1");
    let mut decoded_broken = Vec::new();
    for n in &d_h1.needs {
        match &n.kind {
            NeedKind::Fwd(fwd) => decoded_broken.extend(fwd.decode_with_opts(n.span, false)),
            _ => decoded_broken.push(n.clone()),
        }
    }
    assert_ne!(
        e_h1.needs, decoded_broken,
        "Control A: decoding without clearing Map.lambda must disagree with E on lambda n=2"
    );

    // Control B: decode_in_generalize -> quadratic generalize_needs_walked
    let mut fixed_walked = Vec::new();
    let mut broken_walked = Vec::new();
    for n in [10usize, 20, 40] {
        let src = chain_src(n, "f", false);
        let (_, st_d) = run_with_cfg(&src, R10Config::default());
        let (_, st_b) = run_with_cfg(
            &src,
            R10Config {
                decode_in_generalize: true,
                ..R10Config::default()
            },
        );
        fixed_walked.push(st_d.generalize_needs_walked);
        broken_walked.push(st_b.generalize_needs_walked);
    }
    // Fixed D: 2*(n-1) + 2 = 2n (or 3n-1): linear (2x growth when n doubles)
    let fixed_ratio = fixed_walked[2] as f64 / fixed_walked[1] as f64;
    let broken_ratio = broken_walked[2] as f64 / broken_walked[1] as f64;
    assert!(
        fixed_ratio < 2.2,
        "fixed D generalize_needs_walked should be linear: {fixed_walked:?}"
    );
    assert!(
        broken_ratio > 3.5,
        "Control B decode_in_generalize should be quadratic: {broken_walked:?}"
    );
}

/// M31: Shared `split_sites` memo across `info.sigs` in `Ck::finish` keeps `finish_sigs_walked`
/// O(1) per link (linear total) on chains with split folds, with `D = E` (including `split_needs`),
/// while dropping the memo (`no_split_memo: true`) makes `finish_sigs_walked` quadratic and
/// skipping compact `split_needs` (`skip_compact_split_needs: true`) loses `split_needs` entries.
#[test]
fn r10_m31_finish_split_walk_constant_and_neg_controls() {
    let make_split_chain = |n: usize| -> String {
        let mut s = "top(positional xs) = xs >< max;\n".to_string();
        s.push_str("h0(positional f, positional m) = m.map(f);\n");
        for i in 1..n {
            s.push_str(&format!(
                "h{i}(positional f, positional m) = h{}(f, m).map(f);\n",
                i - 1
            ));
        }
        s.push_str(&format!(
            "a = h{}(x -> top(x), {{\"k\" -> {{\"a\" -> 1}}}});\n",
            n - 1
        ));
        s.push_str(&format!(
            "b = h{}(x -> top(x), {{\"k\" -> {{\"a\" -> 1.0f64}}}});\n",
            n - 1
        ));
        s
    };

    let mut memo_sigs = Vec::new();
    let mut nomemo_sigs = Vec::new();
    for n in [10usize, 20, 40, 80] {
        let src = make_split_chain(n);
        let (e_info, _) = run_with_cfg(&src, R10Config::eager());
        let (d_info, d_stats) = run_with_cfg(&src, R10Config::default());
        assert!(
            !e_info.split_folds.is_empty(),
            "n={n}: expected split_folds"
        );
        assert_info_eq(&format!("m31_split_n{n}"), &e_info, &d_info);
        memo_sigs.push(d_stats.finish_sigs_walked);

        if n <= 40 {
            let (_, nb_stats) = run_with_cfg(
                &src,
                R10Config {
                    no_split_memo: true,
                    ..R10Config::default()
                },
            );
            nomemo_sigs.push(nb_stats.finish_sigs_walked);
        }
    }
    // Memoized: exact constant per link across 10->20, 20->40, 40->80
    let d1 = memo_sigs[1] - memo_sigs[0];
    let d2 = memo_sigs[2] - memo_sigs[1];
    let d3 = memo_sigs[3] - memo_sigs[2];
    assert_eq!(
        d2,
        2 * d1,
        "M31 finish_sigs_walked must scale linearly: {memo_sigs:?}"
    );
    assert_eq!(
        d3,
        2 * d2,
        "M31 finish_sigs_walked must scale linearly: {memo_sigs:?}"
    );

    // Negative control A: no_split_memo grows quadratically (~4x per 2x n)
    let nomemo_ratio = nomemo_sigs[2] as f64 / nomemo_sigs[1] as f64;
    assert!(
        nomemo_ratio > 3.2,
        "M31 Control A (no_split_memo) must grow quadratically: {nomemo_sigs:?}"
    );

    // Negative control B: skip_compact_split_needs drops split_needs when a fold is nested
    // inside a lambda held by a kept FwdNeed.
    let nested_split = "\
h0(positional f, positional m) = m.map(f);\n\
h1(positional m) = h0(xs -> xs >< max, m);\n\
h2(positional m) = h1(m);\n\
a = h2({\"k\" -> {\"a\" -> 1}});\n\
b = h2({\"k\" -> {\"a\" -> 1.0f64}});\n";
    let (e_ns, _) = run_with_cfg(nested_split, R10Config::eager());
    let (d_ns, _) = run_with_cfg(nested_split, R10Config::default());
    assert_info_eq("m31_nested_split", &e_ns, &d_ns);
    assert!(
        !e_ns.split_needs.is_empty(),
        "nested_split must populate split_needs"
    );
    let (d_skip, _) = run_with_cfg(
        nested_split,
        R10Config {
            skip_compact_split_needs: true,
            ..R10Config::default()
        },
    );
    assert_ne!(
        e_ns.split_needs, d_skip.split_needs,
        "M31 Control B (skip_compact_split_needs) must lose split_needs entries"
    );
}

/// Deliverable (b) + M62: Exact per-link operation counts at `n = 10, 20, 40, 80` on both `f`
/// and `lambda` forms — constant per link for classes made, needs walked by `generalize`,
/// `share_alike`, and `finish`, names drawn, and records written — plus M62 negative controls
/// (`broken_linear_names` -> quadratic `names_drawn`, `BrokenNoCounterAdvance` -> `D != E`).
#[test]
fn r10_m62_op_counts_per_link_f_and_lambda() {
    for form in ["f", "lambda"] {
        let mut d_rows = Vec::new();
        let mut e_rows = Vec::new();
        for n in [10usize, 20, 40, 80] {
            let src = chain_src(n, form, false);
            let (_, e_st) = run_with_cfg(&src, R10Config::eager());
            let (_, d_st) = run_with_cfg(&src, R10Config::default());
            eprintln!(
                "OPCOUNT form={form} mode=D n={n} alloc_classes={} gen_done={} gen_needs={} share_alike={} finish_sigs={} finish_needs={} names_drawn={} records_written={}",
                d_st.alloc_classes,
                d_st.generalize_done_items,
                d_st.generalize_needs_walked,
                d_st.share_alike_needs_walked,
                d_st.finish_sigs_walked,
                d_st.finish_needs_walked,
                d_st.names_drawn,
                d_st.records_written,
            );
            eprintln!(
                "OPCOUNT form={form} mode=E n={n} alloc_classes={} gen_done={} gen_needs={} share_alike={} finish_sigs={} finish_needs={} names_drawn={} records_written={}",
                e_st.alloc_classes,
                e_st.generalize_done_items,
                e_st.generalize_needs_walked,
                e_st.share_alike_needs_walked,
                e_st.finish_sigs_walked,
                e_st.finish_needs_walked,
                e_st.names_drawn,
                e_st.records_written,
            );
            d_rows.push(d_st);
            e_rows.push(e_st);
        }

        // Assert exact constant per-link increments for D between (10->20), (20->40), (40->80)!
        let check_const_per_link = |name: &str, vals: [usize; 4]| {
            let inc_10_20 = vals[1] - vals[0];
            let inc_20_40 = vals[2] - vals[1];
            let inc_40_80 = vals[3] - vals[2];
            assert_eq!(
                inc_20_40,
                2 * inc_10_20,
                "{form} D {name} not constant/link: {vals:?}"
            );
            assert_eq!(
                inc_40_80,
                2 * inc_20_40,
                "{form} D {name} not constant/link: {vals:?}"
            );
        };
        check_const_per_link(
            "alloc_classes",
            [0, 1, 2, 3].map(|i| d_rows[i].alloc_classes),
        );
        check_const_per_link(
            "generalize_done_items",
            [0, 1, 2, 3].map(|i| d_rows[i].generalize_done_items),
        );
        check_const_per_link(
            "generalize_needs_walked",
            [0, 1, 2, 3].map(|i| d_rows[i].generalize_needs_walked),
        );
        check_const_per_link(
            "share_alike_needs_walked",
            [0, 1, 2, 3].map(|i| d_rows[i].share_alike_needs_walked),
        );
        check_const_per_link(
            "finish_sigs_walked",
            [0, 1, 2, 3].map(|i| d_rows[i].finish_sigs_walked),
        );
        check_const_per_link("names_drawn", [0, 1, 2, 3].map(|i| d_rows[i].names_drawn));
        check_const_per_link(
            "records_written",
            [0, 1, 2, 3].map(|i| d_rows[i].records_written),
        );

        // And confirm E is quadratic (40->80 delta > 3.5x of 20->40 delta) on classes/names/records!
        let e_names_20_40 = e_rows[2].names_drawn - e_rows[1].names_drawn;
        let e_names_40_80 = e_rows[3].names_drawn - e_rows[2].names_drawn;
        assert!(
            e_names_40_80 as f64 / e_names_20_40 as f64 > 3.5,
            "{form} E names_drawn should grow quadratically"
        );
    }

    // Also test `share_alike` active (an alike bracket site earlier in the unit so `alike_sites`
    // is non-empty on every chain link): `share_alike_needs_walked` must STILL be constant/link!
    let mut sa_d = Vec::new();
    let mut sa_e = Vec::new();
    for n in [10usize, 20, 40, 80] {
        let mut src = "dup(positional t) = (t[0], t[0]);\n".to_string();
        src.push_str(&chain_src(n, "f", false));
        let (e_info, e_st) = run_with_cfg(&src, R10Config::eager());
        let (d_info, d_st) = run_with_cfg(&src, R10Config::default());
        assert_info_eq(&format!("share_alike_active_n{n}"), &e_info, &d_info);
        sa_d.push(d_st.share_alike_needs_walked);
        sa_e.push(e_st.share_alike_needs_walked);
    }
    eprintln!("OPCOUNT share_alike_active D={sa_d:?} E={sa_e:?}");
    assert_eq!(
        sa_d[2] - sa_d[1],
        2 * (sa_d[1] - sa_d[0]),
        "D share_alike constant/link: {sa_d:?}"
    );
    assert_eq!(
        sa_d[3] - sa_d[2],
        2 * (sa_d[2] - sa_d[1]),
        "D share_alike constant/link: {sa_d:?}"
    );
    assert!(
        (sa_e[3] - sa_e[2]) as f64 / (sa_e[2] - sa_e[1]) as f64 > 3.5,
        "E share_alike should grow quadratically: {sa_e:?}"
    );

    // M62 negative control A: `broken_linear_names: true` reproduces Codex R9's quadratic
    // `fresh_name` draws (`n = 10, 20, 40, 80`).
    let mut lin_names = Vec::new();
    for n in [10usize, 20, 40, 80] {
        let src = chain_src(n, "f", false);
        let (_, st) = run_with_cfg(
            &src,
            R10Config {
                broken_linear_names: true,
                ..R10Config::default()
            },
        );
        lin_names.push(st.names_drawn);
    }
    eprintln!("NEG_M62_LINEAR_NAMES={lin_names:?}");
    let r_lin = (lin_names[3] - lin_names[2]) as f64 / (lin_names[2] - lin_names[1]) as f64;
    assert!(
        r_lin > 3.5,
        "M62 Control A (broken_linear_names) must grow quadratically: {lin_names:?}"
    );

    // M62 negative control B: `BrokenNoCounterAdvance` skips ID reservation -> diverges from E!
    let src_b = chain_src(4, "f", false);
    let (e_b, _) = run_with_cfg(&src_b, R10Config::eager());
    let (d_b, _) = run_with_cfg(
        &src_b,
        R10Config {
            store_mode: StoreMode::BrokenNoCounterAdvance,
            ..R10Config::default()
        },
    );
    assert!(
        info_eq_full("neg_m62_no_counter", &e_b, &d_b).is_err(),
        "M62 Control B (BrokenNoCounterAdvance) must diverge from E"
    );
}

/// M63: Exact `PendingLevel::SlotsM63` preserves E's exact `pending` order when a forward is
/// admitted before another class is created and later forced, whereas `BrokenAppendAtForce`
/// reorders pending classes and causes `D != E`.
#[test]
fn r10_m63_slots_preserve_order_and_neg_append_fails() {
    // 18-line Zed counterexample (Gemini R9 `test_m63b`):
    // `a1 = c0(m1, f1, g1)` (F1) and `a2 = c0(m2, f2, g2)` (F2) are admitted in order.
    // `hit2 = m2.map(f2)` forces F2 FIRST; `hit1 = m1.map(f1)` forces F1 SECOND.
    // `w1 = hit1 ++ ""` and `w2 = hit2 ++ ""` resolve F1's `$r1` and F2's `$r3` to `String`.
    // In `generalize(h)`: the `now` loop walks `pending[level]` in order, running `check_on`
    // (`split(String, $z)`) on `$r1` vs `$r3`:
    // - Under `E` and `D (SlotsM63)`: `$r1` precedes `$r3`, so `s1 = split(hit1, z)` (line 9) is
    //   recorded first on outer `$z`, and `bad = outer(42)` puts note `[1]` on line 9.
    // - Under `PendingMode::BrokenAppendAtForce`: forcing F2 before F1 appends `$r3` BEFORE `$r1`,
    //   moving note `[1]` from line 9 to line 10 AND changing `outer`'s exported signature (`D != E`).
    let prog = "\
c0(positional m, positional f, positional g) = g(m.map(f));\n\
\n\
outer(positional z) = {\n\
    h = (m1, f1, g1, m2, f2, g2) -> {\n\
        a1 = c0(m1, f1, g1);\n\
        a2 = c0(m2, f2, g2);\n\
        hit2 = m2.map(f2);\n\
        hit1 = m1.map(f1);\n\
        s1 = split(hit1, z);\n\
        s2 = split(hit2, z);\n\
        w1 = hit1 ++ \"\";\n\
        w2 = hit2 ++ \"\";\n\
        (a1, a2, s1, s2, w1, w2)\n\
    };\n\
    h\n\
};\n\
\n\
bad = outer(42);\n";
    let (e_info, _) = run_with_cfg(prog, R10Config::eager());
    let (d_ok, st_ok) = run_with_cfg(prog, R10Config::default());
    assert_eq!(st_ok.admitted, 2, "M63: both c0 calls admitted");
    assert_eq!(st_ok.forced, 2, "M63: both forwards forced");
    assert_eq!(
        st_ok.pending_slot_fills, 2,
        "M63: both pending slots filled"
    );
    assert!(!e_info.errors.is_empty(), "M63: bad = outer(42) must error");
    assert_info_eq("m63_slots_exact", &e_info, &d_ok);

    let (d_broken, st_broken) = run_with_cfg(
        prog,
        R10Config {
            pending_mode: PendingMode::BrokenAppendAtForce,
            ..R10Config::default()
        },
    );
    assert_eq!(st_broken.pending_slot_fills, 2);
    assert_ne!(
        e_info.errors, d_broken.errors,
        "M63 negative control (BrokenAppendAtForce) must move note [1] and change errors!"
    );
    let err = info_eq_full("neg_m63_append", &e_info, &d_broken)
        .expect_err("M63 negative control must fail D=E");
    assert!(
        err.contains("errors mismatch"),
        "M63 negative control failed for unexpected reason: {err}"
    );
}

/// Point 2 (M56(c) part (i)): Multi-piece and non-variable arguments are refused by `#14` under
/// `A'`, so `generalize` rewrites no need of any kept block (`m56c_bound_vars == 0`).
/// Negative control: dropping `#14` admits a compound argument `(a, b)` whose components merge,
/// causing `deep` to bind a kept-block variable (`m56c_bound_vars >= 1`) and breaking `D = E`.
#[test]
fn r10_m56c_multi_piece_refused_and_neg_drop_14() {
    // 1. Multi-piece union argument `if c { a } else { b }` is refused by `#14`.
    let src_union = "\
h0(positional f, positional m) = m.map(f);\n\
multi(positional c: bool, positional f, positional a, positional b) = {\n\
  u = if c { a } else { b };\n\
  r = h0(f, u);\n\
  _ = a + 1;\n\
  r\n\
};\n";
    let (e_u, _) = run_with_cfg(src_union, R10Config::eager());
    let (d_u, st_u) = run_with_cfg(src_union, R10Config::default());
    assert!(
        st_u.refused.get("#14").copied().unwrap_or(0) >= 1,
        "M56(c)(i): multi-piece union must be refused by #14: {:?}",
        st_u.refused
    );
    assert_eq!(
        st_u.m56c_bound_vars, 0,
        "M56(c)(i): no kept-block var bound"
    );
    assert_info_eq("m56c_multi_piece_union_ok", &e_u, &d_u);

    // 2. Tuple argument `(a, b)` where `a` and `b` later merge via `same(a, b)`:
    // Under normal D: `#14` refuses `h0(f, (a, b))`, `m56c_bound_vars == 0`, `D = E`.
    // Under dropped `#14`: `h0(f, (a, b))` IS admitted (non-`Piece::Var` tuple does not register
    // `a`/`b` in `watched_roots`), `same(a, b)` merges `b` into `a`, `h0` stays kept in `sig.needs`,
    // `deep` binds `$b -> $a` inside the kept block (`m56c_bound_vars >= 1`), AND `D != E`!
    let src_tuple = "\
same(positional x, positional y) = x + y;\n\
h0(positional f, positional m) = m.map(f);\n\
multi_tuple(positional f, positional a, positional b) = {\n\
  u = (a, b);\n\
  r = h0(f, u);\n\
  s = same(a, b);\n\
  (r, s)\n\
};\n";
    let (et, _) = run_with_cfg(src_tuple, R10Config::eager());
    let (dt_ok, stt_ok) = run_with_cfg(src_tuple, R10Config::default());
    assert!(
        stt_ok.refused.get("#14").copied().unwrap_or(0) >= 1,
        "M56(c)(i): tuple argument must be refused by #14: {:?}",
        stt_ok.refused
    );
    assert_eq!(stt_ok.m56c_bound_vars, 0);
    assert_info_eq("m56c_tuple_ok", &et, &dt_ok);

    let mut drop14 = HashSet::new();
    drop14.insert("#14".to_string());
    let (dt_bad, stt_bad) = run_with_cfg(
        src_tuple,
        R10Config {
            drop_conds: drop14,
            ..R10Config::default()
        },
    );
    assert!(
        stt_bad.admitted >= 1 && stt_bad.kept_at_generalize >= 1,
        "M56(c)(i) control: dropping #14 should admit and keep the call: {stt_bad:?}"
    );
    assert!(
        stt_bad.m56c_bound_vars >= 1,
        "M56(c)(i) control: deep must bind a merged var in the kept block! {stt_bad:?}"
    );
    assert!(
        info_eq_full("neg_m56c_drop14", &et, &dt_bad).is_err(),
        "M56(c)(i) control (drop #14) must diverge from E"
    );
}

/// Point 2 (M56(c) part (ii)): During a `merge`, `r10_force_forward` is a pure leaf copy that
/// never calls `merge`, `need`, `flow`, or `restrict`, so `forcing` is never re-entered
/// (`assert!(!self.r10.forcing)` holds) and BOTH merged roots' watchers are forced before the
/// union-find link is created (`m56c_bound_vars == 0`, `D = E`).
/// Negative control: `force_skip_second_on_merge: true` simulates a stuck `forcing` skipping the
/// second watcher on `merge(m1, m2)` — the second forward stays kept in `sig.needs` and `deep`
/// binds its merged variable (`m56c_bound_vars >= 1`), falsifying M56(c)'s "no kept need
/// rewritten by generalize" property.
#[test]
fn r10_m56c_merge_forcing_and_neg_skip_second() {
    let src = "\
same(positional x, positional y) = x + y;\n\
h0(positional f, positional m) = m.map(f);\n\
both(positional f, positional m1, positional m2) = {\n\
  a = h0(f, m1);\n\
  b = h0(f, m2);\n\
  s = same(m1, m2);\n\
  (a, b, s)\n\
};\n";
    let (e_info, _) = run_with_cfg(src, R10Config::eager());
    let (d_info, d_stats) = run_with_cfg(src, R10Config::default());
    assert_eq!(d_stats.admitted, 2, "M56(c)(ii): both h0 calls admitted");
    assert_eq!(
        d_stats.forced, 2,
        "M56(c)(ii): both forwards forced on merge"
    );
    assert!(
        d_stats.force_reasons.get("f3").copied().unwrap_or(0) >= 2,
        "M56(c)(ii): both forwards must be forced by f3 (merge): {:?}",
        d_stats.force_reasons
    );
    assert_eq!(d_stats.m56c_bound_vars, 0, "M56(c)(ii): no kept var bound");
    assert_info_eq("m56c_merge_ok", &e_info, &d_info);

    // Negative control: simulate stuck `forcing` skipping the second watcher (`b`) in `merge`.
    let (_d_bad, st_bad) = run_with_cfg(
        src,
        R10Config {
            force_skip_second_on_merge: true,
            ..R10Config::default()
        },
    );
    assert!(
        st_bad.kept_at_generalize >= 1,
        "M56(c)(ii) control: skipped second forward should survive into generalize: {st_bad:?}"
    );
    assert!(
        st_bad.m56c_bound_vars >= 1,
        "M56(c)(ii) control: deep must bind the merged variable inside the kept forward! {st_bad:?}"
    );
}

/// Landing review B2 (Sol's `landing_split_memo_diamond`, adopted): `root` holds `leaf` and
/// `branch`, and `branch` holds `leaf`. The shared split memo must give `branch` the split
/// site of `leaf`, as the full walk per signature does.
#[test]
fn r10_m31_split_memo_keeps_a_child_shared_with_a_queued_sibling() {
    use super::{Ck, Tables};
    use std::sync::Arc;
    use zedc_syntax::lex::Span;
    use zedc_types::ty::{CallPath, FoldForm, MapWord, Need, Reducer, Ty};

    let span = Span { start: 1, end: 2 };
    let direct = Need {
        on: Ty::empty(),
        kind: NeedKind::Reduce(Reducer::Max, span, FoldForm::Infix),
        result: None,
        span,
        alike: Arc::from([]),
        via: CallPath::default(),
    };
    let holds = |sig| Need {
        kind: NeedKind::Map {
            f: Ty::func(sig),
            word: MapWord::Map,
            lambda: false,
        },
        ..direct.clone()
    };
    let signature = |needs| {
        let mut sig = Sig::one(vec![], vec![], Ty::empty());
        sig.needs = needs;
        Arc::new(sig)
    };
    let leaf = signature(vec![direct.clone()]);
    let branch = signature(vec![holds(leaf.clone())]);
    let root = signature(vec![holds(leaf), holds(branch.clone())]);
    let res = zedc_resolve::resolve::resolve(&[]).expect("the empty unit resolves");
    let tables = Tables::new(&[], &res);
    let run = |no_split_memo| {
        set_next_config(R10Config {
            no_split_memo,
            ..R10Config::eager()
        });
        let mut ck = Ck::new(&tables, |_, _, _| {});
        ck.info.sigs.insert(0, root.clone());
        ck.info.sigs.insert(1, branch.clone());
        ck.info.split_folds.insert(span, "split".into());
        ck.finish();
        ck.info.split_needs
    };
    let full_walk = run(true);
    let memo = run(false);
    assert_eq!(
        full_walk.get(&1),
        Some(&vec![span]),
        "the full walk control"
    );
    assert_eq!(memo, full_walk, "the memo keeps the branch's split fold");
}

/// Landing review B2 in a program (Sol's `split-diamond.zed`): `outer` maps by `top` and by
/// `branch`, which maps by `top`; the split of `top` reaches `branch` through either walk.
#[test]
fn r10_m31_split_memo_matches_the_full_walk_on_a_diamond_program() {
    let src = "outer(positional a, positional b) = (a.map(top), b.map(branch));\n\
               branch(positional a) = a.map(top);\n\
               top(positional xs) = xs >< max;\n\
               i = top({0 -> 1});\n\
               f = top({0 -> 1.0});\n";
    for d in [false, true] {
        let base = if d {
            R10Config::default()
        } else {
            R10Config::eager()
        };
        let (full_walk, _) = run_with_cfg(
            src,
            R10Config {
                no_split_memo: true,
                ..base.clone()
            },
        );
        let (memo, _) = run_with_cfg(src, base);
        assert!(
            !full_walk.split_needs.is_empty(),
            "the program splits `top`"
        );
        assert_eq!(memo.split_needs, full_walk.split_needs, "D {d}");
    }
}

/// Landing review B3 (Sol's `lambda-key*.zed`): two maps of one operand that differ only in
/// whether the function is written as a lambda replay to one key, so the forward is refused
/// (`#7'`) and D gives E's signatures and errors.
#[test]
fn r10_m66_maps_differing_only_in_the_lambda_bit_agree_with_e() {
    let head = "id = (x: int) -> x;\nh0(positional m) = (m.map(id), m.map((x: int) -> x));\n";
    for tail in [
        "h1(positional m) = h0(m);\nh2(positional m) = h1(m);\n",
        "h1(positional m) = h0(m);\nbad = h1(42);\n",
        "h1(positional m, positional z) = {\n    before = z.map(id);\n    a, b = h0(m);\n    \
         (before, a.map(id), b)\n};\n",
    ] {
        let src = format!("{head}{tail}");
        let (e, _) = run_with_cfg(&src, R10Config::eager());
        let (d, st) = run_with_cfg(&src, R10Config::default());
        assert_info_eq(&src, &e, &d);
        assert!(st.refused.contains_key("#7'"), "{src}: {:?}", st.refused);
    }
}

/// Landing review B4 (Sol's `landing_forward_hash_contract`, adopted): a forward and its clone
/// with the cached digest summary cleared are equal, so they hash alike.
#[test]
fn r10_equal_forwards_hash_alike_with_or_without_the_digest_summary() {
    use std::hash::{DefaultHasher, Hash, Hasher};
    let (d, st) = run_with_cfg(&chain_src(3, "f", false), R10Config::default());
    assert_eq!(st.admitted, 2);
    let fwd = d
        .sigs
        .values()
        .flat_map(|s| &s.needs)
        .find_map(|n| match &n.kind {
            NeedKind::Fwd(f) => Some(f),
            _ => None,
        })
        .expect("a kept forward");
    assert!(fwd.digest_summary.is_some());
    let mut without_summary = (**fwd).clone();
    without_summary.digest_summary = None;
    let hash = |value: &zedc_types::ty::FwdNeed| {
        let mut h = DefaultHasher::new();
        value.hash(&mut h);
        h.finish()
    };
    assert_eq!(**fwd, without_summary);
    assert_eq!(hash(fwd), hash(&without_summary));
}

/// Landing review B5 (Sol's `bounds-hash.rs`, adopted): two signatures that differ only in
/// which of two variables has which bound encode to different streams and digests.
#[test]
fn r10_signature_hash_ties_each_bound_to_its_variable() {
    use zedc_types::ty::{SParam, Ty, r10_hash::encode_sig_stream};
    let signature = |left: u8, right: u8| {
        let params = ["a", "b"]
            .into_iter()
            .map(|name| SParam {
                name: name.into(),
                positional: true,
                default: None,
                range: None,
            })
            .collect();
        let (t, u) = (Ty::var("T".into()), Ty::var("U".into()));
        let mut sig = Sig::one(params, vec![t.clone(), u], t);
        sig.own.extend(["T".into(), "U".into()]);
        sig.bounds.extend([("T".into(), left), ("U".into(), right)]);
        sig
    };
    let (x, y) = (signature(1, 2), signature(2, 1));
    assert_ne!(x, y);
    assert_ne!(x.digest(), y.digest());
    for r in [2, 3, 17, 123_456_789] {
        let (dx, _, sx) = encode_sig_stream(&x, r, true);
        let (dy, _, sy) = encode_sig_stream(&y, r, true);
        assert_ne!(sx, sy, "base {r}");
        assert_ne!(dx, dy, "base {r}");
    }
}
