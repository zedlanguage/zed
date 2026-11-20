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
                for run in &fin.runs {
                    own.extend(run.names::<std::sync::Arc<str>>());
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
    // Names every field with no `..`, so a field added to `Info` fails to compile here until
    // it is compared below (landing review round 1, Opus F2).
    let Info {
        adopt: _,
        calls: _,
        placed: _,
        fits: _,
        sigs: _,
        tops: _,
        passes: _,
        quotients: _,
        follows: _,
        witness: _,
        dense: _,
        brackets: _,
        reduce: _,
        reducers: _,
        family_sums: _,
        list_concats: _,
        generic_sums: _,
        split_folds: _,
        fold_calls: _,
        split_needs: _,
        fold_reads: _,
        escaping_calls: _,
        remaps: _,
        errors: _,
        reported_literals: _,
        warnings: _,
        blocking: _,
        limits: _,
    } = e;
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
fn r10_m66_chains_f_2_to_60() {
    d_equals_e_on_chains("f", 2, 60);
}

/// Split from 2..=79, which took 8.3 s alone at load 38 and 27.4 s in a review seat at load
/// about 60 (landing review round 1, Opus F1).
#[test]
fn r10_m66_chains_f_61_to_79() {
    d_equals_e_on_chains("f", 61, 79);
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
    //    jump (`fresh_variable_span_stats_indexed` skipping `T6`) + M65 `Sig::digest` agree with E.
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
/// (A) Skipping `clear_map_lambda` on decode (`keep_map_lambda_on_decode: true`) makes the
///     decoder's output differ from E's needs on `lambda n = 2` when the decoder is called by
///     hand. This checks the decoder alone: run through the checker, the flag changes nothing
///     on the chains with or without `main` (landing review round 1, Opus F4), since a decoded
///     need reaches stored state only when it is forced or expanded by N4.
/// (B) Decoding forwards in `generalize` (`decode_in_generalize: true`) makes
///     `generalize_needs_walked` grow quadratically instead of linearly.
#[test]
fn r10_m66_neg_keep_map_lambda_and_decode_generalize() {
    // Control A: the decoder without clearing Map.lambda (`clear_map_lambda = false`) gives
    // needs that differ from E's on `lambda n = 2`, whereas `clear_map_lambda = true`
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
    // A lambda whose types hold `max` binds variables of its own, and D refuses to keep a
    // forward that holds one (`#4-own-vars`, landing round 3, Gemini L3-G1): such a forward
    // gave D and E different digests once a lambda sat beside the call. No program was found
    // where a kept forward's callee holds a split fold that the forward's own types do not
    // (tried while landing round 4: a fold in the callee, `m.map(top)`, a lambda calling
    // `top`, chains of these), so the control drops that refusal to keep the forward. This
    // program has no lambda beside the call, and D gives E's results on it with or without
    // the refusal.
    let nested_split = "\
h0(positional f, positional m) = m.map(f);\n\
h1(positional m) = h0(xs -> xs >< max, m);\n\
h2(positional m) = h1(m);\n\
a = h2({\"k\" -> {\"a\" -> 1}});\n\
b = h2({\"k\" -> {\"a\" -> 1.0f64}});\n";
    let unrefused = R10Config {
        drop_conds: ["#4-own-vars".to_string()].into_iter().collect(),
        ..R10Config::default()
    };
    let (_, refused_stats) = run_with_cfg(nested_split, R10Config::default());
    assert_eq!(
        refused_stats.admitted, 0,
        "nested_split holds `max` in a lambda: D keeps no forward"
    );
    let (e_ns, _) = run_with_cfg(nested_split, R10Config::eager());
    let (d_ns, d_ns_stats) = run_with_cfg(nested_split, unrefused.clone());
    assert!(d_ns_stats.admitted > 0, "nested_split must keep a forward");
    assert_info_eq("m31_nested_split", &e_ns, &d_ns);
    assert!(
        !e_ns.split_needs.is_empty(),
        "nested_split must populate split_needs"
    );
    let (d_skip, _) = run_with_cfg(
        nested_split,
        R10Config {
            skip_compact_split_needs: true,
            ..unrefused
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
    let hash = |value: &zedc_types::ty::FwdNeed| zed_kernel::digest::fixed_hash(value);
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

/// Landing review, Neon round 1 (B2 N4 expansion, B3 nested lambda in a callee, B4 sibling
/// lambdas in a closed function, B5 split memo, the Q3 cases): D gives E's results and
/// signature digests on each program.
#[test]
fn r10_neon_round1_programs_agree_with_e() {
    let cases: &[(&str, &str)] = &[
        (
            "n4_expansion",
            "h0(positional f, positional m) = m.map(f).map(f);\n\
             h1(positional f, positional t) = {\n  a = t[0];\n  b = t[0];\n  \
             r = h0(f, b);\n  (a, r)\n};\n",
        ),
        (
            "nested_lambda_in_callee_1",
            "h0(positional f, positional m) = m.map(x -> (y -> (f(x), y)));\n\
             h1(positional f, positional m) = h0(f, m);\n",
        ),
        (
            "nested_lambda_in_callee_2",
            "h0(positional f, positional m) = f(y -> (m, y));\n\
             h1(positional f, positional m) = h0(f, m);\n",
        ),
        (
            "sibling_lambdas_in_closed_function",
            "h0(positional f, positional m) = m.map(f).map(f);\n\
             outer(positional a, positional b) = (\n  (f, m) -> (h0(f, m), a),\n  \
             (g, n) -> (h0(g, n), b)\n);\n",
        ),
        (
            "split_memo_shared",
            "top = xs -> xs >< max;\nb = m -> m.map(top);\n\
             a(positional f, positional m) = (m.map(top), f(b));\nc(positional f) = f(b);\n\
             r1 = b({\"k\" -> {\"a\" -> 1}});\nr2 = b({\"k\" -> {\"a\" -> 1.0f64}});\n",
        ),
        (
            "rank_above_0",
            "h0(positional f, positional m) = m.map(f).map(f);\n\
             h1(positional f, positional g, positional m) = {\n  r0 = m.map(g);\n  \
             r1 = h0(f, r0);\n  r2 = r1.map(g);\n  r2\n};\n\
             h2(positional f, positional g, positional m) = h1(f, g, m);\n",
        ),
        (
            "two_forwards_chained",
            "h0(positional f, positional m) = m.map(f).map(f);\n\
             h1(positional f, positional g, positional m) = {\n  r0 = h0(f, m);\n  \
             r1 = h0(g, r0);\n  r2 = r1.map(f);\n  (r0, r2)\n};\n\
             h2(positional f, positional g, positional m) = h1(f, g, m);\n",
        ),
        (
            "returned_lambda",
            "h0(positional f, positional m) = m.map(f).map(f);\n\
             outer(positional g, positional n) = {\n  r0 = n.map(g);\n  \
             inner = (f, m) -> (h0(f, m), r0);\n  inner\n};\n",
        ),
        (
            "lambda_argument",
            "h0(positional f, positional m) = m.map(f).map(f);\n\
             outer(positional k, positional g, positional n) = {\n  r0 = n.map(g);\n  \
             k((f, m) -> (h0(f, m), r0))\n};\n",
        ),
        (
            "lambda_in_map",
            "h0(positional f, positional m) = m.map(f).map(f);\n\
             outer(positional g, positional n) = {\n  r0 = n.map(g);\n  \
             n.map(x -> ((f, m) -> (h0(f, m), x, r0)))\n};\n",
        ),
        (
            "two_lambda_arguments",
            "h0(positional f, positional m) = m.map(f).map(f);\n\
             outer(positional k, positional g, positional n) = {\n  r0 = n.map(g);\n  \
             k((f, m) -> (h0(f, m), r0), (p, q) -> (h0(p, q), r0))\n};\n",
        ),
    ];
    let mut failed = Vec::new();
    for (name, src) in cases {
        let (e, _) = run_with_cfg(src, R10Config::eager());
        let (d, st) = run_with_cfg(src, R10Config::default());
        if let Err(why) = info_eq_full(name, &e, &d) {
            failed.push(format!(
                "{why} (admitted {}, kept {})",
                st.admitted, st.kept_at_generalize
            ));
            continue;
        }
        for (id, es) in &e.sigs {
            let ds = &d.sigs[id];
            if es.digest() != ds.digest() || es != ds {
                failed.push(format!("{name}: signature {id} differs from E's"));
            }
        }
    }
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}

/// Landing review, Neon B4: forwards kept inside lambdas nested in one closed function. D
/// names every type variable as E does (results, digests and signatures equal), on sibling,
/// nested and mixed shapes; each program admits a forward, so D's path is the one tested.
#[test]
fn r10_neon_b4_nested_lambdas_name_as_e() {
    let h0 = "h0(positional f, positional m) = m.map(f).map(f);\n";
    let bodies: &[(&str, &str)] = &[
        (
            "three_siblings",
            "outer(positional a, positional b, positional c) = (\n  \
             (f, m) -> (h0(f, m), a),\n  (g, n) -> (h0(g, n), b),\n  (k, p) -> (h0(k, p), c)\n);\n",
        ),
        (
            "lambda_in_lambda",
            "outer(positional a) = (f, m) -> (h0(f, m), (g, n) -> (h0(g, n), a, m));\n",
        ),
        (
            "siblings_each_nesting",
            "outer(positional a, positional b) = (\n  \
             (f, m) -> ((g, n) -> (h0(g, n), a), h0(f, m)),\n  \
             (k, p) -> ((q, r) -> (h0(q, r), b), h0(k, p))\n);\n",
        ),
        (
            "two_forwards_in_one_sibling",
            "outer(positional a, positional b) = (\n  \
             (f, m) -> (h0(f, m), h0(f, a)),\n  (g, n) -> (h0(g, n), b)\n);\n",
        ),
    ];
    let mut failed = Vec::new();
    for (name, body) in bodies {
        let src = format!("{h0}{body}");
        let (e, _) = run_with_cfg(&src, R10Config::eager());
        let (d, st) = run_with_cfg(&src, R10Config::default());
        assert!(e.errors.is_empty(), "{name}: E errors {:?}", e.errors);
        assert!(st.admitted > 0, "{name}: no forward admitted");
        if let Err(why) = info_eq_full(name, &e, &d) {
            failed.push(why);
            continue;
        }
        for (id, es) in &e.sigs {
            let ds = &d.sigs[id];
            if es.digest() != ds.digest() || es != ds {
                failed.push(format!("{name}: signature {id} differs from E's"));
            }
        }
    }
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}

/// Neon's landing round 1 note: a decoded forward adds the variables of the results it makes
/// to the own set, and an exit is not one of them. An exit is a type of the caller, which can
/// be a variable of a function around it; such a variable is not the caller's own, so adding
/// it would make `Same::sig` and the digest's own set differ from E's. The exit of a kept
/// forward on the chain is set here to a variable `Outer` of no function in the program, and
/// the decoded own set must not hold it. Before the fix (`materialize_result_tys` in
/// `decoded_needs_and_own`) it did.
#[test]
fn r10_decoded_own_set_leaves_out_the_exits() {
    let src = chain_src(4, "f", false);
    let (d, st) = run_with_cfg(&src, R10Config::default());
    assert!(st.kept_at_generalize > 0, "no kept forward");
    let mut tried = 0;
    for sig in d.sigs.values() {
        for (i, n) in sig.needs.iter().enumerate() {
            let NeedKind::Fwd(fwd) = &n.kind else {
                continue;
            };
            if fwd.exits.is_empty() {
                continue;
            }
            let (_, own_before) = sig.decoded_needs_and_own();
            assert!(
                !own_before.contains("Outer"),
                "the program has no variable Outer"
            );
            let mut f2 = (**fwd).clone();
            for e in &mut f2.exits {
                e.1 = zedc_types::ty::Ty::var("Outer".into());
            }
            let mut s2 = (**sig).clone();
            s2.needs[i].kind = NeedKind::Fwd(std::sync::Arc::new(f2));
            let (_, own) = s2.decoded_needs_and_own();
            assert!(
                !own.contains("Outer"),
                "an exit entered the decoded own set: {own:?}"
            );
            tried += 1;
        }
    }
    assert!(tried > 0, "no kept forward with an exit on the chain");
}

/// Landing review round 2, Neon L2-B3: three bounded variables whose masks keep both
/// `sum(m + 1)` and `sum(k * (m + 1))` gave one hash at every base under the old sum.
#[test]
fn r10_signature_hash_three_bounds_keeping_both_sums_differ() {
    use zedc_types::ty::{SParam, Ty, r10_hash::encode_sig_stream};
    let signature = |names: [&str; 3], masks: [u8; 3]| {
        let params = names
            .iter()
            .map(|n| SParam {
                name: n.to_lowercase().into(),
                positional: true,
                default: None,
                range: None,
            })
            .collect();
        let tys: Vec<Ty> = names.iter().map(|n| Ty::var((*n).into())).collect();
        let mut sig = Sig::one(params, tys.clone(), tys[0].clone());
        sig.own.extend(names.iter().map(|n| (*n).into()));
        sig.bounds
            .extend(names.iter().zip(masks).map(|(n, m)| ((*n).into(), m)));
        sig
    };
    for names in [["T5", "T6", "T7"], ["$0", "$1", "$2"]] {
        let x = signature(names, [1, 4, 1]);
        let y = signature(names, [2, 2, 2]);
        assert_ne!(x, y);
        assert_ne!(x.digest(), y.digest(), "{names:?}");
        for r in [2, 3, 17, 123_456_789] {
            let (dx, _, sx) = encode_sig_stream(&x, r, true);
            let (dy, _, sy) = encode_sig_stream(&y, r, true);
            assert_ne!(sx, sy, "{names:?} base {r}");
            assert_ne!(dx, dy, "{names:?} base {r}");
        }
    }
}

/// Landing review round 2, Sol L2.C1: `pair` maps `m` to `a` and `a` to `b` and returns both;
/// `wrap` forwards to it. The use on the exit `a` must reach `wrap`'s compact block, or `#19`
/// lets `hop(f, a)` reserve a new result where E reuses the key, and D accepts `c ++ "a"`
/// with `c` numeric, which E rejects. The control calls `pair` directly.
#[test]
fn r10_inherited_use_on_an_exit_reaches_the_next_level() {
    let tail = "outer(positional f, positional m) = {\n  a, b = X(f, m);\n  c = hop(f, a);\n  (b + 1, c ++ \"a\")\n};\n";
    let head = "hop(positional f, positional m) = m.map(f);\n\
                pair(positional f, positional m) = {\n  a = m.map(f);\n  b = a.map(f);\n  (a, b)\n};\n\
                wrap(positional f, positional m) = pair(f, m);\n\
                wrap2(positional f, positional m) = wrap(f, m);\n";
    for callee in ["wrap2", "wrap", "pair"] {
        let src = format!("{head}{}", tail.replace('X', callee));
        let (e, _) = run_with_cfg(&src, R10Config::eager());
        let (d, _) = run_with_cfg(&src, R10Config::default());
        assert!(!e.errors.is_empty(), "{callee}: E accepts\n{src}");
        assert_info_eq(&format!("inherited_exit_key_{callee}"), &e, &d);
    }
}

/// Landing review round 2, Neon L2-B1: `h0` holds `x -> f(x)`, whose variables are `h0`'s,
/// not its own. In E the lambda around `h0(f, m)` holds that function through the flat `Map`
/// need, so it does not hold only its own variables; D's compact block hid the function, and
/// the digest of `outer` differed while `==` held. The control `h1` holds `f` itself.
#[test]
fn r10_function_held_in_a_forward_block_counts_for_own_variables() {
    let bodies: &[(&str, &str)] = &[
        (
            "held_lambda",
            "h0(positional f, positional m) = m.map(x -> f(x));\n\
             outer(positional a) = ((f, m) -> h0(f, m), a);\n",
        ),
        (
            "held_lambda_in_map",
            "h0(positional f, positional m) = m.map(x -> f(x));\n\
             outer(positional a, positional m) = (m.map(y -> ((f, n) -> h0(f, n))), a);\n",
        ),
        (
            "control_no_held_lambda",
            "h1(positional f, positional m) = m.map(f);\n\
             outer(positional a) = ((f, m) -> h1(f, m), a);\n",
        ),
    ];
    let mut failed = Vec::new();
    for (name, src) in bodies {
        let (e, _) = run_with_cfg(src, R10Config::eager());
        let (d, st) = run_with_cfg(src, R10Config::default());
        assert!(e.errors.is_empty(), "{name}: E errors {:?}", e.errors);
        assert!(st.admitted > 0, "{name}: no forward admitted");
        if let Err(why) = info_eq_full(name, &e, &d) {
            failed.push(why);
            continue;
        }
        for (id, es) in &e.sigs {
            let ds = &d.sigs[id];
            if es.digest() != ds.digest() || es != ds {
                failed.push(format!("{name}: signature {id} differs from E's"));
            }
        }
    }
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}

/// Landing review round 2, Sol L2.C2 (his probe, adopted): an exit of a compact block replaced
/// by a variable of a function around it, as an instantiation does, must give the digest of
/// the flat form; before, the block was hashed as if the exit were still its own result.
#[test]
fn r10_exit_replaced_by_an_outer_variable_keeps_the_flat_digest() {
    use zedc_types::ty::{Binds, Ty};

    let (d, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::default());
    let (sig, index) = d
        .sigs
        .values()
        .find_map(|s| {
            s.needs
                .iter()
                .position(|n| matches!(&n.kind, NeedKind::Fwd(f) if !f.exits.is_empty()))
                .map(|i| (s, i))
        })
        .expect("a finished signature with an exit");

    let compare = |compact: &Sig| {
        let mut flat = compact.clone();
        let (needs, own) = compact.decoded_needs_and_own();
        flat.needs = needs.into_owned();
        flat.own = own.into_owned();
        flat.facts = Default::default();
        assert_eq!(compact, &flat, "compact and flat must be equal");
        (compact.digest(), flat.digest())
    };
    let control = compare(sig);
    assert_eq!(control.0, control.1, "original forward");

    let NeedKind::Fwd(f) = &sig.needs[index].kind else {
        unreachable!();
    };
    let binds: Binds = f
        .exits
        .iter()
        .map(|(_, t)| {
            (
                t.as_var().expect("a chain exit variable").clone(),
                Ty::var("Outer".into()),
            )
        })
        .collect();
    let mut compact = sig.replace(&binds);
    for v in binds.keys() {
        compact.own.remove(v);
    }
    compact.facts = Default::default();
    let substituted = compare(&compact);
    assert_eq!(
        substituted.0, substituted.1,
        "exit replaced by an outer variable"
    );
}

/// Landing review round 3, Gemini L3-G2: the test above one level down. The exit replaced is
/// one of the callee's own forward, so the parent's digest goes through the callee's summary
/// (`build_sig_needs_summary`), which hashed the exit as the callee's own result while the flat
/// form hashes it as the outer variable it now is: `==` held and the digests differed.
#[test]
fn r10_exit_replaced_in_a_callee_keeps_the_flat_digest() {
    use std::sync::Arc;
    use zedc_types::ty::{Binds, Ty};

    let (d, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::default());
    let has_exit =
        |n: &zedc_types::ty::Need| matches!(&n.kind, NeedKind::Fwd(f) if !f.exits.is_empty());
    let (sig, index) = d
        .sigs
        .values()
        .find_map(|s| {
            s.needs
                .iter()
                .position(
                    |n| matches!(&n.kind, NeedKind::Fwd(f) if f.callee.needs.iter().any(has_exit)),
                )
                .map(|i| (s, i))
        })
        .expect("a finished signature whose forward's callee has a forward with an exit");
    let NeedKind::Fwd(outer) = &sig.needs[index].kind else {
        unreachable!();
    };
    let callee = &outer.callee;
    let inner = callee
        .needs
        .iter()
        .position(has_exit)
        .expect("the inner forward");
    let NeedKind::Fwd(inner) = &callee.needs[inner].kind else {
        unreachable!();
    };
    let binds: Binds = inner
        .exits
        .iter()
        .map(|(_, t)| {
            (
                t.as_var().expect("a chain exit variable").clone(),
                Ty::var("Outer".into()),
            )
        })
        .collect();
    let mut new_callee = callee.replace(&binds);
    for v in binds.keys() {
        new_callee.own.remove(v);
    }
    new_callee.facts = Default::default();

    let mut parent = Sig::clone(sig);
    let NeedKind::Fwd(fwd) = &mut parent.needs[index].kind else {
        unreachable!();
    };
    let fwd = Arc::make_mut(fwd);
    fwd.callee = Arc::new(new_callee);
    fwd.digest_summary = None;
    parent.facts = Default::default();

    let mut flat = parent.clone();
    let (needs, own) = parent.decoded_needs_and_own();
    flat.needs = needs.into_owned();
    flat.own = own.into_owned();
    flat.facts = Default::default();
    assert_eq!(parent, flat, "compact and flat must be equal");
    assert_eq!(
        parent.digest(),
        flat.digest(),
        "exit replaced in the callee"
    );
}

/// Landing review round 3, Codex L3.Codex-2 (his test, adopted): binding an arrow parameter to
/// an earlier result the forward reads makes that result an arrow parameter. The flat form then
/// hashes it as a parameter; the forward's cached summary had hashed it as the result of rank
/// r, so `==` held and the digests differed.
#[test]
fn r10_result_bound_to_an_arrow_parameter_keeps_the_flat_digest() {
    use zedc_types::ty::{Binds, Ty};

    let src = "h0(positional f, positional m) = m.map(f);\n\
               g(positional f, positional m, positional spare) = {\n  a = m.map(f);\n  \
               b = h0(f, a);\n  (b, spare)\n};\n";
    let (e, _) = run_with_cfg(src, R10Config::eager());
    let (d, st) = run_with_cfg(src, R10Config::default());
    assert_eq!(st.kept_at_generalize, 1);
    assert_info_eq("before the substitution", &e, &d);
    let (&id, compact) = d
        .sigs
        .iter()
        .find(|(_, s)| s.has_fwd_needs())
        .expect("a signature with a forward");
    let flat = &e.sigs[&id];
    let spare = compact.arrows[0].params[2]
        .as_var()
        .expect("spare is a variable");
    let prior = (compact.needs[0].result.as_ref())
        .and_then(|t| t.as_var())
        .expect("the first need's result is a variable");
    assert_ne!(prior, spare);
    let NeedKind::Fwd(fwd) = &compact.needs[1].kind else {
        panic!("the second need is not the forward");
    };
    assert!(fwd.sigma.iter().any(|(_, t)| t.as_var() == Some(prior)));
    assert!(fwd.digest_summary.is_some());
    assert_eq!(flat.digest(), compact.digest(), "before the substitution");

    let bind: Binds = [(spare.clone(), Ty::var(prior.clone()))]
        .into_iter()
        .collect();
    let (e2, d2) = (flat.replace(&bind), compact.replace(&bind));
    assert_eq!(e2, d2, "equality after the substitution");
    assert_eq!(e2.digest(), d2.digest(), "digest after the substitution");
}

/// Landing review round 3, Gemini L3-G1: a callee whose `Map` need holds a named function with
/// variables of its own (`id`, `k`). A forward shares the callee, so the variables of that
/// function are neither renamed with the caller's nor counted among the names in use when the
/// caller is named; E renames and counts them. Each program must give E's results and
/// signatures. The controls hold a function with no variables (`inc`), or a parameter or a
/// lambda whose variables are the callee's own, and stay admitted.
#[test]
fn r10_function_with_own_variables_held_in_a_map_agrees_with_e() {
    let id = "id(positional x) = x;\n";
    let cases: &[(&str, String)] = &[
        (
            "p23_lambda_then_call",
            format!("{id}h0(positional m) = m.map(id);\ng(positional m) = (y -> (y, y), h0(m));\n"),
        ),
        (
            "p26_call_then_lambda",
            format!("{id}h0(positional m) = m.map(id);\ng(positional m) = (h0(m), y -> (y, y));\n"),
        ),
        (
            "p24_chain_of_two",
            format!(
                "{id}h0(positional m) = m.map(id);\nh1(positional m) = h0(m);\n\
                 g(positional m) = (y -> (y, y), h1(m));\n"
            ),
        ),
        (
            "p28_with_a_parameter_function",
            format!(
                "{id}h0(positional f, positional m) = m.map(id).map(f);\n\
                 g(positional f, positional m) = (y -> (y, y), h0(f, m));\n"
            ),
        ),
        (
            "p16_closed_siblings",
            format!(
                "{id}h0(positional m) = m.map(id);\n\
                 outer(positional a) = (m -> (m, h0(m)), n -> (n, h0(n)), a);\n"
            ),
        ),
        (
            "p16_one_sibling_beside_a_lambda",
            format!(
                "{id}h0(positional m) = m.map(id).map(id);\n\
                 outer(positional a) = (y -> (y, y), m -> (m, h0(m)), a);\n"
            ),
        ),
        // A fold written in a lambda passed to a forward: its types hold `max` or `(+)`, each
        // of which binds variables of its own. Found while landing round 4: the M31 control
        // below used such a lambda.
        (
            "fold_by_max_in_a_lambda",
            "h0(positional f, positional m) = m.map(f);\n\
             h1(positional m) = h0(xs -> xs >< max, m);\n\
             h2(positional m) = h1(m);\n\
             g(positional m) = (y -> (y, y), h2(m));\n"
                .to_string(),
        ),
        (
            "fold_through_a_named_function_in_a_lambda",
            "top(positional xs) = xs >< max;\n\
             h0(positional f, positional m) = m.map(f);\n\
             h1(positional m) = h0(xs -> top(xs), m);\n\
             h2(positional m) = h1(m);\n\
             g(positional m) = (y -> (y, y), h2(m));\n\
             a = h2({\"k\" -> {\"a\" -> 1}});\n\
             b = h2({\"k\" -> {\"a\" -> 1.0f64}});\n"
                .to_string(),
        ),
        (
            "fold_by_plus_in_a_lambda",
            "h0(positional f, positional m) = m.map(f);\n\
             h1(positional m) = h0(xs -> xs >< (+), m);\n\
             h2(positional m) = h1(m);\n\
             g(positional m) = (y -> (y, y), h2(m));\n\
             a = h2({\"k\" -> {\"a\" -> 1}});\n\
             b = h2({\"k\" -> {\"a\" -> 1.0f64}});\n"
                .to_string(),
        ),
        (
            "map_by_a_named_fold",
            "top(positional xs) = xs >< max;\nh0(positional m) = m.map(top);\n\
             h1(positional m) = h0(m);\nh2(positional m) = h1(m);\n\
             g(positional m) = (y -> (y, y), h2(m));\n\
             a = h2({\"k\" -> {\"a\" -> 1}});\nb = h2({\"k\" -> {\"a\" -> 1.0f64}});\n"
                .to_string(),
        ),
        // D and E agree on this one with the refusal dropped too.
        (
            "p33_returns_a_lambda",
            "k(positional x) = y -> (x, y);\nh0(positional m) = m.map(k);\n\
             g(positional m) = (z -> (z, z), h0(m));\n"
                .to_string(),
        ),
    ];
    let controls: &[(&str, &str)] = &[
        (
            "p34_function_with_no_variables",
            "inc(positional x: int) = x + 1;\nh0(positional m) = m.map(inc);\n\
             g(positional m) = (y -> (y, y), h0(m));\n",
        ),
        (
            "parameter_function",
            "h0(positional f, positional m) = m.map(f).map(f);\n\
             g(positional f, positional m) = (y -> (y, y), h0(f, m));\n",
        ),
        (
            "lambda_of_the_callee",
            "h0(positional f, positional m) = m.map(x -> f(x)).map(f);\n\
             g(positional f, positional m) = (y -> (y, y), h0(f, m));\n",
        ),
    ];
    // Whether D gives E's results and signatures on `src`, or the first difference.
    let agrees = |name: &str, e: &Info, d: &Info| -> Result<(), String> {
        info_eq_full(name, e, d)?;
        for (id, es) in &e.sigs {
            let ds = &d.sigs[id];
            if es.digest() != ds.digest() || es != ds || !fits_sig(es, ds) || !fits_sig(ds, es) {
                return Err(format!("{name}: signature {id} differs from E's"));
            }
        }
        Ok(())
    };
    // Negative control: D with the refusal dropped.
    let unrefused = R10Config {
        drop_conds: ["#4-own-vars".to_string()].into_iter().collect(),
        ..R10Config::default()
    };
    let mut failed = Vec::new();
    let all = (cases.iter().map(|(n, s)| (*n, s.as_str(), false)))
        .chain(controls.iter().map(|(n, s)| (*n, *s, true)));
    for (name, src, control) in all {
        let (e, _) = run_with_cfg(src, R10Config::eager());
        let (d, st) = run_with_cfg(src, R10Config::default());
        assert!(e.errors.is_empty(), "{name}: E errors {:?}", e.errors);
        if control && st.admitted == 0 {
            failed.push(format!("{name}: the control admits no forward"));
        }
        if let Err(why) = agrees(name, &e, &d) {
            failed.push(why);
        }
        if !control && name != "p33_returns_a_lambda" {
            let (u, _) = run_with_cfg(src, unrefused.clone());
            if agrees(name, &e, &u).is_ok() {
                failed.push(format!("{name}: D agrees with E with the refusal dropped"));
            }
        }
    }
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}

/// One function with n forward calls of `h0` beside a held lambda of n parameters, so the
/// signature `generalize` names holds n named variables (its skip set) and n internal runs.
fn many_runs_wide_skip_src(n: usize) -> String {
    let mut s = String::from("h0(positional f, positional m) = m.map(f).map(f);\n");
    let calls: Vec<String> = (0..n).map(|i| format!("h0(a, m{i})")).collect();
    let ms: Vec<String> = (0..n).map(|i| format!("positional m{i}")).collect();
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    s.push_str(&format!(
        "g(positional a, {}) = ({}, ({}) -> ({}));\n",
        ms.join(", "),
        calls.join(", "),
        xs.join(", "),
        xs.join(", ")
    ));
    s
}

/// Step 1 of the closed-sibling repair: `generalize` names each internal run of a forward in
/// one step against the signature's skip set. Reading the whole skip set at each run made n
/// runs against n skipped names cost O(n^2); the set is now sorted once per signature.
#[test]
fn r10_generalize_runs_against_a_wide_skip_set_scale() {
    let inputs = crate::scaling::inputs(400, many_runs_wide_skip_src);
    crate::scaling::check(
        "generalize naming n internal runs against n skipped names",
        400,
        |n| {
            let (d, _) = run_with_cfg(&inputs[&n], R10Config::default());
            assert!(d.errors.is_empty(), "errors {:?}", d.errors);
        },
    );
}

/// Landing review round 2, Opus L2-C1 and Neon L2-B2: two closed lambdas inside one function,
/// each holding a call of `h0`, whose forward blocks name their inner classes. E names them in
/// one count over the function; D must give the same names, digest and equality.
#[test]
fn r10_closed_sibling_lambdas_name_as_e_does() {
    let bodies: &[(&str, &str)] = &[
        (
            "opus_two_siblings",
            "h0(positional f, positional m) = m.map(f).map(f);\n\
             outer(positional a) = ((f, m) -> (h0(f, m), a), (k, p) -> h0(k, p));\n",
        ),
        (
            "neon_two_siblings",
            "h0(positional f, positional m) = m.map(f).map(f);\n\
             outer(positional a) = ((f, m) -> h0(f, m), (g, n) -> h0(g, n), a);\n",
        ),
        (
            "three_siblings",
            "h0(positional f, positional m) = m.map(f).map(f);\n\
             outer(positional a) = ((f, m) -> (h0(f, m), a), (k, p) -> h0(k, p), (g, q) -> h0(g, q));\n",
        ),
    ];
    let mut failed = Vec::new();
    for (name, src) in bodies {
        let (e, _) = run_with_cfg(src, R10Config::eager());
        let (d, _) = run_with_cfg(src, R10Config::default());
        assert!(e.errors.is_empty(), "{name}: E errors {:?}", e.errors);
        if let Err(why) = info_eq_full(name, &e, &d) {
            failed.push(why);
            continue;
        }
        for (id, es) in &e.sigs {
            let ds = &d.sigs[id];
            if es.digest() != ds.digest() || es != ds {
                failed.push(format!("{name}: signature {id} differs from E's"));
            }
        }
    }
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}

/// Landing review round 3, bug 3b: `finished_with` leaves the names of a held forward's
/// internal runs out of the names in use, so a fresh name given to an ordinary variable of
/// the same signature can be one a run already gives, and two variables share a name. Each
/// held function's decoded variables must be as many, and named alike, as E's.
#[test]
fn r10_finished_names_never_take_a_run_name() {
    let src = "h0(positional f, positional m) = m.map(f).map(f);\n\
               outer(positional a) = ((f, m) -> h0(f, m), (g, n) -> h0(g, n), a);\n";
    let held_own = |info: &Info| -> Vec<BTreeSet<std::sync::Arc<str>>> {
        let mut out = Vec::new();
        for s in info.sigs.values() {
            for a in &s.arrows {
                a.result.each_held_fn(|h| out.push(decoded_own_vars(h)));
            }
        }
        out
    };
    let (e, _) = run_with_cfg(src, R10Config::eager());
    let (d, _) = run_with_cfg(src, R10Config::default());
    let (eo, dov) = (held_own(&e), held_own(&d));
    assert_eq!(eo.len(), dov.len(), "held functions E {eo:?} D {dov:?}");
    for (x, y) in eo.iter().zip(&dov) {
        assert_eq!(x.len(), y.len(), "a run name taken twice: E {x:?} D {y:?}");
    }
    assert_eq!(eo, dov, "held functions' variables named apart from E");
}

/// n closed sibling lambdas, each calling `h1`, which calls `h0` twice (a chain of two), beside
/// a lambda of n parameters, so the function's signature holds n named variables (a wide skip
/// set) and n forwards whose internal runs all start at the same names and must be named apart.
fn chain2_siblings_src(n: usize) -> String {
    let mut s = String::from(
        "h0(positional f, positional m) = m.map(f).map(f);\n\
         h1(positional f, positional m) = h0(f, h0(f, m));\n",
    );
    let sibs: Vec<String> = (0..n)
        .map(|i| format!("(g{i}, m{i}) -> h1(g{i}, m{i})"))
        .collect();
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    s.push_str(&format!(
        "outer(positional a) = ({}, ({}) -> ({}), a);\n",
        sibs.join(", "),
        xs.join(", "),
        xs.join(", ")
    ));
    s
}

/// Step 4 of the closed-sibling repair: the sibling forwards' runs named apart as E names them,
/// signature by signature, at small n.
#[test]
fn r10_chain2_siblings_name_as_e_does() {
    for n in 1..=4 {
        let src = chain2_siblings_src(n);
        let (e, _) = run_with_cfg(&src, R10Config::eager());
        let (d, _) = run_with_cfg(&src, R10Config::default());
        assert!(e.errors.is_empty(), "n = {n}: E errors {:?}", e.errors);
        info_eq_full(&format!("chain2 siblings n = {n}"), &e, &d).unwrap();
        for (id, es) in &e.sigs {
            let ds = &d.sigs[id];
            assert!(
                es.digest() == ds.digest() && es == ds,
                "n = {n}: signature {id} differs from E's"
            );
        }
    }
}

/// Step 4 of the closed-sibling repair: naming n sibling forwards' runs apart against a skip
/// set of n names cuts each run only where it meets a name given before, so the whole costs
/// O(n log n), not one name at a time per run.
#[test]
fn r10_chain2_siblings_wide_skip_set_scale() {
    let inputs = crate::scaling::inputs(200, chain2_siblings_src);
    crate::scaling::check(
        "finishing n sibling chain-2 forwards against n skipped names",
        200,
        |n| {
            let (d, _) = run_with_cfg(&inputs[&n], R10Config::default());
            assert!(d.errors.is_empty(), "errors {:?}", d.errors);
        },
    );
}

/// Landing review round 2, Opus C2: a function that holds a forward call and returns a lambda
/// holding one of its parameters has a variable it does not own (the lambda's) and a function
/// in it that holds one not its own (the parameter's), so its forward is decoded when it
/// finishes (`r10_promote_open_fwds`), and the forward's internal results become variables of
/// its own, as E has them. Its own variables, digest and equality must be E's. (A lambda that
/// holds an outer variable has no forward of its own, so it does not reach that path.)
#[test]
fn r10_promoted_forward_results_are_own_variables() {
    let srcs = [
        "h0(positional f, positional m) = m.map(f).map(f);\n\
         g(positional f, positional m) = (h0(f, m), (x) -> (x, m));\n",
        "h0(positional f, positional m) = m.map(f).map(f);\n\
         g(positional f, positional m) = (h0(f, m), (x) -> (x, f));\n",
    ];
    // Each signature, by node, and each function its arrows' results hold, with the internal
    // names of its forwards decoded ([`decoded_own_vars`]).
    let own_vars = |info: &Info| -> Vec<BTreeSet<std::sync::Arc<str>>> {
        let mut ids: Vec<_> = info.sigs.keys().copied().collect();
        ids.sort_unstable();
        let mut out = Vec::new();
        for id in ids {
            let s = &info.sigs[&id];
            out.push(decoded_own_vars(s));
            for a in &s.arrows {
                a.result.each_held_fn(|h| out.push(decoded_own_vars(h)));
            }
        }
        out
    };
    for src in srcs {
        let (e, _) = run_with_cfg(src, R10Config::eager());
        let (d, _) = run_with_cfg(src, R10Config::default());
        assert!(e.errors.is_empty(), "E errors {:?}", e.errors);
        assert_eq!(own_vars(&e), own_vars(&d), "own variables\n{src}");
        for (id, es) in &e.sigs {
            let ds = &d.sigs[id];
            assert!(
                es.digest() == ds.digest() && es == ds,
                "signature {id} differs\n{src}"
            );
        }
    }
}

/// D against E over a sweep of 197 programs: five leaf mapping functions, chains 0 to 2
/// links deep, 13 bodies that place the forward beside siblings, captures and a written type
/// variable, and two lambdas that capture an outer variable in a nested leaf. Codex's
/// landing round 3 audit test (land/r3/codex/audit/extra-test.rs), kept under P328 with two
/// changes: it fails if no forward is kept (so it cannot pass with D turned off), and a
/// negative control drops condition `#16` (a class at another generalize level) and requires
/// D to differ from E then (27 of the 197 differ). Dropping any other single condition
/// changes nothing on this sweep; dropping all of them gives 28 that differ (chainxr4,
/// 2026-11-19).
#[test]
fn r10_forward_sweep_of_leaves_depths_and_siblings_agrees_with_e() {
    fn sweep(cfg: &R10Config) -> (usize, usize, Vec<String>) {
        let mut srcs = Vec::new();
        for by in [
            "f",
            "x -> f(x)",
            "x -> (f(x), x)",
            "x -> f(1)",
            "(x: int) -> f(x)",
        ] {
            let base = format!("h0(positional f, positional m) = m.map({by}).map(f);\n");
            for level in 0..=2 {
                let mut head = base.clone();
                for i in 1..=level {
                    head += &format!(
                        "h{i}(positional f, positional m) = h{}(f, m).map(f);\n",
                        i - 1
                    );
                }
                for body in [
                    "((f,m) -> H(f,m), (g,n) -> H(g,n), a)",
                    "((f,m) -> (H(f,m), a), (g,n) -> H(g,n))",
                    "((f,m) -> H(f,m), (g,n) -> (H(g,n), a))",
                    "((f,m) -> { _ = H(f,m); a }, (g,n) -> H(g,n))",
                    "((f,m) -> (H(f,m), f), (g,n) -> (H(g,n), g), a)",
                    "((f,m) -> (H(f,m), m), (g,n) -> (H(g,n), n), a)",
                    "((f,m) -> { r = H(f,m); (x) -> (r, x) }, (g,n) -> H(g,n), a)",
                    "((f,m) -> { r = H(f,m); (x) -> (m, r, x) }, (g,n) -> H(g,n), a)",
                    "((f,m) -> H(a,m), (g,n) -> H(g,n))",
                    "((f,m) -> H(f,a), (g,n) -> H(g,n))",
                    "((f,m) -> (H(f,m), x -> (x, a, f)), (g,n) -> H(g,n))",
                    "((f,m) -> (H(f,m), (x: T6, y: T6) -> x), (g,n) -> H(g,n), a)",
                    "(a.map(x -> ((f,m) -> H(f,m), (g,n) -> H(g,n))))",
                ] {
                    let call = format!("h{level}");
                    srcs.push(format!(
                        "{head}outer(positional a) = {};\n",
                        body.replace('H', &call)
                    ));
                }
            }
        }
        for leaf in ["x -> (f(x), a)", "x -> f(x)"] {
            srcs.push(format!(
                "outer(positional a) = {{\n  h = (f,m) -> m.map({leaf}).map(f);\n  \
                 ((k,p) -> h(k,p), (k,p) -> h(k,p), a)\n}};"
            ));
        }
        let mut kept = 0;
        let mut mismatches = Vec::new();
        for src in &srcs {
            let (e, _) = run_with_cfg(src, R10Config::eager());
            let (d, st) = run_with_cfg(src, cfg.clone());
            kept += usize::from(st.kept_at_generalize > 0);
            if let Err(why) = info_eq_full("forward sweep", &e, &d) {
                mismatches.push(format!("{src}{why}"));
            }
        }
        (srcs.len(), kept, mismatches)
    }
    let (tried, kept, mismatches) = sweep(&R10Config::default());
    assert_eq!(tried, 197);
    assert!(kept > 0, "D kept no forward in the sweep");
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n\n"));
    let dropped = R10Config {
        drop_conds: ["#16".to_string()].into_iter().collect(),
        ..R10Config::default()
    };
    let (_, _, mismatches) = sweep(&dropped);
    assert!(
        !mismatches.is_empty(),
        "negative control: D agrees with E on the sweep with #16 dropped"
    );
}

#[test]
fn landing4_cached_digest_must_follow_need_span() {
    let (d, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::default());
    let (sig, i) = d
        .sigs
        .values()
        .find_map(|s| {
            s.needs
                .iter()
                .position(|n| matches!(&n.kind, NeedKind::Fwd(f) if f.digest_summary.is_some()))
                .map(|i| (s, i))
        })
        .unwrap();

    let compare = |compact: &Sig| {
        let mut flat = compact.clone();
        let (needs, own) = compact.decoded_needs_and_own();
        flat.needs = needs.into_owned();
        flat.own = own.into_owned();
        assert_eq!(compact, &flat);
        (compact.digest(), flat.digest())
    };
    let original = compare(sig);
    assert_eq!(original.0, original.1, "original");

    let mut revised = Sig::clone(sig);
    let need = &revised.needs[i];
    let new_span = zedc_syntax::lex::Span {
        start: need.span.start + 1,
        end: need.span.end + 1,
    };
    revised.needs[i] = need.alike_at(new_span, new_span, &need.via);
    let revised_hash = compare(&revised);
    eprintln!(
        "changed span: compact={} flat={}",
        revised_hash.0, revised_hash.1
    );

    let NeedKind::Fwd(fwd) = &mut revised.needs[i].kind else {
        unreachable!()
    };
    std::sync::Arc::make_mut(fwd).digest_summary = None;
    revised.facts = Default::default();
    let cleared = compare(&revised);
    assert_eq!(cleared.0, cleared.1, "cache cleared");
    assert_eq!(revised_hash.0, revised_hash.1, "with cached digest");
}

#[test]
fn landing4_compound_first_appearance() {
    use zedc_types::ty::{Binds, Ty};
    let (d, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::default());
    let mut compact = d
        .sigs
        .values()
        .find(|s| {
            s.needs.iter().any(|n| {
                matches!(&n.kind, NeedKind::Fwd(f)
            if f.need_count > f.exits.len() && !f.sigma.is_empty())
            })
        })
        .map(|s| Sig::clone(s))
        .unwrap();

    // Isolate the needs' first appearances from the arrow's appearances.
    for arrow in &mut compact.arrows {
        arrow.params.fill(Ty::empty());
        arrow.result = Ty::empty();
    }
    let mut flat = compact.clone();
    let (needs, own) = compact.decoded_needs_and_own();
    flat.needs = needs.into_owned();
    flat.own = own.into_owned();

    let NeedKind::Fwd(fwd) = &compact.needs[0].kind else {
        panic!("expected the forward first")
    };
    let arg = fwd.sigma[0].1.as_var().unwrap().clone();
    let earlier = Ty::var("FirstNew".into());
    let later = Ty::var("SecondNew".into());
    let compound = earlier.union(&later);
    let binds: Binds = [(arg, compound)].into_iter().collect();
    let expand_order = |s: &Sig| {
        let mut result = Vec::new();
        for i in 0..=s.vars_order().len() {
            for mark in s.vars_marks().iter().filter(|m| m.at == i) {
                for run in &mark.runs {
                    result.extend(run.names::<std::sync::Arc<str>>());
                }
            }
            result.extend(s.vars_order().get(i).cloned());
        }
        result
    };
    assert_eq!(expand_order(&compact), expand_order(&flat), "original");
    let (compact, flat) = (compact.replace(&binds), flat.replace(&binds));
    assert_eq!(compact, flat, "equal after substitution");
    eprintln!(
        "compound compact={:?} flat={:?}",
        expand_order(&compact),
        expand_order(&flat)
    );
    assert_eq!(
        expand_order(&compact),
        expand_order(&flat),
        "compound argument"
    );
}

#[test]
fn landing4_bound_name_can_also_be_free_in_a_sibling() {
    use std::sync::Arc;
    use zedc_types::ty::Ty;

    let (d, _) = run_with_cfg("id(positional x) = x;", R10Config::eager());
    let bound = d.sigs.values().next().unwrap().clone();
    let v = bound.arrows[0].params[0].as_var().unwrap();
    assert!(bound.own.contains(v));
    let ty = Ty::func(bound.clone());
    let facts = ty.var_facts();
    assert!(facts.names.contains(v));
    assert!(!facts.outer.contains(v), "closed function control");

    let mut free = Sig::clone(&bound);
    free.own.remove(v);
    let pair = Ty::tuple(vec![ty, Ty::func(Arc::new(free.clone()))]);
    let facts = pair.var_facts();
    assert!(facts.outer.iter().all(|v| facts.names.contains(v)));
    assert!(
        facts.outer.contains(v),
        "a sibling still refers to that spelling freely"
    );
    assert_eq!(
        facts.names.len(),
        facts.outer.len(),
        "the size test misses the binder"
    );
    // The bit `#4-own-vars` reads does not (landing round 4, Codex L4.Codex-own-facts).
    assert!(facts.binds, "the pair holds a function that binds `v`");
    let open = Ty::func(Arc::new(free)).var_facts();
    assert!(!open.binds, "the open function alone binds nothing");
}

#[test]
fn landing4_public_replace_reaches_hidden_results() {
    use zedc_types::ty::{Binds, Ty};
    let (d, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::default());
    let (compact, hidden) = d
        .sigs
        .values()
        .find_map(|s| {
            s.needs
                .iter()
                .find_map(|n| match &n.kind {
                    NeedKind::Fwd(f) => f.internal_result_tys().into_iter().next(),
                    _ => None,
                })
                .map(|t| (s, t.as_var().unwrap().clone()))
        })
        .unwrap();
    let mut flat = Sig::clone(compact);
    let (needs, own) = compact.decoded_needs_and_own();
    flat.needs = needs.into_owned();
    flat.own = own.into_owned();
    assert_eq!(**compact, flat);
    assert!(!compact.own.contains(&hidden));
    assert!(flat.own.contains(&hidden));
    let missing: Binds = [("FreshlyAbsent".into(), Ty::empty())]
        .into_iter()
        .collect();
    assert_eq!(
        compact.replace(&missing),
        flat.replace(&missing),
        "absent name control"
    );
    let bind: Binds = [(hidden.clone(), Ty::var("OuterReplacement".into()))]
        .into_iter()
        .collect();
    let (c, f) = (compact.replace(&bind), flat.replace(&bind));
    eprintln!(
        "replacing hidden {hidden}: compact owns it = {}, flat owns it = {}",
        c.decoded_needs_and_own().1.contains(&hidden),
        f.own.contains(&hidden)
    );
    assert_eq!(c, f);
}

/// Landing round 4, Gemini F-R4-1: a partial application `h1(1, ...)` of a function that keeps a
/// forward defers the forward's needs into the result function. D and E must agree on every
/// signature, and no unnamed class (`$k`) may reach a finished one. The one-need program is the
/// control: its forward has no internal result.
#[test]
fn landing4_partial_application_of_a_kept_forward_agrees_with_e() {
    let cases: &[(&str, &str)] = &[
        (
            "one_need_control",
            "h0(positional a, m) = m.map((x: int) -> a);\n\
             h1(positional a, m) = h0(a, m: m);\n\
             g() = h1(1, ...);\n",
        ),
        (
            "one_need_beside",
            "h0(positional a, m) = m.map((x: int) -> a);\n\
             h1(positional a, m) = h0(a, m: m);\n\
             g(positional y) = (h1(1, ...), y);\n",
        ),
        (
            "two_needs_beside",
            "h0(positional a, m) = m.map((x: int) -> a).map((x: int) -> a);\n\
             h1(positional a, m) = h0(a, m: m);\n\
             g(positional y) = (h1(1, ...), y);\n",
        ),
        (
            "two_needs",
            "h0(positional p, f, m) = m.map(f).map(f);\n\
             h1(positional p, f, m) = h0(p, f: f, m: m);\n\
             g() = h1(1, ...);\n",
        ),
        (
            "two_needs_called",
            "h0(positional p, f, m) = m.map(f).map(f);\n\
             h1(positional p, f, m) = h0(p, f: f, m: m);\n\
             g() = h1(1, ...);\n\
             k(positional f, positional m) = g()(f: f, m: m);\n",
        ),
        (
            "two_needs_misused",
            "h0(positional p, f, m) = m.map(f).map(f);\n\
             h1(positional p, f, m) = h0(p, f: f, m: m);\n\
             g() = h1(1, ...);\n\
             bad() = g()(f: x -> x + 1, m: 42);\n",
        ),
    ];
    let mut failures = Vec::new();
    for (name, src) in cases {
        let (e, _) = run_with_cfg(src, R10Config::eager());
        let (d, st) = run_with_cfg(src, R10Config::default());
        if let Err(why) = info_eq_full(name, &e, &d) {
            failures.push(format!("{name} (admitted {}): {why}", st.admitted));
        }
        // The flat signature, so a `$k` left inside a kept forward is seen too (landing
        // round 5, Claude F5-4).
        for (id, s) in &d.sigs {
            let flat = flat_of(s);
            let order = flat.vars_order();
            if order.iter().any(|v| v.starts_with('$')) {
                failures.push(format!(
                    "{name}: sig {id} holds an unnamed class: {order:?}"
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// Landing round 4, Gemini F-R4-2: the exit guard of round 4 for a callee's forward, applied to
/// a callee's direct need. A direct need's result replaced by an outer variable must keep the
/// flat digest, as `r10_exit_replaced_in_a_callee_keeps_the_flat_digest` checks for an exit.
#[test]
fn landing4_direct_result_replaced_in_a_callee_keeps_the_flat_digest() {
    use std::sync::Arc;
    use zedc_types::ty::{Binds, Ty};
    let src = "h0(positional f, positional m) = m.map(f).map(f);\n\
               h1(positional f, positional m) = h0(f, m);\n";
    let (d, st) = run_with_cfg(src, R10Config::default());
    assert_eq!(st.kept_at_generalize, 1, "h1 must keep a forward");
    let sig = (d.sigs.values().find(|s| s.has_fwd_needs())).expect("h1 keeps a forward");
    let index = (sig
        .needs
        .iter()
        .position(|n| matches!(n.kind, NeedKind::Fwd(_))))
    .expect("a forward");
    let NeedKind::Fwd(outer) = &sig.needs[index].kind else {
        unreachable!()
    };
    let callee = &outer.callee;
    assert_eq!(callee.needs.len(), 2, "h0 has two direct needs");
    let r0 = (callee.needs[0].result.as_ref().and_then(Ty::as_var))
        .expect("the first need's result is a variable")
        .clone();
    let binds: Binds = [(r0.clone(), Ty::var("Outer".into()))]
        .into_iter()
        .collect();
    let mut new_callee = callee.replace(&binds);
    new_callee.own.remove(&r0);
    new_callee.facts = Default::default();
    let mut parent = Sig::clone(sig);
    let NeedKind::Fwd(fwd) = &mut parent.needs[index].kind else {
        unreachable!()
    };
    let fwd = Arc::make_mut(fwd);
    fwd.callee = Arc::new(new_callee);
    fwd.digest_summary = None;
    parent.facts = Default::default();
    let mut flat = parent.clone();
    let (needs, own) = parent.decoded_needs_and_own();
    flat.needs = needs.into_owned();
    flat.own = own.into_owned();
    flat.facts = Default::default();
    assert_eq!(parent, flat);
    assert_eq!(
        parent.digest(),
        flat.digest(),
        "direct result replaced in the callee"
    );
}

/// Landing round 4, Gemini F-R4-3: binding the variable a held lambda reads (`a`) to `int`
/// closes the lambda. The compact signature must then answer `holds_only_own_variables` as the
/// flat one does, so that a signature holding it hashes alike.
#[test]
fn landing4_replace_closing_a_held_function_keeps_the_flat_digest() {
    use std::sync::Arc;
    use zedc_types::ty::{Binds, Carrier, Ty};
    let src = "h0(positional a, positional m) = m.map((x: int) -> a);\n\
               h1(positional a, positional m) = h0(a, m);\n";
    let (e, _) = run_with_cfg(src, R10Config::eager());
    let (d, _) = run_with_cfg(src, R10Config::default());
    assert_info_eq("closing_initial", &e, &d);
    let (&id, compact) =
        (d.sigs.iter().find(|(_, s)| s.has_fwd_needs())).expect("h1 keeps a forward");
    let flat = &e.sigs[&id];
    let a = (compact.arrows[0].params[0].as_var())
        .expect("a is a variable")
        .clone();
    let bind: Binds = [(a, Ty::carrier(Carrier::Int))].into_iter().collect();
    let (e_sub, d_sub) = (flat.replace(&bind), compact.replace(&bind));
    assert_eq!(e_sub, d_sub);
    assert_eq!(
        e_sub.holds_only_own_variables(),
        d_sub.holds_only_own_variables()
    );
    let outer_e = Sig::one(vec![], vec![], Ty::func(Arc::new(e_sub)));
    let outer_d = Sig::one(vec![], vec![], Ty::func(Arc::new(d_sub)));
    assert_eq!(outer_e, outer_d);
    assert_eq!(
        outer_e.digest(),
        outer_d.digest(),
        "held function closed by replace"
    );
}

/// `s` with its compact forwards decoded and their internal results among its own variables:
/// the flat form of the same signature.
fn flat_of(s: &Sig) -> Sig {
    let mut flat = s.clone();
    let (needs, own) = s.decoded_needs_and_own();
    flat.needs = needs.into_owned();
    flat.own = own.into_owned();
    flat.facts = Default::default();
    flat
}

/// The first signature of `d` that keeps a forward with an internal result, with its id and
/// the variable of that result.
fn sig_with_hidden(d: &Info) -> (usize, std::sync::Arc<Sig>, std::sync::Arc<str>) {
    use zedc_types::ty::Ty;
    let found = d.sigs.iter().find_map(|(id, s)| {
        (s.needs.iter())
            .find_map(|n| match &n.kind {
                NeedKind::Fwd(f) => f
                    .internal_result_tys()
                    .first()
                    .and_then(Ty::as_var)
                    .cloned(),
                _ => None,
            })
            .map(|hidden| (*id, s.clone(), hidden))
    });
    found.expect("a signature keeps a forward with an internal result")
}

/// The variables of `s` in order, with the internal names of its compact forwards where its
/// walk places them ([`Sig::vars_marks`]).
fn order_with_marks(s: &Sig) -> Vec<std::sync::Arc<str>> {
    let mut result = Vec::new();
    for i in 0..=s.vars_order().len() {
        for mark in s.vars_marks().iter().filter(|m| m.at == i) {
            for run in &mark.runs {
                result.extend(run.names::<std::sync::Arc<str>>());
            }
        }
        result.extend(s.vars_order().get(i).cloned());
    }
    result
}

/// Landing round 5, Codex L5.Codex-direct-need: `instantiated` replaces a parameter of a
/// signature that keeps a forward through the needs one by one. Replacing the parameter a held
/// lambda reads by `int` closes the lambda, which the forward's kept bit does not follow, so the
/// replacement must decode the forward as [`Sig::replace`] does.
///
/// This calls `Sig::flat_for` itself and does not go through `instantiated` (Claude L6 Q1.1).
/// The test that does is `landing6_call_fixing_a_parameter_a_held_lambda_reads_agrees_with_e`,
/// which reaches `instantiated` with a kept forward and fails, at the `Need::replace` panic,
/// with its `flat_for` removed (Gemini L6 gap 1). The 48 programs of
/// `landing6_instantiated_written` and `landing6_instantiated_forward` reach it with none.
#[test]
fn landing5_need_replace_bypasses_signature_guard() {
    use zedc_types::ty::{Binds, Carrier, Ty};
    let src = "h0(positional a, positional m) = m.map((x: int) -> a);\n\
               h1(positional a, positional m) = h0(a, m);\n";
    let (e, _) = run_with_cfg(src, R10Config::eager());
    let (d, _) = run_with_cfg(src, R10Config::default());
    assert_info_eq("before direct need replacement", &e, &d);
    let (&id, compact) = d.sigs.iter().find(|(_, s)| s.has_fwd_needs()).unwrap();
    let flat = &e.sigs[&id];
    let a = compact.arrows[0].params[0].as_var().unwrap().clone();
    let binds: Binds = [(a, Ty::carrier(Carrier::Int))].into_iter().collect();
    let flat = flat.replace(&binds);
    let control = compact.replace(&binds);
    assert_eq!(flat, control);
    assert_eq!(
        flat.holds_only_own_variables(),
        control.holds_only_own_variables()
    );
    // As `instantiated` replaces: the arrows and the needs one by one, on the signature
    // [`Sig::flat_for`] gives.
    let base = compact.flat_for(&binds);
    let mut through_needs = Sig::clone(&base);
    for ar in &mut through_needs.arrows {
        for p in &mut ar.params {
            *p = p.replace(&binds);
        }
        ar.result = ar.result.replace(&binds);
    }
    through_needs.needs = base.needs.iter().map(|n| n.replace(&binds)).collect();
    for v in binds.keys() {
        through_needs.own.remove(v);
        through_needs.held.remove(v);
    }
    through_needs.facts = Default::default();
    assert_eq!(flat, through_needs);
    assert_eq!(
        flat.holds_only_own_variables(),
        through_needs.holds_only_own_variables()
    );
}

/// Landing round 5, Codex L5.Codex-direct-map-order: a need's types mapped one by one rename
/// a forward's caller variable; its steps must follow, as a replacement of the signature makes
/// them follow, or the variables come in another order than the flat needs give. Since landing
/// round 6 `Need::map_tys` refuses a compact forward, so the need is renamed by
/// `Need::replace`, which maps its types the same way.
#[test]
fn landing5_need_map_tys_leaves_step_order_stale() {
    use zedc_types::ty::{Binds, Ty};
    let (d, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::default());
    let compact = (d.sigs.values())
        .find(|s| {
            (s.needs.iter())
                .any(|n| matches!(&n.kind, NeedKind::Fwd(f) if f.need_count > f.exits.len()))
        })
        .unwrap();
    let mut compact = Sig::clone(compact);
    for arrow in &mut compact.arrows {
        arrow.params.fill(Ty::empty());
        arrow.result = Ty::empty();
    }
    let flat = flat_of(&compact);
    assert_eq!(
        order_with_marks(&compact),
        order_with_marks(&flat),
        "original order"
    );
    let first = flat.needs[0].on.as_var().unwrap().clone();
    let bind: Binds = [(first, Ty::var("RenamedReceiver".into()))]
        .into_iter()
        .collect();
    let flat = flat.replace(&bind);
    assert_eq!(
        order_with_marks(&compact.replace(&bind)),
        order_with_marks(&flat),
        "signature replacement control"
    );
    let mut mapped = compact.clone();
    mapped.needs = (compact.needs.iter()).map(|n| n.replace(&bind)).collect();
    mapped.facts = Default::default();
    assert_eq!(order_with_marks(&mapped), order_with_marks(&flat));
}

/// Landing round 5, Codex L5.Codex-tuple-rename: a renaming of an internal result of a forward
/// held in a function inside a tuple. The tuple's row keeps bits of the names it holds, which
/// leave out the internal names, so the renaming must not keep the row whole on those bits.
#[test]
fn landing5_rename_hidden_result_inside_a_tuple() {
    use std::sync::Arc;
    use zedc_types::ty::{Binds, Ty};
    let (e, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::eager());
    let (d, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::default());
    assert_info_eq("before tuple rename", &e, &d);
    let (id, compact, hidden) = sig_with_hidden(&d);
    let flat = &e.sigs[&id];
    assert!(!compact.facts().holds(&hidden));
    assert!(flat.facts().holds(&hidden));
    let absent: Binds = [(Arc::from("AbsentAuditName"), Ty::var("AuditRename".into()))]
        .into_iter()
        .collect();
    let names: Binds = [(hidden, Ty::var("AuditRename".into()))]
        .into_iter()
        .collect();
    let wrap = |s: &Arc<Sig>| Ty::tuple(vec![Ty::func(s.clone())]);
    assert_eq!(wrap(&compact).renamed(&absent), wrap(flat).renamed(&absent));
    assert_eq!(
        Ty::func(compact.clone()).renamed(&names),
        Ty::func(flat.clone()).renamed(&names),
        "direct held signature control"
    );
    assert_eq!(wrap(&compact).renamed(&names), wrap(flat).renamed(&names));
}

/// Landing round 5, Codex L5.Codex-hidden-target and Gemini L5-B1: a replacement or a renaming
/// whose target is the name of an internal result. The flat signature then holds that name in
/// two places, so the compact one must decode to hash alike.
#[test]
fn landing5_bind_target_is_a_hidden_result() {
    use zedc_types::ty::{Binds, Ty};
    let (e, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::eager());
    let (d, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::default());
    assert_info_eq("before binding to hidden result", &e, &d);
    let (id, compact, hidden) = sig_with_hidden(&d);
    let flat = &e.sigs[&id];
    let param = compact.arrows[0].params[1].as_var().unwrap().clone();
    let fresh: Binds = [(param.clone(), Ty::var("FreshResultAlias".into()))]
        .into_iter()
        .collect();
    let (c, f) = (compact.replace(&fresh), flat.replace(&fresh));
    assert_eq!(c, f);
    assert_eq!(c.digest(), f.digest(), "fresh spelling control");
    let collision: Binds = [(param, Ty::var(hidden.clone()))].into_iter().collect();
    let (c, f) = (compact.replace(&collision), flat.replace(&collision));
    assert_eq!(c, f);
    assert_eq!(
        c.digest(),
        f.digest(),
        "replace: target is an internal result"
    );
    let (c, f) = (compact.renamed(&collision), flat.renamed(&collision));
    assert_eq!(c, f);
    assert_eq!(
        c.digest(),
        f.digest(),
        "rename: target is an internal result"
    );
    // With no arrows, so that only the forward's arguments name the parameter's variable.
    let mut bare = Sig::clone(&compact);
    for a in &mut bare.arrows {
        a.params.fill(Ty::empty());
        a.result = Ty::empty();
    }
    let bare_flat = flat_of(&bare);
    let first = bare_flat.needs[0].on.as_var().unwrap().clone();
    let collision: Binds = [(first, Ty::var(hidden))].into_iter().collect();
    let (c, f) = (bare.replace(&collision), bare_flat.replace(&collision));
    assert_eq!(c, f);
    assert_eq!(
        c.digest(),
        f.digest(),
        "no arrows: target is an internal result"
    );
}

/// Landing round 5, Codex L5.Codex-own-union: a signature intersected with itself holds the
/// own names once, as a set; the compact one must hash as the flat one does.
#[test]
fn landing5_signature_intersection_counts_own_names_once() {
    let (e, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::eager());
    let (d, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::default());
    assert_info_eq("before function intersection", &e, &d);
    let (&id, compact) = (d.sigs.iter())
        .find(|(_, s)| {
            (s.needs.iter())
                .any(|n| matches!(&n.kind, NeedKind::Fwd(f) if f.need_count > f.exits.len()))
        })
        .unwrap();
    let flat = &e.sigs[&id];
    let mut c = Sig::clone(compact);
    let mut f = Sig::clone(flat);
    c.add_arrows_of(compact);
    f.add_arrows_of(flat);
    assert_eq!(c, f);
    assert_eq!(c.digest(), f.digest(), "own names form a set");
}

/// Landing round 5, Codex: the chains decode no forward, and a call from `main` decodes one,
/// at 100 and 800 links, for both forms (`M66`).
#[test]
fn landing5_chain_decode_grid() {
    for form in ["f", "lambda"] {
        for n in [100, 800] {
            for main in [false, true] {
                let src = chain_src(n, form, main);
                reset_fwd_decode_count();
                let (info, stats) = run_with_cfg(&src, R10Config::default());
                let count = fwd_decode_count();
                assert!(info.errors.is_empty(), "{:?}", info.errors);
                assert_eq!(stats.admitted, n - 1);
                assert_eq!(stats.kept_at_generalize, n - 1);
                assert_eq!(count, u64::from(main), "{form} n={n} main={main}");
                // No forward forced, expanded at a merge or bound by M56(c) (landing round 6,
                // Codex's decode probe).
                assert_eq!(stats.forced, 0);
                assert_eq!(stats.n4_merged_expansions, 0);
                assert_eq!(stats.m56c_bound_vars, 0);
            }
        }
    }
}

/// Landing round 5, Gemini L5-B2: a replacement outside functions of the variable a held
/// lambda reads. The flat needs hold the lambda, which such a replacement does not enter, so
/// the compact forward must not carry the new name into it.
#[test]
fn landing5_replace_outside_leaves_a_held_function() {
    use zedc_types::ty::{Binds, Ty};
    for src in [
        "h0(positional a, positional m) = m.map((x: int) -> a);\n\
         h1(positional a, positional m) = h0(a, m);\n",
        // Control: no function held in the needs.
        "h0(positional f, positional m) = m.map(f);\n\
         h1(positional f, positional m) = h0(f, m);\n",
    ] {
        let (d, _) = run_with_cfg(src, R10Config::default());
        let compact = d.sigs.values().find(|s| s.has_fwd_needs()).unwrap();
        let flat = flat_of(compact);
        assert_eq!(**compact, flat);
        let a = compact.arrows[0].params[0].as_var().unwrap().clone();
        let binds: Binds = [(a, Ty::var("OuterSwap".into()))].into_iter().collect();
        let (c, f) = (
            compact.replace_outside(&binds),
            flat.replace_outside(&binds),
        );
        assert_eq!(c, f, "{src}");
        assert_eq!(c.digest(), f.digest(), "{src}");
    }
}

/// Landing round 5, Gemini L5-B3: [`Ty::renamed_runs`] with runs for a forward and a name map
/// that also names one of its internal results. The flat signature holds no forward, so its
/// runs are not used and the name map renames the result; the compact one must agree.
#[test]
fn landing5_renamed_runs_agree_with_the_flat_signature() {
    use std::collections::HashMap;
    use std::sync::Arc;
    use zedc_types::ty::{Binds, NameRun, RunRenames, SkipIndex, Ty, current_held_var_snapshot};
    let (d, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::default());
    let (_, compact, hidden) = sig_with_hidden(&d);
    let flat = Arc::new(flat_of(&compact));
    let (at, count) = (compact.needs.iter().enumerate())
        .find_map(|(i, n)| match &n.kind {
            NeedKind::Fwd(f) if f.need_count > f.exits.len() => {
                Some((i, f.need_count - f.exits.len()))
            }
            _ => None,
        })
        .unwrap();
    let run = NameRun {
        start_n: 20,
        count,
        skip: Arc::new(SkipIndex::default()),
        held: current_held_var_snapshot(),
    };
    let key = |s: &Arc<Sig>| (Arc::as_ptr(s) as usize, at);
    let runs_c = RunRenames::new(HashMap::from([(key(&compact), vec![run.clone()])]));
    let runs_f = RunRenames::new(HashMap::from([(key(&flat), vec![run])]));
    let to: Binds = [(hidden.clone(), Ty::var("T99".into()))]
        .into_iter()
        .collect();
    let sib = Arc::new(Sig::one(vec![], vec![], Ty::var(hidden)));
    let tup = |s: &Arc<Sig>| Ty::tuple(vec![Ty::func(s.clone()), Ty::func(sib.clone())]);
    let c = tup(&compact).renamed_runs(&to, &runs_c);
    let f = tup(&flat).renamed_runs(&to, &runs_f);
    assert_eq!(c, f);
}

/// The signature of `h1` in `src`, its visible variables renamed to the classes `$10`, `$11`
/// and `$101`, its forward's internal results the classes from `$100` on: a signature as the
/// checker holds it before it is finished, compact, with its flat form.
fn unfinished_pair(src: &str, clear_arrows: bool) -> (std::sync::Arc<Sig>, std::sync::Arc<Sig>) {
    use std::sync::Arc;
    use zedc_types::ty::{Binds, Ty};
    let (d, _) = run_with_cfg(src, R10Config::default());
    let orig = d.sigs.values().find(|s| s.has_fwd_needs()).unwrap();
    let arrow = &orig.arrows[0];
    let ren: Binds = [
        (
            arrow.params[0].as_var().unwrap().clone(),
            Ty::var("$10".into()),
        ),
        (
            arrow.params[1].as_var().unwrap().clone(),
            Ty::var("$11".into()),
        ),
        (
            arrow.result.as_var().unwrap().clone(),
            Ty::var("$101".into()),
        ),
    ]
    .into_iter()
    .collect();
    let mut compact = orig.renamed(&ren);
    if clear_arrows {
        for a in &mut compact.arrows {
            a.params.fill(Ty::empty());
            a.result = Ty::empty();
        }
    }
    let NeedKind::Fwd(f) = &mut compact.needs[0].kind else {
        unreachable!()
    };
    let f = Arc::make_mut(f);
    f.finish_naming = None;
    f.gen_naming = None;
    f.base_class = Some(100);
    f.digest_summary = None;
    compact.facts = Default::default();
    let flat = flat_of(&compact);
    assert_eq!(compact, flat);
    assert_eq!(compact.digest(), flat.digest());
    (Arc::new(compact), Arc::new(flat))
}

/// Landing round 5, Gemini L5-B4: settling a class a held lambda reads to `int` closes the
/// lambda, and settling a class the forward's argument holds to a union puts that union's
/// variables first where the flat needs first use it. The compact forward must be decoded
/// for both, as [`Sig::replace`] decodes it.
#[test]
fn landing5_settle_agrees_with_the_flat_signature() {
    use zedc_types::ty::{Carrier, Ty};
    let src = "h0(positional a, positional m) = m.map((x: int) -> a).map((x: int) -> a);\n\
               h1(positional a, positional m) = h0(a, m);\n";
    let (c, f) = unfinished_pair(src, false);
    let close = |v: &str| (v == "$10").then(|| Ty::carrier(Carrier::Int));
    let (sc, sf) = (c.settle(&close), f.settle(&close));
    assert_eq!(*sc, *sf);
    assert_eq!(sc.holds_only_own_variables(), sf.holds_only_own_variables());
    let outer = |s| Sig::one(vec![], vec![], Ty::func(s));
    assert_eq!(outer(sc).digest(), outer(sf).digest(), "closed by settle");
    let (c, f) = unfinished_pair(src, true);
    let both = Ty::var("FirstNew".into()).union(&Ty::var("SecondNew".into()));
    let compound = |v: &str| (v == "$11").then(|| both.clone());
    let (sc, sf) = (c.settle(&compound), f.settle(&compound));
    assert_eq!(*sc, *sf);
    assert_eq!(
        order_with_marks(&sc),
        order_with_marks(&sf),
        "settled to a union"
    );
    let (wc, wf) = (c.solved_with(&compound), f.solved_with(&compound));
    assert_eq!(wc, wf);
    assert_eq!(
        order_with_marks(&wc),
        order_with_marks(&wf),
        "solved to a union"
    );
}

/// Landing round 5, Gemini L5-B5: a forward whose callee's held lambda reads a variable of a
/// function around the callee (`OuterQ`), replaced in the caller. The flat needs hold the
/// lambda with that variable, so the compact forward must be decoded for the replacement to
/// reach it.
#[test]
fn landing5_outer_variable_of_a_held_function_is_replaced() {
    use std::sync::Arc;
    use zedc_types::ty::{Binds, Carrier, Ty};
    let src = "h0(positional a, positional m) = m.map((x: int) -> a);\n\
               h1(positional a, positional m) = h0(a, m);\n";
    let (d, _) = run_with_cfg(src, R10Config::default());
    let mut compact = Sig::clone(d.sigs.values().find(|s| s.has_fwd_needs()).unwrap());
    let NeedKind::Fwd(fwd) = &mut compact.needs[0].kind else {
        unreachable!()
    };
    let fwd = Arc::make_mut(fwd);
    let bind_q: Binds = [(fwd.sigma[0].0.clone(), Ty::var("OuterQ".into()))]
        .into_iter()
        .collect();
    fwd.callee = Arc::new(fwd.callee.replace(&bind_q));
    fwd.sigma.remove(0);
    fwd.held_names.insert("OuterQ".into());
    fwd.held_outer.insert("OuterQ".into());
    fwd.digest_summary = None;
    compact.facts = Default::default();
    let flat = flat_of(&compact);
    assert_eq!(compact, flat);
    let sub_q: Binds = [("OuterQ".into(), Ty::carrier(Carrier::Int))]
        .into_iter()
        .collect();
    let (c, f) = (compact.replace(&sub_q), flat.replace(&sub_q));
    assert_eq!(c, f);
    assert_eq!(c.digest(), f.digest());
}

/// Landing round 5, Gemini: partial applications and functions passed where a permuted
/// parameter list is wanted, checked under D and E (probes 6 and 6B; all agreed in round 5).
/// Gemini's `permuted_fits_slot_generic` is left out: its `R` is written once, so the unit
/// does not resolve.
#[test]
fn landing5_partial_and_permuted_programs_agree_with_e() {
    let cases: &[(&str, &str)] = &[
        (
            "partial_level2",
            "h0(positional p, f, m) = m.map(f).map(f);\n\
             h1(positional p, f, m) = h0(p, f: f, m: m);\n\
             g() = () -> h1(1, ...);\n",
        ),
        (
            "partial_chain2",
            "h0(positional p, f, m) = m.map(f).map(f);\n\
             h1(positional p, f, m) = h0(p, f: f, m: m).map(f);\n\
             h2(positional p, f, m) = h1(p, f: f, m: m);\n\
             g() = h2(1, ...);\n\
             k(positional f, positional m) = g()(f: f, m: m);\n",
        ),
        (
            "partial_twice_and_full",
            "h0(positional p, f, m) = m.map(f).map(f);\n\
             h1(positional p, f, m) = h0(p, f: f, m: m);\n\
             g1() = h1(1, ...);\n\
             g2() = h1(2, ...);\n\
             k(positional f, positional m) = h1(3, f: f, m: m);\n",
        ),
        (
            "partial_level2_lower_to_outer",
            "h0(positional p, f, m) = m.map(f).map(f);\n\
             h1(positional p, f, m) = h0(p, f: f, m: m);\n\
             g(positional z) = { f = () -> z(h1(1, ...)); f };\n",
        ),
        (
            "partial_half_given",
            "inc(positional x: int) = x + 1;\n\
             h0(positional a, m) = (a.map(inc).map(inc), m.map(inc).map(inc));\n\
             h1(positional a, m) = h0(a, m: m);\n\
             g(positional a) = h1(a, ...);\n\
             k(positional a, positional m) = g(a)(m: m);\n",
        ),
        (
            "partial_returning_lambda_with_fwd",
            "h0(positional f, positional m) = m.map(f).map(f);\n\
             h1(positional a, b) = (a, b, (f, m) -> h0(f, m));\n\
             g() = h1(1, ...);\n",
        ),
        (
            "partial_with_2_internal_and_other_var_order",
            "h0(positional p, f, g, m) = { r1 = m.map(f); r2 = r1.map(g); r2.map(f) };\n\
             h1(positional p, f, g, m) = h0(p, f: f, g: g, m: m);\n\
             g() = h1(1, ...);\n\
             k(positional f, positional g, positional m) = g()(f: f, g: g, m: m);\n",
        ),
        (
            "partial_on_lambda_chain",
            "h0(positional p, f, m) = m.map(x -> f(x)).map(x -> f(x));\n\
             h1(positional p, f, m) = h0(p, f: f, m: m);\n\
             g() = h1(1, ...);\n\
             k(positional f, positional m) = g()(f: f, m: m);\n",
        ),
        (
            "permuted_fits_slot_err",
            "h0(positional f, positional m) = m.map(f).map(f);\n\
             h1(f, m) = h0(f, m);\n\
             use_fn(positional g: (m: int ->? int, f: int -> int) -> (int ->? int)) = \
             g(m: {0 -> 1}, f: x -> x + 1);\n\
             res = use_fn(h1);\n",
        ),
        (
            "permuted_fits_slot_generic_ret",
            "h0(positional f, positional m) = m.map(f).map(f);\n\
             h1(f, m) = h0(f, m);\n\
             use_fn(positional g: (m: M, f: F) -> M, positional m: M, positional f: F) = \
             g(m: m, f: f);\n\
             res = use_fn(h1, {0 -> 1}, x -> x + 1);\n",
        ),
    ];
    for (name, src) in cases {
        let (e, _) = run_with_cfg(src, R10Config::eager());
        let (d, _) = run_with_cfg(src, R10Config::default());
        assert_info_eq(name, &e, &d);
    }
}

/// Landing round 5, Gemini NB3: a signature with no own variable that keeps a forward with
/// internal results binds those results as its own, as the flat one does, so
/// [`VarFacts::binds`](zedc_types::ty::VarFacts::binds) is set for both.
#[test]
fn landing5_internal_results_count_as_bound_for_var_facts() {
    use std::sync::Arc;
    use zedc_types::ty::Ty;
    let (d, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::default());
    let (_, orig, _) = sig_with_hidden(&d);
    let mut s = Sig::clone(&orig);
    s.own.clear();
    s.facts = Default::default();
    let flat = flat_of(&s);
    let vf_c = Ty::func(Arc::new(s)).var_facts();
    let vf_f = Ty::func(Arc::new(flat)).var_facts();
    assert!(vf_f.binds);
    assert_eq!(vf_c.binds, vf_f.binds);
}

/// Two maps through a held lambda that reads the parameter `a`, forwarded once: with
/// [`unfinished_pair`], `$10` is `a`, `$11` is `m`, `$100` the internal result and `$101`
/// the exit (landing round 6, Gemini).
const LANDING6_LAMBDA_SRC: &str = "h0(positional a, positional m) = m.map((x: int) -> a).map((x: int) -> a);\n\
     h1(positional a, positional m) = h0(a, m);\n";

/// The same, with the function passed as an argument (landing round 6, Codex).
const LANDING6_F_SRC: &str = "h0(positional f, positional m) = m.map(f).map(f);\n\
     h1(positional f, positional m) = h0(f, m);\n";

/// Landing round 6, Codex L6.settle-target and Gemini L6-B1: a solution that gives a visible
/// variable the name of an internal result, which `solve` leaves unsolved as `Sig::settle`
/// asks. D kept the forward compact and hashed the result in its inherited role, so the
/// settled signatures were equal with different digests (Codex: 1240585616135713484 against
/// 219136362243331606). A fresh target is the control.
#[test]
fn landing6_settle_target_is_an_internal_result() {
    use zedc_types::ty::Ty;
    for src in [LANDING6_LAMBDA_SRC, LANDING6_F_SRC] {
        for target in ["$999", "$100"] {
            let (c, f) = unfinished_pair(src, false);
            let NeedKind::Fwd(fwd) = &c.needs[0].kind else {
                unreachable!()
            };
            assert!(fwd.holds_internal("$100"));
            let solve = |v: &str| (v == "$10").then(|| Ty::var(target.into()));
            assert!(solve("$100").is_none());
            let (sc, sf) = (c.settle(&solve), f.settle(&solve));
            assert_eq!(*sc, *sf, "{src} -> {target}");
            assert_eq!(sc.digest(), sf.digest(), "{src} -> {target}");
        }
    }
}

/// Landing round 6, Codex L6.first-seen and Gemini L6-B5: `first_seen` read a compact forward
/// by its types, so it never found an internal result (`[]` against E's `["$100"]`). Asked
/// of the signature, of it held in a tuple in another, and of the visible parameters.
#[test]
fn landing6_first_seen_reads_the_flat_form() {
    use std::sync::Arc;
    use zedc_types::ty::Ty;
    for src in [LANDING6_LAMBDA_SRC, LANDING6_F_SRC] {
        for clear in [false, true] {
            let (c, f) = unfinished_pair(src, clear);
            let held =
                |s: &Arc<Sig>| Sig::one(vec![], vec![], Ty::tuple(vec![Ty::func(s.clone())]));
            for want in [
                vec!["$100"],
                vec!["$10", "$11"],
                vec!["$100", "$10", "$101"],
            ] {
                let want: HashSet<Arc<str>> = want.into_iter().map(Arc::from).collect();
                let e = f.first_seen(&want);
                assert_eq!(c.first_seen(&want), e, "{src} {want:?}");
                assert_eq!(held(&c).first_seen(&want), held(&f).first_seen(&want));
            }
            let hidden: HashSet<Arc<str>> = [Arc::from("$100")].into_iter().collect();
            assert_eq!(c.first_seen(&hidden), vec![Arc::<str>::from("$100")]);
        }
    }
}

/// Landing round 7, Codex L7.Codex-first-seen-sharing: `first_seen` walked the flat form of a
/// signature with forwards each time it met it, and each such walk began a new set of rows
/// entered, so a function held twice at each of d levels was decoded 2^(d+1) - 1 times
/// (15, 255 and 4095 at d = 4, 8, 12). Here `top` names the class of its own map after the
/// functions it holds, so the walk meets every one of them first. D agrees with E and decodes
/// at most once per distinct signature.
#[test]
fn landing7_first_seen_decodes_a_shared_function_once() {
    for depth in [4, 8, 12] {
        let mut src = String::from("h0(positional f, positional m) = m.map(f).map(f);\n");
        for i in 1..=depth {
            let j = i - 1;
            src.push_str(&format!(
                "h{i}(positional f, positional m) = (h0(f, m), h{j}, h{j});\n"
            ));
        }
        src.push_str(&format!(
            "top(positional f, positional m) = (h{depth}, m.map(f));\n"
        ));
        let (e, _) = run_with_cfg(&src, R10Config::eager());
        reset_fwd_decode_count();
        let (d, _) = run_with_cfg(&src, R10Config::default());
        let decodes = fwd_decode_count();
        let kept = d.sigs.values().filter(|s| s.has_fwd_needs()).count();
        assert_eq!(kept, depth, "depth {depth}: each h_i keeps its forward");
        assert_info_eq(&format!("depth {depth}"), &e, &d);
        assert!(
            decodes <= depth as u64 + 1,
            "depth {depth}: {decodes} decodes for {} distinct signatures",
            depth + 1
        );
    }
}

/// Landing round 7, Codex L7.Codex-held-read-order: a variable the callee's held function
/// reads from around it was put after all the forward's steps, so `vars_order` gave
/// `[U, V, OuterQ]` where the flat signature gives `[U, OuterQ, V]`: the map's receiver, then
/// the function it holds, which reads `OuterQ`, then its result. The arrows are emptied so
/// the order is that of the needs alone. Codex's probe, ported (P328).
#[test]
fn landing7_held_read_keeps_its_place_in_vars_order() {
    use std::sync::Arc;
    use zedc_types::ty::{Binds, Ty};
    let src = "h0(positional a, positional m) = m.map((x: int) -> a);\n\
               h1(positional a, positional m) = h0(a, m);\n";
    let (d, _) = run_with_cfg(src, R10Config::default());
    let mut compact = Sig::clone(d.sigs.values().find(|s| s.has_fwd_needs()).unwrap());
    for arrow in &mut compact.arrows {
        arrow.params.fill(Ty::empty());
        arrow.result = Ty::empty();
    }
    let NeedKind::Fwd(fwd) = &mut compact.needs[0].kind else {
        unreachable!()
    };
    let fwd = Arc::make_mut(fwd);
    let name: Arc<str> = "OuterQ".into();
    let bind: Binds = [(fwd.sigma[0].0.clone(), Ty::var(name.clone()))]
        .into_iter()
        .collect();
    fwd.callee = Arc::new(fwd.callee.replace(&bind));
    let (_, removed) = fwd.sigma.remove(0);
    for tie in &mut fwd.var_ties {
        tie.retain(|t| t != &removed);
    }
    fwd.var_ties.retain(|tie| tie.len() > 1);
    fwd.held_names.insert(name.clone());
    fwd.held_outer.insert(name);
    fwd.digest_summary = None;
    compact.facts = Default::default();
    let flat = flat_of(&compact);
    assert_eq!(compact, flat);
    assert_eq!(compact.digest(), flat.digest());
    let want: Vec<Arc<str>> = ["U", "OuterQ", "V"].map(Arc::from).into();
    assert_eq!(flat.vars_order(), &want[..], "control: the flat order");
    assert_eq!(compact.vars_order(), flat.vars_order());
}

/// Landing round 6, Gemini L6-B5: `Need::on_holds_var` read a compact forward's kept `.on`
/// variables only, so an internal result that a later map has as its `.on` was not found.
#[test]
fn landing6_on_holds_var_finds_an_internal_receiver() {
    let (d, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::default());
    let (_, compact, hidden) = sig_with_hidden(&d);
    let flat = flat_of(&compact);
    let on = |s: &Sig, v: &str| s.needs.iter().any(|n| n.on_holds_var(v));
    assert!(on(&flat, &hidden));
    assert_eq!(on(&compact, &hidden), on(&flat, &hidden));
    let visible = flat.needs[0].on.as_var().unwrap().clone();
    assert_eq!(on(&compact, &visible), on(&flat, &visible));
    assert!(!on(&compact, "Absent") && !on(&flat, "Absent"));
}

/// Landing round 6, Codex L6.compound-steps, Gemini L6-B3 and Claude Q2.2 (probe 1):
/// `Need::map_tys` on a compact forward's need, with the receiver replaced by `Alpha | Beta`,
/// gave the order `T, W, T5, Alpha, Beta, V` against E's `Alpha, Beta, T, W, T5, V`. One need
/// cannot keep that order, so a mapping that is not a renaming now panics; `Sig::replace` is
/// the control, which decodes.
#[test]
#[should_panic(expected = "decode it first")]
fn landing6_need_map_tys_refuses_a_compound_replacement() {
    use zedc_types::ty::{Binds, Ty};
    let (d, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::default());
    let (_, sig, _) = sig_with_hidden(&d);
    let mut sig = Sig::clone(&sig);
    for arrow in &mut sig.arrows {
        arrow.params.fill(Ty::empty());
        arrow.result = Ty::empty();
    }
    sig.facts = Default::default();
    let flat = flat_of(&sig);
    let receiver = flat.needs[0].on.as_var().unwrap().clone();
    let together = Ty::var("Alpha".into()).union(&Ty::var("Beta".into()));
    let bind: Binds = [(receiver, together)].into_iter().collect();
    assert_eq!(
        order_with_marks(&sig.replace(&bind)),
        order_with_marks(&flat.replace(&bind)),
        "control"
    );
    for n in &sig.needs {
        n.map_tys(|t| t.replace(&bind));
    }
}

/// Landing round 6, Claude Q2.2: a renaming of a visible variable onto an internal result
/// (`T -> W`) through `Need::map_tys` merged two variables in E and none in D; it panics.
/// `Need::map_tys` now refuses every compact forward, so the renaming goes through
/// `Need::replace`, which panics on it too.
#[test]
#[should_panic(expected = "decode it first")]
fn landing6_need_map_tys_refuses_a_rename_onto_an_internal_result() {
    use zedc_types::ty::{Binds, Ty};
    let (d, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::default());
    let (_, sig, hidden) = sig_with_hidden(&d);
    let flat = flat_of(&sig);
    let visible = flat.needs[0].on.as_var().unwrap().clone();
    let bind: Binds = [(visible, Ty::var(hidden))].into_iter().collect();
    for n in &sig.needs {
        n.replace(&bind);
    }
}

/// Landing round 6, Claude Q2.2 (battery): `Need::map_tys` is never shown a forward's
/// internal results nor the other needs' variables, so a mapping of an internal result
/// (`W -> int`), or of a variable no argument or exit holds onto one (`V -> W`), changed the
/// flat needs and not the compact one, with no panic. It now refuses every compact forward,
/// even with a mapping that changes nothing.
#[test]
#[should_panic(expected = "does not take a compact forward")]
fn landing6_need_map_tys_refuses_a_compact_forward() {
    let (d, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::default());
    let (_, sig, _) = sig_with_hidden(&d);
    for n in &sig.needs {
        n.map_tys(|t| t.clone());
    }
}

/// Landing round 6, Claude Q2.2 (battery): the same bindings through `Need::replace`, which
/// sees them: an internal result bound to a variable or to `int`, and a variable that is no
/// argument or exit of the forward renamed onto one, each panic; a binding of an absent name
/// is the control and keeps the need as it was.
#[test]
fn landing6_need_replace_refuses_bindings_of_internal_results() {
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use std::sync::Arc;
    use zedc_types::ty::{Binds, Carrier, Ty};
    let (d, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::default());
    let (_, sig, hidden) = sig_with_hidden(&d);
    let fwd = (sig.needs.iter())
        .find_map(|n| match &n.kind {
            NeedKind::Fwd(f) => f.holds_internal(&hidden).then(|| n.clone()),
            _ => None,
        })
        .unwrap();
    let NeedKind::Fwd(f) = &fwd.kind else {
        unreachable!()
    };
    let held: Vec<Arc<str>> = (f.sigma.iter().map(|(_, t)| t))
        .chain(f.exits.iter().map(|(_, t)| t))
        .filter_map(Ty::as_var)
        .cloned()
        .collect();
    let flat = flat_of(&sig);
    let outside = (flat.vars_order().iter())
        .find(|v| !held.contains(v) && !f.holds_internal(v))
        .expect("a variable of the signature that the forward's arguments and exits do not hold")
        .clone();
    let panics = |b: &Binds| catch_unwind(AssertUnwindSafe(|| fwd.replace(b))).is_err();
    let one = |k: &Arc<str>, t: Ty| -> Binds { [(k.clone(), t)].into_iter().collect() };
    assert!(panics(&one(&hidden, Ty::var("Fresh".into()))), "W -> Fresh");
    assert!(panics(&one(&hidden, Ty::carrier(Carrier::Int))), "W -> int");
    assert!(panics(&one(&outside, Ty::var(hidden.clone()))), "V -> W");
    let absent = one(&Arc::from("AbsentAuditName"), Ty::carrier(Carrier::Int));
    assert!(!panics(&absent));
    assert_eq!(fwd.replace(&absent), fwd);
}

/// Landing round 6: `Need::with_held_fns`, which the checker uses on a compact forward in
/// place of `Need::map_tys`, keeps it compact and equal to itself when each held function is
/// kept, and the signature with it agrees with E. Landing round 7, Gemini B4: the round-6
/// test counted the calls over all needs, and every call came from the direct `map` need,
/// none from the forward; the two are now counted apart, and the forward's are 0, as its
/// types hold no function (its callee's needs hold the lambda, which it does not enter).
#[test]
fn landing6_need_with_held_fns_keeps_a_compact_forward() {
    let (d, _) = run_with_cfg(&chain_src(3, "lambda", false), R10Config::default());
    let (_, sig, _) = sig_with_hidden(&d);
    let (mut fwd_calls, mut direct_calls) = (0, 0);
    let mut kept = Sig::clone(&sig);
    kept.needs = (sig.needs.iter())
        .map(|n| {
            let is_fwd = matches!(n.kind, NeedKind::Fwd(_));
            n.with_held_fns(|f| {
                *(if is_fwd {
                    &mut fwd_calls
                } else {
                    &mut direct_calls
                }) += 1;
                f.clone()
            })
        })
        .collect();
    assert_eq!(fwd_calls, 0, "the forward's own types hold no function");
    assert!(direct_calls > 0, "the direct map need holds the lambda");
    assert_eq!(kept.needs, sig.needs);
    assert!(kept.has_fwd_needs());
    kept.facts = Default::default();
    assert_eq!(kept, flat_of(&sig));
    assert_eq!(kept.digest(), flat_of(&sig).digest());
}

/// Landing round 7, Gemini B4: on a compact forward `Need::with_held_fns` gives `each` only
/// the functions of the types the forward shows, not those its callee's needs hold, so a
/// mapping that changes a function differs from the same mapping of the flat needs (Gemini's
/// probe, ported, P328, as a test of that documented limit). The checker's caller,
/// `r10_promote_open_fwds`, is shown to agree with E on a chain whose callee's leaf need
/// holds a lambda that itself calls a chain and reads a parameter from around it.
#[test]
fn landing7_need_with_held_fns_leaves_the_callee() {
    use std::sync::Arc;
    use zedc_types::ty::{Carrier, SParam, Ty};
    let src = "h0(positional a, positional m) = m.map((x: int) -> a);\n\
               h1(positional a, positional m) = h0(a, m);\n";
    let (e, _) = run_with_cfg(src, R10Config::eager());
    let (d, _) = run_with_cfg(src, R10Config::default());
    let (&id, compact) = d.sigs.iter().find(|(_, s)| s.has_fwd_needs()).unwrap();
    let flat = &e.sigs[&id];
    assert_eq!(**compact, **flat);
    let param = SParam {
        name: "x".into(),
        positional: true,
        default: None,
        range: None,
    };
    let to_bool = Arc::new(Sig::one(
        vec![param],
        vec![Ty::carrier(Carrier::Int)],
        Ty::carrier(Carrier::Bool),
    ));
    let mapped = |s: &Sig, calls: &mut usize| {
        let mut out = s.clone();
        out.needs = (s.needs.iter())
            .map(|n| {
                n.with_held_fns(|_| {
                    *calls += 1;
                    to_bool.clone()
                })
            })
            .collect();
        out.facts = Default::default();
        out
    };
    let (mut d_calls, mut e_calls) = (0, 0);
    let (dm, em) = (mapped(compact, &mut d_calls), mapped(flat, &mut e_calls));
    assert_eq!(
        (d_calls, e_calls),
        (0, 1),
        "the callee's lambda is not entered"
    );
    assert_ne!(dm, em);
    assert_eq!(dm, **compact, "the compact forward is kept as it was");

    // The checker's caller: a lambda in the leaf need of a kept forward that calls a chain
    // and reads `a` from around it. D agrees with E.
    let src = "h0(positional a, positional m) = m.map((x: int) -> a);\n\
               h1(positional a, positional m) = h0(a, m).map((x: int) -> a);\n\
               k0(positional a, positional m, positional ms) = ms.map((y: int) -> h1(a, m));\n\
               k1(positional a, positional m, positional ms) = k0(a, m, ms);\n\
               k2(positional a, positional m, positional ms) = k1(a, m, ms);\n";
    let (e, _) = run_with_cfg(src, R10Config::eager());
    let (d, _) = run_with_cfg(src, R10Config::default());
    assert!(e.errors.is_empty(), "{:?}", e.errors);
    assert_info_eq("a lambda calling a chain in a leaf need", &e, &d);
}

/// Landing round 6, Codex and Gemini controls for the two panics above: swapping two
/// arguments and renaming one onto another keep the forward compact and agree with E on
/// order, `==` and digest. The needs are renamed by `Need::replace`, as `Need::map_tys`
/// refuses a compact forward.
#[test]
fn landing6_need_map_tys_renamings_agree_with_e() {
    use zedc_types::ty::{Binds, Ty};
    let (d, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::default());
    let (_, sig, _) = sig_with_hidden(&d);
    let mut sig = Sig::clone(&sig);
    for arrow in &mut sig.arrows {
        arrow.params.fill(Ty::empty());
        arrow.result = Ty::empty();
    }
    sig.facts = Default::default();
    let flat = flat_of(&sig);
    let NeedKind::Fwd(fwd) = &sig.needs[0].kind else {
        unreachable!()
    };
    let v0 = fwd.sigma[0].1.as_var().unwrap().clone();
    let v1 = fwd.sigma[1].1.as_var().unwrap().clone();
    let map = |s: &Sig, binds: &Binds| {
        let mut s = s.clone();
        s.needs = s.needs.iter().map(|n| n.replace(binds)).collect();
        s.facts = Default::default();
        s
    };
    let swap: Binds = [
        (v0.clone(), Ty::var(v1.clone())),
        (v1.clone(), Ty::var(v0.clone())),
    ]
    .into_iter()
    .collect();
    let merge: Binds = [(v0, Ty::var(v1))].into_iter().collect();
    for binds in [swap, merge] {
        let (c, e) = (map(&sig, &binds), map(&flat, &binds));
        assert_eq!(order_with_marks(&c), order_with_marks(&e));
        assert_eq!(c, e);
        assert_eq!(c.digest(), e.digest());
    }
}

/// Landing round 6, Claude Q2.2 (probe 2): the parameter a held lambda reads, bound to `int`
/// through `Need::replace` on each need without `Sig::flat_for`, gave
/// `holds_only_own_variables` false in D and true in E. `Need::replace` now panics on a
/// binding that must decode; `Sig::replace` is the control.
#[test]
#[should_panic(expected = "decode it first")]
fn landing6_need_replace_refuses_a_binding_that_must_decode() {
    use zedc_types::ty::{Binds, Carrier, Ty};
    let src = "h0(positional a, positional m) = m.map((x: int) -> a);\n\
               h1(positional a, positional m) = h0(a, m);\n";
    let (e, _) = run_with_cfg(src, R10Config::eager());
    let (d, _) = run_with_cfg(src, R10Config::default());
    let (&id, compact) = d.sigs.iter().find(|(_, s)| s.has_fwd_needs()).unwrap();
    let a = compact.arrows[0].params[0].as_var().unwrap().clone();
    let binds: Binds = [(a, Ty::carrier(Carrier::Int))].into_iter().collect();
    assert_eq!(
        e.sigs[&id].replace(&binds),
        compact.replace(&binds),
        "control"
    );
    for n in &compact.needs {
        n.replace(&binds);
    }
}

/// Landing round 6, Gemini (non-blocking coverage gap): with `Sig::flat_for` taken out of
/// `Ck::instantiated`, every test passed, as none called a function keeping a forward with an
/// argument that fixes the parameter its held lambda reads. These calls do; the forward is
/// kept, so the call meets it compact. Only the programs with a written function type reach
/// `instantiated` (`ties_in_fns`); with the line taken out they fail at the panic of
/// `Need::replace` (measured in landing round 6).
#[test]
fn landing6_call_fixing_a_parameter_a_held_lambda_reads_agrees_with_e() {
    let lib = "h0(positional a, positional m) = m.map((x: int) -> a);\n\
               h1(positional a, positional m) = h0(a, m);\n";
    // A written function type holding a variable makes the call instantiate the signature
    // before applying it (`ties_in_fns`), where the literal fixes `T`.
    let typed = "h0(positional a, positional m) = m.map((x: int) -> a);\n\
                 h1(positional a: T, positional f: (T) -> T, positional m) = h0(f(a), m);\n";
    let calls = [
        (
            lib,
            "main(m: MainArgs) {\n  v = h1(1, {\"k\" -> 0})[\"k\"];\n  m.stdout <- [\"${v}\"];\n}\n",
        ),
        (
            lib,
            "main(m: MainArgs) {\n  v = h1(\"s\", {\"k\" -> 0})[\"k\"];\n  m.stdout <- [v];\n}\n",
        ),
        (lib, "g(positional m) = h1(2, m);\n"),
        (
            typed,
            "main(m: MainArgs) {\n  v = h1(1, x -> x + 1, {\"k\" -> 0})[\"k\"];\n  m.stdout <- [\"${v}\"];\n}\n",
        ),
        (typed, "g(positional m) = h1(2, x -> x, m);\n"),
    ];
    for (lib, call) in calls {
        let src = format!("{lib}{call}");
        let (e, _) = run_with_cfg(&src, R10Config::eager());
        assert!(e.errors.is_empty(), "{src}\n{:?}", e.errors);
        let (d, stats) = run_with_cfg(&src, R10Config::default());
        assert!(stats.kept_at_generalize >= 1, "{src}: a forward is kept");
        assert_info_eq(&src, &e, &d);
    }
}

/// The `held_outer` fixture of [`landing5_outer_variable_of_a_held_function_is_replaced`],
/// or the same with the variable a class read by the held function (`held_classes`).
fn landing6_held_read_pair(class: bool) -> (Sig, Sig) {
    use std::sync::Arc;
    use zedc_types::ty::{Binds, FwdVarStep, Ty};
    let src = "h0(positional a, positional m) = m.map((x: int) -> a);\n\
               h1(positional a, positional m) = h0(a, m);\n";
    let (d, _) = run_with_cfg(src, R10Config::default());
    let mut compact = Sig::clone(d.sigs.values().find(|s| s.has_fwd_needs()).unwrap());
    let NeedKind::Fwd(fwd) = &mut compact.needs[0].kind else {
        unreachable!()
    };
    let fwd = Arc::make_mut(fwd);
    let name: Arc<str> = if class { "$99".into() } else { "OuterQ".into() };
    let bind: Binds = [(fwd.sigma[0].0.clone(), Ty::var(name.clone()))]
        .into_iter()
        .collect();
    fwd.callee = Arc::new(fwd.callee.replace(&bind));
    // The caller's variable for the argument goes with it, from the steps, ties and `.on`
    // variables too (landing round 7, Claude F1: left in the steps, it put a stale `T` at the
    // end of D's order with the arrows emptied).
    let (_, gone) = fwd.sigma.remove(0);
    if let Some(gone) = gone.as_var().cloned() {
        (fwd.var_steps).retain(|st| !matches!(st, FwdVarStep::ClassVar(v) if *v == gone));
        fwd.var_ties
            .iter_mut()
            .for_each(|g| g.retain(|t| *t != Ty::var(gone.clone())));
        fwd.var_ties.retain(|g| !g.is_empty());
        fwd.on_vars.retain(|t| *t != Ty::var(gone.clone()));
    }
    match class {
        true => {
            fwd.held_classes.insert(name);
        }
        false => {
            fwd.held_names.insert(name.clone());
            fwd.held_outer.insert(name);
        }
    }
    fwd.digest_summary = None;
    compact.facts = Default::default();
    let flat = flat_of(&compact);
    assert_eq!(compact, flat);
    assert_eq!(compact.digest(), flat.digest());
    (compact, flat)
}

/// Landing round 6, Gemini L6-B2: a variable the callee's held functions read from around it
/// was missed by `Need::vars_in`, so `solved_with` did not solve it (D and E digests
/// 1679879502987995254 and 1734963554527029029), `vars_order` left it out (`[T, U, V]`
/// against `[T, U, V, OuterQ]`), and `fits_sig` accepted two signatures that swap it with
/// another (E false, D true); and a class read so (`held_classes`) was not tested by the
/// guards of `Sig::replace` and `Sig::settle`. The checker keeps no such forward (`#4`,
/// `#4-outer`); these are of the public API.
///
/// The orders are compared exactly, also with the arrows emptied, so that the needs alone
/// give them; per need (`Need::vars_in`) as sets, as documented there. Landing round 7,
/// Claude F1 found D's order different with the arrows emptied (`[U, OuterQ, V, T]` against
/// `[U, OuterQ, V]`, rerun as a control); the cause was the fixture, which removed the
/// argument but left its variable `T` in the forward's steps. With it removed too, the orders
/// agree.
#[test]
fn landing6_variables_read_by_held_functions_agree_with_e() {
    use std::sync::Arc;
    use zedc_types::ty::{Binds, Carrier, Ty, Vars};
    let int = || Ty::carrier(Carrier::Int);
    let (c, f) = landing6_held_read_pair(false);
    let solve = |v: &str| (v == "OuterQ").then(int);
    let (sc, sf) = (c.solved_with(&solve), f.solved_with(&solve));
    assert_eq!(sc, sf);
    assert_eq!(sc.digest(), sf.digest());
    let (c, f) = (Arc::new(c), Arc::new(f));
    let (seen, want) = (c.vars_order(), f.vars_order());
    assert!(seen.iter().any(|v| &**v == "OuterQ"), "{seen:?}");
    assert_eq!(seen, want);
    let pair = |h1: &Arc<Sig>| {
        let make = |a: &str, b: &str| {
            let mut s = Sig::one(
                h1.params.clone(),
                vec![Ty::var(a.into()), Ty::var(b.into())],
                Ty::func(h1.clone()),
            );
            s.own.insert("OuterQ".into());
            s.own.insert("OuterR".into());
            s
        };
        (make("OuterQ", "OuterR"), make("OuterR", "OuterQ"))
    };
    let ((e1, e2), (d1, d2)) = (pair(&f), pair(&c));
    assert!(fits_sig(&e1, &e1) && fits_sig(&d1, &d1), "control");
    assert_eq!(fits_sig(&d1, &d2), fits_sig(&e1, &e2));
    let (c, f) = landing6_held_read_pair(true);
    // Landing review round 8, Gemini BLOCKING-2: the class the held function reads from around
    // is one a signature around may own ([`VarFacts::outer_classes`], read by `fits_sig`); D
    // left it out (`{}` against `{"$99"}`).
    let (oc, of) = (&c.facts().outer_classes, &f.facts().outer_classes);
    assert!(of.contains("$99"), "{of:?}");
    assert_eq!(oc, of);
    let sub: Binds = [("$99".into(), int())].into_iter().collect();
    assert_eq!(c.replace(&sub), f.replace(&sub));
    let solve = |v: &str| (v == "$99").then(int);
    let (sc, sf) = (Arc::new(c).settle(&solve), Arc::new(f).settle(&solve));
    assert_eq!(*sc, *sf);
    assert_eq!(sc.digest(), sf.digest());
    // With the arrows emptied the needs alone give the order: the same variables, the place
    // of the held-read one aside (see the doc).
    for class in [false, true] {
        let (mut c, _) = landing6_held_read_pair(class);
        for a in &mut c.arrows {
            a.params.fill(Ty::empty());
            a.result = Ty::empty();
        }
        let f = flat_of(&c);
        let (c, f) = (Arc::new(c), Arc::new(f));
        let (seen, want) = (c.vars_order(), f.vars_order());
        assert_eq!(seen, want, "arrows emptied, held-read class: {class}");
        let (mut dv, mut ev) = (Vars::default(), Vars::default());
        c.needs.iter().for_each(|n| n.vars_in(&mut dv));
        f.needs.iter().for_each(|n| n.vars_in(&mut ev));
        // A lone forward gives its variables in the order of its types, not of its leaf
        // needs (see `Need::vars_in`): per need, the same set.
        dv.order.sort();
        ev.order.sort();
        assert_eq!(dv.order, ev.order, "`Need::vars_in`, class: {class}");
    }
}

/// Landing round 6, Gemini L6-B2: a function the callee holds that reads a written variable
/// from around it is refused (`#4`) in Zed source, so the checker keeps no forward with
/// `held_outer`, and D and E agree. Gemini's program, with its control that reads nothing.
#[test]
fn landing6_outer_variable_read_in_a_map_is_refused() {
    let read = "outer(positional q: Q, positional r: R, positional q2: Q, positional r2: R) = {\n\
                \th0(positional m) = m.map((x: int) -> q);\n\
                \th1(positional m) = h0(m);\n\
                \t(q2, r, r2, h1)\n\
                };\n";
    let (e, _) = run_with_cfg(read, R10Config::eager());
    assert!(e.errors.is_empty(), "{:?}", e.errors);
    let (d, stats) = run_with_cfg(read, R10Config::default());
    assert_eq!(stats.kept_at_generalize, 0);
    assert!(
        d.sigs
            .values()
            .all(|s| (s.needs.iter()).all(|n| match &n.kind {
                NeedKind::Fwd(f) => f.held_outer.is_empty(),
                _ => true,
            }))
    );
    assert_info_eq("outer variable read in a map", &e, &d);
    let control = read.replace("-> q)", "-> 1)");
    let (e, _) = run_with_cfg(&control, R10Config::eager());
    let (d, stats) = run_with_cfg(&control, R10Config::default());
    assert!(stats.kept_at_generalize >= 1, "control keeps a forward");
    assert_info_eq("control", &e, &d);
}

/// Landing round 6, Gemini L6-B4: `VarBits::is_empty` ignored the `internal` bit, so a
/// signature holding only a forward with internal results read as holding no variable,
/// a tuple holding it did not bind, and a renaming of an internal result inside a tuple or
/// payload two functions deep was skipped. An absent name is the control.
///
/// The signature is Gemini's: every type of the forward's need set to `int`, so its only
/// variables are internal results. Gemini made it with `Need::map_tys`, which since this round
/// refuses that mapping, so the test sets the same fields the old `map_tys` gave (each
/// argument, exit, `.on` type and tie `int`, the steps reduced to the internal runs, the
/// digest summary dropped); `s == flat` and the digests show the forward still decodes to
/// the flat needs.
#[test]
fn landing6_internal_results_count_as_variables_in_rows_and_shapes() {
    use std::collections::BTreeMap;
    use std::sync::Arc;
    use zedc_types::ty::{Binds, SParam, Ty};
    let (s, flat, hidden) = internal_results_only(false);
    let (sc, sf) = (Arc::new(s), Arc::new(flat));
    assert!(!sf.holds_no_variable());
    assert_eq!(sc.holds_no_variable(), sf.holds_no_variable());
    let (t1c, t1f) = (
        Ty::tuple(vec![Ty::func(sc.clone())]),
        Ty::tuple(vec![Ty::func(sf.clone())]),
    );
    assert_eq!(t1c.var_facts().binds, t1f.var_facts().binds);
    assert_eq!(t1c.holds_vars(), t1f.holds_vars());
    let outer = |t: &Ty| Arc::new(Sig::one(vec![], vec![], t.clone()));
    let (oc, of) = (outer(&t1c), outer(&t1f));
    let (t2c, t2f) = (
        Ty::tuple(vec![Ty::func(oc.clone())]),
        Ty::tuple(vec![Ty::func(of.clone())]),
    );
    let shape = |s: Arc<Sig>| Ty::atom_of("box", vec![Ty::func(s)], BTreeMap::new());
    let (shc, shf) = (shape(oc), shape(of));
    let absent: Binds = [("Absent".into(), Ty::var("Renamed".into()))]
        .into_iter()
        .collect();
    assert_eq!(t2c.renamed(&absent), t2f.renamed(&absent), "control");
    let names: Binds = [(hidden, Ty::var("Renamed".into()))].into_iter().collect();
    assert_eq!(t2c.renamed(&names), t2f.renamed(&names));
    assert_eq!(shc.renamed(&names), shf.renamed(&names));

    // Landing round 7, Gemini B2 (probe ported, P328): `Sig::holds_no_var` left out the
    // internal results, so the meet of `(x: int) -> <the signature>` with
    // `(x: int) -> bool` was `Never` in D and `int -> Never` in E.
    use zedc_types::ty::Carrier;
    let int = || Ty::carrier(Carrier::Int);
    let x = || SParam {
        name: "x".into(),
        positional: true,
        default: None,
        range: None,
    };
    let over = |s: &Arc<Sig>| {
        Ty::func(Arc::new(Sig::one(
            vec![x()],
            vec![int()],
            Ty::func(s.clone()),
        )))
    };
    let q = Ty::func(Arc::new(Sig::one(
        vec![x()],
        vec![int()],
        Ty::carrier(Carrier::Bool),
    )));
    let (mc, mf) = (over(&sc).meet(&q), over(&sf).meet(&q));
    assert!(!mf.is_empty(), "control: E's meet is not empty");
    assert_eq!(mc, mf);
}

/// The signature of `h3` of a four-link chain with every type it shows `int`, so that the
/// only variables it holds are its forward's internal results: (compact, flat, one internal
/// result that a later need has as its `.on`). With `unnamed`, the forward is made unnamed
/// (no naming, base class 100), as before `finish`. `Need::map_tys` refuses a compact
/// forward, so the fields the old `map_tys` gave are set directly (each argument, exit, `.on`
/// type and tie `int`, the steps reduced to the internal runs, the digest summary dropped);
/// `s == flat` and the digests show the forward still decodes to the flat needs.
fn internal_results_only(unnamed: bool) -> (Sig, Sig, std::sync::Arc<str>) {
    use std::sync::Arc;
    use zedc_types::ty::{Carrier, FwdVarStep, Ty};
    let int = || Ty::carrier(Carrier::Int);
    let (d, _) = run_with_cfg(&chain_src(4, "f", false), R10Config::default());
    let (_, orig, hidden) = sig_with_hidden(&d);
    let mut s = Sig::clone(&orig);
    for a in &mut s.arrows {
        a.params.fill(int());
        a.result = int();
    }
    for need in &mut s.needs {
        let NeedKind::Fwd(fwd) = &mut need.kind else {
            *need = need.map_tys(|_| int());
            continue;
        };
        let fwd = Arc::make_mut(fwd);
        fwd.sigma.iter_mut().for_each(|(_, t)| *t = int());
        fwd.exits.iter_mut().for_each(|(_, t)| *t = int());
        fwd.on_vars.fill(int());
        fwd.var_ties.iter_mut().for_each(|g| g.fill(int()));
        fwd.var_steps
            .retain(|st| matches!(st, FwdVarStep::InternalRun(_)));
        if unnamed {
            fwd.finish_naming = None;
            fwd.gen_naming = None;
            fwd.base_class = Some(100);
        }
        fwd.digest_summary = None;
        need.on = int();
        need.result = need.result.as_ref().map(|_| int());
    }
    s.own.clear();
    s.facts = Default::default();
    let flat = flat_of(&s);
    assert_eq!(s, flat);
    assert_eq!(s.digest(), flat.digest());
    if !unnamed {
        assert!(flat.needs.iter().any(|n| n.on.as_var() == Some(&hidden)));
    }
    (s, flat, hidden)
}

/// Landing round 7, Gemini B3 (probe ported, P328): `holds_no_variable` read a kept order
/// with no variable and no mark as "no variable", but an unnamed forward leaves no mark, so
/// once `vars_order` had been asked a signature whose only variables are such a forward's
/// internal results read as holding none, where E says it holds some.
#[test]
fn landing7_holds_no_variable_does_not_change_after_vars_order() {
    let (s, flat, _) = internal_results_only(true);
    let first = s.clone();
    assert!(!flat.holds_no_variable(), "control: E");
    assert_eq!(
        first.holds_no_variable(),
        flat.holds_no_variable(),
        "asked first"
    );
    let _ = s.vars_order();
    let _ = flat.vars_order();
    assert_eq!(
        s.holds_no_variable(),
        flat.holds_no_variable(),
        "asked after the order"
    );
}

/// Landing round 7, Gemini B1 (probe ported, P328): `first_seen` decoded a held function
/// whenever it had internal results, so `g_i = (h_i, m.map(f))` decoded all of `h_i`'s
/// links for a class only `m.map(f)` holds, n - 2 decodes over n such functions, O(n²) in
/// all (33.9 times the instructions at 8n); with the tuple the other way round, the class is
/// met first and nothing is decoded (the control). D agrees with E, and neither order
/// decodes.
#[test]
fn landing7_first_seen_passes_over_a_forward_holding_nothing_wanted() {
    for n in [10usize, 20, 40] {
        for before in [false, true] {
            let mut src = chain_src(n, "f", false);
            for i in 0..n {
                src.push_str(&match before {
                    true => format!("g{i}(positional f, positional m) = (h{i}, m.map(f));\n"),
                    false => format!("g{i}(positional f, positional m) = (m.map(f), h{i});\n"),
                });
            }
            let (e, _) = run_with_cfg(&src, R10Config::eager());
            assert!(e.errors.is_empty(), "{:?}", e.errors);
            reset_fwd_decode_count();
            let (d, _) = run_with_cfg(&src, R10Config::default());
            let decodes = fwd_decode_count();
            assert_info_eq(&format!("n {n}, held chain first: {before}"), &e, &d);
            assert_eq!(decodes, 0, "n {n}, held chain first: {before}");
        }
    }
}

/// Landing round 6, Claude Q1.2: a chain function passed where a function type takes its
/// parameters in the other order is checked as `permuted_sig` makes it, whose needs are
/// decoded and which therefore owns its forwards' internal results, as the flat signature
/// (E's) does. Before this test, taking the compact `own` there failed nothing, as no `Info`
/// the probe programs give reads it.
#[test]
fn landing6_permuted_sig_owns_the_internal_results() {
    let src = chain_src(4, "f", false);
    let (d, _) = run_with_cfg(&src, R10Config::default());
    let (e, _) = run_with_cfg(&src, R10Config::eager());
    // `grew`: the signatures whose compact own set lacks internal results the flat one has,
    // where taking the compact set would fail the first assertion.
    let mut grew = 0;
    for (k, s) in &d.sigs {
        if !s.needs.iter().any(|n| matches!(n.kind, NeedKind::Fwd(_))) {
            continue;
        }
        let flat = &e.sigs[k];
        grew += usize::from(s.own != flat.own);
        let mut slot = Sig::clone(s);
        slot.params.reverse();
        let (kept, p) = crate::check::walk::permuted_sig(s, &slot, &[1, 0], &[1, 0]);
        assert_eq!(p.own, flat.own, "sig {k}: own");
        assert_eq!(kept.len(), flat.needs.len(), "sig {k}: decoded needs");
        assert_eq!(p.params, slot.params, "sig {k}: params");
        for (a, b) in p.arrows.iter().zip(&s.arrows) {
            assert_eq!((&a.params[0], &a.params[1]), (&b.params[1], &b.params[0]));
        }
    }
    assert!(grew > 0, "no forward with internal results was met");
}

/// `t{i} = (t{i-1}, t{i-1})` (or `#box(…)`) 40 times over `t0`: one row or shape shared at
/// each of 40 levels.
fn doubled_src(t0: &str, wrap: (&str, &str), tail: &str) -> String {
    let mut s = String::from("{\n  t0 = ");
    s.push_str(t0);
    s.push_str(";\n");
    for i in 1..=40 {
        s.push_str(&format!(
            "  t{i} = {}t{}, t{}{};\n",
            wrap.0,
            i - 1,
            i - 1,
            wrap.1
        ));
    }
    s.push_str(&format!("  {tail}\n}}"));
    s
}

/// Landing review round 8, Gemini BLOCKING-1: the signature hash walks a row shared at each
/// of 40 levels once per context, also when the walk adds to a side sum of the hash (the
/// place of a tracked parameter in a forward's summary, or the rank of an own need result),
/// and D gives E's result. Before the fix such a walk was not stored in the memo, so it went
/// down every path: 2^40 (Gemini measured 5.3G and 6.2G check instructions at 20 levels).
#[test]
fn r10_rows_shared_at_40_levels_holding_side_sum_variables_agree_with_e() {
    let fwd = |wrap| {
        format!(
            "h0(positional f, positional x) = {};\nh1(positional f, positional x) = h0(f, x);\n",
            doubled_src("x", wrap, "f(t40)")
        )
    };
    for src in [
        fwd(("(", ")")),
        fwd(("#box(", ")")),
        format!(
            "f(positional m) = {};\n",
            doubled_src("m[0]", ("(", ")"), "m[t40]")
        ),
    ] {
        let (e, _) = run_with_cfg(&src, R10Config::eager());
        let (d, _) = run_with_cfg(&src, R10Config::default());
        assert_info_eq(&src, &e, &d);
    }
}

mod landing6_battery;
