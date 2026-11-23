//! Tests of paths of `ty.rs` that the local suite did not reach (row
//! TEST-types-unreached-paths-6; the cases are listed in `crates/zedc-types/COMPLETENESS.md`).
//! Each gives an input that takes the path and the answer DESIGN.md or the function's own
//! contract gives for it.

use super::*;

fn int() -> Ty {
    Ty::carrier(Carrier::Int)
}

fn f64_() -> Ty {
    Ty::carrier(Carrier::F64)
}

fn string() -> Ty {
    Ty::carrier(Carrier::Str)
}

fn rat() -> Ty {
    Ty::carrier(Carrier::Rat)
}

/// `int | f64`, the bound `B_MASK` of the tests' `B`.
fn num() -> Ty {
    int().union(&f64_())
}

/// `#b(x: t)`, a payload with a field, which has no exact kernel type.
fn with_field(t: Ty) -> Ty {
    Ty::atom_of("b", vec![], BTreeMap::from([(Arc::from("x"), t)]))
}

/// The function type `p -> r`.
fn f(p: Ty, r: Ty) -> Ty {
    Ty::func(Arc::new(one_of(p, r)))
}

/// The need of a read `v[k]` with a key of type `key`, written at no site.
fn index(key: Ty) -> NeedKind {
    NeedKind::Index { key, site: None }
}

fn var(v: &str) -> Ty {
    Ty::var(v.into())
}

fn ex(params: Vec<Ty>, result: Ty) -> Arrow {
    Arrow::exact(params, result)
}

/// A signature of `width` named parameters with `arrows`, owning the variables of `bounds`,
/// each bounded by its mask, and `T`.
fn bsig(arrows: Vec<Arrow>, width: usize, bounds: &[(&str, u8)]) -> Sig {
    let mut s = sig(arrows, width, false);
    s.own = bounds
        .iter()
        .map(|(v, _)| Arc::from(*v))
        .chain([Arc::from("T")])
        .collect();
    s.bounds = bounds.iter().map(|&(v, m)| (Arc::from(v), m)).collect();
    s.note_held();
    s
}

/// A signature as [`sig`] makes it, owning `T` alone: one that does not own the `B` of the
/// other side, so the comparison does not rename that `B` ([`Cx::own_name`]).
fn plain(arrows: Vec<Arrow>, width: usize) -> Sig {
    let mut s = sig(arrows, width, false);
    s.own = [Arc::from("T")].into_iter().collect();
    s.note_held();
    s
}

fn fty(s: Sig) -> Ty {
    Ty::func(Arc::new(s))
}

/// The positional parameter `x`.
fn x() -> SParam {
    SParam {
        name: "x".into(),
        positional: true,
        default: None,
        range: None,
    }
}

/// `leaf` held 2^`depth` times through rows, each holding the one below twice: `depth` nodes.
fn doubled(leaf: Ty, depth: usize) -> Ty {
    (0..depth).fold(leaf, |t, _| Ty::tuple(vec![t.clone(), t]))
}

/// A component whose form is not built leaves the tuple with no form ([`Forms::form`]): the
/// second component of each tuple is a function, which has no normal form, so the comparison
/// of the tuples is made on their parts, with the answers of the variance law of DESIGN.md
/// sec:type_language (contravariant in the parameter, covariant in the result).
#[test]
fn a_tuple_with_a_component_of_no_form_is_compared_by_parts() {
    let bytes = Ty::set(KType::partial(KType::int(), KType::int()));
    let pair = |g: Ty| Ty::tuple(vec![bytes.clone(), g]);
    let t = pair(f(int(), int()));
    let u = pair(f(int(), int().union(&string())));
    let w = pair(f(int(), string()));
    assert!(t.subtype(&u));
    assert!(!u.subtype(&t));
    assert!(!t.subtype(&w));
}

/// A bounded variable of one carrier is read as that carrier ([`Read::Mask`]), so the function
/// it is held in binds nothing through it ([`Cx::bound_in_fns`]): `(B, T) -> (B -> T)` for `B
/// in int` fits `(int, int) -> (int -> int)` at `T = int`.
#[test]
fn a_variable_of_one_carrier_held_in_a_result_function_is_its_carrier() {
    let c = fty(bsig(
        vec![ex(vec![var("B"), var("T")], f(var("B"), var("T")))],
        2,
        &[("B", 0b01)],
    ));
    let k = fty(sig(vec![ex(vec![int(), int()], f(int(), int()))], 2, false));
    assert!(c.subtype(&k));
}

/// An own variable read as a variable ([`Read::Rigid`]) or as itself is one [`Cx::held_own`]
/// gives for the function of the parameters that holds it, bounded or not, so the function is
/// read at the variable's binding or binds it ([`Cx::read_at`], [`Cx::through_fn`]): a generic
/// function fits the type of its instance. Given only the bounded variables, the unbounded `T`
/// was compared as itself inside the function, which nothing binds, and each of these was a
/// wrong no: `((B, T) -> int, B, T) -> int` for `B in int | f64` within `((int, int) -> int,
/// int, int) -> int` (at `B = T = int`), `((x0: T) -> int, T) -> int` within `((x0: int) ->
/// int, int) -> int`, and `((x0: T) -> int) -> T` within `((x0: int) -> int) -> int`, where
/// [`Binds::of_arrow`] binds the `T` of the result to `Never` first. The binding is still
/// checked: no instance takes `(int -> int, f64)`, as the domain of `int -> int` is exact.
#[test]
fn a_variable_in_a_parameter_function_is_bound_through_it() {
    let pair = |a: Ty, b: Ty| Ty::tuple(vec![a, b]);
    let c = fty(bsig(
        vec![ex(
            vec![f(pair(var("B"), var("T")), int()), var("B"), var("T")],
            int(),
        )],
        3,
        &[("B", B_MASK)],
    ));
    let k = fty(sig(
        vec![ex(vec![f(pair(int(), int()), int()), int(), int()], int())],
        3,
        false,
    ));
    assert!(c.subtype(&k), "{}", c.refused(&k));
    let c = fty(plain(
        vec![ex(vec![f(var("T"), int()), var("T")], int())],
        2,
    ));
    let k = fty(sig(vec![ex(vec![f(int(), int()), int()], int())], 2, false));
    assert!(c.subtype(&k), "{}", c.refused(&k));
    let k = fty(sig(
        vec![ex(vec![f(int(), int()), f64_()], int())],
        2,
        false,
    ));
    assert!(!c.subtype(&k));
    let c = fty(plain(vec![ex(vec![f(var("T"), int())], var("T"))], 1));
    let k = fty(sig(vec![ex(vec![f(int(), int())], int())], 1, false));
    assert!(c.subtype(&k), "{}", c.refused(&k));
}

/// An arrow that holds an own variable only inside a function in its parameters, and that
/// takes part in no cover, still has its permission checked ([`permitted`]):
/// `((x0: int) -> int) & ((x0: (x: T) -> int) -> int)` takes functions, which `(x0: int) ->
/// int` does not, so it is not within it. With one parameter this was a wrong yes
/// (row TEST-types-unreached-paths-6); with two it was refused, and still is.
#[test]
fn an_arrow_holding_a_variable_in_a_function_has_its_permission_checked() {
    for w in [1usize, 2] {
        let params = |p: Ty| {
            let mut v = vec![p];
            v.resize(w, int());
            v
        };
        let c = fty(plain(
            vec![
                ex(params(int()), int()),
                ex(params(f(var("T"), int())), int()),
            ],
            w,
        ));
        let k = fty(sig(vec![ex(params(int()), int())], w, false));
        assert!(!c.subtype(&k), "width {w}");
    }
}

/// [`repeated`] counts a variable a function in the parameters holds as standing twice only
/// where it reads as a rigid variable: `C`, bounded by one carrier, reads as its mask and is
/// passed over. `((int, int) -> int, int) -> int` does not fit `((B, C) -> int, B) -> int` for
/// `B in int | f64`, `C in int`: at `B = f64` its second parameter takes `f64`, which the
/// function does not take (exact domains, DESIGN.md sec:type_language).
#[test]
fn a_variable_of_one_carrier_in_a_parameter_function_is_not_repeated() {
    let c = fty(bsig(
        vec![ex(
            vec![f(Ty::tuple(vec![var("B"), var("C")]), int()), var("B")],
            int(),
        )],
        2,
        &[("B", B_MASK), ("C", 0b01)],
    ));
    let k = fty(sig(
        vec![ex(
            vec![f(Ty::tuple(vec![int(), int()]), int()), int()],
            int(),
        )],
        2,
        false,
    ));
    assert!(!k.subtype(&c));
    // Where `C` alone is in the function, `B` stands once and is widened exactly:
    // `((int) -> int, int | f64) -> int` fits `((C) -> int, B) -> int`.
    let c = fty(bsig(
        vec![ex(vec![f(var("C"), int()), var("B")], int())],
        2,
        &[("B", B_MASK), ("C", 0b01)],
    ));
    let k = fty(sig(vec![ex(vec![f(int(), int()), num()], int())], 2, false));
    assert!(k.subtype(&c), "{}", k.refused(&c));
}

/// [`repeated`] walks a row at most twice for each arrow: read in each place, a parameter
/// that holds the row of `B` 2^40 times through 40 nodes would not be read in any time. `B`
/// stands many times, so it is compared rigid, and the function on rows of `int` is not one
/// on the rows of `f64` that the instance at `B = f64` takes.
#[test]
fn a_row_met_many_times_in_the_parameters_is_walked_twice() {
    let nest = |leaf: Ty| doubled(Ty::tuple(vec![leaf, int()]), 40);
    let c = fty(bsig(
        vec![ex(vec![nest(var("B"))], int())],
        1,
        &[("B", B_MASK)],
    ));
    let k = fty(sig(vec![ex(vec![nest(int())], int())], 1, false));
    assert!(!k.subtype(&c));
}

/// The hash D gives a signature walks a row shared at each level once per scope context
/// ([`r10_hash::Encoder`]), not once per path, which hung the test above; it is the hash of
/// the same signature with every row built apart. The shared row holds `R`, the result of a
/// need, read in the arrow (where `R` hashes as a variable) and in the need (where it hashes
/// as the need's rank): a replay of the arrow's walk in the need would give another hash.
#[test]
fn a_row_shared_in_the_arrows_and_the_needs_hashes_as_rows_built_apart() {
    fn apart(leaf: &dyn Fn() -> Ty, depth: usize) -> Ty {
        if depth == 0 {
            return leaf();
        }
        Ty::tuple(vec![apart(leaf, depth - 1), apart(leaf, depth - 1)])
    }
    let leaf = || Ty::tuple(vec![var("R"), int()]);
    // The row in the arrow and the row in the need, shared or not.
    let signature = |in_arrow: Ty, in_need: Ty| {
        let mut s = bsig(vec![ex(vec![in_arrow], int())], 1, &[]);
        s.own.insert("R".into());
        s.needs = vec![Need {
            on: var("T"),
            kind: index(in_need),
            result: Some(var("R")),
            span: Span { start: 0, end: 1 },
            alike: Arc::from([]),
            via: CallPath::default(),
        }]
        .into();
        s.note_held();
        s
    };
    for depth in 0..8 {
        let row = doubled(leaf(), depth);
        let shared = signature(row.clone(), row);
        let built_apart = signature(apart(&leaf, depth), apart(&leaf, depth));
        assert_eq!(shared, built_apart);
        for r in [r10_hash::R_BASE, 17, 123_456_789] {
            assert_eq!(
                r10_hash::sig_digest_with_base(&shared, r),
                r10_hash::sig_digest_with_base(&built_apart, r),
                "depth {depth}, base {r}"
            );
        }
    }
}

/// A row shared at each of 64 levels stands 2^64 times in the signature. With the memo, the
/// hash reads it in 64 steps, so nothing may count the tokens it stands for: a count in a
/// `usize` overflowed and panicked here (landing review round 8, L8.Codex-memo-length). Two
/// copies built alike hash alike.
#[test]
fn a_row_shared_at_64_levels_hashes_without_counting_its_tokens() {
    let signature = || {
        let row = doubled(Ty::tuple(vec![var("B"), int()]), 64);
        let mut s = bsig(vec![ex(vec![row], int())], 1, &[]);
        s.own.insert("B".into());
        s.note_held();
        s
    };
    assert_eq!(signature().digest(), signature().digest());
}

/// A walk of a shared row that adds to a side sum of the hash is replayed from the memo with
/// its sums, scaled to the place it is met at, although the walk restarts the hash from
/// empty: the hash and the sums, for the rows shared and built apart, are those of a walk of
/// every path that memoizes nothing. The three leaves add to the three kinds of side sum:
/// `P`, a tracked parameter, to `s_params` (as a need's summary takes it); `R`, an own need
/// result read in the needs, to `s_rank`; a class number of `P` or more sets
/// `fallback_large_id`. At 40 levels the walk of every path would take 2^40 steps (landing
/// review round 8, Gemini BLOCKING-1), so the shared row must be read from the memo.
#[test]
fn a_shared_row_of_a_tracked_parameter_adds_each_place_to_the_side_sums() {
    use r10_hash::{Encoder, ScopePhase, SigScope};
    const LARGE: &str = "$18446744073709551615";
    fn apart(leaf: &str, depth: usize) -> Ty {
        if depth == 0 {
            return Ty::tuple(vec![var(leaf), int()]);
        }
        Ty::tuple(vec![apart(leaf, depth - 1), apart(leaf, depth - 1)])
    }
    // With `keep_stream`, the encoder walks every path and memoizes nothing.
    let encode = |t: &Ty, keep_stream: bool| {
        let mut enc = Encoder::new(17, keep_stream);
        enc.push_scope(SigScope {
            own: [Arc::from("P"), Arc::from("R")].into_iter().collect(),
            mat_result_ranks: [(Arc::from("R"), 3)].into_iter().collect(),
            phase: ScopePhase::Needs,
            is_root: true,
        });
        enc.track_params([Arc::from("P")].into_iter().collect());
        // A token before the type, so that its walk starts at a power of `r` other than 1.
        enc.emit_ty(&int());
        enc.emit_ty(t);
        let mut params: Vec<_> = enc.s_params.into_iter().collect();
        params.sort();
        (
            enc.part.finalize(),
            params,
            enc.s_rank,
            enc.fallback_large_id,
        )
    };
    for leaf in ["P", "R", LARGE] {
        for depth in 0..8 {
            let (shared, built_apart) = (doubled(apart(leaf, 0), depth), apart(leaf, depth));
            assert_eq!(shared, built_apart);
            let walked = encode(&built_apart, true);
            let summed = !walked.1.is_empty() || walked.2 != 0 || walked.3;
            assert!(summed, "{leaf}: a side sum is taken");
            assert_eq!(encode(&shared, false), walked, "{leaf}, depth {depth}");
            assert_eq!(encode(&built_apart, false), walked, "{leaf}, depth {depth}");
        }
        let deep = |k| encode(&doubled(apart(leaf, 0), k), false);
        assert_ne!(deep(40).0, deep(39).0, "{leaf}");
    }
}

/// D's hash of a function held inside another reads the inner one's kept summary
/// ([`r10_hash::NestedSummary`]), which leaves out the variables of the functions around it
/// and reads each where the summary is met: the hash and the side sums are those of the walk
/// with every function in place (`keep_stream`). The leaf is a tracked parameter `P`, an own
/// need result `R` (a rank in the needs, a variable times its rank in the arrows), `Q`, which
/// no function owns, and a class number of `P` or more, whose function is walked in place
/// (`Direct`). The types put the leaf under one, two and three functions, beside a variable
/// `M` of a function between (plain and of a large class number), in rows shared at each
/// level, and in a need of a function inside. No function holds only its own variables, as
/// those are read by their hash, which a kept stream does not do.
#[test]
fn a_function_held_inside_another_hashes_by_its_summary_as_walked_in_place() {
    use r10_hash::{NestedSummary, R_BASE, encode_sig_stream, flat_need_summary};
    const LARGE: &str = "$18446744073709551615";
    const LARGE_M: &str = "$18446744073709551614";
    let owning = |t: Ty, own: &str| {
        let mut s = one_of(t, int());
        s.own.insert(own.into());
        s.note_held();
        fty(s)
    };
    let need = |on: Ty, kind: NeedKind, result: Option<Ty>| Need {
        on,
        kind,
        result,
        span: Span { start: 0, end: 1 },
        alike: Arc::from([]),
        via: CallPath::default(),
    };
    let with_need = |leaf: &str| {
        let mut s = one_of(int(), int());
        s.needs = vec![need(var("T"), index(var(leaf)), None)].into();
        s.note_held();
        fty(s)
    };
    for leaf in ["P", "R", "Q", LARGE] {
        let inner = f(var(leaf), int());
        let summary = inner.fns.iter().next().unwrap().facts.12.get().cloned();
        let types = [
            inner,
            owning(f(Ty::tuple(vec![var(leaf), var("M")]), var("M")), "M"),
            owning(f(Ty::tuple(vec![var(leaf), var(LARGE_M)]), int()), LARGE_M),
            doubled(
                Ty::tuple(vec![
                    owning(f(Ty::tuple(vec![var(leaf), var("M")]), var("M")), "M"),
                    int(),
                ]),
                5,
            ),
            f(f(f(var(leaf), var("R")), int()), var("P")),
            f(with_need(leaf), var(leaf)),
        ];
        for (k, t) in types.iter().enumerate() {
            let at = format!("{leaf}, type {k}");
            // In a need, with the side sums a need's summary takes.
            let n = need(var("T"), index(t.clone()), Some(var("R")));
            let own = ["P", "R", "T"].into_iter().map(Arc::from).collect();
            let ranks = [(Arc::from("R"), 3)].into_iter().collect();
            let params = [Arc::from("P")].into_iter().collect();
            let summed = flat_need_summary(&n, &own, &ranks, &params, R_BASE, false);
            let walked = flat_need_summary(&n, &own, &ranks, &params, R_BASE, true);
            assert_eq!(summed.body, walked.body, "{at}");
            assert_eq!(summed.s_rank, walked.s_rank, "{at}");
            assert_eq!(summed.s_params, walked.s_params, "{at}");
            assert_eq!(summed.fallback_large_id, walked.fallback_large_id, "{at}");
            // In an arrow and a need of a signature whose need gives `R`.
            let mut s = bsig(vec![ex(vec![t.clone()], var("R"))], 1, &[]);
            s.own.extend(["P", "R"].map(Arc::from));
            s.needs = vec![
                need(var("T"), index(int()), Some(var("R"))),
                need(var("T"), index(t.clone()), None),
            ]
            .into();
            s.note_held();
            let summed = encode_sig_stream(&s, R_BASE, false);
            assert_eq!(summed.0, encode_sig_stream(&s, R_BASE, true).0, "{at}");
        }
        // The summary of the innermost function is made and kept, and walked in place only
        // where its outer variable has no plain token.
        let made = types_summary(&f(var(leaf), int()));
        assert!(
            summary.is_none(),
            "{leaf}: no summary before a hash needs one"
        );
        match made {
            Some(NestedSummary::Direct) => assert_eq!(leaf, LARGE),
            Some(NestedSummary::Summary { free, .. }) => {
                assert_ne!(leaf, LARGE);
                assert_eq!(free.len(), 1, "{leaf}");
            }
            None => panic!("{leaf}: no summary made"),
        }
    }
}

/// D's hash of functions nested `k` deep, level `i` owning `M{i}` and holding the variables of
/// every level around it and the root's `P` (a tracked parameter), `R` (an own need result)
/// and `Q` (owned by none), is the walk with every function in place: the shape whose
/// summaries carry `O(k)` outer variables, kept in a [`r10_hash::FreeWeights`] whose weights
/// are scaled where a summary is met, and corrected from plain tokens only where a scope owns
/// the variable. The root owns either few variables, so the owned ones are found by its own
/// set, or many, so they are found by the summary's ([`r10_hash::Encoder`]'s
/// `apply_nested`).
#[test]
fn functions_nested_each_holding_every_outer_variable_hash_as_walked_in_place() {
    use r10_hash::{R_BASE, encode_sig_stream, flat_need_summary};
    let owning = |t: Ty, own: &str| {
        let mut s = one_of(t, int());
        s.own.insert(own.into());
        s.note_held();
        fty(s)
    };
    let nest = |k: usize, leaf: &str| {
        (0..k).rev().fold(var(leaf), |t, i| {
            let mut items: Vec<Ty> = (0..=i).map(|j| var(&format!("M{j}"))).collect();
            items.extend([var("P"), var("R"), var("Q"), t]);
            owning(Ty::tuple(items), &format!("M{i}"))
        })
    };
    let need = |on: Ty, kind: NeedKind, result: Option<Ty>| Need {
        on,
        kind,
        result,
        span: Span { start: 0, end: 1 },
        alike: Arc::from([]),
        via: CallPath::default(),
    };
    for k in 1..10 {
        let mut hashes = Vec::new();
        for leaf in ["P", "R", "Q", "M0"] {
            for extra in [0, 3 * k + 5] {
                let at = format!("k {k}, leaf {leaf}, {extra} more own");
                let t = nest(k, leaf);
                let mut own: BTreeSet<Arc<str>> =
                    ["P", "R", "T"].into_iter().map(Arc::from).collect();
                own.extend((0..extra).map(|j| Arc::from(format!("X{j}"))));
                let ranks = [(Arc::from("R"), 3)].into_iter().collect();
                let params = [Arc::from("P")].into_iter().collect();
                let n = need(var("T"), index(t.clone()), Some(var("R")));
                let summed = flat_need_summary(&n, &own, &ranks, &params, R_BASE, false);
                let walked = flat_need_summary(&n, &own, &ranks, &params, R_BASE, true);
                assert_eq!(summed.body, walked.body, "{at}");
                assert_eq!(summed.s_rank, walked.s_rank, "{at}");
                assert_eq!(summed.s_params, walked.s_params, "{at}");
                let mut s = bsig(vec![ex(vec![t.clone()], var("R"))], 1, &[]);
                s.own.extend(own.iter().cloned());
                s.needs = vec![
                    need(var("T"), index(int()), Some(var("R"))),
                    need(var("T"), index(t.clone()), None),
                ]
                .into();
                s.note_held();
                let summed = encode_sig_stream(&s, R_BASE, false).0;
                assert_eq!(summed, encode_sig_stream(&s, R_BASE, true).0, "{at}");
                hashes.push(summed);
            }
        }
        // The leaves are told apart, so the equalities above test something.
        let mut distinct = hashes.clone();
        zed_collections::sorted::sort_dedup(&mut distinct);
        assert_eq!(distinct.len(), hashes.len(), "k {k}");
    }
}

/// The hashes of signatures are the numbers they were before the hash's own arithmetic modulo
/// `2^61 - 1` (`mod_p`, `add_p`, `sub_p`, `mul_p`) was replaced by the shared
/// `zed_numtheory::m61` (row DRY-types-m61-helpers, 2026-11-20). The expected numbers were
/// printed by this test on main at 9074c4490, before the change. The signatures take the
/// paths of the hash that do arithmetic on its tokens: plain variables, class variables `$k`,
/// the letters `T` to `W` and the fresh variables `T5`, `T6` (affine tokens), a need result
/// read by its rank, a tracked parameter (`s_params`), functions nested in functions holding
/// the variables around them (scaled weights, `FreeWeights`), a row shared at 30 levels (the
/// memo's powers of `r`) and a class number past `P` (`fallback_large_id`). The test catches
/// any change in a token, in the reduction of a sum or a product, or in the order the parts
/// are joined; it does not reach the sums of runs of class and fresh variables of forward
/// needs (`sum_cls_range_o1`, `sum_fresh_vars_o1`), which the unit tests of
/// `zed_numtheory::m61::reduce` cover for every residue class of their `u128` arguments.
#[test]
fn signature_hashes_are_the_numbers_they_were_before_the_shared_arithmetic() {
    use r10_hash::{R_BASE, encode_sig_stream, flat_need_summary};
    const LARGE: &str = "$18446744073709551615";
    let owning = |t: Ty, own: &str| {
        let mut s = one_of(t, int());
        s.own.insert(own.into());
        s.note_held();
        fty(s)
    };
    let nest = |k: usize, leaf: &str| {
        (0..k).rev().fold(var(leaf), |t, i| {
            let mut items: Vec<Ty> = (0..=i).map(|j| var(&format!("M{j}"))).collect();
            items.extend([var("P"), var("R"), var("Q"), t]);
            owning(Ty::tuple(items), &format!("M{i}"))
        })
    };
    let need = |on: Ty, kind: NeedKind, result: Option<Ty>| Need {
        on,
        kind,
        result,
        span: Span { start: 3, end: 17 },
        alike: Arc::from([]),
        via: CallPath::default(),
    };
    let mut got = Vec::new();
    for leaf in ["P", "R", "Q", "$7", "T5", "W", LARGE] {
        for t in [
            nest(3, leaf),
            doubled(Ty::tuple(vec![var(leaf), int()]), 30),
        ] {
            let own: BTreeSet<Arc<str>> = ["P", "R", "T"].into_iter().map(Arc::from).collect();
            let ranks = [(Arc::from("R"), 3)].into_iter().collect();
            let params = [Arc::from("P")].into_iter().collect();
            let n = need(var("T"), index(t.clone()), Some(var("R")));
            let summary = flat_need_summary(&n, &own, &ranks, &params, R_BASE, false);
            let mut params: Vec<_> = summary.s_params.into_iter().collect();
            params.sort();
            got.extend([summary.body.val, summary.body.pow, summary.s_rank]);
            got.extend(params.into_iter().map(|(_, w)| w));
            let mut s = bsig(vec![ex(vec![t.clone()], var("R"))], 1, &[]);
            s.own.extend(own.iter().cloned());
            s.needs = vec![
                need(var("T"), index(int()), Some(var("R"))),
                need(var("T"), index(t), None),
            ]
            .into();
            s.note_held();
            got.push(encode_sig_stream(&s, R_BASE, false).0);
        }
    }
    // For each leaf and each of the two types: the need's summary (its hash, its power of
    // `r`, `s_rank`, then the weights of `s_params` by name) and the signature's hash.
    let expected: [u64; 64] = [
        2167896917970484714,
        372772465237166190,
        1506640472885109537,
        1253231855573020471,
        323469015626661332,
        233787326021364033,
        1916802044237633057,
        396490681546329558,
        735087603464591777,
        983884292370639285,
        2101579779831255766,
        372772465237166190,
        595186455637230143,
        2164685872820899865,
        2160293382132049668,
        821717398565642192,
        1916802044237633057,
        1131578285010921335,
        1391210599347757306,
        34324831161644961,
        372772465237166190,
        1506640472885109537,
        2164685872820899865,
        2161466544111747016,
        1912209306356504545,
        1916802044237633057,
        396490681546329558,
        1862041912059484906,
        510466988845592009,
        372772465237166190,
        1506640472885109537,
        2164685872820899865,
        947404955622620844,
        528652274601177619,
        1916802044237633057,
        396490681546329558,
        453239204546691116,
        2150371459327423737,
        372772465237166190,
        1506640472885109537,
        2164685872820899865,
        1961252974571939293,
        1053801508397639124,
        1916802044237633057,
        396490681546329558,
        1454509796671920970,
        1082799928928214530,
        372772465237166190,
        1506640472885109537,
        2164685872820899865,
        742188977315931964,
        430179442322097325,
        1916802044237633057,
        396490681546329558,
        881253340637273375,
        627364193662941076,
        1803402181238694075,
        1625371962217328914,
        2164685872820899865,
        157203675933149751,
        736088785808388687,
        202891524623332401,
        1514351330971421828,
        506968033703741763,
    ];
    assert_eq!(got, expected);
}

/// A signature whose need takes an int at a path hashes alike whether the path's steps are
/// emitted one at a time (the stream kept) or added by the tokens the path keeps
/// ([`PathSteps::r10_part`], PERF-keyed-part-path-d-squared), for paths of 0 to 40 steps of
/// both kinds; the paths are told apart, so the equality tests something. A path made one
/// step at a time and one made from the slice are equal, though in different allocations, and
/// give back their steps; a path of 200 000 steps is dropped without a stack overflow.
#[test]
fn a_path_hashes_alike_by_its_kept_tokens_and_one_step_at_a_time() {
    use r10_hash::{R_BASE, encode_sig_stream};
    let step = |j: usize| match j % 3 {
        0 => PathStep::Index(j * 7),
        1 => PathStep::Part { i: j % 2, n: 2 },
        _ => PathStep::Part { i: j, n: j + 1 },
    };
    let mut hashes = Vec::new();
    let mut path = PathSteps::default();
    for l in 0..=40 {
        let steps: Vec<PathStep> = (0..l).map(step).collect();
        let flat = PathSteps::from(&steps[..]);
        assert_eq!(path, flat, "{l} steps");
        assert_eq!(path.len(), l);
        assert_eq!(path.to_vec(), steps);
        let mut s = bsig(vec![ex(vec![int()], int())], 1, &[]);
        s.needs = vec![Need {
            on: Ty::empty(),
            kind: NeedKind::InDomain {
                domain: IntDomain {
                    what: "a use".into(),
                    name: "x".into(),
                    below_two_pow: None,
                    written: None,
                    key: None,
                },
                param: 0,
                via: None,
                bits: None,
                path: path.clone(),
            },
            result: None,
            span: Span { start: 3, end: 17 },
            alike: Arc::from([]),
            via: CallPath::default(),
        }]
        .into();
        s.note_held();
        let summed = encode_sig_stream(&s, R_BASE, false).0;
        assert_eq!(summed, encode_sig_stream(&s, R_BASE, true).0, "{l} steps");
        hashes.push(summed);
        path = path.push(step(l));
    }
    let mut distinct = hashes.clone();
    zed_collections::sorted::sort_dedup(&mut distinct);
    assert_eq!(distinct.len(), hashes.len());
    let long = (0..200_000).fold(PathSteps::default(), |p, j| p.push(step(j)));
    assert_eq!(long.len(), 200_000);
    drop(long);
}

/// The summary kept by the function `t` holds, after a signature holding it in an arrow is
/// hashed.
fn types_summary(t: &Ty) -> Option<r10_hash::NestedSummary> {
    let s = bsig(vec![ex(vec![t.clone()], int())], 1, &[]);
    r10_hash::encode_sig_stream(&s, r10_hash::R_BASE, false);
    t.fns.iter().next().unwrap().facts.12.get().cloned()
}

/// The depth of the types of the two tests below, and the stack they run on: 2 MiB for each
/// 100,000 levels, the stack the step tests' deep types run on (row
/// FAIL-l0126-stack-overflow-after-d), so a walk that takes stack at each level overflows it.
const DEEP: usize = 20_000;
const DEEP_STACK: usize = (2 << 20) * DEEP / 100_000;

/// Runs `f` on a thread with a stack of [`DEEP_STACK`] bytes.
fn on_deep_stack(f: impl FnOnce() + Send) {
    std::thread::scope(|s| {
        let thread = std::thread::Builder::new().stack_size(DEEP_STACK);
        thread.spawn_scoped(s, f).unwrap().join().unwrap();
    });
}

/// D's hash of a signature walks rows and payload shapes nested [`DEEP`] levels without a
/// stack frame a level: it overflowed the stack, recursing through `Encoder::memoized` at each
/// level, where the hash before D read each row's kept hash (row
/// FAIL-l0126-stack-overflow-after-d). Rows with and without a variable are walked in turn,
/// as they are memoized under different keys.
#[test]
fn a_signature_of_rows_and_payloads_nested_deep_hashes_on_a_small_stack() {
    on_deep_stack(|| {
        let nest = |leaf: &str| {
            (0..DEEP).fold(var(leaf), |t, k| match k % 4 {
                0 => Ty::tuple(vec![t, int()]),
                1 => Ty::atom_of("a", vec![t], BTreeMap::new()),
                2 => Ty::tuple(vec![int(), t, var("T")]),
                _ => with_field(t),
            })
        };
        let signature = |leaf: &str| bsig(vec![ex(vec![nest(leaf)], int())], 1, &[]);
        let (s, same, other) = (signature("T"), signature("T"), signature("U"));
        assert_eq!(s.digest(), same.digest());
        assert_ne!(s.digest(), other.digest());
    });
}

/// D's hash of a function nested [`DEEP`] levels deep, each level holding the outermost
/// function's own `T`, takes no stack frame a level: each level hashed the one below in
/// place, under the scopes of every level around it, and overflowed the stack (the l01_22
/// bench
/// `function_types_nested_deep_whose_inner_levels_hold_the_outer_variable_fit_in_linear_time`,
/// row FAIL-l0126-stack-overflow-after-d). Tuples between the levels put the inner functions
/// in rows.
#[test]
fn functions_nested_deep_holding_the_outer_variable_hash_on_a_small_stack() {
    on_deep_stack(|| {
        let nest = |leaf: &str| {
            (0..DEEP).fold(var(leaf), |t, k| match k % 3 {
                0 => f(t, var("T")),
                1 => f(var("T"), t),
                _ => Ty::tuple(vec![t, var("T")]),
            })
        };
        let signature = |leaf: &str| bsig(vec![ex(vec![nest(leaf)], int())], 1, &[]);
        let (s, same, other) = (signature("T"), signature("T"), signature("U"));
        assert_eq!(s.digest(), same.digest());
        assert_ne!(s.digest(), other.digest());
    });
}

/// One level of the nest of
/// [`functions_holding_an_outer_variable_in_an_arrow_and_a_need_hash_once_each`]:
/// a function whose arrow and whose need hold the same row, which holds the level below and,
/// when `open`, the outer variable `T`; else `int`.
fn level_in_arrow_and_need(inner: Ty, open: bool) -> Ty {
    let outer = if open { var("T") } else { int() };
    let row = Ty::tuple(vec![inner, outer]);
    let mut s = bsig(vec![ex(vec![row.clone()], int())], 1, &[]);
    s.own.remove("T");
    s.own.insert("R".into());
    s.needs = vec![Need {
        on: var("R"),
        kind: index(row),
        result: Some(var("R")),
        span: Span { start: 0, end: 1 },
        alike: Arc::from([]),
        via: CallPath::default(),
    }]
    .into();
    s.note_held();
    fty(s)
}

/// D's hash walks each held function once, also one that holds a variable of the function
/// around it in a row shared by its arrow and its need. Before the fix such a function was
/// walked in place under a new scope for its arrows and another for its needs, so the row
/// and the function below it were walked twice at each level: 2^depth, here 2^40 (review
/// round 8, Claude seat F4; main before the landing read each function's kept hash). The
/// nests open and closed differ, and building the open one twice gives one hash. Claude's
/// probe `l8_nested_open_functions_are_hashed_once_per_path`, ported (P328).
#[test]
fn functions_holding_an_outer_variable_in_an_arrow_and_a_need_hash_once_each() {
    const LEVELS: usize = 40;
    let nest = |open: bool| {
        let t = (0..LEVELS).fold(int(), |t, _| level_in_arrow_and_need(t, open));
        let mut s = bsig(vec![ex(vec![t], int())], 1, &[]);
        s.note_held();
        s
    };
    let (open, again, closed) = (nest(true), nest(true), nest(false));
    let held = &open.arrows[0].params[0].fns;
    assert!(held.iter().any(|f| !f.holds_only_own_variables()));
    assert_eq!(open.digest(), again.digest());
    assert_ne!(open.digest(), closed.digest());
}

/// A bounded variable that the arrow takes only inside a function type is given by no
/// argument, so no argument fixes its carrier ([`refused_cover`], [`Places`]), and the message
/// names the arrow and the variable as the program wrote them: `B`, not the name the
/// comparison reads it by (`B'1`), and the arrow with its `for` clause, not with `B` printed
/// as an unbounded `T`.
#[test]
fn a_variable_no_argument_gives_is_named_as_written() {
    let c = fty(bsig(
        vec![ex(vec![f(var("B"), int())], var("B"))],
        1,
        &[("B", B_MASK)],
    ));
    let q = fty(sig(vec![ex(vec![f(num(), int())], num())], 1, false));
    assert_eq!(
        c.refused(&q),
        ": at `type Part1 = int | f64;\n(x0: Part1 -> int) -> Part1`, the arrow `(x0: B -> int) \
         -> B for B in int | f64` takes it only with `B` bound to `int | f64`, values of more \
         than one carrier, but a call fixes `B` to one carrier, and no argument gives values of \
         `B` outside a function type, so none fixes its carrier"
    );
    let c = fty(bsig(
        vec![ex(vec![var("B"), var("B")], int())],
        2,
        &[("B", B_MASK)],
    ));
    let q = fty(sig(vec![ex(vec![num(), num()], int())], 2, false));
    assert_eq!(
        c.refused(&q),
        ": at `type Part1 = int | f64;\n(x0: Part1, x1: Part1) -> int`, the arrow `(x0: B, x1: \
         B) -> int for B in int | f64` takes it only with `B` bound to `int | f64`, values of \
         more than one carrier, but a call fixes `B` to one carrier, and `B` stands at 2 places \
         the arguments give, which could be given values of two carriers"
    );
}

/// A payload shape with fields has no kernel type; read from below ([`Approx::made`]) it is
/// the empty type, the largest kernel type within it that is known.
#[test]
fn a_payload_with_fields_is_empty_from_below() {
    let k = Approx::default().of(&with_field(int()), false);
    assert_eq!(k.verdict(), Verdict::Empty);
}

/// The meet of two functions whose parameter types are functions ([`Domains::fns_apart`],
/// [`Domains::kernel_of`], [`Domains::keys_apart`]): the answers of the meet of functions,
/// DESIGN.md sec:type_language. Over one parameter type, the values meet; over parameter
/// function types with no common function, no function takes both exactly (`Never`).
#[test]
fn meets_of_functions_of_function_parameters() {
    let meet = |p: Ty, r: Ty, r2: Ty| f(p.clone(), r).meet(&f(p, r2)).to_string();
    let rs = || rat().union(&string());
    let g = f(int(), f(int(), int()));
    assert_eq!(meet(g, rat(), rs()), "(int -> int -> int) -> rat");
    let g = f(int(), Ty::empty());
    assert_eq!(meet(g, rat(), rs()), "(int -> Never) -> rat");
    let g = f(f(int(), int()), int());
    assert_eq!(meet(g, rat(), rs()), "((int -> int) -> int) -> rat");
    let m = f(f(int(), f(int(), int())), rat()).meet(&f(f(int(), string()), rat()));
    assert!(m.is_empty(), "{m}");
    // A function type of two parameters is not read through its arrows, so nothing is proved
    // apart, and the meet of one parameter type is kept.
    let mut h = sig(vec![ex(vec![int(), int()], int())], 2, false);
    h.own.clear();
    h.note_held();
    let m = meet(fty(h), rat(), rs());
    assert!(!m.is_empty() && m.ends_with("-> rat"), "{m}");
}

/// [`Domains::inhabited_fn`] on value types read each way: no value (`int -> Never`); a kernel
/// value type with a value (`int | #b(x: int)`, its `int`); a value type of no kernel type
/// whose part read from below is empty (`#b(x: int)`, given up: it is not claimed, which only
/// keeps a meet); data beside a function type (given up, the same).
#[test]
fn inhabited_fn_reads_each_kind_of_value_type() {
    let one = |r: Ty| sig(vec![ex(vec![int()], r)], 1, false);
    assert!(!Domains::inhabited_fn(&one(Ty::empty())));
    assert!(Domains::inhabited_fn(&one(int().union(&with_field(int())))));
    assert!(!Domains::inhabited_fn(&one(with_field(int()))));
    assert!(!Domains::inhabited_fn(&one(int().union(&f(int(), int())))));
    // Two value types of no kernel type that differ: not claimed, as a value shared by both
    // is not found.
    let two = sig(
        vec![
            ex(vec![int()], with_field(int())),
            ex(vec![string()], with_field(string())),
        ],
        1,
        false,
    );
    assert!(!Domains::inhabited_fn(&two));
    // A value type of function types alone holds a function where one of them does: case (b).
    assert!(Domains::inhabited_fn(&one(f(int(), int()))));
}

/// [`Domains::inhabited_fn`] enters each signature once: `k_{i+1}` returns `(bool -> k_i) |
/// (String -> k_i)`, so `k_0` is met 2^40 times through 40 levels. The innermost returns a
/// tuple that holds a function, not claimed, so none is.
#[test]
fn inhabited_fn_enters_a_signature_met_twice_once() {
    let mut k = Arc::new(one_of(int(), Ty::tuple(vec![int(), f(int(), int())])));
    for _ in 0..40 {
        let fk = Ty::func(k.clone());
        let r = f(Ty::carrier(Carrier::Bool), fk.clone()).union(&f(string(), fk));
        k = Arc::new(one_of(int(), r));
    }
    assert!(!Domains::inhabited_fn(&k));
}

/// Partial arrows that each take no value of an exact arrow of the other side, read through
/// their parameters, leave the meet no function ([`Domains::meet`]): a function of `(x0: int
/// -> int, x1: int -> int) -> rat` takes every pair of such functions, and the other side's
/// arrows take a `String -> int` at one parameter or the other, which no function of the
/// first takes, and a function of both has the domain of each.
#[test]
fn partial_arrows_taking_nothing_of_the_exact_arrow_leave_no_function() {
    let (si, ii) = (f(string(), int()), f(int(), int()));
    let s = fty(sig(
        vec![
            Arrow::partial_of(vec![si.clone(), ii.clone()], rat()),
            Arrow::partial_of(vec![ii.clone(), si], rat()),
        ],
        2,
        false,
    ));
    let q = fty(sig(vec![ex(vec![ii.clone(), ii], rat())], 2, false));
    let m = s.meet(&q);
    assert!(m.is_empty(), "{m}");
}

/// A function in the parameters that owns a variable of the same name is passed over by
/// [`Places::walk`]: its `B` is another variable, so `(x0: B, x1: (x0: B) -> B) -> int`, with
/// both `B`s bounded by `int | f64`, has its outer `B` at one place, and it fits `(x0: int |
/// f64, x1: (x0: U) -> U) -> int` for `U in int | f64`.
#[test]
fn a_variable_a_parameter_function_owns_is_another_variable() {
    let g = |v: &str| fty(bsig(vec![ex(vec![var(v)], var(v))], 1, &[(v, B_MASK)]));
    let c = fty(bsig(
        vec![ex(vec![var("B"), g("B")], int())],
        2,
        &[("B", B_MASK)],
    ));
    let k = fty(plain(vec![ex(vec![num(), g("U")], int())], 2));
    assert!(c.subtype(&k), "{}", c.refused(&k));
}

/// [`Sig::first_seen`] enters a row or payload shape met twice once: the parameter holds the
/// row and the shape 2^40 times through 40 nodes each, and `U`, not held, keeps the walk going.
#[test]
fn first_seen_enters_a_row_or_shape_met_twice_once() {
    let rows = doubled(Ty::tuple(vec![int(), Ty::carrier(Carrier::Bool)]), 40);
    let shapes = (0..40).fold(int(), |t, _| {
        Ty::atom_of("a", vec![t.clone(), t], BTreeMap::new())
    });
    let s = sig(
        vec![ex(vec![Ty::tuple(vec![rows, shapes])], var("T"))],
        1,
        false,
    );
    let want: HashSet<Arc<str>> = [Arc::from("T"), Arc::from("U")].into_iter().collect();
    assert_eq!(s.first_seen(&want), vec![Arc::<str>::from("T")]);
}

/// The printer takes a union written `_` out once: in `T | ((U | int), int)`, `_` printed for
/// the whole, the union inside it is taken out already ([`Walk::plan`]). A result printed as
/// `_` in a partial arrow is not entered by [`Print::Found`].
#[test]
fn the_unknown_printed_for_a_union_and_a_found_result() {
    let p = var("T").union(&Ty::tuple(vec![var("U").union(&int()), int()]));
    assert_eq!(p.to_string(), "_");
    let g = fty(Sig::one_partial(
        vec![x()],
        vec![int()],
        var("T").union(&int()),
    ));
    assert_eq!(g.to_string(), "int ->? _");
    assert_eq!(Ty::tuple(vec![g, int()]).to_string(), "(int ->? _, int)");
    // In `(x0: T | (U | V, int)) -> V`, the inner union is taken out first (`U` stands once),
    // then the outer one, which steps over it: each variable inside is counted down once, so
    // `V`, left at one place, is `_` too. Counted down twice, `V`'s count went below zero.
    let mut s = sig(
        vec![ex(
            vec![var("T").union(&Ty::tuple(vec![var("U").union(&var("V")), int()]))],
            var("V"),
        )],
        1,
        false,
    );
    s.own = ["T", "U", "V"].into_iter().map(Arc::from).collect();
    s.note_held();
    assert_eq!(fty(s).to_string(), "(x0: _) -> _");
}

/// Where the union inside has written more names than the union around it, its set is the
/// one kept ([`walk_parts`], the smaller set merged into the larger) and still holds them: the
/// clause of the outer union, written after `B` and `C` inside, bounds every member, so it
/// names its own `B` `T`.
#[test]
fn names_of_a_larger_inner_union_are_kept_by_the_union_around_it() {
    let g = bsig(
        vec![
            ex(vec![var("B"), var("C")], var("B")),
            ex(vec![f64_(), f64_()], var("C")),
        ],
        2,
        &[("B", B_MASK), ("C", B_MASK)],
    );
    let f1 = plain(
        vec![
            ex(vec![rat().union(&fty(g))], int()),
            ex(vec![Ty::carrier(Carrier::Bool)], int()),
        ],
        1,
    );
    let f2 = bsig(
        vec![ex(vec![var("B")], var("B")), ex(vec![string()], int())],
        1,
        &[("B", B_MASK)],
    );
    assert_eq!(
        int().union(&fty(f1)).union(&fty(f2)).to_string(),
        "int | ((x0: rat | ((x0: B, x1: C) -> B) & ((x0: f64, x1: f64) -> C) for B in int | f64, \
         C in int | f64) -> int) & ((x0: bool) -> int) | ((x0: T) -> T) & ((x0: String) -> int) \
         for T in int | f64"
    );
}

/// Names written inside a union that a union around it holds are added to that union
/// ([`walk_parts`], the smaller set merged into the larger): a bounded `B` inside a function
/// in a parameter union of another function in a union.
#[test]
fn names_in_nested_unions_are_printed_once() {
    let inner = sig(
        vec![ex(vec![var("B")], var("B")), ex(vec![f64_()], int())],
        1,
        true,
    );
    let outer = sig(
        vec![
            ex(vec![rat().union(&fty(inner))], int()),
            ex(vec![Ty::carrier(Carrier::Bool)], int()),
        ],
        1,
        false,
    );
    assert_eq!(
        int().union(&fty(outer)).to_string(),
        "int | ((x0: rat | ((x0: B) -> B) & ((x0: f64) -> int) for B in int | f64) -> int) & \
         ((x0: bool) -> int)"
    );
}

/// No results to intersect ([`meet_within`] through [`Meet`], whose caller may give none):
/// no arrow takes the parameters, so nothing bounds the answer, and the intersection is not
/// within any result, not even every value. [`met`] never asks this; the scaling tests may.
#[test]
fn an_intersection_of_no_results_is_within_nothing() {
    assert!(!Meet::new(Vec::new(), Ty::dynamic(), &[]).within());
    assert!(!Meet::new(Vec::new(), int(), &[]).within());
    assert!(Meet::new(vec![int()], int(), &[]).within());
}

/// [`Domains::fns_apart`] builds, from a function type `g` of exact and partial arrows, also
/// the function whose domain is the union of all of them (its case (iii)). `g = ((x0: int) ->
/// int) & ((x0: String) ->? int)` holds the function over `int | String`, which `h = ((x0:
/// int) -> int) & ((x0: rat) ->? int)` does not permit, so `g` and `h` are different sets of
/// functions and `(g -> rat) & (h -> rat | String)`, two exact arrows over different domains,
/// is empty (DESIGN.md sec:type_language). So is the meet with `h` taking `String` too, which
/// holds the function over `int | rat` that `g` does not permit. Without (iii) both were kept,
/// which is sound but not narrow.
#[test]
fn a_function_type_of_exact_and_partial_arrows_holds_the_function_over_all_of_them() {
    let closed = |arrows: Vec<Arrow>| {
        let mut s = sig(arrows, 1, false);
        s.own.clear();
        s.note_held();
        fty(s)
    };
    let g = closed(vec![
        ex(vec![int()], int()),
        Arrow::partial_of(vec![string()], int()),
    ]);
    let hs = [
        closed(vec![
            ex(vec![int()], int()),
            Arrow::partial_of(vec![rat()], int()),
        ]),
        closed(vec![
            ex(vec![int()], int()),
            Arrow::partial_of(vec![string()], int()),
            Arrow::partial_of(vec![rat()], int()),
        ]),
    ];
    for h in hs {
        let a = f(g.clone(), rat());
        let b = f(h, rat().union(&string()));
        assert!(a.meet(&b).is_empty(), "{}", a.meet(&b));
        assert!(b.meet(&a).is_empty(), "{}", b.meet(&a));
    }
}

/// PROOF-held-own-outer-or-class: a class variable a function of the nest owns is that
/// function's variable where it stands in it, so [`VarFacts::outer_classes`] leaves it out,
/// as [`VarFacts::outer`] leaves out a name the nest owns; the same class variable standing
/// outside every owner is one a signature around may own, and is kept. Before, every class
/// variable was taken as one of a signature around ([`outer_or_class`]).
#[test]
fn a_class_variable_the_nest_owns_is_not_an_outer_one() {
    let k = || var("$3");
    let mut owner = sig(vec![ex(vec![k()], int())], 1, false);
    owner.own = [Arc::from("$3")].into_iter().collect();
    owner.note_held();
    let inside = sig(vec![ex(vec![fty(owner.clone())], int())], 1, false);
    let facts = inside.facts();
    assert!(facts.classes.contains("$3"), "{inside}");
    assert!(!facts.outer_classes.contains("$3"), "{inside}");
    let both = sig(vec![ex(vec![fty(owner), k()], int())], 2, false);
    assert!(both.facts().outer_classes.contains("$3"), "{both}");
}

/// A bounded variable a signature does not own, as [`Sig::replace`] leaves one when it
/// replaces a bounded own variable by another variable, met at an arrow equal to one of the
/// other side by the same free variable ([`equal_fits`], case 2c): `((x0: B) -> int) &
/// ((x0: String) -> int)` with the bound `B in int | f64` it does not own fits `((x0: B) ->
/// int) & ((x0: String) -> int | f64)` of the same `B`, whose first arrow is equal to its
/// own. `bounds_hold` refuses `B`, of no known mask, and the comparison after it decides.
#[test]
fn a_bounded_variable_not_owned_fits_an_equal_arrow() {
    let c = bounded_not_owned(vec![ex(vec![var("B")], int()), ex(vec![string()], int())]);
    let k = bounded_not_owned(vec![
        ex(vec![var("B")], int()),
        ex(vec![string()], int().union(&f64_())),
    ]);
    assert!(c.subtype(&k), "{}", c.refused(&k));
}

/// A bounded variable `B` that a signature does not own, met by an own unbounded variable
/// `B` of the other side, which [`Cx::own_name`] reads under its own name, is a different
/// variable ([`equal_fits`], case (a)): `(x0: B) -> int` with `B` fixed outside within `int |
/// f64` does not take every type, so it does not fit `(x0: B) -> int` whose `B` is its own.
#[test]
fn a_bounded_variable_not_owned_is_not_an_own_one_of_the_same_name() {
    let c = bounded_not_owned(vec![ex(vec![var("B")], int())]);
    let mut every = sig(vec![ex(vec![var("B")], int())], 1, false);
    every.own = [Arc::from("B")].into_iter().collect();
    every.note_held();
    let k = fty(every);
    assert!(!c.subtype(&k), "{c} fits {k}");
}

/// A function type of `arrows`, with the bound `B in int | f64` on a `B` it does not own.
fn bounded_not_owned(arrows: Vec<Arrow>) -> Ty {
    let mut s = sig(arrows, 1, false);
    s.bounds = [(Arc::from("B"), B_MASK)].into_iter().collect();
    s.note_held();
    fty(s)
}
