//! Landing round 6, Claude's review battery (ported under P328): each public operation of
//! ty.rs that takes a signature, run on a compact signature (D) and on its flat form (E) with
//! many bindings, and compared on every reading a caller can make. D and E must agree, but
//! for two differences the review found and accepted, which `cmp_sig` allows by name:
//!
//! - A signature that holds an unfinished forward has no runs for its internal classes, so
//!   they have no marks and `order_with_marks` leaves them out; only the visible order is
//!   compared.
//! - A function that holds a compact signature beside an outer variable named as one of its
//!   internal results (`Outside -> W`) lists the name twice in D (in a mark and in
//!   `vars_order`) and once in E, whose `vars_order` merges the two variables by name
//!   (Claude Q2.3). The allowance is kept, with its reason proved: D here is built by hand
//!   with that clash, which no signature of the check holds, and E is an untagged decode, so
//!   no reader of the check sees the merge (the proof at `Sig::vars_marks` in zedc-types,
//!   row FAIL-flat-vars-order-merge-by-name). A variable bound to the compact signature
//!   itself lists its internal names twice in both. Under such a binding (`Ctx::under`) the
//!   order is compared with each internal name once, on both sides. Under every other, a
//!   signature that holds two different compact signatures with the same internal results
//!   lists each such name once per held signature in D and once in E, for the same reason;
//!   D's count must then equal the number of held signatures whose marks name it, and the
//!   orders are compared with each internal name once (landing round 8).
//!
//! `Need::map_tys` refuses every compact forward and `Need::replace` refuses a binding that
//! must decode (landing round 6, Claude Q2.2), so those operations may panic in D and not in
//! E; nothing else may.

use super::*;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;
use zedc_types::ty::{Binds, Carrier, Need, NeedKind, Ty, why_unfit};

type Pair = (String, Arc<Sig>, Arc<Sig>);

/// What the battery found: differences, and how many operations it compared and how many
/// panicked in D alone where that is allowed, so a run that compares nothing fails.
#[derive(Default)]
struct Found {
    bad: Vec<String>,
    compared: usize,
    d_refused: usize,
}

/// The pair being run: the internal results of D's forwards, whether one is unfinished, and
/// whether the binding run may make the clash of Q2.3.
struct Ctx {
    internal: BTreeSet<Arc<str>>,
    unfinished: bool,
    clash: bool,
}

impl Ctx {
    /// `self` for a run under `b`, which makes the clash of Q2.3 when one of its types names
    /// an internal result or holds a function with internal results (the compact signature
    /// itself, `Ty::func(c)`); no other binding of the battery can (landing round 7, Claude
    /// F7: the orders were compared with each internal name once for every binding).
    fn under(&self, b: &Binds) -> Ctx {
        let clash = b.values().any(|t| {
            let f = t.var_facts();
            f.internal || (f.classes.iter().chain(&f.names)).any(|v| self.internal.contains(v))
        });
        Ctx {
            internal: self.internal.clone(),
            unfinished: self.unfinished,
            clash,
        }
    }
}

/// The internal results of the forwards of `s` and of every function it holds at any depth.
/// Landing review round 8, Claude F2: with those of its own forwards only, a signature that
/// holds other functions with kept forwards gave battery differences that are all the accepted
/// one of Q2.3 (1,412 on `b06_codex_shared.zed`), among which a real one would be lost. The
/// held ones are read from the marks of a walk of the signature held in a type, as its order
/// gives them.
fn internal_names(s: &Sig) -> BTreeSet<Arc<str>> {
    let mut out = BTreeSet::new();
    for n in &s.needs {
        if let NeedKind::Fwd(f) = &n.kind {
            out.extend(
                f.internal_result_tys()
                    .iter()
                    .filter_map(Ty::as_var)
                    .cloned(),
            );
        }
    }
    let hold = Sig::one(vec![], vec![], Ty::func(Arc::new(Sig::clone(s))));
    for m in hold.vars_marks() {
        for run in &m.runs {
            out.extend(run.names::<Arc<str>>());
        }
    }
    out
}

fn visible_names(flat: &Sig, internal: &BTreeSet<Arc<str>>) -> Vec<Arc<str>> {
    let f = Ty::func(Arc::new(flat.clone())).var_facts();
    let mut all: BTreeSet<Arc<str>> = f.classes.iter().chain(&f.names).cloned().collect();
    all.retain(|v| !internal.contains(v));
    all.into_iter().collect()
}

/// `order` with each repeated internal name after its first place left out (Q2.3).
fn once_each_internal(order: Vec<Arc<str>>, internal: &BTreeSet<Arc<str>>) -> Vec<Arc<str>> {
    let mut seen = BTreeSet::new();
    (order.into_iter())
        .filter(|v| !internal.contains(v) || seen.insert(v.clone()))
        .collect()
}

/// Compares two signatures on every reading a caller can make of them.
fn cmp_sig(label: &str, c: &Sig, f: &Sig, cx: &Ctx, out: &mut Found) {
    out.compared += 1;
    let mut bad = |what: &str, a: String, b: String| {
        if a != b {
            out.bad
                .push(format!("{label}: {what}\n    D: {a}\n    E: {b}"));
        }
    };
    bad("==", format!("{}", c == f), "true".into());
    bad("digest", c.digest().to_string(), f.digest().to_string());
    bad("Display", c.to_string(), f.to_string());
    bad(
        "holds_only_own_variables",
        c.holds_only_own_variables().to_string(),
        f.holds_only_own_variables().to_string(),
    );
    bad(
        "holds_no_variable",
        c.holds_no_variable().to_string(),
        f.holds_no_variable().to_string(),
    );
    let (mut oc, mut of) = (order_with_marks(c), order_with_marks(f));
    if cx.unfinished {
        oc.retain(|v| !cx.internal.contains(v));
        of.retain(|v| !cx.internal.contains(v));
    }
    let (oc, of) = match cx.clash {
        true => (
            once_each_internal(oc, &cx.internal),
            once_each_internal(of, &cx.internal),
        ),
        false => {
            // Landing review round 8: a signature that holds two different compact
            // signatures with the same internal results (the copy `add_arrows_of` adds beside
            // the original, or the copies `fresh` makes of one function held twice, as `h{i}`
            // of "held shared" holds `h{i-1}`) lists each such name once per held signature in
            // D, each from its own mark, and once in E, whose `vars_order` merges the variables
            // by name: the difference of Q2.3 again, which no reader sees (proof at
            // `Sig::vars_marks`). So each internal name D lists more than
            // once must come from that many marks of different signatures, and E must list it
            // at most once; the orders are then compared with each internal name once.
            // In an `Arc`, which a mark's holder is read against (`RunMark::holder`).
            let root = Arc::new(c.clone());
            for v in &cx.internal {
                let count = |o: &[Arc<str>]| o.iter().filter(|x| *x == v).count();
                let (in_d, in_e) = (count(&oc), count(&of));
                let sigs: BTreeSet<usize> = (root.vars_marks().iter())
                    .filter(|m| m.runs.iter().any(|r| r.names::<Arc<str>>().contains(v)))
                    .map(|m| m.holder(&root))
                    .collect();
                if in_d > 1 && (in_d != sigs.len() || in_e > 1) {
                    bad(
                        "an internal name once per held signature",
                        format!("{v} {in_d} times, from {} signatures", sigs.len()),
                        format!("{v} {in_e} times"),
                    );
                }
            }
            (
                once_each_internal(oc, &cx.internal),
                once_each_internal(of, &cx.internal),
            )
        }
    };
    bad("order_with_marks", format!("{oc:?}"), format!("{of:?}"));
    bad(
        "decoded own",
        format!("{:?}", decoded_own_vars(c)),
        format!("{:?}", decoded_own_vars(f)),
    );
    let mut st_c: Vec<_> = c.standing_twice().into_iter().collect();
    let mut st_f: Vec<_> = f.standing_twice().into_iter().collect();
    st_c.sort();
    st_f.sort();
    bad("standing_twice", format!("{st_c:?}"), format!("{st_f:?}"));
    bad(
        "fits_sig both ways",
        format!("{} {}", fits_sig(c, f), fits_sig(f, c)),
        "true true".into(),
    );
    bad(
        "why_unfit",
        format!("{:?}", why_unfit(c, f)),
        format!("{:?}", why_unfit(f, f)),
    );
    let (fc, ff) = (c.facts(), f.facts());
    bad(
        "facts.outer",
        format!("{:?}", fc.outer),
        format!("{:?}", ff.outer),
    );
    bad(
        "facts.outer_classes",
        format!("{:?}", fc.outer_classes),
        format!("{:?}", ff.outer_classes),
    );
    bad("facts.binds", fc.binds.to_string(), ff.binds.to_string());
    let tc = Ty::func(Arc::new(c.clone()));
    let tf = Ty::func(Arc::new(f.clone()));
    bad(
        "held digest",
        Sig::one(vec![], vec![], tc.clone()).digest().to_string(),
        Sig::one(vec![], vec![], tf.clone()).digest().to_string(),
    );
    bad(
        "subtype both ways",
        format!("{} {}", tc.subtype(&tf), tf.subtype(&tc)),
        "true true".into(),
    );
    let reads = |t: &Ty| {
        format!(
            "{} {} {} {}",
            t.closed(),
            t.first_order(),
            t.may_hold_needs(),
            t.holds_vars()
        )
    };
    bad(
        "closed/first_order/may_hold_needs/holds_vars",
        reads(&tc),
        reads(&tf),
    );
    let (mut vc, mut vf) = (
        zedc_types::ty::Vars::default(),
        zedc_types::ty::Vars::default(),
    );
    tc.vars_outside_held(&mut vc);
    tf.vars_outside_held(&mut vf);
    bad(
        "vars_outside_held",
        format!("{:?}", vc.order),
        format!("{:?}", vf.order),
    );
    bad(
        "union with flat",
        tc.union(&tf).to_string(),
        tf.union(&tf).to_string(),
    );
    bad(
        "meet with flat",
        tc.meet(&tf).to_string(),
        tf.meet(&tf).to_string(),
    );
    bad(
        "int_params/callable_names",
        format!("{:?} {:?}", c.int_params(), c.callable_names()),
        format!("{:?} {:?}", f.int_params(), f.callable_names()),
    );
}

/// The refusal an operation that meets a compact forward's need alone (`Need::map_tys`,
/// `Need::replace`) documents: the start of its panic message, and whether D's signature
/// warrants it under this binding.
struct Refusal {
    says: &'static str,
    warranted: bool,
}

/// `op` on D and on E, compared. With `refusal`, D may panic where E does not, but only with
/// that message and only where it is warranted; any other panic, on either side or on both,
/// is a difference (landing round 7, Codex L7.Codex-battery-panic: every D-only panic was
/// counted a refusal, and two panics passed).
fn run_op(
    label: &str,
    cx: &Ctx,
    out: &mut Found,
    refusal: Option<Refusal>,
    op: impl Fn(&Arc<Sig>) -> Sig,
    c: &Arc<Sig>,
    f: &Arc<Sig>,
) {
    let said = |e: &Box<dyn std::any::Any + Send>| -> String {
        (e.downcast_ref::<String>().cloned())
            .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
            .unwrap_or_default()
    };
    let rc = catch_unwind(AssertUnwindSafe(|| op(c)));
    let rf = catch_unwind(AssertUnwindSafe(|| op(f)));
    match (rc, rf) {
        (Ok(a), Ok(b)) => cmp_sig(label, &a, &b, cx, out),
        (Err(e), Ok(_)) => match &refusal {
            Some(r) if r.warranted && said(&e).starts_with(r.says) => out.d_refused += 1,
            _ => out
                .bad
                .push(format!("{label}: D panicked, E did not: {}", said(&e))),
        },
        (Ok(_), Err(e)) => out
            .bad
            .push(format!("{label}: E panicked, D did not: {}", said(&e))),
        (Err(d), Err(e)) => out.bad.push(format!(
            "{label}: both panicked: D {}; E {}",
            said(&d),
            said(&e)
        )),
    }
}

fn held_one(t: Ty) -> Sig {
    Sig::one(vec![], vec![], t)
}

/// `s` with its arrows' types replaced by `b`, and its needs each mapped by `need`.
fn each_need(s: &Sig, b: &Binds, need: impl Fn(&Need) -> Need) -> Sig {
    let mut x = s.clone();
    for ar in &mut x.arrows {
        for p in &mut ar.params {
            *p = p.replace(b);
        }
        ar.result = ar.result.replace(b);
    }
    x.needs = s.needs.iter().map(need).collect();
    x.facts = Default::default();
    x
}

/// `s` made anew with its facts cleared at every depth: in its arrows, in its needs, in each
/// function their types hold and in the callee of each compact forward. `Sig::settle` keeps
/// what a signature was settled into in its facts, once, as the checker settles each
/// signature under one solution; the battery settles the same signature under many bindings,
/// so each settle starts from such a copy (landing round 7, Gemini B5: reusing the pair made
/// every binding after the first return the first one's result).
fn fresh(s: &Arc<Sig>) -> Arc<Sig> {
    let mut x = Sig::clone(s);
    x.facts = Default::default();
    for a in &mut x.arrows {
        a.params
            .iter_mut()
            .for_each(|p| *p = p.with_held_fns(fresh));
        a.result = a.result.with_held_fns(fresh);
    }
    for n in &mut x.needs {
        *n = n.with_held_fns(fresh);
        if let NeedKind::Fwd(fwd) = &mut n.kind {
            let fwd = Arc::make_mut(fwd);
            fwd.callee = fresh(&fwd.callee);
        }
    }
    Arc::new(x)
}

/// All operations of the battery under one binding. `internal_key`: `b` binds an internal
/// result, which `Sig::settle` and `Sig::solved_with` do not take.
fn ops(name: &str, c: &Arc<Sig>, f: &Arc<Sig>, b: &Binds, internal_key: bool, cx: &Ctx) -> Found {
    let cx = &cx.under(b);
    let mut out = Found::default();
    let bs: Vec<String> = (b.iter())
        .map(|(k, t)| match t.as_var() {
            Some(v) => format!("{k}->{v}"),
            None => format!("{k}->[{t}]"),
        })
        .collect();
    let l = |op: &str| format!("{name} {op} {{{}}}", bs.join(", "));
    let o = &mut out;
    run_op(&l("Sig::replace"), cx, o, None, |s| s.replace(b), c, f);
    run_op(&l("Sig::renamed"), cx, o, None, |s| s.renamed(b), c, f);
    let replace_outside = |s: &Arc<Sig>| s.replace_outside(b);
    run_op(
        &l("Sig::replace_outside"),
        cx,
        o,
        None,
        replace_outside,
        c,
        f,
    );
    let flat_for = |s: &Arc<Sig>| s.flat_for(b).into_owned();
    run_op(&l("Sig::flat_for"), cx, o, None, flat_for, c, f);
    let in_tuple = |s: &Arc<Sig>| Ty::tuple(vec![Ty::func(s.clone())]);
    let op = |s: &Arc<Sig>| held_one(in_tuple(s).replace(b));
    run_op(&l("tuple(func).replace"), cx, o, None, op, c, f);
    let op = |s: &Arc<Sig>| held_one(in_tuple(s).renamed(b));
    run_op(&l("tuple(func).renamed"), cx, o, None, op, c, f);
    let op = |s: &Arc<Sig>| held_one(in_tuple(s).replace_outside(b));
    run_op(&l("tuple(func).replace_outside"), cx, o, None, op, c, f);
    let op = |s: &Arc<Sig>| held_one(Ty::func(s.clone()).replace(b));
    run_op(&l("func.replace"), cx, o, None, op, c, f);
    let op = |s: &Arc<Sig>| held_one(Ty::func(s.clone()).renamed(b));
    run_op(&l("func.renamed"), cx, o, None, op, c, f);
    // As `instantiated` (walk.rs) replaces: on the signature `flat_for` gives, arrows and
    // needs one by one.
    let instantiated = |s: &Arc<Sig>| {
        let base = s.flat_for(b);
        let mut x = each_need(&base, b, |n| n.replace(b));
        for v in b.keys() {
            x.own.remove(v);
            x.held.remove(v);
        }
        x
    };
    run_op(&l("instantiated"), cx, o, None, instantiated, c, f);
    // `Need::map_tys` and `Need::replace` one by one, on the signature as it is.
    // `Need::map_tys` refuses every compact forward; `Need::replace` one that the binding
    // must decode, which is when `Sig::flat_for` decodes.
    let refusal = |says, warranted| Some(Refusal { says, warranted });
    let op = |s: &Arc<Sig>| each_need(s, b, |n| n.map_tys(|t| t.replace(b)));
    let map_says = "`Need::map_tys` does not take a compact forward";
    let r = refusal(map_says, c.has_fwd_needs());
    run_op(&l("Need::map_tys each"), cx, o, r, op, c, f);
    let op = |s: &Arc<Sig>| each_need(s, b, |n| n.replace(b));
    let replace_says = "a compact forward is replaced in only by a replacement that keeps it";
    let must = matches!(c.flat_for(b), std::borrow::Cow::Owned(_));
    run_op(
        &l("Need::replace each"),
        cx,
        o,
        refusal(replace_says, must),
        op,
        c,
        f,
    );
    if !internal_key {
        let solve = |v: &str| b.get(v).cloned();
        let op = |s: &Arc<Sig>| Sig::clone(&fresh(s).settle(&solve));
        run_op(&l("Sig::settle"), cx, o, None, op, c, f);
        let op = |s: &Arc<Sig>| s.solved_with(&solve);
        run_op(&l("Sig::solved_with"), cx, o, None, op, c, f);
        let op = |s: &Arc<Sig>| held_one(in_tuple(&fresh(s)).settle(&solve));
        run_op(&l("tuple(func).settle"), cx, o, None, op, c, f);
    }
    let op = |s: &Arc<Sig>| {
        let mut x = Sig::clone(s);
        x.add_arrows_of(&s.replace(b));
        x
    };
    run_op(&l("add_arrows_of replaced"), cx, o, None, op, c, f);
    out
}

impl Found {
    fn add(&mut self, other: Found) {
        self.bad.extend(other.bad);
        self.compared += other.compared;
        self.d_refused += other.d_refused;
    }

    /// Fails on any difference, or if too little was compared, or, with `refuses`, if no
    /// need was refused (the held battery's top signature has no forward of its own).
    fn check(&self, name: &str, refuses: bool) {
        for m in &self.bad {
            eprintln!("MISMATCH {m}");
        }
        assert!(
            self.bad.is_empty(),
            "{name}: {} differences",
            self.bad.len()
        );
        assert!(self.compared > 1000, "{name}: {} compared", self.compared);
        assert!(!refuses || self.d_refused > 0, "{name}: no need refused");
    }
}

/// The bindings of the battery for a pair: each of five visible variables bound to a new
/// variable, `int`, a union, the signature in a function and in a tuple, an internal result
/// and a union with one, another visible variable, a swap, and a union with another; and
/// each of two internal results bound to a new variable, `int` and a visible variable.
fn bindings(c: &Arc<Sig>, vis: &[Arc<str>], internal: &BTreeSet<Arc<str>>) -> Vec<(Binds, bool)> {
    let h: Vec<Arc<str>> = internal.iter().take(2).cloned().collect();
    let var = |s: &str| Ty::var(s.into());
    let mut binds: Vec<(Binds, bool)> = Vec::new();
    for (i, v) in vis.iter().take(5).enumerate() {
        let one = |t: Ty| [(v.clone(), t)].into_iter().collect::<Binds>();
        binds.push((one(var("Fresh")), false));
        binds.push((one(Ty::carrier(Carrier::Int)), false));
        binds.push((one(var("Fresh1").union(&var("Fresh2"))), false));
        binds.push((one(Ty::func(c.clone())), false));
        binds.push((one(Ty::tuple(vec![Ty::func(c.clone())])), false));
        for hh in &h {
            binds.push((one(Ty::var(hh.clone())), false));
            binds.push((one(var("Fresh").union(&Ty::var(hh.clone()))), false));
        }
        for w in vis.iter().skip(i + 1).take(4) {
            binds.push((one(Ty::var(w.clone())), false));
            let swap = [
                (v.clone(), Ty::var(w.clone())),
                (w.clone(), Ty::var(v.clone())),
            ];
            binds.push((swap.into_iter().collect(), false));
            binds.push((one(Ty::var(w.clone()).union(&var("Fresh"))), false));
        }
    }
    for hh in &h {
        let one = |t: Ty| [(hh.clone(), t)].into_iter().collect::<Binds>();
        binds.push((one(var("Fresh")), true));
        binds.push((one(Ty::carrier(Carrier::Int)), true));
        if let Some(v) = vis.first() {
            binds.push((one(Ty::var(v.clone())), true));
        }
    }
    binds
}

/// The sets of pairs, each run by tests of its own so that each test runs in under 60 s.
#[derive(Clone, Copy, PartialEq)]
enum Set {
    /// Each signature with a forward of a chain of four by `f`, of three by a lambda, and of
    /// a function whose lambdas read a parameter, each also with its arrows emptied, and the
    /// unfinished forward of the function whose lambdas read a parameter, with its arrows
    /// kept and emptied.
    Base,
    /// Those of a program whose signatures hold other functions with kept forwards, shared
    /// (Codex's `b06`), each also with its arrows emptied.
    Shared,
    /// As `Shared`, the functions held nested two chains deep (`c02`).
    Nested,
}

/// The pairs of the sets `sets`.
fn pairs(sets: &[Set]) -> Vec<Pair> {
    let mut out: Vec<Pair> = Vec::new();
    let mut from_src = |name: &str, src: &str| {
        let (d, _) = run_with_cfg(src, R10Config::default());
        let e = expected_of(src, &d);
        assert_info_eq(name, &e, &d);
        let mut ids: Vec<_> = (d.sigs.iter())
            .filter(|(_, s)| s.has_fwd_needs())
            .map(|(id, _)| *id)
            .collect();
        ids.sort();
        assert!(!ids.is_empty(), "{name}: a signature keeps a forward");
        for id in ids {
            let c = d.sigs[&id].clone();
            out.push((format!("{name}#{id}"), c.clone(), e.sigs[&id].clone()));
            let mut bare = Sig::clone(&c);
            for a in &mut bare.arrows {
                a.params.fill(Ty::empty());
                a.result = Ty::empty();
            }
            let bf = flat_of(&bare);
            out.push((format!("{name}#{id} bare"), Arc::new(bare), Arc::new(bf)));
        }
    };
    let held = "h0(positional a, positional m) = m.map((x: int) -> a).map((x: int) -> a);\n\
                h1(positional a, positional m) = h0(a, m);\n";
    if sets.contains(&Set::Base) {
        from_src("chain f 4", &chain_src(4, "f", false));
        from_src("chain lambda 3", &chain_src(3, "lambda", false));
        from_src("held lambda", held);
    }
    // Landing review round 8, Claude F2: signatures that hold other functions with kept
    // forwards, shared (Codex's `b06`) and nested two chains deep (`c02`).
    if sets.contains(&Set::Shared) {
        let mut shared = String::from("h0(positional f, positional m) = m.map(f).map(f);\n");
        // Three levels where `b06` has six: the shape (each level holds the one below twice)
        // is what the battery needs, and six take over 60 s.
        for i in 1..=3 {
            let j = i - 1;
            shared.push_str(&format!(
                "h{i}(positional f, positional m) = (h0(f, m), h{j}, h{j});\n"
            ));
        }
        shared.push_str("top(positional f, positional m) = (h3, m.map(f));\n");
        from_src("held shared", &shared);
    }
    let nested = "h0(positional f, positional m) = m.map(f);\n\
                  h1(positional f, positional m) = h0(f, m).map(f);\n\
                  h2(positional f, positional m) = h1(f, m).map(f);\n\
                  k0(positional f, positional m) = m.map(f);\n\
                  k1(positional f, positional m) = k0(f, m).map(f);\n\
                  k2(positional f, positional m) = k1(f, m).map(f);\n\
                  p(positional f, positional m) = ((h2, k2), h1(f, m).map(f));\n\
                  q(positional f, positional m) = (p(f, m), (k2, h2), k1(f, m));\n\
                  r(positional f, positional m) = (q, q(f, m));\n";
    if sets.contains(&Set::Nested) {
        from_src("held nested", nested);
    }
    if sets.contains(&Set::Base) {
        for clear in [false, true] {
            let (c, f) = unfinished_pair(held, clear);
            out.push((format!("unfinished held clear={clear}"), c, f));
        }
    }
    out
}

fn ctx(name: &str, c: &Sig) -> Ctx {
    Ctx {
        internal: internal_names(c),
        unfinished: name.starts_with("unfinished"),
        clash: false,
    }
}

/// Every pair through the battery, at the top level.
#[test]
fn landing6_battery_top() {
    battery_top(&[Set::Base]);
}

/// As `landing6_battery_top`, on `Set::Shared`.
#[test]
fn landing6_battery_top_shared() {
    battery_top(&[Set::Shared]);
}

/// As `landing6_battery_top`, on `Set::Nested`.
#[test]
fn landing6_battery_top_nested() {
    battery_top(&[Set::Nested]);
}

fn battery_top(sets: &[Set]) {
    let mut found = Found::default();
    for (name, c, f) in pairs(sets) {
        let cx = ctx(&name, &c);
        cmp_sig(&format!("{name} as is"), &c, &f, &cx, &mut found);
        let vis = visible_names(&f, &cx.internal);
        for (b, internal_key) in bindings(&c, &vis, &cx.internal) {
            found.add(ops(&name, &c, &f, &b, internal_key, &cx));
        }
    }
    found.check("top", true);
}

/// Every pair held in a function inside a tuple of an outer signature, beside an outer
/// variable `Outside`, through the battery: the held signature is entered with `nested` set.
/// `Outside -> W`, with `W` an internal result, makes the clash of Q2.3.
#[test]
fn landing6_battery_held() {
    battery_held(&[Set::Base]);
}

/// As `landing6_battery_held`, on `Set::Shared` and `Set::Nested`.
#[test]
fn landing6_battery_held_holding() {
    battery_held(&[Set::Shared, Set::Nested]);
}

fn battery_held(sets: &[Set]) {
    let mut found = Found::default();
    for (name, c, f) in pairs(sets) {
        let wrap = |s: &Arc<Sig>| {
            Arc::new(Sig::one(
                vec![],
                vec![],
                Ty::tuple(vec![Ty::func(s.clone()), Ty::var("Outside".into())]),
            ))
        };
        let (wc, wf) = (wrap(&c), wrap(&f));
        let cx = ctx(&name, &c);
        let vis = visible_names(&f, &cx.internal);
        let mut binds: Vec<Binds> = Vec::new();
        for v in vis.iter().take(5) {
            binds.push([(v.clone(), Ty::var("Fresh".into()))].into_iter().collect());
            let int = Ty::carrier(Carrier::Int);
            binds.push([(v.clone(), int)].into_iter().collect());
            for hh in cx.internal.iter().take(2) {
                binds.push([(v.clone(), Ty::var(hh.clone()))].into_iter().collect());
            }
        }
        for hh in cx.internal.iter().take(2) {
            let fresh = Ty::var("Fresh".into());
            binds.push([(hh.clone(), fresh)].into_iter().collect());
            let outside: Arc<str> = "Outside".into();
            binds.push([(outside, Ty::var(hh.clone()))].into_iter().collect());
        }
        cmp_sig(&format!("{name} held as is"), &wc, &wf, &cx, &mut found);
        for b in &binds {
            let internal_key = b.keys().any(|k| cx.internal.contains(k));
            found.add(ops(&format!("{name} held"), &wc, &wf, b, internal_key, &cx));
        }
    }
    found.check("held", false);
}

/// `src` checked under E and D, which must agree on every field of `Info`; whether D kept a
/// forward.
fn agree(label: &str, src: &str, bad: &mut Vec<String>) -> bool {
    let (d, _) = run_with_cfg(src, R10Config::default());
    let e = expected_of(src, &d);
    if let Err(msg) = info_eq_full(label, &e, &d) {
        bad.push(format!("{src}{msg}"));
    }
    d.sigs.values().any(|s| s.has_fwd_needs())
}

/// Programs where a function holds a finished chain function, whose internal results are
/// named by runs, beside many own variables (T, U, V, W, T5, T6, T7), so the names may clash.
/// The other program's E is the control: it differs from this D.
#[test]
fn landing6_clash_programs() {
    let tails = [
        "p(positional a, positional b, positional c, positional d, positional e) = (H, a, b, c, d, e);\n",
        "p(positional a, positional b, positional c, positional d, positional e, positional g, positional i) = ((y) -> (H, y, a), b, c, d, e, g, i);\n",
        "p(positional f, positional m, positional a, positional b, positional c, positional d, positional e) = (H(f, m), a, b, c, d, e);\n",
        "p(positional a, positional b, positional c, positional d, positional e, positional g) = (H, a, b, c, d, e, g);\nq(positional x) = p(x, x, x, x, x, x);\n",
        "p(positional f, positional m, positional a, positional b, positional c, positional d, positional e) = ((y) -> (H(f, y), a, b, c, d, e), m);\n",
    ];
    let mut bad = Vec::new();
    let mut kept = 0;
    for (n, form) in [(4usize, "f"), (3, "lambda"), (6, "f")] {
        for t in tails {
            let src = chain_src(n, form, false) + &t.replace('H', &format!("h{}", n - 1));
            kept += usize::from(agree("clash", &src, &mut bad));
        }
    }
    let one = chain_src(4, "f", false) + &tails[0].replace('H', "h3");
    let other = chain_src(4, "f", false) + &tails[1].replace('H', "h3");
    let (e2, _) = run_expected(&other);
    let (d1, _) = run_with_cfg(&one, R10Config::default());
    assert!(info_eq_full("control", &e2, &d1).is_err(), "control");
    for b in &bad {
        eprintln!("{b}");
    }
    assert!(bad.is_empty(), "{} of 15 programs differ", bad.len());
    assert_eq!(kept, 15, "each program keeps a forward");
}

/// Calls that reach `instantiated` (walk.rs): a callee with a compact forward, a parameter
/// whose variable stands inside a function type, and a literal argument for a parameter that
/// a held lambda reads. None of the three `landing6_instantiated_*` tests depends on the
/// decode in `instantiated` (`flat_for`): each passes with it taken out. The test that does is
/// `landing6_call_fixing_a_parameter_a_held_lambda_reads_agrees_with_e` (landing review round
/// 8, Claude NB4).
#[test]
fn landing6_instantiated_programs() {
    let defs = [
        "h0(positional a, positional g, positional m) = m.map(g).map((x: int) -> a);\n\
         h1(positional a, positional g, positional m) = h0(a, g, m);\n",
        "h0(positional a, positional g, positional m) = m.map(g).map((x) -> a);\n\
         h1(positional a, positional g, positional m) = h0(a, g, m).map(g);\n",
        "h0(positional a, positional g, positional m) = m.map((x: int) -> a).map(g);\n\
         h1(positional a, positional g, positional m) = h0(a, g, m);\n\
         h2(positional a, positional g, positional m) = h1(a, g, m);\n",
    ];
    let calls = [
        "main(m: MainArgs) {\n  r = H(1, x -> x + 1, {\"k\" -> 0})[\"k\"];\n  m.stdout <- [\"${r}\"];\n}\n",
        "p(positional m) = H(1, x -> x, m);\n",
        "q(positional g) = H(2, g, {\"k\" -> 0});\n",
    ];
    let mut bad = Vec::new();
    let mut kept = 0;
    for d in defs {
        let top = if d.contains("h2(") { "h2" } else { "h1" };
        for c in calls {
            let src = format!("{d}{}", c.replace('H', top));
            kept += usize::from(agree("inst", &src, &mut bad));
        }
    }
    for b in &bad {
        eprintln!("{b}");
    }
    assert!(bad.is_empty(), "{} of 9 programs differ", bad.len());
    assert!(kept > 0, "a program keeps a forward");
}

/// As [`landing6_instantiated_programs`], with written parameter types holding a variable
/// inside a function type, as `map2(xs: T, f: (T) -> T)` (l02_12), so `ties` is set.
#[test]
fn landing6_instantiated_written() {
    let defs = [
        "h0(positional a, positional g, positional m) = m.map(g).map((x: int) -> a);\n\
         h1(a, g: (T) -> T, m) = h0(a, g, m);\n",
        "h0(positional a, positional g, positional m) = m.map(g).map((x: int) -> a);\n\
         h1(positional a, positional g, positional m) = h0(a, g, m);\n\
         h2(a, g: (T) -> T, m) = h1(a, g, m);\n",
        "h0(positional g, positional m) = m.map(g);\n\
         h1(positional g, positional m) = h0(g, m).map(g);\n\
         h2(a, g: (T) -> T, m) = (h1(g, m), a);\n",
        "h0(positional a, positional g, positional m) = m.map(g).map((x) -> a);\n\
         h1(positional a, positional g, positional m) = h0(a, g, m).map(g);\n\
         h2(a, g: (T) -> T, m) = h1(a, g, m);\n",
    ];
    let calls = [
        "main(mm: MainArgs) {\n  r = H(a: 1, g: (v) -> v + 1, m: {\"k\" -> 0});\n  mm.stdout <- [\"x\"];\n}\n",
        "p(positional m) = H(a: 1, g: (v) -> v, m: m);\n",
        "q(positional m) = H(a: 2.5, g: (v: int) -> v * 5, m: m);\n",
    ];
    let mut bad = Vec::new();
    let mut kept = 0;
    for d in defs {
        let top = if d.contains("h2(") { "h2" } else { "h1" };
        for c in calls {
            let src = format!("{d}{}", c.replace('H', top));
            kept += usize::from(agree("instw", &src, &mut bad));
        }
    }
    for b in &bad {
        eprintln!("{b}");
    }
    assert!(bad.is_empty(), "{} of 12 programs differ", bad.len());
    assert!(kept > 0, "a program keeps a forward");
}

/// Programs whose bottom function has a written parameter of function type with an own
/// variable, under chains of two to four, called with fitting and unfitting arguments. Claude
/// meant `instantiated` to meet a forward here; none of the 36 keeps one (measured in landing
/// round 6, and asserted below), so these check that D and E agree, errors included, where
/// the written type stops the forward.
#[test]
fn landing6_instantiated_forward() {
    let defs: [(&str, &[&str]); 4] = [
        (
            "h0(positional a, positional m, g: (T) -> T) = m.map(g).map((x: int) -> a);\n\
             h1(positional a, positional m, positional g) = h0(a, m, g: g);\n\
             h2(positional a, positional m, positional g) = h1(a, m, g);\n",
            &["h1", "h2"],
        ),
        (
            "f1(positional a, positional m, g: (T) -> T) = m.map(g);\n\
             f2(positional a, positional m, positional g) = f1(a, m, g: g).map(g);\n\
             f3(positional a, positional m, positional g) = f2(a, m, g).map((x) -> a);\n",
            &["f2", "f3"],
        ),
        (
            "h0(positional a, positional m, g: (T) -> T) = m.map((x) -> a).map(g);\n\
             h1(positional a, positional m, positional g) = h0(a, m, g: g).map((x: int) -> a);\n\
             h2(positional a, positional m, positional g) = h1(a, m, g).map((x) -> a);\n",
            &["h1", "h2"],
        ),
        (
            "f1(positional a, positional m, g: (T) -> T) = m.map(g).map((x) -> a);\n\
             f2(positional a, positional m, positional g) = f1(a, m, g: g).map((x) -> a);\n\
             f3(positional a, positional m, positional g) = f2(a, m, g).map(g);\n\
             f4(positional a, positional m, positional g) = f3(a, m, g).map((x) -> a);\n",
            &["f2", "f3", "f4"],
        ),
    ];
    let calls = [
        "p(positional m) = H(1, m, (v) -> v);\n",
        "q(positional m) = H(2.5, m, (v: int) -> v * 5);\n",
        "r(positional m, positional b) = H(b, m, (v: int) -> v);\n",
        "main(mm: MainArgs) {\n  r = H(1, [0, 1], (v) -> v + 1);\n  mm.stdout <- [\"x\"];\n}\n",
    ];
    let mut bad = Vec::new();
    let mut kept = 0;
    for (d, tops) in defs {
        for top in tops {
            for c in calls {
                let src = format!("{d}{}", c.replace('H', top));
                kept += usize::from(agree("instf", &src, &mut bad));
            }
        }
    }
    for b in &bad {
        eprintln!("{b}");
    }
    assert!(bad.is_empty(), "{} of 36 programs differ", bad.len());
    assert_eq!(kept, 0, "a program keeps a forward: update the doc above");
}

/// Programs that pass a chain function, which holds a forward, to a written function type
/// whose named parameters come in another order (`fit_declared_as`, walk.rs, the permuted
/// signature's `own`), or do not fit it.
#[test]
fn landing6_permuted_programs() {
    let chains = [
        "h0(f, m) = m.map(f);\nh1(f, m) = h0(f: f, m: m).map(f);\nh2(f, m) = h1(f: f, m: m).map(f);\n",
        "h0(f, m) = m.map(f);\nh1(f, m) = h0(f: f, m: m).map((x) -> f(x));\nh2(f, m) = h1(f: f, m: m).map((x) -> f(x));\nh3(f, m) = h2(f: f, m: m).map(f);\n",
        "h0(f, m) = m.map(f).map(f);\nh1(f, m) = h0(f: f, m: m).map(f);\nh2(f, m) = h1(f: f, m: m);\n",
    ];
    let users = [
        "use(g: (m: [int], f: (int) -> int) -> [int]) = g(m: [1, 2], f: (x) -> x + 1);\np() = use(g: H);\n",
        "use(g: (f: (int) -> int, m: [int]) -> [int]) = g(f: (x) -> x + 1, m: [1, 2]);\np() = use(g: H);\n",
        "use(positional t: T, g: (m: [T], f: (T) -> T) -> [T]) = g(m: [t], f: (x) -> x);\np() = use(3, g: H);\n",
        "main(mm: MainArgs) {\n  r = use(g: H);\n  mm.stdout <- [\"x\"];\n}\nuse(g: (m: [int], f: (int) -> int) -> [int]) = g(m: [1, 2], f: (x) -> x + 1);\n",
        "use(g: (m: [int], f: (int) -> int) -> [bool]) = g(m: [1, 2], f: (x) -> x + 1);\np() = use(g: H);\n",
        "use(g: (m: [int], f: (bool) -> int) -> [int]) = g(m: [1, 2], f: (x) -> 1);\np() = use(g: H);\n",
        "use(g: (m: [int], k: (int) -> int) -> [int]) = g(m: [1, 2], k: (x) -> x + 1);\np() = use(g: H);\n",
        "use(g: (m: [int], f: (int) -> int, z: int) -> [int]) = g(m: [1, 2], f: (x) -> x, z: 0);\np() = use(g: H);\n",
    ];
    let mut bad = Vec::new();
    let mut kept = 0;
    for c in chains {
        let top = if c.contains("h3(") { "h3" } else { "h2" };
        for u in users {
            let src = format!("{c}{}", u.replace('H', top));
            kept += usize::from(agree("perm", &src, &mut bad));
        }
    }
    for b in &bad {
        eprintln!("{b}");
    }
    assert!(bad.is_empty(), "{} of 24 programs differ", bad.len());
    assert!(kept > 0, "a program keeps a forward");
}
