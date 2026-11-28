//! Expected output of the r10 tests (PROOF-map-chain-d-skip-and-admit, step 2, row
//! FAIL-e-merge-by-name-internal-result): the output of the eager checker E (the flat needs)
//! on each program the tests ran E on, recorded while E existed (commit "r10 tests: record E's
//! output as expected output", where each line was written only after D's text was found
//! equal to E's). E is removed; D's output on each of those programs is checked against it
//! ([`check_d`], called by `run_expected`).
//!
//! The text of a check is [`info_text`]: every field of [`Info`], each map and set in a fixed
//! order, every signature in its flat form at every depth ([`deep_flat`]) written by its
//! `Debug`, which writes every field of a signature (its cached `facts` as `_`), each row,
//! payload shape and signature it holds written once and named by a hash of its text
//! ([`Names`]). E's signatures held no compact forward, so `deep_flat` left their fields as
//! they were; D's are decoded at every depth. D's text equal to E's means that D's
//! signatures, decoded, are E's field by field, which is more than the tests compared before
//! (`sig_eq_full` compares the decoded needs of the top level only, by the `PartialEq` that
//! takes a compact forward and its flat needs as equal).
//!
//! `expected.out` holds one line per program: the first 32 hex digits of the BLAKE3 hash of
//! its source (its key), the length of its text in bytes, and the BLAKE3 hash of the text in
//! hex. A program is found by its source, so every test that runs `run_expected` on a program
//! is covered without a label of its own, and a program two tests run is one line. The text is
//! not stored: the chains of 100 links write texts of megabytes, and the sweeps check 99
//! chains of each form. On a mismatch the test gives the two lines; E's text can be rebuilt
//! from the commit that recorded the file, which still has E.
//!
//! With `ZED_R10_EXPECTED_WRITE=<dir>` set, [`check_d`] writes each program's line to the file
//! `<dir>/<key>` instead of comparing; a program run twice must write the same line.
//! `LC_ALL=C sort <dir>/*` is then the new `expected.out`. A line written so is D's output, no
//! longer checked against E: each changed line must be explained by the change that made it.

use std::collections::{BTreeMap, HashMap};
use std::fmt::Debug;
use std::sync::{Arc, OnceLock};

use zed_collections::by_address::ByAddress;
use zedc_types::ty::{DebugPart, NodeId, Sig, Ty, debug_cut};

use crate::check::{Info, RemapPlan};

/// `s` with its compact forwards decoded and their internal results among its own variables:
/// the flat form of the same signature. It is here, not in `r10_tests.rs` where most of its
/// callers are, so that this file imports nothing from `r10_tests.rs` and the two are no import
/// cycle (step S.1f); `r10_tests.rs` and its other children take it from here.
pub(super) fn flat_of(s: &Sig) -> Sig {
    let mut flat = s.clone();
    let (needs, own) = s.decoded_needs_and_own();
    flat.needs = needs.into_owned().into();
    flat.own = own.into_owned();
    flat.facts = Default::default();
    flat
}

/// The signatures [`deep_flat`] has done, by address: a function a nest holds at several places
/// is done once. The map holds each key's `Arc`, so no other signature takes its address while
/// the map lives ([`ByAddress`]).
type Memo = HashMap<ByAddress<Sig>, Arc<Sig>>;

/// `s` with every compact forward decoded ([`flat_of`]), in `s` and in each function it holds,
/// in its arrows and in its needs, at any depth: the flat form E builds.
/// Complexity: each signature of the nest is entered once (`memo`), so the cost is the size of
/// the flat nest. Without the memo a chain whose functions each hold the one before twice (the
/// "held shared" programs) would be walked once per path, 2^depth times. The recursion is as
/// deep as the nest, at most the 100 links of the longest chain the tests check.
fn deep_flat(s: &Arc<Sig>, memo: &mut Memo) -> Arc<Sig> {
    if let Some(done) = memo.get(&Arc::as_ptr(s)) {
        return done.clone();
    }
    let mut copy = flat_of(s);
    for a in &mut copy.arrows {
        for p in &mut a.params {
            *p = deep_flat_ty(p, memo);
        }
        a.result = deep_flat_ty(&a.result, memo);
    }
    copy.needs = (copy.needs.iter())
        .map(|n| n.with_held_fns(|f| deep_flat(f, memo)))
        .collect();
    copy.facts = Default::default();
    let out = Arc::new(copy);
    memo.insert(ByAddress::new(s), out.clone());
    out
}

/// [`deep_flat`] on each function `t` holds.
fn deep_flat_ty(t: &Ty, memo: &mut Memo) -> Ty {
    t.with_held_fns(|f| deep_flat(f, memo))
}

/// The text of the types and signatures of one [`info_text`]: each row, payload shape and
/// signature below a root is written as its name, `#` and the first 32 hex digits of the
/// BLAKE3 hash of its own text, and each name's text is written once, in `texts`.
///
/// Why: `Debug` writes a part once per path to it, and a row shared at each of n levels (the
/// test `r10_rows_shared_at_40_levels_holding_side_sum_variables_agree_with_e`) has 2^n paths;
/// written so, its text did not end in 60 s. Here each part is written once.
///
/// Why the text still compares D with E: a name is a hash of the part's text, and that text is
/// the part's `Debug` text with each part below it replaced by its name, so (by induction on
/// depth, the parts at the bottom holding no part) two parts have one name exactly when their
/// `Debug` texts are equal, up to BLAKE3 collisions (128 bits: for the at most some millions
/// of parts the tests write, odds below 2^-80). Which parts are shared, which differs between D
/// and E, changes how often a part is met, never its name. So the roots' texts with the sorted
/// set of `name = text` lines are equal for D and E exactly when their `Debug` texts are.
///
/// Cost: a part is found again by its number (`Row::node`, `Shape::node`) or, for a signature,
/// by address, and so is written and hashed once; its own text has its fields and, per part it
/// holds, a name of 33 bytes. The total is linear in the number of distinct parts and their
/// own sizes, not in the number of paths. The addresses are sound keys because every signature
/// met lives until `info_text` returns: it is in `Info`, in the [`Memo`] of [`deep_flat`], or
/// in a flat top kept to the end (`info_text`'s `kept`), so no address is reused. The writing
/// recurses once per level of the nest ([`debug_cut`] calls `cut`, which writes the part
/// below), at most the depth of the deepest type the tests build.
#[derive(Default)]
struct Names {
    rows: HashMap<NodeId, String>,
    sigs: HashMap<*const Sig, String>,
    texts: BTreeMap<String, String>,
}

impl Names {
    /// The text of `root` with each part below it written as its name.
    fn text(&mut self, root: DebugPart<'_>) -> String {
        debug_cut(root, &mut |p| Some(self.name(p)))
    }

    /// The name of `p`, written into `texts` the first time `p` is met.
    fn name(&mut self, p: DebugPart<'_>) -> String {
        let found = match p {
            DebugPart::Row(r) => self.rows.get(&r.node()),
            DebugPart::Shape(s) => self.rows.get(&s.node()),
            DebugPart::Sig(s) => self.sigs.get(&std::ptr::from_ref(s)),
            DebugPart::Ty(_) => unreachable!("a type is only a root (`debug_cut`)"),
        };
        if let Some(name) = found {
            return name.clone();
        }
        let text = self.text(p);
        let name = format!("#{}", &blake3::hash(text.as_bytes()).to_hex()[..32]);
        match p {
            DebugPart::Row(r) => self.rows.insert(r.node(), name.clone()),
            DebugPart::Shape(s) => self.rows.insert(s.node(), name.clone()),
            DebugPart::Sig(s) => self.sigs.insert(std::ptr::from_ref(s), name.clone()),
            DebugPart::Ty(_) => unreachable!("a type is only a root (`debug_cut`)"),
        };
        self.texts.insert(name.clone(), text);
        name
    }
}

/// `name:` and then each of `lines` on a line of its own.
fn field(out: &mut String, name: &str, lines: Vec<String>) {
    out.push_str(name);
    out.push_str(":\n");
    for l in lines {
        out.push_str("  ");
        out.push_str(&l);
        out.push('\n');
    }
}

/// The entries of a map, `key => value`, sorted, so that the order a hash map keeps does not
/// change the text.
fn entries<K: Debug, V>(
    m: impl IntoIterator<Item = (K, V)>,
    mut v: impl FnMut(V) -> String,
) -> Vec<String> {
    let mut lines: Vec<String> = (m.into_iter())
        .map(|(k, x)| format!("{k:?} => {}", v(x)))
        .collect();
    lines.sort();
    lines
}

/// The members of a set, each by its `Debug`, sorted.
fn members<K: Debug>(s: impl IntoIterator<Item = K>) -> Vec<String> {
    let mut lines: Vec<String> = s.into_iter().map(|k| format!("{k:?}")).collect();
    lines.sort();
    lines
}

/// Each item of a list by its `Debug`, in its order.
fn items<K: Debug>(s: impl IntoIterator<Item = K>) -> Vec<String> {
    s.into_iter().map(|k| format!("{k:?}")).collect()
}

/// A value by its `Debug`.
fn debug(x: &dyn Debug) -> String {
    format!("{x:?}")
}

/// A remap plan by its fields, its folds sorted by level.
fn remap_text(p: &RemapPlan) -> String {
    let RemapPlan {
        order,
        kept,
        folds,
        leaf,
        witness,
        boxed,
    } = p;
    let mut folds: Vec<_> = folds.iter().collect();
    folds.sort_by_key(|(level, _)| **level);
    format!(
        "RemapPlan {{ order: {order:?}, kept: {kept:?}, folds: {folds:?}, leaf: {leaf:?}, \
         witness: {witness:?}, boxed: {boxed:?} }}"
    )
}

/// The text of `info`: each field by name, in the order `Info` declares them.
pub(super) fn info_text(info: &Info) -> String {
    // Names every field with no `..`, so that a field added to `Info` fails to compile here
    // until it is written.
    let Info {
        adopt,
        calls,
        placed,
        fits,
        sigs,
        tops,
        passes,
        quotients,
        ints,
        follows,
        follows_own,
        witness,
        dense,
        atom_keys,
        brackets,
        reduce,
        reducers,
        family_sums,
        list_concats,
        generic_sums,
        split_folds,
        fold_calls,
        split_needs,
        fold_reads,
        escaping_calls,
        remaps,
        boxed_groups,
        errors,
        reported_literals,
        warnings,
        blocking,
        limits,
        // Not printed: the binders of the parameters pushed to, which `ports` finds from the
        // pushes and errors already show; a field here would change the text of every program
        // with such a parameter from what `expected.out` holds (PORT-table-param).
        port_params: _,
    } = info;
    let mut memo = Memo::new();
    let mut names = Names::default();
    // The flat tops, kept so that no signature `names` keys by address is freed (`Names`).
    let mut kept = Vec::new();
    let mut out = String::new();
    field(&mut out, "adopt", entries(adopt, |v| debug(v)));
    field(
        &mut out,
        "calls",
        entries(calls, |s| {
            names.text(DebugPart::Sig(&deep_flat(s, &mut memo)))
        }),
    );
    field(&mut out, "placed", members(placed));
    field(&mut out, "fits", entries(fits, |v| debug(v)));
    field(
        &mut out,
        "sigs",
        entries(sigs, |s| {
            names.text(DebugPart::Sig(&deep_flat(s, &mut memo)))
        }),
    );
    field(
        &mut out,
        "tops",
        entries(tops, |t| {
            let flat = deep_flat_ty(t, &mut memo);
            let text = names.text(DebugPart::Ty(&flat));
            kept.push(flat);
            text
        }),
    );
    field(
        &mut out,
        "passes",
        entries(passes, |m| entries(m, |v| debug(v)).join("; ")),
    );
    field(&mut out, "quotients", entries(quotients, |v| debug(v)));
    field(&mut out, "ints", entries(ints, |v| debug(v)));
    field(&mut out, "follows", entries(follows, |v| debug(v)));
    // `follows_own` (row WIDEN-generic-literal-op-int-instance) came after E and is not
    // printed, so E's text stands: it is read only by the widening pass, whose result is the
    // `warnings` field below, and two runs of D are compared on it in `info_eq_full`.
    let _ = follows_own;
    field(&mut out, "witness", entries(witness, |v| debug(v)));
    field(&mut out, "dense", entries(dense, |v| debug(v)));
    // `atom_keys` (row KERNEL-atom-key-read) came after E: a check that records no read of
    // an atom key prints as E's text did; one recorded still prints, so E's output differs
    // from D's wherever D records one.
    if !atom_keys.is_empty() {
        field(&mut out, "atom_keys", entries(atom_keys, |v| debug(v)));
    }
    field(&mut out, "brackets", entries(brackets, |v| debug(v)));
    field(&mut out, "reduce", entries(reduce, |v| debug(v)));
    field(&mut out, "reducers", entries(reducers, |v| debug(v)));
    field(&mut out, "family_sums", members(family_sums));
    field(&mut out, "list_concats", members(list_concats));
    field(&mut out, "generic_sums", members(generic_sums));
    field(&mut out, "split_folds", entries(split_folds, |v| debug(v)));
    field(&mut out, "fold_calls", entries(fold_calls, |v| debug(v)));
    field(&mut out, "split_needs", entries(split_needs, |v| debug(v)));
    field(&mut out, "fold_reads", members(fold_reads));
    field(&mut out, "escaping_calls", members(escaping_calls));
    field(&mut out, "remaps", entries(remaps, remap_text));
    // `boxed_groups` (rows GROUP-nested, REMAP-dynamic-deep-binder) came after E: a check
    // that boxes no group prints as E's text did; a group boxed still prints, so E's output
    // differs from D's wherever D boxes one.
    if !boxed_groups.is_empty() {
        field(&mut out, "boxed_groups", members(boxed_groups));
    }
    field(&mut out, "errors", items(errors));
    field(&mut out, "reported_literals", items(reported_literals));
    field(&mut out, "warnings", items(warnings));
    // `Cause::Calls::via` (row PORT-block-name) came after E: it is the argument a blocking
    // call writes for the callee's port, read only for the message's wording. A call that
    // writes none prints as E's text did; a `Some` still prints, so E's output still differs
    // from D's wherever D names a port E did not have.
    field(
        &mut out,
        "blocking",
        entries(blocking, |v| debug(v).replace(", via: None", "")),
    );
    field(&mut out, "limits", vec![debug(limits)]);
    let parts = names.texts.iter().map(|(n, t)| format!("{n} = {t}"));
    field(&mut out, "parts", parts.collect());
    out
}

/// The key of a program in `expected.out`: the first 32 hex digits of the BLAKE3 hash of its
/// source (128 bits, so two of the few thousand programs share one with odds below 2^-100).
fn key_of(src: &str) -> String {
    blake3::hash(src.as_bytes()).to_hex()[..32].to_string()
}

/// The line `expected.out` holds for a text, after the key: its length in bytes and its
/// BLAKE3 hash.
fn line_of(text: &str) -> String {
    format!("{} {}", text.len(), blake3::hash(text.as_bytes()).to_hex())
}

/// `expected.out`, by key.
fn expected() -> &'static HashMap<&'static str, &'static str> {
    static EXPECTED: OnceLock<HashMap<&'static str, &'static str>> = OnceLock::new();
    EXPECTED.get_or_init(|| {
        let mut m = HashMap::new();
        for l in include_str!("expected.out").lines() {
            let (key, line) =
                (l.split_once(' ')).expect("a line of expected.out is `key length hash`");
            assert!(
                m.insert(key, line).is_none(),
                "expected.out lists `{key}` twice"
            );
        }
        m
    })
}

/// E's output, rebuilt from `d`, D's output on a program [`check_d`] has checked: `d` with each
/// signature of `calls`, `sigs` and `tops` in its flat form at every depth ([`deep_flat`]),
/// which is what [`info_text`] writes. Why it is E's: the check found `info_text(d)` equal to
/// E's text, every field of `Info` and every field of each signature (its cached `facts`,
/// written as `_`, are left empty here and computed again on use), and `deep_flat` leaves a
/// signature with no compact forward as it is, so E's text is the text of this `Info`. The tests
/// that read E's flat signatures (to compare D's compact ones with them) read these.
/// Complexity: the size of the flat nests, each signature entered once (`deep_flat`'s memo).
pub(super) fn flat_info(d: &Info) -> Info {
    let mut memo = Memo::new();
    let mut e = d.clone();
    for s in e.calls.values_mut().chain(e.sigs.values_mut()) {
        *s = deep_flat(s, &mut memo);
    }
    for t in e.tops.values_mut() {
        *t = deep_flat_ty(t, &mut memo);
    }
    e
}

/// Checks `d`, D's output on `src`, against `expected.out`, or with `ZED_R10_EXPECTED_WRITE`
/// set writes its line (see the module's comment).
pub(super) fn check_d(src: &str, d: &Info) {
    let text = info_text(d);
    let (key, line) = (key_of(src), line_of(&text));
    if let Some(dir) = std::env::var_os("ZED_R10_EXPECTED_WRITE") {
        use std::io::Write as _;
        let path = std::path::Path::new(&dir).join(&key);
        let want = format!("{key} {line}\n");
        match (std::fs::OpenOptions::new())
            .write(true)
            .create_new(true)
            .open(&path)
        {
            Ok(mut f) => f.write_all(want.as_bytes()).expect("the line is written"),
            // A program run twice (by two tests, or by a sweep and its negative control)
            // must give one text.
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
                let had = std::fs::read_to_string(&path).expect("the line is read");
                assert_eq!(had, want, "D gives two texts on one program\n{src}");
            }
            Err(e) => panic!("{}: {e}", path.display()),
        }
        return;
    }
    let Some(want) = expected().get(key.as_str()) else {
        panic!("expected.out has no line for this program (key {key}, text {line})\n{src}");
    };
    assert_eq!(
        *want, line,
        "D's text (length, BLAKE3) on this program differs from the expected output, E's (key \
         {key}); the commit that recorded expected.out still has E, whose text is the \
         expected one\n{src}"
    );
}
