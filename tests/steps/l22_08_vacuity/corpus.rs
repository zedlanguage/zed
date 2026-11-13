//! The theories of DESIGN.md sec:theories and a few more, with the report each prints.

use super::brute::{expand, models};
use super::trivial::{Mode, Theory, in_forest_fragment, render, report};

pub fn semigroup() -> Theory {
    let mut t = Theory::new("Semigroup");
    t.field("mul", 2).law(
        "mulAssoc",
        "a b c",
        "mul(mul(a, b), c) == mul(a, mul(b, c))",
    );
    t
}

pub fn monoid() -> Theory {
    let mut t = semigroup();
    t.name = "Monoid".into();
    t.field("one", 0)
        .law("oneMul", "a", "mul(one, a) == a")
        .law("mulOne", "a", "mul(a, one) == a");
    t
}

pub fn non_comm_ring() -> Theory {
    let mut t = monoid();
    t.name = "NonCommRing".into();
    t.field("add", 2)
        .field("zero", 0)
        .field("neg", 1)
        .law(
            "addAssoc",
            "a b c",
            "add(add(a, b), c) == add(a, add(b, c))",
        )
        .law("addComm", "a b", "add(a, b) == add(b, a)")
        .law("addZero", "a", "add(a, zero) == a")
        .law("addNeg", "a", "add(a, neg(a)) == zero")
        .law(
            "distrib",
            "a b c",
            "mul(a, add(b, c)) == add(mul(a, b), mul(a, c))",
        )
        .law(
            "distribRight",
            "a b c",
            "mul(add(a, b), c) == add(mul(a, c), mul(b, c))",
        );
    t
}

pub fn comm_ring() -> Theory {
    let mut t = non_comm_ring();
    t.name = "CommRing".into();
    t.law("mulComm", "a b", "mul(a, b) == mul(b, a)");
    t
}

pub fn ring() -> Theory {
    let mut t = comm_ring();
    t.name = "Ring".into();
    t.field("sub", 2)
        .law("subDef", "a b", "sub(a, b) == add(a, neg(b))");
    t
}

/// `CommRing` with `law oneNeZero() = one != zero`, which has no binders.
pub fn field_like() -> Theory {
    let mut t = comm_ring();
    t.name = "NonTrivialRing".into();
    t.law("oneNeZero", "", "one != zero");
    t
}

/// A codec with no law on the size of `compress(x)`.
pub fn codec() -> Theory {
    let mut t = Theory::new("Codec");
    t.field("compress", 1).field("decompress", 1).law(
        "roundTrip",
        "x",
        "decompress(compress(x)) == x",
    );
    t
}

pub fn twenty_free() -> Theory {
    let mut t = Theory::new("Twenty");
    for i in 1..=20 {
        t.field(&format!("f{i}"), 0);
    }
    t
}

pub fn group() -> Theory {
    let mut t = monoid();
    t.name = "Group".into();
    t.field("inv", 1)
        .law("mulInv", "a", "mul(a, inv(a)) == one")
        .law("invMul", "a", "mul(inv(a), a) == one");
    t
}

pub fn lattice() -> Theory {
    let mut t = Theory::new("Lattice");
    t.field("join", 2)
        .field("meet", 2)
        .law(
            "joinAssoc",
            "a b c",
            "join(join(a, b), c) == join(a, join(b, c))",
        )
        .law(
            "meetAssoc",
            "a b c",
            "meet(meet(a, b), c) == meet(a, meet(b, c))",
        )
        .law("joinComm", "a b", "join(a, b) == join(b, a)")
        .law("meetComm", "a b", "meet(a, b) == meet(b, a)")
        .law("joinMeet", "a b", "join(a, meet(a, b)) == a")
        .law("meetJoin", "a b", "meet(a, join(a, b)) == a");
    t
}

pub fn boolean_algebra() -> Theory {
    let mut t = lattice();
    t.name = "BooleanAlgebra".into();
    t.field("top", 0)
        .field("bot", 0)
        .field("compl", 1)
        .law("joinBot", "a", "join(a, bot) == a")
        .law("meetTop", "a", "meet(a, top) == a")
        .law("joinCompl", "a", "join(a, compl(a)) == top")
        .law("meetCompl", "a", "meet(a, compl(a)) == bot")
        .law(
            "distrib",
            "a b c",
            "meet(a, join(b, c)) == join(meet(a, b), meet(a, c))",
        );
    t
}

/// A band, a semigroup whose multiplication is idempotent: two laws over one field.
pub fn band() -> Theory {
    let mut t = semigroup();
    t.name = "Band".into();
    t.law("mulIdem", "a", "mul(a, a) == a");
    t
}

pub fn all() -> Vec<Theory> {
    vec![
        semigroup(),
        monoid(),
        non_comm_ring(),
        comm_ring(),
        ring(),
        field_like(),
        codec(),
        twenty_free(),
        group(),
        lattice(),
        boolean_algebra(),
        band(),
    ]
}

/// The report DESIGN.md sec:theories prints for the theory named `name` ("The report's form",
/// "Groups on which deciding is hard"), read from the spec at test time (item
/// SPEC-no-verbatim); `None` where `ZED_SPEC_DIR=none` says not to read the spec.
pub fn designs_report(name: &str) -> Option<String> {
    zed_tests::spec::dir(&format!("the report of {name} against DESIGN.md"))?;
    Some(zed_tests::fences::passage(&format!(
        "trivial models of {name}"
    )))
}

/// The line of a report for the model on one value where every law holds, as DESIGN.md
/// writes it in the report of `CommRing`.
fn every_law_holds() -> Option<String> {
    let report = designs_report("CommRing")?;
    let line = report
        .lines()
        .nth(1)
        .expect("the report has a line for one value");
    Some(line.to_string())
}

#[test]
fn codec_with_no_size_law_lists_the_identity() {
    let Some(one) = every_law_holds() else {
        return;
    };
    let t = codec();
    let r = report(&t, Mode::Default);
    assert_eq!(
        render(&t, &r),
        format!(
            "\
trivial models of Codec
{one}
  on two values, #a | #b:
    compress, decompress, linked by law roundTrip: exactly one model,
      compress: (x -> x), decompress: (x -> x)
  models on two values: 1.
"
        )
    );
}

#[test]
fn twenty_fields_with_no_law_are_free() {
    let Some(one) = every_law_holds() else {
        return;
    };
    let t = twenty_free();
    let r = report(&t, Mode::Default);
    assert_eq!(r.free.len(), 20);
    assert!(r.groups.is_empty());
    assert_eq!(
        render(&t, &r),
        format!(
            "\
trivial models of Twenty
{one}
  on two values, #a | #b:
    f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20 are named by no law: each may be any constant or any projection.
  models on two values: 2^20.
"
        )
    );
}

#[test]
fn comm_ring_lists_the_one_element_ring() {
    let Some(want) = designs_report("CommRing") else {
        return;
    };
    let t = comm_ring();
    let r = report(&t, Mode::Default);
    assert_eq!(render(&t, &r), want);
}

/// Every theory of the corpus: the exhaustive report agrees with brute force, and no search
/// reaches a choice that leads to no model.
#[test]
fn the_corpus_agrees_with_brute_force_and_has_no_dead_ends() {
    for t in all() {
        let full = report(&t, Mode::Exhaustive);
        let short = report(&t, Mode::Default);
        let dead: u64 = full.groups.iter().map(|g| g.dead_ends).sum();
        let nodes: u64 = full.groups.iter().map(|g| g.nodes).sum();
        let listed: usize = full.groups.iter().map(|g| g.models.len()).sum();
        eprintln!(
            "{:<16} forest {:<5} groups {} free {} listed {listed} choices {nodes} dead ends \
             {dead}",
            t.name,
            in_forest_fragment(&t),
            full.groups.len(),
            full.free.len()
        );
        eprint!("{}", render(&t, &short));
        assert_eq!(dead, 0, "{}", render(&t, &full));
        if t.fields.len() <= 6 {
            let mut want = models(&t);
            want.sort();
            assert_eq!(expand(&t, &full), want, "{}", t.name);
        }
    }
}
