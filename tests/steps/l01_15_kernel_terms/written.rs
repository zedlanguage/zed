//! `print::written`: a term on one line with each binder by the name the program wrote and the
//! elaborated `&&` and `||` written back, for a message (NAME-at-print-warnings).

use zed_kernel::Prim;
use zed_kernel::Term;
use zed_kernel::print::{pretty, written};
use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};

/// The part of a kernel name before `@`, as `zedc::elab::written_name` gives it.
fn before_at(k: &str) -> &str {
    k.split_once('@').map_or(k, |(w, _)| w)
}

fn ge0(x: &str) -> Term {
    prim(Prim::Ge, vec![var(x), lit(0)])
}

/// Each place a binder is named is written through the function: a name read, a lambda's
/// parameters, a let's binder, the head of a call. A temporary `$k` has no `@` and stays.
#[test]
fn every_binder_is_named_through_the_function() {
    let t = let_(
        "g@1",
        lam(
            &["x@1", "y@1"],
            prim(Prim::Add, vec![var("x@1"), var("y@1")]),
        ),
        app(var("g@1"), vec![var("x@2"), var("$3")]),
    );
    assert_eq!(
        written(&t, before_at),
        "{ g = (x, y) -> (x + y); g(x, $3) }"
    );
    // Display is unchanged.
    assert_eq!(
        t.to_string(),
        "{ g@1 = (x@1, y@1) -> (x@1 + y@1); g@1(x@2, $3) }"
    );
}

/// `a && b` elaborates to `if a { b } else { false }` and `a || b` to `if a { true } else { b }`
/// (elab/walk.rs): written, each is the operator again, in parentheses as every binary
/// operator is. Any other `if` is written as it is, and `pretty` keeps the `if` form.
#[test]
fn the_elaborated_and_and_or_are_written_as_operators() {
    let and = if_(ge0("x@1"), ge0("y@2"), lit(false));
    assert_eq!(written(&and, before_at), "((x >= 0) && (y >= 0))");
    let or = if_(ge0("x"), lit(true), ge0("y"));
    assert_eq!(written(&or, before_at), "((x >= 0) || (y >= 0))");
    let nested = if_(if_(ge0("a"), ge0("b"), lit(false)), lit(true), ge0("c"));
    assert_eq!(
        written(&nested, before_at),
        "(((a >= 0) && (b >= 0)) || (c >= 0))"
    );
    let other = if_(ge0("x"), lit(1), lit(0));
    assert_eq!(written(&other, before_at), "if (x >= 0) { 1 } else { 0 }");
    assert_eq!(
        pretty(&and, usize::MAX),
        "if (x@1 >= 0) { (y@2 >= 0) } else { false }"
    );
}

/// The text is linear in the term: `k` tests joined by `&&`, nested to the left and to the
/// right, each name renamed.
#[test]
fn written_text_scales_with_the_term() {
    let chain = |k: usize, left: bool| -> Term {
        (1..k).fold(ge0("v@0"), |t, i| {
            let next = ge0(&format!("v@{i}"));
            if left {
                if_(t, next, lit(false))
            } else {
                if_(next, t, lit(false))
            }
        })
    };
    zed_tests::deep::on_small_stack(|| {
        for left in [true, false] {
            let n = 2_000;
            let inputs = [n, zed_tests::scaling::FACTOR * n].map(|k| chain(k, left));
            let what = if left { "left" } else { "right" };
            zed_tests::scaling::check(&format!("written, && nested to the {what}"), n, |k| {
                let t = &inputs[usize::from(k != n)];
                std::hint::black_box(written(t, before_at));
            });
        }
    });
}

/// A type test in a pattern writes its type as a program writes it, the empty type as `Never`
/// (DESIGN.md, the L1 row of "Defined words by layer"), not in the kernel's prefix form.
#[test]
fn a_type_pattern_writes_its_type_in_type_syntax() {
    use zed_kernel::Pattern;
    use zed_kernel::types::Type;
    let small = &Type::int() - &Type::lit(&zed_kernel::Value::Int(0)).expect("an int literal");
    let t = Term::Match(
        zed_tests::kernel::rc(var("v@1")),
        vec![
            (Pattern::Is(Type::empty()), lit("none")),
            (Pattern::Is(small), lit("nonzero")),
            (Pattern::Is(&Type::int() | &Type::bool()), lit("scalar")),
        ],
    );
    let shown = written(&t, before_at);
    assert_eq!(
        shown,
        "match v { (is Never) -> \"none\", (is int \\ 0) -> \"nonzero\", \
         (is bool | int) -> \"scalar\" }"
    );
    assert!(!shown.contains("(|") && !shown.contains("(\\"), "{shown}");
}

/// Item PRINT-group-site-defs: a part a type test writes twice is declared once, on a line of
/// its own before the term, as a user declares it, and the term after it uses the name. The
/// declaration reads as the top level of a file, and with the type tested, `(T1, T1)`, reads
/// back as that type. The term itself is not read back: the kernel writes a type test as
/// `(is T)`, where sec:grammar has `IsPat`, `Name? is T`, and the parser stops at its `)`
/// expecting a `,`.
/// Before, the definition stood inside the pattern: `(is type T1 = int | #x; (T1, T1))`.
#[test]
fn a_part_a_type_test_writes_twice_is_declared_before_the_term() {
    use zed_kernel::Pattern;
    use zed_kernel::types::Type;
    let int_or_x = &Type::int() | &Type::atom("x");
    let pair = Type::tuple(vec![int_or_x.clone(), int_or_x]);
    let t = Term::Match(
        zed_tests::kernel::rc(var("v@1")),
        vec![
            (Pattern::Is(pair.clone()), lit("pair")),
            (Pattern::Wild, lit("other")),
        ],
    );
    let want = "type T1 = int | #x;\nmatch v { (is (T1, T1)) -> \"pair\", _ -> \"other\" }";
    assert_eq!(written(&t, before_at), want);
    assert_eq!(t.to_string(), want.replace("match v ", "match v@1 "));
    let (decl, _) = want.split_once('\n').expect("a declaration first");
    let tokens = zedc::lex::lex_fence(decl).unwrap_or_else(|e| panic!("{decl}: {e:?}"));
    zedc::parse::parse(decl, &tokens, "Unit", zedc::parse::TOP)
        .unwrap_or_else(|e| panic!("{decl}: {e:?}"));
    let back = zedc::check::read::parse_type(&format!("{decl}\n(T1, T1)")).expect("reads back");
    let pair = zedc::check::ty::Ty::set(pair);
    assert!(back.subtype(&pair) && pair.subtype(&back), "{back}");
}
