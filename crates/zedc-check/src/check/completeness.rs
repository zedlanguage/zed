//! The cases of the pieces the unit tests of `check` exercise that those tests leave out
//! (row TEST-complete-crates): the limits of `main` (DESIGN.md sec:ports, "`main` may limit
//! its own run"), the steps that explain a type with no value, a family atom passed to a call
//! (step L1.27), `ungrouped` and `Label`.

use std::time::Duration;

use super::*;

fn checker<'t, 'a>(t: &'t Tables<'a>) -> Ck<'t, 'a> {
    Ck::new(t, |_, _, _| {})
}

fn span(start: usize) -> Span {
    Span {
        start,
        end: start + 1,
    }
}

/// The messages of the errors `ck` holds, with their notes.
fn messages(ck: Ck<'_, '_>, text: Option<&str>) -> Vec<(String, Vec<String>)> {
    (ck.errors.into_iter())
        .map(|f| {
            let mut e = f.written(text);
            lay_out(&mut e.message, &mut e.notes, &mut e.menu);
            (e.message, e.notes.into_iter().map(|n| n.text).collect())
        })
        .collect()
}

fn rat(n: i128, d: i128) -> Value {
    Value::Rat(Arc::new(
        Rat::new(n.into(), d.into()).expect("a nonzero denominator"),
    ))
}

/// `bytes_limit` of `value` with the target `target`: the bytes, or the one message.
fn bytes(target: Option<&str>, value: Option<Value>) -> Result<u128, String> {
    let res = zedc_resolve::resolve::resolve(&[]).expect("the empty unit resolves");
    let mut t = Tables::new(&[], &res);
    t.target = target;
    let mut ck = checker(&t);
    let got = ck.bytes_limit(span(0), "n", value);
    let ms = messages(ck, None);
    match got {
        Some(b) => {
            assert!(ms.is_empty(), "{ms:?}");
            Ok(b)
        }
        None => {
            assert_eq!(ms.len(), 1, "{ms:?}");
            Err(ms[0].0.clone())
        }
    }
}

/// `duration_limit` of `value` after `cpu: `: the duration, or the one message.
fn duration(value: Option<Value>) -> Result<Duration, String> {
    let res = zedc_resolve::resolve::resolve(&[]).expect("the empty unit resolves");
    let t = Tables::new(&[], &res);
    let mut ck = checker(&t);
    let got = ck.duration_limit(span(0), "d", "cpu: ", value);
    let ms = messages(ck, None);
    match got {
        Some(d) => {
            assert!(ms.is_empty(), "{ms:?}");
            Ok(d)
        }
        None => {
            assert_eq!(ms.len(), 1, "{ms:?}");
            Err(ms[0].0.clone())
        }
    }
}

#[test]
fn a_memory_limit_is_a_positive_int_of_bytes_within_the_address_space() {
    assert_eq!(bytes(None, Some(Value::Int(1))), Ok(1));
    assert_eq!(
        bytes(None, Some(Value::Int(i64::MAX))),
        Ok(i64::MAX as u128)
    );
    let none = "`memory: n` leaves the run no memory: the memory limit of `main` is a number of \
                bytes above 0, as `memory: 1048576` for 1 MiB.";
    assert_eq!(bytes(None, Some(Value::Int(0))), Err(none.into()));
    assert_eq!(bytes(None, Some(Value::Int(-1))), Err(none.into()));
    // Past `i64::MAX` and up to the address space, 2^64 bytes, the limit is kept exactly
    // (FAIL-check-memory-limit-2-63).
    for b in [1u128 << 63, (1 << 64) - 1, 1 << 64] {
        let v = Value::int(i128::try_from(b).expect("below 2^127").into());
        assert!(matches!(v, Value::Big(_)));
        assert_eq!(bytes(None, Some(v)), Ok(b));
    }
    // Past the address space, it is named, system first, and the largest limit with it.
    let big = Value::int(((1i128 << 64) + 1).into());
    assert!(matches!(big, Value::Big(_)));
    assert_eq!(
        bytes(Some("x86_64-linux"), Some(big.clone())),
        Err("`memory: n` is more memory than Linux x86_64 addresses: write at most `2^64`.".into())
    );
    assert_eq!(
        bytes(None, Some(big)),
        Err(
            "`memory: n` is more memory than a 64-bit target addresses: write at most `2^64`."
                .into()
        )
    );
    // A negative big integer, a rat, a string: no number of bytes.
    let not = "`memory: n` is not a number of bytes: the memory limit of `main` is an `int` above \
               0, as `memory: 1048576` for 1 MiB.";
    assert_eq!(
        bytes(None, Some(Value::int((-1i128 << 64).into()))),
        Err(not.into())
    );
    assert_eq!(bytes(None, Some(rat(1, 2))), Err(not.into()));
    assert_eq!(bytes(None, Some(Value::str("1"))), Err(not.into()));
    assert_eq!(
        bytes(None, None),
        Err(
            "`memory: n` is not a constant: the memory limit of `main` is fixed when the program \
             is built. Write the number of bytes, as `memory: 1048576`."
                .into()
        )
    );
}

#[test]
fn a_duration_is_a_positive_int_or_rat_of_seconds_below_2_to_the_64_nanoseconds() {
    assert_eq!(duration(Some(Value::Int(3))), Ok(Duration::from_secs(3)));
    assert_eq!(duration(Some(rat(1, 2))), Ok(Duration::from_millis(500)));
    // Rounded up to a whole nanosecond, so a limit is never shorter than written.
    assert_eq!(
        duration(Some(rat(1, 3_000_000_000))),
        Ok(Duration::from_nanos(1))
    );
    // `u64::MAX` nanoseconds is the longest; one nanosecond more is too long.
    let most = i128::from(u64::MAX);
    assert_eq!(
        duration(Some(rat(most, 1_000_000_000))),
        Ok(Duration::from_nanos(u64::MAX))
    );
    let long = "`cpu: d` is not a time the run can have: a limit of `main` is a number of seconds \
                above 0 and below 2^64 nanoseconds, as `cpu: 60r`.";
    assert_eq!(
        duration(Some(rat(most + 1, 1_000_000_000))),
        Err(long.into())
    );
    assert_eq!(
        duration(Some(Value::int((1i128 << 64).into()))),
        Err(long.into())
    );
    assert_eq!(duration(Some(Value::Int(0))), Err(long.into()));
    assert_eq!(duration(Some(Value::Int(-5))), Err(long.into()));
    assert_eq!(duration(Some(rat(-1, 2))), Err(long.into()));
    assert_eq!(duration(Some(rat(0, 1))), Err(long.into()));
    assert_eq!(
        duration(Some(Value::str("1"))),
        Err(
            "`cpu: d` is not a number of seconds: write an `int` or a `rat` above 0, as `cpu: 2r` \
             for 2 s or `cpu: 1r/2r` for half a second."
                .into()
        )
    );
    assert_eq!(
        duration(None),
        Err(
            "`cpu: d` is not a constant: a limit of `main` is fixed when the program is built. \
             Write the number of seconds, as `cpu: 60r`."
                .into()
        )
    );
}

#[test]
fn a_target_of_another_form_is_kept_or_split_at_its_first_dash() {
    assert_eq!(limits::target_text("x86_64-"), " x86_64");
    assert_eq!(limits::target_text("arm-none-eabi"), "none-eabi arm");
    assert_eq!(limits::target_text(""), "");
}

/// The steps `explain_empty` gives for the written type `text`, the parts written as `found`
/// taken to have no value; each with the text it is placed at.
fn why_found(text: &str, found: &[&str]) -> Vec<(String, String)> {
    let tokens = zedc_syntax::lex::lex(text).expect("lexing a type");
    let tree = zedc_syntax::parse::parse(text, &tokens, "Type", zedc_syntax::parse::TOP)
        .expect("parsing a type");
    let t = zedc_syntax::ast::ty(text, &tokens, &tree).expect("reading a type");
    let mut out = Vec::new();
    explain_empty(
        &t,
        |p| found.contains(&&text[p.span.start..p.span.end]),
        &mut out,
    );
    (out.into_iter())
        .map(|n| (text[n.span.start..n.span.end].to_string(), n.text))
        .collect()
}

fn step(at: &str, text: &str) -> (String, String) {
    (at.to_string(), format!("{text}, so it is `Never`"))
}

#[test]
fn each_kind_of_cause_is_named_by_its_kind_in_the_step_after_it() {
    let tuple = |cause: &str| {
        format!("this tuple type has no value, since its component 0, {cause}, has none")
    };
    assert_eq!(
        why_found(
            "(#a(Never), int)",
            &["(#a(Never), int)", "#a(Never)", "Never"]
        ),
        [
            step(
                "#a(Never)",
                "this atom type `#a` has no value, since its payload's component 0, `Never`, has \
                 none"
            ),
            step(
                "(#a(Never), int)",
                &tuple("the atom type of the step before")
            ),
        ]
    );
    assert_eq!(
        why_found("(int | bool, int)", &["(int | bool, int)", "int | bool"]),
        [
            step(
                "int | bool",
                "this union has no value, since none of its members has one"
            ),
            step("(int | bool, int)", &tuple("the union of the step before")),
        ]
    );
    assert_eq!(
        why_found("(int \\ int, int)", &["(int \\ int, int)", "int \\ int"]),
        [
            step(
                "int \\ int",
                "this difference has no value, since each value of `int` is also in `int`"
            ),
            step(
                "(int \\ int, int)",
                &tuple("the difference of the step before")
            ),
        ]
    );
}

#[test]
fn an_intersection_or_a_difference_with_an_empty_operand_names_it() {
    assert_eq!(
        why_found(
            "(int, Never) & (int, int)",
            &["(int, Never) & (int, int)", "(int, Never)", "Never"]
        ),
        [
            step(
                "(int, Never)",
                "this tuple type has no value, since its component 1, `Never`, has none"
            ),
            step(
                "(int, Never) & (int, int)",
                "this intersection has no value, since its operand, the tuple type of the step \
                 before, has none"
            ),
        ]
    );
    assert_eq!(
        why_found("Never \\ int", &["Never \\ int", "Never"]),
        [step(
            "Never \\ int",
            "this difference has no value, since its left operand, `Never`, has none"
        )]
    );
}

#[test]
fn parts_with_no_value_are_found_inside_every_kind_of_type() {
    let inner = || {
        step(
            "(int, Never)",
            "this tuple type has no value, since its component 1, `Never`, has none",
        )
    };
    let found = &["(int, Never)", "Never"];
    for text in [
        "(int, (int, Never)) -> int",
        "((int, Never), int) -> int",
        "(x: (int, Never)) -> int",
        "(int) -> (int, Never)",
        "int .. int -> (int, Never)",
        "List((int, Never))",
        "{ a: (int, Never) }",
        "[(int, Never)]",
        "#b(x: (int, Never)) | int",
        "(int, Never) | int",
        "(int, int) & (int, Never)",
        "(int, Never) \\ int",
        "int \\ (int, Never)",
        "(T, (int, Never)) for T in int | f64",
    ] {
        assert_eq!(why_found(text, found), [inner()], "{text}");
    }
    // Parts that hold no parts: nothing to explain.
    for text in ["int", "#a", "#_", "(..)", "{..}", "#a(..)"] {
        assert_eq!(why_found(text, &[]), [], "{text}");
    }
}

#[test]
fn an_atom_found_empty_names_a_positional_part_by_its_position() {
    assert_eq!(
        why_found("#a(int, Never)", &["#a(int, Never)", "Never"]),
        [step(
            "#a(int, Never)",
            "this atom type `#a` has no value, since its payload's component 1, `Never`, has none"
        )]
    );
}

/// The errors `passing` gives for `t` in a call, the value's code `code` written at 0.
fn passed(t: &Ty, code: &str) -> (Ty, Vec<(String, Vec<String>)>) {
    let res = zedc_resolve::resolve::resolve(&[]).expect("the empty unit resolves");
    let mut tables = Tables::new(&[], &res);
    tables.text = Some(code);
    let mut ck = checker(&tables);
    let of = Span {
        start: 0,
        end: code.len(),
    };
    let left = ck.passing(t, "a call", span(0), Some(of));
    (left, messages(ck, Some(code)))
}

fn atoms(names: &[&str]) -> Ty {
    (names.iter()).fold(Ty::empty(), |t, n| t.union(&Ty::set(KType::atom(n))))
}

const DATA: &str =
    "an atom of a named family is data, not a failure, so it does not pass through a call";

#[test]
fn a_family_of_one_atom_and_nothing_else_gets_one_d_and_no_rest_arm() {
    let (left, ms) = passed(&atoms(&["red"]).named(), "c");
    assert_eq!(left, Ty::empty());
    assert_eq!(
        ms,
        [(
            "No case for `#red` in a call: `c : #red`. Try `(c else #red -> d)` instead."
                .to_string(),
            vec![
                DATA.to_string(),
                "`d` is the value to use in place of the atom".to_string(),
                "repair: `(c else #red -> d)`".to_string(),
                "repair: `match c { #red -> d }`".to_string(),
            ]
        )]
    );
}

#[test]
fn a_family_of_every_atom_but_some_gets_a_match_in_words() {
    let t = Ty::set(&ty::atoms() - &KType::atom("ok")).named();
    let (left, ms) = passed(&t, "c");
    assert_eq!(left, Ty::empty());
    assert_eq!(ms.len(), 1);
    let (message, notes) = &ms[0];
    assert!(message.starts_with("No case for `"), "{message}");
    assert!(!message.contains("Try"), "{message}");
    assert_eq!(notes.len(), 2, "{notes:?}");
    assert_eq!(notes[0], DATA);
    assert!(
        notes[1].starts_with("repair: a `match` on `c` with one arm for each atom of `"),
        "{notes:?}"
    );
}

#[test]
fn code_on_more_than_one_line_or_blank_is_not_quoted_in_the_repair() {
    for code in ["a\n+ b", "   "] {
        let (_, ms) = passed(&atoms(&["red"]).named(), code);
        assert_eq!(
            ms,
            [(
                "No case for `#red` in a call: a value of `#red`.".to_string(),
                vec![
                    DATA.to_string(),
                    "repair: handle each atom of `#red` with `else` or `match` before the value \
                     reaches a call"
                        .to_string(),
                ]
            )],
            "{code:?}"
        );
    }
}

#[test]
fn a_type_with_no_family_passes_on_its_loose_atoms_and_rejects_nothing() {
    let t = atoms(&["ioError"])
        .written()
        .union(&Ty::carrier(Carrier::Int));
    let (left, ms) = passed(&t, "c");
    assert_eq!(left, atoms(&["ioError"]).written());
    assert!(ms.is_empty());
    let (left, ms) = passed(&Ty::carrier(Carrier::Int), "c");
    assert_eq!(left, Ty::empty());
    assert!(ms.is_empty());
}

#[test]
fn code_that_does_not_lex_keeps_its_parentheses() {
    // An unclosed string: the code is not read, so nothing is taken off.
    for code in ["(\"a)", "(\"a"] {
        assert_eq!(&code[ungrouped(code)], code);
    }
    assert_eq!(&""[ungrouped("")], "");
}

#[test]
fn only_an_operator_label_is_an_operator() {
    let o = Operator::Binary(BinaryOp::Add);
    assert_eq!(Label::Operator(o).operator(), Some(o));
    assert_eq!(Label::Text("f").operator(), None);
    assert_eq!(Label::Text("f").to_string(), "f");
}

#[test]
fn a_list_in_a_sentence_joins_its_last_item_with_or_or_and() {
    let list = |items: &[&str]| items.iter().map(|s| s.to_string()).collect::<Vec<_>>();
    for (items, or, and) in [
        (list(&[]), "", ""),
        (list(&["a"]), "a", "a"),
        (list(&["a", "b"]), "a or b", "a and b"),
        (list(&["a", "b", "c"]), "a, b or c", "a, b and c"),
    ] {
        assert_eq!(super::or_list(&items), or);
        assert_eq!(super::and_list(&items), and);
    }
}
