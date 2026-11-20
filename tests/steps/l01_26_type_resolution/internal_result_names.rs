//! The internal results of a compact forward are named from `T`, `U`, `V`, `W`, `T5`, …, as a
//! program's own type variables may be. These tests check that no spelling a program writes,
//! and no class of a function around a lambda, is ever taken for one of them (proof at
//! `Sig::vars_marks`, zedc-types `ty.rs`, sub-cases (a) and (b); row
//! PROOF-flat-vars-instantiated-clash). The forwards `h1` and `h2` keep have internal results
//! spelled `W` and `T5` (read from their decoded signatures when the row's probes ran).

use super::{info, sig, type_errors};

const CHAINS: &str = "h0(positional f, positional m) = m.map(f);\n\
                      h1(positional f, positional m) = h0(f, m).map(f);\n\
                      h2(positional f, positional m) = h1(f, m).map(f);\n\
                      id(positional x) = x;\n";

/// `s` with each whole identifier `n` written `#N#`, so that two texts that differ only in the
/// spelling of the caller's variable compare equal.
fn word(s: &str, n: &str) -> String {
    let b = s.as_bytes();
    let id = |c: u8| c.is_ascii_alphanumeric() || c == b'_' || c == b'\'';
    let mut out = String::new();
    let mut i = 0;
    while i < s.len() {
        if s[i..].starts_with(n)
            && (i == 0 || !id(b[i - 1]))
            && (i + n.len() == s.len() || !id(b[i + n.len()]))
        {
            out.push_str("#N#");
            i += n.len();
        } else {
            let c = s[i..].chars().next().expect("a char");
            out.push(c);
            i += c.len_utf8();
        }
    }
    out
}

/// Sub-case (a): a caller's written type variable `N`, spelled as one of the callee's internal
/// results (`W`, `T5`) or as any other made-up name, gives the signature and the errors it gives
/// spelled `T20`, which no internal result here takes. Before the proof, a caller type holding
/// an internal result's spelling at `Ck::instantiated` would have made the decode merge the two.
/// `T` is left out: a written `T` prints as itself where `T20` prints renamed to `T`, a
/// difference of printing only, measured on these templates.
#[test]
fn caller_names_spelled_as_internal_results_change_nothing() {
    let callers = [
        "k(positional y: N, positional z: N) = (h2(id, [y]), z);",
        "k(positional y: N, positional z: N) = (h1(x -> [x], [y]), z);",
        "k(positional y: N, positional g: (N) -> N) = h2(g, [y]);",
        "k(positional y: N, positional g: (N) -> (N, int)) = h1(g, [y]);",
        "k(positional y: N, positional z: N) = (h2(x -> y, [1]), z);",
        "k(positional y) = if y is N { h2(id, [y]) } else { [] };",
        "k(positional y) = if y is [N] { h1(x -> [x], y) } else { [] };",
        "k(positional y: int, positional g: (N) -> [N] for N in int | f64) = h1(g, [y]);",
    ];
    for c in callers {
        let run = |n: &str| {
            let p = format!("{CHAINS}{}\n", c.replace('N', n));
            let errs: Vec<String> = type_errors(&p).iter().map(|e| word(e, n)).collect();
            (word(&sig(&p, "k"), n), errs)
        };
        let base = run("T20");
        for n in ["U", "V", "W", "T5", "T6"] {
            assert_eq!(run(n), base, "{c} with N = {n}");
        }
    }
}

/// Sub-case (b): a lambda that holds a class of the function around it keeps no compact
/// forward (`generalize` expands it), so the names that function's classes get never meet a
/// decoded internal result. `d`'s class and the lambda's `x` print apart in the signature, and
/// in the top values that `Ck::shown` prints after `g` ended.
#[test]
fn lambda_holding_a_class_keeps_no_forward_and_prints_apart() {
    let cases = [
        (
            "g(positional d) = x -> h1(z -> [(z, d)], [x]);\na = g(1);",
            "T -> U -> 0 -> 0 -> (0 -> (U, T), T)",
            "T -> 0 -> 0 -> (0 -> (T, 1), 1)",
        ),
        (
            "g(positional d) = (x -> h1(z -> [(z, d)], [x]), d + 1);\na = g(1);",
            "U -> (T -> 0 -> 0 -> (0 -> (T, U), U), U) for U in int | f32 | f64 | rat",
            "(T -> 0 -> 0 -> (0 -> (T, int), int), int)",
        ),
        (
            "g(positional d) = (x -> h2(z -> [(z, d)], [x]), d + 1);\na = g(1);",
            "U -> (T -> 0 -> 0 -> (0 -> (0 -> (T, U), U), U), U) for U in int | f32 | f64 | rat",
            "(T -> 0 -> 0 -> (0 -> (0 -> (T, int), int), int), int)",
        ),
    ];
    for (g, want_sig, want_top) in cases {
        let p = format!("{CHAINS}{g}\n");
        assert_eq!(sig(&p, "g"), want_sig, "{g}");
        let (i, _) = info(&p);
        assert!(
            i.errors.is_empty(),
            "{g}: {:?}",
            i.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
        );
        let top = (i.tops.iter())
            .find(|(k, _)| *k == "a")
            .map(|(_, t)| t.to_string());
        assert_eq!(top.as_deref(), Some(want_top), "{g}");
    }
}
