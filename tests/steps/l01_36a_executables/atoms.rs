//! An atom with an empty payload, `#e()`, built into an executable: the native code builds it
//! apart from the bare atom `#e`, as `zedc run` does (ATOM-empty-payload).

use super::{Ran, built, dir, executable, interpreter};

/// `f(1)` is `#e()` and `f(0)` is `#e`; the program prints which branch of `x is #e` each
/// takes, the two comparisons with `#e`, and the three atoms in a tuple.
const SRC: &str = "\
f(positional n: int) {
  x = if n > 0 { #e() } else { #e };
  return if x is #e { \"bare\" } else { \"not bare\" };
}
main(m: MainArgs) {
  m.stdout <- \"${f(1)} ${f(0)} ${#e() is #e} ${#e() == #e} ${#e() == #e()} ${#e is #e} \
     ${(#e(), #e, #e(1))}\";
}
";

#[test]
fn an_empty_payload_is_built_apart_from_the_bare_atom() {
    // Code that built `#e()` as `#e` would take the "bare" branch for `f(1)`, find the two
    // equal and print `(#e, #e, #e(1))`.
    let d = dir("empty_payload");
    let (src, exe) = (d.join("empty_payload.zed"), d.join("empty_payload"));
    std::fs::write(&src, SRC).unwrap();
    built(&src, &exe);
    let expected = Ran {
        status: 0,
        stdout: "not bare bare false false true true (#e(), #e, #e(1))\n".into(),
        stderr: String::new(),
    };
    assert_eq!(executable(&exe, &[], b""), expected);
    assert_eq!(interpreter(&src, &[], b""), expected);
}
