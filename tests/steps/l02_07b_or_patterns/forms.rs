//! Each pattern of DESIGN.md step L2.7b builds and formats: or-patterns of any patterns, nested
//! and in groups, ranges and `is`-patterns in their parentheses, and an atom's sole payload
//! sharing the atom's parentheses. The formatter writes each in one pair of parentheses.

use super::{fmt, sx};

/// Checks that each `(text, tree)` builds to `tree`.
#[track_caller]
fn trees(cases: &[(&str, &str)]) {
    zed_tests::tables::check(cases, sx);
}

#[test]
fn an_or_pattern_builds_with_its_alternatives_in_order() {
    trees(&[
        (
            "f(c) = match c { (#red | #green) -> 1, #blue -> 2 };",
            "(def f (c) = (match c (-> (| #red #green) 1) (-> #blue 2)))",
        ),
        (
            "f(v) = match v { (\"a\" | \"b\" | -1 | true) -> 1, _ -> 0 };",
            "(def f (v) = (match v (-> (| (str \"a\") (str \"b\") (- 1) true) 1) (-> _ 0)))",
        ),
        // Nested, each group its own node: no flattening.
        (
            "f(v) = match v { ((#a | (#b | #c)) | #d) -> 1, _ -> 0 };",
            "(def f (v) = (match v (-> (| (| #a (| #b #c)) #d) 1) (-> _ 0)))",
        ),
        (
            "f(v) = match v { ((n is int) | (n is f64)) -> n, _ -> 0 };",
            "(def f (v) = (match v (-> (| (is n int) (is n f64)) n) (-> _ 0)))",
        ),
        (
            "f(t) = match t { ((#a | #b), x) -> x };",
            "(def f (t) = (match t (-> ((| #a #b), x) x)))",
        ),
        (
            "f(v) = match v { Box(v: (#a | #b)) -> 2, _ -> 0 };",
            "(def f (v) = (match v (-> Box(v: (| #a #b)) 2) (-> _ 0)))",
        ),
    ]);
}

#[test]
fn ranges_and_is_patterns_build_in_their_parentheses() {
    trees(&[
        (
            "f(v) = match v { (0..=9) -> #digit, (10..<20) -> #teen, (-5..) -> #big, _ -> #other };",
            "(def f (v) = (match v (-> (..= 0 9) #digit) (-> (..< 10 20) #teen) (-> (.. (- 5)) #big) (-> _ #other)))",
        ),
        (
            "f(v) = match v { (n is int) where n > 0 -> n, (is String | bool) -> 0, _ -> 0 };",
            "(def f (v) = (match v (-> (is n int) (where (> n 0)) n) (-> (is (| String bool)) 0) (-> _ 0)))",
        ),
        // The union is the type's: `n is int | #none` tests one type.
        (
            "f(v) = match v { (n is int | #none) -> 0, _ -> 1 };",
            "(def f (v) = (match v (-> (is n (| int #none)) 0) (-> _ 1)))",
        ),
    ]);
}

#[test]
fn an_atoms_sole_payload_shares_its_parentheses() {
    trees(&[
        (
            "f(v) = match v { #p(0..=9) -> 1, #q(#a | #b) -> 2, #r(n is int) -> n, #s() -> 3, _ -> 0 };",
            "(def f (v) = (match v (-> #p((..= 0 9)) 1) (-> #q((| #a #b)) 2) (-> #r((is n int)) n) (-> #s() 3) (-> _ 0)))",
        ),
        // With a second payload, each stands in its own.
        (
            "f(v) = match v { #p((0..=9), y) -> 1, _ -> 0 };",
            "(def f (v) = (match v (-> #p((..= 0 9), y) 1) (-> _ 0)))",
        ),
        // An `else` tail takes an atom pattern, so an or-pattern stands as its payload.
        (
            "f(r) = r else #p(#ok(x) | #err(x)) -> x;",
            "(def f (r) = (else r #p((| #ok(x) #err(x))) x))",
        ),
    ]);
}

#[test]
fn each_form_formats_in_one_pair_of_parentheses() {
    let cases = [
        (
            "f(c)=match c{(#red|#green)->1,#blue->2};\n",
            "f(c) = match c {\n  (#red | #green) -> 1,\n  #blue -> 2,\n};\n",
        ),
        (
            "f(v)=match v{(0..=9)->#digit,(10..<20)->#teen,(-5..)->#big,_->#other};\n",
            "f(v) = match v {\n  (0..=9) -> #digit,\n  (10..<20) -> #teen,\n  (-5..) -> #big,\n  _ -> #other,\n};\n",
        ),
        (
            "f(v)=match v{(n is int)where n>0->n,(is String|bool)->0,_->0};\n",
            "f(v) = match v {\n  (n is int) where n > 0 -> n,\n  (is String | bool) -> 0,\n  _ -> 0,\n};\n",
        ),
        (
            "f(v)=match v{#p(0..=9)->1,#q(#a|#b)->2,#r(n is int)->n,#s()->3,_->0};\n",
            "f(v) = match v {\n  #p(0..=9) -> 1,\n  #q(#a | #b) -> 2,\n  #r(n is int) -> n,\n  #s() -> 3,\n  _ -> 0,\n};\n",
        ),
        (
            "f(v)=match v{#p((0..=9),y)->1,Box(v:(#a|#b))->2,_->0};\n",
            "f(v) = match v {\n  #p((0..=9), y) -> 1,\n  Box(v: (#a | #b)) -> 2,\n  _ -> 0,\n};\n",
        ),
        (
            "f(v)=match v{((n is int)|(n is f64))->n,((#a|(#b|#c))|#d)->1,_->0};\n",
            "f(v) = match v {\n  ((n is int) | (n is f64)) -> n,\n  ((#a | (#b | #c)) | #d) -> 1,\n  _ -> 0,\n};\n",
        ),
        (
            "f(t)=match t{((#a|#b),x)->x};\n",
            "f(t) = match t {\n  ((#a | #b), x) -> x,\n};\n",
        ),
        (
            "f(r)=r else #p(#ok(x)|#err(x))->x;\n",
            "f(r) = r else #p(#ok(x) | #err(x)) -> x;\n",
        ),
    ];
    for (text, want) in cases {
        assert_eq!(fmt(text), want, "{text}");
    }
}
