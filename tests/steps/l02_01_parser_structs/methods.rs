//! `T.m` methods, with or without a parameter list, in equation or block form, and `this`.

use super::check;

#[test]
fn a_method_is_declared_on_its_receiver_type() {
    check(&[
        (
            "Point.norm = (x * x + y * y).sqrt;",
            "(method Point.norm = (. (+ (* x x) (* y y)) sqrt))",
        ),
        (
            "Point.scale(k) = Point(x: x * k, y: y * k);",
            "(method Point.scale (k) = (call Point (x: (* x k)) (y: (* y k))))",
        ),
        (
            "Point.move(positional dx, positional dy) = Point(x: x + dx, y: y + dy);",
            "(method Point.move ((positional dx) (positional dy)) = \
             (call Point (x: (+ x dx)) (y: (+ y dy))))",
        ),
        (
            "Counter.reset() = Counter(n: 0, hi:);",
            "(method Counter.reset () = (call Counter (n: 0) (hi: hi)))",
        ),
    ]);
}

#[test]
fn a_method_body_may_be_a_block_with_tests() {
    check(&[(
        "Range.clamp(v) {\n  low = if v < lo { lo } else { v };\n  if low > hi { hi } else { low }\n}\n  test { 3 -> 3 }",
        "(method Range.clamp (v) (block (= (low) (if (< v lo) (block (return lo)) (block (return v)))) \
         (return (if (> low hi) (block (return hi)) (block (return low))))) (test (3 3)))",
    )]);
}

#[test]
fn this_is_the_receiver() {
    check(&[
        (
            "Number.eval = int(this) else 0;",
            "(method Number.eval = (else (call int this) 0))",
        ),
        (
            "Point.same(q) = this == q;",
            "(method Point.same (q) = (== this q))",
        ),
    ]);
}
