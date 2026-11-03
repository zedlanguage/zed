//! Struct destructuring, which a payload pattern holds at this step (a `match` arm holds it
//! from step L2.2), and the tuple-destructuring parameter `((a, b)) -> e`.

use super::check;

#[test]
fn a_payload_destructures_a_struct_by_field_name() {
    check(&[
        (
            "x = r else #hit(Point(x: px, y:)) -> 0;",
            "(= (x) (else r #hit(Point(x: px, y:)) 0))",
        ),
        (
            "d = e else #pair(Span(lo:), (_, n)) -> n;",
            "(= (d) (else e #pair(Span(lo:), (_, n)) n))",
        ),
        (
            "t = e else #node(left: Tree(label: l), right: _) -> l;",
            "(= (t) (else e #node(left: Tree(label: l), right: _) l))",
        ),
    ]);
}

#[test]
fn a_tuple_parameter_destructures_its_argument() {
    check(&[
        (
            "byKey = pairs.sortBy(((k, _)) -> k);",
            "(= (byKey) (call (. pairs sortBy) (fn ((k, _)) k)))",
        ),
        (
            "dist = ((a, b): (int, int)) -> b - a;",
            "(= (dist) (fn (((a, b): (tuple int int))) (- b a)))",
        ),
        (
            "f = ((s, c), w) -> s * w + c;",
            "(= (f) (fn ((s, c) w) (+ (* s w) c)))",
        ),
    ]);
}
