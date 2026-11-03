//! The formatter writes each L2 form in one layout, parenthesizes what the grammar needs, and
//! what it writes builds to the same statements and formats to itself.

use super::fmt;

#[track_caller]
fn check(text: &str, want: &str) {
    assert_eq!(fmt(text), want);
}

#[test]
fn a_geometry_module_round_trips() {
    let text = "struct Point{x:f64,y:f64=0.0,}\nstruct Point3 {import Point,import geo.Datum,z:f64}\n\
                type Shape=#circle(c:Point,r:f64)|#poly(pts:Points);\n\
                type Tree(T)=#leaf|#node(left:Tree(T),value:T,right:Tree(T));\n\
                Point.norm=(x*x+y*y).sqrt;\nPoint.scale(k)=Point(x:x*k,y:y*k);\n\
                Number.eval=int(this) else 0;\n\
                origin={x:0.0,y:0.0};\nstats(xs){lo=xs.min;hi=xs.max;return {lo:lo,hi:hi};}\n\
                moved=p with{x=3.0,c.y=p.c.y+1};\n";
    check(
        text,
        "struct Point { x: f64, y: f64 = 0.0 }\nstruct Point3 { import Point, import geo.Datum, z: f64 }\n\
         type Shape = #circle(c: Point, r: f64) | #poly(pts: Points);\n\
         type Tree(T) = #leaf | #node(left: Tree(T), value: T, right: Tree(T));\n\
         Point.norm = (x * x + y * y).sqrt;\nPoint.scale(k) = Point(x: x * k, y: y * k);\n\
         Number.eval = int(this) else 0;\n\
         origin = { x: 0.0, y: 0.0 };\nstats(xs) {\n  lo = xs.min;\n  hi = xs.max;\n  { lo:, hi: }\n}\n\
         moved = p with { x = 3.0, c.y = p.c.y + 1 };\n",
    );
}

#[test]
fn a_display_in_body_position_keeps_its_parentheses() {
    check(
        "swap = p -> ({x:p.y,y:p.x});\n",
        "swap = p -> ({ x: p.y, y: p.x });\n",
    );
    check("d = r else ({x:0});\n", "d = r else ({ x: 0 });\n");
    check("d = r else ({x:0}).x;\n", "d = r else ({ x: 0 }.x);\n");
    check(
        "f = p -> ({x:1} with {x=2});\n",
        "f = p -> ({ x: 1 } with { x = 2 });\n",
    );
    // A lambda inside a display is parenthesized.
    check("h = {f:(x -> x)};\n", "h = { f: (x -> x) };\n");
}

#[test]
fn with_is_parenthesized_by_its_level() {
    check("n = p with {x=3}.norm;\n", "n = (p with { x = 3 }).norm;\n");
    check("s = (a + b) with {x=1};\n", "s = a + b with { x = 1 };\n");
    check("t = (a < b) with {x=1};\n", "t = (a < b) with { x = 1 };\n");
    check("u = -(p with {x=1});\n", "u = -(p with { x = 1 });\n");
    check(
        "v = (p with {x=1}) is Point;\n",
        "v = p with { x = 1 } is Point;\n",
    );
    check(
        "w = p with {x=1} with {y=2};\n",
        "w = p with { x = 1 } with { y = 2 };\n",
    );
    check(
        "z = p with {c=(q with {x=1})};\n",
        "z = p with { c = q with { x = 1 } };\n",
    );
}

#[test]
fn tuple_parameters_and_patterns_are_kept() {
    check(
        "f=((a,b):(int,int))->a;\ng=pairs.map(((k,_))->k);\n",
        "f = ((a, b): (int, int)) -> a;\ng = pairs.map(((k, _)) -> k);\n",
    );
    check(
        "x=r else #hit(Point(x:px,y:),(_,n))->n;\n",
        "x = r else #hit(Point(x: px, y:), (_, n)) -> n;\n",
    );
}

#[test]
fn a_method_body_block_is_on_several_lines() {
    check(
        "Range.clamp(v){low=if v<lo {lo} else {v};if low>hi {hi} else {low}}\n",
        "Range.clamp(v) {\n  low = if v < lo { lo } else { v };\n  if low > hi { hi } else { low }\n}\n",
    );
}
