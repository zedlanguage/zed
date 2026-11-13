//! The formatter writes a `match` with one arm a line, each followed by `,`, an import on one
//! line with its pin, and annotations on their declaration's line, as DESIGN.md writes them;
//! what it writes builds to the same statements and formats to itself.

use super::fmt;

#[track_caller]
fn check(text: &str, want: &str) {
    assert_eq!(fmt(text), want);
}

#[test]
fn arms_go_one_to_a_line() {
    check(
        "size(t)=match t{#leaf->0,Node(l:,r:)->1+size(l)+size(r)};\n\
         sign(n)=match n{0->0,k where k>0->1,_->-1,};\n",
        "size(t) = match t {\n  #leaf -> 0,\n  Node(l:, r:) -> 1 + size(l) + size(r),\n};\n\
         sign(n) = match n {\n  0 -> 0,\n  k where k > 0 -> 1,\n  _ -> -1,\n};\n",
    );
}

#[test]
fn nested_patterns_blocks_and_matches_are_indented() {
    check(
        "f(r){d=match r{#ok(Pair(a:(x,_),b:n is int|f64))->{y=x;y*2},is Point->1,\
         \"s\"->-2.5,-1->(match n{_->0})};d}\n",
        "f(r) {\n  d = match r {\n    #ok(Pair(a: (x, _), b: n is int | f64)) -> {\n      y = x;\n      y * 2\n    },\n    \
         is Point -> 1,\n    \"s\" -> -2.5,\n    -1 -> match n {\n      _ -> 0,\n    },\n  };\n  d\n}\n",
    );
}

#[test]
fn a_match_as_an_operand() {
    check(
        "k=1+match x{_->2}*3;\nn=match(if c{a}else{b}){_->0};\n\
         g=r else #ok(v:n is int)->n;\nh=x->match x{_->({a:1}),_->({a:1}).a};\n",
        "k = 1 + match x {\n  _ -> 2,\n} * 3;\nn = match if c { a } else { b } {\n  _ -> 0,\n};\n\
         g = r else #ok(v: n is int) -> n;\nh = x -> match x {\n  _ -> ({ a: 1 }),\n  _ -> ({ a: 1 }.a),\n};\n",
    );
}

#[test]
fn imports_and_annotations() {
    check(
        "import geometry.shapes;\nimport geometry.shapes as gs @hash(\
         \"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef\",);\n\
         import a.{b,c,} ;\n@memoized fib(n)=n;\n@cost(O(n*log(n)),space:n) @noalloc\nsort(xs)=xs;\n\
         @log() f(x){@measure(x) g(y)=y;g(x)}\n",
        "import geometry.shapes;\nimport geometry.shapes as gs @hash(\
         \"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef\");\n\
         import a.{b, c};\n@memoized fib(n) = n;\n@cost(O(n * log(n)), space: n) @noalloc sort(xs) = xs;\n\
         @log() f(x) {\n  @measure(x) g(y) = y;\n  g(x)\n}\n",
    );
}
