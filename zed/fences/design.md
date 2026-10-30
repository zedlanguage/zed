<!-- The `zed` fences of the spec's DESIGN.md, copied by sync.py: do not edit. -->

<!-- DESIGN.md:196 layer L8: ring L8, word none, label none, documentation notation -->
```zed
src as (sourceKeypathPattern) into (outputKeypathPattern -> leaf)
```

<!-- DESIGN.md:217 layer L8: ring L8, word none, label none, documentation notation -->
```zed
   as (k1 -> k2 -> v) into (k2 -> k1 -> v)        // transpose levels
   as (k1 -> k2 -> v) into ((k1, k2) -> v)        // flatten to a tuple key
   as (k -> v)        into (k + 1 -> v)           // bijective key transform
```

<!-- DESIGN.md:224 layer L8: ring L8, word none, label none, documentation notation -->
```zed
   as (k1 -> k2 -> v) into (k1 -> (k2, v) -> v)   // key widened with the value: still injective
   as (k -> v)        into ((k, f(k)) -> v)       // key widened with derived data
```

<!-- DESIGN.md:229 layer L8: ring L8, word none, label none, documentation notation -->
```zed
   as (k1 -> k2 -> v) into (k1 -> k2 -> _)        // keep the key structure, discard values:
                                                  //   result type  K1 -> (K2 -> K2)   (set-leaf)
   as (k1 -> k2 -> v) into (k1 -> k2)             // sugar for the same (trailing source-key = truncate)
```

<!-- DESIGN.md:240 layer L8: ring L8, word none, label none, documentation notation -->
```zed
as (k1 -> k2 -> v) into (k1 -> v)                 // ✗ compile error
```

<!-- DESIGN.md:258 layer L8: ring L8, word none, label none, documentation notation -->
```zed
as (k1 -> k2 -> v) into (k1 -> k2 >< (+) -> v)    // collapse the k2 level by explicit reduction
```

<!-- DESIGN.md:268 layer L8: ring L8, word none, label none -->
```zed
byScore = scores into (desc score -> name -> score);   // scores : name -> score; adjoin a rank level ordered by score
```

<!-- DESIGN.md:283 layer L8: ring L8, word L4 (rekey), label none -->
```zed
byLower = words into (w.lower -> i -> w);   // words : i -> w; residue `i` written — injective, one level deeper
// byLower = words.group(w -> w.lower);     // the same program: the word `group` declares the same deeper type, Lower ->? (i -> w)
byId    = users.rekey(u -> u.id);         // flat claim: error unless id-uniqueness is witnessed
```

<!-- DESIGN.md:344 layer L8: ring L8, word none, label none -->
```zed
  matmul(positional a: (r -> c -> f64), positional b: (c -> k -> f64)) =  // one shared inner domain c; the float
    (a, b) into (r -> k -> c >< (+) -> a[r][c] * b[c][k]); //   fold takes c's order — a rank for a
                                                           //   matrix, its key order otherwise
                                                           //   (sec:order, sec:reduction)
```

<!-- DESIGN.md:403 layer L6: ring L6, word none, label none -->
```zed
sim = loop {
  pos' = pos + vel * dt      with pos = p0;    // x' means the frame being built; bare x the previous
  vel' = vel + a(pos) * dt   with vel = v0;
  until pos'.x > bound;
};
```

<!-- DESIGN.md:423 layer L6: ring L6, word none, label none -->
```zed
x[i in 0..<warm]  = coldStart(i);         // piecewise definition: phase 1
x[i in warm..<n]  = anneal(x[i-1]);       // phase 2 — reads across the seam legally
```

<!-- DESIGN.md:462 layer L10: ring L10, word none, label none, documentation notation -->
```zed
(div) : ((int, int \ 0) -> int) & ((int, 0) -> #divByZero)
```

<!-- DESIGN.md:600 layer L10: ring L10, word L1 (String), label none -->
```zed
type Small = (x: int where x * x < 100);                    // nonlinear
type Even  = (n: int where n mod 2 == 0);                   // a residue
type Prime = (p: int[2..] where isPrime(p));                // a predicate no domain models
type Short = (s: String where s.len < 100);                 // a length
area(a: int[1..], b: int[1..] where a * b <= 99) -> int = a * b;   // a relation
```

<!-- DESIGN.md:649 layer L11: ring L10, word L11 (Ast), label none -->
```zed
type Bound = int | Ast | #unbounded;                         // an affine bound is an expression over names in scope
struct Interval   { min: Bound, max: Bound }
struct Congruence { modulus: int[0..], residue: int }        // residue in 0..<modulus when modulus > 0
struct FloatClass { finite: bool, nonNaN: bool, width: #f16 | #f32 | #f64 }   // false: not known
struct Constraints {
  subject:    Ast,                                         // the name that stands for the value in every Ast below
  interval:   Interval | [Interval] | #none,                 // a list for a finite union: sorted, disjoint, not adjacent
  congruence: Congruence | #none,
  values:     [_] | #unknown,                                // the finite set, where one is known
  length:     Interval | #none,                              // strings and lists; ::card for morphisms
  floats:     FloatClass | #none,
  relations:  [Ast],                                         // the linear relations that name x
  written:    [Ast],                                         // the constraints as written
}
```

<!-- DESIGN.md:716 layer L2: ring L2, word none, label none -->
```zed
import geometry.shapes;               // qualified: shapes.area(s: c)
import geometry.shapes as g;          // aliased:   g.area(s: c)
import geometry.shapes.{area, Rect};  // selective: area(s: c), Rect(…)
```

<!-- DESIGN.md:773 layer L20: ring L20, word L1 (String), label none -->
```zed
type Nonzero = String matching grammar { "0"* ("1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9") digit* };
type UnitName = String matching grammar { alpha (alpha | "_")* };
type UnitPower = String matching grammar { "-"? digit+ | "(" "-"? digit+ "/" Nonzero ")" };
type UnitFactor = String matching grammar { UnitName ("^" UnitPower)? };
type UnitProduct = String matching grammar { UnitFactor sep (" " | "*" | "·") };
type UnitText = String matching grammar { (UnitProduct | "1") ("/" (UnitFactor | "(" UnitProduct ")"))? };
// accepted: "m^2 s^-1", "kg m/s^2", "J/(kg K)", "m^(3/2)", "1/s"
// rejected: "m2", "J/kg K", "m^1.5", "m / s", "m^(3/0)"
```

<!-- DESIGN.md:798 layer L14: ring L10, word L14 (quat), label none -->
```zed
matmul(positional v: (c -> T), positional b: (c -> k -> T)) = (v, b) into (k -> c >< (+) -> v[c] * b[c][k]);
matmul(positional a: (r -> c -> T), positional v: (c -> T)) = (a, v) into (r -> c >< (+) -> a[r][c] * v[c]);
dot(positional u: (i -> T), positional v: (i -> T)) = (u, v) into (i >< (+) -> conj(u[i]) * v[i]);
cross(positional u: (int[0..<3] -> T), positional v: (int[0..<3] -> T)) = (quat(0, u) * quat(0, v)).im;
cross(positional u: (int[0..<7] -> T), positional v: (int[0..<7] -> T)) = (oct(0, u) * oct(0, v)).im;
```

<!-- DESIGN.md:810 layer L14: ring L14, word L14 (layout), label none -->
```zed
type Rgb = [f32; 3];                                              // int[0..<3] -> f32
type Batch = [f32; n: _, h: 224, w: 224, c: 3] with layout(n, h, w, c);
scale(positional s: T, positional v: [T; n]) = s * v;            // : [T; n]
```

<!-- DESIGN.md:822 layer L14: ring L10, word L14 (matmul), label none -->
```zed
type State = int[0..<2];
step(positional f: ((i: State with units(["m", "m/s"])) -> (j: State with units(["1/m", "s/m"])) -> f64),
     positional x: ((j: State with units(["m", "m/s"])) -> f64)) = f.matmul(x);
// step(f, x) : (i: State with units(["m", "m/s"])) -> f64
```

<!-- DESIGN.md:864 layer L11: ring L10, word L11 (Constraints), label none -->
```zed
type Shape =
    #scalar(name: String, constraints: Constraints)  // int, rat, f64, bool, …, with its refinement: int[0..<10]
  | #string(syntax: Grammar | #none, constraints: Constraints)   // String, or String matching grammar { … }
  | #atom(name: String, payload: Type | #none)       // #red, or #parseError(pos: int, msg: String)
  | #struct(name: String | #none, fields: [Field], syntax: Grammar | #none)
  | #interface(name: String, fields: [Field])
  | #tuple(items: [Type])
  | #union(name: String | #none, members: [Type])
  | #morphism(key: Type, value: Type, partial: bool) // K -> V, or K ->? V when partial
  | #function(params: [Param], result: Type)
  | #refined(base: Type, predicate: Ast)             // t where p, an opaque refinement (sec:domains)
  | #negation(of: Type)
  | #intersection(parts: [Type]);
struct Field { key: _, name: String, valueType: Type, default: Ast | #none, facets: [Ast] }
struct Param { name: String | #none, kind: #positional | #named, valueType: Type, default: Ast | #none }
```

<!-- DESIGN.md:904 layer L11: ring L10, word L11 (::shape), label none -->
```zed
encode(positional v: T) -> String = match T::shape {
  #struct(fields:) -> "{" ++ (fields.map(f -> quote(f.name) ++ ": " ++ encode(v[f.key])) >< ((a, b) -> a ++ ", " ++ b) else "") ++ "}",
  #string          -> quote(v),
  #atom(name:, payload: #none) -> quote(name),
  _                -> String(v),
};
// For u: User, encode(u) specializes to "{\"id\": " ++ String(u.id) ++ ", \"name\": " ++ quote(u.name) ++ "}":
// the match, the map over the two fields, and the fold all run at build.
```

<!-- DESIGN.md:925 layer L22: ring L3, word L22 (expand), label none -->
```zed
p = ((x: rat) -> (x + 1) ** 2)::source;
e = expand(p);         // the tree of (x: rat) -> x ** 2 + 2 * x + 1
d = derivative(p);     // the tree of (x: rat) -> 2 * x + 2
```

<!-- DESIGN.md:946 layer L15: ring L15, word L5 (sort), label none -->
```zed
law addComm(a: int, b: int) = a + b == b + a;
law sortIdempotent(xs: [int]) = xs.sort(asc x -> x).sort(asc x -> x) == xs.sort(asc x -> x);
law noOverdraft(s: Account, t: Txn where t.amount > 0) = (apply(s, t) else s).balance >= 0;   // `else` strips the loose #rejected: the body is exactly bool
```

<!-- DESIGN.md:978 layer L11: ring L3, word L11 (Ast), label none -->
```zed
type Proof = #eval                                            // discharge by enumeration (rung 1)
           | #domain                                          // by the store's lattices and Presburger layer (rung 2)
           | #rewrite(rule: LawId, at: Path, bindings: Bindings) // one equational step
           | #chain(steps: [Proof], claims: [Ast])            // each step proves its claim
           | #cases(on: Binder, arms: Member -> Proof)        // one arm per union member
           | #induction(on: Binder, base: Proof, step: Proof) // `ih` bound in `step`
           | #use(rule: LawId, args: [Ast])                   // instantiate a proved law
           | #implies(assume: Ast, then: Proof)               // discharge under a hypothesis
           | #reflect(sound: LawId)                           // run a decision procedure proved sound (sec:checking_in_zed)
           | #assume(why: String);                            // rung 9, recorded at the site
```

<!-- DESIGN.md:1045 layer L12: ring L7, word L12 (parity), label none -->
```zed
type Parity = #even | #odd | #either;
parity = Facet(
  kind:     #evidence,
  lattice:  flat([#even, #odd], top: #either),     // a prelude lattice; finite, so each rule's monotonicity is enumerated
  holds:    (p, x: int) -> match p { #even -> x mod 2 == 0, #odd -> x mod 2 == 1, #either -> true },
  transfer: (op, a, b) -> match op {
    #add -> if a == #either || b == #either { #either } else if a == b { #even } else { #odd },
    #mul -> if a == #even || b == #even { #even } else if a == #odd && b == #odd { #odd } else { #either },
    _    -> #either,
  },
);

half(positional x: int with parity(#even)) = x div 2;                     // a demand on the argument's fact
g(n: int with parity(#odd)) = half(n + n);                              // ✓ #add's soundness law splits by cases (rung 5) into Presburger facts (rung 2): Proved, so the demand is met
h(n: int with parity(#odd), m: int with parity(#even)) = half(n * m);   // #mul's law is nonlinear: Bounded(instance) at rung 6, so the demand stays a run-time test; --strict rejects until a proof is written
seven = 7 with parity(#odd);                                            // attaching a fact to a value is an obligation: holds(#odd, 7), rung 1
```

<!-- DESIGN.md:1097 layer L22: ring L22, word none, label none -->
```zed
interface Semigroup(T) {
  mul: (T, T) -> T,
  law mulAssoc(a: T, b: T, c: T) = mul(mul(a, b), c) == mul(a, mul(b, c)),
}

interface Monoid(T) {
  import Semigroup(T),
  one: T,
  law oneMul(a: T) = mul(one, a) == a,
  law mulOne(a: T) = mul(a, one) == a,
}

interface CommRing(T) {
  import Monoid(T),
  add: (T, T) -> T,
  zero: T,
  neg: (T) -> T,
  law mulComm(a: T, b: T) = mul(a, b) == mul(b, a),
  law addAssoc(a: T, b: T, c: T) = add(add(a, b), c) == add(a, add(b, c)),
  law addComm(a: T, b: T) = add(a, b) == add(b, a),
  law addZero(a: T) = add(a, zero) == a,
  law addNeg(a: T) = add(a, neg(a)) == zero,
  law distrib(a: T, b: T, c: T) = mul(a, add(b, c)) == add(mul(a, b), mul(a, c)),
}

intRing: CommRing(int) = { mul: (*), one: 1, add: (+), zero: 0, neg: (a -> -a) };
```

<!-- DESIGN.md:1134 layer L22: ring L22, word L22 (CommRing), label none -->
```zed
law square(R: CommRing(T), a: T, b: T) = (a + b) * (a + b) == a * a + 2 * a * b + b * b
proof {
  (a + b) * (a + b)
    == (a + b) * a + (a + b) * b
    == a * a + b * a + (a * b + b * b)
    == a * a + 2 * a * b + b * b
}
```

<!-- DESIGN.md:1148 layer L22: ring L15, word L22 (Monoid), label none -->
```zed
pow(M: Monoid(T), x: T, n: int[0..]) -> T = if n == 0 { 1 } else { pow(M:, x:, n: n - 1) * x };

law powAdd(M: Monoid(T), x: T, m: int[0..], n: int[0..]) =
  pow(M:, x:, n: m + n) == pow(M:, x:, n: m) * pow(M:, x:, n: n)
proof { byInduction(n) }                        // base by mulOne; step by ih and mulAssoc at rung 3
```

<!-- DESIGN.md:1158 layer L22: ring L10, word L22 (Monoid), label none -->
```zed
additive(R: CommRing(T)) -> Monoid(T) = { mul: R.add, one: R.zero };   // mulAssoc is R.addAssoc; mulOne is R.addZero; oneMul by addComm
```

<!-- DESIGN.md:1197 layer L22: ring L22, word none, label none -->
```zed
interface MonoInt {
  f: (int) -> int,
  law mono(a: int, b: int) = (a <= b).implies(f(a) <= f(b)),
}

law monoTwice(M: MonoInt, a: int, b: int) = (a <= b).implies(M.f(M.f(a)) <= M.f(M.f(b))) proof {
  #implies(assume: a <= b, then: #chain(steps: [
    #use(rule: M.mono, args: [a, b]),
    #use(rule: M.mono, args: [M.f(a), M.f(b)]),
  ], claims: [M.f(a) <= M.f(b), M.f(M.f(a)) <= M.f(M.f(b))]))
}
```

<!-- DESIGN.md:1443 layer L7: ring L7, word L7 (terminated), label none -->
```zed
@foreign struct SockAddr { family: int with bits(16), data: [byte] with length(14) }
@foreign struct AddrInfo {
  flags: i32, family: i32, socktype: i32, protocol: i32,
  addrlen: int with bits(32),
  addr: Ptr(SockAddr) | #none,
  canonname: Ptr([byte] with terminated(0)) | #none,
  next: Ptr(AddrInfo) | #none,
}
@foreign("c", "freeaddrinfo") freeAddrInfo: (res: Ptr(AddrInfo)) -> #ok;
@foreign("c", "getaddrinfo") getAddrInfo: (node: [byte] with terminated(0), service: [byte] with terminated(0), hints: Ptr(AddrInfo) | #none) -> {rc: i32, res: Ptr(AddrInfo) | #none with release(freeAddrInfo)};
```

<!-- DESIGN.md:2430 layer L10: ring L10, word L1 (String), label none -->
```zed
// bindings — immutable, inferred; domains where they carry intent
x = 42;
port: int[1..=65535] = 8080;
name = "Zed";
color = #green;                         // atom; family inferred from use

// functions: equation form (terminated), block form (ended by its brace), defaults,
//   positional parameters, named arguments, currying, UFCS
//   (uniform function call syntax: x.f(a) passes x as f's first parameter — the . row of sec:lexical)
double(positional x) = x * 2;
clamp(positional v, positional lo, positional hi) -> int {
  if v < lo { lo } else if v > hi { hi } else { v }   // the export: no `;`
}
greet(positional name: String, punct = "!") = "Hi, " ++ name ++ punct;
y = 5.double.clamp(0, 8);               // ≡ clamp(double(5), 0, 8);  y == 8
ann = greet("Ann", punct: "?");         // positional arguments first, then named
hiAnn = greet("Ann", ...);              // currying leaves out named parameters: called hiAnn(punct: "?") or hiAnn()

// structs, unions, matching, narrowing
struct Point  { x: f64, y: f64 }
struct Circle { c: Point, r: f64 = 1.0 }   // a field default
struct Rect   { lo: Point, hi: Point }
type Shape = Circle | Rect;             // a union, not a hierarchy

area(s: Shape) = match s {               // arms are display entries — commas, not `;`
  Circle(r:)      -> pi * r * r,
  Rect(lo:, hi:)  -> (hi.x - lo.x) * (hi.y - lo.y),
};                                       // exhaustive, or it doesn't compile

p  = Point(x: 1.0, y: 2.0);
p2 = p with { x = 3.0 };                // functional update — a new value
unit = Circle(c: p);                    // r takes its default
onAxis = Point(x: 0.0, ...);            // a struct is its constructor, curried by name: called onAxis(y: 1.0)

struct Round { import Rect, r: f64 }     // composition-import, not inheritance
```

<!-- DESIGN.md:2470 layer L10: ring L10, word none, label none -->
```zed
struct Counter { n: int, hi: int }

Counter.tick() {                 // no declared return ⇒ the next receiver is the whole result
  n'  = n + 1;                   // primes build the next version of the receiver;
  hi' = max(hi, n + 1);          //   unassigned fields carry forward
}
Counter.bump(positional by) -> int {  // declared -> int, and primed, so the result is (Counter, int)
  n'  = n + by;
  hi' = max(hi, n + by);
  return n;                      // the old count rides beside the mutated receiver
}
Counter.atHi = n == hi;          // no primes, no prefix — an ordinary read

p       = Counter(n: 0, hi: 9);  // `.` is pure, so every spelling below is pure
p2      = p.tick().tick();       //   T -> T chains by composition
p3, was = p.bump(2);             //   two results, two targets — the non-OO spelling
p4, w2  = bump(p, 2);            //   ≡ the same call, written without UFCS
// p*.bump(3);                   // ✗ p is a value binding — no next generation to write

run = loop {
  mutable c = Counter(n: 0, hi: 9); // state receiver: carry-forward, boundary at t = -1
  prev = c*.bump(3);                // `*.` calls and mutates: writes c', yields the return
  until prev > 20;                  //   — one write of c' per step, as always

  // each variant below replaces the `prev = …` line; none may join it (one writer of c')
  // a, b = c*.bump(1).bump(2);     // a chain threads the receiver: ONE write of c' at the
                                    //   end, its value the links' returns, in order
  // c*.tick().tick();              // no returns ⇒ a statement, still exactly one write
  // _ = c*.bump(1); _ = c*.bump(2); // ✗ two chains, two writers of c': the collision error
  // c.bump(3);                     // ✗ `.` never mutates, so this writes nothing: dead
  // c', prev = c.bump(3);          // the explicit spelling; `*.` abbreviates it, both legal
};
```

<!-- DESIGN.md:2514 layer L5: ring L5, word L5 (sort), label none -->
```zed
xs   = [3, 1, 4, 1, 5];                 // [int]  ≡  int[0..<5] -> int
m    = { "a" -> 1, "b" -> 2 };          // display: commas inside, `;` ends the statement;
                                        //   inferred exact {"a","b"} -> int  <:  String ->? int
tags = { #red, #green };                // set ≡ self-map
word = "never" ++ "the" ++ "less";      // String: rank-keyed, ++ concatenates by offset — O(1), rope-backed

tens = xs.map(x -> x * 10);             // same keys, new values
big  = xs.where(x -> x > 2);            // sparse subdomain (type records sparsity)
srt  = xs.sort(desc x -> x);            // [5, 4, 3, 1, 1]: a ranked source sorts flat; stability is a theorem
tot  = xs.sum;                          // = xs >< (+): sum, count, and reduce(op) are the fold in the method register

// WORD COUNT — method register:
counts = text.split(" ").group(w -> w.lower).count;
// counts : String ->? int     (f() ≡ f — a unit morphism reads as its value)
```

<!-- DESIGN.md:2531 layer L8: ring L8, word L3 (split), label none -->
```zed
// the same program, symbolic register (what the optimizer reasons over):
counts = text.split(" ") as (i -> w) into (w.lower -> i -> 1) >< (+);
```

<!-- DESIGN.md:2536 layer L4: ring L1, word L4 (rekey), label none -->
```zed
// group vs rekey — the grouping decision is always a visible word:
byId = users.rekey(u -> u.id);  // ✗ compile error unless id-uniqueness is witnessed:
                                //   "two users could share an id — use group,
                                //    or mark the key function @injective"
```

<!-- DESIGN.md:2543 layer L5: ring L1, word L5 (maxBy), label none -->
```zed
byId = users.group(u -> u.id);  // ✓ type: Id ->? (UserKey -> User)  (the extra level, declared by the word)

// argmax keeps ties honest — keypath integrity forces the policy into the open:
best = scores.maxBy(v -> v);    // (score ->? name -> score) | #none: ALL tied entries kept, #none only when scores is empty
one  = best?.first;             // #none carried; lexicographic: the max-score group, then least name
                                // (first/last descend by each level's order — sec:corner_cases)
```

<!-- DESIGN.md:2554 layer L5: ring L1, word L5 (join), label none -->
```zed
// query projection      (payments : OrderId -> Payment — uniquely keyed,
//                        which is what keeps the join flat, sec:joins;
//                        kind: #inner | #left | #right | #outer, #inner by default)
paid = orders.join(payments, on: #orderId, kind: #left);
     // OrderId -> (Order, Payment | #none) — the pair of sec:joins; absence is a value, not a null row
```

<!-- DESIGN.md:2562 layer L3: ring L3, word none, label none -->
```zed
// iteration projection — the SAME kernel term; the compiler picks the plan
paid = for o in orders {
  payment = payments[o.orderId] else #none;
  (o, payment)                 // the frame's export: the one statement without a `;`
};
```

<!-- DESIGN.md:2570 layer L5: ring L1, word L5 (diff), label none -->
```zed
// anti-join, both ways (same term again)
unpaid = orders.diff(payments, on: #orderId);
```

<!-- DESIGN.md:2575 layer L8: ring L8, word L3 (where), label none -->
```zed
unpaid = orders.where(o -> payments[o.orderId] is #notFound);

// several generators: one level keyed by the tuple of keys; generators that do not depend on each other
// range over the product of their domains — an equality between them in `where` is planned as a join,
// and no predicate is the cross product (shipments : ShipmentId -> Shipment, orderId a field — one order, several shipments)
shipped = for o in orders, s in shipments where o.orderId == s.orderId { (o, s) };   // ((OrderId, ShipmentId)) ->? (Order, Shipment): one level, tuple-keyed

// a domain that mentions another generator's binder nests inside it, as the dependency requires: the
// pairs with i < j, keyed (i, j) — the same family as `for i in 0..<n, j in 0..<n where i < j`
pairs = for i in 0..<n, j in i+1..<n { (i, j) };

// matrix multiply — join on the inner dimension, reduce it away
matmul(positional a: (r -> c -> f64), positional b: (c -> k -> f64)) =
  (a, b) into (r -> k -> c >< (+) -> a[r][c] * b[c][k]);  // shared inner domain c, named by both sources; the float fold takes c's order — a rank for a matrix (sec:joins)
// read as an index expression: the output names the free levels (r, k), the reduced level (c) is summed
// away, and the leaf is the product — einsum's "rc,ck->rk", with the contraction written where it happens
prod = a.matmul(b);
```

<!-- DESIGN.md:2597 layer L6: ring L6, word L6 (::frames), label none -->
```zed
// comprehension — parallel by default
sq = for i in 0..<n { i * i };

// recurrence with a sentinel — compiled to a parallel scan (+ is associative)
cdf[i] = cdf[i-1] + hist[i]  with cdf[-1] = 0;
total  = cdf.last else 0;                // .first/.last: by rank order; | #none when empty

// generations: the only mutable state
sim = loop {
  pos' = pos + vel * dt        with pos = p0;
  vel' = vel + a(pos) * dt     with vel = v0;
  until pos'.x > bound;                  // primes test the new state; bare names the old
};
final   = sim.pos;                       // last generation's value
history = sim::frames;                   // Gen -> { pos: P, vel: V } — the whole trajectory
steps   = sim::len;

// fixpoint loops need no dirty flags
simplified = loop {
  terms' = simplifyOnce(terms)  with terms = input;
  until terms' == terms;
};

// group-boundary processing without the classic off-by-one-flush bug
sessions = events.chunkBy(e -> e.userId);     // key-change splits; last chunk included
report   = sessions.map(s -> summarize(s));
```

<!-- DESIGN.md:2628 layer L3: ring L3, word L3 (where), label none, documentation notation -->
```zed
parse : (String) -> Config | #syntaxError(pos: int)   // an assumed input, shown as a type — no ';' (sec:lexical)

conf = parse(text) else defaultConfig;
port = parse(text)?.server?.port else 8080;    // ?. carries the union; else disposes of it

results = files.map(f -> read(f)).map(b -> parse(b));
// File -> Config | #ioError | #notFound | #syntaxError(pos)   — bad records flow, tagged, with lineage
good = results.where(r -> r is Config);
bad  = results.where(r -> r is not Config);     // each still knows which file, which wave

amounts = files.map(f -> int(read(f)));        // File -> int | #ioError | #notFound | #invalid
sum     = amounts >< (+);                      // ✗ (+) is not total on int | #ioError | #notFound | #invalid —
                                               //   the unlifted-carrier rule (sec:reduction),
// so the fold is rejected here — not lifted, not summarized behind your back, and with
// nothing accumulated there is no retained-error count to tune. Say what they mean:
sumKept   = amounts.where(a -> a is int) >< (+);   // 1: drop errors — visibly
sumZeroed = amounts.map(a -> a else 0) >< (+);     // 2: default them — visibly
badAmounts = amounts.where(a -> a is not int);     // 3: keep them — an ordinary
                                                   //    collection, sized and reported
sumAll    = amounts.allOk >< (+);                  // 4: all or nothing: the sum, or the failures
```

<!-- DESIGN.md:2653 layer L21: ring L20, word L21 (store), label none, documentation notation -->
```zed
// one declaration: type + parser + serializer (round-trip canonical)
struct KeyVal  grammar { key: Ident  ":"  value: Json }
struct JsonObj grammar { "{"  entries: KeyVal sep ","  "}" }
type   Json = JsonObj | JsonArr | JsonStr | JsonNum | #true | #false | #null;

cfg = Json.parse(bytes);         // Json | #syntaxError(pos: int)  — recovery structural
out = cfg?.serialize;            // keys sorted: parse(serialize(x)) == x; ?. carries the union

type Ident = String matching grammar { alpha (alpha | digit)* };  // typed strings, not regexes
// whitespace: struct grammars (phrase level) skip insignificant whitespace between elements;
// matching grammars (token level, as here) are exact. serialize emits none — the canonical form.

// tests are data, attached to the definition, run in the dirty cone only
double(positional x) = x * 2       // the `test` clause ends the declaration, so no `;` here
  test { 0 -> 0, 2 -> 4, -3 -> -6 }
law doubleIsSum(x: int) = double(x) == x + x;   // a test over the whole domain: graded, never run (sec:verification)

// ports are the only outside world
main(stdin: Lines) -> (stdout: Lines) {
  stdout <- stdin.map(l -> l.upper);
}

// a stored collection is a port too; its schema is a build input, matched statically
orders: OrderId ->? { total: rat, note: String | #none }
  with store(postgres(dbUrl, table: "orders", schema: sql("db/orders.sql")));

n = orders[id]?.note;              // String | #none | #notFound | #dbError — NULL, no row, no db
// note:  String                   // ✗ the column is nullable: #none missing from the field type
// total: f64                      // ✗ NUMERIC is not a binary float

// facets: units and taint are checked like types
v = 3.0 with units("m/s");
t = 2.0 with units("s");
d = v * t;                         // d::units == "m"
// e = v + t;                      // ✗ compile error: unit mismatch

exec : (Db, String with taint(#clean)) -> Rows | #sqlError   // a sink's signature, shown as a type
// exec(db, userInput);            // ✗ #userInput taint reaches a #clean sink
rows = exec(db, sanitize(userInput));     // ✓ sanitizers are the only taint-removers
```

<!-- DESIGN.md:2746 layer L3: ring L1, word none, label L3 -->
```zed
// layer L3
priceOf(positional items, positional id) = items[id]?.price * (1 + taxRate);
```

<!-- DESIGN.md:2753 layer L2: ring L2, word none, label none, documentation notation -->
```zed
priceOf : (K ->? {price: f64}, K) -> f64 | #notFound
```

<!-- DESIGN.md:2765 layer L20: ring L20, word L20 (serialize), label none -->
```zed
// 1 — Deterministic parallel float sum: bit-identical at any core count.
total = readings >< (+);
// Elsewhere: parallel float reduction is nondeterministic unless you build the tree yourself.

// 2 — Scatter and gather are the same computation; the compiler proves it and picks the plan.
histA = words.group(w -> w.len).count;
histB = for n in 0..=maxLen { words.where(w -> w.len == n).count };
// Same kernel term up to the stated domain (law 24): histB's dense domain also states the zero
// buckets (outer-join histA with 0s to convert); the plans converge on the shared part.
// Elsewhere: two different programs, two different performance cliffs, no equivalence check.

// 3 — Edit distance, written both ways, one meaning: memoized recursion or wavefront table.
d[i][j] = min(d[i-1][j] + 1, d[i][j-1] + 1, d[i-1][j-1] + cost(a[i], b[j]))
  with d[-1][j in -1..<b::len] = j + 1, d[i in 0..][-1] = i + 1;  // disjoint pieces: the corner
  // d[-1][-1] = 0 is the first family's j = -1 entry — overlap would be a collision
// The demanded corner pulls (memoized); dense demand pushes (wavefront). Same source.

// 4 — "Inherently serial" text scan, parallelized because the state domain is finite.
state[i] = csvStep(state[i-1], text[i])  with state[-1] = #outsideQuotes;
// state : #outsideQuotes | #inQuotes | #escape (finite) — so the compiler reifies
// csvStep into a transition table and runs a parallel prefix scan.

// 5 — First prime above N: speculative parallel search with automatic cancellation.
firstPrime = (for i in n.. { i }).where(isPrime).first;
// Pure ⇒ higher candidates run speculatively and are canceled the instant a lower hit lands.
// Typed `int | #none`: the source is infinite but primality is not the checker's business,
// so a use site still says what an empty selection means (sec:corner_cases).

// 6 — Sessionize a log: the group-boundary/flush-the-last-group bug cannot be written.
sessions = clicks.chunkBy(c -> c.userId).map(s -> Session(start: s.first.time, count: s.count));
// a chunk exists only because a click fell into it (L ≠ ∅), so .first is exact — no #none case

// 7 — Undo, redo, and time travel are field reads, not an architecture.
run  = loop t { while t < edits::len && !closed; doc' = doc.patch(edits[t])  with doc = empty; };
     // history bounded by edits::len; retained because ::frames is demanded below
past = run::frames[run::len - 2].doc else empty;  // any past state, O(log n), shared

// 8 — A spreadsheet cell is just a memoized value; editing one input reflows in milliseconds.
@memoized report = sales.join(costs, on: #sku).group(((s, c)) -> s.region).map(rows -> rows.map(((s, c)) -> margin(s, c)).sum);
// Edit one row of sales ⇒ exactly the dirty cone recomputes, with provenance for every cell.

// 9 — SQL injection is a compile error, not a code-review hope.
// rows = exec(db, "SELECT * WHERE name = " ++ userName);      // ✗ taint #userInput reaches #clean sink
rows = exec(db, "SELECT * WHERE name = " ++ sanitize(userName));  // ✓ and the sanitizer is auditable

// 10 — Wrong physics doesn't build.
energy = 0.5 * m * v * v;         // energy::units == "kg m^2 s^-2"  (a joule)
// e = energy + force;            // ✗ unit mismatch at compile time: kg m s^-2 is not kg m^2 s^-2

// 11 — One declaration = type + parser + printer, with round-trip guaranteed.
struct Vec3 grammar { "(" x: f64 "," y: f64 "," z: f64 ")" }
v = Vec3.parse("(1.0, 2.0, 3.0)") else Vec3(x: 0.0, y: 0.0, z: 0.0);
s = v.serialize;                   // "(1.0,2.0,3.0)" — phrase grammars skip input whitespace, serialize emits the canonical none; parse ∘ serialize == id

// 12 — Compute only what's asked: one stats module, demand-pruned.
stats(positional data: [f64]) {
  n = f64(data::len);                // conversion by type application — no cast syntax
  mean = data.sum / n;
  sd   = (data.map(x -> (x - mean) ** 2).sum / n).sqrt;
  return { mean:, sd: };     // one export, a record display: each field is its own node
}
m = stats(xs).mean;                // sd's sub-graph never runs
// Elsewhere: you split the API, or you pay for everything every call.

// 13 — Invert any finite map in one line — grouping is a type, not a runtime surprise.
whoTeaches = teacherOf as (teacher -> course) into (course -> teacher -> _);   // teacherOf : Teacher -> Course; result Course ->? {Teacher}

// 14 — A tiny service, split into client and server by the compiler.
main(req: Stream(Query)) -> (resp: Stream(Answer)) {
  resp <- req.map(q -> lookup(db, q) else #unknown);
}
// Deploy with a keypath cut: the boundary serializes via struct grammars — RPC without stubs.

// 15 — Exhaustive correctness, free, when domains are small.
@exhaustive romanDigit(n: int[1..=9]) -> String { … }
  test { 1 -> "I", 4 -> "IV", 9 -> "IX" }
  // @exhaustive: all nine inputs run at build time — totality, the declared
  // properties, and the test table are checked on every one. (A complete
  // expected-output table makes this a full proof; with a partial table,
  // unlisted inputs are verified for totality and properties only.)
  // (@checked is different: it marks representation-capped integers whose
  //  overflow surfaces as a value instead of widening)

// 16 — A ten-hour pipeline survives its bad records and can prove which they were.
out = files.map(read).map(parse).map(transform);
bad = out.where(r -> r is not Row);   // every failure carries file, offset, wave, and cause

// 17 — Declared history, inferred storage: the compiler keeps exactly two frames.
pos[i in 0..<n] = 2*pos[i-1] - pos[i-2] + accel(pos[i-1]) * dt ** 2
  with pos[-1] = p0, pos[-2] = p0 - v0*dt;
last = pos[n-1] else p0;    // dependence window = 2 ⇒ a two-slot ring; no array exists
// traj = pos::frames;      // demanding the history would turn storage back on — a different plan
// Elsewhere: you hand-rewrite the array into two variables and lose the history option.

// 18 — Indexes are demand: no keyed lookups, no index — the "table" stays a flat run.
report = logs.map(rowCost).sum;       // logs : Id ->? Row, but only ever scanned here:
                                      //   the id index has no dependents — pruned;
                                      //   contents compile to a linear unindexed run
// hot = logs[someId];                // one keyed probe would demand the index, built
                                      //   lazily or eagerly by the cost arithmetic
// Elsewhere: the index exists because the schema says so, and you pay for it either way.

// 19 — Maximum subarray, a non-associative scan, parallelized because its step is affine over (max, +).
cur[i] = max(xs[i], cur[i-1] + xs[i])  with cur[-1] = 0;
best = cur >< max else 0;
// xs : int[0..<n] -> int. The step c -> max(xs[i], c + xs[i]) is the (max, +) affine map
// (a, b) = (xs[i], xs[i]), and two such maps compose to (max(a2, a1 + b2), b1 + b2),
// so cur is a parallel prefix scan (sec:optimizer). Floats do not take this path.
// Elsewhere: Kadane's loop is serial, and its parallel form is a research exercise.

// 20 — A generic JSON decoder, specialized by partial evaluation into a decoder for one struct.
struct User { id: int, name: String }
u: User | #parseError(pos: int, msg: String) = Json.decode(text);
// The ascription fixes decode's result type at User (sec:type_resolution, rule 2), and User
// is known at build, so mix specializes decode on it (sec:staging): the generic JSON parser,
// the schema check, and the unpacker into a native struct become one deserializer that reads
// the two fields of User directly into a User, with no intermediate Json tree, and with the
// field names of User compiled into the matcher. text : String has no finite domain, so mix
// does not specialize on it: the checks on its contents stay in the residual program, and
// #parseError stays in the type.
ok:  User | #parseError(pos: int, msg: String) = Json.decode("{\"id\": 5, \"name\": \"John\"}");
bad: User | #parseError(pos: int, msg: String) = Json.decode("{\"id\": \"5\", \"name\": \"John\"}");
// Here the input is a literal, whose domain is a singleton (sec:domains), so the whole call
// runs at build: ok is the constant User(id: 5, name: "John"), and bad is the constant
// #parseError(pos: 7, msg: "expected int for field 'id', got string"). Neither residual
// program contains a parser. decode is written in Zed, in the prelude unit Json, with the
// reads of (sec:introspection): T::shape selects the arm, T::fields gives the names and types.
// Elsewhere: a generic decoder reflects on the type at run time (Jackson), or a macro or a
// code generator writes the specialized decoder (serde, protoc), as a second tool.
```
