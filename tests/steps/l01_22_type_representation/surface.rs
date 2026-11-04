//! A type in a message is printed in the surface syntax (cross-review xv, SYNTHESIS Q5): the
//! parser accepts the text, and read back it is the same type. The reader here is the test's
//! own, from the grammar's meaning of each form; the kernel's printer and this reader share no
//! code.

use std::collections::BTreeMap;

use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::types::{Surface, Type, Universe};
use zed_kernel::value::Value;
use zed_tests::scaling;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};

fn lit(i: i64) -> Type {
    Type::lit(&Value::Int(i)).unwrap()
}

fn tuple(ts: &[Type]) -> Type {
    Type::tuple(ts.to_vec())
}

/// Whether the parser accepts `text` from the rule `start`.
fn accepts(text: &str, start: &str) -> Result<(), String> {
    let tokens = lex_fence(text).map_err(|e| format!("{text}: {e:?}"))?;
    parse(text, &tokens, start, TOP)
        .map(|_| ())
        .map_err(|e| format!("{text}: {e:?}"))
}

/// A reader of printed types, for comparing meaning.
struct Reader<'a> {
    tokens: Vec<String>,
    at: usize,
    names: &'a BTreeMap<String, Type>,
}

fn tokens(s: &str) -> Vec<String> {
    let c: Vec<char> = s.chars().collect();
    let (mut i, mut out) = (0, Vec::new());
    while i < c.len() {
        if c[i].is_whitespace() {
            i += 1;
        } else if c[i].is_alphanumeric() || c[i] == '#' || c[i] == '_' {
            let j = i;
            i += 1;
            while i < c.len() && (c[i].is_alphanumeric() || c[i] == '_') {
                i += 1;
            }
            out.push(c[j..i].iter().collect());
        } else if let Some(p) = ["->?", "->", ".."]
            .into_iter()
            .find(|p| c[i..].iter().take(p.len()).copied().eq(p.chars()))
        {
            out.push(p.to_string());
            i += p.len();
        } else {
            out.push(c[i].to_string());
            i += 1;
        }
    }
    out
}

impl Reader<'_> {
    fn peek(&self) -> &str {
        self.tokens.get(self.at).map_or("", |s| s)
    }

    fn eat(&mut self, s: &str) -> bool {
        let found = self.peek() == s;
        self.at += usize::from(found);
        found
    }

    fn expect(&mut self, s: &str) -> Type {
        assert!(self.eat(s), "expected `{s}` at `{}`", self.peek());
        Type::empty()
    }

    /// `Arrow`: `K -> V`, `K ->? V`, `L .. U -> V`, or a union.
    fn ty(&mut self) -> Type {
        let a = self.union();
        if self.eat("->") {
            let v = self.ty();
            Type::morphism(a.clone(), a, v)
        } else if self.eat("->?") {
            Type::morphism(Type::empty(), a, self.ty())
        } else if self.eat("..") {
            let u = self.union();
            self.expect("->");
            Type::morphism(a, u, self.ty())
        } else {
            a
        }
    }

    fn union(&mut self) -> Type {
        let mut a = self.and();
        loop {
            if self.eat("|") {
                a = &a | &self.and();
            } else if self.eat("\\") {
                a = &a - &self.not();
            } else {
                return a;
            }
        }
    }

    fn and(&mut self) -> Type {
        let mut a = self.not();
        while self.eat("&") {
            a = &a & &self.not();
        }
        a
    }

    fn not(&mut self) -> Type {
        match self.eat("!") {
            true => &Type::top() - &self.not(),
            false => self.prim(),
        }
    }

    /// The items of a parenthesized list, after its `(`, through its `)`.
    fn items(&mut self) -> Vec<Type> {
        let mut xs = Vec::new();
        while !self.eat(")") {
            xs.push(self.ty());
            if !self.eat(",") {
                self.expect(")");
                break;
            }
        }
        xs
    }

    fn prim(&mut self) -> Type {
        if self.eat("(") {
            if self.eat("..") {
                self.expect(")");
                return Type::universe(Universe::Tuple);
            }
            let a = self.ty();
            if self.eat(")") {
                return a;
            }
            self.expect(",");
            let mut xs = vec![a];
            xs.extend(self.items());
            return Type::tuple(xs);
        }
        if self.eat("-") {
            let n: i64 = self.peek().parse().unwrap();
            self.at += 1;
            return lit(-n);
        }
        if self.eat("{") {
            self.expect("..");
            self.expect("}");
            return Type::universe(Universe::Struct);
        }
        let w = self.peek().to_string();
        self.at += 1;
        match w.as_str() {
            "_" => Type::top(),
            // Every atom: the scalars that are not of a carrier.
            "#_" => [
                Type::bool(),
                Type::int(),
                Type::rat(),
                Type::f64(),
                Type::string(),
            ]
            .iter()
            .fold(Type::universe(Universe::Scalar), |a, c| &a - c),
            "true" => Type::lit(&Value::Bool(true)).unwrap(),
            "false" => Type::lit(&Value::Bool(false)).unwrap(),
            "bool" => Type::bool(),
            "int" => Type::int(),
            "rat" => Type::rat(),
            "f64" => Type::f64(),
            "String" => Type::string(),
            _ => {
                if let Ok(n) = w.parse() {
                    return lit(n);
                }
                let Some(name) = w.strip_prefix('#') else {
                    return self
                        .names
                        .get(&w)
                        .cloned()
                        .unwrap_or_else(|| panic!("`{w}`"));
                };
                if !self.eat("(") {
                    return Type::atom(name);
                }
                // `#a(..)` is the atom with any payload; `#a(A, B)` with the payload `(A, B)`,
                // so `#a(_)` is the one-tuple payload only.
                if self.eat("..") {
                    self.expect(")");
                    return Type::atom_with(name, &Type::top());
                }
                Type::atom_with(name, &Type::tuple(self.items()))
            }
        }
    }
}

/// The type a printed text denotes, its definitions read in order.
fn read(s: &Surface) -> Type {
    let mut names = BTreeMap::new();
    for (name, body) in &s.defs {
        let mut r = Reader {
            tokens: tokens(body),
            at: 0,
            names: &names,
        };
        let t = r.ty();
        assert_eq!(r.at, r.tokens.len(), "{body}");
        names.insert(name.clone(), t);
    }
    let mut r = Reader {
        tokens: tokens(&s.root),
        at: 0,
        names: &names,
    };
    let t = r.ty();
    assert_eq!(r.at, r.tokens.len(), "{s}");
    t
}

/// Panics unless `t` prints as text the parser accepts and that reads back as `t`.
fn round_trip(t: &Type) -> Surface {
    let s = t.surface();
    assert!(s.exact, "{s}");
    accepts(&s.root, "Type").unwrap();
    for (name, body) in &s.defs {
        accepts(&format!("type {name} = {body};"), "Unit").unwrap();
    }
    let back = read(&s);
    assert!(
        back.subtype(t) && t.subtype(&back),
        "{s} reads back as another type"
    );
    s
}

#[test]
fn the_types_of_everyday_values_print_as_written() {
    let small = Type::union_all((0..3).map(lit));
    for (t, text) in [
        (Type::top(), "_"),
        (Type::empty(), "!_"),
        (Type::int(), "int"),
        (lit(-3), "-3"),
        (small.clone(), "0 | 1 | 2"),
        (&Type::int() - &small, r"int \ (0 | 1 | 2)"),
        (Type::atom("none"), "#none"),
        (&Type::top() - &Type::atom("none"), r"_ \ #none"),
        (tuple(&[Type::int()]), "(int,)"),
        (tuple(&[Type::int(), Type::string()]), "(int, String)"),
        (&tuple(&[lit(0)]) | &Type::int(), "int | (0,)"),
        (Type::exact(Type::int(), Type::bool()), "int -> bool"),
        (Type::partial(Type::int(), Type::bool()), "int ->? bool"),
        (
            Type::morphism(lit(0), Type::int(), Type::bool()),
            "0 .. int -> bool",
        ),
        (
            Type::exact(tuple(&[Type::int(), Type::int()]), Type::int()),
            "((int, int)) -> int",
        ),
    ] {
        let s = round_trip(&t);
        assert_eq!(s.to_string(), text);
    }
}

#[test]
fn records_of_a_shape_and_its_differences_read_back_as_the_same_type() {
    let pair = tuple(&[Type::int(), Type::int()]);
    let origin = tuple(&[lit(0), Type::top()]);
    let cons = Type::atom_with("cons", &tuple(&[Type::int(), Type::string()]));
    let either = &Type::exact(Type::int(), Type::bool()) & &Type::exact(Type::bool(), Type::int());
    for t in [
        &pair - &origin,
        &Type::top() - &tuple(&[lit(0), lit(1)]),
        tuple(&[tuple(&[lit(1), tuple(&[lit(2), lit(3)])]), lit(4)]),
        cons.clone(),
        &cons | &Type::atom("nil"),
        Type::atom_with("some", &Type::top()),
        either,
        &Type::exact(Type::int(), Type::top()) - &Type::exact(Type::int(), Type::bool()),
        Type::exact(Type::int(), Type::exact(Type::int(), Type::int())),
    ] {
        round_trip(&t);
    }
}

/// A seeded generator of formulas over tuple types.
struct Seed(u64);

impl Seed {
    fn next(&mut self, m: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 33) % m
    }

    fn cell(&mut self) -> Type {
        match self.next(9) {
            0 => Type::int(),
            1 => Type::top(),
            2 => Type::bool(),
            3 => Type::atom("a"),
            _ => {
                let m = 1 + self.next(7);
                Type::union_all((0..3).filter(|i| m & (1 << i) != 0).map(lit))
            }
        }
    }

    fn formula(&mut self, w: usize, d: usize) -> Type {
        if d == 0 || self.next(4) == 0 {
            return Type::tuple((0..w).map(|_| self.cell()).collect());
        }
        let (a, b) = (self.formula(w, d - 1), self.formula(w, d - 1));
        match self.next(4) {
            0 => &a | &b,
            1 => &a & &b,
            2 => &a - &b,
            _ => &(&a - &b) | &(&b - &a),
        }
    }
}

#[test]
fn unions_differences_and_intersections_of_rows_read_back_as_the_same_type() {
    for s in 0..400 {
        let mut seed = Seed(s * 7919 + 1);
        let w = 1 + seed.next(3) as usize;
        round_trip(&seed.formula(w, 3));
    }
}

/// `n` levels of a pair of the level below: `2^n` paths, `n` nodes.
fn shared(n: usize) -> Type {
    (0..n).fold(lit(0), |t, _| tuple(&[t.clone(), t]))
}

/// Binary words of length `n` over 0 and 1, as nested pairs.
fn words(n: usize) -> Type {
    (0..n).fold(lit(0), |t, _| {
        &tuple(&[lit(0), t.clone()]) | &tuple(&[lit(1), t])
    })
}

/// The pairs `(i, i)` for `i < n`, built by symmetric difference.
fn xor(n: usize) -> Type {
    (0..n as i64).fold(Type::empty(), |x, i| {
        let t = tuple(&[lit(i), lit(i)]);
        &(&x - &t) | &(&t - &x)
    })
}

#[test]
fn a_type_used_twice_is_named_once() {
    let s = round_trip(&shared(3));
    assert_eq!(
        s.to_string(),
        "type T1 = (0, 0); type T2 = (T1, T1); (T2, T2)"
    );
    for n in [1, 2, 6] {
        round_trip(&shared(n));
        round_trip(&words(n));
        round_trip(&xor(n));
    }
}

fn list() -> Type {
    let body = Expr::Union(vec![
        Expr::Type(Type::atom("nil")),
        Expr::Atom(
            "cons".into(),
            vec![Expr::Type(Type::int()), Expr::Ref(0, vec![])],
        ),
    ]);
    let def = Def {
        name: "List".into(),
        params: vec![],
        body,
    };
    Group::new(vec![def]).unwrap().instance(vec![]).remove(0)
}

#[test]
fn a_list_type_prints_as_a_definition_that_names_itself() {
    let s = list().surface();
    assert!(s.exact, "{s}");
    assert_eq!(s.to_string(), "type T1 = #cons(int, T1) | #nil; T1");
    accepts("type T1 = #cons(int, T1) | #nil;", "Unit").unwrap();
    let s = tuple(&[list(), lit(1)]).surface();
    assert_eq!(s.to_string(), "type T1 = #cons(int, T1) | #nil; (T1, 1)");
}

#[test]
fn every_atom_every_tuple_and_every_struct_print_as_the_kind_wide_types() {
    // Step L1.40d: `#_`, `(..)`, `{..}` and `#a(..)` are user syntax, so each prints exactly.
    let atoms = &Type::universe(Universe::Scalar)
        - &Type::union_all([
            Type::bool(),
            Type::int(),
            Type::rat(),
            Type::f64(),
            Type::string(),
        ]);
    let tuples = (&Type::top() - &Type::int()).part(Universe::Tuple);
    let structs = Type::universe(Universe::Struct);
    let pair = tuple(&[Type::int(), Type::int()]);
    for (t, text) in [
        (atoms.clone(), "#_"),
        (tuples.clone(), "(..)"),
        (structs.clone(), "{..}"),
        (Type::atom_with("a", &Type::top()), "#a(..)"),
        (Type::atom_with("a", &tuple(&[])), "#a()"),
        (Type::atom_with("a", &tuple(&[Type::top()])), "#a(_)"),
        (&atoms - &Type::atom("b"), r"#_ \ #b"),
        (&tuples - &pair, r"(..) \ (int, int)"),
        (&tuples | &structs, "(..) | {..}"),
        (
            &Type::atom_with("a", &Type::top()) - &Type::atom_with("a", &pair),
            r"#a(..) \ #a(int, int)",
        ),
    ] {
        let s = round_trip(&t);
        assert_eq!(s.to_string(), text);
    }
    // `#a()` is the atom with the empty payload, not the bare atom `#a`.
    assert!(!Type::atom("a").subtype(&Type::atom_with("a", &tuple(&[]))));
    assert!(!Type::atom_with("a", &tuple(&[])).subtype(&Type::atom("a")));
}

#[test]
fn a_payload_of_every_tuple_alone_or_every_struct_alone_is_marked_not_exact() {
    // A payload holds tuples and structs; the surface syntax has no type for one kind of
    // payload alone, as DESIGN.md names none.
    for (t, text) in [
        (
            Type::atom_with("a", &Type::universe(Universe::Tuple)),
            "#a(tuple)",
        ),
        (
            Type::atom_with("a", &Type::universe(Universe::Struct)),
            "#a(struct)",
        ),
    ] {
        let s = t.surface();
        assert!(!s.exact, "{s}");
        assert_eq!(s.to_string(), text);
    }
}

#[test]
fn the_text_does_not_depend_on_what_was_built_before() {
    let text = |junk: bool| -> String {
        let mut out = String::new();
        for s in 0..100 {
            let mut seed = Seed(s * 7919 + 1);
            let w = 1 + seed.next(3) as usize;
            let kept: Vec<Type> = match junk {
                true => (0..50).map(|i| tuple(&[lit(9000 + i), lit(i)])).collect(),
                false => Vec::new(),
            };
            let t = seed.formula(w, 3);
            let t = match junk {
                true => {
                    let _ = t.is_empty();
                    t
                }
                false => t,
            };
            out.push_str(&t.surface().to_string());
            out.push('\n');
            drop(kept);
        }
        out
    };
    assert_eq!(text(false), text(true));
}

#[test]
fn the_text_of_a_type_shared_n_deep_scales() {
    // A pair of the level below, n deep, has 2^n paths: the text names each level once.
    scaling::check("the text of a pair type shared n deep", 1000, |n| {
        let s = shared(n).surface();
        assert_eq!(s.defs.len(), n - 1);
    });
}
