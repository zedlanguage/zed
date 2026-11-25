//! The order in which the members of a union print (DESIGN.md sec:diagnostics, author decision
//! A92): one order fixed by the type, so that equal types print alike whatever order the
//! program wrote them in, and two messages that print one union print it alike. Every printer
//! of a union, the kernel's (`super::Printer`) and the checker's, places its members by
//! [`cmp`]:
//!
//! 1. numeric literals, ascending by value, two of one value by their carrier in the order of
//!    the next group;
//! 2. the number types: `int`, then `bf16`, `f16`, `f32`, `f64`, `rat`;
//! 3. `false`, `true`, `bool`;
//! 4. string literals, by their code points;
//! 5. named types (`String`, structs, aliases, recursive types) and type variables, by name
//!    ([`name_cmp`]); two recursive types of one name by their arguments, which no printer
//!    meets yet, since the union of two recursive types is their unfolding;
//! 6. tuples, by their components ([`seq_cmp`]); then every struct, `{..}`;
//! 7. functions;
//! 8. atoms: every atom `#_` first, then by name, the bare atom before the one with a payload,
//!    two payloads of one name by their components ([`seq_cmp`]);
//! 9. `_`, every value.
//!
//! Character literals and types have no member here yet: no printer writes one.

use std::cmp::Ordering;

use crate::text::Text;
use crate::value::{Value, number_cmp};

/// A member of a union, as much of it as its place in the order reads.
#[derive(Clone, Copy, Debug)]
pub enum Member<'a> {
    /// A numeric literal.
    Number(&'a Value),
    /// A number type, or what is left of one after some literals are taken out.
    NumberType(NumberType),
    /// `false`.
    False,
    /// `true`.
    True,
    /// `bool`.
    Bool,
    /// A string literal, by its text.
    Str(&'a Text),
    /// A named type or a type variable, by its name.
    Named(&'a str),
    /// A tuple type.
    Tuple,
    /// Every struct, `{..}`.
    Struct,
    /// A function type.
    Function,
    /// Every atom, `#_`, or what is left of it after some atoms are taken out.
    AnyAtom,
    /// An atom by its name: bare, or with a payload.
    Atom {
        /// Its name, without the `#`.
        name: &'a str,
        /// Whether it is the atom with a payload.
        payload: bool,
    },
    /// `_`, every value.
    Top,
}

/// The number types, in the order they print.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum NumberType {
    /// `int`.
    Int,
    /// `bf16`.
    Bf16,
    /// `f16`.
    F16,
    /// `f32`.
    F32,
    /// `f64`.
    F64,
    /// `rat`.
    Rat,
}

impl<'a> Member<'a> {
    /// The member a type written as the one name `name` is: a number type, `bool`, or else a
    /// named type or type variable.
    pub fn of_name(name: &'a str) -> Member<'a> {
        match name {
            "int" => Member::NumberType(NumberType::Int),
            "bf16" => Member::NumberType(NumberType::Bf16),
            "f16" => Member::NumberType(NumberType::F16),
            "f32" => Member::NumberType(NumberType::F32),
            "f64" => Member::NumberType(NumberType::F64),
            "rat" => Member::NumberType(NumberType::Rat),
            "bool" => Member::Bool,
            "false" => Member::False,
            "true" => Member::True,
            _ => Member::Named(name),
        }
    }

    /// Its group, the place of its kind in the order.
    fn group(&self) -> u8 {
        match self {
            Member::Number(_) => 0,
            Member::NumberType(_) => 1,
            Member::False => 2,
            Member::True => 3,
            Member::Bool => 4,
            Member::Str(_) => 5,
            Member::Named(_) => 6,
            Member::Tuple => 7,
            Member::Struct => 8,
            Member::Function => 9,
            Member::AnyAtom => 10,
            Member::Atom { .. } => 11,
            Member::Top => 12,
        }
    }
}

/// The number type a numeric literal is of.
fn carrier(v: &Value) -> NumberType {
    match v {
        Value::Rat(_) => NumberType::Rat,
        Value::Float32(_) => NumberType::F32,
        Value::Float(_) => NumberType::F64,
        _ => NumberType::Int,
    }
}

/// The order of two members of a union: by group, then within it as the module says. Two
/// members it finds equal (two tuples, two functions) keep the order they are given in, by a
/// stable sort. O(1) but for two numbers, compared exactly, and two names or strings, compared
/// by their code points.
///
/// A total preorder, as `sort_by` needs: it is the order of the pair (group, key within the
/// group), first by group, since each arm but the last takes two members of one group (only
/// `Number` is in group 0, `NumberType` in 1, `Str` in 5, `Named` in 6, `Atom` in 11) and the
/// last gives `Equal` to two of one group it has no key for. Each key is a total preorder:
/// `Ord` on `NumberType`, `Text`, `str` and `(name, payload)`; for numbers, the triple
/// (`Exact`, derived `Ord`; the carrier; `number_cmp`), where `number_cmp` is reached only
/// for two of one carrier and one place on the line, so two `Int`s, two `Big`s, two of one
/// float width (the float total order) or two `Rat`s, each a total order. Tests:
/// `groups_follow_the_decision` and `numbers_ascend_and_ties_go_int_f64_rat`.
pub fn cmp(a: &Member<'_>, b: &Member<'_>) -> Ordering {
    match (a, b) {
        (Member::Number(x), Member::Number(y)) => x
            .exact()
            .cmp(&y.exact())
            .then_with(|| carrier(x).cmp(&carrier(y)))
            .then_with(|| number_cmp(x, y)),
        (Member::NumberType(x), Member::NumberType(y)) => x.cmp(y),
        (Member::Str(x), Member::Str(y)) => x.cmp(y),
        (Member::Named(x), Member::Named(y)) => name_cmp(x, y),
        (
            Member::Atom {
                name: x,
                payload: p,
            },
            Member::Atom {
                name: y,
                payload: q,
            },
        ) => x.cmp(y).then(p.cmp(q)),
        _ => a.group().cmp(&b.group()),
    }
}

/// The order of two names (DESIGN.md sec:diagnostics, "Types in a message"): "by name in
/// code-point order with a run of digits compared as a number, so `T5` before `T10` and `Part2`
/// before `Part10`". Two names equal in that order, which differ only in a run's leading zeros
/// (`T5` and `T05`), are ordered by their code points, so two names are equal only when they
/// are one name.
///
/// A total order: each name reads as a sequence of tokens, a run of ASCII digits or one other
/// character. Two runs compare by value: by length once their leading zeros are dropped, then
/// digit by digit, which is the order of their values for any length, with no overflow. A run
/// and a character compare by the run's first digit against the character: the ten digits are
/// the consecutive code points U+0030 to U+0039, so a character other than a digit is below all
/// of them or above all of them, and this is a total preorder on tokens. Sequences of tokens in
/// the lexicographic order of a total preorder are a total preorder, and the code points break
/// its ties, which makes the order total. O(|x| + |y|). Test `digit_runs_compare_as_numbers`.
pub fn name_cmp(x: &str, y: &str) -> Ordering {
    let (a, b) = (x.as_bytes(), y.as_bytes());
    let (mut i, mut j) = (0, 0);
    /// The run of digits from `from`, its leading zeros dropped, and where it ends.
    fn run(s: &[u8], from: usize) -> (&[u8], usize) {
        let end = from + s[from..].iter().take_while(|c| c.is_ascii_digit()).count();
        let first = from + s[from..end].iter().take_while(|&&c| c == b'0').count();
        (&s[first..end], end)
    }
    while i < a.len() && j < b.len() {
        if a[i].is_ascii_digit() && b[j].is_ascii_digit() {
            let ((p, pe), (q, qe)) = (run(a, i), run(b, j));
            let o = p.len().cmp(&q.len()).then_with(|| p.cmp(q));
            if o.is_ne() {
                return o;
            }
            (i, j) = (pe, qe);
        } else {
            // Bytes of UTF-8 compare as their code points do, and a digit is one byte.
            let o = a[i].cmp(&b[j]);
            if o.is_ne() {
                return o;
            }
            (i, j) = (i + 1, j + 1);
        }
    }
    (a.len() - i).cmp(&(b.len() - j)).then_with(|| x.cmp(y))
}

/// The member a value is, as the literal type of it: its own literal for a number, a boolean,
/// a string or an atom, and its kind for a tuple, a keypath or a family.
pub fn of_value(v: &Value) -> Member<'_> {
    match v {
        Value::Int(_) | Value::Big(_) | Value::Rat(_) | Value::Float(_) | Value::Float32(_) => {
            Member::Number(v)
        }
        Value::Bool(false) => Member::False,
        Value::Bool(true) => Member::True,
        Value::Str(s) => Member::Str(s),
        Value::Atom(a) => Member::Atom {
            name: &a.name,
            payload: !a.is_bare(),
        },
        Value::Tuple(_) | Value::Path(_) => Member::Tuple,
        Value::Family(_) => Member::Function,
    }
}

/// The order in which two values print as members of a union of their literal types: by
/// [`cmp`], and two of one member, such as two atoms of one name with payloads, by the order
/// of values.
pub fn cmp_values(a: &Value, b: &Value) -> Ordering {
    cmp(&of_value(a), &of_value(b)).then_with(|| a.cmp(b))
}

/// Two sequences in the order of a union (DESIGN.md sec:diagnostics): element by element by
/// `cmp`, and a sequence that is the start of the other first. Tuples are so ordered by their
/// components, "a shorter tuple before a longer one that starts the same way", and two atoms
/// of one name by their payloads' components; a type is so ordered by its members, each list
/// sorted by [`cmp`] ([`Member`]s of `crate::types::Type::members`), which is the order of
/// two components (MSG-union-order-tuples).
///
/// The lexicographic order of a total preorder `cmp`, which is a total preorder: two
/// sequences that differ first at `i` compare as their elements at `i` do, and one that is
/// the start of the other compares by length. O(k) calls of `cmp` for the k elements of the
/// shorter. Test `sequences_compare_element_by_element_shorter_first`.
pub fn seq_cmp<T>(a: &[T], b: &[T], mut cmp: impl FnMut(&T, &T) -> Ordering) -> Ordering {
    for (x, y) in a.iter().zip(b) {
        let o = cmp(x, y);
        if o.is_ne() {
            return o;
        }
    }
    a.len().cmp(&b.len())
}

/// Sorts `items` by the member each has, stably, in O(m log m) for m items: the order a
/// union prints them in.
pub fn sort_by_member<T>(items: &mut [T], member: impl Fn(&T) -> Member<'_>) {
    items.sort_by(|a, b| cmp(&member(a), &member(b)));
}

/// The names `names`, each a type written as one name, joined by `|` in the order a union
/// prints them, each once: `f64 | rat`, `int | bool | String`.
pub fn union_of_names<'a>(names: impl IntoIterator<Item = &'a str>) -> String {
    let mut names: Vec<&str> = names.into_iter().collect();
    sort_by_member(&mut names, |n| Member::of_name(n));
    names.dedup();
    names.join(" | ")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn numbers_ascend_and_ties_go_int_f64_rat() {
        let half_rat = Value::rat(crate::num::Rat::new(1.into(), 2.into()).expect("a ratio"));
        let vs = [
            Value::Int(2),
            Value::rat(crate::num::Rat::int(1.into())),
            Value::float(1.0),
            Value::Int(1),
            half_rat,
            Value::float(f64::NEG_INFINITY),
        ];
        let mut order: Vec<&Value> = vs.iter().collect();
        sort_by_member(&mut order, |v| Member::Number(v));
        let kinds: Vec<String> = order.iter().map(|v| format!("{v:?}")).collect();
        assert!(matches!(order[0], Value::Float(_)), "{kinds:?}");
        assert!(matches!(order[1], Value::Rat(_)), "{kinds:?}");
        assert!(matches!(order[2], Value::Int(1)), "{kinds:?}");
        assert!(matches!(order[3], Value::Float(_)), "{kinds:?}");
        assert!(matches!(order[4], Value::Rat(_)), "{kinds:?}");
        assert!(matches!(order[5], Value::Int(2)), "{kinds:?}");
    }

    #[test]
    fn names_print_in_the_fixed_order() {
        assert_eq!(
            union_of_names(["String", "bool", "rat", "f64", "int", "rat"]),
            "int | f64 | rat | bool | String"
        );
        assert_eq!(
            union_of_names(["Zeta", "Alpha", "String"]),
            "Alpha | String | Zeta"
        );
        // Every name `of_name` reads: the number types in their order, then the booleans.
        assert_eq!(
            union_of_names([
                "bool", "true", "f16", "false", "rat", "bf16", "f32", "int", "f64"
            ]),
            "int | bf16 | f16 | f32 | f64 | rat | false | true | bool"
        );
    }

    /// A run of digits in a name compares as a number (DESIGN.md sec:diagnostics); before,
    /// names compared by code points alone, `T10 | T5`.
    #[test]
    fn digit_runs_compare_as_numbers() {
        assert_eq!(union_of_names(["T10", "T5", "T"]), "T | T5 | T10");
        assert_eq!(
            union_of_names(["Part10", "Part2", "Part1", "Parts"]),
            "Part1 | Part2 | Part10 | Parts"
        );
        // A long run, past any machine word, and leading zeros: by value, ties by code points.
        let long = format!("A{}", "9".repeat(40));
        let longer = format!("A1{}", "0".repeat(40));
        assert_eq!(name_cmp(&long, &longer), Ordering::Less);
        assert_eq!(name_cmp("T05", "T5"), Ordering::Less);
        assert_eq!(name_cmp("T5", "T05"), Ordering::Greater);
        assert_eq!(name_cmp("T5", "T5"), Ordering::Equal);
        assert_eq!(name_cmp("T5a", "T5"), Ordering::Greater);
        assert_eq!(name_cmp("T5", "T_"), Ordering::Less);
        // Sorted, each name is strictly below the next: no two distinct names are tied.
        let names = [
            "T", "T5", "T05", "T10", "T5a", "Ta", "U", "T_", "T1x2", "T1x10",
        ];
        let mut want = names;
        want.sort_by(|a, b| name_cmp(a, b));
        for (k, w) in want.windows(2).enumerate() {
            assert_eq!(name_cmp(w[0], w[1]), Ordering::Less, "{k}: {want:?}");
        }
        assert_eq!(
            want,
            [
                "T", "T1x2", "T1x10", "T05", "T5", "T5a", "T10", "T_", "Ta", "U"
            ]
        );
    }

    /// Sequences compare element by element, a shorter one first on a common start
    /// (MSG-union-order-tuples).
    #[test]
    fn sequences_compare_element_by_element_shorter_first() {
        let (one, two) = (Value::Int(1), Value::Int(2));
        let (int, a, b) = (
            Member::NumberType(NumberType::Int),
            Member::Atom {
                name: "a",
                payload: false,
            },
            Member::Atom {
                name: "b",
                payload: false,
            },
        );
        assert_eq!(seq_cmp(&[int, a], &[int, b], cmp), Ordering::Less);
        assert_eq!(seq_cmp(&[int, b], &[int, a], cmp), Ordering::Greater);
        assert_eq!(seq_cmp(&[int], &[int, a], cmp), Ordering::Less);
        assert_eq!(seq_cmp(&[int, a], &[int], cmp), Ordering::Greater);
        assert_eq!(seq_cmp(&[int, a], &[int, a], cmp), Ordering::Equal);
        assert_eq!(seq_cmp::<Member>(&[], &[], cmp), Ordering::Equal);
        // The first difference decides, whatever follows it.
        let (m1, m2) = (Member::Number(&one), Member::Number(&two));
        assert_eq!(seq_cmp(&[m1, b, b], &[m2, a], cmp), Ordering::Less);
    }

    /// Two literals of one value and one carrier, `-0.0` and `0.0`, are ordered by the value
    /// itself: `-0.0` first, as `f64::total_cmp` orders them.
    #[test]
    fn literals_of_one_value_and_carrier_go_by_the_value() {
        let (neg, pos) = (Value::float(-0.0), Value::float(0.0));
        assert_eq!(
            cmp(&Member::Number(&pos), &Member::Number(&neg)),
            Ordering::Greater
        );
        assert_eq!(
            cmp(&Member::Number(&neg), &Member::Number(&pos)),
            Ordering::Less
        );
        assert_eq!(
            cmp(&Member::Number(&pos), &Member::Number(&pos)),
            Ordering::Equal
        );
    }

    #[test]
    fn groups_follow_the_decision() {
        let one = Value::Int(1);
        let x = Text::from("x");
        let ms = [
            Member::Top,
            Member::Atom {
                name: "a",
                payload: true,
            },
            Member::Atom {
                name: "a",
                payload: false,
            },
            Member::AnyAtom,
            Member::Function,
            Member::Struct,
            Member::Tuple,
            Member::Named("T"),
            Member::Str(&x),
            Member::Bool,
            Member::True,
            Member::False,
            Member::NumberType(NumberType::Rat),
            Member::NumberType(NumberType::Int),
            Member::Number(&one),
        ];
        let mut sorted = ms;
        sort_by_member(&mut sorted, |m| *m);
        let mut want = ms;
        want.reverse();
        assert_eq!(format!("{sorted:?}"), format!("{want:?}"));
    }

    /// Each kind of value takes its literal type's place: the checker sorts only atoms by
    /// [`cmp_values`] (a cast whose operand fails with two), so the other kinds are read here
    /// (item TEST-types-unreached-paths).
    #[test]
    fn values_sort_as_their_literal_types() {
        let want = [
            Value::Int(1),
            Value::Bool(false),
            Value::Bool(true),
            Value::str("s"),
            Value::tuple(vec![]),
            Value::Family(crate::value::Family::new()),
            Value::atom("a"),
            Value::atom("b"),
        ];
        let mut sorted = want.clone();
        sorted.reverse();
        sorted.sort_by(cmp_values);
        assert_eq!(sorted, want);
    }
}
