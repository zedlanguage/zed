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
//! 5. named types (`String`, structs, aliases) and type variables, by name;
//! 6. tuples; then every struct, `{..}`;
//! 7. functions;
//! 8. atoms: every atom `#_` first, then by name, the bare atom before the one with a payload;
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
        Value::Float(_) => NumberType::F64,
        _ => NumberType::Int,
    }
}

/// The order of two members of a union: by group, then within it as the module says. Two
/// members it finds equal (two tuples, two functions) keep the order they are given in, by a
/// stable sort. O(1) but for two numbers, compared exactly, and two names or strings, compared
/// by their code points.
pub fn cmp(a: &Member<'_>, b: &Member<'_>) -> Ordering {
    match (a, b) {
        (Member::Number(x), Member::Number(y)) => x
            .exact()
            .cmp(&y.exact())
            .then_with(|| carrier(x).cmp(&carrier(y)))
            .then_with(|| number_cmp(x, y)),
        (Member::NumberType(x), Member::NumberType(y)) => x.cmp(y),
        (Member::Str(x), Member::Str(y)) => x.cmp(y),
        (Member::Named(x), Member::Named(y)) => x.cmp(y),
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

/// The member a value is, as the literal type of it: its own literal for a number, a boolean,
/// a string or an atom, and its kind for a tuple, a keypath or a family.
pub fn of_value(v: &Value) -> Member<'_> {
    match v {
        Value::Int(_) | Value::Big(_) | Value::Rat(_) | Value::Float(_) => Member::Number(v),
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
}
