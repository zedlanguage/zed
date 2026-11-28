//! The kernel type a written type denotes, which the checker reads to check a bounded type's
//! guarantee against its permission and elaboration reads for an `is` test.

use zed_kernel::Universe;
use zed_kernel::types::Type as KType;

use zedc_syntax::ast::{Every, Type, TypeKind};
use zedc_syntax::lex::Span;

/// The kernel type a written type denotes. A function type is curried, one level per
/// parameter, and `->?` makes each level partial; `() -> V` has the empty tuple as its one key.
/// A name of a port denotes no type: it is an error in `ports`, and the type is `None`. With
/// `bounds`, each `L .. U -> V` whose guarantee `L` is not within its permission `U` is an
/// error there, with the cause when that check was refused; the checker passes it once for
/// each written type of a program (the list `Tables::written`, walked by `Ck::bounds`), so
/// every way a program is checked runs this check, and runs it once. One pass over the type.
///
/// Types nest as deep as the source, so the types still open wait on a stack, each with the
/// types of its parts so far; every part is elaborated, in written order, before the type that
/// holds it, so the errors come in the order a recursion would give (step T2-mid).
pub fn kernel_type(
    t: &Type,
    ports: &mut Vec<(Span, String)>,
    mut bounds: Option<&mut Vec<(Span, String)>>,
) -> Option<KType> {
    let mut stack = vec![OpenType::of(t)];
    loop {
        let top = stack.last_mut().expect("a type in progress");
        if let Some(&part) = top.parts.get(top.done.len()) {
            stack.push(OpenType::of(part));
            continue;
        }
        let OpenType { t, done, .. } = stack.pop().expect("a type in progress");
        let k = kernel_form(t, done, ports, bounds.as_deref_mut());
        match stack.last_mut() {
            Some(holder) => holder.done.push(k),
            None => return k,
        }
    }
}

/// The type `t` denotes, given the types of its parts in [`type_parts`] order, `None` where a
/// part was refused; the errors of [`kernel_type`] for `t` itself go to `ports` and `bounds`.
fn kernel_form(
    t: &Type,
    parts: Vec<Option<KType>>,
    ports: &mut Vec<(Span, String)>,
    bounds: Option<&mut Vec<(Span, String)>>,
) -> Option<KType> {
    Some(match &t.kind {
        TypeKind::Apply(..) | TypeKind::AtomApply(..) | TypeKind::Record(_) => {
            unreachable!(
                "name resolution rejects every record type and every type applied to \
                 arguments before a type is read"
            )
        }
        TypeKind::Local { .. } => unreachable!(
            "name resolution rejects every local part declaration of a type, of layer L2, \
             before a type is read"
        ),
        // The kernel has no list type: reading `[V]` as the arrow `int ->? V` the checker
        // denotes it by would make `f is [int]` hold for a function `f` that is no list, since
        // the kernel's arrow does not say that a list is data (LIST-type-written). Without a
        // type for it, the check that a bound's guarantee is within its permission cannot run,
        // so a list type inside `L .. U -> V` is refused there rather than passed unchecked;
        // a bound whose two sides are lists is checked through their element types
        // ([`lists_within`]).
        TypeKind::Array(_) => {
            if let Some(bounds) = bounds {
                bounds.push((t.span, LIST_IN_BOUND.to_string()));
            }
            ports.push((t.span, LIST_TEST.to_string()));
            return None;
        }
        // The kernel has no type with a range, and reading one as its base would make
        // `x is int[0..=9]` hold for 100; the checker reads a parameter's apart.
        TypeKind::Range { .. } => unreachable!(
            "name resolution rejects every range type but the whole type of a parameter, \
             which the checker reads apart, before a type is read"
        ),
        // A bounded variable stands for one carrier that a call of the function chooses; a
        // run-time test has no call to choose it.
        TypeKind::For { bounds, .. } => {
            let vars: Vec<String> = bounds.iter().map(|b| format!("`{}`", b.name)).collect();
            let (variables, each) = match vars.len() {
                1 => ("variable", "it"),
                _ => ("variables", "each one"),
            };
            ports.push((
                t.span,
                format!(
                    "this `is` test names a type with the bounded {variables} {}; a call of a \
                     function chooses which carrier of its bound {each} stands for, and a test \
                     has no call to choose it, so the test has no one type to check against. \
                     To repair it, test each carrier of the bound in turn, as `x is int`",
                    vars.join(", ")
                ),
            ));
            return None;
        }
        TypeKind::Name(n) => match n.as_str() {
            "int" => KType::int(),
            "rat" => KType::rat(),
            "f64" => KType::f64(),
            "f32" => KType::f32(),
            "bool" => KType::bool(),
            "String" => KType::string(),
            "Never" => KType::empty(),
            // A name of a type variable's form is a type variable (DESIGN sec:type_resolution,
            // rule 4), never a port's type, which this arm's last case named it before (row
            // PROOF-push-vars-other-route). A test `v is T` narrows `v` to `old & T` (DESIGN
            // sec:type_language, flow narrowing), but the kernel test runs with no call to say
            // which type `T` stands for, so this version refuses it, as it does a list type.
            n if zedc_syntax::ast::type_var_form(n) => {
                ports.push((
                    t.span,
                    format!(
                        "a test against a type variable `{n}` is part of the Zed language but \
                         is not supported by this version of zedc. Write the program without it"
                    ),
                ));
                return None;
            }
            _ => {
                ports.push((
                    t.span,
                    format!(
                        "`{n}` is the type of a port, which only a port parameter has; no value \
                         has it, so it cannot be written here. To repair it, write the type \
                         of the values the port carries, such as `String`"
                    ),
                ));
                return None;
            }
        },
        TypeKind::Every(Every::Atom) => super::ty::atoms(),
        TypeKind::Every(Every::Tuple) => KType::universe(Universe::Tuple),
        TypeKind::Every(Every::Struct) => KType::universe(Universe::Struct),
        TypeKind::AtomAny(a) => KType::atom_with(a, &KType::top()),
        TypeKind::Atom(a) => KType::atom(a),
        TypeKind::Tuple(_) => KType::tuple(parts.into_iter().collect::<Option<_>>()?),
        TypeKind::Union(_) => KType::union_all(parts.into_iter().collect::<Option<Vec<_>>>()?),
        TypeKind::And(_) => KType::meet_all(parts.into_iter().collect::<Option<Vec<_>>>()?),
        TypeKind::Diff(..) => {
            let [a, b] = <[Option<KType>; 2]>::try_from(parts).expect("two parts");
            a? - &b?
        }
        TypeKind::Arrow { partial, .. } => {
            let mut keys: Vec<KType> = parts.into_iter().collect::<Option<_>>()?;
            let result = keys.pop().expect("the result is the last part");
            if keys.is_empty() {
                keys.push(KType::tuple(Vec::new()));
            }
            let level = if *partial {
                KType::partial
            } else {
                KType::exact
            };
            keys.into_iter().rev().fold(result, |v, k| level(k, v))
        }
        TypeKind::Bounded { lower, upper, .. } => {
            if let (TypeKind::Array(a), TypeKind::Array(b)) = (&lower.kind, &upper.kind) {
                // `type_parts` gave the result alone. The whole type has no kernel type, as a
                // list has none, so a test against it is refused as one against a list is.
                if let Some(bounds) = bounds {
                    let refused = lists_within(a, b, ports, bounds);
                    bounds.extend(refused.map(|why| (t.span, why)));
                }
                ports.push((lower.span, LIST_TEST.to_string()));
                return None;
            }
            let [l, u, v] = <[Option<KType>; 3]>::try_from(parts).expect("three parts");
            let (l, u) = (l?, u?);
            if let Some(bounds) = bounds
                && let Some(why) = not_within(&l, &u)
            {
                bounds.push((t.span, why));
            }
            KType::morphism(l, u, v?)
        }
    })
}

/// The refusal of a test against a list type, which has no kernel type.
const LIST_TEST: &str = "a test against a list type `[T]` is part of the Zed language but is \
                         not supported by this version of zedc. Write the program without it";

/// The refusal of a list type inside `L .. U -> V` that is not the whole of both sides.
const LIST_IN_BOUND: &str = "a list type `[T]` inside a function type `L .. U -> V` is part of \
                             the Zed language but is not supported by this version of zedc. \
                             Write the function type without `..`, as `(…) -> …`";

/// The error for a bound whose guarantee `l` is not proved within its permission `u`, or
/// `None` where it is.
fn not_within(l: &KType, u: &KType) -> Option<String> {
    if l.subtype(u) {
        return None;
    }
    // A refused check is not a proved failure, so it is not stated as one. The headline ends
    // with the repair, and the reason stands in a note after it.
    let (found, because) = match l.subtype_verdict(u) {
        zed_kernel::types::Verdict::Refused(r) => (
            "and the checker could not decide whether this one's guarantee is within its \
             permission, so it is not proved wrong",
            crate::ty::undecided_because(&r.message()),
        ),
        _ => (
            "and in this one the guarantee allows functions the permission does not",
            String::new(),
        ),
    };
    Some(format!(
        "in a function type `L .. U -> V`, every function the guarantee `L`, left of `..`, \
         describes must also be allowed by the permission `U`, right of `..`, {found}. To \
         repair it, narrow the type left of `..`, or widen the type right of it.{because}"
    ))
}

/// The error for the bound `[a] .. [b] -> V`, or `None` where every list of `[a]` is a list of
/// `[b]` (LIST-in-bound-check). The kernel has no list type, so the two are compared through
/// their element types, by this lemma, for any types `A` and `B` and `Lists(T)` the lists
/// whose elements are each of type `T`, of any length:
///
/// `Lists(A) ⊆ Lists(B)` if and only if `A ⊆ B`.
///
/// Proof. If `A ⊆ B`, each element of a list of `Lists(A)` is of `A`, so of `B`, and the list
/// is of `Lists(B)`. If not, some `x` is of `A` and not of `B`; the list `[x]` of one element
/// is of `Lists(A)`, and it is not of `Lists(B)`, as its element is not of `B`. ∎
///
/// Applied while both element types are lists again (`[[a]] .. [[b]]`), the lemma reduces the
/// question to the innermost element types, which are compared as kernel types with the
/// check of any other bound ([`not_within`]); their bounds, if they hold any, are checked by
/// that elaboration. A list anywhere else in either side still has no kernel type and is
/// refused, as before (`LIST_IN_BOUND`): reading `[T]` as the family `int ->? T`, or as an
/// atom with a payload, is unsound there. Counterexamples: as a family, with `L = int ->? int`
/// and `U = (int ->? int) \ [int]`, the difference reads as empty and the check refuses,
/// rightly, by luck, but with `L = int ->? int` and `U = [int] | String` it accepts, though the
/// family `{5: 1}` is no list; as an atom `#list(T)`, `U = (int ->? int) \ [int]` reads as `int
/// ->? int`, so `L = int ->? int` is accepted though the list `[1]` is of `L` and not of `U`,
/// and `[#a | #b] .. [#a] | [#b]` is accepted though `[#a, #b]` is of neither list. A sound
/// reading of a list inside a union, difference or tuple needs a list type in the kernel.
///
/// O(depth of the lists written) besides the elaboration of the two element types.
fn lists_within(
    mut a: &Type,
    mut b: &Type,
    ports: &mut Vec<(Span, String)>,
    bounds: &mut Vec<(Span, String)>,
) -> Option<String> {
    while let (TypeKind::Array(x), TypeKind::Array(y)) = (&a.kind, &b.kind) {
        (a, b) = (&**x, &**y);
    }
    let l = kernel_type(a, ports, Some(bounds));
    let u = kernel_type(b, ports, Some(bounds));
    match (l, u) {
        (Some(l), Some(u)) => not_within(&l, &u),
        // The element type that has none was refused where it was read (a list in it, or a
        // name of a port).
        _ => None,
    }
}

/// A type expression being elaborated by [`kernel_type`]: its parts and the types of those done.
struct OpenType<'t> {
    t: &'t Type,
    parts: Vec<&'t Type>,
    done: Vec<Option<KType>>,
}

impl<'t> OpenType<'t> {
    fn of(t: &'t Type) -> Self {
        Self {
            t,
            parts: type_parts(t),
            done: Vec::new(),
        }
    }
}

/// The parts of `t` that [`kernel_form`] takes the types of, in the order the source writes
/// them: a function type's parameters, then its result.
fn type_parts(t: &Type) -> Vec<&Type> {
    match &t.kind {
        TypeKind::Tuple(ts) | TypeKind::Union(ts) | TypeKind::And(ts) => ts.iter().collect(),
        TypeKind::Diff(a, b) => vec![a, b],
        TypeKind::Arrow { params, result, .. } => {
            params.iter().map(|p| &p.ty).chain([&**result]).collect()
        }
        TypeKind::Bounded {
            lower,
            upper,
            result,
        } => match (&lower.kind, &upper.kind) {
            // Two lists are compared element type with element type in `kernel_form`
            // ([`lists_within`]): neither has a kernel type.
            (TypeKind::Array(_), TypeKind::Array(_)) => vec![result],
            _ => vec![lower, upper, result],
        },
        TypeKind::Name(_)
        | TypeKind::Atom(_)
        | TypeKind::Every(_)
        | TypeKind::AtomAny(_)
        | TypeKind::Apply(..)
        | TypeKind::AtomApply(..)
        | TypeKind::Record(_)
        | TypeKind::Array(_)
        | TypeKind::Range { .. }
        | TypeKind::For { .. }
        | TypeKind::Local { .. } => Vec::new(),
    }
}
