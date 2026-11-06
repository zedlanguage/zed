//! The kernel type a written type denotes, which the checker reads to check a bounded type's
//! guarantee against its permission and elaboration reads for an `is` test.

use zed_kernel::Universe;
use zed_kernel::types::Type as KType;

use crate::ast::{Every, Type, TypeKind};
use crate::lex::Span;

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
pub(crate) fn kernel_type(
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
            unreachable!("resolve rejects the forms of layer L2")
        }
        TypeKind::Array(_) => unreachable!("resolve rejects the forms of layer L3"),
        // A bounded variable stands for one carrier that a call of the function chooses; a
        // run-time test has no call to choose it.
        TypeKind::For { bounds, .. } => {
            let vars: Vec<String> = bounds.iter().map(|b| format!("`{}`", b.name)).collect();
            ports.push((
                t.span,
                format!(
                    "an `is` test cannot take a type with bounded variables ({}): a call \
                     chooses each one's carrier, and a test has no call; test each carrier \
                     instead",
                    vars.join(", ")
                ),
            ));
            return None;
        }
        TypeKind::Name(n) => match n.as_str() {
            "int" => KType::int(),
            "rat" => KType::rat(),
            "f64" => KType::f64(),
            "bool" => KType::bool(),
            "String" => KType::string(),
            _ => {
                ports.push((
                    t.span,
                    format!("`{n}` is the type of a port, and no value has it"),
                ));
                return None;
            }
        },
        TypeKind::Every(Every::Atom) => crate::check::ty::atoms(),
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
        TypeKind::Bounded { .. } => {
            let [l, u, v] = <[Option<KType>; 3]>::try_from(parts).expect("three parts");
            let (l, u) = (l?, u?);
            if let Some(bounds) = bounds
                && !l.subtype(&u)
            {
                let why = match l.subtype_verdict(&u) {
                    zed_kernel::types::Verdict::Refused(r) => {
                        format!(" (not decided: {})", r.message())
                    }
                    _ => String::new(),
                };
                bounds.push((
                    t.span,
                    format!(
                        "the guarantee (left of `..`) of this morphism type is not within its \
                         permission (right of `..`){why}"
                    ),
                ));
            }
            KType::morphism(l, u, v?)
        }
    })
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
        } => vec![lower, upper, result],
        TypeKind::Name(_)
        | TypeKind::Atom(_)
        | TypeKind::Every(_)
        | TypeKind::AtomAny(_)
        | TypeKind::Apply(..)
        | TypeKind::AtomApply(..)
        | TypeKind::Record(_)
        | TypeKind::Array(_)
        | TypeKind::For { .. } => Vec::new(),
    }
}
