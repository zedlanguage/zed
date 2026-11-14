//! The scaling of unions of pinwheels whose ends are atom payloads or one-tuples, with the
//! third end of the last pinwheel cofinite (item T6-payload-pinwheel; test audit 2026-11-08,
//! which found the cofinite case held for correctness only). The pinwheel and its ends are
//! built as in `scaling.rs`, kept apart here so that file is not edited by two items at once.

use std::collections::HashMap;
use zed_kernel::Value;
use zed_kernel::types::{Type, Verdict};
use zed_tests::scaling;

fn lit(i: i64) -> Type {
    Type::lit(&Value::Int(i)).unwrap()
}

/// The pinwheel on `ends`: the square of them less four boxes around its middle
/// `(ends[1], ends[1])`, and less the middle too when `full`, which makes it empty.
fn pinwheel(full: bool, ends: [Type; 3]) -> Type {
    let set = |m: u8| Type::union_all((0..3).filter(|i| m >> i & 1 == 1).map(|i| ends[i].clone()));
    let boxes: &[[u8; 2]] = match full {
        false => &[[3, 1], [4, 3], [6, 4], [1, 6]],
        true => &[[3, 1], [4, 3], [6, 4], [1, 6], [2, 2]],
    };
    let square = Type::tuple(vec![set(7); 2]);
    &square
        - &Type::union_all(
            boxes
                .iter()
                .map(|b| Type::tuple(b.iter().map(|&m| set(m)).collect())),
        )
}

/// The union of `k` pinwheels whose ends are `wrap` of the integers `10 i + 1`, `10 i + 2` and
/// `10 i + 3`, with the third end of the last pinwheel cofinite: its own integer and every
/// integer no pinwheel uses.
fn cofinite_pinwheels(k: i64, full: bool, wrap: fn(Type) -> Type) -> Type {
    let used = Type::union_all((0..k).flat_map(|i| (1..=3).map(move |j| lit(10 * i + j))));
    Type::union_all((0..k).map(|i| {
        let [a, b, c] = [1, 2, 3].map(|j| lit(10 * i + j));
        let c = match i == k - 1 {
            true => &(&Type::int() - &used) | &c,
            false => c,
        };
        pinwheel(full, [a, b, c].map(wrap))
    }))
}

fn payload(t: Type) -> Type {
    Type::atom_with("e", &Type::tuple(vec![t]))
}

fn one_tuple(t: Type) -> Type {
    Type::tuple(vec![t])
}

mod bench;
