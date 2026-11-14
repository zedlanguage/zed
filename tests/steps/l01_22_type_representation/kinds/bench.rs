//! The benchmarks of `kinds.rs`, run by `tools/run_tests.sh --bench` and left out of its
//! default run (TEST-bench-move-l0123, author P169). Each check they make besides the ratio
//! has a small instance among the correctness tests of `kinds.rs`.

use super::*;

#[test]
fn a_union_of_kind_wide_and_exact_members_scales() {
    // Building, printing and reading back the union is O(n log n) in its members.
    scaling::check("a union of kind-wide and exact members", 256, |n| {
        let t = mixed(n);
        let s = t.surface();
        assert!(s.exact);
        let back = ty(&s.to_string());
        assert!(back.subtype(&Ty::set(t)));
    });
}

#[test]
fn narrowing_tuple_shapes_by_a_kind_wide_type_scales() {
    // `is` and `is not` against a kind-wide part read each shape once against it.
    scaling::check("narrowing n tuple shapes by (..) \\ (0, 0)", 256, |n| {
        let (t, w) = shapes(n);
        let met = t.meet(&w);
        assert_eq!(met.tuples.len(), n - 1);
        let left = t.diff(&w);
        assert_eq!(left.tuples.len(), 1);
    });
}

#[test]
fn the_function_part_of_a_kind_wide_part_is_found_in_linear_time() {
    // `Ty::held_wide` walks the tuple types its set keeps (COMPLEXITY.md K103), each node
    // once: n tuple types `(int, (i, #a))` less `(i, (i, #a))`, which hold data, and the same
    // with `(..)` in place of `#a` in the last, which holds a function; and a pair nested n
    // deep whose two components are one node, which has 2^n paths and n nodes.
    let int = Type::int;
    let tuples = Type::universe(Universe::Tuple);
    scaling::check("the function part of n tuple types", 256, |n| {
        assert_eq!(wide_rows(n, Type::atom("a")).held_wide(), None);
        assert_eq!(
            wide_rows(n, tuples.clone()).held_wide(),
            Some(tuples.clone())
        );
    });
    scaling::check("the function part of a pair nested n deep", 256, |n| {
        assert_eq!(pair_nested(n, int()).held_wide(), None);
        assert_eq!(
            pair_nested(n, &int() | &tuples).held_wide(),
            Some(tuples.clone())
        );
    });
    // `((..), int)` taken away from `(..)` n times, met with `(int, int | #a)`, which holds no
    // function, and with `(int | (..), int)`, which holds one when n is even and the tuple type
    // is kept.
    let shape = Type::tuple(vec![int(), &int() | &Type::atom("a")]);
    let kept = Type::tuple(vec![&int() | &tuples, int()]);
    scaling::check(
        "the function part of a tuple type taken away n times",
        256,
        |n| {
            assert_eq!(Ty::set(&shape & &taken_away(n)).held_wide(), None);
            let want = (n % 2 == 0).then(|| tuples.clone());
            assert_eq!(Ty::set(&kept & &taken_away(n)).held_wide(), want);
        },
    );
    // The exclusive or of n tuple types `(i, int)`, which hold data, and of the same with a
    // last `(n, (..))`, which holds a function: an expression each of whose nodes a path to
    // `true` reaches both kept and taken away, so 2^n paths and n nodes.
    scaling::check(
        "the function part of the exclusive or of n tuple types",
        256,
        |n| {
            assert_eq!(parity(n, int()).held_wide(), None);
            assert_eq!(parity(n, tuples.clone()).held_wide(), Some(tuples.clone()));
        },
    );
}

#[test]
fn payloads_of_many_atoms_are_compared_in_the_size_of_the_union() {
    // `#a0(0) | … | #a(n-1)(n-1)` against `#ai(int)` for each name, and against the same with
    // `#a0(String)`: the listed names are taken out and put back in one union each.
    scaling::check("payloads of n atoms against n atoms", 256, |n| {
        let each = |f: &dyn Fn(usize) -> Ty| -> Ty {
            let ts: Vec<Ty> = (0..n)
                .map(|i| with_payloads(&format!("a{i}"), vec![vec![f(i)]]))
                .collect();
            Ty::union_all(&ts)
        };
        let small = each(&int);
        let wide = each(&|_| ty("int"));
        let other = each(&|i| if i == 0 { ty("String") } else { ty("int") });
        assert!(small.subtype(&wide));
        assert!(!small.subtype(&other));
    });
}

#[test]
fn many_payloads_of_one_atom_are_compared_in_the_size_of_the_union() {
    // `#a(0, 0) | … | #a(n-1, n-1)` against itself and `#a(n, n)`: each payload tried against
    // each would be n² component checks; the kernel reads both unions once.
    scaling::check("n payloads of one atom against n + 1", 256, |n| {
        let pairs = |m: usize| with_payloads("a", (0..m).map(|i| vec![int(i), int(i)]).collect());
        let (small, big) = (pairs(n), pairs(n + 1));
        assert!(small.subtype(&big));
        assert!(!big.subtype(&small));
    });
}

#[test]
fn a_kind_wide_part_deep_in_tuples_is_found_once() {
    // `((…((..), 0)…), 0)`, n deep: each row keeps the kind-wide part its components hold, so
    // finding it reads one row, and building the type reads each row once.
    scaling::check("a kind-wide part n tuples deep", 256, |n| {
        let mut t = ty("(..)");
        for _ in 0..n {
            t = Ty::tuple(vec![t, int(0)]);
        }
        assert!(!t.first_order());
    });
}

#[test]
fn payloads_that_hold_functions_are_compared_in_the_size_of_the_union() {
    // `#a0((int) -> #r0, 0) | … ` against the same with `(int) -> #r_i | #s` and `int`: one
    // function on each side at each place, so each is compared once; trying each payload
    // against each was n² comparisons (A6, 2026-11-08).
    let union = |n: usize, f: &dyn Fn(usize) -> String| {
        let parts: Vec<String> = (0..n).map(|i| format!("#a{i}({})", f(i))).collect();
        ty(&parts.join(" | "))
    };
    let inputs = scaling::inputs(256, |n| {
        (
            union(n, &|i| format!("(int) -> #r{i}, {i}")),
            union(n, &|i| format!("(int) -> #r{i} | #s, int")),
            union(n, &|i| format!("(int) -> #s, {i}")),
        )
    });
    scaling::check("n payloads that hold functions against n", 256, |n| {
        let (small, wide, other) = &inputs[&n];
        assert!(small.subtype(wide));
        assert!(!small.subtype(other));
    });
    // One atom: `#a((int) -> int, 0) | …` against the same payloads in the other order, and
    // against them with `String` results, all of one length, which trying each payload against
    // each of its length compared in `n²`.
    let one = |n: usize, order: &dyn Fn(usize) -> usize, r: &str| {
        let parts: Vec<String> = (0..n)
            .map(|i| format!("#a((int) -> {r}, {})", order(i)))
            .collect();
        ty(&parts.join(" | "))
    };
    let inputs = scaling::inputs(256, |n| {
        (
            one(n, &|i| i, "int"),
            one(n, &|i| n - 1 - i, "int"),
            one(n, &|i| n - 1 - i, "String"),
        )
    });
    scaling::check(
        "n payloads of one atom that hold functions against n",
        256,
        |n| {
            let (small, same, other) = &inputs[&n];
            assert!(small.subtype(same));
            assert!(!small.subtype(other));
        },
    );
}

#[test]
fn payloads_with_fields_and_tuples_that_hold_functions_are_compared_in_the_size_of_the_union() {
    // `#a(x: 0, f: (int) -> int) | … | #a(x: n-1, …)` against `#a(x: int, f: (int) -> int)`,
    // and `(#a0 | … | #a(n-1), (int) -> int)` against the n shapes `(#a_i, (int) -> int)`,
    // which hold it only together (K38).
    let inputs = scaling::inputs(256, |n| {
        let fields: Vec<String> = (0..n)
            .map(|i| format!("#a(x: {i}, f: (int) -> int)"))
            .collect();
        let atoms: Vec<String> = (0..n).map(|i| format!("#a{i}")).collect();
        let shapes: Vec<String> = atoms
            .iter()
            .map(|a| format!("({a}, (int) -> int)"))
            .collect();
        (
            ty(&fields.join(" | ")),
            ty(&format!("({}, (int) -> int)", atoms.join(" | "))),
            ty(&shapes.join(" | ")),
        )
    });
    let whole = ty("#a(x: int, f: (int) -> int)");
    let not = ty("#a(x: int, f: (int) -> String)");
    scaling::check("n payloads with fields that hold functions", 256, |n| {
        let (fields, _, _) = &inputs[&n];
        assert!(fields.subtype(&whole));
        assert!(!fields.subtype(&not));
    });
    scaling::check(
        "a tuple that holds a function, held by n shapes",
        256,
        |n| {
            let (_, tuple, shapes) = &inputs[&n];
            assert!(tuple.subtype(shapes));
        },
    );
}

#[test]
fn payloads_with_a_variable_are_searched_by_their_keys() {
    // `#a(String, 0) | … | #a(String, n-1)` against `#a(T, n-1) | … | #a(T, 0)`: each payload
    // is found by its second component, not tried against each shape before it (n²).
    let inputs = scaling::inputs(256, |n| {
        let l = with_payloads("a", (0..n).map(|i| vec![ty("String"), int(i)]).collect());
        let r = with_payloads("a", (0..n).rev().map(|i| vec![var("T"), int(i)]).collect());
        let wrong = with_payloads("a", (0..=n).map(|i| vec![ty("String"), int(i)]).collect());
        (l, r, wrong)
    });
    scaling::check("n payloads with a variable against n", 256, |n| {
        let (l, r, wrong) = &inputs[&n];
        assert_eq!(bound(l, r), Some(vec![("T".into(), "String".into())]));
        assert_eq!(bound(wrong, r), None);
        assert_eq!(wrong.refused(r), "");
    });
}

#[test]
fn tuples_with_a_variable_are_searched_by_their_keys() {
    // The same with tuples: `(String, i)` against `(T, i)` in the reverse order.
    let inputs = scaling::inputs(256, |n| {
        let l: Vec<Ty> = (0..n)
            .map(|i| Ty::tuple(vec![ty("String"), int(i)]))
            .collect();
        let r: Vec<Ty> = (0..n)
            .rev()
            .map(|i| Ty::tuple(vec![var("T"), int(i)]))
            .collect();
        (Ty::union_all(&l), Ty::union_all(&r))
    });
    scaling::check("n tuples with a variable against n", 256, |n| {
        let (l, r) = &inputs[&n];
        assert_eq!(bound(l, r), Some(vec![("T".into(), "String".into())]));
    });
}

#[test]
fn a_refused_bucket_of_long_shapes_that_repeat_a_variable_prints_in_linear_time() {
    // Pairs grown to `n` components, `T` at each place after the first: each text of the
    // message is printed once, in one walk of its type, so the refusal grows with `n`.
    let row = |head: Ty, rest: &dyn Fn() -> Ty, n: usize| {
        Ty::tuple(
            std::iter::once(head)
                .chain((1..n).map(|_| rest()))
                .collect(),
        )
    };
    let inputs = scaling::inputs(256, |n| {
        let l = Ty::union_all(&[row(int(3), &|| int(5), n), row(int(4), &|| int(6), n)]);
        let r = Ty::union_all(&[
            row(ty("1 | 2"), &|| var("T"), n),
            row(ty("int"), &|| var("T"), n),
        ]);
        let bucket = format!("(1 | 2{ts}) | (int{ts})", ts = ", T".repeat(n - 1));
        (l, r, bucket)
    });
    scaling::check("a refused bucket of two shapes of n components", 256, |n| {
        let (l, r, bucket) = &inputs[&n];
        let why = l.refused(r);
        assert!(
            why.contains(&format!("one of the shapes {bucket}, which")),
            "{why}"
        );
    });
}

#[test]
fn subtracting_tuples_scales() {
    // `t \ u` as `is not` narrows: each tuple of `t` is compared with the tuples of `u` that
    // may share a value with it, found by key lookup.
    let inputs = scaling::inputs(256, tuple_families);
    scaling::check("n tuples without n tuples, four ways", 256, |n| {
        for (what, t, u, left, _) in &inputs[&n] {
            assert_eq!(t.diff(u).tuples.len(), *left, "{what}");
        }
    });
}

#[test]
fn meeting_tuples_scales() {
    // `t` meet `u` as `is` narrows: each tuple of `t` is met with the tuples of `u` that may
    // share a value with it, found by key lookup; the tuples met are as many as the pairs.
    let inputs = scaling::inputs(256, tuple_families);
    scaling::check("n tuples met with n tuples, four ways", 256, |n| {
        for (what, t, u, _, met) in &inputs[&n] {
            let m = t.meet(u);
            // A tuple met twice, `(bool, i)` with `(true, i)` and `(false, i)`, gives two.
            let met = if *what == "together" { 2 * met } else { *met };
            assert_eq!(m.tuples.len(), met, "{what}");
        }
    });
}

#[test]
fn meeting_and_subtracting_tuples_of_many_patterns_costs_the_patterns() {
    // Tuples are filed by their arrangement of points, classes and components of no class, and
    // each arrangement of one side is looked up once in each of the other: two arrangements,
    // as `(i, int) | (int, n + i)`, cost O(n log n) for the points `(i, n + i)`, though each
    // place alone has `n` tuples that hold any value there.
    let inputs = scaling::inputs(256, two_patterns);
    scaling::check("n points against n tuples of two arrangements", 256, |n| {
        let (points, open) = &inputs[&n];
        assert!(points.diff(open).tuples.is_empty());
        assert_eq!(points.meet(open).tuples.len(), n);
        assert_eq!(open.meet(points).tuples.len(), n);
    });
    // Complexity tradeoff (COMPLEXITY.md F127): as many arrangements as tuples cost the
    // product of the two sides, which no algorithm avoids unless the strong exponential time
    // hypothesis fails (the comment at `Near` in `zedc_types::ty`).
    let inputs = scaling::inputs(64, many_patterns);
    scaling::check_order("n tuples against n of n arrangements", 64, 2, |n| {
        let (ones, zeros) = &inputs[&n];
        let met = ones.meet(zeros).tuples.len();
        assert!(met <= n * n, "{met}");
        let left = ones.diff(zeros).tuples.len();
        assert!(left <= n, "{left}");
    });
}

#[test]
fn meets_of_many_tuples_scales() {
    // Each tuple of one side is compared only with the tuples of the other that agree with it
    // at every place where both have a class or a value, found by key lookup.
    let inputs = scaling::inputs(256, meets_families);
    scaling::check("n tuples against n tuples, meets, four ways", 256, |n| {
        for (what, t, u, shares) in &inputs[&n] {
            assert_eq!(t.meets(u), *shares, "{what}");
            assert_eq!(u.meets(t), *shares, "{what}");
        }
    });
}

#[test]
fn meets_of_tuples_of_many_patterns_costs_the_patterns() {
    // Complexity tradeoff (COMPLEXITY.md F132): as many arrangements as tuples cost up to the
    // product of the two sides; whether any pair shares a value is the orthogonal vectors
    // problem, which no algorithm decides faster unless the strong exponential time hypothesis
    // fails (the comment at `Near` in `zedc_types::ty`).
    let inputs = scaling::inputs(64, |n| {
        let (ones, zeros) = many_patterns(n);
        let shares = !ones.meet(&zeros).tuples.is_empty();
        (ones, zeros, shares)
    });
    scaling::check_order("n tuples against n of n arrangements, meets", 64, 2, |n| {
        let (ones, zeros, shares) = &inputs[&n];
        assert_eq!(ones.meets(zeros), *shares);
    });
}

#[test]
fn contains_of_many_tuples_scales() {
    // Each component of the value is looked for only in the tuples of the union that agree
    // with it at every place where they have a class or a value, found by key lookup.
    let inputs = scaling::inputs(256, contains_families);
    scaling::check(
        "n tuple values in n tuples, contains, four ways",
        256,
        |n| {
            for (what, t, v, held) in &inputs[&n] {
                assert_eq!(t.contains(v), *held, "{what}");
            }
        },
    );
}

#[test]
fn contains_of_tuples_of_many_patterns_costs_the_patterns() {
    // Complexity tradeoff (COMPLEXITY.md F133): as many arrangements as tuples cost up to the
    // product of the tuples and the values; whether a tuple holds a value is the orthogonal
    // vectors problem, which no algorithm decides faster unless the strong exponential time
    // hypothesis fails (the comment at `Holders` in `zedc_types::ty`).
    let inputs = scaling::inputs(128, arrangements);
    scaling::check_order(
        "n tuple values in n tuples of n arrangements",
        128,
        2,
        |n| {
            let (t, v) = &inputs[&n];
            assert!(t.contains(v));
        },
    );
}

#[test]
fn the_meet_of_many_payloads_of_one_atom_scales() {
    // The payloads of the two sides are filed by the class or value of each component, as
    // tuples are, so the meet of n shapes with n shapes meets the n pairs that share a value
    // and not all n² (READ-atom-meet).
    let inputs = scaling::inputs(256, payload_pairs);
    scaling::check(
        "the meet of n payloads of #a with n payloads of #a",
        256,
        |n| {
            let (l, r) = &inputs[&n];
            let met = l.meet(r);
            assert!(met.subtype(l) && l.subtype(&met));
        },
    );
}

#[test]
fn the_difference_of_many_payloads_of_one_atom_scales() {
    // Each shape of the left side is compared with the shapes of the right side that may share
    // a value with it, found as for the meet, so n shapes less n shapes costs n comparisons of
    // one shape with one, not n comparisons with n (READ-atom-meet).
    let inputs = scaling::inputs(256, payload_pairs);
    scaling::check(
        "the difference of n payloads of #a and n payloads of #a",
        256,
        |n| {
            let (l, r) = &inputs[&n];
            assert!(l.diff(r).is_empty());
        },
    );
}

#[test]
fn the_difference_of_many_wide_tuple_types_scales() {
    // Each tuple type of the left side that the right side holds in part loses what the right
    // side's tuple types near it hold, found as for the meet: n tuple types less n costs n
    // differences of one tuple type with one, not n with n (FIX-ty-diff-wide-row).
    let inputs = scaling::inputs(256, wide_pairs);
    scaling::check(
        "the difference of n tuple types (i, (..)) and n tuple types (i, (int, int))",
        256,
        |n| {
            let (l, r) = &inputs[&n];
            assert!(!l.diff(r).is_empty());
        },
    );
}

#[test]
fn a_refused_bucket_of_tuples_of_many_functions_prints_in_linear_time() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    // Tuples of the bucket grown to `n` functions: each is put back once for each text that
    // prints it, so the message grows with `n`.
    let inputs = scaling::inputs(64, bucket_of_functions);
    scaling::check("a refused bucket of tuples of n functions", 64, |n| {
        let (src, shapes) = &inputs[&n];
        let errors = type_errors(src);
        assert!(
            errors.len() == 1 && errors[0].contains(shapes.as_str()),
            "{errors:?}"
        );
    });
}

#[test]
fn function_types_nested_deep_whose_variables_share_names_across_the_two_fit_in_linear_time() {
    use zed_tests::step_helpers::l01_26_type_resolution::type_errors;
    // Level `k` from the inside of `g`'s type binds `A{k}_0` to `A{k}_7`, of `f`'s type
    // `A{k + 1}_0` to `A{k + 1}_7`: the same type up to the names, each variable held by a
    // parameter. The comparison of the two levels `k` meets the names of `f`'s, which the
    // comparison around it, of the levels `k + 1`, may already read as themselves for `g`'s,
    // and then gives them new names. The type fits at every depth, as it does without the
    // clash. Eight variables a level make a search of the names kept, instead of their count,
    // cost the square of the depth times 64.
    let inputs = scaling::inputs(256, |n| {
        format!(
            "p(f: {}) = 0;\nq(g: {}) = p(f: g);\n",
            nested_functions(n, 1),
            nested_functions(n, 0)
        )
    });
    scaling::check(
        "function types nested n deep, names shared across",
        256,
        |n| {
            assert_eq!(type_errors(&inputs[&n]), Vec::<String>::new());
        },
    );
}
