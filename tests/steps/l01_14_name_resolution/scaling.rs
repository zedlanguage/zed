//! Name resolution at the rule of low complexity (DESIGN.md Part G).

use super::{at, errors, run};

/// Blocks nested `n` deep, each binding a name, the innermost reading the top-level `c` `n`
/// times.
fn nested(n: usize) -> String {
    let mut src = "c = 1;\nmain = ".to_string();
    for i in 0..n {
        src += &format!("{{\ny{i} = c;\n");
    }
    src += &format!("{}\n", vec!["c"; n].join(" + "));
    src += &"}\n".repeat(n);
    src + ";\n"
}

/// `k` overloads of `f`, at most 8^5: five parameters, each with no written type or one of
/// the seven types of L1, so no two have the same parameter types.
fn overloads(k: usize) -> String {
    const TYPES: [&str; 8] = [
        "", ": int", ": rat", ": f64", ": bool", ": String", ": Lines", ": Files",
    ];
    let mut src = String::new();
    for i in 0..k {
        let ps: Vec<String> = (0..5)
            .map(|j| format!("p{j}{}", TYPES[i >> (3 * j) & 7]))
            .collect();
        src += &format!("f({}) = 0;\n", ps.join(", "));
    }
    src
}

#[test]
fn names_read_inside_deeply_nested_blocks_scale() {
    // A name was looked for in each open scope in turn, innermost first.
    std::thread::Builder::new()
        .stack_size(1 << 32)
        .spawn(|| {
            zed_tests::scaling::check("names read in blocks nested n deep", 800, |n| {
                assert!(run(&nested(n)).is_ok());
            });
            assert_eq!(at(&nested(3), "c", 2), ["binding c = 1;"]);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn declaring_many_overloads_scales() {
    // Each overload's parameter types were compared with those of every one before it.
    zed_tests::scaling::check("k overloads of one function", 1000, |k| {
        assert_eq!(run(&overloads(k)).unwrap().binders.len(), 6 * k);
    });
    assert_eq!(
        errors("f(x: int) = x;\nf(y: int) = 1;\ng = 1;\ng(x) = x;\n"),
        [
            "`f` is already declared in this scope with these parameter types \
             [f(y: int) = 1;]; the first `f` with these parameter types [f(x: int) = x;]",
            "`g` is already bound in this scope [g(x) = x;]; the first binding of `g` [g = 1;]",
        ]
    );
}
