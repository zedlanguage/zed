//! Elaboration at the rule of low complexity (DESIGN.md Part G).

use super::{elab, term, value};

/// `f0(x = 1) = x;` and `f{i}(x = f{i-1}() + f{i-1}()) = x;` up to `k`, and `main = f{k}();`.
fn chain(k: usize) -> String {
    let mut src = "f0(x = 1) = x;\n".to_string();
    for i in 1..=k {
        src += &format!("f{i}(x = f{j}() + f{j}()) = x;\n", j = i - 1);
    }
    src + &format!("main = f{k}();\n")
}

#[test]
fn defaults_calling_functions_with_defaults_scale() {
    // A call leaving a parameter out held a copy of its default, and the copy's own calls
    // copies of theirs, so the chain's term doubled with each function (2.9 million
    // characters for `main` at `k = 16`).
    zed_tests::scaling::check("a chain of defaults, by length", 8, |k| {
        let u = elab(&chain(k)).unwrap();
        let main = u.defs.iter().find(|d| d.name == "main").unwrap();
        assert!(main.term.to_string().len() < 40, "{}", main.term);
    });
    assert_eq!(value(&chain(3), "main"), "8");
    assert_eq!(term(&chain(3), "main"), "{ x@4 = f3$x@4(); f3(x@4) }");
    assert_eq!(
        term(&chain(3), "f3$x@4"),
        "() -> ({ x@3 = f2$x@3(); f2(x@3) } + { x@3 = f2$x@3(); f2(x@3) })"
    );
}

#[test]
fn a_compound_default_reads_the_parameters_it_names() {
    let src = "area(positional w, h = w + 1) = w * h;\na = area(3);\nb = area(3, h: 2);\n";
    assert_eq!(value(src, "a"), "12");
    assert_eq!(value(src, "b"), "6");
    assert_eq!(term(src, "a"), "{ w = 3; h = area$h(w); area(w, h) }");
    assert_eq!(term(src, "area$h"), "w -> (w + 1)");
}

/// The order `topo` gave before it kept the ready items in a heap: the first ready item by
/// index, found by a scan of all of them, at each step.
fn topo_by_scan(deps: &[Vec<usize>]) -> Result<Vec<usize>, Vec<usize>> {
    let n = deps.len();
    let mut done = vec![false; n];
    let mut order = Vec::new();
    while order.len() < n {
        match (0..n).find(|&i| !done[i] && deps[i].iter().all(|&d| done[d])) {
            Some(i) => {
                done[i] = true;
                order.push(i);
            }
            None => {
                let mut seen = std::collections::BTreeMap::new();
                let mut path = Vec::new();
                let mut i = (0..n).find(|&i| !done[i]).unwrap();
                while !seen.contains_key(&i) {
                    seen.insert(i, path.len());
                    path.push(i);
                    i = *deps[i].iter().find(|&&d| !done[d]).unwrap();
                }
                return Err(path.split_off(seen[&i]));
            }
        }
    }
    Ok(order)
}

#[test]
fn the_dependency_order_is_the_first_ready_by_index() {
    let mut x: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut next = |m: usize| {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        (x % m as u64) as usize
    };
    let (mut orders, mut cycles) = (0, 0);
    for _ in 0..2000 {
        let n = 1 + next(12);
        let deps: Vec<Vec<usize>> = (0..n)
            .map(|_| (0..next(3)).map(|_| next(n)).collect())
            .collect();
        let want = topo_by_scan(&deps);
        match &want {
            Ok(_) => orders += 1,
            Err(_) => cycles += 1,
        }
        assert_eq!(zedc::elab::topo(&deps), want, "{deps:?}");
    }
    assert!(
        orders > 200 && cycles > 200,
        "{orders} orders, {cycles} cycles"
    );
}

#[test]
fn the_dependency_order_scales() {
    // Each item waits on the next, so the scan for the first ready item passed every item
    // before it: `n²/2` steps.
    zed_tests::scaling::check("a reversed chain of dependencies, by length", 4000, |n| {
        let deps: Vec<Vec<usize>> = (0..n)
            .map(|i| if i + 1 < n { vec![i + 1] } else { Vec::new() })
            .collect();
        assert_eq!(zedc::elab::topo(&deps).unwrap()[0], n - 1);
    });
}

/// Functions nested `n` deep, each declaring a local and the next function, which it calls.
fn nested(n: usize) -> String {
    let mut src = String::new();
    for i in 0..n {
        src += &format!("f{i}(positional x) {{\ny{i} = x + 1;\n");
    }
    src += "x\n";
    for i in (0..n).rev() {
        if i + 1 < n {
            src += &format!("f{}(y{i})\n", i + 1);
        }
        src += "}\n";
    }
    src + "main = f0(1);\n"
}

/// Functions nested `n` deep, each declaring `w` functions beside the next, and calling one.
fn wide(n: usize, w: usize) -> String {
    let mut src = String::new();
    for i in 0..n {
        src += &format!("f{i}(positional x) {{\n");
        for j in 0..w {
            src += &format!("g{i}_{j}(positional z) = z;\n");
        }
        src += &format!("y{i} = g{i}_0(x) + 1;\n");
    }
    src += "x\n";
    for i in (0..n).rev() {
        if i + 1 < n {
            src += &format!("f{}(y{i})\n", i + 1);
        }
        src += "}\n";
    }
    src + "main = f0(1);\n"
}

/// The type of `main` in `src` and the signature of `f{last}`, which a search stopped by
/// its budget does not find.
fn found(src: &str, last: usize) -> (Option<String>, Option<String>) {
    let (i, names) = crate::l01_26_type_resolution::info(src);
    assert!(i.errors.is_empty(), "{:?}", i.errors);
    let name = format!("f{last}");
    let sig = i.sigs.iter().find(|(id, _)| names[**id] == name);
    (
        i.tops.get("main").map(|t| t.to_string()),
        sig.map(|(_, s)| s.to_string()),
    )
}

#[test]
fn checking_and_ordering_nested_functions_scales() {
    // Each scope ordered its statements by the uses inside them, those of the scopes nested
    // in them too, so a use was read once for each scope around it. Each run of a signature
    // search checked the functions declared inside it again, so the runs multiplied with the
    // depth; and once found, a nested function's writes were made again at each finding.
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            zed_tests::scaling::check("functions nested n deep", 100, |n| {
                let u = elab(&nested(n)).unwrap();
                assert!(u.defs.iter().any(|d| d.name == "main"));
            });
            assert_eq!(value(&nested(3), "main"), "3");
            let want = (Some("int".to_string()), Some("(int) -> int".to_string()));
            assert_eq!(found(&nested(3), 2), want);
            assert_eq!(found(&nested(100), 99), want);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn checking_nested_functions_beside_many_others_scales() {
    // A nested function's writes were made again each time its signature was found again,
    // the writes of the functions inside it too.
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            zed_tests::scaling::check("functions nested n deep beside 20 others", 50, |n| {
                assert_eq!(found(&wide(n, 20), n - 1).0.as_deref(), Some("int"));
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn ordering_a_function_with_many_rows_scales() {
    // Each use in a row was tested against every row of the function.
    zed_tests::scaling::check("a function with n rows naming a constant", 250, |n| {
        let rows: Vec<String> = (0..n).map(|_| "c -> c".to_string()).collect();
        let src = format!("c = 2;\nf(x) = x test {{ {} }}\n", rows.join(", "));
        let u = elab(&src).unwrap();
        assert_eq!(u.tests.len(), n);
    });
}

/// Functions nested `n` deep, each with a parameter of no declared type, the innermost
/// adding all of them.
fn open(n: usize) -> String {
    let mut src = String::new();
    for i in 0..n {
        src += &format!("f{i}(positional x{i}) {{\n");
    }
    let xs: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    src += &format!("{}\n", xs.join(" + "));
    for i in (0..n).rev() {
        if i + 1 < n {
            src += &format!("f{}(x{i})\n", i + 1);
        }
        src += "}\n";
    }
    src + "main = f0(1);\n"
}

#[test]
fn searches_through_nested_functions_scale() {
    // Each run of a search checks the functions declared in its body again, in a context
    // that is new whenever they read the parameter it searches: the innermost function's
    // signature depends on the type of every parameter around it. Each search runs its body
    // at least twice, with `_` and with type variables, so the contexts, all distinct, grew
    // about 1.6 times with each level, until the budget stopped them (167 s at 32 deep). A
    // function is now searched in at most `CONTEXTS` contexts, and gives `_` in the rest.
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            zed_tests::scaling::check("searches through n nested functions", 8, |n| {
                elab(&open(n)).unwrap();
            });
            assert_eq!(value(&open(4), "main"), "4");
            let int = (Some("int".to_string()), Some("(int) -> int".to_string()));
            assert_eq!(found(&open(6), 5), int);
            // At 8 deep, the context that types `x7` as int is past the first 64.
            let unknown = (Some("_".to_string()), Some("(_) -> _".to_string()));
            assert_eq!(found(&open(8), 7), unknown);
        })
        .unwrap()
        .join()
        .unwrap();
}
