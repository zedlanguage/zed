//! Name-resolution helpers of step L1.14 (tests/steps/l01_14_name_resolution).

/// `k` overloads of `f`, at most 8^5: five parameters, each with no written type or one of
/// the seven types of L1, so no two have the same parameter types.
pub fn overloads(k: usize) -> String {
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
