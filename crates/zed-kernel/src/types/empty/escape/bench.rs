//! A benchmark of the cell discovery of `escape` on a dump of its rows (REFUSAL-front-unsolved):
//! `ZED_ESCAPE_BENCH` names the dump and `ZED_ESCAPE_METHOD` the method run on it.

use super::*;

fn ints(cof: &str, vals: &str) -> Ints {
    Ints {
        cof: cof == "1",
        vals: vals
            .split(',')
            .filter(|s| !s.is_empty())
            .map(|s| Value::Int(s.parse().expect("an integer")))
            .collect(),
    }
}

/// Reads the first instance of a dump; runs the method named by `ZED_ESCAPE_METHOD` on it.
#[test]
#[ignore]
fn escape_cells_bench() {
    let path = std::env::var("ZED_ESCAPE_BENCH").expect("ZED_ESCAPE_BENCH");
    let method = std::env::var("ZED_ESCAPE_METHOD").expect("ZED_ESCAPE_METHOD");
    let text = std::fs::read_to_string(path).expect("the dump");
    let empty_row = Row::new(Vec::new());
    let mut nodes: Vec<Node> = Vec::new();
    let mut pl: Vec<Ints> = vec![ints("0", "")];
    let mut roots: Vec<Root> = Vec::new();
    let mut finals: Vec<(i64, Vec<(usize, Ints)>)> = Vec::new();
    let mut l0 = 0;
    let parse_atoms = |parts: &[&str]| -> Vec<(usize, Ints)> {
        parts
            .iter()
            .map(|a| {
                let w: Vec<&str> = a.split_whitespace().collect();
                (
                    w[0].parse().unwrap(),
                    ints(w[1], w.get(2).copied().unwrap_or("")),
                )
            })
            .collect()
    };
    for line in text.lines() {
        if line == "END" {
            break;
        }
        let parts: Vec<&str> = line.split(" | ").collect();
        let w: Vec<&str> = parts[0].split(' ').collect();
        match w[0] {
            "BEGIN" => l0 = w[2].parse().unwrap(),
            "N" => {
                let next: i64 = w[3].parse().unwrap();
                nodes.push(Node {
                    stop: false,
                    head: ints(w[5], w.get(6).copied().unwrap_or("")),
                    next: (next >= 0).then_some(next as usize),
                    carrier: w[4] == "1",
                    ht: w[2].parse().unwrap(),
                });
            }
            "P" => pl.push(ints(w[2], w.get(3).copied().unwrap_or(""))),
            "R" => {
                let kill: i64 = w[3].parse().unwrap();
                roots.push(Root {
                    row: empty_row.clone(),
                    s: w[2].parse().unwrap(),
                    kill: (kill >= 0).then_some(kill as usize),
                    atoms: parse_atoms(&parts[1..]),
                });
            }
            "F" => finals.push((w[2].parse().unwrap(), parse_atoms(&parts[1..]))),
            _ => {}
        }
    }
    assert_eq!(pl.len(), l0 + 1);
    let anc = Ancestors::new(&nodes);
    let mut counts = (0, 0);
    match method.as_str() {
        "sweep" => cells_sweep(
            &nodes,
            &anc,
            &pl,
            &mut roots,
            l0,
            &HashSet::default(),
            &mut counts,
        ),
        "windows" => cells_windows(&nodes, &anc, &pl, &mut roots, l0, &mut counts),
        "none" => {}
        m => panic!("unknown method {m}"),
    }
    use std::hash::{Hash, Hasher};
    let mut hs = std::collections::hash_map::DefaultHasher::new();
    let mut bad = 0;
    for (i, r) in roots.iter_mut().enumerate() {
        r.atoms.sort_unstable_by_key(|a| a.0);
        r.kill.hash(&mut hs);
        r.atoms.hash(&mut hs);
        if let Some((k, at)) = finals.get(i) {
            let mut at = at.clone();
            at.sort_unstable_by_key(|a| a.0);
            if r.kill.map_or(-1, |x| x as i64) != *k || r.atoms != at {
                bad += 1;
            }
        }
    }
    eprintln!(
        "BENCH method {method} rows {} digest {:016x} bad {bad} checked {} reads {} empty {}",
        roots.len(),
        hs.finish(),
        finals.len(),
        counts.0,
        counts.1
    );
}
