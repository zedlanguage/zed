//! The benchmarks of `one_scope.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::one_scope::*;
use zed_tests::step_helpers::l01_16_elaboration::elab;

#[test]
fn the_questions_of_a_chain_of_calls_scale() {
    // `step{i}(x) = step{i-1}(x: x) + i`, the chain LOAD-chain found (5.4 s at 100 functions
    // and 17.7 s at 200 when each body was closed over its cone). The questions are timed
    // alone, on units elaborated before the timing.
    let unit = |n: usize| {
        let mut src = String::from("step0(x: int) = x;\n");
        for i in 1..n {
            src.push_str(&format!("step{i}(x: int) = step{}(x: x) + {i};\n", i - 1));
        }
        src
    };
    let n = 1800;
    let units: std::collections::BTreeMap<usize, _> = [n, n * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|m| {
            let src = unit(m);
            (
                m,
                (
                    zed_tests::deep::statements(&src),
                    zedc::lex::lex_fence(&src).unwrap(),
                    elab(&src).unwrap(),
                    src,
                ),
            )
        })
        .collect();
    zed_tests::scaling::check("the linear questions of a chain of n calls", n, |m| {
        let (stmts, tokens, unit, src) = &units[&m];
        let refused = zedc::front::linear_questions(src, tokens, stmts, unit);
        assert!(refused.is_empty(), "{refused:?}");
    });
}

#[test]
fn the_questions_of_a_chain_of_tests_scale() {
    // `p{i}(x) = p{i-1}(x: x) && x > i`, the chain of LOAD-chain-share: 62.6 times the bytes
    // for 8 times the functions (100 to 800) when each body translated the chain again, 8.1
    // times when each takes its callee's translation as made for the body before.
    questions_scale("a chain of tests", 1600, "p0(x: int) = x > 0;\n", |i| {
        format!("p{i}(x: int) = p{}(x: x) && x > {i};\n", i - 1)
    });
}

#[test]
fn the_questions_of_a_chain_over_two_variables_scale() {
    // `p{i}(x, y) = p{i-1}(x: x, y: y) && x + i * y < 1000 i`: the relation of `p{i}` holds i
    // constraints, none tighter than another. 195.6 times the bytes for 8 times the functions
    // (50 to 400) when each relation was copied out of its callee's and decided whole, 7.8
    // times when it holds its callee's as a shared part and is decided from its answers.
    questions_scale(
        "a chain of tests over two variables",
        1000,
        "p0(x: int, y: int) = x > y && y >= 0;\n",
        |i| {
            format!(
                "p{i}(x: int, y: int) = p{}(x: x, y: y) && x + {i} * y < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_questions_of_a_chain_defining_auxiliary_variables_scale() {
    // `p{i}(x) = p{i-1}(x: x) && x mod 7 + i > 0`, the chain of LOAD-chain-aux: each link
    // defines a quotient and a remainder. When a body that defined one dropped its
    // translations, each link translated the chain again and each relation was decided whole
    // with all its definitions, O(n²): 90.9 times the bytes for 8 times the functions (50 to
    // 400) on main, 7.9 times now.
    questions_scale(
        "a chain of tests defining auxiliary variables",
        1900,
        "p0(x: int) = x div 3 > 0;\n",
        |i| format!("p{i}(x: int) = p{}(x: x) && x mod 7 + {i} > 0;\n", i - 1),
    );
}

#[test]
fn the_questions_of_a_drifting_chain_scale() {
    // `p{i}(x) = q(x: x) && p{i-1}(x: x + 3) && x < 1000 i` beside `q(x) = r(x: x) && x mod 3
    // == 1` (LOAD-call-summary): each link extends `q`'s point, which it read with the whole
    // chain beside it before; now with the chain's face, `x >= 1`, `x mod 3 == 1` and the
    // link's bound. 40 → 320: 83.9 times the bytes before, the chain read at each link (190
    // MB → 15.9 GB, measured once), 8.2 now (40.9 MB → 334 MB).
    questions_scale(
        "a chain whose links extend a callee's point beside the chain",
        390,
        "r(x: int) = x > 0 && x < 1000000;\nq(x: int) = r(x: x) && x mod 3 == 1;\n\
         p0(x: int) = x > 0;\n",
        drifting_link,
    );
}

#[test]
fn the_questions_of_a_drifting_disjunctive_chain_scale() {
    // The drifting chain beside `q(x) = (x mod 3 == 1 || x mod 5 == 2) && x > 0 && x <
    // 1000000` (LOAD-disj-residue): each link's face keeps one clause for each residue of the
    // shift modulo 5, five at most, where before the chain was read whole at each link (0.244,
    // 1.005, 5.399 s at 40, 80, 160 links, debug, measured once).
    questions_scale(
        "a chain whose links extend a callee's point beside a chain of disjunctions",
        340,
        "q(x: int) = (x mod 3 == 1 || x mod 5 == 2) && x > 0 && x < 1000000;\n\
         p0(x: int) = x > 0;\n",
        drifting_link,
    );
}

#[test]
fn the_questions_of_a_chain_moving_its_argument_scale() {
    // `p{i}(x) = p{i-1}(x: x + 1) && x + 2 i > 0`, the chain of LOAD-chain-args: each link
    // passes its callee another term than its own parameter. 50 → 400: 61.5 times the bytes
    // before (57.2 MB → 3.52 GB, each call translated again), 8.1 now (7.9 MB → 63.9 MB).
    questions_scale(
        "a chain of tests moving the argument",
        1700,
        "p0(x: int) = x > 0;\n",
        |i| {
            format!(
                "p{i}(x: int) = p{}(x: x + 1) && x + {} > 0;\n",
                i - 1,
                2 * i
            )
        },
    );
}

#[test]
fn the_questions_of_a_chain_renaming_its_argument_scale() {
    // `p{i}(x) = p{i-1}(y: x) && x > -i`, the parameter named `x` and `y` by turns: each link
    // passes its callee its own parameter under the callee's name. 50 → 400: 60.7 times the
    // bytes before (45.4 MB → 2.76 GB), 8.0 now (6.3 MB → 50.9 MB).
    questions_scale(
        "a chain of tests renaming the argument",
        1200,
        "p0(x: int) = x > 0;\n",
        |i| {
            let (own, callee) = if i % 2 == 0 { ("x", "y") } else { ("y", "x") };
            format!(
                "p{i}({own}: int) = p{}({callee}: {own}) && {own} > 0 - {i};\n",
                i - 1
            )
        },
    );
}

#[test]
fn the_questions_of_a_chain_of_tests_over_a_chain_of_definitions_scale() {
    // `p{i}(x) = p{i-1}(x: x) && h{i}(x: x) > 0` with `h{i}(x) = h{i-1}(x: x) div 2 + 1`: each
    // link's new constraint reaches the i definitions of `h{i}`. When each link read them all,
    // 74.6 times the instructions and 66.8 times the bytes for 8 times the links (25 to 200);
    // 8.1 and 8.0 times when it reads past those its callee's point gives a value.
    questions_scale(
        "a chain of tests over a chain of halvings",
        720,
        "h0(x: int) = x;\np0(x: int) = x > 0;\n",
        |i| {
            format!(
                "h{i}(x: int) = h{}(x: x) div 2 + 1;\np{i}(x: int) = p{}(x: x) && h{i}(x: x) > 0;\n",
                i - 1,
                i - 1
            )
        },
    );
}

#[test]
fn the_questions_of_a_chain_of_tests_over_mixed_definitions_scale() {
    // As above, the definitions by turns a quotient, a remainder plus the input, a minimum and
    // an absolute value less a quotient: 103.2 times the instructions and 98.5 times the bytes
    // from 25 to 200 links when each link read the chain, about 8.2 times now.
    questions_scale(
        "a chain of tests over mixed definitions",
        520,
        "h0(x: int) = x;\np0(x: int) = x > 0;\n",
        |i| {
            let h = i - 1;
            let op = match i % 4 {
                0 => format!("h{h}(x: x) div 2"),
                1 => format!("h{h}(x: x) mod 7 + x"),
                2 => format!("min(h{h}(x: x), {i}) + 1"),
                _ => format!("abs(h{h}(x: x)) - x div 3"),
            };
            format!("h{i}(x: int) = {op};\np{i}(x: int) = p{h}(x: x) && h{i}(x: x) > 0 - {i};\n")
        },
    );
}

#[test]
fn the_questions_of_a_chain_of_tests_holding_everywhere_scale() {
    // A root and links that hold everywhere, `p{i}(x) = p{i-1}(x: x) && abs(h{i}(x: x)) >= 0`:
    // each link's negation is decided from the definitions its link added, which never hold
    // with it. 85.4 times the instructions and 73.0 times the bytes from 25 to 200 links when
    // it read the chain (81.1 and 62.7 times with only the side that holds reading past the
    // point), 7.7 times now.
    questions_scale(
        "a chain of tests holding everywhere over a chain of halvings",
        420,
        "h0(x: int) = x;\np0(x: int) = x > 0 || x <= 0;\n",
        |i| {
            format!(
                "h{i}(x: int) = h{}(x: x) div 2 + 1;\np{i}(x: int) = p{}(x: x) && abs(h{i}(x: x)) >= 0;\n",
                i - 1,
                i - 1
            )
        },
    );
}

#[test]
fn separate_tests_over_the_links_of_one_chain_of_definitions_scale() {
    // LOAD-chain-sep: `t{i}(x) = h{i}(x: x) > 0` with `h{i}(x) = h{i-1}(x: x) div 2 + 1`, each
    // test a question of its own over the i definitions of `h{i}`, with no kept part. Each was
    // decided with all i definitions, O(n²): 80.4 times the bytes for 8 times the functions (25
    // to 200) on main; read through the summary of `h{i}`'s definition, made from that of
    // `h{i-1}`'s, 8.4 times the bytes and 9.0 times the instructions now.
    questions_scale(
        "separate tests over one chain of halvings",
        680,
        "h0(x: int) = x;\nt0(x: int) = x > 0;\n",
        |i| {
            format!(
                "h{i}(x: int) = h{}(x: x) div 2 + 1;\nt{i}(x: int) = h{i}(x: x) > 0;\n",
                i - 1
            )
        },
    );
}

#[test]
fn separate_tests_over_a_chain_of_branches_scale() {
    // 0.042 s at 50 links, 0.387 s at 400.
    separate_tests_scale(
        "separate tests over a chain of `if`s",
        630,
        1,
        "if H > 3 { H div 2 } else { H + 1 }",
        "H > 2",
    );
}

#[test]
fn separate_tests_over_a_chain_of_smallest_values_scale() {
    // 0.100 s at 50 links, 1.58 s at 400: the summary's coefficients are `2^i` at link i.
    separate_tests_scale(
        "separate tests over a chain of `min`s",
        540,
        1,
        "min(H div 2, x)",
        "H > 0",
    );
}

#[test]
fn separate_tests_over_a_chain_of_largest_values_scale() {
    // LOAD-max-div-xr: the values of `max(H div 2, x - 9)` over `x` at a link are no union of
    // polyhedra without a remainder of `x` (they hold where `x - 10 <= 2 * (x div 8)`), so no
    // summary was made, and each test was decided with every definition it reaches: n^2.4 to
    // n^2.5 from 10 to 80 links. The quotient `x div 8` is now kept beside the key, read as
    // any value, with the rows read through its division pair (Summaries::summary).
    separate_tests_scale(
        "separate tests over a chain of `max`s",
        710,
        1,
        "max(H div 2, x - 9)",
        "H < 0",
    );
}

#[test]
fn separate_tests_over_a_chain_of_largest_values_against_a_quotient_apart_from_it_scale() {
    // Cross-review of LOAD-max-div-xr, round 2 (Claude): the first test numbers `x div 64`
    // before the later links, which then found it outside each link's summary and read every
    // link beside, so that each later test was the whole chain and was refused (`Growth`)
    // from the fourth link on. The quotient is now read beside in the link's place.
    separate_tests_scale(
        "separate tests over a chain of `max`s against a quotient apart from it",
        250,
        1,
        "max(H div 2, x - 9)",
        "H < x div 64 - 1",
    );
}

#[test]
fn separate_tests_over_a_chain_of_largest_values_of_quotients_scale() {
    // LOAD-max-div-xr: `x div 3` beside `H div 2`. Its symbol `x` is kept beside the key where
    // the quotient is, so the next link meets `x div 3` again through the division pair and
    // needs no remainder of it; without that, 5.9 and 153 billion instructions at 10 and 20
    // links, n^4.7.
    separate_tests_scale(
        "separate tests over a chain of `max`s of quotients",
        660,
        1,
        "max(H div 2, x div 3 - 9)",
        "H < 0",
    );
}

#[test]
fn separate_tests_over_a_chain_of_largest_values_of_remainders_scale() {
    // LOAD-max-div-xr: `x mod 3` beside `H div 2`. The variables of `x mod 3` are a function of
    // `x` alone and one fixed set, so one left by a projection stays in the piece as a symbol
    // does, and its definition's variables join the key of a summary that reads them; before,
    // no summary was made: 12.8 and 138 billion instructions at 10 and 20 links, 6 and 16
    // tests refused, n^3.4.
    separate_tests_scale(
        "separate tests over a chain of `max`s of remainders",
        81,
        1,
        "max(H div 2, x mod 3 - 9)",
        "H < 0",
    );
}

#[test]
fn separate_tests_over_a_chain_of_largest_values_of_two_divisions_scale() {
    // LOAD-max-div-xr: `x mod 5 + x div 7` beside `H div 2`. Its projection left a quotient of
    // the chain in rows over both divisions; a piece is now projected again keeping the
    // symbols and the variables of definitions of symbols alone, the bounds `x >= 2^k * (q3 +
    // q4) - 9 * 2^k` piling up at each link are cut to two ([`envelope`] in presburger::extend),
    // unit-bounded division pairs are folded in [`without_free_pairs`] so [`decide_cons`]'s
    // two-pointer hull check discharges empty candidate pieces without `live3`, and big-integer
    // `gcd` uses in-place binary Stein below the half-gcd threshold (`zed_kernel::num::fast`).
    // Before: 37.3 and 477 billion instructions at 10 and 20 links, 6 and 16 tests refused,
    // n^3.7; 15.2 to 240 billion from 40 to 320 links (15.7 times, failing n log n) before
    // unit-pair folding and slice Stein gcd. Now held to O(n log n) at 40 and 320 links.
    separate_tests_scale(
        "separate tests over a chain of `max`s of two divisions",
        430,
        1,
        "max(H div 2, x mod 5 + x div 7 - 9)",
        "H < 0",
    );
}

#[test]
fn separate_tests_over_a_chain_of_largest_values_of_two_inputs_scale() {
    // LOAD-max-div-xr (cross-review round 2, I8): `x + y - 9` beside `H div 2`. The values
    // `h{i}` takes as `x + y - 9` were cut at each link `k` where the chain took it, by `(2^k -
    // 1) x + 2^k y >= c_k` and the form of link `k - 1`, one piece more at each link: 0.25 to
    // 21.4 billion instructions from 10 to 80 links, n^2.1, 70 times from 10 to 80. Pieces next
    // to each other on one form whose rests hold on each other now merge (`merge_pieces` in
    // presburger::extend): four pieces at each link, 0.25, 0.60, 1.29 and 2.79 billion. The
    // coefficients still grow one bit a link, so the work grows by n^1.3 to n^1.6 from 80 to
    // 320 links (13.2 times from 25 to 200): held at 10 and 80 links; the item for n log n at
    // every size is LOAD-max-div-bits.
    separate_tests_over_inputs_scale(
        "separate tests over a chain of `max`s of two inputs",
        440,
        1,
        &["x", "y"],
        "max(H div 2, x + y - 9)",
        "H < 0",
    );
}

#[test]
fn separate_tests_over_a_chain_of_largest_values_less_one_scale() {
    // LOAD-max-div-xr: `x mod 5 + x div 7` beside `H - 1`. The values `h{i}` takes as `x mod 5
    // + x div 7 - 9` are pieces equal but for the interval of `x - (x mod 5) - (x div 7)`,
    // one more at every few links, with gaps between them holding no integer point of the
    // rest (`merge_pieces` in presburger::extend now merges them). Before: 0.67, 2.09, 8.39
    // and 32.6 billion instructions at 10, 20, 40 and 80 links, n^2.0.
    separate_tests_scale(
        "separate tests over a chain of `max`s of a decrement",
        700,
        1,
        "max(H - 1, x mod 5 + x div 7 - 9)",
        "H < 0",
    );
}

#[test]
fn separate_tests_over_a_chain_reading_a_new_symbol_at_each_link_scale() {
    // LOAD-max-div-xr (cross-review round 2, I7): `q{i} = q{i-1} + s{i}`, a test `q{i} >= 0`
    // at each link. The symbols of link i's cone are i + 1; a set copied at each link stores
    // O(n^2) atoms in all (Codex measured 26.7 times the bytes from 320 to 2560 links); a
    // persistent set shares its input's tree, O(log n) at each link.
    use zedc::store::presburger::extend::Extending;
    use zedc::store::presburger::{Atom, Con, Formula, Lin, Shared};
    let defs = |m: usize| -> Vec<Formula> {
        let sym = |i: usize| Lin::atom(Atom::Sym(format!("s{i}").into()));
        let aux = |i: usize| Lin::atom(Atom::Aux(i as u32));
        (0..m)
            .map(|i| {
                let rhs = if i == 0 {
                    sym(0)
                } else {
                    aux(i - 1).plus(&sym(i))
                };
                Formula::And(Shared::new(vec![Formula::Con(Con::eq(&aux(i), &rhs))]))
            })
            .collect()
    };
    let inputs = zed_tests::scaling::inputs(18000, |m| {
        let asks: Vec<Formula> = (0..m)
            .map(|i| Formula::Con(Con::ge(&Lin::atom(Atom::Aux(i as u32)), &Lin::constant(0))))
            .collect();
        (defs(m), asks)
    });
    zed_tests::scaling::check(
        "separate tests over a chain reading a new symbol at each link",
        18000,
        |m| {
            let (defs, asks) = &inputs[&m];
            let mut extending = Extending::new();
            for f in asks {
                let a = extending.defined(f, &|n| defs[n as usize].clone());
                assert_eq!(a.holds, Ok(true));
            }
        },
    );
}

#[test]
fn separate_tests_over_a_chain_reading_a_new_division_pair_at_each_link_scale() {
    // LOAD-max-div-xr (cross-review round 3, I24): each link reads both `q_{i-1}` and `r_{i-1}` of
    // the multi-output division pair below it plus a fresh symbol `s{i}`. Without input
    // deduplication in `Summaries::syms`, each frame pushed the child `Formula` twice and merged
    // its `i`-element `OrdSet` into itself (14.41 times from 200 to 1600 links, failing the 14.08
    // limit). With `seen_in` per frame, each distinct input is visited once.
    use zedc::store::presburger::extend::Extending;
    use zedc::store::presburger::{Atom, Con, Formula, Lin, Shared};
    let inputs = zed_tests::scaling::inputs(8800, |m| {
        let sym = |i: usize| Lin::atom(Atom::Sym(format!("s{i}").into()));
        let q = |i: usize| Lin::atom(Atom::Aux((2 * i) as u32));
        let r = |i: usize| Lin::atom(Atom::Aux((2 * i + 1) as u32));
        let defs: Vec<Formula> = (0..m)
            .flat_map(|i| {
                let dividend = if i == 0 {
                    sym(0)
                } else {
                    q(i - 1).plus(&r(i - 1)).plus(&sym(i))
                };
                let eq = Con::eq(&dividend, &q(i).times(7).plus(&r(i)));
                let lo = Con::ge(&r(i), &Lin::constant(0));
                let hi = Con::ge(&Lin::constant(6), &r(i));
                let d = Formula::And(Shared::new(vec![
                    Formula::Con(eq),
                    Formula::Con(lo),
                    Formula::Con(hi),
                ]));
                [d.clone(), d]
            })
            .collect();
        let asks: Vec<Formula> = (0..m)
            .map(|i| Formula::Con(Con::ge(&q(i), &Lin::constant(0))))
            .collect();
        (defs, asks)
    });
    zed_tests::scaling::check(
        "separate tests over a chain reading a new division pair at each link",
        8800,
        |m| {
            let (defs, asks) = &inputs[&m];
            let mut extending = Extending::new();
            for f in asks {
                let a = extending.defined(f, &|n| defs[n as usize].clone());
                assert_eq!(a.holds, Ok(true));
            }
        },
    );
}

#[test]
fn separate_tests_over_a_periodic_remainder_chain_scale() {
    // LOAD-max-div-xr (I12, I26): `H mod 7 + H` has period 7 (`h_k(x) = x + d_k(x mod 7)`, at most
    // 7 pieces), but inlining multi-term call values added one remainder atom a link to the key
    // and left no summary (1.07 G and 16 refused at 20 links, 12.0 G and 36 refused at 40, timed
    // out past 60 s at 160). Binding multi-term call values to a value variable in `preimage` and
    // splitting on bounded periodic quotient offsets (`quotient_offsets`, `normalize_own_leaf`)
    // summarizes every link in O(n log n) with 0 refusals.
    separate_tests_scale(
        "separate tests over a periodic remainder chain",
        870,
        1,
        "H mod 7 + H",
        "H < 0",
    );
}

#[test]
fn separate_tests_over_two_chains_sharing_an_input_scale() {
    // LOAD-max-div-xr (I21): a test at each depth reading two independent chains `g{i}(x)` and
    // `p{i}(x, y)` that share both input `x` and a functional leaf `x div 7`, after an earlier
    // test numbered `g{m}` first. Before, `Summaries::local` kept at most one summary and unrolled
    // the entire lower-numbered chain into `beside`, O(n^2) with refusals.
    let inputs = zed_tests::scaling::inputs(30, |m| {
        let mut src = "g0(x: int) = x;\np0(x: int, y: int) = x + y;\n".to_string();
        for i in 1..=m {
            src += &format!("g{i}(x: int) = max(g{}(x: x) div 2, x div 7 - 9);\n", i - 1);
            src += &format!(
                "p{i}(x: int, y: int) = if p{}(x: x, y: y) > x div 7 {{ p{}(x: x, y: y) + 1 }} else {{ p{}(x: x, y: y) }};\n",
                i - 1,
                i - 1,
                i - 1
            );
        }
        src += &format!("u(x: int) = g{m}(x: x) < 0;\n");
        for i in 1..=m {
            src +=
                &format!("t{i}(x: int, y: int) = g{i}(x: x) + p{i}(x: x, y: y) < 0 && y == 0;\n");
        }
        let stmts = zed_tests::deep::statements(&src);
        let tokens = zedc::lex::lex_fence(&src).expect("lex");
        let unit = elab(&src).expect("elab");
        (src, tokens, stmts, unit)
    });
    zed_tests::scaling::check("separate tests over two chains sharing an input", 30, |m| {
        let (src, tokens, stmts, unit) = &inputs[&m];
        let refused = zedc::front::linear_questions(src, tokens, stmts, unit);
        assert!(refused.is_empty(), "m = {m}: {} refused", refused.len());
    });
}

#[test]
fn separate_tests_over_a_chain_of_largest_values_of_multiples_scale() {
    // LOAD-max-div-xr: `2 * x - 9` beside `H div 2`.
    separate_tests_scale(
        "separate tests over a chain of `max`s of multiples",
        720,
        1,
        "max(H div 2, 2 * x - 9)",
        "H < 0",
    );
}

#[test]
fn separate_tests_over_a_chain_of_smallest_values_against_the_input_scale() {
    // LOAD-max-div-xr: `min` against a step of the input.
    separate_tests_scale(
        "separate tests over a chain of `min`s against `x - 5`",
        470,
        1,
        "min(H div 2 + 1, x - 5)",
        "H > 3",
    );
}

#[test]
fn separate_tests_over_a_chain_of_absolute_values_scale() {
    // 0.051 s at 50 links, 0.468 s at 400.
    separate_tests_scale(
        "separate tests over a chain of `abs`s",
        550,
        1,
        "abs(H - 5) div 2",
        "H > 1",
    );
}

#[test]
fn separate_tests_over_a_chain_of_two_inputs_scale() {
    // 0.100 s at 50 links, 0.972 s at 400.
    separate_tests_scale(
        "separate tests over a chain reading two quotients of one link",
        660,
        1,
        "min(H div 2, H div 3 + 1)",
        "H > 1",
    );
}

#[test]
fn separate_tests_over_two_links_of_one_chain_scale() {
    // 0.053 s at 50 links, 0.232 s at 400.
    separate_tests_scale(
        "separate tests over two links of one chain",
        510,
        1,
        "H div 2 + 1",
        "H > h1(x: x)",
    );
}

#[test]
fn separate_conjunctions_over_the_links_of_one_chain_scale() {
    // 0.027 s at 50 links, 0.375 s at 400.
    separate_tests_scale(
        "separate conjunctions over one chain of halvings",
        470,
        1,
        "H div 2 + 1",
        "H > 0 && x < 1000",
    );
}

#[test]
fn separate_tests_over_a_chain_of_divisions_by_a_parameter_scale() {
    // LOAD-chain-sep-nonlinear: the product `x * q` of a quotient by `x` is read as an atom of
    // its own, as the solver reads it, so each definition has a summary. Before, no summary was
    // made and each test was decided with every definition it reaches: 0.58 s at 50 links, 55 s
    // at 400; 74.5 times the instructions from 10 to 80 links, and 112 times the bytes from 25
    // to 200. Now 77.0 and 641 million instructions at 25 and 200 links, 8.3 times.
    separate_tests_scale(
        "separate tests over a chain of divisions by a parameter",
        560,
        1,
        "H div x",
        "H > 0",
    );
}

#[test]
fn separate_tests_over_a_chain_of_products_scale() {
    // LOAD-chain-sep-nonlinear: the translation of each body fails at the product
    // `h{i-1}(x: x) * x`, and the failed translations of the chain below it are kept for the
    // next body (`Tx::forget`), so a body reads only its own link. Before, each body read the
    // chain below it again: 0.072 s at 50 links, 3.46 s at 400; 41.8 times the instructions
    // from 10 to 80 links, and 52 times the bytes from 25 to 200. Now 17.2 and 137 million
    // instructions at 25 and 200 links, 8.0 times.
    separate_tests_scale(
        "separate tests over a chain of products",
        770,
        1,
        "H * x + 1",
        "H > 0",
    );
}

#[test]
fn tests_that_forget_deep_and_wide_translations_scale() {
    // T11-preimage-log: each test reads four chains `n` links deep, and the translation of
    // all of them is undone (`Tx::forget`, `Tr::truncate`), since the right side `q(x: x)` is
    // the product `x * x * x`, which has no linear term. The next test translates the chains
    // again, so each test makes and undoes about `32n` entries, linear in `n`.
    let tests = 4;
    let units: std::collections::BTreeMap<usize, _> = [250, 250 * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|m| {
            let mut src = String::from("q(x: int) = x * x * x;\n");
            for a in 0..4 {
                src += &format!("g{a}_0(x: int) = x + {a};\n");
                for i in 1..m {
                    src += &format!("g{a}_{i}(x: int) = g{a}_{}(x: x) + {i};\n", i - 1);
                }
            }
            let sum = (0..4)
                .map(|a| format!("g{a}_{}(x: x)", m - 1))
                .collect::<Vec<_>>()
                .join(" + ");
            for j in 0..tests {
                src += &format!("t{j}(x: int) = {sum} < q(x: x) + {j};\n");
            }
            (
                m,
                (
                    zed_tests::deep::statements(&src),
                    zedc::lex::lex_fence(&src).unwrap(),
                    elab(&src).unwrap(),
                    src,
                ),
            )
        })
        .collect();
    zed_tests::scaling::check_order(
        "tests that undo the translation of four chains",
        250,
        1,
        |m| {
            let (stmts, tokens, unit, src) = &units[&m];
            let refused = zedc::front::linear_questions(src, tokens, stmts, unit);
            assert!(refused.is_empty(), "{refused:?}");
        },
    );
}

#[test]
fn separate_tests_over_a_chain_of_nonunit_steps_scale() {
    // 0.032 s at 50 links, 0.127 s at 400: the remainder, read by no other link, is projected
    // out with the input, so `2 * H == 3 * q + r` leaves no congruence.
    separate_tests_scale(
        "separate tests over a chain of `(2 * H) div 3`",
        990,
        1,
        "(2 * H) div 3",
        "H > 0",
    );
}

#[test]
fn the_questions_of_a_chain_doubling_its_argument_scale() {
    // `p{i}(x) = p{i-1}(x: 2 * x) && x < 1000 i`, LOAD-chain-affine: a map of the parameter
    // that is not a move. 50 → 400: 59.3 times the bytes when each call was translated again
    // at its argument; each body is now read once over its canonical atom, and a call binds
    // that atom to its argument.
    questions_scale(
        "a chain of tests doubling the argument",
        760,
        "p0(x: int) = x > 0;\n",
        |i| format!("p{i}(x: int) = p{}(x: 2 * x) && x < {};\n", i - 1, 1000 * i),
    );
}

#[test]
fn the_questions_of_a_chain_negating_its_argument_scale() {
    // `p{i}(x) = p{i-1}(x: 0 - x) && x < 1000 i`: a map with a negative factor. Linear before
    // LOAD-chain-affine too; kept so that the canonical reading stays so.
    questions_scale(
        "a chain of tests negating the argument",
        720,
        "p0(x: int) = x > 0;\n",
        |i| format!("p{i}(x: int) = p{}(x: 0 - x) && x < {};\n", i - 1, 1000 * i),
    );
}

#[test]
fn the_questions_of_a_chain_passing_a_constant_scale() {
    // `p{i}(x, y) = p{i-1}(x: x, y: 5) && x + y < 1000 i`: a constant argument beside a
    // parameter passed as it is. Linear before LOAD-chain-affine too (the moved case is
    // `the_relations_of_a_chain_passing_a_moved_parameter_and_a_constant_scale`).
    questions_scale(
        "a chain of tests passing a constant",
        580,
        "p0(x: int, y: int) = x > y;\n",
        |i| {
            format!(
                "p{i}(x: int, y: int) = p{}(x: x, y: 5) && x + y < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_questions_of_a_chain_passing_a_parameter_twice_scale() {
    // `p{i}(x, y) = p{i-1}(x: x, y: x) && x + y < 1000 i`: a map that is not one-to-one; the
    // join of `x` to both of the callee's parameters is refused once per link
    // (`preimage::identity_classes`). Linear before LOAD-chain-affine too (the moved case is
    // `the_relations_of_a_chain_passing_a_moved_parameter_twice_scale`).
    questions_scale(
        "a chain of tests passing a parameter twice",
        650,
        "p0(x: int, y: int) = x >= y;\n",
        |i| {
            format!(
                "p{i}(x: int, y: int) = p{}(x: x, y: x) && x + y < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_questions_of_a_chain_with_a_second_call_scale() {
    // `p{i}(x) = q(x: x) && p{i-1}(x: x + 1) && x < 1000 i`: one function, `q`, called by
    // every link with another argument; its relation, one constraint, is written at each
    // call's argument. 50 → 400: 60.1 times the bytes when each link read the chain below
    // it again.
    questions_scale(
        "a chain of tests with a second call",
        760,
        "q(x: int) = x < 1000000;\np0(x: int) = x > 0;\n",
        |i| {
            format!(
                "p{i}(x: int) = q(x: x) && p{}(x: x + 1) && x < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_questions_of_a_chain_calling_its_helpers_in_a_diamond_scale() {
    // `h{i}(x) = h{i-1}(x: x) div 2 + 1; p{i}(x) = p{i-1}(x: x) && h{i}(x: x) > 0`: `h{i-1}`
    // is called by `h{i}` and through `p{i-1}`, each passing its parameter as it is; one class
    // of parameters holds them all (`preimage::identity_classes`), so each body is read once.
    // Linear before LOAD-chain-affine too; kept so that the classes keep it so.
    questions_scale(
        "a chain of tests calling its helpers in a diamond",
        450,
        "h0(x: int) = x;\np0(x: int) = x > 0;\n",
        |i| {
            format!(
                "h{i}(x: int) = h{}(x: x) div 2 + 1;\np{i}(x: int) = p{}(x: x) && h{i}(x: x) > 0;\n",
                i - 1,
                i - 1
            )
        },
    );
}

#[test]
fn the_relations_of_a_chain_with_a_second_call_whose_points_move_scale() {
    // 50 → 400: 62.5 times the bytes when each call was translated again.
    relations_scale(
        "the relations of a chain with a second call whose points move",
        950,
        "q(x: int) = x > 0;\np0(x: int) = x > 0;\n",
        |i| {
            format!(
                "p{i}(x: int) = q(x: x) && p{}(x: x + 1) && x < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_relations_of_a_chain_dividing_by_its_argument_scale() {
    // `q`, whose condition holds four divisors, called by every link with another argument
    // list, and each link called by the next with a moved one: the condition of a call that
    // holds no claim is its callee's, written at its arguments ([`Walk::defined_called`] in
    // preimage.rs).
    relations_scale(
        "the relations of a chain dividing by its argument",
        520,
        "q(x: int, n: int) = x mod n + x mod (n + 1) + x div (n + 2) + x div (n + 3) >= 0;\n\
         p0(x: int, n: int) = x mod n >= 0;\n",
        |i| {
            format!(
                "p{i}(x: int, n: int) = q(x: x, n: n + {i}) && p{}(x: x + 1, n: n) && x < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_relations_of_a_chain_passing_a_moved_parameter_twice_scale() {
    // A map that is not one-to-one, of a moved parameter. 50 → 400: 62.5 times the bytes when
    // each call was translated again.
    relations_scale(
        "the relations of a chain passing a moved parameter twice",
        740,
        "p0(x: int, y: int) = x >= y;\n",
        |i| {
            format!(
                "p{i}(x: int, y: int) = p{}(x: x + 1, y: x + 1) && x + y < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_relations_of_a_chain_passing_a_moved_parameter_and_a_constant_scale() {
    // A constant beside a moved parameter. 50 → 400: 62.4 times the bytes when each call was
    // translated again.
    relations_scale(
        "the relations of a chain passing a moved parameter and a constant",
        650,
        "p0(x: int, y: int) = x > y;\n",
        |i| {
            format!(
                "p{i}(x: int, y: int) = p{}(x: x + 1, y: 5) && x + y < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_relations_of_a_chain_with_a_second_call_of_two_constraints_scale() {
    // `q` of two constraints is claimed by its first call and bound by each other. 50 → 400:
    // 61.1 times the bytes when each call was translated again.
    relations_scale(
        "the relations of a chain with a second call of two constraints",
        1200,
        "q(x: int) = x > 0 && x < 1000000;\np0(x: int) = x > 0;\n",
        |i| {
            format!(
                "p{i}(x: int) = q(x: x) && p{}(x: x + 1) && x < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_relations_of_a_chain_with_a_second_call_of_a_call_scale() {
    // `q` calls `r` with its parameter as it is, so the two are one class
    // (`preimage::identity_classes`), read once. 50 → 400: 59.2 times the bytes when each call
    // was translated again.
    relations_scale(
        "the relations of a chain with a second call of a call",
        950,
        "r(x: int) = x > 0 && x < 1000000;\nq(x: int) = r(x: x) && x mod 3 == 1;\n\
         p0(x: int) = x > 0;\n",
        |i| {
            format!(
                "p{i}(x: int) = q(x: x) && p{}(x: x + 1) && x < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_questions_of_a_chain_with_a_second_call_of_a_call_scale() {
    // `p{i}(x) = q(x: x) && p{i-1}(x: x + 1) && x < 1000 i`, `q` calling `r`, with upper bounds
    // alone, so each link's point extends its callee's. Each conjunction keeps its largest
    // part, `p{i-1}`'s relation, and reads `q`'s beside it (`presburger::extend`); keeping the
    // first, `q`'s, read the chain again at each link. 50 → 400: 59.1 times the bytes when each
    // link translated the chain below it again.
    questions_scale(
        "a chain of tests with a second call of a call",
        670,
        "r(x: int) = x < 2000000;\nq(x: int) = r(x: x) && x < 1000000;\np0(x: int) = x > 0;\n",
        |i| {
            format!(
                "p{i}(x: int) = q(x: x) && p{}(x: x + 1) && x < {};\n",
                i - 1,
                1000 * i
            )
        },
    );
}

#[test]
fn the_questions_of_a_chain_with_a_second_call_of_a_large_callee_scale() {
    // `p{i}(x) = h{n-1}(x: x) && p{i-1}(x: x + 1) && x < 1000 i`, `h{j}(x) = h{j-1}(x: x) &&
    // x mod 3 + j < 2000000` a chain of n links (LOAD-affine-cone): one callee whose cone
    // grows with the chain, called by every link with another argument. Its first call claims
    // it; each other is its relation with the quotients and remainders and the bindings of its
    // calls eliminated, made once and written at the call's argument in O(its rows). 50 → 400:
    // 51.6 times the bytes when each such call read the callee's cone again (304 MB → 15.7 GB,
    // measured once), 8.0 now (45.2 MB → 361 MB).
    let unit = |n: usize| {
        let mut src = String::from("h0(x: int) = x < 2000000;\n");
        for j in 1..n {
            src.push_str(&format!(
                "h{j}(x: int) = h{}(x: x) && x mod 3 + {j} < 2000000;\n",
                j - 1
            ));
        }
        src.push_str("p0(x: int) = x > 0;\n");
        for i in 1..n {
            src.push_str(&format!(
                "p{i}(x: int) = h{}(x: x) && p{}(x: x + 1) && x < {};\n",
                n - 1,
                i - 1,
                1000 * i
            ));
        }
        src
    };
    let n = 330;
    let units: std::collections::BTreeMap<usize, _> = [n, n * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|m| {
            let src = unit(m);
            (
                m,
                (
                    zed_tests::deep::statements(&src),
                    zedc::lex::lex_fence(&src).unwrap(),
                    elab(&src).unwrap(),
                    src,
                ),
            )
        })
        .collect();
    zed_tests::scaling::check(
        "the linear questions of a chain with a second call of a large callee",
        n,
        |m| {
            let (stmts, tokens, unit, src) = &units[&m];
            let refused = zedc::front::linear_questions(src, tokens, stmts, unit);
            assert!(refused.is_empty(), "{refused:?}");
        },
    );
}

#[test]
fn the_relations_of_a_chain_calling_an_integer_function_scale() {
    // `p{i}(x) = h{n-1}(x: x) < 3n && p{i-1}(x: x + 1) && x < 1000 i` beside `h{j}(x) =
    // h{j-1}(x: x) + x mod 3` (LOAD-call-relation): each call but the first read the integer
    // function's cone again, O(n) a call (0.062, 0.238, 1.082 s for the relations at 50, 100,
    // 200 links; 50 → 400: 60.2 times the bytes, 88.2 MB → 5.31 GB; measured once). Its
    // value is now written once over its argument's pairs and, at a call, at the argument: 8.1
    // times (13.6 MB → 111 MB). Only the relations are timed: deciding these
    // questions (`Extending::defined_with`) grows faster than n log n with the remainders
    // along the chain (10.7 s at 400 links), which item LOAD-call-relation returns.
    unit_relations_scale(
        "the relations of a chain calling an integer function",
        510,
        |n| {
            let mut src = String::from("h0(x: int) = x mod 3;\n");
            for j in 1..n {
                src.push_str(&format!("h{j}(x: int) = h{}(x: x) + x mod 3;\n", j - 1));
            }
            src.push_str("p0(x: int) = x > 0;\n");
            for i in 1..n {
                src.push_str(&format!(
                    "p{i}(x: int) = h{}(x: x) < {} && p{}(x: x + 1) && x < {};\n",
                    n - 1,
                    3 * n,
                    i - 1,
                    1000 * i
                ));
            }
            src
        },
    );
}

#[test]
fn the_questions_of_a_chain_moving_a_hole_scale() {
    // LOAD-bound-holes: the drifting chain beside `q(x) = (x < 10 || x > 20) && 0 < x <
    // 1000000`. Each link moves the hole `10..=20` by 3 and keeps it, so the face of the
    // chain at link i says `x` lies outside the union of i holes. Before, a face held one
    // clause a link and each link was decided whole: 0.39, 1.62, 7.06 s at 40, 80, 160 links
    // (debug, measured once). Now the holes are one ordered map of disjoint intervals, read
    // through each call's binding and merged in O(log n): 0.032, 0.098, 0.198 s.
    questions_scale(
        "a chain whose links move a hole of their callee",
        470,
        "q(x: int) = (x < 10 || x > 20) && x > 0 && x < 1000000;\np0(x: int) = x > 0;\n",
        drifting_link,
    );
    // The same moved down by 30, so that the holes do not overlap: 0.011, 0.021, 0.038 s.
    questions_scale(
        "a chain whose links move a hole of their callee apart",
        470,
        "q(x: int) = (x < 10 || x > 20) && x > 0 && x < 1000000;\np0(x: int) = x > 0;\n",
        falling_link,
    );
}

#[test]
fn the_questions_of_a_chain_moving_bounds_beside_a_shared_remainder_scale() {
    // LOAD-bound-holes: `q(x) = (x mod 6 == 1 || x > 100) && (x mod 6 == 5 || x < 50)`, whose
    // two disjunctions share the remainder of `x` by 6, in a chain moving `x` by 12. Each link
    // kept its own bound atom, quotient and remainder, and a clause each, so a link read the
    // chain: 3.06 s at 40 links, 25.4 s at 80 (debug, measured once). Now the bindings are
    // followed to the caller's atom, the divisions of one term by 6 read one remainder, and
    // the clauses `r == 5 || x <= b` keep the tightest `b`: 0.111, 0.369 s at 40, 80 links,
    // about 2.4 ms a link. Sized 8 and 64: without these three steps the cost of a link grows
    // until about link 60 and then stays, so 40 and 320 passed the limit, where 8 and 64 fail
    // it (243 times the bytes; 189, 181 and 64 times without each step alone). Link 76, the
    // first with no point, was decided whole, about 0.15 s at any length; LOAD-holes-mod
    // decides its face empty (3.5 ms), and the sizes past it are timed in
    // `the_questions_of_a_chain_of_holes_beside_one_modulus_scale`.
    questions_scale(
        "a chain whose links move bounds beside a shared remainder",
        340,
        "q(x: int) = (x mod 6 == 1 || x > 100) && (x mod 6 == 5 || x < 50) && x > 0 \
         && x < 1000000;\np0(x: int) = x > 0;\n",
        rising_link,
    );
}

#[test]
fn the_questions_of_a_chain_of_holes_beside_one_modulus_scale() {
    // LOAD-holes-mod. The chain of the task has no point from link 4 on; each link was decided
    // whole and refused (Shadows): 8.73 s at 12 links, 29.2 s at 16 (debug, measured once).
    // Now its face is read empty from its holes and the residues left by 4: 0.044 s at 12
    // links, 0.75 s at 320.
    questions_scale_unit("a chain of holes beside one modulus", 94, mod4_chain);
    // The gapped chain keeps a point until its holes cover the range: 17.6 s at 23 links
    // before, 0.071 s now, 1.68 s at 320.
    questions_scale_unit("a chain of a gap beside one modulus", 94, gapped_chain);
    // Link 76 of the shared-remainder chain is the first with no point: before, it was
    // decided whole, 0.13 s; now its face is decided empty by the solver, 3.5 ms.
    questions_scale_unit(
        "a chain moving bounds beside a shared remainder past link 76",
        94,
        shared_remainder_chain,
    );
}

#[test]
fn the_questions_of_a_chain_of_remainders_scale() {
    // LOAD-mod-chain. The chain of the task holds nowhere from link 3 on; its face kept the
    // residues of the link below as one-sided rows, read one at a time, so each link was
    // decided whole and refused (Shadows), and asked again whole: 5.5 s at 100 links, 21.9 s
    // at 200 (debug, measured once). Now the face of link 3 is read empty, and each later
    // link holds nowhere from the link below: 0.063 s at 100 links, 0.23 s at 400.
    questions_scale_unit("a chain of remainders by 3", 200, mod3_chain);
    questions_scale_unit("a chain of remainders by 5", 200, mod5_chain);
    questions_scale_unit("a chain of remainders by 7 moved by 2", 200, mod7_chain);
    questions_scale_unit(
        "a chain of remainders moved by the modulus",
        200,
        kept_residue_chain,
    );
}

#[test]
fn the_questions_of_a_chain_of_residue_maps_scale() {
    // I49. Each link moves h by an amount set by h mod M, with two exceptional residues or an
    // affine default 3 r + 1 on the remainder r; its image is the integers whose residue is
    // not missing, the missing residues kept in the frame of the composed default maps.
    // Before, the graph path split on residues: two guards 3.08e9 instructions at 10 links,
    // 5.14e10 at 40 (exponent 2.0); the affine default 1.17e9 at 5 links (exponent 4.5).
    // Now 2.0e7 and 8.4e7 for two guards, 1.4e8 at 80 links for the affine default.
    questions_scale_unit("a chain of two exceptional residues", 43, two_guards_chain);
    questions_scale_unit(
        "a chain of an affine default with an exception",
        43,
        affine_default_chain,
    );
    // LOAD-max-div-unsolved: a default multiplier that shares a factor with M. The residues
    // are the coset c + d Z with the missing ones kept by position, and the residues outside
    // it kept apart; each step whose multiplier is no unit on the coset shrinks it by that
    // factor, at most log2 M times. Before, the graph path: 1.2e11 instructions at 80 links
    // for the doubling chain.
    questions_scale_unit("a chain doubling the residue by 1000", 43, doubling_chain);
    questions_scale_unit(
        "a chain of a default doubling the residue by 2^40",
        43,
        power_of_two_default_chain,
    );
    // The residues outside the coset are keyed by M split into coprime blocks; a step maps
    // one by one only those not yet equal to the coset's point on a block where its
    // multiplier is no unit, each at most log2 M times. Before (346407a9f), every residue
    // outside the coset was mapped at every step whose multiplier is no unit mod M: 1.95e8
    // and 2.55e9 instructions at 160 and 1280 links, 13.1 times. Now 1.94e8 and 1.72e9, 8.9
    // times. 160 links, not 40, since the first 24 links build the coset.
    questions_scale_unit(
        "a chain of a default unit on the coset only, by 2^10 3^10 5^10",
        360,
        nonunit_persist_chain,
    );
}

#[test]
fn the_questions_of_a_chain_of_residue_intervals_scale() {
    // LOAD-max-div-unsolved: steps that move h by a constant on each interval of h mod M. The
    // image is a union of intervals of residues, kept in a persistent tree whose subtrees
    // move by a constant in O(1), so a link costs its pieces' cuts and the runs its union
    // merges, not the size of the image.
    questions_scale_unit("a chain of two intervals, by 10^18 + 9", 37, gap_chain);
    questions_scale_unit(
        "a chain of two wide intervals, by 2^31 - 1",
        37,
        gap_wide_chain,
    );
    questions_scale_unit(
        "a chain of nested cuts, by 2^31 - 1",
        37,
        cuts_reversed_chain,
    );
    questions_scale_unit(
        "two alternating steps of cuts, by 2^31 - 1",
        37,
        two_cut_steps_chain,
    );
    questions_scale_unit(
        "three steps of overlapping cuts, by 2^31 - 1",
        37,
        overlap_chain,
    );
    // Steps with offsets near M, whose shifted parts overlap across most of the residues.
    questions_scale_unit(
        "two steps of wide overlaps, by 10^12 + 39",
        37,
        overlap0_chain,
    );
    questions_scale_unit(
        "three steps of wide overlaps, by 10^12 + 39",
        37,
        overlap6_chain,
    );
    questions_scale_unit(
        "three steps of wide overlaps, by 10^18 + 9",
        37,
        overlap19_chain,
    );
}

#[test]
fn the_questions_of_a_chain_of_residue_intervals_with_no_period_scale() {
    // LOAD-max-div-unsolved: chains whose steps never repeat with a period, or repeat only
    // after a different first step, or switch between two steps every five links. Main
    // before the interval tree, which listed the whole image at each change of period, took
    // 11.3 times the work at 100 and 800 links on the small moves and 14.1 times the bytes on
    // the switching chain, over the limit of 12.77.
    questions_scale_unit("random cuts and moves, by 2^31 - 1", 220, random_cuts_chain);
    questions_scale_unit(
        "random cuts and moves of 0 to 6, by 2^31 - 1",
        220,
        random_small_moves_chain,
    );
    questions_scale_unit(
        "a step switching every five links, by 10^12 + 39",
        220,
        switching_chain,
    );
    questions_scale_unit(
        "a first step apart from the rest, by 10^12 + 39",
        220,
        first_step_apart_chain,
    );
}

#[test]
fn independent_question_frontiers_scale() {
    questions_scale_unit("independent question frontiers", 370, |n| {
        r6_local_source("leaves", n)
    });
}

#[test]
fn questions_over_two_branches_of_one_prefix_scale() {
    questions_scale_unit("two branches of one common prefix", 560, |n| {
        r6_local_source("prefix", n)
    });
}

#[test]
fn scalar_images_of_periodic_chains_scale() {
    questions_scale_unit("scalar image of guarded increments", 400, |n| {
        r6_periodic_value_questions(n, "if H mod 1000 == 0 { H + 1 } else { H + 2 }", "H == 9")
    });
    questions_scale_unit("scalar lattice image of a remainder sum", 400, |n| {
        r6_periodic_value_questions(n, "H mod 1000 + H", "H == 0")
    });
}

#[test]
fn period_orbits_with_a_kept_input_remainder_scale() {
    questions_scale_unit(
        "guarded increment orbit with kept input residue",
        160,
        |n| {
            r6_periodic_value_questions(
                n,
                "if H mod 1000 == 0 { H + 1 } else { H + 2 }",
                "x mod 1000 == 3 && H == 9",
            )
        },
    );
    questions_scale_unit("remainder-sum orbit with kept input residue", 160, |n| {
        r6_periodic_value_questions(n, "H mod 1000 + H", "x mod 1000 == 3 && H == 9")
    });
    questions_scale_unit(
        "guarded increment orbit with previous link residue",
        160,
        |n| {
            r6_periodic_value_questions(
                n,
                "if H mod 1000 == 0 { H + 1 } else { H + 2 }",
                "P mod 1000 == 3 && H == 5",
            )
        },
    );
    questions_scale_unit("remainder-sum orbit with previous link residue", 160, |n| {
        r6_periodic_value_questions(n, "H mod 1000 + H", "P mod 1000 == 3 && H == 6")
    });
}

#[test]
fn the_questions_of_a_negated_modular_chain_scale() {
    // PNCX-modular: a chain of functions over `q(x) = !(x mod 3 == 2 && x > 11) && (x mod 4 == 1
    // || x > -5) && 0 < x < 1000000` with negated and disjunctive residues over moduli 3, 4, 5
    // and 7 at each link. On main (cbfd0720), links from 6 on took 0.2 to 0.8 s each and were
    // refused with Shadows. Now decided in O(n log n) with no refusals, 40 to 320 links.
    questions_scale_unit(
        "a chain of negated and disjunctive residues over several moduli",
        250,
        negated_modular_chain,
    );
}

#[test]
fn the_coprime_base_of_distinct_primes_scales() {
    // PNCX-modular, R3 (R3-CLAUDE-3): the coprime base of `n` distinct primes is found by one
    // product tree, in which each prime is coprime to the product of the others, and the point
    // is combined by one remainder tree. The pairwise base, and the pairwise combination by the
    // Euclidean algorithm, cost order `n^2`; at 512 and 4096 this test fails with either (15.5
    // and 20.4 times the work or bytes, against 11.7), at 64 and 512 with neither.
    questions_scale_unit(
        "residues over distinct primes",
        1100,
        residues_over_distinct_primes,
    );
}

#[test]
fn the_questions_of_clauses_over_many_segments_scale() {
    // PNCX-modular, R3 (R3-CLAUDE-2): the segments between the bounds of `n` clauses are walked
    // as a segment tree, each clause stored at O(log n) nodes, so the walk costs order
    // `n log n`; solving each segment with all the clauses active in it cost order `n^2`.
    questions_scale_unit(
        "clauses over many segments",
        920,
        clauses_over_many_segments,
    );
}

#[test]
fn clauses_sharing_one_residue_condition_scale() {
    // PNCX-modular, R4 (I3.12): the bounds of the clauses that share one residue condition are
    // intersected as one, by sorting the pieces of their complements, so this costs order
    // `n log n`; intersecting them one after another cost order `n^2`.
    let formulas: std::collections::BTreeMap<usize, _> =
        [21500, 21500 * zed_tests::scaling::FACTOR]
            .into_iter()
            .map(|n| (n, clauses_sharing_one_residue_condition(n)))
            .collect();
    zed_tests::scaling::check("clauses sharing one residue condition", 21500, |n| {
        assert_eq!(zedc::store::presburger::decide(&formulas[&n]), Ok(true));
    });
}

#[test]
fn a_disjunction_of_many_moduli_scales() {
    // PNCX-modular, R4 (R4-CLAUDE-2): the clauses over the coprime base are built with each
    // literal merged into the clause built so far, not into a copy of it, so a clause of `n`
    // literals costs order `n`; copying cost order `n^2`.
    let formulas: std::collections::BTreeMap<usize, _> = [4900, 4900 * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|n| (n, a_disjunction_of_many_moduli(n)))
        .collect();
    zed_tests::scaling::check("a disjunction of many moduli", 4900, |n| {
        assert_eq!(zedc::store::presburger::decide(&formulas[&n]), Ok(true));
    });
}

#[test]
fn the_fails_questions_of_pairs_scale() {
    // PNCX-modular, R4 (R4-CLAUDE-3): the negation of a conjunction of clauses beside the
    // remainders' definitions is decided one negated clause at a time by the one-variable path,
    // order `n` per clause; it went to the general path, near `n^1.5` per doubling.
    let formulas: std::collections::BTreeMap<usize, _> = [8000, 8000 * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|n| (n, the_fails_question_of_pairs(n)))
        .collect();
    zed_tests::scaling::check("the fails questions of pairs", 8000, |n| {
        assert_eq!(zedc::store::presburger::decide(&formulas[&n]), Ok(true));
    });
}

#[test]
fn the_questions_of_negated_residues_over_distinct_bounds_scale() {
    // PNCX-modular, R2: the one-variable path multiplied a disjunction of conjunctions out into
    // clauses, 2^n of them for the `n` parts of the negated body (0.3 s at 16 parts); such a
    // disjunction is now left to the general path, and each question costs order `n`.
    questions_scale_unit(
        "negated residues over distinct bounds",
        1000,
        negated_residues_over_distinct_bounds,
    );
}
