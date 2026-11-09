//! The report against brute force on small theories: every choice of every field is tried, and
//! each law is evaluated at every binding by applying the fields as functions, with no use of
//! the paths, cubes or search of the report.

use zed_tests::instances::Rng;

use super::trivial::{
    Choice, End, Mode, Rel, Report, Term, Theory, choices, in_forest_fragment, render, report,
};

/// The value of `term` when each field `f` is the function `choice[f]` and the binders are
/// `binding`; every argument is evaluated, as a call does.
fn eval(t: &Theory, term: usize, choice: &[Choice], binding: &[u32]) -> u32 {
    match &t.terms[term] {
        Term::Var(v) => binding[*v],
        Term::App { field, args } => {
            let values: Vec<u32> = args.iter().map(|&a| eval(t, a, choice, binding)).collect();
            match choice[*field] {
                c @ (0 | 1) => c,
                p => values[(p - 2) as usize],
            }
        }
    }
}

/// Whether every law holds at every binding of its binders to values in `0..carrier`.
fn satisfies(t: &Theory, choice: &[Choice], carrier: u32) -> bool {
    t.laws.iter().all(|law| {
        let v = law.binders.len() as u32;
        (0..carrier.pow(v)).all(|code| {
            let binding: Vec<u32> = (0..v).map(|i| code / carrier.pow(i) % carrier).collect();
            law.body.iter().any(|conj| {
                conj.iter().all(|a| {
                    let (l, r) = (
                        eval(t, a.lhs, choice, &binding),
                        eval(t, a.rhs, choice, &binding),
                    );
                    match a.rel {
                        Rel::Eq => l == r,
                        Rel::Ne => l != r,
                    }
                })
            })
        })
    })
}

/// Every model on two values, as the choice of every field, in mixed-radix order.
pub fn models(t: &Theory) -> Vec<Vec<Choice>> {
    let radix: Vec<u32> = t.fields.iter().map(|f| choices(f.arity)).collect();
    let mut choice = vec![0; t.fields.len()];
    let mut out = Vec::new();
    loop {
        if satisfies(t, &choice, 2) {
            out.push(choice.clone());
        }
        let Some(i) = (0..choice.len()).find(|&i| choice[i] + 1 < radix[i]) else {
            return out;
        };
        choice[i] += 1;
        choice[..i].fill(0);
    }
}

/// Whether the one-value model satisfies every law: each field returns the one value, so every
/// binding and every choice is `0`.
pub fn one_value_holds(t: &Theory) -> bool {
    satisfies(t, &vec![0; t.fields.len()], 1)
}

/// The models a complete report describes: the product of its groups' lists and the free
/// fields' choices, as full choices sorted.
pub fn expand(t: &Theory, r: &Report) -> Vec<Vec<Choice>> {
    if !r.closed_fail.is_empty() {
        return Vec::new();
    }
    let mut out: Vec<Vec<Choice>> = vec![vec![0; t.fields.len()]];
    for g in &r.groups {
        out = out
            .iter()
            .flat_map(|partial| {
                g.models.iter().map(move |m| {
                    let mut next = partial.clone();
                    for (&f, &c) in g.fields.iter().zip(m) {
                        next[f] = c;
                    }
                    next
                })
            })
            .collect();
    }
    for &f in &r.free {
        out = out
            .iter()
            .flat_map(|partial| {
                (0..choices(t.fields[f].arity)).map(move |c| {
                    let mut next = partial.clone();
                    next[f] = c;
                    next
                })
            })
            .collect();
    }
    out.sort();
    out
}

/// The fields and laws of `t`, for a failure message.
pub fn describe(t: &Theory) -> String {
    let fields: Vec<String> = t
        .fields
        .iter()
        .map(|f| format!("{}/{}", f.name, f.arity))
        .collect();
    let laws: Vec<String> = t
        .laws
        .iter()
        .map(|l| format!("law {}({}) = {}", l.name, l.binders.join(", "), l.text))
        .collect();
    format!("fields {}\n{}", fields.join(", "), laws.join("\n"))
}

/// A random term of depth at most `depth` over `t`'s fields and the binders `binders`.
fn random_term(rng: &mut Rng, t: &Theory, binders: &[&str], depth: usize) -> String {
    let leaf = depth == 0 || rng.below(3) == 0;
    let nullary: Vec<usize> = (0..t.fields.len())
        .filter(|&f| t.fields[f].arity == 0)
        .collect();
    if leaf && !binders.is_empty() && (nullary.is_empty() || rng.below(3) > 0) {
        return rng.pick(binders).to_string();
    }
    if leaf && !nullary.is_empty() {
        return t.fields[rng.pick(&nullary)].name.clone();
    }
    let f = rng.below(t.fields.len());
    let field = &t.fields[f];
    if field.arity == 0 {
        return field.name.clone();
    }
    let args: Vec<String> = (0..field.arity)
        .map(|_| random_term(rng, t, binders, depth.saturating_sub(1)))
        .collect();
    format!("{}({})", field.name, args.join(", "))
}

/// A random theory of one to five fields of at most two arguments and one to four laws, with
/// `||` and `&&` now and then.
pub fn random_theory(rng: &mut Rng) -> Theory {
    let mut t = Theory::new("Random");
    let n = 1 + rng.below(5);
    for i in 0..n {
        t.field(&format!("f{i}"), rng.below(3));
    }
    for l in 0..1 + rng.below(4) {
        let binders: &[&str] = match rng.below(4) {
            0 => &[],
            1 => &["a"],
            2 => &["a", "b"],
            _ => &["a", "b", "c"],
        };
        // A term with no binder needs a field of no arguments to end at.
        let binders = if binders.is_empty() && t.fields.iter().all(|f| f.arity > 0) {
            &["a"]
        } else {
            binders
        };
        let mut disjuncts = Vec::new();
        for _ in 0..if rng.below(5) == 0 { 2 } else { 1 } {
            let mut atoms = Vec::new();
            for _ in 0..if rng.below(5) == 0 { 2 } else { 1 } {
                let rel = if rng.below(6) == 0 { "!=" } else { "==" };
                let l = random_term(rng, &t, binders, 2);
                let r = random_term(rng, &t, binders, 2);
                atoms.push(format!("{l} {rel} {r}"));
            }
            disjuncts.push(atoms.join(" && "));
        }
        t.law(
            &format!("l{l}"),
            &binders.join(" "),
            &disjuncts.join(" || "),
        );
    }
    t
}

/// Checks every report of `t` against brute force, and returns the dead ends of the exhaustive
/// search.
fn check(t: &Theory) -> u64 {
    let full = report(t, Mode::Exhaustive);
    let mut want = models(t);
    want.sort();
    let got = expand(t, &full);
    let text = || format!("{}\n{}", describe(t), render(t, &full));
    assert_eq!(got, want, "models differ\n{}", text());
    assert_eq!(
        full.one_value_fails.is_none(),
        one_value_holds(t),
        "the one-value model differs\n{}",
        text()
    );
    // The default report lists a prefix of the exhaustive list, in the same order.
    let short = report(t, Mode::Default);
    for (s, g) in short.groups.iter().zip(&full.groups) {
        assert!(
            g.models.starts_with(&s.models),
            "the default report lists other models\n{}",
            text()
        );
        match &s.end {
            End::Complete => assert_eq!(s.models, g.models, "{}", text()),
            End::Several => assert!(s.models.len() == 2, "{}", text()),
            End::Stopped(_) => assert!(g.dead_ends > 0, "{}", text()),
        }
        // A search with no dead end tries only choices that lead to a model, so it makes at most
        // one choice per field per model.
        if g.dead_ends == 0 {
            assert!(
                g.nodes <= (g.models.len() * g.fields.len()) as u64,
                "{} choices for {} models of {} fields\n{}",
                g.nodes,
                g.models.len(),
                g.fields.len(),
                text()
            );
        }
    }
    full.groups.iter().map(|g| g.dead_ends).sum()
}

#[test]
fn the_report_agrees_with_brute_force_on_random_theories() {
    let mut rng = Rng::new(0x7121_7a11);
    let (mut forest, mut forest_dead, mut other, mut other_dead) = (0, 0, 0, 0);
    for _ in 0..4000 {
        let t = random_theory(&mut rng);
        let dead = check(&t);
        if in_forest_fragment(&t) {
            forest += 1;
            assert_eq!(
                dead,
                0,
                "a theory in the forest fragment reached a dead end\n{}",
                describe(&t)
            );
            forest_dead += dead;
        } else {
            other += 1;
            other_dead += u64::from(dead > 0);
        }
    }
    eprintln!(
        "random theories: {forest} in the forest fragment ({forest_dead} dead ends), {other} \
         outside it ({other_dead} with a dead end)"
    );
    assert!(forest >= 500, "too few theories in the fragment: {forest}");
}
