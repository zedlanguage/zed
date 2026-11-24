// `entails` end to end on the star, through the public interface only, so the same file runs
// on the code before the factored solver (the red run of PRES-products-factored-solver): the
// premises are the k rows `x + u_i >= 0` and the k rows `y + w_j >= 0`, the goal `x * y >= 0`.
// `products` listed the k² pairs of rows on x and y before the factored solver, so this bench
// grew about 64 times at 8 times k there; the factored solver lists none (each product holds
// its free atom `u_i * w_j` alone).

use crate::presburger::{Atom, Con, Factor, Formula, Lin, Rel, Relation, Shared, entails};

fn star_relations(k: usize) -> (Relation, Relation) {
    let s = |n: String| Factor::Sym(std::sync::Arc::from(n));
    let (x, y) = (s("x".into()), s("y".into()));
    let mut fs = Vec::with_capacity(2 * k);
    for (f, other) in [(&x, "u"), (&y, "w")] {
        for i in 0..k {
            let mut l = Lin::atom(f.atom());
            l.plus_assign(&Lin::atom(s(format!("{other}{i}")).atom()));
            fs.push(Formula::Con(Con {
                lin: l,
                rel: Rel::Ge,
            }));
        }
    }
    let goal = Formula::Con(Con {
        lin: Lin::atom(Atom::product_of(x, y)),
        rel: Rel::Ge,
    });
    (
        Relation::of(Formula::And(Shared::new(fs))),
        Relation::of(goal),
    )
}

#[test]
fn bench_entails_on_the_star() {
    let (p, g) = star_relations(3);
    println!("k=3: {:?}", entails(&p, &g));
    crate::scaling::check_inputs("entails on the star", 1000, star_relations, |(p, g)| {
        std::hint::black_box(entails(p, g));
    });
}
