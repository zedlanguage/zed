//! The weak topological order of a dependency graph (DESIGN.md sec:domains, fixed by step
//! M0.5), computed by Bourdoncle's algorithm [Bourdoncle, "Efficient chaotic iteration
//! strategies with widenings", 1993, figure 4].
//!
//! The vertices are `0..n` in source order, and each vertex's successors are listed in source
//! order; the depth-first traversal starts from the vertices in that order and visits
//! successors in that order. A graph has many weak topological orders, and this traversal
//! picks one, so the order, and with it the widening points, is a function of the source.

use std::fmt;

/// An element of a weak topological order: a vertex, or a component with its head and body.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Element {
    /// A vertex on no cycle through the enclosing head.
    Vertex(usize),
    /// A strongly connected part, iterated as a loop: the head, where widening happens, and
    /// the order of the rest, with the edges into the head removed.
    Component {
        /// The head: the first vertex of the component the traversal reaches.
        head: usize,
        /// The weak topological order of the rest of the component.
        body: Vec<Element>,
    },
}

impl Element {
    /// The vertices of the element, in order.
    pub fn vertices(&self) -> Vec<usize> {
        match self {
            Element::Vertex(v) => vec![*v],
            Element::Component { head, body } => {
                let mut out = vec![*head];
                out.extend(body.iter().flat_map(Element::vertices));
                out
            }
        }
    }
}

impl fmt::Display for Element {
    /// Bourdoncle's notation: `0 (1 2 (3 4)) 5`, a component in parentheses, head first.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Element::Vertex(v) => write!(f, "{v}"),
            Element::Component { head, body } => {
                write!(f, "({head}")?;
                for e in body {
                    write!(f, " {e}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// Prints an order in Bourdoncle's notation.
pub fn show(order: &[Element]) -> String {
    order
        .iter()
        .map(|e| e.to_string())
        .collect::<Vec<_>>()
        .join(" ")
}

/// The weak topological order of the graph whose vertex `v` has the successors `succ[v]`.
///
/// The recursion is as deep as the longest simple path; the store's graphs are the program's
/// own value graph, which the M0.11 limit of 20 000 nested calls bounds in the same way.
pub fn weak_topological_order(succ: &[Vec<usize>]) -> Vec<Element> {
    let mut b = Bourdoncle {
        succ,
        dfn: vec![Dfn::Unvisited; succ.len()],
        num: 0,
        stack: Vec::new(),
    };
    let mut partition = Vec::new();
    for v in 0..succ.len() {
        if b.dfn[v] == Dfn::Unvisited {
            b.visit(v, &mut partition);
        }
    }
    partition.reverse();
    partition
}

/// A vertex's depth-first number: unvisited, on the current path or stack, or finished.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Dfn {
    Unvisited,
    Number(usize),
    Done,
}

struct Bourdoncle<'a> {
    succ: &'a [Vec<usize>],
    dfn: Vec<Dfn>,
    num: usize,
    stack: Vec<usize>,
}

impl Bourdoncle<'_> {
    /// Visits `v`, appending each finished element to `partition` (reversed by the caller,
    /// where the paper prepends), and returns the least depth-first number `v` reaches.
    fn visit(&mut self, v: usize, partition: &mut Vec<Element>) -> Dfn {
        self.stack.push(v);
        self.num += 1;
        self.dfn[v] = Dfn::Number(self.num);
        let mut head = self.dfn[v];
        let mut is_loop = false;
        for &w in &self.succ[v] {
            let min = match self.dfn[w] {
                Dfn::Unvisited => self.visit(w, partition),
                d => d,
            };
            if min <= head {
                head = min;
                is_loop = true;
            }
        }
        if head == self.dfn[v] {
            self.dfn[v] = Dfn::Done;
            let mut e = self.stack.pop().expect("v is on the stack");
            if is_loop {
                while e != v {
                    self.dfn[e] = Dfn::Unvisited;
                    e = self.stack.pop().expect("v is below e");
                }
                let c = self.component(v);
                partition.push(c);
            } else {
                partition.push(Element::Vertex(v));
            }
        }
        head
    }

    /// The component headed by `v`, whose other vertices have just been reset to unvisited.
    fn component(&mut self, v: usize) -> Element {
        let mut body = Vec::new();
        for &w in &self.succ[v] {
            if self.dfn[w] == Dfn::Unvisited {
                self.visit(w, &mut body);
            }
        }
        body.reverse();
        Element::Component { head: v, body }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_chain_has_no_component() {
        let order = weak_topological_order(&[vec![1], vec![2], vec![]]);
        assert_eq!(show(&order), "0 1 2");
    }

    #[test]
    fn an_inner_loop_is_a_component_inside_the_outer_one() {
        // A loop 2 → 3 → 4 → 5 → 6 → 2 with an inner loop 4 ⇄ 5 and an exit 6 → 7. The inner
        // head is 4, which the traversal reaches before 5.
        let succ = vec![
            vec![1],
            vec![2, 7],
            vec![3],
            vec![4, 6],
            vec![5],
            vec![4, 6],
            vec![2, 7],
            vec![],
        ];
        assert_eq!(show(&weak_topological_order(&succ)), "0 1 (2 3 (4 5) 6) 7");
    }

    #[test]
    fn a_self_loop_is_a_component() {
        let order = weak_topological_order(&[vec![0, 1], vec![]]);
        assert_eq!(show(&order), "(0) 1");
        assert_eq!(order[0].vertices(), vec![0]);
    }
}
