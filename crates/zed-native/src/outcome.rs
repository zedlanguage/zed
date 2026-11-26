//! A native run's outcome and the running of generated code, shared by the JIT
//! ([`run`](crate::run)) and a linked executable's start (`exe`), in a file of its own so that the
//! start does not import the crate root, which imports it (step S.1f: no import cycle between
//! files).

use std::sync::Arc;

use zed_kernel::{Evaluator, Value, World};
use zed_rt::code::CodeMap;
use zed_rt::{Stack, Stats, Word};

use crate::hooks;
use crate::tables::Tables;

/// What one native run gives.
#[derive(Clone, Debug)]
pub struct Outcome {
    /// The program's value.
    pub value: Value,
    /// The heap's counts.
    pub stats: Stats,
    /// How many nodes the kernel ran for the runtime.
    pub kernel_calls: u64,
    /// How many calls by name ran through a placed entry, sent there by the merge kept for the
    /// call's node (`hooks::rt_direct`).
    pub placed_calls: u64,
    /// The entries of the heap's table of uncounted values when the run ends.
    pub table: usize,
    /// The cells the heap holds when the run ends, live or free.
    pub cells: usize,
}

/// Runs the generated code entered at `root`, made from the tables `t`, the kernel in `ev`
/// running the nodes the runtime does not: the JIT's way and a linked executable's. An error
/// comes with the number of the node that raised it, when a node did (plan row RT-sites).
/// With `code`, the map of the code, a fault in it that no rule of the language explains
/// stops the process as a bug in zedc (plan row RT-internal-fault): an executable's way. The
/// JIT runs inside a test's process, whose own faults that handler must not take.
pub(crate) fn call(
    t: Arc<Tables>,
    root: extern "C" fn() -> Word,
    ev: &mut Evaluator,
    code: Option<&CodeMap<'_>>,
) -> Result<Outcome, (String, Option<usize>)> {
    // Generated code recurses on the machine stack once per Zed call and keeps a function's
    // words in its frame, so it runs on a stack as large as memory (COMPLEXITY.md R10), mapped
    // before the run's state is installed so that a failure leaves nothing to undo.
    let stack = Stack::new().map_err(|e| (e, None))?;
    let taken = std::mem::replace(ev, Evaluator::new(World::new()));
    hooks::install(hooks::State::new(t, taken));
    let w = match code {
        Some(map) => stack.run_mapped(map, root),
        None => Ok(stack.run(root)),
    };
    let w = match w {
        Ok(w) => w,
        // The system refused a handler: nothing ran, and the evaluator goes back to `ev`.
        Err(e) => {
            *ev = hooks::remove().run.ev;
            return Err((e, None));
        }
    };
    drop(stack);
    let mut s = hooks::remove();
    let r = hooks::finish(&s.t, &mut s.run, w);
    *ev = s.run.ev;
    // The hooks record the node's index in the tables; the sites are by its number in the
    // graph, which counts the nodes of the bodies the kernel runs too.
    // Cannot panic: N1 (hooks.rs); `err_at` is only ever the `id` a node's hook got (`fail`).
    let at = s.run.err_at.map(|i| s.t.nodes[i].number);
    Ok(Outcome {
        value: r.map_err(|e| (e, at))?,
        stats: s.run.heap.stats,
        kernel_calls: s.run.kernel_calls,
        placed_calls: s.run.placed_calls,
        table: s.run.heap.table_len(),
        cells: s.run.heap.cell_slots(),
    })
}
