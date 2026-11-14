//! The validator's rules, each broken alone in an otherwise valid graph, and each graph shape it
//! accepts: the inputs, outputs and regions of every operation, the kinds and arguments of
//! regions, and the paths a port's state edge may take (DESIGN L1.31).

use super::{rejected, round};

/// A function that pushes its argument to `stdout`, called twice: the lambda's region takes
/// the state after its parameter and returns it after its value, and each `apply` takes the
/// state after its arguments and gives it back after its value.
const SAY_TWICE: &str = "\
zir 1
r region port (state stdout)
r.0 lambda () -> (_)
r.0/0 region function (_; state stdout)
r.0/0.0 port push stdout (r.0/0^1, r.0/0^0) -> (_; state stdout)
r.0/0 results (r.0/0.0^0, r.0/0.0^1)
r.1 apply (r.0^0, \"a\", r^0) -> (_; state stdout)
r.2 apply (r.0^0, \"b\", r.1^1) -> (_; state stdout)
r.3 prim tuple (r.1^0, r.2^0) -> (_)
r results (r.3^0, r.2^1)
";

/// The graphs the validator accepts, one per shape it checks, each through every round trip.
const ACCEPTED: &[(&str, &str)] = &[
    ("a lambda and two applies thread one port", SAY_TWICE),
    (
        "a function with no nodes and no results",
        "zir 1\nr region function ()\nr results ()\n",
    ),
    (
        "a lambda that takes two ports returns both states in the order of its arguments",
        "zir 1\nr region port (state a; state b)\nr.0 lambda () -> (_)\nr.0/0 region function (state a; state b)\nr.0/0.0 port push b (r.0/0^1, 1) -> (_; state b)\nr.0/0.1 port push a (r.0/0^0, 2) -> (_; state a)\nr.0/0 results (r.0/0.1^0, r.0/0.1^1, r.0/0.0^1)\nr.1 apply (r.0^0, r^0, r^1) -> (_; state a; state b)\nr results (r.1^0, r.1^1, r.1^2)\n",
    ),
    (
        "an if threads two states, one arm pushing and one passing both through",
        "zir 1\nr region port (state in; state out)\nr.0 port read in (r^0) -> (String; state in)\nr.1 prim == (r.0^0, \"x\") -> (bool)\nr.2 if (r.1^0, r.0^1, r^1) -> (int; state in; state out)\nr.2/0 region match (state in; state out)\nr.2/0.0 port push out (r.2/0^1, \"yes\") -> (_; state out)\nr.2/0 results (1, r.2/0^0, r.2/0.0^1)\nr.2/1 region match (state in; state out)\nr.2/1 results (0, r.2/1^0, r.2/1^1)\nr results (r.2^0, r.2^1, r.2^2)\n",
    ),
    (
        "a match threads a state after its pattern's binders",
        "zir 1\nr region port ((| #none (#some (tuple int))); state out)\nr.0 match [#some(n), #none] (r^0, r^1) -> (int; state out)\nr.0/0 region match (int; state out)\nr.0/0.0 port push out (r.0/0^1, r.0/0^0) -> (_; state out)\nr.0/0 results (r.0/0^0, r.0/0.0^1)\nr.0/1 region match (state out)\nr.0/1 results (0, r.0/1^0)\nr results (r.0^0, r.0^1)\n",
    ),
    (
        "a wave with two ports",
        "zir 1\nr region port (state a; state b)\nr.0 wave (r^0, r^1) -> (state a; state b)\nr.0/0 region port (state a; state b)\nr.0/0.0 port push a (r.0/0^0, 1) -> (_; state a)\nr.0/0.1 port push b (r.0/0^1, 2) -> (_; state b)\nr.0/0 results (r.0/0.0^1, r.0/0.1^1)\nr results (r.0^0, r.0^1)\n",
    ),
    (
        "a gen that tests its guard after the step, with a capture",
        "zir 1\nr region function (int; int)\nr.0 gen after (r^0, r^1) -> (struct)\nr.0/0 region loop (int; int)\nr.0/0.0 prim - (r.0/0^0, r.0/0^1) -> (int)\nr.0/0 results (r.0/0.0^0)\nr.0/1 region loop (int; int)\nr.0/1.0 prim > (r.0/1^0, 0) -> (bool)\nr.0/1 results (r.0/1.0^0)\nr results (r.0^0)\n",
    ),
    (
        "a definedness fixpoint: its region takes the key and the function so far",
        "zir 1\nr region function (struct)\nr.0 fix definedness {} (r^0) -> (struct)\nr.0/0 region loop (int; struct)\nr.0/0 results (r.0/0^0)\nr results (r.0^0)\n",
    ),
    (
        "a reindex by a catalog entry",
        "zir 1\nr region function (struct; (-> _ _); (-> _ _))\nr.0 reindex catalog transpose (r^0, r^1, r^2) -> (struct)\nr results (r.0^0)\n",
    ),
    (
        "a discard and a fold with no identity",
        "zir 1\nr region function (struct; (-> _ bool); (-> (tuple int int) int))\nr.0 discard (r^0, r^1) -> (struct)\nr.1 fold 2 {} (r.0^0, r^2) -> (int)\nr results (r.1^0)\n",
    ),
    (
        "a scan and a join with captures, the join with two outputs",
        "zir 1\nr region function (struct; struct)\nr.0 scan (r^0) -> (struct)\nr.0/0 region function (struct)\nr.0/0 results (r.0/0^0)\nr.1 join (r.0^0, r^1) -> (struct; struct)\nr.1/0 region function (struct; struct)\nr.1/0 results (r.1/0^0, r.1/0^1)\nr results (r.1^0, r.1^1)\n",
    ),
    (
        "a primitive used as a value has no inputs",
        "zir 1\nr region function ()\nr.0 prim + () -> (_)\nr.1 prim neg () -> (_)\nr results (r.0^0, r.1^0)\n",
    ),
    (
        "a variadic primitive with no inputs and with three",
        "zir 1\nr region function ()\nr.0 prim tuple () -> (_)\nr.1 prim tuple (1, 2, 3) -> (_)\nr results (r.0^0, r.1^0)\n",
    ),
    (
        "an apply with no arguments and an apply of a captured function",
        "zir 1\nr region function ((-> (tuple) int); (-> int int))\nr.0 apply (r^0) -> (int)\nr.1 apply (r^1, r.0^0) -> (int)\nr results (r.1^0)\n",
    ),
    (
        "a rec of one function",
        "zir 1\nr region function ()\nr.0 rec () -> ((-> int int))\nr.0/0 region rec ((-> int int))\nr.0/0.0 lambda (r.0/0^0) -> ((-> int int))\nr.0/0.0/0 region function (int; (-> int int))\nr.0/0.0/0.0 apply (r.0/0.0/0^1, r.0/0.0/0^0) -> (int)\nr.0/0.0/0 results (r.0/0.0/0.0^0)\nr.0/0 results (r.0/0.0^0)\nr results (r.0^0)\n",
    ),
    (
        "a match on every pattern form",
        "zir 1\nr region function (_; int)\nr.0 match [=3, #a(), #b(x: n, y: _), #c(m, (p, q)), (is int), (k,), #_, _] (r^0, r^1) -> (int)\nr.0/0 region match (int)\nr.0/0 results (r.0/0^0)\nr.0/1 region match (int)\nr.0/1 results (r.0/1^0)\nr.0/2 region match (_; int)\nr.0/2 results (r.0/2^1)\nr.0/3 region match (_; _; _; int)\nr.0/3 results (r.0/3^3)\nr.0/4 region match (int)\nr.0/4 results (r.0/4^0)\nr.0/5 region match (_; int)\nr.0/5 results (r.0/5^1)\nr.0/6 region match (int)\nr.0/6 results (r.0/6^0)\nr.0/7 region match (int)\nr.0/7 results (r.0/7^0)\nr results (r.0^0)\n",
    ),
];

#[test]
fn each_shape_the_validator_accepts_round_trips() {
    let failed: Vec<&str> = ACCEPTED
        .iter()
        .filter(|(_, src)| std::panic::catch_unwind(|| round(src)).is_err())
        .map(|(what, _)| *what)
        .collect();
    assert!(failed.is_empty(), "rejected: {failed:#?}");
}

/// Each case: the rule broken, the text, and the message, which names the node or region at
/// fault by its path.
const BROKEN: &[(&str, &str, &str)] = &[
    // The inputs, outputs and regions of each operation.
    (
        "a derived node with no input",
        "zir 1\nr region function ()\nr.0 group () -> (struct)\nr.0/0 region function ()\nr.0/0 results (1)\nr results (r.0^0)\n",
        "r.0: a derived node has at least one input and one output",
    ),
    (
        "a derived node with no output",
        "zir 1\nr region function (struct)\nr.0 scan (r^0) -> ()\nr.0/0 region function (struct)\nr.0/0 results ()\nr results ()\n",
        "r.0: a derived node has at least one input and one output",
    ),
    (
        "an apply with no input",
        "zir 1\nr region function ()\nr.0 apply () -> (int)\nr results (r.0^0)\n",
        "r.0: `apply` has no function input",
    ),
    (
        "a match with no arm",
        "zir 1\nr region function (int)\nr.0 match [] (r^0) -> (int)\nr results (r.0^0)\n",
        "r.0: `match` has no arm",
    ),
    (
        "a rec with no output",
        "zir 1\nr region function ()\nr.0 rec () -> ()\nr.0/0 region rec ()\nr.0/0 results ()\nr results ()\n",
        "r.0: `rec` defines no function",
    ),
    (
        "a primitive with two outputs",
        "zir 1\nr region function (int)\nr.0 prim neg (r^0) -> (int; int)\nr results (r.0^0)\n",
        "r.0: `prim neg` has 1 output, and 2 are written",
    ),
    (
        "a primitive with no output",
        "zir 1\nr region function (int)\nr.0 prim neg (r^0) -> ()\nr results ()\n",
        "r.0: `prim neg` has 1 output, and 0 are written",
    ),
    (
        "a push with one output",
        "zir 1\nr region port (state out)\nr.0 port push out (r^0, 1) -> (state out)\nr results (r.0^0)\n",
        "r.0: `port push out` has 2 outputs, and 1 is written",
    ),
    (
        "a read with two inputs",
        "zir 1\nr region port (state in)\nr.0 port read in (r^0, 1) -> (String; state in)\nr results (r.0^1)\n",
        "r.0: `port read in` takes 1 input, and has 2",
    ),
    (
        "a push with one input",
        "zir 1\nr region port (state out)\nr.0 port push out (r^0) -> (_; state out)\nr results (r.0^1)\n",
        "r.0: `port push out` takes 2 inputs, and has 1",
    ),
    (
        "a discard with three inputs",
        "zir 1\nr region function (struct; (-> _ bool))\nr.0 discard (r^0, r^1, 1) -> (struct)\nr results (r.0^0)\n",
        "r.0: `discard` takes 2 inputs, and has 3",
    ),
    (
        "a reindex with two inputs",
        "zir 1\nr region function (struct; (-> _ _))\nr.0 reindex residue (r^0, r^1) -> (struct)\nr results (r.0^0)\n",
        "r.0: `reindex` takes 3 inputs, and has 2",
    ),
    (
        "a fold with an identity and two inputs",
        "zir 1\nr region function (struct; (-> (tuple int int) int))\nr.0 fold 1 identity {} (r^0, r^1) -> (int)\nr results (r.0^0)\n",
        "r.0: `fold` takes 3 inputs, and has 2",
    ),
    (
        "a fam with no input",
        "zir 1\nr region function ()\nr.0 fam () -> (struct)\nr.0/0 region function (String)\nr.0/0 results (1)\nr results (r.0^0)\n",
        "r.0: `fam` takes 1 input or more, and has 0",
    ),
    (
        "a lattice fixpoint with one input",
        "zir 1\nr region function (struct)\nr.0 fix lattice {} (r^0) -> (struct)\nr.0/0 region loop (struct)\nr.0/0 results (r.0/0^0)\nr results (r.0^0)\n",
        "r.0: `fix` takes 2 inputs or more, and has 1",
    ),
    (
        "a gen with no input",
        "zir 1\nr region function ()\nr.0 gen before () -> (struct)\nr.0/0 region loop (int)\nr.0/0 results (r.0/0^0)\nr.0/1 region loop (int)\nr.0/1 results (true)\nr results (r.0^0)\n",
        "r.0: `gen` takes 1 input or more, and has 0",
    ),
    (
        "an if with no condition",
        "zir 1\nr region function ()\nr.0 if () -> (int)\nr.0/0 region match ()\nr.0/0 results (1)\nr.0/1 region match ()\nr.0/1 results (2)\nr results (r.0^0)\n",
        "r.0: `if` takes 1 input or more, and has 0",
    ),
    (
        "a lambda with two outputs",
        "zir 1\nr region function ()\nr.0 lambda () -> (_; _)\nr.0/0 region function (int)\nr.0/0 results (r.0/0^0)\nr results (r.0^0)\n",
        "r.0: `lambda` has 1 output, and 2 are written",
    ),
    (
        "a primitive with a region",
        "zir 1\nr region function (int)\nr.0 prim neg (r^0) -> (int)\nr.0/0 region function ()\nr.0/0 results ()\nr results (r.0^0)\n",
        "r.0: `prim neg` has 0 regions, and 1 is written",
    ),
    (
        "a gen with one region",
        "zir 1\nr region function (int)\nr.0 gen before (r^0) -> (struct)\nr.0/0 region loop (int)\nr.0/0 results (r.0/0^0)\nr results (r.0^0)\n",
        "r.0: `gen` has 2 regions, and 1 is written",
    ),
    (
        "an if with three regions",
        "zir 1\nr region function (bool)\nr.0 if (r^0) -> (int)\nr.0/0 region match ()\nr.0/0 results (1)\nr.0/1 region match ()\nr.0/1 results (2)\nr.0/2 region match ()\nr.0/2 results (3)\nr results (r.0^0)\n",
        "r.0: `if` has 2 regions, and 3 are written",
    ),
    // The kinds, arguments and results of regions.
    (
        "an if arm that is a function region",
        "zir 1\nr region function (bool)\nr.0 if (r^0) -> (int)\nr.0/0 region function ()\nr.0/0 results (1)\nr.0/1 region match ()\nr.0/1 results (2)\nr results (r.0^0)\n",
        "r.0/0: region 0 of `if` must be a match region, and is written `function`",
    ),
    (
        "a wave whose region is a function region",
        "zir 1\nr region port (state out)\nr.0 wave (r^0) -> (state out)\nr.0/0 region function (state out)\nr.0/0 results (r.0/0^0)\nr results (r.0^0)\n",
        "r.0/0: region 0 of `wave` must be a port region, and is written `function`",
    ),
    (
        "a rec whose region is a function region",
        "zir 1\nr region function ()\nr.0 rec () -> ((-> int int))\nr.0/0 region function ((-> int int))\nr.0/0 results (r.0/0^0)\nr results (r.0^0)\n",
        "r.0/0: region 0 of `rec` must be a rec region, and is written `function`",
    ),
    (
        "a lambda whose region is a loop region",
        "zir 1\nr region function ()\nr.0 lambda () -> ((-> int int))\nr.0/0 region loop (int)\nr.0/0 results (r.0/0^0)\nr results (r.0^0)\n",
        "r.0/0: region 0 of `lambda` must be a function region, and is written `loop`",
    ),
    (
        "a gen guard that is a match region",
        "zir 1\nr region function (int)\nr.0 gen before (r^0) -> (struct)\nr.0/0 region loop (int)\nr.0/0 results (r.0/0^0)\nr.0/1 region match (int)\nr.0/1 results (true)\nr results (r.0^0)\n",
        "r.0/1: region 1 of `gen` must be a loop region, and is written `match`",
    ),
    (
        "a fam region missing its capture",
        "zir 1\nr region function (struct; int)\nr.0 fam (r^0, r^1) -> (struct)\nr.0/0 region function (String)\nr.0/0 results (r.0/0^0)\nr results (r.0^0)\n",
        "r.0/0: the region takes 1 argument from the node and 1 capture, 2 in all, and has 1",
    ),
    (
        "a definedness fixpoint region with one argument",
        "zir 1\nr region function (struct)\nr.0 fix definedness {} (r^0) -> (struct)\nr.0/0 region loop (int)\nr.0/0 results (r.0/0^0)\nr results (r.0^0)\n",
        "r.0/0: the region takes 2 arguments from the node and 0 captures, 2 in all, and has 1",
    ),
    (
        "a rec region with fewer arguments than functions",
        "zir 1\nr region function ()\nr.0 rec () -> ((-> int int); (-> int int))\nr.0/0 region rec ((-> int int))\nr.0/0 results (r.0/0^0, r.0/0^0)\nr results (r.0^0, r.0^1)\n",
        "r.0/0: the region takes 2 arguments from the node and 0 captures, 2 in all, and has 1",
    ),
    (
        "a lambda region with no result",
        "zir 1\nr region function ()\nr.0 lambda () -> ((-> int int))\nr.0/0 region function (int)\nr.0/0 results ()\nr results (r.0^0)\n",
        "r.0/0: the region must have 1 result, and 0 are written",
    ),
    (
        "a derived certificate with fewer results than outputs",
        "zir 1\nr region function (struct)\nr.0 join (r^0) -> (struct; struct)\nr.0/0 region function (struct)\nr.0/0 results (r.0/0^0)\nr results (r.0^0, r.0^1)\n",
        "r.0/0: the region must have 2 results, and 1 is written",
    ),
    // Where a state edge may go.
    (
        "a state edge into a loop region",
        "zir 1\nr region port (state out)\nr.0 gen before (1) -> (struct)\nr.0/0 region loop (state out)\nr.0/0 results (r.0/0^0)\nr.0/1 region loop (int)\nr.0/1 results (true)\nr results (r.0^0, r^0)\n",
        "r.0/0^0: a state edge cannot enter a loop region",
    ),
    (
        "a state edge into a rec region",
        "zir 1\nr region function ()\nr.0 rec () -> ((-> int int))\nr.0/0 region rec (state out)\nr.0/0 results (1)\nr results (r.0^0)\n",
        "r.0/0^0: a state edge cannot enter a rec region",
    ),
    (
        "a state captured into a fam",
        "zir 1\nr region port (struct; state out)\nr.0 fam (r^0, r^1) -> (struct)\nr.0/0 region function (String; state out)\nr.0/0 results (1)\nr results (r.0^0)\n",
        "r.0: input 1 of `fam` is a state edge",
    ),
    (
        "a state captured into a lambda",
        "zir 1\nr region port (state out)\nr.0 lambda (r^0) -> (_)\nr.0/0 region function (state out)\nr.0/0 results (1, r.0/0^0)\nr results (r.0^0)\n",
        "r.0: input 0 of `lambda` is a state edge",
    ),
    (
        "a state as the condition of an if",
        "zir 1\nr region port (state out)\nr.0 if (r^0) -> (int)\nr.0/0 region match ()\nr.0/0 results (1)\nr.0/1 region match ()\nr.0/1 results (2)\nr results (r.0^0)\n",
        "r.0: input 0 of `if` is a state edge",
    ),
    (
        "a primitive that gives a state",
        "zir 1\nr region function ()\nr.0 prim neg (1) -> (state out)\nr results (r.0^0)\n",
        "r.0: output 0 of `prim neg` is a state edge",
    ),
    (
        "a fam that gives a state",
        "zir 1\nr region function (struct)\nr.0 fam (r^0) -> (state out)\nr.0/0 region function (String)\nr.0/0 results (1)\nr results (r.0^0)\n",
        "r.0: output 0 of `fam` is a state edge",
    ),
    (
        "a push with a second state input",
        "zir 1\nr region port (state out; state in)\nr.0 port push out (r^0, r^1) -> (_; state out)\nr results (r.0^1, r^1)\n",
        "r.0: input 1 of `port push out` is a state edge",
    ),
    (
        "a push whose value output is a state",
        "zir 1\nr region port (state out)\nr.0 port push out (r^0, 1) -> (state out; state out)\nr results (r.0^1)\n",
        "r.0: `port push out` has outputs (a value; state out), and has (state out; state out)",
    ),
    (
        "a push that gives the state of another port",
        "zir 1\nr region port (state out)\nr.0 port push out (r^0, 1) -> (int; state in)\nr results (r.0^1)\n",
        "r.0: `port push out` has outputs (a value; state out), and has (int; state in)",
    ),
    (
        "a read whose first input is a value",
        "zir 1\nr region function ()\nr.0 port read in (1) -> (String; state in)\nr results (r.0^0)\n",
        "r.0: input 0 of `port read in` is 1, and must be `state in`",
    ),
    (
        "an apply whose function is a state",
        "zir 1\nr region port (state out)\nr.0 apply (r^0) -> (_; state out)\nr results (r.0^1)\n",
        "r.0: input 0 of `apply`, the function, is a state edge",
    ),
    (
        "an apply with a value after the state",
        "zir 1\nr region port (state stdout)\nr.0 lambda () -> (_)\nr.0/0 region function (_; state stdout)\nr.0/0.0 port push stdout (r.0/0^1, r.0/0^0) -> (_; state stdout)\nr.0/0 results (r.0/0.0^0, r.0/0.0^1)\nr.1 apply (r.0^0, r^0, \"a\") -> (_; state stdout)\nr results (r.1^0, r.1^1)\n",
        "r.1: input 2 of `apply` is a value after a state edge, and the states come after the arguments",
    ),
    (
        "an apply that does not give back the state it takes",
        "zir 1\nr region port (state stdout)\nr.0 lambda () -> (_)\nr.0/0 region function (_; state stdout)\nr.0/0.0 port push stdout (r.0/0^1, r.0/0^0) -> (_; state stdout)\nr.0/0 results (r.0/0.0^0, r.0/0.0^1)\nr.1 apply (r.0^0, \"a\", r^0) -> (_)\nr results (r.1^0)\n",
        "r.1: `apply` has outputs (a value; state stdout), the states it takes, and has (_)",
    ),
    (
        "an apply with no output",
        "zir 1\nr region function ((-> int int))\nr.0 apply (r^0, 1) -> ()\nr results ()\n",
        "r.0: `apply` has outputs (a value; ), the states it takes, and has ()",
    ),
    (
        "an apply whose first output is a state",
        "zir 1\nr region port (state stdout)\nr.0 lambda () -> (_)\nr.0/0 region function (_; state stdout)\nr.0/0.0 port push stdout (r.0/0^1, r.0/0^0) -> (_; state stdout)\nr.0/0 results (r.0/0.0^0, r.0/0.0^1)\nr.1 apply (r.0^0, \"a\", r^0) -> (state stdout; _)\nr results (r.1^1, r.1^0)\n",
        "r.1: `apply` has outputs (a value; state stdout), the states it takes, and has (state stdout; _)",
    ),
    (
        "a lambda region that returns its state first",
        "zir 1\nr region port (state stdout)\nr.0 lambda () -> (_)\nr.0/0 region function (_; state stdout)\nr.0/0.0 port push stdout (r.0/0^1, r.0/0^0) -> (_; state stdout)\nr.0/0 results (r.0/0.0^1, r.0/0.0^0)\nr results (r.0^0, r^0)\n",
        "r.0/0: a lambda's region returns its value and then the state of each port it takes, in the order of its arguments (state stdout), and returns (state stdout, _)",
    ),
    (
        "a lambda region that returns two states out of order",
        "zir 1\nr region port (state a; state b)\nr.0 lambda () -> (_)\nr.0/0 region function (state a; state b)\nr.0/0 results (1, r.0/0^1, r.0/0^0)\nr results (r.0^0, r^0, r^1)\n",
        "r.0/0: a lambda's region returns its value and then the state of each port it takes, in the order of its arguments (state a, state b), and returns (1, state b, state a)",
    ),
    (
        "an arm that gives a state where the if gives a value",
        "zir 1\nr region port (state out)\nr.0 if (true, r^0) -> (int)\nr.0/0 region match (state out)\nr.0/0 results (r.0/0^0)\nr.0/1 region match (state out)\nr.0/1 results (r.0/1^0)\nr results (r.0^0)\n",
        "r.0/0: result 0 is state out, and output 0 is int",
    ),
    (
        "an arm that gives the state of another port",
        "zir 1\nr region port (state in; state out)\nr.0 if (true, r^0, r^1) -> (int; state in; state out)\nr.0/0 region match (state in; state out)\nr.0/0 results (1, r.0/0^1, r.0/0^0)\nr.0/1 region match (state in; state out)\nr.0/1 results (2, r.0/1^0, r.0/1^1)\nr results (r.0^0, r.0^1, r.0^2)\n",
        "r.0/0: result 1 is state out, and output 1 is state in",
    ),
    (
        "an arm that gives a value where the if gives a state",
        "zir 1\nr region port (state out)\nr.0 if (true) -> (int; state out)\nr.0/0 region match ()\nr.0/0 results (1, 2)\nr.0/1 region match ()\nr.0/1 results (1, 2)\nr results (r.0^0, r.0^1, r^0)\n",
        "r.0/0: result 1 is 2, and output 1 is state out",
    ),
];

#[test]
fn each_broken_rule_names_the_node_and_the_rule() {
    let wrong: Vec<String> = BROKEN
        .iter()
        .filter(|(_, src, want)| rejected(src) != *want)
        .map(|(what, src, want)| format!("{what}:\n  got  {}\n  want {want}", rejected(src)))
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
