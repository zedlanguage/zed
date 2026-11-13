//! The kinds of refusal the checker has today, each found in a diagnostic by a phrase of its
//! reason that no other kind's reason holds. The list follows the code: the solver's
//! `presburger::Refusal` (Growth, Shadows, Disjuncts, Tie, Unordered) and the reduced
//! product's `Cause::Holes`; the memory refused for a constant written as a power; the type
//! checks' `types::Refusal` (Fork, Residues, TupleSplit, SharedCells, MorphismSplit, NoWitness,
//! Group); the two refused arrow combinations of `ty.rs`, its functions at one place left
//! unpaired (`Forms::tie`, FunctionPairs) and its unions whose shape is not chosen
//! (`unchosen_text`, Unchosen); and the normal form's `poly::Refused` (PolyWork,
//! PolyExponent). A diagnostic that says it could not decide, or that the
//! checker does not try, and holds none of these phrases is of kind `Other`, so a new kind
//! fails the census until it is named here.

/// A kind of refusal: its name in the census and the phrase of its reason that marks it.
pub struct Kind {
    pub name: &'static str,
    pub phrase: &'static str,
}

/// Every kind, in the order the census lists them.
pub const KINDS: &[Kind] = &[
    Kind {
        name: "Growth",
        phrase: "removing any one of them would leave more conditions than there are now",
    },
    Kind {
        name: "Shadows",
        phrase: "would have to be split again with as many",
    },
    Kind {
        name: "Disjuncts",
        phrase: "no choice it tried has values that meet every condition",
    },
    Kind {
        name: "Tie",
        phrase: "Its next step must choose among the variables",
    },
    Kind {
        name: "Unordered",
        phrase: "so only their names could order the search",
    },
    Kind {
        name: "Holes",
        phrase: "the ends of such names are found exactly when at most two of them have holes",
    },
    Kind {
        name: "PowerMemory",
        phrase: "the system refused the memory",
    },
    Kind {
        name: "Fork",
        phrase: "following both at once can take time exponential in the size of the types",
    },
    Kind {
        name: "Residues",
        phrase: "allow list lengths that repeat with a period",
    },
    Kind {
        name: "TupleSplit",
        phrase: "is decided only by splitting more than one of its components into cases at once",
    },
    Kind {
        name: "SharedCells",
        phrase: "comparing every pair of them takes time that grows with the square of their number",
    },
    Kind {
        name: "MorphismSplit",
        phrase: "is decided neither by the types its arguments must have nor by splitting it",
    },
    Kind {
        name: "NoWitness",
        phrase: "could neither show that no value has the type nor build a value that has it",
    },
    Kind {
        name: "Group",
        phrase: "deciding such a group takes time that grows with the square of its size",
    },
    Kind {
        name: "ArrowSplit",
        phrase: "arrows are combined only when they differ at one parameter",
    },
    Kind {
        name: "ArrowMeet",
        phrase: "the checker works that out only for arrows that each take all",
    },
    Kind {
        name: "FunctionPairs",
        phrase: "the checker does not try every way of pairing them",
    },
    Kind {
        name: "Unchosen",
        phrase: "through those shapes for one of the two only",
    },
    Kind {
        name: "PolyWork",
        phrase: " ms, more than 250 ms.",
    },
    Kind {
        name: "PolyExponent",
        phrase: ": an exponent is above",
    },
];

/// Phrases with which a diagnostic says that a question was not decided. A diagnostic holding
/// one of them and no phrase of [`KINDS`] is a refusal of kind `Other`.
const UNDECIDED: &[&str] = &[
    "could not decide",
    "not proved wrong",
    "does not try",
    "Cannot find exactly",
    "could not work out",
    "Cannot expand",
];

/// The kinds of refusal `text`, a diagnostic's message, steps and menu, reports: each kind
/// whose phrase it holds, in the order of [`KINDS`]; `["Other"]` when it says a question was
/// not decided and holds no kind's phrase; and none when it is no refusal. O(the kinds times
/// the text).
pub fn of(text: &str) -> Vec<&'static str> {
    let found: Vec<&'static str> = KINDS
        .iter()
        .filter(|k| text.contains(k.phrase))
        .map(|k| k.name)
        .collect();
    if found.is_empty() && UNDECIDED.iter().any(|p| text.contains(p)) {
        return vec!["Other"];
    }
    found
}
