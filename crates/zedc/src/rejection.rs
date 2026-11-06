//! The rows of the rejection table (DESIGN.md sec:diagnostics, "What a rejection owes"). Each
//! diagnostic of a rejection the table lists names its row, and every `// ✗ Row: …` comment
//! names the row it is checked against (step L1.21). The names are the table's first column up to
//! any parenthesis; the sync tool copies them into `zed/fences/rejections.txt`, and a test
//! holds this list equal to that copy.

/// Declares `Row`, each variant documented by its name, with `Row::ALL` and `Row::name`.
macro_rules! rows {
    ($($row:ident => $name:literal,)*) => {
        /// A row of the rejection table.
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
        pub enum Row {
            $(#[doc = $name] $row,)*
        }

        impl Row {
            /// Every row, in the table's order.
            pub const ALL: &[Row] = &[$(Row::$row,)*];

            /// The row's name: its first column in the table, up to any parenthesis.
            pub fn name(self) -> &'static str {
                match self {
                    $(Row::$row => $name,)*
                }
            }
        }
    };
}

rows! {
    Collision => "Collision",
    UnliftedCarrier => "Unlifted carrier",
    MissingAlgebraicObligation => "Missing algebraic obligation",
    UndischargeableEnsure => "Undischargeable `@ensure`",
    UnsatisfiableConstraints => "Unsatisfiable declared constraints",
    QuantifierNotFinite => "Quantifier in a law over a domain that is not finite",
    BelowProofGrade =>
        "Obligation below proof grade under `--strict` / `@proved` / `total` / `@decides`",
    NonExhaustiveMatch => "Non-exhaustive `match`",
    UnreachableArm => "Unreachable `match` arm",
    FoldWithNone => "`.fold` on a type that has none",
    MapOutsideValues => "`.map` at a parameter outside the value positions",
    PositionalMap =>
        "Positional `.map`, or a name that is no parameter, on a value that is not a morphism",
    KeyOutsideBound => "Key outside the permission bound",
    UndischargedRegion => "Undischarged region assertion",
    ReadBelowDomain => "Read below the domain with no boundary entry",
    OverlappingArrows => "Cross-unit overlapping incomparable arrows",
    AmbiguousImport => "Ambiguous imported name",
    NeedInCallerScope => "Need met only by an arrow in the caller's scope",
    MemberTwice =>
        "Two members of one name with different declarations in a struct or interface body",
    PathLeavesPackage =>
        "File read at the compile-time stage by a path that leaves the package root",
    StalePin => "Pinned file whose content no longer matches its pin",
    ImportCycle => "Import cycle",
    OrderWithNone =>
        "Order read on a level with no natural order — origin keys outside their `Seq`",
    TwoOrders => "Two declared orders meet in one key type",
    EmissionDisjointness => "Emission-disjointness",
    Rebinding => "Rebinding in the same scope",
    BinderNamingType => "Binder naming a type",
    NoCommonCarrier => "Two numeric values with no common carrier",
    UnusedMatchBinder => "Match binder unused in its guard and arm",
    CapitalizedFreeName => "Capitalized free name used once in a signature and nowhere in the body",
    RemapOutputName =>
        "Remap output name that names a source level and resolves to a value in scope",
    MethodOnValue => "Method declared on a value",
    PrefixMinus => "Prefix `-` on a numeric literal's postfix chain",
    DisplayInBody => "Display in body position",
    NamedBeforePositional => "Named argument before a positional one",
    PositionalAfterNamed => "`positional` parameter after a named one",
    WrongForm => "Argument in the wrong form",
    ParameterKinds => "Function whose parameter kinds do not fit the expected function type",
    MissingArgument => "Missing argument",
    NothingLeftOut => "`...` with no named parameter left out",
    PositionalConstructor => "Positional constructor call or pattern",
    InnerDomain => "Inner-domain dependency outside the fragment",
    AmbiguousAtCarrier => "Operator or literal ambiguous at a theory's carrier",
    NoFieldAtCarrier => "Operator or literal at a theory's carrier with no field to name",
    GenericInstance => "Instance of a generic definition that fails to type",
    UnboundedSize => "Size with no proven bound under `@preallocated` or the `preallocated` mode",
    CellReadsItself => "Cell read on a path back to its own cell",
    MeaningCase => "Meaning function with a case `@decides` cannot reify",
    NonLinearQuestion =>
        "Linear question outside the polynomial fragment of the linear-relation domain",
    WritesNothing => "Statement that writes nothing, or drops a declared result",
    StateValueCycle => "Cycle through state and value edges",
    NoArrowAtCarrier => "Operator with no arrow at its operands' carrier",
    UnitsDiffer => "Units that differ where an operation requires equal ones",
    TaintAtSink => "Taint at a sink whose parameter does not take it",
}

impl Row {
    /// The row a `✗` comment names: the text after the `✗` begins with the row's name and a
    /// colon, as in `// ✗ Collision: …`. A comment that names no row gives `None`.
    pub fn named_by(comment: &str) -> Option<Row> {
        let text = comment.trim_start();
        Row::ALL.iter().copied().find(|r| {
            text.strip_prefix(r.name())
                .is_some_and(|rest| rest.starts_with(':'))
        })
    }
}
