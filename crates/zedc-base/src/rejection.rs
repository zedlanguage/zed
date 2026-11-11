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
    // No diagnostic uses this row yet: plan row ST-B4 emits it.
    LoopedAlternatives => "A test whose `||` alternatives limit each other's ranges in a loop",
    // No diagnostic uses this row yet: plan row H10-refuse emits it.
    UndecidablePremise => "Undecidable premise class",
    // No diagnostic uses this row yet: plan row HULL-conic emits it.
    NumberTooWide => "Number too wide to factor",
    // No diagnostic uses this row yet: plan row ASSOC-select emits it.
    SelectionKeysNotInOneOrder => "Selection keys not in one order",
    // No diagnostic uses this row yet: plan row ASSOC-table emits it.
    TableLawNotDecided => "Table law not decided",
    // No diagnostic uses this row yet: plan rows ASSOC-lattice, ASSOC-mod, ASSOC-gf2, ASSOC-gcd
    // and ENUM-quotient emit it.
    OutsideNormalForms => "Operator outside the normal forms",
    // No diagnostic uses this row yet: plan row TERM-stall emits it.
    ReadsOwnValue => "A definition that reads its own value",
    QuantifierNotFinite => "Quantifier in a law over a domain that is not finite",
    BelowProofGrade =>
        "Obligation below proof grade",
    NonExhaustiveMatch => "Non-exhaustive `match`",
    UnreachableArm => "Unreachable `match` arm",
    FoldWithNone => "`.fold` on a type that has none",
    MapOutsideValues => "`.map` at a parameter outside the value positions",
    PositionalMap =>
        "Positional `.map`, or a name that is no parameter, on a value that is not a morphism",
    KeyOutsideBound => "Key outside the permission bound",
    AlwaysFails => "Operation that always fails",
    UndischargedRegion => "Undischarged region assertion",
    ReadBelowDomain => "Read below the domain with no boundary entry",
    BareBoundary => "Boundary item with neither `initial` nor an index",
    TwoInitials => "Two `with initial` items for one variable",
    OverlappingArrows => "Cross-unit overlapping incomparable arrows",
    AmbiguousImport => "Ambiguous imported name",
    NameAboveDefinition => "Name used above its definition",
    // No diagnostic uses this row yet: plan row L1.14a emits it.
    UnresolvedName => "Name that resolves to nothing",
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
    // No diagnostic uses these four rows yet: plan rows L7.4 (the first and third), TERM-1 and
    // EXPORT-unique emit them.
    BitFieldWithNoUnit => "Bit-field of a foreign struct with no C unit",
    ItemWithNoBitOrder => "Grammar item narrower than a byte with no bit order",
    ReleaseWhileKept => "Release of a foreign value while a result that keeps it is still read",
    SymbolExportedTwice => "One C symbol exported twice",
    Rebinding => "Rebinding in the same scope",
    BinderNamingType => "Binder naming a type",
    // A numeric literal at a carrier it cannot take (as `x * 2.0` with `x: int`), and a decimal
    // literal, or a `/` of integer literals, that nothing gives a carrier (as `half = 1 / 2`).
    LiteralCarrier => "Numeric literal at a carrier that cannot take it",
    UnfixedDecimal => "Decimal literal, or `/` of integer literals, that nothing gives a carrier",
    NoCommonCarrier => "Two numeric values with no common carrier",
    // `b == s` with `b: bool` and `s: String`, or `x == 1r` with `x: bool`: the comparison always
    // gives the same answer.
    EqNoCommonCarrier => "Two values compared by `==` or `!=` whose types share no value",
    UnusedMatchBinder => "Match binder unused in its guard and arm",
    CapitalizedFreeName => "Capitalized free name used once in a signature and nowhere in the body",
    UndeclaredNameInField =>
        "Capitalized name in a `struct` field that is neither a declared type parameter nor a name in scope",
    UnusedTypeParameter =>
        "Type parameter that no field of its `struct`, or the body of its `type`, uses",
    StructParameterNamesField => "`struct` type parameter with the name of a field",
    // No diagnostic uses this row yet: plan row L12.0 emits it.
    StructLawNotProved => "Struct law not proved at a value built, ascribed or passed at the struct type",
    RemapOutputName =>
        "Remap output name that names a source level and resolves to a value in scope",
    MethodOnValue => "Method declared on a value",
    PrefixMinus => "Prefix `-` on a numeric literal's postfix chain",
    DisplayInBody => "Display in body position",
    // No diagnostic uses this row yet: plan row L1.29d emits it.
    SyntaxError => "Syntax error",
    NamedBeforePositional => "Named argument before a positional one",
    PositionalAfterNamed => "`positional` parameter after a named one",
    WrongForm => "Argument in the wrong form",
    ParameterKinds => "Function whose parameter kinds do not fit the expected function type",
    MissingArgument => "Missing argument",
    // No diagnostic uses these four rows yet: plan row L1.29c emits them.
    ArgumentBeyondParameters => "Argument beyond the parameters",
    ArgumentNamedForNoParameter => "Argument named for no parameter",
    ParameterGivenTwice => "Parameter given two values",
    ValueBeforeDotWithNoParameters => "Value before the dot for a function with no parameters",
    NothingLeftOut => "`...` with no named parameter left out",
    PositionalConstructor => "Positional constructor call or pattern",
    InnerDomain => "Inner-domain dependency outside the fragment",
    AmbiguousAtCarrier => "Operator or literal ambiguous at a theory's carrier",
    NoFieldAtCarrier => "Operator or literal at a theory's carrier with no field to name",
    GenericInstance => "Instance of a generic definition that fails to type",
    UnboundedHistory => "Demanded history of a loop whose step count has no proven bound",
    HistoryBoundForm => "Bound on a history keyed by step number, or an overflow policy on a history bound",
    UnboundedSize => "Size with no proven bound under `@preallocated` or the `preallocated` mode",
    CellReadsItself => "Cell read on a path back to its own cell",
    MeaningCase => "Meaning function with a case `@decides` cannot reify",
    NonLinearQuestion =>
        "Linear question outside the polynomial fragment of the linear-relation domain",
    WritesNothing => "Statement that writes nothing, or drops a declared result",
    // No diagnostic uses the next three rows yet: plan rows L2.12d, L15.8b and L21.0b emit them.
    UnreadBinding => "Block binding that nothing reads",
    ProgramHole => "Hole in the program",
    UngrantedReach => "Dependency reaching what its importer did not grant",
    // No diagnostic uses this row yet: plan row L7.2 emits it.
    UncommutedPortOps => "Two operations on one port that may not commute, with nothing ordering them",
    NoArrowAtCarrier => "Operator with no arrow at its operands' carrier",
    UnitsDiffer => "Units that differ where an operation requires equal ones",
    // No diagnostic uses the next eight rows yet: plan rows L12.2a-L12.2d emit them.
    UnitNameNotDeclared => "Unit name not declared",
    UnitDeclarationCycle => "Cycle of unit declarations",
    UnitDeclaredTwice => "Two different declarations of one unit name, or of one spelling",
    UnitDefNotConstant => "`UnitDef` that is not a constant at a unit's top level",
    ConversionFactorNotHeld => "Conversion whose factor the carrier cannot hold",
    ConversionBetweenExpansions => "`.to` between units of different full expansions",
    SumOfPointReadings => "No `+` of two point readings",
    PointUnitInProduct => "Point unit in a product, quotient or power",
    // No diagnostic uses the next six rows yet: plan rows L12.2h-L12.2k emit them.
    FactDiffersFromCarried => "Fact written on a value that carries a different one",
    RemovedFactNotCarried => "Fact removed that the value does not carry",
    RemovedFactNotRemovable => "Fact removed from a facet that does not allow it",
    UnitNotTaken => "Unit that an operation does not take",
    LogUnitInOperation => "Logarithmic unit in an operation that would change with the unit",
    ExponentialBaseDiffers => "Exponential whose base differs from the logarithm's",
    TaintAtSink => "Taint at a sink whose parameter does not take it",
    MutatingCallOnValue => "`*.` call on a receiver that is not a state variable",
    StoreSchemaMismatch => "Stored collection whose type and schema disagree",
    LevelDomainsDiffer => "Levels of one name with different domains",
    OutsideRefinement => "Argument outside its parameter's refinement",
    AtomCannotPassOut => "Loose atom inside an argument at a position from which it cannot pass out of the call",
    // No diagnostic uses the next four rows yet: plan rows L7.1b, L8.2c and L20.3c emit them.
    LevelNamesMisfit => "Level names that do not fit the type",
    LevelNameClash => "Two levels of one map with one name at the instantiation of a generic type",
    UnknownSliceName => "Named slice of a name the value's type does not have, or of one level twice",
    UnnamedCodecLevel => "Codec of a map type with an unnamed level",
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

/// The message for `what`, a form or prelude name of the Zed language that this version of
/// zedc does not compile yet: one text for every such form, so that a reader is never sent to
/// the plan that schedules it.
pub fn not_yet(what: &str) -> String {
    format!(
        "{what} is part of the Zed language, and this version of zedc does not compile it yet. \
         Write the program without it, with the forms this zedc compiles."
    )
}

/// Where a bug in zedc is reported.
pub const REPORT_TO: &str = "https://github.com/zedlanguage/zed/issues";

/// What zedc prints when it stops at a broken assumption of its own (a panic): that this is a
/// bug in zedc and not in the program, what zedc `expected`, the file and line of zedc where it
/// stopped, and how to report it (DESIGN.md sec:diagnostics).
pub fn bug(expected: &str, place: Option<(&str, u32)>) -> String {
    let place = place.map_or(String::new(), |(file, line)| {
        format!(" ({file}, line {line})")
    });
    format!(
        "zedc stopped because of a bug in zedc itself, not in your program. zedc expected this \
         to hold, and it did not: {expected}{place}.\n\
         Please report it at {REPORT_TO}, with the command line you ran and the files it read, \
         so that it can be repeated."
    )
}
