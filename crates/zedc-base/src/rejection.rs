//! The rows of the rejection table (DESIGN.md sec:diagnostics, "What a rejection owes"). Each
//! diagnostic of a rejection the table lists names its row, and every `// ✗ Row: …` comment
//! names the row it is checked against (step L1.21). The names are the table's first column up to
//! any parenthesis; a test (feature `spec` of `zed-tests`) reads the table in DESIGN.md in place
//! and holds this list equal to it.

use crate::address::ContentAddress;

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
    // No diagnostic uses this row yet: step L4.5 emits it (row DIAG-computed-key-display wrote it,
    // from QUESTIONS A86).
    DisplayKeysNotDistinct => "Display with computed keys not proved distinct",
    UnliftedCarrier => "Unlifted carrier",
    MissingAlgebraicObligation => "Missing algebraic obligation",
    UndischargeableEnsure => "Undischargeable `@ensure`",
    UnsatisfiableConstraints => "Unsatisfiable declared constraints",
    LoopedAlternatives => "A test whose `||` alternatives limit each other's ranges in a loop",
    // No diagnostic uses this row yet: plan row H10-refuse emits it.
    UndecidablePremise => "Undecidable premise class",
    // No diagnostic uses this row yet: plan row HULL-conic emits it.
    NumberTooWide => "Number too wide to factor",
    // No diagnostic uses this row yet: `zed_kernel::poly::Refusal::message` writes its text for
    // `Refused::Work`, and plan rows L3.9 (rung 3) and ASSOC-demand (rung 2) emit it.
    ExpansionTooCostly => "Expansion too costly",
    // No diagnostic uses this row yet: `zed_kernel::poly::Refusal::message` writes its text for
    // `Refused::Exponent`, and plan rows L3.9 (rung 3) and ASSOC-demand (rung 2) emit it, as for
    // `ExpansionTooCostly`.
    ExponentTooLarge => "Exponent too large",
    // No diagnostic uses the next two rows yet (warnings): plan row L3.9 (rung 3) emits them.
    LawDirectionShapedOperands => "Law direction with two shaped operands under one associative and commutative operator",
    LawDirectionRepeatedName => "Law direction with a repeated name under one associative and commutative operator",
    // No diagnostic uses this row yet: plan row ASSOC-select emits it.
    SelectionKeysNotInOneOrder => "Selection keys not in one order",
    // No diagnostic uses this row yet: plan row ASSOC-table emits it.
    TableLawNotDecided => "Table law not decided",
    // No diagnostic uses this row yet: plan rows ASSOC-lattice, ASSOC-mod, ASSOC-gf2, ASSOC-gcd
    // and ENUM-quotient emit it.
    OutsideNormalForms => "Operator outside the normal forms",
    // A cycle of values each read as the next is computed (`Tables::cycle_reports`); plan row
    // TERM-stall compiles the loops and indexed definitions its repairs offer.
    ReadsOwnValue => "A definition that reads its own value",
    // No diagnostic uses this row yet: plan row SCHED-eval-before-check emits it, from a
    // `zedc::store::schedule::Refusal`.
    NeededToCheckItsOwnComputation => "Compile-time value needed to check its own computation",
    // No diagnostic uses this row yet: plan row PE-what-to-evaluate emits it, when a check needs
    // a value the rules of DESIGN "What partial evaluation evaluates" leave to run time.
    LeftToRunTime => "Compile-time value left to run time",
    QuantifierNotFinite => "Quantifier in a law over a domain that is not finite",
    // `Resolver::unending` (zedc-resolve), plan row RANGE-open-walk.
    OpenRangeEveryEntry => "A read of a range with no upper end that takes every entry",
    BelowProofGrade =>
        "Obligation below proof grade",
    // No diagnostic uses this row yet: step L6.12b emits it, a note under `BelowProofGrade` (row
    // DIAG-arms-cost wrote it, from QUESTIONS A71).
    ArmsOneKey => "Call left an atom at a node reached with other arguments",
    // No diagnostic uses the next two rows yet: step L18.2a emits them.
    CostAboveClaim => "Work above its cost claim",
    CostUnbounded => "Unbounded work under a cost claim",
    // No diagnostic uses the next row yet: plan row TERM-verdicts emits it.
    NotProvedToEnd => "Not proved to end",
    // No diagnostic uses the next four rows yet: plan row COST-required emits them.
    CostClaimMissing => "Function without a cost claim in a unit under `@cost(#required);`",
    CostReasonMissing => "Cost claim above `O(n log n)` without a reason",
    CostClaimUnbounded => "Cost claim that bounds nothing",
    CostKindMissing => "Cost claim with no kind of bound, or with a lower bound",
    // No diagnostic uses the next row yet: plan row L18.2g emits it.
    CostClaimTime => "Time in a cost claim",
    // No diagnostic uses the next two rows yet: plan row COST-required emits them.
    EquivalentShape => "Equivalent switch of another shape",
    EquivalentNoInputs => "Equivalent switch below proof grade without inputs",
    // No diagnostic uses the next three rows yet: steps L18.2d (the first) and L18.2e (the other
    // two) emit them.
    MemoizedNotAFunction => "`@memoized` on code whose result is not a function of its key",
    MemoArenaAfterWith => "`memoizationArena` written after `with`",
    MemoArenaAroundNothing => "Memo arena around no `@memoized` code",
    // No diagnostic uses this row yet: plan rows L18.2a and L18.2f emit it.
    FusedNotMet => "Plan assertion `@fused` not met",
    // No diagnostic uses this row yet: step L18.2a emits it (row DIAG-noalloc-row wrote it).
    NoallocNotMet => "Plan assertion `@noalloc` not met",
    NonExhaustiveMatch => "Non-exhaustive `match`",
    UnreachableArm => "Unreachable `match` arm",
    BareOperatorPattern => "Pattern built with an operator, written bare",
    ElseNamesNoAtoms => "An `else` that does not name its atoms",
    OrPatternNamesDiffer => "Or-pattern alternatives bind different names",
    // No diagnostic uses this row yet: plan row OR-PAT-check emits it.
    GuardedOrPatternOverlap => "Guarded or-pattern with overlapping alternatives",
    FoldWithNone => "`.fold` on a type that has none",
    MapOutsideValues => "`.map` at a parameter outside the value positions",
    PositionalMap =>
        "Positional `.map`, or a name that is not a parameter, on a value that is not a morphism",
    KeyOutsideBound => "Key outside the permission bound",
    FunctionAnswersOutsidePartialMap => "Function value that answers outside a partial map's value type",
    AlwaysFails => "Operation that always fails",
    // No diagnostic uses the next two rows yet: plan row L5.4c emits them.
    KeyEditOnPositions => "Insert or delete by key on a level keyed by position",
    SpliceWithoutPositions => "`splice` on a level with no positions",
    // No diagnostic uses this row yet: plan row CHECK-concat-non-rank-menu emits it, in place of
    // the headline `list_concat_end` (zedc-check walk/fp_ops.rs) gives today.
    ConcatNonRankKeys => "`++` on a family keyed by `int` that is not a rank level",
    UndischargedRegion => "Undischarged region assertion",
    ReadBelowDomain => "Read below the domain with no boundary entry",
    BareBoundary => "Boundary item with neither `initial` nor an index",
    WithInitialItem => "A `with initial` item",
    BareLoopEntry => "A boundary entry of a loop written without `initial`",
    InitialOutsideLoop => "An `initial` statement outside a loop, or under `local`",
    BreakOutsideLoop => "`break` outside the body of a loop or a `for`",
    InitialNotUpdated => "An `initial` statement for a name the loop does not update",
    InitialReadsLoop => "An `initial` value that reads a name of its own loop",
    TwoSentinels => "Two sentinel values for one variable",
    NotEveryPath => "A loop variable not updated on every path of a step",
    CarryOnKeyedEntry => "`with carryForward` on a keyed boundary entry",
    MutableDeclaration => "A `mutable` declaration",
    CarryWord => "A word other than `carryForward` after `with` at the end of an `initial` statement",
    OverlappingArrows =>
        "Overlapping incomparable arrows that no arrow on the overlap decides, in one unit or across units",
    AmbiguousImport => "Ambiguous imported name",
    NameAboveDefinition => "Name used above its definition",
    TopLevelStatement => "Statement at a unit's top level",
    // No diagnostic uses this row yet: plan row L1.14a emits it.
    UnresolvedName => "Name that resolves to nothing",
    NeedInCallerScope => "Need met only by an arrow in the caller's scope",
    MemberTwice =>
        "Two members of one name with different declarations in a struct or interface body",
    PathLeavesPackage =>
        "File read at the compile-time stage by a path that leaves the package root",
    StalePin => "Pinned file whose content no longer matches its pin",
    // No diagnostic uses this row yet: plan row SCHED-schema-types emits it.
    SchemaNotInBuild => "Type computed from a schema file the build does not carry",
    ImportCycle => "Import cycle",
    // No diagnostic uses this row yet: plan row LOCAL-fields-typed emits it, from the type of the
    // value read.
    LocalFieldRead => "Local field read outside its unit",
    // `Resolver::local_fields` (zedc-resolve) gives this rejection with no row, as an import of a
    // `local` name is: the near misses of l01_21 are one unit each, and this needs two.
    LocalFieldConstructed => "Local field named in a construction outside its unit",
    // `Resolver::local_fields` (zedc-resolve) gives this rejection with no row, as an import of a
    // `local` name is: the near misses of l01_21 are one unit each, and this needs two.
    LocalFieldPattern => "Local field bound by a pattern outside its unit",
    // No diagnostic uses this row yet: plan row LOCAL-fields-typed emits it.
    LocalFieldMatched => "Structural match on a local field outside its unit",
    // No diagnostic uses this row yet: plan row L2.12 emits it.
    ImportPathNamesNoUnit => "Import of a path that names no unit",
    OrderWithNone =>
        "Order read on a level with no natural order — origin keys outside their `Seq`",
    TwoOrders => "Two declared orders meet in one key type",
    EmissionDisjointness => "Emission-disjointness",
    // No diagnostic uses these thirty-six rows yet. The plan rows that emit them: L7.4 the first,
    // second, sixth, eighth to tenth, twenty-first and thirty-sixth; TERM-1 the third to fifth;
    // FFI-token-check the seventh, thirteenth and sixteenth to nineteenth; IMPL-consume-unless the
    // eleventh and twelfth; FFI-release-failure the fourteenth; FFI-release-zed the fifteenth;
    // FFI-held the twentieth, twenty-second and twenty-third; FFI-thread the twenty-fourth and
    // twenty-fifth; FFI-isolate the twenty-sixth to twenty-eighth and the thirty-fourth;
    // FFI-sandbox-linux the twenty-ninth to thirty-second; STRICT-build the thirty-third;
    // EXPORT-unique the thirty-fifth.
    BitFieldWithNoUnit => "Bit-field of a foreign struct with no C unit",
    ForeignFieldMisaligned => "Foreign field at an offset its alignment does not divide",
    ItemWithNoBitOrder => "Grammar item narrower than a byte with no bit order",
    MixedTextBinaryGrammar => "Struct grammar that mixes text and binary items",
    ParseOfOtherMode => "Parse function of the other mode",
    ReleaseWhileKept => "Release of a foreign value while a result that keeps it is still read",
    UseAfterRelease => "Use of a value after the program releases it",
    ReleaseParametersUnfilled => "Release function whose parameters the `release` does not fill",
    TerminatorInArgument => "Terminated argument that may hold its terminator",
    IntegerHandleAsInteger => "Integer handle used as an integer",
    ConsumesMisplaced => "Parameter declared `with consumes()` that is not typed `Ptr(…)` or is given a value Zed does not own",
    UseOfPossiblyTakenValue => "Use of a value that a call may have taken",
    ReleasedValueUnused => "Released value that nothing uses",
    ReleaseCanFail => "Release that Zed makes whose function can report a failure",
    ZedReleaseKeepsValue => "Release function written in Zed that does not free the value",
    NotPassedMisused =>
        "Parameter declared `with notPassed()` that cannot keep its argument",
    SecondRelease => "Value given a second release",
    ReleaseCallWithoutToken => "Call of a token's release that names no token",
    ForeignSignatureWithoutState => "Foreign signature that does not take its library's state",
    UseOfHeldValue => "Use of a value after a call that holds it",
    OneCFunctionTwoNames => "One C function declared under two library names for one file",
    HoldNeverEnds => "Hold that Zed cannot end",
    HolderCallUnordered =>
        "Call on a holder with nothing ordering it with a call that changes its holds",
    StatefulLibraryOnTwoThreads => "Stateful library on two threads",
    CallbackCrossesThread => "Callback that calls a library bound to another thread",
    IsolatedAndNot => "One foreign library declared isolated and not isolated",
    IsolatedWithoutOneToken => "Isolated foreign library without one token",
    IsolatedMemoryRead => "Foreign memory of an isolated library read in the program",
    RestrictionNotIsolated => "Restriction of a library that is not isolated",
    RestrictedTwoWays => "One isolated library restricted in two ways",
    RestrictionNotEnforceable => "Restriction the target cannot enforce",
    RestrictionRelativePath => "Relative path in a restriction",
    NotIsolatedInStrictBuild => "Foreign library not isolated in a strict build",
    ForeignFailureNotInResult => "Failure of a foreign call not written in the result type",
    CNameGeneratedTwice => "One C name generated twice",
    // No diagnostic uses the next six rows yet: plan row FFI-cexport emits them.
    GenericExportWithoutResolutions => "Generic function exported without its resolutions",
    ExportResolutionDoesNotCheck => "Export resolution that does not check",
    ExportTypeNotInC => "Type C cannot hold in an export",
    ExportNameNotInC => "Name C cannot spell in an export",
    CLibraryWithoutPrefixOrVersion => "C library build without a prefix or a version",
    ExportLanguageNotTargeted => "Export to a language zedc does not target",
    MisalignedForeignPointer => "Misaligned foreign pointer in a run",
    Rebinding => "Rebinding in the same scope",
    BinderNamingType => "Binder naming a type",
    // A numeric literal at a carrier it cannot take (as `x * 2.0` with `x: int`), and a `/` of
    // integer literals alone that nothing gives a carrier (as `half = 1 / 2`).
    LiteralCarrier => "Numeric literal at a carrier that cannot take it",
    UnfixedDecimal => "`/` of integer literals alone that nothing gives a carrier",
    NoCommonCarrier => "Two numeric values with no common carrier",
    // `b == s` with `b: bool` and `s: String`, or `x == 1r` with `x: bool`: the comparison always
    // gives the same answer.
    EqNoCommonCarrier => "Two values compared by `==` or `!=` whose types share no value",
    UnusedMatchBinder => "Match binder unused in its guard and arm",
    TypeVariableOnce => "Type variable",
    UnknownTypeName => "Capitalized name, not of a type variable's form, that names no type in scope",
    TypeVariableFormDeclared => "Name of a type variable's form, or of that form followed by `'`, declared as a type, `struct`, interface, field, function, parameter, value or module",
    // No diagnostic uses this row yet: plan row L2.12 emits it.
    TypeParameterNotTypeVariableForm =>
        "Type parameter of a `struct`, `type` or `interface` whose name is not of a type variable's form",
    StructFieldTypeVariable =>
        "Type variable in a `struct` field that is not one of the struct's declared type parameters",
    UnusedTypeParameter =>
        "Type parameter that no field of its `struct`, or the body of its `type`, uses",
    StructParameterNamesField => "`struct` type parameter with the name of a field",
    // No diagnostic uses this row yet: plan row L12.0 emits it.
    StructLawNotProved => "Struct law not proved at a value built, ascribed or passed at the struct type",
    RemapOutputName =>
        "Remap output name that names a source level and resolves to a value in scope",
    MethodOnValue => "Method declared on a value",
    PrefixMinus => "Prefix `-` on a numeric literal's postfix chain",
    BareKey => "Union, intersection or difference written bare as a key, guarantee or permission",
    DisplayInBody => "Display in body position",
    SyntaxError => "Syntax error",
    InfixOperand => "Arithmetic operator written without parentheses in an operand of an infix call",
    ReservedWordAsName => "Reserved word written where a name stands",
    BidiControlInText => "`Bidi_Control` character in a comment or in the text of a string literal",
    LeadingZero => "Decimal number with a leading `0`",
    PushWhereLessMeant => "`<-` written where a comparison with a negative operand was meant",
    PushTargetNotPushable => "Push to a target that cannot be pushed to",
    PushToNameNotPort => "Push to a name that is not a port",
    PushToInput => "Push to an input or a read view",
    PushToReadOnlyView => "Push to a view that takes no push",
    PushToFieldNotPort => "Push to a field that is not a port",
    // No diagnostic uses this row yet: plan row PORT-process emits it, with `spawn`.
    PushToMaybeFailure => "Push to a target that may be a failure",
    GenerationPushOutsideLoop => "Generation push outside a loop",
    GenerationPushNotReceiverField => "Generation push to a name that is not a field of the receiver",
    BindingInCondition => "`=` written in a condition where `==` was meant",
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
    // No diagnostic uses the next eight rows yet: plan rows L7.3l (port policies), L7.14 (derived
    // queue sizes and carried state) and L7.3m (`::batches`) emit them.
    PolicyOffPort => "Overflow policy on a value that is not a port",
    BoundBelowDerivedSize => "Bound below the derived size",
    QueueSizeOpen => "Queue whose size the domains leave open",
    TwoPortPolicies => "Two policies on one port",
    PolicyKindRefuses => "Overflow policy a port kind does not take",
    UnpausableSourceNoPolicy => "Source that cannot pause read with no overflow policy",
    CarriedGrowthUnbounded => "Carried collection whose growth has no proved bound",
    BatchesOnOutput => "`::batches` on an output port",
    // No diagnostic uses the next two rows yet: plan row L18.2c emits them.
    StackOverBound => "Stack depth over `@stack(bytes: b)`",
    StackOverflow => "Stack overflow in a run",
    NumberOverAddressSpace => "Number too large for any memory of the target",
    // No code names the next two rows: the run prints their messages itself, never through
    // these rows. "Out of memory in a run" is the run's "Number too large for memory"
    // (zed-kernel value.rs:4871, `NUMBER_TOO_LARGE`); "Limit of `main` passed in a run" is the
    // run's "Memory limit of `main` passed" (zed-rt limits.rs:372, stack.rs:568),
    // "Processor-time limit of `main` passed" (limits.rs:190) and "Deadline of `main` passed"
    // (limits.rs:253). Plan row MAIN-limits, which built them, is done.
    OutOfMemory => "Out of memory in a run",
    MainLimitPassed => "Limit of `main` passed in a run",
    // No diagnostic uses the next row yet: plan row STOP-releases-rt emits it.
    StopReleaseFailed => "Release that fails during a stop",
    // No code names the next row: the runtime prints its message itself, in a signal handler
    // too, where no row can be formatted (zed-rt close.rs, `message`; PORT-stdout-close-status).
    StdoutCloseFailed => "Standard output failed when the run closed it",
    // No diagnostic uses the next row yet: plan row STOP-releases-rt emits it.
    StopReleasesCut => "Releases of a stop cut short",
    SignalsReadWithoutHandles => "Signals of `main` read without `handles`",
    SignalDeclarationCannotHold => "Signal declaration of `main` that cannot hold",
    // No diagnostic uses the next row yet: plan row STOP-releases-rt emits it.
    ForeignFault => "Fault of foreign code in a run",
    UnboundedSize => "Size with no proven bound under `@preallocated` or the `preallocated` mode",
    // No diagnostic uses the next row yet: plan row MEM-verdicts emits it.
    NoProvedMemoryBound => "No proved memory bound",
    // No diagnostic uses this row yet: plan row MAIN-limits-strict emits it.
    ThreadCountUnknown => "Thread count that `--strict` cannot fix",
    CellReadsItself => "Cell read on a path back to its own cell",
    MeaningCase => "Meaning function with a case `@decides` cannot reify",
    NonLinearQuestion =>
        "Linear question outside the polynomial fragment of the linear-relation domain",
    WritesNothing => "Statement that writes nothing, or drops a declared result",
    // No diagnostic uses the next row yet: plan row FFI-status emits it. The row after it is
    // emitted at a division whose divisor is 0 at a root where a constraint fails (ROOTS-listed).
    OneTargetForResults => "One target for a call with several results",
    RootConstraintFails => "A root of an obligation's equation at which a written constraint does not yield `true` or `false`",
    // No diagnostic uses this row yet: plan row MOD-residue-fragment emits it.
    ResidueRefused => "Residue question refused",
    // No diagnostic uses the next five rows yet: plan rows L2.12d, IMPL-reached-effects, L15.8b,
    // L7.4 and L21.0b emit them.
    UnreadBinding => "Block binding that nothing reads",
    PortOpInLogLine => "Port operation in a log line",
    ProgramHole => "Hole in the program",
    LibraryNameUnresolved => "Foreign library name the build cannot resolve",
    UngrantedReach => "Dependency reaching what its importer did not grant",
    // No diagnostic uses this row yet: plan row L7.2 emits it.
    UncommutedPortOps => "Two operations on one port that may not commute, with nothing ordering them",
    // No diagnostic uses this row yet: plan row L7.2b emits it.
    OrderDependentPortOpInMap =>
        "Port operation in a `map` or a `where` that depends on the order of its entries",
    // No diagnostic uses this row yet: plan row PORT-interchangeable emits it.
    UnnamedDraw => "Draw where no keypath names it",
    // No diagnostic uses this row yet: plan row L7.5c emits it.
    EventClassOnNonWavePort => "Event class on a port that starts no wave",
    NonblockingCanBlock => "Function marked `@nonblocking` that can block",
    BlockingWritten => "`@blocking` written",
    // No diagnostic uses the next nine rows yet: plan row DIAG-scan-rows emits them.
    RecursiveTypeIrregular =>
        "Recursive type that is not contractive, not regular, or whose emptiness is not monotone",
    FunctionWhereFamilyNeeded =>
        "`==`, `!=` or a fold over the whole present domain given a function where a family is needed",
    NoArrowTakesCall => "Call that no arrow of the name takes",
    ExportUninferable =>
        "Exported definition whose signature cannot be inferred without its call sites",
    LawBodyNotBool => "Law whose body is not exactly `bool`",
    LawProofCycle => "Laws whose proofs depend on each other in a cycle",
    RunTimeReadsHint => "Run-time value that depends on a hint-kind fact or an `f::residual` read",
    GenericCallAtBuiltType => "Call of a generic definition at a type its body builds",
    ReadOfComputedValue => "Read of `::source`, `::zir` or `::shape` on a computed value",
    NoArrowAtCarrier => "Operator with no arrow at its operands' carrier",
    ModOnFloat => "`mod` on a float",
    UnitsDiffer => "Units that differ where an operation requires equal ones",
    // No diagnostic uses the next twelve rows yet: plan rows L12.2a-L12.2d,
    // UNITS-assumed-args and UNITS-compare emit them.
    UnitNameNotDeclared => "Unit name not declared",
    UnitDeclarationCycle => "Cycle of unit declarations",
    UnitDeclaredTwice => "Two different declarations of one unit name, or of one spelling",
    UnitDefNotConstant => "`UnitDef` that is not a constant at a unit's top level",
    ConversionFactorNotHeld => "Conversion whose factor the carrier cannot hold",
    ConversionBetweenExpansions => "`.to` between units of different full expansions",
    ArgumentUnitNotConvertible => "Argument whose unit does not convert to its parameter's",
    BareNumberForUnits => "Number with no unit for a parameter declared `units(u)`",
    AssumedUnitsMisplaced =>
        "`assumedUnits` beside `units` on one declaration, or written where it does not attach",
    SumOfPointReadings => "No `+` of two point readings",
    PointUnitInProduct => "Point unit in a product, quotient or power",
    PointReadingComparedWithNonReading => "Point reading compared with a value that is not a reading",
    // No diagnostic uses the next six rows yet: plan rows L12.2h-L12.2k emit them.
    FactDiffersFromCarried => "Fact written on a value that carries a different one",
    RemovedFactNotCarried => "Fact removed that the value does not carry",
    RemovedFactNotRemovable => "Fact removed from a facet that does not allow it",
    UnitNotTaken => "Unit that an operation does not take",
    LogUnitInOperation => "Logarithmic unit in an operation that would change with the unit",
    ExponentialBaseDiffers => "Exponential whose base differs from the logarithm's",
    TaintAtSink => "Taint at a sink whose parameter does not take it",
    // No diagnostic uses the next six rows yet: plan row L33.1e emits them.
    SecretPosition => "Read or write at a secret position",
    SecretLoopEnd => "Loop whose end depends on a secret",
    SecretVariableTime => "Variable-time operation on a secret",
    SecretAllocationSize => "Allocation sized by a secret",
    SecretSelectionNotBranchFree => "Secret selection that cannot be made branch-free",
    CryptosafeCallNotFollowed => "Call that `@cryptosafe` cannot follow",
    // No diagnostic uses the next row yet: plan row FPWARN emits it.
    RoundedAtRefusingParameter => "Rounded value at a parameter that refuses it",
    NoIntEquals => "No `int` equals the value",
    MutatingCallOnValue => "`*.` call on a receiver that is not a state variable",
    StoreSchemaMismatch => "Stored collection whose type and schema disagree",
    LevelDomainsDiffer => "Levels of one name with different domains",
    OutsideRefinement => "Argument outside its parameter's refinement",
    AtomCannotPassOut => "Loose atom inside an argument at a position from which it cannot pass out of the call",
    // No diagnostic names the next row yet: `Ck::passing` raises it, and names it once a `type`
    // declaration gives a value a named family, which waits on elaboration (step L2.4), when a
    // near miss can raise it (plan row MSG-family-atom-row-name).
    FamilyAtomUnhandled => "Atom of a named family reaching a call, an index, the condition of `if`, `sum`, destructuring or an ordering of tuples, none of which has a case for it",
    // No diagnostic uses the next four rows yet: plan rows L7.1b, L8.2c and L20.3c emit them.
    LevelNamesMisfit => "Level names that do not fit the type",
    LevelNameClash => "Two levels of one map with one name at the instantiation of a generic type",
    UnknownSliceName => "Named slice of a name the value's type does not have, or of one level twice",
    UnnamedCodecLevel => "Codec of a map type with an unnamed level",
    // No diagnostic uses the next three rows yet: plan rows STR-layer-views and UNITS-text-lengths
    // emit them.
    StringWithNoView => "String read with no view",
    ViewNotOfType => "View a string's type does not have",
    CountedInMisplaced => "`countedIn` written where it does not attach, or twice",
    // No diagnostic uses the next four rows yet: plan rows THEORY-partial (the first two), L22.9a
    // and AD-forward emit them.
    ModelFieldMisfit => "Model field that does not fit an arrow of its type",
    OpaquePredicateFact => "Fact needed about an opaque predicate",
    IntegralWithNoClosedForm =>
        "`integral` with no closed form, or of a lambda of more than one parameter",
    NotDifferentiable => "Differentiating a function outside the numeric programs",
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
/// zedc does not support (it is not implemented here): one text for every such form, so that a
/// reader is never sent to the plan that schedules it. The words "not supported" rather than
/// "does not compile it yet", which readers took for a failure of compile order
/// (MSG-not-supported-wording, author 2026-11-19).
pub fn not_yet(what: &str) -> String {
    format!(
        "{what} is part of the Zed language but is not supported by this version of zedc. \
         Write the program without it."
    )
}

use crate::work::Place;
/// Where a bug in zedc is reported, defined once in `zed_kernel::bug` with the words every
/// message for a bug in zedc shares (plan row MSG-bug-sentence-one).
pub use zed_kernel::bug::REPORT_TO;
use zed_kernel::bug::{Stopped, report, with_details};

/// The version of zedc, as `zedc` with no arguments prints it: every package of the workspace
/// takes the workspace's version, so this package's is zedc's.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// What zedc prints when it stops at a broken assumption of its own (a panic): that this is a
/// bug in zedc and not in the program, the declaration of the program it was at work on, and
/// how to report it (DESIGN.md sec:diagnostics), then the details for the report: zedc's
/// version, the stage, the declaration and the unit, what zedc `expected` (a panic's text) and
/// the file and line of zedc where it stopped (plan row MSG-bug-report-plain, author
/// 2026-11-09 and 2026-11-15). The place is this thread's ([`crate::work::place`]).
pub fn bug(expected: &str, place: Option<(&str, u32)>) -> String {
    bug_at(expected, place, &crate::work::place())
}

/// [`bug`] at the place `at`.
pub fn bug_at(expected: &str, place: Option<(&str, u32)>, at: &Place) -> String {
    with_details(
        report(
            Stopped::Zedc,
            &format!(
                "zedc expected something of its own to hold, and it did not{}.",
                at_work_on(at)
            ),
            "the command line you ran, the files it read and the details below",
        ),
        &details(expected, place, at),
    )
}

/// The words that name what zedc was at work on at `at`, after "it did not": the declaration
/// and the unit, each where known, or nothing.
fn at_work_on(at: &Place) -> String {
    match (&at.declaration, &at.unit) {
        (Some(d), Some(u)) => format!(", while it was at work on the declaration `{d}` in `{u}`"),
        (Some(d), None) => format!(", while it was at work on the declaration `{d}`"),
        (None, Some(u)) => format!(", while it was at work on `{u}`"),
        (None, None) => String::new(),
    }
}

/// The details of a report of a bug in zedc, each where known: zedc's version, the stage, the
/// declaration and the unit of `at`, what zedc `expected`, and the file and line of zedc.
fn details(expected: &str, place: Option<(&str, u32)>, at: &Place) -> Vec<(&'static str, String)> {
    let mut out = vec![("zedc version", VERSION.to_string())];
    out.extend(at.stage.map(|s| ("stage", s.name().to_string())));
    out.extend(at.declaration.clone().map(|d| ("declaration", d)));
    out.extend(at.unit.clone().map(|u| ("unit", u)));
    out.push(("expected", expected.to_string()));
    out.extend(place.map(|(file, line)| ("in zedc at", format!("{file}, line {line}"))));
    out
}

/// What a run prints when it stops at a broken assumption of zedc's own (a panic) while it
/// runs a program, under `zedc run` and in the executable `zedc build` makes alike (plan row
/// EXE-panic-status): that this is a bug in zedc and not in the program, what zedc `expected`,
/// the file and line of zedc where the run stopped, the content address of the program the
/// run is of, when the run had come far enough to know it, and how to report it. The run then
/// exits with status 3, a fault of the run (DESIGN.md sec:ports).
///
/// DESIGN.md sec:checking_in_zed: "the run reports it as a compiler bug with the build's
/// content address". At this layer the program's content address, which a record names too
/// (step L1.19b), is that address (plan row EXE-bug-report-address): a build is its target and
/// the options it turns on (step L2.8d), each read of either is replaced by its literal before
/// the address is taken, so the address changes with every part of the build the program
/// reads; the target is the host's, the one target zedc builds for; and no other switch of
/// `zedc run` or `zedc build` changes the program run (`--suppress` and `--addresses` change
/// only what is printed, `--record` only what is written beside the run). Measured
/// 2026-11-15: an option the program reads changes the address, and one it does not read
/// leaves it as it is, as it leaves the program. A switch that changes the program built
/// without a read, as `--strict` and `--total` will, joins the address when it is added.
pub fn run_bug(
    expected: &str,
    place: Option<(&str, u32)>,
    program: Option<ContentAddress>,
) -> String {
    run_bug_at(expected, place, program, &crate::work::place())
}

/// [`run_bug`] at the place `at`.
pub fn run_bug_at(
    expected: &str,
    place: Option<(&str, u32)>,
    program: Option<ContentAddress>,
    at: &Place,
) -> String {
    // The program's content address names the program, so the report of a run names no unit:
    // an executable is run with no source file, and `zedc run`'s path is the one given on its
    // command line, so a unit would make the two engines' reports differ.
    let at = &Place {
        unit: None,
        ..at.clone()
    };
    let program = program.map_or(String::new(), |a| {
        format!(
            "\nThe run was of the program whose content address is {a}, the address a record \
             of its run names."
        )
    });
    with_details(
        report(
            Stopped::Run,
            &format!(
                "zedc expected something of its own to hold, and it did not{}.{program}",
                at_work_on(at)
            ),
            "this message, the program's source, the command line you ran and the files the run \
             read",
        ),
        &details(expected, place, at),
    )
}
