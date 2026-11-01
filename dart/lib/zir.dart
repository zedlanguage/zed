/// ZIR, the intermediate representation (step L1.31; DESIGN.md sec:ir): the graph, its
/// validator, and its text and binary forms.
library;

export 'src/zir/binary.dart' show decode, encode, nanBits;
export 'src/zir/canon.dart';
export 'src/zir/graph.dart';
export 'src/zir/text.dart'
    show
        edge,
        parse,
        parseEdge,
        parsePattern,
        parseType,
        parseValue,
        pattern,
        print,
        spell,
        version;
