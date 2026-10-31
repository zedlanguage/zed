/// Step L1.20: provenance. A run asked for it records one fact per node instance, at a fact
/// address (static node address, dynamic keypath) no other fact of the run holds, with the
/// facts it read; a failure's origins are the facts where each of its members appeared.
library;

import 'package:test/test.dart';
import 'package:zed/kernel.dart';

/// The value of `t` and the provenance of its run, under wave stamp 0.
(Value, Provenance) trace(Term t) {
  final ev = Evaluator(World(), provenanceRoot: const [Int(0)]);
  final v = ev.run(t);
  return (v, ev.provenance!);
}

/// Asserts no two facts of `p` share an address.
void unique(Provenance p) {
  expect([for (final a in p.repeated()) '$a'], isEmpty, reason: 'repeated fact addresses');
  expect(p.facts.length, greaterThan(1));
}

/// The facts at the node whose term prints as `text`.
List<Fact> at(Provenance p, String text) {
  final terms = p.terms();
  return [
    for (final f in p.facts)
      if ('${terms[f.address.node.position]}' == text) f,
  ];
}

/// The terms of the origins of fact `i`'s failure, printed, with the value each produced.
List<(String, String)> origins(Provenance p, int i) {
  final out = [
    for (final j in p.origins(i))
      ('${p.term(p.facts[j].address.node)}', p.facts[j].value?.toString() ?? '<fn>'),
  ];
  return out..sort((a, b) => '$a'.compareTo('$b'));
}
